module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bGamma
public import CFSG.Quasithin.Background.L34BinMult
public import CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm

open Subgroup CFSG.RankThree.FFModules CFSG.QuasithinUnique.Setup.X7b
open CFSG.LocalAnalysis.UniquenessCase.UC22.F05 CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF

theorem exists_min_sub {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (P : Submodule (ZMod 2) X → Prop) {U₀ : Submodule (ZMod 2) X} (hP : P U₀) (h0 : U₀ ≠ ⊥) :
    ∃ U ≤ U₀, P U ∧ U ≠ ⊥ ∧ ∀ M ≤ U, P M → M ≠ ⊥ → M = U := by
  have : Finite (Submodule (ZMod 2) X) :=
    Finite.of_injective (fun S : Submodule (ZMod 2) X => (S : Set X)) SetLike.coe_injective
  obtain ⟨U, ⟨hU₀, hPU, hU0⟩, hmin⟩ :=
    (Set.toFinite {U : Submodule (ZMod 2) X | U ≤ U₀ ∧ P U ∧ U ≠ ⊥}).exists_minimal
      ⟨U₀, le_rfl, hP, h0⟩
  exact ⟨U, hU₀, hPU, hU0, fun M hMU hPM hM0 =>
    le_antisymm hMU (hmin ⟨hMU.trans hU₀, hPM, hM0⟩ hMU)⟩

section Group

variable {G : Type} [Group G]

theorem normal_of_numConj_eq_one [Finite G] {L : Subgroup G} (h : numConj L = 1) : L.Normal := by
  obtain ⟨K, hK⟩ := Set.ncard_eq_one.mp h
  have hmem : ∀ g : G, L.map (MulAut.conj g).toMonoidHom = K := fun g => by
    have : L.map (MulAut.conj g).toMonoidHom ∈
        {K : Subgroup G | ∃ g : G, K = L.map (MulAut.conj g).toMonoidHom} := ⟨g, rfl⟩
    rw [hK] at this
    exact this
  have hL : L = K := by
    rw [← hmem 1]
    ext x
    simp
  refine ⟨fun x hx g => ?_⟩
  have : g * x * g⁻¹ ∈ L.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
  rwa [hmem g, ← hL] at this

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem fixSub_zpowers_eq [Finite G] (ρ : Representation (ZMod 2) G V) {t : G}
    (ht : orderOf t = 2) : fixSub ρ (zpowers t) = repFixedSpace ρ {t} := by
  classical
  ext v
  constructor
  · intro hv a ha
    rw [Set.mem_singleton_iff] at ha
    subst ha
    exact hv a (mem_zpowers a)
  · intro hv a ha
    rw [mem_zpowers_iff_mem_range_orderOf, ht] at ha
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.mp ha
    have hk2 : k = 0 ∨ k = 1 := by
      have := Finset.mem_range.mp hk
      omega
    rcases hk2 with rfl | rfl
    · simp
    · rw [pow_one]
      exact hv t rfl

theorem exists_involution_of_mGV_le [Finite G] [Finite V] (ρ : Representation (ZMod 2) G V)
    (hev : Even (Nat.card G)) {k : ℕ} (h : mGV ρ ≤ k) :
    ∃ t : G, orderOf t = 2 ∧
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) ≤ k := by
  classical
  unfold mGV at h
  rw [if_pos hev] at h
  have hne : {k | ∃ t : G, orderOf t = 2 ∧
      k = Module.finrank (ZMod 2) (V ⧸ fixSub ρ (Subgroup.zpowers t))}.Nonempty := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hev)
    exact ⟨_, t, ht, rfl⟩
  obtain ⟨t, ht, hk⟩ := Nat.sInf_mem hne
  refine ⟨t, ht, ?_⟩
  have h1 := Submodule.finrank_quotient_add_finrank (fixSub ρ (zpowers t))
  rw [fixSub_zpowers_eq ρ ht] at h1 hk
  omega

theorem eq_zero_of_fixed (ρ : Representation (ZMod 2) G V) (hirr : ρ.IsIrreducible)
    {L : Subgroup G} (hL : L.Normal) (hnt : ∃ l ∈ L, ρ l ≠ 1) {v : V} (hv : ∀ l ∈ L, ρ l v = v) :
    v = 0 := by
  have hinv : ∀ g, ∀ u ∈ fixSub ρ L, ρ g u ∈ fixSub ρ L := by
    intro g u hu l hl
    have h1 : g⁻¹ * l * g ∈ L := by simpa using hL.conj_mem l hl g⁻¹
    calc ρ l (ρ g u) = ρ g (ρ (g⁻¹ * l * g) u) := by
          rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
          congr 2
          group
      _ = ρ g u := by rw [hu _ h1]
  rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2 _ hinv with h | h
  · have : v ∈ fixSub ρ L := hv
    rw [h] at this
    exact (Submodule.mem_bot _).mp this
  · exfalso
    obtain ⟨l, hl, hne⟩ := hnt
    apply hne
    apply LinearMap.ext
    intro w
    have : w ∈ fixSub ρ L := h ▸ Submodule.mem_top
    exact this l hl

theorem commOn_eq_top_of_normal (ρ : Representation (ZMod 2) G V) (hirr : ρ.IsIrreducible)
    {L : Subgroup G} (hL : L.Normal) (hnt : ∃ l ∈ L, ρ l ≠ 1) : commOn ρ L ⊤ = ⊤ := by
  have hinv : ∀ g, ∀ u ∈ commOn ρ L ⊤, ρ g u ∈ commOn ρ L ⊤ := fun g u hu =>
    commOn_top_mapsTo (by rw [normalizer_eq_top_iff.mpr hL]; exact mem_top g) hu
  rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2 _ hinv with h | h
  · exfalso
    obtain ⟨l, hl, hne⟩ := hnt
    apply hne
    apply LinearMap.ext
    intro v
    exact commOn_eq_bot_iff.mp h l hl v Submodule.mem_top
  · exact h

theorem exists_isCompl_of_normal [Finite V] (ρ : Representation (ZMod 2) G V)
    (hirr : ρ.IsIrreducible) {L : Subgroup G} (hL : L.Normal) {N : Submodule (ZMod 2) V}
    (hN : ∀ l ∈ L, ∀ v ∈ N, ρ l v ∈ N) :
    ∃ C : Submodule (ZMod 2) V, (∀ l ∈ L, ∀ v ∈ C, ρ l v ∈ C) ∧ IsCompl N C := by
  classical
  let σ : ↥L →* Module.End (ZMod 2) V := ρ.comp L.subtype
  let 𝒲 : Set (Submodule (ZMod 2) V) := {W | CFSG.Quasithin.L34Bin.IsInvSub σ W ∧
    ∀ M : Submodule (ZMod 2) V, CFSG.Quasithin.L34Bin.IsInvSub σ M → M ≤ W → M = ⊥ ∨ M = W}
  have hcomm : ∀ (g l : G) (v : V), ρ l (ρ g v) = ρ g (ρ (g⁻¹ * l * g) v) := by
    intro g l v
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  have hmemL : ∀ (g l : G), l ∈ L → g⁻¹ * l * g ∈ L := fun g l hl => by
    simpa using hL.conj_mem l hl g⁻¹
  have hinvmap : ∀ (g : G) (W : Submodule (ZMod 2) V), CFSG.Quasithin.L34Bin.IsInvSub σ W →
      CFSG.Quasithin.L34Bin.IsInvSub σ (W.map (ρ g)) := by
    rintro g W hW l _ ⟨w, hw, rfl⟩
    exact ⟨_, hW ⟨g⁻¹ * l * g, hmemL g l l.2⟩ w hw, (hcomm g l w).symm⟩
  have hid : ∀ (g : G) (M : Submodule (ZMod 2) V), (M.map (ρ g⁻¹)).map (ρ g) = M := by
    intro g M
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, mul_inv_cancel, map_one]
    exact Submodule.map_id M
  have hmap : ∀ (g : G), ∀ W ∈ 𝒲, W.map (ρ g) ∈ 𝒲 := by
    rintro g W ⟨hW, hWmin⟩
    refine ⟨hinvmap g W hW, fun M hM hMW => ?_⟩
    have hM' : M.map (ρ g⁻¹) ≤ W := by
      rintro _ ⟨m, hm, rfl⟩
      obtain ⟨w, hw, rfl⟩ := hMW hm
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      exact hw
    rcases hWmin _ (hinvmap g⁻¹ M hM) hM' with h | h
    · left
      rw [← hid g M, h, Submodule.map_bot]
    · right
      rw [← hid g M, h]
  have hS : ∀ g : G, ∀ v ∈ sSup 𝒲, ρ g v ∈ sSup 𝒲 := by
    intro g v hv
    have h1 : sSup 𝒲 ≤ (sSup 𝒲).comap (ρ g) := sSup_le fun W hW =>
      Submodule.map_le_iff_le_comap.mp (le_sSup (hmap g W hW))
    exact h1 hv
  obtain ⟨hVnt, hirr'⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr
  have htop : sSup 𝒲 = ⊤ := by
    rcases hirr' _ hS with h | h
    · exfalso
      obtain ⟨W₀, -, hW₀, hW₀0, hW₀min⟩ := exists_min_sub (CFSG.Quasithin.L34Bin.IsInvSub σ)
        (U₀ := ⊤) (fun _ _ _ => Submodule.mem_top) top_ne_bot
      have hW₀𝒲 : W₀ ∈ 𝒲 := ⟨hW₀, fun M hM hMW => by
        by_cases hM0 : M = ⊥
        · exact Or.inl hM0
        · exact Or.inr (hW₀min M hMW hM hM0)⟩
      exact hW₀0 (eq_bot_iff.mpr (h ▸ le_sSup hW₀𝒲))
    · exact h
  obtain ⟨C, hC, hc⟩ := CFSG.Quasithin.L34Bin.exists_isCompl_of_sSup σ 𝒲 (fun W hW => hW) htop
    (N := N) (fun l v hv => hN l l.2 v hv)
  exact ⟨C, fun l hl v hv => hC ⟨l, hl⟩ v hv, hc⟩

end Group

section NoTrivSec

variable {K : Type} [Group K] {X : Type} [AddCommGroup X] [Module (ZMod 2) X]

@[expose] def NoTrivSec (σ : Representation (ZMod 2) K X) : Prop :=
  ∀ Y₁ Y₂ : Submodule (ZMod 2) X, (∀ k, ∀ y ∈ Y₁, σ k y ∈ Y₁) → (∀ k, ∀ y ∈ Y₂, σ k y ∈ Y₂) →
    Y₁ ≤ Y₂ → (∀ k, ∀ y ∈ Y₂, σ k y - y ∈ Y₁) → Y₂ ≤ Y₁

theorem NoTrivSec.eq_zero {σ : Representation (ZMod 2) K X} (h : NoTrivSec σ) {v : X}
    (hv : ∀ k, σ k v = v) : v = 0 := by
  have key := h ⊥ (Submodule.span (ZMod 2) {v}) (fun k y hy => by
      rw [(Submodule.mem_bot _).mp hy, map_zero]
      exact Submodule.zero_mem _)
    (fun k y hy => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, hv k]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
    bot_le (fun k y hy => by
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
      rw [map_smul, hv k, sub_self]
      exact Submodule.zero_mem _)
  exact (Submodule.mem_bot _).mp (key (Submodule.mem_span_singleton_self v))

theorem NoTrivSec.exists_ne {σ : Representation (ZMod 2) K X} (h : NoTrivSec σ)
    {Y : Submodule (ZMod 2) X} (hY0 : Y ≠ ⊥) : ∃ k, ∃ y ∈ Y, σ k y ≠ y := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hY0
  exact hy0 (h.eq_zero fun k => hcon k y hy)

variable {H : Type} [Group H]

theorem NoTrivSec.sub {π : Representation (ZMod 2) H X} {ι : K →* H} (h : NoTrivSec (π.comp ι))
    (U : Subrepresentation π) : NoTrivSec (U.toRepresentation.comp ι) := by
  intro Y₁ Y₂ hY₁ hY₂ h12 htriv
  have key := h (Y₁.map U.toSubmodule.subtype) (Y₂.map U.toSubmodule.subtype)
    (by rintro k _ ⟨y, hy, rfl⟩; exact ⟨_, hY₁ k y hy, rfl⟩)
    (by rintro k _ ⟨y, hy, rfl⟩; exact ⟨_, hY₂ k y hy, rfl⟩) (Submodule.map_mono h12)
    (by
      rintro k _ ⟨y, hy, rfl⟩
      exact ⟨_, htriv k y hy, by simp; rfl⟩)
  exact (Submodule.map_le_map_iff_of_injective U.toSubmodule.injective_subtype _ _).mp key

theorem NoTrivSec.quot {π : Representation (ZMod 2) H X} {ι : K →* H} (h : NoTrivSec (π.comp ι))
    (U : Subrepresentation π) : NoTrivSec (U.quotient.comp ι) := by
  intro Y₁ Y₂ hY₁ hY₂ h12 htriv
  have key := h (Y₁.comap U.toSubmodule.mkQ) (Y₂.comap U.toSubmodule.mkQ)
    (fun k y hy => hY₁ k _ hy) (fun k y hy => hY₂ k _ hy) (Submodule.comap_mono h12)
    (fun k y hy => by
      show U.toSubmodule.mkQ (π (ι k) y - y) ∈ Y₁
      rw [map_sub]
      exact htriv k _ hy)
  exact (Submodule.comap_le_comap_iff_of_surjective (Submodule.mkQ_surjective _)).mp key

end NoTrivSec

theorem noTrivSec_of_normal {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
    (ρ : Representation (ZMod 2) G V) (hirr : ρ.IsIrreducible) {L : Subgroup G} (hL : L.Normal)
    (hnt : ∃ l ∈ L, ρ l ≠ 1) : NoTrivSec (ρ.comp L.subtype) := by
  intro Y₁ Y₂ hY₁ hY₂ h12 htriv
  obtain ⟨C, hC, hc⟩ := exists_isCompl_of_normal ρ hirr hL (N := Y₁)
    (fun l hl v hv => hY₁ ⟨l, hl⟩ v hv)
  have hC0 : C ⊓ Y₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro v ⟨hvC, hv2⟩
    apply (Submodule.mem_bot _).mpr
    apply eq_zero_of_fixed ρ hirr hL hnt
    intro l hl
    have h1 : ρ l v - v ∈ Y₁ := htriv ⟨l, hl⟩ v hv2
    have h2 : ρ l v - v ∈ C := C.sub_mem (hC l hl v hvC) hvC
    have h3 : ρ l v - v ∈ Y₁ ⊓ C := ⟨h1, h2⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot, sub_eq_zero] at h3
    exact h3
  have : Y₂ = Y₁ := by
    calc Y₂ = (Y₁ ⊔ C) ⊓ Y₂ := by rw [hc.sup_eq_top, top_inf_eq]
      _ = Y₁ ⊔ C ⊓ Y₂ := sup_inf_assoc_of_le C h12
      _ = Y₁ := by rw [hC0, sup_bot_eq]
  exact this.le

section Length

variable {H K : Type} [Group H] [Group K]

theorem exists_irreducible_sub {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X]
    (π : Representation (ZMod 2) H X) {U₀ : Submodule (ZMod 2) X}
    (hU₀ : ∀ h, ∀ u ∈ U₀, π h u ∈ U₀) (h0 : U₀ ≠ ⊥) :
    ∃ U : Subrepresentation π, U.toSubmodule ≤ U₀ ∧ U.toRepresentation.IsIrreducible := by
  classical
  obtain ⟨U, hUU₀, hU, hU0, hmin⟩ :=
    exists_min_sub (fun M : Submodule (ZMod 2) X => ∀ h, ∀ u ∈ M, π h u ∈ M) hU₀ h0
  refine ⟨⟨U, fun h v hv => hU h v hv⟩, hUU₀, ?_⟩
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨Submodule.nontrivial_iff_ne_bot.mpr hU0, fun M hM => ?_⟩
  by_cases hM0 : M = ⊥
  · exact Or.inl hM0
  · right
    have hinv : ∀ h, ∀ u ∈ M.map U.subtype, π h u ∈ M.map U.subtype := by
      rintro h _ ⟨m, hm, rfl⟩
      exact ⟨_, hM h m hm, rfl⟩
    have hne : M.map U.subtype ≠ ⊥ := fun h =>
      hM0 (Submodule.map_injective_of_injective U.injective_subtype
        (h.trans (Submodule.map_bot _).symm))
    have h1 := hmin (M.map U.subtype) (Submodule.map_subtype_le U M) hinv hne
    rw [eq_top_iff]
    rintro m -
    have hm : (m : X) ∈ M.map U.subtype := by
      rw [h1]
      exact m.2
    obtain ⟨m', hm', he⟩ := hm
    rwa [show m' = m from Subtype.ext he] at hm'

variable (ι : K →* H) (t : H)

theorem le_disp_of_forall_irreducible {c : ℕ}
    (hc : ∀ {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
      (σ : Representation (ZMod 2) H Y), σ.IsIrreducible → NoTrivSec (σ.comp ι) →
        c ≤ 2 * (Module.finrank (ZMod 2) Y - Module.finrank (ZMod 2) (repFixedSpace σ {t})))
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X] [Nontrivial X]
    (π : Representation (ZMod 2) H X) (h : NoTrivSec (π.comp ι)) :
    c ≤ 2 * (Module.finrank (ZMod 2) X - Module.finrank (ZMod 2) (repFixedSpace π {t})) := by
  obtain ⟨U, -, hU⟩ :=
    exists_irreducible_sub π (U₀ := ⊤) (fun _ _ _ => Submodule.mem_top) top_ne_bot
  have h1 := hc U.toRepresentation hU (h.sub U)
  have h2 := codim_sub_quot π U {t}
  omega

theorem isIrreducible_of_disp_lt {c : ℕ}
    (hc : ∀ {Y : Type} [AddCommGroup Y] [Module (ZMod 2) Y] [Finite Y]
      (σ : Representation (ZMod 2) H Y), σ.IsIrreducible → NoTrivSec (σ.comp ι) →
        c ≤ 2 * (Module.finrank (ZMod 2) Y - Module.finrank (ZMod 2) (repFixedSpace σ {t})))
    {X : Type} [AddCommGroup X] [Module (ZMod 2) X] [Finite X] [Nontrivial X]
    (π : Representation (ZMod 2) H X) (h : NoTrivSec (π.comp ι))
    (hlt : 2 * (Module.finrank (ZMod 2) X - Module.finrank (ZMod 2) (repFixedSpace π {t})) <
      2 * c) :
    π.IsIrreducible := by
  rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
  refine ⟨inferInstance, fun U hU => ?_⟩
  by_contra hne
  rw [not_or] at hne
  let U' : Subrepresentation π := ⟨U, fun g v hv => hU g v hv⟩
  haveI : Nontrivial U'.toSubmodule := Submodule.nontrivial_iff_ne_bot.mpr hne.1
  haveI : Nontrivial (X ⧸ U'.toSubmodule) := Submodule.Quotient.nontrivial_iff.mpr hne.2
  haveI : Finite (X ⧸ U'.toSubmodule) := Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have h1 := le_disp_of_forall_irreducible ι t hc U'.toRepresentation (h.sub U')
  have h2 := le_disp_of_forall_irreducible ι t hc U'.quotient (h.quot U')
  have h3 := codim_sub_quot π U' {t}
  omega

end Length

section Split

variable {H K X : Type} [Group H] [Group K] [AddCommGroup X] [Module (ZMod 2) X] [Finite X]

theorem irreducible_or_split (π : Representation (ZMod 2) H X) (hπ : π.IsIrreducible) (ι : K →* H)
    (t : H) (htt : t * t = 1) (hnorm : ∀ k, ∃ k', ι k * t = t * ι k')
    (hgen : ∀ U : Submodule (ZMod 2) X, (∀ k, ∀ u ∈ U, π (ι k) u ∈ U) → (∀ u ∈ U, π t u ∈ U) →
      ∀ h, ∀ u ∈ U, π h u ∈ U) :
    Representation.IsIrreducible (π.comp ι) ∨
      ∃ Y : Submodule (ZMod 2) X, (∀ k, ∀ y ∈ Y, π (ι k) y ∈ Y) ∧ Y ≠ ⊥ ∧
        Module.finrank (ZMod 2) Y ≤
          Module.finrank (ZMod 2) X - Module.finrank (ZMod 2) (repFixedSpace π {t}) := by
  classical
  obtain ⟨hnt, hirr⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff π).mp hπ
  let PK : Submodule (ZMod 2) X → Prop := fun M => ∀ k, ∀ y ∈ M, π (ι k) y ∈ M
  obtain ⟨Y, -, hY, hY0, hmin⟩ := exists_min_sub PK (U₀ := ⊤) (fun _ _ _ => Submodule.mem_top)
    top_ne_bot
  have htt' : ∀ x, π t (π t x) = x := fun x => by
    rw [← Module.End.mul_apply, ← map_mul, htt, map_one, Module.End.one_apply]
  let tY := Y.map (π t)
  have htYK : PK tY := by
    rintro k _ ⟨y, hy, rfl⟩
    obtain ⟨k', hk'⟩ := hnorm k
    refine ⟨π (ι k') y, hY k' y hy, ?_⟩
    show π t (π (ι k') y) = π (ι k) (π t y)
    rw [← Module.End.mul_apply, ← map_mul, ← hk', map_mul, Module.End.mul_apply]
  have hsupK : PK (Y ⊔ tY) := fun k y hy => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add]
    exact Submodule.add_mem_sup (hY k a ha) (htYK k b hb)
  have hsupt : ∀ u ∈ Y ⊔ tY, π t u ∈ Y ⊔ tY := fun u hu => by
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
    rw [map_add]
    obtain ⟨c, hc, rfl⟩ := hb
    rw [htt']
    exact add_mem (Submodule.mem_sup_right ⟨a, ha, rfl⟩) (Submodule.mem_sup_left hc)
  by_cases hint : Y ⊓ tY = ⊥
  · right
    refine ⟨Y, hY, hY0, ?_⟩
    have hdisj : Y ⊓ repFixedSpace π {t} = ⊥ := by
      rw [eq_bot_iff]
      rintro y ⟨hyY, hyF⟩
      have : y ∈ Y ⊓ tY := ⟨hyY, ⟨y, hyY, hyF t rfl⟩⟩
      rw [hint] at this
      exact this
    have h1 := Submodule.finrank_sup_add_finrank_inf_eq Y (repFixedSpace π {t})
    rw [hdisj, finrank_bot] at h1
    have h2 := Submodule.finrank_le (Y ⊔ repFixedSpace π {t})
    omega
  · left
    have hinfK : PK (Y ⊓ tY) := fun k y hy => ⟨hY k y hy.1, htYK k y hy.2⟩
    have hYt : Y ⊓ tY = Y := hmin _ inf_le_left hinfK hint
    have hle : Y ≤ tY := hYt ▸ inf_le_right
    have heq : Y = tY := Submodule.eq_of_le_of_finrank_le hle (Submodule.finrank_map_le _ _)
    have hYtinv : ∀ u ∈ Y, π t u ∈ Y := fun u hu => heq ▸ ⟨u, hu, rfl⟩
    have hYtop : Y = ⊤ := (hirr Y (hgen Y hY hYtinv)).resolve_left hY0
    rw [CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff]
    refine ⟨hnt, fun M hM => ?_⟩
    by_cases hM0 : M = ⊥
    · exact Or.inl hM0
    · exact Or.inr ((hmin M (hYtop ▸ le_top) hM hM0).trans hYtop)

end Split

theorem exists_le_disp_of_commute {G V : Type} [Group G] [AddCommGroup V] [Module (ZMod 2) V]
    [Finite V] (ρ : Representation (ZMod 2) G V) (hρ : Function.Injective ρ) {L : Subgroup G}
    {t : G} (ht1 : t ≠ 1) (hc : ∀ l ∈ L, t * l = l * t) :
    ∃ Y : Submodule (ZMod 2) V, (∀ l ∈ L, ∀ y ∈ Y, ρ l y ∈ Y) ∧ Y ≠ ⊥ ∧
      Module.finrank (ZMod 2) Y ≤
        Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) := by
  refine ⟨LinearMap.range (ρ t - 1), ?_, ?_, ?_⟩
  · rintro l hl _ ⟨v, rfl⟩
    refine ⟨ρ l v, ?_⟩
    simp only [LinearMap.sub_apply, Module.End.one_apply, map_sub]
    rw [← Module.End.mul_apply, ← map_mul, hc l hl, map_mul, Module.End.mul_apply]
  · intro h
    apply ht1
    apply hρ
    rw [map_one]
    apply LinearMap.ext
    intro v
    have : (ρ t - 1) v ∈ LinearMap.range (ρ t - 1) := ⟨v, rfl⟩
    rw [h, Submodule.mem_bot, LinearMap.sub_apply, sub_eq_zero] at this
    exact this
  · have h1 := LinearMap.finrank_range_add_finrank_ker (ρ t - 1)
    have hk : LinearMap.ker (ρ t - 1) = repFixedSpace ρ {t} := by
      ext v
      simp [LinearMap.mem_ker, mem_repFixedSpace, sub_eq_zero]
    rw [hk] at h1
    omega

section LT

variable {G : Type} [Group G] (L : Subgroup G) (t : G)

@[expose] def incL : ↥L →* ↥(L ⊔ zpowers t) := Subgroup.inclusion le_sup_left

@[expose] def tElt : ↥(L ⊔ zpowers t) := ⟨t, mem_sup_right (mem_zpowers t)⟩

@[simp] theorem coe_incL (l : ↥L) : ((incL L t l : ↥(L ⊔ zpowers t)) : G) = l := rfl

@[simp] theorem coe_tElt : ((tElt L t : ↥(L ⊔ zpowers t)) : G) = t := rfl

theorem exists_eq_incL [L.Normal] (ht : t * t = 1) (h : ↥(L ⊔ zpowers t)) :
    ∃ l : ↥L, h = incL L t l ∨ h = incL L t l * tElt L t := by
  have hh : (h : G) ∈ ((L ⊔ zpowers t : Subgroup G) : Set G) := h.2
  rw [Subgroup.normal_mul] at hh
  obtain ⟨x, hx, z, hz, hxz⟩ := Set.mem_mul.mp hh
  obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hz
  have hk : t ^ k = t ^ (k % 2) := by
    conv_lhs => rw [← Int.mul_ediv_add_emod k 2]
    rw [zpow_add, zpow_mul, show t ^ (2 : ℤ) = 1 by rw [zpow_two, ht], one_zpow, one_mul]
  refine ⟨⟨x, hx⟩, ?_⟩
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    apply Subtype.ext
    rw [coe_incL, ← hxz, hk, h0, zpow_zero, mul_one]
  · right
    apply Subtype.ext
    rw [Subgroup.coe_mul, coe_incL, coe_tElt, ← hxz, hk, h1, zpow_one]

theorem exists_incL_mul_tElt [hL : L.Normal] (l : ↥L) :
    ∃ l' : ↥L, incL L t l * tElt L t = tElt L t * incL L t l' := by
  refine ⟨⟨t⁻¹ * l * t, by simpa using hL.conj_mem l l.2 t⁻¹⟩, Subtype.ext ?_⟩
  simp only [Subgroup.coe_mul, coe_incL, coe_tElt]
  group

theorem invariant_of_incL_tElt [L.Normal] (ht : t * t = 1) {X : Type} [AddCommGroup X]
    [Module (ZMod 2) X] (π : Representation (ZMod 2) ↥(L ⊔ zpowers t) X) (U : Submodule (ZMod 2) X)
    (hU : ∀ l, ∀ u ∈ U, π (incL L t l) u ∈ U) (hUt : ∀ u ∈ U, π (tElt L t) u ∈ U) :
    ∀ h, ∀ u ∈ U, π h u ∈ U := by
  intro h u hu
  obtain ⟨l, rfl | rfl⟩ := exists_eq_incL L t ht h
  · exact hU l u hu
  · rw [map_mul, Module.End.mul_apply]
    exact hU l _ (hUt u hu)

end LT

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm
