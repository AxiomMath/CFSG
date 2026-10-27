module

public import CFSG.Quasithin.EmptyFaithful.S146F5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem IsDec12.isSylowTwoOf_tU (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDec12 T M H p H₀ H₁ H₂ t) {u : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T) (huT : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u) :
    IsSylowTwoOf (tU T u) (H ⊓ Subgroup.centralizer ({u} : Set G)) := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHG : H ≤ mcOf T := S.le_mcOf hH
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hT₀ : IsSylowTwoOf (T ⊓ H₀) H₀ := B6.isSylowTwoOf_inf_normal hTsyl h.le h.le_normalizer_H₀
  have hAH₀ := h.centralizerMod_le S hred hu huZ
  have hTeq := h.tZero_eq S hred hu huZ huT
  have hT₀A : T ⊓ H₀ ≤ centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) := by
    rw [← h.inf_normalizer_eq hTH, ← hTeq]
    exact centralizerMod_mono_left _ hTH
  have hTA := B6.isSylowTwoOf_mono hT₀ hT₀A hAH₀
  have hKA : H ⊓ Subgroup.centralizer ({u} : Set G) ≤
      centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) := by
    rintro x ⟨hxH, hxc⟩
    refine ⟨hxH, S.normalizer_Z.ge (hHG hxH), fun w hw => ?_⟩
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hcomm : Commute u x := Subgroup.mem_centralizer_iff.mp hxc u rfl
    have : x * u ^ k * x⁻¹ * (u ^ k)⁻¹ = 1 := by
      have h1 : Commute (u ^ k) x := hcomm.zpow_left k
      rw [← h1.eq]
      group
    rw [this]
    exact Subgroup.one_mem _
  have hAK : centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u) ≤
      Subgroup.normalizer ((H ⊓ Subgroup.centralizer ({u} : Set G) : Subgroup G) : Set G) := by
    refine S146A.le_normalizer_of_forall_conj_mem fun a ha k hk => ?_
    obtain ⟨hkH, hkc⟩ := hk
    have haH : a ∈ H := ha.1
    have ha' := (centralizerMod (quasithinOmegaOneCenter T) H (Subgroup.zpowers u)).inv_mem ha
    have hz₂ : a⁻¹ * u * a⁻¹⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := ha'.2.2 u (Subgroup.mem_zpowers u)
    refine ⟨H.mul_mem (H.mul_mem haH hkH) (H.inv_mem haH), ?_⟩
    show a * k * a⁻¹ ∈ Subgroup.centralizer ({u} : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    subst hw
    set z₂ := a⁻¹ * w * a⁻¹⁻¹ * w⁻¹ with hz₂def
    have hb : a⁻¹ * w * a = z₂ * w := by rw [hz₂def]; group
    have hkz : k * z₂ = z₂ * k := S146T.comm_Z (hHG hkH) hz₂
    have hwk : w * k = k * w := Subgroup.mem_centralizer_iff.mp hkc w rfl
    have hmid : (a⁻¹ * w * a) * k = k * (a⁻¹ * w * a) := by
      rw [hb]
      calc z₂ * w * k = z₂ * (w * k) := by group
        _ = z₂ * (k * w) := by rw [hwk]
        _ = (z₂ * k) * w := by group
        _ = (k * z₂) * w := by rw [hkz]
        _ = k * (z₂ * w) := by group
    calc w * (a * k * a⁻¹) = a * ((a⁻¹ * w * a) * k) * a⁻¹ := by group
      _ = a * (k * (a⁻¹ * w * a)) * a⁻¹ := by rw [hmid]
      _ = (a * k * a⁻¹) * w := by group
  have hsyl := B6.isSylowTwoOf_inf_normal hTA hKA hAK
  have heq : T ⊓ H₀ ⊓ (H ⊓ Subgroup.centralizer ({u} : Set G)) = tU T u := by
    ext x
    constructor
    · rintro ⟨⟨hxT, -⟩, -, hxc⟩
      exact ⟨hxT, hxc⟩
    · rintro ⟨hxT, hxc⟩
      have hx0 : x ∈ tZero T u := tU_le_tZero T u ⟨hxT, hxc⟩
      rw [hTeq, h.inf_normalizer_eq hTH] at hx0
      exact ⟨hx0, hTH hxT, hxc⟩
  rwa [heq] at hsyl

end Sylow

section Inputs

variable {G : Type} [Group G]

@[expose] def Stage14614At (T H : Subgroup G) (p : ℕ) : Prop :=
  (conjClosure (oTwoUpper H) (mcOf T) = oTwoUpper H ∧
      (p = 3 → ∀ r : ℕ, r.Prime → r ∣ Nat.card (mcOf T) → r = 2 ∨ r = 3)) ∨
  (p = 3 ∧ conjClosure (oTwoUpper H) (mcOf T) ∈ cComp (mcOf T) ∧
      ∃ n : ℕ, (n = 4 ∨ n = 5) ∧
        Nonempty (OTwoQuot (mcOf T) ≃* MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))) ∨
  (p = 3 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
      s ∉ Subgroup.normalizer (K₁ : Set G) ∧
      conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
      (Nonempty (OTwoQuot (mcOf T) ≃* (Equiv.Perm (Fin 5) ≀ᵣ Multiplicative (ZMod 2))) ∨
        Nonempty (OTwoQuot (mcOf T) ≃*
          (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2) ≀ᵣ Multiplicative (ZMod 2))))) ∨
  (p = 5 ∧ ∃ (K₁ : Subgroup G) (s : G), K₁ ∈ cComp (mcOf T) ∧ s ∈ T ∧
      s ∉ Subgroup.normalizer (K₁ : Set G) ∧
      conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁ ∧
      mcOf T = conjClosure (oTwoUpper H) (mcOf T) ⊔ T ∧
      (imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T))).index ∣ 32 ∧
      Nonempty (OTwoQuot K₁ ≃* Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 4)))

theorem stage14614At_of (h : Stage14614) {G : Type} [Group G] [Finite G] {T M : Subgroup G}
    (S : Setting146 G T M) {H PQ : Subgroup G} {p : ℕ} (hred : IsRedCE T M H PQ p)
    (hmax : PMaximal T M p) : Stage14614At T H p :=
  h G T M S H PQ p hred hmax

end Inputs

@[expose] def Input14617Mod : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p →
      ∀ (H₀ H₁ H₂ : Subgroup G) (t : G), IsDec12 T M H p H₀ H₁ H₂ t →
        ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
          ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T

@[expose] def Input14617Fstar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Setting146 G T M →
    ∀ (H PQ : Subgroup G) (p : ℕ), IsRedCE T M H PQ p → PMaximal T M p →
      Stage14614At T H p → oTwoUpper H ≤ oTwoFstarIn (mcOf T)

section U2

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

theorem not_mem_centralizer_pCoreOf_mcOf (S : Setting146 G T M) (h5 : Stage1461Five)
    {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T))
    {v : G} (hv : v ∈ conjClosure (VZ T M) H) {x : G} (hx : x ∈ oTwoUpper H) (hxv : x * v * x⁻¹ ≠ v) :
    v ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
  intro hvc
  have hH : IsHTM T M H := hred.isHTM
  have hchar : CharTwo (mcOf T) := charTwo_of_inH' S.hyp.qtke S.hyp.sylow S.isHTM_mcOf.1
  have hvG : v ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH hv
  have hvQ : v ∈ pCoreOf 2 (mcOf T) := hchar ⟨hvG, hvc⟩
  have hvZ : v ∈ centerOf (pCoreOf 2 (mcOf T)) := Subgroup.mem_inf.mpr ⟨hvQ, hvc⟩
  have hvsq : v ^ 2 = 1 := isElemAbelian_pow_eq_one (S.lemma_14_5_15_two hH) hv
  have hvΩ : v ∈ omegaOneCenterOf (pCoreOf 2 (mcOf T)) := Subgroup.subset_closure ⟨hvZ, hvsq⟩
  have hxC := h5 G T M S (mcOf T) S.isHTM_mcOf (hF hx)
  have hcomm : v * x = x * v := Subgroup.mem_centralizer_iff.mp hxC v hvΩ
  apply hxv
  calc x * v * x⁻¹ = (x * v) * x⁻¹ := rfl
    _ = (v * x) * x⁻¹ := by rw [hcomm]
    _ = v := by group

theorem IsDec12.not_mem_centralizer_pCore (S : Setting146 G T M) (h5 : Stage1461Five) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T)) {u : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T) :
    u ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
  obtain ⟨x, hx1, hxu⟩ := hMod u hu huZ
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  refine not_mem_centralizer_pCoreOf_mcOf S h5 hred hF (uHi_le_conjClosure hH₁H hu)
    (oTwoUpper_mono hH₁H hx1) fun heq => hxu ?_
  have : x * u * x⁻¹ * u⁻¹ = 1 := by rw [heq]; group
  rw [this]
  exact Subgroup.one_mem _

theorem IsDec12.not_mem_centralizer_pCore_mul (S : Setting146 G T M) (h5 : Stage1461Five)
    {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T)) {u : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u) {s : G} (hsT : s ∈ T)
    (hs : s ∉ tZero T u) :
    u * (s * u * s⁻¹) ∉ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hH₂H : H₂ ≤ H := h.le₂.trans h.le
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) := le_normalizer_conjClosure _ _
  have hTeq := h.tZero_eq S hred hu huZ huT
  have hs0 : s ∉ H₀ := fun hs0 => hs (by rw [hTeq]; exact ⟨hsT, h.H₀_le_normalizer_H₁ hs0⟩)
  have hconj := h.conjSub_uHi_of_not_mem S hred (hTH hsT) hs0
  have hu' : s * u * s⁻¹ ∈ uHi T M H H₂ := by
    rw [← hconj]
    exact mem_conjSub.mpr (by simpa [mul_assoc] using hu)
  obtain ⟨x, hx1, hxu⟩ := hMod u hu huZ
  have hxH₁ : x ∈ H₁ := oTwoUpper_le H₁ hx1
  have hc₂ : x * (s * u * s⁻¹) * x⁻¹ * (s * u * s⁻¹)⁻¹ ∈ quasithinOmegaOneCenter T := by
    have h2 := (quasithinOmegaOneCenter T).inv_mem
      (h.cent₂ (Subgroup.commutator_mem_commutator hu' hxH₁))
    rw [commutatorElement_inv] at h2
    simpa [commutatorElement_def] using h2
  have huU : u ∈ conjClosure (VZ T M) H := uHi_le_conjClosure hH₁H hu
  have hu'U : s * u * s⁻¹ ∈ conjClosure (VZ T M) H :=
    (Subgroup.mem_normalizer_iff.mp (hHU (hTH hsT)) u).mp huU
  refine not_mem_centralizer_pCoreOf_mcOf S h5 hred hF
    ((conjClosure (VZ T M) H).mul_mem huU hu'U) (oTwoUpper_mono hH₁H hx1) fun heq => ?_
  have huG : u ∈ mcOf T := S.mem_mcOf_of_mem_conjClosure hH huU
  have hcen : u * (x * (s * u * s⁻¹) * x⁻¹ * (s * u * s⁻¹)⁻¹) =
      (x * (s * u * s⁻¹) * x⁻¹ * (s * u * s⁻¹)⁻¹) * u := S146T.comm_Z huG hc₂
  have e : x * (u * (s * u * s⁻¹)) * x⁻¹ * (u * (s * u * s⁻¹))⁻¹ =
      (x * u * x⁻¹ * u⁻¹) * (u * (x * (s * u * s⁻¹) * x⁻¹ * (s * u * s⁻¹)⁻¹) * u⁻¹) := by group
  have e1 : u * (x * (s * u * s⁻¹) * x⁻¹ * (s * u * s⁻¹)⁻¹) * u⁻¹ =
      x * (s * u * s⁻¹) * x⁻¹ * (s * u * s⁻¹)⁻¹ := by
    rw [hcen]; group
  have h1 : x * (u * (s * u * s⁻¹)) * x⁻¹ * (u * (s * u * s⁻¹))⁻¹ = 1 := by
    rw [heq]; group
  rw [e, e1] at h1
  apply hxu
  have : x * u * x⁻¹ * u⁻¹ = (x * (s * u * s⁻¹) * x⁻¹ * (s * u * s⁻¹)⁻¹)⁻¹ := by
    rw [eq_inv_iff_mul_eq_one]; exact h1
  rw [this]
  exact (quasithinOmegaOneCenter T).inv_mem hc₂

theorem IsDec12.isInvU_of_fixed (S : Setting146 G T M) (h5 : Stage1461Five) (h16 : Stage14616)
    {PQ : Subgroup G} (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t)
    (hMod : ∀ u ∈ uHi T M H H₁, u ∉ quasithinOmegaOneCenter T →
      ∃ x ∈ oTwoUpper H₁, x * u * x⁻¹ * u⁻¹ ∉ quasithinOmegaOneCenter T)
    (hF : oTwoUpper H ≤ oTwoFstarIn (mcOf T)) {u : G} (hu : u ∈ uHi T M H H₁)
    (huZ : u ∉ quasithinOmegaOneCenter T)
    (huT : T ⊓ Subgroup.normalizer (H₁ : Set G) ≤ tZero T u) : IsInvU T M H u := by
  have hTeq := h.tZero_eq S hred hu huZ huT
  obtain ⟨hidx, hnorm⟩ := h16 G T M S H PQ p hred hmax H₀ H₁ H₂ t h
  refine ⟨uHi_le_conjClosure (h.le₁.trans h.le) hu, h.isSylowTwoOf_tU S hred hu huZ huT, ?_,
    h.not_mem_centralizer_pCore S h5 hred hMod hF hu huZ,
    fun s hsT hs => h.not_mem_centralizer_pCore_mul S h5 hred hMod hF hu huZ huT hsT hs, ?_⟩
  · rw [hTeq]
    exact hidx
  · rw [hTeq]
    exact hnorm

end U2

end CFSG.Quasithin
