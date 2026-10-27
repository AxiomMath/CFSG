module

public import CFSG.Quasithin.Vol2.Ch4Sec3C57Gen
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCStd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCSplit
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13.Ch4.C57

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.AppC
  CFSG.QuasithinUnique.A5.Delta5 Equiv
open scoped commutatorElement

@[expose] def NormNT (a b : Perm (Fin 5)) : Prop :=
  a * a = 1 ∧ b * b = 1 ∧ a * b = b * a ∧ four a b ≠ {1} ∧
    ∀ σ ∈ Dset, ∀ g ∈ four a b, σ * g * σ⁻¹ ∈ four a b

instance (a b : Perm (Fin 5)) : Decidable (NormNT a b) := by unfold NormNT; infer_instance

@[expose] def PairOK (a b c d : Perm (Fin 5)) : Prop :=
  c * c = 1 → d * d = 1 → c * d = d * c →
    (four a b).card * (fixOf c d).card = 16 → (four c d).card * (fixOf a b).card = 16 →
      four a b = Eset

instance (a b c d : Perm (Fin 5)) : Decidable (PairOK a b c d) := by
  unfold PairOK; infer_instance

theorem fin_pair : ∀ a ∈ Dset, ∀ b ∈ Dset, NormNT a b → ∀ c ∈ Dset, ∀ d ∈ Dset,
    PairOK a b c d := by
  decide +kernel

@[expose] def partner (σ : Perm (Fin 5)) : Perm (Fin 5) :=
  if σ = swap 0 1 then swap 2 3 else swap 0 1

theorem fin_comm : ∀ σ ∈ Eset, σ ≠ 1 → ∀ w w' : Fin 5 → ZMod 2, pact σ w = w →
    pact (partner σ) w' = w' → pact (partner σ) w + w' = pact σ w' + w →
    pact (swap 0 1) w = w ∧ pact (swap 2 3) w = w := by
  unfold partner
  decide +kernel

theorem rho_mem_Dset : swap (0 : Fin 5) 2 * swap 1 3 ∈ Dset := by decide +kernel

theorem rho_conj :
    swap (0 : Fin 5) 2 * swap 1 3 * swap 0 1 * (swap 0 2 * swap 1 3)⁻¹ = swap 2 3 ∧
      swap (0 : Fin 5) 2 * swap 1 3 * swap 2 3 * (swap 0 2 * swap 1 3)⁻¹ = swap 0 1 := by
  decide +kernel

theorem swaps_ne : swap (0 : Fin 5) 1 ≠ swap 2 3 ∧ swap (0 : Fin 5) 1 ≠ 1 ∧
    swap (2 : Fin 5) 3 ≠ 1 := by
  decide +kernel

variable {G : Type} [Group G] [Finite G] {K : Subgroup G}

omit [Finite G] in
theorem im_conj_mem (D : PiData K) {S A : Subgroup G}
    (hSA : S ≤ Subgroup.normalizer (A : Set G)) :
    ∀ σ ∈ D.im S, ∀ g ∈ D.im A, σ * g * σ⁻¹ ∈ D.im A := by
  intro σ hσ g hg
  obtain ⟨s, hs, rfl⟩ := (D.mem_im).1 hσ
  obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
  have h1 : (s : G) * y * (s : G)⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hSA hs) y).mp hy
  have : D.π s * D.π y * (D.π s)⁻¹ = D.π (s * y * s⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [this]
  exact D.pi_mem_im (K := A) (y := s * y * s⁻¹) (by simpa using h1)

omit [Finite G] in
theorem le_normalizer_thompsonJ (R : Subgroup G) :
    R ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
  intro r hr
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => thompsonJ_conj_mem hr hy, fun hy => ?_⟩
  have := thompsonJ_conj_mem (inv_mem hr) hy
  simpa [mul_assoc] using this

namespace Setup

variable {H M₀ R : Subgroup G} (h : Setup H M₀ R K)
include h

theorem exists_thompsonJ_pi_ne_one (P : A5Pi K) :
    ∃ y : ↥(Subgroup.normalizer (K : Set G)), (y : G) ∈ thompsonJ R ∧ P.π y ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hLQ : ¬ K ≤ blockQ K := by
    intro hle
    have : Nontrivial (alternatingGroup (Fin 5)) :=
      Finite.one_lt_card_iff_nontrivial.1 (by rw [A5.Delta5.a5_card]; norm_num)
    obtain ⟨a, ha⟩ := exists_ne (1 : alternatingGroup (Fin 5))
    obtain ⟨ℓ, rfl⟩ := P.hα a
    apply ha
    have h1 : ℓ ∈ P.α.ker := by
      rw [P.hαk, mem_pCore_iff_mem_blockQ]
      exact hle ℓ.2
    exact h1
  apply hLQ
  have hJR : thompsonJ R ≤ R := GammaExtra.thompsonJ_le_self R
  have hLQ' : K ⊓ Subgroup.centralizer (blockU K : Set G) = pCoreOf 2 K :=
    C1.inf_centralizer_blockU_eq h.short le_rfl Subgroup.le_normalizer
      (fun g hg => ⟨0, by simpa using hg⟩)
  calc K = ⁅K, thompsonJ R⁆ := h.thompson.symm
    _ ≤ blockQ K := by
      rw [Subgroup.commutator_le]
      intro ℓ hℓ y hy
      have hyN : y ∈ Subgroup.normalizer (K : Set G) := h.R_le_normalizer_K (hJR hy)
      have hyL : y * ℓ⁻¹ * y⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp hyN _).mp (inv_mem hℓ)
      have hcom : ⁅ℓ, y⁆ = ℓ * (y * ℓ⁻¹ * y⁻¹) := by simp [commutatorElement_def, mul_assoc]
      have hcL : ⁅ℓ, y⁆ ∈ K := by rw [hcom]; exact mul_mem hℓ hyL
      have hπ : P.π (⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
          ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
        have hy1 := hcon ⟨y, hyN⟩ hy
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, hy1]
        simp
      have hc := (P.hker _).1 hπ
      have hcC : ⁅ℓ, y⁆ ∈ Subgroup.centralizer (blockU K : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro u hu
        have h1 := hc u hu
        have h2 : (((⟨ℓ, Subgroup.le_normalizer hℓ⟩ * ⟨y, hyN⟩ *
            ⟨ℓ, Subgroup.le_normalizer hℓ⟩⁻¹ * ⟨y, hyN⟩⁻¹ :
              ↥(Subgroup.normalizer (K : Set G))) : ↥(Subgroup.normalizer (K : Set G))) : G) =
            ⁅ℓ, y⁆ := by
          simp [commutatorElement_def]
        rw [h2] at h1
        calc u * ⁅ℓ, y⁆ = (⁅ℓ, y⁆ * u * ⁅ℓ, y⁆⁻¹) * ⁅ℓ, y⁆ := by rw [h1]
          _ = ⁅ℓ, y⁆ * u := by group
      have h3 : ⁅ℓ, y⁆ ∈ K ⊓ Subgroup.centralizer (blockU K : Set G) := ⟨hcL, hcC⟩
      rw [hLQ'] at h3
      exact h3

theorem swapGen_imJ (D : PiData K) :
    ∀ g ∈ D.im (thompsonJ R),
      g ∈ Subgroup.closure {s : Perm (Fin 5) | s ∈ D.im (thompsonJ R) ∧ s.IsSwap} := by
  have hU := isElemAbelian_blockU h.short
  set Cl := Subgroup.closure {s : Perm (Fin 5) | s ∈ D.im (thompsonJ R) ∧ s.IsSwap} with hCl
  have hW : thompsonJ R ≤ (Cl.comap D.π).map (Subgroup.normalizer (K : Set G)).subtype := by
    refine iSup_le fun A => iSup_le fun hA => ?_
    intro a ha
    have haN : a ∈ Subgroup.normalizer (K : Set G) := h.R_le_normalizer_K (hA.1 ha)
    refine Subgroup.mem_map.2 ⟨⟨a, haN⟩, ?_, rfl⟩
    show D.π ⟨a, haN⟩ ∈ Cl
    have hmem : D.π ⟨a, haN⟩ ∈ D.im A := D.pi_mem_im ha
    have := D.swapGen_im hU h.blockU_le_R h.R_le_normalizer_K hA _ hmem
    refine Subgroup.closure_mono ?_ this
    intro s hs
    exact ⟨D.im_mono (GammaExtra.le_thompsonJ hA) hs.1, hs.2⟩
  intro g hg
  obtain ⟨y, hy, rfl⟩ := (D.mem_im).1 hg
  obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.1 (hW hy)
  have : y' = y := Subtype.ext hyy
  rw [this] at hy'
  exact hy'

theorem card_im_R (P : A5Pi K) : Nat.card (P.im R) = 8 := by
  classical
  let D : PiData K := P.toPiData
  have hHN := h.le_normalizer_K
  obtain ⟨y₀, hy₀J, hy₀⟩ := h.exists_thompsonJ_pi_ne_one P
  have hJ1 : ∃ j ∈ D.im (thompsonJ R), j ≠ 1 := ⟨D.π y₀, D.pi_mem_im hy₀J, hy₀⟩
  obtain ⟨t, htJ, htsw⟩ := exists_swap_of_swapGen _ hJ1 (h.swapGen_imJ D)
  have hJR : thompsonJ R ≤ R := GammaExtra.thompsonJ_le_self R
  have hsurj : Function.Surjective (D.π.comp (Subgroup.inclusion hHN)) := by
    intro σ
    by_cases hs : Equiv.Perm.sign σ = 1
    · obtain ⟨ℓ, hℓ⟩ := P.hα ⟨σ, Equiv.Perm.mem_alternatingGroup.mpr hs⟩
      refine ⟨⟨ℓ, h.K_le ℓ.2⟩, ?_⟩
      have := P.hπα ℓ ℓ.2
      rw [hℓ] at this
      exact this
    · obtain ⟨y, hyJ, hyt⟩ := (D.mem_im).1 htJ
      have hsg : Equiv.Perm.sign (σ * t⁻¹) = 1 := by
        obtain ⟨a, b, hab, rfl⟩ := htsw
        rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_inv, Equiv.Perm.sign_swap hab]
        rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h' | h'
        · exact absurd h' hs
        · rw [h']; decide
      obtain ⟨ℓ, hℓ⟩ := P.hα ⟨σ * t⁻¹, Equiv.Perm.mem_alternatingGroup.mpr hsg⟩
      have hyH : (y : G) ∈ H := h.R_le_H (hJR hyJ)
      refine ⟨⟨ℓ, h.K_le ℓ.2⟩ * ⟨y, hyH⟩, ?_⟩
      have h1 := P.hπα ℓ ℓ.2
      rw [hℓ] at h1
      show D.π (⟨(ℓ : G), hHN (h.K_le ℓ.2)⟩ * ⟨(y : G), y.2⟩) = σ
      rw [map_mul, hyt]
      have h3 : D.π ⟨(ℓ : G), hHN (h.K_le ℓ.2)⟩ = σ * t⁻¹ := h1
      rw [h3]
      exact inv_mul_cancel_right σ t
  have hS := h.sylow
  have hS' : IsPGroup 2 (R.subgroupOf H) :=
    hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
  let Q : Sylow 2 H := hS'.toSylow hS.2.2
  have h1 := sylow_card_perm_five (Q.mapSurjective hsurj)
  have h2 : ((Q.mapSurjective hsurj : Sylow 2 (Equiv.Perm (Fin 5))) :
      Subgroup (Equiv.Perm (Fin 5))) =
      (R.subgroupOf H).map (D.π.comp (Subgroup.inclusion hHN)) := by
    rw [Sylow.coe_mapSurjective]
    rfl
  have h3 : (R.subgroupOf H).map (D.π.comp (Subgroup.inclusion hHN)) = D.im R := by
    ext g
    rw [D.mem_im, Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact ⟨Subgroup.inclusion hHN x, Subgroup.mem_subgroupOf.1 hx, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨⟨(y : G), hS.1 hy⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  show Nat.card (D.im R) = 8
  rw [← h3, ← h2]
  exact h1

theorem exists_std (h5 : IsAltType K 5) :
    ∃ P : A5Pi K, P.im (thompsonJ R) = Estd ∧ P.im R = Dstd := by
  obtain ⟨P⟩ := nonempty_a5pi h.short h5
  let D : PiData K := P.toPiData
  obtain ⟨y₀, hy₀J, hy₀⟩ := h.exists_thompsonJ_pi_ne_one P
  have hJ1 : ∃ j ∈ D.im (thompsonJ R), j ≠ 1 := ⟨D.π y₀, D.pi_mem_im hy₀J, hy₀⟩
  have hJR : thompsonJ R ≤ R := GammaExtra.thompsonJ_le_self R
  have hJn : ∀ d ∈ D.im R, ∀ j ∈ D.im (thompsonJ R), d * j * d⁻¹ ∈ D.im (thompsonJ R) :=
    im_conj_mem D (le_normalizer_thompsonJ R)
  obtain ⟨τ₁, τ₂, hτ₁, hτ₂, hdisj, hJeq, -, -⟩ :=
    swap_core (D.im R) (D.im (thompsonJ R)) (h.card_im_R P) (D.im_mono hJR) hJn hJ1
      (h.swapGen_imJ D)
  obtain ⟨ρ, hρ1, hρ2⟩ := swaps_conj τ₁ τ₂ hτ₁ hτ₂ hdisj
  have hcl : (Subgroup.closure ({τ₁, τ₂} : Set (Perm (Fin 5)))).map (MulAut.conj ρ).toMonoidHom =
      Estd := by
    rw [MonoidHom.map_closure, ← closure_swaps]
    congr 1
    ext g
    simp only [Set.mem_image, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨x, rfl | rfl, rfl⟩
      · exact Or.inl hρ1
      · exact Or.inr hρ2
    · rintro (rfl | rfl)
      · exact ⟨τ₁, Or.inl rfl, hρ1⟩
      · exact ⟨τ₂, Or.inr rfl, hρ2⟩
  have hJ' : (P.conj ρ).im (thompsonJ R) = Estd := by rw [A5Pi.im_conj, hJeq, hcl]
  have hnorm' : ∀ d ∈ (P.conj ρ).im R, ∀ j ∈ (P.conj ρ).im (thompsonJ R),
      d * j * d⁻¹ ∈ (P.conj ρ).im (thompsonJ R) :=
    im_conj_mem (P.conj ρ).toPiData (le_normalizer_thompsonJ R)
  have hle : (P.conj ρ).im R ≤ Dstd := by
    intro d hd
    rw [mem_Dstd, mem_Dset]
    intro x hx
    have := hnorm' d hd x (by rw [hJ']; exact hx)
    rwa [hJ'] at this
  have hcard : Nat.card ((P.conj ρ).im R) = 8 := by
    rw [A5Pi.im_conj, Subgroup.card_map_of_injective (MulAut.conj ρ).injective]
    exact h.card_im_R P
  exact ⟨P.conj ρ, hJ', Subgroup.eq_of_le_of_card_ge hle (by rw [Dstd_card, hcard])⟩

end Setup

end CFSG.Quasithin.H13.Ch4.C57
