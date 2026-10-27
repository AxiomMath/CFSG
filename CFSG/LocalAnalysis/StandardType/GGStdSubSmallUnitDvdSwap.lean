module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdPair
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdDelta
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperUnitary

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

variable {K : Type} [Field K] [Finite K] {n d p : ℕ} {L' : Type} [Group L']
  {φ : ↥(unitarySU 2 n K d) →* L'}

theorem swap_comm_diag {s t : Fin d} {τ : Fin d → Kˣ} (hτ : τ s = τ t) :
    permGL (Equiv.swap s t) * diagHom d τ = diagHom d τ * permGL (Equiv.swap s t) := by
  have h1 := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap s t) τ
  have h2 : τ ∘ (Equiv.swap s t).symm = τ := by
    funext k
    rw [Function.comp_apply, Equiv.symm_swap, Equiv.swap_apply_def]
    split_ifs with h3 h4
    · rw [h3, hτ]
    · rw [h4, hτ]
    · rfl
  rw [h2] at h1
  calc permGL (Equiv.swap s t) * diagHom d τ = permGL (Equiv.swap s t) * diagHom d τ *
        (permGL (Equiv.swap s t))⁻¹ * permGL (Equiv.swap s t) := by group
    _ = diagHom d τ * permGL (Equiv.swap s t) := by rw [h1]

theorem exists_swap_group (hM : Model φ) {s t : Fin d} (hst : s ≠ t) (hd : 3 ≤ d)
    {A : Subgroup (MulAut L')} (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    (hpair : ∀ a ∈ A, ∀ σ : Fin d → Kˣ, ActsU φ a σ → σ s = σ t) :
    ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U) ∧
      (∀ e : L', (∃ (g : ↥(unitarySU 2 n K d)) (τ : Fin d → Kˣ), φ g = e ∧
        (g : GL (Fin d) K) = diagHom d τ ∧ τ s = τ t) → e ∈ Subgroup.normalizer (U : Set L')) ∧
      ∀ S : Finset (Fin d), s ∈ S → t ∈ S → U ≤ (blockSU S).map φ := by
  set P : ↥(unitarySU 2 n K d) := IOneU.swapSU hM.field s t with hP
  have hPc : (P : GL (Fin d) K) = permGL (Equiv.swap s t) := rfl
  refine ⟨Subgroup.zpowers (φ P), ?_, ?_, ?_, ?_, ?_⟩
  · intro hbot
    rw [Subgroup.zpowers_eq_bot] at hbot
    apply IOneU.projMk_swapSU_ne_one hM.field hst
    exact (projMk_eq_one_iff (by omega)).mpr (hM.ker P hbot)
  · refine isPGroup_two_zpowers (k := 1) ?_
    rw [← map_pow, hP, IOneU.swapSU_sq hM.field s t, map_one]
  · intro a' ha' u hu
    obtain ⟨t', ht'⟩ := hdiag a' ha'
    obtain ⟨σ', -, hσ'⟩ := ActsU.of_actsDiagU ht'
    have hfix : a' (φ P) = φ P := by
      obtain ⟨hD, hact⟩ := hσ'
      have hc := swap_comm_diag (hpair a' ha' σ' ⟨hD, hact⟩)
      rw [hact P]
      congr 1
      apply Subtype.ext
      rw [coe_conjN, hPc, ← hc, mul_assoc, mul_inv_cancel, mul_one]
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    rw [map_zpow, hfix]
    exact Subgroup.zpow_mem_zpowers _ _
  · rintro e ⟨g, τ, rfl, hg, hτ⟩
    have hcomm : (g : GL (Fin d) K) * (P : GL (Fin d) K) = P * g := by
      rw [hg, hPc]
      exact (swap_comm_diag hτ).symm
    have h1 : φ g * φ P = φ P * φ g := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
    exact (Commute.zpow_left (show Commute (φ P) (φ g) from h1.symm) m).eq
  · intro S hs ht
    exact Subgroup.zpowers_le.mpr ⟨P, isBlockOn_permGL_swap hs ht, rfl⟩


omit [Finite K] in
theorem exists_swap_group_le_layer (hM : Model φ) (hn : 2 ≤ n) (hd : 3 ≤ d)
    {A : Subgroup (MulAut L')} (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiagU φ a t)
    {a : MulAut L'} (haA : a ∈ A) {σ : Fin d → Kˣ} (hσ : ActsU φ a σ)
    (hEcomp : IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a))
    {s t : Fin d} (hst : s ≠ t)
    (hpair : ∀ a' ∈ A, ∀ τ : Fin d → Kˣ, ActsU φ a' τ → τ s = τ t) :
    ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U) ∧
      U ≤ LargeEvenLayer (ggFix a) := by
  classical
  have : Finite K := hM.field.finite
  have : Finite L' := Finite.of_surjective φ hM.surj
  obtain ⟨U, hU1, hU2, hUA, -, hUS⟩ := exists_swap_group hM hst hd hdiag hpair
  have hts : σ t = σ s := (hpair a haA σ hσ).symm
  have hsS : s ∈ cls σ s := mem_cls.mpr rfl
  have htS : t ∈ cls σ s := mem_cls.mpr hts
  have hSc : 2 ≤ (cls σ s).card := by
    have h1 := Finset.card_le_card
      (show ({s, t} : Finset (Fin d)) ⊆ cls σ s from fun k hk => by
        rcases Finset.mem_insert.mp hk with rfl | hk
        · exact hsS
        · rw [Finset.mem_singleton.mp hk]
          exact htS)
    rwa [Finset.card_pair hst] at h1
  have hbig : BigOK n (cls σ s) := Or.inr ⟨hn, hSc⟩
  have hlayer : LargeEvenLayer (ggFix a) = (blockSU (cls σ s)).map φ :=
    layer_eq_block hM hσ (cls_isCls σ s) (isQuasisimple_block hM hbig) hEcomp
  exact ⟨U, hU1, hU2, hUA, hlayer ▸ hUS (cls σ s) hsS htS⟩

theorem exists_witness (hM : Model φ) (hp : p.Prime) (hpq : p ∣ 2 ^ n + 1) (hn : 1 ≤ n)
    {s t c e : Fin d} (hst : s ≠ t) (hsc : s ≠ c) (hse : s ≠ e) (htc : t ≠ c) (hte : t ≠ e)
    (hce : c ≠ e) :
    ∃ (g : ↥(unitarySU 2 n K d)) (τ : Fin d → Kˣ), (g : GL (Fin d) K) = diagHom d τ ∧
      (∀ k, τ k ^ p = 1) ∧ (∀ k, k ≠ s → k ≠ t → k ≠ c → τ k = 1) ∧ τ s = τ t ∧
      φ (IOneU.swapSU hM.field c e) * φ g ≠ φ g * φ (IOneU.swapSU hM.field c e) := by
  classical
  have hp2 : p ≠ 2 := TableBU.ne_two_of_dvd_two_pow_add_one hn hpq
  obtain ⟨ζ, hζo, hζq⟩ := exists_orderOf_eq_norm_one hM.field hp hpq
  have hζp : ζ ^ p = 1 := hζo ▸ pow_orderOf_eq_one ζ
  have hζroot : ζ ∈ rootsOfUnity p K := by
    rw [mem_rootsOfUnity]
    exact hζp
  have hζQ : ζ ∈ rootsOfUnity (2 ^ n + 1) K := by
    rw [mem_rootsOfUnity]
    exact hζq
  set τ : Fin d → Kˣ := Pi.mulSingle s ζ * Pi.mulSingle t ζ * Pi.mulSingle c (ζ⁻¹ ^ 2) with hτ
  have hτs : τ s = ζ := by
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hst,
      Pi.mulSingle_eq_of_ne hsc, mul_one]
  have hτt : τ t = ζ := by
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hst.symm,
      Pi.mulSingle_eq_of_ne htc, mul_one, one_mul]
  have hτc : τ c = ζ⁻¹ ^ 2 := by
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne hsc.symm,
      Pi.mulSingle_eq_of_ne htc.symm, one_mul]
  have hτe : τ e = 1 := by
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_of_ne hse.symm, Pi.mulSingle_eq_of_ne hte.symm,
      Pi.mulSingle_eq_of_ne hce.symm, one_mul]
  have hτoff : ∀ k, k ≠ s → k ≠ t → k ≠ c → τ k = 1 := by
    intro k hks hkt hkc
    simp only [hτ, Pi.mul_apply, Pi.mulSingle_eq_of_ne hks, Pi.mulSingle_eq_of_ne hkt,
      Pi.mulSingle_eq_of_ne hkc, one_mul]
  have hτmem : ∀ X : Subgroup Kˣ, ζ ∈ X → ∀ k, τ k ∈ X := fun X hX k => by
    simp only [hτ, Pi.mul_apply]
    exact X.mul_mem (X.mul_mem (StdSubRestU.mulSingle_mem hX k) (StdSubRestU.mulSingle_mem hX k))
      (StdSubRestU.mulSingle_mem (X.pow_mem (X.inv_mem hX) 2) k)
  have hτq : ∀ k, τ k ^ (2 ^ n + 1) = 1 := fun k => by
    have h1 := hτmem _ hζQ k
    rwa [mem_rootsOfUnity] at h1
  have hτp : ∀ k, τ k ^ p = 1 := fun k => by
    have h1 := hτmem _ hζroot k
    rwa [mem_rootsOfUnity] at h1
  have hτprod : ∏ k, τ k = 1 := by
    simp only [hτ, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
    group
  refine ⟨⟨diagHom d τ, diagHom_mem_unitarySU hM.field hτq hτprod⟩, τ, rfl, hτp, hτoff,
    by rw [hτs, hτt], fun hcomm => ?_⟩
  set Q : ↥(unitarySU 2 n K d) := IOneU.swapSU hM.field c e with hQ
  set yt : ↥(unitarySU 2 n K d) := ⟨diagHom d τ, diagHom_mem_unitarySU hM.field hτq hτprod⟩
    with hyt
  have hz : φ (Q * yt * Q⁻¹ * yt⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hcomm]
    group
  obtain ⟨u, hu⟩ := hM.ker _ hz
  have hzv : ((Q * yt * Q⁻¹ * yt⁻¹ : ↥(unitarySU 2 n K d)) : GL (Fin d) K) =
      diagHom d ((τ ∘ (Equiv.swap c e).symm) * τ⁻¹) := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.coe_inv]
    show permGL (Equiv.swap c e) * diagHom d τ * (permGL (Equiv.swap c e))⁻¹ *
      (diagHom d τ)⁻¹ = _
    rw [permGL_mul_diagHom_mul_inv, ← map_inv, ← map_mul]
  rw [hzv, coe_diagHom] at hu
  have hf := Matrix.diagonal_injective hu
  have e1 := congrFun hf s
  have e2 := congrFun hf c
  have e3 : ((τ ∘ (Equiv.swap c e).symm) * τ⁻¹) s = ((τ ∘ (Equiv.swap c e).symm) * τ⁻¹) c :=
    Units.ext (e1.trans e2.symm)
  simp only [Pi.mul_apply, Pi.inv_apply, Function.comp_apply, Equiv.symm_swap,
    Equiv.swap_apply_of_ne_of_ne hsc hse, Equiv.swap_apply_left, hτc, hτe, hτs, mul_inv_cancel,
    one_mul, inv_pow, inv_inv] at e3
  have h2 : ζ ^ 2 = 1 := e3.symm
  have h4 := orderOf_dvd_of_pow_eq_one h2
  rw [hζo] at h4
  exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h4)

end CFSG.StandardType.SmallU

end
