module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.L511.KRadical
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec5.T515.Comp
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Conj
public import CFSG.SignalizerFunctorTheorem.McBride.Functor.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot.Components

public section

open CFSG.Open
open scoped commutatorElement

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L69

variable {Γ : Type u} [Group Γ]

theorem commutator_sup_le {H A : Subgroup Γ} (hA : IsMulCommutative A)
    (hAH : A ≤ Subgroup.normalizer (H : Set Γ)) : ⁅H ⊔ A, H ⊔ A⁆ ≤ H := by
  set X := H ⊔ A
  have hXn : X ≤ Subgroup.normalizer (H : Set Γ) := sup_le Subgroup.le_normalizer hAH
  have hHX : H ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hn : (H.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hHX).mpr hXn
  let q : ↥X →* ↥X ⧸ H.subgroupOf X := QuotientGroup.mk' (H.subgroupOf X)
  have hsup : (A.subgroupOf X) ⊔ (H.subgroupOf X) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hAX hHX, sup_comm, Subgroup.subgroupOf_self]
  have hmap : (A.subgroupOf X).map q = ⊤ := by
    have h1 := congrArg (Subgroup.map q) hsup
    rw [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h1
    have h2 : (H.subgroupOf X).map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rwa [h2, sup_bot_eq] at h1
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hxy : ∀ x y : ↥X, q x * q y = q y * q x := by
    intro x y
    have hx' : q x ∈ (A.subgroupOf X).map q := hmap ▸ Subgroup.mem_top _
    have hy' : q y ∈ (A.subgroupOf X).map q := hmap ▸ Subgroup.mem_top _
    exact comm_of_mem_of_isMulCommutative inferInstance hx' hy'
  have h1 : q ⁅(⟨x, hx⟩ : X), ⟨y, hy⟩⁆ = 1 := by
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hxy _ _
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

theorem commutator_eq_top_of_not_isMulCommutative {S : Type*} [Group S] [IsSimpleGroup S]
    (hnc : ¬ IsMulCommutative S) : commutator S = ⊤ := by
  have hn : (commutator S).Normal := by
    rw [commutator_def]
    infer_instance
  rcases hn.eq_bot_or_eq_top with h | h
  · exact absurd ((commutator_eq_bot_iff S).mp h) hnc
  · exact h

theorem le_commutator_of_isSimpleGroup {M : Subgroup Γ} (hs : IsSimpleGroup M)
    (hnc : ¬ IsMulCommutative M) : M ≤ ⁅M, M⁆ := by
  have h := Subgroup.map_subtype_commutator M
  rw [commutator_eq_top_of_not_isMulCommutative hnc, Subgroup.map_top, Subgroup.range_subtype]
    at h
  exact h.le

theorem mem_lcal_of_mem_lcal_sup {H A M : Subgroup Γ} (hA : IsMulCommutative A)
    (hAH : A ≤ Subgroup.normalizer (H : Set Γ)) (hM : M ∈ lcal (H ⊔ A)) : M ∈ lcal H := by
  obtain ⟨hMX, -, hs, hnc⟩ := mem_lcal_iff.mp hM
  have h1 : M ≤ ⁅M, M⁆ := le_commutator_of_isSimpleGroup hs hnc
  have h2 : ⁅M, M⁆ ≤ ⁅H ⊔ A, H ⊔ A⁆ := Subgroup.commutator_mono hMX hMX
  exact L511.mem_lcal_of_le hM (h1.trans (h2.trans (commutator_sup_le hA hAH))) le_sup_left

open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.SolQuot
open CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.AChief

theorem isMulCommutative_qimg {R A : Subgroup Γ} (hA : IsMulCommutative A) :
    IsMulCommutative (qimg R A) := by
  have := hA
  unfold qimg
  infer_instance

variable [Finite Γ]

theorem exists_eq_sol_sup_of_mem_mcal {H A M : Subgroup Γ} (hA : IsMulCommutative A)
    (hAH : A ≤ Subgroup.normalizer (H : Set Γ)) (hsol : sol H = ⊥) (hM : M ∈ mcal (H ⊔ A)) :
    ∃ L ∈ lcal H, M = sol (H ⊔ A) ⊔ L := by
  set X := H ⊔ A
  set R := sol X with hR
  have hXn : X ≤ nrm R := le_nrm_sol X
  have hRs : Group.IsSolvable R := isSolvable_sol X
  have hHX : H ≤ X := le_sup_left
  have hAX : A ≤ X := le_sup_right
  have hHn : H ≤ nrm R := hHX.trans hXn
  have h1 : qimg R M ∈ mcal (qimg R X) := (bijOn_mcal hRs hXn).mapsTo hM
  have hsolX : sol (qimg R X) = ⊥ := by rw [sol_qimg hRs hXn, hR, qimg_self]
  have h2 : qimg R M ∈ lcal (qimg R X) := by rwa [← mcal_eq_lcal_of_sol_eq_bot hsolX]
  have hqX : qimg R X = qimg R H ⊔ qimg R A := qimg_sup hHn (hAX.trans hXn)
  rw [hqX] at h2
  have h3 : qimg R M ∈ lcal (qimg R H) :=
    mem_lcal_of_mem_lcal_sup (isMulCommutative_qimg hA) (qimg_le_normalizer hAH) h2
  have hsolH : sol (qimg R H) = ⊥ := by rw [sol_qimg hRs hHn, hsol, qimg_bot]
  have h4 : qimg R M ∈ mcal (qimg R H) := by rwa [mcal_eq_lcal_of_sol_eq_bot hsolH]
  obtain ⟨L, hL, hLM⟩ := (bijOn_mcal hRs hHn).surjOn h4
  rw [mcal_eq_lcal_of_sol_eq_bot hsol] at hL
  refine ⟨L, hL, ?_⟩
  have hLn : L ≤ nrm R := hL.1.trans hHn
  refine qimg_injOn ⟨hM.2.1, hM.1.trans hXn⟩ ⟨le_sup_left, sup_le Subgroup.le_normalizer hLn⟩ ?_
  rw [qimg_sup Subgroup.le_normalizer hLn, qimg_self, bot_sup_eq, hLM]

omit [Finite Γ] in
theorem mem_khat_iff {X : Subgroup Γ} {x : Γ} :
    x ∈ khat X ↔ x ∈ X ∧ ∀ M ∈ ltilde X, x ∈ Subgroup.normalizer (M : Set Γ) := by
  simp [khat, Subgroup.mem_inf, Subgroup.mem_iInf]

theorem commute_of_mem_sol_sup {H A : Subgroup Γ} (hAH : A ≤ Subgroup.normalizer (H : Set Γ))
    (hsol : sol H = ⊥) {s c : Γ} (hs : s ∈ sol (H ⊔ A)) (hc : c ∈ H) : Commute s c := by
  set X := H ⊔ A
  have hHX : H ≤ X := le_sup_left
  have hXn : X ≤ Subgroup.normalizer (H : Set Γ) := sup_le Subgroup.le_normalizer hAH
  have hsX : s ∈ X := sol_le X hs
  have h1 : c * s⁻¹ * c⁻¹ ∈ sol X :=
    (Subgroup.mem_normalizer_iff.mp (le_nrm_sol X (hHX hc)) s⁻¹).mp (inv_mem hs)
  have h2 : s * c * s⁻¹ ∈ H := (Subgroup.mem_normalizer_iff.mp (hXn hsX) c).mp hc
  have h3 : s * c * s⁻¹ * c⁻¹ ∈ H ⊓ sol X :=
    Subgroup.mem_inf.mpr ⟨mul_mem h2 (inv_mem hc), by simpa [mul_assoc] using mul_mem hs h1⟩
  have h4 : H ⊓ sol X ≤ sol H := inf_le_sol (isSolvable_sol X) (hHX.trans (le_nrm_sol X))
  rw [hsol, le_bot_iff] at h4
  have h5 : s * c * s⁻¹ * c⁻¹ = 1 := Subgroup.mem_bot.mp (h4 ▸ h3)
  exact commutatorElement_eq_one_iff_mul_comm.mp h5

theorem mem_khat_sup_iff {H A : Subgroup Γ} (hA : IsMulCommutative A)
    (hAH : A ≤ Subgroup.normalizer (H : Set Γ)) (hsol : sol H = ⊥) (hne : (lcal H).Nonempty)
    {a : Γ} (ha : a ∈ H ⊔ A) :
    a ∈ khat (H ⊔ A) ↔ ∀ L ∈ lcal H, a ∈ Subgroup.normalizer (L : Set Γ) := by
  set X := H ⊔ A
  have hHX : H ≤ X := le_sup_left
  have hXn : X ≤ Subgroup.normalizer (H : Set Γ) := sup_le Subgroup.le_normalizer hAH
  obtain ⟨L₀, hL₀⟩ := hne
  have hXns : ¬ Group.IsSolvable X := by
    intro hXs
    obtain ⟨hL₀H, -, hs, hnc⟩ := mem_lcal_iff.mp hL₀
    exact T515ab.not_isSolvable_of_not_isMulCommutative hnc
      (T515ab.isSolvable_of_le (hL₀H.trans hHX) hXs)
  rw [mem_khat_iff]
  constructor
  · rintro ⟨-, hx⟩ L hL
    have hLX : L ∈ lcal X := T515ab.mem_lcal_of_isSubnormal hL hHX
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hHX).mpr hXn).isSubnormal
    exact T515ab.mem_normalizer_of_mem_khat_of_mem_lcal hXns hLX
      (fun s hs c hc => commute_of_mem_sol_sup hAH hsol hs (lcal_le hL hc))
      (mem_khat_iff.mpr ⟨ha, hx⟩)
  · intro hall
    refine ⟨ha, fun M hM => ?_⟩
    have hMm : M ∈ mcal X := by
      rcases hM with ⟨hs, -⟩ | ⟨-, hm⟩
      · exact absurd hs hXns
      · exact hm
    obtain ⟨L, hL, rfl⟩ := exists_eq_sol_sup_of_mem_mcal hA hAH hsol hMm
    exact mem_normalizer_sup (le_nrm_sol X ha) (hall L hL)

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L69
