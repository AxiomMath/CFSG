module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M24Tab
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsSporJ4Quot
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtJ4LocDef

public section

namespace CFSG.Quasithin.J4Fam

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.QuasithinUnique.Vol2Native.L239.J4Pairs
open CFSG.Quasithin.J4Loc
open scoped commutatorElement
open CFSG.QuasithinUnique.Vol2Native.A312L.Seven CFSG.Quasithin.A312M24

section


noncomputable def fHj : ↥Hj →* G24 :=
  starHom.codRestrict CFSG.Blueprint.NativeSporadic.M24 fun g => by
    rw [← range_starHom_eq]
    exact ⟨g, rfl⟩

theorem fHj_surjective : Function.Surjective fHj := by
  intro m
  obtain ⟨g, hg⟩ : (m : Equiv.Perm (Fin 24)) ∈ starHom.range := by
    rw [range_starHom_eq]
    exact m.2
  exact ⟨g, Subtype.ext hg⟩

theorem ker_fHj : fHj.ker = (Eg uJ 11).subgroupOf Hj := by
  rw [← ker_starHom]
  ext g
  simp only [MonoidHom.mem_ker, fHj]
  constructor
  · intro h
    exact congrArg Subtype.val h
  · intro h
    exact Subtype.ext h

theorem isSporadic_Hj_quotient :
    CFSG.Quasithin.IsSporadic .M24 (↥Hj ⧸ (Eg uJ 11).subgroupOf Hj) :=
  ⟨((QuotientGroup.quotientMulEquivOfEq ker_starHom.symm).trans
      (QuotientGroup.quotientKerEquivRange starHom)).trans
    (MulEquiv.subgroupCongr range_starHom_eq)⟩

theorem isPGroup_ker_fHj : IsPGroup 2 fHj.ker := by
  have hM := j4Facts.mat
  rw [ker_fHj]
  exact (isPGroup_Eg (elem_uJ hM)).of_equiv (Subgroup.subgroupOfEquivOfLe Eg_le_Hj).symm

theorem isPerfect_G24 : Group.IsPerfect G24 := by
  have hs : IsSimpleGroup G24 := CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
  have hna : ∃ a b : G24, a * b ≠ b * a := by
    refine nonabelian_of_card_not_prime (S := G24) ?_
    rw [show Nat.card G24 = 244823040 from CFSG.Sporadic.Mathieu.card_M24]
    norm_num
  exact Group.isPerfect_def.mpr (commutator_eq_top_of_simple hna)

@[expose] def commWit : List (List ℕ) :=
  [[4, 32, 64, 256], [1, 4, 32, 64, 256], [4, 64, 256, 512], [1, 16, 32, 64, 128],
    [1, 2, 4, 32, 64, 256], [1, 2, 64, 128, 256, 1024], [1, 8, 16, 64, 256, 512], [64, 256, 512],
    [2, 4, 16, 32, 64, 128, 512], [1, 8, 16, 32, 64, 128],
    [2, 4, 16, 32, 128, 256, 512, 1024]]

theorem commWit_spec : ∀ i < 11,
    (commWit.getD i []).foldr (fun c acc => (act 1 c ^^^ c) ^^^ acc) 0 = 2 ^ i := by
  decide

theorem one_mem_letters : (1 : ℤ) ∈ letters := by simp [letters]

theorem eta_comm_mem_commutator (c : ℕ) :
    eta uJ 11 (act 1 c ^^^ c) ∈ ⁅Hj, Hj⁆ := by
  have hM := j4Facts.mat
  have h1 : XJ 1 * eta uJ 11 c * (XJ 1)⁻¹ = eta uJ 11 (act 1 c) := hX_all hM one_mem_letters c
  have h2 : (eta uJ 11 c)⁻¹ = eta uJ 11 c :=
    inv_eq_of_mul_eq_one_right (by
      rw [eta_mul_eta hM _ _, Nat.xor_self, eta_zero])
  have h3 : ⁅XJ 1, eta uJ 11 c⁆ = eta uJ 11 (act 1 c ^^^ c) := by
    rw [commutatorElement_def, h1, h2, eta_mul_eta hM _ _]
  rw [← h3]
  exact Subgroup.commutator_mem_commutator (XJ_mem one_mem_letters)
    (Eg_le_Hj (eta_mem_Eg 11 le_rfl c))


theorem Eg_le_commutator : Eg uJ 11 ≤ ⁅Hj, Hj⁆ := by
  have hM := j4Facts.mat
  have key : ∀ L : List ℕ,
      eta uJ 11 (L.foldr (fun c acc => (act 1 c ^^^ c) ^^^ acc) 0) ∈ ⁅Hj, Hj⁆ := by
    intro L
    induction L with
    | nil =>
      simp only [List.foldr_nil, eta_zero]
      exact Subgroup.one_mem _
    | cons c L ih =>
      simp only [List.foldr_cons]
      rw [← eta_mul_eta hM _ _]
      exact Subgroup.mul_mem _ (eta_comm_mem_commutator c) ih
  rw [Eg, Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  have h := key (commWit.getD j [])
  rw [commWit_spec j hj, eta_two_pow hj] at h
  exact h

theorem isPerfect_Hj : Group.IsPerfect ↥Hj := by
  have hf := fHj_surjective
  set K : Subgroup ↥Hj := commutator ↥Hj with hK
  have hKmap : K.map fHj = ⊤ := by
    have h1 : K.map fHj = commutator G24 := by
      rw [hK, commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hf]
    rw [h1]
    exact Group.isPerfect_def.1 isPerfect_G24
  have hkerK : fHj.ker ≤ K := by
    intro x hx
    rw [ker_fHj, Subgroup.mem_subgroupOf] at hx
    have hx' : (x : J) ∈ ⁅Hj, Hj⁆ := Eg_le_commutator hx
    have hmap : (K.map Hj.subtype) = ⁅Hj, Hj⁆ := by
      rw [hK, commutator_def, Subgroup.map_commutator, Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmap] at hx'
    exact (Subgroup.mem_map_iff_mem Hj.subtype_injective).1 hx'
  have hsup : K ⊔ fHj.ker = ⊤ := by
    rw [← Subgroup.comap_map_eq, hKmap, Subgroup.comap_top]
  have hKtop : K = ⊤ := by
    rw [← hsup]
    exact (sup_eq_left.2 hkerK).symm
  exact Group.isPerfect_def.2 hKtop

end

end CFSG.Quasithin.J4Fam
