module

public import CFSG.RankThree.SubgroupLists.OrthogonalForms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RepresentationTheory.UniqueVectorOrbitTwisting
public import CFSG.LocalAnalysis.ComponentInitial.CentralSL2Semilinear
import CFSG.RankThree.SubgroupLists2.InvariantForm
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115OddL3AutCard
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonTwoTransvections
import CFSG.LinearAlgebra.LinearGroups.Perfect

public section

namespace CFSG.RankThree.SubgroupLists

open Matrix CFSG.RepresentationTheory CFSG.Assembly.LowTwoRank
open scoped MatrixGroups

section SL2

open CFSG.LocalAnalysis.ComponentInitial (sl2Upper sl2Lower sl2Weyl coe_sl2Upper coe_sl2Weyl
  sl2Upper_add sl2Upper_zero sl2Lower_neg sl2Weyl_mul_upper)

variable {F : Type*} [Field F]

theorem sl2Weyl_one_mul_sl2Upper_one_mul_inv :
    sl2Weyl F 1 * sl2Upper F 1 * (sl2Weyl F 1)⁻¹ = (sl2Lower F 1)⁻¹ := by
  rw [sl2Weyl_mul_upper, mul_inv_cancel_right, ← sl2Lower_neg]
  simp

theorem sl2Weyl_one_mul_self_mem_center :
    sl2Weyl F 1 * sl2Weyl F 1 ∈ Subgroup.center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  refine ⟨-1, by norm_num, ?_⟩
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Weyl, Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Upper_one_mul_sl2Weyl_one_pow_three : (sl2Upper F 1 * sl2Weyl F 1) ^ 3 = 1 := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Weyl, Matrix.mul_fin_two,
    pow_succ, pow_zero, Matrix.one_mul, Matrix.SpecialLinearGroup.coe_one]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem sl2Upper_one_pow (n : ℕ) : sl2Upper F 1 ^ n = sl2Upper F (n : F) := by
  induction n with
  | zero => rw [pow_zero, Nat.cast_zero, sl2Upper_zero]
  | succ n ih => rw [pow_succ, ih, ← sl2Upper_add, Nat.cast_succ]

theorem not_mem_center_of_apply_zero_one_ne_zero {A : SL(2, F)}
    (h : (A : Matrix (Fin 2) (Fin 2) F) 0 1 ≠ 0) : A ∉ Subgroup.center SL(2, F) := by
  rw [Matrix.SpecialLinearGroup.mem_center_iff]
  rintro ⟨r, -, hr⟩
  apply h
  rw [← hr]
  simp

end SL2

theorem exists_psl2_generators {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    (hF : Nat.card F = p) :
    ∃ u w : ProjectiveSpecialLinearGroup (Fin 2) F, u ^ p = 1 ∧ u ≠ 1 ∧ w ^ 2 = 1 ∧ w ≠ 1 ∧
      (u * w) ^ 3 = 1 ∧ Subgroup.closure {u, w * u * w⁻¹} = ⊤ := by
  classical
  have : Fintype F := Fintype.ofFinite F
  have hcard : Fintype.card F = p ^ 1 := by rw [pow_one, ← Nat.card_eq_fintype_card, hF]
  have : CharP F p := charP_of_card_eq_prime_pow hcard
  let _ : Algebra (ZMod p) F := ZMod.algebra F p
  have hfin : Module.finrank (ZMod p) F = 1 := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := F)
    rw [ZMod.card, hcard] at h
    exact Nat.pow_right_injective (Fact.out : p.Prime).two_le h.symm
  let π := QuotientGroup.mk' (Subgroup.center SL(2, F))
  set U := CFSG.LocalAnalysis.ComponentInitial.sl2Upper F 1 with hU
  set L := CFSG.LocalAnalysis.ComponentInitial.sl2Lower F 1 with hL
  set W := CFSG.LocalAnalysis.ComponentInitial.sl2Weyl F 1 with hW
  refine ⟨π U, π W, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hU, sl2Upper_one_pow, CharP.cast_eq_zero,
      CFSG.LocalAnalysis.ComponentInitial.sl2Upper_zero, map_one]
  · intro h
    exact not_mem_center_of_apply_zero_one_ne_zero (by simp [hU])
      ((QuotientGroup.eq_one_iff _).mp h)
  · rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (by rw [sq]; exact sl2Weyl_one_mul_self_mem_center)
  · intro h
    exact not_mem_center_of_apply_zero_one_ne_zero (by simp [hW])
      ((QuotientGroup.eq_one_iff _).mp h)
  · rw [← map_mul, ← map_pow, sl2Upper_one_mul_sl2Weyl_one_pow_three, map_one]
  · have hw : π W * π U * (π W)⁻¹ = (π L)⁻¹ := by
      rw [← map_mul, ← map_inv, ← map_mul, sl2Weyl_one_mul_sl2Upper_one_mul_inv, map_inv]
    rw [hw]
    have hgen : Subgroup.closure ({U, L} : Set SL(2, F)) = ⊤ :=
      CFSG.Glauberman.Dickson.standard_two_transvections_generate_of_finrank_one (p := p)
        (K := F) 1 one_ne_zero hfin
    have hle : Subgroup.closure ({U, L} : Set SL(2, F)) ≤ Subgroup.closure {U, L⁻¹} := by
      rw [Subgroup.closure_le]
      rintro g (rfl | rfl)
      · exact Subgroup.subset_closure (by simp)
      · have : L⁻¹ ∈ Subgroup.closure ({U, L⁻¹} : Set SL(2, F)) :=
          Subgroup.subset_closure (by simp)
        simpa using Subgroup.inv_mem _ this
    have htop : Subgroup.closure ({U, L⁻¹} : Set SL(2, F)) = ⊤ :=
      top_le_iff.mp (hgen ▸ hle)
    have := congrArg (Subgroup.map π) htop
    rw [MonoidHom.map_closure, Set.image_pair, map_inv,
      Subgroup.map_top_of_surjective π (QuotientGroup.mk'_surjective _)] at this
    exact this

theorem exists_generators_of_mulEquiv_psl2 {G : Type*} [Group G] {H : Subgroup G} {p : ℕ}
    [Fact p.Prime] {F : Type} [Field F] [Finite F] (hF : Nat.card F = p)
    (e : H ≃* StatedProj (StatedSL 2 F)) :
    ∃ x y : G, x ∈ H ∧ y ∈ H ∧ x ^ p = 1 ∧ x ≠ 1 ∧ y * y = 1 ∧ y ≠ 1 ∧ (x * y) ^ 3 = 1 ∧
      Subgroup.closure {x, y * x * y⁻¹} = H := by
  obtain ⟨u, w, hup, hu1, hw2, hw1, huw3, hcl⟩ := exists_psl2_generators hF
  set χ : ProjectiveSpecialLinearGroup (Fin 2) F ≃* H :=
    (projectiveSpecialLinearGroupEquivStatedProj 2 F).trans e.symm
  refine ⟨χ u, χ w, (χ u).2, (χ w).2, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← Subgroup.coe_pow, ← map_pow, hup, map_one, Subgroup.coe_one]
  · intro h
    apply hu1
    apply χ.injective
    rw [map_one]
    exact Subtype.ext h
  · rw [← Subgroup.coe_mul, ← map_mul, ← sq, hw2, map_one, Subgroup.coe_one]
  · intro h
    apply hw1
    apply χ.injective
    rw [map_one]
    exact Subtype.ext h
  · rw [← Subgroup.coe_mul, ← Subgroup.coe_pow, ← map_mul, ← map_pow, huw3, map_one,
      Subgroup.coe_one]
  · have h1 := congrArg (Subgroup.map χ.toMonoidHom) hcl
    rw [MonoidHom.map_closure, Set.image_pair,
      Subgroup.map_top_of_surjective _ χ.surjective] at h1
    have h2 := congrArg (Subgroup.map H.subtype) h1
    rw [MonoidHom.map_closure, Set.image_pair, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2
    simpa [map_mul, map_inv] using h2

theorem card_statedProj_statedSL_two {p : ℕ} (hp2 : Odd p) {F : Type} [Field F] [Finite F]
    (hF : Nat.card F = p) :
    Nat.card (StatedProj (StatedSL 2 F)) = p * (p ^ 2 - 1) / 2 := by
  rw [CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSL (by norm_num), hF]
  have hg : Nat.gcd 2 (p - 1) = 2 := by
    obtain ⟨k, rfl⟩ := hp2
    simp
  norm_num [hg]

theorem isPerfect_of_mulEquiv_psl2 {G : Type*} [Group G] {p : ℕ} (hp5 : 5 ≤ p) {F : Type}
    [Field F] [Finite F] (hF : Nat.card F = p) (e : G ≃* StatedProj (StatedSL 2 F)) :
    Group.IsPerfect G := by
  classical
  have : Fintype F := Fintype.ofFinite F
  obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
    (by rw [Finset.card_univ, ← Nat.card_eq_fintype_card, hF]; omega)
  have : Group.IsPerfect (ProjectiveSpecialLinearGroup (Fin 2) F) :=
    CFSG.LinearGroups.linear_projective_perfect (by norm_num) (Or.inr ⟨s, hs⟩)
  exact Group.IsPerfect.ofSurjective
    (f := ((projectiveSpecialLinearGroupEquivStatedProj 2 F).trans e.symm).toMonoidHom)
    (MulEquiv.surjective _)

theorem pow_three_eq_zero_of_isNilpotent {K : Type*} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    (h : IsNilpotent N) : N ^ 3 = 0 := by
  have hc : N.charpoly = Polynomial.X ^ 3 := by
    have := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent h).eq_zero
    rw [sub_eq_zero, Fintype.card_fin] at this
    exact this
  have := Matrix.aeval_self_charpoly N
  rw [hc, map_pow, Polynomial.aeval_X] at this
  exact this

theorem two_le_finrank_ker_of_sq_eq_zero {K : Type*} [Field K] {N : Matrix (Fin 3) (Fin 3) K}
    (hN : N ^ 2 = 0) : 2 ≤ Module.finrank K (LinearMap.ker (Matrix.toLin' N)) := by
  have hle : LinearMap.range (Matrix.toLin' N) ≤ LinearMap.ker (Matrix.toLin' N) := by
    rintro _ ⟨v, rfl⟩
    rw [LinearMap.mem_ker, Matrix.toLin'_apply, Matrix.toLin'_apply, mulVec_mulVec, ← sq, hN,
      zero_mulVec]
  have h1 := LinearMap.finrank_range_add_finrank_ker (Matrix.toLin' N)
  have h2 := Submodule.finrank_mono hle
  rw [Module.finrank_fin_fun] at h1
  omega

theorem sq_sub_one_ne_zero_of_irreducible {K : Type*} [Field K] {H : Subgroup (GL (Fin 3) K)}
    (hirr : IsIrreducibleMatrixRep H.subtype) {x y : GL (Fin 3) K}
    (hcl : Subgroup.closure {x, y * x * y⁻¹} = H) (hx1 : x ≠ 1) :
    ((x : Matrix (Fin 3) (Fin 3) K) - 1) ^ 2 ≠ 0 := by
  intro hN
  set x' := y * x * y⁻¹ with hx'
  have hN' : ((x' : Matrix (Fin 3) (Fin 3) K) - 1) ^ 2 = 0 := by
    set Y := (y : Matrix (Fin 3) (Fin 3) K)
    set Yi := ((y⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    set N := (x : Matrix (Fin 3) (Fin 3) K) - 1
    have hyy : Y * Yi = 1 := by rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
    have hyy' : Yi * Y = 1 := by rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hc : (x' : Matrix (Fin 3) (Fin 3) K) - 1 = Y * N * Yi := by
      rw [hx', Units.val_mul, Units.val_mul, Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hyy]
    rw [hc]
    calc (Y * N * Yi) ^ 2 = Y * N * (Yi * Y) * N * Yi := by
          rw [sq]
          simp only [Matrix.mul_assoc]
      _ = Y * N ^ 2 * Yi := by
          rw [hyy', Matrix.mul_one, sq]
          simp only [Matrix.mul_assoc]
      _ = 0 := by rw [hN, Matrix.mul_zero, Matrix.zero_mul]
  set A := LinearMap.ker (Matrix.toLin' ((x : Matrix (Fin 3) (Fin 3) K) - 1))
  set B := LinearMap.ker (Matrix.toLin' ((x' : Matrix (Fin 3) (Fin 3) K) - 1))
  have hA : 2 ≤ Module.finrank K A := two_le_finrank_ker_of_sq_eq_zero hN
  have hB : 2 ≤ Module.finrank K B := two_le_finrank_ker_of_sq_eq_zero hN'
  have hAB := Submodule.finrank_sup_add_finrank_inf_eq A B
  have hsup : Module.finrank K ↥(A ⊔ B) ≤ 3 := by
    have := Submodule.finrank_le (A ⊔ B)
    rwa [Module.finrank_fin_fun] at this
  have hfix : ∀ g ∈ H, ∀ v ∈ A ⊓ B, (g : Matrix (Fin 3) (Fin 3) K) *ᵥ v = v := by
    intro g hg
    rw [← hcl] at hg
    induction hg using Subgroup.closure_induction with
    | mem g hg =>
      intro v hv
      rcases hg with rfl | rfl
      · have h := (Submodule.mem_inf.mp hv).1
        rw [LinearMap.mem_ker, Matrix.toLin'_apply, sub_mulVec, one_mulVec, sub_eq_zero] at h
        exact h
      · have h := (Submodule.mem_inf.mp hv).2
        rw [LinearMap.mem_ker, Matrix.toLin'_apply, sub_mulVec, one_mulVec, sub_eq_zero] at h
        exact h
    | one => intro v _; rw [Units.val_one, one_mulVec]
    | mul g h _ _ ihg ihh =>
      intro v hv
      rw [Units.val_mul, ← mulVec_mulVec, ihh v hv, ihg v hv]
    | inv g _ ih =>
      intro v hv
      conv_lhs => rw [← ih v hv]
      rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  rcases hirr (A ⊓ B) (fun g v hv => by rw [Subgroup.coe_subtype, hfix g g.2 v hv]; exact hv)
    with h | h
  · rw [h, finrank_bot] at hAB
    omega
  · apply hx1
    have hAtop : A = ⊤ := top_le_iff.mp (h ▸ inf_le_left)
    have h0 : Matrix.toLin' ((x : Matrix (Fin 3) (Fin 3) K) - 1) = 0 :=
      LinearMap.ker_eq_top.mp hAtop
    have h1 : (x : Matrix (Fin 3) (Fin 3) K) - 1 = 0 :=
      Matrix.toLin'.injective (by rw [h0, map_zero])
    exact Units.ext (sub_eq_zero.mp h1)

theorem card_soGL_three {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {M : Matrix (Fin 3) (Fin 3) (ZMod p)}
    (hM : Mᵀ = M) (hdet : M.det ≠ 0) :
    Nat.card (soGL M) = p * (p ^ 2 - 1) := by
  have hodd : ringChar (ZMod p) ≠ 2 := by rw [ZMod.ringChar_zmod_n]; exact hp2
  have h := CFSG.QuasithinUnique.Ch1.card_soForm hodd (GeneralLinearGroup.mkOfDetNeZero M hdet) hM
  rw [Nat.card_zmod] at h
  rw [← h]
  refine Nat.card_congr
    { toFun := fun g => ⟨⟨(g : GL (Fin 3) (ZMod p)), (mem_soGL.mp g.2).2⟩, (mem_soGL.mp g.2).1⟩
      invFun := fun g => ⟨Matrix.SpecialLinearGroup.toGL (g : SL(3, ZMod p)), mem_soGL.mpr
        ⟨g.2, (g : SL(3, ZMod p)).2⟩⟩
      left_inv := fun g => by ext : 2; rfl
      right_inv := fun g => by ext : 2; rfl }

theorem commutator_mem_of_index_eq_two {G : Type*} [Group G] {K : Subgroup G} (hK : K.index = 2)
    (a b : G) : a * b * a⁻¹ * b⁻¹ ∈ K := by
  have h := fun x y : G => Subgroup.mul_mem_iff_of_index_two hK (a := x) (b := y)
  rw [h, h, h, inv_mem_iff, inv_mem_iff]
  tauto

theorem eq_omegaGL_of_mulEquiv_psl2 {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    {H : Subgroup (GL (Fin 3) (ZMod p))}
    (hirr : IsIrreducibleMatrixRep H.subtype)
    (hdet : ∀ x ∈ H, (x : Matrix (Fin 3) (Fin 3) (ZMod p)).det = 1)
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = p)
    (e : H ≃* StatedProj (StatedSL 2 F)) :
    ∃ M : Matrix (Fin 3) (Fin 3) (ZMod p), Mᵀ = M ∧ M.det ≠ 0 ∧ H = omegaGL M := by
  classical
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := by omega
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  obtain ⟨x, y, hxH, hyH, hxp, hx1, hy2, hy1, hxy3, hcl⟩ := exists_generators_of_mulEquiv_psl2 hF e
  have hN3 : ((x : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1) ^ 3 = 0 := by
    have hNp : ((x : Matrix (Fin 3) (Fin 3) (ZMod p)) - 1) ^ p = 0 := by
      rw [sub_pow_char_of_commute p (Commute.one_right _), ← Units.val_pow_eq_pow_val, hxp,
        Units.val_one, one_pow, sub_self]
    exact pow_three_eq_zero_of_isNilpotent ⟨p, hNp⟩
  have hN2 := sq_sub_one_ne_zero_of_irreducible hirr hcl hx1
  obtain ⟨M, hMsymm, hMdet, hMx, hMy⟩ :=
    exists_invariant_symmetric_form h2 hN3 hN2 hy2 hy1 (hdet y hyH) hxy3
  have hxso : x ∈ soGL M := mem_soGL.mpr ⟨hMx, hdet x hxH⟩
  have hyso : y ∈ soGL M := mem_soGL.mpr ⟨hMy, hdet y hyH⟩
  have hHso : H ≤ soGL M := by
    rw [← hcl, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact hxso
    · exact (soGL M).mul_mem ((soGL M).mul_mem hyso hxso) ((soGL M).inv_mem hyso)
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have hcardH : Nat.card H = p * (p ^ 2 - 1) / 2 := by
    rw [Nat.card_congr e.toEquiv, card_statedProj_statedSL_two hodd hF]
  have hcardS := card_soGL_three hp2 hMsymm hMdet
  have heven : 2 ∣ p * (p ^ 2 - 1) :=
    Dvd.dvd.mul_left (even_iff_two_dvd.mp (Nat.Odd.sub_odd (hodd.pow) odd_one)) p
  have hpos : 0 < p * (p ^ 2 - 1) / 2 := by
    have : 24 ≤ p ^ 2 - 1 := by
      have : 25 ≤ p ^ 2 := by nlinarith
      omega
    have : 2 ≤ p * (p ^ 2 - 1) := by nlinarith
    omega
  have hidx : (H.subgroupOf (soGL M)).index = 2 := by
    have h := Subgroup.card_mul_index (H.subgroupOf (soGL M))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHso).toEquiv, hcardH, hcardS] at h
    have h' : p * (p ^ 2 - 1) / 2 * (H.subgroupOf (soGL M)).index = p * (p ^ 2 - 1) / 2 * 2 :=
      h.trans (Nat.div_mul_cancel heven).symm
    exact Nat.eq_of_mul_eq_mul_left hpos h'
  refine ⟨M, hMsymm, hMdet, le_antisymm ?_ ?_⟩
  · have : Group.IsPerfect H := isPerfect_of_mulEquiv_psl2 hp5 hF e
    rw [← Subgroup.commutator_eq_self (H := H)]
    exact Subgroup.commutator_mono hHso hHso
  · rw [omegaGL, Subgroup.commutator_le]
    intro g₁ h₁ g₂ h₂
    have h := commutator_mem_of_index_eq_two hidx ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    rw [Subgroup.mem_subgroupOf] at h
    rw [commutatorElement_def]
    simpa using h

end CFSG.RankThree.SubgroupLists
