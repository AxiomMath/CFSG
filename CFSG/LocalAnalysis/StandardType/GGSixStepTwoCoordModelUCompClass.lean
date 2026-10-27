module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelUCompZero

public section

namespace CFSG.StandardType

namespace CoordSU

open Matrix Module Polynomial CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LinearGroups SUTB NoOffOm NsFrameComp CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCUnitary Multiplicative

variable {f n : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 f K} {p : ℕ}
  {A : Subgroup ↥(unitarySU 2 f K n)}

local notation "Xe" x:max => ((toUnitHom x : LinearMap.GeneralLinearGroup K (Fin n → K)) :
  Module.End K (Fin n → K))

@[expose] def PieceIn (F : PieceFrame f n K h p A) (x : ↥(unitarySU 2 f K n)) (a : K[X])
    (i : Fin F.r) : Prop :=
  ∀ v ∈ (orbW h x a).orthogonalBilin (stdHermForm h n), lin (F.b i) v = v

theorem mem_orth_of_not_pieceIn (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {x : ↥(unitarySU 2 f K n)} (hxA : x ∈ A) {a : K[X]} (ha : a ∈ primaryFactors (Xe x))
    {i : Fin F.r} (hi : ¬ PieceIn F x a i) {v : Fin n → K} (hv : v ∈ orbW h x a) :
    v ∈ (rng (F.y i)).orthogonalBilin (stdHermForm h n) := by
  rcases piece_orbW hA F hxA ha i with h1 | h1
  · exact absurd h1 hi
  · exact (lin_b_eq_self_iff hA F i v).mp (h1 v hv)

theorem mem_orth_of_pieceIn (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {x : ↥(unitarySU 2 f K n)} {a : K[X]} {i : Fin F.r} (hi : PieceIn F x a i) {v : Fin n → K}
    (hv : v ∈ (orbW h x a).orthogonalBilin (stdHermForm h n)) :
    v ∈ (rng (F.y i)).orthogonalBilin (stdHermForm h n) :=
  (lin_b_eq_self_iff hA F i v).mp (hi v hv)

theorem b_ne_one (hA : MaxElemAb p A) (F : PieceFrame f n K h p A) (i : Fin F.r) : F.b i ≠ 1 := by
  have : Fact (1 < p) := ⟨hA.prime.one_lt⟩
  intro h1
  rw [← F.ι_single i, ← map_one F.ι] at h1
  have h2 := congrFun (ofAdd.injective (F.ι_injective h1)) i
  simp at h2

theorem ne_zero_of_pieceIn (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {β : Fin F.r → ZMod p} {x : ↥(unitarySU 2 f K n)} (hxβ : F.ι (ofAdd β) = x) {a : K[X]}
    (ha : a ∈ primaryFactors (Xe x)) (ha1 : a ≠ X - C 1) {i : Fin F.r} (hi : PieceIn F x a i) :
    β i ≠ 0 := by
  intro hβi
  have hp := hA.prime
  have hxA : x ∈ A := hxβ ▸ ι_mem F _
  have H := primaryData h hp hA.ne_two (hA.pow x hxA)
  have hfixU : ∀ u ∈ rng (F.y i), u ∈ primaryComponent (Xe x) (X - C 1) := by
    intro u hu
    rw [primaryComponent_X_sub_C_one, LinearMap.mem_ker, LinearMap.sub_apply,
      Module.End.one_apply, sub_eq_zero]
    change lin x u = u
    rw [← hxβ]
    exact lin_ι_apply_of_eq_zero F hβi hu
  have hmem : (X - C 1 : K[X]) ∈ primaryFactors (Xe x) := by
    obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (F.ne_bot i)
    exact mem_primaryFactors_of_ker (irreducible_X_sub_C 1) (monic_X_sub_C 1) hu0
      (mem_primaryComponent.mp (hfixU u hu))
  have had := dualPoly_mem_primaryFactors H ha
  have had1 : dualPoly h.bar a ≠ X - C 1 := by
    intro e
    apply ha1
    rw [← dualPoly_dualPoly_of_mem H ha, e, dualPoly_X_sub_C_one]
  have hW : ∀ w ∈ orbW h x a, lin (F.b i) w = w := by
    intro w hw
    refine (lin_b_eq_self_iff hA F i w).mpr (Submodule.mem_orthogonalBilin.mpr fun u hu => ?_)
    obtain ⟨w₁, hw₁, w₂, hw₂, rfl⟩ := Submodule.mem_sup.mp hw
    have h1 := orthogonal_of_ne_dualPoly H hmem ha
      (by rw [dualPoly_X_sub_C_one]; exact ha1) (hfixU u hu) hw₁
    have h2 := orthogonal_of_ne_dualPoly H hmem had
      (by rw [dualPoly_X_sub_C_one]; exact had1) (hfixU u hu) hw₂
    rw [map_add, h1, h2, add_zero]
  apply b_ne_one hA F i
  refine eq_of_lin_apply fun v => ?_
  obtain ⟨m, hm, z, hz, rfl⟩ := exists_add_orth (orbW_nondeg H ha) v
  rw [map_add, hW m hm, hi z hz, lin_one]
  rfl

theorem exists_pieceIn (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {β : Fin F.r → ZMod p} {x : ↥(unitarySU 2 f K n)} (hxβ : F.ι (ofAdd β) = x) {a : K[X]}
    (ha : a ∈ primaryFactors (Xe x)) (ha1 : a ≠ X - C 1) : ∃ i, PieceIn F x a i := by
  have hp := hA.prime
  have hxA : x ∈ A := hxβ ▸ ι_mem F _
  have H := primaryData h hp hA.ne_two (hA.pow x hxA)
  by_contra hex
  push Not at hex
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot
    (primaryComponent_ne_bot H.squarefree ha)
  apply hw0
  refine eq_zero_of_fix_primaryComponent ha ha1 hw ?_
  rw [← hxβ]
  exact (F.ι_fix _ w).mpr fun k _ =>
    mem_orth_of_not_pieceIn hA F hxA ha (hex k) (Submodule.mem_sup_left hw)

theorem ι_smul_eq_pow (F : PieceFrame f n K h p A) (β : Fin F.r → ZMod p) (κ : ZMod p) :
    F.ι (ofAdd (κ.val • β)) = F.ι (ofAdd β) ^ κ.val := by
  rw [ofAdd_nsmul, map_pow]

theorem lin_ι_eq_on_orbW (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {β : Fin F.r → ZMod p} {x : ↥(unitarySU 2 f K n)} (hxβ : F.ι (ofAdd β) = x) {a : K[X]}
    (ha : a ∈ primaryFactors (Xe x)) {s : Fin F.r → ZMod p} {κ : ZMod p}
    (hs : ∀ i, PieceIn F x a i → s i = κ * β i) {w : Fin n → K} (hw : w ∈ orbW h x a) :
    lin (F.ι (ofAdd s)) w = lin (x ^ κ.val) w := by
  have : NeZero p := ⟨hA.prime.ne_zero⟩
  have hxA : x ∈ A := hxβ ▸ ι_mem F _
  have hsplit : ofAdd s = ofAdd (κ.val • β) * ofAdd (s - κ.val • β) := by
    rw [← ofAdd_add]
    congr 1
    abel
  have hrest : lin (F.ι (ofAdd (s - κ.val • β))) w = w := by
    refine (F.ι_fix _ w).mpr fun k hk => ?_
    by_cases hkS : PieceIn F x a k
    · exfalso
      apply hk
      rw [toAdd_ofAdd, Pi.sub_apply, Pi.smul_apply, hs k hkS, nsmul_eq_mul,
        ZMod.natCast_zmod_val, sub_self]
    · exact mem_orth_of_not_pieceIn hA F hxA ha hkS hw
  rw [hsplit, map_mul, lin_mul, Module.End.mul_apply, hrest, ι_smul_eq_pow, hxβ]

theorem ι_comm_sb_class (hA : MaxElemAb p A) (F : PieceFrame f n K h p A)
    {β : Fin F.r → ZMod p} {x : ↥(unitarySU 2 f K n)} (hxβ : F.ι (ofAdd β) = x) {a : K[X]}
    (ha : a ∈ primaryFactors (Xe x)) {s : Fin F.r → ZMod p} {κ : ZMod p}
    (hs : ∀ i, PieceIn F x a i → s i = κ * β i) {g : ↥(unitarySU 2 f K n)} (hg : g ∈ sb h x a) :
    F.ι (ofAdd s) * g = g * F.ι (ofAdd s) := by
  have hp := hA.prime
  have hxA : x ∈ A := hxβ ▸ ι_mem F _
  have hsC := mem_centralizer_of_mem hA hxA (ι_mem F (ofAdd s))
  have hgC : g ∈ Subgroup.centralizer {x} := sb_le_centralizer hg
  have hgtriv := (mem_specialBlock.mp (mem_sb.mp hg)).1.2
  have hgx1 : Commute g x := Subgroup.mem_centralizer_singleton_iff.mp hgC
  have hgx : g * x ^ κ.val = x ^ κ.val * g := (hgx1.pow_right κ.val).eq
  refine mul_comm_of_forall_primaryComponent h hp hA.ne_two (hA.pow x hxA) fun b hb v hv => ?_
  by_cases hbS : b ∈ ({a, dualPoly h.bar a} : Set K[X])
  · have hvW : v ∈ orbW h x a := by
      rcases hbS with rfl | rfl
      · exact Submodule.mem_sup_left hv
      · exact Submodule.mem_sup_right hv
    have hgvW : lin g v ∈ orbW h x a := orbW_inv hgC v hvW
    rw [lin_ι_eq_on_orbW hA F hxβ ha hs hgvW, lin_ι_eq_on_orbW hA F hxβ ha hs hvW,
      ← Module.End.mul_apply, ← Module.End.mul_apply, ← lin_mul, ← lin_mul, hgx]
  · have e1 : lin g v = v := hgtriv b hb hbS v hv
    have e2 : lin g (lin (F.ι (ofAdd s)) v) = lin (F.ι (ofAdd s)) v :=
      hgtriv b hb hbS _ (lin_mem_primaryComponent hsC hv)
    rw [e1, e2]

end CoordSU

end CFSG.StandardType
