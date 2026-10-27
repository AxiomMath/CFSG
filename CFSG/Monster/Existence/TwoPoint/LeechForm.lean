module

public import CFSG.Monster.B.Cbar.LocalE

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.B.Short CFSG.Monster.B CFSG.Monster.VisCert Subgroup

private theorem zmod_two_cases' : ∀ a : ZMod 2, a = 0 ∨ a = 1 := by decide

theorem leech_zmod_two_add_eq_one :
    ∀ a b : ZMod 2, a + b = 1 → (a = 1 ∧ b = 0) ∨ (a = 0 ∧ b = 1) := by
  decide

theorem leech_exists_dual {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    ∀ e₁ e₂ : ZMod 2, ∃ y : L2, bL u y = e₁ ∧ bL v y = e₂ := by
  have hsum : u + v ≠ 0 := fun h => huv (by
    have := add_eq_zero_iff_eq_neg.1 h
    rw [this, ZModModule.neg_eq_self])
  obtain ⟨ya, hya⟩ := exists_bL_eq_one hu
  obtain ⟨yb, hyb⟩ := exists_bL_eq_one hv
  obtain ⟨yc, hyc⟩ := exists_bL_eq_one hsum
  have hc : bL u yc + bL v yc = 1 := by
    rw [← hyc]
    simp only [map_add, LinearMap.add_apply]
  have key : (∃ y : L2, bL u y = 1 ∧ bL v y = 0) ∧ (∃ y : L2, bL u y = 0 ∧ bL v y = 1) := by
    rcases leech_zmod_two_add_eq_one _ _ hc with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · refine ⟨⟨yc, h1, h2⟩, ?_⟩
      rcases zmod_two_cases' (bL u yb) with h | h
      · exact ⟨yb, h, hyb⟩
      · refine ⟨yb + yc, ?_, ?_⟩
        · simp only [map_add, h, h1]; decide
        · simp only [map_add, hyb, h2]; decide
    · refine ⟨?_, ⟨yc, h1, h2⟩⟩
      rcases zmod_two_cases' (bL v ya) with h | h
      · exact ⟨ya, hya, h⟩
      · refine ⟨ya + yc, ?_, ?_⟩
        · simp only [map_add, hya, h1]; decide
        · simp only [map_add, h, h2]; decide
  obtain ⟨⟨y₁, h11, h12⟩, ⟨y₂, h21, h22⟩⟩ := key
  intro e₁ e₂
  refine ⟨e₁ • y₁ + e₂ • y₂, ?_, ?_⟩
  · simp only [map_add, map_smul, smul_eq_mul, h11, h21, mul_one, mul_zero, add_zero]
  · simp only [map_add, map_smul, smul_eq_mul, h12, h22, mul_one, mul_zero, zero_add]

theorem leech_linearIndependent_pair {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    LinearIndependent (ZMod 2) ![u, v] := by
  rw [LinearIndependent.pair_iff]
  intro s t h
  rcases zmod_two_cases' s with rfl | rfl <;> rcases zmod_two_cases' t with rfl | rfl
  · exact ⟨rfl, rfl⟩
  · simp only [zero_smul, one_smul, zero_add] at h
    exact absurd h hv
  · simp only [zero_smul, one_smul, add_zero] at h
    exact absurd h hu
  · simp only [one_smul] at h
    exact absurd (by rw [← sub_eq_zero, ZModModule.sub_eq_add]; exact h) huv

theorem leech_finrank_span_pair {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {u, v}) = 2 := by
  have h := finrank_span_eq_card (leech_linearIndependent_pair hu hv huv)
  rw [Fintype.card_fin] at h
  have e : Set.range ![u, v] = {u, v} := by
    ext x
    simp only [Set.mem_range, Set.mem_insert_iff, Set.mem_singleton_iff]
    constructor
    · rintro ⟨i, rfl⟩
      fin_cases i
      · exact .inl rfl
      · exact .inr rfl
    · rintro (rfl | rfl)
      · exact ⟨0, rfl⟩
      · exact ⟨1, rfl⟩
  rw [e] at h
  exact h

theorem leech_natCard_span_pair {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Nat.card (Submodule.span (ZMod 2) {u, v}) = 4 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), leech_finrank_span_pair hu hv huv, Nat.card_zmod]
  norm_num

@[expose] def leechPerp (u v : L2) : Submodule (ZMod 2) L2 :=
  LinearMap.ker (bL u) ⊓ LinearMap.ker (bL v)

theorem mem_leechPerp {u v y : L2} : y ∈ leechPerp u v ↔ bL u y = 0 ∧ bL v y = 0 := by
  simp [leechPerp, LinearMap.mem_ker]

theorem leechPerp_eq_orthogonal (u v : L2) :
    leechPerp u v = bL.orthogonal (Submodule.span (ZMod 2) {u, v}) := by
  ext y
  rw [LinearMap.BilinForm.mem_orthogonal_iff, mem_leechPerp]
  constructor
  · rintro ⟨h1, h2⟩ w hw
    obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hw
    have e : bL (a • u + b • v) y = a * bL u y + b * bL v y := by
      simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    change bL (a • u + b • v) y = 0
    rw [e, h1, h2, mul_zero, mul_zero, add_zero]
  · intro h
    exact ⟨h u (Submodule.subset_span (Set.mem_insert _ _)),
      h v (Submodule.subset_span (Set.mem_insert_of_mem _ (Set.mem_singleton _)))⟩

theorem finrank_leechPerp {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Module.finrank (ZMod 2) (leechPerp u v) = 22 := by
  rw [leechPerp_eq_orthogonal, LinearMap.BilinForm.finrank_orthogonal bL_nondegenerate, finrank_L2,
    leech_finrank_span_pair hu hv huv]

theorem natCard_leechPerp {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Nat.card (leechPerp u v) = 2 ^ 22 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_leechPerp hu hv huv, Nat.card_zmod]

@[expose] def leechPre (S : Submodule (ZMod 2) L2) : Subgroup Q where
  carrier := {q | phi0 (coordOf q) ∈ S}
  mul_mem' ha hb := by
    change phi0 (coordOf (_ * _)) ∈ S
    rw [phi0_coordOf_mul]
    exact S.add_mem ha hb
  one_mem' := by
    change phi0 (coordOf 1) ∈ S
    rw [(phi0_coordOf_eq_zero_iff 1).2 (Or.inl rfl)]
    exact S.zero_mem
  inv_mem' ha := by
    change phi0 (coordOf (_)⁻¹) ∈ S
    rw [phi0_coordOf_inv]
    exact ha

theorem mem_leechPre {S : Submodule (ZMod 2) L2} {q : Q} :
    q ∈ leechPre S ↔ phi0 (coordOf q) ∈ S := Iff.rfl

theorem zQ_mem_leechPre (S : Submodule (ZMod 2) L2) : zQ ∈ leechPre S := by
  rw [mem_leechPre, (phi0_coordOf_eq_zero_iff zQ).2 (Or.inr rfl)]
  exact S.zero_mem

def leechMulSub (S : Submodule (ZMod 2) L2) : Subgroup (Multiplicative L2) where
  carrier := {x | Multiplicative.toAdd x ∈ S}
  mul_mem' ha hb := S.add_mem ha hb
  one_mem' := S.zero_mem
  inv_mem' ha := S.neg_mem ha

theorem natCard_leechMulSub (S : Submodule (ZMod 2) L2) :
    Nat.card (leechMulSub S) = Nat.card S :=
  Nat.card_congr (Equiv.subtypeEquiv Multiplicative.toAdd fun _ => Iff.rfl)

theorem leech_natCard_L2 : Nat.card L2 = 2 ^ 24 := by
  rw [Module.natCard_eq_pow_finrank (K := ZMod 2), finrank_L2, Nat.card_zmod]

theorem natCard_leechPre (S : Submodule (ZMod 2) L2) : Nat.card (leechPre S) = 2 * Nat.card S := by
  have hcomap : leechPre S = (leechMulSub S).comap phiQ := by
    ext q
    rw [mem_leechPre, Subgroup.mem_comap]
    exact iff_of_eq (congrArg (· ∈ S) (toAdd_phiQ q).symm)
  have h1 := (leechPre S).card_mul_index
  have h2 := (leechMulSub S).card_mul_index
  rw [hcomap, Subgroup.index_comap_of_surjective (H := leechMulSub S) phiQ_surjective,
    natCard_Q] at h1
  rw [natCard_leechMulSub, Nat.card_congr Multiplicative.toAdd, leech_natCard_L2] at h2
  have hidx : (leechMulSub S).index ≠ 0 := by
    intro h0
    rw [h0, mul_zero] at h2
    norm_num at h2
  rw [hcomap]
  refine Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hidx) ?_
  rw [h1, mul_assoc, h2]
  norm_num

theorem natCard_leechPre_perp {u v : L2} (hu : u ≠ 0) (hv : v ≠ 0) (huv : u ≠ v) :
    Nat.card (leechPre (leechPerp u v)) = 2 ^ 23 := by
  rw [natCard_leechPre, natCard_leechPerp hu hv huv]
  norm_num

theorem centralizer_inf_eq_leechPre (r₁ r₂ : Q) :
    centralizer {r₁} ⊓ centralizer {r₂} =
      leechPre (leechPerp (phi0 (coordOf r₁)) (phi0 (coordOf r₂))) := by
  ext q
  rw [mem_inf, mem_centralizer_iff_bL, mem_centralizer_iff_bL, mem_leechPre, mem_leechPerp]

@[expose] def leechCorr (u v y : L2) : L2 := bL v y • u + bL u y • v

theorem add_leechCorr_mem_leechPerp {u v : L2} (h1 : bL u v = 1) (y : L2) :
    y + leechCorr u v y ∈ leechPerp u v := by
  have h2 : bL v u = 1 := by rw [bL_comm, h1]
  rw [mem_leechPerp, leechCorr]
  constructor
  · simp only [map_add, map_smul, smul_eq_mul, bL_self, h1, mul_zero, mul_one, zero_add]
    exact ZModModule.add_self (bL u y)
  · simp only [map_add, map_smul, smul_eq_mul, bL_self, h2, mul_zero, mul_one, add_zero]
    exact ZModModule.add_self (bL v y)

theorem phi0_eq_zero_of_forall_commute {u v : L2} (h1 : bL u v = 1) {c : Q}
    (hc : c ∈ leechPre (leechPerp u v)) (hcomm : ∀ d ∈ leechPre (leechPerp u v), d * c = c * d) :
    phi0 (coordOf c) = 0 := by
  have hw : phi0 (coordOf c) ∈ leechPerp u v := hc
  rw [mem_leechPerp] at hw
  refine bL_nondegenerate.1 _ fun y => ?_
  obtain ⟨d, hd⟩ := phiQ_surjective (Multiplicative.ofAdd (y + leechCorr u v y))
  have hdφ : phi0 (coordOf d) = y + leechCorr u v y := by rw [← toAdd_phiQ, hd, toAdd_ofAdd]
  have hdmem : d ∈ leechPre (leechPerp u v) := by
    rw [mem_leechPre, hdφ]
    exact add_leechCorr_mem_leechPerp h1 y
  have h := (commute_iff_bL d c).1 (hcomm d hdmem)
  rw [hdφ, leechCorr] at h
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul] at h
  rw [hw.1, hw.2] at h
  simp only [mul_zero, add_zero] at h
  rw [bL_comm]
  exact h

theorem span_pair_le_leechPerp {u v : L2} (h : bL u v = 0) :
    Submodule.span (ZMod 2) {u, v} ≤ leechPerp u v := by
  rw [Submodule.span_le]
  intro y hy
  rw [SetLike.mem_coe, mem_leechPerp]
  have h' : bL v u = 0 := by rw [bL_comm, h]
  rcases hy with rfl | hy
  · exact ⟨bL_self _, h'⟩
  · rw [Set.mem_singleton_iff.1 hy]
    exact ⟨h, bL_self _⟩

theorem qL_eq_zero_of_mem_span_pair {u v : L2} (hu : qL u = 0) (hv : qL v = 0) (h : bL u v = 0)
    {w : L2} (hw : w ∈ Submodule.span (ZMod 2) {u, v}) : qL w = 0 := by
  obtain ⟨a, b, rfl⟩ := Submodule.mem_span_pair.1 hw
  rcases zmod_two_cases' a with rfl | rfl <;> rcases zmod_two_cases' b with rfl | rfl
  · simp
  · simpa using hv
  · simpa using hu
  · simp only [one_smul]
    rw [qL_add, hu, hv, h, add_zero, add_zero]

end CFSG.Monster.Existence
