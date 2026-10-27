module

public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsGenCoatom
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1

open CFSG.GorensteinWalter

variable {G : Type} [Group G] {L : Subgroup G} {K : Type} [Field K]

@[expose] def embL (e : L ≃* PSL2 K) : PSL2 K →* G := L.subtype.comp e.symm.toMonoidHom

theorem embL_injective (e : L ≃* PSL2 K) : Function.Injective (embL e) :=
  Subtype.val_injective.comp e.symm.injective

theorem embL_mem (e : L ≃* PSL2 K) (c : PSL2 K) : embL e c ∈ L := (e.symm c).2

theorem embL_apply (e : L ≃* PSL2 K) {y : G} (hy : y ∈ L) : embL e (e ⟨y, hy⟩) = y := by
  simp [embL]

theorem range_embL (e : L ≃* PSL2 K) : (embL e).range = L := by
  refine le_antisymm (fun _ ⟨c, hc⟩ => hc ▸ embL_mem e c) fun y hy => ⟨e ⟨y, hy⟩, ?_⟩
  exact embL_apply e hy

theorem inf_centralizer_eq_map (e : L ≃* PSL2 K) {x : G} (hx : x ∈ L) :
    L ⊓ Subgroup.centralizer {x} = (Subgroup.centralizer {e ⟨x, hx⟩}).map (embL e) := by
  have h1 : x = embL e (e ⟨x, hx⟩) := (embL_apply e hx).symm
  ext y
  rw [Subgroup.mem_inf, Subgroup.mem_map]
  constructor
  · rintro ⟨hyL, hyc⟩
    refine ⟨e ⟨y, hyL⟩, ?_, embL_apply e hyL⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hyc ⊢
    apply embL_injective e
    rw [map_mul, map_mul, embL_apply, ← h1]
    exact hyc
  · rintro ⟨c, hc, rfl⟩
    refine ⟨embL_mem e c, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    rw [h1, ← map_mul, ← map_mul, hc]

variable [Finite K]

variable {p : ℕ} [Fact p.Prime]

theorem inner_conj_of_equiv (e : L ≃* PSL2 K) (hK : Nat.card K = p ^ 2) (hp : Odd p)
    {x y : G} (hxL : x ∈ L) (hyL : y ∈ L) (hx : orderOf x = 2) (hy : orderOf y = 2) :
    ∃ g ∈ L, g * x * g⁻¹ = y := by
  have hord : ∀ (z : G) (hz : z ∈ L), orderOf z = 2 → orderOf (e ⟨z, hz⟩) = 2 := fun z hz h =>
    by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, h]
  obtain ⟨c, hc⟩ := isConj_iff.mp (CFSG.Walter.psl2_isConj_of_orderOf_eq_two K hK hp
    (by norm_num) (hord x hxL hx) (hord y hyL hy))
  refine ⟨embL e c, embL_mem e c, ?_⟩
  have h1 : x = embL e (e ⟨x, hxL⟩) := (embL_apply e hxL).symm
  rw [h1, ← map_inv, ← map_mul, ← map_mul, hc, embL_apply]

theorem inner_dihedral_of_equiv (e : L ≃* PSL2 K) (hK : Nat.card K = p ^ 2) (hp : Odd p)
    (hp5 : 5 ≤ p) {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) :
    ∃ n : ℕ, 4 ≤ n ∧ 2 * n = p ^ 2 - 1 ∧
      Nonempty (↥(L ⊓ Subgroup.centralizer {x}) ≃* DihedralGroup n) := by
  have hex : orderOf (e ⟨x, hxL⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  have h4 : p ^ 2 % 4 = 1 := by
    obtain ⟨k, rfl⟩ := hp
    ring_nf
    omega
  obtain ⟨hcard, ⟨d⟩⟩ := (CFSG.Walter.psl2_centralizer_involution K hK hp (by norm_num) hex).1 h4
  have h25 : 25 ≤ p ^ 2 := by nlinarith
  rw [inf_centralizer_eq_map e hxL]
  refine ⟨(p ^ 2 - 1) / 2, by omega, by omega, ⟨?_⟩⟩
  exact ((Subgroup.centralizer {e ⟨x, hxL⟩}).equivMapOfInjective _ (embL_injective e)).symm.trans d

theorem inner_solvable_of_equiv (e : L ≃* PSL2 K) (hK : Nat.card K = p ^ 2) (hp : Odd p)
    (hp5 : 5 ≤ p) {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) :
    Group.IsSolvable ↥(L ⊓ Subgroup.centralizer {x}) := by
  obtain ⟨n, hn, -, ⟨d⟩⟩ := inner_dihedral_of_equiv e hK hp hp5 hxL hx
  have : NeZero n := ⟨by omega⟩
  have := CFSG.Walter.isSolvable_dihedralGroup' n
  exact Group.isSolvable_of_isSolvable_injective (f := d.toMonoidHom) d.injective

theorem inner_max_of_equiv (e : L ≃* PSL2 K) (hK : Nat.card K = p ^ 2)
    (hp5 : 5 ≤ p) {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) (H : Subgroup G)
    (hlt : L ⊓ Subgroup.centralizer {x} < H) (hHL : H ≤ L) : H = L := by
  have hex : orderOf (e ⟨x, hxL⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  have hp2 : p ≠ 2 := by omega
  have h4 : p ^ 2 % 4 = 1 := by
    obtain ⟨k, rfl⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
    ring_nf
    omega
  have hco := CFSG.ComponentClassification.AutL2Facts.isCoatom_centralizer_involution
    (Fact.out : p.Prime) hp2 hK h4 (by nlinarith) hex
  have hmap : (H.comap (embL e)).map (embL e) = H := by
    rw [Subgroup.map_comap_eq, range_embL, inf_eq_right.mpr hHL]
  rw [inf_centralizer_eq_map e hxL] at hlt
  have hle : Subgroup.centralizer {e ⟨x, hxL⟩} ≤ H.comap (embL e) :=
    (Subgroup.map_le_iff_le_comap).mp hlt.le
  have hne : Subgroup.centralizer {e ⟨x, hxL⟩} ≠ H.comap (embL e) := fun h =>
    hlt.ne (by rw [h, hmap])
  rw [← hmap, hco.2 _ (lt_of_le_of_ne hle hne), ← MonoidHom.range_eq_map, range_embL]

theorem inner_center_of_equiv (e : L ≃* PSL2 K) (hK : Nat.card K = p ^ 2) (hp : Odd p)
    (hp5 : 5 ≤ p) {x : G} (hxL : x ∈ L) (hx : orderOf x = 2) {y : G}
    (hy : y ∈ L ⊓ Subgroup.centralizer {x})
    (hcen : ∀ w ∈ L ⊓ Subgroup.centralizer {x}, y * w = w * y) : y ∈ Subgroup.zpowers x := by
  have hex : orderOf (e ⟨x, hxL⟩) = 2 := by rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx]
  set C := Subgroup.centralizer ({e ⟨x, hxL⟩} : Set (PSL2 K)) with hC
  have hZ := CFSG.Walter.psl2_center_centralizer_involution K hK hp (by norm_num)
    (by nlinarith) hex
  rw [inf_centralizer_eq_map e hxL] at hy hcen
  obtain ⟨c, hcC, rfl⟩ := hy
  have hcZ : (⟨c, hcC⟩ : C) ∈ Subgroup.center C := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    apply embL_injective e
    have := hcen (embL e w) ⟨w, w.2, rfl⟩
    simpa [map_mul] using this.symm
  have hcz : c ∈ Subgroup.zpowers (e ⟨x, hxL⟩) := by
    rw [← hZ]
    exact ⟨⟨c, hcC⟩, hcZ, rfl⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hcz
  refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
  rw [← hk, map_zpow, embL_apply]

end CFSG.Quasithin.Vol2.Ch11.SecU1
