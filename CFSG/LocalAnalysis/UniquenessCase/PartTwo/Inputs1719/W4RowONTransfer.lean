module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowONHeis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowFstarLift
public import CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic.MDichotomy

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1
  CFSG.QuasithinUnique.Setup.Family CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit
  CFSG.HardMathSupport.Cooperstein.Coordinator.FFSporadic
  CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem actS_mul_self {W : Type} [CommGroup W] {Y L : Subgroup (MulAut W)}
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S]
    (e : CQ L ≃* S) {t : MulAut W} (ht : t ∈ Y) (hto : orderOf t = 2) :
    actS hY e ⟨t, Subgroup.mem_sup_right ht⟩ * actS hY e ⟨t, Subgroup.mem_sup_right ht⟩ = 1 := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hto]
    exact pow_orderOf_eq_one t
  rw [← map_mul, show (⟨t, Subgroup.mem_sup_right ht⟩ : ↥(L ⊔ Y)) *
      ⟨t, Subgroup.mem_sup_right ht⟩ = 1 from Subtype.ext ht2, map_one]

private theorem actS_ne_one {W : Type} [CommGroup W] [Finite W] {Y L : Subgroup (MulAut W)}
    (hLY : L ≤ Y) (hF : Fstar Y = L) (hperf : Group.IsPerfect ↥L) (hO2 : O2Trivial L)
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S]
    (e : CQ L ≃* S) {t : MulAut W} (ht : t ∈ Y) (hto : orderOf t = 2) :
    actS hY e ⟨t, Subgroup.mem_sup_right ht⟩ ≠ 1 := by
  intro hσ
  have hact : actionOnCQ (le_sup_left : L ≤ L ⊔ Y) (normal_sup_of_le_normalizer hY)
      ⟨t, Subgroup.mem_sup_right ht⟩ = 1 := by
    apply (MulAut.congr e).injective
    rw [← actS_apply hY e ⟨t, Subgroup.mem_sup_right ht⟩, hσ, map_one]
  have hc : t ∈ Subgroup.centralizer (L : Set (MulAut W)) := by
    have := (actionOnCQ_eq_one_iff (le_sup_left : L ≤ L ⊔ Y)
      (normal_sup_of_le_normalizer hY) hperf ⟨t, Subgroup.mem_sup_right ht⟩).1 hact
    simpa using this
  have htL : t ∈ L := mem_of_mem_centralizer_of_fstar_eq hLY hF ht hc
  have hcenter : (⟨t, htL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hc (l : MulAut W) l.2)
  have h2 : 2 ∣ Nat.card (Subgroup.center ↥L) := by
    have h := Subgroup.orderOf_dvd_natCard (Subgroup.center ↥L) hcenter
    rwa [Subgroup.orderOf_mk, hto] at h
  exact (odd_card_center_of_o2Trivial hO2).not_two_dvd_nat h2

private theorem exists_conj_inv_heis_center {W : Type} [CommGroup W]
    {Y L : Subgroup (MulAut W)} (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)))
    {S : Type} [Group S] (e : CQ L ≃* S) (hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center ↥L))
    {t : MulAut W} (ht : t ∈ Y) {z₀ : S} (hz₀ : IsHeisCenter7 z₀)
    (hinv : actS hY e ⟨t, Subgroup.mem_sup_right ht⟩ z₀ = z₀⁻¹) :
    ∃ (x y : Fin 1 → MulAut W) (z : MulAut W), HeisCfg 7 1 x y z ∧
      t * z * t⁻¹ = z⁻¹ := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨x, y₀, hcfg, hy7⟩ := hz₀
  have hK : (redHom L e).ker = Subgroup.center ↥L := by
    ext k
    rw [MonoidHom.mem_ker, redHom_eq_one_iff L e k]
  have hKp : ¬ 7 ∣ Nat.card (redHom L e).ker := by rw [hK]; exact hZ7
  obtain ⟨x', y', z', h', hx', hy', hz', hy'7⟩ :=
    HeisCfg.exists_lift (redHom L e) (redHom_surjective L e) hK.le hKp hcfg (fun _ => hy7)
  have hz'1 : L.subtype z' ≠ 1 := fun h1 => h'.z1 (Subtype.ext h1)
  have hmem : t * (z' : MulAut W) * t⁻¹ ∈ L :=
    (Subgroup.mem_set_normalizer_iff.mp (hY ht) (z' : MulAut W)).mp z'.2
  let c : ↥L := ⟨t * (z' : MulAut W) * t⁻¹, hmem⟩
  have hact : redHom L e c =
      actS hY e ⟨t, Subgroup.mem_sup_right ht⟩ (redHom L e z') := by
    rw [actS_apply, MulAut.congr_apply]
    simp only [MulEquiv.trans_apply, redHom_apply, MulEquiv.symm_apply_apply, actionOnCQ_mk]
    rfl
  have hz'p : z' ^ 7 = 1 := h'.zp
  have hzW7 : (z' : MulAut W) ^ 7 = 1 := by
    simpa using congrArg (fun u : ↥L => (u : MulAut W)) hz'p
  have hc7 : c ^ 7 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, show ((c : ↥L) : MulAut W) = t * (z' : MulAut W) * t⁻¹ from rfl,
      conj_pow (a := t) (b := (z' : MulAut W)) (i := 7), hzW7]
    simp
  have hEq : redHom L e c = redHom L e z'⁻¹ := by
    rw [hact, hz', hinv, ← hz', map_inv]
  have hcz : c = z'⁻¹ :=
    eq_of_map_eq_of_pow_eq_one (redHom L e) hK.le (p := 7) hKp hc7
      (by rw [inv_pow, h'.zp, inv_one]) hEq
  refine ⟨_, _, (z' : MulAut W), h'.map L.subtype hz'1, ?_⟩
  simpa using congrArg (fun u : ↥L => (u : MulAut W)) hcz

theorem two_pow_le_index_sq_of_inv_heis {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Y L : Subgroup (MulAut W)} (hLY : L ≤ Y) (hF : Fstar Y = L)
    (hperf : Group.IsPerfect ↥L) (hO2 : O2Trivial L)
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) {S : Type} [Group S] (e : CQ L ≃* S)
    (hZ7 : ¬ 7 ∣ Nat.card (Subgroup.center ↥L))
    (hinv : ∀ σ : MulAut S, σ * σ = 1 → σ ≠ 1 → ∃ z : S, IsHeisCenter7 z ∧ σ z = z⁻¹)
    {t : MulAut W} (ht : t ∈ Y) (hto : orderOf t = 2) :
    2 ^ (2 * 21) ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hto]
    exact pow_orderOf_eq_one t
  have hσ2 := actS_mul_self hY e ht hto
  have hσ1 : actS hY e ⟨t, Subgroup.mem_sup_right ht⟩ ≠ 1 :=
    actS_ne_one hLY hF hperf hO2 hY e ht hto
  obtain ⟨z₀, hz₀, hinvz⟩ := hinv _ hσ2 hσ1
  obtain ⟨x, y, z, hcfg, hinv'⟩ := exists_conj_inv_heis_center hY e hZ7 ht hz₀ hinvz
  have h42 : 2 ^ (2 * 21) ≤ Nat.card (imgT z) := by
    have h := two_pow_le_card_imgT_of_heisCfg_of_inv_seven hW hcfg hinv'
    rwa [show 2 * (7 ^ 1 * 3) = 2 * 21 by norm_num] at h
  rw [← index_fixV_zpowers_eq_card_imgT z] at h42
  exact h42.trans (index_fixV_le_sq_of_inverts (p := 7) (by norm_num) hcfg.zp ht2 hinv')

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
