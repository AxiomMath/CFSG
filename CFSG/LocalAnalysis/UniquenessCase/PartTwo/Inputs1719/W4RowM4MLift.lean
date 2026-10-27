module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HeisLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem closure_conj_eq_top_of_perfect_cover {K S : Type*} [Group K] [Group S] [IsSimpleGroup S]
    (hK : Group.IsPerfect K) (π : K →* S) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center K) {t : K} (ht : π t ≠ 1) :
    Subgroup.closure {v : K | ∃ k : K, v = k * t * k⁻¹} = ⊤ := by
  haveI : Group.IsPerfect K := hK
  have hset : {v : K | ∃ k : K, v = k * t * k⁻¹} = Group.conjugatesOfSet ({t} : Set K) := by
    ext v
    constructor
    · rintro ⟨k, rfl⟩
      exact Group.mem_conjugatesOfSet_iff.2 ⟨t, rfl, isConj_iff.2 ⟨k, rfl⟩⟩
    · intro hv
      obtain ⟨a, ha, hconj⟩ := Group.mem_conjugatesOfSet_iff.1 hv
      rw [Set.mem_singleton_iff] at ha
      subst ha
      obtain ⟨k, hk⟩ := isConj_iff.1 hconj
      exact ⟨k, hk.symm⟩
  have hclosure : Subgroup.closure {v : K | ∃ k : K, v = k * t * k⁻¹}
      = Subgroup.normalClosure ({t} : Set K) := by
    rw [hset]
    rfl
  rw [hclosure]
  have hN_normal : (Subgroup.normalClosure ({t} : Set K)).Normal :=
    Subgroup.normalClosure_normal
  have ht_mem : t ∈ Subgroup.normalClosure ({t} : Set K) :=
    Subgroup.subset_normalClosure (Set.mem_singleton t)
  haveI hmap_normal : ((Subgroup.normalClosure ({t} : Set K)).map π).Normal :=
    hN_normal.map π hπ
  have hmap_top : (Subgroup.normalClosure ({t} : Set K)).map π = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((Subgroup.normalClosure ({t} : Set K)).map π) with h | h
    · exfalso
      have : π t ∈ (⊥ : Subgroup S) := h ▸ Subgroup.mem_map_of_mem π ht_mem
      exact ht (by simpa using this)
    · exact h
  have hsup : Subgroup.normalClosure ({t} : Set K) ⊔ π.ker = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : π x ∈ (Subgroup.normalClosure ({t} : Set K)).map π := by
      rw [hmap_top]; exact Subgroup.mem_top (π x)
    rw [Subgroup.mem_map] at hx
    obtain ⟨n, hn, hnx⟩ := hx
    have hz : n⁻¹ * x ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hnx, inv_mul_cancel]
    have hx_eq : n * (n⁻¹ * x) = x := by group
    rw [← hx_eq]
    exact Subgroup.mul_mem_sup hn hz
  have hker_comm : IsMulCommutative π.ker :=
    IsMulCommutative.of_comm fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hker a.2) b.1).symm
  have hcomm_le : commutator K ≤ Subgroup.normalClosure ({t} : Set K) :=
    Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top hsup hker_comm
  rw [eq_top_iff, ← hK.commutator_eq_top]
  exact hcomm_le

theorem exists_lift_noncentral_isConj {C Q : Type*} [Group C] [Group Q] (π : C →* Q)
    (hπs : Function.Surjective π) (hker : π.ker = Subgroup.center C)
    (hc2 : Nat.card (Subgroup.center C) = 2) {x y : Fin 4 → Q} {z u : Q}
    (h : HeisCfg 3 4 x y z) (hy : ∀ i, y i ^ 3 = 1)
    (hu : u ∈ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}))
    (huz : u ∉ Subgroup.zpowers z) (hconj : IsConj u z) :
    ∃ (x' y' : Fin 4 → C) (z' u' : C), HeisCfg 3 4 x' y' z' ∧ (∀ i, y' i ^ 3 = 1) ∧
      u' ∈ Subgroup.closure (Set.range x' ∪ Set.range y' ∪ {z'}) ∧
      u' ∉ Subgroup.zpowers z' ∧ IsConj u' z' := by
  have hker_card : Nat.card π.ker = 2 := by rw [hker, hc2]
  have hKp : ¬ 3 ∣ Nat.card π.ker := by rw [hker_card]; norm_num
  obtain ⟨xL, yL, zL, hL, hxL, hyL, hzL, hyL3⟩ :=
    HeisCfg.exists_lift π hπs (le_of_eq hker) hKp h hy
  let Q' : Subgroup C := Subgroup.closure (Set.range xL ∪ Set.range yL ∪ {zL})
  have hxL_mem : ∀ i, xL i ∈ Q' := fun i =>
    Subgroup.subset_closure (Or.inl (Or.inl ⟨i, rfl⟩))
  have hyL_mem : ∀ i, yL i ∈ Q' := fun i =>
    Subgroup.subset_closure (Or.inl (Or.inr ⟨i, rfl⟩))
  have hzL_mem : zL ∈ Q' := Subgroup.subset_closure (Or.inr rfl)
  have hle : Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}) ≤ Q'.map π := by
    rw [Subgroup.closure_le]
    intro w hw
    rcases hw with hw | hw
    · rcases hw with hw | hw
      · obtain ⟨i, rfl⟩ := hw
        rw [← hxL i]
        exact Subgroup.mem_map_of_mem π (hxL_mem i)
      · obtain ⟨i, rfl⟩ := hw
        rw [← hyL i]
        exact Subgroup.mem_map_of_mem π (hyL_mem i)
    · obtain rfl := Set.mem_singleton_iff.mp hw
      rw [← hzL]
      exact Subgroup.mem_map_of_mem π hzL_mem
  obtain ⟨u0, hu0_mem, hu0⟩ := Subgroup.mem_map.mp (hle hu)
  have hu3 : u ^ 3 = 1 := by
    obtain ⟨c, hc⟩ := isConj_iff.1 hconj
    have huc : u = c⁻¹ * z * (c⁻¹)⁻¹ := by rw [← hc]; group
    rw [huc, conj_pow, h.zp]
    group
  have hu0_3_ker : u0 ^ 3 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow, hu0, hu3]
  have hu0_6 : (u0 ^ 3) ^ 2 = 1 := by
    have h6 := pow_card_eq_one' (G := π.ker) (x := ⟨u0 ^ 3, hu0_3_ker⟩)
    rw [hker_card] at h6
    exact congrArg Subtype.val h6
  set u' : C := u0 ^ 4 with hu'_def
  have hpi_u' : π u' = u := by
    rw [hu'_def, map_pow, hu0]
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_add, hu3, one_mul, pow_one]
  have hu0_six : u0 ^ 6 = 1 := by
    rw [show (6 : ℕ) = 3 * 2 from rfl, pow_mul, hu0_6]
  have hu'_3 : u' ^ 3 = 1 := by
    rw [hu'_def, ← pow_mul]
    rw [show (4 * 3 : ℕ) = 6 * 2 from rfl, pow_mul, hu0_six, one_pow]
  have hu'_mem : u' ∈ Q' := by
    rw [hu'_def]
    exact Q'.pow_mem hu0_mem 4
  obtain ⟨c, hc⟩ := isConj_iff.1 hconj
  obtain ⟨c0, hc0⟩ := hπs c
  set a : C := c0 * u' * c0⁻¹ with ha_def
  have ha_pi : π a = z := by
    rw [ha_def, map_mul, map_mul, map_inv, hc0, hpi_u', hc]
  have ha_3 : a ^ 3 = 1 := by
    rw [ha_def, conj_pow, hu'_3]
    group
  have hk_mem : zL⁻¹ * a ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hzL, ha_pi, inv_mul_cancel]
  have hk_center : zL⁻¹ * a ∈ Subgroup.center C := by
    rw [← hker]; exact hk_mem
  have hcomm_zk : Commute zL (zL⁻¹ * a) := Subgroup.mem_center_iff.1 hk_center zL
  have hk_3 : (zL⁻¹ * a) ^ 3 = 1 := by
    have ha_eq : a = zL * (zL⁻¹ * a) := by group
    rw [ha_eq, hcomm_zk.mul_pow 3] at ha_3
    rw [hL.zp, one_mul] at ha_3
    exact ha_3
  have hk_2 : (zL⁻¹ * a) ^ 2 = 1 := by
    have h2 := pow_card_eq_one' (G := π.ker) (x := ⟨zL⁻¹ * a, hk_mem⟩)
    rw [hker_card] at h2
    exact congrArg Subtype.val h2
  have hk_eq_one : zL⁻¹ * a = 1 := by
    have h1 : (zL⁻¹ * a) ^ 3 = zL⁻¹ * a := by rw [pow_succ, hk_2, one_mul]
    rw [← h1, hk_3]
  have ha_eq_z : a = zL := by
    have h2 : zL * (zL⁻¹ * a) = a := by group
    rw [hk_eq_one, mul_one] at h2
    exact h2.symm
  have hisConj : IsConj u' zL := by
    rw [isConj_iff]
    exact ⟨c0, by rw [← ha_def, ha_eq_z]⟩
  have hu'_not_zpowers : u' ∉ Subgroup.zpowers zL := by
    intro hmem
    apply huz
    have hmem' : π u' ∈ (Subgroup.zpowers zL).map π := Subgroup.mem_map_of_mem π hmem
    rw [MonoidHom.map_zpowers, hzL, hpi_u'] at hmem'
    exact hmem'
  exact ⟨xL, yL, zL, u', hL, hyL3, hu'_mem, hu'_not_zpowers, hisConj⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row
