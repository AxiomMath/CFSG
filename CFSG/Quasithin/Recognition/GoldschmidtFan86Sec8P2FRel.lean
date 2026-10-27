module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P2FCal
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P3AY
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4Loc

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec8P2F

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
  {F : FanTree Γ G} {L : ZLab Γ G} {α : V} (D : D10Set L α)

theorem comm_of_fcomm_eq_one {a b : G} (h : fcomm a b = 1) : a * b = b * a := by
  have h1 : b⁻¹ * a * b = a := by
    calc b⁻¹ * a * b = a * (a⁻¹ * b⁻¹ * a * b) := by group
      _ = a := by rw [show a⁻¹ * b⁻¹ * a * b = 1 from h, mul_one]
  calc a * b = b * (b⁻¹ * a * b) := by group
    _ = b * a := by rw [h1]

theorem y_zero (δ' : V) : D.y δ' 0 = L.z (D.delta 0) * L.z δ' := by
  simp [D10Set.y]

theorem fiveRel (F : FanTree Γ G) (h71c : Fan71c F L) (h83a : Fan83a F L) (h83b : Fan83b F L)
    (h83d : Fan83d F L) {δ' : V} (hY : D.IsYPair δ') :
    FiveRel (D.y δ') (fun m => L.z (D.alpha m)) (L.z α) := by
  have hz2 : ∀ m, L.z (D.alpha m) * L.z (D.alpha m) = 1 := fun m =>
    L.z_mul_self (D.valence_alpha F m)
  have hy2 := Sec8P3.y_mul_self D F h71c hY
  have hyinv : ∀ i, (D.y δ' i)⁻¹ = D.y δ' i := fun i => inv_eq_of_mul_eq_one_right (hy2 i)
  have hzinv : ∀ m, (L.z (D.alpha m))⁻¹ = L.z (D.alpha m) := fun m =>
    inv_eq_of_mul_eq_one_right (hz2 m)
  have hc : ∀ i, D.y δ' i * L.z (D.alpha i) = L.z (D.alpha i) * D.y δ' i := fun i => by
    have h : fcomm (D.y δ' i) (L.z (D.alpha i)) = 1 := by simpa using h83b α D δ' hY i i
    exact comm_of_fcomm_eq_one h
  refine ⟨hy2, hz2, L.z_mul_self D.val, fun m n => ?_, fun m => ?_, fun i => ?_,
    fun i m hne => ?_, fun i => ?_, fun i j hij => ?_⟩
  · exact comm_of_fcomm_eq_one (Sec8P3.zGroup_fcomm h71c _ (Sec8P3.z_alpha_mem_zGroup D F m) _
      (Sec8P3.z_alpha_mem_zGroup D F n))
  · exact comm_of_fcomm_eq_one (Sec8P3.zGroup_fcomm h71c _ (Sec8P3.z_alpha_mem_zGroup D F m) _
      (Sec8P3.z_mem_zGroup D.val))
  · show D.y δ' i * L.z (D.alpha i) * D.y δ' i = L.z (D.alpha i)
    rw [hc i, mul_assoc, hy2 i, mul_one]
  · show D.y δ' i * L.z (D.alpha m) * D.y δ' i = L.z (D.alpha m) * L.z α
    have h : fcomm (D.y δ' i) (L.z (D.alpha m)) = L.z α := by
      simpa [hne] using h83b α D δ' hY i m
    unfold fcomm at h
    rw [hyinv, hzinv] at h
    have hw : L.z (D.alpha m) * L.z α = L.z α * L.z (D.alpha m) :=
      comm_of_fcomm_eq_one (Sec8P3.zGroup_fcomm h71c _ (Sec8P3.z_alpha_mem_zGroup D F m) _
        (Sec8P3.z_mem_zGroup D.val))
    calc D.y δ' i * L.z (D.alpha m) * D.y δ' i
        = (D.y δ' i * L.z (D.alpha m) * D.y δ' i * L.z (D.alpha m)) * L.z (D.alpha m) := by
          rw [mul_assoc _ (L.z (D.alpha m)) (L.z (D.alpha m)), hz2 m, mul_one]
      _ = L.z α * L.z (D.alpha m) := by rw [h]
      _ = L.z (D.alpha m) * L.z α := hw.symm
  · have hy : D.y δ' i ∈ MulAction.stabilizer G α :=
      F.nbrStab_le_stabilizer α (Sec8P3.y_mem_nbrStab D h83a hY i)
    exact L.comm_z_of_mem_stabilizer D.val hy
  · have h := h83d.2 α D δ' hY i j hij
    unfold fcomm at h
    rw [hyinv, hyinv] at h
    show D.y δ' i * D.y δ' j = _
    have hmid : D.y δ' i * D.y δ' j * D.y δ' i * D.y δ' j * (D.y δ' j * D.y δ' i) =
        D.y δ' i * D.y δ' j := by
      calc D.y δ' i * D.y δ' j * D.y δ' i * D.y δ' j * (D.y δ' j * D.y δ' i)
          = D.y δ' i * D.y δ' j * D.y δ' i * (D.y δ' j * D.y δ' j) * D.y δ' i := by
            simp only [mul_assoc]
        _ = D.y δ' i * D.y δ' j * (D.y δ' i * D.y δ' i) := by
            rw [hy2 j, mul_one]
            simp only [mul_assoc]
        _ = D.y δ' i * D.y δ' j := by rw [hy2 i, mul_one]
    calc D.y δ' i * D.y δ' j
        = (D.y δ' i * D.y δ' j * D.y δ' i * D.y δ' j) * (D.y δ' j * D.y δ' i) := hmid.symm
      _ = _ := by rw [h]

theorem y_shift (δ' : V) (i : Fin 5) : D.x⁻¹ * D.y δ' i * D.x = D.y δ' (i + 1) := by
  have hx5 := D.x_pow_five
  have hn : D.x ^ ((i + 1 : Fin 5) : ℕ) = D.x ^ ((i : ℕ) + 1) := by
    rw [pow_eq_pow_mod ((i : ℕ) + 1) hx5]
    congr 1
  unfold D10Set.y
  rw [hn]
  group

theorem refl_one_two (F : FanTree Γ G) (h71c : Fan71c F L) {δ' : V} (hY : D.IsYPair δ') :
    L.z (D.delta 0) * D.y δ' 1 * L.z (D.delta 0) = D.y δ' 4 ∧
      L.z (D.delta 0) * D.y δ' 2 * L.z (D.delta 0) = D.y δ' 3 := by
  have hv' := Sec8P3.valence_of_isYPair D F hY
  have h0 := D.zd_mul_self F 0
  have hzinv : (L.z (D.delta 0))⁻¹ = L.z (D.delta 0) := inv_eq_of_mul_eq_one_right h0
  have hzx := D.zd_x_inv F
  have hx5 := D.x_pow_five
  have hcomm : L.z (D.delta 0) * L.z δ' = L.z δ' * L.z (D.delta 0) := by
    refine h71c.z_comm_of_dist_le (D.valence_delta F 0) hv' ?_
    have h1 := F.isTree.connected.dist_triangle (u := D.delta 0) (v := D.alpha 0) (w := δ')
    have h2 : Γ.dist (D.delta 0) (D.alpha 0) = Γ.dist (D.alpha 0) (D.delta 0) :=
      SimpleGraph.dist_comm
    rw [h2, D.dist_alpha_delta F 0, hY.2.2.2.2.1] at h1
    omega
  have hy0 : L.z (D.delta 0) * (L.z (D.delta 0) * L.z δ') * L.z (D.delta 0) =
      L.z (D.delta 0) * L.z δ' := by
    calc L.z (D.delta 0) * (L.z (D.delta 0) * L.z δ') * L.z (D.delta 0)
        = (L.z (D.delta 0) * L.z (D.delta 0)) * (L.z δ' * L.z (D.delta 0)) := by
          simp only [mul_assoc]
      _ = L.z (D.delta 0) * L.z δ' := by rw [h0, one_mul, ← hcomm]
  have hzp : ∀ n : ℕ, L.z (D.delta 0) * D.x ^ n * L.z (D.delta 0) = (D.x ^ n)⁻¹ := fun n => by
    have h1 : (L.z (D.delta 0) * D.x * (L.z (D.delta 0))⁻¹) ^ n =
        L.z (D.delta 0) * D.x ^ n * (L.z (D.delta 0))⁻¹ := conj_pow
    rw [hzinv] at h1
    rw [← h1, hzx, inv_pow]
  have hzp' : ∀ n : ℕ, L.z (D.delta 0) * (D.x ^ n)⁻¹ * L.z (D.delta 0) = D.x ^ n := fun n => by
    calc L.z (D.delta 0) * (D.x ^ n)⁻¹ * L.z (D.delta 0)
        = L.z (D.delta 0) * (L.z (D.delta 0) * D.x ^ n * L.z (D.delta 0)) * L.z (D.delta 0) := by
          rw [hzp n]
      _ = (L.z (D.delta 0) * L.z (D.delta 0)) * D.x ^ n *
          (L.z (D.delta 0) * L.z (D.delta 0)) := by simp only [mul_assoc]
      _ = D.x ^ n := by rw [h0, one_mul, mul_one]
  have key : ∀ n m : ℕ, n + m = 5 →
      L.z (D.delta 0) * ((D.x ^ n)⁻¹ * (L.z (D.delta 0) * L.z δ') * D.x ^ n) *
        L.z (D.delta 0) = (D.x ^ m)⁻¹ * (L.z (D.delta 0) * L.z δ') * D.x ^ m := by
    intro n m hnm
    have hxx : D.x ^ n * D.x ^ m = 1 := by rw [← pow_add, hnm, hx5]
    rw [inv_eq_of_mul_eq_one_left hxx, ← inv_eq_of_mul_eq_one_right hxx,
      conj_mul h0, conj_mul h0, hzp' n, hzp n, hy0]
  exact ⟨key 1 4 (by norm_num), key 2 3 (by norm_num)⟩

end Sec8P2F

end CFSG.Quasithin.Fan86
