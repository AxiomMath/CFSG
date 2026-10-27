module

public import CFSG.Timmesfeld.Exceptional.DeepQ
public import CFSG.Timmesfeld.Exceptional.DeepHData

public section

namespace CFSG.Timmesfeld.Moufang.Deep

open CFSG.Certificates CFSG.Certificates.CosetEnumeration

variable {G : Type*} [Group G]

theorem self_mem_centralizer (z : G) : z ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]

theorem mem_centralizer_of_commute {z g : G} (h : Commute z g) :
    g ∈ Subgroup.centralizer ({z} : Set G) :=
  Subgroup.mem_centralizer_iff.2 fun k hk => by rw [Set.mem_singleton_iff.1 hk]; exact h.eq

theorem zpowers_le_center (z : G) :
    Subgroup.zpowers (⟨z, self_mem_centralizer z⟩ : Subgroup.centralizer ({z} : Set G)) ≤
      Subgroup.center (Subgroup.centralizer ({z} : Set G)) := by
  rw [Subgroup.zpowers_le]
  rw [Subgroup.mem_center_iff]
  intro g
  apply Subtype.ext
  have := Subgroup.mem_centralizer_iff.1 g.2 z rfl
  simpa using this.symm

theorem eq_one_of_relations {p c q : G} {x : Fin 2 → G} (hcfg : LineConfig p c x)
    (hzq : Commute (zEl p c x) q) (hq : q * q = 1) (hpq : Commute p q)
    (hY : ∀ i, (q * yPt p c x i) ^ 2 = p) (hW : ∀ i, (q * wPt p c x i) ^ 3 = 1)
    (hZ : ∀ i, (q * zPt p c x i) ^ 5 = 1) (hodd : Odd (orderOf (q * c))) : q = 1 := by
  set y : Fin 4 → G := lineGens p c x with hy_def
  have hrel : ∀ r ∈ lineRels 2 false, signedProd y r = 1 := hcfg.signedProd_lineRels (by simp)
  set z := zEl p c x with hz_def
  have hzw : signedProd y zw = z := rfl
  have hzy : ∀ i, Commute z (y i) := zEl_commute_lineGens hcfg
  have hz3 : z ^ 3 = 1 := zEl_pow_three hcfg
  set C := Subgroup.centralizer ({z} : Set G) with hC
  set zC : C := ⟨z, self_mem_centralizer z⟩ with hzC
  set N := Subgroup.zpowers zC with hN
  have : N.Normal := Subgroup.normal_of_le_center (zpowers_le_center z)
  set π := QuotientGroup.mk' N with hπ
  set yC : Fin 4 → C := fun i => ⟨y i, mem_centralizer_of_commute (hzy i)⟩ with hyC
  have hyCw : ∀ w, ((signedProd yC w : C) : G) = signedProd y w := fun w => by
    rw [← C.coe_subtype, map_signedProd]
    rfl
  have hzCw : signedProd yC zw = zC := Subtype.ext (by rw [hyCw]; rfl)
  have hπz : π zC = 1 := (QuotientGroup.eq_one_iff zC).2 (Subgroup.mem_zpowers zC)
  set yb : Fin 4 → C ⧸ N := fun i => π (yC i) with hyb
  have hybw : ∀ w, signedProd yb w = π (signedProd yC w) := fun w => (map_signedProd π yC w).symm
  have hπ1 : ∀ g : C, (g : G) = 1 → π g = 1 := fun g hg => by
    rw [show g = 1 from Subtype.ext hg, map_one]
  have key : ∀ (u v : List (Fin 4 × Bool)) (k : ℕ), WalkA6 (u ++ zInv k ++ FreeGroup.invRev v) →
      signedProd yb u = signedProd yb v := by
    intro u v k hw
    have h := signedProd_eq_one_of_walk (y := yC) (fun r hr => Subtype.ext (by
      rw [hyCw]; exact hrel r hr)) hw
    rw [signedProd_append, signedProd_append, signedProd_zInv, signedProd_invRev, hzCw] at h
    have h' := congrArg π h
    rw [map_mul, map_mul, map_inv, map_pow, map_inv, hπz, inv_one, one_pow, mul_one,
      map_one] at h'
    rw [hybw, hybw]
    exact mul_inv_eq_one.1 h'
  have hqC : q ∈ C := mem_centralizer_of_commute hzq
  set qC : C := ⟨q, hqC⟩ with hqC_def
  set xb : Fin 3 → C ⧸ N := ![signedProd yb ua, signedProd yb ub, π qC] with hxb
  have hsub := signedProd_subst yb xb rfl rfl
  have hval : ∀ (w : List (Fin 3 × Bool)) (t : List (Fin 4 × Bool)) (k : ℕ),
      (∀ l ∈ w, l.1 ≠ 2) → WalkA6 (subst w ++ zInv k ++ FreeGroup.invRev t) →
      signedProd xb w = π (signedProd yC t) := by
    intro w t k hw hwalk
    rw [hsub w hw, key _ _ k hwalk, hybw]
  have hP : signedProd xb wP = π (yC 0) := by
    rw [hval wP [(0, true)] 1 (by decide) walk_P]
    simp [signedProd]
  have hCb : signedProd xb wC = π (yC 1) := by
    rw [hval wC [(1, true)] 1 (by decide) walk_C]
    simp [signedProd]
  have hYb : ∀ i, signedProd xb (wY i) = π (signedProd yC (tY i)) := fun i =>
    hval _ _ _ (by revert i; decide) (walk_Y i)
  have hWb : ∀ i, signedProd xb (wW i) = π (signedProd yC (tW i)) := fun i =>
    hval _ _ _ (by revert i; decide) (walk_W i)
  have hZb : ∀ i, signedProd xb (wZ i) = π (signedProd yC (tZ i)) := fun i =>
    hval _ _ _ (by revert i; decide) (walk_Z i)
  have hq2 : xb 2 = π qC := rfl
  have hx : ∀ r ∈ relsQ, signedProd xb r = 1 := by
    intro r hr
    simp only [relsQ, List.mem_append, List.mem_cons, List.not_mem_nil, or_false,
      List.mem_ofFn] at hr
    rcases hr with (((hr | hr | hr) | ⟨i, rfl⟩) | ⟨i, rfl⟩) | ⟨i, rfl⟩
    ·
      obtain ⟨i, hi⟩ : ∃ i : Fin 4, relsA6.getD i [] = r := by
        simp only [relsA6, List.mem_cons, List.not_mem_nil, or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl
        exacts [⟨0, rfl⟩, ⟨1, rfl⟩, ⟨2, rfl⟩, ⟨3, rfl⟩]
      subst hi
      rw [hval _ [] (fA6 i) (by revert i; decide) (by simpa using walk_rA6 i)]
      simp
    ·
      subst hr
      simp only [signedProd_cons, signedProd_nil, mul_one, ite_true]
      rw [hq2, ← map_mul]
      exact hπ1 _ hq
    ·
      subst hr
      rw [signedProd_append, signedProd_append, signedProd_append, signedProd_invRev, hP]
      simp only [signedProd_cons, signedProd_nil, mul_one, ite_true, Bool.false_eq_true,
        ite_false, hq2]
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      refine hπ1 _ ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyC, hqC_def]
      rw [show y 0 = p from lineGens_zero p c x, mul_assoc (q⁻¹ * p⁻¹), ← hpq.eq]
      group
    ·
      rw [signedProd_append, signedProd_append, signedProd_append, signedProd_append,
        signedProd_invRev, hP, hYb]
      simp only [signedProd_cons, signedProd_nil, mul_one, ite_true, hq2]
      rw [← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_mul]
      refine hπ1 _ ?_
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyCw]
      rw [show (yC 0 : G) = p from lineGens_zero p c x]
      have := hY i
      rw [yPt] at this
      rw [mul_inv_eq_one, ← this, sq]
      simp only [mul_assoc]
      rfl
    ·
      rw [signedProd_replicate, signedProd_append, hWb]
      simp only [signedProd_cons, signedProd_nil, mul_one, ite_true, hq2]
      rw [← map_mul, ← map_pow]
      refine hπ1 _ ?_
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, hyCw]
      exact hW i
    ·
      rw [signedProd_replicate, signedProd_append, hZb]
      simp only [signedProd_cons, signedProd_nil, mul_one, ite_true, hq2]
      rw [← map_mul, ← map_pow]
      refine hπ1 _ ?_
      simp only [Subgroup.coe_pow, Subgroup.coe_mul, hyCw]
      exact hZ i
  have hgc : signedProd xb wQC6 = π (qC * yC 1) ^ 6 := by
    rw [wQC6, signedProd_replicate, signedProd_append, hCb]
    simp only [signedProd_cons, signedProd_nil, mul_one, ite_true, hq2, map_mul]
  have h6 : π (qC * yC 1) ^ 6 = 1 := by rw [← hgc]; exact signedProd_wQC6 xb hx
  have hord : orderOf (π (qC * yC 1)) ∣ orderOf (q * c) := by
    refine (orderOf_map_dvd π _).trans ?_
    rw [← Subgroup.orderOf_coe]
    rfl
  have h3 : π (qC * yC 1) ^ 3 = 1 := by
    have h6' := orderOf_dvd_of_pow_eq_one h6
    obtain ⟨k, hk⟩ := hodd
    have hd : orderOf (π (qC * yC 1)) ∣ 3 := by
      have h2 : Nat.Coprime (orderOf (π (qC * yC 1))) 2 := by
        refine Nat.Coprime.coprime_dvd_left hord ?_
        rw [hk]
        exact Nat.coprime_comm.1 (Nat.coprime_two_left.2 (odd_two_mul_add_one k))
      have : orderOf (π (qC * yC 1)) ∣ 2 * 3 := h6'
      exact h2.dvd_of_dvd_mul_left this
    exact orderOf_dvd_iff_pow_eq_one.1 hd
  have hgc3 : signedProd xb wQC3 = 1 := by
    rw [wQC3, signedProd_replicate, signedProd_append, hCb]
    simp only [signedProd_cons, signedProd_nil, mul_one, ite_true, hq2]
    rw [← map_mul]
    exact h3
  have hq1 : π qC = 1 := eq_one_of_wQC3 xb hx hgc3 2
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 ((QuotientGroup.eq_one_iff qC).1 hq1)
  have hqz : z ^ k = q := by
    have := congrArg Subtype.val hk
    simpa using this
  have hq3 : q ^ 3 = 1 := by
    rw [← hqz, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hz3, one_zpow]
  calc q = q ^ 3 * (q * q)⁻¹ := by group
    _ = 1 := by rw [hq3, hq, inv_one, one_mul]

end CFSG.Timmesfeld.Moufang.Deep
