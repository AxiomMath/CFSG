module

public import CFSG.Quasithin.Recognition.RuTypeJ47k
public import CFSG.Quasithin.Recognition.RuTypeQuasithin
public import CFSG.Quasithin.Recognition.RuTypeJ45a

public section

namespace CFSG.Quasithin.RuType

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Sporadic.Schreier.Tits
open CFSG.Quasithin.RankTwoAmalgam.Completion

namespace J47

section Path

variable {V : Type*} {Γ : SimpleGraph V}

@[expose] def path8 (v0 v1 v2 v3 v4 v5 v6 v7 v8 : V) (h01 : Γ.Adj v0 v1) (h12 : Γ.Adj v1 v2)
    (h23 : Γ.Adj v2 v3) (h34 : Γ.Adj v3 v4) (h45 : Γ.Adj v4 v5) (h56 : Γ.Adj v5 v6)
    (h67 : Γ.Adj v6 v7) (h78 : Γ.Adj v7 v8) : GPath Γ 8 where
  toFun i := match i with
    | 0 => v0
    | 1 => v1
    | 2 => v2
    | 3 => v3
    | 4 => v4
    | 5 => v5
    | 6 => v6
    | 7 => v7
    | _ => v8
  adj i hi := by
    interval_cases i
    exacts [h01, h12, h23, h34, h45, h56, h67, h78]
  tail i hi := by
    obtain ⟨k, rfl⟩ : ∃ k, i = k + 8 := ⟨i - 8, by omega⟩
    rfl

end Path

section Small

variable {α : RankTwoAmalgam.{0}} {Y : Type} [Group Y] {c : α.Completion Y}

theorem adj_smul (g : c.G0) {u v : c.Γ} (h : c.graph.Adj u v) : c.graph.Adj (g • u) (g • v) :=
  (CosetGeom.smul_adj g).mpr h

theorem smul_xv_ne_of_not_mem {g : c.G0} (h : g ∉ (f1 (c := c)).range) : g • c.xv ≠ c.xv :=
  fun h' => h (by rw [← stv_xv_eq_range]; exact MulAction.mem_stabilizer_iff.mpr h')

theorem smul_lv_ne_of_not_mem {g : c.G0} (h : g ∉ (f2 (c := c)).range) : g • c.lv ≠ c.lv :=
  fun h' => h (stv_lv_le_range_f2 c (MulAction.mem_stabilizer_iff.mpr h'))

theorem isSmall_of_conf (F : c.Facts46 8) {a ee bb cc : c.G0} (ha : a • c.lv = c.lv)
    (ha' : a • c.xv ≠ c.xv) (he : ee • c.xv = c.xv) (he' : ee • c.lv ≠ c.lv)
    (hb : bb • c.xv = c.xv) (hb' : bb • c.lv ≠ c.lv) (hc : cc • c.xv = c.xv)
    (hc' : cc • c.lv ≠ c.lv)
    (hcomm : bb * ((a * ee * a⁻¹) * cc * (a * ee * a⁻¹)⁻¹) =
      ((a * ee * a⁻¹) * cc * (a * ee * a⁻¹)⁻¹) * bb) : c.IsSmall 8 := by
  obtain ⟨j, hj⟩ : ∃ j, j = a * ee * a⁻¹ := ⟨_, rfl⟩
  obtain ⟨b', hbd⟩ : ∃ b', b' = j * cc * j⁻¹ := ⟨_, rfl⟩
  rw [← hj, ← hbd] at hcomm
  have hadj : c.graph.Adj c.xv c.lv := CosetGeom.adj_γ₀_γ₁
  have hai : a⁻¹ • c.lv = c.lv := by rw [inv_smul_eq_iff, ha]
  have hb'4 : b' • (j • c.xv) = j • c.xv := by
    rw [← mul_smul, hbd, show j * cc * j⁻¹ * j = j * cc by group, mul_smul, hc]
  have h12 : c.graph.Adj c.lv (a • c.xv) := by
    have h := adj_smul a hadj
    rw [ha] at h
    exact h.symm
  have h23 : c.graph.Adj (a • c.xv) ((a * ee) • c.lv) := by
    have h := adj_smul (a * ee) hadj
    rwa [mul_smul a ee c.xv, he] at h
  have h34 : c.graph.Adj ((a * ee) • c.lv) (j • c.xv) := by
    have h0 := adj_smul a⁻¹ hadj
    rw [hai] at h0
    have h := adj_smul (a * ee) h0.symm
    rwa [← mul_smul, show a * ee * a⁻¹ = j from hj.symm] at h
  have h45 : c.graph.Adj (j • c.xv) (b' • ((a * ee) • c.lv)) := by
    have h := adj_smul b' h34.symm
    rwa [hb'4] at h
  have h56 := adj_smul b' h23.symm
  have h67 := adj_smul b' h12.symm
  have h78 := adj_smul b' hadj.symm
  set p := path8 c.xv c.lv (a • c.xv) ((a * ee) • c.lv) (j • c.xv) (b' • ((a * ee) • c.lv))
    (b' • (a • c.xv)) (b' • c.lv) (b' • c.xv) hadj h12 h23 h34 h45 h56 h67 h78 with hp
  have n0 : c.xv ≠ a • c.xv := fun h => ha' h.symm
  have n1 : c.lv ≠ (a * ee) • c.lv := by
    intro h
    apply he'
    calc ee • c.lv = a⁻¹ • ((a * ee) • c.lv) := by rw [mul_smul, inv_smul_smul]
      _ = c.lv := by rw [← h, hai]
  have n2 : a • c.xv ≠ j • c.xv := by
    intro h
    apply ha'
    have h1 : c.xv = ee • (a⁻¹ • c.xv) := by
      rw [hj, mul_smul, mul_smul] at h
      exact smul_left_cancel a h
    have h2 : a⁻¹ • c.xv = c.xv := by
      calc a⁻¹ • c.xv = ee⁻¹ • (ee • (a⁻¹ • c.xv)) := by rw [inv_smul_smul]
        _ = ee⁻¹ • c.xv := by rw [← h1]
        _ = c.xv := by rw [inv_smul_eq_iff, he]
    calc a • c.xv = a • (a⁻¹ • c.xv) := by rw [h2]
      _ = c.xv := smul_inv_smul a c.xv
  have n3 : (a * ee) • c.lv ≠ b' • ((a * ee) • c.lv) := by
    intro h
    apply hc'
    have e : (a * ee)⁻¹ * b' * (a * ee) = a⁻¹ * cc * a := by rw [hbd, hj]; group
    have h1 : ((a * ee)⁻¹ * b' * (a * ee)) • c.lv = c.lv := by
      rw [mul_smul, mul_smul, ← h, inv_smul_smul]
    rw [e, mul_smul, mul_smul, ha] at h1
    calc cc • c.lv = a • (a⁻¹ • (cc • c.lv)) := by rw [smul_inv_smul]
      _ = a • c.lv := by rw [h1]
      _ = c.lv := ha
  have hnb : p.NoBack := by
    intro i hi
    have hi' : i ≤ 6 := by omega
    interval_cases i
    · exact n0
    · exact n1
    · exact n2
    · exact n3
    · intro h
      exact n2 (smul_left_cancel b' (h.symm.trans hb'4.symm))
    · exact fun h => n1 (smul_left_cancel b' h).symm
    · exact fun h => n0 (smul_left_cancel b' h).symm
  have hpm : p ∈ GPath.nbPaths c.graph c.xv 8 := ⟨rfl, hnb⟩
  have hd : c.graph.dist c.xv (b' • c.xv) = 8 := F.dist_m c.xv p hpm
  intro hl
  have hq8 : (bb • p) 8 = b' • c.xv := by
    show bb • (b' • c.xv) = b' • c.xv
    rw [← mul_smul, hcomm, mul_smul, hb]
  have hq0 : (bb • p) 0 = c.xv := hb
  have hpq := hl p (bb • p) hd (by rw [GPath.IsGeodesic, hq0, hq8]; exact hd) hq0.symm hq8.symm
  have h7 := congrArg (fun r : GPath c.graph 8 => r 7) hpq
  have h7' : b' • c.lv = bb • (b' • c.lv) := h7
  apply hb'
  have h8 : b' • (bb • c.lv) = b' • c.lv := by rw [← mul_smul, ← hcomm, mul_smul, ← h7']
  exact smul_left_cancel b' h8

end Small

theorem sup_twoF4H_N :
    twoF4H ⊔ twoF4N = twoF4M := by
  apply le_antisymm (sup_le twoF4H_le_twoF4M twoF4N_le_M)
  have hD : titsD ≤ twoF4H ⊔ twoF4N := by
    rw [← titsH_sup_N]
    exact sup_le_sup (fun y hy => Or.inl hy) (fun y hy => Or.inl hy)
  have hπ : tπ ∈ twoF4H := Or.inr (by rw [mul_inv_cancel]; exact one_mem _)
  intro x hx
  rcases hx with h | h
  · exact hD h
  · have := mul_mem (hD h) (Subgroup.mem_sup_left hπ)
    rwa [inv_mul_cancel_right] at this

section Beta

variable {G : Type} [Group G] {F1 F2 : Subgroup G}

theorem mem_H_of_hom2_mem_F1
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (x : ↥twoF4N) (hx : hom2 e x ∈ F1) : (x : Equiv.Perm (Fin 1755)) ∈ twoF4H := by
  set g := (phi12 e).symm ⟨hom2 e x, Subgroup.mem_inf.mpr ⟨hx, hom2_mem e x⟩⟩ with hg
  have h1 := phi12_eq_phi2 e g
  have h2 : phi12 e g = ⟨hom2 e x, Subgroup.mem_inf.mpr ⟨hx, hom2_mem e x⟩⟩ := by
    rw [hg, MulEquiv.apply_symm_apply]
  rw [h2] at h1
  have hxs : x = ⟨(g : Equiv.Perm (Fin 1755)), (Subgroup.mem_inf.mp g.2).2⟩ := by
    apply hom2_injective e
    rw [hom2_apply, hom2_apply]
    exact h1
  rw [hxs]
  exact (Subgroup.mem_inf.mp g.2).1

@[expose] noncomputable def beta
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2)) :
    (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Completion ↥(F1 ⊔ F2) :=
  precompIso e (subCompletion F1 F2)

noncomputable abbrev toG
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (g : (beta e).G0) : G := ((g : ↥(F1 ⊔ F2)) : G)

theorem toG_injective
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2)) :
    Function.Injective (toG e) := fun _ _ h => Subtype.ext (Subtype.ext h)

theorem toG_f1
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (x : ↥twoF4H) : toG e (f1 (c := beta e) x) = hom1 e x := rfl

theorem toG_f2
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (x : ↥twoF4N) : toG e (f2 (c := beta e) x) = hom2 e x := rfl

theorem mem_range_f1_iff
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (g : (beta e).G0) : g ∈ (f1 (c := beta e)).range ↔ toG e g ∈ F1 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact hom1_mem e x
  · intro h
    obtain ⟨x, hx⟩ := exists_hom1_eq e h
    exact ⟨x, toG_injective e (by rw [toG_f1, hx])⟩

theorem mem_range_f2_iff
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups F1 F2))
    (g : (beta e).G0) : g ∈ (f2 (c := beta e)).range ↔ toG e g ∈ F2 := by
  constructor
  · rintro ⟨x, rfl⟩
    exact hom2_mem e x
  · intro h
    refine ⟨(phi2 e).symm ⟨toG e g, h⟩, toG_injective e ?_⟩
    rw [toG_f2, hom2_apply, MulEquiv.apply_symm_apply]

end Beta

end J47

namespace RuDataM

open J47

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_F1_inf_F2 (M : RuDataM G) {x : G}
    (h1 : x ∈ M.F1) (h2 : x ∈ M.F2) (hx5 : x ^ 5 = 1) : x = 1 := by
  have hT : x ∈ M.TF := by rw [← M.F1_inf_F2]; exact ⟨h1, h2⟩
  have h := Subgroup.orderOf_dvd_natCard _ hT
  rw [M.card_TF] at h
  have h4096 : x ^ 4096 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by simpa using h)
  have := (pow_gcd_eq_one (a := x)).mpr ⟨hx5, h4096⟩
  rwa [show Nat.gcd 5 4096 = 1 by norm_num, pow_one] at this

theorem isSmall_beta
    (M : RuDataM G) (h45 : F45TwoF4)
    (e : (RankTwoAmalgam.ofSubgroups twoF4H twoF4N).Iso (RankTwoAmalgam.ofSubgroups M.F1 M.F2)) :
    (beta e).IsSmall 8 := by
  have hβ : (beta e).IsFaithful := precompIso_isFaithful e (subCompletion_isFaithful _ _)
  have F : (beta e).Facts46 8 := LieSetting.Facts45L.facts46 h45 (beta e) hβ
  obtain ⟨w, hw5, hw1, hwb, hjw⟩ := (M.conf47 e).exists_mem_F1_conj
  have hjw' : jG e * w * (jG e)⁻¹ ∈ M.F1 := hjw
  have hwb' : w * bG e = bG e * w := hwb
  obtain ⟨h', hh'⟩ := exists_hom1_eq e hjw'
  have hjj : jG e * jG e = 1 := jG_mul_self e
  have hjinv : (jG e)⁻¹ = jG e := inv_eq_of_mul_eq_one_right hjj
  refine isSmall_of_conf F (a := f2 (c := beta e) ⟨a1P, a1P_mem_N⟩)
    (ee := f1 (c := beta e) ⟨eP, eP_mem_H⟩) (bb := f1 (c := beta e) ⟨b0P, b0P_mem_H⟩)
    (cc := f1 (c := beta e) h') (f2_smul_lv _) (smul_xv_ne_of_not_mem ?_) (f1_smul_xv _)
    (smul_lv_ne_of_not_mem ?_) (f1_smul_xv _) (smul_lv_ne_of_not_mem ?_) (f1_smul_xv _)
    (smul_lv_ne_of_not_mem ?_) ?_
  · rw [mem_range_f1_iff]
    intro h
    exact a1P_not_mem_H (mem_H_of_hom2_mem_F1 e _ h)
  · rw [mem_range_f2_iff]
    intro h
    exact eP_not_mem_N (mem_N_of_hom1_mem_F2 e _ h)
  · rw [mem_range_f2_iff]
    intro h
    exact bG_ne_one e (M.eq_one_of_mem_F1_inf_F2 (hom1_mem e _) h (bG_pow_five e))
  · rw [mem_range_f2_iff]
    intro h
    have h2 : jG e * w * (jG e)⁻¹ ∈ M.F2 := by
      have h3 : toG e (f1 (c := beta e) h') = hom1 e h' := rfl
      rw [h3, hh'] at h
      exact h
    apply hw1
    have h3 := M.eq_one_of_mem_F1_inf_F2 hjw' h2 (by rw [conj_pow, hw5]; group)
    calc w = (jG e)⁻¹ * (jG e * w * (jG e)⁻¹) * jG e := by group
      _ = 1 := by rw [h3]; group
  · apply toG_injective e
    show bG e * (jG e * hom1 e h' * (jG e)⁻¹) = jG e * hom1 e h' * (jG e)⁻¹ * bG e
    have hjw2 : jG e * hom1 e h' * (jG e)⁻¹ = w := by
      rw [hh', hjinv]
      calc jG e * (jG e * w * jG e) * jG e = (jG e * jG e) * w * (jG e * jG e) := by group
        _ = w := by rw [hjj]; group
    rw [hjw2]
    exact hwb'.symm

theorem theorem_J47
    (M : RuDataM G) (hHay : HayashiFiveThree) (h45 : F45TwoF4) (h48 : F48TwoF4) :
    Nonempty (↥(M.F1 ⊔ M.F2) ≃* CFSG.Sporadic.Schreier.Tits.titsA) := by
  have hRu : IsTypeRu G := ⟨M.L, M.one, M.T, M.two⟩
  obtain ⟨e⟩ := exists_amalgamIso_of_case2F4 (M.case2F4 hHay (isQuasithinSub_of_isTypeRu hRu _))
  have hβ : (beta e).IsFaithful := precompIso_isFaithful e (subCompletion_isFaithful _ _)
  have hF := h48 ↥(M.F1 ⊔ M.F2) (beta e) hβ (M.isSmall_beta h45 e)
  obtain ⟨-, h2⟩ := hF
  obtain ⟨φ, -, -⟩ := h2 rfl
  have hsup : twoF4H ⊔ twoF4N = CFSG.Sporadic.Schreier.Tits.titsA :=
    sup_twoF4H_N.trans twoF4M_eq_titsA
  exact ⟨φ.trans (MulEquiv.subgroupCongr hsup)⟩

end RuDataM

end CFSG.Quasithin.RuType
