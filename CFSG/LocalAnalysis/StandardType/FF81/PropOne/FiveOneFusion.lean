module

public import CFSG.LocalAnalysis.StandardType.FF81.PropOne.QSylow
public import CFSG.Mathlib.GroupTheory.WeakClosureFusion

@[expose] public section

namespace CFSG.StandardType.FF81.PropOne

open scoped Pointwise

open CFSG.RankThree.PartTwo.Sec4.Item434Kit (vecElt)

private theorem conj_vecElt_cycle {G : Type} [Group G] {z : Fin 3 → G}
    (hc : ∀ i j, z i * z j = z j * z i) {c : G}
    (hc0 : c * z 0 * c⁻¹ = z 1) (hc1 : c * z 1 * c⁻¹ = z 2)
    (hc2 : c * z 2 * c⁻¹ = z 0) (v : Fin 3 → ZMod 3) :
    c * vecElt z v * c⁻¹ =
      vecElt z (fun i => if i = 0 then v 2 else if i = 1 then v 0 else v 1) := by
  have hc' : ∀ x : G, c * x * c⁻¹ = MulAut.conj c x := fun x => rfl
  rw [hc', vecElt, map_mul, map_mul, map_pow, map_pow, map_pow, ← hc', ← hc', ← hc',
    hc0, hc1, hc2, vecElt]
  simp only [Fin.isValue, Fin.reduceEq, if_true, if_false]
  have h10 : z 1 ^ (v 0).val * z 0 ^ (v 2).val = z 0 ^ (v 2).val * z 1 ^ (v 0).val :=
    (Commute.pow_pow (show Commute (z 1) (z 0) from hc 1 0) _ _).eq
  have h12 : z 1 ^ (v 0).val * z 2 ^ (v 1).val = z 2 ^ (v 1).val * z 1 ^ (v 0).val :=
    (Commute.pow_pow (show Commute (z 1) (z 2) from hc 1 2) _ _).eq
  have h20 : z 2 ^ (v 1).val * z 0 ^ (v 2).val = z 0 ^ (v 2).val * z 2 ^ (v 1).val :=
    (Commute.pow_pow (show Commute (z 2) (z 0) from hc 2 0) _ _).eq
  calc z 1 ^ (v 0).val * z 2 ^ (v 1).val * z 0 ^ (v 2).val
      = (z 1 ^ (v 0).val * z 2 ^ (v 1).val) * z 0 ^ (v 2).val := by group
    _ = (z 2 ^ (v 1).val * z 1 ^ (v 0).val) * z 0 ^ (v 2).val := by rw [h12]
    _ = z 2 ^ (v 1).val * (z 1 ^ (v 0).val * z 0 ^ (v 2).val) := by group
    _ = z 2 ^ (v 1).val * (z 0 ^ (v 2).val * z 1 ^ (v 0).val) := by rw [h10]
    _ = (z 2 ^ (v 1).val * z 0 ^ (v 2).val) * z 1 ^ (v 0).val := by group
    _ = (z 0 ^ (v 2).val * z 2 ^ (v 1).val) * z 1 ^ (v 0).val := by rw [h20]
    _ = z 0 ^ (v 2).val * (z 2 ^ (v 1).val * z 1 ^ (v 0).val) := by group
    _ = z 0 ^ (v 2).val * (z 1 ^ (v 0).val * z 2 ^ (v 1).val) := by rw [← h12]
    _ = z 0 ^ (v 2).val * z 1 ^ (v 0).val * z 2 ^ (v 1).val := by group

private theorem vecElt_const {G : Type} [Group G] {z : Fin 3 → G}
    (hc : ∀ i j, z i * z j = z j * z i) (a : ZMod 3) :
    vecElt z (fun _ => a) = (z 0 * z 1 * z 2) ^ a.val := by
  rw [vecElt]
  have h01 : Commute (z 0) (z 1) := hc 0 1
  have h012 : Commute (z 0 * z 1) (z 2) := Commute.mul_left (hc 0 2) (hc 1 2)
  rw [h012.mul_pow, h01.mul_pow]

private theorem commute_conj_of_commute {G : Type} [Group G] {s b x : G}
    (h : b * (s * x * s⁻¹) = (s * x * s⁻¹) * b) :
    (s⁻¹ * b * s) * x = x * (s⁻¹ * b * s) := by
  calc (s⁻¹ * b * s) * x
      = s⁻¹ * (b * (s * x * s⁻¹)) * s := by group
    _ = s⁻¹ * ((s * x * s⁻¹) * b) * s := by rw [h]
    _ = x * (s⁻¹ * b * s) := by group

private theorem exists_pow_of_mem_center {G : Type} [Group G] [Finite G] {n : ℕ} {b : G}
    {L : Subgroup G} {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ A : Subgroup G}
    {τ c : G} (hB₂ : B2Package b z B₂) (hA : AStar b z B₂ A) (hτc : TauC z τ c)
    (hS : SylowData b B₂ A c) {y : G}
    (hyS : y ∈ A ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G))
    (hyZ : ∀ x ∈ (A ⊔ (Subgroup.zpowers b ⊔ Subgroup.zpowers c) : Subgroup G), x * y = y * x) :
    ∃ k : ℕ, y = (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ^ k := by
  classical
  let Q : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers c
  let S : Subgroup G := A ⊔ Q
  have hQd : Q ≤ dGrp b z := by
    refine sup_le le_sup_left ?_
    have hc_nor_bOne : c ∈ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) := by
      rw [show (bOne z : Subgroup G) =
          Subgroup.closure ({GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G) from
        CFSG.StandardType.GGFF.SettingCore.tor_eq_closure z]
      refine CFSG.StandardType.GGFF.mem_nor_of_closure
        (S := ({GGFF.zs z 0, GGFF.zs z 1, GGFF.zs z 2} : Set G)) ?_
      rintro s hs
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
      rcases hs with rfl | rfl | rfl
      · rw [hτc.cyc₀]; exact Subgroup.subset_closure (by simp)
      · rw [hτc.cyc₁]; exact Subgroup.subset_closure (by simp)
      · rw [hτc.cyc₂]; exact Subgroup.subset_closure (by simp)
    have hc_d : c ∈ L ⊓ Subgroup.normalizer ((bOne z : Subgroup G) : Set G) :=
      ⟨hτc.c_mem, hc_nor_bOne⟩
    exact (Subgroup.zpowers_le.mpr hc_d).trans le_sup_right
  have hQA : Q ≤ Subgroup.normalizer (A : Set G) :=
    fun g hg => CFSG.StandardType.GGFF.mem_nor_of_conj_mem (fun x hx => hA.nor g (hQd hg) x hx)
  have hy_mul : (y : G) ∈ (A : Set G) * (Q : Set G) := by
    have hle : (A : Set G) * (Q : Set G) = (↑S : Set G) := by
      rw [show S = A ⊔ Q from rfl]
      exact (Subgroup.coe_mul_of_right_le_normalizer_left A Q hQA).symm
    rw [hle]
    exact hyS
  obtain ⟨a, ha, q, hq, haq⟩ := hy_mul
  have hq_cen : q ∈ Subgroup.centralizer (B₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxB₂ : x ∈ B₂ := hx
    have hxS : x ∈ S := hA.B₂_le.trans le_sup_left hxB₂
    have hyx : y * x = x * y := (hyZ x hxS).symm
    have hax : a * x = x * a :=
      (Subgroup.mem_centralizer_iff.mp (hA.le_cen ha) x hx).symm
    have hqx : q * x = x * q := by
      have hqeq : q = a⁻¹ * y := by rw [← haq]; group
      rw [hqeq]
      calc (a⁻¹ * y) * x = a⁻¹ * (y * x) := by group
        _ = a⁻¹ * (x * y) := by rw [hyx]
        _ = (a⁻¹ * x) * y := by group
        _ = x * (a⁻¹ * y) := by
          rw [show a⁻¹ * x = x * a⁻¹ from ((commute_iff_eq a x).mpr hax).inv_left.eq]
          group
    exact hqx.symm
  have hq_one : q = 1 := by
    by_contra hq1
    have hle : B₂ ≤ B₂ ⊓ Subgroup.centralizer ({q} : Set G) := by
      intro x hx
      refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_iff.mp hq_cen x hx)
    have hcardle : Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({q} : Set G)) ≤ 3 ^ 3 :=
      card_centralizer_le h hB₂ hτc hq hq1
    have hcardeq : Nat.card B₂ ≤ Nat.card ↥(B₂ ⊓ Subgroup.centralizer ({q} : Set G)) :=
      Subgroup.card_le_of_le hle
    rw [hB₂.card] at hcardeq
    have : (3 : ℕ) ^ 6 ≤ 3 ^ 3 := hcardeq.trans hcardle
    norm_num at this
  have hya : y = a := by
    rw [show y = a * q from haq.symm, hq_one, mul_one]
  have hyaA : y ∈ A := hya ▸ ha
  have hby : b * y = y * b := hyZ b (Subgroup.mem_sup_right (Subgroup.mem_sup_left
    (Subgroup.mem_zpowers b)))
  have hzy : ∀ i : Fin 3, GGFF.zs z i * y = y * GGFF.zs z i := by
    intro i
    exact hyZ (GGFF.zs z i)
      (Subgroup.mem_sup_left (hA.B₂_le (hB₂.B₁_le (Subgroup.subset_closure ⟨i, rfl⟩))))
  have hy_cen_Bt : y ∈ cB b z := by
    rw [cB, Subgroup.mem_centralizer_iff]
    intro x hx
    have hb_cen : Subgroup.zpowers b ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_singleton_iff]
      exact hby
    have ht_cen : GGFF.tor (GGFF.zs z) ≤ Subgroup.centralizer ({y} : Set G) := by
      change Subgroup.closure (Set.range (GGFF.zs z)) ≤ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      change GGFF.zs z i ∈ Subgroup.centralizer ({y} : Set G)
      exact Subgroup.mem_centralizer_singleton_iff.mpr (hzy i)
    have hBt : GGFF.Bt b z ≤ Subgroup.centralizer ({y} : Set G) := by
      rw [GGFF.Bt]
      exact sup_le hb_cen ht_cen
    exact Subgroup.mem_centralizer_singleton_iff.mp (hBt hx)
  have hyP : IsPGroup 3 (Subgroup.zpowers y) :=
    hS.isP.to_le (Subgroup.zpowers_le.mpr hyS)
  have hyBt : y ∈ GGFF.Bt b z := mem_Bt_of_isPGroup_cen h y hy_cen_Bt hyP
  obtain ⟨j, v, hyv⟩ := (GGFF.SettingCore.mem_Bt h.settingCore).mp hyBt
  have hvB2 : vecElt (GGFF.zs z) v ∈ B₂ :=
    hB₂.B₁_le (GGFF.vecElt_mem_tor (GGFF.zs z) v)
  have hy_cen_B2 : y ∈ Subgroup.centralizer (B₂ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hyZ x (Subgroup.mem_sup_left (hA.B₂_le hx))
  have hbj_cen : b ^ j ∈ Subgroup.centralizer (B₂ : Set G) := by
    have hbj_eq : b ^ j = y * (vecElt (GGFF.zs z) v)⁻¹ := by rw [hyv]; group
    rw [Subgroup.mem_centralizer_iff] at hy_cen_B2 ⊢
    intro x hx
    have hyx := hy_cen_B2 x hx
    have hvx : vecElt (GGFF.zs z) v * x = x * vecElt (GGFF.zs z) v :=
      congrArg Subtype.val (hB₂.abel.1.is_comm.comm
        ⟨vecElt (GGFF.zs z) v, hvB2⟩ ⟨x, hx⟩)
    have hvx' : (vecElt (GGFF.zs z) v)⁻¹ * x = x * (vecElt (GGFF.zs z) v)⁻¹ := by
      calc (vecElt (GGFF.zs z) v)⁻¹ * x
          = (vecElt (GGFF.zs z) v)⁻¹ * (x * vecElt (GGFF.zs z) v) *
              (vecElt (GGFF.zs z) v)⁻¹ := by group
        _ = (vecElt (GGFF.zs z) v)⁻¹ * (vecElt (GGFF.zs z) v * x) *
              (vecElt (GGFF.zs z) v)⁻¹ := by rw [← hvx]
        _ = x * (vecElt (GGFF.zs z) v)⁻¹ := by group
    rw [hbj_eq]
    exact (calc (y * (vecElt (GGFF.zs z) v)⁻¹) * x
        = y * ((vecElt (GGFF.zs z) v)⁻¹ * x) := by group
      _ = y * (x * (vecElt (GGFF.zs z) v)⁻¹) := by rw [hvx']
      _ = (y * x) * (vecElt (GGFF.zs z) v)⁻¹ := by group
      _ = (x * y) * (vecElt (GGFF.zs z) v)⁻¹ := by rw [hyx]
      _ = x * (y * (vecElt (GGFF.zs z) v)⁻¹) := by group).symm
  have hbj_one : b ^ j = 1 := by
    by_contra hbj
    have hb_zpow : b ∈ Subgroup.zpowers (b ^ j) := by
      rcases GGFF.eq_or_eq_inv_of_mem_zpowers h.settingCore.ord
        (Subgroup.zpow_mem_zpowers b j) hbj with he | he
      · rw [he]; exact Subgroup.mem_zpowers b
      · rw [he]
        simp
    have hb_cen : b ∈ Subgroup.centralizer (B₂ : Set G) :=
      (Subgroup.zpowers_le.mpr hbj_cen) hb_zpow
    have hB2leB1 : B₂ ≤ bOne z := by
      intro x hx
      exact hB₂.fix x hx (Subgroup.mem_centralizer_iff.mp hb_cen x hx)
    have hcardle : Nat.card B₂ ≤ Nat.card (bOne z) := Subgroup.card_le_of_le hB2leB1
    rw [hB₂.card, h.settingCore.card_torG] at hcardle
    norm_num at hcardle
  have hyvec : y = vecElt (GGFF.zs z) v := by rw [hyv, hbj_one, one_mul]
  have hcS : c ∈ S := Subgroup.mem_sup_right (Subgroup.mem_sup_right (Subgroup.mem_zpowers c))
  have hcy : c * y * c⁻¹ = y := by
    have hcomm := hyZ c hcS
    calc c * y * c⁻¹ = y * c * c⁻¹ := by rw [hcomm]
      _ = y := by group
  have hcyc : vecElt (GGFF.zs z) v =
      vecElt (GGFF.zs z) (fun i => if i = 0 then v 2 else if i = 1 then v 0 else v 1) := by
    rw [hyvec] at hcy
    rw [← hcy]
    exact conj_vecElt_cycle h.settingCore.zs_comm hτc.cyc₀ hτc.cyc₁ hτc.cyc₂ v
  have hvw : v = (fun i => if i = 0 then v 2 else if i = 1 then v 0 else v 1) :=
    GGFF.vecElt_injective h.settingCore.zs_pow h.settingCore.zs_comm h.settingCore.inj' hcyc
  have hv0 : v 0 = v 2 := by
    have := congrFun hvw 0
    simpa using this
  have hv1 : v 1 = v 0 := by
    have := congrFun hvw 1
    simpa using this
  have hvconst : v = fun _ => v 0 := by
    funext i
    fin_cases i
    · rfl
    · exact hv1
    · exact hv0.symm
  refine ⟨(v 0).val, ?_⟩
  rw [hyvec, hvconst, vecElt_const h.settingCore.zs_comm]

theorem exists_conj_z0 {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    {z : Fin 3 → ↥L} (h : Counterexample G n b L z) {B₂ A : Subgroup G} {τ c : G}
    (hB₂ : B2Package b z B₂) (hA : AStar b z B₂ A) (hτc : TauC z τ c)
    (hS : SylowData b B₂ A c) (P : Sylow 3 G)
    (hP : (P : Subgroup G) ≤ Subgroup.centralizer ({GGFF.zs z 0} : Set G)) :
    ∃ m ∈ Subgroup.normalizer (B₂ : Set G), ∃ k : ℕ,
      m * (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ^ k * m⁻¹ = GGFF.zs z 0 := by
  classical
  let Q : Subgroup G := Subgroup.zpowers b ⊔ Subgroup.zpowers c
  let S : Subgroup G := A ⊔ Q
  have hS₀ : IsPGroup 3 S := hS.isP
  let S₀ : Sylow 3 G :=
    { toSubgroup := S
      isPGroup' := hS₀
      is_maximal' := fun {U} hU hSU => hS.max U hU hSU }
  obtain ⟨s, hs⟩ := MulAction.exists_smul_eq G S₀ P
  have hb1 : GGFF.zs z 0 ≠ 1 := by
    intro h1
    exact h.model.z_ne_one 0 (Subtype.ext (by simpa [GGFF.zs] using h1))
  have hb1_cenP : GGFF.zs z 0 ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact (Subgroup.mem_centralizer_iff.mp (hP hx) (GGFF.zs z 0) (Set.mem_singleton _)).symm
  have hPn : (P : Subgroup G) ≤ Subgroup.normalizer (Subgroup.zpowers (GGFF.zs z 0) : Set G) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : Commute x (GGFF.zs z 0) :=
        (commute_iff_eq x (GGFF.zs z 0)).mpr
          (Subgroup.mem_centralizer_iff.mp (hP hx) (GGFF.zs z 0) (Set.mem_singleton _)).symm
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      exact (show x * GGFF.zs z 0 ^ m * x⁻¹ = GGFF.zs z 0 ^ m from by
        rw [(hcomm.zpow_right m).eq, mul_assoc, mul_inv_cancel, mul_one]).symm
    · intro hy
      obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hcomm : Commute x (GGFF.zs z 0) :=
        (commute_iff_eq x (GGFF.zs z 0)).mpr
          (Subgroup.mem_centralizer_iff.mp (hP hx) (GGFF.zs z 0) (Set.mem_singleton _)).symm
      have hyeq : y = x⁻¹ * GGFF.zs z 0 ^ m * x := by rw [hm]; group
      rw [hyeq]
      refine Subgroup.mem_zpowers_iff.mpr ⟨m, ?_⟩
      exact (show x⁻¹ * GGFF.zs z 0 ^ m * x = GGFF.zs z 0 ^ m from by
        calc x⁻¹ * GGFF.zs z 0 ^ m * x
            = x⁻¹ * (GGFF.zs z 0 ^ m * x) := by group
          _ = x⁻¹ * (x * GGFF.zs z 0 ^ m) := by rw [← (hcomm.zpow_right m).eq]
          _ = GGFF.zs z 0 ^ m := by group).symm
  have hsup_isP : IsPGroup 3 ((P : Subgroup G) ⊔ Subgroup.zpowers (GGFF.zs z 0) : Subgroup G) :=
    IsPGroup.to_sup_of_normal_right' P.isPGroup'
      (CFSG.Open.isElemAbelian_zpowers (p := 3) (x := GGFF.zs z 0)
        (h.settingCore.zs_pow 0)).isPGroup hPn
  have hsup_eq : ((P : Subgroup G) ⊔ Subgroup.zpowers (GGFF.zs z 0) : Subgroup G) = P :=
    P.is_maximal' hsup_isP le_sup_left
  have hb1P : GGFF.zs z 0 ∈ (P : Subgroup G) := by
    have hmem : GGFF.zs z 0 ∈
        ((P : Subgroup G) ⊔ Subgroup.zpowers (GGFF.zs z 0) : Subgroup G) :=
      Subgroup.mem_sup_right (S := (P : Subgroup G)) (Subgroup.mem_zpowers (GGFF.zs z 0))
    rwa [hsup_eq] at hmem
  have hsSub : (P : Subgroup G) = (S₀ : Subgroup G).map (MulAut.conj s : G →* G) := by
    rw [← hs, Sylow.coe_subgroup_smul]
    rfl
  obtain ⟨y, hyS, hyconj⟩ := Subgroup.mem_map.mp (hsSub ▸ hb1P)
  have hyZ : ∀ x ∈ S, x * y = y * x := by
    intro x hx
    have hxP : s * x * s⁻¹ ∈ (P : Subgroup G) := by
      have hxS₀ : x ∈ (S₀ : Subgroup G) := hx
      rw [hsSub]
      change (MulAut.conj s) x ∈ (S₀ : Subgroup G).map (MulAut.conj s : G →* G)
      exact Subgroup.mem_map_of_mem (MulAut.conj s : G →* G) hxS₀
    have hcomm := (Subgroup.mem_centralizer_singleton_iff.mp (hP hxP)).symm
    have hy_eq : y = s⁻¹ * GGFF.zs z 0 * s := by
      change (MulAut.conj s) y = GGFF.zs z 0 at hyconj
      rw [MulAut.conj_apply] at hyconj
      rw [← hyconj]
      group
    simpa [hy_eq] using (commute_conj_of_commute hcomm).symm
  obtain ⟨k, hye⟩ := exists_pow_of_mem_center h hB₂ hA hτc hS hyS hyZ
  have heB2 : (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ∈ B₂ := by
    refine hB₂.B₁_le ?_
    exact (GGFF.tor (GGFF.zs z)).mul_mem
      ((GGFF.tor (GGFF.zs z)).mul_mem (Subgroup.subset_closure ⟨0, rfl⟩)
        (Subgroup.subset_closure ⟨1, rfl⟩)) (Subgroup.subset_closure ⟨2, rfl⟩)
  have hb1B2 : GGFF.zs z 0 ∈ B₂ :=
    hB₂.B₁_le (Subgroup.subset_closure ⟨0, rfl⟩)
  have ha : ∀ x ∈ B₂, x * (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ^ k =
      (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ^ k * x := by
    intro x hx
    have hxe : Commute x (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) :=
      congrArg Subtype.val (hB₂.abel.1.is_comm.comm ⟨x, hx⟩
        ⟨GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2, heB2⟩)
    exact (hxe.pow_right k).eq
  have hsa : s * (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ^ k * s⁻¹ = GGFF.zs z 0 := by
    rw [← hye]
    exact hyconj
  have hg : ∀ x ∈ B₂, x * (s * (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ^ k * s⁻¹) =
      (s * (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ^ k * s⁻¹) * x := by
    intro x hx
    rw [hsa]
    exact congrArg Subtype.val (hB₂.abel.1.is_comm.comm ⟨x, hx⟩ ⟨GGFF.zs z 0, hb1B2⟩)
  have hB2leS : B₂ ≤ (S₀ : Subgroup G) := hA.B₂_le.trans le_sup_left
  have hwc : ∀ g : G, (∀ x ∈ B₂, g * x * g⁻¹ ∈ (S₀ : Subgroup G)) →
      ∀ x ∈ B₂, g * x * g⁻¹ ∈ B₂ := fun g hg => hS.wc g hg
  obtain ⟨m, hmN, hmconj⟩ :=
    CFSG.WeakClosureFusion.exists_mem_normalizer_conj_eq (p := 3) (P := S₀) (W := B₂)
      hB2leS hwc (a := (GGFF.zs z 0 * GGFF.zs z 1 * GGFF.zs z 2) ^ k) ha (g := s) hg
  exact ⟨m, hmN, k, by rw [hmconj, hsa]⟩

end CFSG.StandardType.FF81.PropOne

end
