module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5zs
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zr

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.S127.L715.Set714.N3

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.ASInputs S127 S127.L715 S127.L716
  G31 CFSG.LargeExtraspecial Module QuadraticMap
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G}
  {s : Set714 G T L V t z} {h1222 : Stmt12_2_2} (hn : s.N3 h1222)
include hn

theorem rhoQ_T_v {v : G}
    (hv : v ∈ V1 T L V) (hvz : v ∉ Subgroup.zpowers z) {t₀ : G} (ht : t₀ ∈ T) :
    hn.rhoQ ⟨t₀, s.le_cent ht⟩ (hn.setting.cl v) = hn.setting.cl v := by
  have hvQ : v ∈ s.Qz h1222 := s.U_le_Qz hn (le_conjClosure _ _ hv)
  rw [hn.rhoQ_cl _ hvQ]
  have htv : t₀ * v * t₀⁻¹ ∈ V1 T L V :=
    (Subgroup.mem_normalizer_iff.mp (s.T_le_normalizer_V1 h1222 ht) v).mp hv
  rcases hn.cl_V1 hv hvz htv with h | h
  · exfalso
    have htvQ : t₀ * v * t₀⁻¹ ∈ s.Qz h1222 := s.U_le_Qz hn (le_conjClosure _ _ htv)
    rw [hn.setting.cl_eq_zero_iff (hn.mem_QG htvQ)] at h
    apply hvz
    have hzt : t₀ * z = z * t₀ := Subgroup.mem_centralizer_singleton_iff.mp (s.le_cent ht)
    rcases h with h | h
    · have : v = 1 := by
        have := congrArg (fun g => t₀⁻¹ * g * t₀) h
        simpa [mul_assoc] using this
      rw [this]
      exact Subgroup.one_mem _
    · have : v = z := by
        have e : v = t₀⁻¹ * (t₀ * v * t₀⁻¹) * t₀ := by group
        rw [e]
        show t₀⁻¹ * (t₀ * v * t₀⁻¹) * t₀ = z
        rw [h]
        calc t₀⁻¹ * z * t₀ = t₀⁻¹ * (z * t₀) := by group
          _ = t₀⁻¹ * (t₀ * z) := by rw [hzt]
          _ = z := by group
      rw [this]
      exact Subgroup.mem_zpowers z
  · exact h

theorem exists_compl_T {y : G}
    (hyL1 : y ∈ L1 T L V) (hy3 : orderOf y = 3)
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {v : G} (hv : v ∈ V1 T L V)
    (hvz : v ∉ Subgroup.zpowers z) :
    ∃ E : Submodule (ZMod 2) hn.setting.Qt, IsCompl (hn.setting.clSub (U714 T L V z)) E ∧
      ∀ (t₀ : G) (ht : t₀ ∈ T), ∀ e ∈ E, hn.rhoQ ⟨t₀, s.le_cent ht⟩ e ∈ E := by
  have hw := hn.setting_width
  have hvQ : v ∈ s.Qz h1222 := s.U_le_Qz hn (le_conjClosure _ _ hv)
  have hvA : hn.setting.cl v ∈ hn.setting.clSub (V ⊓ s.Qz h1222) :=
    hn.setting.cl_mem_clSub ⟨(inf_le_left : V1 T L V ≤ V) hv, hvQ⟩ (hn.mem_QG hvQ)
  have hvW : hn.setting.cl v ∈ hn.setting.clSub (U714 T L V z) :=
    hn.setting.cl_mem_clSub (le_conjClosure _ _ hv) (hn.mem_QG hvQ)
  have hpolA : ∀ a ∈ hn.setting.clSub (V ⊓ s.Qz h1222),
      ∀ b ∈ hn.setting.clSub (V ⊓ s.Qz h1222), polar hn.setting.q a b = 0 := by
    intro a ha b hb
    rw [polar, hn.q_A0 _ (Submodule.add_mem _ ha hb), hn.q_A0 a ha, hn.q_A0 b hb]
    simp
  have hpolW : ∀ a ∈ hn.setting.clSub (U714 T L V z),
      ∀ b ∈ hn.setting.clSub (U714 T L V z), polar hn.setting.q a b = 0 := by
    intro a ha b hb
    rw [polar, hn.q_W1 _ (Submodule.add_mem _ ha hb), hn.q_W1 a ha, hn.q_W1 b hb]
    simp
  obtain ⟨e, he, heq, hev, huniq⟩ := exists_singular_compl hn.setting hw hn.q_A0 hn.finrank_A0
    (hn.Yt_le_A0 hyL1) (hn.finrank_Yt hyL1 hy3 hv hvz) hvA
    (hn.cl_v_not_mem_Yt hyL1 hy3 hv hvz)
  have hYv : ∀ y' ∈ hn.Yt hyL1, polar hn.setting.q y' (hn.setting.cl v) = 0 := fun y' hy' =>
    hpolA y' (hn.Yt_le_A0 hyL1 hy') _ hvA
  set E := hn.Yt hyL1 ⊔ Submodule.span (ZMod 2) {e} with hE
  have hdisj : Disjoint (hn.setting.clSub (U714 T L V z)) E := by
    rw [Submodule.disjoint_def]
    intro w hwU hwE
    obtain ⟨y', hy', w', hw', rfl⟩ := Submodule.mem_sup.mp hwE
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw'
    have hpv : polar hn.setting.q (y' + c • e) (hn.setting.cl v) = c := by
      rw [polar_add_left, polar_smul_left, hev, hYv y' hy', zero_add, smul_eq_mul, mul_one]
    have hpv0 : polar hn.setting.q (y' + c • e) (hn.setting.cl v) = 0 := hpolW _ hwU _ hvW
    rw [hpv] at hpv0
    rw [hpv0, zero_smul, add_zero] at hwU ⊢
    exact Submodule.disjoint_def.mp (hn.disjoint_Yt_W1 hyL1 hy3 hv hvz) y' hy' hwU
  have heY : e ∉ hn.Yt hyL1 := fun h => by
    have := hYv e h
    rw [hev] at this
    exact one_ne_zero this
  have hfin : finrank (ZMod 2) E = 3 := by
    have hYe : Disjoint (hn.Yt hyL1) (Submodule.span (ZMod 2) {e}) := by
      rw [Submodule.disjoint_span_singleton]
      exact fun h => absurd h heY
    have he0 : e ≠ 0 := fun h => heY (h ▸ Submodule.zero_mem _)
    have h := Submodule.finrank_sup_add_finrank_inf_eq (hn.Yt hyL1) (Submodule.span (ZMod 2) {e})
    rw [hYe.eq_bot, finrank_bot, add_zero, finrank_span_singleton he0,
      hn.finrank_Yt hyL1 hy3 hv hvz] at h
    rw [hE, h]
  have hdim : finrank (ZMod 2) hn.setting.Qt = 6 := by
    rw [hn.setting.finrank_Qt_eq_two_mul_width, hw]
  have hc : IsCompl (hn.setting.clSub (U714 T L V z)) E :=
    (Submodule.isCompl_iff_disjoint _ _ (by rw [hn.finrank_W1, hfin, hdim])).mpr hdisj
  refine ⟨E, hc, fun t₀ ht x hx => ?_⟩
  set ρt := hn.rhoQ ⟨t₀, s.le_cent ht⟩ with hρt
  obtain ⟨y', hy', w', hw', rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw'
  rw [map_add, map_smul]
  refine Submodule.add_mem _
    (Submodule.mem_sup_left (hn.rhoQ_T_Yt hyL1 hy3 hU hv hvz ht hy')) (Submodule.smul_mem _ _ ?_)
  have hinv : ∀ w, ρt (hn.rhoQ ⟨t₀⁻¹, s.le_cent (T.inv_mem ht)⟩ w) = w := by
    intro w
    rw [hρt, ← hn.rhoQ_mul]
    have e1 : (⟨t₀, s.le_cent ht⟩ * ⟨t₀⁻¹, s.le_cent (T.inv_mem ht)⟩ : hn.setting.M) = 1 :=
      Subtype.ext (mul_inv_cancel t₀)
    rw [e1, hn.rhoQ_one]
  have hρe : ρt e ∈ LinearMap.BilinForm.orthogonal hn.setting.q.polarBilin (hn.Yt hyL1) := by
    refine DW.mem_perp.mpr fun y'' hy'' => ?_
    have hy₀ := hn.rhoQ_T_Yt hyL1 hy3 hU hv hvz (T.inv_mem ht) hy''
    rw [← hinv y'', hρt]
    rw [DW.polar_ρ_apply]
    exact DW.mem_perp.mp he _ hy₀
  have hρq : hn.setting.q (ρt e) = 0 := by rw [hρt, DW.q_ρ_apply, heq]
  have hρv : polar hn.setting.q (ρt e) (hn.setting.cl v) = 1 := by
    rw [← hn.rhoQ_T_v hv hvz ht, hρt, DW.polar_ρ_apply, hev]
  have hd := huniq _ hρe hρq hρv
  have e2 : ρt e = (ρt e - e) + e := by abel
  rw [e2]
  exact Submodule.add_mem _ (Submodule.mem_sup_left hd)
    (Submodule.mem_sup_right (Submodule.mem_span_singleton_self e))

theorem exists_W2
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) :
    ∃ W₂ : Submodule (ZMod 2) hn.setting.Qt, IsCompl (hn.setting.clSub (U714 T L V z)) W₂ ∧
      ∀ m : hn.setting.M, ∀ w ∈ W₂, hn.rhoQ m w ∈ W₂ := by
  obtain ⟨v, hv, hvz⟩ := s.exists_v h1222
  obtain ⟨y, hyL1, hy3⟩ := S127.Mod.idx3_exists (s.relIndex_L1 h1222)
  obtain ⟨E, hcE, hET⟩ := hn.exists_compl_T hyL1 hy3 hU hv hvz
  have hy := s.setting.hyp.hyp
  have hT : ¬ 2 ∣ (T.subgroupOf hn.setting.M).index := fun h =>
    hy.sylow.2 (h.trans (Subgroup.relIndex_dvd_index_of_le s.le_cent))
  exact exists_invariant_compl hn.setting (T.subgroupOf hn.setting.M) hT hcE hn.rhoQ_W1
    fun t ht e he => hET t ht e he

theorem mem_V1_of_comm
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {u : G} (hu : u ∈ U714 T L V z)
    (hc : ∀ x ∈ V, x * u * x⁻¹ * u⁻¹ ∈ Subgroup.zpowers z) : u ∈ V1 T L V := by
  have h := s.setting.hyp
  have := s.isMulCommutative_V h1222
  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    S127.Mod.T_le_normalizer h1222 h ((s.U_le_T h1222).1 hu)
  have ha : conjAct V ⟨u, huN⟩ ∈ autOn (R1 T L V) V := hU ▸ S127.Mod.conjAct_mem_autOn hu huN
  obtain ⟨r, hrN, hrR, hre⟩ := S127.Mod.mem_autOn'.1 ha
  have hur : ∀ x ∈ V, u * x * u⁻¹ = r * x * r⁻¹ := by
    intro x hx
    have := congrArg (fun f : MulAut ↥V => ((f ⟨x, hx⟩ : ↥V) : G)) hre
    simp only [S127.Mod.conjAct_val] at this
    exact this.symm
  obtain ⟨-, -, -, hsq, hR, -⟩ := S127.Mod.lemma12_7_2_two h1222 h
  by_cases hrC : r ∈ Subgroup.centralizer (V : Set G)
  ·
    have huC : u ∈ U714 T L V z ⊓ Subgroup.centralizer (V : Set G) := by
      refine ⟨hu, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
      have h1 := hur x hx
      rw [(Subgroup.mem_centralizer_iff.mp hrC x hx).symm, mul_inv_cancel_right] at h1
      calc x * u = u * x * u⁻¹ * u := by rw [h1]
        _ = u * x := by group
    have hV1le : V1 T L V ≤ U714 T L V z ⊓ Subgroup.centralizer (V : Set G) := fun x hx =>
      ⟨le_conjClosure _ _ hx, Subgroup.mem_centralizer_iff.mpr fun y hy =>
        s.comm_V h1222 hy ((inf_le_left : V1 T L V ≤ V) hx)⟩
    have hcard := s.card_U_inf_C h1222 hU
    rw [hn.card_U] at hcard
    have heq : V1 T L V = U714 T L V z ⊓ Subgroup.centralizer (V : Set G) :=
      Subgroup.eq_of_le_of_card_ge hV1le (by rw [s.card_V1 h1222]; omega)
    rw [heq]
    exact huC
  · exfalso
    have hV1 := hR r hrR hrC
    have hle : ⁅V, Subgroup.zpowers r⁆ ≤ Subgroup.zpowers z := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
      rw [commutatorElement_def]
      rcases Int.even_or_odd' k with ⟨m, rfl | rfl⟩
      · have hk : r ^ (2 * m) ∈ Subgroup.centralizer (V : Set G) := by
          rw [zpow_mul]
          exact Subgroup.zpow_mem _ (by exact_mod_cast hsq r hrR) m
        rw [(Subgroup.mem_centralizer_iff.mp hk a ha), mul_inv_cancel_right, mul_inv_cancel]
        exact Subgroup.one_mem _
      · have hk : r ^ (2 * m) ∈ Subgroup.centralizer (V : Set G) := by
          rw [zpow_mul]
          exact Subgroup.zpow_mem _ (by exact_mod_cast hsq r hrR) m
        have hmem : r * a⁻¹ * r⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hrN a⁻¹).mp (V.inv_mem ha)
        have e : a * r ^ (2 * m + 1) * a⁻¹ * (r ^ (2 * m + 1))⁻¹ = a * (r * a⁻¹ * r⁻¹) := by
          rw [zpow_add_one]
          calc a * (r ^ (2 * m) * r) * a⁻¹ * (r ^ (2 * m) * r)⁻¹
              = a * r ^ (2 * m) * (r * a⁻¹ * r⁻¹) * (r ^ (2 * m))⁻¹ := by group
            _ = a * (r ^ (2 * m) * (r * a⁻¹ * r⁻¹)) * (r ^ (2 * m))⁻¹ := by group
            _ = a * ((r * a⁻¹ * r⁻¹) * r ^ (2 * m)) * (r ^ (2 * m))⁻¹ := by
                rw [(Subgroup.mem_centralizer_iff.mp hk _ hmem).symm]
            _ = a * (r * a⁻¹ * r⁻¹) := by group
        rw [e, ← hur a⁻¹ (V.inv_mem ha)]
        have e2 : a * (u * a⁻¹ * u⁻¹) = a * u * a⁻¹ * u⁻¹ := by group
        rw [e2]
        exact hc a ha
    rw [hV1] at hle
    have h1 := Subgroup.card_le_of_le hle
    rw [s.card_V1 h1222, Nat.card_zpowers, s.orderOf_z] at h1
    omega

theorem fix_V_W1
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {v : G} (hv : v ∈ V1 T L V)
    (hvz : v ∉ Subgroup.zpowers z) {w : hn.setting.Qt}
    (hw : w ∈ hn.setting.clSub (U714 T L V z))
    (hfix : ∀ (x : G) (hx : x ∈ V), hn.rhoQ ⟨x, s.V_le_Gz h1222 hx⟩ w = w) :
    w = 0 ∨ w = hn.setting.cl v := by
  obtain ⟨u, hu, huQ, rfl⟩ := hn.setting.mem_clSub_iff.mp hw
  have huQz : u ∈ s.Qz h1222 := s.U_le_Qz hn hu
  refine hn.cl_V1 hv hvz (hn.mem_V1_of_comm hU hu fun x hx => ?_)
  have h := hfix x hx
  rw [hn.rhoQ_cl _ huQz] at h
  have hxu : x * u * x⁻¹ ∈ s.Qz h1222 :=
    (Subgroup.mem_normalizer_iff.mp (hn.Gz_le_normalizer_Qz (s.V_le_Gz h1222 hx)) u).mp huQz
  exact hn.mul_inv_mem_of_cl_eq hxu huQz h

theorem rhoQ_V_A0 {x : G}
    (hx : x ∈ V) {a : hn.setting.Qt} (ha : a ∈ hn.setting.clSub (V ⊓ s.Qz h1222)) :
    hn.rhoQ ⟨x, s.V_le_Gz h1222 hx⟩ a = a := by
  obtain ⟨y, hy, hyQ, rfl⟩ := hn.setting.mem_clSub_iff.mp ha
  rw [hn.rhoQ_cl _ hy.2]
  show hn.setting.cl (x * y * x⁻¹) = hn.setting.cl y
  rw [s.comm_V h1222 hx hy.1, mul_inv_cancel_right]

theorem clSub_C0_le {x : G}
    (hx : x ∈ V ⊓ s.Qz h1222 ⊔ U714 T L V z) :
    hn.setting.cl x ∈ hn.setting.clSub (V ⊓ s.Qz h1222) ⊔ hn.setting.clSub (U714 T L V z) := by
  have hN : V ⊓ s.Qz h1222 ≤ Subgroup.normalizer (U714 T L V z : Set G) :=
    fun x hx => s.H_le_normalizer_U h1222 (V_le_H714 T L V z hx.1)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hx
  obtain ⟨a, ha, b, hb, rfl⟩ := hx
  have haQ : a ∈ s.Qz h1222 := ha.2
  have hbQ : b ∈ s.Qz h1222 := s.U_le_Qz hn hb
  rw [hn.setting.cl_mul (hn.mem_QG haQ) (hn.mem_QG hbQ)]
  exact Submodule.add_mem_sup (hn.setting.cl_mem_clSub ha (hn.mem_QG haQ))
    (hn.setting.cl_mem_clSub hb (hn.mem_QG hbQ))

theorem q_W2
    (hU : autOn (U714 T L V z) V = autOn (R1 T L V) V) {W₂ : Submodule (ZMod 2) hn.setting.Qt}
    (hc : IsCompl (hn.setting.clSub (U714 T L V z)) W₂)
    (hinv : ∀ m : hn.setting.M, ∀ w ∈ W₂, hn.rhoQ m w ∈ W₂) :
    ∀ w ∈ W₂, hn.setting.q w = 0 := by
  obtain ⟨v, hv, hvz⟩ := s.exists_v h1222
  have hvQ : v ∈ s.Qz h1222 := s.U_le_Qz hn (le_conjClosure _ _ hv)
  have hvA : hn.setting.cl v ∈ hn.setting.clSub (V ⊓ s.Qz h1222) :=
    hn.setting.cl_mem_clSub ⟨(inf_le_left : V1 T L V ≤ V) hv, hvQ⟩ (hn.mem_QG hvQ)
  have hkey : ∀ w ∈ W₂, w ∈ hn.setting.clSub (V ⊓ s.Qz h1222) ⊔
      hn.setting.clSub (U714 T L V z) → w ∈ hn.setting.clSub (V ⊓ s.Qz h1222) := by
    intro w hw hwAU
    obtain ⟨b, hb, u, hu, rfl⟩ := Submodule.mem_sup.mp hwAU
    have hfix : ∀ (x : G) (hx : x ∈ V), hn.rhoQ ⟨x, s.V_le_Gz h1222 hx⟩ u = u := by
      intro x hx
      have h1 : hn.rhoQ ⟨x, s.V_le_Gz h1222 hx⟩ (b + u) - (b + u) ∈ W₂ :=
        Submodule.sub_mem _ (hinv _ _ hw) hw
      have h2 : hn.rhoQ ⟨x, s.V_le_Gz h1222 hx⟩ (b + u) - (b + u) =
          hn.rhoQ ⟨x, s.V_le_Gz h1222 hx⟩ u - u := by
        rw [map_add, hn.rhoQ_V_A0 hx hb]
        abel
      have h3 : hn.rhoQ ⟨x, s.V_le_Gz h1222 hx⟩ u - u ∈ hn.setting.clSub (U714 T L V z) :=
        Submodule.sub_mem _ (hn.rhoQ_W1 _ u hu) hu
      rw [h2] at h1
      have h4 := Submodule.disjoint_def.mp hc.1 _ h3 h1
      exact sub_eq_zero.mp h4
    rcases hn.fix_V_W1 hU hv hvz hu hfix with h | h
    · rw [h, add_zero]
      exact hb
    · rw [h]
      exact Submodule.add_mem _ hb hvA
  intro w hw
  obtain ⟨a, haQ, rfl⟩ := hn.setting.exists_cl w
  have haQz : a ∈ s.Qz h1222 := by rw [← hn.setting_QG]; exact haQ
  obtain ⟨h, hh, ha', -⟩ := hn.exists_conj_mem_C0 haQz haQz
  have hhz := s.H_le_Gz h1222 hh
  have hmem : hn.rhoQ ⟨h, hhz⟩ (hn.setting.cl a) ∈ W₂ := hinv _ _ hw
  rw [hn.rhoQ_cl _ haQz] at hmem
  have hA := hkey _ hmem (hn.clSub_C0_le ha')
  rw [← DW.q_ρ_apply ⟨h, hhz⟩, show ((hn.setting.ρ ⟨h, hhz⟩ : hn.setting.O) :
      hn.setting.Qt ≃ₗ[ZMod 2] hn.setting.Qt) (hn.setting.cl a) = hn.rhoQ ⟨h, hhz⟩
        (hn.setting.cl a) from rfl, hn.rhoQ_cl _ haQz]
  exact hn.q_A0 _ hA

end CFSG.Quasithin.H13.S127.L715.Set714.N3
