module

public import CFSG.Quasithin.EmptyFaithful.R3c17A
public import CFSG.Quasithin.EmptyFaithful.R3c16Act

public section

namespace CFSG.Quasithin.R3c17

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15 CFSG.Quasithin.R3c16
open scoped commutatorElement

section Swap

variable {G : Type} [Group G] [Finite G]

theorem exists_y_centralizing_V₂ {T Mc M V₁ V₂ : Subgroup G} {t : G} (h113 : StageLemma14113)
    (hh : Hyp153 G T Mc M) (D : Decomp153 T M V₁ V₂ t) :
    ∃ y ∈ Y153 Mc M, (∀ v ∈ V₂, y * v = v * y) ∧ ¬ ∀ v ∈ V₁, y * v = v * y := by
  classical
  obtain ⟨e⟩ := D.iso₁
  have hc3 : orderOf (finRotate 3) = 3 := by
    have h1 : (finRotate 3) ^ 3 = 1 := by decide
    have h2 : finRotate 3 ≠ 1 := by decide
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime h1 h2
  set a : ↥(autOn (M ⊓ Subgroup.centralizer (V₂ : Set G)) (VZ T M)) := e.symm (finRotate 3) with ha
  have ha3 : orderOf (a : MulAut ↥(VZ T M)) = 3 := by
    rw [Subgroup.orderOf_coe, ha, MulEquiv.orderOf_eq, hc3]
  have hmem : (a : MulAut ↥(VZ T M)) ∈
      oTwoUpper (autOn (M ⊓ Subgroup.centralizer (V₂ : Set G)) (VZ T M)) :=
    Subgroup.subset_closure ⟨a.2, by rw [ha3]; decide⟩
  have hAY : (a : MulAut ↥(VZ T M)) ∈ autOn (Y153 Mc M) (VZ T M) := by
    rw [hh.autOn_Y153 h113]
    exact oTwoUpper_mono (A4.autOn_mono inf_le_left) hmem
  obtain ⟨y', hy', hy'a⟩ := hAY
  obtain ⟨m', hm', hm'a⟩ := a.2
  have hconj : ∀ (g : Subgroup.normalizer (VZ T M : Set G)) (v : ↥(VZ T M)),
      ((conjAct (VZ T M) g v : ↥(VZ T M)) : G) = (g : G) * (v : G) * (g : G)⁻¹ := fun g v =>
    Subgroup.normalizerMonoidHom_apply_apply_coe (VZ T M) g v
  have hy₁ : (y' : G) ∈ Y153 Mc M := Subgroup.mem_subgroupOf.mp hy'
  have hact : ∀ v ∈ V₂, (y' : G) * v * (y' : G)⁻¹ = v := by
    intro v hv
    have hv' : v ∈ VZ T M := D.le₂ hv
    have h1 := hconj y' ⟨v, hv'⟩
    rw [hy'a, ← hm'a] at h1
    have h2 := hconj m' ⟨v, hv'⟩
    have hmc : (m' : G) ∈ Subgroup.centralizer (V₂ : Set G) :=
      (Subgroup.mem_subgroupOf.mp hm').2
    have h3 : (m' : G) * v * (m' : G)⁻¹ = v := by
      have := Subgroup.mem_centralizer_iff.1 hmc v hv
      rw [← this]
      group
    rw [h3] at h2
    have h4 : ((conjAct (VZ T M) m' ⟨v, hv'⟩ : ↥(VZ T M)) : G) = v := by rw [h2]
    exact h1.symm.trans h4
  refine ⟨y', hy₁, fun v hv => ?_, fun hV₁ => ?_⟩
  · calc (y' : G) * v = ((y' : G) * v * (y' : G)⁻¹) * y' := by group
      _ = v * y' := by rw [hact v hv]
  ·
    have hV' : V₁ ⊔ V₂ ≤ Subgroup.centralizer {(y' : G)} := by
      refine sup_le (fun v hv => ?_) (fun v hv => ?_)
      · exact Subgroup.mem_centralizer_singleton_iff.2 (hV₁ v hv).symm
      · refine Subgroup.mem_centralizer_singleton_iff.2 ?_
        have : (y' : G) * v = v * y' := by
          calc (y' : G) * v = ((y' : G) * v * (y' : G)⁻¹) * y' := by group
            _ = v * y' := by rw [hact v hv]
        exact this.symm
    have hV : VZ T M ≤ Subgroup.centralizer {(y' : G)} := D.sup.ge.trans hV'
    have h1 : (a : MulAut ↥(VZ T M)) = 1 := by
      rw [← hy'a]
      refine MulEquiv.ext fun x => Subtype.ext ?_
      rw [hconj y' x, MulAut.one_apply]
      have := Subgroup.mem_centralizer_singleton_iff.1 (hV x.2)
      calc (y' : G) * x * (y' : G)⁻¹ = (x * y') * (y' : G)⁻¹ := by rw [← this]
        _ = x := by group
    rw [h1, orderOf_one] at ha3
    omega

end Swap

section Case1

variable {G : Type} [Group G] [Finite G]

theorem cl_case1_of_centralScalar {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (h113 : StageLemma14113) (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) (hY : Yp = Y153 Mc M)
    (hX : CentralScalar (↥L ⧸ Subgroup.center ↥L)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := fun s hs => hN (hSI hs)
  have hZ : centerOf L = CFSG.Open.pCoreOf 2 L := c.c33.center_eq
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  obtain ⟨hYN₂, hfix₂, hV2Y, hMIV⟩ := R3c10.ctx2_facts h113 c
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  obtain ⟨hY₁, -⟩ := hh.hyp.Y153_le_normalizer_V h113 hh.decomp
  have hYN₁ : Yp ≤ Subgroup.normalizer (V₁ : Set G) := hY ▸ hY₁
  have hV4 : Nat.card V₂ = 4 := hh.decomp.card₂
  have hV14 : Nat.card V₁ = 4 := hh.decomp.card₁
  have hV2sq : ∀ x ∈ V₂, x * x = 1 := fun x hx => by
    have := hh.hyp.elemAbelian.2 x (hh.decomp.le₂ hx)
    rw [← sq]
    exact this
  have hV1sq : ∀ x ∈ V₁, x * x = 1 := fun x hx => by
    have := hh.hyp.elemAbelian.2 x (hh.decomp.le₁ hx)
    rw [← sq]
    exact this
  have hVS : VZ T M ≤ Sgp153 T V₁ := by
    intro v hv
    refine ⟨hh.hyp.VZ_le_T hv, A4.mem_normalizer_of_conj_mem fun k hk => ?_⟩
    have hc' := congrArg Subtype.val
      (hh.hyp.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨k, hh.decomp.le₁ hk⟩)
    have : v * k * v⁻¹ = k := by
      have h1 : v * k = k * v := hc'
      rw [h1]
      group
    rw [this]
    exact hk
  have hV1S : V₁ ≤ Sgp153 T V₁ := fun v hv => hVS (hh.decomp.le₁ hv)
  have htM : t ∈ M := hh.decomp.t_mem
  have hYt : ∀ y, y ∈ Yp ↔ t * y * t⁻¹ ∈ Yp := fun y => by
    rw [hY]
    exact Subgroup.mem_normalizer_iff.mp (le_normalizer_Y153 Mc M htM) y
  have hfix₁ : ∀ x ∈ V₁, (∀ a ∈ Yp, a * x = x * a) → x = 1 := by
    intro x hx hc
    have hx' : t * x * t⁻¹ ∈ V₂ := hh.decomp.swap₁ x hx
    have h1 : t * x * t⁻¹ = 1 := hfix₂ _ hx' fun a ha => by
      have hta : t⁻¹ * a * t ∈ Yp := (hYt (t⁻¹ * a * t)).mpr (by
        rw [show t * (t⁻¹ * a * t) * t⁻¹ = a by group]
        exact ha)
      have h2 := hc _ hta
      calc a * (t * x * t⁻¹) = t * ((t⁻¹ * a * t) * x) * t⁻¹ := by group
        _ = t * (x * (t⁻¹ * a * t)) * t⁻¹ := by rw [h2]
        _ = (t * x * t⁻¹) * a := by group
    calc x = t⁻¹ * (t * x * t⁻¹) * t := by group
      _ = 1 := by rw [h1]; group
  have hgen : Yp ≤ Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    conv_lhs => rw [c.facts.theta]
    rw [thetaOf, Subgroup.closure_le]
    intro x hx
    have hxY : x ∈ Yp := by
      rw [c.facts.theta]
      exact Subgroup.subset_closure hx
    exact Subgroup.subset_closure ⟨hxY, 1, by simpa using hx.2⟩
  have hV1N : V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun v hv =>
    hMIY ⟨hSM (hV1S hv), hSI (hV1S hv)⟩
  have hV1Y : V₁ ≤ Yp := by
    rcases R3c9.centralizes_or_le_of_generated_by_threePow hgen hV1N hYN₁ hV14 with hc | ⟨hle, -⟩
    · exfalso
      obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V₁, u ≠ 1 := by
        by_contra hcon
        push Not at hcon
        have : V₁ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon x hx)
        rw [this, Subgroup.card_bot] at hV14
        omega
      exact hu1 (hfix₁ u hu fun a ha => hc a ha u hu)
    · exact hle
  have hV1L : V₁ ≤ L := hV1Y.trans hYL
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hQS : Sgp153 T V₁ ⊓ L ≤ Sgp153 T V₁ := inf_le_left
  have hV1Q : V₁ ≤ Sgp153 T V₁ ⊓ L := le_inf hV1S hV1L
  have hV2Q : V₂ ≤ Sgp153 T V₁ ⊓ L := le_inf hV2S hV2L
  have hQV₂ : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (V₂ : Set G) := fun q hq =>
    hMIV ⟨hSM (hQS hq), hSI (hQS hq)⟩
  have hQV₁ : Sgp153 T V₁ ⊓ L ≤ Subgroup.normalizer (V₁ : Set G) := fun q hq => (hQS hq).2
  have hVz₁ : ∀ x ∈ V₁, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix₁ x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  have hVz₂ : ∀ x ∈ V₂, x ∈ centerOf L → x = 1 := fun x hx hxc =>
    hfix₂ x hx fun b hb => Subgroup.mem_centralizer_iff.mp hxc.2 b (hYL hb)
  have hy : ∃ y ∈ Yp, ∃ k : ℕ, y ^ (3 ^ k) = 1 ∧ ¬ ∀ v ∈ V₁, y * v = v * y := by
    by_contra hcon
    push Not at hcon
    obtain ⟨u, hu, hu1⟩ : ∃ u ∈ V₁, u ≠ 1 := by
      by_contra hcon'
      push Not at hcon'
      have : V₁ = ⊥ := eq_bot_iff.mpr fun x hx => Subgroup.mem_bot.mpr (hcon' x hx)
      rw [this, Subgroup.card_bot] at hV14
      omega
    have hle : Yp ≤ Subgroup.centralizer (V₁ : Set G) := by
      refine hgen.trans ((Subgroup.closure_le _).2 fun x hx => ?_)
      obtain ⟨hxY, k, hk⟩ := hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hcon x hxY k (by rw [← hk]; exact pow_orderOf_eq_one x) v hv).symm
    exact hu1 (hfix₁ u hu fun b hb => (Subgroup.mem_centralizer_iff.mp (hle hb) u hu).symm)
  obtain ⟨y, hyY, k, hyk, hyn⟩ := hy
  obtain ⟨Tsyl, hT, hTcomap, hNcomap⟩ := exists_quotSylow hZ hQsyl
  have hTsyl : IsSylowTwoOf (((Sgp153 T V₁ ⊓ L).subgroupOf L).map
      (QuotientGroup.mk' (Subgroup.center ↥L))) ⊤ := by
    rw [← hT]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  obtain ⟨h4₁, h2₁⟩ := quot_klein hV1L hV14 hV1sq hVz₁
  obtain ⟨h4₂, h2₂⟩ := quot_klein hV2L hV4 hV2sq hVz₂
  have hVT₁ : (V₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤
      ((Sgp153 T V₁ ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hV1Q (Subgroup.mem_subgroupOf.mp hx))
  have hVT₂ : (V₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≤
      ((Sgp153 T V₁ ⊓ L).subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :=
    Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr
      (hV2Q (Subgroup.mem_subgroupOf.mp hx))
  have hTN₁ := quot_normalizes hV1L hQV₁
  have hTN₂ := quot_normalizes hV2L hQV₂
  have hyL : y ∈ L := hYL hyY
  have hyN : QuotientGroup.mk' (Subgroup.center ↥L) (⟨y, hyL⟩ : ↥L) ∈
      Subgroup.normalizer (((V₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :
        Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set (↥L ⧸ Subgroup.center ↥L)) :=
    quot_normalizes hV1L hYN₁ ⟨⟨y, hyL⟩, Subgroup.mem_subgroupOf.mpr hyY, rfl⟩
  have hyk' : (QuotientGroup.mk' (Subgroup.center ↥L) (⟨y, hyL⟩ : ↥L)) ^ (3 ^ k) = 1 := by
    rw [← map_pow]
    have : (⟨y, hyL⟩ : ↥L) ^ (3 ^ k) = 1 := Subtype.ext (by simpa using hyk)
    rw [this, map_one]
  have hynq : ¬ ∀ v ∈ (V₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)),
      QuotientGroup.mk' (Subgroup.center ↥L) (⟨y, hyL⟩ : ↥L) * v =
        v * QuotientGroup.mk' (Subgroup.center ↥L) (⟨y, hyL⟩ : ↥L) := by
    intro h
    apply hyn
    intro v hv
    have hc := h (QuotientGroup.mk' (Subgroup.center ↥L) (⟨v, hV1L hv⟩ : ↥L))
      ⟨⟨v, hV1L hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
    exact comm_of_quot_comm hYN₁ hVz₁ (a₀ := ⟨y, hyL⟩) (v₀ := ⟨v, hV1L hv⟩) hyY hv hc
  obtain ⟨-, hb⟩ := hX hTsyl hVT₁ h4₁ hTN₁ hyN hyk' hynq
  obtain ⟨y₁, hy₁Y, hy₁V₂, hy₁V₁⟩ := exists_y_centralizing_V₂ h113 hh.hyp hh.decomp
  rw [← hY] at hy₁Y
  have hy₁L : y₁ ∈ L := hYL hy₁Y
  have hV₂ne : (V₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≠ ⊥ := by
    intro hb0
    rw [hb0, Subgroup.card_bot] at h4₂
    omega
  obtain ⟨z, hzV, hz1, hzc⟩ := exists_central_of_normal (K1.isSylowTwoOf_top_iff.mp hTsyl).1
    hVT₂ hV₂ne hTN₂
  have hy₁N : QuotientGroup.mk' (Subgroup.center ↥L) (⟨y₁, hy₁L⟩ : ↥L) ∈
      Subgroup.normalizer (((V₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :
        Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set (↥L ⧸ Subgroup.center ↥L)) :=
    quot_normalizes hV1L hYN₁ ⟨⟨y₁, hy₁L⟩, Subgroup.mem_subgroupOf.mpr hy₁Y, rfl⟩
  have hy₁z : QuotientGroup.mk' (Subgroup.center ↥L) (⟨y₁, hy₁L⟩ : ↥L) * z =
      z * QuotientGroup.mk' (Subgroup.center ↥L) (⟨y₁, hy₁L⟩ : ↥L) := by
    obtain ⟨v₂, hv₂, rfl⟩ := hzV
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hy₁V₂ _ (Subgroup.mem_subgroupOf.mp hv₂))
  have hall := hb _ hy₁N z (hVT₂ hzV) hzc hz1 hy₁z
  apply hy₁V₁
  intro v hv
  have hc := hall (QuotientGroup.mk' (Subgroup.center ↥L) (⟨v, hV1L hv⟩ : ↥L))
    ⟨⟨v, hV1L hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  exact comm_of_quot_comm hYN₁ hVz₁ (a₀ := ⟨y₁, hy₁L⟩) (v₀ := ⟨v, hV1L hv⟩) hy₁Y hv hc

end Case1

end CFSG.Quasithin.R3c17
