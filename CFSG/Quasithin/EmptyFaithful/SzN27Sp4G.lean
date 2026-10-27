module

public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4E
public import CFSG.Quasithin.EmptyFaithful.SzN27Sp4F
public import CFSG.Quasithin.EmptyFaithful.R3c17D

public section

namespace CFSG.Quasithin.SzN27

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Blueprint
open CFSG.Quasithin.R3c10 CFSG.Quasithin.R3c14 CFSG.Quasithin.R3c15 CFSG.Quasithin.R3c16
open scoped commutatorElement

section Case1

variable {G : Type} [Group G] [Finite G]

theorem cl15335_case1_of_sp4 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (h113 : StageLemma14113) (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hN : I ≤ Subgroup.normalizer (L : Set G)) (hYL : Yp ≤ L) (hY : Yp = Y153 Mc M) {f : ℕ}
    (hf : 2 ≤ f)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 f) :
    False := by
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
  obtain ⟨y₁, hy₁Y, hy₁V₂, hy₁V₁⟩ := R3c17.exists_y_centralizing_V₂ h113 hh.hyp hh.decomp
  rw [← hY] at hy₁Y
  have hy₁L : y₁ ∈ L := hYL hy₁Y
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
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun s hs =>
    hMIY ⟨hSM hs, hSI hs⟩
  have hTH := quot_normalizes hYL (fun q hq => hSN (hQS hq))
  have hy₁N : QuotientGroup.mk' (Subgroup.center ↥L) (⟨y₁, hy₁L⟩ : ↥L) ∈
      Subgroup.normalizer (((V₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) :
        Subgroup (↥L ⧸ Subgroup.center ↥L)) : Set (↥L ⧸ Subgroup.center ↥L)) :=
    quot_normalizes hV1L hYN₁ ⟨⟨y₁, hy₁L⟩, Subgroup.mem_subgroupOf.mpr hy₁Y, rfl⟩
  have hy₁nq : ¬ ∀ v ∈ (V₁.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)),
      QuotientGroup.mk' (Subgroup.center ↥L) (⟨y₁, hy₁L⟩ : ↥L) * v =
        v * QuotientGroup.mk' (Subgroup.center ↥L) (⟨y₁, hy₁L⟩ : ↥L) := by
    intro h'
    apply hy₁V₁
    intro v hv
    have hc := h' (QuotientGroup.mk' (Subgroup.center ↥L) (⟨v, hV1L hv⟩ : ↥L))
      ⟨⟨v, hV1L hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
    exact comm_of_quot_comm hYN₁ hVz₁ (a₀ := ⟨y₁, hy₁L⟩) (v₀ := ⟨v, hV1L hv⟩) hy₁Y hv hc
  have hV₂ne : (V₂.subgroupOf L).map (QuotientGroup.mk' (Subgroup.center ↥L)) ≠ ⊥ := by
    intro hb0
    rw [hb0, Subgroup.card_bot] at h4₂
    omega
  obtain ⟨z, hzV, hz1, hzc⟩ := exists_central_of_normal (K1.isSylowTwoOf_top_iff.mp hTsyl).1
    hVT₂ hV₂ne hTN₂
  have hy₁z : QuotientGroup.mk' (Subgroup.center ↥L) (⟨y₁, hy₁L⟩ : ↥L) * z =
      z * QuotientGroup.mk' (Subgroup.center ↥L) (⟨y₁, hy₁L⟩ : ↥L) := by
    obtain ⟨v₂, hv₂, rfl⟩ := hzV
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hy₁V₂ _ (Subgroup.mem_subgroupOf.mp hv₂))
  have hTle := sp4_sylow_le hf h hTsyl hVT₁ h4₁ h2₁ hTN₁ hTH
    (y := QuotientGroup.mk' (Subgroup.center ↥L) (⟨y₁, hy₁L⟩ : ↥L)) (z := z)
    ⟨⟨y₁, hy₁L⟩, Subgroup.mem_subgroupOf.mpr hy₁Y, rfl⟩ hy₁N hy₁nq (hVT₂ hzV) hz1
    (fun t ht => (hzc t ht).symm) hy₁z
  obtain ⟨φ, hφ, hφk⟩ := c.s3s3
  have hY3 : ∀ y ∈ Yp, y ^ 3 ∈ pCoreOf 2 Yp := exp3_of_struct c.facts11.struct_Yp
  exact false_of_s3s3 hZ hSyl.2.1 hSL hSN hYL hQsyl hY3 φ hφ hφk hTle (outCyclic_of_sp4 hf h)

theorem cl15335_of_sp4 {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G} (h113 : StageLemma14113)
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hN : I ≤ Subgroup.normalizer (L : Set G))
    (hYL : Yp ≤ L) {f : ℕ} (hf : 2 ≤ f)
    (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel (↥L ⧸ Subgroup.center ↥L) .PSp 2 2 f) :
    False := by
  rcases c.hyp.cases with hY | hU
  · exact cl15335_case1_of_sp4 h113 c hN hYL hY hf h
  · exact cl15335_case2_of_sp4 h113 c hN hYL hU hf h

end Case1

end CFSG.Quasithin.SzN27
