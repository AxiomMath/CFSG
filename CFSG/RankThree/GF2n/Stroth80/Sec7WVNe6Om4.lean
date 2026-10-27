module

public import CFSG.RankThree.GF2n.Stroth80.Sec7GStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Frame
public import CFSG.RankThree.GF2n.Stroth80.Sec7WVOrder
public import CFSG.RankThree.GF2n.Stroth80.Sec7CentralizerWt
public import CFSG.RankThree.GF2n.Stroth80.Sec7Om4Quad
public import CFSG.RankThree.GF2n.Stroth80.Sec78RootOrders
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaFacts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped commutatorElement Matrix

theorem sec7om4_sup_comm {G : Type} [Group G] {S V : Subgroup G}
    (hS : ∀ a ∈ S, ∀ b ∈ S, a * b = b * a) (hV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    (hSV : ∀ a ∈ S, ∀ v ∈ V, a * v = v * a) : ∀ a ∈ S ⊔ V, ∀ b ∈ S ⊔ V, a * b = b * a := by
  have hn : V ≤ Subgroup.normalizer (S : Set G) := by
    refine Subgroup.le_normalizer_iff.mpr fun v hv s hs => ?_
    have : v * s * v⁻¹ = s := by
      rw [mul_inv_eq_iff_eq_mul]
      exact (hSV s hs v hv).symm
    rw [this]
    exact hs
  intro a ha b hb
  have ha' : a ∈ ((S ⊔ V : Subgroup G) : Set G) := ha
  have hb' : b ∈ ((S ⊔ V : Subgroup G) : Set G) := hb
  rw [Subgroup.coe_mul_of_right_le_normalizer_left S V hn] at ha' hb'
  obtain ⟨s₁, hs₁, v₁, hv₁, rfl⟩ := ha'
  obtain ⟨s₂, hs₂, v₂, hv₂, rfl⟩ := hb'
  calc s₁ * v₁ * (s₂ * v₂) = s₁ * (v₁ * s₂) * v₂ := by simp only [mul_assoc]
    _ = s₁ * (s₂ * v₁) * v₂ := by rw [← hSV s₂ hs₂ v₁ hv₁]
    _ = (s₁ * s₂) * (v₁ * v₂) := by simp only [mul_assoc]
    _ = (s₂ * s₁) * (v₂ * v₁) := by rw [hS s₁ hs₁ s₂ hs₂, hV v₁ hv₁ v₂ hv₂]
    _ = s₂ * (s₁ * v₂) * v₁ := by simp only [mul_assoc]
    _ = s₂ * (v₂ * s₁) * v₁ := by rw [hSV s₁ hs₁ v₂ hv₂]
    _ = s₂ * v₂ * (s₁ * v₁) := by simp only [mul_assoc]

theorem sec7_conj_LomGL {G : Type} [Group G] {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K]
    {R : Subgroup G} {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q' X) (φ : ↥R →* GL ι K) (hφ : φ.range = X) (r₀ : ↥R) {L₀ : Subgroup G}
    {w : ι → K} (hL : (L₀.subgroupOf R).map φ = E.LomGL w) :
    ((conjSubgroup (r₀ : G) L₀).subgroupOf R).map φ =
      E.LomGL ((φ r₀ : Matrix ι ι K) *ᵥ w) := by
  have hr₀ : φ r₀ ∈ X := hφ ▸ MonoidHom.mem_range.mpr ⟨r₀, rfl⟩
  refine map_conjSubgroup_subgroupOf (e := E.equiv) φ hφ r₀ (S := Lom Q' w)
    (S' := Lom Q' ((φ r₀ : Matrix ι ι K) *ᵥ w)) (fun h => ?_) hL
  have := mem_Lom_app_iff (E.equiv ⟨φ r₀, hr₀⟩) w h
  rwa [E.app ⟨φ r₀, hr₀⟩ w] at this

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7_om4_points (hPts : Sec5NatPointsOmegaStatement) (hc : Ctx M Q Z B) {n : ℕ} {t : G}
    (hs : Sec7Hyp hc n t) (hom : OmegaMinusNat hc t 2) {r : G} (hr : Sec7A hc t r) :
    (∀ y ∈ LB M Q (conjSubgroup r B), y ∉ hc.CN t →
      Rt M (LB M Q B) t ≤ hc.CN t ⊔ (LB M Q B ⊔ conjSubgroup y (LB M Q B))) ∧
    (∀ y ∈ LB M Q B, y ∉ hc.CN t →
      Rt M (LB M Q B) t ≤ hc.CN t ⊔
        (LB M Q (conjSubgroup r B) ⊔ conjSubgroup y (LB M Q (conjSubgroup r B)))) ∧
    Nat.card (LB M Q B) = Nat.card ↥(LB M Q B ⊓ hc.CN t) * Nat.card Z ^ 2 ∧
    Nat.card (LB M Q (conjSubgroup r B)) =
      Nat.card ↥(LB M Q (conjSubgroup r B) ⊓ hc.CN t) * Nat.card Z ^ 2 := by
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hq : 1 < Nat.card Z := by omega
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hLA : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  obtain ⟨K, hKf, hKfin, hchar, hKZ, hcases⟩ :=
    hPts G M Q Z B hc n t hs.toSec5 hs.omegaNat r hr.mem hr.plane
  have hV := n12N_card_V hc t 2 le_rfl (Or.inr hom)
  rcases hcases with
    ⟨m', hm', φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩ |
    ⟨m', b, c, hm', hirr, φ, u, u', hu, hu', hu0, hu0', huu', hrange, hker, hsec, hLu, hLu'⟩
  · exfalso
    have hnat : NaturalRep (ι := Fin m' ⊕ Fin m') K (StatedOmega (StatedQuadPlus m' K))
        (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hι : Fintype.card (Fin m' ⊕ Fin m') = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    have hmm : m' = 2 := sec7_pin_dim hq (hcard.symm.trans hV)
    omega
  · have hnat : NaturalRep (ι := Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) K
        (StatedOmega (StatedQuadMinus m' K b c)) (Rt M (LB M Q B) t)
        (Vt M (LB M Q B) B Z t) Z (hc.CN t) := ⟨φ, hrange, hker, hsec⟩
    have hcard := card_of_naturalRep hnat sec39_Z_le_Vt hKZ
    have hι : Fintype.card (Fin (m' - 1) ⊕ Fin (m' - 1) ⊕ Fin 2) = 2 * m' := by
      simp only [Fintype.card_sum, Fintype.card_fin]
      omega
    rw [hι] at hcard
    have hmm : m' = 2 := sec7_pin_dim hq (hcard.symm.trans hV)
    subst hmm
    haveI : Nonempty (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
    have hQnd := nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
    set E := ElemMatrixIso.minus (K := K) hm' hirr with hE
    have hL₁ : ((LB M Q B).subgroupOf (Rt M (LB M Q B) t)).map φ = E.LomGL u := by
      rw [hE, ElemMatrixIso.LomGL_minus hm' hirr]
      exact hLu
    have hL₂ : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ =
        E.LomGL u' := by
      rw [hE, ElemMatrixIso.LomGL_minus hm' hirr, hLA]
      exact hLu'
    have hroot : ∀ (A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) (v : _ → K),
        quadMinus 2 K b c v = 0 → v ≠ 0 → A ∈ E.LomGL v →
          A ∈ rootGroupGL (quadMinus 2 K b c) v := by
      intro A v hv hv0 hA
      obtain ⟨hAX, hrest⟩ := (E.mem_LomGL_iff_flag hQnd hv hv0).mp hA
      exact (mem_rootGroupGL_iff hQnd hv hv0).mpr ⟨fun x => E.quad_mulVec hAX x, hrest⟩
    refine ⟨?_, ?_, ?_, ?_⟩
    · intro y hy hyN
      have hyR : y ∈ Rt M (LB M Q B) t := hL2R hy
      have hmem : φ ⟨y, hyR⟩ ∈ E.LomGL u' := by
        rw [← hL₂]
        exact ⟨⟨y, hyR⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      have hne1 : φ ⟨y, hyR⟩ ≠ 1 := by
        intro h1
        have : (⟨y, hyR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := (MonoidHom.mem_ker).mpr h1
        rw [hker, Subgroup.mem_subgroupOf] at this
        exact hyN this
      have hne := sec7_polar_apply_ne_zero_of_mem_rootGroupGL hirr hu hu' hu0 hu0' huu'
        (hroot _ u' hu' hu0' hmem) hne1
      have hrX : φ ⟨y, hyR⟩ ∈ StatedOmega (StatedQuadMinus 2 K b c) :=
        hrange ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
      have hu₂ : quadMinus 2 K b c ((φ ⟨y, hyR⟩ : Matrix _ _ K) *ᵥ u) = 0 := by
        rw [E.quad_mulVec hrX]
        exact hu
      exact le_sup_secOmega E hQnd φ hrange hker hu hu₂ hne hL₁
        (sec7_conj_LomGL E φ hrange ⟨y, hyR⟩ hL₁)
    · intro y hy hyN
      have hyR : y ∈ Rt M (LB M Q B) t := hLR hy
      have hmem : φ ⟨y, hyR⟩ ∈ E.LomGL u := by
        rw [← hL₁]
        exact ⟨⟨y, hyR⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
      have hne1 : φ ⟨y, hyR⟩ ≠ 1 := by
        intro h1
        have : (⟨y, hyR⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := (MonoidHom.mem_ker).mpr h1
        rw [hker, Subgroup.mem_subgroupOf] at this
        exact hyN this
      have hu'u : polar (quadMinus 2 K b c) u' u ≠ 0 := by
        rw [polar_comm]
        exact huu'
      have hne := sec7_polar_apply_ne_zero_of_mem_rootGroupGL hirr hu' hu hu0' hu0 hu'u
        (hroot _ u hu hu0 hmem) hne1
      have hrX : φ ⟨y, hyR⟩ ∈ StatedOmega (StatedQuadMinus 2 K b c) :=
        hrange ▸ MonoidHom.mem_range.mpr ⟨_, rfl⟩
      have hu₂ : quadMinus 2 K b c ((φ ⟨y, hyR⟩ : Matrix _ _ K) *ᵥ u') = 0 := by
        rw [E.quad_mulVec hrX]
        exact hu'
      exact le_sup_secOmega E hQnd φ hrange hker hu' hu₂ hne hL₂
        (sec7_conj_LomGL E φ hrange ⟨y, hyR⟩ hL₂)
    · have hsplit := card_inf_mul_card_map hLR φ hker
      rw [hLu, sec7ctr_card_LomGLMinus hm' hirr hu hu0] at hsplit
      rw [← hsplit, hKZ]
    · have hsplit := card_inf_mul_card_map hL2R φ hker
      rw [hLA] at hsplit ⊢
      rw [hLu', sec7ctr_card_LomGLMinus hm' hirr hu' hu0'] at hsplit
      rw [← hsplit, hKZ]

theorem sec7WVNe6Om4_of (h34 : Stroth34Statement) (hA : Sec7AExistsStatement)
    (hPts : Sec5NatPointsOmegaStatement) (h52a : Stroth52aStatement) (h52b : Stroth52bStatement)
    (h52c : Stroth52cStatement) : Sec7WVNe6Om4Statement := by
  intro G _ _ M Q Z B hc n t hs hom hn6
  classical
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  have h5 := hs.toSec5
  have ht : t ∈ LB M Q B := h5.mem
  have htQ : t ∉ Q := h5.notQ
  have h35 := (stroth_3_5 h34 hc h5.width h5.n_gt h5.noA2 h5.gen).2.1
  have hcC : Ctx M Q Z (conjSubgroup r B) := hc.conj_of_mem (hc.Rt_le_M t hr.mem)
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  obtain ⟨hgen, hgen', hcardL, hcardL'⟩ := sec7_om4_points hPts hc hs hom hr
  have hLR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) ht
  have hL2R : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t := le_sup_right.trans hr.gen.ge
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hVabel := hc.Vt_isElemAbelian h35 ht htQ
  obtain ⟨-, hPN⟩ := h52a G M Q Z B hc n t h5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (hc.CN t) (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
    rfl rfl rfl rfl
  have hd := h52b G M Q Z B hc n t h5 hs.omegaNat r hr.mem hr.plane
    (conjSubgroup r B) (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t)
    (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl rfl rfl
  haveI : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (fun v hv =>
      hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (hVQ hv)))
  have hWQ : Wt Q (Vt M (LB M Q B) B Z t) ≤ Q := inf_le_left
  have hchi := card_mul_card_of_isChiIso
    (h52c G M Q Z B hc n t h5 hs.omegaNat (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t)
      (Wt Q (Vt M (LB M Q B) B Z t)) rfl rfl rfl) hWQ sec39_Z_le_Vt
  have hV := n12N_card_V hc t 2 le_rfl (Or.inr hom)
  have hVpos : 0 < Nat.card (Vt M (LB M Q B) B Z t) := Nat.card_pos
  have hWV : Nat.card (Wt Q (Vt M (LB M Q B) B Z t)) =
      Nat.card (Vt M (LB M Q B) B Z t) * Nat.card Z ^ 4 := by
    have hQc : Nat.card Q = Nat.card Z ^ (2 * n + 1) := h5.width
    subst hn6
    have h14 : Nat.card Q * Nat.card Z = Nat.card Z ^ 14 := by
      rw [hQc]
      ring
    apply Nat.eq_of_mul_eq_mul_right hVpos
    rw [← hchi, h14, hV]
    ring
  have hVW : Vt M (LB M Q B) B Z t ≤ Wt Q (Vt M (LB M Q B) B Z t) := fun b hb =>
    ⟨hVQ hb, Subgroup.mem_centralizer_iff.mpr fun v hv =>
      congrArg Subtype.val (hVabel.1.is_comm.comm ⟨v, hv⟩ ⟨b, hb⟩)⟩
  have hVcen : ∀ v ∈ Vt M (LB M Q B) B Z t, ∀ x ∈ Wt Q (Vt M (LB M Q B) B Z t), v * x = x * v :=
    fun v hv x hx => Subgroup.mem_centralizer_iff.mp hx.2 v hv
  have hAab : ∀ (C' : Subgroup G), Ctx M Q Z C' →
      ∀ a ∈ (QB C' ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t,
        ∀ b ∈ (QB C' ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t,
          a * b = b * a := by
    intro C' hcC'
    refine sec7om4_sup_comm (fun a ha b hb => ?_) (fun a ha b hb => ?_) (fun a ha v hv => ?_)
    · have hE := hcC'.inf_QB_elemAbelian
      have := hE.1.is_comm.comm ⟨a, hWQ ha.2, ha.1⟩ ⟨b, hWQ hb.2, hb.1⟩
      exact congrArg Subtype.val this
    · exact hVcen a ha b (hVW hb)
    · exact (hVcen v hv a ha.2).symm
  have hZc : ∀ (C' : Subgroup G), Ctx M Q Z C' → ∀ y ∈ LB M Q C', ∀ z ∈ Z, y * z = z * y := by
    intro C' hcC' y hy z hz
    have := hcC'.LB_centralizes_Z hy z hz
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  have F : Om4Frame Q Z (Vt M (LB M Q B) B Z t) (Wt Q (Vt M (LB M Q B) B Z t))
      (Rt M (LB M Q B) t) (hc.CN t) (LB M Q B) (LB M Q (conjSubgroup r B))
      ((QB B ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t)
      ((QB (conjSubgroup r B) ⊓ Wt Q (Vt M (LB M Q B) B Z t)) ⊔ Vt M (LB M Q B) B Z t)
      (Nat.card Z) :=
    { ZV := sec39_Z_le_Vt
      VW := hVW
      WQ := hWQ
      Qcomm := fun x hx y hy => hc.hyp.toHyp79.comm_mem_V hx hy
      Qsq := fun x hx => hc.hyp.toHyp79.sq_mem_V hx
      Zcen := fun z hz x hx => hc.hyp.toHyp79.V_central hz hx
      Vsq := hVabel.2
      Vcen := hVcen
      RV := fun s hs x hx => (Subgroup.mem_normalizer_iff.mp (hc.Rt_normalizes_Vt ht hs) x).mp hx
      RW := fun s hs x hx => sec7WVOrd_conj_mem hc ht hs hx
      NR := fun x hx => (Ctx.mem_CN.mp hx).1
      LR := hLR
      L'R := hL2R
      N3 := hPN
      opp := hd
      Lsq := fun y hy => hc.sq_mem_Q_of_mem_LB hy
      L'sq := fun y hy => hcC.sq_mem_Q_of_mem_LB hy
      LZ := hZc B hc
      L'Z := hZc (conjSubgroup r B) hcC
      gen := hgen
      gen' := hgen'
      cardL := hcardL
      cardL' := hcardL'
      Aab := hAab B hc
      A'ab := hAab (conjSubgroup r B) hcC
      CQW := fun x hx hxW => hc.centralizer_Wt_le_Vt t hx hxW
      q2 := by omega
      WV := hWV }
  exact F.contradiction

end CFSG.RankThree.GF2n.Stroth80
