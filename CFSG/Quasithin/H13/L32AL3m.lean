module

public import CFSG.Quasithin.H13.L32AL3f
public import CFSG.Quasithin.H13.L32AL3h
public import CFSG.Quasithin.H13.L32AL3l
public import CFSG.Quasithin.H13.L32AL3S
public import CFSG.Quasithin.H13.L32A7S6wa
public import CFSG.Quasithin.H13.L32AL3d

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

theorem lemma14_7_32_L2_loc_of (hD36 : D36) (hD37 : D37)
    (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (h76 : Lemma14_7_6) (h33 : Lemma14_7_33)
    (h36 : A36ForSQTK) (hA39 : A39ForSQTK) (hlist : SQTKList3Dvd) (h29 : Thm14_7_29)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14)
    (hI : Lemma14_7_32_L2_I) : Lemma14_7_32_L2_loc := by
  intro G _ _ T L V K R hcase
  have hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V) :=
    hypF98_of h1222 h1332 h1334 hA37 hA38 hA39 R.S
  have : IsMulCommutative ↥(conjClosure V (A6.g1 T V)) := hF.F911_3.1
  obtain ⟨c, t, hcR, hV1c, hA1c, hne, hDH, htU, htQ, ht2⟩ := exists_alpha hF hcase
  obtain ⟨t₀, Cx⟩ := exists_ctxL2_of_red hA37 hA38 R
  obtain ⟨W, hW⟩ := exists_topW R.S hF
  have hWV : W = fsuV1 T V := by
    rcases L2Red.irred hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334 R hF hcase
      hW.hV₁W hW.hWU.le hW.hHW with h | h
    · exact h
    · exact absurd h hW.hWU.ne
  subst hWV
  have X : TopCtx T L V K (fsuV1 T V) t₀ := ⟨R, Cx, hW⟩
  obtain ⟨F, _, _, π, β, Y⟩ :=
    X.exists_model hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332 h1334
  have : CharP F 2 := Y.charP
  obtain ⟨e, he1, he2, he3⟩ := Y.exists_normalized
  obtain ⟨z, hzV, hz1⟩ : ∃ z ∈ fsuV1 T V, z ≠ 1 := by
    by_contra hall
    push Not at hall
    have : fsuV1 T V = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr hall
    have h2 := hF.card_V₁
    rw [this, Subgroup.card_bot] at h2
    omega
  have hz : Subgroup.zpowers z = fsuV1 T V := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hzV) ?_
    rw [hF.card_V₁, Nat.card_zpowers]
    have h1 : orderOf z ≠ 1 := fun h0 => hz1 (orderOf_eq_one_iff.mp h0)
    have h2 : orderOf z ≠ 0 := (orderOf_pos z).ne'
    omega
  set z' := c * z * c⁻¹ with hz'
  have hzc : Subgroup.zpowers z' = Quasithin.conjSub c (fsuV1 T V) := by
    rw [← hz]
    exact (MonoidHom.map_zpowers (MulAut.conj c).toMonoidHom z).symm
  have hz'U : z' ∈ conjClosure V (A6.g1 T V) := hA1c (hzc ▸ Subgroup.mem_zpowers z')
  have hC := L2Red.inf_centralizer_qh hD36 hD37 hA37 hA38 h76 h33 h36 hlist h29 h1222 h1332
    h1334 h13314 R hF hcase
  have hcU' : Quasithin.conjSub c⁻¹ (fsuV1 T V) ≤ conjClosure V (A6.g1 T V) := by
    rw [Quasithin.conjSub_le_iff, inv_inv]
    exact hV1c
  have h1 := a114Hyp_of hF hC hz hA1c hcU' hne
  rw [← hzc] at h1
  have hcard : Nat.card ↥(Quasithin.conjSub c (fsuV1 T V)) = 2 :=
    (Subgroup.card_map_of_injective (MulAut.conj c).injective).trans hF.card_V₁
  have ht1 : X.top.act t ≠ 1 := fun h0 =>
    htQ ((X.act_eq_one_iff hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 t).mp h0)
  have hidx := L32A.relIndex_centralizer_le hDH hcard htU
  have hz'1 : z' ≠ 1 := fun h0 => hz1 (by
    calc z = c⁻¹ * (c * z * c⁻¹) * c := by group
      _ = 1 := by rw [← hz', h0]; group)
  have hcardz' : Nat.card ↥(Subgroup.zpowers z') ≤ 2 := by rw [hzc, hcard]
  have hDt : ∀ d ∈ F8.DH V (fsuV1 T V) (A6.g1 T V) c, d ∈ conjClosure V (A6.g1 T V) →
      (t : G) * d * (t : G)⁻¹ * d⁻¹ = 1 ∨ (t : G) * d * (t : G)⁻¹ * d⁻¹ = z' := by
    intro d hd _
    have h2 : d * t * d⁻¹ * (t : G)⁻¹ ∈ Quasithin.conjSub c (fsuV1 T V) := hd.2.2 _ htU
    rw [← hzc] at h2
    have h3 : (t : G) * d * (t : G)⁻¹ * d⁻¹ ∈ Subgroup.zpowers z' := by
      have := Subgroup.inv_mem _ h2
      simpa [mul_assoc] using this
    by_cases h0 : (t : G) * d * (t : G)⁻¹ * d⁻¹ = 1
    · exact Or.inl h0
    · exact Or.inr (WrData.eq_of_card_le_two hcardz' h3 (Subgroup.mem_zpowers z') h0 hz'1)
  have hR1t : (t : G) ∈ pCoreOf 2 (l1 T L V ⊔ T) := hcR htU
  have C : X.CfgAt e t hz'U := X.l2Cfg hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 h13314
    Y.card e he1 he2 he3 hR1t ht2 ht1 hidx hDH.le hz'U hDt
  set VY := fsuV1 T V ⊔ Subgroup.zpowers z' with hVY
  set TY := pCoreOf 2 (l1 T L V ⊔ T) ⊓ Subgroup.normalizer (VY : Set G) with hTY
  have hTN : TY ≤ Subgroup.normalizer (VY : Set G) := inf_le_right
  have hTT : TY ≤ T := inf_le_left.trans (Setting147.R1_le_T R.S)
  have hCz := centralizer_singleton_eq hF hz
  have hTz : TY ≤ Subgroup.centralizer ({z} : Set G) := by
    rw [hCz]
    exact hTT.trans (Setting147.TH' R.S)
  have hT2 : IsPGroup 2 TY := (pCoreOf_isPGroup 2 _).to_le inf_le_left
  have hOT := X.pCoreOf_le_TY e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hF hz h1 C he1 hR1t
  have hQH := X.pCoreOf_g1_le_TY hF hz h1 hz'U
  have hQT : twoCoreCentralizer z ≤ TY := by
    rw [twoCoreCentralizer, hCz]
    exact hQH
  have hS := isSylowTwoOf_sup h1 hTN hTz hT2 hOT hQT
  have hO := pCoreOf_sup_eq h1 hTN hTz hT2 hOT hQT
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, hV2⟩ := Hyp147.exists_V2 R.S.hyp (stmt13_3_2_two_of h1332) hMod h1222
  have hCV := X.centralizer_V2_le e h1332 h1334 C hV2
  have hU : ∀ g : G, Quasithin.conjSub g (fsuV1 T V) ≤ VY →
      Quasithin.conjSub g (fsuU T V) ≤ Subgroup.centralizer (VY : Set G) := by
    intro g hg
    have hgz : g * z * g⁻¹ ∈ VY := hg (Quasithin.mul_mem_conjSub hzV)
    have hgz1 : g * z * g⁻¹ ≠ 1 := fun h0 => hz1 (by
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group)
    obtain ⟨y, hy, hyz⟩ := exists_conj_of_mem h1 hgz hgz1
    have hyN : y ∈ Subgroup.normalizer (VY : Set G) := (a114_one h1).1 hy
    have hyg : y⁻¹ * g ∈ A6.g1 T V := by
      rw [← hCz, Subgroup.mem_centralizer_singleton_iff]
      calc y⁻¹ * g * z = y⁻¹ * (g * z * g⁻¹) * g := by group
        _ = y⁻¹ * (y * z * y⁻¹) * g := by rw [hyz]
        _ = z * (y⁻¹ * g) := by group
    have hgU : Quasithin.conjSub g (fsuU T V) = Quasithin.conjSub y (fsuU T V) := by
      rw [show g = y * (y⁻¹ * g) by group, Quasithin.conjSub_mul,
        L32A.conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V (A6.g1 T V) hyg)]
    rw [hgU]
    intro u hu
    rw [Quasithin.mem_conjSub] at hu
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hv' : y⁻¹ * v * y ∈ VY := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) v).mp hv
      simpa using this
    have hVYU : VY ≤ conjClosure V (A6.g1 T V) :=
      sup_le (hF.toHypF91.V₁_le_V.trans (le_conjClosure V _)) (Subgroup.zpowers_le.mpr hz'U)
    have hc := F7.isElemAbelian_comm hF.F911_3 (hVYU hv') hu
    calc v * u = y * ((y⁻¹ * v * y) * (y⁻¹ * u * y)) * y⁻¹ := by group
      _ = y * ((y⁻¹ * u * y) * (y⁻¹ * v * y)) * y⁻¹ := by rw [hc]
      _ = u * v := by group
  have h3 := lemma14_7_31_two R.S.hyp h1222 h1332 h1334 hV2 hCV hS
    (relIndex_pCoreOf_le_two h1 hTN hTz hT2 hOT hQT) (sup_le_normalizer h1 hTN) hO hU
  exact hI G T L V TY z z' R.S hz h1 hTT (X.le_normalizer_TY e hF hz h1 C) hTN hOT hQH hS hO h3
    (X.V_le_TY hF h1222 h1332 h1334 hz'U)
    (X.not_le_normalizer e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hF hz h1 C)
    (X.exists_three_centralizer e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 hF hz h1 C)
    (X.V_le_closure e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 C)
    (X.inf_le_TY e hA37 hA38 h76 h33 h36 hlist h1222 h1332 h1334 C)

end CFSG.Quasithin.H13.L32A.L2
