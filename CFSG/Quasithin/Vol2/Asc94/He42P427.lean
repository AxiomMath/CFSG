module

public import CFSG.Quasithin.Vol2.Asc94.He42P427G
public import CFSG.Quasithin.Vol2.Asc94.He42P427T
public import CFSG.Quasithin.Vol2.Asc94.He42P427H4
public import CFSG.Quasithin.Vol2.Asc94.He42Top
public import CFSG.Quasithin.Vol2.Asc94.He42SE8
public import CFSG.Quasithin.Vol2.Asc94.He42Main
public import CFSG.Quasithin.Vol2.Asc94.He42SE3

public section

namespace CFSG.Quasithin.A94

open Subgroup CFSG.CGT.M24S CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS81
open CFSG.ComponentClassification CFSG.ComponentClassification.RankTwoL3Four
open CFSG.Quasithin.A94.He42 CFSG.Quasithin.A94.He42P427T

private theorem p427f_trichot : ∀ M : HeJ.M2, M.det ≠ 0 →
    M 1 0 = 1 ∨ M = 1 ∨ M = Matrix.of ![![1, 1], ![0, 1]] := by
  decide

theorem p427_cent_z_mul {G : Type} [Group G] (z a : G) :
    centralizer ({z} : Set G) ⊓ centralizer ({z * a} : Set G) =
      centralizer ({z} : Set G) ⊓ centralizer ({a} : Set G) := by
  ext x
  simp only [Subgroup.mem_inf, mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hxz, hxza⟩
    refine ⟨hxz, ?_⟩
    have h : z * (x * a) = z * (a * x) := by
      calc z * (x * a) = (z * x) * a := by group
        _ = (x * z) * a := by rw [← hxz]
        _ = x * (z * a) := by group
        _ = z * a * x := hxza
        _ = z * (a * x) := by group
    exact mul_left_cancel h
  · rintro ⟨hxz, hxa⟩
    refine ⟨hxz, ?_⟩
    calc x * (z * a) = (x * z) * a := by group
      _ = (z * x) * a := by rw [hxz]
      _ = z * (x * a) := by group
      _ = z * (a * x) := by rw [hxa]
      _ = z * a * x := by group

theorem p427_P427
    (h422 : ∀ (hF6 : L52.F6Model) (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
        IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ (S : Setting G z e) (h1
        : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) (a
        x : G) (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1) (hxN : x ∈ normalizer
        ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) (hxa : x ∈ centralizer ({a} : Set G))
        (hx3 : orderOf x = 3) (y₁ y₂ : G), He42.YSpec (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN
        hxa hx3) y₁ y₂ → He42.Open422 (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3) y₁
        y₂) (hF6 : L52.F6Model) (G : Type) [Group G] [Finite G] (z : G)
    (e : ↥(Cz z) ≃* L52.Hc) (hs : IsSimpleGroup G)
    (hK : CFSG.Assembly.KProper CFSG.Blueprint.Catalog G) (S : Setting G z e)
    (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z)
    (a x : G) (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1)
    (hxN : x ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G))
    (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3) :
    P427 (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3) z := by
  set T := He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3 with hT
  have hB : T.BaseFacts := T.baseFacts
  obtain ⟨hzZ, -, hzm⟩ := z_facts_426 e hF6 S h1 h2 ha ham hxN hxa hx3
  have haZ : T.a ∈ T.Z := T.hD.ha
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [S.ord, pow_two] at h
    exact h
  have hfus : T.StepFus := by
    intro y hy y' hy' g hg
    exact (frame2 e S.ord hF6).fusion_B (a := y) (b := y') hy hy' hg
  have hL : ∀ c : G, (∀ b ∈ T.B, c * b = b * c) → c ∈ T.L := fun c hc =>
    he42Input426_of_422 h422 hF6 G z e hs hK S h1 h2 a x ha ham hxN hxa hx3
      (mem_centralizer_iff.2 (fun b hb => (hc b hb).symm))
  have hmain := T.typeL34_main
    (fun y₁ y₂ hY => h422 hF6 G z e hs hK S h1 h2 a x ha ham hxN hxa hx3 y₁ y₂ hY)
  obtain ⟨hcen, htype⟩ := hmain
  have hBL : T.B ≤ T.L := fun b hb => Subgroup.mem_sup_left (p427_A_le_L1 T hB (hB.B_le_Z hb).1)
  have hsimp : IsSimpleGroup (rankTwoQuot T.L) := He42SE.typeL34_isSimpleGroup htype
  have hLcard : Nat.card T.L = 80640 := by
    have hq := card_rankTwoQuot_of_typeL34 htype
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥T.L)
    have hc : Nat.card ↥(Subgroup.center ↥T.L) = 4 := by
      rw [hcen, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv, hB.card_B]
    rw [hc] at h
    have hq' : Nat.card (↥T.L ⧸ Subgroup.center ↥T.L) = 20160 := hq
    rw [hq'] at h
    omega
  have hLodd : ∀ K : Subgroup G, K ≤ T.L → (K.subgroupOf T.L).Normal → Odd (Nat.card K) →
      K ≤ T.B := by
    intro K hKL hKn hKodd
    let π : ↥T.L →* ↥T.L ⧸ Subgroup.center ↥T.L := QuotientGroup.mk' _
    haveI hKπ : ((K.subgroupOf T.L).map π).Normal :=
      hKn.map π (QuotientGroup.mk'_surjective _)
    rcases hsimp.eq_bot_or_eq_top_of_normal ((K.subgroupOf T.L).map π) with hbot | htop
    · intro k hk
      have hk' : (⟨k, hKL hk⟩ : ↥T.L) ∈ K.subgroupOf T.L := Subgroup.mem_subgroupOf.2 hk
      have hmem : π ⟨k, hKL hk⟩ ∈ (K.subgroupOf T.L).map π := Subgroup.mem_map_of_mem π hk'
      rw [hbot, Subgroup.mem_bot] at hmem
      have hkc : (⟨k, hKL hk⟩ : ↥T.L) ∈ Subgroup.center ↥T.L := (QuotientGroup.eq_one_iff _).1 hmem
      rw [hcen] at hkc
      exact Subgroup.mem_subgroupOf.1 hkc
    · exfalso
      have hcard1 : Nat.card ↥((K.subgroupOf T.L).map π) = 20160 := by
        rw [htop, Subgroup.card_top]
        exact He42SE.typeL34_card htype
      have hdvd := Subgroup.card_map_dvd (H := K.subgroupOf T.L) π
      rw [hcard1, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKL).toEquiv] at hdvd
      have hodd := Odd.of_dvd_nat hKodd hdvd
      exact absurd hodd (by decide)
  have hSp : T.StepSpread := by
    have hP := T.stepPsi hB
    obtain ⟨y₁, y₂, hY⟩ := T.stepY
    have hn := T.stepYnorm hB hY
    have hf := T.stepYfpf hB hY
    have h0 := T.stepY0 hB hY
    have hR := T.stepR hB hY
    have hZm := T.stepZmat hB hY
    obtain ⟨hc, -, -, -⟩ := T.exists_wspec hB hP hY hn hf h0
    exact T.stepSpread hB hP hY hn h0 hR hZm hc
  have ha_emb : T.a = emb e He42P427H.abar := a_eq_emb_abar e ha ham
  have hS : Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) = 512 := by
    rw [ha_emb, tr_cent1 e He42P427H.abar, card_tr, He42P427H.card_Sg]
  have hS2 : IsPGroup 2 ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G)) :=
    (IsPGroup.iff_card).2 ⟨9, by rw [hS]; norm_num⟩
  have hfour : ∀ y ∈ T.Z, (T.m y).det ≠ 0 →
      IsPGroup 2 ↥(centralizer ({z} : Set G) ⊓ centralizer ({y} : Set G)) := by
    intro y hy hdet
    rcases p427f_trichot (T.m y) hdet with h1' | h1' | h1'
    · obtain ⟨yt1, hyt1, hyt1e⟩ := (Subgroup.mem_inf.1 hy).1
      obtain ⟨yt2, hyt2, hyt2e⟩ := (Subgroup.mem_inf.1 hy).2
      have hEq : yt1 = yt2 := emb_injective e (hyt1e.trans hyt2e.symm)
      subst hEq
      have hyt : yt1 ∈ L52.A1 ⊓ L52.A2 := Subgroup.mem_inf.2 ⟨hyt1, hyt2⟩
      have hmy : T.m y = L52.zC yt1 := by
        rw [← hyt1e]
        exact HeJ.mG_emb e yt1
      have hytsq : yt1 * yt1 = 1 := by
        apply emb_injective e
        rw [map_mul, map_one, hyt1e]
        exact hB.A_sq y (hB.Z_le_A hy)
      have hpi : L52.piHom yt1 ≠ 1 := He42SE.piHom_ne_one_of_zC (by rw [← hmy]; exact h1')
      rw [← hyt1e, tr_cent1 e yt1]
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 (He42SE.isPGroup_centralizer_of_piHom_ne_one hpi hytsq)
      exact IsPGroup.of_card (n := n) (by rw [card_tr, hn])
    · have hyA : y = T.a := T.hD.hT.minj y hy T.a haZ (by rw [h1', T.hD.ham])
      rw [hyA]
      exact hS2
    · have hza : T.m (z * T.a) = Matrix.of ![![1, 1], ![0, 1]] := by
        rw [T.hD.hT.mmul z hzZ T.a haZ, hzm, T.hD.ham]
        decide
      have hyza : y = z * T.a :=
        T.hD.hT.minj y hy (z * T.a) (T.Z.mul_mem hzZ haZ) (by rw [h1', hza])
      rw [hyza, p427_cent_z_mul]
      exact hS2
  have hS3 : ∀ c ∈ centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G), c * c = 1 →
      c ∉ T.J → Nat.card ↥(centralizer ({z} : Set G) ⊓ centralizer ({T.a} : Set G) ⊓
        centralizer ({c} : Set G)) ≤ 32 := by
    intro c hc hcc hcJ
    rw [ha_emb] at hc hS2 ⊢
    rw [tr_cent1 e He42P427H.abar] at hc
    obtain ⟨cb, hcb, rfl⟩ := (mem_tr e).1 hc
    have hcc' : cb * cb = 1 := by
      apply emb_injective e
      rw [map_mul, map_one]
      exact hcc
    have hJ : T.J = tr e L52.Jm := (tr_sup e L52.A1 L52.A2).symm
    have hcbJ : cb ∉ L52.Jm := fun h => hcJ (by rw [hJ]; exact emb_mem_tr e h)
    have hcm : L52.cm cb 0 1 = 1 := by
      have h := (He42P427H.mem_Jm_iff_of_mem_Sg hcb).not.1 hcbJ
      have hz : ∀ v : ZMod 2, ¬ v = 0 → v = 1 := by decide
      exact hz _ h
    rw [tr_cent2 e He42P427H.abar cb, card_tr]
    exact He42P427H.card_cent_le hcb hcc' hcm
  exact ⟨hfus, hzZ, hzm, hz2, hL, hLodd, hLcard, hSp, hfour, hS, hS3⟩


theorem he42Input427_holds
    (h422 : ∀ (hF6 : L52.F6Model) (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
        IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ (S : Setting G z e) (h1
        : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) (a
        x : G) (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1) (hxN : x ∈ normalizer
        ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) (hxa : x ∈ centralizer ({a} : Set G))
        (hx3 : orderOf x = 3) (y₁ y₂ : G), He42.YSpec (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN
        hxa hx3) y₁ y₂ → He42.Open422 (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3) y₁
        y₂) : He42Input427 := by
  intro hF6 G _ _ z e hs hK S h1 h2 a x ha ham hxN hxa hx3
  intro c hc
  exact p427_open427 (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3)
    (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3).baseFacts
    (p427_P427 h422 hF6 G z e hs hK S h1 h2 a x ha ham hxN hxa hx3) c
    (mem_centralizer_singleton_iff.1 hc)

end CFSG.Quasithin.A94
