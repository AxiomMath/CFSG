module

public import CFSG.Quasithin.Vol2.Asc94.He42Top
public import CFSG.Quasithin.Vol2.Asc94.He42SE4
public import CFSG.Quasithin.Vol2.Asc94.He42SE5
public import CFSG.Quasithin.Vol2.Asc94.He42SE6
public import CFSG.Quasithin.Vol2.Asc94.He42SE7

public section

namespace CFSG.Quasithin.A94

open Subgroup CFSG.CGT.M24S CFSG.Open CFSG.Blueprint
open CFSG.ABGLocalTools CFSG.ComponentClassification.AschbacherTightEmbedding
open CFSG.ComponentClassification.RankTwoStandard CFSG.ComponentClassification.AS81

private theorem he42s8_gl2_not_comm_e12 : ∀ g : HeJ.GL2, g ^ 3 = 1 → g ≠ 1 →
    (g : HeJ.M2) * Matrix.of ![![0, 1], ![0, 0]] ≠ Matrix.of ![![0, 1], ![0, 0]] * (g : HeJ.M2) := by
  decide +kernel

private theorem he42s8_cent_le_L {G : Type} [Group G] [Finite G] {z : G}
    (T : He42.HeSetup G) (hB : T.BaseFacts) (hP : T.StepPsi)
    (hmain : Subgroup.center ↥T.L = T.B.subgroupOf T.L ∧
      CFSG.ComponentClassification.AS81.TypeL34
        (CFSG.ComponentClassification.RankTwoStandard.rankTwoQuot T.L))
    (hfus : T.StepFus) (hzZ : z ∈ T.Z) (hzB : z ∉ T.B)
    (hzm : T.m z = Matrix.of ![![0, 1], ![0, 0]]) (hz2 : z * z = 1)
    (hPz : IsPGroup 2 ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (T.B : Set G))) :
    ∀ c : G, (∀ b ∈ T.B, c * b = b * c) → c ∈ T.L := by
  have hcent : ∀ c : G, (∀ b ∈ T.B, c * b = b * c) → c * z * c⁻¹ * z⁻¹ ∈ T.B → c ∈ T.L := by
    intro c hcB hc
    have hczc : c * z * c⁻¹ = z := T.fix_of_centralizes_B hB hfus hzZ hzm hcB hc
    have hcz : c * z = z * c := by
      calc c * z = c * z * c⁻¹ * c := by group
        _ = z * c := by rw [hczc]
    have hcJ : c ∈ T.J := T.le_J_of_isPGroup hB hzZ hPz hcz hcB
    have hcL1 : c ∈ T.L1 := hB.K_le_L1 (hB.J_le_K hcJ)
    show c ∈ T.L1 ⊔ T.L2
    exact Subgroup.mem_sup_left hcL1
  exact T.centralizer_le_L hB hP hmain hzZ hzB hz2 hcent

variable {G : Type} [Group G] [Finite G] {z : G}
  (e : ↥(Cz z) ≃* L52.Hc) (hF6 : L52.F6Model) (S : Setting G z e)
  (h1 : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z)
  {a x : G} (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1)
  (hxN : x ∈ normalizer ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G))
  (hxa : x ∈ centralizer ({a} : Set G)) (hx3 : orderOf x = 3)

include hF6 S h1 h2 ha ham hxN hxa hx3 in
theorem isPGroup_cent_z_B :
    IsPGroup 2 ↥(centralizer ({z} : Set G) ⊓ centralizer ((HeB e x : Subgroup G) : Set G)) := by
  have hD := HeJ.data40 e hF6 S h1 h2 ha ham
  obtain ⟨b, hbB, hbm⟩ := hD.exists_b hxN hxa hx3
  obtain ⟨hbZ, -⟩ := Subgroup.mem_inf.1 hbB
  obtain ⟨y, rfl⟩ := exists_emb e (tr_le_Cz e L52.A1 (Subgroup.mem_inf.1 hbZ).1)
  rw [HeJ.mG_emb] at hbm
  have hg3 := hD.g_pow_three hxN hxa hx3
  have hg1 := hD.g_ne_one hxN hxa hx3
  have hy1 : L52.zC y 1 0 = 1 := by
    rw [hbm]
    exact He42SE.gl2_order3_entry _ hg3 hg1
  have hy2 : y * y = 1 := by
    apply emb_injective e
    rw [map_mul, map_one]
    exact hD.hK.Asq _ (Subgroup.mem_inf.1 hbZ).1
  have hP : IsPGroup 2 (Subgroup.centralizer ({y} : Set L52.Hc)) :=
    He42SE.isPGroup_centralizer_of_piHom_ne_one (He42SE.piHom_ne_one_of_zC hy1) hy2
  have hle : centralizer ({z} : Set G) ⊓ centralizer ((HeB e x : Subgroup G) : Set G) ≤
      (Subgroup.centralizer ({y} : Set L52.Hc)).map (emb e) := by
    intro c hc
    obtain ⟨hcz, hcB⟩ := Subgroup.mem_inf.1 hc
    obtain ⟨y', hy'⟩ := exists_emb e hcz
    refine Subgroup.mem_map.2 ⟨y', ?_, hy'⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hbc : emb e y * c = c * emb e y := Subgroup.mem_centralizer_iff.1 hcB _ hbB
    rw [← hy'] at hbc
    exact ((emb_mul_comm e).1 hbc).symm
  exact (hP.map (emb e)).to_le hle

theorem z_facts_426 :
    z ∈ (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3).Z ∧
      z ∉ (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3).B ∧
      (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3).m z =
        Matrix.of ![![0, 1], ![0, 0]] := by
  have hD := HeJ.data40 e hF6 S h1 h2 ha ham
  have hzZ : z ∈ tr e L52.A1 ⊓ tr e L52.A2 := (frame4 e S.ord hF6).z_mem_B
  have hzm : HeJ.mG e z = Matrix.of ![![0, 1], ![0, 0]] := (HeJ.mG_z e S.ord).trans L52.zC_zt
  refine ⟨hzZ, ?_, hzm⟩
  intro hzB
  have hzB' : z ∈ (tr e L52.A1 ⊓ tr e L52.A2) ⊓ centralizer ({x} : Set G) := hzB
  have h := ((hD.mem_B_iff hxN hxa hx3).1 hzB').2
  rw [hzm] at h
  exact he42s8_gl2_not_comm_e12 _ (hD.g_pow_three hxN hxa hx3) (hD.g_ne_one hxN hxa hx3) h

theorem he42Input426_of_422
    (h422 : ∀ (hF6 : L52.F6Model) (G : Type) [Group G] [Finite G] (z : G) (e : ↥(Cz z) ≃* L52.Hc),
        IsSimpleGroup G → CFSG.Assembly.KProper CFSG.Blueprint.Catalog G → ∀ (S : Setting G z e) (h1
        : normalizer (tr e L52.U1 : Set G) = Cz z) (h2 : normalizer (tr e L52.U2 : Set G) = Cz z) (a
        x : G) (ha : a ∈ tr e L52.A1 ⊓ tr e L52.A2) (ham : HeJ.mG e a = 1) (hxN : x ∈ normalizer
        ((tr e L52.A1 ⊔ tr e L52.A2 : Subgroup G) : Set G)) (hxa : x ∈ centralizer ({a} : Set G))
        (hx3 : orderOf x = 3) (y₁ y₂ : G), He42.YSpec (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN
        hxa hx3) y₁ y₂ → He42.Open422 (He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3) y₁
        y₂) : He42Input426 := by
  intro hF6 G _ _ z e hs hK S h1 h2 a x ha ham hxN hxa hx3
  set T := He42.HeSetup.ofCtx e hF6 S h1 h2 ha ham hxN hxa hx3
  have hfus : T.StepFus := by
    intro y hy y' hy' g hg
    exact (frame2 e S.ord hF6).fusion_B (a := y) (b := y') hy hy' hg
  obtain ⟨hzZ, hzB, hzm⟩ : z ∈ T.Z ∧ z ∉ T.B ∧ T.m z = Matrix.of ![![0, 1], ![0, 0]] :=
    z_facts_426 e hF6 S h1 h2 ha ham hxN hxa hx3
  have hz2 : z * z = 1 := by
    have h := pow_orderOf_eq_one z
    rw [S.ord, pow_two] at h
    exact h
  have hPz : IsPGroup 2 ↥(Subgroup.centralizer ({z} : Set G) ⊓ Subgroup.centralizer (T.B : Set G)) :=
    isPGroup_cent_z_B e hF6 S h1 h2 ha ham hxN hxa hx3
  have hB := T.baseFacts
  have hP := T.stepPsi hB
  have hmain := T.typeL34_main
    (fun y₁ y₂ hY => h422 hF6 G z e hs hK S h1 h2 a x ha ham hxN hxa hx3 y₁ y₂ hY)
  have key := he42s8_cent_le_L T hB hP hmain hfus hzZ hzB hzm hz2 hPz
  intro c hc
  exact key c (fun b hb => (Subgroup.mem_centralizer_iff.1 hc b hb).symm)

end CFSG.Quasithin.A94
