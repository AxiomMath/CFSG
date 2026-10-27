module

public import CFSG.Quasithin.Recognition.St84.Gen.D4qAmalModel
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.Native
public import CFSG.LocalAnalysis.EvenBN.TrialityD4.LeviCentralizers
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocWeyl
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocOrient
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qLocStd

public section

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.LocalAnalysis.EvenBN.TrialityD4 CFSG.Quasithin.H13.F431.D4q
  CFSG.Quasithin.H13.F431.D4q.Struct CFSG.Quasithin.H13.F431.D4q.Loc CFSG.Quasithin.H13.F431.D4q.NFq
  CFSG.Quasithin.H13.F431.D4q.Hex CFSG.Quasithin.H13.Sec53F.Yam
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.D4 CFSG.ComponentClassification.RankTwoExceptional.D4
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

noncomputable def d4ModelData {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) : TrialityD4Data (Struct.Cm σ) (2 ^ f) :=
  letI : CharP K 2 := CFSG.Quasithin.H13.F431.D4q.NFq.charP_two_of_std hf hK
  modelData hf K σ (RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσ c) hσ hK
    (CFSG.Quasithin.H13.F431.D4q.NFq.card_d4k σ hf hK hσ)

theorem d4ModelData_S {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) : (d4ModelData σ hf hK hσ).S = Struct.Ust σ := by
  haveI : CharP K 2 := CFSG.Quasithin.H13.F431.D4q.NFq.charP_two_of_std hf hK
  exact Model.sixClosure_eq σ (RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσ c)

theorem d4ModelData_V_eq_ZC {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) : (d4ModelData σ hf hK hσ).V = Loc.ZC σ := by
  haveI : CharP K 2 := CFSG.Quasithin.H13.F431.D4q.NFq.charP_two_of_std hf hK
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  let d := d4ModelData σ hf hK hσ
  have hZC : Nat.card (Loc.ZC σ) = 2 ^ f := by
    have hle : d4Zz K σ ≤ graphFixedRootGroup TwistTag.D4 K σ.toRingHom :=
      (NFq.Zg_le_Qg σ (CFSG.Quasithin.H13.F431.D4q.NFq.sigma_cube σ hK hσ)).trans
        ((graphFixedSimpleComplement_le _).trans
          (graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _))
    rw [Loc.ZC, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact NFq.card_Zg σ hf hK hσ
  refine Subgroup.eq_of_le_of_card_ge ?_ ?_
  · intro x hx
    change (x : ModGL TwistTag.D4.tag K) ∈ d4Zz K σ
    obtain ⟨a, rfl⟩ : ∃ a : fixedSubfield σ, d.x₆ a = x := hx
    exact Subgroup.subset_closure (Set.mem_range_self a)
  · rw [d.card_V, hZC]

theorem Pst0_le_normalizer_d4ModelData_V {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Struct.Pst0 σ ≤
      Subgroup.normalizer (((d4ModelData σ hf hK hσ).V : Subgroup (Struct.Cm σ)) :
        Set (Struct.Cm σ)) := by
  haveI : CharP K 2 := CFSG.Quasithin.H13.F431.D4q.NFq.charP_two_of_std hf hK
  let d := d4ModelData σ hf hK hσ
  have hV : d.V = Loc.ZC σ := d4ModelData_V_eq_ZC σ hf hK hσ
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [hV]
  change (x : ModGL TwistTag.D4.tag K) ∈ d4Zz K σ ↔
    ((p * x * p⁻¹ : Struct.Cm σ) : ModGL TwistTag.D4.tag K) ∈ d4Zz K σ
  constructor
  · exact fun hx => Pst0_conj_Zg σ (CFSG.Quasithin.H13.F431.D4q.NFq.sigma_cube σ hK hσ) hp hx
  · intro hx
    have hp' : p⁻¹ ∈ Struct.Pst0 σ := inv_mem hp
    have h := Pst0_conj_Zg σ (CFSG.Quasithin.H13.F431.D4q.NFq.sigma_cube σ hK hσ) hp' hx
    have h' : ((p⁻¹ : Struct.Cm σ) : ModGL TwistTag.D4.tag K) *
        (((p * x * p⁻¹ : Struct.Cm σ)) : ModGL TwistTag.D4.tag K) *
          (((p⁻¹ : Struct.Cm σ) : ModGL TwistTag.D4.tag K))⁻¹ =
        (x : ModGL TwistTag.D4.tag K) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
      group
    rwa [h'] at h

theorem normalizer_d4ModelData_V {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Subgroup.normalizer (((d4ModelData σ hf hK hσ).V : Subgroup (Struct.Cm σ)) :
      Set (Struct.Cm σ)) = Struct.Pst0 σ := by
  let d := d4ModelData σ hf hK hσ
  have hS := d4_yamStd σ hf hK (fun c => hσ c)
  have hle := Pst0_le_normalizer_d4ModelData_V σ hf hK hσ
  have hVne : d.V ≠ ⊥ := by
    intro hbot
    have hc := d.card_V
    rw [hbot, Subgroup.card_bot] at hc
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    omega
  have hV2 : IsPGroup 2 d.V := IsPGroup.of_card (n := f) d.card_V
  have hne : Subgroup.normalizer (d.V : Set (Struct.Cm σ)) ≠ ⊤ := by
    intro htop
    exact hVne (hS.no_normal d.V (Subgroup.normalizer_eq_top_iff.mp htop) hV2)
  rcases hS.coatom₀.le_iff.mp hle with htop | heq
  · exact absurd htop hne
  · exact heq

theorem d4ModelData_M {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    (d4ModelData σ hf hK hσ).M = pCoreOf 2 (Struct.Pst1 σ) := by
  haveI : CharP K 2 := CFSG.Quasithin.H13.F431.D4q.NFq.charP_two_of_std hf hK
  haveI : Finite (ModGL TwistTag.D4.tag K) := finite_modGL
  have hσ3 : σ.toRingHom ^ 3 = 1 :=
    RingHom.ext fun c => ringEquiv_cube_apply_eq hK hσ c
  let d := d4ModelData σ hf hK hσ
  have h1 : d.U₁ ≤ pCoreOf 2 (Struct.Pst1 σ) := by
    intro x hx
    obtain ⟨a, rfl⟩ : ∃ a : K, d.x₁ a = x := hx
    rw [pCoreOf_Pst1 σ, Subgroup.mem_subgroupOf]
    exact ox₁_mem_Q1 σ hσ3 a
  have h3 : d.U₃ ≤ pCoreOf 2 (Struct.Pst1 σ) := by
    intro x hx
    obtain ⟨a, rfl⟩ : ∃ a : K, d.x₃ a = x := hx
    rw [pCoreOf_Pst1 σ, Subgroup.mem_subgroupOf]
    exact ox₃_mem_Q1 σ hσ3 a
  have h4 : d.U₄ ≤ pCoreOf 2 (Struct.Pst1 σ) := by
    intro x hx
    obtain ⟨a, rfl⟩ : ∃ a : K, d.x₄ a = x := hx
    rw [pCoreOf_Pst1 σ, Subgroup.mem_subgroupOf]
    exact ox₄_mem_Q1 σ hσ3 a
  have h5 : d.U₅ ≤ pCoreOf 2 (Struct.Pst1 σ) := by
    intro x hx
    obtain ⟨a, rfl⟩ : ∃ a : fixedSubfield σ, d.x₅ a = x := hx
    rw [pCoreOf_Pst1 σ, Subgroup.mem_subgroupOf]
    exact ox₅_mem_Q1 σ hσ3 a
  have h6 : d.U₆ ≤ pCoreOf 2 (Struct.Pst1 σ) := by
    intro x hx
    obtain ⟨a, rfl⟩ : ∃ a : fixedSubfield σ, d.x₆ a = x := hx
    rw [pCoreOf_Pst1 σ, Subgroup.mem_subgroupOf]
    exact ox₆_mem_Q1 σ hσ3 a
  have hle : d.M ≤ pCoreOf 2 (Struct.Pst1 σ) := by
    have hM : d.M = d.U₁ ⊔ (d.U₃ ⊔ (d.U₄ ⊔ (d.U₅ ⊔ d.U₆))) := rfl
    rw [hM]
    exact sup_le h1 (sup_le h3 (sup_le h4 (sup_le h5 h6)))
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  rw [card_pCoreOf_Pst1 σ hf hK hσ, d.card_M, ← pow_mul, Nat.mul_comm f 11]

theorem normalizer_d4ModelData_Y {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ (2 ^ f)) :
    Subgroup.normalizer (((d4ModelData σ hf hK hσ).Y : Subgroup (Struct.Cm σ)) :
      Set (Struct.Cm σ)) = Struct.Pst1 σ := by
  let d := d4ModelData σ hf hK hσ
  have hS := d4_yamStd σ hf hK (fun c => hσ c)
  have hMY : Subgroup.normalizer (d.M : Set (Struct.Cm σ)) =
      Subgroup.normalizer (d.Y : Set (Struct.Cm σ)) :=
    d.normalizer_Y_eq_normalizer_W_and_M.2.symm
  have hle : Struct.Pst1 σ ≤ Subgroup.normalizer (d.Y : Set (Struct.Cm σ)) := by
    rw [← hMY, d4ModelData_M σ hf hK hσ]
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Struct.Pst1 σ)
  have hYne : d.Y ≠ ⊥ := by
    intro hbot
    have hc := d.card_Y
    rw [hbot, Subgroup.card_bot] at hc
    have hq : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    have h2 : 1 < (2 ^ f) ^ 2 := by nlinarith
    omega
  have hY2 : IsPGroup 2 d.Y := IsPGroup.of_card (n := 2 * f) (by
    rw [d.card_Y, ← pow_mul, Nat.mul_comm f 2])
  have hne : Subgroup.normalizer (d.Y : Set (Struct.Cm σ)) ≠ ⊤ := by
    intro htop
    exact hYne (hS.no_normal d.Y (Subgroup.normalizer_eq_top_iff.mp htop) hY2)
  rcases hS.coatom₁.le_iff.mp hle with htop | heq
  · exact absurd htop hne
  · exact heq

end CFSG.Quasithin.F112R.St84

end
