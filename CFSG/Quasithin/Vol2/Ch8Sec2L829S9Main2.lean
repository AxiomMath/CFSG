module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNb
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNe2
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LNf
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

private theorem s9main_comm_mem_of_ρ_eq_one {G : Type} [Group G] {Λ W₀ W₁ : Subgroup G} {W : Type}
    [AddCommGroup W] [Module (ZMod 2) W] (S : SectionModule Λ W₀ W₁ W) (y : ↥Λ)
    (hy : S.ρ y = 1) (x : ↥W₁) :
    (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ ∈ W₀ := by
  have hmem : (y : G) * x * (y : G)⁻¹ * (x : G)⁻¹ ∈ W₁ :=
    W₁.mul_mem ((Subgroup.mem_normalizer_iff.mp (S.norm₁ y.2) x).mp x.2) (W₁.inv_mem x.2)
  have h1 := S.ρ_sub_self y x hmem
  have h2 : S.π ⟨(y : G) * x * (y : G)⁻¹ * (x : G)⁻¹, hmem⟩ = 1 := by
    have h4 : (show W from Additive.ofMul (S.π ⟨(y : G) * x * (y : G)⁻¹ * (x : G)⁻¹, hmem⟩)) =
        S.ρ y (Additive.ofMul (S.π x)) - (show W from Additive.ofMul (S.π x)) := h1.symm
    have h3 : (show W from Additive.ofMul (S.π ⟨(y : G) * x * (y : G)⁻¹ * (x : G)⁻¹, hmem⟩)) =
        (0 : W) := by
      rw [h4, hy]
      exact sub_self _
    exact Additive.ofMul.injective (h3.trans rfl)
  exact (S.ker _).mp h2

theorem s9main_config {G : Type} [Group G] [Finite G] {Lu H K T V U B B₁ : Subgroup G}
    (hchar : QuasithinUnique.CharTwo (Lu ⊔ H))
    (hHLu : H ≤ Subgroup.normalizer (Lu : Set G))
    (hTH : T ≤ H)
    (hHG : H ≤ conjClosure V H ⊔ T)
    (hR₀T : pCoreOf 2 (Lu ⊔ H) ≤ T)
    (hVT : V ≤ T) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hVc : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hVsq : ∀ v ∈ V, v * v = 1)
    (hLuV : Lu ≤ Subgroup.normalizer (V : Set G)) (hVLuB : ⁅V, Lu⁆ ≤ B)
    (hΛU : Lu ⊔ H ≤ Subgroup.normalizer (U : Set G))
    (hLuB : Lu ≤ Subgroup.normalizer (B : Set G))
    (hLuB₁ : Lu ≤ Subgroup.normalizer (B₁ : Set G))
    (hUB₁ : U ≤ B₁) (hB₁B : B₁ ≤ B) (hBV : B ≤ V)
    (hVR : V ⊓ pCoreOf 2 (Lu ⊔ H) ≤ B)
    (hirr : ∀ C : Subgroup G, U ≤ C → C ≤ B₁ → Lu ≤ Subgroup.normalizer (C : Set G) →
      C = U ∨ C = B₁)
    (hlt : U < B₁) (hcard : Nat.card ↥B₁ = 16 * Nat.card ↥U)
    (hnonab : ∃ x ∈ Lu, ∃ y ∈ Lu, ∃ b ∈ B₁, ⁅⁅x, y⁆, b⁆ ∉ U)
    (hBdim : Nat.card ↥B ≤ 2 * Nat.card ↥B₁)
    (hKH : K ≤ H) (hKG : K ≤ conjClosure V H) (hKnot2 : ¬ IsPGroup 2 ↥K)
    (hKU : K ≤ Subgroup.centralizer (U : Set G)) (hKsub : IsSubnormal K H) :
    ∃ (W₀ W₁ : Subgroup G) (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (SW : SectionModule (Lu ⊔ H) W₀ W₁ W),
      TransvConfig (SW.img Lu) (SW.img (conjClosure V H)) (SW.img T) (SW.img V)
        (SW.sub (V ⊓ W₁)) ∧ SW.img K ≠ ⊥ := by
  have hHΛ : H ≤ Lu ⊔ H := le_sup_right
  have hLuΛ : Lu ≤ Lu ⊔ H := le_sup_left
  have hKΛ : K ≤ Lu ⊔ H := hKH.trans hHΛ
  obtain ⟨y, W₀, W₁, hyK, -, hlt01, hW₁R, h0, h1, hchief, hy⟩ :=
    exists_chief_factor_odd hKΛ hchar hKnot2
  have hW₁2 : IsPGroup 2 ↥W₁ :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (Lu ⊔ H)).to_le hW₁R
  obtain ⟨hab, hsq⟩ := chief_section_elemAb hlt01 hW₁2 h0 h1 hchief
  obtain ⟨W, hWa, hWm, hWf, ⟨SW⟩⟩ := exists_sectionModule hlt01.le h0 h1 hab hsq
  obtain ⟨hnt, hirr'⟩ := SW.irreducible_of_chief hlt01 hchief
  have hVp2 : IsPGroup 2 ↥V := fun g => ⟨1, by
    apply Subtype.ext
    have := hVsq g.1 g.2
    simpa [pow_two] using this⟩
  have hVLu : ⁅V, Lu⁆ ≤ pCoreOf 2 Lu := by
    have h1' : ⁅V, Lu⁆ ≤ V ⊓ Lu := by
      rw [Subgroup.commutator_le]
      intro v hv l hl
      refine ⟨hBV (hVLuB (Subgroup.commutator_mem_commutator hv hl)), ?_⟩
      have h3 : v * l * v⁻¹ ∈ Lu :=
        (Subgroup.mem_normalizer_iff.mp (hHLu (hTH (hVT hv))) l).mp hl
      have e : ⁅v, l⁆ = (v * l * v⁻¹) * l⁻¹ := rfl
      rw [e]
      exact Lu.mul_mem h3 (Lu.inv_mem hl)
    have h2' : Lu ≤ Subgroup.normalizer ((V ⊓ Lu : Subgroup G) : Set G) :=
      (le_inf hLuV Subgroup.le_normalizer).trans Subgroup.inf_normalizer_le_normalizer_inf
    exact h1'.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right h2'
      (hVp2.to_le inf_le_left))
  have hΛN : Lu ⊔ H ≤ Subgroup.normalizer (Lu : Set G) := sup_le Subgroup.le_normalizer hHLu
  have hQ : ∀ q ∈ pCoreOf 2 Lu, ∀ x ∈ W₁, q * x * q⁻¹ * x⁻¹ ∈ W₀ := by
    intro q hq x hx
    refine chief_normal_two_trivial hlt01 hW₁2 h0 h1 hchief (Q := pCoreOf 2 Lu) ?_ ?_ ?_ x hx q hq
    · exact (Subgroup.map_subtype_le _).trans hLuΛ
    · exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Lu
    · intro y' hy' q' hq'
      have := CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Lu (hΛN hy')
      exact (Subgroup.mem_normalizer_iff.mp this q').mp hq'
  have hW₁V : W₁ ≤ Subgroup.normalizer (V : Set G) := hW₁R.trans (hR₀T.trans hTV)
  have hρy : SW.ρ ⟨y, hKΛ hyK⟩ ≠ 1 := by
    intro h1'
    apply hy
    rw [Subgroup.commutator_le]
    intro x hx g hg
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
    have hn : SW.ρ (⟨y, hKΛ hyK⟩ ^ n) = 1 := by
      rw [map_zpow, h1', one_zpow]
    have h5 := s9main_comm_mem_of_ρ_eq_one SW _ hn ⟨x, hx⟩
    have e : ⁅x, y ^ n⁆ = (y ^ n * x * (y ^ n)⁻¹ * x⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact W₀.inv_mem (by simpa using h5)
  have hKΛ' : ∀ k ∈ K, k ∈ Lu ⊔ H := fun k hk => hKΛ hk
  have hUW : U ⊓ W₁ ≤ W₀ := by
    by_contra hnot
    have hC : ∀ z : ↥(Lu ⊔ H), ∀ c ∈ U ⊓ W₁, (z : G) * c * (z : G)⁻¹ ∈ U ⊓ W₁ := by
      intro z c hc
      exact ⟨(Subgroup.mem_normalizer_iff.mp (hΛU z.2) c).mp hc.1,
        (Subgroup.mem_normalizer_iff.mp (SW.norm₁ z.2) c).mp hc.2⟩
    rcases hirr' (SW.sub (U ⊓ W₁)) (fun z w hw => SW.sub_inv (U ⊓ W₁) z (hC z) w hw) with hP | hP
    · apply hnot
      intro x hx
      have hxW : x ∈ W₁ := hx.2
      have hmem := SW.mem_sub_of_mem (C := U ⊓ W₁) (x := ⟨x, hxW⟩) hx
      rw [hP] at hmem
      have h2 : SW.π ⟨x, hxW⟩ = 1 := by
        have : (show W from Additive.ofMul (SW.π ⟨x, hxW⟩)) = 0 :=
          (Submodule.mem_bot (ZMod 2)).mp hmem
        exact Additive.ofMul.injective (this.trans rfl)
      exact (SW.ker _).mp h2
    · apply hρy
      refine LinearEquiv.ext fun w => ?_
      have hw : w ∈ SW.sub (U ⊓ W₁) := by rw [hP]; trivial
      obtain ⟨x, hxC, hxw⟩ := (SW.mem_sub).mp hw
      have hcomm : (x : G) * y = y * (x : G) := (Subgroup.mem_centralizer_iff.mp (hKU hyK)) x hxC.1
      have hx' : y * (x : G) * y⁻¹ ∈ W₁ := by
        rw [show y * (x : G) * y⁻¹ = x by rw [← hcomm]; group]
        exact x.2
      have hxeq : (⟨y * (x : G) * y⁻¹, hx'⟩ : ↥W₁) = x :=
        Subtype.ext (by
          show y * (x : G) * y⁻¹ = x
          rw [← hcomm]
          group)
      have hact := SW.act ⟨y, hKΛ hyK⟩ x hx'
      rw [← hxw]
      exact hact.trans (congrArg (fun a : ↥W₁ => Additive.ofMul (SW.π a)) hxeq)
  have hVne : ∃ v ∈ V, ¬ ∀ x ∈ W₁, v * x * v⁻¹ * x⁻¹ ∈ W₀ := by
    by_contra hno
    push Not at hno
    have hVone : ∀ v : ↥(Lu ⊔ H), (v : G) ∈ V → SW.ρ v = 1 := fun v hv =>
      SW.ρ_eq_one v (fun x => hno v hv x x.2)
    let Z : Subgroup G := (SW.ρ.ker).map (Lu ⊔ H).subtype
    have hcc : conjClosure V H ≤ Z := by
      refine conjClosure_le (fun x hx z hz => ?_)
      have hmemH : x * z * x⁻¹ ∈ H := H.mul_mem (H.mul_mem hx (hTH (hVT hz))) (H.inv_mem hx)
      refine Subgroup.mem_map.mpr ⟨⟨x * z * x⁻¹, hHΛ hmemH⟩, ?_, rfl⟩
      have hxΛ : x ∈ Lu ⊔ H := hHΛ hx
      have hzΛ : z ∈ Lu ⊔ H := hHΛ (hTH (hVT hz))
      have e : (⟨x * z * x⁻¹, hHΛ hmemH⟩ : ↥(Lu ⊔ H)) =
          ⟨x, hxΛ⟩ * ⟨z, hzΛ⟩ * ⟨x, hxΛ⟩⁻¹ := rfl
      rw [MonoidHom.mem_ker, e, map_mul, map_mul, map_inv, hVone ⟨z, hzΛ⟩ hz]
      simp
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp (hcc (hKG hyK))
    apply hρy
    have : z = ⟨y, hKΛ hyK⟩ := Subtype.ext hzy
    rw [← this]
    exact hz
  have hVR' : V ⊓ W₁ ≤ B := fun x hx => hVR ⟨hx.1, hW₁R hx.2⟩
  have hLuU : Lu ≤ Subgroup.normalizer (U : Set G) := hLuΛ.trans hΛU
  have hb := hb_group SW hLuΛ hVc hVsq hLuV hLuU hLuB₁ hLuB hUB₁ hB₁B hBV hirr hlt hcard hnonab
    hBdim hUW hVR'
  have hcfg := config_of_data (Λ := Lu ⊔ H) SW hnt hirr' hLuΛ hHΛ le_rfl hTH hHLu hHG hVT hTV
    hVsq hVLu hQ hW₁V hVne hb
  refine ⟨W₀, W₁, W, hWa, hWm, hWf, SW, hcfg, ?_⟩
  intro hbot
  apply hρy
  have hmem : SW.ρ ⟨y, hKΛ hyK⟩ ∈ SW.img K := (SW.mem_img).mpr ⟨⟨y, hKΛ hyK⟩, hyK, rfl⟩
  rw [hbot] at hmem
  simpa using hmem

end CFSG.Quasithin.H13.L829N
