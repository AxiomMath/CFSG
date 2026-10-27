module

public import CFSG.RankThree.GF2n.Smith81.LinOddSteps
public import CFSG.ClassicalGroups.SpecialLinear.Transitive
public import CFSG.RankThree.GF2n.Smith81.LinStmt

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z : Subgroup G}

theorem exists_comm_eq (H : StrothHyp M Q Z) {v : G} (hvQ : v ∈ Q) (hvZ : v ∉ Z) {z : G}
    (hz : z ∈ Z) : ∃ w ∈ Q, ⁅w, v⁆ = z := by
  obtain ⟨K, hK, hfin, hch, γ, M₀, hD⟩ := stroth_globalModelData H
  have hπv : M₀.π v ≠ 0 := fun h => hvZ ((M₀.π_ker v hvQ).mp h)
  obtain ⟨f, hf⟩ : ∃ f, M₀.B (M₀.π v) f ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hπv (M₀.nondeg _ hcon)
  obtain ⟨u, hu, hπu⟩ := M₀.π_surj ((γ z / M₀.B (M₀.π v) f) • f)
  have hγ : γ ⁅v, u⁆ = γ z := by
    rw [M₀.comm_eq v hvQ u hu, hπu, map_smul, smul_eq_mul]
    field_simp
  have hc : ⁅v, u⁆ ∈ Z := comm_mem_Z H hvQ hu
  have hz2 : z * z = 1 := by rw [← pow_two]; exact Z_sq H hz
  have h2 : γ (⁅v, u⁆ * z) = 0 := by
    rw [hD.reg.add _ hc _ hz, hγ]
    exact CharTwo.add_self_eq_zero _
  have h3 : ⁅v, u⁆ * z = 1 := hD.reg.inj _ (Z.mul_mem hc hz) h2
  have h4 : ⁅v, u⁆ = z := by
    have := eq_inv_of_mul_eq_one_left h3
    rw [this]; exact inv_eq_of_mul_eq_one_right hz2
  refine ⟨u, hu, ?_⟩
  rw [← commutatorElement_inv, h4]
  exact inv_eq_of_mul_eq_one_right hz2

theorem lin31Back_holds :
    ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
      Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n → B ≤ V₁ →
        ∀ v : G, v ≠ 1 → (v ∈ V₁ ∨ v ∈ V₂) → InZClass Z v := by
  intro G _ _ M Q Z B n V₁ V₂ hc hS hn hBV
  have H := hc.hyp
  have hn2 : 2 ≤ n := by omega
  obtain ⟨K, hK, hfin, hcard, φ, hrange, hker, hZV₁, hV₁Q, hZV₂, hV₂Q, hint, hsup,
    hs₁, hs₂, ⟨x₀, hx₀M, hx₀V⟩, hcent⟩ := hS
  obtain ⟨hN₁, hn₁, ψ, hψ⟩ := hs₁
  have hBne : B ≠ ⊥ := by
    intro h
    have h1 : Nat.card B = Nat.card Z := by
      obtain ⟨g, hg⟩ := hc.conj
      rw [hg, card_conjSubgroup]
    rw [h, Subgroup.card_bot] at h1
    have := H.q4
    omega
  obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hBne
  have hb1' : b ≠ 1 := fun h => hb1 (Subtype.ext h)
  have hbV : b ∈ V₁ := hBV hb
  have hbZ : b ∉ Z := by
    intro hbz
    have : b ∈ Z ⊓ B := ⟨hbz, hb⟩
    rw [hc.inf_eq_bot, Subgroup.mem_bot] at this
    exact hb1' this
  have hbcl : InZClass Z b := inZClass_of_mem_root hc.conj hb hb1'
  have key : ∀ v ∈ V₁, v ≠ 1 → InZClass Z v := by
    intro v hv hv1
    by_cases hvZ : v ∈ Z
    · exact ⟨1, v, hvZ, hv1, by group⟩
    have hcoord : ∀ (u : G) (hu : u ∈ V₁), u ∉ Z →
        Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨u, hu⟩)) ≠ 0 := by
      intro u hu huZ h0
      have h1 : ψ (QuotientGroup.mk ⟨u, hu⟩) = 1 := by
        apply Multiplicative.toAdd.injective
        rw [h0]; rfl
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
      exact huZ h1
    obtain ⟨A, hA, hAw⟩ := CFSG.ClassicalGroups.SpecialLinear.exists_statedSL_mulVec_eq hn2
      (hcoord b hbV hbZ) (hcoord v hv hvZ)
    obtain ⟨l, hl⟩ : A ∈ φ.range := hrange ▸ hA
    have hlb : (l : G) * b * (l : G)⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hN₁ l.2) b).mp hbV
    have hmk := hψ l ⟨b, hbV⟩ ⟨(l : G) * b * (l : G)⁻¹, hlb⟩ rfl
    have hvec : Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨(l : G) * b * (l : G)⁻¹, hlb⟩)) =
        Multiplicative.toAdd (ψ (QuotientGroup.mk ⟨v, hv⟩)) := by
      rw [hmk, ← hAw, ← hl]
    have hz₁ : v⁻¹ * ((l : G) * b * (l : G)⁻¹) ∈ Z := by
      have h2 := ψ.injective (Multiplicative.toAdd.injective hvec)
      have h3 := (QuotientGroup.eq.mp h2.symm)
      rw [Subgroup.mem_subgroupOf] at h3
      simpa using h3
    set z₁ : G := v⁻¹ * ((l : G) * b * (l : G)⁻¹) with hz₁def
    have hlbcl : InZClass Z ((l : G) * b * (l : G)⁻¹) := hbcl.conj l
    obtain ⟨w, hwQ, hw⟩ := exists_comm_eq H (hV₁Q hv) hvZ hz₁
    have hz2 : z₁ * z₁ = 1 := by rw [← pow_two]; exact Z_sq H hz₁
    have hcomm1 : (l : G) * b * (l : G)⁻¹ = v * z₁ := by rw [hz₁def]; group
    have hwz : w * z₁ * w⁻¹ = z₁ := by
      have := Z_central H hz₁ hwQ
      rw [← this]; group
    have hvz : v * z₁ = z₁ * v := Z_central H hz₁ (hV₁Q hv) |>.symm
    have hconj : w * ((l : G) * b * (l : G)⁻¹) * w⁻¹ = v := by
      rw [hcomm1]
      have e : w * (v * z₁) * w⁻¹ = (w * v * w⁻¹ * v⁻¹) * (v * (w * z₁ * w⁻¹)) := by group
      have hw' : w * v * w⁻¹ * v⁻¹ = z₁ := by rw [← commutatorElement_def]; exact hw
      rw [e, hw', hwz]
      calc z₁ * (v * z₁) = z₁ * (z₁ * v) := by rw [hvz]
        _ = (z₁ * z₁) * v := by group
        _ = v := by rw [hz2, one_mul]
    have := hlbcl.conj w
    rwa [hconj] at this
  intro v hv1 hv
  rcases hv with hv | hv
  · exact key v hv hv1
  · have hv' : x₀⁻¹ * v * x₀ ∈ V₁ := by
      have : v ∈ conjSubgroup x₀ V₁ := by rw [hx₀V]; exact hv
      exact mem_conjSubgroup.mp this
    have hne : x₀⁻¹ * v * x₀ ≠ 1 := by
      intro h
      apply hv1
      have : v = x₀ * (x₀⁻¹ * v * x₀) * x₀⁻¹ := by group
      rw [this, h]; group
    have := key _ hv' hne
    have h2 := (inZClass_conj_iff (Z := Z) (v := v) x₀⁻¹).mp (by simpa using this)
    exact h2

@[expose] def LinBInStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n → B ≤ V₁ ∨ B ≤ V₂

@[expose] def Lin31FwdStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (n : ℕ) (V₁ V₂ : Subgroup G),
    Ctx M Q Z B → LinSetup M Q Z B n V₁ V₂ → 3 ≤ n →
      ∀ v ∈ Q, v ≠ 1 → InZClass Z v → v ∈ V₁ ∨ v ∈ V₂

@[expose] def Lin31TwoStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (V₁ V₂ : Subgroup G),
    Smith1981Below (Nat.card G) → Ctx M Q Z B → LinSetup M Q Z B 2 V₁ V₂ → Lin31Prop M Q Z B 2

theorem lin31Statement_of (hBin : LinBInStatement) (hFwd : Lin31FwdStatement)
    (hTwo : Lin31TwoStatement) : Lin31Statement := by
  intro G _ _ M Q Z B n V₁ V₂ hb hc hS hn
  rcases Nat.lt_or_ge n 3 with h | h
  · have hn2 : n = 2 := by omega
    subst hn2
    exact hTwo G M Q Z B V₁ V₂ hb hc hS
  · rcases hBin G M Q Z B n V₁ V₂ hc hS h with hB | hB
    · exact ⟨V₁, V₂, hS, hB, fun v hv hv1 =>
        ⟨fun hcl => hFwd G M Q Z B n V₁ V₂ hc hS h v hv hv1 hcl,
          fun hv' => lin31Back_holds G M Q Z B n V₁ V₂ hc hS h hB v hv1 hv'⟩⟩
    · exact ⟨V₂, V₁, hS.symm, hB, fun v hv hv1 =>
        ⟨fun hcl => Or.comm.mp (hFwd G M Q Z B n V₁ V₂ hc hS h v hv hv1 hcl),
          fun hv' => lin31Back_holds G M Q Z B n V₂ V₁ hc hS.symm h hB v hv1 hv'⟩⟩

end CFSG.RankThree.GF2n.Smith81
