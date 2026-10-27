module

public import CFSG.RankThree.GF2n.Smith81.OrthAct
public import CFSG.RankThree.GF2n.Smith81.OrthCount
public import CFSG.RankThree.GF2n.Smith81.OrthLane

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80

@[expose] def Smith24ActStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ),
      GlobalModelData M Q Z γ M₀ ∧ ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι)
        (qU : QuadraticForm K (ι → K)) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))

@[expose] def Smith52ActStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), SmithOrthCfg M Q Z B →
    ∀ (K : Type) [Field K] [Finite K] [CharP K 2] (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ →
      ∀ (ι : Type) [Fintype ι] [DecidableEq ι]
      (qU : QuadraticForm K (ι → K)) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
      OrthFrame Q Z M₀ qU φ → OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) →
      ∀ A : Subgroup G, IsZConjugate Z A → A ≤ Q → A ≠ Z →
      ∀ (c₁ c₂ : K) (u : ι → K), (c₁ ≠ 0 ∨ c₂ ≠ 0) → u ≠ 0 → qU u = 0 →
        (∃ a ∈ A, a ≠ 1 ∧ φ (M₀.π a) = (c₁ • u, c₂ • u)) →
        (∀ v ∈ Q ⊓ QB A, ∃ (w : ι → K) (s t : K), QuadraticMap.polar qU w u = 0 ∧
          φ (M₀.π v) = (c₁ • w + s • u, c₂ • w + t • u)) ∧
        (∀ (w : ι → K) (s t : K), QuadraticMap.polar qU w u = 0 →
          ∃ v ∈ Q ⊓ QB A, φ (M₀.π v) = (c₁ • w + s • u, c₂ • w + t • u))

variable {G : Type} [Group G] [Finite G]

theorem smith216OrthCount_of_52Act (h24 : Smith24ActStatement) (h52 : Smith52ActStatement) :
    Smith216OrthCountStatement := by
  intro G _ _ M Q Z B hc z hz hz1 A C hA hC hAC hCA
  obtain ⟨K, _, _, _, γ, M₀, hD, ι, _, _, qU, φ, hF, hAct⟩ := h24 G M Q Z B hc
  have H := hc.ctx.hyp
  obtain ⟨g, hgA, hgQ, -⟩ := hA.QB_eq H
  have hCeq : C = conjSubgroup g (conjSubgroup g⁻¹ C) := (Sec117.conj_conj_inv g C).symm
  set B' := conjSubgroup g⁻¹ C with hB'
  have hB'conj : IsZConjugate Z B' := hC.conj g⁻¹
  have hB'Q : B' ≤ Q := by
    intro y hy
    have h1 : g * y * g⁻¹ ∈ conjSubgroup g Q := by
      rw [← hgQ]
      apply hCA
      have := mem_conjSubgroup.mp hy
      simpa using this
    have h2 := mem_conjSubgroup.mp h1
    simpa [mul_assoc] using h2
  have hB'Z : B' ≠ Z := by
    intro h
    apply hAC
    rw [hgA, hCeq, h]
  have hB'ne : B' ≠ ⊥ := by
    intro h
    have h1 := hB'conj.card_eq
    rw [h, Subgroup.card_bot] at h1
    have h4 := H.q4
    omega
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB'ne
  have haB' : (a : G) ∈ B' := a.2
  have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
  have haQ : (a : G) ∈ Q := hB'Q haB'
  obtain ⟨h, hh⟩ := hB'conj
  have haZ : (a : G) ∉ Z := by
    intro haZ
    have hne : conjSubgroup h Z ≠ Z := fun e => hB'Z (hh.trans e)
    have hbot := inf_conjSubgroup_eq_bot_of_isTI H.ti hne
    have hmem : (a : G) ∈ Z ⊓ conjSubgroup h Z := ⟨haZ, hh ▸ haB'⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact ha1' hmem
  have hconj_a : IsConj z (a : G) := by
    have hz' : h⁻¹ * (a : G) * h ∈ Z := mem_conjSubgroup.mp (hh ▸ haB')
    have hz1' : h⁻¹ * (a : G) * h ≠ 1 := by
      intro h1
      apply ha1'
      have : (a : G) = h * (h⁻¹ * (a : G) * h) * h⁻¹ := by group
      rw [this, h1]
      group
    obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hz' hz1'
    refine isConj_iff.mpr ⟨h * m, ?_⟩
    calc h * m * z * (h * m)⁻¹ = h * (m * z * m⁻¹) * h⁻¹ := by group
      _ = (a : G) := by rw [hm]; group
  obtain ⟨c₁, c₂, u, hc12, hu0, hqu, hpa⟩ := (hF.root z hz hz1 a haQ haZ).mp hconj_a
  have hB'' : IsZConjugate Z B' := ⟨h, hh⟩
  obtain ⟨-, hconv⟩ := h52 G M Q Z B hc K γ M₀ hD ι qU φ hF hAct B' hB'' hB'Q hB'Z c₁ c₂ u hc12
    hu0 hqu ⟨a, haB', ha1', hpa⟩
  have hZQB : Z ≤ QB B' :=
    (hB''.le_QB_iff H (IsZConjugate.self Z)).mpr (by rw [H.QB_Z]; exact hB'Q)
  have hSQ : Q ⊓ QB B' ≤ Q := inf_le_left
  have hZS : Z ≤ Q ⊓ QB B' := le_inf H.Z_normal.1 hZQB
  let T : Set M₀.E := {e | ∃ s t : K, φ e = (s • u, t • u)}
  have h0 : (0 : M₀.E) ∈ T := ⟨0, 0, by rw [map_zero, zero_smul]; rfl⟩
  have hadd : ∀ a ∈ T, ∀ b ∈ T, a + b ∈ T := by
    rintro e ⟨s, t, he⟩ e' ⟨s', t', he'⟩
    refine ⟨s + s', t + t', ?_⟩
    rw [map_add, he, he']
    simp [add_smul]
  have hneg : ∀ a ∈ T, -a ∈ T := by
    rintro e ⟨s, t, he⟩
    refine ⟨-s, -t, ?_⟩
    rw [map_neg, he]
    simp
  have hsurj : ∀ t ∈ T, ∃ v ∈ Q ⊓ QB B', M₀.π v = t := by
    rintro e ⟨s, t, he⟩
    obtain ⟨v, hv, hve⟩ := hconv 0 s t (by simp)
    refine ⟨v, hv, φ.injective ?_⟩
    rw [hve, he]
    simp
  obtain ⟨S', hS'mem, hS'card⟩ := exists_preimage_subgroup M₀ hSQ hZS T h0 hadd hneg hsurj
  have hTcard : Nat.card T = Nat.card K ^ 2 := by
    rw [← card_pairLine u hu0]
    exact Nat.card_congr (φ.toEquiv.subtypeEquiv (fun e => Iff.rfl))
  have hKZ : Nat.card K = Nat.card Z := hD.card
  refine ⟨conjSubgroup g S', ?_, ?_, ?_⟩
  ·
    intro s hs
    have hs' := (hS'mem (g⁻¹ * s * g)).mp (mem_conjSubgroup.mp hs)
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [hgQ, mem_conjSubgroup]
      exact (Subgroup.mem_inf.mp hs'.1).1
    · rw [hCeq, QB_conj, mem_conjSubgroup]
      exact (Subgroup.mem_inf.mp hs'.1).2
  ·
    intro s hs hs1
    have hs' := (hS'mem (g⁻¹ * s * g)).mp (mem_conjSubgroup.mp hs)
    have hs0Q : g⁻¹ * s * g ∈ Q := (Subgroup.mem_inf.mp hs'.1).1
    have hs01 : g⁻¹ * s * g ≠ 1 := by
      intro h1
      apply hs1
      have : s = g * (g⁻¹ * s * g) * g⁻¹ := by group
      rw [this, h1]
      group
    have hroot : IsConj z (g⁻¹ * s * g) := by
      by_cases hZm : g⁻¹ * s * g ∈ Z
      · obtain ⟨m, -, hm⟩ := Z_isConj H hz hz1 hZm hs01
        exact isConj_iff.mpr ⟨m, hm⟩
      · refine (hF.root z hz hz1 _ hs0Q hZm).mpr ?_
        obtain ⟨s₁, t₁, hst⟩ := hs'.2
        have hπ : M₀.π (g⁻¹ * s * g) ≠ 0 := fun h0' => hZm ((M₀.π_ker _ hs0Q).mp h0')
        have hne : (s₁ ≠ 0 ∨ t₁ ≠ 0) := by
          by_contra hcon
          push Not at hcon
          apply hπ
          apply φ.injective
          rw [hst, hcon.1, hcon.2]
          simp
        exact ⟨s₁, t₁, u, hne, hu0, hqu, hst⟩
    exact IsConj.trans hroot (isConj_iff.mpr ⟨g, by group⟩)
  ·
    have h4 := H.q4
    have hcard : Nat.card (conjSubgroup g S') = Nat.card Z ^ 3 := by
      rw [card_conjSubgroup, hS'card, hTcard, hKZ]
      ring
    rw [hcard]
    exact Nat.pow_lt_pow_right (by omega) (by norm_num)

theorem smithLaneOrth_of_section5Act (hT : TimmesfeldOutcomeStatement)
    (h212 : Smith212OrthCoreStatement) (h213 : Smith213OrthStatement)
    (h24 : Smith24ActStatement) (h52 : Smith52ActStatement)
    (hOdd : Smith216OrthOddStatement) (h217 : Smith217Statement)
    (hInsp : Smith219OrthInspectionStatement) : LaneOrthStep :=
  smithLaneOrth_of_inputs hT h212 h213 (smith216OrthCount_of_52Act h24 h52) hOdd h217 hInsp

end CFSG.RankThree.GF2n.Smith81
