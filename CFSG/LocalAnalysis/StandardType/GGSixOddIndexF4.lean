module

public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexAut

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

section Elementary

variable {G : Type*} [Group G]

theorem ggF4_normalizer_inf_le (H K : Subgroup G) :
    Subgroup.normalizer (H : Set G) ⊓ Subgroup.normalizer (K : Set G) ≤
      Subgroup.normalizer ((H ⊓ K : Subgroup G) : Set G) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have h1 := Subgroup.mem_normalizer_iff.mp hm.1 z
  have h2 := Subgroup.mem_normalizer_iff.mp hm.2 z
  simp only [Subgroup.mem_inf]
  exact ⟨fun h => ⟨h1.mp h.1, h2.mp h.2⟩, fun h => ⟨h1.mpr h.1, h2.mpr h.2⟩⟩

theorem ggF4_false_of_pow_le {p k m : ℕ} (hp : p.Prime) (hk : k < 4) (h4 : p ^ 4 ≤ m)
    (hm : m ≤ p ^ k) : False :=
  absurd (h4.trans hm) (not_le.mpr (pow_lt_pow_right₀ hp.one_lt hk))

theorem ggF4_orderOf_eq_of_elemAbelian {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hE : IsElemAbelian p E) {b : G} (hb : b ∈ E) (hb1 : b ≠ 1) : orderOf b = p := by
  rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one (hE.2 b hb)) with h | h
  · exact absurd (orderOf_eq_one_iff.mp h) hb1
  · exact h

theorem ggF4_exists_involution_of_card_le_two [Finite G] {U : Subgroup G} (hU : U ≠ ⊥)
    (hU2 : Nat.card U ≤ 2) : ∃ s ∈ U, orderOf s = 2 ∧ U = Subgroup.zpowers s := by
  obtain ⟨s, hsU, hs1⟩ : ∃ s ∈ U, s ≠ 1 := by
    by_contra h
    push Not at h
    exact hU ((Subgroup.eq_bot_iff_forall U).mpr h)
  have hdvd : orderOf s ∣ Nat.card U := Subgroup.orderOf_dvd_natCard U hsU
  have hpos : 0 < Nat.card U := Nat.card_pos
  have hle : orderOf s ≤ 2 := (Nat.le_of_dvd hpos hdvd).trans hU2
  have hne : orderOf s ≠ 1 := fun h => hs1 (orderOf_eq_one_iff.mp h)
  have hord : orderOf s = 2 := by
    have h0 : 0 < orderOf s := orderOf_pos s
    omega
  refine ⟨s, hsU, hord, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hsU) ?_).symm
  rw [Nat.card_zpowers, hord]
  exact hU2

end Elementary

section Normalizer

variable {G : Type*} [Group G] {G₀ : Subgroup G}

theorem ggF4_normalizerMonoidHom_injective (hC : Subgroup.centralizer (G₀ : Set G) = ⊥) :
    Function.Injective G₀.normalizerMonoidHom := by
  rw [← MonoidHom.ker_eq_bot_iff, Subgroup.normalizerMonoidHom_ker, hC]
  ext x
  simp

theorem ggF4_normalizerMonoidHom_of_mem (g : G₀) :
    G₀.normalizerMonoidHom ⟨g, Subgroup.le_normalizer g.2⟩ = MulAut.conj g := by
  have hφapp : ∀ (m : Subgroup.normalizer (G₀ : Set G)) (h : G₀),
      ((G₀.normalizerMonoidHom m h : G₀) : G) = (m : G) * h * (m : G)⁻¹ := fun _ _ => rfl
  ext h
  rw [MulAut.conj_apply, hφapp]
  rfl

theorem ggF4_card_le_two_of_inf_eq_bot (hC : Subgroup.centralizer (G₀ : Set G) = ⊥)
    (hQ : ∀ Q : Subgroup (MulAut G₀), IsPGroup 2 Q →
      Q ⊓ (MulAut.conj : G₀ →* MulAut G₀).range = ⊥ → Nat.card Q ≤ 2)
    {U : Subgroup G} (hUN : U ≤ Subgroup.normalizer (G₀ : Set G)) (hU2 : IsPGroup 2 U)
    (hUG : U ⊓ G₀ = ⊥) : Nat.card U ≤ 2 := by
  classical
  set N := Subgroup.normalizer (G₀ : Set G)
  set φ := G₀.normalizerMonoidHom
  have hφ : Function.Injective φ := ggF4_normalizerMonoidHom_injective hC
  have hcard : Nat.card ((U.subgroupOf N).map φ) = Nat.card U := by
    rw [Subgroup.card_map_of_injective hφ]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUN).toEquiv
  rw [← hcard]
  refine hQ _ ((hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUN).symm).map φ) ?_
  rw [eq_bot_iff]
  rintro σ ⟨⟨u, hu, rfl⟩, ⟨g, hg⟩⟩
  have hug : u = ⟨g, Subgroup.le_normalizer g.2⟩ := by
    apply hφ
    rw [← hg, ggF4_normalizerMonoidHom_of_mem]
  have hu1 : (u : G) ∈ U ⊓ G₀ := ⟨hu, by rw [hug]; exact g.2⟩
  rw [hUG, Subgroup.mem_bot] at hu1
  have hu1' : u = 1 := Subtype.ext hu1
  rw [Subgroup.mem_bot, hu1', map_one]

theorem ggF4_exists_involution_of_even [Finite G] (hC : Subgroup.centralizer (G₀ : Set G) = ⊥)
    {X : Subgroup G} (hGX : G₀ ≤ X) (hXN : X ≤ Subgroup.normalizer (G₀ : Set G))
    (heven : Even (G₀.relIndex X)) {C : Subgroup (MulAut G₀)}
    (hIC : ∀ σ : MulAut G₀, ∃ i ∈ (MulAut.conj : G₀ →* MulAut G₀).range, ∃ c ∈ C, σ = i * c)
    (hIC' : (MulAut.conj : G₀ →* MulAut G₀).range ⊓ C = ⊥) :
    ∃ s ∈ X, s ∉ G₀ ∧ orderOf s = 2 := by
  classical
  set N := Subgroup.normalizer (G₀ : Set G)
  set φ := G₀.normalizerMonoidHom
  have hφ : Function.Injective φ := ggF4_normalizerMonoidHom_injective hC
  set K := (MulAut.conj : G₀ →* MulAut G₀).range
  have hKn : K.Normal := ggSix_conj_range_normal
  have hKmap : (G₀.subgroupOf N).map φ = K := by
    ext σ
    constructor
    · rintro ⟨m, hm, rfl⟩
      exact ⟨⟨m, hm⟩, (ggF4_normalizerMonoidHom_of_mem ⟨(m : G), hm⟩).symm⟩
    · rintro ⟨g, rfl⟩
      exact ⟨⟨g, Subgroup.le_normalizer g.2⟩, g.2, ggF4_normalizerMonoidHom_of_mem g⟩
  set X' := (X.subgroupOf N).map φ
  have hKX : K ≤ X' := by
    rw [← hKmap]
    exact Subgroup.map_mono fun m hm => hGX hm
  have heven' : Even (K.relIndex X') := by
    rw [← hKmap, Subgroup.relIndex_map_map_of_injective _ _ hφ,
      Subgroup.relIndex_subgroupOf hXN]
    exact heven
  have hodd : Odd (K.relIndex K) := by
    rw [Subgroup.relIndex_self]
    exact odd_one
  obtain ⟨σ, hσX, hσ2, hσK, -⟩ :=
    ggSix_exists_conj_involution_of_even hKn le_rfl hodd hIC hIC' hKX heven'
  obtain ⟨m, hmX, rfl⟩ := hσX
  refine ⟨m, hmX, ?_, ?_⟩
  · intro hmG
    apply hσK
    rw [← hKmap]
    exact ⟨m, hmG, rfl⟩
  · rw [Subgroup.orderOf_coe, ← orderOf_injective φ hφ m, hσ2]

end Normalizer

section Inputs

@[expose] def GGF4Config {G : Type} [Group G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G)
    (G₀ : Subgroup G) : Prop :=
  StatedLieAdmissible .F4 n 2 f ∧ 2 ≤ (ggU .F4 n f).D.rank ∧ ψ.range = G₀ ∧
    ψ.ker ≤ Subgroup.center (ggU .F4 n f).K ∧ commutator ↥G₀ = ⊤ ∧
    LieModel (↥G₀ ⧸ Subgroup.center ↥G₀) .F4 n 2 f ∧ Subgroup.centralizer (G₀ : Set G) = ⊥

@[expose] def GGF4AutInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → Odd f →
      ∃ C : Subgroup (MulAut G₀),
        (∀ σ : MulAut G₀, ∃ i ∈ (MulAut.conj : G₀ →* MulAut G₀).range, ∃ c ∈ C, σ = i * c) ∧
        (MulAut.conj : G₀ →* MulAut G₀).range ⊓ C = ⊥ ∧
        ∀ Q : Subgroup (MulAut G₀), IsPGroup 2 Q →
          Q ⊓ (MulAut.conj : G₀ →* MulAut G₀).range = ⊥ → Nat.card Q ≤ 2

@[expose] def GGF4InnerDiagInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → ∀ b ∈ Subgroup.normalizer (G₀ : Set G),
      GGPsiInnerDiag (ggU .F4 n f).D ψ b → b ∈ G₀

@[expose] def GGF4GraphFieldRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → Odd f → ∀ p : ℕ, p.Prime → p ≠ 2 →
    ∀ s ∈ Subgroup.normalizer (G₀ : Set G), s ∉ G₀ → orderOf s = 2 →
      ∀ E : Subgroup G, E ≤ G₀ ⊓ Subgroup.centralizer {s} → IsElemAbelian p E →
        Nat.card E ≤ p ^ 2

@[expose] def GGF4TwoLocalRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ∣ 2 ^ f - 1 →
    ∀ R : Subgroup G, R ≤ G₀ → R ≠ ⊥ → IsPGroup 2 R →
      ∀ E : Subgroup G, E ≤ G₀ → E ≤ Subgroup.normalizer (R : Set G) → IsElemAbelian p E →
        Nat.card E ≤ p ^ 3

@[expose] def GGF4TorusElementInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → Odd f → ∀ (p : ℕ) (Bs : Subgroup G), p.Prime → p ≠ 2 →
    p ∣ 2 ^ f - 1 → IsElemAbelian p Bs → p ^ 4 ≤ Nat.card Bs → Bs ≤ G₀ →
    ∀ s ∈ Subgroup.normalizer (G₀ : Set G), s ∉ G₀ → orderOf s = 2 →
      ∃ b ∈ Bs, b ≠ 1 ∧
        (∃ L₁ : Subgroup G, IsComponentOf L₁ (G₀ ⊓ Subgroup.centralizer {b}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2) ∧
        ∃ g ∈ G₀, g * b * g⁻¹ * s = s * (g * b * g⁻¹)

@[expose] def GGF4GraphFieldCoreInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → Odd f → ∀ s ∈ Subgroup.normalizer (G₀ : Set G), s ∉ G₀ →
    orderOf s = 2 → ∀ Q : Subgroup G, Q ≤ G₀ ⊓ Subgroup.centralizer {s} → IsPGroup 2 Q →
      G₀ ⊓ Subgroup.centralizer {s} ≤ Subgroup.normalizer (Q : Set G) → Q = ⊥

@[expose] def GGF4FixedPointInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (n f : ℕ) (ψ : (ggU .F4 n f).K →* G) (G₀ : Subgroup G),
    GGF4Config n f ψ G₀ → Odd f → ∀ s ∈ Subgroup.normalizer (G₀ : Set G), s ∉ G₀ →
    orderOf s = 2 → ∀ e ∈ G₀ ⊓ Subgroup.centralizer {s}, Odd (orderOf e) →
    ∀ P : Subgroup G, IsPGroup 2 P →
      G₀ ⊓ Subgroup.centralizer {s} ≤ Subgroup.normalizer (P : Set G) →
      (∀ x ∈ P, x * e = e * x → ∀ y ∈ G₀ ⊓ Subgroup.centralizer {s}, x * y = y * x) →
        ∀ x ∈ P, x * e = e * x

theorem ggSixStepThreeCFourInput_of_inputs (hA : GGF4AutInput) (hI : GGF4InnerDiagInput)
    (hR : GGF4GraphFieldRankInput) (hL : GGF4TwoLocalRankInput) (hT : GGF4TorusElementInput)
    (hO : GGF4GraphFieldCoreInput) (hE : GGF4FixedPointInput) : GGSixStepThreeCFourInput := by
  intro G _ _ p B Bs x L D J n f ψ hf hctx s1 s2 _E _r _hch _hCr
  obtain ⟨⟨-, -, -, hchar, -, hp, hS, -⟩, hcore⟩ := hctx
  obtain ⟨hBs, hstd, ⟨hadm, hrank⟩, ⟨hrange, hker⟩, ⟨hperf, hlie⟩, ⟨hBsN, hBsI⟩, -, -⟩ := hcore
  obtain ⟨hCG₀, -, hsig, -, -⟩ := s1
  set G₀ := ggG0 p B x L D J with hG₀
  set M := ggM p B x L D J with hM
  have hcfg : GGF4Config n f ψ G₀ := ⟨hadm, hrank, hrange, hker, hperf, hlie, hCG₀⟩
  obtain ⟨hpp, hp2, -, hrk⟩ := hp
  have hBsG₀ : Bs ≤ G₀ := fun b hb => hI G n f ψ G₀ hcfg b (hBsN hb) (hBsI b hb)
  have hBG₀ : B ≤ G₀ := hBs.1.trans hBsG₀
  have hBel : IsElemAbelian p B := hS.1.1
  have hcardB : p ^ 4 ≤ Nat.card B := by
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hpp.pos hrk
      _ = Nat.card B := hS.1.2.1.symm
  obtain ⟨U, hU1, hU2, hBU⟩ := hS.1.2.2
  have hcop : Nat.Coprime p (Nat.card U) := by
    obtain ⟨k, hk⟩ := hU2.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k ((Nat.coprime_primes hpp Nat.prime_two).mpr hp2)
  have hUM : U ≤ M := hsig U (hstd.1.1.trans hBU) hcop
  have hUG : U ⊓ G₀ ≠ ⊥ := by
    intro hbot
    obtain ⟨C, -, -, hQ⟩ := hA G n f ψ G₀ hcfg hf
    obtain ⟨s, hsU, hs2, hUs⟩ := ggF4_exists_involution_of_card_le_two hU1
      (ggF4_card_le_two_of_inf_eq_bot hCG₀ hQ hUM hU2 hbot)
    have hsG₀ : s ∉ G₀ := by
      intro hs
      have hs' : s ∈ U ⊓ G₀ := ⟨hsU, hs⟩
      rw [hbot, Subgroup.mem_bot] at hs'
      rw [hs', orderOf_one] at hs2
      exact absurd hs2 (by norm_num)
    have hBC : B ≤ Subgroup.centralizer {s} := by
      rw [hUs] at hBU
      exact hBU.trans (ggSix_normalizer_zpowers_le_centralizer hs2)
    exact ggF4_false_of_pow_le hpp (by norm_num) hcardB
      (hR G n f ψ G₀ hcfg hf p hpp hp2 s (hUM hsU) hsG₀ hs2 B (le_inf hBG₀ hBC) hBel)
  have hpq : p ∣ 2 ^ f - 1 := by
    by_contra hnot
    have hBR : B ≤ Subgroup.normalizer ((U ⊓ G₀ : Subgroup G) : Set G) := fun b hb =>
      ggF4_normalizer_inf_le U G₀ ⟨hBU hb, Subgroup.le_normalizer (hBG₀ hb)⟩
    exact ggF4_false_of_pow_le hpp (by norm_num) hcardB
      (hL G n f ψ G₀ hcfg p hpp hp2 hnot (U ⊓ G₀) inf_le_right hUG (hU2.to_le inf_le_left) B
        hBG₀ hBR hBel)
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨C, hIC, hIC', -⟩ := hA G n f ψ G₀ hcfg hf
  obtain ⟨s, hsM, hsG₀, hs2⟩ :=
    ggF4_exists_involution_of_even hCG₀ Subgroup.le_normalizer le_rfl hev hIC hIC'
  have hcardBs : p ^ 4 ≤ Nat.card Bs := hcardB.trans (Subgroup.card_le_of_le hBs.1)
  obtain ⟨b, hbBs, hb1, ⟨L₁, hL₁, hL₁c⟩, g, hgG₀, hgs⟩ :=
    hT G n f ψ G₀ hcfg hf p Bs hpp hp2 hpq hBs.2.1 hcardBs hBsG₀ s hsM hsG₀ hs2
  have hCb : Subgroup.centralizer {b} ≤ M :=
    (s2 b hbBs hb1 L₁ hL₁ hL₁c).2.centralizer_le (Subgroup.mem_zpowers b) hb1
  have hCe : Subgroup.centralizer {g * b * g⁻¹} ≤ M :=
    centralizer_conj_le hCb (Subgroup.le_normalizer hgG₀)
  have heY : g * b * g⁻¹ ∈ G₀ ⊓ Subgroup.centralizer {s} :=
    ⟨G₀.mul_mem (G₀.mul_mem hgG₀ (hBsG₀ hbBs)) (G₀.inv_mem hgG₀),
      Subgroup.mem_centralizer_singleton_iff.mpr hgs⟩
  have heodd : Odd (orderOf (g * b * g⁻¹)) := by
    rw [ggSix_orderOf_conj, ggF4_orderOf_eq_of_elemAbelian hpp hBs.2.1 hbBs hb1]
    exact hpp.odd_of_ne_two hp2
  set H := Subgroup.normalizer (Subgroup.zpowers s : Set G) with hH
  have hYO := hO G n f ψ G₀ hcfg hf s hsM hsG₀ hs2
  have hfix : ∀ x ∈ CFSG.Assembly.pCoreOf 2 H, x * (g * b * g⁻¹) = g * b * g⁻¹ * x →
      ∀ y ∈ G₀ ⊓ Subgroup.centralizer {s}, x * y = y * x := fun x hx hxe y hy =>
    ggSix_commute_of_mem_pCoreOf_inf (M := M) hs2 inf_le_right hYO
      (ggSix_inf_centralizer_le_normalizer G₀ s)
      ⟨hx, hCe (Subgroup.mem_centralizer_singleton_iff.mpr hxe)⟩ hy
  have hYH : G₀ ⊓ Subgroup.centralizer {s} ≤ H :=
    inf_le_right.trans (ggSix_centralizer_le_normalizer_zpowers s)
  have hcent := hE G n f ψ G₀ hcfg hf s hsM hsG₀ hs2 (g * b * g⁻¹) heY heodd
    (CFSG.Assembly.pCoreOf 2 H) (ggSix_pCoreOf_isPGroup 2 H)
    (hYH.trans (ggSix_le_normalizer_pCoreOf 2 H)) hfix
  have heP : g * b * g⁻¹ ∈ CFSG.Assembly.pCoreOf 2 H :=
    hchar H (ggSix_isTwoLocal_normalizer_zpowers hs2)
      ⟨hYH heY, Subgroup.mem_centralizer_iff.mpr hcent⟩
  have he1 := ggSix_eq_one_of_mem_of_odd (ggSix_pCoreOf_isPGroup 2 H) heP heodd
  apply hb1
  calc b = g⁻¹ * (g * b * g⁻¹) * g := by group
    _ = 1 := by rw [he1]; group

theorem ggSixStepThreeCInput_of_aut_of_F4 (h : GGAutStructureInput) (hA : GGF4AutInput)
    (hI : GGF4InnerDiagInput) (hR : GGF4GraphFieldRankInput) (hL : GGF4TwoLocalRankInput)
    (hT : GGF4TorusElementInput) (hO : GGF4GraphFieldCoreInput) (hE : GGF4FixedPointInput) :
    GGSixStepThreeCInput :=
  ggSixStepThreeCInput_of_aut h (ggSixStepThreeCFourInput_of_inputs hA hI hR hL hT hO hE)

end Inputs

end CFSG.StandardType
