module

public import CFSG.LocalAnalysis.StandardType.GGStepTwoToralSmallOfFrameAux
public import CFSG.LocalAnalysis.StandardType.GGExcKGToralFrame
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoToralRestTags
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcDiagramAutomorphisms

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.StandardType.StepTwoToralCert
  CFSG.StandardType.StepTwoToralSmall

namespace StepTwoToralSmall

section Clauses

variable {G : Type} [Group G] {U' : Type} [Group U'] {p : ℕ} {Bs G₀ : Subgroup G}
  {Δ : UniversalRootDatum U'} {S : Matrix (Fin Δ.rank) (Fin Δ.rank) ℤ}
  {π : Equiv.Perm (Fin Δ.rank)} {f : ℕ}

@[expose] def FrameW (F : GGStdForm p Bs G₀ Δ S π f) : Prop :=
  ∀ u : GGWeyl Δ, (∀ α, weylAction Δ.isFiniteType u (latPerm π α) =
      latPerm π (weylAction Δ.isFiniteType u α)) →
    ∃ m ∈ G₀ ⊓ Subgroup.normalizer (Bs : Set G), ∀ b b' : Bs, (b' : G) = m * b * m⁻¹ →
      ∀ i, Multiplicative.toAdd (F.coord b') i = latChar p (Multiplicative.toAdd (F.coord b))
        (weylAction Δ.isFiniteType u⁻¹ (Pi.single i 1))

@[expose] def FrameA (F : GGStdForm p Bs G₀ Δ S π f) : Prop :=
  ∀ b : Bs, b ≠ 1 → ∀ L : Subgroup G, IsComponentOf L (G₀ ⊓ Subgroup.centralizer {(b : G)}) →
    ∃ O, IsCompOrbit S π (latPhi Δ.roots p (Multiplicative.toAdd (F.coord b))) O ∧
      (∀ b' : Bs, (b' : G) ∈ Subgroup.centralizer (L : Set G) ↔
        ∀ α ∈ O, latChar p (Multiplicative.toAdd (F.coord b')) α = 0) ∧
      ∀ b' : Bs, Multiplicative.toAdd (F.coord b') ∈ latEigenCoroot p S π O → (b' : G) ∈ L

@[expose] def FrameAU (F : GGStdForm p Bs G₀ Δ S π f) : Prop :=
  ∀ U : Subgroup G, U ≤ Bs → U ≠ ⊥ → ∀ K : Subgroup G,
    IsComponentOf K (G₀ ⊓ Subgroup.centralizer (U : Set G)) →
      ∃ O, IsCompOrbit S π {α | α ∈ Δ.roots ∧ ∀ u : Bs, (u : G) ∈ U →
          latChar p (Multiplicative.toAdd (F.coord u)) α = 0} O ∧
        ∀ b' : Bs, (∀ α ∈ O, latChar p (Multiplicative.toAdd (F.coord b')) α = 0) →
          (b' : G) ∈ Subgroup.centralizer (K : Set G)

end Clauses

section Convert

variable {G : Type} [Group G] {p : ℕ} [NeZero p] {f : ℕ} {Bs G₀ : Subgroup G}

theorem toralFrame_E6
    {S : Matrix (Fin (ggU .E6 6 f).D.rank) (Fin (ggU .E6 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU .E6 6 f).D.rank)} (F : GGStdForm p Bs G₀ (ggU .E6 6 f).D S π f)
    (hS : IsRootGram (ggU .E6 6 f).D S) (hW : FrameW F) (hA : FrameA F) (hAU : FrameAU F) :
    Nonempty (ToralFrame Tag.E6 p G₀ Bs π) := by
  obtain ⟨k, hk, rfl⟩ := isRootGram_E6 6 f S hS
  have hroots : (ggU .E6 6 f).D.roots = {α | IsRoot Tag.E6 α} :=
    Set.ext fun α => (mem_roots_E6 6 f α).trans mem_rootFinset
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨
    { coord := F.coord
      coord_inj := F.coord_inj
      coord_fixed := F.coord_fixed
      coord_surj := fun g hg hfix => F.coord_surj g (exists_int_of_mem_t0Sub hg) hfix
      weyl := fun u hu => ?_
      orbit := fun b hb L hL => ?_
      orbitU := fun U hU hne K hK => ?_ }⟩
  · obtain ⟨m, hm, h⟩ := hW u hu
    exact ⟨m, hm, fun b b' hb' => funext fun i => h b b' hb' i⟩
  · obtain ⟨O, hO, h1, h2⟩ := hA b hb L hL
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1, fun b' hb' =>
      h2 b' ((Set.ext_iff.1 (latEigenCoroot_smul hkpos p _ π O) _).2 hb')⟩
  · obtain ⟨O, hO, h1⟩ := hAU U hU hne K hK
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1⟩

theorem toralFrame_F4
    {S : Matrix (Fin (ggU .F4 6 f).D.rank) (Fin (ggU .F4 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU .F4 6 f).D.rank)} (F : GGStdForm p Bs G₀ (ggU .F4 6 f).D S π f)
    (hS : IsRootGram (ggU .F4 6 f).D S) (hW : FrameW F) (hA : FrameA F) (hAU : FrameAU F) :
    Nonempty (ToralFrame Tag.F4 p G₀ Bs π) := by
  obtain ⟨k, hk, rfl⟩ := isRootGram_F4 6 f S hS
  have hroots : (ggU .F4 6 f).D.roots = {α | IsRoot Tag.F4 α} :=
    Set.ext fun α => (mem_roots_F4 6 f α).trans mem_rootFinset
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨
    { coord := F.coord
      coord_inj := F.coord_inj
      coord_fixed := F.coord_fixed
      coord_surj := fun g hg hfix => F.coord_surj g (exists_int_of_mem_t0Sub hg) hfix
      weyl := fun u hu => ?_
      orbit := fun b hb L hL => ?_
      orbitU := fun U hU hne K hK => ?_ }⟩
  · obtain ⟨m, hm, h⟩ := hW u hu
    exact ⟨m, hm, fun b b' hb' => funext fun i => h b b' hb' i⟩
  · obtain ⟨O, hO, h1, h2⟩ := hA b hb L hL
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1, fun b' hb' =>
      h2 b' ((Set.ext_iff.1 (latEigenCoroot_smul hkpos p _ π O) _).2 hb')⟩
  · obtain ⟨O, hO, h1⟩ := hAU U hU hne K hK
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1⟩

theorem toralFrame_E7
    {S : Matrix (Fin (ggU .E7 6 f).D.rank) (Fin (ggU .E7 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU .E7 6 f).D.rank)} (F : GGStdForm p Bs G₀ (ggU .E7 6 f).D S π f)
    (hS : IsRootGram (ggU .E7 6 f).D S) (hW : FrameW F) (hA : FrameA F) (hAU : FrameAU F) :
    Nonempty (ToralFrame Tag.E7 p G₀ Bs π) := by
  obtain ⟨k, hk, rfl⟩ := isRootGram_E7 6 f S hS
  have hroots : (ggU .E7 6 f).D.roots = {α | IsRoot Tag.E7 α} :=
    Set.ext fun α => (mem_roots_E7 6 f α).trans mem_rootFinset
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨
    { coord := F.coord
      coord_inj := F.coord_inj
      coord_fixed := F.coord_fixed
      coord_surj := fun g hg hfix => F.coord_surj g (exists_int_of_mem_t0Sub hg) hfix
      weyl := fun u hu => ?_
      orbit := fun b hb L hL => ?_
      orbitU := fun U hU hne K hK => ?_ }⟩
  · obtain ⟨m, hm, h⟩ := hW u hu
    exact ⟨m, hm, fun b b' hb' => funext fun i => h b b' hb' i⟩
  · obtain ⟨O, hO, h1, h2⟩ := hA b hb L hL
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1, fun b' hb' =>
      h2 b' ((Set.ext_iff.1 (latEigenCoroot_smul hkpos p _ π O) _).2 hb')⟩
  · obtain ⟨O, hO, h1⟩ := hAU U hU hne K hK
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1⟩

theorem toralFrame_E8
    {S : Matrix (Fin (ggU .E8 6 f).D.rank) (Fin (ggU .E8 6 f).D.rank) ℤ}
    {π : Equiv.Perm (Fin (ggU .E8 6 f).D.rank)} (F : GGStdForm p Bs G₀ (ggU .E8 6 f).D S π f)
    (hS : IsRootGram (ggU .E8 6 f).D S) (hW : FrameW F) (hA : FrameA F) (hAU : FrameAU F) :
    Nonempty (ToralFrame Tag.E8 p G₀ Bs π) := by
  obtain ⟨k, hk, rfl⟩ := isRootGram_E8 6 f S hS
  have hroots : (ggU .E8 6 f).D.roots = {α | IsRoot Tag.E8 α} :=
    Set.ext fun α => (mem_roots_E8 6 f α).trans mem_rootFinset
  have hkpos : (0 : ℤ) < k := by exact_mod_cast hk
  refine ⟨
    { coord := F.coord
      coord_inj := F.coord_inj
      coord_fixed := F.coord_fixed
      coord_surj := fun g hg hfix => F.coord_surj g (exists_int_of_mem_t0Sub hg) hfix
      weyl := fun u hu => ?_
      orbit := fun b hb L hL => ?_
      orbitU := fun U hU hne K hK => ?_ }⟩
  · obtain ⟨m, hm, h⟩ := hW u hu
    exact ⟨m, hm, fun b b' hb' => funext fun i => h b b' hb' i⟩
  · obtain ⟨O, hO, h1, h2⟩ := hA b hb L hL
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1, fun b' hb' =>
      h2 b' ((Set.ext_iff.1 (latEigenCoroot_smul hkpos p _ π O) _).2 hb')⟩
  · obtain ⟨O, hO, h1⟩ := hAU U hU hne K hK
    rw [hroots] at hO
    exact ⟨O, (isCompOrbit_smul_iff hkpos.ne' _ _ _ _).1 hO, h1⟩

end Convert

section Primes

theorem prime_dvd_cases {p a b c d : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ a * 3 ^ b * 5 ^ c * 7 ^ d) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h))
      · exact Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1
          (hp.dvd_of_dvd_pow h)))
    · exact Or.inr (Or.inr (Or.inl ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1
        (hp.dvd_of_dvd_pow h))))
  · exact Or.inr (Or.inr (Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1
      (hp.dvd_of_dvd_pow h))))

theorem prime_dvd_F4 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 1152) : p = 3 := by
  have h' : p ∣ 2 ^ 7 * 3 ^ 2 * 5 ^ 0 * 7 ^ 0 := by
    have e : (1152 : ℕ) = 2 ^ 7 * 3 ^ 2 * 5 ^ 0 * 7 ^ 0 := by norm_num
    rw [← e]; exact h
  rcases prime_dvd_cases hp h' with rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · rfl
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem prime_dvd_E6 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 51840) : p = 3 ∨ p = 5 := by
  have h' : p ∣ 2 ^ 7 * 3 ^ 4 * 5 ^ 1 * 7 ^ 0 := by
    have e : (51840 : ℕ) = 2 ^ 7 * 3 ^ 4 * 5 ^ 1 * 7 ^ 0 := by norm_num
    rw [← e]; exact h
  rcases prime_dvd_cases hp h' with rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · exact Or.inl rfl
  · exact Or.inr rfl
  · exact absurd h (by decide)

theorem prime_dvd_E7 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 2903040) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have h' : p ∣ 2 ^ 10 * 3 ^ 4 * 5 ^ 1 * 7 ^ 1 := by
    have e : (2903040 : ℕ) = 2 ^ 10 * 3 ^ 4 * 5 ^ 1 * 7 ^ 1 := by norm_num
    rw [← e]; exact h
  rcases prime_dvd_cases hp h' with rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

theorem prime_dvd_E8 {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h : p ∣ 696729600) :
    p = 3 ∨ p = 5 ∨ p = 7 := by
  have h' : p ∣ 2 ^ 14 * 3 ^ 5 * 5 ^ 2 * 7 ^ 1 := by
    have e : (696729600 : ℕ) = 2 ^ 14 * 3 ^ 5 * 5 ^ 2 * 7 ^ 1 := by norm_num
    rw [← e]; exact h
  rcases prime_dvd_cases hp h' with rfl | rfl | rfl | rfl
  · exact absurd rfl hp2
  · exact Or.inl rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inr (Or.inr rfl)

end Primes

section Cases

variable {G : Type} [Group G] {G₀ Bs : Subgroup G}

theorem splitCertSpec_V
    (hC : CertAll) {τ : Tag} {p : ℕ} [NeZero p] (hp : p.Prime)
    (hτp : (τ = .F4 ∧ p = 3) ∨ (τ = .E6 ∧ (p = 3 ∨ p = 5)) ∨
      (τ = .E7 ∧ (p = 3 ∨ p = 5 ∨ p = 7)) ∨ (τ = .E8 ∧ (p = 3 ∨ p = 5 ∨ p = 7)))
    (fr : ToralFrame τ p G₀ Bs 1) : SplitCertSpec τ p fr.V := by
  obtain ⟨cF4, ⟨cE63, cE63t, cE65⟩, ⟨cE73, cE75, cE77⟩, ⟨cE83, cE85, cE87⟩, -⟩ := hC
  rcases hτp with ⟨rfl, rfl⟩ | ⟨rfl, rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩ | ⟨rfl, rfl | rfl | rfl⟩
  · rw [fr.V_eq_top rfl (t0Sub_eq_top hp (by rw [det_cartan_F4]; norm_num))]; exact cF4
  · rcases eq_t0Sub_or_top_E6 (fr.t0Sub_le_V rfl) with h | h
    · rw [h]; exact cE63t
    · rw [h]; exact cE63
  · rw [fr.V_eq_top rfl (t0Sub_eq_top hp (by rw [det_cartan_E6]; norm_num))]; exact cE65
  · rw [fr.V_eq_top rfl (t0Sub_eq_top hp (by rw [det_cartan_E7]; norm_num))]; exact cE73
  · rw [fr.V_eq_top rfl (t0Sub_eq_top hp (by rw [det_cartan_E7]; norm_num))]; exact cE75
  · rw [fr.V_eq_top rfl (t0Sub_eq_top hp (by rw [det_cartan_E7]; norm_num))]; exact cE77
  · rw [fr.V_eq_top rfl (t0Sub_eq_top hp (by rw [det_cartan_E8]; norm_num))]; exact cE83
  · rw [fr.V_eq_top rfl (t0Sub_eq_top hp (by rw [det_cartan_E8]; norm_num))]; exact cE85
  · rw [fr.V_eq_top rfl (t0Sub_eq_top hp (by rw [det_cartan_E8]; norm_num))]; exact cE87

theorem twistCase (hC : CertAll) {p : ℕ} [NeZero p]
    (hp : p.Prime) (hp35 : p = 3 ∨ p = 5) (fr : ToralFrame Tag.E6 p G₀ Bs e6Gamma) :
    fr.V = fixedSub p e6Gamma ∧ TwistCertSpec p e6Gamma := by
  obtain ⟨-, -, -, -, cT3, cT5⟩ := hC
  rcases hp35 with rfl | rfl
  · exact ⟨fr.V_eq_fixedSub fixedSub_e6Gamma_le_t0Sub_three, cT3⟩
  · exact ⟨fr.V_eq_fixedSub (le_of_le_of_eq le_top
      (t0Sub_eq_top hp (by rw [det_cartan_E6]; norm_num)).symm), cT5⟩

end Cases

end StepTwoToralSmall

section Main

theorem ggStepTwoToralWitnessSmallOn_of_frameSpec (hF : GGExcKGToralFrame) (hreg : GGExcRegimeInput)
    (hC : StepTwoToralCert.CertAll) {t : StatedLieTag}
    (ht : t = .F4 ∨ t = .E6 ∨ t = .E7 ∨ t = .E8 ∨ t = .twistedE6) :
    GGStepTwoToralWitnessSmallOn t := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hWo b L₁ hpair _
  have ht' : GGExcFive t := ht
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hks : GGKnownSetting t n f ψ := ggKnownSetting_of_ctx hctx s1
  have hcard : p ^ 4 ≤ Nat.card Bs := hctx.pow_four_le_card_bstar
  have hBsN : Bs ≤ Subgroup.normalizer (ψ.range : Set G) := by
    rw [hctx.range_eq]; exact hctx.bstar_le_normalizer
  have hinn : ∀ b ∈ (Bs : Subgroup G), GGPsiInnerDiag (ggU t n f).D ψ b :=
    hctx.2.2.2.2.2.2.1.2
  have hsyl : ∃ P : Sylow p (Subgroup.normalizer (ψ.range : Set G)),
      Bs ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype ∧
      ∀ E : Subgroup G, E ≤ (P : Subgroup (Subgroup.normalizer (ψ.range : Set G))).map
        (Subgroup.normalizer (ψ.range : Set G)).subtype →
        IsElemAbelian p E → Nat.card E = Nat.card Bs → E = Bs := by
    have hnorm : Subgroup.normalizer (ψ.range : Set G) =
        Subgroup.normalizer (ggG0 p B x L D J : Set G) := by rw [hctx.range_eq]
    exact hnorm.symm ▸ s1.2.2.2.1
  obtain ⟨S, π, F, ⟨hSr, hπ, hπ1, -, -, -, -⟩, hW, hA, hAU⟩ :=
    hF t n f ht' G ψ hks p hp hp2 (hreg G p B Bs x L D J t n f ψ ht' hctx s1) Bs
      hctx.bstar.2.1 hcard hBsN hinn hsyl
  obtain ⟨hb, hb1, hL₁, hL₁card⟩ := hpair
  rw [← hctx.range_eq] at hL₁
  have hJ := hctx.j_isComponentOf_inf
  rw [← hctx.range_eq] at hJ
  rw [← hctx.range_eq]
  have hDBs := hctx.d_le_bstar
  have hDcard := hctx.card_d
  have hJcard := hctx.card_bstar_inf_centralizer_le
  rcases ht with rfl | rfl | rfl | rfl | rfl
  ·
    have hp3 := StepTwoToralSmall.prime_dvd_F4 hp hp2 hWo
    obtain ⟨fr⟩ := StepTwoToralSmall.toralFrame_F4 F hSr hW hA hAU
    have h1 : π = 1 := hπ1 (Or.inl rfl)
    subst h1
    exact StepTwoToralSmall.witness_of_split fr hp
      (StepTwoToralSmall.splitCertSpec_V hC hp (Or.inl ⟨rfl, hp3⟩) fr)
      hDBs hDcard hJ hJcard hb hb1 hL₁ hL₁card
  ·
    have h35 := StepTwoToralSmall.prime_dvd_E6 hp hp2 hWo
    obtain ⟨fr⟩ := StepTwoToralSmall.toralFrame_E6 F hSr hW hA hAU
    rcases perm_eq_one_or_eq_sigma_of_cartan_E6 π (fun i j => hπ i j) with h1 | h1
    · subst h1
      exact StepTwoToralSmall.witness_of_split fr hp
        (StepTwoToralSmall.splitCertSpec_V hC hp (Or.inr (Or.inl ⟨rfl, h35⟩)) fr)
        hDBs hDcard hJ hJcard hb hb1 hL₁ hL₁card
    · have h2 : π = e6Gamma := h1
      subst h2
      obtain ⟨hV, hT⟩ := StepTwoToralSmall.twistCase hC hp h35 fr
      exact StepTwoToralSmall.witness_of_twist fr hp hV hT hDBs hDcard hJ hJcard hb hb1 hL₁
        hL₁card
  ·
    have h357 := StepTwoToralSmall.prime_dvd_E7 hp hp2 hWo
    obtain ⟨fr⟩ := StepTwoToralSmall.toralFrame_E7 F hSr hW hA hAU
    have h1 : π = 1 := hπ1 (Or.inr (Or.inl rfl))
    subst h1
    exact StepTwoToralSmall.witness_of_split fr hp
      (StepTwoToralSmall.splitCertSpec_V hC hp (Or.inr (Or.inr (Or.inl ⟨rfl, h357⟩))) fr)
      hDBs hDcard hJ hJcard hb hb1 hL₁ hL₁card
  ·
    have h357 := StepTwoToralSmall.prime_dvd_E8 hp hp2 hWo
    obtain ⟨fr⟩ := StepTwoToralSmall.toralFrame_E8 F hSr hW hA hAU
    have h1 : π = 1 := hπ1 (Or.inr (Or.inr rfl))
    subst h1
    exact StepTwoToralSmall.witness_of_split fr hp
      (StepTwoToralSmall.splitCertSpec_V hC hp (Or.inr (Or.inr (Or.inr ⟨rfl, h357⟩))) fr)
      hDBs hDcard hJ hJcard hb hb1 hL₁ hL₁card
  ·
    have h35 := StepTwoToralSmall.prime_dvd_E6 hp hp2 hWo
    obtain ⟨fr⟩ := StepTwoToralSmall.toralFrame_E6 F hSr hW hA hAU
    rcases perm_eq_one_or_eq_sigma_of_cartan_E6 π (fun i j => hπ i j) with h1 | h1
    · subst h1
      exact StepTwoToralSmall.witness_of_split fr hp
        (StepTwoToralSmall.splitCertSpec_V hC hp (Or.inr (Or.inl ⟨rfl, h35⟩)) fr)
        hDBs hDcard hJ hJcard hb hb1 hL₁ hL₁card
    · have h2 : π = e6Gamma := h1
      subst h2
      obtain ⟨hV, hT⟩ := StepTwoToralSmall.twistCase hC hp h35 fr
      exact StepTwoToralSmall.witness_of_twist fr hp hV hT hDBs hDcard hJ hJcard hb hb1 hL₁
        hL₁card

end Main

end CFSG.StandardType
