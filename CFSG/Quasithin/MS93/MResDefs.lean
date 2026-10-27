module

public import CFSG.Quasithin.MS93.S46Qj
public import CFSG.Quasithin.MS93.ASSL3
public import CFSG.Quasithin.MS93.S34FDesc
public import CFSG.Quasithin.MS93.S45IV

public section

namespace CFSG.Quasithin.MS93.MRes

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

section NotSL3Big

variable {G : Type} [Group G]

@[expose] def NotSL3Big (L : Subgroup G) : Prop :=
  ¬ ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
    2 ≤ n ∧ Fintype.card F = 2 ^ n ∧ IsModO2Surj L α

variable [Finite G] {M T L : Subgroup G}

theorem isModO2Surj_of_surjective (h : PUHyp M T L) {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) {α : ↥L →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) :
    IsModO2Surj L α := by
  refine ⟨hα, le_antisymm ?_ (pCore_le_ker_of_statedSL3 α hα)⟩
  set e := specialLinearGroupEquivStatedSL 3 F
  set ψ : ↥L →* SL3 F := e.symm.toMonoidHom.comp α with hψ
  have hψs : Function.Surjective ψ := e.symm.surjective.comp hα
  have hker := S46.QjAux.ker_le_pCore_of_surjective_sl3 h.quasisimple
    (by rw [Nat.card_eq_fintype_card, hF]) hψs
  intro x hx
  refine hker ?_
  rw [MonoidHom.mem_ker] at hx ⊢
  rw [hψ, MonoidHom.comp_apply, hx, map_one]

theorem card_eq_two_of_surjective (h : PUHyp M T L) (hL : NotSL3Big L) {F : Type} [Field F]
    [Fintype F] {n : ℕ} (hF : Fintype.card F = 2 ^ n) {α : ↥L →* ↥(StatedSL 3 F)}
    (hα : Function.Surjective α) : Fintype.card F = 2 := by
  have h1 : 1 < Fintype.card F := Fintype.one_lt_card
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [hF, pow_zero] at h1
    exact lt_irrefl 1 h1
  have hn1 : n = 1 := by
    by_contra hne
    exact hL ⟨n, F, inferInstance, inferInstance, α, by omega, hF,
      isModO2Surj_of_surjective h hF hα⟩
  rw [hF, hn1, pow_one]

theorem card_eq_two_of_via (h : PUHyp M T L) (hL : NotSL3Big L) {F : Type} [Field F] [Fintype F]
    {φ : ↥M →* ↥(StatedSL 3 F)} (hφ : IsSL3FullVia M T L φ) : Fintype.card F = 2 := by
  obtain ⟨⟨n, hn⟩, hφs, -⟩ := hφ
  have hα : Function.Surjective (φ.comp (Subgroup.inclusion h.L_le)) := fun y => by
    obtain ⟨ℓ, hℓL, hℓ⟩ := exists_mem_L_eq h hφs y
    exact ⟨⟨ℓ, hℓL⟩, hℓ⟩
  exact card_eq_two_of_surjective h hL hn hα

theorem not_isSL3UEven (h : PUHyp M T L) (hL : NotSL3Big L) : ¬ S34F.IsSL3UEven M T L := by
  rintro ⟨-, -, m, F, _, _, α, hcard, hα, -⟩
  have h2 := card_eq_two_of_surjective h hL (n := 2 * m) (by rw [hcard, S34F.four_pow_eq]) hα
  rw [hcard] at h2
  rcases m with _ | m
  · rw [pow_zero] at h2
    exact absurd h2 (by decide)
  · have h4 : 4 ≤ 4 ^ (m + 1) := Nat.le_self_pow (by omega) 4
    omega

theorem isSL3Full_of_isSL3U (h : PUHyp M T L) (hL : NotSL3Big L) (hU : IsSL3U M T L) :
    IsSL3Full M T L := by
  by_contra hF
  exact not_isSL3UEven h hL (S34F.isSL3UEven_of_nonfull h hU hF)

end NotSL3Big

section Descent

@[expose] def S34FDescSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) →
    S34F.IsSp4UEven M T L ∧ ¬ IsSp4Full M T L →
    (∃ θ : MulAut ↥T, ∃ x : ↥T, (x : G) ∈ pCoreOf 2 M ∧ ((θ x : ↥T) : G) ∉ L ⊔ pCoreOf 2 M) →
    (∀ μ : Vtx (puAmalgam h.le), IsCritical (puAmalgam h.le) μ (baseA _) →
      geo (puAmalgam h.le) (baseA _) μ 1 = baseB _ →
      ¬ Qv (puAmalgam h.le) (baseB _) ≤
        Subgroup.centralizer (critR (puAmalgam h.le) μ (baseA _) :
          Set (puAmalgam h.le).Universal)) →
    (∃ C : Subgroup G, C ≤ T ⊓ (L ⊔ pCoreOf 2 M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (T ⊓ (L ⊔ pCoreOf 2 M))).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)) →
    (∃ C : Subgroup G, C ≤ T ⊓ L ∧ C ≠ ⊥ ∧ (C.subgroupOf (T ⊓ L)).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)) →
    ∃ T' : Subgroup G, T' ≤ T ∧ T' ≠ T ∧ PUHyp (L ⊔ T') T' L

@[expose] def S34RDescSp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (h : PUHyp M T L), PUMin M T L →
    2 < critDist (puAmalgam h.le) → IsSp4U M T L ∧ ¬ IsSp4Full M T L →
    ∃ T' : Subgroup G, T' ≤ T ∧ T' ≠ T ∧ PUHyp (L ⊔ T') T' L

theorem descSp4_of_fDescSp4 (hF : S34FDescSp4) : S34RDescSp4 := by
  intro G _ _ M T L h hmin hb hc
  have hc' : (IsSL3U M T L ∧ ¬ IsSL3Full M T L) ∨ (IsSp4U M T L ∧ ¬ IsSp4Full M T L) :=
    Or.inr hc
  by_cases hflat : ∃ C : Subgroup G, C ≤ T ⊓ (L ⊔ pCoreOf 2 M) ∧ C ≠ ⊥ ∧
      (C.subgroupOf (T ⊓ (L ⊔ pCoreOf 2 M))).Characteristic ∧
      M ≤ Subgroup.normalizer (C : Set G)
  · by_cases hinf : ∃ C : Subgroup G, C ≤ T ⊓ L ∧ C ≠ ⊥ ∧
        (C.subgroupOf (T ⊓ L)).Characteristic ∧ M ≤ Subgroup.normalizer (C : Set G)
    · exact hF G M T L h hmin hb ⟨S34F.isSp4UEven_of_nonfull h hc.1 hc.2, hc.2⟩
        (S34F.exists_mulAut_not_mem h hmin hc')
        (fun μ hcμ hμβ => S34F.not_le_centralizer_critR h hc' hcμ hμβ) hflat hinf
    · push Not at hinf
      refine ⟨T ⊓ L, inf_le_left, fun heq => ?_, S34E.inf_desc h hinf⟩
      exact hc.2 (S34D.sp4Full_of_le_sup h hc.1
        (heq.symm.le.trans (inf_le_right.trans le_sup_left)))
  · push Not at hflat
    refine ⟨T ⊓ (L ⊔ pCoreOf 2 M), inf_le_left, fun heq => ?_, S34E.flat_desc h hflat⟩
    exact hc.2 (S34D.sp4Full_of_le_sup h hc.1 (heq.symm.le.trans inf_le_right))

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem endConcl_of_notSL3Big (hred : PUReduce) (hdesc : S34RDescSp4) (hL : NotSL3Big L) :
    ∀ (n : ℕ) (M T : Subgroup G), PUHyp M T L → Nat.card T = n → S34D.EndConcl T L := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro M T h hn
    obtain ⟨M₁, T₁, h₁, hT₁, hmin₁, -⟩ := exists_minimal_reduction hred h
    by_cases hb₁ : critDist (puAmalgam h₁.le) = 2
    · exact ⟨M₁, T₁, h₁, hT₁, hmin₁, Or.inl hb₁⟩
    have hSL : IsSL3U M₁ T₁ L → IsSL3Full M₁ T₁ L := isSL3Full_of_isSL3U h₁ hL
    by_cases hgood : IsSp4U M₁ T₁ L → IsSp4Full M₁ T₁ L
    · exact ⟨M₁, T₁, h₁, hT₁, hmin₁, Or.inr ⟨hSL, hgood⟩⟩
    have hpos := h₁.critDist_pos
    obtain ⟨m, hm⟩ := h₁.critDist_even
    have hb' : 2 < critDist (puAmalgam h₁.le) := by omega
    obtain ⟨T', hT', hne, h'⟩ := hdesc G M₁ T₁ L h₁ hmin₁ hb' (not_imp.1 hgood)
    have hlt : Nat.card T' < n :=
      hn ▸ lt_of_lt_of_le (Subgroup.card_lt_of_lt (lt_of_le_of_ne hT' hne))
        (Subgroup.card_le_of_le hT₁)
    obtain ⟨M₂, T₂, h₂, hT₂, hmin₂, hor⟩ := ih _ hlt (L ⊔ T') T' h' rfl
    exact ⟨M₂, T₂, h₂, hT₂.trans (hT'.trans hT₁), hmin₂, hor⟩

end Descent

section C1B

open CFSG.Quasithin.MS93.S45

@[expose] def S45C1BTwo : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M T L : Subgroup G) (F : Type) [Field F] [Fintype F]
    (φ : ↥M →* ↥(StatedSL 3 F)) (c : Ctx M T L φ), c.HZV → Fintype.card F = 2 →
    ∀ (p : ℕ → Vtx (puAmalgam c.hyp.le)) (N : ℕ), IsGoodPath _ p N →
    ∀ a : ℕ, Even a → 34 ≤ a → a + 30 ≤ N →
    ¬ Zloc c.hyp.le L (p a) ≤ Hloc c.hyp.le L (p a) →
    stab (puAmalgam c.hyp.le) (p (a + 1)) ≤ Subgroup.normalizer
      ((⁅Qv (puAmalgam c.hyp.le) (p a), Ltil c.hyp.le L (p a)⁆ ⊓
        (Zloc c.hyp.le L (p a) ⊓ Zloc c.hyp.le L (p (a + 2))) : Subgroup _) :
          Set (puAmalgam c.hyp.le).Universal)

end C1B

end CFSG.Quasithin.MS93.MRes
