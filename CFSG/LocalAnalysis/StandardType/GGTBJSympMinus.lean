module

public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusSide
public import CFSG.LocalAnalysis.StandardType.GGTBJLabelSides
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitClassical
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Defs
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrEnnola
public import CFSG.LocalAnalysis.StandardType.GGSpJoinBstarSplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB CFSG.HardMathSupport.Solomon.Coordinator

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace SympMinus

theorem not_split_of_dvd_succ {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {lab : LargeEvenLabel}
    (ht : lab.tag = .B ∨ lab.tag = .C) (hpd : p ∣ 2 ^ lab.n + 1) (hn : 2 ≤ lab.n) :
    ¬ LargeEvenSplit p lab := by
  have hun : LargeEvenUntwisted lab.tag := by
    rcases ht with h | h <;> rw [h] <;> trivial
  rintro (⟨-, h1⟩ | ⟨h1, -⟩ | ⟨h1, -⟩ | ⟨h1, -⟩)
  · have h2 : p ∣ 2 := by
      have h3 := Nat.dvd_sub hpd h1
      have e : 2 ^ lab.n + 1 - (2 ^ lab.n - 1) = 2 := by
        have := Nat.one_le_two_pow (n := lab.n)
        omega
      rwa [e] at h3
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)
  · exact h1 hun
  · rcases h1 with h | h <;> rcases ht with h' | h' <;> rw [h'] at h <;> cases h
  · omega

theorem ggLabelIso_symp {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab')
    (ht : lab.tag = .B ∨ lab.tag = .C) : (lab'.tag = .B ∨ lab'.tag = .C) ∧ lab'.n = lab.n := by
  rcases lab with ⟨t, r, n⟩
  rcases lab' with ⟨t', r', n'⟩
  simp only at ht
  unfold GGLabelIso at h
  rcases h with h | h | h | h | h | h | h | h
  · obtain ⟨rfl, rfl, rfl⟩ := LargeEvenLabel.mk.inj h
    exact ⟨ht, rfl⟩
  · exact ⟨h.2.1, h.2.2.2.symm⟩
  all_goals
    exfalso
    rcases ht with rfl | rfl <;> simp_all

theorem labelAll_ge_two {p : ℕ} {lab : LargeEvenLabel}
    (h : (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n) :
    LargeEvenLabelAll lab fun R _ I _ =>
      ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
        (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K m)), 3 ≤ m ∧ 4 ≤ Nat.card K ∧
          p ∣ Nat.card K + 1 ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R) := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, hl, hpn, hn2⟩ := h
  intro Q hQ
  have key : ∀ (_ : LargeEvenRecipeSymplectic l (2 ^ n) false Q),
      LargeEvenRecipeSymplectic l (2 ^ n) false fun R _ I F => Q R I F ∧
        (∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
          (_ : R ≃* LargeEvenProj (LargeEvenSpGroup K m)), 3 ≤ m ∧ 4 ≤ Nat.card K ∧
            p ∣ Nat.card K + 1 ∧ I ⊆ Set.range (MulAut.conj : R →* MulAut R)) := by
    intro hQ'
    obtain ⟨K, _, _, hK, hQK⟩ := hQ'
    have hch : CharP K 2 := charP_two_of_card hK
    have hpq : p ∣ Nat.card K + 1 := by
      rw [hK]
      exact hpn
    have hK4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    exact ⟨K, inferInstance, inferInstance, hK, hQK, l, K, inferInstance, inferInstance, hch,
      MulEquiv.refl _, hl, hK4, hpq, TableBSymp.sp_I_subset_inn⟩
  rcases htag with h | h <;> dsimp only at h <;> subst h <;> exact key hQ

theorem exists_data_of_marking {G : Type} [Group G] {p : ℕ} {Bs X : Subgroup G}
    (hmark : GGInnerDiagOnLabel (fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n) p Bs X) :
    ∃ (m : ℕ) (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2)
      (hN : Bs ≤ Subgroup.normalizer (X : Set G))
      (θ : ↥X ⧸ Subgroup.center ↥X ≃* LargeEvenProj (LargeEvenSpGroup K m)),
      3 ≤ m ∧ 4 ≤ Nat.card K ∧ p ∣ Nat.card K + 1 ∧ commutator ↥X = ⊤ ∧
        ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈
          Set.range (MulAut.conj : LargeEvenProj (LargeEvenSpGroup K m) →*
            MulAut (LargeEvenProj (LargeEvenSpGroup K m))) := by
  classical
  obtain ⟨hXc, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll_simple
    (S := fun lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧ p ∣ 2 ^ lab.n + 1 ∧
      2 ≤ lab.n)
    (fun lab _ hs => nbrC_labelAll_guard (labelAll_ge_two hs)) (fun _ _ _ _ _ _ hP => hP.1) hmark
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBsN, h3I⟩, m, Kf, _, _, _, e, hm3, hK4, hpq, hIinn⟩ :=
    largeEvenRawDatum_exists hraw
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hBsN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hBsN h3I hb
  refine ⟨m, Kf, inferInstance, inferInstance, inferInstance, hBsN, θ.trans e, hm3, hK4, hpq, hXc,
    fun b hb => ?_⟩
  obtain ⟨g, hg⟩ := hIinn (hBsI b hb)
  refine ⟨e g, ?_⟩
  rw [ggLAut_congr X θ (θ.trans e) ⟨b, hBsN hb⟩, ← hg]
  ext z
  simp [MulAut.congr_apply, MulAut.conj_apply]

theorem sympMinus_J_ne_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : J ≠ K := by
  have hp : p.Prime := Fact.out
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hnb.1.2.1
  have hy1 : y ≠ 1 := hnb.1.2.2.1
  intro hJK
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := hH.1.2.2.1.2.2.2.2.2.2
  have hDcard : Nat.card D = p ^ 2 := hH.1.2.2.1.2.2.1
  rw [hJK, inf_centralizer_eq_zpowers_of_sHat hnb.1] at hD
  rw [hD, Nat.card_zpowers, orderOf_eq_prime (hBs.2 y hyBs) hy1] at hDcard
  have : 1 < p := hp.one_lt
  nlinarith

theorem left_false_of_ge_two (hRig : GGLabelRigidInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hL : GGInnerDiagOnLabel (fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n) p Bs L) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨lab₁, hΛ₁, hhas₁, R₁, _, I₁, F₁, θ₁, hP₁⟩ := largeEvenMarking_exists_hasLabel hL
  obtain ⟨⟨ht₁, -, hpd₁, hn₁⟩, -⟩ := hP₁
  have hsplit : LargeEvenMarking ↥L (fun lab _ _ _ _ _ => LargeEvenSplit p lab) :=
    largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.1) hH.1.1.2.2.2.2.2.2.2.1
  obtain ⟨lab₂, hΛ₂, hhas₂, R₂, _, I₂, F₂, θ₂, hs₂⟩ := largeEvenMarking_exists_hasLabel hsplit
  have hiso := hRig lab₁ lab₂ (↥L ⧸ Subgroup.center ↥L) hΛ₁ hΛ₂ hhas₁ hhas₂
  obtain ⟨ht₂, hn₂⟩ := ggLabelIso_symp hiso ht₁
  exact not_split_of_dvd_succ hp hp2 ht₂ (hn₂ ▸ hpd₁) (hn₂ ▸ hn₁) hs₂

theorem ggTBJNbr_sympMinus_of_marking
    (hI3 : GGNbrSubcomponentInput) {G : Type} [Group G] [Finite G]
    {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hmark : GGInnerDiagOnLabel (fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n) p Bs K) :
    GGResSideDatum p Bs K J ∨ GGResLeviSideDatumLE3 p Bs K J := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hnb : GGNbr p B x D J y K := hH.2.2.2.2.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hcfg.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  obtain ⟨m, Kf, _, _, _, hN, θ, hm3, hK4, hpq, hXc, hBsI⟩ := exists_data_of_marking hmark
  haveI : NeZero m := ⟨by omega⟩
  have hxBs : x ∈ Bs := hcfg.tableB_facts.2.2.1
  have hJK : J ≤ K := hI3 G p B x L D J hH.1.1 hH.1.2.2 y K hnb
  have hJcomp : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    ggIsComponentOf_inf_centralizer_nbr hcfg hnb hJK
  rcases ggTBJ_sympMinus_side hp2 hm3 (Or.inl hK4) hpq hBs hSC hN hXc θ hBsI hxBs hJcomp
    hcfg.card_bstar_inf_centralizer_J_le (sympMinus_J_ne_K hH) with h | h | ⟨hK2, -⟩
  · exact Or.inl h
  · exact Or.inr h
  · omega

end SympMinus

theorem ggTBJLeftOn_sympMinus_ge_two (hRig : GGLabelRigidInput) :
    GGTBJLeftOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n := by
  intro G _ _ p B Bs x L D J y K hH hp hL _
  exact (SympMinus.left_false_of_ge_two hRig hH hL).elim

theorem ggTBJNbrOn_sympMinus_ge_two
    (hI3 : GGNbrSubcomponentInput) :
    GGTBJNbrOn fun p lab => (lab.tag = .B ∨ lab.tag = .C) ∧ 3 ≤ lab.rank ∧
      p ∣ 2 ^ lab.n + 1 ∧ 2 ≤ lab.n := by
  intro G _ _ p B Bs x L D J y K hH hp hK _
  rcases SympMinus.ggTBJNbr_sympMinus_of_marking hI3 hH hK with h | h
  · exact Or.inl h
  · exact Or.inr (Or.inl h)

end CFSG.StandardType

end
