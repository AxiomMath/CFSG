module

public import CFSG.RankThree.PartTwo.Sec21.Item232
public import CFSG.RankThree.PartTwo.KFacts.KS21Terminal
public import CFSG.RankThree.PartTwo.Sec21.Item231
public import CFSG.RankThree.PartTwo.Sec21.Item23Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Open (GLBStronglyEmbedded)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

theorem exists_le_card_three [Finite G] {B : Subgroup G} (hBe : IsElemAbelian 3 B)
    (hB1 : B ≠ ⊥) : ∃ B₀ : Subgroup G, B₀ ≤ B ∧ Nat.card B₀ = 3 := by
  obtain ⟨b, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hB1
  refine ⟨Subgroup.zpowers (b : G), (Subgroup.zpowers_le).mpr b.2, ?_⟩
  rw [Nat.card_zpowers]
  exact orderOf_eq_prime (hBe.2 b b.2) (fun h => hb1 (Subtype.ext h))

theorem rank3II_23_3_of_centralizers [Finite G] {A I : Subgroup G} (P : Sylow 3 G)
    (hAP : A ≤ P) (hPI : (P : Subgroup G) ≤ I) (hAe : IsElemAbelian 3 A) (hA1 : A ≠ ⊥)
    (hJ : (CFSG.elemThompson (P : Subgroup G) 3).map (P : Subgroup G).subtype = A)
    (hW : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (I : Set G))
    (hN : Subgroup.normalizer (I : Set G) ≠ ⊤)
    (hfuse : ∀ B : Subgroup G, B ≤ P → IsElemAbelian 3 B → B ≠ ⊥ →
      ∃ i ∈ I, B.map (MulAut.conj i).toMonoidHom ≤ A)
    (hcent : ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ Subgroup.normalizer (I : Set G)) :
    GLBStronglyEmbedded 3 (Subgroup.normalizer (I : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set M := Subgroup.normalizer (I : Set G)
  have hIM : I ≤ M := Subgroup.le_normalizer
  have hPM : (P : Subgroup G) ≤ M := hPI.trans hIM
  have huniq := unique_of_elemThompson_eq P hAe hJ
  have hpM : 3 ∣ Nat.card M := by
    obtain ⟨B₀, hB₀A, hB₀⟩ := exists_le_card_three hAe hA1
    rw [← hB₀]
    exact Subgroup.card_dvd_of_le ((hB₀A.trans hAP).trans hPM)
  refine glbStronglyEmbedded_of_elemAbelian hN hpM (P.subtype hPM) fun B hB hBe hB1 => ?_
  have hBP : B ≤ P := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := hB hx
    rw [Sylow.coe_subtype] at hy
    exact Subgroup.mem_subgroupOf.mp hy
  obtain ⟨i, hiI, hiB⟩ := hfuse B hBP hBe hB1
  set B' := B.map (MulAut.conj i).toMonoidHom
  have hB'e : IsElemAbelian 3 B' := isElemAbelian_map hBe _
  have hB'1 : B' ≠ ⊥ := fun hb =>
    hB1 ((Subgroup.map_eq_bot_iff_of_injective B (MulAut.conj i).injective).mp hb)
  obtain ⟨B₀, hB₀B', hB₀⟩ := exists_le_card_three hB'e hB'1
  have hC' : Subgroup.centralizer (B' : Set G) ≤ M :=
    (Subgroup.centralizer_le hB₀B').trans (hcent B₀ (hB₀B'.trans hiB) hB₀)
  have hN' : Subgroup.normalizer (B' : Set G) ≤ M :=
    normalizer_le_of_centralizer_le hAe huniq hiB hC' hW
  intro y hy
  have hy' : i * y * i⁻¹ ∈ Subgroup.normalizer (B' : Set G) := by
    rw [← Subgroup.map_equiv_normalizer_eq B (MulAut.conj i)]
    exact ⟨y, hy, rfl⟩
  have hiM : i ∈ M := hIM hiI
  have := M.mul_mem (M.mul_mem (M.inv_mem hiM) (hN' hy')) hiM
  simpa [mul_assoc] using this

@[expose] def Item233Centralizers : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      Subgroup.centralizer (B : Set G) ≤ nGroup A

theorem exists_conj_le_of_fusedIntoJ {I : Subgroup G} (hI : KFacts.KS21.ElemAbelianFusedIntoJ I)
    (Q : Sylow 3 I) {B : Subgroup G} (hB : B ≤ (Q : Subgroup I).map I.subtype)
    (hBe : IsElemAbelian 3 B) :
    ∃ i ∈ I, B.map (MulAut.conj i).toMonoidHom ≤
      (CFSG.elemThompson ((Q : Subgroup I).map I.subtype) 3).map
        ((Q : Subgroup I).map I.subtype).subtype := by
  have hBI : B ≤ I := hB.trans (Subgroup.map_subtype_le _)
  have hBQ : B.subgroupOf I ≤ (Q : Subgroup I) := by
    intro x hx
    obtain ⟨y, hy, hyx⟩ := hB (Subgroup.mem_subgroupOf.mp hx)
    rwa [show y = x from Subtype.ext hyx] at hy
  obtain ⟨x, hx⟩ := hI Q (B.subgroupOf I) hBQ (isElemAbelian_subgroupOf hBe I)
  refine ⟨x, x.2, ?_⟩
  rw [map_elemThompson_map_subtype]
  rintro _ ⟨b, hb, rfl⟩
  have h1 : (MulAut.conj x) ⟨b, hBI hb⟩ ∈
      ((CFSG.elemThompson (Q : Subgroup I) 3).map (Q : Subgroup I).subtype) :=
    hx ⟨⟨b, hBI hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  exact ⟨_, h1, by simp [MulAut.conj_apply]⟩

theorem rank3II_23_3_of (h231 : Item231) (h232 : Item232)
    (hfuse : KFacts.KS21.TerminalFusion) (hcent : Item233Centralizers) : Item233 := by
  intro G _ _ A E U c L hpair
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hG := hpair.standing
  have hconc := h231 G A E U c L hpair
  obtain ⟨hAI, h2⟩ := h232 G A E U c L hpair
  have hN := nGroup_ne_top_of_item231Concl hG hconc
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hAp : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  obtain ⟨Q, hQ⟩ := (hAp.comap_subtype (K := iGroup A)).exists_le_sylow
  have hAQ : A ≤ (Q : Subgroup (iGroup A)).map (iGroup A).subtype := by
    intro a ha
    exact ⟨⟨a, hAI ha⟩, hQ (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
  obtain ⟨-, hJ, hW, S, hS⟩ := h2 Q hAQ
  have hT : KFacts.KS21.IsTerminalGroup (iGroup A) := by
    rcases hconc with ⟨he, -⟩ | ⟨he, -⟩ | ⟨he, -⟩
    · exact Or.inl he
    · exact Or.inr (Or.inl he)
    · exact Or.inr (Or.inr he)
  have hF := hfuse (iGroup A) hT
  have hA1 : A ≠ ⊥ := by
    obtain ⟨E', hE', hE'A⟩ := hpair.mem_S.1.2.2
    intro hb
    have h27 := hE'.2.1
    rw [hb, le_bot_iff] at hE'A
    rw [hE'A, Subgroup.card_bot] at h27
    omega
  have hJ' : (CFSG.elemThompson (S : Subgroup G) 3).map (S : Subgroup G).subtype = A := by
    rw [hS]; exact hJ
  refine rank3II_23_3_of_centralizers S (hS ▸ hAQ) (hS ▸ Subgroup.map_subtype_le _) hAe hA1 hJ'
    hW hN ?_ (hcent G A E U c L hpair)
  intro B hB hBe hB1
  obtain ⟨i, hi, hiB⟩ := exists_conj_le_of_fusedIntoJ hF Q (by rw [← hS]; exact hB) hBe
  exact ⟨i, hi, hiB.trans (le_of_eq hJ)⟩

end CFSG.RankThree.PartTwo.Sec21
