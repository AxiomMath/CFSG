module

public import CFSG.RankThree.PartTwo.Sec21.Item22Statements
public import CFSG.RankThree.PartTwo.Sec21.Theorem236
public import CFSG.RankThree.GF2n.Item310
import CFSG.RankThree.Classical2.UnitarySplitPrimeRank
import CFSG.RankThree.GF2n.Tim78Normal
import CFSG.RankThree.PartTwo.Sec5.Tools
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

@[expose] def Item224Elliptic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A A U c L → Nat.card A = 3 ^ 3 →
    ∀ S : Sylow 2 (Subgroup.centralizer (A : Set G)),
      (S : Subgroup (Subgroup.centralizer (A : Set G))) ≠ ⊥ →
    ∀ M : Subgroup G, IsMaximalTwoLocal M →
      Subgroup.normalizer
          (((S : Subgroup (Subgroup.centralizer (A : Set G))).map
            (Subgroup.centralizer (A : Set G)).subtype : Subgroup G) : Set G) ≤ M →
      U ≤ inSubgroup (CFSG.pCore 2) M → False

namespace Item228ResProof

variable {G : Type} [Group G] [Finite G]

theorem card_eq_of_mem_centralizer {A E U L : Subgroup G} {c : G}
    (hpair : Sec21Pair G A E U c L) {u : G} (hu : orderOf u = 2)
    (huA : u ∈ Subgroup.centralizer (A : Set G)) : Nat.card A = 3 ^ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAe, -, E₀, hE₀, hE₀A⟩ := hpair.mem_S.1
  obtain ⟨k, hk⟩ := (Sec5.isPGroup_of_isElemAbelian hAe).exists_card_eq
  have hAu : A ≤ Subgroup.centralizer ({u} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp huA a ha)
  have hk3 : k ≤ 3 := by
    have h := CFSG.RankThree.Classical2.le_localRank_of_involution_elemAbelian Nat.prime_three hu
      hAu hAe hk
    rwa [hpair.standing.toTheoremFourHyp.localRank_three] at h
  have hk3' : 3 ≤ k := by
    have hdvd : 3 ^ 3 ∣ 3 ^ k := by
      rw [← hk, show (3 : ℕ) ^ 3 = 27 by norm_num, ← hE₀.2.1]
      exact Subgroup.card_dvd_of_le hE₀A
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp hdvd
  rw [hk, show k = 3 by omega]

theorem mem_partTwoE_of_card {A E U L : Subgroup G} {c : G} (hpair : Sec21Pair G A E U c L)
    (hA27 : Nat.card A = 3 ^ 3) : A ∈ partTwoE G := by
  have hEA : E = A := Subgroup.eq_of_le_of_card_ge hpair.mem_E.2
    (by rw [hA27, hpair.mem_E.1.2.1]; norm_num)
  exact hEA ▸ hpair.mem_E.1

theorem exists_fourGroup_le_pCore (h310 : CFSG.RankThree.GF2n.Item3_10_small)
    (hG : PartTwoStanding G) {A : Subgroup G} (hAe : IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    {M : Subgroup G} (hM : IsMaximalTwoLocal M) (hAM : A ≤ M) :
    ∃ U₁ ∈ fourGroups A, U₁ ≤ inSubgroup (CFSG.pCore 2) M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V, -, hVmax⟩ := Finite.exists_le_maximal (p := fun W : Subgroup G => W ≤ M ∧
      M ≤ Subgroup.normalizer (W : Set G) ∧ IsElemAbelian 2 W) (a := ⊥)
    ⟨bot_le, fun m _ => Subgroup.mem_normalizer_iff.mpr fun x => by simp,
      ⟨⟨fun a b => Subsingleton.elim _ _⟩⟩, fun x hx => by rw [Subgroup.mem_bot.mp hx, one_pow]⟩
  obtain ⟨hVM, hMV, hVab⟩ := hVmax.prop
  have hV2 : IsPGroup 2 V := Sec5.isPGroup_of_isElemAbelian hVab
  obtain ⟨k, hk⟩ := hV2.exists_card_eq
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have hVle : Nat.card V ≤ 2 := by
      rw [hk]
      calc 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 2 := by norm_num
    have hTI : ∀ g : G, V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥ ∨
        V ⊓ V.map (MulAut.conj g).toMonoidHom = V := by
      intro g
      by_cases h : V ⊓ V.map (MulAut.conj g).toMonoidHom = ⊥
      · exact Or.inl h
      · refine Or.inr (Subgroup.eq_of_le_of_card_ge inf_le_left ?_)
        have := (Subgroup.one_lt_card_iff_ne_bot _).mpr h
        omega
    exact hG.not_inCatalog (h310 G hG.isSimpleGroup hG.nonabelian hG.kProper hG.charTwoType M hM
      V hVmax hTI hVle)
  obtain ⟨U₁, hU₁, hU₁V⟩ := Sec6.exists_mem_fourGroups_le hAe hA27 hVab
    (by
      rw [hk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk2) (hAM.trans hMV)
  exact ⟨U₁, hU₁, hU₁V.trans (CFSG.RankThree.GF2n.Tim78.le_inSubgroup_pCore hVM hMV hV2)⟩

end Item228ResProof

open Item228ResProof

theorem item224_of (h310 : CFSG.RankThree.GF2n.Item3_10_small) (h612 : Item612Sec21)
    (hEll : Item224Elliptic) : Item224 := by
  intro G _ _ A E U c L hpair
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.centralizer (A : Set G)) :=
    even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hA27 : Nat.card A = 3 ^ 3 := card_eq_of_mem_centralizer hpair
    (by rw [← Subgroup.orderOf_coe] at hu; exact hu) u.2
  have hAE : A ∈ partTwoE G := mem_partTwoE_of_card hpair hA27
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  obtain ⟨S⟩ : Nonempty (Sylow 2 (Subgroup.centralizer (A : Set G))) := inferInstance
  have hS1 : (S : Subgroup (Subgroup.centralizer (A : Set G))) ≠ ⊥ := S.ne_bot_of_dvd_card h2
  set S' : Subgroup G :=
    (S : Subgroup (Subgroup.centralizer (A : Set G))).map (Subgroup.centralizer (A : Set G)).subtype
    with hS'
  have hS'1 : S' ≠ ⊥ := fun h =>
    hS1 ((Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).mp h)
  have hS'2 : IsPGroup 2 S' := S.isPGroup'.map _
  have hAN : A ≤ Subgroup.normalizer (S' : Set G) :=
    (Subgroup.le_centralizer_iff.mp (Subgroup.map_subtype_le _)).trans
      (Subgroup.centralizer_le_normalizer _)
  obtain ⟨M, hM, hSM⟩ := exists_mem_scriptM_of_isTwoLocal (X := (A : Set G))
    (H := Subgroup.normalizer (S' : Set G)) ⟨S', hS'1, hS'2, rfl⟩ fun a ha => hAN ha
  obtain ⟨U₁, hU₁, hU₁M⟩ := exists_fourGroup_le_pCore h310 hpair.standing hAe
    (by rw [hA27]; norm_num) hM.1 (fun a ha => hM.2 ha)
  obtain ⟨⟨c₁, L₁⟩, hcL⟩ := h612 G A hpair.toSec21Std A ⟨hAE, le_rfl⟩ U₁ hU₁
  exact hEll G A U₁ c₁ L₁ ⟨hpair.toSec21Std, ⟨hAE, le_rfl⟩, hU₁, hcL⟩ hA27 S hS1 M hM.1 hSM hU₁M

end CFSG.RankThree.PartTwo.Sec21
