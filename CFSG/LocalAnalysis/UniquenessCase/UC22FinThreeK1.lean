module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.LocalAnalysis.UniquenessCase.UC22P22wb
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Ta
import CFSG.LocalAnalysis.UniquenessCase.UC22P22finB
import CFSG.Adapters.Certificate43Check
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitKG
import CFSG.LocalAnalysis.ComponentClassification.HarrisLitPSL
import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListAlt7
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19Defs
import CFSG.LocalAnalysis.SeitzReduction.RankOneCatSL2TwoFixedA5
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsEightK
import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
import CFSG.LocalAnalysis.UniquenessCase.UC22P21e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22r
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rm
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ro
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rp
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rr
import CFSG.Quasithin.Background.C1PackS15212C
import CFSG.Quasithin.Background.C1PackS1531Top
import CFSG.Quasithin.Background.D2
import CFSG.Quasithin.Background.E3
import CFSG.Quasithin.Background.E3Nprime
import CFSG.Quasithin.Background.E3Uniq
import CFSG.Quasithin.Background.GoldschmidtS146RBend1
import CFSG.Quasithin.EmptyFaithful.S14110
import CFSG.Quasithin.EmptyFaithful.S146F4
import CFSG.Quasithin.EmptyFaithful.S152N11
import CFSG.Quasithin.EmptyFaithful.S152UGen
import CFSG.Quasithin.EmptyFaithful.S152Y15
import CFSG.Quasithin.EmptyFaithful.S152Y19
import CFSG.Quasithin.EmptyFaithful.S153E59A
import CFSG.Quasithin.EmptyFaithful.T1531Final
import CFSG.Quasithin.Vol2.Ch10SecB4
import CFSG.Quasithin.Vol2.Ch10StatementsInputs
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS3
import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
import CFSG.Quasithin.Vol2.Ch1EightFourChar2
import CFSG.Quasithin.Vol2.Ch3Sec3L2pSylowNorm
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3312D
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3313Pre
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323B
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3324X
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3329
import CFSG.Quasithin.Vol2.Ch3Sec3Lem3330
import CFSG.RankThree.PartOne.S11d.LieFieldTransfer
import CFSG.RankThree.PartOne.S11d.ThreeCompEasy
import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P22fin3

theorem mem_calC_of_le_normalizer {M X L : Subgroup G} (hL : L ∈ calC M) (hLX : L ≤ X)
    (hXL : X ≤ normalizer (L : Set G)) : L ∈ calC X :=
  ⟨.step hLX ((Subgroup.normal_subgroupOf_iff_le_normalizer hLX).2 hXL) (.refl X), hL.2.1,
    hL.2.2⟩

theorem card_le_pRank_of_finset {X : Subgroup G} {S : Finset (Subgroup G)} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hS : ∀ L ∈ S, L ∈ calC X)
    (hZ : ∀ L ∈ S, ¬ q ∣ Nat.card (center (Bar2 L))) (hd : ∀ L ∈ S, q ∣ Nat.card L) :
    S.card ≤ CFSG.Open.pRank q X := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hg : ∀ L : S, ∃ g : G, g ∈ (L : Subgroup G) ∧ orderOf g = q := fun L => by
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(L : Subgroup G)) q (hd L L.2)
    exact ⟨x, x.2, (Subgroup.orderOf_coe x).trans hx⟩
  choose g hgL hgq using hg
  have hLX : ∀ L : S, (L : Subgroup G) ≤ X := fun L => (hS L L.2).1.le
  have hgX : ∀ L : S, zpowers (g L) ≤ X := fun L => (zpowers_le.2 (hgL L)).trans (hLX L)
  have hC := fun L : S => UC6S846.calC_subgroupOf (hS L L.2)
  obtain ⟨W, hWel, hWcard⟩ := UC6S898.rank_sum_of_family (Y := ↥X) (ι := S)
    (A := fun L => (L : Subgroup G).subgroupOf X) (E := fun L => (zpowers (g L)).subgroupOf X)
    (a := fun _ => 1) hq hq2 (fun L => (hC L).1) (fun L => (hC L).2.1) (fun L => (hC L).2.2.1)
    (fun L L' h => Subtype.ext <| by
      have h' : ((L : Subgroup G).subgroupOf X).map X.subtype =
          ((L' : Subgroup G).subgroupOf X).map X.subtype := congrArg _ h
      rwa [Subgroup.map_subgroupOf_eq_of_le (hLX L), Subgroup.map_subgroupOf_eq_of_le (hLX L')]
        at h')
    (fun L => by rw [(hC L).2.2.2]; exact hZ L L.2)
    (fun L _ hx => zpowers_le.2 (hgL L) hx)
    (fun L => (CFSG.Open.isElemAbelian_zpowers
      (by rw [← hgq L]; exact pow_orderOf_eq_one _)).subgroupOf X)
    (fun L => by
      show Nat.card ((zpowers (g L)).subgroupOf X) = q ^ 1
      rw [pow_one, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hgX L)).toEquiv,
        Nat.card_zpowers, hgq L])
    Finset.univ
  have hsum : (∑ L ∈ (Finset.univ : Finset S), (fun _ : S => 1) L) = S.card := by simp
  rw [hsum] at hWcard
  exact UC6S846.le_pRank' hq (Subgroup.map_subtype_le W) (hWel.map X.subtype)
    (by rw [Subgroup.card_map_of_injective X.subtype_injective, hWcard])

theorem hyp81_of_three_isL2 {M L₁ L₂ L₃ : Subgroup G} (h₁ : L₁ ∈ calC M) (h₂ : L₂ ∈ calC M)
    (h₃ : L₃ ∈ calC M) (h12 : L₁ ≠ L₂) (h13 : L₁ ≠ L₃) (h23 : L₂ ≠ L₃) {a₁ a₂ a₃ : ℕ}
    (s₁ : IsL2 (Bar2 L₁) a₁) (s₂ : IsL2 (Bar2 L₂) a₂) (s₃ : IsL2 (Bar2 L₃) a₃) :
    F08.Hyp81 M (L₁ ⊔ L₂ ⊔ L₃) := by
  classical
  have hle₁ : L₁ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_left.trans le_sup_left
  have hle₂ : L₂ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right.trans le_sup_left
  have hle₃ : L₃ ≤ L₁ ⊔ L₂ ⊔ L₃ := le_sup_right
  have hN : ∀ {A B : Subgroup G}, A ∈ calC M → B ∈ calC M → B ≤ normalizer (A : Set G) := by
    intro A B hA hB
    by_cases hAB : A = B
    · subst hAB
      exact Subgroup.le_normalizer
    · exact PartTwo.calC_le_normalizer_of_ne hA hB hAB
  have hS : ∀ L ∈ ({L₁, L₂, L₃} : Finset (Subgroup G)),
      L ∈ calC M ∧ L ≤ L₁ ⊔ L₂ ⊔ L₃ ∧ ∃ a, IsL2 (Bar2 L) a := by
    simp only [Finset.mem_insert, Finset.mem_singleton]
    rintro L (rfl | rfl | rfl)
    exacts [⟨h₁, hle₁, a₁, s₁⟩, ⟨h₂, hle₂, a₂, s₂⟩, ⟨h₃, hle₃, a₃, s₃⟩]
  have h3 := card_le_pRank_of_finset (X := L₁ ⊔ L₂ ⊔ L₃) Nat.prime_three (by norm_num)
    (fun L hL => mem_calC_of_le_normalizer (hS L hL).1 (hS L hL).2.1
      (sup_le (sup_le (hN (hS L hL).1 h₁) (hN (hS L hL).1 h₂)) (hN (hS L hL).1 h₃)))
    (fun L hL => by
      obtain ⟨a, ha⟩ := (hS L hL).2.2
      rw [P22y.center_eq_bot_of_isL2Ev (P22fin.isL2Ev_of_isL2 ha).1, Subgroup.card_bot]
      norm_num)
    (fun L hL => by
      obtain ⟨a, ha⟩ := (hS L hL).2.2
      exact PartTwo.S17.three_dvd_card_of_bar_isL2Even ha)
  rw [Finset.card_eq_three.2 ⟨L₁, L₂, L₃, h12, h13, h23, rfl⟩] at h3
  exact ⟨PartTwo.isSubnormal_sup_sup h₁ h₂ h₃, PartTwo.commutator_sup_sup h₁ h₂ h₃, by omega,
    Or.inr ⟨L₁, L₂, L₃, h₁, h₂, h₃, PartTwo.S17.pRank_three_eq_one_of_isL2 s₁,
      PartTwo.S17.pRank_three_eq_one_of_isL2 s₂, PartTwo.S17.pRank_three_eq_one_of_isL2 s₃,
      hle₁, hle₂, hle₃, PartTwo.coe_sup_sup_eq_mul h₁ h₂ h₃ h12 h13 h23⟩⟩

theorem exists_isL2_bar2 (D : Data G) {Ch : Choice2011 G} (h17 : S21_17 D Ch)
    (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hKn : ¬ D.M ≤ normalizer (K : Set G)) {n : ℕ} (hL2 : IsL2 ↥(mbarImage D.M c.V K) n) :
    ∃ a, IsL2 (Bar2 K) a := by
  have hKM : K ≤ D.M := hK.1.le
  have h3 : 3 ∣ Nat.card ↥(mbarImage D.M c.V K) := three_dvd_card_of_isL2 hL2
  have hKV : ¬ K ≤ centralizer (c.V : Set G) := fun h => by
    rw [← uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM] at h
    rw [h, Subgroup.card_bot] at h3
    norm_num at h3
  have hOV : CFSG.Open.pCoreOf 2 D.M ≤ centralizer (c.V : Set G) :=
    (Subgroup.le_centralizer_iff.1 ((uc22p22c_U_facts D).1.trans inf_le_right)).trans
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 c.hVU))
  obtain ⟨ψ, hψs, hψk, -⟩ := uc22p2213t_onto c.hVM hKM
    (fun x hx => hOV (uc22p22r_pCoreOf_le_of_isSubnormal hK.1 ⟨x, hx, rfl⟩)) hK.2.2 hKV
  rcases h17 h1930 c.toCtx21 K hK with hcl | ⟨-, a, -, ha | ha⟩ | ⟨-, hJ, -⟩
  · have h := PartTwo.TwelveTwentyThree.le_normalizer_conjClosure D.M K
    rw [← hcl] at h
    exact absurd h hKn
  · exact ⟨a, ha⟩
  · exact absurd (h3.trans (Subgroup.card_dvd_of_surjective hψs))
      (CFSG.LocalAnalysis.EvenBN.GMSK.not_three_dvd_card_of_lieModel_twistedB2 ha)
  · haveI : IsSimpleGroup (Bar2 K) := (kJ1_holds (Bar2 K) hJ).2.1
    obtain ⟨e⟩ := P22w.mulEquiv_of_isSimpleGroup hK.2.2 ψ hψs hψk
    obtain ⟨e₀⟩ := hJ
    exact absurd hL2 (not_isL2_of_isJ1 (X := ↥(mbarImage D.M c.V K)) ⟨e.symm.trans e₀⟩)

theorem isStronglyPEmbedded_three_of_sup (D : Data G) {Ch : Choice2011 G} (h82 : F08.R82 D)
    (h17 : S21_17 D Ch) (h1930 : H1930 D) (c : Ctx22b D Ch) {K : Subgroup G}
    (hK : K ∈ calC D.M) {n : ℕ} (hL2 : IsL2 ↥(mbarImage D.M c.V K) n) {t : G} (htM : t ∈ D.M)
    (htN : t ∉ normalizer (K : Set G)) {Y : Subgroup G} (hY : Y ∈ calC D.M)
    (hYV : Y ≤ centralizer (c.V : Set G)) {m : ℕ} (hm : 2 ≤ m)
    (eY : Bar2 Y ≃* CFSG.Open.StatedSL 2 (GaloisField 2 m)) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
  have hKM : K ≤ D.M := hK.1.le
  have hMt : D.M.map (MulAut.conj t).toMonoidHom = D.M :=
    UC6S846.mem_normalizer_iff_map_conj.1 (Subgroup.le_normalizer htM)
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ calC D.M := UC6S846.calC_map D.M _ hMt hK
  have hne : K ≠ K.map (MulAut.conj t).toMonoidHom :=
    fun h => htN (UC6S846.mem_normalizer_iff_map_conj.2 h.symm)
  obtain ⟨a, ha⟩ := exists_isL2_bar2 D h17 h1930 c hK (fun h => htN (h htM)) hL2
  have hat : IsL2 (Bar2 (K.map (MulAut.conj t).toMonoidHom)) a := by
    unfold IsL2 at ha ⊢
    exact CFSG.Blueprint.LieModel.of_mulEquiv (UC6S846.bar2Equiv
      (K.equivMapOfInjective (MulAut.conj t).toMonoidHom (MulAut.conj t).injective)) ha
  have hYs : IsL2 (Bar2 Y) m := uc22p22d_isL2_of_statedSL hm (GaloisField.card 2 m (by omega)) eY
  have hK1 : mbarImage D.M c.V K ≠ ⊥ := fun h => by
    have h3 := three_dvd_card_of_isL2 hL2
    rw [h, Subgroup.card_bot] at h3
    norm_num at h3
  have hYK : K ≠ Y := fun h =>
    hK1 ((uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM).2 (by rw [h]; exact hYV))
  have hYKt : K.map (MulAut.conj t).toMonoidHom ≠ Y := fun h => by
    apply hK1
    have h0 : mbarImage D.M c.V (K.map (MulAut.conj t).toMonoidHom) = ⊥ :=
      (uc22br4_mbarImage_eq_bot_iff D.M c.V _ c.hVM hKt.1.le).2 (by rw [h]; exact hYV)
    rw [P22fin.mbarImage_conj htM hKM] at h0
    exact (Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj _).injective).1 h0
  exact h82 _ (hyp81_of_three_isL2 hK hKt hY hne hYK hYKt ha hat hYs)

end P22fin3

end CFSG.LocalAnalysis.UniquenessCase.UC22
