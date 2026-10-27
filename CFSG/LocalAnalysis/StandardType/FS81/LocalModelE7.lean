module

public import CFSG.LocalAnalysis.StandardType.FS81.LocalModelE7Realized
public import CFSG.LocalAnalysis.StandardType.FS81.RowSplit
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteE7Models
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoBstar

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.Blueprint CFSG.Blueprint.Chevalley
open CFSG.LieType.Chevalley CFSG.LieType.RootSystem
open CFSG.HardMathSupport.Timmesfeld.CrossChar
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem e7_torus_setup
    {G : Type} [Group G] [Finite G] {b₀ : G} {K E : Subgroup G}
    (hstd : StdAssumptions b₀ K E Row.E7) :
    ∃ (e : ↥K ≃* ↥(adjointGroup Tag.E7 (GaloisField 2 1)))
      (A' : Subgroup ↥(adjointGroup Tag.E7 (GaloisField 2 1))),
      Nat.card A' = 3 ^ 7 ∧
      (∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E) ∧
      (∀ g : ↥(adjointGroup Tag.E7 (GaloisField 2 1)),
        (∀ x ∈ A', g * x = x * g) → g ^ 3 = 1 → g ∈ A') ∧
      ∃ (w : GGTorusTorWit 3 7 _ (A'.map (MulAut.conj : _ →* MulAut _)))
        (hcomm : ∀ j k (ζ ξ : Multiplicative (ZMod 3)),
          Commute (w.cor j ζ) (w.cor k ξ)),
        w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇ ∧
        (⨆ k, (w.cor k).range) = A' ∧
        (w.coordHom hcomm).range = A' := by
  obtain ⟨hsimple, hhyp, hcanon⟩ := hstd
  obtain ⟨hA, hmaxE, hb₀E, hEcard, hm7, hbig⟩ := hhyp
  obtain ⟨hb₀, hKC, hKn, hKz, hmark, hcyc, hm23, hweak⟩ := hA
  obtain ⟨hrow, hdisj, hsup, hmaxK, hAcard, hCK⟩ := hcanon
  let A : Subgroup G := E ⊓ K
  have hAK : A ≤ K := hmaxK.1
  obtain ⟨lab, hlabP, hlab⟩ := exists_glaLabel hrow
  obtain ⟨t, r, n⟩ := lab
  have hn1 : n = 1 := hlabP.1
  subst hn1
  have ht : t = .E7 := by
    obtain ⟨-, hcases⟩ := hlabP
    rcases hcases with ⟨h, -⟩ | ⟨h, -⟩ | ⟨-, h, -⟩
    · exact absurd h (by decide)
    · exact absurd h (by decide)
    · exact h
  obtain ⟨φ⟩ := exists_mulEquiv_adjointGroup_of_isLabel_E7' (lab := ⟨t, r, 1⟩) hlab ht hKz
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  have hm : Nat.card (GaloisField 2 1) + 1 = 3 := by omega
  let A' : Subgroup ↥(adjointGroup Tag.E7 (GaloisField 2 1)) := (A.subgroupOf K).map φ.toMonoidHom
  have hA' : IsElemAbelian 3 A' := (hmaxK.2.1.subgroupOf K).map φ.toMonoidHom
  have hA'card : Nat.card A' = 3 ^ 7 := by
    rw [Subgroup.card_map_of_injective φ.injective,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hmaxK.1).toEquiv, hAcard,
      show Row.E7.n = 7 from rfl]
  have hA'card6 : 3 ^ 6 ≤ Nat.card A' := by rw [hA'card]; norm_num
  have hEE : ∀ x : ↥K, φ x ∈ A' ↔ (x : G) ∈ E := by
    intro x
    constructor
    · rintro ⟨a, ha, hax⟩
      have hax' : a = x := φ.injective hax
      subst hax'
      exact (Subgroup.mem_subgroupOf.mp ha).1
    · intro hxE
      exact ⟨x, Subgroup.mem_subgroupOf.mpr ⟨hxE, x.2⟩, rfl⟩
  have hSC : ∀ g : ↥(adjointGroup Tag.E7 (GaloisField 2 1)),
      (∀ x ∈ A', g * x = x * g) → g ^ 3 = 1 → g ∈ A' := by
    intro g hg hg3
    have hgK : ((φ.symm g : ↥K) : G) ∈ K := (φ.symm g).2
    have hgcent : ((φ.symm g : ↥K) : G) ∈ Subgroup.centralizer (A : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have haK : a ∈ K := hAK ha
      have hmem : φ ⟨a, haK⟩ ∈ A' :=
        ⟨⟨a, haK⟩, Subgroup.mem_subgroupOf.mpr ha, rfl⟩
      have hcomm : g * φ ⟨a, haK⟩ = φ ⟨a, haK⟩ * g := hg _ hmem
      have h := congrArg (fun z : ↥K => (z : G)) (congrArg φ.symm hcomm)
      simpa using h.symm
    have hgin : ((φ.symm g : ↥K) : G) ∈ A := by
      have hmem : ((φ.symm g : ↥K) : G) ∈ Subgroup.centralizer (A : Set G) ⊓ K :=
        ⟨hgcent, hgK⟩
      rwa [hCK] at hmem
    exact ⟨φ.symm g, Subgroup.mem_subgroupOf.mpr hgin, φ.apply_symm_apply g⟩
  have hq : 3 ∣ Nat.card (GaloisField 2 1) + 1 := by norm_num [hGF]
  have hdata := ggTorusTorData_E7_plus (K := GaloisField 2 1) (p := 3)
    Nat.prime_three (by norm_num) hq A' hA' hA'card6 hSC
  have hdata3 : GGTorusTorData 3 7 (CartanMatrix.E 7) CoxeterMatrix.E₇
      (↥(adjointGroup Tag.E7 (GaloisField 2 1))) (A'.map (MulAut.conj : _ →* MulAut _)) :=
    hm ▸ hdata
  obtain ⟨w, hw⟩ := hdata3
  have hwkeep : w.Holds (CartanMatrix.E 7) CoxeterMatrix.E₇ := hw
  obtain ⟨-, hAT, hcorT, hαmul, hcorinj, hcomm, hTfix, hpair, -, -, -, -, hinner, -⟩ := hw
  have hAle : A' ≤ (w.coordHom hcomm).range := by
    rw [w.coordHom_range hcomm]
    intro a ha
    have hconja : MulAut.conj a ∈ A'.map (MulAut.conj : _ →* MulAut _) := ⟨a, ha, rfl⟩
    obtain ⟨t, ht, hat⟩ := hinner _ hconja ⟨a, rfl⟩
    exact (mulAut_conj_injective center_adjointGroup_eq_bot hat).symm ▸ ht
  have hdom : Nat.card (Multiplicative (Fin 7 → ZMod 3)) = 3 ^ 7 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  have hrange_card : Nat.card ↥(w.coordHom hcomm).range ≤ 3 ^ 7 := by
    rw [← hdom]
    exact Nat.card_le_card_of_surjective _ (MonoidHom.rangeRestrict_surjective _)
  have htor : (⨆ k, (w.cor k).range) = A' := by
    rw [← w.coordHom_range hcomm]
    exact (Subgroup.eq_of_le_of_card_ge hAle (by rw [hA'card]; exact hrange_card)).symm
  exact ⟨φ, A', hA'card, hEE, hSC, w, hcomm, hwkeep, htor,
    (w.coordHom_range hcomm).trans htor⟩


theorem l1LocalAt_E7
    : L1LocalAt Row.E7 := by
  intro G _ _ b₀ K E hstd
  have hstd' : StdAssumptions b₀ K E Row.E7 := hstd
  obtain ⟨-, hhyp, hcanon⟩ := hstd
  obtain ⟨hA, -, -, -, -, -⟩ := hhyp
  obtain ⟨hb₀, hKC, hKn, hKz, -, -, -, -⟩ := hA
  obtain ⟨-, -, hsup, -, -, -⟩ := hcanon
  obtain ⟨e, A', hA'card, hEE, -, w, hcomm, hw, htor, -⟩ := e7_torus_setup hstd'
  have hcardTau : Nat.card ↥(⨆ k, (w.cor k).range) = 3 ^ 7 := by
    rw [htor]
    exact hA'card
  have hτ : Function.Injective (w.e7Tau hcomm) :=
    GGTorusTorWit.e7Tau_injective w hcomm hcardTau
  have hdisj : Disjoint (Subgroup.zpowers b₀) K := by
    rw [Subgroup.disjoint_def]
    intro x hx hxK
    have hxZ : (⟨x, hxK⟩ : ↥K) ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hc : Commute b₀ (y : G) :=
        (Subgroup.mem_centralizer_singleton_iff.mp (hKC y.2)).symm
      exact Subtype.ext (hc.zpow_left z).eq.symm
    rw [hKz] at hxZ
    have hx1 : (⟨x, hxK⟩ : ↥K) = 1 := Subgroup.mem_bot.mp hxZ
    simpa using congrArg Subtype.val hx1
  have hEK : ∀ x : ↥K, (x : G) ∈ E ↔ e x ∈ (w.e7Tau hcomm).range := by
    intro x
    rw [GGTorusTorWit.e7Tau_range w hcomm, htor]
    exact (hEE x).symm
  let B : Basis3 G 8 := torusBasis e hτ hb₀ hKC hdisj
  have hadapted : Adapted B b₀ K E :=
    torusBasis_adapted e hτ hb₀ hKC hdisj hEK hsup
  have hspan : B.span = E := hadapted.1
  have hA'E : ∀ x : ↥K, e x ∈ A' ↔ (x : G) ∈ E := hEE
  have hKN : Subgroup.centralizer ({b₀} : Set G) ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKC).mp hKn
  have hK2 : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 (by omega)
  have hOut : ∀ φ : MulAut ↥(adjointGroup Tag.E7 (GaloisField 2 1)),
      φ ∈ (MulAut.conj : ↥(adjointGroup Tag.E7 (GaloisField 2 1)) →*
        MulAut ↥(adjointGroup Tag.E7 (GaloisField 2 1))).range :=
    fun φ => TableBExcTwo.mem_range_conj_adjoint (Or.inl rfl) hK2 φ
  have hZ : Subgroup.center ↥(adjointGroup Tag.E7 (GaloisField 2 1)) = ⊥ :=
    center_adjointGroup_eq_bot
  have hrange : (w.e7Tau hcomm).range = A' :=
    (GGTorusTorWit.e7Tau_range w hcomm).trans htor
  obtain ⟨eW, -⟩ : ∃ eW : (CoxeterMatrix.E₇).Group ≃* ↥(e7FrameAut A'), True := by
    obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hAutGroup⟩ := hw
    exact ⟨hAutGroup.choose, trivial⟩
  have hAutCard : Nat.card ↥(e7FrameAut A') = 2903040 :=
    card_e7FrameAut_eq_2903040 (L' := ↥(adjointGroup Tag.E7 (GaloisField 2 1))) ⟨eW⟩
  have hcardB : Nat.card ↥(B.realized (Subgroup.centralizer ({b₀} : Set G))) = 2903040 :=
    card_realized_centralizer (E := E) hw hKN hOut hZ hrange hspan hA'E hAutCard
  have hcardCl : Nat.card ↥(Submonoid.closure (Set.range e7LocalGen)) = 2903040 :=
    card_closure_eq_2903040 (E := E) hw hKN hOut hZ hrange hspan hA'E hAutCard
  have hEq : B.realized (Subgroup.centralizer ({b₀} : Set G)) =
      (Submonoid.closure (Set.range e7LocalGen) :
        Set (Matrix (Fin 8) (Fin 8) (ZMod 3))) :=
    realized_centralizer_eq_closure (E := E) hw hKN hOut hZ hrange hspan hA'E
  have hclause3 : B.realized (Subgroup.centralizer ({b₀} : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers (B.b 1) : Set G)) =
      spSet fun σ s => σ 0 = 0 ∧ s 0 = 1 ∧ σ 1 = 1 ∧ ∏ i : Fin 6, s i.succ.succ = 1 := by
    rw [Basis3.realized_inf_normalizer_zpowers, hEq]
    exact e7Local_stab (by rw [hcardCl])
  have hclause2 : B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G)) =
        B.realized (Subgroup.centralizer ({b₀} : Set G)) ∨
      Nat.card ↥(B.realized (Subgroup.normalizer (Subgroup.zpowers b₀ : Set G))) =
        2 * 2903040 := by
    rcases realized_normalizer_eq_or_card_eq_two B b₀ hb₀
      (torusBasis_b_zero e hτ hb₀ hKC hdisj) with h | h
    · exact Or.inl h
    · right
      rw [h, hcardB]
  exact ⟨B, hadapted, hcardB, hclause2, hclause3⟩

end CFSG.StandardType.FrameRoute.FS81

end
