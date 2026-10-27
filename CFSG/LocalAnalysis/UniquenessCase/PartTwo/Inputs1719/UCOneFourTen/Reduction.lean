module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.Core
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight90S5
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.Star
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.OTwo
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.QuotientBasic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.QuotientStar
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.QuotientCent
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.AlmostSimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.Component

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)

theorem isSubnormal_top_of_core (hKSch : UCK.KSch) (hcore : UC1_4_10Core) {X : Type} [Group X]
    [Finite X] {Ls Ts Ys : Subgroup X} {n : ℕ} (hKX : CFSG.Open.IsKGroup X)
    (hpX : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (hO2X : CFSG.pCore 2 X = ⊥) (hLsp : ⁅Ls, Ls⁆ = Ls) (hSzs : IsSz (Bar2 Ls) n)
    (hLO : ⁅Ls, CFSG.oddCore X⁆ = ⊥)
    (hstarX : ∀ As : Subgroup X, As ≤ Ls → (Nat.card As).Prime → Nat.card As ≠ 2 →
      normalizer (As : Set X) ≤ normalizer (Ls : Set X))
    (hAX : ∀ As : Subgroup X, As ≤ Ls → (Nat.card As).Prime → Nat.card As ≠ 2 →
      normalizer (As : Set X) ≤ Ys)
    (hTsL : Ts ≤ normalizer (Ls : Set X)) (hTs2 : IsPGroup 2 Ts) (hYs : Ys ≠ ⊤)
    (hLY : CFSG.Open.IsSubnormal Ls Ys) (hSyl : IsSylowOf 2 Ts (F08.CentOverO2 Ys Ls))
    (hNT : normalizer (Ts : Set X) ≤ Ys)
    (hT2 : ∀ X₁ : Subgroup X, X₁ ≠ ⊤ → Ls ≤ X₁ → Ts ≤ X₁ → CFSG.Open.IsSubnormal Ls X₁) :
    CFSG.Open.IsSubnormal Ls ⊤ := by
  have hLs1 : Ls ≠ ⊥ := UC410.ne_bot_of_isSz hSzs
  obtain ⟨Ks, hKsq, hKss, hLKs⟩ :=
    UC410.exists_component_le hKSch hKX hpX hO2X hLsp hSzs hLO hstarX
  have hTsK : Ts ≤ normalizer (Ks : Set X) :=
    hTsL.trans (UC410.le_normalizer_of_le_component hKsq hKss hLKs hLsp hLs1)
  by_cases hX₁ : Ks ⊔ Ts = ⊤
  · exfalso
    have hKsn : Ks.Normal := by
      have hN : Ks ⊔ Ts ≤ normalizer (Ks : Set X) := sup_le le_normalizer hTsK
      rw [hX₁] at hN
      exact normalizer_eq_top_iff.mp (eq_top_iff.mpr hN)
    have hCK := UC410.centralizer_le_of_sup_eq_top hO2X hKsn hTs2 hX₁
    exact hcore X Ks Ls Ts Ys n hKX hpX hO2X hKsq hKsn hCK hX₁ hLKs hLsp hSzs hYs hLY hSyl hNT
      hAX hT2
  · have h1 := hT2 (Ks ⊔ Ts) hX₁ (hLKs.trans le_sup_left) le_sup_right
    have h2 : CFSG.Open.IsSubnormal Ls Ks := UC410.isSubnormal_mono h1 hLKs le_sup_left
    have h3 : Ls = Ks := UC410.eq_of_isSubnormal_of_le hKsq hLsp hLs1 h2
    exact h3 ▸ hKss

theorem isSubnormal_of_lt (h5d3 : PartOne.Section8.Lemma5d3_890) (hK318 : UCK.K318)
    (hKSch : UCK.KSch) (hcore : UC1_4_10Core) {G : Type} [Group G] [Finite G]
    {H M L R : Subgroup G} {n : ℕ} (hK : CFSG.Open.IsKGroup ↥H) (heM : S17.eM H ≤ 3)
    (hMH : M ≤ H) (hL : L ∈ calC M) (hSz : IsSz (Bar2 L) n)
    (hR : IsSylowOf 2 R (F08.CentOverO2 M L)) (hNR : H ⊓ normalizer (R : Set G) ≤ M)
    (hA : ∀ A : Subgroup G, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
      H ⊓ normalizer (A : Set G) ≤ M) (hMH' : M ≠ H)
    (hIH : ∀ H₁ : Subgroup G, H₁ < H → CFSG.Open.pCoreOf 2 H ≤ H₁ → L ≤ H₁ → R ≤ H₁ →
      CFSG.Open.IsSubnormal L H₁) :
    CFSG.Open.IsSubnormal L H := by
  have hRC : R ≤ F08.CentOverO2 M L := by
    obtain ⟨P, rfl⟩ := hR
    exact map_subtype_le _
  have hRM : R ≤ M := hRC.trans (UC410.centOverO2_le M L)
  have hRL : R ≤ normalizer (L : Set G) := hRC.trans (UC410.centOverO2_le_normalizer M L)
  have hQR : CFSG.Open.pCoreOf 2 H ≤ R := UC410.pCoreOf_le_of_isSylowOf hMH hL hR hNR
  have hQM : CFSG.Open.pCoreOf 2 H ≤ M := hQR.trans hRM
  have hLH : L ≤ H := hL.1.le.trans hMH
  have hRH : R ≤ H := hRM.trans hMH
  have hR2 : IsPGroup 2 ((R.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) := by
    obtain ⟨P, rfl⟩ := hR
    exact ((P.isPGroup'.map _).of_equiv (subgroupOfEquivOfLe hRH).symm).map _
  have hsub : ∀ {A B : Subgroup G}, A ≤ B → A.subgroupOf H ≤ B.subgroupOf H :=
    fun h _ hx => h hx
  have hlift : ∀ As : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H),
      As ≤ (L.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) →
      (Nat.card As).Prime → Nat.card As ≠ 2 →
      normalizer (As : Set (↥H ⧸ CFSG.pCore 2 ↥H)) ≤
        ((normalizer (L : Set G) ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    intro As hAs hp hp2
    obtain ⟨A, hAL, hcard, rfl⟩ := UC410.exists_prime_lift hLH hAs hp hp2
    rw [← hcard] at hp hp2
    refine (UC410.normalizer_map_le_map (hAL.trans hLH) hp hp2).trans (map_mono (hsub ?_))
    refine le_inf ?_ (hA A hAL hp hp2)
    exact (le_inf (hA A hAL hp hp2) inf_le_right).trans
      (UC410.inf_normalizer_le_normalizer hL hSz hAL hp hp2)
  have hn := PartOne.Section8.r890_odd_three_le_of_isSz hSz
  have hpX := fun (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2) => UC410.pRank_top_quotient_le heM hp hp2
  have hLsp := UC410.commutator_map_self hLH hL.2.1
  have hSzs := UC410.isSz_bar2_map hLH hSz
  refine UC410.isSubnormal_of_map_top hMH hQM hL.1 (isSubnormal_top_of_core hKSch hcore
    (hK.quotient _) hpX (UC410.pCore_quotient_eq_bot H) hLsp hSzs
    (h5d3 hK318 _ _ n (hK.quotient _) hpX hn.2 hn.1 hLsp hSzs)
    (fun As hAs hp hp2 => (hlift As hAs hp hp2).trans
      (UC410.map_le_normalizer_map (H := H) inf_le_left))
    (fun As hAs hp hp2 => (hlift As hAs hp hp2).trans (map_mono (hsub inf_le_right)))
    (UC410.map_le_normalizer_map hRL) hR2
    (fun h => hMH' (UC410.eq_of_map_eq_top hMH hQM h)) (UC410.isSubnormal_map hL.1)
    (UC410.isSylowOf_map hMH hQM hL hMH hR)
    ((UC410.normalizer_map_le_map_of_le hRH hQR).trans (map_mono (hsub hNR))) ?_)
  intro X₁ hX₁ hLX hTX
  obtain ⟨H₁, hH₁H, hQH₁, rfl⟩ := UC410.exists_preimage X₁
  have hH₁ne : H₁ ≠ H := by
    rintro rfl
    exact hX₁ (by rw [subgroupOf_self, Subgroup.map_top_of_surjective _
      (QuotientGroup.mk'_surjective _)])
  exact UC410.isSubnormal_map (hIH H₁ (lt_of_le_of_ne hH₁H hH₁ne) hQH₁
    (UC410.le_of_map_le hLH hQH₁ hLX) (UC410.le_of_map_le hRH hQH₁ hTX))

theorem uc1_4_10_of_core (h5d3 : PartOne.Section8.Lemma5d3_890) (hK318 : UCK.K318)
    (hKSch : UCK.KSch) (hcore : UC1_4_10Core) : UC1_4_10 := by
  intro G _ _
  suffices h : ∀ k : ℕ, ∀ (H M L R : Subgroup G) (n : ℕ), Nat.card H = k →
      CFSG.Open.IsKGroup ↥H → S17.eM H ≤ 3 → M ≤ H → L ∈ calC M → Fstar L = pCoreOf 2 L →
      IsSz (Bar2 L) n → IsSylowOf 2 R (F08.CentOverO2 M L) →
      H ⊓ normalizer (R : Set G) ≤ M →
      (∀ A : Subgroup G, A ≤ L → (Nat.card A).Prime → Nat.card A ≠ 2 →
        H ⊓ normalizer (A : Set G) ≤ M) →
      L ∈ calC H by
    intro H M L R n
    exact h _ H M L R n rfl
  intro k
  induction k using Nat.strong_induction_on with
  | _ k IH =>
  intro H M L R n hk hK heM hMH hL hF hSz hR hNR hA
  by_cases hMH' : M = H
  · subst hMH'
    exact hL
  refine ⟨isSubnormal_of_lt h5d3 hK318 hKSch hcore hK heM hMH hL hSz hR hNR hA hMH' ?_, hL.2⟩
  intro H₁ hH₁ _ hLH₁ hRH₁
  have hRC : R ≤ F08.CentOverO2 M L := by
    obtain ⟨P, rfl⟩ := hR
    exact map_subtype_le _
  have h := IH _ (hk ▸ Subgroup.card_lt_of_lt hH₁) H₁ (M ⊓ H₁) L R n rfl
    (hK.of_le hH₁.le) (UC410.eM_le_of_le hH₁.le heM) inf_le_right
    ⟨UC410.isSubnormal_mono hL.1 (le_inf hL.1.le hLH₁) inf_le_left, hL.2⟩ hF hSz
    (UC410.isSylowOf_centOverO2_inf hR hRH₁)
    (fun x hx => ⟨hNR ⟨hH₁.le hx.1, hx.2⟩, hx.1⟩)
    (fun A hAL hp hp2 x hx => ⟨hA A hAL hp hp2 ⟨hH₁.le hx.1, hx.2⟩, hx.1⟩)
  exact h.1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
