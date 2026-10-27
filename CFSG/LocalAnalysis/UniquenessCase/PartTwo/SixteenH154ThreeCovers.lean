module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154BarCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154UNt
public import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenSixFive

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem s16h_pRank_conjSubgroup (q : ℕ) (K : Subgroup G) (x : G) :
    CFSG.Open.pRank q (conjSubgroup K x) = CFSG.Open.pRank q K :=
  s16h_pRank_map_aut q K (MulAut.conj x⁻¹)

theorem s16h_three_dvd_card_of_pRank_eq_one {K : Subgroup G} (h : CFSG.Open.pRank 3 K = 1) :
    3 ∣ Nat.card K := by
  obtain ⟨E, hEK, -, hE⟩ := CFSG.SectionRank.exists_pRank Nat.prime_three.one_lt K
  rw [h, pow_one] at hE
  have h3 : Nat.card E ∣ Nat.card K := Subgroup.card_dvd_of_le hEK
  rwa [hE] at h3

theorem s16h_card_barSub_dvd (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V) {X : Subgroup G}
    (hX : X ≤ stabTil V₀ V) : Nat.card (barSub V₀ V hV X) ∣ Nat.card X := by
  have h1 := Subgroup.card_map_dvd (X.subgroupOf (stabTil V₀ V)) (actTil V₀ V hV)
  have h2 : Nat.card (X.subgroupOf (stabTil V₀ V)) = Nat.card X :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv
  rw [h2] at h1
  exact h1

theorem s16h_calC_le_normalizer {M A B : Subgroup G} (hA : A ∈ calC M) (hB : B ∈ calC M) :
    B ≤ normalizer (A : Set G) := by
  by_cases hAB : A = B
  · subst hAB
    exact Subgroup.le_normalizer
  · exact calC_le_normalizer_of_ne hA hB hAB

theorem s16h_card_le_pRank_of_pRank_one {M X : Subgroup G} {S : Finset (Subgroup G)}
    (hS : ∀ L ∈ S, L ∈ calC M ∧ L ≤ X ∧ X ≤ normalizer (L : Set G) ∧
      CFSG.Open.pRank 3 L = 1) : S.card ≤ CFSG.Open.pRank 3 X :=
  P22fin3.card_le_pRank_of_finset Nat.prime_three (by norm_num)
    (fun L hL => P22fin3.mem_calC_of_le_normalizer (hS L hL).1 (hS L hL).2.1 (hS L hL).2.2.1)
    (fun L hL => s16h_not_dvd_card_center_bar2 (hS L hL).1.2.2 (hS L hL).2.2.2.le)
    (fun L hL => s16h_three_dvd_card_of_pRank_eq_one (hS L hL).2.2.2)

theorem s16h_hyp81_of_three_pRank_one {M K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ∈ calC M)
    (h₂ : K₂ ∈ calC M) (h₃ : K₃ ∈ calC M) (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃)
    (e₁ : CFSG.Open.pRank 3 K₁ = 1) (e₂ : CFSG.Open.pRank 3 K₂ = 1)
    (e₃ : CFSG.Open.pRank 3 K₃ = 1) : F08.Hyp81 M (K₁ ⊔ K₂ ⊔ K₃) := by
  classical
  have hle₁ : K₁ ≤ K₁ ⊔ K₂ ⊔ K₃ := le_sup_left.trans le_sup_left
  have hle₂ : K₂ ≤ K₁ ⊔ K₂ ⊔ K₃ := le_sup_right.trans le_sup_left
  have hle₃ : K₃ ≤ K₁ ⊔ K₂ ⊔ K₃ := le_sup_right
  have hX : ∀ {A : Subgroup G}, A ∈ calC M → K₁ ⊔ K₂ ⊔ K₃ ≤ normalizer (A : Set G) := fun hA =>
    sup_le (sup_le (s16h_calC_le_normalizer hA h₁) (s16h_calC_le_normalizer hA h₂))
      (s16h_calC_le_normalizer hA h₃)
  have h3 : ({K₁, K₂, K₃} : Finset (Subgroup G)).card ≤ CFSG.Open.pRank 3 (K₁ ⊔ K₂ ⊔ K₃) := by
    refine s16h_card_le_pRank_of_pRank_one (M := M) fun L hL => ?_
    simp only [Finset.mem_insert, Finset.mem_singleton] at hL
    rcases hL with rfl | rfl | rfl
    exacts [⟨h₁, hle₁, hX h₁, e₁⟩, ⟨h₂, hle₂, hX h₂, e₂⟩, ⟨h₃, hle₃, hX h₃, e₃⟩]
  rw [Finset.card_eq_three.2 ⟨K₁, K₂, K₃, h12, h13, h23, rfl⟩] at h3
  exact ⟨isSubnormal_sup_sup h₁ h₂ h₃, commutator_sup_sup h₁ h₂ h₃, by omega,
    Or.inr ⟨K₁, K₂, K₃, h₁, h₂, h₃, e₁, e₂, e₃, hle₁, hle₂, hle₃,
      coe_sup_sup_eq_mul h₁ h₂ h₃ h12 h13 h23⟩⟩

theorem s16h_stronglyEmbedded_three_of_three_pRank_one (D : Data G) (h82 : F08.R82 D)
    {K₁ K₂ K₃ : Subgroup G} (h₁ : K₁ ∈ calC D.M) (h₂ : K₂ ∈ calC D.M) (h₃ : K₃ ∈ calC D.M)
    (h12 : K₁ ≠ K₂) (h13 : K₁ ≠ K₃) (h23 : K₂ ≠ K₃) (e₁ : CFSG.Open.pRank 3 K₁ = 1)
    (e₂ : CFSG.Open.pRank 3 K₂ = 1) (e₃ : CFSG.Open.pRank 3 K₃ = 1) :
    IsStronglyPEmbedded 3 D.M :=
  h82 _ (s16h_hyp81_of_three_pRank_one h₁ h₂ h₃ h12 h13 h23 e₁ e₂ e₃)

theorem s16h_stronglyEmbedded_of_pRank_one_cover (D : Data G) (h82 : F08.R82 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 2 < s15 D.M V₀ V h.hyp151.isElemAbelian L) {K₀ : Subgroup G} (hK₀ : K₀ ∈ calC D.M)
    (hbar : barSub V₀ V h.hyp151.isElemAbelian K₀ = barSub V₀ V h.hyp151.isElemAbelian L)
    (e : CFSG.Open.pRank 3 K₀ = 1) : IsStronglyPEmbedded 3 D.M := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨x, hx, y, hy, hxn, hyn, hxy⟩ := s16h_exists_conj_pair D h.hyp151 hs
  have hbx : barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup K₀ x) =
      barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L x) := by
    rw [s15_Infra_barSub_conjSubgroup _ _ _ (hMs hx), s15_Infra_barSub_conjSubgroup _ _ _ (hMs hx),
      hbar]
  have hby : barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup K₀ y) =
      barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L y) := by
    rw [s15_Infra_barSub_conjSubgroup _ _ _ (hMs hy), s15_Infra_barSub_conjSubgroup _ _ _ (hMs hy),
      hbar]
  have hxL : barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L x) ≠
      barSub V₀ V h.hyp151.isElemAbelian L := fun heq =>
    hxn ((s15_Infra_mem_nBar_iff h.hyp151.hyp125 h.hyp151.isElemAbelian hx).2 heq)
  have hyL : barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L y) ≠
      barSub V₀ V h.hyp151.isElemAbelian L := fun heq =>
    hyn ((s15_Infra_mem_nBar_iff h.hyp151.hyp125 h.hyp151.isElemAbelian hy).2 heq)
  have hKx : conjSubgroup K₀ x ∈ calC D.M := uc22p22u_calC_conj Subgroup.le_normalizer hK₀ hx
  have hKy : conjSubgroup K₀ y ∈ calC D.M := uc22p22u_calC_conj Subgroup.le_normalizer hK₀ hy
  exact s16h_stronglyEmbedded_three_of_three_pRank_one D h82 hK₀ hKx hKy
    (fun heq => hxL (hbx.symm.trans
      ((congrArg (barSub V₀ V h.hyp151.isElemAbelian) heq.symm).trans hbar)))
    (fun heq => hyL (hby.symm.trans
      ((congrArg (barSub V₀ V h.hyp151.isElemAbelian) heq.symm).trans hbar)))
    (fun heq => hxy (hbx.symm.trans
      ((congrArg (barSub V₀ V h.hyp151.isElemAbelian) heq).trans hby)))
    e (by rwa [s16h_pRank_conjSubgroup]) (by rwa [s16h_pRank_conjSubgroup])

private theorem s16h_barSub_eq_bot_of_le_conj {D : Data G} {V₀ V L : Subgroup G}
    (h : Setting16 D V₀ V L) {x : G} (hx : x ∈ D.M)
    (hxn : x ∉ nBar D.M V₀ V h.hyp151.isElemAbelian L) {K : Subgroup G} (hK : K ∈ calC D.M)
    (hb : barSub V₀ V h.hyp151.isElemAbelian K ≤ barSub V₀ V h.hyp151.isElemAbelian L)
    (hb' : barSub V₀ V h.hyp151.isElemAbelian K ≤
      barSub V₀ V h.hyp151.isElemAbelian (conjSubgroup L x)) :
    barSub V₀ V h.hyp151.isElemAbelian K = ⊥ := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  have h1 := (Subgroup.commutator_mono hb hb').trans (h.hyp151.commute x hx hxn).1.le
  rw [S18.commutator_barSub_self h.hyp151.isElemAbelian (hK.1.le.trans hMs) hK.2.1] at h1
  exact le_bot_iff.1 h1

theorem s16h_stronglyEmbedded_of_two_pRank_one_covers (D : Data G) (h82 : F08.R82 D)
    {V₀ V L : Subgroup G} (h : Setting16 D V₀ V L)
    (hs : 1 < s15 D.M V₀ V h.hyp151.isElemAbelian L) {K₁ K₂ : Subgroup G} (h₁ : K₁ ∈ calC D.M)
    (h₂ : K₂ ∈ calC D.M) (hne : K₁ ≠ K₂)
    (b₁ : barSub V₀ V h.hyp151.isElemAbelian K₁ ≤ barSub V₀ V h.hyp151.isElemAbelian L)
    (b₂ : barSub V₀ V h.hyp151.isElemAbelian K₂ ≤ barSub V₀ V h.hyp151.isElemAbelian L)
    (n₁ : barSub V₀ V h.hyp151.isElemAbelian K₁ ≠ ⊥)
    (n₂ : barSub V₀ V h.hyp151.isElemAbelian K₂ ≠ ⊥) (e₁ : CFSG.Open.pRank 3 K₁ = 1)
    (e₂ : CFSG.Open.pRank 3 K₂ = 1) : IsStronglyPEmbedded 3 D.M := by
  have hMs : D.M ≤ stabTil V₀ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer h.hyp151.hyp125.pairFacts.le_normalizer₀
  obtain ⟨x, hx, hxn⟩ := s16c34_exists_not_mem_nBar D h.hyp151 hs
  have hK₃ : conjSubgroup K₁ x ∈ calC D.M := uc22p22u_calC_conj Subgroup.le_normalizer h₁ hx
  have hb₃ := s16h_barSub_conjSubgroup_le h.hyp151.isElemAbelian b₁ (hMs hx)
  exact s16h_stronglyEmbedded_three_of_three_pRank_one D h82 h₁ h₂ hK₃ hne
    (fun heq => n₁ (s16h_barSub_eq_bot_of_le_conj h hx hxn h₁ b₁
      ((congrArg (barSub V₀ V h.hyp151.isElemAbelian) heq).trans_le hb₃)))
    (fun heq => n₂ (s16h_barSub_eq_bot_of_le_conj h hx hxn h₂ b₂
      ((congrArg (barSub V₀ V h.hyp151.isElemAbelian) heq).trans_le hb₃)))
    e₁ e₂ (by rwa [s16h_pRank_conjSubgroup])

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
