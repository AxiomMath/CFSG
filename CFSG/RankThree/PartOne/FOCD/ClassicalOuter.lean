module

public import CFSG.RankThree.PartOne.FOCD.Classical
public import CFSG.RankThree.PartOne.FOC.PSLTwoOuter
public import CFSG.RankThree.PartOne.FOC.SpOuter
import CFSG.RankThree.PartOne.S11c.MatrixModelLift
import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder
public import CFSG.RankThree.PartOne.FOC.CompEquiv

public section

namespace CFSG.RankThree.PartOne.FOCD

open Subgroup CFSG CFSG.Blueprint CFSG.RankThree.PartOne CFSG.RankThree.PartOne.FOC
open CFSG.Assembly.LowTwoRank (StatedLieTag StatedLieAdmissible StatedClassicalModel
  projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open CFSG.RankThree.PartOne.Sec66T (LocalRankLeTwo fixSub innerAut)
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.GorensteinWalter (PSL2)
open CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem outerComp_of_comm {p : ℕ} {T : Type} [Group T] [Finite T] (h : ∀ a b : T, a * b = b * a) :
    OuterComp p T := by
  intro _ β _ _ _ x _ _ E hE
  exfalso
  have : Group.IsSolvable ↥(fixSub β) := Group.isSolvable_of_comm fun x y => Subtype.ext (h _ _)
  exact false_of_isComponentOf (fun L => not_isComponent_of_isSolvable L) hE

theorem outerComp_of_not_dvd_outer {p : ℕ} {T : Type} [Group T] [Finite T] (hp : p.Prime) {m : ℕ}
    (hout : Nat.card (Outer T) ∣ m) (hpm : ¬ p ∣ m) : OuterComp p T := by
  intro _ β hβp hβout _
  exfalso
  have hor : orderOf β ∣ p := orderOf_dvd_of_pow_eq_one hβp
  have hE : IsPGroup p (Subgroup.zpowers β) := by
    rcases (Nat.dvd_prime hp).1 hor with h | h
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h, pow_one])
  exact hβout (le_inner_of_not_dvd_outer hp hout hpm hE (Subgroup.mem_zpowers β))

theorem outerComp_psl_psu {τ : StatedLieTag} {n p f : ℕ} {T : Type} [Group T] [Finite T]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hτ : τ = .PSL ∨ τ = .PSU) (hn : 3 ≤ n) (hn4 : n ≤ 4)
    (hf : 1 ≤ f) (hf3 : f ≤ 3) (hmod : StatedClassicalModel T τ n p f) : OuterComp p T := by
  obtain ⟨hout, -⟩ := CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
    hτ hn hp hf hmod
  refine outerComp_of_not_dvd_outer hp hout ?_
  intro h
  have hdn : CFSG.RankThree.OuterOrder.determinantParameter τ n (p ^ f) ∣ n := by
    rcases hτ with rfl | rfl <;> exact Nat.gcd_dvd_left _ _
  generalize CFSG.RankThree.OuterOrder.determinantParameter τ n (p ^ f) = d at h hdn
  have hd0 : 0 < d := Nat.pos_of_dvd_of_pos hdn (by omega)
  have hd4 : d ≤ 4 := (Nat.le_of_dvd (by omega) hdn).trans hn4
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have := Nat.le_of_dvd (by omega) h
      omega
  · have := Nat.le_of_dvd hd0 h
    omega

theorem outerComp_projectiveSL_two {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) : OuterComp p (projectiveSL 2 K) := by
  intro _ α hαp hαinn _ x hx hxp E hE
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hαord : orderOf α = p := by
    refine orderOf_eq_prime hαp ?_
    intro h1
    exact hαinn (h1 ▸ (innerAut (projectiveSL 2 K)).one_mem)
  obtain ⟨ℓ, hℓchar⟩ := CharP.exists K
  have hℓ : ℓ.Prime := CharP.char_is_prime K ℓ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨f, hℓ', hcard⟩ := FiniteField.card K ℓ
  have hK : Nat.card K = ℓ ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card]; exact hcard
  have hf : 1 ≤ (f : ℕ) := f.pos
  let ψ : projectiveSL 2 K ≃* coordinateG K :=
    (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K).symm.trans (pslEquivCoordinateG K)
  obtain ⟨-, k, hkcard, ⟨eX⟩⟩ := psl_two_fixSub_equiv_gen hℓ hp hp2 hf hK ψ hαord hαinn
  by_cases h4 : 4 ≤ Nat.card k
  · have hs : IsSimpleGroup (PSL2 ↥k) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    have : IsSimpleGroup (coordinateG ↥k) := (pslEquivCoordinateG ↥k).symm.isSimpleGroup
    have : IsSimpleGroup ↥(fixSub α) := eX.isSimpleGroup
    rw [eq_of_isComponentOf_simple hE]
    exact hx
  · have hN : ¬ p ∣ Nat.card (fixSub α) := by
      intro hd
      have h1 : Nat.card (fixSub α) ∣ Nat.card (Equiv.Perm (Omega ↥k)) := by
        rw [Nat.card_congr eX.toEquiv]
        exact Subgroup.card_subgroup_dvd_card (coordinateG ↥k)
      have h2 : p ∣ (Nat.card (Omega ↥k)).factorial := by
        rw [← Nat.card_perm]
        exact hd.trans h1
      have h3 := (Nat.Prime.dvd_factorial hp).mp h2
      have h5 : Nat.card (Omega ↥k) = Nat.card ↥k + 1 := by simp [Omega]
      omega
    have hx1 : x = 1 := by
      have h1 : orderOf (⟨x, hx⟩ : ↥(fixSub α)) ∣ p :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hxp))
      have h2 : orderOf (⟨x, hx⟩ : ↥(fixSub α)) ∣ Nat.card (fixSub α) := orderOf_dvd_natCard _
      have hcop : Nat.Coprime p (Nat.card (fixSub α)) := (Nat.Prime.coprime_iff_not_dvd hp).mpr hN
      have h3 : orderOf (⟨x, hx⟩ : ↥(fixSub α)) = 1 :=
        Nat.dvd_one.mp (hcop.gcd_eq_one ▸ Nat.dvd_gcd h1 h2)
      exact congrArg Subtype.val (orderOf_eq_one_iff.mp h3)
    rw [hx1]
    exact E.one_mem

theorem outerComp_classical {t : StatedLieTag} {n p f : ℕ} {T : Type} [Group T] [Finite T]
    (hp : p.Prime) (hp5 : 5 ≤ p) (hs : IsSimpleGroup T)
    (ht : t = .PSL ∨ t = .PSU ∨ t = .PSp ∨ t = .POmegaOdd ∨ t = .POmegaPlus ∨ t = .POmegaMinus)
    (hmod : StatedClassicalModel T t n p f) : OuterComp p T := by
  by_cases hcomm : ∀ a b : T, a * b = b * a
  · exact outerComp_of_comm hcomm
  · have hnab : ∃ a b : T, a * b ≠ b * a := by
      by_contra h
      exact hcomm fun a b => by_contra fun h' => h ⟨a, b, h'⟩
    have hZ := center_eq_bot_of_nonab hs hnab
    have hf : 1 ≤ f := hmod.1.2.1
    rcases ht with rfl | rfl | rfl | ht
    · rcases Nat.lt_or_ge n 3 with h | h
      · obtain rfl : n = 2 := by have := hmod.1.2.2.1; omega
        obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
        exact OuterComp.of_mulEquiv
          (e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
            (LinearCover.projectiveSpecialLinearEquivProjectiveSL 2 K))) hp
          (outerComp_projectiveSL_two hp hp5)
      · intro hLR
        obtain ⟨hn4, hf3⟩ := psl_params hp hp5 hZ hLR h hmod
        exact outerComp_psl_psu hp hp5 (Or.inl rfl) h hn4 hf hf3 hmod hLR
    · intro hLR
      have hn3 : 3 ≤ n := hmod.1.2.2.1
      obtain ⟨hn4, hf3⟩ := psu_params hp hp5 hZ hLR hn3 hmod
      exact outerComp_psl_psu hp hp5 (Or.inr rfl) hn3 hn4 hf hf3 hmod hLR
    · have hn2 : 2 ≤ n := hmod.1.2.2.1
      obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hmod
      exact OuterComp.of_mulEquiv e hp (outerComp_sp hp hf hK hn2 hp (by omega))
    · exact fun hLR => (orth_false ht hp hp5 hZ hLR hmod).elim

end CFSG.RankThree.PartOne.FOCD
