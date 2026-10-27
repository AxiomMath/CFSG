module

public import CFSG.Quasithin.Vol2.Ch1Sec3E9List
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Group
import CFSG.Quasithin.Background.A3Structure36AQuasi
public import CFSG.Quasithin.Background.A3Structure37Base

public section

namespace CFSG.Quasithin.P134

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.EmptyFaithfulMultiple CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

theorem card_center_of_a36Common {X : Type} [Group X] (hq : CFSG.IsQuasisimple X)
    (h : A36Common X) :
    Nat.card (Subgroup.center X) = 1 ∨ Nat.card (Subgroup.center X) = 3 := by
  obtain ⟨-, -, hbr, -⟩ := id h
  rcases hbr with ⟨hFF, -⟩ | ⟨hFZ, -, hc⟩
  · exact absurd hFF (A36A.generalizedFitting_ne_fittingSubgroup hq (A37.fitting_le_center hq h))
  · rwa [← hFZ]

theorem le_normalizer_inf {Γ : Type*} [Group Γ] {N A B : Subgroup Γ}
    (hA : N ≤ Subgroup.normalizer (A : Set Γ)) (hB : N ≤ Subgroup.normalizer (B : Set Γ)) :
    N ≤ Subgroup.normalizer ((A ⊓ B : Subgroup Γ) : Set Γ) :=
  fun _ hn => Subgroup.inf_normalizer_le_normalizer_inf ⟨hA hn, hB hn⟩

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem normal_case (hyp : SQTKHypCat Γ) (h36 : A36CoreStatementCat Γ) (hC : TheoremCSimple)
    (hF : Facts134E9He) {P T N L : Subgroup Γ} (hP9 : Nat.card P = 9) (hexp : ∀ x ∈ P, x ^ 3 = 1)
    (hT : IsSylowTwoOf T ⊤) (hNT : N ≤ T) (hNP : N ≤ Subgroup.normalizer (P : Set Γ))
    (hirr : ∀ U : Subgroup Γ, U ≤ P → N ≤ Subgroup.normalizer (U : Set Γ) → U = ⊥ ∨ U = P)
    (hmul : ∀ t ∈ T, ∀ x ∈ P, ∃ y ∈ P, ∃ s ∈ T, t * x = y * s)
    (hLc : L ∈ cComp (⊤ : Subgroup Γ)) (hL : CFSG.IsComponent L) (hLn : L.Normal)
    (hLP : ¬ P ≤ Subgroup.centralizer (L : Set Γ)) :
    P ≤ L ∧ E9Outcome L P T := by
  have hrank : Open.pRank 3 (⊤ : Subgroup Γ) ≤ 2 :=
    (CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt) 3 Nat.prime_three (by norm_num)
  have hnL : ∀ K : Subgroup Γ, K ≤ Subgroup.normalizer (L : Set Γ) := fun K => by
    rw [Subgroup.normalizer_eq_top]
    exact le_top
  set Z := (Subgroup.center ↥L).map L.subtype with hZ
  have hnZ : ∀ K : Subgroup Γ, K ≤ Subgroup.normalizer (Z : Set Γ) := fun K =>
    (hnL K).trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hZC : Z ≤ Subgroup.centralizer (L : Set Γ) := by
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨l, hl⟩))
  have hZ1 : Subgroup.center ↥L = ⊥ := by
    rcases card_center_of_a36Common hL.1 (h36 L hLc).2.1 with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hcardZ : Nat.card Z = 3 := by
        rw [hZ, Subgroup.card_map_of_injective L.subtype_injective, h3]
      rcases hirr (P ⊓ Z) inf_le_left (le_normalizer_inf hNP (hnZ N)) with h | h
      · exact false_of_normalizes hrank hP9 hexp (hnZ P) h (Nat.dvd_of_mod_eq_zero (by rw [hcardZ]))
      · exact hLP (h ▸ inf_le_right.trans hZC)
  have hLZ : L ⊓ Subgroup.centralizer (L : Set Γ) = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hxZ : (⟨x, hx.1⟩ : L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext ((Subgroup.mem_centralizer_iff.mp hx.2) l l.2)
    rw [hZ1, Subgroup.mem_bot] at hxZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hxZ)
  have hsimple : IsSimpleGroup ↥L := by
    have e : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ1.symm)
    exact e.isSimpleGroup_congr.mpr hL.1.2.1
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hL.1.2.2
    obtain ⟨a', rfl⟩ := QuotientGroup.mk'_surjective _ a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk'_surjective _ b
    refine ⟨a', b', fun h => hab ?_⟩
    rw [← map_mul, ← map_mul, h]
  have hsqtk : CFSG.SectionRank.IsSQTKCat ↥L :=
    CFSG.SectionRank.IsSQTKCat.subgroup ⟨hyp.sqt, hyp.kgroup⟩ L
  have hlist := hC ↥L hnab hsqtk
  have hPL : P ⊓ L = ⊥ ∨ P ⊓ L = P := hirr (P ⊓ L) inf_le_left (le_normalizer_inf hNP (hnL N))
  rcases dispatch hF (P := P) (T := T) hlist with ⟨f, hsz⟩ | ⟨h3, hout⟩
  ·
    exfalso
    have h3 : ¬ 3 ∣ Nat.card L := (hF.szOrder f) ↥L hsz
    have : (Subgroup.centralizer (L : Set Γ)).Normal := Subgroup.normal_centralizer
    set D := L ⊔ Subgroup.centralizer (L : Set Γ) with hD
    have hnD : ∀ K : Subgroup Γ, K ≤ Subgroup.normalizer (D : Set Γ) := fun K => by
      rw [Subgroup.normalizer_eq_top]
      exact le_top
    rcases hirr (P ⊓ D) inf_le_left (le_normalizer_inf hNP (hnD N)) with h | h
    ·
      have hcen : ∀ n ∈ N, ∀ a ∈ P, n * a * n⁻¹ = a := by
        intro n hn a ha
        have h1 : ⁅n, a⁆ ∈ D := (hF.szOut f) Γ L hyp hsz n (hnL N hn) a (hnL P ha)
        have h2 : ⁅n, a⁆ ∈ P := by
          rw [commutatorElement_def]
          exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hNP hn) a).mp ha) (P.inv_mem ha)
        have h4 : ⁅n, a⁆ ∈ P ⊓ D := ⟨h2, h1⟩
        rw [h, Subgroup.mem_bot, commutatorElement_def] at h4
        calc n * a * n⁻¹ = n * a * n⁻¹ * a⁻¹ * a := by group
          _ = a := by rw [h4, one_mul]
      obtain ⟨U, hUP, hU1, hUP', hNU⟩ := exists_invariant_of_index_two (N₀ := ⊤) hP9 hexp hNP
        (fun n hn _ a ha => hcen n hn a ha) (fun x _ _ _ hx => absurd (Subgroup.mem_top x) hx)
      rcases hirr U hUP hNU with h' | h'
      · exact hU1 h'
      · exact hUP' h'
    ·
      apply hLP
      intro a ha
      have haD : a ∈ P ⊓ D := by
        rw [h]
        exact ha
      exact mem_centralizer_of_pow_three_eq_one hLZ h3 haD.2 (hexp a ha)
  ·
    rcases hPL with h | h
    · exact (false_of_normalizes hrank hP9 hexp (hnL P) h h3).elim
    · have hPle : P ≤ L := by
        rw [← h]
        exact inf_le_right
      refine ⟨hPle, hout ⟨hyp, hLn, hPle, hP9, hexp, hT, hmul, fun U hU hTU => ?_⟩⟩
      exact hirr U hU ((le_inf hNT hNP).trans hTU)

end CFSG.Quasithin.P134
