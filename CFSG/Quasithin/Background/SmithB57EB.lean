module

public import CFSG.Quasithin.Background.SmithB57EA

public section

namespace CFSG.Quasithin

namespace SmithB57E

open CFSG.Open CFSG.QuasithinUnique FFC
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

namespace Hyp

variable {G L : Subgroup (MulAut V)} (S : Hyp G L)
include S

theorem exists_offender : ∃ A, IsFFStarOffender G A ∧
    ¬ A ≤ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V)) := by
  have hX : ⁅pCoreOf 3 G, ffJ G⁆ ≠ ⊥ := by
    rw [← S.hJ]
    intro h
    apply S.hO3
    intro x hx
    refine ⟨(pCore3_le G) hx, ?_⟩
    show x ∈ Subgroup.centralizer (G : Set (MulAut V))
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have := Subgroup.commutator_mem_commutator hx hg
    rw [h, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at this
    exact this.symm
  obtain ⟨A, hA, -, hAX⟩ := B113.exists_offender_not_le_centralizer (le_refl G) hX
  exact ⟨A, hA, hAX⟩

theorem not_le_of_not_le_centralizer {A : Subgroup (MulAut V)}
    (hAX : ¬ A ≤ Subgroup.centralizer (pCoreOf 3 G : Set (MulAut V))) : ¬ A ≤ L := by
  intro hAL
  apply hAX
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact S.commute_X x hx a (hAL ha)

theorem le_normalizer (hP4 : AsB15Part4) : G ≤ Subgroup.normalizer (L : Set (MulAut V)) :=
  B55.normalizes_comp hP4 S.hV S.hJ S.hL

theorem conj_mem (hP4 : AsB15Part4) {g : MulAut V} (hg : g ∈ G) :
    ∀ l ∈ L, g * l * g⁻¹ ∈ L := fun l hl =>
  (Subgroup.mem_normalizer_iff.1 (S.le_normalizer hP4 hg) l).1 hl

theorem offender_eq_one {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) {b : MulAut V}
    (hb : b ∈ B) (hbL : ∀ l ∈ L, b * l = l * b) : b = 1 :=
  S.eq_one_of_inv_of_commute (hB.1 hb) (by simpa [sq] using hB.2.2.1.2 b hb) hbL

theorem commutator_offender (hP4 : AsB15Part4) {B : Subgroup (MulAut V)}
    (hB : IsFFStarOffender G B) : ⁅L, B⁆ = L := by
  rcases B1Red.commutator_eq_or_commute (Or.inl S.hL.2.2)
      (fun b hb l hl => S.conj_mem hP4 (hB.1 hb) l hl) with h | h
  · exact h
  · exfalso
    apply hB.2.1
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    exact S.offender_eq_one hB hb (fun l hl => h b hb l hl)

theorem not_le_of_isPGroup_two {P : Subgroup (MulAut V)} (hP : IsPGroup 2 ↥P) : ¬ L ≤ P := by
  intro hLP
  have hLo : CFSG.Open.IsQuasisimple ↥L := S.hL.2.2
  have hnt : Nontrivial ↥L := CFSG.ComponentClassification.Quasisimple.nontrivial hLo
  have hperf : Group.IsPerfect ↥L := ⟨hLo.1⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL2 : IsPGroup 2 ↥L := hP.to_le hLP
  exact Group.IsPerfect.not_isNilpotent ↥L hL2.isNilpotent

theorem b51Hyp_sup (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection) {B : Subgroup (MulAut V)}
    (hB : IsFFStarOffender G B) : B51Hyp (L ⊔ B) L := by
  have hLB := S.commutator_offender hP4 hB
  have hMG : L ⊔ B ≤ G := sup_le S.hLG hB.1
  have hn : ∀ y ∈ L ⊔ B, ∀ l ∈ L, y * l * y⁻¹ ∈ L := fun y hy => S.conj_mem hP4 (hMG hy)
  have hBn : B ≤ Subgroup.normalizer (L : Set (MulAut V)) := fun b hb =>
    S.le_normalizer hP4 (hB.1 hb)
  have h2 : ∀ y ∈ L ⊔ B, y ^ 2 ∈ L := B1Red.sq_mem_of_mem_sup hBn hB.2.2.1.2
  have hO2 : pCoreOf 2 (L ⊔ B) = ⊥ := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    set P := pCoreOf 2 (L ⊔ B) with hP
    have hPM : P ≤ L ⊔ B := CFSG.LieType.BorelTits.pCoreOf_le 2 (L ⊔ B)
    have hP2 : IsPGroup 2 ↥P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ B)
    have hcomm := B1Red.commute_of_normal_not_le (N := P) S.hL.2.2
      (fun x hx l hl => hn x (hPM hx) l hl)
      (fun l hl x hx => (Subgroup.mem_normalizer_iff.1
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (L ⊔ B)
          ((le_sup_left : L ≤ L ⊔ B) hl)) x).1 hx)
      (S.not_le_of_isPGroup_two hP2)
    exact S.eq_bot_of_isPGroup_two hP2 (hPM.trans hMG) hcomm
  have hF := FFC.genFitting_eq_of_quot le_sup_left hn S.hLq h2 hO2
  have hZ : centerOf (L ⊔ B) ≤ L := by
    have h := FFC.centerOf_le_genFitting (L ⊔ B)
    rwa [hF] at h
  have hB' : IsFFStarOffender (L ⊔ B) B := ⟨le_sup_right, hB.2⟩
  refine ⟨by rw [hF, sup_eq_left.2 hZ], S.hLq, FFC.sqtk_of_le hA21 S.hq S.hLG S.hLq,
    le_sup_left, hO2, ?_⟩
  exact le_antisymm (sup_le (B1Red.K_le_ffJ le_sup_left hB' hLB) (B6.le_ffJ hB'))
    (B6.ffJ_le _)

theorem case1i (hP4 : AsB15Part4) (hA21 : AsA21SQTKSection) (hB51 : AsB51)
    {B : Subgroup (MulAut V)} (hB : IsFFStarOffender G B) (hBL : ¬ B ≤ L) :
    commV L ∈ IrrPlus L ⊤ ∧
      ((∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural (L ⊔ B) (commV L) (fixV L ⊓ commV L) n) ∨
        G2Natural (L ⊔ B) (commV L) (fixV L ⊓ commV L) 1) := by
  have hconc := hB51 V S.hV (L ⊔ B) L (S.b51Hyp_sup hP4 hA21 hB)
  obtain ⟨-, hcases⟩ := hconc.1
  have hne : L ⊔ B ≠ L := fun h => hBL (h ▸ le_sup_right)
  rcases hcases with ⟨hI, -, hT⟩ | ⟨hG, -⟩ | ⟨n, hG, -⟩ | ⟨hG, -⟩
  · obtain ⟨T, hT'⟩ := B5.exists_isSylowTwoOf (L ⊔ B)
    rcases hT T hT' with h | ⟨-, h⟩
    · exact absurd h hne
    · exact ⟨hI, h⟩
  · exact absurd hG hne
  · exact absurd hG hne
  · exact absurd hG hne

end Hyp

end SmithB57E

end CFSG.Quasithin
