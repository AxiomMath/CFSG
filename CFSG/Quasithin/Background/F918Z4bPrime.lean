module

public import CFSG.Quasithin.Background.F918Z4bAut
public import CFSG.Quasithin.Background.A3StructureDefs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear

public section

namespace CFSG.Quasithin

open CFSG.GorensteinWalter CFSG.ComponentClassification.CatalogueSchreierLinearTwo

theorem card_le_four_of_isElemAb2_pgl2 {K : Type} [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) {B : Subgroup (PGL2 K)} (hB : IsElemAb2 B) :
    Nat.card B ≤ 4 := by
  classical
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  obtain ⟨Q, hBQ⟩ := hB.isPGroup.exists_le_sylow
  obtain ⟨m, hm, ⟨ψ⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hK Q
  let E : Subgroup (DihedralGroup (2 ^ m)) := (B.subgroupOf (Q : Subgroup _)).map ψ.toMonoidHom
  have hE2 : ∀ a ∈ E, a * a = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul]
    have : b * b = 1 := Subtype.ext (by simpa [sq] using hB.2 b.1 hb)
    simp [this]
  have h1 := CFSG.QuasithinUnique.Setup.Family.dihedral_elemAbelian_card_le_four E hE2
  have h2 : Nat.card E = Nat.card B :=
    calc Nat.card E = Nat.card (B.subgroupOf (Q : Subgroup _)) :=
          (Nat.card_congr (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).toEquiv).symm
      _ = Nat.card B := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBQ).toEquiv
  rw [← h2]
  exact h1

theorem autRankLe_psl2_of_card_prime {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hK : Nat.card K = p) : AutRankLe (PSL2 K) 2 := by
  intro E hE
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, hp, hp.odd_of_ne_two hp2, le_rfl, by rw [hK, pow_one]⟩
  have hsub : Subsingleton (RingAut K) := by
    have h := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hp K
      (n := 1) (by rw [hK, pow_one])).1
    exact (Nat.card_eq_one_iff_unique.mp h).1
  have hrange : E ≤ (pglAction K).range := fun α _ =>
    mem_range_pglAction_of_autFieldPart_eq_one (Subsingleton.elim _ _)
  have hinj : Function.Injective (pglAction K) := pglAction_injective_of_finite K
  have hel : IsElemAb2 (E.comap (pglAction K)) := hE.comap _ hinj
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  rw [← rk_comap_eq_of_le_range _ hinj hrange]
  exact rk_le_of_card_le_two_pow hel.isPGroup
    (by simpa using card_le_four_of_isElemAb2_pgl2 hodd hel)

theorem autRankLe_psl2_prime {L : Type} [Group L] [Finite L] {p : ℕ} (hp : p.Prime) (h7 : 7 ≤ p)
    (h : IsPSL 2 p 1 L) : AutRankLe L 2 := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  rw [pow_one] at hK
  exact AutRankLe.of_mulEquiv
    (e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
    (autRankLe_psl2_of_card_prime hp (by omega) hK)

end CFSG.Quasithin
