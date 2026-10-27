module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22sb
public import CFSG.LocalAnalysis.UniquenessCase.UC6R2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e
import CFSG.LocalAnalysis.UniquenessCase.UC22P22t
import CFSG.LocalAnalysis.UniquenessCase.UC22P22v
import CFSG.LocalAnalysis.UniquenessCase.UC22P22yb
import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge3
import CFSG.CGT.PushingUpLit.Transport
import CFSG.RankThree.PartTwo.KFacts.KS116ProofTools
import CFSG.LocalAnalysis.EvenBN.Tits.N.P3Frob
import CFSG.CGT.PushingUpLit.Statements
import CFSG.LocalAnalysis.ComponentClassification.SmallLocalFitting
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.CampbellBasic
import CFSG.LocalAnalysis.UniquenessCase.UC6S846d
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UCR638
import CFSG.RankThree.PartTwo.KFacts.KS116

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (InClassG tripleE tripleV InClassX oResidualTwo omegaOne omegaOneCenterIn)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open P22x

namespace P22s

noncomputable def slMapEquiv {R S : Type} [CommRing R] [CommRing S] (f : R ≃+* S) :
    Matrix.SpecialLinearGroup (Fin 2) R ≃* Matrix.SpecialLinearGroup (Fin 2) S where
  toFun := Matrix.SpecialLinearGroup.map f.toRingHom
  invFun := Matrix.SpecialLinearGroup.map f.symm.toRingHom
  left_inv A := Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp
  right_inv A := Matrix.SpecialLinearGroup.ext _ _ fun i j => by simp
  map_mul' := map_mul _

theorem exists_mulEquiv_projSL {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) (hn : 1 ≤ n) :
    Nonempty (X ≃* CFSG.Assembly.RankThreeEven.projSL 2 (GaloisField 2 n)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨F, _, _, _, hF, ⟨e⟩⟩ := P22y.exists_equiv_sl2 h
  haveI := Fintype.ofFinite F
  haveI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hF, GaloisField.card 2 n (by omega)]
  exact ⟨e.trans ((slMapEquiv (FiniteField.ringEquivOfCardEq hcard)).trans
    (CFSG.RankThree.PartTwo.KFacts.KS116Proof.projSLEquiv (GaloisField 2 n)))⟩

variable {G : Type} [Group G]

theorem isSubnormal_subgroupOf_step {A B C : Subgroup G} (hAB : A ≤ B) (hBC : B ≤ C)
    (hA : (A.subgroupOf B).Normal) (hB : (B.subgroupOf C).IsSubnormal) : (A.subgroupOf C).IsSubnormal := by
  have hAC : A.subgroupOf C ≤ B.subgroupOf C := fun x hx => hAB hx
  refine Subgroup.IsSubnormal.trans hAC ?_ hB
  let e := Subgroup.subgroupOfEquivOfLe hBC
  have heq : (A.subgroupOf C).subgroupOf (B.subgroupOf C) = (A.subgroupOf B).comap e.toMonoidHom := by
    ext x
    rfl
  rw [heq]
  exact (hA.comap e.toMonoidHom).isSubnormal

theorem oResidualTwo_normal (X : Type) [Group X] : (oResidualTwo X).Normal := by
  constructor
  intro x hx g
  unfold oResidualTwo at hx ⊢
  rw [Subgroup.mem_sInf] at hx ⊢
  rintro N ⟨hN, hp⟩
  exact hN.conj_mem x (hx N ⟨hN, hp⟩) g

theorem oResidualTwo_le {X : Type} [Group X] {N : Subgroup X} (hN : N.Normal)
    (hp : ∀ x : X, ∃ k : ℕ, x ^ (2 ^ k) ∈ N) : oResidualTwo X ≤ N := by
  refine sInf_le ⟨hN, fun q => ?_⟩
  induction q using QuotientGroup.induction_on with
  | H x =>
    obtain ⟨k, hk⟩ := hp x
    exact ⟨k, by rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]; exact hk⟩

end P22s

open P22s

variable {G : Type} [Group G] [Finite G]

end CFSG.LocalAnalysis.UniquenessCase.UC22
