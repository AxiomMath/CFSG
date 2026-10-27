module

public import CFSG.Quasithin.Background.Harris.L3.IdentNat
public import CFSG.Quasithin.Background.Harris.L3.Classify
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.GLOrder
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.NaturalEndField

public section

namespace CFSG.Quasithin.G11.Harris.L3

open Matrix CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.Background.Harris.OrdinaryProofs
open scoped MatrixGroups

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem autAll_of_natShape_one [Finite V] {L : Subgroup (GLV V)}
    {π : SL(3, GaloisField 2 1) →* ↥L} (hπ : Function.Surjective π) (h : NatShape L π) :
    AutAll L ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF : Nat.card (GaloisField 2 1) = 2 := by
    simpa using GaloisField.card 2 1 one_ne_zero
  let _ : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 2 1) = 2 := by rw [← Nat.card_eq_fintype_card, hF]
  have hV : Nat.card V = 2 ^ 3 := by rw [card_of_natShape h, hF]
  have hfin : Module.finrank (ZMod 2) V = 3 := finrank_eq_of_natCard hV
  have hVfin : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hGL : Nat.card (GLV V) = 168 := by
    rw [card_GLV, Fin.prod_univ_eq_prod_range (fun i => 2 ^ Module.finrank (ZMod 2) V - 2 ^ i),
      hfin]
    decide
  have hL : Nat.card ↥L = 168 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective π ⟨natShape_injective h, hπ⟩).toEquiv,
      Matrix.card_SL_field 3, hq]
    decide
  have htop : L = ⊤ := Subgroup.eq_top_of_card_eq L (hL.trans hGL.symm)
  intro g
  refine ⟨((Submodule.topEquiv (R := ZMod 2) (M := V)).symm.trans g).trans
    (Submodule.topEquiv (R := ZMod 2) (M := V)), htop ▸ Subgroup.mem_top _, fun i => rfl⟩

theorem case8_holds : Case8Input := by
  intro V _ _ _ Γ A L m f hs hf π hπ hm hN
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf0 : f ≠ 0 := by omega
  have hcard : Nat.card V = 2 ^ (3 * f) := by
    rw [card_of_natShape hN, GaloisField.card 2 f hf0, ← pow_mul, mul_comm]
  have hdim : Module.finrank (ZMod 2) V = 3 * f := finrank_eq_of_natCard hcard
  have hmod := isNaturalMatrixModule_of_natShape hπ hN
  refine ⟨f, ⟨hf, hdim, by have := hs.bound; omega, hm, hmod, fun h1 => ?_⟩, ?_,
    not_selfDual_natShape hN⟩
  · subst h1
    exact autAll_of_natShape_one hπ hN
  · have hSL : ∀ M : Matrix (Fin 3) (Fin 3) (GaloisField 2 f), M.det = 1 →
        ∃ g ∈ StatedSL 3 (GaloisField 2 f), (g : Matrix (Fin 3) (Fin 3) (GaloisField 2 f)) = M :=
      fun M hM => ⟨_, (specialLinearGroupEquivStatedSL 3 _ ⟨M, hM⟩).2, rfl⟩
    have := endIsField_of_isNaturalMatrixModule hSL hmod
    rwa [GaloisField.finrank 2 hf0] at this

end CFSG.Quasithin.G11.Harris.L3
