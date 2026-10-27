module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Q8
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Res
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Mod

import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X3AutIso
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerNilp
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerQuad
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSect1

public section

namespace CFSG.Quasithin

open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open scoped MatrixGroups

namespace S143

namespace InspW2

theorem resWAny_a6 : ResWAny (fun L _ => Nonempty (L ≃* alternatingGroup (Fin 6))) := by
  intro L _ _ _ ⟨e⟩ Gc _ _ ρ ž Ŝ Kh hin
  obtain ⟨-, A, B, -, -, -, ⟨eB⟩⟩ := hin.K_shape
  have hZ : Subgroup.center L = ⊥ :=
    (card_quotient_center_of_equiv e (alternatingGroup.center_eq_bot (by simp))).1
  have hout4 : Nat.card (Outer L) = 2 ^ 2 := by
    rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv]
    exact CFSG.QuasithinUnique.Setup.X3Aut.index_inner_alt6
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq hout4
  have hκ : Function.Injective
      (Kh.subtype.comp (B.subtype.comp eB.symm.toMonoidHom) : SL(2, ZMod 3) →* Gc) :=
    Kh.subtype_injective.comp (B.subtype_injective.comp eB.symm.injective)
  have h8 := eight_le_of_sl23_in_aut hZ (fun a b => hcomm.is_comm.comm a b) ρ hin.inj _ hκ
    ((alternatingGroup (Fin 6)).subtype.comp e.toMonoidHom)
    (Subtype.val_injective.comp e.injective)
  omega

theorem card_mulAut_alt7 : Nat.card (MulAut (alternatingGroup (Fin 7))) = 5040 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 7
    (by norm_num) (by norm_num)
  let c : Equiv.Perm (Fin 7) →* MulAut (alternatingGroup (Fin 7)) :=
    MulAut.conjNormal (H := alternatingGroup (Fin 7))
  rw [← Nat.card_congr (MulEquiv.ofBijective c hbij).toEquiv]
  simp [Nat.card_eq_fintype_card, Fintype.card_perm, Nat.factorial]

theorem resWAny_a7 : ResWAny (fun L _ => Nonempty (L ≃* alternatingGroup (Fin 7))) :=
  resWAny_of_not_dvd_aut fun _ _ _ _ ⟨e⟩ => by
    rw [Nat.card_congr (MulAut.congr e).toEquiv, card_mulAut_alt7]
    decide

theorem inspWo : InspWo := by
  refine resWAny_of_union
    (G' := fun L _ => Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 6)))
    (H := fun L _ => Nonempty ((L ⧸ Subgroup.center L) ≃* alternatingGroup (Fin 7)))
    (fun L _ ⟨n, hn, he, _⟩ => ?_) (resWAny_cover (fun _ _ _ _ h => h) resWAny_a6)
    (resWAny_cover (fun _ _ _ _ h => h) resWAny_a7)
  rcases hn with rfl | rfl
  · exact Or.inl he
  · exact Or.inr he

end InspW2

end S143

end CFSG.Quasithin
