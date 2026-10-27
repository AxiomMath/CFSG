module

public import CFSG.Quasithin.Background.B4Models
public import CFSG.Quasithin.Background.Module

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

namespace G64

@[expose] def symCoreModel (n : ℕ) : FFModel where
  Gam := Equiv.Perm (Fin n)
  Amb := G6.PermMod n
  act σ x := G6.permAct n σ x
  sec := G6.coreMod n
  ker := ⊥

@[expose] def SymmetricCore {V : Type*} [CommGroup V] (H : Subgroup (MulAut V)) (U Z : Subgroup V)
    (n : ℕ) : Prop :=
  (symCoreModel n).Realizes H U Z

@[expose] def IsQuotientOfSQTKCat (X : Type) [Group X] : Prop :=
  ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (N : Subgroup Y) (_ : N.Normal),
    CFSG.SectionRank.IsSQTKCat Y ∧ Nonempty (X ≃* Y ⧸ N)

section Statement

variable {V : Type} [CommGroup V]

structure Hyp61 (G : Subgroup (MulAut V)) (a : MulAut V) : Prop where
  pCore_eq_bot : pCoreOf 2 G = ⊥
  quotient_sqtk : IsQuotientOfSQTKCat ↥G
  mem : a ∈ G
  ne_one : a ≠ 1
  sq_eq_one : a ^ 2 = 1
  card_comm_le : Nat.card ↥(commV (Subgroup.zpowers a)) ≤ 2 ^ 2
  span : (⨆ (g : MulAut V) (_ : g ∈ G), (commV (Subgroup.zpowers a)).map g.toMonoidHom) = ⊤

@[expose] def ModuleType (H : Subgroup (MulAut V)) (U : Subgroup V) : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ BinaryNaturalSL H U ⊥ n 1) ∨
    (∃ n, 5 ≤ n ∧ n ≤ 8 ∧ SymmetricNatural H U ⊥ n) ∨
    (∃ n, (n = 6 ∨ n = 8) ∧ SymmetricCore H U ⊥ n)

@[expose] def FactorType (H : Subgroup (MulAut V)) : Prop :=
  Nonempty (↥H ≃* ↥(StatedSL 2 (ZMod 2))) ∨ Nonempty (↥H ≃* ↥(StatedSL 3 (ZMod 2))) ∨
    Nonempty (↥H ≃* Equiv.Perm (Fin 5))

@[expose] def CentralType (X : Type) [Group X] : Prop :=
  (∃ n, 2 ≤ n ∧ n ≤ 5 ∧ Nonempty (X ≃* ↥(StatedSL n (ZMod 2)))) ∨
    Nonempty (X ≃* Equiv.Perm (Fin 6)) ∨ Nonempty (X ≃* Equiv.Perm (Fin 7))

@[expose] def Conclusion (G : Subgroup (MulAut V)) (a : MulAut V) : Prop :=
  ∃ (s : ℕ) (Ks : Fin s → Subgroup (MulAut V)),
    s ≤ 2 ∧ (⨆ i, Ks i) = conjClosure (Subgroup.zpowers a) G ∧ iSupIndep Ks ∧
    (∀ i j, i ≠ j → ∀ x ∈ Ks i, ∀ y ∈ Ks j, x * y = y * x) ∧
    (⨆ i, commV (Ks i)) = ⊤ ∧ (∀ i j, i ≠ j → commV (Ks j) ≤ fixV (Ks i)) ∧
    (∃ hs : 0 < s, a ∈ Ks ⟨0, hs⟩) ∧
    (∀ g ∈ G, ∀ i, ∃ j, (Ks i).map (MulAut.conj g).toMonoidHom = Ks j) ∧
    (∀ i j, ∃ g ∈ G, (Ks i).map (MulAut.conj g).toMonoidHom = Ks j) ∧
    (∀ i, ModuleType (Ks i) (commV (Ks i))) ∧
    ((s = 1 ∧ G = conjClosure (Subgroup.zpowers a) G) ∨
      (s = 2 ∧ (∀ i, FactorType (Ks i)) ∧
        ∃ t ∈ G, t ≠ 1 ∧ t ^ 2 = 1 ∧
          G = conjClosure (Subgroup.zpowers a) G ⊔ Subgroup.zpowers t ∧
          ∀ i j, i ≠ j → (Ks i).map (MulAut.conj t).toMonoidHom = Ks j)) ∧
    ((∃ T, IsSylowTwoOf T G ∧ a ∈ T ∧ ∀ x ∈ T, x * a = a * x) →
      s = 1 ∧ G = conjClosure (Subgroup.zpowers a) G ∧ CentralType ↥G)

end Statement

@[expose] def LemmaG64 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G : Subgroup (MulAut V)) (a : MulAut V), Hyp61 G a →
      Nat.card ↥(commV (Subgroup.zpowers a)) = 2 → Conclusion G a

end G64

end CFSG.Quasithin
