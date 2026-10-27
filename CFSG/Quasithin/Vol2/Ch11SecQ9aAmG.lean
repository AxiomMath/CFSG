module

public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch11SecSXK2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

abbrev sXT (X T : Subgroup G) : Subgroup G := pCoreOf 2 (X ⊔ T)

theorem isPGroup_sXT (X T : Subgroup G) : IsPGroup 2 ↥(sXT X T) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _

theorem sXT_le_T {X T : Subgroup G} (hT : quasithinIsSylowTwo T) : sXT X T ≤ T :=
  pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hT le_sup_right)

omit [Finite G] in
theorem le_normalizer_sXT (X T : Subgroup G) :
    X ⊔ T ≤ Subgroup.normalizer (sXT X T : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _

omit [Finite G] in
theorem le_sXT {X T A : Subgroup G} (hAT : A ≤ T) (hA : IsPGroup 2 ↥A)
    (hXA : X ≤ Subgroup.normalizer (A : Set G)) (hTA : T ≤ Subgroup.normalizer (A : Set G)) :
    A ≤ sXT X T :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hAT.trans le_sup_right) (sup_le hXA hTA)
    hA

theorem sXT_inf_eq {X T A : Subgroup G} (hT : quasithinIsSylowTwo T) (h : T ⊓ A ≤ sXT X T) :
    sXT X T ⊓ A = T ⊓ A :=
  le_antisymm (inf_le_inf_right _ (sXT_le_T hT)) (le_inf h inf_le_right)

theorem pCoreOf_normalizer_le_sXT {X T U : Subgroup G} (hT : quasithinIsSylowTwo T)
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hTU : T ≤ Subgroup.normalizer (U : Set G)) :
    pCoreOf 2 (Subgroup.normalizer (U : Set G)) ≤ sXT X T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) (Subgroup.normalizer (U : Set G))
  exact le_sXT (pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hT hTU))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) (hXU.trans hN) (hTU.trans hN)

section Star

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem isSylowTwoOf_inf_of (h : StarHyp G T L I V₁ V₂ X K) {J : Subgroup G}
    (hTJ : T ≤ Subgroup.normalizer (J : Set G)) : QuasithinUnique.IsSylowTwoOf (T ⊓ J) J :=
  A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
    le_sup_left (sup_le Subgroup.le_normalizer hTJ)

theorem V₁_le_sXT (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K) :
    V₁ ≤ sXT X T :=
  le_sXT h.V₁_le_T h.isPGroup_V₁ (cartan_le_normalizer_Vi hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan)
    h.T_le_normalizer_V₁

theorem cartan_le_normalizer_inf_k0Of (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    X ≤ Subgroup.normalizer ((T ⊓ k0Of K P₂ : Subgroup G) : Set G) := by
  have he : T ⊓ k0Of K P₂ = (T ⊓ K) ⊓ k0Of K P₂ := by
    rw [inf_assoc, inf_eq_right.mpr (k0Of_le K P₂)]
  intro x hx
  rw [he]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨h.cartan_le_normalizer_inf hN h1102 hP hx, h.cartan_le_normalizer_k0Of hN h1102 hP hx⟩

theorem T_le_normalizer_inf_k0Of (h : StarHyp G T L I V₁ V₂ X K)
    (hP : ParData T K (LOf L V₁) P₁ P₂) :
    T ≤ Subgroup.normalizer ((T ⊓ k0Of K P₂ : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf
    ⟨Subgroup.le_normalizer ht, h.T_le_normalizer_k0Of hP ht⟩

theorem inf_k0Of_le_sXT (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K)
    (hP : ParData T K (LOf L V₁) P₁ P₂) : T ⊓ k0Of K P₂ ≤ sXT X T :=
  le_sXT inf_le_left (h.sylow.1.to_le inf_le_left) (cartan_le_normalizer_inf_k0Of hN h1102 h hP)
    (T_le_normalizer_inf_k0Of h hP)

theorem cartan_le_normalizer_inf_L₂ (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) :
    X ≤ Subgroup.normalizer ((T ⊓ LOf L V₂ : Subgroup G) : Set G) := by
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have he : T ⊓ LOf L V₂ = TL T L ⊓ LOf L V₂ := by
    refine le_antisymm (le_inf (le_inf inf_le_left (inf_le_right.trans
      (hL₂L.trans le_sup_left))) inf_le_right) (inf_le_inf_right _ inf_le_left)
  intro x hx
  rw [he]
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨(h.cartan.1 hx).2, cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inr rfl) h.v₂ h.cartan hx⟩

theorem T_le_normalizer_inf_L₂ (h : StarHyp G T L I V₁ V₂ X K) :
    T ≤ Subgroup.normalizer ((T ⊓ LOf L V₂ : Subgroup G) : Set G) := fun _ ht =>
  Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, h.T_le_normalizer_L₂ ht⟩

theorem inf_L₂_le_sXT (hN : NatFacts) (h1102 : Stmt11_0_2) (h : StarHyp G T L I V₁ V₂ X K) :
    T ⊓ LOf L V₂ ≤ sXT X T :=
  le_sXT inf_le_left (h.sylow.1.to_le inf_le_left) (cartan_le_normalizer_inf_L₂ hN h1102 h)
    (T_le_normalizer_inf_L₂ h)

end Star

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS
