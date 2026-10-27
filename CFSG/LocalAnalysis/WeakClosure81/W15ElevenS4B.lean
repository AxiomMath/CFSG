module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenS4A
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenS4C
public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenThreeD

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique.Setup.Campbell
open Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_eq_twentyFour_of_equiv_perm_fin_four {K : Subgroup G}
    (hK : Nonempty (↥K ≃* Equiv.Perm (Fin 4))) : Nat.card ↥K = 24 := by
  obtain ⟨e⟩ := hK
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  rfl

namespace Cfg1511

variable {M V₀ V U S H P Q₀ X : Subgroup G} {p : ℕ} {v : G}

theorem card_tSub15_inf_kHull15_eq_eight
    (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hK : Nonempty (↥(kHull15 V₀ H) ≃* Equiv.Perm (Fin 4))) :
    Nat.card ↥(tSub15 M V₀ V U P ⊓ kHull15 V₀ H) = 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h3 : (Nat.factorization 24) 2 = 3 := by
    rw [Nat.factorization_def 24 Nat.prime_two]; decide +kernel
  rw [c.tSub15_inf_kHull15, c.isSylowIn_two_sup.card_eq,
    card_eq_twentyFour_of_equiv_perm_fin_four hK, h3]
  norm_num

theorem card_iHull15_eq_four (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hK : Nonempty (↥(kHull15 V₀ H) ≃* Equiv.Perm (Fin 4))) :
    Nat.card ↥(iHull15 V₀ U H) = 4 := by
  have hE := card_tSub15_inf_kHull15_eq_eight c hK
  rw [c.tSub15_inf_kHull15] at hE
  have h := Subgroup.relIndex_mul_card (H := iHull15 V₀ U H) (K := V₀ ⊔ iHull15 V₀ U H)
  rw [inf_eq_left.2 (le_sup_right : iHull15 V₀ U H ≤ V₀ ⊔ iHull15 V₀ U H),
    c.relIndex_iHull15_sup, hE] at h
  omega

theorem isElemAbelian_iHull15 (c : Cfg1511 M V₀ V U S H P Q₀ p) :
    IsElemAbelian 2 (iHull15 V₀ U H) :=
  B2F.isElemAbelian_mono (Hyp1510.iHull15_le_zSub15 V₀ U H)
    (c.hyp.fam.isElemAbelian_zSub15 c.cex)

theorem not_isMulCommutative_tSub15_inf_kHull15
    (c : Cfg1511 M V₀ V U S H P Q₀ p) (hX : XData15 V₀ U H Q₀ p X v) :
    ¬ IsMulCommutative ↥(tSub15 M V₀ V U P ⊓ kHull15 V₀ H) := by
  intro hcomm
  have hIE : iHull15 V₀ U H ≤ tSub15 M V₀ V U P ⊓ kHull15 V₀ H :=
    le_inf c.iHull15_le_tSub15 (Hyp1510.iHull15_le_kHull15 V₀ U H)
  have hvE : v ∈ tSub15 M V₀ V U P ⊓ kHull15 V₀ H :=
    ⟨c.V₀_le_tSub15 hX.mem, Hyp1510.V₀_le_kHull15 V₀ H hX.mem⟩
  have hle : v1Sub15 V₀ U ≤ ⊥ := by
    rw [← hX.commutator_eq, Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg₂
    have hcom : g₁ * v ^ n = v ^ n * g₁ :=
      congrArg Subtype.val (mul_comm' (⟨g₁, hIE hg₁⟩ : ↥(tSub15 M V₀ V U P ⊓ kHull15 V₀ H))
        ⟨v ^ n, Subgroup.zpow_mem _ hvE n⟩)
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact hcom
  exact c.cex.v1Sub15_ne_bot c.std (le_bot_iff.1 hle)

theorem card_V₀_eq_four (c : Cfg1511 M V₀ V U S H P Q₀ p)
    (hX : XData15 V₀ U H Q₀ p X v)
    (hK : Nonempty (↥(kHull15 V₀ H) ≃* Equiv.Perm (Fin 4))) : Nat.card ↥V₀ = 4 := by
  have hE := card_tSub15_inf_kHull15_eq_eight c hK
  have hnc := not_isMulCommutative_tSub15_inf_kHull15 c hX
  have hV₀E : V₀ ≤ tSub15 M V₀ V U P ⊓ kHull15 V₀ H :=
    le_inf c.V₀_le_tSub15 (Hyp1510.V₀_le_kHull15 V₀ H)
  have hle := card_le_four_of_order_eight hE hnc hV₀E c.cex.hyp.elemAbelian₀
  have h := Subgroup.relIndex_mul_card (H := v1Sub15 V₀ U) (K := V₀)
  rw [inf_eq_left.2 (v1Sub15_le_left V₀ U), W15Eight1.relIndex_eq_two c.w81 c.std c.cex] at h
  have hpos : 1 < Nat.card ↥(v1Sub15 V₀ U) :=
    (Subgroup.one_lt_card_iff_ne_bot _).2 (c.cex.v1Sub15_ne_bot c.std)
  omega

theorem elemFamilyIn_s4
    (c : Cfg1511 M V₀ V U S H S Q₀ p) (hX : XData15 V₀ U H Q₀ p X v)
    (hb : S4Branch15 M V₀ V U S H) :
    elemFamilyIn 2 (tSub15 M V₀ V U S) =
      {tSub15 M V₀ V U S ⊓ centralizer (V : Set G), iHull15 V₀ U H ⊔ cSub15 M V₀ V U H S} := by
  obtain ⟨hK, hTKC⟩ := hb
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set T := tSub15 M V₀ V U S with hTdef
  set C := cSub15 M V₀ V U H S with hCdef
  set K := kHull15 V₀ H with hKdef
  set E := T ⊓ K with hEdef
  set I := iHull15 V₀ U H with hIdef
  have hE : Nat.card E = 8 := card_tSub15_inf_kHull15_eq_eight c hK
  have hnc : ¬ IsMulCommutative E := not_isMulCommutative_tSub15_inf_kHull15 c hX
  have hIE : I ≤ E := le_inf c.iHull15_le_tSub15 (Hyp1510.iHull15_le_kHull15 V₀ U H)
  have hWE : V₀ ≤ E := le_inf c.V₀_le_tSub15 (Hyp1510.V₀_le_kHull15 V₀ H)
  have hI : IsElemAbelian 2 I := isElemAbelian_iHull15 c
  have hI4 : Nat.card I = 4 := card_iHull15_eq_four c hK
  have hW : IsElemAbelian 2 V₀ := c.cex.hyp.elemAbelian₀
  have hW4 : Nat.card V₀ = 4 := card_V₀_eq_four c hX hK
  have hIW : I ≠ V₀ := fun h => c.hyp.not_V₀_le_iHull15 c.cex h.symm.le
  have hCK : C ≤ centralizer (K : Set G) := cSub15_le_centralizer M V₀ V U H S
  have hEK : E ≤ K := inf_le_right
  have hEC : C ≤ centralizer (E : Set G) := hCK.trans (Subgroup.centralizer_le hEK)
  have hdisj : E ⊓ C = ⊥ := by
    rw [eq_bot_iff, ← c.kHull15_inf_cSub15 hX]
    exact fun x hx => ⟨hEK hx.1, hx.2⟩
  have hCT : C ≤ T := cSub15_le_tSub15 M V₀ V U H S
  have hKn : K ≤ normalizer (C : Set G) :=
    (Subgroup.le_centralizer_iff.1 hCK).trans (Subgroup.centralizer_le_normalizer _)
  have hEn : E ≤ normalizer (C : Set G) := hEK.trans hKn
  have hT : T = E ⊔ C := by
    refine le_antisymm (fun t ht => ?_) (sup_le inf_le_left hCT)
    have htKC : t ∈ ((K ⊔ C : Subgroup G) : Set G) := hTKC ht
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K C hKn] at htKC
    obtain ⟨k, hk, c', hc', rfl⟩ := htKC
    have hk' : k = (k * c') * c'⁻¹ := by group
    have hkT : k ∈ T := by
      rw [hk']
      exact T.mul_mem ht (T.inv_mem (hCT hc'))
    exact Subgroup.mul_mem_sup ⟨hkT, hk⟩ hc'
  have hEV : E ⊓ centralizer (V₀ : Set G) ≤ V₀ :=
    (inf_centralizer_eq_of_order_eight_card_four hE hnc hWE hW hW4).le
  have hD : IsElemAbelian 2 (T ⊓ centralizer (V : Set G)) :=
    c.isElemAbelian_tSub15_inf_centralizer hX hTKC hEV
  have hCD : C ≤ T ⊓ centralizer (V : Set G) := le_inf hCT (c.cSub15_le_centralizer_V hX)
  have hC : IsElemAbelian 2 C := B2F.isElemAbelian_mono hCD hD
  have hfam := elemFamilyIn_two_eq_of_order_eight hT hEC hdisj hC hE hnc hIE hI hI4 hWE hW hW4 hIW
  have hV₀V : V₀ ≤ centralizer (V : Set G) := fun x hx =>
    Subgroup.mem_centralizer_iff.2 fun y hy =>
      (B2F.isElemAbelian_comm c.cex.hyp.h6.elemAbelian (c.cex.hyp.h6.le hx) hy).symm
  have hDeq : T ⊓ centralizer (V : Set G) = V₀ ⊔ C := by
    refine le_antisymm (fun d hd => ?_) (sup_le (le_inf (hWE.trans inf_le_left) hV₀V) hCD)
    have hdEC : d ∈ ((E ⊔ C : Subgroup G) : Set G) := by
      rw [← hT]
      exact hd.1
    rw [Subgroup.coe_mul_of_left_le_normalizer_right E C hEn] at hdEC
    obtain ⟨e, he, c', hc', rfl⟩ := hdEC
    have hcV : c' ∈ centralizer (V : Set G) := c.cSub15_le_centralizer_V hX hc'
    have hecV : e ∈ centralizer (V : Set G) := by
      have he' : e = (e * c') * c'⁻¹ := by group
      rw [he']
      exact (centralizer (V : Set G)).mul_mem hd.2 ((centralizer (V : Set G)).inv_mem hcV)
    exact Subgroup.mul_mem_sup
      (hEV ⟨he, Subgroup.centralizer_le c.cex.hyp.h6.le hecV⟩) hc'
  rw [hfam, hDeq]
  exact Set.pair_comm _ _

end Cfg1511

section Certified


theorem w15Eleven3S4_holds : W15Eleven3S4 G := by
  intro M V₀ V U S H Q₀ p c hb
  obtain ⟨X, v, hX⟩ := Cfg1511.exists_xData c
  exact c.elemFamilyIn_s4 hX hb

end Certified

end CFSG.LocalAnalysis.WeakClosure81
