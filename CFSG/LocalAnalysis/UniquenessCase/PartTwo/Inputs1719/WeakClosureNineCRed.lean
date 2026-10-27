module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCRedAut
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCRedShape

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81

namespace TC914R

variable {G : Type} [Group G] {T N L : Subgroup G} {X : Type} [Group X]

theorem tcBase_sup_eq_top (hTN : T ≤ N) (hLN : L ≤ N) (hN : N = T ⊔ L) (ψ : ↥N →* X)
    (hψs : Function.Surjective ψ) :
    tcBase (NFW.barSub ψ L) (NFW.barSub ψ T) ⊔ NFW.barSub ψ T = ⊤ := by
  have htop : L.subgroupOf N ⊔ T.subgroupOf N = ⊤ := by
    apply Subgroup.map_injective N.subtype_injective
    rw [Subgroup.map_sup, Subgroup.map_top, Subgroup.range_subtype,
      Subgroup.map_subgroupOf_eq_of_le hLN, Subgroup.map_subgroupOf_eq_of_le hTN, sup_comm, ← hN]
  have hsup : NFW.barSub ψ L ⊔ NFW.barSub ψ T = ⊤ := by
    rw [NFW.barSub, NFW.barSub, ← Subgroup.map_sup, htop, Subgroup.map_top,
      MonoidHom.range_eq_top_of_surjective ψ hψs]
  rw [eq_top_iff, ← hsup]
  exact sup_le_sup_right (le_tcBase _ _) _

theorem pre_of_hyps [Finite G] [Finite X] {V : Subgroup G} (hyp : Hyp9 V T) (hTN : T ≤ N)
    (hNM : N ≤ normalizer (V : Set G)) (hN : N = T ⊔ L) (ψ : ↥N →* X)
    (hψs : Function.Surjective ψ) (hψk : ∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N)
    (hcomp : CFSG.IsComponent (NFW.barSub ψ L)) : Pre (NFW.barSub ψ L) (NFW.barSub ψ T) :=
  ⟨NF914.isSylowIn_map_of_surjective hyp.sylow hTN hNM ψ hψs,
    NF914.eq_bot_of_normal_of_isPGroup_two ψ hψs hψk, hcomp.1,
    fun t _ t' _ => comm_of_isComponent hcomp t t',
    tcBase_sup_eq_top hTN (hN ▸ le_sup_right) hN ψ hψs⟩

end TC914R

theorem tcBarOfHyps_holds :
    TCCoord → ∀ (G : Type) [Group G] [Finite G] (V T N L : Subgroup G), Hyp9 V T → T ≤ N →
      N ≤ normalizer (V : Set G) → N = T ⊔ L →
      L = CFSG.Quasithin.perfectCore (L ⊔ pCoreOf 2 N) →
      (∃ (Z : Type) (_ : Group Z) (ψ : ↥N →* Z), Function.Surjective ψ ∧
        (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) ∧
        CFSG.IsComponent ((L.subgroupOf N).map ψ)) →
      (∃ (A : Type) (_ : Group A) (φ : ↥(N ⊓ normalizer (L : Set G)) →* A),
        Function.Surjective φ ∧
        (∀ x : ↥(N ⊓ normalizer (L : Set G)),
          φ x = 1 ↔ (x : G) ∈ S17.centSection N L (oTwoThreeIn L)) ∧
        (CFSG.Quasithin.F6.IsPGL2 7 A ∨
          Inputs1719.IsAutOf A (alternatingGroup (Fin 6)) ∨ Inputs1719.IsM10 A ∨
          CFSG.Quasithin.F6.IsPGL2 9 A)) →
      ∃ (X : Type) (_ : Group X) (_ : Finite X) (ψ : ↥N →* X), Function.Surjective ψ ∧
        (∀ x : ↥N, ψ x = 1 ↔ (x : G) ∈ pCoreOf 2 N) ∧
        ∃ (Lb : Subgroup X) (B : Type) (_ : Group B) (_ : Finite B)
          (π : ↥(tcN1 Lb (NFW.barSub ψ T)) →* B) (Es : Subgroup B),
          TCBar Lb (NFW.barSub ψ T) π Es := by
  intro hTC G _ _ V T N L hyp hTN hNM hN hL hψ hφ
  obtain ⟨Z, _, ψ, hψs, hψk, hcomp⟩ := hψ
  obtain ⟨A, _, φ, hφs, hφk, hA⟩ := hφ
  have : Finite Z := Finite.of_surjective ψ hψs
  have hLN : L ≤ N := by rw [hN]; exact le_sup_right
  have c := TC914R.pre_of_hyps hyp hTN hNM hN ψ hψs hψk hcomp
  have hO2L := TC914R.pCoreOf_le_pCoreOf hLN hL ψ hψs hψk c
  obtain ⟨φb, hφbs, hφbk⟩ :=
    TC914R.exists_automizer_bar hLN hL hO2L ψ hψs hψk hcomp.1 φ hφs hφk
  obtain ⟨hcoord, h3⟩ := c.isCoordGroup914_of_pre φb hφbs hφbk hA
  have : Finite (TC914R.CoordB (NFW.barSub ψ L) (NFW.barSub ψ T)) :=
    Finite.of_surjective _ TC914R.coordπ_surjective
  obtain ⟨Es, hEs⟩ := hTC _ _ _ hcoord
  exact ⟨Z, inferInstance, inferInstance, ψ, hψs, hψk, NFW.barSub ψ L,
    TC914R.CoordB (NFW.barSub ψ L) (NFW.barSub ψ T), inferInstance, inferInstance,
    TC914R.coordπ _ _, Es, c.sylow, c.o2, c.quasi, h3, c.comm, c.gen, TC914R.coordπ_surjective,
    TC914R.coordπ_eq_one_iff, hEs⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
