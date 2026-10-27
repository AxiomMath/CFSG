module

public import CFSG.Quasithin.Vol2.Ch4Sec4L446Mod

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
open CFSG.Blueprint CFSG.Quasithin.A4
open scoped IsMulCommutative Pointwise commutatorElement

theorem lemma446ModOrth_holds : Lemma446ModOrth := by
  intro G _ _ T M L VB hs hnab hK hT hM hTM hL hLf hLM hq hn hVB1 hVB2 hVB3 hVB0 hO
  have h : Hyp4_2_1 G T M L := ⟨hs, hnab, hK, hT, hM, hTM, hL, hLf, hLM, hq⟩
  set R := reducedAggregate (L ⊔ T) with hR
  have hRred : IsTwoReducedIn (L ⊔ T) R := by
    refine isTwoReducedIn_iff_isPrimeReduced_subgroupOf.2 ⟨Subgroup.map_subtype_le _, ?_⟩
    have hsub : R.subgroupOf (L ⊔ T) = primeReducedAggregate (↥(L ⊔ T)) 2 :=
      Subgroup.comap_map_eq_self_of_injective (L ⊔ T).subtype_injective _
    rw [hsub]
    exact isPrimeReduced_primeReducedAggregate 2
  have hLR : L ≤ Subgroup.normalizer (R : Set G) := le_sup_left.trans hRred.2.1
  have hRL : R ≤ Subgroup.normalizer (L : Set G) := hRred.1.trans (h.sup_le.trans hn)
  have hVR : ⁅R, L⁆ ≤ R := commutator_le_left_of_le_normalizer hLR
  have hRel : IsElemAbelian 2 R := hRred.2.2.1
  have hVcomm : ∀ a ∈ ⁅R, L⁆, ∀ b ∈ ⁅R, L⁆, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hRel.1.1.1 ⟨a, hVR ha⟩ ⟨b, hVR hb⟩)
  have hLV : L ≤ Subgroup.normalizer ((⁅R, L⁆ : Subgroup G) : Set G) := fun l hl =>
    mem_normalizer_commutator (hLR hl) (Subgroup.le_normalizer hl)
  have hVeq : ⁅R, L⁆ = ⁅⁅R, L⁆, L⁆ :=
    commutator_eq_commutator_commutator_of_perfect h.perfect hRL hLR
  have hVBV : VB ≤ ⁅R, L⁆ := h.le_commutator_reducedAggregate hn hVB1 hVB2 hVB3 hVB0
  have hLVB : L ≤ Subgroup.normalizer (VB : Set G) := le_sup_left.trans hVB2
  obtain ⟨-, -, hBOF, hirr⟩ := hO
  have heq : VB = ⁅R, L⁆ := eq_of_irreducible_quot hVcomm hLV hVeq hVBV hLVB hVB3 hVB0 hirr
  subst heq
  exact hBOF

end CFSG.Quasithin.H13.Ch4
