module

import CFSG.SignalizerFunctorTheorem.CatalogBridge.NearSz
import CFSG.SignalizerFunctorTheorem.CatalogBridge.BenderSection
import CFSG.Open.BenderStronglyEmbedded
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Sections
import CFSG.Adapters.Certificate43Check
public import CFSG.Open.Catalog

public section

open CFSG.Open

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem isSolvable_of_ne_top_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (hY : ∀ H : Subgroup Y, H ≠ ⊤ → Group.IsSolvable H) (H : Subgroup X) (hH : H ≠ ⊤) :
    Group.IsSolvable H := by
  have hmap : H.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hH
    rw [← Subgroup.comap_map_eq_self_of_injective (f := e.toMonoidHom) e.injective H, htop,
      Subgroup.comap_top]
  haveI := hY _ hmap
  exact solvable_of_solvable_injective (f := (H.equivMapOfInjective e.toMonoidHom
    e.injective).toMonoidHom) (H.equivMapOfInjective e.toMonoidHom e.injective).injective

theorem eq_top_of_isPerfect_of_ne_bot {Y : Type*} [Group Y]
    (hY : ∀ H : Subgroup Y, H ≠ ⊤ → Group.IsSolvable H) {U : Subgroup Y} (hU : ⁅U, U⁆ = U)
    (hU1 : U ≠ ⊥) : U = ⊤ := by
  by_contra hne
  haveI := hY U hne
  haveI : Group.IsPerfect U := Subgroup.isPerfect_iff.2 hU
  haveI : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).2 hU1
  exact Group.IsPerfect.not_isSolvable (G := ↥U) ‹_›

theorem isSolvable_of_ne_top_sz {n : ℕ} (hp : (2 * n + 1).Prime)
    (H : Subgroup (Sz n)) (hH : H ≠ ⊤) : Group.IsSolvable H := by
  haveI := CFSG.Adapters.certificate43_holds
  have hn : 1 ≤ n := Nat.pos_of_ne_zero (by rintro rfl; exact Nat.not_prime_one hp)
  by_contra hns
  obtain ⟨S, _, hS, hnab, hsec⟩ := McBride.exists_nonabelian_simple_section_of_not_isSolvable hns
  haveI := hS
  have hSH : Nat.card S ∣ Nat.card H := McBride.card_dvd_of_isSectionOf hsec
  obtain ⟨K, f, hf⟩ := hsec.of_injective H.subtype H.subtype_injective
  let L : Subgroup (Sz n) := f.ker.map K.subtype
  have hLK : L ≤ K := Subgroup.map_subtype_le _
  have hker : L.subgroupOf K = f.ker :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective f.ker
  haveI : (L.subgroupOf K).Normal := by
    rw [hker]
    exact MonoidHom.normal_ker f
  let E : K ⧸ L.subgroupOf K ≃* S :=
    (QuotientGroup.quotientMulEquivOfEq hker).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  have hsimple : IsSimpleGroup (K ⧸ L.subgroupOf K) := E.isSimpleGroup
  have hnonab : ∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨E.symm x, E.symm y, fun hc => hxy (by simpa using congrArg E hc)⟩
  have hB := isBenderGroup_of_simple_section (CFSG.Open.Open.bender_suzuki_borel n hn) K L hLK
    hsimple hnonab
  have hES : Nat.card (K ⧸ L.subgroupOf K) = Nat.card S := Nat.card_congr E.toEquiv
  have hdvd : Nat.card (K ⧸ L.subgroupOf K) ∣ Nat.card (Sz n) := by
    rw [hES]
    exact hSH.trans (Subgroup.card_subgroup_dvd_card H)
  rcases hB with ⟨g, hg, ⟨e⟩⟩ | ⟨g, hg, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · rw [Nat.card_congr e.toEquiv] at hdvd
    exact not_three_dvd_card_sz n ((three_dvd_card_psl2_two_pow (by omega)).trans hdvd)
  · rw [Nat.card_congr e.toEquiv] at hdvd
    exact not_three_dvd_card_sz n ((three_dvd_card_psu3 (by omega)).trans hdvd)
  · have hSa : Nat.card S = Nat.card (Sz a) := by
      rw [← hES]
      exact Nat.card_congr e.toEquiv
    rw [Nat.card_congr e.toEquiv] at hdvd
    obtain rfl := eq_of_card_sz_dvd hp ha hdvd
    exact hH (McBride.NearSolvable.eq_top_of_card_dvd (hSa ▸ hSH))

end CFSG.SignalizerFunctorTheorem.CatalogBridge
