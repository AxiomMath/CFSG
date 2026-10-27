module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C626Cent
public import CFSG.LocalAnalysis.UniquenessCase.UC6C626L2
public import CFSG.LocalAnalysis.UniquenessCase.UC6AutL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.Blueprint
open CFSG.PSL2Table CFSG.GH74.GLS.IVK.L2Borel
open scoped MatrixGroups

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem sup_zpowers_eq_top_of_lieModel_three {S : Type} [Group S] [Finite S] {r : ℕ} (hr3 : r = 3)
    (hL : LieModel S .PSL 2 r 2) (E : Subgroup S) (hE : IsSylowOf r E ⊤) {x : S}
    (hx : (orderOf x).Prime) (hx2 : orderOf x ≠ 2) (hx3 : orderOf x ≠ r) : E ⊔ zpowers x = ⊤ := by
  classical
  subst hr3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨F, _, _, e, -, hFq⟩ :=
    CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' Nat.prime_three (by norm_num) hL
  let φ : S ≃* PSL(2, F) := CFSG.GH74.GLS.IVK.toPSL e
  obtain ⟨-, hSp, hSnd⟩ := isSylowOf_iff.1 hE
  let W : Sylow 3 S := hSp.toSylow (by simpa [Subgroup.relIndex_top_right] using hSnd)
  let W' : Sylow 3 (PSL(2, F)) := Sylow.mapSurjective (f := φ.toMonoidHom) φ.surjective W
  have hW' : (W' : Subgroup (PSL(2, F))) = E.map φ.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hodd : Odd (Nat.card F) := by
    rw [hFq]
    exact (Nat.prime_three.odd_of_ne_two (by norm_num)).pow
  have h2 : (2 : F) ≠ 0 := CFSG.GH74.GLS.IVK.L2Borel.two_ne_zero_of_odd_card hodd
  haveI : Fintype F := Fintype.ofFinite F
  obtain ⟨c, hc⟩ := exists_conj_eq_unipotent hFq W'
  have hNW' : Subgroup.normalizer ((W' : Subgroup (PSL(2, F))) : Set (PSL(2, F))) =
      (borel F).map (MulAut.conj c).toMonoidHom := by
    rw [hc, normalizer_map_equiv,
      normalizer_unipotent_eq h2]
  have hB := card_borel h2 (F := F)
  have hcardF : Fintype.card F = 9 := by
    rw [← Nat.card_eq_fintype_card, hFq]
    norm_num
  rw [hcardF] at hB
  have hB36 : Nat.card (borel F) = 36 := by omega
  have hNcard : Nat.card (Subgroup.normalizer ((W' : Subgroup (PSL(2, F))) : Set (PSL(2, F)))) = 36 := by
    rw [hNW', Subgroup.card_map_of_injective (MulAut.conj c).injective, hB36]
  have hxN : φ x ∉ Subgroup.normalizer ((W' : Subgroup (PSL(2, F))) : Set (PSL(2, F))) := by
    intro hmem
    have hd := Subgroup.orderOf_dvd_natCard _ hmem
    rw [hNcard, MulEquiv.orderOf_eq] at hd
    have hp : (orderOf x) ∣ 2 ^ 2 * 3 ^ 2 := by simpa using hd
    rcases (Nat.Prime.dvd_mul hx).1 hp with h | h
    · exact hx2 ((Nat.prime_dvd_prime_iff_eq hx Nat.prime_two).1 (hx.dvd_of_dvd_pow h))
    · exact hx3 ((Nat.prime_dvd_prime_iff_eq hx Nat.prime_three).1 (hx.dvd_of_dvd_pow h))
  have key := sylow_sup_zpowers_eq_top hFq h2 W' hxN
  rw [hW'] at key
  have key' : (E ⊔ zpowers x).map φ.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    exact key
  have := congrArg (Subgroup.comap φ.toMonoidHom) key'
  rwa [Subgroup.comap_map_eq_self_of_injective φ.injective, Subgroup.comap_top] at this

theorem c626gen_of_lieModel_three (h619 : m.C619) (h620 : m.C620) (hr3 : m.r = 3)
    (hL : LieModel m.Lbar .PSL 2 m.r 2) : m.C626gen := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hEs := m.isSylowOf_Ebar_of_lieModel h620 hL
  have hcen : Subgroup.center m.Lbar = ⊥ := by
    obtain ⟨F, _, _, e, -, -⟩ := CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' m.hr m.d.odd hL
    exact CFSG.GorensteinWalter.center_eq_bot_of_mulEquiv (CFSG.GH74.GLS.IVK.toPSL e)
      (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  have hEab := (UC22.uc22p22q_psl2_sylow_elem m.hr m.d.odd hL hEs).1
  refine m.c626gen_of_Lbar_cent h619 h620 ?_ ?_
  · intro p hp hp2 hpr α hα
    obtain ⟨s, hs⟩ := CFSG.ComponentClassification.AutL2Facts.oddOuterInner_lieModel_sq m.hr m.Lbar hL α
      (by rw [hα]; exact hp.odd_of_ne_two hp2)
    refine ⟨s, hs, ?_⟩
    rw [← hα, hs]
    exact (orderOf_injective _ (conj_injective_of_center_eq_bot hcen) s).symm
  · intro K hK x hxK hxp hx2 hxr
    have hEbne : m.Ebar ≠ ⊥ := by
      intro h
      have := m.card_Ebar h620
      rw [h, Subgroup.card_bot] at this
      have h1 : 1 < m.r ^ 2 := Nat.one_lt_pow (by norm_num) m.hr.one_lt
      omega
    obtain ⟨e0, he01⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hEbne
    have hEK : m.Ebar ≤ K := fun e' he' =>
      hK e0 e0.2 (fun h => he01 (Subtype.ext h)) e' (by
        have := hEab.1.is_comm.comm ⟨e', he'⟩ e0
        exact congrArg Subtype.val this)
    have := sup_zpowers_eq_top_of_lieModel_three hr3 hL m.Ebar hEs hxp hx2 hxr
    rw [eq_top_iff, ← this]
    exact sup_le hEK ((Subgroup.zpowers_le).2 hxK)

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
