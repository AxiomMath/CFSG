module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154Std
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL8RA3BAABC
public import CFSG.Quasithin.Background.HLUBase
public import CFSG.GroupTheory.ConjTransport
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenInfra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.LU CFSG.Open Subgroup
  CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16h_commute_of_card_dvd_seven {H : Type} [Group H]
    (h : Nat.card H ∣ 7) (a b : H) : a * b = b * a := by
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  haveI : IsCyclic H := isCyclic_of_card_dvd_prime h
  letI : CommGroup H := IsCyclic.commGroup
  exact mul_comm a b

theorem s16h_sl28_autSub_card_map_conj {W : Type} [CommGroup W]
    (X : Subgroup (MulAut W)) (U : Subgroup W) (t : MulAut W) :
    Nat.card ↥(autSub (X.map (MulAut.conj t).toMonoidHom) (U.map t.toMonoidHom)) =
      Nat.card ↥(autSub X U) := by
  have hcongr : congrHom t = (MulAut.conj t).toMonoidHom :=
    MonoidHom.ext fun x => MulEquiv.ext fun w => by
      simp [congrHom_apply, MulAut.conj_apply]
  have hU : ∀ v, v ∈ U ↔ t v ∈ U.map t.toMonoidHom := by
    intro v
    rw [Subgroup.mem_map]
    exact ⟨fun hv => ⟨v, hv, rfl⟩, fun ⟨w, hw, hwv⟩ => t.injective hwv ▸ hw⟩
  have h := autSub_map (U' := U.map t.toMonoidHom) t X hU
  rw [hcongr] at h
  rw [h, Subgroup.card_map_of_injective (K := autSub X U)
    (f := congrHom (resEquiv t hU)) (congrHom_injective (resEquiv t hU))]

theorem s16h_sl28_centralizer_aut_card_dvd_seven_conj
    (D : Data G) (S : s16h_Std D) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 3)
    {x : G} (hxM : x ∈ D.M) :
    Nat.card ↥(autSub
      (Subgroup.centralizer (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))))
      (commSub ⊤ (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)))) ∣ 7 := by
  have hpf := hyp123_pairFacts h.hyp151.hyp125.1
  have hxstab : x ∈ stabTil (⊥ : Subgroup G) V :=
    (le_stabTil hpf.le_normalizer hpf.le_normalizer₀) hxM
  have hB : barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) =
      (lBar ⊥ V h.hyp151.isElemAbelian L).map
        (MulAut.conj ((actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hxstab⟩)⁻¹)).toMonoidHom := by
    simpa only [lBar, map_inv] using
      s15_Infra_barSub_conjSubgroup ⊥ V h.hyp151.isElemAbelian hxstab L
  have hcomm : commSub ⊤ (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)) =
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L)).map
        (actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hxstab⟩)⁻¹.toMonoidHom := by
    have h1 := s15_Infra_commSub_top_map_conj (lBar ⊥ V h.hyp151.isElemAbelian L)
      (actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hxstab⟩)⁻¹
    rw [← hB] at h1
    exact h1
  have hcent : Subgroup.centralizer (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) =
      (Subgroup.centralizer ((lBar ⊥ V h.hyp151.isElemAbelian L) :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))).map
        (MulAut.conj ((actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hxstab⟩)⁻¹)).toMonoidHom := by
    rw [hB]
    exact CFSG.GroupTheory.centralizer_map_conj
      (actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hxstab⟩)⁻¹
      (lBar ⊥ V h.hyp151.isElemAbelian L)
  have heq : Nat.card ↥(autSub
        (Subgroup.centralizer (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) :
          Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))))
        (commSub ⊤ (barSub ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x)))) =
      Nat.card ↥(autSub
        (Subgroup.centralizer ((lBar ⊥ V h.hyp151.isElemAbelian L) :
          Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))))
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))) := by
    rw [hcent, hcomm]
    exact s16h_sl28_autSub_card_map_conj
      (Subgroup.centralizer ((lBar ⊥ V h.hyp151.isElemAbelian L) :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (actTil ⊥ V h.hyp151.isElemAbelian ⟨x, hxstab⟩)⁻¹
  have hcardL : Nat.card ↥(autSub
        (Subgroup.centralizer ((lBar ⊥ V h.hyp151.isElemAbelian L) :
          Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))))
        (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))) ∣ 7 :=
    s16h_sl28_centralizer_aut_card_dvd_seven
      (s15_Infra_vtil_sq_eq_one ⊥ V h.hyp151.isElemAbelian) hrow
  rw [heq]
  exact hcardL

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
