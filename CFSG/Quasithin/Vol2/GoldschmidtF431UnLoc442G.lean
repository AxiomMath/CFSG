module

public import CFSG.Quasithin.Vol2.GoldschmidtF431UnLoc442F
public import CFSG.Quasithin.Vol2.GoldschmidtF431Loc442QShult
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpLocal

public section

namespace CFSG.Quasithin.H13.F431.Un

open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.Loc442Q
open scoped commutatorElement

section Solv

variable {G : Type} [Group G] {X Y V U R K P : Subgroup G} {z t : G} {N : Subgroup G}
  [(U.subgroupOf N).Normal]

theorem Loc442UCore.not_solvable_quot (D : Loc442UCore X Y V U R K P z t) (hXN : X ≤ N)
    [((Subgroup.centralizer (qimg N U V : Set (↥N ⧸ U.subgroupOf N))).subgroupOf
      (qimg N U X)).Normal] :
    ¬ Group.IsSolvable (↥(qimg N U X) ⧸ (Subgroup.centralizer
      (qimg N U V : Set (↥N ⧸ U.subgroupOf N))).subgroupOf (qimg N U X)) := by
  intro hsolv
  obtain ⟨L, hLX, hLns, hL⟩ := D.nonsolv
  have hLN : L ≤ N := hLX.trans hXN
  have hVN : V ≤ N := D.V_X.trans hXN
  let ρ : ↥L →* ↥(qimg N U X) := ((qmk N U).comp (Subgroup.inclusion hLN)).codRestrict
    (qimg N U X) (fun x => mem_subImg_of_mem _ (hLN x.2) (hLX x.2))
  let σ := (QuotientGroup.mk' ((Subgroup.centralizer
    (qimg N U V : Set (↥N ⧸ U.subgroupOf N))).subgroupOf (qimg N U X))).comp ρ
  have hker : Group.IsSolvable ↥σ.ker := by
    have h1 : Group.IsSolvable ↥(σ.ker.map L.subtype) := by
      refine hL _ (Subgroup.map_subtype_le _) ?_
      rintro _ ⟨y, hy, rfl⟩ v hv
      have hy1 := (QuotientGroup.eq_one_iff _).mp (MonoidHom.mem_ker.mp hy)
      have hyc := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_subgroupOf.mp hy1)
        (qmk N U ⟨v, hVN hv⟩) (mem_subImg_of_mem _ (hVN hv) hv)
      have hcomm : qmk N U ⟨v, hVN hv⟩ * qmk N U ⟨(y : G), hLN y.2⟩ =
          qmk N U ⟨(y : G), hLN y.2⟩ * qmk N U ⟨v, hVN hv⟩ := hyc
      have hone : qmk N U (⁅(⟨(y : G), hLN y.2⟩ : ↥N), ⟨v, hVN hv⟩⁆) = 1 := by
        rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact hcomm.symm
      exact (qmk_eq_one_iff (N := N) (W := U) (a := (y : G) * v * (y : G)⁻¹ * v⁻¹)
        (N.mul_mem (N.mul_mem (N.mul_mem (hLN y.2) (hVN hv)) (N.inv_mem (hLN y.2)))
          (N.inv_mem (hVN hv)))).mp hone
    exact Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.equivMapOfInjective σ.ker L.subtype L.subtype_injective).toMonoidHom)
      (Subgroup.equivMapOfInjective σ.ker L.subtype L.subtype_injective).injective
  exact hLns (Group.isSolvable_of_ker_le_range σ.ker.subtype σ
    (by rw [Subgroup.range_subtype]))

end Solv

section CaseC


variable {G : Type} [Group G] [Finite G] {X Y V U R K P : Subgroup G} {z t : G}

theorem Loc442UCore.false_of_eq (D : Loc442UCore X Y V U R K P z t) (hlt : nS X U < nS Y U) :
    False := by
  have hUX : U ≤ X := D.U_V.trans D.V_X
  have hUY : U ≤ Y := hUX.trans D.XY
  have : (U.subgroupOf (nS Y U)).Normal := normal_subgroupOf_nS hUY
  have hXN : X ≤ nS Y U := fun x hx => ⟨D.X_le_normalizer_U hx, D.XY hx⟩
  have hVN : V ≤ nS Y U := D.V_X.trans hXN
  have hVn : ∀ x ∈ qimg (nS Y U) U X, ∀ v ∈ qimg (nS Y U) U V,
      x * v * x⁻¹ ∈ qimg (nS Y U) U V := fun x hx v hv =>
    (Subgroup.mem_normalizer_iff.mp
      (subImg_le_normalizer (qmk (nS Y U) U) D.X_le_normalizer_V hx) v).mp hv
  have := centralizer_subgroupOf_normal hVn
  have hV1 : qimg (nS Y U) U V ≠ ⊥ := by
    obtain ⟨v, hv, hvU⟩ := IsConcreteLE.not_le_iff_exists.mp D.not_V_le_U
    intro h
    have hmem : qmk (nS Y U) U ⟨v, hVN hv⟩ ∈ qimg (nS Y U) U V :=
      mem_subImg_of_mem _ (hVN hv) hv
    rw [h, Subgroup.mem_bot] at hmem
    exact hvU ((qmk_eq_one_iff (hVN hv)).mp hmem)
  have hfix : ∀ v ∈ qimg (nS Y U) U V, v ≠ 1 →
      ∀ g ∈ (⊤ : Subgroup (↥(nS Y U) ⧸ U.subgroupOf (nS Y U))),
        g⁻¹ * v * g ∈ qimg (nS Y U) U X → g ∈ qimg (nS Y U) U X := by
    intro v hv hv1 g _ hg
    obtain ⟨v₀, hv₀N, hv₀V, rfl⟩ := mem_subImg.mp hv
    obtain ⟨g₀, hg₀N, rfl⟩ := qmk_surj g
    have hv₀U : v₀ ∉ U := fun h => hv1 ((qmk_eq_one_iff hv₀N).mpr h)
    obtain ⟨x, hx, u, hu, hvx⟩ := D.coset v₀ hv₀V hv₀U
    have hm : g₀⁻¹ * v₀ * g₀ ∈ nS Y U := (nS Y U).mul_mem ((nS Y U).mul_mem
      ((nS Y U).inv_mem hg₀N) hv₀N) hg₀N
    have h1 : g₀⁻¹ * v₀ * g₀ ∈ X := by
      refine (qmk_mem_qimg_iff hUX hm).mp ?_
      rw [qmk_conj_inv _ _ hg₀N hv₀N hm]
      exact hg
    have hxz : x * z * x⁻¹ = v₀ * u⁻¹ := by rw [hvx]; group
    have h2 : g₀⁻¹ * (x * z * x⁻¹) * g₀ ∈ X := by
      have e : g₀⁻¹ * (x * z * x⁻¹) * g₀ = (g₀⁻¹ * v₀ * g₀) * (g₀⁻¹ * u⁻¹ * g₀) := by
        rw [hxz]; group
      rw [e]
      refine X.mul_mem h1 (hUX ?_)
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (U : Set G)).inv_mem hg₀N.1) u⁻¹).mp (U.inv_mem hu)
      simpa using this
    exact mem_subImg_of_mem _ hg₀N (D.H1 x hx g₀ hg₀N.2 h2)
  have hfin := shult_finish (G := ↥(nS Y U) ⧸ U.subgroupOf (nS Y U)) (K := ⊤)
    (X := qimg (nS Y U) U X) (V := qimg (nS Y U) U V) le_top (subImg_mono _ D.V_X) hVn hV1
    (subImg_comm D.V_ab) (subImg_sq D.V_sq) hfix (D.not_solvable_quot hXN)
  have key : nS Y U ≤ X := fun g hg => (qmk_mem_qimg_iff hUX hg).mp (hfin (Subgroup.mem_top _))
  exact absurd hlt (not_lt_of_ge fun g hg => ⟨hg.1, key hg⟩)

end CaseC

end CFSG.Quasithin.H13.F431.Un
