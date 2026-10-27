module

public import CFSG.Quasithin.Background.C1PackC129Solv

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_oTwoFIn (H : Subgroup G) : Group.IsSolvable ↥(oTwoFIn H) := by
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set F := CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) with hF
  set P : Subgroup ↥H := F.comap π with hP
  have hKP : CFSG.pCore 2 ↥H ≤ P := fun k hk => by
    show π k ∈ F
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
    exact F.one_mem
  have hp : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup (G := ↥H) (p := 2)
  have hKn : Group.IsNilpotent ↥(CFSG.pCore 2 ↥H) := hp.isNilpotent
  have hFn : Group.IsNilpotent ↥F := inferInstance
  have hKs : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := inferInstance
  have hFs : Group.IsSolvable ↥F := inferInstance
  let f : ↥(CFSG.pCore 2 ↥H) →* ↥P := Subgroup.inclusion hKP
  let g : ↥P →* ↥F := (π.comp P.subtype).codRestrict F (fun x => x.2)
  have hker : g.ker ≤ f.range := by
    intro x hx
    have h1 : π (x : ↥H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨⟨x, h2⟩, rfl⟩
  have hPs : Group.IsSolvable ↥P := Group.isSolvable_of_ker_le_range f g hker
  have hsurj : Function.Surjective (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).toMonoidHom :=
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).surjective
  exact Group.isSolvable_of_surjective hsurj

theorem isSolvable_oTwoFIn_sup {H R : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R) :
    Group.IsSolvable ↥(oTwoFIn H ⊔ R) := by
  have hN : R ≤ Subgroup.normalizer (oTwoFIn H : Set G) := hRH.trans C2Six.le_normalizer_oTwoFIn
  have : Group.IsSolvable ↥(oTwoFIn H) := isSolvable_oTwoFIn H
  have hRn : Group.IsNilpotent ↥R := hR.isNilpotent
  have : Group.IsSolvable ↥R := inferInstance
  exact A3.isSolvable_sup_of_le_normalizer hN

theorem c2_6_two_thompson_solv {H R M : Subgroup G} (h : HypC23 H R M)
    (hF : CharTwo (oTwoFIn H)) :
    ∃ (r : ℕ) (Lb : Fin r → Subgroup G),
      (∀ i, IsBlock2 (oTwoFIn H) (Lb i) ∧ IsAltType (Lb i) 3 ∧ ¬ Lb i ≤ M ∧
        ⁅Lb i, thompsonJ R⁆ = Lb i) ∧
      ∀ x ∈ oTwoFIn H, ∃ m ∈ M ⊓ oTwoFIn H, ∃ y : Fin r → G, (∀ i, y i ∈ Lb i) ∧
        x = m * (List.ofFn y).prod := by
  have hRH : R ≤ H := h.radical.1
  have hRp : IsPGroup 2 R := h.radical.isPGroup
  have hXH : oTwoFIn H ⊔ R ≤ H := sup_le C2Six.oTwoFIn_le hRH
  have hYX : oTwoFIn H ≤ oTwoFIn H ⊔ R := le_sup_left
  have hcgs : cgsIn (oTwoFIn H ⊔ R) R ≤ M ⊓ (oTwoFIn H ⊔ R) :=
    le_inf ((C2Nine.cgsIn_mono_left hXH R).trans h.cgs) (cgsIn_le _ R)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := asc129StatementSolv G (oTwoFIn H ⊔ R) R
    (M ⊓ (oTwoFIn H ⊔ R)) (h.sqtk.mono hXH) (C2Six.charTwo_oTwoFIn_sup hRH hRp hF) (c2_6_one h) hcgs
    inf_le_right (isSolvable_oTwoFIn_sup hRH hRp)
  have hLY : ∀ i, Lb i ≤ oTwoFIn H := fun i =>
    C2Six.le_oTwoFIn_of_isShort2 hRH hRp (hLb i).1.1.1 (hLb i).1.1.2.1
  refine ⟨r, Lb, fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨hchi, hBor, hJ⟩ := hLb i
    have hLX : Lb i ≤ oTwoFIn H ⊔ R := hchi.1.2.1
    have hA3 : IsAltType (Lb i) 3 := C2Six.isAltType_three_of_isChi0Block hchi (hLY i)
    refine ⟨⟨hchi.1.1, hLY i, ?_⟩, hA3, fun hLM => ?_, hJ⟩
    · have hsub : IsSubnormal (Lb i) (oTwoFIn H ⊔ R) := IsBlock2.isSubnormal hchi.1
      exact (isSubnormal_iff_subgroupOf (hLY i)).mp (A3.subnormal_of_le_of_le hsub (hLY i) hYX)
    · apply C2Six.not_isBorelOfBlock_self hA3
      have : Lb i ⊓ (M ⊓ (oTwoFIn H ⊔ R)) = Lb i := inf_eq_left.mpr (le_inf hLM hLX)
      rwa [this] at hBor
  · obtain ⟨m, hm, y, hy, hxy⟩ := hprod x (hYX hx)
    have hprodY : (List.ofFn y).prod ∈ oTwoFIn H := by
      refine Subgroup.list_prod_mem _ fun z hz => ?_
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hz
      exact hLY i (hy i)
    have hmY : m ∈ oTwoFIn H := by
      have : m = x * ((List.ofFn y).prod)⁻¹ := by rw [hxy]; group
      rw [this]
      exact (oTwoFIn H).mul_mem hx ((oTwoFIn H).inv_mem hprodY)
    exact ⟨m, ⟨hm.1, hmY⟩, y, hy, hxy⟩

end CFSG.Quasithin
