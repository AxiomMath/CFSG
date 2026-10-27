module

public import CFSG.Quasithin.Background.C1PackC129Solv
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.Vol2.Ch10SecB6QS

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem isSolvable_oTwoFIn'' (H : Subgroup G) : Group.IsSolvable ↥(oTwoFIn H) := by
  set π : ↥H →* ↥H ⧸ CFSG.pCore 2 ↥H := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hπ
  set F := CFSG.fittingSubgroup (↥H ⧸ CFSG.pCore 2 ↥H) with hF
  set P : Subgroup ↥H := F.comap π with hP
  have hKP : CFSG.pCore 2 ↥H ≤ P := fun k hk => by
    show π k ∈ F
    rw [hπ, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff k).mpr hk]
    exact F.one_mem
  have hp : IsPGroup 2 (CFSG.pCore 2 ↥H) := CFSG.pCore_isPGroup (G := ↥H) (p := 2)
  have hKn : Group.IsNilpotent ↥(CFSG.pCore 2 ↥H) := hp.isNilpotent
  have hFs : Group.IsSolvable ↥F := inferInstance
  have hKs : Group.IsSolvable ↥(CFSG.pCore 2 ↥H) := inferInstance
  let f : ↥(CFSG.pCore 2 ↥H) →* ↥P := Subgroup.inclusion hKP
  let g : ↥P →* ↥F := (π.comp P.subtype).codRestrict F (fun x => x.2)
  have hker : g.ker ≤ f.range := by
    intro x hx
    have h1 : π (x : ↥H) = 1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
    have h2 : (x : ↥H) ∈ CFSG.pCore 2 ↥H := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨⟨x, h2⟩, rfl⟩
  have hPs : Group.IsSolvable ↥P := Group.isSolvable_of_ker_le_range f g hker
  have hsurj : Function.Surjective
      (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).toMonoidHom :=
    (Subgroup.equivMapOfInjective P H.subtype H.subtype_injective).surjective
  exact Group.isSolvable_of_surjective hsurj

theorem isSolvable_oTwoFIn_sup'' {H R : Subgroup G} (hRH : R ≤ H) (hR : IsPGroup 2 R) :
    Group.IsSolvable ↥(oTwoFIn H ⊔ R) := by
  have hN : R ≤ Subgroup.normalizer (oTwoFIn H : Set G) := hRH.trans C2Six.le_normalizer_oTwoFIn
  have : Group.IsSolvable ↥(oTwoFIn H) := isSolvable_oTwoFIn'' H
  have hRn : Group.IsNilpotent ↥R := hR.isNilpotent
  have : Group.IsSolvable ↥R := inferInstance
  exact A3.isSolvable_sup_of_le_normalizer hN

theorem c2_6_two'' {H R M : Subgroup G} (h : HypC23 H R M) (hF : CharTwo (oTwoFIn H)) :
    ∃ (r : ℕ) (Lb : Fin r → Subgroup G),
      (∀ i, IsBlock2 (oTwoFIn H) (Lb i) ∧ IsAltType (Lb i) 3) ∧
      ∀ x ∈ oTwoFIn H, ∃ m ∈ M ⊓ oTwoFIn H, ∃ y : Fin r → G, (∀ i, y i ∈ Lb i) ∧
        x = m * (List.ofFn y).prod := by
  have hRH : R ≤ H := h.radical.1
  have hRp : IsPGroup 2 R := h.radical.isPGroup
  have hXH : oTwoFIn H ⊔ R ≤ H := sup_le C2Six.oTwoFIn_le hRH
  have hYX : oTwoFIn H ≤ oTwoFIn H ⊔ R := le_sup_left
  have hcgs : cgsIn (oTwoFIn H ⊔ R) R ≤ M ⊓ (oTwoFIn H ⊔ R) :=
    le_inf ((C2Nine.cgsIn_mono_left hXH R).trans h.cgs) (cgsIn_le _ R)
  obtain ⟨r, Lb, -, hLb, hprod⟩ := asc129StatementSolv G (oTwoFIn H ⊔ R) R
    (M ⊓ (oTwoFIn H ⊔ R)) (h.sqtk.mono hXH) (C2Six.charTwo_oTwoFIn_sup hRH hRp hF) (c2_6_one h)
    hcgs inf_le_right (isSolvable_oTwoFIn_sup'' hRH hRp)
  have hLY : ∀ i, Lb i ≤ oTwoFIn H := fun i =>
    C2Six.le_oTwoFIn_of_isShort2 hRH hRp (hLb i).1.1.1 (hLb i).1.1.2.1
  refine ⟨r, Lb, fun i => ?_, fun x hx => ?_⟩
  · obtain ⟨hchi, -, -⟩ := hLb i
    refine ⟨⟨hchi.1.1, hLY i, ?_⟩, C2Six.isAltType_three_of_isChi0Block hchi (hLY i)⟩
    have hsub : IsSubnormal (Lb i) (oTwoFIn H ⊔ R) := IsBlock2.isSubnormal hchi.1
    exact (isSubnormal_iff_subgroupOf (hLY i)).mp (A3.subnormal_of_le_of_le hsub (hLY i) hYX)
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

theorem charTwo_oTwoFIn' {H : Subgroup G} (hO : A37.oddCoreOf H = ⊥) : CharTwo (oTwoFIn H) := by
  set Y := oTwoFIn H with hYdef
  have hYH : Y ≤ H := C2Six.oTwoFIn_le
  have hYn : (Y.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYH).mpr C2Six.le_normalizer_oTwoFIn
  have hOY : A37.oddCoreOf Y = ⊥ :=
    le_bot_iff.mp (hO ▸ A37.oddCoreOf_le_of_subnormal (A4.subnormal_of_normal hYH hYn))
  have hO' : CFSG.oddCore ↥Y = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ Y.subtype_injective).mp hOY
  have hsol : Group.IsSolvable ↥Y := isSolvable_oTwoFIn'' H
  have hE : CFSG.layer ↥Y = ⊥ := by
    refine sSup_eq_bot.mpr fun J hJ => ?_
    by_contra hJ1
    obtain ⟨hq, -⟩ := hJ
    obtain ⟨-, hs, a, b, hab⟩ := hq
    have : Group.IsSolvable ↥J := inferInstance
    have h2 : Group.IsSolvable (↥J ⧸ Subgroup.center ↥J) := inferInstance
    exact hab ((IsSimpleGroup.comm_iff_isSolvable.mpr h2) a b)
  have hF : CFSG.generalizedFitting ↥Y ≤ CFSG.pCore 2 ↥Y := by
    rw [CFSG.generalizedFitting, hE, sup_bot_eq]
    refine (SecB.fittingSubgroup_le_pCore_sup_oddCore' ↥Y).trans ?_
    rw [hO', sup_bot_eq]
  intro x hx
  obtain ⟨hxY, hxC⟩ := hx
  have h1 : (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.centralizer (CFSG.generalizedFitting ↥Y : Set ↥Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : (y : G) ∈ pCoreOf 2 Y := ⟨y, by exact hF hy, rfl⟩
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ hy')
  have h2 := hF (CFSG.centralizer_generalizedFitting_le ↥Y h1)
  exact ⟨_, by exact h2, rfl⟩

omit [Finite G] in
theorem exists_pow_eq_of_commute_coprime' {X : Type*} [Group X] {x z : X} (hc : Commute x z)
    (hcop : (orderOf x).Coprime (orderOf z)) : ∃ k : ℕ, (x * z) ^ k = x := by
  obtain ⟨k, hk1, hk2⟩ := Nat.chineseRemainder hcop 1 0
  refine ⟨k, ?_⟩
  rw [hc.mul_pow, (pow_eq_pow_iff_modEq.mpr hk1 : x ^ k = x ^ 1),
    (pow_eq_pow_iff_modEq.mpr hk2 : z ^ k = z ^ 0), pow_one, pow_zero, mul_one]

theorem mk_pow_three_eq_one' {H B : Subgroup G} (hB : IsBlock2 (oTwoFIn H) B)
    (h3 : IsAltType B 3) {y : G} (hy : y ∈ B) :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H) (⟨y, C2Six.oTwoFIn_le (hB.2.1 hy)⟩ : ↥H)) ^ 3 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hBH : B ≤ H := hB.2.1.trans C2Six.oTwoFIn_le
  have hYn : ((oTwoFIn H).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer C2Six.oTwoFIn_le).mpr
      C2Six.le_normalizer_oTwoFIn
  have hsub : IsSubnormal B H := A4.subnormal_trans (IsBlock2.isSubnormal hB)
    (A4.subnormal_of_normal C2Six.oTwoFIn_le hYn)
  have hc := C2Six.natCard_pCore_quotient_of_isAltType_three h3
  have hn : (CFSG.pCore 2 ↥B).Normal := CFSG.pCore_normal
  have h1 : (QuotientGroup.mk' (CFSG.pCore 2 ↥B) (⟨y, hy⟩ : ↥B)) ^ 3 = 1 := by
    rw [← hc]
    exact pow_card_eq_one'
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  have h2 : y ^ 3 ∈ pCoreOf 2 B := by
    exact ⟨_, h1, rfl⟩
  have h3' := A4.pCoreOf_le_of_subnormal 2 hsub h2
  rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨z, hz, hzy⟩ := h3'
  have : z = (⟨y, hBH hy⟩ : ↥H) ^ 3 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hzy)
  rw [← this]
  exact hz


end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F
