module

public import CFSG.Quasithin.EmptyFaithful.R3c9Alt7
public import CFSG.Quasithin.EmptyFaithful.R3c8Main
public import CFSG.Quasithin.EmptyFaithful.S153IClose
public import CFSG.Quasithin.EmptyFaithful.R3c9Alt4

public section

namespace CFSG.Quasithin.R3c9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.OuterAutomorphisms
open scoped commutatorElement

section Glue

variable {G : Type} [Group G] [Finite G]

theorem false_of_fourSelfCentTwo {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}
    (c : CtxComp1 T Mc M V₁ V₂ Yp I L t) (o : Concl15343Open T M V₁ V₂ Yp I L) (hYL : Yp ≤ L)
    (hF : FourSelfCentTwo ↥L) : False := by
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hV2S : V₂ ≤ Sgp153 T V₁ := R3c8.V₂_le_Sgp153 hh.hyp hh.decomp
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hYpI : Yp ≤ I := le_sup_left.trans c.inH.1.1
  have hMIY : M ⊓ I ≤ Subgroup.normalizer (Yp : Set G) := fun x hx => by
    have : x ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by rw [c.facts.norm_eq]; exact hx
    exact this.2
  have hMIV : M ⊓ I ≤ Subgroup.normalizer (V₂ : Set G) :=
    R3c8.MI_le_normalizer_V₂ hh o.b_V1 o.b_V2.1 c.facts.norm_eq
  have hV2Y : V₂ ≤ Yp := by
    have h1 : ⁅V₂, Yp⁆ ≤ Yp := by
      rw [Subgroup.commutator_le]
      intro v hv y hy
      have hvN : v ∈ Subgroup.normalizer (Yp : Set G) := hMIY ⟨hSM (hV2S hv), hSI (hV2S hv)⟩
      have h2 : v * y * v⁻¹ ∈ Yp := (Subgroup.mem_normalizer_iff.mp hvN y).mp hy
      have : ⁅v, y⁆ = (v * y * v⁻¹) * y⁻¹ := rfl
      rw [this]
      exact Yp.mul_mem h2 (Yp.inv_mem hy)
    rwa [o.b_V2.1] at h1
  have hYN : Yp ≤ Subgroup.normalizer (V₂ : Set G) := fun y hy => hMIV ⟨hYpM hy, hYpI hy⟩
  obtain ⟨eV⟩ := o.b_V2.2
  have hV4 : Nat.card V₂ = 4 := by
    rw [Nat.card_congr eV.toEquiv, Nat.card_eq_fintype_card]
    simp
  have hV2sq : ∀ v ∈ V₂, v ^ 2 = 1 := by
    intro v hv
    have h1 : eV ⟨v, hv⟩ ^ 2 = 1 := by
      ext i
      simp [pow_two]
      exact CharTwo.add_self_eq_zero _
    have : (⟨v, hv⟩ : ↥V₂) ^ 2 = 1 := eV.injective (by rw [map_pow, h1, map_one])
    simpa using congrArg Subtype.val this
  have hV2c : ∀ u ∈ V₂, ∀ v ∈ V₂, u * v = v * u := by
    intro u hu v hv
    have : (⟨u, hu⟩ : ↥V₂) * ⟨v, hv⟩ = ⟨v, hv⟩ * ⟨u, hu⟩ := by
      apply eV.injective
      rw [map_mul, map_mul]
      exact mul_comm _ _
    simpa using congrArg Subtype.val this
  obtain ⟨a, hcard⟩ : ∃ a : ℕ, Nat.card ↥Yp = 3 * 2 ^ a := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥Yp)).exists_card_eq
    refine ⟨a, ?_⟩
    have h2 : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 3 := o.a_ord
    rw [h1, ha, h2]
  have hgen : Yp = Subgroup.closure {x : G | x ∈ Yp ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    apply le_antisymm
    · conv_lhs => rw [o.a_eq]
      rw [oPrimeResidualOf, Subgroup.closure_le]
      intro x hx
      have hxY : x ∈ Yp := by
        rw [o.a_eq]
        exact Subgroup.subset_closure hx
      exact Subgroup.subset_closure ⟨hxY, hx.2⟩
    · rw [Subgroup.closure_le]
      exact fun x hx => hx.1
  have hact : ¬ Yp ≤ Subgroup.centralizer (V₂ : Set G) := by
    intro hle
    have h1 : ⁅Yp, V₂⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hle
    have h2 : ⁅V₂, Yp⁆ = ⊥ := by rw [Subgroup.commutator_comm]; exact h1
    rw [o.b_V2.1] at h2
    have : Nat.card V₂ = 1 := by rw [h2]; simp
    omega
  have hK3 : ¬ 9 ∣ Nat.card ↥Yp := by
    rw [hcard]
    intro h9
    have h3 : 3 ∣ 2 ^ a := by
      have : 3 * 3 ∣ 3 * 2 ^ a := by simpa using h9
      exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  have hV2L : V₂ ≤ L := hV2Y.trans hYL
  have hFY : ∀ x ∈ Yp, (∀ v ∈ V₂, x * v = v * x) → ¬ 3 ∣ orderOf x → x ∈ V₂ := by
    intro x hx hxc h3
    have hd : orderOf x ∣ 3 * 2 ^ a := hcard ▸ Subgroup.orderOf_dvd_natCard Yp hx
    have hd2 : orderOf x ∣ 2 ^ a :=
      (Nat.Coprime.dvd_of_dvd_mul_left ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm hd)
    obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
    let V' : Subgroup ↥L := V₂.subgroupOf L
    have hV'4 : Nat.card V' = 4 := by
      rw [← hV4]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV2L).toEquiv
    have hV'2 : ∀ v ∈ V', v ^ 2 = 1 := by
      intro v hv
      have : (v : G) ^ 2 = 1 := hV2sq v hv
      exact Subtype.ext (by simpa using this)
    have hV'c : ∀ u ∈ V', ∀ v ∈ V', u * v = v * u := by
      intro u hu v hv
      exact Subtype.ext (hV2c u hu v hv)
    have hxL : x ∈ L := hYL hx
    have := hF V' hV'4 hV'2 hV'c ⟨x, hxL⟩
      (fun v hv => Subtype.ext (hxc v hv)) ⟨m, (Subgroup.orderOf_coe (⟨x, hxL⟩ : ↥L)).symm.trans hm⟩
    exact this
  obtain ⟨e⟩ := isAlt4_of_selfCent (K := Yp) (V := V₂) (Y := Yp) hV2Y hYN hV4 hV2sq hV2c hgen hV2Y hK3 hact hFY
  exact o.d_notA4 ⟨e⟩

end Glue

section Main

@[expose] def Input15343ElimSporadic : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp1 T Mc M V₁ V₂ Yp I L t → Concl15343Open T M V₁ V₂ Yp I L →
      (∀ K : Subgroup G, IsHPlus Yp (Sgp153 T V₁) M K → K ≤ I → K = I) →
        I ≤ Subgroup.normalizer (L : Set G) → I = L ⊔ Sgp153 T V₁ → Yp ≤ L →
          (∃ s : TauCeti.SporadicName, IsLemma115SporadicName s ∧
            Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier s)) → False

theorem input15343ElimNonLie_of_sporadic
    (hlist : Lemma115_3_List) (hA : R3c2.Input15333Two) (kS : Input15343ElimSporadic) :
    Input15343ElimNonLie := by
  classical
  intro G _ _ T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hnl
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hQ : CFSG.IsQuasisimple ↥L := c.c33.quasisimple
  have hperf : Group.IsPerfect ↥L := hQ.1
  have hZ : IsPGroup 2 ↥(Subgroup.center ↥L) := R3c3.isPGroup_two_center c.c33.center_eq
  obtain ⟨z, hz⟩ := hA G T Mc M V₁ V₂ Yp I t c.toCtxComp
  have hcomp : IsComponentIn L I := Id2519.isComponentIn_of_mem_cComp c.c33.mem c.c33.quasisimple
  have hsimple : IsSimpleGroup G := hq.simple
  have hcore : QTKECore G := qtkeCore_of_cat hq.nonabelian hq.qtke
  have hcases : Lemma115Cases L z :=
    (Lemma115_3_List.component_cases hlist hsimple hq.nonabelian hcore hz hcomp).2.2.2
  rcases hcases with ⟨hs, hlie, -⟩ | ⟨-, hZO, hmod, -⟩ | ⟨φ, σ, -⟩ | ⟨φ, σ, hZ13, -⟩ | ⟨hE, -⟩ |
    ⟨hF, -⟩
  ·
    exact hnl (Lemma115LieCharTwo.of_mulEquiv (R3c3.quotCenterEquivOfSimple hs hperf) hlie)
  ·
    have hLie : Lemma115LieCharTwo (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rcases hmod with h | h
      · exact Or.inl (Or.inl (Or.inl ⟨2, Or.inr (Or.inl ⟨by norm_num, h⟩)⟩))
      · exact Or.inl (Or.inl (Or.inl ⟨2, Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨le_rfl, h⟩))))⟩))
    exact hnl (Lemma115LieCharTwo.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hZO) hLie)
  ·
    exact hnl (Or.inr (Or.inl ⟨φ⟩))
  ·
    have hZ1 : Subgroup.center ↥L = ⊥ := by
      rcases hZ13 with h1 | h3
      · exact Subgroup.card_eq_one.mp h1
      · exfalso
        obtain ⟨n, hn⟩ := hZ.exists_card_eq
        rw [h3] at hn
        have hn0 : n ≠ 0 := by
          rintro rfl
          simp at hn
        have : 2 ∣ 3 := by
          rw [hn]
          exact dvd_pow_self 2 hn0
        omega
    let eL : ↥L ≃* ↥L ⧸ Subgroup.center ↥L :=
      (QuotientGroup.quotientBot (G := ↥L)).symm.trans (QuotientGroup.quotientMulEquivOfEq hZ1.symm)
    exact false_of_fourSelfCentTwo c o hYL
      (FourSelfCentTwo.of_mulEquiv (eL.trans φ).symm fourSelfCentTwo_alt7)
  ·
    rcases hE with hL33 | ⟨p, hFM, hm⟩
    · exact false_of_fourSelfCentTwo c o hYL (fourSelfCentTwo_l33 hL33)
    · have hp2 : p ≠ 2 := by
        rintro rfl
        obtain ⟨⟨-, -, -, h22, -⟩, -⟩ := hm
        exact h22 (by simp)
      have hodd : Odd p := hFM.1.odd_of_ne_two hp2
      exact false_of_fourSelfCentTwo c o hYL (fourSelfCentTwo_of_isPSL_two hFM.1 hodd hm)
  ·
    exact kS G T Mc M V₁ V₂ Yp I L t c o hmin hN hIeq hYL hF

end Main

end CFSG.Quasithin.R3c9
