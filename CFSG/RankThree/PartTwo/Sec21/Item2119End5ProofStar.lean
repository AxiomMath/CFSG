module

public import CFSG.RankThree.PartTwo.Sec21.Item2119End4Proof2125Star
import CFSG.RankThree.PartTwo.Sec21.Item2119End3Proof2125Unique
import CFSG.RankThree.PartTwo.Sec5.Tools

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)

@[expose] def Item2125StarV : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G) (e : G) (Y : Subgroup G),
    Gen2125 G A E U c L d U₀ a X e Y →
      ∀ U₁ ∈ fourGroupsMinus E, U₁ ≤ Sec11.sec11K L e → e ∈ Subgroup.centralizer (U₁ : Set G) →
        ¬ ⁅Y, lThreeV E U₁ e⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y

@[expose] def Item2125StarLocal : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G) (d : G)
    (U₀ : Subgroup G) (a : G) (X : Subgroup G) (e : G) (Y : Subgroup G),
    Gen2125 G A E U c L d U₀ a X e Y →
      ∀ U₁ ∈ fourGroupsMinus E, U₁ ≤ Sec11.sec11K L e → e ∈ Subgroup.centralizer (U₁ : Set G) →
        ¬ ⁅Y, ⁅inSubgroup (CFSG.pCore 2) (Y ⊓ Subgroup.centralizer (U₁ : Set G)),
          E ⊓ Subgroup.centralizer (U₁ : Set G)⁆⁆ ≤ inSubgroup (aschbacherSolvableCore 3) Y

namespace Item2119End5Proof

open Item2119EndProof Item2119End3Proof Item2119End4Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isElemAbelian_map {p : ℕ} {H H' : Type*} [Group H] [Group H'] {S : Subgroup H}
    (hS : IsElemAbelian p S) (φ : H →* H') : IsElemAbelian p (S.map φ) :=
  CFSG.SectionRank.isElemAbelian_map hS _

theorem map_conj_mem_fourGroupsMinus {E U : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (E : Set G)) (hU : U ∈ fourGroupsMinus E) :
    U.map (MulAut.conj g).toMonoidHom ∈ fourGroupsMinus E := by
  obtain ⟨hU4, hUE⟩ := hU
  obtain ⟨hEN, hab, hcard⟩ := mem_fourGroups_iff.mp hU4
  have hEg : E.map (MulAut.conj g).toMonoidHom = E :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hg
  refine ⟨mem_fourGroups_iff.mpr ⟨?_, isElemAbelian_map hab _, ?_⟩, ?_⟩
  · calc E = E.map (MulAut.conj g).toMonoidHom := hEg.symm
      _ ≤ (Subgroup.normalizer (U : Set G)).map (MulAut.conj g).toMonoidHom := Subgroup.map_mono hEN
      _ ≤ Subgroup.normalizer ((U.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) :=
        Subgroup.le_normalizer_map _
  · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
    exact hcard
  · conv_lhs => rw [hUE]
    rw [Subgroup.map_commutator, hEg]

theorem eq_bot_or_eq_of_mem_fourGroupsMinus {E U : Subgroup G} (hE3 : IsPGroup 3 E)
    (hU : U ∈ fourGroupsMinus E) :
    ∀ X : Subgroup G, X ≤ U → E ≤ Subgroup.normalizer (X : Set G) → X = ⊥ ∨ X = U := by
  rcases Sec6.mem_fourGroupsPlus_or_mem_fourGroupsMinus hE3 hU.1 with hp | ⟨-, hirr⟩
  · exact absurd hU (Set.disjoint_left.mp (disjoint_fourGroupsPlus_fourGroupsMinus E) hp)
  · exact hirr

omit [Finite G] in
theorem exists_eq_inv_mul_conj {U : Subgroup G} [Finite U] {d : G}
    (hdU : d ∈ Subgroup.normalizer (U : Set G))
    (hfix : ∀ u ∈ U, d * u * d⁻¹ = u → u = 1) : ∀ x ∈ U, ∃ u ∈ U, x = u⁻¹ * (d * u * d⁻¹) := by
  have hmem : ∀ u : U, (u : G)⁻¹ * (d * u * d⁻¹) ∈ U := fun u =>
    U.mul_mem (U.inv_mem u.2) ((Subgroup.mem_normalizer_iff.mp hdU u).mp u.2)
  set f : U → U := fun u => ⟨(u : G)⁻¹ * (d * u * d⁻¹), hmem u⟩ with hf
  have hinj : Function.Injective f := by
    intro u v huv
    have h1 : (u : G)⁻¹ * (d * u * d⁻¹) = (v : G)⁻¹ * (d * v * d⁻¹) := congrArg Subtype.val huv
    have h2 : d * ((v : G) * (u : G)⁻¹) * d⁻¹ = (v : G) * (u : G)⁻¹ := by
      have h3 : (v : G) * (u : G)⁻¹ = (d * v * d⁻¹) * (d * u * d⁻¹)⁻¹ := by
        calc (v : G) * (u : G)⁻¹ = (v : G) * ((u : G)⁻¹ * (d * u * d⁻¹)) * (d * u * d⁻¹)⁻¹ := by
              group
          _ = (d * v * d⁻¹) * (d * u * d⁻¹)⁻¹ := by rw [h1]; group
      calc d * ((v : G) * (u : G)⁻¹) * d⁻¹ = (d * v * d⁻¹) * (d * u * d⁻¹)⁻¹ := by group
        _ = (v : G) * (u : G)⁻¹ := h3.symm
    have h4 := hfix _ (U.mul_mem v.2 (U.inv_mem u.2)) h2
    exact (Subtype.ext (mul_inv_eq_one.mp h4)).symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro x hx
  obtain ⟨u, hu⟩ := hsurj ⟨x, hx⟩
  exact ⟨u, u.2, (congrArg Subtype.val hu).symm⟩

theorem le_sec11K_of_not_mem_centralizer {E U₁ L : Subgroup G} {d e : G} (hE3 : IsPGroup 3 E)
    (hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) (hU : U₁ ∈ fourGroupsMinus E) (hdE : d ∈ E)
    (hUL : U₁ ≤ L) (heU : e ∈ Subgroup.centralizer (U₁ : Set G))
    (hdU : d ∉ Subgroup.centralizer (U₁ : Set G)) (hdI : d ∈ Sec11.sec11K L e) :
    U₁ ≤ Sec11.sec11K L e := by
  have hEN : E ≤ Subgroup.normalizer (U₁ : Set G) := (mem_fourGroups_iff.mp hU.1).1
  have hfix : ∀ u ∈ U₁, d * u * d⁻¹ = u → u = 1 := by
    have hEC : E ≤ Subgroup.normalizer ((Subgroup.centralizer ({d} : Set G) : Subgroup G) :
        Set G) := fun x hx =>
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hcommE d hdE x hx).symm)
    have hECU : E ≤ Subgroup.normalizer
        ((U₁ ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) : Set G) :=
      (le_inf hEN hEC).trans Subgroup.inf_normalizer_le_normalizer_inf
    rcases eq_bot_or_eq_of_mem_fourGroupsMinus hE3 hU _ inf_le_left hECU with h | h
    · intro u hu hdu
      have hmem : u ∈ U₁ ⊓ Subgroup.centralizer ({d} : Set G) := by
        refine ⟨hu, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
        calc u * d = d * u * d⁻¹ * d := by rw [hdu]
          _ = d * u := by group
      rw [h, Subgroup.mem_bot] at hmem
      exact hmem
    · exfalso
      apply hdU
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have hu' : u ∈ U₁ ⊓ Subgroup.centralizer ({d} : Set G) := by rw [h]; exact hu
      exact Subgroup.mem_centralizer_singleton_iff.mp hu'.2
  set K := L ⊓ Subgroup.centralizer ({e} : Set G) with hK
  have hUK : U₁ ≤ K := fun u hu =>
    ⟨hUL hu, Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp heU u hu)⟩
  have hKI : K ≤ Subgroup.normalizer (Sec11.sec11K L e : Set G) :=
    Subgroup.le_normalizer.trans
      (GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual K)
  intro x hx
  obtain ⟨u, hu, rfl⟩ := exists_eq_inv_mul_conj (hEN hdE) hfix x hx
  have h1 : u⁻¹ * d * u ∈ Sec11.sec11K L e := by
    have := (Subgroup.mem_normalizer_iff.mp (hKI (K.inv_mem (hUK hu))) d).mp hdI
    simpa using this
  rw [show u⁻¹ * (d * u * d⁻¹) = (u⁻¹ * d * u) * d⁻¹ by group]
  exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hdI)

theorem inf_theta_eq_bot {A E U₁ Y : Subgroup G} {e : G} (hA : A ∈ partTwoS G) (heA : e ∈ A)
    (he1 : e ≠ 1) (hEA : E ≤ A) (hE3 : IsPGroup 3 E) (hY : Y ∈ thetaComponentsAt 3 e)
    (hEY : E ≤ Subgroup.normalizer (Y : Set G)) (hU : U₁ ∈ fourGroupsMinus E) :
    U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y = ⊥ := by
  obtain ⟨hU2, hU1⟩ := Sec6.isPGroup_two_and_ne_bot_of_mem_fourGroups hU.1
  have hEN : E ≤ Subgroup.normalizer
      ((U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y : Subgroup G) : Set G) :=
    (le_inf (mem_fourGroups_iff.mp hU.1).1
      (hEY.trans (Sec6.normalizer_le_normalizer_theta Y))).trans
        Subgroup.inf_normalizer_le_normalizer_inf
  rcases eq_bot_or_eq_of_mem_fourGroupsMinus hE3 hU _ inf_le_left hEN with h | h
  · exact h
  · exfalso
    have hTθ : U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y ≤
        inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) := by
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hY]
      exact inf_le_right.trans inf_le_right
    have h1 := Sec6.commutator_eq_bot_of_mem_partTwoS hA heA he1 hEA hTθ (hU2.to_le inf_le_left)
      hEN
    rw [h] at h1
    apply hU1
    rw [hU.2, h1]

theorem not_le_thetaQuotCentralizer {U₁ Y : Subgroup G} {d : G} (hdY : d ∈ Y)
    (hdN : d ∈ Subgroup.normalizer (U₁ : Set G)) (hdU : d ∉ Subgroup.centralizer (U₁ : Set G))
    (hUθ : U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y = ⊥) :
    ¬ U₁ ≤ Sec4.thetaQuotCentralizer Y := by
  intro h
  apply hdU
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  have hc := (Sec6.mem_thetaQuotCentralizer_iff.mp (h hu)).2 d⁻¹ (Y.inv_mem hdY)
  have hU : d * u * d⁻¹ * u⁻¹ ∈ U₁ :=
    U₁.mul_mem ((Subgroup.mem_normalizer_iff.mp hdN u).mp hu) (U₁.inv_mem hu)
  have hθ : d * u * d⁻¹ * u⁻¹ ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
    have e1 : d⁻¹⁻¹ * (u * d⁻¹ * u⁻¹) = d * u * d⁻¹ * u⁻¹ := by group
    rw [← e1]
    exact hc
  have h1 : d * u * d⁻¹ * u⁻¹ = 1 := by
    have hmem : d * u * d⁻¹ * u⁻¹ ∈ U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y := ⟨hU, hθ⟩
    rwa [hUθ, Subgroup.mem_bot] at hmem
  calc u * d = (d * u * d⁻¹ * u⁻¹)⁻¹ * (d * u) := by group
    _ = d * u := by rw [h1, inv_one, one_mul]

theorem commutator_eq_of_le {U₁ Y : Subgroup G} {e : G} (hY : Y ∈ thetaComponentsAt 3 e)
    (hUY : U₁ ≤ Y) (h : ¬ U₁ ≤ Sec4.thetaQuotCentralizer Y) : ⁅Y, U₁⁆ = Y :=
  Sec6.commutator_eq_of_not_le_theta (Sec6.isPerfect_of_mem_thetaComponentsAt hY)
    (Sec6.isQuasisimple_of_mem_thetaComponentsAt hY) (hUY.trans Subgroup.le_normalizer)
    fun h' => h ((Sec6.commutator_le_theta_iff (hUY.trans Subgroup.le_normalizer)).mp h')

theorem centralizer_union_le_normalizer {U₁ Y : Subgroup G} {e : G}
    (hY : Y ∈ thetaComponentsAt 3 e) (hUY : U₁ ≤ Y) (h : ¬ U₁ ≤ Sec4.thetaQuotCentralizer Y) :
    Subgroup.centralizer ((U₁ : Set G) ∪ {e}) ≤ Subgroup.normalizer (Y : Set G) := by
  intro g hg
  rw [Subgroup.mem_centralizer_iff] at hg
  have hgU : ∀ u ∈ U₁, g * u * g⁻¹ = u := fun u hu => by
    rw [← hg u (Or.inl hu), mul_inv_cancel_right]
  have hge : g * e * g⁻¹ = e := by
    rw [← hg e (Or.inr rfl), mul_inv_cancel_right]
  have hY' : Y.map (MulAut.conj g).toMonoidHom ∈ thetaComponentsAt 3 e := by
    have h1 := map_mem_thetaComponentsAt (MulAut.conj g) hY
    rwa [MulAut.conj_apply, hge] at h1
  by_cases hYY : Y.map (MulAut.conj g).toMonoidHom = Y
  · exact mem_normalizer_of_map_conj_eq hYY
  · exfalso
    apply h
    have h1 := le_thetaQuotCentralizer_of_ne hY hY' (Ne.symm hYY)
    intro u hu
    apply h1
    refine ⟨u, hUY hu, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact hgU u hu

omit [Finite G] in
theorem inSubgroup_pCore_le {U₁ Y : Subgroup G} {e : G} (hY : Y ∈ thetaComponentsAt 3 e)
    (hN : Subgroup.centralizer ((U₁ : Set G) ∪ {e}) ≤ Subgroup.normalizer (Y : Set G)) :
    inSubgroup (CFSG.pCore 2) (Y ⊓ Subgroup.centralizer (U₁ : Set G)) ≤
      inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ((U₁ : Set G) ∪ {e})) := by
  set H := Subgroup.centralizer ((U₁ : Set G) ∪ {e}) with hH
  set K := Y ⊓ Subgroup.centralizer (U₁ : Set G) with hK
  set P := inSubgroup (CFSG.pCore 2) K with hP
  have hYe : Y ≤ Subgroup.centralizer ({e} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hY
  have hKH : K ≤ H := by
    intro x hx
    rw [hH, Subgroup.mem_centralizer_iff]
    rintro y (hy | hy)
    · exact Subgroup.mem_centralizer_iff.mp hx.2 y hy
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hYe hx.1)).symm
  have hPH : P ≤ H := (Subgroup.map_subtype_le _).trans hKH
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup.map _
  have hHU : H ≤ Subgroup.centralizer (U₁ : Set G) := Subgroup.centralizer_le Set.subset_union_left
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    (le_inf hN (hHU.trans Subgroup.le_normalizer)).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hHP : H ≤ Subgroup.normalizer (P : Set G) :=
    hHK.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
      (CFSG.pCore 2 K))
  set Q : Subgroup H := P.subgroupOf H with hQ
  have hQ2 : IsPGroup 2 Q := hP2.comap_subtype
  have hQn : Q.Normal := by
    constructor
    intro x hx h
    have hx' : (x : G) ∈ P := Subgroup.mem_subgroupOf.mp hx
    exact Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hHP h.2) x).mp hx')
  have hQle : Q ≤ CFSG.pCore 2 H := le_sSup ⟨hQn, hQ2⟩
  intro x hx
  exact ⟨⟨x, hPH hx⟩, hQle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem exists_fourGroupsMinus_conj (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    {A E U L U₀ X : Subgroup G} {c d a : G} (hE : Config2119End G A E U c L d U₀ a X) {e : G}
    (he : e ∈ A) (hecd : e ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d) :
    ∃ U₁ ∈ fourGroupsMinus E, U₁ ≤ L ∧ e ∈ Subgroup.centralizer (U₁ : Set G) ∧
      d ∉ Subgroup.centralizer (U₁ : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hE.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hpairs' := mem_lThreeStarPairs_iff.mp hE.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hEA : E ≤ A := hpair.mem_E.2
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hpair.mem_E.1.2.1])
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have haA : a ∈ A := hpair.mem_E.2 hpairs'.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have ha1 : a ≠ 1 := hpairs'.2.1
  have hdA : d ∈ A := hE.mem_d.1
  have hdL : d ∈ L := hE.mem_d.2
  have hd1 := hE.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  obtain ⟨hcL, d₀, -, -, -, hTU, -, -, -, ⟨w, ⟨hwL, hwN⟩, -, hwd₀, hwA, hwmove⟩, -⟩ :=
    Item21Late2Proof.frame_of h45 h66 hcfg
  have hZ₀ : Subgroup.zpowers d₀ = Subgroup.zpowers d :=
    zpowers_eq_of_eq_or_eq_inv (hTU d hE.mem_d hd1 hE.type_d)
  have hwd : w * d * w⁻¹ = d :=
    Item21LateProof.conj_eq_of_mem_zpowers hwd₀ (by rw [hZ₀]; exact Subgroup.mem_zpowers d)
  rw [hZ₀] at hwA
  have hwc : w * c * w⁻¹ = c := by
    rw [Subgroup.mem_centralizer_singleton_iff.mp (hLC hwL), mul_inv_cancel_right]
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hdc : d ∉ Subgroup.zpowers c := not_mem_zpowers_symm (h3 c hcA) hd1 hcd
  have haCD : a ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers d := not_mem_sup_of_config2119End hE
  have hac : a ∉ Subgroup.zpowers c := fun h => haCD (Subgroup.mem_sup_left h)
  have hca : c ∉ Subgroup.zpowers a := not_mem_zpowers_symm (h3 a haA) hc1 hac
  have hdB : d ∉ Subgroup.zpowers a ⊔ Subgroup.zpowers c := by
    rw [sup_comm]
    exact not_mem_sup_swap (hcomm c hcA d hdA) (hcomm c hcA a haA) (h3 c hcA) hd3 (h3 a haA) hc1
      hdc haCD
  have hB9 : Nat.card (Subgroup.zpowers a ⊔ Subgroup.zpowers c : Subgroup G) = 9 :=
    Item21LateProof.card_zpowers_sup_zpowers (hcomm a haA c hcA) (h3 a haA) (h3 c hcA) ha1 hca
  have hBA : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤ A :=
    sup_le (Subgroup.zpowers_le.mpr haA) (Subgroup.zpowers_le.mpr hcA)
  obtain ⟨m, hm, b, hbB, hebd⟩ :=
    Item21LateProof.exists_pow_mul_of_card hcomm h3 hBA (by rw [h27, hB9]) hdA hdB e he
  have hbA : b ∈ A := hBA hbB
  have hbc : b ∉ Subgroup.zpowers c := by
    intro hb
    apply hecd
    rw [hebd]
    exact Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)) _)
      (Subgroup.mem_sup_left hb)
  have hcU₀ : c ∈ Subgroup.centralizer (U₀ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hLC (hE.le_U₀ hu)))
  have hBU₀ : Subgroup.zpowers a ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer (U₀ : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hE.mem_a.2) (Subgroup.zpowers_le.mpr hcU₀)
  have hbU₀ : b ∈ Subgroup.centralizer (U₀ : Set G) := hBU₀ hbB
  have hwb : w * b * w⁻¹ ≠ b := by
    intro hwb
    have hb1 : b ≠ 1 := fun h => hbc (h ▸ Subgroup.one_mem _)
    have hcb : c ∉ Subgroup.zpowers b := not_mem_zpowers_symm (h3 b hbA) hc1 hbc
    have hbc9 : Nat.card (Subgroup.zpowers b ⊔ Subgroup.zpowers c : Subgroup G) = 9 :=
      Item21LateProof.card_zpowers_sup_zpowers (hcomm b hbA c hcA) (h3 b hbA) (h3 c hcA) hb1 hcb
    have hle : Subgroup.zpowers b ⊔ Subgroup.zpowers c ≤ Subgroup.zpowers a ⊔ Subgroup.zpowers c :=
      sup_le (Subgroup.zpowers_le.mpr hbB) le_sup_right
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hB9, hbc9])
    have haB : a ∈ Subgroup.zpowers b ⊔ Subgroup.zpowers c := by
      rw [heq]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers a)
    have hwa : w * a * w⁻¹ = a := conj_eq_of_mem_sup hwb hwc haB
    have hdc9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm d hdA c hcA) hd3 (h3 c hcA) hd1 hcd
    have haDC : a ∉ Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
      rw [sup_comm]
      exact haCD
    obtain ⟨y, hyA, hy⟩ := hwmove
    exact hy (conj_eq_of_fix_basis hcomm h3 h27 hcA hdA haA hdc9 haDC hwa hwd hwc y hyA)
  obtain ⟨k, hk, hkd⟩ := Item21LateProof.exists_pow_lt_three_of_mem_zpowers hd3 (hwA b hbA)
  have hk0 : k ≠ 0 := by
    rintro rfl
    apply hwb
    rw [pow_zero, inv_mul_eq_one] at hkd
    exact hkd.symm
  have hvx : w * b * w⁻¹ = b * d ^ k := by
    rw [← hkd]
    group
  obtain ⟨n, hn⟩ := exists_pow_conj_eq hd3 hwd hk hk0 hvx m hm
  have hgb : w ^ n * b * (w ^ n)⁻¹ = e := by
    rw [hn, hebd, hcomm b hbA _ (Subgroup.pow_mem _ hdA m)]
  set g := w ^ n with hg
  have hgN : g ∈ Subgroup.normalizer (E : Set G) := by
    rw [hEeq]
    exact Subgroup.pow_mem _ hwN n
  have hgL : g ∈ L := Subgroup.pow_mem _ hwL n
  have hgd : g * d * g⁻¹ = d := conj_pow_eq_of_conj_eq hwd n
  refine ⟨U₀.map (MulAut.conj g).toMonoidHom, map_conj_mem_fourGroupsMinus hgN hE.mem_U₀, ?_, ?_,
    ?_⟩
  · rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    exact L.mul_mem (L.mul_mem hgL (hE.le_U₀ hu)) (L.inv_mem hgL)
  · rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u, hu, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    have hub : u * b = b * u := Subgroup.mem_centralizer_iff.mp hbU₀ u hu
    rw [← hgb]
    calc g * u * g⁻¹ * (g * b * g⁻¹) = g * (u * b) * g⁻¹ := by group
      _ = g * (b * u) * g⁻¹ := by rw [hub]
      _ = g * b * g⁻¹ * (g * u * g⁻¹) := by group
  · intro hdU
    have hdU₀ : d ∈ Subgroup.centralizer (U₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro u hu
      have h1 := Subgroup.mem_centralizer_iff.mp hdU (g * u * g⁻¹)
        ⟨u, hu, by simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]⟩
      have h2 : g * (u * d) * g⁻¹ = g * (d * u) * g⁻¹ := by
        calc g * (u * d) * g⁻¹ = g * u * g⁻¹ * (g * d * g⁻¹) := by group
          _ = g * u * g⁻¹ * d := by rw [hgd]
          _ = d * (g * u * g⁻¹) := h1
          _ = g * d * g⁻¹ * (g * u * g⁻¹) := by rw [hgd]
          _ = g * (d * u) * g⁻¹ := by group
      simpa using h2
    have hAU₀ : A ≤ Subgroup.centralizer (U₀ : Set G) := by
      intro y hy
      obtain ⟨i, j, l, rfl⟩ := exists_basis_repr hcomm h3 h27 hdA haA hcA hB9 hdB y hy
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ hdU₀ _)
        (Subgroup.mul_mem _ (Subgroup.pow_mem _ hE.mem_a.2 _) (Subgroup.pow_mem _ hcU₀ _))
    obtain ⟨-, hU₀1⟩ := Sec6.isPGroup_two_and_ne_bot_of_mem_fourGroups hE.mem_U₀.1
    apply hU₀1
    rw [hE.mem_U₀.2, hEeq]
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hAU₀ hy) u hu).symm

end Item2119End5Proof

open Item2119End5Proof

theorem item2125StarV_of_local (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hLoc : Item2125StarLocal) : Item2125StarV := by
  intro G _ _ A E U c L d U₀ a X e Y hgen U₁ hU₁ hU₁I heU₁
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 := hLoc G A E U c L d U₀ a X e Y hgen U₁ hU₁ hU₁I heU₁
  have hcfg := hgen.cfg.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hEA : E ≤ A := hpair.mem_E.2
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hpair.mem_E.1.2.1])
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hpair.mem_E.1.1
  have hcA : c ∈ A := hpair.mem_E.2 hpairs.1.1
  have hc1 : c ≠ 1 := hpairs.2.1
  have he := hgen.mem_e
  have hdA : d ∈ A := hgen.cfg.mem_d.1
  have hdL : d ∈ L := hgen.cfg.mem_d.2
  have hd1 := hgen.cfg.ne_one_d
  have hd3 : d ^ 3 = 1 := h3 d hdA
  have he3 : e ^ 3 = 1 := h3 e he
  have hed : e ∉ Subgroup.zpowers d := fun h => hgen.not_mem_cd (Subgroup.mem_sup_right h)
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  have hec : e ∉ Subgroup.zpowers c := fun h => hgen.not_mem_cd (Subgroup.mem_sup_left h)
  have hY := hgen.mem_Y
  have hG4 := hpair.standing.toTheoremFourHyp
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe he he1 Y hY
  have hLc : L ∈ thetaComponentsAt 3 c := lZeroStarAt_subset A c hpairs.2.2.1
  have hLC : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hcL : c ∉ L := (Item21Late2Proof.frame_of h45 h66 hcfg).1
  have hcd : c ∉ Subgroup.zpowers d := fun h => hcL ((Subgroup.zpowers_le.mpr hdL) h)
  have hdc : d ∉ Subgroup.zpowers c :=
    Item2119End4Proof.not_mem_zpowers_symm (h3 c hcA) hd1 hcd
  have hdCE : d ∉ Subgroup.zpowers c ⊔ Subgroup.zpowers e :=
    Item2119End4Proof.not_mem_sup_swap (hcomm c hcA d hdA) (hcomm c hcA e he) (h3 c hcA) hd3 he3
      hc1 hdc hgen.not_mem_cd
  have hdI : d ∈ Sec11.sec11K L e :=
    (show d ∈ A ⊓ Sec11.sec11K L e by rw [hgen.inf_I]; exact Subgroup.mem_zpowers d).2
  have hdY : d ∈ Y := hgen.le_I hdI
  have hU₁Y : U₁ ≤ Y := hU₁I.trans hgen.le_I
  have hU₁L : U₁ ≤ L := hU₁I.trans ((Sec6.inSubgroup_perfectResidual_le _).trans inf_le_left)
  have hcU₁ : c ∈ Subgroup.centralizer (U₁ : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_singleton_iff.mp (hLC (hU₁L hu))
  have hdU₁ : d ∉ Subgroup.centralizer (U₁ : Set G) := by
    intro hdU
    have hB9 := Sec6.card_inf_centralizer_of_mem_fourGroupsMinus
      (Late.isE27_of_mem_partTwoE hpair.mem_E.1) hU₁
    have hce9 := Item21LateProof.card_zpowers_sup_zpowers (hcomm c hcA e he) (h3 c hcA) he3 hc1
      hec
    have hle : Subgroup.zpowers c ⊔ Subgroup.zpowers e ≤ E ⊓ Subgroup.centralizer (U₁ : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr ⟨hEeq ▸ hcA, hcU₁⟩)
        (Subgroup.zpowers_le.mpr ⟨hEeq ▸ he, heU₁⟩)
    have heq := Subgroup.eq_of_le_of_card_ge hle (by rw [hB9, hce9])
    apply hdCE
    rw [heq]
    exact ⟨hEeq ▸ hdA, hdU⟩
  have hUθ := inf_theta_eq_bot hpair.mem_S he he1 hEA hE3 hY (hEA.trans hAY) hU₁
  have hdN : d ∈ Subgroup.normalizer (U₁ : Set G) :=
    (mem_fourGroups_iff.mp hU₁.1).1 (hEeq ▸ hdA)
  have hnC := not_le_thetaQuotCentralizer hdY hdN hdU₁ hUθ
  have hN := centralizer_union_le_normalizer hY hU₁Y hnC
  have hle := inSubgroup_pCore_le hY hN
  intro h2
  apply h1
  refine le_trans ?_ h2
  exact Subgroup.commutator_mono le_rfl (Subgroup.commutator_mono hle le_rfl)

theorem item2125Star_of_starV (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hV : Item2125StarV) : Item2125Star := by
  intro G _ _ A E U c L d U₀ a X e Y hgen
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcfg := hgen.cfg.cfg
  have hpair := hcfg.pair
  have hpairs := mem_lThreeStarPairs_iff.mp hpair.mem_pair
  have hAe : IsElemAbelian 3 A := hpair.mem_S.1.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have h27 : Nat.card A = 27 := by rw [hcfg.card]; norm_num
  have hEA : E ≤ A := hpair.mem_E.2
  have hEeq : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [h27, hpair.mem_E.1.2.1])
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hpair.mem_E.1.1
  have hcommE : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    hcomm x (hEA hx) y (hEA hy)
  have he := hgen.mem_e
  have heE : e ∈ E := hEeq ▸ he
  have hdA : d ∈ A := hgen.cfg.mem_d.1
  have hed : e ∉ Subgroup.zpowers d := fun h => hgen.not_mem_cd (Subgroup.mem_sup_right h)
  have he1 : e ≠ 1 := fun h => hed (h ▸ Subgroup.one_mem _)
  have hY := hgen.mem_Y
  have hG4 := hpair.standing.toTheoremFourHyp
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe he he1 Y hY
  have hdI : d ∈ Sec11.sec11K L e :=
    (show d ∈ A ⊓ Sec11.sec11K L e by rw [hgen.inf_I]; exact Subgroup.mem_zpowers d).2
  have hdY : d ∈ Y := hgen.le_I hdI
  obtain ⟨U₁, hU₁, hU₁L, heU₁, hdU₁⟩ := exists_fourGroupsMinus_conj h45 h66 hgen.cfg he
    hgen.not_mem_cd
  have hU₁I : U₁ ≤ Sec11.sec11K L e :=
    le_sec11K_of_not_mem_centralizer hE3 hcommE hU₁ (hEeq ▸ hdA) hU₁L heU₁ hdU₁ hdI
  have hU₁Y : U₁ ≤ Y := hU₁I.trans hgen.le_I
  have hEN : E ≤ Subgroup.normalizer (U₁ : Set G) := (mem_fourGroups_iff.mp hU₁.1).1
  have hUθ := inf_theta_eq_bot hpair.mem_S he he1 hEA hE3 hY (hEA.trans hAY) hU₁
  have hnC := not_le_thetaQuotCentralizer hdY (hEN (hEeq ▸ hdA)) hdU₁ hUθ
  have hYU := commutator_eq_of_le hY hU₁Y hnC
  obtain ⟨hU₂, hU₁1⟩ := Sec6.isPGroup_two_and_ne_bot_of_mem_fourGroups hU₁.1
  have hY0 : Y ∈ lZero E := by
    refine ⟨mem_thetaComponentFamily_iff.mpr ⟨e, heE, he1, hY⟩, U₁,
      (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).mpr ⟨hU₁Y, hU₂, hEN⟩, ?_⟩
    intro hle
    apply hU₁1
    rw [← hU₁.2] at hle
    have h1 : U₁ ≤ U₁ ⊓ inSubgroup (aschbacherSolvableCore 3) Y := le_inf le_rfl hle
    rw [hUθ] at h1
    exact le_bot_iff.mp h1
  have hYs : Y ∈ lZeroStarAt A e :=
    Sec6.mem_lZeroStarAt_of_inf_le_zpowers h45 hpair.standing hpair.mem_S hpair.mem_E heE he1 hY
      hY0 (le_of_eq hgen.cent)
  have hA : ∀ L' ∈ thetaComponentsAt 3 e, A ≤ Subgroup.normalizer (L' : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG4 hAe he he1
  have hVN := lThreeV_le_normalizer (U := U₁) hEA hA hY
  have hYV : ⁅Y, lThreeV E U₁ e⁆ = Y :=
    Sec6.commutator_eq_of_not_le_theta (Sec6.isPerfect_of_mem_thetaComponentsAt hY)
      (Sec6.isQuasisimple_of_mem_thetaComponentsAt hY) hVN
      (hV G A E U c L d U₀ a X e Y hgen U₁ hU₁ hU₁I heU₁)
  exact ⟨U₁, hU₁.1, Y, ⟨heE, heU₁⟩, he1, hYs, hU₁Y.trans Subgroup.le_normalizer, hVN, hYU, hYV⟩

theorem item2125Star_of_local (h45 : Sec4.Item4_5) (h66 : Sec6.Item6_6)
    (hLoc : Item2125StarLocal) : Item2125Star :=
  item2125Star_of_starV h45 h66 (item2125StarV_of_local h45 h66 hLoc)

end CFSG.RankThree.PartTwo.Sec21
