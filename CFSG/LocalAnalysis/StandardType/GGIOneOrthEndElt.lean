module

public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestOddEndMat
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
public import CFSG.GroupTheory.WeirSylow.OrthogonalOrders

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGEndNodeIOneElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A As : Subgroup R, IsElemAbelian p A → A ≤ As → IsElemAbelian p As →
    p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    (∃ U : Subgroup R, U ≠ ⊥ ∧ IsPGroup 2 U ∧ A ≤ Subgroup.normalizer (U : Set R)) →
    ∃ t ∈ A, TableBOrth.IsEndNode As t ∧
      (p = 3 → 7 ∣ Nat.card (LargeEvenLayer (Subgroup.centralizer ({t} : Set R))))

theorem ggEndNodeIOneElt_of_mulEquiv {p r : ℕ} {R R' : Type} [Group R] [Group R'] (φ : R ≃* R')
    (h : GGEndNodeIOneElt p r R) : GGEndNodeIOneElt p r R' := by
  intro A As hA hAAs hAs hr h3 ⟨U, hU1, hU2, hAU⟩
  set A₀ := A.map φ.symm.toMonoidHom with hA₀
  set As₀ := As.map φ.symm.toMonoidHom with hAs₀
  have hcard : Nat.card A₀ = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ φ.symm.injective).toEquiv).symm
  have hU₀1 : U.map φ.symm.toMonoidHom ≠ ⊥ := by
    intro h0
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have : φ.symm u ∈ U.map φ.symm.toMonoidHom := ⟨u, hu, rfl⟩
    rw [h0, Subgroup.mem_bot] at this
    rw [Subgroup.mem_bot, ← φ.apply_symm_apply u, this, map_one]
  have hU₀N : A₀ ≤ Subgroup.normalizer ((U.map φ.symm.toMonoidHom : Subgroup R) : Set R) := by
    rw [Subgroup.le_normalizer_iff]
    rintro _ ⟨a, ha, rfl⟩ _ ⟨u, hu, rfl⟩
    refine ⟨a * u * a⁻¹, Subgroup.le_normalizer_iff.mp hAU a ha u hu, ?_⟩
    simp
  obtain ⟨t, htA, hend, h7⟩ := h A₀ As₀ (TableB.isElemAbelian_map hA _)
    (Subgroup.map_mono hAAs) (TableB.isElemAbelian_map hAs _) (hcard ▸ hr) (hcard ▸ h3)
    ⟨U.map φ.symm.toMonoidHom, hU₀1, hU2.map _, hU₀N⟩
  have hid : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id R' :=
    MonoidHom.ext fun x => φ.apply_symm_apply x
  have hAs' : As₀.map φ.toMonoidHom = As := by
    rw [hAs₀, Subgroup.map_map, hid, Subgroup.map_id]
  have hend' := hend.map φ
  rw [hAs'] at hend'
  refine ⟨φ t, ?_, hend', fun hp3 => ?_⟩
  · obtain ⟨a, ha, rfl⟩ := htA
    simpa using ha
  · have hC : Subgroup.centralizer ({φ t} : Set R') =
        (Subgroup.centralizer ({t} : Set R)).map φ.toMonoidHom :=
      (TableBSymp.map_centralizer_singleton φ t).symm
    rw [hC, largeEvenLayer_map_of_injective _ φ.injective,
      Subgroup.card_map_of_injective φ.injective]
    exact h7 hp3

namespace IOneOrthEnd

open Module CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.Classical2 CFSG.StandardType.OrthRestOdd

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem seven_dvd_card_orthDerived {n : ℕ} (hK : Nat.card K = 2 ^ n) {W : Type} [AddCommGroup W]
    [Module K W] [FiniteDimensional K W] {R : QuadraticForm K W}
    (hR : (QuadraticMap.polarBilin R).Nondegenerate) (hW : 8 ≤ finrank K W) :
    7 ∣ Nat.card (orthDerived R) := by
  obtain ⟨k, hk⟩ := even_finrank_of_regular R hR
  obtain ⟨m, rfl⟩ : ∃ m, k = m + 1 := ⟨k - 1, by omega⟩
  have hdim : finrank K W = 2 * (m + 1) := by omega
  have hm3 : 3 ≤ m := by omega
  have h7 : 7 ∣ Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) := by
    obtain ⟨ε, hε⟩ : ∃ ε : ℤ, (Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) =
        2 * (Nat.card K : ℤ) ^ (m * (m + 1)) * ((Nat.card K : ℤ) ^ (m + 1) - ε) *
          ∏ i ∈ Finset.Icc 1 m, (((Nat.card K : ℤ) ^ 2) ^ i - 1) := by
      by_cases hpl : CFSG.GroupTheory.WeirSylow.IsPlusType R
      · exact ⟨1, CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hR hdim
          (Or.inl ⟨rfl, hpl⟩)⟩
      · exact ⟨-1, CFSG.GroupTheory.WeirSylow.natCard_orthogonalGroup_of_type hR hdim
          (Or.inr ⟨rfl, hpl⟩)⟩
    have hq6 : (7 : ℤ) ∣ ((Nat.card K : ℤ) ^ 2) ^ 3 - 1 := by
      have h1 : ((Nat.card K : ℤ) ^ 2) ^ 3 = (64 : ℤ) ^ n := by
        rw [hK]
        push_cast
        rw [← pow_mul, ← pow_mul, show (64 : ℤ) = 2 ^ 6 by norm_num, ← pow_mul]
        congr 1
        ring
      have h2 : (64 : ℤ) - 1 ∣ (64 : ℤ) ^ n - 1 ^ n := sub_dvd_pow_sub_pow _ _ _
      rw [h1]
      rw [one_pow] at h2
      exact (show (7 : ℤ) ∣ 64 - 1 by norm_num).trans h2
    have hdvd : (7 : ℤ) ∣ (Nat.card (TauCeti.QuadraticMap.orthogonalGroup R) : ℤ) := by
      rw [hε]
      refine Dvd.dvd.mul_left ?_ _
      exact hq6.trans (Finset.dvd_prod_of_mem (fun i => (((Nat.card K : ℤ) ^ 2) ^ i - 1))
        (Finset.mem_Icc.mpr ⟨by norm_num, hm3⟩))
    exact_mod_cast hdvd
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 7 h7
  have hg7 : (g : W ≃ₗ[K] W) ^ 7 = 1 := by
    have h1 := pow_orderOf_eq_one g
    rw [hg] at h1
    exact congrArg Subtype.val h1
  obtain ⟨-, -, hodd⟩ := orthDerived_facts R hR (by omega : 6 ≤ finrank K W)
  have hgΩ : (g : W ≃ₗ[K] W) ∈ orthDerived R := hodd g g.2 7 (by decide) hg7
  have hord : orderOf (⟨(g : W ≃ₗ[K] W), hgΩ⟩ : orthDerived R) = 7 := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hg]
  rw [← hord]
  exact orderOf_dvd_natCard _

theorem layer_equiv_of_commSpace_two (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hV : 8 ≤ finrank K V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {t : orthDerived Q} (htp : t ^ p = 1)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2) :
    Nonempty (LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q))) ≃*
      orthDerived (Q.comp (fixedSpace (t : V ≃ₗ[K] V)).subtype)) := by
  classical
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set x : V ≃ₗ[K] V := ↑t with hxdef
  have hxp : x ^ p = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, htp]
    rfl
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup t.2
  have hx : OddOrderIsometry Q p x := ⟨hxO, hxp, hpK, fun v hv => hQ.1 v fun w => by
    rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hxp
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hW6 : 6 ≤ finrank K (fixedSpace x) := by rw [fixedSpace_eq_lit]; omega
  obtain ⟨hq, hcenter, hodd⟩ := orthDerived_facts (Q.comp (fixedSpace x).subtype)
    hx.polarBilin_fixed_nondegenerate hW6
  set D₀ := supportedFixedDerived Q x with hD₀
  have hD₀Ω : D₀ ≤ orthDerived Q := hx.supportedFixedDerived_le_orthDerived
  set D : Subgroup (orthDerived Q) := D₀.subgroupOf (orthDerived Q) with hD
  have hmemC : ∀ y : orthDerived Q,
      y ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)) ↔
        (y : V ≃ₗ[K] V) ∈ isometryCentralizer Q x := by
    intro y
    rw [Subgroup.mem_centralizer_singleton_iff, isometryCentralizer, Subgroup.mem_inf,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact ⟨CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup y.2,
        congrArg Subtype.val h⟩
    · rintro ⟨-, h⟩
      exact Subtype.ext h
  have hDH : D ≤ Subgroup.centralizer ({t} : Set (orthDerived Q)) := by
    intro y hy
    rw [hmemC]
    exact supportedFixedDerived_le_isometryCentralizer (Subgroup.mem_subgroupOf.mp hy)
  have hcomm : ∀ g ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)),
      ∀ h ∈ Subgroup.centralizer ({t} : Set (orthDerived Q)), g * h * g⁻¹ * h⁻¹ ∈ D := by
    intro g hg h hh
    rw [hD, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact commutator_mem_supportedFixedDerived hx hK1 ht2 ((hmemC g).mp hg) ((hmemC h).mp hh)
  have hDq : CFSG.IsQuasisimple D := by
    have e1 : D ≃* D₀ := Subgroup.subgroupOfEquivOfLe hD₀Ω
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (e1.trans (supportedFixedDerivedEquiv hx)).symm hq
  obtain ⟨hlay, -⟩ := TableBSymp.largeEvenLayer_eq_of_commutator_mem hDH hcomm hDq
  exact ⟨(MulEquiv.subgroupCongr hlay).trans
    ((Subgroup.subgroupOfEquivOfLe hD₀Ω).trans (supportedFixedDerivedEquiv hx))⟩

theorem seven_dvd_card_layer {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : 10 ≤ finrank K V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {t : orthDerived Q}
    (htp : t ^ p = 1)
    (ht2 : finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2) :
    7 ∣ Nat.card (LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q)))) := by
  obtain ⟨e⟩ := layer_equiv_of_commSpace_two hQ (by omega) hp hp2 hK1 htp ht2
  rw [Nat.card_congr e.toEquiv]
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set x : V ≃ₗ[K] V := ↑t with hxdef
  have hxp : x ^ p = 1 := by
    rw [hxdef, ← Subgroup.coe_pow, htp]
    rfl
  have hxO : x ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup t.2
  have hx : OddOrderIsometry Q p x := ⟨hxO, hxp, hpK, fun v hv => hQ.1 v fun w => by
    rw [QuadraticMap.polarBilin_apply_apply]; exact hv w⟩
  have hc := CFSG.RankThree.PartOne.LIT.isCompl_fixedSpace_commSpace hpK hxp
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hW8 : 8 ≤ finrank K (fixedSpace x) := by rw [fixedSpace_eq_lit]; omega
  exact seven_dvd_card_orthDerived hK hx.polarBilin_fixed_nondegenerate hW8

theorem exists_commSpace_two_of_twoSubgroup (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hV : 6 ≤ finrank K V) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {A : Subgroup (orthDerived Q)}
    (hA : IsElemAbelian p A) (hcard : p ^ (finrank K V / 2 - 1) ≤ Nat.card A)
    {V₀ : Subgroup (orthDerived Q)} (hV₀ : V₀ ≠ ⊥) (hV₀2 : IsPGroup 2 V₀)
    (hnorm : ∀ a ∈ A, ∀ v ∈ V₀, a * v * a⁻¹ ∈ V₀) :
    ∃ t ∈ A, t ≠ 1 ∧
      finrank K (CFSG.RankThree.PartOne.LIT.commSpace (t : V ≃ₗ[K] V)) = 2 := by
  classical
  obtain ⟨Y, hY, hYinv, hYiso⟩ := isotropic_of_two_subgroup hV₀ hV₀2 hnorm
  have hpK : (p : K) ≠ 0 := natCast_ne_zero_of_odd hp hp2
  set E := A.map (orthDerived Q).subtype with hEdef
  have : Finite V := Module.finite_of_finite K
  have : Finite (V ≃ₗ[K] V) := Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
    fun e₁ e₂ h => LinearEquiv.ext (congrFun h)
  have hE : IsoGroup (QuadraticMap.polarBilin Q) p E :=
    { sep := hQ.1
      alt := fun v => by rw [QuadraticMap.polarBilin_apply_apply]; exact polar_self_eq_zero Q v
      comm := by
        rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
        exact congrArg Subtype.val (TableB.IsElemAbelian.comm hA ha hb)
      pow := by
        rintro _ ⟨a, ha, rfl⟩
        rw [← map_pow, hA.2 a ha, map_one]
      pres := by
        rintro _ ⟨a, ha, rfl⟩ u w
        rw [QuadraticMap.polarBilin_apply_apply, QuadraticMap.polarBilin_apply_apply]
        exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup
          (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup a.2) u w }
  have hcardE : Nat.card E = Nat.card A :=
    (Nat.card_congr (A.equivMapOfInjective _ Subtype.val_injective).toEquiv).symm
  obtain ⟨t', ⟨t, htA, rfl⟩, ht1, ht2⟩ := exists_commSpace_two_of_isotropic hp hpK hK1
    hV hE hY (by rintro _ ⟨a, ha, rfl⟩ y hy; exact hYinv a ha y hy)
    (fun y hy y' hy' => by rw [QuadraticMap.polarBilin_apply_apply]; exact hYiso y hy y' hy')
    (hcardE ▸ hcard)
  exact ⟨t, htA, fun h => ht1 (by rw [h]; rfl), ht2⟩

theorem exists_endNode_pair {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : 10 ≤ finrank K V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1)
    {A As : Subgroup (orthDerived Q)} (hA : IsElemAbelian p A) (hAAs : A ≤ As)
    (hAs : IsElemAbelian p As) (hcard : p ^ (finrank K V / 2 - 1) ≤ Nat.card A)
    {V₀ : Subgroup (orthDerived Q)} (hV₀ : V₀ ≠ ⊥) (hV₀2 : IsPGroup 2 V₀)
    (hnorm : ∀ a ∈ A, ∀ v ∈ V₀, a * v * a⁻¹ ∈ V₀) :
    ∃ t ∈ A, TableBOrth.IsEndNode As t ∧
      7 ∣ Nat.card (LargeEvenLayer (Subgroup.centralizer ({t} : Set (orthDerived Q)))) := by
  obtain ⟨t, htA, ht1, ht2⟩ := exists_commSpace_two_of_twoSubgroup hQ (by omega) hp hp2 hK1 hA
    hcard hV₀ hV₀2 hnorm
  have htp : t ^ p = 1 := hA.2 t htA
  exact ⟨t, htA, isEndNode_of_commSpace_two hQ (by omega) hp hp2 hK1 hAs (hAAs htA) ht1 ht2,
    seven_dvd_card_layer hK hQ hV hp hp2 hK1 htp ht2⟩

theorem ggEndNodeIOneElt_orthDerived {n : ℕ} (hK : Nat.card K = 2 ^ n)
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hV : 10 ≤ finrank K V) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hK1 : ∀ c : K, c ^ p = 1 → c = 1) {r : ℕ}
    (hr : finrank K V / 2 - 1 = r) : GGEndNodeIOneElt p r (orthDerived Q) := by
  intro A As hA hAAs hAs hcard _ ⟨U, hU1, hU2, hAU⟩
  obtain ⟨t, htA, hend, h7⟩ := exists_endNode_pair hK hQ hV hp hp2 hK1 hA hAAs hAs (hr ▸ hcard)
    hU1 hU2 (Subgroup.le_normalizer_iff.mp hAU)
  exact ⟨t, htA, hend, fun _ => h7⟩

end IOneOrthEnd

end CFSG.StandardType
