module

public import CFSG.LocalAnalysis.StandardType.GGTBJTwE6LeviSplitThreeFrameAux
public import CFSG.LocalAnalysis.StandardType.GGTorusF4Split
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6RankOuter

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.LieType.AlgebraicGroups
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.Chevalley.TwistedE6Cover

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem twE6Split_frame
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {n p : ℕ} [Fact p.Prime] [NeZero p]
    (hn : 2 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n)
    (hp2 : p ≠ 2) (hpn : p ∣ 2 ^ n - 1)
    {ζ : Kˣ} (hζo : orderOf ζ = p) (hζ : ζ ^ p = 1) (hζσ : σ (ζ : K) = ζ) :
    ∃ (nk : Fin Tag.F4.rank → ↥(graphFixedRootGroup TwistTag.E6 K σ))
      (wt : GGTorusTorWit (2 ^ n - 1) 4 ↥(graphFixedRootGroup TwistTag.E6 K σ)
        ((ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range.map
          (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
            MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)))),
      (∀ k s, nk k * ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) * (nk k)⁻¹ =
        ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
          (Multiplicative.ofAdd (TableBExc.torusAct .F4 p (simple .F4 k) s))) ∧
      (∀ k, wt.n k = nk k) ∧ wt.Holds CartanMatrix.F₄ CoxeterMatrix.F₄ := by
  classical
  have hp : p.Prime := Fact.out
  obtain ⟨σ0, hσ0, hσ0ord, -, -, -⟩ :=
    finite_graph_field_parameter_fields TwistTag.E6 Nat.prime_two (by omega) K hK
  have hσeq : ∀ c, σ c = σ0 c := fun c => by rw [hσ c, hσ0 c]
  have hσ0sq : σ0 ^ 2 = 1 := by
    have h2 : orderOf σ0 = 2 := hσ0ord
    rw [← h2]
    exact pow_orderOf_eq_one σ0
  have hσσ0 : ∀ c, σ0 (σ0 c) = c := by
    intro c
    have h := congrArg (fun f : K ≃+* K => f c) hσ0sq
    simpa using h
  have hσσ : ∀ c, σ (σ c) = c := fun c => by rw [hσeq, hσeq]; exact hσσ0 c
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζo
    exact hp.ne_one hζo.symm
  have hfixcard : Nat.card (fixField σ) = 2 ^ n :=
    E6RelativeTorus.natCard_fixField σ (by omega) hK hσ
  obtain ⟨l⟩ := F4SplitTorus.exists_unitValue_equiv (K := fixField σ)
  rw [hfixcard] at l
  obtain ⟨B, hCB, hBC⟩ := exists_int_matrix_inverse_mod_of_isUnit_det
    (m := 2 ^ n - 1) CartanMatrix.F₄ (by
      have hdet : CartanMatrix.F₄.det = 1 := by decide +kernel
      rw [hdet]
      simpa using (isUnit_one : IsUnit (1 : ZMod (2 ^ n - 1))))
  let E0 : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    (ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range
  let Tsc : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ) := E6RelativeTorus.fullTorus σ
  let κ : Fin 4 → Fin TwistTag.E6.foldedTag.rank := fun k => k
  let nn : Fin 4 → ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    fun k => E6RelativeWeyl.nNative (σ := σ) (κ k)
  have hcenter : Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ) = ⊥ := by
    obtain ⟨e⟩ := TwE6Rank.exists_mulEquiv_graphFixedRootGroup (by omega) hK σ hσ
    rw [← Subgroup.map_center_eq e, TwE6Delta.center_recipeR_eq_bot (by omega) hK,
      Subgroup.map_bot]
  have hconj : Function.Injective (MulAut.conj :
      ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  obtain ⟨hnN, -, e, he⟩ := tw3f_markedWeyl σ hp2 hζo hζ hζσ
  let eNat : CoxeterMatrix.F₄.Group ≃*
      ↥(ggAutomizer (⊤ : Subgroup ↥(graphFixedRootGroup TwistTag.E6 K σ)) E0) :=
    ggF4Row_coxeterGroupEquiv.trans e
  have heNat : ∀ k : Fin 4,
      (eNat (CoxeterMatrix.F₄.simple k) : MulAut ↥E0) = ggConjAut E0 (hnN (κ k)) := by
    intro k
    have h2 : ggF4Row_coxeterGroupEquiv (CoxeterMatrix.F₄.simple k) = simple Tag.F4 (κ k) :=
      ggF4Row_coxeterGroupEquiv_simple (Fin.cast (by rfl) k)
    change (e (ggF4Row_coxeterGroupEquiv (CoxeterMatrix.F₄.simple k)) : MulAut ↥E0) = _
    rw [h2]
    exact he (κ k)
  have hnN' : ∀ k : Fin 4,
      nn k ∈ Subgroup.normalizer (E0 : Set ↥(graphFixedRootGroup TwistTag.E6 K σ)) :=
    fun k => hnN (κ k)
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_innerImage E0 hconj nn hnN' eNat heNat
  let A0 : Subgroup (MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)) := scalarA E0
  let ρ : CoxeterMatrix.F₄.Group →* MulAut ↥A0 :=
    (ggAutomizer (MulAut.conj :
      ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range A0).subtype.comp eA.toMonoidHom
  have hρ : Function.Injective ρ := Subtype.val_injective.comp eA.injective
  have hρrange : ρ.range = ggAutomizer (MulAut.conj :
      ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range A0 := by
    ext a
    constructor
    · rintro ⟨g, rfl⟩
      exact (eA g).2
    · intro ha
      obtain ⟨g, hg⟩ := eA.surjective ⟨a, ha⟩
      exact ⟨g, congrArg Subtype.val hg⟩
  have hρsimple : ∀ k (a : ↥A0),
      ((ρ (CoxeterMatrix.F₄.simple k) a : ↥A0) : MulAut _) =
        MulAut.conj (nn k) * (a : MulAut _) * (MulAut.conj (nn k))⁻¹ := by
    intro k a
    rw [show ρ (CoxeterMatrix.F₄.simple k) =
      (eA (CoxeterMatrix.F₄.simple k) : MulAut ↥A0) from rfl, heA k, ggConjAut_apply]
  let u : Fin 4 → ℕ := ![2, 2, 1, 1]
  let Ψ : (Fin 4 → (fixField σ)ˣ) →* (Fin Tag.F4.rank → (fixField σ)ˣ) :=
    { toFun := fun a j => a (f4FoldedIndex j) ^ u j
      map_one' := by funext j; exact one_pow (u j)
      map_mul' := by
        intro a b
        funext j
        exact mul_pow (a (f4FoldedIndex j)) (b (f4FoldedIndex j)) (u j) }
  let φ : (Fin 4 → (fixField σ)ˣ) →*
      ↥(graphFixedRootGroup TwistTag.E6 K σ) :=
    (E6RelativeTorus.coordHom σ hσσ).comp Ψ
  have hcard_units : Nat.card (fixField σ)ˣ = 2 ^ n - 1 := by
    rw [Nat.card_units, hfixcard]
  obtain ⟨ζ0, hζ0o⟩ := exists_prime_orderOf_dvd_card' p (by rw [hcard_units]; exact hpn)
  have hζ0p : ζ0 ^ p = 1 := hζ0o ▸ pow_orderOf_eq_one ζ0
  have hζ01 : ζ0 ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ0o
    exact hp.ne_one hζ0o.symm
  have hpow : 2 ^ n = 2 * 2 ^ (n - 1) := by
    conv_lhs => rw [show n = n - 1 + 1 by omega, pow_succ]
    rw [mul_comm]
  have h2n : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
  have h2ngt : 1 < 2 ^ n := by
    have := Nat.pow_le_pow_right (by norm_num : 1 ≤ 2) hn
    omega
  have hodd : Odd (Nat.card (fixField σ)ˣ) := by
    rw [hcard_units]
    refine ⟨2 ^ (n - 1) - 1, ?_⟩
    have h1 : 1 ≤ 2 ^ (n - 1) := Nat.one_le_pow _ _ (by norm_num)
    omega
  have hsq_one : ∀ x : (fixField σ)ˣ, x ^ 2 = 1 → x = 1 := by
    intro x hx
    have hcop : Nat.Coprime 2 (Nat.card (fixField σ)ˣ) := Nat.coprime_two_left.mpr hodd
    have hd : orderOf x ∣ Nat.gcd 2 (Nat.card (fixField σ)ˣ) :=
      Nat.dvd_gcd (orderOf_dvd_iff_pow_eq_one.mpr hx) (orderOf_dvd_natCard x)
    rw [hcop.gcd_eq_one] at hd
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hd)
  have hpow_card : ∀ x : (fixField σ)ˣ, x ^ 2 ^ n = x := by
    intro x
    have h1 : x ^ (2 ^ n - 1) = 1 :=
      orderOf_dvd_iff_pow_eq_one.mp (by rw [← hcard_units]; exact orderOf_dvd_natCard x)
    have h2 : 2 ^ n = 2 ^ n - 1 + 1 := by omega
    rw [h2, pow_succ, h1, one_mul]
  have hu_eq : ∀ j : Fin 4, u j = 1 ∨ u j = 2 := by
    intro j
    fin_cases j <;> (first | left; rfl | right; rfl)
  have hΨ_surj : Function.Surjective Ψ := by
    intro b
    refine ⟨fun i => (b (f4FoldedIndex i)) ^
      (if u (f4FoldedIndex i) = 1 then 1 else 2 ^ (n - 1)), ?_⟩
    funext j
    have hff : f4FoldedIndex (f4FoldedIndex j) = j := by fin_cases j <;> rfl
    simp only [Ψ, MonoidHom.coe_mk, OneHom.coe_mk, hff]
    rcases hu_eq j with h | h
    · rw [h]
      simp
    · rw [h, if_neg (by decide : ¬ ((2 : ℕ) = 1)), ← pow_mul,
        show 2 ^ (n - 1) * 2 = 2 ^ n by rw [hpow, mul_comm], hpow_card]
  have hΨ_inj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    funext i
    have hff : f4FoldedIndex (f4FoldedIndex i) = i := by fin_cases i <;> rfl
    have hi : a i ^ u (f4FoldedIndex i) = 1 := by
      have h := congrFun ha (f4FoldedIndex i)
      simp only [Ψ, MonoidHom.coe_mk, OneHom.coe_mk, hff] at h
      exact h
    rcases hu_eq (f4FoldedIndex i) with h | h
    · rw [h, pow_one] at hi
      exact hi
    · exact hsq_one _ (by simpa only [h] using hi)
  have hφrange : φ.range = (E6RelativeTorus.coordHom σ hσσ).range := by
    apply le_antisymm
    · rintro _ ⟨a, rfl⟩
      exact ⟨Ψ a, rfl⟩
    · rintro _ ⟨b, rfl⟩
      obtain ⟨a, rfl⟩ := hΨ_surj b
      exact ⟨a, rfl⟩
  have hFormula : ∀ k : Fin 4, ∀ a : Fin 4 → (fixField σ)ˣ,
      nn k * φ a * (nn k)⁻¹ =
        φ a * (φ (corTuple CartanMatrix.F₄.transpose k (a k)))⁻¹ := by
    intro k a
    apply Subtype.ext
    have h := E6RelativeTorus.orbitN_conj_coordHom σ hσσ (f4FoldedIndex k) (Ψ a)
    have hff : f4FoldedIndex (f4FoldedIndex k) = k := by fin_cases k <;> rfl
    have h1 : f4FoldedIndex (f4FoldedIndex k) = κ k := by fin_cases k <;> rfl
    have h2 : (Ψ a) (f4FoldedIndex k) = (a k) ^ (u (f4FoldedIndex k)) := by
      simp only [Ψ, MonoidHom.coe_mk, OneHom.coe_mk, hff]
    have h3 : corTuple CartanMatrix.F₄.transpose (f4FoldedIndex k)
          ((a k) ^ (u (f4FoldedIndex k))) =
        Ψ (corTuple CartanMatrix.F₄.transpose k (a k)) := by
      funext i
      have he : (u (f4FoldedIndex k) : ℤ) *
            CartanMatrix.F₄.transpose (f4FoldedIndex k) i =
          CartanMatrix.F₄.transpose k (f4FoldedIndex i) * (u i : ℤ) := by
        fin_cases i <;> fin_cases k <;> decide
      simp only [corTuple, Ψ, MonoidHom.coe_mk, OneHom.coe_mk]
      rw [← zpow_natCast (a k) (u (f4FoldedIndex k)), ← zpow_mul, he, zpow_mul,
        zpow_natCast]
    rw [h1] at h
    rw [h2] at h
    change (nn k : ModGL TwistTag.E6.tag K) *
        (E6RelativeTorus.coordHom σ hσσ (Ψ a) : ModGL TwistTag.E6.tag K) *
        (nn k : ModGL TwistTag.E6.tag K)⁻¹ =
      (E6RelativeTorus.coordHom σ hσσ (Ψ a) : ModGL TwistTag.E6.tag K) *
        (E6RelativeTorus.coordHom σ hσσ
          (Ψ (corTuple CartanMatrix.F₄.transpose k (a k))) : ModGL TwistTag.E6.tag K)⁻¹
    refine h.trans ?_
    exact congrArg (fun x => (E6RelativeTorus.coordHom σ hσσ (Ψ a) : ModGL TwistTag.E6.tag K) *
      (E6RelativeTorus.coordHom σ hσσ x : ModGL TwistTag.E6.tag K)⁻¹) h3
  have hE : ∀ g, g ∈ E0 ↔ g ^ p = 1 ∧ g ∈ φ.range := by
    intro g
    rw [hφrange]
    exact tw3f_mem_standardFrame_iff σ hσσ hp2 h2ngt hσ hpn hζo hζ hζσ g
  have hφZ : ∀ a, φ a ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ) → a = 1 := by
    intro a ha
    rw [hcenter, Subgroup.mem_bot] at ha
    have h1 : Ψ a = 1 := E6RelativeTorus.coordHom_injective σ hσσ
      (ha.trans (map_one (E6RelativeTorus.coordHom σ hσσ)).symm)
    exact hΨ_inj (h1.trans (map_one Ψ).symm)
  have hTsc_comm : ∀ a, ∀ t ∈ Tsc, Commute (φ a) t := by
    intro a t ht
    exact E6RelativeTorus.commute_coordHom_of_mem_fullTorus σ hσσ (Ψ a) ht
  have hTsc_tors : ∀ t ∈ Tsc, t ^ (2 ^ n - 1) = 1 → t ∈ φ.range := by
    intro t ht htq
    rw [hφrange]
    exact E6RelativeTorus.mem_range_coordHom_of_mem_fullTorus σ hσσ (q := 2 ^ n)
      h2ngt hσ ht htq
  have hTsc_odd : ∀ z ∈ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ),
      Odd (orderOf z) → z ∈ Tsc := by
    intro z hz _
    rw [hcenter, Subgroup.mem_bot] at hz
    rw [hz]
    exact Tsc.one_mem
  have hcent : ∀ g : ↥(graphFixedRootGroup TwistTag.E6 K σ),
      (∀ e ∈ E0, g * e * g⁻¹ * e⁻¹ ∈
        Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ)) →
      g ∈ Tsc ⊔ Subgroup.center ↥(graphFixedRootGroup TwistTag.E6 K σ) := by
    intro g hg
    have hgcent : g ∈ Subgroup.centralizer
        (E0 : Set ↥(graphFixedRootGroup TwistTag.E6 K σ)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro e he
      have h := hg e he
      rw [hcenter, Subgroup.mem_bot] at h
      have h1 : g * e = e * g := by
        calc g * e = (g * e * g⁻¹ * e⁻¹) * (e * g) := by group
          _ = 1 * (e * g) := by rw [h]
          _ = e * g := one_mul _
      exact h1.symm
    have hle := tw3f_centralizer_le_fullTorus σ hp2 hζo hζ hζσ hgcent
    rw [hcenter]
    exact Subgroup.mem_sup_left (by simpa only [Tsc] using hle)
  obtain ⟨w, -, -, -, hwn, hw⟩ := exists_ggTorusTorWit_of_rootCoordinates_tsc
    l φ ((E6RelativeTorus.coordHom_injective σ hσσ).comp hΨ_inj) CartanMatrix.F₄ B hCB hBC
    hφZ Tsc hTsc_comm hTsc_tors hTsc_odd E0 hE ζ0 hζ0p hζ01 nn hnA hFormula hcent
    CoxeterMatrix.F₄ ρ hρ hρrange hρsimple
  refine ⟨nn, w, ?_, ?_, hw⟩
  · intro k s
    have h := E6RelativeWeyl.nNative_conj (σ := σ) (hp := hp) (hζσ := hζσ)
      (hζo := hζo) (hζ := hζ) (a := κ k) (s := s)
    simpa only [nn, E6RelativeWeyl.stdFrame] using h
  · intro k
    exact hwn k

theorem twE6Split_frame_three
    {K : Type} [Field K] [Finite K] (σ : K →+* K) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ 2 ^ n) (h3 : 3 ∣ 2 ^ n - 1)
    {ζ : Kˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1) (hζσ : σ (ζ : K) = ζ) :
    ∃ (nk : Fin Tag.F4.rank → ↥(graphFixedRootGroup TwistTag.E6 K σ))
      (wt : GGTorusTorWit (2 ^ n - 1) 4 ↥(graphFixedRootGroup TwistTag.E6 K σ)
        ((ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ).range.map
          (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
            MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)))),
      (∀ k s, nk k * ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ (Multiplicative.ofAdd s) * (nk k)⁻¹ =
        ExcFrames.twE6SplitFrameHom σ ζ hζ hζσ
          (Multiplicative.ofAdd (TableBExc.torusAct .F4 3 (simple .F4 k) s))) ∧
      (∀ k, wt.n k = nk k) ∧ wt.Holds CartanMatrix.F₄ CoxeterMatrix.F₄ := by
  exact twE6Split_frame (p := 3) σ hn hK hσ (by norm_num) h3 hζo hζ hζσ

end CFSG.StandardType

end
