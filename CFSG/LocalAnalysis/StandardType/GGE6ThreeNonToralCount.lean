module

public import CFSG.LocalAnalysis.StandardType.GGTableBE6ThreeEndNode
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderExcRestProofE6Ad
public import CFSG.LocalAnalysis.StandardType.GGTwE6HyperplaneTypes

public section

namespace CFSG.StandardType.E6NonToralThree

open CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley TableBExc.Three TableBExc.E6Three

open CFSG.StandardType.E6ThreeEnd

private theorem adAct_zero (a : WeylGroup .E6) :
    adAct .E6 3 a (0 : Fin Tag.E6.rank → ZMod 3) = 0 := by
  have h := NoOffRest.adAct_add (τ := Tag.E6) (p := 3) a
    (0 : Fin Tag.E6.rank → ZMod 3) (0 : Fin Tag.E6.rank → ZMod 3)
  have h' : adAct .E6 3 a 0 = adAct .E6 3 a 0 + adAct .E6 3 a 0 := by simpa using h
  have h2 : adAct .E6 3 a 0 + 0 = adAct .E6 3 a 0 + adAct .E6 3 a 0 := by simpa using h'
  exact (add_left_cancel h2).symm

private theorem adAct_neg (a : WeylGroup .E6) (x : Fin Tag.E6.rank → ZMod 3) :
    adAct .E6 3 a (-x) = -adAct .E6 3 a x := by
  have h := NoOffRest.adAct_add (τ := Tag.E6) (p := 3) a (-x) x
  have hneg : -x + x = 0 := neg_add_cancel x
  rw [hneg, adAct_zero a] at h
  exact eq_neg_of_add_eq_zero_left h.symm

private def fixSub (A : Subgroup (WeylGroup .E6)) : AddSubgroup (Fin Tag.E6.rank → ZMod 3) where
  carrier := {x | ∀ a ∈ A, adAct .E6 3 a x = x}
  add_mem' := by
    intro x y hx hy a ha
    change adAct .E6 3 a (x + y) = x + y
    rw [NoOffRest.adAct_add, hx a ha, hy a ha]
  zero_mem' := by
    intro a ha
    exact adAct_zero a
  neg_mem' := by
    intro x hx a ha
    change adAct .E6 3 a (-x) = -x
    rw [adAct_neg, hx a ha]

private theorem eq_range_of_hEA
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w) :
    A = ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).range := by
  ext w
  rw [hEA w, MonoidHom.mem_range]
  constructor
  · rintro ⟨e, he, hw⟩
    exact ⟨⟨e, he⟩, hw⟩
  · rintro ⟨e, hw⟩
    exact ⟨e, e.2, hw⟩

private theorem exists_rootDiagUnit_eq_of_mem_ker
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) :
    ∀ k : ((weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)).ker,
      ∃ x : Fin Tag.E6.rank → ZMod 3, (k : E) = rootDiagUnit .E6 (zetaVec ζ hζ x) := by
  intro k
  have hk : weylQuotientHom .E6 L
      ⟨((k : E) : ModGL .E6 L), hEM (k : E).2⟩ = 1 := k.2
  have hψ : psiHat .E6 L
      ⟨((k : E) : ModGL .E6 L), monomial_le_monoHat (hEM (k : E).2)⟩ = 1 := by
    rw [psiHat_of_mem_monomial (hEM (k : E).2)]
    exact hk
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_psiHat_eq_one hψ
  have hb' : ((k : E) : ModGL .E6 L) = rootDiagUnit .E6 b := hb
  have hk3 : ((k : E) : ModGL .E6 L) ^ 3 = 1 := hE.2 (k : E) (k : E).2
  rw [hb', rootDiagUnit_pow] at hk3
  have hb3 : b ^ 3 = 1 := rootDiagUnit_injective (hk3.trans rootDiagUnit_one.symm)
  obtain ⟨x, hx⟩ := exists_zetaVec_eq (p := 3) hζo hζ hb3
  exact ⟨x, by rw [hb', hx]⟩

theorem card_E_eq_card_A_mul_card_expE
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) [Finite E]
    (hE : IsElemAbelian 3 E) {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w) :
    Nat.card E = Nat.card A * Nat.card (expE ζ hζ E) := by
  classical
  let ρ : E →* WeylGroup .E6 := (weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)
  have hρ : ∀ e : E, ρ e = weylQuotientHom .E6 L ⟨(e : ModGL .E6 L), hEM e.2⟩ := fun _ => rfl
  have hAeq : A = ρ.range := eq_range_of_hEA hEM hEA
  have hker : ∀ k : ρ.ker, ∃ x : Fin Tag.E6.rank → ZMod 3,
      (k : E) = rootDiagUnit .E6 (zetaVec ζ hζ x) :=
    exists_rootDiagUnit_eq_of_mem_ker hζo hζ hEM hE
  let Φ : ρ.ker → expE ζ hζ E := fun k =>
    ⟨(hker k).choose, by
      rw [E6ThreeEnd.mem_expE, ← (hker k).choose_spec]
      exact (k : E).2⟩
  let Ψ : expE ζ hζ E → ρ.ker := fun x =>
    ⟨⟨rootDiagUnit .E6 (zetaVec ζ hζ x.1),
        (E6ThreeEnd.mem_expE).mp x.2⟩, by
      rw [MonoidHom.mem_ker, hρ]
      rw [← psiHat_of_mem_monomial (hEM ((E6ThreeEnd.mem_expE).mp x.2))]
      exact psiHat_eq (mapsRootLines_rootDiagUnit (zetaVec ζ hζ x.1))⟩
  have hleft : Function.LeftInverse Ψ Φ := by
    intro k
    apply Subtype.ext
    apply Subtype.ext
    exact ((hker k).choose_spec).symm
  have hright : Function.RightInverse Ψ Φ := by
    intro x
    apply Subtype.ext
    apply zetaVec_injective hζo hζ
    apply rootDiagUnit_injective
    simpa using ((hker (Ψ x)).choose_spec).symm
  have hcardker : Nat.card ρ.ker = Nat.card (expE ζ hζ E) :=
    Nat.card_congr { toFun := Φ, invFun := Ψ, left_inv := hleft, right_inv := hright }
  have hcardE := TableB.card_range_mul_card_ker ρ
  rw [← hAeq, hcardker] at hcardE
  exact hcardE.symm

private theorem expE_le_fixSub
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w) :
    expE ζ hζ E ≤ fixSub A := by
  intro x hx a ha
  change adAct .E6 3 a x = x
  obtain ⟨e, he, hwe⟩ := (hEA a).mp ha
  have hc := conj_rootDiagUnit_of_mem_monoHat
    (x := (⟨e, monomial_le_monoHat (hEM he)⟩ : monoHat .E6 L)) (zetaVec ζ hζ x)
  rw [psiHat_of_mem_monomial (hEM he), hwe, weylTuple_zetaVec] at hc
  have hdE : rootDiagUnit .E6 (zetaVec ζ hζ x) ∈ E := (E6ThreeEnd.mem_expE).mp hx
  have hcomm : e * rootDiagUnit .E6 (zetaVec ζ hζ x) * e⁻¹ =
      rootDiagUnit .E6 (zetaVec ζ hζ x) := by
    rw [TableB.IsElemAbelian.comm hE he hdE, mul_inv_cancel_right]
  have h2 : rootDiagUnit .E6 (zetaVec ζ hζ (adAct .E6 3 a x)) =
      rootDiagUnit .E6 (zetaVec ζ hζ x) := by
    rw [← hc, hcomm]
  exact zetaVec_injective hζo hζ (rootDiagUnit_injective h2)

theorem exists_planeKey_of_card_nine
    (H : AddSubgroup (Fin Tag.E6.rank → ZMod 3)) (hH : Nat.card H = 9)
    (hfix : ∀ v ∈ H, adWord .E6 3 wordE6C v = v) :
    ∃ k : Fin 3 → ZMod 3, k ≠ 0 ∧
      ∀ v, v ∈ H ↔ ∃ x : Fin 3 → ZMod 3,
        ∑ i, k i * x i = 0 ∧ v = TwE6HyperplaneTypes.combC x := by
  classical
  let c : (Fin 3 → ZMod 3) →+ (Fin Tag.E6.rank → ZMod 3) :=
    { toFun := TwE6HyperplaneTypes.combC
      map_zero' := by decide +kernel
      map_add' := TwE6HyperplaneTypes.combC_add }
  have hcinj : Function.Injective c := by
    change ∀ x y : Fin 3 → ZMod 3,
      TwE6HyperplaneTypes.combC x = TwE6HyperplaneTypes.combC y → x = y
    decide +kernel
  let X := H.comap c
  let f : X → H := fun x => ⟨c x, x.2⟩
  have hfinj : Function.Injective f := by
    intro x y h
    exact Subtype.ext (hcinj (congrArg Subtype.val h))
  have hfsurj : Function.Surjective f := by
    intro v
    obtain ⟨x, hx⟩ := TwE6HyperplaneTypes.exists_combC_of_adWord v (hfix v v.2)
    refine ⟨⟨x, ?_⟩, Subtype.ext hx.symm⟩
    change c x ∈ H
    change TwE6HyperplaneTypes.combC x ∈ H
    rw [← hx]
    exact v.2
  have hX : Nat.card X = 9 :=
    (Nat.card_congr (Equiv.ofBijective f ⟨hfinj, hfsurj⟩)).trans hH
  obtain ⟨k, hk⟩ := exists_forall_mem_iff_dot X (by rw [hX]; decide)
  have hk0 : k ≠ 0 := by
    intro h0
    have htop : X = ⊤ := eq_top_iff.mpr fun x _ => (hk x).mpr (by simp [h0])
    have hcard : Nat.card X = 27 := by
      rw [htop, Nat.card_congr (AddSubgroup.topEquiv : (⊤ : AddSubgroup (Fin 3 → ZMod 3)) ≃+ _).toEquiv]
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin]
      norm_num
    omega
  refine ⟨k, hk0, fun v => ⟨fun hv => ?_, ?_⟩⟩
  · obtain ⟨x, hx⟩ := TwE6HyperplaneTypes.exists_combC_of_adWord v (hfix v hv)
    refine ⟨x, (hk x).mp ?_, hx⟩
    change TwE6HyperplaneTypes.combC x ∈ H
    rwa [← hx]
  · rintro ⟨x, hx, rfl⟩
    exact (hk x).mpr hx

theorem exists_planeKey_of_zpowers_c_rank_three
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) [Finite E]
    (hE : IsElemAbelian 3 E) (hcard : Nat.card E = 3 ^ 3)
    (hEA : ∀ w, w ∈ Subgroup.zpowers cE6 ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w) :
    ∃ k : Fin 3 → ZMod 3, k ≠ 0 ∧
      ∀ v, v ∈ expE ζ hζ E ↔ ∃ x : Fin 3 → ZMod 3,
        ∑ i, k i * x i = 0 ∧ v = TwE6HyperplaneTypes.combC x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAcard : Nat.card (Subgroup.zpowers cE6) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime cE6_pow_three TwE6HyperplaneTypes.cE6_ne_one
  have hc := card_E_eq_card_A_mul_card_expE hζo hζ hEM hE hEA
  rw [hcard, hAcard] at hc
  have htor : Nat.card (expE ζ hζ E) = 9 := by omega
  refine exists_planeKey_of_card_nine (expE ζ hζ E) htor fun v hv => ?_
  have h := expE_le_fixSub hζo hζ hEM hE hEA hv cE6 (Subgroup.mem_zpowers cE6)
  change adAct .E6 3 cE6 v = v at h
  rw [adWord_eq_adAct]
  exact h

private theorem card_mul_card_fix_lt
    {L : Type} [Field L] {E : Subgroup (ModGL .E6 L)}
    (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hA1 : A ≠ ⊥)
    (hAg : ∀ i, A ≠ Subgroup.zpowers (gE6 i)) :
    Nat.card A * Nat.card (fixSub A) < 3 ^ 5 := by
  let ρ : E →* WeylGroup .E6 := (weylQuotientHom .E6 L).comp (Subgroup.inclusion hEM)
  have hAeq : A = ρ.range := eq_range_of_hEA hEM hEA
  have hAea : IsElemAbelian 3 A := by
    rw [hAeq]
    exact isElemAbelian_range
      (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hE a.2 b.2))
      (fun a => Subtype.ext (by simpa using hE.2 a a.2)) ρ
  have hAea' : IsElemAbelian 3 ρ.range := by rw [← hAeq]; exact hAea
  have hAS' : ρ.range ≤ modelHomE6.range := by rw [← hAeq]; exact hAS
  have hA1' : ρ.range ≠ ⊥ := by rw [← hAeq]; exact hA1
  rcases refined_E6 ρ.range hAS' hAea' hA1' with h | ⟨i, hi⟩
  · rw [← hAeq] at h
    exact h
  · exact absurd (hAeq.trans hi) (hAg i)

private theorem mul_eq_pow_four {P Q : ℕ} (hlo : 3 ^ 4 ≤ P * Q) (hhi : P * Q < 3 ^ 5)
    (hP : P ∣ 3 ^ 4) (hQ : Q ∣ 3 ^ 6) : P * Q = 3 ^ 4 := by
  obtain ⟨a, -, ha⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hP
  obtain ⟨c, -, hc⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hQ
  have hprod : P * Q = 3 ^ (a + c) := by rw [ha, hc, ← pow_add]
  have h4 : 4 ≤ a + c :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by rwa [hprod] at hlo)
  have h5 : a + c < 5 :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp (by rwa [hprod] at hhi)
  rw [hprod, show a + c = 4 by omega]

private theorem card_mul_card_fix_eq_range
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 4 ≤ Nat.card E)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hA1 : A ≠ ⊥)
    (hAg : ∀ i, A ≠ Subgroup.zpowers (gE6 i)) :
    Nat.card A * Nat.card (fixSub A) = 3 ^ 4 := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hζ : ζ ^ 3 = 1 := by simpa [hζo] using pow_orderOf_eq_one ζ
  have h1 := card_E_eq_card_A_mul_card_expE hζo hζ hEM hE hEA
  have h2 := expE_le_fixSub hζo hζ hEM hE hEA
  have hle : Nat.card (expE ζ hζ E) ≤ Nat.card (fixSub A) := by
    refine Nat.card_le_card_of_injective
      (fun x : expE ζ hζ E => (⟨x.1, h2 x.2⟩ : fixSub A)) ?_
    intro x y hxy
    exact Subtype.ext
      (congrArg (fun z : fixSub A => (z : Fin Tag.E6.rank → ZMod 3)) hxy)
  have hlt := card_mul_card_fix_lt hEM hE hEA hAS hA1 hAg
  have h3 : 3 ^ 4 ≤ Nat.card A * Nat.card (fixSub A) := by
    calc 3 ^ 4 ≤ Nat.card E := hcard
      _ = Nat.card A * Nat.card (expE ζ hζ E) := h1
      _ ≤ Nat.card A * Nat.card (fixSub A) := Nat.mul_le_mul_left _ hle
  have hdvdA : Nat.card A ∣ 3 ^ 4 := by
    have h := Subgroup.card_dvd_of_le hAS
    rwa [card_range_modelHomE6, show (81 : ℕ) = 3 ^ 4 by norm_num] at h
  have hdvdF : Nat.card (fixSub A) ∣ 3 ^ 6 := by
    have h := AddSubgroup.card_dvd_of_le (le_top : fixSub A ≤ ⊤)
    rw [AddSubgroup.card_top] at h
    have hV : Nat.card (Fin Tag.E6.rank → ZMod 3) = 3 ^ 6 := by
      rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin, show Tag.E6.rank = 6 from rfl]
    rwa [hV] at h
  exact mul_eq_pow_four h3 hlt hdvdA hdvdF

private theorem expE_eq_fixSub
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3) (hζ : ζ ^ 3 = 1)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 4 ≤ Nat.card E)
    {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E,
      weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hA1 : A ≠ ⊥)
    (hAg : ∀ i, A ≠ Subgroup.zpowers (gE6 i)) :
    expE ζ hζ E = fixSub A := by
  classical
  haveI : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hle : expE ζ hζ E ≤ fixSub A := expE_le_fixSub hζo hζ hEM hE hEA
  have h1 := card_E_eq_card_A_mul_card_expE hζo hζ hEM hE hEA
  have h3 := card_mul_card_fix_eq_range hζo hEM hE hcard hEA hAS hA1 hAg
  have hle_card : Nat.card (expE ζ hζ E) ≤ Nat.card (fixSub A) := by
    refine Nat.card_le_card_of_injective
      (fun x : expE ζ hζ E => (⟨x.1, hle x.2⟩ : fixSub A)) ?_
    intro x y hxy
    exact Subtype.ext
      (congrArg (fun z : fixSub A => (z : Fin Tag.E6.rank → ZMod 3)) hxy)
  have hE4 : 3 ^ 4 ≤ Nat.card A * Nat.card (expE ζ hζ E) := by
    rw [← h1]; exact hcard
  have hprod_le : Nat.card A * Nat.card (expE ζ hζ E) ≤
      Nat.card A * Nat.card (fixSub A) := Nat.mul_le_mul_left _ hle_card
  have hEq : Nat.card A * Nat.card (expE ζ hζ E) = 3 ^ 4 :=
    le_antisymm (h3 ▸ hprod_le) hE4
  have hApos : 0 < Nat.card A :=
    Nat.pos_of_dvd_of_pos (by
      have h := Subgroup.card_dvd_of_le hAS
      rwa [card_range_modelHomE6, show (81 : ℕ) = 3 ^ 4 by norm_num] at h) (by norm_num)
  have hcards : Nat.card (expE ζ hζ E) = Nat.card (fixSub A) :=
    Nat.mul_left_cancel hApos (hEq.trans h3.symm)
  exact AddSubgroup.eq_of_le_of_card_ge hle (le_of_eq hcards.symm)

theorem card_mul_card_fix_eq
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3)
    {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L) (hE : IsElemAbelian 3 E)
    (hcard : 3 ^ 4 ≤ Nat.card E) {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E, weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hA1 : A ≠ ⊥) (hAg : ∀ i, A ≠ Subgroup.zpowers (gE6 i)) :
    Nat.card A * Nat.card {x : Fin Tag.E6.rank → ZMod 3 // ∀ a ∈ A, adAct .E6 3 a x = x} =
      3 ^ 4 := by
  exact card_mul_card_fix_eq_range hζo hEM hE hcard hEA hAS hA1 hAg

theorem rootDiagUnit_zetaVec_mem
    {L : Type} [Field L] {ζ : Lˣ} (hζo : orderOf ζ = 3)
    (hζ : ζ ^ 3 = 1) {E : Subgroup (ModGL .E6 L)} (hEM : E ≤ monomialSubgroup .E6 L)
    (hE : IsElemAbelian 3 E) (hcard : 3 ^ 4 ≤ Nat.card E) {A : Subgroup (WeylGroup .E6)}
    (hEA : ∀ w, w ∈ A ↔ ∃ e, ∃ he : e ∈ E, weylQuotientHom .E6 L ⟨e, hEM he⟩ = w)
    (hAS : A ≤ modelHomE6.range) (hA1 : A ≠ ⊥) (hAg : ∀ i, A ≠ Subgroup.zpowers (gE6 i))
    {x : Fin Tag.E6.rank → ZMod 3} (hx : ∀ a ∈ A, adAct .E6 3 a x = x) :
    rootDiagUnit .E6 (zetaVec ζ hζ x) ∈ E := by
  have heq := expE_eq_fixSub hζo hζ hEM hE hcard hEA hAS hA1 hAg
  have hx' : x ∈ expE ζ hζ E := by
    rw [heq]
    exact hx
  exact (E6ThreeEnd.mem_expE).mp hx'

end CFSG.StandardType.E6NonToralThree
