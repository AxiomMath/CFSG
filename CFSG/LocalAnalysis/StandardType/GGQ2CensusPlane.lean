module

public import CFSG.LocalAnalysis.StandardType.GGQ2ClassicalCensusStatements
import CFSG.LocalAnalysis.StandardType.GGQ2PlaneChainProofs

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

private def cplSign {t : ℕ} (e : PlaneRaw.V t) (k : Fin t) : PlaneRaw.F :=
  if e k = -1 then -1 else 1

private lemma cpl_sq_eq_one (a : PlaneRaw.F) (ha : a ≠ 0) : a * a = 1 := by
  revert a
  decide

private lemma cpl_span_singleton_eq_of_mem {t : ℕ} {v w : PlaneRaw.V t} (hv : v ≠ 0)
    (hw : w ∈ Submodule.span PlaneRaw.F {v}) (hw0 : w ≠ 0) :
    Submodule.span PlaneRaw.F {v} = Submodule.span PlaneRaw.F {w} :=
  eq_span_singleton_of_mem_of_finrank_eq_one (by rw [finrank_span_singleton hv]) hw hw0

private lemma cpl_eq_one_or_neg_one (a : PlaneRaw.F) (ha : a ≠ 0) : a = 1 ∨ a = -1 := by
  revert a
  decide

private lemma cplSign_sq {t : ℕ} (e : PlaneRaw.V t) (k : Fin t) :
    cplSign e k * cplSign e k = 1 := by
  unfold cplSign
  split_ifs with h
  · ring
  · ring

private lemma cpl_orient_apply {t : ℕ} (e : PlaneRaw.V t) (v : PlaneRaw.V t) (k : Fin t) :
    PlaneRaw.orientEquiv t e v k = cplSign e k * v k := by
  simp only [PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply]
  unfold cplSign
  by_cases h : e k = -1
  · rw [if_pos h, if_pos h, LinearEquiv.neg_apply]; ring
  · rw [if_neg h, if_neg h, LinearEquiv.refl_apply]; ring

private lemma cpl_orient_mul_self {t : ℕ} (e : PlaneRaw.V t) :
    PlaneRaw.orientEquiv t e * PlaneRaw.orientEquiv t e = 1 := by
  ext w k
  simp only [LinearEquiv.mul_apply, PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply]
  split_ifs <;> simp

private lemma cpl_orient_inv {t : ℕ} (e : PlaneRaw.V t) :
    (PlaneRaw.orientEquiv t e)⁻¹ = PlaneRaw.orientEquiv t e :=
  inv_eq_of_mul_eq_one_right (cpl_orient_mul_self e)

private lemma cpl_swapEquiv_apply {t : ℕ} (i j : Fin t) (v : PlaneRaw.V t) (k : Fin t) :
    PlaneRaw.swapEquiv t i j v k = if k = i then v j else if k = j then v i else v k := by
  rw [PlaneRaw.swapEquiv, LinearEquiv.funCongrLeft_apply, LinearMap.funLeft_apply]
  by_cases hki : k = i
  · subst hki
    rw [if_pos rfl, Equiv.swap_apply_left]
  · rw [if_neg hki]
    by_cases hkj : k = j
    · subst hkj
      rw [if_pos rfl, Equiv.swap_apply_right]
    · rw [if_neg hkj, Equiv.swap_apply_def, if_neg hki, if_neg hkj]

private lemma cpl_swapTwist_apply {t : ℕ} (e : PlaneRaw.V t) {i j : Fin t} (hij : i ≠ j)
    (v : PlaneRaw.V t) (k : Fin t) :
    PlaneRaw.swapTwist t e i j v k =
      if k = i then cplSign e i * cplSign e j * v j
      else if k = j then cplSign e i * cplSign e j * v i
      else v k := by
  rw [PlaneRaw.swapTwist, cpl_orient_inv]
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  simp only [cpl_orient_apply, cpl_swapEquiv_apply]
  by_cases hki : k = i
  · subst hki
    simp only [if_true]
    ring
  · by_cases hkj : k = j
    · subst hkj
      simp only [if_neg hki, if_true]
      ring
    · simp only [if_neg hki, if_neg hkj]
      rw [← mul_assoc, cplSign_sq, one_mul]

private lemma cplSign_eq_one {t : ℕ} {e : PlaneRaw.V t} {k : Fin t} (h : e k = 1) :
    cplSign e k = 1 := by
  unfold cplSign
  rw [h, if_neg (by decide : (1 : PlaneRaw.F) ≠ -1)]

private lemma cplSign_eq_neg_one {t : ℕ} {e : PlaneRaw.V t} {k : Fin t} (h : e k = -1) :
    cplSign e k = -1 := by
  unfold cplSign
  rw [h, if_pos rfl]

private lemma cplSign_mul_eq {t : ℕ} {e : PlaneRaw.V t} {i j : Fin t} (hi : e i ≠ 0)
    (hj : e j ≠ 0) : cplSign e i * cplSign e j = e i * e j := by
  rcases cpl_eq_one_or_neg_one (e i) hi with h | h <;>
    rcases cpl_eq_one_or_neg_one (e j) hj with h' | h'
  · rw [cplSign_eq_one h, cplSign_eq_one h', h, h']
  · rw [cplSign_eq_one h, cplSign_eq_neg_one h', h, h']
  · rw [cplSign_eq_neg_one h, cplSign_eq_one h', h, h']
  · rw [cplSign_eq_neg_one h, cplSign_eq_neg_one h', h, h']

private lemma cpl_negEquiv_apply {t : ℕ} (i : Fin t) (v : PlaneRaw.V t) (k : Fin t) :
    PlaneRaw.negEquiv t i v k = if k = i then -v k else v k := by
  simp only [PlaneRaw.negEquiv, LinearEquiv.piCongrRight_apply]
  by_cases hki : k = i
  · subst hki
    simp [LinearEquiv.neg_apply]
  · simp [hki, LinearEquiv.refl_apply]

private lemma cpl_swap_mul_neg_apply {t : ℕ} (i j : Fin t) (hij : i ≠ j) (v : PlaneRaw.V t)
    (k : Fin t) :
    (PlaneRaw.swapEquiv t i j * PlaneRaw.negEquiv t i * PlaneRaw.negEquiv t j) v k =
      if k = i then -v j else if k = j then -v i else v k := by
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, cpl_swapEquiv_apply]
  simp only [cpl_negEquiv_apply]
  by_cases hki : k = i
  · subst hki
    simp [Ne.symm hij]
  · by_cases hkj : k = j
    · subst hkj
      simp [hki, hij]
    · simp [hki, hkj]

private lemma cpl_swapTwist_eq_swap {t : ℕ} {e : PlaneRaw.V t} {i j : Fin t} (hij : i ≠ j)
    (hi : e i ≠ 0) (hj : e j ≠ 0) (h : e i * e j = 1) :
    PlaneRaw.swapTwist t e i j = PlaneRaw.swapEquiv t i j := by
  ext w k
  rw [cpl_swapTwist_apply e hij w k, cpl_swapEquiv_apply]
  have hsign : cplSign e i * cplSign e j = 1 := by rw [cplSign_mul_eq hi hj, h]
  simp only [hsign, one_mul]

private lemma cpl_swapTwist_eq_swap_mul_neg {t : ℕ} {e : PlaneRaw.V t} {i j : Fin t}
    (hij : i ≠ j) (hi : e i ≠ 0) (hj : e j ≠ 0) (h : e i * e j = -1) :
    PlaneRaw.swapTwist t e i j =
      PlaneRaw.swapEquiv t i j * PlaneRaw.negEquiv t i * PlaneRaw.negEquiv t j := by
  ext w k
  rw [cpl_swapTwist_apply e hij w k, cpl_swap_mul_neg_apply i j hij w k]
  have hsign : cplSign e i * cplSign e j = -1 := by rw [cplSign_mul_eq hi hj, h]
  simp only [hsign, neg_mul, one_mul]

private lemma cpl_zero_cent {t : ℕ} {k : PlaneRaw.PlaneKind} {S : Finset (Fin t)}
    {z : PlaneRaw.V t} (hz : z ≠ 0)
    (h : PlaneRaw.cent k (PlaneRaw.Code.zero S) = Submodule.span PlaneRaw.F {z}) :
    ∃ i₁ : Fin t, S = Finset.univ.erase i₁ ∧
      Submodule.span PlaneRaw.F {z} =
        Submodule.span PlaneRaw.F {Pi.single i₁ (1 : PlaneRaw.F)} := by
  have hdelta : ∀ i, i ∉ S → Pi.single i (1 : PlaneRaw.F) ∈ Submodule.span PlaneRaw.F {z} := by
    intro i hi
    rw [← h, PlaneRaw.mem_cent_zero]
    intro j hj
    exact Pi.single_eq_of_ne (fun hji : j = i => hi (hji ▸ hj)) 1
  have hex : ∃ i, i ∉ S := by
    by_contra hall
    have hall' : ∀ i, i ∈ S := by
      intro i
      by_contra hmem
      exact hall ⟨i, hmem⟩
    have hSup : S = Finset.univ := Finset.eq_univ_of_forall hall'
    have hzmem : z ∈ PlaneRaw.cent k (PlaneRaw.Code.zero S) := by
      rw [h]
      exact Submodule.mem_span_singleton_self z
    have hzero : ∀ i ∈ S, z i = 0 := (PlaneRaw.mem_cent_zero k S z).mp hzmem
    refine hz (funext fun i => ?_)
    exact hzero i (by simp [hSup])
  obtain ⟨i₁, hi₁⟩ := hex
  have huniq : ∀ i, i ∉ S → i = i₁ := by
    intro i hi
    by_contra hne
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp (hdelta i hi)
    obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp (hdelta i₁ hi₁)
    have hai : a * z i = 1 := by
      have hh := congrFun ha i
      simpa [Pi.single_eq_same] using hh
    have ha1 : a * z i₁ = 0 := by
      have hh := congrFun ha i₁
      rw [Pi.single_eq_of_ne (Ne.symm hne) 1] at hh
      simpa using hh
    have hb1 : b * z i₁ = 1 := by
      have hh := congrFun hb i₁
      simpa [Pi.single_eq_same] using hh
    have hz1 : z i₁ ≠ 0 := by
      intro h0
      rw [h0, mul_zero] at hb1
      exact zero_ne_one hb1
    rcases mul_eq_zero.mp ha1 with h0 | h0
    · rw [h0, zero_mul] at hai
      exact zero_ne_one hai
    · exact hz1 h0
  refine ⟨i₁, ?_, ?_⟩
  · ext i
    rw [Finset.mem_erase]
    simp only [Finset.mem_univ, and_true]
    constructor
    · intro hi
      exact fun h => hi₁ (h ▸ hi)
    · intro hi
      by_contra hmem
      exact hi (huniq i hmem)
  · apply eq_span_singleton_of_mem_of_finrank_eq_one
      (by rw [finrank_span_singleton hz]) (hdelta i₁ hi₁)
    intro hzero
    have := congrFun hzero i₁
    simp at this

private lemma cpl_ext_shape {t : ℕ} {k : PlaneRaw.PlaneKind} {e v : PlaneRaw.V t}
    (hv : v ≠ 0) (he : e ≠ 0)
    (hcent : PlaneRaw.cent k (PlaneRaw.Code.extension e) = Submodule.span PlaneRaw.F {v}) :
    (∀ i, e i ≠ 0) ∧ Submodule.span PlaneRaw.F {v} = Submodule.span PlaneRaw.F {e} := by
  have hcard : (PlaneRaw.Code.extSupport e).card = t := by
    have hfr := PlaneRaw.finrank_cent_extension k e he
    rw [hcent, finrank_span_singleton hv] at hfr
    have hle : (PlaneRaw.Code.extSupport e).card ≤ t := by
      simpa using Finset.card_le_univ (PlaneRaw.Code.extSupport e)
    omega
  have hsupp : PlaneRaw.Code.extSupport e = Finset.univ :=
    Finset.eq_univ_of_card _ (by simpa using hcard)
  have hei : ∀ i, e i ≠ 0 := by
    intro i
    have hi : i ∈ PlaneRaw.Code.extSupport e := by rw [hsupp]; exact Finset.mem_univ i
    simpa using hi
  have he_cent : e ∈ PlaneRaw.cent k (PlaneRaw.Code.extension e) := by
    rw [PlaneRaw.mem_cent_extension]
    intro i _ j _
    rw [cpl_sq_eq_one (e i) (hei i), cpl_sq_eq_one (e j) (hei j)]
  have he_mem : e ∈ Submodule.span PlaneRaw.F {v} := by rw [← hcent]; exact he_cent
  exact ⟨hei, cpl_span_singleton_eq_of_mem hv he_mem he⟩

private lemma cpl_ext_cent_shape {t : ℕ} {k : PlaneRaw.PlaneKind} {e' : PlaneRaw.V t}
    {U : Submodule PlaneRaw.F (PlaneRaw.V t)} (ht : 4 ≤ t)
    (hU : finrank PlaneRaw.F U = 2)
    (hcentj : PlaneRaw.cent k (PlaneRaw.Code.extension e') = U) (he' : e' ≠ 0) :
    ∃ i₀ : Fin t, PlaneRaw.Code.extSupport e' = Finset.univ.erase i₀ := by
  have hcard : (PlaneRaw.Code.extSupport e').card = t - 1 := by
    have hfr := PlaneRaw.finrank_cent_extension k e' he'
    rw [hcentj, hU] at hfr
    have hle : (PlaneRaw.Code.extSupport e').card ≤ t := by
      simpa using Finset.card_le_univ (PlaneRaw.Code.extSupport e')
    omega
  have hcompl : (PlaneRaw.Code.extSupport e')ᶜ.card = 1 := by
    rw [Finset.card_compl, Fintype.card_fin, hcard]
    omega
  obtain ⟨i₀, hi₀⟩ := Finset.card_eq_one.mp hcompl
  refine ⟨i₀, ?_⟩
  have hi₀T : i₀ ∉ PlaneRaw.Code.extSupport e' := by
    have h : i₀ ∈ (PlaneRaw.Code.extSupport e')ᶜ := by rw [hi₀]; simp
    simpa using h
  ext i
  rw [Finset.mem_erase]
  constructor
  · intro hi
    exact ⟨fun h => hi₀T (h ▸ hi), Finset.mem_univ i⟩
  · rintro ⟨hne, -⟩
    by_contra hmem
    have h : i ∈ (PlaneRaw.Code.extSupport e')ᶜ := by simpa using hmem
    rw [hi₀] at h
    exact hne (by simpa using h)

private lemma cpl_zero_normalizer_linear {t : ℕ} (ε : Fin 2) (i : Fin t) :
    PlaneRaw.normalizerOf (.linear ε) t (.zero (Finset.univ.erase i)) =
      PlaneRaw.signedPermGroupOn t (Finset.univ.erase i) := rfl

private lemma cpl_zero_normalizer_symp {t : ℕ} (ht : 4 ≤ t) (i : Fin t) :
    PlaneRaw.normalizerOf .symplectic t (.zero (Finset.univ.erase i)) =
      PlaneRaw.signedPermGroupOn t (Finset.univ.erase i) := by
  have hcard : (Finset.univ.erase i : Finset (Fin t)).card = t - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  simp only [PlaneRaw.normalizerOf]
  rw [if_neg]
  omega

private lemma cpl_zero_normalizer_orth {t : ℕ} (δ : Fin 2) (i : Fin t) :
    PlaneRaw.normalizerOf (.orthogonal δ) t (.zero (Finset.univ.erase i)) =
      if δ.val = 0 then PlaneRaw.evenSignedPermGroupOn t (Finset.univ.erase i)
      else PlaneRaw.signedPermGroupOn t (Finset.univ.erase i) := rfl

private lemma cpl_admissible_zero_erase {t : ℕ} {k : PlaneRaw.PlaneKind} (ht : 4 ≤ t)
    (i : Fin t) : PlaneRaw.admissible k (.zero (Finset.univ.erase i)) := by
  have hcard : (Finset.univ.erase i : Finset (Fin t)).card = t - 1 := by
    rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
  cases k with
  | linear ε =>
      simp only [PlaneRaw.admissible, hcard]
      have hε : ε.val < 2 := ε.isLt
      omega
  | symplectic =>
      simp only [PlaneRaw.admissible, hcard]
      omega
  | orthogonal δ =>
      simp only [PlaneRaw.admissible, hcard]
      have hδ : δ.val < 2 := δ.isLt
      rcases Nat.even_or_odd (t - 1) with h | h
      · left
        refine ⟨h, ?_⟩
        rw [even_iff_exists_two_mul] at h
        obtain ⟨m, hm⟩ := h
        omega
      · right
        refine ⟨h, ?_⟩
        omega

private lemma cpl_admissible_extension_full {t : ℕ} {k : PlaneRaw.PlaneKind} (ht : 4 ≤ t)
    {e : PlaneRaw.V t} (he : e ≠ 0) (hcard : (PlaneRaw.Code.extSupport e).card = t) :
    PlaneRaw.admissible k (.extension e) := by
  cases k with
  | linear ε =>
      exact ⟨he, by rw [hcard]; omega⟩
  | symplectic =>
      exact ⟨he, by rw [hcard]; omega⟩
  | orthogonal δ =>
      exact ⟨he, by rw [hcard]; omega⟩

private lemma cpl_cent_zero_erase {t : ℕ} (k : PlaneRaw.PlaneKind) (i : Fin t) :
    PlaneRaw.cent k (.zero (Finset.univ.erase i)) =
      Submodule.span PlaneRaw.F {Pi.single i (1 : PlaneRaw.F)} := by
  ext v
  rw [PlaneRaw.mem_cent_zero, Submodule.mem_span_singleton]
  constructor
  · intro hv
    refine ⟨v i, ?_⟩
    funext j
    by_cases hji : j = i
    · subst hji
      simp [Pi.smul_apply]
    · have hvj : v j = 0 :=
        hv j (by rw [Finset.mem_erase]; exact ⟨hji, Finset.mem_univ j⟩)
      simp [Pi.smul_apply, Pi.single_eq_of_ne hji, hvj]
  · rintro ⟨c, hc⟩ j hj
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    rw [← hc]
    simp [Pi.smul_apply, Pi.single_eq_of_ne hji]

private lemma cpl_cent_ext_self {t : ℕ} {k : PlaneRaw.PlaneKind} {z : PlaneRaw.V t}
    (i : Fin t) (hz : ∀ j, z j ≠ 0) :
    PlaneRaw.cent k (.extension z) = Submodule.span PlaneRaw.F {z} := by
  have hz0 : z ≠ 0 := by
    intro h0
    exact hz i (by rw [h0]; rfl)
  have hzc : z ∈ PlaneRaw.cent k (.extension z) := by
    rw [PlaneRaw.mem_cent_extension]
    intro a _ b _
    rw [cpl_sq_eq_one (z a) (hz a), cpl_sq_eq_one (z b) (hz b)]
  have hcard : (PlaneRaw.Code.extSupport z).card = t := by
    have hsupp : PlaneRaw.Code.extSupport z = Finset.univ :=
      Finset.eq_univ_of_forall (fun j => by simpa using hz j)
    rw [hsupp, Finset.card_univ, Fintype.card_fin]
  apply eq_span_singleton_of_mem_of_finrank_eq_one ?_ hzc hz0
  rw [PlaneRaw.finrank_cent_extension k z hz0, hcard]
  omega

private lemma cpl_occurs_zero_erase {t : ℕ} (i : Fin t) :
    PlaneRaw.occurs (Submodule.span PlaneRaw.F {Pi.single i (1 : PlaneRaw.F)})
      (.zero (Finset.univ.erase i)) := by
  intro j
  constructor
  · intro hj u
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp u.2
    have hji : j ≠ i := (Finset.mem_erase.mp hj).1
    have h1 : (u : PlaneRaw.V t) j =
        c * (Pi.single i (1 : PlaneRaw.F) : PlaneRaw.V t) j := by
      rw [hc.symm]; simp [Pi.smul_apply]
    rw [h1, Pi.single_eq_of_ne hji, mul_zero]
  · intro h
    rw [Finset.mem_erase]
    refine ⟨?_, Finset.mem_univ j⟩
    intro hji
    have hu : (Pi.single i (1 : PlaneRaw.F) : PlaneRaw.V t) ∈
        Submodule.span PlaneRaw.F {Pi.single i (1 : PlaneRaw.F)} :=
      Submodule.mem_span_singleton_self _
    have h0 : (Pi.single i (1 : PlaneRaw.F) : PlaneRaw.V t) j = 0 :=
      h ⟨Pi.single i (1 : PlaneRaw.F), hu⟩
    rw [hji, Pi.single_eq_same] at h0
    exact one_ne_zero h0

private lemma cpl_occurs_extension_self {t : ℕ} {z : PlaneRaw.V t} (i : Fin t)
    (hz : ∀ j, z j ≠ 0) :
    PlaneRaw.occurs (Submodule.span PlaneRaw.F {z}) (.extension z) := by
  have hz0 : z ≠ 0 := by
    intro h0
    exact hz i (by rw [h0]; rfl)
  refine ⟨hz0, (z i)⁻¹ • PlaneRaw.evalRestr (Submodule.span PlaneRaw.F {z}) i, ?_, ?_, ?_⟩
  · intro hzero
    have h1 : ((z i)⁻¹ • PlaneRaw.evalRestr (Submodule.span PlaneRaw.F {z}) i)
        ⟨z, Submodule.mem_span_singleton_self z⟩ = 0 := by rw [hzero]; rfl
    simp only [LinearMap.smul_apply, PlaneRaw.evalRestr, LinearMap.comp_apply,
      Submodule.coe_subtype, PlaneRaw.coordProj_apply, smul_eq_mul] at h1
    rw [inv_mul_cancel₀ (hz i)] at h1
    exact one_ne_zero h1
  · intro k _
    ext u
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp u.2
    have huk : (u : PlaneRaw.V t) k = c * z k := by
      rw [hc.symm]; simp [Pi.smul_apply]
    have hui : (u : PlaneRaw.V t) i = c * z i := by
      rw [hc.symm]; simp [Pi.smul_apply]
    simp only [LinearMap.smul_apply, PlaneRaw.evalRestr, LinearMap.comp_apply,
      Submodule.coe_subtype, PlaneRaw.coordProj_apply, smul_eq_mul]
    rw [huk, hui]
    rw [show (z i)⁻¹ * (c * z i) = c from by
      calc (z i)⁻¹ * (c * z i) = c * ((z i)⁻¹ * z i) := by ring
        _ = c := by rw [inv_mul_cancel₀ (hz i), mul_one]]
    ring
  · intro j hj
    exact absurd hj (hz j)

private lemma cpl_swap_mem_signed {t : ℕ} {S : Finset (Fin t)} {i j : Fin t} (hi : i ∈ S)
    (hj : j ∈ S) : PlaneRaw.swapEquiv t i j ∈ PlaneRaw.signedPermGroupOn t S :=
  Subgroup.subset_closure (Or.inl ⟨i, hi, j, hj, rfl⟩)

private lemma cpl_neg_mem_signed {t : ℕ} {S : Finset (Fin t)} {i : Fin t} (hi : i ∈ S) :
    PlaneRaw.negEquiv t i ∈ PlaneRaw.signedPermGroupOn t S :=
  Subgroup.subset_closure (Or.inr ⟨i, hi, rfl⟩)

private lemma cpl_swap_mem_evenSigned {t : ℕ} {S : Finset (Fin t)} {i j : Fin t} (hi : i ∈ S)
    (hj : j ∈ S) : PlaneRaw.swapEquiv t i j ∈ PlaneRaw.evenSignedPermGroupOn t S :=
  Subgroup.subset_closure (Or.inl ⟨i, hi, j, hj, rfl⟩)

private lemma cpl_doubleNeg_mem_evenSigned {t : ℕ} {S : Finset (Fin t)} {i j : Fin t}
    (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j) :
    PlaneRaw.negEquiv t i * PlaneRaw.negEquiv t j ∈ PlaneRaw.evenSignedPermGroupOn t S :=
  Subgroup.subset_closure (Or.inr ⟨i, hi, j, hj, hij, rfl⟩)

private lemma cpl_swapTwist_self {t : ℕ} (e : PlaneRaw.V t) (i : Fin t) :
    PlaneRaw.swapTwist t e i i = 1 := by
  rw [PlaneRaw.swapTwist]
  have h : PlaneRaw.swapEquiv t i i = 1 := by
    rw [PlaneRaw.swapEquiv, Equiv.swap_self]
    rfl
  rw [h, mul_one]
  simp

private lemma cpl_twisted_le_signed {t : ℕ} {e' : PlaneRaw.V t} {i₀ : Fin t}
    (hsupp : PlaneRaw.Code.extSupport e' = Finset.univ.erase i₀) :
    PlaneRaw.twistedPermGroupOn t e' ≤
      PlaneRaw.signedPermGroupOn t (Finset.univ.erase i₀) := by
  rw [PlaneRaw.twistedPermGroupOn, Subgroup.closure_le]
  rintro T ⟨i, j, hi, hj, rfl⟩
  have hiT : i ∈ Finset.univ.erase i₀ := by rw [← hsupp]; simpa using hi
  have hjT : j ∈ Finset.univ.erase i₀ := by rw [← hsupp]; simpa using hj
  by_cases hij : i = j
  · subst hij
    rw [cpl_swapTwist_self]
    exact Subgroup.one_mem _
  · rcases cpl_eq_one_or_neg_one (e' i * e' j) (mul_ne_zero hi hj) with h | h
    · rw [cpl_swapTwist_eq_swap hij hi hj h]
      exact cpl_swap_mem_signed hiT hjT
    · rw [cpl_swapTwist_eq_swap_mul_neg hij hi hj h]
      exact Subgroup.mul_mem _
        (Subgroup.mul_mem _ (cpl_swap_mem_signed hiT hjT) (cpl_neg_mem_signed hiT))
        (cpl_neg_mem_signed hjT)

private lemma cpl_twisted_le_evenSigned {t : ℕ} {e' : PlaneRaw.V t} {i₀ : Fin t}
    (hsupp : PlaneRaw.Code.extSupport e' = Finset.univ.erase i₀) :
    PlaneRaw.twistedPermGroupOn t e' ≤
      PlaneRaw.evenSignedPermGroupOn t (Finset.univ.erase i₀) := by
  rw [PlaneRaw.twistedPermGroupOn, Subgroup.closure_le]
  rintro T ⟨i, j, hi, hj, rfl⟩
  have hiT : i ∈ Finset.univ.erase i₀ := by rw [← hsupp]; simpa using hi
  have hjT : j ∈ Finset.univ.erase i₀ := by rw [← hsupp]; simpa using hj
  by_cases hij : i = j
  · subst hij
    rw [cpl_swapTwist_self]
    exact Subgroup.one_mem _
  · rcases cpl_eq_one_or_neg_one (e' i * e' j) (mul_ne_zero hi hj) with h | h
    · rw [cpl_swapTwist_eq_swap hij hi hj h]
      exact cpl_swap_mem_evenSigned hiT hjT
    · rw [cpl_swapTwist_eq_swap_mul_neg hij hi hj h]
      rw [mul_assoc]
      exact Subgroup.mul_mem _ (cpl_swap_mem_evenSigned hiT hjT)
        (cpl_doubleNeg_mem_evenSigned hiT hjT hij)

private theorem cpl_twisted_le_zero_normalizer (k : PlaneRaw.PlaneKind) (t : ℕ) (ht : 4 ≤ t)
    {e' : PlaneRaw.V t} {i₀ : Fin t}
    (hsupp : PlaneRaw.Code.extSupport e' = Finset.univ.erase i₀) :
    PlaneRaw.twistedPermGroupOn t e' ≤
      PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₀)) := by
  cases k with
  | linear ε =>
      rw [cpl_zero_normalizer_linear]
      exact cpl_twisted_le_signed hsupp
  | symplectic =>
      rw [cpl_zero_normalizer_symp ht]
      exact cpl_twisted_le_signed hsupp
  | orthogonal δ =>
      rw [cpl_zero_normalizer_orth]
      by_cases hδ : δ.val = 0
      · rw [if_pos hδ]
        exact cpl_twisted_le_evenSigned hsupp
      · rw [if_neg hδ]
        exact cpl_twisted_le_signed hsupp

private theorem cpl_chainWitness_zero_left (k : PlaneRaw.PlaneKind) (t : ℕ) (ht : 4 ≤ t)
    {z : PlaneRaw.V t} (hz : ∀ i, z i ≠ 0) (i₁ : Fin t) :
    PlaneRaw.ChainWitnessOn t (PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₁)))
      (PlaneRaw.twistedPermGroupOn t z) (Pi.single i₁ 1) z := by
  cases k with
  | linear ε =>
      rw [cpl_zero_normalizer_linear]
      exact (PlaneRaw.leafModelSigned_holds _ ht _ hz i₁).swap.chainWitnessOn
  | symplectic =>
      rw [cpl_zero_normalizer_symp ht]
      exact (PlaneRaw.leafModelSigned_holds _ ht _ hz i₁).swap.chainWitnessOn
  | orthogonal δ =>
      rw [cpl_zero_normalizer_orth]
      by_cases hδ : δ.val = 0
      · rw [if_pos hδ]
        exact (PlaneRaw.leafModelEvenSigned_holds _ ht _ hz i₁).swap.chainWitnessOn
      · rw [if_neg hδ]
        exact (PlaneRaw.leafModelSigned_holds _ ht _ hz i₁).swap.chainWitnessOn

private theorem cpl_chainWitness_zero_right (k : PlaneRaw.PlaneKind) (t : ℕ) (ht : 4 ≤ t)
    {e : PlaneRaw.V t} (he : ∀ i, e i ≠ 0) (i₀ : Fin t) :
    PlaneRaw.ChainWitnessOn t (PlaneRaw.twistedPermGroupOn t e)
      (PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₀))) e (Pi.single i₀ 1) := by
  cases k with
  | linear ε =>
      rw [cpl_zero_normalizer_linear]
      exact (PlaneRaw.leafModelSigned_holds _ ht _ he i₀).chainWitnessOn
  | symplectic =>
      rw [cpl_zero_normalizer_symp ht]
      exact (PlaneRaw.leafModelSigned_holds _ ht _ he i₀).chainWitnessOn
  | orthogonal δ =>
      rw [cpl_zero_normalizer_orth]
      by_cases hδ : δ.val = 0
      · rw [if_pos hδ]
        exact (PlaneRaw.leafModelEvenSigned_holds _ ht _ he i₀).chainWitnessOn
      · rw [if_neg hδ]
        exact (PlaneRaw.leafModelSigned_holds _ ht _ he i₀).chainWitnessOn

private theorem cpl_ambient_zero (k : PlaneRaw.PlaneKind) (t : ℕ) (ht : 4 ≤ t)
    {i₁ i₂ : Fin t} (h : i₁ ≠ i₂) :
    PlaneRaw.AmbientChainOn t (PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₁)))
      (PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₁)) ⊔
        PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₂)))
      (Pi.single i₁ 1) (Pi.single i₂ 1) := by
  cases k with
  | linear ε =>
      have h1 := cpl_zero_normalizer_linear (t := t) ε i₁
      have h2 := cpl_zero_normalizer_linear (t := t) ε i₂
      rw [h1, h2]
      exact PlaneRaw.ambientChainOn_signed ht h
  | symplectic =>
      have h1 := cpl_zero_normalizer_symp (t := t) ht i₁
      have h2 := cpl_zero_normalizer_symp (t := t) ht i₂
      rw [h1, h2]
      exact PlaneRaw.ambientChainOn_signed ht h
  | orthogonal δ =>
      have h1 := cpl_zero_normalizer_orth (t := t) δ i₁
      have h2 := cpl_zero_normalizer_orth (t := t) δ i₂
      by_cases hδ : δ.val = 0
      · rw [h1, h2]
        simp only [if_pos hδ]
        exact PlaneRaw.ambientChainOn_evenSigned ht h
      · rw [h1, h2]
        simp only [if_neg hδ]
        exact PlaneRaw.ambientChainOn_signed ht h

private lemma cpl_orient_add_single {t : ℕ} {e : PlaneRaw.V t} {i₁ : Fin t} (hi : e i₁ = 0) :
    PlaneRaw.orientEquiv t (e + Pi.single i₁ (1 : PlaneRaw.F)) = PlaneRaw.orientEquiv t e := by
  apply LinearEquiv.ext
  intro v
  funext k
  simp only [PlaneRaw.orientEquiv, LinearEquiv.piCongrRight_apply]
  by_cases hk : k = i₁
  · subst hk
    rw [Pi.add_apply, Pi.single_eq_same, hi, zero_add, if_neg (by decide : (1 : PlaneRaw.F) ≠ -1),
      if_neg (by decide : (0 : PlaneRaw.F) ≠ -1)]
  · rw [Pi.add_apply, Pi.single_eq_of_ne hk, add_zero]

private lemma cpl_twisted_le_twisted_add_single {t : ℕ} {e : PlaneRaw.V t} {i₁ : Fin t}
    (hi : e i₁ = 0)
    (hfull : ∀ k, (e + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) k ≠ 0) :
    PlaneRaw.twistedPermGroupOn t e ≤
      PlaneRaw.twistedPermGroupOn t (e + Pi.single i₁ (1 : PlaneRaw.F)) := by
  have horient := cpl_orient_add_single (e := e) hi
  rw [PlaneRaw.twistedPermGroupOn, Subgroup.closure_le]
  rintro T ⟨i, j, hi', hj', rfl⟩
  have hTw : PlaneRaw.swapTwist t e i j =
      PlaneRaw.swapTwist t (e + Pi.single i₁ (1 : PlaneRaw.F)) i j := by
    rw [PlaneRaw.swapTwist, PlaneRaw.swapTwist, horient]
  rw [hTw]
  exact Subgroup.subset_closure ⟨i, j, hfull i, hfull j, rfl⟩

private theorem cpl_chainWitnessOn_congr {t : ℕ}
    {Na Nb : Subgroup (PlaneRaw.V t ≃ₗ[PlaneRaw.F] PlaneRaw.V t)} {vx vx' z z' : PlaneRaw.V t}
    (hv : Submodule.span PlaneRaw.F {vx} = Submodule.span PlaneRaw.F {vx'})
    (hz : Submodule.span PlaneRaw.F {z} = Submodule.span PlaneRaw.F {z'}) :
    PlaneRaw.ChainWitnessOn t Na Nb vx z ↔ PlaneRaw.ChainWitnessOn t Na Nb vx' z' := by
  simp only [PlaneRaw.ChainWitnessOn, hv, hz]

private theorem cpl_ambientChainOn_span {t : ℕ}
    {Na Nab : Subgroup (PlaneRaw.V t ≃ₗ[PlaneRaw.F] PlaneRaw.V t)} {vx vx' z : PlaneRaw.V t}
    (hv : Submodule.span PlaneRaw.F {vx} = Submodule.span PlaneRaw.F {vx'}) :
    PlaneRaw.AmbientChainOn t Na Nab vx z → PlaneRaw.AmbientChainOn t Na Nab vx' z := by
  rintro ⟨W, h1, h2, h3, h4, h5, h6, h7⟩
  exact ⟨W, h1, h2, by rw [← hv]; exact h3, h4, h5, h6, h7⟩

private theorem cpl_ambientChainOn_smul_z {t : ℕ}
    {Na Nab : Subgroup (PlaneRaw.V t ≃ₗ[PlaneRaw.F] PlaneRaw.V t)} {vx z : PlaneRaw.V t}
    {c : PlaneRaw.F} (_hc : c ≠ 0) :
    PlaneRaw.AmbientChainOn t Na Nab vx z →
      PlaneRaw.AmbientChainOn t Na Nab vx (c • z) := by
  rintro ⟨W, h1, h2, h3, h4, h5, h6, h7⟩
  refine ⟨W, h1, h2, h3, ?_, h5, h6, h7⟩
  intro i hi hj
  rw [LinearMap.map_smul, h4 i hi hj]
  simp
private theorem cpl_censusCases_planeEntry_raw {k : PlaneRaw.PlaneKind} {t : ℕ}
    (h4t : 4 ≤ t) :
    ∀ vx : PlaneRaw.V t, vx ≠ 0 →
    ∀ ℓ : PlaneRaw.Code t, PlaneRaw.admissible k ℓ →
      PlaneRaw.cent k ℓ = Submodule.span PlaneRaw.F {vx} →
    ∀ U : Submodule PlaneRaw.F (PlaneRaw.V t), finrank PlaneRaw.F U = 2 → vx ∈ U →
    ∀ j : PlaneRaw.Code t, PlaneRaw.admissible k j → PlaneRaw.cent k j = U →
      (∃ z ∈ U, z ∉ Submodule.span PlaneRaw.F {vx} ∧ ∃ c : PlaneRaw.Code t,
        (4 ≤ t ∧ PlaneRaw.admissible k c) ∧
          PlaneRaw.occurs (Submodule.span PlaneRaw.F {z}) c ∧
          PlaneRaw.cent k c = Submodule.span PlaneRaw.F {z} ∧
          PlaneRaw.normalizerOf k t j ≤ PlaneRaw.normalizerOf k t c ∧
          vx ∉ PlaneRaw.cent k c ∧
          PlaneRaw.ChainWitnessOn t (PlaneRaw.normalizerOf k t ℓ)
            (PlaneRaw.normalizerOf k t c) vx z) ∨
      (∀ z ∈ U, z ∉ Submodule.span PlaneRaw.F {vx} → ∀ c : PlaneRaw.Code t,
        (4 ≤ t ∧ PlaneRaw.admissible k c) →
        PlaneRaw.occurs (Submodule.span PlaneRaw.F {z}) c →
        PlaneRaw.cent k c = Submodule.span PlaneRaw.F {z} →
        PlaneRaw.normalizerOf k t j ≤ PlaneRaw.normalizerOf k t c →
        vx ∉ PlaneRaw.cent k c →
        PlaneRaw.AmbientChainOn t (PlaneRaw.normalizerOf k t ℓ)
          (PlaneRaw.normalizerOf k t ℓ ⊔ PlaneRaw.normalizerOf k t c) vx z) := by
  intro vx hvx ℓ hℓadm hcent U hU hvxU j hjadm hcentj
  cases ℓ with
  | zero S =>
      obtain ⟨i₁, hS, hspan_vx⟩ := cpl_zero_cent hvx hcent
      rw [hS]
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
        (by rw [← hspan_vx]; exact Submodule.mem_span_singleton_self vx)
      have ha0 : a ≠ 0 := by
        intro h0
        apply hvx
        rw [← ha, h0, zero_smul]
      cases j with
      | zero S' =>
          refine Or.inr ?_
          have hS'ne : S' ≠ ∅ := by
            intro h0
            have hUtop : U = ⊤ := by
              rw [← hcentj, h0]
              rw [Submodule.eq_top_iff']
              intro v
              rw [PlaneRaw.mem_cent_zero]
              intro i hi
              exact absurd hi (by simp)
            have hdt : finrank PlaneRaw.F U = t := by
              rw [hUtop, finrank_top]
              simp
            rw [hdt] at hU
            omega
          intro z hzU hzx c hcadm hcocc hccent hcN hcnin
          cases c with
          | zero S'' =>
              have hz0 : z ≠ 0 := by
                intro h0
                exact hzx (by rw [h0]; exact Submodule.zero_mem _)
              obtain ⟨i₂, hS'', hspan_z⟩ := cpl_zero_cent hz0 hccent
              have hi₂ : i₂ ≠ i₁ := by
                intro h
                have hδ : Submodule.span PlaneRaw.F
                    {(Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)} =
                    Submodule.span PlaneRaw.F
                    {(Pi.single i₂ (1 : PlaneRaw.F) : PlaneRaw.V t)} := by
                  rw [h]
                apply hzx
                rw [hspan_vx, hδ, ← hspan_z]
                exact Submodule.mem_span_singleton_self z
              obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.mp
                (by rw [← hspan_z]; exact Submodule.mem_span_singleton_self z)
              have hb0 : b ≠ 0 := by
                intro h0
                apply hz0
                rw [← hb, h0, zero_smul]
              rw [hS'']
              refine cpl_ambientChainOn_span hspan_vx.symm ?_
              rw [← hb]
              exact cpl_ambientChainOn_smul_z hb0 (cpl_ambient_zero k t h4t (Ne.symm hi₂))
          | extension e'' =>
              have hz0 : z ≠ 0 := by
                intro h0
                exact hzx (by rw [h0]; exact Submodule.zero_mem _)
              obtain ⟨hzfull, hspan_ze⟩ := cpl_ext_shape hz0 hcadm.2.1 hccent
              obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS'ne
              have hzU' : z ∈ PlaneRaw.cent k (.zero S') := by rw [hcentj]; exact hzU
              have hzi : z i = 0 := (PlaneRaw.mem_cent_zero k S' z).mp hzU' i hi
              have he''mem : e'' ∈ Submodule.span PlaneRaw.F {z} := by
                rw [hspan_ze]
                exact Submodule.mem_span_singleton_self e''
              obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp he''mem
              have he''i : e'' i = 0 := by
                rw [← hcc]
                simp [Pi.smul_apply, smul_eq_mul, hzi]
              exfalso
              exact (hzfull i) he''i
      | extension e' =>
          have he' : e' ≠ 0 := hjadm.1
          obtain ⟨i₀, hsupp'⟩ := cpl_ext_cent_shape h4t hU hcentj he'
          have hi₁supp_of : ∀ hne : i₀ ≠ i₁,
              i₁ ∈ PlaneRaw.Code.extSupport e' := by
            intro hne
            rw [hsupp']
            exact Finset.mem_erase.mpr ⟨Ne.symm hne, Finset.mem_univ i₁⟩
          have hex : ∃ j' ∈ PlaneRaw.Code.extSupport e', j' ≠ i₁ := by
            by_contra hall
            have hsub : PlaneRaw.Code.extSupport e' ⊆ {i₁} := by
              intro j' hj'
              rw [Finset.mem_singleton]
              by_contra hne'
              exact hall ⟨j', hj', hne'⟩
            have hle := Finset.card_le_card hsub
            rw [Finset.card_singleton] at hle
            have hcard : (PlaneRaw.Code.extSupport e').card = t - 1 := by
              rw [hsupp', Finset.card_erase_of_mem (Finset.mem_univ i₀),
                Finset.card_univ, Fintype.card_fin]
            omega
          obtain ⟨j', hj'supp, hj'ne⟩ := hex
          have hi₀ : i₀ = i₁ := by
            by_contra hne
            have hi₁supp : i₁ ∈ PlaneRaw.Code.extSupport e' := hi₁supp_of hne
            have hvxU' : vx ∈ PlaneRaw.cent k (.extension e') := by
              rw [hcentj]; exact hvxU
            have hcent_eq :=
              (PlaneRaw.mem_cent_extension k e' vx).mp hvxU' i₁ hi₁supp j' hj'supp
            have hvxj : vx j' = 0 := by
              rw [← ha]
              simp [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hj'ne]
            have hvxi : vx i₁ = a := by
              rw [← ha]
              simp [Pi.smul_apply, smul_eq_mul]
            have he'i₁ : e' i₁ ≠ 0 := by simpa using hi₁supp
            rw [hvxj, mul_zero, hvxi] at hcent_eq
            exact (mul_ne_zero he'i₁ ha0) hcent_eq
          have hsupp'i : PlaneRaw.Code.extSupport e' = Finset.univ.erase i₁ := by
            rw [hsupp', hi₀]
          have he'i₁ : e' i₁ = 0 := by
            have h : i₁ ∉ PlaneRaw.Code.extSupport e' := by rw [hsupp'i]; simp
            simpa using h
          have hzfull : ∀ j, (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) j ≠ 0 := by
            intro j
            by_cases hj : j = i₁
            · subst hj
              simp [Pi.add_apply, he'i₁]
            · have hj' : j ∈ PlaneRaw.Code.extSupport e' := by rw [hsupp'i]; simp [hj]
              have hej : e' j ≠ 0 := by simpa using hj'
              simpa [Pi.add_apply, Pi.single_eq_of_ne hj] using hej
          have hz0 : (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) ≠ 0 := by
            intro h0
            exact hzfull i₁ (by rw [h0]; rfl)
          have hzU : (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) ∈ U := by
            rw [← hcentj, PlaneRaw.mem_cent_extension]
            intro p hp q hq
            have hp' : p ≠ i₁ := by
              have h := hp; rw [hsupp'i] at h
              exact (Finset.mem_erase.mp h).1
            have hq' : q ≠ i₁ := by
              have h := hq; rw [hsupp'i] at h
              exact (Finset.mem_erase.mp h).1
            have hzp : (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) p = e' p := by
              simp [Pi.add_apply, Pi.single_eq_of_ne hp']
            have hzq : (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) q = e' q := by
              simp [Pi.add_apply, Pi.single_eq_of_ne hq']
            rw [hzp, hzq]
            exact (cpl_sq_eq_one (e' p) (by simpa using hp)).trans
              (cpl_sq_eq_one (e' q) (by simpa using hq)).symm
          have hzx : (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) ∉
              Submodule.span PlaneRaw.F {vx} := by
            intro hmem
            rw [hspan_vx] at hmem
            obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hmem
            have hzj' : (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) j' = 0 := by
              rw [← hcc]
              simp [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hj'ne]
            have hz' : (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) j' = e' j' := by
              simp [Pi.add_apply, Pi.single_eq_of_ne hj'ne]
            rw [hz'] at hzj'
            have hej' : e' j' ≠ 0 := by simpa using hj'supp
            exact hej' hzj'
          have hsuppz : PlaneRaw.Code.extSupport
              (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) = Finset.univ :=
            Finset.eq_univ_of_forall (fun j => by simpa using hzfull j)
          have hcardz : (PlaneRaw.Code.extSupport
              (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t))).card = t := by
            rw [hsuppz, Finset.card_univ, Fintype.card_fin]
          have hadm : 4 ≤ t ∧ PlaneRaw.admissible k
              (.extension (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t))) :=
            ⟨h4t, cpl_admissible_extension_full h4t hz0 hcardz⟩
          have hocc : PlaneRaw.occurs (Submodule.span PlaneRaw.F
              {e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)})
              (.extension (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t))) :=
            cpl_occurs_extension_self i₁ hzfull
          have hcentz : PlaneRaw.cent k
              (.extension (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t))) =
              Submodule.span PlaneRaw.F
                {e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)} :=
            cpl_cent_ext_self i₁ hzfull
          have hN : PlaneRaw.normalizerOf k t (.extension e') ≤
              PlaneRaw.normalizerOf k t
                (.extension (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t))) :=
            cpl_twisted_le_twisted_add_single he'i₁ hzfull
          have hnin : vx ∉ PlaneRaw.cent k
              (.extension (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t))) := by
            intro hmem
            have hzline : vx ∈ Submodule.span PlaneRaw.F
                {e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)} := by
              rw [← hcentz]; exact hmem
            have heqline : Submodule.span PlaneRaw.F
                {e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)} =
                Submodule.span PlaneRaw.F {vx} :=
              cpl_span_singleton_eq_of_mem hz0 hzline hvx
            exact hzx (by rw [← heqline]; exact Submodule.mem_span_singleton_self _)
          have hwit : PlaneRaw.ChainWitnessOn t
              (PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₁)))
              (PlaneRaw.normalizerOf k t
                (.extension (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t))))
              vx (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)) := by
            refine (cpl_chainWitnessOn_congr hspan_vx rfl).mpr ?_
            exact cpl_chainWitness_zero_left k t h4t hzfull i₁
          exact Or.inl ⟨e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t), hzU, hzx,
            .extension (e' + (Pi.single i₁ (1 : PlaneRaw.F) : PlaneRaw.V t)),
            hadm, hocc, hcentz, hN, hnin, hwit⟩
  | extension e =>
      have he : e ≠ 0 := hℓadm.1
      obtain ⟨hei, hspan_vx_e⟩ := cpl_ext_shape hvx he hcent
      obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.mp
        (by rw [← hspan_vx_e]; exact Submodule.mem_span_singleton_self vx)
      have ha0 : a ≠ 0 := by
        intro h0
        apply hvx
        rw [← ha, h0, zero_smul]
      cases j with
      | zero S' =>
          exfalso
          by_cases hS' : S' = ∅
          · have hUtop : U = ⊤ := by
              rw [← hcentj, hS']
              rw [Submodule.eq_top_iff']
              intro v
              rw [PlaneRaw.mem_cent_zero]
              intro i hi
              exact absurd hi (by simp)
            have hdt : finrank PlaneRaw.F U = t := by
              rw [hUtop, finrank_top]
              simp
            rw [hdt] at hU
            omega
          · obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hS'
            have hvxU' : vx ∈ PlaneRaw.cent k (.zero S') := by rw [hcentj]; exact hvxU
            have hvi : vx i = 0 := (PlaneRaw.mem_cent_zero k S' vx).mp hvxU' i hi
            have hve : vx i = a * e i := by rw [← ha]; simp [Pi.smul_apply, smul_eq_mul]
            rw [hve] at hvi
            exact (mul_ne_zero ha0 (hei i)) hvi
      | extension e' =>
          have he' : e' ≠ 0 := hjadm.1
          obtain ⟨i₀, hsupp'⟩ := cpl_ext_cent_shape h4t hU hcentj he'
          have hexj : ∃ j : Fin t, j ≠ i₀ := by
            by_contra hall
            have hsub : Finset.univ ⊆ {i₀} := by
              intro j _
              rw [Finset.mem_singleton]
              by_contra hne
              exact hall ⟨j, hne⟩
            have hle := Finset.card_le_card hsub
            rw [Finset.card_singleton, Finset.card_univ, Fintype.card_fin] at hle
            omega
          obtain ⟨j, hjne⟩ := hexj
          have hzU : (Pi.single i₀ (1 : PlaneRaw.F) : PlaneRaw.V t) ∈ U := by
            rw [← hcentj, PlaneRaw.mem_cent_extension]
            intro p hp q hq
            have hp' : p ≠ i₀ := by
              have h := hp; rw [hsupp'] at h
              exact (Finset.mem_erase.mp h).1
            have hq' : q ≠ i₀ := by
              have h := hq; rw [hsupp'] at h
              exact (Finset.mem_erase.mp h).1
            simp [Pi.single_eq_of_ne hp', Pi.single_eq_of_ne hq']
          have hzx : (Pi.single i₀ (1 : PlaneRaw.F) : PlaneRaw.V t) ∉
              Submodule.span PlaneRaw.F {vx} := by
            intro hmem
            rw [hspan_vx_e] at hmem
            obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hmem
            have h1 : cc * e i₀ = 1 := by
              have hh := congrFun hcc i₀
              simpa [Pi.smul_apply, smul_eq_mul] using hh
            have h2 : cc * e j = 0 := by
              have hh := congrFun hcc j
              simpa [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hjne] using hh
            have hcc0 : cc = 0 := (mul_eq_zero.mp h2).resolve_right (hei j)
            rw [hcc0, zero_mul] at h1
            exact zero_ne_one h1
          have hN : PlaneRaw.normalizerOf k t (.extension e') ≤
              PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₀)) :=
            cpl_twisted_le_zero_normalizer k t h4t hsupp'
          have hnin : vx ∉ PlaneRaw.cent k (.zero (Finset.univ.erase i₀)) := by
            rw [cpl_cent_zero_erase]
            intro hmem
            obtain ⟨cc, hcc⟩ := Submodule.mem_span_singleton.mp hmem
            have hvj : vx j = 0 := by
              rw [← hcc]
              simp [Pi.smul_apply, smul_eq_mul, Pi.single_eq_of_ne hjne]
            have hvj' : vx j = a * e j := by rw [← ha]; simp [Pi.smul_apply, smul_eq_mul]
            rw [hvj'] at hvj
            exact (mul_ne_zero ha0 (hei j)) hvj
          have hwit : PlaneRaw.ChainWitnessOn t
              (PlaneRaw.normalizerOf k t (.extension e))
              (PlaneRaw.normalizerOf k t (.zero (Finset.univ.erase i₀)))
              vx (Pi.single i₀ (1 : PlaneRaw.F)) := by
            refine (cpl_chainWitnessOn_congr hspan_vx_e rfl).mpr ?_
            exact cpl_chainWitness_zero_right k t h4t hei i₀
          exact Or.inl ⟨Pi.single i₀ (1 : PlaneRaw.F), hzU, hzx,
            .zero (Finset.univ.erase i₀), ⟨h4t, cpl_admissible_zero_erase h4t i₀⟩,
            cpl_occurs_zero_erase i₀, cpl_cent_zero_erase k i₀, hN, hnin, hwit⟩

end

theorem censusCases_planeEntry (k : PlaneRaw.PlaneKind) (t : ℕ) :
    CensusCases (planeEntry k t) := by
  intro vx hvx ℓ hℓ hocc hcent hnin U hU hvxU j hj hoccj hcentj hinj hNj
  obtain ⟨h4t, hℓadm⟩ := hℓ
  obtain ⟨-, hjadm⟩ := hj
  rcases cpl_censusCases_planeEntry_raw (k := k) (t := t) h4t vx hvx ℓ hℓadm hcent U hU
      hvxU j hjadm hcentj with ⟨z, hzU, hzx, c, hcA, hcB, hcC, hcD, hcE, hcF⟩ | hD
  · refine Or.inl ⟨z, hzU, hzx, c, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_, ?_, ?_⟩
      · exact hcA
      · exact hcB
      · exact hcC
      · exact hcD
      · exact hcE
    · exact hcF
  · refine Or.inr (Or.inr (Or.inr ?_))
    intro z hzU hzx c hc hinc
    exact Or.inr (hD z hzU hzx c hc.1 hc.2.1 hc.2.2.1 hc.2.2.2.1 hc.2.2.2.2)

theorem censusCasesLin_holds : CensusCasesLin := by
  intro t ε
  change CensusCases (planeEntry (.linear ε) t)
  exact censusCases_planeEntry (.linear ε) t

theorem censusCasesSymp_holds : CensusCasesSymp := by
  intro t
  change CensusCases (planeEntry .symplectic t)
  exact censusCases_planeEntry .symplectic t

theorem censusCasesOrth_holds : CensusCasesOrth := by
  intro t δ
  change CensusCases (planeEntry (.orthogonal δ) t)
  exact censusCases_planeEntry (.orthogonal δ) t

end CFSG.StandardType.GGQ2Frame

end
