module

public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorCore
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorRot

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open Polynomial Module CFSG CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal CFSG.RankThree.OrthogonalInvolutions
open scoped commutatorElement

section Elementary

theorem isSquare_inv_mul_of_not_isSquare {K : Type*} [Field K] [Finite K] {a b : K} (ha : a ≠ 0)
    (hb : b ≠ 0) (ha' : ¬ IsSquare a) (hb' : ¬ IsSquare b) : IsSquare (a⁻¹ * b) := by
  classical
  have := Fintype.ofFinite K
  by_cases hF : ringChar K = 2
  · exact FiniteField.isSquare_of_char_two hF _
  · have ha1 : a ^ (Fintype.card K / 2) = -1 :=
      (FiniteField.pow_dichotomy hF ha).resolve_left fun h =>
        ha' ((FiniteField.isSquare_iff hF ha).mpr h)
    have hb1 : b ^ (Fintype.card K / 2) = -1 :=
      (FiniteField.pow_dichotomy hF hb).resolve_left fun h =>
        hb' ((FiniteField.isSquare_iff hF hb).mpr h)
    rw [FiniteField.isSquare_iff hF (mul_ne_zero (inv_ne_zero ha) hb), mul_pow, inv_pow, ha1, hb1]
    norm_num

theorem relIndex_le_two_of_forall {G : Type*} [Group G] {H H' : Subgroup G}
    (h : ∀ g ∈ H', ∀ g' ∈ H', g ∉ H → g' ∉ H → g⁻¹ * g' ∈ H) : H.relIndex H' ≤ 2 := by
  by_cases htop : H.subgroupOf H' = ⊤
  · rw [Subgroup.relIndex, htop, Subgroup.index_top]
    omega
  · have hex : ∃ a : H', a ∉ H.subgroupOf H' := by
      by_contra hcon
      push Not at hcon
      exact htop (eq_top_iff.mpr fun a _ => hcon a)
    obtain ⟨a, ha⟩ := hex
    have h2 : (H.subgroupOf H').index = 2 := by
      rw [Subgroup.index_eq_two_iff]
      refine ⟨a, fun b => ?_⟩
      by_cases hb : b ∈ H.subgroupOf H'
      · refine Or.inr ⟨hb, fun hba => ha ?_⟩
        have := (H.subgroupOf H').mul_mem ((H.subgroupOf H').inv_mem hb) hba
        simpa using this
      · refine Or.inl ⟨?_, hb⟩
        rw [Subgroup.mem_subgroupOf] at hb ha ⊢
        have hbinv : (b : G)⁻¹ ∉ H := fun hh => hb (by simpa using H.inv_mem hh)
        have := h (b : G)⁻¹ (H'.inv_mem b.2) (a : G) a.2 hbinv ha
        simpa using this
    rw [Subgroup.relIndex, h2]

end Elementary

section Restrict

variable {K : Type} [Field K] {V : Type*} [AddCommGroup V] [Module K V] {xe : V ≃ₗ[K] V}

@[expose] def restrictLin (M : V ≃ₗ[K] V) (hM : ∀ v, M (xe v) = xe (M v)) :
    fixedSpace xe ≃ₗ[K] fixedSpace xe where
  toFun w := ⟨M (w : V), mem_fixedSpace.mpr (by rw [← hM, mem_fixedSpace.mp w.2])⟩
  invFun w := ⟨M.symm (w : V), mem_fixedSpace.mpr (by
    apply M.injective
    rw [hM, LinearEquiv.apply_symm_apply]
    exact mem_fixedSpace.mp w.2)⟩
  map_add' a b := Subtype.ext (map_add M (a : V) (b : V))
  map_smul' c a := Subtype.ext (map_smul M c (a : V))
  left_inv w := Subtype.ext (M.symm_apply_apply (w : V))
  right_inv w := Subtype.ext (M.apply_symm_apply (w : V))

theorem coe_restrictLin (M : V ≃ₗ[K] V) (hM : ∀ v, M (xe v) = xe (M v)) (w : fixedSpace xe) :
    ((restrictLin M hM w : fixedSpace xe) : V) = M (w : V) := rfl

@[expose] def restrictAdd (F : V ≃+ V) (hF : ∀ v, F (xe v) = xe (F v)) :
    fixedSpace xe ≃+ fixedSpace xe where
  toFun w := ⟨F (w : V), mem_fixedSpace.mpr (by rw [← hF, mem_fixedSpace.mp w.2])⟩
  invFun w := ⟨F.symm (w : V), mem_fixedSpace.mpr (by
    apply F.injective
    rw [hF, AddEquiv.apply_symm_apply]
    exact mem_fixedSpace.mp w.2)⟩
  left_inv w := Subtype.ext (F.symm_apply_apply (w : V))
  right_inv w := Subtype.ext (F.apply_symm_apply (w : V))
  map_add' a b := Subtype.ext (map_add F (a : V) (b : V))

theorem coe_restrictAdd (F : V ≃+ V) (hF : ∀ v, F (xe v) = xe (F v)) (w : fixedSpace xe) :
    ((restrictAdd F hF w : fixedSpace xe) : V) = F (w : V) := rfl

theorem coe_restrictAdd_symm (F : V ≃+ V) (hF : ∀ v, F (xe v) = xe (F v))
    (w : fixedSpace xe) : (((restrictAdd F hF).symm w : fixedSpace xe) : V) = F.symm (w : V) :=
  rfl

end Restrict

section Subgroups

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
  (xe : (Fin d → K) ≃ₗ[K] (Fin d → K))

theorem pairMap_smul_of_right {u : similarityPairs Q} (hu : u.val.right = 1) (c : K)
    (v : Fin d → K) : pairMap Q u (c • v) = c • pairMap Q u v := by
  rw [pairMap_smul, hu]
  rfl

theorem exists_mult_of_right {u : similarityPairs Q} (hu : u.val.right = 1) :
    ∃ μ : Kˣ, ∀ v, Q (pairMap Q u v) = (μ : K) * Q v := by
  obtain ⟨μ, hμ⟩ := exists_pairMap_sim Q u
  refine ⟨μ, fun v => ?_⟩
  rw [hμ v, hu]
  rfl

@[expose] def UP1 : Subgroup (similarityPairs Q) where
  carrier := {u | u ∈ UP Q xe ∧ ∃ c : Kˣ, ∀ v, Q (pairMap Q u v) = (c : K) ^ 2 * Q v}
  one_mem' := ⟨one_mem _, 1, fun v => by rw [pairMap_one, Units.val_one, one_pow, one_mul]⟩
  mul_mem' := by
    rintro u u' ⟨hu, c, hc⟩ ⟨hu', c', hc'⟩
    refine ⟨mul_mem hu hu', c * c', fun v => ?_⟩
    rw [pairMap_mul, hc, hc', Units.val_mul]
    ring
  inv_mem' := by
    rintro u ⟨hu, c, hc⟩
    refine ⟨inv_mem hu, c⁻¹, fun v => ?_⟩
    rw [pairMap_inv]
    have h1 := hc ((pairMap Q u).symm v)
    rw [AddEquiv.apply_symm_apply] at h1
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    rw [h1, Units.val_inv_eq_inv_val]
    field_simp

theorem UP1_le_UP : UP1 Q xe ≤ UP Q xe := fun _ hu => hu.1

variable {Q xe}

@[expose] noncomputable def UplusBin
    (hQW : (QuadraticMap.polarBilin (Q.comp (fixedSpace xe).subtype)).Nondegenerate) :
    Subgroup (similarityPairs Q) where
  carrier := {u | u ∈ UP1 Q xe ∧ ∃ (c : Kˣ) (y : fixedSpace xe ≃ₗ[K] fixedSpace xe),
    y ∈ rotGroup (Q.comp (fixedSpace xe).subtype) hQW ∧
      ∀ w : fixedSpace xe, pairMap Q u (w : Fin d → K) = (c : K) • ((y w : fixedSpace xe) : _)}
  one_mem' := ⟨one_mem _, 1, 1, one_mem _, fun w => by
    rw [pairMap_one, Units.val_one, one_smul]
    rfl⟩
  mul_mem' := by
    rintro u u' ⟨hu, c, y, hy, hcy⟩ ⟨hu', c', y', hy', hcy'⟩
    refine ⟨mul_mem hu hu', c * c', y * y', mul_mem hy hy', fun w => ?_⟩
    rw [pairMap_mul, hcy', pairMap_smul_of_right Q hu.1.1, hcy (y' w), smul_smul, Units.val_mul,
      mul_comm]
    rfl
  inv_mem' := by
    rintro u ⟨hu, c, y, hy, hcy⟩
    refine ⟨inv_mem hu, c⁻¹, y⁻¹, inv_mem hy, fun w => ?_⟩
    rw [pairMap_inv]
    apply (pairMap Q u).injective
    rw [AddEquiv.apply_symm_apply, pairMap_smul_of_right Q hu.1.1, hcy ((y⁻¹) w), smul_smul]
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    rw [Units.val_inv_eq_inv_val, inv_mul_cancel₀ hc0, one_smul]
    change _ = ((y (y⁻¹ w) : fixedSpace xe) : Fin d → K)
    rw [← LinearEquiv.mul_apply, mul_inv_cancel]
    rfl

theorem UplusBin_le_UP1
    (hQW : (QuadraticMap.polarBilin (Q.comp (fixedSpace xe).subtype)).Nondegenerate) :
    UplusBin hQW ≤ UP1 Q xe := fun _ hu => hu.1

end Subgroups

section Index

variable {K : Type} [Field K] [Finite K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))
  (xe : (Fin d → K) ≃ₗ[K] (Fin d → K))

omit [Finite K] in
theorem exists_isometry_of_mem_UP1 {g : similarityPairs Q} (hg : g ∈ UP1 Q xe) :
    ∃ (c : Kˣ) (y : fixedSpace xe ≃ₗ[K] fixedSpace xe),
      y ∈ TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace xe).subtype) ∧
      ∀ w : fixedSpace xe, pairMap Q g (w : Fin d → K) = (c : K) • ((y w : fixedSpace xe) : _) := by
  obtain ⟨hgUP, c, hc⟩ := hg
  have hMx : ∀ v, linOf Q g hgUP.1 (xe v) = xe (linOf Q g hgUP.1 v) := fun v =>
    UP_comm_xe Q hgUP v
  let y : fixedSpace xe ≃ₗ[K] fixedSpace xe :=
    (restrictLin (linOf Q g hgUP.1) hMx).trans (LinearEquiv.smulOfUnit c⁻¹)
  have hy : ∀ w : fixedSpace xe, ((y w : fixedSpace xe) : Fin d → K) =
      ((c⁻¹ : Kˣ) : K) • pairMap Q g (w : Fin d → K) := fun w => rfl
  refine ⟨c, y, ?_, fun w => ?_⟩
  · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
    intro w
    change Q ((y w : fixedSpace xe) : Fin d → K) = Q (w : Fin d → K)
    rw [hy, QuadraticMap.map_smul, hc, smul_eq_mul, Units.val_inv_eq_inv_val]
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    field_simp
  · rw [hy, smul_smul, Units.val_inv_eq_inv_val, mul_inv_cancel₀ c.ne_zero, one_smul]

theorem relIndex_UP1_le_two : (UP1 Q xe).relIndex (UP Q xe) ≤ 2 := by
  refine relIndex_le_two_of_forall fun g hg g' hg' hgn hg'n => ?_
  obtain ⟨μ, hμ⟩ := exists_mult_of_right Q hg.1
  obtain ⟨μ', hμ'⟩ := exists_mult_of_right Q hg'.1
  have hns : ∀ {u : similarityPairs Q}, u ∈ UP Q xe → ∀ m : Kˣ,
      (∀ v, Q (pairMap Q u v) = (m : K) * Q v) → u ∉ UP1 Q xe → ¬ IsSquare (m : K) := by
    intro u hu m hm hun ⟨r, hr⟩
    apply hun
    have hr0 : r ≠ 0 := by
      rintro rfl
      simp at hr
    refine ⟨hu, Units.mk0 r hr0, fun v => ?_⟩
    rw [hm v, hr, Units.val_mk0, sq]
  obtain ⟨r, hr⟩ := isSquare_inv_mul_of_not_isSquare μ.ne_zero μ'.ne_zero
    (hns hg μ hμ hgn) (hns hg' μ' hμ' hg'n)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  refine ⟨mul_mem (inv_mem hg) hg', Units.mk0 r hr0, fun v => ?_⟩
  rw [pairMap_mul, pairMap_inv]
  have hμ0 : (μ : K) ≠ 0 := μ.ne_zero
  have h1 : Q (pairMap Q g ((pairMap Q g).symm (pairMap Q g' v))) =
      (μ : K) * Q ((pairMap Q g).symm (pairMap Q g' v)) := hμ _
  rw [AddEquiv.apply_symm_apply, hμ' v] at h1
  calc Q ((pairMap Q g).symm (pairMap Q g' v))
      = (μ : K)⁻¹ * ((μ : K) * Q ((pairMap Q g).symm (pairMap Q g' v))) := by
        rw [inv_mul_cancel_left₀ hμ0]
    _ = (μ : K)⁻¹ * ((μ' : K) * Q v) := by rw [← h1]
    _ = ((μ : K)⁻¹ * μ') * Q v := by rw [mul_assoc]
    _ = ((Units.mk0 r hr0 : Kˣ) : K) ^ 2 * Q v := by rw [hr, Units.val_mk0, sq]

variable {Q xe}

omit [Finite K] in
theorem relIndex_UplusBin_le_two
    (hQW : (QuadraticMap.polarBilin (Q.comp (fixedSpace xe).subtype)).Nondegenerate) :
    (UplusBin hQW).relIndex (UP1 Q xe) ≤ 2 := by
  refine relIndex_le_two_of_forall fun g hg g' hg' hgn hg'n => ?_
  obtain ⟨c, y, hyO, hcy⟩ := exists_isometry_of_mem_UP1 Q xe hg
  obtain ⟨c', y', hyO', hcy'⟩ := exists_isometry_of_mem_UP1 Q xe hg'
  have hδ : dicksonHom (Q.comp (fixedSpace xe).subtype) hQW ⟨y, hyO⟩ ≠ 1 := fun h1 =>
    hgn ⟨hg, c, y, mem_rotGroup.mpr ⟨hyO, h1⟩, hcy⟩
  have hδ' : dicksonHom (Q.comp (fixedSpace xe).subtype) hQW ⟨y', hyO'⟩ ≠ 1 := fun h1 =>
    hg'n ⟨hg', c', y', mem_rotGroup.mpr ⟨hyO', h1⟩, hcy'⟩
  have key : ∀ a b : Multiplicative (ZMod 2), a ≠ 1 → b ≠ 1 → a⁻¹ * b = 1 := by decide
  refine ⟨mul_mem (inv_mem hg) hg', c⁻¹ * c', y⁻¹ * y', ?_, fun w => ?_⟩
  · refine mem_rotGroup.mpr ⟨mul_mem (inv_mem hyO) hyO', ?_⟩
    have : (⟨y⁻¹ * y', mul_mem (inv_mem hyO) hyO'⟩ :
        TauCeti.QuadraticMap.orthogonalGroup (Q.comp (fixedSpace xe).subtype)) =
        ⟨y, hyO⟩⁻¹ * ⟨y', hyO'⟩ := rfl
    rw [this, map_mul, map_inv]
    exact key _ _ hδ hδ'
  · rw [pairMap_mul, pairMap_inv]
    apply (pairMap Q g).injective
    have hyy : y ((y⁻¹ * y') w) = y' w := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel_left]
    rw [AddEquiv.apply_symm_apply, hcy', pairMap_smul_of_right Q hg.1.1, hcy ((y⁻¹ * y') w), hyy,
      smul_smul, Units.val_mul, Units.val_inv_eq_inv_val]
    congr 1
    have hc0 : (c : K) ≠ 0 := c.ne_zero
    field_simp

theorem relIndex_UplusBin_le
    (hQW : (QuadraticMap.polarBilin (Q.comp (fixedSpace xe).subtype)).Nondegenerate) :
    (UplusBin hQW).relIndex (UP Q xe) ≤ 4 := by
  have h1 := relIndex_UP1_le_two Q xe
  have h2 := relIndex_UplusBin_le_two hQW
  rw [← Subgroup.relIndex_mul_relIndex (UplusBin hQW) (UP1 Q xe) (UP Q xe)
    (UplusBin_le_UP1 hQW) (UP1_le_UP Q xe)]
  calc (UplusBin hQW).relIndex (UP1 Q xe) * (UP1 Q xe).relIndex (UP Q xe) ≤ 2 * 2 :=
        Nat.mul_le_mul h2 h1
    _ = 4 := rfl

end Index

section Comm

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)}

theorem blockScalar_of_mem_UP_ne (Q : QuadraticForm K (Fin d → K)) (hx : OddOrderIsometry Q p xe)
    (hp : p.Prime) (hp3 : 3 < p) {g : similarityPairs Q} (hg : g ∈ UP Q xe) {h : K[X]}
    (hh : h ∈ primaryFactors xe.toLinearMap) (hne1 : h ≠ X - 1) :
    BlockScalar xe (linOf Q g hg.1) h := by
  have hMx : ∀ v, linOf Q g hg.1 (xe v) = xe (linOf Q g hg.1 v) := fun v => UP_comm_xe Q hg v
  exact exists_blockScalar hx hp hp3 hh hne1 hMx fun f hf v =>
    hg.2.1 f (mem_commFam_of_specialBlock Q hh hne1 hf) v

theorem kappa_comm_of_mem_UplusBin (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p)
    (hdim : finrank K (fixedSpace xe) = 2)
    {hQW : (QuadraticMap.polarBilin (Q.comp (fixedSpace xe).subtype)).Nondegenerate}
    {u u' : similarityPairs Q} (hu : u ∈ UplusBin hQW) (hu' : u' ∈ UplusBin hQW) :
    kappa Q u * kappa Q u' = kappa Q u' * kappa Q u := by
  rw [← map_mul, ← map_mul]
  refine kappa_congr Q fun v => ?_
  obtain ⟨hu1, c, y, hy, hcy⟩ := hu
  obtain ⟨hu1', c', y', hy', hcy'⟩ := hu'
  have hUP : u ∈ UP Q xe := hu1.1
  have hUP' : u' ∈ UP Q xe := hu1'.1
  have hlin : ((linOf Q u hUP.1 * linOf Q u' hUP'.1 : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
      (Fin d → K) →ₗ[K] (Fin d → K)) =
      ((linOf Q u' hUP'.1 * linOf Q u hUP.1 : (Fin d → K) ≃ₗ[K] (Fin d → K)) :
        (Fin d → K) →ₗ[K] (Fin d → K)) := by
    refine ext_primaryComponent hx.squarefree_minpoly fun h hh v hv => ?_
    by_cases hne1 : h = X - 1
    · subst hne1
      have hvW : v ∈ fixedSpace xe := by
        rw [fixedSpace_eq_primaryComponent (x := xe)]
        exact hv
      have hcomm := LinearEquiv.congr_fun (commute_of_mem_rotGroup hdim hy hy') ⟨v, hvW⟩
      change pairMap Q u (pairMap Q u' v) = pairMap Q u' (pairMap Q u v)
      have h1 : pairMap Q u' v = (c' : K) • ((y' ⟨v, hvW⟩ : fixedSpace xe) : Fin d → K) :=
        hcy' ⟨v, hvW⟩
      have h2 : pairMap Q u v = (c : K) • ((y ⟨v, hvW⟩ : fixedSpace xe) : Fin d → K) :=
        hcy ⟨v, hvW⟩
      rw [h1, pairMap_smul_of_right Q hUP.1, hcy (y' ⟨v, hvW⟩), h2,
        pairMap_smul_of_right Q hUP'.1, hcy' (y ⟨v, hvW⟩), smul_comm (c' : K) (c : K)]
      congr 2
      exact congrArg Subtype.val (by simpa using hcomm)
    · exact mul_comm_apply_of_blockScalar (blockScalar_of_mem_UP_ne Q hx hp hp3 hUP hh hne1)
        (blockScalar_of_mem_UP_ne Q hx hp hp3 hUP' hh hne1) hv
  rw [pairMap_mul, pairMap_mul]
  exact LinearMap.congr_fun hlin v

end Comm

section Iterate

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

theorem iterate_semilinConj_apply (F : W ≃+ W) (σ : K ≃+* K)
    (hF : ∀ (c : K) (v : W), F (c • v) = σ c • F v) (n : ℕ) (z : W ≃ₗ[K] W) (v : W) :
    ((semilinConj F σ hF)^[n] z) v = F^[n] (z ((F.symm)^[n] v)) := by
  induction n generalizing v with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', semilinConj_apply, ih,
      Function.iterate_succ_apply' (f := (F : W → W)),
      Function.iterate_succ_apply (f := (F.symm : W → W))]

theorem iterate_semilinConj_eq_self (F : W ≃+ W) (σ : K ≃+* K)
    (hF : ∀ (c : K) (v : W), F (c • v) = σ c • F v) {N : ℕ} {c₀ : K}
    (hc : ∀ v, F^[N] v = c₀ • v) (z : W ≃ₗ[K] W) : (semilinConj F σ hF)^[N] z = z := by
  refine LinearEquiv.ext fun v => ?_
  rw [iterate_semilinConj_apply]
  have hri : Function.RightInverse (F.symm : W → W) (F : W → W) := F.apply_symm_apply
  have hu : c₀ • (F.symm)^[N] v = v := by
    rw [← hc]
    exact (hri.iterate N) v
  rw [hc, ← map_smul, hu]

theorem ringEquiv_pow_apply (σ : K ≃+* K) (n : ℕ) (x : K) : (σ ^ n) x = σ^[n] x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    rw [pow_succ', RingAut.mul_apply, ih, Function.iterate_succ_apply']

end Iterate

section Conj

variable {K : Type} [Field K] [Finite K] {d : ℕ} {Q : QuadraticForm K (Fin d → K)} {p : ℕ}
  {xe : (Fin d → K) ≃ₗ[K] (Fin d → K)}

@[expose] def restrictPair (g : similarityPairs Q)
    (hFx : ∀ v, pairMap Q g (xe v) = xe (pairMap Q g v)) : fixedSpace xe ≃+ fixedSpace xe :=
  restrictAdd (pairMap Q g) hFx

omit [Finite K] in
theorem restrictPair_smul (g : similarityPairs Q)
    (hFx : ∀ v, pairMap Q g (xe v) = xe (pairMap Q g v)) (a : K) (w : fixedSpace xe) :
    restrictPair g hFx (a • w) = g.val.right a • restrictPair g hFx w :=
  Subtype.ext (pairMap_smul Q g a (w : Fin d → K))

omit [Finite K] in
theorem restrictPair_sim (g : similarityPairs Q)
    (hFx : ∀ v, pairMap Q g (xe v) = xe (pairMap Q g v)) {μ : Kˣ}
    (hμ : ∀ v, Q (pairMap Q g v) = (μ : K) * g.val.right (Q v)) (w : fixedSpace xe) :
    (Q.comp (fixedSpace xe).subtype) (restrictPair g hFx w) =
      (μ : K) * g.val.right ((Q.comp (fixedSpace xe).subtype) w) :=
  hμ (w : Fin d → K)

omit [Finite K] in
theorem pairMap_conj_apply_fixed (g u : similarityPairs Q)
    (hFx : ∀ v, pairMap Q g (xe v) = xe (pairMap Q g v)) {c : K}
    {y : fixedSpace xe ≃ₗ[K] fixedSpace xe}
    (hcy : ∀ w : fixedSpace xe, pairMap Q u (w : Fin d → K) = c • ((y w : fixedSpace xe) : _))
    (w : fixedSpace xe) :
    pairMap Q (g * u * g⁻¹) (w : Fin d → K) =
      g.val.right c • ((semilinConj (restrictPair g hFx) g.val.right (restrictPair_smul g hFx) y w :
        fixedSpace xe) : Fin d → K) := by
  rw [pairMap_mul, pairMap_mul, pairMap_inv]
  have h1 : (pairMap Q g).symm (w : Fin d → K) =
      (((restrictPair g hFx).symm w : fixedSpace xe) : Fin d → K) := rfl
  rw [h1, hcy, pairMap_smul Q g]
  rfl

omit [Finite K] in
theorem coe_restrictPair_iterate (g : similarityPairs Q)
    (hFx : ∀ v, pairMap Q g (xe v) = xe (pairMap Q g v)) (m : ℕ) (w : fixedSpace xe) :
    (((restrictPair g hFx)^[m] w : fixedSpace xe) : Fin d → K) =
      (pairMap Q g)^[m] (w : Fin d → K) := by
  induction m generalizing w with
  | zero => rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, ih]
    rfl

theorem mem_UplusBin_conj (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p)
    (hdim : finrank K (fixedSpace xe) = 2)
    {hQW : (QuadraticMap.polarBilin (Q.comp (fixedSpace xe).subtype)).Nondegenerate}
    {g : similarityPairs Q} (hg : GoodPair Q xe p g) {u : similarityPairs Q}
    (hu : u ∈ UplusBin hQW) : g * u * g⁻¹ ∈ UplusBin hQW := by
  obtain ⟨hu1, c, y, hy, hcy⟩ := hu
  have hUP : g * u * g⁻¹ ∈ UP Q xe := conj_mem_UP Q hx hp hp3 g hg.1 hg.2.2 hu1.1
  obtain ⟨μ, hμ⟩ := exists_pairMap_sim Q g
  refine ⟨⟨hUP, ?_⟩, ?_⟩
  ·
    obtain ⟨-, c₁, hc₁⟩ := hu1
    refine ⟨Units.map (g.val.right : K →+* K).toMonoidHom c₁, fun v => ?_⟩
    rw [pairMap_mul, pairMap_mul, pairMap_inv]
    have h2 := hμ ((pairMap Q g).symm v)
    rw [AddEquiv.apply_symm_apply] at h2
    rw [hμ, hc₁, map_mul, map_pow, h2]
    have : ((Units.map (g.val.right : K →+* K).toMonoidHom c₁ : Kˣ) : K) =
        g.val.right (c₁ : K) := rfl
    rw [this]
    ring
  · refine ⟨Units.map (g.val.right : K →+* K).toMonoidHom c,
      semilinConj (restrictPair g hg.1) g.val.right (restrictPair_smul g hg.1) y,
      semilinConj_mem_rotGroup hdim (restrictPair g hg.1) g.val.right (restrictPair_smul g hg.1)
        μ (restrictPair_sim g hg.1 hμ) hy, fun w => ?_⟩
    rw [pairMap_conj_apply_fixed g u hg.1 hcy w]
    rfl

omit [Finite K] in
theorem pairMap_conj_apply_fixed_of_pow (hdim : finrank K (fixedSpace xe) = 2)
    {hQW : (QuadraticMap.polarBilin (Q.comp (fixedSpace xe).subtype)).Nondegenerate}
    {g : similarityPairs Q} (hgood : GoodPair Q xe p g) (hp2 : Odd p) {u : similarityPairs Q}
    (hu : u ∈ UplusBin hQW) {s : ℕ} (hus : u ^ 2 ^ s = 1) (w : fixedSpace xe) :
    pairMap Q (g * u * g⁻¹) (w : Fin d → K) = pairMap Q u (w : Fin d → K) := by
  obtain ⟨hFx, ⟨j, hσ, c₀, hc₀⟩, -⟩ := hgood
  obtain ⟨hu1, c, y, hy, hcy⟩ := hu
  have hUP : u ∈ UP Q xe := hu1.1
  obtain ⟨μ, hμ⟩ := exists_pairMap_sim Q g
  have hN : Odd (p ^ j) := hp2.pow
  have : Nontrivial (fixedSpace xe) := Module.nontrivial_of_finrank_pos (R := K) (by omega)
  obtain ⟨w₀, hw₀⟩ := exists_map_ne_zero hQW
  have hiter : ∀ (m : ℕ) (w : fixedSpace xe), (pairMap Q u)^[m] (w : Fin d → K) =
      ((c : K) ^ m) • (((y ^ m) w : fixedSpace xe) : Fin d → K) := by
    intro m
    induction m with
    | zero => intro w; simp
    | succ m ih =>
      intro w
      rw [Function.iterate_succ_apply', ih w, pairMap_smul_of_right Q hUP.1, hcy ((y ^ m) w),
        smul_smul, pow_succ (c : K) m, pow_succ' y m, LinearEquiv.mul_apply]
  have hid : ∀ v, (pairMap Q u)^[2 ^ s] v = v := fun v => by
    rw [← pairMap_pow, hus, pairMap_one]
  have hw : ∀ w : fixedSpace xe, ((c : K) ^ 2 ^ s) • (((y ^ 2 ^ s) w : fixedSpace xe) :
      Fin d → K) = (w : Fin d → K) := fun w => by rw [← hiter, hid]
  have hIso := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    (rotGroup_le_orthogonalGroup hQW (Subgroup.pow_mem _ hy (2 ^ s)))
  have hcc : (c : K) ^ 2 ^ s * (c : K) ^ 2 ^ s = 1 := by
    have h1 := congrArg Q (hw w₀)
    rw [QuadraticMap.map_smul, smul_eq_mul] at h1
    have h2 : Q (((y ^ 2 ^ s) w₀ : fixedSpace xe) : Fin d → K) = Q (w₀ : Fin d → K) := hIso w₀
    rw [h2] at h1
    have hQ0 : Q (w₀ : Fin d → K) ≠ 0 := hw₀
    exact mul_right_cancel₀ hQ0 (by rw [h1, one_mul])
  have hc2 : (c : K) ^ 2 ^ (s + 1) = 1 := by
    rw [pow_succ, pow_mul, sq]
    exact hcc
  have hy2 : y ^ 2 ^ (s + 1) = 1 := by
    rw [pow_succ, pow_mul, sq]
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    calc (((y ^ 2 ^ s * y ^ 2 ^ s) w : fixedSpace xe) : Fin d → K)
        = (((c : K) ^ 2 ^ s * (c : K) ^ 2 ^ s) •
          (((y ^ 2 ^ s) ((y ^ 2 ^ s) w) : fixedSpace xe) : Fin d → K)) := by
          rw [hcc, one_smul]
          rfl
      _ = ((c : K) ^ 2 ^ s) • (((c : K) ^ 2 ^ s) •
          (((y ^ 2 ^ s) ((y ^ 2 ^ s) w) : fixedSpace xe) : Fin d → K)) := (smul_smul _ _ _).symm
      _ = ((c : K) ^ 2 ^ s) • (((y ^ 2 ^ s) w : fixedSpace xe) : Fin d → K) := by
          rw [hw ((y ^ 2 ^ s) w)]
      _ = (w : Fin d → K) := hw w
  have hτ : ∀ x : K, ((g.val.right : K →+* K).toMonoidHom)^[p ^ j] x = x := fun x => by
    have := ringEquiv_pow_apply g.val.right (p ^ j) x
    rw [hσ] at this
    exact this.symm
  have hσc : g.val.right (c : K) = c :=
    KCMatrixAlgebra.monoidHom_apply_eq_of_pow_two_pow_eq_one
      ((g.val.right : K →+* K).toMonoidHom) hN hτ hc2
  have hFW := restrictPair_smul g hFx
  have hFWQ := restrictPair_sim g hFx hμ
  have hc₀W : ∀ w : fixedSpace xe, (restrictPair g hFx)^[p ^ j] w = c₀ • w := fun w =>
    Subtype.ext (by rw [coe_restrictPair_iterate, hc₀]; rfl)
  have hτy : semilinConj (restrictPair g hFx) g.val.right hFW y = y :=
    apply_eq_of_pow_two_pow_eq_one (rotGroup (Q.comp (fixedSpace xe).subtype) hQW)
      (fun a ha b hb => commute_of_mem_rotGroup hdim ha hb)
      (semilinConj (restrictPair g hFx) g.val.right hFW)
      (fun z hz => semilinConj_mem_rotGroup hdim (restrictPair g hFx) g.val.right hFW μ hFWQ hz)
      hN (fun z _ => iterate_semilinConj_eq_self (restrictPair g hFx) g.val.right hFW hc₀W z)
      (fun z hz hzz => by
        rcases eq_one_or_eq_neg_of_sq hdim hz hzz with h1 | h1
        · rw [h1, map_one]
        · refine LinearEquiv.ext fun w => ?_
          rw [semilinConj_apply, h1, h1, map_neg, AddEquiv.apply_symm_apply])
      (s + 1) y hy hy2
  rw [pairMap_conj_apply_fixed g u hFx hcy w, hτy, hσc, hcy w]

theorem kappa_conj_eq_of_mem_UplusBin (hx : OddOrderIsometry Q p xe) (hp : p.Prime)
    (hp3 : 3 < p) (hdim : finrank K (fixedSpace xe) = 2)
    {hQW : (QuadraticMap.polarBilin (Q.comp (fixedSpace xe).subtype)).Nondegenerate}
    {g : similarityPairs Q} (hgood : GoodPair Q xe p g) {u : similarityPairs Q}
    (hu : u ∈ UplusBin hQW) {s : ℕ} (hus : u ^ 2 ^ s = 1) :
    kappa Q (g * u * g⁻¹) = kappa Q u := by
  have hp2 : Odd p := hp.odd_of_ne_two (by omega)
  have hgood' := hgood
  obtain ⟨hFx, ⟨j, hσ, c₀, hc₀⟩, hfix⟩ := hgood
  have hUP : u ∈ UP Q xe := hu.1.1
  have hUPconj : g * u * g⁻¹ ∈ UP Q xe := conj_mem_UP Q hx hp hp3 g hFx hfix hUP
  have hMs : linOf Q u hUP.1 ^ 2 ^ s = 1 := by
    refine LinearEquiv.ext fun v => ?_
    rw [linOf_pow_apply, ← pairMap_pow, hus, pairMap_one]
    rfl
  have hlin : (linOf Q (g * u * g⁻¹) hUPconj.1).toLinearMap = (linOf Q u hUP.1).toLinearMap := by
    refine ext_primaryComponent hx.squarefree_minpoly fun h hh v hv => ?_
    by_cases hne1 : h = X - 1
    · subst hne1
      have hvW : v ∈ fixedSpace xe := by
        rw [fixedSpace_eq_primaryComponent (x := xe)]
        exact hv
      exact pairMap_conj_apply_fixed_of_pow hdim hgood' hp2 hu hus ⟨v, hvW⟩
    · have := semilinConj_apply_eq_of_blockScalar hx.squarefree_minpoly (pairMap_smul Q g) hFx
        (hp2.pow : Odd (p ^ j)) hσ hh (hfix h hh)
        (blockScalar_of_mem_UP_ne Q hx hp hp3 hUP hh hne1) hMs hv
      change pairMap Q (g * u * g⁻¹) v = pairMap Q u v
      rw [pairMap_mul, pairMap_mul, pairMap_inv]
      exact this
  exact kappa_congr Q fun v => LinearMap.congr_fun hlin v

noncomputable def plusDataOfTwo (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p)
    (hdim : finrank K (fixedSpace xe) = 2) : PlusData Q xe p where
  Uplus := UplusBin hx.polarBilin_fixed_nondegenerate
  le := fun _ hu => hu.1.1
  index := by
    have h4 := relIndex_UplusBin_le hx.polarBilin_fixed_nondegenerate
    have hp4 : 4 < p := by
      by_contra hlt
      have h4 : p = 4 := by omega
      rw [h4] at hp
      exact absurd hp (by norm_num)
    exact lt_of_le_of_lt h4 hp4
  comm := fun _ hu _ hu' => kappa_comm_of_mem_UplusBin hx hp hp3 hdim hu hu'
  conj := fun _ hg _ hu => mem_UplusBin_conj hx hp hp3 hdim hg hu
  fix2 := fun _ hg _ hu hs => by
    obtain ⟨s, hs⟩ := hs
    exact kappa_conj_eq_of_mem_UplusBin hx hp hp3 hdim hg hu hs

theorem nonempty_plusData (hx : OddOrderIsometry Q p xe) (hp : p.Prime) (hp3 : 3 < p) :
    Nonempty (PlusData Q xe p) := by
  by_cases h2 : finrank K (fixedSpace xe) = 2
  · exact ⟨plusDataOfTwo hx hp hp3 h2⟩
  · exact ⟨plusDataOfNeTwo Q hx hp hp3 h2⟩

end Conj

end CFSG.RankThree.PartOne.KCOrthComm
