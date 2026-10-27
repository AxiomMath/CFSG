module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.LocalAnalysis.StandardType.GGTwE6CorootCoreFrame

public section

namespace CFSG.StandardType

namespace ExcE6Plus

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TwE6CorootCore CFSG.StandardType.TableBExcTwo
  CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE

private lemma ggKGE6b_HSL_mul {F : Type} [Field F] (s t : Fˣ) :
    HSL (s * t) = HSL s * HSL t := by
  ext i j
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_HSL, coe_HSL, coe_HSL]
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Units.val_mul, mul_inv_rev, mul_comm]

private lemma ggKGE6b_units_map_fr_eq_inv
    {K L : Type} [Field L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (t : Lˣ) (ht : t ^ (Nat.card K + 1) = 1) :
    Units.map Fr.toMonoidHom t = t⁻¹ := by
  refine Units.ext ?_
  rw [Units.coe_map, Units.val_inv_eq_inv_val]
  rw [show Fr.toMonoidHom (t : L) = Fr (t : L) from rfl, hFr]
  have htL : (t : L) ^ (Nat.card K + 1) = 1 := by
    rw [← Units.val_pow_eq_pow_val, ht, Units.val_one]
  rw [pow_succ] at htL
  exact eq_inv_of_mul_eq_one_left htL

private lemma ggKGE6b_map_conj_HSL_fixed
    {K L : Type} [Field L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (g₀ : SL2 L)
    (hg₀ : Matrix.SpecialLinearGroup.map Fr g₀ = g₀ * nSL (1 : Lˣ))
    (t : Lˣ) (ht : t ^ (Nat.card K + 1) = 1) :
    Matrix.SpecialLinearGroup.map Fr (g₀ * HSL t * g₀⁻¹) = g₀ * HSL t * g₀⁻¹ := by
  rw [map_mul, map_mul, map_inv, hg₀, map_HSL, ggKGE6b_units_map_fr_eq_inv Fr hFr t ht,
    nSL_one]
  have h2 : WSL * HSL t⁻¹ * WSL⁻¹ = HSL t := by
    rw [WSL_mul_HSL, inv_inv, mul_assoc, mul_inv_cancel, mul_one]
  rw [mul_inv_rev,
    show g₀ * WSL * HSL t⁻¹ * (WSL⁻¹ * g₀⁻¹) =
      g₀ * (WSL * HSL t⁻¹ * WSL⁻¹) * g₀⁻¹ by group,
    h2]

private lemma ggKGE6b_exists_SL2_map_eq
    {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (g₀ : SL2 L)
    (hg₀ : Matrix.SpecialLinearGroup.map Fr g₀ = g₀ * nSL (1 : Lˣ))
    (t : Lˣ) (ht : t ^ (Nat.card K + 1) = 1) :
    ∃ B : SL2 K, Matrix.SpecialLinearGroup.map (algebraMap K L) B = g₀ * HSL t * g₀⁻¹ := by
  refine SeitzReduction.E6Pilot.exists_specialLinearGroup_map_eq_of_map_eq
    (algebraMap K L) Fr ?_ (g₀ * HSL t * g₀⁻¹)
    (ggKGE6b_map_conj_HSL_fixed Fr hFr g₀ hg₀ t ht)
  intro x
  rw [hFr x]
  exact TauCeti.FiniteField.pow_natCard_eq_self_iff_mem_range_algebraMap x

private lemma ggKGE6b_rootTorusSL2_torusRootChar
    {L : Type} [Field L] {β γ : Fin Tag.E6.rank → ℤ}
    (hβ : IsRoot Tag.E6 β) (hγ : IsRoot Tag.E6 γ) (c : Lˣ) :
    torusRootChar (rootTorusSL2 Tag.E6 L β c) γ =
      ((c ^ CFSG.LieType.Steinberg.Adjoint.iform β γ : Lˣ) : L) := by
  have hββ : CFSG.LieType.Steinberg.Adjoint.iform β β = 2 :=
    TableBExcTwo.iform_self_eq_two_of_isRoot corootFrame.symm_one hβ
  obtain ⟨-, hev⟩ :=
    (exceptional_Lang_root_rank_one_torus_transport Tag.E6 L hβ).2.2.2.2.1 c
  have h := hev γ hγ
  rw [hββ] at h
  have h2 : (2 : ℤ) * CFSG.LieType.Steinberg.Adjoint.iform β γ / 2 =
      CFSG.LieType.Steinberg.Adjoint.iform β γ := by
    rw [show (2 : ℤ) * CFSG.LieType.Steinberg.Adjoint.iform β γ =
      CFSG.LieType.Steinberg.Adjoint.iform β γ * 2 by ring]
    exact Int.mul_ediv_cancel (CFSG.LieType.Steinberg.Adjoint.iform β γ) (by norm_num : (2:ℤ) ≠ 0)
  rw [h2] at h
  exact torusRootChar_eq_of_apply hγ h

private lemma ggKGE6b_torusRootChar_list_prod
    {τ : Tag} {L : Type} [Field L]
    (l : List (ModGL τ L)) :
    (∀ x ∈ l, x ∈ torusGroup τ L) →
      ∀ α : Fin τ.rank → ℤ,
        torusRootChar l.prod α = (l.map fun x => torusRootChar x α).prod := by
  induction l with
  | nil => intro _ α; simp [torusRootChar_one]
  | cons x xs ih =>
    intro hl α
    have hx : x ∈ torusGroup τ L := hl x (by simp)
    have hxs : xs.prod ∈ torusGroup τ L :=
      Subgroup.list_prod_mem _ (fun y hy => hl y (by simp [hy]))
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      torusRootChar_mul (torusGroup_le_diagonalGroup hx) (torusGroup_le_diagonalGroup hxs),
      ih (fun y hy => hl y (by simp [hy])) α]

private lemma ggKGE6b_conj_list_prod {G : Type*} [Group G] (z : G) (l : List G) :
    z⁻¹ * l.prod * z = (l.map fun x => z⁻¹ * x * z).prod := by
  induction l with
  | nil => simp
  | cons x xs ih =>
    rw [List.prod_cons, List.map_cons, List.prod_cons,
      show z⁻¹ * (x * xs.prod) * z = (z⁻¹ * x * z) * (z⁻¹ * xs.prod * z) by group]
    rw [ih]

theorem exists_sylow_conj_le_torus
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (g₀ : SL2 (AlgebraicClosure K))
    (hg₀ : Matrix.SpecialLinearGroup.map Fr g₀ = g₀ * nSL (1 : (AlgebraicClosure K)ˣ)) :
    ∃ P : Subgroup (adjointGroup .E6 K),
      IsPGroup p P ∧ Nat.card P = p ^ (4 * padicValNat p (Nat.card K + 1)) ∧
      ∀ x ∈ P,
        (frameProd (AlgebraicClosure K) corootFrame g₀ : ModGL .E6 (AlgebraicClosure K))⁻¹ *
            baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) *
            (frameProd (AlgebraicClosure K) corootFrame g₀ : ModGL .E6 (AlgebraicClosure K)) ∈
          twistedTorusOf
            (frameProd (AlgebraicClosure K) corootFrame (nSL (1 : (AlgebraicClosure K)ˣ)) :
              ModGL .E6 (AlgebraicClosure K)) (Units.map (entrywiseHom Fr)) := by

  classical
  haveI : Fintype K := Fintype.ofFinite K
  let L := AlgebraicClosure K
  set a := padicValNat p (Nat.card K + 1) with ha
  haveI : NeZero (p ^ a) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hp_not_dvd : ¬ 2 ∣ p := by
    obtain ⟨k, hk⟩ := hp.odd_of_ne_two hp2
    rintro ⟨j, hj⟩
    omega
  haveI : NeZero ((p : L)) := ⟨by
    rw [Ne, CharP.cast_eq_zero_iff L 2]
    exact hp_not_dvd⟩
  haveI : NeZero (((p ^ a : ℕ)) : L) := ⟨by
    rw [Nat.cast_pow]
    exact pow_ne_zero _ (NeZero.ne (p : L))⟩
  have hpq' : p ^ a ∣ Nat.card K + 1 := by rw [ha]; exact pow_padicValNat_dvd
  let V := rootsOfUnity (p ^ a) L
  have hcardV : Nat.card V = p ^ a :=
    HasEnoughRootsOfUnity.natCard_rootsOfUnity L (p ^ a)
  have ht_mem : ∀ t : V, (t : Lˣ) ^ (p ^ a) = 1 := fun t => (mem_rootsOfUnity _ _).mp t.2
  have ht_q : ∀ t : V, (t : Lˣ) ^ (Nat.card K + 1) = 1 := by
    intro t
    obtain ⟨k, hk⟩ := hpq'
    rw [hk, pow_mul, ht_mem t, one_pow]
  have hBex : ∀ t : V, ∃ B : SL2 K,
      Matrix.SpecialLinearGroup.map (algebraMap K L) B = g₀ * HSL (t : Lˣ) * g₀⁻¹ := fun t =>
    ggKGE6b_exists_SL2_map_eq Fr hFr g₀ hg₀ (t : Lˣ) (ht_q t)
  let B : V → SL2 K := fun t => Classical.choose (hBex t)
  have hBspec : ∀ t : V,
      Matrix.SpecialLinearGroup.map (algebraMap K L) (B t) = g₀ * HSL (t : Lˣ) * g₀⁻¹ :=
    fun t => Classical.choose_spec (hBex t)
  have hmap_inj : Function.Injective
      (Matrix.SpecialLinearGroup.map (algebraMap K L) : SL2 K → SL2 L) := by
    intro A B' h
    ext i j
    have h2 : algebraMap K L (A.1 i j) = algebraMap K L (B'.1 i j) := by
      have := congrArg (fun g : SL2 L => (g : Matrix (Fin 2) (Fin 2) L) i j) h
      simpa [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.map_apply] using this
    exact (algebraMap K L).injective h2
  have hB_one : B 1 = 1 := by
    apply hmap_inj
    rw [hBspec, Subgroup.coe_one, HSL_one, map_one]
    group
  have hB_mul : ∀ s t : V, B (s * t) = B s * B t := by
    intro s t
    apply hmap_inj
    rw [map_mul, hBspec, hBspec, hBspec, Subgroup.coe_mul, ggKGE6b_HSL_mul]
    group
  let Bhom : V →* SL2 K :=
    { toFun := B, map_one' := hB_one, map_mul' := hB_mul }
  let Ψ : (Fin 4 → V) →* adjointGroup .E6 K :=
    { toFun := fun t => (List.ofFn fun i : Fin 4 => rho K corootFrame i (B (t i))).prod
      map_one' := by
        simp only [Pi.one_apply, hB_one, map_one, List.ofFn_const, List.prod_replicate]
        simp
      map_mul' := by
        intro s t
        have hfun : (fun i : Fin 4 => rho K corootFrame i (B ((s * t) i))) =
            (fun i : Fin 4 =>
              rho K corootFrame i (B (s i)) * rho K corootFrame i (B (t i))) := by
          funext i
          rw [Pi.mul_apply, hB_mul, map_mul]
        rw [hfun]
        exact list_prod_ofFn_mul_of_ne _ _
          (fun i j hij => commute_rho corootFrame hij _ _) }
  let gAdj : adjointGroup .E6 L := frameProd L corootFrame g₀
  let nFAdj : adjointGroup .E6 L := frameProd L corootFrame (nSL (1 : Lˣ))
  let gM : ModGL .E6 L := gAdj
  let nFM : ModGL .E6 L := nFAdj
  let Q : (Fin 4 → V) → ModGL .E6 L := fun t =>
    (List.ofFn fun i : Fin 4 => rootTorusSL2 .E6 L (corootFrame.root i) (t i : Lˣ)).prod
  have hbc : ∀ t : Fin 4 → V,
      baseChangeGL (algebraMap K L) ((Ψ t : ModGL .E6 K)) =
      (List.ofFn fun i : Fin 4 => rootSL2 .E6 L (corootFrame.root i)
        (g₀ * HSL (t i : Lˣ) * g₀⁻¹)).prod := by
    intro t
    change baseChangeGL (algebraMap K L)
      (((List.ofFn fun i : Fin 4 => rho K corootFrame i (B (t i))).prod :
        adjointGroup .E6 K) : ModGL .E6 K) = _
    rw [SubmonoidClass.coe_list_prod, MonoidHom.map_list_prod, List.map_map, List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    change baseChangeGL (algebraMap K L)
      (((rho K corootFrame i (B (t i)) : adjointGroup .E6 K)) : ModGL .E6 K) =
      rootSL2 .E6 L (corootFrame.root i) (g₀ * HSL (t i : Lˣ) * g₀⁻¹)
    rw [← coe_adjointMap, adjointMap_rho, hBspec, coe_rho]
  have hf1 : frameProd L corootFrame (1 : SL2 L) = 1 := by
    simp [frameProd]
  have hgM_inv : ((frameProd L corootFrame g₀⁻¹ : adjointGroup .E6 L) : ModGL .E6 L) =
      gM⁻¹ := by
    have h := frameProd_mul (L := L) corootFrame g₀ g₀⁻¹
    rw [mul_inv_cancel, hf1] at h
    have h2 : frameProd L corootFrame g₀⁻¹ = (frameProd L corootFrame g₀)⁻¹ := by
      have hh : frameProd L corootFrame g₀ * frameProd L corootFrame g₀⁻¹ = 1 := h.symm
      have := congrArg (fun z => (frameProd L corootFrame g₀)⁻¹ * z) hh
      simpa [mul_assoc] using this
    rw [h2, Subgroup.coe_inv]
  have hconj_factor : ∀ t : Fin 4 → V, ∀ i : Fin 4,
      gM⁻¹ * rootSL2 .E6 L (corootFrame.root i) (g₀ * HSL (t i : Lˣ) * g₀⁻¹) * gM =
      rootTorusSL2 .E6 L (corootFrame.root i) (t i : Lˣ) := by
    intro t i
    have h := frameProd_mul_rootSL2 (L := L) corootFrame i (g₀⁻¹) (HSL (t i : Lˣ))
    rw [inv_inv] at h
    rw [hgM_inv] at h
    have h2 := congrArg (fun z : ModGL .E6 L => z * gM) h
    have h3 : (rootSL2 .E6 L (corootFrame.root i) (HSL (t i : Lˣ)) * gM⁻¹) * gM =
        rootTorusSL2 .E6 L (corootFrame.root i) (t i : Lˣ) := by
      rw [mul_assoc, inv_mul_cancel, mul_one]
      rfl
    rw [h3] at h2
    exact h2
  have hQ : ∀ t : Fin 4 → V,
      gM⁻¹ * (List.ofFn fun i : Fin 4 => rootSL2 .E6 L (corootFrame.root i)
        (g₀ * HSL (t i : Lˣ) * g₀⁻¹)).prod * gM = Q t := by
    intro t
    rw [ggKGE6b_conj_list_prod gM (List.ofFn fun i : Fin 4 =>
      rootSL2 .E6 L (corootFrame.root i) (g₀ * HSL (t i : Lˣ) * g₀⁻¹)), List.map_ofFn]
    refine congrArg List.prod (congrArg List.ofFn (funext fun i => ?_))
    exact hconj_factor t i
  have hconj : ∀ t : Fin 4 → V,
      gM⁻¹ * baseChangeGL (algebraMap K L) ((Ψ t : ModGL .E6 K)) * gM = Q t := by
    intro t
    rw [hbc t, hQ t]
  have hQ_torus : ∀ t : Fin 4 → V, Q t ∈ torusGroup .E6 L := by
    intro t
    dsimp only [Q]
    refine Subgroup.list_prod_mem _ (fun x hx => ?_)
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact (exceptional_Lang_root_rank_one_torus_transport .E6 L
      (corootFrame.isRoot i)).2.1 (t i : Lˣ)
  have hΦg : Units.map (entrywiseHom Fr) gM = gM * nFM := by
    dsimp only [gM, nFM, gAdj, nFAdj]
    rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self, ← coe_adjointMap,
      adjointMap_frameProd, hg₀, frameProd_mul, Subgroup.coe_mul]
  have hΦx : ∀ x : adjointGroup .E6 K,
      Units.map (entrywiseHom Fr) (baseChangeGL (algebraMap K L) (x : ModGL .E6 K)) =
      baseChangeGL (algebraMap K L) (x : ModGL .E6 K) := by
    intro x
    rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL]
    have hcomp : Fr.comp (algebraMap K L) = algebraMap K L := by
      ext c
      rw [RingHom.comp_apply, hFr, ← map_pow, Nat.card_eq_fintype_card, FiniteField.pow_card]
    rw [hcomp]
  have htw : ∀ t : Fin 4 → V,
      nFM * Units.map (entrywiseHom Fr)
          (gM⁻¹ * baseChangeGL (algebraMap K L) ((Ψ t : ModGL .E6 K)) * gM) * nFM⁻¹ =
      gM⁻¹ * baseChangeGL (algebraMap K L) ((Ψ t : ModGL .E6 K)) * gM := by
    intro t
    rw [map_mul, map_mul, map_inv, hΦg, hΦx (Ψ t)]
    group
  have hchar : ∀ t : Fin 4 → V, ∀ j : Fin 4,
      torusRootChar (Q t) (corootFrame.root j) =
      (((t j : Lˣ) ^ (2 : ℤ) : Lˣ) : L) := by
    intro t j
    dsimp only [Q]
    have hmem : ∀ x ∈ (List.ofFn fun i : Fin 4 =>
        rootTorusSL2 .E6 L (corootFrame.root i) (t i : Lˣ)),
        x ∈ torusGroup .E6 L := by
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
      exact (exceptional_Lang_root_rank_one_torus_transport .E6 L
        (corootFrame.isRoot i)).2.1 _
    rw [ggKGE6b_torusRootChar_list_prod _ hmem (corootFrame.root j), List.map_ofFn]
    change (List.ofFn fun i : Fin 4 => torusRootChar
      (rootTorusSL2 .E6 L (corootFrame.root i) (t i : Lˣ)) (corootFrame.root j)).prod =
      (((t j : Lˣ) ^ (2 : ℤ) : Lˣ) : L)
    rw [List.prod_ofFn, Finset.prod_eq_single j]
    · rw [ggKGE6b_rootTorusSL2_torusRootChar (corootFrame.isRoot j)
        (corootFrame.isRoot j) (t j : Lˣ),
        TableBExcTwo.iform_self_eq_two_of_isRoot corootFrame.symm_one (corootFrame.isRoot j)]
    · intro i _ hij
      rw [ggKGE6b_rootTorusSL2_torusRootChar (corootFrame.isRoot i)
        (corootFrame.isRoot j) (t i : Lˣ), corootFrame.orth i j hij]
      simp
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hker : ∀ t : Fin 4 → V, Ψ t = 1 → t = 1 := by
    intro t ht
    have hQ1 : Q t = 1 := by
      rw [← hconj t, ht]
      simp
    have htj : ∀ j : Fin 4, t j = 1 := by
      intro j
      have h1 := hchar t j
      rw [hQ1, torusRootChar_one] at h1
      have h2 : ((t j : Lˣ) : L) ^ 2 = 1 := h1.symm
      rcases (sq_eq_one_iff.mp h2) with h | h
      · exact Subtype.ext (Units.ext h)
      · rw [CharTwo.neg_eq] at h
        exact Subtype.ext (Units.ext h)
    funext j
    exact htj j
  have hΨ_inj : Function.Injective Ψ := by
    intro s t hst
    have h1 : s⁻¹ * t = 1 := by
      apply hker (s⁻¹ * t)
      rw [map_mul, map_inv, hst, inv_mul_cancel]
    have h2 : s * (s⁻¹ * t) = s * 1 := by rw [h1]
    rw [← mul_assoc, mul_inv_cancel, one_mul, mul_one] at h2
    exact h2.symm
  let P : Subgroup (adjointGroup .E6 K) := Ψ.range
  have hcardP : Nat.card P = p ^ (4 * a) := by
    have h1 : Nat.card (Fin 4 → V) = (p ^ a) ^ 4 := by
      rw [Nat.card_fun, hcardV, Nat.card_fin]
    have h2 : Nat.card (Fin 4 → V) = Nat.card P := by
      dsimp only [P]
      exact Nat.card_congr (Equiv.ofInjective Ψ hΨ_inj)
    calc Nat.card P = Nat.card (Fin 4 → V) := h2.symm
      _ = (p ^ a) ^ 4 := h1
      _ = p ^ (a * 4) := (pow_mul p a 4).symm
      _ = p ^ (4 * a) := by rw [Nat.mul_comm]
  have hPgroup : IsPGroup p P := IsPGroup.of_card (n := 4 * a) hcardP
  refine ⟨P, hPgroup, hcardP, ?_⟩
  intro x hx
  change x ∈ Ψ.range at hx
  obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
  rw [mem_twistedTorusOf]
  refine ⟨?_, ?_⟩
  · change gM⁻¹ * baseChangeGL (algebraMap K L) ((Ψ t : ModGL .E6 K)) * gM ∈ torusGroup .E6 L
    rw [hconj t]
    exact hQ_torus t
  · change nFM * Units.map (entrywiseHom Fr)
        (gM⁻¹ * baseChangeGL (algebraMap K L) ((Ψ t : ModGL .E6 K)) * gM) * nFM⁻¹ =
      gM⁻¹ * baseChangeGL (algebraMap K L) ((Ψ t : ModGL .E6 K)) * gM
    exact htw t


end ExcE6Plus

end CFSG.StandardType

end
