module

public import CFSG.RankThree.PartOne.SEITZ6.G2Defs
public import CFSG.RankThree.PartOne.SEITZ6.G2Close

public section

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.SEITZ3

variable {K : Type} [Field K]

theorem smul_eq_end (g : adjointGroup .G2 K) (x : RootModule .G2 K) :
    g • x = ((g : ModGL .G2 K) : Module.End K (RootModule .G2 K)) x := rfl

theorem smul_smul_comm (g : adjointGroup .G2 K) (c : K) (x : RootModule .G2 K) :
    g • (c • x) = c • (g • x) := by
  simp only [smul_eq_end, map_smul]

theorem height_labelWt_bounds (a : Label .G2) :
    -5 ≤ height (labelWt .G2 a) ∧ height (labelWt .G2 a) ≤ 5 := by
  rcases a with l | ⟨γ, hγ⟩
  · simp [labelWt, height]
  · obtain ⟨p, hp, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
    have : ∀ p < 12, -5 ≤ height (τ := .G2) (rt p) ∧ height (τ := .G2) (rt p) ≤ 5 := by
      decide +kernel
    exact this p (by rw [len_roots] at hp; exact hp)

theorem height_add {τ : Tag} (v w : Fin τ.rank → ℤ) : height (v + w) = height v + height w := by
  simp [height, Finset.sum_add_distrib]

theorem height_nsmul {τ : Tag} (k : ℕ) (v : Fin τ.rank → ℤ) : height (k • v) = k * height v := by
  simp [height, ← Finset.mul_sum]

theorem posRoot_fix {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ)
    (hpos : 0 < height γ) (c : K) :
    xPar (rootOperatorFamily .G2) γ c • rootVec .G2 K (rt 7) = rootVec .G2 K (rt 7) ∧
      ∀ x : RootModule .G2 K,
        coordAt (rt 10) (xPar (rootOperatorFamily .G2) γ c • x) = coordAt (rt 10) x := by
  set F := rootOperatorFamily .G2
  have h7 : IsRoot .G2 (rt 7) := isRoot_rt (by norm_num)
  have h10 : IsRoot .G2 (rt 10) := isRoot_rt (by norm_num)
  have e : ∀ x : RootModule .G2 K, xPar F γ c • x = F.elt K ⟨γ, hγ⟩ c x := fun x => by
    rw [xPar_of_isRoot hγ]
    rfl
  have ht7 : height (τ := .G2) (rt 7) = 5 := by decide +kernel
  have ht10 : height (τ := .G2) (rt 10) = -5 := by decide +kernel
  constructor
  · rw [e, rootVec_eq_single h7]
    refine Finsupp.ext fun a => ?_
    by_contra hne
    obtain ⟨k, hk, hwt⟩ := F.elt_weight_shift ⟨γ, hγ⟩ c a _ (sub_ne_zero.2 hne)
    have h1 := congrArg height hwt
    rw [height_add, height_nsmul] at h1
    change height (labelWt .G2 a) = height (τ := .G2) (rt 7) + k * height γ at h1
    rw [ht7] at h1
    have : (1 : ℤ) ≤ k := by exact_mod_cast hk
    nlinarith [this, hpos, (height_labelWt_bounds a).2]
  · intro x
    rw [e, coordAt_eq h10, coordAt_eq h10]
    induction x using Finsupp.induction_linear with
    | zero => simp
    | add x y hx hy => rw [map_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply]
    | single b r =>
      rw [← Finsupp.smul_single_one, map_smul, Finsupp.smul_apply, Finsupp.smul_apply]
      congr 1
      by_contra hne
      obtain ⟨k, hk, hwt⟩ := F.elt_weight_shift ⟨γ, hγ⟩ c _ b (sub_ne_zero.2 hne)
      have h1 := congrArg height hwt
      rw [height_add, height_nsmul] at h1
      change height (τ := .G2) (rt 10) = height (labelWt .G2 b) + k * height γ at h1
      rw [ht10] at h1
      have : (1 : ℤ) ≤ k := by exact_mod_cast hk
      nlinarith [this, hpos, (height_labelWt_bounds b).1]

@[expose] def omega7 (K : Type) [Field K] : Subgroup (adjointGroup .G2 K) where
  carrier := {b | ∃ χ : Kˣ, b • rootVec .G2 K (rt 7) = (χ : K) • rootVec .G2 K (rt 7) ∧
      (∀ x : RootModule .G2 K, coordAt (rt 10) (b • x) = ((χ⁻¹ : Kˣ) : K) * coordAt (rt 10) x) ∧
      (∀ c : K, b * xp 7 c * b⁻¹ = xp 7 ((χ : K) * c))}
  mul_mem' := by
    rintro a b ⟨χ₁, a1, b1, c1⟩ ⟨χ₂, a2, b2, c2⟩
    refine ⟨χ₁ * χ₂, ?_, ?_, ?_⟩
    · rw [mul_smul, a2, smul_smul_comm, a1, smul_smul, Units.val_mul, mul_comm]
    · intro x
      rw [mul_smul, b1, b2, mul_inv, Units.val_mul, mul_assoc]
    · intro c
      rw [show a * b * xp 7 c * (a * b)⁻¹ = a * (b * xp 7 c * b⁻¹) * a⁻¹ by group, c2, c1,
        Units.val_mul, mul_assoc]
  one_mem' := by
    refine ⟨1, ?_, ?_, ?_⟩
    · simp
    · intro x; simp
    · intro c; simp
  inv_mem' := by
    rintro a ⟨χ, a1, b1, c1⟩
    refine ⟨χ⁻¹, ?_, ?_, ?_⟩
    · have h : rootVec .G2 K (rt 7) = (χ : K) • (a⁻¹ • rootVec .G2 K (rt 7)) := by
        have := congrArg (fun y => a⁻¹ • y) a1
        simpa [smul_smul_comm] using this
      calc a⁻¹ • rootVec .G2 K (rt 7)
          = ((χ⁻¹ : Kˣ) : K) • ((χ : K) • (a⁻¹ • rootVec .G2 K (rt 7))) := by
            rw [smul_smul, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_smul]
        _ = ((χ⁻¹ : Kˣ) : K) • rootVec .G2 K (rt 7) := by rw [← h]
    · intro x
      have h := b1 (a⁻¹ • x)
      rw [smul_inv_smul] at h
      rw [inv_inv]
      calc coordAt (rt 10) (a⁻¹ • x)
          = (χ : K) * (((χ⁻¹ : Kˣ) : K) * coordAt (rt 10) (a⁻¹ • x)) := by
            rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul]
        _ = (χ : K) * coordAt (rt 10) x := by rw [← h]
    · intro c
      have h := c1 (((χ⁻¹ : Kˣ) : K) * c)
      rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h
      rw [inv_inv]
      calc a⁻¹ * xp 7 c * a = a⁻¹ * (a * xp 7 (((χ⁻¹ : Kˣ) : K) * c) * a⁻¹) * a := by rw [h]
        _ = xp 7 (((χ⁻¹ : Kˣ) : K) * c) := by group

theorem rt10_eq_neg : rt 10 = -rt 7 := by
  ext i; fin_cases i <;> decide

theorem torus_mem_omega7 (i : Fin (Tag.rank .G2)) (s : Kˣ) :
    torusElement .G2 K i s ∈ omega7 K := by
  have h7 : IsRoot .G2 (rt 7) := isRoot_rt (by norm_num)
  have h10 : IsRoot .G2 (rt 10) := isRoot_rt (by norm_num)
  set e : ℤ := ∑ j, (Tag.G2).cartan i j * (rt 7) j with he
  have hneg : (∑ j, (Tag.G2).cartan i j * (rt 10) j) = -e := by
    rw [he, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [rt10_eq_neg]
    change _ * (-(rt 7 j)) = -(_ * rt 7 j)
    ring
  refine ⟨s ^ e, ?_, ?_, ?_⟩
  · exact torusElt_rootVec i s h7
  · intro x
    rw [coordAt_eq h10, coordAt_eq h10]
    change (torusElt .G2 K i s : Module.End K (RootModule .G2 K)) x _ = _
    rw [torusElt_apply]
    change ((s ^ (∑ j, (Tag.G2).cartan i j * (rt 10) j) : Kˣ) : K) * _ = _
    rw [hneg, zpow_neg]
  · intro c
    have := (rootOperatorFamily .G2).torusElement_mul_eltElement_mul_inv (K := K) i s ⟨rt 7, h7⟩ c
    simpa [xp, xPar_of_isRoot h7] using this

theorem posRoot_mem_omega7 {γ : Fin (Tag.rank .G2) → ℤ} (hγ : IsRoot .G2 γ)
    (hpos : 0 < height γ) (c : K) :
    xPar (rootOperatorFamily .G2) γ c ∈ omega7 K := by
  obtain ⟨h1, h2⟩ := posRoot_fix (K := K) hγ hpos c
  refine ⟨1, ?_, ?_, ?_⟩
  · simpa using h1
  · intro x
    simpa using h2 x
  · intro c'
    obtain ⟨p, hp, rfl⟩ := RootCertificate.exists_root_eq (Tag.rootCertificate_check .G2) hγ
    have hp12 : p < 12 := by rwa [len_roots] at hp
    have hpmem : p ∈ ({0, 1, 3, 4, 7, 8} : Finset ℕ) := ht_pos_aux p hp12 hpos
    have hc := commute_Xp_pos7 (K := K) hpmem
    have hx : xPar (rootOperatorFamily .G2) (rt p) c ∈ Xp K p :=
      (mem_Xp_iff hp12 _).2 ⟨c, rfl⟩
    have hy : xp 7 c' ∈ Xp K 7 := (mem_Xp_iff (by norm_num) _).2 ⟨c', rfl⟩
    have h := (hc _ hx _ hy).eq
    rw [h]
    simp

theorem borel_le_omega7 :
    CFSG.LieType.Steinberg.borel (g2Datum K) (CFSG.LieType.Steinberg.Adjoint.torus (τ := .G2) K) ≤
      omega7 K := by
  refine sup_le ?_ ?_
  · refine iSup_le fun i => ?_
    rintro _ ⟨t, rfl⟩
    exact torus_mem_omega7 i t
  · refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγR, hγp⟩ := hγ
    intro x hx
    have hγ' : IsRoot .G2 γ := CFSG.Timmesfeld.RankTwo.mem_g2_roots.1 hγR
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff hγ' x).1 hx
    exact posRoot_mem_omega7 hγ' hγp c

theorem borel_stab_X7 {b : adjointGroup .G2 K}
    (hb : b ∈ CFSG.LieType.Steinberg.borel (g2Datum K)
      (CFSG.LieType.Steinberg.Adjoint.torus (τ := .G2) K)) :
    ∃ χ : Kˣ,
      b • rootVec .G2 K (rt 7) = (χ : K) • rootVec .G2 K (rt 7) ∧
      (∀ x : RootModule .G2 K, coordAt (rt 10) (b • x) = ((χ⁻¹ : Kˣ) : K) * coordAt (rt 10) x) ∧
      (∀ c : K, b * xp 7 c * b⁻¹ = xp 7 ((χ : K) * c)) :=
  borel_le_omega7 hb

theorem reflect_long : ∀ t ∈ longPos, ∀ i : Fin (Tag.rank .G2),
    ∃ t' ∈ longPos, reflect .G2 i (rt t) = rt t' := by decide +kernel

theorem weylElement_smul_rootVec [CharP K 2] (i : Fin (Tag.rank .G2)) {t t' : ℕ}
    (ht : t < 12) (h : reflect .G2 i (rt t) = rt t') :
    weylElement .G2 K i • rootVec .G2 K (rt t) = rootVec .G2 K (rt t') := by
  have hα : IsRoot .G2 (rt t) := isRoot_rt ht
  have hw := weylElt_rootVec (R := K) i (1 : Kˣ) hα
  have hm1 : (-1 : K) = 1 := by simp [CharTwo.neg_eq]
  show (weylElt .G2 K i 1 : Module.End K (RootModule .G2 K)) (rootVec .G2 K (rt t)) = _
  rw [hw, h, hm1]
  simp

theorem list_prod_weylElement [CharP K 2] (ω : List (Fin (Tag.rank .G2))) :
    ∃ t ∈ longPos,
      (ω.map (weylElement .G2 K)).prod • rootVec .G2 K (rt 7) = rootVec .G2 K (rt t) ∧
      ∀ c : K, (ω.map (weylElement .G2 K)).prod * xp 7 c * ((ω.map (weylElement .G2 K)).prod)⁻¹ =
        xp t c := by
  induction ω with
  | nil => exact ⟨7, by simp [longPos], by simp, fun c => by simp⟩
  | cons i ω ih =>
    obtain ⟨t, ht, h1, h2⟩ := ih
    obtain ⟨t', ht', hr⟩ := reflect_long t ht i
    have ht12 : t < 12 := by
      simp only [longPos, Finset.mem_insert, Finset.mem_singleton] at ht
      omega
    refine ⟨t', ht', ?_, ?_⟩
    · rw [List.map_cons, List.prod_cons, mul_smul, h1]
      exact weylElement_smul_rootVec i ht12 hr
    · intro c
      rw [List.map_cons, List.prod_cons,
        show weylElement .G2 K i * (ω.map (weylElement .G2 K)).prod * xp 7 c *
          (weylElement .G2 K i * (ω.map (weylElement .G2 K)).prod)⁻¹ =
          weylElement .G2 K i * ((ω.map (weylElement .G2 K)).prod * xp 7 c *
            ((ω.map (weylElement .G2 K)).prod)⁻¹) * (weylElement .G2 K i)⁻¹ by group, h2 c]
      exact weylElement_conj_xp i ht12 hr c

theorem nrep_stab_X7 [CharP K 2]
    (w : (CFSG.LieType.RootSystem.coxeterMatrix (g2Datum K).isFiniteType).Group) :
    ∃ t ∈ longPos,
      CFSG.LieType.Steinberg.nrep (g2_isCTGroupDatum K) w • rootVec .G2 K (rt 7) =
        rootVec .G2 K (rt t) ∧
      (∀ c : K, CFSG.LieType.Steinberg.nrep (g2_isCTGroupDatum K) w * xp 7 c *
        (CFSG.LieType.Steinberg.nrep (g2_isCTGroupDatum K) w)⁻¹ = xp t c) := by
  obtain ⟨ω, hω, rfl⟩ :=
    ((CFSG.LieType.RootSystem.coxeterMatrix
      (g2Datum K).isFiniteType).toCoxeterSystem).exists_isReduced w
  rw [CFSG.LieType.Steinberg.nrep_wordProd (g2_isCTGroupDatum K) hω]
  exact list_prod_weylElement ω

end CFSG.RankThree.PartOne.SEITZ6
