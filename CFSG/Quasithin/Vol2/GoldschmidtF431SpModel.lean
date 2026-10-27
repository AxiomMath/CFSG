module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpData
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpAxis
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpBorel
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelSp4

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis
  CFSG.QuasithinUnique.Borel252 CFSG.Open CFSG.Quasithin

namespace SpModel

section Reps

variable {F : Type} [Field F] [CharP F 2]

@[expose] def iRep (F : Type) [Field F] [CharP F 2] : Fin 3 → antiSp F :=
  ![uElt 0 1 0 0, uElt 0 0 1 0, uElt 0 1 1 0]

@[expose] def Rrad (F : Type) [Field F] [CharP F 2] : Fin 2 → Subgroup (antiSp F) :=
  ![radA1 F, radA2 F]

@[expose] def axisOf : Fin 2 → Axis := ![.one, .two]

theorem rootA_axisOf (j : Fin 2) : rootA F (axisOf j) = Rrad F j := by
  fin_cases j <;> rfl

theorem rootU_axisOf_zero : rootU F (axisOf 0) = rootU₁ F := rfl

theorem rootU_axisOf_one : rootU F (axisOf 1) = rootU₂ F := rfl

theorem firstCol_of_commute {g : antiSp F} {c' : F}
    (h : g * uElt 0 0 1 0 = uElt 0 0 c' 0 * g) : FirstCol g := by
  have key : ∀ i : Fin 4, mat g i 0 + mat g i 3 =
      mat g i 3 + (if i = 0 then c' * mat g 3 3 else 0) := by
    intro i
    have := congrFun (congrFun (congrArg mat h) i) 3
    fin_cases i <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at this ⊢ <;>
      grind
  refine ⟨?_, ?_, ?_⟩
  · simpa using key 1
  · simpa using key 2
  · simpa using key 3

theorem firstCol_of_commute_i2 {g : antiSp F}
    (h : g * uElt 0 1 1 0 = uElt 0 1 1 0 * g) : FirstCol g := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have e := fun i j : Fin 4 => congrFun (congrFun (congrArg mat h) i) j
  have e10 := e 1 0
  have e00 := e 0 0
  have e12 := e 1 2
  have e02 := e 0 2
  simp [Matrix.mul_apply, Fin.sum_univ_four, mat, glMat_uElt, uMat] at e10 e00 e12 e02
  have s02 := mat_entry_eq g 0 2
  simp at s02
  have h30 : mat g 3 0 = 0 := e10
  have e00' : mat g 0 0 = mat g 0 0 + mat g 2 0 + mat g 3 0 := e00
  have e12' : mat g 1 0 + mat g 1 2 = mat g 1 2 + mat g 3 2 := e12
  have e02' : mat g 0 0 + mat g 0 2 = mat g 0 2 + mat g 2 2 + mat g 3 2 := e02
  have h20 : mat g 2 0 = 0 := by linear_combination (-1 : F) * e00' - h30
  have e1 : mat g 1 0 = mat g 3 2 := by linear_combination e12'
  have e2 : mat g 0 0 = mat g 2 2 + mat g 3 2 := by linear_combination e02'
  have ht : mat g 3 2 = 0 := by
    have hsq : (mat g 3 2) ^ 2 = 0 := by
      rw [h20, h30, e1, e2] at s02
      linear_combination s02 - (mat g 2 2 * mat g 3 2) * h2
    exact pow_eq_zero_iff two_ne_zero |>.mp hsq
  exact ⟨by rw [e1, ht], h20, h30⟩

end Reps

section Rho

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem minorAut_iRep (k : Fin 3) :
    minorAut F (iRep F k) = iRep F (![1, 0, 2] k) := by
  fin_cases k
  · show minorAut F (uElt 0 1 0 0) = uElt 0 0 1 0
    have := minorAut_uElt_radA2 (K := F) 0 1 0
    simpa using this
  · show minorAut F (uElt 0 0 1 0) = uElt 0 1 0 0
    exact minorAut_uElt_zero_zero 1
  · show minorAut F (uElt 0 1 1 0) = uElt 0 1 1 0
    have := minorAut_uElt_radA2 (K := F) 0 1 1
    simpa using this

omit [Finite F] in
theorem centralizer_i1_le :
    Subgroup.centralizer ({uElt 0 0 1 0} : Set (antiSp F)) ≤
      Subgroup.normalizer (rootU₂ F : Set (antiSp F)) := by
  intro g hg
  have hg' : g * uElt 0 0 1 0 = uElt 0 0 1 0 * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  exact mem_normalizer_rootU₂_iff.mpr (firstCol_of_commute (c' := 1) hg')

theorem centralizer_i0_le :
    Subgroup.centralizer ({uElt 0 1 0 0} : Set (antiSp F)) ≤
      Subgroup.normalizer (rootU₁ F : Set (antiSp F)) := by
  intro g hg
  have hg' : g * uElt 0 1 0 0 = uElt 0 1 0 0 * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hρ : minorAut F (uElt 0 0 1 0) = uElt 0 1 0 0 := minorAut_uElt_zero_zero 1
  have h1 : (minorAut F).symm g * uElt 0 0 1 0 = uElt 0 0 1 0 * (minorAut F).symm g := by
    apply (minorAut F).injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hρ]
    exact hg'
  have h2 : (minorAut F).symm g ∈ Subgroup.normalizer (rootU₂ F : Set (antiSp F)) :=
    mem_normalizer_rootU₂_iff.mpr (firstCol_of_commute (c' := 1) h1)
  rw [rootU₁_eq_map]
  exact (mem_normalizer_map (minorAut F) (rootU₂ F) g).mpr h2

theorem centralizer_i2_le :
    Subgroup.centralizer ({uElt 0 1 1 0} : Set (antiSp F)) ≤
      Subgroup.normalizer (radA1 F : Set (antiSp F)) ⊓
        Subgroup.normalizer (radA2 F : Set (antiSp F)) := by
  intro g hg
  have hg' : g * uElt 0 1 1 0 = uElt 0 1 1 0 * g := Subgroup.mem_centralizer_singleton_iff.mp hg
  have hρ : minorAut F (uElt 0 1 1 0) = uElt 0 1 1 0 := minorAut_iRep 2
  refine ⟨?_, ?_⟩
  · have h1 : (minorAut F).symm g * uElt 0 1 1 0 = uElt 0 1 1 0 * (minorAut F).symm g := by
      apply (minorAut F).injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hρ]
      exact hg'
    have h2 : (minorAut F).symm g ∈ Subgroup.normalizer (radA2 F : Set (antiSp F)) := by
      rw [normalizer_radA2_eq]
      exact firstCol_of_commute_i2 h1
    rw [radA1_eq_map]
    exact (mem_normalizer_map (minorAut F) (radA2 F) g).mpr h2
  · rw [normalizer_radA2_eq]
    exact firstCol_of_commute_i2 hg'

theorem fus_radA2 {x : antiSp F} (hx : x ∈ radA2 F) (hx1 : x ≠ 1) :
    ∃ k : Fin 3, ∃ m ∈ lineStab F, m * x * m⁻¹ = iRep F k := by
  obtain ⟨v, c, rfl⟩ := mem_radA2_iff.mp hx
  have hconjd : ∀ (l : Fˣ) (w : Fin 2 → F) (e : F),
      dElt l * aElt w e * (dElt l)⁻¹ = aElt ((l : F) • w) ((l : F) ^ 2 * e) := by
    intro l w e
    rw [dElt_mul_aElt, mul_inv_cancel_right]
  have hconjs : ∀ (M : SL₂ F) (w : Fin 2 → F) (e : F),
      sElt M * aElt w e * (sElt M)⁻¹ = aElt ((M : Matrix (Fin 2) (Fin 2) F) *ᵥ w) e := by
    intro M w e
    rw [sElt_mul_aElt, mul_inv_cancel_right]
  have hsq : ∀ c : F, c ≠ 0 → ∃ (l : Fˣ), (l : F) ^ 2 * c = 1 := by
    intro c hc
    obtain ⟨r, hr⟩ := exists_sq_eq c⁻¹
    have hr0 : r ≠ 0 := by
      rintro rfl
      exact inv_ne_zero hc (by rw [← hr]; ring)
    exact ⟨Units.mk0 r hr0, by rw [Units.val_mk0, hr, inv_mul_cancel₀ hc]⟩
  have he : (![1, 0] : Fin 2 → F) ≠ 0 := by
    intro h
    have := congrFun h 0
    simp at this
  by_cases hv : v = 0
  · subst hv
    have hc : c ≠ 0 := by
      rintro rfl
      exact hx1 aElt_zero_zero
    obtain ⟨l, hl⟩ := hsq c hc
    refine ⟨1, dElt l, mem_lineStab.mpr (firstCol_dElt l), ?_⟩
    rw [hconjd, smul_zero, hl, aElt_zero]
    rfl
  · obtain ⟨M₁, hM₁⟩ := exists_sl2_mulVec_eq hv he
    have h1 : sElt M₁ * aElt v c * (sElt M₁)⁻¹ = aElt ![1, 0] c := by
      rw [hconjs, hM₁]
    by_cases hc : c = 0
    · subst hc
      refine ⟨0, sElt M₁, mem_lineStab.mpr (firstCol_sElt M₁), ?_⟩
      rw [h1]
      show aElt ![1, 0] 0 = uElt 0 1 0 0
      simp [aElt]
    · obtain ⟨l, hl⟩ := hsq c hc
      have h2 : dElt l * aElt ![1, 0] c * (dElt l)⁻¹ = aElt ((l : F) • ![1, 0]) 1 := by
        rw [hconjd, hl]
      have hl0 : (l : F) ≠ 0 := l.ne_zero
      have hw : ((l : F) • ![1, 0] : Fin 2 → F) ≠ 0 := by
        intro h
        have := congrFun h 0
        simp [hl0] at this
      obtain ⟨M₂, hM₂⟩ := exists_sl2_mulVec_eq hw he
      have h3 : sElt M₂ * aElt ((l : F) • ![1, 0]) 1 * (sElt M₂)⁻¹ = aElt ![1, 0] 1 := by
        rw [hconjs, hM₂]
      refine ⟨2, sElt M₂ * dElt l * sElt M₁, mem_lineStab.mpr
        (((firstCol_sElt M₂).mul (firstCol_dElt l)).mul (firstCol_sElt M₁)), ?_⟩
      calc sElt M₂ * dElt l * sElt M₁ * aElt v c * (sElt M₂ * dElt l * sElt M₁)⁻¹
          = sElt M₂ * (dElt l * (sElt M₁ * aElt v c * (sElt M₁)⁻¹) * (dElt l)⁻¹) *
              (sElt M₂)⁻¹ := by group
        _ = aElt ![1, 0] 1 := by rw [h1, h2, h3]
        _ = iRep F 2 := by
          show aElt ![1, 0] 1 = uElt 0 1 1 0
          simp [aElt]

theorem fus_radA1 {x : antiSp F} (hx : x ∈ radA1 F) (hx1 : x ≠ 1) :
    ∃ k : Fin 3, ∃ m ∈ Subgroup.normalizer (radA1 F : Set (antiSp F)),
      m * x * m⁻¹ = iRep F k := by
  rw [radA1_eq_map] at hx
  obtain ⟨y, hy, rfl⟩ := hx
  have hy1 : y ≠ 1 := fun h => hx1 (by rw [h]; exact map_one _)
  obtain ⟨k, m, hm, hmk⟩ := fus_radA2 hy hy1
  refine ⟨![1, 0, 2] k, minorAut F m, ?_, ?_⟩
  · rw [radA1_eq_map]
    refine (mem_normalizer_map (minorAut F) (radA2 F) _).mpr ?_
    rw [MulEquiv.symm_apply_apply, normalizer_radA2_eq]
    exact hm
  · rw [← minorAut_iRep, ← hmk]
    simp [map_mul, map_inv]

end Rho

section Assembly

variable {F : Type} [Field F] [CharP F 2] {n : ℕ}

theorem borel_antiSp [Finite F] (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    BorelData (antiSp F) (antiUnipotent F) (radA1 F) (radA2 F) :=
  Sp4.borelData_Sp hn hF

omit [Field F] [CharP F 2] in
theorem two_lt_card (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) : 2 < Nat.card F := by
  rw [hF]
  calc 2 < 4 := by norm_num
    _ = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

theorem rootCoord_injective' (i : Axis) : Function.Injective (rootCoord F i) := by
  cases i
  · intro a b h
    exact (uElt_inj h).2.1
  · intro a b h
    exact (uElt_inj h).2.2.1

theorem rootCoord_zero (i : Axis) : rootCoord F i 0 = 1 := by
  cases i <;> exact uElt_zero_eq_one

theorem centerOf_antiUnipotent :
    centerOf (antiUnipotent F) = antiUnipotentCenter F := by
  ext g
  rw [mem_centerOf_iff, mem_antiUnipotentCenter_iff_central]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h hh => (h2 h hh).symm⟩
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun h hh => (h2 h hh).symm⟩

theorem mem_centerOf_of_mem_Z₀ {g : antiSp F} (hg : g ∈ antiUnipotentCenter F) :
    g ∈ centerOf (antiUnipotent F) := by
  rw [centerOf_antiUnipotent]
  exact hg

theorem mem_radA1_of_commute_uElt {y : antiSp F} (hy : y ∈ antiUnipotent F) {b c d : F}
    (hd : d ≠ 0) (h : y * uElt 0 b c d = uElt 0 b c d * y) : y ∈ radA1 F := by
  obtain ⟨a', b', c', d', rfl⟩ := hy
  rw [uElt_mul, uElt_mul] at h
  have h1 := (uElt_inj h).2.1
  have ha : a' = 0 := by
    have : a' * d = 0 := by linear_combination h1
    exact (mul_eq_zero.mp this).resolve_right hd
  exact ⟨b', c', d', by rw [ha]⟩

theorem mem_radA2_of_commute_uElt {y : antiSp F} (hy : y ∈ antiUnipotent F) {a b c : F}
    (ha : a ≠ 0) (h : y * uElt a b c 0 = uElt a b c 0 * y) : y ∈ radA2 F := by
  obtain ⟨a', b', c', d', rfl⟩ := hy
  rw [uElt_mul, uElt_mul] at h
  have h1 := (uElt_inj h).2.1
  have hd : d' = 0 := by
    have : a * d' = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp this).resolve_left ha
  exact ⟨a', b', c', by rw [hd]⟩

theorem shape_antiSp [Finite F] (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    SpShape (antiUnipotent F) (Rrad F) where
  Q_le j := by
    fin_cases j
    · exact radA1_le_antiUnipotent
    · exact radA2_le_antiUnipotent
  Q_norm j := by
    have hB := borel_antiSp (F := F) hn hF
    fin_cases j
    · exact Subgroup.le_normalizer.trans hB.lt₁.le
    · exact Subgroup.le_normalizer.trans hB.lt₂.le
  Q_abel j := by
    fin_cases j
    · exact fun x hx y hy => radA1_comm hx hy
    · exact fun x hx y hy => radA2_comm hx hy
  Z_le j := by
    intro x hx
    rw [centerOf_antiUnipotent] at hx
    fin_cases j
    · exact antiUnipotentCenter_le_radA1 hx
    · exact antiUnipotentCenter_le_radA2 hx
  Z_sq := by
    intro z hz
    rw [centerOf_antiUnipotent] at hz
    rw [sq]
    exact mul_self_of_mem_radA1 (antiUnipotentCenter_le_radA1 hz)
  inv_mem := by
    intro x hx hx2
    rw [sq] at hx2
    rcases (mul_self_eq_one_iff hx).mp hx2 with h | h
    · exact ⟨0, h⟩
    · exact ⟨1, h⟩
  cen := by
    intro j x hx hxZ y hy hxy
    rw [centerOf_antiUnipotent] at hxZ
    fin_cases j
    · obtain ⟨b, c, d, rfl⟩ := hx
      have hd : d ≠ 0 := by
        rintro rfl
        exact hxZ ⟨b, c, rfl⟩
      exact mem_radA1_of_commute_uElt hy hd hxy
    · obtain ⟨a, b, c, rfl⟩ := hx
      have ha : a ≠ 0 := by
        rintro rfl
        exact hxZ ⟨b, c, rfl⟩
      exact mem_radA2_of_commute_uElt hy ha hxy
  ex := by
    intro j
    fin_cases j
    · refine ⟨uElt 0 0 0 1, ⟨0, 0, 1, rfl⟩, ?_, by
        rw [sq]
        exact mul_self_of_mem_radA1 ⟨0, 0, 1, rfl⟩⟩
      rw [centerOf_antiUnipotent]
      rintro ⟨b, c, h⟩
      exact one_ne_zero (uElt_inj h).2.2.2
    · refine ⟨uElt 1 0 0 0, ⟨1, 0, 0, rfl⟩, ?_, by
        rw [sq]
        exact mul_self_of_mem_radA2 ⟨1, 0, 0, rfl⟩⟩
      rw [centerOf_antiUnipotent]
      rintro ⟨b, c, h⟩
      exact one_ne_zero (uElt_inj h).1

end Assembly


section Roots

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem hS_axis (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (j : Fin 2) :
    RootAxisStructure (rootU F (axisOf j)) (rootA F (axisOf j)) (sHom F (axisOf j))
      (dHom F (axisOf j)) (rootCoord F (axisOf j)) (vecOf F (axisOf j)) :=
  even_symplectic_four_root_axis_centralizer_structure hF hn (axisOf j)

omit [Finite F] in
theorem rootU_le_rootA (j : Fin 2) : rootU F (axisOf j) ≤ rootA F (axisOf j) := by
  fin_cases j
  · exact rootU₁_le_radA1
  · exact rootU₂_le_radA2

theorem spZc_eq (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (j : Fin 2) :
    spZc (Rrad F) j = rootU F (axisOf j) := by
  unfold spZc
  rw [← rootA_axisOf j, axis_perfectCore_normalizer (hS_axis hn hF j),
    axis_centerOf_centralizer (hS_axis hn hF j) (rootU_le_rootA j) (two_lt_card hn hF)]

omit [Finite F] in
theorem rootU_le_center (j : Fin 2) :
    rootU F (axisOf j) ≤ centerOf (antiUnipotent F) := by
  intro x hx
  apply mem_centerOf_of_mem_Z₀
  fin_cases j
  · obtain ⟨b, rfl⟩ := hx
    exact ⟨b, 0, rfl⟩
  · obtain ⟨c, rfl⟩ := hx
    exact ⟨0, c, rfl⟩

omit [Finite F] in
theorem rootU_inf (x : antiSp F) (h0 : x ∈ rootU F (axisOf 0)) (h1 : x ∈ rootU F (axisOf 1)) :
    x = 1 := by
  obtain ⟨b, rfl⟩ := h0
  obtain ⟨c, hc⟩ := h1
  have hb : b = 0 := (uElt_inj hc).2.1
  rw [hb]
  exact uElt_zero_eq_one

theorem O2_antiSp (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) (P : Subgroup (antiSp F))
    (hPn : P.Normal) (hPp : IsPGroup 2 P) : P = ⊥ := by
  have hB := borel_antiSp (F := F) hn hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hPU : P ≤ antiUnipotent F := by
    have h1 : P ≤ pCoreOf 2 (⊤ : Subgroup (antiSp F)) :=
      CFSG.LieType.BorelTits.le_pCoreOf 2 le_top (hPn.subgroupOf ⊤) hPp
    exact h1.trans (CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le hB.sylow)
  have hPR : ∀ j, P ≤ Rrad F j := by
    intro j
    fin_cases j
    · have hle : P ≤ Subgroup.normalizer (radA1 F : Set (antiSp F)) :=
        hPU.trans (Subgroup.le_normalizer.trans hB.lt₁.le)
      have := CFSG.LieType.BorelTits.le_pCoreOf 2 hle (hPn.subgroupOf _) hPp
      rwa [hB.core₁] at this
    · have hle : P ≤ Subgroup.normalizer (radA2 F : Set (antiSp F)) :=
        hPU.trans (Subgroup.le_normalizer.trans hB.lt₂.le)
      have := CFSG.LieType.BorelTits.le_pCoreOf 2 hle (hPn.subgroupOf _) hPp
      rwa [hB.core₂] at this
  have hPUj : ∀ j, P ≤ rootU F (axisOf j) := by
    intro j
    have hS := hS_axis hn hF j
    have hA : P ≤ rootA F (axisOf j) := by
      rw [rootA_axisOf]
      exact hPR j
    by_contra hnot
    have hPA := hS.normal_eq_A P (hA.trans hS.A_le_C)
      (fun g _ v hv => hPn.conj_mem v hv g) hA hnot
    have hAn : (rootA F (axisOf j)).Normal := hPA ▸ hPn
    have htop : Subgroup.normalizer (rootA F (axisOf j) : Set (antiSp F)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.mpr hAn
    rw [rootA_axisOf] at htop
    fin_cases j
    · exact absurd htop hB.lt_top₁.ne
    · exact absurd htop hB.lt_top₂.ne
  rw [eq_bot_iff]
  intro x hx
  rw [Subgroup.mem_bot]
  exact rootU_inf x (hPUj 0 hx) (hPUj 1 hx)

end Roots


section Data

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

omit [Finite F] in
theorem iRep_mem_Z₀ (k : Fin 3) : iRep F k ∈ antiUnipotentCenter F := by
  fin_cases k
  · exact ⟨1, 0, rfl⟩
  · exact ⟨0, 1, rfl⟩
  · exact ⟨1, 1, rfl⟩

theorem spDData_antiSp (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) :
    SpDData (antiUnipotent F) (Rrad F) (iRep F) where
  borel := borel_antiSp hn hF
  shape := shape_antiSp hn hF
  Z_le j := by
    rw [spZc_eq hn hF j]
    exact rootU_le_center j
  Z_ne j := by
    refine ⟨rootCoord F (axisOf j) 1, ?_, fun h => ?_⟩
    · rw [spZc_eq hn hF j]
      exact (hS_axis hn hF j).coord_mem 1
    · exact one_ne_zero (rootCoord_injective' (axisOf j) (h.trans (rootCoord_zero (axisOf j)).symm))
  Z_trans j := by
    intro x hx y hy hx1 hy1
    rw [spZc_eq hn hF j] at hx hy
    have := axis_exists_normalizer_conj (hS_axis hn hF j) (rootCoord_zero _) hx hy hx1 hy1
    rwa [rootA_axisOf] at this
  Z_inf x hx0 hx1 := by
    rw [spZc_eq hn hF 0] at hx0
    rw [spZc_eq hn hF 1] at hx1
    exact rootU_inf x hx0 hx1
  i_mem k := mem_centerOf_of_mem_Z₀ (iRep_mem_Z₀ k)
  i_ne k := by
    intro h
    rw [← uElt_zero_eq_one] at h
    fin_cases k
    · have h' : uElt (0 : F) 1 0 0 = uElt 0 0 0 0 := h
      exact one_ne_zero (uElt_inj h').2.1
    · have h' : uElt (0 : F) 0 1 0 = uElt 0 0 0 0 := h
      exact one_ne_zero (uElt_inj h').2.2.1
    · have h' : uElt (0 : F) 1 1 0 = uElt 0 0 0 0 := h
      exact one_ne_zero (uElt_inj h').2.1
  i_sq k := by
    rw [sq]
    exact mul_self_of_mem_radA1 (antiUnipotentCenter_le_radA1 (iRep_mem_Z₀ k))
  i0 := by
    rw [spZc_eq hn hF 0]
    exact ⟨1, rfl⟩
  i1 := by
    rw [spZc_eq hn hF 1]
    exact ⟨1, rfl⟩
  i2 := by
    constructor
    · rw [spZc_eq hn hF 0]
      rintro ⟨b, h⟩
      exact one_ne_zero (uElt_inj h).2.2.1
    · rw [spZc_eq hn hF 1]
      rintro ⟨c, h⟩
      exact one_ne_zero (uElt_inj h).2.1
  cent0 := by
    have := axis_pCoreOf_centralizer_singleton (hS_axis hn hF 0)
      (rootCoord_injective' (axisOf 0)) (centralizer_i0_le (F := F))
    exact this
  cent1 := by
    have := axis_pCoreOf_centralizer_singleton (hS_axis hn hF 1)
      (rootCoord_injective' (axisOf 1)) (centralizer_i1_le (F := F))
    exact this
  cent2 := (centralizer_i2_le (F := F)).trans (borel_antiSp (F := F) hn hF).inf_norm.le
  fus := by
    intro x hx hx1 hx2
    rw [sq] at hx2
    rcases (mul_self_eq_one_iff hx).mp hx2 with h | h
    · obtain ⟨k, m, hm, hmk⟩ := fus_radA1 h hx1
      exact ⟨k, 0, m, hm, hmk⟩
    · obtain ⟨k, m, hm, hmk⟩ := fus_radA2 h hx1
      exact ⟨k, 1, m, by rw [← normalizer_radA2_eq] at hm; exact hm, hmk⟩

theorem yam_antiSp (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n) {P₁ P₂ : Subgroup (antiSp F)}
    (hy : IsYAmalgamPair (antiUnipotent F) P₁ P₂) :
    (P₁ = Subgroup.normalizer (radA1 F : Set (antiSp F)) ∧
        P₂ = Subgroup.normalizer (radA2 F : Set (antiSp F))) ∨
      (P₁ = Subgroup.normalizer (radA2 F : Set (antiSp F)) ∧
        P₂ = Subgroup.normalizer (radA1 F : Set (antiSp F))) :=
  (borel_antiSp hn hF).yam_cases (O2_antiSp hn hF) hy

end Data


end SpModel

end CFSG.Quasithin.H13.F431
