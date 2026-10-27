module

public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Local3
public import Certificates.Certificate148004

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148V

open CFSG.ComponentClassification.J2Cover CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Native
  CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 Subgroup
open scoped commutatorElement

section General

variable {X : Type*} [Group X]

theorem exists_conj_zpow_of_mem_normalizer {z m : X}
    (hm : m ∈ normalizer ((zpowers z : Subgroup X) : Set X)) :
    ∃ k : ℤ, ∀ j : ℤ, m⁻¹ * z ^ j * m = z ^ (k * j) := by
  have h : m⁻¹ * z * m⁻¹⁻¹ ∈ zpowers z :=
    (mem_normalizer_iff.mp (inv_mem hm) z).mp (mem_zpowers z)
  rw [inv_inv] at h
  obtain ⟨k, hk⟩ := mem_zpowers_iff.mp h
  refine ⟨k, fun j => ?_⟩
  have e : (m⁻¹ * z * m⁻¹⁻¹) ^ j = m⁻¹ * z ^ j * m⁻¹⁻¹ := conj_zpow
  rw [inv_inv] at e
  rw [← e, ← hk, zpow_mul]

theorem commutator_mem_centralizer_of_mem_normalizer_zpowers {z m₁ m₂ : X}
    (h₁ : m₁ ∈ normalizer ((zpowers z : Subgroup X) : Set X))
    (h₂ : m₂ ∈ normalizer ((zpowers z : Subgroup X) : Set X)) :
    ⁅m₁, m₂⁆ ∈ centralizer ({z} : Set X) := by
  obtain ⟨k₁, hk₁⟩ := exists_conj_zpow_of_mem_normalizer h₁
  obtain ⟨k₂, hk₂⟩ := exists_conj_zpow_of_mem_normalizer h₂
  have e₁ : m₁⁻¹ * z * m₁ = z ^ k₁ := by simpa using hk₁ 1
  have e₂ : m₂⁻¹ * z * m₂ = z ^ k₂ := by simpa using hk₂ 1
  have e₁₂ : m₂⁻¹ * (m₁⁻¹ * z * m₁) * m₂ = z ^ (k₂ * k₁) := by rw [e₁, hk₂]
  have e₂₁ : m₁⁻¹ * (m₂⁻¹ * z * m₂) * m₁ = z ^ (k₁ * k₂) := by rw [e₂, hk₁]
  rw [mem_centralizer_singleton_iff, commutatorElement_def]
  calc m₁ * m₂ * m₁⁻¹ * m₂⁻¹ * z
      = m₁ * m₂ * (m₁⁻¹ * (m₂⁻¹ * z * m₂) * m₁) * m₂⁻¹ * m₁⁻¹ *
          (m₁ * m₂ * m₁⁻¹ * m₂⁻¹) := by group
    _ = m₁ * m₂ * (m₂⁻¹ * (m₁⁻¹ * z * m₁) * m₂) * m₂⁻¹ * m₁⁻¹ *
          (m₁ * m₂ * m₁⁻¹ * m₂⁻¹) := by rw [e₂₁, e₁₂, mul_comm k₁ k₂]
    _ = z * (m₁ * m₂ * m₁⁻¹ * m₂⁻¹) := by group

theorem le_centralizer_of_isPerfect_of_le_normalizer {z : X} {M : Subgroup X}
    (hM : Group.IsPerfect ↥M) (hle : M ≤ normalizer ((zpowers z : Subgroup X) : Set X)) :
    M ≤ centralizer ({z} : Set X) := by
  rw [← Subgroup.isPerfect_iff.mp hM, Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  exact commutator_mem_centralizer_of_mem_normalizer_zpowers (hle hg₁) (hle hg₂)

end General

theorem wordA_mem {M' : Subgroup (Equiv.Perm (Fin 315))} {gs gi : Array (Array ℕ)} {j : ℕ}
    (hgs : ∀ h < j, ∃ x ∈ M', Rep 315 gs[h]! x ∧ Rep 315 gi[h]! x⁻¹) :
    ∀ w : List ℤ, lettersOK j w = true → ∃ x ∈ M', Rep 315 (wordA 315 gs gi w) x
  | [], _ => ⟨1, M'.one_mem, by simpa [wordA] using (rep_idA (n := 315))⟩
  | l :: w, hw => by
    simp only [lettersOK, List.all_cons, Bool.and_eq_true, bne_iff_ne, ne_eq,
      decide_eq_true_eq] at hw
    obtain ⟨⟨hl0, hlj⟩, hw⟩ := hw
    have hw' : lettersOK j w = true := by
      simpa [lettersOK, List.all_eq_true] using hw
    obtain ⟨y, hyM, hy⟩ := wordA_mem hgs w hw'
    obtain ⟨x, hxM, hx, hxi⟩ := hgs (l.natAbs - 1) (by omega)
    rw [wordA]
    unfold letterA
    by_cases hpos : 0 < l
    · rw [if_pos hpos]
      have e : l.toNat - 1 = l.natAbs - 1 := by omega
      rw [e]
      exact ⟨x * y, M'.mul_mem hxM hyM, rep_compA hx hy⟩
    · rw [if_neg hpos]
      have e : (-l).toNat - 1 = l.natAbs - 1 := by omega
      rw [e]
      exact ⟨x⁻¹ * y, M'.mul_mem (M'.inv_mem hxM) hyM, rep_compA hxi hy⟩

theorem rep_of_eqA_symm {n : ℕ} {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (hu : Rep n u g)
    (h : eqA n t u = true) : Rep n t g := fun x => by
  have := allLt_spec h x.2
  rw [beq_iff_eq] at this
  rw [this]
  exact hu x

theorem exists_eqA_of_any {n : ℕ} {S : Array (Array ℕ)} {t : Array ℕ}
    (h : S.any (eqA n t) = true) : ∃ j < S.size, eqA n t S[j]! = true := by
  rw [Array.any_eq_true] at h
  obtain ⟨j, hj, h⟩ := h
  exact ⟨j, hj, by rw [getElem!_pos S j hj]; exact h⟩

section Model


theorem over_parts :
    validA 315 autStrong[0]! = true ∧ validA 315 autStrong[1]! = true ∧
      gensCzArr.size = 2 ∧ mArrs.size = 8 ∧ wordsA.size = 8 ∧ wordsB.size = 8 ∧
      (∀ r < 8, okA mArrs[r]! = true) ∧ 0 < (zOrbit ()).size ∧
      eqA 315 (zOrbit ())[0]! zArr = true ∧
      (∀ i < (zOrbit ()).size, closedAt (zOrbit ()) autStrong[0]! i = true ∧
        closedAt (zOrbit ()) autStrong[1]! i = true) ∧
      (∀ i < (zOrbit ()).size, inZ (zOrbit ())[i]! = true ∨
        coveredBy cCz.pts (mArrs.map fun m => conjA 315 m zArr) (zOrbit ())[i]! = true) ∧
      ∀ r < 8, wordsOK r = true := by
  have h := Certificates.certificate148004
  simp only [overCheck, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, allLt_iff,
    Bool.or_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12⟩

theorem permOfArr_a : permOfArr 315 autStrong[0]! = permA :=
  (rep_of_validA over_parts.1).unique rep_permA

theorem permOfArr_b : permOfArr 315 autStrong[1]! = permB :=
  (rep_of_validA over_parts.2.1).unique rep_permB

theorem orbit_step {g : Array ℕ} {x : Equiv.Perm (Fin 315)} (hg : validA 315 g = true)
    (hx : permOfArr 315 g = x)
    (hcl : ∀ i < (zOrbit ()).size, closedAt (zOrbit ()) g i = true) {i : ℕ}
    (hi : i < (zOrbit ()).size) {y : Equiv.Perm (Fin 315)} (hy : Rep 315 (zOrbit ())[i]! y) :
    (∃ j < (zOrbit ()).size, Rep 315 (zOrbit ())[j]! (x * y * x⁻¹)) ∧
      ∃ j < (zOrbit ()).size, Rep 315 (zOrbit ())[j]! (x⁻¹ * y * x) := by
  have h := hcl i hi
  simp only [closedAt, Bool.and_eq_true] at h
  obtain ⟨j₁, hj₁, e₁⟩ := exists_eqA_of_any h.1
  obtain ⟨j₂, hj₂, e₂⟩ := exists_eqA_of_any h.2
  have r₁ := rep_conjA hg hy
  have r₂ := rep_conjInvA hg hy
  rw [hx] at r₁ r₂
  exact ⟨⟨j₁, hj₁, rep_of_eqA r₁ e₁⟩, ⟨j₂, hj₂, rep_of_eqA r₂ e₂⟩⟩

theorem orbit_rep (g : Equiv.Perm (Fin 315)) (hg : g ∈ P) :
    ∃ i < (zOrbit ()).size, Rep 315 (zOrbit ())[i]! (g * zJ.1 * g⁻¹) := by
  obtain ⟨hva, hvb, -, -, -, -, -, h0, hz0, hcl, -, -⟩ := over_parts
  rw [P] at hg
  induction hg using Subgroup.closure_induction_left with
  | one => exact ⟨0, h0, by simpa using rep_of_eqA_symm rep_z hz0⟩
  | mul_left x hx y hy ih =>
    obtain ⟨i, hi, hr⟩ := ih
    have e : x * y * zJ.1 * (x * y)⁻¹ = x * (y * zJ.1 * y⁻¹) * x⁻¹ := by group
    rw [e]
    rcases hx with rfl | rfl
    · exact (orbit_step hva permOfArr_a (fun i hi => (hcl i hi).1) hi hr).1
    · exact (orbit_step hvb permOfArr_b (fun i hi => (hcl i hi).2) hi hr).1
  | inv_mul_cancel x hx y hy ih =>
    obtain ⟨i, hi, hr⟩ := ih
    have e : x⁻¹ * y * zJ.1 * (x⁻¹ * y)⁻¹ = x⁻¹ * (y * zJ.1 * y⁻¹) * x := by group
    rw [e]
    rcases hx with rfl | rfl
    · exact (orbit_step hva permOfArr_a (fun i hi => (hcl i hi).1) hi hr).2
    · exact (orbit_step hvb permOfArr_b (fun i hi => (hcl i hi).2) hi hr).2

theorem exists_centralizer_of_cCz {k : ℕ} (hk : k < cCz.pts.size) :
    ∃ h : GJ, h ∈ centralizer ({zJ} : Set GJ) ∧ Rep 315 cCz.pts[k]! h.1 ∧
      validA 315 cCz.pts[k]! = true := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec (n := 315) (gs := gensCzArr) (ps := keyPts)
    (by decide) enum_spec.2.2.1
  have hx : permOfArr 315 cCz.pts[k]! ∈ Subgroup.closure (permsA 315 gensCzArr) :=
    (hmem _).2 ⟨k, hk, rfl⟩
  refine ⟨⟨_, closure_le_P gensCz_spec hx⟩, ?_, rep_of_validA (hval k hk), hval k hk⟩
  rw [centralizer_z]
  exact mem_subOf.2 hx

theorem wGens_mem {M : Subgroup GJ} (hCM : centralizer ({zJ} : Set GJ) ≤ M) {t : Array ℕ}
    (ht : okA t = true) (htM : eltOf t ht ∈ M) :
    ∀ h < 3, ∃ x ∈ M.map P.subtype, Rep 315 (wGens t)[h]! x ∧
      Rep 315 ((wGens t).map (invCand 315))[h]! x⁻¹ := by
  have hsz : (wGens t).size = 3 := rfl
  have hinv : ∀ h < 3, ((wGens t).map (invCand 315))[h]! = invCand 315 (wGens t)[h]! := by
    intro h hh
    rw [getElem!_pos _ h (by simpa [hsz] using hh), getElem!_pos _ h (by rw [hsz]; exact hh)]
    simp
  have hcz : ∀ k < 2, ∃ x ∈ M.map P.subtype, Rep 315 gensCzArr[k]! x ∧
      Rep 315 (invCand 315 gensCzArr[k]!) x⁻¹ := by
    intro k hk
    have hk' : k < gensCzArr.size := by rw [over_parts.2.2.1]; exact hk
    have hv := (gensCz_spec k hk').1
    have hx : permOfArr 315 gensCzArr[k]! ∈ Subgroup.closure (permsA 315 gensCzArr) :=
      Subgroup.subset_closure (mem_permsA hk')
    refine ⟨_, ⟨⟨_, closure_le_P gensCz_spec hx⟩, hCM ?_, rfl⟩, rep_of_validA hv,
      rep_inv_of_validA hv⟩
    rw [centralizer_z]
    exact mem_subOf.2 hx
  intro h hh
  rw [hinv h hh]
  interval_cases h
  · exact hcz 0 (by norm_num)
  · exact hcz 1 (by norm_num)
  · refine ⟨_, ⟨eltOf t ht, htM, rfl⟩, rep_eltOf ht, ?_⟩
    have := rep_inv_of_validA (okA_spec ht).1
    rwa [(rep_of_validA (okA_spec ht).1).unique (rep_eltOf ht)] at this

theorem eq_top_of_not_le_normalizer {M : Subgroup GJ} (hCM : centralizer ({zJ} : Set GJ) ≤ M)
    {g : GJ} (hgM : g ∈ M) (hgN : g ∉ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ)) :
    M = ⊤ := by
  obtain ⟨-, -, -, hm8, -, -, hm, -, -, -, hcov, hw⟩ := over_parts
  obtain ⟨i, hi, hrep⟩ := orbit_rep g.1 g.2
  have hrep' : Rep 315 (zOrbit ())[i]! (g * zJ * g⁻¹).1 := by simpa using hrep
  rcases hcov i hi with hZ | hc
  · exact absurd (mem_normalizer_zpowers_of_mem (inZ_spec hrep' hZ)) hgN
  simp only [coveredBy, Array.any_eq_true] at hc
  obtain ⟨k, hk, hc⟩ := hc
  obtain ⟨r, hr, hc⟩ := hc
  have hr8 : r < 8 := by simpa [hm8] using hr
  obtain ⟨h, hhC, hhrep, hhv⟩ := exists_centralizer_of_cCz hk
  have hhrep' : Rep 315 cCz.pts[k] h.1 := by rwa [← getElem!_pos cCz.pts k hk]
  have hhv' : validA 315 cCz.pts[k] = true := by rwa [← getElem!_pos cCz.pts k hk]
  set t := mArrs[r]! with htdef
  have ht : okA t = true := hm r hr8
  set m := eltOf t ht with hmdef
  have hTr : (mArrs.map fun m => conjA 315 m zArr)[r] = conjA 315 t zArr := by
    simp [htdef, getElem!_pos mArrs r (by rw [hm8]; exact hr8)]
  rw [hTr] at hc
  have e : h * (g * zJ * g⁻¹) * h⁻¹ = m * zJ * m⁻¹ :=
    eq_of_rep (rep_conj hhrep' hhv' hrep') (rep_conj (rep_eltOf ht) (okA_spec ht).1 rep_z) hc
  have hu : m⁻¹ * (h * g) ∈ centralizer ({zJ} : Set GJ) := by
    rw [mem_centralizer_singleton_iff]
    calc m⁻¹ * (h * g) * zJ = m⁻¹ * (h * (g * zJ * g⁻¹) * h⁻¹) * (h * g) := by group
      _ = m⁻¹ * (m * zJ * m⁻¹) * (h * g) := by rw [e]
      _ = zJ * (m⁻¹ * (h * g)) := by group
  have hmM : m ∈ M := by
    have h1 : h * g ∈ M := M.mul_mem (hCM hhC) hgM
    have h2 := M.mul_mem h1 (M.inv_mem (hCM hu))
    have e2 : h * g * (m⁻¹ * (h * g))⁻¹ = m := by group
    rwa [e2] at h2
  have hwr := hw r hr8
  simp only [wordsOK, Bool.and_eq_true] at hwr
  obtain ⟨⟨⟨hla, hea⟩, hlb⟩, heb⟩ := hwr
  have hgs := wGens_mem hCM ht hmM
  obtain ⟨xa, hxaM, hxa⟩ := wordA_mem hgs _ hla
  obtain ⟨xb, hxbM, hxb⟩ := wordA_mem hgs _ hlb
  have hxa' : xa = permA := eq_of_eqA hxa rep_permA hea
  have hxb' : xb = permB := eq_of_eqA hxb rep_permB heb
  have hPM : ∀ x ∈ Subgroup.closure ({permA, permB} : Set (Equiv.Perm (Fin 315))),
      x ∈ M.map P.subtype := by
    intro x hx
    refine (Subgroup.closure_le (K := M.map P.subtype)).2 ?_ hx
    rintro x (rfl | rfl)
    · exact hxa' ▸ hxaM
    · exact hxb' ▸ hxbM
  rw [eq_top_iff]
  intro x _
  obtain ⟨y, hyM, hy⟩ := hPM x.1 x.2
  rwa [Subtype.ext hy] at hyM

theorem le_normalizer_or_eq_top {M : Subgroup GJ} (hCM : centralizer ({zJ} : Set GJ) ≤ M) :
    M ≤ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ) ∨ M = ⊤ := by
  by_cases h : M ≤ normalizer ((zpowers zJ : Subgroup GJ) : Set GJ)
  · exact Or.inl h
  · obtain ⟨g, hgM, hgN⟩ := Set.not_subset.mp h
    exact Or.inr (eq_top_of_not_le_normalizer hCM hgM hgN)

end Model

end CFSG.RankThree.PartTwo.Sec4.Ronan148V
