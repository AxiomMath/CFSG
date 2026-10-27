module

public import CFSG.RankThree.GF2n.Stroth80.Sec8HPoints
public import CFSG.RankThree.GF2n.Stroth80.Sec8Inv
public import CFSG.RankThree.GF2n.Stroth80.Sec8WittPair

public section

namespace CFSG.RankThree.GF2n.Stroth80

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_conj_Vone {g : G} {Q V B' C' : Subgroup G} (hQ : conjSubgroup g Q = Q)
    (hV : conjSubgroup g V = V) :
    conjSubgroup g (Vone Q B' C' V) = Vone Q (conjSubgroup g B') (conjSubgroup g C') V := by
  simp only [Vone, CFSG.RankThree.GF2n.conjSubgroup_inf, conjSubgroup_sup', QB_conj, hQ, hV]

theorem sec8_point_of_vec {hc : Ctx M Q Z B} {n : ℕ} {t : G} (hs : Sec8Hyp hc n t) {m : ℕ}
    {K : Type} [Field K] [Finite K] {φ : ↥(Rt M (LB M Q B) t) →* GL (Fin m ⊕ Fin m) K}
    {u : Fin m ⊕ Fin m → K} (hu : u ≠ 0)
    [hn : (Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
    (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
      Multiplicative (Fin m ⊕ Fin m → K))
    (hBiff : ∀ x : Fin m ⊕ Fin m → K,
      (∃ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B ∧ secVec ψ b = x) ↔ ∃ c : K, x = c • u)
    (hψ : ∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
      (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ
            Multiplicative.toAdd (ψ (QuotientGroup.mk v)))
    {h h' : ↥(Rt M (LB M Q B) t)} {c : K}
    (hv : (φ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u =
      c • ((φ h' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)) :
    conjSubgroup (h : G) B ⊔ Z = conjSubgroup (h' : G) B ⊔ Z := by
  have hhM : (h : G) ∈ M := hc.Rt_le_M t h.2
  have hh'M : (h' : G) ∈ M := hc.Rt_le_M t h'.2
  have hhV : conjSubgroup (h : G) B ≤ Vt M (LB M Q B) B Z t :=
    (le_sup_left : conjSubgroup (h : G) B ≤ conjSubgroup (h : G) B ⊔ Z).trans
      (hc.conj_Rt_le_Vt hs.toSec5.mem h.2)
  have hh'V : conjSubgroup (h' : G) B ≤ Vt M (LB M Q B) B Z t :=
    (le_sup_left : conjSubgroup (h' : G) B ≤ conjSubgroup (h' : G) B ⊔ Z).trans
      (hc.conj_Rt_le_Vt hs.toSec5.mem h'.2)
  obtain ⟨bV, hbB, hbu⟩ := (hBiff u).mpr ⟨1, by rw [one_smul]⟩
  obtain ⟨b'V, hb'B, hb'u⟩ := (hBiff (c • u)).mpr ⟨c, rfl⟩
  have hbu' : Multiplicative.toAdd (ψ (QuotientGroup.mk bV)) = u := hbu
  have hb'u' : Multiplicative.toAdd (ψ (QuotientGroup.mk b'V)) = c • u := hb'u
  have hdB : (h : G) * (bV : G) * (h : G)⁻¹ ∈ conjSubgroup (h : G) B := by
    rw [mem_conjSubgroup]
    have e : (h : G)⁻¹ * ((h : G) * (bV : G) * (h : G)⁻¹) * (h : G) = (bV : G) := by group
    rw [e]
    exact hbB
  have hd'B : (h' : G) * (b'V : G) * (h' : G)⁻¹ ∈ conjSubgroup (h' : G) B := by
    rw [mem_conjSubgroup]
    have e : (h' : G)⁻¹ * ((h' : G) * (b'V : G) * (h' : G)⁻¹) * (h' : G) = (b'V : G) := by
      group
    rw [e]
    exact hb'B
  have hdV : (h : G) * (bV : G) * (h : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := hhV hdB
  have hd'V : (h' : G) * (b'V : G) * (h' : G)⁻¹ ∈ Vt M (LB M Q B) B Z t := hh'V hd'B
  have hd_vec : secVec ψ ⟨(h : G) * (bV : G) * (h : G)⁻¹, hdV⟩ =
      (φ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u := by
    have e := hψ h bV ⟨(h : G) * (bV : G) * (h : G)⁻¹, hdV⟩ rfl
    rw [hbu'] at e
    exact e
  have hd'_vec : secVec ψ ⟨(h' : G) * (b'V : G) * (h' : G)⁻¹, hd'V⟩ =
      c • ((φ h' : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
    have e := hψ h' b'V ⟨(h' : G) * (b'V : G) * (h' : G)⁻¹, hd'V⟩ rfl
    rw [hb'u'] at e
    exact e.trans (Matrix.mulVec_smul _ _ _)
  have hvec : secVec ψ ⟨(h : G) * (bV : G) * (h : G)⁻¹, hdV⟩ =
      secVec ψ ⟨(h' : G) * (b'V : G) * (h' : G)⁻¹, hd'V⟩ := by
    rw [hd_vec, hd'_vec]
    exact hv
  have hz : (h : G) * (bV : G) * (h : G)⁻¹ * ((h' : G) * (b'V : G) * (h' : G)⁻¹)⁻¹ ∈ Z :=
    (secVec_eq_iff ψ _ _).mp hvec
  have hdh' : (h : G) * (bV : G) * (h : G)⁻¹ ∈ conjSubgroup (h' : G) B ⊔ Z := by
    have h1 := (conjSubgroup (h' : G) B ⊔ Z).mul_mem (Subgroup.mem_sup_right hz)
      (Subgroup.mem_sup_left hd'B)
    rwa [inv_mul_cancel_right] at h1
  have hdZ : (h : G) * (bV : G) * (h : G)⁻¹ ∉ Z := by
    intro hz0
    have h0 : secVec ψ ⟨(h : G) * (bV : G) * (h : G)⁻¹, hdV⟩ = 0 :=
      (secVec_eq_zero_iff ψ _).mpr hz0
    rw [hd_vec] at h0
    have hinj : Function.Injective (φ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K).mulVec :=
      Matrix.mulVec_injective_iff_isUnit.mpr (Units.isUnit (φ h))
    have h1 : (φ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u =
        (φ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ 0 := by
      rw [Matrix.mulVec_zero, h0]
    exact hu (hinj h1)
  exact sec8_point_eq (hc := hc) hhM hh'M (Subgroup.mem_sup_left hdB) hdh' hdZ

end

section

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic
open scoped commutatorElement Matrix

section Witt

variable {H : Type} [Group H] {m : ℕ} {K : Type} [Field K]

theorem sec8_witt_pair (φ : H →* GL (Fin m ⊕ Fin m) K) (hφ : φ.range = StatedSp m K)
    {u : Fin m ⊕ Fin m → K} {h₁ h₂ r : H}
    (hr : spForm m K u ((φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0)
    (h12 : spForm m K u ((φ (h₁⁻¹ * h₂) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0) :
    ∃ (h : H) (c : K), c ≠ 0 ∧
      (φ h : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u =
        (φ h₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u ∧
      (φ (h * r) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u =
        c • ((φ h₂ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) := by
  have hAh₁ : φ h₁ ∈ StatedSp m K := by
    rw [← hφ]
    exact ⟨h₁, rfl⟩
  have hfm : spForm m K ((φ h₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)
      ((φ h₂ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) ≠ 0 := by
    have e : φ h₂ = φ h₁ * φ (h₁⁻¹ * h₂) := by rw [← map_mul, mul_inv_cancel_left]
    rw [e, Units.val_mul, ← Matrix.mulVec_mulVec, (mem_statedSp_iff_forall _).mp hAh₁ u _]
    exact h12
  set b := spForm m K u ((φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) with hbdef
  set b' := spForm m K ((φ h₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)
    ((φ h₂ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u) with hb'def
  obtain ⟨A, hA, hAu, hAf⟩ := exists_statedSp_mulVec_pair (m := m) (K := K)
    (e := u) (f := (φ r : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)
    (e' := (φ h₁ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u)
    (f' := (b * b'⁻¹) • ((φ h₂ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ u))
    (by rw [map_smul, smul_eq_mul, mul_assoc, inv_mul_cancel₀ hfm, mul_one]) hr
  obtain ⟨h, hhA⟩ : ∃ h : H, φ h = A := by
    have : A ∈ φ.range := by
      rw [hφ]
      exact hA
    exact MonoidHom.mem_range.mp this
  refine ⟨h, b * b'⁻¹, mul_ne_zero hr (inv_ne_zero hfm), by rw [hhA, hAu], ?_⟩
  rw [map_mul, Units.val_mul, ← Matrix.mulVec_mulVec, hhA, hAf]

end Witt

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec8_canon_hypPlane (h34 : Stroth34Statement) {hc : Ctx M Q Z B} {n : ℕ} {t r : G}
    (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) {g h₁ h₂ : G} (hgM : g ∈ M)
    (hh₁ : h₁ ∈ Rt M (LB M Q B) t) (hh₂ : h₂ ∈ Rt M (LB M Q B) t)
    (hp₁ : conjSubgroup g B ⊔ Z = conjSubgroup h₁ B ⊔ Z)
    (hp₂ : conjSubgroup (g * r) B ⊔ Z = conjSubgroup h₂ B ⊔ Z) :
    HypPlane Q Z B (conjSubgroup (h₁⁻¹ * h₂) B) t := by
  have hrM : r ∈ M := hc.Rt_le_M t hr.mem
  have hh₁M : h₁ ∈ M := hc.Rt_le_M t hh₁
  have hh₂M : h₂ ∈ M := hc.Rt_le_M t hh₂
  have hnpC : ¬ conjSubgroup r B ≤ QB B := (sec8_hypPlane_iff h34 hs hr.mem).mp hr.plane
  have hnp₁ : ¬ conjSubgroup (g * r) B ≤ QB (conjSubgroup g B) := by
    intro h
    apply hnpC
    rw [QB_conj, conjSubgroup_mul] at h
    have h1 : conjSubgroup g⁻¹ (conjSubgroup g (conjSubgroup r B)) ≤
        conjSubgroup g⁻¹ (conjSubgroup g (QB B)) := Subgroup.map_mono h
    rwa [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one, ← conjSubgroup_mul,
      inv_mul_cancel, conjSubgroup_one] at h1
  have hBQ : ∀ m₀ ∈ M, conjSubgroup m₀ B ≤ Q := by
    intro m₀ hm₀
    have h1 : conjSubgroup m₀ B ≤ conjSubgroup m₀ Q := Subgroup.map_mono hc.le
    rwa [hc.conj_Q_eq hm₀] at h1
  have hnp₂ : ¬ conjSubgroup h₂ B ≤ QB (conjSubgroup h₁ B) := fun h =>
    hnp₁ ((sec8_le_QB_iff_of_sup_eq (hc.conj_of_mem hgM) (hc.conj_of_mem hh₁M) hp₁
      (hBQ _ (M.mul_mem hgM hrM)) (hBQ _ hh₂M) hp₂).mpr h)
  have hr'R : h₁⁻¹ * h₂ ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).inv_mem hh₁) hh₂
  refine (sec8_hypPlane_iff h34 hs hr'R).mpr ?_
  intro hle
  apply hnp₂
  have h1 : conjSubgroup h₁ (conjSubgroup (h₁⁻¹ * h₂) B) ≤ conjSubgroup h₁ (QB B) :=
    Subgroup.map_mono hle
  rw [← conjSubgroup_mul, mul_inv_cancel_left, ← QB_conj] at h1
  exact h1

theorem sec8_canon_exists_h (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    {hc : Ctx M Q Z B} {n : ℕ} {t r : G} (hs : Sec8Hyp hc n t) (hr : Sec7A hc t r) {g : G}
    (hgM : g ∈ M) (hgV : g ∈ Subgroup.normalizer (Vt M (LB M Q B) B Z t : Set G)) :
    ∃ h ∈ Rt M (LB M Q B) t, conjSubgroup g B ⊔ Z = conjSubgroup h B ⊔ Z ∧
      conjSubgroup (g * r) B ⊔ Z = conjSubgroup (h * r) B ⊔ Z := by
  classical
  have hs5 := hs.toSec5
  have ht : t ∈ LB M Q B := hs5.mem
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  obtain ⟨m, hm2, hmSp⟩ := hs.sp
  obtain ⟨K, fK, finK, hchar, φ, hn, ψ, u, u', hpts, hhyp, hBiff, hψ, -⟩ :=
    sec8_natdata h34 hRoot hs hr hmSp
  haveI := hn
  haveI := hchar
  have hgVeq : conjSubgroup g (Vt M (LB M Q B) B Z t) = Vt M (LB M Q B) B Z t :=
    sec8_conjSubgroup_eq_of_mem_normalizer hgV
  have hBV : B ≤ Vt M (LB M Q B) B Z t := hc.B_le_Vt ht
  have hCV : conjSubgroup r B ⊔ Z ≤ Vt M (LB M Q B) B Z t := hc.conj_Rt_le_Vt ht hrR
  have hZV : Z ≤ Vt M (LB M Q B) B Z t := sec39_Z_le_Vt
  have hBg : conjSubgroup g B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    refine sup_le ?_ hZV
    have h1 : conjSubgroup g B ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      Subgroup.map_mono hBV
    rwa [hgVeq] at h1
  have hCg : conjSubgroup (g * r) B ⊔ Z ≤ Vt M (LB M Q B) B Z t := by
    refine sup_le ?_ hZV
    have h1 : conjSubgroup g (conjSubgroup r B) ≤ conjSubgroup g (Vt M (LB M Q B) B Z t) :=
      Subgroup.map_mono (le_sup_left.trans hCV)
    rw [hgVeq, ← conjSubgroup_mul] at h1
    exact h1
  obtain ⟨h₁, hh₁, hp₁⟩ := stroth56Sp_holds G M Q Z B hc n t hs g hgM hBg
  obtain ⟨h₂, hh₂, hp₂⟩ := stroth56Sp_holds G M Q Z B hc n t hs (g * r) (M.mul_mem hgM hrM) hCg
  have hplane := sec8_canon_hypPlane h34 hs hr hgM hh₁ hh₂ hp₁ hp₂
  have hr'R : h₁⁻¹ * h₂ ∈ Rt M (LB M Q B) t :=
    (Rt M (LB M Q B) t).mul_mem ((Rt M (LB M Q B) t).inv_mem hh₁) hh₂
  have hb' := (hhyp ⟨h₁⁻¹ * h₂, hr'R⟩).mp hplane
  have hb := (hhyp ⟨r, hrR⟩).mp hr.plane
  obtain ⟨h, c, hc0, hv₁, hv₂⟩ := sec8_witt_pair (h₁ := (⟨h₁, hh₁⟩ : ↥(Rt M (LB M Q B) t)))
    (h₂ := (⟨h₂, hh₂⟩ : ↥(Rt M (LB M Q B) t))) (r := (⟨r, hrR⟩ : ↥(Rt M (LB M Q B) t))) φ
    hpts.range hb hb'
  refine ⟨h, h.2, ?_, ?_⟩
  · exact hp₁.trans (sec8_point_of_vec hs hpts.u_ne_zero ψ hBiff hψ (h := ⟨h₁, hh₁⟩) (h' := h)
      (c := 1) (by rw [one_smul]; exact hv₁.symm))
  · exact hp₂.trans (sec8_point_of_vec hs hpts.u_ne_zero ψ hBiff hψ (h := ⟨h₂, hh₂⟩)
      (h' := h * (⟨r, hrR⟩ : ↥(Rt M (LB M Q B) t))) (c := c⁻¹)
      (by rw [hv₂, smul_smul, inv_mul_cancel₀ hc0, one_smul]))

end

end CFSG.RankThree.GF2n.Stroth80
