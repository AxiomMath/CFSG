module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5PCore
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3Star

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P55

theorem valence_smul' (F : FanTree Γ G) (g : G) (v : V) :
    valence Γ (g • v) = valence Γ v := by
  unfold valence
  refine Nat.card_congr (Equiv.subtypeEquiv (MulAction.toPerm g⁻¹) fun w => ?_)
  have := F.adj_smul g⁻¹ (g • v) w
  simp only [inv_smul_smul] at this
  simp only [mem_neighborSet, MulAction.toPerm_apply]
  exact this.symm

theorem Gcirc_conj_iff (F : FanTree Γ G) (g k : G) (α β : V) :
    g * k * g⁻¹ ∈ Gcirc Γ G (g • α) (g • β) ↔ k ∈ Gcirc Γ G α β := by
  have hst : ∀ v : V, (g * k * g⁻¹) • (g • v) = g • v ↔ k • v = v := by
    intro v
    simp only [mul_smul, inv_smul_smul]
    exact (MulAction.injective g).eq_iff
  have hnb : g * k * g⁻¹ * (g * k * g⁻¹) ∈ nbrStab Γ G (g • α) ↔ k * k ∈ nbrStab Γ G α := by
    rw [F.mem_nbrStab_smul_iff g α, show g * k * g⁻¹ * (g * k * g⁻¹) = g * (k * k) * g⁻¹ by group]
    simp [mul_assoc]
  simp only [mem_Gcirc, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rw [hst α, hst β, hnb]

theorem cen_conj_iff {S S' : Set G} (g : G) (hS : ∀ k, g * k * g⁻¹ ∈ S' ↔ k ∈ S) (z : G) :
    g * z * g⁻¹ ∈ Cen S' ↔ z ∈ Cen S := by
  show (g * z * g⁻¹ ∈ S' ∧ ∀ h ∈ S', h * (g * z * g⁻¹) = g * z * g⁻¹ * h) ↔
    (z ∈ S ∧ ∀ h ∈ S, h * z = z * h)
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨(hS z).1 h1, fun h hh => ?_⟩
    have e := h2 (g * h * g⁻¹) ((hS h).2 hh)
    calc h * z = g⁻¹ * (g * h * g⁻¹ * (g * z * g⁻¹)) * g := by group
      _ = g⁻¹ * (g * z * g⁻¹ * (g * h * g⁻¹)) * g := by rw [e]
      _ = z * h := by group
  · rintro ⟨h1, h2⟩
    refine ⟨(hS z).2 h1, fun h' hh' => ?_⟩
    have hh : g⁻¹ * h' * g ∈ S := (hS _).1 (by simpa [mul_assoc] using hh')
    have e := h2 _ hh
    calc h' * (g * z * g⁻¹) = g * (g⁻¹ * h' * g * z) * g⁻¹ := by group
      _ = g * (z * (g⁻¹ * h' * g)) * g⁻¹ := by rw [e]
      _ = g * z * g⁻¹ * h' := by group

theorem sq_conj (g : G) {z : G} (hz : z * z = 1) : g * z * g⁻¹ * (g * z * g⁻¹) = 1 := by
  calc g * z * g⁻¹ * (g * z * g⁻¹) = g * (z * z) * g⁻¹ := by group
    _ = 1 := by rw [hz]; group

variable (ℓ : Line Γ)

@[expose] def IsShift (g : G) (s : ℤ) : Prop := ∀ i, g • ℓ.vert i = ℓ.vert (i + s)

variable {ℓ}

theorem mem_edgeCirc_of_fix {i : ℤ} {g : G} (hgg : g * g = 1) (h0 : g • ℓ.vert i = ℓ.vert i)
    (h1 : g • ℓ.vert (i + 1) = ℓ.vert (i + 1)) : g ∈ ℓ.edgeCirc (G := G) i := by
  by_cases h5 : valence Γ (ℓ.vert i) = 5
  · rw [ℓ.edgeCirc_of_five h5]
    exact ⟨⟨MulAction.mem_stabilizer_iff.2 h0, MulAction.mem_stabilizer_iff.2 h1⟩,
      hgg ▸ (nbrStab Γ G _).one_mem⟩
  · rw [ℓ.edgeCirc_of_ne_five h5]
    exact ⟨⟨MulAction.mem_stabilizer_iff.2 h1, MulAction.mem_stabilizer_iff.2 h0⟩,
      hgg ▸ (nbrStab Γ G _).one_mem⟩

section Transport

variable (F : FanTree Γ G) {g : G} {s : ℤ} (hg : IsShift ℓ g s)
include F hg

theorem IsShift.edgeCirc_iff (i : ℤ) (k : G) :
    g * k * g⁻¹ ∈ ℓ.edgeCirc (G := G) (i + s) ↔ k ∈ ℓ.edgeCirc (G := G) i := by
  have hv : valence Γ (ℓ.vert (i + s)) = valence Γ (ℓ.vert i) := by
    rw [← hg i]; exact P55.valence_smul' F g _
  have h1 : ℓ.vert (i + s) = g • ℓ.vert i := (hg i).symm
  have h2 : ℓ.vert (i + s + 1) = g • ℓ.vert (i + 1) := by
    rw [show i + s + 1 = i + 1 + s by ring]; exact (hg (i + 1)).symm
  by_cases h5 : valence Γ (ℓ.vert i) = 5
  · rw [ℓ.edgeCirc_of_five h5, ℓ.edgeCirc_of_five (hv.trans h5), h1, h2]
    exact P55.Gcirc_conj_iff F g k _ _
  · rw [ℓ.edgeCirc_of_ne_five h5, ℓ.edgeCirc_of_ne_five (by rwa [hv]), h1, h2]
    exact P55.Gcirc_conj_iff F g k _ _

omit F in
theorem IsShift.edgeStab_iff (i : ℤ) (k : G) :
    g * k * g⁻¹ ∈ (ℓ.edgeStab (G := G) (i + s) : Set G) ↔ k ∈ (ℓ.edgeStab (G := G) i : Set G) := by
  have h1 : ℓ.vert (i + s) = g • ℓ.vert i := (hg i).symm
  have h2 : ℓ.vert (i + s + 1) = g • ℓ.vert (i + 1) := by
    rw [show i + s + 1 = i + 1 + s by ring]; exact (hg (i + 1)).symm
  have hst : ∀ v : V, (g * k * g⁻¹) • (g • v) = g • v ↔ k • v = v := by
    intro v
    simp only [mul_smul, inv_smul_smul]
    exact (MulAction.injective g).eq_iff
  simp only [Line.edgeStab, SetLike.mem_coe, Subgroup.mem_inf, MulAction.mem_stabilizer_iff]
  rw [h1, h2, hst, hst]

omit F in
theorem IsShift.mem_fixIdx_iff (z : G) (i : ℤ) :
    i + s ∈ ℓ.fixIdx (g * z * g⁻¹) ↔ i ∈ ℓ.fixIdx z := by
  show (g * z * g⁻¹) • ℓ.vert (i + s) = ℓ.vert (i + s) ↔ z • ℓ.vert i = ℓ.vert i
  rw [← hg i]
  constructor
  · intro h
    have : g • (z • ℓ.vert i) = g • ℓ.vert i := by simpa [mul_smul] using h
    exact MulAction.injective g this
  · intro h
    simp [mul_smul, h]

omit F in
theorem IsShift.isCoreWith {P P' : ℤ → Prop} (hP : ∀ i, P' (i + s) ↔ P i) {z : G} {a b : ℤ}
    (h : ℓ.IsCoreWith P z a b) : ℓ.IsCoreWith P' (g * z * g⁻¹) (a + s) (b + s) := by
  obtain ⟨hab, hfix, hP1, hna, hnb⟩ := h
  have hf : ∀ i, i ∈ ℓ.fixIdx (g * z * g⁻¹) ↔ i - s ∈ ℓ.fixIdx z := by
    intro i
    have := IsShift.mem_fixIdx_iff hg z (i - s)
    rwa [show i - s + s = i by omega] at this
  have hp : ∀ i, P' i ↔ P (i - s) := by
    intro i
    have := hP (i - s)
    rwa [show i - s + s = i by omega] at this
  refine ⟨by omega, fun i h1 h2 => (hf i).2 (hfix _ (by omega) (by omega)),
    fun i h1 h2 => (hp i).2 (hP1 _ (by omega) (by omega)), ?_, ?_⟩
  · rintro ⟨h1, h2⟩
    rw [hf] at h1
    rw [hp] at h2
    exact hna ⟨by simpa [sub_right_comm] using h1, by simpa [sub_right_comm] using h2⟩
  · rintro ⟨h1, h2⟩
    rw [hf] at h1
    rw [hp] at h2
    exact hnb ⟨by simpa using h1, by simpa using h2⟩

theorem IsShift.cen_edgeCirc_iff (z : G) (i : ℤ) :
    g * z * g⁻¹ ∈ Cen (ℓ.edgeCirc (G := G) (i + s)) ↔ z ∈ Cen (ℓ.edgeCirc (G := G) i) :=
  P55.cen_conj_iff g (fun k => IsShift.edgeCirc_iff F hg i k) z

omit F in
theorem IsShift.cen_edgeStab_iff (z : G) (i : ℤ) :
    g * z * g⁻¹ ∈ Cen (ℓ.edgeStab (G := G) (i + s) : Set G) ↔
      z ∈ Cen (ℓ.edgeStab (G := G) i : Set G) :=
  P55.cen_conj_iff g (fun k => IsShift.edgeStab_iff hg i k) z

theorem IsShift.zc {z : G} (hz : z ∈ ℓ.Zc) : g * z * g⁻¹ ∈ ℓ.Zc := by
  obtain ⟨hz2, i, hi⟩ := hz
  exact ⟨P55.sq_conj g hz2, i + s, (IsShift.cen_edgeCirc_iff F hg z i).2 hi⟩

omit F in
theorem IsShift.zz {z : G} (hz : z ∈ ℓ.ZZ) : g * z * g⁻¹ ∈ ℓ.ZZ := by
  obtain ⟨hz2, i, hi⟩ := hz
  exact ⟨P55.sq_conj g hz2, i + s, (IsShift.cen_edgeStab_iff hg z i).2 hi⟩

theorem IsShift.isCoreC {z : G} {a b : ℤ} (h : ℓ.IsCoreC z a b) :
    ℓ.IsCoreC (g * z * g⁻¹) (a + s) (b + s) :=
  IsShift.isCoreWith hg (fun i => IsShift.cen_edgeCirc_iff F hg z i) h

omit F in
theorem IsShift.isCore {z : G} {a b : ℤ} (h : ℓ.IsCore z a b) :
    ℓ.IsCore (g * z * g⁻¹) (a + s) (b + s) :=
  IsShift.isCoreWith hg (fun i => IsShift.cen_edgeStab_iff hg z i) h

theorem IsShift.isCoreCFix {z : G} {a b tL tR : ℤ} (h : ℓ.IsCoreCFix z a b tL tR) :
    ℓ.IsCoreCFix (g * z * g⁻¹) (a + s) (b + s) (tL + s) (tR + s) where
  fix i := by
    have h1 := IsShift.mem_fixIdx_iff hg z (i - s)
    rw [show i - s + s = i by omega] at h1
    rw [h1, h.fix]
    omega
  core := IsShift.isCoreC F hg h.core

omit F in
theorem IsShift.isCoreFix {z : G} {a b tL tR : ℤ} (h : ℓ.IsCoreFix z a b tL tR) :
    ℓ.IsCoreFix (g * z * g⁻¹) (a + s) (b + s) (tL + s) (tR + s) where
  fix i := by
    have h1 := IsShift.mem_fixIdx_iff hg z (i - s)
    rw [show i - s + s = i by omega] at h1
    rw [h1, h.fix]
    omega
  core := IsShift.isCore hg h.core

end Transport

variable {ℓ : Line Γ} {z : G} {a b tL tR : ℤ}

theorem cfix_a_lt (h : ℓ.IsCoreCFix z a b tL tR) : a < b := h.core.1

theorem cfix_tL_le (h : ℓ.IsCoreCFix z a b tL tR) : tL ≤ a :=
  ((h.fix a).1 (h.core.2.1 a le_rfl h.core.1.le)).1

theorem cfix_le_tR (h : ℓ.IsCoreCFix z a b tL tR) : b ≤ tR :=
  ((h.fix b).1 (h.core.2.1 b h.core.1.le le_rfl)).2

theorem cfix_cen {i : ℤ} (h : ℓ.IsCoreCFix z a b tL tR) (h1 : a ≤ i) (h2 : i < b) :
    z ∈ Cen (ℓ.edgeCirc (G := G) i) := h.core.2.2.1 i h1 h2

theorem fix_a_lt (h : ℓ.IsCoreFix z a b tL tR) : a < b := h.core.1

theorem fix_tL_le (h : ℓ.IsCoreFix z a b tL tR) : tL ≤ a :=
  ((h.fix a).1 (h.core.2.1 a le_rfl h.core.1.le)).1

theorem fix_le_tR (h : ℓ.IsCoreFix z a b tL tR) : b ≤ tR :=
  ((h.fix b).1 (h.core.2.1 b h.core.1.le le_rfl)).2

end P55

end CFSG.Quasithin.Fan86
