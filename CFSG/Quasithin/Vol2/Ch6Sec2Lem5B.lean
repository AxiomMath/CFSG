module

public import CFSG.Quasithin.Vol2.Ch6Sec2Lem5A
public import CFSG.Quasithin.Vol2.Ch6Sec2Lem8A

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

omit [Finite G] in
theorem isSylowIn_conjSubgroup_ch625 {P H : Subgroup G} (hP : IsSylowIn 2 P H) (g : G) :
    IsSylowIn 2 (conjSubgroup P g) (conjSubgroup H g) := by
  refine ⟨conjSubgroup_mono_left g hP.le, hP.isPGroup.map _, ?_⟩
  rw [relIndex_conjSubgroup]
  exact hP.not_dvd_relIndex

namespace Hyp6Sec2

variable (h : Hyp6Sec2 G T M L V)
include h

theorem card_K_ch625 : Nat.card h.data.K = 4 := by
  rw [h.data.card]; norm_num

@[expose] noncomputable def vec625 (w : Fin 2 → h.data.K) : G :=
  ((h.data.E.symm (Multiplicative.ofAdd w) : ↥V) : G)

theorem vec625_add (w w' : Fin 2 → h.data.K) :
    h.vec625 (w + w') = h.vec625 w * h.vec625 w' := by
  simp only [vec625, ofAdd_add, map_mul, Subgroup.coe_mul]

theorem vec625_zero : h.vec625 0 = 1 := by
  simp [vec625]

theorem vec625_injective : Function.Injective h.vec625 := fun w w' hw => by
  have h1 : h.data.E.symm (Multiplicative.ofAdd w) = h.data.E.symm (Multiplicative.ofAdd w') :=
    Subtype.ext hw
  exact Multiplicative.ofAdd.injective (h.data.E.symm.injective h1)

theorem exists_vec625_eq {v : G} (hv : v ∈ V) : ∃ w, h.vec625 w = v :=
  ⟨Multiplicative.toAdd (h.data.E ⟨v, hv⟩), by simp [vec625]⟩

theorem conj_vec625 (m : Subgroup.normalizer (V : Set G)) (w : Fin 2 → h.data.K) :
    (m : G) * h.vec625 w * (m : G)⁻¹ = h.vec625 (h.data.conj m w) := by
  set v : ↥V := h.data.E.symm (Multiplicative.ofAdd w) with hv
  have hw : Multiplicative.toAdd (h.data.E v) = w := by simp [hv]
  have h1 := h.data.conj_apply m v
  rw [hw] at h1
  rw [h1]
  simp only [vec625, ofAdd_toAdd, MulEquiv.symm_apply_apply]
  rw [conjAct_apply_coe]

theorem vec625_mem_conjSubgroup_iff (F : Subgroup G) (m : Subgroup.normalizer (V : Set G))
    (w : Fin 2 → h.data.K) :
    h.vec625 w ∈ conjSubgroup F m ↔ h.vec625 (h.data.conj m w) ∈ F := by
  rw [mem_conjSubgroup_iff, h.conj_vec625]

theorem eq_of_vec625_iff {F F' : Subgroup G} (hF : F ≤ V) (hF' : F' ≤ V)
    (hiff : ∀ w, h.vec625 w ∈ F ↔ h.vec625 w ∈ F') : F = F' := by
  ext g
  constructor
  · intro hg
    obtain ⟨w, rfl⟩ := h.exists_vec625_eq (hF hg)
    exact (hiff w).mp hg
  · intro hg
    obtain ⟨w, rfl⟩ := h.exists_vec625_eq (hF' hg)
    exact (hiff w).mpr hg

@[expose] def IsLine625 (F : Subgroup G) (v : Fin 2 → h.data.K) : Prop :=
  v ≠ 0 ∧ ∀ w, h.vec625 w ∈ F ↔ ∃ c : h.data.K, w = c • v

@[expose] def IsPlane625 (F : Subgroup G) (x y : Fin 2 → h.data.K) : Prop :=
  det2 x y ≠ 0 ∧ ∀ w, h.vec625 w ∈ F ↔ (w = 0 ∨ w = x ∨ w = y ∨ w = x + y)

theorem four_cases_ch625 {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4) :
    (∃ v, h.IsLine625 F v) ∨ (∃ x y, h.IsPlane625 F x y) := by
  have hP : Nat.card (h.data.addSub F) = 4 := by rw [h.data.card_addSub hFV, hF4]
  rcases card_eq_four_cases_ch625 h.card_K_ch625 _ hP with ⟨v, hv, hP'⟩ | ⟨x, y, hxy, hP'⟩
  · exact Or.inl ⟨v, hv, fun w => (h.data.mem_addSub).symm.trans (hP' w)⟩
  · exact Or.inr ⟨x, y, hxy, fun w => (h.data.mem_addSub).symm.trans (hP' w)⟩

theorem not_isLine625_of_isPlane625 {F : Subgroup G} {x y v : Fin 2 → h.data.K}
    (hP : h.IsPlane625 F x y) (hL : h.IsLine625 F v) : False := by
  obtain ⟨c, hc⟩ := (hL.2 x).mp ((hP.2 x).mpr (Or.inr (Or.inl rfl)))
  obtain ⟨d, hd⟩ := (hL.2 y).mp ((hP.2 y).mpr (Or.inr (Or.inr (Or.inl rfl))))
  apply hP.1
  rw [hc, hd, det2_smul_left_ch625, det2_smul_right_ch625, det2_self_ch625, mul_zero, mul_zero]

theorem isPlane625_conjSubgroup {F : Subgroup G} {x y : Fin 2 → h.data.K}
    (hP : h.IsPlane625 F x y) (m : Subgroup.normalizer (V : Set G)) {x' y' : Fin 2 → h.data.K}
    (hx : h.data.conj m x' = x) (hy : h.data.conj m y' = y) (hdet : det2 x' y' ≠ 0) :
    h.IsPlane625 (conjSubgroup F m) x' y' := by
  refine ⟨hdet, fun w => ?_⟩
  rw [h.vec625_mem_conjSubgroup_iff, hP.2]
  have hinj := (h.data.conj m).injective
  constructor
  · rintro (h0 | h0 | h0 | h0)
    · left; apply hinj; rw [h0, map_zero]
    · right; left; apply hinj; rw [h0, hx]
    · right; right; left; apply hinj; rw [h0, hy]
    · right; right; right; apply hinj; rw [h0, map_add, hx, hy]
  · rintro (rfl | rfl | rfl | rfl)
    · left; exact map_zero _
    · right; left; exact hx
    · right; right; left; exact hy
    · right; right; right; rw [map_add, hx, hy]

theorem isLine625_conjSubgroup {F : Subgroup G} {v : Fin 2 → h.data.K} (hL : h.IsLine625 F v)
    (m : Subgroup.normalizer (V : Set G)) {σ : h.data.K ≃+* h.data.K}
    (hσ : ∀ (c : h.data.K) w, h.data.conj m (c • w) = σ c • h.data.conj m w)
    {v' : Fin 2 → h.data.K} (hv : h.data.conj m v' = v) :
    h.IsLine625 (conjSubgroup F m) v' := by
  have hv0 : v' ≠ 0 := by
    rintro rfl
    rw [map_zero] at hv
    exact hL.1 hv.symm
  refine ⟨hv0, fun w => ?_⟩
  rw [h.vec625_mem_conjSubgroup_iff, hL.2]
  constructor
  · rintro ⟨c, hc⟩
    refine ⟨σ.symm c, (h.data.conj m).injective ?_⟩
    rw [hc, hσ, hv, RingEquiv.apply_symm_apply]
  · rintro ⟨c, rfl⟩
    exact ⟨σ c, by rw [hσ, hv]⟩

theorem exists_isLine625_ZS : ∃ v, h.IsLine625 (ch6ZS T L V) v := by
  obtain ⟨v, hv, hle⟩ := h.toHyp611Nat.exists_line
  refine ⟨v, hv, fun w => ?_⟩
  have := h.toHyp611Nat.mem_ZS_iff_line hv hle (h.data.E.symm (Multiplicative.ofAdd w))
  simpa [vec625] using this

theorem exists_conj_ZS_of_isLine625 {F : Subgroup G} (hFV : F ≤ V) {v : Fin 2 → h.data.K}
    (hL : h.IsLine625 F v) : ∃ l ∈ L, F = conjSubgroup (ch6ZS T L V) l := by
  refine h.toHyp611Nat.exists_conj_ZS_of_line hFV hL.1 fun u hu => ?_
  obtain ⟨w, rfl⟩ := h.exists_vec625_eq hu
  have e : Multiplicative.toAdd (h.data.E ⟨h.vec625 w, hu⟩) = w := by simp [vec625]
  rw [e, hL.2]

theorem exists_isLine625_conj_ZS {l : G} (hl : l ∈ L) :
    ∃ v, h.IsLine625 (conjSubgroup (ch6ZS T L V) l) v := by
  obtain ⟨v, hv⟩ := h.exists_isLine625_ZS
  set m : Subgroup.normalizer (V : Set G) := ⟨l, h.toHyp611.L_le_normalizer hl⟩ with hm
  obtain ⟨A, hA⟩ := h.data.exists_matrix_of_mem m hl
  set v' := (h.data.conj m).symm v with hv'
  refine ⟨v', h.isLine625_conjSubgroup hv m (σ := RingEquiv.refl _) (fun c w => ?_) ?_⟩
  · rw [hA, hA, Matrix.mulVec_smul]
    rfl
  · rw [hv', AddEquiv.apply_symm_apply]

theorem isCentralType_iff_ch625 {F : Subgroup G} (hFV : F ≤ V) (hF4 : Nat.card F = 4) :
    IsCentralType L V F 1 ↔ ∃ l ∈ L, F = conjSubgroup (ch6ZS T L V) l := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTL := h.toHyp611.isSylowIn_TL
  constructor
  · rintro ⟨-, -, P, hP, hPC⟩
    rw [conjSubgroup_one] at hP
    obtain ⟨x, hx, hPx⟩ := F7.isSylowTwoOf_exists_conj_le hTL hP.le hP.isPGroup
    have hcard : Nat.card (conjSub x (T ⊓ L)) ≤ Nat.card P := by
      rw [CosetGeom.card_conjSub]
      exact card_le_of_isSylowIn_ch62 hP inf_le_right (h.sylow.1.to_le inf_le_left)
    have hPeq := Subgroup.eq_of_le_of_card_ge hPx hcard
    have hxV : x ∈ Subgroup.normalizer (V : Set G) := h.toHyp611.L_le_normalizer hx
    have hle : F ≤ conjSub x (ch6ZS T L V) := by
      intro f hf
      rw [mem_conjSub]
      have hfV : x⁻¹ * f * x ∈ V := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxV) f).mp (hFV hf)
        simpa using this
      refine ⟨hfV, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
      have hz' : x * z * x⁻¹ ∈ P := by
        rw [hPeq, mem_conjSub]
        simpa [mul_assoc] using hz
      have h1 := Subgroup.mem_centralizer_iff.mp (hPC hz') f hf
      calc z * (x⁻¹ * f * x) = x⁻¹ * ((x * z * x⁻¹) * f) * x := by group
        _ = x⁻¹ * (f * (x * z * x⁻¹)) * x := by rw [h1]
        _ = x⁻¹ * f * x * z := by group
    have hZ4 : Nat.card (conjSub x (ch6ZS T L V)) = 4 := by
      rw [CosetGeom.card_conjSub, h.card_ZS_four]
    refine ⟨x⁻¹, L.inv_mem hx, ?_⟩
    rw [← conjSub_eq_conjSubgroup_ch62]
    exact Subgroup.eq_of_le_of_card_ge hle (by rw [hZ4, hF4])
  · rintro ⟨l, hl, rfl⟩
    refine ⟨by rw [conjSubgroup_one]; exact hFV, hF4, conjSubgroup (T ⊓ L) l, ?_, ?_⟩
    · rw [conjSubgroup_one]
      have hLl : conjSubgroup L l = L :=
        conjSubgroup_eq_iff_mem_normalizer.mpr (Subgroup.le_normalizer hl)
      have := isSylowIn_conjSubgroup_ch625 hTL l
      rwa [hLl] at this
    · intro p hp
      rw [mem_conjSubgroup_iff] at hp
      refine Subgroup.mem_centralizer_iff.mpr fun f hf => ?_
      have hf' : l * f * l⁻¹ ∈ ch6ZS T L V := mem_conjSubgroup_iff.mp hf
      have h1 := Subgroup.mem_centralizer_iff.mp hf'.2 _ hp
      calc f * p = l⁻¹ * ((l * f * l⁻¹) * (l * p * l⁻¹)) * l := by group
        _ = l⁻¹ * ((l * p * l⁻¹) * (l * f * l⁻¹)) * l := by rw [← h1]
        _ = p * f := by group

end Hyp6Sec2

end CFSG.Quasithin.H13
