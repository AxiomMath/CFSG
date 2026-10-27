module

public import CFSG.Quasithin.Vol2.GoldschmidtF431Setting

public section

namespace CFSG.Quasithin.H13.F48Rig

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13.F431 CFSG.Quasithin.RankTwoAmalgam.Completion

section Parabolic

variable {D : Type} [Group D]

theorem normalizer_eq_of_maximalTwoLocal [Finite D] {M : Subgroup D} (hM : IsMaximalTwoLocal M) :
    Subgroup.normalizer (M : Set D) = M := by
  obtain ⟨⟨U, hU0, hUp, hMU⟩, hmax⟩ := hM
  have hUle : U ≤ pCoreOf 2 M := by
    have := CFSG.LieType.BorelTits.le_pCoreOf_normalizer 2 U hUp
    rwa [← hMU] at this
  have hP0 : pCoreOf 2 M ≠ ⊥ := fun h => hU0 (le_bot_iff.mp (h ▸ hUle))
  have hPp : IsPGroup 2 (pCoreOf 2 M) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have h1 : M ≤ Subgroup.normalizer (pCoreOf 2 M : Set D) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have h2 := hmax _ ⟨_, hP0, hPp, rfl⟩ h1
  refine le_antisymm ?_ Subgroup.le_normalizer
  calc Subgroup.normalizer (M : Set D)
      ≤ Subgroup.normalizer (pCoreOf 2 M : Set D) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M
    _ = M := h2

theorem normalizer_P1 [Finite D] (A : LieAmalgamExt D) :
    Subgroup.normalizer (A.P1 : Set D) = A.P1 :=
  normalizer_eq_of_maximalTwoLocal ((A.yam.2.2 A.P1).mpr (Or.inl rfl)).1

theorem normalizer_P2 [Finite D] (A : LieAmalgamExt D) :
    Subgroup.normalizer (A.P2 : Set D) = A.P2 :=
  normalizer_eq_of_maximalTwoLocal ((A.yam.2.2 A.P2).mpr (Or.inr rfl)).1

theorem conj_mem_autStab_iff (P : Subgroup D) (e : D) :
    (MulAut.conj e : MulAut D) ∈ autStab P ↔ e ∈ Subgroup.normalizer (P : Set D) := by
  rw [Subgroup.mem_normalizer_iff]
  exact ⟨fun h x => by simpa [MulAut.conj_apply] using h x,
    fun h x => by simpa [MulAut.conj_apply] using h x⟩

theorem mulAut_mul_conj_mul_inv (φ : MulAut D) (d : D) :
    φ * MulAut.conj d * φ⁻¹ = MulAut.conj (φ d) := by
  ext z
  simp [MulAut.conj_apply]

end Parabolic

section Setting

variable {D : Type} [Group D] (A : LieAmalgamExt D) (hfin : Finite D) (pm : ℕ) (hpm : 3 ≤ pm)

@[expose] noncomputable def toK (n : (A.setting hfin pm hpm).ι.G0) : ↥A.K :=
  (A.ι0.φ1.range ⊔ A.ι0.φ2.range).subtype n

@[expose] noncomputable def extNu : (A.setting hfin pm hpm).N →* ↥A.K :=
  (A.ι0.φ1.range ⊔ A.ι0.φ2.range).subtype.comp (A.setting hfin pm hpm).N.subtype

theorem mem_G0 (k : ↥A.K) : k ∈ A.ι0.φ1.range ⊔ A.ι0.φ2.range := by
  rw [A.ι0.gen]
  exact Subgroup.mem_top k

theorem mem_range_extNu {k : ↥A.K} :
    k ∈ (extNu A hfin pm hpm).range ↔ (k : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range := by
  constructor
  · rintro ⟨n, rfl⟩
    exact n.2
  · intro hk
    exact ⟨⟨⟨k, mem_G0 A k⟩, hk⟩, rfl⟩

theorem mem_stv_xv (n : (A.setting hfin pm hpm).ι.G0) :
    n ∈ stv (A.setting hfin pm hpm).ι (A.setting hfin pm hpm).ι.xv ↔
      ((toK A hfin pm hpm n : ↥A.K) : MulAut D) ∈ A.N1 := by
  rw [stv_xv_eq_range]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨(toK A hfin pm hpm n).1, h⟩, Subtype.ext (Subtype.ext rfl)⟩

theorem mem_stv_lv (n : (A.setting hfin pm hpm).ι.G0) :
    n ∈ stv (A.setting hfin pm hpm).ι (A.setting hfin pm hpm).ι.lv ↔
      ((toK A hfin pm hpm n : ↥A.K) : MulAut D) ∈ A.N2 := by
  have hr : stv (A.setting hfin pm hpm).ι (A.setting hfin pm hpm).ι.lv =
      (f2 (c := (A.setting hfin pm hpm).ι)).range :=
    le_antisymm (stv_lv_le_range_f2 _) (by
      rintro _ ⟨a, rfl⟩
      exact MulAction.mem_stabilizer_iff.mpr (f2_smul_lv a))
  rw [hr]
  constructor
  · rintro ⟨a, rfl⟩
    exact a.2
  · intro h
    exact ⟨⟨(toK A hfin pm hpm n).1, h⟩, Subtype.ext (Subtype.ext rfl)⟩

@[expose] def extX1 : Subgroup ↥A.K :=
  ((MulAut.conj : D →* MulAut D).range.comap A.K.subtype) ⊓ A.N1.comap A.K.subtype

@[expose] def extX12 : Subgroup ↥A.K :=
  ((MulAut.conj : D →* MulAut D).range.comap A.K.subtype) ⊓ (A.N1 ⊓ A.N2).comap A.K.subtype

theorem map_N1_eq : (A.setting hfin pm hpm).N1.map (extNu A hfin pm hpm) = extX1 A := by
  ext k
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, (mem_stv_xv A hfin pm hpm n.1).mp hn⟩
  · rintro ⟨hI, h1⟩
    exact ⟨⟨⟨k, mem_G0 A k⟩, hI⟩, (mem_stv_xv A hfin pm hpm ⟨k, mem_G0 A k⟩).mpr h1, rfl⟩

theorem map_N12_eq : (A.setting hfin pm hpm).N12.map (extNu A hfin pm hpm) = extX12 A := by
  ext k
  constructor
  · rintro ⟨n, hn, rfl⟩
    exact ⟨n.2, (mem_stv_xv A hfin pm hpm n.1).mp hn.1, (mem_stv_lv A hfin pm hpm n.1).mp hn.2⟩
  · rintro ⟨hI, h1, h2⟩
    exact ⟨⟨⟨k, mem_G0 A k⟩, hI⟩, ⟨(mem_stv_xv A hfin pm hpm ⟨k, mem_G0 A k⟩).mpr h1,
      (mem_stv_lv A hfin pm hpm ⟨k, mem_G0 A k⟩).mpr h2⟩, rfl⟩

theorem conj_injective_of_center {D : Type} [Group D] (hZ : Subgroup.center D = ⊥) :
    Function.Injective (MulAut.conj : D →* MulAut D) := by
  intro a b h
  have hc : b⁻¹ * a ∈ Subgroup.center D := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 : (MulAut.conj (b⁻¹ * a) : MulAut D) = 1 := by
      rw [map_mul, map_inv, h, inv_mul_cancel]
    have h3 := congrArg (fun φ : MulAut D => φ y) h2
    simp only [MulAut.conj_apply, MulAut.one_apply] at h3
    calc y * (b⁻¹ * a) = (b⁻¹ * a * y * (b⁻¹ * a)⁻¹) * (b⁻¹ * a) := by rw [h3]
      _ = (b⁻¹ * a) * y := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hc
  exact hc.symm

variable (hZ : Subgroup.center D = ⊥) (hgen : (MulAut.conj : D →* MulAut D).range ≤ A.K)

include hfin hZ hgen in
theorem centralizer_extNu :
    Subgroup.centralizer ((extNu A hfin pm hpm).range : Set ↥A.K) = ⊥ := by
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  refine MulEquiv.ext fun d => ?_
  have hy : (⟨MulAut.conj d, hgen ⟨d, rfl⟩⟩ : ↥A.K) ∈ (extNu A hfin pm hpm).range :=
    (mem_range_extNu A hfin pm hpm).mpr ⟨d, rfl⟩
  have h1 := congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hk _ hy)
  have h2 : (k : MulAut D) * MulAut.conj d * (k : MulAut D)⁻¹ = MulAut.conj d := by
    have h1' : MulAut.conj d * (k : MulAut D) = (k : MulAut D) * MulAut.conj d := h1
    rw [← h1']
    group
  rw [mulAut_mul_conj_mul_inv] at h2
  exact conj_injective_of_center hZ h2

include hfin hZ hgen in
theorem isExtension_setting : (A.setting hfin pm hpm).IsExtension ↥A.K := by
  have : Finite D := hfin
  refine ⟨extNu A hfin pm hpm, ?_, ?_, centralizer_extNu A hfin pm hpm hZ hgen, ?_⟩
  · exact (Subgroup.subtype_injective _).comp (Subgroup.subtype_injective _)
  · refine ⟨fun x hx g => ?_⟩
    rw [mem_range_extNu] at hx ⊢
    exact (innRange_normal (D := D)).conj_mem _ hx g.1
  · intro g hg
    rw [map_N12_eq] at hg
    rw [map_N1_eq]
    have hgM : (g : MulAut D) ∈ A.Mbar :=
      (sup_le inf_le_left inf_le_left : A.K ≤ A.Mbar) g.2
    let ke : D → ↥A.K := fun e => ⟨MulAut.conj e, hgen ⟨e, rfl⟩⟩
    have hke : ∀ e : D, ke e ∈ extX12 A ↔ e ∈ A.P1 ⊓ A.P2 := fun e => by
      have h1 : (MulAut.conj e : MulAut D) ∈ A.N1 ↔ e ∈ A.P1 := by
        rw [LieAmalgamExt.N1, Subgroup.mem_inf, conj_mem_autStab_iff, normalizer_P1 A]
        exact ⟨fun h => h.2, fun h => ⟨A.inn_le ⟨e, rfl⟩, h⟩⟩
      have h2 : (MulAut.conj e : MulAut D) ∈ A.N2 ↔ e ∈ A.P2 := by
        rw [LieAmalgamExt.N2, Subgroup.mem_inf, conj_mem_autStab_iff, normalizer_P2 A]
        exact ⟨fun h => h.2, fun h => ⟨A.inn_le ⟨e, rfl⟩, h⟩⟩
      show ((MulAut.conj e : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range ∧
        ((MulAut.conj e : MulAut D) ∈ A.N1 ⊓ A.N2)) ↔ _
      rw [Subgroup.mem_inf (x := e), Subgroup.mem_inf (x := (MulAut.conj e : MulAut D)), h1, h2]
      exact ⟨fun h => h.2, fun h => ⟨⟨e, rfl⟩, h⟩⟩
    have hconj : ∀ d : D, g * ke d * g⁻¹ = ke (g.1 d) := fun d =>
      Subtype.ext (mulAut_mul_conj_mul_inv (g : MulAut D) d)
    have hstab : (g : MulAut D) ∈ autStab (A.P1 ⊓ A.P2) := fun d =>
      (hke d).symm.trans ((Subgroup.mem_normalizer_iff.mp hg (ke d)).trans
        (by rw [hconj d]; exact hke (g.1 d)))
    have hP1 : (g : MulAut D) ∈ autStab A.P1 := A.diag g.1 hgM hstab
    have hgN1 : (g : MulAut D) ∈ A.N1 := ⟨hgM, hP1⟩
    refine Subgroup.mem_normalizer_iff.mpr fun k => ?_
    have hI : (k : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range ↔
        ((g * k * g⁻¹ : ↥A.K) : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range := by
      constructor
      · intro h
        exact (innRange_normal (D := D)).conj_mem _ h g.1
      · intro h
        have := (innRange_normal (D := D)).conj_mem _ h (g.1)⁻¹
        simpa [mul_assoc] using this
    have hN : (k : MulAut D) ∈ A.N1 ↔ ((g * k * g⁻¹ : ↥A.K) : MulAut D) ∈ A.N1 := by
      constructor
      · intro h
        exact A.N1.mul_mem (A.N1.mul_mem hgN1 h) (A.N1.inv_mem hgN1)
      · intro h
        have := A.N1.mul_mem (A.N1.mul_mem (A.N1.inv_mem hgN1) h) hgN1
        simpa [mul_assoc] using this
    exact ⟨fun h => ⟨hI.mp h.1, hN.mp h.2⟩, fun h => ⟨hI.mpr h.1, hN.mpr h.2⟩⟩

end Setting

end CFSG.Quasithin.H13.F48Rig
