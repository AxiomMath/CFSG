module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8T5

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

section Outer

variable (c : AutCtx G M₁ M₂ z) {R : Subgroup G}

@[expose] def Eg (c : AutCtx G M₁ M₂ z) : Subgroup G := (M₁ ⊔ M₂) ⊓ cenOf (c.iso.toG fhB)

theorem TfG_le_Eg : TfG c ≤ Eg c :=
  le_inf ((TfG_le_M1 c).trans le_sup_left) (TfG_le_cen c)

theorem Eg_le_cen : Eg c ≤ cenOf (c.iso.toG fhB) := inf_le_right

theorem isSylowTwoOf_Tf_Eg (hE : Nat.card ↥(Eg c) = 1440) : IsSylowTwoOf (TfG c) (Eg c) := by
  refine isSylowTwoOf_of_card_eq (TfG_le_Eg c)
    (IsPGroup.of_card (n := 5) (by rw [card_TfG]; norm_num)) ?_
  rw [twoPart_eq_of_card_eq (k := 5) (m := 45) (by norm_num) (by rw [hE]; norm_num), card_TfG]
  norm_num

theorem E_counts (h : F55Ctx c R) (hE : Nat.card ↥(Eg c) = 1440) :
    Set.ncard {x : G | x ∈ R ∧ x ∈ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x z} ≤ 11 ∧
    Set.ncard {x : G | x ∈ R ∧ x ∈ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧
      IsConj x (c.iso.toG fhB)} ≤ 12 := by
  set F := c.iso.toG fhB with hF
  have hS := isSylowTwoOf_Tf_Eg c hE
  have hRg : IsPGroup 2 ↥(R ⊓ Eg c) :=
    (IsPGroup.of_card (n := 6) h.hR64 : IsPGroup 2 ↥R).to_le inf_le_left
  obtain ⟨e, -, hle⟩ := F7.isSylowTwoOf_exists_conj_le hS (inf_le_right : R ⊓ Eg c ≤ Eg c) hRg
  obtain ⟨kf, hkf, hkfL, hzkf⟩ := exists_kf
  have hkfF : ivG c kf = F := by
    have hA : ivA kf = fhatA := Subtype.ext (eq_of_repL (ivA_spec hkf).2 (by
      rw [hkfL]
      exact repL_fhat))
    have hB : ivB kf = fhB := Subtype.ext ((ivB_coe hkf).trans (hA.trans coe_fhB.symm))
    rw [ivG, hB]
  have key : ∀ x : G, x ∈ R → x ∈ Eg c → x * x = 1 → x ≠ 1 →
      ∃ j ∈ JC kf, ivG c j = e⁻¹ * x * e⁻¹⁻¹ := by
    intro x hxR hxE hx2 hx1
    have hxT : e⁻¹ * x * e ∈ TfG c := B6.mem_conjSub.1 (hle ⟨hxR, hxE⟩)
    have hy2 : (e⁻¹ * x * e) * (e⁻¹ * x * e) = 1 := by
      calc (e⁻¹ * x * e) * (e⁻¹ * x * e) = e⁻¹ * (x * x) * e := by group
        _ = 1 := by rw [hx2]; group
    have hy1 : e⁻¹ * x * e ≠ 1 := by
      intro h1
      apply hx1
      have : x = e * (e⁻¹ * x * e) * e⁻¹ := by group
      rw [this, h1]
      group
    obtain ⟨j, hj, hjy⟩ := exists_ivG c hxT.1 hy2 hy1
    refine ⟨j, mem_JC.2 ⟨hj, ?_⟩, by rw [hjy]; simp⟩
    rw [← ivG_comm_iff c hj hkf, hjy, hkfF]
    have hF' : e⁻¹ * x * e * F = F * (e⁻¹ * x * e) :=
      Subgroup.mem_centralizer_singleton_iff.1 hxT.2
    exact hF'
  have hconj : ∀ (w x : G) (j : ℕ), ivG c j = e⁻¹ * x * e⁻¹⁻¹ → IsConj x w →
      IsConj (ivG c j) w := by
    intro w x j hj hxw
    have := isConj_conj_self e⁻¹ x
    rw [← hj] at this
    exact this.trans hxw
  constructor
  · refine le_trans (ncard_le_of_idx c _ e⁻¹ (JZ kf) (JZ_nodup kf) ?_) (count_Tf kf hkf hkfL).1
    rintro x ⟨hxR, hxE, hx2, hx1, hxz⟩
    obtain ⟨j, hjC, hj⟩ := key x hxR hxE hx2 hx1
    refine ⟨j, mem_JZ.2 ⟨hjC, ?_⟩, hj⟩
    exact (ivG_conj_z_iff c h (mem_JC.1 hjC).1).1 (hconj z x j hj hxz)
  · refine le_trans (ncard_le_of_idx c _ e⁻¹ (JP kf) (JP_nodup kf) ?_) (count_Tf kf hkf hkfL).2
    rintro x ⟨hxR, hxE, hx2, hx1, hxz⟩
    obtain ⟨j, hjC, hj⟩ := key x hxR hxE hx2 hx1
    refine ⟨j, mem_JP.2 ⟨hjC, ?_⟩, hj⟩
    exact (ivG_conj_F_iff c h (mem_JC.1 hjC).1).1 (hconj F x j hj hxz)

theorem outer_counts (h : F55Ctx c R) (hE : Nat.card ↥(Eg c) = 1440) :
    6 ≤ Set.ncard {x : G | x ∈ R ∧ x ∉ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x z} ∧
    6 ≤ Set.ncard {x : G | x ∈ R ∧ x ∉ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧
      IsConj x (c.iso.toG fhB)} := by
  obtain ⟨hZ, hP⟩ := R_counts c h
  obtain ⟨hZE, hPE⟩ := E_counts c h hE
  constructor
  · have hsub : {x : G | x ∈ R ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x z} ⊆
        {x : G | x ∈ R ∧ x ∈ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x z} ∪
          {x : G | x ∈ R ∧ x ∉ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x z} := by
      intro x hx
      by_cases hxE : x ∈ Eg c
      · exact Or.inl ⟨hx.1, hxE, hx.2⟩
      · exact Or.inr ⟨hx.1, hxE, hx.2⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le {x : G | x ∈ R ∧ x ∈ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x z}
      {x : G | x ∈ R ∧ x ∉ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x z}
    omega
  · have hsub : {x : G | x ∈ R ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x (c.iso.toG fhB)} ⊆
        {x : G | x ∈ R ∧ x ∈ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x (c.iso.toG fhB)} ∪
          {x : G | x ∈ R ∧ x ∉ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x (c.iso.toG fhB)} := by
      intro x hx
      by_cases hxE : x ∈ Eg c
      · exact Or.inl ⟨hx.1, hxE, hx.2⟩
      · exact Or.inr ⟨hx.1, hxE, hx.2⟩
    have h1 := Set.ncard_le_ncard hsub (Set.toFinite _)
    have h2 := Set.ncard_union_le
      {x : G | x ∈ R ∧ x ∈ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x (c.iso.toG fhB)}
      {x : G | x ∈ R ∧ x ∉ Eg c ∧ x * x = 1 ∧ x ≠ 1 ∧ IsConj x (c.iso.toG fhB)}
    omega

end Outer

end CFSG.Quasithin.H13.F431.U42Aut
