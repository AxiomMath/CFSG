module

public import CFSG.Quasithin.Recognition.St84.Gen.U4qAmalExtModel
public import CFSG.Assembly.GL83LieDefs

public section

namespace CFSG.Quasithin.F112R.St84

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.U4Par

variable {m : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 m K)

theorem eq_bot_of_comap_inl_eq_bot_u4Ext {R : Subgroup (u4ExtGroup h)}
    (hR : R.comap SemidirectProduct.inl = ⊥)
    (hU : ∀ u ∈ hypUnitriangular h 2 0,
      (SemidirectProduct.inl u : u4ExtGroup h) ∈ Subgroup.normalizer (R : Set (u4ExtGroup h))) :
    R = ⊥ := by
  rw [eq_bot_iff]
  intro r hr
  rw [Subgroup.mem_bot]
  have hc : ∀ u ∈ hypUnitriangular h 2 0,
      r * SemidirectProduct.inl u = SemidirectProduct.inl u * r := by
    intro u hu
    have h1 : r * SemidirectProduct.inl u * r⁻¹ * (SemidirectProduct.inl u)⁻¹ ∈ R := by
      have h2 := (Subgroup.mem_normalizer_iff.mp (hU u hu) r⁻¹).mp (R.inv_mem hr)
      have e : r * SemidirectProduct.inl u * r⁻¹ * (SemidirectProduct.inl u)⁻¹ =
          r * (SemidirectProduct.inl u * r⁻¹ * (SemidirectProduct.inl u)⁻¹) := by group
      rw [e]
      exact R.mul_mem hr h2
    rw [conj_inl_u4Ext, ← map_inv, ← map_mul] at h1
    have h3 : r.left * u4FieldInvolHom h r.right u * r.left⁻¹ * u⁻¹ ∈
        R.comap SemidirectProduct.inl := h1
    rw [hR, Subgroup.mem_bot] at h3
    calc r * SemidirectProduct.inl u
        = r * SemidirectProduct.inl u * r⁻¹ * (SemidirectProduct.inl u)⁻¹ *
            (SemidirectProduct.inl u * r) := by group
      _ = SemidirectProduct.inl u * r := by
        rw [conj_inl_u4Ext, ← map_inv, ← map_mul, h3, map_one, one_mul]
  rcases z2_cases_u4Ext r.right with h0 | h0
  · have hr' : r = SemidirectProduct.inl r.left := by
      conv_lhs => rw [← SemidirectProduct.inl_left_mul_inr_right r]
      rw [h0, map_one, mul_one]
    have h4 : r.left ∈ R.comap SemidirectProduct.inl := by
      show SemidirectProduct.inl r.left ∈ R
      rw [← hr']
      exact hr
    rw [hR, Subgroup.mem_bot] at h4
    rw [hr', h4, map_one]
  · exfalso
    apply not_forall_u4FieldInvol_mul_eq h r.left⁻¹
    intro v hv
    have e := congrArg SemidirectProduct.left (hc v hv)
    simp only [SemidirectProduct.mul_left, SemidirectProduct.left_inl,
      SemidirectProduct.right_inl, h0, u4FieldInvolHom_ofAdd_one, map_one,
      MulAut.one_apply] at e
    calc u4FieldInvol h v * r.left⁻¹ = r.left⁻¹ * (r.left * u4FieldInvol h v) * r.left⁻¹ := by
          group
      _ = r.left⁻¹ * (v * r.left) * r.left⁻¹ := by rw [e]
      _ = r.left⁻¹ * v := by group

theorem holds_borelTits_hypSU_u4 : CFSG.LieType.BorelTits.Holds (hypSU h 2 0) 2 := by
  have := h.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := h.charP
  obtain ⟨e⟩ := nonempty_hypSU_equiv_statedProj h
  have hK : Nat.card K = (2 ^ m) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  exact (CFSG.LieType.BorelTits.holds_statedProj_statedSU hK 4).of_mulEquiv e.symm

theorem normalizer_le_parP_or_parP2_u4Ext {R : Subgroup (hypSU h 2 0)} (hR : R ≠ ⊥)
    (hR2 : IsPGroup 2 R)
    (hU : hypUnitriangular h 2 0 ≤ Subgroup.normalizer (R : Set (hypSU h 2 0))) :
    Subgroup.normalizer (R : Set (hypSU h 2 0)) ≤ parP h ∨
      Subgroup.normalizer (R : Set (hypSU h 2 0)) ≤ parP2 h := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, P', hP', hNR, -, -, hNS⟩ := holds_borelTits_hypSU_u4 h R hR hR2
  obtain ⟨PU, hPU⟩ :=
    (unitary_order_and_Sylow (r := 2) (ε := 0) h (by norm_num) (by norm_num)).2.1
  have hUP : (PU : Subgroup (hypSU h 2 0)) ≤ P' := hPU ▸ hU.trans hNR
  have hSP : (S : Subgroup (hypSU h 2 0)) ≤ P' := Subgroup.le_normalizer.trans hNS
  obtain ⟨p, hp⟩ := MulAction.exists_smul_eq P' (S.subtype hSP) (PU.subtype hUP)
  rw [Sylow.smul_subtype] at hp
  have hp' : (p : hypSU h 2 0) • S = PU := Sylow.subtype_injective hp
  have hBP : hypBorel h 2 0 ≤ P' := by
    rw [← UnitaryHigher.normalizer_hypUnitriangular (r := 2) (ε := 0) h (by norm_num)
      (by norm_num), ← hPU]
    intro b hb
    have hb' : b • PU = PU := Sylow.smul_eq_iff_mem_normalizer.mpr hb
    have hS : ((p : hypSU h 2 0)⁻¹ * b * p) • S = S := by
      rw [mul_smul, mul_smul, hp', hb', ← hp', inv_smul_smul]
    have h1 := hNS (Sylow.smul_eq_iff_mem_normalizer.mp hS)
    have e : b = p * ((p : hypSU h 2 0)⁻¹ * b * p) * (p : hypSU h 2 0)⁻¹ := by group
    rw [e]
    exact P'.mul_mem (P'.mul_mem p.2 h1) (P'.inv_mem p.2)
  obtain ⟨A, hA, hPA⟩ := (IsCoatomic.eq_top_or_exists_le_coatom P').resolve_left hP'
  rcases eq_parP_or_eq_parP2 h hA (hBP.trans hPA) with rfl | rfl
  · exact Or.inl (hNR.trans hPA)
  · exact Or.inr (hNR.trans hPA)

theorem le_u4ExtParP_or_le_u4ExtParP2 {H : Subgroup (u4ExtGroup h)} (hH : IsTwoLocal H)
    (hTH : u4ExtSylow h ≤ H) : H ≤ u4ExtParP h ∨ H ≤ u4ExtParP2 h := by
  obtain ⟨R, hR1, hR2, rfl⟩ := hH
  have hU : ∀ u ∈ hypUnitriangular h 2 0, (SemidirectProduct.inl u : u4ExtGroup h) ∈
      Subgroup.normalizer (R : Set (u4ExtGroup h)) := fun u hu =>
    hTH ((inl_mem_u4ExtLift h u).mpr hu)
  have hinr : ∀ s, (SemidirectProduct.inr s : u4ExtGroup h) ∈
      Subgroup.normalizer (R : Set (u4ExtGroup h)) := fun s => hTH (inr_mem_u4ExtLift h s)
  have hR01 : R.comap SemidirectProduct.inl ≠ ⊥ := fun h0 =>
    hR1 (eq_bot_of_comap_inl_eq_bot_u4Ext h h0 hU)
  have hR02 : IsPGroup 2 (R.comap SemidirectProduct.inl) :=
    hR2.comap_of_injective _ SemidirectProduct.inl_injective
  have hN := Subgroup.le_normalizer_comap (H := R)
    (SemidirectProduct.inl : hypSU h 2 0 →* u4ExtGroup h)
  rcases normalizer_le_parP_or_parP2_u4Ext h hR01 hR02 (fun u hu => hN (hU u hu)) with hP | hP
  · exact Or.inl (le_u4ExtLift_of_comap_le h hinr (hN.trans hP))
  · exact Or.inr (le_u4ExtLift_of_comap_le h hinr (hN.trans hP))

theorem isTwoLocal_u4ExtParP : IsTwoLocal (u4ExtParP h) :=
  ⟨(radQ h).map SemidirectProduct.inl,
    (Subgroup.map_eq_bot_iff_of_injective _ SemidirectProduct.inl_injective).not.mpr
      (radQ_ne_bot_u4Ext h),
    (radQ_isPGroup h).map _, u4ExtParP_eq_normalizer h⟩

theorem isTwoLocal_u4ExtParP2 : IsTwoLocal (u4ExtParP2 h) :=
  ⟨(radQ2 h).map SemidirectProduct.inl,
    (Subgroup.map_eq_bot_iff_of_injective _ SemidirectProduct.inl_injective).not.mpr
      (radQ2_ne_bot_u4Ext h),
    (radQ2_isPGroup h).map _, u4ExtParP2_eq_normalizer h⟩

theorem isMaximalTwoLocal_u4ExtParP : IsMaximalTwoLocal (u4ExtParP h) := by
  refine ⟨isTwoLocal_u4ExtParP h, fun H hH hle => ?_⟩
  rcases le_u4ExtParP_or_le_u4ExtParP2 h hH
      (((u4ExtSylow_le_u4ExtBorel h).trans (u4ExtBorel_le_u4ExtParP h)).trans hle) with h1 | h1
  · exact le_antisymm h1 hle
  · exfalso
    have hPP : parP h ≤ parP2 h := (u4ExtLift_le_iff h).mp (hle.trans h1)
    rcases (isCoatom_parP h).le_iff.mp hPP with h2 | h2
    · exact (isCoatom_parP2 h).1 h2
    · exact parP_ne_parP2 h h2.symm

theorem isMaximalTwoLocal_u4ExtParP2 : IsMaximalTwoLocal (u4ExtParP2 h) := by
  refine ⟨isTwoLocal_u4ExtParP2 h, fun H hH hle => ?_⟩
  rcases le_u4ExtParP_or_le_u4ExtParP2 h hH
      (((u4ExtSylow_le_u4ExtBorel h).trans (u4ExtBorel_le_u4ExtParP2 h)).trans hle) with h1 | h1
  · exfalso
    have hPP : parP2 h ≤ parP h := (u4ExtLift_le_iff h).mp (hle.trans h1)
    rcases (isCoatom_parP2 h).le_iff.mp hPP with h2 | h2
    · exact (isCoatom_parP h).1 h2
    · exact parP_ne_parP2 h h2
  · exact le_antisymm h1 hle

theorem isSylowTwoOf_u4ExtSylow : IsSylowTwoOf (u4ExtSylow h) ⊤ := by
  have := CFSG.Quasithin.H13.U4Par.finite_hypSU h
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcard, ⟨PU, hPU⟩, -⟩ :=
    unitary_order_and_Sylow (r := 2) (ε := 0) h (by norm_num) (by norm_num)
  refine ⟨le_top, ?_, ?_⟩
  · have h6 : (2 * 2 + 0) * (2 * 2 + 0 - 1) / 2 = 6 := by norm_num
    apply IsPGroup.of_card (n := 6 * m + 1)
    rw [card_u4ExtLift, hcard, h6]
    ring
  · rw [show ((u4ExtSylow h).subgroupOf ⊤).index = (u4ExtSylow h).index from
      Subgroup.relIndex_top_right _, index_u4ExtLift, ← hPU]
    exact PU.not_dvd_index

theorem isYAmalgamPair_u4Ext : IsYAmalgamPair (u4ExtSylow h) (u4ExtParP h) (u4ExtParP2 h) := by
  refine ⟨isSylowTwoOf_u4ExtSylow h, u4ExtParP_ne_u4ExtParP2 h, fun M => ⟨?_, ?_⟩⟩
  · rintro ⟨hM, hNM⟩
    rcases le_u4ExtParP_or_le_u4ExtParP2 h hM.1 (Subgroup.le_normalizer.trans hNM) with h1 | h1
    · exact Or.inl (hM.2 _ (isTwoLocal_u4ExtParP h) h1).symm
    · exact Or.inr (hM.2 _ (isTwoLocal_u4ExtParP2 h) h1).symm
  · rintro (rfl | rfl)
    · exact ⟨isMaximalTwoLocal_u4ExtParP h,
        (normalizer_u4ExtSylow_le h).trans (u4ExtBorel_le_u4ExtParP h)⟩
    · exact ⟨isMaximalTwoLocal_u4ExtParP2 h,
        (normalizer_u4ExtSylow_le h).trans (u4ExtBorel_le_u4ExtParP2 h)⟩

theorem isU4ExtTwo_of_iso {α : RankTwoAmalgam.{0}}
    (e : α.Iso (RankTwoAmalgam.ofSubgroups (u4ExtParP h) (u4ExtParP2 h))) : IsU4ExtTwo m α :=
  ⟨↥(hypSU h 2 0), inferInstance, u4ExtGroup h, inferInstance, SemidirectProduct.inl,
    isLieOverTwo_psu4 h, SemidirectProduct.inl_injective, index_range_inl_u4Ext h, u4ExtSylow h,
    u4ExtParP h, u4ExtParP2 h, isYAmalgamPair_u4Ext h, ⟨e⟩⟩

end CFSG.Quasithin.F112R.St84

end
