module

public import CFSG.Milestones.ASVolI.F429.bC7

public section

namespace CFSG.ASVolI

open CFSG.Open CFSG.ASVolI.ChF CFSG.Quasithin

section F4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4

theorem burnsideF429b_F4_center_trivial {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    {a : ℕ} (hK : Nat.card K = 2 ^ (2 * a + 1)) : Subgroup.center ↥(reeGroup K a) = ⊥ := by
  have := large_Ree_fixed_group_center_trivial a K hK
  rwa [burnsideF4gF4Inv_reeGroup_eq]

theorem burnsideF429b_F4_exists_iso {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {H : Type} [Group H]
    (marking : (reeGroup K a ⧸ Subgroup.center (reeGroup K a)) ≃* H) :
    ∃ Φ : Gm K a ≃* H, ∀ (P : Subgroup (Gm K a)) (R : Subgroup (ModGL F4.tag K)),
      (∀ y : Gm K a, y ∈ P ↔ (y : ModGL F4.tag K) ∈ R) →
        (centralImage (reeGroup K a) R).map marking.toMonoidHom = P.map Φ.toMonoidHom := by
  obtain ⟨q, hq⟩ := burnsideF4gF4Inv_exists_quotEquiv (burnsideF429b_F4_center_trivial hK)
  let e0 : Gm K a ≃* ↥(reeGroup K a) := MulEquiv.subgroupCongr burnsideF4gF4Inv_reeGroup_eq.symm
  refine ⟨(e0.trans q).trans marking, fun P R hPR => ?_⟩
  ext z
  constructor
  · rintro ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    refine ⟨e0.symm g, (hPR _).2 hg, ?_⟩
    show marking (q (e0 (e0.symm g))) = marking (QuotientGroup.mk' _ g)
    rw [MulEquiv.apply_symm_apply, hq]
    rfl
  · rintro ⟨y, hy, rfl⟩
    refine ⟨_, ⟨e0 y, (hPR y).1 hy, rfl⟩, ?_⟩
    show marking (QuotientGroup.mk' _ (e0 y)) = marking (q (e0 y))
    rw [hq]
    rfl

theorem burnsideF429b_F4_chartAll {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (h : HypF_4_4g .F4tw 2 f Gp M₁ M₂) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K F4.prime) (a : ℕ),
      Nat.card K = 2 ^ (2 * a + 1) ∧
      ∃ Ψ : Gm K a ≃* ↥Gp,
        M₁.subgroupOf Gp = (Pg K a ⟨1, by decide⟩).map Ψ.toMonoidHom ∧
        M₂.subgroupOf Gp = (Pg K a ⟨0, by decide⟩).map Ψ.toMonoidHom := by
  obtain ⟨a, K, fK, finK, charK, hscope, -, marking, h1, h2⟩ := burnsideF4g_chart_F4tw h
  letI := fK
  haveI := finK
  have hK : Nat.card K = 2 ^ (2 * a + 1) := hscope
  haveI : CharP K F4.prime := inferInstanceAs (CharP K 2)
  obtain ⟨Φ, hΦ⟩ := burnsideF429b_F4_exists_iso hK marking
  refine ⟨K, fK, finK, inferInstance, a, hK, Φ, h1.trans (hΦ _ _ fun y => ?_),
    h2.trans (hΦ _ _ fun y => ?_)⟩
  · rw [burnsideF4gF4Inv_reeParabolic_one_eq]
    exact Subgroup.mem_subgroupOf
  · rw [burnsideF4gF4Inv_reeParabolic_zero_eq]
    exact Subgroup.mem_subgroupOf

theorem burnsideF429b_F4_model_ctr {K : Type} [Field K] [Finite K] [CharP K F4.prime] {a : ℕ}
    (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1)) :
    ctr (pCoreOf 2 (Pg K a ⟨1, by decide⟩ ⊓ Pg K a ⟨0, by decide⟩)) =
      ctr (oPPrime 2 (Pg K a ⟨1, by decide⟩)) := by
  haveI : IsSimpleGroup (Gm K a) := isSimpleGroup_gm ha hK
  haveI : Finite (Gm K a) := finite_gm K a
  rw [burnsideF4gF4Inv_Pg_one_eq hK, burnsideF4gF4Inv_Pg_zero_eq hK,
    burnsideF4gF4Inv_pCoreOf_inf hK]
  have hzS := burnsideF4gF4Inv_zg_ctr ha hK
  have hoP := burnsideF4gF4Inv_oP ha hK
  refine burnsideF429b_ctr_eq_of_conj hzS hoP ?_
    (burnsideF429b_back_of_sylow (isSylowTwoOf_Ug hK) (burnsideF4gF4Inv_zg_inv hK).2 hzS hoP
      (burnsideF4gF4Inv_oP_ctr ha hK))
  intro w hw hw1
  obtain ⟨h, hh, hhw⟩ := center_gm ha hK w hw.1
    (fun y hy => Subgroup.mem_centralizer_iff.1 hw.2 y hy) hw1
  refine ⟨h, ?_, hhw⟩
  rw [← burnsideF4gF4Inv_Pg_one_eq hK]
  exact (Subgroup.mem_inf.1 hh).1

end F4

section F4Two

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.ASVolI.ChF.ExceptionalRoots
  CFSG.LieType.Chevalley CFSG.LieType.Ree CFSG.LieType.Ree.ReeTag
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Sporadic.Schreier.Tits

theorem burnsideF429b_twoF4_ctr :
    ctr (pCoreOf 2 (twoF4M1 ⊓ twoF4M2)) = ctr (oPPrime 2 twoF4M1) := by
  have hL := twoF4_F431LieI
  have hT2 : IsPGroup 2 twoF4TT := hL.sylow.2.1
  have hMT : twoF4M1 ⊓ twoF4M2 = twoF4TT :=
    le_antisymm burnsideF4gF4TwoInv_twoF4_inf (le_inf hL.T_le₁ hL.T_le₂)
  have hpc : pCoreOf 2 (twoF4M1 ⊓ twoF4M2) = twoF4TT := by
    rw [hMT]
    exact le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le 2 twoF4TT)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_rfl Subgroup.le_normalizer hT2)
  rw [hpc]
  have hoP : oPPrime 2 twoF4M1 = Subgroup.centralizer ({zM} : Set ↥twoF4M) :=
    burnsideF4gF4TwoInv_twoF4_oPPrime.trans hL.cent_z.symm
  have hzS : zM ∈ ctr twoF4TT := Subgroup.mem_inf.2 ⟨hL.z_mem, Subgroup.mem_centralizer_iff.2
    fun y hy => Subgroup.mem_centralizer_singleton_iff.1 (hL.cent_z ▸ hL.T_le₁ hy)⟩
  refine burnsideF429b_ctr_eq_of_conj hzS hoP ?_ ?_
  · intro w hw hw1
    obtain ⟨m, hm, hmz⟩ := hL.center_T w hw.1
      (fun y hy => Subgroup.mem_centralizer_iff.1 hw.2 y hy) hw1
    exact ⟨m, (Subgroup.mem_inf.1 hm).1, hmz⟩
  · intro x hx
    rw [burnsideF4gF4TwoInv_twoF4_oPPrime] at hx
    have hxT : x ∈ twoF4Lattice.S := burnsideF4gG2TwoInv_mem_of_cent twoF4Lattice.normS
      fun t ht => (Subgroup.mem_centralizer_iff.1 hx.2 t
        (hL.T_le₁ (twoF4Lattice_S ▸ ht : t ∈ twoF4TT))).symm
    rwa [twoF4Lattice_S] at hxT

theorem burnsideF429b_F4two_model_ctr {K : Type} [Field K] [Finite K] [CharP K F4.prime]
    (hKa : Nat.card K = 2 ^ (2 * 0 + 1)) :
    ctr (pCoreOf 2 (Pg K 0 ⟨1, by decide⟩ ⊓ Pg K 0 ⟨0, by decide⟩)) =
      ctr (oPPrime 2 (Pg K 0 ⟨1, by decide⟩)) := by
  have hK : Nat.card K = 2 := by simpa using hKa
  obtain ⟨Φ, -, h1, h2⟩ := burnsideF4gF4TwoInv_gamma hK hKa
  have e1 : Pg K 0 ⟨1, by decide⟩ = (burnsideF4gF4Two_system hK).P₁ := by
    ext y
    rw [burnsideF4gF4Two_mem_P₁_iff hK y, burnsideF4gF4Inv_reeParabolic_one_eq]
    exact Subgroup.mem_subgroupOf
  have e0 : Pg K 0 ⟨0, by decide⟩ = (burnsideF4gF4Two_system hK).P₂ := by
    ext y
    rw [burnsideF4gF4Two_mem_P₂_iff hK y, burnsideF4gF4Inv_reeParabolic_zero_eq]
    exact Subgroup.mem_subgroupOf
  rw [e1, e0]
  apply Subgroup.map_injective (f := Φ.toMonoidHom) Φ.injective
  rw [← burnsideF429b_ctr_map _ Φ.injective, ← burnsideF429b_ctr_map _ Φ.injective,
    ← CFSG.Quasithin.H13.F431.pCoreOf_map_of_injective _ Φ.injective,
    ← burnsideF4gF4Inv_oPPrime_map_inj _ Φ.injective, Subgroup.map_inf_eq _ _ _ Φ.injective, h1,
    h2]
  exact burnsideF429b_twoF4_ctr

theorem burnsideF429b_c7_F4tw {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .F4tw 2 f Gp M₁ M₂) :
    ctr (pCoreOf 2 (Gp ⊓ (M₁ ⊓ M₂))) = ctr (oPPrime 2 (Gp ⊓ M₁)) := by
  obtain ⟨K, fK, finK, cK, a, hK, Ψ, h1, h2⟩ := burnsideF429b_F4_chartAll hyp.toHypF_4_4g
  refine burnsideF429b_c7_of_model Ψ h1 (burnsideF429b_inf_subgroupOf Ψ h1 h2) ?_
  rcases Nat.eq_zero_or_pos a with rfl | ha
  · exact burnsideF429b_F4two_model_ctr hK
  · exact burnsideF429b_F4_model_ctr ha hK

end F4Two

end CFSG.ASVolI
