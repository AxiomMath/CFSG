module

public import CFSG.Milestones.ASVolI.F431.BCoreU5Chart
public import CFSG.Milestones.ASVolI.F431.BCoreGenP
public import CFSG.Milestones.ASVolI.F431.BCoreGenQ
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieVD
public import CFSG.Quasithin.Vol2.GoldschmidtF431Un5OutLieNst

public section

namespace CFSG.ASVolI

open CFSG.ASVolI.ChF CFSG.Quasithin CFSG.Open Matrix CFSG.ClassicalGroups.UnitaryFlag
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.U5K.Hyp
  CFSG.Quasithin.H13.Sec53F.Unit CFSG.Quasithin.H13.F431.Un.OL5 CFSG.LocalAnalysis.EvenBN.U5
open scoped commutatorElement

section U5Model

variable {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)

theorem burnsideF4m_U5_Pt_center_le (hf : 2 ≤ f) :
    centerOf (perfectCore (u5PtP h)) ≤ ctr (oPPrime 2 (u5PtP h)) := by
  have := h.finite
  have : Finite (hypPSU h 2 1) := finite_hypPSU_five h
  have hY := u5_yamStd (h := h)
  have hOP : oPPrime 2 (u5PtP h) ≤ perfectCore (u5PtP h) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hyP, k, hk⟩
    have hy : y ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
    exact CFSG.Quasithin.H13.U4Par.le_of_isPGroup_of_sylow_le (perfectCore_le _)
      (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _))
      (U_le_perfectCore_u5PtP hf) hY.sylow
      (CFSG.Quasithin.H13.U4Par.isPGroup_zpowers_of_pow hy)
      ((Subgroup.zpowers_le (H := u5PtP h)).mpr hyP) (Subgroup.mem_zpowers y)
  intro x hx
  have hx' := hx
  rw [centerOf_perfectCore_u5PtP h hf] at hx'
  obtain ⟨w, hw, rfl⟩ := hx'
  have hw2 : w * w = 1 := Vsub_sq (ZPsub_le_Vsub hw)
  have hxP : hypProj h 2 1 w ∈ u5PtP h := perfectCore_le _ hx.1
  have hx2 : hypProj h 2 1 w ^ 2 ^ 1 = 1 := by
    rw [pow_one, pow_two, ← map_mul, hw2, map_one]
  refine ⟨burnsideF4gU4Inv_mem_oPPrime hxP hx2, Subgroup.mem_centralizer_iff.mpr fun g hg => ?_⟩
  exact Subgroup.mem_centralizer_iff.mp hx.2 g (hOP hg)

theorem burnsideF4m_U5_pCore_le_Sh (hf : 2 ≤ f) {K₀ : Subgroup (MulAut (hypPSU h 2 1))}
    (hP : Pi h ≤ K₀) : pCoreOf 2 (K₀ ⊓ autStab (u5LnP h)) ≤ Sh h := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := finite_mulAut_hyp h
  refine core_Sh (u5_center_eq_bot h) (un5v_four_le hf)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) ?_
  intro ρ hρP hρS
  obtain ⟨g, rfl⟩ := hρP
  have hg := un5v_cj_mem_normalizer_Vh h (mem_normalizer_Vh_of_Sh (u5_center_eq_bot h) hρS)
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _ (un5v_cj_mem_N' h hP hg)

theorem burnsideF4m_U5_Sh_le_Pi : Sh h ≤ Pi h := Sh_le_Uh.trans Uh_le_Pi

end U5Model

theorem burnsideF4m_core12_U5 {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    (∀ x ∈ centerOf (perfectCore M₁), x ≠ 1 → x * x = 1 → x ∈ ctr (oPPrime 2 (Gp ⊓ M₁))) ∧
    (∀ x ∈ centerOf (perfectCore M₂), x ≠ 1 → x * x = 1 →
      GLKind.U5 = .Sp4 ∧ x ∈ ctr (oPPrime 2 (Gp ⊓ M₂))) := by
  haveI := hyp.normal
  haveI := hyp.finite
  obtain ⟨K, fK, h, Ψ, h1, h2⟩ := burnsideF4m_U5_chart hyp.toHypF_4_4g
  have hperf : ∀ S : Subgroup (MulAut ↥Gp), ⁅S, S⁆ = S →
      S ≤ (MulAut.conj : ↥Gp →* MulAut ↥Gp).range :=
    burnsideF4m_perf_transport Ψ (fun S hS =>
      CFSG.LocalAnalysis.EvenBN.U5.perfectLeInn h hf (u5_center_eq_bot h) S hS)
  have hpc := burnsideF4m_perfectCore_eq_inf_of_perfect hyp.centralizer_trivial hperf
  have hφ : Function.Injective (Gp.subtype.comp Ψ.toMonoidHom) :=
    Gp.subtype_injective.comp Ψ.injective
  refine ⟨burnsideF4m_core1_of_model' (hpc M₁) _ hφ h1 (burnsideF4m_U5_Pt_center_le h hf), ?_⟩
  intro x hx hx1 _
  rw [burnsideF4m_centerOf_perfectCore_eq_bot_of_model' (hpc M₂) _ hφ h2
    (centerOf_u5LnP_eq_bot hf)] at hx
  exact absurd (Subgroup.mem_bot.1 hx) hx1

theorem burnsideF4m_U5_pCore {f : ℕ} {E : Type} [Group E] {Gp M₁ M₂ : Subgroup E}
    (hyp : HypF_4_4 .U5 2 f Gp M₁ M₂) (hf : 2 ≤ f) :
    pCoreOf 2 M₂ = pCoreOf 2 (Gp ⊓ M₂) := by
  haveI := hyp.normal
  haveI := hyp.finite
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K, fK, h, Ψ, -, h2⟩ := burnsideF4m_U5_chart hyp.toHypF_4_4g
  set φ : hypPSU h 2 1 →* E := Gp.subtype.comp Ψ.toMonoidHom with hφdef
  have hφ : Function.Injective φ := Gp.subtype_injective.comp Ψ.injective
  have hrange : φ.range = Gp := by
    rw [hφdef, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Ψ.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  have hN2 : Subgroup.normalizer ((Gp ⊓ M₂ : Subgroup E) : Set E) ≤ M₂ :=
    burnsideF4m_normalizer_inf_le (M₁ := M₁)
      (fun e => by
        obtain ⟨n, hn, k, hk, he⟩ := hyp.split e
        exact ⟨n, hn, k, hk, he⟩) φ hφ hrange h2
      (fun g hg => by rwa [u5LnP_normalizer h] at hg)
  set Θ : E →* MulAut (hypPSU h 2 1) :=
    (MulAut.congr Ψ.symm).toMonoidHom.comp (burnsideF4d_rho Gp) with hΘdef
  have hΘinj : Function.Injective Θ :=
    (MulAut.congr Ψ.symm).injective.comp (burnsideF4d_rho_injective hyp.centralizer_trivial)
  have hΘapp : ∀ (e : E) (y : hypPSU h 2 1), φ (Θ e y) = e * φ y * e⁻¹ := by
    intro e y
    show (Gp.subtype.comp Ψ.toMonoidHom) (Ψ.symm (burnsideF4d_rho Gp e (Ψ y))) = _
    simp only [MonoidHom.coe_comp, Function.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.apply_symm_apply, Subgroup.coe_subtype]
    rw [burnsideF4d_rho_apply]
    rfl
  have hΘGp : Gp.map Θ = Pi h := by
    ext α
    constructor
    · rintro ⟨g, hg, rfl⟩
      refine ⟨Ψ.symm ⟨g, hg⟩, MulEquiv.ext fun y => hφ ?_⟩
      rw [hΘapp]
      show φ (Ψ.symm ⟨g, hg⟩ * y * (Ψ.symm ⟨g, hg⟩)⁻¹) = _
      rw [map_mul, map_mul, map_inv]
      congr 2 <;> simp [φ]
    · rintro ⟨y₀, rfl⟩
      refine ⟨φ y₀, hrange ▸ ⟨y₀, rfl⟩, MulEquiv.ext fun y => hφ ?_⟩
      rw [hΘapp]
      show _ = φ (y₀ * y * y₀⁻¹)
      rw [map_mul, map_mul, map_inv]
  have hmemP2 : ∀ y : hypPSU h 2 1, y ∈ u5LnP h ↔ φ y ∈ Gp ⊓ M₂ := by
    intro y
    rw [h2, Subgroup.mem_map_iff_mem hφ]
  have hΘM2 : M₂.map Θ = Θ.range ⊓ autStab (u5LnP h) := by
    ext α
    constructor
    · rintro ⟨e, he, rfl⟩
      refine ⟨⟨e, rfl⟩, fun y => ?_⟩
      rw [hmemP2, hmemP2, hΘapp]
      exact (Subgroup.mem_normalizer_iff.mp (burnsideF4m_mem_normalizer_inf (Gp := Gp) he)) _
    · rintro ⟨⟨e, rfl⟩, hst⟩
      refine ⟨e, hN2 ?_, rfl⟩
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxr : x ∈ φ.range := hrange ▸ hx.1
        obtain ⟨y, rfl⟩ := hxr
        rw [← hΘapp, ← hmemP2]
        exact (hst y).1 ((hmemP2 y).2 hx)
      · intro hx
        have hxG : x ∈ Gp := by
          have := Subgroup.Normal.conj_mem (inferInstance : Gp.Normal) _ hx.1 e⁻¹
          simpa [mul_assoc] using this
        have hxr : x ∈ φ.range := hrange ▸ hxG
        obtain ⟨y, rfl⟩ := hxr
        rw [← hΘapp, ← hmemP2] at hx
        exact (hmemP2 y).1 ((hst y).2 hx)
  have hinn : Pi h ≤ Θ.range := by
    rw [← hΘGp]
    exact Subgroup.map_le_range Θ Gp
  have hle := burnsideF4m_U5_pCore_le_Sh h hf hinn
  rw [← hΘM2, CFSG.Quasithin.H13.U4Par.pCoreOf_map_of_inj hΘinj] at hle
  refine burnsideF4m_pCoreOf_eq_inf_of_le Gp M₂ fun x hx => ?_
  have h3 : Θ x ∈ Gp.map Θ := by
    rw [hΘGp]
    exact burnsideF4m_U5_Sh_le_Pi h (hle ⟨x, hx, rfl⟩)
  exact (Subgroup.mem_map_iff_mem hΘinj).mp h3

end CFSG.ASVolI
