module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9GrpOne
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ActSub

public section

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem pCore_mZ_le_centralizer {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G}
    (hq : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M) (hCE : IsCE1513 T M)
    (hE : E9Pre T Mc M Z₁ Z₂ V₁ V₂) (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M)
    (h14 : Lemma15114Concl T Mc M) (h113 : Lemma15113Four T Mc M) :
    q1_1516 Mc Z₁ ≤ Subgroup.centralizer (vE1516 T Mc M : Set G) := by
  obtain ⟨hVe, d, hV₁, hV₂⟩ := hE.data
  have h5 := hE.h5
  obtain ⟨x₁, x₂, r⟩ := exists_reflData d h5 h113
  obtain ⟨-, ε₂, -, ⟨hε₂M, hε₂3, hε₂₁, hε₂a, hε₂f, hε₂s1, hε₂s2⟩⟩ := exists_torus r hE.e9
  have hC1 := vZ_mc_eq_vE hq hM hCE h5 hE.e9 h15 h19 h14 h113
  have hW : ∀ w : IntMod (V154 T Mc M) hVe, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  have hZ₁ := r.z₁_eq hE.z₁ hV₁
  have hMN : M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := d.hMN
  have hord : OrdLE T Mc M := h19.two.2 Mc ⟨hq.mc_max, hq.t_le_mc⟩
  have hCst : ∀ g ∈ SixData151b.ptFix (SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂))
      (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)), ∀ w : IntMod (V154 T Mc M) hVe,
      w ∈ d.S.vEMod x₁ x₂ ↔ g w ∈ d.S.vEMod x₁ x₂ := fun g hg w => hg.1.2 w
  have hR2 : IsPGroup 2 ↥(q1_1516 Mc Z₁) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _
  have hRnorm : ∀ γ ∈ mZ1516 Mc Z₁, ∀ ρ ∈ q1_1516 Mc Z₁, γ * ρ * γ⁻¹ ∈ q1_1516 Mc Z₁ :=
    fun γ hγ ρ hρ =>
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (mZ1516 Mc Z₁) hγ) ρ).mp hρ
  have hP2 : IsPGroup 2 ↥(actSub (valHomI hVe) (d.S.vEMod x₁ x₂)
      (SixData151b.ptFix (SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂))
        (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁))) hCst (q1_1516 Mc Z₁)) := by
    refine isPGroup_actSub IntMod.val_injective hR2 ?_
    intro h hh hodd htriv
    exact d.S.odd_trivial_on_vE hW d.hcard d.hnorm r.x₁_mem.1 r.x₂_mem.1 r.x₁_two r.x₂_two
      hε₂M.1 hε₂3 hε₂₁ hε₂f hε₂a hh hodd htriv
  have hPn : ∀ c ∈ SixData151b.ptFix (SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂))
      (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)), ∀ p ∈ actSub (valHomI hVe) (d.S.vEMod x₁ x₂)
      (SixData151b.ptFix (SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂))
        (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁))) hCst (q1_1516 Mc Z₁),
      c * p * c⁻¹ ∈ actSub (valHomI hVe) (d.S.vEMod x₁ x₂)
      (SixData151b.ptFix (SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂))
        (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁))) hCst (q1_1516 Mc Z₁) := by
    intro c hc p hp
    obtain ⟨γ, hγN, hγM, hγVE, hγc⟩ := r.exists_lift hc.1
    have hγZ : γ ∈ Subgroup.centralizer (Z₁ : Set G) := by
      rw [hZ₁]
      refine (mem_centralizer_map_iff hγN).2 fun z hz => ?_
      rw [hγc]
      exact hc.2 z hz
    have hγMc : γ ∈ Mc := by
      have h := hγVE
      rw [← r.vE, ← hC1.2] at h
      exact h
    refine actSub_conj hc (fun w => ?_) (hRnorm γ ⟨hγZ, hγMc⟩) hp
    have h1 := conj_val (hV := hVe) hγN w
    rw [hγc] at h1
    exact h1.symm
  have hE6 := d.S.normal_two_group_trivial_on_vE hW d.hcard d.hnorm r.x₁_mem.1 r.x₂_mem.1
    r.x₁_two r.x₂_two hε₂M hε₂3 hε₂₁ hε₂f hP2 (fun g hg => hg.1) hPn
  intro ρ hρ
  have hρmZ : ρ ∈ mZ1516 Mc Z₁ := (q1_1516_le Mc Z₁) hρ
  obtain ⟨a, ha, c, hc, hρac⟩ := hord ρ hρmZ.2
  rw [hC1.1] at hc
  have hZVE : Z₁ ≤ vE1516 T Mc M := by
    rw [hE.z₁]
    exact inf_le_left
  have hcZ : c ∈ Subgroup.centralizer (Z₁ : Set G) := Subgroup.centralizer_le hZVE hc.2
  have haZ : a ∈ Subgroup.centralizer (Z₁ : Set G) := by
    have : a = ρ * c⁻¹ := by rw [hρac]; group
    rw [this]
    exact Subgroup.mul_mem _ hρmZ.1 (Subgroup.inv_mem _ hcZ)
  have haN : a ∈ Subgroup.normalizer (V154 T Mc M : Set G) := hMN ha.2
  have haNE : a ∈ Subgroup.normalizer (((d.S.vEMod x₁ x₂).map (valHomI hVe) : Subgroup G) :
      Set G) := by
    rw [← r.vE, ← hC1.2]
    exact ha.1
  have haZ' : a ∈ Subgroup.centralizer (((d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)).map
      (valHomI hVe) : Subgroup G) : Set G) := by
    rw [← hZ₁]
    exact haZ
  have hφC : convI hVe ⟨a, haN⟩ ∈ SixData151b.ptFix (SixData151b.stabSub (autI hVe M)
      (d.S.vEMod x₁ x₂)) (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) :=
    ⟨⟨convI_mem_autI hVe ha.2 haN, stab_of_mem_normalizer_map haN haNE⟩,
      fun z hz => (mem_centralizer_map_iff haN).1 haZ' z hz⟩
  have hvc : ∀ v ∈ d.S.vEMod x₁ x₂, IntMod.val v * c = c * IntMod.val v := by
    intro v hv
    have hvVE : IntMod.val v ∈ vE1516 T Mc M := by
      rw [r.vE]
      exact Subgroup.mem_map.2 ⟨v, hv, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hc.2 _ hvVE
  have hφP : convI hVe ⟨a, haN⟩ ∈ actSub (valHomI hVe) (d.S.vEMod x₁ x₂)
      (SixData151b.ptFix (SixData151b.stabSub (autI hVe M) (d.S.vEMod x₁ x₂))
        (d.S.W₁ ⊓ fixV (Subgroup.zpowers x₁))) hCst (q1_1516 Mc Z₁) := by
    refine ⟨hφC, ρ, hρ, fun v hv => ?_⟩
    have h1 := conj_val (hV := hVe) haN v
    show IntMod.val (convI hVe ⟨a, haN⟩ v) = ρ * IntMod.val v * ρ⁻¹
    rw [← h1, hρac]
    have := hvc v hv
    calc a * IntMod.val v * a⁻¹ = a * (c * IntMod.val v * c⁻¹) * a⁻¹ := by
          rw [← this]
          group
      _ = a * c * IntMod.val v * (a * c)⁻¹ := by group
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  rw [r.vE] at hx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hx
  have h2 := hE6 _ hφP v hv
  have h1 := conj_val (hV := hVe) haN v
  rw [h2] at h1
  have hvc' := hvc v hv
  show IntMod.val v * ρ = ρ * IntMod.val v
  rw [hρac]
  calc IntMod.val v * (a * c) = (a * IntMod.val v * a⁻¹) * (a * c) := by rw [h1]
    _ = a * (IntMod.val v * c) := by group
    _ = a * (c * IntMod.val v) := by rw [hvc']
    _ = a * c * IntMod.val v := by group

theorem q1_normal {T Mc M Z₁ Z₂ V₁ V₂ : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    (hM : IsMf T Mc M) (hCE : IsCE1513 T M) (hE : E9Pre T Mc M Z₁ Z₂ V₁ V₂)
    (h15 : Lemma1515Concl T Mc M) (h19 : Lemma1519Concl T Mc M) (h14 : Lemma15114Concl T Mc M)
    (h113 : Lemma15113Four T Mc M) :
    q1_1516 Mc Z₁ = pCoreOf 2 (Subgroup.centralizer (vE1516 T Mc M : Set G)) ∧
      Mc ≤ Subgroup.normalizer (q1_1516 Mc Z₁ : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hC1 := vZ_mc_eq_vE hq hM hCE hE.h5 hE.e9 h15 h19 h14 h113
  have hle := pCore_mZ_le_centralizer hq hM hCE hE h15 h19 h14 h113
  have hZVE : Z₁ ≤ vE1516 T Mc M := by
    rw [hE.z₁]
    exact inf_le_left
  have hCVMc : Subgroup.centralizer (vE1516 T Mc M : Set G) ≤ Mc := by
    intro g hg
    rw [hC1.2]
    exact Subgroup.centralizer_le_normalizer _ hg
  have hCVmZ : Subgroup.centralizer (vE1516 T Mc M : Set G) ≤ mZ1516 Mc Z₁ :=
    fun g hg => ⟨Subgroup.centralizer_le hZVE hg, hCVMc hg⟩
  have hMcCV : Mc ≤ Subgroup.normalizer (Subgroup.centralizer (vE1516 T Mc M : Set G) : Set G) := by
    intro g hg
    have hgN : g ∈ Subgroup.normalizer (vE1516 T Mc M : Set G) := by rw [← hC1.2]; exact hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ k ∈ Subgroup.normalizer (vE1516 T Mc M : Set G),
        ∀ x ∈ Subgroup.centralizer (vE1516 T Mc M : Set G),
        k * x * k⁻¹ ∈ Subgroup.centralizer (vE1516 T Mc M : Set G) := by
      intro k hk x hx
      refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
      have h1 : k⁻¹ * h * k ∈ vE1516 T Mc M := by
        have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem hk) h).mp hh
        simpa using this
      have h2 := Subgroup.mem_centralizer_iff.mp hx _ h1
      calc h * (k * x * k⁻¹) = k * ((k⁻¹ * h * k) * x) * k⁻¹ := by group
        _ = k * (x * (k⁻¹ * h * k)) * k⁻¹ := by rw [h2]
        _ = k * x * k⁻¹ * h := by group
    intro x
    refine ⟨fun hx => key g hgN x hx, fun hx => ?_⟩
    have := key g⁻¹ ((Subgroup.normalizer _).inv_mem hgN) _ hx
    simpa [mul_assoc] using this
  have hO₂ : q1_1516 Mc Z₁ = pCoreOf 2 (Subgroup.centralizer (vE1516 T Mc M : Set G)) := by
    apply le_antisymm
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hle ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      exact hCVmZ.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
    · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans hCVmZ) ?_
        (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
      exact (mZ1516_le_mc Mc Z₁).trans
        (hMcCV.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _))
  refine ⟨hO₂, ?_⟩
  rw [hO₂]
  exact hMcCV.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)

end CFSG.Quasithin.E9
