module

public import CFSG.Quasithin.EmptyFaithful.S143GA
public import CFSG.Quasithin.EmptyFaithful.S143FI

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace S143

section Model

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G} {g : G} (c : Counter T M g)

include c

noncomputable abbrev Counter.tildeCommGroup : CommGroup (UT T M) :=
  { (inferInstance : Group (UT T M)) with
    mul_comm := fun a b => (tilde_isMulCommutative c.h1281).is_comm.comm a b }

theorem Counter.swap_model {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M)
    (hr2 : r * r = 1) {α : MulAut (UT T M)} (hαT : α ∈ (T.subgroupOf (mcOf T)).map c.actK)
    (hα1 : α ≠ 1) (hαx : α (tclsE c.hUN hrW.1) = tclsE c.hUN hrW.1) :
    ∃ (L₁ L₂ : Subgroup (MulAut (UT T M))) (t₀ : MulAut (UT T M)),
      @OfourStruct (UT T M) c.tildeCommGroup c.actK.range L₁ L₂ t₀ ∧ α ∉ L₁ ⊔ L₂ := by
  let _ : CommGroup (UT T M) := c.tildeCommGroup
  have h := c.h1281
  have hg := c.goodElt
  obtain ⟨q, hq1, hq2, hq3, hq4, hq5, hq6⟩ := c.c15.orth
  have hHN := hHN_of T
  have hHU := c.hHU
  have hUN := c.hUN
  obtain ⟨L₁, L₂, t₀, hS, hsing⟩ := exists_ofourStruct_of_plusType
    (W := UT T M) (q := q) (tilde_mul_self h) hq4 hq1 hq2 hq3
  have hrange : c.actK.range = orthogonalGroupOf q := c.actK_range.trans hq6
  have hT' : IsSylowTwoOf ((T.subgroupOf (mcOf T)).map c.actK) (orthogonalGroupOf q) := by
    have := isSylowTwoOf_map_range' (sylow_G1_of_hyp h) c.actK
    rwa [hrange] at this
  obtain ⟨z, a, hzZ, hz1, ha, haV, haZ, hzz, haa, hza, hga, hgza, hcases⟩ :=
    exists_three_cycle h hg
  have hrU : r ∈ uOfL22 T M := hrW.1
  have haU : a ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M haV
  have hZV : ∀ y ∈ quasithinOmegaOneCenter T, y ∈ VZ T M := fun y hy =>
    Hyp1281Two.omegaOneCenter_le_VZ T M hy
  have hTH : T ≤ mcOf T := h.almostSpecialHyp_g1.T_le_H
  have hTM : T ≤ M := c.hyp.m_max.1.2
  set x := tclsE hUN hrU with hx
  set v := tclsE hUN haU with hv
  have hv1 : v ≠ 1 := fun he => haZ ((tclsE_eq_one_iff hUN haU).mp he)
  have hx1 : x ≠ 1 := fun he => hrV (hZV _ ((tclsE_eq_one_iff hUN hrU).mp he))
  have hxv : x ≠ v := by
    intro he
    have h1 : r⁻¹ * a ∈ VZ T M := hZV _ ((tclsE_eq_iff hUN hrU haU).mp he)
    apply hrV
    have h2 : r⁻¹ ∈ VZ T M := by
      have := (VZ T M).mul_mem h1 ((VZ T M).inv_mem haV)
      simpa using this
    simpa using (VZ T M).inv_mem h2
  have hxq : q x = 0 :=
    (hq5 x.1 x.2 ⟨r, hUN hrU⟩ hrU (tclsE_val hUN hrU).symm).mpr (by rw [sq]; exact hr2)
  have har : a * r = r * a := Subgroup.mem_centralizer_iff.mp hrW.2 a haV
  have hvxq : q (v * x) = 0 := by
    have hu : a * r ∈ uOfL22 T M := (uOfL22 T M).mul_mem haU hrU
    have e : v * x = tclsE hUN hu := (tclsE_mul hUN haU hrU).symm
    rw [e]
    refine (hq5 _ _ ⟨a * r, hUN hu⟩ hu (tclsE_val hUN hu).symm).mpr ?_
    rw [sq]
    calc a * r * (a * r) = a * (r * a) * r := by group
      _ = a * (a * r) * r := by rw [← har]
      _ = (a * a) * (r * r) := by group
      _ = 1 := by rw [haa, hr2, one_mul]
  have hvfix : ∀ y ∈ (T.subgroupOf (mcOf T)).map c.actK, y v = v := by
    intro y hy
    obtain ⟨τ', hτ', rfl⟩ := Subgroup.mem_map.mp hy
    have hτT : (τ' : G) ∈ T := hτ'
    have hτa : (τ' : G) * a * (τ' : G)⁻¹ ∈ uOfL22 T M :=
      (Subgroup.mem_normalizer_iff.mp (hHU τ'.2) a).mp haU
    rw [hv]
    show actTilde (quasithinOmegaOneCenter T) (uOfL22 T M) (mcOf T) hHN hHU τ' (tclsE hUN haU) =
      tclsE hUN haU
    rw [actTilde_tclsE hUN hHN hHU τ' haU hτa]
    refine (tclsE_eq_iff hUN hτa haU).mpr ?_
    have hτN : (τ' : G) ∈ Subgroup.normalizer (VZ T M : Set G) := by
      rw [h.normalizer_VZ]; exact hTM hτT
    have hτaV : (τ' : G) * a * (τ' : G)⁻¹ ∈ VZ T M :=
      (Subgroup.mem_normalizer_iff.mp hτN a).mp haV
    have hτz : (τ' : G) * z * (τ' : G)⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp τ'.2 z hzZ
      rw [← this]; group
    rcases hcases _ hτaV with he | he | he | he
    · exfalso
      apply haZ
      have : a = (τ' : G)⁻¹ * ((τ' : G) * a * (τ' : G)⁻¹) * (τ' : G) := by group
      rw [this, he]
      simp [(quasithinOmegaOneCenter T).one_mem]
    · exfalso
      apply haZ
      have : a = (τ' : G)⁻¹ * ((τ' : G) * a * (τ' : G)⁻¹) * (τ' : G) := by group
      rw [this, he]
      have h2 : (τ' : G)⁻¹ * z * (τ' : G) = z := by
        calc (τ' : G)⁻¹ * z * (τ' : G) = (τ' : G)⁻¹ * ((τ' : G) * z * (τ' : G)⁻¹) * (τ' : G) := by
              rw [hτz]
          _ = z := by group
      rw [h2]; exact hzZ
    · rw [he, inv_mul_cancel]; exact (quasithinOmegaOneCenter T).one_mem
    · rw [he]
      have : (z * a)⁻¹ * a = z⁻¹ := by rw [hza]; group
      rw [this]; exact (quasithinOmegaOneCenter T).inv_mem hzZ
  have hαN : α ∉ L₁ ⊔ L₂ := fun hN => hα1 (eq_one_of_mem_S_of_fix hS hsing (tilde_mul_self h) hT' hv1
    hvfix hx1 hxv hxq hvxq ⟨hαT, hN⟩ hαx)
  refine ⟨L₁, L₂, t₀, ?_, hαN⟩
  rw [hrange]
  exact hS

variable {r : G} (hrW : r ∈ Hyp1281Two.wOfU T M) (hrV : r ∉ VZ T M) (hr2 : r * r = 1)
  {α : MulAut (UT T M)} (hαT : α ∈ (T.subgroupOf (mcOf T)).map c.actK) (hα1 : α ≠ 1)
  (hα2 : α * α = 1) (hαx : α (tclsE c.hUN hrW.1) = tclsE c.hUN hrW.1)

include hrW hrV hr2 hαT hα1 hα2 hαx

omit hα2 in
theorem Counter.odd_fix_trivial {y : MulAut (UT T M)}
    (hy : y ∈ Subgroup.centralizer ({α} : Set (MulAut (UT T M))) ⊓ c.actK.range)
    (hodd : Odd (orderOf y)) {w : UT T M} (hw : w ≠ 1) (hyw : y w = w) : y = 1 := by
  let _ : CommGroup (UT T M) := c.tildeCommGroup
  obtain ⟨L₁, L₂, t₀, hS, hαN⟩ := c.swap_model hrW hrV hr2 hαT hα1 hαx
  have hαX : α ∈ c.actK.range := Subgroup.map_le_range _ _ hαT
  exact eq_one_of_odd_fix hS hαX hαN hy.2 (Subgroup.mem_centralizer_singleton_iff.mp hy.1).symm
    hodd hw hyw

theorem Counter.exists_ffp_centralizer :
    ∃ y ∈ Subgroup.centralizer ({α} : Set (MulAut (UT T M))) ⊓ c.actK.range,
      orderOf y = 3 ∧ ∀ w : UT T M, y w = w → w = 1 := by
  obtain ⟨-, ⟨e⟩⟩ := c.swap_facts hrW hrV hr2 hαT hα1 hα2 hαx
  obtain ⟨ω, hω⟩ := exists_orderOf_three e
  refine ⟨(ω : MulAut (UT T M)), ω.2, by rw [Subgroup.orderOf_coe]; exact hω, fun w hyw => ?_⟩
  by_contra hw
  have h1 := c.odd_fix_trivial hrW hrV hr2 hαT hα1 hαx ω.2
    (by rw [Subgroup.orderOf_coe, hω]; decide) hw hyw
  have h2 : orderOf (ω : MulAut (UT T M)) = 1 := by rw [h1]; exact orderOf_one
  rw [Subgroup.orderOf_coe, hω] at h2
  omega

end Model

end S143

end CFSG.Quasithin
