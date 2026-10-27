module

public import CFSG.Monster.Existence.BabyW3Co1
public import CFSG.Monster.Existence.EbFrame
public import CFSG.Monster.AxisCount.SetupGroups
public import CFSG.Monster.Existence.Census.CosetOneFusion

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Visible CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.Griess CFSG.Monster.Generated CFSG.Monster.B CFSG.Monster.B.TwoA.Census

@[expose] noncomputable def trVis (g : Gvis) : ℚ :=
  LinearMap.trace ℚ SpaceB ((g : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB →ₗ[ℚ] SpaceB)

theorem trVis_conj (s f : Gvis) : trVis (s * f * s⁻¹) = trVis f :=
  CFSG.Monster.B.trace_conj (s : SpaceB ≃ₗ[ℚ] SpaceB) (f : SpaceB ≃ₗ[ℚ] SpaceB)

theorem trVis_conj' (s f : Gvis) : trVis (s⁻¹ * f * s) = trVis f := by
  have h := trVis_conj s⁻¹ f
  rwa [inv_inv] at h

theorem trVis_cosetRep_one :
    trVis (cosetRep 1) = 4372 := by
  have h := CFSG.Monster.B.trace_conj (tauB ^ 2) (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)
  rw [Census.trialityWitness_one] at h
  exact h.symm.trans (trace_of_mem_shortInv rhoEquiv_qP_zero_three_sixty_mem_shortInv)

theorem trVis_cosetElt_sixtythree :
    trVis (cosetElt 1 63) = 276 := by
  have h := CFSG.Monster.B.trace_conj (tauB ^ 2)
    (rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB))
  rw [Census.trialityWitness_two] at h
  obtain ⟨g, -, hg⟩ := exists_Gmat_conj_rhoEquiv_qP_one_sixty_sixty
  have h2 := CFSG.Monster.B.trace_conj g xmat
  rw [hg, trace_xmat] at h2
  have h3 : trVis (cosetElt 1 63) = LinearMap.trace ℚ SpaceB
      ((rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) : SpaceB ≃ₗ[ℚ] SpaceB) :
        SpaceB →ₗ[ℚ] SpaceB) := by
    unfold trVis
    rw [Census.cosetElt_sixtythree]
  rw [h3, ← h, h2]

theorem trVis_ne :
    trVis (cosetRep 1) ≠ trVis (cosetElt 1 63) := by
  rw [trVis_cosetRep_one, trVis_cosetElt_sixtythree]
  norm_num

@[expose] noncomputable def stabR1 :
    Subgroup Gvis :=
  (Subgroup.centralizer ({piVis (cosetRep 1)} : Set (latticeO ⧸ Subgroup.zpowers negOneO)ᵐᵒᵖ)).comap
    piVis

theorem mem_stabR1_iff (g : Gvis) :
    g ∈ stabR1 ↔ piVis g * piVis (cosetRep 1) = piVis (cosetRep 1) * piVis g := by
  rw [stabR1, Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]

theorem rhoQvis_le_stabR1 :
    rhoQvis ≤ stabR1 := by
  intro q hq
  rw [mem_stabR1_iff]
  have h : piVis q = 1 := by
    rw [← MonoidHom.mem_ker, ker_piVis]
    exact hq
  simp [h]

theorem centralizer_le_stabR1 :
    Subgroup.centralizer ({cosetRep 1} : Set Gvis) ≤ stabR1 := by
  intro g hg
  rw [mem_stabR1_iff, ← map_mul, ← map_mul]
  congr 1
  exact Subgroup.mem_centralizer_singleton_iff.1 hg

theorem natCard_stabR1 :
    Nat.card stabR1 = 2 ^ 25 * (2 ^ 21 * 3 ^ 5 * 5 ^ 2 * 7) := by
  rw [stabR1, TwoA.natCard_comap_of_surjective (MonoidHom.range_eq_top.1 range_piVis),
    ker_piVis, natCard_rhoQvis, natCard_centralizer_piVis_cosetRep_one]

theorem cosetRep_one_mul_self :
    cosetRep 1 * cosetRep 1 = 1 :=
  Subtype.ext cosetRep_sq.1

theorem mem_cosetInv_conj
    {g : Gvis} (hg : g ∈ stabR1) : g⁻¹ * cosetRep 1 * g ∈ cosetInv 1 := by
  refine ⟨?_, ?_⟩
  · rw [mem_cosetR_iff]
    have h := (mem_stabR1_iff g).1 hg
    rw [map_mul, map_mul, map_inv]
    calc (piVis g)⁻¹ * piVis (cosetRep 1) * piVis g
        = (piVis g)⁻¹ * (piVis g * piVis (cosetRep 1)) := by rw [h, mul_assoc]
      _ = piVis (cosetRep 1) := by rw [inv_mul_cancel_left]
  · calc g⁻¹ * cosetRep 1 * g * (g⁻¹ * cosetRep 1 * g)
        = g⁻¹ * (cosetRep 1 * cosetRep 1) * g := by group
      _ = 1 := by rw [cosetRep_one_mul_self]; group

theorem classRep_zero_eq :
    classRep 0 = cosetRep 1 :=
  (Census.classRep_zero).trans (Subtype.ext Census.cosetElt_zero)

theorem classRep_four_eq :
    classRep 4 = cosetElt 1 63 := Census.classRep_four

theorem qmatClass_conj (g f : Gvis) :
    qmatClass (g⁻¹ * f * g) = (fun x => g⁻¹ * x * g) '' qmatClass f := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    have hn : g * u * g⁻¹ ∈ rhoQ.subgroupOf Gvis := by
      have h : (rhoQ.subgroupOf Gvis).Normal := by
        rw [← ker_piVis]
        infer_instance
      exact h.conj_mem u hu g
    refine ⟨(g * u * g⁻¹)⁻¹ * f * (g * u * g⁻¹), ⟨_, hn, rfl⟩, ?_⟩
    show g⁻¹ * ((g * u * g⁻¹)⁻¹ * f * (g * u * g⁻¹)) * g = u⁻¹ * (g⁻¹ * f * g) * u
    group
  · rintro ⟨x, ⟨u, hu, rfl⟩, rfl⟩
    have hn : g⁻¹ * u * g ∈ rhoQ.subgroupOf Gvis := by
      have h : (rhoQ.subgroupOf Gvis).Normal := by
        rw [← ker_piVis]
        infer_instance
      have := h.conj_mem u hu g⁻¹
      rwa [inv_inv] at this
    refine ⟨g⁻¹ * u * g, hn, ?_⟩
    show g⁻¹ * (u⁻¹ * f * u) * g = (g⁻¹ * u * g)⁻¹ * (g⁻¹ * f * g) * (g⁻¹ * u * g)
    group

theorem ncard_qmatClass_conj (g f : Gvis) :
    (qmatClass (g⁻¹ * f * g)).ncard = (qmatClass f).ncard := by
  rw [qmatClass_conj]
  exact Set.ncard_image_of_injective _ (fun a b h => by simpa using h)

theorem ncard_qmatClass_h1 :
    (qmatClass (cosetRep 1)).ncard = 256 := by
  have h := ncard_qmatClass_classRep (k := 0) (by norm_num)
  rw [classRep_zero_eq, classSize_eq 0 (by norm_num)] at h
  simpa using h

theorem mem_qmatClass_trVis {f g : Gvis} (h : g ∈ qmatClass f) : trVis g = trVis f := by
  obtain ⟨u, -, rfl⟩ := h
  exact trVis_conj' u f

theorem orbit_stabR1_eq :
    {u : Gvis | ∃ g ∈ stabR1, u = g⁻¹ * cosetRep 1 * g} = qmatClass (cosetRep 1) := by
  ext f
  constructor
  · rintro ⟨g, hg, rfl⟩
    obtain ⟨k, hk, hfk⟩ := mem_qmatClass_of_mem_cosetInv_one (mem_cosetInv_conj hg)
    have hcard : (qmatClass (classRep k)).ncard = 256 := by
      rw [← qmatClass_eq_of_mem hfk, ncard_qmatClass_conj, ncard_qmatClass_h1]
    rw [ncard_qmatClass_classRep hk, classSize_eq k hk] at hcard
    have hk04 : k = 0 ∨ k = 4 := by
      by_contra hne
      have h512 : (if k = 0 ∨ k = 4 then 256 else 512) = 512 := by simp [hne]
      rw [h512] at hcard
      omega
    rcases hk04 with rfl | rfl
    · rw [classRep_zero_eq] at hfk
      exact hfk
    · exfalso
      rw [classRep_four_eq] at hfk
      have h1 := mem_qmatClass_trVis hfk
      rw [trVis_cosetElt_sixtythree] at h1
      have h2 := trVis_conj' g (cosetRep 1)
      rw [h1, trVis_cosetRep_one] at h2
      norm_num at h2
  · rintro ⟨u, hu, rfl⟩
    exact ⟨u, rhoQvis_le_stabR1 hu, rfl⟩

theorem natCard_stabR1_eq :
    Nat.card stabR1 = 256 * Nat.card ↥(Subgroup.centralizer ({cosetRep 1} : Set Gvis)) := by
  have h := ncard_conj_mul_natCard_inf_centralizer stabR1 (cosetRep 1)
  rw [orbit_stabR1_eq, ncard_qmatClass_h1,
    inf_eq_right.2 centralizer_le_stabR1] at h
  exact h.symm

theorem natCard_centralizer_cosetRep_one :
    Nat.card ↥(Subgroup.centralizer ({cosetRep 1} : Set Gvis)) = 2 ^ 38 * 3 ^ 5 * 5 ^ 2 * 7 := by
  have h := natCard_stabR1_eq
  rw [natCard_stabR1] at h
  omega

end CFSG.Monster.Existence
