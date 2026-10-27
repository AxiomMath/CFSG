module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2QOne
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2CentE2

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.Cent

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
open scoped commutatorElement

set_option linter.unusedSectionVars false

section Defs

variable (K : Type) [Field K]

@[expose] def Pa : Subgroup (C K) :=
  (parabolicSubgroup Tag.G2 K {i0}).subgroupOf (adjointGroup Tag.G2 K)

@[expose] def Pr : Subgroup (C K) :=
  (parabolicSubgroup Tag.G2 K {i1}).subgroupOf (adjointGroup Tag.G2 K)

variable {K}

theorem mem_Pa_iff {g : C K} :
    g ∈ Pa K ↔ (g : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K {i0} := Iff.rfl

theorem mem_Pr_iff {g : C K} :
    g ∈ Pr K ↔ (g : ModGL Tag.G2 K) ∈ parabolicSubgroup Tag.G2 K {i1} := Iff.rfl

end Defs

section Main


variable {K : Type} [Field K] [CharP K 2]

theorem i0_ne_i1 : i0 ≠ i1 := by decide

theorem cz {s : K} (hs : s ≠ 0) : Subgroup.centralizer ({xc s} : Set (C K)) ≤ Pr K := by
  intro g hg
  rw [mem_Pr_iff]
  refine cent_gX_c_le hs g.2 ?_
  have h := Subgroup.mem_centralizer_singleton_iff.1 hg
  exact congrArg Subtype.val h

theorem ct : Subgroup.centralizer ({xv 1} : Set (C K)) ≤ Pa K := by
  intro g hg
  rw [mem_Pa_iff]
  refine cent_gX_v_le g.2 ?_
  have h := Subgroup.mem_centralizer_singleton_iff.1 hg
  exact congrArg Subtype.val h

theorem weylElt_conj_gX (i : Fin Tag.G2.rank) {γ : Fin Tag.G2.rank → ℤ} (hγ : IsRoot Tag.G2 γ)
    (s : K) : weylElt Tag.G2 K i 1 * gX γ s * (weylElt Tag.G2 K i 1)⁻¹ =
      gX (reflect Tag.G2 i γ) s := by
  obtain ⟨ε, hε, h⟩ := weylElt_mul_pinnedX_mul_inv K i hγ
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hε1 : ε = 1 := by
    have : (ε - 1) * (ε - 1) = 0 := by linear_combination hε + (1 - ε) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp this)
  rw [h s, hε1, one_mul]

theorem nR_mem_centralizer_xc (s : K) :
    (⟨weylElt Tag.G2 K i1 1, weylElt_mem_adjointGroup i1 1⟩ : C K) ∈
      Subgroup.centralizer ({xc s} : Set (C K)) := by
  refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
  have hrc : IsRoot Tag.G2 rC := (pos_TC rC (Set.mem_singleton _)).1
  have h := weylElt_conj_gX (K := K) i1 hrc s
  have hr : reflect Tag.G2 i1 rC = rC := List.ofFn_injective (by decide +kernel)
  rw [hr] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem nA_mem_centralizer_xv :
    (⟨weylElt Tag.G2 K i0 1, weylElt_mem_adjointGroup i0 1⟩ : C K) ∈
      Subgroup.centralizer ({xv 1} : Set (C K)) := by
  refine Subgroup.mem_centralizer_singleton_iff.2 (Subtype.ext ?_)
  have hrv : IsRoot Tag.G2 rV := (pos_TVBC rV (Or.inl rfl)).1
  have h := weylElt_conj_gX (K := K) i0 hrv 1
  rw [reflect_a_v] at h
  exact mul_inv_eq_iff_eq_mul.1 h

theorem nz : ¬ Subgroup.centralizer ({xc 1} : Set (C K)) ≤ Pa K := fun h => by
  have h1 := h (nR_mem_centralizer_xc (K := K) 1)
  rw [mem_Pa_iff, weylElt_mem_parabolicSubgroup_iff] at h1
  exact i0_ne_i1 (Set.mem_singleton_iff.1 h1).symm

theorem nt : ¬ Subgroup.centralizer ({xv 1} : Set (C K)) ≤ Pr K := fun h => by
  have h1 := h (nA_mem_centralizer_xv (K := K))
  rw [mem_Pr_iff, weylElt_mem_parabolicSubgroup_iff] at h1
  exact i0_ne_i1 (Set.mem_singleton_iff.1 h1)

theorem reflect_r_c : reflect Tag.G2 i1 rC = rC := List.ofFn_injective (by decide +kernel)

theorem reflect_image_TC_r : reflect Tag.G2 i1 '' TC = TC := by
  rw [TC, Set.image_singleton, reflect_r_c]

theorem weylElt_r_mem_normalizer_TC :
    weylElt Tag.G2 K i1 1 ∈ Subgroup.normalizer (rootSpan Tag.G2 K TC : Set (ModGL Tag.G2 K)) := by
  refine mem_normalizer_of_map_eq ?_
  rw [map_conj_weylElt_rootSpan K i1 1 (fun α hα => (pos_TC α hα).1), reflect_image_TC_r]

theorem parabolic_r_le_normalizer_TC :
    parabolicSubgroup Tag.G2 K {i1} ≤
      Subgroup.normalizer (rootSpan Tag.G2 K TC : Set (ModGL Tag.G2 K)) :=
  sup_le borel_le_normalizer_TC ((Subgroup.closure_le _).2 (by
    rintro _ ⟨j, hj, rfl⟩
    rw [Set.mem_singleton_iff.1 hj]
    exact weylElt_r_mem_normalizer_TC))

theorem mem_Xc_iff_rootSpan {g : C K} :
    g ∈ Xc K ↔ (g : ModGL Tag.G2 K) ∈ rootSpan Tag.G2 K TC := by
  rw [mem_rootSpan_TC_iff]
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, rfl⟩
  · rintro ⟨s, h⟩
    exact ⟨s, Subtype.ext h.symm⟩

theorem coe_nf_V (β γ : K) :
    ((nf 0 0 0 0 β γ : C K) : ModGL Tag.G2 K) = gX rB β * gX rC γ := by
  have h : nf (0 : K) 0 0 0 β γ = xb β * xc γ := by
    simp [nf, xa_zero, xr_zero, xu_zero, xv_zero]
  rw [h]
  rfl

theorem mem_V_iff_rootSpan {g : C K} :
    g ∈ V K ↔ (g : ModGL Tag.G2 K) ∈ rootSpan Tag.G2 K TBC := by
  rw [mem_rootSpan_TBC_iff]
  constructor
  · intro hg
    obtain ⟨β, γ, rfl⟩ := mem_V_iff.1 hg
    exact ⟨β, γ, coe_nf_V β γ⟩
  · rintro ⟨β, γ, h⟩
    have : g = nf 0 0 0 0 β γ := Subtype.ext (h.trans (coe_nf_V β γ).symm)
    rw [this]
    exact mem_V_iff.2 ⟨β, γ, rfl⟩

theorem le_normalizer_of_rootSpan {M : Subgroup (ModGL Tag.G2 K)} {T : Set (Fin Tag.G2.rank → ℤ)}
    {X P : Subgroup (C K)}
    (hX : ∀ g : C K, g ∈ X ↔ (g : ModGL Tag.G2 K) ∈ rootSpan Tag.G2 K T)
    (hM : M ≤ Subgroup.normalizer (rootSpan Tag.G2 K T : Set (ModGL Tag.G2 K)))
    (hP : ∀ p ∈ P, (p : ModGL Tag.G2 K) ∈ M) : P ≤ Subgroup.normalizer (X : Set (C K)) := by
  intro p hp
  rw [Subgroup.mem_normalizer_iff]
  intro h
  rw [hX, hX]
  have := Subgroup.mem_normalizer_iff.1 (hM (hP p hp)) (h : ModGL Tag.G2 K)
  simpa using this

theorem Pa_le_normalizer_V : Pa K ≤ Subgroup.normalizer (V K : Set (C K)) :=
  le_normalizer_of_rootSpan (fun _ => mem_V_iff_rootSpan) parabolic_a_le_normalizer_TBC
    (fun _ hp => hp)

theorem Pr_le_normalizer_Xc : Pr K ≤ Subgroup.normalizer (Xc K : Set (C K)) :=
  le_normalizer_of_rootSpan (fun _ => mem_Xc_iff_rootSpan) parabolic_r_le_normalizer_TC
    (fun _ hp => hp)

end Main

end CFSG.Quasithin.H13.F431.G2.Cent
