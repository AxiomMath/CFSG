module

public import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5CalL0

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic CFSG.Quasithin.G11 CFSG.Quasithin CFSG.Open
  CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (HasCompFactor)

variable {G : Type} [Group G] [Finite G]

theorem not_hasCompFactor_sup_of_normal_zero (hB : ListBNonabelian) {H N T : Subgroup G}
    (hNH : N ≤ H) (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hTH : T ≤ H) (hT : IsPGroup 2 ↥T)
    (hH : ¬ HasCompFactor H IsCalL0) : ¬ HasCompFactor (N ⊔ T) IsCalL0 := by
  rintro ⟨L, hLgrp, hLc, hcal⟩
  letI := hLgrp
  have hNX : N ≤ N ⊔ T := le_sup_left
  have hTX : T ≤ N ⊔ T := le_sup_right
  have hXH : N ⊔ T ≤ H := sup_le hNH hTH
  let A : Subgroup ↥(N ⊔ T) := N.subgroupOf (N ⊔ T)
  have hAn : A.Normal := by
    refine ⟨fun a ha x => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hNn (x : G) (hXH x.2) a ha
  haveI := hAn
  rcases isCompositionFactor_of_normal A hLc with hA | hQ
  ·
    have hLN : E1.IsCompositionFactor ↥N L :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe hNX)).mp hA
    have hNnorm : (N.subgroupOf H).Normal := by
      refine ⟨fun a ha x => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      exact hNn (x : G) x.2 a ha
    haveI := hNnorm
    have hLN' : E1.IsCompositionFactor ↥(N.subgroupOf H) L :=
      (CFSG.Quasithin.H13.L829N.isCompositionFactor_congr
        (Subgroup.subgroupOfEquivOfLe hNH)).mpr hLN
    exact hH ⟨L, hLgrp, kbr_isCompositionFactor_of_normal_subgroup (N.subgroupOf H) hLN', hcal⟩
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hPq : IsPGroup 2 (↥(N ⊔ T) ⧸ A) := by
      let g : ↥T →* ↥(N ⊔ T) ⧸ A :=
        (QuotientGroup.mk' A).comp (Subgroup.inclusion hTX)
      have hg : Function.Surjective g := by
        intro q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective A q
        have hsup : (N.subgroupOf (N ⊔ T)) ⊔ (T.subgroupOf (N ⊔ T)) = ⊤ := by
          rw [← Subgroup.subgroupOf_sup hNX hTX]
          exact Subgroup.subgroupOf_self (N ⊔ T)
        have hx : x ∈ (N.subgroupOf (N ⊔ T)) ⊔ (T.subgroupOf (N ⊔ T)) := by
          rw [hsup]; exact Subgroup.mem_top x
        obtain ⟨n, hn, t, ht, hnt⟩ :=
          (Subgroup.mem_sup_of_normal_left
            (s := N.subgroupOf (N ⊔ T)) (t := T.subgroupOf (N ⊔ T))).mp hx
        refine ⟨⟨(t : G), Subgroup.mem_subgroupOf.mp ht⟩, ?_⟩
        have hgapp : g ⟨(t : G), Subgroup.mem_subgroupOf.mp ht⟩ =
            QuotientGroup.mk' A t := by
          apply congrArg (QuotientGroup.mk' A)
          exact Subtype.ext rfl
        have hn1 : QuotientGroup.mk' A n = 1 := (QuotientGroup.eq_one_iff n).mpr hn
        calc g ⟨(t : G), Subgroup.mem_subgroupOf.mp ht⟩
            = QuotientGroup.mk' A t := hgapp
          _ = QuotientGroup.mk' A (n * t) := by rw [map_mul, hn1, one_mul]
          _ = QuotientGroup.mk' A x := by rw [hnt]
      exact hT.of_surjective g hg
    haveI : Group.IsNilpotent (↥(N ⊔ T) ⧸ A) := hPq.isNilpotent
    obtain ⟨a, b, hab⟩ := hB L ((isCalL0_iff_asc1930ListB L).mp hcal)
    exact hab (uc22p20a_abelian_of_compositionFactor inferInstance hQ a b)

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem sup_eq_of_normal_not_le_kerMV_zero (hB : ListBNonabelian) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i) {N : Subgroup G} (hNH : N ≤ H)
    (hNn : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hNK : ¬ N ≤ kerMV V H) : N ⊔ D.T = H := by
  have hTH : D.T ≤ H := c.hyp.hyp171.2.1
  by_contra hne
  have hlt : N ⊔ D.T < H := lt_of_le_of_ne (sup_le hNH hTH) hne
  have hX : ¬ HasCompFactor (N ⊔ D.T) IsCalL0 :=
    not_hasCompFactor_sup_of_normal_zero hB hNH hNn hTH c.hyp.isSylowIn_T.isPGroup
      (not_concl182_iff.mp h2).2.2
  have hM : N ⊔ D.T ≤ D.M := c.le_normalizer_zero h2 le_sup_right hlt hX
  refine hNK (le_kerMV_of_normal hNH hNn ?_)
  rw [c.hyp.setting.normalizer_eq]
  exact le_sup_left.trans hM

theorem two_quotient_img_zero (hB : ListBNonabelian) (c : MinCex183 D V₀ V H i)
    (h2 : ¬ Concl182 D V₀ V H i)
    (M : ModDataE H (eOmegaZ H D.T)) {Kk : Subgroup ↥(M.img H)}
    (hKk : ∀ (j : ↥H) (r : ↥(M.img H)), (r : LGL 2 M.W) = M.ρ j →
      (r ∈ Kk ↔ (j : G) ∈ kerMV V H))
    {N : Subgroup ↥(M.img H)} (hN : N.Normal) (hNK : ¬ N ≤ Kk) :
    ∀ y : ↥(M.img H), ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
  obtain ⟨π, hπs, hπval, -⟩ := M.exists_surjective_img
  let N' : Subgroup G := (N.comap π).map H.subtype
  have hN'H : N' ≤ H := Subgroup.map_subtype_le _
  have hN'eq : N'.subgroupOf H = N.comap π := by
    show ((N.comap π).map H.subtype).comap H.subtype = N.comap π
    rw [Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
  have hN'norm : (N'.subgroupOf H).Normal := by
    rw [hN'eq]
    exact hN.comap π
  have hN'n : ∀ h ∈ H, ∀ n ∈ N', h * n * h⁻¹ ∈ N' := by
    intro h hh n hn
    obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.1 hn
    refine Subgroup.mem_map.2 ⟨⟨h, hh⟩ * j * ⟨h, hh⟩⁻¹, ?_, rfl⟩
    rw [Subgroup.mem_comap, map_mul, map_mul, map_inv]
    exact hN.conj_mem (π j) (Subgroup.mem_comap.mp hj) (π ⟨h, hh⟩)
  have hN'K : ¬ N' ≤ kerMV V H := by
    intro hle
    obtain ⟨r, hrN, hrK⟩ := SetLike.not_le_iff_exists.mp hNK
    obtain ⟨j, -, hj⟩ := M.mem_img.1 r.2
    have hjr : π j = r := Subtype.ext ((hπval j).trans hj)
    have hjN' : (j : G) ∈ N' := by
      refine Subgroup.mem_map.2 ⟨j, ?_, rfl⟩
      rw [Subgroup.mem_comap, hjr]
      exact hrN
    exact hrK ((hKk j r hj.symm).mpr (hle hjN'))
  have hsup : N' ⊔ D.T = H :=
    MinCex183.sup_eq_of_normal_not_le_kerMV_zero hB c h2 hN'H hN'n hN'K
  have hTH : D.T ≤ H := c.hyp.hyp171.2.1
  have hsupH : (N'.subgroupOf H) ⊔ (D.T.subgroupOf H) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hN'H hTH, hsup]
    exact Subgroup.subgroupOf_self H
  let Tsub : Subgroup (LGL 2 M.W) := M.img D.T
  let TsubH : Subgroup ↥(M.img H) := Tsub.subgroupOf (M.img H)
  have hTsub_le : Tsub ≤ M.img H := M.img_mono hTH
  have hTsubH2 : IsPGroup 2 ↥TsubH :=
    (M.isPGroup_img (S := D.T) c.hyp.isSylowIn_T.isPGroup).of_equiv
      (Subgroup.subgroupOfEquivOfLe hTsub_le).symm
  intro y
  obtain ⟨j, rfl⟩ := hπs y
  have hjmem : j ∈ (N'.subgroupOf H) ⊔ (D.T.subgroupOf H) := by
    rw [hsupH]; exact Subgroup.mem_top j
  haveI := hN'norm
  obtain ⟨n, hn, t, ht, hnt⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := N'.subgroupOf H)
      (t := D.T.subgroupOf H)).mp hjmem
  have hmem_n : π n ∈ N := by
    have h1 : n ∈ N.comap π := by rw [← hN'eq]; exact hn
    exact Subgroup.mem_comap.mp h1
  have hmem_t : π t ∈ TsubH := by
    show π t ∈ Tsub.subgroupOf (M.img H)
    rw [Subgroup.mem_subgroupOf]
    refine M.mem_img.2 ⟨t, Subgroup.mem_subgroupOf.mp ht, (hπval t).symm⟩
  obtain ⟨a, ha⟩ := hTsubH2 ⟨π t, hmem_t⟩
  refine ⟨a, (QuotientGroup.eq_one_iff ((π j) ^ 2 ^ a)).mp ?_⟩
  have hq : (QuotientGroup.mk' N (π j)) ^ 2 ^ a = 1 := by
    have hntπ : π n * π t = π j := by rw [← map_mul, hnt]
    have h1 : QuotientGroup.mk' N (π j) = QuotientGroup.mk' N (π t) := by
      rw [← hntπ, map_mul]
      have hn1 : QuotientGroup.mk' N (π n) = 1 := (QuotientGroup.eq_one_iff (π n)).mpr hmem_n
      rw [hn1, one_mul]
    have ht1 : (π t) ^ 2 ^ a = 1 := by
      have h := congrArg Subtype.val ha
      simpa using h
    rw [h1, ← map_pow, ht1, map_one]
  simpa [map_pow] using hq

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
