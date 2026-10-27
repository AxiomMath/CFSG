module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Hall.theorem_14_4_1
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core

namespace CFSG
end CFSG
open CFSG

/-!
# Hall Corollary 14.4.2

Source interface for the Engel special case preceding Hall-Wielandt.
-/

namespace CFSG.BenderSuzuki
namespace External

open scoped commutatorElement

universe u

private theorem hall_normal_commutator_lt_of_nilpotent
    {S : Type*} [Group S] [Group.IsNilpotent S]
    (A : Subgroup S) [A.Normal] (hA : A ≠ ⊥) :
    ⁅A, (⊤ : Subgroup S)⁆ < A := by
  have hle : ⁅A, (⊤ : Subgroup S)⁆ ≤ A := Subgroup.commutator_le_left A ⊤
  refine lt_of_le_of_ne hle ?_
  intro heq
  have hseries : ∀ n : ℕ, A ≤ (⊤ : Subgroup S).lowerCentralSeries n := by
    intro n
    induction n with
    | zero => simp [Subgroup.lowerCentralSeries_zero]
    | succ n ih =>
        rw [← heq]
        rw [show (⊤ : Subgroup S).lowerCentralSeries (n + 1) =
          ⁅(⊤ : Subgroup S).lowerCentralSeries n, (⊤ : Subgroup S)⁆ by
            exact Subgroup.lowerCentralSeries_succ (⊤ : Subgroup S) n]
        exact Subgroup.commutator_mono ih le_rfl
  obtain ⟨n, hn⟩ := Subgroup.nilpotent_iff_lowerCentralSeries.mp
    (inferInstance : Group.IsNilpotent S)
  apply hA
  apply le_antisymm
  · simpa [hn] using hseries n
  · exact bot_le

/-- If the p-residual of H is proper in Hall's intersection setup, then the
transfer modulus is proper as well. -/
public theorem hallTransferModulus_proper_of_residual_lt
    {G : Type*} [Group G] [Finite G] (p : ℕ) [Fact p.Prime]
    (H₁ G₀ H : Subgroup G)
    (hG₀ : G₀ = hallPResidual p G)
    (hH : H = G₀ ⊓ H₁)
    (hres_lt : (hallPResidual p H).map H.subtype < H) :
    hallTransferModulus p H H₁ < H := by
  classical
  have hH_le_H₁ : H ≤ H₁ := by
    rw [hH]
    exact inf_le_right
  have hmod_le : hallTransferModulus p H H₁ ≤ H :=
    hallTransferModulus_le_of_inf p H₁ G₀ H hG₀ hH
  have hG₀_normal : G₀.Normal := by
    subst G₀
    exact hallPResidual_normal p G
  have hHsub_normal : (H.subgroupOf H₁).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hH_le_H₁]
    intro x n hx hn
    rw [hH] at hx ⊢
    exact ⟨hG₀_normal.conj_mem x hx.1 n,
      H₁.mul_mem (H₁.mul_mem hn hx.2) (H₁.inv_mem hn)⟩
  let R : Subgroup H₁ := hallPResidual p H₁
  letI : R.Normal := hallPResidual_normal p H₁
  let q : H₁ →* H₁ ⧸ R := QuotientGroup.mk' R
  let ι : H →* H₁ := H.subtype.codRestrict H₁ (fun x => hH_le_H₁ x.2)
  let φ : H →* H₁ ⧸ R := q.comp ι
  let A : Subgroup (H₁ ⧸ R) := φ.range
  have hA_eq : A = (H.subgroupOf H₁).map q := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨ι x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), hx⟩, rfl⟩
  letI : A.Normal := by
    rw [hA_eq]
    exact QuotientGroup.map_normal R (H.subgroupOf H₁)
  have hquot_p : IsPGroup p (H₁ ⧸ R) := by
    simpa [R] using hallPResidual_quotient_isPGroup (G := H₁) p
  letI : Fact (IsPGroup p A) := ⟨hquot_p.to_subgroup A⟩
  have hres_map :
      (hallPResidual p H₁).map H₁.subtype =
        (hallPResidual p H).map H.subtype :=
    hallPResidual_map_inf_eq p H₁ G₀ H hG₀ hH
  have hA_ne_bot : A ≠ ⊥ := by
    obtain ⟨x, hxH, hxnot⟩ := SetLike.exists_of_lt hres_lt
    let x₁ : H₁ := ⟨x, hH_le_H₁ hxH⟩
    have hx₁_not : x₁ ∉ R := by
      intro hxR
      apply hxnot
      rw [← hres_map]
      exact Subgroup.mem_map.mpr ⟨x₁, hxR, rfl⟩
    have hφx_ne : φ ⟨x, hxH⟩ ≠ 1 := by
      intro heq
      apply hx₁_not
      exact (QuotientGroup.eq_one_iff (N := R) (x := x₁)).1 heq
    intro hbot
    have hmem : φ ⟨x, hxH⟩ ∈ A := ⟨⟨x, hxH⟩, rfl⟩
    rw [hbot] at hmem
    exact hφx_ne (by simpa using hmem)
  letI : Group.IsNilpotent (H₁ ⧸ R) := hquot_p.isNilpotent
  let C : Subgroup (H₁ ⧸ R) := ⁅A, (⊤ : Subgroup (H₁ ⧸ R))⁆
  have hC_lt : C < A :=
    hall_normal_commutator_lt_of_nilpotent A hA_ne_bot
  have hC_le : C ≤ A := hC_lt.le
  let T : Subgroup A := C.subgroupOf A ⊔ frattini A
  have hT_lt : T < (⊤ : Subgroup A) := by
    have hCsub_lt : C.subgroupOf A < (⊤ : Subgroup A) := by
      rw [← Subgroup.map_subtype_lt_map_subtype]
      rw [Subgroup.map_subgroupOf_eq_of_le hC_le]
      rw [show Subgroup.map A.subtype (⊤ : Subgroup A) = A by
        ext x
        simp]
      exact hC_lt
    apply lt_top_iff_ne_top.mpr
    intro htop
    have hCtop : C.subgroupOf A = ⊤ :=
      frattini_nongenerating (G := A) (K := C.subgroupOf A) htop
    exact hCsub_lt.ne hCtop
  let f : H →* A := φ.rangeRestrict
  let K : Subgroup H := T.comap f
  have hf_surj : Function.Surjective f := by
    exact φ.rangeRestrict_surjective
  have hK_lt : K < (⊤ : Subgroup H) := by
    have hcomap_lt :
        T.comap f < (⊤ : Subgroup A).comap f :=
      (Subgroup.comap_lt_comap_of_surjective (f := f) hf_surj).2 hT_lt
    simpa [K] using hcomap_lt
  have hcomm_le_H : ⁅H, H₁⁆ ≤ H :=
    (le_sup_right.trans le_sup_left).trans hmod_le
  have hpower_le :
      hallPPowerSubgroup p H ≤ K.map H.subtype := by
    unfold hallPPowerSubgroup
    rw [Subgroup.closure_le]
    rintro x ⟨h, rfl⟩
    refine Subgroup.mem_map.mpr ⟨h ^ p, ?_, by simp⟩
    change f (h ^ p) ∈ T
    apply (show frattini A ≤ T by simp [T])
    simpa using
      pth_power_mem_frattini_of_isPGroup (R := A) (p := p) (f h)
  have hcomm_le :
      ⁅H, H₁⁆ ≤ K.map H.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    let xH : H := ⟨⁅a, b⁆,
      hcomm_le_H (Subgroup.commutator_mem_commutator ha hb)⟩
    refine Subgroup.mem_map.mpr ⟨xH, ?_, rfl⟩
    change f xH ∈ T
    apply (show C.subgroupOf A ≤ T by simp [T])
    change (f xH : H₁ ⧸ R) ∈ C
    have hcomm_mem :
        ⁅(f ⟨a, ha⟩ : H₁ ⧸ R), q ⟨b, hb⟩⁆ ∈ C :=
      Subgroup.commutator_mem_commutator
        (f ⟨a, ha⟩).2 (by simp)
    have hfx :
        (f xH : H₁ ⧸ R) = ⁅(f ⟨a, ha⟩ : H₁ ⧸ R), q ⟨b, hb⟩⁆ := by
      change q (ι xH) = ⁅q (ι ⟨a, ha⟩), q ⟨b, hb⟩⁆
      rw [← map_commutatorElement]
      congr 1
    rw [hfx]
    exact hcomm_mem
  have hres_le :
      (hallPResidual p H).map H.subtype ≤ K.map H.subtype := by
    rintro x ⟨h, hh, rfl⟩
    refine Subgroup.mem_map.mpr ⟨h, ?_, rfl⟩
    change f h ∈ T
    have hh_ambient :
        (h : G) ∈ (hallPResidual p H).map H.subtype :=
      Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
    rw [← hres_map] at hh_ambient
    rcases Subgroup.mem_map.mp hh_ambient with ⟨r, hr, hre⟩
    have hι_mem : ι h ∈ R := by
      have hir : ι h = r := by
        ext
        exact hre.symm
      simpa [hir, R] using hr
    have hq_one : q (ι h) = 1 :=
      (QuotientGroup.eq_one_iff (N := R) (x := ι h)).2 hι_mem
    have hf_one : f h = 1 := by
      apply Subtype.ext
      exact hq_one
    rw [hf_one]
    exact T.one_mem
  have hmod_le_mapK :
      hallTransferModulus p H H₁ ≤ K.map H.subtype := by
    unfold hallTransferModulus
    exact sup_le (sup_le hpower_le hcomm_le) hres_le
  have hsub_le_K :
      (hallTransferModulus p H H₁).subgroupOf H ≤ K := by
    intro x hx
    have hxmap := hmod_le_mapK hx
    rcases Subgroup.mem_map.mp hxmap with ⟨y, hy, hyx⟩
    have hy_eq : y = x := by
      ext
      exact hyx
    simpa [hy_eq] using hy
  have hsub_lt :
      (hallTransferModulus p H H₁).subgroupOf H <
        (⊤ : Subgroup H) :=
    lt_of_le_of_lt hsub_le_K hK_lt
  rw [← Subgroup.map_subtype_lt_map_subtype] at hsub_lt
  rw [Subgroup.map_subgroupOf_eq_of_le hmod_le] at hsub_lt
  rw [show Subgroup.map H.subtype (⊤ : Subgroup H) = H by
    ext x
    simp] at hsub_lt
  exact hsub_lt


end External
end CFSG.BenderSuzuki
