module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Huppert IV.5.2 transport core
-/

namespace CFSG.BenderSuzuki
namespace External

open PFchapter1section1 PFAppendixIII
open scoped Pointwise

universe u v

public theorem hkt_huppert_iv52_sylow_le_normalizer_centerIn
    {Q : Type u} [Group Q] {q : ℕ} (S : Sylow q Q) :
    (S : Subgroup Q) ≤
      Subgroup.normalizer ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem
    (centerIn (G := Q) (S : Subgroup Q)) (S : Subgroup Q) ?_
  intro s z hz
  have hs : (s : Q) ∈ (S : Subgroup Q) := s.property
  have hzC : z ∈ Subgroup.centralizer (((S : Subgroup Q) : Set Q)) := hz.2
  have hcomm : (s : Q) * z = z * (s : Q) :=
    (Subgroup.mem_centralizer_iff.mp hzC) (s : Q) hs
  have hconj_eq : (s : Q) * z * (s : Q)⁻¹ = z := by
    calc
      (s : Q) * z * (s : Q)⁻¹ = z * (s : Q) * (s : Q)⁻¹ := by rw [hcomm]
      _ = z := by simp [mul_assoc]
  simpa [hconj_eq] using hz

public theorem hkt_huppert_iv52_centers_eq_of_center_normalized
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (_hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hT_le_normalizer_center :
      (T : Subgroup Q) ≤
        Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)) :
    centerIn (G := Q) (S : Subgroup Q) =
      centerIn (G := Q) (T : Subgroup Q) := by
  classical
  let Z : Subgroup Q := centerIn (G := Q) (S : Subgroup Q)
  have hS_le_N : (S : Subgroup Q) ≤ Subgroup.normalizer ((Z : Subgroup Q) : Set Q) := by
    simpa [Z] using hkt_huppert_iv52_sylow_le_normalizer_centerIn (Q := Q) (q := q) S
  let N : Subgroup Q := Subgroup.normalizer ((Z : Subgroup Q) : Set Q)
  have hT_le_N : (T : Subgroup Q) ≤ N := by
    simpa [N, Z] using hT_le_normalizer_center
  let SN : Sylow q N := S.subtype hS_le_N
  let TN : Sylow q N := T.subtype hT_le_N
  obtain ⟨n, hn⟩ := MulAction.exists_smul_eq N TN SN
  have hTN_SN : (MulAut.conj n • (TN : Subgroup N) : Subgroup N) = (SN : Subgroup N) := by
    simpa only [Sylow.coe_subgroup_smul]
      using congrArg (fun P : Sylow q N => (P : Subgroup N)) hn
  have hconjT_eq_S :
      (MulAut.conj (n : Q) • (T : Subgroup Q) : Subgroup Q) = (S : Subgroup Q) := by
    ext x
    constructor
    · intro hx
      rcases hx with ⟨y, hyT, rfl⟩
      let yN : N := ⟨y, hT_le_N hyT⟩
      have hyTN : yN ∈ (TN : Subgroup N) := by
        change (yN : Q) ∈ (T : Subgroup Q)
        exact hyT
      have hySN : (MulAut.conj n) yN ∈ (SN : Subgroup N) := by
        simpa [hTN_SN] using
          Subgroup.smul_mem_pointwise_smul yN (MulAut.conj n) (TN : Subgroup N) hyTN
      change ((MulAut.conj (n : Q)) y) ∈ (S : Subgroup Q)
      simpa [SN, Sylow.coe_subtype, Subgroup.mem_subgroupOf, yN, MulAut.conj_apply]
        using hySN
    · intro hxS
      have hSN_TN : (MulAut.conj n)⁻¹ • (SN : Subgroup N) = (TN : Subgroup N) := by
        rw [← hTN_SN]
        simp
      let xN : N := ⟨x, hS_le_N hxS⟩
      have hxSN : xN ∈ (SN : Subgroup N) := by
        simpa [SN, Sylow.coe_subtype, Subgroup.mem_subgroupOf, xN] using hxS
      have hxTN : ((MulAut.conj n)⁻¹) xN ∈ (TN : Subgroup N) := by
        simpa [hSN_TN] using
          Subgroup.smul_mem_pointwise_smul xN ((MulAut.conj n)⁻¹) (SN : Subgroup N) hxSN
      refine ⟨((MulAut.conj n)⁻¹ xN : N), ?_, ?_⟩
      · change ((((MulAut.conj n)⁻¹ xN : N) : Q)) ∈ (T : Subgroup Q)
        exact hxTN
      · simp [MulAut.conj_apply, xN, mul_assoc]
  have hmapT_eq_conjT :
      (T : Subgroup Q).map (MulAut.conj (n : Q)).toMonoidHom =
        (MulAut.conj (n : Q) • (T : Subgroup Q) : Subgroup Q) := by
    ext x
    constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩
  have hmap_centerT :
      (centerIn (G := Q) (T : Subgroup Q)).map (MulAut.conj (n : Q)).toMonoidHom =
        centerIn (G := Q) (S : Subgroup Q) := by
    rw [centerIn_map_mulEquiv (MulAut.conj (n : Q)) (T : Subgroup Q)]
    rw [hmapT_eq_conjT, hconjT_eq_S]
  have hmap_centerS :
      (centerIn (G := Q) (S : Subgroup Q)).map (MulAut.conj (n : Q)).toMonoidHom =
        centerIn (G := Q) (S : Subgroup Q) := by
    ext x
    constructor
    · rintro ⟨y, hyZ, rfl⟩
      exact (n.property y).1 (by simpa [Z] using hyZ)
    · intro hxZ
      have hninv : ((n : Q)⁻¹) ∈ Subgroup.normalizer ((Z : Subgroup Q) : Set Q) :=
        (Subgroup.normalizer ((Z : Subgroup Q) : Set Q)).inv_mem n.property
      have hpre : (n : Q)⁻¹ * x * ((n : Q)⁻¹)⁻¹ ∈ Z :=
        (hninv x).1 (by simpa [Z] using hxZ)
      refine ⟨(n : Q)⁻¹ * x * (n : Q), by simpa [Z] using hpre, ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
  symm
  exact (Subgroup.map_injective (MulAut.conj (n : Q)).injective).eq_iff.mp (by
    rw [hmap_centerS, hmap_centerT])

public theorem hkt_huppert_iv52_center_element_commutes_with_other_sylow_of_double_normalization
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hT_le_normalizer_center :
      (T : Subgroup Q) ≤
        Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q))
    {z t : Q} (hz : z ∈ centerIn (G := Q) (S : Subgroup Q))
    (ht : t ∈ (T : Subgroup Q)) : z * t = t * z := by
  classical
  have hcenters :
      centerIn (G := Q) (S : Subgroup Q) =
        centerIn (G := Q) (T : Subgroup Q) :=
    hkt_huppert_iv52_centers_eq_of_center_normalized
      (Q := Q) (q := q) S T hcenter_le_T hT_le_normalizer_center
  have hzT : z ∈ centerIn (G := Q) (T : Subgroup Q) := by
    simpa [hcenters] using hz
  exact ((Subgroup.mem_centralizer_iff.mp hzT.2) t ht).symm

public theorem hkt_huppert_iv52_other_center_element_mem_sylow_of_double_normalization
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hT_le_normalizer_center :
      (T : Subgroup Q) ≤
        Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q))
    {z : Q} (hz : z ∈ centerIn (G := Q) (T : Subgroup Q)) :
    z ∈ (S : Subgroup Q) := by
  classical
  have hcenters :
      centerIn (G := Q) (S : Subgroup Q) =
        centerIn (G := Q) (T : Subgroup Q) :=
    hkt_huppert_iv52_centers_eq_of_center_normalized
      (Q := Q) (q := q) S T hcenter_le_T hT_le_normalizer_center
  have hzS : z ∈ centerIn (G := Q) (S : Subgroup Q) := by
    simpa [hcenters] using hz
  exact hzS.1

public theorem hkt_huppert_iv52_other_center_element_commutes_with_sylow_of_double_normalization
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hT_le_normalizer_center :
      (T : Subgroup Q) ≤
        Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q))
    {z s : Q} (hz : z ∈ centerIn (G := Q) (T : Subgroup Q))
    (hs : s ∈ (S : Subgroup Q)) : z * s = s * z := by
  classical
  have hcenters :
      centerIn (G := Q) (S : Subgroup Q) =
        centerIn (G := Q) (T : Subgroup Q) :=
    hkt_huppert_iv52_centers_eq_of_center_normalized
      (Q := Q) (q := q) S T hcenter_le_T hT_le_normalizer_center
  have hzS : z ∈ centerIn (G := Q) (S : Subgroup Q) := by
    simpa [hcenters] using hz
  exact ((Subgroup.mem_centralizer_iff.mp hzS.2) s hs).symm

public theorem hkt_huppert_iv52_center_le_other_center_of_double_normalization
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hT_le_normalizer_center :
      (T : Subgroup Q) ≤
        Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)) :
    centerIn (G := Q) (S : Subgroup Q) ≤
      centerIn (G := Q) (T : Subgroup Q) := by
  classical
  intro z hz
  refine ⟨hcenter_le_T hz, ?_⟩
  change z ∈ Subgroup.centralizer (((T : Subgroup Q) : Set Q))
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact (hkt_huppert_iv52_center_element_commutes_with_other_sylow_of_double_normalization
    (Q := Q) (q := q) S T hcenter_le_T hT_le_normalizer_center (z := z) (t := t) hz ht).symm

public theorem hkt_huppert_iv52_other_center_le_center_of_double_normalization
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hT_le_normalizer_center :
      (T : Subgroup Q) ≤
        Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)) :
    centerIn (G := Q) (T : Subgroup Q) ≤
      centerIn (G := Q) (S : Subgroup Q) := by
  classical
  intro z hz
  refine ⟨?_, ?_⟩
  · exact hkt_huppert_iv52_other_center_element_mem_sylow_of_double_normalization
      (Q := Q) (q := q) S T hcenter_le_T hT_le_normalizer_center hz
  · change z ∈ Subgroup.centralizer (((S : Subgroup Q) : Set Q))
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hkt_huppert_iv52_other_center_element_commutes_with_sylow_of_double_normalization
      (Q := Q) (q := q) S T hcenter_le_T hT_le_normalizer_center (z := z) (s := s) hz hs).symm

public theorem hkt_huppert_iv52_centers_eq_of_double_normalization
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hT_le_normalizer_center :
      (T : Subgroup Q) ≤
        Subgroup.normalizer
          ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q)) :
    centerIn (G := Q) (S : Subgroup Q) =
      centerIn (G := Q) (T : Subgroup Q) := by
  classical
  exact le_antisymm
    (hkt_huppert_iv52_center_le_other_center_of_double_normalization
      (Q := Q) (q := q) S T hcenter_le_T hT_le_normalizer_center)
    (hkt_huppert_iv52_other_center_le_center_of_double_normalization
      (Q := Q) (q := q) S T hcenter_le_T hT_le_normalizer_center)


/-- Huppert IV.5.2, normalizer-failure substep: the second Sylow cannot
normalize `Z(S)`, otherwise the two Sylow centers agree, contradicting the
weak-closure failure. -/
public theorem hkt_huppert_iv52_normalizer_failure_of_center_mismatch
    {Q : Type u} [Group Q] [Finite Q] {q : ℕ} [Fact q.Prime]
    (S T : Sylow q Q)
    (hcenter_le_T :
      centerIn (G := Q) (S : Subgroup Q) ≤ (T : Subgroup Q))
    (hcenter_ne_T :
      centerIn (G := Q) (S : Subgroup Q) ≠
        centerIn (G := Q) (T : Subgroup Q)) :
    ¬ (T : Subgroup Q) ≤
      Subgroup.normalizer
        ((centerIn (G := Q) (S : Subgroup Q) : Subgroup Q) : Set Q) := by
  classical
  intro hT_le_normalizer_center
  exact hcenter_ne_T
    (hkt_huppert_iv52_centers_eq_of_double_normalization
      (Q := Q) (q := q) S T hcenter_le_T hT_le_normalizer_center)

end External
end CFSG.BenderSuzuki
