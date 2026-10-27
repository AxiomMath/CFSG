module

public import CFSG.Assembly.Defs
public import CFSG.Assembly.Subnormal
public import CFSG.LocalAnalysis.EvenBN.LinearThree.CentralLift

public section

namespace CFSG.StandardType

open CFSG.Assembly
open scoped Pointwise commutatorElement

variable {L R : Type*} [Group L] [Group R]

theorem ggQ2s08r6_map_comm_comap {π : L →* R} (hπ : Function.Surjective π) (S : Subgroup R)
    (hS : ⁅S, S⁆ = S) : (⁅S.comap π, S.comap π⁆).map π = S := by
  rw [Subgroup.map_commutator, Subgroup.map_comap_eq_self_of_surjective hπ S, hS]

theorem ggQ2s08r6_comap_eq_sup {π : L →* R} (hπ : Function.Surjective π) (S : Subgroup R)
    (hS : ⁅S, S⁆ = S) : S.comap π = ⁅S.comap π, S.comap π⁆ ⊔ π.ker := by
  have hmap : (⁅S.comap π, S.comap π⁆).map π = S := ggQ2s08r6_map_comm_comap hπ S hS
  refine le_antisymm ?_ (sup_le (Subgroup.commutator_le_self _) ?_)
  · intro p hp
    have hp' : π p ∈ (⁅S.comap π, S.comap π⁆).map π := by rw [hmap]; exact hp
    obtain ⟨q, hq, hqπ⟩ := Subgroup.mem_map.mp hp'
    have hmem : p ∈ ((⁅S.comap π, S.comap π⁆ ⊔ π.ker : Subgroup L) : Set L) := by
      rw [Subgroup.mul_normal]
      have hk : q⁻¹ * p ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hqπ]
        exact inv_mul_cancel _
      exact Set.mem_mul.mpr ⟨q, hq, q⁻¹ * p, hk, by group⟩
    exact hmem
  · intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_comap, hx]
    exact S.one_mem

theorem ggQ2s08r6_comm_comap_perfect {π : L →* R} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) (S : Subgroup R) (hS : ⁅S, S⁆ = S) :
    ⁅⁅S.comap π, S.comap π⁆, ⁅S.comap π, S.comap π⁆⁆ = ⁅S.comap π, S.comap π⁆ := by
  have hP : S.comap π = ⁅S.comap π, S.comap π⁆ ⊔ π.ker := ggQ2s08r6_comap_eq_sup hπ S hS
  refine le_antisymm (Subgroup.commutator_le_self _) ?_
  have hle : ⁅⁅S.comap π, S.comap π⁆ ⊔ π.ker, ⁅S.comap π, S.comap π⁆ ⊔ π.ker⁆ ≤
      ⁅⁅S.comap π, S.comap π⁆, ⁅S.comap π, S.comap π⁆⁆ :=
    CFSG.LocalAnalysis.EvenBN.LinearThree.commutator_sup_le_of_le_center hker
  calc ⁅S.comap π, S.comap π⁆
      = ⁅⁅S.comap π, S.comap π⁆ ⊔ π.ker, ⁅S.comap π, S.comap π⁆ ⊔ π.ker⁆ := by
        conv_lhs => rw [hP]
    _ ≤ ⁅⁅S.comap π, S.comap π⁆, ⁅S.comap π, S.comap π⁆⁆ := hle

private lemma ggQ2s08r6_isPerfect_of_commutator_eq_self {G : Type*} [Group G]
    {H : Subgroup G} (hH : ⁅H, H⁆ = H) : Group.IsPerfect ↥H := by
  rw [Group.isPerfect_def, eq_top_iff]
  intro x _
  have hx : (x : G) ∈ ⁅H, H⁆ := hH.symm ▸ x.2
  rw [← Subgroup.map_subtype_commutator H] at hx
  obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
  have hyx' : y = x := Subtype.ext hyx
  rwa [hyx'] at hy

private lemma ggQ2s08r6_center_eq_bot_of_isSimpleGroup (S : Subgroup R)
    (hS : ⁅S, S⁆ = S) (hSs : IsSimpleGroup ↥S) : Subgroup.center ↥S = ⊥ := by
  haveI : IsSimpleGroup ↥S := hSs
  haveI : Group.IsPerfect ↥S := ggQ2s08r6_isPerfect_of_commutator_eq_self hS
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥S) with h | h
  · exact h
  · exact absurd (Subgroup.center_eq_top_iff.mp h)
      (Group.IsPerfect.not_isMulCommutative (G := ↥S))

private lemma ggQ2s08r6_mem_center_comm_comap_aux {π : L →* R} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) (S : Subgroup R) (hS : ⁅S, S⁆ = S)
    (hScenter : Subgroup.center ↥S = ⊥) (q : ↥(⁅S.comap π, S.comap π⁆)) :
    (q ∈ Subgroup.center ↥(⁅S.comap π, S.comap π⁆)) ↔ π q = 1 := by
  have hmap : (⁅S.comap π, S.comap π⁆).map π = S := ggQ2s08r6_map_comm_comap hπ S hS
  constructor
  · intro hq
    have hqS : π (q : L) ∈ S :=
      Subgroup.mem_comap.mp (Subgroup.commutator_le_self (S.comap π) q.2)
    have hmem : (⟨π (q : L), hqS⟩ : ↥S) ∈ Subgroup.center ↥S := by
      rw [Subgroup.mem_center_iff]
      intro s
      obtain ⟨y, hy, hyπ⟩ := Subgroup.mem_map.mp
        (show (s : R) ∈ (⁅S.comap π, S.comap π⁆).map π by rw [hmap]; exact s.2)
      have hcomm : (⟨y, hy⟩ : ↥(⁅S.comap π, S.comap π⁆)) * q = q * ⟨y, hy⟩ :=
        Subgroup.mem_center_iff.mp hq ⟨y, hy⟩
      have h2 := congrArg (fun t : ↥(⁅S.comap π, S.comap π⁆) => π (t : L)) hcomm
      apply Subtype.ext
      simpa [map_mul, hyπ] using h2
    rw [hScenter] at hmem
    have h1 : (⟨π (q : L), hqS⟩ : ↥S) = 1 := by simpa using hmem
    simpa using congrArg (fun t : ↥S => (t : R)) h1
  · intro hq
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hq' : (q : L) ∈ π.ker := MonoidHom.mem_ker.mpr hq
    simpa using Subgroup.mem_center_iff.mp (hker hq') (y : L)

theorem ggQ2s08r6_comm_comap_quasisimple {π : L →* R} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) (S : Subgroup R) (hS : ⁅S, S⁆ = S)
    (hSs : IsSimpleGroup ↥S) : IsQuasisimple ↥(⁅S.comap π, S.comap π⁆) := by
  set Q : Subgroup L := ⁅S.comap π, S.comap π⁆
  have hScenter : Subgroup.center ↥S = ⊥ := ggQ2s08r6_center_eq_bot_of_isSimpleGroup S hS hSs
  have hQperf : ⁅Q, Q⁆ = Q := ggQ2s08r6_comm_comap_perfect hπ hker S hS
  have hperf : commutator ↥Q = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : (x : L) ∈ ⁅Q, Q⁆ := by rw [hQperf]; exact x.2
    rw [← Subgroup.map_subtype_commutator Q] at hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    have hyx' : y = x := Subtype.ext hyx
    rwa [hyx'] at hy
  have hmap : Q.map π = S := ggQ2s08r6_map_comm_comap hπ S hS
  let f : ↥Q →* ↥S :=
    { toFun := fun x =>
        ⟨π (x : L), Subgroup.mem_comap.mp (Subgroup.commutator_le_self (S.comap π) x.2)⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by apply Subtype.ext; simp [map_mul] }
  have hf : Function.Surjective f := by
    intro s
    have hs : (s : R) ∈ Q.map π := by rw [hmap]; exact s.2
    obtain ⟨x, hx, hxπ⟩ := Subgroup.mem_map.mp hs
    exact ⟨⟨x, hx⟩, Subtype.ext hxπ⟩
  have hfx : ∀ x : ↥Q, (f x = 1) ↔ π (x : L) = 1 := by
    intro x
    constructor
    · exact fun h => Subtype.ext_iff.mp h
    · exact fun h => Subtype.ext h
  have hkerf : f.ker = Subgroup.center ↥Q := by
    ext x
    rw [MonoidHom.mem_ker, hfx x]
    exact (ggQ2s08r6_mem_center_comm_comap_aux hπ hker S hS hScenter x).symm
  refine ⟨hperf, ?_⟩
  have e : (↥Q ⧸ Subgroup.center ↥Q) ≃* ↥S :=
    (QuotientGroup.quotientMulEquivOfEq hkerf.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective f hf)
  exact (MulEquiv.isSimpleGroup_congr e).mpr hSs

theorem ggQ2s08r6_mem_center_comm_comap {π : L →* R} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) (S : Subgroup R) (hS : ⁅S, S⁆ = S)
    (hSs : IsSimpleGroup ↥S) (q : ↥(⁅S.comap π, S.comap π⁆)) :
    q ∈ Subgroup.center ↥(⁅S.comap π, S.comap π⁆) ↔ π q = 1 :=
  ggQ2s08r6_mem_center_comm_comap_aux hπ hker S hS
    (ggQ2s08r6_center_eq_bot_of_isSimpleGroup S hS hSs) q

theorem ggQ2s08r6_comm_comap_sup {π : L →* R} (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center L) (hL : commutator L = ⊤) (S S' : Subgroup R)
    (hS : ⁅S, S⁆ = S) (hS' : ⁅S', S'⁆ = S') (hSS' : S ⊔ S' = ⊤) :
    ⁅S.comap π, S.comap π⁆ ⊔ ⁅S'.comap π, S'.comap π⁆ = ⊤ := by
  have hP : S.comap π = ⁅S.comap π, S.comap π⁆ ⊔ π.ker := ggQ2s08r6_comap_eq_sup hπ S hS
  have hP' : S'.comap π = ⁅S'.comap π, S'.comap π⁆ ⊔ π.ker := ggQ2s08r6_comap_eq_sup hπ S' hS'
  have hPP' : S.comap π ⊔ S'.comap π = ⊤ := by
    rw [Subgroup.comap_sup_eq (f := π) S S' hπ, hSS', Subgroup.comap_top]
  have hsupeq : S.comap π ⊔ S'.comap π =
      (⁅S.comap π, S.comap π⁆ ⊔ ⁅S'.comap π, S'.comap π⁆) ⊔ π.ker := by
    conv_lhs => rw [hP, hP']
    ac_rfl
  have htop : ⁅S.comap π ⊔ S'.comap π, S.comap π ⊔ S'.comap π⁆ ≤
      ⁅S.comap π, S.comap π⁆ ⊔ ⁅S'.comap π, S'.comap π⁆ := by
    calc ⁅S.comap π ⊔ S'.comap π, S.comap π ⊔ S'.comap π⁆
        = ⁅(⁅S.comap π, S.comap π⁆ ⊔ ⁅S'.comap π, S'.comap π⁆) ⊔ π.ker,
            (⁅S.comap π, S.comap π⁆ ⊔ ⁅S'.comap π, S'.comap π⁆) ⊔ π.ker⁆ := by
          rw [← hsupeq]
      _ ≤ ⁅⁅S.comap π, S.comap π⁆ ⊔ ⁅S'.comap π, S'.comap π⁆,
            ⁅S.comap π, S.comap π⁆ ⊔ ⁅S'.comap π, S'.comap π⁆⁆ :=
          CFSG.LocalAnalysis.EvenBN.LinearThree.commutator_sup_le_of_le_center hker
      _ ≤ _ := Subgroup.commutator_le_self _
  rw [eq_top_iff]
  calc (⊤ : Subgroup L) = ⁅(⊤ : Subgroup L), ⊤⁆ := hL.symm
    _ = ⁅S.comap π ⊔ S'.comap π, S.comap π ⊔ S'.comap π⁆ := by rw [hPP']
    _ ≤ ⁅S.comap π, S.comap π⁆ ⊔ ⁅S'.comap π, S'.comap π⁆ := htop

theorem ggQ2s08r6_isQuasisimple_map_subtype {G : Type*} [Group G] {H : Subgroup G}
    {Q : Subgroup ↥H} (hQ : IsQuasisimple ↥Q) : IsQuasisimple ↥(Q.map H.subtype) :=
  Assembly.IsQuasisimple.of_mulEquiv
    (Subgroup.equivMapOfInjective Q H.subtype (fun a b h => Subtype.ext h)).symm hQ

end CFSG.StandardType
