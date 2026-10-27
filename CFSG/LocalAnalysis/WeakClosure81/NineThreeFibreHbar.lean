module

public import CFSG.LocalAnalysis.WeakClosure81.NineThreeNine

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G] {V T A K S X : Subgroup G} {p : ℕ} {g x : G}

theorem nineI_le_nineH (V K : Subgroup G) : nineI V K ≤ nineH V K :=
  iSup₂_mono fun _ _ => inf_le_left

instance nine3_normal_nineI_subgroupOf (V K : Subgroup G) :
    ((nineI V K).subgroupOf (nineH V K)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (nineI_le_nineH V K)).mpr fun _ hh =>
    conjSubgroup_eq_iff_mem_normalizer.mp
      (Nine3Core.conjSubgroup_nineI (Nine3Choice.nineH_le_K hh))

abbrev Nine3Hbar (V K : Subgroup G) : Type := ↥(nineH V K) ⧸ (nineI V K).subgroupOf (nineH V K)

@[expose] noncomputable def nine3Pi (V K : Subgroup G) {p : ℕ} (ρ : ↥K →* Equiv.Perm (ZMod p))
    (hker : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → ρ k = 1) :
    Nine3Hbar V K →* Equiv.Perm (ZMod p) :=
  QuotientGroup.lift ((nineI V K).subgroupOf (nineH V K))
    (ρ.comp (Subgroup.inclusion Nine3Choice.nineH_le_K))
    (fun _ ha => hker _ (Nine3Core.nineI_le_pCoreOf (Subgroup.mem_subgroupOf.mp ha)))

theorem nine3Pi_mk (V K : Subgroup G) {p : ℕ} (ρ : ↥K →* Equiv.Perm (ZMod p))
    (hker : ∀ k : ↥K, (k : G) ∈ pCoreOf 2 K → ρ k = 1) (u : ↥(nineH V K)) :
    nine3Pi V K ρ hker (QuotientGroup.mk u) = ρ ⟨u, Nine3Choice.nineH_le_K u.2⟩ :=
  rfl

@[expose] def Nine3Dbar (V K : Subgroup G) : Set (Nine3Hbar V K) :=
  {d | ∃ U ∈ omegaIn V K (nineE V K), ∃ u : ↥(nineH V K), (u : G) ∈ U ∧
    (u : G) ∉ pCoreOf 2 K ∧ (QuotientGroup.mk u : Nine3Hbar V K) = d}

end CFSG.LocalAnalysis.WeakClosure81
