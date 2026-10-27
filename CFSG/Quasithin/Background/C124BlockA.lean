module

public import CFSG.Quasithin.Background.C124Dict
public import CFSG.Quasithin.Background.C124Core
public import CFSG.Quasithin.Background.C124Perf

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem noTwoQuot_of_perfect {L : Subgroup G} (h : ⁅L, L⁆ = L) :
    ∀ (N : Subgroup ↥L) [N.Normal], IsPGroup 2 (↥L ⧸ N) → N = ⊤ := by
  intro N _ hp
  have : Group.IsPerfect ↥L := isPerfect_of_comm_eq h
  by_contra hN
  have hnt : Nontrivial (↥L ⧸ N) := QuotientGroup.nontrivial_iff.mpr hN
  have hq : Group.IsPerfect (↥L ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hn : Group.IsNilpotent (↥L ⧸ N) := hp.isNilpotent
  exact Group.IsPerfect.not_isNilpotent (↥L ⧸ N) hn

@[expose] def cqSub (X Q U : Subgroup G) (hQ : X ≤ Subgroup.normalizer (Q : Set G))
    (hU : X ≤ Subgroup.normalizer (U : Set G)) : Subgroup G where
  carrier := {x | x ∈ X ∧ ∀ q ∈ Q, ⁅q, x⁆ ∈ U}
  one_mem' := ⟨X.one_mem, fun q _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hx, hxq⟩ ⟨hy, hyq⟩
    refine ⟨X.mul_mem hx hy, fun q hq => ?_⟩
    have e : ⁅q, x * y⁆ = ⁅q, x⁆ * (x * ⁅q, y⁆ * x⁻¹) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact U.mul_mem (hxq q hq) ((Subgroup.mem_normalizer_iff.1 (hU hx) _).1 (hyq q hq))
  inv_mem' := by
    rintro x ⟨hx, hxq⟩
    refine ⟨X.inv_mem hx, fun q hq => ?_⟩
    have hq' : x⁻¹ * q * x ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.1 (hQ (X.inv_mem hx)) q).1 hq
      simpa using this
    have e : ⁅q, x⁻¹⁆ = ⁅x⁻¹ * q * x, x⁆⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact U.inv_mem (hxq _ hq')

theorem cqSub_conj {X Q U : Subgroup G} {hQ : X ≤ Subgroup.normalizer (Q : Set G)}
    {hU : X ≤ Subgroup.normalizer (U : Set G)} {x g : G} (hx : x ∈ cqSub X Q U hQ hU) (hg : g ∈ X) :
    g * x * g⁻¹ ∈ cqSub X Q U hQ hU := by
  obtain ⟨hxX, hxq⟩ := hx
  refine ⟨X.mul_mem (X.mul_mem hg hxX) (X.inv_mem hg), fun q hq => ?_⟩
  have hq' : g⁻¹ * q * g ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.1 (hQ (X.inv_mem hg)) q).1 hq
    simpa using this
  have e : ⁅q, g * x * g⁻¹⁆ = g * ⁅g⁻¹ * q * g, x⁆ * g⁻¹ := by
    simp only [commutatorElement_def]; group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (hU hg) _).1 (hxq _ hq')

namespace EntryPlus

variable {X T V L R : Subgroup G} {m : ℕ} {hV : IsElemAbelian 2 V}
  (E : EntryPlus X T V L R m hV)

include E

theorem irr_group :
    ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) < ⁅V, L⁆ ∧
      ∀ W : Subgroup G, ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) ≤ W → W ≤ ⁅V, L⁆ →
        L ≤ Subgroup.normalizer (W : Set G) →
        W = ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) ∨ W = ⁅V, L⁆ := by
  have hI := E.case1i.1.2.2.2
  have hU : toG hV (commV (autI hV L)) = ⁅V, L⁆ := by
    rw [toG_commV hV E.hLN, Subgroup.commutator_comm]
  have hZ : toG hV (XMod.fixed ↥(autI hV L) (commV (autI hV L))) =
      ⁅V, L⁆ ⊓ Subgroup.centralizer (L : Set G) := by
    rw [toG_fixed hV E.hLN, hU]
  refine ⟨?_, fun W hZW hWU hLW => ?_⟩
  · have h := lt_of_le_of_ne ((toG_le_iff hV).2 hI.1.le)
      (fun h => hI.1.ne ((toG_inj hV).1 h))
    rwa [hZ, hU] at h
  · rw [← hZ] at hZW
    rw [← hU] at hWU
    have hWV : W ≤ V := hWU.trans (toG_le hV _)
    set W' : Subgroup (IntMod V hV) := W.comap (valHom hV) with hW'
    have hW'G : toG hV W' = W := by
      ext g
      constructor
      · intro hg
        obtain ⟨w, hw, rfl⟩ := (mem_toG hV).1 hg
        exact hw
      · intro hg
        exact (mem_toG hV).2 ⟨IntMod.mk hV ⟨g, hWV hg⟩, hg, rfl⟩
    have hinv : XMod.IsInv ↥(autI hV L) W' := by
      rw [isInv_iff hV E.hLN, hW'G]
      intro g hg w hw
      exact (Subgroup.mem_normalizer_iff.1 (hLW hg) w).1 hw
    have hfix : XMod.fixed ↥(autI hV L) (commV (autI hV L)) ≤ W' := by
      rw [← toG_le_iff hV, hW'G]
      exact hZW
    have hle : W' ≤ commV (autI hV L) := by
      rw [← toG_le_iff hV, hW'G]
      exact hWU
    rcases hI.2 W' hinv hfix hle with h | h
    · left
      rw [← hW'G, h, hZ]
    · right
      rw [← hW'G, h, hU]

end EntryPlus

end CFSG.Quasithin.C124
