module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G43Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem s16c1G43_conjSubgroup_conj_inv_mul (A : Subgroup G) (h c : G) :
    conjSubgroup (conjSubgroup A c) (c⁻¹ * h * c) = conjSubgroup (conjSubgroup A h) c := by
  rw [conjSubgroup_conjSubgroup, conjSubgroup_conjSubgroup]
  congr 1
  group

private theorem s16c1G43_BOf_conj (M V : Subgroup G) (h c : G) :
    BOf (conjSubgroup M c) (conjSubgroup V c) (c⁻¹ * h * c) =
      conjSubgroup (BOf M V h) c := by
  unfold BOf
  rw [s16c1G43_conjSubgroup_conj_inv_mul, conjSubgroup_inf]

private theorem s16c1G43_centralizer_BOf_conj (M V : Subgroup G) (h c : G) :
    centralizer ((BOf (conjSubgroup M c) (conjSubgroup V c) (c⁻¹ * h * c) : Subgroup G) :
      Set G) = conjSubgroup (centralizer ((BOf M V h : Subgroup G) : Set G)) c := by
  rw [s16c1G43_BOf_conj, E3.conjSubgroup_centralizer]

private theorem s16c1G43_primHalf_conj_mp {M V : Subgroup G} {h : G} (c : G)
    (hh : PrimHalf M V h) :
    PrimHalf (conjSubgroup M c) (conjSubgroup V c) (c⁻¹ * h * c) := by
  unfold PrimHalf at hh ⊢
  refine ⟨?_, ?_⟩
  · rw [s16c1G43_centralizer_BOf_conj, ← conjSubgroup_inf,
      s16c1G43_conjSubgroup_conj_inv_mul, E3.conjSubgroup_le_conjSubgroup_iff]
    exact hh.1
  · intro b hb hbV v hv hcomm
    rw [s16c1G43_BOf_conj] at hb
    rw [s16c1G43_conjSubgroup_conj_inv_mul] at hcomm
    have hb₀ : c * b * c⁻¹ ∈ BOf M V h := mem_conjSubgroup_iff.1 hb
    have hb₀V : c * b * c⁻¹ ∉ V := fun hmem => hbV (mem_conjSubgroup_iff.2 hmem)
    have hv₀ : c * v * c⁻¹ ∈ V := mem_conjSubgroup_iff.1 hv
    have hcomm₀ : ⁅c * v * c⁻¹, c * b * c⁻¹⁆ ∈ V ⊓ conjSubgroup V h := by
      rw [← conjugate_commutatorElement]
      exact ⟨mem_conjSubgroup_iff.1 hcomm.1, mem_conjSubgroup_iff.1 hcomm.2⟩
    have hres := hh.2 (c * b * c⁻¹) hb₀ hb₀V (c * v * c⁻¹) hv₀ hcomm₀
    rw [s16c1G43_conjSubgroup_conj_inv_mul]
    exact mem_conjSubgroup_iff.2 hres

theorem s16c1G43_primHalf_conj {M V : Subgroup G} {h : G} (c : G) :
    PrimHalf M V h ↔ PrimHalf (conjSubgroup M c) (conjSubgroup V c) (c⁻¹ * h * c) := by
  refine ⟨s16c1G43_primHalf_conj_mp c, fun hh => ?_⟩
  have hconj := s16c1G43_primHalf_conj_mp (M := conjSubgroup M c) (V := conjSubgroup V c)
    (h := c⁻¹ * h * c) c⁻¹ hh
  rw [show (c⁻¹)⁻¹ * (c⁻¹ * h * c) * c⁻¹ = h by group] at hconj
  simpa only [E3.conjSubgroup_conj_inv] using hconj

theorem s16c1G43_mQuot_le {M V : Subgroup G} {g : G} (hV64 : Nat.card ↥V = 64)
    (hG : PrimGeom M V g) :
    E3.mQuot V (conjSubgroup M g) ≤ 1 ∧ E3.mQuot (conjSubgroup V g) M ≤ 1 := by
  have hrel1 : (conjSubgroup M g).relIndex V = 2 := by
    rw [← Subgroup.inf_relIndex_left (H := V) (K := conjSubgroup M g)]
    exact hG.relIndex_U
  have hcardB : Nat.card ↥(M ⊓ conjSubgroup V g) = 32 := by
    rw [inf_comm]
    exact hG.card_B
  have hcardV : Nat.card ↥(conjSubgroup V g) = 64 := by
    rw [E3.card_conjSubgroup, hV64]
  have hrel2 : M.relIndex (conjSubgroup V g) = 2 := by
    have h := Subgroup.relIndex_mul_card (H := M) (K := conjSubgroup V g)
    rw [hcardB, hcardV] at h
    omega
  constructor
  · unfold E3.mQuot
    rw [hrel1]
    exact le_of_eq padicValNat_self
  · unfold E3.mQuot
    rw [hrel2]
    exact le_of_eq padicValNat_self

theorem s16c1G43_hyp612Sym {M V : Subgroup G} {g : G} (hV : IsElemAbelian 2 V)
    (hM : normalizer (V : Set G) = M) (hV64 : Nat.card ↥V = 64)
    (hlt : (1 : ℕ∞) < rStarMV M V) (hnotVg : ¬ conjSubgroup V g ≤ M)
    (hnotV : ¬ V ≤ conjSubgroup M g) (hG : PrimGeom M V g) (h2 : PrimHalf M V g⁻¹) :
    Hyp612Sym 1 M V g := by
  have hm := s16c1G43_mQuot_le hV64 hG
  have hin : InCalO 1 M ⊥ V g :=
    ⟨⟨hnotVg, hm.1, fun h => absurd rfl h⟩, ⟨hnotV, hm.2, fun h => absurd rfl h⟩⟩
  have h2' : PrimHalf (conjSubgroup M g) (conjSubgroup V g) g⁻¹ := by
    have h := (s16c1G43_primHalf_conj (M := M) (V := V) (h := g⁻¹) g).1 h2
    rwa [show g⁻¹ * g⁻¹ * g = g⁻¹ by group] at h
  unfold PrimHalf at h2'
  simp only [BOf_swap, conjSubgroup_conjSubgroup_inv] at h2'
  exact ⟨hV, hM, by simpa using hlt, hin, hG.half.1, hG.half.2, h2'.1,
    fun a ha haV w hw hc => h2'.2 a ha haV w hw (by rwa [inf_comm] at hc)⟩

theorem s16c1G43_mQuot_inv {M V : Subgroup G} {g : G} (hU : (UOf M V g).relIndex V = 2) :
    E3.mQuot (conjSubgroup V g⁻¹) (conjSubgroup V g⁻¹ ⊓ M) = 1 := by
  have h := E3.mQuot_conjSubgroup (conjSubgroup V g⁻¹) (conjSubgroup V g⁻¹ ⊓ M) g
  rw [E3.conjSubgroup_inv_conj, conjSubgroup_inf, E3.conjSubgroup_inv_conj] at h
  rw [← h]
  unfold E3.mQuot
  have hU' : (V ⊓ conjSubgroup M g).relIndex V = 2 := hU
  rw [hU']
  exact padicValNat_self

theorem s16c1G43_not_le_inv {M V : Subgroup G} {g : G} (h : ¬ conjSubgroup V g ≤ M) :
    ¬ V ≤ conjSubgroup M g⁻¹ := by
  intro hV
  apply h
  have hc := E3.conjSubgroup_mono_left g hV
  rwa [E3.conjSubgroup_inv_conj] at hc

theorem s16c1G43_hyp1643_inv {D : Data G} {V : Subgroup G} {g : G}
    (hU : (UOf D.M V g).relIndex V = 2) :
    Hyp1643 D ⊥ V 1 (conjSubgroup V g⁻¹ ⊓ D.M) g⁻¹ := by
  refine ⟨Or.inr ⟨rfl, rfl⟩, ?_, inf_le_left⟩
  exact ⟨inf_le_right, g⁻¹, inf_le_left, s16c1G43_mQuot_inv hU⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
