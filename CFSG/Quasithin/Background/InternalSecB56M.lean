module

public import CFSG.Quasithin.Background.B5Statement

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

theorem commV_le_commV {H K : Subgroup (MulAut V)} (h : H ≤ K) : commV H ≤ commV K :=
  Subgroup.closure_mono fun _ ⟨g, hg, v, hv⟩ => ⟨g, h hg, v, hv⟩

theorem false_of_realizesVia_of_le {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) (hUZ : U ≤ Z) {m : D.Amb} (hm : m ∈ D.sec)
    (hm' : m ∉ D.ker) : False := by
  obtain ⟨-, -, -, -, -, -, -, β, hβ, hker, -⟩ := h
  obtain ⟨u, hu⟩ := hβ (QuotientGroup.mk ⟨m, hm⟩)
  rw [(hker u).2 (hUZ u.2)] at hu
  exact hm' (Subgroup.mem_subgroupOf.1 ((QuotientGroup.eq_one_iff _).1 hu.symm))

theorem false_of_realizesVia_nat {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Nonempty ι]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : (FFModel.nat Γ).Gam →* ↥H} (h : (FFModel.nat Γ).RealizesVia H U Z π) (hUZ : U ≤ Z) :
    False := by
  obtain ⟨i⟩ := ‹Nonempty ι›
  refine false_of_realizesVia_of_le h hUZ (m := Multiplicative.ofAdd (Pi.single i (1 : K)))
    (Subgroup.mem_top _) fun hm => ?_
  have h1 : (Multiplicative.ofAdd (Pi.single i (1 : K)) : Multiplicative (ι → K)) = 1 :=
    Subgroup.mem_bot.1 hm
  have h2 := congrFun (congrArg Multiplicative.toAdd h1) i
  simp at h2

theorem false_of_symmetricNatural_five {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    (h : SymmetricNatural H U Z 5) (hUZ : U ≤ Z) : False := by
  obtain ⟨_, hR⟩ := h
  refine false_of_realizesVia_of_le hR hUZ
    (m := Multiplicative.ofAdd (Pi.single (0 : Fin 5) (1 : ZMod 2) + Pi.single 1 1))
    (G6.mem_coreMod.2 (by decide)) fun hm => ?_
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (Subgroup.mem_inf.1 hm).1
  have hk' : (G6.allOnes 5 : G6.PermMod 5) ^ k =
      Multiplicative.ofAdd (Pi.single (0 : Fin 5) (1 : ZMod 2) + Pi.single 1 1) := hk
  have hc : Multiplicative.toAdd ((G6.allOnes 5 : G6.PermMod 5) ^ k) 0 =
      Multiplicative.toAdd ((G6.allOnes 5 : G6.PermMod 5) ^ k) 2 := by
    rw [toAdd_zpow]
    rfl
  rw [hk'] at hc
  exact absurd hc (by decide)

theorem not_b56Piece_self [Finite V] {Gi : Subgroup (MulAut V)} {C : Subgroup V}
    (h : B56Piece Gi C C) : False := by
  rcases h with ⟨-, ⟨_, _, _, _, -, _, hR⟩ | hR | ⟨_, _, _, _, -, _, hR⟩⟩ |
      ⟨-, _, _, _, _, -, I, _, -, -, hsup, hR⟩ | ⟨-, -, hcard, -⟩
  · exact false_of_realizesVia_nat hR le_rfl
  · exact false_of_symmetricNatural_five hR le_rfl
  · exact false_of_realizesVia_nat hR le_rfl
  · exact false_of_realizesVia_nat (hR 0) ((le_iSup I 0).trans (le_sup_right.trans hsup.le))
  · have hpos : 0 < Nat.card ↥C := Nat.card_pos
    rw [show (2 : ℕ) ^ 4 = 16 by norm_num] at hcard
    omega

theorem commV_le_of_b56Piece {Gi : Subgroup (MulAut V)} {Wi C : Subgroup V}
    (h : B56Piece Gi Wi C) : commV Gi ≤ Wi := by
  rcases h with ⟨hW, -⟩ | ⟨hW, -⟩ | ⟨-, hle, -⟩
  · rw [hW]
    exact le_sup_left
  · rw [hW]
    exact le_sup_left
  · exact hle

end CFSG.Quasithin.InternalSec
