module

public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeALeech
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.TabMThreeAType
public import CFSG.YGroups.Y443.Tri.AssemblyLit

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Sporadic.MI301Three

open CFSG.Monster CFSG.Monster.GMS CFSG.Monster.Griess CFSG.Monster.Existence
  CFSG.Blueprint.NativeSporadic CFSG.HardMathSupport.Dickson.I271
  CFSG.HardMathSupport.Dickson.I271.TabMThreeA CFSG.YGroups.Y443

section Leech

variable {d₀ : B} {G : Type} [Group G] [Finite G] {a z₀ : G}

theorem isConj_c0_leech (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) {α β t : G}
    (hα : IsConj a α) (hβ : β ∈ typeSet a z₀ α .threeA)
    (ht : t ∈ Subgroup.centralizer ({α} : Set G) ⊓ Subgroup.centralizer ({β} : Set G))
    (htB : IsConj z₀ t) (L : LeechSystem t)
    (hαβ : α * β ∈ Subgroup.centralizer ({t} : Set G)) :
    IsConj TabMThreeALeech.c0 (L.φ ⟨α * β, hαβ⟩) := by
  obtain ⟨⟨hβa, hβne, hodd, -⟩, hk⟩ := hβ
  have hY : IsOddPair a t α β := IsOddPair.of_mem_inf hα hβa hβne.symm hodd ht
  have hty : LeechOddType t α β 0 := hk t ht htB
  have hyp := LeechOdd.oddPairHyp I hG htB hY L
  have hot := LeechOdd.oddType I hG htB hY L hty
  obtain ⟨g, hgr, hgs⟩ := CFSG.Sporadic.Co1.Module.Odd.exists_conj_base hyp.twoA hyp.conj
    hyp.ne hyp.four hot
  have hφ : L.φ ⟨α * β, hαβ⟩ = L.φ ⟨α, hY.1⟩ * L.φ ⟨β, hY.2.1⟩ := by
    rw [← map_mul]
    rfl
  rw [hφ]
  refine isConj_iff.2 ⟨g, ?_⟩
  rw [← hgr, ← hgs]
  unfold TabMThreeALeech.c0
  group

end Leech

section MGriess


theorem isConj_c0_of_zeta {ζ t : MGriess} (hζ3 : orderOf ζ = 3)
    (hinv : tGriess * ζ * tGriess⁻¹ = ζ⁻¹)
    (h23 : 23 ∣ Nat.card ↥(Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer ({ζ} : Set MGriess)))
    (htc : t * tGriess = tGriess * t) (htζ : t * ζ = ζ * t) (htB : IsConj xGriess t)
    (L : LeechSystem t) (hζt : ζ ∈ Subgroup.centralizer ({t} : Set MGriess)) :
    IsConj TabMThreeALeech.c0 (L.φ ⟨ζ, hζt⟩) := by
  have I := gmsInterfaces_MGriess
  have hG := gmsF1Type_MGriess_uncond
  have hex := oddExhaustive_MGriess I
  have hOT : OddTypeOrdersCF tGriess xGriess :=
    oddTypeOrdersCF_MGriess I hex monster_clauses_MGriess.1
      (natCard_cent_tGriess_of monster_clauses_MGriess.2.2)
      CFSG.Sporadic.Presentation.Th.finite_card_le CFSG.Monster.Existence.Compat.card_nativeTh
      exists_hn_two_point'
  have h1 : ¬ 23 ∣ oddTypeStab 1 := by norm_num [oddTypeStab]
  have h2 : ¬ 23 ∣ oddTypeStab 2 := by norm_num [oddTypeStab]
  obtain ⟨hnbr, hty, hαβ⟩ :=
    oddNbrType_zero_of_dvd I hG hex hOT (IsConj.refl tGriess) hζ3 hinv h23 h1 h2
  have hβ : ζ⁻¹ * tGriess ∈ typeSet tGriess xGriess tGriess .threeA := ⟨hnbr, hty⟩
  have ht : t ∈ Subgroup.centralizer ({tGriess} : Set MGriess) ⊓
      Subgroup.centralizer ({ζ⁻¹ * tGriess} : Set MGriess) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.2 htc,
      Subgroup.mem_centralizer_singleton_iff.2
        ((Commute.inv_right (show Commute t ζ from htζ)).mul_right
          (show Commute t tGriess from htc)).eq⟩
  have hmem : tGriess * (ζ⁻¹ * tGriess) ∈ Subgroup.centralizer ({t} : Set MGriess) := by
    rw [hαβ]
    exact hζt
  have h := isConj_c0_leech I hG (IsConj.refl tGriess) hβ ht htB L hmem
  have he : (⟨tGriess * (ζ⁻¹ * tGriess), hmem⟩ : Subgroup.centralizer ({t} : Set MGriess)) =
      ⟨ζ, hζt⟩ := Subtype.ext hαβ
  rwa [he] at h

end MGriess

end CFSG.Sporadic.MI301Three
