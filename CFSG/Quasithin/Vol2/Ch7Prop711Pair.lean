module

public import CFSG.Quasithin.Vol2.Ch7Prop711Mod
public import CFSG.Quasithin.Vol2.Ch7Prop711Grp
public import CFSG.Quasithin.Background.HA7Rec
public import CFSG.Quasithin.Vol2.Ch7Setup

public section

namespace CFSG.Quasithin.H13.Prop711

open CFSG.Open CFSG.Quasithin CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem isTwistedPair_of {t : G} (ht : t ∈ T) (hsum : fsuV T I = I ⊔ CFSG.conjugate I t)
    (hinf : I ⊓ CFSG.conjugate I t = ⊥) (hniso : ¬ IsXSectionIso₂ L I ⊥ (CFSG.conjugate I t) ⊥) :
    IsTwistedPair T L I :=
  ⟨t, ht, hsum.symm, hinf, hniso⟩

omit [Finite G] in
theorem concl701FF_of_isFFModule [Finite ↥(fsuV T I)] [IsMulCommutative ↥(fsuV T I)]
    (h : IsFFModule (V := ↥(fsuV T I)) (autOn (fsuL0 T L) (fsuV T I))) : Concl701FF T L I := by
  obtain ⟨A, hA, hrest⟩ := h
  exact B6.exists_isFFStarOffender ⟨A, hA.trans Subgroup.le_normalizer, hrest⟩


section Rows

variable [IsMulCommutative ↥(fsuV T I)]

theorem row711SL3Pair_of (hL0 : fsuL0 T L = L) (htw : IsTwistedPair T L I)
    (hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hLI : L ≤ Subgroup.normalizer (I : Set G)) {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ n) (e : ↥(autOn L (fsuV T I)) ≃* Matrix.SpecialLinearGroup (Fin 3) K)
    [IsMulCommutative ↥I] (hnat : BinaryNaturalSL (V := ↥I) (autOn L I) ⊤ ⊥ 3 n) :
    Row711SL3Pair T L I n := by
  refine ⟨htw, ?_⟩
  rw [hL0]
  exact binaryNaturalSL_subgroupOf (le_fsuV I T) hLV hLI hK e hnat

theorem row711Sp4Pair_of_sp4 (hL0 : fsuL0 T L = L) (htw : IsTwistedPair T L I)
    (hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hLI : L ≤ Subgroup.normalizer (I : Set G)) (hperf : Group.IsPerfect ↥(autOn L (fsuV T I)))
    {n : ℕ} {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (e : ↥(autOn L (fsuV T I)) ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSp 2 K))
    [IsMulCommutative ↥I] (hnat : BinaryNaturalSp4 (V := ↥I) (autOn L I) ⊤ ⊥ n) :
    Row711Sp4Pair T L I := by
  refine ⟨htw, Or.inl ⟨n, ?_, ?_⟩⟩
  · rcases Nat.lt_or_ge n 2 with hn | hn
    · exfalso
      interval_cases n
      · have := Finite.one_lt_card (α := K)
        rw [hK] at this
        norm_num at this
      · apply not_isPerfect_statedSp_two (K := K) (by rw [hK]; norm_num)
        exact Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective
    · exact hn
  · rw [hL0]
    exact binaryNaturalSp4_subgroupOf (le_fsuV I T) hLV hLI hK e hnat

theorem row711Sp4Pair_of_alt (hL0 : fsuL0 T L = L) (htw : IsTwistedPair T L I)
    (hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (hLI : L ≤ Subgroup.normalizer (I : Set G))
    (e : ↥(autOn L (fsuV T I)) ≃* alternatingGroup (Fin 6))
    [IsMulCommutative ↥I] (hnat : AlternatingNatural (V := ↥I) (autOn L I) ⊤ ⊥ 6) :
    Row711Sp4Pair T L I := by
  refine ⟨htw, Or.inr ?_⟩
  rw [hL0]
  exact alternatingNatural_subgroupOf (le_fsuV I T) hLV hLI e hnat

omit [Finite G] in
theorem row711S7Pair_of (hL0 : fsuL0 T L = L) (htw : IsTwistedPair T L I)
    (hV : IsElemAbelian 2 (fsuV T I)) (hLI : L ≤ Subgroup.normalizer (I : Set G))
    (hCI : I ⊓ Subgroup.centralizer (L : Set G) = ⊥) (hI1 : I ≠ ⊥)
    (hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G))
    (e : ↥(autOn L (fsuV T I)) ≃* alternatingGroup (Fin 7)) (hcard : Nat.card I = 2 ^ 4) :
    Row711S7Pair T L I := by
  refine ⟨htw, ?_⟩
  rw [hL0]
  have hIV : I ≤ fsuV T I := le_fsuV I T
  refine H.A7.a7Four_of_nontrivial ⟨e⟩ (InternalSec.autOn_inv_subgroupOf hLI) (fun u hu => ?_)
    ?_ ?_
  · apply Subtype.ext
    have h1 := hV.2 (u : G) u.2
    rw [Subgroup.coe_mul, ← sq, h1]
    rfl
  · rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hIV).toEquiv
  · obtain ⟨⟨i, hi⟩, hi1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hI1
    have hi1 : i ≠ 1 := fun h => hi1' (Subtype.ext h)
    have hiC : i ∉ Subgroup.centralizer (L : Set G) := fun h => by
      have : (i : G) ∈ I ⊓ Subgroup.centralizer (L : Set G) := ⟨hi, h⟩
      rw [hCI, Subgroup.mem_bot] at this
      exact hi1 this
    rw [Subgroup.mem_centralizer_iff] at hiC
    push Not at hiC
    obtain ⟨l, hl, hli⟩ := hiC
    refine ⟨A4.actionOn (fsuV T I) L hLV ⟨l, hl⟩, (A4.mem_autOn_iff hLV).mpr ⟨⟨l, hl⟩, rfl⟩,
      ⟨i, hIV hi⟩, hi, fun h => hli ?_⟩
    have h1 := congrArg Subtype.val h
    rw [A4.actionOn_apply_coe] at h1
    calc l * i = (l * i * l⁻¹) * l := by group
      _ = i * l := by rw [h1]

end Rows

end CFSG.Quasithin.H13.Prop711
