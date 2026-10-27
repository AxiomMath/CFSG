module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Fin
import CFSG.Quasithin.H13.GoldschmidtC137SQL32
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

private theorem c8_card_of_isE64L3 (X : Type) [Group X] (h : IsE64L3 X) :
    Nat.card X = 10752 := by
  obtain ⟨N, hN, hNcard, hL3⟩ := h
  haveI : N.Normal := hN
  have hN' : Nat.card ↥N = 2 ^ 6 := by
    obtain ⟨e⟩ := hNcard
    rw [Nat.card_congr e.toEquiv, Nat.card_congr Multiplicative.toAdd, Nat.card_fun,
      Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hq : Nat.card (X ⧸ N) = 168 :=
    (CFSG.Quasithin.H13.U3.GC137.SQ.simple_card_of_lieModel_psl_three_two hL3).2
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup N, hq, hN']
  norm_num

private theorem c8_card_of_isSpn_six (X : Type) [Group X] (h : IsSpn X 6 1) :
    Nat.card X = 1451520 := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := h
  letI : Field K := hKf
  letI : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hK
  have hidx : (6 / 2 : ℕ) = 3 := by norm_num
  rw [Nat.card_congr e.toEquiv, hidx,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hK2]
  decide

private noncomputable def c8_barHom (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {M : Subgroup G} (hM : M ≤ stabTil V₀ V) : ↥M →* MulAut (Vtil V₀ V hV) :=
  (actTil V₀ V hV).comp (Subgroup.inclusion hM)

private theorem c8_range_barHom (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {M : Subgroup G} (hM : M ≤ stabTil V₀ V) :
    (c8_barHom V₀ V hV hM).range = barSub V₀ V hV M := by
  unfold c8_barHom barSub
  rw [MonoidHom.range_comp, Subgroup.inclusion_range]

private theorem c8_barHom_fix_iff (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    {M : Subgroup G} (hM : M ≤ stabTil V₀ V) (y : ↥M) (x : IntMod V hV) :
    c8_barHom V₀ V hV hM y (mkTil V₀ V hV x) = mkTil V₀ V hV x ↔
      (y : G) * x.val * (y : G)⁻¹ * x.val⁻¹ ∈ V₀ := by
  show actTil V₀ V hV (Subgroup.inclusion hM y) (mkTil V₀ V hV x) = mkTil V₀ V hV x ↔ _
  rw [actTil_mk, mkTil_eq_iff, actStab_apply_val]
  exact Iff.rfl

theorem c8_tle_of_bot (D : Data G) (h1217 : R1217 D) (hSpA : RSp6SmallMod)
    (hSpC : RSp6SpinCent) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (h8 : Case167_8 D V₀ V hV L) (hV₀ : V₀ = ⊥)
    {v₀ : IntMod V hV} {T₀ K T' : Subgroup G} (hU : C8SetUp D V₀ V L hV v₀ T₀ K T') :
    T' ≤ K := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  subst V₀
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil ⊥ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  let f : ↥D.M →* MulAut (Vtil ⊥ V hV) := c8_barHom (V₀ := ⊥) (V := V) hV hMs
  set P₀ : Subgroup (MulAut (Vtil ⊥ V hV)) :=
    ptCent (Mbar D.M ⊥ V hV) (mkTil ⊥ V hV v₀) with hP₀def
  have hf_range : f.range = Mbar D.M ⊥ V hV := c8_range_barHom (V₀ := ⊥) (V := V) hV hMs
  have hf_fix : ∀ (y : ↥D.M) (x : IntMod V hV),
      f y (mkTil ⊥ V hV x) = mkTil ⊥ V hV x ↔
        (y : G) * x.val * (y : G)⁻¹ * x.val⁻¹ ∈ (⊥ : Subgroup G) :=
    fun y x => c8_barHom_fix_iff (V₀ := ⊥) (V := V) hV hMs y x
  have hf_mem : ∀ y : ↥D.M, f y ∈ Mbar D.M ⊥ V hV := by
    intro y
    rw [← hf_range]
    exact MonoidHom.mem_range.2 ⟨y, rfl⟩
  have hP₀mem : ∀ φ : MulAut (Vtil ⊥ V hV),
      φ ∈ P₀ ↔ φ ∈ Mbar D.M ⊥ V hV ∧ φ (mkTil ⊥ V hV v₀) = mkTil ⊥ V hV v₀ := by
    intro φ
    rw [hP₀def]
    change φ ∈ Mbar D.M ⊥ V hV ⊓
        MulAction.stabilizer (MulAut (Vtil ⊥ V hV)) (mkTil ⊥ V hV v₀) ↔
      φ ∈ Mbar D.M ⊥ V hV ∧ φ (mkTil ⊥ V hV v₀) = mkTil ⊥ V hV v₀
    rw [Subgroup.mem_inf, MulAction.mem_stabilizer_iff, MulAut.smul_def]
  have hcardP : Nat.card ↥P₀ = 10752 := c8_card_of_isE64L3 ↥P₀ hU.e64
  have hcardM : Nat.card ↥(Mbar D.M ⊥ V hV) = 1451520 := by
    rw [c8_mbar_eq_lbar D h1217 hSpA hSpC hS h8]
    exact c8_card_of_isSpn_six ↥(lBar ⊥ V hV L) h8.1
  have hP₀le : P₀ ≤ Mbar D.M ⊥ V hV := by
    rw [hP₀def]
    exact inf_le_left
  have i1 : P₀.relIndex (Mbar D.M ⊥ V hV) = 135 := by
    have hrel := Subgroup.relIndex_mul_card (H := P₀) (K := Mbar D.M ⊥ V hV)
    rw [inf_eq_left.2 hP₀le, hcardP, hcardM] at hrel
    omega
  have e1 : (D.M ⊓ centralizer ({v₀.val} : Set G)).subgroupOf D.M = P₀.comap f := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_inf,
      and_iff_right x.2, hP₀mem]
    simp only [hf_mem x, true_and]
    rw [hf_fix x v₀, Subgroup.mem_bot, Subgroup.mem_centralizer_singleton_iff]
    have hcomm : (x : G) * v₀.val * (x : G)⁻¹ * v₀.val⁻¹ = 1 ↔
        (x : G) * v₀.val = v₀.val * (x : G) := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul]
    exact hcomm.symm
  have i2 : (D.M ⊓ centralizer ({v₀.val} : Set G)).relIndex D.M = 135 := by
    show ((D.M ⊓ centralizer ({v₀.val} : Set G)).subgroupOf D.M).index = 135
    rw [e1, Subgroup.index_comap, hf_range]
    exact i1
  have s1 : IsSylowIn 2 T₀ D.M := by
    refine ⟨hU.sylow.le.trans inf_le_left, hU.sylow.isPGroup, ?_⟩
    intro h2
    have hrel := Subgroup.relIndex_mul_relIndex (H := T₀)
      (K := D.M ⊓ centralizer ({v₀.val} : Set G)) (L := D.M) hU.sylow.le inf_le_left
    rw [i2] at hrel
    rw [← hrel] at h2
    rcases (Nat.Prime.dvd_mul Nat.prime_two).1 h2 with h2' | h2'
    · exact hU.sylow.not_dvd_relIndex h2'
    · exact absurd h2' (by decide)
  have hTK : T₀ ≤ D.M ⊓ K := le_inf (hU.sylow.le.trans inf_le_left) hU.mem.1
  obtain ⟨S, hS', hle⟩ := exists_isSylowIn_ge 2 hTK hU.sylow.isPGroup
  have hcard_TS : Nat.card ↥S = Nat.card ↥(T' ⊓ K) := by
    rw [hS'.card_eq, hU.sylowK.card_eq]
  have hcard_T0S : Nat.card ↥T₀ ≤ Nat.card ↥S := Subgroup.card_le_of_le hle
  have hcard_T0T' : Nat.card ↥T₀ = Nat.card ↥T' := by
    have hSylT' : IsSylowIn 2 T' D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 hU.sylowM
    rw [s1.card_eq, hSylT'.card_eq]
  have hcard_le : Nat.card ↥T' ≤ Nat.card ↥(T' ⊓ K) := by
    calc Nat.card ↥T' = Nat.card ↥T₀ := hcard_T0T'.symm
      _ ≤ Nat.card ↥S := hcard_T0S
      _ = Nat.card ↥(T' ⊓ K) := hcard_TS
  exact inf_eq_left.1 (Subgroup.eq_of_le_of_card_ge inf_le_left hcard_le)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
