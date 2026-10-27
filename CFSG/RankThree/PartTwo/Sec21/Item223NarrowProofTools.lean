module

public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofU4
import CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem55Even
public import CFSG.RankThree.PartTwo.Census.Classical.Bridges
public import CFSG.RankThree.PartTwo.Sec21.Commute33Odd
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44PartTwo

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item223NarrowProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSU localRank)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)
open scoped commutatorElement Pointwise

variable {Y : Type} [Group Y] [Finite Y]

omit [Finite Y] in
theorem le_of_forall_commutator_mem
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hYp : Group.IsPerfect Y) {T : Subgroup Y} [T.Normal] {m : ℕ} (hm : 2 ≤ m)
    (eY : Y ⧸ T ≃* projSU 4 2 m) {N : Subgroup Y} [N.Normal] (hNT : N ≤ T)
    (h : ∀ t ∈ T, ∀ y : Y, ⁅t, y⁆ ∈ N) : T ≤ N := by
  set π := QuotientGroup.mk' N with hπ
  set Tb : Subgroup (Y ⧸ N) := T.map π with hTbdef
  have : Tb.Normal := Subgroup.Normal.map inferInstance π (QuotientGroup.mk'_surjective N)
  have hYbp : Group.IsPerfect (Y ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := π) (QuotientGroup.mk'_surjective N)
  have : Group.IsPerfect (Y ⧸ N) := hYbp
  let e₁ : (Y ⧸ N) ⧸ Tb ≃* Y ⧸ T := QuotientGroup.quotientQuotientEquivQuotient N T hNT
  have : IsSimpleGroup (projSU 4 2 m) := Sec21.isSimpleGroup_projSU le_rfl (by omega)
  have : IsSimpleGroup ((Y ⧸ N) ⧸ Tb) := (e₁.trans eY).isSimpleGroup
  have hTZ : Tb ≤ Subgroup.center (Y ⧸ N) := by
    rintro _ ⟨t, ht, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro yb
    obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N yb
    have h1 : π ⁅t, y⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr (h t ht y)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hZT : Subgroup.center (Y ⧸ N) ≤ Tb :=
    Sec4.Census.le_of_isSolvable_of_normal inferInstance
      (Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a))
  have hZeq : Subgroup.center (Y ⧸ N) = Tb := le_antisymm hZT hTZ
  have hZ := Item223PrintProof.center_eq_bot_of_quotient_projSU_four hGA hYbp hm
    ((QuotientGroup.quotientMulEquivOfEq hZeq).trans (e₁.trans eY))
  have hTb : Tb = ⊥ := hZeq ▸ hZ
  rwa [hTbdef, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hTb

theorem odd_card_of_centralizes_sylow
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hYp : Group.IsPerfect Y) {T : Subgroup Y} [T.Normal] (hTs : Group.IsSolvable T) {m : ℕ}
    (hm : 2 ≤ m) (eY : Y ⧸ T ≃* projSU 4 2 m) {z : Y} (hzT : z ∉ T) (S : Sylow 2 T)
    (hzS : ∀ s ∈ (S : Subgroup T).map T.subtype, z * s = s * z) : Odd (Nat.card T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := inSubgroup (pPrimeCore 2) T with hOdef
  set P := Commute33Steps.oddTwoCore T with hPdef
  have : Group.IsPerfect Y := hYp
  have : IsSimpleGroup (projSU 4 2 m) := Sec21.isSimpleGroup_projSU le_rfl (by omega)
  have : IsSimpleGroup (Y ⧸ T) := eY.isSimpleGroup
  have hNT : Subgroup.normalizer (T : Set Y) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hNO : ∀ y : Y, y ∈ Subgroup.normalizer (O : Set Y) := fun y =>
    Commute33Steps.normalizer_le_normalizer_oddCore T (hNT ▸ Subgroup.mem_top y)
  have hOn : O.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun y _ => hNO y)
  have hPn : P.Normal :=
    Subgroup.normalizer_eq_top_iff.mp (eq_top_iff.mpr fun y _ =>
      Commute33Steps.normalizer_le_normalizer_oddTwoCore T (hNT ▸ Subgroup.mem_top y))
  have hOT : O ≤ T := Subgroup.map_subtype_le _
  have hset : ((O ⊔ (S : Subgroup T).map T.subtype : Subgroup Y) : Set Y) =
      (O : Set Y) * (((S : Subgroup T).map T.subtype : Subgroup Y) : Set Y) :=
    Subgroup.coe_mul_of_right_le_normalizer_left O _ fun s _ => hNO s
  have hzP : ∀ p ∈ P, ⁅p, z⁆ ∈ O := by
    intro p hp
    have hpOS : p ∈ ((O ⊔ (S : Subgroup T).map T.subtype : Subgroup Y) : Set Y) :=
      Commute33Steps.oddTwoCore_le_sup S hp
    rw [hset] at hpOS
    obtain ⟨o, ho, s, hs, rfl⟩ := hpOS
    have hsz : s * z = z * s := (hzS s hs).symm
    have e : ⁅o * s, z⁆ = o * (z * o⁻¹ * z⁻¹) := by
      rw [commutatorElement_def]
      calc o * s * z * (o * s)⁻¹ * z⁻¹ = o * (s * z) * s⁻¹ * o⁻¹ * z⁻¹ := by group
        _ = o * (z * s) * s⁻¹ * o⁻¹ * z⁻¹ := by rw [hsz]
        _ = o * (z * o⁻¹ * z⁻¹) := by group
    rw [e]
    exact O.mul_mem ho ((Subgroup.mem_normalizer_iff.mp (hNO z) _).mp (O.inv_mem ho))
  set C : Subgroup Y := (Subgroup.centralizer
    ((P.map (QuotientGroup.mk' O) : Subgroup (Y ⧸ O)) : Set (Y ⧸ O))).comap
      (QuotientGroup.mk' O) with hCdef
  have hmemC : ∀ y : Y, y ∈ C ↔ ∀ p ∈ P, ⁅p, y⁆ ∈ O := by
    intro y
    rw [Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    constructor
    · intro hy p hp
      have h1 := hy _ ⟨p, hp, rfl⟩
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm]
      exact h1
    · rintro hy _ ⟨p, hp, rfl⟩
      have h1 := (QuotientGroup.eq_one_iff _).mpr (hy p hp)
      rw [← QuotientGroup.mk'_apply, map_commutatorElement,
        commutatorElement_eq_one_iff_mul_comm] at h1
      exact h1
  have hCn : C.Normal := by
    have : (P.map (QuotientGroup.mk' O)).Normal :=
      Subgroup.Normal.map hPn _ (QuotientGroup.mk'_surjective O)
    exact Subgroup.Normal.comap Subgroup.normal_centralizer _
  have hCtop : C = ⊤ := by
    refine Sec4.Census.eq_top_of_not_le hTs fun hCT => hzT (hCT ?_)
    exact (hmemC z).mpr hzP
  have hPY : ∀ p ∈ P, ∀ y : Y, ⁅p, y⁆ ∈ O := fun p hp y =>
    (hmemC y).mp (hCtop ▸ Subgroup.mem_top y) p hp
  have hTP : T ≤ P := fun x hx =>
    Commute33Steps.mem_oddTwoCore_of_commutator_mem hTs hx fun y hy => by
      rw [← commutatorElement_inv]
      exact O.inv_mem (hPY y hy x)
  have hTO : T ≤ O := le_of_forall_commutator_mem hGA hYp hm eY hOT fun t ht y =>
    hPY t (hTP ht) y
  have hTeq : O = T := le_antisymm hOT hTO
  rw [← hTeq]
  exact Commute33Steps.odd_card_inSubgroup_pPrimeCore T

theorem four_le_pRank_projSU {m : ℕ} (hm : 2 ≤ m) [Finite (projSU 4 2 m)] :
    4 ≤ CFSG.Open.pRank 2 (⊤ : Subgroup (projSU 4 2 m)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e : StatedProj (StatedSU 4 (2 ^ m) (GaloisField 2 (2 * m))) ≃* projSU 4 2 m :=
    (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage _).trans
      (MulEquiv.subgroupCongr (CFSG.RankThree.PartTwo.Census.projImage_statedSU 4 2 m))
  have : Finite (StatedProj (StatedSU 4 (2 ^ m) (GaloisField 2 (2 * m)))) :=
    Finite.of_equiv _ e.symm.toEquiv
  have hK : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by
    rw [GaloisField.card 2 (2 * m) (by omega), ← pow_mul, mul_comm]
  have h := CFSG.GH74.GLS.Stage1.Thm3.Sec5.Lem55.two_mul_le_pRank_psu_even hK
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv Nat.one_lt_two e] at h
  omega

theorem eq_bot_of_isPGroup_of_le {p : ℕ} [Fact p.Prime] {Q T : Subgroup Y} (hQ : IsPGroup p Q)
    (hQT : Q ≤ T) (hp : ¬ p ∣ Nat.card T) : Q = ⊥ := by
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  rcases Nat.eq_zero_or_pos k with rfl | hk0
  · rw [pow_zero] at hk
    exact Subgroup.eq_bot_of_card_eq _ hk
  · exact absurd ((dvd_pow_self p hk0.ne').trans (hk ▸ Subgroup.card_dvd_of_le hQT)) hp

theorem eq_bot_of_odd
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hloc : ∀ s : ℕ, s.Prime → 3 < s → localRank s Y < 3) (hYp : Group.IsPerfect Y)
    {T : Subgroup Y} [T.Normal] (hTs : Group.IsSolvable T) (hT3 : ¬ 3 ∣ Nat.card T) {m : ℕ}
    (hm : 2 ≤ m) (eY : Y ⧸ T ≃* projSU 4 2 m) (hodd : Odd (Nat.card T)) : T = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Group.IsPerfect Y := hYp
  have : IsSimpleGroup (projSU 4 2 m) := Sec21.isSimpleGroup_projSU le_rfl (by omega)
  have : IsSimpleGroup (Y ⧸ T) := eY.isSimpleGroup
  have : Finite (projSU 4 2 m) := Finite.of_equiv _ eY.toEquiv
  have hT2 : ¬ 2 ∣ Nat.card T := fun h =>
    (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h)
  have hTtop : T ≠ ⊤ := fun h => by
    have : Nontrivial (Y ⧸ T) := IsSimpleGroup.toNontrivial
    exact (QuotientGroup.nontrivial_iff.mp this) h
  by_cases hq : IsQuasisimple Y
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (inferInstance : T.Normal) with h | h
    · exact absurd h hTtop
    · refine le_bot_iff.mp (le_of_forall_commutator_mem hGA hYp hm eY bot_le fun t ht y => ?_)
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact (Subgroup.mem_center_iff.mp (h ht) y).symm
  · exfalso
    obtain ⟨p, hp, hpS⟩ := Sec4.Census.exists_centralizer_pCore_le hTs hq
    have : Fact p.Prime := ⟨hp⟩
    have hPT : pCore p Y ≤ T := Sec4.Census.pCore_le p
    have hPne : pCore p Y ≠ ⊥ := by
      intro h
      apply hTtop
      refine top_le_iff.mp (le_trans (fun g _ => ?_) hpS)
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have hx' : x ∈ (⊥ : Subgroup Y) := h ▸ hx
      rw [Subgroup.mem_bot] at hx'
      rw [hx', one_mul, mul_one]
    have hp3 : 3 < p := by
      have hp2 : p ≠ 2 := by
        rintro rfl
        exact hPne (eq_bot_of_isPGroup_of_le pCore_isPGroup hPT hT2)
      have hp3 : p ≠ 3 := by
        rintro rfl
        exact hPne (eq_bot_of_isPGroup_of_le pCore_isPGroup hPT hT3)
      have := hp.two_le
      omega
    obtain ⟨D, hD⟩ := Sec4.Census.exists_criticalAt (by omega : p ≠ 2) hPne
    have hCD : Subgroup.centralizer (D : Set Y) ≤ T := hD.centralizer_le hTs hpS
    have hCDodd : Odd (Nat.card (Subgroup.centralizer (D : Set Y))) :=
      Odd.of_dvd_nat hodd (Subgroup.card_dvd_of_le hCD)
    have h3 := Sec4.Census.twoRank_le_three hloc hp3 hD hCDodd
    have e₁ := CFSG.SectionRank.pRank_quotient_eq (p := 2) T hT2
    have e₂ := CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 2) Nat.one_lt_two eY
    have h4 := four_le_pRank_projSU hm
    omega

theorem eq_bot_of_centralizes_sylow
    (hGA : CFSG.ComponentClassification.TBLit.GriessMultipliersAllModels)
    (hloc : ∀ s : ℕ, s.Prime → 3 < s → localRank s Y < 3) (hYp : Group.IsPerfect Y)
    {T : Subgroup Y} [T.Normal] (hTs : Group.IsSolvable T) (hT3 : ¬ 3 ∣ Nat.card T) {m : ℕ}
    (hm : 2 ≤ m) (eY : Y ⧸ T ≃* projSU 4 2 m) {z : Y} (hzT : z ∉ T) (S : Sylow 2 T)
    (hzS : ∀ s ∈ (S : Subgroup T).map T.subtype, z * s = s * z) : T = ⊥ :=
  eq_bot_of_odd hGA hloc hYp hTs hT3 hm eY
    (odd_card_of_centralizes_sylow hGA hYp hTs hm eY hzT S hzS)

end CFSG.RankThree.PartTwo.Sec21.Item223NarrowProof
