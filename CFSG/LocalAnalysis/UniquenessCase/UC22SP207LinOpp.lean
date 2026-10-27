module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
import CFSG.Adapters.StatedQuasisimple
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KOrdNatural.PCoreSL
import CFSG.LocalAnalysis.UniquenessCase.UC22SP207LinPoint
import CFSG.RankThree.PartOne.KFOUT3.KtyGen
import CFSG.RankThree.PartTwo.Sec4.Item462AltProofKSLThreeGLTwoQs
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.Assembly.OddCoreElimination.CentralizerContainmentKernel
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.SP207Lin

open Subgroup
open CFSG.RankThree.PartOne (pElementSubgroup)

theorem pElementSubgroup_top_eq_map {Q B : Type} [Group Q] [Finite Q] [Group B] {p : ℕ}
    (hp : p.Prime) (ψ : Q →* B) (hψ : Function.Surjective ψ) {R L : Subgroup Q}
    (hR : R ≤ ψ.ker) (hgen : ∀ x : Q, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ R ⊔ L)
    (hL : pElementSubgroup p L = L) :
    pElementSubgroup p (⊤ : Subgroup B) = L.map ψ := by
  rw [← map_top_of_surjective ψ hψ, ← PartTwo.s13_pElementSubgroup_map hp ψ ⊤]
  refine le_antisymm ?_ ?_
  · have hle : pElementSubgroup p (⊤ : Subgroup Q) ≤ R ⊔ L := by
      rw [pElementSubgroup, closure_le]
      rintro x ⟨-, k, hk⟩
      exact hgen x ⟨k, by rw [← hk, pow_orderOf_eq_one]⟩
    refine (map_mono hle).trans ?_
    rw [Subgroup.map_sup, (Subgroup.map_eq_bot_iff _).2 hR, bot_sup_eq]
  · calc L.map ψ = (pElementSubgroup p L).map ψ := by rw [hL]
      _ ≤ (pElementSubgroup p (⊤ : Subgroup Q)).map ψ :=
        map_mono (closure_mono fun x hx => ⟨mem_top x, hx.2⟩)

theorem injective_comp_subtype_of_pCore_eq_bot {Q B : Type} [Group Q] [Group B] (ψ : Q →* B)
    (L : Subgroup Q) (hker : ∀ x ∈ L, ψ x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1)
    (hcore : CFSG.pCore 2 ↥L = ⊥) : Function.Injective (ψ.comp L.subtype) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hcore]
  refine le_sSup ⟨inferInstance, fun x => ?_⟩
  obtain ⟨k, hk⟩ := hker x.1.1 x.1.2 x.2
  exact ⟨k, Subtype.ext (Subtype.ext hk)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.SP207Lin

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne (pElementSubgroup)

namespace SP207Lin

theorem isQuasisimple_specialLinear_pred {m : ℕ} (hm : m = 3 ∨ m = 4) {K : Type} [Field K]
    [Finite K] (hK : 4 ≤ Nat.card K) :
    CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin (m - 1)) K) := by
  rcases hm with rfl | rfl
  · exact CFSG.RankThree.PartTwo.Sec4.Item462AltProof.KSLThree.isQuasisimple_specialLinear_two hK
  · exact CFSG.IsQuasisimple.of_mulEquiv
      (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 K)
      (CFSG.Open.StatedAPI.isQuasisimple_statedSL_of_two_le (m := 2) le_rfl K)

theorem pElementSubgroup_eq_of_equiv {G : Type} [Group G] [Finite G] {k : ℕ} (hk : 1 ≤ k)
    {K : Type} [Field K] [Finite K] {L : Subgroup G}
    (e : ↥L ≃* Matrix.SpecialLinearGroup (Fin k) K)
    (hq : CFSG.IsQuasisimple (Matrix.SpecialLinearGroup (Fin k) K)) {p : ℕ} (hp : p.Prime)
    (hpq : ¬ p ∣ Nat.card K - 1) (hpd : p ∣ Nat.card (Matrix.SpecialLinearGroup (Fin k) K)) :
    pElementSubgroup p L = L := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p (by rwa [Nat.card_congr e.toEquiv])
  refine RankThree.PartOne.KFOUT3.pElementSubgroup_eq_of_quasisimple
    (CFSG.IsQuasisimple.of_mulEquiv e hq) z.2 (by rw [Subgroup.orderOf_coe, hz]) fun hzc => ?_
  have hcen : e z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin k) K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h := Subgroup.mem_center_iff.1 hzc (e.symm g)
    have h' := congrArg e h
    simpa using h'
  have hdvd : Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin k) K)) ∣
      Nat.card K - 1 := by
    have h := LinearFlag.card_scalars_dvd (K := K) hk
    rwa [LinearFlag.scalars_eq_center] at h
  have hord : orderOf (⟨e z, hcen⟩ : Subgroup.center (Matrix.SpecialLinearGroup (Fin k) K)) = p :=
    by rw [Subgroup.orderOf_mk, MulEquiv.orderOf_eq, hz]
  exact hpq (hord ▸ (_root_.orderOf_dvd_natCard _).trans hdvd)

end SP207Lin

theorem uc22sp207_opp_bar2 {m d n : ℕ} (hm : m = 3 ∨ m = 4) (hd : d = 1 ∨ d = m - 1)
    (hn : 2 < n) {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ n)
    {X : Type} [Group X] [Finite X] (α : SpecialLinearGroup (Fin m) K →* X)
    (hα : Function.Surjective α) (hαc : α.ker ≤ center (SpecialLinearGroup (Fin m) K))
    {Y : Subgroup X} (hY : Y.comap α = LinearFlag.stabilizer (LinearFlag.flagSpace m K d))
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    (hpY : p ∣ Nat.card Y) :
    Nonempty (↥(Opp p (⊤ : Subgroup (Bar2 Y))) ≃*
      CFSG.Open.StatedSL (m - 1) (GaloisField 2 n)) := by
  have hm3 : 3 ≤ m := by omega
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn.le
  obtain ⟨R, L₁, hRQ, hRn, hR2, hLQ, hLZ, ⟨eL⟩, hpcl⟩ :=
    uc22sp207_flagPoint_structure (K := K) hm3 hd
  obtain ⟨hdiv, hgen⟩ := hpcl hp hp2 hpq
  set Q := LinearFlag.stabilizer (LinearFlag.flagSpace m K d) with hQ
  have hmem : ∀ x : SpecialLinearGroup (Fin m) K, x ∈ Q ↔ α x ∈ Y := fun x => by
    rw [← hY]
    rfl
  let Yq : ↥Q →* ↥Y := (α.comp Q.subtype).codRestrict Y fun x => (hmem x.1).1 x.2
  have hYq : Function.Surjective Yq := fun y => by
    obtain ⟨x, hx⟩ := hα y.1
    exact ⟨⟨x, (hmem x).2 (hx ▸ y.2)⟩, Subtype.ext hx⟩
  have hLp : pElementSubgroup p L₁ = L₁ :=
    SP207Lin.pElementSubgroup_eq_of_equiv (by omega) eL
      (SP207Lin.isQuasisimple_specialLinear_pred hm hK4) hp hpq
      (hdiv (hpY.trans (Subgroup.card_dvd_of_surjective hYq)))
  let π : ↥Y →* Bar2 Y := QuotientGroup.mk' (CFSG.pCore 2 ↥Y)
  let ψ : ↥Q →* Bar2 Y := π.comp Yq
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hYq
  have hker : ∀ x : ↥Q, ψ x = 1 → ∃ k : ℕ, (x : SpecialLinearGroup (Fin m) K) ^ 2 ^ k ∈ α.ker :=
    fun x hx => by
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥Y)
      ⟨Yq x, (QuotientGroup.eq_one_iff _).1 hx⟩
    refine ⟨k, ?_⟩
    rw [MonoidHom.mem_ker, map_pow]
    exact congrArg Subtype.val (congrArg Subtype.val hk)
  have hR'2 : IsPGroup 2 ↥(R.subgroupOf Q) :=
    hR2.of_injective (subgroupOfEquivOfLe hRQ).toMonoidHom (MulEquiv.injective _)
  have hR'ker : R.subgroupOf Q ≤ ψ.ker := by
    have hN : (R.subgroupOf Q).map Yq ≤ CFSG.pCore 2 ↥Y :=
      le_sSup ⟨hRn.map Yq hYq, hR'2.map Yq⟩
    intro r hr
    exact (QuotientGroup.eq_one_iff _).2 (hN ⟨r, hr, rfl⟩)
  have hgen' : ∀ x : ↥Q, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ R.subgroupOf Q ⊔ L₁.subgroupOf Q := by
    rintro x ⟨k, hk⟩
    rw [← subgroupOf_sup hRQ hLQ, mem_subgroupOf]
    exact hgen x.1 x.2 ⟨k, congrArg Subtype.val hk⟩
  have hLp' : pElementSubgroup p (L₁.subgroupOf Q) = L₁.subgroupOf Q := by
    have h1 : (L₁.subgroupOf Q).map Q.subtype = L₁ := by
      rw [subgroupOf_map_subtype, inf_of_le_left hLQ]
    have h2 := PartTwo.s13_pElementSubgroup_map hp Q.subtype (L₁.subgroupOf Q)
    have h3 : pElementSubgroup p ((L₁.subgroupOf Q).map Q.subtype) =
        (L₁.subgroupOf Q).map Q.subtype := by
      rw [h1]
      exact hLp
    exact Subgroup.map_injective Q.subtype_injective (h2.trans h3)
  have hEq := SP207Lin.pElementSubgroup_top_eq_map hp ψ hψ hR'ker hgen' hLp'
  have hcore : CFSG.pCore 2 ↥(L₁.subgroupOf Q) = ⊥ := by
    let f : ↥(L₁.subgroupOf Q) ≃* CFSG.Open.StatedSL (m - 1) K :=
      ((subgroupOfEquivOfLe hLQ).trans eL).trans
        (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (m - 1) K)
    have h1 := CFSG.pCore_map_iso 2 f
    rw [KOrdNat.pCore_statedSL_eq_bot (K := K) 2 (m - 1)] at h1
    exact (Subgroup.map_eq_bot_iff_of_injective _ f.injective).1 h1
  have hinj : Function.Injective (ψ.comp (L₁.subgroupOf Q).subtype) :=
    SP207Lin.injective_comp_subtype_of_pCore_eq_bot ψ (L₁.subgroupOf Q)
      (fun x hx hψx => by
        obtain ⟨k, hk⟩ := hker x hψx
        have h : (x : SpecialLinearGroup (Fin m) K) ^ 2 ^ k ∈
            L₁ ⊓ center (SpecialLinearGroup (Fin m) K) :=
          ⟨pow_mem (mem_subgroupOf.1 hx) _, hαc hk⟩
        rw [hLZ, Subgroup.mem_bot] at h
        exact ⟨k, Subtype.ext h⟩) hcore
  have hrange : (ψ.comp (L₁.subgroupOf Q).subtype).range = (L₁.subgroupOf Q).map ψ := by
    rw [MonoidHom.range_comp, range_subtype]
  have hop : Opp p (⊤ : Subgroup (Bar2 Y)) = (L₁.subgroupOf Q).map ψ := hEq
  let e1 : ↥(L₁.subgroupOf Q) ≃* ↥((L₁.subgroupOf Q).map ψ) :=
    (MonoidHom.ofInjective hinj).trans (MulEquiv.subgroupCongr hrange)
  let eF := CFSG.ClassicalModels.specialLinearFieldEquiv
    (CFSG.ClassicalModels.finiteFieldEquivGaloisField K 2 n (by omega) hK) (Fin (m - 1))
  let eS := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL (m - 1) (GaloisField 2 n)
  exact ⟨(MulEquiv.subgroupCongr hop).trans
    (e1.symm.trans (((subgroupOfEquivOfLe hLQ).trans eL).trans (eF.trans eS)))⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
