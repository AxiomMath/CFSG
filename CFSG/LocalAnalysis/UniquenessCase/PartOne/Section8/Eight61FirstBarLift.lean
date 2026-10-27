module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.BarOutInner
public import CFSG.GroupTheory.FixedPointQuotientCard
import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma43One
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.LocalAnalysis.UniquenessCase.UC22

private lemma autFixedSubgroup_zpow_apply {J : Type*} [Group J] (α : MulAut J) {j : J}
    (hj : j ∈ CFSG.autFixedSubgroup α) (i : ℤ) : (α ^ i) j = j := by
  have h : j ∈ MulAction.fixedBy J α := by
    rw [MulAction.mem_fixedBy]
    exact CFSG.mem_autFixedSubgroup.mp hj
  have h' := MulAction.mem_fixedBy_zpow h i
  rw [MulAction.mem_fixedBy] at h'
  simpa [MulAut.smul_def] using h'

theorem pRank_fixed_bar_le_pRank_centralizer {G : Type} [Group G] [Finite G]
    {L : Subgroup G} {x : G} (hx : x ∈ Subgroup.normalizer (L : Set G))
    (hx3 : IsPGroup 3 (Subgroup.zpowers x)) :
    CFSG.Open.pRank 3 (CFSG.autFixedSubgroup (barConjAut (L := L) x)) ≤
      CFSG.Open.pRank 3 (Subgroup.centralizer (Subgroup.zpowers x : Set G) ⊓ L) := by
  classical
  let N : Subgroup ↥L := CFSG.pCore 2 ↥L
  let π : ↥L →* Bar2 L := QuotientGroup.mk' N
  let A : Subgroup G := Subgroup.zpowers x
  let hz : A ≤ Subgroup.normalizer (L : Set G) := Subgroup.zpowers_le.mpr hx
  let incl : A →* Subgroup.normalizer (L : Set G) := Subgroup.inclusion hz
  let ψ : A →* MulAut ↥L := (Subgroup.normalizerMonoidHom L).comp incl
  let Φ : A →* MulAut (Bar2 L) := (barAction L).comp incl
  let gx : A := ⟨x, Subgroup.mem_zpowers x⟩
  have hincl : incl gx = (⟨x, hx⟩ : Subgroup.normalizer (L : Set G)) := Subtype.ext rfl
  have hΦgx : Φ gx = barConjAut (L := L) x := by
    change barAction L (incl gx) = barConjAut (L := L) x
    rw [hincl, barConjAut_of_mem hx]
  obtain ⟨E, hEfix, hEea, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (CFSG.autFixedSubgroup (barConjAut (L := L) x))
  let H : Subgroup ↥L := E.comap π
  have hHinv : ∀ a : A, ∀ h ∈ H, ψ a h ∈ H := by
    intro a h hh
    have hhE : π h ∈ E := hh
    show π (ψ a h) ∈ E
    have hπ : π (ψ a h) = Φ a (π h) := by
      simp only [π, ψ, Φ, MonoidHom.comp_apply]
      exact (barAction_mk L (incl a) h).symm
    rw [hπ]
    have hΦeq : Φ a (π h) = π h := by
      obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      have hai : gx ^ i = a := Subtype.ext (by simpa using hi)
      rw [← hai, map_zpow, hΦgx]
      exact autFixedSubgroup_zpow_apply (barConjAut (L := L) x) (hEfix hhE) i
    rw [hΦeq]
    exact hhE
  obtain ⟨S, hSH, hScard, hSinv⟩ :=
    CFSG.HardMathSupport.Solomon.LocalBalance.exists_fixed_sylow_of_action
      (M := ↥L) (p := 3) (A := A) Nat.prime_three hx3 ψ hHinv
  have hcardH : Nat.card H = Nat.card N * Nat.card E := by
    have h := QuotientGroup.card_preimage_mk N (E : Set (Bar2 L))
    exact h
  have hNnot3 : ¬ 3 ∣ Nat.card N := by
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    rw [hm]
    intro hd
    have h32 : (3 : ℕ) ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd
    norm_num at h32
  have hfac : (Nat.card H).factorization 3 =
      CFSG.Open.pRank 3 (CFSG.autFixedSubgroup (barConjAut (L := L) x)) := by
    rw [hcardH, hEcard,
      Nat.factorization_mul (Nat.card_pos.ne') (pow_ne_zero _ (by norm_num : (3 : ℕ) ≠ 0)),
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hNnot3,
      Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same, zero_add]
  have hScard' : Nat.card S =
      3 ^ CFSG.Open.pRank 3 (CFSG.autFixedSubgroup (barConjAut (L := L) x)) := by
    rw [hScard, hfac]
  have hS3 : IsPGroup 3 S := IsPGroup.of_card hScard'
  have hdisjSN : Disjoint S N :=
    IsPGroup.disjoint_of_coprime hS3 (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) (by norm_num)
  have hπS_inj : Function.Injective (π.comp S.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro s hs
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hs
    have h1 : (s : ↥L) ∈ S ⊓ N := ⟨s.2, hs⟩
    rw [hdisjSN.eq_bot, Subgroup.mem_bot] at h1
    exact Subtype.ext h1
  have hScent : ∀ s ∈ S, (s : G) ∈ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    intro s hs
    have hsψS : ψ gx s ∈ S := hSinv gx s hs
    have hπeq : π (ψ gx s) = π s := by
      have hπs : π s ∈ E := hSH hs
      have h1 : π (ψ gx s) = Φ gx (π s) := by
        simp only [π, ψ, Φ, MonoidHom.comp_apply]
        exact (barAction_mk L (incl gx) s).symm
      rw [h1, hΦgx]
      exact CFSG.mem_autFixedSubgroup.mp (hEfix hπs)
    have hmemN : (ψ gx s)⁻¹ * s ∈ N :=
      (QuotientGroup.eq_one_iff ((ψ gx s)⁻¹ * s)).mp (by
        show π ((ψ gx s)⁻¹ * s) = 1
        rw [map_mul, map_inv, hπeq, inv_mul_cancel])
    have hmemS : (ψ gx s)⁻¹ * s ∈ S := S.mul_mem (S.inv_mem hsψS) hs
    have hsfix : ψ gx s = s := by
      have hbot : (ψ gx s)⁻¹ * s ∈ (⊥ : Subgroup ↥L) := by
        rw [← hdisjSN.eq_bot]
        exact ⟨hmemS, hmemN⟩
      have h1 : (ψ gx s)⁻¹ * s = 1 := Subgroup.mem_bot.mp hbot
      exact inv_mul_eq_one.mp h1
    have hcoe : (ψ gx s : G) = x * (s : G) * x⁻¹ := rfl
    have hsx : x * (s : G) = (s : G) * x := by
      have h : x * (s : G) * x⁻¹ = (s : G) := by
        rw [← hcoe, hsfix]
      have := congrArg (fun z : G => z * x) h
      simpa [mul_assoc] using this
    have hcommgx : Commute (s : G) x := hsx.symm
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← hi]
    exact (hcommgx.zpow_right i).symm
  have hcommE : IsMulCommutative E := hEea.1
  have hcomm : ∀ a b : S, (π.comp S.subtype) a * (π.comp S.subtype) b =
      (π.comp S.subtype) b * (π.comp S.subtype) a := by
    intro a b
    have ha : (π.comp S.subtype) a ∈ E := hSH a.2
    have hb : (π.comp S.subtype) b ∈ E := hSH b.2
    exact congrArg Subtype.val (mul_comm' (⟨_, ha⟩ : E) ⟨_, hb⟩)
  have hpow : ∀ a : S, (π.comp S.subtype) a ^ 3 = 1 := by
    intro a
    exact hEea.2 _ (hSH a.2)
  obtain ⟨hScomm, hS3pow⟩ :=
    CFSG.SectionRank.comm_pow_of_injective (p := 3) hπS_inj hcomm hpow
  have hrange : (L.subtype.comp S.subtype).range = S.map L.subtype := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  refine CFSG.SectionRank.le_pRank_of_injective (p := 3) (by norm_num) hScomm hS3pow
    hScard' (L.subtype.comp S.subtype) ?_ ?_
  · exact Subtype.val_injective.comp Subtype.val_injective
  · rw [hrange]
    intro g hg
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hg
    exact ⟨hScent s hs, s.2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
