module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixteenKFacts
public import CFSG.Quasithin.Recognition.Stroth.Str86Frame
public import CFSG.GroupTheory.CardMapInfKer
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.Timmesfeld75.ListWCSzU3
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open
open Subgroup
open CFSG.GH74.Uniqueness.Bender
open scoped Pointwise

theorem Shape166.conj_inf_normalizer_eq_bot_of_benderType
    {X : Type} [Group X] [Finite X] {n i e : ℕ} (hB : BenderType X n i e)
    {Y : Subgroup X} (hY : IsElemAbelian 2 Y) (hcardY : Nat.card Y = 2 ^ n)
    {W : Subgroup X} (hWY : W ≤ Y) (hW : W ≠ ⊥) {x : X} (hx : conjSubgroup Y x ≠ Y) :
    conjSubgroup Y x ⊓ normalizer (W : Set X) = ⊥ := by
  haveI : IsSimpleGroup X := hB.isSimple
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := n) hcardY
  obtain ⟨S, hYS⟩ := hY2.exists_le_sylow
  obtain ⟨t, hc⟩ := hB.exists_benderCore S
  have hYroot : Y ≤ rootCenter (S : Subgroup X) :=
    hc.elemAbelian_le_rootCenter hYS fun z hz => by
      have := hY.2 z hz
      simpa [sq] using this
  have hYrootEq : Y = rootCenter (S : Subgroup X) :=
    Subgroup.eq_of_le_of_card_ge hYroot (by rw [hcardY, hc.card_center])
  have hSW : (S : Subgroup X) ≤ normalizer (W : Set X) := by
    refine le_normalizer_of_commute fun a ha b hb => ?_
    have haZ : a ∈ rootCenter (S : Subgroup X) := by
      rw [← hYrootEq]
      exact hWY ha
    exact (Subgroup.mem_centralizer_iff.mp haZ.2 b hb).symm
  have hNne : normalizer (W : Set X) ≠ ⊤ := by
    intro htop
    have hWn : W.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal W with h | h
    · exact hW h
    · have hYtop : Y = ⊤ := top_le_iff.mp (h ▸ hWY)
      have hroot_top : rootCenter (S : Subgroup X) = ⊤ := by rw [← hYrootEq]; exact hYtop
      have hSt : (S : Subgroup X) = ⊤ :=
        top_le_iff.mp (hroot_top ▸ rootCenter_le (S : Subgroup X))
      have hb : t ∈ CFSG.GH74.Uniqueness.Bender.borel (⊤ : Subgroup X) := by
        rw [CFSG.GH74.Uniqueness.Bender.borel, Subgroup.normalizer_eq_top]
        trivial
      exact hc.not_mem (hSt ▸ hb)
  have hYx2 : IsPGroup 2 (conjSubgroup Y x) := by
    apply IsPGroup.of_card (n := n)
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hcardY]
  have h1 : conjSubgroup Y x ⊓ normalizer (W : Set X) ≤
      conjSubgroup Y x ⊓ normalizer (S : Subgroup X) :=
    inf_le_inf_left _ (hc.le_borel_of_le hSW hNne)
  have h2 : conjSubgroup Y x ⊓ normalizer (S : Set X) =
      conjSubgroup Y x ⊓ (S : Subgroup X) :=
    IsPGroup.inf_normalizer_sylow hYx2 S
  let S' : Sylow 2 X := S.mapSurjective (f := (MulAut.conj x⁻¹).toMonoidHom)
    (MulAut.conj x⁻¹).surjective
  have hS'coe : (S' : Subgroup X) = conjSubgroup (S : Subgroup X) x := by
    simp [S', conjSubgroup]
  have hYxroot : conjSubgroup Y x = rootCenter (S' : Subgroup X) := by
    rw [hS'coe, conjSubgroup, conjSubgroup, hYrootEq, ← rootCenter_map]
  have hSne : S ≠ S' := by
    intro heq
    apply hx
    rw [hYxroot, ← heq, hYrootEq]
  have h3 : conjSubgroup Y x ⊓ (S : Subgroup X) = ⊥ := by
    rw [hYxroot]
    have hle : rootCenter (S' : Subgroup X) ⊓ (S : Subgroup X) ≤
        (S' : Subgroup X) ⊓ (S : Subgroup X) :=
      le_inf (inf_le_left.trans (rootCenter_le _)) inf_le_right
    have hle2 : rootCenter (S' : Subgroup X) ⊓ (S : Subgroup X) ≤ ⊥ := by
      calc rootCenter (S' : Subgroup X) ⊓ (S : Subgroup X)
          ≤ (S' : Subgroup X) ⊓ (S : Subgroup X) := hle
        _ = (S : Subgroup X) ⊓ (S' : Subgroup X) := inf_comm _ _
        _ = ⊥ := CFSG.Quasithin.Stroth.BenderType.sylowTwoTI hB S S' hSne
    exact le_bot_iff.mp hle2
  rw [eq_bot_iff] at h3 ⊢
  exact h1.trans (h2.trans_le h3)

theorem Shape166.conj_inf_normalizer_eq_bot_of_isPSUGp
    {X : Type} [Group X] [Finite X]
    {Y : Subgroup X} {n : ℕ}
    (hPSU : commutator X = ⊤ ∧ IsPSUGp (X ⧸ Subgroup.center X) 3 n ∧
      Nat.card (Subgroup.center X) ∣ 3) (hY : IsElemAbelian 2 Y)
    (hcardY : Nat.card Y = 2 ^ n) {W : Subgroup X} (hWY : W ≤ Y) (hW : W ≠ ⊥) {x : X}
    (hx : conjSubgroup Y x ≠ Y) :
    conjSubgroup Y x ⊓ normalizer (W : Set X) = ⊥ := by
  classical
  have hn : 2 ≤ n := two_le_of_isPSUGp hPSU.2.1
  let π : X →* X ⧸ Subgroup.center X := QuotientGroup.mk' (Subgroup.center X)
  have hker : π.ker = Subgroup.center X := QuotientGroup.ker_mk' _
  have hcl : StatedClassicalModel (X ⧸ Subgroup.center X) .PSU 3 2 n :=
    CFSG.Blueprint.LieModel.statedClassicalModel hPSU.2.1 (by decide)
  obtain ⟨e⟩ := CFSG.CGT.Timmesfeld75.exists_psu3_of_statedClassicalModel hn hcl
  have hB : BenderType (X ⧸ Subgroup.center X) n 3
      ((2 ^ n + 1) / Nat.gcd 3 (2 ^ n + 1)) :=
    BenderType.unitary n hn (e.trans (MulEquiv.subgroupCongr
      (show CFSG.Open.PSU3 2 n = CFSG.Theory.Comparator.PSU3Model n from rfl)))
  have hZodd : Odd (Nat.card (Subgroup.center X)) := by
    rcases Nat.prime_three.eq_one_or_self_of_dvd (Nat.card (Subgroup.center X)) hPSU.2.2 with
      h1 | h3
    · rw [h1]; decide
    · rw [h3]; decide
  have hY2 : IsPGroup 2 Y := IsPGroup.of_card (n := n) hcardY
  have hYZ : Y ⊓ Subgroup.center X = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hY2 hZodd
  have hYker : Y ⊓ π.ker = ⊥ := by rw [hker]; exact hYZ
  have hcardYbar : Nat.card (Y.map π) = 2 ^ n := by
    rw [CFSG.card_map_eq_card_of_inf_ker_eq_bot π hYker, hcardY]
  have hYbar : IsElemAbelian 2 (Y.map π) := by
    refine ⟨IsMulCommutative.of_comm ?_, ?_⟩
    · intro a b
      rcases a with ⟨a, ha⟩
      rcases b with ⟨b, hb⟩
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
      obtain ⟨b₀, hb₀, rfl⟩ := Subgroup.mem_map.mp hb
      apply Subtype.ext
      change π a₀ * π b₀ = π b₀ * π a₀
      have hcomm : a₀ * b₀ = b₀ * a₀ :=
        congrArg Subtype.val (hY.1.is_comm.comm ⟨a₀, ha₀⟩ ⟨b₀, hb₀⟩)
      rw [← map_mul, ← map_mul, hcomm]
    · intro z hz
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hz
      rw [← map_pow, hY.2 y hy, map_one]
  have hWZ : W ⊓ Subgroup.center X = ⊥ := by
    have h : W ⊓ Subgroup.center X ≤ Y ⊓ Subgroup.center X :=
      le_inf (inf_le_left.trans hWY) inf_le_right
    rw [hYZ] at h
    exact le_bot_iff.mp h
  have hWbar : W.map π ≠ ⊥ := by
    intro hbot
    apply hW
    rw [eq_bot_iff]
    intro w hw
    have hπw : π w ∈ W.map π := Subgroup.mem_map_of_mem π hw
    rw [hbot, Subgroup.mem_bot] at hπw
    have hwker : w ∈ π.ker := by rwa [MonoidHom.mem_ker]
    have hwZ : w ∈ Subgroup.center X := by rwa [hker] at hwker
    have hmem : w ∈ W ⊓ Subgroup.center X := ⟨hw, hwZ⟩
    rwa [hWZ] at hmem
  have hcomp : (MulAut.conj ((π x)⁻¹)).toMonoidHom.comp π =
      π.comp (MulAut.conj x⁻¹).toMonoidHom := by
    ext y
    simp [map_mul]
  have hconjmap : conjSubgroup (Y.map π) (π x) = (conjSubgroup Y x).map π := by
    simp only [conjSubgroup, Subgroup.map_map, hcomp]
  have hYx2 : IsPGroup 2 (conjSubgroup Y x) := by
    apply IsPGroup.of_card (n := n)
    rw [conjSubgroup, Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective, hcardY]
  have hxbar : conjSubgroup (Y.map π) (π x) ≠ Y.map π := by
    intro heq
    apply hx
    have hmap : (conjSubgroup Y x).map π = Y.map π := by
      rw [← hconjmap]; exact heq
    exact CFSG.GroupTheory.eq_of_map_eq_map_of_isPGroup_of_odd_ker π (le_of_eq hker)
      (by rw [hker]; exact hZodd) hYx2 hY2 hmap
  have hmain := Shape166.conj_inf_normalizer_eq_bot_of_benderType hB hYbar hcardYbar
    (Subgroup.map_mono hWY) hWbar hxbar
  rw [eq_bot_iff]
  intro v hv
  have hvYx : v ∈ conjSubgroup Y x := hv.1
  have hvN : v ∈ normalizer (W : Set X) := hv.2
  have hπv : π v ∈ conjSubgroup (Y.map π) (π x) ⊓
      normalizer (W.map π : Set (X ⧸ Subgroup.center X)) := by
    refine ⟨?_, ?_⟩
    · rw [hconjmap]
      exact Subgroup.mem_map_of_mem π hvYx
    · exact Subgroup.le_normalizer_map π (Subgroup.mem_map_of_mem π hvN)
  rw [hmain, Subgroup.mem_bot] at hπv
  have hvker : v ∈ π.ker := by rw [MonoidHom.mem_ker]; exact hπv
  have hvZ : v ∈ Subgroup.center X := by rwa [hker] at hvker
  have hbot : conjSubgroup Y x ⊓ Subgroup.center X = ⊥ :=
    CFSG.GroupTheory.inf_eq_bot_of_isPGroup_two_of_odd hYx2 hZodd
  have hmem : v ∈ conjSubgroup Y x ⊓ Subgroup.center X := ⟨hvYx, hvZ⟩
  rwa [hbot] at hmem

end CFSG.LocalAnalysis.WeakClosure81

end
