module

public import CFSG.LocalAnalysis.WeakClosure81.FiveFiveBase
public import CFSG.LocalAnalysis.WeakClosure81.FiveFourThree
public import CFSG.LocalAnalysis.WeakClosure81.FiveSevenPhi

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem eq_bot_or_fstar_le_of_normal {H N : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n)) (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) :
    N = ⊥ ∨ Fstar H ≤ N := by
  classical
  haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
    alternatingGroup.isSimpleGroup (by simpa [Nat.card_fin] using hn)
  haveI : IsSimpleGroup ↥(Fstar H) := e.isSimpleGroup
  obtain ⟨φ, hφinj, -, hφapp⟩ := exists_injective_conj_apply_of_fstar_alt hn e
  have hCn : ((N ⊓ Fstar H).subgroupOf (Fstar H)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff (inf_le_right : N ⊓ Fstar H ≤ Fstar H)]
    intro x g hx hg
    obtain ⟨hxN, hxF⟩ := Subgroup.mem_inf.mp hx
    exact Subgroup.mem_inf.mpr
      ⟨(Subgroup.normal_subgroupOf_iff hNH).1 hN x g hxN (fstar_le_group H hg),
        conj_mem_fstar (fstar_le_group H hg) hxF⟩
  haveI := hCn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N ⊓ Fstar H).subgroupOf (Fstar H)) with
    hCbot | hCtop
  · left
    have hNF : N ⊓ Fstar H = ⊥ := by
      have h := Subgroup.map_subgroupOf_eq_of_le (inf_le_right : N ⊓ Fstar H ≤ Fstar H)
      rw [hCbot, Subgroup.map_bot] at h
      exact h.symm
    have hconj : ∀ (x : G), x ∈ N → ∀ (f : G), f ∈ Fstar H → x * f * x⁻¹ = f := by
      intro x hxN f hf
      have hmem : f * x⁻¹ * f⁻¹ ∈ N :=
        (Subgroup.normal_subgroupOf_iff hNH).1 hN x⁻¹ f (N.inv_mem hxN)
          (fstar_le_group H hf)
      have hcN : (x * f * x⁻¹) * f⁻¹ ∈ N := by
        have heq : (x * f * x⁻¹) * f⁻¹ = x * (f * x⁻¹ * f⁻¹) := by group
        rw [heq]
        exact N.mul_mem hxN hmem
      have hcF : (x * f * x⁻¹) * f⁻¹ ∈ Fstar H :=
        (Fstar H).mul_mem (conj_mem_fstar (hNH hxN) hf) ((Fstar H).inv_mem hf)
      have hc : (x * f * x⁻¹) * f⁻¹ ∈ (⊥ : Subgroup G) := by
        rw [← hNF]
        exact Subgroup.mem_inf.mpr ⟨hcN, hcF⟩
      exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hc)
    rw [Subgroup.eq_bot_iff_forall]
    intro x hxN
    have hmemx : x ∈ H := hNH hxN
    have hφx : φ ⟨x, hmemx⟩ = 1 := by
      apply MulEquiv.ext
      intro y
      obtain ⟨f, rfl⟩ := e.surjective y
      have hfix : φ ⟨x, hmemx⟩ (e f) = e f := by
        have h1 : ((e.symm (φ ⟨x, hmemx⟩ (e f)) : ↥(Fstar H)) : G) = (f : G) := by
          rw [hφapp ⟨x, hmemx⟩ f]
          exact hconj x hxN (f : G) f.2
        have h2 : e.symm (φ ⟨x, hmemx⟩ (e f)) = f := Subtype.ext h1
        simpa using congrArg e h2
      simpa using hfix
    have hxH1 : (⟨x, hmemx⟩ : ↥H) = 1 := hφinj (by rw [hφx, map_one])
    have hval : ((⟨x, hmemx⟩ : ↥H) : G) = ((1 : ↥H) : G) := congrArg Subtype.val hxH1
    simpa using hval
  · right
    have htop : N ⊓ Fstar H = Fstar H := by
      have h := Subgroup.map_subgroupOf_eq_of_le (inf_le_right : N ⊓ Fstar H ≤ Fstar H)
      rw [hCtop, Subgroup.map_top, Subgroup.range_subtype] at h
      exact h.symm
    intro f hf
    have : f ∈ N ⊓ Fstar H := by rw [htop]; exact hf
    exact (Subgroup.mem_inf.mp this).1

theorem kerMOf_eq_bot_of_fstar_alt {H M A : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n)) (h : Sec5Hyp H M A)
    (hM : maxOver H A = {M}) : kerMOf M H = ⊥ := by
  classical
  let Y : Subgroup G := kerMOf M H
  have hYH : Y ≤ H := kerMOf_le_group M H
  have hYM : Y ≤ M := kerMOf_le_left M H
  have hYn : (Y.subgroupOf H).Normal := normal_subgroupOf_kerMOf M H
  have hYlt : Y < H := by
    refine lt_of_le_of_ne hYH ?_
    intro hYeq
    exact h.not_le (hYeq ▸ hYM)
  obtain ⟨X, hX⟩ := exists_isMinNormalOver hYlt hYn
  obtain ⟨-, hQnil⟩ := five_four_three h hM hX
  have hYsol : Group.IsSolvable ↥Y := by
    haveI : Group.IsNilpotent ↥(pCore 2 ↥Y) := pCore_isNilpotent
    haveI : Group.IsNilpotent (↥Y ⧸ pCore 2 ↥Y) := hQnil
    refine Group.isSolvable_of_ker_le_range (pCore 2 ↥Y).subtype
      (QuotientGroup.mk' (pCore 2 ↥Y))
      (le_of_eq ((QuotientGroup.ker_mk' (pCore 2 ↥Y)).trans
        (Subgroup.range_subtype (pCore 2 ↥Y)).symm))
  rcases eq_bot_or_fstar_le_of_normal hn e hYH hYn with hYbot | hFY
  · exact hYbot
  · exfalso
    haveI : Group.IsSolvable ↥Y := hYsol
    have hFsol : Group.IsSolvable ↥(Fstar H) :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hFY)
        (Subgroup.inclusion_injective hFY)
    haveI : Group.IsSolvable ↥(Fstar H) := hFsol
    have hAsol : Group.IsSolvable ↥(alternatingGroup (Fin n)) :=
      Group.isSolvable_of_isSolvable_injective (f := e.symm.toMonoidHom) e.symm.injective
    haveI : IsSimpleGroup ↥(alternatingGroup (Fin n)) :=
      alternatingGroup.isSimpleGroup (by simpa [Nat.card_fin] using hn)
    have hcommA : ∀ a b : ↥(alternatingGroup (Fin n)), a * b = b * a :=
      IsSimpleGroup.comm_iff_isSolvable.mpr hAsol
    have hcard : Nat.card (Fin n) ≤ 3 :=
      alternatingGroup.isMulCommutative_iff_card_le_three.mp
        (IsMulCommutative.of_comm hcommA)
    rw [Nat.card_fin] at hcard
    omega

theorem ne_bot_of_maxOver_eq_singleton {H M A : Subgroup G} {n : ℕ} (hn : 5 ≤ n)
    (e : ↥(Fstar H) ≃* alternatingGroup (Fin n)) (hM : maxOver H A = {M}) : A ≠ ⊥ := by
  intro hAbot
  rw [hAbot] at hM
  obtain ⟨hMmax, -, hunique⟩ := isUniqueMaxOver_iff.mp (show IsUniqueMaxOver H ⊥ M from hM)
  obtain ⟨x, hxH, hxM⟩ := SetLike.exists_of_lt hMmax.1
  have hzx : Subgroup.zpowers x = H := by
    by_contra hne
    have hlt : Subgroup.zpowers x < H :=
      lt_of_le_of_ne (Subgroup.zpowers_le.mpr hxH) hne
    obtain ⟨N, hNmax, hNge⟩ := exists_isMaxSubgroupIn hlt
    have hNM : N = M := hunique N hNmax bot_le
    exact hxM (hNM ▸ hNge (Subgroup.mem_zpowers x))
  have hcommH : ∀ a b : ↥H, a * b = b * a := by
    intro a b
    have ha : (a : G) ∈ Subgroup.zpowers x := by rw [hzx]; exact a.2
    have hb : (b : G) ∈ Subgroup.zpowers x := by rw [hzx]; exact b.2
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp ha
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hb
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact zpow_mul_comm x i j
  have hcommF : ∀ a b : ↥(Fstar H), a * b = b * a := by
    intro a b
    have h := hcommH ⟨(a : G), fstar_le_group H a.2⟩ ⟨(b : G), fstar_le_group H b.2⟩
    apply Subtype.ext
    simpa using congrArg (fun t : ↥H => (t : G)) h
  have hcommA : ∀ a b : ↥(alternatingGroup (Fin n)), a * b = b * a := by
    intro a b
    have h := hcommF (e.symm a) (e.symm b)
    have := congrArg e h
    simpa using this
  have hcard : Nat.card (Fin n) ≤ 3 :=
    alternatingGroup.isMulCommutative_iff_card_le_three.mp (IsMulCommutative.of_comm hcommA)
  rw [Nat.card_fin] at hcard
  omega

end CFSG.LocalAnalysis.WeakClosure81
