module

public import CFSG.RankThree.GF2n.Tim77.Defs
public import CFSG.RankThree.GF2n.Tim77.InvolAut
public import CFSG.RankThree.GF2n.Tim77TI
public import CFSG.RankThree.GF2n.Tim77Prop24Conj
public import CFSG.CGT.Timmesfeld75.WCBasic
public import CFSG.CGT.Timmesfeld75.Sec3Thirteen
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap
public import CFSG.LocalAnalysis.RankThreeUC.Notation
public import CFSG.RankThree.GF2n.Stroth80.Sec5NatStmt
public import CFSG.RankThree.GF2n.Stroth80.Sec78NormZ0
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsE
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly1015
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssembly69
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailAssemblyFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBarFrattini
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailStmts
public import CFSG.RankThree.GF2n.Stroth80.Tim81Stroth.Defs

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec415a_mem_conj_mono {K A : Subgroup G} (hKA : K ≤ A) (g : G) {x : G}
    (hx : x ∈ conjSubgroup g K) : x ∈ conjSubgroup g A := by
  rw [mem_conjSubgroup] at hx ⊢
  exact hKA hx

theorem sec415a_conj_le {K N : Subgroup G} [N.Normal] (hK : K ≤ N) (g : G) :
    conjSubgroup g K ≤ N := by
  intro x hx
  rw [mem_conjSubgroup] at hx
  have h := Subgroup.Normal.conj_mem inferInstance _ (hK hx) g
  rwa [show g * (g⁻¹ * x * g) * g⁻¹ = x by group] at h

theorem sec415a_le_normalizer_conj {A N : Subgroup G} [N.Normal]
    (hN : N ≤ normalizer (A : Set G)) (h : G) :
    N ≤ normalizer ((conjSubgroup h A : Subgroup G) : Set G) := by
  intro o ho
  rw [← conjSubgroup_eq_self_iff]
  have ho' : h⁻¹ * o * h ∈ N := by
    simpa [mul_assoc] using Subgroup.Normal.conj_mem inferInstance o ho h⁻¹
  have hA' : conjSubgroup (h⁻¹ * o * h) A = A := conjSubgroup_eq_self_iff.mpr (hN ho')
  rw [← conjSubgroup_mul, show o * h = h * (h⁻¹ * o * h) by group, conjSubgroup_mul, hA']

theorem sec415a_normal_iSup (K : Subgroup G) : (⨆ g : G, conjSubgroup g K).Normal := by
  refine ⟨fun n hn k => ?_⟩
  refine Subgroup.iSup_induction (fun g : G => conjSubgroup g K)
    (C := fun n => k * n * k⁻¹ ∈ ⨆ g : G, conjSubgroup g K) hn ?_ ?_ ?_
  · intro g x hx
    have hx' : g⁻¹ * x * g ∈ K := mem_conjSubgroup.mp hx
    refine Subgroup.mem_iSup_of_mem (k * g) (mem_conjSubgroup.mpr ?_)
    rw [show (k * g)⁻¹ * (k * x * k⁻¹) * (k * g) = g⁻¹ * x * g by group]
    exact hx'
  · rw [mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  · intro x y hx hy
    rw [show k * (x * y) * k⁻¹ = (k * x * k⁻¹) * (k * y * k⁻¹) by group]
    exact Subgroup.mul_mem _ hx hy

theorem sec415a_prop24 [Finite G] {A : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    {g h : G}
    (hne_bot : conjSubgroup g A ⊓ normalizer ((conjSubgroup h A : Subgroup G) : Set G) ≠ ⊥)
    (hne : conjSubgroup g A ⊓ normalizer ((conjSubgroup h A : Subgroup G) : Set G) ≠
      conjSubgroup g A) :
    Prop24Setup (conjSubgroup g A) (conjSubgroup h A)
      (conjSubgroup g A ⊓ normalizer ((conjSubgroup h A : Subgroup G) : Set G))
      (conjSubgroup h A ⊓ normalizer ((conjSubgroup g A : Subgroup G) : Set G))
      ((conjSubgroup g A ⊓ normalizer ((conjSubgroup h A : Subgroup G) : Set G)) ⊔
        (conjSubgroup h A ⊓ normalizer ((conjSubgroup g A : Subgroup G) : Set G))) where
  elem := isElemAbelian_conjSubgroup hA g
  ti := isTI_conjSubgroup hTI g
  conj := ⟨h * g⁻¹, by rw [← conjSubgroup_mul, inv_mul_cancel_right]⟩
  hL := rfl
  hLb := rfl
  hM := rfl
  ne_bot := hne_bot
  ne := hne

theorem sec415a_comm_conj [Finite G] {A K : Subgroup G} (hA : IsElemAbelian 2 A) (hTI : IsTI A)
    (hKA : K ≤ A)
    (hK : ∀ g h : G, conjSubgroup g K ≤ normalizer ((conjSubgroup h A : Subgroup G) : Set G))
    (g h : G) {x y : G} (hx : x ∈ conjSubgroup g K) (hy : y ∈ conjSubgroup h K) :
    x * y = y * x := by
  have hxA : x ∈ conjSubgroup g A := sec415a_mem_conj_mono hKA g hx
  have hyA : y ∈ conjSubgroup h A := sec415a_mem_conj_mono hKA h hy
  by_cases hgh : conjSubgroup g A ≤ normalizer ((conjSubgroup h A : Subgroup G) : Set G)
  ·
    have e : conjSubgroup g A = conjSubgroup (g * h⁻¹) (conjSubgroup h A) := by
      rw [← conjSubgroup_mul, inv_mul_cancel_right]
    have hE := tim77_2_3 (isElemAbelian_conjSubgroup hA h) (isTI_conjSubgroup hTI h)
      (g := g * h⁻¹) (by rw [← e]; exact hgh)
    have hxS : x ∈ conjSubgroup h A ⊔ conjSubgroup (g * h⁻¹) (conjSubgroup h A) := by
      rw [← e]
      exact Subgroup.mem_sup_right hxA
    have hyS : y ∈ conjSubgroup h A ⊔ conjSubgroup (g * h⁻¹) (conjSubgroup h A) :=
      Subgroup.mem_sup_left hyA
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hxS⟩ ⟨y, hyS⟩)
  ·
    by_cases hx1 : x = 1
    · simp [hx1]
    have hxL : x ∈ conjSubgroup g A ⊓ normalizer ((conjSubgroup h A : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hxA, hK g h hx⟩
    have hyLb : y ∈ conjSubgroup h A ⊓ normalizer ((conjSubgroup g A : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hyA, hK h g hy⟩
    have hne_bot : conjSubgroup g A ⊓ normalizer ((conjSubgroup h A : Subgroup G) : Set G) ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.mem_bot] at hxL
      exact hx1 hxL
    have hne : conjSubgroup g A ⊓ normalizer ((conjSubgroup h A : Subgroup G) : Set G) ≠
        conjSubgroup g A := by
      intro heq
      apply hgh
      intro z hz
      have hzL : z ∈ conjSubgroup g A ⊓ normalizer ((conjSubgroup h A : Subgroup G) : Set G) := by
        rw [heq]
        exact hz
      exact (Subgroup.mem_inf.mp hzL).2
    exact (sec415a_prop24 hA hTI hne_bot hne).comm_L_Lb hxL hyLb

theorem sec415a_of (h414 : Tim77Sec414Statement) : Tim77Sec415aStatement := by
  intro G _ _ A Abar S₀ B hctx hq hH
  have hA : IsElemAbelian 2 A := hctx.hyp.elemAbelian
  have hTI : IsTI A := hctx.hyp.ti
  have hA0O : Section3.A0 A Abar ≤ pCore 2 G := h414 G A Abar S₀ B hctx hq hH
  have hA0A : Section3.A0 A Abar ≤ A := fun x hx => (Subgroup.mem_inf.mp hx).1
  have hON : pCore 2 G ≤ normalizer (A : Set G) := by
    obtain ⟨S, hS2, hSmax, hSN⟩ := hctx.hyp.sylow
    let P : Sylow 2 G := ⟨S, hS2, fun {Q} hQ hle => hSmax Q hQ hle⟩
    have hOS : pCore 2 G ≤ S := IsPGroup.le_sylow_of_normal pCore_isPGroup P
    exact hOS.trans hSN
  have hK : ∀ g h : G, conjSubgroup g (Section3.A0 A Abar) ≤
      normalizer ((conjSubgroup h A : Subgroup G) : Set G) := fun g h =>
    (sec415a_conj_le hA0O g).trans (sec415a_le_normalizer_conj hON h)
  have hcomm : ∀ g h : G, ∀ x ∈ conjSubgroup g (Section3.A0 A Abar),
      ∀ y ∈ conjSubgroup h (Section3.A0 A Abar), x * y = y * x :=
    fun g h x hx y hy => sec415a_comm_conj hA hTI hA0A hK g h hx hy
  have hsq : ∀ g : G, ∀ x ∈ conjSubgroup g (Section3.A0 A Abar), x ^ 2 = 1 := fun g x hx =>
    (isElemAbelian_conjSubgroup hA g).2 x (sec415a_mem_conj_mono hA0A g hx)
  have hN0el : IsElemAbelian 2 (Sec415N0 A Abar) :=
    isElemAbelian_iSup_of_comm (fun g => conjSubgroup g (Section3.A0 A Abar)) hsq
      (fun g h a ha b hb => hcomm g h a ha b hb)
  have hN0n : (Sec415N0 A Abar).Normal := sec415a_normal_iSup (Section3.A0 A Abar)
  have hA0N : Section3.A0 A Abar ≤ Sec415N0 A Abar := by
    intro x hx
    refine Subgroup.mem_iSup_of_mem (1 : G) ?_
    show x ∈ conjSubgroup 1 (Section3.A0 A Abar)
    rw [conjSubgroup_one]
    exact hx
  obtain ⟨g, hg⟩ := hctx.nota.choice.1
  have hbot : Section3.Abar0 A Abar ≠ ⊥ := hctx.nota.choice.2.1.1
  have htop : Section3.Abar0 A Abar ≠ Abar := hctx.nota.choice.2.1.2
  let S₁ : Prop24Setup Abar A (Section3.Abar0 A Abar) (Section3.A0 A Abar)
      (Section3.Abar0 A Abar ⊔ Section3.A0 A Abar) :=
    { elem := by
        rw [hg]
        exact isElemAbelian_conjSubgroup hA g
      ti := by
        rw [hg]
        exact isTI_conjSubgroup hTI g
      conj := ⟨g⁻¹, by rw [hg, ← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one]⟩
      hL := rfl
      hLb := rfl
      hM := rfl
      ne_bot := hbot
      ne := htop }
  let S : Prop24Setup A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar)
      (Section3.Abar0 A Abar ⊔ Section3.A0 A Abar) := S₁.symm
  have hinf : A ⊓ Sec415N0 A Abar ≤ Section3.A0 A Abar := by
    intro x hx
    obtain ⟨hxA, hxN⟩ := Subgroup.mem_inf.mp hx
    by_contra hxA0
    obtain ⟨β, hβ, hβ0⟩ : ∃ β ∈ Abar, β ∉ Section3.Abar0 A Abar := by
      by_contra hcon
      refine htop (le_antisymm (fun y hy => (Subgroup.mem_inf.mp hy).1) ?_)
      intro β hβ
      by_contra hβ0
      exact hcon ⟨β, hβ, hβ0⟩
    have hodd : Odd (orderOf (x * β)) := S.odd_orderOf_mul hxA hxA0 hβ hβ0
    have hββ : β * β = 1 := S.sq_Ab hβ
    have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hββ
    have hsq' : (x * β) * (x * β) ∈ Sec415N0 A Abar := by
      have hc : β * x * β⁻¹ ∈ Sec415N0 A Abar := Subgroup.Normal.conj_mem hN0n x hxN β
      have e : (x * β) * (x * β) = x * (β * x * β⁻¹) := by
        rw [hβinv]
        group
      rw [e]
      exact Subgroup.mul_mem _ hxN hc
    have h4 : (x * β) ^ 4 = 1 := by
      have h2 := hN0el.2 _ hsq'
      rw [← sq, ← pow_mul] at h2
      exact h2
    have hdvd : orderOf (x * β) ∣ 4 := orderOf_dvd_of_pow_eq_one h4
    have hone : orderOf (x * β) = 1 := by
      obtain ⟨d, hd⟩ : ∃ d, orderOf (x * β) = d := ⟨_, rfl⟩
      have hpos : 0 < orderOf (x * β) := orderOf_pos _
      rw [hd] at hdvd hodd hpos ⊢
      have hle : d ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
      interval_cases d <;> first | rfl | omega | (exfalso; revert hodd; decide)
    have hxβ : x * β = 1 := orderOf_eq_one_iff.mp hone
    have hxeq : x = β := by
      rw [eq_inv_of_mul_eq_one_left hxβ, hβinv]
    have hxbot : x ∈ A ⊓ Abar := Subgroup.mem_inf.mpr ⟨hxA, by rw [hxeq]; exact hβ⟩
    rw [S.inf_eq_bot, Subgroup.mem_bot] at hxbot
    exact hxA0 (by rw [hxbot]; exact Subgroup.one_mem _)
  have hSec45 : Sec45Q A Abar B ≤ Sec415N0 A Abar := by
    obtain ⟨k, -, hk⟩ := sec34_exists_k S
    unfold Sec45Q
    refine sup_le hA0N (iSup₂_le fun b _ => ?_)
    intro x hx
    rw [hk, ← conjSubgroup_mul] at hx
    exact Subgroup.mem_iSup_of_mem (b * k) hx
  exact ⟨hN0n, hN0el, le_antisymm hinf (le_inf hA0A hA0N), hSec45⟩

end CFSG.RankThree.GF2n.Tim77
