module

public import CFSG.RankThree.GF2n.Tim77.Sec415a
import all CFSG.Timmesfeld.RootInvolutions.RootInvolutionSetting

public section

namespace CFSG.RankThree.GF2n.Tim77

open scoped commutatorElement
open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec415c_map_pCore_le (A : Subgroup G) :
    (pCore 2 ↥(normalClosure (A : Set G))).map (normalClosure (A : Set G)).subtype ≤
      pCore 2 G := by
  have hn : ((pCore 2 ↥(normalClosure (A : Set G))).map
      (normalClosure (A : Set G)).subtype).Normal := inferInstance
  have hp := IsPGroup.map (pCore_isPGroup (p := 2) (G := ↥(normalClosure (A : Set G))))
    (normalClosure (A : Set G)).subtype
  exact le_sSup ⟨hn, hp⟩

theorem sec415c_pCore_le_normalizer [Finite G] {A Abar S₀ B : Subgroup G}
    (hctx : Sec3Ctx A Abar S₀ B) (g : G) :
    pCore 2 G ≤ normalizer ((conjSubgroup g A : Subgroup G) : Set G) := by
  obtain ⟨S, hS2, hSmax, hSN⟩ := hctx.hyp.sylow
  let P : Sylow 2 G := ⟨S, hS2, fun {Q} hQ hle => hSmax Q hQ hle⟩
  have hOS : pCore 2 G ≤ S := IsPGroup.le_sylow_of_normal pCore_isPGroup P
  exact sec415a_le_normalizer_conj (hOS.trans hSN) g

theorem sec415c_prop24 [Finite G] {A Abar S₀ B : Subgroup G} (hctx : Sec3Ctx A Abar S₀ B) :
    Prop24Setup A Abar (Section3.A0 A Abar) (Section3.Abar0 A Abar)
      (Section3.Abar0 A Abar ⊔ Section3.A0 A Abar) := by
  obtain ⟨g, hg⟩ := hctx.nota.choice.1
  have hbot : Section3.Abar0 A Abar ≠ ⊥ := hctx.nota.choice.2.1.1
  have htop : Section3.Abar0 A Abar ≠ Abar := hctx.nota.choice.2.1.2
  have hA : IsElemAbelian 2 A := hctx.hyp.elemAbelian
  have hTI : IsTI A := hctx.hyp.ti
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
  exact S₁.symm

theorem sec415c_inf_pCore_le [Finite G] {A Abar S₀ B : Subgroup G}
    (hctx : Sec3Ctx A Abar S₀ B) : A ⊓ pCore 2 G ≤ Section3.A0 A Abar := by
  intro x hx
  obtain ⟨hxA, hxO⟩ := Subgroup.mem_inf.mp hx
  by_contra hxA0
  obtain ⟨β, hβ, hβ0⟩ : ∃ β ∈ Abar, β ∉ Section3.Abar0 A Abar := by
    by_contra hcon
    refine hctx.nota.choice.2.1.2 (le_antisymm (fun y hy => (Subgroup.mem_inf.mp hy).1) ?_)
    intro β hβ
    by_contra hβ0
    exact hcon ⟨β, hβ, hβ0⟩
  let S := sec415c_prop24 hctx
  have hodd : Odd (orderOf (x * β)) := S.odd_orderOf_mul hxA hxA0 hβ hβ0
  have hββ : β * β = 1 := S.sq_Ab hβ
  have hβinv : β⁻¹ = β := inv_eq_of_mul_eq_one_right hββ
  have hsq : (x * β) ^ 2 ∈ pCore 2 G := by
    have hc : β * x * β⁻¹ ∈ pCore 2 G :=
      Subgroup.Normal.conj_mem (pCore_normal (p := 2) (G := G)) x hxO β
    have e : (x * β) ^ 2 = x * (β * x * β⁻¹) := by
      rw [sq, hβinv]
      group
    rw [e]
    exact Subgroup.mul_mem _ hxO hc
  have hcop : Nat.Coprime (orderOf (x * β)) 2 := Nat.coprime_two_right.mpr hodd
  have hg : Nat.gcd (orderOf (x * β)) 2 = 1 := hcop
  have hord2 : orderOf ((x * β) ^ 2) = orderOf (x * β) := by
    rw [orderOf_pow, hg, Nat.div_one]
  obtain ⟨k, hk⟩ := (pCore_isPGroup (p := 2) (G := G)) ⟨(x * β) ^ 2, hsq⟩
  have hk' : ((x * β) ^ 2) ^ 2 ^ k = 1 := by
    simpa using congrArg Subtype.val hk
  have hdvd : orderOf (x * β) ∣ 2 ^ k := by
    rw [← hord2]
    exact orderOf_dvd_of_pow_eq_one hk'
  have hone : orderOf (x * β) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hcop) hdvd
  have hxβ : x * β = 1 := orderOf_eq_one_iff.mp hone
  have hxeq : x = β := by
    rw [eq_inv_of_mul_eq_one_left hxβ, hβinv]
  have hxbot : x ∈ A ⊓ Abar := Subgroup.mem_inf.mpr ⟨hxA, by rw [hxeq]; exact hβ⟩
  rw [S.inf_eq_bot, Subgroup.mem_bot] at hxbot
  exact hxA0 (by rw [hxbot]; exact Subgroup.one_mem _)

theorem sec415c_conj_inf_pCore_le [Finite G] {A Abar S₀ B : Subgroup G}
    (hctx : Sec3Ctx A Abar S₀ B) (c : G) :
    conjSubgroup c A ⊓ pCore 2 G ≤ conjSubgroup c (Section3.A0 A Abar) := by
  intro x hx
  obtain ⟨hxc, hxO⟩ := Subgroup.mem_inf.mp hx
  have h1 : c⁻¹ * x * c ∈ A ⊓ pCore 2 G := by
    refine Subgroup.mem_inf.mpr ⟨mem_conjSubgroup.mp hxc, ?_⟩
    have h := Subgroup.Normal.conj_mem (pCore_normal (p := 2) (G := G)) x hxO c⁻¹
    rwa [inv_inv] at h
  exact mem_conjSubgroup.mpr (sec415c_inf_pCore_le hctx h1)

theorem sec415c_conj_le_N0 {A Abar : Subgroup G} (c : G) :
    conjSubgroup c (Section3.A0 A Abar) ≤ Sec415N0 A Abar :=
  le_iSup (fun g : G => conjSubgroup g (Section3.A0 A Abar)) c

theorem sec415c_commutatorElement_mem [Finite G] {A Abar S₀ B : Subgroup G}
    (hctx : Sec3Ctx A Abar S₀ B) {o : G} (ho : o ∈ pCore 2 G) (c : G) {t : G}
    (ht : t ∈ conjSubgroup c A) : ⁅o, t⁆ ∈ Sec415N0 A Abar := by
  have hon : o ∈ normalizer ((conjSubgroup c A : Subgroup G) : Set G) :=
    sec415c_pCore_le_normalizer hctx c ho
  have h1 : o * t * o⁻¹ ∈ conjSubgroup c A := (Subgroup.mem_normalizer_iff.mp hon t).mp ht
  have h2 : o * t * o⁻¹ * t⁻¹ ∈ conjSubgroup c A :=
    (conjSubgroup c A).mul_mem h1 ((conjSubgroup c A).inv_mem ht)
  have h3 : o * t * o⁻¹ * t⁻¹ ∈ pCore 2 G := by
    have hc : t * o⁻¹ * t⁻¹ ∈ pCore 2 G :=
      Subgroup.Normal.conj_mem (pCore_normal (p := 2) (G := G)) o⁻¹ ((pCore 2 G).inv_mem ho) t
    have e : o * t * o⁻¹ * t⁻¹ = o * (t * o⁻¹ * t⁻¹) := by group
    rw [e]
    exact (pCore 2 G).mul_mem ho hc
  have h4 : o * t * o⁻¹ * t⁻¹ ∈ conjSubgroup c (Section3.A0 A Abar) :=
    sec415c_conj_inf_pCore_le hctx c (Subgroup.mem_inf.mpr ⟨h2, h3⟩)
  rw [commutatorElement_def]
  exact sec415c_conj_le_N0 c h4

theorem sec415c_commutatorElement_normalClosure [Finite G] {A Abar S₀ B : Subgroup G}
    (hctx : Sec3Ctx A Abar S₀ B) {o : G} (ho : o ∈ pCore 2 G) {y : G}
    (hy : y ∈ normalClosure (A : Set G)) : ⁅o, y⁆ ∈ Sec415N0 A Abar := by
  have hN0n : (Sec415N0 A Abar).Normal := sec415a_normal_iSup (Section3.A0 A Abar)
  let K : Subgroup G :=
    { carrier := {y | ⁅o, y⁆ ∈ Sec415N0 A Abar}
      mul_mem' := fun {y z} hy hz => by
        have hy' : ⁅o, y⁆ ∈ Sec415N0 A Abar := hy
        have hz' : ⁅o, z⁆ ∈ Sec415N0 A Abar := hz
        have e : ⁅o, y * z⁆ = ⁅o, y⁆ * (y * ⁅o, z⁆ * y⁻¹) := by
          simp only [commutatorElement_def]
          group
        show ⁅o, y * z⁆ ∈ Sec415N0 A Abar
        rw [e]
        exact (Sec415N0 A Abar).mul_mem hy' (hN0n.conj_mem _ hz' y)
      one_mem' := by
        show ⁅o, (1 : G)⁆ ∈ Sec415N0 A Abar
        rw [commutatorElement_one_right]
        exact (Sec415N0 A Abar).one_mem
      inv_mem' := fun {y} hy => by
        have hy' : ⁅o, y⁆ ∈ Sec415N0 A Abar := hy
        have e : ⁅o, y⁻¹⁆ = y⁻¹ * ⁅o, y⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        show ⁅o, y⁻¹⁆ ∈ Sec415N0 A Abar
        rw [e]
        exact hN0n.conj_mem _ ((Sec415N0 A Abar).inv_mem hy') y⁻¹ }
  have hK : normalClosure (A : Set G) ≤ K := by
    unfold normalClosure
    rw [Subgroup.closure_le]
    intro x hx
    obtain ⟨a, ha, hax⟩ := Group.mem_conjugatesOfSet_iff.mp hx
    obtain ⟨c, hc⟩ := isConj_iff.mp hax
    subst hc
    have hmem : c * a * c⁻¹ ∈ conjSubgroup c A :=
      mem_conjSubgroup.mpr (by rw [show c⁻¹ * (c * a * c⁻¹) * c = a by group]; exact ha)
    show ⁅o, c * a * c⁻¹⁆ ∈ Sec415N0 A Abar
    exact sec415c_commutatorElement_mem hctx ho c hmem
  exact hK hy

theorem sec415c_of : Tim77Sec415cStatement := by
  intro G _ _ A Abar S₀ B hctx _ _
  refine Subgroup.commutator_le.mpr ?_
  intro x hx y _
  have hxO : (x : G) ∈ pCore 2 G := sec415c_map_pCore_le A (Subgroup.mem_map_of_mem _ hx)
  have key := sec415c_commutatorElement_normalClosure hctx hxO y.2
  rw [Subgroup.mem_subgroupOf]
  exact key

end CFSG.RankThree.GF2n.Tim77
