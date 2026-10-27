module

public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRestDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepZpowersInf
public import CFSG.LocalAnalysis.StandardType.GGE6DepNormalizerOfConj
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenOver
import TauCeti.GroupTheory.FixedSubgroup
import Mathlib.GroupTheory.Index

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G] [Finite G]

private theorem gg6D5_conjAut_fixed_of_gamma_fixed {p : ℕ} (hp : p.Prime)
    {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k)
    {n : G} (hnL : n ∈ L) (hnB : n ∈ Subgroup.normalizer (Bs : Set G))
    {φ : MulAut ↥(ggGamma L hBsN).range}
    (hover : ∀ b : ↥Bs, (ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnB b) =
      φ ((ggGamma L hBsN).rangeRestrict b))
    {b : ↥Bs}
    (hb : φ ((ggGamma L hBsN).rangeRestrict b) = (ggGamma L hBsN).rangeRestrict b) :
    ggConjAut Bs hnB b = b := by
  have hx : x ∈ Bs ⊓ Subgroup.centralizer (L : Set G) := by
    rw [hker]; exact Subgroup.mem_zpowers x
  have hxp : x ^ p = 1 := hBs.2 x hx.1
  have hzbot : Subgroup.zpowers x ⊓ L = ⊥ :=
    GGE6Dep.zpowers_inf_eq_bot_of_centralizer hp hx.2 hxp hZ
  obtain ⟨l, hlL, k, hbk⟩ := hBsL b b.2
  have hlBs : l ∈ Bs := by
    have hl : l = b * (x ^ k)⁻¹ := by rw [hbk]; group
    rw [hl]
    exact Bs.mul_mem b.2 (Bs.inv_mem (Bs.pow_mem hx.1 k))
  have hlH0 : l ∈ Bs ⊓ L := ⟨hlBs, hlL⟩
  have hconjBs : n * l * n⁻¹ ∈ Bs := (Subgroup.mem_normalizer_iff.mp hnB l).mp hlBs
  have hconjL : n * l * n⁻¹ ∈ L := L.mul_mem (L.mul_mem hnL hlL) (L.inv_mem hnL)
  have hconjH0 : n * l * n⁻¹ ∈ Bs ⊓ L := ⟨hconjBs, hconjL⟩
  have hratioBs : (n * l * n⁻¹) * l⁻¹ ∈ Bs := Bs.mul_mem hconjBs (Bs.inv_mem hlBs)
  have hratioH0 : (n * l * n⁻¹) * l⁻¹ ∈ Bs ⊓ L :=
    (Bs ⊓ L).mul_mem hconjH0 ((Bs ⊓ L).inv_mem hlH0)
  have hxγ : (ggGamma L hBsN) ⟨x, hx.1⟩ = 1 :=
    (ggGamma_eq_one_iff L hBsN ⟨x, hx.1⟩).mpr hx.2
  have hxγ' : (ggGamma L hBsN).rangeRestrict ⟨x, hx.1⟩ = 1 := by
    apply Subtype.ext
    simpa using hxγ
  have hbγ : (ggGamma L hBsN).rangeRestrict ⟨b, b.2⟩ =
      (ggGamma L hBsN).rangeRestrict ⟨l, hlBs⟩ := by
    have hbsub : (⟨b, b.2⟩ : ↥Bs) = ⟨l, hlBs⟩ * ⟨x, hx.1⟩ ^ k := by
      apply Subtype.ext
      simpa using hbk
    rw [hbsub, map_mul, map_pow, hxγ', one_pow, mul_one]
  have hconjγ : (ggGamma L hBsN).rangeRestrict ⟨n * l * n⁻¹, hconjBs⟩ =
      (ggGamma L hBsN).rangeRestrict ⟨l, hlBs⟩ := by
    have h1 := hover ⟨l, hlBs⟩
    have h2 : ggConjAut Bs hnB ⟨l, hlBs⟩ = ⟨n * l * n⁻¹, hconjBs⟩ := by
      apply Subtype.ext
      rw [ggConjAut_apply]
    rw [h2] at h1
    have h3 : φ ((ggGamma L hBsN).rangeRestrict ⟨l, hlBs⟩) =
        (ggGamma L hBsN).rangeRestrict ⟨l, hlBs⟩ := by
      rw [← hbγ]
      simpa using hb
    rw [h3] at h1
    exact h1
  have hratioγ : (ggGamma L hBsN) ⟨(n * l * n⁻¹) * l⁻¹, hratioBs⟩ = 1 := by
    have h1 : (ggGamma L hBsN).rangeRestrict ⟨(n * l * n⁻¹) * l⁻¹, hratioBs⟩ = 1 := by
      have hmul : (ggGamma L hBsN).rangeRestrict ⟨(n * l * n⁻¹) * l⁻¹, hratioBs⟩ =
          (ggGamma L hBsN).rangeRestrict ⟨n * l * n⁻¹, hconjBs⟩ *
            ((ggGamma L hBsN).rangeRestrict ⟨l, hlBs⟩)⁻¹ := by
        rw [show (⟨(n * l * n⁻¹) * l⁻¹, hratioBs⟩ : ↥Bs) =
            ⟨n * l * n⁻¹, hconjBs⟩ * (⟨l, hlBs⟩)⁻¹ from Subtype.ext rfl, map_mul, map_inv]
      rw [hmul, hconjγ, mul_inv_cancel]
    have := congrArg Subtype.val h1
    simpa using this
  have hratioZp : (n * l * n⁻¹) * l⁻¹ ∈ Subgroup.zpowers x := by
    rw [← hker]
    exact ⟨hratioBs, (ggGamma_eq_one_iff L hBsN ⟨_, hratioBs⟩).mp hratioγ⟩
  have hle : (Bs ⊓ L) ⊓ Subgroup.zpowers x ≤ (⊥ : Subgroup G) :=
    calc (Bs ⊓ L) ⊓ Subgroup.zpowers x ≤ L ⊓ Subgroup.zpowers x :=
          inf_le_inf inf_le_right le_rfl
      _ = Subgroup.zpowers x ⊓ L := inf_comm _ _
      _ = ⊥ := hzbot
  have hratio1 : (n * l * n⁻¹) * l⁻¹ = 1 := by
    have hmem : (n * l * n⁻¹) * l⁻¹ ∈ (Bs ⊓ L) ⊓ Subgroup.zpowers x :=
      ⟨hratioH0, hratioZp⟩
    simpa using hle hmem
  have hconjeq : n * l * n⁻¹ = l := mul_inv_eq_one.mp hratio1
  have hnx : n * x * n⁻¹ = x := by
    have h := (Subgroup.mem_centralizer_iff.mp hx.2) n hnL
    rw [h]; group
  have hnxk_all : ∀ m : ℕ, n * x ^ m * n⁻¹ = x ^ m := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ]
      calc n * (x ^ m * x) * n⁻¹ = (n * x ^ m * n⁻¹) * (n * x * n⁻¹) := by group
        _ = x ^ m * x := by rw [ih, hnx]
  have hnxk : n * x ^ k * n⁻¹ = x ^ k := hnxk_all k
  apply Subtype.ext
  rw [ggConjAut_apply, hbk]
  calc n * (l * x ^ k) * n⁻¹ = (n * l * n⁻¹) * (n * x ^ k * n⁻¹) := by group
    _ = l * x ^ k := by rw [hconjeq, hnxk]

private theorem gg6D5_card_fix {p : ℕ} (hp : p.Prime)
    {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k)
    {n : G} (hnL : n ∈ L) (hnB : n ∈ Subgroup.normalizer (Bs : Set G))
    {φ : MulAut ↥(ggGamma L hBsN).range}
    (hover : ∀ b : ↥Bs, (ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnB b) =
      φ ((ggGamma L hBsN).rangeRestrict b)) :
    Nat.card {b : ↥Bs // ggConjAut Bs hnB b = b} =
      Nat.card ↥(ggGamma L hBsN).ker *
        Nat.card {a : ↥(ggGamma L hBsN).range // φ a = a} := by
  let ψ : MulAut ↥Bs := ggConjAut Bs hnB
  let Fψ : Subgroup ↥Bs := TauCeti.fixedSubgroup (ψ : ↥Bs →* ↥Bs)
  let Fφ : Subgroup ↥(ggGamma L hBsN).range :=
    TauCeti.fixedSubgroup (φ : ↥(ggGamma L hBsN).range →* ↥(ggGamma L hBsN).range)
  have memFψ : ∀ b : ↥Bs, b ∈ Fψ ↔ ψ b = b := fun b => TauCeti.mem_fixedSubgroup
  have memFφ : ∀ a : ↥(ggGamma L hBsN).range, a ∈ Fφ ↔ φ a = a :=
    fun a => TauCeti.mem_fixedSubgroup
  have hle : (ggGamma L hBsN).ker ≤ Fψ := by
    intro b hb
    rw [memFψ b]
    refine gg6D5_conjAut_fixed_of_gamma_fixed hp hBs hBsN hker hZ hBsL hnL hnB hover ?_
    have hb' : (ggGamma L hBsN).rangeRestrict b = 1 := by
      rw [← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict]
      exact hb
    rw [hb', map_one]
  have hrange : ((ggGamma L hBsN).rangeRestrict.domRestrict Fψ).range = Fφ := by
    apply le_antisymm
    · rintro a ⟨b, rfl⟩
      rw [memFφ, MonoidHom.domRestrict_apply]
      have hb : ψ (b : ↥Bs) = (b : ↥Bs) := (memFψ _).mp b.2
      have h1 := hover (b : ↥Bs)
      rw [hb] at h1
      exact h1.symm
    · intro a ha
      have ha' : φ a = a := (memFφ a).mp ha
      obtain ⟨b, hb⟩ := MonoidHom.rangeRestrict_surjective (ggGamma L hBsN) a
      refine ⟨⟨b, ?_⟩, ?_⟩
      · rw [memFψ b]
        refine gg6D5_conjAut_fixed_of_gamma_fixed hp hBs hBsN hker hZ hBsL hnL hnB hover ?_
        rw [hb, ha']
      · rw [MonoidHom.domRestrict_apply]
        exact hb
  have hker' : Nat.card ↥((ggGamma L hBsN).rangeRestrict.domRestrict Fψ).ker =
      Nat.card ↥(ggGamma L hBsN).ker := by
    rw [MonoidHom.ker_restrict, MonoidHom.ker_rangeRestrict]
    have h := Subgroup.card_subtype Fψ ((ggGamma L hBsN).ker.subgroupOf Fψ)
    rw [Subgroup.subgroupOf_map_subtype,
      le_antisymm inf_le_left (le_inf le_rfl hle)] at h
    exact h.symm
  have hcard := Subgroup.card_ker_mul_card_range
    ((ggGamma L hBsN).rangeRestrict.domRestrict Fψ)
  rw [hker', hrange] at hcard
  change Nat.card ↥Fψ = Nat.card ↥(ggGamma L hBsN).ker * Nat.card ↥Fφ
  exact hcard.symm

theorem ggTorusAut_noTransvection_gamma {p : ℕ} (hp : p.Prime) {Bs L : Subgroup G} {x : G}
    (hBs : IsElemAbelian p Bs) (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hker : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x)
    (hZ : ¬ p ∣ Nat.card ↥(Subgroup.center ↥L))
    (hBsL : ∀ b ∈ Bs, ∃ l ∈ L, ∃ k : ℕ, b = l * x ^ k) (hnt : GGNoTransvection p Bs) :
    ∀ φ ∈ ggTorusAut (ggGamma L hBsN).range, ¬ GGIsTransvection p φ := by
  intro φ hφmem hφtr
  have hφmem' : φ ∈ ggAutomizer (MulAut.conj : ↥L →* MulAut ↥L).range
      (ggGamma L hBsN).range := by
    simpa only [ggTorusAut] using hφmem
  obtain ⟨g', hg'range, hg'N, hφg'⟩ := (mem_ggAutomizer_iff).mp hφmem'
  obtain ⟨n, hn_eq⟩ := MonoidHom.mem_range.mp hg'range
  have hmem : MulAut.conj (⟨(n : G), n.2⟩ : ↥L) ∈
      Subgroup.normalizer ((ggGamma L hBsN).range : Set (MulAut ↥L)) := by
    have hnsub : (⟨(n : G), n.2⟩ : ↥L) = n := Subtype.ext rfl
    rw [hnsub, hn_eq]
    exact hg'N
  have hnB : (n : G) ∈ Subgroup.normalizer (Bs : Set G) :=
    GGE6Dep.mem_normalizer_of_conj_mem_normalizer_range hp hBsN hBs hker hZ hBsL n.2 hmem
  have h'' := conj_mem_normalizer_range_ggGamma hBsN n.2 hnB
  have hφeq : φ = ggConjAut (ggGamma L hBsN).range h'' := by
    refine MulEquiv.ext fun a => ?_
    apply Subtype.ext
    rw [hφg' a, ggConjAut_apply]
    rw [show (⟨(n : G), n.2⟩ : ↥L) = n from Subtype.ext rfl, hn_eq]
  have hover : ∀ b : ↥Bs, (ggGamma L hBsN).rangeRestrict (ggConjAut Bs hnB b) =
      φ ((ggGamma L hBsN).rangeRestrict b) := by
    intro b
    rw [hφeq]
    exact ggOverGamma_conjAut (K := L) (hN := hBsN) n.2 hnB b
  have hntψ : ¬ GGIsTransvection p (ggConjAut Bs hnB) :=
    hnt _ (ggConjAut_mem_ggInduced (Subgroup.mem_top (n : G)) hnB)
  refine hntψ ⟨?_, ?_⟩
  · have hcardfix := gg6D5_card_fix hp hBs hBsN hker hZ hBsL n.2 hnB hover
    have hcardγ : Nat.card ↥(ggGamma L hBsN).ker *
        Nat.card ↥(ggGamma L hBsN).range = Nat.card ↥Bs :=
      Subgroup.card_ker_mul_card_range (ggGamma L hBsN)
    rw [hcardfix, mul_assoc, hφtr.1, hcardγ]
  · intro b
    refine gg6D5_conjAut_fixed_of_gamma_fixed hp hBs hBsN hker hZ hBsL n.2 hnB hover ?_
    have hγ : (ggGamma L hBsN).rangeRestrict (b⁻¹ * ggConjAut Bs hnB b) =
        ((ggGamma L hBsN).rangeRestrict b)⁻¹ *
          φ ((ggGamma L hBsN).rangeRestrict b) := by
      rw [map_mul, map_inv, hover b]
    rw [hγ]
    exact hφtr.2 _

end CFSG.StandardType

end
