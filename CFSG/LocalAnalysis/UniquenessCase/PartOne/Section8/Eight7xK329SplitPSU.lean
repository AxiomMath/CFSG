module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitDefs
import CFSG.LieType.SemisimpleCentralizers.HeldUCDMain
import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofUTypes
import CFSG.LieType.SemisimpleCentralizers.OrderThree.CenterQuot
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitOrder
import CFSG.LieType.SemisimpleCentralizers.OrderThree.OrthoBasis
import CFSG.LieType.SemisimpleCentralizers.OrderThree.Projectors
public import CFSG.LieType.SemisimpleCentralizers.HeldUCDKBlock
public import CFSG.LieType.SemisimpleCentralizers.HeldUnitaryComponents
import CFSG.LieType.SemisimpleCentralizers.HeldCompTrivSU

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open (StatedLieAdmissible StatedSU)

open CFSG.Open (StatedScalars StatedSL)
open CFSG.LieType.SemisimpleCentralizers


private theorem k329u3c_map_commutator_top {Γ Γ' : Type} [Group Γ] [Group Γ'] (e : Γ ≃* Γ') :
    (commutator Γ).map e.toMonoidHom = commutator Γ' := by
  rw [commutator_def, commutator_def, Subgroup.map_commutator,
    Subgroup.map_top_of_surjective _ e.surjective]

private theorem k329u3c_commutator_GL {d : ℕ} (M : Type) [Field M] [Finite M]
    (hd : 2 ≤ d) (hM4 : 4 ≤ Nat.card M) :
    commutator (GL (Fin d) M) = StatedSL d M := by
  have h22 : d ≠ 2 ∨ Nat.card M ≠ 2 := Or.inr (by omega)
  have h23 : d ≠ 2 ∨ Nat.card M ≠ 3 := Or.inr (by omega)
  apply le_antisymm
  · rw [commutator_def]
    exact Subgroup.commutator_le.mpr fun x _ y _ =>
      Held.commutatorElement_mem_statedSL x y
  · rw [commutator_def]
    have hperf : Group.IsPerfect (StatedSL d M) :=
      Held.hct_isPerfect_statedSL M hd h22 h23
    calc StatedSL d M = ⁅StatedSL d M, StatedSL d M⁆ :=
          (Subgroup.isPerfect_iff.mp hperf).symm
      _ ≤ ⁅(⊤ : Subgroup (GL (Fin d) M)), ⊤⁆ := Subgroup.commutator_mono le_top le_top

private theorem k329u3c_commutator_heldGU_map {a d : ℕ} {M : Type} [Field M] [Finite M]
    (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ (2 ^ (3 * d)))
    (hK : Nat.card M = (2 ^ (3 * d)) ^ 2) (hf : 2 ≤ 3 * d) (ha : 2 ≤ a) :
    (commutator (Held.heldGU a M τ hτ)).map (Held.heldGU a M τ hτ).subtype =
      Held.heldSU a M τ hτ := by
  apply le_antisymm
  · rw [Subgroup.map_subtype_commutator]
    exact Subgroup.commutator_le.mpr fun x hx y hy => Held.commutatorElement_mem_heldSU hx hy
  · rw [Subgroup.map_subtype_commutator]
    have : Fintype M := Fintype.ofFinite M
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : CharP M 2 := charP_of_card_eq_prime_pow (p := 2) (f := 6 * d)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]; congr 1; ring)
    have hperf : Group.IsPerfect (Held.heldSU a M τ hτ) := by
      rw [Held.hct_heldSU_eq_statedSU hτQ]
      exact Group.isPerfect_def.mpr
        (CFSG.ComponentClassification.RankTwoClassical.commutator_statedSU hK hf ha)
    calc Held.heldSU a M τ hτ = ⁅Held.heldSU a M τ hτ, Held.heldSU a M τ hτ⁆ :=
          (Subgroup.isPerfect_iff.mp hperf).symm
      _ ≤ ⁅Held.heldGU a M τ hτ, Held.heldGU a M τ hτ⁆ :=
          Subgroup.commutator_mono inf_le_left inf_le_left

private theorem k329u3c_block {Γ : Type} [Group Γ]
    (hΓ : Held.UnitaryOrLinearBlock (2 ^ 3) Γ) :
    commutator Γ = ⊥ ∨ CFSG.Open.IsQuasisimple ↥(commutator Γ) := by
  rcases hΓ with
    ⟨a, d, M, hMF, hMfin, τ, hτ, hodd, hτQ, hcard, ⟨ε⟩⟩ |
    ⟨b, e, M, hMF, hMfin, hcard, ⟨ε⟩⟩
  ·
    let : Field M := hMF
    have : Finite M := hMfin
    have hd1 : 1 ≤ d := by
      obtain ⟨k, rfl⟩ := hodd
      omega
    have hf : 2 ≤ 3 * d := by omega
    have hτQ' : ∀ x, τ x = x ^ (2 ^ (3 * d)) := fun x => by
      rw [hτQ x, ← pow_mul]
    have hK : Nat.card M = (2 ^ (3 * d)) ^ 2 := by
      rw [hcard]
      congr 1
      rw [← pow_mul]
    by_cases ha : 2 ≤ a
    · right
      have hmap : (commutator Γ).map ε.toMonoidHom = commutator ↥(Held.heldGU a M τ hτ) :=
        k329u3c_map_commutator_top ε
      have hmap2 := k329u3c_commutator_heldGU_map τ hτ hτQ' hK hf ha
      have hcomp : (commutator Γ).map
          ((Held.heldGU a M τ hτ).subtype.comp ε.toMonoidHom) =
          Held.heldSU a M τ hτ := by
        rw [← Subgroup.map_map, hmap, hmap2]
      have hinj : Function.Injective
          ((Held.heldGU a M τ hτ).subtype.comp ε.toMonoidHom) :=
        (Held.heldGU a M τ hτ).subtype_injective.comp ε.injective
      have hiso : Nonempty (↥(commutator Γ) ≃* ↥(Held.heldSU a M τ hτ)) :=
        ⟨(Subgroup.equivMapOfInjective (commutator Γ)
            ((Held.heldGU a M τ hτ).subtype.comp ε.toMonoidHom) hinj).trans
          (MulEquiv.subgroupCongr hcomp)⟩
      have : Fintype M := Fintype.ofFinite M
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : CharP M 2 := charP_of_card_eq_prime_pow (p := 2) (f := 6 * d)
        (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul]; congr 1; ring)
      have hq : CFSG.Open.IsQuasisimple ↥(Held.heldSU a M τ hτ) := by
        rw [Held.hct_heldSU_eq_statedSU hτQ']
        exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).mp
          ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
            (CFSG.ComponentClassification.RankTwoClassical.isQuasisimple_statedSU_of_two_le
              hK hf ha))
      obtain ⟨hiso'⟩ := hiso
      exact k329_isQuasisimple_of_mulEquiv hiso'.symm hq
    · left
      have ha1 : a ≤ 1 := by omega
      have : IsMulCommutative Γ := IsMulCommutative.of_comm (M := Γ) fun x y =>
        ε.injective (by
          rw [map_mul, map_mul]
          exact Subtype.ext
            (CFSG.LieType.SemisimpleCentralizers.OrderThree.mul_comm_GL_fin_of_le_one
              (F := M) ha1
              ((ε x : ↥(Held.heldGU a M τ hτ)) : GL (Fin a) M)
              ((ε y : ↥(Held.heldGU a M τ hτ)) : GL (Fin a) M)))
      exact commutator_eq_bot Γ
  ·
    let : Field M := hMF
    have : Finite M := hMfin
    have h1 : 1 < Nat.card M := Finite.one_lt_card
    have he1 : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with he | he
      · subst he
        rw [hcard] at h1
        norm_num at h1
      · exact he
    have hM4 : 4 ≤ Nat.card M := by
      rw [hcard]
      have h2e : 2 ≤ 2 * e := by omega
      calc 4 ≤ ((2 : ℕ) ^ 3) ^ 2 := by norm_num
        _ ≤ ((2 : ℕ) ^ 3) ^ (2 * e) := pow_le_pow_right' (by norm_num) h2e
    by_cases hb : 2 ≤ b
    · right
      have hmap : (commutator Γ).map ε.toMonoidHom = commutator (GL (Fin b) M) :=
        k329u3c_map_commutator_top ε
      have hcomp : (commutator Γ).map ε.toMonoidHom = StatedSL b M := by
        rw [hmap, k329u3c_commutator_GL M hb hM4]
      have hiso : Nonempty (↥(commutator Γ) ≃* ↥(StatedSL b M)) :=
        ⟨(Subgroup.equivMapOfInjective (commutator Γ) ε.toMonoidHom ε.injective).trans
          (MulEquiv.subgroupCongr hcomp)⟩
      have hq : CFSG.Open.IsQuasisimple ↥(StatedSL b M) :=
        Held.hct_isQuasisimple_statedSL M hb (Or.inr (by omega)) (Or.inr (by omega))
      obtain ⟨hiso'⟩ := hiso
      exact k329_isQuasisimple_of_mulEquiv hiso'.symm hq
    · left
      have hb1 : b ≤ 1 := by omega
      have : IsMulCommutative Γ := IsMulCommutative.of_comm (M := Γ) fun x y =>
        ε.injective (by
          rw [map_mul, map_mul]
          exact CFSG.LieType.SemisimpleCentralizers.OrderThree.mul_comm_GL_fin_of_le_one
            (F := M) hb1 (ε x) (ε y))
      exact commutator_eq_bot Γ




private theorem k329u3c_pi_eq_iSup {ι : Type} [Fintype ι] [DecidableEq ι] {M : ι → Type}
    [∀ i, Group (M i)] (S : (i : ι) → Subgroup (M i)) :
    Subgroup.pi Set.univ S = ⨆ i, (S i).map (MonoidHom.mulSingle M i) := by
  refine le_antisymm ?_ ?_
  · rw [Subgroup.pi_le_iff]
    intro i
    exact le_iSup (fun i => (S i).map (MonoidHom.mulSingle M i)) i
  · refine iSup_le fun i => ?_
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_pi]
    intro j _
    rw [MonoidHom.mulSingle_apply]
    by_cases h : j = i
    · subst h; simpa using ha
    · rw [Pi.mulSingle_eq_of_ne h]; exact Subgroup.one_mem _

private theorem k329u3c_mem_centralizer_subtype {G H : Type} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) (x a : G) :
    a ∈ Subgroup.centralizer ({x} : Set G) ↔
      f a ∈ Subgroup.centralizer ({(f x)} : Set H) := by
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h; rw [← map_mul, ← map_mul, h]
  · intro h; exact hf (by rw [map_mul, map_mul, h])

private theorem k329u3c_iSup_subtype_eq {M : Type} [Group M] {r : ℕ} (p : Fin r → Prop)
    [DecidablePred p] (S : Fin r → Subgroup M) (htriv : ∀ i, ¬ p i → S i = ⊥) :
    (⨆ i : Fin r, S i) = ⨆ i : {i : Fin r // p i}, S i.val := by
  refine le_antisymm ?_ ?_
  · refine iSup_le fun i => ?_
    by_cases h : p i
    · exact le_iSup (fun j : {i : Fin r // p i} => S j.val) ⟨i, h⟩
    · rw [htriv i h]; exact bot_le
  · refine iSup_le fun i => ?_
    exact le_iSup (fun j : Fin r => S j) i.val

private theorem k329u3c_map_commutator_top_le {K : Type} [Field K] {n r : ℕ}
    {H : Fin r → Type} [∀ k, Group (H k)] (θ : (∀ k, H k) →* GL (Fin n) K) :
    Subgroup.map θ (⁅(⊤ : Subgroup (∀ k, H k)), ⊤⁆) ≤
      ⨆ k, ((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ := by
  have hpi : (⊤ : Subgroup (∀ k, H k)) = Subgroup.pi Set.univ (fun _ => ⊤) := by
    ext w; simp [Subgroup.mem_pi]
  rw [hpi, Subgroup.commutator_pi_pi_of_finite, k329u3c_pi_eq_iSup, Subgroup.map_iSup]
  refine iSup_le fun k => le_iSup (fun j => ((commutator (H j)).map
    (MonoidHom.mulSingle H j)).map θ) k

private theorem k329u3c_factor_le_SU {K : Type} [Field K] {n r : ℕ}
    {H : Fin r → Type} [∀ k, Group (H k)]
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x)
    (hSUeq : Held.heldSU n K τ hτ = StatedSU n (2 ^ 3) K)
    (θ : (∀ k, H k) →* GL (Fin n) K)
    (hθleGU : θ.range ≤ Held.heldGU n K τ hτ)
    {k : Fin r} (hperf : ⁅(commutator (H k)).map (MonoidHom.mulSingle H k),
        (commutator (H k)).map (MonoidHom.mulSingle H k)⁆ =
        (commutator (H k)).map (MonoidHom.mulSingle H k)) :
    ((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ ≤ StatedSU n (2 ^ 3) K := by
  have hleGU : ((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ ≤
      Held.heldGU n K τ hτ :=
    (Subgroup.map_le_range θ _).trans hθleGU
  have hperf' : ((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ =
      ⁅((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ,
        ((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ⁆ := by
    rw [← Subgroup.map_commutator, hperf]
  rw [hperf', ← hSUeq]
  exact Subgroup.commutator_le.mpr fun x hx y hy =>
    Held.commutatorElement_mem_heldSU (hleGU hx) (hleGU hy)

private theorem k329u3c_factor_quasisimple {K : Type} [Field K] {n r : ℕ}
    {H : Fin r → Type} [∀ k, Group (H k)]
    (θ : (∀ k, H k) →* GL (Fin n) K) (hθinj : Function.Injective θ)
    {k : Fin r} (hle : ((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ ≤
      StatedSU n (2 ^ 3) K)
    (hq : CFSG.Open.IsQuasisimple ↥(commutator (H k))) :
    CFSG.Open.IsQuasisimple
      ↥((((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ).subgroupOf
        (StatedSU n (2 ^ 3) K)) := by
  have hms : Function.Injective (MonoidHom.mulSingle H k) := Held.mulSingle_injective' k
  have e1 : ↥((((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ).subgroupOf
      (StatedSU n (2 ^ 3) K)) ≃*
      ↥(((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ) :=
    Subgroup.subgroupOfEquivOfLe hle
  have e2 : ↥(((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ) ≃*
      ↥((commutator (H k)).map (MonoidHom.mulSingle H k)) :=
    (Subgroup.equivMapOfInjective ((commutator (H k)).map (MonoidHom.mulSingle H k))
      θ hθinj).symm
  have e3 : ↥((commutator (H k)).map (MonoidHom.mulSingle H k)) ≃*
      ↥(commutator (H k)) :=
    (Subgroup.equivMapOfInjective (commutator (H k))
      (MonoidHom.mulSingle H k) hms).symm
  exact k329_isQuasisimple_of_mulEquiv ((e1.trans e2).trans e3).symm hq

private theorem k329u3c_factors_commute {K : Type} [Field K] {n r : ℕ}
    {H : Fin r → Type} [∀ k, Group (H k)]
    (θ : (∀ k, H k) →* GL (Fin n) K)
    (_hle : ∀ k, ((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ ≤
      StatedSU n (2 ^ 3) K)
    {i j : Fin r} (hij : i ≠ j) :
    ⁅(((commutator (H i)).map (MonoidHom.mulSingle H i)).map θ).subgroupOf
        (StatedSU n (2 ^ 3) K),
      (((commutator (H j)).map (MonoidHom.mulSingle H j)).map θ).subgroupOf
        (StatedSU n (2 ^ 3) K)⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have ha' : (a : GL (Fin n) K) ∈ ((commutator (H i)).map (MonoidHom.mulSingle H i)).map θ :=
    Subgroup.mem_subgroupOf.mp ha
  have hb' : (b : GL (Fin n) K) ∈ ((commutator (H j)).map (MonoidHom.mulSingle H j)).map θ :=
    Subgroup.mem_subgroupOf.mp hb
  obtain ⟨ta, hta, htaeq⟩ := Subgroup.mem_map.mp ha'
  obtain ⟨tb, htb, htbeq⟩ := Subgroup.mem_map.mp hb'
  obtain ⟨xa, hxa, rfl⟩ := Subgroup.mem_map.mp hta
  obtain ⟨xb, hxb, rfl⟩ := Subgroup.mem_map.mp htb
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← htaeq, ← htbeq]
  exact ((Pi.mulSingle_commute hij xa xb).map θ).eq.symm

private theorem k329u3c_centralizer_commutator_le_iSup {K : Type} [Field K] {n r : ℕ}
    {H : Fin r → Type} [∀ k, Group (H k)]
    (τ : K ≃+* K) (hτ : ∀ x, τ (τ x) = x)
    (hSUeq : Held.heldSU n K τ hτ = StatedSU n (2 ^ 3) K)
    (θ : (∀ k, H k) →* GL (Fin n) K)
    (hle : ∀ k, ((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ ≤
      StatedSU n (2 ^ 3) K)
    (x : ↥(StatedSU n (2 ^ 3) K))
    (hθrange : θ.range = Subgroup.centralizer ({(x : GL (Fin n) K)} : Set (GL (Fin n) K)) ⊓
      Held.heldGU n K τ hτ) :
    ⁅Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K)),
        Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K))⁆ ≤
      ⨆ k, (((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ).subgroupOf
        (StatedSU n (2 ^ 3) K) := by
  have hCmap : (Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K))).map
      (Subgroup.subtype (StatedSU n (2 ^ 3) K)) = StatedSU n (2 ^ 3) K ⊓ θ.range := by
    ext g
    constructor
    · intro hg
      obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hg
      refine Subgroup.mem_inf.mpr ⟨c.2, ?_⟩
      rw [hθrange]
      have hcGU : (c : GL (Fin n) K) ∈ Held.heldGU n K τ hτ := by
        have hcSU : (c : GL (Fin n) K) ∈ Held.heldSU n K τ hτ := by
          rw [hSUeq]; exact c.2
        exact (Subgroup.mem_inf.mp hcSU).1
      exact Subgroup.mem_inf.mpr ⟨(k329u3c_mem_centralizer_subtype
          (Subgroup.subtype (StatedSU n (2 ^ 3) K))
          (Subgroup.subtype_injective (StatedSU n (2 ^ 3) K)) x c).mp hc, hcGU⟩
    · intro hg
      rw [Subgroup.mem_inf] at hg
      obtain ⟨hgH, hgrange⟩ := hg
      rw [hθrange] at hgrange
      refine Subgroup.mem_map.mpr ⟨⟨g, hgH⟩, ?_, rfl⟩
      exact (k329u3c_mem_centralizer_subtype (Subgroup.subtype (StatedSU n (2 ^ 3) K))
        (Subgroup.subtype_injective (StatedSU n (2 ^ 3) K)) x ⟨g, hgH⟩).mpr hgrange.1
  have key : (⁅Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K)),
      Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K))⁆).map
        (Subgroup.subtype (StatedSU n (2 ^ 3) K)) ≤
      (⨆ k, (((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ).subgroupOf
        (StatedSU n (2 ^ 3) K)).map (Subgroup.subtype (StatedSU n (2 ^ 3) K)) := by
    rw [Subgroup.map_commutator, hCmap]
    calc ⁅StatedSU n (2 ^ 3) K ⊓ θ.range, StatedSU n (2 ^ 3) K ⊓ θ.range⁆ ≤
          ⁅θ.range, θ.range⁆ := Subgroup.commutator_mono inf_le_right inf_le_right
      _ = Subgroup.map θ (⁅(⊤ : Subgroup (∀ k, H k)), ⊤⁆) := by
          rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator]
      _ ≤ ⨆ k, (((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ) :=
          k329u3c_map_commutator_top_le θ
      _ ≤ (⨆ k, (((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ).subgroupOf
            (StatedSU n (2 ^ 3) K)).map (Subgroup.subtype (StatedSU n (2 ^ 3) K)) := by
          rw [Subgroup.map_iSup]
          refine iSup_le fun k => ?_
          refine le_trans ?_ (le_iSup (fun j =>
            ((((commutator (H j)).map (MonoidHom.mulSingle H j)).map θ).subgroupOf
              (StatedSU n (2 ^ 3) K)).map (Subgroup.subtype (StatedSU n (2 ^ 3) K))) k)
          rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hle k)]
  exact (Subgroup.map_le_map_iff_of_injective
    (Subgroup.subtype_injective (StatedSU n (2 ^ 3) K))).mp key


section K329u3fPrivate

open CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held
open scoped commutatorElement

private theorem k329u3f_blockSub_data {Γ : Type} [Group Γ] {Q : ℕ}
    (hSU0 : SUComponentsTrivial) (hSL0 : SLComponentsTrivial)
    (hΓ : UnitaryOrLinearBlock Q Γ) :
    ∃ S : Subgroup Γ, (∀ x y : Γ, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧
      ((∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M)
          (hτ : ∀ x, τ (τ x) = x), Odd d ∧ (∀ x, τ x = x ^ (Q ^ d)) ∧
          Nat.card M = (Q ^ d) ^ 2 ∧ Nonempty (S ≃* heldSU a M τ hτ)) ∨
       (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M),
          Nat.card M = Q ^ (2 * e) ∧ Nonempty (S ≃* StatedSL b M))) := by
  have hSU : ∀ (a Q : ℕ) (M : Type) [Field M] [Finite M] (τ : M ≃+* M) (hτ : ∀ x, τ (τ x) = x),
      Nat.card M = Q ^ 2 → (∀ x, τ x = x ^ Q) →
        ∀ X : Subgroup (heldSU a M τ hτ), IsComponentOf X ⊤ → X = ⊤ := hSU0
  have hSL : ∀ (d : ℕ) (K : Type) [Field K] [Finite K] (X : Subgroup (StatedSL d K)),
      IsComponentOf X ⊤ → X = ⊤ := hSL0
  rcases hΓ with ⟨a, d, M, hMF, hMfin, τ, hτ, hodd, hτQ, hcard, ⟨ε⟩⟩ |
      ⟨b, e, M, hMF, hMfin, hcard, ⟨ε⟩⟩
  · let f : Γ →* GL (Fin a) M := (heldGU a M τ hτ).subtype.comp ε.toMonoidHom
    have hf : Function.Injective f := fun x y h => ε.injective (Subtype.ext h)
    have hle : heldSU a M τ hτ ≤ f.range := by
      intro x hx
      have hxG : x ∈ heldGU a M τ hτ := (Subgroup.mem_inf.mp hx).1
      refine MonoidHom.mem_range.mpr ⟨ε.symm ⟨x, hxG⟩, ?_⟩
      simp [f]
    refine ⟨(heldSU a M τ hτ).comap f, ?_, ?_,
      Or.inl ⟨a, d, M, hMF, hMfin, τ, hτ, hodd, hτQ, hcard, ?_⟩⟩
    · intro x y
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact commutatorElement_mem_heldSU (ε x).2 (ε y).2
    · exact triv_comap f hf _ hle (fun X hX => hSU a (Q ^ d) M τ hτ hcard hτQ X hX)
    · obtain ⟨eS⟩ := comap_equiv_of_injective_le_range f hf _ hle
      exact ⟨eS⟩
  · let f : Γ →* GL (Fin b) M := ε.toMonoidHom
    have hf : Function.Injective f := ε.injective
    have hle : StatedSL b M ≤ f.range := by
      intro x _
      exact MonoidHom.mem_range.mpr ⟨ε.symm x, by simp [f]⟩
    refine ⟨(StatedSL b M).comap f, ?_, ?_,
      Or.inr ⟨b, e, M, hMF, hMfin, hcard, ?_⟩⟩
    · intro x y
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact commutatorElement_mem_statedSL _ _
    · exact triv_comap f hf _ hle (fun X hX => hSL b M X hX)
    · obtain ⟨eS⟩ := comap_equiv_of_injective_le_range f hf _ hle
      exact ⟨eS⟩

private theorem k329u3f_component_data {Q n : ℕ} {L : Type} [Field L] [Finite L]
    (τ : L ≃+* L) (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (hL : Nat.card L = Q ^ 2) (s : GL (Fin n) L) (hs : s ∈ heldSU n L τ hτ)
    (hord : (orderOf s : L) ≠ 0) (J : Subgroup (GL (Fin n) L))
    (hJ : IsComponentOf J (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ)) :
    (∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ' : M ≃+* M)
        (hτ' : ∀ x, τ' (τ' x) = x), Odd d ∧ (∀ x, τ' x = x ^ (Q ^ d)) ∧
        Nat.card M = (Q ^ d) ^ 2 ∧ 2 ≤ a ∧
        Nonempty (J ≃* heldSU a M τ' hτ')) ∨
    (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M), 2 ≤ b ∧
        Nat.card M = Q ^ (2 * e) ∧ Nonempty (J ≃* StatedSL b M)) := by
  obtain ⟨r, H, hgrp, hfinH, hblk, ⟨ε⟩⟩ :=
    unitaryCentralizerDecomposition_holds Q n L τ hτ s hL hτQ hs hord
  have hbl : ∀ k, ∃ S : Subgroup (H k), (∀ x y : H k, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧
      ((∃ (a d : ℕ) (M : Type) (_ : Field M) (_ : Finite M) (τ : M ≃+* M)
          (hτ : ∀ x, τ (τ x) = x), Odd d ∧ (∀ x, τ x = x ^ (Q ^ d)) ∧
          Nat.card M = (Q ^ d) ^ 2 ∧ Nonempty (S ≃* heldSU a M τ hτ)) ∨
        (∃ (b e : ℕ) (M : Type) (_ : Field M) (_ : Finite M),
          Nat.card M = Q ^ (2 * e) ∧ Nonempty (S ≃* StatedSL b M))) :=
    fun k => k329u3f_blockSub_data SUComponentsTrivial_holds SLComponentsTrivial_holds (hblk k)
  choose S hS hSt hty using hbl
  let C : Subgroup (GL (Fin n) L) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ
  let ψ : (∀ k, H k) →* GL (Fin n) L := C.subtype.comp ε.symm.toMonoidHom
  have hψinj : Function.Injective ψ := fun x y h => ε.symm.injective (Subtype.ext h)
  have hrange : ψ.range = C := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩
      exact (ε.symm w).2
    · intro hx
      refine ⟨ε ⟨x, hx⟩, ?_⟩
      simp [ψ]
  have hJle : J ≤ ψ.range := by
    rw [hrange]; exact hJ.1
  have hJmap : (J.comap ψ).map ψ = J := by
    rw [Subgroup.map_comap_eq, inf_eq_right.mpr hJle]
  have hJ'top : IsComponentOf (J.comap ψ) ⊤ := by
    apply isComponentOf_of_map_injective ψ hψinj
    rw [hJmap, ← MonoidHom.range_eq_map, hrange]; exact hJ
  obtain ⟨k, hk⟩ := component_eq_factor_image S hS hSt hJ'top
  have hJeq : J = ((S k).map (MonoidHom.mulSingle H k)).map ψ := by
    rw [← hk, hJmap]
  have hms := mulSingle_injective' (H := H) k
  obtain ⟨e1⟩ : Nonempty (↥J ≃* ↥(S k)) := ⟨(MulEquiv.subgroupCongr hJeq).trans
    (((Subgroup.equivMapOfInjective _ ψ hψinj).symm).trans
      ((Subgroup.equivMapOfInjective (S k) (MonoidHom.mulSingle H k) hms).symm))⟩
  rcases hty k with ⟨a, d, M, hMF, hMfin, τM, hτM, hodd, hτMQ, hMcard, ⟨eS⟩⟩ |
      ⟨b, e, M, hMF, hMfin, hMcard, ⟨eS⟩⟩
  · let e : ↥J ≃* ↥(heldSU a M τM hτM) := e1.trans eS
    by_cases ha2 : 2 ≤ a
    · exact Or.inl ⟨a, d, M, hMF, hMfin, τM, hτM, hodd, hτMQ, hMcard, ha2, ⟨e⟩⟩
    · exact absurd hJ.2.2 (not_isQuasisimple_of_mulEquiv e fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one (by omega) (x : GL (Fin a) M) (y : GL (Fin a) M)))
  · let eiso : ↥J ≃* ↥(StatedSL b M) := e1.trans eS
    by_cases hb2 : 2 ≤ b
    · exact Or.inr ⟨b, e, M, hMF, hMfin, hb2, hMcard, ⟨eiso⟩⟩
    · exact absurd hJ.2.2 (not_isQuasisimple_of_mulEquiv eiso fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one (by omega) (x : GL (Fin b) M) (y : GL (Fin b) M)))

end K329u3fPrivate

section K329u3fSetup

open CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held

private theorem k329u3f_order {n r e : ℕ} (hadm : StatedLieAdmissible .PSU n r e) (hr : r ≠ 3)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = (r ^ e) ^ 2)
    (x : ↥(StatedSU n (r ^ e) K)) (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (r ^ e) K)) :
    (orderOf ((x : GL (Fin n) K)) : K) ≠ 0 := by
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r e K :=
    ⟨hadm.1, hadm.2.1, by rw [hK]; rw [show (2 : ℕ) * e = e * 2 by ring]; rw [pow_mul]⟩
  let τ : K ≃+* K := RingEquiv.ofRingHom hUF.bar hUF.bar
    (RingHom.ext hUF.bar_bar) (RingHom.ext hUF.bar_bar)
  have hτ : ∀ c, τ (τ c) = c := hUF.bar_bar
  have hτQ : ∀ c, τ c = c ^ (r ^ e) := by
    intro c; simpa [τ] using hUF.bar_apply c
  have hSUeq : heldSU n K τ hτ = StatedSU n (r ^ e) K := hct_heldSU_eq_statedSU hτQ
  let s : GL (Fin n) K := (x : GL (Fin n) K)
  have hs : s ∈ heldSU n K τ hτ := by rw [hSUeq]; exact x.2
  have hs3 : s ^ 3 ∈ StatedScalars (Fin n) K := by
    have h := Subgroup.mem_subgroupOf.mp hx3
    simpa [s, K329Zh] using h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hs3
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (r ^ e) K := by
    rw [hc]
    rw [hSUeq] at hs
    exact pow_mem hs 3
  have hcq : c ^ (r ^ e + 1) = 1 := by
    have hn : 1 ≤ n := le_trans (by norm_num : 1 ≤ 3) hadm.2.2.1
    have h := (CFSG.LinearGroups.unitary_scalar_kernel (p := r) (f := e) hadm.1 hK hn).2.1 c
    exact (h.mp hsc).2
  have hs_pow : s ^ (3 * (r ^ e + 1)) = 1 := by
    calc s ^ (3 * (r ^ e + 1)) = (s ^ 3) ^ (r ^ e + 1) := by rw [pow_mul]
      _ = (Matrix.GeneralLinearGroup.scalar (Fin n) c) ^ (r ^ e + 1) := by rw [hc]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) (c ^ (r ^ e + 1)) := by rw [map_pow]
      _ = Matrix.GeneralLinearGroup.scalar (Fin n) 1 := by rw [hcq]
      _ = 1 := map_one _
  have horder_dvd : orderOf s ∣ 3 * (r ^ e + 1) := orderOf_dvd_of_pow_eq_one hs_pow
  have hrprime : r.Prime := hadm.1
  have he1 : 1 ≤ e := hadm.2.1
  have hr_not_dvd : ¬ r ∣ 3 * (r ^ e + 1) := by
    intro h
    rcases (hrprime.dvd_mul).mp h with h3 | hq1
    · exact hr ((Nat.prime_dvd_prime_iff_eq hrprime Nat.prime_three).mp h3)
    · have hre : r ∣ r ^ e := by
        obtain ⟨k, rfl⟩ := he1.dest
        rw [pow_add, pow_one]; exact dvd_mul_right r _
      have h1 : r ∣ 1 := by
        have := Nat.dvd_sub hq1 hre
        rwa [show r ^ e + 1 - r ^ e = 1 by omega] at this
      exact hrprime.ne_one (Nat.dvd_one.mp h1)
  have hrn : ¬ r ∣ orderOf s := fun h => hr_not_dvd (h.trans horder_dvd)
  have : Fact r.Prime := ⟨hrprime⟩
  have : CharP K r := hUF.charP
  have hord : (orderOf s : K) ≠ 0 :=
    fun h => hrn ((CharP.cast_eq_zero_iff K r (orderOf s)).mp h)
  simpa [s] using hord

end K329u3fSetup

section K329u3fReduction

open CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held

private theorem k329u3f_reduction (n r e : ℕ) (hadm : StatedLieAdmissible .PSU n r e) (hr : r ≠ 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (r ^ e) ^ 2)
    (x : ↥(StatedSU n (r ^ e) K)) (hx : x ∉ K329Zh (StatedSU n (r ^ e) K))
    (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (r ^ e) K))
    (Q : Subgroup ↥(StatedSU n (r ^ e) K)) (hQL : Q ≤ K329Lres x)
    (hQn : (Q.subgroupOf (K329Lres x)).Normal) (hQq : CFSG.Open.IsQuasisimple ↥Q)
    (hQcard : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 504) :
    r ^ e = 8 ∨ (r = 2 ∧ e = 1) := by
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData r e K :=
    ⟨hadm.1, hadm.2.1, by rw [hK]; rw [show (2 : ℕ) * e = e * 2 by ring]; rw [pow_mul]⟩
  let τ : K ≃+* K := RingEquiv.ofRingHom hUF.bar hUF.bar
    (RingHom.ext hUF.bar_bar) (RingHom.ext hUF.bar_bar)
  have hτ : ∀ c, τ (τ c) = c := hUF.bar_bar
  have hτQ : ∀ c, τ c = c ^ (r ^ e) := by
    intro c; simpa [τ] using hUF.bar_apply c
  have hSUeq : heldSU n K τ hτ = StatedSU n (r ^ e) K := hct_heldSU_eq_statedSU hτQ
  let s : GL (Fin n) K := (x : GL (Fin n) K)
  have hs : s ∈ heldSU n K τ hτ := by rw [hSUeq]; exact x.2
  have hord : (orderOf s : K) ≠ 0 := k329u3f_order hadm hr hK x hx3
  let D : Subgroup ↥(StatedSU n (r ^ e) K) :=
    Subgroup.centralizer ({x} : Set ↥(StatedSU n (r ^ e) K))
  have hDnorm : ((K329Lres x).subgroupOf D).Normal := by
    change ((K329Res D).subgroupOf D).Normal
    exact k329_res_normal (C := D) (D := D) le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hQcompD : IsComponentOf Q D :=
    ⟨hQL.trans (Subgroup.map_subtype_le _), IsSubnormal.step hQL hQn
      (IsSubnormal.step (Subgroup.map_subtype_le _) hDnorm (IsSubnormal.refl D)), hQq⟩
  let Q' : Subgroup (GL (Fin n) K) := Q.map (StatedSU n (r ^ e) K).subtype
  let CC : Subgroup (GL (Fin n) K) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ heldGU n K τ hτ
  have hQ'q : CFSG.Open.IsQuasisimple ↥Q' :=
    k329_isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective Q (StatedSU n (r ^ e) K).subtype
        (Subgroup.subtype_injective _)) hQq
  have hQ'comp : IsComponentOf Q' CC := by
    let D' : Subgroup (GL (Fin n) K) := D.map (StatedSU n (r ^ e) K).subtype
    have hD'eq : D' = Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ StatedSU n (r ^ e) K := by
      ext g; constructor
      · intro hg
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, y.2⟩
        intro z hz
        rw [Set.mem_singleton_iff] at hz; subst hz
        have h := (Subgroup.mem_centralizer_iff.mp hy) x (Set.mem_singleton x)
        exact congrArg Subtype.val h
      · rintro ⟨hg1, hg2⟩
        refine Subgroup.mem_map.mpr ⟨⟨g, hg2⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
        intro z hz
        rw [Set.mem_singleton_iff] at hz; subst hz
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hg1 s (Set.mem_singleton s)
    have hD'eq2 : D' = CC ⊓ StatedSL n K := by
      rw [hD'eq]
      ext g; constructor
      · rintro ⟨hg1, hg2⟩
        rw [← hSUeq] at hg2
        exact ⟨⟨hg1, (Subgroup.mem_inf.mp hg2).1⟩, (Subgroup.mem_inf.mp hg2).2⟩
      · rintro ⟨⟨hg1, hg2⟩, hg3⟩
        exact ⟨hg1, by rw [← hSUeq]; exact Subgroup.mem_inf.mpr ⟨hg2, hg3⟩⟩
    have hD'leC : D' ≤ CC := by rw [hD'eq2]; exact inf_le_left
    have hD'normC : (D'.subgroupOf CC).Normal := by
      rw [hD'eq2, Subgroup.inf_subgroupOf_left]
      infer_instance
    have hQ'compD' : IsComponentOf Q' D' := by
      have := isComponentOf_map_of_injective (StatedSU n (r ^ e) K).subtype
        (Subgroup.subtype_injective _) (L := Q) (K := D) hQcompD
      simpa [Q', D'] using this
    exact ⟨hQ'compD'.1.trans hD'leC,
      IsSubnormal.trans hQ'compD'.2.1 (IsSubnormal.step hD'leC hD'normC (IsSubnormal.refl CC)),
      hQ'q⟩
  have hQ'card : Nat.card (↥Q' ⧸ Subgroup.center ↥Q') = 504 := by
    let e0 : ↥Q ≃* ↥Q' := Subgroup.equivMapOfInjective Q _ (Subgroup.subtype_injective _)
    have hc := Subgroup.map_center_eq e0
    exact (Nat.card_congr (QuotientGroup.congr _ _ e0 hc).toEquiv).symm.trans hQcard
  rcases k329u3f_component_data τ hτ hτQ hK s hs hord Q' hQ'comp with
    ⟨a, d, M, hMF, hMfin, τ', hτ', hodd, hτ'Q, hMcard, ha2, ⟨eJ⟩⟩ |
    ⟨b, e', M, hMF, hMfin, hb2, hMcard, ⟨eJ⟩⟩
  ·
    let : Field M := hMF
    let : Finite M := hMfin
    have hMcard' : Nat.card M = (r ^ (e * d)) ^ 2 := by
      rw [hMcard]; congr 1; rw [← pow_mul]
    have hSUq : CFSG.Open.IsQuasisimple ↥(heldSU a M τ' hτ') :=
      k329_isQuasisimple_of_mulEquiv eJ hQ'q
    have : Fact r.Prime := ⟨hadm.1⟩
    have : Fintype M := Fintype.ofFinite M
    have : CharP M r := charP_of_card_eq_prime_pow (p := r) (f := 2 * (e * d))
      (by rw [← Nat.card_eq_fintype_card, hMcard', pow_mul]; ring_nf)
    by_cases ha : a = 2
    ·
      subst ha
      have hτ'Q2 : ∀ z, τ' z = z ^ (r ^ (e * d)) := by
        intro z; rw [hτ'Q z, ← pow_mul]
      have hSU2 : heldSU 2 M τ' hτ' = StatedSU 2 (r ^ (e * d)) M :=
        hct_heldSU_eq_statedSU hτ'Q2
      let F := CFSG.LieType.Steinberg.fixedSubfield M r (e * d)
      obtain ⟨e2⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
        (K := M) (r := r) (f := e * d) hMcard'
      let eQSL : ↥Q' ≃* ↥(StatedSL 2 F) :=
        (eJ.trans (MulEquiv.subgroupCongr hSU2)).trans
          (e2.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F))
      obtain ⟨eQc⟩ := nonempty_quotientCenter_equiv_statedProj eQSL
      have hY : Nat.card (StatedProj (StatedSL 2 F)) = 504 := by
        rw [← Nat.card_congr eQc.toEquiv, hQ'card]
      have hFcard : Nat.card F = r ^ (e * d) :=
        CFSG.LieType.Steinberg.card_fixedSubfield hMcard'
      have hSLq : CFSG.Open.IsQuasisimple ↥(StatedSL 2 F) :=
        k329_isQuasisimple_of_mulEquiv eQSL hQ'q
      have hF4 : 4 ≤ Nat.card F := by
        by_contra hlt
        push Not at hlt
        have h2 : Nat.card F = 2 ∨ Nat.card F = 3 := by
          have := Finite.one_lt_card (α := F); omega
        rcases h2 with h2 | h2
        · have hc := CFSG.Open.StatedAPI.card_statedSL_two F
          have hs2 : Group.IsSolvable ↥(StatedSL 2 F) :=
            hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1) (b := 1)
              Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc, h2]; norm_num)
          have : Nontrivial (↥(StatedSL 2 F) ⧸ Subgroup.center ↥(StatedSL 2 F)) :=
            hSLq.2.toNontrivial
          have : Nontrivial ↥(StatedSL 2 F) :=
            (QuotientGroup.mk_surjective (s := Subgroup.center ↥(StatedSL 2 F))).nontrivial
          have : Group.IsPerfect ↥(StatedSL 2 F) := Group.isPerfect_def.mpr hSLq.1
          exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL 2 F)) hs2
        · have hc := CFSG.Open.StatedAPI.card_statedSL_two F
          have hs2 : Group.IsSolvable ↥(StatedSL 2 F) :=
            hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 1)
              Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc, h2]; norm_num)
          have : Nontrivial (↥(StatedSL 2 F) ⧸ Subgroup.center ↥(StatedSL 2 F)) :=
            hSLq.2.toNontrivial
          have : Nontrivial ↥(StatedSL 2 F) :=
            (QuotientGroup.mk_surjective (s := Subgroup.center ↥(StatedSL 2 F))).nontrivial
          have : Group.IsPerfect ↥(StatedSL 2 F) := Group.isPerfect_def.mpr hSLq.1
          exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL 2 F)) hs2
      have hd1 : 1 ≤ d := by obtain ⟨k, hk⟩ := hodd; omega
      have he1 : 1 ≤ e := hadm.2.1
      have hAdm : StatedLieAdmissible .PSL 2 r (e * d) := by
        refine ⟨hadm.1, by simpa using Nat.mul_le_mul he1 hd1, by norm_num, ?_, ?_⟩
        · intro h
          have h2 : r ^ (e * d) = 2 := congrArg Prod.snd h
          rw [← hFcard] at h2; omega
        · intro h
          have h3 : r ^ (e * d) = 3 := congrArg Prod.snd h
          rw [← hFcard] at h3; omega
      have hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSL 2 F)) .PSL 2 r (e * d) :=
        Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
          ⟨hAdm, F, inferInstance, inferInstance, hFcard, ⟨MulEquiv.refl _⟩⟩⟩
      obtain ⟨-, -, hrf⟩ := k329_S2_order504 (by norm_num : (2 : ℕ) ≠ 0) hLie hY
      have hr2 : r = 2 := by
        have hdvd : r ∣ 8 := by
          rw [← hrf]
          exact dvd_pow_self r (Nat.mul_ne_zero (by omega : e ≠ 0) (by omega : d ≠ 0))
        have hdvd2 : r ∣ 2 := by
          rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at hdvd
          exact hadm.1.dvd_of_dvd_pow hdvd
        exact (Nat.prime_dvd_prime_iff_eq hadm.1 Nat.prime_two).mp hdvd2
      have hed : e * d = 3 := by
        have h : r ^ (e * d) = 2 ^ 3 := by rw [hrf]; norm_num
        rw [hr2] at h
        exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
      rcases (Nat.dvd_prime Nat.prime_three).mp ⟨d, hed.symm⟩ with he | he
      · exact Or.inr ⟨hr2, he⟩
      · exact Or.inl (by rw [hr2, he]; norm_num)
    ·
      have ha3 : 3 ≤ a := by omega
      have hτ'Q3 : ∀ z, τ' z = z ^ (r ^ (e * d)) := by
        intro z; rw [hτ'Q z, ← pow_mul]
      have hSUeq' : heldSU a M τ' hτ' = StatedSU a (r ^ (e * d)) M :=
        hct_heldSU_eq_statedSU hτ'Q3
      have hnot32 : (a, r ^ (e * d)) ≠ (3, 2) := by
        intro h
        have ha' : a = 3 := congrArg Prod.fst h
        have hq : r ^ (e * d) = 2 := congrArg Prod.snd h
        have hM4 : Nat.card M = (2 ^ 1) ^ 2 := by rw [hMcard', hq]; norm_num
        have hc : Nat.card (StatedSU 3 (2 ^ 1) M) = 216 := by
          rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two hM4]; norm_num
        have hs2 : Group.IsSolvable ↥(StatedSU 3 (2 ^ 1) M) :=
          hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 3)
            Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc]; norm_num)
        have hs3 : Group.IsSolvable ↥(StatedSU a (r ^ (e * d)) M) := by
          subst ha'
          rw [hq]
          simpa using hs2
        have hsol : Group.IsSolvable ↥(heldSU a M τ' hτ') := by
          rw [hSUeq']; exact hs3
        have : Nontrivial (↥(heldSU a M τ' hτ') ⧸ Subgroup.center ↥(heldSU a M τ' hτ')) :=
          hSUq.2.toNontrivial
        have : Nontrivial ↥(heldSU a M τ' hτ') :=
          (QuotientGroup.mk_surjective (s := Subgroup.center ↥(heldSU a M τ' hτ'))).nontrivial
        have : Group.IsPerfect ↥(heldSU a M τ' hτ') := Group.isPerfect_def.mpr hSUq.1
        exact Group.IsPerfect.not_isSolvable (G := ↥(heldSU a M τ' hτ')) hsol
      have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := M)
        (p := r) (f := e * d) hMcard' ha3 hnot32).2
      have hcenter : Subgroup.center ↥(heldSU a M τ' hτ') =
          (StatedScalars (Fin a) M).subgroupOf (heldSU a M τ' hτ') := by
        rw [hSUeq']
        exact hZ
      let eQc : ↥Q' ⧸ Subgroup.center ↥Q' ≃* StatedProj (heldSU a M τ' hτ') :=
        (QuotientGroup.congr (Subgroup.center ↥Q') (Subgroup.center ↥(heldSU a M τ' hτ')) eJ
          (Subgroup.map_center_eq eJ)).trans
          (QuotientGroup.quotientMulEquivOfEq hcenter)
      have hY : Nat.card (StatedProj (StatedSU a (r ^ (e * d)) M)) = 504 := by
        rw [← hSUeq']
        exact (Nat.card_congr eQc.toEquiv).symm.trans hQ'card
      have hd1 : 1 ≤ d := by obtain ⟨k, hk⟩ := hodd; omega
      have he1 : 1 ≤ e := hadm.2.1
      have hAdm : StatedLieAdmissible .PSU a r (e * d) :=
        ⟨hadm.1, by simpa using Nat.mul_le_mul he1 hd1, ha3, hnot32⟩
      have hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSU a (r ^ (e * d)) M))
          .PSU a r (e * d) :=
        Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
          ⟨hAdm, M, hMF, hMfin, hMcard', ⟨MulEquiv.refl _⟩⟩⟩
      obtain ⟨hPSL, -, -⟩ := k329_S2_order504 (by omega : a ≠ 0) hLie hY
      exact absurd hPSL (by decide)
  ·
    let : Field M := hMF
    let : Finite M := hMfin
    have he1 : 1 ≤ e := hadm.2.1
    have hSLq : CFSG.Open.IsQuasisimple ↥(StatedSL b M) :=
      k329_isQuasisimple_of_mulEquiv eJ hQ'q
    have hMcard' : Nat.card M = r ^ (2 * e * e') := by
      rw [hMcard, show 2 * e * e' = e * (2 * e') by ring, ← pow_mul]
    have he' : 1 ≤ e' := by
      by_contra hlt
      have h0 : e' = 0 := by omega
      have h1 : Nat.card M = 1 := by rw [hMcard, h0]; simp
      have := Finite.one_lt_card (α := M); omega
    have hnot22 : (b, Nat.card M) ≠ (2, 2) := by
      intro h
      have hb : b = 2 := congrArg Prod.fst h
      have hM2 : Nat.card M = 2 := congrArg Prod.snd h
      have hc := CFSG.Open.StatedAPI.card_statedSL_two M
      have hs2 : Group.IsSolvable ↥(StatedSL 2 M) :=
        hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc, hM2]; norm_num)
      have hb' : Group.IsSolvable ↥(StatedSL b M) := by
        rw [hb]; exact hs2
      have : Nontrivial (↥(StatedSL b M) ⧸ Subgroup.center ↥(StatedSL b M)) :=
        hSLq.2.toNontrivial
      have : Nontrivial ↥(StatedSL b M) :=
        (QuotientGroup.mk_surjective (s := Subgroup.center ↥(StatedSL b M))).nontrivial
      have : Group.IsPerfect ↥(StatedSL b M) := Group.isPerfect_def.mpr hSLq.1
      exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL b M)) hb'
    have hnot23 : (b, Nat.card M) ≠ (2, 3) := by
      intro h
      have hb : b = 2 := congrArg Prod.fst h
      have hM3 : Nat.card M = 3 := congrArg Prod.snd h
      have hc := CFSG.Open.StatedAPI.card_statedSL_two M
      have hs2 : Group.IsSolvable ↥(StatedSL 2 M) :=
        hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc, hM3]; norm_num)
      have hb' : Group.IsSolvable ↥(StatedSL b M) := by
        rw [hb]; exact hs2
      have : Nontrivial (↥(StatedSL b M) ⧸ Subgroup.center ↥(StatedSL b M)) :=
        hSLq.2.toNontrivial
      have : Nontrivial ↥(StatedSL b M) :=
        (QuotientGroup.mk_surjective (s := Subgroup.center ↥(StatedSL b M))).nontrivial
      have : Group.IsPerfect ↥(StatedSL b M) := Group.isPerfect_def.mpr hSLq.1
      exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL b M)) hb'
    obtain ⟨eQc⟩ := nonempty_quotientCenter_equiv_statedProj eJ
    have hY : Nat.card (StatedProj (StatedSL b M)) = 504 := by
      rw [← Nat.card_congr eQc.toEquiv, hQ'card]
    have hAdm : StatedLieAdmissible .PSL b r (2 * e * e') :=
      ⟨hadm.1, by simpa using Nat.mul_le_mul (Nat.mul_le_mul (by norm_num : 1 ≤ 2) he1) he', hb2,
        by rw [← hMcard']; exact hnot22, by rw [← hMcard']; exact hnot23⟩
    have hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSL b M)) .PSL b r (2 * e * e') :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
        ⟨hAdm, M, hMF, hMfin, hMcard', ⟨MulEquiv.refl _⟩⟩⟩
    obtain ⟨-, -, hrf⟩ := k329_S2_order504 (by omega : b ≠ 0) hLie hY
    have hr2 : r = 2 := by
      have hdvd : r ∣ 8 := by
        rw [← hrf]
        exact dvd_pow_self r (Nat.mul_ne_zero (Nat.mul_ne_zero (by norm_num : (2 : ℕ) ≠ 0)
          (by omega : e ≠ 0)) (by omega : e' ≠ 0))
      have hdvd2 : r ∣ 2 := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num] at hdvd
        exact hadm.1.dvd_of_dvd_pow hdvd
      exact (Nat.prime_dvd_prime_iff_eq hadm.1 Nat.prime_two).mp hdvd2
    have h3 : 2 * e * e' = 3 := by
      have h : r ^ (2 * e * e') = 2 ^ 3 := by rw [hrf]; norm_num
      rw [hr2] at h
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
    have h2dvd : 2 ∣ 3 := ⟨e * e', by rw [← h3]; ring⟩
    exact absurd h2dvd (by norm_num)

end K329u3fReduction

section K329q2Private

open CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.LieType.SemisimpleCentralizers.HeldUCD
open CFSG.LocalAnalysis.ComponentInitial
open Polynomial
open scoped commutatorElement

private theorem k329q2_selfDual_block_iso {L : Type} [Field L] [Finite L] {n m Q : ℕ}
    {τ : L ≃+* L} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {aa bb : L[X] → L[X]}
    {f : L[X]} [Fact (Irreducible f)]
    [Fact (∀ x ∈ Vf s bb F f, Matrix.mulVec (Polynomial.aeval s f) x = 0)]
    (H : PrimaryHyp τ s m F aa bb) (hQ : Nat.card L = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q)
    (hf : f ∈ F) (hPf : Pmat s bb F f ≠ 0)
    (hsa : adjM τ (Pmat s bb F f) = Pmat s bb F f) :
    ∃ (ρE : AdjoinRoot f ≃+* AdjoinRoot f) (hρE : ∀ x, ρE (ρE x) = x),
      Nat.card (AdjoinRoot f) = (Q ^ f.natDegree) ^ 2 ∧
      (∀ x, ρE x = x ^ (Q ^ f.natDegree)) ∧
      Nonempty (↥(unitaryBlock τ s bb F f) ≃* heldGU (Module.finrank (AdjoinRoot f) (Vf s bb F f))
        (AdjoinRoot f) ρE hρE) := by
  classical
  have hf0 : f ≠ 0 := (Fact.out : Irreducible f).ne_zero
  have hdiv : f ∣ starP τ m f := dvd_starP_of_self_dual H hf hPf hsa
  have hdvd : f ∣ (X ^ m - 1 : L[X]) := by
    rw [← H.hprod]
    exact Finset.dvd_prod_of_mem _ hf
  have hσσ : ∀ x, sigmaK τ m hdiv (sigmaK τ m hdiv x) = x :=
    sigmaK_sigmaK τ H.hτ H.hm hdiv hdvd
  have hσL : ∀ l : L, sigmaK τ m hdiv (algebraMap L (AdjoinRoot f) l) =
      algebraMap L (AdjoinRoot f) (τ l) := fun l => sigmaK_of τ m hdiv l
  have : Module.Finite L (AdjoinRoot f) := (H.hmon f hf).finite_adjoinRoot
  have : Finite (AdjoinRoot f) :=
    Finite.of_equiv (Fin (Module.finrank L (AdjoinRoot f)) → L)
      (Module.finBasis L (AdjoinRoot f)).equivFun.toEquiv.symm
  let σE : AdjoinRoot f ≃+* AdjoinRoot f := invEquiv (sigmaK τ m hdiv) hσσ
  obtain ⟨p, e, hp, he1, hQe, hodd, hcard, hsig⟩ :=
    sigma_eq_frobenius_pow hQ τ hτQ σE hσL hσσ
  set k := Module.finrank L (AdjoinRoot f) with hk
  have hbar_card : Nat.card (AdjoinRoot f) = p ^ (2 * (e * k)) := by
    rw [hcard, hQe, ← pow_mul]
    congr 1
    ring
  have hUFD : UnitaryFieldData p (e * k) (AdjoinRoot f) :=
    ⟨hp, Nat.mul_pos he1 hodd.pos, hbar_card⟩
  have hbar : ∀ x, hUFD.bar x = sigmaK τ m hdiv x := by
    intro x
    rw [UnitaryFieldData.bar_apply]
    have h1 := hsig x
    rw [hQe, ← pow_mul] at h1
    exact h1.symm
  have hρE : ∀ x, hUFD.bar (hUFD.bar x) = x := hUFD.bar_bar
  have hρL : ∀ l : L, hUFD.bar (algebraMap L (AdjoinRoot f) l) =
      algebraMap L (AdjoinRoot f) (τ l) := fun l => by
    rw [hbar]
    exact hσL l
  have hherm : ∀ x y : Vf s bb F f, τ (hW τ s bb F f x y) = hW τ s bb F f y x := by
    intro x y
    rw [hW_apply, hW_apply]
    exact hfm_symm τ H.hτ _ _
  have hadj : ∀ (c : AdjoinRoot f) (x y : Vf s bb F f),
      hW τ s bb F f (c • x) y = hW τ s bb F f x (hUFD.bar c • y) := by
    intro c x y
    rw [hbar]
    exact hW_smul_adj H hdiv c x y
  obtain ⟨B, hsymm, hsep, hrep⟩ :=
    exists_trace_form hUFD.bar (τ : L →+* L) hρE hρL (hW τ s bb F f) hherm hadj
      (hW_nondeg H hf hsa)
  have : Module.Finite L (Vf s bb F f) := inferInstance
  have : FiniteDimensional (AdjoinRoot f) (Vf s bb F f) :=
    Module.Finite.of_restrictScalars_finite L (AdjoinRoot f) (Vf s bb F f)
  obtain ⟨e0, he0⟩ :=
    UnitaryFieldData.exists_orthonormal_basis hUFD (B := B) (LinearMap.isSymm_def.mpr hsymm) hsep
  let ρE : AdjoinRoot f ≃+* AdjoinRoot f := invEquiv hUFD.bar hρE
  obtain ⟨φ⟩ := nonempty_mulEquiv_heldGU ρE hρE B e0 he0
  have hsub : unitaryBlock τ s bb F f = sesqUnitaryGroup B := by
    ext g
    rw [mem_sesqUnitaryGroup]
    exact unitary_trace_iff (hW τ s bb F f) B hrep g.1
  have hkf : k = f.natDegree := by
    rw [hk]
    exact ((AdjoinRoot.powerBasis (K := L) hf0).finrank).trans (AdjoinRoot.powerBasis_dim hf0)
  have hcard' : Nat.card (AdjoinRoot f) = (Q ^ f.natDegree) ^ 2 := by
    rw [hcard, hkf, mul_comm 2, pow_mul]
  have hτQ' : ∀ x, ρE x = x ^ (Q ^ f.natDegree) := by
    intro x
    change hUFD.bar x = x ^ (Q ^ f.natDegree)
    have h := hsig x
    rw [hkf] at h
    rw [hbar]
    simpa [σE, invEquiv] using h
  exact ⟨ρE, hρE, hcard', hτQ', ⟨(MulEquiv.subgroupCongr hsub).trans φ⟩⟩

private theorem k329q2_det_of_full {L : Type} [Field L] [Finite L] {n m : ℕ}
    {τ : L ≃+* L} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {aa bb : L[X] → L[X]}
    (H : PrimaryHyp τ s m F aa bb) (g : ↥(Fset s bb F))
    [hfact : Fact (∀ x ∈ Vf s bb F g.1, Matrix.mulVec (Polynomial.aeval s g.1) x = 0)]
    (hfull : Vf s bb F g.1 = ⊤) :
    s.det = (Algebra.norm L (AdjoinRoot.root g.1)) ^
      (Module.finrank (AdjoinRoot g.1) (Vf s bb F g.1)) := by
  classical
  have hgF : g.1 ∈ F := (mem_Fset.mp g.2).1
  have hIrr : Fact (Irreducible g.1) := ⟨H.hirr g.1 hgF⟩
  let M := AdjoinRoot g.1
  have hfreeM : Module.Free M (Vf s bb F g.1) := Module.Free.of_divisionRing M _
  have hop : opV s bb F g.1 X =
      (Algebra.lsmul M M (Vf s bb F g.1) (AdjoinRoot.root g.1)).restrictScalars L := by
    apply LinearMap.ext
    intro x
    apply Subtype.ext
    rw [LinearMap.restrictScalars_apply, Algebra.lsmul_apply, coe_opV,
      ← AdjoinRoot.mk_X (f := g.1), coe_smul_mk]
  let e : ↥(Vf s bb F g.1) ≃ₗ[L] (Fin n → L) :=
    (LinearEquiv.ofEq (Vf s bb F g.1) ⊤ hfull).trans Submodule.topEquiv
  have hconj : Matrix.toLin' s = e.toLinearMap ∘ₗ opV s bb F g.1 X ∘ₗ e.symm.toLinearMap := by
    apply LinearMap.ext
    intro v
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe]
    change Matrix.toLin' s v = (opV s bb F g.1 X (e.symm v) : Fin n → L)
    rw [coe_opV, Polynomial.aeval_X, Matrix.toLin'_apply]
    congr 1
  rw [← LinearMap.det_toLin', hconj, LinearMap.det_conj, hop, LinearMap.det_restrictScalars,
    Algebra.lsmul_eq_smul_one, LinearMap.det_smul]
  simp only [map_pow, map_one, mul_one]
  rfl


private theorem k329q2_full_of_minpoly {L : Type} [Field L] {n m : ℕ}
    {τ : L ≃+* L} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {aa bb : L[X] → L[X]}
    (H : PrimaryHyp τ s m F aa bb) (g : ↥(Fset s bb F))
    (hmin : minpoly L s = g.1) : Vf s bb F g.1 = ⊤ := by
  classical
  have hgF : g.1 ∈ F := (mem_Fset.mp g.2).1
  have hsum_single : ∑ f ∈ F, Pmat s bb F f = Pmat s bb F g.1 := by
    refine Finset.sum_eq_single g.1 ?_ ?_
    · intro h hh hne
      by_contra h0
      have hPf : Pmat s bb F h ≠ 0 := h0
      have hzero : aeval s (minpoly L s) * Pmat s bb F h = 0 := by
        rw [minpoly.aeval L s, zero_mul]
      have hdvd : h ∣ minpoly L s :=
        (aeval_mul_Pmat_iff H.hirr H.hmon H.hprod H.hsm H.hab hh hPf (minpoly L s)).mp hzero
      rw [hmin] at hdvd
      exact hne (Polynomial.eq_of_monic_of_associated (H.hmon h hh) (H.hmon g.1 hgF)
        ((H.hirr h hh).associated_of_dvd (H.hirr g.1 hgF) hdvd))
    · intro hnot
      exact absurd hgF hnot
  have hP : Pmat s bb F g.1 = 1 := by
    rw [← hsum_single, sum_Pmat H.hirr H.hmon H.hprod H.hsm H.hab]
  simp [Vf, hP]

private theorem k329q2_blockSub_selfDual {L : Type} [Field L] [Finite L] {n m Q : ℕ}
    {τ : L ≃+* L} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {aa bb : L[X] → L[X]}
    [hK : ∀ g : ↥(Fset s bb F),
      Fact (∀ x ∈ Vf s bb F g.1, Matrix.mulVec (Polynomial.aeval s g.1) x = 0)]
    (H : PrimaryHyp τ s m F aa bb) (hQ : Nat.card L = Q ^ 2) (hτQ : ∀ x, τ x = x ^ Q)
    (g : ↥(Fset s bb F)) (hself : piI H g = g) :
    ∃ S : Subgroup ↥(Bl H g), (∀ x y : ↥(Bl H g), ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧
      ∃ (a : ℕ) (_ : Fact (Irreducible g.1)) (_ : Finite (AdjoinRoot g.1))
        (ρE : AdjoinRoot g.1 ≃+* AdjoinRoot g.1) (hρE : ∀ x, ρE (ρE x) = x),
        Nat.card (AdjoinRoot g.1) = (Q ^ g.1.natDegree) ^ 2 ∧
        (∀ x, ρE x = x ^ (Q ^ g.1.natDegree)) ∧
        ((minpoly L s = g.1) → s.det = (Algebra.norm L (AdjoinRoot.root g.1)) ^ a) ∧
        Nonempty (S ≃* heldSU a (AdjoinRoot g.1) ρE hρE) := by
  classical
  have hf : g.1 ∈ F := (mem_Fset.mp g.2).1
  have : Fact (Irreducible g.1) := ⟨H.hirr g.1 hf⟩
  have : Module.Finite L (AdjoinRoot g.1) := (H.hmon g.1 hf).finite_adjoinRoot
  have : Finite (AdjoinRoot g.1) :=
    Finite.of_equiv (Fin (Module.finrank L (AdjoinRoot g.1)) → L)
      (Module.finBasis L (AdjoinRoot g.1)).equivFun.toEquiv.symm
  obtain ⟨ρE, hρE, hcard', hτQ', ⟨φ⟩⟩ :=
    k329q2_selfDual_block_iso H hQ hτQ hf (mem_Fset.mp g.2).2
      (by rw [adjM_piI H g, hself])
  let a := Module.finrank (AdjoinRoot g.1) (Vf s bb F g.1)
  let w : ↥(Bl H g) ≃* heldGU a (AdjoinRoot g.1) ρE hρE :=
    (MulEquiv.subgroupCongr (Bl_of_selfDual H hself)).trans φ
  let w' : ↥(Bl H g) →* GL (Fin a) (AdjoinRoot g.1) :=
    (heldGU a (AdjoinRoot g.1) ρE hρE).subtype.comp w.toMonoidHom
  let S : Subgroup ↥(Bl H g) := (heldSU a (AdjoinRoot g.1) ρE hρE).comap w'
  have hw'inj : Function.Injective w' :=
    (heldGU a (AdjoinRoot g.1) ρE hρE).subtype_injective.comp w.injective
  have hle : heldSU a (AdjoinRoot g.1) ρE hρE ≤ w'.range := by
    intro x hx
    have hxG : x ∈ heldGU a (AdjoinRoot g.1) ρE hρE := (Subgroup.mem_inf.mp hx).1
    refine MonoidHom.mem_range.mpr ⟨w.symm ⟨x, hxG⟩, ?_⟩
    simp [w', w]
  refine ⟨S, ?_, ?_, a, inferInstance, inferInstance, ρE, hρE, hcard', hτQ', ?_, ?_⟩
  · intro x y
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact commutatorElement_mem_heldSU (w x).2 (w y).2
  · exact triv_comap w' hw'inj _ hle
      (SUComponentsTrivial_holds a (Q ^ g.1.natDegree) (AdjoinRoot g.1) ρE hρE hcard' hτQ')
  · intro hmin
    exact k329q2_det_of_full H g (k329q2_full_of_minpoly H g hmin)
  · exact comap_equiv_of_injective_le_range w' hw'inj _ hle

private theorem k329q2_blockSub_isRep {L : Type} [Field L] [Finite L] {n m : ℕ}
    {τ : L ≃+* L} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {aa bb : L[X] → L[X]}
    [hK : ∀ g : ↥(Fset s bb F),
      Fact (∀ x ∈ Vf s bb F g.1, Matrix.mulVec (Polynomial.aeval s g.1) x = 0)]
    (H : PrimaryHyp τ s m F aa bb) (g : ↥(Fset s bb F)) (hr : IsRep H g) :
    ∃ S : Subgroup ↥(Bl H g), (∀ x y : ↥(Bl H g), ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧
      ∃ (b : ℕ) (_ : Fact (Irreducible g.1)) (_ : Finite (AdjoinRoot g.1)),
        Nonempty (S ≃* StatedSL b (AdjoinRoot g.1)) := by
  classical
  have hf : g.1 ∈ F := (mem_Fset.mp g.2).1
  have : Fact (Irreducible g.1) := ⟨H.hirr g.1 hf⟩
  have : Module.Finite L (AdjoinRoot g.1) := (H.hmon g.1 hf).finite_adjoinRoot
  have : Finite (AdjoinRoot g.1) :=
    Finite.of_equiv (Fin (Module.finrank L (AdjoinRoot g.1)) → L)
      (Module.finBasis L (AdjoinRoot g.1)).equivFun.toEquiv.symm
  let b := Module.finrank (AdjoinRoot g.1) (Vf s bb F g.1)
  let w : ↥(Bl H g) ≃* GL (Fin b) (AdjoinRoot g.1) :=
    (MulEquiv.subgroupCongr (Bl_of_isRep H hr)).trans
      (Subgroup.topEquiv.trans
        (Matrix.GeneralLinearGroup.toLin' (Module.finBasis (AdjoinRoot g.1)
          (Vf s bb F g.1))).symm)
  let S : Subgroup ↥(Bl H g) := (StatedSL b (AdjoinRoot g.1)).comap w.toMonoidHom
  have hle : StatedSL b (AdjoinRoot g.1) ≤ w.toMonoidHom.range := by
    rw [MonoidHom.range_eq_top.mpr w.surjective]
    exact le_top
  refine ⟨S, ?_, ?_, b, inferInstance, inferInstance, ?_⟩
  · intro x y
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact commutatorElement_mem_statedSL (w x) (w y)
  · exact triv_comap w.toMonoidHom w.injective _ hle
      (SLComponentsTrivial_holds b (AdjoinRoot g.1))
  · exact comap_equiv_of_injective_le_range w.toMonoidHom w.injective _ hle

private theorem k329q2_bl_finite {L : Type} [Field L] [Finite L] {n m : ℕ}
    {τ : L ≃+* L} {s : Matrix (Fin n) (Fin n) L} {F : Finset L[X]} {aa bb : L[X] → L[X]}
    [hK : ∀ g : ↥(Fset s bb F),
      Fact (∀ x ∈ Vf s bb F g.1, Matrix.mulVec (Polynomial.aeval s g.1) x = 0)]
    (H : PrimaryHyp τ s m F aa bb) (g : ↥(Fset s bb F)) : Finite ↥(Bl H g) := by
  have : Finite ↥(Vf s bb F g.1) := Subtype.finite
  have : Finite (↥(Vf s bb F g.1) →ₗ[AdjoinRoot g.1] ↥(Vf s bb F g.1)) :=
    Finite.of_injective _ DFunLike.coe_injective
  exact Subtype.finite

private theorem k329q2_component_factor_data {Q n : ℕ} {L : Type} [Field L] [Finite L]
    {τ : L ≃+* L} (hτ : ∀ x, τ (τ x) = x) (hτQ : ∀ x, τ x = x ^ Q)
    (hL : Nat.card L = Q ^ 2) {s : GL (Fin n) L} (hs : s ∈ heldSU n L τ hτ)
    (hord : (orderOf s : L) ≠ 0) (c : L) (hs3 : (s : Matrix (Fin n) (Fin n) L) ^ 3 = c • 1)
    (J : Subgroup (GL (Fin n) L))
    (hJ : IsComponentOf J (Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ)) :
    ∃ (f : L[X]) (_ : Fact (Irreducible f)) (_ : Finite (AdjoinRoot f)),
      Irreducible f ∧ Monic f ∧ f ∣ (X ^ 3 - C c) ∧
      ((∃ (a : ℕ) (ρE : AdjoinRoot f ≃+* AdjoinRoot f) (hρE : ∀ x, ρE (ρE x) = x),
          2 ≤ a ∧
          Nat.card (AdjoinRoot f) = (Q ^ f.natDegree) ^ 2 ∧
          (∀ x, ρE x = x ^ (Q ^ f.natDegree)) ∧
          ((minpoly L (s : Matrix (Fin n) (Fin n) L) = f) →
            (s : Matrix (Fin n) (Fin n) L).det = (Algebra.norm L (AdjoinRoot.root f)) ^ a) ∧
          Nonempty (J ≃* heldSU a (AdjoinRoot f) ρE hρE)) ∨
       (∃ (b : ℕ), 2 ≤ b ∧ Nonempty (J ≃* StatedSL b (AdjoinRoot f)))) := by
  classical
  have hm0 : 0 < orderOf s := orderOf_pos s
  have hsm : (s : Matrix (Fin n) (Fin n) L) ^ orderOf s = 1 := by
    rw [← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one]
  have hs' : adjM τ (s : Matrix (Fin n) (Fin n) L) * (s : Matrix (Fin n) (Fin n) L) = 1 :=
    Held.mem_heldGU.mp (Subgroup.mem_inf.mp hs).1
  set F : Finset L[X] := factorsOf (L := L) (orderOf s) with hF
  have hirr : ∀ g ∈ F, Irreducible g := fun g hg => factorsOf_irreducible hg
  have hmon : ∀ g ∈ F, Monic g := fun g hg => factorsOf_monic hg
  have hprod : ∏ g ∈ F, g = X ^ orderOf s - 1 := prod_factorsOf hord hm0
  have hcop : ∀ g ∈ F, ∃ u v : L[X], u * g + v * gcF F g = 1 :=
    fun g hg => isCoprime_gcF hirr hmon hg
  choose! aa bb hab using hcop
  let H : PrimaryHyp τ (s : Matrix (Fin n) (Fin n) L) (orderOf s) F aa bb :=
    ⟨hτ, hm0, hirr, hmon, hprod, hsm, hs', hab⟩
  have hK : ∀ g : ↥(Fset (s : Matrix (Fin n) (Fin n) L) bb F),
      Fact (∀ x ∈ Vf (s : Matrix (Fin n) (Fin n) L) bb F g.1,
        Matrix.mulVec (Polynomial.aeval (s : Matrix (Fin n) (Fin n) L) g.1) x = 0) :=
    fun g => ⟨fun x hx => aeval_factor_mulVec_eq_zero H (mem_Fset.mp g.2).1 hx⟩
  let CC : Subgroup (GL (Fin n) L) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) L)) ⊓ heldGU n L τ hτ
  let r := Fintype.card (Activ H)
  let e : Activ H ≃ Fin r := Fintype.equivFin (Activ H)
  let Wf : Fin r → Type := fun k => ↥(Bl H (e.symm k).1)
  have hfin : ∀ k, Finite (Wf k) := fun k => k329q2_bl_finite H (e.symm k)
  have hiso : ↥CC ≃* ((k : Fin r) → Wf k) :=
    (centralizerEquivGlin hτ s).trans ((glinEquivBlocks H).trans (reindexBlocks H e))
  have hJsub : IsComponentOf (J.subgroupOf CC) ⊤ := by
    refine isComponentOf_of_map_injective CC.subtype (Subgroup.subtype_injective CC) ?_
    have h1 : (J.subgroupOf CC).map CC.subtype = J :=
      Subgroup.map_subgroupOf_eq_of_le hJ.1
    have h2 : (⊤ : Subgroup ↥CC).map CC.subtype = CC := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [h1, h2]
    exact hJ
  let J' : Subgroup ((k : Fin r) → Wf k) := (J.subgroupOf CC).map hiso.toMonoidHom
  have hJ'top : IsComponentOf J' ⊤ := by
    have h := isComponentOf_map_of_injective hiso.toMonoidHom hiso.injective hJsub
    rwa [Subgroup.map_top_of_surjective _ hiso.surjective] at h
  have hS_ex : ∀ k : Fin r, ∃ S : Subgroup (Wf k),
      (∀ x y : Wf k, ⁅x, y⁆ ∈ S) ∧
      (∀ X : Subgroup S, IsComponentOf X ⊤ → X = ⊤) ∧
      ((∃ (a : ℕ) (_ : Fact (Irreducible (e.symm k).1.1))
          (_ : Finite (AdjoinRoot (e.symm k).1.1))
          (ρE : AdjoinRoot (e.symm k).1.1 ≃+* AdjoinRoot (e.symm k).1.1)
          (hρE : ∀ x, ρE (ρE x) = x),
          Nat.card (AdjoinRoot (e.symm k).1.1) = (Q ^ (e.symm k).1.1.natDegree) ^ 2 ∧
          (∀ x, ρE x = x ^ (Q ^ (e.symm k).1.1.natDegree)) ∧
          ((minpoly L (s : Matrix (Fin n) (Fin n) L) = (e.symm k).1.1) →
            (s : Matrix (Fin n) (Fin n) L).det =
              (Algebra.norm L (AdjoinRoot.root (e.symm k).1.1)) ^ a) ∧
          Nonempty (S ≃* heldSU a (AdjoinRoot (e.symm k).1.1) ρE hρE)) ∨
       (∃ (b : ℕ) (_ : Fact (Irreducible (e.symm k).1.1))
          (_ : Finite (AdjoinRoot (e.symm k).1.1)),
          Nonempty (S ≃* StatedSL b (AdjoinRoot (e.symm k).1.1)))) := by
    intro k
    rcases (e.symm k).2 with hself | hrep
    · obtain ⟨S, hS, hSt, a, hFld, hFin, ρE, hρE, hcard', hτQ', hdet, hiso'⟩ :=
        k329q2_blockSub_selfDual H hL hτQ (e.symm k) hself
      exact ⟨S, hS, hSt, Or.inl ⟨a, hFld, hFin, ρE, hρE, hcard', hτQ', hdet, hiso'⟩⟩
    · obtain ⟨S, hS, hSt, b, hFld, hFin, hiso'⟩ :=
        k329q2_blockSub_isRep H (e.symm k) hrep
      exact ⟨S, hS, hSt, Or.inr ⟨b, hFld, hFin, hiso'⟩⟩
  choose S hS₀ hSt₀ hty using hS_ex
  obtain ⟨k, hk⟩ := component_eq_factor_image S hS₀ hSt₀ hJ'top
  have hJeq : J' = (S k).map (MonoidHom.mulSingle Wf k) := hk
  have hms := mulSingle_injective' (H := Wf) k
  have e1 : ↥J ≃* ↥(S k) :=
    (Subgroup.subgroupOfEquivOfLe hJ.1).symm.trans
      ((Subgroup.equivMapOfInjective (J.subgroupOf CC) hiso.toMonoidHom hiso.injective).trans
        ((MulEquiv.subgroupCongr hJeq).trans
          ((Subgroup.equivMapOfInjective (S k) (MonoidHom.mulSingle Wf k) hms).symm)))
  have hfF : (e.symm k).1.1 ∈ F := (mem_Fset.mp (e.symm k).1.2).1
  have hPf : Pmat (s : Matrix (Fin n) (Fin n) L) bb F (e.symm k).1.1 ≠ 0 :=
    (mem_Fset.mp (e.symm k).1.2).2
  have hdvd : (e.symm k).1.1 ∣ (X ^ 3 - C c) := by
    rw [← (aeval_mul_Pmat_iff H.hirr H.hmon H.hprod H.hsm H.hab hfF hPf (X ^ 3 - C c))]
    rw [map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C,
      Algebra.algebraMap_eq_smul_one, hs3, sub_self, zero_mul]
  rcases hty k with ⟨a, hFld, hFin, ρE, hρE, hcard', hτQ', hdet, hiso'⟩ | ⟨b, hFld, hFin, hiso'⟩
  · by_cases ha2 : 2 ≤ a
    · refine ⟨(e.symm k).1.1, hFld, hFin, H.hirr _ hfF, H.hmon _ hfF, hdvd,
        Or.inl ⟨a, ρE, hρE, ha2, hcard', hτQ', hdet, ?_⟩⟩
      exact ⟨e1.trans hiso'.some⟩
    · exfalso
      exact absurd hJ.2.2 (not_isQuasisimple_of_mulEquiv (e1.trans hiso'.some) fun x y =>
        Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact mul_comm_GL_of_le_one (by omega)
            (x : GL (Fin a) (AdjoinRoot (e.symm k).1.1))
            (y : GL (Fin a) (AdjoinRoot (e.symm k).1.1))))
  · by_cases hb2 : 2 ≤ b
    · refine ⟨(e.symm k).1.1, hFld, hFin, H.hirr _ hfF, H.hmon _ hfF, hdvd,
        Or.inr ⟨b, hb2, ?_⟩⟩
      exact ⟨e1.trans hiso'.some⟩
    · exfalso
      exact absurd hJ.2.2 (not_isQuasisimple_of_mulEquiv (e1.trans hiso'.some) fun x y =>
        Subtype.ext (by
          rw [Subgroup.coe_mul, Subgroup.coe_mul]
          exact mul_comm_GL_of_le_one (by omega)
            (x : GL (Fin b) (AdjoinRoot (e.symm k).1.1))
            (y : GL (Fin b) (AdjoinRoot (e.symm k).1.1))))



private theorem k329q2_card_adjoinRoot {L : Type} [Field L] [Finite L] {Q : ℕ}
    (hL : Nat.card L = Q ^ 2) {f : L[X]} (hmon : f.Monic) :
    Nat.card (AdjoinRoot f) = (Q ^ f.natDegree) ^ 2 := by
  have : Module.Finite L (AdjoinRoot f) := hmon.finite_adjoinRoot
  have : Finite (AdjoinRoot f) := Module.finite_of_finite L
  have : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hcard : Nat.card (AdjoinRoot f) = Nat.card L ^ f.natDegree := by
    rw [Module.natCard_eq_pow_finrank (K := L) (V := AdjoinRoot f),
      (AdjoinRoot.powerBasis (K := L) hmon.ne_zero).finrank,
      AdjoinRoot.powerBasis_dim hmon.ne_zero]
  rw [hcard, hL, ← pow_mul, mul_comm, pow_mul]

private theorem k329q2_order {L : Type} [Field L] [Finite L] {n : ℕ}
    {f : L[X]} [Fact (Irreducible f)] [Finite (AdjoinRoot f)]
    {ρE : AdjoinRoot f ≃+* AdjoinRoot f} (hρE : ∀ x, ρE (ρE x) = x)
    (hcardM : Nat.card (AdjoinRoot f) = (2 ^ f.natDegree) ^ 2)
    (hτ'Q : ∀ x, ρE x = x ^ (2 ^ f.natDegree))
    {a : ℕ} (ha2 : 2 ≤ a)
    {J : Subgroup (GL (Fin n) L)} (eJ : ↥J ≃* heldSU a (AdjoinRoot f) ρE hρE)
    (hJq : CFSG.Open.IsQuasisimple ↥J)
    (hJcard : Nat.card (↥J ⧸ Subgroup.center ↥J) = 504) :
    a = 2 ∧ f.natDegree = 3 := by
  have hfn : 1 ≤ f.natDegree := (Fact.out : Irreducible f).natDegree_pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype (AdjoinRoot f) := Fintype.ofFinite _
  have hchar : CharP (AdjoinRoot f) 2 :=
    charP_of_card_eq_prime_pow (p := 2) (f := 2 * f.natDegree)
      (by rw [← Nat.card_eq_fintype_card, hcardM, ← pow_mul, mul_comm])
  by_cases ha : a = 2
  · subst ha
    have hSU2 : heldSU 2 (AdjoinRoot f) ρE hρE =
        StatedSU 2 (2 ^ f.natDegree) (AdjoinRoot f) :=
      hct_heldSU_eq_statedSU hτ'Q
    let F := CFSG.LieType.Steinberg.fixedSubfield (AdjoinRoot f) 2 f.natDegree
    obtain ⟨e2⟩ := CFSG.RankThree.SubgroupLists.nonempty_sl2_mulEquiv_statedSU_two
      (K := AdjoinRoot f) (r := 2) (f := f.natDegree) hcardM
    let eQSL : ↥J ≃* ↥(StatedSL 2 F) :=
      (eJ.trans (MulEquiv.subgroupCongr hSU2)).trans
        (e2.symm.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F))
    obtain ⟨eQc⟩ := nonempty_quotientCenter_equiv_statedProj eQSL
    have hY : Nat.card (StatedProj (StatedSL 2 F)) = 504 := by
      rw [← Nat.card_congr eQc.toEquiv, hJcard]
    have hFcard : Nat.card F = 2 ^ f.natDegree :=
      CFSG.LieType.Steinberg.card_fixedSubfield hcardM
    have hSLq : CFSG.Open.IsQuasisimple ↥(StatedSL 2 F) :=
      k329_isQuasisimple_of_mulEquiv eQSL hJq
    have hF4 : 4 ≤ Nat.card F := by
      by_contra hlt
      push Not at hlt
      have h2 : Nat.card F = 2 ∨ Nat.card F = 3 := by
        have := Finite.one_lt_card (α := F); omega
      rcases h2 with h2 | h2
      · have hc := CFSG.Open.StatedAPI.card_statedSL_two F
        have hs2 : Group.IsSolvable ↥(StatedSL 2 F) :=
          hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1) (b := 1)
            Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc, h2]; norm_num)
        have : Nontrivial (↥(StatedSL 2 F) ⧸ Subgroup.center ↥(StatedSL 2 F)) :=
          hSLq.2.toNontrivial
        have : Nontrivial ↥(StatedSL 2 F) :=
          (QuotientGroup.mk_surjective (s := Subgroup.center ↥(StatedSL 2 F))).nontrivial
        have : Group.IsPerfect ↥(StatedSL 2 F) := Group.isPerfect_def.mpr hSLq.1
        exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL 2 F)) hs2
      · have hc := CFSG.Open.StatedAPI.card_statedSL_two F
        have hs2 : Group.IsSolvable ↥(StatedSL 2 F) :=
          hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 1)
            Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc, h2]; norm_num)
        have : Nontrivial (↥(StatedSL 2 F) ⧸ Subgroup.center ↥(StatedSL 2 F)) :=
          hSLq.2.toNontrivial
        have : Nontrivial ↥(StatedSL 2 F) :=
          (QuotientGroup.mk_surjective (s := Subgroup.center ↥(StatedSL 2 F))).nontrivial
        have : Group.IsPerfect ↥(StatedSL 2 F) := Group.isPerfect_def.mpr hSLq.1
        exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL 2 F)) hs2
    have hAdm : StatedLieAdmissible .PSL 2 2 f.natDegree :=
      ⟨Nat.prime_two, hfn, by norm_num,
        by intro h; have h2 : 2 ^ f.natDegree = 2 := congrArg Prod.snd h
           rw [← hFcard] at h2; omega,
        by intro h; have h3 : 2 ^ f.natDegree = 3 := congrArg Prod.snd h
           rw [← hFcard] at h3; omega⟩
    have hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSL 2 F)) .PSL 2 2 f.natDegree :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
        ⟨hAdm, F, inferInstance, inferInstance, hFcard, ⟨MulEquiv.refl _⟩⟩⟩
    obtain ⟨-, -, hrf⟩ := k329_S2_order504 (by norm_num : (2 : ℕ) ≠ 0) hLie hY
    have hdeg : f.natDegree = 3 := by
      have h : 2 ^ f.natDegree = 2 ^ 3 := by rw [hrf]; norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
    exact ⟨rfl, hdeg⟩
  · have ha3 : 3 ≤ a := by omega
    have hSUq : CFSG.Open.IsQuasisimple ↥(heldSU a (AdjoinRoot f) ρE hρE) :=
      k329_isQuasisimple_of_mulEquiv eJ hJq
    have hSUeq' : heldSU a (AdjoinRoot f) ρE hρE =
        StatedSU a (2 ^ f.natDegree) (AdjoinRoot f) :=
      hct_heldSU_eq_statedSU hτ'Q
    have hnot32 : (a, 2 ^ f.natDegree) ≠ (3, 2) := by
      intro h
      have ha' : a = 3 := congrArg Prod.fst h
      have hq : 2 ^ f.natDegree = 2 := congrArg Prod.snd h
      have hM4 : Nat.card (AdjoinRoot f) = (2 ^ 1) ^ 2 := by rw [hcardM, hq]; norm_num
      have hc : Nat.card (StatedSU 3 (2 ^ 1) (AdjoinRoot f)) = 216 := by
        rw [CFSG.RankThree.PartTwo.Sec8.Item87Proof.card_statedSU_three_two hM4]; norm_num
      have hs2 : Group.IsSolvable ↥(StatedSU 3 (2 ^ 1) (AdjoinRoot f)) :=
        hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 3)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc]; norm_num)
      have hs3 : Group.IsSolvable ↥(StatedSU a (2 ^ f.natDegree) (AdjoinRoot f)) := by
        subst ha'; rw [hq]; simpa using hs2
      have hsol : Group.IsSolvable ↥(heldSU a (AdjoinRoot f) ρE hρE) := by
        rw [hSUeq']; exact hs3
      have : Nontrivial (↥(heldSU a (AdjoinRoot f) ρE hρE) ⧸
          Subgroup.center ↥(heldSU a (AdjoinRoot f) ρE hρE)) := hSUq.2.toNontrivial
      have : Nontrivial ↥(heldSU a (AdjoinRoot f) ρE hρE) :=
        (QuotientGroup.mk_surjective (s := Subgroup.center
          ↥(heldSU a (AdjoinRoot f) ρE hρE))).nontrivial
      have : Group.IsPerfect ↥(heldSU a (AdjoinRoot f) ρE hρE) :=
        Group.isPerfect_def.mpr hSUq.1
      exact Group.IsPerfect.not_isSolvable (G := ↥(heldSU a (AdjoinRoot f) ρE hρE)) hsol
    have hZ := (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card (F := AdjoinRoot f)
      (p := 2) (f := f.natDegree) hcardM ha3 hnot32).2
    have hcenter : Subgroup.center ↥(heldSU a (AdjoinRoot f) ρE hρE) =
        (StatedScalars (Fin a) (AdjoinRoot f)).subgroupOf (heldSU a (AdjoinRoot f) ρE hρE) := by
      rw [hSUeq']; exact hZ
    let eQc : ↥J ⧸ Subgroup.center ↥J ≃* StatedProj (heldSU a (AdjoinRoot f) ρE hρE) :=
      (QuotientGroup.congr (Subgroup.center ↥J)
        (Subgroup.center ↥(heldSU a (AdjoinRoot f) ρE hρE)) eJ
        (Subgroup.map_center_eq eJ)).trans
        (QuotientGroup.quotientMulEquivOfEq hcenter)
    have hY : Nat.card (StatedProj (StatedSU a (2 ^ f.natDegree) (AdjoinRoot f))) = 504 := by
      rw [← hSUeq']
      exact (Nat.card_congr eQc.toEquiv).symm.trans hJcard
    have hAdm : StatedLieAdmissible .PSU a 2 f.natDegree :=
      ⟨Nat.prime_two, hfn, ha3, hnot32⟩
    have hLie : CFSG.Blueprint.LieModel
        (StatedProj (StatedSU a (2 ^ f.natDegree) (AdjoinRoot f))) .PSU a 2 f.natDegree :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
        ⟨hAdm, AdjoinRoot f, inferInstance, inferInstance, hcardM, ⟨MulEquiv.refl _⟩⟩⟩
    obtain ⟨hPSL, -, -⟩ := k329_S2_order504 (by omega : a ≠ 0) hLie hY
    exact absurd hPSL (by decide)

end K329q2Private

section K329u3fQTwo

open CFSG.Open CFSG.LieType.SemisimpleCentralizers.Held
open Polynomial

private theorem k329u3f_q_two (n r e : ℕ) (hadm : StatedLieAdmissible .PSU n r e) (hr : r ≠ 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (r ^ e) ^ 2) (hr2 : r = 2) (he1 : e = 1)
    (x : ↥(StatedSU n (r ^ e) K)) (hx : x ∉ K329Zh (StatedSU n (r ^ e) K))
    (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (r ^ e) K))
    (Q : Subgroup ↥(StatedSU n (r ^ e) K)) (hQL : Q ≤ K329Lres x)
    (hQn : (Q.subgroupOf (K329Lres x)).Normal) (hQq : CFSG.Open.IsQuasisimple ↥Q)
    (hQcard : Nat.card (↥Q ⧸ Subgroup.center ↥Q) = 504) : False := by
  subst hr2
  subst he1
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 1 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
  let τ : K ≃+* K := RingEquiv.ofRingHom hUF.bar hUF.bar
    (RingHom.ext hUF.bar_bar) (RingHom.ext hUF.bar_bar)
  have hτ : ∀ c, τ (τ c) = c := hUF.bar_bar
  have hτQ : ∀ c, τ c = c ^ (2 ^ 1) := by
    intro c; simpa [τ] using hUF.bar_apply c
  have hSUeq : heldSU n K τ hτ = StatedSU n (2 ^ 1) K := hct_heldSU_eq_statedSU hτQ
  let s : GL (Fin n) K := (x : GL (Fin n) K)
  have hs : s ∈ heldSU n K τ hτ := by rw [hSUeq]; exact x.2
  have hord : (orderOf s : K) ≠ 0 := k329u3f_order hadm hr hK x hx3
  have hs3Z : s ^ 3 ∈ StatedScalars (Fin n) K := by
    have h := Subgroup.mem_subgroupOf.mp hx3
    simpa [s, K329Zh] using h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hs3Z
  have hs3mat : (s : Matrix (Fin n) (Fin n) K) ^ 3 = (c : K) • 1 := by
    have h := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) hc.symm
    rw [Units.val_pow_eq_pow_val, Matrix.GeneralLinearGroup.coe_scalar] at h
    rw [h, Matrix.smul_one_eq_diagonal]
    ext i j
    simp [Matrix.scalar_apply, Matrix.diagonal_apply]
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (2 ^ 1) K := by
    rw [← hSUeq]; rw [hc]; exact pow_mem hs 3
  have hc3 : (c : K) ^ 3 = 1 := by
    have hn : 1 ≤ n := le_trans (by norm_num) hadm.2.2.1
    have h := (CFSG.LinearGroups.unitary_scalar_kernel (p := 2) (f := 1)
      Nat.prime_two hK hn).2.1 c
    have h' := (h.mp hsc).2
    have h2 := congrArg Units.val h'
    rw [Units.val_pow_eq_pow_val, Units.val_one] at h2
    norm_num at h2
    exact h2
  let D : Subgroup ↥(StatedSU n (2 ^ 1) K) :=
    Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 1) K))
  have hDnorm : ((K329Lres x).subgroupOf D).Normal := by
    change ((K329Res D).subgroupOf D).Normal
    exact k329_res_normal (C := D) (D := D) le_rfl (by rw [Subgroup.subgroupOf_self]; infer_instance)
  have hQcompD : IsComponentOf Q D :=
    ⟨hQL.trans (Subgroup.map_subtype_le _), IsSubnormal.step hQL hQn
      (IsSubnormal.step (Subgroup.map_subtype_le _) hDnorm (IsSubnormal.refl D)), hQq⟩
  let Q' : Subgroup (GL (Fin n) K) := Q.map (StatedSU n (2 ^ 1) K).subtype
  let CC : Subgroup (GL (Fin n) K) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ heldGU n K τ hτ
  have hQ'q : CFSG.Open.IsQuasisimple ↥Q' :=
    k329_isQuasisimple_of_mulEquiv
      (Subgroup.equivMapOfInjective Q (StatedSU n (2 ^ 1) K).subtype
        (Subgroup.subtype_injective _)) hQq
  have hQ'comp : IsComponentOf Q' CC := by
    let D' : Subgroup (GL (Fin n) K) := D.map (StatedSU n (2 ^ 1) K).subtype
    have hD'eq : D' = Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ StatedSU n (2 ^ 1) K := by
      ext g; constructor
      · intro hg
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hg
        refine Subgroup.mem_inf.mpr ⟨Subgroup.mem_centralizer_iff.mpr ?_, y.2⟩
        intro z hz
        rw [Set.mem_singleton_iff] at hz; subst hz
        have h := (Subgroup.mem_centralizer_iff.mp hy) x (Set.mem_singleton x)
        exact congrArg Subtype.val h
      · rintro ⟨hg1, hg2⟩
        refine Subgroup.mem_map.mpr ⟨⟨g, hg2⟩, Subgroup.mem_centralizer_iff.mpr ?_, rfl⟩
        intro z hz
        rw [Set.mem_singleton_iff] at hz; subst hz
        apply Subtype.ext
        exact Subgroup.mem_centralizer_iff.mp hg1 s (Set.mem_singleton s)
    have hD'eq2 : D' = CC ⊓ StatedSL n K := by
      rw [hD'eq]
      ext g; constructor
      · rintro ⟨hg1, hg2⟩
        rw [← hSUeq] at hg2
        exact ⟨⟨hg1, (Subgroup.mem_inf.mp hg2).1⟩, (Subgroup.mem_inf.mp hg2).2⟩
      · rintro ⟨⟨hg1, hg2⟩, hg3⟩
        exact ⟨hg1, by rw [← hSUeq]; exact Subgroup.mem_inf.mpr ⟨hg2, hg3⟩⟩
    have hD'leC : D' ≤ CC := by rw [hD'eq2]; exact inf_le_left
    have hD'normC : (D'.subgroupOf CC).Normal := by
      rw [hD'eq2, Subgroup.inf_subgroupOf_left]
      infer_instance
    have hQ'compD' : IsComponentOf Q' D' := by
      have := isComponentOf_map_of_injective (StatedSU n (2 ^ 1) K).subtype
        (Subgroup.subtype_injective _) (L := Q) (K := D) hQcompD
      simpa [Q', D'] using this
    exact ⟨hQ'compD'.1.trans hD'leC,
      IsSubnormal.trans hQ'compD'.2.1 (IsSubnormal.step hD'leC hD'normC (IsSubnormal.refl CC)),
      hQ'q⟩
  have hQ'card : Nat.card (↥Q' ⧸ Subgroup.center ↥Q') = 504 := by
    let e0 : ↥Q ≃* ↥Q' := Subgroup.equivMapOfInjective Q _ (Subgroup.subtype_injective _)
    have hc' := Subgroup.map_center_eq e0
    exact (Nat.card_congr (QuotientGroup.congr _ _ e0 hc').toEquiv).symm.trans hQcard
  obtain ⟨f, hFact, hFin, hirr, hmonf, hdvd, hdisj⟩ :=
    k329q2_component_factor_data (Q := 2) hτ hτQ hK hs hord c hs3mat Q' hQ'comp
  rcases hdisj with ⟨a, ρE, hρE, ha2, hcardM, hτ'Q, hdet, ⟨eJ⟩⟩ | ⟨b, hb2, ⟨eJ⟩⟩
  · obtain ⟨haeq, hdegf⟩ := k329q2_order hρE hcardM hτ'Q ha2 eJ hQ'q hQ'card
    subst haeq
    have hf_eq : f = Polynomial.X ^ 3 - Polynomial.C (c : K) := by
      have hdeg : (Polynomial.X ^ 3 - Polynomial.C (c : K) : K[X]).natDegree ≤ f.natDegree := by
        rw [Polynomial.natDegree_X_pow_sub_C, hdegf]
      exact (Polynomial.eq_of_monic_of_dvd_of_natDegree_le hmonf
        (Polynomial.monic_X_pow_sub_C (c : K) (by norm_num)) hdvd hdeg).symm
    have haeval : Polynomial.aeval (s : Matrix (Fin n) (Fin n) K) f = 0 := by
      rw [hf_eq, map_sub, map_pow, Polynomial.aeval_X, Polynomial.aeval_C, hs3mat,
        Algebra.algebraMap_eq_smul_one, sub_self]
    have : NeZero n := ⟨by have h := hadm.2.2.1; omega⟩
    have hmin : minpoly K (s : Matrix (Fin n) (Fin n) K) = f := by
      have h := minpoly.eq_of_irreducible (A := K) (B := Matrix (Fin n) (Fin n) K) hirr haeval
      rw [hmonf.leadingCoeff, inv_one, Polynomial.C_1, mul_one] at h
      exact h.symm
    have hnorm : Algebra.norm K (AdjoinRoot.root f) = (c : K) := by
      rw [← AdjoinRoot.powerBasis_gen (K := K) (f := f) (Fact.out : Irreducible f).ne_zero,
        Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly
          (AdjoinRoot.powerBasis (K := K) (f := f) (Fact.out : Irreducible f).ne_zero)]
      have hcoeff : (minpoly K (AdjoinRoot.powerBasis (K := K) (f := f)
            (Fact.out : Irreducible f).ne_zero).gen).coeff 0 = (c : K) := by
        rw [AdjoinRoot.minpoly_powerBasis_gen_of_monic (K := K) (f := f) hmonf
              (Fact.out : Irreducible f).ne_zero, hf_eq,
          Polynomial.coeff_sub, Polynomial.coeff_X_pow, Polynomial.coeff_C]
        simp only [Nat.reduceEqDiff, if_true, if_false, zero_sub]
        have : CharP K 2 := hUF.charP
        rw [CharTwo.neg_eq]
      rw [hcoeff,
        show (AdjoinRoot.powerBasis (K := K) (f := f)
            (Fact.out : Irreducible f).ne_zero).dim = f.natDegree from
          AdjoinRoot.powerBasis_dim (Fact.out : Irreducible f).ne_zero, hdegf]
      have : CharP K 2 := hUF.charP
      rw [CharTwo.neg_eq]
      ring
    have hdet_su : (s : Matrix (Fin n) (Fin n) K).det = 1 :=
      CFSG.Open.StatedAPI.mem_statedSL_iff.mp (Subgroup.mem_inf.mp hs).2
    have hc2 : (c : K) ^ 2 = 1 := by
      rw [← hnorm, ← hdet hmin, hdet_su]
    have hc1 : (c : K) = 1 := by
      have h : (c : K) ^ 3 = (c : K) * (c : K) ^ 2 := by ring
      rw [h, hc2, mul_one] at hc3
      exact hc3
    have hroot : f.IsRoot 1 := by
      rw [hf_eq, hc1]
      simp [Polynomial.IsRoot, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X]
    exact hirr.not_isRoot_of_natDegree_ne_one (by rw [hdegf]; norm_num) hroot
  · have hfn : 1 ≤ f.natDegree := (Fact.out : Irreducible f).natDegree_pos
    have hSLq : CFSG.Open.IsQuasisimple ↥(StatedSL b (AdjoinRoot f)) :=
      k329_isQuasisimple_of_mulEquiv eJ hQ'q
    have hcard_f : Nat.card (AdjoinRoot f) = 2 ^ (2 * f.natDegree) := by
      rw [k329q2_card_adjoinRoot (Q := 2) hK hmonf, ← pow_mul, mul_comm]
    have hnot22 : (b, Nat.card (AdjoinRoot f)) ≠ (2, 2) := by
      intro h
      have hb : b = 2 := congrArg Prod.fst h
      have hM2 : Nat.card (AdjoinRoot f) = 2 := congrArg Prod.snd h
      have hc' := CFSG.Open.StatedAPI.card_statedSL_two (AdjoinRoot f)
      have hs2 : Group.IsSolvable ↥(StatedSL 2 (AdjoinRoot f)) :=
        hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 1) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc', hM2]; norm_num)
      have hb' : Group.IsSolvable ↥(StatedSL b (AdjoinRoot f)) := by rw [hb]; exact hs2
      have : Nontrivial (↥(StatedSL b (AdjoinRoot f)) ⧸
          Subgroup.center ↥(StatedSL b (AdjoinRoot f))) := hSLq.2.toNontrivial
      have : Nontrivial ↥(StatedSL b (AdjoinRoot f)) :=
        (QuotientGroup.mk_surjective (s := Subgroup.center
          ↥(StatedSL b (AdjoinRoot f)))).nontrivial
      have : Group.IsPerfect ↥(StatedSL b (AdjoinRoot f)) := Group.isPerfect_def.mpr hSLq.1
      exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL b (AdjoinRoot f))) hb'
    have hnot23 : (b, Nat.card (AdjoinRoot f)) ≠ (2, 3) := by
      intro h
      have hb : b = 2 := congrArg Prod.fst h
      have hM3 : Nat.card (AdjoinRoot f) = 3 := congrArg Prod.snd h
      have hc' := CFSG.Open.StatedAPI.card_statedSL_two (AdjoinRoot f)
      have hs2 : Group.IsSolvable ↥(StatedSL 2 (AdjoinRoot f)) :=
        hct_isSolvable_of_natCard_eq (p := 2) (q := 3) (a := 3) (b := 1)
          Nat.prime_two Nat.prime_three (by norm_num) (by rw [hc', hM3]; norm_num)
      have hb' : Group.IsSolvable ↥(StatedSL b (AdjoinRoot f)) := by rw [hb]; exact hs2
      have : Nontrivial (↥(StatedSL b (AdjoinRoot f)) ⧸
          Subgroup.center ↥(StatedSL b (AdjoinRoot f))) := hSLq.2.toNontrivial
      have : Nontrivial ↥(StatedSL b (AdjoinRoot f)) :=
        (QuotientGroup.mk_surjective (s := Subgroup.center
          ↥(StatedSL b (AdjoinRoot f)))).nontrivial
      have : Group.IsPerfect ↥(StatedSL b (AdjoinRoot f)) := Group.isPerfect_def.mpr hSLq.1
      exact Group.IsPerfect.not_isSolvable (G := ↥(StatedSL b (AdjoinRoot f))) hb'
    obtain ⟨eQc⟩ := nonempty_quotientCenter_equiv_statedProj eJ
    have hY : Nat.card (StatedProj (StatedSL b (AdjoinRoot f))) = 504 := by
      rw [← Nat.card_congr eQc.toEquiv, hQ'card]
    have hAdm : StatedLieAdmissible .PSL b 2 (2 * f.natDegree) :=
      ⟨Nat.prime_two, by omega, hb2,
        by rw [← hcard_f]; exact hnot22, by rw [← hcard_f]; exact hnot23⟩
    have hLie : CFSG.Blueprint.LieModel (StatedProj (StatedSL b (AdjoinRoot f)))
        .PSL b 2 (2 * f.natDegree) :=
      Or.inl ⟨by simp [CFSG.Blueprint.classicalTags],
        ⟨hAdm, AdjoinRoot f, inferInstance, inferInstance, hcard_f, ⟨MulEquiv.refl _⟩⟩⟩
    obtain ⟨-, -, hrf⟩ := k329_S2_order504 (by omega : b ≠ 0) hLie hY
    have h3 : 2 * f.natDegree = 3 := by
      have h : 2 ^ (2 * f.natDegree) = 2 ^ 3 := by rw [hrf]; norm_num
      exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h
    have h2dvd : 2 ∣ 3 := ⟨f.natDegree, h3.symm⟩
    exact absurd h2dvd (by norm_num)

end K329u3fQTwo


theorem k329_S3f_PSU (n r e : ℕ) (hadm : StatedLieAdmissible .PSU n r e) (hr : r ≠ 3)
    (K : Type) [Field K] [Finite K] (hK : Nat.card K = (r ^ e) ^ 2) :
    K329YMatrix (StatedSU n (r ^ e) K) (r ^ e) := by
  intro x hx hx3 ⟨Q, hQL, hQn, hQq, hQcard⟩
  rcases k329u3f_reduction n r e hadm hr K hK x hx hx3 Q hQL hQn hQq hQcard with h8 | ⟨hr2, he1⟩
  · exact h8
  · exact (k329u3f_q_two n r e hadm hr K hK hr2 he1 x hx hx3 Q hQL hQn hQq hQcard).elim

theorem k329_S3c_PSU (n : ℕ) (hadm : StatedLieAdmissible .PSU n 2 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2) :
    K329CentralProductMatrix (StatedSU n (2 ^ 3) K) := by
  classical
  have hn : 3 ≤ n := hadm.2.2.1
  intro x hxZ hx3
  let s : GL (Fin n) K := (x : GL (Fin n) K)
  have hUF : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
  let τ : K ≃+* K := RingEquiv.ofRingHom hUF.bar hUF.bar
    (RingHom.ext hUF.bar_bar) (RingHom.ext hUF.bar_bar)
  have hτ : ∀ c, τ (τ c) = c := hUF.bar_bar
  have hτQ : ∀ c, τ c = c ^ (2 ^ 3) := by
    intro c
    simpa [τ] using hUF.bar_apply c
  have hSUeq : Held.heldSU n K τ hτ = StatedSU n (2 ^ 3) K :=
    Held.hct_heldSU_eq_statedSU hτQ
  have hs : s ∈ Held.heldSU n K τ hτ := by
    rw [hSUeq]
    exact x.2
  have hs3 : s ^ 3 ∈ StatedScalars (Fin n) K := by
    have h := Subgroup.mem_subgroupOf.mp hx3
    simpa [s, K329Zh] using h
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hs3
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := hUF.charP
  have hc9 : c ^ 9 = 1 := by
    have hs3held : s ^ 3 ∈ Held.heldSU n K τ hτ := pow_mem hs 3
    have hgu : s ^ 3 ∈ Held.heldGU n K τ hτ := (Subgroup.mem_inf.mp hs3held).1
    have heq := Held.mem_heldGU.mp hgu
    rw [← hc, Matrix.GeneralLinearGroup.coe_scalar] at heq
    have hmap : (Matrix.scalar (Fin n) (c : K)).map τ =
        Matrix.scalar (Fin n) (τ (c : K)) := by
      ext i j
      simp only [Matrix.map_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij]
    rw [hmap, hτQ] at heq
    have hprod : Matrix.scalar (Fin n) ((c : K) ^ 2 ^ 3) * Matrix.scalar (Fin n) (c : K) =
        Matrix.scalar (Fin n) ((c : K) ^ 9) := by
      rw [← map_mul]
      congr 1
      rw [← pow_succ]
      norm_num
    have htr : Matrix.transpose (Matrix.scalar (Fin n) ((c : K) ^ 2 ^ 3)) =
        Matrix.scalar (Fin n) ((c : K) ^ 2 ^ 3) := by
      ext i j
      simp only [Matrix.transpose_apply, Matrix.scalar_apply, Matrix.diagonal_apply]
      by_cases hij : i = j
      · subst hij; simp
      · simp [hij, eq_comm]
    rw [htr, hprod] at heq
    have hmat : Matrix.scalar (Fin n) ((c : K) ^ 9) = 1 := heq
    apply Units.ext
    have : Nonempty (Fin n) := ⟨⟨0, by omega⟩⟩
    simpa using (Matrix.scalar_inj (n := Fin n)).mp (by simpa using hmat)
  have hs27 : s ^ 27 = 1 := by
    have h : s ^ 27 = (s ^ 3) ^ 9 := by group
    rw [h, ← hc]
    have : (Matrix.GeneralLinearGroup.scalar (Fin n) c) ^ 9 =
        Matrix.GeneralLinearGroup.scalar (Fin n) (c ^ 9) := by
      rw [map_pow]
    rw [this, hc9, map_one]
  have hord27 : orderOf s ∣ 27 := orderOf_dvd_of_pow_eq_one hs27
  have hordK : (orderOf s : K) ≠ 0 := by
    intro h0
    have h2 : 2 ∣ orderOf s := (CharP.cast_eq_zero_iff K 2 (orderOf s)).mp h0
    exact (by norm_num : ¬ (2 : ℕ) ∣ 27) (h2.trans hord27)
  obtain ⟨r, H, hgrp, hfin, hblk, ⟨e⟩⟩ :=
    Held.unitaryCentralizerDecomposition_holds (2 ^ 3) n K τ hτ s hK hτQ hs hordK
  let : ∀ k, Group (H k) := hgrp
  let : ∀ k, Finite (H k) := hfin
  let C : Subgroup (GL (Fin n) K) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ Held.heldGU n K τ hτ
  let θ : (∀ k, H k) →* GL (Fin n) K := (Subgroup.subtype C).comp e.symm.toMonoidHom
  have hθinj : Function.Injective θ :=
    (Subgroup.subtype_injective C).comp e.symm.injective
  have hθrange : θ.range = C := by
    change ((Subgroup.subtype C).comp e.symm.toMonoidHom).range = C
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.symm.surjective]
    ext g
    constructor
    · intro hg; exact Subgroup.map_subtype_le ⊤ hg
    · intro hg; exact ⟨⟨g, hg⟩, trivial, rfl⟩
  have hblk' : ∀ k, commutator (H k) = ⊥ ∨
      CFSG.Open.IsQuasisimple ↥(commutator (H k)) := fun k => k329u3c_block (hblk k)
  let T : Fin r → Subgroup (∀ k, H k) := fun k =>
    (commutator (H k)).map (MonoidHom.mulSingle H k)
  have hT_perf : ∀ k, ⁅T k, T k⁆ = T k := by
    intro k
    change ⁅(commutator (H k)).map (MonoidHom.mulSingle H k),
      (commutator (H k)).map (MonoidHom.mulSingle H k)⁆ =
      (commutator (H k)).map (MonoidHom.mulSingle H k)
    rcases hblk' k with h | h
    · rw [h, Subgroup.map_bot, Subgroup.commutator_bot_left]
    · have hperf : ⁅commutator (H k), commutator (H k)⁆ = commutator (H k) :=
        Subgroup.isPerfect_iff.mp ⟨h.1⟩
      rw [← Subgroup.map_commutator, hperf]
  have hleT : ∀ k, (T k).map θ ≤ StatedSU n (2 ^ 3) K := fun k =>
    k329u3c_factor_le_SU τ hτ hSUeq θ (hθrange.le.trans inf_le_right) (hT_perf k)
  let ι : Type := {k : Fin r // commutator (H k) ≠ ⊥}
  have : Fintype ι := Subtype.fintype _
  let Lf : ι → Subgroup ↥(StatedSU n (2 ^ 3) K) := fun i =>
    ((T i.val).map θ).subgroupOf (StatedSU n (2 ^ 3) K)
  have hLf_q : ∀ i : ι, CFSG.Open.IsQuasisimple ↥(Lf i) := fun i =>
    k329u3c_factor_quasisimple θ hθinj (hleT i.val) ((hblk' i.val).resolve_left i.2)
  have hLf_c : ∀ i j : ι, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥ := fun i j hij =>
    k329u3c_factors_commute θ hleT (fun h => hij (Subtype.ext h))
  have hLf_le : ∀ i : ι, Lf i ≤ K329Lres x := by
    intro i
    refine k329_perfect_le_res ?_ ?_
    · intro a ha
      refine (k329u3c_mem_centralizer_subtype (Subgroup.subtype (StatedSU n (2 ^ 3) K))
        (Subgroup.subtype_injective (StatedSU n (2 ^ 3) K)) x a).mpr ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have ha' : (a : GL (Fin n) K) ∈ (T i.val).map θ := Subgroup.mem_subgroupOf.mp ha
      have harange : (a : GL (Fin n) K) ∈ θ.range := by
        rw [MonoidHom.range_eq_map]
        exact Subgroup.map_mono le_top ha'
      rw [hθrange] at harange
      exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp harange).1
    · exact Subgroup.isPerfect_iff.mp ⟨(hLf_q i).1⟩
  have hsup_le : ⨆ i : ι, Lf i ≤ K329Lres x := iSup_le hLf_le
  have htriv : ∀ k : Fin r, ¬ commutator (H k) ≠ ⊥ →
      ((T k).map θ).subgroupOf (StatedSU n (2 ^ 3) K) = ⊥ := by
    intro k hk
    push Not at hk
    change (((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ).subgroupOf
      (StatedSU n (2 ^ 3) K) = ⊥
    rw [hk, Subgroup.map_bot, Subgroup.map_bot, Subgroup.bot_subgroupOf]
  have hjoin_eq : (⨆ k : Fin r, ((T k).map θ).subgroupOf (StatedSU n (2 ^ 3) K)) =
      ⨆ i : ι, Lf i := by
    have h := k329u3c_iSup_subtype_eq (fun k => commutator (H k) ≠ ⊥)
      (fun k => ((T k).map θ).subgroupOf (StatedSU n (2 ^ 3) K)) htriv
    simpa [Lf] using h
  have hsup_ge : K329Lres x ≤ ⨆ i : ι, Lf i := by
    calc K329Lres x
        = K329Res (Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K))) := rfl
      _ ≤ ⁅Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K)),
            Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K))⁆ :=
          k329_res_le_commutator _
      _ ≤ ⨆ k : Fin r, ((T k).map θ).subgroupOf (StatedSU n (2 ^ 3) K) :=
          k329u3c_centralizer_commutator_le_iSup τ hτ hSUeq θ hleT x
            (by simpa [C, s] using hθrange)
      _ = ⨆ i : ι, Lf i := hjoin_eq
  have hsup : ⨆ i : ι, Lf i = K329Lres x := le_antisymm hsup_le hsup_ge
  exact ⟨ι, inferInstance, Lf, hLf_q, hLf_c, hsup⟩

open CFSG.LieType.SemisimpleCentralizers.Held
open CFSG.ClassicalGroups.UnitaryFlag

private theorem k329u4_order {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) {s : GL (Fin n) K} (hn : 1 ≤ n)
    (hsU : s ∈ StatedSU n (2 ^ 3) K)
    (hs3 : s ^ 3 ∈ CFSG.Open.StatedScalars (Fin n) K) :
    (orderOf s : K) ≠ 0 := by
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hs3
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (2 ^ 3) K := by
    rw [hc]
    exact pow_mem hsU 3
  have h9 : c ^ 9 = 1 := by
    have h := (CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := 3)
      Nat.prime_two hK hn c).mp hsc
    norm_num at h
    exact h.2
  have hs27 : s ^ 27 = 1 := by
    have h : s ^ 27 = (s ^ 3) ^ 9 := by
      rw [show (27 : ℕ) = 3 * 9 by norm_num, pow_mul]
    rw [h, ← hc, ← map_pow, h9, map_one]
  have hdvd : orderOf s ∣ 27 := orderOf_dvd_of_pow_eq_one hs27
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 6)
    (by rw [hK]; norm_num)
  have : CharP K 2 := hchar
  intro h0
  have h2 : 2 ∣ orderOf s := (CharP.cast_eq_zero_iff K 2 (orderOf s)).mp h0
  have : 2 ∣ 27 := h2.trans hdvd
  norm_num at this

private theorem k329u4_card_ge_four {M : Type} [Nontrivial M] [Finite M] {k : ℕ}
    (hcard : Nat.card M = 2 ^ (3 * k)) : 4 ≤ Nat.card M := by
  have h2 : 2 ≤ Nat.card M := Finite.one_lt_card
  rw [hcard] at h2 ⊢
  have hk : 1 ≤ k := by
    by_contra h
    have : k = 0 := by omega
    subst this
    norm_num at h2
  calc 4 = 2 ^ 2 := by norm_num
    _ ≤ 2 ^ (3 * k) := Nat.pow_le_pow_right (by norm_num) (by omega)

private theorem k329u4_perfect_subgroup_commutator {G : Type} [Group G] {S T : Subgroup G}
    (hST : ⁅S, S⁆ = T) (hTT : ⁅T, T⁆ = T) :
    ⁅commutator ↥S, commutator ↥S⁆ = commutator ↥S := by
  apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
  have hc : (commutator ↥S).map S.subtype = T := by
    rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype, hST]
  rw [Subgroup.map_commutator, hc, hTT]

private theorem k329u4_map_commutator {G G' : Type} [Group G] [Group G'] (f : G ≃* G') :
    (commutator G).map f.toMonoidHom = commutator G' := by
  rw [_root_.commutator_def, _root_.commutator_def, Subgroup.map_commutator]
  simp [Subgroup.map_top_of_surjective, f.surjective]

private theorem k329u4_commutator_GL_eq_statedSL {b : ℕ} {M : Type} [Field M] [Finite M]
    (hb : 2 ≤ b) (h4 : 4 ≤ Nat.card M) :
    commutator (GL (Fin b) M) = CFSG.Open.StatedSL b M := by
  have hperf : Group.IsPerfect ↥(CFSG.Open.StatedSL b M) :=
    hct_isPerfect_statedSL M hb (Or.inr (by omega)) (Or.inr (by omega))
  apply le_antisymm
  · rw [_root_.commutator_def]
    exact Subgroup.commutator_le.mpr (fun x _ y _ => commutatorElement_mem_statedSL x y)
  · calc CFSG.Open.StatedSL b M = ⁅CFSG.Open.StatedSL b M, CFSG.Open.StatedSL b M⁆ :=
        (Subgroup.isPerfect_iff.1 hperf).symm
      _ ≤ ⁅(⊤ : Subgroup (GL (Fin b) M)), ⊤⁆ := Subgroup.commutator_mono le_top le_top
      _ = commutator (GL (Fin b) M) := rfl

private theorem k329u4_heldSU_perfect {a d : ℕ} {M : Type} [Field M] [Finite M]
    {τ : M ≃+* M} {hτ : ∀ x, τ (τ x) = x}
    (hodd : Odd d) (hτQ : ∀ x, τ x = x ^ ((2 ^ 3) ^ d))
    (hcard : Nat.card M = ((2 ^ 3) ^ d) ^ 2) (ha : 2 ≤ a) :
    Group.IsPerfect ↥(heldSU a M τ hτ) := by
  have hcard' : Nat.card M = (2 ^ (3 * d)) ^ 2 := by
    rw [hcard]
    congr 1
    rw [← pow_mul]
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP M 2 := CFSG.LieType.BorelTits.charP_of_natCard_eq (p := 2) (f := 2 * (3 * d))
    (by rw [hcard', ← pow_mul]; congr 1; ring)
  have hf : 2 ≤ 3 * d := by obtain ⟨k, hk⟩ := hodd; omega
  rw [hct_heldSU_eq_statedSU hτQ, ← pow_mul]
  exact (CFSG.ComponentClassification.RankTwoClassical.isQuasisimple_statedSU_of_two_le
    (K := M) (f := 3 * d) hcard' hf (k := a) ha).1

private theorem k329u4_commutator_heldGU_eq_heldSU {a d : ℕ} {M : Type} [Field M] [Finite M]
    {τ : M ≃+* M} {hτ : ∀ x, τ (τ x) = x}
    (hodd : Odd d) (hτQ : ∀ x, τ x = x ^ ((2 ^ 3) ^ d))
    (hcard : Nat.card M = ((2 ^ 3) ^ d) ^ 2) (ha : 2 ≤ a) :
    ⁅heldGU a M τ hτ, heldGU a M τ hτ⁆ = heldSU a M τ hτ := by
  have hperf := k329u4_heldSU_perfect (hτ := hτ) hodd hτQ hcard ha
  apply le_antisymm
  · exact Subgroup.commutator_le.mpr (fun x hx y hy => commutatorElement_mem_heldSU hx hy)
  · calc heldSU a M τ hτ = ⁅heldSU a M τ hτ, heldSU a M τ hτ⁆ :=
        (Subgroup.isPerfect_iff.1 hperf).symm
      _ ≤ ⁅heldGU a M τ hτ, heldGU a M τ hτ⁆ :=
        Subgroup.commutator_mono inf_le_left inf_le_left

private theorem k329u4_unitary_eq_scalar {a d : ℕ} {M : Type} [Field M] [Finite M]
    {τ : M ≃+* M} {hτ : ∀ x, τ (τ x) = x}
    (hodd : Odd d) (hτQ : ∀ x, τ x = x ^ ((2 ^ 3) ^ d))
    (hcard : Nat.card M = ((2 ^ 3) ^ d) ^ 2) (ha : 2 ≤ a)
    {g : GL (Fin a) M} (hg : ∀ x ∈ heldSU a M τ hτ, Commute g x) :
    ∃ lam : M, (g : Matrix (Fin a) (Fin a) M) = Matrix.scalar (Fin a) lam := by
  have hcard' : Nat.card M = (2 ^ (3 * d)) ^ 2 := by
    rw [hcard]
    congr 1
    rw [← pow_mul]
  let hE : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * d) M :=
    { prime := Nat.prime_two
      one_le := by obtain ⟨k, hk⟩ := hodd; omega
      card := by
        rw [hcard', ← pow_mul]
        congr 1
        ring }
  have hbar : hE.bar = τ.toRingHom := by
    ext x
    rw [hE.bar_apply]
    change x ^ 2 ^ (3 * d) = τ x
    rw [hτQ, ← pow_mul]
  have hbar_fn : (⇑hE.bar : M → M) = ⇑τ := by
    funext x
    have h := congrArg (fun f : M →+* M => f x) hbar
    simpa using h
  have hgram : gramSU hE (1 : Matrix (Fin a) (Fin a) M) = heldSU a M τ hτ := by
    ext z
    simp only [heldSU, Subgroup.mem_inf, mem_gramSU, mem_heldGU,
      CFSG.Open.StatedAPI.mem_statedSL_iff, hbar_fn, Matrix.mul_one]
  have hd1 : 1 ≤ d := by obtain ⟨k, hk⟩ := hodd; omega
  have hq : 2 ≤ 2 ^ (3 * d) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (3 * d) := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨lam, hlam⟩ :=
    CFSG.RankThree.PartOne.KCUnitary.exists_smul_one_of_commute_gramSU hE ha hq
      (M := (g : Matrix (Fin a) (Fin a) M))
      (fun A hA => by
        have h := (hg A (by rwa [hgram] at hA)).eq
        show (A : Matrix (Fin a) (Fin a) M) * (g : Matrix (Fin a) (Fin a) M) =
          (g : Matrix (Fin a) (Fin a) M) * (A : Matrix (Fin a) (Fin a) M)
        rw [← Units.val_mul, ← Units.val_mul, h])
  exact ⟨lam, by rw [hlam, Matrix.smul_one_eq_diagonal, Matrix.scalar_apply]⟩

private theorem k329u4_linear_eq_scalar {b : ℕ} {M : Type} [Field M]
    {g : GL (Fin b) M} (hg : ∀ x ∈ CFSG.Open.StatedSL b M, Commute g x) :
    ∃ lam : M, (g : Matrix (Fin b) (Fin b) M) = Matrix.scalar (Fin b) lam := by
  apply matrix_eq_scalar_of_commute_transvection
  intro i j hij
  have hT : Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.transvection hij 1)
      ∈ CFSG.Open.StatedSL b M := transvection_toGL_mem_statedSL hij 1
  have h := (hg _ hT).eq
  exact congrArg (fun z : GL (Fin b) M => (z : Matrix (Fin b) (Fin b) M)) h

private theorem k329u4_commutator_perfect {Γ : Type} [Group Γ]
    (hΓ : UnitaryOrLinearBlock (2 ^ 3) Γ) :
    ⁅commutator Γ, commutator Γ⁆ = commutator Γ := by
  rcases hΓ with ⟨a, d, M, hMF, hMfin, τ, hτ, hodd, hτQ, hcard, ⟨ε⟩⟩ |
      ⟨b, e, M, hMF, hMfin, hcard, ⟨ε⟩⟩
  · let : Field M := hMF
    let : Finite M := hMfin
    by_cases ha : 2 ≤ a
    · have hST := k329u4_commutator_heldGU_eq_heldSU (hτ := hτ) hodd hτQ hcard ha
      have hTT := Subgroup.isPerfect_iff.1 (k329u4_heldSU_perfect (hτ := hτ) hodd hτQ hcard ha)
      have hΓ' := k329u4_perfect_subgroup_commutator hST hTT
      apply Subgroup.map_injective (f := ε.toMonoidHom) (fun x y h => ε.injective h)
      rw [Subgroup.map_commutator, k329u4_map_commutator ε, hΓ']
    · have hab : ∀ x y : ↥(heldGU a M τ hτ), x * y = y * x := fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one (show a ≤ 1 by omega) (x : GL (Fin a) M)
          (y : GL (Fin a) M))
      have hΓ'bot : commutator ↥(heldGU a M τ hτ) = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      have hΓbot : commutator Γ = ⊥ := by
        apply Subgroup.map_injective (f := ε.toMonoidHom) (fun x y h => ε.injective h)
        rw [k329u4_map_commutator ε, hΓ'bot, Subgroup.map_bot]
      rw [hΓbot]
      simp
  · let : Field M := hMF
    let : Finite M := hMfin
    by_cases hb : 2 ≤ b
    · have h4 : 4 ≤ Nat.card M :=
        k329u4_card_ge_four (k := 2 * e) (by rw [hcard, ← pow_mul])
      have hcommGL : commutator (GL (Fin b) M) = CFSG.Open.StatedSL b M :=
        k329u4_commutator_GL_eq_statedSL hb h4
      have hperf : Group.IsPerfect ↥(CFSG.Open.StatedSL b M) :=
        hct_isPerfect_statedSL M hb (Or.inr (by omega)) (Or.inr (by omega))
      apply Subgroup.map_injective (f := ε.toMonoidHom) (fun x y h => ε.injective h)
      rw [Subgroup.map_commutator, k329u4_map_commutator ε, hcommGL,
        Subgroup.isPerfect_iff.1 hperf]
    · have hab : ∀ x y : GL (Fin b) M, x * y = y * x := fun x y =>
        mul_comm_GL_of_le_one (show b ≤ 1 by omega) x y
      have hbot : commutator (GL (Fin b) M) = ⊥ := by
        rw [_root_.commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro x _
        rw [Subgroup.mem_centralizer_iff]
        intro y _
        exact hab y x
      apply Subgroup.map_injective (f := ε.toMonoidHom) (fun x y h => ε.injective h)
      rw [Subgroup.map_commutator, k329u4_map_commutator ε, hbot]
      simp

private theorem k329u4_block_comm_of_comm_commutator {Γ : Type} [Group Γ]
    (hΓ : UnitaryOrLinearBlock (2 ^ 3) Γ) {c₁ c₂ : Γ}
    (h₁ : ∀ x ∈ commutator Γ, c₁ * x = x * c₁)
    (h₂ : ∀ x ∈ commutator Γ, c₂ * x = x * c₂) :
    c₁ * c₂ = c₂ * c₁ := by
  rcases hΓ with ⟨a, d, M, hMF, hMfin, τ, hτ, hodd, hτQ, hcard, ⟨ε⟩⟩ |
      ⟨b, e, M, hMF, hMfin, hcard, ⟨ε⟩⟩
  · let : Field M := hMF
    let : Finite M := hMfin
    by_cases ha : 2 ≤ a
    · let S : Subgroup (GL (Fin a) M) := heldGU a M τ hτ
      let T : Subgroup (GL (Fin a) M) := heldSU a M τ hτ
      have hTS : T ≤ S := fun x hx => (Subgroup.mem_inf.mp hx).1
      have hc : (commutator ↥S).map S.subtype = T := by
        rw [_root_.commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
          Subgroup.range_subtype]
        exact k329u4_commutator_heldGU_eq_heldSU (hτ := hτ) hodd hτQ hcard ha
      have hsub : commutator ↥S = T.subgroupOf S := by
        apply Subgroup.map_injective (f := S.subtype) S.subtype_injective
        rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hTS, hc]
      have hcommEq : (commutator Γ).map ε.toMonoidHom = T.subgroupOf S := by
        rw [k329u4_map_commutator ε, hsub]
      have hsc : ∀ c : Γ, (∀ x ∈ commutator Γ, c * x = x * c) →
          ∃ lam : M,
            ((ε c : GL (Fin a) M) : Matrix (Fin a) (Fin a) M) = Matrix.scalar (Fin a) lam := by
        intro c hcΓ
        refine k329u4_unitary_eq_scalar (τ := τ) (hτ := hτ) (g := (ε c : GL (Fin a) M))
          hodd hτQ hcard ha ?_
        intro y hy
        have hyS : y ∈ S := (Subgroup.mem_inf.mp hy).1
        have hy' : (⟨y, hyS⟩ : ↥S) ∈ (commutator Γ).map ε.toMonoidHom := by
          rw [hcommEq]
          exact Subgroup.mem_subgroupOf.mpr hy
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
        have hzy' : (ε.toMonoidHom z : GL (Fin a) M) = y := congrArg Subtype.val hzy
        rw [← hzy']
        exact (commute_iff_eq _ _).mpr (by
          have h := congrArg ε.toMonoidHom (hcΓ z hz)
          simpa only [map_mul, Subgroup.coe_mul, MulEquiv.coe_toMonoidHom]
            using congrArg Subtype.val h)
      obtain ⟨lam₁, hlam₁⟩ := hsc c₁ h₁
      obtain ⟨lam₂, hlam₂⟩ := hsc c₂ h₂
      apply ε.injective
      rw [map_mul, map_mul]
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hlam₁, hlam₂, ← map_mul, ← map_mul, mul_comm]
    · have hab : ∀ x y : ↥(heldGU a M τ hτ), x * y = y * x := fun x y =>
        Subtype.ext (mul_comm_GL_of_le_one (show a ≤ 1 by omega) (x : GL (Fin a) M)
          (y : GL (Fin a) M))
      exact ε.injective (by rw [map_mul, map_mul]; exact hab (ε c₁) (ε c₂))
  · let : Field M := hMF
    let : Finite M := hMfin
    by_cases hb : 2 ≤ b
    · have h4 : 4 ≤ Nat.card M :=
        k329u4_card_ge_four (k := 2 * e) (by rw [hcard, ← pow_mul])
      have hcommGL : commutator (GL (Fin b) M) = CFSG.Open.StatedSL b M :=
        k329u4_commutator_GL_eq_statedSL hb h4
      have hcommEq : (commutator Γ).map ε.toMonoidHom = CFSG.Open.StatedSL b M := by
        rw [k329u4_map_commutator ε, hcommGL]
      have hsc : ∀ c : Γ, (∀ x ∈ commutator Γ, c * x = x * c) →
          ∃ lam : M,
            ((ε c : GL (Fin b) M) : Matrix (Fin b) (Fin b) M) = Matrix.scalar (Fin b) lam := by
        intro c hcΓ
        refine k329u4_linear_eq_scalar (g := (ε c : GL (Fin b) M)) ?_
        intro y hy
        have hy' : y ∈ (commutator Γ).map ε.toMonoidHom := by rw [hcommEq]; exact hy
        obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy'
        rw [← hzy]
        exact (commute_iff_eq _ _).mpr (by
          have h := congrArg ε.toMonoidHom (hcΓ z hz)
          rw [map_mul, map_mul] at h
          exact h)
      obtain ⟨lam₁, hlam₁⟩ := hsc c₁ h₁
      obtain ⟨lam₂, hlam₂⟩ := hsc c₂ h₂
      apply ε.injective
      rw [map_mul, map_mul]
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, hlam₁, hlam₂, ← map_mul, ← map_mul, mul_comm]
    · have hab : ∀ x y : GL (Fin b) M, x * y = y * x := fun x y =>
        mul_comm_GL_of_le_one (show b ≤ 1 by omega) x y
      exact ε.injective (by rw [map_mul, map_mul]; exact hab (ε c₁) (ε c₂))

theorem k329_S4_PSU (n : ℕ) (hadm : StatedLieAdmissible .PSU n 2 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2) : K329SchurMatrix (StatedSU n (2 ^ 3) K) := by
  intro x hxZ hx3 R hRC hR3 hcomm a ha b hb
  have hn : 1 ≤ n := by have := hadm.2.2.1; omega
  let s : GL (Fin n) K := (x : GL (Fin n) K)
  have hsU : s ∈ StatedSU n (2 ^ 3) K := x.2
  have hs3 : s ^ 3 ∈ CFSG.Open.StatedScalars (Fin n) K := by
    have h := Subgroup.mem_subgroupOf.mp hx3
    simpa [s] using h
  have hord : (orderOf s : K) ≠ 0 := k329u4_order hK hn hsU hs3
  let hFU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K :=
    { prime := Nat.prime_two
      one_le := by norm_num
      card := by rw [hK]; norm_num }
  let τ : K ≃+* K := RingEquiv.ofRingHom hFU.bar hFU.bar
    (RingHom.ext hFU.bar_bar) (RingHom.ext hFU.bar_bar)
  have hτ : ∀ z, τ (τ z) = z := hFU.bar_bar
  have hτQ : ∀ z, τ z = z ^ (2 ^ 3) := hFU.bar_apply
  have hs_held : s ∈ heldSU n K τ hτ := by
    rw [hct_heldSU_eq_statedSU hτQ]
    exact hsU
  obtain ⟨r, H, hGrp, hFin, hBlock, ⟨e⟩⟩ :=
    unitaryCentralizerDecomposition_holds (Q := 2 ^ 3) (n := n) (L := K) τ hτ s hK hτQ
      hs_held hord
  let C : Subgroup (GL (Fin n) K) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ heldGU n K τ hτ
  let θ : (∀ k, H k) →* GL (Fin n) K := C.subtype.comp e.symm.toMonoidHom
  have hθinj : Function.Injective θ := fun p q h => e.symm.injective (Subtype.ext h)
  have hθrange : θ.range = C := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (e.symm w).2
    · intro hz
      refine ⟨e ⟨z, hz⟩, ?_⟩
      simp [θ]
  have hmem_C : ∀ y ∈ R, (y : GL (Fin n) K) ∈ C := by
    intro y hy
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg (fun g : ↥(StatedSU n (2 ^ 3) K) => (g : GL (Fin n) K))
        (Subgroup.mem_centralizer_singleton_iff.mp (hRC hy))
    · have hyS : (y : GL (Fin n) K) ∈ heldSU n K τ hτ := by
        rw [hct_heldSU_eq_statedSU hτQ]
        exact y.2
      exact (Subgroup.mem_inf.mp hyS).1
  have hmem_range : ∀ y ∈ R, (y : GL (Fin n) K) ∈ θ.range := by
    intro y hy
    rw [hθrange]
    exact hmem_C y hy
  obtain ⟨wa, hwa⟩ := MonoidHom.mem_range.mp (hmem_range a ha)
  obtain ⟨wb, hwb⟩ := MonoidHom.mem_range.mp (hmem_range b hb)
  let T : Fin r → Subgroup (∀ i, H i) := fun k =>
    (commutator (H k)).map (MonoidHom.mulSingle H k)
  have hT_le_GU : ∀ k, (T k).map θ ≤ heldGU n K τ hτ := fun k =>
    (Subgroup.map_le_range θ (T k)).trans (hθrange.le.trans inf_le_right)
  have hT_perf : ∀ k, ⁅(T k).map θ, (T k).map θ⁆ = (T k).map θ := by
    intro k
    have hmap : (T k).map θ =
        (commutator (H k)).map (θ.comp (MonoidHom.mulSingle H k)) := by
      change (((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ) = _
      rw [Subgroup.map_map]
    rw [hmap, ← Subgroup.map_commutator, k329u4_commutator_perfect (hBlock k)]
  have hT_le_SU : ∀ k, (T k).map θ ≤ StatedSU n (2 ^ 3) K := by
    intro k
    have hle : ⁅(T k).map θ, (T k).map θ⁆ ≤ heldSU n K τ hτ :=
      Subgroup.commutator_le.mpr (fun p hp q hq =>
        commutatorElement_mem_heldSU (hT_le_GU k hp) (hT_le_GU k hq))
    rw [hT_perf k] at hle
    rwa [hct_heldSU_eq_statedSU hτQ] at hle
  let Tk' : Fin r → Subgroup ↥(StatedSU n (2 ^ 3) K) := fun k =>
    ((T k).map θ).subgroupOf (StatedSU n (2 ^ 3) K)
  have hTk'_perf : ∀ k, ⁅Tk' k, Tk' k⁆ = Tk' k := by
    intro k
    apply Subgroup.map_injective (f := (StatedSU n (2 ^ 3) K).subtype)
      (Subgroup.subtype_injective (StatedSU n (2 ^ 3) K))
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hT_le_SU k), hT_perf k]
  have hTk'_cent : ∀ k, Tk' k ≤ Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K)) := by
    intro k t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have htGL : (t : GL (Fin n) K) ∈ (T k).map θ := Subgroup.mem_subgroupOf.mp ht
    have hrange : (t : GL (Fin n) K) ∈ θ.range := Subgroup.map_le_range θ (T k) htGL
    rw [hθrange] at hrange
    simpa [s] using Subgroup.mem_centralizer_singleton_iff.mp hrange.1
  have hTk'_res : ∀ k, Tk' k ≤ K329Lres x := fun k =>
    k329_perfect_le_res (hTk'_cent k) (hTk'_perf k)
  have hRL : R ≤ Subgroup.centralizer (K329Lres x : Set ↥(StatedSU n (2 ^ 3) K)) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hcomm_factor : ∀ (y : ↥(StatedSU n (2 ^ 3) K)) (hy : y ∈ R)
      (wy : ∀ i, H i) (hwy : θ wy = (y : GL (Fin n) K)) (k : Fin r)
      (t : H k), t ∈ commutator (H k) → wy k * t = t * wy k := by
    intro y hy wy hwy k t ht
    let u : ∀ i, H i := MonoidHom.mulSingle H k t
    have hu_mem : u ∈ T k := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    have hθu_mem : θ u ∈ (T k).map θ := Subgroup.mem_map.mpr ⟨u, hu_mem, rfl⟩
    have hθu_SU : θ u ∈ StatedSU n (2 ^ 3) K := hT_le_SU k hθu_mem
    let tt : ↥(StatedSU n (2 ^ 3) K) := ⟨θ u, hθu_SU⟩
    have htt_mem : tt ∈ Tk' k := by
      simp only [Tk', Subgroup.mem_subgroupOf]
      exact hθu_mem
    have htt_res : tt ∈ K329Lres x := hTk'_res k htt_mem
    have hca := Subgroup.mem_centralizer_iff.mp (hRL hy) tt htt_res
    have hca' : θ u * (y : GL (Fin n) K) = (y : GL (Fin n) K) * θ u := by
      have := congrArg (fun g : ↥(StatedSU n (2 ^ 3) K) => (g : GL (Fin n) K)) hca
      simpa [tt] using this
    have hca'' : u * wy = wy * u := by
      apply hθinj
      rw [map_mul, map_mul, hwy, hca']
    have := congrFun hca'' k
    simp only [Pi.mul_apply, u, MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] at this
    exact this.symm
  have hcoord : ∀ k, wa k * wb k = wb k * wa k := fun k =>
    k329u4_block_comm_of_comm_commutator (hBlock k)
      (fun t ht => hcomm_factor a ha wa hwa k t ht)
      (fun t ht => hcomm_factor b hb wb hwb k t ht)
  have hw : wa * wb = wb * wa := funext hcoord
  have hGL : (a : GL (Fin n) K) * (b : GL (Fin n) K) =
      (b : GL (Fin n) K) * (a : GL (Fin n) K) := by
    rw [← hwa, ← hwb, ← map_mul, ← map_mul, hw]
  apply Subtype.ext
  simpa only [Subgroup.coe_mul] using hGL

private theorem k329u5_twist {n : ℕ} {K : Type} [Field K] {H : Subgroup (GL (Fin n) K)}
    {x g : H} (hg : g ∈ K329Ct (K329Zh H) x) : x⁻¹ * g⁻¹ * x * g ∈ K329Zh H := by
  have h1 : QuotientGroup.mk' (K329Zh H) g ∈ Subgroup.centralizer
      ({(QuotientGroup.mk x : H ⧸ K329Zh H)} : Set (H ⧸ K329Zh H)) :=
    Subgroup.mem_comap.1 hg
  have h2 := Subgroup.mem_centralizer_iff.1 h1 (QuotientGroup.mk x) (Set.mem_singleton _)
  have h2' : QuotientGroup.mk (s := K329Zh H) (x * g) =
      QuotientGroup.mk (s := K329Zh H) (g * x) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
    rw [QuotientGroup.mk'_apply] at h2
    exact h2
  have hmem : (x * g)⁻¹ * (g * x) ∈ K329Zh H := QuotientGroup.eq.1 h2'
  have hinv : ((x * g)⁻¹ * (g * x))⁻¹ ∈ K329Zh H := Subgroup.inv_mem _ hmem
  convert hinv using 1
  group

private theorem k329u5_twist_eq {n : ℕ} {K : Type} [Field K] {H : Subgroup (GL (Fin n) K)}
    {x g : H} : g⁻¹ * x * g = x * (x⁻¹ * g⁻¹ * x * g) := by
  group

private theorem k329u5_omega_ne_one {n : ℕ} {K : Type} [Field K] {H : Subgroup (GL (Fin n) K)}
    {x g : H} (hgnc : g ∉ Subgroup.centralizer ({x} : Set H)) :
    x⁻¹ * g⁻¹ * x * g ≠ 1 := by
  intro h
  apply hgnc
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hyx : y = x := Set.mem_singleton_iff.1 hy
  rw [hyx]
  have h1 : g⁻¹ * x * g = x := by
    calc g⁻¹ * x * g = x * (x⁻¹ * g⁻¹ * x * g) := k329u5_twist_eq
      _ = x * 1 := by rw [h]
      _ = x := mul_one x
  have h2 : x * g = g * x := by
    have := congrArg (fun z => g * z) h1
    simpa [mul_assoc] using this
  exact h2

private theorem k329u5_omega_cube {n : ℕ} {K : Type} [Field K] {H : Subgroup (GL (Fin n) K)}
    {x g : H} (hg : g ∈ K329Ct (K329Zh H) x) (hx3 : x ^ 3 ∈ K329Zh H) :
    (x⁻¹ * g⁻¹ * x * g) ^ 3 = 1 := by
  set ω : H := x⁻¹ * g⁻¹ * x * g with hωdef
  have hωZ : ω ∈ K329Zh H := k329u5_twist hg
  have hωc : ω ∈ Subgroup.center H := k329_Zh_le_center H hωZ
  have hx3c : x ^ 3 ∈ Subgroup.center H := k329_Zh_le_center H hx3
  have hcomm : Commute x ω := Subgroup.mem_center_iff.1 hωc x
  have hgx : g⁻¹ * x * g = x * ω := by
    rw [hωdef]; exact k329u5_twist_eq
  have hcube : g⁻¹ * x ^ 3 * g = (g⁻¹ * x * g) ^ 3 := by
    rw [show g⁻¹ * x * g = g⁻¹ * x * (g⁻¹)⁻¹ by rw [inv_inv]]
    exact (conj_pow (a := g⁻¹) (b := x) (i := 3)).symm
  have h3 : g⁻¹ * x ^ 3 * g = x ^ 3 * ω ^ 3 := by
    rw [hcube, hgx, hcomm.mul_pow 3]
  have hx3g : g⁻¹ * x ^ 3 * g = x ^ 3 := by
    rw [mul_assoc, ← Subgroup.mem_center_iff.1 hx3c g, ← mul_assoc, inv_mul_cancel, one_mul]
  exact mul_left_cancel (h3.symm.trans (hx3g.trans (mul_one (x ^ 3)).symm))

private theorem k329u5_exists_scalar {n : ℕ} {K : Type} [Field K] {H : Subgroup (GL (Fin n) K)}
    {ω : H} (hω : ω ∈ K329Zh H) :
    ∃ a : Kˣ, Matrix.GeneralLinearGroup.scalar (Fin n) a = (ω : GL (Fin n) K) := by
  have h : (ω : GL (Fin n) K) ∈ CFSG.Open.StatedScalars (Fin n) K :=
    Subgroup.mem_subgroupOf.1 hω
  exact MonoidHom.mem_range.1 (by simpa [CFSG.Open.StatedScalars] using h)

private theorem k329u5_scalar_injective {n : ℕ} (hn : 0 < n) {K : Type} [Field K] :
    Function.Injective (Matrix.GeneralLinearGroup.scalar (Fin n) : Kˣ → GL (Fin n) K) := by
  intro a b hab
  apply Units.ext
  let i : Fin n := ⟨0, hn⟩
  have h := congrArg (fun M : GL (Fin n) K => (M : Matrix (Fin n) (Fin n) K) i i) hab
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h

private theorem k329u5_scalar_cube {n : ℕ} (hn : 0 < n) {K : Type} [Field K]
    {ω : ↥(StatedSU n (2 ^ 3) K)} {a : Kˣ}
    (ha : Matrix.GeneralLinearGroup.scalar (Fin n) a = (ω : GL (Fin n) K))
    (hω3 : (ω : ↥(StatedSU n (2 ^ 3) K)) ^ 3 = 1) : a ^ 3 = 1 := by
  have h1 : (Matrix.GeneralLinearGroup.scalar (Fin n) a) ^ 3 = 1 := by
    rw [ha]
    exact congrArg (fun z : ↥(StatedSU n (2 ^ 3) K) => (z : GL (Fin n) K)) hω3
  rw [← map_pow, map_eq_one_iff _ (k329u5_scalar_injective hn)] at h1
  exact h1

private theorem k329u5_scalar_ne_one {n : ℕ} {K : Type} [Field K]
    {ω : ↥(StatedSU n (2 ^ 3) K)} {a : Kˣ}
    (ha : Matrix.GeneralLinearGroup.scalar (Fin n) a = (ω : GL (Fin n) K))
    (hωne : (ω : ↥(StatedSU n (2 ^ 3) K)) ≠ 1) : a ≠ 1 := by
  intro ha1
  apply hωne
  apply Subtype.ext
  rw [← ha, ha1, map_one]
  rfl

private theorem k329u5_scalar_pow {n : ℕ} {K : Type} [Field K]
    {ω : ↥(StatedSU n (2 ^ 3) K)} {a : Kˣ}
    (ha : Matrix.GeneralLinearGroup.scalar (Fin n) a = (ω : GL (Fin n) K)) : a ^ n = 1 := by
  have hdet : Matrix.GeneralLinearGroup.det
      ((ω : ↥(StatedSU n (2 ^ 3) K)) : GL (Fin n) K) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply]
    exact CFSG.Open.StatedAPI.det_of_mem_statedSU ω.2
  rw [← ha, Matrix.GeneralLinearGroup.det_scalar] at hdet
  simpa using hdet

private theorem k329u5_trace_zero {n : ℕ} {K : Type} [Field K]
    {G S L : GL (Fin n) K} {a : K}
    (hcomm : (L : Matrix (Fin n) (Fin n) K) * (G : Matrix (Fin n) (Fin n) K) =
      (G : Matrix (Fin n) (Fin n) K) * (L : Matrix (Fin n) (Fin n) K))
    (hconj : (↑(G⁻¹) : Matrix (Fin n) (Fin n) K) * (S : Matrix (Fin n) (Fin n) K) *
      (G : Matrix (Fin n) (Fin n) K) = a • (S : Matrix (Fin n) (Fin n) K))
    (ha : a ≠ 1) :
    ((L : Matrix (Fin n) (Fin n) K) * (S : Matrix (Fin n) (Fin n) K)).trace = 0 := by
  have hunit : IsUnit ((G : Matrix (Fin n) (Fin n) K).det) := by
    rw [← Matrix.GeneralLinearGroup.val_det_apply]; exact Units.isUnit _
  have hconjL : (↑(G⁻¹) : Matrix (Fin n) (Fin n) K) * (L : Matrix (Fin n) (Fin n) K) *
      (G : Matrix (Fin n) (Fin n) K) = (L : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.coe_inv, mul_assoc, hcomm, ← mul_assoc,
      Matrix.nonsing_inv_mul _ hunit, one_mul]
  have hsplit : ((↑(G⁻¹) : Matrix (Fin n) (Fin n) K) * (L : Matrix (Fin n) (Fin n) K) *
        (G : Matrix (Fin n) (Fin n) K)) *
      ((↑(G⁻¹) : Matrix (Fin n) (Fin n) K) * (S : Matrix (Fin n) (Fin n) K) *
        (G : Matrix (Fin n) (Fin n) K)) =
      (↑(G⁻¹) : Matrix (Fin n) (Fin n) K) * ((L : Matrix (Fin n) (Fin n) K) *
        (S : Matrix (Fin n) (Fin n) K)) * (G : Matrix (Fin n) (Fin n) K) := by
    rw [Matrix.GeneralLinearGroup.coe_inv,
      show ((↑G)⁻¹ * (L : Matrix (Fin n) (Fin n) K) * (↑G)) *
          ((↑G)⁻¹ * (S : Matrix (Fin n) (Fin n) K) * (↑G)) =
        (↑G)⁻¹ * (L : Matrix (Fin n) (Fin n) K) * ((↑G) * (↑G)⁻¹) *
          (S : Matrix (Fin n) (Fin n) K) * (↑G) by noncomm_ring]
    rw [Matrix.mul_nonsing_inv _ hunit, mul_one]
    noncomm_ring
  have h1 : ((L : Matrix (Fin n) (Fin n) K) * (S : Matrix (Fin n) (Fin n) K)).trace =
      ((↑(G⁻¹) : Matrix (Fin n) (Fin n) K) * ((L : Matrix (Fin n) (Fin n) K) *
        (S : Matrix (Fin n) (Fin n) K)) * (G : Matrix (Fin n) (Fin n) K)).trace := by
    have hinv : (↑(G⁻¹) : Matrix (Fin n) (Fin n) K)⁻¹ = (↑G : Matrix (Fin n) (Fin n) K) := by
      rw [← Matrix.GeneralLinearGroup.coe_inv]
      exact congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) (inv_inv G)
    have h := Matrix.trace_conj (Units.isUnit (G⁻¹))
      ((L : Matrix (Fin n) (Fin n) K) * (S : Matrix (Fin n) (Fin n) K))
    rw [hinv] at h
    exact h.symm
  have h2 : (↑(G⁻¹) : Matrix (Fin n) (Fin n) K) * ((L : Matrix (Fin n) (Fin n) K) *
        (S : Matrix (Fin n) (Fin n) K)) * (G : Matrix (Fin n) (Fin n) K) =
      a • ((L : Matrix (Fin n) (Fin n) K) * (S : Matrix (Fin n) (Fin n) K)) := by
    rw [← hsplit, hconjL, hconj, Matrix.mul_smul]
  have h3 : ((L : Matrix (Fin n) (Fin n) K) * (S : Matrix (Fin n) (Fin n) K)).trace =
      a * ((L : Matrix (Fin n) (Fin n) K) * (S : Matrix (Fin n) (Fin n) K)).trace := by
    nth_rewrite 1 [h1]
    rw [h2, Matrix.trace_smul, smul_eq_mul]
  have h4 : (1 - a) * ((L : Matrix (Fin n) (Fin n) K) *
      (S : Matrix (Fin n) (Fin n) K)).trace = 0 := by
    rw [sub_mul, one_mul]
    exact sub_eq_zero.mpr h3
  rcases mul_eq_zero.1 h4 with h5 | h5
  · exact absurd (sub_eq_zero.mp h5).symm ha
  · exact h5

private theorem k329u5_three_dvd {n : ℕ} {K : Type} [Field K] [Finite K]
    (hadm : StatedLieAdmissible .PSU n 2 3)
    {x g : ↥(StatedSU n (2 ^ 3) K)}
    (hg : g ∈ K329Ct (K329Zh (StatedSU n (2 ^ 3) K)) x)
    (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (2 ^ 3) K))
    (hgnc : g ∉ Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K))) :
    3 ∣ n := by
  have hn : 0 < n := by have := hadm.2.2.1; omega
  let ω : ↥(StatedSU n (2 ^ 3) K) := x⁻¹ * g⁻¹ * x * g
  have hωZ : ω ∈ K329Zh (StatedSU n (2 ^ 3) K) := k329u5_twist hg
  have hωne : ω ≠ 1 := k329u5_omega_ne_one hgnc
  have hω3 : ω ^ 3 = 1 := k329u5_omega_cube hg hx3
  obtain ⟨a, ha⟩ := k329u5_exists_scalar hωZ
  have ha3 : a ^ 3 = 1 := k329u5_scalar_cube hn ha hω3
  have hane : a ≠ 1 := k329u5_scalar_ne_one ha hωne
  have han : a ^ n = 1 := k329u5_scalar_pow ha
  have hord : orderOf a = 3 := orderOf_eq_prime (p := 3) ha3 hane
  have := orderOf_dvd_of_pow_eq_one han
  rwa [hord] at this

section K329U5E

open Matrix

private def k329u5e_adj {K : Type} [Field K] {α β : Type} (τ : K ≃+* K)
    (M : Matrix α β K) : Matrix β α K :=
  (M.map τ)ᵀ

private theorem k329u5e_adj_mul {K : Type} [Field K] {α β γ : Type} [Fintype β]
    (τ : K ≃+* K) (M : Matrix α β K) (N : Matrix β γ K) :
    k329u5e_adj τ (M * N) = k329u5e_adj τ N * k329u5e_adj τ M := by
  ext i j
  simp [k329u5e_adj, Matrix.mul_apply, mul_comm]

private theorem k329u5e_adj_add {K : Type} [Field K] {α β : Type} (τ : K ≃+* K)
    (M N : Matrix α β K) :
    k329u5e_adj τ (M + N) = k329u5e_adj τ M + k329u5e_adj τ N := by
  ext i j
  simp [k329u5e_adj]

private theorem k329u5e_adj_sub {K : Type} [Field K] {α β : Type} (τ : K ≃+* K)
    (M N : Matrix α β K) :
    k329u5e_adj τ (M - N) = k329u5e_adj τ M - k329u5e_adj τ N := by
  ext i j
  simp [k329u5e_adj]

private theorem k329u5e_adj_one {K : Type} [Field K] {α : Type} [DecidableEq α] (τ : K ≃+* K) :
    k329u5e_adj τ (1 : Matrix α α K) = 1 := by
  ext i j
  by_cases h : i = j <;> simp [k329u5e_adj, Matrix.one_apply, h, eq_comm]

private theorem k329u5e_adj_adj {K : Type} [Field K] {α β : Type} (τ : K ≃+* K)
    (hτ : ∀ z, τ (τ z) = z) (M : Matrix α β K) :
    k329u5e_adj τ (k329u5e_adj τ M) = M := by
  ext i j
  simp [k329u5e_adj, hτ]

private def k329u5e_u {n : ℕ} {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (τ : K ≃+* K) (W : Matrix (Fin n) κ K) (D : Matrix κ κ K) : Matrix (Fin n) (Fin n) K :=
  1 + W * (D - 1) * k329u5e_adj τ W

private theorem k329u5e_u_one {n : ℕ} {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (τ : K ≃+* K) (W : Matrix (Fin n) κ K) : k329u5e_u τ W 1 = 1 := by
  simp [k329u5e_u]

private theorem k329u5e_u_mul {n : ℕ} {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (τ : K ≃+* K) {W : Matrix (Fin n) κ K} (hW : k329u5e_adj τ W * W = 1)
    (D D' : Matrix κ κ K) :
    k329u5e_u τ W D * k329u5e_u τ W D' = k329u5e_u τ W (D * D') := by
  have hWW : ∀ Y : Matrix κ (Fin n) K, k329u5e_adj τ W * (W * Y) = Y := fun Y => by
    rw [← Matrix.mul_assoc, hW, Matrix.one_mul]
  simp only [k329u5e_u, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul,
    Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_assoc, hWW]
  abel

private theorem k329u5e_u_adj {n : ℕ} {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (τ : K ≃+* K) (hτ : ∀ z, τ (τ z) = z) (W : Matrix (Fin n) κ K) (D : Matrix κ κ K) :
    k329u5e_adj τ (k329u5e_u τ W D) = k329u5e_u τ W (k329u5e_adj τ D) := by
  simp only [k329u5e_u, k329u5e_adj_add, k329u5e_adj_one, k329u5e_adj_mul, k329u5e_adj_sub,
    k329u5e_adj_adj τ hτ, Matrix.mul_assoc]

private theorem k329u5e_u_comm {n : ℕ} {K : Type} [Field K] {κ : Type} [Fintype κ] [DecidableEq κ]
    (τ : K ≃+* K) {W : Matrix (Fin n) κ K} {X : Matrix (Fin n) (Fin n) K} {T D : Matrix κ κ K}
    (hXW : X * W = W * T) (hWX : k329u5e_adj τ W * X = T * k329u5e_adj τ W)
    (hDT : D * T = T * D) :
    X * k329u5e_u τ W D = k329u5e_u τ W D * X := by
  have e1 : X * (W * (D - 1) * k329u5e_adj τ W) =
      W * (T * (D - 1)) * k329u5e_adj τ W := by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hXW, Matrix.mul_assoc W T]
  have e2 : (W * (D - 1) * k329u5e_adj τ W) * X =
      W * ((D - 1) * T) * k329u5e_adj τ W := by
    rw [Matrix.mul_assoc, hWX, ← Matrix.mul_assoc, ← Matrix.mul_assoc, Matrix.mul_assoc W]
  have e3 : T * (D - 1) = (D - 1) * T := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, hDT]
  unfold k329u5e_u
  rw [Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, Matrix.one_mul, e1, e2, e3]

private theorem k329u5e_u_trace {n : ℕ} {K : Type} [Field K] {κ : Type} [Fintype κ]
    [DecidableEq κ] (τ : K ≃+* K) {W : Matrix (Fin n) κ K} {X : Matrix (Fin n) (Fin n) K}
    {T : Matrix κ κ K} (hW : k329u5e_adj τ W * W = 1)
    (hWX : k329u5e_adj τ W * X = T * k329u5e_adj τ W) (D : Matrix κ κ K) :
    (k329u5e_u τ W D * X).trace = X.trace + ((D - 1) * T).trace := by
  unfold k329u5e_u
  rw [Matrix.add_mul, Matrix.one_mul, Matrix.trace_add]
  congr 1
  have e : W * (D - 1) * k329u5e_adj τ W * X =
      W * ((D - 1) * T * k329u5e_adj τ W) := by
    rw [Matrix.mul_assoc, hWX, Matrix.mul_assoc W (D - 1), Matrix.mul_assoc (D - 1) T]
  rw [e, Matrix.trace_mul_comm, Matrix.mul_assoc, hW, Matrix.mul_one]

private theorem k329u5e_trace_fromBlocks {K : Type} [Field K] {α : Type} [Fintype α]
    (A D : Matrix α α K) : (Matrix.fromBlocks A 0 0 D).trace = A.trace + D.trace := by
  simp [Matrix.trace, Fintype.sum_sum_type]

private theorem k329u5e_frame_elements {n : ℕ} {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (τ : K ≃+* K) (hτ : ∀ z, τ (τ z) = z) {X : Matrix (Fin n) (Fin n) K}
    (hXu : k329u5e_adj τ X * X = 1) {W₁ W₂ : Matrix (Fin n) ι K} {S C : Matrix ι ι K}
    (h11 : k329u5e_adj τ W₁ * W₁ = 1) (h22 : k329u5e_adj τ W₂ * W₂ = 1)
    (h12 : k329u5e_adj τ W₁ * W₂ = 0) (hX1 : X * W₁ = W₁ * S) (hX2 : X * W₂ = W₂ * S)
    (hCu : k329u5e_adj τ C * C = 1) (hCS : C * S = S * C) :
    ∃ A B : GL (Fin n) K, k329u5e_adj τ (A : Matrix (Fin n) (Fin n) K) * A = 1 ∧
      k329u5e_adj τ (B : Matrix (Fin n) (Fin n) K) * B = 1 ∧
      (A : Matrix (Fin n) (Fin n) K) * X = X * A ∧ (B : Matrix (Fin n) (Fin n) K) * X = X * B ∧
      (((A * B * A⁻¹ * B⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * X).trace =
        X.trace + ((C * S).trace + (k329u5e_adj τ C * S).trace - 2 * S.trace) := by
  classical
  set W : Matrix (Fin n) (ι ⊕ ι) K := Matrix.fromCols W₁ W₂ with hWdef
  set T : Matrix (ι ⊕ ι) (ι ⊕ ι) K := Matrix.fromBlocks S 0 0 S with hTdef
  have hadjW : k329u5e_adj τ W = Matrix.fromRows (k329u5e_adj τ W₁) (k329u5e_adj τ W₂) := by
    simp [hWdef, k329u5e_adj, Matrix.fromCols_map, Matrix.transpose_fromCols]
  have h21 : k329u5e_adj τ W₂ * W₁ = 0 := by
    have h := congrArg (k329u5e_adj τ) h12
    rw [k329u5e_adj_mul, k329u5e_adj_adj τ hτ] at h
    simpa [k329u5e_adj] using h
  have hW : k329u5e_adj τ W * W = 1 := by
    rw [hadjW, hWdef, Matrix.fromRows_mul_fromCols, h11, h12, h21, h22, Matrix.fromBlocks_one]
  have hXW : X * W = W * T := by
    rw [hWdef, hTdef, Matrix.mul_fromCols, Matrix.fromCols_mul_fromBlocks, hX1, hX2]
    simp
  have hTu : k329u5e_adj τ T * T = 1 := by
    have e1 : k329u5e_adj τ T * T = k329u5e_adj τ (W * T) * (W * T) := by
      rw [k329u5e_adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (k329u5e_adj τ W), hW,
        Matrix.one_mul]
    rw [e1, ← hXW, k329u5e_adj_mul, Matrix.mul_assoc, ← Matrix.mul_assoc (k329u5e_adj τ X), hXu,
      Matrix.one_mul, hW]
  have hTu' : T * k329u5e_adj τ T = 1 := mul_eq_one_comm.mp hTu
  have hXW' : k329u5e_adj τ X * W = W * k329u5e_adj τ T := by
    calc k329u5e_adj τ X * W = k329u5e_adj τ X * W * (T * k329u5e_adj τ T) := by
          rw [hTu', Matrix.mul_one]
      _ = k329u5e_adj τ X * (W * T) * k329u5e_adj τ T := by simp only [Matrix.mul_assoc]
      _ = k329u5e_adj τ X * (X * W) * k329u5e_adj τ T := by rw [hXW]
      _ = W * k329u5e_adj τ T := by
          rw [← Matrix.mul_assoc (k329u5e_adj τ X), hXu, Matrix.one_mul]
  have hWX : k329u5e_adj τ W * X = T * k329u5e_adj τ W := by
    have h := congrArg (k329u5e_adj τ) hXW'
    rwa [k329u5e_adj_mul, k329u5e_adj_mul, k329u5e_adj_adj τ hτ, k329u5e_adj_adj τ hτ] at h
  have hCC : C * k329u5e_adj τ C = 1 := mul_eq_one_comm.mp hCu
  set D₁ : Matrix (ι ⊕ ι) (ι ⊕ ι) K := Matrix.fromBlocks C 0 0 1 with hD₁
  set D₁' : Matrix (ι ⊕ ι) (ι ⊕ ι) K := Matrix.fromBlocks (k329u5e_adj τ C) 0 0 1 with hD₁'
  set D₂ : Matrix (ι ⊕ ι) (ι ⊕ ι) K := Matrix.fromBlocks 0 1 1 0 with hD₂
  have hD₁D₁' : D₁ * D₁' = 1 := by
    rw [hD₁, hD₁', Matrix.fromBlocks_multiply]
    simp [hCC, Matrix.fromBlocks_one]
  have hD₁'D₁ : D₁' * D₁ = 1 := by
    rw [hD₁, hD₁', Matrix.fromBlocks_multiply]
    simp [hCu, Matrix.fromBlocks_one]
  have hD₂D₂ : D₂ * D₂ = 1 := by
    rw [hD₂, Matrix.fromBlocks_multiply]
    simp [Matrix.fromBlocks_one]
  have hadjD₁ : k329u5e_adj τ D₁ = D₁' := by
    simp [hD₁, hD₁', k329u5e_adj, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
  have hadjD₂ : k329u5e_adj τ D₂ = D₂ := by
    simp [hD₂, k329u5e_adj, Matrix.fromBlocks_map, Matrix.fromBlocks_transpose]
  have hD₁T : D₁ * T = T * D₁ := by
    rw [hD₁, hTdef, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp [hCS]
  have hD₂T : D₂ * T = T * D₂ := by
    rw [hD₂, hTdef, Matrix.fromBlocks_multiply, Matrix.fromBlocks_multiply]
    simp
  have hA1 : k329u5e_u τ W D₁ * k329u5e_u τ W D₁' = 1 := by
    rw [k329u5e_u_mul τ hW, hD₁D₁', k329u5e_u_one]
  have hA2 : k329u5e_u τ W D₁' * k329u5e_u τ W D₁ = 1 := by
    rw [k329u5e_u_mul τ hW, hD₁'D₁, k329u5e_u_one]
  have hB1 : k329u5e_u τ W D₂ * k329u5e_u τ W D₂ = 1 := by
    rw [k329u5e_u_mul τ hW, hD₂D₂, k329u5e_u_one]
  refine ⟨⟨k329u5e_u τ W D₁, k329u5e_u τ W D₁', hA1, hA2⟩,
    ⟨k329u5e_u τ W D₂, k329u5e_u τ W D₂, hB1, hB1⟩, ?_, ?_, ?_, ?_, ?_⟩
  · show k329u5e_adj τ (k329u5e_u τ W D₁) * k329u5e_u τ W D₁ = 1
    rw [k329u5e_u_adj τ hτ, hadjD₁, k329u5e_u_mul τ hW, hD₁'D₁, k329u5e_u_one]
  · show k329u5e_adj τ (k329u5e_u τ W D₂) * k329u5e_u τ W D₂ = 1
    rw [k329u5e_u_adj τ hτ, hadjD₂, k329u5e_u_mul τ hW, hD₂D₂, k329u5e_u_one]
  · exact (k329u5e_u_comm τ hXW hWX hD₁T).symm
  · exact (k329u5e_u_comm τ hXW hWX hD₂T).symm
  · have hE : D₁ * D₂ * D₁' * D₂ = Matrix.fromBlocks C 0 0 (k329u5e_adj τ C) := by
      rw [hD₁, hD₂, hD₁']
      simp [Matrix.fromBlocks_multiply]
    have hcomm : ((((⟨k329u5e_u τ W D₁, k329u5e_u τ W D₁', hA1, hA2⟩ : GL (Fin n) K) *
        (⟨k329u5e_u τ W D₂, k329u5e_u τ W D₂, hB1, hB1⟩ : GL (Fin n) K) *
        (⟨k329u5e_u τ W D₁, k329u5e_u τ W D₁', hA1, hA2⟩ : GL (Fin n) K)⁻¹ *
        (⟨k329u5e_u τ W D₂, k329u5e_u τ W D₂, hB1, hB1⟩ : GL (Fin n) K)⁻¹ : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K)) =
        k329u5e_u τ W D₁ * k329u5e_u τ W D₂ * k329u5e_u τ W D₁' * k329u5e_u τ W D₂ := rfl
    rw [hcomm, k329u5e_u_mul τ hW, k329u5e_u_mul τ hW, k329u5e_u_mul τ hW, hE,
      k329u5e_u_trace τ hW hWX]
    have hET : (Matrix.fromBlocks C 0 0 (k329u5e_adj τ C) - 1) * T =
        Matrix.fromBlocks (C * S) 0 0 (k329u5e_adj τ C * S) - T := by
      rw [Matrix.sub_mul, Matrix.one_mul, hTdef, Matrix.fromBlocks_multiply]
      simp
    rw [hET, Matrix.trace_sub, k329u5e_trace_fromBlocks, hTdef, k329u5e_trace_fromBlocks, two_mul]


private theorem k329u5e_comm_mem_Lres {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (hn : 1 ≤ n) (τ : K ≃+* K) (hτ : ∀ z, τ (τ z) = z)
    (hτQ : ∀ z, τ z = z ^ (2 ^ 3)) {x : ↥(StatedSU n (2 ^ 3) K)}
    (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (2 ^ 3) K)) {A B : GL (Fin n) K}
    (hA : A ∈ Subgroup.centralizer ({(x : GL (Fin n) K)} : Set (GL (Fin n) K)) ⊓
      heldGU n K τ hτ)
    (hB : B ∈ Subgroup.centralizer ({(x : GL (Fin n) K)} : Set (GL (Fin n) K)) ⊓
      heldGU n K τ hτ) :
    ∃ l ∈ K329Lres x, (l : GL (Fin n) K) = A * B * A⁻¹ * B⁻¹ := by
  let s : GL (Fin n) K := (x : GL (Fin n) K)
  have hsU : s ∈ StatedSU n (2 ^ 3) K := x.2
  have hs3 : s ^ 3 ∈ CFSG.Open.StatedScalars (Fin n) K := by
    have h := Subgroup.mem_subgroupOf.mp hx3
    simpa [s] using h
  have hord : (orderOf s : K) ≠ 0 := k329u4_order hK hn hsU hs3
  have hs_held : s ∈ heldSU n K τ hτ := by
    rw [hct_heldSU_eq_statedSU hτQ]
    exact hsU
  obtain ⟨r, H, hGrp, hFin, hBlock, ⟨e⟩⟩ :=
    unitaryCentralizerDecomposition_holds (Q := 2 ^ 3) (n := n) (L := K) τ hτ s hK hτQ
      hs_held hord
  let C : Subgroup (GL (Fin n) K) :=
    Subgroup.centralizer ({s} : Set (GL (Fin n) K)) ⊓ heldGU n K τ hτ
  let θ : (∀ k, H k) →* GL (Fin n) K := C.subtype.comp e.symm.toMonoidHom
  have hθrange : θ.range = C := by
    ext z
    constructor
    · rintro ⟨w, rfl⟩
      exact (e.symm w).2
    · intro hz
      refine ⟨e ⟨z, hz⟩, ?_⟩
      simp [θ]
  let T : Fin r → Subgroup (∀ i, H i) := fun k =>
    (commutator (H k)).map (MonoidHom.mulSingle H k)
  have hT_le_GU : ∀ k, (T k).map θ ≤ heldGU n K τ hτ := fun k =>
    (Subgroup.map_le_range θ (T k)).trans (hθrange.le.trans inf_le_right)
  have hT_perf : ∀ k, ⁅(T k).map θ, (T k).map θ⁆ = (T k).map θ := by
    intro k
    have hmap : (T k).map θ =
        (commutator (H k)).map (θ.comp (MonoidHom.mulSingle H k)) := by
      change (((commutator (H k)).map (MonoidHom.mulSingle H k)).map θ) = _
      rw [Subgroup.map_map]
    rw [hmap, ← Subgroup.map_commutator, k329u4_commutator_perfect (hBlock k)]
  have hT_le_SU : ∀ k, (T k).map θ ≤ StatedSU n (2 ^ 3) K := by
    intro k
    have hle : ⁅(T k).map θ, (T k).map θ⁆ ≤ heldSU n K τ hτ :=
      Subgroup.commutator_le.mpr (fun p hp q hq =>
        commutatorElement_mem_heldSU (hT_le_GU k hp) (hT_le_GU k hq))
    rw [hT_perf k] at hle
    rwa [hct_heldSU_eq_statedSU hτQ] at hle
  let Tk' : Fin r → Subgroup ↥(StatedSU n (2 ^ 3) K) := fun k =>
    ((T k).map θ).subgroupOf (StatedSU n (2 ^ 3) K)
  have hTk'_perf : ∀ k, ⁅Tk' k, Tk' k⁆ = Tk' k := by
    intro k
    apply Subgroup.map_injective (f := (StatedSU n (2 ^ 3) K).subtype)
      (Subgroup.subtype_injective (StatedSU n (2 ^ 3) K))
    rw [Subgroup.map_commutator, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr (hT_le_SU k), hT_perf k]
  have hTk'_cent : ∀ k, Tk' k ≤ Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K)) := by
    intro k t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    have htGL : (t : GL (Fin n) K) ∈ (T k).map θ := Subgroup.mem_subgroupOf.mp ht
    have hrange : (t : GL (Fin n) K) ∈ θ.range := Subgroup.map_le_range θ (T k) htGL
    rw [hθrange] at hrange
    simpa [s] using Subgroup.mem_centralizer_singleton_iff.mp hrange.1
  have hTk'_res : ∀ k, Tk' k ≤ K329Lres x := fun k =>
    k329_perfect_le_res (hTk'_cent k) (hTk'_perf k)
  have hsingle : ∀ (k : Fin r) (t : H k), t ∈ commutator (H k) →
      θ (Pi.mulSingle k t) ∈ (K329Lres x).map (StatedSU n (2 ^ 3) K).subtype := by
    intro k t ht
    let u : ∀ i, H i := MonoidHom.mulSingle H k t
    have hu_mem : u ∈ T k := Subgroup.mem_map.mpr ⟨t, ht, rfl⟩
    have hθu_mem : θ u ∈ (T k).map θ := Subgroup.mem_map.mpr ⟨u, hu_mem, rfl⟩
    have hθu_SU : θ u ∈ StatedSU n (2 ^ 3) K := hT_le_SU k hθu_mem
    have htt_mem : (⟨θ u, hθu_SU⟩ : ↥(StatedSU n (2 ^ 3) K)) ∈ Tk' k := by
      simp only [Tk', Subgroup.mem_subgroupOf]
      exact hθu_mem
    exact ⟨⟨θ u, hθu_SU⟩, hTk'_res k htt_mem, rfl⟩
  obtain ⟨wa, hwa⟩ := MonoidHom.mem_range.mp (show A ∈ θ.range by rw [hθrange]; exact hA)
  obtain ⟨wb, hwb⟩ := MonoidHom.mem_range.mp (show B ∈ θ.range by rw [hθrange]; exact hB)
  have hmem : θ (wa * wb * wa⁻¹ * wb⁻¹) ∈
      (K329Lres x).map (StatedSU n (2 ^ 3) K).subtype := by
    have hmem' : (wa * wb * wa⁻¹ * wb⁻¹ : ∀ i, H i) ∈
        ((K329Lres x).map (StatedSU n (2 ^ 3) K).subtype).comap θ := by
      classical
      apply Subgroup.pi_mem_of_mulSingle_mem
      intro k
      apply hsingle k
      simp only [Pi.mul_apply, Pi.inv_apply]
      rw [_root_.commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top (wa k))
        (Subgroup.mem_top (wb k))
    exact hmem'
  obtain ⟨l, hl, hlθ⟩ := Subgroup.mem_map.mp hmem
  refine ⟨l, hl, ?_⟩
  rw [← hwa, ← hwb]
  simp only [map_mul, map_inv] at hlθ
  exact hlθ

private theorem k329u5e_unitary {n : ℕ} {K : Type} [Field K] (τ : K ≃+* K)
    (hτ : ∀ z, τ (τ z) = z) (hτQ : ∀ z, τ z = z ^ (2 ^ 3)) (x : ↥(StatedSU n (2 ^ 3) K)) :
    k329u5e_adj τ ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) = 1 := by
  have hx : (x : GL (Fin n) K) ∈ heldSU n K τ hτ := by
    rw [hct_heldSU_eq_statedSU hτQ]
    exact x.2
  exact mem_heldGU.mp (Subgroup.mem_inf.mp hx).1

private theorem k329u5e_cube_scalar {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (hn : 1 ≤ n) {x : ↥(StatedSU n (2 ^ 3) K)}
    (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (2 ^ 3) K)) :
    ∃ lam : K, ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
      lam • (1 : Matrix (Fin n) (Fin n) K) ∧ lam ^ 9 = 1 := by
  obtain ⟨c, hc⟩ := k329u5_exists_scalar hx3
  have hsc : Matrix.GeneralLinearGroup.scalar (Fin n) c ∈ StatedSU n (2 ^ 3) K := by
    rw [hc]
    exact (x ^ 3).2
  have h9 : c ^ 9 = 1 := by
    have h := (CFSG.LinearGroups.scalar_mem_statedSU_iff (p := 2) (f := 3)
      Nat.prime_two hK hn c).mp hsc
    norm_num at h
    exact h.2
  refine ⟨(c : K), ?_, by simpa using congrArg Units.val h9⟩
  have h := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) hc
  simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.smul_one_eq_diagonal,
    Matrix.scalar_apply] using h.symm

private theorem k329u5e_pow_nine_iff {n : ℕ} {K : Type} [Field K] (hn : 1 ≤ n)
    {x : ↥(StatedSU n (2 ^ 3) K)} {lam : K}
    (hX3 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 3 =
      lam • (1 : Matrix (Fin n) (Fin n) K)) :
    x ^ 9 = 1 ↔ lam ^ 3 = 1 := by
  have h9 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 9 =
      lam ^ 3 • (1 : Matrix (Fin n) (Fin n) K) := by
    rw [show (9 : ℕ) = 3 * 3 by norm_num, pow_mul, hX3, smul_pow, one_pow]
  constructor
  · intro h
    have h1 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 9 = 1 := by
      have := congrArg (fun z : ↥(StatedSU n (2 ^ 3) K) =>
        ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) h
      simpa using this
    rw [h1] at h9
    have := congrFun (congrFun h9 ⟨0, hn⟩) ⟨0, hn⟩
    simpa using this.symm
  · intro h
    apply Subtype.ext
    apply Units.ext
    have h1 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) ^ 9 = 1 := by
      rw [h9, h, one_smul]
    simpa using h1

private theorem k329u5e_twist_data {n : ℕ} {K : Type} [Field K] [Finite K] (hn : 0 < n)
    {x g : ↥(StatedSU n (2 ^ 3) K)}
    (hg : g ∈ K329Ct (K329Zh (StatedSU n (2 ^ 3) K)) x)
    (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (2 ^ 3) K))
    (hgnc : g ∉ Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K))) :
    ∃ a : K, a ^ 3 = 1 ∧ a ≠ 1 ∧
      (↑((g : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        a • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) := by
  have hωZ : x⁻¹ * g⁻¹ * x * g ∈ K329Zh (StatedSU n (2 ^ 3) K) := k329u5_twist hg
  have hωne : x⁻¹ * g⁻¹ * x * g ≠ 1 := k329u5_omega_ne_one hgnc
  have hω3 : (x⁻¹ * g⁻¹ * x * g) ^ 3 = 1 := k329u5_omega_cube hg hx3
  obtain ⟨a, ha⟩ := k329u5_exists_scalar hωZ
  have ha3 : a ^ 3 = 1 := k329u5_scalar_cube hn ha hω3
  have hane : a ≠ 1 := k329u5_scalar_ne_one ha hωne
  refine ⟨(a : K), by simpa using congrArg Units.val ha3, fun h => hane (Units.ext h), ?_⟩
  have hgx : g⁻¹ * x * g = x * (x⁻¹ * g⁻¹ * x * g) := k329u5_twist_eq
  generalize x⁻¹ * g⁻¹ * x * g = ω at ha hgx
  have h := congrArg (fun z : ↥(StatedSU n (2 ^ 3) K) =>
    ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) hgx
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul] at h
  rw [h, ← ha]
  simp [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal]

private theorem k329u5e_contra {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (hn : 1 ≤ n) (τ : K ≃+* K) (hτ : ∀ z, τ (τ z) = z)
    (hτQ : ∀ z, τ z = z ^ (2 ^ 3)) {x g : ↥(StatedSU n (2 ^ 3) K)}
    (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (2 ^ 3) K))
    (hgc : ∀ l ∈ K329Lres x, g * l = l * g) {a : K} (ha : a ≠ 1)
    (hconj : (↑((g : GL (Fin n) K)⁻¹) : Matrix (Fin n) (Fin n) K) *
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
        ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        a • ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K))
    {ι : Type} [Fintype ι] [DecidableEq ι] {W₁ W₂ : Matrix (Fin n) ι K} {S C : Matrix ι ι K}
    (h11 : k329u5e_adj τ W₁ * W₁ = 1) (h22 : k329u5e_adj τ W₂ * W₂ = 1)
    (h12 : k329u5e_adj τ W₁ * W₂ = 0)
    (hX1 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * W₁ = W₁ * S)
    (hX2 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * W₂ = W₂ * S)
    (hCu : k329u5e_adj τ C * C = 1) (hCS : C * S = S * C)
    (hval : (C * S).trace + (k329u5e_adj τ C * S).trace - 2 * S.trace ≠ 0) : False := by
  obtain ⟨A, B, hAu, hBu, hAX, hBX, htr⟩ :=
    k329u5e_frame_elements τ hτ (k329u5e_unitary τ hτ hτQ x) h11 h22 h12 hX1 hX2 hCu hCS
  have hmemC : ∀ M : GL (Fin n) K, k329u5e_adj τ (M : Matrix (Fin n) (Fin n) K) * M = 1 →
      (M : Matrix (Fin n) (Fin n) K) * ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * M →
      M ∈ Subgroup.centralizer ({(x : GL (Fin n) K)} : Set (GL (Fin n) K)) ⊓
        heldGU n K τ hτ := by
    intro M hMu hMX
    refine Subgroup.mem_inf.mpr ⟨?_, hMu⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact hMX
  obtain ⟨l, hl, hlAB⟩ :=
    k329u5e_comm_mem_Lres hK hn τ hτ hτQ hx3 (hmemC A hAu hAX) (hmemC B hBu hBX)
  have hcomm : ((l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (l : GL (Fin n) K) := by
    have h := congrArg (fun z : ↥(StatedSU n (2 ^ 3) K) =>
      ((z : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)) (hgc l hl)
    simpa only [Subgroup.coe_mul, Units.val_mul] using h.symm
  have h1 : (((l : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *
      ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)).trace = 0 :=
    k329u5_trace_zero (G := (g : GL (Fin n) K)) (S := (x : GL (Fin n) K))
      (L := (l : GL (Fin n) K)) hcomm hconj ha
  have h0 : ((x : GL (Fin n) K) : Matrix (Fin n) (Fin n) K).trace = 0 := by
    simpa using k329u5_trace_zero (G := (g : GL (Fin n) K)) (S := (x : GL (Fin n) K))
      (L := (1 : GL (Fin n) K)) (by simp) hconj ha
  rw [hlAB, htr, h0, zero_add] at h1
  exact hval h1

private theorem k329u5c_cube_root {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) {lam : K} (hlam : lam ^ 3 = 1) :
    ∃ ν : K, ν ^ 3 = lam := by
  have hlam0 : lam ≠ 0 := by
    rintro rfl
    simp at hlam
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Kˣ)
  have hord : orderOf g = 63 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units, hK]
    norm_num
  simp_rw [← mem_powers_iff_mem_zpowers] at hg
  obtain ⟨j, hj⟩ : ∃ j : ℕ, g ^ j = Units.mk0 lam hlam0 := hg (Units.mk0 lam hlam0)
  have h3 : g ^ (j * 3) = 1 := by
    rw [pow_mul, hj]
    ext
    simp [hlam]
  have hdvd : 63 ∣ j * 3 := hord ▸ orderOf_dvd_of_pow_eq_one h3
  obtain ⟨m, hm⟩ : 21 ∣ j := by omega
  refine ⟨((g ^ (7 * m) : Kˣ) : K), ?_⟩
  have hcube : (g ^ (7 * m)) ^ 3 = Units.mk0 lam hlam0 := by
    rw [← pow_mul, ← hj, hm]
    congr 1
    ring
  simpa using congrArg Units.val hcube

private theorem k329u5c_pow_eight {K : Type} [Field K] {t : K} (ht : t ^ 3 = 1) :
    t ^ (2 ^ 3) = t ^ 2 := by
  calc t ^ (2 ^ 3) = (t ^ 3) ^ 2 * t ^ 2 := by ring
    _ = t ^ 2 := by rw [ht]; ring

private theorem k329u5c_selfAdj {K : Type} [Field K] [CharP K 2] {ι : Type} [Fintype ι]
    [DecidableEq ι] (σ : K →+* K) {B : Matrix ι ι K} (hB : (B.map σ)ᵀ * B = 1)
    (hB3 : B ^ 3 = 1) {t : K} (ht : t ^ 3 = 1) (hσ : σ t = t ^ 2) :
    ((CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t).map σ)ᵀ =
      CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t := by
  have ht4 : t ^ 4 = t := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, ht, one_mul]
  have hB4 : B ^ 4 = B := by
    rw [show (4 : ℕ) = 3 + 1 by norm_num, pow_succ, hB3, one_mul]
  have hBB2 : B * B ^ 2 = 1 := by rw [← pow_succ']; exact hB3
  have hBinv : (B.map σ)ᵀ = B ^ 2 := by
    calc (B.map σ)ᵀ = (B.map σ)ᵀ * (B * B ^ 2) := by rw [hBB2, Matrix.mul_one]
      _ = ((B.map σ)ᵀ * B) * B ^ 2 := by rw [Matrix.mul_assoc]
      _ = B ^ 2 := by rw [hB, Matrix.one_mul]
  have hmap : (CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t).map σ =
      1 + σ (t ^ 2) • B.map σ + σ t • (B.map σ) ^ 2 := by
    simp only [CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj,
      Matrix.map_add σ (map_add σ), Matrix.map_smul' σ (t ^ 2) B (map_mul σ),
      Matrix.map_smul' σ t (B ^ 2) (map_mul σ),
      Matrix.map_one σ (map_zero σ) (map_one σ), Matrix.map_pow]
  calc ((CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t).map σ)ᵀ
      = (1 + σ (t ^ 2) • B.map σ + σ t • (B.map σ) ^ 2)ᵀ := by rw [hmap]
    _ = 1 + σ (t ^ 2) • (B.map σ)ᵀ + σ t • ((B.map σ)ᵀ) ^ 2 := by
        simp only [Matrix.transpose_add, Matrix.transpose_smul, Matrix.transpose_pow,
          Matrix.transpose_one]
    _ = 1 + σ (t ^ 2) • B ^ 2 + σ t • (B ^ 2) ^ 2 := by rw [hBinv]
    _ = CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t := by
        rw [map_pow, hσ, CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj,
          show (t ^ 2) ^ 2 = t by rw [← pow_mul]; exact ht4,
          show (B ^ 2) ^ 2 = B by rw [← pow_mul]; exact hB4]
        abel

private theorem k329u5c_eigen_cols {K : Type} [Field K]
    (h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K) {n : ℕ}
    {B : Matrix (Fin n) (Fin n) K} (hB : (B.map h.bar)ᵀ * B = 1) (hB3 : B ^ 3 = 1)
    {t : K} (ht : t ^ 3 = 1) :
    ∃ (k : ℕ) (U : Matrix (Fin n) (Fin k) K), (U.map h.bar)ᵀ * U = 1 ∧ B * U = t • U ∧
      U * (U.map h.bar)ᵀ = CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t := by
  have : CharP K 2 := h.charP
  have hσt : h.bar t = t ^ 2 := by
    rw [h.bar_apply]
    exact k329u5c_pow_eight ht
  have hPa := k329u5c_selfAdj h.bar hB hB3 ht hσt
  have hPP := CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj_mul_self hB3 ht
  obtain ⟨k, U, hUU, hUUs⟩ :=
    CFSG.LieType.SemisimpleCentralizers.OrderThree.exists_orthonormal_cols h hPP hPa
  refine ⟨k, U, hUU, ?_, hUUs⟩
  have hPU : CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t * U = U := by
    rw [← hUUs, Matrix.mul_assoc, hUU, Matrix.mul_one]
  calc B * U = B * (CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t * U) := by
        rw [hPU]
    _ = (B * CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t) * U := by
        rw [Matrix.mul_assoc]
    _ = (t • CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t) * U := by
        rw [CFSG.LieType.SemisimpleCentralizers.OrderThree.mul_eigenProj hB3 ht]
    _ = t • (CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj B t * U) := by
        rw [Matrix.smul_mul]
    _ = t • U := by rw [hPU]

private theorem k329u5c_card_le {K : Type} [Field K] {n k₁ k₂ k₃ : ℕ} (σ : K →+* K)
    (U₁ : Matrix (Fin n) (Fin k₁) K) (U₂ : Matrix (Fin n) (Fin k₂) K)
    (U₃ : Matrix (Fin n) (Fin k₃) K)
    (h : U₁ * (U₁.map σ)ᵀ + U₂ * (U₂.map σ)ᵀ + U₃ * (U₃.map σ)ᵀ = 1) :
    n ≤ k₁ + k₂ + k₃ := by
  set U : Matrix (Fin n) (Fin k₁ ⊕ Fin k₂ ⊕ Fin k₃) K := fromCols U₁ (fromCols U₂ U₃) with hU
  have hUU : U * (U.map σ)ᵀ = 1 := by
    rw [hU, Matrix.fromCols_map, Matrix.fromCols_map, Matrix.transpose_fromCols,
      Matrix.transpose_fromCols, Matrix.fromCols_mul_fromRows, Matrix.fromCols_mul_fromRows,
      ← add_assoc]
    exact h
  have h1 : (U * (U.map σ)ᵀ).rank = n := by
    rw [hUU, Matrix.rank_one, Fintype.card_fin]
  have h2 := Matrix.rank_mul_le_left U (U.map σ)ᵀ
  have h3 := Matrix.rank_le_card_width U
  simp only [Fintype.card_sum, Fintype.card_fin] at h3
  omega

private theorem k329u5c_cols {n k : ℕ} {K : Type} [Field K] (σ : K →+* K) (hk : 2 ≤ k)
    (U : Matrix (Fin n) (Fin k) K) (hU : (U.map σ)ᵀ * U = 1)
    (X : Matrix (Fin n) (Fin n) K) (c : K) (hXU : X * U = c • U) :
    ∃ (W₁ W₂ : Matrix (Fin n) Unit K),
      (W₁.map σ)ᵀ * W₁ = 1 ∧ (W₂.map σ)ᵀ * W₂ = 1 ∧ (W₁.map σ)ᵀ * W₂ = 0 ∧
      X * W₁ = c • W₁ ∧ X * W₂ = c • W₂ := by
  let i₀ : Fin k := ⟨0, by omega⟩
  let i₁ : Fin k := ⟨1, hk⟩
  have hne : i₀ ≠ i₁ := by simp [i₀, i₁, Fin.ext_iff]
  let col : Fin k → Matrix (Fin n) Unit K := fun i => Matrix.of fun a _ => U a i
  have hgram : ∀ i j, ((col i).map σ)ᵀ * col j =
      Matrix.of fun _ _ => ((U.map σ)ᵀ * U) i j := by
    intro i j
    ext u v
    simp [Matrix.mul_apply, col]
  have hX : ∀ i, X * col i = c • col i := by
    intro i
    ext a u
    have := congrFun (congrFun hXU a) i
    simpa [Matrix.mul_apply, col] using this
  refine ⟨col i₀, col i₁, ?_, ?_, ?_, hX i₀, hX i₁⟩
  · rw [hgram, hU]
    ext u v
    simp
  · rw [hgram, hU]
    ext u v
    simp
  · rw [hgram, hU]
    ext u v
    simp [hne]

private theorem k329u5c_frame {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (τ : K ≃+* K) (hτ : ∀ z, τ (τ z) = z)
    (hτQ : ∀ z, τ z = z ^ (2 ^ 3)) (hn : 6 ≤ n)
    (X : Matrix (Fin n) (Fin n) K) (hXu : (X.map τ)ᵀ * X = 1)
    (lam : K) (hX3 : X ^ 3 = lam • (1 : Matrix (Fin n) (Fin n) K)) (hlam : lam ^ 3 = 1)
    (ω : K) (hω3 : ω ^ 3 = 1) (hω : ω ≠ 1) :
    ∃ (W₁ W₂ : Matrix (Fin n) Unit K) (ν : K), ν ^ 9 = 1 ∧
      (W₁.map τ)ᵀ * W₁ = 1 ∧ (W₂.map τ)ᵀ * W₂ = 1 ∧ (W₁.map τ)ᵀ * W₂ = 0 ∧
      X * W₁ = ν • W₁ ∧ X * W₂ = ν • W₂ := by
  have h : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K :=
    ⟨Nat.prime_two, by norm_num, by rw [hK]; norm_num⟩
  have : CharP K 2 := h.charP
  have hfun : (⇑τ : K → K) = ⇑h.bar := funext fun z => by rw [h.bar_apply, hτQ]
  rw [hfun] at hXu ⊢
  obtain ⟨ν₀, hν₀⟩ := k329u5c_cube_root hK hlam
  have hν₀0 : ν₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hν₀
    rw [← hν₀] at hlam
    simp at hlam
  have hν₀9 : ν₀ ^ 9 = 1 := by
    calc ν₀ ^ 9 = (ν₀ ^ 3) ^ 3 := by ring
      _ = 1 := by rw [hν₀, hlam]
  set B : Matrix (Fin n) (Fin n) K := ν₀⁻¹ • X with hBdef
  have hXB : X = ν₀ • B := by
    rw [hBdef, smul_smul, mul_inv_cancel₀ hν₀0, one_smul]
  have hB3 : B ^ 3 = 1 := by
    have hc : ν₀⁻¹ ^ 3 * lam = 1 := by
      rw [← hν₀, inv_pow, inv_mul_cancel₀ (pow_ne_zero 3 hν₀0)]
    rw [hBdef, smul_pow, hX3, smul_smul, hc, one_smul]
  have hB : (B.map h.bar)ᵀ * B = 1 := by
    have hτν : τ ν₀ = ν₀⁻¹ := by
      rw [hτQ]
      exact eq_inv_of_mul_eq_one_left (by rw [← hν₀9]; ring)
    have hbar : h.bar ν₀⁻¹ = ν₀ := by
      rw [← congrFun hfun ν₀⁻¹]
      calc τ ν₀⁻¹ = τ (τ ν₀) := by rw [hτν]
        _ = ν₀ := hτ ν₀
    have hc : h.bar ν₀⁻¹ * ν₀⁻¹ = 1 := by
      rw [hbar]
      exact mul_inv_cancel₀ hν₀0
    rw [hBdef, Matrix.map_smul' h.bar ν₀⁻¹ X (map_mul h.bar), Matrix.transpose_smul,
      Matrix.smul_mul, Matrix.mul_smul, smul_smul, hXu, hc, one_smul]
  have hω2 : (ω ^ 2) ^ 3 = 1 := by
    calc (ω ^ 2) ^ 3 = (ω ^ 3) ^ 2 := by ring
      _ = 1 := by rw [hω3, one_pow]
  have hωq : ω ^ 2 + ω + 1 = 0 := by
    have hfac : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by
      calc (ω - 1) * (ω ^ 2 + ω + 1) = ω ^ 3 - 1 := by ring
        _ = 0 := by rw [hω3, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hω)
  obtain ⟨k₁, U₁, hU₁, hBU₁, hP₁⟩ := k329u5c_eigen_cols h hB hB3 (t := 1) (one_pow 3)
  obtain ⟨k₂, U₂, hU₂, hBU₂, hP₂⟩ := k329u5c_eigen_cols h hB hB3 (t := ω) hω3
  obtain ⟨k₃, U₃, hU₃, hBU₃, hP₃⟩ := k329u5c_eigen_cols h hB hB3 (t := ω ^ 2) hω2
  have hsum : U₁ * (U₁.map h.bar)ᵀ + U₂ * (U₂.map h.bar)ᵀ + U₃ * (U₃.map h.bar)ᵀ = 1 := by
    rw [hP₁, hP₂, hP₃]
    exact CFSG.LieType.SemisimpleCentralizers.OrderThree.eigenProj_add hB3 hωq
  have hk := k329u5c_card_le h.bar U₁ U₂ U₃ hsum
  have hXU : ∀ {k : ℕ} (U : Matrix (Fin n) (Fin k) K) (t : K), B * U = t • U →
      X * U = (ν₀ * t) • U := by
    intro k U t hBU
    rw [hXB, Matrix.smul_mul, hBU, smul_smul]
  have hν9 : ∀ t : K, t ^ 3 = 1 → (ν₀ * t) ^ 9 = 1 := fun t ht => by
    calc (ν₀ * t) ^ 9 = ν₀ ^ 9 * (t ^ 3) ^ 3 := by ring
      _ = 1 := by rw [hν₀9, ht]; ring
  by_cases h₁ : 2 ≤ k₁
  · obtain ⟨W₁, W₂, h11, h22, h12, hX1, hX2⟩ :=
      k329u5c_cols h.bar h₁ U₁ hU₁ X (ν₀ * 1) (hXU U₁ 1 hBU₁)
    exact ⟨W₁, W₂, ν₀ * 1, hν9 1 (one_pow 3), h11, h22, h12, hX1, hX2⟩
  by_cases h₂ : 2 ≤ k₂
  · obtain ⟨W₁, W₂, h11, h22, h12, hX1, hX2⟩ :=
      k329u5c_cols h.bar h₂ U₂ hU₂ X (ν₀ * ω) (hXU U₂ ω hBU₂)
    exact ⟨W₁, W₂, ν₀ * ω, hν9 ω hω3, h11, h22, h12, hX1, hX2⟩
  by_cases h₃ : 2 ≤ k₃
  · obtain ⟨W₁, W₂, h11, h22, h12, hX1, hX2⟩ :=
      k329u5c_cols h.bar h₃ U₃ hU₃ X (ν₀ * ω ^ 2) (hXU U₃ (ω ^ 2) hBU₃)
    exact ⟨W₁, W₂, ν₀ * ω ^ 2, hν9 (ω ^ 2) hω2, h11, h22, h12, hX1, hX2⟩
  omega

private theorem k329u5_case_i {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (hn : 6 ≤ n)
    {x g : ↥(StatedSU n (2 ^ 3) K)}
    (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (2 ^ 3) K))
    (hg : g ∈ K329Ct (K329Zh (StatedSU n (2 ^ 3) K)) x)
    (hgc : ∀ l ∈ K329Lres x, g * l = l * g)
    (hgnc : g ∉ Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K)))
    (h9 : x ^ 9 = 1) : False := by
  have hn1 : 1 ≤ n := by omega
  let hFU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K :=
    { prime := Nat.prime_two
      one_le := by norm_num
      card := by rw [hK]; norm_num }
  let τ : K ≃+* K := RingEquiv.ofRingHom hFU.bar hFU.bar
    (RingHom.ext hFU.bar_bar) (RingHom.ext hFU.bar_bar)
  have hτ : ∀ z, τ (τ z) = z := hFU.bar_bar
  have hτQ : ∀ z, τ z = z ^ (2 ^ 3) := hFU.bar_apply
  have hchar : CharP K 2 := hFU.charP
  obtain ⟨lam, hX3, -⟩ := k329u5e_cube_scalar hK hn1 hx3
  have hlam3 : lam ^ 3 = 1 := (k329u5e_pow_nine_iff hn1 hX3).mp h9
  obtain ⟨a, ha3, hane, hconj⟩ := k329u5e_twist_data (by omega) hg hx3 hgnc
  obtain ⟨W₁, W₂, ν, hν9, h11, h22, h12, hX1, hX2⟩ :=
    k329u5c_frame hK τ hτ hτQ hn _ (k329u5e_unitary τ hτ hτQ x) lam hX3 hlam3 a ha3 hane
  have hν0 : ν ≠ 0 := by
    rintro rfl
    simp at hν9
  have hτa : τ a = a ^ 2 := by rw [hτQ]; exact k329u5c_pow_eight ha3
  have hsum : a ^ 2 + a + 1 = 0 := by
    have hfac : (a - 1) * (a ^ 2 + a + 1) = 0 := by
      calc (a - 1) * (a ^ 2 + a + 1) = a ^ 3 - 1 := by ring
        _ = 0 := by rw [ha3, sub_self]
    exact (mul_eq_zero.mp hfac).resolve_left (sub_ne_zero.mpr hane)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  refine k329u5e_contra hK hn1 τ hτ hτQ hx3 hgc hane hconj (ι := Unit)
    (S := ν • (1 : Matrix Unit Unit K)) (C := a • (1 : Matrix Unit Unit K)) h11 h22 h12 ?_ ?_ ?_
    ?_ ?_
  · rw [Matrix.mul_smul, Matrix.mul_one]
    exact hX1
  · rw [Matrix.mul_smul, Matrix.mul_one]
    exact hX2
  · ext u v
    have : τ a * a = 1 := by rw [hτa, ← pow_succ]; exact ha3
    simpa [k329u5e_adj, Matrix.mul_apply, Matrix.one_apply] using this
  · rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.mul_smul, Matrix.smul_mul]
  · intro h
    apply hν0
    simp [k329u5e_adj, Matrix.trace, hτa] at h
    linear_combination (-1 : K) * h + ν * hsum + (-ν) * h2

private def k329u5d_shift {K : Type} [Field K] (lam : K) : Matrix (Fin 3) (Fin 3) K :=
  !![0, 0, lam; 1, 0, 0; 0, 1, 0]

private theorem k329u5d_shift_unitary {K : Type} [Field K] (τ : K ≃+* K) (lam : K)
    (h : τ lam * lam = 1) :
    k329u5e_adj τ (k329u5d_shift lam) * k329u5d_shift lam = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [k329u5e_adj, k329u5d_shift, Matrix.mul_apply, Fin.sum_univ_three, h]

private theorem k329u5d_assemble {n : ℕ} {K : Type} [Field K] (τ : K ≃+* K)
    (X : Matrix (Fin n) (Fin n) K) (lam : K) (hX3 : X ^ 3 = lam • (1 : Matrix (Fin n) (Fin n) K))
    (e : Fin 2 → Fin n → K)
    (he : ∀ (i j : Fin 2) (k l : Fin 3),
      ∑ a, τ ((X ^ (k : ℕ) *ᵥ e i) a) * (X ^ (l : ℕ) *ᵥ e j) a =
        if i = j ∧ k = l then 1 else 0) :
    ∃ (W₁ W₂ : Matrix (Fin n) (Fin 3) K),
      (W₁.map τ)ᵀ * W₁ = 1 ∧ (W₂.map τ)ᵀ * W₂ = 1 ∧ (W₁.map τ)ᵀ * W₂ = 0 ∧
      X * W₁ = W₁ * k329u5d_shift lam ∧ X * W₂ = W₂ * k329u5d_shift lam := by
  let W : Fin 2 → Matrix (Fin n) (Fin 3) K := fun i => Matrix.of fun a k => (X ^ (k : ℕ) *ᵥ e i) a
  have hgram : ∀ i j, ((W i).map τ)ᵀ * W j = if i = j then 1 else 0 := by
    intro i j
    ext k l
    simp only [Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, W, Matrix.of_apply]
    rw [he]
    by_cases hij : i = j
    · subst hij
      simp [Matrix.one_apply]
    · simp [hij]
  have hshift : ∀ i, X * W i = W i * k329u5d_shift lam := by
    intro i
    ext a k
    have h1 : ∀ k : Fin 3, (X * W i) a k = (X ^ ((k : ℕ) + 1) *ᵥ e i) a := by
      intro k
      simp only [W, Matrix.mul_apply, Matrix.of_apply]
      rw [pow_succ', ← Matrix.mulVec_mulVec]
      rfl
    rw [h1]
    fin_cases k
    · simp [W, k329u5d_shift, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [W, k329u5d_shift, Matrix.mul_apply, Fin.sum_univ_three]
    · simp [W, k329u5d_shift, Matrix.mul_apply, Fin.sum_univ_three, hX3, Matrix.smul_mulVec,
        mul_comm]
  exact ⟨W 0, W 1, by simpa using hgram 0 0, by simpa using hgram 1 1, by simpa using hgram 0 1,
    hshift 0, hshift 1⟩

section K329U5D

open CFSG.LocalAnalysis.ComponentInitial CFSG.LieType.SemisimpleCentralizers.HeldUCD

private theorem k329u5d_pair {K F V : Type} [Field K] [Finite K] [Field F] [Finite F]
    [Algebra K F] [AddCommGroup V] [Module K V] [Module F V] [IsScalarTower K F V] {p f : ℕ}
    (hU : UnitaryFieldData p f F) (τ : K →+* K)
    (hρL : ∀ l : K, hU.bar (algebraMap K F l) = algebraMap K F (τ l))
    (h : V →ₛₗ[τ] V →ₗ[K] K) (hherm : ∀ x y, τ (h x y) = h y x)
    (hadj : ∀ (c : F) (x y : V), h (c • x) y = h x (hU.bar c • y))
    (hnd : ∀ x : V, (∀ y, h x y = 0) → x = 0)
    [FiniteDimensional F V] (hd : 2 ≤ Module.finrank F V) :
    ∃ e : Fin 2 → V, ∀ (i j : Fin 2) (c d : F),
      h (c • e i) (d • e j) = if i = j then Algebra.trace K F (hU.bar c * d) else 0 := by
  obtain ⟨B, hsymm, hsep, hrep⟩ := exists_trace_form hU.bar τ hU.bar_bar hρL h hherm hadj hnd
  obtain ⟨e0, he0⟩ := UnitaryFieldData.exists_orthonormal_basis hU (B := B)
    (LinearMap.isSymm_def.mpr hsymm) hsep
  refine ⟨fun i => e0 ⟨i, by omega⟩, fun i j c d => ?_⟩
  rw [hrep]
  have h1 := he0 ⟨i, by omega⟩ ⟨j, by omega⟩
  simp only [map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul]
  by_cases hij : i = j
  · subst hij
    simp at h1
    simp [h1, mul_comm]
  · have : (⟨i, by omega⟩ : Fin (Module.finrank F V)) ≠ ⟨j, by omega⟩ := by
      intro hh
      exact hij (Fin.ext (Fin.mk.inj hh))
    rw [if_neg this] at h1
    simp [h1, hij]

open Polynomial in
private theorem k329u5d_no_root {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2)
    (lam : K) (hlam9 : lam ^ 9 = 1) (hlam3 : lam ^ 3 ≠ 1) (y : K) : y ^ 3 ≠ lam := by
  intro hy
  have hy0 : y ≠ 0 := by
    rintro rfl
    have h0 : lam = 0 := by rw [← hy]; norm_num
    rw [h0] at hlam9
    norm_num at hlam9
  have := Fintype.ofFinite K
  have h63 : y ^ 63 = 1 := by
    have := FiniteField.pow_card_sub_one_eq_one y hy0
    rw [← Nat.card_eq_fintype_card, hK] at this
    simpa using this
  apply hlam3
  calc lam ^ 3 = lam ^ 3 * (lam ^ 9) ^ 2 := by rw [hlam9]; ring
    _ = (y ^ 3) ^ 21 := by rw [hy]; ring
    _ = 1 := by rw [← pow_mul]; exact h63

open Polynomial in
private theorem k329u5d_irred {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2)
    (lam : K) (hlam9 : lam ^ 9 = 1) (hlam3 : lam ^ 3 ≠ 1) :
    Irreducible (X ^ 3 - C lam : K[X]) := by
  apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
  · rw [Polynomial.natDegree_X_pow_sub_C]
    simp
  · intro x hx
    apply k329u5d_no_root hK lam hlam9 hlam3 x
    simpa [Polynomial.IsRoot, sub_eq_zero] using hx

private theorem k329u5d_trace_table {K F : Type} [Field K] [Finite K] [Field F] [Finite F]
    [Algebra K F] (hK : Nat.card K = (2 ^ 3) ^ 2) (hfr : Module.finrank K F = 3)
    (lam : K) (hlam9 : lam ^ 9 = 1) (hlam3 : lam ^ 3 ≠ 1)
    (r : F) (hr : r ^ 3 = algebraMap K F lam) (bar : F →+* F) (hbar : ∀ x, bar x = x ^ 2 ^ 9)
    (k l : Fin 3) :
    Algebra.trace K F (bar (r ^ (k : ℕ)) * r ^ (l : ℕ)) = if k = l then 1 else 0 := by
  have := Fintype.ofFinite K
  have h2 : (2 : K) = 0 := by
    have : CharP K 2 := charP_of_card_eq_prime_pow (f := 6)
      (by rw [← Nat.card_eq_fintype_card, hK]; norm_num)
    exact_mod_cast CharP.cast_eq_zero K 2
  have hr27 : r ^ 27 = 1 := by
    rw [show 27 = 3 * 9 by norm_num, pow_mul, hr, ← map_pow, hlam9, map_one]
  obtain ⟨ζ, hζdef⟩ : ∃ ζ : F, ζ = r ^ 9 := ⟨_, rfl⟩
  have hζ : ζ = algebraMap K F (lam ^ 3) := by
    rw [hζdef, show 9 = 3 * 3 by norm_num, pow_mul, hr, ← map_pow]
  have hζne : ζ ≠ 1 := by
    rw [hζ]
    intro h
    exact hlam3 ((algebraMap K F).injective (by rw [h, map_one]))
  have hζ3 : ζ ^ 3 = 1 := by rw [hζdef, ← pow_mul]; exact hr27
  have hζ1 : 1 + ζ + ζ ^ 2 = 0 := by
    have h : (ζ - 1) * (1 + ζ + ζ ^ 2) = 0 := by linear_combination hζ3
    rcases mul_eq_zero.mp h with h | h
    · exact absurd (sub_eq_zero.mp h) hζne
    · exact h
  have htr : ∀ s : ℕ, algebraMap K F (Algebra.trace K F (r ^ s)) =
      r ^ s * (1 + ζ ^ s + ζ ^ (2 * s)) := by
    intro s
    have e1 : (r ^ s) ^ 64 = r ^ s * ζ ^ s := by
      calc (r ^ s) ^ 64 = r ^ (s + 9 * s + 27 * (2 * s)) := by rw [← pow_mul]; congr 1; ring
        _ = r ^ s * ζ ^ s := by
          rw [pow_add, pow_add, pow_mul r 27 (2 * s), hr27, one_pow, mul_one, hζdef, ← pow_mul]
    have e2 : (r ^ s) ^ 4096 = r ^ s * ζ ^ (2 * s) := by
      calc (r ^ s) ^ 4096 = r ^ (s + 18 * s + 27 * (151 * s)) := by
            rw [← pow_mul]; congr 1; ring
        _ = r ^ s * ζ ^ (2 * s) := by
          rw [pow_add, pow_add, pow_mul r 27 (151 * s), hr27, one_pow, mul_one, hζdef, ← pow_mul,
            show 9 * (2 * s) = 18 * s by ring]
    rw [FiniteField.algebraMap_trace_eq_sum_pow, hfr, hK]
    simp only [Finset.sum_range_succ, Finset.sum_range_zero, zero_add]
    norm_num only
    rw [e1, e2]
    ring
  have hoff : ∀ s : ℕ, s % 3 ≠ 0 → Algebra.trace K F (r ^ s) = 0 := by
    intro s hs
    apply (algebraMap K F).injective
    rw [htr, map_zero]
    rcases (by omega : s % 3 = 1 ∨ s % 3 = 2) with h1 | h1
    · have h2s : (2 * s) % 3 = 2 := by omega
      rw [pow_eq_pow_mod s hζ3, pow_eq_pow_mod (2 * s) hζ3, h1, h2s, pow_one, hζ1, mul_zero]
    · have h2s : (2 * s) % 3 = 1 := by omega
      rw [pow_eq_pow_mod s hζ3, pow_eq_pow_mod (2 * s) hζ3, h1, h2s, pow_one]
      linear_combination r ^ s * hζ1
  have hbar_pow : ∀ k : ℕ, bar (r ^ k) = r ^ (512 * k) := by
    intro k
    rw [map_pow, hbar, ← pow_mul]
    norm_num
  rw [hbar_pow, ← pow_add]
  by_cases hkl : k = l
  · subst hkl
    have h1 : r ^ (512 * (k : ℕ) + k) = 1 := by
      rw [show 512 * (k : ℕ) + k = 27 * (19 * k) by ring, pow_mul, hr27, one_pow]
    rw [h1, if_pos rfl, ← map_one (algebraMap K F), Algebra.trace_algebraMap, hfr]
    simp only [nsmul_eq_mul, Nat.cast_ofNat, mul_one]
    linear_combination h2
  · rw [if_neg hkl]
    apply hoff
    have hkl' : (k : ℕ) ≠ l := fun h => hkl (Fin.ext h)
    have hk := k.2
    have hl := l.2
    omega

open Polynomial in
private noncomputable def k329u5d_psi {n : ℕ} {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : aeval M f = 0) : AdjoinRoot f →+* Matrix (Fin n) (Fin n) K :=
  Ideal.Quotient.lift (Ideal.span {f}) (aeval (R := K) M).toRingHom (by
    intro p hp
    obtain ⟨g, rfl⟩ := Ideal.mem_span_singleton.mp hp
    change aeval M (f * g) = 0
    rw [map_mul, hf, zero_mul])

open Polynomial in
private theorem k329u5d_psi_mk {n : ℕ} {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : aeval M f = 0) (q : K[X]) :
    k329u5d_psi M f hf (AdjoinRoot.mk f q) = aeval M q :=
  Ideal.Quotient.lift_mk _ _ _

open Polynomial in
private noncomputable def k329u5d_act {n : ℕ} {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : aeval M f = 0) : AdjoinRoot f →+* Module.End K (Fin n → K) :=
  (Matrix.toLinAlgEquiv' : Matrix (Fin n) (Fin n) K ≃ₐ[K] Module.End K (Fin n → K)).toAlgHom.toRingHom.comp
    (k329u5d_psi M f hf)

open Polynomial in
private theorem k329u5d_act_mk {n : ℕ} {K : Type} [Field K] (M : Matrix (Fin n) (Fin n) K)
    (f : K[X]) (hf : aeval M f = 0) (q : K[X]) (v : Fin n → K) :
    k329u5d_act M f hf (AdjoinRoot.mk f q) v = aeval M q *ᵥ v := by
  simp [k329u5d_act, k329u5d_psi_mk, Matrix.toLinAlgEquiv'_apply]

open Polynomial in
private theorem k329u5d_orbits_of_module {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (τ : K ≃+* K) (hτ : ∀ z, τ (τ z) = z)
    (hτQ : ∀ z, τ z = z ^ (2 ^ 3)) (hn : 6 ≤ n)
    (M : Matrix (Fin n) (Fin n) K) (hMu : (M.map τ)ᵀ * M = 1)
    (lam : K) (hM3 : M ^ 3 = lam • (1 : Matrix (Fin n) (Fin n) K))
    (hlam9 : lam ^ 9 = 1) (hlam3 : lam ^ 3 ≠ 1)
    (f : K[X]) (hfdef : f = X ^ 3 - C lam) [Fact (Irreducible f)]
    [Module (AdjoinRoot f) (Fin n → K)]
    (hsmul : ∀ (q : K[X]) (v : Fin n → K), AdjoinRoot.mk f q • v = aeval M q *ᵥ v) :
    ∃ e : Fin 2 → Fin n → K, ∀ (i j : Fin 2) (k l : Fin 3),
      ∑ a, τ ((M ^ (k : ℕ) *ᵥ e i) a) * (M ^ (l : ℕ) *ᵥ e j) a =
        if i = j ∧ k = l then 1 else 0 := by
  classical
  have hmonic : f.Monic := by rw [hfdef]; exact Polynomial.monic_X_pow_sub_C lam (by norm_num)
  have hf0 : f ≠ 0 := hmonic.ne_zero
  have : Module.Finite K (AdjoinRoot f) := hmonic.finite_adjoinRoot
  have : Finite (AdjoinRoot f) := Module.finite_of_finite K
  have hfr : Module.finrank K (AdjoinRoot f) = 3 := by
    rw [(AdjoinRoot.powerBasis hf0).finrank, AdjoinRoot.powerBasis_dim, hfdef,
      natDegree_X_pow_sub_C]
  have hcardF : Nat.card (AdjoinRoot f) = 2 ^ (2 * 9) := by
    rw [Module.natCard_eq_pow_finrank (K := K) (V := AdjoinRoot f), hfr, hK]
    norm_num
  have hU : UnitaryFieldData 2 9 (AdjoinRoot f) := ⟨Nat.prime_two, by norm_num, hcardF⟩
  have hroot3 : (AdjoinRoot.root f) ^ 3 = algebraMap K (AdjoinRoot f) lam := by
    have h0 : AdjoinRoot.mk f (X ^ 3 - C lam) = 0 := by rw [← hfdef]; exact AdjoinRoot.mk_self
    rw [map_sub, map_pow, AdjoinRoot.mk_X, AdjoinRoot.mk_C, sub_eq_zero] at h0
    exact h0
  have hroot27 : (AdjoinRoot.root f) ^ 27 = 1 := by
    rw [show 27 = 3 * 9 by norm_num, pow_mul, hroot3, ← map_pow, hlam9, map_one]
  have hbar_root : hU.bar (AdjoinRoot.root f) = AdjoinRoot.root f ^ (27 - 1) := by
    rw [UnitaryFieldData.bar_apply, pow_eq_pow_mod _ hroot27]
    norm_num
  have hρL : ∀ l : K,
      hU.bar (algebraMap K (AdjoinRoot f) l) = algebraMap K (AdjoinRoot f) (τ l) := by
    intro l
    have := Fintype.ofFinite K
    have hl64 : l ^ ((2 ^ 3) ^ 2) = l := by
      have := FiniteField.pow_card l
      rwa [← Nat.card_eq_fintype_card, hK] at this
    rw [UnitaryFieldData.bar_apply, ← map_pow, hτQ]
    congr 1
    calc l ^ 2 ^ 9 = (l ^ ((2 ^ 3) ^ 2)) ^ 8 := by rw [← pow_mul]; norm_num
      _ = l ^ 2 ^ 3 := by rw [hl64]; norm_num
  have hbar_mk : ∀ q : K[X],
      hU.bar (AdjoinRoot.mk f q) = AdjoinRoot.mk f (starP τ 27 q) := by
    intro q
    rw [← eval₂_starP τ 27 f q]
    have h1 : AdjoinRoot.mk f q = q.eval₂ (AdjoinRoot.of f) (AdjoinRoot.root f) := by
      rw [← AdjoinRoot.aeval_eq, Polynomial.aeval_def]
      rfl
    rw [h1, Polynomial.hom_eval₂, hbar_root]
    congr 1
    ext l
    exact hρL l
  have : IsScalarTower K (AdjoinRoot f) (Fin n → K) := ⟨by
    intro l c v
    induction c using AdjoinRoot.induction_on with
    | ih q =>
      rw [Algebra.smul_def (A := AdjoinRoot f) l, AdjoinRoot.algebraMap_eq, ← AdjoinRoot.mk_C,
        ← map_mul, hsmul, hsmul, map_mul, aeval_C, Algebra.algebraMap_eq_smul_one,
        smul_mul_assoc, one_mul, Matrix.smul_mulVec]⟩
  let h : (Fin n → K) →ₛₗ[(τ : K →+* K)] (Fin n → K) →ₗ[K] K :=
    LinearMap.mk₂'ₛₗ (τ : K →+* K) (RingHom.id K) (fun x y => hfm τ x y)
      (fun x x' y => hfm_add_left τ x x' y)
      (fun c x y => by rw [hfm_smul_left, smul_eq_mul]; rfl)
      (fun x y y' => hfm_add_right τ x y y')
      (fun c x y => by rw [hfm_smul_right, RingHom.id_apply, smul_eq_mul])
  have happ : ∀ x y, h x y = hfm τ x y := fun x y => rfl
  have hM27 : M ^ 27 = 1 := by
    rw [show 27 = 3 * 9 by norm_num, pow_mul, hM3, _root_.smul_pow, hlam9, one_pow, one_smul]
  have hadj : ∀ (c : AdjoinRoot f) (x y : Fin n → K), h (c • x) y = h x (hU.bar c • y) := by
    intro c x y
    induction c using AdjoinRoot.induction_on with
    | ih q =>
      rw [happ, happ, hsmul, hbar_mk, hsmul, hfm_mulVec,
        adjM_aeval_eq_aeval_starP τ hτ (by norm_num) M hM27 hMu q]
  have : FiniteDimensional (AdjoinRoot f) (Fin n → K) :=
    Module.Finite.of_restrictScalars_finite K (AdjoinRoot f) (Fin n → K)
  have hd : 2 ≤ Module.finrank (AdjoinRoot f) (Fin n → K) := by
    have := Module.finrank_mul_finrank K (AdjoinRoot f) (Fin n → K)
    rw [hfr, Module.finrank_fin_fun] at this
    omega
  obtain ⟨e, he⟩ := k329u5d_pair hU (τ : K →+* K) hρL h (fun x y => hfm_symm τ hτ x y) hadj
    (fun x hx => hfm_nondeg τ x (fun y => hx y)) hd
  refine ⟨e, fun i j k l => ?_⟩
  have hpow : ∀ (m : ℕ) (v : Fin n → K), AdjoinRoot.root f ^ m • v = M ^ m *ᵥ v := by
    intro m v
    rw [← AdjoinRoot.mk_X, ← map_pow, hsmul, aeval_X_pow]
  have h1 := he i j (AdjoinRoot.root f ^ (k : ℕ)) (AdjoinRoot.root f ^ (l : ℕ))
  rw [happ, hpow, hpow] at h1
  show hfm τ (M ^ (k : ℕ) *ᵥ e i) (M ^ (l : ℕ) *ᵥ e j) = _
  rw [h1]
  by_cases hij : i = j
  · rw [if_pos hij, k329u5d_trace_table hK hfr lam hlam9 hlam3 (AdjoinRoot.root f) hroot3 hU.bar
      (fun x => hU.bar_apply x) k l]
    simp [hij]
  · simp [hij]

open Polynomial in
private theorem k329u5d_orbits {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (τ : K ≃+* K) (hτ : ∀ z, τ (τ z) = z)
    (hτQ : ∀ z, τ z = z ^ (2 ^ 3)) (hn : 6 ≤ n)
    (M : Matrix (Fin n) (Fin n) K) (hMu : (M.map τ)ᵀ * M = 1)
    (lam : K) (hM3 : M ^ 3 = lam • (1 : Matrix (Fin n) (Fin n) K))
    (hlam9 : lam ^ 9 = 1) (hlam3 : lam ^ 3 ≠ 1) :
    ∃ e : Fin 2 → Fin n → K, ∀ (i j : Fin 2) (k l : Fin 3),
      ∑ a, τ ((M ^ (k : ℕ) *ᵥ e i) a) * (M ^ (l : ℕ) *ᵥ e j) a =
        if i = j ∧ k = l then 1 else 0 := by
  have : Fact (Irreducible (X ^ 3 - C lam : K[X])) := ⟨k329u5d_irred hK lam hlam9 hlam3⟩
  have hf : aeval M (X ^ 3 - C lam : K[X]) = 0 := by
    rw [map_sub, map_pow, aeval_X, aeval_C, hM3, Algebra.algebraMap_eq_smul_one, sub_self]
  let : Module (AdjoinRoot (X ^ 3 - C lam : K[X])) (Fin n → K) :=
    Module.compHom (Fin n → K) (k329u5d_act M (X ^ 3 - C lam) hf)
  exact k329u5d_orbits_of_module hK τ hτ hτQ hn M hMu lam hM3 hlam9 hlam3 _ rfl
    (fun q v => k329u5d_act_mk M _ hf q v)

end K329U5D

private theorem k329u5d_frame {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (τ : K ≃+* K) (hτ : ∀ z, τ (τ z) = z)
    (hτQ : ∀ z, τ z = z ^ (2 ^ 3)) (hn : 6 ≤ n)
    (X : Matrix (Fin n) (Fin n) K) (hXu : (X.map τ)ᵀ * X = 1)
    (lam : K) (hX3 : X ^ 3 = lam • (1 : Matrix (Fin n) (Fin n) K))
    (hlam9 : lam ^ 9 = 1) (hlam3 : lam ^ 3 ≠ 1) :
    ∃ (W₁ W₂ : Matrix (Fin n) (Fin 3) K),
      (W₁.map τ)ᵀ * W₁ = 1 ∧ (W₂.map τ)ᵀ * W₂ = 1 ∧ (W₁.map τ)ᵀ * W₂ = 0 ∧
      X * W₁ = W₁ * k329u5d_shift lam ∧ X * W₂ = W₂ * k329u5d_shift lam := by
  obtain ⟨e, he⟩ := k329u5d_orbits hK τ hτ hτQ hn X hXu lam hX3 hlam9 hlam3
  exact k329u5d_assemble τ X lam hX3 e he

private theorem k329u5_case_ii {n : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 3) ^ 2) (hn : 6 ≤ n)
    {x g : ↥(StatedSU n (2 ^ 3) K)}
    (hx3 : x ^ 3 ∈ K329Zh (StatedSU n (2 ^ 3) K))
    (hg : g ∈ K329Ct (K329Zh (StatedSU n (2 ^ 3) K)) x)
    (hgc : ∀ l ∈ K329Lres x, g * l = l * g)
    (hgnc : g ∉ Subgroup.centralizer ({x} : Set ↥(StatedSU n (2 ^ 3) K)))
    (h9 : x ^ 9 ≠ 1) : False := by
  have hn1 : 1 ≤ n := by omega
  let hFU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 3 K :=
    { prime := Nat.prime_two
      one_le := by norm_num
      card := by rw [hK]; norm_num }
  let τ : K ≃+* K := RingEquiv.ofRingHom hFU.bar hFU.bar
    (RingHom.ext hFU.bar_bar) (RingHom.ext hFU.bar_bar)
  have hτ : ∀ z, τ (τ z) = z := hFU.bar_bar
  have hτQ : ∀ z, τ z = z ^ (2 ^ 3) := hFU.bar_apply
  have hchar : CharP K 2 := hFU.charP
  obtain ⟨lam, hX3, hlam9⟩ := k329u5e_cube_scalar hK hn1 hx3
  have hlam3 : lam ^ 3 ≠ 1 := fun h => h9 ((k329u5e_pow_nine_iff hn1 hX3).mpr h)
  obtain ⟨a, ha3, hane, hconj⟩ := k329u5e_twist_data (by omega) hg hx3 hgnc
  obtain ⟨W₁, W₂, h11, h22, h12, hX1, hX2⟩ :=
    k329u5d_frame hK τ hτ hτQ hn _ (k329u5e_unitary τ hτ hτQ x) lam hX3 hlam9 hlam3
  have hτlam : τ lam * lam = 1 := by
    rw [hτQ]
    calc lam ^ (2 ^ 3) * lam = lam ^ 9 := by ring
      _ = 1 := hlam9
  have hSu := k329u5d_shift_unitary τ lam hτlam
  refine k329u5e_contra hK hn1 τ hτ hτQ hx3 hgc hane hconj (ι := Fin 3)
    (S := k329u5d_shift lam) (C := k329u5d_shift lam) h11 h22 h12 hX1 hX2 hSu rfl ?_
  rw [hSu]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h3 : (3 : K) ≠ 0 := by
    have : (3 : K) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  simpa [k329u5d_shift, Matrix.trace, Fin.sum_univ_three, Matrix.mul_apply] using h3

end K329U5E

theorem k329_S5_PSU (n : ℕ) (hadm : StatedLieAdmissible .PSU n 2 3) (K : Type) [Field K]
    [Finite K] (hK : Nat.card K = (2 ^ 3) ^ 2) :
    K329TwistMatrix (StatedSU n (2 ^ 3) K) (n = 3) := by
  intro x hxZ hx3 g hg hgc hgnc
  have h3 : 3 ∣ n := k329u5_three_dvd hadm hg hx3 hgnc
  have hn3 : 3 ≤ n := hadm.2.2.1
  rcases Nat.lt_or_ge n 6 with hn | hn
  · obtain ⟨m, hm⟩ := h3
    omega
  · by_cases h9 : x ^ 9 = 1
    · exact (k329u5_case_i hK hn hx3 hg hgc hgnc h9).elim
    · exact (k329u5_case_ii hK hn hx3 hg hgc hgnc h9).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
