module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosDefs
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryMat
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel
import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRankAux3
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.Assembly.GL83LieDefs
import CFSG.Walter.Bender1970.S3.CoreExchangeTools
import CFSG.GroupTheory.SupCommute
import CFSG.Walter.Bender1970.S1
import CFSG.Walter.Bender1970.S2
import CFSG.Walter.PSL2Facts

public section

namespace CFSG.StandardType

open CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial

theorem ggNSPosPC_ufd {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) : UnitaryFieldData 2 f K where
  prime := Nat.prime_two
  one_le := by
    by_contra hf
    have hf0 : f = 0 := by omega
    subst hf0
    have hp2 : p ∣ 2 := by simpa using h.dvd
    exact h.odd ((Nat.prime_dvd_prime_iff_eq h.prime Nat.prime_two).mp hp2)
  card := by rw [h.card, ← pow_mul, Nat.mul_comm]

theorem ggNSPosPC_exists_zeta {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) :
    ∃ ζ : Kˣ, orderOf ζ = p ∧ ζ ^ (2 ^ f + 1) = 1 :=
  CFSG.RankThree.Classical2.exists_orderOf_eq_norm_one (ggNSPosPC_ufd h) h.prime h.dvd

section Kernel

open CFSG.SectionRank.OddCover CFSG.ClassicalGroups.UnitaryFlag Multiplicative

private noncomputable def ggNSPosPC_prodHom (n p : ℕ) :
    (Fin n → Multiplicative (ZMod p)) →* Multiplicative (ZMod p) where
  toFun f := ∏ i, f i
  map_one' := by simp
  map_mul' a b := by simp [Finset.prod_mul_distrib]

private noncomputable def ggNSPosPC_ratioHom {n p : ℕ} (i j : Fin n) :
    (Fin n → Multiplicative (ZMod p)) →* Multiplicative (ZMod p) :=
  (Pi.evalMonoidHom (fun _ : Fin n => Multiplicative (ZMod p)) i) *
    ((Pi.evalMonoidHom (fun _ : Fin n => Multiplicative (ZMod p)) j)⁻¹)

private noncomputable def ggNSPosPC_deltaHom {n p : ℕ} (i j : Fin n) :
    (Fin n → Multiplicative (ZMod p)) →* Multiplicative (ZMod p) × Multiplicative (ZMod p) :=
  (ggNSPosPC_ratioHom (p := p) i j).prod (ggNSPosPC_prodHom n p)

noncomputable def ggNSPosPC_W {n p : ℕ} (i j : Fin n) :
    Subgroup (Fin n → Multiplicative (ZMod p)) := (ggNSPosPC_deltaHom (p := p) i j).ker

private theorem ggNSPosPC_deltaHom_surjective {n p : ℕ} [Fact p.Prime] {i j k : Fin n}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    Function.Surjective (ggNSPosPC_deltaHom (p := p) i j) := by
  rintro ⟨a, b⟩
  let u : Fin n → Multiplicative (ZMod p) :=
    Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) i a *
      Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) k (b * a⁻¹)
  refine ⟨u, ?_⟩
  have hi : u i = a := by
    simp only [u, Pi.mul_apply, Pi.mulSingle_eq_same,
      Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod p)) (Ne.symm hki) (b * a⁻¹),
      mul_one]
  have hj : u j = 1 := by
    simp only [u, Pi.mul_apply]
    rw [Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod p)) (Ne.symm hij) a,
      Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod p)) (Ne.symm hkj)
        (b * a⁻¹), one_mul]
  have hA : ∏ l : Fin n,
      Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) i a l = a := by
    have h := Finset.prod_eq_single (s := Finset.univ)
      (f := fun l : Fin n =>
        Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) i a l)
      i (fun c _ hc => Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod p)) hc a)
      (fun h => False.elim (h (Finset.mem_univ _)))
    simpa using h
  have hB : ∏ l : Fin n,
      Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) k (b * a⁻¹) l = b * a⁻¹ := by
    have h := Finset.prod_eq_single (s := Finset.univ)
      (f := fun l : Fin n =>
        Pi.mulSingle (M := fun _ : Fin n => Multiplicative (ZMod p)) k (b * a⁻¹) l)
      k (fun c _ hc => Pi.mulSingle_eq_of_ne (M := fun _ : Fin n => Multiplicative (ZMod p)) hc
        (b * a⁻¹))
      (fun h => False.elim (h (Finset.mem_univ _)))
    simpa using h
  have hprod : ∏ l, u l = b := by
    simp only [u, Pi.mul_apply]
    rw [Finset.prod_mul_distrib, hA, hB]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_mul, toAdd_inv]
    abel
  apply Prod.ext
  · simp only [ggNSPosPC_deltaHom, MonoidHom.prod_apply, ggNSPosPC_ratioHom]
    apply Multiplicative.toAdd.injective
    change Multiplicative.toAdd (u i * (u j)⁻¹) = Multiplicative.toAdd a
    rw [toAdd_mul, toAdd_inv, hi, hj, toAdd_one]
    abel
  · simp only [ggNSPosPC_deltaHom, MonoidHom.prod_apply, ggNSPosPC_prodHom]
    exact hprod

private theorem ggNSPosPC_W_card {n p : ℕ} [Fact p.Prime] {i j k : Fin n}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    Nat.card ↥(ggNSPosPC_W (p := p) i j) = p ^ (n - 2) := by
  have hsurj := ggNSPosPC_deltaHom_surjective (p := p) hij hki hkj
  have hrange : (ggNSPosPC_deltaHom (p := p) i j).range = ⊤ :=
    MonoidHom.range_eq_top.mpr hsurj
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (ggNSPosPC_W (p := p) i j)
  have hMc : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [← Nat.card_congr (Multiplicative.ofAdd (α := ZMod p)), Nat.card_zmod]
  have hquot : Nat.card ((Fin n → Multiplicative (ZMod p)) ⧸ ggNSPosPC_W (p := p) i j) =
      p ^ 2 := by
    change Nat.card ((Fin n → Multiplicative (ZMod p)) ⧸
      (ggNSPosPC_deltaHom (p := p) i j).ker) = p ^ 2
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange
      (ggNSPosPC_deltaHom (p := p) i j)).toEquiv, hrange,
      Nat.card_congr (Subgroup.topEquiv (G := Multiplicative (ZMod p) ×
        Multiplicative (ZMod p))).toEquiv, Nat.card_prod, hMc]
    ring
  have hG : Nat.card (Fin n → Multiplicative (ZMod p)) = p ^ n := by
    rw [Nat.card_fun, Nat.card_fin, hMc]
  have hmain : Nat.card ↥(ggNSPosPC_W (p := p) i j) * p ^ 2 = p ^ n := by
    rw [← hquot, Nat.mul_comm, ← hcard, hG]
  have hright : p ^ (n - 2) * p ^ 2 = p ^ n := by
    rw [← pow_add]; congr 1; omega
  exact Nat.eq_of_mul_eq_mul_right (pow_pos (Fact.out : p.Prime).pos 2)
    (hmain.trans hright.symm)

noncomputable def ggNSPosPC_powHom {n p : ℕ} {K : Type} [Field K] {u : Kˣ} (hu : u ^ p = 1) :
    (Fin n → Multiplicative (ZMod p)) →* (Fin n → Kˣ) :=
  MonoidHom.pi fun i : Fin n =>
    (TableBSymp.zmodPowHom hu).comp
      (Pi.evalMonoidHom (fun _ : Fin n => Multiplicative (ZMod p)) i)

private theorem ggNSPosPC_zmodPowHom_injective {p : ℕ} [NeZero p] {L : Type} [Group L]
    {u : L} (hu : u ^ p = 1) (hord : orderOf u = p) :
    Function.Injective (TableBSymp.zmodPowHom hu) := by
  intro x y hxy
  rw [TableBSymp.zmodPowHom_apply, TableBSymp.zmodPowHom_apply] at hxy
  have h2 := (pow_inj_mod (x := u)).mp hxy
  rw [hord, Nat.mod_eq_of_lt (ZMod.val_lt _), Nat.mod_eq_of_lt (ZMod.val_lt _)] at h2
  exact Multiplicative.toAdd.injective (ZMod.val_injective p h2)

private theorem ggNSPosPC_powHom_injective {n p : ℕ} {K : Type} [Field K] [NeZero p] {u : Kˣ}
    (hu : u ^ p = 1) (hord : orderOf u = p) :
    Function.Injective (ggNSPosPC_powHom (n := n) (p := p) (K := K) hu) := by
  intro f g hfg
  funext k
  exact ggNSPosPC_zmodPowHom_injective hu hord (by
    simpa [ggNSPosPC_powHom] using congrFun hfg k)

@[expose] noncomputable def ggNSPosPC_E0GL {n p : ℕ} {K : Type} [Field K] {u : Kˣ} (hu : u ^ p = 1) :
    (Fin n → Multiplicative (ZMod p)) →* GL (Fin n) K :=
  (CFSG.SectionRank.OddCover.diagHom n).comp (ggNSPosPC_powHom (p := p) hu)

private theorem ggNSPosPC_E0GL_injective {n p : ℕ} {K : Type} [Field K] [NeZero p] {u : Kˣ}
    (hu : u ^ p = 1) (hord : orderOf u = p) :
    Function.Injective (ggNSPosPC_E0GL (p := p) (n := n) (K := K) hu) :=
  (CFSG.SectionRank.OddCover.diagHom_injective n).comp
    (ggNSPosPC_powHom_injective (K := K) hu hord)

private theorem ggNSPosPC_E0GL_mem {n p f : ℕ} [Fact p.Prime] [NeZero p] {K : Type} [Field K]
    {u : Kˣ} (hu : u ^ p = 1) (huq : u ^ (2 ^ f + 1) = 1)
    (hUF : UnitaryFieldData 2 f K) {i j : Fin n}
    {fvec : Fin n → Multiplicative (ZMod p)} (hf : fvec ∈ ggNSPosPC_W (p := p) i j) :
    ggNSPosPC_E0GL (p := p) (n := n) (K := K) hu fvec ∈ unitarySU 2 f K n := by
  refine TableBUE.diagHom_mem_unitarySU hUF (fun k => ?_) ?_
  · simp only [ggNSPosPC_E0GL, ggNSPosPC_powHom, MonoidHom.comp_apply, MonoidHom.pi_apply,
      Pi.evalMonoidHom_apply, TableBSymp.zmodPowHom_apply]
    rw [← pow_mul, mul_comm, pow_mul, huq, one_pow]
  · simp only [ggNSPosPC_E0GL, ggNSPosPC_powHom, MonoidHom.comp_apply, MonoidHom.pi_apply,
      Pi.evalMonoidHom_apply]
    have hker := MonoidHom.mem_ker.mp hf
    have hprod : (∏ k, fvec k) = 1 := by
      have h := congrArg Prod.snd hker
      simpa [ggNSPosPC_deltaHom, ggNSPosPC_prodHom, MonoidHom.prod_apply] using h
    rw [← map_prod (TableBSymp.zmodPowHom hu) fvec Finset.univ, hprod, map_one]

@[expose] noncomputable def ggNSPosPC_E0Su {n p f : ℕ} [Fact p.Prime] [NeZero p] {K : Type}
    [Field K] [Finite K] [CharP K 2] {u : Kˣ} (hu : u ^ p = 1) (huq : u ^ (2 ^ f + 1) = 1)
    (hUF : UnitaryFieldData 2 f K) {i j : Fin n} : ↥(ggNSPosPC_W (p := p) i j) →* Su K 2 f n :=
  MonoidHom.codRestrict
    ((ggNSPosPC_E0GL (p := p) (n := n) (K := K) hu).comp (ggNSPosPC_W (p := p) i j).subtype)
    (SUid (unitaryInvolution K 2 f) n)
    (fun x => by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [SUid_eq_statedSU hUF.card_eq_sq n]
      exact ggNSPosPC_E0GL_mem (p := p) (f := f) hu huq hUF x.2)

private theorem ggNSPosPC_E0Su_injective {n p f : ℕ} [Fact p.Prime] [NeZero p] {K : Type}
    [Field K] [Finite K] [CharP K 2] {u : Kˣ} (hu : u ^ p = 1) (huq : u ^ (2 ^ f + 1) = 1)
    (hUF : UnitaryFieldData 2 f K) (hord : orderOf u = p) {i j : Fin n} :
    Function.Injective (ggNSPosPC_E0Su (p := p) (f := f) hu huq hUF (i := i) (j := j)) := by
  intro x y hxy
  have hval : ggNSPosPC_E0GL (p := p) (n := n) (K := K) hu x.1 =
      ggNSPosPC_E0GL (p := p) (n := n) (K := K) hu y.1 := by
    simpa [ggNSPosPC_E0Su, MonoidHom.codRestrict_apply] using congrArg Subtype.val hxy
  exact Subtype.ext (ggNSPosPC_E0GL_injective (K := K) hu hord hval)

theorem ggNSPosPC_E0Su_card {n p f : ℕ} [Fact p.Prime] [NeZero p] {K : Type}
    [Field K] [Finite K] [CharP K 2] {u : Kˣ} (hu : u ^ p = 1) (huq : u ^ (2 ^ f + 1) = 1)
    (hUF : UnitaryFieldData 2 f K) (hord : orderOf u = p) {i j k : Fin n}
    (hij : i ≠ j) (hki : k ≠ i) (hkj : k ≠ j) :
    Nat.card ↥(Subgroup.map (ggNSPosPC_E0Su (p := p) (f := f) hu huq hUF (i := i) (j := j)) ⊤) =
      p ^ (n - 2) := by
  rw [Subgroup.card_map_of_injective
    (ggNSPosPC_E0Su_injective (p := p) (f := f) hu huq hUF hord (i := i) (j := j)),
    Nat.card_congr (Subgroup.topEquiv (G := ↥(ggNSPosPC_W (p := p) i j))).toEquiv,
    ggNSPosPC_W_card (p := p) hij hki hkj]

theorem ggNSPosPC_W_apply_eq {n p : ℕ} [Fact p.Prime] {i j : Fin n}
    {x : Fin n → Multiplicative (ZMod p)} (hx : x ∈ ggNSPosPC_W (p := p) i j) :
    x i = x j := by
  have hker := MonoidHom.mem_ker.mp hx
  have hratio : ggNSPosPC_ratioHom (p := p) i j x = 1 := by
    have h := congrArg Prod.fst hker
    simpa [ggNSPosPC_deltaHom, MonoidHom.prod_apply] using h
  apply Multiplicative.toAdd.injective
  have h := congrArg Multiplicative.toAdd hratio
  change Multiplicative.toAdd (x i * (x j)⁻¹) = Multiplicative.toAdd (1 : Multiplicative (ZMod p)) at h
  rw [toAdd_mul, toAdd_inv, toAdd_one] at h
  exact add_right_cancel
    (h.trans (add_neg_cancel (Multiplicative.toAdd (x j))).symm)

private theorem ggNSPosPC_commutator_diag_permGL {n : ℕ} {K : Type} [Field K] {i j : Fin n}
    (hij : i ≠ j) (u : Fin n → Kˣ) :
    (CFSG.SectionRank.OddCover.diagHom n u) *
        (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) *
        (CFSG.SectionRank.OddCover.diagHom n u)⁻¹ *
        (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K)⁻¹ =
      CFSG.SectionRank.OddCover.diagHom n (fun k => u k * (u (Equiv.swap i j k))⁻¹) := by
  have hX : (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) *
      (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) = 1 := by
    rw [← map_mul, Equiv.swap_mul_self, map_one]
  have hXinv : (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K)⁻¹ =
      (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) :=
    inv_eq_of_mul_eq_one_left hX
  have hmul := CFSG.StandardType.TableBUM.diagHom_mul_permGL_swap (K := K) (i := i) (j := j) u
  have hmul2 := CFSG.StandardType.TableBUM.permGL_swap_mul_diagHom (K := K) (i := i) (j := j)
  calc (CFSG.SectionRank.OddCover.diagHom n u) *
        (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) *
        (CFSG.SectionRank.OddCover.diagHom n u)⁻¹ *
        (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K)⁻¹
      = (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) *
          CFSG.SectionRank.OddCover.diagHom n (u ∘ Equiv.swap i j) *
          (CFSG.SectionRank.OddCover.diagHom n u)⁻¹ *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) := by
        rw [hmul, hXinv]
    _ = (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) *
          CFSG.SectionRank.OddCover.diagHom n ((u ∘ Equiv.swap i j) * u⁻¹) *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) := by
        rw [map_mul, map_inv]
        group
    _ = CFSG.SectionRank.OddCover.diagHom n (((u ∘ Equiv.swap i j) * u⁻¹) ∘ Equiv.swap i j) *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) := by
        rw [hmul2]
    _ = CFSG.SectionRank.OddCover.diagHom n (((u ∘ Equiv.swap i j) * u⁻¹) ∘ Equiv.swap i j) := by
        simp only [mul_assoc, hX, mul_one]
    _ = CFSG.SectionRank.OddCover.diagHom n (fun k => u k * (u (Equiv.swap i j k))⁻¹) := by
        congr 1
        funext k
        simp [Function.comp, Pi.mul_apply, Pi.inv_apply]

theorem ggNSPosPC_diagHom_commute_monoSwap {n p : ℕ} {K : Type} [Field K] {u : Kˣ}
    (hu : u ^ p = 1) {i j : Fin n} {x : Fin n → Multiplicative (ZMod p)} (hx : x i = x j) :
    ggNSPosPC_E0GL (p := p) (n := n) (K := K) hu x *
        TableBUM.monoSwap i j 1 =
      TableBUM.monoSwap i j 1 * ggNSPosPC_E0GL (p := p) (n := n) (K := K) hu x := by
  simp only [ggNSPosPC_E0GL, MonoidHom.comp_apply, ggNSPosPC_powHom, MonoidHom.pi_apply,
    Pi.evalMonoidHom_apply]
  exact TableBUM.commute_monoSwap (by simpa using congrArg (TableBSymp.zmodPowHom hu) hx) 1

@[expose] noncomputable def ggNSPosPC_t {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hUF : UnitaryFieldData 2 f K) (hn : 2 ≤ n) : Su K 2 f n :=
  ⟨TableBUM.monoSwap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) 1,
    by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      rw [SUid_eq_statedSU hUF.card_eq_sq n]
      exact TableBUM.monoSwap_mem hUF (by simp) (one_pow _)⟩

theorem ggNSPosPC_E0GL_apply {n p : ℕ} {K : Type} [Field K] {u : Kˣ} (hu : u ^ p = 1)
    (x : Fin n → Multiplicative (ZMod p)) :
    ggNSPosPC_E0GL (p := p) (n := n) (K := K) hu x =
      CFSG.SectionRank.OddCover.diagHom n (ggNSPosPC_powHom (p := p) hu x) := rfl

theorem ggNSPosPC_E0Su_coe {n p f : ℕ} [Fact p.Prime] [NeZero p] {K : Type} [Field K]
    [Finite K] [CharP K 2] {u : Kˣ} (hu : u ^ p = 1) (huq : u ^ (2 ^ f + 1) = 1)
    (hUF : UnitaryFieldData 2 f K) {i j : Fin n} (w : ↥(ggNSPosPC_W (p := p) i j)) :
    ((ggNSPosPC_E0Su (p := p) (f := f) hu huq hUF (i := i) (j := j) w : Su K 2 f n) :
        GL (Fin n) K) = ggNSPosPC_E0GL (p := p) (n := n) (K := K) hu w.1 := rfl

theorem ggNSPosPC_t_coe {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hUF : UnitaryFieldData 2 f K) (hn : 2 ≤ n) :
    ((ggNSPosPC_t hUF hn : Su K 2 f n) : GL (Fin n) K) =
      TableBUM.monoSwap (⟨0, by omega⟩ : Fin n) (⟨1, by omega⟩ : Fin n) 1 := rfl

theorem ggNSPosPC_t_mul_self {n f : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hUF : UnitaryFieldData 2 f K) (hn : 2 ≤ n) :
    ggNSPosPC_t hUF hn * ggNSPosPC_t hUF hn = 1 := by
  apply Subtype.ext
  exact TableBUM.monoSwap_mul_self (by simp) 1

theorem ggNSPosPC_psi_t_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) (hn : 2 ≤ n) :
    ψ (ggNSPosPC_t (ggNSPosPC_ufd h) hn) ≠ 1 := by
  intro h1
  have htker : ggNSPosPC_t (ggNSPosPC_ufd h) hn ∈ ψ.ker := h1
  have hcenter := h.ker htker
  have hcomm : ∀ g : Su K 2 f n,
      ggNSPosPC_t (ggNSPosPC_ufd h) hn * g = g * ggNSPosPC_t (ggNSPosPC_ufd h) hn :=
    fun g => (Subgroup.mem_center_iff.mp hcenter g).symm
  have hGL : ∀ g ∈ unitarySU 2 f K n,
      (ggNSPosPC_t (ggNSPosPC_ufd h) hn : GL (Fin n) K) * g =
        g * (ggNSPosPC_t (ggNSPosPC_ufd h) hn : GL (Fin n) K) := by
    intro g hg
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hg' : g ∈ SUid (unitaryInvolution K 2 f) n := by
      rwa [SUid_eq_statedSU (ggNSPosPC_ufd h).card_eq_sq n]
    have := hcomm ⟨g, hg'⟩
    exact congrArg Subtype.val this
  exact TableBUM.monoSwap_not_mem_scalars (show (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ by simp) 1
    (TableBUE.mem_scalars_of_commute (ggNSPosPC_ufd h) h.prime h.dvd hGL)


theorem ggNSPosPC_uconst_of_permutation_central {n : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] {p f : ℕ} [Fact p.Prime] (hUF : UnitaryFieldData 2 f K) (hn : 3 ≤ n)
    (u : Fin n → Kˣ)
    (hcomm : ∀ i j : Fin n, i ≠ j →
      CFSG.SectionRank.OddCover.diagHom n u *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K) *
          (CFSG.SectionRank.OddCover.diagHom n u)⁻¹ *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i j) : GL (Fin n) K)⁻¹ ∈
        CFSG.Assembly.LargeEvenScalars (Fin n) K) :
    ∀ i j : Fin n, u i = u j := by
  intro i j
  by_cases hij : i = j
  · subst hij; rfl
  · specialize hcomm i j hij
    rw [ggNSPosPC_commutator_diag_permGL hij u] at hcomm
    obtain ⟨c, hc⟩ := hcomm
    have hk_exists : ∃ k : Fin n, k ≠ i ∧ k ≠ j := by
      by_contra h
      have hsub : (Finset.univ : Finset (Fin n)) ⊆ {i, j} := by
        intro k _
        by_contra hk
        simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hk
        exact h ⟨k, hk.1, hk.2⟩
      have hle := Finset.card_le_card hsub
      rw [Finset.card_univ, Fintype.card_fin] at hle
      have h2 : ({i, j} : Finset (Fin n)).card ≤ 2 := Finset.card_le_two
      omega
    obtain ⟨k, hki, hkj⟩ := hk_exists
    have hentry : (fun l : Fin n => u l * (u (Equiv.swap i j l))⁻¹) k = c := by
      have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin n) K =>
        (g : Matrix (Fin n) (Fin n) K)) hc) k) k
      apply Units.ext
      simpa [CFSG.SectionRank.OddCover.coe_diagHom] using h1.symm
    have hk1 : (fun l : Fin n => u l * (u (Equiv.swap i j l))⁻¹) k = 1 := by
      simp [Equiv.swap_apply_of_ne_of_ne hki hkj]
    rw [hk1] at hentry
    have hci : (fun l : Fin n => u l * (u (Equiv.swap i j l))⁻¹) i = c := by
      have h1 := congrFun (congrFun (congrArg (fun g : GL (Fin n) K =>
        (g : Matrix (Fin n) (Fin n) K)) hc) i) i
      apply Units.ext
      simpa [CFSG.SectionRank.OddCover.coe_diagHom] using h1.symm
    have hswap : Equiv.swap i j i = j := Equiv.swap_apply_left i j
    have hval : u i * (u j)⁻¹ = 1 := by
      rw [← hentry] at hci
      simpa [hswap] using hci
    exact mul_inv_eq_one.mp hval

end Kernel

end CFSG.StandardType

end
