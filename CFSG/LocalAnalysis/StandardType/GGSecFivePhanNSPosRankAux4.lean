module

import Lean
public import CFSG.LocalAnalysis.StandardType.GGSecFivePhanNSPosRankAux2
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

open CFSG.Assembly CFSG.ClassicalInvolution.Phan CFSG.LieType.Universal.Unitary
  CFSG.LieType.BorelTits CFSG.RankThree.Classical2 CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.ClassicalGroups.UnitaryFlag Multiplicative Matrix

open scoped MatrixGroups

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_center_le_scalars {n p f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] (hUF : UnitaryFieldData 2 f K) (hp : p.Prime) (hdvd : p ∣ 2 ^ f + 1) :
    Subgroup.center (Su K 2 f n) ≤
      (LargeEvenScalars (Fin n) K).subgroupOf (SUid (unitaryInvolution K 2 f) n) := by
  intro x hx
  rw [Subgroup.mem_subgroupOf]
  have hcomm : ∀ g ∈ unitarySU 2 f K n,
      (x.1 : GL (Fin n) K) * g = g * (x.1 : GL (Fin n) K) := by
    intro g hg
    have hg' : g ∈ SUid (unitaryInvolution K 2 f) n := by
      rwa [SUid_eq_statedSU hUF.card_eq_sq n]
    have := (Subgroup.mem_center_iff.mp hx) ⟨g, hg'⟩
    exact (congrArg Subtype.val this).symm
  exact TableBUE.mem_scalars_of_commute hUF hp hdvd hcomm

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_scalar_inf_card_le {n p f : ℕ} {K : Type} [Field K] [Finite K]
    [CharP K 2] [NeZero p] {T : Subgroup (Su K 2 f n)} (hT : IsElemAbelian p T) (i : Fin n) :
    Nat.card ↥(T ⊓ (LargeEvenScalars (Fin n) K).subgroupOf
      (SUid (unitaryInvolution K 2 f) n)) ≤ p := by
  let Zs : Subgroup (Su K 2 f n) :=
    T ⊓ (LargeEvenScalars (Fin n) K).subgroupOf (SUid (unitaryInvolution K 2 f) n)
  change Nat.card ↥Zs ≤ p
  have hs : ∀ z : ↥Zs, ∃ c : Kˣ,
      Matrix.GeneralLinearGroup.scalar (Fin n) c = (z.1.1 : GL (Fin n) K) := by
    intro z
    have hz := Subgroup.mem_subgroupOf.mp z.2.2
    rw [largeEvenScalars_def] at hz
    exact MonoidHom.mem_range.mp hz
  let s : ↥Zs → Kˣ := fun z => Classical.choose (hs z)
  have hspec : ∀ z, Matrix.GeneralLinearGroup.scalar (Fin n) (s z) =
      (z.1.1 : GL (Fin n) K) := fun z => Classical.choose_spec (hs z)
  have hsinj : Function.Injective s := by
    intro z z' hzz
    have h1 : (z.1.1 : GL (Fin n) K) = (z'.1.1 : GL (Fin n) K) := by
      rw [← hspec z, ← hspec z', hzz]
    exact Subtype.ext (Subtype.ext h1)
  have hscalar_inj : Function.Injective
      (Matrix.GeneralLinearGroup.scalar (Fin n) : Kˣ →* GL (Fin n) K) := by
    intro a b hab
    apply Units.ext
    have h1 := congrArg (fun g : GL (Fin n) K =>
      (g : Matrix (Fin n) (Fin n) K) i i) hab
    simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply] using h1
  have hsp : ∀ z, (s z) ^ p = 1 := by
    intro z
    apply hscalar_inj
    rw [map_pow, map_one, hspec z]
    simpa using congrArg Subtype.val (hT.2 z.1 z.2.1)
  let g : ↥Zs → ↥(rootsOfUnity p K) := fun z =>
    ⟨s z, (mem_rootsOfUnity (M := K) p (s z)).mpr (hsp z)⟩
  have hginj : Function.Injective g := fun z z' hzz => hsinj (Subtype.ext_iff.mp hzz)
  calc Nat.card ↥Zs ≤ Nat.card ↥(rootsOfUnity p K) :=
        Nat.card_le_card_of_injective g hginj
    _ ≤ p := card_rootsOfUnity (k := p) (R := K)

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_card_lt_of_subgroupOf_ne_top {A : Type*} [Group A] [Finite A]
    {H Zs : Subgroup A} (hHZs : H ≤ Zs) (hne : H.subgroupOf Zs ≠ ⊤) :
    Nat.card ↥H < Nat.card ↥Zs := by
  have hidx : 1 < (H.subgroupOf Zs).index := Subgroup.one_lt_index_of_ne_top hne
  have hcard : Nat.card ↥Zs = (H.subgroupOf Zs).index * Nat.card ↥H := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (H.subgroupOf Zs),
      ← Subgroup.index_eq_card]
    congr 1
    rw [Nat.card_congr (ggNSPosPC_subgroupOfEquiv H Zs),
      show H ⊓ Zs = H from inf_eq_left.mpr hHZs]
  calc Nat.card ↥H = 1 * Nat.card ↥H := (one_mul _).symm
    _ < (H.subgroupOf Zs).index * Nat.card ↥H :=
        Nat.mul_lt_mul_of_pos_right hidx Nat.card_pos
    _ = Nat.card ↥Zs := hcard.symm

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_zpowers_data {G : Type} [Group G] {p : ℕ} {y : G}
    (hy : orderOf y = p) :
    Nat.card ↥(Subgroup.zpowers y) = p ∧ IsElemAbelian p (Subgroup.zpowers y) :=
  ⟨by rw [Nat.card_zpowers, hy],
    hy ▸ isElemAbelian_zpowers (pow_orderOf_eq_one y)⟩

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_zpowers_le_centralizer_map {G H : Type*} [Group G] [Group H]
    {ψ : H →* G} {T : Subgroup H} {y : G}
    (hy : y ∈ Subgroup.centralizer (ψ.range : Set G)) :
    Subgroup.zpowers y ≤ Subgroup.centralizer (T.map ψ : Set G) := by
  rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp ha
  exact (Subgroup.mem_centralizer_iff.mp hy) (ψ t) (MonoidHom.mem_range.mpr ⟨t, rfl⟩)

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_zpowers_le_normalizer_map {G H : Type*} [Group G] [Group H]
    {ψ : H →* G} {y : G} {b : H} (hy : y ∈ Subgroup.centralizer (ψ.range : Set G)) :
    Subgroup.zpowers y ≤ Subgroup.normalizer (Subgroup.zpowers (ψ b) : Set G) := by
  have hyc : y * ψ b = ψ b * y :=
    ((Subgroup.mem_centralizer_iff.mp hy) (ψ b) (MonoidHom.mem_range.mpr ⟨b, rfl⟩)).symm
  rw [Subgroup.le_normalizer_iff]
  intro a ha u hu
  obtain ⟨m', hm'⟩ := Subgroup.mem_zpowers_iff.mp ha
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [← hm', ← hl]
  have hpow : Commute (y ^ m') ((ψ b) ^ l) :=
    Commute.zpow_right (Commute.zpow_left hyc m') l
  have hpow' : y ^ m' * (ψ b) ^ l = (ψ b) ^ l * y ^ m' := hpow
  rw [hpow', mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.mem_zpowers_iff.mpr ⟨l, rfl⟩

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_card_map_ge {A G : Type*} [Group A] [Group G] [Finite A] {p n : ℕ}
    (hp : p.Prime) {ψ : A →* G} {T Zs : Subgroup A}
    (hTcard : Nat.card ↥T = p ^ (n - 2)) (hZscard : Nat.card ↥Zs ≤ p)
    (hK0le : T ⊓ ψ.ker ≤ Zs) (hn : 4 ≤ n) :
    p ^ (n - 3) ≤ Nat.card ↥(T.map ψ) := by
  have hrel := ggNSPosPC_card_map_mul_card_inf_ker ψ T
  rw [hTcard] at hrel
  have hK0card : Nat.card ↥(T ⊓ ψ.ker) ≤ p := by
    have hinj : Function.Injective
        (fun x : ↥(T ⊓ ψ.ker) => (⟨x.1, hK0le x.2⟩ : ↥Zs)) := by
      intro a b hab
      have h1 : (a : A) = (b : A) := congrArg (fun y : ↥Zs => (y.1 : A)) hab
      exact Subtype.ext h1
    exact (Nat.card_le_card_of_injective _ hinj).trans hZscard
  have h1 : Nat.card ↥(T.map ψ) * Nat.card ↥(T ⊓ ψ.ker) ≤
      Nat.card ↥(T.map ψ) * p := Nat.mul_le_mul_left _ hK0card
  rw [← hrel] at h1
  have hpow : p ^ (n - 2) = p ^ (n - 3) * p := by
    rw [show n - 2 = (n - 3) + 1 by omega]
    exact pow_succ p (n - 3)
  have h2 : p ^ (n - 3) * p ≤ Nat.card ↥(T.map ψ) * p := by rwa [hpow] at h1
  exact Nat.le_of_mul_le_mul_right h2 hp.pos

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_exists_order_p_mem_cent {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] [Fact p.Prime] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) :
    ∃ y : G, y ∈ B ⊓ Subgroup.centralizer (ψ.range : Set G) ∧ orderOf y = p ∧ y ≠ 1 := by
  have hdvd : p ∣ Nat.card ↥(B ⊓ Subgroup.centralizer (ψ.range : Set G)) := by
    rw [h.cent]
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' p hdvd
  have hg' : orderOf (g.1 : G) = p := by simpa using hg
  refine ⟨g.1, g.2, hg', ?_⟩
  intro h1
  rw [h1, orderOf_one] at hg'
  exact h.prime.ne_one hg'.symm

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_card_sup_ge_of_not_mem {G : Type} [Group G] {p n : ℕ} {A : Subgroup G}
    {y : G} (hp : p.Prime) (hy : y ∉ A) (hYcard : Nat.card ↥(Subgroup.zpowers y) = p)
    (hAcard : p ^ (n - 3) ≤ Nat.card ↥A)
    (hYcent : Subgroup.zpowers y ≤ Subgroup.centralizer (A : Set G)) (hn : 4 ≤ n) :
    p ^ (n - 2) ≤ Nat.card ↥(A ⊔ Subgroup.zpowers y) := by
  have hdisj : A ⊓ Subgroup.zpowers y = ⊥ := by
    have : Fact (Nat.Prime (Nat.card ↥(Subgroup.zpowers y))) := ⟨by rw [hYcard]; exact hp⟩
    rcases Subgroup.eq_bot_or_eq_top_of_prime_card (A.subgroupOf (Subgroup.zpowers y)) with
      hbot | htop
    · rw [Subgroup.subgroupOf_eq_bot] at hbot
      exact disjoint_iff.mp hbot
    · have hle : Subgroup.zpowers y ≤ A := Subgroup.subgroupOf_eq_top.mp htop
      exact absurd (hle (Subgroup.mem_zpowers y)) hy
  have hcomm : ∀ a ∈ A, ∀ b ∈ Subgroup.zpowers y, Commute a b := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hYcent hb)) a ha
  have hcardF : Nat.card ↥(A ⊔ Subgroup.zpowers y) =
      Nat.card ↥A * Nat.card ↥(Subgroup.zpowers y) :=
    CFSG.card_sup_eq_mul_of_commute A (Subgroup.zpowers y) hcomm hdisj
  rw [hcardF, hYcard]
  calc p ^ (n - 2) = p ^ (n - 3) * p := by
        rw [show n - 2 = (n - 3) + 1 by omega]
        exact pow_succ p (n - 3)
    _ ≤ Nat.card ↥A * p := Nat.mul_le_mul_right p hAcard

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_diagHom_commutator_mem_scalars {n p f : ℕ} {K : Type} [Field K]
    [Finite K] [CharP K 2] {G : Type} [Group G] {ψ : Su K 2 f n →* G} {z : Su K 2 f n}
    {u : Fin n → Kˣ} (hUF : UnitaryFieldData 2 f K) (hp : p.Prime) (hdvd : p ∣ 2 ^ f + 1)
    (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n))
    (hz : (z : GL (Fin n) K) = CFSG.SectionRank.OddCover.diagHom n u)
    (hcentz : ψ z ∈ Subgroup.centralizer (ψ.range : Set G)) :
    ∀ i' j' : Fin n, i' ≠ j' →
      CFSG.SectionRank.OddCover.diagHom n u *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i' j') : GL (Fin n) K) *
          (CFSG.SectionRank.OddCover.diagHom n u)⁻¹ *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i' j') : GL (Fin n) K)⁻¹ ∈
        CFSG.Assembly.LargeEvenScalars (Fin n) K := by
  intro i' j' hij'
  have hkerz : z * ggPermSU (K := K) (f := f) (Equiv.swap i' j') * z⁻¹ *
      (ggPermSU (K := K) (f := f) (Equiv.swap i' j'))⁻¹ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    have hyc : ψ z * ψ (ggPermSU (K := K) (f := f) (Equiv.swap i' j')) =
        ψ (ggPermSU (K := K) (f := f) (Equiv.swap i' j')) * ψ z :=
      ((Subgroup.mem_centralizer_iff.mp hcentz)
        (ψ (ggPermSU (K := K) (f := f) (Equiv.swap i' j')))
        (MonoidHom.mem_range.mpr ⟨_, rfl⟩)).symm
    rw [hyc]
    group
  have hcent := hker hkerz
  have hcommSU : ∀ g : Su K 2 f n, (z * ggPermSU (K := K) (f := f) (Equiv.swap i' j') *
      z⁻¹ * (ggPermSU (K := K) (f := f) (Equiv.swap i' j'))⁻¹) * g =
      g * (z * ggPermSU (K := K) (f := f) (Equiv.swap i' j') * z⁻¹ *
        (ggPermSU (K := K) (f := f) (Equiv.swap i' j'))⁻¹) :=
    fun g => (Subgroup.mem_center_iff.mp hcent g).symm
  have hGL : ∀ g ∈ unitarySU 2 f K n,
      (((z * ggPermSU (K := K) (f := f) (Equiv.swap i' j') * z⁻¹ *
        (ggPermSU (K := K) (f := f) (Equiv.swap i' j'))⁻¹ : Su K 2 f n) : GL (Fin n) K)) *
          g = g * (((z * ggPermSU (K := K) (f := f) (Equiv.swap i' j') * z⁻¹ *
        (ggPermSU (K := K) (f := f) (Equiv.swap i' j'))⁻¹ : Su K 2 f n) : GL (Fin n) K)) := by
    intro g' hg'
    have hg'' : g' ∈ SUid (unitaryInvolution K 2 f) n := by
      rwa [SUid_eq_statedSU hUF.card_eq_sq n]
    have := hcommSU ⟨g', hg''⟩
    exact congrArg Subtype.val this
  have hsc := TableBUE.mem_scalars_of_commute hUF hp hdvd hGL
  have hcoe : (((z * ggPermSU (K := K) (f := f) (Equiv.swap i' j') * z⁻¹ *
      (ggPermSU (K := K) (f := f) (Equiv.swap i' j'))⁻¹ : Su K 2 f n) :
        GL (Fin n) K)) =
      CFSG.SectionRank.OddCover.diagHom n u *
        (CFSG.RankThree.Classical.permGL (Equiv.swap i' j') : GL (Fin n) K) *
        (CFSG.SectionRank.OddCover.diagHom n u)⁻¹ *
        (CFSG.RankThree.Classical.permGL (Equiv.swap i' j') : GL (Fin n) K)⁻¹ := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hz, ggNSPosPC_coe_ggPermSU_swap (K := K) (f := f) i' j']
  rwa [hcoe] at hsc

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_diagHom_mem_scalars {n p f : ℕ} [Fact p.Prime] {K : Type} [Field K]
    [Finite K] [CharP K 2] (hUF : UnitaryFieldData 2 f K) (hn : 3 ≤ n) (i : Fin n)
    (u : Fin n → Kˣ)
    (hcomm : ∀ i' j' : Fin n, i' ≠ j' →
      CFSG.SectionRank.OddCover.diagHom n u *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i' j') : GL (Fin n) K) *
          (CFSG.SectionRank.OddCover.diagHom n u)⁻¹ *
          (CFSG.RankThree.Classical.permGL (Equiv.swap i' j') : GL (Fin n) K)⁻¹ ∈
        CFSG.Assembly.LargeEvenScalars (Fin n) K) :
    CFSG.SectionRank.OddCover.diagHom n u ∈ CFSG.Assembly.LargeEvenScalars (Fin n) K := by
  have hconst := ggNSPosPC_uconst_of_permutation_central (p := p) (f := f) hUF hn u hcomm
  have huconst : u = Function.const (Fin n) (u i) := funext fun l => hconst l i
  rw [CFSG.Assembly.largeEvenScalars_def]
  refine MonoidHom.mem_range.mpr ⟨u i, ?_⟩
  rw [huconst]
  ext a b
  simp [CFSG.SectionRank.OddCover.coe_diagHom, Matrix.scalar_apply, Matrix.diagonal_apply]

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_E0Su_mem_scalars {n p f : ℕ} [Fact p.Prime] [NeZero p] {K : Type}
    [Field K] [Finite K] [CharP K 2] {G : Type} [Group G] {ψ : Su K 2 f n →* G}
    (hUF : UnitaryFieldData 2 f K) {ζ : Kˣ} (hζp : ζ ^ p = 1) (hζq : ζ ^ (2 ^ f + 1) = 1)
    (hp : p.Prime) (hdvd : p ∣ 2 ^ f + 1) (hker : ψ.ker ≤ Subgroup.center (Su K 2 f n))
    {i j : Fin n} (hn : 3 ≤ n) {w : ↥(ggNSPosPC_W (p := p) i j)}
    (hcent : ψ (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w) ∈
      Subgroup.centralizer (ψ.range : Set G)) :
    ((ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w :
      Su K 2 f n) : GL (Fin n) K) ∈ CFSG.Assembly.LargeEvenScalars (Fin n) K := by
  have hz : ((ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w :
      Su K 2 f n) : GL (Fin n) K) =
      CFSG.SectionRank.OddCover.diagHom n (ggNSPosPC_powHom (p := p) hζp w.1) := by
    rw [ggNSPosPC_E0Su_coe (p := p) (f := f) hζp hζq hUF w,
      ggNSPosPC_E0GL_apply (p := p) hζp w.1]
  rw [hz]
  exact ggNSPosPC_diagHom_mem_scalars (p := p) hUF hn ⟨0, by omega⟩ _
    (ggNSPosPC_diagHom_commutator_mem_scalars hUF hp hdvd hker hz hcent)

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_torus_facts {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] [Fact p.Prime] [NeZero p] {f n : ℕ}
    {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) (hn4 : 4 ≤ n) (hUF : UnitaryFieldData 2 f K) {ζ : Kˣ}
    (hζp : ζ ^ p = 1) (hζq : ζ ^ (2 ^ f + 1) = 1) (hζord : orderOf ζ = p) :
    ∃ T : Subgroup (Su K 2 f n),
      T = Subgroup.map (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF
        (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)) ⊤ ∧
      IsElemAbelian p T ∧ Nat.card ↥T = p ^ (n - 2) ∧
      Nat.card ↥(T ⊓ (LargeEvenScalars (Fin n) K).subgroupOf
        (SUid (unitaryInvolution K 2 f) n)) ≤ p ∧
      T ⊓ ψ.ker ≤ T ⊓ (LargeEvenScalars (Fin n) K).subgroupOf
        (SUid (unitaryInvolution K 2 f) n) ∧
      (∀ z ∈ T, ψ z ∈ Subgroup.centralizer (ψ.range : Set G) → z ∈ T ⊓
        (LargeEvenScalars (Fin n) K).subgroupOf (SUid (unitaryInvolution K 2 f) n)) := by
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let k : Fin n := ⟨2, by omega⟩
  have hij : i ≠ j := by simp [i, j]
  have hki : k ≠ i := by simp [k, i]
  have hkj : k ≠ j := by simp [k, j]
  let T' : Subgroup (Su K 2 f n) :=
    Subgroup.map (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j)) ⊤
  have hTab : IsElemAbelian p T' := by
    have hWab : IsElemAbelian p (⊤ : Subgroup ↥(ggNSPosPC_W (p := p) i j)) :=
      ⟨isMulCommutative_iff.mpr fun a b => Subtype.ext (mul_comm _ _),
        fun x _ => Subtype.ext (ggNSPosPC_pow_pi_zmod (p := p) x.1)⟩
    have := IsElemAbelian.map (E := (⊤ : Subgroup ↥(ggNSPosPC_W (p := p) i j))) hWab
      (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j))
    simpa only [T', Subgroup.map_top] using this
  have hTcard : Nat.card ↥T' = p ^ (n - 2) :=
    ggNSPosPC_E0Su_card (p := p) (f := f) hζp hζq hUF hζord hij hki hkj
  have hZscard : Nat.card ↥(T' ⊓ (LargeEvenScalars (Fin n) K).subgroupOf
      (SUid (unitaryInvolution K 2 f) n)) ≤ p :=
    ggNSPosPC_scalar_inf_card_le hTab i
  have hK0le : T' ⊓ ψ.ker ≤ T' ⊓ (LargeEvenScalars (Fin n) K).subgroupOf
      (SUid (unitaryInvolution K 2 f) n) :=
    fun x hx => ⟨hx.1, ggNSPosPC_center_le_scalars hUF h.prime h.dvd (h.ker hx.2)⟩
  have hscalar : ∀ z ∈ T', ψ z ∈ Subgroup.centralizer (ψ.range : Set G) → z ∈ T' ⊓
      (LargeEvenScalars (Fin n) K).subgroupOf (SUid (unitaryInvolution K 2 f) n) := by
    intro z hz hzent
    obtain ⟨w, -, hw⟩ := Subgroup.mem_map.mp hz
    have hzent' : ψ (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w) ∈
        Subgroup.centralizer (ψ.range : Set G) := by
      rwa [← hw] at hzent
    refine ⟨hz, ?_⟩
    rw [← hw]
    change ((ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w :
      Su K 2 f n) : GL (Fin n) K) ∈ LargeEvenScalars (Fin n) K
    exact ggNSPosPC_E0Su_mem_scalars hUF hζp hζq h.prime h.dvd h.ker (by omega) hzent'
  exact ⟨_, rfl, hTab, hTcard, hZscard, hK0le, hscalar⟩

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_card_map_eq_of_mem {A G : Type*} [Group A] [Group G] [Finite A]
    {p n : ℕ} [Fact p.Prime] {ψ : A →* G} {T Zs : Subgroup A} {y : G} (hp : p.Prime)
    (hTab : IsElemAbelian p T) (hTcard : Nat.card ↥T = p ^ (n - 2))
    (hZscard : Nat.card ↥Zs ≤ p) (hK0le : T ⊓ ψ.ker ≤ Zs)
    (hy : y ∈ Subgroup.centralizer (ψ.range : Set G)) (hyA : y ∈ T.map ψ) (hyne : y ≠ 1)
    (hscalar : ∀ z ∈ T, ψ z ∈ Subgroup.centralizer (ψ.range : Set G) → z ∈ Zs) :
    Nat.card ↥(T.map ψ) = p ^ (n - 2) := by
  obtain ⟨z, hzT, hzψ⟩ := Subgroup.mem_map.mp hyA
  have hzZs : z ∈ Zs := hscalar z hzT (by rw [hzψ]; exact hy)
  have hzK0 : z ∉ T ⊓ ψ.ker := by
    intro hz
    have h1 : ψ z = 1 := hz.2
    rw [hzψ] at h1
    exact hyne h1
  have hne_top : (T ⊓ ψ.ker).subgroupOf Zs ≠ ⊤ := by
    intro htop
    exact hzK0 (Subgroup.subgroupOf_eq_top.mp htop hzZs)
  have hK0card1 : Nat.card ↥(T ⊓ ψ.ker) = 1 := by
    obtain ⟨j0, hj0⟩ := (IsElemAbelian.isPGroup
      (IsElemAbelian.mono hTab inf_le_left) : IsPGroup p ↥(T ⊓ ψ.ker)).exists_card_eq
    have hlt : p ^ j0 < p := by
      rw [← hj0]
      exact (ggNSPosPC_card_lt_of_subgroupOf_ne_top hK0le hne_top).trans_le hZscard
    have hj00 : j0 = 0 := by
      have hlt' : p ^ j0 < p ^ 1 := by simpa using hlt
      have := (Nat.pow_lt_pow_iff_right hp.one_lt).mp hlt'
      omega
    rw [hj00, pow_zero] at hj0
    exact hj0
  have hrel := ggNSPosPC_card_map_mul_card_inf_ker ψ T
  rw [hTcard, hK0card1, mul_one] at hrel
  exact hrel.symm

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_exists_elemAbelian_le {G : Type} [Group G] [Finite G] {p n : ℕ}
    [Fact p.Prime] (hp : p.Prime) {F : Subgroup G} (hF : IsElemAbelian p F)
    (hcard : p ^ (n - 2) ≤ Nat.card ↥F) :
    ∃ E : Subgroup G, E ≤ F ∧ IsElemAbelian p E ∧ Nat.card ↥E = p ^ (n - 2) := by
  have hFp : IsPGroup p ↥F := IsElemAbelian.isPGroup hF
  obtain ⟨m, hm⟩ := hFp.exists_card_eq
  have hdle : n - 2 ≤ m := by
    have hle := hcard
    rw [hm] at hle
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hle
  have hdiv : p ^ (n - 2) ∣ Nat.card ↥F := by
    rw [hm]
    exact pow_dvd_pow p hdle
  obtain ⟨Kfin, hKcard⟩ := Sylow.exists_subgroup_card_pow_prime (G := ↥F) p hdiv
  refine ⟨Kfin.map F.subtype, Subgroup.map_subtype_le Kfin, ?_, ?_⟩
  · exact IsElemAbelian.mono hF (Subgroup.map_subtype_le Kfin)
  · rw [Subgroup.card_map_of_injective F.subtype_injective, hKcard]

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_zpowers_psi_t {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ}
    {ψ : Su K 2 f n →* G} (h : GGNSLocalHyp p B Bs K f n ψ) (hn : 2 ≤ n) :
    Subgroup.zpowers (ψ (ggNSPosPC_t (ggNSPosPC_ufd h) hn)) ≠ ⊥ ∧
      IsPGroup 2 (Subgroup.zpowers (ψ (ggNSPosPC_t (ggNSPosPC_ufd h) hn))) := by
  let t : Su K 2 f n := ggNSPosPC_t (ggNSPosPC_ufd h) hn
  have ht2 : t * t = 1 := ggNSPosPC_t_mul_self (ggNSPosPC_ufd h) hn
  have hψt2 : ψ t * ψ t = 1 := by rw [← map_mul, ht2, map_one]
  have hdvd : orderOf (ψ t) ∣ 2 :=
    orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hψt2)
  constructor
  · rw [Subgroup.zpowers_ne_bot]
    exact ggNSPosPC_psi_t_ne_one h hn
  · rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
    · exact IsPGroup.of_card (n := 0) (by rw [Nat.card_zpowers, h1, pow_zero])
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, h2, pow_one])

open CFSG.Open CFSG.Assembly in
private theorem ggNSPosPC_torus_map_le_normalizer {G : Type} [Group G] {K : Type} [Field K]
    [Finite K] [CharP K 2] {f n p : ℕ} [Fact p.Prime] [NeZero p] {ψ : Su K 2 f n →* G}
    {ζ : Kˣ} (hζp : ζ ^ p = 1) (hζq : ζ ^ (2 ^ f + 1) = 1) (hUF : UnitaryFieldData 2 f K)
    (hn : 2 ≤ n) {T : Subgroup (Su K 2 f n)}
    (hT : T = Subgroup.map (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF
      (i := ⟨0, by omega⟩) (j := ⟨1, by omega⟩)) ⊤) :
    T.map ψ ≤ Subgroup.normalizer (Subgroup.zpowers (ψ (ggNSPosPC_t hUF hn)) : Set G) := by
  subst hT
  let i : Fin n := ⟨0, by omega⟩
  let j : Fin n := ⟨1, by omega⟩
  let t : Su K 2 f n := ggNSPosPC_t hUF hn
  change Subgroup.map ψ (Subgroup.map (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF
    (i := i) (j := j)) ⊤) ≤
    Subgroup.normalizer (Subgroup.zpowers (ψ t) : Set G)
  rw [Subgroup.le_normalizer_iff]
  intro a ha u hu
  obtain ⟨z, hzT, hza⟩ := Subgroup.mem_map.mp ha
  obtain ⟨w, -, hw⟩ := Subgroup.mem_map.mp hzT
  obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp hu
  rw [← hza, ← hw, ← hl]
  have hzt : ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w * t =
      t * ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul,
      ggNSPosPC_E0Su_coe (p := p) (f := f) hζp hζq hUF w, ggNSPosPC_t_coe hUF hn]
    exact ggNSPosPC_diagHom_commute_monoSwap (p := p) hζp
      (ggNSPosPC_W_apply_eq (p := p) (i := i) (j := j) w.2)
  have hcommt : Commute
      (ψ (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w)) (ψ t) := by
    show ψ (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w) * ψ t =
      ψ t * ψ (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w)
    simpa only [map_mul] using congrArg ψ hzt
  have hpow' : ψ (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w) *
      (ψ t) ^ l = (ψ t) ^ l *
        ψ (ggNSPosPC_E0Su (p := p) (f := f) hζp hζq hUF (i := i) (j := j) w) :=
    hcommt.zpow_right l
  rw [hpow', mul_assoc, mul_inv_cancel, mul_one]
  exact Subgroup.mem_zpowers_iff.mpr ⟨l, rfl⟩

open CFSG.Open CFSG.Assembly in
theorem ggNSPosPC_rank_witness_aux {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {K : Type} [Field K] [Finite K] [CharP K 2] {f n : ℕ} {ψ : Su K 2 f n →* G}
    (h : GGNSLocalHyp p B Bs K f n ψ) :
    ∃ (E U : Subgroup G), IsElemAbelian p E ∧ Nat.card E = p ^ (n - 2) ∧
      U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set G) := by
  classical
  have : Fact p.Prime := ⟨h.prime⟩
  have : NeZero p := ⟨h.prime.ne_zero⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUF : UnitaryFieldData 2 f K := ggNSPosPC_ufd h
  obtain ⟨ζ, hζord, hζq⟩ := ggNSPosPC_exists_zeta h
  have hζp : ζ ^ p = 1 := hζord ▸ pow_orderOf_eq_one ζ
  have hn2 : 2 ≤ n := by have := h.four_le; omega
  obtain ⟨T, hTeq, hTab, hTcard, hZscard, hK0le, hscalar⟩ :=
    ggNSPosPC_torus_facts h h.four_le hUF hζp hζq hζord
  let A : Subgroup G := T.map ψ
  have hAab : IsElemAbelian p A := IsElemAbelian.map hTab ψ
  have hAcard : p ^ (n - 3) ≤ Nat.card A :=
    ggNSPosPC_card_map_ge h.prime hTcard hZscard hK0le h.four_le
  obtain ⟨y, hy_mem, hy_order, hyne⟩ := ggNSPosPC_exists_order_p_mem_cent h
  let Y : Subgroup G := Subgroup.zpowers y
  obtain ⟨hYcard, hYp⟩ := ggNSPosPC_zpowers_data hy_order
  have hYcent : Y ≤ Subgroup.centralizer (A : Set G) :=
    ggNSPosPC_zpowers_le_centralizer_map hy_mem.2
  let F : Subgroup G := A ⊔ Y
  have hAcent : A ≤ Subgroup.centralizer (Y : Set G) := fun a ha =>
    Subgroup.mem_centralizer_iff.mpr fun b hb =>
      ((Subgroup.mem_centralizer_iff.mp (hYcent hb)) a ha).symm
  have hFab : IsElemAbelian p F := CFSG.Walter.isElemAbelian_sup hAab hYp hAcent
  have hFcard : p ^ (n - 2) ≤ Nat.card ↥F := by
    by_cases hyA : y ∈ A
    · have hFA : F = A := by
        change A ⊔ Y = A
        rw [sup_eq_left.mpr (show Y ≤ A from Subgroup.zpowers_le.mpr hyA)]
      rw [hFA]
      exact (ggNSPosPC_card_map_eq_of_mem h.prime hTab hTcard hZscard hK0le hy_mem.2 hyA
        hyne hscalar).ge
    · exact ggNSPosPC_card_sup_ge_of_not_mem h.prime hyA hYcard hAcard hYcent h.four_le
  obtain ⟨E, hEF, hEab, hEcard⟩ := ggNSPosPC_exists_elemAbelian_le h.prime hFab hFcard
  let t : Su K 2 f n := ggNSPosPC_t hUF hn2
  obtain ⟨hU1, hU2⟩ := ggNSPosPC_zpowers_psi_t h hn2
  have hF_norm : F ≤ Subgroup.normalizer (Subgroup.zpowers (ψ t) : Set G) :=
    sup_le (ggNSPosPC_torus_map_le_normalizer hζp hζq hUF hn2 hTeq)
      (ggNSPosPC_zpowers_le_normalizer_map hy_mem.2)
  exact ⟨E, Subgroup.zpowers (ψ t), hEab, hEcard, hU1, hU2, le_trans hEF hF_norm⟩

end CFSG.StandardType

end
