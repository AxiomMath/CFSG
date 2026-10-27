module

public import CFSG.Quasithin.EmptyFaithful.S146F14
public import CFSG.Quasithin.EmptyFaithful.S146F19

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

section Defs

variable {G : Type} [Group G]

structure IsDecP (T M H : Subgroup G) (p : ℕ) (H₀ H₁ H₂ : Subgroup G) (t : G) : Prop where
  le : H₀ ≤ H
  normal : H ≤ Subgroup.normalizer (H₀ : Set G)
  eq : H = H₀ ⊔ T
  indexT : (T ⊓ Subgroup.normalizer (H₁ : Set G)).relIndex T = 2
  Q₁ : pCoreOf 2 H ≤ H₁
  Q₂ : pCoreOf 2 H ≤ H₂
  le₁ : H₁ ≤ H₀
  le₂ : H₂ ≤ H₀
  sup : H₀ = H₁ ⊔ H₂
  inf : H₁ ⊓ H₂ = pCoreOf 2 H
  comm : ⁅H₁, H₂⁆ ≤ pCoreOf 2 H
  dihedral₁ : SecIso H₁ (pCoreOf 2 H) (DihedralGroup p)
  dihedral₂ : SecIso H₂ (pCoreOf 2 H) (DihedralGroup p)
  t_mem : t ∈ T
  t_not : t ∉ Subgroup.normalizer (H₁ : Set G)
  conj : H₂ = conjSub t H₁
  dir_inf : uHi T M H H₁ ⊓ uHi T M H H₂ = quasithinOmegaOneCenter T
  dir_sup : uHi T M H H₁ ⊔ uHi T M H H₂ = uK T M H ⊔ quasithinOmegaOneCenter T
  cent₁ : ⁅uHi T M H H₁, H₂⁆ ≤ quasithinOmegaOneCenter T
  cent₂ : ⁅uHi T M H H₂, H₁⁆ ≤ quasithinOmegaOneCenter T
  rank₁ : (p = 5 → mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 4) ∧
    (p = 3 → mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 2 ∨
      mIdx (uHi T M H H₁) (quasithinOmegaOneCenter T) = 4)
  rank₂ : (p = 5 → mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = 4) ∧
    (p = 3 → mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = 2 ∨
      mIdx (uHi T M H H₂) (quasithinOmegaOneCenter T) = 4)

end Defs

section Basic

variable {G : Type} [Group G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

namespace IsDecP

theorem H₂_le_normalizer_H₁ (h : IsDecP T M H p H₀ H₁ H₂ t) :
    H₂ ≤ Subgroup.normalizer (H₁ : Set G) :=
  S146A.le_normalizer_of_commutator_le h.Q₁ h.comm

theorem H₁_le_normalizer_H₂ (h : IsDecP T M H p H₀ H₁ H₂ t) :
    H₁ ≤ Subgroup.normalizer (H₂ : Set G) :=
  S146A.le_normalizer_of_commutator_le h.Q₂ (by rw [Subgroup.commutator_comm]; exact h.comm)

theorem H₀_le_normalizer_H₁ (h : IsDecP T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (H₁ : Set G) := by
  rw [h.sup]
  exact sup_le Subgroup.le_normalizer h.H₂_le_normalizer_H₁

theorem H₀_le_normalizer_H₂ (h : IsDecP T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (H₂ : Set G) := by
  rw [h.sup]
  exact sup_le h.H₁_le_normalizer_H₂ Subgroup.le_normalizer

theorem le_normalizer_inf (h : IsDecP T M H p H₀ H₁ H₂ t) :
    T ≤ Subgroup.normalizer ((T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) : Set G) := by
  have h2 : ((T ⊓ Subgroup.normalizer (H₁ : Set G)).subgroupOf T).index = 2 := h.indexT
  have hn : ((T ⊓ Subgroup.normalizer (H₁ : Set G)).subgroupOf T).Normal :=
    Subgroup.normal_of_index_eq_two h2
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mp hn

theorem inf_le_inf_normalizer (h : IsDecP T M H p H₀ H₁ H₂ t) :
    T ⊓ H₀ ≤ T ⊓ Subgroup.normalizer (H₁ : Set G) :=
  le_inf inf_le_left (inf_le_right.trans h.H₀_le_normalizer_H₁)

theorem inf_normalizer_swap_eq (h : IsDecP T M H p H₀ H₁ H₂ t) :
    T ⊓ Subgroup.normalizer (H₂ : Set G) = T ⊓ Subgroup.normalizer (H₁ : Set G) := by
  have hn := h.le_normalizer_inf h.t_mem
  have hmem : ∀ x : G, x ∈ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) ↔
      t * x * t⁻¹ ∈ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) := fun x =>
    Subgroup.mem_normalizer_iff.mp hn x
  ext s
  constructor
  · rintro ⟨hsT, hsN⟩
    have hs : conjSub s H₂ = H₂ := conjSub_eq_of_mem_normalizer hsN
    rw [h.conj] at hs
    have e1 : conjSub (t⁻¹ * s * t) H₁ = H₁ := by
      calc conjSub (t⁻¹ * s * t) H₁ = conjSub t⁻¹ (conjSub s (conjSub t H₁)) := by
            rw [mul_assoc, conjSub_mul, conjSub_mul]
        _ = conjSub t⁻¹ (conjSub t H₁) := by rw [hs]
        _ = H₁ := conjSub_conjSub_inv t H₁
    have hy : t⁻¹ * s * t ∈ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) :=
      ⟨T.mul_mem (T.mul_mem (T.inv_mem h.t_mem) hsT) h.t_mem,
        CosetGeom.mem_normalizer_of_conjSub_eq e1⟩
    have := (hmem _).mp hy
    have e : t * (t⁻¹ * s * t) * t⁻¹ = s := by group
    rw [e] at this
    exact this
  · rintro ⟨hsT, hsN⟩
    refine ⟨hsT, ?_⟩
    have hy : t⁻¹ * s * t ∈ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) := by
      refine (hmem _).mpr ?_
      have e : t * (t⁻¹ * s * t) * t⁻¹ = s := by group
      rw [e]
      exact ⟨hsT, hsN⟩
    have hy' : conjSub (t⁻¹ * s * t) H₁ = H₁ := conjSub_eq_of_mem_normalizer hy.2
    have e1 : conjSub s H₂ = H₂ := by
      calc conjSub s H₂ = conjSub s (conjSub t H₁) := by rw [h.conj]
        _ = conjSub t (conjSub (t⁻¹ * s * t) H₁) := by
            rw [← conjSub_mul, ← conjSub_mul]
            congr 1
            group
        _ = conjSub t H₁ := by rw [hy']
        _ = H₂ := h.conj.symm
    exact CosetGeom.mem_normalizer_of_conjSub_eq e1

theorem swap (h : IsDecP T M H p H₀ H₁ H₂ t) : IsDecP T M H p H₀ H₂ H₁ t⁻¹ := by
  have hconj : conjSub t⁻¹ H₂ = H₁ := by
    rw [h.conj]
    exact conjSub_conjSub_inv t H₁
  refine
    { le := h.le
      normal := h.normal
      eq := h.eq
      indexT := by rw [h.inf_normalizer_swap_eq]; exact h.indexT
      Q₁ := h.Q₂
      Q₂ := h.Q₁
      le₁ := h.le₂
      le₂ := h.le₁
      sup := by rw [sup_comm]; exact h.sup
      inf := by rw [inf_comm]; exact h.inf
      comm := by rw [Subgroup.commutator_comm]; exact h.comm
      dihedral₁ := h.dihedral₂
      dihedral₂ := h.dihedral₁
      t_mem := T.inv_mem h.t_mem
      t_not := ?_
      conj := hconj.symm
      dir_inf := by rw [inf_comm]; exact h.dir_inf
      dir_sup := by rw [sup_comm]; exact h.dir_sup
      cent₁ := h.cent₂
      cent₂ := h.cent₁
      rank₁ := h.rank₂
      rank₂ := h.rank₁ }
  intro hmem
  have h1 : conjSub t⁻¹ H₂ = H₂ := conjSub_eq_of_mem_normalizer hmem
  have h12 : H₁ = H₂ := by rw [← hconj, h1]
  apply h.t_not
  have h2 : conjSub t H₁ = H₁ := by rw [← h.conj, ← h12]
  exact CosetGeom.mem_normalizer_of_conjSub_eq h2

theorem conjSub_eq_of_not_mem (h : IsDecP T M H p H₀ H₁ H₂ t) {s : G} (hsT : s ∈ T)
    (hs : s ∉ Subgroup.normalizer (H₁ : Set G)) : conjSub s H₁ = H₂ := by
  have hs0 : s ∉ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) := fun hh => hs hh.2
  have ht0 : t ∉ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) := fun hh => h.t_not hh.2
  have hst : s * t⁻¹ ∈ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) :=
    mul_inv_mem_of_relIndex_two h.indexT hsT h.t_mem hs0 ht0
  have hst2 : s * t⁻¹ ∈ Subgroup.normalizer (H₂ : Set G) := by
    have : s * t⁻¹ ∈ (T ⊓ Subgroup.normalizer (H₂ : Set G) : Subgroup G) := by
      rw [h.inf_normalizer_swap_eq]
      exact hst
    exact this.2
  have e : s = (s * t⁻¹) * t := by group
  rw [e, conjSub_mul, ← h.conj]
  exact conjSub_eq_of_mem_normalizer hst2

end IsDecP

theorem IsDec12.toIsDecP [Finite G] {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDec12 T M H p H₀ H₁ H₂ t) : IsDecP T M H p H₀ H₁ H₂ t := by
  have hTH : T ≤ H := hred.isHTM.1.1
  have htH₀ : t ∉ H₀ := fun ht0 => h.t_not (h.H₀_le_normalizer_H₁ ht0)
  have heq : H = H₀ ⊔ T := by
    have h1 : H₀ ⊔ T ≤ H := sup_le h.le hTH
    have hmul := Subgroup.relIndex_mul_relIndex H₀ (H₀ ⊔ T) H le_sup_left h1
    have h2 : H₀.relIndex H = 2 := h.index
    have hne0 : H₀.relIndex (H₀ ⊔ T) ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hne1 : H₀.relIndex (H₀ ⊔ T) ≠ 1 := fun h1' =>
      htH₀ ((Subgroup.relIndex_eq_one.mp h1') ((le_sup_right : T ≤ H₀ ⊔ T) h.t_mem))
    rw [h2] at hmul
    have hdvd : H₀.relIndex (H₀ ⊔ T) ∣ 2 := ⟨(H₀ ⊔ T).relIndex H, hmul.symm⟩
    have h22 : H₀.relIndex (H₀ ⊔ T) = 2 := by
      rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h3 | h3
      · exact absurd h3 hne1
      · exact h3
    have hK : (H₀ ⊔ T).relIndex H = 1 := by
      rw [h22] at hmul
      omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp hK) h1
  exact
    { le := h.le
      normal := h.le_normalizer_H₀
      eq := heq
      indexT := IsDec12.relIndex_inf_normalizer_eq_two hred h
      Q₁ := h.Q₁
      Q₂ := h.Q₂
      le₁ := h.le₁
      le₂ := h.le₂
      sup := h.sup
      inf := h.inf
      comm := h.comm
      dihedral₁ := h.dihedral₁
      dihedral₂ := h.dihedral₂
      t_mem := h.t_mem
      t_not := h.t_not
      conj := h.conj
      dir_inf := h.dir_inf
      dir_sup := h.dir_sup
      cent₁ := h.cent₁
      cent₂ := h.cent₂
      rank₁ := h.rank₁
      rank₂ := h.rank₂ }

theorem IsDecP.toIsDec12 (h : IsDecP T M H p H₀ H₁ H₂ t) (hidx : H₀.relIndex H = 2) :
    IsDec12 T M H p H₀ H₁ H₂ t :=
  { le := h.le
    index := hidx
    Q₁ := h.Q₁
    Q₂ := h.Q₂
    le₁ := h.le₁
    le₂ := h.le₂
    sup := h.sup
    inf := h.inf
    comm := h.comm
    dihedral₁ := h.dihedral₁
    dihedral₂ := h.dihedral₂
    t_mem := h.t_mem
    t_not := h.t_not
    conj := h.conj
    dir_inf := h.dir_inf
    dir_sup := h.dir_sup
    cent₁ := h.cent₁
    cent₂ := h.cent₂
    rank₁ := h.rank₁
    rank₂ := h.rank₂ }

end Basic

section Norm

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem IsDecP.card_H₁_gen (hp0 : p ≠ 0) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    Nat.card H₁ = 2 * p * Nat.card (pCoreOf 2 H) := by
  have : NeZero p := ⟨hp0⟩
  obtain ⟨hQn, ⟨e⟩⟩ := h.dihedral₁
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup ((pCoreOf 2 H).subgroupOf H₁)
  rw [Nat.card_congr e.toEquiv, Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.Q₁).toEquiv] at h1
  have h6 : Nat.card (DihedralGroup p) = 2 * p := by
    rw [Nat.card_eq_fintype_card, DihedralGroup.card]
  rw [h1, h6]

theorem IsDecP.isSylowTwoOf_inf_H₁ (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    IsSylowTwoOf ((T ⊓ H₀) ⊓ H₁) H₁ ∧ pCoreOf 2 H ≤ (T ⊓ H₀) ⊓ H₁ ∧
      (pCoreOf 2 H).relIndex ((T ⊓ H₀) ⊓ H₁) = 2 := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hTsyl : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hT₀ : IsSylowTwoOf (T ⊓ H₀) H₀ := B6.isSylowTwoOf_inf_normal hTsyl h.le h.normal
  have hS₁ : IsSylowTwoOf ((T ⊓ H₀) ⊓ H₁) H₁ :=
    B6.isSylowTwoOf_inf_normal hT₀ h.le₁ h.H₀_le_normalizer_H₁
  have hQT : pCoreOf 2 H ≤ T := S.pCoreOf_le_T hH
  have hQS : pCoreOf 2 H ≤ (T ⊓ H₀) ⊓ H₁ := le_inf (le_inf hQT (h.Q₁.trans h.le₁)) h.Q₁
  have hQ2 : IsPGroup 2 (pCoreOf 2 H) := hTsyl.isPGroup.to_le hQT
  have hodd : Odd p := hred.prime.odd_of_ne_two hred.odd
  have hp2 : ¬ 2 ∣ p := by
    rcases hodd with ⟨k, hk⟩
    omega
  have htw : twoPart H₁ = 2 ^ 1 * Nat.card (pCoreOf 2 H) :=
    twoPart_eq_of_card_eq_odd_mul hQ2 hp2 (by rw [h.card_H₁_gen hred.prime.ne_zero]; ring)
  have hcard : Nat.card ↥((T ⊓ H₀) ⊓ H₁) = 2 * Nat.card (pCoreOf 2 H) := by
    rw [hS₁.card_eq, htw]
    ring
  refine ⟨hS₁, hQS, ?_⟩
  have hmul := Subgroup.relIndex_mul_card (pCoreOf 2 H) ((T ⊓ H₀) ⊓ H₁)
  rw [inf_eq_left.mpr hQS, hcard] at hmul
  have hQpos : 0 < Nat.card (pCoreOf 2 H) := Nat.card_pos
  exact Nat.eq_of_mul_eq_mul_right hQpos hmul

end Norm

section Module

variable {G : Type} [Group G] [Finite G] {T M H : Subgroup G} {p : ℕ} {H₀ H₁ H₂ : Subgroup G} {t : G}

omit [Finite G] in
theorem IsDecP.conjSub_uHi {PQ : Subgroup G} (hred : IsRedCE T M H PQ p)
    (h : IsDecP T M H p H₀ H₁ H₂ t) : conjSub t (uHi T M H H₁) = uHi T M H H₂ := by
  have hH : IsHTM T M H := hred.isHTM
  have hTH : T ≤ H := hH.1.1
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hsZ : t ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) :=
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T h.t_mem)
  unfold uHi
  have e1 : conjSub t ⁅conjClosure (VZ T M) H, H₁⁆ =
      ⁅conjSub t (conjClosure (VZ T M) H), conjSub t H₁⁆ := (conjSub_commutator t _ _).symm
  have e2 : conjSub t (conjClosure (VZ T M) H) = conjClosure (VZ T M) H :=
    conjSub_eq_of_mem_normalizer (hHU (hTH h.t_mem))
  have e3 : conjSub t (quasithinOmegaOneCenter T) = quasithinOmegaOneCenter T :=
    conjSub_eq_of_mem_normalizer hsZ
  rw [show conjSub t (⁅conjClosure (VZ T M) H, H₁⁆ ⊔ quasithinOmegaOneCenter T) =
      conjSub t ⁅conjClosure (VZ T M) H, H₁⁆ ⊔ conjSub t (quasithinOmegaOneCenter T) from
      Subgroup.map_sup _ _ _, e1, e2, e3, ← h.conj]

theorem IsDecP.le_normalizer_uHi (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    H₁ ≤ Subgroup.normalizer (uHi T M H H₁ : Set G) := by
  have hH : IsHTM T M H := hred.isHTM
  have hH₁H : H₁ ≤ H := h.le₁.trans h.le
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hNZ : H₁ ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    S.normalizer_Z.ge (S.le_mcOf hH (hH₁H hx))
  exact (le_inf (S145.le_normalizer_commutator (hH₁H.trans hHU) Subgroup.le_normalizer) hNZ).trans
    (Subgroup.inf_normalizer_le_normalizer_sup _ _)

theorem IsDecP.le_normalizer_uHi₁ (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (uHi T M H H₁ : Set G) := by
  rw [h.sup]
  exact sup_le (h.le_normalizer_uHi S hred)
    (S146A.le_normalizer_of_commutator_le (Z_le_uHi T M H H₁) h.cent₁)

theorem IsDecP.le_normalizer_uHi₂ (S : Setting146 G T M) {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) :
    H₀ ≤ Subgroup.normalizer (uHi T M H H₂ : Set G) :=
  h.swap.le_normalizer_uHi₁ S hred

omit [Finite G] in
theorem inf_normalizer_le_normalizer_uHi (hTH : T ≤ H) (X : Subgroup G) :
    T ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (uHi T M H X : Set G) := by
  have hHU : H ≤ Subgroup.normalizer (conjClosure (VZ T M) H : Set G) :=
    le_normalizer_conjClosure _ _
  have hNZ : T ⊓ Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (le_centralizer_quasithinOmegaOneCenter T hx.1)
  exact (le_inf (S145.le_normalizer_commutator (inf_le_left.trans (hTH.trans hHU)) inf_le_right)
    hNZ).trans (Subgroup.inf_normalizer_le_normalizer_sup _ _)

omit [Finite G] in
theorem IsDecP.conjSub_uHi_of_not_mem {PQ : Subgroup G}
    (hred : IsRedCE T M H PQ p) (h : IsDecP T M H p H₀ H₁ H₂ t) {s : G} (hsT : s ∈ T)
    (hs : s ∉ Subgroup.normalizer (H₁ : Set G)) :
    conjSub s (uHi T M H H₁) = uHi T M H H₂ := by
  have hs0 : s ∉ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) := fun hh => hs hh.2
  have ht0 : t ∉ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) := fun hh => h.t_not hh.2
  have hst : s * t⁻¹ ∈ (T ⊓ Subgroup.normalizer (H₁ : Set G) : Subgroup G) :=
    mul_inv_mem_of_relIndex_two h.indexT hsT h.t_mem hs0 ht0
  have hst2 : s * t⁻¹ ∈ (T ⊓ Subgroup.normalizer (H₂ : Set G) : Subgroup G) := by
    rw [h.inf_normalizer_swap_eq]
    exact hst
  have hstU : s * t⁻¹ ∈ Subgroup.normalizer (uHi T M H H₂ : Set G) :=
    inf_normalizer_le_normalizer_uHi hred.isHTM.1.1 H₂ hst2
  have e : s = (s * t⁻¹) * t := by group
  rw [e, conjSub_mul, h.conjSub_uHi hred]
  exact conjSub_eq_of_mem_normalizer hstU

end Module

end CFSG.Quasithin
