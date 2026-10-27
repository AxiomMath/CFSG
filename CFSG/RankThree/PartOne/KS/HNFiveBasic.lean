module

public import CFSG.Monster.B.Pinned.Primes.Extraspecial
public import CFSG.Open.LocalVocabulary
public import CFSG.RankThree.CentralExtension.InvariantComplement

public section

namespace CFSG.RankThree.PartOne.KS.HNFive

open Subgroup CFSG.Monster.B.Pinned CFSG.RankThree.CentralExtension
open scoped Matrix

theorem fact5 : Fact (Nat.Prime 5) := ⟨by norm_num⟩

variable {G : Type*} [Group G]

abbrev QG (q : Fin 4 → G) : Subgroup G := closure (Set.range q)

@[expose] def HG {k : ℕ} (q : Fin 4 → G) (x : G) (r : Fin k → G) : Subgroup G :=
  closure ((QG q : Set G) ∪ {x} ∪ Set.range r)

theorem q_mem {q : Fin 4 → G} (i : Fin 4) : q i ∈ QG q := subset_closure ⟨i, rfl⟩

theorem Q_le_H {k : ℕ} {q : Fin 4 → G} {x : G} {r : Fin k → G} : QG q ≤ HG q x r := fun _ hg =>
  subset_closure (Or.inl (Or.inl hg))

theorem x_mem_H {k : ℕ} {q : Fin 4 → G} {x : G} {r : Fin k → G} : x ∈ HG q x r :=
  subset_closure (Or.inl (Or.inr rfl))

theorem r_mem_H {k : ℕ} {q : Fin 4 → G} {x : G} {r : Fin k → G} (j : Fin k) :
    r j ∈ HG q x r := subset_closure (Or.inr ⟨j, rfl⟩)

structure Rel {k : ℕ} (q : Fin 4 → G) (z x : G) (r : Fin k → G)
    (M : Matrix (Fin 4) (Fin 4) (ZMod 5)) (XU : GL (Fin 4) (ZMod 5)) (cx : Fin 4 → ℕ)
    (BU : Fin k → GL (Fin 4) (ZMod 5)) (cr : Fin k → Fin 4 → ℕ) : Prop where
  commData : CommData 5 q z M
  z_eq : bcomm (q 0) (q 1) = z
  x_pow : x ^ 5 = 1
  comm_x : x * z = z * x
  conj_x : ∀ i, x⁻¹ * q i * x =
    (List.ofFn fun j => q j ^ ((XU : Matrix (Fin 4) (Fin 4) (ZMod 5)) i j).val).prod * z ^ cx i
  comm_r : ∀ j, r j * z = z * r j
  conj_r : ∀ j i, (r j)⁻¹ * q i * r j =
    (List.ofFn fun l => q l ^ ((BU j : Matrix (Fin 4) (Fin 4) (ZMod 5)) i l).val).prod *
      z ^ cr j i

theorem bcomm_conj' (g a b : G) :
    bcomm (g⁻¹ * a * g) (g⁻¹ * b * g) = g⁻¹ * bcomm a b * g := by
  simp only [bcomm]
  group

theorem mul_pow_class_two {a b c : G}
    (hc : b * a = a * b * c) (hca : Commute c a) (hcb : Commute c b) (n : ℕ) :
    (a * b) ^ n = a ^ n * b ^ n * c ^ n.choose 2 := by
  have hbk : ∀ k : ℕ, b ^ k * a = a * b ^ k * c ^ k := by
    intro k
    induction k with
    | zero => simp
    | succ k ih =>
      calc b ^ (k + 1) * a = b * (b ^ k * a) := by rw [pow_succ', mul_assoc]
        _ = b * (a * b ^ k * c ^ k) := by rw [ih]
        _ = (b * a) * b ^ k * c ^ k := by group
        _ = a * b * c * b ^ k * c ^ k := by rw [hc]
        _ = a * b * (c * b ^ k) * c ^ k := by group
        _ = a * b * (b ^ k * c) * c ^ k := by rw [(hcb.pow_right k).eq]
        _ = a * b ^ (k + 1) * c ^ (k + 1) := by rw [pow_succ' b k, pow_succ' c k]; group
  induction n with
  | zero => simp
  | succ n ih =>
    have hT : (n + 1).choose 2 = n + n.choose 2 := by
      rw [Nat.choose_succ_succ, Nat.choose_one_right]
    have e1 : c ^ n.choose 2 * a = a * c ^ n.choose 2 := (hca.pow_left _).eq
    have e2 : c ^ n.choose 2 * b = b * c ^ n.choose 2 := (hcb.pow_left _).eq
    have e3 : c ^ n * b = b * c ^ n := (hcb.pow_left _).eq
    rw [pow_succ, ih, hT, pow_add c n (n.choose 2)]
    calc a ^ n * b ^ n * c ^ n.choose 2 * (a * b)
        = a ^ n * b ^ n * (c ^ n.choose 2 * a) * b := by group
      _ = a ^ n * (b ^ n * a) * (c ^ n.choose 2 * b) := by rw [e1]; group
      _ = a ^ n * (a * b ^ n * c ^ n) * (b * c ^ n.choose 2) := by rw [hbk, e2]
      _ = a ^ n * a * b ^ n * (c ^ n * b) * c ^ n.choose 2 := by group
      _ = a ^ n * a * b ^ n * (b * c ^ n) * c ^ n.choose 2 := by rw [e3]
      _ = a ^ (n + 1) * b ^ (n + 1) * (c ^ n * c ^ n.choose 2) := by
        rw [pow_succ a n, pow_succ b n]; group

theorem bcomm_map {G' : Type*} [Group G'] (ι : G →* G') (a b : G) :
    ι (bcomm a b) = bcomm (ι a) (ι b) := by
  simp only [bcomm, map_mul, map_inv]

theorem Rel.of_injective {G' : Type*} [Group G'] (ι : G →* G') (hι : Function.Injective ι)
    {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G} {M : Matrix (Fin 4) (Fin 4) (ZMod 5)}
    {XU : GL (Fin 4) (ZMod 5)} {cx : Fin 4 → ℕ} {BU : Fin k → GL (Fin 4) (ZMod 5)}
    {cr : Fin k → Fin 4 → ℕ}
    (h : Rel (fun j => ι (q j)) (ι z) (ι x) (fun j => ι (r j)) M XU cx BU cr) :
    Rel q z x r M XU cx BU cr := by
  have hz_eq : bcomm (q 0) (q 1) = z := hι (by rw [bcomm_map]; exact h.z_eq)
  refine ⟨⟨fun i => hι (by rw [map_pow, map_one]; exact h.commData.pow_q i),
    (orderOf_injective ι hι z).symm.trans h.commData.orderOf_z,
    fun i => hι (by rw [map_mul, map_mul]; exact h.commData.comm_z i),
    fun i j => hι (by rw [map_pow, bcomm_map]; exact h.commData.bcomm_q i j),
    h.commData.isUnit_det, ?_⟩, hz_eq,
    hι (by rw [map_pow, map_one]; exact h.x_pow),
    hι (by rw [map_mul, map_mul]; exact h.comm_x),
    fun i => hι (by
      have := h.conj_x i
      simp only [map_mul, map_inv, map_pow, map_list_prod, List.map_ofFn, Function.comp_def]
      exact this),
    fun j => hι (by rw [map_mul, map_mul]; exact h.comm_r j),
    fun j i => hι (by
      have := h.conj_r j i
      simp only [map_mul, map_inv, map_pow, map_list_prod, List.map_ofFn, Function.comp_def]
      exact this)⟩
  rw [← hz_eq]
  unfold bcomm
  exact mul_mem (mul_mem (mul_mem (inv_mem (subset_closure ⟨0, rfl⟩))
    (inv_mem (subset_closure ⟨1, rfl⟩))) (subset_closure ⟨0, rfl⟩)) (subset_closure ⟨1, rfl⟩)

namespace Rel

variable {k : ℕ} {q : Fin 4 → G} {z x : G} {r : Fin k → G} {M : Matrix (Fin 4) (Fin 4) (ZMod 5)}
  {XU : GL (Fin 4) (ZMod 5)} {cx : Fin 4 → ℕ} {BU : Fin k → GL (Fin 4) (ZMod 5)}
  {cr : Fin k → Fin 4 → ℕ} (hR : Rel q z x r M XU cx BU cr)
include hR

theorem z_mem : z ∈ QG q := hR.commData.mem_z

theorem orderOf_z : orderOf z = 5 := hR.commData.orderOf_z

theorem z_pow_five : z ^ 5 = 1 := by rw [← hR.orderOf_z]; exact pow_orderOf_eq_one z

theorem prod_mem (a : Fin 4 → ℕ) (c : ℕ) :
    (List.ofFn fun j => q j ^ a j).prod * z ^ c ∈ QG q := by
  refine mul_mem (list_prod_mem fun g hg => ?_) (pow_mem hR.z_mem _)
  obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hg
  exact pow_mem (q_mem j) _

theorem conj_x_mem (i : Fin 4) : x⁻¹ * q i * x ∈ QG q := by
  rw [hR.conj_x i]
  exact hR.prod_mem _ _

theorem conj_r_mem (j : Fin k) (i : Fin 4) : (r j)⁻¹ * q i * r j ∈ QG q := by
  rw [hR.conj_r j i]
  exact hR.prod_mem _ _

theorem x_conj_Q : ∀ g ∈ QG q, x⁻¹ * g * x ∈ QG q := fun _ hg =>
  CommData.conj_mem hR.conj_x_mem hg

theorem r_conj_Q (j : Fin k) : ∀ g ∈ QG q, (r j)⁻¹ * g * r j ∈ QG q := fun _ hg =>
  CommData.conj_mem (hR.conj_r_mem j) hg

theorem Q_commute_z {g : G} (hg : g ∈ QG q) : g * z = z * g :=
  hR.commData.commute_of_mem hg (mem_zpowers z)

theorem bcomm_mem_zpowers {u v : G} (hu : u ∈ QG q) (hv : v ∈ QG q) : bcomm u v ∈ zpowers z :=
  hR.commData.bcomm_mem hu hv

theorem lg_inv {y : G} (hy : y ∈ zpowers z) : lg 5 z y⁻¹ = -lg 5 z y := by
  have h := lg_mul (p := 5) hR.orderOf_z hy (inv_mem hy)
  rw [mul_inv_cancel, lg_one hR.orderOf_z] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem bcomm_mul_right {u v w : G} (hu : u ∈ QG q) (hv : v ∈ QG q) (hw : w ∈ QG q) :
    bcomm u (v * w) = bcomm u v * bcomm u w := by
  have h1 : bcomm (v * w) u = bcomm v u * bcomm w u := hR.commData.bcomm_mul hv hw hu
  have hcomm : Commute (bcomm u v) (bcomm u w) := by
    obtain ⟨a, ha⟩ := mem_zpowers_iff.1 (hR.bcomm_mem_zpowers hu hv)
    obtain ⟨b, hb⟩ := mem_zpowers_iff.1 (hR.bcomm_mem_zpowers hu hw)
    rw [← ha, ← hb]
    exact (Commute.refl z).zpow_zpow a b
  calc bcomm u (v * w) = (bcomm (v * w) u)⁻¹ := bcomm_swap _ _
    _ = (bcomm v u * bcomm w u)⁻¹ := by rw [h1]
    _ = (bcomm w u)⁻¹ * (bcomm v u)⁻¹ := mul_inv_rev _ _
    _ = bcomm u w * bcomm u v := by rw [← bcomm_swap, ← bcomm_swap]
    _ = bcomm u v * bcomm u w := hcomm.eq.symm

theorem bcomm_inv_right {u v : G} (hu : u ∈ QG q) (hv : v ∈ QG q) :
    bcomm u v⁻¹ = (bcomm u v)⁻¹ := by
  have h := hR.bcomm_mul_right hu (inv_mem hv) hv
  rw [inv_mul_cancel, show bcomm u 1 = 1 by simp [bcomm]] at h
  exact eq_inv_of_mul_eq_one_left h.symm

theorem psi_eq (u : G) :
    psi 5 q z u = coord 5 q z M u ᵥ* M := by
  rw [coord, Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hR.commData.isUnit_det,
    Matrix.vecMul_one]

theorem lg_bcomm {u v : G} (hu : u ∈ QG q) (hv : v ∈ QG q) :
    lg 5 z (bcomm u v) =
      coord 5 q z M u ⬝ᵥ (M *ᵥ coord 5 q z M v) := by
  have hpsi := hR.psi_eq u
  induction hv using closure_induction with
  | mem v hv =>
    obtain ⟨j, rfl⟩ := hv
    have h1 : lg 5 z (bcomm u (q j)) = psi 5 q z u j := rfl
    rw [h1, hpsi, hR.commData.coord_q j, Matrix.mulVec_single_one]
    rfl
  | one =>
    rw [show bcomm u 1 = 1 by simp [bcomm], lg_one hR.orderOf_z, hR.commData.coord_one,
      Matrix.mulVec_zero, dotProduct_zero]
  | mul v w hv hw ihv ihw =>
    rw [hR.bcomm_mul_right hu hv hw, lg_mul hR.orderOf_z (hR.bcomm_mem_zpowers hu hv)
      (hR.bcomm_mem_zpowers hu hw), ihv, ihw, hR.commData.coord_mul hv hw, Matrix.mulVec_add,
      dotProduct_add]
  | inv v hv ihv =>
    rw [hR.bcomm_inv_right hu hv, hR.lg_inv (hR.bcomm_mem_zpowers hu hv), ihv,
      hR.commData.coord_inv hv, Matrix.mulVec_neg, dotProduct_neg]

theorem pow_five_of_mem {g : G} (hg : g ∈ QG q) : g ^ 5 = 1 := by
  induction hg using closure_induction with
  | mem g hg =>
    obtain ⟨i, rfl⟩ := hg
    exact hR.commData.pow_q i
  | one => exact one_pow 5
  | mul a b ha hb iha ihb =>
    set c := bcomm b a with hcdef
    have hcz : c ∈ zpowers z := hR.bcomm_mem_zpowers hb ha
    have hc : b * a = a * b * c := by rw [hcdef, bcomm]; group
    have hca : Commute c a := (hR.commData.commute_of_mem ha hcz).symm
    have hcb : Commute c b := (hR.commData.commute_of_mem hb hcz).symm
    have hc5 : c ^ 5 = 1 := by
      obtain ⟨k, hk⟩ := mem_zpowers_iff.1 hcz
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hR.z_pow_five,
        one_zpow]
    rw [mul_pow_class_two hc hca hcb, iha, ihb, show (5 : ℕ).choose 2 = 5 * 2 by decide,
      pow_mul, hc5, one_pow, one_mul, one_mul]
  | inv a ha iha => rw [inv_pow, iha, inv_one]

section Finite

variable [Finite G]

theorem H_conj {h : G} (hh : h ∈ HG q x r) : ∀ g ∈ QG q, h⁻¹ * g * h ∈ QG q := by
  refine conj_mem_of_mem_closure ?_ hh
  intro b hb g hg
  rcases hb with (hb | hb) | hb
  · exact mul_mem (mul_mem (inv_mem hb) hg) hb
  · rw [Set.mem_singleton_iff.1 hb]
    exact hR.x_conj_Q g hg
  · obtain ⟨j, rfl⟩ := hb
    exact hR.r_conj_Q j g hg

theorem H_conj' {h : G} (hh : h ∈ HG q x r) : ∀ g ∈ QG q, h * g * h⁻¹ ∈ QG q := by
  intro g hg
  have := hR.H_conj (inv_mem hh) g hg
  rwa [inv_inv] at this

theorem conj_q_mem_H {g : G} (hg : g ∈ HG q x r) (i : Fin 4) : g⁻¹ * q i * g ∈ QG q :=
  hR.H_conj hg _ (q_mem i)

theorem Q_normal_H : ((QG q).subgroupOf (HG q x r)).Normal := by
  rw [normal_subgroupOf_iff Q_le_H]
  intro u g hu hg
  exact hR.H_conj' hg u hu

omit [Finite G] in
theorem H_commute_z {h : G} (hh : h ∈ HG q x r) : Commute h z := by
  induction hh using closure_induction with
  | mem g hg =>
    rcases hg with (hg | hg) | hg
    · exact hR.Q_commute_z hg
    · rw [Set.mem_singleton_iff.1 hg]
      exact hR.comm_x
    · obtain ⟨j, rfl⟩ := hg
      exact hR.comm_r j
  | one => exact Commute.one_left z
  | mul a b _ _ iha ihb => exact iha.mul_left ihb
  | inv a _ iha => exact iha.inv_left

end Finite

theorem actMat_x : CommData.actMat 5 q z M x = (XU : Matrix (Fin 4) (Fin 4) (ZMod 5)) :=
  hR.commData.actMat_eq _ cx hR.conj_x

theorem actMat_r (j : Fin k) :
    CommData.actMat 5 q z M (r j) = (BU j : Matrix (Fin 4) (Fin 4) (ZMod 5)) :=
  hR.commData.actMat_eq _ (cr j) (hR.conj_r j)

section ActionFinite

variable [Finite G]

theorem A_mul {g g' : G} (hg : g ∈ HG q x r) (hg' : g' ∈ HG q x r) :
    CommData.actMat 5 q z M (g * g') =
      CommData.actMat 5 q z M g * CommData.actMat 5 q z M g' :=
  hR.commData.actMat_mul (hR.conj_q_mem_H hg) (hR.conj_q_mem_H hg')

@[expose] noncomputable def AU : HG q x r →* GL (Fin 4) (ZMod 5) where
  toFun g := ⟨CommData.actMat 5 q z M (g : G), CommData.actMat 5 q z M (g : G)⁻¹,
    by rw [← hR.A_mul g.2 (inv_mem g.2), mul_inv_cancel, hR.commData.actMat_one],
    by rw [← hR.A_mul (inv_mem g.2) g.2, inv_mul_cancel, hR.commData.actMat_one]⟩
  map_one' := Units.ext hR.commData.actMat_one
  map_mul' g g' := Units.ext (hR.A_mul g.2 g'.2)

theorem AU_x : hR.AU ⟨x, x_mem_H⟩ = XU := Units.ext hR.actMat_x

theorem AU_r (j : Fin k) : hR.AU ⟨r j, r_mem_H j⟩ = BU j := Units.ext (hR.actMat_r j)

theorem AU_of_mem_Q {g : HG q x r} (hg : (g : G) ∈ QG q) : hR.AU g = 1 :=
  Units.ext (hR.commData.actMat_of_mem hg)

theorem Q_le_ker_AU : (QG q).subgroupOf (HG q x r) ≤ hR.AU.ker := fun g hg => by
  rw [MonoidHom.mem_ker]
  exact hR.AU_of_mem_Q (mem_subgroupOf.1 hg)

@[expose] noncomputable def rho [((QG q).subgroupOf (HG q x r)).Normal] :
    HG q x r ⧸ (QG q).subgroupOf (HG q x r) →* GL (Fin 4) (ZMod 5) :=
  QuotientGroup.lift _ hR.AU hR.Q_le_ker_AU

theorem rho_mk [((QG q).subgroupOf (HG q x r)).Normal] (g : HG q x r) :
    hR.rho (g : HG q x r ⧸ (QG q).subgroupOf (HG q x r)) = hR.AU g := rfl

theorem card_Q : Nat.card (QG q) = 5 ^ 5 := by
  have := fact5
  exact hR.commData.card_eq

omit [Finite G] in
theorem x_not_mem_Q (hX : XU ≠ 1) : x ∉ QG q := fun hx => by
  have h1 := hR.commData.actMat_of_mem hx
  rw [hR.actMat_x] at h1
  exact hX (Units.ext h1)

omit [Finite G] in
theorem orderOf_x (hX : XU ≠ 1) : orderOf x = 5 := by
  have := fact5
  have hx1 : x ≠ 1 := fun h => hR.x_not_mem_Q hX (h ▸ one_mem _)
  exact orderOf_eq_prime hR.x_pow hx1

theorem card_P (hX : XU ≠ 1) : Nat.card (QG q ⊔ zpowers x : Subgroup G) = 5 ^ 6 := by
  have := fact5
  rw [card_sup_zpowers (hR.orderOf_x hX) (hR.x_not_mem_Q hX) hR.x_conj_Q, hR.card_Q]
  norm_num

omit hR [Finite G] in
theorem P_le_H : QG q ⊔ zpowers x ≤ HG q x r :=
  sup_le Q_le_H (zpowers_le.2 x_mem_H)

theorem P_sylow (hX : XU ≠ 1) (h5 : (Nat.card G).factorization 5 = 6) :
    ∃ S : Sylow 5 G, (S : Subgroup G) = QG q ⊔ zpowers x := by
  have := fact5
  have hcard : Nat.card (QG q ⊔ zpowers x : Subgroup G) = 5 ^ (Nat.card G).factorization 5 := by
    rw [hR.card_P hX, h5]
  exact ⟨Sylow.ofCard _ hcard, rfl⟩

theorem card_center_Q : Nat.card (center (QG q)) = 5 := by
  have := fact5
  rw [hR.commData.center_eq]
  exact hR.commData.card_zQ

theorem center_Q_eq_commutator : center (QG q) = commutator (QG q) := by
  have := fact5
  rw [hR.commData.center_eq, hR.commData.commutator_eq hR.z_eq]

end ActionFinite

section Kernel

variable [Finite G] [((QG q).subgroupOf (HG q x r)).Normal]

omit [((QG q).subgroupOf (HG q x r)).Normal] in
theorem card_H_eq : Nat.card (HG q x r) =
    Nat.card (HG q x r ⧸ (QG q).subgroupOf (HG q x r)) * 5 ^ 5 := by
  rw [card_eq_card_quotient_mul_card_subgroup ((QG q).subgroupOf (HG q x r)),
    Nat.card_congr (subgroupOfEquivOfLe Q_le_H).toEquiv, hR.card_Q]

omit [((QG q).subgroupOf (HG q x r)).Normal] in
theorem factorization_HL_le (h5 : (Nat.card G).factorization 5 = 6) :
    (Nat.card (HG q x r ⧸ (QG q).subgroupOf (HG q x r))).factorization 5 ≤ 1 := by
  have hdvd : Nat.card (HG q x r) ∣ Nat.card G := card_subgroup_dvd_card _
  have h1 : (Nat.card (HG q x r)).factorization 5 ≤ 6 := by
    have := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').2 hdvd 5
    omega
  rw [hR.card_H_eq, Nat.factorization_mul Nat.card_pos.ne' (by norm_num), Finsupp.add_apply,
    Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same] at h1
  omega

theorem sylow_HL_cyclic (h5 : (Nat.card G).factorization 5 = 6)
    (S : Sylow 5 (HG q x r ⧸ (QG q).subgroupOf (HG q x r))) : IsCyclic S := by
  have := fact5
  have hS : Nat.card S =
      5 ^ (Nat.card (HG q x r ⧸ (QG q).subgroupOf (HG q x r))).factorization 5 :=
    Sylow.card_eq_multiplicity S
  have hle := hR.factorization_HL_le h5
  rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hle with h | h
  · rw [h, pow_zero] at hS
    have : Subsingleton S := (Nat.card_eq_one_iff_unique.1 hS).1
    exact isCyclic_of_subsingleton
  · rw [h, pow_one] at hS
    exact isCyclic_of_prime_card hS

theorem coprime_ker (hX : XU ≠ 1) (h5 : (Nat.card G).factorization 5 = 6) :
    (Nat.card hR.rho.ker).Coprime 5 := by
  have := fact5
  set xq : HG q x r ⧸ (QG q).subgroupOf (HG q x r) :=
    ((⟨x, x_mem_H⟩ : HG q x r) : HG q x r ⧸ (QG q).subgroupOf (HG q x r)) with hxq
  have hxrho : hR.rho xq = XU := hR.AU_x
  have hx5 : xq ^ 5 = 1 := by
    rw [hxq, ← QuotientGroup.mk_pow]
    have : (⟨x, x_mem_H⟩ : HG q x r) ^ 5 = 1 := Subtype.ext hR.x_pow
    rw [this, QuotientGroup.mk_one]
  have hord : orderOf XU = 5 := by
    have h1 : XU ^ 5 = 1 := by rw [← hxrho, ← map_pow, hx5, map_one]
    exact orderOf_eq_prime h1 hX
  have h5ran : 5 ∣ Nat.card hR.rho.range := by
    have hmem : XU ∈ hR.rho.range := ⟨xq, hxrho⟩
    have h1 : orderOf (⟨XU, hmem⟩ : hR.rho.range) = 5 := by
      rw [← Subgroup.orderOf_coe]
      exact hord
    exact (dvd_of_eq h1.symm).trans (orderOf_dvd_natCard (⟨XU, hmem⟩ : hR.rho.range))
  have hcard : Nat.card hR.rho.ker * Nat.card hR.rho.range =
      Nat.card (HG q x r ⧸ (QG q).subgroupOf (HG q x r)) := by
    rw [← index_ker]
    exact card_mul_index _
  have hle := hR.factorization_HL_le h5
  rw [← hcard, Nat.factorization_mul Nat.card_pos.ne' Nat.card_pos.ne', Finsupp.add_apply] at hle
  have h1 : 1 ≤ (Nat.card hR.rho.range).factorization 5 :=
    (Nat.prime_five.dvd_iff_one_le_factorization Nat.card_pos.ne').1 h5ran
  rw [Nat.coprime_comm, Nat.prime_five.coprime_iff_not_dvd]
  intro hd
  have h2 : 1 ≤ (Nat.card hR.rho.ker).factorization 5 :=
    (Nat.prime_five.dvd_iff_one_le_factorization Nat.card_pos.ne').1 hd
  omega

@[expose] noncomputable def R (T : Subgroup (GL (Fin 4) (ZMod 5))) :
    Subgroup (HG q x r ⧸ (QG q).subgroupOf (HG q x r)) :=
  T.comap hR.rho

theorem AU_mem_normalizer (T : Subgroup (GL (Fin 4) (ZMod 5)))
    (hXn : XU ∈ normalizer (T : Set (GL (Fin 4) (ZMod 5)))) (hB : ∀ j, BU j ∈ T)
    (g : HG q x r) : hR.AU g ∈ normalizer (T : Set (GL (Fin 4) (ZMod 5))) := by
  obtain ⟨g, hg⟩ := g
  refine closure_induction
    (p := fun g hg => hR.AU ⟨g, hg⟩ ∈ normalizer (T : Set (GL (Fin 4) (ZMod 5)))) ?_ ?_ ?_ ?_ hg
  · intro g hg'
    simp only [Set.mem_union, Set.mem_singleton_iff, SetLike.mem_coe, Set.mem_range] at hg'
    rcases hg' with (hQ | rfl) | ⟨j, rfl⟩
    · rw [hR.AU_of_mem_Q hQ]
      exact one_mem _
    · rw [hR.AU_x]
      exact hXn
    · rw [hR.AU_r]
      exact le_normalizer (hB j)
  · rw [show (⟨1, one_mem _⟩ : HG q x r) = 1 from rfl, map_one]
    exact one_mem _
  · intro a b ha hb iha ihb
    rw [show (⟨a * b, mul_mem ha hb⟩ : HG q x r) = ⟨a, ha⟩ * ⟨b, hb⟩ from rfl, map_mul]
    exact mul_mem iha ihb
  · intro a ha iha
    rw [show (⟨a⁻¹, inv_mem ha⟩ : HG q x r) = (⟨a, ha⟩)⁻¹ from rfl, map_inv]
    exact inv_mem iha

theorem R_normal (T : Subgroup (GL (Fin 4) (ZMod 5)))
    (hXn : XU ∈ normalizer (T : Set (GL (Fin 4) (ZMod 5)))) (hB : ∀ j, BU j ∈ T) :
    (hR.R T).Normal := ⟨fun r hr y => by
  rw [R, mem_comap] at hr ⊢
  rw [map_mul, map_mul, map_inv]
  have hy : hR.rho y ∈ normalizer (T : Set (GL (Fin 4) (ZMod 5))) := by
    induction y using QuotientGroup.induction_on with
    | H g => exact hR.AU_mem_normalizer T hXn hB g
  exact ((mem_normalizer_iff.1 hy) _).1 hr⟩

theorem coprime_R (T : Subgroup (GL (Fin 4) (ZMod 5))) (hT : IsPGroup 2 T) (hX : XU ≠ 1)
    (h5 : (Nat.card G).factorization 5 = 6) : (Nat.card (hR.R T)).Coprime 5 := by
  set f : hR.R T →* GL (Fin 4) (ZMod 5) := hR.rho.comp (hR.R T).subtype with hf
  have hker_le : hR.rho.ker ≤ hR.R T := fun r hr => by
    rw [R, mem_comap, MonoidHom.mem_ker.1 hr]
    exact one_mem _
  have hker : f.ker = hR.rho.ker.subgroupOf (hR.R T) := by
    ext r
    rw [hf, MonoidHom.mem_ker, MonoidHom.comp_apply, mem_subgroupOf, MonoidHom.mem_ker]
    rfl
  have hrange : f.range ≤ T := by
    rintro _ ⟨r, rfl⟩
    exact r.2
  have hcard : Nat.card f.ker * Nat.card f.range = Nat.card (hR.R T) := by
    rw [← index_ker]
    exact card_mul_index _
  have h1 : Nat.card f.ker = Nat.card hR.rho.ker := by
    rw [hker]
    exact Nat.card_congr (subgroupOfEquivOfLe hker_le).toEquiv
  have h2 : Nat.card f.range ∣ Nat.card T := card_dvd_of_le hrange
  obtain ⟨n, hn⟩ := hT.exists_card_eq
  rw [← hcard, h1]
  rw [hn] at h2
  exact Nat.coprime_mul_iff_left.2 ⟨hR.coprime_ker hX h5,
    Nat.Coprime.coprime_dvd_left h2 (Nat.Coprime.pow_left n (by norm_num))⟩

end Kernel

end Rel

end CFSG.RankThree.PartOne.KS.HNFive
