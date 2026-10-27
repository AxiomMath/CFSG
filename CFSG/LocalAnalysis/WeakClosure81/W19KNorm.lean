module

public import CFSG.LocalAnalysis.WeakClosure81.W19Conf
public import CFSG.LocalAnalysis.WeakClosure81.W19Four
public import CFSG.LocalAnalysis.WeakClosure81.W19KSeries

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

structure KData196 (p : ℕ) (H T X A : Subgroup G) : Prop where
  prime : p.Prime
  odd : p ≠ 2
  isSylow : IsSylowIn 2 T H
  X_le : X ≤ H
  isPGroup : IsPGroup p X
  normal : H ≤ normalizer ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G)
  A_le : A ≤ T
  isElemAbelian : IsElemAbelian 2 A
  relIndex : (pCoreOf 2 H).relIndex A = 2
  not_le : ¬ ⁅X, A⁆ ≤ pCoreOf 2 H

@[expose] def KN196 (H X A : Subgroup G) : Subgroup G :=
  ⁅X ⊔ pCoreOf 2 H, A⁆ ⊔ pCoreOf 2 H

@[expose] def K196 (H T X A : Subgroup G) : Subgroup G :=
  KN196 H X A ⊔ E1.tauOf H T A

namespace KData196

variable {p : ℕ} {H T X A : Subgroup G}

theorem T_le_H (h : KData196 p H T X A) : T ≤ H := h.isSylow.le

theorem A_le_H (h : KData196 p H T X A) : A ≤ H := h.A_le.trans h.T_le_H

theorem pCoreOf_le_T (h : KData196 p H T X A) : pCoreOf 2 H ≤ T :=
  E1.pCoreOf_two_le_of_isSylowIn h.isSylow

theorem H_le_normalizer_pCoreOf (_h : KData196 p H T X A) :
    H ≤ normalizer (pCoreOf 2 H : Set G) :=
  CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H

theorem isPGroup_A (h : KData196 p H T X A) : IsPGroup 2 A :=
  h.isSylow.isPGroup.to_le h.A_le

theorem isPGroup_pCoreOf (_h : KData196 p H T X A) : IsPGroup 2 (pCoreOf 2 H) :=
  CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H

theorem N_le_normalizer_pCoreOf (h : KData196 p H T X A) :
    X ⊔ pCoreOf 2 H ≤ normalizer (pCoreOf 2 H : Set G) :=
  sup_le (h.X_le.trans h.H_le_normalizer_pCoreOf) Subgroup.le_normalizer

theorem A_le_normalizer_N (h : KData196 p H T X A) :
    A ≤ normalizer ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
  h.A_le_H.trans h.normal

theorem A_le_normalizer_pCoreOf (h : KData196 p H T X A) :
    A ≤ normalizer (pCoreOf 2 H : Set G) :=
  h.A_le_H.trans h.H_le_normalizer_pCoreOf

theorem pow_mem_of_mem_N (h : KData196 p H T X A) {x : G} (hx : x ∈ X ⊔ pCoreOf 2 H) :
    ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 H :=
  exists_pow_mem_of_mem_sup_pGroup h.isPGroup (h.X_le.trans h.H_le_normalizer_pCoreOf) hx

theorem pCoreOf_le_tauOf (h : KData196 p H T X A) : pCoreOf 2 H ≤ E1.tauOf H T A :=
  le_sup_right.trans (E1.le_tauOf h.isSylow h.A_le h.isElemAbelian)

theorem A_le_tauOf (h : KData196 p H T X A) : A ≤ E1.tauOf H T A :=
  le_sup_left.trans (E1.le_tauOf h.isSylow h.A_le h.isElemAbelian)

theorem isPGroup_tauOf (h : KData196 p H T X A) : IsPGroup 2 (E1.tauOf H T A) :=
  h.isSylow.isPGroup.to_le (E1.tauOf_le H T A)

theorem tauOf_le_H (h : KData196 p H T X A) : E1.tauOf H T A ≤ H :=
  (E1.tauOf_le H T A).trans h.T_le_H

theorem tauOf_le_normalizer_N (h : KData196 p H T X A) :
    E1.tauOf H T A ≤ normalizer ((X ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
  h.tauOf_le_H.trans h.normal

theorem tauOf_le_normalizer_pCoreOf (h : KData196 p H T X A) :
    E1.tauOf H T A ≤ normalizer (pCoreOf 2 H : Set G) :=
  h.tauOf_le_H.trans h.H_le_normalizer_pCoreOf

theorem KN_le_N (h : KData196 p H T X A) : KN196 H X A ≤ X ⊔ pCoreOf 2 H :=
  sup_le (E1.commutator_le_of_le_normalizer h.A_le_normalizer_N) le_sup_right

theorem pCoreOf_le_KN (_h : KData196 p H T X A) : pCoreOf 2 H ≤ KN196 H X A := le_sup_right

theorem KN_le_H (h : KData196 p H T X A) : KN196 H X A ≤ H :=
  h.KN_le_N.trans (sup_le h.X_le (h.pCoreOf_le_T.trans h.T_le_H))

theorem KN_le_normalizer_pCoreOf (h : KData196 p H T X A) :
    KN196 H X A ≤ normalizer (pCoreOf 2 H : Set G) :=
  h.KN_le_N.trans h.N_le_normalizer_pCoreOf

theorem pow_mem_of_mem_KN (h : KData196 p H T X A) {x : G} (hx : x ∈ KN196 H X A) :
    ∃ k : ℕ, x ^ p ^ k ∈ pCoreOf 2 H :=
  h.pow_mem_of_mem_N (h.KN_le_N hx)

theorem KN_inf_T_le (h : KData196 p H T X A) : KN196 H X A ⊓ T ≤ pCoreOf 2 H := by
  intro x hx
  obtain ⟨k, hk⟩ := h.pow_mem_of_mem_KN hx.1
  obtain ⟨j, hj⟩ := h.isSylow.isPGroup ⟨x, hx.2⟩
  exact E1.mem_of_pow_mem_two_p h.prime h.odd hk (by
    have : x ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    rw [this]
    exact Subgroup.one_mem _)

theorem not_KN_le_pCoreOf (h : KData196 p H T X A) : ¬ KN196 H X A ≤ pCoreOf 2 H := fun hle =>
  h.not_le ((Subgroup.commutator_mono le_sup_left le_rfl).trans (le_sup_left.trans hle))

theorem tauOf_le_normalizer_A_sup (h : KData196 p H T X A) :
    E1.tauOf H T A ≤ normalizer ((A ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
  intro t ht
  apply E1.mem_normalizer_of_conj_mem
  intro x hx
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A (pCoreOf 2 H)
    h.A_le_normalizer_pCoreOf] at hx
  obtain ⟨a, ha, o, ho, rfl⟩ := hx
  have h1 : ⁅t, a⁆ ∈ pCoreOf 2 H := ht.2.2 a ha
  have h2 : t * o * t⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.1 (h.tauOf_le_normalizer_pCoreOf ht) o).1 ho
  have e : t * (a * o) * t⁻¹ = ⁅t, a⁆ * a * (t * o * t⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right h1)
    (Subgroup.mem_sup_left ha)) (Subgroup.mem_sup_right h2)

theorem KN_eq_comm_sup (h : KData196 p H T X A) :
    KN196 H X A = ⁅X ⊔ pCoreOf 2 H, A ⊔ pCoreOf 2 H⁆ ⊔ pCoreOf 2 H :=
  le_antisymm (sup_le_sup_right (Subgroup.commutator_mono le_rfl le_sup_left) _)
    (sup_le (E1.commutator_sup_le h.N_le_normalizer_pCoreOf h.A_le_normalizer_pCoreOf)
      le_sup_right)

theorem tauOf_le_normalizer_KN (h : KData196 p H T X A) :
    E1.tauOf H T A ≤ normalizer ((KN196 H X A : Subgroup G) : Set G) := by
  intro t ht
  rw [h.KN_eq_comm_sup]
  exact E1.mem_normalizer_sup (E1.mem_normalizer_commutator (h.tauOf_le_normalizer_N ht)
    (h.tauOf_le_normalizer_A_sup ht)) (h.tauOf_le_normalizer_pCoreOf ht)

theorem isSylowIn_tauOf_K (h : KData196 p H T X A) :
    IsSylowIn 2 (E1.tauOf H T A) (K196 H T X A) := by
  have hO : E1.tauOf H T A ⊓ KN196 H X A = pCoreOf 2 H :=
    le_antisymm (fun x hx => h.KN_inf_T_le ⟨hx.2, E1.tauOf_le H T A hx.1⟩)
      (le_inf h.pCoreOf_le_tauOf h.pCoreOf_le_KN)
  have hS : IsSylowIn 2 (E1.tauOf H T A ⊓ KN196 H X A) (KN196 H X A) := by
    rw [hO]
    exact isSylowIn_two_of_pow_mem h.prime h.odd h.isPGroup_pCoreOf h.pCoreOf_le_KN
      h.KN_le_normalizer_pCoreOf fun x hx => h.pow_mem_of_mem_KN hx
  exact E1.isSylowIn_two_of_sup_inf h.tauOf_le_normalizer_KN h.isPGroup_tauOf hS

theorem isSylowIn_inf_K (h : KData196 p H T X A) : IsSylowIn 2 (T ⊓ K196 H T X A) (K196 H T X A) :=
  E1.isSylowIn_two_of_le h.isSylowIn_tauOf_K
    (le_inf (E1.tauOf_le H T A) le_sup_right) inf_le_right
    (h.isSylow.isPGroup.to_le inf_le_left)

theorem K_le_H (h : KData196 p H T X A) : K196 H T X A ≤ H := sup_le h.KN_le_H h.tauOf_le_H

theorem A_le_K (h : KData196 p H T X A) : A ≤ K196 H T X A := h.A_le_tauOf.trans le_sup_right

theorem KN_le_comm_sup (h : KData196 p H T X A) :
    KN196 H X A ≤ ⁅KN196 H X A, A⁆ ⊔ pCoreOf 2 H := by
  have h1 := comm_le_comm_comm_sup_of_pow_mem h.prime h.odd (N := X ⊔ pCoreOf 2 H) (A := A)
    (O := pCoreOf 2 H) le_sup_right h.N_le_normalizer_pCoreOf h.A_le_normalizer_pCoreOf
    h.A_le_normalizer_N h.isPGroup_A fun x hx => h.pow_mem_of_mem_N hx
  exact sup_le (h1.trans (sup_le_sup_right (Subgroup.commutator_mono le_sup_left le_rfl) _))
    le_sup_right

theorem eOneAmb_K (h : KData196 p H T X A) : E1.EOneAmb (K196 H T X A) A :=
  eOneAmb_sup_mod h.prime h.odd h.isPGroup_pCoreOf h.pCoreOf_le_KN h.KN_le_normalizer_pCoreOf
    h.tauOf_le_normalizer_pCoreOf (fun x hx => h.pow_mem_of_mem_KN hx) h.isPGroup_tauOf
    h.tauOf_le_normalizer_KN h.not_KN_le_pCoreOf h.A_le_tauOf h.KN_le_comm_sup h.relIndex

theorem isE_K (h : KData196 p H T X A) : E1.IsE 1 H T A (K196 H T X A) := by
  have hE : E1.EOne ↥(K196 H T X A) (A.subgroupOf (K196 H T X A)) :=
    (E1.eOne_iff_amb h.A_le_K).2 h.eOneAmb_K
  refine ⟨h.K_le_H, le_inf (E1.tauOf_le H T A) le_sup_right, h.isSylowIn_inf_K,
    Or.inl ⟨hE, ?_⟩⟩
  obtain ⟨-, -, -, -, -, -, hcard⟩ := hE
  rw [hcard]
  norm_num

theorem K_le_normalizer_KN_sup (h : KData196 p H T X A) :
    K196 H T X A ≤ normalizer ((KN196 H X A ⊔ A : Subgroup G) : Set G) := by
  show KN196 H X A ⊔ E1.tauOf H T A ≤ _
  refine sup_le (le_sup_left.trans Subgroup.le_normalizer) fun t ht => ?_
  have hKNA : KN196 H X A ⊔ A = KN196 H X A ⊔ (A ⊔ pCoreOf 2 H) :=
    le_antisymm (sup_le le_sup_left (le_sup_left.trans le_sup_right))
      (sup_le le_sup_left (sup_le le_sup_right (h.pCoreOf_le_KN.trans le_sup_left)))
  rw [hKNA]
  exact E1.mem_normalizer_sup (h.tauOf_le_normalizer_KN ht) (h.tauOf_le_normalizer_A_sup ht)

theorem iSup_conj_sup_pCoreOf_eq (h : KData196 p H T X A) :
    (⨆ k ∈ K196 H T X A, conjSubgroup A k) ⊔ pCoreOf 2 H = KN196 H X A ⊔ A := by
  have hKn := h.K_le_normalizer_KN_sup
  have hle : ⨆ k ∈ K196 H T X A, conjSubgroup A k ≤ KN196 H X A ⊔ A := by
    refine iSup₂_le fun k hk x hx => ?_
    have hk' := Subgroup.mem_normalizer_iff.1 (hKn (Subgroup.inv_mem _ hk)) (k * x * k⁻¹)
    rw [mem_conjSubgroup_iff] at hx
    have := hk'.1 (Subgroup.mem_sup_right hx)
    simpa [mul_assoc] using this
  refine le_antisymm (sup_le hle (h.pCoreOf_le_KN.trans le_sup_left)) (sup_le ?_ ?_)
  · refine h.KN_le_comm_sup.trans (sup_le_sup_right ?_ _)
    refine Subgroup.commutator_le.2 fun n hn a ha => ?_
    have hnK : n⁻¹ ∈ K196 H T X A := Subgroup.inv_mem _ (le_sup_left (a := KN196 H X A) hn)
    have h1 : n * a * n⁻¹ ∈ conjSubgroup A n⁻¹ := by
      rw [mem_conjSubgroup_iff]
      have e : n⁻¹ * (n * a * n⁻¹) * (n⁻¹)⁻¹ = a := by group
      rw [e]
      exact ha
    have h2 : a⁻¹ ∈ conjSubgroup A 1 := by
      rw [conjSubgroup_one]
      exact A.inv_mem ha
    have e : ⁅n, a⁆ = (n * a * n⁻¹) * a⁻¹ := commutatorElement_def n a
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_iSup_of_mem n⁻¹ (Subgroup.mem_iSup_of_mem hnK h1))
      (Subgroup.mem_iSup_of_mem 1 (Subgroup.mem_iSup_of_mem (Subgroup.one_mem _) h2))
  · exact le_sup_of_le_left (le_iSup₂_of_le 1 (Subgroup.one_mem _) (by rw [conjSubgroup_one]))

theorem A_le_normalizer_KN (h : KData196 p H T X A) :
    A ≤ normalizer ((KN196 H X A : Subgroup G) : Set G) := by
  intro a ha
  rw [h.KN_eq_comm_sup]
  exact E1.mem_normalizer_sup (E1.mem_normalizer_commutator (h.A_le_normalizer_N ha)
    (Subgroup.le_normalizer (Subgroup.mem_sup_left ha))) (h.A_le_normalizer_pCoreOf ha)

theorem X_le_normalizer_KN_sup (h : KData196 p H T X A) :
    X ≤ normalizer ((KN196 H X A ⊔ A : Subgroup G) : Set G) := by
  intro x hx
  have hxN : x ∈ X ⊔ pCoreOf 2 H := Subgroup.mem_sup_left hx
  have hxKN : x ∈ normalizer ((KN196 H X A : Subgroup G) : Set G) :=
    E1.mem_normalizer_sup (E1.le_normalizer_commutator_left hxN) (h.N_le_normalizer_pCoreOf hxN)
  apply E1.mem_normalizer_of_conj_mem
  intro y hy
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left (KN196 H X A) A
    h.A_le_normalizer_KN] at hy
  obtain ⟨k, hk, a, ha, rfl⟩ := hy
  have h1 : x * k * x⁻¹ ∈ KN196 H X A := (Subgroup.mem_normalizer_iff.1 hxKN k).1 hk
  have h2 : ⁅x, a⁆ ∈ KN196 H X A :=
    Subgroup.mem_sup_left (Subgroup.commutator_mem_commutator hxN ha)
  have e : x * (k * a) * x⁻¹ = (x * k * x⁻¹) * ⁅x, a⁆ * a := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
    (Subgroup.mem_sup_left h2)) (Subgroup.mem_sup_right ha)

theorem exists_isE_normalizer_gen (h : KData196 p H T X A) :
    ∃ K : Subgroup G, E1.IsE 1 H T A K ∧
      X ≤ normalizer (((⨆ k ∈ K, conjSubgroup A k) ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
  ⟨K196 H T X A, h.isE_K, by rw [h.iSup_conj_sup_pCoreOf_eq]; exact h.X_le_normalizer_KN_sup⟩

end KData196

namespace MinCex193

variable {D : Data G} {V₀ V : Subgroup G} {p : ℕ} {X : Subgroup G}

theorem kData196 (c : MinCex193 D V₀ V p X) {A : Subgroup G} (hAT : A ≤ D.T)
    (hAab : IsElemAbelian 2 A) (hA2 : (pCoreOf 2 (X ⊔ D.T)).relIndex A = 2)
    (hXA : ¬ ⁅X, A⁆ ≤ pCoreOf 2 (X ⊔ D.T)) : KData196 p (X ⊔ D.T) D.T X A :=
  ⟨c.hyp.prime, c.hyp.odd, c.hyp.isSylowIn_T, le_sup_left, c.hyp.isPGroup,
    c.le_normalizer_sup_pCoreOf, hAT, hAab, hA2, hXA⟩

theorem exists_isE_normalizer (c : MinCex193 D V₀ V p X) {A : Subgroup G} (hAT : A ≤ D.T)
    (hAab : IsElemAbelian 2 A) (hA2 : (pCoreOf 2 (X ⊔ D.T)).relIndex A = 2)
    (hXA : ¬ ⁅X, A⁆ ≤ pCoreOf 2 (X ⊔ D.T)) :
    ∃ K : Subgroup G, E1.IsE 1 (X ⊔ D.T) D.T A K ∧ X ≤ normalizer (K0193 D X A K : Set G) :=
  (c.kData196 hAT hAab hA2 hXA).exists_isE_normalizer_gen

theorem exists_conf196_le_J (c : MinCex193 D V₀ V p X) {g : G} (hg : conjSubgroup V g ≤ D.T)
    (hA2 : (pCoreOf 2 (X ⊔ D.T)).relIndex (conjSubgroup V g) = 2)
    (hXA : ¬ ⁅X, conjSubgroup V g⁆ ≤ pCoreOf 2 (X ⊔ D.T)) :
    ∃ K : Subgroup G, Conf196 D V X g K ∧ X ≤ J193 D X (conjSubgroup V g) K := by
  obtain ⟨K, hK, hX⟩ := c.exists_isE_normalizer hg
    (E3.isElemAbelian_conjSubgroup c.setting.isElemAbelian g) hA2 hXA
  exact ⟨K, ⟨hg, hK⟩, le_inf le_sup_left hX⟩

end MinCex193

end CFSG.LocalAnalysis.WeakClosure81

end
