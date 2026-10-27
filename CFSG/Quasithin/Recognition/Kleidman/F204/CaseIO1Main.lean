module

public import CFSG.Quasithin.Recognition.Kleidman.F204.CaseIO1Step2
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.CharTwo

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.QuasithinUnique.A5.Delta5

open scoped commutatorElement

set_option linter.unusedSectionVars false

section Count

theorem covering_of_card {U : Type*} [Fintype U] [DecidableEq U] (A : Fin 5 → Finset U)
    (F : Finset U) (hF : F.card = 4) (hA : ∀ i, (A i).card = 16) (hsub : ∀ i, F ⊆ A i)
    (hinter : ∀ i j, i ≠ j → A i ∩ A j = F) (hU : Fintype.card U = 64) :
    ∀ y : U, ∃ i, y ∈ A i := by
  by_contra hcon
  push Not at hcon
  obtain ⟨y, hy⟩ := hcon
  set B : Fin 5 → Finset U := fun i => A i \ F with hB
  have hBc : ∀ i, (B i).card = 12 := fun i => by
    rw [hB]; simp only; rw [Finset.card_sdiff_of_subset (hsub i), hA i, hF]
  have hBd : ∀ i ∈ (Finset.univ : Finset (Fin 5)), ∀ j ∈ (Finset.univ : Finset (Fin 5)), i ≠ j →
      Disjoint (B i) (B j) := by
    intro i _ j _ hij
    rw [Finset.disjoint_left]
    intro x hxi hxj
    have h1 : x ∈ A i ∩ A j := Finset.mem_inter.mpr ⟨(Finset.mem_sdiff.mp hxi).1,
      (Finset.mem_sdiff.mp hxj).1⟩
    rw [hinter i j hij] at h1
    exact (Finset.mem_sdiff.mp hxi).2 h1
  have hS : ((Finset.univ : Finset (Fin 5)).biUnion B).card = 60 := by
    rw [Finset.card_biUnion hBd]
    simp [hBc]
  have hFS : Disjoint F ((Finset.univ : Finset (Fin 5)).biUnion B) := by
    rw [Finset.disjoint_left]
    intro x hxF hxS
    obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp hxS
    exact (Finset.mem_sdiff.mp hi).2 hxF
  have hyFS : y ∉ F ∪ (Finset.univ : Finset (Fin 5)).biUnion B := by
    intro hyy
    rcases Finset.mem_union.mp hyy with h1 | h1
    · exact hy 0 (hsub 0 h1)
    · obtain ⟨i, _, hi⟩ := Finset.mem_biUnion.mp h1
      exact hy i (Finset.mem_sdiff.mp hi).1
  have hcard : (insert y (F ∪ (Finset.univ : Finset (Fin 5)).biUnion B)).card = 65 := by
    rw [Finset.card_insert_of_notMem hyFS, Finset.card_union_of_disjoint hFS, hF, hS]
  have := Finset.card_le_univ (insert y (F ∪ (Finset.univ : Finset (Fin 5)).biUnion B))
  rw [hcard, hU] at this
  omega

theorem card_filter_subgroup {G : Type*} [Group G] [Finite G] {K H : Subgroup G} (hHK : H ≤ K)
    [Fintype ↥K] [DecidablePred (fun y : ↥K => (y : G) ∈ H)] :
    (Finset.univ.filter (fun y : ↥K => (y : G) ∈ H)).card = Nat.card H := by
  rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
  have e : {y : ↥K // (y : G) ∈ H} ≃ ↥H :=
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨⟨y.1, hHK y.2⟩, y.2⟩
      left_inv := fun y => rfl
      right_inv := fun y => rfl }
  exact Nat.card_congr e

theorem comm_of_sq_one {G : Type*} [Group G] {Q : Subgroup G} (hq : ∀ a ∈ Q, a * a = 1) :
    ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a := by
  intro a ha b hb
  have h1 := hq (a * b) (Q.mul_mem ha hb)
  have ha' : a⁻¹ = a := inv_eq_of_mul_eq_one_right (hq a ha)
  have hb' : b⁻¹ = b := inv_eq_of_mul_eq_one_right (hq b hb)
  have : a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right h1).symm
  rw [this, mul_inv_rev, ha', hb']

end Count

section Main

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}
variable (F : Frame L1 L2 S D X)
include F

theorem X_not_mem_B {x : G} (hx : x ∈ X) (hx1 : x ≠ 1) : x ∉ bigB L1 L2 S := by
  intro hxB
  have hcard : Nat.card (↥(P1 L1 L2 S) ⧸ (bigB L1 L2 S).subgroupOf (P1 L1 L2 S)) = 5 := by
    have h := F.pair.relIndex_bigB_left
    rw [Subgroup.relIndex, Subgroup.index_eq_card] at h
    exact h
  let ψ : ↥X → (↥(P1 L1 L2 S) ⧸ (bigB L1 L2 S).subgroupOf (P1 L1 L2 S)) :=
    fun y => QuotientGroup.mk ⟨y, F.mem_P1_of_mem_X y.2⟩
  have hsurj : Function.Surjective ψ := by
    intro q
    obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨y, hy, b, hb, hpyb⟩ := F.exists_mul p p.2
    refine ⟨⟨y, hy⟩, ?_⟩
    show (QuotientGroup.mk (⟨y, F.mem_P1_of_mem_X hy⟩ : ↥(P1 L1 L2 S)) :
        ↥(P1 L1 L2 S) ⧸ (bigB L1 L2 S).subgroupOf (P1 L1 L2 S)) = QuotientGroup.mk p
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have : (y : G)⁻¹ * (p : G) = b := by rw [hpyb]; group
    simpa [this] using hb
  have hbij : Function.Bijective ψ := hsurj.bijective_of_nat_card_le (by rw [F.X_card, hcard])
  have h1 : ψ ⟨x, hx⟩ = ψ ⟨1, X.one_mem⟩ := by
    show (QuotientGroup.mk (⟨x, F.mem_P1_of_mem_X hx⟩ : ↥(P1 L1 L2 S)) :
        ↥(P1 L1 L2 S) ⧸ (bigB L1 L2 S).subgroupOf (P1 L1 L2 S)) =
      QuotientGroup.mk (⟨1, F.mem_P1_of_mem_X X.one_mem⟩ : ↥(P1 L1 L2 S))
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simpa using (bigB L1 L2 S).inv_mem hxB
  exact hx1 (congrArg Subtype.val (hbij.1 h1))

theorem Z2q_not_normalized (h : O1Hyp L1 L2 S) {x : G} (hx : x ∈ X) (hx1 : x ≠ 1)
    (hxn : x ∈ Subgroup.normalizer (Z2q L1 L2 S : Set G)) : False := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hx5 : x ^ 5 = 1 := by
    have := pow_card_eq_one' (G := ↥X) (x := ⟨x, hx⟩)
    rw [F.X_card] at this
    simpa using congrArg Subtype.val this
  have hord : orderOf x = 5 := orderOf_eq_prime hx5 hx1
  have hzp : Subgroup.zpowers x ≤ X := (Subgroup.zpowers_le).mpr hx
  have hXeq : Subgroup.zpowers x = X := by
    apply Subgroup.eq_of_le_of_card_ge hzp
    rw [F.X_card, Nat.card_zpowers, hord]
  have hXN : X ≤ Subgroup.normalizer (Z2q L1 L2 S : Set G) := by
    rw [← hXeq]; exact (Subgroup.zpowers_le).mpr hxn
  have hP2N : P2 L1 L2 S ≤ Subgroup.normalizer (Z2q L1 L2 S : Set G) :=
    le_normalizer_conjClosure _ _
  have hBN : bigB L1 L2 S ≤ Subgroup.normalizer (Z2q L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans hP2N
  have hP1N : P1 L1 L2 S ≤ Subgroup.normalizer (Z2q L1 L2 S : Set G) := by
    intro p hp
    obtain ⟨y, hy, b, hb, rfl⟩ := F.exists_mul p hp
    exact (Subgroup.normalizer _).mul_mem (hXN hy) (hBN hb)
  have hle : P1 L1 L2 S ⊔ P2 L1 L2 S ≤ Subgroup.normalizer (Z2q L1 L2 S : Set G) :=
    sup_le hP1N hP2N
  have hZle : Z2q L1 L2 S ≤ P1 L1 L2 S ⊔ P2 L1 L2 S :=
    (Z2q_le_Q2 F).trans ((pCoreOf_le 2 _).trans le_sup_right)
  have hpg : IsPGroup 2 (Z2q L1 L2 S) :=
    (pCoreOf_isPGroup 2 (P2 L1 L2 S)).to_le (Z2q_le_Q2 F)
  have hcore := le_pCoreOf_of_le_normalizer hZle hle hpg
  rw [(Amal.of_frame F).amalgam.o2_trivial] at hcore
  have hbot : Z2q L1 L2 S = ⊥ := le_bot_iff.mp hcore
  have := h.card16
  rw [hbot, Subgroup.card_bot] at this
  omega

theorem conjSub_Z_eq (h : O1Hyp L1 L2 S) {g : G} (hg : g ∈ P1 L1 L2 S) :
    conjSub g (quasithinOmegaOneCenter S) = quasithinOmegaOneCenter S := by
  ext y
  rw [mem_conjSub]
  constructor
  · intro hy
    have := h.norm1 g hg _ hy
    simpa [mul_assoc] using this
  · intro hy
    have := h.norm1 g⁻¹ ((P1 L1 L2 S).inv_mem hg) y hy
    rwa [inv_inv] at this


theorem o1_false (h : O1Hyp L1 L2 S) : False := by
  classical
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  obtain ⟨g0, hg0, hg0B, hnot0⟩ := h.exists_crit
  have hQ12 : Q1 L1 L2 S ⊓ Q2 L1 L2 S = Z2q L1 L2 S :=
    le_antisymm (Q1_inf_Q2_le F h hg0 hg0B hnot0) (le_inf (Z2q_le_Q1 F) (Z2q_le_Q2 F))
  have hcardQ1 : Nat.card (Q1 L1 L2 S) = 64 := by
    have := card_Q1 F
    rw [hQ12, h.card16] at this
    omega
  obtain ⟨x0, hx0, hx05, hx01, hgen⟩ := F.exists_gen
  have hord0 : orderOf x0 = 5 := orderOf_eq_prime hx05 hx01
  have hxX : ∀ j : ℕ, x0 ^ j ∈ X := fun j => X.pow_mem hx0 j
  have hxP : ∀ j : ℕ, x0 ^ j ∈ P1 L1 L2 S := fun j => F.mem_P1_of_mem_X (hxX j)
  have hx1 : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → x0 ^ j ≠ 1 := by
    intro j hj1 hj4 hxj
    have := orderOf_dvd_of_pow_eq_one hxj
    rw [hord0] at this
    have := Nat.le_of_dvd (by omega) this
    omega
  have hxB : ∀ j : ℕ, 1 ≤ j → j ≤ 4 → x0 ^ j ∉ bigB L1 L2 S := fun j hj1 hj4 =>
    X_not_mem_B F (hxX j) (hx1 j hj1 hj4)
  have hnotk1 : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → ¬ conjSub (x0 ^ k) (Z2q L1 L2 S) ≤ Q2 L1 L2 S := by
    intro k hk1 hk4 hle
    have h1 : conjSub (x0 ^ k) (Z2q L1 L2 S) ≤ Z2q L1 L2 S := by
      have : conjSub (x0 ^ k) (Z2q L1 L2 S) ≤ Q1 L1 L2 S ⊓ Q2 L1 L2 S :=
        le_inf (conjZ2q_le_Q1 F (hxP k)) hle
      rwa [hQ12] at this
    have h2 : conjSub (x0 ^ k) (Z2q L1 L2 S) = Z2q L1 L2 S := by
      apply Subgroup.eq_of_le_of_card_ge h1
      rw [CosetGeom.card_conjSub]
    exact Z2q_not_normalized F h (hxX k) (hx1 k hk1 hk4) (mem_normalizer_of_conjSub_eq h2)
  have hnotk : ∀ k : ℕ, 1 ≤ k → k ≤ 4 → NotLe L1 L2 S (x0 ^ k) := by
    intro k hk1 hk4
    have hQ1g : conjSub (x0 ^ k) (Q1 L1 L2 S) = Q1 L1 L2 S := conjSub_Q1 F (hxP k)
    refine ⟨fun hle => ?_, fun hle => ?_⟩
    · exact hnotk1 k hk1 hk4 hle
    · have h1 : Z2q L1 L2 S ≤ conjSub (x0 ^ k) (Z2q L1 L2 S) := by
        have : Z2q L1 L2 S ≤ conjSub (x0 ^ k) (Q1 L1 L2 S ⊓ Q2 L1 L2 S) := by
          rw [conjSub_inf, hQ1g]; exact le_inf (Z2q_le_Q1 F) hle
        rwa [hQ12] at this
      have h2 : conjSub (x0 ^ k) (Z2q L1 L2 S) = Z2q L1 L2 S := by
        symm
        apply Subgroup.eq_of_le_of_card_ge h1
        rw [CosetGeom.card_conjSub]
      exact Z2q_not_normalized F h (hxX k) (hx1 k hk1 hk4) (mem_normalizer_of_conjSub_eq h2)
  have hpd : ∀ k : ℕ, 1 ≤ k → k ≤ 4 →
      Z2q L1 L2 S ⊓ conjSub (x0 ^ k) (Z2q L1 L2 S) = quasithinOmegaOneCenter S := by
    intro k hk1 hk4
    obtain ⟨-, -, h3⟩ := pair_data F h (hxP k) (hxB k hk1 hk4) (hnotk k hk1 hk4)
    apply le_antisymm
    · rw [← h3, inf_comm]
      exact inf_le_inf_left _ (Z2q_le_Q2 F)
    · exact le_inf Z_le_Z2q (Z_le_conjZ2q F h (hxP k))
  have hpair : ∀ i j : ℕ, i < j → j ≤ 4 →
      conjSub (x0 ^ i) (Z2q L1 L2 S) ⊓ conjSub (x0 ^ j) (Z2q L1 L2 S) =
        quasithinOmegaOneCenter S := by
    intro i j hij hj4
    have e : conjSub (x0 ^ j) (Z2q L1 L2 S) =
        conjSub (x0 ^ i) (conjSub (x0 ^ (j - i)) (Z2q L1 L2 S)) := by
      rw [← conjSub_mul, ← pow_add, Nat.add_sub_cancel' hij.le]
    rw [e, ← conjSub_inf, hpd (j - i) (by omega) (by omega), conjSub_Z_eq F h (hxP i)]
  have : Fintype ↥(Q1 L1 L2 S) := Fintype.ofFinite _
  let A : Fin 5 → Finset ↥(Q1 L1 L2 S) := fun i =>
    Finset.univ.filter (fun y : ↥(Q1 L1 L2 S) => (y : G) ∈ conjSub (x0 ^ (i : ℕ)) (Z2q L1 L2 S))
  let Fz : Finset ↥(Q1 L1 L2 S) :=
    Finset.univ.filter (fun y : ↥(Q1 L1 L2 S) => (y : G) ∈ quasithinOmegaOneCenter S)
  have hZQ1 : quasithinOmegaOneCenter S ≤ Q1 L1 L2 S :=
    Z_le_Z2q.trans (Z2q_le_Q1 F)
  have hFz : Fz.card = 4 := by
    show (Finset.univ.filter _).card = 4
    rw [card_filter_subgroup hZQ1]
    obtain ⟨hZ4, -, -⟩ := pair_data F h hg0 hg0B hnot0
    exact hZ4
  have hA : ∀ i, (A i).card = 16 := by
    intro i
    show (Finset.univ.filter _).card = 16
    rw [card_filter_subgroup (conjZ2q_le_Q1 F (hxP i)), CosetGeom.card_conjSub]
    exact h.card16
  have hsub : ∀ i, Fz ⊆ A i := by
    intro i y hy
    simp only [Fz, A, Finset.mem_filter, Finset.mem_univ, true_and] at hy ⊢
    exact Z_le_conjZ2q F h (hxP i) hy
  have hinter : ∀ i j, i ≠ j → A i ∩ A j = Fz := by
    have key : ∀ i j : Fin 5, i < j → A i ∩ A j = Fz := by
      intro i j hij
      ext y
      simp only [Fz, A, Finset.mem_inter, Finset.mem_filter, Finset.mem_univ, true_and]
      have := hpair i j (by exact_mod_cast hij) (by omega)
      constructor
      · rintro ⟨h1, h2⟩
        rw [← this]; exact ⟨h1, h2⟩
      · intro hy
        rw [← this] at hy
        exact hy
    intro i j hij
    rcases lt_or_gt_of_ne hij with h1 | h1
    · exact key i j h1
    · rw [Finset.inter_comm]; exact key j i h1
  have hU : Fintype.card ↥(Q1 L1 L2 S) = 64 := by
    rw [← Nat.card_eq_fintype_card]; exact hcardQ1
  have hcover := covering_of_card A Fz hFz hA hsub hinter hU
  have hsq : ∀ y ∈ Q1 L1 L2 S, y * y = 1 := by
    intro y hy
    obtain ⟨i, hi⟩ := hcover ⟨y, hy⟩
    simp only [A, Finset.mem_filter, Finset.mem_univ, true_and] at hi
    rw [mem_conjSub] at hi
    have := Z2q_sq F _ hi
    calc y * y = (x0 ^ (i : ℕ)) * ((x0 ^ (i : ℕ))⁻¹ * y * x0 ^ (i : ℕ)) *
        ((x0 ^ (i : ℕ))⁻¹ * y * x0 ^ (i : ℕ)) * (x0 ^ (i : ℕ))⁻¹ := by group
      _ = 1 := by rw [mul_assoc _ _ ((x0 ^ (i : ℕ))⁻¹ * y * x0 ^ (i : ℕ)), this]; group
  have hcomm := comm_of_sq_one hsq
  have hn1 := (hnotk 1 le_rfl (by omega)).left
  obtain ⟨z', hz', hz'Q⟩ := Set.not_subset.mp hn1
  have hz'Q1 : z' ∈ Q1 L1 L2 S := conjZ2q_le_Q1 F (hxP 1) hz'
  have hz'S : z' ∈ S := F.Q1_le_S hz'Q1
  apply hz'Q
  apply h.faith z' hz'S
  intro z hz
  exact hcomm z' hz'Q1 z (Z2q_le_Q1 F hz)

end Main

end CFSG.Quasithin.Kleidman.F204
