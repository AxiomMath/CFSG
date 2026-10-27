module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Sixteen67NeG
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenDefsB
public import CFSG.Quasithin.H13.VolIF956
public import CFSG.Quasithin.EmptyFaithful.S1422Extra
public import CFSG.Quasithin.H13.L32A76S2e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Cfg1667Ne

variable {M V₀ V W₁ W₂ : Subgroup G} {g : G}

theorem cube_mem_M (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹)
    {v i : G} (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) :
    (v * i) ^ 3 ∈ M := by
  refine mem_M_of_commutator_mem_E h hs (fun u hu => ?_)
  exact cube_commutator_mem_E h hs hs' hv hvU hi hiB (Subgroup.mem_sup_left hu)

theorem conj_le_M_of_cube (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹)
    {v i : G} (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) :
    conjSubgroup V (g * ((v * i) ^ 2)⁻¹) ≤ M := by
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let K : Subgroup G := U ⊔ B
  let X : Subgroup G := V ⊔ conjSubgroup V g
  let x : G := (v * i) ^ 2
  change conjSubgroup V (g * x⁻¹) ≤ M
  have hv2 : v * v = 1 := by simpa [pow_two] using h.elemAbelian.2 v hv
  have hi2 : i * i = 1 := by simpa [pow_two] using (h.conj g).elemAbelian.2 i hi
  have hx2 : x = v * i * v * i := by rw [show x = (v * i) ^ 2 from rfl, pow_two]; group
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hi' : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hxinv : x⁻¹ = i * v * i * v := by
    rw [hx2]
    simp only [mul_inv_rev, inv_inv, hv', hi']
    group
  have hxiconj : x * i * x⁻¹ = (v * i) ^ 3 * v := by
    rw [hxinv, hx2]
    rw [show (v * i * v * i) * i = (v * i * v) * (i * i) by group, hi2, mul_one]
    rw [pow_three]
    group
  have hxX : x ∈ X := by
    have hvX : v ∈ X := Subgroup.mem_sup_left hv
    have hiX : i ∈ X := Subgroup.mem_sup_right hi
    have hx_eq : x = (v * i) * (v * i) := by rw [show x = (v * i) ^ 2 from rfl, pow_two]
    rw [hx_eq]
    exact X.mul_mem (X.mul_mem hvX hiX) (X.mul_mem hvX hiX)
  have hxN : x ∈ normalizer (K : Set G) := by
    have hXN : X ≤ normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (K_le_X h)).mp (K_normal h hs)
    exact hXN hxX
  have hconjB : ∀ b ∈ B, x * b * x⁻¹ ∈ K := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp hxN b).1 (Subgroup.mem_sup_right hb)
  have hcM : (v * i) ^ 3 ∈ M := cube_mem_M h hs hs' hv hvU hi hiB
  intro a ha
  rw [← conjSubgroup_conjSubgroup V g x⁻¹] at ha
  rw [mem_conjSubgroup_iff] at ha
  rw [inv_inv] at ha
  set a₀ : G := x⁻¹ * a * x with ha₀def
  have hxax : x * a₀ * x⁻¹ = a := by rw [ha₀def]; group
  have ha₀Vg : a₀ ∈ conjSubgroup V g := ha
  by_cases ha₀B : a₀ ∈ B
  · have hxb : x * a₀ * x⁻¹ ∈ K := hconjB a₀ ha₀B
    rw [hxax] at hxb
    exact (K_le_M h) hxb
  · have hicos : ∀ y ∈ conjSubgroup V g, y * i ∈ B ∨ y ∈ B := by
      intro y hy
      by_cases hyB : y ∈ B
      · exact Or.inr hyB
      · left
        have hiff := Subgroup.mul_mem_iff_of_index_two
          (H := B.subgroupOf (conjSubgroup V g)) (a := (⟨y, hy⟩ : ↥(conjSubgroup V g)))
          (b := (⟨i, hi⟩ : ↥(conjSubgroup V g)))
          (show (B.subgroupOf (conjSubgroup V g)).index = 2 from relIndex_B h hs.1)
        have hnode : (⟨y, hy⟩ : ↥(conjSubgroup V g)) ∈ B.subgroupOf (conjSubgroup V g) ↔
            (⟨i, hi⟩ : ↥(conjSubgroup V g)) ∈ B.subgroupOf (conjSubgroup V g) := by
          rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
          exact (iff_false_intro hyB).trans (iff_false_intro hiB).symm
        have hprod : (⟨y, hy⟩ * ⟨i, hi⟩ : ↥(conjSubgroup V g)) ∈
            B.subgroupOf (conjSubgroup V g) := hiff.mpr hnode
        simpa using (Subgroup.mem_subgroupOf.mp hprod)
    rcases hicos a₀ ha₀Vg with ha₀iB | ha₀B'
    · obtain ⟨b, hbB, hb_eq⟩ : ∃ b ∈ B, a₀ = b * i :=
        ⟨a₀ * i, ha₀iB, by rw [mul_assoc, hi2, mul_one]⟩
      have hxb : x * b * x⁻¹ ∈ K := hconjB b hbB
      have heq2 : x * (b * i) * x⁻¹ = (x * b * x⁻¹) * (x * i * x⁻¹) := by group
      have haeq : a = (x * b * x⁻¹) * (x * i * x⁻¹) := by
        rw [← hxax, hb_eq, heq2]
      rw [haeq, hxiconj]
      exact M.mul_mem ((K_le_M h) hxb) (M.mul_mem hcM (h.le_M hv))
    · exact absurd ha₀B' ha₀B

theorem mul_inv_mem_M_of_cube (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹)
    {v i : G} (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) :
    g * ((v * i) ^ 2)⁻¹ ∈ M := by
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let K : Subgroup G := U ⊔ B
  let X : Subgroup G := V ⊔ conjSubgroup V g
  let x : G := (v * i) ^ 2
  change g * x⁻¹ ∈ M
  have hv2 : v * v = 1 := by simpa [pow_two] using h.elemAbelian.2 v hv
  have hi2 : i * i = 1 := by simpa [pow_two] using (h.conj g).elemAbelian.2 i hi
  have hx2 : x = v * i * v * i := by rw [show x = (v * i) ^ 2 from rfl, pow_two]; group
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hi' : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hxinv : x⁻¹ = i * v * i * v := by
    rw [hx2]
    simp only [mul_inv_rev, inv_inv, hv', hi']
    group
  have hxX : x ∈ X := by
    have hvX : v ∈ X := Subgroup.mem_sup_left hv
    have hiX : i ∈ X := Subgroup.mem_sup_right hi
    have hx_eq : x = (v * i) * (v * i) := by rw [show x = (v * i) ^ 2 from rfl, pow_two]
    rw [hx_eq]
    exact X.mul_mem (X.mul_mem hvX hiX) (X.mul_mem hvX hiX)
  have hxN : x ∈ normalizer (K : Set G) := by
    have hXN : X ≤ normalizer (K : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (K_le_X h)).mp (K_normal h hs)
    exact hXN hxX
  have hconjB : ∀ b ∈ B, x * b * x⁻¹ ∈ K := fun b hb =>
    (Subgroup.mem_normalizer_iff.mp hxN b).1 (Subgroup.mem_sup_right hb)
  have hVgxM : conjSubgroup V (g * x⁻¹) ≤ M := conj_le_M_of_cube h hs hs' hv hvU hi hiB
  have hxbU : ∀ b ∈ B, x * b * x⁻¹ ∈ U := by
    intro b hb
    have hxb_mem : x * b * x⁻¹ ∈ conjSubgroup V (g * x⁻¹) := by
      rw [← conjSubgroup_conjSubgroup V g x⁻¹]
      refine mem_conjSubgroup_iff.mpr ?_
      have e : x⁻¹ * (x * b * x⁻¹) * (x⁻¹)⁻¹ = b := by group
      rw [e]
      exact hb.1
    have hcomm : ⁅V, conjSubgroup V (g * x⁻¹)⁆ = ⊥ := h.comm_eq_bot (g * x⁻¹) hVgxM
    have hcentV : conjSubgroup V (g * x⁻¹) ≤ centralizer (V : Set G) :=
      Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm)
    have hcentV' : x * b * x⁻¹ ∈ centralizer (V : Set G) := hcentV hxb_mem
    exact K_inf_centralizer_V_le h hs ⟨hconjB b hb, hcentV'⟩
  have hxBU : conjSubgroup B x⁻¹ ≤ U := by
    intro a ha
    have hb : x⁻¹ * a * x ∈ B := by
      simpa using (mem_conjSubgroup_iff.mp ha : x⁻¹ * a * (x⁻¹)⁻¹ ∈ B)
    have h := hxbU (x⁻¹ * a * x) hb
    have e : x * (x⁻¹ * a * x) * x⁻¹ = a := by group
    rwa [e] at h
  have hxBU' : conjSubgroup B x⁻¹ ≤ V ⊓ conjSubgroup V (g * x⁻¹) := by
    refine le_inf ?_ ?_
    · exact hxBU.trans (fun y hy => hy.1)
    · rw [← conjSubgroup_conjSubgroup V g x⁻¹]
      exact E3.conjSubgroup_mono_left x⁻¹ (fun y hy => hy.1)
  have hcardge : 8 ≤ Nat.card (V ⊓ conjSubgroup V (g * x⁻¹) : Subgroup G) := by
    have hle := Nat.card_le_card_of_injective
      (fun y : ↥(conjSubgroup B x⁻¹) =>
        (⟨(y : G), hxBU' y.2⟩ : ↥(V ⊓ conjSubgroup V (g * x⁻¹))))
      (fun y z hyz => Subtype.ext (by
        have := congrArg Subtype.val hyz
        simpa using this))
    rw [E3.card_conjSubgroup B x⁻¹, card_B h hs.1] at hle
    have h8 : 8 ≤ 8 * Nat.card V₀ := by
      have := Nat.card_pos (α := V₀)
      omega
    exact h8.trans hle
  by_contra hgx
  have hle2 := h.card_inf_conj_le (y := g * x⁻¹) hgx
  omega

theorem cube_mem_V (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹)
    {v i : G} (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) :
    (v * i) ^ 3 ∈ V := by
  let x : G := (v * i) ^ 2
  have hv2 : v * v = 1 := by simpa [pow_two] using h.elemAbelian.2 v hv
  have hi2 : i * i = 1 := by simpa [pow_two] using (h.conj g).elemAbelian.2 i hi
  have hx2 : x = v * i * v * i := by rw [show x = (v * i) ^ 2 from rfl, pow_two]; group
  have hv' : v⁻¹ = v := inv_eq_of_mul_eq_one_right hv2
  have hi' : i⁻¹ = i := inv_eq_of_mul_eq_one_right hi2
  have hxinv : x⁻¹ = i * v * i * v := by
    rw [hx2]
    simp only [mul_inv_rev, inv_inv, hv', hi']
    group
  have hxiconj : x * i * x⁻¹ = (v * i) ^ 3 * v := by
    rw [hxinv, hx2]
    rw [show (v * i * v * i) * i = (v * i * v) * (i * i) by group, hi2, mul_one]
    rw [pow_three]
    group
  have hgxM : g * x⁻¹ ∈ M := mul_inv_mem_M_of_cube h hs hs' hv hvU hi hiB
  have hconjV : conjSubgroup V (g * x⁻¹) = V :=
    conjSubgroup_eq_iff_mem_normalizer.mpr (by rw [h.normalizer_eq]; exact hgxM)
  have hxiV : x * i * x⁻¹ ∈ V := by
    have hmem : x * i * x⁻¹ ∈ conjSubgroup V (g * x⁻¹) := by
      rw [← conjSubgroup_conjSubgroup V g x⁻¹]
      refine mem_conjSubgroup_iff.mpr ?_
      have e : x⁻¹ * (x * i * x⁻¹) * (x⁻¹)⁻¹ = i := by group
      rw [e]
      exact hi
    rwa [hconjV] at hmem
  have hxiV' : (v * i) ^ 3 * v ∈ V := by
    rw [← hxiconj]
    exact hxiV
  have h2 : ((v * i) ^ 3 * v) * v⁻¹ ∈ V := V.mul_mem hxiV' (V.inv_mem hv)
  simpa only [mul_assoc, mul_inv_cancel, mul_one] using h2

theorem cube_mem_K (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹)
    {v i : G} (hv : v ∈ V) (hvU : v ∉ V ⊓ conjSubgroup M g) (hi : i ∈ conjSubgroup V g)
    (hiB : i ∉ conjSubgroup V g ⊓ M) :
    (v * i) ^ 3 ∈ (V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M) := by
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let N : Subgroup G := U ⊓ B
  have hcV : (v * i) ^ 3 ∈ V := cube_mem_V h hs hs' hv hvU hi hiB
  by_cases hcU : (v * i) ^ 3 ∈ U
  · exact Subgroup.mem_sup_left hcU
  · exfalso
    have hBU : B ≤ conjSubgroup V₀ g ⊔ N := by
      intro b hb
      have h1 : (v * i) ^ 3 * b * ((v * i) ^ 3)⁻¹ * b⁻¹ ∈ V₀ ⊔ conjSubgroup V₀ g :=
        cube_commutator_mem_E h hs hs' hv hvU hi hiB (Subgroup.mem_sup_right hb)
      have h2 : ⁅(v * i) ^ 3, b⁆ ∈ (V₀ ⊔ conjSubgroup V₀ g) ⊔ N := by
        rw [commutatorElement_def]
        exact Subgroup.mem_sup_left h1
      exact stepF h hs hcV hcU hb h2
    have hcardB_le : Nat.card B ≤ Nat.card (conjSubgroup V₀ g ⊔ N : Subgroup G) :=
      Nat.card_le_card_of_injective
        (fun y : ↥B => (⟨(y : G), hBU y.2⟩ : ↥(conjSubgroup V₀ g ⊔ N : Subgroup G)))
        (fun y z hyz => Subtype.ext (by simpa using congrArg Subtype.val hyz))
    have hA_le : conjSubgroup V₀ g ≤ conjSubgroup V g :=
      E3.conjSubgroup_mono_left g (V₀_le h)
    have hN_le : N ≤ conjSubgroup V g := (inf_le_right : N ≤ B).trans inf_le_left
    have hcomm : ∀ x ∈ conjSubgroup V₀ g, ∀ y ∈ N, x * y = y * x := by
      intro x hx y hy
      exact Subtype.ext_iff.mp ((E3.isElemAbelian_conjSubgroup h.elemAbelian g).1.is_comm.comm
        ⟨x, hA_le hx⟩ ⟨y, hN_le hy⟩)
    have hcard_sup : Nat.card (conjSubgroup V₀ g ⊔ N : Subgroup G) ≤
        Nat.card (conjSubgroup V₀ g) * Nat.card N := by
      have hcard := (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
        (conjSubgroup V₀ g) N hcomm).1
      calc Nat.card (conjSubgroup V₀ g ⊔ N : Subgroup G)
          = Nat.card (conjSubgroup V₀ g ⊔ N : Subgroup G) * 1 := (mul_one _).symm
        _ ≤ Nat.card (conjSubgroup V₀ g ⊔ N : Subgroup G) *
              Nat.card ↥(conjSubgroup V₀ g ⊓ N) :=
              Nat.mul_le_mul_left _ (Nat.card_pos (α := ↥(conjSubgroup V₀ g ⊓ N)))
        _ = Nat.card (conjSubgroup V₀ g) * Nat.card N := hcard
    have hcardB : Nat.card B = 8 * Nat.card V₀ := card_B h hs.1
    have hcardA : Nat.card (conjSubgroup V₀ g) = Nat.card V₀ := E3.card_conjSubgroup V₀ g
    have hcardN : Nat.card N = 2 := by
      change Nat.card ((V ⊓ conjSubgroup M g) ⊓ (conjSubgroup V g ⊓ M) : Subgroup G) = 2
      exact card_U_inf_B h hs
    rw [hcardB] at hcardB_le
    rw [hcardA, hcardN] at hcard_sup
    have hpos : 0 < Nat.card V₀ := Nat.card_pos
    omega

theorem isSym_X_quot_K
    [(((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)).subgroupOf
      (V ⊔ conjSubgroup V g)).Normal]
    (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    IsSym (↥(V ⊔ conjSubgroup V g) ⧸
      ((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)).subgroupOf (V ⊔ conjSubgroup V g)) 3 := by
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let K : Subgroup G := U ⊔ B
  let X : Subgroup G := V ⊔ conjSubgroup V g
  haveI hN : (K.subgroupOf X).Normal := K_normal h hs
  obtain ⟨v, hv, hvU, hvcos⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
        (H := U) (K := V)).mp (relIndex_U h hs.1)
  obtain ⟨i, hi, hiB, hicos⟩ := (Subgroup.relIndex_eq_two_iff_exists_notMem_and
        (H := B) (K := conjSubgroup V g)).mp (relIndex_B h hs.1)
  have hv2 : v * v = 1 := by simpa [pow_two] using h.elemAbelian.2 v hv
  have hi2 : i * i = 1 := by simpa [pow_two] using (h.conj g).elemAbelian.2 i hi
  have hvK : v ∉ K := by
    intro hvK
    have hVKU : V ⊓ K = U := V_inf_K h hs
    have : v ∈ U := by
      rw [← hVKU]
      exact ⟨hv, hvK⟩
    exact hvU this
  have hAcos : ∀ w ∈ V, w ∈ K ∨ w * v ∈ K := by
    intro w hw
    rcases hvcos w hw with hwv | hwU
    · exact Or.inr (Subgroup.mem_sup_left hwv)
    · exact Or.inl (Subgroup.mem_sup_left hwU)
  have hBcos : ∀ y ∈ conjSubgroup V g, y ∈ K ∨ y * i ∈ K := by
    intro y hy
    rcases hicos y hy with hyi | hyB
    · exact Or.inr (Subgroup.mem_sup_right hyi)
    · exact Or.inl (Subgroup.mem_sup_right hyB)
  have hab3 : (v * i) ^ 3 ∈ K := cube_mem_K h hs hs' hv hvU hi hiB
  have hnot : ¬ ∀ y ∈ V ⊔ conjSubgroup V g, ∃ n : ℕ, y ^ 2 ^ n ∈ K := by
    intro hall
    obtain ⟨n, hn⟩ := hall (v * i)
      (X.mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hi))
    let π : ↥X →* (↥X ⧸ K.subgroupOf X) := QuotientGroup.mk' _
    have hπ1 : ∀ x : ↥X, π x = 1 ↔ (x : G) ∈ K := fun x => QuotientGroup.eq_one_iff x
    let a : ↥X ⧸ K.subgroupOf X :=
      π ⟨v * i, X.mul_mem (Subgroup.mem_sup_left hv) (Subgroup.mem_sup_right hi)⟩
    have haeq : a = π (⟨v * i, X.mul_mem (Subgroup.mem_sup_left hv)
        (Subgroup.mem_sup_right hi)⟩ : ↥X) := rfl
    have h3 : a ^ 3 = 1 := by
      dsimp only [a]
      rw [← map_pow]
      exact (hπ1 _).2 hab3
    have h2 : a ^ (2 ^ n) = 1 := by
      dsimp only [a]
      rw [← map_pow]
      exact (hπ1 _).2 hn
    have hdvd : orderOf a ∣ Nat.gcd 3 (2 ^ n) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    have hcop : Nat.gcd 3 (2 ^ n) = 1 :=
      Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)
    rw [hcop] at hdvd
    have ha1 : a = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)
    have hviK : v * i ∈ K := by
      rw [haeq] at ha1
      exact (hπ1 _).1 ha1
    have hKM : K ≤ M := K_le_M h
    have hviM : v * i ∈ M := hKM hviK
    have hiM : i ∈ M := by
      have hh : v * (v * i) ∈ M := M.mul_mem (h.le_M hv) hviM
      rwa [show v * (v * i) = i by rw [← mul_assoc, hv2, one_mul]] at hh
    exact hiB ⟨hi, hiM⟩
  exact CFSG.Quasithin.H13.VolI.nonempty_sup_quotient_perm_three (A := V)
    (B := conjSubgroup V g) (P := K) hv hi hv2 hi2 hvK hab3 hAcos hBcos hnot

theorem isExtraspecialPlus2_K_quot
    [((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal]
    (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    IsExtraspecialPlus2 ↥((((V ⊓ conjSubgroup M g) ⊔ (conjSubgroup V g ⊓ M)).subgroupOf
        (V ⊔ conjSubgroup V g)).map
      (QuotientGroup.mk' ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)))) 2 := by
  let X : Subgroup G := V ⊔ conjSubgroup V g
  let E : Subgroup G := V₀ ⊔ conjSubgroup V₀ g
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let K : Subgroup G := U ⊔ B
  let π : ↥X →* (↥X ⧸ E.subgroupOf X) := QuotientGroup.mk' _
  change IsExtraspecialPlus2 ↥((K.subgroupOf X).map π) 2
  refine ⟨isExtraspecial_of_isQ8Sq (isQ8Sq_K_quot h hs hs'), ?_, ?_⟩
  · rw [card_K_quot h hs hs']
    norm_num
  · refine ⟨((U.subgroupOf X).map π).subgroupOf ((K.subgroupOf X).map π), ?_⟩
    have hUK : U ≤ K := le_sup_left
    have hUK' : (U.subgroupOf X).map π ≤ (K.subgroupOf X).map π :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono X hUK)
    have hA : IsElemAbelian 2 (((U.subgroupOf X).map π).subgroupOf ((K.subgroupOf X).map π)) :=
      (isElemAbelian_U_quot h).subgroupOf _
    have h8 : Nat.card ↥(((U.subgroupOf X).map π).subgroupOf ((K.subgroupOf X).map π)) = 8 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK').toEquiv, card_U_quot h hs]
    obtain ⟨e⟩ := H13.L32A.S2.E8.exists_coord hA h8
    exact ⟨e⟩

theorem isQ8Q8S3_X_quot [((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal]
    (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    IsQ8Q8S3 (↥(V ⊔ conjSubgroup V g) ⧸
      (V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)) := by
  let X : Subgroup G := V ⊔ conjSubgroup V g
  let E : Subgroup G := V₀ ⊔ conjSubgroup V₀ g
  let U : Subgroup G := V ⊓ conjSubgroup M g
  let B : Subgroup G := conjSubgroup V g ⊓ M
  let K : Subgroup G := U ⊔ B
  let π : ↥X →* (↥X ⧸ E.subgroupOf X) := QuotientGroup.mk' _
  change IsQ8Q8S3 (↥X ⧸ E.subgroupOf X)
  haveI hKn : (K.subgroupOf X).Normal := K_normal h hs
  have hEK : E.subgroupOf X ≤ K.subgroupOf X := fun y hy =>
    Subgroup.mem_subgroupOf.mpr (E_le_K h hs (Subgroup.mem_subgroupOf.mp hy))
  refine ⟨(K.subgroupOf X).map π, ?_, isExtraspecialPlus2_K_quot h hs hs', ?_⟩
  · exact Subgroup.Normal.map hKn π (QuotientGroup.mk'_surjective (E.subgroupOf X))
  · obtain ⟨e⟩ := isSym_X_quot_K h hs hs'
    exact ⟨(QuotientGroup.quotientQuotientEquivQuotient (E.subgroupOf X) (K.subgroupOf X)
      hEK).trans e⟩

theorem concl (h : Cfg1667Ne M V₀ V W₁ W₂) (hs : InCalOStar 1 M V₀ V g)
    (hs' : InCalOStar 1 (conjSubgroup M g) (conjSubgroup V₀ g) (conjSubgroup V g) g⁻¹) :
    ¬ conjSubgroup V g ⊓ M ≤ normalizer (W₁ : Set G) ∧
      rk ↥(barSub V₀ V h.elemAbelian (conjSubgroup V g ⊓ M)) = 2 ∧
      (∃ z : G, orderOf z = 2 ∧
        V ⊓ conjSubgroup M g ⊓ (conjSubgroup V g ⊓ M) = Subgroup.zpowers z) ∧
      ∃ _ : ((V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)).Normal,
        IsQ8Q8S3
          (↥(V ⊔ conjSubgroup V g) ⧸
            (V₀ ⊔ conjSubgroup V₀ g).subgroupOf (V ⊔ conjSubgroup V g)) := by
  refine ⟨not_le_normalizer_W h hs, rk_barSub_B h hs, exists_eq_zpowers h hs, ?_⟩
  exact ⟨E_normal h hs hs', by
    haveI := E_normal h hs hs'
    exact isQ8Q8S3_X_quot h hs hs'⟩

end Cfg1667Ne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
