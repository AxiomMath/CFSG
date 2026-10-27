module

public import CFSG.Quasithin.Background.C2Defs
public import CFSG.Quasithin.EmptyFaithful.S153WJOff
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Coord
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4Off

public section

namespace CFSG.Quasithin.Sp4

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin

variable {G : Type} [Group G]

theorem conjByElt_one_sp4 (K : Subgroup G) : conjByElt 1 K = K := by
  ext x
  rw [mem_conjByElt]
  simp

theorem conjByElt_mul_sp4 (s t : G) (K : Subgroup G) :
    conjByElt (s * t) K = conjByElt s (conjByElt t K) := by
  ext x
  rw [mem_conjByElt, mem_conjByElt, mem_conjByElt]
  rw [_root_.mul_inv_rev]
  group

theorem mem_normalizer_of_conjByElt_eq_sp4 {y : G} {L : Subgroup G} (h : conjByElt y L = L) :
    y ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := mem_conjByElt (t := y) (x := y * x * y⁻¹) (K := L)
  rw [h] at h1
  have h2 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
  rw [h2] at h1
  exact h1.symm

theorem isElemAbelian_conjByElt_sp4 {V : Subgroup G} (hV : CFSG.Open.IsElemAbelian 2 V) (a : G) :
    CFSG.Open.IsElemAbelian 2 (conjByElt a V) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨x, u, hu, rfl⟩ := x
    obtain ⟨y, v, hv, rfl⟩ := y
    apply Subtype.ext
    have h := congrArg Subtype.val (hV.1.is_comm.comm (⟨u, hu⟩ : V) ⟨v, hv⟩)
    change (a * u * a⁻¹) * (a * v * a⁻¹) = (a * v * a⁻¹) * (a * u * a⁻¹)
    have h' : u * v = v * u := h
    calc (a * u * a⁻¹) * (a * v * a⁻¹) = a * (u * v) * a⁻¹ := by group
      _ = a * (v * u) * a⁻¹ := by rw [h']
      _ = (a * v * a⁻¹) * (a * u * a⁻¹) := by group
  · obtain ⟨u, hu, rfl⟩ := hx
    have h := hV.2 u hu
    change (a * u * a⁻¹) ^ 2 = 1
    rw [conj_pow, h]
    group

variable [Finite G]

theorem le_normalizer_of_wreath_sp4 {S L : Subgroup G} {n : ℕ} (hn : 2 ≤ n)
    (hL : IsPSp4 2 n ↥L) (hSyl : IsSylowTwoOf (S ⊓ L) L) (hS2 : IsPGroup 2 S) {t : G}
    (hset : conjSubgroupsBy S L = {L, conjByElt t L}) (hcomm : ⁅L, conjByElt t L⁆ = ⊥)
    {A : Subgroup G} (hA : IsMaxElemAbelian S A) : A ≤ Subgroup.normalizer (L : Set G) := by
  classical
  by_contra hAnot
  obtain ⟨a, haA, han⟩ : ∃ a ∈ A, a ∉ Subgroup.normalizer (L : Set G) := by
    by_contra h
    exact hAnot fun x hx => by
      by_contra hc
      exact h ⟨x, hx, hc⟩
  have haS : a ∈ S := hA.1 haA
  have hM : ∀ y ∈ S, y ∉ Subgroup.normalizer (L : Set G) → conjByElt y L = conjByElt t L := by
    intro y hy hyn
    have h1 : conjByElt y L ∈ conjSubgroupsBy S L := ⟨y, hy, rfl⟩
    rw [hset] at h1
    rcases h1 with h1 | h1
    · exact absurd (mem_normalizer_of_conjByElt_eq_sp4 h1) hyn
    · exact h1
  have hMa : conjByElt a L = conjByElt t L := hM a haS han
  have hAcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hA.2.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have ha2 : a * a = 1 := by
    have := hA.2.1.2 a haA
    rwa [sq] at this
  have hhalf : ∀ x ∈ A, x ∈ A ⊓ Subgroup.normalizer (L : Set G) ∨
      a⁻¹ * x ∈ A ⊓ Subgroup.normalizer (L : Set G) := by
    intro x hx
    by_cases hxn : x ∈ Subgroup.normalizer (L : Set G)
    · exact Or.inl ⟨hx, hxn⟩
    · right
      refine ⟨A.mul_mem (A.inv_mem haA) hx, ?_⟩
      have h1 : conjByElt x L = conjByElt a L := (hM x (hA.1 hx) hxn).trans hMa.symm
      apply mem_normalizer_of_conjByElt_eq_sp4
      rw [conjByElt_mul_sp4, h1, ← conjByElt_mul_sp4, inv_mul_cancel, conjByElt_one_sp4]
  have hindexA : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set G)) :=
    W153.card_le_two_mul_of_forall inf_le_left hAcomm haA ha2 hhalf
  obtain ⟨K, hKf, hKfin, φ, hK, hφ⟩ := exists_equiv_projUnipotent hn hL hSyl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      Nat.prime_two (by omega) hK
  have hRL : S ⊓ L ≤ L := inf_le_right
  have hRS : S ⊓ L ≤ S := inf_le_left
  have hVLR : vSub φ ≤ S ⊓ L := vSub_le_R hφ
  have hVLL : vSub φ ≤ L := vSub_le_L φ
  have hS₀N : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (L : Set G) := inf_le_right
  have hS₀2 : IsPGroup 2 ↥(S ⊓ Subgroup.normalizer (L : Set G)) := hS2.to_le inf_le_left
  have hRS₀ : S ⊓ L ≤ S ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf hRS (Subgroup.le_normalizer (H := L) |> fun h => inf_le_right.trans h)
  have hA₀S₀ : A ⊓ Subgroup.normalizer (L : Set G) ≤ S ⊓ Subgroup.normalizer (L : Set G) :=
    le_inf (inf_le_left.trans hA.1) inf_le_right
  have hA₀e : CFSG.Open.IsElemAbelian 2 (A ⊓ Subgroup.normalizer (L : Set G)) :=
    B2F.isElemAbelian_mono inf_le_left hA.2.1
  have hindexA₀ : Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set G)) ≤
      2 * Nat.card ↥((A ⊓ Subgroup.normalizer (L : Set G)) ⊓
        Subgroup.centralizer ((vSub φ : Subgroup G) : Set G)) :=
    card_le_two_mul_of_out (by omega) hK φ hS₀N hS₀2 hRL hRS₀ hSyl hVLL
      (fun r hr v hv => by
        obtain ⟨x, rfl⟩ := exists_vW_of_mem φ hv
        exact vW_commute_R hφ hRL hr x) hA₀S₀ hA₀e
  set VL : Subgroup G := vSub φ with hVLdef
  set VM : Subgroup G := conjByElt a VL with hVMdef
  have hVMS : VM ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact S.mul_mem (S.mul_mem haS (hVLR hy).1) (S.inv_mem haS)
  have hVMM : VM ≤ conjByElt t L := by
    rw [← hMa]
    exact Subgroup.map_mono hVLL
  have hLM : ∀ x ∈ L, ∀ y ∈ conjByElt t L, x * y = y * x := by
    intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm
  have hcommLM : ∀ x ∈ VL, ∀ y ∈ VM, x * y = y * x := fun x hx y hy =>
    hLM x (hVLL hx) y (hVMM hy)
  have hVLea : CFSG.Open.IsElemAbelian 2 VL := isElemAbelian_vSub
  have hVMea : CFSG.Open.IsElemAbelian 2 VM := isElemAbelian_conjByElt_sp4 hVLea a
  have hUea : CFSG.Open.IsElemAbelian 2 (VL ⊔ VM) :=
    B2F.isElemAbelian_sup_of_commute hVLea hVMea hcommLM
  have hUS : VL ⊔ VM ≤ S := sup_le (hVLR.trans hRS) hVMS
  have hZ : Subgroup.center ↥L = ⊥ := CFSG.QuasithinUnique.Lin2.Five.center_eq_bot_of_equiv φ
  have hbot : VL ⊓ VM = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzL : z ∈ L := hVLL hz.1
    have hzM : z ∈ conjByElt t L := hVMM hz.2
    have hcent : ⟨z, hzL⟩ ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hLM y.1 y.2 z hzM)
    rw [hZ, Subgroup.mem_bot] at hcent
    have h8 : z = 1 := congrArg Subtype.val hcent
    rw [h8]
    exact Subgroup.one_mem _
  have hVLcard : Nat.card VL = Nat.card K ^ 2 := card_vSub
  have hVMcard : Nat.card VM = Nat.card VL :=
    Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective
  have hUcard : Nat.card ↥(VL ⊔ VM) = Nat.card K ^ 2 * Nat.card K ^ 2 := by
    have h := B2F.card_sup_mul_card_inf_of_commute hcommLM
    rw [hbot, Subgroup.card_bot, mul_one, hVMcard, hVLcard] at h
    exact h
  have hAU : Nat.card ↥(A ⊓ (VL ⊔ VM)) ≤ Nat.card K ^ 2 := by
    have hHU : A ⊓ (VL ⊔ VM) ≤ VL ⊔ VM := inf_le_right
    have hHVL : (A ⊓ (VL ⊔ VM)) ⊓ VL = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hzA : z ∈ A := hz.1.1
      have hzVL : z ∈ VL := hz.2
      have hcz : a * z * a⁻¹ = z := by
        rw [mul_inv_eq_iff_eq_mul]
        exact hAcomm a haA z hzA
      have hzVM : z ∈ VM := ⟨z, hzVL, hcz⟩
      have h1 : z ∈ VL ⊓ VM := ⟨hzVL, hzVM⟩
      rw [hbot] at h1
      exact h1
    have hcommHVL : ∀ x ∈ A ⊓ (VL ⊔ VM), ∀ y ∈ VL, x * y = y * x := by
      intro x hx y hy
      exact congrArg Subtype.val (hUea.1.is_comm.comm (⟨x, hHU hx⟩ : ↥(VL ⊔ VM))
        ⟨y, Subgroup.mem_sup_left hy⟩)
    have h := B2F.card_sup_mul_card_inf_of_commute hcommHVL
    rw [hHVL, Subgroup.card_bot, mul_one] at h
    have hle : Nat.card ↥((A ⊓ (VL ⊔ VM)) ⊔ VL) ≤ Nat.card ↥(VL ⊔ VM) :=
      Subgroup.card_le_of_le (sup_le hHU le_sup_left)
    rw [h, hUcard, hVLcard] at hle
    exact Nat.le_of_mul_le_mul_right hle (pow_pos Nat.card_pos 2)
  have hCsub : (A ⊓ Subgroup.normalizer (L : Set G)) ⊓ Subgroup.centralizer (VL : Set G) ≤
      A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G) := by
    intro b hb
    refine Subgroup.mem_inf.mpr ⟨hb.1.1, ?_⟩
    have hbVL : ∀ h ∈ VL, h * b = b * h := Subgroup.mem_centralizer_iff.mp hb.2
    have hab : Commute a b := hAcomm a haA b hb.1.1
    have hbVM : ∀ h ∈ VM, h * b = b * h := by
      rintro _ ⟨v, hv, rfl⟩
      have hvb : Commute v b := hbVL v hv
      exact (((hab.mul_left hvb).mul_left hab.inv_left) : Commute (a * v * a⁻¹) b).eq
    have hle : VL ⊔ VM ≤ Subgroup.centralizer ({b} : Set G) := by
      refine sup_le (fun h hh => ?_) (fun h hh => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hbVL h hh
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hbVM h hh
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  have hineq := W153.card_mul_le_of_isMaxElemAbelian hA hUea hUS
  have hC4 : Nat.card A ≤
      4 * Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G)) := by
    have h1 := Subgroup.card_le_of_le hCsub
    omega
  have hCpos : 0 < Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G)) :=
    Nat.card_pos
  have hq : 0 < Nat.card K ^ 2 := pow_pos Nat.card_pos 2
  have h2 : Nat.card K ^ 2 * Nat.card K ^ 2 *
        Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G)) ≤
      (4 * Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G))) *
        Nat.card K ^ 2 :=
    calc _ = Nat.card ↥(VL ⊔ VM) *
          Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G)) := by
          rw [hUcard]
      _ ≤ Nat.card A * Nat.card ↥(A ⊓ (VL ⊔ VM)) := hineq
      _ ≤ (4 * Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G))) *
          Nat.card K ^ 2 := Nat.mul_le_mul hC4 hAU
  have h3 : Nat.card K ^ 2 * Nat.card K ^ 2 ≤ 4 * Nat.card K ^ 2 :=
    Nat.le_of_mul_le_mul_right (c := Nat.card ↥(A ⊓ Subgroup.centralizer
      ((VL ⊔ VM : Subgroup G) : Set G))) (h2.trans (le_of_eq (by ring))) hCpos
  have h4 : Nat.card K ^ 2 ≤ 4 := Nat.le_of_mul_le_mul_right h3 hq
  rw [hK] at h4
  have h5 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h6 : (2 ^ 2) ^ 2 ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h5 2
  omega

end CFSG.Quasithin.Sp4
