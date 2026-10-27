module

public import CFSG.Quasithin.EmptyFaithful.T1521SL2EOff
public import CFSG.Quasithin.EmptyFaithful.T1521SL2EAct
public import CFSG.Quasithin.EmptyFaithful.S153WJOff

public section

namespace CFSG.Quasithin.L21521E

open CFSG.PSL2Table CFSG.Open CFSG.QuasithinUnique
open scoped MatrixGroups

variable {G : Type} [Group G]

theorem conjByElt_one' (K : Subgroup G) : conjByElt 1 K = K := by
  ext x
  rw [mem_conjByElt]
  simp

theorem conjByElt_mul' (s t : G) (K : Subgroup G) :
    conjByElt (s * t) K = conjByElt s (conjByElt t K) := by
  ext x
  rw [mem_conjByElt, mem_conjByElt, mem_conjByElt]
  rw [mul_inv_rev]
  group

theorem mem_normalizer_of_conjByElt_eq {y : G} {L : Subgroup G} (h : conjByElt y L = L) :
    y ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := mem_conjByElt (t := y) (x := y * x * y⁻¹) (K := L)
  rw [h] at h1
  have h2 : y⁻¹ * (y * x * y⁻¹) * y = x := by group
  rw [h2] at h1
  exact h1.symm

theorem isElemAbelian_conjByElt {V : Subgroup G} (hV : IsElemAbelian 2 V) (a : G) :
    IsElemAbelian 2 (conjByElt a V) := by
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

theorem le_normalizer_of_wreath {S L : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hL : IsPSL 2 2 n ↥L)
    (hSyl : IsSylowTwoOf (S ⊓ L) L) {t : G} (hset : conjSubgroupsBy S L = {L, conjByElt t L})
    (hcomm : ⁅L, conjByElt t L⁆ = ⊥) {A : Subgroup G} (hA : IsMaxElemAbelian S A) :
    A ≤ Subgroup.normalizer (L : Set G) := by
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
    · exact absurd (mem_normalizer_of_conjByElt_eq h1) hyn
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
      apply mem_normalizer_of_conjByElt_eq
      rw [conjByElt_mul', h1, ← conjByElt_mul', inv_mul_cancel, conjByElt_one']
  have hindexA : Nat.card A ≤ 2 * Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set G)) :=
    W153.card_le_two_mul_of_forall inf_le_left hAcomm haA ha2 hhalf
  obtain ⟨K, hKf, hKfin, φ, hK, hφ⟩ := exists_equiv_unipotent (by omega) hL hSyl
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hVL : S ⊓ L ≤ L := inf_le_right
  have hSN : ∀ b ∈ A ⊓ Subgroup.normalizer (L : Set G), ∀ y ∈ S ⊓ L, b * y * b⁻¹ ∈ S ⊓ L := by
    intro b hb y hy
    have hbS : b ∈ S := hA.1 hb.1
    exact ⟨S.mul_mem (S.mul_mem hbS hy.1) (S.inv_mem hbS),
      (Subgroup.mem_normalizer_iff.mp hb.2 y).mp hy.2⟩
  have hindexA₀ : Nat.card ↥(A ⊓ Subgroup.normalizer (L : Set G)) ≤
      2 * Nat.card ↥((A ⊓ Subgroup.normalizer (L : Set G)) ⊓
        Subgroup.centralizer ((S ⊓ L : Subgroup G) : Set G)) :=
    card_le_two_mul_of_twist hK (fun x : K => ((φ.symm (mk (unip x)) : ↥L) : G))
      (coord_injective φ) (coord_mem φ hφ) (fun y hy => coord_surj φ hφ hVL hy)
      (B2F.isElemAbelian_mono inf_le_left hA.2.1)
      (fun b hb => exists_twist_conj φ hφ hb.2 (hSN b hb))
  set VL : Subgroup G := S ⊓ L with hVLdef
  set VM : Subgroup G := conjByElt a VL with hVMdef
  have hVMS : VM ≤ S := by
    rintro _ ⟨y, hy, rfl⟩
    exact S.mul_mem (S.mul_mem haS hy.1) (S.inv_mem haS)
  have hVMM : VM ≤ conjByElt t L := by
    rw [← hMa]
    exact Subgroup.map_mono inf_le_right
  have hLM : ∀ x ∈ L, ∀ y ∈ conjByElt t L, x * y = y * x := by
    intro x hx y hy
    have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.1 hcomm
    exact (Subgroup.mem_centralizer_iff.1 (hle hx) y hy).symm
  have hcommLM : ∀ x ∈ VL, ∀ y ∈ VM, x * y = y * x := fun x hx y hy =>
    hLM x (hVL hx) y (hVMM hy)
  have hVLea : IsElemAbelian 2 VL := isElemAbelian_of_equiv_unipotent φ hφ hVL
  have hVMea : IsElemAbelian 2 VM := isElemAbelian_conjByElt hVLea a
  have hUea : IsElemAbelian 2 (VL ⊔ VM) := B2F.isElemAbelian_sup_of_commute hVLea hVMea hcommLM
  have hUS : VL ⊔ VM ≤ S := sup_le inf_le_left hVMS
  have hbot : VL ⊓ VM = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hzL : z ∈ L := hVL hz.1
    have hzM : z ∈ conjByElt t L := hVMM hz.2
    have hcent : ∀ y : ↥L, y * ⟨z, hzL⟩ = ⟨z, hzL⟩ * y := fun y =>
      Subtype.ext (hLM y.1 y.2 z hzM)
    have h1 : φ ⟨z, hzL⟩ ∈ unipotent K := (hφ ⟨z, hzL⟩).mp hz.1
    have h4 : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h5 : φ ⟨z, hzL⟩ = 1 := eq_one_of_central_unipotent h2K h4 h1 (fun y => by
      have h6 := congrArg φ (hcent (φ.symm y))
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h6)
    have h7 : (⟨z, hzL⟩ : ↥L) = 1 := φ.injective (h5.trans (map_one φ).symm)
    have h8 : z = 1 := congrArg Subtype.val h7
    rw [h8]
    exact Subgroup.one_mem _
  have hVLcard : Nat.card VL = Nat.card K := card_eq_of_coord φ hφ hVL
  have hVMcard : Nat.card VM = Nat.card VL :=
    Subgroup.card_map_of_injective (f := (MulAut.conj a).toMonoidHom) (MulAut.conj a).injective
  have hUcard : Nat.card ↥(VL ⊔ VM) = Nat.card K * Nat.card K := by
    have h := B2F.card_sup_mul_card_inf_of_commute hcommLM
    rw [hbot, Subgroup.card_bot, mul_one, hVMcard, hVLcard] at h
    exact h
  have hAU : Nat.card ↥(A ⊓ (VL ⊔ VM)) ≤ Nat.card K := by
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
    exact Nat.le_of_mul_le_mul_right hle Nat.card_pos
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
  have hq : 0 < Nat.card K := Nat.card_pos
  have h2 : Nat.card K * (Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G)) *
        Nat.card K) ≤
      4 * (Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G)) * Nat.card K) :=
    calc _ = Nat.card ↥(VL ⊔ VM) *
          Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G)) := by
          rw [hUcard]; ring
      _ ≤ Nat.card A * Nat.card ↥(A ⊓ (VL ⊔ VM)) := hineq
      _ ≤ (4 * Nat.card ↥(A ⊓ Subgroup.centralizer ((VL ⊔ VM : Subgroup G) : Set G))) *
          Nat.card K := Nat.mul_le_mul hC4 hAU
      _ = _ := by ring
  have h3 : Nat.card K ≤ 4 := Nat.le_of_mul_le_mul_right h2 (Nat.mul_pos hCpos hq)
  rw [hK] at h3
  have h4 : 2 ^ 3 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  omega

end CFSG.Quasithin.L21521E
