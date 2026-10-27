module

public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item211Res3Proof

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.Native.ONTriple
open Subgroup
open scoped commutatorElement

theorem isPGroup_zpowers_of_pow_three {X : Type*} [Group X] {k : X} (hk : k ^ 3 = 1) :
    IsPGroup 3 (zpowers k) := by
  intro g
  obtain ⟨n, hn⟩ := mem_zpowers_iff.mp g.2
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
    zpow_natCast, hk, one_zpow, Subgroup.coe_one]

section Model

theorem conj_zG_eq (g : GM) :
    MulAut.conj g zG = zG := by
  rw [MulAut.conj_apply, ← zG_central g, mul_inv_cancel_right]


theorem model_comm_mem_of_isPGroup {H : Subgroup GM} (hH : IsPGroup 3 H) {g k : GM}
    (hg : g ∈ H) (hk : k ∈ H) : ⁅g, k⁆ ∈ zpowers zG := by
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨n, hn⟩ := sylow_eq_threeQ P
  have hgP : g ∈ threeQ (MulAut.conj n zG) (fun i => MulAut.conj n (xG i)) := hn ▸ hP hg
  have hkP : k ∈ threeQ (MulAut.conj n zG) (fun i => MulAut.conj n (xG i)) := hn ▸ hP hk
  have h := (relG_conj n).comm_mem hgP hkP
  rwa [conj_zG_eq] at h

theorem model_exists_centralizer_two {k₁ k₂ : GM} (h1 : k₁ ^ 3 = 1) (h2 : k₂ ^ 3 = 1)
    (hc : ⁅k₁, k₂⁆ ∈ zpowers zG) :
    ∃ x : GM, x ^ 3 = 1 ∧ x * k₁ = k₁ * x ∧ x * k₂ = k₂ * x ∧ x ∉ zpowers zG := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hz3 : IsPGroup 3 (zpowers zG) := isPGroup_zpowers_of_pow_three relG.xcube
  have hzN : ∀ g : GM, g ∈ normalizer (zpowers zG : Set GM) := by
    intro g
    refine mem_normalizer_fintype fun y hy => ?_
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.mp hy
    have hc' : Commute g (zG ^ n) := (Commute.zpow_right (zG_central g).symm n)
    rw [SetLike.mem_coe, hc'.eq, mul_inv_cancel_right]
    exact zpow_mem_zpowers zG n
  set K := zpowers k₂ ⊔ zpowers zG with hK
  have hK3 : IsPGroup 3 K :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_three h2) hz3
      (fun g _ => hzN g)
  have hk₁K : k₁ ∈ normalizer (K : Set GM) := by
    have hle : K.map (MulAut.conj k₁).toMonoidHom ≤ K := by
      rw [hK, Subgroup.map_sup]
      refine sup_le ?_ ?_
      · rw [MonoidHom.map_zpowers, zpowers_le]
        have e : (MulAut.conj k₁).toMonoidHom k₂ = ⁅k₁, k₂⁆ * k₂ := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, commutatorElement_def]
          group
        rw [e]
        exact mul_mem (mem_sup_right hc) (mem_sup_left (mem_zpowers k₂))
      · rw [MonoidHom.map_zpowers, zpowers_le]
        have e : (MulAut.conj k₁).toMonoidHom zG = zG := conj_zG_eq k₁
        rw [e]
        exact mem_sup_right (mem_zpowers zG)
    exact mem_normalizer_fintype fun y hy => hle ⟨y, hy, rfl⟩
  have hH : IsPGroup 3 (zpowers k₁ ⊔ K : Subgroup GM) :=
    IsPGroup.to_sup_of_normal_right' (isPGroup_zpowers_of_pow_three h1) hK3
      (zpowers_le.mpr hk₁K)
  obtain ⟨P, hP⟩ := hH.exists_le_sylow
  obtain ⟨n, hn⟩ := sylow_eq_threeQ P
  set rel := relG_conj n with hrel
  set Q := threeQ (MulAut.conj n zG) (fun i => MulAut.conj n (xG i)) with hQ
  have hzQ : MulAut.conj n zG = zG := conj_zG_eq n
  have hk₁P : k₁ ∈ Q := hn ▸ hP (mem_sup_left (mem_zpowers k₁))
  have hk₂P : k₂ ∈ Q := hn ▸ hP (mem_sup_right (mem_sup_left (mem_zpowers k₂)))
  have hcardQ : Nat.card Q = 243 := rel.card_threeQ
  have hidx : ∀ (k : GM) (hk : k ∈ Q), (centralizer {(⟨k, hk⟩ : Q)}).index ≤ 3 := by
    intro k hk
    by_cases hkz : k ∈ zpowers (MulAut.conj n zG)
    · have htop : centralizer {(⟨k, hk⟩ : Q)} = ⊤ := by
        rw [eq_top_iff]
        intro y _
        rw [mem_centralizer_singleton_iff]
        apply Subtype.ext
        obtain ⟨m, hm⟩ := mem_zpowers_iff.mp hkz
        simp only [Subgroup.coe_mul]
        rw [← hm]
        exact ((Commute.zpow_left (rel.x_comm y.2) m).eq).symm
      rw [htop, Subgroup.index_top]
      norm_num
    · have h81 := rel.card_centralizer ⟨k, hk⟩ hkz
      have hmul := (centralizer {(⟨k, hk⟩ : Q)}).card_mul_index
      rw [h81, hcardQ] at hmul
      omega
  set C₁ := centralizer {(⟨k₁, hk₁P⟩ : Q)} with hC₁
  set C₂ := centralizer {(⟨k₂, hk₂P⟩ : Q)} with hC₂
  have hinf : (C₁ ⊓ C₂).index ≤ 9 :=
    (Subgroup.index_inf_le).trans (Nat.mul_le_mul (hidx k₁ hk₁P) (hidx k₂ hk₂P))
  have hcard : 27 ≤ Nat.card (C₁ ⊓ C₂ : Subgroup Q) := by
    have hmul := (C₁ ⊓ C₂).card_mul_index
    rw [hcardQ] at hmul
    have hpos : 0 < (C₁ ⊓ C₂).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
    by_contra hlt
    push Not at hlt
    have : Nat.card (C₁ ⊓ C₂ : Subgroup Q) * (C₁ ⊓ C₂).index < 27 * 9 :=
      Nat.mul_lt_mul_of_lt_of_le hlt hinf (by norm_num)
    omega
  by_contra hcon
  push Not at hcon
  have hle : (C₁ ⊓ C₂).map Q.subtype ≤ zpowers zG := by
    rintro _ ⟨y, ⟨hy₁, hy₂⟩, rfl⟩
    have hy3 : (y : GM) ^ 3 = 1 := rel.pow_three_of_mem y.2
    have e₁ : (y : GM) * k₁ = k₁ * y :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy₁)
    have e₂ : (y : GM) * k₂ = k₂ * y :=
      congrArg Subtype.val (mem_centralizer_singleton_iff.mp hy₂)
    exact hcon y hy3 e₁ e₂
  have h3 := Subgroup.card_le_of_le hle
  rw [Subgroup.card_map_of_injective Q.subtype_injective, Nat.card_zpowers,
    orderOf_eq_prime relG.xcube relG.x1] at h3
  omega

end Model

section Abstract

theorem map_le_normalizer_map {Y Y' : Type*} [Group Y] [Group Y'] {T D : Subgroup Y}
    (φ : Y →* Y') (hDT : D ≤ normalizer (T : Set Y)) :
    D.map φ ≤ normalizer ((T.map φ : Subgroup Y') : Set Y') := by
  rintro _ ⟨d, hd, rfl⟩
  rw [mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨d * t * d⁻¹, (mem_normalizer_iff.mp (hDT hd) t).mp ht, ?_⟩
    rw [map_mul, map_mul, map_inv]
  · rintro ⟨t, ht, hx⟩
    refine ⟨d⁻¹ * t * d, ?_, ?_⟩
    · have h1 := (mem_normalizer_iff.mp (hDT (D.inv_mem hd)) t).mp ht
      rwa [inv_inv] at h1
    · rw [map_mul, map_mul, map_inv, hx]
      group

variable {X : Type} [Group X]


theorem comm_mem_center_of_isPGroup (ψ : X ≃* GM) {H : Subgroup X} (hH : IsPGroup 3 H)
    {g k : X} (hg : g ∈ H) (hk : k ∈ H) : ⁅g, k⁆ ∈ center X := by
  rw [Sec13.ON134.mem_center_iff_model ψ, map_commutatorElement]
  exact model_comm_mem_of_isPGroup (hH.map ψ.toMonoidHom) (mem_map_of_mem _ hg)
    (mem_map_of_mem _ hk)

theorem exists_centralizer_two (ψ : X ≃* GM) {k₁ k₂ : X} (h1 : k₁ ^ 3 = 1) (h2 : k₂ ^ 3 = 1)
    (hc : ⁅k₁, k₂⁆ ∈ center X) :
    ∃ x : X, x ^ 3 = 1 ∧ x * k₁ = k₁ * x ∧ x * k₂ = k₂ * x ∧ x ∉ center X := by
  obtain ⟨y, hy3, hy1, hy2, hyz⟩ := model_exists_centralizer_two (k₁ := ψ k₁) (k₂ := ψ k₂)
    (by rw [← map_pow, h1, map_one]) (by rw [← map_pow, h2, map_one])
    (by rw [← map_commutatorElement]; exact (Sec13.ON134.mem_center_iff_model ψ).1 hc)
  refine ⟨ψ.symm y, ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hy3, map_one]
  · apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy1]
  · apply ψ.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hy2]
  · intro hmem
    apply hyz
    have := (Sec13.ON134.mem_center_iff_model ψ).1 hmem
    rwa [MulEquiv.apply_symm_apply] at this

theorem card_le_four_of_isE27
    [Finite X] (ψ : X ≃* GM) {B S : Subgroup X} (hB : Late.IsE27 B) (hS : IsPGroup 2 S)
    (hBS : B ≤ normalizer (S : Set X)) : Nat.card S ≤ 4 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set B' := B.map ψ.toMonoidHom with hB'
  set S' := S.map ψ.toMonoidHom with hS'
  have hB'27 : Late.IsE27 B' := Sec13.ON134.isE27_map hB ψ.toMonoidHom ψ.injective
  have hS'mem : S' ∈ invariantPiSubgroups ⊤ B' (piOf 2) :=
    (mem_invariantPiSubgroups_piOf_iff Nat.prime_two).2
      ⟨le_top, hS.map _, map_le_normalizer_map ψ.toMonoidHom hBS⟩
  obtain ⟨S'', hS'', hle⟩ := exists_le_mem_maxInvariantPiSubgroups hS'mem
  obtain ⟨a, haB, haz⟩ : ∃ a ∈ B', a ∉ zpowers zG := by
    by_contra hall
    push Not at hall
    have h := Subgroup.card_le_of_le (show B' ≤ zpowers zG from hall)
    rw [hB'27.2, Nat.card_zpowers, orderOf_eq_prime relG.xcube relG.x1] at h
    omega
  obtain ⟨hK4, -⟩ := part_three_M hB'27 haB haz hS''
  have h4 : Nat.card S'' = 4 := hK4.card_four
  have hcard := Subgroup.card_le_of_le hle
  rw [hS', Subgroup.card_map_of_injective ψ.injective, h4] at hcard
  exact hcard

end Abstract

end CFSG.RankThree.PartTwo.Sec21.Item211Res3Proof
