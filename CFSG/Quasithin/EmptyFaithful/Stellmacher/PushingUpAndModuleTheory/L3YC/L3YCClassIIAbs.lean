module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCIndexBound
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.L3YC.L3YCExtraspecial

public section

open scoped commutatorElement

namespace CFSG.Quasithin

namespace Stellmacher.PU.L3YC

section Frattini

variable {R B : Type*} [Group R] [Finite R] [Group B]

theorem frattini_le_comap_center (hR : IsPGroup 2 R) (V : Subgroup B) [CFSG.IsExtraspecial 2 ↥V]
    (ρ : R →* B) (hρ : ∀ y, ρ y ∈ V) :
    frattini R ≤ (Subgroup.center ↥V).comap (ρ.codRestrict V hρ) := by
  have : Fact (IsPGroup 2 R) := ⟨hR⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [frattini_eq_closure_commutator_union_powers (p := 2)]
  refine (Subgroup.closure_le _).mpr ?_
  rintro y (hy | ⟨x, rfl⟩)
  · have hc : _root_.commutator R ≤ (Subgroup.center ↥V).comap (ρ.codRestrict V hρ) := by
      rw [_root_.commutator_def, Subgroup.commutator_le]
      intro a _ b _
      show (ρ.codRestrict V hρ) ⁅a, b⁆ ∈ Subgroup.center ↥V
      rw [map_commutatorElement, commutatorElement_def]
      exact comm_mem_center 2 _ _
    exact hc hy
  · show (ρ.codRestrict V hρ) (x ^ 2) ∈ Subgroup.center ↥V
    rw [map_pow]
    exact pow_mem_center 2 _

theorem comm_of_frattini_trivial (hR : IsPGroup 2 R) (ρ : R →* B)
    (h : ∀ y ∈ frattini R, ρ y = 1) (a b : R) : ρ a * ρ b = ρ b * ρ a := by
  have : Fact (IsPGroup 2 R) := ⟨hR⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc : ⁅a, b⁆ ∈ _root_.commutator R := by
    rw [_root_.commutator_def]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  have h1 := h _ (commutator_le_frattini_of_isPGroup (p := 2) hc)
  rwa [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1

end Frattini

section Quotient

variable {Λ B : Type} [Group Λ] [Group B]

theorem le_pCore_two' {X : Type} [Group X] {N : Subgroup X} (hN : N.Normal) (hp : IsPGroup 2 N) :
    N ≤ CFSG.pCore 2 X :=
  le_sSup ⟨hN, hp⟩

theorem ker_le_pCore (π : Λ →* B) (hK : IsPGroup 2 π.ker) : π.ker ≤ CFSG.pCore 2 Λ :=
  le_pCore_two' inferInstance hK

theorem map_le_pCore (π : Λ →* B) (hπ : Function.Surjective π) (Q : Subgroup Λ) [Q.Normal]
    (hQ : IsPGroup 2 Q) : Q.map π ≤ CFSG.pCore 2 B :=
  le_pCore_two' (Subgroup.Normal.map ‹_› π hπ)
    (hQ.of_surjective (π.subgroupMap Q) (MonoidHom.subgroupMap_surjective π Q))

theorem pCore_le_map (π : Λ →* B) (hπ : Function.Surjective π) (hK : IsPGroup 2 π.ker) :
    CFSG.pCore 2 B ≤ (CFSG.pCore 2 Λ).map π := by
  have hn : ((CFSG.pCore 2 B).comap π).Normal := (CFSG.pCore_normal).comap π
  have hp : IsPGroup 2 ↥((CFSG.pCore 2 B).comap π) := by
    intro x
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (G := B) (p := 2)) ⟨π x, x.2⟩
    have hm' : (π x) ^ (2 ^ m) = 1 := congrArg Subtype.val hm
    have hxk : ((x : Λ) ^ (2 ^ m)) ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_pow]; exact hm'
    obtain ⟨n, hn'⟩ := hK ⟨_, hxk⟩
    refine ⟨m + n, Subtype.ext ?_⟩
    have := congrArg Subtype.val hn'
    simpa [pow_add, pow_mul] using this
  have hle := le_pCore_two' hn hp
  calc CFSG.pCore 2 B = ((CFSG.pCore 2 B).comap π).map π :=
        (Subgroup.map_comap_eq_self_of_surjective hπ _).symm
    _ ≤ (CFSG.pCore 2 Λ).map π := Subgroup.map_mono hle

theorem card_eq_card_ker_mul_card_map [Finite Λ] (π : Λ →* B) (X : Subgroup Λ) (hX : π.ker ≤ X) :
    Nat.card X = Nat.card π.ker * Nat.card (X.map π) := by
  let φ : ↥X →* B := π.comp X.subtype
  have h1 := Subgroup.card_ker_mul_card_range φ
  have hφk : φ.ker = π.ker.subgroupOf X := by
    ext x
    simp [φ, MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  have hφr : φ.range = X.map π := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hφk, hφr] at h1
  have hc : Nat.card ↥(π.ker.subgroupOf X) = Nat.card ↥π.ker := by
    rw [← Subgroup.card_map_of_injective X.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hX]
  rw [hc] at h1
  exact h1.symm

theorem card_map_pCore_le [Finite Λ]
    [Group.IsPerfect Λ] (π : Λ →* B) (hK : IsPGroup 2 π.ker)
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* GL (Fin 3) (ZMod 2)) :
    Nat.card ((CFSG.pCore 2 Λ).map π) ≤
      2 * Nat.card (⁅CFSG.pCore 2 Λ, (⊤ : Subgroup Λ)⁆.map π) := by
  set N := CFSG.pCore 2 Λ with hN
  have hKN : π.ker ≤ N := ker_le_pCore π hK
  set M : Subgroup Λ := ⁅N, (⊤ : Subgroup Λ)⁆ ⊔ π.ker with hM
  have : (⁅N, (⊤ : Subgroup Λ)⁆).Normal := Subgroup.commutator_normal N ⊤
  have : M.Normal := Subgroup.sup_normal _ _
  have hMN : M ≤ N := sup_le (Subgroup.commutator_le_left N ⊤) hKN
  have h1 := card_le_two_mul_of_commutator_le N M le_sup_left hMN e
  have h2 := card_eq_card_ker_mul_card_map π N hKN
  have h3 := card_eq_card_ker_mul_card_map π M le_sup_right
  have h4 : M.map π = ⁅N, (⊤ : Subgroup Λ)⁆.map π := by
    have hker : π.ker.map π = ⊥ := by
      rw [eq_bot_iff]
      rintro _ ⟨x, hx, rfl⟩
      exact hx
    rw [hM, Subgroup.map_sup, hker, sup_bot_eq]
  rw [h4] at h3
  have hpos : 0 < Nat.card π.ker := Nat.card_pos
  rw [h2, h3] at h1
  nlinarith

theorem exists_noncomm_map_commutator [Finite Λ] [Finite B]
    [Group.IsPerfect Λ]
    (π : Λ →* B) (hπ : Function.Surjective π) (hK : IsPGroup 2 π.ker)
    (e : Λ ⧸ CFSG.pCore 2 Λ ≃* GL (Fin 3) (ZMod 2)) (hV : CFSG.IsExtraspecial 2 ↥(CFSG.pCore 2 B))
    (hV7 : Nat.card (CFSG.pCore 2 B) = 2 ^ 7) :
    ∃ a ∈ ⁅CFSG.pCore 2 Λ, (⊤ : Subgroup Λ)⁆, ∃ b ∈ ⁅CFSG.pCore 2 Λ, (⊤ : Subgroup Λ)⁆,
      π a * π b ≠ π b * π a := by
  by_contra hcon
  push Not at hcon
  set N := CFSG.pCore 2 Λ with hN
  set Q : Subgroup Λ := ⁅N, (⊤ : Subgroup Λ)⁆ with hQ
  have : Q.Normal := Subgroup.commutator_normal N ⊤
  have hQN : Q ≤ N := Subgroup.commutator_le_left N ⊤
  have hQp : IsPGroup 2 Q := (CFSG.pCore_isPGroup (G := Λ) (p := 2)).to_le hQN
  have hQV : Q.map π ≤ CFSG.pCore 2 B := map_le_pCore π hπ Q hQp
  set A : Subgroup ↥(CFSG.pCore 2 B) := (Q.map π).subgroupOf (CFSG.pCore 2 B) with hA
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_subgroupOf.mp ha
    obtain ⟨y, hy, hyb⟩ := Subgroup.mem_subgroupOf.mp hb
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    rw [← hxa, ← hyb]
    exact hcon x hx y hy
  have hAcard : Nat.card A = Nat.card (Q.map π) := by
    rw [← Subgroup.card_map_of_injective (CFSG.pCore 2 B).subtype_injective,
      hA, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQV]
  have h1 := card_map_pCore_le π hK e
  have h2 : Nat.card (CFSG.pCore 2 B) ≤ Nat.card (N.map π) :=
    Subgroup.card_le_of_le (pCore_le_map π hπ hK)
  have h3 := card_le_eight_of_abelian_index_le_two (V := ↥(CFSG.pCore 2 B)) A hAc
    (by rw [hAcard]; exact h2.trans h1)
  rw [hV7] at h3
  norm_num at h3

end Quotient


end Stellmacher.PU.L3YC

end CFSG.Quasithin
