module

public import CFSG.Quasithin.EmptyFaithful.S153QPD2
public import CFSG.Quasithin.EmptyFaithful.S153QPD4

public section

namespace CFSG.Quasithin.QP

open Matrix CFSG.QuasithinUnique CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

section Transport

theorem transport_data {L M : Type*} [Group L] [Group M] (e : L ≃* M) {X : Subgroup L} {N : Type*}
    [Group N] (θ : ↥X →* N) :
    ∃ θ' : ↥(X.map e.toMonoidHom) →* N,
      (Function.Surjective θ → Function.Surjective θ') ∧
        (IsPGroup 2 θ.ker → IsPGroup 2 θ'.ker) := by
  let ε : ↥X ≃* ↥(X.map e.toMonoidHom) := X.equivMapOfInjective e.toMonoidHom e.injective
  refine ⟨θ.comp ε.symm.toMonoidHom, fun hs => hs.comp ε.symm.surjective, fun hk z => ?_⟩
  have hz : ε.symm (z : ↥(X.map e.toMonoidHom)) ∈ θ.ker := z.2
  obtain ⟨k, hk'⟩ := hk ⟨_, hz⟩
  refine ⟨k, Subtype.ext ?_⟩
  have h1 : (ε.symm (z : ↥(X.map e.toMonoidHom))) ^ 2 ^ k = 1 := congrArg Subtype.val hk'
  have h2 : ((z : ↥(X.map e.toMonoidHom))) ^ 2 ^ k = 1 := by
    apply ε.symm.injective
    rw [map_pow, map_one]
    exact h1
  rw [Subgroup.coe_pow, Subgroup.coe_one]
  exact h2

theorem isSylowTwoOf_map_equiv {L M : Type*} [Group L] [Group M] (e : L ≃* M) {S : Subgroup L}
    (hS : IsSylowTwoOf S ⊤) : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
  refine ⟨le_top, hS.2.1.map e.toMonoidHom, ?_⟩
  have h1 : ((S.map e.toMonoidHom).subgroupOf ⊤).index = (S.map e.toMonoidHom).index :=
    Subgroup.relIndex_top_right _
  have h3 : (S.map e.toMonoidHom).index = S.index := Subgroup.index_map_equiv S e
  rw [h1, h3]
  have h2 : (S.subgroupOf ⊤).index = S.index := Subgroup.relIndex_top_right S
  rw [← h2]
  exact hS.2.2

end Transport

section Conj

variable {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}

theorem exists_conj_unitriangular (hn : 1 ≤ n) {S : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hS : IsSylowTwoOf S ⊤) :
    ∃ g : SpecialLinearGroup (Fin n) F,
      S = (unitriangular n F).map
        (MulAut.conj g : SpecialLinearGroup (Fin n) F →* SpecialLinearGroup (Fin n) F) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U₀, hU₀⟩ := exists_sylow_unitriangular (K := F) 2 (n := n) hn
  obtain ⟨-, hSp, hSi⟩ := hS
  have hSi' : ¬ 2 ∣ S.index := by
    rwa [show (S.subgroupOf ⊤).index = S.index from Subgroup.relIndex_top_right S] at hSi
  let T : Sylow 2 (SpecialLinearGroup (Fin n) F) := hSp.toSylow hSi'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (SpecialLinearGroup (Fin n) F) U₀ T
  refine ⟨g, ?_⟩
  have h1 : (T : Subgroup (SpecialLinearGroup (Fin n) F)) = S := rfl
  rw [← h1, ← hg, ← hU₀]
  exact Sylow.coe_subgroup_smul

theorem exists_unitriangular_data (hn : 1 ≤ n) {Ū X : Subgroup (SpecialLinearGroup (Fin n) F)}
    (hŪ : IsSylowTwoOf Ū ⊤) (hN : Ū ≤ Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin n) F)))
    {N : Type*} [Group N] (θ : ↥X →* N) :
    ∃ (X₀ : Subgroup (SpecialLinearGroup (Fin n) F)) (θ₀ : ↥X₀ →* N),
      unitriangular n F ≤ Subgroup.normalizer (X₀ : Set (SpecialLinearGroup (Fin n) F)) ∧
        (Function.Surjective θ → Function.Surjective θ₀) ∧
          (IsPGroup 2 θ.ker → IsPGroup 2 θ₀.ker) := by
  obtain ⟨g, hg⟩ := exists_conj_unitriangular hn hŪ
  let c : SpecialLinearGroup (Fin n) F ≃* SpecialLinearGroup (Fin n) F := MulAut.conj g⁻¹
  obtain ⟨θ₀, h1, h2⟩ := transport_data c θ
  refine ⟨X.map c.toMonoidHom, θ₀, ?_, h1, h2⟩
  intro u hu
  rw [← Subgroup.map_equiv_normalizer_eq X c]
  refine ⟨g * u * g⁻¹, hN (hg ▸ ⟨u, hu, rfl⟩), ?_⟩
  simp [c, mul_assoc]

end Conj

section Models

variable {L : Type} [Group L] [Finite L] {F : Type} [Field F] [Finite F]

omit [Finite L] in
theorem false_of_sylow_normalizes_sl3 [CharP F 2] {n : ℕ} (hn3 : 3 ≤ n) (hFn : Nat.card F = 2 ^ n)
    (e : L ≃* SpecialLinearGroup (Fin 3) F) {Ŝ X : Subgroup L} (hŜ : IsSylowTwoOf Ŝ ⊤)
    (hN : Ŝ ≤ Subgroup.normalizer (X : Set L)) {N : Type} [Group N] [Finite N] [IsSimpleGroup N]
    (hN60 : Nat.card N = 60) (θ : ↥X →* N) (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) :
    False := by
  obtain ⟨θ', h1, h2⟩ := transport_data e θ
  have hŪ : IsSylowTwoOf (Ŝ.map e.toMonoidHom) ⊤ := isSylowTwoOf_map_equiv e hŜ
  have hN' : Ŝ.map e.toMonoidHom ≤ Subgroup.normalizer ((X.map e.toMonoidHom : Subgroup _) :
      Set (SpecialLinearGroup (Fin 3) F)) := by
    rw [← Subgroup.map_equiv_normalizer_eq X e]
    exact Subgroup.map_mono hN
  obtain ⟨X₀, θ₀, hN₀, h3, h4⟩ := exists_unitriangular_data (by norm_num) hŪ hN' θ'
  exact false_of_unitriangular_normalizes_sl3 hn3 hFn hN₀ hN60 θ₀ (h3 (h1 hθ)) (h4 (h2 hk))

omit [Finite L] in
theorem false_of_sylow_normalizes_sl4 (hF : Nat.card F = 2)
    (e : L ≃* SpecialLinearGroup (Fin 4) F) {Ŝ X : Subgroup L} (hŜ : IsSylowTwoOf Ŝ ⊤)
    (hN : Ŝ ≤ Subgroup.normalizer (X : Set L)) {N : Type} [Group N] [Finite N] [IsSimpleGroup N]
    (hN60 : Nat.card N = 60) (θ : ↥X →* N) (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) :
    False := by
  have : CharP F 2 := by
    let _ := Fintype.ofFinite F
    exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  obtain ⟨θ', h1, h2⟩ := transport_data e θ
  have hŪ : IsSylowTwoOf (Ŝ.map e.toMonoidHom) ⊤ := isSylowTwoOf_map_equiv e hŜ
  have hN' : Ŝ.map e.toMonoidHom ≤ Subgroup.normalizer ((X.map e.toMonoidHom : Subgroup _) :
      Set (SpecialLinearGroup (Fin 4) F)) := by
    rw [← Subgroup.map_equiv_normalizer_eq X e]
    exact Subgroup.map_mono hN
  obtain ⟨X₀, θ₀, hN₀, h3, h4⟩ := exists_unitriangular_data (by norm_num) hŪ hN' θ'
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 X₀.subtype.ker := by
    rw [Subgroup.ker_subtype]
    exact IsPGroup.of_card (n := 0) (by rw [Subgroup.card_bot, pow_zero])
  refine false_of_normalizes_sl4 hF X₀.subtype hker ?_ hN60 θ₀ (h3 (h1 hθ)) (h4 (h2 hk))
  rw [Subgroup.range_subtype]
  exact hN₀

omit [Finite L] in
theorem false_of_sylow_normalizes_sl5 (hF : Nat.card F = 2)
    (e : L ≃* SpecialLinearGroup (Fin 5) F) {Ŝ X : Subgroup L} (hŜ : IsSylowTwoOf Ŝ ⊤)
    (hN : Ŝ ≤ Subgroup.normalizer (X : Set L)) {N : Type} [Group N] [Finite N] [IsSimpleGroup N]
    (hN60 : Nat.card N = 60) (θ : ↥X →* N) (hθ : Function.Surjective θ) (hk : IsPGroup 2 θ.ker) :
    False := by
  have : CharP F 2 := by
    let _ := Fintype.ofFinite F
    exact charP_of_card_eq_prime (by rw [← Nat.card_eq_fintype_card]; exact hF)
  obtain ⟨θ', h1, h2⟩ := transport_data e θ
  have hŪ : IsSylowTwoOf (Ŝ.map e.toMonoidHom) ⊤ := isSylowTwoOf_map_equiv e hŜ
  have hN' : Ŝ.map e.toMonoidHom ≤ Subgroup.normalizer ((X.map e.toMonoidHom : Subgroup _) :
      Set (SpecialLinearGroup (Fin 5) F)) := by
    rw [← Subgroup.map_equiv_normalizer_eq X e]
    exact Subgroup.map_mono hN
  obtain ⟨X₀, θ₀, hN₀, h3, h4⟩ := exists_unitriangular_data (by norm_num) hŪ hN' θ'
  exact false_of_unitriangular_normalizes_sl5 hF hN₀ hN60 θ₀ (h3 (h1 hθ)) (h4 (h2 hk))

end Models

end CFSG.Quasithin.QP
