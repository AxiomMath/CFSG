module

public import CFSG.RankThree.PartOne.SRC.ProductCentral
public import CFSG.RankThree.PartOne.SRC.ProductBig
public import CFSG.RankThree.PartOne.SRC.CentralizerKer
public import CFSG.RankThree.PartOne.SRC.ProductNT

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.SL2MinimalFaithful Subgroup

theorem isPerfect_prod {A B : Type*} [Group A] [Group B] (hA : Group.IsPerfect A)
    (hB : Group.IsPerfect B) : Group.IsPerfect (A × B) := by
  rw [Group.isPerfect_def, eq_top_iff]
  rintro ⟨a, b⟩ -
  have h1 : (a, (1 : B)) ∈ commutator (A × B) := by
    have ha : a ∈ commutator A := by rw [hA.commutator_eq_top]; exact mem_top a
    have := Subgroup.mem_map_of_mem (MonoidHom.inl A B) ha
    rw [_root_.commutator_def, Subgroup.map_commutator] at this
    refine (Subgroup.commutator_mono le_top le_top) this
  have h2 : ((1 : A), b) ∈ commutator (A × B) := by
    have hb : b ∈ commutator B := by rw [hB.commutator_eq_top]; exact mem_top b
    have := Subgroup.mem_map_of_mem (MonoidHom.inr A B) hb
    rw [_root_.commutator_def, Subgroup.map_commutator] at this
    refine (Subgroup.commutator_mono le_top le_top) this
  have := mul_mem h1 h2
  simpa using this

theorem card_center_SL2_eq_two_pow (F : Type*) [Field F] [Finite F] :
    ∃ n : ℕ, Nat.card (Subgroup.center (SpecialLinearGroup (Fin 2) F)) = 2 ^ n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (Subgroup.center (SpecialLinearGroup (Fin 2) F)) := by
    intro g
    exact ⟨1, Subtype.ext (by simpa using sq_eq_one_of_mem_center_SL2 g.2)⟩
  exact hp.exists_card_eq

theorem specialLinear_quasisimple_of_card {F : Type*} [Field F] [Finite F]
    (hF : 4 ≤ Nat.card F) : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F) :=
  CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2 F le_rfl
    (Or.inr (by omega)) (Or.inr (by omega))


theorem rank_four_of_cover_SL2_prod {p e₁ e₂ : ℕ} [Fact p.Prime] {F₁ F₂ : Type} [Field F₁]
    [Field F₂] [Finite F₁] [Finite F₂] [CharP F₁ p] [CharP F₂ p] (hF₁ : Nat.card F₁ = p ^ e₁)
    (hF₂ : Nat.card F₂ = p ^ e₂) (hp2 : p ≠ 2) (he₁ : 2 ≤ e₁) (he₂ : 2 ≤ e₂)
    (h₁9 : Nat.card F₁ ≠ 9) (h₂9 : Nat.card F₂ ≠ 9) {W : Type} [Group W] [Finite W]
    (ρ : W →* SpecialLinearGroup (Fin 2) F₁ × SpecialLinearGroup (Fin 2) F₂)
    (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) :
    ∃ (E : Subgroup W) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  classical
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hF₁9 : 9 ≤ p ^ e₁ := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ e₁ := Nat.pow_le_pow_right (by norm_num) he₁
      _ ≤ p ^ e₁ := Nat.pow_le_pow_left hp3 e₁
  have hF₂9 : 9 ≤ p ^ e₂ := by
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ e₂ := Nat.pow_le_pow_right (by norm_num) he₂
      _ ≤ p ^ e₂ := Nat.pow_le_pow_left hp3 e₂
  have hQ₁ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F₁) :=
    specialLinear_quasisimple_of_card (by omega)
  have hQ₂ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F₂) :=
    specialLinear_quasisimple_of_card (by omega)
  have hXperf : Group.IsPerfect (SpecialLinearGroup (Fin 2) F₁ × SpecialLinearGroup (Fin 2) F₂) :=
    isPerfect_prod hQ₁.1 hQ₂.1
  obtain ⟨W₀, -, hW₀min⟩ := Finite.exists_le_minimal (p := fun K : Subgroup W => K.map ρ = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective ρ hρ])
  set ρ₀ : W₀ →* SpecialLinearGroup (Fin 2) F₁ × SpecialLinearGroup (Fin 2) F₂ :=
    ρ.comp W₀.subtype with hρ₀
  have hρ₀s : Function.Surjective ρ₀ := by
    intro x
    have hx : x ∈ W₀.map ρ := by
      rw [hW₀min.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin₀ : ∀ M : Subgroup W₀, M.map ρ₀ = ⊤ → M = ⊤ := by
    intro M hM
    have h1 : (M.map W₀.subtype).map ρ = ⊤ := by
      rw [Subgroup.map_map]
      exact hM
    have h2 := hW₀min.le_of_le h1 (Subgroup.map_subtype_le M)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  have hker₀ : IsPGroup p ρ₀.ker := by
    intro x
    have hx1 : ρ ((x : W₀) : W) = 1 := MonoidHom.mem_ker.mp x.2
    obtain ⟨k, hk⟩ := hker ⟨((x : W₀) : W), hx1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : ρ.ker => (z : W)) hk))⟩
  have hperf : Group.IsPerfect W₀ := by
    rw [Group.isPerfect_def]
    apply hmin₀
    have h1 := hXperf.commutator_eq_top
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hρ₀s]
    rwa [_root_.commutator_def] at h1
  suffices H : ∃ (E : Subgroup W₀) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧
      Nat.card E = p ^ k by
    obtain ⟨E, k, hk, hE, hc⟩ := H
    refine ⟨E.map W₀.subtype, k, hk, isElementaryAbelian_map' W₀.subtype hE, ?_⟩
    rw [Subgroup.card_map_of_injective W₀.subtype_injective, hc]
  by_cases hcen : ρ₀.ker ≤ center W₀
  ·
    obtain ⟨E, hE, hc⟩ := exists_elementaryAbelian_of_central_prod hF₁ hF₂ (by omega) h₁9
      (by omega) h₂9 ρ₀ hρ₀s hcen
    exact ⟨E, e₁ + e₂, by omega, hE, hc⟩
  ·
    by_contra hno
    push Not at hno
    apply hcen
    obtain ⟨m₁, hm₁2, hm₁, hm₁g⟩ := bigAt_of_card hp2 he₁ hF₁
    obtain ⟨m₂, hm₂2, hm₂, hm₂g⟩ := bigAt_of_card hp2 he₂ hF₂
    obtain ⟨n₁, hn₁⟩ := card_center_SL2_eq_two_pow F₁
    obtain ⟨n₂, hn₂⟩ := card_center_SL2_eq_two_pow F₂
    have hp4 : Nat.Coprime (p ^ 4) 2 := Nat.coprime_two_right.mpr
      ((hp.odd_of_ne_two hp2).pow)
    have hp4SL : p ^ 4 ∣ Nat.card (SpecialLinearGroup (Fin 2) F₁) *
        Nat.card (SpecialLinearGroup (Fin 2) F₂) := by
      have h1 : p ^ e₁ ∣ Nat.card (SpecialLinearGroup (Fin 2) F₁) := by
        rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF₁]
        exact dvd_mul_right _ _
      have h2 : p ^ e₂ ∣ Nat.card (SpecialLinearGroup (Fin 2) F₂) := by
        rw [CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hF₂]
        exact dvd_mul_right _ _
      have h3 : p ^ (e₁ + e₂) ∣ Nat.card (SpecialLinearGroup (Fin 2) F₁) *
          Nat.card (SpecialLinearGroup (Fin 2) F₂) := by
        rw [pow_add]
        exact mul_dvd_mul h1 h2
      exact (pow_dvd_pow p (by omega : 4 ≤ e₁ + e₂)).trans h3
    refine central_of_rank_le_three_gen hp hp2 ρ₀ hρ₀s hker₀ hmin₀ ?_ ?_ ?_
    · intro K hK n hn hdvd
      rw [Nat.card_prod] at hdvd
      exact eq_top_of_card_dvd_prod hQ₁ hQ₂ (m := p ^ 4) hp4SL
        (by rw [hn₁, hn₂, ← pow_add]; exact Nat.Coprime.pow_right _ hp4)
        (fun h => not_pow_four_dvd_card_GL hn h)
        hm₁ (by rw [hn₁]; exact Nat.Coprime.pow_right _ hm₁2) (hm₁g n hn)
        hm₂ (by rw [hn₂]; exact Nat.Coprime.pow_right _ hm₂2) (hm₂g n hn) K hdvd
    · intro N hN hall
      obtain ⟨ζ₁, hζ₁, hζo₁⟩ := exists_torus_gen (F := F₁) p e₁ hp2 he₁ hF₁
      obtain ⟨ζ₂, hζ₂, hζo₂⟩ := exists_torus_gen (F := F₂) p e₂ hp2 he₂ hF₂
      exact eq_top_of_coprime_elements hQ₁ hQ₂ (torus_not_mem_center hζ₁)
        (Nat.Coprime.coprime_dvd_left (orderOf_torus_dvd ζ₁) hζo₁) (torus_not_mem_center hζ₂)
        (Nat.Coprime.coprime_dvd_left (orderOf_torus_dvd ζ₂) hζo₂) N hall
    · intro E hE
      have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
      obtain ⟨k, hk⟩ := hEp.exists_card_eq
      rw [hk]
      by_contra hlt
      have hk4 : 4 ≤ k := by
        by_contra h
        push Not at h
        exact hlt (Nat.pow_le_pow_right hp.pos (by omega))
      exact hno E k hk4 hE hk

end CFSG.RankThree.PartOne.SRC
