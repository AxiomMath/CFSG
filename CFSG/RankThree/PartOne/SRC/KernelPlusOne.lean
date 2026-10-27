module

public import CFSG.RankThree.PartOne.SRC.ProductCover

public section

namespace CFSG.RankThree.PartOne.SRC

open Matrix CFSG.SL2MinimalFaithful Subgroup

theorem hbig_SL2 {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ e) (hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F)) :
    ∀ K₁ : Subgroup (SpecialLinearGroup (Fin 2) F), K₁.Normal → ∀ n : ℕ, n ≤ 3 →
      Nat.card (SpecialLinearGroup (Fin 2) F) ∣
        Nat.card K₁ * Nat.card (Matrix.GeneralLinearGroup (Fin n) (ZMod p)) → K₁ = ⊤ := by
  intro K₁ hK₁ n hn hdvd
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hK₁ with htop | hle
  · exact htop
  · exfalso
    obtain ⟨m, hm2, hm, hmg⟩ := bigAt_of_card hp2 he hF
    obtain ⟨k, hk⟩ := card_center_SL2_eq_two_pow F
    have hK₁c : Nat.card K₁ ∣ 2 ^ k := hk ▸ Subgroup.card_dvd_of_le hle
    have hcop : Nat.Coprime m (Nat.card K₁) :=
      Nat.Coprime.coprime_dvd_right hK₁c (Nat.Coprime.pow_right k hm2)
    exact hmg n hn (hcop.dvd_of_dvd_mul_left (hm.trans hdvd))

theorem hgen_SL2 {p e : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (he : 2 ≤ e) {F : Type} [Field F]
    [Finite F] (hF : Nat.card F = p ^ e) (hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F)) :
    ∀ N : Subgroup (SpecialLinearGroup (Fin 2) F), N.Normal →
      (∀ h : SpecialLinearGroup (Fin 2) F, Nat.Coprime (orderOf h) p → h ∈ N) → N = ⊤ := by
  intro N hN hall
  obtain ⟨ζ, hζ, hζo⟩ := exists_torus_gen (F := F) p e hp2 he hF
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hQ hN with htop | hle
  · exact htop
  · exact absurd (hle (hall (torus ζ) (Nat.Coprime.coprime_dvd_left (orderOf_torus_dvd ζ) hζo)))
      (torus_not_mem_center hζ)


theorem exists_elementaryAbelian_of_nontrivial_kernel_SL2 {p e : ℕ} [Fact p.Prime] {F : Type}
    [Field F] [Finite F] [CharP F p] (hF : Nat.card F = p ^ e) (hp2 : p ≠ 2) (he : 3 ≤ e)
    {A : Type} [Group A] [Finite A] (ρ : A →* SpecialLinearGroup (Fin 2) F)
    (hρ : Function.Surjective ρ) (hker : IsPGroup p ρ.ker) (hK : ρ.ker ≠ ⊥) :
    ∃ (E : Subgroup A) (k : ℕ), 4 ≤ k ∧ IsElementaryAbelian p E ∧ Nat.card E = p ^ k := by
  classical
  have hp : p.Prime := Fact.out
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have hF27 : 27 ≤ p ^ e := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he
      _ ≤ p ^ e := Nat.pow_le_pow_left hp3 e
  have hQ : CFSG.IsQuasisimple (SpecialLinearGroup (Fin 2) F) :=
    specialLinear_quasisimple_of_card (by omega)
  by_contra hno
  push Not at hno
  have hrank : ∀ E : Subgroup A, IsElementaryAbelian p E → Nat.card E ≤ p ^ 3 := by
    intro E hE
    have hEp : IsPGroup p E := IsElementaryAbelian.isPGroup p E
    obtain ⟨k, hk⟩ := hEp.exists_card_eq
    rw [hk]
    by_contra hlt
    have hk4 : 4 ≤ k := by
      by_contra h
      push Not at h
      exact hlt (Nat.pow_le_pow_right hp.pos (by omega))
    exact hno E k hk4 hE hk
  obtain ⟨A₀, -, hA₀min⟩ := Finite.exists_le_minimal (p := fun K : Subgroup A => K.map ρ = ⊤)
    (a := ⊤) (by rw [Subgroup.map_top_of_surjective ρ hρ])
  set ρ₀ : A₀ →* SpecialLinearGroup (Fin 2) F := ρ.comp A₀.subtype with hρ₀
  have hρ₀s : Function.Surjective ρ₀ := by
    intro x
    have hx : x ∈ A₀.map ρ := by
      rw [hA₀min.prop]
      exact mem_top x
    obtain ⟨k, hk, rfl⟩ := hx
    exact ⟨⟨k, hk⟩, rfl⟩
  have hmin₀ : ∀ M : Subgroup A₀, M.map ρ₀ = ⊤ → M = ⊤ := by
    intro M hM
    have h1 : (M.map A₀.subtype).map ρ = ⊤ := by
      rw [Subgroup.map_map]
      exact hM
    have h2 := hA₀min.le_of_le h1 (Subgroup.map_subtype_le M)
    rw [eq_top_iff]
    intro y _
    obtain ⟨y', hy', hyy⟩ := h2 y.2
    rwa [show y' = y from Subtype.ext hyy] at hy'
  have hker₀ : IsPGroup p ρ₀.ker := by
    intro x
    have hx1 : ρ ((x : A₀) : A) = 1 := MonoidHom.mem_ker.mp x.2
    obtain ⟨k, hk⟩ := hker ⟨((x : A₀) : A), hx1⟩
    exact ⟨k, Subtype.ext (Subtype.ext (by simpa using congrArg (fun z : ρ.ker => (z : A)) hk))⟩
  have hperf : Group.IsPerfect A₀ := by
    rw [Group.isPerfect_def]
    apply hmin₀
    have h1 := hQ.1.commutator_eq_top
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ hρ₀s]
    rwa [_root_.commutator_def] at h1
  have hrank₀ : ∀ E : Subgroup A₀, IsElementaryAbelian p E → Nat.card E ≤ p ^ 3 := by
    intro E hE
    have hEel : IsElementaryAbelian p (E.map A₀.subtype) :=
      isElementaryAbelian_map' A₀.subtype hE
    have := hrank _ hEel
    rwa [Subgroup.card_map_of_injective A₀.subtype_injective] at this
  have hcen : ρ₀.ker ≤ center A₀ :=
    central_of_rank_le_three_gen hp hp2 ρ₀ hρ₀s hker₀ hmin₀
      (hbig_SL2 hp2 (by omega) hF hQ) (hgen_SL2 hp2 (by omega) hF hQ) hrank₀
  obtain ⟨σ, hσ⟩ := CFSG.LieType.Steinberg.CentralExt.SL2Closed.sl2_exists_section_of_central
    (k := F) (by omega) (by omega) hρ₀s hcen
  let τ : Multiplicative F →* A := A₀.subtype.comp (σ.comp unipotentHom)
  have hρτ : ∀ a, ρ (τ a) = unipotentHom a := by
    intro a
    change ρ₀ (σ (unipotentHom a)) = _
    exact hσ _
  have hτinj : Function.Injective τ := by
    intro a b h
    apply unipotentHom_injective
    rw [← hρτ, ← hρτ, h]
  have hpow : ∀ a : Multiplicative F, a ^ p = 1 := by
    intro a
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  set E₁ : Subgroup A := τ.range with hE₁
  have hE₁el : IsElementaryAbelian p E₁ := isElementaryAbelian_range τ hpow
  have hE₁p : IsPGroup p E₁ := IsElementaryAbelian.isPGroup p E₁
  have hE₁card : Nat.card E₁ = p ^ e := by
    rw [hE₁, ← Nat.card_congr (MonoidHom.ofInjective hτinj).toEquiv, ← hF]
    exact Nat.card_congr Multiplicative.toAdd
  have hE₁K : ∀ g ∈ E₁, g ∈ ρ.ker → g = 1 := by
    rintro g ⟨a, rfl⟩ hg
    have h1 : unipotentHom a = 1 := by
      rw [← hρτ]
      exact MonoidHom.mem_ker.mp hg
    have : a = 1 := unipotentHom_injective (h1.trans (map_one unipotentHom).symm)
    rw [this, map_one]
  let ψ : E₁ →* Equiv.Perm ρ.ker :=
    (MulAut.toPerm ρ.ker).comp ((MulAut.conjNormal (H := ρ.ker)).comp E₁.subtype)
  let _inst : MulAction E₁ ρ.ker := MulAction.compHom _ ψ
  have h1fix : (1 : ρ.ker) ∈ MulAction.fixedPoints E₁ ρ.ker := fun g => by
    show MulAut.conjNormal (g : A) (1 : ρ.ker) = 1
    exact map_one _
  have hpK : p ∣ Nat.card ρ.ker := by
    rcases hker.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hK
    · exact h
  obtain ⟨b, hb, hne⟩ := hE₁p.exists_fixed_point_of_prime_dvd_card_of_fixed_point ρ.ker hpK h1fix
  have hb1 : b ≠ 1 := fun h => hne h.symm
  have hbfix : ∀ g ∈ E₁, g * (b : A) * g⁻¹ = (b : A) := by
    intro g hg
    have := hb ⟨g, hg⟩
    exact congrArg Subtype.val this
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hker) b
  have hk1 : 1 ≤ k := by
    by_contra h
    have h0 : k = 0 := by omega
    rw [h0, pow_zero, orderOf_eq_one_iff] at hk
    exact hb1 hk
  set z' : ρ.ker := b ^ (p ^ (k - 1)) with hz'
  have hz'ord : orderOf z' = p := by
    have hdvd : p ^ (k - 1) ∣ orderOf b := by rw [hk]; exact pow_dvd_pow p (Nat.sub_le k 1)
    rw [hz', orderOf_pow_of_dvd (pow_ne_zero _ hp.ne_zero) hdvd, hk,
      Nat.pow_div (Nat.sub_le k 1) hp.pos]
    have h1 : k - (k - 1) = 1 := by omega
    rw [h1, pow_one]
  set z : A := (z' : A) with hz
  have hzK : z ∈ ρ.ker := z'.2
  have hz_pow : z ^ p = 1 := by
    have := pow_orderOf_eq_one z'
    rw [hz'ord] at this
    exact congrArg Subtype.val this
  have hz1 : z ≠ 1 := by
    intro h
    have : z' = 1 := Subtype.ext h
    rw [this, orderOf_one] at hz'ord
    exact hp.one_lt.ne hz'ord
  have hz_fix : ∀ g ∈ E₁, g * z * g⁻¹ = z := by
    intro g hg
    have h1 := hbfix g hg
    have h2 : z = (b : A) ^ (p ^ (k - 1)) := rfl
    rw [h2, ← conj_pow, h1]
  have hcomm : ∀ g ∈ E₁, g * z = z * g := fun g hg => by
    have := hz_fix g hg
    calc g * z = g * z * g⁻¹ * g := by group
      _ = z * g := by rw [this]
  have hzE₁ : z ∉ E₁ := fun h => hz1 (hE₁K z h hzK)
  have hC : IsElementaryAbelian p (Subgroup.zpowers z) :=
    IsElementaryAbelian.zpowers_of_pow_eq_one hz_pow
  have hCE : Subgroup.zpowers z ≤ Subgroup.centralizer (E₁ : Set A) := by
    rintro y ⟨m, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    exact (Commute.zpow_right (show Commute g z from hcomm g hg) m).eq
  have hEel : IsElementaryAbelian p ↥(E₁ ⊔ Subgroup.zpowers z : Subgroup A) :=
    IsElementaryAbelian.sup_of_le_centralizer (E := E₁) (C := Subgroup.zpowers z) hCE
  obtain ⟨k', hk'⟩ := (IsElementaryAbelian.isPGroup p _ : IsPGroup p ↥(E₁ ⊔ Subgroup.zpowers z :
    Subgroup A)).exists_card_eq
  have hle : E₁ ≤ E₁ ⊔ Subgroup.zpowers z := le_sup_left
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [hE₁card, hk'] at hdvd
  have hek : e ≤ k' := (Nat.pow_dvd_pow_iff_le_right hp.one_lt).mp hdvd
  have hne : e ≠ k' := by
    intro h
    have hcard : Nat.card (E₁ ⊔ Subgroup.zpowers z : Subgroup A) ≤ Nat.card E₁ := by
      rw [hE₁card, hk', ← h]
    have heq := Subgroup.eq_of_le_of_card_ge hle hcard
    exact hzE₁ (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers z))
  exact hno _ k' (by omega) hEel hk'

end CFSG.RankThree.PartOne.SRC
