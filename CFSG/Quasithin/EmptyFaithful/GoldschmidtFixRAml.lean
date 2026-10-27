module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRCoord
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtFixRMod3

public section

namespace CFSG.Quasithin.FixR

open CFSG.Quasithin CFSG.Quasithin.SBc16

variable {W : Type} [CommGroup W]

theorem card_le_four {R : Z52 →* MulAut W} (hR : Function.Injective R)
    {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A)
    (hAN : A ≤ Subgroup.normalizer (R.range : Set (MulAut W)))
    (hAf : ∀ a ∈ A, (∀ κ ∈ R.range, a * κ = κ * a) → a = 1) : Nat.card A ≤ 4 := by
  let φ : A →* Matrix (Fin 2) (Fin 2) (ZMod 5) := (cmHom R hR).comp (Subgroup.inclusion hAN)
  have hinj : Function.Injective φ := by
    intro a b hab
    have h1 : φ (a⁻¹ * b) = 1 := by
      rw [map_mul, ← hab, ← map_mul, inv_mul_cancel, map_one]
    have h2 := centralizes_of_cm_eq_one hR (γ := Subgroup.inclusion hAN (a⁻¹ * b)) h1
    have h3 : ((a⁻¹ * b : A) : MulAut W) = 1 :=
      hAf _ (a⁻¹ * b).2 (fun κ hκ => h2 κ hκ)
    have : a⁻¹ * b = 1 := Subtype.ext h3
    exact (inv_mul_eq_one.mp this)
  have hsq : ∀ a : A, a * a = 1 := fun a => Subtype.ext (by simpa [pow_two] using hA.2 a a.2)
  have hinv : ∀ a : A, φ a * φ a = 1 := fun a => by rw [← map_mul, hsq, map_one]
  have hcomm : ∀ a b : A, φ a * φ b = φ b * φ a := fun a b => by
    rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hA.1 a a.2 b b.2)
  by_cases hex : ∃ a : A, φ a ≠ 1 ∧ φ a ≠ -1
  · obtain ⟨a₀, h1, h2⟩ := hex
    let S : Finset (Matrix (Fin 2) (Fin 2) (ZMod 5)) := {1, -1, φ a₀, -φ a₀}
    have hS : ∀ b : A, φ b ∈ S := by
      intro b
      have := two_four (φ a₀) (hinv a₀) h1 h2 (φ b) (hinv b) (hcomm a₀ b)
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      tauto
    calc Nat.card A ≤ Nat.card ↥(S : Set (Matrix (Fin 2) (Fin 2) (ZMod 5))) :=
          Nat.card_le_card_of_injective (fun b => ⟨φ b, hS b⟩)
            (fun b b' h => hinj (congrArg Subtype.val h))
      _ = S.card := by simp
      _ ≤ 4 := Finset.card_le_four
  · push Not at hex
    let S : Finset (Matrix (Fin 2) (Fin 2) (ZMod 5)) := {1, -1}
    have hS : ∀ b : A, φ b ∈ S := by
      intro b
      simp only [S, Finset.mem_insert, Finset.mem_singleton]
      by_cases hb : φ b = 1
      · exact Or.inl hb
      · exact Or.inr (hex b hb)
    calc Nat.card A ≤ Nat.card ↥(S : Set (Matrix (Fin 2) (Fin 2) (ZMod 5))) :=
          Nat.card_le_card_of_injective (fun b => ⟨φ b, hS b⟩)
            (fun b b' h => hinj (congrArg Subtype.val h))
      _ = S.card := by simp
      _ ≤ 2 := Finset.card_le_two
      _ ≤ 4 := by norm_num

theorem map_ln_conj {R : Z52 →* MulAut W} (hR : Function.Injective R) {x : MulAut W}
    (hxN : x ∈ Subgroup.normalizer (R.range : Set (MulAut W))) (v : Vec) :
    (ln R v).map (MulAut.conj x).toMonoidHom = ln R ((cmHom R hR ⟨x, hxN⟩).mulVec v) := by
  rw [ln, MonoidHom.map_zpowers, ln]
  congr 1
  rw [← conj_Ru hR ⟨x, hxN⟩ v]
  simp [MulAut.conj_apply]

theorem tp_ln_conj_ne_bot {R : Z52 →* MulAut W} (hR : Function.Injective R) {x : MulAut W}
    (hxN : x ∈ Subgroup.normalizer (R.range : Set (MulAut W))) {v : Vec}
    (h : tp R.range (ln R v) ≠ ⊥) :
    tp R.range (ln R ((cmHom R hR ⟨x, hxN⟩).mulVec v)) ≠ ⊥ := by
  have key := map_tp R.range (ln R v) hxN
  rw [map_ln_conj hR hxN v] at key
  intro hbot
  rw [hbot] at key
  exact h ((Subgroup.map_eq_bot_iff_of_injective _ x.injective).mp key)

theorem aml_false [Finite W] (hW : ∀ w : W, w ^ 2 = 1) (R : Z52 →* MulAut W)
    (hR : Function.Injective R) {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) (hA0 : A ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (R.range : Set (MulAut W)))
    (hAf : ∀ a ∈ A, (∀ κ ∈ R.range, a * κ = κ * a) → a = 1)
    (hAr : Nat.card W ≤ Nat.card A ^ 2 * Nat.card (fixV A)) {x : MulAut W}
    (hxN : x ∈ Subgroup.normalizer (R.range : Set (MulAut W)))
    (hx5 : ∀ κ ∈ R.range, x ^ 5 * κ = κ * x ^ 5) (hx1 : ∃ κ ∈ R.range, x * κ ≠ κ * x) :
    False := by
  have : Fintype ↥R.range := Fintype.ofFinite _
  have hP : Fintype.card ↥R.range = 25 := by rw [← Nat.card_eq_fintype_card, card_range hR]
  have hPc : ∀ a ∈ R.range, ∀ b ∈ R.range, a * b = b * a := by
    rintro _ ⟨z, rfl⟩ _ ⟨z', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hP5 : ∀ κ ∈ R.range, κ ^ 5 = 1 := by
    rintro _ ⟨z, rfl⟩
    exact Ru_pow_five R (Multiplicative.toAdd z)
  set X := cmHom R hR ⟨x, hxN⟩ with hX
  have hX5 : X ^ 5 = 1 := by
    rw [hX, ← map_pow]
    apply cm_eq_one_of_centralizes hR
    intro κ hκ
    have e : (((⟨x, hxN⟩ : ↥(Subgroup.normalizer (R.range : Set (MulAut W)))) ^ 5 :
        ↥(Subgroup.normalizer (R.range : Set (MulAut W)))) : MulAut W) = x ^ 5 := rfl
    rw [e]
    exact hx5 κ hκ
  have hX1 : X ≠ 1 := by
    intro h
    obtain ⟨κ, hκ, hne⟩ := hx1
    exact hne (centralizes_of_cm_eq_one hR h κ hκ)
  obtain ⟨u₀, hu₀, hfix⟩ := exists_fixed_vec X hX5 hX1
  obtain ⟨u, hdet, htp⟩ := exists_part_ne_bot hW R hR hu₀
  obtain ⟨d01, d02, d03, d12, d13, d23⟩ := orbit_indep X hX5 hX1 u₀ hu₀ hfix u hdet
  have z0 : ∀ v : Vec, det2 0 v = 0 := fun v => by simp [det2]
  have z1 : ∀ v : Vec, det2 v 0 = 0 := fun v => by simp [det2]
  have hv0 : u ≠ 0 := fun h => d01 (h ▸ z0 _)
  have hv1 : X.mulVec u ≠ 0 := fun h => d01 (h ▸ z1 _)
  have hv2 : X.mulVec (X.mulVec u) ≠ 0 := fun h => d02 (h ▸ z1 _)
  have hv3 : X.mulVec (X.mulVec (X.mulVec u)) ≠ 0 := fun h => d03 (h ▸ z1 _)
  have t1 := tp_ln_conj_ne_bot hR hxN htp
  have t2 := tp_ln_conj_ne_bot hR hxN t1
  have t3 := tp_ln_conj_ne_bot hR hxN t2
  exact final_contra hW hPc hP hP5 hA hA0 hAN hAf (card_le_four hR hA hAN hAf) hAr
    (ln_le R u) (ln_le R _) (ln_le R _) (ln_le R _)
    (card_ln hR hv0) (card_ln hR hv1) (card_ln hR hv2) (card_ln hR hv3)
    (ln_ne hR d01) (ln_ne hR d02) (ln_ne hR d03) (ln_ne hR d12) (ln_ne hR d13) (ln_ne hR d23)
    htp t1 t2 t3

theorem exists_coord [Finite W] {P : Subgroup (MulAut W)}
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Nat.card P = 25)
    (hP5 : ∀ κ ∈ P, κ ^ 5 = 1) :
    ∃ R : Z52 →* MulAut W, Function.Injective R ∧ R.range = P := by
  let _ : CommGroup ↥P :=
    { (inferInstance : Group ↥P) with mul_comm := fun a b => Subtype.ext (hPc a a.2 b b.2) }
  have h5 : ∀ x : ↥P, x ^ 5 = 1 := fun x => Subtype.ext (hP5 x x.2)
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hnt : Nontrivial ↥P := Finite.one_lt_card_iff_nontrivial.mp (by rw [hP]; norm_num)
  obtain ⟨v₁, hv₁1⟩ := exists_ne (1 : ↥P)
  have ho₁ : orderOf v₁ = 5 := orderOf_eq_prime (h5 v₁) hv₁1
  have hc₁ : Nat.card (Subgroup.zpowers v₁) = 5 := by rw [Nat.card_zpowers, ho₁]
  have hne : Subgroup.zpowers v₁ ≠ ⊤ := fun h => by
    rw [h, Subgroup.card_top, hP] at hc₁
    omega
  obtain ⟨v₂, hv₂⟩ : ∃ v₂ : ↥P, v₂ ∉ Subgroup.zpowers v₁ := by
    by_contra hcon
    push Not at hcon
    exact hne ((Subgroup.eq_top_iff' _).mpr hcon)
  have hv₂1 : v₂ ≠ 1 := fun h => hv₂ (h ▸ Subgroup.one_mem _)
  have ho₂ : orderOf v₂ = 5 := orderOf_eq_prime (h5 v₂) hv₂1
  have hc₂ : Nat.card (Subgroup.zpowers v₂) = 5 := by rw [Nat.card_zpowers, ho₂]
  have hd : Subgroup.zpowers v₁ ⊓ Subgroup.zpowers v₂ = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers v₁ ⊓ Subgroup.zpowers v₂) ∣ 5 := by
      rw [← hc₂]
      exact Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hdvd with h1 | h5'
    · exact Subgroup.eq_bot_of_card_eq _ h1
    · exfalso
      have heq : Subgroup.zpowers v₁ ⊓ Subgroup.zpowers v₂ = Subgroup.zpowers v₂ :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h5', hc₂])
      have : v₂ ∈ Subgroup.zpowers v₁ ⊓ Subgroup.zpowers v₂ := by
        rw [heq]
        exact Subgroup.mem_zpowers v₂
      exact hv₂ this.1
  have hbij := coordHom_bijective (h5 := h5) hP hd
    (Subgroup.mem_zpowers v₁) ho₁ (Subgroup.mem_zpowers v₂) ho₂
  refine ⟨P.subtype.comp (coordHom h5 v₁ v₂), Subtype.val_injective.comp hbij.1, ?_⟩
  ext κ
  constructor
  · rintro ⟨z, rfl⟩
    exact (coordHom h5 v₁ v₂ z).2
  · intro hκ
    obtain ⟨z, hz⟩ := hbij.2 ⟨κ, hκ⟩
    exact ⟨z, congrArg Subtype.val hz⟩

theorem aml_false' [Finite W] (hW : ∀ w : W, w ^ 2 = 1) {P : Subgroup (MulAut W)}
    (hPc : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a) (hP : Nat.card P = 25) (hP5 : ∀ κ ∈ P, κ ^ 5 = 1)
    {A : Subgroup (MulAut W)} (hA : IsElemAbelian2 A) (hA0 : A ≠ ⊥)
    (hAN : A ≤ Subgroup.normalizer (P : Set (MulAut W)))
    (hAf : ∀ a ∈ A, (∀ κ ∈ P, a * κ = κ * a) → a = 1)
    (hAr : Nat.card W ≤ Nat.card A ^ 2 * Nat.card (fixV A)) {x : MulAut W}
    (hxN : x ∈ Subgroup.normalizer (P : Set (MulAut W)))
    (hx5 : ∀ κ ∈ P, x ^ 5 * κ = κ * x ^ 5) (hx1 : ∃ κ ∈ P, x * κ ≠ κ * x) : False := by
  obtain ⟨R, hR, hRP⟩ := exists_coord hPc hP hP5
  subst hRP
  exact aml_false hW R hR hA hA0 hAN hAf hAr hxN hx5 hx1

end CFSG.Quasithin.FixR
