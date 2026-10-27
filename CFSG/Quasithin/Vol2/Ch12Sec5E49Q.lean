module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma5E49

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin
open scoped commutatorElement

namespace S125E49

theorem sq_eq_one_entries : ∀ a b c d : ZMod 7, a * d - b * c = 1 → a * a + b * c = 1 →
    a * b + b * d = 0 → c * a + d * c = 0 → c * b + d * d = 1 →
      (a = 1 ∧ b = 0 ∧ c = 0 ∧ d = 1) ∨ (a = -1 ∧ b = 0 ∧ c = 0 ∧ d = -1) := by
  decide +kernel

theorem coe_eq_neg_one {g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)} (hg : g * g = 1)
    (hg1 : g ≠ 1) : (g : Matrix (Fin 2) (Fin 2) (ZMod 7)) = !![-1, 0; 0, -1] := by
  have hdet : (g : Matrix (Fin 2) (Fin 2) (ZMod 7)).det = 1 := g.2
  rw [Matrix.det_fin_two] at hdet
  have hm : (g : Matrix (Fin 2) (Fin 2) (ZMod 7)) * g = 1 := by
    have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) =>
      (x : Matrix (Fin 2) (Fin 2) (ZMod 7))) hg
    simpa using this
  have h00 := congrFun₂ hm 0 0
  have h01 := congrFun₂ hm 0 1
  have h10 := congrFun₂ hm 1 0
  have h11 := congrFun₂ hm 1 1
  simp only [Matrix.mul_apply, Fin.sum_univ_two, Matrix.one_apply_eq,
    Matrix.one_apply_ne (show (0 : Fin 2) ≠ 1 by decide),
    Matrix.one_apply_ne (show (1 : Fin 2) ≠ 0 by decide)] at h00 h01 h10 h11
  rcases sq_eq_one_entries _ _ _ _ hdet h00 h01 h10 h11 with ⟨ha, hb, hc, hd⟩ | ⟨ha, hb, hc, hd⟩
  · exfalso
    apply hg1
    apply Subtype.ext
    rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (ZMod 7)), ha, hb, hc, hd,
      Matrix.SpecialLinearGroup.coe_one, Matrix.one_fin_two]
  · rw [Matrix.eta_fin_two (g : Matrix (Fin 2) (Fin 2) (ZMod 7)), ha, hb, hc, hd]

theorem exists_involution :
    ∃ g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7), g * g = 1 ∧ g ≠ 1 := by
  refine ⟨⟨!![-1, 0; 0, -1], by rw [Matrix.det_fin_two_of]; decide⟩, Subtype.ext ?_, fun h => ?_⟩
  · show !![(-1 : ZMod 7), 0; 0, -1] * !![-1, 0; 0, -1] = 1
    decide
  · have := congrArg (fun x : Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) =>
      (x : Matrix (Fin 2) (Fin 2) (ZMod 7)) 0 0) h
    revert this
    decide

variable {Q : Type} [Group Q] {E A : Subgroup Q}

theorem exists_mul_of_sup [E.Normal] (hQ : A ⊔ E = ⊤) (q : Q) :
    ∃ a ∈ A, ∃ e ∈ E, q = a * e := by
  have h : q ∈ ((A ⊔ E : Subgroup Q) : Set Q) := by
    rw [hQ]
    exact Subgroup.mem_top q
  rw [Subgroup.mul_normal] at h
  obtain ⟨a, ha, e, he, hae⟩ := h
  exact ⟨a, ha, e, he, hae.symm⟩

theorem eq_of_inv_mul_mem (hAE : A ⊓ E = ⊥) {a b : Q} (ha : a ∈ A) (hb : b ∈ A)
    (h : a⁻¹ * b ∈ E) : a = b := by
  have : a⁻¹ * b ∈ A ⊓ E := ⟨A.mul_mem (A.inv_mem ha) hb, h⟩
  rw [hAE, Subgroup.mem_bot, inv_mul_eq_one] at this
  exact this

theorem eq_one_of_mul_self {e : Q} (h7 : e ^ 7 = 1) (h2 : e * e = 1) : e = 1 := by
  have : e = e ^ 7 * ((e * e)⁻¹) ^ 3 := by group
  rw [this, h7, h2]
  simp

theorem commutator_le_of_index_two {B : Subgroup Q} (h : B.index = 2) :
    ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ B := by
  rw [Subgroup.commutator_le]
  intro a _ b _
  rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two h,
    Subgroup.mul_mem_iff_of_index_two h, Subgroup.mul_mem_iff_of_index_two h,
    Subgroup.inv_mem_iff, Subgroup.inv_mem_iff]
  tauto

variable [Finite Q]

theorem sup_eq_top_of_card [E.Normal] (hAE : A ⊓ E = ⊥) (hA : Nat.card (Q ⧸ E) ≤ 2 * Nat.card A)
    (hQp : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) : A ⊔ E = ⊤ := by
  set μ := QuotientGroup.mk' E with hμ
  have hB : A ⊔ E = (A.map μ).comap μ := by
    rw [QuotientGroup.comap_map_mk', sup_comm]
  have hcard : Nat.card (A.map μ) = Nat.card A := by
    symm
    refine Nat.card_eq_of_bijective (fun a : ↥A => (⟨μ a, a, a.2, rfl⟩ : ↥(A.map μ))) ⟨?_, ?_⟩
    · intro a b hab
      have h := congrArg Subtype.val hab
      simp only [hμ, QuotientGroup.mk'_apply, QuotientGroup.eq] at h
      exact Subtype.ext (eq_of_inv_mul_mem hAE a.2 b.2 h)
    · rintro ⟨_, a, ha, rfl⟩
      exact ⟨⟨a, ha⟩, rfl⟩
  have hidx : (A ⊔ E).index ≤ 2 := by
    rw [hB, Subgroup.index_comap_of_surjective _ (QuotientGroup.mk'_surjective E)]
    have h := Subgroup.index_mul_card (A.map μ)
    rw [hcard] at h
    have hpos : 0 < Nat.card A := Nat.card_pos
    by_contra hlt
    have hlt' : 3 ≤ (A.map μ).index := by omega
    have : 3 * Nat.card A ≤ (A.map μ).index * Nat.card A := Nat.mul_le_mul_right _ hlt'
    omega
  have hne : (A ⊔ E).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases (show (A ⊔ E).index = 1 ∨ (A ⊔ E).index = 2 by omega) with h | h
  · exact Subgroup.index_eq_one.1 h
  · exact eq_top_iff.2 (hQp ▸ commutator_le_of_index_two h)

omit [Finite Q] in
theorem conj_mul_comm {x a b : Q} (ha : a * x * a⁻¹ ∈ Subgroup.zpowers x)
    (hb : b * x * b⁻¹ ∈ Subgroup.zpowers x) :
    (a * b) * x * (a * b)⁻¹ = (b * a) * x * (b * a)⁻¹ := by
  obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 ha
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hb
  have h1 : (a * b) * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
  have h2 : (b * a) * x * (b * a)⁻¹ = b * (a * x * a⁻¹) * b⁻¹ := by group
  rw [h1, h2, ← hi, ← hj, ← conj_zpow, ← conj_zpow, ← hi, ← hj, ← zpow_mul, ← zpow_mul,
    mul_comm]

omit [Finite Q] in
theorem mem_center_of_perfect {x : Q} (hx : ∀ q : Q, q * x * q⁻¹ ∈ Subgroup.zpowers x)
    (hQp : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) : x ∈ Subgroup.center Q := by
  have hle : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ ≤ Subgroup.centralizer {x} := by
    rw [Subgroup.commutator_le]
    intro g₁ _ g₂ _
    have h := conj_mul_comm (hx g₁⁻¹) (hx g₂⁻¹)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have e1 : ⁅g₁, g₂⁆ = (g₂⁻¹ * g₁⁻¹)⁻¹ * (g₁⁻¹ * g₂⁻¹) := by
      rw [commutatorElement_def]
      group
    rw [e1]
    refine (calc x * ((g₂⁻¹ * g₁⁻¹)⁻¹ * (g₁⁻¹ * g₂⁻¹))
        = (g₂⁻¹ * g₁⁻¹)⁻¹ * ((g₂⁻¹ * g₁⁻¹) * x * (g₂⁻¹ * g₁⁻¹)⁻¹) * (g₁⁻¹ * g₂⁻¹) := by group
      _ = (g₂⁻¹ * g₁⁻¹)⁻¹ * ((g₁⁻¹ * g₂⁻¹) * x * (g₁⁻¹ * g₂⁻¹)⁻¹) * (g₁⁻¹ * g₂⁻¹) := by rw [h]
      _ = (g₂⁻¹ * g₁⁻¹)⁻¹ * (g₁⁻¹ * g₂⁻¹) * x := by group).symm
  rw [hQp] at hle
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))

theorem exists_central_involution [hEn : E.Normal] (hE : IsElemAbelian 7 E)
    (hEc : Nat.card E = 49) (hcent : Subgroup.centralizer (E : Set Q) = E)
    (f : Q ⧸ E ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7)) (hAE : A ⊓ E = ⊥)
    (hQ : A ⊔ E = ⊤) (hQp : ⁅(⊤ : Subgroup Q), (⊤ : Subgroup Q)⁆ = ⊤) :
    ∃ z ∈ A, z ≠ 1 ∧ z * z = 1 ∧ (∀ a ∈ A, a * z = z * a) ∧
      (∀ e ∈ E, z * e * z⁻¹ = e⁻¹) ∧ ∀ w ∈ A, w * w = 1 → w ≠ 1 → w = z := by
  have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  set φ : Q →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 7) :=
    f.toMonoidHom.comp (QuotientGroup.mk' E) with hφ
  have hφE : ∀ q, φ q = 1 ↔ q ∈ E := by
    intro q
    rw [hφ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hinj : ∀ a ∈ A, ∀ b ∈ A, φ a = φ b → a = b := by
    intro a ha b hb h
    refine eq_of_inv_mul_mem hAE ha hb ((hφE _).1 ?_)
    rw [map_mul, map_inv, h, inv_mul_cancel]
  obtain ⟨g, hg2, hg1⟩ := exists_involution
  obtain ⟨q, hq⟩ := QuotientGroup.mk_surjective (f.symm g)
  obtain ⟨z, hzA, e, he, hqz⟩ := exists_mul_of_sup hQ q
  have hφz : φ z = g := by
    have h1 : (z : Q ⧸ E) = (q : Q ⧸ E) := by
      rw [hqz, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff e).2 he, mul_one]
    change f (z : Q ⧸ E) = g
    rw [h1, hq, MulEquiv.apply_symm_apply]
  have hz1 : z ≠ 1 := by
    rintro rfl
    rw [map_one] at hφz
    exact hg1 hφz.symm
  have hz2 : z * z = 1 := by
    have h : φ (z * z) = φ 1 := by rw [map_mul, hφz, hg2, map_one]
    exact hinj _ (A.mul_mem hzA hzA) _ A.one_mem h
  have huniq : ∀ w ∈ A, w * w = 1 → w ≠ 1 → w = z := by
    intro w hwA hw2 hw1
    have hφw1 : φ w ≠ 1 := fun h => hw1 (hinj _ hwA _ A.one_mem (by rw [h, map_one]))
    have hφw2 : φ w * φ w = 1 := by rw [← map_mul, hw2, map_one]
    refine hinj _ hwA _ hzA (Subtype.ext ?_)
    rw [coe_eq_neg_one hφw2 hφw1, hφz, coe_eq_neg_one hg2 hg1]
  have hcen : ∀ a ∈ A, a * z = z * a := by
    intro a ha
    have h := huniq (a * z * a⁻¹) (A.mul_mem (A.mul_mem ha hzA) (A.inv_mem ha))
      (by rw [show a * z * a⁻¹ * (a * z * a⁻¹) = a * (z * z) * a⁻¹ by group, hz2]; group)
      (fun h1 => hz1 (by rw [mul_inv_eq_one, mul_eq_left] at h1; exact h1))
    calc a * z = a * z * a⁻¹ * a := by group
      _ = z * a := by rw [h]
  set Ep := E ⊓ Subgroup.centralizer {z} with hEp
  have hEpn : Ep.Normal := by
    refine ⟨fun x hx q => ?_⟩
    obtain ⟨a, ha, e', he', rfl⟩ := exists_mul_of_sup hQ q
    obtain ⟨hxE, hxz⟩ := Subgroup.mem_inf.1 hx
    rw [Subgroup.mem_centralizer_singleton_iff] at hxz
    have hex : e' * x * e'⁻¹ = x := by
      rw [hcomm e' he' x hxE]
      group
    have hconj : a * e' * x * (a * e')⁻¹ = a * x * a⁻¹ := by
      rw [show a * e' * x * (a * e')⁻¹ = a * (e' * x * e'⁻¹) * a⁻¹ by group, hex]
    rw [hconj]
    refine Subgroup.mem_inf.2 ⟨hEn.conj_mem x hxE a, ?_⟩
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hza := hcen a ha
    refine (calc z * (a * x * a⁻¹) = (z * a) * x * a⁻¹ := by group
      _ = a * (z * x) * a⁻¹ := by rw [← hza]; group
      _ = a * (x * z) * a⁻¹ := by rw [← hxz]
      _ = a * x * (z * a⁻¹) := by group
      _ = a * x * a⁻¹ * z := by
        have : z * a⁻¹ = a⁻¹ * z := by
          calc z * a⁻¹ = a⁻¹ * (a * z) * a⁻¹ := by group
            _ = a⁻¹ * (z * a) * a⁻¹ := by rw [hza]
            _ = a⁻¹ * z := by group
        rw [this]
        group).symm
  have hEpb : Ep = ⊥ := by
    by_contra hne
    obtain ⟨e₁, he₁1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
    have he₁E : (e₁ : Q) ∈ E := (Subgroup.mem_inf.1 e₁.2).1
    have he₁ne : (e₁ : Q) ≠ 1 := fun h => he₁1 (Subtype.ext h)
    have h7p : Nat.Prime 7 := by norm_num
    have hdvd : Nat.card Ep ∣ 7 ^ 2 := by
      rw [show (7 : ℕ) ^ 2 = 49 by norm_num, ← hEc]
      exact Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow h7p).1 hdvd
    interval_cases k
    ·
      rw [pow_zero] at hk'
      exact hne (Subgroup.card_eq_one.1 hk')
    ·
      have : Fact (Nat.Prime 7) := ⟨h7p⟩
      have hord : orderOf (e₁ : Q) = 7 := orderOf_eq_prime (hE.2 _ he₁E) he₁ne
      have hz : Subgroup.zpowers (e₁ : Q) = Ep := by
        refine Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 e₁.2) ?_
        rw [Nat.card_zpowers, hord, hk', pow_one]
      have hc : (e₁ : Q) ∈ Subgroup.center Q := by
        refine mem_center_of_perfect (fun q => ?_) hQp
        rw [hz]
        exact hEpn.conj_mem _ e₁.2 q
      have hb := IsSL27OverE49.center_eq_bot ⟨E, hE, hEc, hcent, hEn, ⟨f⟩⟩
      rw [hb, Subgroup.mem_bot] at hc
      exact he₁ne hc
    ·
      have hEq : Ep = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk', hEc]; norm_num)
      have hzE : z ∈ E := by
        rw [← hcent, Subgroup.mem_centralizer_iff]
        intro e he
        have h := (Subgroup.mem_inf.1 (hEq ▸ he : e ∈ Ep)).2
        rw [Subgroup.mem_centralizer_singleton_iff] at h
        exact h
      have : z ∈ A ⊓ E := ⟨hzA, hzE⟩
      rw [hAE, Subgroup.mem_bot] at this
      exact hz1 this
  have hinv : ∀ e ∈ E, z * e * z⁻¹ = e⁻¹ := by
    intro e he
    have hze : z * e * z⁻¹ ∈ E := hEn.conj_mem e he z
    have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hz2
    have hw : e * (z * e * z⁻¹) ∈ Ep := by
      refine Subgroup.mem_inf.2 ⟨E.mul_mem he hze, ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine (calc z * (e * (z * e * z⁻¹)) = (z * e * z⁻¹) * (z * z) * e * z⁻¹ := by group
        _ = (z * e * z⁻¹) * e * z⁻¹ := by rw [hz2, mul_one]
        _ = e * (z * e * z⁻¹) * z⁻¹ := by rw [hcomm _ hze e he]
        _ = e * (z * e * z⁻¹) * z := by rw [hzinv]).symm
    rw [hEpb, Subgroup.mem_bot] at hw
    exact (eq_inv_of_mul_eq_one_right hw)
  exact ⟨z, hzA, hz1, hz2, hcen, hinv, huniq⟩

theorem eq_of_mem_normalizer [E.Normal] (h7 : ∀ e ∈ E, e ^ 7 = 1) (hAE : A ⊓ E = ⊥)
    (hQ : A ⊔ E = ⊤) {z : Q} (hzc : ∀ a ∈ A, a * z = z * a)
    (hzi : ∀ e ∈ E, z * e * z⁻¹ = e⁻¹) {X : Subgroup Q} (hXE : X ⊓ E = ⊥)
    (hcard : Nat.card X = Nat.card A) (hzX : z ∈ Subgroup.normalizer (X : Set Q)) : X = A := by
  set μ := QuotientGroup.mk' E with hμ
  have hinj : ∀ {B : Subgroup Q}, B ⊓ E = ⊥ → Function.Injective (fun b : ↥B => μ b) := by
    intro B hBE a b hab
    simp only [hμ, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
    exact Subtype.ext (eq_of_inv_mul_mem hBE a.2 b.2 hab)
  have hAs : Function.Surjective (fun a : ↥A => μ a) := by
    intro q
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective E q
    obtain ⟨a, ha, e, he, rfl⟩ := exists_mul_of_sup hQ q
    refine ⟨⟨a, ha⟩, ?_⟩
    simp only [hμ, QuotientGroup.mk'_apply, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff e).2 he, mul_one]
  have hcA : Nat.card A = Nat.card (Q ⧸ E) := Nat.card_eq_of_bijective _ ⟨hinj hAE, hAs⟩
  have hXs : Function.Surjective (fun x : ↥X => μ x) :=
    ((hinj hXE).bijective_of_nat_card_le (by rw [hcard, hcA])).2
  have hAX : A ≤ X := by
    intro l hl
    obtain ⟨x, hx⟩ := hXs (μ l)
    simp only [hμ, QuotientGroup.mk'_apply, QuotientGroup.eq] at hx
    set e := (x : Q)⁻¹ * l with he
    have hle : l = x * e := by rw [he]; group
    have hzx : z * x * z⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hzX x).mp x.2
    have hee : e * e ∈ X ⊓ E := by
      refine ⟨?_, E.mul_mem hx hx⟩
      have h1 : z * l * z⁻¹ = l := by rw [← hzc l hl]; group
      have h2 : z * l * z⁻¹ = (z * x * z⁻¹) * e⁻¹ := by
        rw [hle, show z * (↑x * e) * z⁻¹ = (z * x * z⁻¹) * (z * e * z⁻¹) by group,
          hzi e hx]
      have h3 : e * e = (x : Q)⁻¹ * (z * x * z⁻¹) := by
        have h4 : (x : Q) * e = (z * x * z⁻¹) * e⁻¹ := by rw [← hle, ← h1, h2]
        calc e * e = (x : Q)⁻¹ * ((x : Q) * e) * e := by group
          _ = (x : Q)⁻¹ * ((z * x * z⁻¹) * e⁻¹) * e := by rw [h4]
          _ = (x : Q)⁻¹ * (z * x * z⁻¹) := by group
      rw [h3]
      exact X.mul_mem (X.inv_mem x.2) hzx
    rw [hXE, Subgroup.mem_bot] at hee
    have he1 : e = 1 := eq_one_of_mul_self (h7 e hx) hee
    rw [hle, he1, mul_one]
    exact x.2
  exact (Subgroup.eq_of_le_of_card_ge hAX hcard.le).symm

end S125E49

end CFSG.Quasithin.H13
