module

public import CFSG.RankThree.PartTwo.Sec18.Item187F4GL25

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.Quasithin.SBc16 (GL25)
open scoped commutatorElement Pointwise

private theorem q8_sq : ∀ u : QuaternionGroup 2, u * u = 1 ∨ u * u = QuaternionGroup.a 2 := by
  decide

private theorem q8_comm : ∀ u v : QuaternionGroup 2, u * u = QuaternionGroup.a 2 →
    v * v = QuaternionGroup.a 2 → u * v = v * u → v = u ∨ v = QuaternionGroup.a 2 * u := by
  decide

private theorem q8_prod : ∀ u v : QuaternionGroup 2, u * u = QuaternionGroup.a 2 →
    v * v = QuaternionGroup.a 2 → v ≠ u → v ≠ QuaternionGroup.a 2 * u →
    (u * v) * (u * v) = QuaternionGroup.a 2 := by
  decide

private theorem q8_comm_ex : ∃ u v : QuaternionGroup 2,
    u * v * u⁻¹ * v⁻¹ = QuaternionGroup.a 2 := by
  decide

private abbrev M2 : Type := Matrix (Fin 2) (Fin 2) (ZMod 5)

private theorem m2_sq_one : ∀ M : M2, M.det = 1 → M * M = 1 → M = 1 ∨ M = -1 := by
  decide +kernel

private theorem m2_key : ∀ g : M2, g ^ 3 = 1 → g ≠ 1 →
    ∀ q : M2, q * q = -1 → q.det = 1 → q * g ≠ g * q := by
  decide +kernel

private theorem zmod5_sq_neg_one : ∀ a b : ZMod 5, a * a = -1 → b * b = -1 → b = a ∨ b = -a := by
  decide

private theorem zmod5_sq_one : ∀ a : ZMod 5, a * a = 1 → a = 1 ∨ a = -1 := by
  decide

private def scU (a : (ZMod 5)ˣ) : GL25 :=
  Units.map (Matrix.scalar (Fin 2) : ZMod 5 →+* M2).toMonoidHom a

private theorem scU_val (a : (ZMod 5)ˣ) :
    ((scU a : GL25) : M2) = Matrix.scalar (Fin 2) (a : ZMod 5) := rfl

private theorem scU_one : scU 1 = 1 := Units.ext (by simp [scU_val])

private theorem scU_mul (a b : (ZMod 5)ˣ) : scU (a * b) = scU a * scU b :=
  Units.ext (by simp [scU_val])

private theorem scU_neg : scU (-1) = -1 := Units.ext (by
  rw [scU_val]
  exact (map_neg (Matrix.scalar (Fin 2) : ZMod 5 →+* M2) 1).trans (congrArg _ (map_one _)))

private theorem scU_eq_neg {a b : (ZMod 5)ˣ} (h : (b : ZMod 5) = -(a : ZMod 5)) :
    scU b = -scU a := by
  apply Units.ext
  rw [scU_val, Units.val_neg, scU_val, h]
  exact map_neg (Matrix.scalar (Fin 2) : ZMod 5 →+* M2) (a : ZMod 5)

private theorem scU_inj {a b : (ZMod 5)ˣ} (h : scU a = scU b) : a = b := by
  apply Units.ext
  have h' := congrArg (fun x : GL25 => (x : M2)) h
  simp only [scU_val] at h'
  exact Matrix.scalar_inj.1 h'

private theorem scU_central (x : GL25) (a : (ZMod 5)ˣ) : x * scU a = scU a * x := by
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, scU_val]
  exact (Matrix.scalar_commute _ (fun r => Commute.all _ _) _).eq.symm

private theorem scU_sq {a : (ZMod 5)ˣ} (ha : (a : ZMod 5) * a = -1) : scU a * scU a = -1 := by
  have h : a * a = -1 := Units.ext ha
  rw [← scU_mul, h, scU_neg]

private theorem mul_scU_mul (q q' : GL25) (a : (ZMod 5)ˣ) :
    (q * scU a) * (q' * scU a) = (q * q') * (scU a * scU a) := by
  calc (q * scU a) * (q' * scU a) = q * (scU a * q') * scU a := by group
    _ = q * (q' * scU a) * scU a := by rw [← scU_central q' a]
    _ = (q * q') * (scU a * scU a) := by group

private theorem conj_scU (g q : GL25) (a : (ZMod 5)ˣ) :
    g * (q * scU a) * g⁻¹ = (g * q * g⁻¹) * scU a := by
  calc g * (q * scU a) * g⁻¹ = g * q * (scU a * g⁻¹) := by group
    _ = g * q * (g⁻¹ * scU a) := by rw [← scU_central g⁻¹ a]
    _ = (g * q * g⁻¹) * scU a := by group

private theorem sl_det {x : GL25} (hx : x ∈ SL25) : (x : M2).det = 1 := by
  have h := mem_SL25.1 hx
  rw [← Matrix.GeneralLinearGroup.val_det_apply, h, Units.val_one]

private theorem sq_one_SL {x : GL25} (hx : x ∈ SL25) (h2 : x * x = 1) : x = 1 ∨ x = -1 := by
  have hM : (x : M2) * (x : M2) = 1 := by rw [← Units.val_mul, h2, Units.val_one]
  rcases m2_sq_one _ (sl_det hx) hM with h | h
  · exact Or.inl (Units.ext (by rw [h, Units.val_one]))
  · exact Or.inr (Units.ext h)

private theorem neg_one_ne_one' : (-1 : GL25) ≠ 1 := by
  intro h
  have h' := congrArg (fun x : GL25 => (x : M2) 0 0) h
  revert h'
  decide

private theorem gl_key {g q : GL25} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hq : q * q = -1)
    (hqS : q ∈ SL25) : ¬ (q * g = g * q) := by
  intro h
  have hg3M : (g : M2) ^ 3 = 1 := by
    have := congrArg Units.val hg3
    rwa [Units.val_pow_eq_pow_val, Units.val_one] at this
  have hg1M : (g : M2) ≠ 1 := fun h' => hg1 (Units.ext (by rw [h', Units.val_one]))
  have hqM : (q : M2) * (q : M2) = -1 := congrArg Units.val hq
  have hcM : (q : M2) * (g : M2) = (g : M2) * (q : M2) := by
    have := congrArg Units.val h
    rwa [Units.val_mul, Units.val_mul] at this
  exact m2_key (g : M2) hg3M hg1M (q : M2) hqM (sl_det hqS) hcM

private theorem gl_conj_ne {g q : GL25} (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hq : q * q = -1)
    (hqS : q ∈ SL25) : g * q * g⁻¹ ≠ q ∧ g * q * g⁻¹ ≠ -q := by
  constructor
  · intro h
    exact gl_key hg3 hg1 hq hqS (mul_inv_eq_iff_eq_mul.1 h).symm
  · intro h
    have hg2 : (g ^ 2) ^ 3 = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hg3, one_pow]
    have hg2' : g ^ 2 ≠ 1 := by
      intro h2
      have h1 : g ^ Nat.gcd 2 3 = 1 := pow_gcd_eq_one.2 ⟨h2, hg3⟩
      exact hg1 (by simpa using h1)
    have hcomm : g ^ 2 * q * (g ^ 2)⁻¹ = q := by
      have e : g ^ 2 * q * (g ^ 2)⁻¹ = g * (g * q * g⁻¹) * g⁻¹ := by
        rw [pow_two]; group
      rw [e, h, mul_neg, neg_mul, h, neg_neg]
    exact gl_key hg2 hg2' hq hqS (mul_inv_eq_iff_eq_mul.1 hcomm).symm

private theorem conj_sq (g q : GL25) (hqq : q * q = -1) :
    (g * q * g⁻¹) * (g * q * g⁻¹) = -1 := by
  calc (g * q * g⁻¹) * (g * q * g⁻¹) = g * (q * q) * g⁻¹ := by group
    _ = -1 := by rw [hqq, mul_neg_one, neg_mul, mul_inv_cancel]

private theorem neg_one_mem_iso {Q : Subgroup GL25} (hQ : Q ≤ SL25)
    (ψ : ↥Q ≃* QuaternionGroup 2) :
    ∃ hm : (-1 : GL25) ∈ Q, ψ ⟨-1, hm⟩ = QuaternionGroup.a 2 := by
  have hψu : ψ (ψ.symm (QuaternionGroup.a 2)) = QuaternionGroup.a 2 := ψ.apply_symm_apply _
  set u : ↥Q := ψ.symm (QuaternionGroup.a 2) with hu_def
  have hu2 : (u : GL25) * u = 1 := by
    have h : ψ (u * u) = ψ 1 := by
      rw [map_mul, hψu, map_one]
      decide
    have h' : u * u = 1 := ψ.injective h
    simpa using congrArg Subtype.val h'
  have hu1 : (u : GL25) ≠ 1 := by
    intro h
    have hu : u = 1 := Subtype.ext h
    have h' : ψ u = 1 := by rw [hu, map_one]
    rw [hψu] at h'
    exact absurd h' (by decide)
  have hu3 : (u : GL25) = -1 := (sq_one_SL (hQ u.2) hu2).resolve_left hu1
  have hm : (-1 : GL25) ∈ Q := hu3 ▸ u.2
  refine ⟨hm, ?_⟩
  have hue : (⟨-1, hm⟩ : ↥Q) = u := Subtype.ext hu3.symm
  rw [hue, hψu]

private theorem sq_iso {Q : Subgroup GL25} (hQ : Q ≤ SL25) (ψ : ↥Q ≃* QuaternionGroup 2)
    {hm : (-1 : GL25) ∈ Q} (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2) :
    ∀ q ∈ Q, q * q = 1 ∨ q * q = -1 := by
  intro q hq
  rcases q8_sq (ψ ⟨q, hq⟩) with h | h
  · left
    have h' : (⟨q, hq⟩ : ↥Q) * ⟨q, hq⟩ = 1 := ψ.injective (by rw [map_mul, h, map_one])
    simpa using congrArg Subtype.val h'
  · right
    have h' : (⟨q, hq⟩ : ↥Q) * ⟨q, hq⟩ = ⟨-1, hm⟩ :=
      ψ.injective (by rw [map_mul, hψm]; exact h)
    simpa using congrArg Subtype.val h'

private theorem comm_iso {Q : Subgroup GL25} (hQ : Q ≤ SL25) (ψ : ↥Q ≃* QuaternionGroup 2)
    {hm : (-1 : GL25) ∈ Q} (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2)
    {q q' : GL25} (hq : q ∈ Q) (hq' : q' ∈ Q) (hqq : q * q = -1) (hq'q' : q' * q' = -1)
    (hc : q * q' = q' * q) : q' = q ∨ q' = -q := by
  have hU : (⟨q, hq⟩ : ↥Q) * ⟨q, hq⟩ = ⟨-1, hm⟩ := Subtype.ext (by simpa using hqq)
  have hV : (⟨q', hq'⟩ : ↥Q) * ⟨q', hq'⟩ = ⟨-1, hm⟩ := Subtype.ext (by simpa using hq'q')
  have hcU : (⟨q, hq⟩ : ↥Q) * ⟨q', hq'⟩ = ⟨q', hq'⟩ * ⟨q, hq⟩ :=
    Subtype.ext (by simpa using hc)
  have h1 : ψ ⟨q, hq⟩ * ψ ⟨q, hq⟩ = QuaternionGroup.a 2 := by rw [← map_mul, hU, hψm]
  have h2 : ψ ⟨q', hq'⟩ * ψ ⟨q', hq'⟩ = QuaternionGroup.a 2 := by rw [← map_mul, hV, hψm]
  have h3 : ψ ⟨q, hq⟩ * ψ ⟨q', hq'⟩ = ψ ⟨q', hq'⟩ * ψ ⟨q, hq⟩ := by
    rw [← map_mul, ← map_mul, hcU]
  rcases q8_comm _ _ h1 h2 h3 with h | h
  · left
    exact congrArg Subtype.val (ψ.injective h)
  · right
    have h' : ψ ⟨q', hq'⟩ = ψ (⟨-1, hm⟩ * ⟨q, hq⟩) := by
      rw [map_mul, hψm]
      exact h
    have := congrArg Subtype.val (ψ.injective h')
    simpa [neg_mul] using this

private theorem prod_iso {Q : Subgroup GL25} (hQ : Q ≤ SL25) (ψ : ↥Q ≃* QuaternionGroup 2)
    {hm : (-1 : GL25) ∈ Q} (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2)
    {q q' : GL25} (hq : q ∈ Q) (hq' : q' ∈ Q) (hqq : q * q = -1) (hq'q' : q' * q' = -1)
    (hne : q' ≠ q) (hne' : q' ≠ -q) : (q * q') * (q * q') = -1 := by
  have h1 : ψ ⟨q, hq⟩ * ψ ⟨q, hq⟩ = QuaternionGroup.a 2 := by
    rw [← map_mul, Subtype.ext (show (⟨q, hq⟩ * ⟨q, hq⟩ : ↥Q).1 = (⟨-1, hm⟩ : ↥Q).1 by
      simpa using hqq), hψm]
  have h2 : ψ ⟨q', hq'⟩ * ψ ⟨q', hq'⟩ = QuaternionGroup.a 2 := by
    rw [← map_mul, Subtype.ext (show (⟨q', hq'⟩ * ⟨q', hq'⟩ : ↥Q).1 = (⟨-1, hm⟩ : ↥Q).1 by
      simpa using hq'q'), hψm]
  have hne1 : ψ ⟨q', hq'⟩ ≠ ψ ⟨q, hq⟩ := fun h => hne (congrArg Subtype.val (ψ.injective h))
  have hne2 : ψ ⟨q', hq'⟩ ≠ QuaternionGroup.a 2 * ψ ⟨q, hq⟩ := fun h => by
    have h' : ψ ⟨q', hq'⟩ = ψ (⟨-1, hm⟩ * ⟨q, hq⟩) := by
      rw [map_mul, hψm]
      exact h
    apply hne'
    have := congrArg Subtype.val (ψ.injective h')
    simpa [neg_mul] using this
  have h3 := q8_prod _ _ h1 h2 hne1 hne2
  have h4 : (⟨q, hq⟩ * ⟨q', hq'⟩ : ↥Q) * (⟨q, hq⟩ * ⟨q', hq'⟩) = ⟨-1, hm⟩ := by
    apply ψ.injective
    rw [map_mul, map_mul, hψm]
    exact h3
  have := congrArg Subtype.val h4
  simpa using this

private theorem comm_neg_one_iso {Q : Subgroup GL25} (hQ : Q ≤ SL25)
    (ψ : ↥Q ≃* QuaternionGroup 2) {hm : (-1 : GL25) ∈ Q}
    (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2) :
    ∃ x ∈ Q, ∃ y ∈ Q, x * y * x⁻¹ * y⁻¹ = -1 := by
  obtain ⟨u, v, huv⟩ := q8_comm_ex
  refine ⟨(ψ.symm u : GL25), (ψ.symm u).2, (ψ.symm v : GL25), (ψ.symm v).2, ?_⟩
  have h : ψ (ψ.symm u * ψ.symm v * (ψ.symm u)⁻¹ * (ψ.symm v)⁻¹) = ψ ⟨-1, hm⟩ := by
    rw [hψm, map_mul, map_mul, map_mul, map_inv, map_inv, MulEquiv.apply_symm_apply,
      MulEquiv.apply_symm_apply]
    exact huv
  have h' := congrArg Subtype.val (ψ.injective h)
  simpa using h'

private theorem inv_comm {Q : Subgroup GL25} (hQ : Q ≤ SL25) (ψ : ↥Q ≃* QuaternionGroup 2)
    {q q' : GL25} {a b : (ZMod 5)ˣ} (hq : q ∈ Q) (hq' : q' ∈ Q) (hqq : q * q = -1)
    (hq'q' : q' * q' = -1) (ha : (a : ZMod 5) * a = -1) (hb : (b : ZMod 5) * b = -1)
    (hc : (q * scU a) * (q' * scU b) = (q' * scU b) * (q * scU a)) :
    q' * scU b = q * scU a ∨ q' * scU b = -(q * scU a) := by
  obtain ⟨hm, hψm⟩ := neg_one_mem_iso hQ ψ
  have e1 : (q * scU a) * (q' * scU b) = (q * q') * scU (a * b) := by
    rw [scU_mul]
    calc (q * scU a) * (q' * scU b) = q * (scU a * q') * scU b := by group
      _ = q * (q' * scU a) * scU b := by rw [← scU_central q' a]
      _ = (q * q') * (scU a * scU b) := by group
  have e2 : (q' * scU b) * (q * scU a) = (q' * q) * scU (a * b) := by
    rw [mul_comm a b, scU_mul]
    calc (q' * scU b) * (q * scU a) = q' * (scU b * q) * scU a := by group
      _ = q' * (q * scU b) * scU a := by rw [← scU_central q b]
      _ = (q' * q) * (scU b * scU a) := by group
  have hcomm : q * q' = q' * q := by
    rw [e1, e2] at hc
    exact mul_right_cancel hc
  have hb2 : scU b = scU a ∨ scU b = -scU a := by
    rcases zmod5_sq_neg_one _ _ ha hb with h | h
    · left
      rw [show b = a from Units.ext h]
    · right
      exact scU_eq_neg h
  rcases comm_iso hQ ψ hψm hq hq' hqq hq'q' hcomm with h | h
  · rw [h]
    rcases hb2 with h2 | h2
    · left; rw [h2]
    · right; rw [h2, mul_neg]
  · rw [h, neg_mul]
    rcases hb2 with h2 | h2
    · right; rw [h2]
    · left; rw [h2, mul_neg, neg_neg]

private theorem inv_form {Q T : Subgroup GL25} (hQ : Q ≤ SL25) (ψ : ↥Q ≃* QuaternionGroup 2)
    (hdec : ∀ t ∈ T, ∃ q ∈ Q, ∃ a : (ZMod 5)ˣ, t = q * scU a) {x : GL25} (hx : x ∈ T)
    (hx2 : x * x = 1) (hx1 : x ≠ 1) (hxm : x ≠ -1) :
    ∃ q ∈ Q, q * q = -1 ∧ ∃ a : (ZMod 5)ˣ, (a : ZMod 5) * a = -1 ∧ x = q * scU a := by
  obtain ⟨q, hq, a, hxq⟩ := hdec x hx
  obtain ⟨hm, hψm⟩ := neg_one_mem_iso hQ ψ
  rcases sq_iso hQ ψ hψm q hq with hqq | hqq
  · exfalso
    have hq1 := sq_one_SL (hQ hq) hqq
    have hsa : scU a * scU a = 1 := by
      have h := hx2
      rw [hxq, mul_scU_mul, hqq, one_mul] at h
      exact h
    have haa : (a : ZMod 5) * a = 1 := by
      have h : a * a = 1 := scU_inj (by rw [scU_mul, scU_one]; exact hsa)
      exact congrArg Units.val h
    have hsc : scU a = 1 ∨ scU a = -1 := by
      rcases zmod5_sq_one _ haa with h | h
      · left
        rw [show a = 1 from Units.ext (by simp [h]), scU_one]
      · right
        rw [show a = -1 from Units.ext h, scU_neg]
    rcases hq1 with h1 | h1 <;> rcases hsc with h2 | h2
    · exact hx1 (by rw [hxq, h1, h2, mul_one])
    · exact hxm (by rw [hxq, h1, h2, one_mul])
    · exact hxm (by rw [hxq, h1, h2, mul_one])
    · exact hx1 (by rw [hxq, h1, h2, neg_one_mul, neg_neg])
  · have hsa : scU a * scU a = -1 := by
      have h := hx2
      rw [hxq, mul_scU_mul, hqq] at h
      calc scU a * scU a = (-1 * -1) * (scU a * scU a) := by rw [neg_one_mul, neg_neg, one_mul]
        _ = (-1) * ((-1) * (scU a * scU a)) := by rw [mul_assoc]
        _ = -1 := by rw [h, mul_one]
    have ha : (a : ZMod 5) * a = -1 := by
      have h : a * a = -1 := scU_inj (by rw [scU_mul, scU_neg]; exact hsa)
      exact congrArg Units.val h
    exact ⟨q, hq, hqq, a, ha, hxq⟩

private theorem q8_mul : ∀ u v w : QuaternionGroup 2, u * u = QuaternionGroup.a 2 →
    v * v = QuaternionGroup.a 2 → w * w = QuaternionGroup.a 2 → v ≠ u →
    v ≠ QuaternionGroup.a 2 * u → w ≠ u → w ≠ QuaternionGroup.a 2 * u → w ≠ v →
    w ≠ QuaternionGroup.a 2 * v → u * v = w ∨ u * v = QuaternionGroup.a 2 * w := by
  decide

private theorem q8_cover : ∀ u v w : QuaternionGroup 2, u * u = QuaternionGroup.a 2 →
    v * v = QuaternionGroup.a 2 → w * w = QuaternionGroup.a 2 → v ≠ u →
    v ≠ QuaternionGroup.a 2 * u → w ≠ u → w ≠ QuaternionGroup.a 2 * u → w ≠ v →
    w ≠ QuaternionGroup.a 2 * v → ∀ y : QuaternionGroup 2, y = 1 ∨ y = QuaternionGroup.a 2 ∨
      y = u ∨ y = QuaternionGroup.a 2 * u ∨ y = v ∨ y = QuaternionGroup.a 2 * v ∨
      y = w ∨ y = QuaternionGroup.a 2 * w := by
  decide

private def emb {Q : Subgroup GL25} (ψ : ↥Q ≃* QuaternionGroup 2) : QuaternionGroup 2 →* GL25 :=
  Q.subtype.comp ψ.symm.toMonoidHom

private theorem emb_apply {Q : Subgroup GL25} (ψ : ↥Q ≃* QuaternionGroup 2)
    (y : QuaternionGroup 2) : emb ψ y = ((ψ.symm y : ↥Q) : GL25) := rfl

private theorem emb_psi {Q : Subgroup GL25} (ψ : ↥Q ≃* QuaternionGroup 2) (x : GL25)
    (hx : x ∈ Q) : emb ψ (ψ ⟨x, hx⟩) = x := by
  rw [emb_apply, MulEquiv.symm_apply_apply]

private theorem emb_a2 {Q : Subgroup GL25} (ψ : ↥Q ≃* QuaternionGroup 2) {hm : (-1 : GL25) ∈ Q}
    (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2) : emb ψ (QuaternionGroup.a 2) = -1 := by
  rw [emb_apply, ← hψm, MulEquiv.symm_apply_apply]

private theorem emb_injective {Q : Subgroup GL25} (ψ : ↥Q ≃* QuaternionGroup 2) :
    Function.Injective (emb ψ) := fun _ _ h => ψ.symm.injective (Subtype.ext h)

private theorem sq_transfer {Q : Subgroup GL25} (ψ : ↥Q ≃* QuaternionGroup 2)
    {hm : (-1 : GL25) ∈ Q} (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2) {a : GL25} (ha : a ∈ Q)
    (haa : a * a = -1) : ψ ⟨a, ha⟩ * ψ ⟨a, ha⟩ = QuaternionGroup.a 2 := by
  apply emb_injective ψ
  rw [map_mul, emb_psi, emb_a2 ψ hψm]
  exact haa

private theorem ne_transfer {Q : Subgroup GL25} (ψ : ↥Q ≃* QuaternionGroup 2)
    {hm : (-1 : GL25) ∈ Q} (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2) {a b : GL25} (ha : a ∈ Q)
    (hb : b ∈ Q) (hba : b ≠ a) (hba' : b ≠ -a) :
    ψ ⟨b, hb⟩ ≠ ψ ⟨a, ha⟩ ∧ ψ ⟨b, hb⟩ ≠ QuaternionGroup.a 2 * ψ ⟨a, ha⟩ := by
  constructor
  · intro h
    apply hba
    have h' := congrArg (emb ψ) h
    rwa [emb_psi, emb_psi] at h'
  · intro h
    apply hba'
    have h' := congrArg (emb ψ) h
    rw [emb_psi, map_mul, emb_a2 ψ hψm, emb_psi, neg_one_mul] at h'
    exact h'

private theorem mul_of_emb {Q : Subgroup GL25} (ψ : ↥Q ≃* QuaternionGroup 2)
    {hm : (-1 : GL25) ∈ Q} (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2)
    {a b c : GL25} (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q) (haa : a * a = -1) (hbb : b * b = -1)
    (hcc : c * c = -1) (hba : b ≠ a) (hba' : b ≠ -a) (hca : c ≠ a) (hca' : c ≠ -a)
    (hcb : c ≠ b) (hcb' : c ≠ -b) : a * b = c ∨ a * b = -c := by
  obtain ⟨h1, h2⟩ := ne_transfer ψ hψm ha hb hba hba'
  obtain ⟨h3, h4⟩ := ne_transfer ψ hψm ha hc hca hca'
  obtain ⟨h5, h6⟩ := ne_transfer ψ hψm hb hc hcb hcb'
  rcases q8_mul _ _ _ (sq_transfer ψ hψm ha haa) (sq_transfer ψ hψm hb hbb)
    (sq_transfer ψ hψm hc hcc) h1 h2 h3 h4 h5 h6 with h | h
  · left
    have h' := congrArg (emb ψ) h
    rwa [map_mul, emb_psi, emb_psi, emb_psi] at h'
  · right
    have h' := congrArg (emb ψ) h
    rw [map_mul, map_mul, emb_psi, emb_psi, emb_a2 ψ hψm, emb_psi, neg_one_mul] at h'
    exact h'

private theorem cover_of_emb {Q : Subgroup GL25} (ψ : ↥Q ≃* QuaternionGroup 2)
    {hm : (-1 : GL25) ∈ Q} (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2)
    {a b c : GL25} (ha : a ∈ Q) (hb : b ∈ Q) (hc : c ∈ Q) (haa : a * a = -1) (hbb : b * b = -1)
    (hcc : c * c = -1) (hba : b ≠ a) (hba' : b ≠ -a) (hca : c ≠ a) (hca' : c ≠ -a)
    (hcb : c ≠ b) (hcb' : c ≠ -b) {x : GL25} (hx : x ∈ Q) :
    x = 1 ∨ x = -1 ∨ x = a ∨ x = -a ∨ x = b ∨ x = -b ∨ x = c ∨ x = -c := by
  obtain ⟨h1, h2⟩ := ne_transfer ψ hψm ha hb hba hba'
  obtain ⟨h3, h4⟩ := ne_transfer ψ hψm ha hc hca hca'
  obtain ⟨h5, h6⟩ := ne_transfer ψ hψm hb hc hcb hcb'
  have key := q8_cover (ψ ⟨a, ha⟩) (ψ ⟨b, hb⟩) (ψ ⟨c, hc⟩) (sq_transfer ψ hψm ha haa)
    (sq_transfer ψ hψm hb hbb) (sq_transfer ψ hψm hc hcc) h1 h2 h3 h4 h5 h6 (ψ ⟨x, hx⟩)
  have hx' : x = emb ψ (ψ ⟨x, hx⟩) := (emb_psi ψ x hx).symm
  rcases key with h | h | h | h | h | h | h | h
  · exact Or.inl (by rw [hx', h, map_one])
  · exact Or.inr (Or.inl (by rw [hx', h, emb_a2 ψ hψm]))
  · exact Or.inr (Or.inr (Or.inl (by rw [hx', h, emb_psi])))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (by rw [hx', h, map_mul, emb_a2 ψ hψm, emb_psi,
      neg_one_mul]))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hx', h, emb_psi])))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hx', h, map_mul,
      emb_a2 ψ hψm, emb_psi, neg_one_mul]))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (by rw [hx', h, emb_psi])))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (by rw [hx', h, map_mul,
      emb_a2 ψ hψm, emb_psi, neg_one_mul])))))))

private theorem gl_small_cube (k : ℕ) (hk : k ≤ 1) (x : GL (Fin k) (ZMod 5)) (h : x ^ 3 = 1) :
    x = 1 := by
  interval_cases k
  · apply Units.ext
    exact Matrix.ext fun i => i.elim0
  · have hdet : (Matrix.GeneralLinearGroup.det x) ^ 3 = 1 := by rw [← map_pow, h, map_one]
    have hu : ((Matrix.GeneralLinearGroup.det x : (ZMod 5)ˣ) : ZMod 5) = 1 := by
      have h3 : ∀ a : ZMod 5, a ^ 3 = 1 → a = 1 := by decide
      exact h3 _ (by simpa using congrArg Units.val hdet)
    have hd : Matrix.GeneralLinearGroup.det x = 1 := Units.ext hu
    have hdetM : (x : Matrix (Fin 1) (Fin 1) (ZMod 5)).det = 1 := by
      rw [← Matrix.GeneralLinearGroup.val_det_apply, hd, Units.val_one]
    rw [Matrix.det_fin_one] at hdetM
    apply Units.ext
    ext i j
    rw [Subsingleton.elim i 0, Subsingleton.elim j 0, Units.val_one, Matrix.one_apply_eq]
    exact hdetM

private theorem conj_mem_SL25 {g x : GL25} (hx : x ∈ SL25) : g * x * g⁻¹ ∈ SL25 := by
  rw [mem_SL25, map_mul, map_mul, map_inv, mem_SL25.1 hx, mul_one, mul_inv_cancel]

private theorem natCard_le_four_of_mem {Γ : Type} [Group Γ] [Finite Γ] (E : Subgroup Γ)
    (F : Finset Γ) (hF : F.card ≤ 4) (h : ∀ e ∈ E, e ∈ F) : Nat.card E ≤ 4 := by
  classical
  have hinj : Function.Injective (fun e : E => (⟨e.1, h e.1 e.2⟩ : {x // x ∈ F})) := by
    intro e1 e2 he
    have h2 := congrArg Subtype.val he
    exact Subtype.ext h2
  calc Nat.card E ≤ Nat.card {x // x ∈ F} := Nat.card_le_card_of_injective _ hinj
    _ = F.card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 4 := hF

private theorem closure_gen {Q : Subgroup GL25} (hQSL : Q ≤ SL25) (ψ : ↥Q ≃* QuaternionGroup 2)
    {hm : (-1 : GL25) ∈ Q} (hψm : ψ ⟨-1, hm⟩ = QuaternionGroup.a 2) {g : GL25}
    (hg3 : g ^ 3 = 1) (hg1 : g ≠ 1) (hgQ : ∀ x ∈ Q, g * x * g⁻¹ ∈ Q) {x : GL25} (hx : x ∈ Q) :
    x ∈ Subgroup.closure {y : GL25 | ∃ t ∈ Q, y = t * (g * t * g⁻¹)⁻¹} := by
  set H := Subgroup.closure {y : GL25 | ∃ t ∈ Q, y = t * (g * t * g⁻¹)⁻¹} with hH
  have hd : ∀ t ∈ Q, t * (g * t * g⁻¹)⁻¹ ∈ H := fun t ht => Subgroup.subset_closure ⟨t, ht, rfl⟩
  obtain ⟨t0, ht0⟩ : ∃ t0 : GL25, t0 = ((ψ.symm (QuaternionGroup.a 1) : ↥Q) : GL25) := ⟨_, rfl⟩
  have ht0Q : t0 ∈ Q := by rw [ht0]; exact (ψ.symm (QuaternionGroup.a 1)).2
  have hsq8 : (QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.a 1 =
      QuaternionGroup.a 2 := by decide
  have ht0sq : t0 * t0 = -1 := by
    have h : ψ.symm (QuaternionGroup.a 1) * ψ.symm (QuaternionGroup.a 1) = ⟨-1, hm⟩ := by
      apply ψ.injective
      rw [map_mul, MulEquiv.apply_symm_apply, hψm, hsq8]
    rw [ht0]
    exact congrArg Subtype.val h
  have hsl0 : t0 ∈ SL25 := hQSL ht0Q
  obtain ⟨t1, ht1⟩ : ∃ t1 : GL25, t1 = g * t0 * g⁻¹ := ⟨_, rfl⟩
  obtain ⟨t2, ht2⟩ : ∃ t2 : GL25, t2 = g * t1 * g⁻¹ := ⟨_, rfl⟩
  have ht1Q : t1 ∈ Q := by rw [ht1]; exact hgQ t0 ht0Q
  have ht2Q : t2 ∈ Q := by rw [ht2]; exact hgQ t1 ht1Q
  have ht1sq : t1 * t1 = -1 := by rw [ht1]; exact conj_sq g t0 ht0sq
  have ht2sq : t2 * t2 = -1 := by rw [ht2]; exact conj_sq g t1 ht1sq
  have hsl1 : t1 ∈ SL25 := by rw [ht1]; exact conj_mem_SL25 hsl0
  have h01 : t1 ≠ t0 ∧ t1 ≠ -t0 := by rw [ht1]; exact gl_conj_ne hg3 hg1 ht0sq hsl0
  have h12 : t2 ≠ t1 ∧ t2 ≠ -t1 := by rw [ht2]; exact gl_conj_ne hg3 hg1 ht1sq hsl1
  have hg3' : g * g * g = 1 := by rw [← pow_three']; exact hg3
  have hα : g * t2 * g⁻¹ = t0 := by
    have e : g * t2 * g⁻¹ = (g * g * g) * t0 * (g * g * g)⁻¹ := by
      rw [ht2, ht1]; group
    rw [e, hg3', one_mul, inv_one, mul_one]
  have ht2ne : t2 ≠ t0 ∧ t2 ≠ -t0 := by
    constructor
    · intro h
      apply h01.1
      rw [h] at hα
      rw [ht1]
      exact hα
    · intro h
      apply h01.2
      rw [h, mul_neg, neg_mul] at hα
      have h3 := congrArg (fun y => -y) hα
      simp only [neg_neg] at h3
      rw [ht1]
      exact h3
  have nt01 : t0 ≠ t1 := fun h => h01.1 h.symm
  have nt01' : t0 ≠ -t1 := fun h => h01.2 (by rw [h, neg_neg])
  have nt02 : t0 ≠ t2 := fun h => ht2ne.1 h.symm
  have nt02' : t0 ≠ -t2 := fun h => ht2ne.2 (by rw [h, neg_neg])
  have nt12 : t1 ≠ t2 := fun h => h12.1 h.symm
  have nt12' : t1 ≠ -t2 := fun h => h12.2 (by rw [h, neg_neg])
  have hcov : ∀ y ∈ Q, y = 1 ∨ y = -1 ∨ y = t0 ∨ y = -t0 ∨ y = t1 ∨ y = -t1 ∨ y = t2 ∨
      y = -t2 := fun y hy => cover_of_emb ψ hψm ht0Q ht1Q ht2Q ht0sq ht1sq ht2sq h01.1 h01.2
        ht2ne.1 ht2ne.2 h12.1 h12.2 hy
  have hm1 := mul_of_emb ψ hψm ht0Q ht1Q ht2Q ht0sq ht1sq ht2sq h01.1 h01.2 ht2ne.1 ht2ne.2
    h12.1 h12.2
  have hm2 := mul_of_emb ψ hψm ht1Q ht2Q ht0Q ht1sq ht2sq ht0sq h12.1 h12.2 nt01 nt01' nt02 nt02'
  have hm3 := mul_of_emb ψ hψm ht2Q ht0Q ht1Q ht2sq ht0sq ht1sq nt02 nt02' nt12 nt12' h01.1 h01.2
  have hinv1 : t1⁻¹ = -t1 := inv_eq_of_mul_eq_one_right (by rw [mul_neg, ht1sq, neg_neg])
  have hinv2 : t2⁻¹ = -t2 := inv_eq_of_mul_eq_one_right (by rw [mul_neg, ht2sq, neg_neg])
  have hinv0 : t0⁻¹ = -t0 := inv_eq_of_mul_eq_one_right (by rw [mul_neg, ht0sq, neg_neg])
  have hd0 : t0 * -t1 ∈ H := by
    have h := hd t0 ht0Q
    rwa [← ht1, hinv1] at h
  have hd1 : t1 * -t2 ∈ H := by
    have h := hd t1 ht1Q
    rwa [← ht2, hinv2] at h
  have hd2 : t2 * -t0 ∈ H := by
    have h := hd t2 ht2Q
    rwa [hα, hinv0] at h
  have hsq0 : (t0 * -t1) * (t0 * -t1) = -1 := by
    rw [mul_neg, neg_mul_neg]
    exact prod_iso hQSL ψ hψm ht0Q ht1Q ht0sq ht1sq h01.1 h01.2
  have hsq1 : (t1 * -t2) * (t1 * -t2) = -1 := by
    rw [mul_neg, neg_mul_neg]
    exact prod_iso hQSL ψ hψm ht1Q ht2Q ht1sq ht2sq h12.1 h12.2
  have hsq2 : (t2 * -t0) * (t2 * -t0) = -1 := by
    rw [mul_neg, neg_mul_neg]
    exact prod_iso hQSL ψ hψm ht2Q ht0Q ht2sq ht0sq nt02 nt02'
  have hneg1 : (-1 : GL25) ∈ H := by
    have h := H.mul_mem hd0 hd0
    rwa [hsq0] at h
  have hneg : ∀ y ∈ H, -y ∈ H := fun y hy => by
    rw [← neg_one_mul]
    exact H.mul_mem hneg1 hy
  have hmemof : ∀ y z : GL25, y ∈ H → (y = z ∨ y = -z) → z ∈ H := by
    rintro y z hy (rfl | rfl)
    · exact hy
    · have h := hneg _ hy
      rwa [neg_neg] at h
  have ht01 : t0 * t1 ∈ H := by
    have h := hneg _ hd0
    rwa [mul_neg, neg_neg] at h
  have ht12 : t1 * t2 ∈ H := by
    have h := hneg _ hd1
    rwa [mul_neg, neg_neg] at h
  have ht20 : t2 * t0 ∈ H := by
    have h := hneg _ hd2
    rwa [mul_neg, neg_neg] at h
  have hmem2 : t2 ∈ H := hmemof _ _ ht01 hm1
  have hmem0 : t0 ∈ H := hmemof _ _ ht12 hm2
  have hmem1 : t1 ∈ H := hmemof _ _ ht20 hm3
  rcases hcov x hx with h | h | h | h | h | h | h | h <;> rw [h]
  · exact H.one_mem
  · exact hneg1
  · exact hmem0
  · exact hneg _ hmem0
  · exact hmem1
  · exact hneg _ hmem1
  · exact hmem2
  · exact hneg _ hmem2

variable {Γ : Type} [Group Γ] [Finite Γ]

@[expose] def Shape81 (S : Subgroup Γ) (c : Γ) : Prop :=
  (IsCyclic S ∧ ∀ s ∈ S, c * s * c⁻¹ = s) ∨
  ∃ z ∈ S, orderOf z = 2 ∧ c * z * c⁻¹ = z ∧ (∀ s ∈ S, s * z = z * s) ∧
    (∀ r ∈ S, orderOf r = 2 → r ≠ z → z = (r * (c * r * c⁻¹)) ^ 2) ∧
    (∀ E : Subgroup Γ, E ≤ S → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → (∀ x ∈ E, x * x = 1) →
      E ≠ ⊥ → Nat.card E ≤ 4 ∧
        (z ∈ E ∨ ∃ r ∈ S, orderOf r = 2 ∧ r ≠ z ∧ E = Subgroup.zpowers r)) ∧
    ∃ Q : Subgroup Γ, Q ≤ S ∧ z ∈ ⁅Q, Q⁆ ∧ (∀ q ∈ Q, c * q * c⁻¹ ∈ Q) ∧
      ∀ q ∈ Q, q ∈ Subgroup.closure {x | ∃ t ∈ Q, x = t * (c * t * c⁻¹)⁻¹}

private theorem shape81_two (S : Subgroup Γ) (c : Γ) (hS : IsPGroup 2 S) (hc3 : orderOf c = 3)
    (hcS : c ∈ Subgroup.normalizer (S : Set Γ)) (φ : Γ →* GL25)
    (hφc : φ c ≠ 1) (hφS : ∀ s ∈ S, φ s = 1 → s = 1) : Shape81 S c := by
  classical
  have hinj : ∀ s ∈ S, ∀ t ∈ S, φ s = φ t → s = t := by
    intro s hs t ht h
    have h1 : s⁻¹ * t ∈ S := S.mul_mem (S.inv_mem hs) ht
    have h2 : φ (s⁻¹ * t) = 1 := by rw [map_mul, map_inv, h, inv_mul_cancel]
    exact inv_mul_eq_one.1 (hφS _ h1 h2)
  have hcS' : ∀ h : Γ, h ∈ S ↔ c * h * c⁻¹ ∈ S := fun h => Subgroup.mem_normalizer_iff.1 hcS h
  have hcinv : ∀ s ∈ S, c⁻¹ * s * c ∈ S := fun s hs => (hcS' _).2 (by
    have e : c * (c⁻¹ * s * c) * c⁻¹ = s := by group
    rw [e]; exact hs)
  obtain ⟨T, hTdef⟩ : ∃ T : Subgroup GL25, T = S.map φ := ⟨_, rfl⟩
  have hTiff : ∀ x : GL25, x ∈ T ↔ ∃ s ∈ S, φ s = x := fun x => by
    rw [hTdef, Subgroup.mem_map]
  have hTmem : ∀ s ∈ S, φ s ∈ T := fun s hs => (hTiff _).2 ⟨s, hs, rfl⟩
  obtain ⟨g, hgdef⟩ : ∃ g : GL25, g = φ c := ⟨_, rfl⟩
  have hg3 : g ^ 3 = 1 := by rw [hgdef, ← map_pow, ← hc3, pow_orderOf_eq_one, map_one]
  have hg1 : g ≠ 1 := by rw [hgdef]; exact hφc
  have hgord : orderOf g = 3 := orderOf_eq_prime hg3 hg1
  have hT2 : IsPGroup 2 T := by rw [hTdef]; exact hS.map φ
  have hgT : g ∈ Subgroup.normalizer (T : Set GL25) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    show x ∈ T ↔ g * x * g⁻¹ ∈ T
    rw [hTiff, hTiff]
    constructor
    · rintro ⟨s, hs, rfl⟩
      refine ⟨c * s * c⁻¹, (hcS' s).1 hs, ?_⟩
      simp only [map_mul, map_inv, hgdef]
    · rintro ⟨s, hs, hsx⟩
      refine ⟨c⁻¹ * s * c, hcinv s hs, ?_⟩
      simp only [map_mul, map_inv]
      rw [hsx, hgdef]
      group
  by_cases hcent : ∀ s ∈ S, c * s * c⁻¹ = s
  ·
    left
    refine ⟨?_, hcent⟩
    have hcyc := gl25_centralizer_cyclic g hgord
    have hcs : ∀ s ∈ S, g * φ s = φ s * g := by
      intro s hs
      rw [hgdef, ← map_mul, ← map_mul]
      congr 1
      have := hcent s hs
      rwa [mul_inv_eq_iff_eq_mul] at this
    let f : ↥S →* ↥(Subgroup.centralizer ({g} : Set GL25)) :=
      MonoidHom.codRestrict (φ.comp S.subtype) _ (fun s => by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hcs s s.2)
    have hf : Function.Injective f := by
      intro a b hab
      apply Subtype.ext
      have h1 := congrArg Subtype.val hab
      exact hinj a.1 a.2 b.1 b.2 h1
    haveI := hcyc
    exact isCyclic_of_injective f hf
  ·
    right
    have hnc' : ¬ ∀ t ∈ T, g * t * g⁻¹ = t := by
      intro hall
      apply hcent
      intro s hs
      apply hinj _ ((hcS' s).1 hs) s hs
      have h := hall (φ s) (hTmem s hs)
      rw [hgdef, ← map_inv, ← map_mul, ← map_mul] at h
      exact h
    obtain ⟨Q, hQT, ⟨ψ⟩, hQdef, hdec⟩ := gl25_two_subgroup_normalized hT2 hgord hgT hnc'
    have hQSL : Q ≤ SL25 := by
      rw [← hQdef]
      refine Subgroup.commutator_le.2 fun a _ b _ => ?_
      rw [mem_SL25, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact mul_comm _ _
    obtain ⟨hm, hψm⟩ := neg_one_mem_iso hQSL ψ
    have hdec' : ∀ t ∈ T, ∃ q ∈ Q, ∃ a : (ZMod 5)ˣ, t = q * scU a := by
      intro t ht
      obtain ⟨q, hq, a, h⟩ := hdec t ht
      exact ⟨q, hq, a, Units.ext (by rw [Units.val_mul, scU_val]; exact h)⟩
    have hgQ : ∀ x ∈ Q, g * x * g⁻¹ ∈ Q := by
      have hle : ⁅T, Subgroup.zpowers g⁆ ≤
          Subgroup.comap (MulAut.conj g).toMonoidHom ⁅T, Subgroup.zpowers g⁆ := by
        refine Subgroup.commutator_le.2 fun a ha b hb => ?_
        rw [Subgroup.mem_comap]
        have hconjT : ∀ a ∈ T, g * a * g⁻¹ ∈ T := fun a ha =>
          (Subgroup.mem_normalizer_iff.1 hgT a).1 ha
        have hconjZ : ∀ b ∈ Subgroup.zpowers g, g * b * g⁻¹ ∈ Subgroup.zpowers g := by
          intro b hb
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
          exact Subgroup.mem_zpowers_iff.2 ⟨k, by group⟩
        have key : g * ⁅a, b⁆ * g⁻¹ = ⁅g * a * g⁻¹, g * b * g⁻¹⁆ := by
          simp only [commutatorElement_def]
          group
        show g * ⁅a, b⁆ * g⁻¹ ∈ ⁅T, Subgroup.zpowers g⁆
        rw [key]
        exact Subgroup.commutator_mem_commutator (hconjT a ha) (hconjZ b hb)
      intro x hx
      rw [← hQdef] at hx ⊢
      exact hle hx
    obtain ⟨QΓ, hQΓ⟩ : ∃ QΓ : Subgroup Γ, QΓ = S ⊓ Q.comap φ := ⟨_, rfl⟩
    have hQΓmem : ∀ q : Γ, q ∈ QΓ ↔ q ∈ S ∧ φ q ∈ Q := fun q => by
      rw [hQΓ, Subgroup.mem_inf, Subgroup.mem_comap]
    have hlift : ∀ x ∈ Q, ∃ s ∈ QΓ, φ s = x := by
      intro x hx
      obtain ⟨s, hs, hsx⟩ := (hTiff x).1 (hQT hx)
      exact ⟨s, (hQΓmem s).2 ⟨hs, by rw [hsx]; exact hx⟩, hsx⟩
    obtain ⟨z, hzS, hzφ⟩ : ∃ z ∈ S, φ z = -1 := (hTiff (-1)).1 (hQT hm)
    have hneg_conj : g * (-1) * g⁻¹ = -1 := by rw [mul_neg_one, neg_mul, mul_inv_cancel]
    have hz2 : z ^ 2 = 1 := hinj _ (S.pow_mem hzS 2) 1 S.one_mem
      (by rw [map_pow, hzφ, neg_one_sq, map_one])
    have hz1 : z ≠ 1 := fun h => neg_one_ne_one' (by rw [← hzφ, h, map_one])
    have hzord : orderOf z = 2 := orderOf_eq_prime hz2 hz1
    have hcz : c * z * c⁻¹ = z := hinj _ ((hcS' z).1 hzS) z hzS (by
      rw [map_mul, map_mul, map_inv, hzφ, ← hgdef, hneg_conj])
    have hzcen : ∀ s ∈ S, s * z = z * s := fun s hs => hinj _ (S.mul_mem hs hzS) _
      (S.mul_mem hzS hs) (by rw [map_mul, map_mul, hzφ, mul_neg_one, neg_one_mul])
    have hφsq : ∀ s : Γ, s * s = 1 → φ s * φ s = 1 := fun s hs => by
      rw [← map_mul, hs, map_one]
    have hinvol : ∀ r ∈ S, orderOf r = 2 → r ≠ z → z = (r * (c * r * c⁻¹)) ^ 2 := by
      intro r hr hord hrz
      have hr2 : r ^ 2 = 1 := by rw [← hord]; exact pow_orderOf_eq_one r
      have hr1 : r ≠ 1 := fun h => by
        rw [h, orderOf_one] at hord
        norm_num at hord
      have hφr1 : φ r ≠ 1 := fun h => hr1 (hφS r hr h)
      have hφrm : φ r ≠ -1 := fun h => hrz (hinj r hr z hzS (by rw [h, hzφ]))
      obtain ⟨q, hq, hqq, a, ha, hxq⟩ := inv_form hQSL ψ hdec' (hTmem r hr)
        (hφsq r (by rw [← pow_two]; exact hr2)) hφr1 hφrm
      have hqS : q ∈ SL25 := hQSL hq
      have hφprod : φ (r * (c * r * c⁻¹)) = (q * (g * q * g⁻¹)) * -1 := by
        simp only [map_mul, map_inv]
        rw [← hgdef, hxq, conj_scU, mul_scU_mul, scU_sq ha]
      have hprod_sq : (q * (g * q * g⁻¹)) * (q * (g * q * g⁻¹)) = -1 :=
        prod_iso hQSL ψ hψm hq (hgQ q hq) hqq (conj_sq g q hqq)
          (gl_conj_ne hg3 hg1 hqq hqS).1 (gl_conj_ne hg3 hg1 hqq hqS).2
      have hprodS : r * (c * r * c⁻¹) ∈ S := S.mul_mem hr ((hcS' r).1 hr)
      apply hinj z hzS _ (S.pow_mem hprodS 2)
      rw [map_pow, hφprod, hzφ, sq, mul_neg_one, neg_mul_neg]
      exact hprod_sq.symm
    have hE : ∀ E : Subgroup Γ, E ≤ S → (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) →
        (∀ x ∈ E, x * x = 1) → E ≠ ⊥ → Nat.card E ≤ 4 ∧
          (z ∈ E ∨ ∃ r ∈ S, orderOf r = 2 ∧ r ≠ z ∧ E = Subgroup.zpowers r) := by
      intro E hES hEc hEsq hEbot
      by_cases hnc : ∃ r0 ∈ E, φ r0 ≠ 1 ∧ φ r0 ≠ -1
      · obtain ⟨r0, hr0E, hr01, hr0m⟩ := hnc
        have hr0S : r0 ∈ S := hES hr0E
        have hr0sq : r0 * r0 = 1 := hEsq r0 hr0E
        have hr0z : r0 ≠ z := fun h => hr0m (by rw [h, hzφ])
        have hr0ord : orderOf r0 = 2 := orderOf_eq_prime (by rw [sq]; exact hr0sq)
          (fun h => hr01 (by rw [h, map_one]))
        obtain ⟨q0, hq0, hq0q0, a0, ha0, hx0⟩ := inv_form hQSL ψ hdec' (hTmem r0 hr0S)
          (hφsq r0 hr0sq) hr01 hr0m
        have key : ∀ e ∈ E, e = 1 ∨ e = z ∨ e = r0 ∨ e = z * r0 := by
          intro e he
          have heS : e ∈ S := hES he
          by_cases h1 : φ e = 1
          · exact Or.inl (hinj e heS 1 S.one_mem (by rw [h1, map_one]))
          by_cases h2 : φ e = -1
          · exact Or.inr (Or.inl (hinj e heS z hzS (by rw [h2, hzφ])))
          obtain ⟨q, hq, hqq, b, hb, hxe⟩ := inv_form hQSL ψ hdec' (hTmem e heS)
            (hφsq e (hEsq e he)) h1 h2
          have hc : (q0 * scU a0) * (q * scU b) = (q * scU b) * (q0 * scU a0) := by
            rw [← hx0, ← hxe, ← map_mul, ← map_mul, hEc r0 hr0E e he]
          rcases inv_comm hQSL ψ hq0 hq hq0q0 hqq ha0 hb hc with h | h
          · exact Or.inr (Or.inr (Or.inl (hinj e heS r0 hr0S (by rw [hxe, h, hx0]))))
          · refine Or.inr (Or.inr (Or.inr (hinj e heS (z * r0) (S.mul_mem hzS hr0S) ?_)))
            rw [map_mul, hzφ, neg_one_mul, hxe, h, hx0]
        have hcard : Nat.card E ≤ 4 := natCard_le_four_of_mem E {1, z, r0, z * r0}
          Finset.card_le_four (fun e he => by
            rcases key e he with h | h | h | h <;> simp [h])
        refine ⟨hcard, ?_⟩
        by_cases hzE : z ∈ E
        · exact Or.inl hzE
        · refine Or.inr ⟨r0, hr0S, hr0ord, hr0z, le_antisymm ?_ (Subgroup.zpowers_le.2 hr0E)⟩
          intro e he
          rcases key e he with h | h | h | h
          · rw [h]; exact Subgroup.one_mem _
          · exact absurd (h ▸ he) hzE
          · rw [h]; exact Subgroup.mem_zpowers r0
          · exfalso
            apply hzE
            have hm' : z * r0 * r0 ∈ E := E.mul_mem (h ▸ he) hr0E
            rwa [mul_assoc, hr0sq, mul_one] at hm'
      ·
        push Not at hnc
        obtain ⟨⟨e, he⟩, hne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hEbot
        have heS : e ∈ S := hES he
        have he1 : e ≠ 1 := fun h => hne (Subtype.ext h)
        have hez : φ e = -1 := hnc e he (fun h => he1 (hφS e heS h))
        have hzE : z ∈ E := by
          have h' : e = z := hinj e heS z hzS (by rw [hez, hzφ])
          rw [← h']
          exact he
        refine ⟨?_, Or.inl hzE⟩
        refine natCard_le_four_of_mem E {1, z} ?_ (fun x hx => ?_)
        · exact Finset.card_le_two.trans (by norm_num)
        · by_cases hx1 : x = 1
          · simp [hx1]
          · have hxS := hES hx
            have hxz : x = z := hinj x hxS z hzS
              (by rw [hzφ]; exact hnc x hx (fun h => hx1 (hφS x hxS h)))
            simp [hxz]
    have hQle : QΓ ≤ S := fun q hq => ((hQΓmem q).1 hq).1
    have hzcomm : z ∈ ⁅QΓ, QΓ⁆ := by
      obtain ⟨x, hx, y, hy, hxy⟩ := comm_neg_one_iso hQSL ψ hψm
      obtain ⟨s, hs, hsx⟩ := hlift x hx
      obtain ⟨t, ht, hty⟩ := hlift y hy
      have hcS2 : ⁅s, t⁆ ∈ S := by
        rw [commutatorElement_def]
        exact S.mul_mem (S.mul_mem (S.mul_mem ((hQΓmem s).1 hs).1 ((hQΓmem t).1 ht).1)
          (S.inv_mem ((hQΓmem s).1 hs).1)) (S.inv_mem ((hQΓmem t).1 ht).1)
      have hφcomm : φ ⁅s, t⁆ = φ z := by
        rw [hzφ, commutatorElement_def]
        simp only [map_mul, map_inv, hsx, hty]
        exact hxy
      have hsame : ⁅s, t⁆ = z := hinj _ hcS2 z hzS hφcomm
      rw [← hsame]
      exact Subgroup.commutator_mem_commutator hs ht
    have hQconj : ∀ q ∈ QΓ, c * q * c⁻¹ ∈ QΓ := fun q hq => by
      obtain ⟨hqS, hqQ⟩ := (hQΓmem q).1 hq
      refine (hQΓmem _).2 ⟨(hcS' q).1 hqS, ?_⟩
      rw [map_mul, map_mul, map_inv, ← hgdef]
      exact hgQ _ hqQ
    have closureS : Subgroup.closure {x | ∃ t ∈ QΓ, x = t * (c * t * c⁻¹)⁻¹} ≤ S := by
      refine (Subgroup.closure_le _).2 ?_
      rintro _ ⟨t, ht, rfl⟩
      exact S.mul_mem ((hQΓmem t).1 ht).1 (S.inv_mem ((hcS' t).1 ((hQΓmem t).1 ht).1))
    have hQgen : ∀ q ∈ QΓ, q ∈ Subgroup.closure {x | ∃ t ∈ QΓ, x = t * (c * t * c⁻¹)⁻¹} := by
      intro q hq
      have hqS := ((hQΓmem q).1 hq).1
      have hqQ := ((hQΓmem q).1 hq).2
      have hgen := closure_gen hQSL ψ hψm hg3 hg1 hgQ hqQ
      have hsub : {x : GL25 | ∃ t ∈ Q, x = t * (g * t * g⁻¹)⁻¹} ⊆
          φ '' {x | ∃ t ∈ QΓ, x = t * (c * t * c⁻¹)⁻¹} := by
        rintro _ ⟨t, htQ, rfl⟩
        obtain ⟨s, hs, hsφ⟩ := hlift t htQ
        refine ⟨s * (c * s * c⁻¹)⁻¹, ⟨s, hs, rfl⟩, ?_⟩
        simp only [map_mul, map_inv, ← hgdef, hsφ]
      have hcl : Subgroup.closure {x : GL25 | ∃ t ∈ Q, x = t * (g * t * g⁻¹)⁻¹} ≤
          (Subgroup.closure {x | ∃ t ∈ QΓ, x = t * (c * t * c⁻¹)⁻¹}).map φ := by
        refine (Subgroup.closure_le _).2 ?_
        intro y hy
        obtain ⟨x, hx, rfl⟩ := hsub hy
        exact Subgroup.mem_map_of_mem φ (Subgroup.subset_closure hx)
      obtain ⟨y, hy, hyq⟩ := Subgroup.mem_map.1 (hcl hgen)
      have hyq' : y = q := hinj y (closureS hy) q hqS hyq
      rw [← hyq']
      exact hy
    exact ⟨z, hzS, hzord, hcz, hzcen, hinvol, hE, QΓ, hQle, hzcomm, hQconj, hQgen⟩

theorem shape81_of_gl (S : Subgroup Γ) (c : Γ) (hS : IsPGroup 2 S) (hc3 : orderOf c = 3)
    (hcS : c ∈ Subgroup.normalizer (S : Set Γ)) (k : ℕ) (hk : k ≤ 2)
    (φ : Γ →* GL (Fin k) (ZMod 5))
    (hφc : φ c ≠ 1) (hφS : ∀ s ∈ S, φ s = 1 → s = 1) : Shape81 S c := by
  have hφ3 : φ c ^ 3 = 1 := by rw [← map_pow, ← hc3, pow_orderOf_eq_one, map_one]
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
  · exact absurd (gl_small_cube 0 (by norm_num) (φ c) hφ3) hφc
  · exact absurd (gl_small_cube 1 (by norm_num) (φ c) hφ3) hφc
  · exact shape81_two S c hS hc3 hcS φ hφc hφS

private def subPre {A B : Type} [Group A] [Group B] {P : Subgroup A} {R : Subgroup B}
    (f : ↥P ≃* ↥R) (X : Subgroup B) : Subgroup A where
  carrier := {x | ∃ h : x ∈ P, ((f ⟨x, h⟩ : ↥R) : B) ∈ X}
  mul_mem' := by
    rintro a b ⟨ha, hax⟩ ⟨hb, hbx⟩
    refine ⟨P.mul_mem ha hb, ?_⟩
    have key : ((f ⟨a * b, P.mul_mem ha hb⟩ : ↥R) : B) =
        ((f ⟨a, ha⟩ : ↥R) : B) * ((f ⟨b, hb⟩ : ↥R) : B) :=
      congrArg Subtype.val (map_mul f ⟨a, ha⟩ ⟨b, hb⟩)
    rw [key]
    exact X.mul_mem hax hbx
  one_mem' := by
    refine ⟨P.one_mem, ?_⟩
    have key : ((f ⟨1, P.one_mem⟩ : ↥R) : B) = 1 := congrArg Subtype.val (map_one f)
    rw [key]
    exact X.one_mem
  inv_mem' := by
    rintro a ⟨ha, hax⟩
    refine ⟨P.inv_mem ha, ?_⟩
    have key : ((f ⟨a⁻¹, P.inv_mem ha⟩ : ↥R) : B) = ((f ⟨a, ha⟩ : ↥R) : B)⁻¹ :=
      congrArg Subtype.val (map_inv f ⟨a, ha⟩)
    rw [key]
    exact X.inv_mem hax

private theorem mem_subPre {A B : Type} [Group A] [Group B] {P : Subgroup A} {R : Subgroup B}
    (f : ↥P ≃* ↥R) (X : Subgroup B) {x : A} :
    x ∈ subPre f X ↔ ∃ h : x ∈ P, ((f ⟨x, h⟩ : ↥R) : B) ∈ X := Iff.rfl

theorem Shape81.of_equiv {Γ' : Type} [Group Γ'] {S : Subgroup Γ} {c : Γ}
    {S' : Subgroup Γ'} {c' : Γ'} (hcS : c ∈ Subgroup.normalizer (S : Set Γ))
    (hcS' : c' ∈ Subgroup.normalizer (S' : Set Γ')) (e : ↥S ≃* ↥S')
    (he : ∀ s t : S, c * (s : Γ) * c⁻¹ = t → c' * (e s : Γ') * c'⁻¹ = e t)
    (h : Shape81 S c) : Shape81 S' c' := by
  have hcS2 : ∀ x ∈ S, c * x * c⁻¹ ∈ S := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hcS x).1 hx
  have hcS2' : ∀ x ∈ S', c' * x * c'⁻¹ ∈ S' := fun x hx =>
    (Subgroup.mem_normalizer_iff.1 hcS' x).1 hx
  have hconj : ∀ x : ↥S, c' * ((e x : ↥S') : Γ') * c'⁻¹ =
      ((e ⟨c * (x : Γ) * c⁻¹, hcS2 _ x.2⟩ : ↥S') : Γ') :=
    fun x => he x ⟨c * (x : Γ) * c⁻¹, hcS2 _ x.2⟩ rfl
  have hconjΓ : ∀ (x : Γ) (hx : x ∈ S), c' * ((e ⟨x, hx⟩ : ↥S') : Γ') * c'⁻¹ =
      ((e ⟨c * x * c⁻¹, hcS2 x hx⟩ : ↥S') : Γ') :=
    fun x hx => he ⟨x, hx⟩ ⟨c * x * c⁻¹, hcS2 x hx⟩ rfl
  rcases h with ⟨hcyc, hcent⟩ | ⟨z, hzS, hzord, hcz, hzcen, hinvol, hE, Q, hQS, hzQ, hQc, hQgen⟩
  ·
    left
    refine ⟨(MulEquiv.isCyclic e).1 hcyc, ?_⟩
    intro s' hs'
    obtain ⟨s, hs⟩ : ∃ s : ↥S, e s = ⟨s', hs'⟩ := ⟨e.symm ⟨s', hs'⟩, e.apply_symm_apply _⟩
    have h1 := he s s (hcent s.1 s.2)
    rw [hs] at h1
    exact h1
  · right
    obtain ⟨z', hz'⟩ : ∃ z' : Γ', z' = ((e ⟨z, hzS⟩ : ↥S') : Γ') := ⟨_, rfl⟩
    have hz'S : z' ∈ S' := by
      rw [hz']
      exact (e ⟨z, hzS⟩).2
    have hz'conj : c' * z' * c'⁻¹ = z' := by
      have h2 := hconjΓ z hzS
      have h3 : (⟨c * z * c⁻¹, hcS2 z hzS⟩ : ↥S) = ⟨z, hzS⟩ := Subtype.ext hcz
      rw [h3, ← hz'] at h2
      exact h2
    have hz'ord : orderOf z' = 2 := by
      rw [hz', Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
      exact hzord
    have hz'cen : ∀ s' ∈ S', s' * z' = z' * s' := by
      intro s' hs'
      have hcomm : (e.symm ⟨s', hs'⟩ : ↥S) * (⟨z, hzS⟩ : ↥S) =
          (⟨z, hzS⟩ : ↥S) * (e.symm ⟨s', hs'⟩ : ↥S) :=
        Subtype.ext (hzcen _ (e.symm ⟨s', hs'⟩).2)
      have h3 := congrArg e hcomm
      rw [map_mul, map_mul, e.apply_symm_apply] at h3
      rw [hz']
      exact congrArg Subtype.val h3
    have hz'inv : ∀ r' ∈ S', orderOf r' = 2 → r' ≠ z' → z' = (r' * (c' * r' * c'⁻¹)) ^ 2 := by
      intro r' hr' hord' hne
      obtain ⟨r, hr⟩ : ∃ r : ↥S, e r = ⟨r', hr'⟩ := ⟨e.symm ⟨r', hr'⟩, e.apply_symm_apply _⟩
      have hrord : orderOf (r : Γ) = 2 := by
        rw [Subgroup.orderOf_coe, ← MulEquiv.orderOf_eq e r, hr, Subgroup.orderOf_mk]
        exact hord'
      have hrz : (r : Γ) ≠ z := by
        intro heq
        apply hne
        have hr_eq : r = ⟨z, hzS⟩ := Subtype.ext heq
        rw [hz', ← hr_eq]
        exact congrArg Subtype.val hr.symm
      have hzeq : (⟨z, hzS⟩ : ↥S) =
          (r * (⟨c * (r : Γ) * c⁻¹, hcS2 _ r.2⟩ : ↥S)) ^ 2 :=
        Subtype.ext (hinvol (r : Γ) r.2 hrord hrz)
      have hX : e ⟨c * (r : Γ) * c⁻¹, hcS2 _ r.2⟩ = ⟨c' * r' * c'⁻¹, hcS2' _ hr'⟩ := by
        apply Subtype.ext
        have h5 := hconj r
        rw [hr] at h5
        exact h5.symm
      have h4 := congrArg e hzeq
      rw [map_pow, map_mul, hr, hX] at h4
      rw [hz']
      exact congrArg Subtype.val h4
    have hz'E : ∀ E' : Subgroup Γ', E' ≤ S' → (∀ x ∈ E', ∀ y ∈ E', x * y = y * x) →
        (∀ x ∈ E', x * x = 1) → E' ≠ ⊥ → Nat.card E' ≤ 4 ∧
          (z' ∈ E' ∨ ∃ r ∈ S', orderOf r = 2 ∧ r ≠ z' ∧ E' = Subgroup.zpowers r) := by
      intro E' hE'S hE'c hE'sq hE'bot
      have hES : subPre e E' ≤ S := fun x hx => by
        obtain ⟨hxS, _⟩ := (mem_subPre e E').1 hx
        exact hxS
      have hEc : ∀ x ∈ subPre e E', ∀ y ∈ subPre e E', x * y = y * x := by
        intro x hx y hy
        obtain ⟨hxS, hxE⟩ := (mem_subPre e E').1 hx
        obtain ⟨hyS, hyE⟩ := (mem_subPre e E').1 hy
        have key : (e ⟨x, hxS⟩ : ↥S') * e ⟨y, hyS⟩ = e ⟨y, hyS⟩ * e ⟨x, hxS⟩ :=
          Subtype.ext (hE'c _ hxE _ hyE)
        rw [← map_mul, ← map_mul] at key
        exact congrArg Subtype.val (e.injective key)
      have hEsq : ∀ x ∈ subPre e E', x * x = 1 := by
        intro x hx
        obtain ⟨hxS, hxE⟩ := (mem_subPre e E').1 hx
        have key : e ((⟨x, hxS⟩ : ↥S) * ⟨x, hxS⟩) = e 1 := by
          rw [map_mul, map_one]
          exact Subtype.ext (hE'sq _ hxE)
        exact congrArg Subtype.val (e.injective key)
      have hEbot : subPre e E' ≠ ⊥ := by
        obtain ⟨⟨a', ha'⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hE'bot
        obtain ⟨y, hy⟩ : ∃ y : ↥S, e y = ⟨a', hE'S ha'⟩ :=
          ⟨e.symm ⟨a', hE'S ha'⟩, e.apply_symm_apply _⟩
        have hyE : (y : Γ) ∈ subPre e E' := by
          refine (mem_subPre e E').2 ⟨y.2, ?_⟩
          show ((e y : ↥S') : Γ') ∈ E'
          rw [hy]
          exact ha'
        have hy1 : (y : Γ) ≠ 1 := by
          intro hy0
          have hy' : y = 1 := Subtype.ext hy0
          have h7 : (⟨a', hE'S ha'⟩ : ↥S') = 1 := by rw [← hy, hy', map_one]
          have h8 : a' = 1 := congrArg Subtype.val h7
          exact ha1 (Subtype.ext h8)
        apply Subgroup.ne_bot_iff_exists_ne_one.2
        refine ⟨⟨(y : Γ), hyE⟩, ?_⟩
        intro h
        exact hy1 (congrArg Subtype.val h)
      have hfmem : ∀ w : ↥E', ((e.symm ⟨(w : Γ'), hE'S w.2⟩ : ↥S) : Γ) ∈ subPre e E' := by
        intro w
        have h6 : e (e.symm ⟨(w : Γ'), hE'S w.2⟩) = ⟨(w : Γ'), hE'S w.2⟩ :=
          e.apply_symm_apply _
        refine (mem_subPre e E').2 ⟨(e.symm ⟨(w : Γ'), hE'S w.2⟩ : ↥S).2, ?_⟩
        show ((e (e.symm ⟨(w : Γ'), hE'S w.2⟩) : ↥S') : Γ') ∈ E'
        rw [h6]
        exact w.2
      have hinj_card : Function.Injective (fun w : ↥E' =>
          (⟨((e.symm ⟨(w : Γ'), hE'S w.2⟩ : ↥S) : Γ), hfmem w⟩ : ↥(subPre e E'))) := by
        intro w1 w2 hw
        have h7 := congrArg Subtype.val hw
        have h8 : e.symm ⟨(w1 : Γ'), hE'S w1.2⟩ = e.symm ⟨(w2 : Γ'), hE'S w2.2⟩ :=
          Subtype.ext h7
        have h9 := e.symm.injective h8
        have h10 : ((⟨(w1 : Γ'), hE'S w1.2⟩ : ↥S') : Γ') =
            ((⟨(w2 : Γ'), hE'S w2.2⟩ : ↥S') : Γ') := congrArg Subtype.val h9
        exact Subtype.ext h10
      obtain ⟨hcardE, hzcase⟩ := hE (subPre e E') hES hEc hEsq hEbot
      refine ⟨le_trans (Nat.card_le_card_of_injective _ hinj_card) hcardE, ?_⟩
      rcases hzcase with hzE | ⟨r, hrS, hrord, hrz, hEr⟩
      · left
        obtain ⟨_, hzE'⟩ := (mem_subPre e E').1 hzE
        rw [hz']
        exact hzE'
      · right
        refine ⟨((e ⟨r, hrS⟩ : ↥S') : Γ'), (e ⟨r, hrS⟩).2, ?_, ?_, ?_⟩
        · rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_mk]
          exact hrord
        · intro hne
          apply hrz
          have h10 : ((e ⟨r, hrS⟩ : ↥S') : Γ') = ((e ⟨z, hzS⟩ : ↥S') : Γ') := by
            rw [hne, hz']
          exact congrArg Subtype.val (e.injective (Subtype.ext h10))
        · ext y
          constructor
          · intro hy
            have hyS : y ∈ S' := hE'S hy
            obtain ⟨x, hx⟩ : ∃ x : ↥S, e x = ⟨y, hyS⟩ :=
              ⟨e.symm ⟨y, hyS⟩, e.apply_symm_apply _⟩
            have hxE : (x : Γ) ∈ subPre e E' := by
              refine (mem_subPre e E').2 ⟨x.2, ?_⟩
              show ((e x : ↥S') : Γ') ∈ E'
              rw [hx]
              exact hy
            rw [hEr] at hxE
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hxE
            have hxr : x = (⟨r, hrS⟩ : ↥S) ^ k :=
              Subtype.ext (by rw [Subgroup.coe_zpow]; exact hk.symm)
            have h12 : (⟨y, hyS⟩ : ↥S') = (e ⟨r, hrS⟩) ^ k := by
              rw [← hx, hxr, map_zpow]
            apply Subgroup.mem_zpowers_iff.2
            exact ⟨k, (congrArg Subtype.val h12).symm⟩
          · intro hy
            obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hy
            have hrk : r ^ k ∈ subPre e E' := by
              rw [hEr]
              exact Subgroup.mem_zpowers_iff.2 ⟨k, rfl⟩
            obtain ⟨h13, h14⟩ := (mem_subPre e E').1 hrk
            have h16' : (⟨r ^ k, h13⟩ : ↥S) = (⟨r, hrS⟩ : ↥S) ^ k :=
              Subtype.ext (by rw [Subgroup.coe_zpow])
            have h16 : e ⟨r ^ k, h13⟩ = (e ⟨r, hrS⟩) ^ k := by
              rw [h16', map_zpow]
            have h17 : ((e ⟨r, hrS⟩ ^ k : ↥S') : Γ') = ((e ⟨r, hrS⟩ : ↥S') : Γ') ^ k := by
              rw [Subgroup.coe_zpow]
            have h15 : ((e ⟨r ^ k, h13⟩ : ↥S') : Γ') = y := by
              rw [h16, h17, hk]
            rw [h15] at h14
            exact h14
    have hQ'S : subPre e.symm Q ≤ S' := fun y hy => by
      obtain ⟨h', _⟩ := (mem_subPre e.symm Q).1 hy
      exact h'
    have hcomm_le : ⁅Q, Q⁆ ≤ subPre e ⁅subPre e.symm Q, subPre e.symm Q⁆ := by
      refine Subgroup.commutator_le.2 fun a ha b hb => ?_
      have haS : a ∈ S := hQS ha
      have hbS : b ∈ S := hQS hb
      have hab : ⁅a, b⁆ ∈ S := by
        rw [commutatorElement_def]
        exact S.mul_mem (S.mul_mem (S.mul_mem haS hbS) (S.inv_mem haS)) (S.inv_mem hbS)
      have hA : ((e ⟨a, haS⟩ : ↥S') : Γ') ∈ subPre e.symm Q := by
        refine (mem_subPre e.symm Q).2 ⟨(e ⟨a, haS⟩).2, ?_⟩
        show ((e.symm (e ⟨a, haS⟩) : ↥S) : Γ) ∈ Q
        rw [MulEquiv.symm_apply_apply]
        exact ha
      have hB : ((e ⟨b, hbS⟩ : ↥S') : Γ') ∈ subPre e.symm Q := by
        refine (mem_subPre e.symm Q).2 ⟨(e ⟨b, hbS⟩).2, ?_⟩
        show ((e.symm (e ⟨b, hbS⟩) : ↥S) : Γ) ∈ Q
        rw [MulEquiv.symm_apply_apply]
        exact hb
      have h18 : (⟨⁅a, b⁆, hab⟩ : ↥S) = ⁅(⟨a, haS⟩ : ↥S), (⟨b, hbS⟩ : ↥S)⁆ := Subtype.ext rfl
      have hpush : ((e ⟨⁅a, b⁆, hab⟩ : ↥S') : Γ') =
          ⁅((e ⟨a, haS⟩ : ↥S') : Γ'), ((e ⟨b, hbS⟩ : ↥S') : Γ')⁆ := by
        rw [h18]
        exact congrArg Subtype.val (map_commutatorElement e _ _)
      refine (mem_subPre e _).2 ⟨hab, ?_⟩
      rw [hpush]
      exact Subgroup.commutator_mem_commutator hA hB
    have hz'comm : z' ∈ ⁅subPre e.symm Q, subPre e.symm Q⁆ := by
      obtain ⟨_, hmem⟩ := (mem_subPre e _).1 (hcomm_le hzQ)
      rw [hz']
      exact hmem
    have hQ'c : ∀ q' ∈ subPre e.symm Q, c' * q' * c'⁻¹ ∈ subPre e.symm Q := by
      intro q' hq'
      obtain ⟨hq'S, hq'Q⟩ := (mem_subPre e.symm Q).1 hq'
      obtain ⟨x, hx⟩ : ∃ x : ↥S, e x = ⟨q', hq'S⟩ :=
        ⟨e.symm ⟨q', hq'S⟩, e.apply_symm_apply _⟩
      have hxQ : (x : Γ) ∈ Q := by
        have hxeq : x = e.symm ⟨q', hq'S⟩ := by
          rw [← hx, MulEquiv.symm_apply_apply]
        rw [hxeq]
        exact hq'Q
      refine (mem_subPre e.symm Q).2 ⟨hcS2' _ hq'S, ?_⟩
      have hsym : e.symm ⟨c' * q' * c'⁻¹, hcS2' _ hq'S⟩ = ⟨c * (x : Γ) * c⁻¹, hcS2 _ x.2⟩ := by
        rw [MulEquiv.symm_apply_eq]
        apply Subtype.ext
        have h19 := hconj x
        rw [hx] at h19
        exact h19
      show ((e.symm ⟨c' * q' * c'⁻¹, hcS2' _ hq'S⟩ : ↥S) : Γ) ∈ Q
      rw [hsym]
      exact hQc _ hxQ
    have hQ'gen : ∀ q' ∈ subPre e.symm Q,
        q' ∈ Subgroup.closure {x | ∃ t ∈ subPre e.symm Q, x = t * (c' * t * c'⁻¹)⁻¹} := by
      have hsub : {x : Γ | ∃ t ∈ Q, x = t * (c * t * c⁻¹)⁻¹} ⊆
          ↑(subPre e (Subgroup.closure
            {x : Γ' | ∃ t ∈ subPre e.symm Q, x = t * (c' * t * c'⁻¹)⁻¹})) := by
        rintro _ ⟨t, htQ, rfl⟩
        have htS : t ∈ S := hQS htQ
        have hctS : c * t * c⁻¹ ∈ S := hcS2 t htS
        have ht' : ((e ⟨t, htS⟩ : ↥S') : Γ') ∈ subPre e.symm Q := by
          refine (mem_subPre e.symm Q).2 ⟨(e ⟨t, htS⟩).2, ?_⟩
          show ((e.symm (e ⟨t, htS⟩) : ↥S) : Γ) ∈ Q
          rw [MulEquiv.symm_apply_apply]
          exact htQ
        have hconjt : ((e ⟨c * t * c⁻¹, hctS⟩ : ↥S') : Γ') =
            c' * ((e ⟨t, htS⟩ : ↥S') : Γ') * c'⁻¹ := (hconj ⟨t, htS⟩).symm
        have h20 : ((e ⟨t * (c * t * c⁻¹)⁻¹, S.mul_mem htS (S.inv_mem hctS)⟩ : ↥S') : Γ') =
            ((e ⟨t, htS⟩ : ↥S') : Γ') * ((e ⟨c * t * c⁻¹, hctS⟩ : ↥S') : Γ')⁻¹ := by
          have h21 : e ((⟨t, htS⟩ : ↥S) * (⟨c * t * c⁻¹, hctS⟩ : ↥S)⁻¹) =
              e ⟨t, htS⟩ * (e ⟨c * t * c⁻¹, hctS⟩)⁻¹ := by
            rw [map_mul, map_inv]
          exact congrArg Subtype.val h21
        rw [SetLike.mem_coe]
        refine (mem_subPre e _).2 ⟨S.mul_mem htS (S.inv_mem hctS), ?_⟩
        refine Subgroup.subset_closure ⟨((e ⟨t, htS⟩ : ↥S') : Γ'), ht', ?_⟩
        rw [h20, hconjt]
      have hle : Subgroup.closure {x : Γ | ∃ t ∈ Q, x = t * (c * t * c⁻¹)⁻¹} ≤
          subPre e (Subgroup.closure
            {x : Γ' | ∃ t ∈ subPre e.symm Q, x = t * (c' * t * c'⁻¹)⁻¹}) :=
        (Subgroup.closure_le _).2 hsub
      intro q' hq'
      obtain ⟨hq'S, hq'Q⟩ := (mem_subPre e.symm Q).1 hq'
      obtain ⟨x, hx⟩ : ∃ x : ↥S, e x = ⟨q', hq'S⟩ :=
        ⟨e.symm ⟨q', hq'S⟩, e.apply_symm_apply _⟩
      have hxQ : (x : Γ) ∈ Q := by
        have hxeq : x = e.symm ⟨q', hq'S⟩ := by
          rw [← hx, MulEquiv.symm_apply_apply]
        rw [hxeq]
        exact hq'Q
      obtain ⟨h22, hmem⟩ := (mem_subPre e _).1 (hle (hQgen _ hxQ))
      have h23 : ((e ⟨(x : Γ), h22⟩ : ↥S') : Γ') = q' := by
        have h24 : (⟨(x : Γ), h22⟩ : ↥S) = x := rfl
        rw [h24, hx]
      rw [h23] at hmem
      exact hmem
    exact ⟨z', hz'S, hz'ord, hz'conj, hz'cen, hz'inv, hz'E, subPre e.symm Q, hQ'S, hz'comm,
      hQ'c, hQ'gen⟩

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
