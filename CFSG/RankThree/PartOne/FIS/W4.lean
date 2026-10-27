module

public import CFSG.Fischer.Classification.Basic.ClassT
public import CFSG.Fischer.Classification.Basic.Small
public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.RankThree.PartOne.FIS

open CFSG.Blueprint.Fischer CFSG.Fischer CFSG.Fischer.Classification

@[expose] def cjProd {X : Type} [Group X] (x p q : X) : X := (p * q) * x * (p * q)

theorem cjProd_comm {X : Type} [Group X] (x : X) {p q : X} (h : p * q = q * p) :
    cjProd x p q = cjProd x q p := by
  simp only [cjProd, h]

theorem conj_cjProd {X : Type} [Group X] (x : X) {u v w : X} (huu : u * u = 1)
    (huv : u * v = v * u) (huw : u * w = w * u) (hvw : v * w = w * v) :
    (u * v) * cjProd x u w * (u * v) = cjProd x v w := by
  have h1 : (u * v) * (u * w) = v * w := by
    calc (u * v) * (u * w) = u * (v * u) * w := by simp only [mul_assoc]
      _ = u * (u * v) * w := by rw [← huv]
      _ = (u * u) * (v * w) := by simp only [mul_assoc]
      _ = v * w := by rw [huu, one_mul]
  have h2 : (u * w) * (u * v) = v * w := by
    calc (u * w) * (u * v) = u * (w * u) * v := by simp only [mul_assoc]
      _ = u * (u * w) * v := by rw [← huw]
      _ = (u * u) * (w * v) := by simp only [mul_assoc]
      _ = v * w := by rw [huu, one_mul, hvw]
  calc (u * v) * cjProd x u w * (u * v)
      = ((u * v) * (u * w)) * x * ((u * w) * (u * v)) := by simp only [cjProd, mul_assoc]
    _ = cjProd x v w := by rw [h1, h2]; rfl

theorem cjProd_self {X : Type} [Group X] (x : X) {a b : X} (h : (a * b) * (a * b) = 1) :
    (a * b) * cjProd x a b * (a * b) = x := by
  calc (a * b) * cjProd x a b * (a * b)
      = ((a * b) * (a * b)) * x * ((a * b) * (a * b)) := by simp only [cjProd, mul_assoc]
    _ = x := by rw [h, one_mul, mul_one]

theorem cjProd_commute {X : Type} [Group X] (x : X) {u v w : X} (huu : u * u = 1)
    (hvv : v * v = 1) (huv : u * v = v * u) (huw : u * w = w * u) (hvw : v * w = w * v)
    (hx : x * cjProd x v w = cjProd x v w * x) :
    cjProd x u v * cjProd x u w = cjProd x u w * cjProd x u v := by
  have haa : (u * v) * (u * v) = 1 := by
    calc (u * v) * (u * v) = u * (v * u) * v := by simp only [mul_assoc]
      _ = u * (u * v) * v := by rw [← huv]
      _ = (u * u) * (v * v) := by simp only [mul_assoc]
      _ = 1 := by rw [huu, hvv, mul_one]
  have h1 := cjProd_self x haa
  have h2 := conj_cjProd x huu huv huw hvw
  have hmul : ∀ P Q : X, (u * v) * (P * Q) * (u * v) =
      ((u * v) * P * (u * v)) * ((u * v) * Q * (u * v)) := by
    intro P Q
    calc (u * v) * (P * Q) * (u * v)
        = (u * v) * P * ((u * v) * (u * v)) * Q * (u * v) := by
          rw [haa]; simp only [mul_assoc, mul_one]
      _ = ((u * v) * P * (u * v)) * ((u * v) * Q * (u * v)) := by simp only [mul_assoc]
  have key : (u * v) * (cjProd x u v * cjProd x u w) * (u * v) =
      (u * v) * (cjProd x u w * cjProd x u v) * (u * v) := by
    rw [hmul, hmul, h1, h2]
    exact hx
  exact mul_left_cancel (mul_right_cancel key)

theorem w4 {X : Type} [Group X] {E : Set X} (hP : Pair X E) {x d e e' : X}
    (hx : x ∈ E) (hd : d ∈ E) (he : e ∈ E) (he' : e' ∈ E)
    (hde : d * e = e * d) (hde' : d * e' = e' * d) (hee' : e * e' = e' * e)
    (hdne : d ≠ e) (hdne' : d ≠ e') (hene' : e ≠ e')
    (hxd : x * d ≠ d * x) (hxe : x * e ≠ e * x) (hxe' : x * e' ≠ e' * x) :
    ∃ y₁ ∈ LocalClass E x, ∃ y₂ ∈ LocalClass E x, ∃ y₃ ∈ LocalClass E x,
      y₁ ≠ y₂ ∧ y₁ ≠ y₃ ∧ y₂ ≠ y₃ ∧ y₁ * y₂ = y₂ * y₁ ∧ y₁ * y₃ = y₃ * y₁ ∧
        y₂ * y₃ = y₃ * y₂ := by
  have hdd := Pair.mul_self hP hd
  have hee := Pair.mul_self hP he
  have hff := Pair.mul_self hP he'
  have hsq : ∀ p q : X, p ∈ E → q ∈ E → p * q = q * p → (p * q) * (p * q) = 1 := by
    intro p q hp hq hpq
    calc (p * q) * (p * q) = p * (q * p) * q := by simp only [mul_assoc]
      _ = p * (p * q) * q := by rw [← hpq]
      _ = (p * p) * (q * q) := by simp only [mul_assoc]
      _ = 1 := by rw [Pair.mul_self hP hp, Pair.mul_self hP hq, mul_one]
  have hmem : ∀ p q : X, p ∈ E → q ∈ E → p * q = q * p → cjProd x p q ∈ E := by
    intro p q hp hq hpq
    have hi : (p * q)⁻¹ = p * q := inv_eq_of_mul_eq_one_right (hsq p q hp hq hpq)
    have := Pair.conj_mem hP hx (p * q)
    rwa [hi] at this
  have hcomm : ∀ p q : X, p ∈ E → q ∈ E → p * q = q * p → p * x ≠ x * p → x * q ≠ q * x →
      x * cjProd x p q = cjProd x p q * x := by
    intro p q hp hq hpq hpx hxq
    exact Pair.commute_conj_of_path hP hp hx hq hpq hpx hxq
  have hne : ∀ p q : X, p ∈ E → q ∈ E → p * q = q * p → p ≠ q → x * p ≠ p * x →
      x * q ≠ q * x → cjProd x p q ≠ x := by
    intro p q hp hq hpq hpne hxp hxq h
    apply Pair.not_commute_mul hP hp hq hx hpq hpne hxp hxq
    have h1 := hsq p q hp hq hpq
    have h2 : (p * q) * x = x * (p * q) := by
      calc (p * q) * x = (p * q) * x * ((p * q) * (p * q)) := by rw [h1, mul_one]
        _ = cjProd x p q * (p * q) := by simp only [cjProd, mul_assoc]
        _ = x * (p * q) := by rw [h]
    exact h2.symm
  have hxd' : d * x ≠ x * d := fun h => hxd h.symm
  have hxe'' : e * x ≠ x * e := fun h => hxe h.symm
  have hxf'' : e' * x ≠ x * e' := fun h => hxe' h.symm
  have hc1 := hcomm d e hd he hde hxd' hxe
  have hc2 := hcomm d e' hd he' hde' hxd' hxe'
  have hc3 := hcomm e e' he he' hee' hxe'' hxe'
  have hn1 := hne d e hd he hde hdne hxd hxe
  have hn2 := hne d e' hd he' hde' hdne' hxd hxe'
  have hn3 := hne e e' he he' hee' hene' hxe hxe'
  have hy₁ : cjProd x d e ∈ LocalClass E x :=
    ⟨hmem d e hd he hde, hn1, (hc1).symm⟩
  have hy₂ : cjProd x d e' ∈ LocalClass E x :=
    ⟨hmem d e' hd he' hde', hn2, (hc2).symm⟩
  have hy₃ : cjProd x e e' ∈ LocalClass E x :=
    ⟨hmem e e' he he' hee', hn3, (hc3).symm⟩
  have c12 := cjProd_comm x hde.symm
  have c13 := cjProd_comm x hde'.symm
  have c23 := cjProd_comm x hee'.symm
  have h12 := cjProd_commute x hdd hee hde hde' hee' hc3
  have h13 := cjProd_commute x hee hdd hde.symm hee' hde' hc2
  have h23 := cjProd_commute x hff hdd hde'.symm hee'.symm hde hc1
  rw [c12] at h13
  rw [c13, c23] at h23
  refine ⟨_, hy₁, _, hy₂, _, hy₃, ?_, ?_, ?_, h12, h13, h23⟩
  · intro h
    have e1 := conj_cjProd x hdd hde hde' hee'
    rw [← h, cjProd_self x (hsq d e hd he hde)] at e1
    exact hn3 e1.symm
  · intro h
    have e1 := conj_cjProd x hee hde.symm hee' hde'
    rw [← h, ← c12, cjProd_self x (hsq e d he hd hde.symm)] at e1
    exact hn2 e1.symm
  · intro h
    have e1 := conj_cjProd x hff hde'.symm hee'.symm hde
    rw [c23, ← h, ← c13, cjProd_self x (hsq e' d he' hd hde'.symm)] at e1
    exact hn1 e1.symm

end CFSG.RankThree.PartOne.FIS
