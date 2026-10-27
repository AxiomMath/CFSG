module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.H13.ModelsSymplectic
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open CFSG.Quasithin Subgroup
open scoped commutatorElement

variable {Q : Type*} [Group Q] {V : Type*} [CommGroup V]

private def psi (a y : Q) : Q := y * (a * y * a)

private lemma psi_one {a : Q} (ha : a * a = 1) : psi a 1 = 1 := by
  simp [psi, ha]

private lemma psi_mul {L : Subgroup Q} {a : Q} (ha : a * a = 1)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    {x y : Q} (hx : x ∈ L) (hy : y ∈ L) :
    psi a (x * y) = psi a x * psi a y := by
  have hyx : y * (a * x * a) = (a * x * a) * y := hLa y hy x hx
  have hconj : a * (x * y) * a = (a * x * a) * (a * y * a) := by
    have h := (conj_mul (a := x) (b := a) (c := y)).symm
    simpa [inv_eq_of_mul_eq_one_right ha] using h
  calc
    psi a (x * y) = (x * y) * ((a * x * a) * (a * y * a)) := by rw [psi, hconj]
    _ = x * (y * (a * x * a)) * (a * y * a) := by group
    _ = x * ((a * x * a) * y) * (a * y * a) := by rw [hyx]
    _ = psi a x * psi a y := by simp only [psi]; group

private lemma psi_inv {L : Subgroup Q} {a : Q} (ha : a * a = 1)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    {y : Q} (hy : y ∈ L) :
    psi a y⁻¹ = (psi a y)⁻¹ := by
  have hyu : y * (a * y * a) = (a * y * a) * y := hLa y hy y hy
  have hainv : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hconj : a * y⁻¹ * a = (a * y * a)⁻¹ := by
    simp [mul_inv_rev, hainv, mul_assoc]
  calc
    psi a y⁻¹ = y⁻¹ * (a * y⁻¹ * a) := rfl
    _ = y⁻¹ * (a * y * a)⁻¹ := by rw [hconj]
    _ = ((a * y * a) * y)⁻¹ := (mul_inv_rev (a * y * a) y).symm
    _ = (y * (a * y * a))⁻¹ := by rw [hyu]
    _ = (psi a y)⁻¹ := rfl

private lemma psi_commute_a {L : Subgroup Q} {a : Q} (ha : a * a = 1)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    {y : Q} (hy : y ∈ L) :
    psi a y * a = a * psi a y := by
  have hyu : y * (a * y * a) = (a * y * a) * y := hLa y hy y hy
  have hua : (a * y * a) * a = a * y := by
    rw [mul_assoc, ha, mul_one]
  have hau : a * (a * y * a) = y * a := by
    rw [← mul_assoc, ← mul_assoc, ha, one_mul]
  calc
    psi a y * a = (y * (a * y * a)) * a := rfl
    _ = y * ((a * y * a) * a) := by rw [mul_assoc]
    _ = y * (a * y) := by rw [hua]
    _ = y * a * y := by rw [mul_assoc]
    _ = (a * (a * y * a)) * y := by rw [← hau]
    _ = a * ((a * y * a) * y) := by rw [mul_assoc]
    _ = a * (y * (a * y * a)) := by rw [← hyu]
    _ = a * psi a y := rfl

private def fixesA (ρ : Q →* MulAut V) (a : Q) : Set Q :=
  {x | ∀ v : V, ρ x (ρ a v * v⁻¹) = ρ a v * v⁻¹}

private lemma one_mem_fixesA (ρ : Q →* MulAut V) (a : Q) :
    (1 : Q) ∈ fixesA ρ a := by
  intro v
  simp [fixesA]

private lemma mul_mem_fixesA {ρ : Q →* MulAut V} {a x y : Q}
    (hx : x ∈ fixesA ρ a) (hy : y ∈ fixesA ρ a) :
    x * y ∈ fixesA ρ a := by
  intro v
  have hx' := hx v
  have hy' := hy v
  calc
    ρ (x * y) (ρ a v * v⁻¹) = ρ x (ρ y (ρ a v * v⁻¹)) := by
      simp [map_mul]
    _ = ρ x (ρ a v * v⁻¹) := by rw [hy']
    _ = ρ a v * v⁻¹ := hx'

private lemma inv_mem_fixesA {ρ : Q →* MulAut V} {a x : Q}
    (hx : x ∈ fixesA ρ a) : x⁻¹ ∈ fixesA ρ a := by
  intro v
  have hx' := hx v
  calc
    ρ x⁻¹ (ρ a v * v⁻¹) = (ρ x)⁻¹ (ρ a v * v⁻¹) := by rw [map_inv]
    _ = (ρ x)⁻¹ (ρ x (ρ a v * v⁻¹)) := by rw [hx']
    _ = ρ a v * v⁻¹ := by simp

private lemma conj_mem_fixesA {ρ : Q →* MulAut V} {a c x : Q} (ha : a * a = 1)
    (hca : c * a = a * c) (hx : x ∈ fixesA ρ a) :
    c * x * c⁻¹ ∈ fixesA ρ a := by
  intro v
  have hcainv : c⁻¹ * a = a * c⁻¹ := by
    have h := congrArg Inv.inv hca
    simp [mul_inv_rev, inv_eq_of_mul_eq_one_right ha] at h
    exact h.symm
  have hstep : ρ a (ρ c⁻¹ v) * (ρ c⁻¹ v)⁻¹ = ρ c⁻¹ (ρ a v * v⁻¹) := by
    calc
      ρ a (ρ c⁻¹ v) * (ρ c⁻¹ v)⁻¹ = ρ a (ρ c⁻¹ v) * ρ c⁻¹ (v⁻¹) := by
        rw [← map_inv]
      _ = ρ (a * c⁻¹) v * ρ c⁻¹ (v⁻¹) := by simp [map_mul]
      _ = ρ (c⁻¹ * a) v * ρ c⁻¹ (v⁻¹) := by rw [hcainv]
      _ = ρ c⁻¹ (ρ a v) * ρ c⁻¹ (v⁻¹) := by simp [map_mul]
      _ = ρ c⁻¹ (ρ a v * v⁻¹) := by rw [map_mul]
  have hxw : ρ x (ρ c⁻¹ (ρ a v * v⁻¹)) = ρ c⁻¹ (ρ a v * v⁻¹) := by
    rw [← hstep]
    exact hx (ρ c⁻¹ v)
  calc
    ρ (c * x * c⁻¹) (ρ a v * v⁻¹) = ρ c (ρ x (ρ c⁻¹ (ρ a v * v⁻¹))) := by
      simp [map_mul]
    _ = ρ c (ρ c⁻¹ (ρ a v * v⁻¹)) := by rw [hxw]
    _ = ρ a v * v⁻¹ := by simp

private lemma psi_conj_inv {L : Subgroup Q} {a b : Q} (ha : a * a = 1)
    (hab : a * b = b * a)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    {y : Q} (hy : y ∈ L) :
    psi a (b * y⁻¹ * b⁻¹) = b * (psi a y)⁻¹ * b⁻¹ := by
  have hyu : y * (a * y * a) = (a * y * a) * y := hLa y hy y hy
  have hyuinv : y⁻¹ * (a * y⁻¹ * a) = (a * y⁻¹ * a) * y⁻¹ := by
    have h := congrArg Inv.inv hyu
    simpa [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, mul_assoc] using h.symm
  have hbainv : b⁻¹ * a = a * b⁻¹ := by
    have h := congrArg Inv.inv hab
    simp [mul_inv_rev, inv_eq_of_mul_eq_one_right ha] at h
    exact h
  have hpsiinv : (psi a y)⁻¹ = psi a y⁻¹ := (psi_inv ha hLa hy).symm
  have hpsiinv' : (psi a y)⁻¹ = (a * y⁻¹ * a) * y⁻¹ := by
    rw [hpsiinv]
    simp only [psi]
    exact hyuinv
  have haz : a * (b * y⁻¹ * b⁻¹) * a = (a * b) * y⁻¹ * (a * b⁻¹) := by
    rw [show a * (b * y⁻¹ * b⁻¹) * a = a * b * y⁻¹ * (b⁻¹ * a) by group]
    rw [hbainv]
  calc
    psi a (b * y⁻¹ * b⁻¹) = (b * y⁻¹ * b⁻¹) * (a * (b * y⁻¹ * b⁻¹) * a) := rfl
    _ = (b * y⁻¹ * b⁻¹) * ((a * b) * y⁻¹ * (a * b⁻¹)) := by rw [haz]
    _ = b * (y⁻¹ * (a * y⁻¹ * a)) * b⁻¹ := by
      calc
        b * y⁻¹ * b⁻¹ * (a * b * y⁻¹ * (a * b⁻¹))
            = b * y⁻¹ * (b⁻¹ * a) * b * y⁻¹ * a * b⁻¹ := by group
        _ = b * y⁻¹ * (a * b⁻¹) * b * y⁻¹ * a * b⁻¹ := by rw [hbainv]
        _ = b * (y⁻¹ * (a * y⁻¹ * a)) * b⁻¹ := by group
    _ = b * ((a * y⁻¹ * a) * y⁻¹) * b⁻¹ := by rw [hyuinv]
    _ = b * (psi a y)⁻¹ * b⁻¹ := by rw [hpsiinv']

private lemma psi_commute_conj_inv {L : Subgroup Q} {a b : Q} (ha : a * a = 1)
    (hbb : b * b = 1) (hab : a * b = b * a)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    (hLb : ∀ x ∈ L, ∀ y ∈ L, x * (b * y * b) = (b * y * b) * x)
    (hLab : ∀ x ∈ L, ∀ y ∈ L,
      x * ((a * b) * y * (a * b)) = ((a * b) * y * (a * b)) * x)
    {z y : Q} (hz : z ∈ L) (hy : y ∈ L) :
    psi a z * (b * (psi a y)⁻¹ * b⁻¹) =
      (b * (psi a y)⁻¹ * b⁻¹) * psi a z := by
  let U : Q := (a * b) * y⁻¹ * (a * b)
  let W : Q := b * y⁻¹ * b
  let u : Q := a * z * a
  have hyL : y⁻¹ ∈ L := L.inv_mem hy
  have hzU : z * U = U * z := hLab z hz y⁻¹ hyL
  have hzW : z * W = W * z := hLb z hz y⁻¹ hyL
  have hconjU : a * U * a = W := by
    have h1 : a * (a * b) = b := by rw [← mul_assoc, ha, one_mul]
    have h2 : (a * b) * a = b := by rw [hab, mul_assoc, ha, mul_one]
    simp only [U]
    calc
      a * (a * b * y⁻¹ * (a * b)) * a = (a * (a * b)) * y⁻¹ * ((a * b) * a) := by
        group
      _ = b * y⁻¹ * b := by rw [h1, h2]
  have hconjW : a * W * a = U := by
    simp only [U, W]
    calc
      a * (b * y⁻¹ * b) * a = (a * b) * y⁻¹ * (b * a) := by group
      _ = (a * b) * y⁻¹ * (a * b) := by rw [← hab]
  have hcm : ∀ x y : Q, a * (x * y) * a = (a * x * a) * (a * y * a) := by
    intro x y
    have h := (conj_mul (a := x) (b := a) (c := y)).symm
    simpa [inv_eq_of_mul_eq_one_right ha] using h
  have huW : u * W = W * u := by
    have h := congrArg (fun t => a * t * a) (hLab z hz y⁻¹ hyL)
    have h1 : a * (z * U) * a = u * W := by
      rw [hcm, hconjU]
    have h2 : a * (U * z) * a = W * u := by
      rw [hcm, hconjU]
    rwa [h1, h2] at h
  have huU : u * U = U * u := by
    have h := congrArg (fun t => a * t * a) (hLb z hz y⁻¹ hyL)
    have h1 : a * (z * W) * a = u * U := by
      rw [hcm, hconjW]
    have h2 : a * (W * z) * a = U * u := by
      rw [hcm, hconjW]
    rwa [h1, h2] at h
  have hzu : z * u = u * z := hLa z hz z hz
  have hpsiU : psi a z * U = U * psi a z := by
    simpa [psi] using (Commute.mul_left hzU huU).eq
  have hpsiW : psi a z * W = W * psi a z := by
    simpa [psi] using (Commute.mul_left hzW huW).eq
  have hD : b * (psi a y)⁻¹ * b⁻¹ = U * W := by
    have hpsiinv : (psi a y)⁻¹ = psi a y⁻¹ := (psi_inv ha hLa hy).symm
    have hbinv : b⁻¹ = b := inv_eq_of_mul_eq_one_right hbb
    have hUW : U * W = b * ((a * y⁻¹ * a) * y⁻¹) * b := by
      simp only [U, W]
      calc
        ((a * b) * y⁻¹ * (a * b)) * (b * y⁻¹ * b)
            = a * b * y⁻¹ * (a * (b * b)) * y⁻¹ * b := by group
        _ = a * b * y⁻¹ * a * y⁻¹ * b := by rw [hbb, mul_one]
        _ = b * a * y⁻¹ * a * y⁻¹ * b := by rw [hab]
        _ = b * ((a * y⁻¹ * a) * y⁻¹) * b := by group
    rw [hUW, hpsiinv]
    simp only [psi, hbinv]
    have hyuinv : y⁻¹ * (a * y⁻¹ * a) = (a * y⁻¹ * a) * y⁻¹ := by
      have hyu : y * (a * y * a) = (a * y * a) * y := hLa y hy y hy
      have h := congrArg Inv.inv hyu
      simpa [mul_inv_rev, inv_eq_of_mul_eq_one_right ha, mul_assoc] using h.symm
    rw [hyuinv]
  calc
    psi a z * (b * (psi a y)⁻¹ * b⁻¹) = psi a z * (U * W) := by rw [hD]
    _ = (psi a z * U) * W := by group
    _ = (U * psi a z) * W := by rw [hpsiU]
    _ = U * (psi a z * W) := by group
    _ = U * (W * psi a z) := by rw [hpsiW]
    _ = (U * W) * psi a z := by group
    _ = (b * (psi a y)⁻¹ * b⁻¹) * psi a z := by rw [hD]

private lemma psi_commutator_mem_fixesA (ρ : Q →* MulAut V) {L : Subgroup Q} {a b : Q}
    (ha : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    (hLb : ∀ x ∈ L, ∀ y ∈ L, x * (b * y * b) = (b * y * b) * x)
    (hLab : ∀ x ∈ L, ∀ y ∈ L,
      x * ((a * b) * y * (a * b)) = ((a * b) * y * (a * b)) * x)
    (hb : b ∈ fixesA ρ a) {z y : Q} (hz : z ∈ L) (hy : y ∈ L) :
    psi a ⁅z, y⁆ ∈ fixesA ρ a := by
  let Z : Q := psi a z
  let Y : Q := psi a y
  let D : Q := b * Y⁻¹ * b⁻¹
  let X : Q := Y * D
  have hDcomm : Z * D = D * Z := by
    simpa [Z, D, Y] using
      psi_commute_conj_inv (L := L) ha hbb hab hLa hLb hLab hz hy
  have hbInv : b⁻¹ ∈ fixesA ρ a := inv_mem_fixesA hb
  have hYb : Y * b * Y⁻¹ ∈ fixesA ρ a :=
    conj_mem_fixesA ha (by simpa [Y] using psi_commute_a ha hLa hy) hb
  have hX : X ∈ fixesA ρ a := by
    have hprod : (Y * b * Y⁻¹) * b⁻¹ ∈ fixesA ρ a := mul_mem_fixesA hYb hbInv
    simpa [X, D, mul_assoc] using hprod
  have hconjX : Z * X * Z⁻¹ ∈ fixesA ρ a :=
    conj_mem_fixesA ha (by simpa [Z] using psi_commute_a ha hLa hz) hX
  have hXinv : X⁻¹ ∈ fixesA ρ a := inv_mem_fixesA hX
  have hcomm : (Z * X * Z⁻¹) * X⁻¹ ∈ fixesA ρ a := mul_mem_fixesA hconjX hXinv
  have hDZ : D * Z = Z * D := hDcomm.symm
  have hDZinv : D * Z⁻¹ = Z⁻¹ * D := by
    calc
      D * Z⁻¹ = (Z⁻¹ * Z) * D * Z⁻¹ := by group
      _ = Z⁻¹ * (Z * D) * Z⁻¹ := by group
      _ = Z⁻¹ * (D * Z) * Z⁻¹ := by rw [hDZ]
      _ = Z⁻¹ * D := by group
  have hkey : (Z * X * Z⁻¹) * X⁻¹ = Z * Y * Z⁻¹ * Y⁻¹ := by
    simp only [X]
    calc
      (Z * (Y * D) * Z⁻¹) * (Y * D)⁻¹ = Z * Y * D * Z⁻¹ * D⁻¹ * Y⁻¹ := by group
      _ = Z * Y * (D * Z⁻¹) * D⁻¹ * Y⁻¹ := by group
      _ = Z * Y * (Z⁻¹ * D) * D⁻¹ * Y⁻¹ := by rw [hDZinv]
      _ = Z * Y * Z⁻¹ * Y⁻¹ := by group
  have hpsi : psi a ⁅z, y⁆ = Z * Y * Z⁻¹ * Y⁻¹ := by
    rw [commutatorElement_def]
    rw [show z * y * z⁻¹ * y⁻¹ = (z * y) * (z⁻¹ * y⁻¹) by group]
    rw [psi_mul ha hLa (L.mul_mem hz hy) (L.mul_mem (L.inv_mem hz) (L.inv_mem hy))]
    rw [psi_mul ha hLa hz hy, psi_mul ha hLa (L.inv_mem hz) (L.inv_mem hy)]
    rw [psi_inv ha hLa hz, psi_inv ha hLa hy]
    simp only [Z, Y]
    group
  rw [hpsi, ← hkey]
  exact hcomm

theorem fixes_commV_diag_of_mem_normalizer (ρ : Q →* MulAut V) {L : Subgroup Q} {a b : Q}
    (ha : a * a = 1) (hab : a * b = b * a)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    (hbL : b ∈ normalizer (L : Set Q))
    (hLb : L ≤ closure {z | ∃ y ∈ L, z = y * b * y⁻¹ * b⁻¹})
    (hb : ∀ v : V, ρ b (ρ a v * v⁻¹) = ρ a v * v⁻¹) :
    ∀ y ∈ L, ∀ v : V, ρ (y * (a * y * a)) (ρ a v * v⁻¹) = ρ a v * v⁻¹ := by
  let S : Set Q := {z | ∃ y ∈ L, z = y * b * y⁻¹ * b⁻¹}
  have hgenL : ∀ z ∈ S, z ∈ L := by
    rintro z ⟨y, hy, rfl⟩
    have hz : b * y⁻¹ * b⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hbL y⁻¹).mp (L.inv_mem hy)
    simpa only [mul_assoc] using L.mul_mem hy hz
  have hgenF : ∀ z ∈ S, psi a z ∈ fixesA ρ a := by
    rintro z ⟨y, hy, rfl⟩
    have hyL : y ∈ L := hy
    have hz : b * y⁻¹ * b⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp hbL y⁻¹).mp (L.inv_mem hy)
    have hxeq : y * b * y⁻¹ * b⁻¹ = y * (b * y⁻¹ * b⁻¹) := by group
    have hmul : psi a (y * (b * y⁻¹ * b⁻¹)) =
        psi a y * psi a (b * y⁻¹ * b⁻¹) := psi_mul ha hLa hyL hz
    have hconj : psi a (b * y⁻¹ * b⁻¹) = b * (psi a y)⁻¹ * b⁻¹ :=
      psi_conj_inv ha hab hLa hyL
    have hYb : psi a y * b * (psi a y)⁻¹ ∈ fixesA ρ a :=
      conj_mem_fixesA ha (psi_commute_a ha hLa hyL) hb
    have hbInv : b⁻¹ ∈ fixesA ρ a := inv_mem_fixesA hb
    have hprod : (psi a y * b * (psi a y)⁻¹) * b⁻¹ ∈ fixesA ρ a :=
      mul_mem_fixesA hYb hbInv
    rw [hxeq, hmul, hconj]
    simpa [mul_assoc] using hprod
  have hclosure : ∀ x ∈ closure S, x ∈ L ∧ psi a x ∈ fixesA ρ a := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem z hz => exact ⟨hgenL z hz, hgenF z hz⟩
    | one => exact ⟨L.one_mem, by rw [psi_one ha]; exact one_mem_fixesA ρ a⟩
    | mul x y hx hy ihx ihy =>
        refine ⟨L.mul_mem ihx.1 ihy.1, ?_⟩
        rw [psi_mul ha hLa ihx.1 ihy.1]
        exact mul_mem_fixesA ihx.2 ihy.2
    | inv x hx ihx =>
        refine ⟨L.inv_mem ihx.1, ?_⟩
        rw [psi_inv ha hLa ihx.1]
        exact inv_mem_fixesA ihx.2
  intro y hy v
  exact (hclosure y (hLb hy)).2 v

theorem fixes_commV_diag_of_commute (ρ : Q →* MulAut V) {L : Subgroup Q} {a b : Q}
    (ha : a * a = 1) (hbb : b * b = 1) (hab : a * b = b * a)
    (hLa : ∀ x ∈ L, ∀ y ∈ L, x * (a * y * a) = (a * y * a) * x)
    (hLb : ∀ x ∈ L, ∀ y ∈ L, x * (b * y * b) = (b * y * b) * x)
    (hLab : ∀ x ∈ L, ∀ y ∈ L, x * ((a * b) * y * (a * b)) = ((a * b) * y * (a * b)) * x)
    (hperf : ⁅L, L⁆ = L) (hb : ∀ v : V, ρ b (ρ a v * v⁻¹) = ρ a v * v⁻¹) :
    ∀ y ∈ L, ∀ v : V, ρ (y * (a * y * a)) (ρ a v * v⁻¹) = ρ a v * v⁻¹ := by
  have hb' : b ∈ fixesA ρ a := hb
  have hprop : ∀ x ∈ (⁅L, L⁆ : Subgroup Q), x ∈ L ∧ psi a x ∈ fixesA ρ a := by
    intro x hx
    rw [Subgroup.commutator_def] at hx
    induction hx using Subgroup.closure_induction with
    | mem z hz =>
        obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hz
        refine ⟨?_, ?_⟩
        · rw [commutatorElement_def]
          exact L.mul_mem (L.mul_mem (L.mul_mem hg₁ hg₂) (L.inv_mem hg₁))
            (L.inv_mem hg₂)
        · exact psi_commutator_mem_fixesA ρ ha hbb hab hLa hLb hLab hb' hg₁ hg₂
    | one => exact ⟨L.one_mem, by rw [psi_one ha]; exact one_mem_fixesA ρ a⟩
    | mul x y hx hy ihx ihy =>
        refine ⟨L.mul_mem ihx.1 ihy.1, ?_⟩
        rw [psi_mul ha hLa ihx.1 ihy.1]
        exact mul_mem_fixesA ihx.2 ihy.2
    | inv x hx ihx =>
        refine ⟨L.inv_mem ihx.1, ?_⟩
        rw [psi_inv ha hLa ihx.1]
        exact inv_mem_fixesA ihx.2
  intro y hy v
  exact (hprop y (hperf.ge hy)).2 v

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
