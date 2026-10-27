module

public import CFSG.Quasithin.Vol2.F134MatCode20
public import CFSG.Blueprint.NativeSporadic
public import CFSG.Blueprint.MatrixSeedIdentification
import all CFSG.Blueprint.NativeSporadic

public section

namespace CFSG.Quasithin.F134

open CFSG.Blueprint.NativeSporadic Matrix

@[expose] def hsMA : List (List ℕ) :=
  [[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 1, 0, 1, 1, 0, 0, 1, 0, 1, 0, 1, 0, 1, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 1, 1, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0],
  [1, 1, 1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0],
  [0, 1, 1, 0, 1, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0, 0, 0, 1, 0, 0, 0, 1, 0],
  [0, 1, 1, 0, 1, 1, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1]]

@[expose] def hsMB : List (List ℕ) :=
  [[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 1, 0, 1, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 1, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  [1, 0, 1, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  [1, 0, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 1, 0, 0, 1, 0, 1, 0],
  [0, 1, 1, 0, 0, 0, 1, 1, 1, 0, 1, 1, 0, 0, 1, 0, 1, 1, 0, 0],
  [0, 1, 0, 0, 1, 0, 0, 1, 1, 0, 0, 0, 1, 0, 1, 0, 0, 1, 1, 1],
  [0, 0, 1, 0, 1, 1, 0, 1, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 0, 0],
  [1, 1, 0, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 1, 1, 0, 1, 0, 1]]

@[expose] def toM20 (X : List (List ℕ)) : Matrix (Fin 20) (Fin 20) (ZMod 2) :=
  Matrix.of fun i j => (((X.getD i.val []).getD j.val 0 : ℕ) : ZMod 2)

set_option maxRecDepth 100000 in
theorem decode_hs₁ : decode 2 20 1 HSSeed1 = toM20 hsMA := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem decode_hs₂ : decode 2 20 1 HSSeed2 = toM20 hsMB := by
  decide +kernel

@[expose] def hsAC : ℕ := ofDigs (2 ^ 160)
  [2854495396046068246954393125921682314752950274, 57835590236944379700856800189699739637747023904,
   698382509103154565548183]

@[expose] def hsBC : ℕ := ofDigs (2 ^ 160)
  [738713545831443612643357095657708668678307844, 468340040609536285998713767972130682435061944320,
   824084290602081139772870]

@[expose] def hsOneC : ℕ := ofDigs (2 ^ 160)
  [178406046658877280205451737702897146191151105, 45671947944672583732595644851941669424934682880,
   604463198037828178083840]

theorem matCode20_hsA : matCode20 (toM20 hsMA) = hsAC := by decide +kernel

theorem matCode20_hsB : matCode20 (toM20 hsMB) = hsBC := by decide +kernel

theorem matCode20_one : matCode20 (1 : Matrix (Fin 20) (Fin 20) (ZMod 2)) = hsOneC := by
  decide +kernel

theorem hs_seed_pow_check : mulX20 hsAC hsAC = hsOneC ∧
    mulX20 hsBC (mulX20 hsBC (mulX20 hsBC (mulX20 hsBC hsBC))) = hsOneC := by
  decide +kernel

theorem hsMA_sq : toM20 hsMA * toM20 hsMA = 1 := matCode20_injective (by
  rw [matCode20_mul, matCode20_hsA, matCode20_one]
  exact hs_seed_pow_check.1)

theorem hsMB_pow : toM20 hsMB * (toM20 hsMB * (toM20 hsMB * (toM20 hsMB * toM20 hsMB))) = 1 :=
  matCode20_injective (by
    rw [matCode20_mul, matCode20_mul, matCode20_mul, matCode20_mul, matCode20_hsB, matCode20_one]
    exact hs_seed_pow_check.2)

theorem det_hsMA_ne_zero : (toM20 hsMA).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hsMA_sq
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

theorem det_hsMB_ne_zero : (toM20 hsMB).det ≠ 0 := by
  intro h
  have := congrArg Matrix.det hsMB_pow
  rw [Matrix.det_mul, h, zero_mul, Matrix.det_one] at this
  exact zero_ne_one this

@[expose] noncomputable def hsUA : GL (Fin 20) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (toM20 hsMA) det_hsMA_ne_zero

@[expose] noncomputable def hsUB : GL (Fin 20) (ZMod 2) :=
  Matrix.GeneralLinearGroup.mkOfDetNeZero (toM20 hsMB) det_hsMB_ne_zero

noncomputable abbrev hsGroup : Subgroup (GL (Fin 20) (ZMod 2)) := Subgroup.closure {hsUA, hsUB}

theorem hs_seedMonoid_eq : seedMonoid 2 20 1 HSSeed1 HSSeed2 =
    Submonoid.closure {toM20 hsMA, toM20 hsMB} := by
  unfold seedMonoid
  rw [decode_hs₁, decode_hs₂]

noncomputable def hsNativeEquiv : Blueprint.NativeSporadic.HS ≃* hsGroup := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change (seedMonoid 2 20 1 HSSeed1 HSSeed2)ˣ ≃* _
  rw [hs_seedMonoid_eq]
  exact matrixSeedEquiv 2 20 (by norm_num) _ _ det_hsMA_ne_zero det_hsMB_ne_zero

end CFSG.Quasithin.F134
