module

public import CFSG.Quasithin.Vol2.Ch10SecKRSr
public import CFSG.Quasithin.Vol2.Ch10SecKRSzb
public import CFSG.Quasithin.Vol2.Ch10SecKRSzc

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique C10P4F
open scoped Matrix

set_option maxRecDepth 4000 in
theorem trvE_mul_self : ∀ (a b : Fin 5) (h : a ≠ b), trvE a b h * trvE a b h = 1 := by decide

set_option maxRecDepth 4000 in
theorem trvE_transpose : ∀ (a b : Fin 5) (h : a ≠ b),
    ((trvE a b h : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2))ᵀ =
      ((trvE b a (Ne.symm h) : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by decide

theorem tw_true_trvE (a b : Fin 5) (h : a ≠ b) :
    ((tw true (trvE a b h) : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      ((trvE b a (Ne.symm h) : SL5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
  rw [tw_true, inv_eq_of_mul_eq_one_right (trvE_mul_self a b h), trvE_transpose]

theorem eq_zero_of_eq_add_single {x : Fin 5 → ZMod 2} {c : ZMod 2} {a : Fin 5}
    (h : x = x + c • Pi.single a 1) : c = 0 := by
  have h1 := congrFun h a
  simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_same, smul_eq_mul, mul_one] at h1
  have key : ∀ y z : ZMod 2, y = y + z → z = 0 := by decide
  exact key _ _ h1

variable {G : Type} [Group G]

namespace MultiCoord

variable {J W : Subgroup G} {k : ℕ} (C : MultiCoord J W k)

theorem comp_eq_zero_nat {v : G} (hv : v ∈ W) {j : ↥J} (hjv : (j : G) * v * (j : G)⁻¹ = v)
    {a b : Fin 5} (hab : a ≠ b) (hj : C.ρ j = trvE a b hab) {i : Fin k} (hi : C.dual i = false) :
    C.E v i b = 0 := by
  have h1 := C.conj j v hv i
  rw [hjv, hi, hj, tw_false, ← smul_eq_mulVec', trvE_mulVec] at h1
  exact eq_zero_of_eq_add_single h1

theorem comp_eq_zero_dual {v : G} (hv : v ∈ W) {j : ↥J} (hjv : (j : G) * v * (j : G)⁻¹ = v)
    {a b : Fin 5} (hab : a ≠ b) (hj : C.ρ j = trvE a b hab) {i : Fin k} (hi : C.dual i = true) :
    C.E v i a = 0 := by
  have h1 := C.conj j v hv i
  rw [hjv, hi, hj, tw_true_trvE, ← smul_eq_mulVec', trvE_mulVec] at h1
  exact eq_zero_of_eq_add_single h1

end MultiCoord

variable [Finite G] {T L I J : Subgroup G} {t w : G}

theorem Conf.false_of_multi_triv (c : Conf T L I t w J) {k : ℕ}
    (C : MultiCoord J (VI T L I J w) k) (hV1W : fsuUL T L I ≤ VI T L I J w) (S : Fin k → Prop)
    {i₀ : Fin k} (hi₀ : S i₀)
    (hS : ∀ v ∈ fsuUL T L I, ∀ l ∈ L, ∀ i, S i → C.E (l * v * l⁻¹) i = C.E v i) : False := by
  let Y : Subgroup G :=
    { carrier := {v | v ∈ VI T L I J w ∧ ∀ i, S i → C.E v i = 0}
      one_mem' := ⟨Subgroup.one_mem _, fun i _ => by rw [C.E_one]; rfl⟩
      mul_mem' := fun {a b} ha hb => ⟨Subgroup.mul_mem _ ha.1 hb.1, fun i hi => by
        rw [C.map_mul a ha.1 b hb.1, Pi.add_apply, ha.2 i hi, hb.2 i hi, add_zero]⟩
      inv_mem' := fun {a} ha => ⟨Subgroup.inv_mem _ ha.1, fun i hi => by
        rw [C.E_inv ha.1, ha.2 i hi]⟩ }
  have hV1Y : fsuUL T L I ≤ Y := by
    rw [← commutator_fsuUL_eq c.hyp, Subgroup.commutator_le]
    intro v hv l hl
    have hvW := hV1W hv
    have hlv : l * v * l⁻¹ ∈ VI T L I J w := C.conj_mem ⟨l, c.le hl⟩ hvW
    rw [commutatorElement_def, show v * l * v⁻¹ * l⁻¹ = v * (l * v * l⁻¹)⁻¹ by group]
    refine ⟨Subgroup.mul_mem _ hvW (Subgroup.inv_mem _ hlv), fun i hi => ?_⟩
    rw [C.map_mul v hvW _ (Subgroup.inv_mem _ hlv), C.E_inv hlv, Pi.add_apply, hS v hv l hl i hi,
      add_self_vec]
  have hJY : J ≤ Subgroup.normalizer (Y : Set G) := fun j hj =>
    mem_normalizer_of_conj_mem fun y hy => ⟨C.conj_mem ⟨j, hj⟩ hy.1, fun i hi => by
      rw [show j * y * j⁻¹ = ((⟨j, hj⟩ : ↥J) : G) * y * ((⟨j, hj⟩ : ↥J) : G)⁻¹ from rfl,
        C.conj _ y hy.1 i, hy.2 i hi, Matrix.mulVec_zero]⟩
  have hVY : VI T L I J w ≤ Y := Conf.VI_le_of c hJY (inf_le_left.trans hV1Y)
  obtain ⟨v, hv, hEv⟩ := C.surj fun i => if i = i₀ then Pi.single 0 1 else 0
  have h1 := (hVY hv).2 i₀ hi₀
  rw [hEv] at h1
  have h2 := congrFun h1 0
  simp at h2

theorem Conf.lstar_data (c : Conf T L I t w J) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (ρ : ↥J →* SL5) (hρ : Function.Surjective ρ)
    (hker : ∀ j : ↥J, ρ j = 1 → ∃ m : ℕ, (j : G) ^ 2 ^ m = 1)
    (hU : ∀ j : ↥J, ρ j ∈ uniSL 5 ↔ (j : G) ∈ T ⊓ Subgroup.centralizer ({w} : Set G))
    (eL : ↥L ⧸ CFSG.pCore 2 ↥L ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :
    uniSL 5 ≤ Subgroup.normalizer ((piL ρ c.le).range : Set SL5) ∧
      ⁅(piL ρ c.le).range, (piL ρ c.le).range⁆ = (piL ρ c.le).range ∧
      Nonempty (↥(piL ρ c.le).range ⧸ CFSG.pCore 2 ↥(piL ρ c.le).range ≃*
        Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) := by
  refine ⟨fun g hg => ?_, image_perfect ρ c.le (SecA.perfect_L c.hyp.fsu.maximal.1),
    image_quot_equiv ρ c.le hker eL⟩
  obtain ⟨j, rfl⟩ := hρ g
  exact rho_mem_normalizer ρ c.le j.2 (c.Tw_le_T1 h37 h38 ((hU j).mp hg)).2

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS
