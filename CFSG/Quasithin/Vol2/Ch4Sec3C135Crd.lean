module

public import CFSG.Quasithin.Vol2.Ch4Sec3C135H1

public section

namespace CFSG.Quasithin.H13.Ch4.C135

open Matrix CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.Ch4

variable {G : Type} [Group G] {A V Z : Subgroup G} {F : Type} [Field F] {k : ℕ}
  {α : ↥A →* ↥(StatedSL 3 F)} {dual : Bool}

noncomputable def crdHom (h : IsSumOfNaturalModulesVia A V Z α dual k) :
    ↥V →* Multiplicative (Fin k → Fin 3 → F) :=
  Classical.choose h.2.2

theorem crdHom_spec (h : IsSumOfNaturalModulesVia A V Z α dual k) :
    Function.Surjective (crdHom h) ∧ (crdHom h).ker = Z.subgroupOf V ∧
      ∀ (a : ↥A) (u v : ↥V), (v : G) = a * u * a⁻¹ → ∀ i : Fin k,
        Multiplicative.toAdd (crdHom h v) i =
          (moduleAct dual (α a : GL (Fin 3) F)).mulVec (Multiplicative.toAdd (crdHom h u) i) :=
  Classical.choose_spec h.2.2

noncomputable def crd (h : IsSumOfNaturalModulesVia A V Z α dual k) (v : ↥V) :
    Fin k → Fin 3 → F :=
  Multiplicative.toAdd (crdHom h v)

theorem crd_mul (h : IsSumOfNaturalModulesVia A V Z α dual k) (v w : ↥V) :
    crd h (v * w) = crd h v + crd h w := by
  simp [crd]

theorem crd_one (h : IsSumOfNaturalModulesVia A V Z α dual k) : crd h 1 = 0 := by
  simp [crd]

theorem crd_inv (h : IsSumOfNaturalModulesVia A V Z α dual k) (v : ↥V) :
    crd h v⁻¹ = -crd h v := by
  simp [crd]

theorem crd_surjective (h : IsSumOfNaturalModulesVia A V Z α dual k) :
    Function.Surjective (crd h) := fun x => by
  obtain ⟨v, hv⟩ := (crdHom_spec h).1 (Multiplicative.ofAdd x)
  exact ⟨v, by rw [crd, hv, toAdd_ofAdd]⟩

theorem crd_eq_zero_iff (h : IsSumOfNaturalModulesVia A V Z α dual k) (v : ↥V) :
    crd h v = 0 ↔ (v : G) ∈ Z := by
  have h1 := (crdHom_spec h).2.1
  rw [← Subgroup.mem_subgroupOf, ← h1, MonoidHom.mem_ker, crd]
  constructor
  · intro h2
    exact Multiplicative.toAdd.injective (h2.trans toAdd_one.symm)
  · intro h2
    rw [h2, toAdd_one]

theorem crd_eq_iff (h : IsSumOfNaturalModulesVia A V Z α dual k) (v w : ↥V) :
    crd h v = crd h w ↔ ((v⁻¹ * w : ↥V) : G) ∈ Z := by
  rw [← crd_eq_zero_iff h, crd_mul, crd_inv, neg_add_eq_zero]

theorem crd_injective (h : IsSumOfNaturalModulesVia A V ⊥ α dual k) :
    Function.Injective (crd h) := fun v w hvw => by
  rw [crd_eq_iff h, Subgroup.mem_bot] at hvw
  have h1 : v⁻¹ * w = 1 := Subtype.ext hvw
  exact (inv_mul_eq_one.mp h1)

theorem crd_conj (h : IsSumOfNaturalModulesVia A V Z α dual k) (a : ↥A) (u v : ↥V)
    (huv : (v : G) = a * u * a⁻¹) :
    crd h v = dact (moduleAct dual (α a : GL (Fin 3) F)) (crd h u) := by
  funext i
  exact (crdHom_spec h).2.2 a u v huv i

theorem crd_conj_false (h : IsSumOfNaturalModulesVia A V Z α false k) (a : ↥A) (u v : ↥V)
    (huv : (v : G) = a * u * a⁻¹) :
    crd h v = dact ((slNat α a : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
      (crd h u) := by
  rw [crd_conj h a u v huv, moduleAct_false_eq]

theorem crd_conj_true (h : IsSumOfNaturalModulesVia A V Z α true k) (a : ↥A) (u v : ↥V)
    (huv : (v : G) = a * u * a⁻¹) :
    crd h v = dact ((dualHom (slNat α a) : SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) (crd h u) := by
  rw [crd_conj h a u v huv, moduleAct_true_eq]

theorem slNat_surjective (hα : Function.Surjective α) : Function.Surjective (slNat α) :=
  ((specialLinearGroupEquivStatedSL 3 F).symm.surjective).comp hα

theorem slNat_eq_one_iff (a : ↥A) : slNat (F := F) α a = 1 ↔ α a = 1 := by
  rw [slNat, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]

end CFSG.Quasithin.H13.Ch4.C135

end
