module

public import CFSG.Sporadic.J4.Group

public noncomputable section

namespace CFSG.Quasithin.H13.J4

open CFSG.Sporadic.J4 Matrix

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def u : GL (Fin 112) (ZMod 2) :=
  (gA * gB) ^ (-9 : ℤ) * (gA * gB * gA * gB * gB) ^ 5 * (gA * gB) ^ 9

@[expose] def v : GL (Fin 112) (ZMod 2) :=
  (gA * gB ^ 3) ^ 16 * (gA * gB * gA * gB * gA * gB * gB) ^ 8 * (gA * gB ^ 3) ^ 21

abbrev W : Subgroup (GL (Fin 112) (ZMod 2)) := Subgroup.closure {u, v}

@[expose] def d : GL (Fin 112) (ZMod 2) := v⁻¹ * u * v * u

@[expose] def t : GL (Fin 112) (ZMod 2) := d ^ 22

@[expose] def r : GL (Fin 112) (ZMod 2) := d ^ 11

@[expose] def coreBasisConjugators : List (List ℤ) :=
  [[], [2], [-2], [1, -2], [2, 1, -2], [-2, 1, -2], [1, 2, 1, -2], [1, -2, 1, -2],
    [2, 1, 2, 1, -2], [-2, 1, 2, 1, -2], [2, 1, -2, 1, -2], [-2, 1, -2, 1, -2]]

@[expose] def uvGen (i : ℕ) : GL (Fin 112) (ZMod 2) := if i = 0 then u else if i = 1 then v else 1

@[expose] def conjugator (i : Fin 12) : GL (Fin 112) (ZMod 2) :=
  wordProd uvGen (coreBasisConjugators.getD i [])

@[expose] def rConj (i : Fin 12) : GL (Fin 112) (ZMod 2) := conjugator i * r * (conjugator i)⁻¹

abbrev P : Subgroup (GL (Fin 112) (ZMod 2)) := Subgroup.closure (insert t (Set.range rConj))

@[expose] def kerT : Submodule (ZMod 2) (Fin 112 → ZMod 2) :=
  LinearMap.ker (Matrix.toLin' ((t : Matrix (Fin 112) (Fin 112) (ZMod 2)) + 1))

@[expose] def imT : Submodule (ZMod 2) (Fin 112 → ZMod 2) :=
  LinearMap.range (Matrix.toLin' ((t : Matrix (Fin 112) (Fin 112) (ZMod 2)) + 1))

@[expose] def QT : Type := kerT ⧸ imT.comap kerT.subtype

instance : AddCommGroup QT := inferInstanceAs (AddCommGroup (kerT ⧸ imT.comap kerT.subtype))

instance : Module (ZMod 2) QT := inferInstanceAs (Module (ZMod 2) (kerT ⧸ imT.comap kerT.subtype))

@[expose] def QT.mk : kerT →ₗ[ZMod 2] QT := (imT.comap kerT.subtype).mkQ

theorem QT.mk_surjective : Function.Surjective QT.mk := Submodule.mkQ_surjective _

theorem QT.mk_eq_mk_iff {x y : kerT} :
    QT.mk x = QT.mk y ↔ (x : Fin 112 → ZMod 2) - y ∈ imT := by
  show Submodule.Quotient.mk x = Submodule.Quotient.mk y ↔ _
  rw [Submodule.Quotient.eq, Submodule.mem_comap, Submodule.coe_subtype, Submodule.coe_sub]

theorem mulVec_mem_kerT {g : GL (Fin 112) (ZMod 2)} (hg : g ∈ Subgroup.centralizer {t})
    {x : Fin 112 → ZMod 2} (hx : x ∈ kerT) :
    (g : Matrix (Fin 112) (Fin 112) (ZMod 2)) *ᵥ x ∈ kerT := by
  have hc : t * g = g * t := Subgroup.mem_centralizer_iff.1 hg t rfl
  have hcm : (t : Matrix (Fin 112) (Fin 112) (ZMod 2)) * g = g * t := by
    rw [← Units.val_mul, hc, Units.val_mul]
  simp only [kerT, LinearMap.mem_ker, Matrix.toLin'_apply] at hx ⊢
  have e : ((t : Matrix (Fin 112) (Fin 112) (ZMod 2)) + 1) * g = g * (t + 1) := by
    rw [Matrix.add_mul, Matrix.mul_add, hcm, Matrix.one_mul, Matrix.mul_one]
  rw [Matrix.mulVec_mulVec, e, ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_zero]

theorem mulVec_mem_imT {g : GL (Fin 112) (ZMod 2)} (hg : g ∈ Subgroup.centralizer {t})
    {x : Fin 112 → ZMod 2} (hx : x ∈ imT) :
    (g : Matrix (Fin 112) (Fin 112) (ZMod 2)) *ᵥ x ∈ imT := by
  have hc : t * g = g * t := Subgroup.mem_centralizer_iff.1 hg t rfl
  have hcm : (t : Matrix (Fin 112) (Fin 112) (ZMod 2)) * g = g * t := by
    rw [← Units.val_mul, hc, Units.val_mul]
  obtain ⟨y, rfl⟩ := hx
  refine ⟨(g : Matrix (Fin 112) (Fin 112) (ZMod 2)) *ᵥ y, ?_⟩
  simp only [Matrix.toLin'_apply]
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.add_mul, Matrix.mul_add, hcm,
    Matrix.one_mul, Matrix.mul_one]

@[expose] def kerMap (g : Subgroup.centralizer ({t} : Set (GL (Fin 112) (ZMod 2)))) :
    kerT →ₗ[ZMod 2] kerT :=
  (Matrix.toLin' ((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2))).restrict
    fun _ hx => by rw [Matrix.toLin'_apply]; exact mulVec_mem_kerT g.2 hx

theorem kerMap_apply (g : Subgroup.centralizer ({t} : Set (GL (Fin 112) (ZMod 2))))
    (x : kerT) :
    (kerMap g x : Fin 112 → ZMod 2) =
      ((g : GL (Fin 112) (ZMod 2)) : Matrix (Fin 112) (Fin 112) (ZMod 2)) *ᵥ x := by
  rw [kerMap, LinearMap.coe_restrict_apply, Matrix.toLin'_apply]

theorem kerMap_le (g : Subgroup.centralizer ({t} : Set (GL (Fin 112) (ZMod 2)))) :
    imT.comap kerT.subtype ≤ (imT.comap kerT.subtype).comap (kerMap g) := by
  intro x hx
  simp only [Submodule.mem_comap, Submodule.coe_subtype] at hx ⊢
  rw [kerMap_apply]
  exact mulVec_mem_imT g.2 hx

@[expose] def quotMap (g : Subgroup.centralizer ({t} : Set (GL (Fin 112) (ZMod 2)))) :
    QT →ₗ[ZMod 2] QT :=
  (imT.comap kerT.subtype).mapQ (imT.comap kerT.subtype) (kerMap g) (kerMap_le g)

theorem quotMap_mk (g : Subgroup.centralizer ({t} : Set (GL (Fin 112) (ZMod 2)))) (x : kerT) :
    quotMap g (QT.mk x) = QT.mk (kerMap g x) := rfl

@[expose] def quotAction : Subgroup.centralizer ({t} : Set (GL (Fin 112) (ZMod 2))) →*
    LinearMap.GeneralLinearGroup (ZMod 2) QT :=
  MonoidHom.toHomUnits
    { toFun := quotMap
      map_one' := by
        refine LinearMap.ext fun q => ?_
        obtain ⟨x, rfl⟩ := QT.mk_surjective q
        rw [quotMap_mk, Module.End.one_apply]
        have e : kerMap 1 x = x := Subtype.ext (by
          rw [kerMap_apply, OneMemClass.coe_one, Units.val_one, Matrix.one_mulVec])
        rw [e]
      map_mul' := fun g h => by
        refine LinearMap.ext fun q => ?_
        obtain ⟨x, rfl⟩ := QT.mk_surjective q
        rw [Module.End.mul_apply, quotMap_mk, quotMap_mk, quotMap_mk]
        have e : kerMap (g * h) x = kerMap g (kerMap h x) := Subtype.ext (by
          rw [kerMap_apply, kerMap_apply, kerMap_apply, Subgroup.coe_mul, Units.val_mul,
            Matrix.mulVec_mulVec])
        rw [e] }

theorem quotAction_mk (g : Subgroup.centralizer ({t} : Set (GL (Fin 112) (ZMod 2))))
    (x : kerT) :
    (quotAction g : QT →ₗ[ZMod 2] QT) (QT.mk x) = QT.mk (kerMap g x) := rfl

end CFSG.Quasithin.H13.J4
