module

public import CFSG.Monster.GMS.S365Leech
public import CFSG.Monster.GMS.S365Native
import CFSG.Assembly.Defs
import CFSG.Monster.B.TwoA.Census.PermClasses

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ w : G}

theorem exists_conj_one
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hw : IsConj z₀ w)
    {x y x' y' : G} (hl : IsLineTriple a x y) (hl' : IsLineTriple a x' y')
    (hx : x ∈ leechQ w) (hy : y ∈ leechQ w) (hx' : x' ∈ leechQ w) (hy' : y' ∈ leechQ w) :
    ∃ g ∈ Subgroup.centralizer ({w} : Set G), g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' := by
  obtain ⟨L⟩ := exists_leechSystem_of_isConj hG hw
  have hxy : x * y ∈ leechQ w := (leechQ w).mul_mem hx hy
  have hxy' : x' * y' ∈ leechQ w := (leechQ w).mul_mem hx' hy'
  have hx0 := mem_typeSet_zero_of_isConj I hG hw L hx hl.1
  have hy0 := mem_typeSet_zero_of_isConj I hG hw L hy hl.2.1
  have hxy0 := mem_typeSet_zero_of_isConj I hG hw L hxy hl.2.2
  have hx0' := mem_typeSet_zero_of_isConj I hG hw L hx' hl'.1
  have hy0' := mem_typeSet_zero_of_isConj I hG hw L hy' hl'.2.1
  have hxy0' := mem_typeSet_zero_of_isConj I hG hw L hxy' hl'.2.2
  rw [L.mem_typeSet, L.vec_mul x hx y hy] at hxy0
  rw [L.mem_typeSet, L.vec_mul x' hx' y' hy'] at hxy0'
  obtain ⟨g₀, hg₀x, hg₀y⟩ := exists_co1Act_pair hx0.2 hy0.2 hxy0.2 hx0'.2 hy0'.2 hxy0'.2
  obtain ⟨c, hc⟩ := L.φ_surj g₀
  have hv1 : L.vec ((c : G) * x * (c : G)⁻¹) = L.vec x' := by
    rw [L.vec_conj c x hx, hc, hg₀x]
  have hv2 : L.vec ((c : G) * y * (c : G)⁻¹) = L.vec y' := by
    rw [L.vec_conj c y hy, hc, hg₀y]
  have hind : LinearIndependent (ZMod 2) fun i : Fin 2 => L.vec (![x', y'] i) := by
    have : (fun i : Fin 2 => L.vec (![x', y'] i)) = ![L.vec x', L.vec y'] := by
      funext i
      fin_cases i <;> rfl
    rw [this]
    exact Leech.linearIndependent_pair_of_add_mem (Leech.ne_zero_of_mem_co1Orbit hx0'.2)
      (Leech.ne_zero_of_mem_co1Orbit hy0'.2) hxy0'.2
  obtain ⟨p, hp, hpa⟩ := L.exists_conj_eq (a := ![(c : G) * x * (c : G)⁻¹, (c : G) * y * (c : G)⁻¹])
    (b := ![x', y']) (fun i => by fin_cases i; exacts [L.conj_mem c hx, L.conj_mem c hy])
    (fun i => by fin_cases i; exacts [hx', hy']) (fun i => by fin_cases i; exacts [hv1, hv2]) hind
  refine ⟨p * (c : G), mul_mem (L.mem_centralizer hp) c.2, ?_, ?_⟩
  · have := hpa 0
    simp only [Matrix.cons_val_zero] at this
    rw [← this]
    group
  · have := hpa 1
    simp only [Matrix.cons_val_one, Matrix.cons_val_zero] at this
    rw [← this]
    group

end S365

end CFSG.Monster.GMS
