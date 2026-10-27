module

public import CFSG.Quasithin.EmptyFaithful.S14117Basic
public import CFSG.Quasithin.EmptyFaithful.S1417Natural

public section

namespace CFSG.Quasithin.S153D

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1417
open scoped commutatorElement

section Commutator

variable {G : Type*} [Group G]

theorem commutator_subgroupOf_eq' {M X Y : Subgroup G} (hX : X ≤ M) (hY : Y ≤ M) :
    ⁅X, Y⁆.subgroupOf M = ⁅X.subgroupOf M, Y.subgroupOf M⁆ := by
  have h1 : ⁅X, Y⁆ ≤ M := Subgroup.commutator_le.mpr fun x hx y hy => by
    rw [commutatorElement_def]
    exact M.mul_mem (M.mul_mem (M.mul_mem (hX hx) (hY hy)) (M.inv_mem (hX hx)))
      (M.inv_mem (hY hy))
  apply Subgroup.map_injective M.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le h1, Subgroup.map_commutator,
    Subgroup.map_subgroupOf_eq_of_le hX, Subgroup.map_subgroupOf_eq_of_le hY]

theorem autOn_commutator {V X R : Subgroup G} (hX : X ≤ Subgroup.normalizer (V : Set G))
    (hR : R ≤ Subgroup.normalizer (V : Set G)) :
    autOn ⁅X, R⁆ V = ⁅autOn X V, autOn R V⁆ := by
  unfold autOn
  rw [commutator_subgroupOf_eq' hX hR, Subgroup.map_commutator]

theorem isSolvable_autOn {V K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G))
    (hs : Group.IsSolvable ↥K) : Group.IsSolvable ↥(autOn K V) := by
  have h1 : Group.IsSolvable ↥(K.subgroupOf (Subgroup.normalizer (V : Set G))) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hK).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hK).injective
  exact Group.isSolvable_of_surjective (f := (conjAct V).subgroupMap
    (K.subgroupOf (Subgroup.normalizer (V : Set G)))) ((conjAct V).subgroupMap_surjective _)

end Commutator

theorem not_isSolvable_of_isQuasisimple {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  intro hs
  have hnt : Nontrivial Q := CFSG.LocalCores.isQuasisimple_nontrivial hQ
  have hp : commutator Q = ⊤ := Group.isPerfect_def.mp hQ.1
  obtain ⟨n, hn⟩ := hs.solvable
  have hall : ∀ k : ℕ, derivedSeries Q k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [derivedSeries_succ, ih]; exact hp
  rw [hall n] at hn
  obtain ⟨a, b, hab⟩ := exists_pair_ne Q
  exact hab (by
    have ha : a ∈ (⊥ : Subgroup Q) := hn ▸ Subgroup.mem_top a
    have hb : b ∈ (⊥ : Subgroup Q) := hn ▸ Subgroup.mem_top b
    rw [Subgroup.mem_bot] at ha hb
    rw [ha, hb])

theorem commutator_eq_bot_of_quasisimple {Γ : Type*} [Group Γ] {A B : Subgroup Γ}
    (hA : CFSG.IsQuasisimple ↥A) (h : ⁅A, B⁆ ≤ Subgroup.centralizer (A : Set Γ)) :
    ⁅A, B⁆ = ⊥ :=
  CFSG.LocalCores.perfect_double_commutator hA.1
    (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h)

section LeOfAutOn

variable {G : Type} [Group G]

theorem le_of_autOn_le {I U X MI : Subgroup G} (hUN : I ≤ Subgroup.normalizer (U : Set G))
    (hXI : X ≤ I) (hMI : MI ≤ I) (hcent : I ⊓ Subgroup.centralizer (U : Set G) ≤ MI)
    (h : autOn X U ≤ autOn MI U) : X ≤ MI := by
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (U : Set G) := hUN (hXI hx)
  have hmem : conjAct U ⟨x, hxN⟩ ∈ autOn X U := mem_autOn_iff_exists.mpr ⟨x, hxN, hx, rfl⟩
  obtain ⟨m, hmN, hmM, hm⟩ := mem_autOn_iff_exists.mp (h hmem)
  have h1 : conjAct U (⟨x, hxN⟩ * ⟨m, hmN⟩⁻¹) = 1 := by
    rw [map_mul, map_inv, hm, mul_inv_cancel]
  have h2 : x * m⁻¹ ∈ Subgroup.centralizer (U : Set G) := A4.conjAct_eq_one_iff.mp h1
  have h3 : x * m⁻¹ ∈ I ⊓ Subgroup.centralizer (U : Set G) :=
    ⟨I.mul_mem (hXI hx) (I.inv_mem (hMI hmM)), h2⟩
  have : x = (x * m⁻¹) * m := by group
  rw [this]
  exact MI.mul_mem (hcent h3) hmM

end LeOfAutOn

end CFSG.Quasithin.S153D
