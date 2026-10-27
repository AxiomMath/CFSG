module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKDefs

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix
open CFSG.Open hiding StatedSL
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem mulVec_coord_of_conj_eq {K Q : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    (hco : CoordData K Q F α β) (k : ↥K) (q : ↥Q) (h : (k : G) * q * (k : G)⁻¹ = q) (i : Fin 2) :
    (matOf (α k)).mulVec (coord β q i) = coord β q i :=
  (hco.eq k q q h.symm i).symm

private theorem matOf_eq_one_of_fix {F : Type} [Field F] {M : Matrix (Fin 3) (Fin 3) F}
    (h : ∀ x : Fin 3 → F, M *ᵥ x = x) : M = 1 := by
  refine Matrix.ext_of_mulVec_single fun j => ?_
  rw [Matrix.one_mulVec]
  exact h _

private theorem eq_one_of_matOf_eq_one {F : Type} [Field F] {g : ↥(StatedSL 3 F)}
    (h : matOf g = 1) : g = 1 :=
  Subtype.ext (Units.ext h)

private theorem exists_coord_zero_eq {K Q : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    (hco : CoordData K Q F α β) (x : Fin 3 → F) : ∃ q : ↥Q, coord β q 0 = x := by
  obtain ⟨q, hq⟩ := hco.surj (Multiplicative.ofAdd ![x, 0])
  exact ⟨q, by simp [coord, hq]⟩

theorem inf_centralizer_le_pCoreOf {K Q : Subgroup G} {F : Type} [Field F]
    {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    (hco : CoordData K Q F α β) (hker : α.ker = CFSG.pCore 2 ↥K) (hQK : Q ≤ K) :
    K ⊓ Subgroup.centralizer (K : Set G) ≤ pCoreOf 2 K := by
  rintro g ⟨hgK, hgC⟩
  have hcomm : ∀ q : ↥Q, (g : G) * (q : G) * g⁻¹ = q := by
    intro q
    have h := Subgroup.mem_centralizer_iff.mp hgC (q : G) (hQK q.2)
    rw [← h, mul_inv_cancel_right]
  have hfix : ∀ x : Fin 3 → F, (matOf (α ⟨g, hgK⟩)).mulVec x = x := by
    intro x
    obtain ⟨q, hq⟩ := exists_coord_zero_eq hco x
    have h := mulVec_coord_of_conj_eq hco ⟨g, hgK⟩ q (hcomm q) 0
    rwa [hq] at h
  have ha1 : (⟨g, hgK⟩ : ↥K) ∈ α.ker :=
    MonoidHom.mem_ker.mpr (eq_one_of_matOf_eq_one (matOf_eq_one_of_fix hfix))
  rw [hker] at ha1
  exact Subgroup.mem_map_of_mem K.subtype ha1

theorem card_inf_centralizer_le {K Q : Subgroup G} {F : Type} [Field F] [Fintype F]
    {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    (hco : CoordData K Q F α β) {g : G} (hg : g ∈ K) (hg1 : α ⟨g, hg⟩ ≠ 1) :
    Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) ≤ Fintype.card F ^ 4 := by
  set M : Matrix (Fin 3) (Fin 3) F := matOf (α ⟨g, hg⟩)
  let ℓ : Submodule F (Fin 3 → F) := LinearMap.ker (Matrix.mulVecLin M - LinearMap.id)
  have hmemℓ : ∀ x, x ∈ ℓ ↔ M *ᵥ x = x := fun x => by
    simp [ℓ, LinearMap.mem_ker, sub_eq_zero]
  have hℓ : ℓ ≠ ⊤ := by
    intro htop
    refine hg1 (eq_one_of_matOf_eq_one (matOf_eq_one_of_fix fun x => (hmemℓ x).mp ?_))
    rw [htop]
    exact Submodule.mem_top
  have hdim : Module.finrank F ℓ ≤ 2 := by
    have h := Submodule.finrank_lt hℓ
    rw [Module.finrank_fin_fun] at h
    omega
  have hcent : ∀ x : ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)),
      g * (x : G) * g⁻¹ = (x : G) := by
    intro x
    have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp x.2).2 g (Set.mem_singleton g)
    rw [h, mul_inv_cancel_right]
  let qOf : ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) → ↥Q :=
    fun x => ⟨(x : G), (Subgroup.mem_inf.mp x.2).1⟩
  let φ : ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) → (Fin 2 → ↥ℓ) := fun x i =>
    ⟨coord β (qOf x) i, (hmemℓ _).mpr (mulVec_coord_of_conj_eq hco ⟨g, hg⟩ (qOf x) (hcent x) i)⟩
  have hφ : Function.Injective φ := by
    intro x y hxy
    have h1 : β (qOf x) = β (qOf y) := by
      apply Multiplicative.toAdd.injective
      funext i
      exact congrArg Subtype.val (congrFun hxy i)
    have h2 : ((qOf x : ↥Q) : G) = ((qOf y : ↥Q) : G) := congrArg Subtype.val (hco.inj h1)
    exact Subtype.ext h2
  have hcardφ : Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) ≤ Nat.card (Fin 2 → ↥ℓ) :=
    Nat.card_le_card_of_injective φ hφ
  have hℓcard : Nat.card ↥ℓ = Fintype.card F ^ Module.finrank F ℓ := by
    rw [Module.natCard_eq_pow_finrank (K := F) (V := ↥ℓ), Nat.card_eq_fintype_card]
  have hfin : Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) ≤ (Fintype.card F ^ 2) ^ 2 := by
    calc Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) ≤ Nat.card (Fin 2 → ↥ℓ) := hcardφ
      _ = (Fintype.card F ^ Module.finrank F ℓ) ^ 2 := by
          rw [Nat.card_fun, Nat.card_fin, hℓcard]
      _ ≤ (Fintype.card F ^ 2) ^ 2 :=
          Nat.pow_le_pow_left (Nat.pow_le_pow_right Fintype.card_pos hdim) 2
  calc Nat.card ↥(Q ⊓ Subgroup.centralizer ({g} : Set G)) ≤ (Fintype.card F ^ 2) ^ 2 := hfin
    _ = Fintype.card F ^ 4 := by ring

end CFSG.Quasithin.H13.Ch4.CentK
