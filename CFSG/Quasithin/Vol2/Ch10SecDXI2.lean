module

public import CFSG.Quasithin.Vol2.Ch10SecDXI
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Vol2.Ch10SecDGroup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Quasithin
open scoped IsMulCommutative

section Coord

variable {V : Type*} [CommGroup V] {Gp : Subgroup (MulAut V)}

@[expose] def coord (D : L3Data Gp ⊤ ⊥) (u : V) : L3.Vec :=
  Multiplicative.toAdd (D.β ⟨u, trivial⟩)

theorem coord_mul (D : L3Data Gp ⊤ ⊥) (a b : V) : coord D (a * b) = coord D a + coord D b := by
  unfold coord
  have e : (⟨a * b, trivial⟩ : ↥(⊤ : Subgroup V)) = ⟨a, trivial⟩ * ⟨b, trivial⟩ := rfl
  rw [e, map_mul, toAdd_mul]

theorem coord_one (D : L3Data Gp ⊤ ⊥) : coord D 1 = 0 := by
  unfold coord
  have e : (⟨1, trivial⟩ : ↥(⊤ : Subgroup V)) = 1 := rfl
  rw [e, map_one, toAdd_one]

theorem coord_inv (D : L3Data Gp ⊤ ⊥) (a : V) : coord D a⁻¹ = - coord D a := by
  unfold coord
  have e : (⟨a⁻¹, trivial⟩ : ↥(⊤ : Subgroup V)) = (⟨a, trivial⟩)⁻¹ := rfl
  rw [e, map_inv, toAdd_inv]

theorem coord_injective (D : L3Data Gp ⊤ ⊥) : Function.Injective (coord D) := by
  intro a b hab
  have hβinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (D.ker_β u).mp hu
    rw [Subgroup.mem_bot] at this
    exact Subtype.ext this
  exact congrArg Subtype.val (hβinj (Multiplicative.toAdd.injective hab))

theorem coord_rho (D : L3Data Gp ⊤ ⊥) (γ : L3.Γ) (u : V) :
    coord D (D.rho γ u) = L3.act γ (coord D u) := by
  unfold coord
  rw [D.β_rho γ u trivial trivial, toAdd_ofAdd]

end Coord

variable {G : Type} [Group G] {W : Subgroup G} [IsMulCommutative ↥W]
  {Gp : Subgroup (MulAut ↥W)}

theorem mem_kOf_of_rho (D : L3Data Gp ⊤ ⊥) {g v : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    (hv : v ∈ W) (hgv : g * v = v * g) {γ : L3.Γ} (hγ : D.rho γ = conjAct W ⟨g, hg⟩)
    (hA : γ ∈ L3.AS {0, coord D ⟨v, hv⟩}) : g ∈ kOf W v := by
  refine ⟨hg, hgv, fun u hu => ?_⟩
  have hAu : L3.act γ (coord D ⟨u, hu⟩) - coord D ⟨u, hu⟩ ∈
      ({0, coord D ⟨v, hv⟩} : Finset L3.Vec) := by
    unfold L3.AS at hA
    exact (Finset.mem_filter.mp hA).2 _
  have hc : coord D (conjAct W ⟨g, hg⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥W)⁻¹) =
      L3.act γ (coord D ⟨u, hu⟩) - coord D ⟨u, hu⟩ := by
    rw [coord_mul, coord_inv, ← hγ, coord_rho, sub_eq_add_neg]
    rfl
  have hcoe : ((conjAct W ⟨g, hg⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥W)⁻¹ : ↥W) : G) =
      g * u * g⁻¹ * u⁻¹ := rfl
  rcases Finset.mem_insert.mp hAu with h0 | h0
  · have h1 : conjAct W ⟨g, hg⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥W)⁻¹ = 1 :=
      coord_injective D (by rw [hc, h0, coord_one])
    rw [← hcoe, h1]
    exact Subgroup.one_mem _
  · have h1 : conjAct W ⟨g, hg⟩ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥W)⁻¹ = ⟨v, hv⟩ :=
      coord_injective D (by rw [hc, Finset.mem_singleton.mp h0])
    rw [← hcoe, h1]
    exact Subgroup.mem_zpowers v

theorem act_coord_of_rho (D : L3Data Gp ⊤ ⊥) {g v : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    (hv : v ∈ W) (hgv : g * v = v * g) {γ : L3.Γ} (hγ : D.rho γ = conjAct W ⟨g, hg⟩) :
    L3.act γ (coord D ⟨v, hv⟩) = coord D ⟨v, hv⟩ := by
  rw [← coord_rho, hγ]
  congr 1
  apply Subtype.ext
  show g * v * g⁻¹ = v
  rw [hgv, mul_inv_cancel_right]

theorem pow_eq_one_of_rho (D : L3Data Gp ⊤ ⊥) {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    {γ : L3.Γ} (hγ : D.rho γ = conjAct W ⟨g, hg⟩) {n : ℕ} (hn : g ^ n = 1) : γ ^ n = 1 := by
  apply D.rho_injective
  rw [map_pow, hγ, map_one, ← map_pow]
  have : (⟨g, hg⟩ : ↥(Subgroup.normalizer (W : Set G))) ^ n = 1 := Subtype.ext (by simp [hn])
  rw [this, map_one]

theorem ne_one_of_rho (D : L3Data Gp ⊤ ⊥) {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    {γ : L3.Γ} (hγ : D.rho γ = conjAct W ⟨g, hg⟩)
    (hgC : g ∉ Subgroup.centralizer (W : Set G)) : γ ≠ 1 := by
  rintro rfl
  apply hgC
  have : conjAct W ⟨g, hg⟩ = 1 := by rw [← hγ, map_one]
  exact (conjAct_eq_one_iff _).mp this

theorem rho_mul_of (D : L3Data Gp ⊤ ⊥) {g h : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    (hh : h ∈ Subgroup.normalizer (W : Set G)) {γ δ : L3.Γ} (hγ : D.rho γ = conjAct W ⟨g, hg⟩)
    (hδ : D.rho δ = conjAct W ⟨h, hh⟩) :
    D.rho (γ * δ) = conjAct W ⟨g * h, Subgroup.mul_mem _ hg hh⟩ := by
  rw [map_mul, hγ, hδ, ← map_mul]
  rfl

theorem rho_inv_of (D : L3Data Gp ⊤ ⊥) {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    {γ : L3.Γ} (hγ : D.rho γ = conjAct W ⟨g, hg⟩) :
    D.rho γ⁻¹ = conjAct W ⟨g⁻¹, Subgroup.inv_mem _ hg⟩ := by
  rw [map_inv, hγ, ← map_inv]
  rfl

theorem rho_pow_of (D : L3Data Gp ⊤ ⊥) {g : G} (hg : g ∈ Subgroup.normalizer (W : Set G))
    {γ : L3.Γ} (hγ : D.rho γ = conjAct W ⟨g, hg⟩) (n : ℕ) :
    D.rho (γ ^ n) = conjAct W ⟨g ^ n, Subgroup.pow_mem _ hg n⟩ := by
  rw [map_pow, hγ, ← map_pow]
  rfl

end CFSG.Quasithin.Vol2.Ch10.SecD
