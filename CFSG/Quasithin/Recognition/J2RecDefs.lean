module

public import CFSG.Quasithin.EmptyFaithful.S1421Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique

structure IsTypeH2 (G : Type) [Group G] (z : G) : Prop where
  sq : z ^ 2 = 1
  ne_one : z ≠ 1
  charTwo : CharTwo (Subgroup.centralizer ({z} : Set G))
  q8d8 : IsQ8D8 ↥(pCoreOf 2 (Subgroup.centralizer ({z} : Set G)))
  quot : Nonempty (OTwoQuot (Subgroup.centralizer ({z} : Set G)) ≃* alternatingGroup (Fin 5))
  notWeaklyClosed : ∃ g : G, g * z * g⁻¹ ∈ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ∧
    g * z * g⁻¹ ≠ z

structure J2FiveLines {G : Type*} [Group G] (d : G) (x : Fin 5 → G) : Prop where
  d_sq : d * d = 1
  x_sq : ∀ i, x i * x i = 1
  d_comm : ∀ i, Commute d (x i)
  sq_eq : ∀ i j, i ≠ j → (x i * x j) ^ 2 = d
  prod_eq : x 0 * x 1 * x 2 * x 3 * x 4 = 1

structure J2ClosingRels {G : Type*} [Group G] (d c : G) (x : Fin 5 → G) : Prop where
  c_sq : c * c = 1
  dc_pow : (d * c) ^ 5 = 1
  dc_ne : d * c ≠ 1
  cx_pow : ∀ i, (c * x i) ^ 3 = 1
  cdx_pow : ∀ i, (c * (d * x i)) ^ 5 = 1

@[expose] def J2Recognition : Prop :=
  ∀ (G : Type) [Group G] [Finite G], IsSimpleGroup G → (∃ a b : G, a * b ≠ b * a) →
    ∀ z : G, IsTypeH2 G z → involutionClassCount G = 2 →
      Nonempty (G ≃* CFSG.Blueprint.NativeSporadic.J2)

end CFSG.Quasithin
