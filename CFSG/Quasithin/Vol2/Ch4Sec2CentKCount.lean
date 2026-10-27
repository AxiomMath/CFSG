module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCoord

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Quasithin CFSG.Quasithin.A4 CFSG.Assembly.LowTwoRank Matrix
open CFSG.Open hiding StatedSL
open scoped commutatorElement

variable {G : Type} [Group G]

theorem omega_inf_eq_of_card {K Q V R : Subgroup G} {F : Type} [Field F] [Fintype F]
    {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥Q →* Multiplicative (Fin 2 → Fin 3 → F)}
    (hco : CoordData K Q F α β) {g₀ : G} (hg₀K : g₀ ∈ K) (hg₀α : α ⟨g₀, hg₀K⟩ ≠ 1)
    (hg₀R : g₀ ∈ R) (hVQ : V ≤ Q) (hVΩ : V ≤ omegaOneCenterOf R)
    (hVcard : Nat.card ↥V = Fintype.card F ^ 4) :
    omegaOneCenterOf R ⊓ Q ≤ V ∧ ∀ q ∈ Q, q ∈ V ↔ g₀ * q = q * g₀ := by
  have hΩle : omegaOneCenterOf R ≤ R ⊓ Subgroup.centralizer (R : Set G) :=
    (Subgroup.closure_le _).mpr fun _ hx => hx.1
  have hΩC : ∀ x ∈ omegaOneCenterOf R, x ∈ Subgroup.centralizer ({g₀} : Set G) := by
    intro x hx
    have hxC : x ∈ Subgroup.centralizer (R : Set G) := (Subgroup.mem_inf.mp (hΩle hx)).2
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    rw [Set.mem_singleton_iff.mp hh]
    exact (Subgroup.mem_centralizer_iff.mp hxC) g₀ hg₀R
  have hVC : V ≤ Q ⊓ Subgroup.centralizer ({g₀} : Set G) := fun v hv =>
    Subgroup.mem_inf.mpr ⟨hVQ hv, hΩC v (hVΩ hv)⟩
  have hCcard : Nat.card ↥(Q ⊓ Subgroup.centralizer ({g₀} : Set G)) ≤ Nat.card ↥V := by
    rw [hVcard]
    exact card_inf_centralizer_le hco hg₀K hg₀α
  haveI : Finite ↥Q := Finite.of_injective _ hco.inj
  haveI : Finite ↥(Q ⊓ Subgroup.centralizer ({g₀} : Set G)) :=
    Finite.of_injective
      (Subgroup.inclusion (inf_le_left : Q ⊓ Subgroup.centralizer ({g₀} : Set G) ≤ Q))
      (Subgroup.inclusion_injective _)
  have hVeq : V = Q ⊓ Subgroup.centralizer ({g₀} : Set G) :=
    Subgroup.eq_of_le_of_card_ge hVC hCcard
  refine ⟨fun x hx => ?_, fun q hq => ?_⟩
  · rw [hVeq]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hx).2, hΩC x (Subgroup.mem_inf.mp hx).1⟩
  · rw [hVeq, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, h⟩
      exact (Subgroup.mem_centralizer_iff.mp h) g₀ (Set.mem_singleton g₀)
    · intro h
      refine ⟨hq, Subgroup.mem_centralizer_iff.mpr fun y hy => ?_⟩
      rw [Set.mem_singleton_iff.mp hy]
      exact h

end CFSG.Quasithin.H13.Ch4.CentK
