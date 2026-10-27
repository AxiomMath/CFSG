module

public import Mathlib.GroupTheory.Index
public import Mathlib.Tactic.Group

public section

namespace CFSG.Quasithin.H13.U43

variable {G : Type} [Group G]

theorem card_eq_ncard_mul_card_inf_centralizer (N : Subgroup G) (Ω : Set G) (x : G)
    (hΩ : ∀ g ∈ N, ∀ y ∈ Ω, g * y * g⁻¹ ∈ Ω) (hx : x ∈ Ω)
    (htr : ∀ y ∈ Ω, ∃ g ∈ N, g * x * g⁻¹ = y) :
    Nat.card ↥N = Ω.ncard * Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) := by
  classical
  let _ : MulAction ↥N G :=
    MulAction.compHom G ((ConjAct.toConjAct : G ≃* ConjAct G).toMonoidHom.comp N.subtype)
  have hsmul : ∀ (g : ↥N) (y : G), g • y = (g : G) * y * (g : G)⁻¹ := fun g y => by
    show ConjAct.toConjAct (g : G) • y = _
    rw [ConjAct.smul_def]
    simp
  have horb : MulAction.orbit ↥N x = Ω := by
    ext y
    constructor
    · rintro ⟨g, rfl⟩
      show g • x ∈ Ω
      rw [hsmul]
      exact hΩ g g.2 x hx
    · intro hy
      obtain ⟨g, hg, rfl⟩ := htr y hy
      exact ⟨⟨g, hg⟩, hsmul _ _⟩
  have hstab : Nat.card (MulAction.stabilizer ↥N x) =
      Nat.card ↥(N ⊓ Subgroup.centralizer ({x} : Set G)) :=
    Nat.card_congr
      { toFun := fun g => ⟨(g : ↥N), Subgroup.mem_inf.mpr ⟨g.1.2, by
          have e : ((g : ↥N) • x : G) = x := g.2
          rw [hsmul] at e
          rw [Subgroup.mem_centralizer_singleton_iff]
          calc ((g : ↥N) : G) * x
              = (((g : ↥N) : G) * x * ((g : ↥N) : G)⁻¹) * ((g : ↥N) : G) := by group
            _ = x * ((g : ↥N) : G) := by rw [e]⟩⟩
        invFun := fun g => ⟨⟨g, (Subgroup.mem_inf.mp g.2).1⟩, by
          have hg := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp g.2).2
          show (⟨(g : G), _⟩ : ↥N) • x = x
          rw [hsmul]
          calc (g : G) * x * (g : G)⁻¹ = (x * (g : G)) * (g : G)⁻¹ := by rw [hg]
            _ = x := by group⟩
        left_inv := fun g => rfl
        right_inv := fun g => rfl }
  have h1 := Subgroup.card_mul_index (MulAction.stabilizer ↥N x)
  rw [MulAction.index_stabilizer, horb, hstab] at h1
  rw [← h1, mul_comm]

theorem mem_normalizer_of_forward [Finite G] {X : Subgroup G} {g : G}
    (h : ∀ x ∈ X, g * x * g⁻¹ ∈ X) : g ∈ Subgroup.normalizer (X : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨h x, fun hx => ?_⟩
  let φ : ↥X → ↥X := fun v => ⟨g * v * g⁻¹, h v v.2⟩
  have hinj : Function.Injective φ := by
    intro v v' hvv
    have : g * (v : G) * g⁻¹ = g * (v' : G) * g⁻¹ := congrArg Subtype.val hvv
    exact Subtype.ext (by simpa using this)
  obtain ⟨v, hv⟩ := Finite.surjective_of_injective hinj ⟨g * x * g⁻¹, hx⟩
  have : g * (v : G) * g⁻¹ = g * x * g⁻¹ := congrArg Subtype.val hv
  have hvx : (v : G) = x := by simpa using this
  rw [← hvx]
  exact v.2

theorem conj_mem_closure {S : Set G} {g : G}
    (h : ∀ y ∈ S, g * y * g⁻¹ ∈ Subgroup.closure S) {x : G} (hx : x ∈ Subgroup.closure S) :
    g * x * g⁻¹ ∈ Subgroup.closure S := by
  have : Subgroup.closure S ≤ (Subgroup.closure S).comap (MulAut.conj g).toMonoidHom :=
    (Subgroup.closure_le _).mpr fun y hy => h y hy
  simpa using this hx

end CFSG.Quasithin.H13.U43
