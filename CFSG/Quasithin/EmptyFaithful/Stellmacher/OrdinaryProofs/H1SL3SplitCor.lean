module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitHom
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3SplitTop

public section

namespace CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

open CFSG.Assembly.LowTwoRank CFSG.Quasithin
open scoped commutatorElement

theorem conj_trivial_mod {G : Type} [Group G] (S : AbelSub G) {X Z W A L : Subgroup G}
    (hXS : X ≤ S.carrier) (hZS : Z ≤ S.carrier) (hWX : W ≤ X)
    (hXn : A ≤ Subgroup.normalizer (X : Set G))
    (hZW : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ * z⁻¹ ∈ W)
    (hsup : X ⊔ Z = S.carrier) (hLA : L ≤ A) :
    ∀ l ∈ L, ∀ x ∈ S.carrier, l * x * l⁻¹ * x⁻¹ ∈ X := by
  have hcS : ∀ y ∈ S.carrier, ∀ e ∈ S.carrier, y * e * y⁻¹ = e := by
    intro y hy e he
    rw [S.comm y hy e he]
    group
  let C : Subgroup G :=
    { carrier := {x | x ∈ S.carrier ∧ ∀ l ∈ L, l * x * l⁻¹ * x⁻¹ ∈ X}
      one_mem' := by
        refine ⟨S.carrier.one_mem, fun l _ => ?_⟩
        simp only [mul_one, one_mul, inv_one, mul_inv_cancel]
        exact X.one_mem
      mul_mem' := by
        intro x y hx hy
        obtain ⟨hxS, hxL⟩ := hx
        obtain ⟨hyS, hyL⟩ := hy
        refine ⟨S.carrier.mul_mem hxS hyS, fun l hl => ?_⟩
        have ex := hxL l hl
        have ey := hyL l hl
        have key : l * (x * y) * l⁻¹ * (x * y)⁻¹ =
            (l * x * l⁻¹ * x⁻¹) * (x * (l * y * l⁻¹ * y⁻¹) * x⁻¹) := by
          group
        rw [key, hcS x hxS _ (hXS ey)]
        exact X.mul_mem ex ey
      inv_mem' := by
        intro x hx
        obtain ⟨hxS, hxL⟩ := hx
        refine ⟨S.carrier.inv_mem hxS, fun l hl => ?_⟩
        have ex := hxL l hl
        have key : l * x⁻¹ * l⁻¹ * (x⁻¹)⁻¹ =
            x⁻¹ * (l * x * l⁻¹ * x⁻¹)⁻¹ * (x⁻¹)⁻¹ := by
          group
        rw [key, hcS (x⁻¹) (S.carrier.inv_mem hxS) _ (S.carrier.inv_mem (hXS ex))]
        exact X.inv_mem ex }
  have hXC : X ≤ C := by
    intro x hx
    refine ⟨hXS hx, fun l hl => ?_⟩
    have hconj : l * x * l⁻¹ ∈ X := ((Subgroup.mem_normalizer_iff.mp (hXn (hLA hl)) x).mp hx)
    exact X.mul_mem hconj (X.inv_mem hx)
  have hZC : Z ≤ C := by
    intro z hz
    refine ⟨hZS hz, fun l hl => ?_⟩
    exact hWX (hZW l (hLA hl) z hz)
  have hSC : X ⊔ Z ≤ C := sup_le hXC hZC
  rw [hsup] at hSC
  intro l hl x hx
  exact (hSC hx).2 l hl

theorem comm_mem_of_hom {G : Type} [Group G] (S : AbelSub G) {X L : Subgroup G}
    (hS2 : ∀ x ∈ S.carrier, x * x = 1)
    (hL2 : ∀ f : ↥L →* Multiplicative (ZMod 2), f = 1) (v : G)
    (hvS : ∀ l ∈ L, v * l * v⁻¹ * l⁻¹ ∈ S.carrier)
    (htriv : ∀ l ∈ L, ∀ x ∈ S.carrier, l * x * l⁻¹ * x⁻¹ ∈ X) :
    ∀ l ∈ L, v * l * v⁻¹ * l⁻¹ ∈ X := by
  letI : Module (ZMod 2) (S.quot X) := AbelSub.quotZMod S X hS2
  let cS : ↥L → S.carrier := fun l => ⟨v * (l : G) * v⁻¹ * (l : G)⁻¹, hvS l l.2⟩
  have hconjS : ∀ a b : ↥L, (a : G) * (v * (b : G) * v⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ ∈ S.carrier := by
    intro a b
    have h : (a : G) * (v * (b : G) * v⁻¹ * (b : G)⁻¹) * (a : G)⁻¹ =
        (v * (a : G) * v⁻¹ * (a : G)⁻¹)⁻¹ * (v * ((a : G) * (b : G)) * v⁻¹ * ((a : G) * (b : G))⁻¹) := by
      group
    rw [h]
    exact S.carrier.mul_mem (S.carrier.inv_mem (hvS a a.2))
      (hvS ((a : G) * (b : G)) (L.mul_mem a.2 b.2))
  have hsplit : ∀ a b : ↥L, (QuotientGroup.mk (cS (a * b)) : S.carrier ⧸ X.subgroupOf S.carrier) =
      QuotientGroup.mk (cS a) * QuotientGroup.mk (cS b) := by
    intro a b
    have hel : cS (a * b) = cS a * ⟨(a : G) * (v * (b : G) * v⁻¹ * (b : G)⁻¹) * (a : G)⁻¹,
        hconjS a b⟩ := Subtype.ext (by
          simp only [cS, Subgroup.coe_mul]
          group)
    rw [hel, QuotientGroup.mk_mul]
    congr 1
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have h := htriv (a : G) a.2 ((cS b : S.carrier) : G)⁻¹ (S.carrier.inv_mem (cS b).2)
    convert h using 1
    simp only [cS, Subgroup.coe_mul, Subgroup.coe_inv]
    group
  let f : ↥L →* Multiplicative (S.quot X) :=
    { toFun := fun l => Multiplicative.ofAdd (Additive.ofMul (QuotientGroup.mk (cS l)))
      map_one' := by
        have h1 : cS 1 = 1 := Subtype.ext (by simp [cS])
        rw [h1, QuotientGroup.mk_one] <;> rfl
      map_mul' := by
        intro a b
        rw [hsplit a b] <;> rfl }
  intro l hl
  have h1 := hom_trivial_of_hom_zmod2 hL2 f ⟨l, hl⟩
  have h2 : (QuotientGroup.mk (cS ⟨l, hl⟩) : S.carrier ⧸ X.subgroupOf S.carrier) = 1 := h1
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h2)

theorem eq_of_isSum_of_commutator_eq {G : Type} [Group G] {F : Type} [Field F]
    [Fintype F] [CharP F 2] (hF : 4 ≤ Fintype.card F) {A V Z W : Subgroup G}
    {α : ↥A →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) {dual : Bool} {k : ℕ}
    (hV : IsSumOfNaturalModulesVia A V Z α dual k)
    (hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hV2 : ∀ x ∈ V, x * x = 1)
    (hWZ : W ≤ Z) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hZW : ∀ a ∈ A, ∀ z ∈ Z, a * z * a⁻¹ * z⁻¹ ∈ W)
    (hker : ∀ a : ↥A, α a = 1 → ∀ v ∈ V, (a : G) * v * (a : G)⁻¹ * v⁻¹ ∈ W)
    {V₀ L : Subgroup G} (hLA : L ≤ A) (hcomm : ⁅V₀, L⁆ = V)
    (hL2 : ∀ f : ↥L →* Multiplicative (ZMod 2), f = 1) : Z = W := by
  obtain ⟨S, rfl⟩ : ∃ S : AbelSub G, S.carrier = V := ⟨⟨V, hVab⟩, rfl⟩
  have hS2 : ∀ x ∈ S.carrier, x * x = 1 := hV2
  have hZS : Z ≤ S.carrier := hV.2.1
  obtain ⟨X, hWX, hXS, hAX, hXZ, hsup⟩ :=
    exists_complement_of_isSum hF hα hV hVab hV2 hWZ hAW hZW hker
  have htriv := conj_trivial_mod S hXS hZS hWX hAX hZW hsup hLA
  have hvS : ∀ v ∈ V₀, ∀ l ∈ L, v * l * v⁻¹ * l⁻¹ ∈ S.carrier := by
    intro v hv l hl
    rw [← hcomm]
    have key : v * l * v⁻¹ * l⁻¹ = ⁅v, l⁆ := (commutatorElement_def v l).symm
    rw [key]
    exact Subgroup.commutator_mem_commutator hv hl
  have hcommX : ⁅V₀, L⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro h hh k hk
    have hk' := comm_mem_of_hom S hS2 hL2 h (fun l hl => hvS h hh l hl) htriv k hk
    rw [commutatorElement_def]
    exact hk'
  have hVX : S.carrier ≤ X := by
    rw [← hcomm]
    exact hcommX
  refine le_antisymm ?_ hWZ
  intro z hz
  have hzX : z ∈ X ⊓ Z := ⟨hVX (hZS hz), hz⟩
  rw [hXZ] at hzX
  exact hzX

end CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.H1SL3

end
