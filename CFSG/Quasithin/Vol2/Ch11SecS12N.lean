module

public import CFSG.Quasithin.Vol2.Ch11SecS12B
public import CFSG.Quasithin.Vol2.Ch11SecS12G
public import CFSG.Quasithin.Background.C3Defs

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.OperatorJH

variable {G : Type} [Group G] [Finite G]

section LSeries

variable {L X : Subgroup G} {x : G} {F : Type} [Field F] {α₀ : ↥L →* ↥(StatedSL 2 F)}

omit [Finite G] in
theorem isNatEigSection_one {C S : Subgroup G} {a : F} (h : IsNatEigSection L x α₀ C S a) :
    IsNatEigSection L 1 α₀ C S 1 := by
  obtain ⟨β, hs, hk, hK, -⟩ := h
  refine ⟨β, hs, hk, hK, fun c c' hc' => ?_⟩
  have : c' = c := Subtype.ext (by simpa using hc')
  rw [this, one_smul]

theorem exists_isLabSeries_L (hα : Function.Surjective α₀) :
    ∀ (l : List (Subgroup G × Option F)) (C D : Subgroup G),
      IsLabSeries (L ⊔ X) L x α₀ C l D →
        ∃ l' : List (Subgroup G × Option F), IsLabSeries L L 1 α₀ C l' D := by
  intro l
  induction l with
  | nil =>
    intro C D h
    exact ⟨[], h⟩
  | cons p l ih =>
    intro C D h
    obtain ⟨hf, hl⟩ := h
    obtain ⟨l₂, hl₂⟩ := ih p.1 D hl
    have hLC : L ≤ Subgroup.normalizer (C : Set G) := le_sup_left.trans hf.2.2.1
    have hLS : L ≤ Subgroup.normalizer (p.1 : Set G) := le_sup_left.trans hf.2.2.2.1
    rcases hp : p.2 with _ | a
    ·
      have hc := hf.2.2.2.2.2
      rw [hp] at hc
      obtain ⟨l₁, hl₁, -⟩ := exists_isLabSeries_central (Y := L) (K := L) (x := 1) (α₀ := α₀)
        hf.1.le hf.2.1 hLC hLS hc
      exact ⟨l₁ ++ l₂, hl₁.append hl₂⟩
    ·
      have hn := hf.2.2.2.2.2
      rw [hp] at hn
      have hf' : IsLabFactor L L 1 α₀ C p.1 (some 1) := isLabFactor_of_nat hα le_rfl hf.1.le
        hf.2.1 hLC hLS (isNatEigSection_one hn)
      exact ⟨(p.1, some 1) :: l₂, hf', hl₂⟩

theorem isNaturalSection_of_labSeries (hα : Function.Surjective α₀) {Z V : Subgroup G}
    (hab : ∀ v ∈ V, ∀ w ∈ V, v * w * v⁻¹ * w⁻¹ ∈ Z) {l : List (Subgroup G × Option F)}
    (hl : IsLabSeries (L ⊔ X) L x α₀ Z l V) (C₁ C₂ : Subgroup G) (hZC : Z ≤ C₁)
    (hC : C₁ < C₂) (hCV : C₂ ≤ V) (hL₁ : L ≤ Subgroup.normalizer (C₁ : Set G))
    (hL₂ : L ≤ Subgroup.normalizer (C₂ : Set G))
    (hsimple : ∀ J : Subgroup G, C₁ ≤ J → J ≤ C₂ → L ≤ Subgroup.normalizer (J : Set G) →
      J = C₁ ∨ J = C₂)
    (hnc : ∃ k ∈ L, ∃ c ∈ C₂, k * c * k⁻¹ * c⁻¹ ∉ C₁) :
    ∃ N' : Subgroup ↥L, IsNaturalSection L C₂ C₁ N' (StatedSL 2 F) := by
  obtain ⟨l', hl'⟩ := exists_isLabSeries_L hα l Z V hl
  have hJH := operatorJHNatEig_holds G L L 1 2 F α₀ le_rfl L.one_mem le_rfl hα
  have hC₁V : C₁ ≤ V := hC.le.trans hCV
  obtain ⟨-, l₂, -, hl₂, -⟩ := (hJH Z V l' hl').2 C₁ hZC hC₁V
    (le_normalizer_of_comm le_rfl (hZC.trans hC₁V) hC₁V hab)
    (le_normalizer_of_comm hZC hC₁V le_rfl hab) hL₁
  obtain ⟨l₃, -, hl₃, -, -⟩ := (hJH C₁ V l₂ hl₂).2 C₂ hC.le hCV
    (le_normalizer_of_comm hZC hC₁V hCV hab)
    (le_normalizer_of_comm (hZC.trans hC.le) hCV le_rfl hab) hL₂
  rcases l₃ with _ | ⟨p, l₄⟩
  · exact absurd (show C₁ = C₂ from hl₃) hC.ne
  obtain ⟨hf, hl₄⟩ := hl₃
  have hp1 : p.1 = C₂ := by
    rcases hsimple p.1 hf.1.le hl₄.le hf.2.2.2.1 with h | h
    · exact absurd h hf.1.ne'
    · exact h
  rcases hp : p.2 with _ | a
  · exfalso
    have hc := hf.2.2.2.2.2
    rw [hp, hp1] at hc
    obtain ⟨k, hk, c, hcC, hkc⟩ := hnc
    exact hkc (hc k hk c hcC)
  · have hn := hf.2.2.2.2.2
    rw [hp, hp1] at hn
    obtain ⟨β, hs, hk, hK, -⟩ := hn
    refine ⟨α₀.ker, hL₂, α₀, hα, rfl, β, hs, ?_, fun k u v huv => hK k u v huv⟩
    ext c
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hk c

end LSeries

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
