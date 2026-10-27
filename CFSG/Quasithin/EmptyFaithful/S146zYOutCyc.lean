module

public import CFSG.Quasithin.EmptyFaithful.S146zYCfg
public import CFSG.Quasithin.EmptyFaithful.S146zYRes

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Blueprint CFSG.QuasithinUnique.Vol2Native
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)

noncomputable def toOuter {A : Type} [Group A] (L : Subgroup A) [L.Normal] : A →* Outer ↥L :=
  (QuotientGroup.mk' (inner ↥L)).comp (MulAut.conjNormal : A →* MulAut ↥L)

theorem mem_sup_centralizer_of_toOuter_eq_one {A : Type} [Group A] (L : Subgroup A) [L.Normal]
    {x : A} (hx : toOuter L x = 1) : x ∈ L ⊔ Subgroup.centralizer (L : Set A) := by
  have h1 : (MulAut.conjNormal x : MulAut ↥L) ∈ inner ↥L := (QuotientGroup.eq_one_iff _).1 hx
  obtain ⟨l, hl⟩ := h1
  have hl' : ∀ y : ↥L, ((l * y * l⁻¹ : ↥L) : A) = x * y * x⁻¹ := by
    intro y
    have := congrArg (fun φ : MulAut ↥L => ((φ y : ↥L) : A)) hl
    simpa [MulAut.conj_apply] using this
  have hc : (l : A)⁻¹ * x ∈ Subgroup.centralizer (L : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have := hl' ⟨y, hy⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at this
    calc y * ((l : A)⁻¹ * x) = (l : A)⁻¹ * ((l : A) * y * (l : A)⁻¹) * x := by group
      _ = (l : A)⁻¹ * (x * y * x⁻¹) * x := by rw [this]
      _ = (l : A)⁻¹ * x * y := by group
  have : x = (l : A) * ((l : A)⁻¹ * x) := by group
  rw [this]
  exact Subgroup.mul_mem_sup l.2 hc

@[expose] def OutCycFact : Prop :=
  ∀ (J : Type) [Group J] [Finite J], CFSG.IsQuasisimple J → CFSG.SectionRank.IsSQTKCat J →
    ∀ p : ℕ, p.Prime → 5 ≤ p → ∀ S : Sylow p (Outer J), IsCyclic ↥S

theorem outNoE25Fact_of_cyclic (h : OutCycFact) : OutNoE25Fact := by
  intro p hp hp5 A _ _ L P hyp hLn hL _ _ hexp hcard hbot
  subst hp5
  have := hLn
  have hK : CFSG.SectionRank.IsSQTKCat ↥L :=
    CFSG.SectionRank.IsSQTKCat.subgroup ⟨hyp.sqt, hyp.kgroup⟩ L
  have hker : ∀ x ∈ P, toOuter L x = 1 → x = 1 := by
    intro x hxP hx1
    have : x ∈ P ⊓ (L ⊔ Subgroup.centralizer (L : Set A)) :=
      ⟨hxP, mem_sup_centralizer_of_toOuter_eq_one L hx1⟩
    rw [hbot] at this
    exact this
  have hinj : Function.Injective ((toOuter L).comp P.subtype) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    exact Subtype.ext (hker x.1 x.2 hx)
  set Q : Subgroup (Outer ↥L) := ((toOuter L).comp P.subtype).range with hQdef
  have hQcard : Nat.card Q = 25 := by
    have h1 : Nat.card P = Nat.card Q := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
    rw [← h1, hcard]
    norm_num
  have hQexp : ∀ x ∈ Q, x ^ 5 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow]
    have : (y : A) ^ 5 = 1 := hexp y y.2
    have hy5 : y ^ 5 = 1 := Subtype.ext (by simpa using this)
    rw [hy5, map_one]
  have hQp : IsPGroup 5 Q := by
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    exact IsPGroup.iff_card.mpr ⟨2, by rw [hQcard]; norm_num⟩
  obtain ⟨S, hQS⟩ := hQp.exists_le_sylow
  have hSc : IsCyclic ↥S := h ↥L hL.1 hK 5 (by norm_num) le_rfl S
  have : IsCyclic Q := Subgroup.isCyclic_of_le hQS
  exact not_isCyclic_of_card_twentyFive hQcard hQexp this

end CFSG.Quasithin.S146zY
