module

public import CFSG.RankThree.PartTwo.Sec21.Item223PrintProofU4
public import CFSG.RankThree.PartTwo.Sec21.Item22DStar
public import CFSG.RankThree.PartTwo.Sec21.Item22Refl

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly (IsElemAbelian)

variable {G : Type} [Group G]

namespace Item223PrintProof

theorem conj_eq_of_conj_eq_on_inf {A X : Subgroup G}
    (hdec : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G)) {g : G}
    (hg : g ∈ X) (h : ∀ t ∈ A ⊓ X, g * t * g⁻¹ = t) : ∀ b ∈ A, g * b * g⁻¹ = b := by
  intro b hb
  obtain ⟨y, hy, hyb⟩ := hdec b hb
  have hs : g * (y⁻¹ * b) = (y⁻¹ * b) * g := Subgroup.mem_centralizer_iff.mp hyb g hg
  calc g * b * g⁻¹ = (g * y * g⁻¹) * (g * (y⁻¹ * b)) * g⁻¹ := by group
    _ = y * ((y⁻¹ * b) * g) * g⁻¹ := by rw [h y hy, hs]
    _ = b := by group

theorem fixedInG_eq_of_inf_eq {A X : Subgroup G}
    (hdec : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G))
    {F₁ F₂ : Subgroup G} (hF₁ : F₁ ≤ A) (hF₂ : F₂ ≤ A)
    (hc₁ : A ⊓ Subgroup.centralizer (X : Set G) ≤ F₁)
    (hc₂ : A ⊓ Subgroup.centralizer (X : Set G) ≤ F₂) (h : A ⊓ X ⊓ F₁ = A ⊓ X ⊓ F₂) :
    F₁ = F₂ := by
  have key : ∀ {F F' : Subgroup G}, F ≤ A → A ⊓ Subgroup.centralizer (X : Set G) ≤ F →
      A ⊓ Subgroup.centralizer (X : Set G) ≤ F' → A ⊓ X ⊓ F = A ⊓ X ⊓ F' → F ≤ F' := by
    intro F F' hF hc hc' h b hb
    obtain ⟨y, hy, hyb⟩ := hdec b (hF hb)
    have hs : y⁻¹ * b ∈ A ⊓ Subgroup.centralizer (X : Set G) :=
      ⟨A.mul_mem (A.inv_mem hy.1) (hF hb), hyb⟩
    have hyF : y ∈ F := by
      have : y = b * (y⁻¹ * b)⁻¹ := by group
      rw [this]
      exact F.mul_mem hb (F.inv_mem (hc hs))
    have hmem : y ∈ A ⊓ X ⊓ F := ⟨hy, hyF⟩
    rw [h] at hmem
    have hyF' : y ∈ F' := hmem.2
    have : b = y * (y⁻¹ * b) := by group
    rw [this]
    exact F'.mul_mem hyF' (hc' hs)
  exact le_antisymm (key hF₁ hc₁ hc₂ h) (key hF₂ hc₂ hc₁ h.symm)

theorem mem_centralizer_of_mem_centralizer_inf {A X F : Subgroup G}
    (hdec : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G)) (hFA : F ≤ A)
    (hc : A ⊓ Subgroup.centralizer (X : Set G) ≤ F) {g : G} (hgX : g ∈ X)
    (hg : g ∈ Subgroup.centralizer ((A ⊓ X ⊓ F : Subgroup G) : Set G)) :
    g ∈ Subgroup.centralizer (F : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨y, hy, hyb⟩ := hdec b (hFA hb)
  have hs : y⁻¹ * b ∈ A ⊓ Subgroup.centralizer (X : Set G) :=
    ⟨A.mul_mem (A.inv_mem hy.1) (hFA hb), hyb⟩
  have hyF : y ∈ F := by
    have : y = b * (y⁻¹ * b)⁻¹ := by group
    rw [this]
    exact F.mul_mem hb (F.inv_mem (hc hs))
  have h1 : y * g = g * y := Subgroup.mem_centralizer_iff.mp hg y ⟨hy, hyF⟩
  have h2 : g * (y⁻¹ * b) = (y⁻¹ * b) * g := Subgroup.mem_centralizer_iff.mp hyb g hgX
  calc b * g = y * ((y⁻¹ * b) * g) := by group
    _ = y * (g * (y⁻¹ * b)) := by rw [h2]
    _ = (y * g) * (y⁻¹ * b) := by group
    _ = (g * y) * (y⁻¹ * b) := by rw [h1]
    _ = g * b := by group

theorem restrict_reflection {A T : Subgroup G} (hTA : T ≤ A)
    (hAc : ∀ a b : A, a * b = b * a) (hA3 : ∀ a : A, a ^ 3 = 1) {j : G}
    (hjA : j ∈ Subgroup.normalizer (A : Set G)) (hjT : j ∈ Subgroup.normalizer (T : Set G))
    (hφ : IsReflectionOn (wConj A ⟨j, hjA⟩))
    (hcT : (commOf (wConj A ⟨j, hjA⟩)).map A.subtype ≤ T) :
    IsReflectionOn (wConj T ⟨j, hjT⟩) ∧
      (commOf (wConj T ⟨j, hjT⟩)).map T.subtype = (commOf (wConj A ⟨j, hjA⟩)).map A.subtype ∧
      fixedInG T (wConj T ⟨j, hjT⟩) = T ⊓ fixedInG A (wConj A ⟨j, hjA⟩) := by
  set φ := wConj A ⟨j, hjA⟩ with hφdef
  set ρ := wConj T ⟨j, hjT⟩ with hρdef
  have key : ∀ a : T, ((ρ a : T) : G) = ((φ ⟨a, hTA a.2⟩ : A) : G) := fun a => rfl
  have hφφ := apply_apply_of_orderOf_eq_two hφ.1
  have hcomm : (commOf ρ).map T.subtype = (commOf φ).map A.subtype := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, commOf, Subgroup.closure_le]
      rintro _ ⟨a, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap]
      refine ⟨(⟨a, hTA a.2⟩ : A)⁻¹ * φ ⟨a, hTA a.2⟩, mem_commOf φ _, ?_⟩
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, key]
    · rintro _ ⟨w, hw, rfl⟩
      have hwT : (w : G) ∈ T := hcT ⟨w, hw, rfl⟩
      have hφw : φ w = w⁻¹ := inv_of_mem_commOf hAc hφφ hw
      refine ⟨(⟨w, hwT⟩ : T)⁻¹ * ρ ⟨w, hwT⟩, mem_commOf ρ _, ?_⟩
      have h1 : ((ρ ⟨w, hwT⟩ : T) : G) = ((w : A) : G)⁻¹ := by
        rw [key]
        have : (⟨(w : G), hTA hwT⟩ : A) = w := rfl
        rw [this, hφw]
        rfl
      have h3 : ((w : A) : G) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, hA3 w, Subgroup.coe_one]
      simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, h1]
      calc ((w : A) : G)⁻¹ * ((w : A) : G)⁻¹ = ((w : A) : G)⁻¹ * ((w : A) : G)⁻¹ *
            ((w : A) : G) ^ 3 := by rw [h3, mul_one]
        _ = (w : G) := by group
  have hfix : fixedInG T ρ = T ⊓ fixedInG A φ := by
    ext x
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨t.2, ⟨⟨t, hTA t.2⟩, ?_, rfl⟩⟩
      rw [SetLike.mem_coe, mem_fixedSubgroupOf] at ht ⊢
      exact Subtype.ext ((key t).symm.trans (congrArg Subtype.val ht))
    · rintro ⟨hxT, ⟨a, ha, rfl⟩⟩
      refine ⟨⟨a, hxT⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, mem_fixedSubgroupOf] at ha ⊢
      exact Subtype.ext ((key ⟨a, hxT⟩).trans (congrArg Subtype.val ha))
  have hcard : Nat.card (commOf ρ) = 3 := by
    rw [← Subgroup.card_map_of_injective T.subtype_injective, hcomm,
      Subgroup.card_map_of_injective A.subtype_injective]
    exact hφ.2
  have hρ2 : ρ ^ 2 = 1 := by
    ext a
    rw [sq, MulAut.mul_apply, MulAut.one_apply]
    have h1 : ((ρ (ρ a) : T) : G) = ((φ (φ ⟨a, hTA a.2⟩) : A) : G) := rfl
    rw [hφφ] at h1
    exact h1
  have hρ1 : ρ ≠ 1 := by
    intro h1
    rw [← commOf_eq_bot_iff] at h1
    rw [h1, Subgroup.card_bot] at hcard
    omega
  exact ⟨⟨orderOf_eq_prime hρ2 hρ1, hcard⟩, hcomm, hfix⟩

theorem nonempty_range_mulEquiv_of_ker_eq {H M₁ M₂ : Type*} [Group H] [Group M₁] [Group M₂]
    (f₁ : H →* M₁) (f₂ : H →* M₂) (hker : f₁.ker = f₂.ker) : Nonempty (f₁.range ≃* f₂.range) :=
  ⟨(QuotientGroup.quotientKerEquivRange f₁).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hker).trans (QuotientGroup.quotientKerEquivRange f₂))⟩

theorem nonempty_closure_pair_mulEquiv {A X : Subgroup G}
    (hdec : ∀ b ∈ A, ∃ y ∈ A ⊓ X, y⁻¹ * b ∈ Subgroup.centralizer (X : Set G))
    (j i : Subgroup.normalizer (A : Set G)) (hjX : (j : G) ∈ X) (hiX : (i : G) ∈ X)
    (hjT : (j : G) ∈ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G))
    (hiT : (i : G) ∈ Subgroup.normalizer ((A ⊓ X : Subgroup G) : Set G)) :
    Nonempty (Subgroup.closure {wConj A j, wConj A i} ≃*
      Subgroup.closure {wConj (A ⊓ X) ⟨j, hjT⟩, wConj (A ⊓ X) ⟨i, hiT⟩}) := by
  set T := A ⊓ X with hT
  set H : Subgroup (Subgroup.normalizer (A : Set G)) := Subgroup.closure {j, i} with hH
  have hHX : ∀ x : H, ((x : Subgroup.normalizer (A : Set G)) : G) ∈ X ∧
      ((x : Subgroup.normalizer (A : Set G)) : G) ∈ Subgroup.normalizer (T : Set G) := by
    have hle : H ≤ (X ⊓ Subgroup.normalizer (T : Set G)).comap
        (Subgroup.normalizer (A : Set G)).subtype := by
      rw [hH, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact ⟨hjX, hjT⟩
      · exact ⟨hiX, hiT⟩
    exact fun x => hle x.2
  set f₁ : H →* MulAut A := (A.normalizerMonoidHom).domRestrict H with hf₁
  set g : H →* Subgroup.normalizer (T : Set G) :=
    ((Subgroup.normalizer (A : Set G)).subtype.comp H.subtype).codRestrict _
      (fun x => (hHX x).2) with hg
  set f₂ : H →* MulAut T := T.normalizerMonoidHom.comp g with hf₂
  have hr₁ : f₁.range = Subgroup.closure {wConj A j, wConj A i} := by
    rw [hf₁, MonoidHom.domRestrict_range, hH, MonoidHom.map_closure, Set.image_pair]
    rfl
  have hr₂ : f₂.range = Subgroup.closure {wConj T ⟨j, hjT⟩, wConj T ⟨i, hiT⟩} := by
    apply le_antisymm
    · rw [MonoidHom.range_eq_map, ← Subgroup.closure_closure_coe_preimage (k := {j, i}),
        MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      rcases hx with hx | hx
      · apply Subgroup.subset_closure
        left
        have : g x = ⟨j, hjT⟩ := Subtype.ext (by
          change ((x : Subgroup.normalizer (A : Set G)) : G) = j
          rw [hx])
        rw [hf₂, MonoidHom.comp_apply, this]
        rfl
      · apply Subgroup.subset_closure
        right
        rw [Set.mem_singleton_iff]
        have : g x = ⟨i, hiT⟩ := Subtype.ext (by
          change ((x : Subgroup.normalizer (A : Set G)) : G) = i
          rw [Set.mem_singleton_iff.mp hx])
        rw [hf₂, MonoidHom.comp_apply, this]
        rfl
    · rw [Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact ⟨⟨j, Subgroup.subset_closure (Or.inl rfl)⟩, rfl⟩
      · exact ⟨⟨i, Subgroup.subset_closure (Or.inr rfl)⟩, rfl⟩
  have hker : f₁.ker = f₂.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    have hf₁x : ∀ a : A, ((f₁ x a : A) : G) =
        ((x : Subgroup.normalizer (A : Set G)) : G) * a *
          ((x : Subgroup.normalizer (A : Set G)) : G)⁻¹ := fun a => rfl
    have hf₂x : ∀ t : T, ((f₂ x t : T) : G) =
        ((x : Subgroup.normalizer (A : Set G)) : G) * t *
          ((x : Subgroup.normalizer (A : Set G)) : G)⁻¹ := fun t => rfl
    constructor
    · intro h
      ext t
      rw [hf₂x, MulAut.one_apply]
      have := congrArg (fun σ : MulAut A => ((σ ⟨t, t.2.1⟩ : A) : G)) h
      simpa [hf₁x] using this
    · intro h
      have h1 : ∀ t ∈ T, ((x : Subgroup.normalizer (A : Set G)) : G) * t *
          ((x : Subgroup.normalizer (A : Set G)) : G)⁻¹ = t := by
        intro t ht
        have := congrArg (fun σ : MulAut T => ((σ ⟨t, ht⟩ : T) : G)) h
        simpa [hf₂x] using this
      ext a
      rw [hf₁x, MulAut.one_apply]
      exact conj_eq_of_conj_eq_on_inf hdec (hHX x).1 h1 a a.2
  obtain ⟨e⟩ := nonempty_range_mulEquiv_of_ker_eq f₁ f₂ hker
  exact ⟨(MulEquiv.subgroupCongr hr₁).symm.trans (e.trans (MulEquiv.subgroupCongr hr₂))⟩

theorem mul_comm_of_commutator_eq_bot [Finite G] (h222 : Item222) {A E U L : Subgroup G}
    {c : G} (hpair : Sec21Pair G A E U c L) (hK : KOfWellDefined A) {φ ψ : MulAut A}
    (hφ : φ ∈ dStar A) (hψ : ψ ∈ dStar A) (h : ⁅kOf A φ, kOf A ψ⁆ = ⊥) : ψ * φ = φ * ψ := by
  obtain ⟨j, hjK, -, hj⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hφ
  obtain ⟨i, hiJ, -, hi⟩ := exists_involution_kOf_wConj_eq h222 hpair hK hψ
  have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
  have hji : (i : G) * j = j * i := Subgroup.mem_centralizer_iff.mp (hle hjK) i hiJ
  have hji' : i * j = j * i := Subtype.ext hji
  rw [← hj, ← hi, wConj, wConj, ← map_mul, ← map_mul, hji']

end Item223PrintProof

open Item223PrintProof

end CFSG.RankThree.PartTwo.Sec21
