module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestNorm

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

@[expose] def GGStdSubSmallHyp (p : ℕ) {L' : Type} [Group L'] (A : Subgroup (MulAut L'))
    (a : MulAut L') : Prop :=
  ∀ E : Subgroup L', IsElemAbelian p E → E ≤ LargeEvenLayer (ggFix a) →
    (∀ a' ∈ A, ∀ e ∈ E, a' e = e) →
    ((∀ e ∈ E, MulAut.conj e ∈ A) ∨ ∃ U : Subgroup L', U ≠ ⊥ ∧ IsPGroup 2 U ∧
      (∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U) ∧ E ≤ Subgroup.normalizer (U : Set L')) →
    Nat.card E < p ^ 3

@[expose] def GGStdSubTwoTorusNormSmall (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) :
    Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGNormTwoR ψ A →
      ∀ a ∈ A, a ≠ 1 → IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) →
        (∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)) →
        GGStdSubSmallHyp p A a → GGStdSubTwoTorusConcl p A a

@[expose] def GGStdSubTwoTorusDeltaSmall (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) :
    Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGDeltaAdm p L' A →
      ∀ a ∈ A, a ≠ 1 → IsComponentOf (LargeEvenLayer (ggFix a)) (ggFix a) →
        (∀ a' ∈ A, ((∀ j ∈ LargeEvenLayer (ggFix a), a' j = j) ↔ a' ∈ Subgroup.zpowers a)) →
        GGStdSubSmallHyp p A a → GGStdSubTwoTorusConcl p A a

theorem ggStdSubTwoTorusDeltaSmall_of_delta {p r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (h : GGStdSubTwoTorusDelta p r R I) : GGStdSubTwoTorusDeltaSmall p r R I :=
  fun L' _ _ ψ hψ hker hL A hA hAI hr h3 hδ a ha ha1 hc hcA _ =>
    h L' ψ hψ hker hL A hA hAI hr h3 hδ a ha ha1 hc hcA

namespace StdSubRestThree

section Members

variable {G : Type} [Group G] [Finite G]

theorem mem_of_conj_mem_range {p : ℕ} (hp : p.Prime) {B : Subgroup G} {x : G} {L : Subgroup G}
    (hS : LargeEvenSStar p B x L) (hBN : B ≤ Subgroup.normalizer (L : Set G)) {e : L}
    (hep : e ^ p = 1) (hfix : ∀ b : B, ggGamma L hBN b e = e)
    (hconj : MulAut.conj e ∈ (ggGamma L hBN).range) : (e : G) ∈ B := by
  have := Fact.mk hp
  obtain ⟨b, hb⟩ := hconj
  obtain ⟨⟨hBe, -, -⟩, hxB, hx1, hLC, hcyc⟩ := hS
  have hxC : x ∈ Subgroup.centralizer (L : Set G) := mem_centralizer_of_le_centralizer hLC.1
  have hcL : (e : G)⁻¹ * b ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hb ⟨l, hl⟩)
    rw [ggGamma_coe, MulAut.conj_apply] at h1
    have h1' : (b : G) * l * (b : G)⁻¹ = (e : G) * l * (e : G)⁻¹ := by
      rw [h1]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc l * ((e : G)⁻¹ * b) = (e : G)⁻¹ * ((e : G) * l * (e : G)⁻¹) * b := by group
      _ = (e : G)⁻¹ * ((b : G) * l * (b : G)⁻¹) * b := by rw [h1']
      _ = (e : G)⁻¹ * b * l := by group
  have heb : (e : G) * b = b * e := by
    have h2 := congrArg Subtype.val (hfix b)
    rw [ggGamma_coe] at h2
    calc (e : G) * b = (b : G) * e * (b : G)⁻¹ * b := by rw [h2]
      _ = b * e := by group
  have hep' : (e : G) ^ p = 1 := by rw [← Subgroup.coe_pow, hep, Subgroup.coe_one]
  have hbp : (b : G) ^ p = 1 := hBe.2 b b.2
  have hcp : ((e : G)⁻¹ * b) ^ p = 1 := by
    have hc : Commute (e : G)⁻¹ (b : G) := (Commute.inv_left heb)
    rw [hc.mul_pow, inv_pow, hep', hbp, inv_one, one_mul]
  have hxe : x * (e : G) = (e : G) * x :=
    (Subgroup.mem_centralizer_iff.mp hxC (e : G) e.2).symm
  have hxb : x * b = b * x := IsElemAbelian.comm hBe hxB b.2
  have hxc : Commute x ((e : G)⁻¹ * b) :=
    (Commute.inv_right (show Commute x (e : G) from hxe)).mul_right hxb
  set c := (e : G)⁻¹ * b with hcdef
  have hxp : x ^ p = 1 := hBe.2 x hxB
  have hSe : IsElemAbelian p (Subgroup.zpowers x ⊔ Subgroup.zpowers c) :=
    isElemAbelian_sup (isElemAbelian_zpowers hxp) (isElemAbelian_zpowers hcp) (by
      intro u hu v hv
      obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact (hxc.zpow_zpow i j).eq)
  have hSC : Subgroup.zpowers x ⊔ Subgroup.zpowers c ≤ Subgroup.centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hxC) (Subgroup.zpowers_le.mpr hcL)
  have hScyc := hcyc _ hSC (isPGroup_of_isElemAbelian hSe)
  have hScard := card_le_of_isCyclic hp.pos hScyc hSe.2
  have hSx : Subgroup.zpowers x ⊔ Subgroup.zpowers c = Subgroup.zpowers x :=
    (Subgroup.eq_of_le_of_card_ge le_sup_left (by
      rw [Nat.card_zpowers, orderOf_eq_prime hxp hx1]
      exact hScard)).symm
  have hcx : c ∈ Subgroup.zpowers x := hSx ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
  have hcB : c ∈ B := Subgroup.zpowers_le.mpr hxB hcx
  have he : (e : G) = b * c⁻¹ := by rw [hcdef]; group
  rw [he]
  exact B.mul_mem b.2 (B.inv_mem hcB)

theorem map_le_of_twoGroup {p : ℕ} (hp : p.Prime) {B : Subgroup G} (hBmax : LargeEvenIsBmax p B)
    {L : Subgroup G} (hBN : B ≤ Subgroup.normalizer (L : Set G)) {E U : Subgroup L}
    (hE : IsElemAbelian p E) (hEfix : ∀ b : B, ∀ e ∈ E, ggGamma L hBN b e = e) (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) (hUB : ∀ b : B, ∀ u ∈ U, ggGamma L hBN b u ∈ U)
    (hEU : E ≤ Subgroup.normalizer (U : Set L)) : E.map L.subtype ≤ B := by
  set T := U.map L.subtype with hTdef
  have hT1 : T ≠ ⊥ := by
    rw [Ne, hTdef, Subgroup.map_eq_bot_iff_of_injective _ L.subtype_injective]
    exact hU
  have hT2 : IsPGroup 2 T := hU2.map _
  have hBT : B ≤ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.le_normalizer_iff]
    rintro b hb _ ⟨u, hu, rfl⟩
    exact ⟨ggGamma L hBN ⟨b, hb⟩ u, hUB _ u hu, ggGamma_coe L hBN ⟨b, hb⟩ u⟩
  have hET : E.map L.subtype ≤ Subgroup.normalizer (T : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    exact Subgroup.le_normalizer_map L.subtype ⟨e, hEU he, rfl⟩
  have hBE : ∀ b ∈ B, ∀ g ∈ E.map L.subtype, b * g = g * b := by
    rintro b hb _ ⟨e, he, rfl⟩
    have h2 := congrArg Subtype.val (hEfix ⟨b, hb⟩ e he)
    rw [ggGamma_coe] at h2
    have h2' : b * (e : G) * b⁻¹ = e := h2
    show b * (e : G) = (e : G) * b
    calc b * (e : G) = b * (e : G) * b⁻¹ * b := by group
      _ = (e : G) * b := by rw [h2']
  have hEe : IsElemAbelian p (B ⊔ E.map L.subtype) :=
    isElemAbelian_sup hBmax.1 (isElemAbelian_map hE _) hBE
  have hcard := card_le_of_twoLocal hp ⟨T, hT1, hT2, rfl⟩ (sup_le hBT hET) hEe
  rw [← hBmax.2.1] at hcard
  have hBE' := Subgroup.eq_of_le_of_card_ge (le_sup_left : B ≤ B ⊔ E.map L.subtype) hcard
  rw [hBE']
  exact le_sup_right

end Members

end StdSubRestThree

end CFSG.StandardType
