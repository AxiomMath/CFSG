module

public import CFSG.Quasithin.Background.F6CatRecogSetting
public import CFSG.Quasithin.Background.F6CatTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique

namespace F6

structure F617Setting {D : Type} [Group D] [Finite D] (G₁ G₂ K : Subgroup D) : Prop where
  triple : IsGoldschmidtTriple G₁ G₂
  pPrimeCore_eq_bot : CFSG.pPrimeCore 3 D = ⊥
  pCore_eq_bot : Open.pCore 2 D = ⊥
  component : CFSG.IsComponent K
  normal : K.Normal
  le_left : twoResidual G₁ ≤ K
  not_le_right : ¬ twoResidual G₂ ≤ K
  card_left : Nat.card ↥(twoResidual G₁) = 3
  sqt : CFSG.IsStronglyQuasithin (↥K ⧸ Subgroup.center ↥K)

theorem f617Setting_of (hF : F613Two.{0}) (hQ : NativeSQTSection) {D : Type} [Group D]
    [Finite D] {G₁ G₂ K : Subgroup D} (h : IsGoldschmidtTriple G₁ G₂)
    (hX : ∃ (X : Type) (_ : Group X) (_ : Finite X), CFSG.SectionRank.IsSQTKCat X ∧
      Nonempty (D ≃* X ⧸ CFSG.pPrimeCore 3 X))
    (hK : CFSG.IsComponent K) (hKn : K.Normal) (h₁ : twoResidual G₁ ≤ K)
    (h₂ : ¬ twoResidual G₂ ≤ K) : F617Setting G₁ G₂ K := by
  obtain ⟨X, _, _, hsq, ⟨e⟩⟩ := hX
  obtain ⟨hO, hO2⟩ := remark_f6_15 e
  exact ⟨h, hO, hO2, hK, hKn, h₁, h₂, card_twoResidual_eq_three_of_F613Two hF h hO2 h₁ h₂,
    isStronglyQuasithin_of_isQuasisimple hQ hsq e hK.1⟩

namespace F617Setting

variable {D : Type} [Group D] [Finite D] {G₁ G₂ K : Subgroup D}

theorem inf_eq (hS : F617Setting G₁ G₂ K) :
    G₂ ⊓ K = pCoreOf 2 G₂ ⊓ K ∧ pCoreOf 2 G₂ ⊓ K = G₂ ⊓ G₁ ⊓ K ∧
      IsSylowTwoOf (G₂ ⊓ G₁ ⊓ K) K := by
  have := hS.normal
  exact ((tfae_inf_le_pCoreOf hS.triple.symm isSubnormal_top_of_normal).out 3 2).mp
    hS.not_le_right

theorem isSylowTwoOf_inf (hS : F617Setting G₁ G₂ K) : IsSylowTwoOf (pCoreOf 2 G₂ ⊓ K) K := by
  obtain ⟨-, e2, hsyl⟩ := hS.inf_eq
  rw [e2]
  exact hsyl

theorem elemAbelian (hS : F617Setting G₁ G₂ K) :
    IsElemAbelian 2 (pCoreOf 2 G₂) ∧ Nat.card ↥(pCoreOf 2 G₂) ≤ 2 ^ 3 :=
  (f6_13_three hS.triple hS.pCore_eq_bot hS.card_left).1

theorem isPGroup_center (hS : F617Setting G₁ G₂ K) :
    IsPGroup 3 ↥(Subgroup.center ↥K) :=
  have := hS.normal
  isPGroup_center_of_pPrimeCore_eq_bot hS.pPrimeCore_eq_bot

theorem odd_card_center (hS : F617Setting G₁ G₂ K) :
    Odd (Nat.card ↥(Subgroup.center ↥K)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := hS.isPGroup_center.exists_card_eq
  rw [hk]
  exact Odd.pow (by decide)

theorem normal_inf_centralizer (hS : F617Setting G₁ G₂ K) :
    (K ⊓ Subgroup.centralizer (K : Set D)).Normal := by
  have hKn := hS.normal
  refine ⟨fun z hz g => Subgroup.mem_inf.mpr ⟨hKn.conj_mem z hz.1 g, ?_⟩⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : g⁻¹ * k * g ∈ K := by simpa using hKn.conj_mem k hk g⁻¹
  have hc := Subgroup.mem_centralizer_iff.mp hz.2 _ hk'
  calc k * (g * z * g⁻¹) = g * ((g⁻¹ * k * g) * z) * g⁻¹ := by group
    _ = g * (z * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
    _ = g * z * g⁻¹ * k := by group

theorem not_le_inf_centralizer (hS : F617Setting G₁ G₂ K) :
    ¬ twoResidual G₁ ≤ K ⊓ Subgroup.centralizer (K : Set D) := by
  intro hle
  set Z := K ⊓ Subgroup.centralizer (K : Set D) with hZ
  have := hS.normal_inf_centralizer
  have hsup : Z ⊔ G₂ = ⊤ := sup_eq_top_of_twoResidual_le hS.triple hle
  have hZab : Group.IsSolvable ↥Z := Group.isSolvable_of_comm fun a b => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp b.2.2 a a.2.1)
  have : Group.IsSolvable ↥G₂ := isSolvable_vertex_right hS.triple
  have hsurj : Function.Surjective ((QuotientGroup.mk' Z).comp G₂.subtype) := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Z q
    have hd : d ∈ Z ⊔ G₂ := hsup ▸ Subgroup.mem_top d
    rw [Subgroup.mem_sup_of_normal_left] at hd
    obtain ⟨z, hz, g, hg, rfl⟩ := hd
    refine ⟨⟨g, hg⟩, ?_⟩
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    rw [QuotientGroup.eq]
    have h1 := hS.normal_inf_centralizer.conj_mem z hz g⁻¹
    rw [inv_inv, mul_assoc] at h1
    exact h1
  have : Group.IsSolvable (D ⧸ Z) := Group.isSolvable_of_surjective hsurj
  have : Group.IsSolvable D := Group.isSolvable_of_subgroup_quotient Z
  have : Group.IsPerfect ↥K := hS.component.1.1
  have : Nontrivial ↥K := CFSG.LocalCores.isQuasisimple_nontrivial hS.component.1
  exact Group.IsPerfect.not_isSolvable ↥K inferInstance

end F617Setting

end F6

end CFSG.Quasithin
