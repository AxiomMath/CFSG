module

public import CFSG.Quasithin.Vol2.Ch11SecO10X
public import CFSG.Quasithin.Vol2.Ch11SecO10Y
public import CFSG.Quasithin.Vol2.Ch11SecO10G

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.Vol2.Ch11.O10

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.Quasithin.SteinbergCB
  CFSG.Quasithin.H13.A7

variable {G : Type} [Group G] [Finite G] {V N K L₁ : Subgroup G}
  {ψ : V ≃* Multiplicative (evenWeight 7)}

omit [Finite G] in
theorem coordRep_comm (hNV : N ≤ normalizer (V : Set G)) (hN : ∀ n ∈ N, ∃ σ, IsCoordAct ψ n σ)
    {r l : G} (hr : r ∈ N) (hl : l ∈ N) (hc : r * l * r⁻¹ * l⁻¹ ∈ centralizer (V : Set G)) :
    coordRep ψ hNV hN ⟨r, hr⟩ * coordRep ψ hNV hN ⟨l, hl⟩ =
      coordRep ψ hNV hN ⟨l, hl⟩ * coordRep ψ hNV hN ⟨r, hr⟩ := by
  have hcN : r * l * r⁻¹ * l⁻¹ ∈ N := mul_mem (mul_mem (mul_mem hr hl) (inv_mem hr)) (inv_mem hl)
  have h1 := (coordRep_eq_one_iff ψ hNV hN ⟨_, hcN⟩).2 hc
  rw [show (⟨r * l * r⁻¹ * l⁻¹, hcN⟩ : N) = ⟨r, hr⟩ * ⟨l, hl⟩ * ⟨r, hr⟩⁻¹ * ⟨l, hl⟩⁻¹ from rfl,
    map_mul, map_mul, map_mul, map_inv, map_inv] at h1
  calc _ = coordRep ψ hNV hN ⟨r, hr⟩ * coordRep ψ hNV hN ⟨l, hl⟩ *
        (coordRep ψ hNV hN ⟨r, hr⟩)⁻¹ * (coordRep ψ hNV hN ⟨l, hl⟩)⁻¹ *
        (coordRep ψ hNV hN ⟨l, hl⟩ * coordRep ψ hNV hN ⟨r, hr⟩) := by group
    _ = _ := by rw [h1, one_mul]

theorem pCoreOf_le_centralizer_coord (hNV : N ≤ normalizer (V : Set G))
    (hN : ∀ n ∈ N, ∃ σ, IsCoordAct ψ n σ) (hKN : K ≤ N)
    (hKA : ∀ k (hk : k ∈ K), coordRep ψ hNV hN ⟨k, hKN hk⟩ ∈ alternatingGroup (Fin 7))
    (hLK : L₁ ≤ K) {y : G} (hyL : y ∈ L₁) (hy5 : orderOf y = 5)
    (hyV : y ∉ centralizer (V : Set G)) : pCoreOf 2 L₁ ≤ centralizer (V : Set G) := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  set ρ := coordRep ψ hNV hN with hρ
  have hON : pCoreOf 2 L₁ ≤ N :=
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₁).trans hLK).trans hKN
  have hyN : y ∈ N := hKN (hLK hyL)
  set P₂ := ((pCoreOf 2 L₁).subgroupOf N).map ρ with hP₂
  have hP₂A : P₂ ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨o, ho, rfl⟩
    exact hKA o ((CFSG.LieType.BorelTits.pCoreOf_le 2 L₁).trans hLK (mem_subgroupOf.1 ho))
  have hP₂2 : IsPGroup 2 P₂ :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L₁).comap_of_injective N.subtype
      N.subtype_injective).map ρ
  have hyO : y ∈ normalizer (pCoreOf 2 L₁ : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L₁ hyL
  have hyP : ρ ⟨y, hyN⟩ ∈ normalizer (P₂ : Set (Perm (Fin 7))) := by
    refine le_normalizer_map ρ ⟨⟨y, hyN⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_normalizer_iff]
    intro o
    rw [mem_subgroupOf, mem_subgroupOf]
    exact mem_normalizer_iff.1 hyO o
  have hy1 : ρ ⟨y, hyN⟩ ≠ 1 := fun h => hyV ((coordRep_eq_one_iff ψ hNV hN _).1 h)
  have hρy5 : orderOf (ρ ⟨y, hyN⟩) = 5 := by
    refine orderOf_eq_prime ?_ hy1
    rw [← map_pow]
    have : (⟨y, hyN⟩ : N) ^ 5 = 1 := Subtype.ext (by rw [SubgroupClass.coe_pow, ← hy5,
      pow_orderOf_eq_one, OneMemClass.coe_one])
    rw [this, map_one]
  have hbot := eq_bot_of_two_of_five hP₂A hP₂2 (hKA y (hLK hyL)) hρy5 hyP
  intro o ho
  have h1 : ρ ⟨o, hON ho⟩ ∈ P₂ := ⟨⟨o, hON ho⟩, mem_subgroupOf.2 ho, rfl⟩
  rw [hbot, mem_bot] at h1
  exact (coordRep_eq_one_iff ψ hNV hN _).1 h1

theorem map_lOf_eq_fix2 (hNV : N ≤ normalizer (V : Set G)) (hN : ∀ n ∈ N, ∃ σ, IsCoordAct ψ n σ)
    (hKN : K ≤ N)
    (hKA : ∀ k (hk : k ∈ K), coordRep ψ hNV hN ⟨k, hKN hk⟩ ∈ alternatingGroup (Fin 7))
    (hLK : L₁ ≤ K) (hLp : ⁅L₁, L₁⁆ = L₁) {K₀ : Type} [Field K₀] [Finite K₀]
    (hK₀ : Nat.card K₀ = 2 ^ 2)
    (e₁ : ↥L₁ ⧸ CFSG.pCore 2 ↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K₀) {y : G} (hyL : y ∈ L₁)
    (hy5 : orderOf y = 5) (hyV : y ∉ centralizer (V : Set G)) {a b : Fin 7} (hab : a ≠ b)
    {r₀ : G} (hr₀N : r₀ ∈ N) (hr₀ : coordRep ψ hNV hN ⟨r₀, hr₀N⟩ = swap a b)
    (hr₀L : ∀ l ∈ L₁, r₀ * l * r₀⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁) :
    (L₁.subgroupOf N).map (coordRep ψ hNV hN) = fix2 a b := by
  classical
  set ρ := coordRep ψ hNV hN with hρ
  have hLN : L₁ ≤ N := hLK.trans hKN
  have hC1 := pCoreOf_le_centralizer_coord hNV hN hKN hKA hLK hyL hy5 hyV
  set X := (L₁.subgroupOf N).map ρ with hX
  have hXA : X ≤ alternatingGroup (Fin 7) := by
    rintro _ ⟨l, hl, rfl⟩
    exact hKA l (hLK (mem_subgroupOf.1 hl))
  have hXp : ⁅X, X⁆ = X := by
    rw [hX, ← map_commutator]
    congr 1
    apply Subgroup.map_injective N.subtype_injective
    rw [map_commutator, subgroupOf_map_subtype, inf_of_le_left hLN, hLp]
  have hXc : ∀ x ∈ X, x * swap a b = swap a b * x := by
    rintro _ ⟨l, hl, rfl⟩
    rw [← hr₀]
    exact (coordRep_comm hNV hN hr₀N l.2 (hC1 (hr₀L l (mem_subgroupOf.1 hl)))).symm
  have hXle := le_fix2_of_perfect hab hXp hXA hXc
  set φ : ↥L₁ →* Perm (Fin 7) := ρ.comp (Subgroup.inclusion hLN) with hφ
  have hle : CFSG.pCore 2 ↥L₁ ≤ φ.ker := by
    intro o ho
    rw [← SecD.pCoreOf_subgroupOf, mem_subgroupOf] at ho
    exact (coordRep_eq_one_iff ψ hNV hN _).2 (hC1 ho)
  set φ' := QuotientGroup.lift (CFSG.pCore 2 ↥L₁) φ hle with hφ'
  have : CharP K₀ 2 := KGNat.charP_two_of_card (by norm_num) hK₀
  have := isSimpleGroup_sl2_two (F := K₀) (by rw [hK₀]; norm_num)
  have : IsSimpleGroup (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) := e₁.isSimpleGroup
  have hinj : Function.Injective φ' := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal φ'.ker with h | h
    · exact (MonoidHom.ker_eq_bot_iff φ').1 h
    · exfalso
      have h1 : φ' (QuotientGroup.mk ⟨y, hyL⟩) = 1 := by
        rw [← MonoidHom.mem_ker, h]
        exact mem_top _
      exact hyV ((coordRep_eq_one_iff ψ hNV hN _).1 h1)
  have hmem : ∀ q, φ' q ∈ X := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H l => exact ⟨Subgroup.inclusion hLN l, mem_subgroupOf.2 l.2, rfl⟩
  have hcardQ : Nat.card (↥L₁ ⧸ CFSG.pCore 2 ↥L₁) = 60 := by
    rw [Nat.card_congr e₁.toEquiv, CFSG.SL2MinimalFaithful.card_specialLinearGroup_fin_two, hK₀]
    norm_num
  have hcardX : 60 ≤ Nat.card X := by
    rw [← hcardQ]
    exact Nat.card_le_card_of_injective (fun q => ⟨φ' q, hmem q⟩)
      fun q q' h => hinj (congrArg Subtype.val h)
  exact Subgroup.eq_of_le_of_card_ge hXle ((card_fix2_le hab).trans hcardX)

end CFSG.Quasithin.Vol2.Ch11.O10
