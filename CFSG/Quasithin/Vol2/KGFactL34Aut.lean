module

public import CFSG.Quasithin.Vol2.KGFactL34Cent
public import CFSG.Quasithin.Vol2.Ch5Sec1L34InputsOddAm
public import CFSG.RankThree.PartTwo.KFacts.L34Aut

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

namespace KGL34A

variable {k : Type} [Field k] [Finite k]

theorem card_le_eight_of_ne {E : Subgroup (projectiveSL 3 k)} (hs : ∀ x ∈ E, x * x = 1)
    (h16 : Nat.card E ≤ 16) (hne : Nat.card E ≠ 16) : Nat.card E ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : IsPGroup 2 E := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, sq]
    exact hs x x.2)⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 hE
  rw [hm] at h16 hne ⊢
  have hm4 : m ≤ 4 := by
    by_contra h
    have : 2 ^ 5 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases m <;> simp_all

theorem card_le_of_mulAut (hk : Nat.card k = 4) {A : Subgroup (MulAut (projectiveSL 3 k))}
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hs : ∀ a ∈ A, a * a = 1) : Nat.card A ≤ 16 := by
  classical
  have : CharP k 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  set σ : k ≃+* k := frobeniusEquiv k 2 with hσdef
  have hσ : ∀ a, σ a = a ^ 2 := fun a => frobeniusEquiv_apply k 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hk
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hk hΨ
  set I := (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)).range with hI
  set ψ : MulAut (projectiveSL 3 k) →* Multiplicative (ZMod 2) × Multiplicative (ZMod 2) :=
    SemidirectProduct.rightHom.comp Ψ with hψdef
  have hψnf : ∀ H a b, ψ (LinearThreeFourOuter.nf σ H a b) =
      (Multiplicative.ofAdd a, Multiplicative.ofAdd b) := by
    intro H a b
    rw [hψdef, MonoidHom.comp_apply, hΨ, SemidirectProduct.rightHom_eq_right]
  have hψc : ∀ H, ψ (LinearFlag.conjAut 3 k H) = 1 := by
    intro H
    rw [← LinearThreeFourOuter.nf_zero_zero σ H, hψnf]
    rfl
  have hψf : ψ (LinearFlag.fieldAut 3 k σ) = (Multiplicative.ofAdd 1, 1) := by
    rw [← LinearThreeFourOuter.nf_one_zero σ, hψnf]
    rfl
  have hψd : ψ (LinearFlag.dualAut 3 k) = (1, Multiplicative.ofAdd 1) := by
    rw [← LinearThreeFourOuter.nf_zero_one σ, hψnf]
    rfl
  have hψconj : ∀ H τ, ψ (LinearFlag.conjAut 3 k H * τ * (LinearFlag.conjAut 3 k H)⁻¹) = ψ τ := by
    intro H τ
    rw [map_mul, map_mul, mul_comm (ψ _) (ψ τ), mul_assoc, ← map_mul, mul_inv_cancel, map_one,
      mul_one]
  have hIψ : ∀ α ∈ I, ψ α = 1 := by
    intro α hα
    rw [← hker] at hα
    rw [hψdef, MonoidHom.comp_apply, MonoidHom.mem_ker.1 hα, map_one]
  have hψI : ∀ α : MulAut (projectiveSL 3 k), α * α = 1 → ψ α = 1 → α ∈ I := by
    intro α hα hψα
    rw [← hker, MonoidHom.mem_ker]
    have hxr : (Ψ α).right = 1 := hψα
    have hx2 : Ψ α * Ψ α = 1 := by rw [← map_mul, hα, map_one]
    have hl : (Ψ α).left * (Ψ α).left = 1 := by
      have := congrArg SemidirectProduct.left hx2
      rwa [SemidirectProduct.mul_left, hxr, map_one, MulAut.one_apply,
        SemidirectProduct.one_left] at this
    have h3 := LinearThreeFourOuter.units_pow_three hk (Ψ α).left
    have hl1 : (Ψ α).left = 1 := by
      calc (Ψ α).left = (Ψ α).left ^ 3 * ((Ψ α).left * (Ψ α).left)⁻¹ := by group
        _ = 1 := by rw [h3, hl]; group
    exact SemidirectProduct.ext hl1 hxr
  set A₀ := A ⊓ I with hA₀
  set ψA := ψ.comp A.subtype with hψA
  have hkerA : ψA.ker = A₀.subgroupOf A := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact ⟨x.2, hψI _ (hs _ x.2) h⟩
    · intro h
      exact hIψ _ h.2
  have hcardA : Nat.card A = Nat.card A₀ * Nat.card ψA.range := by
    rw [← Subgroup.card_mul_index ψA.ker, Subgroup.index_ker, hkerA,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left : A₀ ≤ A)).toEquiv]
  have h2 : Nat.card (Multiplicative (ZMod 2)) = 2 := by
    rw [Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  have h4 : Nat.card (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) = 4 := by
    rw [Nat.card_prod, h2]
  have hrange4 : Nat.card ψA.range ≤ 4 := h4 ▸ Subgroup.card_le_card_group ψA.range
  have hE : ∀ α : MulAut (projectiveSL 3 k), ∃ E : Subgroup (projectiveSL 3 k),
      Nat.card E = Nat.card A₀ ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧ (∀ x ∈ E, x * x = 1) ∧
      ∀ t ∈ A, ∀ x ∈ E, (α⁻¹ * t * α) x = x := by
    intro α
    set D := A₀.comap (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k)) with hD
    have hinj := CFSG.RankThree.PartTwo.KFacts.L34.conj_injective hk
    refine ⟨D.map α⁻¹.toMonoidHom, ?_, ?_, ?_, ?_⟩
    · rw [Subgroup.card_map_of_injective α⁻¹.injective]
      conv_rhs => rw [← Subgroup.map_comap_eq_self (H := A₀)
        (f := (MulAut.conj : projectiveSL 3 k →* MulAut (projectiveSL 3 k))) inf_le_right]
      rw [Subgroup.card_map_of_injective hinj]
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      rw [← map_mul, ← map_mul]
      congr 1
      apply hinj
      rw [map_mul, map_mul]
      exact hc _ hx.1 _ hy.1
    · rintro _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      have hx2 : x * x = 1 := by
        apply hinj
        rw [map_mul, map_one]
        exact hs _ hx.1
      rw [← map_mul, hx2, map_one]
    · rintro t ht _ ⟨x, hx, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom]
      have htx : t x = x := by
        apply hinj
        rw [← CFSG.RankThree.PartTwo.KFacts.mul_mulAutConj_mul_inv, hc t ht _ hx.1]
        group
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, htx]
  by_cases hF : ∃ s ∈ A, ψ s = (Multiplicative.ofAdd 1, 1)
  · obtain ⟨s, hsA, hψs⟩ := hF
    rcases CFSG.RankThree.PartTwo.KFacts.L34.involution_cases hk hσ (hs s hsA) with
      hinn | ⟨H, hf | hd | hb⟩
    · rw [hIψ s hinn] at hψs
      exact absurd (congrArg Prod.fst hψs) (by decide)
    · obtain ⟨E, hEc, hEcomm, hEs, hEfix⟩ := hE (LinearFlag.conjAut 3 k H)
      have hτ : ∀ x ∈ E, LinearFlag.fieldAut 3 k σ x = x := by
        intro x hx
        have := hEfix s hsA x hx
        set c := LinearFlag.conjAut 3 k H
        rwa [hf, show c⁻¹ * (c * LinearFlag.fieldAut 3 k σ * c⁻¹) * c =
          LinearFlag.fieldAut 3 k σ by group] at this
      have h4' := card_le_four_of_field hk hσ hEcomm hEs hτ
      rw [hcardA, ← hEc]
      calc Nat.card E * Nat.card ψA.range ≤ 4 * 4 := Nat.mul_le_mul h4' hrange4
        _ = 16 := rfl
    · rw [hd, hψconj, hψd] at hψs
      exact absurd (congrArg Prod.fst hψs) (by decide)
    · rw [hb, hψconj, CFSG.RankThree.PartTwo.KFacts.L34.betaAut, map_mul, hψf, hψd] at hψs
      exact absurd (congrArg Prod.snd hψs) (by decide)
  ·
    have hrange2 : Nat.card ψA.range ≤ 2 := by
      have hne : ψA.range ≠ ⊤ := by
        intro htop
        have hmem : (Multiplicative.ofAdd (1 : ZMod 2), (1 : Multiplicative (ZMod 2))) ∈
            ψA.range := htop ▸ Subgroup.mem_top _
        obtain ⟨⟨s, hsA⟩, hs'⟩ := hmem
        exact hF ⟨s, hsA, hs'⟩
      have hne4 : Nat.card ψA.range ≠ 4 := fun h => hne ((Subgroup.card_eq_iff_eq_top _).1
        (h.trans h4.symm))
      have hd := Subgroup.card_subgroup_dvd_card ψA.range
      rw [h4] at hd
      have hpos : 0 < Nat.card ψA.range := Nat.card_pos
      have hle := Nat.le_of_dvd (by norm_num) hd
      interval_cases h : Nat.card ψA.range <;> simp_all
    by_cases hAI : A ≤ I
    · obtain ⟨E, hEc, hEcomm, hEs, -⟩ := hE 1
      have hA₀A : A₀ = A := inf_eq_left.2 hAI
      have := card_le_sixteen hk hEcomm hEs
      rw [hEc, hA₀A] at this
      exact this
    · obtain ⟨t, htA, htI⟩ := Set.not_subset.1 hAI
      have hfix : ∀ τ : MulAut (projectiveSL 3 k), ∀ H : GL (Fin 3) k,
          t = LinearFlag.conjAut 3 k H * τ * (LinearFlag.conjAut 3 k H)⁻¹ →
            ∃ E : Subgroup (projectiveSL 3 k),
            Nat.card E = Nat.card A₀ ∧ (∀ x ∈ E, ∀ y ∈ E, x * y = y * x) ∧
              (∀ x ∈ E, x * x = 1) ∧ ∀ x ∈ E, τ x = x := by
        intro τ H htτ
        obtain ⟨E, hEc, hEcomm, hEs, hEfix⟩ := hE (LinearFlag.conjAut 3 k H)
        refine ⟨E, hEc, hEcomm, hEs, fun x hx => ?_⟩
        have := hEfix t htA x hx
        set c := LinearFlag.conjAut 3 k H
        rwa [htτ, show c⁻¹ * (c * τ * c⁻¹) * c = τ by group] at this
      have h8 : Nat.card A₀ ≤ 8 := by
        rcases CFSG.RankThree.PartTwo.KFacts.L34.involution_cases hk hσ (hs t htA) with
          hinn | ⟨H, hf | hd | hb⟩
        · exact absurd hinn htI
        · obtain ⟨E, hEc, hEcomm, hEs, hEfix⟩ := hfix _ H hf
          rw [← hEc]
          exact (card_le_four_of_field hk hσ hEcomm hEs hEfix).trans (by norm_num)
        · obtain ⟨E, hEc, hEcomm, hEs, hEfix⟩ := hfix _ H hd
          rw [← hEc]
          exact card_le_eight_of_ne hEs (card_le_sixteen hk hEcomm hEs)
            (card_ne_sixteen_of_dual hk hEcomm hEs hEfix)
        · obtain ⟨E, hEc, hEcomm, hEs, hEfix⟩ := hfix _ H hb
          rw [← hEc]
          exact card_le_eight_of_ne hEs (card_le_sixteen hk hEcomm hEs)
            (card_ne_sixteen_of_beta hk hEcomm hEs hEfix)
      rw [hcardA]
      calc Nat.card A₀ * Nat.card ψA.range ≤ 8 * 2 := Nat.mul_le_mul h8 hrange2
        _ = 16 := rfl

end KGL34A

theorem l34AutTwoRankFact_holds : L34AutTwoRankFact := by
  intro X _ _ hX A hA
  obtain ⟨k, _, _, hk, ⟨e⟩⟩ := exists_mulEquiv_projectiveSL_of_lieModel hX
  obtain ⟨hcomm, hsq⟩ := hA
  set A' := A.map (MulAut.congr e).toMonoidHom with hA'
  have hcard : Nat.card A' = Nat.card A := by
    rw [hA', Subgroup.card_map_of_injective (MulAut.congr e).injective]
  have hc : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hs : ∀ a ∈ A', a * a = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    rw [← map_mul, ← sq, hsq a ha, map_one]
  rw [← hcard]
  exact KGL34A.card_le_of_mulAut hk hc hs

end CFSG.Quasithin.H13
