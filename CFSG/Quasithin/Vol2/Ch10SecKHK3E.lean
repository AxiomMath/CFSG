module

public import CFSG.Quasithin.Vol2.Ch10SecKHK3A
public import CFSG.Assembly.Defs
public import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.LieType.BorelTits

theorem exists_torus_of_radicalData {Γ : Type} [Group Γ] [Finite Γ] {J L V₁ : Subgroup Γ}
    {S : Type} [Group S] [Finite S] (ψ : ↥J ≃* S) {N Xj : Subgroup S} {q : ℕ}
    (hN : (L.subgroupOf J).map ψ.toMonoidHom = N) (hD : RadicalData N Xj q)
    (hLJ : L ≤ J) (hV₁L : V₁ ≤ L) (hV₁2 : IsPGroup 2 V₁)
    (hLV : L ≤ Subgroup.normalizer (V₁ : Set Γ)) (hcomm : ⁅V₁, L⁆ = V₁) (hV1 : V₁ ≠ ⊥) :
    ∃ X : Subgroup Γ, X ≤ J ⊓ Subgroup.normalizer (L : Set Γ) ∧ Nat.card X = q - 1 ∧
      (∀ x ∈ X, ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ V₁) ∧
      X ⊓ Subgroup.centralizer (V₁ : Set Γ) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hVc, ⟨C, hCV, hCN, hirr⟩, hcm, hXN, hXc, hXsc, hXfpf⟩ := hD
  have hV₁J : V₁ ≤ J := hV₁L.trans hLJ
  set W := (V₁.subgroupOf J).map ψ.toMonoidHom with hWdef
  have hmemW : ∀ y : S, y ∈ W ↔ ((ψ.symm y : ↥J) : Γ) ∈ V₁ := by
    intro y
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hz
    · intro h
      exact ⟨ψ.symm y, h, by simp⟩
  have hmemN : ∀ y : S, y ∈ N ↔ ((ψ.symm y : ↥J) : Γ) ∈ L := by
    intro y
    rw [← hN]
    constructor
    · rintro ⟨z, hz, rfl⟩
      simpa [Subgroup.mem_subgroupOf] using hz
    · intro h
      exact ⟨ψ.symm y, h, by simp⟩
  have hWN' : W ≤ N := by
    intro y hy
    rw [hmemN]
    exact hV₁L ((hmemW y).1 hy)
  have hNW : N ≤ Subgroup.normalizer (W : Set S) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [hmemW, hmemW]
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    exact Subgroup.mem_normalizer_iff.1 (hLV ((hmemN n).1 hn)) _
  have hW2 : IsPGroup 2 W :=
    (hV₁2.of_equiv (Subgroup.subgroupOfEquivOfLe hV₁J).symm).map _
  have hWV : W ≤ pCoreOf 2 N := le_pCoreOf_of_le_normalizer 2 hWN' hNW hW2
  have hcommW : ⁅W, N⁆ = W := by
    have h1 : ⁅V₁.subgroupOf J, L.subgroupOf J⁆ = V₁.subgroupOf J := by
      apply Subgroup.map_injective J.subtype_injective
      rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hV₁J,
        Subgroup.map_subgroupOf_eq_of_le hLJ, hcomm]
    rw [← hN, hWdef, ← Subgroup.map_commutator, h1]
  have hW1 : W ≠ ⊥ := by
    intro h
    apply hV1
    rw [eq_bot_iff]
    intro v hv
    have h1 : ψ ⟨v, hV₁J hv⟩ ∈ W := ⟨⟨v, hV₁J hv⟩, hv, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    have h2 := ψ.injective (h1.trans (map_one ψ).symm)
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  have hWeq : W = pCoreOf 2 N := eq_of_commutator_eq hVc hCV hCN hirr hcm hWV hNW hcommW hW1
  have hmemX : ∀ x : Γ, x ∈ (Xj.map ψ.symm.toMonoidHom).map J.subtype ↔
      ∃ y ∈ Xj, ((ψ.symm y : ↥J) : Γ) = x := by
    intro x
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨z, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨ψ.symm y, ⟨y, hy, rfl⟩, rfl⟩
  have hconjL : ∀ y ∈ Xj, ∀ l ∈ L,
      ((ψ.symm y : ↥J) : Γ) * l * ((ψ.symm y : ↥J) : Γ)⁻¹ ∈ L := by
    intro y hy l hl
    have hlN : ψ ⟨l, hLJ hl⟩ ∈ N := (hmemN _).2 (by simpa using hl)
    have h1 := (Subgroup.mem_normalizer_iff.1 (hXN hy) (ψ ⟨l, hLJ hl⟩)).1 hlN
    have h2 := (hmemN _).1 h1
    simpa using h2
  refine ⟨(Xj.map ψ.symm.toMonoidHom).map J.subtype, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨y, hy, rfl⟩ := (hmemX x).1 hx
    refine Subgroup.mem_inf.2 ⟨(ψ.symm y).2, ?_⟩
    rw [Subgroup.mem_normalizer_iff]
    intro l
    refine ⟨fun hl => hconjL y hy l hl, fun hl => ?_⟩
    have h3 := hconjL y⁻¹ (Xj.inv_mem hy) _ hl
    simpa [mul_assoc] using h3
  · rw [Subgroup.card_map_of_injective J.subtype_injective,
      Subgroup.card_map_of_injective (f := ψ.symm.toMonoidHom) ψ.symm.injective, hXc]
  · intro x hx l hl
    obtain ⟨y, hy, rfl⟩ := (hmemX x).1 hx
    have hlN : ψ ⟨l, hLJ hl⟩ ∈ N := (hmemN _).2 (by simpa using hl)
    have h1 := hXsc y hy _ hlN
    rw [← hWeq, hmemW] at h1
    simpa using h1
  · rw [eq_bot_iff]
    rintro x ⟨hx, hxc⟩
    obtain ⟨y, hy, rfl⟩ := (hmemX x).1 hx
    rw [Subgroup.mem_bot]
    by_contra hne
    have hy1 : y ≠ 1 := by
      rintro rfl
      exact hne (by simp)
    apply hW1
    rw [eq_bot_iff]
    intro v hv
    rw [Subgroup.mem_bot]
    have hv' : v ∈ pCoreOf 2 N := by
      rw [← hWeq]
      exact hv
    refine hXfpf y hy hy1 v hv' ?_
    have hvV : ((ψ.symm v : ↥J) : Γ) ∈ V₁ := (hmemW v).1 hv
    have h1 := Subgroup.mem_centralizer_iff.1 hxc _ hvV
    apply ψ.symm.injective
    apply Subtype.ext
    simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← h1, mul_inv_cancel_right]

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
