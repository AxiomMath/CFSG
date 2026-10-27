module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLLine63H5LayerGroup
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly

theorem rckEq_of_blockAction {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    {B₁ D J K : Subgroup X} {d : X} (hDcard : Nat.card D = p ^ 2)
    (hB₁J : B₁ ⊓ Subgroup.centralizer (J : Set X) = D) (hp4 : p ^ 4 ≤ Nat.card B₁)
    (hJK : J ≤ K) (hK : IsQuasisimple ↥K) (hdD : d ∈ D)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d}))
    {M : Type} [Group M] (β : ↥B₁ →* M)
    (hβ : ∀ b : ↥B₁, β b = 1 → (b : X) ∈ Subgroup.centralizer (K : Set X))
    (hcard : Nat.card β.range ≤ p ^ 2) : K = J := by
  let N : Subgroup X := β.ker.map B₁.subtype
  have hNleB : N ≤ B₁ := Subgroup.map_subtype_le β.ker
  have hNK : N ≤ Subgroup.centralizer (K : Set X) := by
    intro x hx
    obtain ⟨b, hb, rfl⟩ := hx
    exact hβ b (MonoidHom.mem_ker.mp hb)
  have hNleD : N ≤ D := by
    rw [← hB₁J]
    exact le_inf hNleB (hNK.trans (Subgroup.centralizer_le fun x hx => hJK hx))
  have hNcard : Nat.card N = Nat.card β.ker :=
    Subgroup.card_map_of_injective (K := β.ker) B₁.subtype_injective
  have hker_le : Nat.card β.ker ≤ p ^ 2 := by
    calc Nat.card β.ker = Nat.card N := hNcard.symm
      _ ≤ Nat.card D := Subgroup.card_le_of_le hNleD
      _ = p ^ 2 := hDcard
  have hprod := Subgroup.card_ker_mul_card_range β
  have hker_ge : p ^ 2 ≤ Nat.card β.ker := by
    have hb_le : Nat.card β.ker * Nat.card β.range ≤ Nat.card β.ker * p ^ 2 :=
      Nat.mul_le_mul_left _ hcard
    have hp4' : p ^ 2 * p ^ 2 ≤ Nat.card β.ker * p ^ 2 := by
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ ≤ Nat.card ↥B₁ := hp4
        _ = Nat.card β.ker * Nat.card β.range := hprod.symm
        _ ≤ Nat.card β.ker * p ^ 2 := hb_le
    exact Nat.le_of_mul_le_mul_right hp4' (pow_pos hp.pos 2)
  have hker_eq : Nat.card β.ker = p ^ 2 := le_antisymm hker_le hker_ge
  have hND : N = D := by
    refine Subgroup.eq_of_le_of_card_ge hNleD ?_
    rw [hDcard, hNcard, hker_eq]
  have hdN : d ∈ N := by rw [hND]; exact hdD
  have hdcent : d ∈ Subgroup.centralizer (K : Set X) := hNK hdN
  have hKle : K ≤ Subgroup.centralizer ({d} : Set X) := by
    intro k hk
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_iff.mp hdcent k hk)
  have hKinf : K ⊓ Subgroup.centralizer ({d} : Set X) = K := inf_eq_left.mpr hKle
  have hJ' : IsComponentOf J K := by
    rw [hKinf] at hJ
    exact hJ
  have hKasm : Assembly.IsQuasisimple ↥K :=
    ⟨Group.isPerfect_def.mp hK.1, hK.2.1⟩
  exact (CFSG.StandardType.Line63.H5.eq_of_isComponentOf_of_isQuasisimple hJ' hKasm).symm

end CFSG.StandardType.RCKRP
