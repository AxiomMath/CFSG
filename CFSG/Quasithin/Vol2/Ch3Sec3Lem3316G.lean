module

public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
public import CFSG.LocalAnalysis.SignalizerFunctor.AmbientCommutators
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.B6Defs
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.Quasithin.H13.L3316

open CFSG.QuasithinUnique
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_commutator {P X : Subgroup G} (hP : IsPGroup 2 P) (hX : IsPGroup 3 X)
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) {g : G}
    (hgP : g ∈ Subgroup.normalizer (P : Set G))
    (hgPX : g ∈ Subgroup.normalizer ((P ⊔ X : Subgroup G) : Set G)) :
    g ∈ Subgroup.normalizer ((⁅P, X⁆ : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 X (P ⊔ X) := by
    refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨le_sup_right, hX, fun h3 => ?_⟩
    rw [sup_comm, ← B6.relIndex_inf_eq_relIndex_sup hXP] at h3
    obtain ⟨k, hk⟩ := hP.exists_card_eq
    have h1 : (X ⊓ P).relIndex P ∣ 2 ^ k := hk ▸ Subgroup.index_dvd_card _
    have h2 := (Nat.prime_three.dvd_of_dvd_pow (h3.trans h1))
    norm_num at h2
  have hgPX' := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgPX
  have hS' : CFSG.ABGLocalTools.IsSylowOf 3 (X.map (MulAut.conj g).toMonoidHom) (P ⊔ X) := by
    refine CFSG.ABGLocalTools.isSylowOf_of_card ?_ ?_
    · rw [← hgPX']
      exact Subgroup.map_mono le_sup_right
    · rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hS.card_eq]
  obtain ⟨k, hk, hkc⟩ := hS.exists_mem_conj hS'
  have hPX : ((P ⊔ X : Subgroup G) : Set G) = (P : Set G) * (X : Set G) :=
    Subgroup.coe_mul_of_right_le_normalizer_left P X hXP
  have hk' : k ∈ ((P ⊔ X : Subgroup G) : Set G) := hk
  rw [hPX] at hk'
  obtain ⟨p, hp, y, hy, rfl⟩ := hk'
  have hXg : X.map (MulAut.conj g).toMonoidHom = X.map (MulAut.conj p).toMonoidHom := by
    ext z
    rw [hkc z, Subgroup.mem_map_equiv]
    simp only [MulAut.conj_symm_apply]
    constructor
    · intro hz
      have := X.mul_mem (X.mul_mem hy hz) (X.inv_mem hy)
      simpa [mul_assoc] using this
    · intro hz
      have := X.mul_mem (X.mul_mem (X.inv_mem hy) hz) hy
      simpa [mul_assoc] using this
  have hPp : P.map (MulAut.conj p).toMonoidHom = P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hp)
  have hPg : P.map (MulAut.conj g).toMonoidHom = P := Subgroup.mem_normalizer_iff_map_conj_eq.mp hgP
  have hCp : (⁅P, X⁆ : Subgroup G).map (MulAut.conj p).toMonoidHom = ⁅P, X⁆ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.normalizer_commutator_ge_left P X hp)
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    ← MulEquiv.toMonoidHom_eq_coe, hPg, hXg, ← hCp, Subgroup.map_commutator, hPp]

theorem commutator_eq_of_le {T P X : Subgroup G} (hT : IsPGroup 2 T) (hX : IsPGroup 3 X)
    (hXT : X ≤ Subgroup.normalizer (T : Set G)) (hPT : P ≤ T) (hTXP : ⁅T, X⁆ ≤ P) :
    ⁅P, X⁆ = ⁅T, X⁆ := by
  refine le_antisymm (Subgroup.commutator_mono hPT le_rfl) ?_
  have hcop : Nat.Coprime 3 (Nat.card T) := by
    obtain ⟨k, hk⟩ := hT.exists_card_eq
    rw [hk]
    exact Nat.Coprime.pow_right k (by norm_num)
  have h := CFSG.SignalizerFunctor.Helpers.coprime_normalized_commutator_idempotent 3
    Nat.prime_three X T hX hXT hcop
  calc ⁅T, X⁆ = ⁅⁅T, X⁆, X⁆ := h.symm
    _ ≤ ⁅P, X⁆ := Subgroup.commutator_mono hTXP le_rfl

end CFSG.Quasithin.H13.L3316
