module

public import CFSG.RankThree.PartOne.CTP.OutEmbed
public import CFSG.RankThree.PartOne.CTP.StrongPGlue
import CFSG.GroupTheory.WielandtProductBasic
import CFSG.Walter.J1.Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ

open Subgroup
open scoped Pointwise

variable {X : Type} [Group X] [Finite X]

theorem eq_one_of_forall_sylow_le {p : ℕ} [Fact p.Prime] {N : Subgroup X}
    (hN : ∃ P₀ : Sylow p X, (P₀ : Subgroup X) ≤ N)
    (h : ∀ P₀ : Sylow p X, (P₀ : Subgroup X) ≤ N → ∀ y ∈ (P₀ : Subgroup X),
      (∀ n ∈ normalizer ((P₀ : Subgroup X) : Set X), y * n = n * y) → y = 1)
    (P : Sylow p X) {x : X} (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  obtain ⟨P₀, hP₀N⟩ := hN
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P₀ P
  have hcoe : ((g • P₀ : Sylow p X) : Subgroup X) =
      (P₀ : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  have hNconj : (Subgroup.normalizer ((P : Subgroup X) : Set X)) =
      (Subgroup.normalizer ((P₀ : Subgroup X) : Set X)).map
        (MulAut.conj g).toMonoidHom := by
    rw [← hg, hcoe]
    exact (Subgroup.map_normalizer_eq_of_bijective _ (MulAut.conj g).bijective).symm
  have hyP₀ : g⁻¹ * x * g ∈ (P₀ : Subgroup X) := by
    have hx' : x ∈ ((g • P₀ : Sylow p X) : Subgroup X) := hg.symm ▸ hxP
    exact (CFSG.GroupTheory.WielandtProduct.mem_smul_sylow_iff
      (P := P₀) (g := g) (x := x)).mp hx'
  have hycomm : ∀ n ∈ normalizer ((P₀ : Subgroup X) : Set X),
      (g⁻¹ * x * g) * n = n * (g⁻¹ * x * g) := by
    intro n hn
    have hgn : g * n * g⁻¹ ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) := by
      rw [hNconj]
      simpa [MulAut.conj_apply] using
        (Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hn)
    have hcomm : x * (g * n * g⁻¹) = (g * n * g⁻¹) * x := hx _ hgn
    calc (g⁻¹ * x * g) * n = g⁻¹ * (x * (g * n * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * n * g⁻¹) * x) * g := by rw [hcomm]
      _ = n * (g⁻¹ * x * g) := by group
  have hy1 : g⁻¹ * x * g = 1 := h P₀ hP₀N _ hyP₀ hycomm
  calc x = g * (g⁻¹ * x * g) * g⁻¹ := by group
    _ = g * 1 * g⁻¹ := by rw [hy1]
    _ = 1 := by group

theorem le_of_not_dvd_card_outer {p : ℕ} [Fact p.Prime] {K : Subgroup X} [K.Normal]
    (hKC : centralizer (K : Set X) = ⊥)
    (hout : ¬ p ∣ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K))
    (P : Sylow p X) : (P : Subgroup X) ≤ K := by
  have hdvd : Nat.card (X ⧸ K) ∣
      Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥K) :=
    Subgroup.card_dvd_of_injective _
      (CFSG.RankThree.PartOne.CTP.quotientOuterHom_injective K hKC)
  have hnot : ¬ p ∣ Nat.card (X ⧸ K) := fun hp => hout (hp.trans hdvd)
  exact CFSG.RankThree.PartOne.CTP.le_of_isPGroup_of_not_dvd_card_quotient
    P.isPGroup' hnot

theorem le_of_forall_pElement_mem {p : ℕ} [Fact p.Prime] {N K : Subgroup X} [K.Normal]
    (hN : CFSG.RankThree.PartOne.IsStronglyPEmbedded p N)
    (h : ∀ z : X, z ∈ N → IsPGroup p (zpowers z) → z ∈ K) (P : Sylow p X) :
    (P : Subgroup X) ≤ K := by
  obtain ⟨P₀, hP₀syl, hP₀N⟩ := hN.exists_isSylowOf_le
  have hP₀index : ¬ p ∣ P₀.index := by
    have := hP₀syl.2.2
    rwa [Subgroup.relIndex_top_right] at this
  let R : Sylow p X := hP₀syl.2.1.toSylow hP₀index
  have hRcoe : (R : Subgroup X) = P₀ := IsPGroup.toSylow_coe hP₀syl.2.1 hP₀index
  have hRK : P₀ ≤ K := by
    intro z hz
    exact h z (hP₀N hz) (hP₀syl.2.1.to_le (Subgroup.zpowers_le.mpr hz))
  have hRleK : (R : Subgroup X) ≤ K := hRcoe ▸ hRK
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X R P
  intro y hy
  have hy' : g⁻¹ * y * g ∈ (R : Subgroup X) := by
    have hyR : y ∈ ((g • R : Sylow p X) : Subgroup X) := hg.symm ▸ hy
    exact (CFSG.GroupTheory.WielandtProduct.mem_smul_sylow_iff
      (P := R) (g := g) (x := y)).mp hyR
  have hyK : g * (g⁻¹ * y * g) * g⁻¹ ∈ K :=
    Subgroup.Normal.conj_mem (inferInstance : K.Normal) _ (hRleK hy') g
  rw [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at hyK
  exact hyK

theorem commute_of_card_dvd_sq {p : ℕ} [Fact p.Prime] {P : Subgroup X} (hP : IsPGroup p P)
    (h : Nat.card P ∣ p ^ 2) : ∀ a ∈ P, ∀ b ∈ P, a * b = b * a := by
  obtain ⟨k, hk2, hcard⟩ := (Nat.dvd_prime_pow (Fact.out : p.Prime)).mp h
  interval_cases k
  · have hbot : P = ⊥ := Subgroup.card_eq_one.mp (by simpa using hcard)
    intro a ha b hb
    have ha1 : a = 1 := by simpa [hbot] using ha
    have hb1 : b = 1 := by simpa [hbot] using hb
    rw [ha1, hb1]
  · have hcomm : IsMulCommutative P :=
      (isCyclic_of_prime_card (α := P) (by simpa using hcard)).isMulCommutative
    intro a ha b hb
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  · have hcomm : IsMulCommutative P :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := p) (G := P)
        (by simpa using hcard)
    intro a ha b hb
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem eq_one_of_le_of_commute {p : ℕ} [Fact p.Prime] {K : Subgroup X} [K.Normal]
    [IsSimpleGroup ↥K] (hKnab : ∃ a b : ↥K, a * b ≠ b * a) (P : Sylow p X)
    (hPK : (P : Subgroup X) ≤ K)
    (hab : ∀ a ∈ (P : Subgroup X), ∀ b ∈ (P : Subgroup X), a * b = b * a)
    {x : X} (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  let T : Sylow p ↥K := P.subtype hPK
  have hTcoe : (T : Subgroup ↥K) = (P : Subgroup X).subgroupOf K := by
    simpa only [T] using Sylow.coe_subtype P hPK
  have hTmap : ((T : Subgroup ↥K)).map K.subtype = (P : Subgroup X) := by
    rw [hTcoe]
    exact Subgroup.map_subgroupOf_eq_of_le hPK
  haveI hTcomm : IsMulCommutative ((T : Sylow p ↥K) : Subgroup ↥K) := by
    apply IsMulCommutative.of_comm
    intro a b
    apply Subtype.ext
    apply Subtype.ext
    have haP : ((a : ↥K) : X) ∈ (P : Subgroup X) := by
      have h := Subgroup.mem_map_of_mem K.subtype a.2
      rwa [hTmap] at h
    have hbP : ((b : ↥K) : X) ∈ (P : Subgroup X) := by
      have h := Subgroup.mem_map_of_mem K.subtype b.2
      rwa [hTmap] at h
    exact hab _ haP _ hbP
  have hNmap : (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype ≤
      Subgroup.normalizer ((P : Subgroup X) : Set X) := by
    simpa [hTmap] using
      Subgroup.le_normalizer_map (H := (T : Subgroup ↥K)) K.subtype
  let z : ↥K := ⟨x, hPK hxP⟩
  have hzT : z ∈ (T : Subgroup ↥K) := by
    rw [hTcoe, Subgroup.mem_subgroupOf]
    exact hxP
  have hzcomm : ∀ n ∈ Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K), n * z = z * n := by
    intro n hn
    have hnX : ((n : ↥K) : X) ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) :=
      hNmap (Subgroup.mem_map_of_mem K.subtype hn)
    apply Subtype.ext
    simpa using (hx ((n : ↥K) : X) hnX).symm
  have hz1 := CFSG.Walter.J1.eq_one_of_mem_sylow_of_commute_normalizer
    (G := ↥K) hKnab T hzT hzcomm
  simpa [z] using congrArg Subtype.val hz1

theorem eq_one_of_torus {p e : ℕ} [Fact p.Prime] {F : Type} [Field F] {K : Subgroup X}
    (P : Sylow p X) (hPK : (P : Subgroup X) ≤ K) (ψ : Multiplicative F →* ↥K)
    (hψ : Function.Injective ψ)
    (hψr : ψ.range = ((P.subtype hPK : Sylow p ↥K) : Subgroup ↥K) ⊓
      centralizer (((P.subtype hPK : Sylow p ↥K) : Subgroup ↥K) : Set ↥K))
    (htor : ∀ μ : Fˣ, ∃ c ∈ normalizer (((P.subtype hPK : Sylow p ↥K) : Subgroup ↥K) : Set ↥K),
      ∀ a : Multiplicative F,
        c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) ^ e * Multiplicative.toAdd a)))
    (hμ : ∃ μ : Fˣ, (μ : F) ^ e ≠ 1)
    {x : X} (hxP : x ∈ (P : Subgroup X))
    (hx : ∀ n ∈ normalizer ((P : Subgroup X) : Set X), x * n = n * x) : x = 1 := by
  let T : Sylow p ↥K := P.subtype hPK
  have hT : T = P.subtype hPK := rfl
  have hTcoe : (T : Subgroup ↥K) = (P : Subgroup X).subgroupOf K := by
    simpa only [hT] using Sylow.coe_subtype P hPK
  have hTmap : ((T : Subgroup ↥K)).map K.subtype = (P : Subgroup X) := by
    rw [hTcoe]
    exact Subgroup.map_subgroupOf_eq_of_le hPK
  have hψr' : ψ.range = (T : Subgroup ↥K) ⊓
      centralizer (((T : Subgroup ↥K)) : Set ↥K) := by
    simpa only [hT] using hψr
  have htor' : ∀ μ : Fˣ, ∃ c ∈ normalizer ((T : Subgroup ↥K) : Set ↥K),
      ∀ a : Multiplicative F,
        c * ψ a * c⁻¹ = ψ (Multiplicative.ofAdd ((μ : F) ^ e * Multiplicative.toAdd a)) := by
    simpa only [hT] using htor
  have hNmap : (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)).map K.subtype ≤
      Subgroup.normalizer ((P : Subgroup X) : Set X) := by
    simpa [hTmap] using
      Subgroup.le_normalizer_map (H := (T : Subgroup ↥K)) K.subtype
  let x' : ↥K := ⟨x, hPK hxP⟩
  have hx'T : x' ∈ (T : Subgroup ↥K) := by
    rw [hTcoe, Subgroup.mem_subgroupOf]
    exact hxP
  have hx'cent : x' ∈ centralizer (((T : Subgroup ↥K)) : Set ↥K) := by
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    apply Subtype.ext
    have htP : ((t : ↥K) : X) ∈ (P : Subgroup X) := by
      have h := Subgroup.mem_map_of_mem K.subtype ht
      rwa [hTmap] at h
    have htN : ((t : ↥K) : X) ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) :=
      Subgroup.le_normalizer htP
    simpa using (hx ((t : ↥K) : X) htN).symm
  have hx'range : x' ∈ ψ.range := by
    rw [hψr']
    exact ⟨hx'T, hx'cent⟩
  rw [MonoidHom.mem_range] at hx'range
  obtain ⟨a, ha⟩ := hx'range
  obtain ⟨μ, hμ⟩ := hμ
  obtain ⟨c, hcN, hcact⟩ := htor' μ
  have hcX : ((c : ↥K) : X) ∈ Subgroup.normalizer ((P : Subgroup X) : Set X) :=
    hNmap (Subgroup.mem_map_of_mem K.subtype hcN)
  have hxcommc : x * ((c : ↥K) : X) = ((c : ↥K) : X) * x := hx _ hcX
  have hx'c : x' * c = c * x' := by
    apply Subtype.ext
    exact hxcommc
  have hcψ : c * ψ a * c⁻¹ = ψ a := by
    rw [ha]
    rw [← hx'c]
    group
  have hψeq : ψ (Multiplicative.ofAdd ((μ : F) ^ e * Multiplicative.toAdd a)) = ψ a :=
    (hcact a).symm.trans hcψ
  have hof : Multiplicative.ofAdd ((μ : F) ^ e * Multiplicative.toAdd a) = a := hψ hψeq
  have hmul : (μ : F) ^ e * Multiplicative.toAdd a = Multiplicative.toAdd a :=
    congrArg Multiplicative.toAdd hof
  have hsub : ((μ : F) ^ e - 1) * Multiplicative.toAdd a = 0 := by
    rw [sub_mul, one_mul, hmul, sub_self]
  have hμne : (μ : F) ^ e - 1 ≠ 0 := sub_ne_zero.mpr hμ
  have hzero : Multiplicative.toAdd a = 0 := by
    rcases mul_eq_zero.mp hsub with h | h
    · exact absurd h hμne
    · exact h
  have ha1 : a = 1 := by
    have := congrArg Multiplicative.ofAdd hzero
    simpa using this
  have hx'1 : x' = 1 := by
    rw [← ha, ha1, map_one]
  simpa [x'] using congrArg Subtype.val hx'1

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KIZ
