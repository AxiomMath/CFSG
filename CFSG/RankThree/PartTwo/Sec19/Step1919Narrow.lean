module

public import CFSG.RankThree.PartTwo.Sec19.Step1919O2
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.Sec19.Step1910O2Proof
public import CFSG.RankThree.PartTwo.Sec19.Step1910Proof

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

namespace Step1919Narrow

variable {G : Type} [Group G] [Finite G]

theorem not_mem_pCoreOf_of_pow_three {K : Subgroup G} {x : G} (hx3 : x ^ 3 = 1)
    (hx1 : x ≠ 1) : x ∉ CFSG.Open.pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro hx
  obtain ⟨j, hj⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨x, hx⟩
  exact hx1 (eq_one_of_pow_two_pow_of_pow_three_pow (j := j) (k := 1)
    (by simpa using congrArg Subtype.val hj) (by rw [pow_one]; exact hx3))

omit [Finite G] in
theorem not_mem_of_exists_not_mem {M K : Subgroup G} (hKM : K ≤ M) {z : G}
    (hz : ∃ k ∈ K, z * k * z⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) :
    z ∉ CFSG.Open.pCoreOf 2 M := by
  obtain ⟨k, hk, hzk⟩ := hz
  intro hzQ
  apply hzk
  have hkN : k ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hKM hk)
  have h1 : k * z⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M :=
    (Subgroup.mem_normalizer_iff.mp hkN _).mp (inv_mem hzQ)
  have h2 := (CFSG.Open.pCoreOf 2 M).mul_mem hzQ h1
  rwa [show z * (k * z⁻¹ * k⁻¹) = z * k * z⁻¹ * k⁻¹ by group] at h2

omit [Finite G] in
theorem conj_pow_three_mem {M : Subgroup G} {b z : G} (hb : b ∈ M)
    (hz : z ^ 3 ∈ CFSG.Open.pCoreOf 2 M) : (b * z * b⁻¹) ^ 3 ∈ CFSG.Open.pCoreOf 2 M := by
  rw [conj_pow]
  exact (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hb) _).mp hz

omit [Finite G] in
theorem conj_exists_not_mem {M K : Subgroup G} {b z : G} (hb : b ∈ M)
    (hz : ∃ k ∈ K, z * k * z⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M) :
    ∃ k ∈ K.map (MulAut.conj b).toMonoidHom,
      (b * z * b⁻¹) * k * (b * z * b⁻¹)⁻¹ * k⁻¹ ∉ CFSG.Open.pCoreOf 2 M := by
  obtain ⟨k, hk, hzk⟩ := hz
  refine ⟨b * k * b⁻¹, ⟨k, hk, rfl⟩, fun h => hzk ?_⟩
  have e : (b * z * b⁻¹) * (b * k * b⁻¹) * (b * z * b⁻¹)⁻¹ * (b * k * b⁻¹)⁻¹ =
      b * (z * k * z⁻¹ * k⁻¹) * b⁻¹ := by group
  rw [e] at h
  exact (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hb) _).mpr h

omit [Finite G] in
theorem conj_forall_mem {M K : Subgroup G} {b w : G} (hb : b ∈ M) (hwb : w * b = b * w)
    (hw : ∀ k ∈ K, w * k * w⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    ∀ k ∈ K.map (MulAut.conj b).toMonoidHom, w * k * w⁻¹ * k⁻¹ ∈ CFSG.Open.pCoreOf 2 M := by
  rintro _ ⟨k, hk, rfl⟩
  have hbw : b⁻¹ * w * b = w := by rw [mul_assoc, hwb]; group
  have e : w * (b * k * b⁻¹) * w⁻¹ * (b * k * b⁻¹)⁻¹ =
      b * ((b⁻¹ * w * b) * k * (b⁻¹ * w * b)⁻¹ * k⁻¹) * b⁻¹ := by group
  rw [hbw] at e
  change w * (b * k * b⁻¹) * w⁻¹ * (b * k * b⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 M
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hb) _).mp (hw k hk)

omit [Finite G] in
theorem mem_normalizer_centralizer {X : Type*} [Group X] {S : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (S : Set X)) :
    g ∈ Subgroup.normalizer (Subgroup.centralizer (S : Set X) : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hh s hs
    have hs' : g⁻¹ * s * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) s).mp hs
      simpa using this
    have h1 := hh _ hs'
    calc s * (g * h * g⁻¹) = g * ((g⁻¹ * s * g) * h) * g⁻¹ := by group
      _ = g * (h * (g⁻¹ * s * g)) * g⁻¹ := by rw [h1]
      _ = g * h * g⁻¹ * s := by group
  · intro hh s hs
    have hs' : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg s).mp hs
    have h1 := hh _ hs'
    have e1 : g * (s * h) * g⁻¹ = g * (h * s) * g⁻¹ := by
      calc g * (s * h) * g⁻¹ = (g * s * g⁻¹) * (g * h * g⁻¹) := by group
        _ = (g * h * g⁻¹) * (g * s * g⁻¹) := h1
        _ = g * (h * s) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel e1)

omit [Finite G] in
theorem mk_mem_normalizer_map {M J : Subgroup G} (b : M)
    (hb : (b : G) ∈ Subgroup.normalizer (J : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 M) b ∈ Subgroup.normalizer
      ((J.subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 M)) : Set (M ⧸ CFSG.pCore 2 M)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 M) h
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨m', hm', hmm'⟩
    refine ⟨b * m' * b⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hb _).mp hm'
    · rw [map_mul, map_mul, map_inv, hmm']
  · rintro ⟨m', hm', hmm'⟩
    refine ⟨b⁻¹ * m' * b, ?_, ?_⟩
    · have := (Subgroup.mem_normalizer_iff.mp (inv_mem hb) _).mp hm'
      simpa using this
    · rw [map_mul, map_mul, map_inv, hmm']
      group

theorem exists_not_mem_of_not_mem_center {M J : Subgroup G} (hJM : J ∈ oTwoComponentsIn M)
    (z : J) (hz : (z : J ⧸ CFSG.pCore 2 J) ∉ Subgroup.center (J ⧸ CFSG.pCore 2 J)) :
    ∃ j ∈ J, (z : G) * j * (z : G)⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ : ∃ g : J, (z : J ⧸ CFSG.pCore 2 J) * g ≠ g * z := by
    by_contra hall
    push Not at hall
    apply hz
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    exact (hall g).symm
  refine ⟨g, g.2, fun h => hg ?_⟩
  have h2 : (z * g * z⁻¹ * g⁻¹ : J) ∈ CFSG.pCore 2 J := by
    rw [Step1911EndProof.mem_pCore_iff]
    exact Step1910Proof.inf_pCoreOf_le hJM ⟨(z * g * z⁻¹ * g⁻¹ : J).2, h⟩
  have h3 : ((z * g * z⁻¹ * g⁻¹ : J) : J ⧸ CFSG.pCore 2 J) = 1 :=
    (QuotientGroup.eq_one_iff _).mpr h2
  rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
    QuotientGroup.mk_inv] at h3
  exact Step1910O2Proof.mul_comm_of_commutator_eq_one h3

theorem pow_three_mem_of_mk {M J : Subgroup G} (hJM : J ∈ oTwoComponentsIn M) (z : J)
    (hz : (z : J ⧸ CFSG.pCore 2 J) ^ 3 = 1) : (z : G) ^ 3 ∈ CFSG.Open.pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : z ^ 3 ∈ CFSG.pCore 2 J := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
    exact hz
  rw [Step1911EndProof.mem_pCore_iff] at h1
  exact Sec18.pCoreOf_le_pCoreOf_of_mem_oTwoComponentsIn hJM (by simpa using h1)

omit [Finite G] in
theorem map_conj_ne {J : Subgroup G} {e : G} (he3 : e ^ 3 = 1)
    (heJ : e ∉ Subgroup.normalizer (J : Set G)) :
    J ≠ J.map (MulAut.conj e).toMonoidHom ∧ J ≠ J.map (MulAut.conj (e * e)).toMonoidHom ∧
      J.map (MulAut.conj e).toMonoidHom ≠ J.map (MulAut.conj (e * e)).toMonoidHom := by
  have h1 : J ≠ J.map (MulAut.conj e).toMonoidHom := fun h =>
    heJ (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm)
  refine ⟨h1, fun h => ?_, fun h => ?_⟩
  · have h2 : e * e ∈ Subgroup.normalizer (J : Set G) :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr h.symm
    apply heJ
    have e' : e = (e * e) * (e * e) := by
      calc e = e ^ 3 * e := by rw [he3, one_mul]
        _ = (e * e) * (e * e) := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    rw [e']
    exact Subgroup.mul_mem _ h2 h2
  · apply h1
    have h3 := congrArg (Subgroup.map (MulAut.conj e⁻¹).toMonoidHom) h
    rw [Step199Proof.map_conj_map_conj, Step199Proof.map_conj_map_conj, inv_mul_cancel,
      Step199Proof.map_conj_one, show e⁻¹ * (e * e) = e by group] at h3
    exact h3

end Step1919Narrow

@[expose] def Step1919Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E M : Subgroup G),
    Ctx1912 G A c L E M → ¬ L ≤ M →
      Nat.card (E ⊓ L : Subgroup G) = 9 →
      Sec4.IsExtOf
        (oUpperThreePrime (Sec4.autIn (Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G)) E))
        (Matrix.SpecialLinearGroup (Fin 2) (ZMod 3))
        (Multiplicative (ZMod 3) × Multiplicative (ZMod 3)) →
      ∀ H ∈ scriptM (Subgroup.centralizer ({c} : Set G) : Set G), H ≠ M →
        (scriptJ M H).Nonempty →
        (∀ J ∈ scriptJ M H,
          (IsList194 (J ⧸ CFSG.pCore 2 J) ∨ IsSmall194 (J ⧸ CFSG.pCore 2 J)) ∧
          ((IsEmpty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
              IsProperParabolic (starIm J H)) ∨
            (Nonempty (J ⧸ CFSG.pCore 2 J ≃* alternatingGroup (Fin 10)) ∧
              Sec4.IsExtOf (starIm J H) (Equiv.Perm (Fin 5))
                (Multiplicative (Fin 4 → ZMod 2))))) →
        (∀ J ∈ scriptJ M H, E ≤ Subgroup.normalizer (J : Set G)) →
        (∀ J ∈ scriptJ M H, ∃ j ∈ J, c * j * c⁻¹ * j⁻¹ ∉ CFSG.Open.pCoreOf 2 M) →
          ∃ K ∈ scriptJ M H, E ≤ K

end CFSG.RankThree.PartTwo.Sec19
