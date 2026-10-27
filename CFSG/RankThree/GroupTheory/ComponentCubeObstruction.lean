module

public import CFSG.RankThree.CentralExtension.ThreeCoverCubeLifting
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.GroupTheory.ThetaComponents
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.LocalAnalysis.ComponentClassification.SimpleEvenOrder
import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantConjugacy
import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree

open Subgroup CFSG CFSG.RankThree.CentralExtension CFSG.RankThree.LocalRank
open CFSG.Assembly.RankThreeEven (localRank)
open scoped Pointwise

variable {G : Type*} [Group G]

theorem pow_orderOf_eq_one_of_mem_zpowers {v w : G} (hw : w ∈ zpowers v) :
    w ^ orderOf v = 1 := by
  obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hw
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, pow_orderOf_eq_one, one_zpow]

theorem card_sup_zpowers_of_disjoint {q : ℕ} {W : Subgroup G} {v : G}
    (hvW : v ∈ centralizer (W : Set G)) (hWc : IsMulCommutative W) (hWq : ∀ w ∈ W, w ^ q = 1)
    (hv : orderOf v = q) (hdisj : W ⊓ zpowers v = ⊥) :
    Nat.card (W ⊔ zpowers v : Subgroup G) = Nat.card W * q ∧
      IsMulCommutative (W ⊔ zpowers v : Subgroup G) ∧ ∀ w ∈ W ⊔ zpowers v, w ^ q = 1 := by
  have hle : zpowers v ≤ normalizer (W : Set G) := zpowers_le.2 (centralizer_le_normalizer _ hvW)
  refine ⟨?_, PGroups.isMulCommutative_sup_zpowers hWc hvW, fun w hw => ?_⟩
  · rw [CentralCover.card_sup_eq_mul_of_le_normalizer hle hdisj, Nat.card_zpowers, hv]
  · have hw' : w ∈ (W : Set G) * (zpowers v : Set G) := by
      rw [← coe_mul_of_right_le_normalizer_left W _ hle]
      exact hw
    obtain ⟨a, ha, b, hb, rfl⟩ := hw'
    obtain ⟨n, rfl⟩ := mem_zpowers_iff.1 hb
    have hcomm : Commute a (v ^ n) :=
      (show Commute a v from (mem_centralizer_iff.1 hvW a ha)).zpow_right n
    rw [hcomm.mul_pow, hWq a ha, one_mul, ← hv]
    exact pow_orderOf_eq_one_of_mem_zpowers (zpow_mem (mem_zpowers v) n)

theorem conj_mem_centralizer_map_conj_iff {L : Subgroup G} {g x : G} :
    g * x * g⁻¹ ∈ centralizer ((L.map (MulAut.conj g).toMonoidHom : Subgroup G) : Set G) ↔
      x ∈ centralizer (L : Set G) := by
  constructor
  · intro h
    rw [mem_centralizer_iff]
    intro l hl
    have h1 := mem_centralizer_iff.1 h (g * l * g⁻¹) ⟨l, hl, by simp⟩
    have h2 : g * (l * x) * g⁻¹ = g * (x * l) * g⁻¹ := by
      calc g * (l * x) * g⁻¹ = g * l * g⁻¹ * (g * x * g⁻¹) := by group
        _ = g * x * g⁻¹ * (g * l * g⁻¹) := h1
        _ = g * (x * l) * g⁻¹ := by group
    exact mul_left_cancel (mul_right_cancel h2)
  · intro h
    rw [mem_centralizer_iff]
    rintro _ ⟨l, hl, rfl⟩
    have h1 := mem_centralizer_iff.1 h l hl
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    calc g * l * g⁻¹ * (g * x * g⁻¹) = g * (l * x) * g⁻¹ := by group
      _ = g * (x * l) * g⁻¹ := by rw [h1]
      _ = g * x * g⁻¹ * (g * l * g⁻¹) := by group

theorem orderOf_conj_eq (g x : G) : orderOf (g * x * g⁻¹) = orderOf x := by
  have h := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
  simpa using h

variable [Finite G]

theorem zpowers_inf_eq_bot_of_not_mem {q : ℕ} (hq : q.Prime) {v : G} (hv : orderOf v = q)
    {S : Subgroup G} (hvS : v ∉ S) : zpowers v ⊓ S = ⊥ := by
  have hdvd : Nat.card (zpowers v ⊓ S : Subgroup G) ∣ q := by
    rw [← hv, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases hq.eq_one_or_self_of_dvd _ hdvd with h1 | hq'
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    have heq : zpowers v ⊓ S = zpowers v :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hq', Nat.card_zpowers, hv])
    exact hvS ((le_of_eq heq.symm).trans inf_le_right (mem_zpowers v))

theorem coprime_and_two_dvd_card_of_two_subgroup {U : Subgroup G} (hU : U ≠ ⊥)
    (hU2 : IsPGroup 2 U) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) :
    Nat.Coprime q (Nat.card U) ∧ 2 ∣ Nat.card U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.mp hU2
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hm
    exact hU (Subgroup.card_eq_one.mp hm)
  rw [hm]
  exact ⟨Nat.Coprime.pow_right m ((Nat.coprime_primes hq Nat.prime_two).mpr hq2),
    dvd_pow_self 2 hm0⟩

section Triple

variable {L : Subgroup G} {g₁ g₂ : G}

theorem conjugate_components_commute (hL : IsComponent L)
    (h01 : L ≠ L.map (MulAut.conj g₁).toMonoidHom) (h02 : L ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (h12 : L.map (MulAut.conj g₁).toMonoidHom ≠ L.map (MulAut.conj g₂).toMonoidHom) :
    L ≤ centralizer ((L.map (MulAut.conj g₁).toMonoidHom : Subgroup G) : Set G) ∧
      L ≤ centralizer ((L.map (MulAut.conj g₂).toMonoidHom : Subgroup G) : Set G) ∧
      L.map (MulAut.conj g₁).toMonoidHom ≤
        centralizer ((L.map (MulAut.conj g₂).toMonoidHom : Subgroup G) : Set G) := by
  have hK₁ : IsComponent (L.map (MulAut.conj g₁).toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv _ hL
  have hK₂ : IsComponent (L.map (MulAut.conj g₂).toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv _ hL
  exact ⟨commutator_eq_bot_iff_le_centralizer.1
      ((LocalCores.distinct_components_commute hL hK₁).resolve_left h01),
    commutator_eq_bot_iff_le_centralizer.1
      ((LocalCores.distinct_components_commute hL hK₂).resolve_left h02),
    commutator_eq_bot_iff_le_centralizer.1
      ((LocalCores.distinct_components_commute hK₁ hK₂).resolve_left h12)⟩

theorem mem_centralizer_of_conjugate_components (hL : IsComponent L)
    (h01 : L ≠ L.map (MulAut.conj g₁).toMonoidHom) (h02 : L ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (h12 : L.map (MulAut.conj g₁).toMonoidHom ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (hrank : localRank 3 G ≤ 3) {z : G} (hzL : z ∈ L) (hzc : z ∈ centralizer (L : Set G))
    (hz : orderOf z = 3) {U : Subgroup G} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hUL : U ≤ L)
    {x : G} (hxL : x ∈ L) (hxU : x ∈ normalizer (U : Set G)) (hx : x ^ 3 = 1) :
    x ∈ centralizer (L : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hxc
  obtain ⟨c01, c02, c12⟩ := conjugate_components_commute hL h01 h02 h12
  set K₁ := L.map (MulAut.conj g₁).toMonoidHom with hK₁def
  set K₂ := L.map (MulAut.conj g₂).toMonoidHom with hK₂def
  have hCU : centralizer (L : Set G) ≤ normalizer (U : Set G) :=
    (centralizer_le hUL).trans (centralizer_le_normalizer _)
  have hxo : orderOf x = 3 := orderOf_eq_prime hx fun h => hxc (h ▸ one_mem _)
  have hx₁K : g₁ * x * g₁⁻¹ ∈ K₁ := ⟨x, hxL, by simp⟩
  have hx₂K : g₂ * x * g₂⁻¹ ∈ K₂ := ⟨x, hxL, by simp⟩
  have hx₁c : g₁ * x * g₁⁻¹ ∉ centralizer (K₁ : Set G) := fun h =>
    hxc (conj_mem_centralizer_map_conj_iff.1 h)
  have hx₂c : g₂ * x * g₂⁻¹ ∉ centralizer (K₂ : Set G) := fun h =>
    hxc (conj_mem_centralizer_map_conj_iff.1 h)
  have hx₁o : orderOf (g₁ * x * g₁⁻¹) = 3 := by rw [orderOf_conj_eq, hxo]
  have hx₂o : orderOf (g₂ * x * g₂⁻¹) = 3 := by rw [orderOf_conj_eq, hxo]
  have hW₁L : zpowers z ≤ L := zpowers_le.2 hzL
  have hW₁C : zpowers z ≤ centralizer (L : Set G) := zpowers_le.2 hzc
  have hW₁q : ∀ w ∈ zpowers z, w ^ 3 = 1 := fun w hw => hz ▸ pow_orderOf_eq_one_of_mem_zpowers hw
  have hxW₁ : x ∈ centralizer (zpowers z : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (hW₁C hw) x hxL).symm
  have hd₂ : zpowers z ⊓ zpowers x = ⊥ := by
    rw [eq_bot_iff, ← zpowers_inf_eq_bot_of_not_mem Nat.prime_three hxo hxc]
    exact fun y hy => ⟨hy.2, hW₁C hy.1⟩
  obtain ⟨hW₂card, hW₂c, hW₂q⟩ :=
    card_sup_zpowers_of_disjoint hxW₁ inferInstance hW₁q hxo hd₂
  have hW₂L : zpowers z ⊔ zpowers x ≤ L := sup_le hW₁L (zpowers_le.2 hxL)
  have hW₂K₁ : zpowers z ⊔ zpowers x ≤ centralizer (K₁ : Set G) := hW₂L.trans c01
  have hx₁W₂ : g₁ * x * g₁⁻¹ ∈ centralizer ((zpowers z ⊔ zpowers x : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (hW₂K₁ hw) _ hx₁K).symm
  have hd₃ : (zpowers z ⊔ zpowers x) ⊓ zpowers (g₁ * x * g₁⁻¹) = ⊥ := by
    rw [eq_bot_iff, ← zpowers_inf_eq_bot_of_not_mem Nat.prime_three hx₁o hx₁c]
    exact fun y hy => ⟨hy.2, hW₂K₁ hy.1⟩
  obtain ⟨hW₃card, hW₃c, hW₃q⟩ := card_sup_zpowers_of_disjoint hx₁W₂ hW₂c hW₂q hx₁o hd₃
  have hW₃K₂ : zpowers z ⊔ zpowers x ⊔ zpowers (g₁ * x * g₁⁻¹) ≤ centralizer (K₂ : Set G) :=
    sup_le (hW₂L.trans c02) ((zpowers_le.2 hx₁K).trans c12)
  have hx₂W₃ : g₂ * x * g₂⁻¹ ∈
      centralizer ((zpowers z ⊔ zpowers x ⊔ zpowers (g₁ * x * g₁⁻¹) : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (hW₃K₂ hw) _ hx₂K).symm
  have hd₄ : (zpowers z ⊔ zpowers x ⊔ zpowers (g₁ * x * g₁⁻¹)) ⊓ zpowers (g₂ * x * g₂⁻¹) = ⊥ := by
    rw [eq_bot_iff, ← zpowers_inf_eq_bot_of_not_mem Nat.prime_three hx₂o hx₂c]
    exact fun y hy => ⟨hy.2, hW₃K₂ hy.1⟩
  obtain ⟨hW₄card, hW₄c, hW₄q⟩ := card_sup_zpowers_of_disjoint hx₂W₃ hW₃c hW₃q hx₂o hd₄
  have hcard : Nat.card (zpowers z ⊔ zpowers x ⊔ zpowers (g₁ * x * g₁⁻¹) ⊔
      zpowers (g₂ * x * g₂⁻¹) : Subgroup G) = 3 ^ 4 := by
    rw [hW₄card, hW₃card, hW₂card, Nat.card_zpowers, hz]
    norm_num
  have hWU : zpowers z ⊔ zpowers x ⊔ zpowers (g₁ * x * g₁⁻¹) ⊔ zpowers (g₂ * x * g₂⁻¹) ≤
      normalizer (U : Set G) := by
    refine sup_le (sup_le (sup_le (zpowers_le.2 (hCU hzc)) (zpowers_le.2 hxU)) ?_) ?_
    · exact zpowers_le.2 (hCU (le_centralizer_iff.1 c01 hx₁K))
    · exact zpowers_le.2 (hCU (le_centralizer_iff.1 c02 hx₂K))
  obtain ⟨hcop, h2⟩ := coprime_and_two_dvd_card_of_two_subgroup hU hU2 Nat.prime_three
    (by norm_num)
  have h4 := Classical2.le_localRank_of_normalizes Nat.prime_three hWU ⟨hW₄c, hW₄q⟩ hcard hcop h2
  omega

theorem orderOf_ne_of_conjugate_components (hL : IsComponent L)
    (h01 : L ≠ L.map (MulAut.conj g₁).toMonoidHom) (h02 : L ≠ L.map (MulAut.conj g₂).toMonoidHom)
    (h12 : L.map (MulAut.conj g₁).toMonoidHom ≠ L.map (MulAut.conj g₂).toMonoidHom) {q : ℕ}
    (hq : q.Prime) (hq3 : 3 < q) (hrank : localRank q G ≤ 2)
    (hZ3 : ∀ y ∈ L, y ∈ centralizer (L : Set G) → ∃ k : ℕ, y ^ 3 ^ k = 1) {U : Subgroup G}
    (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hUL : U ≤ L) {y : G} (hyL : y ∈ L)
    (hyU : y ∈ normalizer (U : Set G)) : orderOf y ≠ q := by
  intro hyo
  obtain ⟨c01, c02, c12⟩ := conjugate_components_commute hL h01 h02 h12
  set K₁ := L.map (MulAut.conj g₁).toMonoidHom with hK₁def
  set K₂ := L.map (MulAut.conj g₂).toMonoidHom with hK₂def
  have hCU : centralizer (L : Set G) ≤ normalizer (U : Set G) :=
    (centralizer_le hUL).trans (centralizer_le_normalizer _)
  have hyc : y ∉ centralizer (L : Set G) := by
    intro hyc
    obtain ⟨k, hk⟩ := hZ3 y hyL hyc
    have hdvd : q ∣ 3 ^ k := hyo ▸ orderOf_dvd_of_pow_eq_one hk
    have := (Nat.prime_dvd_prime_iff_eq hq Nat.prime_three).mp (hq.dvd_of_dvd_pow hdvd)
    omega
  have hy₁K : g₁ * y * g₁⁻¹ ∈ K₁ := ⟨y, hyL, by simp⟩
  have hy₂K : g₂ * y * g₂⁻¹ ∈ K₂ := ⟨y, hyL, by simp⟩
  have hy₁c : g₁ * y * g₁⁻¹ ∉ centralizer (K₁ : Set G) := fun h =>
    hyc (conj_mem_centralizer_map_conj_iff.1 h)
  have hy₂c : g₂ * y * g₂⁻¹ ∉ centralizer (K₂ : Set G) := fun h =>
    hyc (conj_mem_centralizer_map_conj_iff.1 h)
  have hy₁o : orderOf (g₁ * y * g₁⁻¹) = q := by rw [orderOf_conj_eq, hyo]
  have hy₂o : orderOf (g₂ * y * g₂⁻¹) = q := by rw [orderOf_conj_eq, hyo]
  have hW₁L : zpowers y ≤ L := zpowers_le.2 hyL
  have hW₁q : ∀ w ∈ zpowers y, w ^ q = 1 := fun w hw => hyo ▸ pow_orderOf_eq_one_of_mem_zpowers hw
  have hW₁K₁ : zpowers y ≤ centralizer (K₁ : Set G) := hW₁L.trans c01
  have hy₁W₁ : g₁ * y * g₁⁻¹ ∈ centralizer (zpowers y : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (hW₁K₁ hw) _ hy₁K).symm
  have hd₂ : zpowers y ⊓ zpowers (g₁ * y * g₁⁻¹) = ⊥ := by
    rw [eq_bot_iff, ← zpowers_inf_eq_bot_of_not_mem hq hy₁o hy₁c]
    exact fun w hw => ⟨hw.2, hW₁K₁ hw.1⟩
  obtain ⟨hW₂card, hW₂c, hW₂q⟩ := card_sup_zpowers_of_disjoint hy₁W₁ inferInstance hW₁q hy₁o hd₂
  have hW₂K₂ : zpowers y ⊔ zpowers (g₁ * y * g₁⁻¹) ≤ centralizer (K₂ : Set G) :=
    sup_le (hW₁L.trans c02) ((zpowers_le.2 hy₁K).trans c12)
  have hy₂W₂ : g₂ * y * g₂⁻¹ ∈
      centralizer ((zpowers y ⊔ zpowers (g₁ * y * g₁⁻¹) : Subgroup G) : Set G) := by
    rw [mem_centralizer_iff]
    intro w hw
    exact (mem_centralizer_iff.1 (hW₂K₂ hw) _ hy₂K).symm
  have hd₃ : (zpowers y ⊔ zpowers (g₁ * y * g₁⁻¹)) ⊓ zpowers (g₂ * y * g₂⁻¹) = ⊥ := by
    rw [eq_bot_iff, ← zpowers_inf_eq_bot_of_not_mem hq hy₂o hy₂c]
    exact fun w hw => ⟨hw.2, hW₂K₂ hw.1⟩
  obtain ⟨hW₃card, hW₃c, hW₃q⟩ := card_sup_zpowers_of_disjoint hy₂W₂ hW₂c hW₂q hy₂o hd₃
  have hcard : Nat.card (zpowers y ⊔ zpowers (g₁ * y * g₁⁻¹) ⊔
      zpowers (g₂ * y * g₂⁻¹) : Subgroup G) = q ^ 3 := by
    rw [hW₃card, hW₂card, Nat.card_zpowers, hyo]
    ring
  have hWU : zpowers y ⊔ zpowers (g₁ * y * g₁⁻¹) ⊔ zpowers (g₂ * y * g₂⁻¹) ≤
      normalizer (U : Set G) := by
    refine sup_le (sup_le (zpowers_le.2 hyU) ?_) ?_
    · exact zpowers_le.2 (hCU (le_centralizer_iff.1 c01 hy₁K))
    · exact zpowers_le.2 (hCU (le_centralizer_iff.1 c02 hy₂K))
  obtain ⟨hcop, h2⟩ := coprime_and_two_dvd_card_of_two_subgroup hU hU2 hq (by omega)
  have h3 := Classical2.le_localRank_of_normalizes hq hWU ⟨hW₃c, hW₃q⟩ hcard hcop h2
  omega

end Triple

theorem card_quotient_centralCubes_le {L : Type*} [Group L] [Finite L] {Z : Subgroup L}
    (hZ : Z ≤ center L) :
    Nat.card (Z ⧸ centralCubes hZ) ≤ 3 ^ Assembly.pRank 3 (center L) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let cube : Z →* Z :=
    MonoidHom.mk' (fun z => z ^ 3) fun a b => (commute_of_le_center hZ a b).mul_pow 3
  have hrange : cube.range = centralCubes hZ := by
    ext w
    exact ⟨fun ⟨z, hz⟩ => ⟨z, hz⟩, fun ⟨z, hz⟩ => ⟨z, hz⟩⟩
  have h1 : Nat.card Z = Nat.card (Z ⧸ centralCubes hZ) * Nat.card (centralCubes hZ) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h2 : Nat.card Z = Nat.card (Z ⧸ cube.ker) * Nat.card cube.ker :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  have h3 : Nat.card (Z ⧸ cube.ker) = Nat.card (centralCubes hZ) := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange cube).toEquiv, hrange]
  have hcard : Nat.card (Z ⧸ centralCubes hZ) = Nat.card cube.ker := by
    have hpos : 0 < Nat.card (centralCubes hZ) := Nat.card_pos
    rw [h3] at h2
    refine Nat.eq_of_mul_eq_mul_right hpos ?_
    rw [← h1, h2, mul_comm]
  have hΩcard : Nat.card (cube.ker.map Z.subtype) = Nat.card cube.ker :=
    card_map_of_injective Z.subtype_injective
  have hΩZ : cube.ker.map Z.subtype ≤ center L := (map_subtype_le _).trans hZ
  have hΩ3 : ∀ x ∈ cube.ker.map Z.subtype, x ^ 3 = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    have hz3 : z ^ 3 = 1 := MonoidHom.mem_ker.1 hz
    simpa using congrArg Subtype.val hz3
  have hΩc : IsMulCommutative (cube.ker.map Z.subtype) :=
    ⟨⟨fun a b => Subtype.ext (mem_center_iff.1 (hΩZ b.2) a)⟩⟩
  have hΩp : IsPGroup 3 (cube.ker.map Z.subtype) := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]; exact hΩ3 _ x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hΩp
  have hle := SectionRank.le_pRank (by norm_num : 1 < 3) hΩZ ⟨hΩc, hΩ3⟩ hk
  rw [hcard, ← hΩcard, hk]
  exact Nat.pow_le_pow_right (by norm_num) hle

omit [Finite G] in
theorem mem_center_iff_coe_mem_centralizer {K : Subgroup G} {x : K} :
    x ∈ center K ↔ (x : G) ∈ centralizer (K : Set G) := by
  rw [mem_center_iff, mem_centralizer_iff]
  constructor
  · intro h y hy
    exact congrArg Subtype.val (h ⟨y, hy⟩)
  · intro h y
    exact Subtype.ext (h y y.2)

omit [Finite G] in
theorem coe_mem_normalizer_map {K : Subgroup G} {U : Subgroup K} {x : K}
    (hx : x ∈ normalizer (U : Set K)) :
    (x : G) ∈ normalizer ((U.map K.subtype : Subgroup G) : Set G) :=
  le_normalizer_map K.subtype (mem_map_of_mem K.subtype hx)

structure CubeObstructionHyp (K : Subgroup G) : Prop where
  isComponent : IsComponent K
  exists_conj : ∃ g₁ g₂ : G, K ≠ K.map (MulAut.conj g₁).toMonoidHom ∧
    K ≠ K.map (MulAut.conj g₂).toMonoidHom ∧
    K.map (MulAut.conj g₁).toMonoidHom ≠ K.map (MulAut.conj g₂).toMonoidHom
  center_ne_bot : center K ≠ ⊥
  center_isPGroup : IsPGroup 3 (center K)
  localRank_three : localRank 3 G ≤ 3
  localRank_large : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2

namespace CubeObstructionHyp

variable {K : Subgroup G} (h : CubeObstructionHyp K)
include h

theorem pow_three_pow_eq_one : ∀ y ∈ K, y ∈ centralizer (K : Set G) → ∃ k : ℕ, y ^ 3 ^ k = 1 := by
  intro y hyK hyc
  have hmem : (⟨y, hyK⟩ : K) ∈ center K := mem_center_iff_coe_mem_centralizer.2 hyc
  obtain ⟨k, hk⟩ := h.center_isPGroup ⟨⟨y, hyK⟩, hmem⟩
  refine ⟨k, ?_⟩
  have := congrArg (fun w : center K => ((w : K) : G)) hk
  simpa using this

theorem exists_center_orderOf_three : ∃ z : K, z ∈ center K ∧ orderOf z = 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.center_isPGroup
  have hk0 : k ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hk
    exact h.center_ne_bot (Subgroup.card_eq_one.mp hk)
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 (by rw [hk]; exact dvd_pow_self 3 hk0)
  exact ⟨z, z.2, by rw [Subgroup.orderOf_coe, hz]⟩

theorem mem_center_of_pow_three_eq_one {U : Subgroup K} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    {x : K} (hx : x ∈ normalizer (U : Set K)) (hx3 : x ^ 3 = 1) : x ∈ center K := by
  obtain ⟨g₁, g₂, h01, h02, h12⟩ := h.exists_conj
  obtain ⟨z, hzc, hz⟩ := h.exists_center_orderOf_three
  rw [mem_center_iff_coe_mem_centralizer]
  refine mem_centralizer_of_conjugate_components h.isComponent h01 h02 h12 h.localRank_three
    z.2 (mem_center_iff_coe_mem_centralizer.1 hzc) (by rw [Subgroup.orderOf_coe, hz])
    (U := U.map K.subtype) ?_ (hU2.map _) (map_subtype_le U) x.2 (coe_mem_normalizer_map hx)
    (by rw [← Subgroup.coe_pow, hx3, Subgroup.coe_one])
  exact fun hb => hU ((map_eq_bot_iff_of_injective _ K.subtype_injective).1 hb)

theorem prime_dvd_card_normalizer {U : Subgroup K} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) {r : ℕ}
    (hr : r.Prime) (hrd : r ∣ Nat.card (normalizer (U : Set K))) : r = 2 ∨ r = 3 := by
  by_contra hne
  push Not at hne
  have hr3 : 3 < r := by
    have := hr.two_le
    omega
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrd
  obtain ⟨g₁, g₂, h01, h02, h12⟩ := h.exists_conj
  refine (orderOf_ne_of_conjugate_components h.isComponent h01 h02 h12 hr hr3
    (h.localRank_large r hr hr3) h.pow_three_pow_eq_one (U := U.map K.subtype) ?_ (hU2.map _)
    (map_subtype_le U) (y : K).2 (coe_mem_normalizer_map y.2)) ?_
  · exact fun hb => hU ((map_eq_bot_iff_of_injective _ K.subtype_injective).1 hb)
  · rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, hy]

theorem le_center_of_isElemAbelian {U : Subgroup K} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U)
    {E : Subgroup K} (hEN : E ≤ normalizer (U : Set K)) (hE : Assembly.IsElemAbelian 3 E) :
    E ≤ center K := fun x hx => h.mem_center_of_pow_three_eq_one hU hU2 (hEN hx) (hE.2 x hx)

theorem pRank_normalizer_eq {U : Subgroup K} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) :
    Assembly.pRank 3 (normalizer (U : Set K)) = Assembly.pRank 3 (center K) := by
  apply le_antisymm
  · obtain ⟨E, hEN, hE, hEcard⟩ :=
      SectionRank.exists_pRank (by norm_num : 1 < 3) (normalizer (U : Set K))
    exact SectionRank.le_pRank (by norm_num) (h.le_center_of_isElemAbelian hU hU2 hEN hE) hE
      hEcard
  · exact SectionRank.pRank_mono (by norm_num)
      ((center_le_centralizer _).trans (centralizer_le_normalizer _))

theorem exists_two_subgroup : ∃ U : Subgroup K, U ≠ ⊥ ∧ IsPGroup 2 U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hsimple, hnonab⟩ := h.isComponent.1
  have hTeven := (ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnonab).1
  have h2 : 2 ∣ Nat.card K := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center K)]
    exact Dvd.dvd.mul_right (even_iff_two_dvd.1 hTeven) _
  obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' 2 h2
  refine ⟨zpowers u, fun hb => ?_,
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hu, pow_one])⟩
  have hu1 : u = 1 := by
    have := mem_zpowers u
    rw [hb, mem_bot] at this
    exact this
  rw [hu1, orderOf_one] at hu
  exact absurd hu (by norm_num)

theorem localRank_three_eq : localRank 3 K = Assembly.pRank 3 (center K) := by
  obtain ⟨U₀, hU₀, hU₀2⟩ := h.exists_two_subgroup
  have hset : {k | ∃ H : Subgroup K, Assembly.IsTwoLocal H ∧ Assembly.pRank 3 H = k} =
      {Assembly.pRank 3 (center K)} := by
    ext k
    simp only [Set.mem_ofPred_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨H, ⟨U, hU, hU2, rfl⟩, rfl⟩
      exact h.pRank_normalizer_eq hU hU2
    · rintro rfl
      exact ⟨_, ⟨U₀, hU₀, hU₀2, rfl⟩, h.pRank_normalizer_eq hU₀ hU₀2⟩
  rw [localRank, CFSG.Open.twoLocalPrimeRank, hset, csSup_singleton]

theorem localRank_large_eq_zero {q : ℕ} (hq : q.Prime) (hq3 : 3 < q) : localRank q K = 0 := by
  have : Fact q.Prime := ⟨hq⟩
  apply Nat.eq_zero_of_le_zero
  apply csSup_le'
  rintro k ⟨H, ⟨U, hU, hU2, rfl⟩, rfl⟩
  refine SectionRank.pRank_le hq.one_lt fun E hEN hE => ?_
  have hEq : IsPGroup q E := fun x =>
    ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]; exact hE.2 _ x.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hEq
  rcases Nat.eq_zero_or_pos j with rfl | hj0
  · rw [hj]
  · exfalso
    have hdvd : q ∣ Nat.card (normalizer (U : Set K)) :=
      (dvd_pow_self q hj0.ne').trans (hj ▸ Subgroup.card_dvd_of_le hEN)
    rcases h.prime_dvd_card_normalizer hU hU2 hq hdvd with h2 | h3 <;> omega

theorem one_le_pRank_center : 1 ≤ Assembly.pRank 3 (center K) := by
  obtain ⟨z, hzc, hz⟩ := h.exists_center_orderOf_three
  exact SectionRank.le_pRank (by norm_num) (zpowers_le.2 hzc)
    ⟨inferInstance, fun w hw => hz ▸ pow_orderOf_eq_one_of_mem_zpowers hw⟩
    (by rw [Nat.card_zpowers, hz, pow_one])

theorem pRank_center_le_three : Assembly.pRank 3 (center K) ≤ 3 := by
  obtain ⟨U, hU, hU2⟩ := h.exists_two_subgroup
  obtain ⟨E, hEZ, hE, hEcard⟩ := SectionRank.exists_pRank (by norm_num : 1 < 3) (center K)
  have hE' : Assembly.IsElemAbelian 3 (E.map K.subtype) := SectionRank.isElemAbelian_map hE _
  have hE'card : Nat.card (E.map K.subtype) = 3 ^ Assembly.pRank 3 (center K) := by
    rw [card_map_of_injective K.subtype_injective, hEcard]
  have hE'U : E.map K.subtype ≤ normalizer ((U.map K.subtype : Subgroup G) : Set G) := by
    rintro _ ⟨e, he, rfl⟩
    exact centralizer_le_normalizer _
      (centralizer_le (map_subtype_le U) (mem_center_iff_coe_mem_centralizer.1 (hEZ he)))
  have hU' : U.map K.subtype ≠ ⊥ := fun hb =>
    hU ((map_eq_bot_iff_of_injective _ K.subtype_injective).1 hb)
  obtain ⟨hcop, h2⟩ := coprime_and_two_dvd_card_of_two_subgroup hU' (hU2.map _) Nat.prime_three
    (by norm_num)
  exact (Classical2.le_localRank_of_normalizes Nat.prime_three hE'U hE' hE'card hcop h2).trans
    h.localRank_three

theorem two_lift {V : Subgroup (K ⧸ center K)} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V) :
    (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map (QuotientGroup.mk' (center K)) = V ∧
      Nat.card U = Nat.card V) ∧
    (∀ U : Subgroup K, IsPGroup 2 U → U.map (QuotientGroup.mk' (center K)) = V →
      (QuotientGroup.mk' (center K)).ker ⊓ U = ⊥ ∧
      (QuotientGroup.mk' (center K)).ker ⊔ U = V.comap (QuotientGroup.mk' (center K)) ∧
      (normalizer (V : Set (K ⧸ center K))).comap (QuotientGroup.mk' (center K)) =
        normalizer (U : Set K) ∧
      ((QuotientGroup.mk' (center K)).domRestrict (normalizer (U : Set K))).ker.map
        (normalizer (U : Set K)).subtype = (QuotientGroup.mk' (center K)).ker) ∧
    ∀ r : ℕ, r.Prime → r ∣ Nat.card (normalizer (V : Set (K ⧸ center K))) → r = 2 ∨ r = 3 := by
  set π := QuotientGroup.mk' (center K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hZ : π.ker ≤ center K := (QuotientGroup.ker_mk' _).le
  have hZ3 : IsPGroup 3 π.ker := by rw [QuotientGroup.ker_mk']; exact h.center_isPGroup
  have hex := exists_unique_two_lift hπ hZ hZ3 hV2
  refine ⟨hex, fun U hU2 hUV => two_lift_structure hZ hZ3 hU2 hUV, fun r hr hrd => ?_⟩
  obtain ⟨U, ⟨hU2, hUV, -⟩, -⟩ := hex
  have hU : U ≠ ⊥ := fun hb => hV (by rw [← hUV, hb, Subgroup.map_bot])
  have hNmap : (normalizer (U : Set K)).map π = normalizer (V : Set (K ⧸ center K)) := by
    rw [← (two_lift_structure hZ hZ3 hU2 hUV).2.2.1, map_comap_eq_self_of_surjective hπ]
  have hdvd : Nat.card (normalizer (V : Set (K ⧸ center K))) ∣
      Nat.card (normalizer (U : Set K)) := by
    rw [← hNmap]
    exact Subgroup.card_dvd_of_surjective (π.subgroupMap_surjective _)
  exact h.prime_dvd_card_normalizer hU hU2 hr (hrd.trans hdvd)

theorem cube {V : Subgroup (K ⧸ center K)} (hV : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (E : Subgroup (K ⧸ center K)) [IsElementaryAbelian 3 E]
    (hEV : E ≤ normalizer (V : Set (K ⧸ center K))) :
    Function.Injective (cubeClassHom (QuotientGroup.mk'_surjective (center K))
      (QuotientGroup.ker_mk' (center K)).le E) ∧
    Nat.card E ≤ 3 ^ Assembly.pRank 3 (center K) ∧
    normalizer (E : Set (K ⧸ center K)) = centralizer (E : Set (K ⧸ center K)) := by
  set π := QuotientGroup.mk' (center K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hZ : π.ker ≤ center K := (QuotientGroup.ker_mk' _).le
  have hZ3 : IsPGroup 3 π.ker := by rw [QuotientGroup.ker_mk']; exact h.center_isPGroup
  obtain ⟨U, ⟨hU2, hUV, -⟩, -⟩ := exists_unique_two_lift hπ hZ hZ3 hV2
  have hU : U ≠ ⊥ := fun hb => hV (by rw [← hUV, hb, Subgroup.map_bot])
  have hno : ∀ x ∈ normalizer (U : Set K), x ^ 3 = 1 → x ∈ π.ker := fun x hx hx3 => by
    rw [QuotientGroup.ker_mk']
    exact h.mem_center_of_pow_three_eq_one hU hU2 hx hx3
  obtain ⟨hinj, hNC⟩ := cubeClass_injOn_and_normalizer_eq_centralizer hπ hZ hZ3 hU2 hUV hno E hEV
  have hinj' : Function.Injective (cubeClassHom hπ hZ E) := fun a b hab =>
    Subtype.ext (hinj a.2 b.2 hab)
  refine ⟨hinj', ?_, hNC⟩
  exact (Nat.card_le_card_of_injective _ hinj').trans (card_quotient_centralCubes_le hZ)

theorem no_real_element_and_no_section {V : Subgroup (K ⧸ center K)} (hV : V ≠ ⊥)
    (hV2 : IsPGroup 2 V) :
    (∀ t ∈ normalizer (V : Set (K ⧸ center K)), orderOf t = 3 → ¬ IsConj t t⁻¹) ∧
    ∀ (E : Subgroup (K ⧸ center K)) [IsElementaryAbelian 3 E],
      E ≤ normalizer (V : Set (K ⧸ center K)) → E ≠ ⊥ →
        ¬ ∃ σ : E →* K, ∀ t : E, QuotientGroup.mk' (center K) (σ t) = t := by
  set π := QuotientGroup.mk' (center K) with hπdef
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hZ : π.ker ≤ center K := (QuotientGroup.ker_mk' _).le
  have hZ3 : IsPGroup 3 π.ker := by rw [QuotientGroup.ker_mk']; exact h.center_isPGroup
  obtain ⟨U, ⟨hU2, hUV, -⟩, -⟩ := exists_unique_two_lift hπ hZ hZ3 hV2
  have hU : U ≠ ⊥ := fun hb => hV (by rw [← hUV, hb, Subgroup.map_bot])
  have hno : ∀ x ∈ normalizer (U : Set K), x ^ 3 = 1 → π x = 1 := fun x hx hx3 => by
    rw [← MonoidHom.mem_ker, QuotientGroup.ker_mk']
    exact h.mem_center_of_pow_three_eq_one hU hU2 hx hx3
  refine ⟨fun t ht hto hconj => ?_, fun E _ hEV hE ⟨σ, hσ⟩ => ?_⟩
  · have ht3 : t ^ 3 = 1 := hto ▸ pow_orderOf_eq_one t
    obtain ⟨x, hx, hx3⟩ := (cubeClass_eq_one_iff hπ hZ t ht3).1
      (cubeClass_eq_one_of_isConj_inv hπ hZ t ht3 hconj)
    have hxN := lift_mem_normalizer hZ hZ3 hU2 hUV (E := normalizer (V : Set (K ⧸ center K)))
      le_rfl (hx ▸ ht)
    rw [← hx, hno x hxN hx3, orderOf_one] at hto
    exact absurd hto (by norm_num)
  · obtain ⟨⟨t, htE⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hE
    have ht3' : t ^ 3 = 1 := elemPow_eq_one_of_isElementaryAbelian t htE
    have ht3 : (⟨t, htE⟩ : E) ^ 3 = 1 := Subtype.ext (by simpa using ht3')
    have hx3 : σ ⟨t, htE⟩ ^ 3 = 1 := by rw [← map_pow, ht3, map_one]
    have hxN := lift_mem_normalizer hZ hZ3 hU2 hUV hEV (x := σ ⟨t, htE⟩) (by rw [hσ]; exact htE)
    have h1 := hno _ hxN hx3
    rw [hσ] at h1
    exact ht1 (Subtype.ext h1)

theorem exists_automizer_three : ∃ V : Subgroup (K ⧸ center K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
    3 ∣ Nat.card (normalizer (V : Set (K ⧸ center K)) ⧸
      (centralizer (V : Set (K ⧸ center K))).subgroupOf (normalizer (V : Set (K ⧸ center K)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hsimple, hnonab⟩ := h.isComponent.1
  by_contra hcon
  push Not at hcon
  have hauto : ∀ Q : Subgroup (K ⧸ center K), IsPGroup 2 Q →
      IsPGroup 2 (normalizer (Q : Set (K ⧸ center K)) ⧸
        (centralizer (Q : Set (K ⧸ center K))).subgroupOf
          (normalizer (Q : Set (K ⧸ center K)))) := by
    intro Q hQ
    by_cases hQb : Q = ⊥
    · subst hQb
      refine IsPGroup.of_card (n := 0) ?_
      rw [pow_zero, ← index_eq_card, index_eq_one, subgroupOf_eq_top]
      exact fun g _ => mem_centralizer_iff.2 fun y hy => by
        rw [show y = 1 from mem_bot.1 hy, one_mul, mul_one]
    · refine IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne'
        fun {r} hr hrd => ?_)
      rcases (h.two_lift hQb hQ).2.2 r hr (hrd.trans (Subgroup.card_quotient_dvd_card _))
        with h2 | h3
      · exact h2
      · exact absurd (h3 ▸ hrd) (hcon Q hQb hQ)
  obtain ⟨N, hNn, hNc, k, hk⟩ :=
    (GroupTheory.frobenius_normal_p_complement (G := K ⧸ center K) 2).1.2 hauto
  have hTeven := (ComponentClassification.SimpleEvenOrder.nonabelian_simple_even hnonab).1
  have := hNn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with rfl | rfl
  · rw [index_bot] at hk
    have hp : IsPGroup 2 (K ⧸ center K) := IsPGroup.of_card hk
    have := hp.isNilpotent
    obtain ⟨a, b, hab⟩ := hnonab
    exact hab (LocalAnalysis.ComponentInitial.solvable_simple_abelian inferInstance a b)
  · rw [card_top] at hNc
    exact (Nat.not_even_iff_odd.2 (Nat.coprime_two_right.1 hNc)) hTeven

end CubeObstructionHyp

omit [Finite G] in
theorem map_conj_map_conj (H : Subgroup G) (g h : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj h).toMonoidHom =
      H.map (MulAut.conj (h * g)).toMonoidHom :=
  (RankThreeEvenClassification.Helpers.subgroup_map_conj_mul H h g).symm

omit [Finite G] in
theorem map_conj_inv_map_conj (H : Subgroup G) (g : G) :
    (H.map (MulAut.conj g).toMonoidHom).map (MulAut.conj g⁻¹).toMonoidHom = H := by
  rw [map_conj_map_conj, inv_mul_cancel]
  ext x
  simp

theorem pRank_center_eq_of_mulEquiv {A B : Type*} [Group A] [Group B] [Finite A] [Finite B]
    {p : ℕ} (hp : 1 < p) (e : A ≃* B) :
    Assembly.pRank p (center A) = Assembly.pRank p (center B) := by
  apply le_antisymm
  · have h := SectionRank.pRank_le_map hp (e : A →* B) e.injective (center A)
    rwa [map_center_eq e] at h
  · have h := SectionRank.pRank_le_map hp (e.symm : B →* A) e.symm.injective (center B)
    rwa [map_center_eq e.symm] at h

theorem cubeObstructionHyp_of_triple {L L₁ L₂ : Subgroup G} (hL : IsComponent L) {g₁ g₂ : G}
    (hL₁ : L₁ = L.map (MulAut.conj g₁).toMonoidHom) (hL₂ : L₂ = L.map (MulAut.conj g₂).toMonoidHom)
    (h01 : L ≠ L₁) (h02 : L ≠ L₂) (h12 : L₁ ≠ L₂) {K : Subgroup G}
    (hK : K ∈ ({L, L₁, L₂} : Set (Subgroup G))) (hZne : center K ≠ ⊥)
    (hZ3 : IsPGroup 3 (center K)) (hrank3 : localRank 3 G ≤ 3)
    (hrankq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2) : CubeObstructionHyp K := by
  have hcomp : ∀ g : G, IsComponent (L.map (MulAut.conj g).toMonoidHom) := fun g =>
    LocalCores.isComponent_map_mulEquiv _ hL
  rcases hK with hK | hK | hK <;> rw [hK] at hZne hZ3 ⊢
  · exact { isComponent := hL
            exists_conj := ⟨g₁, g₂, hL₁ ▸ h01, hL₂ ▸ h02, hL₁ ▸ hL₂ ▸ h12⟩
            center_ne_bot := hZne
            center_isPGroup := hZ3
            localRank_three := hrank3
            localRank_large := hrankq }
  · refine { isComponent := hL₁ ▸ hcomp g₁
             exists_conj := ⟨g₁⁻¹, g₂ * g₁⁻¹, ?_, ?_, ?_⟩
             center_ne_bot := hZne
             center_isPGroup := hZ3
             localRank_three := hrank3
             localRank_large := hrankq }
    · rw [hL₁, map_conj_inv_map_conj]
      exact fun h => h01 (hL₁ ▸ h).symm
    · rw [hL₁, map_conj_map_conj, inv_mul_cancel_right, ← hL₁, ← hL₂]
      exact h12
    · rw [hL₁, map_conj_inv_map_conj, map_conj_map_conj, inv_mul_cancel_right, ← hL₂]
      exact h02
  · refine { isComponent := hL₂ ▸ hcomp g₂
             exists_conj := ⟨g₂⁻¹, g₁ * g₂⁻¹, ?_, ?_, ?_⟩
             center_ne_bot := hZne
             center_isPGroup := hZ3
             localRank_three := hrank3
             localRank_large := hrankq }
    · rw [hL₂, map_conj_inv_map_conj]
      exact fun h => h02 (hL₂ ▸ h).symm
    · rw [hL₂, map_conj_map_conj, inv_mul_cancel_right, ← hL₁, ← hL₂]
      exact fun h => h12 h.symm
    · rw [hL₂, map_conj_inv_map_conj, map_conj_map_conj, inv_mul_cancel_right, ← hL₁]
      exact h01

theorem pRank_coe_eq_assembly_pRank {X : Type*} [Group X] [Finite X] (p : ℕ) (H : Subgroup X) :
    CFSG.pRank p H = Assembly.pRank p H :=
  (SectionRank.pRank_eq_open_pRank_top p H).trans (SectionRank.pRank_eq_pRank_top_subgroup H).symm

theorem three_component_orbit_local_central_cube_obstruction
    (hθ : aschbacherSolvableCore 3 G = ⊥) (he : twoLocalOddRank G ≤ 3)
    (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2) (h3 : pCore 3 G ≠ ⊥)
    {A : Subgroup G} (hA : IsPGroup 3 A) {L : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hLA : ¬ A ≤ normalizer (L : Set G)) :
    (∃ L₁ L₂ : Subgroup G, {K | ∃ a ∈ A, K = conjugate L a} = {L, L₁, L₂} ∧
      L ≠ L₁ ∧ L ≠ L₂ ∧ L₁ ≠ L₂ ∧ IsComponent L ∧ IsComponent L₁ ∧ IsComponent L₂) ∧
    ∀ K : Subgroup G, (∃ a ∈ A, K = conjugate L a) →
      center K ≠ ⊥ ∧ IsPGroup 3 (center K) ∧
      IsSimpleGroup (K ⧸ center K) ∧ (∃ a b : K ⧸ center K, a * b ≠ b * a) ∧
      (QuotientGroup.mk' (center K)).ker = center K ∧
      CFSG.pRank 3 (center K) = CFSG.pRank 3 (center L) ∧
      1 ≤ CFSG.pRank 3 (center L) ∧ CFSG.pRank 3 (center L) ≤ 3 ∧
      localRank 3 K = CFSG.pRank 3 (center L) ∧
      (∀ q : ℕ, q.Prime → 3 < q → localRank q K = 0) ∧
      (∀ U : Subgroup K, U ≠ ⊥ → IsPGroup 2 U →
        (∀ r : ℕ, r.Prime → r ∣ Nat.card (normalizer (U : Set K)) → r = 2 ∨ r = 3) ∧
        ∀ x ∈ normalizer (U : Set K), x ^ 3 = 1 → x ∈ center K) ∧
      (∀ V : Subgroup (K ⧸ center K), V ≠ ⊥ → IsPGroup 2 V →
        (∃! U : Subgroup K, IsPGroup 2 U ∧ U.map (QuotientGroup.mk' (center K)) = V ∧
          Nat.card U = Nat.card V) ∧
        (∀ U : Subgroup K, IsPGroup 2 U → U.map (QuotientGroup.mk' (center K)) = V →
          (QuotientGroup.mk' (center K)).ker ⊓ U = ⊥ ∧
          (QuotientGroup.mk' (center K)).ker ⊔ U = V.comap (QuotientGroup.mk' (center K)) ∧
          (normalizer (V : Set (K ⧸ center K))).comap (QuotientGroup.mk' (center K)) =
            normalizer (U : Set K) ∧
          ((QuotientGroup.mk' (center K)).domRestrict (normalizer (U : Set K))).ker.map
            (normalizer (U : Set K)).subtype = (QuotientGroup.mk' (center K)).ker) ∧
        (∀ r : ℕ, r.Prime → r ∣ Nat.card (normalizer (V : Set (K ⧸ center K))) →
          r = 2 ∨ r = 3) ∧
        (∀ (E : Subgroup (K ⧸ center K)) [IsElementaryAbelian 3 E],
          E ≤ normalizer (V : Set (K ⧸ center K)) →
          (∀ (t : E) (x : K) (hx : x ^ 3 ∈ (QuotientGroup.mk' (center K)).ker),
            QuotientGroup.mk' (center K) x = t →
            cubeClassHom (QuotientGroup.mk'_surjective (center K))
              (QuotientGroup.ker_mk' (center K)).le E t = QuotientGroup.mk ⟨x ^ 3, hx⟩) ∧
          Function.Injective (cubeClassHom (QuotientGroup.mk'_surjective (center K))
            (QuotientGroup.ker_mk' (center K)).le E) ∧
          Nat.card E ≤ 3 ^ CFSG.pRank 3 (center L) ∧
          normalizer (E : Set (K ⧸ center K)) = centralizer (E : Set (K ⧸ center K))) ∧
        (∀ t ∈ normalizer (V : Set (K ⧸ center K)), orderOf t = 3 → ¬ IsConj t t⁻¹) ∧
        ∀ (E : Subgroup (K ⧸ center K)) [IsElementaryAbelian 3 E],
          E ≤ normalizer (V : Set (K ⧸ center K)) → E ≠ ⊥ →
            ¬ ∃ σ : E →* K, ∀ t : E, QuotientGroup.mk' (center K) (σ t) = t) ∧
      ∃ V : Subgroup (K ⧸ center K), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        3 ∣ Nat.card (normalizer (V : Set (K ⧸ center K)) ⧸
          (centralizer (V : Set (K ⧸ center K))).subgroupOf
            (normalizer (V : Set (K ⧸ center K)))) := by
  obtain ⟨a₁, a₂, L₁, L₂, -, -, hL₁, hL₂, horbit, h01, h02, h12, hLc, hL₁c, hL₂c, hcent, -⟩ :=
    Theta.theta_free_three_component_orbit_central_cover_reduction hθ he hq h3 hA hL hLA
  have h3G : 3 ∣ Nat.card G := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (pCore_isPGroup (p := 3) (G := G))
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact h3 (Subgroup.card_eq_one.mp hk)
    exact (dvd_pow_self 3 hk0).trans (hk ▸ Subgroup.card_subgroup_dvd_card _)
  have hrank3 : localRank 3 G ≤ 3 :=
    (Theta.localRank_le_twoLocalOddRank Nat.prime_three (by norm_num) h3G).trans he
  have hhyp : ∀ K ∈ ({L, L₁, L₂} : Set (Subgroup G)), CubeObstructionHyp K := fun K hK =>
    cubeObstructionHyp_of_triple hLc hL₁ hL₂ h01 h02 h12 hK (hcent K hK).1 (hcent K hK).2.1
      hrank3 hq
  refine ⟨⟨L₁, L₂, horbit, h01, h02, h12, hLc, hL₁c, hL₂c⟩, fun K hK => ?_⟩
  have h := hhyp K (horbit ▸ hK)
  have hLh := hhyp L (Or.inl rfl)
  have hs : CFSG.pRank 3 (center K) = CFSG.pRank 3 (center L) := by
    obtain ⟨a, -, rfl⟩ := hK
    rw [pRank_coe_eq_assembly_pRank, pRank_coe_eq_assembly_pRank]
    exact (pRank_center_eq_of_mulEquiv (by norm_num)
      (L.equivMapOfInjective _ (MulAut.conj a⁻¹).injective)).symm
  have hsK : CFSG.pRank 3 (center K) = Assembly.pRank 3 (center K) :=
    pRank_coe_eq_assembly_pRank 3 (center K)
  obtain ⟨-, hsimple, hnonab⟩ := h.isComponent.1
  refine ⟨h.center_ne_bot, h.center_isPGroup, hsimple, hnonab, QuotientGroup.ker_mk' _, hs, ?_,
    ?_, ?_, fun q hq hq3 => h.localRank_large_eq_zero hq hq3, fun U hU hU2 =>
    ⟨fun r hr hrd => h.prime_dvd_card_normalizer hU hU2 hr hrd,
      fun x hx hx3 => h.mem_center_of_pow_three_eq_one hU hU2 hx hx3⟩,
    fun V hV hV2 => ?_, h.exists_automizer_three⟩
  · rw [pRank_coe_eq_assembly_pRank]
    exact hLh.one_le_pRank_center
  · rw [pRank_coe_eq_assembly_pRank]
    exact hLh.pRank_center_le_three
  · rw [h.localRank_three_eq, ← hsK, hs]
  · obtain ⟨hex, hstr, hprime⟩ := h.two_lift hV hV2
    obtain ⟨hreal, hsec⟩ := h.no_real_element_and_no_section hV hV2
    refine ⟨hex, hstr, hprime, fun E _ hEV => ?_, hreal, hsec⟩
    obtain ⟨hinj, hcard, hNC⟩ := h.cube hV hV2 E hEV
    refine ⟨fun t x hx hxt => ?_, hinj, by rw [← hs, hsK]; exact hcard, hNC⟩
    rw [cubeClassHom_apply, ← hxt]
    exact cubeClass_apply _ _ x hx

theorem mem_thetaComponents_of_isComponent {p : ℕ} (hp : p.Prime)
    (hθ : aschbacherSolvableCore p G = ⊥) {L : Subgroup G} (hL : IsComponent L) :
    L ∈ thetaComponents p G := by
  have hcore : aschbacherSolvableCore p L = ⊥ := by
    have h := solvable_prime_complement_core_subnormal_intersection hp hL.2
    rw [hθ, inf_bot_eq, inSubgroup] at h
    exact (map_eq_bot_iff_of_injective _ L.subtype_injective).1 h
  refine ⟨hL.1.1, hL.2, ?_⟩
  have e : (L ⧸ aschbacherSolvableCore p L) ≃* L :=
    (QuotientGroup.quotientMulEquivOfEq hcore).trans QuotientGroup.quotientBot
  exact LocalCores.isQuasisimple_of_mulEquiv e.symm hL.1

theorem normalizes_of_noncentral_three_element (hθ : aschbacherSolvableCore 3 G = ⊥)
    (he : twoLocalOddRank G ≤ 3) (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2)
    (h3 : pCore 3 G ≠ ⊥) {A : Subgroup G} (hA : IsPGroup 3 A) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G)
    (hwit : center L ≠ ⊥ → IsPGroup 3 (center L) → ∃ U : Subgroup L, U ≠ ⊥ ∧ IsPGroup 2 U ∧
      ∃ x ∈ normalizer (U : Set L), x ^ 3 = 1 ∧ x ∉ center L) :
    A ≤ normalizer (L : Set G) := by
  by_contra hLA
  obtain ⟨-, hK⟩ := three_component_orbit_local_central_cube_obstruction hθ he hq h3 hA hL hLA
  obtain ⟨hZne, hZ3, -, -, -, -, -, -, -, -, hloc, -⟩ := hK L ⟨1, A.one_mem, by
    rw [conjugate, inv_one]
    ext x
    simp⟩
  obtain ⟨U, hU, hU2, x, hxN, hx3, hxZ⟩ := hwit hZne hZ3
  exact hxZ ((hloc U hU hU2).2 x hxN hx3)

theorem ker_comp_mk'_center {L T : Type*} [Group L] [Group T] (e : L ⧸ center L ≃* T) :
    (e.toMonoidHom.comp (QuotientGroup.mk' (center L))).ker = center L := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem ne_bot_of_coe_eq_four {K : Type*} [Group K] {U : Subgroup K} {u₁ u₂ u₃ : K}
    (hU : (U : Set K) = {1, u₁, u₂, u₃}) (hu₁ : u₁ ≠ 1) : U ≠ ⊥ := by
  intro hb
  have hmem : u₁ ∈ (U : Set K) := by rw [hU]; simp
  rw [hb] at hmem
  exact hu₁ hmem

theorem normalizes_of_cover_witness (hθ : aschbacherSolvableCore 3 G = ⊥)
    (he : twoLocalOddRank G ≤ 3) (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2)
    (h3 : pCore 3 G ≠ ⊥) {A : Subgroup G} (hA : IsPGroup 3 A) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) {T : Type*} [Group T] (e : L ⧸ center L ≃* T)
    (hcov : ∀ π : L →* T, Function.Surjective π → π.ker ≤ center L → IsPGroup 3 π.ker →
      ∃ U : Subgroup L, U ≠ ⊥ ∧ IsPGroup 2 U ∧
        ∃ x ∈ normalizer (U : Set L), orderOf x = 3 ∧ x ∉ center L) :
    A ≤ normalizer (L : Set G) := by
  refine normalizes_of_noncentral_three_element hθ he hq h3 hA hL fun _ hZ3 => ?_
  have hker := ker_comp_mk'_center e
  obtain ⟨U, hU, hU2, x, hxN, hxo, hxZ⟩ :=
    hcov _ (e.surjective.comp (QuotientGroup.mk'_surjective _)) hker.le (by rw [hker]; exact hZ3)
  exact ⟨U, hU, hU2, x, hxN, hxo ▸ pow_orderOf_eq_one x, hxZ⟩

theorem normalizes_of_quotient_witness (hθ : aschbacherSolvableCore 3 G = ⊥)
    (he : twoLocalOddRank G ≤ 3) (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2)
    (h3 : pCore 3 G ≠ ⊥) {A : Subgroup G} (hA : IsPGroup 3 A) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G)
    (hwit : center L ≠ ⊥ → IsPGroup 3 (center L) →
      ∃ V : Subgroup (L ⧸ center L), V ≠ ⊥ ∧ IsPGroup 2 V ∧
        ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set (L ⧸ center L)))) ∨
          ∃ t ∈ normalizer (V : Set (L ⧸ center L)), orderOf t = 3 ∧ IsConj t t⁻¹)) :
    A ≤ normalizer (L : Set G) := by
  by_contra hLA
  obtain ⟨-, hK⟩ := three_component_orbit_local_central_cube_obstruction hθ he hq h3 hA hL hLA
  obtain ⟨hZne, hZ3, -, -, -, -, -, -, -, -, -, hV, -⟩ := hK L ⟨1, A.one_mem, by
    rw [conjugate, inv_one]
    ext x
    simp⟩
  obtain ⟨V, hVne, hV2, hr | ⟨t, htN, hto, hconj⟩⟩ := hwit hZne hZ3
  · obtain ⟨r, hr, hr3, hrd⟩ := hr
    obtain ⟨-, -, hprime, -⟩ := hV V hVne hV2
    rcases hprime r hr hrd with h2 | h3' <;> omega
  · obtain ⟨-, -, -, -, hreal, -⟩ := hV V hVne hV2
    exact hreal t htN hto hconj

theorem zpowers_ne_bot_and_isPGroup_two {S : Type*} [Group S] {z : S} (hz : orderOf z = 2) :
    zpowers z ≠ ⊥ ∧ IsPGroup 2 (zpowers z) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨fun hb => ?_, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])⟩
  have hz1 : z = 1 := by
    have := mem_zpowers z
    rw [hb, mem_bot] at this
    exact this
  rw [hz1, orderOf_one] at hz
  exact absurd hz (by norm_num)

theorem normalizes_of_center_eq_bot (hθ : aschbacherSolvableCore 3 G = ⊥)
    (he : twoLocalOddRank G ≤ 3) (hq : ∀ q : ℕ, q.Prime → 3 < q → localRank q G ≤ 2)
    (h3 : pCore 3 G ≠ ⊥) {A : Subgroup G} (hA : IsPGroup 3 A) {L : Subgroup G}
    (hL : L ∈ thetaComponents 3 G) (hZ : IsPGroup 3 (center L) → center L = ⊥) :
    A ≤ normalizer (L : Set G) := by
  by_contra hLA
  obtain ⟨-, hK⟩ := three_component_orbit_local_central_cube_obstruction hθ he hq h3 hA hL hLA
  obtain ⟨hZne, hZ3, -⟩ := hK L ⟨1, A.one_mem, by
    rw [conjugate, inv_one]
    ext x
    simp⟩
  exact hZne (hZ hZ3)

theorem quotient_witness_of_mulEquiv {S T : Type*} [Group S] [Group T] (e : S ≃* T)
    (h : ∃ V : Subgroup T, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set T))) ∨
        ∃ t ∈ normalizer (V : Set T), orderOf t = 3 ∧ IsConj t t⁻¹)) :
    ∃ V : Subgroup S, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ((∃ r : ℕ, r.Prime ∧ 3 < r ∧ r ∣ Nat.card (normalizer (V : Set S))) ∨
        ∃ t ∈ normalizer (V : Set S), orderOf t = 3 ∧ IsConj t t⁻¹) := by
  obtain ⟨V, hV, hV2, hw⟩ := h
  have hN : normalizer ((V.map e.symm.toMonoidHom : Subgroup S) : Set S) =
      (normalizer (V : Set T)).map e.symm.toMonoidHom := (map_equiv_normalizer_eq V e.symm).symm
  refine ⟨V.map e.symm.toMonoidHom, fun hb =>
    hV ((map_eq_bot_iff_of_injective _ e.symm.injective).1 hb), hV2.map _, ?_⟩
  rcases hw with ⟨r, hr, hr3, hrd⟩ | ⟨t, htN, hto, hconj⟩
  · refine Or.inl ⟨r, hr, hr3, ?_⟩
    rw [hN, card_map_of_injective e.symm.injective]
    exact hrd
  · refine Or.inr ⟨e.symm t, ?_, ?_, ?_⟩
    · rw [hN]
      exact mem_map_of_mem _ htN
    · rw [MulEquiv.orderOf_eq]
      exact hto
    · obtain ⟨c, hc⟩ := isConj_iff.1 hconj
      refine isConj_iff.2 ⟨e.symm c, ?_⟩
      rw [← map_mul, ← map_inv, ← map_mul, hc, map_inv]

end CFSG.RankThree
