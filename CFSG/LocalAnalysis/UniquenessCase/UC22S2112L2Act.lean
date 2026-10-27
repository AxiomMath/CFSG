module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b
import CFSG.Milestones.ASVolI.A3OddFacts
import CFSG.Quasithin.Vol2.GoldschmidtF134OddDickson
import CFSG.GroupTheory.CenterlessInnerCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112_rhoL_eq_one {L S B : Subgroup G}
    (hS : CFSG.QuasithinUnique.IsSylowTwoOf S L) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hLp : IsL2Odd (Bar2 L) p) (hBN : B ≤ normalizer (L : Set G))
    (hBS : B ≤ normalizer (S : Set G)) (hBab : IsMulCommutative ↥B)
    (hBodd : Odd (Nat.card ↥B)) {x : G} (hx : x ∈ B) (hx3 : (orderOf x).Coprime 3) :
    UC6S846.rhoL L ⟨x, hBN hx⟩ = 1 := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨e⟩ := CFSG.Quasithin.H13.NQCore.nonempty_mulEquiv_psl2_odd
    (CFSG.Blueprint.LieModel.statedClassicalModel hLp (by decide))
  let φ : ↥(normalizer (L : Set G)) →*
      MulAut (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1)) :=
    (MulAut.congr e).toMonoidHom.comp (UC6S846.rhoL L)
  have hφ : ∀ (n : ↥(normalizer (L : Set G))) (z : Bar2 L),
      φ n (e z) = e (UC6S846.rhoL L n z) := by
    intro n z
    show e (UC6S846.rhoL L n (e.symm (e z))) = e (UC6S846.rhoL L n z)
    rw [MulEquiv.symm_apply_apply]
  let BN : Subgroup ↥(normalizer (L : Set G)) := B.subgroupOf (normalizer (L : Set G))
  let B'' := BN.map φ
  have hcardBN : Nat.card ↥BN = Nat.card ↥B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBN).toEquiv
  have hB''odd : Odd (Nat.card ↥B'') :=
    Odd.of_dvd_nat hBodd ((Subgroup.card_map_dvd BN φ).trans (dvd_of_eq hcardBN))
  have hodd_elt : ∀ y ∈ B'', Odd (orderOf y) := by
    intro y hy
    refine Odd.of_dvd_nat hB''odd ?_
    rw [← Subgroup.orderOf_mk y hy]
    exact orderOf_dvd_natCard _
  have hq : Nat.card (GaloisField p 1) = p ^ 1 := GaloisField.card p 1 one_ne_zero
  have hinner : B'' ≤ (MulAut.conj :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1) →* _).range := by
    intro y hy
    obtain ⟨z, hz⟩ :=
      CFSG.ASVolI.burnsideA315x_psl2_odd_inner hp hq (Or.inl rfl) y (hodd_elt y hy)
    exact MonoidHom.mem_range.2 ⟨z, hz.symm⟩
  have hinj : Function.Injective (MulAut.conj :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1) →* _) :=
    CFSG.mulAutConj_injective_of_center_eq_bot (CFSG.GorensteinWalter.psl2_center_eq_bot _)
  let B' := B''.comap (MulAut.conj :
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1) →* _)
  have hmap : B'.map MulAut.conj = B'' := Subgroup.map_comap_eq_self hinner
  have hcardB' : Nat.card ↥B' = Nat.card ↥B'' :=
    (Nat.card_congr (B'.equivMapOfInjective _ hinj).toEquiv).trans (by rw [hmap])
  have hB'odd : Odd (Nat.card ↥B') := hcardB' ▸ hB''odd
  have hB''comm : ∀ a ∈ B'', ∀ b ∈ B'', a * b = b * a := by
    intro a ha b hb
    obtain ⟨n₁, hn₁, rfl⟩ := Subgroup.mem_map.1 ha
    obtain ⟨n₂, hn₂, rfl⟩ := Subgroup.mem_map.1 hb
    rw [← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have h := hBab.is_comm.comm (⟨n₁, Subgroup.mem_subgroupOf.1 hn₁⟩ : ↥B)
      ⟨n₂, Subgroup.mem_subgroupOf.1 hn₂⟩
    simpa using congrArg Subtype.val h
  have hB'ab : IsMulCommutative ↥B' := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    apply hinj
    simp only [Subgroup.coe_mul, map_mul]
    exact hB''comm _ a.2 _ b.2
  let f : ↥L →* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField p 1) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  have hf : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let S' := (S.subgroupOf L).map f
  have hS' : CFSG.QuasithinUnique.IsSylowTwoOf S' ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map f hf (CFSG.Quasithin.isSylowTwoOf_top_subgroupOf hS)
  have hconj : ∀ y ∈ B', ∀ s' ∈ S', y * s' * y⁻¹ ∈ S' := by
    intro y hy s' hs'
    obtain ⟨n, hn, hny⟩ := Subgroup.mem_map.1 (show MulAut.conj y ∈ B'' from hy)
    obtain ⟨s₀, hs₀, rfl⟩ := Subgroup.mem_map.1 hs'
    have h1 : y * f s₀ * y⁻¹ = φ n (f s₀) := by
      rw [hny, MulAut.conj_apply]
    rw [h1]
    change φ n (e (QuotientGroup.mk s₀)) ∈ S'
    rw [hφ, UC6S846.rhoL_mk]
    refine Subgroup.mem_map.2 ⟨Subgroup.normalizerMonoidHom L n s₀, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf, UC6S846.rhoL_mk_coe]
    exact (Subgroup.mem_normalizer_iff.1 (hBS (Subgroup.mem_subgroupOf.1 hn)) _).1
      (Subgroup.mem_subgroupOf.1 hs₀)
  have hB'S' : B' ≤ normalizer (S' : Set _) := by
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro s'
    refine ⟨hconj y hy s', fun hs' => ?_⟩
    have h := hconj y⁻¹ (B'.inv_mem hy) _ hs'
    simpa [mul_assoc] using h
  have h3 : IsPGroup 3 ↥B' := by
    by_contra hn3
    have hc : CFSG.ASVolI.burnsideA315x_Config _ S' B' :=
      ⟨hS', hB'odd, hn3, Or.inl hB'ab,
        Subgroup.set_mul_normalizer_comm (B' : Set _) S' (fun y hy => hB'S' hy)⟩
    obtain ⟨-, -, s, hs, hinv⟩ := CFSG.ASVolI.burnsideA315x_l2_core hp2 le_rfl hc
    have hSB : S' ⊓ B' = ⊥ := by
      obtain ⟨k, hk⟩ := hS'.2.1.exists_card_eq
      refine Subgroup.inf_eq_bot_of_coprime ?_
      rw [hk]
      exact (Nat.coprime_two_left.2 hB'odd).pow_left k
    have hbot : B' = ⊥ := by
      rw [eq_bot_iff]
      intro y hy
      rw [Subgroup.mem_bot]
      have hyS : y * s⁻¹ * y⁻¹ ∈ S' :=
        (Subgroup.mem_normalizer_iff.1 (hB'S' hy) _).1 (S'.inv_mem hs)
      have h2 : y⁻¹ * y⁻¹ ∈ S' := by
        have h5 := S'.mul_mem hs hyS
        rwa [show s * (y * s⁻¹ * y⁻¹) = s * y * s⁻¹ * y⁻¹ by group, hinv y hy] at h5
      have h4 : y⁻¹ * y⁻¹ = 1 := by
        have h6 : y⁻¹ * y⁻¹ ∈ S' ⊓ B' :=
          Subgroup.mem_inf.2 ⟨h2, B'.mul_mem (B'.inv_mem hy) (B'.inv_mem hy)⟩
        rw [hSB] at h6
        exact Subgroup.mem_bot.1 h6
      have hy2 : y ^ 2 = 1 := by
        have h7 : (y ^ 2)⁻¹ = 1 := by
          rw [sq, mul_inv_rev]
          exact h4
        exact inv_eq_one.1 h7
      have hyodd : Odd (orderOf y) := by
        refine Odd.of_dvd_nat hB'odd ?_
        rw [← Subgroup.orderOf_mk y hy]
        exact orderOf_dvd_natCard _
      rcases (Nat.dvd_prime Nat.prime_two).1 (orderOf_dvd_of_pow_eq_one hy2) with h | h
      · exact orderOf_eq_one_iff.1 h
      · rw [h] at hyodd
        exact absurd hyodd (Nat.not_odd_iff_even.2 even_two)
    exact hn3 (hbot ▸ IsPGroup.of_bot)
  have hxB'' : φ ⟨x, hBN hx⟩ ∈ B'' := Subgroup.mem_map_of_mem φ (Subgroup.mem_subgroupOf.2 hx)
  obtain ⟨y, hy⟩ := MonoidHom.mem_range.1 (hinner hxB'')
  have hyB' : y ∈ B' := show MulAut.conj y ∈ B'' from hy ▸ hxB''
  have hyord : orderOf y ∣ orderOf x := by
    rw [← orderOf_injective _ hinj y, hy]
    refine (orderOf_map_dvd φ _).trans ?_
    rw [Subgroup.orderOf_mk]
  obtain ⟨k, hk⟩ := h3 ⟨y, hyB'⟩
  have hyk : y ^ 3 ^ k = 1 := by
    have h8 := congrArg Subtype.val hk
    simpa using h8
  have hy1 : orderOf y = 1 :=
    Nat.Coprime.eq_one_of_dvd ((Nat.Coprime.coprime_dvd_left hyord hx3).pow_right k)
      (orderOf_dvd_of_pow_eq_one hyk)
  have hφ1 : φ ⟨x, hBN hx⟩ = 1 := by
    rw [← hy, orderOf_eq_one_iff.1 hy1, map_one]
  exact (MulEquiv.map_eq_one_iff (MulAut.congr e)).1 hφ1

end CFSG.LocalAnalysis.UniquenessCase.UC22
