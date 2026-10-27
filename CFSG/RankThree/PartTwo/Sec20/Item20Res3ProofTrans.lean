module

public import CFSG.RankThree.PartTwo.Sec20.Item203OneProof
import CFSG.RankThree.PartTwo.Sec3.ElemNineAut
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.CentralCover.FourGroupWitness

public section

namespace CFSG.RankThree.PartTwo.Sec20.Res3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec20
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_conj_mem_of_isSylowOf {p : ℕ} [Fact p.Prime] {T M S : Subgroup G}
    (hT : CFSG.ABGLocalTools.IsSylowOf p T M) (hSM : S ≤ M) (hS : IsPGroup p S) :
    ∃ m ∈ M, ∀ s ∈ S, m * s * m⁻¹ ∈ T := by
  obtain ⟨Q, hQ⟩ := (hS.comap_subtype (K := M)).exists_le_sylow
  obtain ⟨m, hmM, hm⟩ := Sec18.exists_map_conj_eq_of_isSylowOf
    (⟨Q, rfl⟩ : CFSG.ABGLocalTools.IsSylowOf p ((Q : Subgroup M).map M.subtype) M) hT
  refine ⟨m, hmM, fun s hs => ?_⟩
  rw [hm]
  exact ⟨s, ⟨⟨s, hSM hs⟩, hQ hs, rfl⟩, rfl⟩

theorem exists_isPGroup_of_le_autIn {p : ℕ} [Fact p.Prime] {H B : Subgroup G}
    {Q : Subgroup (MulAut B)} (hQ : Q ≤ Sec4.autIn H B) (hQp : IsPGroup p Q) :
    ∃ S : Subgroup G, S ≤ H ⊓ Subgroup.normalizer (B : Set G) ∧ IsPGroup p S ∧
      ∀ σ ∈ Q, ∃ s ∈ S, ∃ hs : s ∈ Subgroup.normalizer (B : Set G),
        B.normalizerMonoidHom ⟨s, hs⟩ = σ := by
  set NB := H ⊓ Subgroup.normalizer (B : Set G) with hNB
  let Φ : NB →* MulAut B :=
    B.normalizerMonoidHom.comp (Subgroup.inclusion (inf_le_right : NB ≤ _))
  set P := Q.comap Φ with hP
  let f : P →* Q := (Φ.comp P.subtype).codRestrict Q fun x => x.2
  have hf : Function.Surjective f := by
    rintro ⟨σ, hσ⟩
    obtain ⟨h, hN, hH, rfl⟩ := Sec4.mem_autIn_iff.mp (hQ hσ)
    exact ⟨⟨⟨h, hH, hN⟩, hσ⟩, rfl⟩
  obtain ⟨S₀⟩ := (inferInstance : Nonempty (Sylow p P))
  have htop : (S₀ : Subgroup P).map f = ⊤ := by
    rw [← Sylow.coe_mapSurjective hf]
    exact ((S₀.mapSurjective hf).is_maximal' (hQp.to_subgroup ⊤) le_top).symm
  refine ⟨(S₀ : Subgroup P).map (NB.subtype.comp P.subtype), ?_, S₀.isPGroup'.map _, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact (x : NB).2
  · intro σ hσ
    have hmem : (⟨σ, hσ⟩ : Q) ∈ (S₀ : Subgroup P).map f := htop ▸ Subgroup.mem_top _
    obtain ⟨x, hx, hxσ⟩ := hmem
    exact ⟨((x : NB) : G), ⟨x, hx, rfl⟩, (x : NB).2.2, congrArg Subtype.val hxσ⟩

theorem exists_conj_le_of_isPGroup_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T)
    (hBn : M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G))
    (h9 : Nat.card (A ⊓ L : Subgroup G) = 9) {S : Subgroup G} (hSM : S ≤ M)
    (hS2 : IsPGroup 2 S) :
    ∃ n ∈ M, n ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
      ∀ s ∈ S, n * s * n⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := A ⊓ L with hB
  set P := CFSG.Open.pCoreOf 2 M with hP
  have hMR : M ≤ Subgroup.normalizer ((B ⊔ P : Subgroup G) : Set G) := hBn
  have hBM : B ≤ M := inf_le_left.trans (le_of_hyp201 hT.toHyp201)
  have hPT : P ≤ T := pCoreOf_le_of_isSylowOf hT.sylow
  have hPM : P ≤ M := CFSG.LieType.BorelTits.pCoreOf_le 2 M
  have hMP : M ≤ Subgroup.normalizer (P : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [h9]; norm_num)
  have hP2 : IsPGroup 2 P := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M
  have hdisj : P ⊓ B = ⊥ := Subgroup.eq_bot_of_card_eq _ (by
    rw [inf_comm]
    exact card_inf_eq_one_of_isPGroup hB3 hP2)
  have hcard : Nat.card (B ⊔ P : Subgroup G) = 2 ^ (Nat.card P).factorization 2 * 9 := by
    obtain ⟨k, hk⟩ := hP2.exists_card_eq
    rw [sup_comm, CFSG.RankThree.CentralCover.card_sup_eq_mul_of_le_normalizer
      (hBM.trans hMP) hdisj, h9, hk, Nat.Prime.factorization_pow Nat.prime_two,
      Finsupp.single_eq_same]
  have hfact : (Nat.card (B ⊔ P : Subgroup G)).factorization 3 = 2 := by
    rw [hcard, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd fun h =>
        absurd (Nat.prime_three.dvd_of_dvd_pow h) (by norm_num),
      show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, zero_add]
  have hBsyl : CFSG.ABGLocalTools.IsSylowOf 3 B (B ⊔ P) :=
    CFSG.ABGLocalTools.isSylowOf_of_card le_sup_left (by rw [h9, hfact]; norm_num)
  obtain ⟨m, hmM, hm⟩ := exists_conj_mem_of_isSylowOf hT.sylow hSM hS2
  set B₁ := B.map (MulAut.conj m).toMonoidHom with hB₁
  have hB₁R : B₁ ≤ B ⊔ P := by
    rintro _ ⟨b, hb, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp (hMR hmM) b).mp (le_sup_left (a := B) hb)
  have hB₁card : Nat.card B₁ = 9 := by
    rw [hB₁, Subgroup.card_map_of_injective (MulAut.conj m).injective, h9]
  have hB₁syl : CFSG.ABGLocalTools.IsSylowOf 3 B₁ (B ⊔ P) :=
    CFSG.ABGLocalTools.isSylowOf_of_card hB₁R (by rw [hB₁card, hfact]; norm_num)
  obtain ⟨r, hrR, hr⟩ := Sec18.exists_map_conj_eq_of_isSylowOf hB₁syl hBsyl
  have hr' : r ∈ (B : Set G) * (P : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B P (hBM.trans hMP)]
    exact hrR
  obtain ⟨b, hb, p, hp, rfl⟩ := hr'
  refine ⟨p * m, M.mul_mem (hPM hp) hmM, ?_, fun s hs => ?_⟩
  · have hle : B.map (MulAut.conj (p * m)).toMonoidHom ≤ B := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : b * p * (m * x * m⁻¹) * (b * p)⁻¹ ∈ B := by
        rw [hr]
        exact ⟨m * x * m⁻¹, ⟨x, hx, rfl⟩, rfl⟩
      have h2 : (MulAut.conj (p * m)).toMonoidHom x =
          b⁻¹ * (b * p * (m * x * m⁻¹) * (b * p)⁻¹) * b := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      rw [h2]
      exact B.mul_mem (B.mul_mem (B.inv_mem hb) h1) hb
    have heq : B.map (MulAut.conj (p * m)).toMonoidHom = B :=
      Subgroup.eq_of_le_of_card_ge hle
        (by rw [Subgroup.card_map_of_injective (MulAut.conj (p * m)).injective])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  · have h1 := hm s hs
    have h2 : p * m * s * (p * m)⁻¹ = p * (m * s * m⁻¹) * p⁻¹ := by group
    rw [h2]
    exact T.mul_mem (T.mul_mem (hPT hp) h1) (T.inv_mem (hPT hp))

theorem exists_conj_eq_core {A M L N : Subgroup G} {c : G} {T : Subgroup G}
    (hT : Ctx20 G A M L N c T) (h9 : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hQ : ∃ Q : Subgroup (MulAut ↥(A ⊓ L)), Q ≤ Sec4.autIn M (A ⊓ L) ∧
      Nonempty (↥Q ≃* QuaternionGroup 2))
    (hBn : M ≤ Subgroup.normalizer (((A ⊓ L) ⊔ CFSG.Open.pCoreOf 2 M : Subgroup G) : Set G))
    {d d' : G} (hd : d ∈ A ⊓ L) (hd' : d' ∈ A ⊓ L) (hd1 : d ≠ 1) (hd'1 : d' ≠ 1) :
    ∃ t ∈ T, t ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧ t * d * t⁻¹ = d' := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ, ⟨e⟩⟩ := hQ
  have hQ2 : IsPGroup 2 Q := IsPGroup.of_card (n := 3) (by
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
    norm_num)
  obtain ⟨S, hSMB, hS2, hSQ⟩ := exists_isPGroup_of_le_autIn hQ hQ2
  obtain ⟨n, -, hnB, hnT⟩ :=
    exists_conj_le_of_isPGroup_core hT hBn h9 (hSMB.trans inf_le_left) hS2
  have hAE := hT.mem_partTwoE.1
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAE.1.is_comm.comm (⟨a, ha⟩ : A) ⟨b, hb⟩)
  let _ : CommGroup ↥(A ⊓ L) :=
    { (inferInstance : Group ↥(A ⊓ L)) with
      mul_comm := fun x y => Subtype.ext (hAc _ x.2.1 _ y.2.1) }
  have h3 : ∀ x : ↥(A ⊓ L), x ^ 3 = 1 := fun x =>
    Subtype.ext (by rw [Subgroup.coe_pow]; exact hAE.2 _ x.2.1)
  have hconj : ∀ y ∈ A ⊓ L, n⁻¹ * y * n ∈ A ⊓ L := fun y hy => by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hnB) y).mp hy
    rwa [inv_inv] at this
  have hne : ∀ y : G, y ≠ 1 → n⁻¹ * y * n ≠ 1 := fun y hy h2 => hy (by
    calc y = n * (n⁻¹ * y * n) * n⁻¹ := by group
      _ = 1 := by rw [h2]; group)
  have hx1 : (⟨n⁻¹ * d * n, hconj d hd⟩ : ↥(A ⊓ L)) ≠ 1 := fun h1 =>
    hne d hd1 (congrArg Subtype.val h1)
  have hy1 : (⟨n⁻¹ * d' * n, hconj d' hd'⟩ : ↥(A ⊓ L)) ≠ 1 := fun h1 =>
    hne d' hd'1 (congrArg Subtype.val h1)
  obtain ⟨σ, hσQ, hσ⟩ := Sec3.exists_apply_eq_of_quaternion h3 h9 e hx1 hy1
  obtain ⟨s, hsS, hsN, rfl⟩ := hSQ σ hσQ
  refine ⟨n * s * n⁻¹, hnT s hsS, mul_mem (mul_mem hnB hsN) (inv_mem hnB), ?_⟩
  have h1 := congrArg Subtype.val hσ
  rw [Sec4.normalizerMonoidHom_apply_coe] at h1
  calc n * s * n⁻¹ * d * (n * s * n⁻¹)⁻¹ = n * (s * (n⁻¹ * d * n) * s⁻¹) * n⁻¹ := by group
    _ = d' := by
      rw [show (s * (n⁻¹ * d * n) * s⁻¹ : G) = n⁻¹ * d' * n from h1]
      group

section Q8

theorem exists_quaternion_le_autIn (h1812 : Sec18.Item181_2) (h184 : Sec18.Item184_1)
    {A M L N : Subgroup G} {c : G} (h : Hyp201One G A M L N c) :
    ∃ Q : Subgroup (MulAut ↥(A ⊓ L)), Q ≤ Sec4.autIn M (A ⊓ L) ∧
      Nonempty (↥Q ≃* QuaternionGroup 2) := by
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set Bb := ((A ⊓ L).subgroupOf L).map π with hBb
  obtain ⟨e⟩ := nonempty_quotient_of_hyp201One h184 h
  set e' := e.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with he'
  have hBb' : Nat.card (Bb.map e'.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective,
      card_map_inf_of_hyp201One h1812 h184 h]
  obtain ⟨q⟩ := KFacts.L34.nonempty_automizer_of_card_eq_nine
    KFacts.L34.card_galoisField_two_two hBb'
  let qB : Sec4.autIn ⊤ Bb ≃* QuaternionGroup 2 :=
    (KFacts.L34.automizerEquivAutIn Bb).symm.trans
      ((CFSG.RankThree.Asc83Table.automizerCongr e' Bb).trans q)
  set κ := MulAut.congr (quotientRestrictEquiv inf_le_right
    (injective_mk_of_hyp201One h1812 h184 h)).symm with hκ
  refine ⟨(Sec4.autIn ⊤ Bb).map κ.toMonoidHom, map_autIn_le_of_hyp201One h1812 h184 h, ⟨?_⟩⟩
  exact ((Sec4.autIn ⊤ Bb).equivMapOfInjective κ.toMonoidHom κ.injective).symm.trans qB

end Q8

end CFSG.RankThree.PartTwo.Sec20.Res3
