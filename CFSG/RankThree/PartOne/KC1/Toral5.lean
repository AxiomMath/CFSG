module

public import CFSG.RankThree.PartOne.KC1.PairData
public import CFSG.RankThree.PartOne.KC1.SylowConj
public import CFSG.RankThree.PartOne.KE8F.Toral5
public import CFSG.RankThree.PartOne.KE8F.E8Arith5

public noncomputable section

namespace CFSG.RankThree.PartOne.KC1

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KE8F
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Frame

theorem exists_frame_wr (K : Type) [Field K] [Finite K] [CharP K 2] {f : ℕ} (hf : 1 ≤ f)
    (hK : Nat.card K = 2 ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    [CharP L 2] : ∃ F : E8P4Frame0 K L 2 f, F.n = wr L e8P4WW := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  have hFr' : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact hFr' c
  set n : ModGL .E8 L := wr L e8P4WW with hn
  have hnm : n ∈ monomialSubgroup .E8 L := wr_mem_monomial _
  have hnW : weylQuotientHom .E8 L ⟨n, hnm⟩ = (coxeterSystem .E8).wordProd e8P4WW :=
    wr_weylImage _
  have hnC : n ∈ adjointGroup .E8 L := monomialSubgroup_le_adjointGroup' hnm
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_gen .E8 K hf L n hnC
  refine ⟨⟨n, hnm, hnW, g0, hg0C, hg0, fun P hP hPC hPF hPperf => ?_,
    e8P4_twistedTorus hnm hnW⟩, rfl⟩
  have := (finite_fixed_subgroup_rational_perfect (K := K) (L := L) 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr P hPC hPF).2.2 P le_rfl hPperf
  rwa [adjEmb_range]

theorem fixed_finite_le_range {K : Type} [Field K] [Finite K] {L : Type} [Field L] [Algebra K L]
    [Algebra.IsAlgebraic K L] (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (X : Subgroup (ModGL .E8 L)) [Finite X]
    (hXC : X ≤ adjointGroup .E8 L) (hXF : ∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) :
    X ≤ (adjEmb .E8 K L).range := by
  have h := (finite_fixed_subgroup_rational_perfect (K := K) (L := L) 1
    (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1
  rw [adjEmb_range]
  exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1 h)

end Frame

section Count

theorem card_comap_of_le_range {G H : Type*} [Group G] [Group H] (ι : G →* H)
    (hι : Function.Injective ι) (X : Subgroup H) (hX : X ≤ ι.range) :
    Nat.card (X.comap ι) = Nat.card X := by
  have h1 : (X.comap ι).map ι = X := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 hX
  rw [← Subgroup.card_map_of_injective hι, h1]

theorem card_range_of_injective' {G H : Type*} [Group G] [Group H] (f : G →* H)
    (hf : Function.Injective f) : Nat.card f.range = Nat.card G :=
  Nat.card_congr (MonoidHom.ofInjective hf).toEquiv.symm

theorem factorization_eq_of_card {q : ℕ} (C N : ℕ)
    (hC : ordProj[5] C = 5 * ordProj[5] ((q * q + 1) ^ 4)) (hN : N = (q * q + 1) ^ 4 * 5) :
    N.factorization 5 = C.factorization 5 := by
  have h0 : (q * q + 1) ^ 4 ≠ 0 := by positivity
  have h2 : ordProj[5] N = ordProj[5] ((q * q + 1) ^ 4) * 5 := by
    rw [hN, Nat.ordProj_mul 5 h0 (by norm_num)]
    have : ordProj[5] 5 = 5 := by
      simpa using Nat.ordProj_self_pow (p := 5) (k := 1) Nat.prime_five
    rw [this]
  have h3 : 5 ^ N.factorization 5 = 5 ^ C.factorization 5 := by
    show ordProj[5] N = ordProj[5] C
    rw [h2, hC, mul_comm]
  exact Nat.pow_right_injective (by norm_num) h3

end Count

section Main

theorem e8FiveToral_of_datum {K L : Type} [Field K] [Finite K] [CharP K 2] [Field L] [Algebra K L]
    [IsAlgClosure K L] [CharP L 2] {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = 2 ^ f)
    (h5 : 5 ∣ Nat.card K * Nat.card K + 1) (D : PairDatum e8P4WW)
    (hD : Nat.card K % 5 = D.c) (F : E8P4Frame0 K L 2 f) (hFn : F.n = wr L e8P4WW) :
    E8FiveToral F := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hLac : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L 2 f with hFrdef
  have hFr' : ∀ c, Fr c = c ^ (2 ^ f) := fun c => iterateFrobenius_def 2 f c
  set q : ℕ := Nat.card K with hqdef
  have hFr : ∀ c, Fr c = c ^ q := fun c => by
    rw [hK]
    exact hFr' c
  set Q : ℕ := q * q with hQdef
  have hFr₂ : ∀ c, (Fr.comp Fr) c = c ^ Q := fun c => by
    rw [RingHom.comp_apply, hFr, hFr, ← pow_mul]
  have hq2 : 2 ≤ q := Finite.one_lt_card
  have hQ2 : 2 ≤ Q := by nlinarith
  have h2q : 2 ∣ q := by
    rw [hK]
    exact dvd_pow_self 2 (by omega)
  have hQodd : ¬ 2 ∣ Q + 1 := by
    intro h
    have h2Q : 2 ∣ Q := Dvd.dvd.mul_right h2q q
    have := (Nat.dvd_add_right h2Q).1 h
    omega
  have h5Q : 5 ∣ Q + 1 := h5
  obtain ⟨ζ, hζ⟩ := exists_primitiveRoot_five (L := L)
  have : Finite (Mon L Q) := finite_Mon hQodd
  have : Finite (U (Fr.comp Fr)) := finite_U hFr₂ hQ2
  set g0 : ModGL .E8 L := F.g0 with hg0
  set ε : Mon L Q →* ModGL .E8 L := (eHom Fr D).comp monHom with hε
  have hε_inj : Function.Injective ε := by
    rw [injective_iff_map_eq_one]
    intro z hz
    have h1 : monHom z = 1 := eHom_ker_trivial D Fr hFr hD hz
    exact monHom_injective (by rw [h1, map_one])
  set εc : Mon L Q →* ModGL .E8 L := (MulAut.conj g0).toMonoidHom.comp ε with hεc
  have hεc_inj : Function.Injective εc := (MulAut.conj g0).injective.comp hε_inj
  have hεc_apply : ∀ z, εc z = g0 * eHom Fr D (monHom z) * g0⁻¹ := fun z => by
    simp [hεc, hε, MulAut.conj_apply]
  set ηU : U (Fr.comp Fr) →* ModGL .E8 L :=
    ((MulAut.conj g0).toMonoidHom.comp (eHom Fr D)).comp (U (Fr.comp Fr)).subtype with hηU
  have hηU_apply : ∀ A : U (Fr.comp Fr), ηU A = g0 * eHom Fr D (A : SL5 L) * g0⁻¹ := fun A => by
    simp [hηU, MulAut.conj_apply]
  set Y : Subgroup (ModGL .E8 L) := ηU.range with hY
  have : Finite Y := Finite.of_surjective ηU.rangeRestrict ηU.rangeRestrict_surjective
  have hΦg : Units.map (entrywiseHom Fr) g0 = g0 * wr L e8P4WW := by
    rw [← hFn]
    exact F.hg0
  have hYC : Y ≤ adjointGroup .E8 L := by
    rintro _ ⟨A, rfl⟩
    rw [hηU_apply]
    exact mul_mem (mul_mem F.hg0C (eHom_mem_adjoint Fr D _)) (inv_mem F.hg0C)
  have hYF : ∀ x ∈ Y, Units.map (entrywiseHom Fr) x = x := by
    rintro _ ⟨A, rfl⟩
    rw [hηU_apply, map_mul, map_mul, map_inv, hΦg]
    have hA := eHom_fixed Fr D A.2
    calc g0 * wr L e8P4WW * Units.map (entrywiseHom Fr) (eHom Fr D (A : SL5 L)) *
          (g0 * wr L e8P4WW)⁻¹
        = g0 * (wr L e8P4WW * Units.map (entrywiseHom Fr) (eHom Fr D (A : SL5 L)) *
          (wr L e8P4WW)⁻¹) * g0⁻¹ := by group
      _ = g0 * eHom Fr D (A : SL5 L) * g0⁻¹ := by rw [hA]
  have hYle : Y ≤ (adjEmb .E8 K L).range := fixed_finite_le_range Fr hFr Y hYC hYF
  have hι_inj : Function.Injective (adjEmb .E8 K L) := adjEmb_injective
  set G₁ : Subgroup (adjointGroup .E8 K) := (εc.range).comap (adjEmb .E8 K L) with hG₁
  have hεc_le : εc.range ≤ Y := by
    rintro _ ⟨z, rfl⟩
    refine ⟨⟨monHom z, monHom_mem_U hFr₂ z⟩, ?_⟩
    rw [hηU_apply, hεc_apply]
  have hG₁card : Nat.card G₁ = Nat.card (Mon L Q) := by
    rw [hG₁, card_comap_of_le_range _ hι_inj _ (hεc_le.trans hYle),
      card_range_of_injective' εc hεc_inj]
  have hcard5 : (Nat.card G₁).factorization 5 =
      (Nat.card (adjointGroup .E8 K)).factorization 5 := by
    rw [hG₁card, card_Mon_eq hQodd]
    exact factorization_eq_of_card _ _ (e8P4_ordProj_five h5) rfl
  intro x hx
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hxP : IsPGroup 5 (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx, pow_one])
  obtain ⟨c, hc⟩ := exists_conj_mem_of_factorization_eq 5 G₁ hcard5 hxP
  obtain ⟨z, hz⟩ : adjEmb .E8 K L (c * x * c⁻¹) ∈ εc.range := hc
  have hy5 : (c * x * c⁻¹) ^ 5 = 1 := by
    rw [conj_pow, ← hx, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
  have hz5 : z ^ 5 = 1 := by
    apply hεc_inj
    rw [map_pow, hz, map_one, ← map_pow, hy5, map_one]
  have hz5' : monHom z ^ 5 = 1 := by rw [← map_pow, hz5, map_one]
  obtain ⟨u, hu, hud⟩ := exists_conj_into_Dgrp hFr₂ hζ h5Q z hz5'
  have hdU : u * monHom z * u⁻¹ ∈ U (Fr.comp Fr) := Dgrp_le_U hFr₂ hud
  have hTor : eHom Fr D (u * monHom z * u⁻¹) ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L 2 f))) := by
    rw [mem_twistedTorusOf, hFn]
    exact ⟨eHom_diagonal_mem Fr D _ (Dgrp_offDiag hud), eHom_fixed Fr D hdU⟩
  obtain ⟨c₀, hc₀⟩ : g0 * eHom Fr D u * g0⁻¹ ∈ (adjEmb .E8 K L).range :=
    hYle ⟨⟨u, hu⟩, hηU_apply ⟨u, hu⟩ ▸ rfl⟩
  refine ⟨c₀ * c, ?_⟩
  have key : g0⁻¹ * adjEmb .E8 K L (c₀ * c * x * (c₀ * c)⁻¹) * g0 =
      eHom Fr D (u * monHom z * u⁻¹) := by
    have e1 : c₀ * c * x * (c₀ * c)⁻¹ = c₀ * (c * x * c⁻¹) * c₀⁻¹ := by group
    rw [e1, map_mul, map_mul, map_inv, hc₀, ← hz, hεc_apply, map_mul, map_mul, map_inv]
    group
  show g0⁻¹ * adjEmb .E8 K L (c₀ * c * x * (c₀ * c)⁻¹) * g0 ∈ _
  rw [key]
  exact hTor

theorem mod_five_of_dvd {q : ℕ} (h : 5 ∣ q * q + 1) : q % 5 = 2 ∨ q % 5 = 3 := by
  have h5 : (q * q + 1) % 5 = 0 := Nat.mod_eq_zero_of_dvd h
  have h6 : ((q % 5) * (q % 5) + 1) % 5 = 0 := by
    have : q * q + 1 ≡ (q % 5) * (q % 5) + 1 [MOD 5] :=
      ((Nat.mod_modEq q 5).symm.mul (Nat.mod_modEq q 5).symm).add_right 1
    exact this.symm.trans (Nat.modEq_zero_iff_dvd.2 h)
  have hlt : q % 5 < 5 := Nat.mod_lt _ (by norm_num)
  interval_cases hr : q % 5 <;> simp_all

theorem phi4FiveToral : Phi4FiveToral := by
  intro K _ _ _ f hf hK h5 L _ _ _ _
  obtain ⟨F, hFn⟩ := exists_frame_wr K hf hK L
  refine ⟨F, ?_⟩
  rcases mod_five_of_dvd h5 with h | h
  · exact e8FiveToral_of_datum hf hK h5 pairDatum2 (by rw [pairDatum2_c]; exact h) F hFn
  · exact e8FiveToral_of_datum hf hK h5 pairDatum3 (by rw [pairDatum3_c]; exact h) F hFn

end Main

end CFSG.RankThree.PartOne.KC1
