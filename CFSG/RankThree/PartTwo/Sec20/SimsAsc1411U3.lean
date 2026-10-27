module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Skeleton
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U3Group
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Order
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Outer
import CFSG.Models.PGL

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup CFSG.Assembly.LowTwoRank

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private theorem relIndex_centralizer_conj' {I : Subgroup X} (hI : I.Normal) (g x : X) :
    (centralizer ({g * x * g⁻¹} : Set X)).relIndex I =
      (centralizer ({x} : Set X)).relIndex I := by
  have hcomap : (centralizer ({g * x * g⁻¹} : Set X)).comap
      (MulAut.conj g).toMonoidHom = centralizer ({x} : Set X) := by
    ext y
    simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hy
      have h1 : g * (x * y) * g⁻¹ = g * (y * x) * g⁻¹ := by
        calc g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
          _ = g * y * g⁻¹ * (g * x * g⁻¹) := hy.symm
          _ = g * (y * x) * g⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel h1)).symm
    · intro hy
      calc g * y * g⁻¹ * (g * x * g⁻¹) = g * (y * x) * g⁻¹ := by group
        _ = g * (x * y) * g⁻¹ := by rw [hy]
        _ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
  rw [← hcomap, Subgroup.relIndex_comap]
  congr 1
  exact (Subgroup.normal_iff_map_conj_eq.mp hI g).symm

theorem conjNormal_not_mem_range_of_hyp1411 (h : Hyp1411 X L S)
    [(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))).Normal]
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥)
    {t : X} (htS : t ∈ S) (htQ : t ∉ CFSG.pCore 2 X) :
    MulAut.conjNormal (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) t) ∉
      (MulAut.conj : ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) →*
        MulAut ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))).range := by
  rintro ⟨g, hg⟩
  obtain ⟨y, hyL, hy⟩ := not_inner_of_inf_eq_bot_of_hyp1411 h hSL htS htQ
    (g : X ⧸ CFSG.pPrimeCore 3 X) g.2
  apply hy
  have h1 := congrArg (fun f : MulAut ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) =>
    ((f ⟨y, hyL⟩ : ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))) :
      X ⧸ CFSG.pPrimeCore 3 X)) hg
  simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  exact h1.symm

theorem noSmall1411_of_U3 (h : Hyp1411 X L S) {m : ℕ} (hm : 2 ≤ m)
    (hD : StatedClassicalModel ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) .PSU 3 2 m)
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    NoSmall1411 X L S := by
  intro I hIn hI hLI t htS htQ htt
  by_contra hle
  push Not at hle
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  set ψ : MulAut ↥(L.map π) := MulAut.conjNormal (π t) with hψ
  have hψ2 : ψ * ψ = 1 := by
    rw [hψ, ← map_mul, ← map_mul, htt, map_one, map_one]
  have hout := conjNormal_not_mem_range_of_hyp1411 h hSL htS htQ
  have hψ1 : ψ ≠ 1 := fun h1 => hout ⟨1, by rw [map_one, ← hψ, h1]⟩
  have hord : orderOf ψ = 2 := orderOf_eq_prime (by rw [sq]; exact hψ2) hψ1
  obtain ⟨x, n, hn, hn105, hx⟩ := exists_odd_dvd_orderOf_mul_inv_U3 hm hD ψ hord hout
  have hsimp : IsSimpleGroup ↥(L.map π) :=
    (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 m hD).2
  have hbot := map_centralizer_inf_eq_bot_of_hyp1411 h hsimp hIn hLI
  obtain ⟨ℓ, -, hℓ⟩ := x.2
  have hu : t ∈ normalizer (I : Set X) := by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top t
  have hv : ℓ * t⁻¹ * ℓ⁻¹ ∈ normalizer (I : Set X) := by
    rw [normalizer_eq_top_iff.mpr hIn]
    exact mem_top _
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right htt
  have hvb : (centralizer ({ℓ * t⁻¹ * ℓ⁻¹} : Set X)).relIndex I ≤ 4 := by
    rw [relIndex_centralizer_conj' hIn, htinv]
    exact hle
  have hvv : ℓ * t⁻¹ * ℓ⁻¹ * (ℓ * t⁻¹ * ℓ⁻¹) = 1 := by
    rw [htinv]
    calc ℓ * t * ℓ⁻¹ * (ℓ * t * ℓ⁻¹) = ℓ * (t * t) * ℓ⁻¹ := by group
      _ = 1 := by rw [htt, mul_one, mul_inv_cancel]
  obtain ⟨N, -, hpow, h15⟩ := exists_pow_mem_centralizer_odd_dvd_15 hI hu hv htt hvv hle hvb
  have himg : π (t * (ℓ * t⁻¹ * ℓ⁻¹)) =
      ((ψ x * x⁻¹ : ↥(L.map π)) : X ⧸ CFSG.pPrimeCore 3 X) := by
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hψ, MulAut.conjNormal_apply, ← hℓ]
    simp only [map_mul, map_inv]
    group
  have h1 : (ψ x * x⁻¹) ^ (2 * N) = 1 := by
    apply Subtype.ext
    have hmem : ((((ψ x * x⁻¹) ^ (2 * N) : ↥(L.map π))) :
        X ⧸ CFSG.pPrimeCore 3 X) ∈ (centralizer (I : Set X)).map π ⊓ L.map π := by
      refine ⟨⟨_, hpow, ?_⟩, Subtype.mem _⟩
      rw [map_pow, himg, Subgroup.coe_pow]
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hdvd : n ∣ 2 * N := hx.trans (orderOf_dvd_of_pow_eq_one h1)
  have hdvdN : n ∣ N := Nat.Coprime.dvd_of_dvd_mul_left (Nat.coprime_two_right.mpr hn) hdvd
  exact hn105 ((h15 n hn hdvdN).trans (by norm_num))

theorem relIndex_pCore_le_two_of_U3 (h : Hyp1411 X L S) {m : ℕ} (hm : 2 ≤ m)
    (hD : StatedClassicalModel ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) .PSU 3 2 m)
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 2 := by
  intro A hAS hA
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 X) with hπ
  have : (L.map π).Normal := h.2.1.map π (QuotientGroup.mk'_surjective _)
  obtain ⟨K, _, Φ, σ₀, hker, hinv⟩ := exists_hom_ringEquiv_of_U3 hm hD
  set χ : A →* (K ≃+* K) :=
    Φ.comp ((MulAut.conjNormal : X ⧸ CFSG.pPrimeCore 3 X →* MulAut ↥(L.map π)).comp
      (π.comp A.subtype)) with hχ
  have hsq : ∀ a : A, (MulAut.conjNormal (π a) : MulAut ↥(L.map π)) *
      MulAut.conjNormal (π a) = 1 := by
    intro a
    rw [← map_mul, ← map_mul, hA.2 _ a.2, map_one, map_one]
  have hkerχ : χ.ker ≤ (CFSG.pCore 2 X).subgroupOf A := by
    intro a ha
    rw [mem_subgroupOf]
    by_contra haQ
    exact conjNormal_not_mem_range_of_hyp1411 h hSL (hAS a.2) haQ (hker _ (hsq a) ha)
  have hrange : ((χ.range : Subgroup (K ≃+* K)) : Set (K ≃+* K)) ⊆ {1, σ₀} := by
    rintro _ ⟨a, rfl⟩
    have h2 : χ a * χ a = 1 := by
      rw [← map_mul, show a * a = 1 from Subtype.ext (hA.2 _ a.2), map_one]
    rcases hinv _ h2 with h1 | h1
    · exact Or.inl h1
    · exact Or.inr h1
  have hcard : Nat.card χ.range ≤ 2 := by
    rw [← SetLike.coe_sort_coe, Nat.card_coe_set_eq]
    calc ((χ.range : Subgroup (K ≃+* K)) : Set (K ≃+* K)).ncard
        ≤ ({1, σ₀} : Set (K ≃+* K)).ncard := Set.ncard_le_ncard hrange
      _ ≤ ({σ₀} : Set (K ≃+* K)).ncard + 1 := Set.ncard_insert_le _ _
      _ = 2 := by rw [Set.ncard_singleton]
  calc (CFSG.pCore 2 X).relIndex A = ((CFSG.pCore 2 X).subgroupOf A).index := rfl
    _ ≤ χ.ker.index :=
      Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
        (Subgroup.index_dvd_of_le hkerχ)
    _ = Nat.card χ.range := Subgroup.index_ker χ
    _ ≤ 2 := hcard

theorem asc82Item1411_of_U3 (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S) {m : ℕ} (hm : 2 ≤ m)
    (hD : StatedClassicalModel ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))) .PSU 3 2 m)
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal :=
  asc82Item1411_of_noSmall h (relIndex_pCore_le_two_of_U3 h hm hD hSL)
    (noSmall1411_of_U3 h hm hD hSL)

theorem statedClassicalModel_of_mulEquiv_projSU3 {G : Type} [Group G] {m : ℕ} (hm : 2 ≤ m)
    (e : G ≃* CFSG.Assembly.RankThreeEven.projSU 3 2 m) :
    StatedClassicalModel G .PSU 3 2 m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU
    ⟨Nat.prime_two, by omega, le_rfl, fun h3 => ?_⟩ e
  have h2 : 2 ^ m = 2 := (Prod.mk.inj h3).2
  have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  omega

theorem statedScalars_subgroupOf_su3_eq_bot {m : ℕ} (hm : Even m) (hm1 : 1 ≤ m) :
    (CFSG.Open.StatedScalars (Fin 3) (GaloisField 2 (2 * m))).subgroupOf
      (CFSG.Open.StatedSU 3 (2 ^ m) (GaloisField 2 (2 * m))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [eq_bot_iff]
  rintro ⟨x, hx⟩ hxs
  rw [mem_subgroupOf] at hxs
  obtain ⟨c, hc⟩ := hxs
  rw [Subgroup.mem_bot, Subtype.ext_iff, Subgroup.coe_one]
  change x = 1
  have hK : Nat.card (GaloisField 2 (2 * m)) = (2 ^ m) ^ 2 := by
    rw [GaloisField.card 2 (2 * m) (by omega), ← pow_mul, mul_comm]
  have hmem : Matrix.GeneralLinearGroup.scalar (Fin 3) c ∈
      CFSG.Open.StatedSU 3 (2 ^ m) (GaloisField 2 (2 * m)) := by
    rw [hc]
    exact hx
  obtain ⟨h3, hq⟩ := (CFSG.LinearGroups.scalar_mem_statedSU_iff Nat.prime_two hK (by norm_num)
    c).mp hmem
  have hmod : 2 * (2 ^ m + 1) % 3 = 1 := by
    obtain ⟨k, rfl⟩ := hm
    rw [← two_mul, pow_mul, Nat.mul_mod, Nat.add_mod, Nat.pow_mod]
    norm_num
  have hc1 : c = 1 := by
    have e1 : c ^ (2 * (2 ^ m + 1)) = 1 := by rw [pow_mul', hq, one_pow]
    rw [← Nat.div_add_mod (2 * (2 ^ m + 1)) 3, hmod, pow_add, pow_mul, h3, one_pow, one_mul,
      pow_one] at e1
    exact e1
  have hx1 : x = Matrix.GeneralLinearGroup.scalar (Fin 3) c := hc.symm
  rw [hx1, hc1, map_one]

theorem su3_eq_statedSU (m : ℕ) :
    Res6.su3 2 m = CFSG.Open.StatedSU 3 (2 ^ m) (GaloisField 2 (2 * m)) := by
  rw [CFSG.PGLModel.statedSU_eq_closure_det]
  rfl

theorem statedClassicalModel_of_mulEquiv_su3 {G : Type} [Group G] {m : ℕ} (hm : Even m)
    (hm2 : 2 ≤ m) (e : G ≃* Res6.su3 2 m) : StatedClassicalModel G .PSU 3 2 m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, fun h3 => ?_⟩, GaloisField 2 (2 * m), inferInstance,
    inferInstance, ?_, ⟨?_⟩⟩
  · have h2 : 2 ^ m = 2 := (Prod.mk.inj h3).2
    have : 2 ^ 2 ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
    omega
  · rw [GaloisField.card 2 (2 * m) (by omega), ← pow_mul, mul_comm]
  · exact e.trans ((MulEquiv.subgroupCongr (su3_eq_statedSU m)).trans
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq
        (statedScalars_subgroupOf_su3_eq_bot hm (by omega)).symm)))

theorem asc82Item1411_projSU3 (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S) {m : ℕ} (hm : 2 ≤ m)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
      CFSG.Assembly.RankThreeEven.projSU 3 2 m))
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal :=
  asc82Item1411_of_U3 X L S h hm (statedClassicalModel_of_mulEquiv_projSU3 hm hL.some) hSL

theorem asc82Item1411_su3even (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S) {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃* Res6.su3 2 m))
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal :=
  asc82Item1411_of_U3 X L S h hm2 (statedClassicalModel_of_mulEquiv_su3 hm hm2 hL.some) hSL

theorem asc82Item1411_U3even (X : Type) [Group X] [Finite X] (L S : Subgroup X)
    (h : Hyp1411 X L S) {m : ℕ} (hm : Even m) (hm2 : 2 ≤ m)
    (hL : Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃* Res6.su3 2 m) ∨
      Nonempty (L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ≃*
        CFSG.Assembly.RankThreeEven.projSU 3 2 m))
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    ∃ i₁ i₂ : Fin 4, i₁ ≠ i₂ ∧ i₁ ≠ 3 ∧ i₂ ≠ 3 ∧ (Sec18.fourChar S i₁).Normal ∧
      (Sec18.fourChar S i₂).Normal := by
  rcases hL with hL | hL
  · exact asc82Item1411_su3even X L S h hm hm2 hL hSL
  · exact asc82Item1411_projSU3 X L S h hm2 hL hSL

end CFSG.RankThree.PartTwo.Sec20
