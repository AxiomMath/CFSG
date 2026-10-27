module

public import CFSG.Quasithin.H13.NQCatLieOverRank2
public import CFSG.LocalAnalysis.ComponentInitial.LinearThreeFourFixedNine
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting

public section

namespace CFSG.Quasithin.H13.D42

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.QuasithinUnique.Setup.X7a
open Matrix

theorem dvd_card_hall_of_model {X Y : Type} [Group X] [Group Y] [Finite Y] {d : ℕ} (hd : Odd d)
    {U₀ : Subgroup Y} (hU₀ : IsSylowTwoOf U₀ ⊤)
    (h : d ∣ Nat.card ↥(Subgroup.normalizer (U₀ : Set Y))) (e : X ≃* Y) {U C : Subgroup X}
    (hU : IsSylowTwoOf U ⊤) (hC : Lin2.IsHallTwoPrimeOf C (Subgroup.normalizer (U : Set X))) :
    d ∣ Nat.card ↥C := by
  have : Finite X := Finite.of_equiv _ e.symm.toEquiv
  have hU₁ : IsSylowTwoOf (U.map e.toMonoidHom) ⊤ := by
    refine ⟨le_top, hU.2.1.map _, ?_⟩
    have h1 := hU.2.2
    rw [show (U.subgroupOf ⊤).index = U.index from Subgroup.relIndex_top_right _] at h1
    rwa [show ((U.map e.toMonoidHom).subgroupOf ⊤).index = (U.map e.toMonoidHom).index from
      Subgroup.relIndex_top_right _, MulEquiv.toMonoidHom_eq_coe, Subgroup.index_map_equiv]
  obtain ⟨g, hg⟩ := NQCat.exists_conj_map_eq hU₁ hU₀
  set f : X ≃* Y := e.trans (MulAut.conj g) with hf
  have hUf : U.map f.toMonoidHom = U₀ := by
    rw [← hg, Subgroup.map_map]
    rfl
  have hN : (Subgroup.normalizer (U : Set X)).map f.toMonoidHom =
      Subgroup.normalizer (U₀ : Set Y) := by
    rw [Subgroup.map_equiv_normalizer_eq, hUf]
  have hcard : Nat.card ↥(Subgroup.normalizer (U : Set X)) =
      Nat.card ↥(Subgroup.normalizer (U₀ : Set Y)) := by
    rw [← hN, Subgroup.card_map_of_injective f.injective]
  obtain ⟨hCN, -, a, ha⟩ := hC
  have h1 := C5.card_eq_card_mul_relIndex hCN
  rw [ha, hcard] at h1
  rw [h1] at h
  exact (Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hd)).dvd_of_dvd_mul_right h

section SL3

variable {F : Type} [Field F]

theorem dHom_mem_upperTriangular (p : Fˣ × Fˣ) :
    LinearThreeFourFixedNine.dHom p ∈ upperTriangular 3 F := by
  intro i j hij
  rw [LinearThreeFourFixedNine.coe_dHom, diagonal_apply_ne _ (ne_of_gt hij)]

theorem dHom_injective : Function.Injective (LinearThreeFourFixedNine.dHom (k := F)) := by
  intro p q h
  have h0 := congrArg
    (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 0 0) h
  have h1 := congrArg
    (fun A : SpecialLinearGroup (Fin 3) F => (A : Matrix (Fin 3) (Fin 3) F) 1 1) h
  simp only [LinearThreeFourFixedNine.coe_dHom, diagonal_apply_eq] at h0 h1
  exact Prod.ext (Units.ext (by simpa using h0)) (Units.ext (by simpa using h1))

variable [Finite F]

omit [Finite F] in
theorem dvd_card_upperTriangular (hF : Nat.card F = 8) :
    49 ∣ Nat.card ↥(upperTriangular 3 F) := by
  have hu : Nat.card Fˣ = 7 := by rw [Nat.card_units, hF]
  have h1 : Nat.card ↥(LinearThreeFourFixedNine.dHom (k := F)).range = 49 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective dHom_injective).toEquiv, Nat.card_prod, hu]
  rw [← h1]
  exact Subgroup.card_dvd_of_le (by
    rintro _ ⟨p, rfl⟩
    exact dHom_mem_upperTriangular p)

omit [Finite F] in
theorem proj_injective_eight (hF : Nat.card F = 8) : Function.Injective (proj 3 F) := by
  rw [← MonoidHom.ker_eq_bot_iff, ker_proj, eq_bot_iff]
  rintro x ⟨c, hc3, hx⟩
  have hu : Nat.card Fˣ = 7 := by rw [Nat.card_units, hF]
  have hc7 : c ^ 7 = 1 := hu ▸ pow_card_eq_one'
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ Nat.gcd 3 7 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hc3) (orderOf_dvd_of_pow_eq_one hc7)
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp (by simpa using h1))
  rw [Subgroup.mem_bot]
  exact Subtype.ext (hx.trans (by rw [hc1]; simp))

theorem dvd_card_sl3 (hF : Nat.card F = 8) {X : Type} [Group X]
    (e : X ≃* SpecialLinearGroup (Fin 3) F) {U C : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hC : Lin2.IsHallTwoPrimeOf C (Subgroup.normalizer (U : Set X))) : 49 ∣ Nat.card ↥C := by
  have : CharP F 2 := finite_field_prime_power_characteristic (k := 3) Nat.prime_two
    (by norm_num) (by rw [hF]; norm_num)
  obtain ⟨P, hP⟩ := exists_sylow_unitriangular (K := F) 2 (n := 3) (by norm_num)
  have hU₀ : IsSylowTwoOf (unitriangular 3 F) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hN : Subgroup.normalizer ((unitriangular 3 F : Subgroup (SpecialLinearGroup (Fin 3) F)) :
      Set (SpecialLinearGroup (Fin 3) F)) = upperTriangular 3 F := normalizer_unitriangular
  refine dvd_card_hall_of_model (by decide) hU₀ ?_ e hU hC
  rw [hN]
  exact dvd_card_upperTriangular hF

end SL3

theorem dvd_card_sp4 {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 8)
    {X : Type} [Group X]
    (e : X ≃* CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K))
    {U C : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hC : Lin2.IsHallTwoPrimeOf C (Subgroup.normalizer (U : Set X))) : 49 ∣ Nat.card ↥C := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let π : CFSG.Assembly.LowTwoRank.StatedSp 2 K ≃*
      CFSG.Assembly.LowTwoRank.StatedProj (CFSG.Assembly.LowTwoRank.StatedSp 2 K) :=
    MulEquiv.ofBijective (SymplecticFlag.proj 2 K)
      ⟨Vol2Native.A312L.proj_injective_charTwo, QuotientGroup.mk'_surjective _⟩
  obtain ⟨P, hP⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 2
  have hU₀ : IsSylowTwoOf (SymplecticFlag.unipotent 2 K) ⊤ :=
    hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hN := SymplecticHigher.normalizer_unipotent (r := 2) (K := K)
  refine dvd_card_hall_of_model (by decide) hU₀ ?_ (e.trans π.symm) hU hC
  rw [hN, SymplecticFlag.card_borelSubgroup, hK]
  norm_num

theorem dvd_card_of_rank2_eight {X : Type} [Group X] [Finite X]
    (htype : IsSL3Ch5 3 X ∨ LieModel X .PSp 2 2 3) {U C : Subgroup X} (hU : IsSylowTwoOf U ⊤)
    (hC : Lin2.IsHallTwoPrimeOf C (Subgroup.normalizer (U : Set X))) : 49 ∣ Nat.card ↥C := by
  rcases htype with (hL | ⟨F, _, _, hcard, ⟨e⟩⟩) | hSp
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hL
    have hK : Nat.card K = 8 := by rw [hcard]; norm_num
    let φ : SpecialLinearGroup (Fin 3) K ≃* projectiveSL 3 K :=
      MulEquiv.ofBijective (proj 3 K) ⟨proj_injective_eight hK, proj_surjective 3 K⟩
    exact dvd_card_sl3 hK (e.trans ((statedSLEquivProjectiveSL 3 K).trans φ.symm)) hU hC
  · exact dvd_card_sl3 (by rw [hcard]; norm_num) e hU hC
  · obtain ⟨-, K, _, _, hcard, ⟨e⟩⟩ :=
      CFSG.LieType.Steinberg.statedClassicalModel_of_lieModel (by decide) hSp
    have : CharP K 2 :=
      finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
    exact dvd_card_sp4 (by rw [hcard]; norm_num) e hU hC

end CFSG.Quasithin.H13.D42
