module

public import CFSG.ClassicalGroups.Orthogonal.MinusSplitTorus
public import CFSG.RankThree.GF2n.Smith81.OrthTensorModel
public import CFSG.GroupTheory.CentralCoverTorus
public import CFSG.GroupTheory.TwoPowOrderFactorization
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Matrix CFSG.Open
open CFSG.Blueprint (LieModel)
open CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.OmegaEven
open CFSG.LieType.Universal.Spin
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl

theorem card_statedOmega_quadMinus_four {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F}
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(StatedOmega (StatedQuadMinus 4 F b c)) =
      Nat.card F ^ 12 * (Nat.card F ^ 4 + 1) *
        ((Nat.card F ^ 2 - 1) * ((Nat.card F ^ 4 - 1) * (Nat.card F ^ 6 - 1))) := by
  have h := CFSG.RankThree.GF2n.Smith81.card_statedOmega_minus_eq (K := F) (m := 4)
    (by norm_num) hirr
  have hset : Finset.Icc 1 3 = ({1, 2, 3} : Finset ℕ) := by decide
  rw [hset, Finset.prod_insert (by decide), Finset.prod_insert (by decide),
    Finset.prod_singleton] at h
  norm_num at h
  have hq : 2 ≤ Nat.card F := Finite.one_lt_card
  have hpow : ∀ k : ℕ, 1 ≤ Nat.card F ^ k := by
    intro k
    calc 1 = 1 ^ k := (one_pow k).symm
      _ ≤ Nat.card F ^ k := Nat.pow_le_pow_left (by omega) k
  have hcast : (((Nat.card F ^ 12 * (Nat.card F ^ 4 + 1) *
      ((Nat.card F ^ 2 - 1) * ((Nat.card F ^ 4 - 1) * (Nat.card F ^ 6 - 1)))) : ℕ) : ℤ) =
      (Nat.card F : ℤ) ^ 12 * ((Nat.card F : ℤ) ^ 4 + 1) *
        (((Nat.card F : ℤ) ^ 2 - 1) * (((Nat.card F : ℤ) ^ 4 - 1) *
          ((Nat.card F : ℤ) ^ 6 - 1))) := by
    simp only [Nat.cast_mul, Nat.cast_add, Nat.cast_one, Nat.cast_pow]
    rw [Nat.cast_sub (hpow 2), Nat.cast_sub (hpow 4), Nat.cast_sub (hpow 6)]
    push_cast
    ring
  rw [← hcast] at h
  exact Nat.cast_injective h

theorem factorization_card_statedOmega_quadMinus_four {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrd : r ∣ Nat.card F - 1) :
    (Nat.card ↥(StatedOmega (StatedQuadMinus 4 F b c))).factorization r =
      3 * (Nat.card F - 1).factorization r := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hq0 : Nat.card F ≠ 0 := by omega
  have h2n : Nat.card F ^ 2 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (by norm_num : 2 ≠ 0) hq; omega
  have h4n : Nat.card F ^ 4 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (by norm_num : 4 ≠ 0) hq; omega
  have h6n : Nat.card F ^ 6 - 1 ≠ 0 := by
    have := Nat.one_lt_pow (by norm_num : 6 ≠ 0) hq; omega
  have h4p1n : Nat.card F ^ 4 + 1 ≠ 0 := by positivity
  have hr2 : r ≠ 2 := by omega
  have hmod : Nat.card F ≡ 1 [MOD r] :=
    ((Nat.modEq_iff_dvd' (a := 1) (b := Nat.card F) (by omega)).mpr (by simpa using hrd)).symm
  have hqzero : (Nat.card F).factorization r = 0 :=
    Nat.factorization_eq_zero_of_not_dvd (CFSG.GroupTheory.not_dvd_of_modEq_one_of_prime hr hmod)
  have hnr2 : ¬ r ∣ 2 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hnr4 : ¬ r ∣ 4 := fun h => by have := Nat.le_of_dvd (by norm_num) h; omega
  have hnr6 : ¬ r ∣ 6 := fun h => by
    have hle := Nat.le_of_dvd (by norm_num) h
    have hr56 : r = 5 ∨ r = 6 := by omega
    rcases hr56 with rfl | rfl <;> [norm_num at h; norm_num at hr]
  have h2 : (Nat.card F ^ 2 - 1).factorization r = (Nat.card F - 1).factorization r := by
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hr hr2 hq hrd
      (by norm_num : 2 ≠ 0), Nat.factorization_eq_zero_of_not_dvd hnr2, add_zero]
  have h4 : (Nat.card F ^ 4 - 1).factorization r = (Nat.card F - 1).factorization r := by
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hr hr2 hq hrd
      (by norm_num : 4 ≠ 0), Nat.factorization_eq_zero_of_not_dvd hnr4, add_zero]
  have h6 : (Nat.card F ^ 6 - 1).factorization r = (Nat.card F - 1).factorization r := by
    rw [CFSG.HardMathSupport.Timmesfeld.LinearRank.factorization_pow_sub_one hr hr2 hq hrd
      (by norm_num : 6 ≠ 0), Nat.factorization_eq_zero_of_not_dvd hnr6, add_zero]
  have h4p1 : (Nat.card F ^ 4 + 1).factorization r = 0 :=
    CFSG.GroupTheory.factorization_pow_add_one_eq_zero (k := 4) hr hr2 hmod
  rw [card_statedOmega_quadMinus_four hirr,
    Nat.factorization_mul (mul_ne_zero (pow_ne_zero 12 hq0) h4p1n)
      (mul_ne_zero h2n (mul_ne_zero h4n h6n)),
    Nat.factorization_mul (pow_ne_zero 12 hq0) h4p1n,
    Nat.factorization_mul h2n (mul_ne_zero h4n h6n),
    Nat.factorization_mul h4n h6n,
    Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply, Finsupp.add_apply,
    Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hqzero, mul_zero,
    h4p1, h2, h4, h6]
  ring

theorem card_closure_minusDiagGL {F : Type} [Field F] [Finite F] [CharP F 2] {b c : F} {r : ℕ}
    (hr : Odd r) (ζ : Fˣ) (hd : ∀ i : Fin 3,
      ∀ j : Fin 3, ((Pi.mulSingle i ζ : Fin 3 → Fˣ) j) ^ r = 1) :
    Nat.card (Subgroup.closure (Set.range fun i : Fin 3 =>
      minusDiagGL (b := b) (c := c) (n := 4) hr (Pi.mulSingle i ζ) (hd i))) = orderOf ζ ^ 3 := by
  classical
  set F' : (Fin 3 → Fˣ) →* GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F :=
    (diagGL (K := F) (ι := Fin 3 ⊕ Fin 3 ⊕ Fin 2)).comp (torusEntMinus 3 F) with hF'
  have hcoe : ∀ i : Fin 3, ((minusDiagGL (b := b) (c := c) (n := 4) hr (Pi.mulSingle i ζ) (hd i) :
      StatedOmega (StatedQuadMinus 4 F b c)) : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) =
      F' (Pi.mulSingle i ζ) := fun i => rfl
  have hinj : Function.Injective F' := by
    intro x y hxy
    have h1 : (diagGL (K := F) (ι := Fin 3 ⊕ Fin 3 ⊕ Fin 2)).comp (torusEntMinus 3 F) x =
        (diagGL (K := F) (ι := Fin 3 ⊕ Fin 3 ⊕ Fin 2)).comp (torusEntMinus 3 F) y := hxy
    simp only [MonoidHom.comp_apply] at h1
    have h2 : torusEntMinus 3 F x = torusEntMinus 3 F y := by
      funext j
      apply Units.ext
      have h := congrArg (fun g : GL (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F =>
        (g : Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) F) j j) h1
      simpa only [coe_diagGL, Matrix.diagonal_apply_eq] using h
    funext j
    have h := congrFun h2 (Sum.inl j : Fin 3 ⊕ Fin 3 ⊕ Fin 2)
    simpa [torusEntMinus] using h
  have hpi : Nat.card (Subgroup.pi Set.univ (fun _ : Fin 3 => Subgroup.zpowers ζ)) =
      orderOf ζ ^ 3 := by
    have h := card_pi_ite_zpowers (k := F) 3 ζ Finset.univ
    simpa using h
  have hmap : Subgroup.closure (Set.range fun i : Fin 3 => F' (Pi.mulSingle i ζ)) =
      (Subgroup.pi Set.univ (fun _ : Fin 3 => Subgroup.zpowers ζ)).map F' := by
    have h1 : Set.range (fun i : Fin 3 => F' (Pi.mulSingle i ζ)) =
        F' '' (Set.range fun i : Fin 3 => Pi.mulSingle i ζ) := by
      ext x
      simp only [Set.mem_range, Set.mem_image]
      exact ⟨fun ⟨i, hi⟩ => ⟨_, ⟨i, rfl⟩, hi⟩, fun ⟨_, ⟨i, rfl⟩, hi⟩ => ⟨i, hi⟩⟩
    rw [h1, ← MonoidHom.map_closure, (pi_zpowers_eq_closure 3 ζ).symm]
  have hSe : (Subgroup.subtype (StatedOmega (StatedQuadMinus 4 F b c)) ''
      (Set.range fun i : Fin 3 =>
        minusDiagGL (b := b) (c := c) (n := 4) hr (Pi.mulSingle i ζ) (hd i))) =
      Set.range (fun i : Fin 3 => F' (Pi.mulSingle i ζ)) := by
    ext x
    simp only [Set.mem_image, Set.mem_range]
    constructor
    · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, (hcoe i).symm⟩
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, hcoe i⟩
  rw [← Subgroup.card_map_of_injective
    (Subgroup.subtype_injective (StatedOmega (StatedQuadMinus 4 F b c))),
    MonoidHom.map_closure, hSe, hmap, Subgroup.card_map_of_injective hinj, hpi]

theorem exists_cover_omegaMinus8 {K : Type} [Group K] [Finite K] {f : ℕ}
    (hK : CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaMinus 4 2 f) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ f ∧
      ∃ b c : F, (∀ s : F, s ^ 2 + b * s + c ≠ 0) ∧
      ∃ φ : K →* ↥(StatedOmega (StatedQuadMinus 4 F b c)),
        Function.Surjective φ ∧ φ.ker ≤ Subgroup.center K := by
  obtain ⟨-, F, hF, hFin, hFcard, b, c, hirr, ⟨e⟩⟩ := hK.statedClassicalModel (by decide)
  letI := hF
  letI := hFin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card, hFcard])
  have hbot : (StatedScalars (Fin (4 - 1) ⊕ Fin (4 - 1) ⊕ Fin 2) F).subgroupOf
      (StatedOmega (StatedQuadMinus 4 F b c)) = ⊥ :=
    CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedOmega_eq_bot
      (Q := quadMinus 4 F b c) (coe_quadMinus 4 F b c)
      ⟨_, by rw [quadMinus_minusFlipVec (n := 4) ⟨0, by norm_num⟩]; exact one_ne_zero⟩
  let eProj : ↥(StatedOmega (StatedQuadMinus 4 F b c)) ≃*
      StatedProj (StatedOmega (StatedQuadMinus 4 F b c)) :=
    CFSG.RankThree.PartOne.KFU.equivProjOfScalarsBot _ hbot
  let ψ : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let φ : K →* ↥(StatedOmega (StatedQuadMinus 4 F b c)) :=
    eProj.symm.toMonoidHom.comp (e.toMonoidHom.comp ψ)
  have hφ : Function.Surjective φ :=
    eProj.symm.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hker : φ.ker ≤ Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ eProj.symm.injective,
      MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  exact ⟨F, hF, hFin, hFcard, b, c, hirr, φ, hφ, hker⟩

private theorem exists_sylow_closure_omegaMinus8 {F : Type} [Field F] [Finite F] [CharP F 2]
    {b c : F} (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrd : r ∣ Nat.card F - 1) :
    ∃ (S : Set (StatedOmega (StatedQuadMinus 4 F b c)))
      (D : Sylow r (StatedOmega (StatedQuadMinus 4 F b c))),
      (D : Subgroup (StatedOmega (StatedQuadMinus 4 F b c))) = Subgroup.closure S ∧
      (∀ s ∈ S, ∀ t ∈ S, Commute s t) ∧
      (∀ s ∈ S, Odd (orderOf s)) ∧
      (∀ s ∈ S, ∀ t ∈ S, s ≠ t →
        (∃ c : StatedOmega (StatedQuadMinus 4 F b c),
            c * s * c⁻¹ = s⁻¹ ∧ c * t * c⁻¹ = t) ∨
          (∃ c : StatedOmega (StatedQuadMinus 4 F b c),
            c * t * c⁻¹ = t⁻¹ ∧ c * s * c⁻¹ = s)) := by
  have hq : 1 < Nat.card F := Finite.one_lt_card
  set a : ℕ := (Nat.card F - 1).factorization r with ha
  have hra : r ^ a ∣ Nat.card F - 1 := by
    rw [ha]; exact (hr.pow_dvd_iff_le_factorization (by omega)).mpr le_rfl
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
  have hgord : orderOf g = Nat.card F - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hg, Nat.card_units]
  let ζ : Fˣ := g ^ (orderOf g / r ^ a)
  have hζ : orderOf ζ = r ^ a :=
    orderOf_pow_orderOf_div (orderOf_pos g).ne' (by rw [hgord]; exact hra)
  have hrodd : Odd (r ^ a) := (hr.odd_of_ne_two (by omega)).pow
  have hdζ : ∀ i : Fin 3, ∀ j : Fin 3, ((Pi.mulSingle i ζ : Fin 3 → Fˣ) j) ^ (r ^ a) = 1 := by
    intro i j
    by_cases hj : j = i
    · subst hj
      simpa [Pi.mulSingle_eq_same, ← hζ] using pow_orderOf_eq_one ζ
    · rw [Pi.mulSingle_eq_of_ne hj, one_pow]
  let S : Set (StatedOmega (StatedQuadMinus 4 F b c)) :=
    Set.range fun i : Fin 3 =>
      minusDiagGL (b := b) (c := c) (n := 4) hrodd (Pi.mulSingle i ζ) (hdζ i)
  have hS_comm : ∀ s ∈ S, ∀ t ∈ S, Commute s t := by
    rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩
    exact commute_minusDiagGL (b := b) (c := c) (n := 4) hrodd _ _ (hdζ i) (hdζ j)
  have hS_odd : ∀ s ∈ S, Odd (orderOf s) := by
    rintro s ⟨i, rfl⟩
    rw [orderOf_minusDiagGL_mulSingle (n := 4) hrodd ζ i (hdζ i), hζ]; exact hrodd
  have hthird : ∀ i j : Fin 3, i ≠ j → ∃ k : Fin 3, k ≠ i ∧ k ≠ j := by decide
  have hinv : ∀ s ∈ S, ∀ t ∈ S, s ≠ t →
      (∃ c : StatedOmega (StatedQuadMinus 4 F b c),
          c * s * c⁻¹ = s⁻¹ ∧ c * t * c⁻¹ = t) ∨
        (∃ c : StatedOmega (StatedQuadMinus 4 F b c),
          c * t * c⁻¹ = t⁻¹ ∧ c * s * c⁻¹ = s) := by
    rintro s ⟨i, rfl⟩ t ⟨j, rfl⟩ hst
    have hij : i ≠ j := fun h => hst (by rw [h])
    obtain ⟨k, hki, hkj⟩ := hthird i j hij
    have hik : i ≠ k := fun h => hki h.symm
    exact Or.inl ⟨minusPairFlip (b := b) (c := c) (n := 4) hirr i k hik,
      minusPairFlip_conj_inv (b := b) (c := c) (n := 4) hirr hrodd _ (hdζ i) hik
        (fun l => congrFun (torusEntMinus_comp_minusFlip_inv (i := i) (k := k) hik
          (fun j' hj' hk' => by rw [Pi.mulSingle_eq_of_ne hj'])) l),
      minusPairFlip_conj_eq (b := b) (c := c) (n := 4) hirr hrodd _ (hdζ j) hik
        (fun l => congrFun (torusEntMinus_comp_minusFlip_eq (i := i) (k := k) hik
          (by rw [Pi.mulSingle_eq_of_ne hij])
          (by rw [Pi.mulSingle_eq_of_ne hkj])) l)⟩
  have hcardS : Nat.card (Subgroup.closure S) = (r ^ a) ^ 3 := by
    rw [card_closure_minusDiagGL hrodd ζ hdζ, hζ]
  have hSpg : IsPGroup r (Subgroup.closure S) :=
    IsPGroup.of_card (n := 3 * a) (by rw [hcardS, ← pow_mul, Nat.mul_comm])
  have hrpow : (r ^ a).factorization r = a := by
    rw [Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hr.factorization_self, mul_one]
  haveI : Fact r.Prime := ⟨hr⟩
  have hidx : ¬ r ∣ (Subgroup.closure S).index :=
    CFSG.HardMathSupport.Timmesfeld.LinearRank.not_dvd_index_of_card_eq hr _
      (by rw [factorization_card_statedOmega_quadMinus_four hirr hr hr5 hrd, hcardS,
        Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hrpow])
  exact ⟨S, hSpg.toSylow hidx, IsPGroup.toSylow_coe hSpg hidx, hS_comm, hS_odd, hinv⟩

theorem k_CartanSylowAbelian_omegaMinus8 :
    ∀ (K : Type) [Group K] [Finite K] (f r : ℕ),
      CFSG.Open.StatedLieAdmissible .POmegaMinus 4 2 f →
        CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .POmegaMinus 4 2 f →
          CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
            r.Prime → 5 ≤ r → r ∣ 2 ^ f - 1 →
              ∀ P : Sylow r K, IsMulCommutative (P : Subgroup K) := by
  intro K _ _ f r hAdm hK hQ hOddC hr hr5 hrdvd P
  obtain ⟨F, hF, hFin, hFcard, b, c, hirr, φ, hφ, hker⟩ := exists_cover_omegaMinus8 hK
  letI := hF
  letI := hFin
  haveI : Fintype F := Fintype.ofFinite F
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (p := 2) (f := f) (by
    rw [← Nat.card_eq_fintype_card, hFcard])
  have hrd' : r ∣ Nat.card F - 1 := by rw [hFcard]; exact hrdvd
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨S, D, hDcoe, hS_comm, hS_odd, hinv⟩ :=
    exists_sylow_closure_omegaMinus8 (F := F) hirr hr hr5 hrd'
  have hcomm := CFSG.GroupTheory.comap_closure_comm_of_inverters (φ := φ) hφ hker
    hS_comm hS_odd hinv
  have hDcomm : ∀ x ∈ (D : Subgroup (StatedOmega (StatedQuadMinus 4 F b c))).comap φ,
      ∀ y ∈ (D : Subgroup (StatedOmega (StatedQuadMinus 4 F b c))).comap φ,
      x * y = y * x := by
    rw [hDcoe]
    exact hcomm
  exact CFSG.GroupTheory.isMulCommutative_sylow_of_comap_comm hφ D hDcomm P

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
