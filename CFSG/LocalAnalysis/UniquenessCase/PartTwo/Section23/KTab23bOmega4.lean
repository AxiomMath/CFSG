module

public import CFSG.CGT.PushingUpLit.CGT6.EmbOmegaData
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section18.EighteenThirteen
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaPlusFourSquare
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineB23Lines
public import CFSG.GroupTheory.ProdFactors
public import CFSG.ClassicalInvolution.AschTight.S19COrd
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bL2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG CFSG.Open CFSG.GroupTheory CFSG.Quasithin.S151S4 Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

theorem conj_uU_mem_Usub {K : Type} [Field K] [CharP K 2] {b : SL2 K}
    (hb : b ∈ Bsub K) (t : K) :
    b * uU t * b⁻¹ ∈ Usub K := by
  rw [mem_Usub]
  refine ⟨(b : Matrix (Fin 2) (Fin 2) K) 0 0 ^ 2 * t, ?_⟩
  apply Subtype.ext
  have hdet : (b : Matrix (Fin 2) (Fin 2) K) 0 0 * (b : Matrix (Fin 2) (Fin 2) K) 1 1 -
      (b : Matrix (Fin 2) (Fin 2) K) 0 1 * (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 1 := by
    have := b.2
    rwa [Matrix.det_fin_two] at this
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, coe_uU, Matrix.mul_fin_two, Matrix.of_apply]
  have hb10 : (b : Matrix (Fin 2) (Fin 2) K) 1 0 = 0 := hb
  have hdet' : (b : Matrix (Fin 2) (Fin 2) K) 0 0 * (b : Matrix (Fin 2) (Fin 2) K) 1 1 = 1 := by
    simpa [hb10] using hdet
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, hb10, hdet', h2, mul_comm, mul_left_comm]
  all_goals ring

theorem Bsub_le_normalizer_Usub (K : Type) [Field K] [CharP K 2] :
    Bsub K ≤ Subgroup.normalizer (Usub K : Set (SL2 K)) := by
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro u
  constructor
  · intro hu
    obtain ⟨t, rfl⟩ := mem_Usub.mp hu
    exact conj_uU_mem_Usub hb t
  · intro hu
    obtain ⟨t, ht⟩ := mem_Usub.mp hu
    have h := conj_uU_mem_Usub (b := b⁻¹) ((Bsub K).inv_mem hb) t
    simpa [ht, mul_assoc] using h

theorem lU_inv {K : Type} [Field K] [CharP K 2] (c : K) :
    (lU c)⁻¹ = lU c := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two, coe_lU,
    Matrix.of_apply]
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h2, CharTwo.neg_eq]

theorem lU_conj_uU_one_not_mem_Usub {K : Type} [Field K] [CharP K 2] {c : K} (hc : c ≠ 0) :
    lU c * uU 1 * (lU c)⁻¹ ∉ Usub K := by
  intro h
  have hB : lU c * uU 1 * (lU c)⁻¹ ∈ Bsub K := by
    obtain ⟨t, ht⟩ := mem_Usub.mp h
    rw [← ht]
    exact uU_mem_Bsub t
  rw [mem_Bsub] at hB
  rw [lU_inv] at hB
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_lU, coe_uU,
    Matrix.mul_fin_two, Matrix.of_apply] at hB
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  simp [h2] at hB
  have h1 : (c + 1) * c = c ^ 2 + c := by ring
  rw [h1] at hB
  have hB2 : c ^ 2 + c * 2 = 0 := by
    calc c ^ 2 + c * 2 = c + (c ^ 2 + c) := by ring
    _ = 0 := hB
  have hc2 : c ^ 2 = 0 := by simpa [h2] using hB2
  exact hc (pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp hc2)

theorem normalizer_Usub_eq_Bsub (K : Type) [Field K] [CharP K 2] :
    Subgroup.normalizer (Usub K : Set (SL2 K)) = Bsub K := by
  refine le_antisymm ?_ (Bsub_le_normalizer_Usub K)
  intro g hg
  by_contra hgb
  have hc : (g : Matrix (Fin 2) (Fin 2) K) 1 0 ≠ 0 := fun h => hgb h
  have hxy := eq_uU_lU_uU g hc
  let N := Subgroup.normalizer (Usub K : Set (SL2 K))
  have huN : uU (((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) /
      (g : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ N :=
    Bsub_le_normalizer_Usub (K := K) (uU_mem_Bsub _)
  have huN' : uU (((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) /
      (g : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ N :=
    Bsub_le_normalizer_Usub (K := K) (uU_mem_Bsub _)
  have hprod : uU (((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0) * lU ((g : Matrix (Fin 2) (Fin 2) K) 1 0) *
      uU (((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ N := by
    rwa [← hxy]
  have hlN : lU ((g : Matrix (Fin 2) (Fin 2) K) 1 0) ∈ N := by
    have h1 : (uU (((g : Matrix (Fin 2) (Fin 2) K) 0 0 - 1) /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0))⁻¹ ∈ N := N.inv_mem huN
    have h2 : (uU (((g : Matrix (Fin 2) (Fin 2) K) 1 1 - 1) /
        (g : Matrix (Fin 2) (Fin 2) K) 1 0))⁻¹ ∈ N := N.inv_mem huN'
    have hm := N.mul_mem (N.mul_mem h1 hprod) h2
    convert hm using 1
    group
  exact lU_conj_uU_one_not_mem_Usub (K := K) hc
    ((Subgroup.mem_normalizer_iff.mp hlN (uU 1)).mp (uU_mem_Usub 1))

theorem uUHom_injective (K : Type) [Field K] : Function.Injective (uUHom K) := by
  intro s t h
  have h' := congrArg (fun x : SL2 K => (x : Matrix (Fin 2) (Fin 2) K) 0 1) h
  have h'' : Multiplicative.toAdd s = Multiplicative.toAdd t := by
    simpa only [show ((uUHom K s : SL2 K) :
        Matrix (Fin 2) (Fin 2) K) 0 1 = Multiplicative.toAdd s from rfl,
      show ((uUHom K t : SL2 K) :
        Matrix (Fin 2) (Fin 2) K) 0 1 = Multiplicative.toAdd t from rfl] using h'
  exact Multiplicative.toAdd.injective h''

theorem card_Usub (K : Type) [Field K] :
    Nat.card (Usub K) = Nat.card K := by
  let e : Multiplicative K ≃* Usub K :=
    MonoidHom.ofInjective (uUHom_injective K)
  calc Nat.card (Usub K) = Nat.card (Multiplicative K) :=
        (Nat.card_congr e.toEquiv).symm
    _ = Nat.card K := rfl

theorem card_sylow_eq_card_field (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (P : Sylow 2 (SL2 K)) :
    Nat.card P = Nat.card K := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨⟨n, hnpos⟩, _hp2, hcard⟩ := FiniteField.card K 2
  have hcardNat : Nat.card K = 2 ^ n := by
    rw [Nat.card_eq_fintype_card]
    simpa using hcard
  have hn2 : 2 ≤ n := by
    by_contra h
    have hnle : n ≤ 1 := by omega
    have hle : 2 ^ n ≤ 2 := by
      calc 2 ^ n ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) hnle
        _ = 2 := by norm_num
    rw [hcardNat] at hK
    omega
  have hfac : (Nat.card (SL2 K)).factorization 2 = n := by
    rw [CFSG.ClassicalInvolution.Disconnected.AschTight.S19C.card_sl2, hcardNat]
    have hodd : Odd ((2 ^ n) ^ 2 - 1) := by
      rw [show (2 ^ n) ^ 2 = 2 ^ (2 * n) by rw [← pow_mul]; ring_nf]
      exact CFSG.Timmesfeld.Orders.odd_two_pow_sub_one (by omega)
    have hpos : 0 < (2 ^ n) ^ 2 - 1 := by
      have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h16 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
      omega
    rw [Nat.factorization_mul (by positivity) hpos.ne']
    simp only [Finsupp.add_apply]
    rw [Nat.factorization_pow_self Nat.prime_two]
    have hz : ((2 ^ n) ^ 2 - 1).factorization 2 = 0 :=
      Nat.factorization_eq_zero_of_not_dvd (by
        intro hd
        exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hd))
    rw [hz, add_zero]
  rw [Sylow.card_eq_multiplicity P, hfac, hcardNat]


theorem exists_ne_zero_ne_one {K : Type} [Field K] [Finite K] (hK : 4 ≤ Nat.card K) :
    ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
  classical
  by_contra hne
  push Not at hne
  have hsub : (Set.univ : Set K) ⊆ ({0, 1} : Set K) := by
    intro a _
    by_cases ha : a = 0
    · simp [ha]
    · have ha1 : a = 1 := by simpa using hne a ha
      simp [ha1]
  have hle : Nat.card K ≤ 2 := by
    calc Nat.card K = (Set.univ : Set K).ncard := by simp
      _ ≤ ({0, 1} : Set K).ncard := Set.ncard_le_ncard hsub
      _ ≤ 2 := by simp
  omega

theorem coe_dD {K : Type} [Field K] (a : K) (ha : a ≠ 0) :
    ((dD a ha : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![a, 0; 0, a⁻¹] := rfl

theorem dD_mem_Bsub {K : Type} [Field K] (a : K) (ha : a ≠ 0) : dD a ha ∈ Bsub K := by
  rw [mem_Bsub]
  simp [dD]

theorem dD_mul_uU_mul_inv {K : Type} [Field K] [CharP K 2] (a : K) (ha : a ≠ 0) (s : K) :
    dD a ha * uU s * (dD a ha)⁻¹ = uU (a ^ 2 * s) := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv,
    Matrix.adjugate_fin_two, coe_uU, coe_dD, Matrix.of_apply]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

theorem commutator_dD_uU {K : Type} [Field K] [CharP K 2] (a : K) (ha : a ≠ 0) (s : K) :
    ⁅dD a ha, uU s⁆ = uU ((a ^ 2 + 1) * s) := by
  rw [commutatorElement_def, dD_mul_uU_mul_inv a ha]
  have hu : (uU s)⁻¹ = uU s := inv_eq_of_mul_eq_one_right (uU_sq s)
  rw [hu, uU_mul]
  congr 1
  ring

theorem uU_mem_comm {K : Type} [Field K] [CharP K 2] (a : K) (ha : a ≠ 0)
    (ha2 : a ^ 2 + 1 ≠ 0) (t : K) :
    uU t ∈ ⁅(⊤ : Subgroup (SL2 K)), Bsub K⁆ := by
  have h := Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup (SL2 K)))
    (H₂ := Bsub K) (g₁ := dD a ha) (g₂ := uU (t / (a ^ 2 + 1)))
    (Subgroup.mem_top _) (dD_mem_Bsub a ha)
  rwa [commutator_dD_uU, mul_div_cancel₀ _ ha2] at h

theorem lU_mem_comm {K : Type} [Field K] [CharP K 2] (a : K) (ha : a ≠ 0)
    (ha2 : a ^ 2 + 1 ≠ 0) (t : K) :
    lU t ∈ ⁅(⊤ : Subgroup (SL2 K)), Bsub K⁆ := by
  have hcomm : ⁅wW K, uU t⁆ ∈ ⁅(⊤ : Subgroup (SL2 K)), Bsub K⁆ :=
    Subgroup.commutator_mem_commutator (H₁ := (⊤ : Subgroup (SL2 K))) (H₂ := Bsub K)
      (g₁ := wW K) (g₂ := uU t) (Subgroup.mem_top _) (uU_mem_Bsub t)
  have hcalc : ⁅wW K, uU t⁆ = lU t * uU t := by
    rw [commutatorElement_def, wW_mul_uU_mul_inv]
    rw [show -t = t by exact CharTwo.neg_eq t]
    have hu : (uU t)⁻¹ = uU t := inv_eq_of_mul_eq_one_right (uU_sq t)
    rw [hu]
  have hu := uU_mem_comm a ha ha2 t
  have heq : lU t = ⁅wW K, uU t⁆ * uU t := by rw [hcalc, mul_assoc, uU_sq, mul_one]
  rw [heq]
  exact Subgroup.mul_mem _ hcomm hu

theorem commutator_top_Bsub (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) :
    ⁅(⊤ : Subgroup (SL2 K)), Bsub K⁆ = ⊤ := by
  obtain ⟨a, ha0, ha1⟩ := exists_ne_zero_ne_one (K := K) hK
  have ha2 : a ^ 2 ≠ 1 := by
    intro h
    apply ha1
    have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
    have h1 : (a - 1) ^ 2 = 0 := by
      rw [sub_sq, h, one_pow]
      ring_nf
      rw [h2]
      ring
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num : 2 ≠ 0) |>.mp h1)
  have ha2' : a ^ 2 + 1 ≠ 0 := by
    intro h
    apply ha2
    have hh : a ^ 2 - 1 = 0 := by
      simpa [sub_eq_add_neg, CharTwo.neg_eq] using h
    exact sub_eq_zero.mp hh
  apply le_antisymm le_top
  intro x _
  exact mem_of_uU_lU (fun t => uU_mem_comm a ha0 ha2' t)
    (fun t => lU_mem_comm a ha0 ha2' t) x

theorem exists_conj_eq_Usub (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (P : Sylow 2 (SL2 K)) :
    ∃ g : SL2 K, (P : Subgroup (SL2 K)) =
      (Usub K).map (MulAut.conj g⁻¹).toMonoidHom := by
  obtain ⟨g, hg⟩ := CFSG.LieType.BorelTits.exists_conj_mem_sylow P (Usub_isPGroup K)
  let f : SL2 K ≃* SL2 K := MulAut.conj g⁻¹
  have hPmap : (Usub K).map f.toMonoidHom ≤ (P : Subgroup (SL2 K)) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [f, MulAut.conj_apply] using hg u hu
  have hcardU : Nat.card ((Usub K).map f.toMonoidHom) =
      Nat.card (P : Subgroup (SL2 K)) := by
    rw [Subgroup.card_map_of_injective f.injective, card_Usub,
      card_sylow_eq_card_field (K := K) hK P]
  refine ⟨g, ?_⟩
  refine (Subgroup.eq_of_le_of_card_ge hPmap ?_).symm
  rw [hcardU]

theorem commutator_top_normalizer_sylow_eq_top (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (P : Sylow 2 (SL2 K)) :
    ⁅(⊤ : Subgroup (SL2 K)), Subgroup.normalizer (P : Set (SL2 K))⁆ = ⊤ := by
  obtain ⟨g, hP⟩ := exists_conj_eq_Usub (K := K) hK P
  let f : SL2 K ≃* SL2 K := MulAut.conj g⁻¹
  have hN : Subgroup.normalizer (P : Set (SL2 K)) =
      (Subgroup.normalizer (Usub K : Set (SL2 K))).map f.toMonoidHom := by
    change Subgroup.normalizer ((P : Subgroup (SL2 K)) : Set (SL2 K)) =
      (Subgroup.normalizer (Usub K : Set (SL2 K))).map f.toMonoidHom
    rw [show (P : Subgroup (SL2 K)) = (Usub K).map f.toMonoidHom from hP]
    exact (Subgroup.map_equiv_normalizer_eq (Usub K) f).symm
  rw [hN, normalizer_Usub_eq_Bsub]
  rw [show (⊤ : Subgroup (SL2 K)) = (⊤ : Subgroup (SL2 K)).map f.toMonoidHom by
        rw [Subgroup.map_top_of_surjective f.toMonoidHom f.surjective]]
  rw [← Subgroup.map_commutator, commutator_top_Bsub K hK,
    Subgroup.map_top_of_surjective f.toMonoidHom f.surjective]

theorem nonempty_mulEquiv_sl2_of_isL2 {X : Type} [Group X] {m : ℕ} (hX : IsL2 X m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ m ∧
      Nonempty (X ≃* SL2 K) := by
  obtain ⟨K, hField, hFinite, hKcard, ⟨eSL⟩⟩ := nonempty_mulEquiv_statedSL_two_of_isL2 hX
  exact ⟨K, hField, hFinite, hKcard,
    ⟨eSL.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm⟩⟩

theorem commutator_top_normalizer_eq_top {X : Type} [Group X] [Finite X] {m : ℕ}
    (hm : 2 ≤ m) (hX : IsL2 X m) (S : Sylow 2 X) :
    ⁅(⊤ : Subgroup X), Subgroup.normalizer (S : Set X)⁆ = ⊤ := by
  obtain ⟨K, hField, hFinite, hKcard, ⟨e⟩⟩ := nonempty_mulEquiv_sl2_of_isL2 hX
  letI : Field K := hField
  letI : Finite K := hFinite
  haveI : CharP K 2 := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_charP_two
    (by omega) hKcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  let P : Sylow 2 (SL2 K) := Sylow.mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective S
  have hN : Subgroup.normalizer (P : Set (SL2 K)) =
      (Subgroup.normalizer (S : Set X)).map e.toMonoidHom := by
    change Subgroup.normalizer ((P : Subgroup (SL2 K)) : Set (SL2 K)) =
      (Subgroup.normalizer ((S : Subgroup X) : Set X)).map e.toMonoidHom
    rw [show (P : Subgroup (SL2 K)) = (S : Subgroup X).map e.toMonoidHom from rfl]
    exact (Subgroup.map_equiv_normalizer_eq (S : Subgroup X) e).symm
  have hmap : (⁅(⊤ : Subgroup X), Subgroup.normalizer (S : Set X)⁆).map e.toMonoidHom =
      ⁅(⊤ : Subgroup (SL2 K)), Subgroup.normalizer (P : Set (SL2 K))⁆ := by
    rw [Subgroup.map_commutator, hN, Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  have htop := commutator_top_normalizer_sylow_eq_top K hK4 P
  have hout : (⁅(⊤ : Subgroup X), Subgroup.normalizer (S : Set X)⁆).map e.toMonoidHom = ⊤ := by
    rw [hmap, htop]
  refine Subgroup.map_injective (f := e.toMonoidHom) e.injective ?_
  rw [Subgroup.map_top_of_surjective e.toMonoidHom e.surjective]
  exact hout

theorem sl2_sylow_le_normalizer (K : Type) [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (P : Sylow 2 (SL2 K)) :
    ∀ H : Subgroup (SL2 K), (P : Subgroup (SL2 K)) ≤ H → H ≠ ⊤ →
      H ≤ Subgroup.normalizer (P : Set (SL2 K)) := by
  intro H hPH hHtop
  obtain ⟨g, hg⟩ := CFSG.LieType.BorelTits.exists_conj_mem_sylow P (Usub_isPGroup K)
  let f : SL2 K ≃* SL2 K := MulAut.conj g⁻¹
  have hPmap : (Usub K).map f.toMonoidHom ≤ (P : Subgroup (SL2 K)) := by
    intro x hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    simpa [f, MulAut.conj_apply] using hg u hu
  have hcardU : Nat.card ((Usub K).map f.toMonoidHom) =
      Nat.card (P : Subgroup (SL2 K)) := by
    rw [Subgroup.card_map_of_injective f.injective, card_Usub,
      card_sylow_eq_card_field (K := K) hK P]
  have hP_eq : (P : Subgroup (SL2 K)) = (Usub K).map f.toMonoidHom := by
    refine (Subgroup.eq_of_le_of_card_ge hPmap ?_).symm
    rw [hcardU]
  have hcomp : f.toMonoidHom.comp f.symm.toMonoidHom = MonoidHom.id (SL2 K) :=
    MulEquiv.toMonoidHom_comp_toMonoidHom_symm f
  have hcancelH : (H.map f.symm.toMonoidHom).map f.toMonoidHom = H := by
    rw [Subgroup.map_map, hcomp, Subgroup.map_id]
  have hcomp' : f.symm.toMonoidHom.comp f.toMonoidHom = MonoidHom.id (SL2 K) :=
    MulEquiv.toMonoidHom_symm_comp_toMonoidHom f
  have hUP : Usub K ≤ H.map f.symm.toMonoidHom := by
    calc Usub K =
          ((Usub K).map f.toMonoidHom).map f.symm.toMonoidHom := by
          rw [Subgroup.map_map, hcomp', Subgroup.map_id]
      _ ≤ H.map f.symm.toMonoidHom := Subgroup.map_mono (hPmap.trans hPH)
  have hbor := borel_or_top (K := K) (H := H.map f.symm.toMonoidHom)
    (fun t => hUP (uU_mem_Usub t))
  have hN : Subgroup.normalizer (P : Set (SL2 K)) =
      (Subgroup.normalizer (Usub K : Set (SL2 K))).map f.toMonoidHom := by
    change Subgroup.normalizer ((P : Subgroup (SL2 K)) : Set (SL2 K)) =
      (Subgroup.normalizer (Usub K : Set (SL2 K))).map f.toMonoidHom
    rw [show (P : Subgroup (SL2 K)) = (Usub K).map f.toMonoidHom from hP_eq]
    exact (Subgroup.map_equiv_normalizer_eq (Usub K) f).symm
  rw [normalizer_Usub_eq_Bsub] at hN
  rcases hbor with hle | htop
  · have hle' : H.map f.symm.toMonoidHom ≤ Bsub K := hle
    have hHle : H ≤ (Bsub K).map f.toMonoidHom := by
      calc H = (H.map f.symm.toMonoidHom).map f.toMonoidHom := hcancelH.symm
        _ ≤ (Bsub K).map f.toMonoidHom := Subgroup.map_mono hle'
    rwa [hN]
  · exfalso
    apply hHtop
    have h := congrArg (Subgroup.map f.toMonoidHom) htop
    rw [hcancelH, Subgroup.map_top_of_surjective f.toMonoidHom f.surjective] at h
    exact h

theorem l2_sylow_le_normalizer {X : Type} [Group X] [Finite X] {m : ℕ} (hm : 2 ≤ m)
    (hX : IsL2 X m) (B : Sylow 2 X) :
    ∀ P : Subgroup X, (B : Subgroup X) ≤ P → P ≠ ⊤ →
      P ≤ Subgroup.normalizer (B : Set X) := by
  obtain ⟨K, hField, hFinite, hKcard, ⟨eSL⟩⟩ := nonempty_mulEquiv_statedSL_two_of_isL2 hX
  letI : Field K := hField
  letI : Finite K := hFinite
  let e : X ≃* SL2 K := eSL.trans
    (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  haveI : CharP K 2 := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_charP_two
    (by omega) hKcard
  have hK4 : 4 ≤ Nat.card K := by
    rw [hKcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
  let P : Sylow 2 (SL2 K) := Sylow.mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective B
  intro Q hBQ hQtop
  have hPQ : (P : Subgroup (SL2 K)) ≤ Q.map e.toMonoidHom := by
    change (B : Subgroup X).map e.toMonoidHom ≤ Q.map e.toMonoidHom
    exact Subgroup.map_mono hBQ
  have hQmap_ne : Q.map e.toMonoidHom ≠ ⊤ := by
    intro htop
    apply hQtop
    rw [eq_top_iff]
    intro x _
    have hx : e x ∈ Q.map e.toMonoidHom := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨q, hq, hqx⟩ := Subgroup.mem_map.mp hx
    have hqx' : q = x := e.injective hqx
    simpa [hqx'] using hq
  have hle := sl2_sylow_le_normalizer (K := K) hK4 P (Q.map e.toMonoidHom) hPQ hQmap_ne
  have hN : Subgroup.normalizer (P : Set (SL2 K)) =
      (Subgroup.normalizer ((B : Subgroup X) : Set X)).map e.toMonoidHom := by
    change Subgroup.normalizer ((P : Subgroup (SL2 K)) : Set (SL2 K)) =
      (Subgroup.normalizer ((B : Subgroup X) : Set X)).map e.toMonoidHom
    rw [show (P : Subgroup (SL2 K)) = (B : Subgroup X).map e.toMonoidHom from rfl,
      ← Subgroup.map_equiv_normalizer_eq]
  rw [hN] at hle
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id X :=
    MulEquiv.toMonoidHom_symm_comp_toMonoidHom e
  calc Q = (Q.map e.toMonoidHom).map e.symm.toMonoidHom := by
        rw [Subgroup.map_map, hcomp, Subgroup.map_id]
    _ ≤ ((Subgroup.normalizer (B : Set X)).map e.toMonoidHom).map e.symm.toMonoidHom :=
        Subgroup.map_mono hle
    _ = Subgroup.normalizer (B : Set X) := by
        rw [Subgroup.map_map, hcomp, Subgroup.map_id]

theorem normalizer_sylow_le_stabilizer_fixedPointSubgroup
    {W : Type} [CommGroup W] [Finite W] (H : Subgroup (MulAut W)) (S : Sylow 2 ↥H) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    Subgroup.normalizer (S : Set ↥H) ≤
      MulAction.stabilizer ↥H (CFSG.fixedPointSubgroup ↥S W : Set W) := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  let C : Subgroup W := CFSG.fixedPointSubgroup ↥S W
  have hsmul : ∀ y : ↥H, y ∈ Subgroup.normalizer (S : Set ↥H) → ∀ v : W, v ∈ C →
      y • v ∈ C := by
    intro y hy v hv s
    change (s : ↥H) • (y • v) = y • v
    have hmem : y⁻¹ * (s : ↥H) * y ∈ (S : Subgroup ↥H) :=
      (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (S : Set ↥H)).inv_mem hy) (s : ↥H)).mp s.2
    have hv' : ((⟨y⁻¹ * (s : ↥H) * y, hmem⟩ : ↥S)) • v = v :=
      hv ⟨y⁻¹ * (s : ↥H) * y, hmem⟩
    change (y⁻¹ * (s : ↥H) * y) • v = v at hv'
    calc (s : ↥H) • (y • v) = ((s : ↥H) * y) • v := by rw [mul_smul]
      _ = (y * (y⁻¹ * (s : ↥H) * y)) • v := by
          rw [show (s : ↥H) * y = y * (y⁻¹ * (s : ↥H) * y) by group]
      _ = y • ((y⁻¹ * (s : ↥H) * y) • v) := by rw [mul_smul]
      _ = y • v := by rw [hv']
  intro x hx
  rw [MulAction.mem_stabilizer_iff]
  ext w
  rw [Set.mem_smul_set_iff_inv_smul_mem]
  constructor
  · intro hw
    have h := hsmul x hx (x⁻¹ • w) hw
    rwa [smul_inv_smul] at h
  · intro hw
    exact hsmul x⁻¹ ((Subgroup.normalizer (S : Set ↥H)).inv_mem hx) w hw



theorem normalizer_prod_eq {A B : Type} [Group A] [Group B]
    (S : Subgroup A) (T : Subgroup B) :
    Subgroup.normalizer (S.prod T : Set (A × B)) =
      (Subgroup.normalizer (S : Set A)).prod (Subgroup.normalizer (T : Set B)) := by
  ext x
  rw [Subgroup.mem_prod]
  constructor
  · intro hx
    rw [Subgroup.mem_normalizer_iff] at hx
    constructor
    · rw [Subgroup.mem_normalizer_iff]
      intro s
      constructor
      · intro hs
        have h2 := (hx (s, 1)).mp (Subgroup.mem_prod.mpr ⟨hs, Subgroup.one_mem T⟩)
        exact (Subgroup.mem_prod.mp h2).1
      · intro hs
        have h2 : x * (s, 1) * x⁻¹ ∈ S.prod T :=
          Subgroup.mem_prod.mpr ⟨hs, by simpa using Subgroup.one_mem T⟩
        exact (Subgroup.mem_prod.mp ((hx (s, 1)).mpr h2)).1
    · rw [Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · intro ht
        have h2 := (hx (1, t)).mp (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem S, ht⟩)
        exact (Subgroup.mem_prod.mp h2).2
      · intro ht
        have h2 : x * (1, t) * x⁻¹ ∈ S.prod T :=
          Subgroup.mem_prod.mpr ⟨by simpa using Subgroup.one_mem S, ht⟩
        exact (Subgroup.mem_prod.mp ((hx (1, t)).mpr h2)).2
  · rintro ⟨ha, hb⟩
    rw [Subgroup.mem_normalizer_iff]
    intro p
    constructor
    · intro hp
      obtain ⟨s, t⟩ := p
      obtain ⟨hs, ht⟩ := Subgroup.mem_prod.mp hp
      exact Subgroup.mem_prod.mpr ⟨(ha s).mp hs, (hb t).mp ht⟩
    · intro hp
      obtain ⟨s, t⟩ := p
      obtain ⟨hs, ht⟩ := Subgroup.mem_prod.mp hp
      exact Subgroup.mem_prod.mpr ⟨(ha s).mpr hs, (hb t).mpr ht⟩

theorem sylow_prod_eq {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    (S : Sylow 2 (A × B)) :
    ∃ SA : Sylow 2 A, ∃ SB : Sylow 2 B,
      (S : Subgroup (A × B)) = (SA : Subgroup A).prod (SB : Subgroup B) := by
  let PA : Subgroup A := (S : Subgroup (A × B)).map (MonoidHom.fst A B)
  let PB : Subgroup B := (S : Subgroup (A × B)).map (MonoidHom.snd A B)
  have hPAp : IsPGroup 2 PA := S.isPGroup'.map _
  have hPBp : IsPGroup 2 PB := S.isPGroup'.map _
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hPAp
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hPBp
  have hSle : (S : Subgroup (A × B)) ≤ PA.prod PB := by
    intro x hx
    exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_map_of_mem _ hx, Subgroup.mem_map_of_mem _ hx⟩
  have hcardS : Nat.card (S : Subgroup (A × B)) =
      2 ^ (Nat.card (A × B)).factorization 2 := by
    simpa using S.card_eq_multiplicity
  have hcardAB : (Nat.card (A × B)).factorization 2 =
      (Nat.card A).factorization 2 + (Nat.card B).factorization 2 := by
    rw [Nat.card_prod, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne')]
    rfl
  have hcardProd : Nat.card (PA.prod PB) = Nat.card PA * Nat.card PB := by
    rw [Nat.card_congr (Subgroup.prodEquiv PA PB).toEquiv, Nat.card_prod]
  have hcard_le : 2 ^ ((Nat.card A).factorization 2 + (Nat.card B).factorization 2) ≤
      2 ^ (a + b) := by
    calc 2 ^ ((Nat.card A).factorization 2 + (Nat.card B).factorization 2)
        = Nat.card (S : Subgroup (A × B)) := by rw [hcardS, hcardAB]
      _ ≤ Nat.card (PA.prod PB) := Subgroup.card_le_of_le hSle
      _ = Nat.card PA * Nat.card PB := hcardProd
      _ = 2 ^ a * 2 ^ b := by rw [ha, hb]
      _ = 2 ^ (a + b) := by rw [← pow_add]
  have hab : (Nat.card A).factorization 2 + (Nat.card B).factorization 2 ≤ a + b :=
    (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp hcard_le
  have hdivA : 2 ^ a ∣ Nat.card A := by
    rw [← ha]
    simpa using Subgroup.card_dvd_of_le (H := PA) (K := ⊤) le_top
  have hdivB : 2 ^ b ∣ Nat.card B := by
    rw [← hb]
    simpa using Subgroup.card_dvd_of_le (H := PB) (K := ⊤) le_top
  have ha_le : a ≤ (Nat.card A).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp hdivA
  have hb_le : b ≤ (Nat.card B).factorization 2 :=
    (Nat.prime_two.pow_dvd_iff_le_factorization (Nat.card_pos.ne')).mp hdivB
  have hav : a = (Nat.card A).factorization 2 := by omega
  have hbv : b = (Nat.card B).factorization 2 := by omega
  let SA : Sylow 2 A := Sylow.ofCard PA (by rw [ha, hav])
  let SB : Sylow 2 B := Sylow.ofCard PB (by rw [hb, hbv])
  refine ⟨SA, SB, ?_⟩
  have hcoeA : (SA : Subgroup A) = PA := Sylow.coe_ofCard PA _
  have hcoeB : (SB : Subgroup B) = PB := Sylow.coe_ofCard PB _
  rw [hcoeA, hcoeB]
  refine Subgroup.eq_of_le_of_card_ge hSle ?_
  rw [hcardProd, ha, hb, hav, hbv, ← pow_add, hcardS, hcardAB]

theorem sylow_eq_of_le_normalizer {A : Type} [Group A] [Finite A]
    (TA SA : Sylow 2 A) (hle : (SA : Subgroup A) ≤ Subgroup.normalizer (TA : Set A)) :
    SA = TA := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N := Subgroup.normalizer (TA : Set A)
  have hTA : (TA : Subgroup A) ≤ N := Subgroup.le_normalizer
  have hNorm : (TA.subtype hTA).Normal := by
    rw [Sylow.coe_subtype]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hTA).mpr le_rfl
  letI : Unique (Sylow 2 N) := Sylow.unique_of_normal (TA.subtype hTA) hNorm
  have hEq : SA.subtype hle = TA.subtype hTA := Subsingleton.elim _ _
  have hsub : (SA.subtype hle : Subgroup N) = (TA.subtype hTA : Subgroup N) :=
    congrArg (fun S : Sylow 2 N => (S : Subgroup N)) hEq
  have hmap := congrArg (Subgroup.map N.subtype) hsub
  rw [Sylow.coe_subtype, Sylow.coe_subtype, Subgroup.subgroupOf_map_subtype,
    Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hle, inf_eq_left.mpr hTA] at hmap
  exact Sylow.ext hmap

theorem firstFactor_le_of_proj_eq_top_of_snd_le {A B : Type} [Group A] [Group B]
    (P : Subgroup (A × B)) (R : Subgroup A) (S : Subgroup B)
    (hP : R.prod S ≤ P)
    (hA : P.map (MonoidHom.fst A B) = ⊤)
    (hB : P.map (MonoidHom.snd A B) ≤ S) :
    (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ P := by
  intro x hx
  obtain ⟨a, b⟩ := x
  obtain ⟨-, hb⟩ := Subgroup.mem_prod.mp hx
  have hb1 : b = 1 := Subgroup.mem_bot.mp hb
  subst hb1
  have ha : a ∈ P.map (MonoidHom.fst A B) := by rw [hA]; exact Subgroup.mem_top a
  obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp ha
  obtain ⟨a', b'⟩ := p
  have ha' : a' = a := hpa
  subst a'
  have hbS : b' ∈ S := hB (Subgroup.mem_map_of_mem (MonoidHom.snd A B) hp)
  have h1binv : (1, b'⁻¹) ∈ P :=
    hP (Subgroup.mem_prod.mpr ⟨Subgroup.one_mem R, S.inv_mem hbS⟩)
  have hmul := P.mul_mem hp h1binv
  simpa using hmul

theorem firstFactor_le_of_proj_eq_top {A B : Type} [Group A] [Group B]
    (P : Subgroup (A × B)) (R : Subgroup A) (S : Subgroup B)
    (hP : R.prod S ≤ P)
    (hA : P.map (MonoidHom.fst A B) = ⊤)
    (hB : P.map (MonoidHom.snd A B) = ⊤)
    (hcomm : ⁅(⊤ : Subgroup A), R⁆ = ⊤) :
    (⊤ : Subgroup A).prod (⊥ : Subgroup B) ≤ P := by
  letI : Bracket A A := commutatorElement
  letI : Bracket (A × B) (A × B) := commutatorElement
  let R' : Subgroup A := (P ⊓ ((⊤ : Subgroup A).prod (⊥ : Subgroup B))).map
    (MonoidHom.fst A B)
  have hcomm_le : ⁅(⊤ : Subgroup A), R⁆ ≤ R' := by
    rw [Subgroup.commutator_le]
    intro a _ r hr
    obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp (by rw [hA]; exact Subgroup.mem_top a)
    obtain ⟨a', b⟩ := p
    have ha' : a' = a := hpa
    subst a'
    have hr1 : (r, 1) ∈ P := hP (Subgroup.mem_prod.mpr ⟨hr, Subgroup.one_mem S⟩)
    have hcommp : ⁅(a, b), (r, 1)⁆ ∈ P := by
      rw [commutatorElement_def]
      exact P.mul_mem (P.mul_mem (P.mul_mem hp hr1) (P.inv_mem hp)) (P.inv_mem hr1)
    have hsecond : (⁅(a, b), (r, 1)⁆ : A × B).2 = 1 := by
      simp [commutatorElement_def]
    have hmem : ⁅(a, b), (r, 1)⁆ ∈ P ⊓ ((⊤ : Subgroup A).prod (⊥ : Subgroup B)) := by
      refine Subgroup.mem_inf.mpr ⟨hcommp, ?_⟩
      exact Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, by simpa using hsecond⟩
    have hfst : (⁅(a, b), (r, 1)⁆ : A × B).1 = ⁅a, r⁆ := by
      simp [commutatorElement_def]
    have hfst_mem : (⁅(a, b), (r, 1)⁆ : A × B).1 ∈ R' :=
      Subgroup.mem_map_of_mem (MonoidHom.fst A B) hmem
    rwa [hfst] at hfst_mem
  have hR' : R' = ⊤ := le_antisymm le_top (hcomm ▸ hcomm_le)
  intro x hx
  obtain ⟨a, b⟩ := x
  obtain ⟨-, hb⟩ := Subgroup.mem_prod.mp hx
  subst hb
  have ha : a ∈ R' := by rw [hR']; exact Subgroup.mem_top a
  obtain ⟨p, hp, hpa⟩ := Subgroup.mem_map.mp ha
  obtain ⟨a', b'⟩ := p
  have ha' : a' = a := hpa
  subst a'
  have hp' := Subgroup.mem_inf.mp hp
  have hb' : b' = 1 := Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hp'.2).2
  subst b'
  simpa using hp'.1


theorem secondFactor_le_of_proj_eq_top_of_fst_le {A B : Type} [Group A] [Group B]
    (P : Subgroup (A × B)) (R : Subgroup A) (S : Subgroup B)
    (hP : R.prod S ≤ P)
    (hB : P.map (MonoidHom.snd A B) = ⊤)
    (hA : P.map (MonoidHom.fst A B) ≤ R) :
    (⊥ : Subgroup A).prod (⊤ : Subgroup B) ≤ P := by
  intro x hx
  obtain ⟨a, b⟩ := x
  obtain ⟨ha, -⟩ := Subgroup.mem_prod.mp hx
  have ha1 : a = 1 := Subgroup.mem_bot.mp ha
  subst ha1
  have hb : b ∈ P.map (MonoidHom.snd A B) := by rw [hB]; exact Subgroup.mem_top b
  obtain ⟨p, hp, hpb⟩ := Subgroup.mem_map.mp hb
  obtain ⟨a', b'⟩ := p
  have hb' : b' = b := hpb
  subst b'
  have haR : a' ∈ R := hA (Subgroup.mem_map_of_mem (MonoidHom.fst A B) hp)
  have h1a : (a'⁻¹, 1) ∈ P :=
    hP (Subgroup.mem_prod.mpr ⟨R.inv_mem haR, Subgroup.one_mem S⟩)
  have hmul := P.mul_mem h1a hp
  simpa using hmul

theorem map_conj_eq_of_normalizerMonoidHom_map_eq
    {W : Type} [CommGroup W] (H : Subgroup (MulAut W)) {t : MulAut W}
    (ht : t ∈ Subgroup.normalizer (H : Set (MulAut W))) {N N' : Subgroup ↥H}
    (h : N.map (H.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom = N') :
    (N.map H.subtype).map (MulAut.conj t).toMonoidHom = N'.map H.subtype := by
  have hcomp : (MulAut.conj t).toMonoidHom.comp H.subtype =
      H.subtype.comp (H.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom := by
    ext x w
    change (MulAut.conj t (x : MulAut W)) w =
      (((H.normalizerMonoidHom ⟨t, ht⟩ x : ↥H) : MulAut W)) w
    rw [MulAut.conj_apply]
    simpa using congrFun (Subgroup.normalizerMonoidHom_apply_apply_coe H ⟨t, ht⟩ x).symm w
  calc (N.map H.subtype).map (MulAut.conj t).toMonoidHom
      = N.map ((MulAut.conj t).toMonoidHom.comp H.subtype) := by rw [Subgroup.map_map]
    _ = N.map (H.subtype.comp (H.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom) := by rw [hcomp]
    _ = (N.map (H.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom).map H.subtype := by rw [Subgroup.map_map]
    _ = N'.map H.subtype := by rw [h]

theorem kTab23b_OmegaMinus_line_uncond (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsOmegaMinus ↥H 4 n ∧ NatOmegaMinus H ⊤ ⊥ 4 n) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    ∀ S : Sylow 2 ↥H,
      letI : MulDistribMulAction ↥S W :=
        MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      let ℓ : Subgroup W := fixedPointSubgroup ↥S W
      let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
      ∀ Tstar : Subgroup (MulAut W),
        Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
        IsPGroup 2 ↥Tstar →
        (S : Subgroup ↥H).map H.subtype ≤ Tstar →
        let Good : Subgroup ↥H → Prop := fun Pstar =>
          IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
          (∀ t ∈ Tstar,
            (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
          ¬ Pstar ≤ Pℓ
        ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
          Pstar = ⊤ ∧ IsL2 (Bar2 (Hinf Pstar)) (2 * n) := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  intro S
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  let ℓ : Subgroup W := fixedPointSubgroup ↥S W
  let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
  dsimp only
  intro Tstar hTnorm hT2 hST
  let Good : Subgroup ↥H → Prop := fun Pstar =>
    IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
    (∀ t ∈ Tstar,
      (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
    ¬ Pstar ≤ Pℓ
  intro Pstar hmin
  have hn1 : 1 ≤ n := by
    obtain ⟨-, K, hKfield, hKfin, b, c, hKcard, -, -⟩ := hline.1
    letI : Field K := hKfield
    letI : Finite K := hKfin
    have hKgt : 1 < Nat.card K := Finite.one_lt_card_iff_nontrivial.mpr inferInstance
    rw [hKcard] at hKgt
    exact Nat.one_le_iff_ne_zero.mpr (Nat.one_lt_two_pow_iff.mp hKgt)
  have hL2 : IsL2 ↥H (2 * n) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.isL2_of_isOmegaMinus_four hn1 hline.1
  have htop : Pstar = ⊤ := by
    by_contra hne
    have hgood : Good Pstar := hmin.1
    have hle := l2_sylow_le_normalizer (m := 2 * n) (by omega) hL2 S Pstar hgood.2.1 hne
    have hstab := normalizer_sylow_le_stabilizer_fixedPointSubgroup H S
    exact hgood.2.2.2 (hle.trans hstab)
  refine ⟨htop, ?_⟩
  have hperfH : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hperf
  have hHinf : Hinf (⊤ : Subgroup ↥H) = ⊤ := Hinf_top_eq_top_of_perfect hperfH
  have hpCore : CFSG.pCore 2 ↥H = ⊥ := pCore_eq_bot_of_isL2 hL2
  obtain ⟨eBar⟩ := nonempty_bar2_top_mulEquiv_of_pCore_eq_bot hpCore
  have hL2bar : IsL2 (Bar2 (⊤ : Subgroup ↥H)) (2 * n) :=
    CFSG.Blueprint.LieModel.of_mulEquiv eBar.symm hL2
  rw [htop, hHinf]
  exact hL2bar

theorem kTab23b_OmegaPlus_line_uncond (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsOmegaPlus ↥H 4 n ∧ NatOmegaPlus H ⊤ ⊥ 4 n) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    ∀ S : Sylow 2 ↥H,
      letI : MulDistribMulAction ↥S W :=
        MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      let ℓ : Subgroup W := fixedPointSubgroup ↥S W
      let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
      ∀ Tstar : Subgroup (MulAut W),
        Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
        IsPGroup 2 ↥Tstar →
        (S : Subgroup ↥H).map H.subtype ≤ Tstar →
        let Good : Subgroup ↥H → Prop := fun Pstar =>
          IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
          (∀ t ∈ Tstar,
            (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
          ¬ Pstar ≤ Pℓ
        ((∀ N : Subgroup ↥H, N.Normal →
            (∀ t ∈ Tstar,
              (N.map H.subtype).map (MulAut.conj t).toMonoidHom = N.map H.subtype) →
            N ≠ ⊤ → N ≤ Subgroup.center ↥H) →
          ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
            Pstar = ⊤ ∧ IsL2Square (Bar2 (Hinf Pstar)) n) := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  intro S
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  let ℓ : Subgroup W := fixedPointSubgroup ↥S W
  let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
  dsimp only
  intro Tstar hTnorm hT2 hST
  let Good : Subgroup ↥H → Prop := fun Pstar =>
    IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
    (∀ t ∈ Tstar,
      (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
    ¬ Pstar ≤ Pℓ
  intro hnormal Pstar hmin
  have hgood : Good Pstar := hmin.1
  have hperfH : Group.IsPerfect ↥H := Subgroup.isPerfect_iff.mpr hperf
  have hntH : Nontrivial ↥H :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.nontrivial_of_isOmegaPlus_four hline.1
  have hn2 : 2 ≤ n :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S18.two_le_of_isOmegaPlus_four_of_perfect
      hline.1 hperfH hntH
  have hL2Sq : IsL2Square ↥H n := isL2Square_of_isOmegaPlus hn2 hline.1
  obtain ⟨A, B, hAg, hBg, ⟨eAB⟩, hLA, hLB⟩ := hL2Sq
  letI : Group A := hAg
  letI : Group B := hBg
  haveI : Finite (A × B) := Finite.of_injective (eAB.symm : A × B → ↥H) eAB.symm.injective
  haveI : Finite A := Finite.of_surjective (MonoidHom.fst A B) (fun a => ⟨(a, 1), rfl⟩)
  haveI : Finite B := Finite.of_surjective (MonoidHom.snd A B) (fun b => ⟨(1, b), rfl⟩)
  have hSA : StatedClassicalModel A .PSL 2 2 n :=
    (isL2_iff_statedClassicalModel (X := A) (a := n)).mp hLA
  have hSB : StatedClassicalModel B .PSL 2 2 n :=
    (isL2_iff_statedClassicalModel (X := B) (a := n)).mp hLB
  obtain ⟨eBA⟩ := CFSG.Blueprint.EvenSource.nonempty_mulEquiv_of_statedClassicalModel hSB hSA
  let e : ↥H ≃* A × A := eAB.trans (MulEquiv.prodCongr (MulEquiv.refl A) eBA)
  let FA : Subgroup ↥H := prodFirstFactor e
  let FB : Subgroup ↥H := prodSecondFactor e
  haveI hSimpleA : IsSimpleGroup A := isSimpleGroup_of_isL2 hLA
  have hsimple : ∀ N : Subgroup A, N.Normal → N = ⊥ ∨ N = ⊤ := by
    intro N hN
    haveI : N.Normal := hN
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
  have hntA : ∃ a : A, a ≠ 1 := by
    by_contra h
    push Not at h
    haveI : Subsingleton A := ⟨fun a b => by rw [h a, h b]⟩
    exact not_subsingleton A inferInstance
  have hcenterA : Subgroup.center A = ⊥ := by
    obtain ⟨K, hField, hFinite, hKcard, ⟨eA⟩⟩ := nonempty_mulEquiv_sl2_of_isL2 hLA
    letI : Field K := hField
    letI : Finite K := hFinite
    haveI : CharP K 2 := CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22d_charP_two
      (by omega) hKcard
    have hc : Subgroup.center (SL2 K) = ⊥ := center_sl2_eq_bot K
    have hcard : Nat.card (Subgroup.center A) = 1 := by
      rw [Nat.card_congr (Subgroup.centerCongr eA).toEquiv, hc, Subgroup.card_bot]
    exact Subgroup.eq_bot_of_card_eq (H := Subgroup.center A) hcard
  have hcentral : ∀ a : A, (∀ c, a * c = c * a) → a = 1 := by
    intro a ha
    have ha_center : a ∈ Subgroup.center A := Subgroup.mem_center_iff.mpr (fun g => (ha g).symm)
    rw [hcenterA] at ha_center
    exact Subgroup.mem_bot.mp ha_center
  have hFAmap : FA.map e.toMonoidHom = (⊤ : Subgroup A).prod (⊥ : Subgroup A) := by
    change (prodFirstFactor e).map e.toMonoidHom = (⊤ : Subgroup A).prod (⊥ : Subgroup A)
    dsimp only [prodFirstFactor]
    rw [Subgroup.map_map]
    have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id (A × A) :=
      MulEquiv.toMonoidHom_comp_toMonoidHom_symm e
    rw [hcomp, Subgroup.map_id]
  have hFA_ne_top : FA ≠ ⊤ := by
    intro hFA_top
    have hne : (⊤ : Subgroup A).prod (⊥ : Subgroup A) ≠ ⊤ := by
      intro htop
      obtain ⟨a, ha⟩ := hntA
      have hmem : (1, a) ∈ (⊤ : Subgroup A).prod (⊥ : Subgroup A) := by
        rw [htop]; exact Subgroup.mem_top _
      exact ha (Subgroup.mem_bot.mp (Subgroup.mem_prod.mp hmem).2)
    exact hne (by rw [← hFAmap, hFA_top, Subgroup.map_top_of_surjective _ e.surjective])
  have hFA_not_center : ¬ FA ≤ Subgroup.center ↥H := by
    intro hcenter
    have hmapc : (⊤ : Subgroup A).prod (⊥ : Subgroup A) ≤ Subgroup.center (A × A) := by
      rw [← hFAmap, ← Subgroup.map_center_eq e]
      exact Subgroup.map_mono hcenter
    have hAle : (⊤ : Subgroup A) ≤ Subgroup.center A := by
      intro a _
      rw [Subgroup.mem_center_iff]
      intro c
      have hmem : (a, (1 : A)) ∈ Subgroup.center (A × A) :=
        hmapc (Subgroup.mem_prod.mpr ⟨Subgroup.mem_top _, Subgroup.mem_bot.mpr rfl⟩)
      exact congrArg Prod.fst (Subgroup.mem_center_iff.mp hmem (c, (1 : A)))
    have hcenter_top : Subgroup.center A = ⊤ := le_antisymm le_top hAle
    rw [hcenterA] at hcenter_top
    exact top_ne_bot hcenter_top.symm
  have hswap_exists : ∃ t : Tstar,
      FA.map (H.normalizerMonoidHom ⟨t.1, hTnorm t.2⟩).toMonoidHom = FB ∧
      FB.map (H.normalizerMonoidHom ⟨t.1, hTnorm t.2⟩).toMonoidHom = FA := by
    by_contra h
    have hpres : ∀ (t : MulAut W) (ht : t ∈ Tstar),
        FA.map (H.normalizerMonoidHom ⟨t, hTnorm ht⟩).toMonoidHom = FA := by
      intro t ht
      have hcases := prodFirstFactor_map_mulAut_eq_or hsimple hcentral hntA e
        (H.normalizerMonoidHom ⟨t, hTnorm ht⟩)
      rcases hcases with ⟨h1, _⟩ | ⟨h1, h2⟩
      · exact h1
      · exact (h ⟨⟨t, ht⟩, And.intro h1 h2⟩).elim
    apply hFA_not_center
    refine hnormal FA (prodFirstFactor_normal e) ?_ hFA_ne_top
    intro t ht
    exact map_conj_eq_of_normalizerMonoidHom_map_eq (H := H) (t := t) (N := FA) (hTnorm ht) (hpres t ht)
  have htop_of_FA : FA ≤ Pstar → Pstar = ⊤ := by
    intro hFAle
    obtain ⟨t0, hswap0, -⟩ := hswap_exists
    have hmap : (FA.map H.subtype).map (MulAut.conj t0.1).toMonoidHom = FB.map H.subtype :=
      map_conj_eq_of_normalizerMonoidHom_map_eq (H := H) (t := t0.1) (N := FA) (hTnorm t0.2) hswap0
    have h1 : FA.map H.subtype ≤ Pstar.map H.subtype := Subgroup.map_mono hFAle
    have h2 : (FA.map H.subtype).map (MulAut.conj t0.1).toMonoidHom ≤
        (Pstar.map H.subtype).map (MulAut.conj t0.1).toMonoidHom :=
      Subgroup.map_mono (f := (MulAut.conj t0.1).toMonoidHom) h1
    have hinv := hgood.2.2.1 t0.1 t0.2
    rw [hmap, hinv] at h2
    have hFBle : FB ≤ Pstar :=
      (Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp h2
    refine le_antisymm le_top ?_
    rw [← prodFirstFactor_sup_prodSecondFactor e]
    exact sup_le hFAle hFBle
  have htop_of_FB : FB ≤ Pstar → Pstar = ⊤ := by
    intro hFBle
    obtain ⟨t0, -, hswap0⟩ := hswap_exists
    have hmap : (FB.map H.subtype).map (MulAut.conj t0.1).toMonoidHom = FA.map H.subtype :=
      map_conj_eq_of_normalizerMonoidHom_map_eq (H := H) (t := t0.1) (N := FB) (hTnorm t0.2) hswap0
    have h1 : FB.map H.subtype ≤ Pstar.map H.subtype := Subgroup.map_mono hFBle
    have h2 : (FB.map H.subtype).map (MulAut.conj t0.1).toMonoidHom ≤
        (Pstar.map H.subtype).map (MulAut.conj t0.1).toMonoidHom :=
      Subgroup.map_mono (f := (MulAut.conj t0.1).toMonoidHom) h1
    have hinv := hgood.2.2.1 t0.1 t0.2
    rw [hmap, hinv] at h2
    have hFAle : FA ≤ Pstar :=
      (Subgroup.map_le_map_iff_of_injective H.subtype_injective).mp h2
    refine le_antisymm le_top ?_
    rw [← prodFirstFactor_sup_prodSecondFactor e]
    exact sup_le hFAle hFBle
  have htop : Pstar = ⊤ := by
    by_contra hne
    let P : Subgroup (A × A) := Pstar.map e.toMonoidHom
    obtain ⟨S0, hS0⟩ := hgood.1
    let T : Sylow 2 (A × A) :=
      Sylow.mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective S0
    have hN_map : (Subgroup.normalizer (S0 : Set ↥H)).map e.toMonoidHom =
        Subgroup.normalizer (T : Set (A × A)) := by
      change (Subgroup.normalizer (S0 : Set ↥H)).map e.toMonoidHom =
        Subgroup.normalizer ((S0 : Subgroup ↥H).map e.toMonoidHom : Set (A × A))
      exact Subgroup.map_equiv_normalizer_eq (S0 : Subgroup ↥H) e
    have hN_le_P : Subgroup.normalizer (T : Set (A × A)) ≤ P := by
      have := Subgroup.map_mono (f := e.toMonoidHom) hS0
      rwa [hN_map] at this
    obtain ⟨TA, TB, hT_eq⟩ := sylow_prod_eq T
    let BA : Subgroup A := Subgroup.normalizer (TA : Set A)
    let BB : Subgroup A := Subgroup.normalizer (TB : Set A)
    have hN_eq : Subgroup.normalizer (T : Set (A × A)) = BA.prod BB := by
      change Subgroup.normalizer ((T : Subgroup (A × A)) : Set (A × A)) = BA.prod BB
      rw [hT_eq, normalizer_prod_eq]
      rfl
    have hP_prod : BA.prod BB ≤ P := hN_eq.symm ▸ hN_le_P
    let QA : Subgroup A := P.map (MonoidHom.fst A A)
    let QB : Subgroup A := P.map (MonoidHom.snd A A)
    have hBA_le_QA : BA ≤ QA := by
      intro x hx
      have hmem : (x, (1 : A)) ∈ BA.prod BB :=
        Subgroup.mem_prod.mpr ⟨hx, Subgroup.one_mem BB⟩
      exact Subgroup.mem_map_of_mem (MonoidHom.fst A A) (hP_prod hmem)
    have hBB_le_QB : BB ≤ QB := by
      intro x hx
      have hmem : ((1 : A), x) ∈ BA.prod BB :=
        Subgroup.mem_prod.mpr ⟨Subgroup.one_mem BA, hx⟩
      exact Subgroup.mem_map_of_mem (MonoidHom.snd A A) (hP_prod hmem)
    have hTA_le_QA : (TA : Subgroup A) ≤ QA := (Subgroup.le_normalizer).trans hBA_le_QA
    have hQA : QA = BA ∨ QA = ⊤ := by
      by_cases h : QA = ⊤
      · exact Or.inr h
      · left
        exact le_antisymm (l2_sylow_le_normalizer hn2 hLA TA QA hTA_le_QA h) hBA_le_QA
    have hTB_le_QB : (TB : Subgroup A) ≤ QB := (Subgroup.le_normalizer).trans hBB_le_QB
    have hQB : QB = BB ∨ QB = ⊤ := by
      by_cases h : QB = ⊤
      · exact Or.inr h
      · left
        exact le_antisymm (l2_sylow_le_normalizer hn2 hLA TB QB hTB_le_QB h) hBB_le_QB
    rcases hQA with hQA | hQA <;> rcases hQB with hQB | hQB
    ·
      have hP_le : P ≤ BA.prod BB := by
        intro x hx
        have hx₁ : x.1 ∈ QA := Subgroup.mem_map_of_mem (MonoidHom.fst A A) hx
        have hx₂ : x.2 ∈ QB := Subgroup.mem_map_of_mem (MonoidHom.snd A A) hx
        rw [hQA] at hx₁
        rw [hQB] at hx₂
        exact Subgroup.mem_prod.mpr ⟨hx₁, hx₂⟩
      have hP_eq : P = BA.prod BB := le_antisymm hP_le hP_prod
      have hS_le_P : (S : Subgroup ↥H) ≤ Pstar := hgood.2.1
      let S' : Sylow 2 (A × A) :=
        Sylow.mapSurjective (p := 2) (f := e.toMonoidHom) e.surjective (S : Sylow 2 ↥H)
      obtain ⟨SA, SB, hS_eq⟩ := sylow_prod_eq S'
      have hS'__le_P : (S' : Subgroup (A × A)) ≤ P := by
        have := Subgroup.map_mono (f := e.toMonoidHom) hS_le_P
        exact this
      have hSA_le_BA : (SA : Subgroup A) ≤ BA := by
        intro a ha
        have hone : (1 : A) ∈ (SB : Subgroup A) := Subgroup.one_mem (SB : Subgroup A)
        have hmemProd : (a, (1 : A)) ∈ (SA : Subgroup A).prod (SB : Subgroup A) := by
          exact Subgroup.mem_prod.mpr ⟨ha, hone⟩
        have hmem' : (a, (1 : A)) ∈ (S' : Subgroup (A × A)) := by
          simpa [hS_eq] using hmemProd
        have hmem : (a, (1 : A)) ∈ P := hS'__le_P hmem'
        have hthis := Subgroup.mem_map_of_mem (MonoidHom.fst A A) hmem
        change a ∈ QA at hthis
        rwa [hQA] at hthis
      have hSB_le_BB : (SB : Subgroup A) ≤ BB := by
        intro b hb
        have hone : (1 : A) ∈ (SA : Subgroup A) := Subgroup.one_mem (SA : Subgroup A)
        have hmemProd : ((1 : A), b) ∈ (SA : Subgroup A).prod (SB : Subgroup A) := by
          exact Subgroup.mem_prod.mpr ⟨hone, hb⟩
        have hmem' : ((1 : A), b) ∈ (S' : Subgroup (A × A)) := by
          simpa [hS_eq] using hmemProd
        have hmem : ((1 : A), b) ∈ P := hS'__le_P hmem'
        have hthis := Subgroup.mem_map_of_mem (MonoidHom.snd A A) hmem
        change b ∈ QB at hthis
        rwa [hQB] at hthis
      have hSA_eq : SA = TA := sylow_eq_of_le_normalizer TA SA hSA_le_BA
      have hSB_eq : SB = TB := sylow_eq_of_le_normalizer TB SB hSB_le_BB
      have hS'_eq_T : S' = T := by
        apply Sylow.ext
        rw [hS_eq, hT_eq, hSA_eq, hSB_eq]
      have hP_le_N : P ≤ Subgroup.normalizer (S' : Set (A × A)) := by
        rw [hS'_eq_T, hP_eq, hN_eq]
      have hN_S_map : (Subgroup.normalizer (S : Set ↥H)).map e.toMonoidHom =
          Subgroup.normalizer (S' : Set (A × A)) := by
        change (Subgroup.normalizer (S : Set ↥H)).map e.toMonoidHom =
          Subgroup.normalizer ((S : Subgroup ↥H).map e.toMonoidHom : Set (A × A))
        exact Subgroup.map_equiv_normalizer_eq (S : Subgroup ↥H) e
      have hPstar_le_N : Pstar ≤ Subgroup.normalizer (S : Set ↥H) := by
        apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
        rw [hN_S_map]
        exact hP_le_N
      exact hgood.2.2.2 (hPstar_le_N.trans (normalizer_sylow_le_stabilizer_fixedPointSubgroup H S))
    ·
      have hsecond : (⊥ : Subgroup A).prod (⊤ : Subgroup A) ≤ P :=
        secondFactor_le_of_proj_eq_top_of_fst_le P BA BB hP_prod (by show QB = ⊤; exact hQB) (by show QA ≤ BA; rw [hQA])
      have hFB_le : FB ≤ Pstar := by
        apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
        change FB.map e.toMonoidHom ≤ P
        change (prodSecondFactor e).map e.toMonoidHom ≤ P
        dsimp only [prodSecondFactor]
        rw [Subgroup.map_map]
        have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id (A × A) :=
          MulEquiv.toMonoidHom_comp_toMonoidHom_symm e
        rw [hcomp, Subgroup.map_id]
        exact hsecond
      exact hne (htop_of_FB hFB_le)
    ·
      have hfirst : (⊤ : Subgroup A).prod (⊥ : Subgroup A) ≤ P :=
        firstFactor_le_of_proj_eq_top_of_snd_le P BA BB hP_prod (by show QA = ⊤; exact hQA) (by show QB ≤ BB; rw [hQB])
      have hFA_le : FA ≤ Pstar := by
        apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
        change FA.map e.toMonoidHom ≤ P
        change (prodFirstFactor e).map e.toMonoidHom ≤ P
        dsimp only [prodFirstFactor]
        rw [Subgroup.map_map]
        have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id (A × A) :=
          MulEquiv.toMonoidHom_comp_toMonoidHom_symm e
        rw [hcomp, Subgroup.map_id]
        exact hfirst
      exact hne (htop_of_FA hFA_le)
    ·
      have hcomm : ⁅(⊤ : Subgroup A), BA⁆ = ⊤ :=
        commutator_top_normalizer_eq_top hn2 hLA TA
      have hfirst : (⊤ : Subgroup A).prod (⊥ : Subgroup A) ≤ P :=
        firstFactor_le_of_proj_eq_top P BA BB hP_prod (by show QA = ⊤; exact hQA) (by show QB = ⊤; exact hQB) hcomm
      have hFA_le : FA ≤ Pstar := by
        apply (Subgroup.map_le_map_iff_of_injective (f := e.toMonoidHom) e.injective).mp
        change FA.map e.toMonoidHom ≤ P
        change (prodFirstFactor e).map e.toMonoidHom ≤ P
        dsimp only [prodFirstFactor]
        rw [Subgroup.map_map]
        have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id (A × A) :=
          MulEquiv.toMonoidHom_comp_toMonoidHom_symm e
        rw [hcomp, Subgroup.map_id]
        exact hfirst
      exact hne (htop_of_FA hFA_le)
  have hpCoreA : CFSG.pCore 2 A = ⊥ := pCore_eq_bot_of_isL2 hLA
  have hpCoreAA : CFSG.pCore 2 (A × A) = ⊥ :=
    CFSG.CGT.PushingUpLit.CGT6.pCore_prod_bot hpCoreA
  have hpCore : CFSG.pCore 2 ↥H = ⊥ := by
    have hmap := CFSG.pCore_map_iso 2 e
    rw [hpCoreAA] at hmap
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := CFSG.pCore 2 ↥H) (f := e.toMonoidHom) e.injective).mp hmap
  obtain ⟨eBar⟩ := nonempty_bar2_top_mulEquiv_of_pCore_eq_bot hpCore
  have hL2SqBar : IsL2Square (Bar2 (⊤ : Subgroup ↥H)) n :=
    IsL2Square.of_mulEquiv eBar.symm (isL2Square_of_isOmegaPlus hn2 hline.1)
  have hHinf : Hinf (⊤ : Subgroup ↥H) = ⊤ := Hinf_top_eq_top_of_perfect hperfH
  refine ⟨htop, ?_⟩
  rw [htop, hHinf]
  exact hL2SqBar


end CFSG.LocalAnalysis.UniquenessCase.UC22

end
