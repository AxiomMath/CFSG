module

public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofKBar
public import CFSG.RankThree.PartTwo.Sec8.Item86ResProofCore
public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.RankThree.PartTwo.Sec8.Item86Res2ProofIndep
import CFSG.RankThree.PartTwo.Sec8.Item87ProofOrders
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofCases

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open CFSG.Assembly.RankThreeEven (projSL)
open scoped Matrix

section Even

theorem two_dvd_card_psl2_of_charTwo (F : Type*) [Field F] [Finite F] [CharP F 2] :
    2 ∣ Nat.card (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) := by
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  set M : Matrix (Fin 2) (Fin 2) F := !![1, 1; 0, 1] with hM
  have hdet : M.det = 1 := by simp [hM, Matrix.det_fin_two]
  have hM2 : M * M = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hM, Matrix.mul_apply, Fin.sum_univ_two]
    rw [one_add_one_eq_two, h2]
  obtain ⟨t, ht⟩ : ∃ t : Matrix.SpecialLinearGroup (Fin 2) F,
      (t : Matrix (Fin 2) (Fin 2) F) = M := ⟨⟨M, hdet⟩, rfl⟩
  have ht1 : t ≠ 1 := by
    intro h
    have := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) F =>
      (g : Matrix (Fin 2) (Fin 2) F) 0 1) h
    simp [ht, hM] at this
  have ht2 : t ^ 2 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, ht, sq, hM2, Matrix.SpecialLinearGroup.coe_one]
  set π := QuotientGroup.mk'
    (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) with hπ
  have hinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, hπ, QuotientGroup.ker_mk',
      center_specialLinearGroup_two_eq_bot]
  have hot : orderOf (π t) = 2 := by
    rw [orderOf_injective π hinj]
    exact orderOf_eq_prime ht2 ht1
  have hdvd := orderOf_dvd_natCard (π t)
  rw [hot] at hdvd
  exact hdvd

theorem two_dvd_card_of_isoSUThree {X : Type} [Group X] {f : ℕ} (hf : 1 ≤ f)
    (h : IsoSUThree X (2 ^ f)) : 2 ∣ Nat.card X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, Item87Proof.card_statedSU_three_two hF]
  exact Dvd.dvd.mul_right (dvd_pow_self 2 (by omega)) _


theorem exists_noncentral_pow_three_statedSU {F : Type} [Field F] [Finite F] {g : ℕ}
    (hF : Nat.card F = (2 ^ g) ^ 2) (h3 : 3 ∣ 2 ^ g + 1) :
    ∃ z w : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ g) F, z ^ 3 = 1 ∧ z * w ≠ w * z := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (f := 2 * g)
    (by rw [← Nat.card_eq_fintype_card, hF, ← pow_mul, mul_comm])
  have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
  have hq1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
  have h3U : 3 ∣ Nat.card Fˣ := by
    rw [Nat.card_units, hF]
    have e : (2 ^ g) ^ 2 - 1 = (2 ^ g - 1) * (2 ^ g + 1) := by
      have : 1 ≤ (2 ^ g) ^ 2 := Nat.one_le_pow _ _ (by positivity)
      zify [hq1, this]
      ring
    rw [e]
    exact Dvd.dvd.mul_left h3 _
  obtain ⟨ω, hω⟩ := exists_prime_orderOf_dvd_card' 3 h3U
  have hω3 : ω ^ 3 = 1 := by rw [← hω]; exact pow_orderOf_eq_one ω
  have hωq : ω ^ (2 ^ g + 1) = 1 := by
    obtain ⟨t, ht⟩ := h3
    rw [ht, pow_mul, hω3, one_pow]
  have hωne : (ω : F) ≠ (ω : F)⁻¹ := by
    intro h
    have h1 : ω ^ 2 = 1 := by
      apply Units.ext
      rw [Units.val_pow_eq_pow_val, sq, Units.val_one]
      nth_rewrite 2 [h]
      exact mul_inv_cancel₀ (Units.ne_zero ω)
    have := orderOf_dvd_of_pow_eq_one h1
    rw [hω] at this
    norm_num at this
  set D := KFacts.diag3 ω ω⁻¹ 1 with hD
  have hDmem : D ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ g) F := by
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · rw [hD, KFacts.coe_diag3, Matrix.det_diagonal, Fin.prod_univ_three]
      simp
    · rw [hD, KFacts.coe_diag3, Matrix.diagonal_map (by simp), Matrix.diagonal_transpose,
        Matrix.diagonal_mul_diagonal]
      have hN : ∀ w : Fˣ, w ^ (2 ^ g + 1) = 1 → (w : F) ^ 2 ^ g * w = 1 := fun w hw => by
        rw [← pow_succ, ← Units.val_pow_eq_pow_val, hw, Units.val_one]
      have h11 : ((ω : F) ^ 2 ^ g)⁻¹ * (ω : F)⁻¹ = 1 := by rw [← mul_inv, hN ω hωq, inv_one]
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.diagonal, hN ω hωq, h11]
  set P : Matrix (Fin 3) (Fin 3) F := !![0, 1, 0; 1, 0, 0; 0, 0, 1] with hP
  have hPP : P * P = 1 := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hP, Matrix.mul_apply, Fin.sum_univ_three]
  set Pu : GL (Fin 3) F := ⟨P, P, hPP, hPP⟩ with hPu
  have hPmem : Pu ∈ CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ g) F := by
    apply Subgroup.subset_closure
    refine ⟨?_, ?_⟩
    · change P.det = 1
      have hneg : (-1 : F) = 1 := by rw [neg_eq_iff_add_eq_zero, one_add_one_eq_two, h2]
      rw [hP, Matrix.det_fin_three]
      simp [hneg]
    · change (P.map (· ^ 2 ^ g))ᵀ * P = 1
      have hmap : P.map (· ^ 2 ^ g) = P := by
        ext i j
        have hz : (0 : F) ^ 2 ^ g = 0 := zero_pow (by positivity)
        fin_cases i <;> fin_cases j <;> simp [hP, hz]
      have htr : Pᵀ = P := by
        ext i j
        fin_cases i <;> fin_cases j <;> simp [hP]
      rw [hmap, htr, hPP]
  refine ⟨⟨D, hDmem⟩, ⟨Pu, hPmem⟩, ?_, ?_⟩
  · apply Subtype.ext
    change D ^ 3 = 1
    rw [hD, KFacts.diag3_pow, hω3, inv_pow, hω3, inv_one, one_pow, KFacts.diag3_one]
  · intro h
    have h1 := congrArg (fun z : CFSG.Assembly.LowTwoRank.StatedSU 3 (2 ^ g) F =>
      ((z : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 1) h
    simp only [Subgroup.coe_mul, Units.val_mul, hD, KFacts.coe_diag3, hPu] at h1
    simp [Matrix.mul_apply, hP, Matrix.diagonal] at h1
    exact hωne h1

end Even

section Transfer

variable {G : Type} [Group G] [Finite G]

theorem imageModTheta_eq_range {K M : Subgroup G} :
    imageModTheta K M =
      ((QuotientGroup.mk' (aschbacherSolvableCore 3 K)).comp (M.subgroupOf K).subtype).range := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rfl

theorem card_barCentralizer_dvd_card_inf {L K : Subgroup G} {a : G} (hKL : K ≤ L)
    (haK : a ∈ Subgroup.normalizer (K : Set G)) (haL : a ∈ Subgroup.normalizer (L : Set G))
    (ha3 : ∃ j : ℕ, a ^ 3 ^ j = 1) :
    Nat.card (barCentralizer (Subgroup.zpowers a) K) ∣
      Nat.card (imageModTheta L K ⊓ barCentralizer (Subgroup.zpowers a) L : Subgroup _) := by
  obtain ⟨-, -, -, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  obtain ⟨hθLs, -, hθL3, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  set M := K ⊓ Subgroup.centralizer ({a} : Set G) with hM
  have hMa : M ≤ Subgroup.centralizer ({a} : Set G) := inf_le_right
  have hC := KFacts.imageModTheta_centralizer_eq (L := K) haK ha3
  rw [← hC]
  set N := (aschbacherSolvableCore 3 L).comap (Subgroup.inclusion hKL) with hN
  set ι : N →* aschbacherSolvableCore 3 L :=
    { toFun := fun x => ⟨Subgroup.inclusion hKL x, x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl } with hι
  have hιinj : Function.Injective ι := by
    intro u v huv
    have h := congrArg (fun w : aschbacherSolvableCore 3 L => ((w : L) : G)) huv
    exact Subtype.ext (Subtype.ext h)
  have hNs : Group.IsSolvable N := Group.isSolvable_of_isSolvable_injective hιinj
  have hN3 : ¬ 3 ∣ Nat.card N := fun h3 =>
    hθL3 (h3.trans (Subgroup.card_dvd_of_injective ι hιinj))
  have hNθ : N ≤ aschbacherSolvableCore 3 K :=
    hθmax N (Subgroup.Normal.comap inferInstance _) hNs hN3
  set M' := M.subgroupOf K with hM'
  set f₁ : M' →* K ⧸ aschbacherSolvableCore 3 K :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 K)).comp M'.subtype with hf₁
  set f₂ : M' →* L ⧸ aschbacherSolvableCore 3 L :=
    ((QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hKL)).comp
      M'.subtype with hf₂
  have hker' : f₂.ker ≤ f₁.ker := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx ⊢
    rw [hf₂, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    rw [hf₁, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hNθ hx
  have h1 : f₁.ker.index ∣ f₂.ker.index := Subgroup.index_dvd_of_le hker'
  rw [Subgroup.index_ker, Subgroup.index_ker] at h1
  have h2 : imageModTheta K M = f₁.range := imageModTheta_eq_range
  rw [h2]
  refine h1.trans (Subgroup.card_dvd_of_le ?_)
  rintro _ ⟨x, rfl⟩
  have hxM : ((x : K) : G) ∈ M := Subgroup.mem_subgroupOf.mp x.2
  refine ⟨⟨Subgroup.inclusion hKL (x : K), Subgroup.mem_subgroupOf.mpr (x : K).2, rfl⟩, ?_⟩
  exact imageModTheta_le_barCentralizer haL hMa
    ⟨⟨(x : K), hKL (x : K).2⟩, Subgroup.mem_subgroupOf.mpr hxM, rfl⟩

theorem nonempty_quot_mulEquiv_psl2 {L : Subgroup G} {d : G} {n : ℕ} (hn : 1 ≤ n)
    (eK : imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
      projSL 2 (GaloisField 2 (3 * n))) :
    Nonempty (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ⧸
        aschbacherSolvableCore 3 (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 (3 * n))) := by
  have hKL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≤ L :=
    (Item87Proof.residual_le _).trans inf_le_left
  obtain ⟨ψ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKL
    (Item87Proof.NoThetaNormal.of_mulEquiv eK (Item87Proof.noThetaNormal_projSL_two (by omega)))
  exact ⟨(ψ.trans eK).trans (Sec4.projSLEquivPSL _)⟩

theorem isoSUThree_quot {L : Subgroup G} {d : G} {n : ℕ} (hn : 1 ≤ n)
    (hK : IsoSUThree (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer {d}))) (2 ^ (3 * n))) :
    IsoSUThree (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ⧸
        aschbacherSolvableCore 3 (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})))
      (2 ^ (3 * n)) := by
  have hKL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≤ L :=
    (Item87Proof.residual_le _).trans inf_le_left
  obtain ⟨F, hF, hFf, hFc, ⟨φ⟩⟩ := hK
  obtain ⟨ψ⟩ := Item87Proof.nonempty_quot_mulEquiv_imageModTheta hKL
    (Item87Proof.NoThetaNormal.of_mulEquiv φ (Item87Proof.noThetaNormal_statedSU hFc (by omega)))
  exact ⟨F, hF, hFf, hFc, ⟨ψ.trans φ⟩⟩

end Transfer

@[expose] def KF84OuterL2 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (A₀ : Subgroup G) (d : G) (n : ℕ), Hyp81 G A c L a → 27 < Nat.card A →
      Data83 G c L a A₀ d n →
      Nonempty (imageModTheta L (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ≃*
        projSL 2 (GaloisField 2 (3 * n))) →
      Sec4.InducesOuterTheta a (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))

@[expose] def KF84FieldReeStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (A₀ : Subgroup G) (d : G) (n : ℕ), Hyp81 G A c L a → 27 < Nat.card A →
      Data83 G c L a A₀ d n → IsoReeF4 (L ⧸ aschbacherSolvableCore 3 L) (3 * n) →
      KFacts.InducesStdKind (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) a .field

@[expose] def KF84FieldStd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (A₀ : Subgroup G) (d : G) (n : ℕ), Hyp81 G A c L a → 27 < Nat.card A →
      Data83 G c L a A₀ d n →
      KFacts.InducesStdKind (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) a .field

section Consequences

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {A₀ : Subgroup G} {d : G} {n : ℕ}

theorem pow_three_of_data83 (hd : Data83 G c L a A₀ d n) : a ^ 3 = 1 :=
  hd.isElemAbelian.2 a hd.a_mem

theorem mem_normalizer_residual_of_data83 (h : Hyp81 G A c L a) (hd : Data83 G c L a A₀ d n) :
    a ∈ Subgroup.normalizer
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) : Set G) := by
  have hA₀e := hd.isElemAbelian
  have hda : d * a = a * d :=
    congrArg Subtype.val (hA₀e.1.is_comm.comm ⟨d, hd.d_mem⟩ ⟨a, hd.a_mem⟩)
  have ha := h.a_mem_normalizer
  have haC : a ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hda.symm)
  have haLd : a ∈ Subgroup.normalizer
      ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp ha y),
      (Subgroup.mem_normalizer_iff.mp haC y)]
  exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
    _ haLd

theorem kF84FieldStd_of (hO : KF84OuterL2) (hR : KF84FieldReeStd) : KF84FieldStd := by
  intro G _ _ A c L a A₀ d n h hA hd
  have hn1 : 1 ≤ n := hd.odd.pos
  have ha3 := pow_three_of_data83 hd
  have hL2 : ∀ eK : imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer {d})) ≃* projSL 2 (GaloisField 2 (3 * n)),
      KFacts.InducesStdKind (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) a
        .field := by
    intro eK
    obtain ⟨e⟩ := nonempty_quot_mulEquiv_psl2 hn1 eK
    exact .psl2 (GaloisField 2 (3 * n))
      ⟨e, KFacts.inducesKind_field_of_pow_three _ ha3 (hO G A c L a A₀ d n h hA hd ⟨eK⟩) e⟩
  rcases hd.cases with ⟨-, ⟨eK⟩, -⟩ | ⟨hRee, -, -⟩ | ⟨-, -, ⟨eK⟩⟩ | ⟨-, -, ⟨eK⟩⟩ |
    ⟨-, -, ⟨eK⟩⟩
  · exact hL2 eK
  · exact hR G A c L a A₀ d n h hA hd hRee
  · exact hL2 eK
  · exact hL2 eK
  · exact hL2 eK

theorem two_dvd_card_barCentralizer_of (hO : KF84OuterL2) (hR : KF84FieldReeStd)
    (h : Hyp81 G A c L a) (hA : 27 < Nat.card A) (hd : Data83 G c L a A₀ d n) :
    2 ∣ Nat.card (barCentralizer (Subgroup.zpowers a)
      (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))) := by
  have hn1 : 1 ≤ n := hd.odd.pos
  have ha3 := pow_three_of_data83 hd
  have hL2 : ∀ eK : imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer {d})) ≃* projSL 2 (GaloisField 2 (3 * n)),
      2 ∣ Nat.card (barCentralizer (Subgroup.zpowers a)
        (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))) := by
    intro eK
    obtain ⟨e⟩ := nonempty_quot_mulEquiv_psl2 hn1 eK
    have hf := KFacts.inducesKind_field_of_pow_three _ ha3 (hO G A c L a A₀ d n h hA hd ⟨eK⟩) e
    obtain ⟨σ, -, -, ⟨φ⟩⟩ := KFacts.exists_barCentralizer_mulEquiv_of_field ha3 e hf
    rw [Nat.card_congr φ.toEquiv]
    exact two_dvd_card_psl2_of_charTwo _
  rcases hd.cases with ⟨-, ⟨eK⟩, -⟩ | ⟨hRee, -, hSU⟩ | ⟨-, -, ⟨eK⟩⟩ | ⟨-, -, ⟨eK⟩⟩ |
    ⟨-, -, ⟨eK⟩⟩
  · exact hL2 eK
  · have hf := hR G A c L a A₀ d n h hA hd hRee
    have hC := KFacts.isoSUThree_barCentralizer_of_inducesStdKind hd.odd (isoSUThree_quot hn1 hSU)
      ha3 hf
    exact two_dvd_card_of_isoSUThree hn1 hC
  · exact hL2 eK
  · exact hL2 eK
  · exact hL2 eK


theorem exists_pow_three_noncentral_of (hO : KF84OuterL2) (hR : KF84FieldReeStd)
    (h : Hyp81 G A c L a) (hA : 27 < Nat.card A) (hd : Data83 G c L a A₀ d n) :
    Sec4.InducesOuterTheta a (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) ∧
      ∃ y : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}),
        (y : G) * a = a * y ∧ y ^ 3 = 1 ∧
        MulAut.conj ((y : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d})) :
          inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ⧸
            aschbacherSolvableCore 3
              (inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}))) ≠ 1 := by
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) with hK
  have hn1 : 1 ≤ n := hd.odd.pos
  have ha3 := pow_three_of_data83 hd
  have haK := mem_normalizer_residual_of_data83 h hd
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have key : Sec4.InducesOuterTheta a K ∧ ∃ z ∈ barCentralizer (Subgroup.zpowers a) K,
      z ^ 3 = 1 ∧ MulAut.conj z ≠ 1 := by
    have hL2 : ∀ eK : imageModTheta L K ≃* projSL 2 (GaloisField 2 (3 * n)),
        Sec4.InducesOuterTheta a K ∧ ∃ z ∈ barCentralizer (Subgroup.zpowers a) K,
          z ^ 3 = 1 ∧ MulAut.conj z ≠ 1 := by
      intro eK
      obtain ⟨e⟩ := nonempty_quot_mulEquiv_psl2 hn1 eK
      have hout := hO G A c L a A₀ d n h hA hd ⟨eK⟩
      have hf := KFacts.inducesKind_field_of_pow_three _ ha3 hout e
      obtain ⟨σ, -, -, ⟨φ⟩⟩ := KFacts.exists_barCentralizer_mulEquiv_of_field ha3 e hf
      have h3C : 3 ∣ Nat.card (barCentralizer (Subgroup.zpowers a) K) := by
        rw [Nat.card_congr φ.toEquiv]
        exact KFacts.three_dvd_card_psl2 _
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3C
      refine ⟨hout, (z : K ⧸ aschbacherSolvableCore 3 K), z.2, ?_, ?_⟩
      · have := pow_orderOf_eq_one z
        rw [hz] at this
        exact congrArg Subtype.val this
      · intro h1
        have hzc : (z : K ⧸ aschbacherSolvableCore 3 K) ∈ Subgroup.center _ := by
          rw [Subgroup.mem_center_iff]
          intro y
          have h2 := congrArg (fun τ : MulAut (K ⧸ aschbacherSolvableCore 3 K) => τ y) h1
          simp only [MulAut.conj_apply, MulAut.one_apply] at h2
          exact (mul_inv_eq_iff_eq_mul.mp h2).symm
        have hez : e (z : K ⧸ aschbacherSolvableCore 3 K) ∈ Subgroup.center _ := by
          rw [Subgroup.mem_center_iff] at hzc ⊢
          intro y
          have h3 := hzc (e.symm y)
          have h4 := congrArg e h3
          rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at h4
        rw [CFSG.GorensteinWalter.psl2_center_eq_bot, Subgroup.mem_bot,
          MulEquiv.map_eq_one_iff] at hez
        have hz1 : z = 1 := Subtype.ext hez
        rw [hz1, orderOf_one] at hz
        omega
    rcases hd.cases with ⟨-, ⟨eK⟩, -⟩ | ⟨hRee, -, hSU⟩ | ⟨-, -, ⟨eK⟩⟩ | ⟨-, -, ⟨eK⟩⟩ |
      ⟨-, -, ⟨eK⟩⟩
    · exact hL2 eK
    · have hf := hR G A c L a A₀ d n h hA hd hRee
      obtain ⟨F, _, _, hF, ⟨φ⟩⟩ :=
        KFacts.isoSUThree_barCentralizer_of_inducesStdKind hd.odd (isoSUThree_quot hn1 hSU) ha3 hf
      obtain ⟨D, P, hD3, hDP⟩ := exists_noncentral_pow_three_statedSU hF
        (Item82OneProof.three_dvd_two_pow_add_one_of_odd hd.odd)
      refine ⟨KFacts.InducesStdKind.inducesOuterTheta K hf (by decide),
        ((φ.symm D : barCentralizer _ K) :
        K ⧸ aschbacherSolvableCore 3 K), (φ.symm D).2, ?_, ?_⟩
      · have h1 : (φ.symm D) ^ 3 = 1 := by rw [← map_pow, hD3, map_one]
        exact congrArg Subtype.val h1
      · intro h1
        have h2 := congrArg (fun τ : MulAut (K ⧸ aschbacherSolvableCore 3 K) =>
          τ ((φ.symm P : barCentralizer _ K) : K ⧸ aschbacherSolvableCore 3 K)) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h2
        apply hDP
        have h3 : φ.symm D * φ.symm P = φ.symm P * φ.symm D := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul]
          exact mul_inv_eq_iff_eq_mul.mp h2
        have h4 := congrArg φ h3
        rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h4
    · exact hL2 eK
    · exact hL2 eK
    · exact hL2 eK
  obtain ⟨hout, z, hzC, hz3, hzc⟩ := key
  have hC := KFacts.imageModTheta_centralizer_eq (L := K) haK ⟨1, by rw [pow_one]; exact ha3⟩
  rw [← hC] at hzC
  obtain ⟨y₁, hy₁, rfl⟩ := hzC
  have hy₁a : (y₁ : G) * a = a * y₁ :=
    Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_subgroupOf.mp hy₁).2
  set r := Nat.card (aschbacherSolvableCore 3 K) with hr
  have hr3 : ¬ 3 ∣ r := KFacts.not_three_dvd_card_aschbacherSolvableCore K
  refine ⟨hout, y₁ ^ r, ?_, ?_, ?_⟩
  · rw [Subgroup.coe_pow]
    exact (Commute.pow_left hy₁a r).eq
  · have hθ : y₁ ^ 3 ∈ aschbacherSolvableCore 3 K := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
      exact hz3
    have := pow_card_eq_one' (x := (⟨y₁ ^ 3, hθ⟩ : aschbacherSolvableCore 3 K))
    have h5 := congrArg Subtype.val this
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h5
    rw [← pow_mul, mul_comm, pow_mul] at h5
    exact h5
  · intro h1
    apply hzc
    have hmem := Item82OneProof.mem_zpowers_pow_of_not_three_dvd hz3 hr3
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    rw [← hk, map_zpow]
    have h1' : MulAut.conj ((QuotientGroup.mk' (aschbacherSolvableCore 3 K)) y₁ ^ r) = 1 := by
      rw [← map_pow]
      exact h1
    rw [h1', one_zpow]

theorem kF83KBarEven_of (hO : KF84OuterL2) (hR : KF84FieldReeStd) : KF83KBarEven := by
  intro G _ _ A c L a A₀ d n h hA hd
  have hKL : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≤ L :=
    (Item87Proof.residual_le _).trans inf_le_left
  exact (two_dvd_card_barCentralizer_of hO hR h hA hd).trans
    (card_barCentralizer_dvd_card_inf hKL (mem_normalizer_residual_of_data83 h hd)
      h.a_mem_normalizer ⟨1, by rw [pow_one]; exact pow_three_of_data83 hd⟩)

end Consequences

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
