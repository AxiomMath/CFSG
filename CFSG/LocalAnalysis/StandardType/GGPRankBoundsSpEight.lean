module

public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsSp
public import CFSG.LocalAnalysis.StandardType.GGPRankBoundsEigen
public import CFSG.LieType.BorelTits.Symplectic

public section

namespace CFSG.StandardType

namespace PRankBounds

open Matrix CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.BorelTits

theorem sq_eq_self_galoisField_two (x : GaloisField 2 1) : x ^ 2 = x := by
  rcases eq_zero_or_eq_one_galoisField_two x with rfl | rfl <;> simp

theorem eq_of_sq_eq_of_pow_three {L : Type*} [Field L] {s t : L} (hs : s ^ 3 = 1)
    (ht : t ^ 3 = 1) (h : s ^ 2 = t ^ 2) : s = t := by
  calc s = s ^ 3 * s := by rw [hs, one_mul]
    _ = (s ^ 2) ^ 2 := by ring
    _ = (t ^ 2) ^ 2 := by rw [h]
    _ = t ^ 3 * t := by ring
    _ = t := by rw [ht, one_mul]

theorem eq_zero_of_orbit_spEight (E : Subgroup (StatedSp 4 (GaloisField 2 1)))
    (hE : IsElemAbelian 3 E) (h81 : 3 ^ 4 ≤ Nat.card E) (v : Fin 4 ⊕ Fin 4 → GaloisField 2 1)
    (hv : ∀ x ∈ E, (spForm 4 (GaloisField 2 1)).β
      ((((x : StatedSp 4 (GaloisField 2 1)) : GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1)) :
        Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (GaloisField 2 1)) *ᵥ v) v = 0) : v = 0 := by
  classical
  set L := AlgebraicClosure (GaloisField 2 1)
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap (GaloisField 2 1) L).injective 2
  have : ExpChar L 2 := ExpChar.prime Nat.prime_two
  set ι' : (GaloisField 2 1) →+* L := algebraMap (GaloisField 2 1) L with hι'
  set Φ : GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1) →* GL (Fin 4 ⊕ Fin 4) L :=
    Matrix.GeneralLinearGroup.map ι' with hΦdef
  have hΦ : Function.Injective Φ := CFSG.RankThree.PartTwo.Sec4.map_injective_GL ι'
  set E₀ : Subgroup (GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1)) :=
    E.map (StatedSp 4 (GaloisField 2 1)).subtype with hE₀
  set EL : Subgroup (GL (Fin 4 ⊕ Fin 4) L) := E₀.map Φ with hEL
  have hΦmat : ∀ x : GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1),
      ((Φ x : GL (Fin 4 ⊕ Fin 4) L) : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) =
        (x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (GaloisField 2 1)).map ι' := fun x => rfl
  have hmemEL : ∀ y ∈ EL, ∃ x ∈ E,
      y = Φ ((x : StatedSp 4 (GaloisField 2 1)) : GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1)) := by
    rintro _ ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    exact ⟨x, hx, rfl⟩
  have hcomm : ∀ x ∈ EL, ∀ y ∈ EL, x * y = y * x := by
    intro x hx y hy
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    obtain ⟨y₀, hy₀, rfl⟩ := hmemEL y hy
    rw [← map_mul, ← map_mul]
    congr 1
    have h : x₀ * y₀ = y₀ * x₀ :=
      congrArg Subtype.val ((isMulCommutative_iff.mp hE.1) ⟨x₀, hx₀⟩ ⟨y₀, hy₀⟩)
    exact congrArg Subtype.val h
  have hexp : ∀ x ∈ EL, x ^ 3 = 1 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    rw [← map_pow, ← Subgroup.coe_pow, hE.2 x₀ hx₀, Subgroup.coe_one, map_one]
  have : Finite E₀ :=
    Finite.of_surjective _ ((StatedSp 4 (GaloisField 2 1)).subtype.subgroupMap_surjective E)
  have : Finite EL := Finite.of_surjective _ (Φ.subgroupMap_surjective E₀)
  have hcard : Nat.card EL = Nat.card E := by
    rw [hEL, Subgroup.card_map_of_injective hΦ, hE₀,
      Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  have h3 : (3 : L) ≠ 0 := by
    have h2 : (2 : L) = 0 := CharP.cast_eq_zero L 2
    have : (3 : L) = 1 := by linear_combination h2
    rw [this]
    exact one_ne_zero
  obtain ⟨b, d, hb⟩ := CFSG.RankThree.PartTwo.Sec4.exists_common_eigenbasis_pow_three h3 EL
    hcomm hexp
  set M : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L := (spJ 4 (GaloisField 2 1)).map ι' with hM
  have hMdet : M.det ≠ 0 := by
    have hJ : spJ 4 (GaloisField 2 1) * (-spJ 4 (GaloisField 2 1)) = 1 := by
      rw [Matrix.mul_neg, spJ_mul_spJ, neg_neg]
    have hu := (Matrix.isUnit_det_of_right_inverse hJ).ne_zero
    rw [hM]
    change (ι'.mapMatrix (spJ 4 (GaloisField 2 1))).det ≠ 0
    rw [← RingHom.map_det]
    exact (map_ne_zero ι').mpr hu
  have hiso : ∀ x ∈ EL, (((x : GL (Fin 4 ⊕ Fin 4) L) :
      Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L).map (RingHom.id L))ᵀ * M *
        (x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) = M := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    have h := transpose_mul_mul_of_mem_statedSp x₀.2
    have hid : ∀ N : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L, N.map (RingHom.id L) = N :=
      fun N => by ext i j; rfl
    rw [hid, hΦmat, hM, ← Matrix.transpose_map, ← Matrix.map_mul, ← Matrix.map_mul, h]
  have hpair : ∀ a, ∃ c, sForm (RingHom.id L) M (b a) (b c) ≠ 0 := fun a =>
    exists_sForm_ne_zero (b := b) (RingHom.id L) Function.injective_id hMdet (b.ne_zero a)
  have hinvchar : ∀ a c, sForm (RingHom.id L) M (b a) (b c) ≠ 0 →
      ∀ x ∈ EL, d x c = (d x a)⁻¹ := by
    intro a c hne x hx
    have h1 := sForm_eigen_ne_zero hb (RingHom.id L) M hiso hne hx
    rw [RingHom.id_apply] at h1
    exact eq_inv_of_mul_eq_one_right h1
  have hdist : ∀ a c, (∀ x ∈ EL, d x a = d x c) → a = c := by
    intro a c hac
    by_contra hne
    set C : Finset (EL → L) := Finset.univ.image fun a => fun x : EL => d x a with hCdef
    have hCne : C.card ≠ (Finset.univ : Finset (Fin 4 ⊕ Fin 4)).card := by
      intro h
      exact hne (Finset.card_image_iff.mp h (Finset.mem_coe.mpr (Finset.mem_univ a))
        (Finset.mem_coe.mpr (Finset.mem_univ c)) (funext fun x => hac x x.2))
    have hCle : C.card ≤ (Finset.univ : Finset (Fin 4 ⊕ Fin 4)).card := Finset.card_image_le
    have h8 : (Finset.univ : Finset (Fin 4 ⊕ Fin 4)).card = 8 := by simp
    have hC7 : C.card ≤ 7 := by omega
    have h := CFSG.RankThree.PartTwo.Sec4.card_sq_le_of_characters (G := EL) (K := L) C.card C ⊤
      le_rfl
      (by
        intro χ hχ x _ y _
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
        exact CFSG.RankThree.PartTwo.Sec4.eigen_mul hb x.2 y.2 a)
      (by
        intro χ hχ x _
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
        exact CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb x.2 (hexp x x.2) a)
      (by
        intro χ hχ
        obtain ⟨a, -, rfl⟩ := Finset.mem_image.mp hχ
        obtain ⟨c, hc⟩ := hpair a
        exact ⟨fun x : EL => d x c, Finset.mem_image.mpr ⟨c, Finset.mem_univ _, rfl⟩,
          fun x _ => hinvchar a c hc x x.2⟩)
      (by
        intro x _ hx
        apply Subtype.ext
        rw [Subgroup.coe_one]
        refine CFSG.RankThree.PartTwo.Sec4.eigen_ext hb x.2 EL.one_mem fun a => ?_
        rw [CFSG.RankThree.PartTwo.Sec4.eigen_one hb a]
        exact hx _ (Finset.mem_image.mpr ⟨a, Finset.mem_univ _, rfl⟩))
    rw [Subgroup.card_top, hcard] at h
    have h' : Nat.card E ^ 2 ≤ 3 ^ 7 := h.trans (Nat.pow_le_pow_right (by norm_num) hC7)
    have h'' : (3 ^ 4) ^ 2 ≤ Nat.card E ^ 2 := Nat.pow_le_pow_left h81 2
    norm_num at h' h''
    omega
  have huniq : ∀ a c c', sForm (RingHom.id L) M (b a) (b c) ≠ 0 →
      sForm (RingHom.id L) M (b a) (b c') ≠ 0 → c = c' := fun a c c' hc hc' =>
    hdist c c' fun x hx => by rw [hinvchar a c hc x hx, hinvchar a c' hc' x hx]
  set vL : Fin 4 ⊕ Fin 4 → L := fun i => ι' (v i) with hvL
  have horbL : ∀ x ∈ EL, sForm (RingHom.id L) M
      ((x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) *ᵥ vL) vL = 0 := by
    intro x hx
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    have h0 := hv x₀ hx₀
    rw [spForm_β] at h0
    have hxe : sForm (RingHom.id L) M (((Φ ((x₀ : StatedSp 4 (GaloisField 2 1)) :
        GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1)) : GL (Fin 4 ⊕ Fin 4) L) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) *ᵥ vL) vL =
        ι' (((((x₀ : StatedSp 4 (GaloisField 2 1)) : GL (Fin 4 ⊕ Fin 4) (GaloisField 2 1)) :
          Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) (GaloisField 2 1)) *ᵥ v) ⬝ᵥ
            (spJ 4 (GaloisField 2 1) *ᵥ v)) := by
      rw [RingHom.map_dotProduct]
      simp only [sForm, RingHom.id_apply]
      congr 1
      · funext i
        rw [Function.comp_apply, RingHom.map_mulVec]
        rfl
      · funext i
        rw [Function.comp_apply, RingHom.map_mulVec]
        rfl
    rw [hxe, h0, map_zero]
  have hcoef := coeff_mul_sForm_eq_zero hb hdist (RingHom.id L) Function.injective_id M vL horbL
  have hpartner : ∀ a c, sForm (RingHom.id L) M (b a) (b c) ≠ 0 →
      sForm (RingHom.id L) M (b a) vL =
        b.repr vL c * sForm (RingHom.id L) M (b a) (b c) := by
    intro a c hc
    rw [sForm_eq_sum_right (b := b), Finset.sum_eq_single c (fun c' _ hc' => by
      rw [show sForm (RingHom.id L) M (b a) (b c') = 0 from
        by_contra fun hne => hc' (huniq a c' c hne hc), mul_zero]) (by simp)]
  set φ : L →+* L := frobenius L 2 with hφ
  have hφinj : Function.Injective φ := frobenius_inj L 2
  set vF : (Fin 4 ⊕ Fin 4 → L) → (Fin 4 ⊕ Fin 4 → L) := fun u i => φ (u i) with hvF
  have hφι : ∀ c : GaloisField 2 1, φ (ι' c) = ι' c := fun c => by
    rw [hφ, frobenius_def, ← map_pow, sq_eq_self_galoisField_two]
  have hF1 : ∀ x ∈ EL, ∀ u, (x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) *ᵥ vF u =
      vF ((x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) *ᵥ u) := by
    intro x hx u
    obtain ⟨x₀, hx₀, rfl⟩ := hmemEL x hx
    funext i
    simp only [hvF, Matrix.mulVec, dotProduct, map_sum, map_mul, hΦmat, Matrix.map_apply, hφι]
  have hF2 : vF vL = vL := by
    funext i
    simp only [hvF, hvL, hφι]
  have hF4 : ∀ (w : Fin 4 ⊕ Fin 4 → L) (ψ : GL (Fin 4 ⊕ Fin 4) L → L),
      (∀ x ∈ EL, (x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) *ᵥ w = ψ x • w) →
        ∀ c, b.repr w c ≠ 0 → ∀ x ∈ EL, ψ x = d x c := by
    intro w ψ hw c hc x hx
    have hxw : (x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) *ᵥ w =
        ∑ i, (b.repr w i * d x i) • b i := by
      conv_lhs => rw [← b.sum_repr w]
      rw [Matrix.mulVec_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Matrix.mulVec_smul, hb x hx i, smul_smul]
    have h1 : b.repr ((x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) *ᵥ w) c =
        b.repr w c * d x c := by
      rw [hxw, b.repr_sum_self]
    rw [hw x hx, map_smul, Finsupp.smul_apply, smul_eq_mul] at h1
    exact mul_right_cancel₀ hc (h1.trans (mul_comm _ _))
  have hF5 : ∀ a, ∀ x ∈ EL, (x : Matrix (Fin 4 ⊕ Fin 4) (Fin 4 ⊕ Fin 4) L) *ᵥ vF (b a) =
      (d x a) ^ 2 • vF (b a) := by
    intro a x hx
    rw [hF1 x hx, hb x hx a]
    funext i
    simp only [hvF, Pi.smul_apply, smul_eq_mul, hφ, frobenius_def]
    ring
  have hzero : ∀ a, b.repr vL a = 0 := by
    intro a
    by_contra hca
    obtain ⟨c, hc⟩ := hpair a
    have h1 := hcoef a
    rw [RingHom.id_apply, hpartner a c hc] at h1
    have hcc : b.repr vL c = 0 := by
      have h2 : b.repr vL a * b.repr vL c * sForm (RingHom.id L) M (b a) (b c) = 0 := by
        linear_combination h1
      rcases mul_eq_zero.mp h2 with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hca
        · exact h'
      · exact absurd h hc
    have hchar : ∀ x ∈ EL, (d x a) ^ 2 = d x c := by
      intro x hx
      rw [hinvchar a c hc x hx]
      have h3a := CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb hx (hexp x hx) a
      have hne0 : d x a ≠ 0 := fun h0 => by
        rw [h0] at h3a
        norm_num at h3a
      exact eq_inv_of_mul_eq_one_left (by linear_combination h3a)
    have hcoefF : ∀ a', b.repr (vF (b a')) c ≠ 0 → a' = a := by
      intro a' ha'
      have h1 := hF4 (vF (b a')) (fun x => d x a' ^ 2) (hF5 a') c ha'
      refine hdist a' a fun x hx => ?_
      exact eq_of_sq_eq_of_pow_three
        (CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb hx (hexp x hx) a')
        (CFSG.RankThree.PartTwo.Sec4.eigen_pow_three hb hx (hexp x hx) a)
        ((h1 x hx).trans (hchar x hx).symm)
    have hFa : b.repr (vF (b a)) c ≠ 0 := by
      have hne : vF (b a) ≠ 0 := by
        intro h0
        apply b.ne_zero a
        funext i
        have h := congrFun h0 i
        exact hφinj (by simpa [hvF] using h)
      obtain ⟨c', hc'⟩ : ∃ c', b.repr (vF (b a)) c' ≠ 0 := by
        by_contra hall
        push Not at hall
        apply hne
        rw [← b.sum_repr (vF (b a))]
        simp [hall]
      have h1 := hF4 (vF (b a)) (fun x => d x a ^ 2) (hF5 a) c' hc'
      have hc'c : c' = c := hdist c' c fun x hx => (h1 x hx).symm.trans (hchar x hx)
      rwa [hc'c] at hc'
    have hsum : b.repr vL c = φ (b.repr vL a) * b.repr (vF (b a)) c := by
      have hvFsum : vF vL = ∑ a', φ (b.repr vL a') • vF (b a') := by
        conv_lhs => rw [← b.sum_repr vL]
        funext i
        simp only [hvF, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, map_sum, map_mul]
      calc b.repr vL c = b.repr (vF vL) c := by rw [hF2]
        _ = ∑ a', φ (b.repr vL a') * b.repr (vF (b a')) c := by
            rw [hvFsum, map_sum]
            simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply,
              smul_eq_mul]
        _ = φ (b.repr vL a) * b.repr (vF (b a)) c := by
            refine Finset.sum_eq_single a (fun a' _ ha' => ?_) (by simp)
            rw [show b.repr (vF (b a')) c = 0 from by_contra fun hne => ha' (hcoefF a' hne),
              mul_zero]
    rw [hcc] at hsum
    have hφa : φ (b.repr vL a) ≠ 0 := (map_ne_zero φ).mpr hca
    exact mul_ne_zero hφa hFa hsum.symm
  have hvL0 : vL = 0 := by
    rw [← b.sum_repr vL]
    simp [hzero]
  funext i
  have := congrFun hvL0 i
  exact ι'.injective (by simpa [hvL] using this)

theorem false_of_spEight (E T : Subgroup (StatedSp 4 (GaloisField 2 1)))
    (hE : IsElemAbelian 3 E) (h81 : 3 ^ 4 ≤ Nat.card E) (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : E ≤ Subgroup.normalizer (T : Set (StatedSp 4 (GaloisField 2 1)))) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set ρ := natRep (StatedSp 4 (GaloisField 2 1)) with hρ
  refine false_of_fixSub_inf_perp 2 (spForm 4 (GaloisField 2 1)) ρ
    (isIsometric_natRep_statedSp 4 _) (natRep_injective _) T hT2 hT1 ?_
  rw [eq_bot_iff]
  rintro v ⟨hvW, hvP⟩
  rw [Submodule.mem_bot]
  refine eq_zero_of_orbit_spEight E hE h81 v fun x hx => ?_
  have hxv : ρ x v ∈ fixSub ρ T := apply_mem_fixSub (hET hx) hvW
  have h := ((spForm 4 (GaloisField 2 1)).mem_perp.mp hvP) _ hxv
  rwa [hρ, natRep_apply] at h

end PRankBounds

open PRankBounds in
theorem ggSpEightTwoLocalThreeInput_holds : GGSpEightTwoLocalThreeInput :=
  fun E T hE h81 hT1 hT2 hET => false_of_spEight E T hE h81 hT1 hT2 hET

theorem ggSpSixEightRankInput_holds : GGSpSixEightRankInput :=
  ggSpSixEightRankInput_of_eight ggSpEightTwoLocalThreeInput_holds

end CFSG.StandardType
