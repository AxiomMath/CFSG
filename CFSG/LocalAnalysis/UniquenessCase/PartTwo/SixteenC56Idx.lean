module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56AsetA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC56Lin2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.Quasithin

namespace OmegaModel

variable {W : Type} [CommGroup W] (S : OmegaModel W)

theorem isSub_fixV_of_aSet {X : Subgroup (MulAut W)}
    (hX : X ≤ Subgroup.normalizer (S.omega : Set (MulAut W))) {A : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet 2 X) : S.IsSub (fixV A) := by
  intro c u hu
  refine mem_fixV.2 fun g hg => ?_
  rw [S.linear_of_mem_aSet_two hX hA g hg c u, mem_fixV.1 hu g hg]

theorem isSub_of_mem_iff_commutator {X : Subgroup (MulAut W)}
    (hX : X ≤ Subgroup.normalizer (S.omega : Set (MulAut W))) {A : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet 2 X) {b : MulAut W} (hbA : b ∈ A) {U : Subgroup W}
    (hU : ∀ x : W, x ∈ U ↔ x * (b x)⁻¹ ∈ fixV A) : S.IsSub U := by
  have hF : S.IsSub (fixV A) := isSub_fixV_of_aSet S hX hA
  have hlin := S.linear_of_mem_aSet_two hX hA
  intro c x hx
  rw [hU]
  have hx' : x * (b x)⁻¹ ∈ fixV A := (hU x).1 hx
  have hx'' : x * b x ∈ fixV A := by
    rwa [inv_eq_of_mul_eq_one_right (S.mul_self_eq_one (b x))] at hx'
  rw [hlin b hbA c x,
    inv_eq_of_mul_eq_one_right (S.mul_self_eq_one (S.smul c (b x)))]
  rw [← S.smul_mul_eq c x (b x)]
  exact hF c (x * b x) hx''

theorem card_eq_mul_pow_of_aSet {X : Subgroup (MulAut W)}
    (hX : X ≤ Subgroup.normalizer (S.omega : Set (MulAut W))) {A : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet 2 X) {b : MulAut W} (hbA : b ∈ A) {U : Subgroup W}
    (hU : ∀ x : W, x ∈ U ↔ x * (b x)⁻¹ ∈ fixV A) :
    ∃ k : ℕ, Nat.card W = Nat.card U * Nat.card S.K ^ k := by
  haveI : Finite W := Finite.of_injective S.vec S.vec_injective
  have hSub : S.IsSub U := isSub_of_mem_iff_commutator S hX hA hbA hU
  obtain ⟨d, hd⟩ := S.exists_card_eq_pow hSub
  have hle : Nat.card U ≤ Nat.card W := Subgroup.card_le_card_group (H := U)
  have hd4 : d ≤ 4 := by
    rw [S.card_eq, hd] at hle
    exact (Nat.pow_le_pow_iff_right (by have := S.four_le; omega)).1 hle
  refine ⟨4 - d, ?_⟩
  rw [S.card_eq, hd, ← pow_add, Nat.add_sub_cancel' hd4]

theorem exists_singular_line_of_fixV {X : Subgroup (MulAut W)}
    (hX : X ≤ Subgroup.normalizer (S.omega : Set (MulAut W))) {A : Subgroup (MulAut W)}
    (hA : A ∈ E3.aSet 2 X) {b : MulAut W} (hbA : b ∈ A) {U : Subgroup W}
    (hU : ∀ x : W, x ∈ U ↔ x * (b x)⁻¹ ∈ fixV A) (hUtop : U ≠ ⊤)
    (hsing : ∀ x ∈ fixV A, S.Q x = 0) :
    ∃ e : W, e ≠ 1 ∧ S.Q e = 0 ∧ ∀ w : W, w ∈ fixV A ↔ ∃ c : S.K, w = S.smul c e := by
  classical
  haveI : Finite W := Finite.of_injective S.vec S.vec_injective
  haveI : Nontrivial W := ⟨⟨1, S.ofVec (Pi.single (Sum.inl 0) 1), fun h => by
    have h1 := congrArg S.vec h
    rw [S.vec_one, S.vec_ofVec] at h1
    have h2 := congrFun h1 (Sum.inl 0)
    simp at h2⟩⟩
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [pow_two]; exact S.mul_self_eq_one w
  have hFsub : S.IsSub (fixV A) := isSub_fixV_of_aSet S hX hA
  have hiso := S.isometry_of_mem_aSet_two hX hA
  have hiso' : ∀ x ∈ fixV A, ∀ y ∈ fixV A, S.pol x y = 0 := fun x hx y hy => by
    simp only [pol]
    rw [hsing (x * y) ((fixV A).mul_mem hx hy), hsing x hx, hsing y hy]
    ring
  have hle_perp : fixV A ≤ S.perp (fixV A) :=
    fun x hx => S.mem_perp.2 fun y hy => hiso' x hx y hy
  have hFne_bot : fixV A ≠ ⊥ := fixV_ne_bot hW2 hA.2.2.1
  obtain ⟨d, hd⟩ := S.exists_card_eq_pow hFsub
  have hcardmul : Nat.card (fixV A) * Nat.card (S.perp (fixV A)) = Nat.card S.K ^ 4 :=
    S.card_mul_card_perp hFsub
  have hFgt1 : 1 < Nat.card (fixV A) := (Subgroup.one_lt_card_iff_ne_bot (fixV A)).2 hFne_bot
  have hd1 : 1 ≤ d := by
    by_contra h
    have h0 : d = 0 := by omega
    rw [hd, h0, pow_zero] at hFgt1
    omega
  have hd2 : d ≤ 2 := by
    have h1 : Nat.card (fixV A) * Nat.card (fixV A) ≤
        Nat.card (fixV A) * Nat.card (S.perp (fixV A)) :=
      Nat.mul_le_mul_left (Nat.card (fixV A)) (Subgroup.card_le_of_le hle_perp)
    rw [hcardmul] at h1
    rw [hd, ← pow_add] at h1
    have h2 : d + d ≤ 4 :=
      (Nat.pow_le_pow_iff_right (by have := S.four_le; omega)).1 h1
    omega
  have hdne2 : d ≠ 2 := by
    intro hd2'
    have hFc : Nat.card (fixV A) = Nat.card S.K ^ 2 := by rw [hd, hd2']
    have hPc : Nat.card (S.perp (fixV A)) = Nat.card S.K ^ 2 := by
      have h : Nat.card S.K ^ 2 * Nat.card (S.perp (fixV A)) =
          Nat.card S.K ^ 2 * Nat.card S.K ^ 2 := by
        calc Nat.card S.K ^ 2 * Nat.card (S.perp (fixV A))
            = Nat.card (fixV A) * Nat.card (S.perp (fixV A)) := by rw [hFc]
          _ = Nat.card S.K ^ 4 := hcardmul
          _ = Nat.card S.K ^ 2 * Nat.card S.K ^ 2 := by ring
      exact Nat.eq_of_mul_eq_mul_left (pow_pos (by have := S.four_le; omega) 2) h
    have hFeq : fixV A = S.perp (fixV A) :=
      Subgroup.eq_of_le_of_card_ge hle_perp (by rw [hPc, hFc])
    have hUtop' : U = ⊤ := by
      rw [Subgroup.eq_top_iff']
      intro x
      rw [hU]
      have hcm : b x * x⁻¹ ∈ S.perp (fixV A) := S.commutator_mem_perp_fixV hiso hbA x
      have hcmF : b x * x⁻¹ ∈ fixV A := by
        rw [hFeq]
        exact hcm
      have hinv := (fixV A).inv_mem hcmF
      simpa [mul_inv_rev] using hinv
    exact hUtop hUtop'
  have hd1' : d = 1 := by omega
  have hFc1 : Nat.card (fixV A) = Nat.card S.K := by rw [hd, hd1', pow_one]
  obtain ⟨e, he_ne, heF⟩ : ∃ e : W, e ≠ 1 ∧ e ∈ fixV A := by
    obtain ⟨u, hu⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hFne_bot
    exact ⟨u, fun h => hu (Subtype.ext h), u.2⟩
  have hne0 : S.vec e ≠ 0 := fun h0 => he_ne (S.vec_injective (by rw [h0, S.vec_one]))
  let ψ : Multiplicative S.K →* W :=
    { toFun := fun c => S.smul (Multiplicative.toAdd c) e
      map_one' := by
        show S.smul (Multiplicative.toAdd (1 : Multiplicative S.K)) e = 1
        rw [show Multiplicative.toAdd (1 : Multiplicative S.K) = 0 from rfl, S.smul_zero_eq]
      map_mul' := fun c c' => by
        show S.smul (Multiplicative.toAdd (c * c')) e =
          S.smul (Multiplicative.toAdd c) e * S.smul (Multiplicative.toAdd c') e
        rw [toAdd_mul, S.smul_add_eq] }
  let L : Subgroup W := ψ.range
  have hLle : L ≤ fixV A := by
    rintro w ⟨c, rfl⟩
    exact hFsub (Multiplicative.toAdd c) e heF
  have hψinj : Function.Injective ψ := by
    intro c c' h
    apply Multiplicative.toAdd.injective
    have h2 : S.smul (Multiplicative.toAdd c) e = S.smul (Multiplicative.toAdd c') e := h
    have h3 := congrArg S.vec h2
    rw [S.vec_smul, S.vec_smul] at h3
    have h4 : (Multiplicative.toAdd c - Multiplicative.toAdd c') • S.vec e = 0 := by
      rw [sub_smul, h3, sub_self]
    obtain ⟨i, hi⟩ : ∃ i, S.vec e i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hne0 (funext hcon)
    have h5 : (Multiplicative.toAdd c - Multiplicative.toAdd c') * S.vec e i = 0 := by
      have := congrFun h4 i
      simpa [Pi.smul_apply, smul_eq_mul] using this
    exact sub_eq_zero.mp ((mul_eq_zero.mp h5).resolve_right hi)
  have hLcard : Nat.card S.K ≤ Nat.card L := by
    rw [← Nat.card_congr Multiplicative.toAdd]
    exact Nat.card_le_card_of_injective (fun c : Multiplicative S.K => (⟨ψ c, ⟨c, rfl⟩⟩ : L))
      (fun a b hab => hψinj (Subtype.ext_iff.mp hab))
  have hLF : L = fixV A :=
    Subgroup.eq_of_le_of_card_ge hLle (by rw [hFc1]; exact hLcard)
  refine ⟨e, he_ne, hsing e heF, ?_⟩
  intro w
  rw [← hLF]
  constructor
  · intro hwL
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hwL
    exact ⟨Multiplicative.toAdd c, by rw [← hc]; rfl⟩
  · rintro ⟨c, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd c, by
      show S.smul (Multiplicative.toAdd (Multiplicative.ofAdd c)) e = S.smul c e
      rw [toAdd_ofAdd]⟩

end OmegaModel

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
