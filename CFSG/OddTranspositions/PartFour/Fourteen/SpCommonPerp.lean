module

public import CFSG.LocalAnalysis.WeakClosure81.SevenKSymplectic
import CFSG.OddTranspositions.PartFour.SpLineCount
import CFSG.ClassicalInvolution.Models.SymplecticPairs.Embed
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherSpTools
import CFSG.RankThree.PartOne.KC.SymplecticFullRankTwo
public import CFSG.Open.StatedAPI

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.Open CFSG.RankThree.PartOne.KCSpFull CFSG.RankThree.Classical
  CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther CFSG.LocalAnalysis.WeakClosure81
  CFSG.LocalAnalysis.WeakClosure81.SevenK
open CFSG.ClassicalInvolution.Models.SymplecticPairs (spIncl spEmbed mat_spEmbed spEmbed_injective
  spEmbedMat gram_mul_spIncl exists_sp_apply_eq)
open scoped Matrix

section Block

variable {m n : ℕ} {F : Type} [Field F] {σ : Fin m → Fin n}

private theorem mulVec_spIncl_map (hσ : Function.Injective σ) (v : Fin m ⊕ Fin m → F)
    (x : Fin m ⊕ Fin m) :
    (spIncl (K := F) σ *ᵥ v) (Sum.map σ σ x) = v x := by
  have hinj : Function.Injective (Sum.map σ σ : Fin m ⊕ Fin m → Fin n ⊕ Fin n) :=
    Sum.map_injective.2 ⟨hσ, hσ⟩
  rw [Matrix.mulVec, dotProduct, Finset.sum_eq_single x]
  · simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.spIncl_apply]
  · intro y _ hy
    simp [CFSG.ClassicalInvolution.Models.SymplecticPairs.spIncl_apply, hinj.eq_iff,
      Ne.symm hy]
  · simp

private theorem mulVec_spIncl_of_not_mem (v : Fin m ⊕ Fin m → F) {a : Fin n ⊕ Fin n}
    (ha : a ∉ Set.range (Sum.map σ σ)) : (spIncl (K := F) σ *ᵥ v) a = 0 := by
  rw [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun y _ => ?_
  rw [CFSG.ClassicalInvolution.Models.SymplecticPairs.spIncl_apply,
    if_neg (fun h => ha ⟨y, h.symm⟩), zero_mul]

private theorem spForm_spIncl_mulVec (y : Fin n ⊕ Fin n → F) (w : Fin m ⊕ Fin m → F) :
    spForm n F y (spIncl (K := F) σ *ᵥ w) = spForm m F ((spIncl (K := F) σ)ᵀ *ᵥ y) w := by
  rw [spForm_apply, spForm_apply, Matrix.mulVec_mulVec, gram_mul_spIncl, ← Matrix.mulVec_mulVec,
    Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]

private theorem spEmbed_spTransvection (hσ : Function.Injective σ) (w : Fin m ⊕ Fin m → F)
    (c : F) :
    spEmbed σ hσ (spTransvection w c) = spTransvection (spIncl (K := F) σ *ᵥ w) c := by
  apply spLin_injective
  refine Units.ext (LinearMap.ext fun y => ?_)
  change spEnd (spEmbed σ hσ (spTransvection w c)) y = spEnd (spTransvection _ c) y
  have hM : ∀ z, ((((spTransvection w c : ↥(StatedSp m F)) : GL (Fin m ⊕ Fin m) F) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) - 1) *ᵥ z = (c * spForm m F z w) • w :=
    fun z => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, ← spEnd_apply (spTransvection w c) z,
      spEnd_spTransvection, add_sub_cancel_left]
  have hE : (((spEmbed σ hσ (spTransvection w c) : ↥(StatedSp n F)) : GL (Fin n ⊕ Fin n) F) :
      Matrix (Fin n ⊕ Fin n) (Fin n ⊕ Fin n) F) = spEmbedMat σ
      (((spTransvection w c : ↥(StatedSp m F)) : GL (Fin m ⊕ Fin m) F) :
        Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) F) := rfl
  rw [spEnd_spTransvection, spEnd_apply, hE, spEmbedMat, Matrix.add_mulVec,
    Matrix.one_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hM, Matrix.mulVec_smul,
    spForm_spIncl_mulVec]

private theorem mem_range_map_succ_iff {n : ℕ} (a : Fin (n + 1) ⊕ Fin (n + 1)) :
    a ∈ Set.range (Sum.map (Fin.succ : Fin n → Fin (n + 1)) Fin.succ) ↔
      a ≠ Sum.inl 0 ∧ a ≠ Sum.inr 0 := by
  rcases a with i | i
  · simp only [Set.mem_range, Sum.exists, Sum.map_inl, Sum.map_inr, reduceCtorEq,
      exists_false, or_false, Sum.inl.injEq, ne_eq, not_false_eq_true, and_true]
    exact Fin.exists_succ_eq
  · simp only [Set.mem_range, Sum.exists, Sum.map_inl, Sum.map_inr, reduceCtorEq,
      exists_false, false_or, Sum.inr.injEq, ne_eq, not_false_eq_true, true_and]
    exact Fin.exists_succ_eq

end Block

section Transvection

variable {k : ℕ} {F : Type} [Field F]

private theorem isSymplecticTransvectionIn_spTransvection {e : Fin k ⊕ Fin k → F} (he : e ≠ 0)
    {c : F} (hc : c ≠ 0) : IsSymplecticTransvectionIn k (spTransvection e c) := by
  unfold IsSymplecticTransvectionIn
  set N : Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F :=
    (((spTransvection e c : ↥(StatedSp k F)) : GL (Fin k ⊕ Fin k) F) :
      Matrix (Fin k ⊕ Fin k) (Fin k ⊕ Fin k) F) - 1 with hNdef
  have hN : ∀ y, N *ᵥ y = (c * spForm k F y e) • e := fun y => by
    rw [hNdef, Matrix.sub_mulVec, Matrix.one_mulVec, ← spEnd_apply (spTransvection e c) y,
      spEnd_spTransvection, add_sub_cancel_left]
  have hNeq : N = Matrix.vecMulVec (c • e)
      (CFSG.ClassicalInvolution.Models.SymplecticPairs.gram F k *ᵥ e) := by
    rw [Matrix.ext_iff_mulVec]
    intro y
    rw [hN, Matrix.vecMulVec_mulVec, op_smul_eq_smul, smul_smul, dotProduct_comm,
      ← spForm_apply, mul_comm]
  obtain ⟨y, hy⟩ : ∃ y, spForm k F y e ≠ 0 := by
    by_contra h
    push Not at h
    exact he (spForm_nondegenerate.2 e h)
  refine le_antisymm (hNeq ▸ Matrix.rank_vecMulVec_le _ _) (Nat.pos_of_ne_zero fun h0 => ?_)
  have h1 : LinearMap.range N.mulVecLin = ⊥ := Submodule.finrank_eq_zero.1 h0
  have h2 : N *ᵥ y ∈ LinearMap.range N.mulVecLin := ⟨y, rfl⟩
  rw [h1, Submodule.mem_bot, hN] at h2
  exact smul_ne_zero (mul_ne_zero hc hy) he h2

private theorem spForm_eq_form {k : ℕ} (u v : Fin k ⊕ Fin k → F) :
    spForm k F u v = CFSG.ClassicalInvolution.Models.SymplecticPairs.form u v := by
  rw [spForm_apply]
  rfl

private theorem spEnd_ne_zero {k : ℕ} (g : StatedSp k F) {y : Fin k ⊕ Fin k → F} (hy : y ≠ 0) :
    spEnd g y ≠ 0 := fun h0 => hy (by
  rw [← spEnd_spEnd_inv_apply g⁻¹ y, inv_inv, h0, map_zero])

end Transvection

section Common

variable {n : ℕ} {F : Type} [Field F]

theorem exists_hom_closure_commonCommute [Finite F] [CharP F 2]
    {s u w : StatedSp (n + 1 + 1) F} (hs : IsSymplecticTransvectionIn (n + 1 + 1) s)
    (hu : IsConj s u) (hw : IsConj s w) (huw : ¬ Commute u w) :
    ∃ (Θ : StatedSp (n + 1) F →* StatedSp (n + 1 + 1) F) (t₀ : StatedSp (n + 1) F),
      Function.Injective Θ ∧ IsSymplecticTransvectionIn (n + 1) t₀ ∧
        Θ.range = Subgroup.closure {x | IsConj s x ∧ Commute x u ∧ Commute x w} ∧
        ∀ x, (IsConj s x ∧ Commute x u ∧ Commute x w) ↔ ∃ h, Θ (h * t₀ * h⁻¹) = x := by
  classical
  obtain ⟨a₀, c₀, ha₀, hc₀, rfl⟩ := borel86_spn_eq_spTransvection hs
  have hconj : ∀ x, IsConj (spTransvection a₀ c₀) x ↔ ∃ b, b ≠ 0 ∧ x = spTransvection b c₀ :=
    fun x => Set.ext_iff.mp (setOf_isConj_spTransvection ha₀ c₀) x
  obtain ⟨p, hp, rfl⟩ := (hconj u).mp hu
  obtain ⟨q, hq, rfl⟩ := (hconj w).mp hw
  have hpq : spForm (n + 1 + 1) F p q ≠ 0 := fun h0 =>
    huw ((commute_spTransvection_iff hc₀ hc₀).mpr h0)
  have hS : ∀ x, (IsConj (spTransvection a₀ c₀) x ∧ Commute x (spTransvection p c₀) ∧
      Commute x (spTransvection q c₀)) ↔ ∃ e, e ≠ 0 ∧ spForm (n + 1 + 1) F e p = 0 ∧
        spForm (n + 1 + 1) F e q = 0 ∧ x = spTransvection e c₀ := by
    intro x
    constructor
    · rintro ⟨hx, hxu, hxw⟩
      obtain ⟨e, he, rfl⟩ := (hconj x).mp hx
      exact ⟨e, he, (commute_spTransvection_iff hc₀ hc₀).mp hxu,
        (commute_spTransvection_iff hc₀ hc₀).mp hxw, rfl⟩
    · rintro ⟨e, he, hep, heq, rfl⟩
      exact ⟨(hconj _).mpr ⟨e, he, rfl⟩, (commute_spTransvection_iff hc₀ hc₀).mpr hep,
        (commute_spTransvection_iff hc₀ hc₀).mpr heq⟩
  obtain ⟨l, hl⟩ : ∃ l, l = spForm (n + 1 + 1) F p q := ⟨_, rfl⟩
  have hl0 : l ≠ 0 := hl ▸ hpq
  obtain ⟨g, hg1, hg2⟩ := exists_sp_apply_eq (m := n + 1) p (l⁻¹ • q) (by
    rw [← spForm_eq_form, map_smul, smul_eq_mul, ← hl, inv_mul_cancel₀ hl0])
  have hgp : spEnd g (Pi.single (Sum.inl 0) 1) = p := hg1
  have hgq : spEnd g (Pi.single (Sum.inr 0) 1) = l⁻¹ • q := hg2
  have hq' : ∀ e, spForm (n + 1 + 1) F e q = l * spForm (n + 1 + 1) F e (l⁻¹ • q) := fun e => by
    rw [map_smul, smul_eq_mul, mul_inv_cancel_left₀ hl0]
  have hmem : ∀ e, (spForm (n + 1 + 1) F e p = 0 ∧ spForm (n + 1 + 1) F e q = 0) ↔
      ∃ v, e = spEnd g (spIncl (K := F) (Fin.succ : Fin (n + 1) → Fin (n + 1 + 1)) *ᵥ v) := by
    intro e
    constructor
    · rintro ⟨hep, heq⟩
      obtain ⟨y, hey⟩ : ∃ y, e = spEnd g y := ⟨spEnd g⁻¹ e, (spEnd_spEnd_inv_apply g e).symm⟩
      have hy1 : y (Sum.inr 0) = 0 := by
        have h1 : spForm (n + 1 + 1) F y (Pi.single (Sum.inl 0) 1) = 0 := by
          rw [← spForm_spEnd_spEnd g y, hgp, ← hey]
          exact hep
        rwa [spForm_single_inl_right, neg_eq_zero] at h1
      have hy2 : y (Sum.inl 0) = 0 := by
        have h1 : spForm (n + 1 + 1) F y (Pi.single (Sum.inr 0) 1) = 0 := by
          rw [← spForm_spEnd_spEnd g y, hgq, ← hey, map_smul, smul_eq_mul, heq, mul_zero]
        rwa [spForm_single_inr_right] at h1
      refine ⟨fun x => y (Sum.map Fin.succ Fin.succ x), ?_⟩
      rw [hey]
      congr 1
      funext a
      by_cases ha : a ∈ Set.range (Sum.map (Fin.succ : Fin (n + 1) → Fin (n + 1 + 1)) Fin.succ)
      · obtain ⟨x, rfl⟩ := ha
        exact (mulVec_spIncl_map (Fin.succ_injective _)
          (fun x => y (Sum.map Fin.succ Fin.succ x)) x).symm
      · rw [mulVec_spIncl_of_not_mem _ ha]
        rw [mem_range_map_succ_iff, not_and_or, not_not, not_not] at ha
        rcases ha with rfl | rfl
        · exact hy2
        · exact hy1
    · rintro ⟨v, rfl⟩
      have h1 : (spIncl (K := F) (Fin.succ : Fin (n + 1) → Fin (n + 1 + 1)) *ᵥ v) (Sum.inl 0) =
          0 := mulVec_spIncl_of_not_mem _ (by simp)
      have h2 : (spIncl (K := F) (Fin.succ : Fin (n + 1) → Fin (n + 1 + 1)) *ᵥ v) (Sum.inr 0) =
          0 := mulVec_spIncl_of_not_mem _ (by simp)
      refine ⟨?_, ?_⟩
      · rw [← hgp, spForm_spEnd_spEnd, spForm_single_inl_right, h2, neg_zero]
      · rw [hq', ← hgq, spForm_spEnd_spEnd, spForm_single_inr_right, h1, mul_zero]
  let Θ₀ : StatedSp (n + 1) F →* StatedSp (n + 1 + 1) F :=
    (MulAut.conj g).toMonoidHom.comp (spEmbed (K := F) Fin.succ (Fin.succ_injective (n + 1)))
  have hΘ₀ : ∀ v c, Θ₀ (spTransvection v c) = spTransvection
      (spEnd g (spIncl (K := F) (Fin.succ : Fin (n + 1) → Fin (n + 1 + 1)) *ᵥ v)) c := by
    intro v c
    change g * spEmbed Fin.succ (Fin.succ_injective (n + 1)) (spTransvection v c) * g⁻¹ = _
    rw [spEmbed_spTransvection, conj_spTransvection]
  have hΘinj : Function.Injective Θ₀ :=
    (MulAut.conj g).injective.comp (spEmbed_injective (Fin.succ_injective (n + 1)))
  have he₀ : (Pi.single (Sum.inl 0) 1 : Fin (n + 1) ⊕ Fin (n + 1) → F) ≠ 0 := fun h0 => by
    simpa using congrFun h0 (Sum.inl 0)
  have hne : ∀ v : Fin (n + 1) ⊕ Fin (n + 1) → F, v ≠ 0 →
      spEnd g (spIncl (K := F) (Fin.succ : Fin (n + 1) → Fin (n + 1 + 1)) *ᵥ v) ≠ 0 :=
    fun v hv => spEnd_ne_zero g fun h0 => hv (funext fun x => by
      rw [← mulVec_spIncl_map (Fin.succ_injective (n + 1)) v x, h0]
      rfl)
  refine ⟨Θ₀, spTransvection (Pi.single (Sum.inl 0) 1) c₀, hΘinj,
    isSymplecticTransvectionIn_spTransvection he₀ hc₀, ?_, ?_⟩
  · refine le_antisymm ?_ ((Subgroup.closure_le _).mpr fun x hx => ?_)
    · rw [MonoidHom.range_eq_map, ← closure_spTransvections_eq_top (r := n + 1) (K := F),
        MonoidHom.map_closure]
      refine (Subgroup.closure_le _).mpr ?_
      rintro _ ⟨_, ⟨v, t, rfl⟩, rfl⟩
      rw [SetLike.mem_coe, hΘ₀]
      set y := spEnd g (spIncl (K := F) (Fin.succ : Fin (n + 1) → Fin (n + 1 + 1)) *ᵥ v) with hy
      by_cases hy0 : y = 0
      · rw [hy0, spTransvection_zero_eq_one]
        exact Subgroup.one_mem _
      by_cases ht0 : t = 0
      · rw [ht0, borel86_spn_spTransvection_param_zero]
        exact Subgroup.one_mem _
      obtain ⟨μ, hμ⟩ := FiniteField.isSquare_of_char_two (ringChar.eq F 2) (t / c₀)
      have hμ0 : μ ≠ 0 := by
        rintro rfl
        rw [mul_zero] at hμ
        exact ht0 ((div_eq_zero_iff.mp hμ).resolve_right hc₀)
      have htμ : spTransvection y t = spTransvection (μ • y) c₀ := by
        rw [spTransvection_smul_eq, ← hμ, div_mul_cancel₀ t hc₀]
      rw [htμ]
      have hv := (hmem y).mpr ⟨v, rfl⟩
      refine Subgroup.subset_closure ((hS _).mpr ⟨μ • y, smul_ne_zero hμ0 hy0, ?_, ?_, rfl⟩)
      · rw [map_smul, LinearMap.smul_apply, hv.1, smul_zero]
      · rw [map_smul, LinearMap.smul_apply, hv.2, smul_zero]
    · obtain ⟨e, he, hep, heq, rfl⟩ := (hS x).mp hx
      obtain ⟨v, hv⟩ := (hmem e).mp ⟨hep, heq⟩
      exact ⟨spTransvection v c₀, by rw [hΘ₀, ← hv]⟩
  · intro x
    constructor
    · intro hx
      obtain ⟨e, he, hep, heq, rfl⟩ := (hS x).mp hx
      obtain ⟨v, hv⟩ := (hmem e).mp ⟨hep, heq⟩
      have hv0 : v ≠ 0 := by
        rintro rfl
        apply he
        rw [hv, Matrix.mulVec_zero, map_zero]
      obtain ⟨h, hh⟩ := exists_spEnd_eq he₀ hv0
      exact ⟨h, by rw [conj_spTransvection, hh, hΘ₀, ← hv]⟩
    · rintro ⟨h, rfl⟩
      rw [conj_spTransvection, hΘ₀]
      have hz : spEnd h (Pi.single (Sum.inl 0) 1) ≠ 0 := spEnd_ne_zero h he₀
      exact (hS _).mpr ⟨_, hne _ hz, ((hmem _).mpr ⟨_, rfl⟩).1, ((hmem _).mpr ⟨_, rfl⟩).2, rfl⟩

end Common

section Main

theorem isSymplecticTransvection_closure_commonCommute {X : Type} [Group X]
    (hZ : Subgroup.center X = ⊥) {s : X} {m f : ℕ} (hm : 4 ≤ m)
    (h : IsSymplecticTransvection X m f s) {u w : X} (hu : IsConj s u) (hw : IsConj s w)
    (huw : ¬ Commute u w) :
    ∃ t : X, ∃ ht : t ∈ Subgroup.closure {x | IsConj s x ∧ Commute x u ∧ Commute x w},
      IsConj s t ∧ Commute t u ∧ Commute t w ∧
      IsSymplecticTransvection
        (Subgroup.closure {x | IsConj s x ∧ Commute x u ∧ Commute x w}) (m - 2) f ⟨t, ht⟩ ∧
      (∀ x, (IsConj s x ∧ Commute x u ∧ Commute x w) ↔
        ∃ g ∈ Subgroup.closure {x | IsConj s x ∧ Commute x u ∧ Commute x w},
          g * t * g⁻¹ = x) ∧
      Subgroup.center ↥(Subgroup.closure {x | IsConj s x ∧ Commute x u ∧ Commute x w}) = ⊥ := by
  classical
  obtain ⟨k, hk, F, hFfield, hFfin, hF, e, hrank⟩ := h
  obtain ⟨n, rfl⟩ : ∃ n, k = n + 1 + 1 := ⟨k - 2, by omega⟩
  have : Fintype F := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 :=
    charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card, hF])
  let ψ₀ : X →* StatedSp (n + 1 + 1) F :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψinj : Function.Injective ψ₀ := by
    intro a b hab
    have h1 : QuotientGroup.mk' (Subgroup.center X) a = QuotientGroup.mk' (Subgroup.center X) b :=
      e.injective hab
    rw [QuotientGroup.mk'_eq_mk'] at h1
    obtain ⟨z, hz, hzb⟩ := h1
    rw [hZ, Subgroup.mem_bot] at hz
    rw [hz, mul_one] at hzb
    exact hzb
  have hψsurj : Function.Surjective ψ₀ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  let ψ : X ≃* StatedSp (n + 1 + 1) F := MulEquiv.ofBijective ψ₀ ⟨hψinj, hψsurj⟩
  have hψ : ∀ x, ψ x = e (QuotientGroup.mk x) := fun x => rfl
  have hcomm : ∀ x y : X, Commute x y ↔ Commute (ψ x) (ψ y) := fun x y =>
    ⟨fun h => h.map ψ, fun h => ψ.injective (by rw [map_mul, map_mul]; exact h.eq)⟩
  have hconj : ∀ x y : X, IsConj x y ↔ IsConj (ψ x) (ψ y) := fun x y =>
    ⟨fun h => MonoidHom.map_isConj ψ.toMonoidHom h, fun h => by
      simpa using MonoidHom.map_isConj ψ.symm.toMonoidHom h⟩
  obtain ⟨Θ, t₀, hΘinj, ht₀, hrange, hchar⟩ := exists_hom_closure_commonCommute
    (s := ψ s) (u := ψ u) (w := ψ w) (by rw [hψ]; exact hrank) ((hconj _ _).mp hu)
    ((hconj _ _).mp hw) (fun h => huw ((hcomm _ _).mpr h))
  set S : Set X := {x | IsConj s x ∧ Commute x u ∧ Commute x w} with hSdef
  have hSψ : ∀ x : X, x ∈ S ↔
      ψ x ∈ {y | IsConj (ψ s) y ∧ Commute y (ψ u) ∧ Commute y (ψ w)} := fun x =>
    ⟨fun ⟨a, b, c⟩ => ⟨(hconj _ _).mp a, (hcomm _ _).mp b, (hcomm _ _).mp c⟩,
      fun ⟨a, b, c⟩ => ⟨(hconj _ _).mpr a, (hcomm _ _).mpr b, (hcomm _ _).mpr c⟩⟩
  let Θ' : StatedSp (n + 1) F →* X := ψ.symm.toMonoidHom.comp Θ
  have hΘ' : ∀ y, ψ (Θ' y) = Θ y := fun y => ψ.apply_symm_apply (Θ y)
  have hΘ'inj : Function.Injective Θ' := ψ.symm.injective.comp hΘinj
  have hL : Θ'.range = Subgroup.closure S := by
    rw [MonoidHom.range_comp, hrange, MonoidHom.map_closure]
    congr 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hSψ]
      simpa using hy
    · intro hx
      exact ⟨ψ x, (hSψ x).mp hx, by simp⟩
  have ht_mem : Θ' t₀ ∈ Subgroup.closure S := hL ▸ ⟨t₀, rfl⟩
  have htS : Θ' t₀ ∈ S := by
    rw [hSψ, hΘ']
    exact (hchar (Θ t₀)).mpr ⟨1, by simp⟩
  let Φ : StatedSp (n + 1) F ≃* ↥(Subgroup.closure S) :=
    (MonoidHom.ofInjective hΘ'inj).trans (MulEquiv.subgroupCongr hL)
  have hcenSp : Subgroup.center (StatedSp (n + 1) F) = ⊥ := by
    rw [CFSG.LieType.Universal.Symplectic.center_eq,
      CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSp_eq_bot]
  have hcen : Subgroup.center ↥(Subgroup.closure S) = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).mpr fun z hz => ?_
    obtain ⟨y, rfl⟩ := Φ.surjective z
    have hy : y ∈ Subgroup.center (StatedSp (n + 1) F) := by
      rw [Subgroup.mem_center_iff]
      intro y'
      apply Φ.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hz (Φ y')
    rw [hcenSp, Subgroup.mem_bot] at hy
    rw [hy, map_one]
  refine ⟨Θ' t₀, ht_mem, htS.1, htS.2.1, htS.2.2, ?_, ?_, hcen⟩
  · let e' : ↥(Subgroup.closure S) ⧸ Subgroup.center ↥(Subgroup.closure S) ≃*
        StatedSp (n + 1) F :=
      (QuotientGroup.quotientMulEquivOfEq hcen).trans (QuotientGroup.quotientBot.trans Φ.symm)
    unfold IsSymplecticTransvection
    refine ⟨n + 1, by omega, F, hFfield, hFfin, hF, e', ?_⟩
    have hΦt : Φ t₀ = ⟨Θ' t₀, ht_mem⟩ := Subtype.ext rfl
    have he't : e' (QuotientGroup.mk ⟨Θ' t₀, ht_mem⟩) = t₀ := by
      change Φ.symm ⟨Θ' t₀, ht_mem⟩ = t₀
      rw [← hΦt, MulEquiv.symm_apply_apply]
    rw [he't]
    exact ht₀
  · intro x
    constructor
    · intro hx
      obtain ⟨h, hh⟩ := (hchar (ψ x)).mp ((hSψ x).mp hx)
      refine ⟨Θ' h, hL ▸ ⟨h, rfl⟩, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul]
      apply ψ.injective
      rw [hΘ', hh]
    · rintro ⟨g, hg, rfl⟩
      obtain ⟨h, rfl⟩ : g ∈ Θ'.range := hL ▸ hg
      rw [← map_inv, ← map_mul, ← map_mul]
      refine (hSψ _).mpr ?_
      rw [hΘ']
      exact (hchar _).mpr ⟨h, rfl⟩

end Main

end CFSG.OddTranspositions.PartFour
