module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.LocalAnalysis.StandardType.GGXInLUF2Aux1
public import CFSG.LocalAnalysis.StandardType.GGXInLUF2Aux3

public section

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly

variable {H : Type} [Group H] {N : Subgroup H} [N.Normal] {L' E' : Subgroup H} {n : ℕ}
  {K : Type} [Field K] [Finite K]

private theorem lup8f_f2_exists_eps (F : lup8f_UFrame0 H N L' E' n K) {g : GL (Fin n) K}
    (hg : g ∈ LargeEvenSUGroup (Fin n) K 2) :
    ∃ (l : H) (hl : l ∈ L'),
      g = (F.eps ⟨QuotientGroup.mk' N l, Subgroup.mem_map_of_mem _ hl⟩ : GL (Fin n) K) := by
  obtain ⟨y, hy⟩ := F.eps.surjective ⟨g, hg⟩
  obtain ⟨l, hl, hly⟩ := Subgroup.mem_map.mp y.2
  refine ⟨l, hl, ?_⟩
  have hy' : y = ⟨QuotientGroup.mk' N l, Subgroup.mem_map_of_mem _ hl⟩ := Subtype.ext hly.symm
  rw [← hy', hy]

theorem lup8f_f2_mat_mul_mem_scalars (F : lup8f_UFrame0 H N L' E' n K) (hK : Nat.card K = 4)
    (hn : 3 ≤ n) (b b' : ↥E') :
    (F.mat b * F.mat b')⁻¹ * F.mat (b * b') ∈ LargeEvenScalars (Fin n) K := by
  apply lup8f_f2_mem_scalars_of_commute hK hn
  intro g hg
  obtain ⟨l, hl, rfl⟩ := lup8f_f2_exists_eps F hg
  have hb'l : (b' : H) * l * (b' : H)⁻¹ ∈ L' :=
    (Subgroup.mem_normalizer_iff.mp (F.E'_le_norm b'.2) l).mp hl
  have h1 := F.mat_ind (b * b') ⟨l, hl⟩
  have h2 := F.mat_ind b' ⟨l, hl⟩
  have h3 := F.mat_ind b ⟨(b' : H) * l * (b' : H)⁻¹, hb'l⟩
  have e1 : lup8f_conjLQ N L' E' F.E'_le_norm (b * b') ⟨l, hl⟩ =
      lup8f_conjLQ N L' E' F.E'_le_norm b ⟨(b' : H) * l * (b' : H)⁻¹, hb'l⟩ := by
    apply Subtype.ext
    simp only [lup8f_conjLQ, Subgroup.coe_mul, mul_inv_rev, mul_assoc]
  have e2 : (⟨QuotientGroup.mk' N (((⟨(b' : H) * l * (b' : H)⁻¹, hb'l⟩ : ↥L')) : H),
      Subgroup.mem_map_of_mem _ (⟨(b' : H) * l * (b' : H)⁻¹, hb'l⟩ : ↥L').2⟩ :
        ↥(L'.map (QuotientGroup.mk' N))) = lup8f_conjLQ N L' E' F.E'_le_norm b' ⟨l, hl⟩ := rfl
  rw [e1, h3, e2, h2] at h1
  simp only [MulAut.conj_apply] at h1
  set G0 := (F.eps ⟨QuotientGroup.mk' N l, Subgroup.mem_map_of_mem _ hl⟩ : GL (Fin n) K)
  calc (F.mat b * F.mat b')⁻¹ * F.mat (b * b') * G0
      = (F.mat b * F.mat b')⁻¹ * (F.mat (b * b') * G0 * (F.mat (b * b'))⁻¹) *
          F.mat (b * b') := by group
    _ = (F.mat b * F.mat b')⁻¹ * (F.mat b * (F.mat b' * G0 * (F.mat b')⁻¹) * (F.mat b)⁻¹) *
          F.mat (b * b') := by rw [h1]
    _ = G0 * ((F.mat b * F.mat b')⁻¹ * F.mat (b * b')) := by group

theorem lup8f_f2_commute_of_det_eq_one [Finite H] (F : lup8f_UFrame0 H N L' E' n K)
    (hK : Nat.card K = 4) (hn : 3 ≤ n) (hEp : IsPGroup 3 E')
    (hEc : ∀ e e' : ↥E', e * e' = e' * e) (hNp : Nat.Coprime 3 (Nat.card N)) {x : H}
    (hxL : x ∈ L') (hxE : x ∈ E') (hxN : x ∉ N) (hxc : ∀ l ∈ L', l * x = x * l)
    (hNT : ∀ a ∈ L' ⊓ Subgroup.normalizer (E' : Set H),
      (∀ e ∈ E', e * a * e⁻¹ * a⁻¹ ∈ Subgroup.zpowers x) → ∀ e ∈ E', a * e = e * a)
    {b : ↥E'} (hb : (F.mat b : Matrix (Fin n) (Fin n) K).det = 1) (e : ↥E') :
    F.mat e * F.mat b = F.mat b * F.mat e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZ : LargeEvenScalars (Fin n) K ≤ Subgroup.center (GL (Fin n) K) :=
    (largeEvenScalars_def.trans Matrix.GeneralLinearGroup.center_eq_range_scalar.symm).le
  obtain ⟨ℓ, hℓ, hbℓ⟩ := lup8f_f2_exists_eps F (lup8f_f2_mem_su_of_det_eq_one (F.mat_mem b) hb)
  have hconjL : ∀ e' : ↥E', (e' : H) * ℓ * (e' : H)⁻¹ ∈ L' := fun e' =>
    (Subgroup.mem_normalizer_iff.mp (F.E'_le_norm e'.2) ℓ).mp hℓ
  have hcL : ∀ e' : ↥E', (e' : H) * ℓ * (e' : H)⁻¹ * ℓ⁻¹ ∈ L' := fun e' =>
    L'.mul_mem (hconjL e') (L'.inv_mem hℓ)
  have hcomm_eps : ∀ e' : ↥E', F.mat e' * F.mat b * (F.mat e')⁻¹ * (F.mat b)⁻¹ =
      (F.eps ⟨QuotientGroup.mk' N ((e' : H) * ℓ * (e' : H)⁻¹ * ℓ⁻¹),
        Subgroup.mem_map_of_mem _ (hcL e')⟩ : GL (Fin n) K) := by
    intro e'
    have h := F.mat_ind e' ⟨ℓ, hℓ⟩
    have hsplit : (⟨QuotientGroup.mk' N ((e' : H) * ℓ * (e' : H)⁻¹ * ℓ⁻¹),
        Subgroup.mem_map_of_mem _ (hcL e')⟩ : ↥(L'.map (QuotientGroup.mk' N))) =
        lup8f_conjLQ N L' E' F.E'_le_norm e' ⟨ℓ, hℓ⟩ *
          (⟨QuotientGroup.mk' N ℓ, Subgroup.mem_map_of_mem _ hℓ⟩)⁻¹ := by
      apply Subtype.ext
      simp [lup8f_conjLQ]
    rw [hsplit, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, h, MulAut.conj_apply, hbℓ]
  have hscal : ∀ e' : ↥E', F.mat e' * F.mat b * (F.mat e')⁻¹ * (F.mat b)⁻¹ ∈
      LargeEvenScalars (Fin n) K := by
    intro e'
    have hs1 := lup8f_f2_mat_mul_mem_scalars F hK hn e' b
    have hs2 := lup8f_f2_mat_mul_mem_scalars F hK hn b e'
    rw [hEc b e'] at hs2
    have hc := (LargeEvenScalars (Fin n) K).mul_mem
      ((LargeEvenScalars (Fin n) K).inv_mem hs1) hs2
    have key : F.mat e' * F.mat b * (F.mat e')⁻¹ * (F.mat b)⁻¹ =
        F.mat (e' * b) * (((F.mat e' * F.mat b)⁻¹ * F.mat (e' * b))⁻¹ *
          ((F.mat b * F.mat e')⁻¹ * F.mat (e' * b))) * (F.mat (e' * b))⁻¹ := by group
    rw [key, Subgroup.mem_center_iff.mp (hZ hc), mul_inv_cancel_right]
    exact hc
  have hz0 : (F.eps ⟨QuotientGroup.mk' N x, Subgroup.mem_map_of_mem _ hxL⟩ : GL (Fin n) K) ∈
      LargeEvenScalars (Fin n) K := by
    apply lup8f_f2_mem_scalars_of_commute hK hn
    intro g hg
    obtain ⟨l, hl, rfl⟩ := lup8f_f2_exists_eps F hg
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul]
    congr 2
    apply Subtype.ext
    simp only [Subgroup.coe_mul, ← map_mul, hxc l hl]
  have hz01 : (F.eps ⟨QuotientGroup.mk' N x, Subgroup.mem_map_of_mem _ hxL⟩ : GL (Fin n) K) ≠
      1 := by
    intro h
    have h' := F.eps.injective ((Subtype.ext h).trans (map_one F.eps).symm)
    exact hxN ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h'))
  have hdispQ : ∀ e' ∈ E', QuotientGroup.mk' N (e' * ℓ * e'⁻¹ * ℓ⁻¹) ∈
      Subgroup.zpowers (QuotientGroup.mk' N x) := by
    intro e' he'
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp
      (lup8f_f2_mem_zpowers_of_mem_scalars hK hz0 hz01 (hscal ⟨e', he'⟩))
    rw [hcomm_eps ⟨e', he'⟩, ← Subgroup.coe_zpow, ← map_zpow] at hk
    have h2 := congrArg Subtype.val (F.eps.injective (Subtype.ext hk))
    rw [Subgroup.coe_zpow] at h2
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, h2⟩
  obtain ⟨a, haLN, hal, hdisp⟩ := lup8f_f2_exists_lift F.le_L hNp hEp hxE hℓ hdispQ
  have hcen := hNT a haLN hdisp
  have h1 : QuotientGroup.mk' N ((e : H) * ℓ * (e : H)⁻¹ * ℓ⁻¹) = 1 := by
    have hea : (e : H) * a * (e : H)⁻¹ * a⁻¹ = 1 := by
      rw [← hcen e e.2, mul_inv_cancel_right, mul_inv_cancel]
    simp only [map_mul, map_inv, ← hal]
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hea, map_one]
  have hc1 : F.mat e * F.mat b * (F.mat e)⁻¹ * (F.mat b)⁻¹ = 1 := by
    rw [hcomm_eps e]
    have h3 : (⟨QuotientGroup.mk' N ((e : H) * ℓ * (e : H)⁻¹ * ℓ⁻¹),
        Subgroup.mem_map_of_mem _ (hcL e)⟩ : ↥(L'.map (QuotientGroup.mk' N))) = 1 :=
      Subtype.ext h1
    rw [h3, map_one, Subgroup.coe_one]
  calc F.mat e * F.mat b
      = (F.mat e * F.mat b * (F.mat e)⁻¹ * (F.mat b)⁻¹) * (F.mat b * F.mat e) := by group
    _ = F.mat b * F.mat e := by rw [hc1, one_mul]

end CFSG.StandardType.GGXInL

end
