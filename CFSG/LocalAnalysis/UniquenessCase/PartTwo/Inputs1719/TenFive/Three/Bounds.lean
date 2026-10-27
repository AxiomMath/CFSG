module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Summand
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Counts
import CFSG.Quasithin.Background.B1Coprime
import CFSG.Quasithin.Background.D2RkIdxBounds
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour.Numerics
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SevenFour

variable {W : Type} [CommGroup W] [Finite W]

omit [Finite W] in
private theorem mem_normalizer_center_map {H : Subgroup (MulAut W)} {h : MulAut W} (hh : h ∈ H) :
    h ∈ Subgroup.normalizer (((center ↥H).map H.subtype : Subgroup (MulAut W)) :
      Set (MulAut W)) := by
  have hcentral : ∀ z ∈ ((center ↥H).map H.subtype : Subgroup (MulAut W)), h * z * h⁻¹ = z := by
    intro z hz
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hz
    have hcomm : (⟨h, hh⟩ : ↥H) * c = c * ⟨h, hh⟩ :=
      Subgroup.mem_center_iff.mp hc ⟨h, hh⟩
    have hval : h * H.subtype c = H.subtype c * h := by
      simpa using congrArg Subtype.val hcomm
    rw [hval]
    group
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  refine le_antisymm ?_ ?_
  · rintro z ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, hcentral y hy] using hy
  · intro z hz
    exact ⟨z, hz, by simp [MulAut.conj_apply, hcentral z hz]⟩

theorem twelve_le_rk_commSub_of_isSpecialType (hW : ∀ w : W, w ^ 2 = 1) {N : ℕ}
    {H : Subgroup (MulAut W)} (hH : IsSpecialType 3 1 N ↥H) (hN : 2 ≤ N) {x : MulAut W}
    (hxH : x ∈ H) (hx : orderOf x = 3) : 12 ≤ rk ↥(commSub ⊤ (zpowers x)) := by
  classical
  let E : Subgroup (MulAut W) := (center ↥H).map H.subtype
  have hE3 : Nat.card E = 3 := by
    show Nat.card ((center ↥H).map H.subtype) = 3
    rw [Subgroup.card_map_of_injective H.subtype_injective, hH.2.2.1]
    norm_num
  have hEne : E ≠ ⊥ := by
    intro h
    have h1 : Nat.card E = 1 := by simp [h]
    omega
  have hE : IsElemAbelian 3 E := by
    have hc : IsElemAbelian 3 (center ↥H) := ⟨inferInstance, fun y _ => hH.1 y⟩
    exact CFSG.Open.IsElemAbelian.map hc H.subtype
  have hZcard : Nat.card (center ↥H) = 3 := by
    rw [hH.2.2.1]
    norm_num
  have hDidx : (⊥ : Subgroup ↥H).relIndex (center ↥H) = 3 := by
    have h := Subgroup.relIndex_mul_card (⊥ : Subgroup ↥H) (center ↥H)
    rw [hZcard] at h
    simpa using h
  have hcard : Nat.card (↥H ⧸ (⊥ : Subgroup ↥H)) = 3 ^ (1 + 2 * N) := by
    have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (⊥ : Subgroup ↥H)
    rw [Subgroup.card_bot, mul_one] at h
    rw [← hH.2.1]
    exact h.symm
  have hext : CFSG.IsExtraspecialPGroup 3 (↥H ⧸ (⊥ : Subgroup ↥H)) :=
    hH.2.2.2 (⊥ : Subgroup ↥H) bot_le hDidx
  have hM : StableUnder H (commSub ⊤ E) := by
    intro h hh u hu
    exact mem_commSub_of_mem_normalizer (mem_normalizer_center_map hh) hu
  have hMD : commSub ⊤ E ≤ fixV ((⊥ : Subgroup ↥H).map H.subtype) := by
    rw [Subgroup.map_bot, B1.fixV_bot]
    exact le_top
  have hfree : commSub ⊤ E ⊓ fixV E = ⊥ := commSub_inf_fixV_eq_bot hW (by norm_num) (by norm_num) hE
  have hM1 : commSub ⊤ E ≠ ⊥ := by
    intro hbot
    have hV : commV E = ⊥ := by
      rw [commV_eq_commSub]
      exact hbot
    exact hEne (FixVLat.eq_bot_of_commV_eq_bot hV)
  have hb := summand_bounds hW (p := 3) (N := N) (H := H) (D := ⊥) (M := commSub ⊤ E)
    (by norm_num) (by norm_num) (by omega) bot_le hDidx hext hH.1 hcard hM hMD hfree hM1
  have hd3 : dParam 3 = 2 := dParam_eq_of_small.1
  by_cases hxE : x ∈ E
  · have hEx : E = Subgroup.zpowers x := by
      have hle : Subgroup.zpowers x ≤ E := Subgroup.zpowers_le.mpr hxE
      have hcardz : Nat.card ↥(Subgroup.zpowers x) = 3 := by
        rw [Nat.card_zpowers, hx]
      exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hE3, hcardz])).symm
    rw [← hEx]
    calc 12 ≤ 3 ^ 2 * 2 := by norm_num
      _ ≤ 3 ^ N * 2 := by gcongr
      _ = 3 ^ N * dParam 3 := by rw [hd3]
      _ ≤ rk ↥(commSub ⊤ E) := hb.1
  · have hb2 := hb.2 x hxH hx hxE
    have hmono : rk ↥(commSub (commSub ⊤ E) (Subgroup.zpowers x)) ≤
        rk ↥(commSub ⊤ (Subgroup.zpowers x)) := rk_mono (commSub_mono le_top le_rfl)
    have hpow : 3 ≤ 3 ^ (N - 1) := by
      calc 3 = 3 ^ 1 := (pow_one 3).symm
        _ ≤ 3 ^ (N - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    calc 12 = (3 - 1) * 3 * 2 := by norm_num
      _ ≤ (3 - 1) * 3 ^ (N - 1) * 2 := by gcongr
      _ = (3 - 1) * 3 ^ (N - 1) * dParam 3 := by rw [hd3]
      _ ≤ rk ↥(commSub (commSub ⊤ E) (Subgroup.zpowers x)) := hb2
      _ ≤ rk ↥(commSub ⊤ (Subgroup.zpowers x)) := hmono

theorem six_le_rkIdx_of_inverts_extraGood (hW : ∀ w : W, w ^ 2 = 1) {t x : MulAut W}
    (ht : orderOf t = 2) (hx : orderOf x = 3) (hinv : t * x * t⁻¹ = x⁻¹)
    (hgood : IsExtraGood x) : 6 ≤ rkIdx (fixV (zpowers t)) := by
  obtain ⟨H, N, hxH, hH, hN⟩ := hgood
  have h12 := twelve_le_rk_commSub_of_isSpecialType hW hH hN hxH hx
  have hx3 : x ^ 3 = 1 := by rw [← hx, pow_orderOf_eq_one]
  have hE : IsElemAbelian 3 (Subgroup.zpowers x) := isElemAbelian_zpowers hx3
  have hinv' : ∀ y ∈ Subgroup.zpowers x, t * y * t⁻¹ = y⁻¹ := by
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    have hk := map_zpow (MulAut.conj t) x k
    simp only [MulAut.conj_apply] at hk
    rw [hk, hinv, inv_zpow]
  have hle := rk_commSub_le_two_mul_rkIdx hW (p := 3) (by norm_num) (by norm_num) hE ht hinv'
  omega

omit [Finite W] in
private theorem rkIdx_fixV_zpowers_conj (g y : MulAut W) :
    rkIdx (fixV (Subgroup.zpowers (g * y * g⁻¹))) = rkIdx (fixV (Subgroup.zpowers y)) := by
  unfold rkIdx
  rw [FixVLat.index_fixV_zpowers_conj]

omit [Finite W] in
private theorem closure_insert_finset_insert [DecidableEq (MulAut W)] (t a : MulAut W)
    (s : Finset (MulAut W)) :
    Subgroup.closure (insert t (((insert a s : Finset (MulAut W)) : Set (MulAut W)))) =
      Subgroup.closure (insert t (s : Set (MulAut W))) ⊔ Subgroup.zpowers a := by
  have hset : insert t (((insert a s : Finset (MulAut W)) : Set (MulAut W))) =
      insert t (s : Set (MulAut W)) ∪ {a} := by
    ext x
    simp only [Finset.coe_insert, Set.mem_insert_iff, Set.mem_union, Set.mem_singleton_iff]
    tauto
  rw [hset, Subgroup.closure_union, Subgroup.zpowers_eq_closure]

private theorem rkIdx_fixV_closure_insert_finset_le [DecidableEq (MulAut W)] (t : MulAut W)
    (s : Finset (MulAut W))
    (hconj : ∀ a ∈ s, ∃ g : MulAut W, a = g * t * g⁻¹) :
    rkIdx (fixV (Subgroup.closure (insert t (s : Set (MulAut W))))) ≤
      (s.card + 1) * rkIdx (fixV (Subgroup.zpowers t)) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have hcl : Subgroup.closure (insert t ((∅ : Finset (MulAut W)) : Set (MulAut W))) =
        Subgroup.zpowers t := by
      simpa using (Subgroup.zpowers_eq_closure t).symm
    rw [hcl]
    simp
  | insert a s ha ih =>
    rw [closure_insert_finset_insert, FixVLat.fixV_sup_eq]
    obtain ⟨g, hg⟩ := hconj a (Finset.mem_insert_self a s)
    have hconj' : ∀ b ∈ s, ∃ g : MulAut W, b = g * t * g⁻¹ :=
      fun b hb => hconj b (Finset.mem_insert_of_mem hb)
    have ih' := ih hconj'
    calc rkIdx (fixV (Subgroup.closure (insert t (s : Set (MulAut W)))) ⊓
          fixV (Subgroup.zpowers a))
        ≤ rkIdx (fixV (Subgroup.closure (insert t (s : Set (MulAut W))))) +
            rkIdx (fixV (Subgroup.zpowers a)) := rkIdx_inf_le_add _ _
      _ ≤ (s.card + 1) * rkIdx (fixV (Subgroup.zpowers t)) +
            rkIdx (fixV (Subgroup.zpowers a)) := Nat.add_le_add_right ih' _
      _ = (s.card + 1) * rkIdx (fixV (Subgroup.zpowers t)) +
            rkIdx (fixV (Subgroup.zpowers t)) := by rw [hg, rkIdx_fixV_zpowers_conj]
      _ = ((s.card + 1) + 1) * rkIdx (fixV (Subgroup.zpowers t)) := by ring
      _ = ((insert a s).card + 1) * rkIdx (fixV (Subgroup.zpowers t)) := by
        rw [Finset.card_insert_of_notMem ha]

theorem rkIdx_fixV_closure_conj_le {k : ℕ} (t : MulAut W) (g : Fin k → MulAut W) :
    rkIdx (fixV (closure (insert t (Set.range fun i => (g i)⁻¹ * t * g i)))) ≤
      (k + 1) * rkIdx (fixV (zpowers t)) := by
  classical
  let f : Fin k → MulAut W := fun i => (g i)⁻¹ * t * g i
  let s : Finset (MulAut W) := Finset.univ.image f
  have hcoe : (s : Set (MulAut W)) = Set.range f := by simp [s]
  have hconj : ∀ a ∈ s, ∃ g' : MulAut W, a = g' * t * g'⁻¹ := by
    intro a ha
    obtain ⟨i, hi⟩ := by simpa [s] using ha
    exact ⟨(g i)⁻¹, by rw [← hi, inv_inv]⟩
  have hmain := rkIdx_fixV_closure_insert_finset_le t s hconj
  rw [hcoe] at hmain
  refine hmain.trans (Nat.mul_le_mul_right _ ?_)
  have hcard : s.card ≤ k := by
    calc s.card ≤ (Finset.univ : Finset (Fin k)).card := Finset.card_image_le
      _ = k := by simp
  omega

theorem dParam_le_rkIdx_fixV_zpowers (hW : ∀ w : W, w ^ 2 = 1) {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) {y : MulAut W} (hy : orderOf y = r) :
    dParam r ≤ rkIdx (fixV (zpowers y)) := by
  classical
  have hy1 : y ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy
    exact hr.ne_one hy.symm
  have hYodd : Odd (Nat.card (Subgroup.zpowers y)) := by
    rw [Nat.card_zpowers, hy]
    exact hr.odd_of_ne_two hr2
  obtain ⟨hsup, hinf⟩ := CFSG.Quasithin.B1.coprime_decomp hW hYodd
    (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
  simp only [top_inf_eq] at hsup hinf
  have hMne : commSub ⊤ (Subgroup.zpowers y) ≠ ⊥ := by
    intro hbot
    have hV : commV (Subgroup.zpowers y) = ⊥ := by
      rw [commV_eq_commSub]
      exact hbot
    have hY : Subgroup.zpowers y = ⊥ := FixVLat.eq_bot_of_commV_eq_bot hV
    have hybot : y ∈ (⊥ : Subgroup (MulAut W)) := hY ▸ Subgroup.mem_zpowers y
    exact hy1 (by simpa using hybot)
  have hMstab : ∀ m ∈ commSub ⊤ (Subgroup.zpowers y), y m ∈ commSub ⊤ (Subgroup.zpowers y) :=
    fun m hm => mem_commSub_of_mem_normalizer
      (Subgroup.le_normalizer (Subgroup.mem_zpowers y)) hm
  have hfix : commSub ⊤ (Subgroup.zpowers y) ⊓ fixV (Subgroup.zpowers y) = ⊥ := by
    rw [inf_comm]
    exact hinf
  have hdvd := dParam_dvd_rk hW hr hr2 hy hMstab hfix
  have hpos : 0 < rk ↥(commSub ⊤ (Subgroup.zpowers y)) :=
    Nat.pos_of_ne_zero fun h0 =>
      hMne ((rk_eq_zero_iff hW).mp h0)
  have hle : dParam r ≤ rk ↥(commSub ⊤ (Subgroup.zpowers y)) := Nat.le_of_dvd hpos hdvd
  have hrk : rk ↥(commSub ⊤ (Subgroup.zpowers y)) = rkIdx (fixV (Subgroup.zpowers y)) := by
    have h1 := rk_sup_add_rk_inf (fixV (Subgroup.zpowers y)) (commSub ⊤ (Subgroup.zpowers y))
    rw [hsup, hinf, rk_bot, rk_top, add_zero] at h1
    have h2 := rk_add_rkIdx (fixV (Subgroup.zpowers y))
    omega
  rwa [hrk] at hle

theorem four_le_rkIdx_of_gen (hW : ∀ w : W, w ^ 2 = 1) {t : MulAut W} {k : ℕ}
    (g : Fin k → MulAut W) {y : MulAut W} {r : ℕ} (hr : r.Prime) (hy : orderOf y = r)
    (hyD : y ∈ closure (Set.range fun i => (g i)⁻¹ * (t * g i * t⁻¹)))
    (hd : 3 * (k + 1) < dParam r) : 4 ≤ rkIdx (fixV (zpowers t)) := by
  classical
  have hr2 : r ≠ 2 := by
    intro h2
    subst h2
    have h0 : dParam 2 = 0 := by
      rw [dParam, show (2 : ZMod 2) = 0 from ZMod.natCast_self 2]
      exact orderOf_zero (ZMod 2)
    omega
  let Dg : Subgroup (MulAut W) :=
    closure (insert t (Set.range fun i => (g i)⁻¹ * t * g i))
  have hgen : ∀ i : Fin k, (g i)⁻¹ * (t * g i * t⁻¹) ∈ Dg := by
    intro i
    have h1 : (g i)⁻¹ * t * g i ∈ insert t (Set.range fun j => (g j)⁻¹ * t * g j) :=
      Set.mem_insert_iff.mpr (Or.inr ⟨i, rfl⟩)
    have h1D : (g i)⁻¹ * t * g i ∈ Dg := Subgroup.subset_closure h1
    have htD : t ∈ Dg := Subgroup.subset_closure (Set.mem_insert_iff.mpr (Or.inl rfl))
    have h2 : ((g i)⁻¹ * t * g i) * t⁻¹ ∈ Dg :=
      Subgroup.mul_mem _ h1D (Subgroup.inv_mem _ htD)
    simpa [mul_assoc] using h2
  have hsub : closure (Set.range fun i => (g i)⁻¹ * (t * g i * t⁻¹)) ≤ Dg :=
    (Subgroup.closure_le Dg).2 fun a ha => by
      obtain ⟨i, rfl⟩ := ha
      exact hgen i
  have hyDg : y ∈ Dg := hsub hyD
  have hfixle : fixV Dg ≤ fixV (zpowers y) :=
    B1.fixV_le_fixV (Subgroup.zpowers_le.mpr hyDg)
  have hle1 : rkIdx (fixV (zpowers y)) ≤ rkIdx (fixV Dg) := rkIdx_anti hfixle
  have hle2 : dParam r ≤ rkIdx (fixV (zpowers y)) :=
    dParam_le_rkIdx_fixV_zpowers hW hr hr2 hy
  have hle3 : rkIdx (fixV Dg) ≤ (k + 1) * rkIdx (fixV (zpowers t)) :=
    rkIdx_fixV_closure_conj_le t g
  have hchain : 3 * (k + 1) < (k + 1) * rkIdx (fixV (zpowers t)) :=
    lt_of_lt_of_le hd (hle2.trans (hle1.trans hle3))
  by_contra hcon
  push Not at hcon
  have hmul : (k + 1) * rkIdx (fixV (zpowers t)) ≤ (k + 1) * 3 :=
    Nat.mul_le_mul_left _ (by omega)
  have hk : (k + 1) * 3 = 3 * (k + 1) := Nat.mul_comm _ _
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenFive.Three
