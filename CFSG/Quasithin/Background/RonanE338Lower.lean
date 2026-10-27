module

public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS2

public section

namespace CFSG.Quasithin.RonanE338

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T V M H : Subgroup G}

section ZSat

@[expose] def zSat (Q V : Subgroup G) : Subgroup G :=
  ⨆ n : ↥(Subgroup.normalizer (Q : Set G)), conjSubgroup V (n : G)

theorem conjSubgroup_le_zSat {Q V : Subgroup G} {n : G} (hn : n ∈ Subgroup.normalizer (Q : Set G)) :
    conjSubgroup V n ≤ zSat Q V :=
  le_iSup (fun m : ↥(Subgroup.normalizer (Q : Set G)) => conjSubgroup V (m : G)) ⟨n, hn⟩

theorem le_zSat (Q V : Subgroup G) : V ≤ zSat Q V := by
  have h := conjSubgroup_le_zSat (Q := Q) (V := V) (n := 1) (Subgroup.one_mem _)
  rwa [conjSubgroup_one] at h

theorem zSat_le {Q V X : Subgroup G}
    (h : ∀ n ∈ Subgroup.normalizer (Q : Set G), conjSubgroup V n ≤ X) : zSat Q V ≤ X :=
  iSup_le fun n => h n n.2

theorem normalizer_le_normalizer_zSat (Q V : Subgroup G) :
    Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (zSat Q V : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer (Q : Set G), ∀ x ∈ zSat Q V, m * x * m⁻¹ ∈ zSat Q V := by
    intro m hm x hx
    refine Subgroup.iSup_induction
      (fun n : ↥(Subgroup.normalizer (Q : Set G)) => conjSubgroup V (n : G))
      (C := fun y => m * y * m⁻¹ ∈ zSat Q V) hx ?_ ?_ ?_
    · intro n y hy
      have hnm : (n : G) * m⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
        Subgroup.mul_mem _ n.2 (Subgroup.inv_mem _ hm)
      have hy' : (n : G) * y * (n : G)⁻¹ ∈ V := mem_conjSubgroup_iff.1 hy
      have : m * y * m⁻¹ ∈ conjSubgroup V ((n : G) * m⁻¹) := by
        rw [mem_conjSubgroup_iff]
        simpa [mul_assoc] using hy'
      exact conjSubgroup_le_zSat hnm this
    · simp
    · intro y z hy hz
      simpa [mul_assoc] using Subgroup.mul_mem _ hy hz
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hm x, fun h => ?_⟩
  simpa [mul_assoc] using key m⁻¹ (Subgroup.inv_mem _ hm) _ h

theorem zSat_le_self {Q V : Subgroup G} (hVQ : V ≤ Q) : zSat Q V ≤ Q :=
  zSat_le fun n hn =>
    (conjSubgroup_mono_left n hVQ).trans (conjSubgroup_eq_iff_mem_normalizer.2 hn).le

theorem zSat_le_centralizer {Q V : Subgroup G} (hVQ : V ≤ Subgroup.centralizer (Q : Set G)) :
    zSat Q V ≤ Subgroup.centralizer (Q : Set G) :=
  zSat_le fun n hn => by
    refine (conjSubgroup_mono_left n hVQ).trans ?_
    rw [conjSubgroup_centralizer, conjSubgroup_eq_iff_mem_normalizer.2 hn]

theorem zSat_comm {Q V : Subgroup G} (hVQ : V ≤ Q)
    (hVC : V ≤ Subgroup.centralizer (Q : Set G)) {x y : G} (hx : x ∈ zSat Q V)
    (hy : y ∈ zSat Q V) : x * y = y * x :=
  (Subgroup.mem_centralizer_iff.1 (zSat_le_centralizer hVC hx) y (zSat_le_self hVQ hy)).symm

theorem isElemAbelian_zSat {Q V : Subgroup G} (hV : IsElemAbelian 2 V) (hVQ : V ≤ Q)
    (hVC : V ≤ Subgroup.centralizer (Q : Set G)) : IsElemAbelian 2 (zSat Q V) := by
  refine ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩
  · exact Subtype.ext (zSat_comm hVQ hVC x.2 y.2)
  · refine Subgroup.iSup_induction'
      (fun n : ↥(Subgroup.normalizer (Q : Set G)) => conjSubgroup V (n : G))
      (C := fun y _ => y ^ 2 = 1) ?_ ?_ ?_ hx
    · intro n y hy
      exact (isElemAbelian_conjSubgroup hV n).2 y hy
    · simp
    · intro y z hy hz hy2 hz2
      have hc := zSat_comm hVQ hVC hy hz
      calc (y * z) ^ 2 = y * z * (y * z) := by rw [pow_two]
        _ = y * (z * y) * z := by simp [mul_assoc]
        _ = y * (y * z) * z := by rw [← hc]
        _ = y ^ 2 * z ^ 2 := by simp [pow_two, mul_assoc]
        _ = 1 := by rw [hy2, hz2, one_mul]

end ZSat

section Param

theorem mQuot_inf_le_of_le {V' Z' A : Subgroup G} (hV' : IsPGroup 2 V') (hZ' : IsPGroup 2 Z')
    (h : V' ≤ Z') : mQuot V' (A ⊓ V') ≤ mQuot Z' A := by
  have h1 : mQuot V' (A ⊓ V') = mQuot V' A := by
    unfold mQuot
    rw [Subgroup.inf_relIndex_right]
  rw [h1]
  have h2 : A.relIndex V' ≤ A.relIndex Z' :=
    Subgroup.relIndex_le_of_le_right h (relIndex_ne_zero' Z' A)
  rw [relIndex_eq_two_pow hV' A, relIndex_eq_two_pow hZ' A] at h2
  exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h2

theorem mem_normalizer_zSat_of_forall {Q V : Subgroup G} {x : G}
    (h : ∀ n : ↥(Subgroup.normalizer (Q : Set G)),
      x ∈ Subgroup.normalizer (conjSubgroup V (n : G) : Set G)) :
    x ∈ Subgroup.normalizer (zSat Q V : Set G) := by
  have key : ∀ y ∈ zSat Q V, ∀ z ∈ Subgroup.zpowers x, z * y * z⁻¹ ∈ zSat Q V := by
    intro y hy z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
    refine Subgroup.iSup_induction
      (fun n : ↥(Subgroup.normalizer (Q : Set G)) => conjSubgroup V (n : G))
      (C := fun y => x ^ k * y * (x ^ k)⁻¹ ∈ zSat Q V) hy ?_ ?_ ?_
    · intro n y hyn
      have hxn : x ^ k ∈ Subgroup.normalizer (conjSubgroup V (n : G) : Set G) :=
        Subgroup.zpow_mem _ (h n) k
      exact conjSubgroup_le_zSat n.2 ((Subgroup.mem_normalizer_iff.1 hxn y).1 hyn)
    · simp
    · intro y z hy hz
      simpa [mul_assoc] using Subgroup.mul_mem _ hy hz
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key y hy x (Subgroup.mem_zpowers x), fun hy => ?_⟩
  have := key _ hy x⁻¹ (Subgroup.inv_mem _ (Subgroup.mem_zpowers x))
  simpa [mul_assoc] using this

theorem rParam_le_rParam_zSat {Q V : Subgroup G} (hV : IsElemAbelian 2 V) (hVQ : V ≤ Q)
    (hVC : V ≤ Subgroup.centralizer (Q : Set G)) : rParam V ≤ rParam (zSat Q V) := by
  refine le_iInf₂ fun U hU => ?_
  obtain ⟨hUZ, hnc⟩ := hU
  have hex : ∃ n : ↥(Subgroup.normalizer (Q : Set G)),
      ¬ Subgroup.centralizer (U : Set G) ≤
        Subgroup.normalizer (conjSubgroup V (n : G) : Set G) := by
    by_contra hcon
    push Not at hcon
    exact hnc fun x hx => mem_normalizer_zSat_of_forall fun n => hcon n hx
  obtain ⟨n, hn⟩ := hex
  have hC : ¬ Subgroup.centralizer ((U ⊓ conjSubgroup V (n : G) : Subgroup G) : Set G) ≤
      Subgroup.normalizer (conjSubgroup V (n : G) : Set G) := fun h =>
    hn ((Subgroup.centralizer_le inf_le_left).trans h)
  have h1 := rParam_le_mQuot (inf_le_right : U ⊓ conjSubgroup V (n : G) ≤ conjSubgroup V (n : G)) hC
  rw [rParam_conj] at h1
  refine h1.trans (Nat.cast_le.2 ?_)
  exact mQuot_inf_le_of_le (isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hV) _)
    (B2F.isPGroup_of_isElemAbelian (isElemAbelian_zSat hV hVQ hVC)) (conjSubgroup_le_zSat n.2)

end Param

section Sat

omit [Finite G] in
theorem le_centralizer_self_of_isElemAbelian (hV : IsElemAbelian 2 V) :
    V ≤ Subgroup.centralizer (V : Set G) := fun v hv =>
  Subgroup.mem_centralizer_iff.2 fun w hw => B2F.isElemAbelian_comm hV hw hv

theorem le_inf_centralizer (hV : IsElemAbelian 2 V) (hT : E3.HypE322 T V) :
    V ≤ T ⊓ Subgroup.centralizer (V : Set G) :=
  le_inf hT.le (le_centralizer_self_of_isElemAbelian hV)

omit [Finite G] in
theorem le_centralizer_inf (hV : IsElemAbelian 2 V) :
    V ≤ Subgroup.centralizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
  le_centralizer_iff_comm.1 inf_le_right

theorem inf_centralizer_zSat (hV : IsElemAbelian 2 V) (hT : E3.HypE322 T V) :
    T ⊓ Subgroup.centralizer
        (zSat (T ⊓ Subgroup.centralizer (V : Set G)) V : Set G) =
      T ⊓ Subgroup.centralizer (V : Set G) := by
  refine le_antisymm (inf_le_inf_left _ (Subgroup.centralizer_le (le_zSat _ _)))
    (le_inf inf_le_left ?_)
  exact le_centralizer_iff_comm.1 (zSat_le_centralizer (le_centralizer_inf hV))

theorem hypE322_zSat (hV : IsElemAbelian 2 V) (hT : E3.HypE322 T V) :
    E3.HypE322 T (zSat (T ⊓ Subgroup.centralizer (V : Set G)) V) where
  sylow := hT.sylow
  le := (zSat_le_self (le_inf_centralizer hV hT)).trans inf_le_left
  normal :=
    (B2F.le_normalizer_inf Subgroup.le_normalizer
      (B2F.le_normalizer_centralizer hT.normal)).trans
      (normalizer_le_normalizer_zSat _ _)

theorem normalizer_zSat_le (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hT : E3.HypE322 T V)
    (hM : IsUniqueM
      (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G)) M) :
    Subgroup.normalizer
        (zSat (T ⊓ Subgroup.centralizer (V : Set G)) V : Set G) ≤ M := by
  have hZ2 : IsPGroup 2 (zSat (T ⊓ Subgroup.centralizer (V : Set G)) V) :=
    B2F.isPGroup_of_isElemAbelian
      (isElemAbelian_zSat hV (le_inf_centralizer hV hT) (le_centralizer_inf hV))
  have hZ1 : zSat (T ⊓ Subgroup.centralizer (V : Set G)) V ≠ ⊥ := fun h =>
    hV1 (le_bot_iff.1 ((le_zSat _ V).trans h.le))
  have hloc : IsTwoLocal (Subgroup.normalizer
      (zSat (T ⊓ Subgroup.centralizer (V : Set G)) V : Set G)) := ⟨_, hZ1, hZ2, rfl⟩
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge hloc
  have hMM' : M' = M := hM.2 M' ⟨hM', (normalizer_le_normalizer_zSat _ V).trans hle⟩
  rw [← hMM']
  exact hle

end Sat

section Lower

theorem wClos_zSat_le (hV : IsElemAbelian 2 V) (hT : E3.HypE322 T V) {j : ℕ}
    (hjw : (j : ℕ∞) < wParam T V) (hjr : (j : ℕ∞) < rParam V) :
    wClos (zSat (T ⊓ Subgroup.centralizer (V : Set G)) V) j T ≤
      T ⊓ Subgroup.centralizer (V : Set G) := by
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hw0 : 0 < wParam T V := lt_of_le_of_lt zero_le hjw
  have hV2 : IsPGroup 2 V := B2F.isPGroup_of_isElemAbelian hV
  have hZ : IsElemAbelian 2 (zSat Q V) :=
    isElemAbelian_zSat hV (le_inf_centralizer hV hT) (le_centralizer_inf hV)
  have hZ2 : IsPGroup 2 (zSat Q V) := B2F.isPGroup_of_isElemAbelian hZ
  refine wClos_le_of_forall fun A hA => ?_
  obtain ⟨hAT, g, hAg, hmg⟩ := hA
  refine le_inf hAT ?_
  have key : ∀ n : ↥(Subgroup.normalizer (Q : Set G)),
      conjSubgroup V ((n : G) * g) ≤ Subgroup.centralizer (V : Set G) := by
    intro n
    have hVx : conjSubgroup V ((n : G) * g) ≤ conjSubgroup (zSat Q V) g := by
      have h1 : conjSubgroup (conjSubgroup V (n : G)) g ≤ conjSubgroup (zSat Q V) g :=
        conjSubgroup_mono_left g (conjSubgroup_le_zSat n.2)
      rwa [conjSubgroup_conjSubgroup] at h1
    set x : G := (n : G) * g with hx
    have hVx2 : IsPGroup 2 (conjSubgroup V x) := isPGroup_conjSubgroup hV2 x
    have hZg2 : IsPGroup 2 (conjSubgroup (zSat Q V) g) := isPGroup_conjSubgroup hZ2 g
    have hD : (A ⊓ conjSubgroup V x) ∈
        gammaSet V (mQuot (conjSubgroup V x) (A ⊓ conjSubgroup V x)) T :=
      ⟨inf_le_left.trans hAT, x, inf_le_right, rfl⟩
    have hmj : mQuot (conjSubgroup V x) (A ⊓ conjSubgroup V x) ≤ j := by
      have := mQuot_inf_le_of_le (A := A) hVx2 hZg2 hVx
      rwa [hmg] at this
    have hDC : A ⊓ conjSubgroup V x ≤ Subgroup.centralizer (V : Set G) := by
      have h1 := le_wClos hD
      have h2 := wClos_le_of_lt_wParam (T := T) (V := V)
        (i := mQuot (conjSubgroup V x) (A ⊓ conjSubgroup V x))
        (lt_of_le_of_lt (Nat.cast_le.2 hmj) hjw)
      exact (h1.trans h2).trans inf_le_right
    have hVN : V ≤ Subgroup.normalizer (conjSubgroup V x : Set G) := by
      by_contra hn
      have h1 := e3_4_two hn
      have h2 : mQuot (conjSubgroup V x) (conjSubgroup V x ⊓ Subgroup.centralizer (V : Set G)) ≤
          mQuot (conjSubgroup V x) (A ⊓ conjSubgroup V x) :=
        mQuot_mono (le_inf inf_le_right hDC)
      exact absurd (lt_of_lt_of_le hjr (h1.trans (Nat.cast_le.2 (h2.trans hmj)))) (lt_irrefl _)
    have h25 := e3_25 hV hT hw0 x
    exact h25.2.1.2 (h25.2.2.2 hVN)
  have hZg : conjSubgroup (zSat Q V) g ≤ Subgroup.centralizer (V : Set G) := by
    rw [conjSubgroup_le_iff_le_inv]
    refine zSat_le fun n hn => ?_
    rw [← conjSubgroup_le_iff_le_inv, conjSubgroup_conjSubgroup]
    exact key ⟨n, hn⟩
  exact hAg.trans hZg

theorem min_le_wParam_zSat (hV : IsElemAbelian 2 V) (hT : E3.HypE322 T V) :
    min (wParam T V) (rParam V) ≤
      wParam T (zSat (T ⊓ Subgroup.centralizer (V : Set G)) V) := by
  refine le_iInf₂ fun j hj => ?_
  by_contra hlt
  push Not at hlt
  have h := wClos_zSat_le hV hT (lt_of_lt_of_le hlt (min_le_left _ _))
    (lt_of_lt_of_le hlt (min_le_right _ _))
  exact hj (h.trans (inf_centralizer_zSat hV hT).ge)

theorem min_le_nParam (hV : IsElemAbelian 2 V) (hV1 : V ≠ ⊥) (hyp : E3.HypE336 T V M)
    (hH : IsHStar T M H) : min (wParam T V) (rParam V) ≤ E1.nParam H := by
  set Q := T ⊓ Subgroup.centralizer (V : Set G) with hQ
  have hVQ : V ≤ Q := le_inf_centralizer hV hyp.hyp322
  have hVC : V ≤ Subgroup.centralizer (Q : Set G) := le_centralizer_inf hV
  have hZ : IsElemAbelian 2 (zSat Q V) := isElemAbelian_zSat hV hVQ hVC
  have hZ1 : zSat Q V ≠ ⊥ := fun h => hV1 (le_bot_iff.1 ((le_zSat Q V).trans h.le))
  have hT' := hypE322_zSat hV hyp.hyp322
  have hcent := inf_centralizer_zSat hV hyp.hyp322
  have hM' : IsUniqueM
      (Subgroup.normalizer ((T ⊓ Subgroup.centralizer (zSat Q V : Set G) : Subgroup G) : Set G))
      M := by
    rw [hcent]
    exact hyp.unique
  have hNM := normalizer_zSat_le hV hV1 hyp.hyp322 hyp.unique
  have hCH : H ⊓ Subgroup.centralizer (zSat Q V : Set G) ≤ M :=
    inf_le_right.trans ((Subgroup.centralizer_le_normalizer _).trans hNM)
  refine not_lt.1 fun hlt => hH.2.1 ?_
  have hlt' : E1.nParam H < min (wParam T (zSat Q V)) (rParam (zSat Q V)) :=
    lt_of_lt_of_le hlt (le_min (min_le_wParam_zSat hV hyp.hyp322)
      ((min_le_right _ _).trans (rParam_le_rParam_zSat hV hVQ hVC)))
  exact e3_35_one hZ hZ1 hT' hM'
    (ASInputs.isSylowIn_of_le_top hyp.hyp322.sylow hH.1.1) hCH inf_le_left hlt'

end Lower

end CFSG.Quasithin.RonanE338

end
