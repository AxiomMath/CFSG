module

public import CFSG.Quasithin.MS93.S38ESecMod

public section

namespace CFSG.Quasithin.MS93.S38EA

open CFSG.Quasithin CFSG.Quasithin.MS93.S38E
open scoped commutatorElement

section AI

variable {Y : Type*} [CommGroup Y]

theorem aI_inf_le [Finite Y] {E : Subgroup (MulAut Y)} {A A' B : Subgroup Y} (hA : Stab E A)
    (hAA' : A ≤ A') : aI E A (A ⊓ B) ≤ aI E A' B := by
  have h1 : fixRel E A (A ⊓ B) = fixRel E A B := by
    ext w
    simp only [mem_fixRel, Subgroup.mem_inf]
    exact ⟨fun ⟨hw, h⟩ => ⟨hw, fun e he => (h e he).2⟩,
      fun ⟨hw, h⟩ => ⟨hw, fun e he => ⟨A.mul_mem (hA e he w hw) (A.inv_mem hw), h e he⟩⟩⟩
  rw [aI, aI, h1, ← fixRel_inf hAA', Subgroup.inf_relIndex_right]
  exact Subgroup.relIndex_le_of_le_right hAA' (relIndex_ne_zero' _ _)

theorem aI_comap {Y' : Type*} [CommGroup Y'] (φ : Y →* Y') (hφ : Function.Surjective φ)
    {E : Subgroup (MulAut Y)} {E' : Subgroup (MulAut Y')}
    (h1 : ∀ x ∈ E, ∃ x' ∈ E', ∀ y, φ (x y) = x' (φ y))
    (h2 : ∀ x' ∈ E', ∃ x ∈ E, ∀ y, φ (x y) = x' (φ y)) (W N : Subgroup Y') :
    aI E (W.comap φ) (N.comap φ) = aI E' W N := by
  have hfix : fixRel E (W.comap φ) (N.comap φ) = (fixRel E' W N).comap φ := by
    ext y
    simp only [mem_fixRel, Subgroup.mem_comap, map_mul, map_inv]
    constructor
    · rintro ⟨hy, h⟩
      refine ⟨hy, fun x' hx' => ?_⟩
      obtain ⟨x, hx, hxx⟩ := h2 x' hx'
      rw [← hxx]
      exact h x hx
    · rintro ⟨hy, h⟩
      refine ⟨hy, fun x hx => ?_⟩
      obtain ⟨x', hx', hxx⟩ := h1 x hx
      rw [hxx]
      exact h x' hx'
  rw [aI, aI, hfix, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective hφ]

theorem exists_irrSec_nonCent [Finite Y] {X K : Subgroup (MulAut Y)} (hKX : K ≤ X)
    (hKp : ⁅K, K⁆ = K) (n : ℕ) :
    ∀ W N : Subgroup Y, Nat.card W ≤ Nat.card N + n → N ≤ W → Stab X W → Stab X N →
      NonCent K W N → ∃ W' N' : Subgroup Y, N ≤ N' ∧ W' ≤ W ∧ IrrSec X W' N' ∧
        NonCent K W' N' := by
  have hlt : ∀ W N : Subgroup Y, N ≤ W → Stab X W → NonCent K W N → N < W := by
    intro W N hNW hW hnc
    refine lt_of_le_of_ne hNW fun h => ?_
    obtain ⟨k, hk, w, hw, hkw⟩ := hnc
    apply hkw
    rw [h]
    exact W.mul_mem (hW k (hKX hk) w hw) (W.inv_mem hw)
  induction n with
  | zero =>
    intro W N hn hNW hW _ hnc
    have hNW' := hlt W N hNW hW hnc
    have := Subgroup.card_lt_of_lt hNW'
    omega
  | succ n ih =>
    intro W N hn hNW hW hN hnc
    have hNW' := hlt W N hNW hW hnc
    obtain ⟨S, hS, hNS, hSW, hSmin⟩ := exists_minimal hNW' hW
    by_cases hncS : NonCent K S N
    · refine ⟨S, N, le_rfl, hSW, ⟨hNS, hS, hN, fun J hJ h1 h2 => ?_⟩, hncS⟩
      rcases eq_or_lt_of_le h1 with h | h
      · exact Or.inl h.symm
      · exact Or.inr (hSmin J hJ h h2)
    · have htS : ∀ k ∈ K, ∀ w ∈ S, k w * w⁻¹ ∈ N := by
        intro k hk w hw
        by_contra hcon
        exact hncS ⟨k, hk, w, hw, hcon⟩
      have hncW : NonCent K W S := by
        by_contra hnc'
        unfold NonCent at hnc' hnc
        push Not at hnc'
        obtain ⟨k, hk, w, hw, hkw⟩ := hnc
        exact hkw (perfect_trivial_of_two_step hKp (hW.mono hKX) (hN.mono hKX) hnc' htS k hk w hw)
      have hcard : Nat.card W ≤ Nat.card S + n := by
        have := Subgroup.card_lt_of_lt hNS
        omega
      obtain ⟨W', N', hSN', hW'W, hirr, hnc'⟩ := ih W S hcard hSW hW hS hncW
      exact ⟨W', N', hNS.le.trans hSN', hW'W, hirr, hnc'⟩

end AI

section VQ

variable {U₀ : Type*} [Group U₀] {V : Subgroup U₀}
  (hV : ⁅V, V⁆ ≤ Subgroup.centralizer (V : Set U₀))

@[expose] def zc (_hV : ⁅V, V⁆ ≤ Subgroup.centralizer (V : Set U₀)) : Subgroup ↥V :=
  Subgroup.center ↥V

instance zc_normal : (zc hV).Normal := Subgroup.instNormalCenter

theorem mem_zc {z : ↥V} : z ∈ zc hV ↔ ∀ w : ↥V, w * z = z * w := Subgroup.mem_center_iff

theorem commutator_mem_zc (a b : ↥V) : ⁅a, b⁆ ∈ zc hV := by
  rw [mem_zc]
  intro w
  have h := hV (Subgroup.commutator_mem_commutator a.2 b.2)
  have h2 := Subgroup.mem_centralizer_iff.mp h w w.2
  apply Subtype.ext
  simp only [Subgroup.coe_mul]
  have e : ((⁅a, b⁆ : ↥V) : U₀) = ⁅(a : U₀), (b : U₀)⁆ := by
    simp [commutatorElement_def]
  rw [e]
  exact h2

instance zcCommGroup : CommGroup (↥V ⧸ zc hV) :=
  { (QuotientGroup.Quotient.group (zc hV)) with
    mul_comm := fun a b => by
      induction a using QuotientGroup.induction_on with
      | H a =>
        induction b using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have e : (a * b)⁻¹ * (b * a) = ⁅b⁻¹, a⁻¹⁆ := by
            simp only [commutatorElement_def]
            group
          rw [e]
          exact commutator_mem_zc hV _ _ }

abbrev VQ : Type _ := ↥V ⧸ zc hV

theorem zc_le_zLam (lam : ↥⁅V, V⁆ →* ℂˣ) : zc hV ≤ zLam hV lam := by
  intro z hz w
  have hzw : ⁅(z : U₀), (w : U₀)⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val ((mem_zc hV).mp hz w).symm
  show lam (vComm z w) = 1
  have : vComm z w = 1 := Subtype.ext hzw
  rw [this, map_one]

@[expose] noncomputable def vqMap (lam : ↥⁅V, V⁆ →* ℂˣ) : VQ hV →* (↥V ⧸ zLam hV lam) :=
  QuotientGroup.map _ _ (MonoidHom.id ↥V) (zc_le_zLam hV lam)

theorem vqMap_surjective (lam : ↥⁅V, V⁆ →* ℂˣ) : Function.Surjective (vqMap hV lam) := by
  intro y
  induction y using QuotientGroup.induction_on with
  | H v => exact ⟨QuotientGroup.mk v, rfl⟩

variable {G₀ : Subgroup U₀} (hG₀ : G₀ ≤ Subgroup.normalizer (V : Set U₀))

theorem map_conjV_zc (g : ↥G₀) : (zc hV).map (conjV hG₀ g).toMonoidHom = zc hV :=
  Subgroup.map_center_eq (conjV hG₀ g)

@[expose] noncomputable def vqAct : ↥G₀ →* MulAut (VQ hV) where
  toFun g := QuotientGroup.congr _ _ (conjV hG₀ g) (map_conjV_zc hV hG₀ g)
  map_one' := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H v =>
      apply congrArg (QuotientGroup.mk (s := zc hV))
      exact Subtype.ext (by simp [conjV])
  map_mul' g h := by
    ext y
    induction y using QuotientGroup.induction_on with
    | H v =>
      apply congrArg (QuotientGroup.mk (s := zc hV))
      exact Subtype.ext (by simp [conjV, mul_assoc])

theorem vqAct_mk (g : ↥G₀) (v : ↥V) :
    vqAct hV hG₀ g (QuotientGroup.mk v) = QuotientGroup.mk (conjV hG₀ g v) := rfl

end VQ

section EndGame

variable {U₀ : Type*} [Group U₀] {V G₀ Lt Tb Qa E : Subgroup U₀} {e : ℕ}
  (hS : EndSetup V G₀ Lt Tb Qa E e) (lam : ↥⁅V, V⁆ →* ℂˣ)
  (hlam1 : ∀ c : ↥⁅V, V⁆, (c : U₀) ∈ ⁅⁅V, V⁆, Tb⁆ → lam c = 1)

noncomputable abbrev kQ : Subgroup (MulAut (VQ hS.cls2)) :=
  (Lt.subgroupOf G₀).map (vqAct hS.cls2 hS.nV)

noncomputable abbrev eQ : Subgroup (MulAut (VQ hS.cls2)) :=
  (E.subgroupOf G₀).map (vqAct hS.cls2 hS.nV)

theorem vqMap_vqAct (g : ↥G₀) (y : VQ hS.cls2) :
    vqMap hS.cls2 lam (vqAct hS.cls2 hS.nV g y) = hS.rho lam hlam1 g (vqMap hS.cls2 lam y) := by
  induction y using QuotientGroup.induction_on with
  | H v => rfl

theorem range_le_normalizer_kQ :
    (vqAct hS.cls2 hS.nV).range ≤ Subgroup.normalizer (kQ hS : Set (MulAut (VQ hS.cls2))) := by
  rintro _ ⟨g, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  have key : ∀ g : ↥G₀, ∀ k ∈ kQ hS,
      vqAct hS.cls2 hS.nV g * k * (vqAct hS.cls2 hS.nV g)⁻¹ ∈ kQ hS := by
    rintro g _ ⟨l, hl, rfl⟩
    refine ⟨g * l * g⁻¹, ?_, by simp⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hl ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hS.nLt g.2) l).mp hl
  intro k
  refine ⟨key g k, fun hk => ?_⟩
  have := key g⁻¹ _ hk
  simpa [mul_assoc] using this

include hS in
theorem kQ_perfect : ⁅kQ hS, kQ hS⁆ = kQ hS := by
  rw [← Subgroup.map_commutator, hS.subgroupOf_perfect]

include hS in
theorem aI_eQ_le : aI (eQ hS) ⊤ ⊥ ≤ e := by
  have : Finite ↥V := hS.finite_V
  rw [aI_top_bot]
  obtain ⟨R, -, hRe, hRE⟩ := hS.ff
  set Rb : Subgroup (VQ hS.cls2) := (R.subgroupOf V).map (QuotientGroup.mk' (zc hS.cls2))
  have hRb : Rb ≤ fixV (eQ hS) := by
    rintro _ ⟨r, hr, rfl⟩ _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hr hg
    rw [QuotientGroup.mk'_apply, vqAct_mk, QuotientGroup.eq, mem_zc]
    intro w
    have e : (((conjV hS.nV g r)⁻¹ * r : ↥V) : U₀) = ⁅(g : U₀), (r : U₀)⁻¹⁆ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, conjV_apply_coe, commutatorElement_def]
      group
    have hc : ⁅(g : U₀), (r : U₀)⁻¹⁆ ∈ Subgroup.centralizer (V : Set U₀) := by
      apply hRE
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hg (R.inv_mem hr)
    apply Subtype.ext
    show (w : U₀) * (((conjV hS.nV g r)⁻¹ * r : ↥V) : U₀) =
      (((conjV hS.nV g r)⁻¹ * r : ↥V) : U₀) * w
    rw [e]
    exact Subgroup.mem_centralizer_iff.mp hc w w.2
  have h1 : (fixV (eQ hS)).index ∣ Rb.index := Subgroup.index_dvd_of_le hRb
  have h2 : Rb.index ∣ (R.subgroupOf V).index :=
    Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective _)
  have h3 : 0 < (R.subgroupOf V).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  exact (Nat.le_of_dvd h3 (h1.trans h2)).trans hRe

include hS in
theorem comap_fixV_le (he : 2 ≤ e ∧ e ≤ 4) (h4 : (fixV (hS.eS lam hlam1)).index = 4) :
    (fixV (hS.kY lam hlam1)).comap (vqMap hS.cls2 lam) ≤ fixV (kQ hS) := by
  have : Finite ↥G₀ := hS.finite
  have : Finite ↥V := hS.finite_V
  have : Finite (hS.YM lam) := hS.finite_YM lam
  set ρQ := vqAct hS.cls2 hS.nV with hρQ
  set φ := vqMap hS.cls2 lam with hφ
  set ρ := hS.rho lam hlam1 with hρ
  set K := hS.kY lam hlam1 with hK
  set W₀ := commV K with hW₀
  set M₀ := W₀ ⊓ fixV K with hM₀
  set P := (fixV K).comap φ with hP
  set B := fixV (kQ hS) with hB
  have hequiv : ∀ g y, φ (ρQ g y) = ρ g (φ y) := vqMap_vqAct hS lam hlam1
  have hstab : ∀ A : Subgroup (hS.YM lam), Stab ρ.range A → Stab ρQ.range (A.comap φ) := by
    rintro A hA _ ⟨g, rfl⟩ y hy
    rw [Subgroup.mem_comap] at hy ⊢
    rw [hequiv]
    exact hA _ ⟨g, rfl⟩ _ hy
  have hBs : Stab ρQ.range B := stab_fixV (range_le_normalizer_kQ hS)
  have hPs : Stab ρQ.range P := hstab _ (stab_fixV (hS.range_le_normalizer_kY lam hlam1))
  have hW₀s : Stab ρQ.range (W₀.comap φ) := hstab _ (hS.stab_W0 lam hlam1)
  have hEQ : ∀ A, Stab ρQ.range A → Stab (eQ hS) A := fun A hA =>
    hA.mono (Subgroup.map_le_range _ _)
  have hBP : B ≤ P := by
    intro y hy
    rw [Subgroup.mem_comap]
    rintro _ ⟨l, hl, rfl⟩
    rw [← hequiv, hy _ ⟨l, hl, rfl⟩]
  have hc1 : ∀ x ∈ eQ hS, ∃ x' ∈ hS.eY lam hlam1, ∀ y, φ (x y) = x' (φ y) := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨ρ g, ⟨g, hg, rfl⟩, hequiv g⟩
  have hc2 : ∀ x' ∈ hS.eY lam hlam1, ∃ x ∈ eQ hS, ∀ y, φ (x y) = x' (φ y) := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨ρQ g, ⟨g, hg, rfl⟩, hequiv g⟩
  have haS : aI (eQ hS) (W₀.comap φ) (M₀.comap φ) = 4 := by
    rw [aI_comap φ (vqMap_surjective hS.cls2 lam) hc1 hc2, ← h4,
      index_fixV_sec (hS.isInv_W0 lam hlam1) (hS.isInv_M0 lam hlam1) inf_le_left]
  have hcount : 4 * aI (eQ hS) P B ≤ e := by
    have c1 : aI (eQ hS) ⊤ P * aI (eQ hS) P B ≤ aI (eQ hS) ⊤ B :=
      aI_mul_le (hEQ _ hPs) hBP le_top
    have c2 : aI (eQ hS) ⊤ B ≤ aI (eQ hS) ⊤ ⊥ := aI_le_of_le' (hEQ _ hBs) bot_le le_top
    have c3 : aI (eQ hS) (W₀.comap φ) (W₀.comap φ ⊓ P) ≤ aI (eQ hS) ⊤ P :=
      aI_inf_le (hEQ _ hW₀s) le_top
    have c4 : W₀.comap φ ⊓ P = M₀.comap φ := (Subgroup.comap_inf _ _ _).symm
    rw [c4, haS] at c3
    have c5 := aI_eQ_le hS
    calc 4 * aI (eQ hS) P B ≤ aI (eQ hS) ⊤ P * aI (eQ hS) P B := Nat.mul_le_mul_right _ c3
      _ ≤ e := c1.trans (c2.trans c5)
  have hPB1 : aI (eQ hS) P B ≤ 1 := by omega
  by_contra hPB
  have hnc : NonCent (kQ hS) P B := by
    by_contra hnc
    unfold NonCent at hnc
    push Not at hnc
    apply hPB
    intro w hw k hk
    have h1 := perfect_trivial_of_two_step (kQ_perfect hS)
      (hPs.mono (Subgroup.map_le_range _ _)) (stab_bot _) hnc
      (fun k hk w hw => by rw [Subgroup.mem_bot, mul_inv_eq_one]; exact hw k hk) k hk w hw
    rwa [Subgroup.mem_bot, mul_inv_eq_one] at h1
  obtain ⟨W', N', hBN', hW'P, hirr', hnc'⟩ :=
    exists_irrSec_nonCent (X := ρQ.range) (Subgroup.map_le_range _ _) (kQ_perfect hS)
      (Nat.card P) P B (by omega) hBP hPs hBs hnc
  have hfaith := le_relIndex_kerRel_aux ρQ hS.e_le hS.faith W' N' hirr'.2.1 hirr'.2.2.1 hnc'
  rw [hS.e_eq] at hfaith
  have hex : ∃ x ∈ eQ hS, ∃ w ∈ W', x w * w⁻¹ ∉ N' := by
    by_contra hcon
    push Not at hcon
    have hle : (E.subgroupOf G₀).map ρQ ≤ kerRel ((E.subgroupOf G₀).map ρQ) W' N'
        (hirr'.2.2.1.mono (Subgroup.map_le_range _ _)) :=
      fun x hx => ⟨hx, fun w hw => hcon x hx w hw⟩
    rw [Subgroup.relIndex_eq_one.mpr hle] at hfaith
    omega
  obtain ⟨x, hx, w, hw, hxw⟩ := hex
  have h2 := two_le_aI hx hw hxw
  have h3 : aI (eQ hS) W' N' ≤ aI (eQ hS) W' B :=
    aI_le_of_le' (hEQ _ hirr'.2.2.1) hBN' hirr'.1.le
  have h4' : aI (eQ hS) W' B ≤ aI (eQ hS) P B :=
    aI_le_of_le (hEQ _ hirr'.2.1) (hBN'.trans hirr'.1.le) hW'P
  omega

include hS in
theorem commutator_mem_centralizer_of_fix (he : 2 ≤ e ∧ e ≤ 4)
    (h4 : (fixV (hS.eS lam hlam1)).index = 4) (v : ↥V)
    (hv : (QuotientGroup.mk v : hS.YM lam) ∈ fixV (hS.kY lam hlam1)) {l : U₀} (hl : l ∈ Lt) :
    ⁅(v : U₀), l⁆ ∈ Subgroup.centralizer (V : Set U₀) := by
  have hvQ : (QuotientGroup.mk v : VQ hS.cls2) ∈
      (fixV (hS.kY lam hlam1)).comap (vqMap hS.cls2 lam) := hv
  have h1 := comap_fixV_le hS lam hlam1 he h4 hvQ
    (vqAct hS.cls2 hS.nV ⟨l, hS.lt_le hl⟩) ⟨⟨l, hS.lt_le hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
  rw [vqAct_mk, QuotientGroup.eq, mem_zc] at h1
  set z : ↥V := (conjV hS.nV ⟨l, hS.lt_le hl⟩ v)⁻¹ * v with hz
  have hz' : (z : U₀) = (l * (v : U₀) * l⁻¹)⁻¹ * v := rfl
  have hzc : (z : U₀) ∈ Subgroup.centralizer (V : Set U₀) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    exact congrArg Subtype.val (h1 ⟨w, hw⟩)
  have hzv : (v : U₀) * z = z * v := Subgroup.mem_centralizer_iff.mp hzc v v.2
  have e : ⁅(v : U₀), l⁆ = z := by
    have : (v : U₀) * z * (v : U₀)⁻¹ = z := by rw [hzv, mul_inv_cancel_right]
    rw [← this, hz', commutatorElement_def]
    group
  rw [e]
  exact hzc

end EndGame

end CFSG.Quasithin.MS93.S38EA
