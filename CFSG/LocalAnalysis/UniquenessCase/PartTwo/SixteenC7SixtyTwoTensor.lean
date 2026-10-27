module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoModel
public import CFSG.GroupTheory.ABGLocalTools.CoreLemmas

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr CFSG.Quasithin.H13

section Model

private theorem fixV_conj_zpowers {A : Subgroup (MulAut WMod)} {z : WMod}
    (h : fixV A = Subgroup.zpowers z) (k : MulAut WMod) :
    fixV (A.map (MulAut.conj k).toMonoidHom) = Subgroup.zpowers (k z) := by
  have h1 : fixV (A.map (MulAut.conj k).toMonoidHom) = (fixV A).map k.toMonoidHom :=
    fixV_map_conj_eq A k
  have h2 : (fixV A).map k.toMonoidHom = Subgroup.zpowers (k z) := by
    have h3 := congrArg (fun B : Subgroup WMod => B.map k.toMonoidHom) h
    exact h3.trans (MonoidHom.map_zpowers _ _)
  exact h1.trans h2

theorem s16c7_model_data {P : Subgroup (MulAut WMod)}
    (hP : CFSG.ABGLocalTools.IsSylowOf 2 P img) :
    ∃ (z : WMod) (X : Subgroup (MulAut WMod)), z ≠ 1 ∧ z ^ 2 = 1 ∧
      fixV P = Subgroup.zpowers z ∧ X ≤ img ∧ IsPGroup 3 X ∧ Nat.card X = 9 ∧
      fixV X = Subgroup.zpowers z ∧
      Set.ncard {w : WMod | ∃ n ∈ L3Wr.norm, n z = w} ≤ 49 ∧
      ∀ h ∈ img, h z = z → ∃ x ∈ X, ∃ t ∈ P, h = x * t := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite (MulAut WMod) := MulEquiv.finite_left
  obtain ⟨k, hk, hconj⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj s16c7_isSylow_S hP
  have hPeq : P = s16c7_S.map (MulAut.conj k).toMonoidHom := by
    ext x
    rw [Subgroup.mem_map]
    constructor
    · intro hx
      refine ⟨k⁻¹ * x * k, (hconj x).1 hx, ?_⟩
      show k * (k⁻¹ * x * k) * k⁻¹ = x
      group
    · rintro ⟨y, hy, rfl⟩
      rw [hconj]
      have : k⁻¹ * (MulAut.conj k).toMonoidHom y * k = y := by
        show k⁻¹ * (k * y * k⁻¹) * k = y
        group
      rw [this]
      exact hy
  refine ⟨k s16c7_z0, s16c7_K.map (MulAut.conj k).toMonoidHom, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => s16c7_z0_ne_one (k.injective (h.trans (map_one k).symm))
  · have : k (s16c7_z0 ^ 2) = 1 := by rw [s16c7_z0_sq, map_one]
    rwa [map_pow] at this
  · rw [hPeq]
    exact fixV_conj_zpowers s16c7_fixV_S k
  · rintro _ ⟨x, hx, rfl⟩
    exact img.mul_mem (img.mul_mem hk (s16c7_K_le_img hx)) (img.inv_mem hk)
  · exact IsPGroup.of_card (n := 2)
      (by rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, s16c7_card_K]; norm_num)
  · rw [Subgroup.card_map_of_injective (MulAut.conj k).injective, s16c7_card_K]
  · exact fixV_conj_zpowers s16c7_fixV_K k
  · refine le_trans (Set.ncard_le_ncard ?_ (Set.toFinite _)) s16c7_ncard_orbit
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n * k, L3Wr.norm.mul_mem hn (img_le_norm hk), ?_⟩
    rfl
  · intro h hh hz
    have hh' : k⁻¹ * h * k ∈ img := img.mul_mem (img.mul_mem (img.inv_mem hk) hh) hk
    have hz' : (k⁻¹ * h * k) s16c7_z0 = s16c7_z0 := by
      show k⁻¹ (h (k s16c7_z0)) = s16c7_z0
      rw [hz]
      exact MulAut.inv_apply_self _ _ _
    obtain ⟨x, hx, t, ht, hxt⟩ := s16c7_stab hh' hz'
    refine ⟨k * x * k⁻¹, ⟨x, hx, rfl⟩, k * t * k⁻¹, ?_, ?_⟩
    · rw [hconj]
      have : k⁻¹ * (k * t * k⁻¹) * k = t := by group
      rw [this]
      exact ht
    · calc h = k * (k⁻¹ * h * k) * k⁻¹ := by group
        _ = k * (x * t) * k⁻¹ := by rw [hxt]
        _ = k * x * k⁻¹ * (k * t * k⁻¹) := by group

end Model

section Abstract

private theorem zpow_eq_one_or_eq_self {G : Type*} [Group G] {z : G} (hz : z ^ 2 = 1) (k : ℤ) :
    z ^ k = 1 ∨ z ^ k = z := by
  have h2 : z ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, hz]
  obtain ⟨m, rfl | rfl⟩ := Int.even_or_odd' k
  · left
    rw [zpow_mul, h2, one_zpow]
  · right
    rw [zpow_add, zpow_mul, h2, one_zpow, one_mul, zpow_one]

theorem s16c7_tensor_data {W : Type*} [CommGroup W] {H Tb : Subgroup (MulAut W)}
    (hreal : (tensorPairModel SL32 SL32).RealizesMod H)
    (hT : Tb ≤ Subgroup.normalizer (H : Set (MulAut W)))
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 2 (Tb ⊓ H) H) :
    ∃ (z : W) (X : Subgroup (MulAut W)), z ≠ 1 ∧ z ^ 2 = 1 ∧ fixV Tb = Subgroup.zpowers z ∧
      X ≤ H ∧ IsPGroup 3 X ∧ Nat.card X = 9 ∧ fixV X = Subgroup.zpowers z ∧
      Set.ncard {w : W | ∃ n ∈ Subgroup.normalizer (H : Set (MulAut W)), n z = w} ≤ 49 ∧
      ∀ h ∈ H, h z = z → ∃ x ∈ X, ∃ t ∈ Tb ⊓ H, h = x * t := by
  obtain ⟨e, he⟩ := exists_model hreal
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Finite W := Finite.of_equiv WMod e.symm.toEquiv
  haveI : Finite (MulAut W) := MulEquiv.finite_left
  haveI : Finite (MulAut WMod) := MulEquiv.finite_left
  have hP : CFSG.ABGLocalTools.IsSylowOf 2 ((Tb ⊓ H).map (congrHom e)) img := by
    have hP' : CFSG.ABGLocalTools.IsSylowOf 2 ((Tb ⊓ H).map (congrHom e))
        (H.map (congrHom e)) := by
      obtain ⟨hle, hpg, hndvd⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hsyl
      refine CFSG.ABGLocalTools.isSylowOf_iff.2 ⟨Subgroup.map_mono hle, ?_, ?_⟩
      · exact hpg.of_equiv ((Tb ⊓ H).equivMapOfInjective _ (congrHom_injective e))
      · rwa [Subgroup.relIndex_map_map_of_injective _ _ (congrHom_injective e)]
    rwa [he] at hP'
  obtain ⟨z₀, X₀, hz1, hz2, hfixP, hX0, hX3, hX9, hfixX, hcard, hstab⟩ := s16c7_model_data hP
  obtain ⟨X, hXH, hXeq⟩ := exists_eq_map_congrHom e (he ▸ hX0 : X₀ ≤ H.map (congrHom e))
  have hz1' : e.symm z₀ ≠ 1 := fun h => hz1 (by simpa using congrArg e h)
  have hmem : ∀ (A : Subgroup (MulAut W)) (v : W),
      v ∈ fixV A ↔ e v ∈ fixV (A.map (congrHom e)) := by
    intro A v
    have h := mem_fixV_map_congr_equiv e A (e v)
    have h2 : e.symm (e v) = v := e.symm_apply_apply v
    have h3 : e.symm (e v) ∈ fixV A ↔ v ∈ fixV A := by rw [h2]
    exact (h.trans h3).symm
  have hzp : ∀ w : WMod, w ∈ Subgroup.zpowers z₀ → w = 1 ∨ w = z₀ := by
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    exact zpow_eq_one_or_eq_self hz2 k
  have hfixTbH : ∀ v : W, v ∈ fixV (Tb ⊓ H) ↔ v = 1 ∨ v = e.symm z₀ := by
    intro v
    rw [hmem, hfixP]
    constructor
    · intro hv
      rcases hzp _ hv with h | h
      · left
        simpa using congrArg e.symm h
      · right
        exact (e.symm_apply_apply v).symm.trans (by rw [h])
    · rintro (h | h)
      · rw [h, map_one]
        exact Subgroup.one_mem _
      · rw [h, e.apply_symm_apply]
        exact Subgroup.mem_zpowers _
  have hcardX : Nat.card X = 9 :=
    calc Nat.card X = Nat.card ↥(X.map (congrHom e)) := (card_map_congrHom e X).symm
      _ = Nat.card X₀ := by
        rw [hXeq]
        rfl
      _ = 9 := hX9
  have hback : ∀ v : W, (e v = 1 ∨ e v = z₀) → v ∈ Subgroup.zpowers (e.symm z₀) := by
    rintro v (h | h)
    · rw [(MulEquiv.map_eq_one_iff e).1 h]
      exact Subgroup.one_mem _
    · have : v = e.symm z₀ := by rw [← h, e.symm_apply_apply]
      rw [this]
      exact Subgroup.mem_zpowers _
  refine ⟨e.symm z₀, X, hz1', ?_, ?_, hXH, ?_, hcardX, ?_, ?_, ?_⟩
  · have : e (e.symm z₀ ^ 2) = 1 := by rw [map_pow, e.apply_symm_apply, hz2]
    simpa using congrArg e.symm this
  ·
    apply le_antisymm
    · intro v hv
      have hv' : v ∈ fixV (Tb ⊓ H) := mem_fixV.2 fun x hx => mem_fixV.1 hv x hx.1
      rcases (hfixTbH v).1 hv' with h | h
      · rw [h]
        exact Subgroup.one_mem _
      · rw [h]
        exact Subgroup.mem_zpowers _
    · have hz : e.symm z₀ ∈ fixV Tb := by
        refine mem_fixV.2 fun t ht => ?_
        have hzin : e.symm z₀ ∈ fixV (Tb ⊓ H) := (hfixTbH _).2 (Or.inr rfl)
        have htz : t (e.symm z₀) ∈ fixV (Tb ⊓ H) := by
          refine mem_fixV.2 fun s hs => ?_
          have hs' : t⁻¹ * s * t ∈ Tb ⊓ H := by
            refine ⟨Tb.mul_mem (Tb.mul_mem (Tb.inv_mem ht) hs.1) ht, ?_⟩
            have hn := hT (Tb.inv_mem ht)
            have h1 := (Subgroup.mem_normalizer_iff.1 hn s).1 hs.2
            simpa using h1
          have h1 : (t⁻¹ * s * t) (e.symm z₀) = e.symm z₀ := mem_fixV.1 hzin _ hs'
          calc s (t (e.symm z₀)) = t (t⁻¹ (s (t (e.symm z₀)))) := (MulAut.apply_inv_self _ t _).symm
            _ = t ((t⁻¹ * s * t) (e.symm z₀)) := rfl
            _ = t (e.symm z₀) := by rw [h1]
        rcases (hfixTbH _).1 htz with h | h
        · exact absurd (t.injective (h.trans (map_one t).symm)) hz1'
        · exact h
      exact Subgroup.zpowers_le.2 hz
  · exact IsPGroup.of_card (n := 2) (by rw [hcardX]; norm_num)
  ·
    apply le_antisymm
    · intro v hv
      have h1 : e v ∈ fixV X₀ := by
        rw [← hXeq]
        exact (hmem X v).1 hv
      rw [hfixX] at h1
      exact hback v (hzp _ h1)
    · have hz : e.symm z₀ ∈ fixV X := by
        refine (hmem X _).2 ?_
        rw [e.apply_symm_apply, hXeq, hfixX]
        exact Subgroup.mem_zpowers _
      exact Subgroup.zpowers_le.2 hz
  ·
    have h3 : (Subgroup.normalizer (H : Set (MulAut W))).map (congrHom e) =
        Subgroup.normalizer ((H.map (congrHom e) : Subgroup (MulAut WMod)) :
          Set (MulAut WMod)) :=
      Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)
    have h5 := congrArg (fun K : Subgroup (MulAut WMod) => Subgroup.normalizer
      (K : Set (MulAut WMod))) he
    have hN : (Subgroup.normalizer (H : Set (MulAut W))).map (congrHom e) ≤ L3Wr.norm :=
      (le_of_eq h3).trans (le_of_eq h5)
    have hsub : e '' {w : W | ∃ n ∈ Subgroup.normalizer (H : Set (MulAut W)),
        n (e.symm z₀) = w} ⊆ {w : WMod | ∃ n ∈ L3Wr.norm, n z₀ = w} := by
      rintro _ ⟨w, ⟨n, hn, rfl⟩, rfl⟩
      exact ⟨congrHom e n, hN ⟨n, hn, rfl⟩, rfl⟩
    calc Set.ncard {w : W | ∃ n ∈ Subgroup.normalizer (H : Set (MulAut W)), n (e.symm z₀) = w}
        = Set.ncard (e '' {w : W | ∃ n ∈ Subgroup.normalizer (H : Set (MulAut W)),
            n (e.symm z₀) = w}) := (Set.ncard_image_of_injective _ e.injective).symm
      _ ≤ Set.ncard {w : WMod | ∃ n ∈ L3Wr.norm, n z₀ = w} :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ ≤ 49 := hcard
  ·
    intro h hh hz
    have hh' : congrHom e h ∈ img := by
      have : congrHom e h ∈ H.map (congrHom e) := Subgroup.mem_map_of_mem _ hh
      rwa [he] at this
    have hz' : (congrHom e h) z₀ = z₀ := by
      show e (h (e.symm z₀)) = z₀
      rw [hz, e.apply_symm_apply]
    obtain ⟨x', hx', t', ht', hxt⟩ := hstab _ hh' hz'
    rw [← hXeq] at hx'
    obtain ⟨x, hx, rfl⟩ := hx'
    obtain ⟨t, ht, rfl⟩ := ht'
    refine ⟨x, hx, t, ht, congrHom_injective e ?_⟩
    rw [map_mul]
    exact hxt

end Abstract

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
