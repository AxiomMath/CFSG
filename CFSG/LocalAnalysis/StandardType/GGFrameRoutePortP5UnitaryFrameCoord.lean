module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9U6
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Diagonal.Basic

public section

namespace CFSG.StandardType.FrameRoute.UnitaryModel

open CFSG.ClassicalGroups.UnitaryFlag CFSG.StandardType.LineU

variable {F : Type} [Field F] [Finite F] {m : ℕ}

private lemma exists_pow_val_eq (hF : Nat.card F = 4) {ζ : Fˣ} (hζ : orderOf ζ = 3) (c : Fˣ) :
    ∃ k : ZMod 3, ζ ^ k.val = c := by
  have hcard_units : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  have hcard_zp : Nat.card (Subgroup.zpowers ζ) = 3 := by rw [Nat.card_zpowers, hζ]
  have htop : Subgroup.zpowers ζ = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [hcard_zp, hcard_units]
  have hmem : c ∈ Subgroup.zpowers ζ := by rw [htop]; exact Subgroup.mem_top c
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  refine ⟨(k : ZMod 3), ?_⟩
  calc ζ ^ ((k : ZMod 3).val)
      = ζ ^ (((k : ZMod 3).val : ℤ)) := by rw [zpow_natCast]
    _ = ζ ^ (k % (3 : ℤ)) := by
          rw [ZMod.val_intCast]
          norm_num
    _ = ζ ^ k := by
          have h := zpow_mod_orderOf ζ k
          rw [hζ] at h
          simpa using h
    _ = c := hk

private noncomputable def dlog (hF : Nat.card F = 4) {ζ : Fˣ} (hζ : orderOf ζ = 3) (c : Fˣ) :
    ZMod 3 :=
  Classical.choose (exists_pow_val_eq hF hζ c)

private lemma dlog_spec (hF : Nat.card F = 4) {ζ : Fˣ} (hζ : orderOf ζ = 3) (c : Fˣ) :
    ζ ^ (dlog hF hζ c).val = c :=
  Classical.choose_spec (exists_pow_val_eq hF hζ c)

omit [Finite F] in
private lemma pow_val_add_zeta {ζ : Fˣ} (hζ : orderOf ζ = 3) (a b : ZMod 3) :
    ζ ^ ((a + b).val) = ζ ^ a.val * ζ ^ b.val :=
  CoordSL.pow_val_add (by rw [← hζ]; exact pow_orderOf_eq_one ζ) a b

omit [Finite F] in
private lemma pow_eq_pow_iff_modEq_zeta {ζ : Fˣ} (hζ : orderOf ζ = 3) (a b : ZMod 3) :
    ζ ^ a.val = ζ ^ b.val ↔ a = b := by
  rw [pow_eq_pow_iff_modEq, hζ]
  constructor
  · intro h
    apply ZMod.val_injective 3
    have hmod : a.val % 3 = b.val % 3 := h
    rwa [Nat.mod_eq_of_lt (ZMod.val_lt a), Nat.mod_eq_of_lt (ZMod.val_lt b)] at hmod
  · rintro rfl
    rfl

omit [Finite F] in
private lemma prod_pow_val_zeta {ζ : Fˣ} (hζ : orderOf ζ = 3) (m : ℕ) (v : Fin m → ZMod 3) :
    ∏ i, ζ ^ (v i).val = ζ ^ (∑ i, v i).val := by
  induction m with
  | zero => simp [ZMod.val_zero]
  | succ n ih =>
    rw [Fin.prod_univ_succ, Fin.sum_univ_succ, ih (fun i => v i.succ)]
    rw [pow_val_add_zeta hζ]

omit [Finite F] in
private lemma c_cubes_one (hF : Nat.card F = 4) (c : Fˣ) : c ^ 3 = 1 := by
  have hcard : Nat.card Fˣ = 3 := by rw [Nat.card_units, hF]
  rw [← hcard]
  exact pow_card_eq_one' (x := c)

private lemma mk_pow_mem_inner_iff_forward (hF : Nat.card F = 4) {ζ : Fˣ} (hζ : orderOf ζ = 3)
    (h3 : 3 ∣ m) (v : Fin m → ZMod 3) :
    (QuotientGroup.mk (fun i => ζ ^ (v i).val) : UTorus.Proj F m) ∈ UTorus.inner F m →
      ∑ i, v i = 0 := by
  intro h
  rcases Subgroup.mem_map.mp h with ⟨d, hd, hmd⟩
  have hd_prod : ∏ i, d i = 1 := UTorus.mem_detOne.mp hd
  have h_eq : QuotientGroup.mk' (UTorus.scalars F m) d =
      QuotientGroup.mk' (UTorus.scalars F m) (fun i => ζ ^ (v i).val) := hmd
  change (d : (Fin m → Fˣ) ⧸ UTorus.scalars F m) =
      ((fun i => ζ ^ (v i).val) : (Fin m → Fˣ) ⧸ UTorus.scalars F m) at h_eq
  rw [QuotientGroup.eq] at h_eq
  rw [UTorus.mem_scalars] at h_eq
  rcases h_eq with ⟨c, hc⟩
  have hζ_eq : ∀ i, ζ ^ (v i).val = c * d i := by
    intro i
    have h : (d i)⁻¹ * ζ ^ (v i).val = c := by
      simpa only [Pi.mul_apply, Pi.inv_apply] using hc i
    calc ζ ^ (v i).val = d i * ((d i)⁻¹ * ζ ^ (v i).val) := by group
      _ = d i * c := by rw [h]
      _ = c * d i := by rw [mul_comm]
  have hprod : ∏ i, ζ ^ (v i).val = c ^ m := by
    calc ∏ i, ζ ^ (v i).val = ∏ i, c * d i := by
          apply Finset.prod_congr rfl
          intro i _
          rw [hζ_eq i]
      _ = c ^ m * ∏ i, d i := by
          rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
      _ = c ^ m * 1 := by rw [hd_prod]
      _ = c ^ m := by rw [mul_one]
  have hsum : ζ ^ (∑ i, v i).val = c ^ m := by
    rw [← prod_pow_val_zeta hζ]
    exact hprod
  have hc3 : c ^ 3 = 1 := c_cubes_one hF c
  obtain ⟨k, hk⟩ := h3
  have hcm : c ^ m = 1 := by
    rw [hk, pow_mul, hc3, one_pow]
  rw [hcm] at hsum
  have h_zero : (∑ i, v i) = 0 := by
    have h1 : ζ ^ ((∑ i, v i).val) = ζ ^ (0 : ZMod 3).val := by
      simpa [ZMod.val_zero] using hsum
    exact (pow_eq_pow_iff_modEq_zeta hζ (∑ i, v i) 0).mp h1
  exact h_zero

theorem mk_pow_mem_inner_iff (hF : Nat.card F = 4) {ζ : Fˣ} (hζ : orderOf ζ = 3) (h3 : 3 ∣ m)
    (v : Fin m → ZMod 3) :
    (QuotientGroup.mk (fun i => ζ ^ (v i).val) : UTorus.Proj F m) ∈ UTorus.inner F m ↔
      ∑ i, v i = 0 := by
  constructor
  · exact mk_pow_mem_inner_iff_forward hF hζ h3 v
  · intro h
    have hprod : ∏ i, ζ ^ (v i).val = 1 := by
      rw [prod_pow_val_zeta hζ, h]
      simp [ZMod.val_zero]
    have hd : (fun i => ζ ^ (v i).val) ∈ UTorus.detOne F m := by
      rw [UTorus.mem_detOne]
      exact hprod
    exact Subgroup.mem_map_of_mem (QuotientGroup.mk' (UTorus.scalars F m)) hd

private lemma mk_pow_eq_mk_pow_iff (hF : Nat.card F = 4) {ζ : Fˣ} (hζ : orderOf ζ = 3)
    (v w : Fin m → ZMod 3) :
    (QuotientGroup.mk (fun i => ζ ^ (v i).val) : UTorus.Proj F m) =
        QuotientGroup.mk (fun i => ζ ^ (w i).val) ↔ ∃ c : ZMod 3, ∀ i, v i = w i + c := by
  constructor
  · intro h
    have h' : (QuotientGroup.mk (fun i => ζ ^ (w i).val) : UTorus.Proj F m) =
        QuotientGroup.mk (fun i => ζ ^ (v i).val) := h.symm
    rw [QuotientGroup.eq] at h'
    rw [UTorus.mem_scalars] at h'
    rcases h' with ⟨c, hc⟩
    refine ⟨dlog hF hζ c, fun i => ?_⟩
    have hi : (ζ ^ (w i).val)⁻¹ * ζ ^ (v i).val = c := by
      simpa only [Pi.inv_apply, Pi.mul_apply] using hc i
    have hpow : ζ ^ (v i).val = ζ ^ ((w i + dlog hF hζ c).val) := by
      rw [pow_val_add_zeta hζ]
      calc ζ ^ (v i).val
          = ζ ^ (w i).val * ((ζ ^ (w i).val)⁻¹ * ζ ^ (v i).val) := by group
        _ = ζ ^ (w i).val * c := by rw [hi]
        _ = ζ ^ (w i).val * ζ ^ (dlog hF hζ c).val := by rw [dlog_spec hF hζ c]
    exact (pow_eq_pow_iff_modEq_zeta hζ (v i) (w i + dlog hF hζ c)).mp hpow
  · rintro ⟨c, hc⟩
    have h' : (QuotientGroup.mk (fun i => ζ ^ (w i).val) : UTorus.Proj F m) =
        QuotientGroup.mk (fun i => ζ ^ (v i).val) := by
      apply QuotientGroup.eq.mpr
      rw [UTorus.mem_scalars]
      refine ⟨ζ ^ c.val, fun i => ?_⟩
      rw [Pi.mul_apply, Pi.inv_apply, hc i, pow_val_add_zeta hζ]
      group
    exact h'.symm

section Coord

variable {G : Type} [Group G] {Bs L : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (L : Set G))

private noncomputable def gammaInv {b : G} (hb : b ∈ Bs) : ↥(ggGamma L hN).range :=
  ⟨ggGamma L hN ⟨b⁻¹, Subgroup.inv_mem Bs hb⟩, MonoidHom.mem_range.mpr ⟨_, rfl⟩⟩

private lemma gammaInv_mul {b b' : G} (hb : b ∈ Bs) (hb' : b' ∈ Bs) :
    gammaInv hN (Subgroup.mul_mem Bs hb hb') = gammaInv hN hb' * gammaInv hN hb := by
  apply Subtype.ext
  change ggGamma L hN ⟨(b * b')⁻¹, _⟩ =
    ggGamma L hN ⟨b'⁻¹, _⟩ * ggGamma L hN ⟨b⁻¹, _⟩
  rw [← map_mul]
  congr 1
  apply Subtype.ext
  simp [mul_inv_rev]

private lemma gammaInv_eq_one_iff {b : G} (hb : b ∈ Bs) :
    gammaInv hN hb = 1 ↔ b ∈ Subgroup.centralizer (L : Set G) := by
  have hgg := ggGamma_eq_one_iff (L := L) (hBN := hN)
    (b := ⟨b⁻¹, Subgroup.inv_mem Bs hb⟩)
  constructor
  · intro h
    have h1 : ggGamma L hN ⟨b⁻¹, Subgroup.inv_mem Bs hb⟩ = 1 := by
      have h2 := congrArg (fun x : ↥(ggGamma L hN).range => (x : MulAut ↥L)) h
      exact h2
    have h3 : b⁻¹ ∈ Subgroup.centralizer (L : Set G) := by
      simpa using hgg.mp h1
    simpa using Subgroup.inv_mem (H := Subgroup.centralizer (L : Set G)) h3
  · intro hbcent
    have h3 : b⁻¹ ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.inv_mem (H := Subgroup.centralizer (L : Set G)) hbcent
    have h1 : ggGamma L hN ⟨b⁻¹, Subgroup.inv_mem Bs hb⟩ = 1 := by
      apply hgg.mpr
      simpa using h3
    apply Subtype.ext
    exact h1

private lemma exists_gammaInv_eq (a : ↥(ggGamma L hN).range) :
    ∃ (b : G) (hb : b ∈ Bs), gammaInv hN hb = a := by
  obtain ⟨b₀, hb₀⟩ := MonoidHom.mem_range.mp a.2
  refine ⟨(b₀ : G)⁻¹, Bs.inv_mem b₀.2, ?_⟩
  apply Subtype.ext
  rw [← hb₀]
  change ggGamma L hN ⟨((b₀ : G)⁻¹)⁻¹, _⟩ = ggGamma L hN b₀
  congr 1
  apply Subtype.ext
  simp

variable (hF : Nat.card F = 4) {φ : ↥(unitarySU 2 1 F m) →* ↥L} {ζ : Fˣ} (hζ : orderOf ζ = 3)
  (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin m → F, ActsDiagU φ a t)

private noncomputable def unitaryCoord_t : G → Fin m → Fˣ := by
  classical
  exact fun b =>
    if hb : b ∈ Bs then
      let ht := hdiag (gammaInv hN hb) (gammaInv hN hb).2
      fun i => Units.mk0 (ht.choose i) (ht.choose_spec.ne_zero i)
    else fun _ => 1

private noncomputable def unitaryCoord_u : G → Fin m → ZMod 3 :=
  fun b i => dlog hF hζ (unitaryCoord_t hN hdiag b i)

private lemma actsDiagU_unitaryCoord {b : G} (hb : b ∈ Bs) :
    ActsDiagU φ (gammaInv hN hb : MulAut ↥L)
      (fun i => ((ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val : Fˣ) : F)) := by
  classical
  have hchoose := (hdiag (gammaInv hN hb) (gammaInv hN hb).2).choose_spec
  have hfun : (fun i => ((ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val : Fˣ) : F)) =
      (hdiag (gammaInv hN hb) (gammaInv hN hb).2).choose := by
    funext i
    simp only [unitaryCoord_u, unitaryCoord_t, dif_pos hb, dlog_spec hF hζ,
      Units.val_mk0]
  rw [hfun]
  exact hchoose

private lemma unitaryCoord_conj {b : G} (hb : b ∈ Bs) (s s' : ↥(unitarySU 2 1 F m))
    (hs : (s' : GL (Fin m) F) =
      TauCeti.diagGL (fun i => ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val) * s *
        (TauCeti.diagGL (fun i => ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val))⁻¹) :
    ((φ s' : ↥L) : G) = b⁻¹ * φ s * b := by
  obtain ⟨D, hD, hDmat, hact⟩ := actsDiagU_unitaryCoord hN hF hζ hdiag hb
  have hD_eq : D = TauCeti.diagGL
      (fun i => ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val) := by
    apply Units.ext
    rw [hDmat, TauCeti.diagGL_coe]
  have hs' : s' = conjN D hD s := by
    apply Subtype.ext
    rw [coe_conjN, hs, hD_eq]
  have h1 := hact s
  rw [← hs'] at h1
  rw [← h1]
  change ((ggGamma L hN ⟨b⁻¹, Subgroup.inv_mem Bs hb⟩ (φ s) : ↥L) : G) =
    b⁻¹ * (φ s : G) * b
  rw [ggGamma_coe]
  simp

variable {hN hF hζ hdiag} (ι : ↥(ggGamma L hN).range →* UTorus.Proj F m)

private lemma ι_gammaInv
    (hι : ∀ (a : ↥(ggGamma L hN).range) (t : Fin m → Fˣ),
      ActsDiagU φ (a : MulAut ↥L) (fun i => (t i : F)) → ι a = QuotientGroup.mk t)
    {b : G} (hb : b ∈ Bs) :
    ι (gammaInv hN hb) =
      QuotientGroup.mk (fun i => ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val) := by
  exact hι (gammaInv hN hb) (fun i => ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val)
    (actsDiagU_unitaryCoord hN hF hζ hdiag hb)

private lemma unitaryCoord_mul
    (hι : ∀ (a : ↥(ggGamma L hN).range) (t : Fin m → Fˣ),
      ActsDiagU φ (a : MulAut ↥L) (fun i => (t i : F)) → ι a = QuotientGroup.mk t)
    {b b' : G} (hb : b ∈ Bs) (hb' : b' ∈ Bs) :
    ∃ c : ZMod 3, ∀ i, unitaryCoord_u hN hF hζ hdiag (b * b') i =
      unitaryCoord_u hN hF hζ hdiag b i + unitaryCoord_u hN hF hζ hdiag b' i + c := by
  have h2 : ι (gammaInv hN (Subgroup.mul_mem Bs hb hb')) =
      ι (gammaInv hN hb') * ι (gammaInv hN hb) := by
    rw [gammaInv_mul hN hb hb', map_mul]
  rw [ι_gammaInv (hF := hF) (hζ := hζ) (hdiag := hdiag) ι hι
      (Subgroup.mul_mem Bs hb hb'),
    ι_gammaInv (hF := hF) (hζ := hζ) (hdiag := hdiag) ι hι hb',
    ι_gammaInv (hF := hF) (hζ := hζ) (hdiag := hdiag) ι hι hb,
    ← QuotientGroup.mk_mul] at h2
  have hfun : ((fun i => ζ ^ (unitaryCoord_u hN hF hζ hdiag b' i).val) *
      (fun i => ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val) : Fin m → Fˣ) =
      (fun i => ζ ^ ((unitaryCoord_u hN hF hζ hdiag b i +
        unitaryCoord_u hN hF hζ hdiag b' i).val)) := by
    funext i
    rw [Pi.mul_apply, pow_val_add_zeta hζ, mul_comm]
  rw [hfun] at h2
  obtain ⟨c, hc⟩ := (mk_pow_eq_mk_pow_iff hF hζ
    (fun i => unitaryCoord_u hN hF hζ hdiag (b * b') i)
    (fun i => unitaryCoord_u hN hF hζ hdiag b i +
      unitaryCoord_u hN hF hζ hdiag b' i)).mp h2
  exact ⟨c, hc⟩

private lemma unitaryCoord_const_iff
    (hι : ∀ (a : ↥(ggGamma L hN).range) (t : Fin m → Fˣ),
      ActsDiagU φ (a : MulAut ↥L) (fun i => (t i : F)) → ι a = QuotientGroup.mk t)
    (hιinj : Function.Injective ι) {b : G} (hb : b ∈ Bs) :
    (∃ c : ZMod 3, ∀ i, unitaryCoord_u hN hF hζ hdiag b i = c) ↔
      b ∈ Subgroup.centralizer (L : Set G) := by
  have hzero : (QuotientGroup.mk (fun i => ζ ^ ((0 : Fin m → ZMod 3) i).val) :
      UTorus.Proj F m) = 1 := by
    have hfun : (fun i => ζ ^ ((0 : Fin m → ZMod 3) i).val) = 1 := by
      funext i
      simp
    rw [hfun, QuotientGroup.mk_one]
  have h1 : (∃ c : ZMod 3, ∀ i, unitaryCoord_u hN hF hζ hdiag b i = c) ↔
      (QuotientGroup.mk (fun i => ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val) :
        UTorus.Proj F m) = 1 := by
    rw [← hzero, mk_pow_eq_mk_pow_iff hF hζ]
    simp
  rw [h1]
  have h7 := ι_gammaInv (hF := hF) (hζ := hζ) (hdiag := hdiag) ι hι hb
  constructor
  · intro h
    have h2 : ι (gammaInv hN hb) = 1 := h7.trans h
    have h3 : gammaInv hN hb = 1 := hιinj (h2.trans (map_one ι).symm)
    exact (gammaInv_eq_one_iff hN hb).mp h3
  · intro hbcent
    have h3 : gammaInv hN hb = 1 := (gammaInv_eq_one_iff hN hb).mpr hbcent
    have h2 : ι (gammaInv hN hb) = 1 := by rw [h3, map_one]
    rw [h7] at h2
    exact h2

private lemma unitaryCoord_surj
    (hι : ∀ (a : ↥(ggGamma L hN).range) (t : Fin m → Fˣ),
      ActsDiagU φ (a : MulAut ↥L) (fun i => (t i : F)) → ι a = QuotientGroup.mk t)
    (v : Fin m → ZMod 3)
    (hv : (QuotientGroup.mk (fun i => ζ ^ (v i).val) : UTorus.Proj F m) ∈ ι.range) :
    ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, unitaryCoord_u hN hF hζ hdiag b i = v i + c := by
  obtain ⟨a, ha⟩ := hv
  obtain ⟨b, hb, rfl⟩ := exists_gammaInv_eq hN a
  have h7 := ι_gammaInv (hF := hF) (hζ := hζ) (hdiag := hdiag) ι hι hb
  have hEq : (QuotientGroup.mk (fun i => ζ ^ (unitaryCoord_u hN hF hζ hdiag b i).val) :
      UTorus.Proj F m) = QuotientGroup.mk (fun i => ζ ^ (v i).val) :=
    h7.symm.trans ha
  obtain ⟨c, hc⟩ := (mk_pow_eq_mk_pow_iff hF hζ _ _).mp hEq
  exact ⟨b, hb, c, hc⟩

end Coord

theorem exists_unitaryCoord {G : Type} [Group G] {Bs L : Subgroup G}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hF : Nat.card F = 4)
    {φ : ↥(unitarySU 2 1 F m) →* ↥L} {ζ : Fˣ} (hζ : orderOf ζ = 3)
    (hdiag : ∀ a ∈ (ggGamma L hN).range, ∃ t : Fin m → F, ActsDiagU φ a t)
    (ι : ↥(ggGamma L hN).range →* UTorus.Proj F m) (hιinj : Function.Injective ι)
    (hι : ∀ (a : ↥(ggGamma L hN).range) (t : Fin m → Fˣ),
      ActsDiagU φ (a : MulAut ↥L) (fun i => (t i : F)) → ι a = QuotientGroup.mk t) :
    ∃ u : G → Fin m → ZMod 3,
      (∀ b ∈ Bs, ∀ s s' : ↥(unitarySU 2 1 F m),
        (s' : GL (Fin m) F) = TauCeti.diagGL (fun i => ζ ^ (u b i).val) * s *
          (TauCeti.diagGL (fun i => ζ ^ (u b i).val))⁻¹ →
        ((φ s' : ↥L) : G) = b⁻¹ * φ s * b) ∧
      (∀ b ∈ Bs, ∀ b' ∈ Bs, ∃ c : ZMod 3, ∀ i, u (b * b') i = u b i + u b' i + c) ∧
      (∀ b ∈ Bs, (∃ c : ZMod 3, ∀ i, u b i = c) ↔ b ∈ Subgroup.centralizer (L : Set G)) ∧
      (∀ b ∈ Bs, (QuotientGroup.mk (fun i => ζ ^ (u b i).val) : UTorus.Proj F m) ∈ ι.range) ∧
      ∀ v : Fin m → ZMod 3,
        (QuotientGroup.mk (fun i => ζ ^ (v i).val) : UTorus.Proj F m) ∈ ι.range →
          ∃ b ∈ Bs, ∃ c : ZMod 3, ∀ i, u b i = v i + c :=
  ⟨unitaryCoord_u hN hF hζ hdiag, fun _ hb => unitaryCoord_conj hN hF hζ hdiag hb,
    fun _ hb _ hb' => unitaryCoord_mul ι hι hb hb',
    fun _ hb => unitaryCoord_const_iff ι hι hιinj hb,
    fun _ hb => ⟨gammaInv hN hb, ι_gammaInv ι hι hb⟩, unitaryCoord_surj ι hι⟩

end CFSG.StandardType.FrameRoute.UnitaryModel
