module

public import CFSG.LocalAnalysis.WeakClosure81.ElevenTenHyp
public import CFSG.Quasithin.Background.E6TwentyFourA

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.RankThree.PartOne CFSG.CGT.PushingUp
  CFSG.CGT.PushingUpLit Subgroup
open scoped commutatorElement Pointwise
open CFSG.QuasithinUnique.Lin2 (IsHallTwoPrimeOf ActsRegularlyOn nonIdentity)

variable {G : Type} [Group G] [Finite G]

private noncomputable def mkTilEquivP (V : Subgroup G) (hV : IsElemAbelian 2 V) :
    IntMod V hV ≃* Vtil (⊥ : Subgroup G) V hV :=
  MulEquiv.ofBijective (mkTil (⊥ : Subgroup G) V hV)
    ⟨fun x y h => by
      have h1 : x.val * y.val⁻¹ = 1 :=
        Subgroup.mem_bot.1 ((mkTil_eq_iff (⊥ : Subgroup G) V hV x y).1 h)
      exact IntMod.val_injective (mul_inv_eq_one.1 h1),
     mkTil_surjective (⊥ : Subgroup G) V hV⟩

private theorem mkTilEquivP_apply (V : Subgroup G) (hV : IsElemAbelian 2 V) (x : IntMod V hV) :
    mkTilEquivP V hV x = mkTil (⊥ : Subgroup G) V hV x := rfl

private theorem actTil_bot_eq_congrP (V : Subgroup G) (hV : IsElemAbelian 2 V)
    (g : stabTil (⊥ : Subgroup G) V) :
    actTil (⊥ : Subgroup G) V hV g =
      MulAut.congr (mkTilEquivP V hV) (convI hV ⟨(g : G), g.2.1⟩) := by
  refine MulEquiv.ext fun q => ?_
  obtain ⟨x, rfl⟩ := mkTil_surjective (⊥ : Subgroup G) V hV q
  rw [actTil_mk, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
  have hsymm : (mkTilEquivP V hV).symm (mkTil (⊥ : Subgroup G) V hV x) = x := by
    rw [← mkTilEquivP_apply V hV x]
    exact (mkTilEquivP V hV).symm_apply_apply x
  rw [hsymm, mkTilEquivP_apply]
  rfl

private theorem barSub_bot_eq_map_congrP (M V : Subgroup G) (hV : IsElemAbelian 2 V)
    (hMn : M = normalizer (V : Set G)) :
    barSub (⊥ : Subgroup G) V hV M =
      (autI hV ⊤).map (MulAut.congr (mkTilEquivP V hV)).toMonoidHom := by
  ext ψ
  rw [mem_barSub, Subgroup.mem_map]
  constructor
  · rintro ⟨g, hgM, rfl⟩
    refine ⟨convI hV ⟨(g : G), g.2.1⟩,
      (mem_autI hV).2 ⟨⟨(g : G), g.2.1⟩, trivial, rfl⟩, ?_⟩
    exact (actTil_bot_eq_congrP V hV g).symm
  · rintro ⟨χ, hχ, rfl⟩
    obtain ⟨g, -, rfl⟩ := (mem_autI hV).1 hχ
    have hg0 : (g : G) ∈ normalizer (⊥ : Subgroup G) := by
      rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top _
    let g' : stabTil (⊥ : Subgroup G) V := ⟨(g : G), ⟨g.2, hg0⟩⟩
    have hgM : (g : G) ∈ M := by
      rw [hMn]
      exact g.2
    exact ⟨g', hgM, actTil_bot_eq_congrP V hV g'⟩

theorem mBar_eq_mParam_autI_of_setting11 {M V Q : Subgroup G} (hset : Setting11 M V Q)
    (hV : IsElemAbelian 2 V) : mBar M ⊥ V hV = E3.mParam (autI hV M) := by
  have hMn : M = Subgroup.normalizer (V : Set G) :=
    (eleven_c_normalizer hset.maxLocal hset.V_ne_bot (B2F.isPGroup_of_isElemAbelian hV)
      hset.normal).symm
  have htop : autI hV ⊤ = autI hV M := by
    ext ξ
    rw [mem_autI, mem_autI]
    constructor
    · rintro ⟨g, -, rfl⟩
      exact ⟨g, by rw [hMn]; exact g.2, rfl⟩
    · rintro ⟨g, -, rfl⟩
      exact ⟨g, trivial, rfl⟩
  have hMbar : Mbar M ⊥ V hV =
      (autI hV ⊤).map (MulAut.congr (mkTilEquivP V hV)).toMonoidHom :=
    barSub_bot_eq_map_congrP M V hV hMn
  show E3.mParam (Mbar M ⊥ V hV) = _
  rw [hMbar, E3.mParam_map_congr (mkTilEquivP V hV) (autI hV ⊤), htop]


theorem eleven_mQuot_lt_mParam {M V Q U L X : Subgroup G} (hV : IsElemAbelian 2 V)
    (hd : Eleven11Data M V Q U L X) : E3.mQuot V U < E3.mParam (autI hV M) := by
  have h1 : ((E3.mQuot V U : ℕ) : ℕ∞) = rMV M V := hd.mem_delta.2
  have h2 := hd.r_lt_m
  have h3 := mBar_eq_mParam_autI_of_setting11 hd.setting hd.setting.isElemAbelian
  rw [← h1, h3] at h2
  exact_mod_cast h2


theorem eleven_ten_card_autI {M V Q U L X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hd : Eleven11Data M V Q U L X) :
    X ⊓ Subgroup.centralizer (V : Set G) = ⊥ ∧ IsCyclic (autI hV X) ∧
      Nat.card (autI hV X) = 2 ^ E3.mQuot V U - 1 ∧ 1 < E3.mQuot V U := by
  obtain ⟨n, hn, -, hr, -, hD⟩ := hd.ten
  obtain ⟨hcyc, hcard, hCV, hreg⟩ := hD X hd.isHall
  have hQU : E3.mQuot V U = n := by
    have h1 : ((E3.mQuot V U : ℕ) : ℕ∞) = rMV M V := hd.mem_delta.2
    rw [hr] at h1
    exact_mod_cast h1
  rw [hQU]
  have hXM : X ≤ M := hd.isHall.1.trans inf_le_right
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hXM.trans hd.setting.normal
  have hcomm_le : ⁅V, X⁆ ≤ V := by
    rw [Subgroup.commutator_le]
    intro v hv x hx
    rw [commutatorElement_def]
    have h1 := (Subgroup.mem_normalizer_iff.1 (hXN hx) v⁻¹).1 (V.inv_mem hv)
    have := V.mul_mem hv h1
    simpa [mul_assoc] using this
  have hne : ⁅V, X⁆ ≠ ⊥ := by
    intro h0
    have hVX : V ≤ Subgroup.centralizer (X : Set G) := by
      intro v hv
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      have : ⁅v, x⁆ ∈ ⁅V, X⁆ := Subgroup.commutator_mem_commutator hv hx
      rw [h0, Subgroup.mem_bot, commutatorElement_def, mul_inv_eq_one,
        mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    have hUV : U = V := by
      rw [← hCV]; exact inf_eq_left.2 hVX
    rw [hUV, E3.mQuot_self] at hQU
    omega
  have hX1 : X ⊓ Subgroup.centralizer (V : Set G) = ⊥ := by
    obtain ⟨z, hz⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hxC : x ∈ Subgroup.centralizer (V : Set G) := hx.2
    have hzV : (z : G) ∈ V := hcomm_le z.2
    have hzc : x⁻¹ * (z : G) * x = z := by
      have := Subgroup.mem_centralizer_iff.1 hxC _ hzV
      rw [mul_assoc, this, inv_mul_cancel_left]
    exact hreg.2.2 z ⟨z.2, fun h => hz (Subtype.ext h)⟩ x hx.1 hzc
  refine ⟨hX1, ?_, ?_, hn⟩
  · haveI := hcyc
    haveI : IsCyclic (X.subgroupOf (Subgroup.normalizer (V : Set G))) :=
      isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hXN).symm.toMonoidHom
        (Subgroup.subgroupOfEquivOfLe hXN).symm.surjective
    exact isCyclic_of_surjective ((convI hV).subgroupMap (X.subgroupOf _))
      ((convI hV).subgroupMap_surjective _)
  · have h := card_autI_mul_card_inf hV hXN
    rw [hX1, Subgroup.card_bot, mul_one] at h
    rw [h, hcard]


theorem eleven_ten_hyp102 {M V Q U L X : Subgroup G}
    (hV : IsElemAbelian 2 V) (hd : Eleven11Data M V Q U L X) :
    Asc81c.Hyp102 (autI hV M) (autI hV X) ∧
      (fixV (autI hV X)).map (E3.valHom hV) = U ∧
      Nat.card (autI hV X) = 2 ^ E3.mQuot V U - 1 ∧
      Nat.card (commSub ⊤ (autI hV X)) = 2 ^ E3.mQuot V U := by
  classical
  obtain ⟨hX1, hXcyc, hXcard, hU1⟩ := eleven_ten_card_autI hV hd
  have hUm := eleven_mQuot_lt_mParam hV hd
  obtain ⟨n', hn', -, hr', -, hD⟩ := hd.ten
  obtain ⟨-, -, hCVeq, hAct⟩ := hD X hd.isHall
  have hXM : X ≤ M := hd.isHall.1.trans inf_le_right
  have hXU : X ≤ Subgroup.centralizer (U : Set G) :=
    (hd.isHall.1.trans inf_le_left).trans
      (isBlockOfInX_of_mem_elevenBlocksB hd.setting
        (deltaEleven_subset_gammaEleven M V hd.mem_delta) hd.mem_blocks).1
  have hXN : X ≤ Subgroup.normalizer (V : Set G) := hXM.trans hd.setting.normal
  have hUV : U ≤ V := (deltaEleven_subset_gammaEleven M V hd.mem_delta).1
  have hreg : ∀ v ∈ ⁅V, X⁆, v ≠ 1 → ∀ x ∈ X, x * v = v * x →
      x ∈ Subgroup.centralizer (V : Set G) := by
    intro v hv hv1 x hx hxv
    have h1 : x⁻¹ * v * x = v := by rw [mul_assoc, hxv.symm, inv_mul_cancel_left]
    have := hAct.2.2 v ⟨hv, hv1⟩ x hx h1
    rw [this]
    exact Subgroup.one_mem _
  have hnorm := eleven_ten_hnorm hd
  have hW : ∀ w : IntMod V hV, w ^ 2 = 1 := IntMod.sq_eq_one
  set n := E3.mQuot V U with hndef
  have h2n : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hU1
  have hXodd : Odd (Nat.card (autI hV X)) := by
    rw [hXcard]
    have he : Even (2 ^ n) := (Nat.even_pow' (by omega)).2 even_two
    exact Nat.Even.sub_odd (by omega) he odd_one
  have hXne : autI hV X ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hXcard
    omega
  have hCVX : ∀ v ∈ V, v ∈ Subgroup.centralizer (X : Set G) → v ∈ U := by
    intro v hv hvC
    rw [← hCVeq]
    exact ⟨hv, hvC⟩
  have hfix : ∀ v : IntMod V hV, v ∈ fixV (autI hV X) ↔ v.val ∈ U := by
    intro v
    rw [mem_fixV_autI hV hXN v]
    exact ⟨hCVX v.val v.val_mem, fun hv => Subgroup.le_centralizer_iff.1 hXU hv⟩
  have hfixmap : (fixV (autI hV X)).map (E3.valHom hV) = U := by
    ext g
    constructor
    · rintro ⟨v, hv, rfl⟩
      exact (hfix v).1 hv
    · intro hg
      exact ⟨IntMod.mk hV ⟨g, hUV hg⟩, (hfix _).2 hg, rfl⟩
  have hrkIdx : rkIdx (fixV (autI hV X)) = n := by
    rw [E3.rkIdx_eq_mQuot_map hV, hfixmap]
  have hprod := Asc81c.card_fixV_mul_card_commSub hW hXodd
  have hrk : rk (commSub ⊤ (autI hV X)) = n := by
    have h1 := rk_add_rkIdx (fixV (autI hV X))
    have h2 : rk (fixV (autI hV X)) + rk (commSub ⊤ (autI hV X)) = rk (IntMod V hV) := by
      unfold rk
      rw [← padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne', hprod]
    omega
  have hcardc : Nat.card (commSub ⊤ (autI hV X)) = 2 ^ n := by
    rw [card_eq_two_pow hW, hrk]
  have hsemi : ∀ v ∈ commSub ⊤ (autI hV X), v ≠ 1 → ∀ ξ ∈ autI hV X, ξ v = v → ξ = 1 := by
    intro v hv hv1 ξ hξ hξv
    obtain ⟨g, hgX, rfl⟩ := (mem_autI hV).1 hξ
    rw [convI_eq_one_iff]
    have hvX : v.val ∈ ⁅V, X⁆ := E6.map_valHom_commSub_le hV X ⟨v, hv, rfl⟩
    have hv1' : v.val ≠ 1 := fun h0 => hv1 (IntMod.val_injective (h0.trans IntMod.val_one.symm))
    have hcv : (g : G) * v.val = v.val * g := by
      have h1 := congrArg IntMod.val hξv
      rw [convI_apply_val] at h1
      calc (g : G) * v.val = (g * v.val * (g : G)⁻¹) * g := by group
        _ = v.val * g := by rw [h1]
    exact hreg v.val hvX hv1' g hgX hcv
  have hregular : ∀ v ∈ commSub ⊤ (autI hV X), v ≠ 1 → ∀ w ∈ commSub ⊤ (autI hV X), w ≠ 1 →
      ∃! ξ : autI hV X, (ξ : MulAut (IntMod V hV)) v = w := by
    intro v hv hv1 w hw hw1
    let f : autI hV X → ↥(((commSub ⊤ (autI hV X)) : Set (IntMod V hV)) \ {1}) := fun ξ =>
      ⟨(ξ : MulAut (IntMod V hV)) v, Asc81c.commSub_stable' ξ.2 hv, fun h0 => hv1 (by
        have h1 : (ξ : MulAut (IntMod V hV)) v = (ξ : MulAut (IntMod V hV)) 1 := by
          rw [map_one]
          exact h0
        exact (ξ : MulAut (IntMod V hV)).injective h1)⟩
    have hf : Function.Injective f := by
      intro ξ₁ ξ₂ h12
      have h12' : (ξ₁ : MulAut (IntMod V hV)) v = (ξ₂ : MulAut (IntMod V hV)) v :=
        congrArg Subtype.val h12
      have h2 : ((ξ₂ : MulAut (IntMod V hV))⁻¹ * ξ₁) v = v := by
        rw [MulAut.mul_apply, h12', MulAut.inv_apply_self]
      have h1 := hsemi v hv hv1 _ ((autI hV X).mul_mem ((autI hV X).inv_mem ξ₂.2) ξ₁.2) h2
      apply Subtype.ext
      have h3 := congrArg (fun x => (ξ₂ : MulAut (IntMod V hV)) * x) h1
      simpa using h3
    have hcardf : Nat.card ↥(((commSub ⊤ (autI hV X)) : Set (IntMod V hV)) \ {1}) ≤
        Nat.card (autI hV X) := by
      rw [Asc81c.card_diff_one, hcardc, hXcard]
    have hbij : Function.Bijective f := hf.bijective_of_nat_card_le hcardf
    obtain ⟨ξ, hξ⟩ := hbij.2 ⟨w, hw, hw1⟩
    refine ⟨ξ, congrArg Subtype.val hξ, fun η hη => hf ?_⟩
    rw [hξ]
    exact Subtype.ext hη
  have hnormal : ∀ φ ∈ autI hV M,
      (fixV (autI hV X)).map (φ : MulAut (IntMod V hV)).toMonoidHom = fixV (autI hV X) →
      ∀ ξ ∈ autI hV X, φ * ξ * φ⁻¹ ∈ autI hV X := by
    intro φ hφ hφfix ξ hξ
    obtain ⟨g, hgM, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨x, hxX, rfl⟩ := (mem_autI hV).1 hξ
    have hgU : (g : G) ∈ Subgroup.normalizer (U : Set G) := by
      have hle : U.map (MulAut.conj (g : G)).toMonoidHom ≤ U := by
        rintro _ ⟨u, hu, rfl⟩
        have hmem : IntMod.mk hV ⟨u, hUV hu⟩ ∈ fixV (autI hV X) := (hfix _).2 hu
        have h1 : convI hV g (IntMod.mk hV ⟨u, hUV hu⟩) ∈ fixV (autI hV X) := by
          rw [← hφfix]
          exact ⟨_, hmem, rfl⟩
        have h2 := (hfix _).1 h1
        rw [convI_apply_val] at h2
        exact h2
      rw [Subgroup.mem_normalizer_iff_map_conj_eq]
      exact Subgroup.eq_of_le_of_card_ge hle
        (Subgroup.card_map_of_injective (MulAut.conj (g : G)).injective).ge
    obtain ⟨y, hyX, hyC⟩ := hnorm g ⟨hgM, g.2⟩ hgU x hxX
    have hyN : y ∈ Subgroup.normalizer (V : Set G) := hXN hyX
    refine (mem_autI hV).2 ⟨⟨y, hyN⟩, hyX, ?_⟩
    have h1 : convI hV (g * x * g⁻¹ * ⟨y, hyN⟩⁻¹) = 1 := by
      rw [convI_eq_one_iff]
      exact hyC
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    rw [← h1, map_mul, map_mul, map_inv]
  refine ⟨⟨⟨autI_mono hV hXM, hXne, hXcyc, hXodd, hregular, hnormal⟩, ?_⟩,
    hfixmap, hXcard, hcardc⟩
  rw [hrk]
  exact hUm


end CFSG.LocalAnalysis.WeakClosure81
