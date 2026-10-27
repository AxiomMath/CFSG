module

public import CFSG.Quasithin.Background.SmithB45TorTitsFive
public import CFSG.Quasithin.Background.F7TwoInvTitsFive
public import CFSG.Quasithin.Background.F7TwoInvTits
public import CFSG.Quasithin.Background.E3MParamAttained

public section

namespace CFSG.Quasithin.TitsMParam

open CFSG.Sporadic.Schreier.Tits CFSG.Quasithin.F7Two


theorem two_pow_twenty_le_index_sq_of_tits {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {Y L : Subgroup (MulAut W)}
    (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W))) (e0 : ↥L ≃* titsD) (hfix : fixV L = ⊥)
    {t : MulAut W} (htY : t ∈ Y) (ht : orderOf t = 2) :
    2 ^ 20 ≤ (fixV (Subgroup.zpowers t)).index ^ 2 := by
  have ht2 : t * t = 1 := by rw [← sq, ← ht]; exact pow_orderOf_eq_one t
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have hN : ∀ l : MulAut W, l ∈ L ↔ t * l * t⁻¹ ∈ L := Subgroup.mem_normalizer_iff.1 (hY htY)
  have hinvol : ∀ l : MulAut W, t * (t * l * t⁻¹) * t⁻¹ = l := fun l => by
    calc t * (t * l * t⁻¹) * t⁻¹ = (t * t) * l * (t * t)⁻¹ := by group
      _ = l := by rw [ht2]; group
  let cL : ↥L ≃* ↥L :=
    { toFun := fun l => ⟨t * l * t⁻¹, (hN l).1 l.2⟩
      invFun := fun l => ⟨t * l * t⁻¹, (hN l).1 l.2⟩
      left_inv := fun l => Subtype.ext (hinvol l)
      right_inv := fun l => Subtype.ext (hinvol l)
      map_mul' := fun a b => Subtype.ext (by
        change t * ((a : MulAut W) * b) * t⁻¹ = t * a * t⁻¹ * (t * b * t⁻¹)
        group) }
  set φ : MulAut titsD := (e0.symm.trans cL).trans e0 with hφdef
  set σ : titsD →* MulAut W := L.subtype.comp e0.symm.toMonoidHom with hσdef
  have hσ : Function.Injective σ := L.subtype_injective.comp e0.symm.injective
  have hσφ : ∀ x, σ (φ x) = t * σ x * t⁻¹ := fun x => by
    change ((e0.symm (e0 (cL (e0.symm x))) : ↥L) : MulAut W) =
      t * ((e0.symm x : ↥L) : MulAut W) * t⁻¹
    rw [MulEquiv.symm_apply_apply]
    rfl
  have hφφ : φ * φ = 1 := by
    refine MulEquiv.ext fun x => hσ ?_
    rw [MulAut.mul_apply, hσφ, hσφ, MulAut.one_apply, hinvol]
  by_cases hφ : φ = 1
  ·
    have hcomm : ∀ l ∈ L, t * l * t⁻¹ = l := by
      intro l hl
      have h := hσφ (e0 ⟨l, hl⟩)
      rw [hφ, MulAut.one_apply] at h
      have hl' : σ (e0 ⟨l, hl⟩) = l := by
        change ((e0.symm (e0 ⟨l, hl⟩) : ↥L) : MulAut W) = l
        rw [MulEquiv.symm_apply_apply]
      rw [hl'] at h
      exact h.symm
    let δ : W →* W :=
      { toFun := fun w => t w * w⁻¹
        map_one' := by simp
        map_mul' := fun a b => by
          rw [map_mul, mul_inv]
          exact mul_mul_mul_comm _ _ _ _ }
    have hker : δ.ker = fixV (Subgroup.zpowers t) := by
      ext v
      rw [MonoidHom.mem_ker, CFSG.QuasithinUnique.Setup.X5.mem_fixV_zpowers]
      change t v * v⁻¹ = 1 ↔ t v = v
      exact mul_inv_eq_one
    have hδl : ∀ l ∈ L, ∀ w, l (δ w) = δ (l w) := by
      intro l hl w
      change l (t w * w⁻¹) = t (l w) * (l w)⁻¹
      rw [map_mul, map_inv]
      congr 1
      rw [← MulAut.mul_apply, ← MulAut.mul_apply]
      congr 1
      calc l * t = (t * l * t⁻¹) * t := by rw [hcomm l hl]
        _ = t * l := by group
    have hLU : ∀ l ∈ L, ∀ u ∈ δ.range, l u ∈ δ.range := by
      rintro l hl _ ⟨w, rfl⟩
      exact ⟨l w, (hδl l hl w).symm⟩
    have hLstab : L ≤ stabSub δ.range := by
      intro l hl u
      refine ⟨fun h => ?_, hLU l hl u⟩
      have h' := hLU l⁻¹ (L.inv_mem hl) _ h
      rwa [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h'
    let σU : titsD →* MulAut ↥δ.range :=
      (resHom δ.range).comp ((Subgroup.inclusion hLstab).comp e0.symm.toMonoidHom)
    have hσU : Function.Injective σU := by
      rw [← MonoidHom.ker_eq_bot_iff]
      have : IsSimpleGroup titsD := titsD_simple
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal σU.ker with h | h
      · exact h
      · exfalso
        have hUfix : δ.range ≤ fixV L := by
          intro u hu
          rw [mem_fixV]
          intro l hl
          have hx : σU (e0 ⟨l, hl⟩) = 1 := by
            rw [← MonoidHom.mem_ker, h]
            trivial
          have h' := congrArg (fun ψ : MulAut ↥δ.range => ((ψ ⟨u, hu⟩ : ↥δ.range) : W)) hx
          change ((resHom δ.range (Subgroup.inclusion hLstab (e0.symm (e0 ⟨l, hl⟩))) ⟨u, hu⟩ :
            ↥δ.range) : W) = u at h'
          rw [MulEquiv.symm_apply_apply, resHom_apply] at h'
          exact h'
        rw [hfix] at hUfix
        have ht1 : t = 1 := by
          refine MulEquiv.ext fun w => ?_
          have hw : δ w ∈ (⊥ : Subgroup W) := hUfix ⟨w, rfl⟩
          rw [Subgroup.mem_bot] at hw
          change t w * w⁻¹ = 1 at hw
          rw [MulAut.one_apply]
          exact mul_inv_eq_one.1 hw
        rw [ht1, orderOf_one] at ht
        norm_num at ht
    have hU2 : ∀ u : ↥δ.range, u * u = 1 := fun u => Subtype.ext (hW u)
    have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
    obtain ⟨g5, hg5⟩ := exists_prime_orderOf_dvd_card' (G := titsD) 5
      (by rw [card_titsD]; norm_num)
    have h1 := B45Tor.two_pow_twenty_le_index_fixV hU2 σU hσU hg5
    have h2 : (fixV (Subgroup.zpowers (σU g5))).index ≤ Nat.card ↥δ.range :=
      Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_card _)
    have h3 : Nat.card ↥δ.range = (fixV (Subgroup.zpowers t)).index := by
      rw [← hker, Subgroup.index_ker]
    have h4 : (fixV (Subgroup.zpowers t)).index ≤ (fixV (Subgroup.zpowers t)).index ^ 2 :=
      Nat.le_self_pow two_ne_zero _
    exact (h1.trans (h2.trans h3.le)).trans h4
  ·
    obtain ⟨u, hu, hφu⟩ := titsD_involutory_aut_inner hφφ hφ
    obtain ⟨x, hx⟩ := titsD_exists_comm_orderOf_five u hu
    have h1 := B45Tor.two_pow_twenty_le_index_fixV hW σ hσ hx
    have hux : u * x * u⁻¹ = φ x := by rw [hφu, MulAut.conj_apply]
    have hy : σ (u * x * u⁻¹ * x⁻¹) = t * (σ x * t * (σ x)⁻¹) := by
      rw [hux, map_mul, map_inv, hσφ, htinv]
      group
    rw [hy] at h1
    have h2 := CFSG.QuasithinUnique.Setup.X5.index_fixV_mul_le t (σ x * t * (σ x)⁻¹)
    rw [CFSG.QuasithinUnique.Setup.X5.index_fixV_conj] at h2
    rw [sq]
    exact h1.trans h2

theorem ten_le_rkIdx_of_tits {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {Y L : Subgroup (MulAut W)} (hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)))
    (e0 : ↥L ≃* titsD) (hfix : fixV L = ⊥) {t : MulAut W} (htY : t ∈ Y) (ht : orderOf t = 2) :
    10 ≤ rkIdx (fixV (Subgroup.zpowers t)) := by
  have h := two_pow_twenty_le_index_sq_of_tits hW hY e0 hfix htY ht
  have hW2 : ∀ w : W, w ^ 2 = 1 := fun w => by rw [sq]; exact hW w
  rw [CFSG.Quasithin.B1.index_eq_two_pow hW2, ← pow_mul] at h
  have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h
  omega

theorem ten_le_mParam_of_isTits (W : Type) [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (Y L : Subgroup (MulAut W)) (hLY : L ≤ Y) (hLn : (L.subgroupOf Y).Normal)
    (hT : CFSG.Quasithin.IsTits ↥L) (hfix : fixV L = ⊥) : 10 ≤ E3.mParam Y := by
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  obtain ⟨e0⟩ := titsModelEquiv ↥L 2 1 hT
  have hY : Y ≤ Subgroup.normalizer (L : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLY).1 hLn
  set z : MulAut W := ((e0.symm titsZD : ↥L) : MulAut W) with hz
  have hzY : z ∈ Y := hLY (e0.symm titsZD).2
  have hzo : orderOf z = 2 := by
    rw [hz, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, orderOf_titsZD]
  have hEven : Even (Nat.card Y) := by
    rw [even_iff_two_dvd, ← hzo]
    exact Subgroup.orderOf_dvd_natCard Y hzY
  obtain ⟨t, htY, hto, hm⟩ := E3.exists_involution_rkIdx_fixV_eq_mParam Y hEven
  rw [← hm]
  exact ten_le_rkIdx_of_tits hW' hY e0 hfix htY hto

end CFSG.Quasithin.TitsMParam
