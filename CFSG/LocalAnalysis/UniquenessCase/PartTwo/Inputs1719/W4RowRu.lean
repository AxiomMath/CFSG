module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm11_1Row
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowAutInner
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowIndex
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowCenter
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowRuPack
public import CFSG.Quasithin.Background.SmithB45ExcRuClass
public import CFSG.Quasithin.Background.E3AParamCard
public import CFSG.Quasithin.Vol2.Ch9KGFFQRAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 CFSG.QuasithinUnique.Bridge.RuExcl
open CFSG.Sporadic.RuSchreier CFSG.Blueprint CFSG.Quasithin.B45Exc.Ru
open CFSG.Quasithin.H13.Ch9.KGFF

private theorem ruP_autInner
    (φ : ↥ruP ≃* ↥ruP) :
    ∃ s : ↥ruP, ∀ x, φ x = s * x * s⁻¹ := by
  obtain ⟨s, hs⟩ := conj_bijective.2 φ
  exact ⟨s, fun x => by rw [← hs, MulAut.conj_apply]⟩

private theorem two_pow_le_index_sq_2B
    {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w * w = 1)
    {L : Subgroup (MulAut W)} (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥ruP) {t : MulAut W}
    (htL : t ∈ L) {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hx : (e (QuotientGroup.mk ⟨t, htL⟩) : Equiv.Perm (Fin 4060)) = g * ruA0 * g⁻¹) :
    2 ^ 24 ≤ (fixV (zpowers t)).index ^ 2 := by
  have : Fact (Nat.Prime 29) := ⟨by norm_num⟩
  obtain ⟨g₀, hg₀, h29, h1⟩ := ru_order29
  let c : ↥ruP :=
    ⟨g * g₀ * g⁻¹, ruP.mul_mem (ruP.mul_mem hg hg₀) (ruP.inv_mem hg)⟩
  have hc : orderOf (e (QuotientGroup.mk ⟨t, htL⟩) *
      (c * e (QuotientGroup.mk ⟨t, htL⟩) * c⁻¹)) = 29 := by
    rw [← Subgroup.orderOf_coe]
    have hval : (((e (QuotientGroup.mk ⟨t, htL⟩) *
        (c * e (QuotientGroup.mk ⟨t, htL⟩) * c⁻¹) : ↥ruP) : Equiv.Perm (Fin 4060)))
        = g * (ruA0 * (g₀ * ruA0 * g₀⁻¹)) * g⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, c, hx]
      group
    rw [hval]
    refine orderOf_eq_prime ?_ ?_
    · rw [conj_pow, h29, mul_one, mul_inv_cancel]
    · intro hconj
      apply h1
      calc ruA0 * (g₀ * ruA0 * g₀⁻¹)
          = g⁻¹ * (g * (ruA0 * (g₀ * ruA0 * g₀⁻¹)) * g⁻¹) * g := by group
        _ = 1 := by rw [hconj]; simp
  have h := two_pow_le_index_sq_of_dihedral hW e htL (p := 29) (by norm_num) c hc
  rw [orderOf_two_zmod_29] at h
  exact (Nat.pow_le_pow_right (by norm_num) (by norm_num : 24 ≤ 28)).trans h

private theorem two_pow_le_index_sq_2A
    {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w * w = 1) (ψ : ↥ruP →* MulAut W) (hψ : Function.Injective ψ)
    {c : Equiv.Perm (Fin 4060)} (hc : c ∈ ruP) {x : ↥ruP}
    (hx : (x : Equiv.Perm (Fin 4060)) = c * (ruA1 * ruA1) * c⁻¹) :
    2 ^ 24 ≤ (fixV (zpowers (ψ x))).index ^ 2 := by
  have h5 : orderOf (2 : ZMod 5) = 4 := by
    rw [orderOf_eq_iff (by norm_num)]
    refine ⟨by decide, fun m hm hm0 => ?_⟩
    interval_cases m <;> decide
  obtain ⟨y, hy, w, hw, h, hh, P⟩ := W4Row.ruE25_invPack
  have Pc : W4Row.InvPack 5 6 ((MulAut.conj c) (ruA1 * ruA1))
      ((MulAut.conj c) y) ((MulAut.conj c) w) ((MulAut.conj c) h) :=
    (W4Row.InvPack.map_iff (f := (MulAut.conj c).toMonoidHom) (MulAut.conj c).injective).2 P
  have hτc : (MulAut.conj c) (ruA1 * ruA1) = (x : Equiv.Perm (Fin 4060)) := by
    rw [MulAut.conj_apply]
    exact hx.symm
  rw [hτc] at Pc
  let y' : ↥ruP := ⟨(MulAut.conj c) y, by
    rw [MulAut.conj_apply]
    exact ruP.mul_mem (ruP.mul_mem hc hy) (ruP.inv_mem hc)⟩
  let w' : ↥ruP := ⟨(MulAut.conj c) w, by
    rw [MulAut.conj_apply]
    exact ruP.mul_mem (ruP.mul_mem hc hw) (ruP.inv_mem hc)⟩
  let h' : ↥ruP := ⟨(MulAut.conj c) h, by
    rw [MulAut.conj_apply]
    exact ruP.mul_mem (ruP.mul_mem hc hh) (ruP.inv_mem hc)⟩
  have Pr : W4Row.InvPack 5 6 x y' w' h' :=
    (W4Row.InvPack.map_iff (f := ruP.subtype) ruP.subtype_injective).1 Pc
  have P' : W4Row.InvPack 5 6 (ψ x) (ψ y') (ψ w') (ψ h') :=
    (W4Row.InvPack.map_iff (f := ψ) hψ).2 Pr
  have h4 : ruA1 ^ 4 = 1 := ruSeed_relations.2.2.1
  have hτ₀ : (ruA1 * ruA1) * (ruA1 * ruA1) = 1 := by
    have h : ruA1 ^ 4 = ruA1 * ruA1 * (ruA1 * ruA1) := by
      rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add, sq]
    rw [← h]
    exact h4
  have hxx : x * x = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_mul, hx]
    calc c * (ruA1 * ruA1) * c⁻¹ * (c * (ruA1 * ruA1) * c⁻¹)
        = c * ((ruA1 * ruA1) * (ruA1 * ruA1)) * c⁻¹ := by group
      _ = 1 := by rw [hτ₀]; group
  have hτψ : ψ x * ψ x = 1 := by
    rw [← map_mul, hxx, map_one]
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have h := W4Row.two_pow_le_index_sq_of_invPack hW (p := 5) (by norm_num) hτψ P'
  rw [h5] at h
  have h24 : 2 ^ (6 * 4) = 2 ^ 24 := by norm_num
  rw [h24] at h
  exact h

private theorem two_pow_le_index_sq_2A_of_ruZ
    {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥ruP) (hZ : Subgroup.center ↥L = ⊥) {t : MulAut W}
    (htL : t ∈ L) {g : Equiv.Perm (Fin 4060)} (hg : g ∈ ruP)
    (hx : (e (QuotientGroup.mk ⟨t, htL⟩) : Equiv.Perm (Fin 4060)) = g * ruZ * g⁻¹) :
    2 ^ 24 ≤ (fixV (zpowers t)).index ^ 2 := by
  let x : ↥ruP := e (QuotientGroup.mk ⟨t, htL⟩)
  obtain ⟨k, hk, hkz⟩ := ruA1_sq_mem
  rw [pow_two] at hkz
  let c : Equiv.Perm (Fin 4060) := g * k⁻¹
  have hc : c ∈ ruP := ruP.mul_mem hg (ruP.inv_mem hk)
  have hz : ruZ = k⁻¹ * (ruA1 * ruA1) * k := by
    rw [← hkz]
    group
  have hx' : (x : Equiv.Perm (Fin 4060)) = c * (ruA1 * ruA1) * c⁻¹ := by
    rw [hx, hz]
    dsimp only [c]
    group
  have hker : (redHom L e).ker = ⊥ := by
    ext y
    rw [MonoidHom.mem_ker, redHom_eq_one_iff L e y, hZ]
  let ε : ↥L ≃* ↥ruP := MulEquiv.ofBijective (redHom L e)
    ⟨(MonoidHom.ker_eq_bot_iff _).1 hker, redHom_surjective L e⟩
  have hε : ε ⟨t, htL⟩ = x := rfl
  let ψ : ↥ruP →* MulAut W := L.subtype.comp ε.symm.toMonoidHom
  have hψ : Function.Injective ψ := L.subtype_injective.comp ε.symm.injective
  have hψx : ψ x = t := by
    have hsymm : ε.symm x = ⟨t, htL⟩ := by
      rw [← hε, MulEquiv.symm_apply_apply]
    exact congrArg (fun y : ↥L => (y : MulAut W)) hsymm
  have hres := two_pow_le_index_sq_2A hW ψ hψ hc hx'
  rw [hψx] at hres
  exact hres

private theorem two_pow_le_index_sq_ru
    {W : Type} [CommGroup W]
    [Finite W] (hW : ∀ w : W, w * w = 1) {L : Subgroup (MulAut W)}
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥ruP) (hZ : Subgroup.center ↥L = ⊥) {t : MulAut W}
    (htL : t ∈ L) (hto : orderOf t = 2) :
    2 ^ 24 ≤ (fixV (zpowers t)).index ^ 2 := by
  let x : ↥ruP := e (QuotientGroup.mk ⟨t, htL⟩)
  have ht2 : t * t = 1 := by
    rw [← pow_two, ← hto]
    exact pow_orderOf_eq_one t
  have hx2 : x * x = 1 := by
    have h : (⟨t, htL⟩ : ↥L) * ⟨t, htL⟩ = 1 := Subtype.ext ht2
    calc x * x
        = e (QuotientGroup.mk (⟨t, htL⟩ : ↥L)) *
            e (QuotientGroup.mk ⟨t, htL⟩) := rfl
      _ = e (QuotientGroup.mk (⟨t, htL⟩ : ↥L) * QuotientGroup.mk ⟨t, htL⟩) := by
            rw [map_mul]
      _ = e (QuotientGroup.mk ((⟨t, htL⟩ : ↥L) * ⟨t, htL⟩)) := by
            rw [QuotientGroup.mk_mul]
      _ = 1 := by rw [h, QuotientGroup.mk_one, map_one]
  have hx1 : x ≠ 1 := by
    intro h
    have h1 : (QuotientGroup.mk (s := Subgroup.center ↥L) (⟨t, htL⟩ : ↥L)) = 1 := by
      apply e.injective
      change x = e 1
      rw [h, map_one]
    rw [QuotientGroup.eq_one_iff] at h1
    have ht1 : (⟨t, htL⟩ : ↥L) = 1 := by
      have h2 := h1
      rw [hZ] at h2
      exact Subgroup.mem_bot.1 h2
    have ht1' : t = 1 := congrArg Subtype.val ht1
    rw [ht1', orderOf_one] at hto
    norm_num at hto
  have hx2' : (x : Equiv.Perm (Fin 4060)) * (x : Equiv.Perm (Fin 4060)) = 1 := by
    simpa using congrArg (fun y : ↥ruP => (y : Equiv.Perm (Fin 4060))) hx2
  have hx1' : (x : Equiv.Perm (Fin 4060)) ≠ 1 := fun h => hx1 (Subtype.ext h)
  rcases ru_inv_class x.2 hx2' hx1' with ⟨⟨g, hg, hxg⟩, -⟩ | ⟨⟨g, hg, hxg⟩, -⟩
  · exact two_pow_le_index_sq_2A_of_ruZ hW e hZ htL hg (by simpa only [x] using hxg)
  · exact two_pow_le_index_sq_2B hW e htL hg (by simpa only [x] using hxg)

theorem w4Thm11_1Row_Ru_holds :
    W4Thm11_1Row .Ru := by
  intro W _ _ hW Y L hLY hLn hF hq hO2 hs
  obtain ⟨e₀⟩ := hs
  let e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥ruP := e₀.trans ruEquivC
  have hYL : Y = L := W4Row.eq_of_fstar_eq_of_autInner hLY hLn hF hq e ruP_autInner
  have hW' : ∀ w : W, w * w = 1 := fun w => by rw [← sq]; exact hW w
  refine ⟨?_, ?_⟩
  · show E3.aParam Y ≤ 6
    exact E3.aParam_le_of_card_le Y fun A hA hA2 =>
      W4Row.card_le_of_sq_eq_one_of_o2Trivial hO2 (hA.trans hYL.le) hA2 e
        fun B hc hs => card_le_of_elemAb_ruP B ⟨hc, fun a ha => by rw [sq]; exact hs a ha⟩
  · show 12 ≤ E3.mParam Y
    have hZ := W4Row.center_eq_bot_of_o2Trivial_of_cover hq.1 hO2 e₀ ru_cover
    have hcard : Nat.card (NativeSporadic.Carrier .Ru) = 145926144000 :=
      CFSG.Sporadic.Ru.card_Ru
    obtain ⟨t₀, ht₀, ht₀o⟩ := W4Row.exists_orderOf_eq_two_of_cq e₀ (by rw [hcard]; norm_num)
    exact W4Row.le_mParam_of_index_sq hW' ⟨t₀, hLY ht₀, ht₀o⟩ fun t ht hto =>
      two_pow_le_index_sq_ru hW' e hZ (hYL.le ht) hto

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
