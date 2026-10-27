module

public import CFSG.Quasithin.Background.D36GluedNDBase
import CFSG.Quasithin.Background.D36GluedL3Mod
import CFSG.Quasithin.Background.D36GluedL3Coord
import CFSG.Quasithin.Background.F918Z4bPrime
import CFSG.LocalAnalysis.ComponentInitial.SmallLinearIsomorphisms

public section

namespace CFSG.Quasithin

variable {Y : Type} [CommGroup Y] [Finite Y] {X A L₀ : Subgroup (MulAut Y)} {U U' : Subgroup Y}

namespace NDSetup

variable (S : NDSetup X A L₀ U U')

include S

theorem mem_stabSub_inf_fixV {b : MulAut Y} (hb : b ∈ A ⊓ stabSub U) :
    b ∈ stabSub (U ⊓ fixV L₀) := by
  intro y
  have hbU : ∀ y, b y ∈ U ↔ y ∈ U := hb.2
  have hbinv : ∀ l ∈ L₀, b⁻¹ * l * b ∈ L₀ := fun l hl => by
    simpa using S.norm b⁻¹ (inv_mem hb) l hl
  constructor
  · rintro ⟨hyU, hyf⟩
    refine ⟨(hbU y).mp hyU, fun l' hl' => ?_⟩
    have h1 := hyf (b * l' * b⁻¹) (S.norm b hb l' hl')
    have h2 : b (l' y) = b y := by
      have := h1
      simpa [MulAut.mul_apply] using this
    exact b.injective h2
  · rintro ⟨hyU, hyf⟩
    refine ⟨(hbU y).mpr hyU, fun l hl => ?_⟩
    have h1 : (b⁻¹ * l * b) y = y := hyf _ (hbinv l hl)
    have h2 : b⁻¹ (l (b y)) = y := by simpa [MulAut.mul_apply] using h1
    have h3 : l (b y) = b y := by
      have := congrArg b h2
      simpa using this
    exact h3

theorem sec_card_eight (e : ↥L₀ ≃* L3.Γ) (hu : rk ↥U - rk ↥(U ⊓ U') ≤ 5) :
    Nat.card (Sec U (U ⊓ fixV L₀)) = 8 := by
  have hZ := le_stabSub_inf_fixV S.stab
  have hZU : U ⊓ fixV L₀ ≤ U := inf_le_left
  have hM2 : ∀ a : Sec U (U ⊓ fixV L₀), a ^ 2 = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H u =>
      have : u ^ 2 = 1 := Subtype.ext (S.exp u)
      rw [← QuotientGroup.mk_pow, this]
      rfl
  let ρ : L3.Γ →* MulAut (Sec U (U ⊓ fixV L₀)) := (glueSecAct S.stab hZ).comp e.symm.toMonoidHom
  letI : MulDistribMulAction L3.Γ (Sec U (U ⊓ fixV L₀)) := MulDistribMulAction.compHom _ ρ
  have hsmul : ∀ (g : L3.Γ) (x : Sec U (U ⊓ fixV L₀)), g • x = glueSecAct S.stab hZ (e.symm g) x :=
    fun _ _ => rfl
  have hfix : ∀ x : Sec U (U ⊓ fixV L₀), (∀ g : L3.Γ, g • x = x) → x = 1 := fun x hx =>
    sec_fixed S.perfect S.stab hZ x fun l => by
      have := hx (e l)
      rwa [hsmul, MulEquiv.symm_apply_apply] at this
  have hperfM : ∀ N : Subgroup (Sec U (U ⊓ fixV L₀)),
      (∀ (g : L3.Γ) (x : Sec U (U ⊓ fixV L₀)), (g • x) * x⁻¹ ∈ N) → N = ⊤ := fun N hN =>
    sec_perfect S.perfect S.stab hZ S.comm N fun l x => by
      have := hN (e l) x
      rwa [hsmul, MulEquiv.symm_apply_apply] at this
  have hcard32 : Nat.card (Sec U (U ⊓ fixV L₀)) ≤ 32 := by
    have hDZ : U ⊓ U' ≤ U ⊓ fixV L₀ := le_inf inf_le_left (fun d hd l hl => S.cent l hl d hd.2)
    have hdz := rk_mono hDZ
    have hsec := card_sec_mul (V := Y) (W := U) (U := U ⊓ fixV L₀) hZU
    rw [card_eq_two_pow S.exp U, card_eq_two_pow S.exp (U ⊓ fixV L₀)] at hsec
    have hpos : 0 < 2 ^ rk ↥(U ⊓ fixV L₀) := by positivity
    have h1 : Nat.card (Sec U (U ⊓ fixV L₀)) * 2 ^ rk ↥(U ⊓ fixV L₀) ≤
        32 * 2 ^ rk ↥(U ⊓ fixV L₀) := by
      rw [hsec]
      calc 2 ^ rk ↥U ≤ 2 ^ (rk ↥(U ⊓ fixV L₀) + 5) :=
            Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 32 * 2 ^ rk ↥(U ⊓ fixV L₀) := by rw [pow_add]; ring
    exact Nat.le_of_mul_le_mul_right h1 hpos
  have hnt : ∃ x : Sec U (U ⊓ fixV L₀), x ≠ 1 := by
    obtain ⟨l, hl, u, hu', hlu⟩ := S.exists_not_mem
    refine ⟨QuotientGroup.mk ⟨u, hu'⟩, fun h1 => hlu ?_⟩
    have h2 : (⟨u, hu'⟩ : ↥U) ∈ (U ⊓ fixV L₀).subgroupOf U := (QuotientGroup.eq_one_iff _).1 h1
    have h3 : l u = u := h2.2 l hl
    rw [h3, mul_inv_cancel]
    exact (U ⊓ U').one_mem
  exact L3Mod.card_eq_eight hM2 hfix hperfM hcard32 hnt

theorem sec_sq : ∀ a : Sec U (U ⊓ fixV L₀), a ^ 2 = 1 := by
  intro a
  induction a using QuotientGroup.induction_on with
  | H u =>
    have : u ^ 2 = 1 := Subtype.ext (S.exp u)
    rw [← QuotientGroup.mk_pow, this]
    rfl

theorem exists_not_mem_Z (hnt : ∃ x : Sec U (U ⊓ fixV L₀), x ≠ 1) :
    ∃ l ∈ L₀, ∃ u ∈ U, l u * u⁻¹ ∉ U ⊓ fixV L₀ := by
  have hZ := le_stabSub_inf_fixV S.stab
  by_contra hcon
  push Not at hcon
  obtain ⟨x, hx1⟩ := hnt
  apply hx1
  apply sec_fixed S.perfect S.stab hZ x
  intro l
  induction x using QuotientGroup.induction_on with
  | H u =>
    rw [glueSecAct_mk]
    exact (mk_eq_mk_iff (U := (U ⊓ fixV L₀).subgroupOf U) _ _).2 (hcon l l.2 u u.2)

theorem false_of_psl2_seven (hL : IsPSL 2 7 1 ↥L₀) : False := by
  obtain ⟨e⟩ := nonempty_equiv_sl3_of_isPSL hL
  have hAut : AutRankLe ↥L₀ 2 := autRankLe_psl2_prime Nat.prime_seven le_rfl hL
  have hu : rk ↥U - rk ↥(U ⊓ U') ≤ 5 := by
    have := S.ubar_le hAut
    omega
  have hcard8 := S.sec_card_eight e hu
  have hZ := le_stabSub_inf_fixV S.stab
  have hnt : ∃ x : Sec U (U ⊓ fixV L₀), x ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h1 : Nat.card (Sec U (U ⊓ fixV L₀)) = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => (hcon a).trans (hcon b).symm⟩, ⟨1⟩⟩
    omega
  have hinj : Function.Injective (glueSecAct S.stab hZ) :=
    glueSecAct_injective S.stab hZ S.simple (S.exists_not_mem_Z hnt)
  have hL168 : Nat.card ↥L₀ = 168 := by
    rw [Nat.card_congr e.toEquiv]
    exact L3Mod.card_Γ
  have hGL : Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) = 168 := by
    rw [← L3Mod.card_Γ]
    exact (Nat.card_congr (MulEquiv.ofBijective _
      CFSG.LocalAnalysis.ComponentInitial.bijective_toGL_three_zmod_two).toEquiv).symm
  have hMcard : Nat.card (MulAut (Sec U (U ⊓ fixV L₀))) ≤ 168 := by
    obtain ⟨β, ρ', hβρ⟩ := exists_coord_of_mulAut (d := 3) S.sec_sq
      (by rw [hcard8]; norm_num) (MonoidHom.id (MulAut (Sec U (U ⊓ fixV L₀))))
    have hρ' : Function.Injective ρ' := by
      rw [injective_iff_map_eq_one]
      intro φ hφ
      apply MulEquiv.ext
      intro x
      apply β.injective
      have := hβρ φ x
      rw [hφ] at this
      simpa using this
    calc Nat.card (MulAut (Sec U (U ⊓ fixV L₀)))
        ≤ Nat.card (Matrix.GeneralLinearGroup (Fin 3) (ZMod 2)) :=
          Nat.card_le_card_of_injective _ hρ'
      _ = 168 := hGL
  have hbij : Function.Bijective (glueSecAct S.stab hZ) :=
    hinj.bijective_of_nat_card_le (by rw [hL168]; exact hMcard)
  obtain ⟨b, hb, hbnd⟩ : ∃ b ∈ A ⊓ stabSub U, ∀ l ∈ L₀, ∃ u ∈ U, b u ≠ l u := by
    by_contra hcon
    push Not at hcon
    exact S.nondiag hcon
  have hHU : L₀ ⊔ Subgroup.zpowers b ≤ stabSub U :=
    sup_le S.stab (Subgroup.zpowers_le.mpr hb.2)
  have hHZ : L₀ ⊔ Subgroup.zpowers b ≤ stabSub (U ⊓ fixV L₀) :=
    sup_le hZ (Subgroup.zpowers_le.mpr (S.mem_stabSub_inf_fixV hb))
  let ρH := glueSecAct hHU hHZ
  let b' : ↥(L₀ ⊔ Subgroup.zpowers b) := ⟨b, Subgroup.mem_sup_right (Subgroup.mem_zpowers b)⟩
  let incl : ↥L₀ →* ↥(L₀ ⊔ Subgroup.zpowers b) := Subgroup.inclusion le_sup_left
  have hcompat : ∀ l : ↥L₀, ρH (incl l) = glueSecAct S.stab hZ l := by
    intro l
    apply MulEquiv.ext
    intro x
    induction x using QuotientGroup.induction_on with
    | H u => rfl
  obtain ⟨l₀, hl₀⟩ := hbij.2 (ρH b')
  have hconj : ∀ l ∈ L₀, b * l * b⁻¹ = (l₀ : MulAut Y) * l * (l₀ : MulAut Y)⁻¹ := by
    intro l hl
    have h1 : incl ⟨b * l * b⁻¹, S.norm b hb l hl⟩ = b' * incl ⟨l, hl⟩ * b'⁻¹ := rfl
    have h2 : glueSecAct S.stab hZ ⟨b * l * b⁻¹, S.norm b hb l hl⟩ =
        glueSecAct S.stab hZ (l₀ * ⟨l, hl⟩ * l₀⁻¹) := by
      rw [← hcompat, h1, map_mul, map_mul, map_inv, hcompat, map_mul, map_mul, map_inv, hl₀]
    have := congrArg Subtype.val (hinj h2)
    simpa using this
  obtain ⟨u, hu, hne⟩ := hbnd l₀ l₀.2
  exact hne (S.inner b hb l₀ l₀.2 hconj u hu)

end NDSetup

end CFSG.Quasithin
