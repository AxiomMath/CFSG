module

public import CFSG.Quasithin.MS93.S512NA6
public import CFSG.Quasithin.MS93.S38OffHatMod
public import CFSG.Quasithin.MS93.S36SpEType

public section

namespace CFSG.Quasithin.MS93.S52i

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.H13.VolI
open CFSG.Quasithin.MS93.S36E
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped Matrix

variable {S : Type} [CommGroup S]

section Coord

variable {F : Type} [Field F]

variable [Finite F] [CharP F 2] {X' : Subgroup (MulAut S)}

theorem false_of_small_coord (φ : ↥X' →* MSP.Sp4 F) (θ : S ≃* Multiplicative (MSP.V4 F))
    (hθ : ∀ (x : ↥X') (s : S), Multiplicative.toAdd (θ ((x : MulAut S) s)) =
      MSP.mat (φ x) *ᵥ Multiplicative.toAdd (θ s))
    {E : Subgroup (MulAut S)} (hEX : E ≤ X')
    (hsmall : Nat.card S < Nat.card F ^ 2 * Nat.card (fixV E))
    (hE : Nat.card F ^ 2 ≤ Nat.card E) : False := by
  have hφi : Function.Injective φ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    refine MulEquiv.ext fun s => θ.injective (Multiplicative.toAdd.injective ?_)
    rw [hθ, hx, MSP.mat_one, Matrix.one_mulVec]
    rfl
  set Eh : Subgroup (MSP.Sp4 F) := (E.subgroupOf X').map φ with hEh
  have hcardE : Nat.card Eh = Nat.card E := by
    rw [hEh, Subgroup.card_map_of_injective hφi]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEX).toEquiv
  have hfixiff : ∀ s : S, s ∈ fixV E ↔ Multiplicative.toAdd (θ s) ∈ MSP.fixSp Eh := by
    intro s
    rw [mem_fixV, MSP.mem_fixSp]
    constructor
    · rintro hs _ ⟨x, hx, rfl⟩
      rw [← hθ, hs _ (Subgroup.mem_subgroupOf.1 hx)]
    · intro hs e he
      have h1 := hs (φ ⟨e, hEX he⟩) ⟨⟨e, hEX he⟩, Subgroup.mem_subgroupOf.2 he, rfl⟩
      rw [← hθ] at h1
      exact θ.injective (Multiplicative.toAdd.injective h1)
  have hcardfix : Nat.card (fixV E) = Nat.card (MSP.fixSp Eh) := by
    refine Nat.card_congr
      { toFun := fun s => ⟨Multiplicative.toAdd (θ s), (hfixiff s).1 s.2⟩
        invFun := fun v => ⟨θ.symm (Multiplicative.ofAdd v), (hfixiff _).2 (by simp)⟩
        left_inv := fun s => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
  have hcardS : Nat.card S = Nat.card (MSP.V4 F) :=
    Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)
  rw [hcardS, MSP.card_V4, hcardfix, MSP.card_fixSp, ← pow_add] at hsmall
  have hq : 1 < Nat.card F := by
    have := MSP.two_dvd_card (F := F)
    have hpos : 0 < Nat.card F := Nat.card_pos
    omega
  have hd : 3 ≤ Module.finrank F (MSP.fixSp Eh) := by
    have := (Nat.pow_lt_pow_iff_right hq).1 hsmall
    omega
  have hE1 : Eh ≠ ⊥ := by
    intro hbot
    rw [← hcardE, hbot, Subgroup.card_bot] at hE
    have : 2 ≤ Nat.card F ^ 2 := le_trans (by omega) (Nat.le_self_pow two_ne_zero _)
    omega
  have h4 : Module.finrank F (MSP.fixSp Eh) ≠ 4 := fun h4 => by
    refine hE1 (MSP.fixSp_eq_top_iff.1 (Submodule.eq_top_of_finrank_eq ?_))
    rw [h4]
    simp
  have hle4 : Module.finrank F (MSP.fixSp Eh) ≤ 4 := by
    have := Submodule.finrank_le (MSP.fixSp Eh)
    simpa using this
  have h3 : Module.finrank F (MSP.fixSp Eh) = 3 := by omega
  obtain ⟨p, hp, -, hEp⟩ := MSP.exists_point_of_finrank_fixSp_three h3
  have hle : Nat.card Eh ≤ Nat.card F := by
    rw [← MSP.card_xPoint hp]
    exact Subgroup.card_le_of_le hEp
  rw [hcardE] at hle
  have : Nat.card F < Nat.card F ^ 2 := by
    calc Nat.card F = Nat.card F ^ 1 := (pow_one _).symm
      _ < Nat.card F ^ 2 := Nat.pow_lt_pow_right hq (by norm_num)
  omega

end Coord

theorem four_mul_card_fixV_le_of_alt {K : Subgroup (MulAut S)}
    (hK : AlternatingNatural K ⊤ ⊥ 6) {x : MulAut S} (hxK : x ∈ K) (hx1 : x ≠ 1) :
    4 * Nat.card (fixV (Subgroup.zpowers x)) ≤ Nat.card S :=
  CFSG.Quasithin.MS93.S512N.four_mul_card_fixV_le_of_alt hK hxK hx1

theorem four_mul_card_fixV_le_of_hat (hS2 : ∀ s : S, s ^ 2 = 1) {K : Subgroup (MulAut S)}
    (hK : FFCaseHatA6 K) {x : MulAut S} (hxK : x ∈ K) (hx1 : x ≠ 1) :
    4 * Nat.card (fixV (Subgroup.zpowers x)) ≤ Nat.card S := by
  have hH := S38H.HatMod.of_tripleA6Six hS2 hK.1
  obtain ⟨zH, hcen, h3, hfp⟩ := hH.exists_z
  have hzc : zH ∈ Subgroup.center ↥K := hcen ▸ Subgroup.mem_zpowers zH
  have hxz : x * (zH : MulAut S) = (zH : MulAut S) * x := by
    have := Subgroup.mem_center_iff.1 hzc ⟨x, hxK⟩
    exact congrArg Subtype.val this
  have hE1 : Subgroup.zpowers x ≠ ⊥ := by
    intro hb
    apply hx1
    have : x ∈ Subgroup.zpowers x := Subgroup.mem_zpowers x
    rw [hb] at this
    exact this
  have h16 := hH.card_fixV_le h3 hfp (fun b hb => by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
    exact (Commute.zpow_left hxz n).eq) hE1
  rw [hH.card]
  omega

theorem false_of_small
    [Finite S] (h14 : MS14AS) (hS2 : ∀ s : S, s ^ 2 = 1) {X K E : Subgroup (MulAut S)}
    (hFF : FFHyp X K) {k : ℕ} (hk : 1 ≤ k)
    (hsmall : Nat.card S < (2 ^ k) ^ 2 * Nat.card (fixV E))
    (htype : (k = 1 ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = 360) ∨
      (2 ≤ k ∧ Nat.card (↥K ⧸ Subgroup.center ↥K) = ordBC 2 (2 ^ k)))
    (hkey2 : 2 ≤ k → E ≤ K ∧ (2 ^ k) ^ 2 ≤ Nat.card E)
    (hkey1 : k = 1 → ∃ x ∈ E, x ∈ K ∧ x ≠ 1) : False := by
  obtain ⟨-, -, hcases, -⟩ := h14 S hS2 X K hFF
  have h360 : 2 ≤ k → ordBC 2 (2 ^ k) ≠ 360 := fun _ => (S32.ordBC_two_ne (by omega)).2.1
  have hsmall1 : k = 1 → ∀ x ∈ E, Nat.card S < 4 * Nat.card (fixV (Subgroup.zpowers x)) := by
    rintro rfl x hx
    have hle : Nat.card (fixV E) ≤ Nat.card (fixV (Subgroup.zpowers x)) :=
      Subgroup.card_le_of_le fun v hv y hy => hv y (Subgroup.zpowers_le.mpr hx hy)
    have : (2 ^ 1) ^ 2 * Nat.card (fixV E) ≤ 4 * Nat.card (fixV (Subgroup.zpowers x)) := by
      norm_num
      exact hle
    omega
  rcases hcases with hSL | hhat | hsp | hG2
  ·
    obtain ⟨n, F, iF, fF, -, hcard, ⟨eK⟩, -, -⟩ := hSL
    obtain ⟨hn, -, hc⟩ := isPSL_quot_of_equiv_statedSL_three hcard eK.symm
    rcases htype with ⟨-, h⟩ | ⟨hk2, h⟩
    · exact absurd (hc.symm.trans h) (S32.ordA_two_ne_360 hn)
    · exact absurd (hc.symm.trans h) (ordA_two_ne_ordBC_two hk2)
  ·
    have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 360 := card_quot_of_isHat hhat.2.1
    rcases htype with ⟨rfl, -⟩ | ⟨hk2, h⟩
    · obtain ⟨x, hxE, hxK, hx1⟩ := hkey1 rfl
      have h1 := four_mul_card_fixV_le_of_hat hS2 hhat hxK hx1
      have h2 := hsmall1 rfl x hxE
      omega
    · exact absurd (h.symm.trans hc) (h360 hk2)
  · rcases hsp with ⟨n, hn2, F, iF, fF, hcard, π, hπ⟩ | hA6
    ·
      have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordBC 2 (2 ^ n) :=
        card_quot_of_equiv_statedSp hcard hn2 (FFC.equivOfRealizes (FFModel.nat_faithful _) hπ)
      rcases htype with ⟨rfl, h⟩ | ⟨hk2, h⟩
      · exact absurd (hc.symm.trans h) (S32.ordBC_two_ne (by omega)).2.1
      · have hnk : n = k := eq_of_ordBC_two_eq (by omega) (by omega) (hc.symm.trans h)
        subst hnk
        have : CharP F 2 := FFC.charP_two_of_card_pow hcard
        obtain ⟨φ, θ, hθ⟩ := coord_of_natSp4 hπ
        obtain ⟨hEK, hEc⟩ := hkey2 hk2
        exact false_of_small_coord φ θ hθ hEK (by rwa [hcard]) (by rwa [hcard])
    ·
      have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 360 := by
        obtain ⟨π, hπ⟩ := hA6
        exact card_quot_of_equiv_alt6 (FFC.equivOfRealizes (FFC.altDn_faithful (by norm_num)) hπ)
      rcases htype with ⟨rfl, -⟩ | ⟨hk2, h⟩
      · obtain ⟨x, hxE, hxK, hx1⟩ := hkey1 rfl
        have h1 := four_mul_card_fixV_le_of_alt hA6 hxK hx1
        have h2 := hsmall1 rfl x hxE
        omega
      · exact absurd (h.symm.trans hc) (h360 hk2)
  ·
    rcases hG2 with ⟨n, hn2, F, iF, fF, hcard, π, hπ⟩ | ⟨⟨F, iF, fF, hcard, π, hπ⟩, -⟩
    · have : CharP F 2 := FFC.charP_two_of_card_pow hcard
      have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = ordG2 (2 ^ n) :=
        card_quot_of_equiv_quasithinG2 hcard hn2
          (FFC.equivOfRealizes (FFC.zornQ_faithful _ le_rfl) hπ)
      rcases htype with ⟨-, h⟩ | ⟨hk2, h⟩
      · exact absurd (hc.symm.trans h) (S32.ordG2_ne (by omega)).2.1
      · exact absurd (hc.symm.trans h) (ordG2_ne_ordBC_two (by omega) (by omega))
    · have hcard' : Nat.card F = 2 := by rw [hcard]; norm_num
      have : CharP F 2 := FFC.charP_two_of_card_pow hcard
      have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 6048 :=
        (card_quot_of_equiv_g2Derived hcard'
          (FFC.equivOfRealizes (FFC.zornQ_faithful _ (Subgroup.commutator_le_self _)) hπ)).2
      rcases htype with ⟨-, h⟩ | ⟨hk2, h⟩
      · rw [hc] at h
        norm_num at h
      · exact absurd (h.symm.trans hc) (S32.ordBC_two_ne (by omega)).2.2

end CFSG.Quasithin.MS93.S52i
