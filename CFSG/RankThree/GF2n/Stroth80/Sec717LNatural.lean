module

public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailInv717
import CFSG.RankThree.GF2n.Stroth80.Sec717DeltaKSpace
import CFSG.RankThree.GF2n.Stroth80.Sec717DeltaAct
import CFSG.RankThree.GF2n.Stroth80.Sec717MoveRepOfLayers
import CFSG.RankThree.GF2n.Stroth80.SL4OfLinear
import CFSG.RankThree.GF2n.Stroth80.StatedOmegaPerfect
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem S717LN.card_sl4_eq {K₁ K₂ : Type} [Field K₁] [Field K₂] [Finite K₁] [Finite K₂]
    (h : Nat.card K₁ = Nat.card K₂) :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) K₁) =
      Nat.card (Matrix.SpecialLinearGroup (Fin 4) K₂) := by
  classical
  haveI := Fintype.ofFinite K₁
  haveI := Fintype.ofFinite K₂
  rw [Matrix.card_SL_field, Matrix.card_SL_field, ← Nat.card_eq_fintype_card,
    ← Nat.card_eq_fintype_card, h]

theorem S717LN.perf_card_of_omega {H R F S K' : Type} [Group H] [Group R] [Field F]
    [AddCommGroup S] [Module F S] [Field K'] (ρ : R →* (S ≃ₗ[F] S)) (π : H →* R)
    (hπ : Function.Surjective π) (φ₀ : H →* GL (Fin 3 ⊕ Fin 3) K')
    (hφr : φ₀.range = StatedOmega (StatedQuadPlus 3 K')) (hk : ∀ x, ρ (π x) = 1 ↔ φ₀ x = 1) :
    (∀ r, ρ r ∈ ⁅ρ.range, ρ.range⁆) ∧
      Nat.card ρ.range = Nat.card ↥(StatedOmega (StatedQuadPlus 3 K')) := by
  constructor
  · intro r
    obtain ⟨x, rfl⟩ := hπ r
    have hx : φ₀ x ∈ ⁅φ₀.range, φ₀.range⁆ := by
      rw [hφr, statedOmega_quadPlus_perfect (le_refl 3), ← hφr]
      exact ⟨x, rfl⟩
    have hmap : ⁅φ₀.range, φ₀.range⁆ = (commutator H).map φ₀ := by
      rw [commutator_def, Subgroup.map_commutator, MonoidHom.range_eq_map]
    rw [hmap] at hx
    obtain ⟨c, hc', hcx⟩ := hx
    have h1 : φ₀ (c⁻¹ * x) = 1 := by rw [map_mul, map_inv, hcx, inv_mul_cancel]
    have h2 : ρ (π (c⁻¹ * x)) = 1 := (hk _).mpr h1
    have e : x = c * (c⁻¹ * x) := by group
    rw [e, map_mul, map_mul, h2, mul_one]
    have hc2 : (ρ.comp π) c ∈ (commutator H).map (ρ.comp π) := ⟨c, hc', rfl⟩
    have hmap2 : (commutator H).map (ρ.comp π) = ⁅(ρ.comp π).range, (ρ.comp π).range⁆ := by
      rw [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map]
    rw [hmap2] at hc2
    have hle : (ρ.comp π).range ≤ ρ.range := by
      rintro _ ⟨y, rfl⟩
      exact ⟨π y, rfl⟩
    exact Subgroup.commutator_mono hle hle hc2
  · have hrange : ρ.range = (ρ.comp π).range := by
      rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hπ, ← MonoidHom.range_eq_map]
    have hkerc : (ρ.comp π).ker = φ₀.ker := by
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, hk]
    rw [hrange, ← hφr]
    exact (Nat.card_congr (QuotientGroup.quotientKerEquivRange (ρ.comp π)).toEquiv).symm.trans
      ((Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hkerc).toEquiv).trans
        (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ₀).toEquiv))


theorem sec717LTyping_of_kstruct (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hZV : Sec7ZVStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hNbK : Sec717NbarKStructureStatement)
    (hInv : Sec717InvStatement) : Sec717LTypingStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZNc hTI L hL hLn m γ M₀ hM φ hφπ
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQL : Q ≤ L := hL.1
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hK : Nat.card (GaloisField 2 m) = Nat.card Z := hM.card
  have hq : 2 ≤ Nat.card Z := two_le_card_Z_of_ctx hc
  obtain ⟨Tt, hTtR, -, -, -⟩ :=
    Ctx.move_Tt_facts hZV hZc hZcard hc hs hp3 hZ0 M₀ hM.card φ hφπ
  have hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = Tt 1 := fun a ha ha1 => by
    have h := hTtR 1 a ha ha1
    rwa [one_mul, inv_one, mul_one] at h
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hZ0M hsZ0
  have hsH : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) :=
    (mk_mem_bar_iff_sec4 hQH _).mpr (hRH (hZ0.le hsZ0))
  set a₀ : ↥(bar M Q (H0 M Z)) := ⟨_, hsH⟩
  have ha₀ : a₀ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :=
    Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQZ0 _).mpr hsZ0)
  have ha₀1 : a₀ ≠ 1 := fun h => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)))
  have D := Ctx.sec717LayerData h34 h311a hZt hZcard hZc h78 hZV h52a hA hc hs hp3 hZ0 hZNc hTI
    hL hLn M₀ hM φ hφπ (Tt 1) hT
  obtain ⟨hroot, -⟩ :=
    hc.sec717_rootGroup hZcard hZc hZV hs hp3 hZ0 M₀ hM φ hφπ (Tt 1) hT a₀ ha₀ ha₀1
  have Bs := Ctx.yBase h34 h311a hZt hZcard hZc h78 hc hs hp3 hZ0 hZNc hTI hL hLn
  have hS : ∀ g ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ c : GaloisField 2 m,
      ∃ g' ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ w ∈ M₀.B.orthogonal (Tt 1),
        opm (φ g') w = c • opm (φ g) w := by
    intro g hg c
    obtain ⟨g', hg', hcor⟩ :=
      hNbK G M Q Z B hc n t hs hp3 Z0 hZ0 m γ M₀ hM φ hφπ (Tt 1) hT g hg c
    refine ⟨g', hg', fun w hw => ?_⟩
    have h := hcor.mid w hw
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at h
  have hNcard : Nat.card ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) =
      Nat.card (GaloisField 2 m) ^ 8 *
        Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
    rw [Bs.Ncard, Bs.Vcard, hK]
    ring
  have hLcard : Nat.card ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z))) =
      Nat.card (GaloisField 2 m) ^ 4 *
        Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
    rw [Bs.Lcard, Bs.Vcard, hK]
    ring
  have hLR : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ l ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
        r * l * r⁻¹ ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)) := fun r hr l hl =>
    (Subgroup.mem_normalizer_iff.mp (Bs.Ln r (Bs.RK hr)) l).mp hl
  have hΔ := D.exists_delta_smul_of_comm (Bs.VL.trans Bs.LN) ha₀ ha₀1 hroot hS Bs.ZN hNcard
    Bs.LN Bs.VL Bs.Lcomm hLcard
  have hinvL : ∀ A : Subgroup ↥(bar M Q (H0 M Z)),
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤ A →
      A ≤ (bar M Q L).subgroupOf (bar M Q (H0 M Z)) →
      (∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)), ∀ a ∈ A,
        r * a * r⁻¹ ∈ A) →
      A = (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ∨
        A = (bar M Q L).subgroupOf (bar M Q (H0 M Z)) := by
    intro A hVA hAL hAinv
    have hZ0A : Z0 ≤ barPreH0 M Q Z A := by
      refine le_barPreH0 hQZ0 hZ0M fun s hs => ?_
      have hsb : QuotientGroup.mk' (Q.subgroupOf M) s ∈ bar M Q Z0 :=
        (mk_mem_bar_iff_sec4 hQZ0 s).mpr hs
      exact ⟨bar_mono' (hZ0.le.trans hRH) hsb, hVA (Subgroup.mem_subgroupOf.mpr hsb)⟩
    have hAL' : barPreH0 M Q Z A ≤ L := barPreH0_le hQL hAL
    have hAN : barPreH0 M Q Z A ≤ hc.CN t := hAL'.trans hL.2.1
    have hRinv := barPreH0_conj hRH hQR hAinv
    rcases hInv G M Q Z B hc n t hs hp3 Z0 hZ0 (barPreH0 M Q Z A) hZ0A hAN
        (sec717_conj_eq_of_inv hRinv) with h | h | h
    · left
      rw [← bar_barPreH0 A, h]
    ·
      exfalso
      have hNL : (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ≤
          (bar M Q L).subgroupOf (bar M Q (H0 M Z)) := by
        have h1 := bar_barPreH0 (M := M) (Q := Q) (Z := Z) A
        rw [h] at h1
        rw [h1]
        exact hAL
      have h2 := Subgroup.card_le_of_le hNL
      rw [Bs.Ncard, Bs.Lcard] at h2
      have h3 : Nat.card Z ^ 5 < Nat.card Z ^ 9 := Nat.pow_lt_pow_right (by omega) (by norm_num)
      omega
    · right
      have heq : barPreH0 M Q Z A = L :=
        Subgroup.eq_of_le_of_card_ge hAL' (by rw [hL.2.2.1, h.2.2.1])
      rw [← bar_barPreH0 A, heq]
  set Sd := S717LN.deltaSub D Bs.LN hΔ with hSd
  set ρS := S717LN.deltaRep D Bs.LN hLR hΔ with hρS
  have hcardS : Nat.card ↥Sd = Nat.card (GaloisField 2 m) ^ 4 := by
    have h1 := S717LN.card_deltaSub_mul D Bs.LN Bs.VL hΔ
    rw [hLcard] at h1
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h1
  have hfinS : Module.finrank (GaloisField 2 m) ↥Sd = 4 := by
    have h1 : Nat.card ↥Sd =
        Nat.card (GaloisField 2 m) ^ Module.finrank (GaloisField 2 m) ↥Sd :=
      Module.natCard_eq_pow_finrank
    have hK2 : 2 ≤ Nat.card (GaloisField 2 m) := by
      rw [hK]
      exact hq
    exact Nat.pow_right_injective hK2 (h1.symm.trans hcardS)
  have hker : ∀ r, ρS r = 1 ↔ (r : ↥(bar M Q (H0 M Z))) ∈
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) :=
    S717LN.deltaRep_eq_one_iff D Bs.LN Bs.VL Bs.NR hLR hΔ (Ctx.sec717_RN_simple hc hs hp3)
      hinvL (by rw [hfinS]; norm_num)
  obtain ⟨K', fK', finK', hK'Z, φ₀, hφr, hφker, -⟩ := hp3
  haveI : CharP K' 2 := by
    obtain ⟨k, -, hk, -⟩ := hc.hyp.cp
    exact charP_two_of_card_eq_two_pow (hK'Z.trans hk)
  have hφker' : ∀ x, φ₀ x = 1 ↔ (x : G) ∈ hc.CN t := fun x => by
    rw [← MonoidHom.mem_ker, hφker, Subgroup.mem_subgroupOf]
  let π : ↥(Rt M (LB M Q B) t) →*
      ↥((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) :=
    MonoidHom.codRestrict
      (MonoidHom.codRestrict ((QuotientGroup.mk' (Q.subgroupOf M)).comp
        (Subgroup.inclusion (hc.Rt_le_M t))) (bar M Q (H0 M Z)) fun x =>
          (mk_mem_bar_iff_sec4 hQH _).mpr (hRH x.2))
      _ fun x => Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQR _).mpr x.2)
  have hπs : Function.Surjective π := by
    intro r
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M)
      ((r : ↥(bar M Q (H0 M Z))) : Mbar M Q)
    have hyR : (y : G) ∈ Rt M (LB M Q B) t :=
      (mk_mem_bar_iff_sec4 hQR y).mp (hy ▸ Subgroup.mem_subgroupOf.mp r.2)
    exact ⟨⟨(y : G), hyR⟩, Subtype.ext (Subtype.ext hy)⟩
  have hπN : ∀ x, ((π x : ↥(bar M Q (H0 M Z)))) ∈
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ↔ (x : G) ∈ hc.CN t := fun x => by
    rw [Subgroup.mem_subgroupOf]
    exact mk_mem_bar_iff_sec4 hQN _
  obtain ⟨hperf, hcardR'⟩ := S717LN.perf_card_of_omega ρS π hπs φ₀ hφr fun x =>
    (hker _).trans ((hπN x).trans (hφker' x).symm)
  have hcardR : Nat.card ρS.range =
      Nat.card (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 2 m)) := by
    obtain ⟨eΩ⟩ := nonempty_statedOmega_quadPlus_three_mulEquiv (K := K') (hK'Z ▸ hc.hyp.q4)
    rw [hcardR', Nat.card_congr eΩ.toEquiv, StatedAPI.card_statedSL]
    exact S717LN.card_sl4_eq (hK'Z.trans hK.symm)
  obtain ⟨η, e, hηs, hηk, hηe⟩ := SL4Lin.exists_sl4_of_linear hfinS ρS hperf hcardR
  let θ : ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z))) →*
      Multiplicative (Fin 4 → GaloisField 2 m) :=
    (AddEquiv.toMultiplicative e.toAddEquiv).toMonoidHom.comp (S717LN.deltaHom D Bs.LN hΔ)
  refine ⟨η, hηs, fun r => (hηk r).trans (hker r), θ, ?_, fun l => ?_, fun r l l' hll' => ?_⟩
  · intro y
    obtain ⟨l, hl⟩ := S717LN.deltaHom_surjective D Bs.LN hΔ
      (Multiplicative.ofAdd (e.symm (Multiplicative.toAdd y)))
    refine ⟨l, ?_⟩
    change Multiplicative.ofAdd (e (Multiplicative.toAdd (S717LN.deltaHom D Bs.LN hΔ l))) = y
    rw [hl]
    simp
  · rw [← S717LN.deltaHom_eq_one_iff D Bs.LN hΔ l]
    change Multiplicative.ofAdd (e (Multiplicative.toAdd (S717LN.deltaHom D Bs.LN hΔ l))) = 1 ↔ _
    constructor
    · intro h1
      apply Multiplicative.toAdd.injective
      apply e.injective
      have h2 := congrArg Multiplicative.toAdd h1
      simpa using h2
    · intro h1
      rw [h1]
      simp
  · change e (Multiplicative.toAdd (S717LN.deltaHom D Bs.LN hΔ l')) =
      η r • e (Multiplicative.toAdd (S717LN.deltaHom D Bs.LN hΔ l))
    rw [S717LN.deltaRep_deltaHom D Bs.LN hLR hΔ r l l' hll', hηe]

end CFSG.RankThree.GF2n.Stroth80
