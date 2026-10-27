module

public import CFSG.RankThree.GF2n.Stroth80.Sec717RepFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec717LayersRootB
public import CFSG.RankThree.GF2n.Stroth80.Sec717QLayers
public import CFSG.RankThree.GF2n.Stroth80.Sec717RSylow
public import CFSG.RankThree.GF2n.Stroth80.Sec717ZNProof
public import CFSG.RankThree.GF2n.Stroth80.Sec717QLayersW1
public import CFSG.RankThree.GF2n.Stroth80.Sec311bNatData

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  [(Q.subgroupOf M).Normal]

@[expose] def barPreH0 (M Q Z : Subgroup G) [(Q.subgroupOf M).Normal]
    (A : Subgroup ↥(bar M Q (H0 M Z))) : Subgroup G :=
  ((A.map (bar M Q (H0 M Z)).subtype).comap (QuotientGroup.mk' (Q.subgroupOf M))).map M.subtype

theorem mem_barPreH0 {A : Subgroup ↥(bar M Q (H0 M Z))} (y : ↥M) :
    (y : G) ∈ barPreH0 M Q Z A ↔
      QuotientGroup.mk' (Q.subgroupOf M) y ∈ A.map (bar M Q (H0 M Z)).subtype := by
  constructor
  · rintro ⟨y', hy', hyy'⟩
    have : y' = y := Subtype.ext hyy'
    rw [← this]
    exact hy'
  · intro h
    exact ⟨y, h, rfl⟩

theorem bar_barPreH0 (A : Subgroup ↥(bar M Q (H0 M Z))) :
    (bar M Q (barPreH0 M Q Z A)).subgroupOf (bar M Q (H0 M Z)) = A := by
  have h1 : (barPreH0 M Q Z A).subgroupOf M =
      (A.map (bar M Q (H0 M Z)).subtype).comap (QuotientGroup.mk' (Q.subgroupOf M)) := by
    ext x
    rw [Subgroup.mem_subgroupOf, mem_barPreH0, Subgroup.mem_comap]
  have h2 : bar M Q (barPreH0 M Q Z A) = A.map (bar M Q (H0 M Z)).subtype := by
    rw [bar, h1, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
  ext a
  rw [Subgroup.mem_subgroupOf, h2]
  exact Subgroup.mem_map_iff_mem (bar M Q (H0 M Z)).subtype_injective

theorem le_barPreH0 {S : Subgroup G} (hQS : Q ≤ S) (hSM : S ≤ M) {A : Subgroup ↥(bar M Q (H0 M Z))}
    (hSA : ∀ s : ↥M, (s : G) ∈ S → ∃ h, (⟨QuotientGroup.mk' (Q.subgroupOf M) s, h⟩ :
      ↥(bar M Q (H0 M Z))) ∈ A) : S ≤ barPreH0 M Q Z A := by
  intro x hx
  obtain ⟨h, hA⟩ := hSA ⟨x, hSM hx⟩ hx
  exact (mem_barPreH0 (A := A) ⟨x, hSM hx⟩).mpr ⟨_, hA, rfl⟩

theorem barPreH0_le {S : Subgroup G} (hQS : Q ≤ S) {A : Subgroup ↥(bar M Q (H0 M Z))}
    (hAS : A ≤ (bar M Q S).subgroupOf (bar M Q (H0 M Z))) : barPreH0 M Q Z A ≤ S := by
  rintro _ ⟨y, ⟨a, ha, hay⟩, rfl⟩
  have h1 : a ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)) := hAS ha
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q S := by
    rw [← hay]
    exact h1
  exact (mk_mem_bar_iff_sec4 hQS y).mp h2

theorem barPreH0_conj {R : Subgroup G} (hRH : R ≤ H0 M Z) (hQR : Q ≤ R)
    {A : Subgroup ↥(bar M Q (H0 M Z))}
    (hA : ∀ r ∈ (bar M Q R).subgroupOf (bar M Q (H0 M Z)), ∀ a ∈ A, r * a * r⁻¹ ∈ A) :
    ∀ r ∈ R, ∀ c ∈ barPreH0 M Q Z A, r * c * r⁻¹ ∈ barPreH0 M Q Z A := by
  rintro r hr _ ⟨y, ⟨a, ha, hay⟩, rfl⟩
  have hrM : r ∈ M := (hRH hr).1
  set rr : ↥M := ⟨r, hrM⟩
  have hrb : QuotientGroup.mk' (Q.subgroupOf M) rr ∈ bar M Q R :=
    (mk_mem_bar_iff_sec4 hQR rr).mpr hr
  have hrH : QuotientGroup.mk' (Q.subgroupOf M) rr ∈ bar M Q (H0 M Z) := bar_mono' hRH hrb
  set rbar : ↥(bar M Q (H0 M Z)) := ⟨_, hrH⟩
  have hrbar : rbar ∈ (bar M Q R).subgroupOf (bar M Q (H0 M Z)) := Subgroup.mem_subgroupOf.mpr hrb
  have hconj := hA rbar hrbar a ha
  refine (mem_barPreH0 (A := A) (rr * y * rr⁻¹)).mpr ⟨_, hconj, ?_⟩
  have hay' : (a : Mbar M Q) = QuotientGroup.mk' (Q.subgroupOf M) y := hay
  show ((rbar * a * rbar⁻¹ : ↥(bar M Q (H0 M Z))) : Mbar M Q) =
    QuotientGroup.mk' (Q.subgroupOf M) (rr * y * rr⁻¹)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hay', map_mul, map_mul, map_inv]

theorem sec717MoveRep_of_layers (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hZV : Sec7ZVStatement) (hCN : Sec7CommNStatement)
    (h52a : Stroth52aStatement) (hA : Sec7AExistsStatement) (hInv : Sec717InvStatement)
    (hL : Sec717QLayersStatement) (hSyl : Sec717RSylowStatement) : Sec717MoveRepStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZNc hTI L hL' hLn m γ M₀ hM φ hφπ Tt hTtR
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hQL : Q ≤ L := hL'.1
  have hLN : L ≤ hc.CN t := hL'.2.1
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hZ0M : Z0 ≤ M := hc.centre_le_M t hZ0
  have hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = Tt 1 := fun a ha ha1 => by
    have h := hTtR 1 a ha ha1
    simp only [one_mul, inv_one, mul_one] at h
    exact h
  have LD := Ctx.sec717LayerData h34 h311a hZt hZcard hZc h78 hZV h52a hA hc hs hp3 hZ0 hZNc hTI
    hL' hLn M₀ hM φ hφπ (Tt 1) hT
  have Bs := Ctx.yBase h34 h311a hZt hZcard hZc h78 hc hs hp3 hZ0 hZNc hTI hL' hLn
  have hroot := Ctx.sec717_rootGroup hZcard hZc hZV hc hs hp3 hZ0 M₀ hM φ hφπ (Tt 1) hT
  have hfix := Ctx.sec717_fixed_P_mod_T h34 hZcard hZc hZV h52a hc hs hp3 hZ0 M₀ hM φ hφπ (Tt 1) hT
  have heven := Ctx.sec717_even_finrank_map_opm hZcard hZc hZV hc hs hp3 hZ0 M₀ hM φ hφπ (Tt 1) hT
  have hirr := Ctx.sec717_T_irred hZcard hZc hZV hc hs hZ0 M₀ φ hφπ (Tt 1) hT
  have hsimple := Ctx.sec717_RN_simple hc hs hp3
  obtain ⟨hquadIso, hkL⟩ := hL G M Q Z B hc n t hs hp3 Z0 hZ0 hZNc hTI L hL' hLn m γ M₀ hM φ hφπ
  obtain ⟨S, hSR⟩ := hSyl G M Q Z B hc n t hs hp3 Z0 hZ0 hZNc hTI L hL' hLn
  have h2 : (2 : GaloisField 2 m) = 0 := by
    have := CharP.cast_eq_zero (GaloisField 2 m) 2
    simpa using this
  have hcardK : 4 ≤ Nat.card (GaloisField 2 m) := hM.card ▸ hc.hyp.q4
  have hRcent : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), r * a = a * r := by
    intro r hr a ha
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (r : Mbar M Q)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (a : Mbar M Q)
    have hxR : (x : G) ∈ Rt M (LB M Q B) t :=
      (mk_mem_bar_iff_sec4 hQR x).mp (hx ▸ Subgroup.mem_subgroupOf.mp hr)
    have hyZ : (y : G) ∈ Z0 :=
      (mk_mem_bar_iff_sec4 hQZ0 y).mp (hy ▸ Subgroup.mem_subgroupOf.mp ha)
    have hyx : ⁅(y : G), (x : G)⁆ ∈ Q := ((hZ0 y).mp hyZ).2 x hxR
    apply Subtype.ext
    show (r : Mbar M Q) * (a : Mbar M Q) = (a : Mbar M Q) * (r : Mbar M Q)
    rw [← hx, ← hy]
    have h1 : QuotientGroup.mk' (Q.subgroupOf M) ⁅y, x⁆ = 1 := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact Subgroup.mem_subgroupOf.mpr (by simpa [commutatorElement_def] using hyx)
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hNcomm : ∀ a ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ b ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
        ⁅a, b⁆ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
    intro a ha b hb
    obtain ⟨x, hx⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (a : Mbar M Q)
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (b : Mbar M Q)
    have hxN : (x : G) ∈ hc.CN t :=
      (mk_mem_bar_iff_sec4 hQN x).mp (hx ▸ Subgroup.mem_subgroupOf.mp ha)
    have hyN : (y : G) ∈ hc.CN t :=
      (mk_mem_bar_iff_sec4 hQN y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hb)
    have hcomm : ⁅(x : G), (y : G)⁆ ∈ Z0 :=
      hCN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator hxN hyN)
    rw [Subgroup.mem_subgroupOf]
    show ⁅(a : Mbar M Q), (b : Mbar M Q)⁆ ∈ bar M Q Z0
    rw [← hx, ← hy, ← map_commutatorElement]
    have hxy : (((⁅x, y⁆ : ↥M)) : G) = ⁅(x : G), (y : G)⁆ := by
      simp [commutatorElement_def]
    exact (mk_mem_bar_iff_sec4 hQZ0 ⁅x, y⁆).mpr (hxy ▸ hcomm)
  have hRnorm : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      r ∈ normalizer (((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) : Subgroup _) : Set _) := by
    intro r hr
    have := Bs.RK hr
    rwa [Bs.K_eq] at this
  have hinv : ∀ C : Subgroup ↥(bar M Q (H0 M Z)),
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤ C →
      C ≤ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) →
      (∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)), ∀ c ∈ C,
        r * c * r⁻¹ ∈ C) →
      C = (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ∨
        C = (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ∨ Sec717L hc t Z0 (barPreH0 M Q Z C) := by
    intro C hVC hCN' hCinv
    have hZ0C : Z0 ≤ barPreH0 M Q Z C := by
      refine le_barPreH0 hQZ0 hZ0M fun s hs => ?_
      have hsb : QuotientGroup.mk' (Q.subgroupOf M) s ∈ bar M Q Z0 :=
        (mk_mem_bar_iff_sec4 hQZ0 s).mpr hs
      exact ⟨bar_mono' (hZ0.le.trans hRH) hsb, hVC (Subgroup.mem_subgroupOf.mpr hsb)⟩
    have hCNt : barPreH0 M Q Z C ≤ hc.CN t := barPreH0_le hQN hCN'
    have hRinv := barPreH0_conj hRH hQR hCinv
    rcases hInv G M Q Z B hc n t hs hp3 Z0 hZ0 (barPreH0 M Q Z C) hZ0C hCNt
        (sec717_conj_eq_of_inv hRinv) with h | h | h
    · left
      rw [← bar_barPreH0 C, h]
    · right; left
      rw [← bar_barPreH0 C, h]
    · right; right
      exact h
  have hq : 2 ≤ Nat.card Z := two_le_card_Z_of_ctx hc
  have hq5 : Nat.card Z < Nat.card Z ^ 5 := by
    calc Nat.card Z = Nat.card Z ^ 1 := (pow_one _).symm
      _ < Nat.card Z ^ 5 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hq59 : Nat.card Z ^ 5 < Nat.card Z ^ 9 := Nat.pow_lt_pow_right (by omega) (by norm_num)
  have hLV : ¬ (bar M Q L).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
    intro h
    have := Subgroup.card_le_of_le h
    rw [Bs.Lcard, Bs.Vcard] at this
    omega
  have hNL : ¬ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q L).subgroupOf (bar M Q (H0 M Z)) := by
    intro h
    have := Subgroup.card_le_of_le h
    rw [Bs.Ncard, Bs.Lcard] at this
    omega
  have hLcard : Nat.card L = Nat.card Q * Nat.card Z ^ 5 := hL'.2.2.1
  have hL_eq_of : ∀ C : Subgroup ↥(bar M Q (H0 M Z)),
      (bar M Q L).subgroupOf (bar M Q (H0 M Z)) ≤ C ∨ C ≤ (bar M Q L).subgroupOf (bar M Q (H0 M Z)) →
      Sec717L hc t Z0 (barPreH0 M Q Z C) → C = (bar M Q L).subgroupOf (bar M Q (H0 M Z)) := by
    intro C hC hSL
    have heq : barPreH0 M Q Z C = L := by
      rcases hC with hLC | hCL
      · have hle : L ≤ barPreH0 M Q Z C := by
          refine le_barPreH0 hQL (hLN.trans (hNR.trans (hRH.trans fun x hx => hx.1))) fun s hs => ?_
          have hsb : QuotientGroup.mk' (Q.subgroupOf M) s ∈ bar M Q L :=
            (mk_mem_bar_iff_sec4 hQL s).mpr hs
          exact ⟨bar_mono' (hLN.trans (hNR.trans hRH)) hsb, hLC (Subgroup.mem_subgroupOf.mpr hsb)⟩
        exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hLcard, hSL.2.2.1])).symm
      · exact Subgroup.eq_of_le_of_card_ge (barPreH0_le hQL hCL) (by rw [hLcard, hSL.2.2.1])
    rw [← bar_barPreH0 C, heq]
  have I : Sec717RepInputs M₀.B M₀.Qf φ ((bar M Q Z0).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q L).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)))
      ((bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z))) (Tt 1) := by
    refine
      { layer := LD
        char2 := h2
        exists_ne := exists_ne_zero_ne_one_of_nat_card_ge_four hcardK
        Qf_add := M₀.Qf_add
        Qf_smul := M₀.Qf_smul
        Qf_isom := hc.phi_Qf_eq M₀ φ hφπ
        VL := Bs.VL
        LN := Bs.LN
        NR := Bs.NR
        Rb_cent := hRcent
        Rb_normL := fun r hr l hl =>
          (mem_normalizer_iff.mp (Bs.Ln r (Bs.RK hr)) l).mp hl
        Rb_normN := fun r hr x hx =>
          (mem_normalizer_iff.mp (Bs.Nn r (Bs.RK hr)) x).mp hx
        Nb_comm := hNcomm
        L_comm := Bs.Lcomm
        V_sq := Bs.Vsq
        root := hroot
        cfix := hfix
        evenT := heven
        irrT := hirr
        simple := hsimple
        invL := ?_
        CNL := ?_
        L_ne_V := ?_
        Nb_ne_L := ?_
        quadIso := hquadIso
        kL := hkL
        two := two_elements_of_sylow (fun r hr => hRnorm r hr)
          (fun k hk => by rw [← Bs.K_eq] at hk; exact Bs.Rn k hk) S hSR }
    ·
      intro C hVC hCL hCinv
      rcases hinv C hVC (hCL.trans Bs.LN) hCinv with h | h | h
      · left; exact h
      · exact absurd (h ▸ hCL) hNL
      · right; exact hL_eq_of C (Or.inr hCL) h
    ·
      intro x hx hxL
      let C : Subgroup ↥(bar M Q (H0 M Z)) :=
        (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) ⊓
          centralizer (((bar M Q L).subgroupOf (bar M Q (H0 M Z)) : Subgroup _) : Set _)
      have hLC : (bar M Q L).subgroupOf (bar M Q (H0 M Z)) ≤ C := fun l hl =>
        ⟨Bs.LN hl, mem_centralizer_iff.mpr fun l' hl' => Bs.Lcomm l' hl' l hl⟩
      have hCinv : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)), ∀ c ∈ C,
          r * c * r⁻¹ ∈ C := by
        rintro r hr c ⟨hcN, hcL⟩
        refine ⟨(mem_normalizer_iff.mp (Bs.Nn r (Bs.RK hr)) c).mp hcN,
          mem_centralizer_iff.mpr fun l hl => ?_⟩
        have hl' : r⁻¹ * l * r⁻¹⁻¹ ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)) :=
          (mem_normalizer_iff.mp (Bs.Ln r⁻¹ (Bs.RK (Subgroup.inv_mem _ hr))) l).mp hl
        have h1 := mem_centralizer_iff.mp hcL _ hl'
        calc l * (r * c * r⁻¹) = r * ((r⁻¹ * l * r⁻¹⁻¹) * c) * r⁻¹ := by group
          _ = r * (c * (r⁻¹ * l * r⁻¹⁻¹)) * r⁻¹ := by rw [h1]
          _ = r * c * r⁻¹ * l := by group
      rcases hinv C ((Bs.VL).trans hLC) inf_le_left hCinv with h | h | h
      · exact absurd (hLC.trans (le_of_eq h)) hLV
      · exfalso
        apply hLV
        intro l hl
        refine Bs.ZN l (Bs.LN hl) fun y hy => ?_
        have hyC : y ∈ C := h ▸ hy
        exact mem_centralizer_iff.mp hyC.2 l hl
      · have hCeq := hL_eq_of C (Or.inl hLC) h
        exact hCeq ▸ (⟨hx, mem_centralizer_iff.mpr fun l hl => (hxL l hl).symm⟩ : x ∈ C)
    ·
      by_contra h
      push Not at h
      exact hLV h
    ·
      by_contra h
      push Not at h
      exact hNL h
  exact I.moveFrameRep hTtR

end CFSG.RankThree.GF2n.Stroth80
