module

public import CFSG.RankThree.GF2n.Stroth80.Sec717QLayers
public import CFSG.RankThree.GF2n.Stroth80.Sec717LayerModelDefs
import CFSG.RankThree.GF2n.Stroth80.Sec717LayersRoot
import CFSG.RankThree.GF2n.Stroth80.Sec717DeltaKSpace
import CFSG.RankThree.GF2n.Stroth80.Sec717QLayersIsotropic
public import CFSG.RankThree.GF2n.Stroth80.Sec7TailMoveRep

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix


theorem sec717QLayers_of_layerModel (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZc : Sec7CentreMpStatement)
    (h78 : Stroth78Statement) (hZV : Sec7ZVStatement) (h52a : Stroth52aStatement)
    (hA : Sec7AExistsStatement) (hNbK : Sec717NbarKStructureStatement)
    (hWedge : Sec717LayerWedgeStatement) (hW3 : SL4HomW3Statement)
    (hNoInv : SL4NoInvFormStatement) : Sec717QLayersStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0 hZNc hTI L hL hLn m γ M₀ hM φ hφπ
  classical
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hQZ0 : Q ≤ Z0 := hc.Q_le_centre ht hZ0
  have hQH : Q ≤ H0 M Z := hc.Q_le_H0'
  have hQR : Q ≤ Rt M (LB M Q B) t := hc.Q_le_Rt ht
  have hQN : Q ≤ hc.CN t := hc.Q_le_CN' ht
  have hQL : Q ≤ L := hL.1
  have hNM : hc.CN t ≤ M := fun x hx => hc.Rt_le_M t (Ctx.mem_CN.mp hx).1
  have hK : Nat.card (GaloisField 2 m) = Nat.card Z := hM.card
  have hK4 : 4 ≤ Nat.card (GaloisField 2 m) := hK ▸ hc.hyp.q4
  obtain ⟨Tt, hTtR, -, -, -⟩ :=
    Ctx.move_Tt_facts hZV hZc hZcard hc hs hp3 hZ0 M₀ hM.card φ hφπ
  have hT : ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), a ≠ 1 →
      LinearMap.range (opm (φ a)) = Tt 1 := fun a ha ha1 => by
    have h := hTtR 1 a ha ha1
    rwa [one_mul, inv_one, mul_one] at h
  obtain ⟨s, hsZ0, hsQ⟩ := sec7_exists_Z0_not_Q hZcard hc hs hZ0
  have hsM : s ∈ M := hc.centre_le_M t hZ0 hsZ0
  have hsH : QuotientGroup.mk' (Q.subgroupOf M) ⟨s, hsM⟩ ∈ bar M Q (H0 M Z) :=
    (mk_mem_bar_iff_sec4 hQH _).mpr ((hc.Rt_le_H0 t) (hZ0.le hsZ0))
  set a₀ : ↥(bar M Q (H0 M Z)) := ⟨_, hsH⟩
  have ha₀ : a₀ ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) :=
    Subgroup.mem_subgroupOf.mpr ((mk_mem_bar_iff_sec4 hQZ0 _).mpr hsZ0)
  have ha₀1 : a₀ ≠ 1 := fun h => hsQ (Subgroup.mem_subgroupOf.mp
    ((QuotientGroup.eq_one_iff _).mp (congrArg Subtype.val h)))
  have D := Ctx.sec717LayerData h34 h311a hZt hZcard hZc h78 hZV h52a hA hc hs hp3 hZ0 hZNc hTI
    hL hLn M₀ hM φ hφπ (Tt 1) hT
  obtain ⟨hroot, hroot'⟩ :=
    hc.sec717_rootGroup hZcard hZc hZV hs hp3 hZ0 M₀ hM φ hφπ (Tt 1) hT a₀ ha₀ ha₀1
  obtain ⟨η, hη, -, ⟨θ, hθ, hθker, hθeq⟩, ψ, hψ⟩ :=
    hWedge G M Q Z B hc n t hs hp3 Z0 hZ0 hZNc hTI L hL hLn m γ M₀ hM φ hφπ (Tt 1) hT
  have hlift : ∀ {S : Subgroup G}, Q ≤ S → ∀ x ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)),
      ∃ y : ↥M, (y : G) ∈ S ∧ QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) := by
    intro S hQS x hx
    obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
    exact ⟨y, (mk_mem_bar_iff_sec4 hQS y).mp (hy ▸ Subgroup.mem_subgroupOf.mp hx), hy⟩
  have hbarmem : ∀ {S : Subgroup G}, Q ≤ S → ∀ (x : ↥(bar M Q (H0 M Z))) (y : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) y = (x : Mbar M Q) → (y : G) ∈ S →
        x ∈ (bar M Q S).subgroupOf (bar M Q (H0 M Z)) := fun hQS x y hy hyS =>
    Subgroup.mem_subgroupOf.mpr (hy ▸ (mk_mem_bar_iff_sec4 hQS y).mpr hyS)
  have hcommQ : ∀ (x y : ↥(bar M Q (H0 M Z))) (x' y' : ↥M),
      QuotientGroup.mk' (Q.subgroupOf M) x' = (x : Mbar M Q) →
      QuotientGroup.mk' (Q.subgroupOf M) y' = (y : Mbar M Q) →
      ⁅(x' : G), (y' : G)⁆ ∈ Q → x * y = y * x := by
    intro x y x' y' hx hy hxy
    have hq : ⁅x', y'⁆ ∈ Q.subgroupOf M := by
      rw [Subgroup.mem_subgroupOf]
      have e : (((⁅x', y'⁆ : ↥M)) : G) = ⁅(x' : G), (y' : G)⁆ := by simp [commutatorElement_def]
      rw [e]
      exact hxy
    have h1 : ⁅QuotientGroup.mk' (Q.subgroupOf M) x',
        QuotientGroup.mk' (Q.subgroupOf M) y'⁆ = 1 := by
      rw [← map_commutatorElement, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hq
    rw [commutatorElement_eq_one_iff_mul_comm, hx, hy] at h1
    exact Subtype.ext h1
  have hVN : (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hZNc.le (Subgroup.mem_subgroupOf.mp hx))
  have hLN : (bar M Q L).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hL.2.1 (Subgroup.mem_subgroupOf.mp hx))
  have hVL : (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) ≤
      (bar M Q L).subgroupOf (bar M Q (H0 M Z)) := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (bar_mono' hL.2.2.2.2.2 (Subgroup.mem_subgroupOf.mp hx))
  have hcent : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ a ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)), r * a = a * r := by
    intro r hr a ha
    obtain ⟨x, hxR, hx⟩ := hlift hQR r hr
    obtain ⟨y, hyZ, hy⟩ := hlift hQZ0 a ha
    exact (hcommQ a r y x hy hx (((hZ0 y).mp hyZ).2 x hxR)).symm
  have hLR : ∀ r ∈ (bar M Q (Rt M (LB M Q B) t)).subgroupOf (bar M Q (H0 M Z)),
      ∀ l ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
        r * l * r⁻¹ ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)) := by
    intro r hr l hl
    obtain ⟨x, hxR, hx⟩ := hlift hQR r hr
    obtain ⟨y, hyL, hy⟩ := hlift hQL l hl
    have hxy : (x : G) * (y : G) * (x : G)⁻¹ ∈ L := by
      have hmem : (x : G) * (y : G) * (x : G)⁻¹ ∈ conjSubgroup (x : G) L := by
        rw [CFSG.CGT.Timmesfeld75.mem_conjSubgroup]
        rw [show (x : G)⁻¹ * ((x : G) * (y : G) * (x : G)⁻¹) * (x : G) = y by group]
        exact hyL
      rwa [hL.2.2.2.1 x hxR] at hmem
    refine hbarmem hQL _ (x * y * x⁻¹) ?_ (by simpa using hxy)
    rw [map_mul, map_mul, map_inv, hx, hy]
    rfl
  have hLab : ∀ l ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
      ∀ l' ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)), l * l' = l' * l := by
    intro l hl l' hl'
    obtain ⟨x, hxL, hx⟩ := hlift hQL l hl
    obtain ⟨y, hyL, hy⟩ := hlift hQL l' hl'
    exact hcommQ l l' x y hx hy (hL.2.2.2.2.1 x hxL y hyL)
  have hZN : ∀ n ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)),
      (∀ m ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), n * m = m * n) →
        n ∈ (bar M Q Z0).subgroupOf (bar M Q (H0 M Z)) := by
    intro n hn hcomm
    obtain ⟨x, hxN, hx⟩ := hlift hQN n hn
    refine hbarmem hQZ0 n x hx ((hZNc x).mpr ⟨hxN, fun r hrN => ?_⟩)
    have hrM : r ∈ M := hNM hrN
    have hrH : QuotientGroup.mk' (Q.subgroupOf M) ⟨r, hrM⟩ ∈ bar M Q (H0 M Z) :=
      (mk_mem_bar_iff_sec4 hQH _).mpr ((hc.Rt_le_H0 t) (Ctx.mem_CN.mp hrN).1)
    have hrbar : (⟨_, hrH⟩ : ↥(bar M Q (H0 M Z))) ∈
        (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)) := hbarmem hQN _ ⟨r, hrM⟩ rfl hrN
    have h1 := hcomm _ hrbar
    have h2 : QuotientGroup.mk' (Q.subgroupOf M) ⁅x, (⟨r, hrM⟩ : ↥M)⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm, hx]
      exact congrArg Subtype.val h1
    have h3 := (QuotientGroup.eq_one_iff _).mp h2
    rw [Subgroup.mem_subgroupOf] at h3
    simpa [commutatorElement_def] using h3
  have hRH : Rt M (LB M Q B) t ≤ H0 M Z := hc.Rt_le_H0 t
  have hNR : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
  have hbarcard : ∀ {S : Subgroup G}, Q ≤ S → S ≤ H0 M Z →
      Nat.card ↥((bar M Q S).subgroupOf (bar M Q (H0 M Z))) * Nat.card Q = Nat.card S := by
    intro S hQS hSH
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe (bar_mono' hSH)).toEquiv]
    exact bar_card_mul_card_of_le hQS (hSH.trans inf_le_left)
  have hVcard : Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) = Nat.card Z := by
    have h := hbarcard hQZ0 (hZ0.le.trans hRH)
    rw [hZcard G M Q Z B hc n t hs Z0 hZ0, Nat.mul_comm (Nat.card Q)] at h
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h
  have hNcard : Nat.card ↥((bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z))) =
      Nat.card (GaloisField 2 m) ^ 8 * Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
    have hcN78 := h78 G M Q Z B hc n t hs.toSec5 hs.large hs.notPlus4 3 (by norm_num) (Or.inl hp3)
    unfold Conc78 at hcN78
    rcases hcN78 with ⟨-, -, h9⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
    · have h := hbarcard hQN (hNR.trans hRH)
      rw [h9, Nat.mul_comm (Nat.card Q)] at h
      rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos h, hVcard, hK, ← pow_succ]
    all_goals omega
  have hLcard : Nat.card ↥((bar M Q L).subgroupOf (bar M Q (H0 M Z))) =
      Nat.card (GaloisField 2 m) ^ 4 * Nat.card ↥((bar M Q Z0).subgroupOf (bar M Q (H0 M Z))) := by
    have h := hbarcard hQL (hL.2.1.trans (hNR.trans hRH))
    rw [hL.2.2.1, Nat.mul_comm (Nat.card Q)] at h
    rw [Nat.eq_of_mul_eq_mul_right Nat.card_pos h, hVcard, hK, ← pow_succ]
  have hS : ∀ g ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ c : GaloisField 2 m,
      ∃ g' ∈ (bar M Q (hc.CN t)).subgroupOf (bar M Q (H0 M Z)), ∀ w ∈ M₀.B.orthogonal (Tt 1),
        opm (φ g') w = c • opm (φ g) w := by
    intro g hg c
    obtain ⟨g', hg', hcor⟩ :=
      hNbK G M Q Z B hc n t hs hp3 Z0 hZ0 m γ M₀ hM φ hφπ (Tt 1) hT g hg c
    refine ⟨g', hg', fun w hw => ?_⟩
    have h := hcor.mid w hw
    rwa [LinearMap.sub_apply, LinearMap.smul_apply, sub_eq_zero] at h
  have hΔ := D.exists_delta_smul_of_comm hVN ha₀ ha₀1 hroot hS hZN hNcard hLN hVL hLab hLcard
  have hiso := D.isotropic_of_layerModel hNoInv hK4 hLN hVL hLR hcent ha₀ ha₀1 hΔ η hη θ hθ hθker
    hθeq ψ hψ
  have hDD : ∀ l ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)),
      ∀ l' ∈ (bar M Q L).subgroupOf (bar M Q (H0 M Z)), ∀ x,
        opm (φ l) (opm (φ l') x) = 0 := by
    intro l hl l' hl' x
    refine D.nondeg.1 _ fun y => ?_
    have hadj : ∀ z, M₀.B (opm (φ l) z) y = M₀.B z (opm (φ l⁻¹) y) := fun z => by
      have h := D.isom l z (φ l⁻¹ y)
      rw [phi_apply_inv_apply] at h
      rw [opm_apply, opm_apply, map_sub, LinearMap.sub_apply, map_sub, h]
    rw [hadj]
    exact hiso l' hl' l⁻¹ (Subgroup.inv_mem _ hl) x y
  exact ⟨hiso, D.exists_opm_eq_smul_of_layerModel hW3 hK4 hLN hVL hLR hcent hDD ha₀ ha₀1 hroot
    hroot' hΔ η hη θ hθ hθker hθeq ψ hψ⟩

end CFSG.RankThree.GF2n.Stroth80
