module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailCaseA
public import CFSG.RankThree.GF2n.Stroth80.Sec717InvProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

@[expose] def sec717CentreN (M Q N : Subgroup G) (hNM : N ≤ M)
    (hQ : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q) : Subgroup G where
  carrier := {x | x ∈ N ∧ ∀ r ∈ N, ⁅x, r⁆ ∈ Q}
  mul_mem' := by
    rintro x y ⟨hx, hxr⟩ ⟨hy, hyr⟩
    refine ⟨N.mul_mem hx hy, fun r hr => ?_⟩
    have key : ⁅x * y, r⁆ = x * ⁅y, r⁆ * x⁻¹ * ⁅x, r⁆ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact Q.mul_mem (hQ x (hNM hx) _ (hyr r hr)) (hxr r hr)
  one_mem' := ⟨N.one_mem, fun r _ => by
    rw [commutatorElement_one_left]
    exact Q.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hxr⟩
    refine ⟨N.inv_mem hx, fun r hr => ?_⟩
    have key : ⁅x⁻¹, r⁆ = x⁻¹ * ⁅x, r⁆⁻¹ * x := by
      simp only [commutatorElement_def]
      group
    rw [key]
    have h1 := hQ x⁻¹ (M.inv_mem (hNM hx)) _ (Q.inv_mem (hxr r hr))
    simpa using h1

theorem mem_sec717CentreN {M Q N : Subgroup G} {hNM : N ≤ M}
    {hQ : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q} {x : G} :
    x ∈ sec717CentreN M Q N hNM hQ ↔ x ∈ N ∧ ∀ r ∈ N, ⁅x, r⁆ ∈ Q :=
  Iff.rfl

theorem sec717_conj_eq_of_inv {R C : Subgroup G} (h : ∀ r ∈ R, ∀ c ∈ C, r * c * r⁻¹ ∈ C) :
    ∀ r ∈ R, conjSubgroup r C = C := by
  intro r hr
  apply le_antisymm
  · intro x hx
    rw [mem_conjSubgroup] at hx
    have := h r hr _ hx
    simpa [mul_assoc] using this
  · intro x hx
    rw [mem_conjSubgroup]
    have := h r⁻¹ (R.inv_mem hr) x hx
    simpa [mul_assoc] using this

theorem sec717ZN_of_parts (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (h78 : Stroth78Statement) (hZc : Sec7ZCardStatement) (hCN : Sec7CommNStatement)
    (h711 : Stroth711StrongStatement) (cited : IrrQ4NoPairingStatement) :
    Sec717ZNStatement := by
  intro G _ _ M Q Z B _ hc n t hs hp3 Z0 hZ0
  have hp3c := hp3
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hNM : hc.CN t ≤ M := fun x hx => hRM (Ctx.mem_CN.mp hx).1
  have hQnorm : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hNR : ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ hc.CN t, g * y * g⁻¹ ∈ hc.CN t := by
    intro g hg y hy
    refine mem_CN_conj_of_normalizes hc (hRM hg) ?_ ?_ hy
    · exact conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hg)
    · exact conjSubgroup_eq_self_iff.mpr (hc.Rt_normalizes_Vt ht hg)
  have hZ0n : ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ Z0, g * y * g⁻¹ ∈ Z0 := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (hZ0.mem_normalizer (fun ρ hρ y hy => hQnorm ρ (hRM hρ) y hy) hg) y).mp hy
  have hZN : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hZR : ∀ z ∈ Z0, ∀ r ∈ Rt M (LB M Q B) t, ⁅z, r⁆ ∈ Q := fun z hz r hr =>
    ((hZ0 z).mp hz).2 r hr
  have hZcard : Nat.card Z0 = Nat.card Q * Nat.card Z := hZc G M Q Z B hc n t hs Z0 hZ0
  have hcN78 := h78 G M Q Z B hc n t hs.toSec5 hs.large hs.notPlus4 3 (le_refl 2 |>.trans (by
      norm_num))
    (Or.inl hp3c)
  unfold Conc78 at hcN78
  have hNcard : Nat.card (hc.CN t) = Nat.card Q * Nat.card Z ^ 9 := by
    rcases hcN78 with ⟨-, -, h9⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩ | ⟨h4, -⟩
    · exact h9
    all_goals omega
  have hq1 : 1 < Nat.card Z := by
    have := hc.hyp.q4
    omega
  have hZnR' : ∀ r ∈ Rt M (LB M Q B) t, ∀ x ∈ sec717CentreN M Q (hc.CN t) hNM hQnorm,
      r * x * r⁻¹ ∈ sec717CentreN M Q (hc.CN t) hNM hQnorm := by
    intro r hr x hx
    obtain ⟨hxN, hxc⟩ := mem_sec717CentreN.mp hx
    refine mem_sec717CentreN.mpr ⟨hNR r hr x hxN, fun s hs' => ?_⟩
    have hs'' : r⁻¹ * s * r ∈ hc.CN t := by
      simpa using hNR r⁻¹ (Subgroup.inv_mem _ hr) s hs'
    have key : ⁅r * x * r⁻¹, s⁆ = r * ⁅x, r⁻¹ * s * r⁆ * r⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact hQnorm r (hRM hr) _ (hxc _ hs'')
  have hZ0Zn : Z0 ≤ sec717CentreN M Q (hc.CN t) hNM hQnorm := fun x hx =>
    mem_sec717CentreN.mpr ⟨hZN hx, fun r hr => ((hZ0 x).mp hx).2 r (Ctx.mem_CN.mp hr).1⟩
  have hZnN : sec717CentreN M Q (hc.CN t) hNM hQnorm ≤ hc.CN t := fun x hx =>
    (mem_sec717CentreN.mp hx).1
  have hInv := sec717Inv_of_parts h51 hA hPts h78 hZc hCN cited
  rcases hInv G M Q Z B hc n t hs hp3 Z0 hZ0 _ hZ0Zn hZnN
    (sec717_conj_eq_of_inv hZnR') with hEq | hEq | hL
  · intro x
    constructor
    · intro hx
      exact ⟨hZN hx, fun r hr => ((hZ0 x).mp hx).2 r (Ctx.mem_CN.mp hr).1⟩
    · rintro ⟨hx, hxc⟩
      have hmem : x ∈ sec717CentreN M Q (hc.CN t) hNM hQnorm := mem_sec717CentreN.mpr ⟨hx, hxc⟩
      rw [hEq] at hmem
      exact hmem
  · exfalso
    apply h711 G M Q Z B hc n t hs
    refine Subgroup.commutator_le.mpr fun x hx y hy => ?_
    have hxZ : x ∈ sec717CentreN M Q (hc.CN t) hNM hQnorm := by
      rw [hEq]
      exact hx
    exact (mem_sec717CentreN.mp hxZ).2 y hy
  · exfalso
    unfold Sec717L at hL
    obtain ⟨hQL, hLN, hLcard, hLR, hLcomm, hZ0L⟩ := hL
    obtain ⟨K, hKf, hKfin, hKZ, φ, hφr, hker, -⟩ := hp3c
    obtain ⟨n0, -, hZn0, -⟩ := hc.hyp.cp
    haveI : CharP K 2 := sec717_charP_two (n := n0) (by rw [hKZ, hZn0])
    have e1 : Nat.card (sec717CentreN M Q (hc.CN t) hNM hQnorm) =
        Nat.card Z0 * Nat.card Z ^ 4 := by
      rw [hLcard, hZcard]
      ring
    have e2 : Nat.card (hc.CN t) = Nat.card Z0 * Nat.card Z ^ 8 := by
      rw [hNcard, hZcard]
      ring
    have hlat : ∀ C : Subgroup G, sec717CentreN M Q (hc.CN t) hNM hQnorm ≤ C → C ≤ hc.CN t →
        (∀ r ∈ Rt M (LB M Q B) t, ∀ c ∈ C, r * c * r⁻¹ ∈ C) →
        C = sec717CentreN M Q (hc.CN t) hNM hQnorm ∨ C = hc.CN t := by
      intro C hZC hCN' hCinv
      have hZC0 : Z0 ≤ C := hZ0Zn.trans hZC
      obtain ⟨k, hk⟩ := sec717CardDvd_of_omegaPlus h51 hA hPts hc hs (le_refl 3) hp3 hZ0 hZC0 hCN'
        (sec717_conj_eq_of_inv hCinv)
      have h4 : (2 : ℕ) ^ (3 - 1) = 4 := by norm_num
      rw [h4] at hk
      have hl := Subgroup.card_le_of_le hZC
      have hu := Subgroup.card_le_of_le hCN'
      rw [hk, e1] at hl
      rw [hk, e2] at hu
      have hk1 : 1 ≤ k := by
        have h2 : Nat.card Z ^ 4 ≤ Nat.card Z ^ (4 * k) :=
          Nat.le_of_mul_le_mul_left hl Nat.card_pos
        have h3 : 4 ≤ 4 * k := (Nat.pow_le_pow_iff_right hq1).mp h2
        omega
      have hk2 : k ≤ 2 := by
        have h2 : Nat.card Z ^ (4 * k) ≤ Nat.card Z ^ 8 :=
          Nat.le_of_mul_le_mul_left hu Nat.card_pos
        have h3 : 4 * k ≤ 8 := (Nat.pow_le_pow_iff_right hq1).mp h2
        omega
      obtain rfl | rfl : k = 1 ∨ k = 2 := by omega
      · left
        have hC1 : Nat.card C = Nat.card (sec717CentreN M Q (hc.CN t) hNM hQnorm) := by
          simp [hk, e1]
        exact (Subgroup.eq_of_le_of_card_ge hZC (le_of_eq hC1)).symm
      · right
        have hC2 : Nat.card C = Nat.card (hc.CN t) := by
          simp [hk, e2]
        exact Subgroup.eq_of_le_of_card_ge hCN' (le_of_eq hC2.symm)
    have hAR_N : hc.CN t ≤ Rt M (LB M Q B) t := fun x hx => (Ctx.mem_CN.mp hx).1
    have hAcomm' : ∀ a ∈ hc.CN t, ∀ a' ∈ hc.CN t, ⁅a, a'⁆ ∈ Z0 := fun a ha a' ha' =>
      hCN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator ha ha')
    have hBQ' : ∀ b ∈ sec717CentreN M Q (hc.CN t) hNM hQnorm, ∀ a ∈ hc.CN t, ⁅b, a⁆ ∈ Q :=
      fun b hb a ha => (mem_sec717CentreN.mp hb).2 a ha
    have hφ' : ∀ h : ↥(Rt M (LB M Q B) t), φ h = 1 → ∀ a ∈ hc.CN t,
        ((h : G) * a * (h : G)⁻¹)⁻¹ * a ∈ sec717CentreN M Q (hc.CN t) hNM hQnorm := by
      intro h hh a ha
      have hmem : (h : G) ∈ hc.CN t := by
        have hh' : h ∈ φ.ker := MonoidHom.mem_ker.mpr hh
        rw [hker] at hh'
        exact Subgroup.mem_subgroupOf.mp hh'
      have hid : ((h : G) * a * (h : G)⁻¹)⁻¹ * a = ⁅(h : G), a⁻¹⁆ := by
        rw [commutatorElement_def]
        group
      show ((h : G) * a * (h : G)⁻¹)⁻¹ * a ∈ sec717CentreN M Q (hc.CN t) hNM hQnorm
      rw [hid]
      exact hZ0Zn (hCN G M Q Z B hc n t hs Z0 hZ0
        (Subgroup.commutator_mem_commutator hmem ((hc.CN t).inv_mem ha)))
    have hQnorm' : ∀ r ∈ Rt M (LB M Q B) t, ∀ q ∈ Q, r * q * r⁻¹ ∈ Q := fun r hr q hq =>
      hQnorm r (hRM hr) q hq
    have hcard' : Nat.card (hc.CN t) =
        Nat.card (sec717CentreN M Q (hc.CN t) hNM hQnorm) * Nat.card K ^ 4 := by
      rw [hKZ, e2, e1]
      ring
    have hcomm := sec717_pairing_trivial cited φ hφr hAR_N hZnN hZ0Zn hNR hZnR' hZ0n hQnorm'
      hZR hAcomm' hBQ' hφ' hlat hcard'
    exact h711 G M Q Z B hc n t hs (Subgroup.commutator_le.mpr fun x hx y hy => hcomm x hx y hy)

end CFSG.RankThree.GF2n.Stroth80
