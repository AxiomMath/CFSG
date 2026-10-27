module

public import CFSG.RankThree.GF2n.Stroth80.HeringSec93FMain
public import CFSG.RankThree.GF2n.Stroth80.CarterSec93Omega

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

theorem step93OmegaCase_of_le_pCore
    (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (h311bComm : Stroth311bCommStatement) (h312b : Stroth312bStatement) :
    ∀ (G : Type) [Group G] [Finite G]
      (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ)
      (t r : G) (Z0 : Subgroup G) (h : G),
      HS9.Cfg93c hc n t r Z0 h →
      ∀ x ∈ LB M Q B ⊓ conjSubgroup h (LB M Q B), x ∉ Q →
      LB M Q B ⊔ conjSubgroup h (LB M Q B) = Rt M (LB M Q B) x →
      LB M Q B ⊓ hc.CN t ≤
        inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)) →
      False := by
  intro G _ _ M Q Z B hc n t r Z0 h cfg x hxK hxQ hR hLN
  obtain ⟨hs, hr, hZ0, hsc, hh, _hne, hK, hZQ⟩ := cfg
  have hs5 := hs.toSec5
  have hNC : Sec9NCommStatement := sec9NComm_of_311b h34 h311bComm
  have h91b : Stroth91bStatement := stroth91b_of_steps h34 h311a hNC (step91OrderQB_of h34)
    (step91OrderVQB_of h34) (step91Inter_of h34) (step91MixedComm_of h34)
  have hc' : Ctx M Q Z (conjSubgroup h B) := hc.conj_of_mem hh
  have hLconj : LB M Q (conjSubgroup h B) = conjSubgroup h (LB M Q B) := hc.LB_conj hh
  have hLH : LB M Q B ≤ H0 M Z := hc.LB_le_H0
  have hL'H : conjSubgroup h (LB M Q B) ≤ H0 M Z := hLconj ▸ hc'.LB_le_H0
  have hFB' : ∀ f ∈ inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)),
      ∀ b ∈ conjSubgroup h B, ⁅f, b⁆ ∈ Z :=
    HS9.comm_mem_Z_of_pCoreIn h34 hc' hs5.width hs5.n_gt (hc.noA2_conj hs5.noA2 hh)
      (hs5.gen.conj_of_mem hh) (hLconj ▸ le_sup_right) (sup_le hLH hL'H)
  have hZ0LB : Z0 ≤ LB M Q B := sec93Omega_Z0_le_LB h34 h311a h311bComm hs hr hZ0
  have hZ0CN : Z0 ≤ hc.CN t := HS9.isCentrePre_le_CN91 hs hZ0
  have htZ : t ∈ Z0 := IsCentrePre.mem_of_mem_LB (hc := hc) hs.mem hZ0
  have htF : t ∈ inSubgroup (pCore 2) (LB M Q B ⊔ conjSubgroup h (LB M Q B)) :=
    hLN (Subgroup.mem_inf.mpr ⟨hZ0LB htZ, hZ0CN htZ⟩)
  have hB'V : conjSubgroup h B ≤ Vt M (LB M Q B) B Z t :=
    HS9.conjB_le_Vt h34 h91b hs hr hc'.le (step93L2_comm_B hc hh hK) htF hFB' hLN
  have hmV : conjSubgroup h B ⊔ Z ≤ Vt M (LB M Q B) B Z t := sup_le hB'V sec39_Z_le_Vt
  obtain ⟨ρ, hρR, hρ⟩ := step93One_of h34 h311a h311bComm h312b G M Q Z B hc n t hs r hr Z0
    hZ0 hsc h hh hmV
  have hρM : ρ ∈ M := hc.Rt_le_M t hρR
  have hLρ : conjSubgroup h (LB M Q B) = conjSubgroup ρ (LB M Q B) :=
    hc.conj_LB_eq_of_conj_BZ hh hρM hρ
  have hρnorm : ∀ ρ' ∈ Rt M (LB M Q B) t, ∀ y ∈ Q, ρ' * y * ρ'⁻¹ ∈ Q := fun ρ' hρ' y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (hc.Rt_le_M t hρ')) y).mp hy
  have hZH : Z0 ≤ LB M Q B ⊓ conjSubgroup h (LB M Q B) := by
    intro z hz
    have hzL' : z ∈ conjSubgroup h (LB M Q B) := by
      rw [hLρ, mem_conjSubgroup]
      have hn1 := hZ0.mem_normalizer hρnorm ((Rt M (LB M Q B) t).inv_mem hρR)
      have hz' : ρ⁻¹ * z * ρ⁻¹⁻¹ ∈ Z0 := (Subgroup.mem_normalizer_iff.mp hn1 z).mp hz
      rw [inv_inv] at hz'
      exact hZ0LB hz'
    exact ⟨hZ0LB hz, hzL'⟩
  exact (sec93Omega_of_centre_le hs hZ0 hZH) hZQ

end CFSG.RankThree.GF2n.Stroth80
