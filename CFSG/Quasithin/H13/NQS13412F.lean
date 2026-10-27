module

public import CFSG.Quasithin.H13.NQS13412E

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem exists_rep_of_odd (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) {y : G} (hyW : y ∈ normalizer (W : Set G))
    (hyK : y ∈ normalizer (K : Set G))
    (hyL : ∀ k ∈ K, k ∈ L₁Of L (fsuV1 T V) ⊔ T → y * k * y⁻¹ ∈ L₁Of L (fsuV1 T V) ⊔ T)
    (hy : ∃ m : ℕ, Odd m ∧ y ^ m = 1) :
    ∃ k ∈ K, k ∈ L₁Of L (fsuV1 T V) ⊔ T ∧ y * k⁻¹ ∈ centralizer (W : Set G) := by
  have hM : normalizer (L : Set G) = L ⊔ T := D.M4.resolve_right hnhat
  obtain ⟨-, hZW, hL1, -, htype⟩ := (D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he).2
  obtain ⟨-, -, -, -, -, -, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S D.exists_inH
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  rcases htype with ⟨hK3, hnat⟩ | ⟨hK6, h6 | hc⟩
  · obtain ⟨C₀⟩ := exists_l3Coords hnat
    obtain ⟨C, hCB⟩ := C₀.exists_conj_eq D.Wirr.2.2.1 (S.h13.sylow.1.to_le inf_le_left)
    have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inl hK3))
    have hCKT : K ⊓ centralizer (W : Set G) ≤ T :=
      (inf_le_inf_right (centralizer (W : Set G)) (le_sup_left : K ≤ K ⊔ T)).trans
        (D.inf_centralizer_le_T hZK)
    obtain ⟨DP, -⟩ := l32_parData C hCB D.Wirr.2.2.1 D.T_le_K D.isSylowTwoOf_inf hCKT
      (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
      D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW) D.Wirr.2.1 S.h13.sylow.1
      D.TW D.W_le_T
    exact DP.exists_of_odd le_top (fun g hg => (C.ker g).1 hg) (p := l3p) l3p_mem
      (fun γ hγ _ => l3_selfnorm γ hγ) hyW hyK hyL hy
  · obtain ⟨R⟩ := exists_rawData4 D.Wirr.2.2.1 h6.1
    obtain ⟨F⟩ := exists_frame4 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW
      D.isSylowTwoOf_inf
    have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
    obtain ⟨DP, -⟩ := frame4_parData F D.T_le_K (D.inf_centralizer_le_T hZK)
      (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
      D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
    exact DP.exists_of_odd stab45_le_alt (frame4_ker F) (p := a6p) a6p_mem
      (fun γ hγ ⟨m, hm, hγm⟩ => a6_selfnorm γ hγ (U3.pow_45_of_odd' hm hγm)) hyW hyK hyL hy
  · obtain ⟨R⟩ := exists_rawData6 D.Wirr.2.2.1 hc.2.2
    obtain ⟨F⟩ := exists_frame5 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW
      D.isSylowTwoOf_inf
    have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
    obtain ⟨DP, -⟩ := frame5_parData F D.T_le_K (D.inf_centralizer_le_T hZK)
      (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
      D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
    exact DP.exists_of_odd stab45_le_alt (frame5_ker F) (p := a6p) a6p_mem
      (fun γ hγ ⟨m, hm, hγm⟩ => a6_selfnorm γ hγ (U3.pow_45_of_odd' hm hγm)) hyW hyK hyL hy

theorem le_normalizer_of_inH (h1332 : Stmt13_3_2) {X : Subgroup G} (hX : InH T X)
    (hKX : K ≤ X) : X ≤ normalizer (K : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨-, -, -, huniq⟩, -, -⟩ := h1332 G T L S.h13 K D.Kf
  obtain ⟨M', hM', hM'le⟩ := exists_maxTwoLocal_ge
    (⟨pCoreOf 2 X, hX.2, LieType.BorelTits.pCoreOf_isPGroup 2 _, rfl⟩ :
      IsTwoLocal (normalizer (pCoreOf 2 X : Set G)))
  have hXM' : X ≤ M' := (LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans hM'le
  rw [← huniq M' hM' ((sup_le hKX hX.1).trans hXM')]
  exact hXM'

theorem false_of_le (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) (hZVW : V ⊓ centralizer (L : Set G) ≤ W) {X : Subgroup G}
    (hX : InH T X) (hKX : K ≤ X) {zb : G} (hzb : zb ∈ fsuV1 T V)
    (hzbL : zb ∉ centralizer (L : Set G)) (hzbz : zb ≠ z) {Y : Subgroup G} (hTY : T ≤ Y)
    (hYX : Y ≤ X) (hYzb : Y ≤ centralizer ({zb} : Set G))
    (hYM : ¬ Y ≤ normalizer (L : Set G)) : False := by
  have hM : normalizer (L : Set G) = L ⊔ T := D.M4.resolve_right hnhat
  obtain ⟨-, -, -, -, -, hZ4, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  have hV1 : Nat.card ↥(fsuV1 T V) = 4 := hZV1 ▸ hZ4
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S D.exists_inH
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  set L₁T := L₁Of L (fsuV1 T V) ⊔ T with hL₁T
  have hL1TZ : L₁T ≤ centralizer (quasithinOmegaOneCenter T : Set G) := sup_le hL1Z hTZ
  have hL1TM : L₁T ≤ normalizer (L : Set G) :=
    sup_le (((oTwoRes_le _).trans inf_le_left).trans le_normalizer) S.T_le_NL
  have hvz : S.zV = z * zb := D.zV_eq_mul hV1 hzb hzbL hzbz
  have hgood : ∀ g : G, g * S.zV = S.zV * g → g * zb = zb * g → g ∈ L₁T := by
    intro g hgv hgzb
    have hgZV : g ∈ centralizer ((V ⊓ centralizer (L : Set G) : Subgroup G) : Set G) := by
      rw [mem_centralizer_iff]
      intro x hx
      rcases S.mem_ZV_iff.1 hx with rfl | rfl
      · rw [one_mul, mul_one]
      · exact hgv.symm
    have h1 := mem_centralizer_V1 S hzb hzbL hgZV hgzb
    rw [← hZV1] at h1
    exact centralizer_Z_le_L1T S hM hZV1 h1
  have hzbL1T : ∀ g ∈ L₁T, g * zb = zb * g := fun g hg =>
    (mem_centralizer_iff.1 (hL1TZ hg) zb hzb.2).symm
  have hYK : Y ≤ normalizer (K : Set G) := hYX.trans (D.le_normalizer_of_inH h1332 hX hKX)
  have hYW : Y ≤ normalizer (W : Set G) := D.le_normalizer_W hV1 hZVW hzb hzbL hzbz hYK hYzb
  have hodd : ∀ y ∈ Y, (∃ m : ℕ, Odd m ∧ y ^ m = 1) → y ∈ L₁T := by
    intro y hy hym
    have hyzb : y * zb = zb * y := mem_centralizer_singleton_iff.1 (hYzb hy)
    have hyL : ∀ k ∈ K, k ∈ L₁T → y * k * y⁻¹ ∈ L₁T := by
      intro k hk hkL
      have hk' : y * k * y⁻¹ ∈ K := (mem_normalizer_iff.mp (hYK hy) k).mp hk
      have hkz : y * k * y⁻¹ * z = z * (y * k * y⁻¹) :=
        mem_centralizer_singleton_iff.1 (D.Kz hk')
      have hkzb : y * k * y⁻¹ * zb = zb * (y * k * y⁻¹) := by
        have h1 := hzbL1T k hkL
        calc y * k * y⁻¹ * zb = y * k * (y⁻¹ * zb) := by group
          _ = y * k * (zb * y⁻¹) := by
              rw [show y⁻¹ * zb = zb * y⁻¹ by
                rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, hyzb, mul_inv_cancel_right]]
          _ = y * (k * zb) * y⁻¹ := by group
          _ = y * (zb * k) * y⁻¹ := by rw [h1]
          _ = (y * zb) * k * y⁻¹ := by group
          _ = zb * (y * k * y⁻¹) := by rw [hyzb]; group
      refine hgood _ ?_ hkzb
      rw [hvz]
      calc y * k * y⁻¹ * (z * zb) = (y * k * y⁻¹ * z) * zb := by group
        _ = z * (y * k * y⁻¹ * zb) := by rw [hkz]; group
        _ = z * zb * (y * k * y⁻¹) := by rw [hkzb]; group
    obtain ⟨k, hkK, hkL, hc⟩ := D.exists_rep_of_odd hC137 h1332 h1228 hC58 h317 h56 he hnhat
      (hYW hy) (hYK hy) hyL hym
    have hcv : y * k⁻¹ * S.zV = S.zV * (y * k⁻¹) :=
      (mem_centralizer_iff.1 hc S.zV (hZVW (S.mem_ZV_iff.2 (Or.inr rfl)))).symm
    have hczb : y * k⁻¹ * zb = zb * (y * k⁻¹) := by
      have h1 := hzbL1T k hkL
      have h2 : k⁻¹ * zb = zb * k⁻¹ := by
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, h1, mul_inv_cancel_right]
      calc y * k⁻¹ * zb = y * (k⁻¹ * zb) := by group
        _ = y * (zb * k⁻¹) := by rw [h2]
        _ = (y * zb) * k⁻¹ := by group
        _ = zb * (y * k⁻¹) := by rw [hyzb]; group
    have hcL := hgood _ hcv hczb
    have e : y = y * k⁻¹ * k := by group
    rw [e]
    exact mul_mem hcL hkL
  have hO : oTwoRes Y ≤ L₁T := by
    rw [oTwoRes, closure_le]
    rintro y ⟨hy, hym⟩
    exact hodd y hy hym
  apply hYM
  exact (le_oTwoRes_sup_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow hTY)).trans
    ((sup_le hO le_sup_right).trans hL1TM)

end Data13410

end CFSG.Quasithin.H13.NQS134
