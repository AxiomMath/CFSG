module

public import CFSG.Quasithin.H13.AS91Sec4EightRec
public import CFSG.Quasithin.Vol2.Asc94.TSSetting

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour
open scoped Pointwise

namespace Two

theorem lamOf_513_spec : kapQ 513 = mk7 (lamOf 513) idA := by decide

theorem orbOK48_spec :
    (∀ p ∈ orbWords48, appN (wordRows (g13Gens ()) p.2) q0c ^^^ p.1 ∈ w1List) ∧
      mk7 (lamOf 513) idA ∈ b7List () ∧ mk7 (lamOf 513) idA ≠ t7el ∧ q0c ^^^ 513 = 5 ∧
      gensOKb (ncGens48 ()) = true ∧
      (∀ p ∈ stabWords48.zip stabNcWords48, wordRows (ncGens48 ()) p.2 = wordRows (g13Gens ()) p.1) ∧
      (∀ w ∈ stabNcWords48, ∀ i ∈ w, i < (ncGens48 ()).length) ∧
      (ncOrbit ()).dedup.length = 45 := by
  have h := ok48_parts.2.2.2.2.2.2
  simp only [orbOK48, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.contains_iff_mem,
    bne_iff_ne, ne_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, -⟩, -⟩, -⟩, -⟩, -⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩, h12⟩, h13⟩ := h
  exact ⟨h1, h7, h8, h9, h10, h11, h12, h13⟩

end Two

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section Lift

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem exists_G13_of_mem_g13Grp {U : V12 ≃ₗ[ZMod 2] V12} (hU : U ∈ Two.g13Grp) :
    ∃ m : h.setting.M, (m : G) ∈ D.G13 ∧ D.Φo (h.setting.ρ m) = U := by
  have hU' : U ∈ h.setting.Mbar.map D.Φo := by
    rw [D.map_Mbar_Φo hOut hTw]
    exact Two.g13Grp_le_nGrp hU
  obtain ⟨σ, hσ, rfl⟩ := hU'
  obtain ⟨m, rfl⟩ := MonoidHom.mem_range.mp hσ
  exact ⟨m, mem_pre_of_rho m hU, rfl⟩

end Lift

section Conj

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)
  (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem toMb_QG_eq {q q' : G} (hq : q ∈ h.setting.QG) (hq' : q' ∈ h.setting.QG)
    (hW : D.ψV (h.setting.cl q) + D.ψV (h.setting.cl q') ∈ Two.W1) :
    D.toMb ⟨q, D.QG_le_N hq⟩ = D.toMb ⟨q', D.QG_le_N hq'⟩ := by
  have hE1 : q * q'⁻¹ ∈ D.E1 := by
    refine D.mem_E1.mpr ⟨mul_mem hq (inv_mem hq'), ?_⟩
    rw [h.setting.cl_mul hq (inv_mem hq'), h.setting.cl_inv hq', map_add]
    exact hW
  have h1 : D.toMb ⟨q * q'⁻¹, D.QG_le_N (mul_mem hq (inv_mem hq'))⟩ = 1 :=
    (D.toMb_eq_one_iff hOut hTw hHat _).mpr (D.E1_le_E hE1)
  have e1 : D.toMb ⟨q * q'⁻¹, D.QG_le_N (mul_mem hq (inv_mem hq'))⟩ =
      D.toMb ⟨q, D.QG_le_N hq⟩ * (D.toMb ⟨q', D.QG_le_N hq'⟩)⁻¹ := by
    rw [← map_inv, ← map_mul]
    rfl
  rw [e1] at h1
  exact mul_inv_eq_one.mp h1

theorem conj_tb_eq {m : h.setting.M} (hm : (m : G) ∈ D.G13) {u : ℕ}
    (hu : D.Φo (h.setting.ρ m) (vecOf Two.q0c) + vecOf u ∈ Two.W1) :
    D.toMb ⟨m, D.G13_le_N hm⟩ * D.tb * (D.toMb ⟨m, D.G13_le_N hm⟩)⁻¹ =
      D.toMb ⟨D.rep u, D.QG_le_N (D.rep_mem u)⟩ := by
  have hq := D.q0e_mem_QG
  have hc : (m : G) * D.q0e * (m : G)⁻¹ ∈ h.setting.QG := h.setting.conj_mem_QG m.2 hq
  have e1 : D.toMb ⟨m, D.G13_le_N hm⟩ * D.tb * (D.toMb ⟨m, D.G13_le_N hm⟩)⁻¹ =
      D.toMb ⟨(m : G) * D.q0e * (m : G)⁻¹, D.QG_le_N hc⟩ := by
    rw [tb, ← map_inv, ← map_mul, ← map_mul]
    rfl
  rw [e1]
  refine D.toMb_QG_eq hOut hTw hHat hc (D.rep_mem u) ?_
  rw [← h.setting.ρ_cl m hq, ← Φo_apply_ψV, D.ψV_cl_rep, q0e, D.ψV_cl_rep]
  exact hu

end Conj

section Inv

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem tb_ne_one : D.tb ≠ 1 := fun h1 => by
  have h2 := D.kap_tb
  rw [h1, Subgroup.coe_one, D.kap_one] at h2
  exact absurd h2 (by decide)

theorem orderOf_tb : orderOf D.tb = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact D.Bb_mul_self hOut hTw hHat (D.tb_mem_Bb hOut hTw hHat))
    (D.tb_ne_one hOut hTw hHat)

@[expose] noncomputable def tb' : ↥D.Mb := D.toMb ⟨D.rep 513, D.QG_le_N (D.rep_mem 513)⟩

theorem tb'_mem_Mz : D.tb' ∈ D.Mz := by
  refine D.mem_Mz.mpr (Subtype.ext ?_)
  change D.rep 513 * z * (D.rep 513)⁻¹ = z
  have := h.setting.z_comm_QG (D.rep_mem 513)
  rw [h.setting_z] at this
  rw [this, mul_inv_cancel_right]

theorem tb'_mem_Bb : D.tb' ∈ D.Bb := by
  have hB : Two.mk7 (Two.lamOf 513) Two.idA ∈ Two.b7List () := Two.orbOK48_spec.2.1
  obtain ⟨β, hβ, hβk⟩ := D.exists_of_mem_b7List hOut hTw hHat hB
  have hk : D.kap (D.tb' : MulAut ↥D.E) = Two.mk7 (Two.lamOf 513) Two.idA := by
    rw [tb', D.kap_toMb_QG (D.rep_mem 513), wc, D.ψV_cl_rep, codeOf_vecOf (by norm_num),
      Two.lamOf_513_spec]
  rwa [D.eq_of_kap_eq hOut hTw hHat (D.tb'_mem_Mz hOut hTw hHat)
    (D.Bb_le_C3 hOut hTw hHat hβ).1 (hk.trans hβk.symm)]

theorem tb'_ne_tb : D.tb' ≠ D.tb := by
  have hne : Two.mk7 (Two.lamOf 513) Two.idA ≠ Two.t7el := Two.orbOK48_spec.2.2.1
  intro he
  apply hne
  rw [← Two.lamOf_513_spec, ← wc_rep513, ← D.kap_toMb_QG (D.rep_mem 513), ← D.kap_tb]
  exact congrArg (fun φ : ↥D.Mb => D.kap (φ : MulAut ↥D.E)) he
where
  wc_rep513 : D.wc (D.rep 513) = 513 := by rw [wc, D.ψV_cl_rep, codeOf_vecOf (by norm_num)]

end Inv

section Words

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem exists_conj_tb {w : List ℕ} (hw : ∀ i ∈ w, i < 2) {u : ℕ} (hu4 : u < 4096)
    (hu : appN (wordRows (Two.g13Gens ()) w) Two.q0c ^^^ u ∈ Two.w1List) :
    ∃ g ∈ D.Mz, g * D.tb * g⁻¹ = D.toMb ⟨D.rep u, D.QG_le_N (D.rep_mem u)⟩ := by
  have hlen : (Two.g13Gens ()).length = 2 := by simp [Two.g13Gens, Two.g13Words]
  obtain ⟨hok, U, hU, hUx⟩ := rep_word Two.gensOK_g13 w fun i hi => hlen ▸ hw i hi
  obtain ⟨m, hm, hmU⟩ := D.exists_G13_of_mem_g13Grp hOut hTw (Two.g13Gens_le_g13Grp hU)
  refine ⟨D.toMb ⟨m, D.G13_le_N hm⟩, (D.mem_Mz_iff hOut hTw).mpr ⟨m, hm, rfl⟩, ?_⟩
  refine D.conj_tb_eq hOut hTw hHat hm ?_
  rw [hmU, hUx, ← vecOf_appN, ← vecOf_xor]
  exact (Two.vecOf_mem_W1 (Nat.xor_lt_two_pow (n := 12)
    (appN_lt (okRows_spec hok).2 _) hu4)).mpr hu

theorem exists_conj_tb' : ∃ g ∈ D.Mz, g * D.tb * g⁻¹ = D.tb' := by
  have h1 := Two.orbOK48_spec.1 (513, [0, 0, 0, 0, 0, 1, 0]) (by decide)
  exact D.exists_conj_tb hOut hTw hHat (by decide) (by norm_num) h1

theorem exists_conj_tb5 :
    ∃ g ∈ D.Mz, g * D.tb * g⁻¹ = D.toMb ⟨D.rep 5, D.QG_le_N (D.rep_mem 5)⟩ := by
  have h1 := Two.orbOK48_spec.1 (5, [0, 0, 1, 1, 0, 1]) (by decide)
  exact D.exists_conj_tb hOut hTw hHat (by decide) (by norm_num) h1

end Words

section Setting

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve) (hHat : HatM22SmallModules)

include hOut hTw hHat

theorem Bb_le_pCore : D.Bb ≤ CFSG.Open.pCoreOf 2 (CFSG.Quasithin.A94.Cz D.tb) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine CFSG.LieType.BorelTits.le_pCoreOf (r := 2) D.Bb_le_Cb (D.BC_normal hOut hTw hHat) ?_
  exact IsPGroup.of_card (n := 4) (by rw [D.card_Bb hOut hTw hHat]; norm_num)

theorem setting (e : ↥(CFSG.Quasithin.A94.Cz D.tb) ≃* CFSG.Quasithin.A94.L52.Hc) :
    CFSG.Quasithin.A94.Setting ↥D.Mb D.tb e := by
  refine ⟨D.orderOf_tb hOut hTw hHat, ?_⟩
  obtain ⟨g, -, hg⟩ := D.exists_conj_tb' hOut hTw hHat
  refine ⟨g⁻¹, ?_, ?_⟩
  · rw [inv_inv, hg]
    exact D.Bb_le_pCore hOut hTw hHat (D.tb'_mem_Bb hOut hTw hHat)
  · rw [inv_inv, hg]
    exact D.tb'_ne_tb hOut hTw hHat

end Setting

end Data41

end CFSG.Quasithin.H13.AS91
