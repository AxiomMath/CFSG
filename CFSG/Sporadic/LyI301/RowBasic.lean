module

public import CFSG.Sporadic.LyI301.RowR
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Layer
public import CFSG.HardMathSupport.Dickson.I271.SporGenR3Aux.Primitive
public import CFSG.Sporadic.Presentation.McLExact
public import CFSG.LocalAnalysis.GLTheoremA.CatB.H301Defs
public import CFSG.Sporadic.Recognition.LyonsLocalTorus

public noncomputable section

namespace CFSG.Sporadic.LyI301

open Equiv Equiv.Perm Subgroup CFSG.Sporadic.Recognition.LyonsSims CFSG.Certificates
  CFSG.Open CFSG.Yardstones.Md0ec50421ce4 CFSG.LocalAnalysis.GLTheoremA
  CFSG.LocalAnalysis.GLTheoremA.S8 CFSG.LocalAnalysis.GLTheoremA.H301
  CFSG.HardMathSupport.Dickson.I271

variable {G : Type} [Group G] [Finite G] {t : G} {ρ : ↥(centralizer ({t} : Set G)) →* Perm (Fin 11)}
  {x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))}

@[expose] def lyB1 (x₁ x₂ x₃ : ↥(centralizer ({t} : Set G))) : Subgroup G :=
  Subgroup.closure {(x₁ : G), (x₂ : G), (x₃ : G)}

theorem ly_hR (D : LyData G t ρ) : IsExtraSpec2 (lyR ρ) ∧ Nat.card (lyR ρ) = 2 ^ Row.ly.rexp := by
  obtain ⟨h2, hc, hf, hz⟩ := lyR_extraspecial D
  refine ⟨⟨h2, hc.trans hf.symm, hf, hz⟩, ?_⟩
  rw [card_lyR D]
  rfl

private theorem xp_indep : ∀ i j k : Fin 3,
    x1p ^ i.val * x2p ^ j.val * x3p ^ k.val = 1 → i = 0 ∧ j = 0 ∧ k = 0 := by
  decide +kernel

theorem ly_hB (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    IsElemAbelian Row.ly.prime (lyB1 x₁ x₂ x₃) ∧
      Nat.card (lyB1 x₁ x₂ x₃) = Row.ly.prime ^ (Row.ly.rank - 1) := by
  have h12 : Commute (x₁ : G) (x₂ : G) := (D.comm₂₁ S).symm
  have h13 : Commute (x₁ : G) (x₃ : G) := (D.comm₃₁ S).symm
  have h23 : Commute (x₂ : G) (x₃ : G) := (D.comm₃₂ S).symm
  have hp : ∀ x : ↥(centralizer ({t} : Set G)), x ^ 3 = 1 → (x : G) ^ 3 = 1 := fun x hx => by
    rw [← Subgroup.coe_pow, hx, Subgroup.coe_one]
  have hind : ∀ i j k : ℕ, i < 3 → j < 3 → k < 3 →
      (x₁ : G) ^ i * (x₂ : G) ^ j * (x₃ : G) ^ k = 1 → i = 0 ∧ j = 0 ∧ k = 0 := by
    intro i j k hi hj hk h
    have hE : x₁ ^ i * x₂ ^ j * x₃ ^ k = 1 := Subtype.ext (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_pow, Subgroup.coe_pow,
        Subgroup.coe_pow, Subgroup.coe_one]
      exact h)
    have hρ := congrArg ρ hE
    rw [map_mul, map_mul, map_pow, map_pow, map_pow, S.rho₁, S.rho₂, S.rho₃, map_one] at hρ
    have := xp_indep ⟨i, hi⟩ ⟨j, hj⟩ ⟨k, hk⟩ hρ
    simp only [Fin.ext_iff, Fin.val_zero] at this
    exact this
  exact isElemAbelian_closure_three h12 h13 h23 (hp _ S.pow₁) (hp _ S.pow₂) (hp _ S.pow₃) hind

private theorem x1p_comm_lyU : ∀ i, lyU i * x1p = x1p * lyU i := by decide +kernel

private theorem x2p_conj_lyU : (∀ i, ∃ v, ExtraspecialNF.mon lyU v = x2p * lyU i * x2p⁻¹) ∧
    ∀ i, ∃ v, ExtraspecialNF.mon lyU v = x2p⁻¹ * lyU i * x2p⁻¹⁻¹ := by decide +kernel

private theorem x3p_conj_lyU : (∀ i, ∃ v, ExtraspecialNF.mon lyU v = x3p * lyU i * x3p⁻¹) ∧
    ∀ i, ∃ v, ExtraspecialNF.mon lyU v = x3p⁻¹ * lyU i * x3p⁻¹⁻¹ := by decide +kernel

theorem lyR_le_centralizer_x₁ (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    lyR ρ ≤ centralizer ({(x₁ : G)} : Set G) :=
  le_centralizer_lyR D S.pow₁ fun π hπ => by
    rw [S.rho₁]
    exact comm_lyVS x1p_comm_lyU hπ

theorem ly_hBN (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    lyB1 x₁ x₂ x₃ ≤ Subgroup.normalizer (lyR ρ : Set G) := by
  refine (Subgroup.closure_le _).2 ?_
  rintro g (rfl | rfl | rfl)
  · refine mem_normalizer_lyR (fun π hπ => ?_) (fun π hπ => ?_) <;> rw [S.rho₁]
    · rw [← comm_lyVS x1p_comm_lyU hπ, mul_inv_cancel_right]
      exact hπ
    · rw [mul_assoc, comm_lyVS x1p_comm_lyU hπ, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hπ
  · refine mem_normalizer_lyR (fun π hπ => ?_) (fun π hπ => ?_) <;> rw [S.rho₂]
    · exact conj_mem_lyVS (fun i => x2p_conj_lyU.1 i) hπ
    · have h := conj_mem_lyVS (π := x2p⁻¹) (fun i => x2p_conj_lyU.2 i) hπ
      rwa [inv_inv] at h
  · refine mem_normalizer_lyR (fun π hπ => ?_) (fun π hπ => ?_) <;> rw [S.rho₃]
    · exact conj_mem_lyVS (fun i => x3p_conj_lyU.1 i) hπ
    · have h := conj_mem_lyVS (π := x3p⁻¹) (fun i => x3p_conj_lyU.2 i) hπ
      rwa [inv_inv] at h

theorem ly_hd (S : LyStd ρ x₁ x₂ x₃) : (x₁ : G) ∈ lyB1 x₁ x₂ x₃ ∧ (x₁ : G) ≠ 1 := by
  refine ⟨Subgroup.subset_closure (Set.mem_insert _ _), fun h => ?_⟩
  have h3 := LyData.orderOf_x₁ S
  rw [h, orderOf_one] at h3
  exact absurd h3 (by norm_num)

theorem ly_R0 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : rowR0Of (x₁ : G) (lyR ρ) = lyR ρ :=
  inf_eq_left.2 (lyR_le_centralizer_x₁ D S)

theorem ly_hR0 (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nat.card (rowR0Of (x₁ : G) (lyR ρ)) = 2 ^ Row.ly.r0exp := by
  rw [ly_R0 D S, card_lyR D]
  rfl

theorem ly_hR0t (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) : IsExtraSpec2 (rowR0Of (x₁ : G) (lyR ρ)) := by
  rw [ly_R0 D S]
  exact (ly_hR D).1

section McL


private theorem nonempty_quot_center_mcl (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    Nonempty ((↥(centralizer ({(x₁ : G)} : Set G)) ⧸
      Subgroup.center ↥(centralizer ({(x₁ : G)} : Set G))) ≃* Blueprint.NativeSporadic.McL) := by
  obtain ⟨e⟩ := D.centQuot_mcl S.pow₁ S.rho₁
  exact ⟨(QuotientGroup.quotientMulEquivOfEq (D.center_centralizer S)).trans e⟩

private theorem isQuasisimple_centralizer (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    CFSG.Open.IsQuasisimple ↥(centralizer ({(x₁ : G)} : Set G)) := by
  refine ⟨(D.isPerfect_centralizer S).commutator_eq_top, ?_⟩
  obtain ⟨hsimple, -, -⟩ := D.centQuot_facts S.pow₁ S.rho₁
  haveI := hsimple
  exact MulEquiv.isSimpleGroup (QuotientGroup.quotientMulEquivOfEq (D.center_centralizer S))

private theorem centralizer_layer (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    GLAPPrimeCore 3 ↥(centralizer ({(x₁ : G)} : Set G)) = ⊥ ∧
      GLAPLayer 3 (centralizer ({(x₁ : G)} : Set G)) = centralizer ({(x₁ : G)} : Set G) := by
  set C := centralizer ({(x₁ : G)} : Set G)
  have hq := isQuasisimple_centralizer D S
  have hCn : ∀ g ∈ C, ∀ l ∈ C, g * l * g⁻¹ ∈ C := fun g hg l hl =>
    C.mul_mem (C.mul_mem hg hl) (C.inv_mem hg)
  have hp3 : 3 ∣ Nat.card ↥C := by
    have h := orderOf_dvd_natCard (⟨(x₁ : G), self_mem_centralizer_singleton _⟩ : ↥C)
    rwa [Subgroup.orderOf_mk, LyData.orderOf_x₁ S] at h
  have hcent : IsPGroup 3 ↥(C ⊓ Subgroup.centralizer (C : Set G)) := by
    intro c
    refine ⟨1, ?_⟩
    have hc := Subgroup.mem_inf.1 c.2
    have hcZ : (⟨(c : G), hc.1⟩ : ↥C) ∈ Subgroup.center ↥C :=
      Subgroup.mem_center_iff.2 fun g => Subtype.ext (Subgroup.mem_centralizer_iff.1 hc.2 g g.2)
    have h3 : (⟨⟨(c : G), hc.1⟩, hcZ⟩ : ↥(Subgroup.center ↥C)) ^ 3 = 1 := by
      rw [← D.card_center_centralizer S]
      exact pow_card_eq_one'
    have h4 := congrArg (fun y : ↥(Subgroup.center ↥C) => ((y : ↥C) : G)) h3
    rw [pow_one]
    apply Subtype.ext
    simpa using h4
  have hcore :=
    glaPPrimeCore_eq_bot_of_normal_quasisimple Nat.prime_three le_rfl hCn hq hp3 hcent
  exact ⟨hcore, glaPLayer_eq_of_unique_glaPComponent
    (glaPComponent_of_normal_quasisimple le_rfl hCn hq hcore) fun J hJ =>
      eq_of_glaPComponent_of_normal_quasisimple Nat.prime_three le_rfl hCn hq hcore hcent hJ⟩

theorem ly_I (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    rowIOf Row.ly.prime (x₁ : G) = centralizer ({(x₁ : G)} : Set G) :=
  (centralizer_layer D S).2

theorem ly_hI (D : LyData G t ρ) (S : LyStd ρ x₁ x₂ x₃) :
    RowI .ly Row.ly.prime (rowIOf Row.ly.prime (x₁ : G)) := by
  rw [ly_I D S]
  show IsTypeWithCenter 3 (centralizer ({(x₁ : G)} : Set G)) (sporIs .McL) 3
  obtain ⟨eM⟩ := nonempty_quot_center_mcl D S
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.McL.nonempty_mulEquiv
  let e : PQuot 3 (centralizer ({(x₁ : G)} : Set G)) ≃*
      ↥(centralizer ({(x₁ : G)} : Set G)) :=
    (QuotientGroup.quotientMulEquivOfEq (centralizer_layer D S).1).trans QuotientGroup.quotientBot
  refine ⟨⟨.sporadic .McL, rfl,
    ⟨((QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)).trans eM).trans b⟩⟩, ?_⟩
  rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv, D.card_center_centralizer S]

end McL

end CFSG.Sporadic.LyI301
