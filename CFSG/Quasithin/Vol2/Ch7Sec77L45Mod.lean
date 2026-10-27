module

public import CFSG.Quasithin.Vol2.Ch7Sec77L45
public import CFSG.Quasithin.Background.HSL4Q13Mod
public import CFSG.Quasithin.EmptyFaithful.T1515dB
public import CFSG.Quasithin.Background.B5NonB
public import CFSG.Quasithin.Background.FFC4Ext

public section

namespace CFSG.Quasithin.H13.LPar

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H.Q13

namespace Cfg

variable {X Y : Subgroup (SpecialLinearGroup (Fin 4) (ZMod 2))}
  {y : SpecialLinearGroup (Fin 4) (ZMod 2)} (C : Cfg 4 {1, 3} X Y y)
include C

theorem scSL_mem (k : Fin 4) : scSL k ∈ Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h1 : (1 : ℕ) = 0 ∨ (1 : ℕ) = 4 ∨ (1 : ℕ) ∈ ({1, 3} : Set ℕ) := Or.inr (Or.inr (by simp))
  have h3 : (1 + 2 : ℕ) = 0 ∨ (1 + 2 : ℕ) = 4 ∨ (1 + 2 : ℕ) ∈ ({1, 3} : Set ℕ) :=
    Or.inr (Or.inr (by simp))
  have hcut : ∀ i ∈ ({1, 3} : Set ℕ), i ≤ 1 ∨ 1 + 2 ≤ i := by
    intro i hi
    rcases hi with rfl | hi
    · left; rfl
    · rw [Set.mem_singleton_iff] at hi
      subst hi
      right; rfl
  set β := blk {1, 3} 1 2 (by norm_num) h1 h3 with hβ
  have hβy3 : β ⟨y, C.yQ⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨y, C.yQ⟩ : ↥(flagStabilizer 4 (ZMod 2) {1, 3})) ^ 3 = 1 :=
      Subtype.ext (by simpa using C.y_pow_three)
    rw [this, map_one]
  have hβy1 : β ⟨y, C.yQ⟩ ≠ 1 := by
    intro hy1
    apply C.not_le_upperTriangular (by norm_num)
    intro x hx
    obtain ⟨j, hj⟩ := C.blk_X (by norm_num) h1 h3 hcut (Or.inl rfl) hx
    rw [← hβ, hy1, _root_.one_zpow] at hj
    have hb : blkAt 1 2 (by norm_num) ((x : SpecialLinearGroup (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) = 1 := by
      have e := congrArg (fun A : SpecialLinearGroup (Fin 2) (ZMod 2) =>
        (A : Matrix (Fin 2) (Fin 2) (ZMod 2))) hj
      simp only [Matrix.SpecialLinearGroup.coe_one] at e
      exact e
    have hxQ := C.hXQ hx
    have hx1 : x ∈ stabilizer (flagSpace 4 (ZMod 2) 1) := mem_flagStabilizer.1 hxQ 1 (by simp)
    have hx3 : x ∈ stabilizer (flagSpace 4 (ZMod 2) (1 + 2)) :=
      mem_flagStabilizer.1 hxQ 3 (by simp)
    have hx2 : x ∈ stabilizer (flagSpace 4 (ZMod 2) 2) :=
      mem_stabilizer_of_blkAt_eq_one (a := 1) (m := 2) (i := 2) (by norm_num) hx1 hx3 hb
        (by norm_num) (by norm_num)
    rw [BinaryParabolic.upperTriangular_eq_unitriangular, ← BinaryParabolic.flagStabilizer_Icc]
    refine mem_flagStabilizer.2 fun i hi => ?_
    simp only [Set.mem_Icc] at hi
    rcases (by omega : i = 1 ∨ i = 2 ∨ i = 3) with rfl | rfl | rfl
    · exact hx1
    · exact hx2
    · exact hx3
  have hβm := sl2_cube _ hβy3 hβy1
  set m : Matrix (Fin 2) (Fin 2) (ZMod 2) :=
    ((β ⟨y, C.yQ⟩ : SpecialLinearGroup (Fin 2) (ZMod 2)) : Matrix (Fin 2) (Fin 2) (ZMod 2))
    with hmdef
  have hmm : m ∈ ({om, om * om} : Finset (Matrix (Fin 2) (Fin 2) (ZMod 2))) := by
    rcases hβm with h | h
    · rw [h]; simp
    · rw [h]; simp
  have hy : (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) =
      q13 ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1) ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2)
        ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 3) ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3)
        ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3) m := eq_q13 C.yQ
  have hy3 : (y : Matrix (Fin 4) (Fin 4) (ZMod 2)) * y * y = 1 := by
    have := congrArg (fun A : SpecialLinearGroup (Fin 4) (ZMod 2) =>
      (A : Matrix (Fin 4) (Fin 4) (ZMod 2))) C.y_pow_three
    simpa [pow_succ, mul_assoc] using this
  rw [hy] at hy3
  have hcj := conj_q13 m hmm _ _ _ _ _ hy3
  rw [← hy] at hcj
  set c : SpecialLinearGroup (Fin 4) (ZMod 2) :=
    ⟨cj ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 1) ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 0 2)
      ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 1 3) ((y : Matrix (Fin 4) (Fin 4) (ZMod 2)) 2 3) m,
      det_cj m hmm _ _ _ _⟩ with hcdef
  have hcQ : c ∈ flagStabilizer 4 (ZMod 2) {1, 3} := q13_mem (g := c) rfl
  set t : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨q13 0 0 0 0 0 m, det_q13_om m hmm⟩ with htdef
  have hct : c * y = t * c := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
    exact hcj)
  have hconj : ∀ g ∈ flagStabilizer 4 (ZMod 2) {1, 3}, ∀ x ∈ X, g * x * g⁻¹ ∈ X :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.1 (C.hQX hg) x).1 hx
  have htX : t ∈ X := by
    have e : t = c * y * c⁻¹ := by rw [hct]; group
    rw [e]
    exact hconj c hcQ y C.hy
  set y0s : SpecialLinearGroup (Fin 4) (ZMod 2) :=
    ⟨y0, by rw [y0]; exact det_q13_om om (by simp)⟩ with hy0s
  have hy0X : y0s ∈ X := by
    rcases hβm with h | h
    · have hq : q13 0 0 0 0 0 m = y0 := by rw [h]; rfl
      have e : t = y0s := Subtype.ext hq
      rw [← e]
      exact htX
    · have hq : q13 0 0 0 0 0 m = y0 * y0 := by rw [h, q13_om_sq]
      have e : t = y0s * y0s := Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul]
        exact hq)
      have e3 : y0s * y0s * y0s = 1 := Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
          Matrix.SpecialLinearGroup.coe_one]
        exact y0_cube)
      have e4 : y0s = t * t := by
        rw [e]
        calc y0s = (y0s * y0s * y0s) * y0s := by rw [e3, one_mul]
          _ = y0s * y0s * (y0s * y0s) := by group
      rw [e4]
      exact X.mul_mem htX htX
  set tk : SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨tv k, by
    fin_cases k
    · exact det_q13_one 1 0 0 0 0
    · exact det_q13_one 0 1 0 0 0
    · exact det_q13_one 0 0 0 1 0
    · exact det_q13_one 0 0 0 0 1⟩ with htkdef
  have htkQ : tk ∈ flagStabilizer 4 (ZMod 2) {1, 3} := by
    fin_cases k
    · exact q13_mem (g := tk) rfl
    · exact q13_mem (g := tk) rfl
    · exact q13_mem (g := tk) rfl
    · exact q13_mem (g := tk) rfl
  have htk2 : tk * tk = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one]
    exact tv_sq k)
  have hy03 : y0s * y0s * y0s = 1 := Subtype.ext (by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_one]
    exact y0_cube)
  have hsc : scSL k = tk * y0s * tk⁻¹ * y0s⁻¹ := by
    rw [inv_eq_of_mul_eq_one_right htk2,
      inv_eq_of_mul_eq_one_right (show y0s * (y0s * y0s) = 1 by rw [← mul_assoc]; exact hy03)]
    exact Subtype.ext rfl
  have hscX : scSL k ∈ X := by
    rw [hsc]
    exact X.mul_mem (hconj tk htkQ y0s hy0X) (X.inv_mem hy0X)
  obtain ⟨u, hu, j, hj⟩ := C.exists_mul_zpow hscX
  have hβsc : β ⟨scSL k, C.hXQ hscX⟩ = 1 := Subtype.ext (blk_sc k)
  have hβuj : β ⟨scSL k, C.hXQ hscX⟩ = β ⟨y, C.yQ⟩ ^ j := by
    have e : (⟨scSL k, C.hXQ hscX⟩ : ↥(flagStabilizer 4 (ZMod 2) {1, 3})) =
        ⟨u, C.YQ hu⟩ * ⟨y, C.yQ⟩ ^ j := Subtype.ext (by simpa using hj)
    rw [e, map_mul, map_zpow, C.blk_Y (by norm_num) h1 h3 hcut (Or.inl rfl) hu, one_mul]
  rw [hβsc] at hβuj
  have ho : orderOf (β ⟨y, C.yQ⟩) = 3 := orderOf_eq_prime hβy3 hβy1
  have hj3 : ((3 : ℕ) : ℤ) ∣ j := by
    rw [← ho]
    exact orderOf_dvd_iff_zpow_eq_one.2 hβuj.symm
  have hyj : y ^ j = 1 := by
    rw [← C.hy3] at hj3
    exact orderOf_dvd_iff_zpow_eq_one.1 hj3
  rw [hj, hyj, mul_one]
  exact hu

end Cfg

end CFSG.Quasithin.H13.LPar

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank CFSG.Quasithin.H.Q13
open scoped commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem tv_noncomm : tv 0 * tv 2 ≠ tv 2 * tv 0 := by decide +kernel

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem false_of_excL45
    (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hC24b : ASC24TwoChar G)
    (hA318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h51 : AsB51) (hI16 : AsI16Cover)
    (hA8 : AsI16CoverA8) (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L)
    (hexc : ExcL45 T L I θ Vp H K) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := C.conf.hc
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTpdef
  set L₀ := oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) with hL₀def
  set L₀V := L₀ ⊓ Subgroup.centralizer (fsuV T I : Set G) with hL₀Vdef
  set V' := omegaOneCenterOf (pCoreOf 2 (K ⊔ Q)) with hV'def
  set Ks := autOn K V' with hKsdef
  obtain ⟨θc, hθcM, ⟨y, hθN, hcfg, hθy⟩, hH⟩ := hexc
  have eK : ↥Ks ≃* ↥(CFSG.Assembly.LowTwoRank.StatedSL 4 (ZMod 2)) :=
    θc.trans (specialLinearGroupEquivStatedSL 4 (ZMod 2))
  obtain ⟨hCK, ⟨eX⟩⟩ := C.inf_centralizer_le_and_equiv hC27 h443 hC24a hC24b hF hK hKq hKM
    (Or.inr (Or.inl rfl)) eK
  have hKeq := C.eq_oPrimeResidualOf_of_sl hA318 h36 h38 hK hKq (Or.inl rfl) eX
  have hHK : H ≤ Subgroup.normalizer (K : Set G) := hKeq ▸ le_normalizer_oPrimeResidualOf_three H
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hTpH : Tp ≤ H := C.conf.tp_le_H
  have hTpK : Tp ≤ Subgroup.normalizer (K : Set G) := hTpH.trans hHK
  have hQN : Q ≤ Subgroup.normalizer (K : Set G) := C.Q_le_normalizer h443 hC24a hC24b hF hK hKq hKM
  have hTQ : T ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hQdef, ← S.hQ]
    exact le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hQTp : Q ≤ Tp :=
    le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le C.conf.vp_le_V))
  have hKQH : K ⊔ Q ≤ H := sup_le hKH (hQTp.trans hTpH)
  have hHKQ : H ≤ Subgroup.normalizer ((K ⊔ Q : Subgroup G) : Set G) := by
    rw [← hH]
    exact sup_le (le_sup_left.trans Subgroup.le_normalizer)
      (le_normalizer_sup_of hTpK (inf_le_left.trans hTQ))
  have hOKQ : pCoreOf 2 (K ⊔ Q) ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans hKQH)
      (hHKQ.trans (normalizer_le_normalizer_pCoreOf (r := 2) (K ⊔ Q))) (pCoreOf_isPGroup 2 _)
  obtain ⟨hUe, hred⟩ := C.isTwoReduced_U hF
  have hVU := C.V_le_U
  have hUO := CFSG.Quasithin.le_pCoreOf_of_isTwoReducedIn hred
  have hOU := CFSG.Quasithin.pCoreOf_le_centralizer_of_isTwoReducedIn hred
  have hVQ : fsuV T I ≤ Q := le_inf (C.conf.V_le_tp.trans inf_le_left)
    (fun v hv => Subgroup.mem_centralizer_iff.2 fun w hw =>
      congrArg Subtype.val (S.comm.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩))
  have hVO : fsuV T I ≤ pCoreOf 2 (K ⊔ Q) := by
    have h1 : pCoreOf 2 H ⊓ (K ⊔ Q) ≤ pCoreOf 2 (K ⊔ Q) :=
      le_pCoreOf_of_le_normalizer 2 inf_le_right
        (fun x hx => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨le_normalizer_pCoreOf 2 H (hKQH hx), Subgroup.le_normalizer hx⟩)
        ((pCoreOf_isPGroup 2 H).to_le inf_le_left)
    exact fun v hv => h1 ⟨hUO (hVU hv), Subgroup.mem_sup_right (hVQ hv)⟩
  have hVV' : fsuV T I ≤ V' := by
    intro v hv
    refine Subgroup.subset_closure ⟨⟨hVO hv, Subgroup.mem_centralizer_iff.2 fun w hw => ?_⟩,
      S.hV.2 v hv⟩
    exact (Subgroup.mem_centralizer_iff.1 (hOU (hOKQ hw)) v (hVU hv)).symm
  have hθL₀ : θ ∈ L₀ := S.th_mem_oTwoUpper hc C.conf.vp_le
  have hL₀K : L₀ ≤ K := hKeq ▸ C.oTwoUpper_le_oPrimeResidualOf
  have hθK : θ ∈ K := hL₀K hθL₀
  obtain ⟨hVmU, hVmZ⟩ := C.vm_le_blockU hF hK hθK (S.L_le_fsuM hc.mem) hc.odd (th_not_mem hc)
  have hVmC : ∀ w ∈ S.vm e, w ∈ Subgroup.centralizer (K : Set G) → w = 1 := by
    intro w hw hwK
    have : w ∈ S.vm e ⊓ blockZ K := ⟨hw, hVmU hw, hwK⟩
    rw [hVmZ] at this
    exact this
  have hVmV' : S.vm e ≤ V' := vm_le.trans hVV'
  have hKV : K ≤ Subgroup.normalizer (V' : Set G) := le_normalizer_omegaOneCenterOf_sup K Q
  have hK2 : CharTwo K := CFSG.Quasithin.A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hF
  obtain ⟨⟨-, -, hredV⟩, ⟨-, hV2, -, A, hAQ, hA⟩, -⟩ := hC27 H _ _ K _ C.hypC23 hK hKq hK2
    (fun h => hKM (h.trans inf_le_left)) hQN rfl
  have : IsMulCommutative ↥V' := hV2.1
  have hKQV : K ⊔ Q ≤ Subgroup.normalizer (V' : Set G) :=
    (le_normalizer_pCoreOf 2 (K ⊔ Q)).trans
      (CFSG.Quasithin.A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hKQK : K ⊔ Q ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hQN
  have hQ2 : IsPGroup 2 ↥Q := C.conf.sylH.2.1.to_le hQTp
  have hpow : ∀ k ∈ K, ∀ q ∈ Subgroup.normalizer (K : Set G), ∀ n : ℕ,
      ∃ k' ∈ K, (k * q) ^ n = k' * q ^ n := by
    intro k hk q hq n
    induction n with
    | zero => exact ⟨1, K.one_mem, by simp⟩
    | succ n ih =>
      obtain ⟨k', hk', e1⟩ := ih
      have hqn : q ^ n ∈ Subgroup.normalizer (K : Set G) := Subgroup.pow_mem _ hq n
      have hc : q ^ n * k * (q ^ n)⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.1 hqn k).1 hk
      refine ⟨k' * (q ^ n * k * (q ^ n)⁻¹), K.mul_mem hk' hc, ?_⟩
      rw [pow_succ, e1, pow_succ]
      group
  have h2 : ∀ x ∈ K ⊔ Q, ∃ n : ℕ, x ^ 2 ^ n ∈ K ⊔ Subgroup.centralizer (V' : Set G) := by
    intro x hx
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left K Q hQN] at hx
    obtain ⟨k, hk, q, hq, rfl⟩ := hx
    obtain ⟨n, hn⟩ := hQ2 ⟨q, hq⟩
    obtain ⟨k', hk', e1⟩ := hpow k hk q (hQN hq) (2 ^ n)
    refine ⟨n, ?_⟩
    have hqn : q ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    rw [e1, hqn, mul_one]
    exact Subgroup.mem_sup_left hk'
  have hO2 : pCoreOf 2 (autOn (K ⊔ Q) V') = ⊥ :=
    CFSG.QuasithinUnique.Setup.pCoreOf_autOn_eq_bot hredV
  have hsl4 := CFSG.Quasithin.H13.NQCat.SLk.isSimpleGroup_sl (n := 4) (by norm_num)
  have hsKs : IsSimpleGroup ↥Ks := θc.isSimpleGroup
  have hnab : ∃ a b : ↥Ks, a * b ≠ b * a := by
    have h0 := tv_noncomm
    have hd0 : (tv 0).det = 1 := det_q13_one 1 0 0 0 0
    have hd2 : (tv 2).det = 1 := det_q13_one 0 0 0 1 0
    set a0 : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨tv 0, hd0⟩ with ha0
    set a2 : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) := ⟨tv 2, hd2⟩ with ha2
    refine ⟨θc.symm a0, θc.symm a2, fun h => h0 ?_⟩
    have h1 := congrArg θc h
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at h1
    have h2 := congrArg (fun z : Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) =>
      (z : Matrix (Fin 4) (Fin 4) (ZMod 2))) h1
    simpa only [Matrix.SpecialLinearGroup.coe_mul] using h2
  obtain ⟨hqKs, hZKs⟩ := CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab
  have hSQ : SQTKGroup ↥H := sqtkGroup_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple
    S.hyp.fsu.nonabelian C.conf.pCoreOf_ne_bot
  have hSK : SQTKGroup ↥K := CFSG.Quasithin.B5.sqtk_of_le hSQ hKH
  have hSKs : SQTKGroup ↥Ks :=
    CFSG.Quasithin.InternalSec.sqtkGroup_autOn hKV hSK ((pCoreOf_isPGroup 2 K).to_le hCK)
  have hAKQ : A ≤ autOn (K ⊔ Q) V' :=
    hAQ.trans (CFSG.Quasithin.InternalSec.autOn_le_autOn_of_le le_sup_right)
  have hKsN : ∀ x ∈ autOn (K ⊔ Q) V', ∀ k ∈ Ks, x * k * x⁻¹ ∈ Ks :=
    CFSG.Quasithin.InternalSec.autOn_normal_of (U := V') hKQK
  have hANKs : A ≤ Subgroup.normalizer (Ks : Set (MulAut ↥V')) := fun a ha =>
    Subgroup.mem_normalizer_iff.2 fun k => ⟨fun hk => hKsN a (hAKQ ha) k hk, fun hk => by
      have := hKsN a⁻¹ (Subgroup.inv_mem _ (hAKQ ha)) _ hk
      simpa [mul_assoc] using this⟩
  have hLA : ⁅Ks, A⁆ = Ks := by
    have hle : ⁅Ks, A⁆ ≤ Ks := Subgroup.le_normalizer_iff_commutator_le_left.1 hANKs
    have hnorm : ((⁅Ks, A⁆ : Subgroup (MulAut ↥V')).subgroupOf Ks).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hle).2
        (Subgroup.normalizer_commutator_ge_left Ks A)
    rcases hnorm.eq_bot_or_eq_top with hbot | htop
    · exfalso
      have hcomm : ⁅Ks, A⁆ = ⊥ := by
        rw [eq_bot_iff]
        intro x hx
        have : (⟨x, hle hx⟩ : ↥Ks) ∈ (⁅Ks, A⁆ : Subgroup (MulAut ↥V')).subgroupOf Ks := hx
        rw [hbot, Subgroup.mem_bot] at this
        exact congrArg Subtype.val this
      have hAC : A ≤ Subgroup.centralizer (Ks : Set (MulAut ↥V')) :=
        (Subgroup.commutator_eq_bot_iff_le_centralizer.1
          (by rw [Subgroup.commutator_comm]; exact hcomm))
      set Cn := Subgroup.centralizer (Ks : Set (MulAut ↥V')) ⊓ autOn (K ⊔ Q) V' with hCn
      have hCn2 : IsPGroup 2 ↥Cn := by
        intro c
        obtain ⟨g, hgKQ, hgc⟩ := CFSG.QuasithinUnique.Setup.mem_autOn_iff.1 c.2.2
        obtain ⟨n, hn⟩ := h2 g hgKQ
        refine ⟨n, Subtype.ext ?_⟩
        have hKC : K ≤ Subgroup.normalizer (Subgroup.centralizer (V' : Set G) : Set G) :=
          fun k hk => mem_normalizer_centralizer (hKV hk)
        rw [sup_comm] at hn
        rw [← SetLike.mem_coe,
          Subgroup.coe_mul_of_right_le_normalizer_left _ K hKC] at hn
        obtain ⟨z, hz, k, hk, hzk⟩ := hn
        have hzN : z ∈ Subgroup.normalizer (V' : Set G) := by
          have : z = g ^ 2 ^ n * k⁻¹ := by rw [← hzk]; group
          rw [this]
          exact Subgroup.mul_mem _ (Subgroup.pow_mem _ g.2 _) (Subgroup.inv_mem _ (hKV hk))
        have hz1 : conjAct V' ⟨z, hzN⟩ = 1 :=
          (CFSG.QuasithinUnique.Setup.rho_eq_one_iff (P := Subgroup.normalizer (V' : Set G))
            le_rfl ⟨z, hzN⟩).2 hz
        have hcpow : (c : MulAut ↥V') ^ 2 ^ n = conjAct V' ⟨k, hKV hk⟩ := by
          rw [← hgc, ← map_pow]
          have e1 : g ^ 2 ^ n = ⟨z, hzN⟩ * ⟨k, hKV hk⟩ := Subtype.ext (by
            rw [Subgroup.coe_pow, Subgroup.coe_mul]
            exact hzk.symm)
          rw [e1, map_mul, hz1, one_mul]
        have hmem : (c : MulAut ↥V') ^ 2 ^ n ∈ Ks := by
          rw [hcpow]
          exact CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨_, hk, rfl⟩
        have hcen : (⟨_, hmem⟩ : ↥Ks) ∈ Subgroup.center ↥Ks := by
          refine Subgroup.mem_center_iff.2 fun b => Subtype.ext ?_
          have hcb := Subgroup.mem_centralizer_iff.1 (Subgroup.pow_mem _ c.2.1 (2 ^ n)) b b.2
          exact hcb
        rw [hZKs, Subgroup.mem_bot] at hcen
        simpa using congrArg Subtype.val hcen
      have hCnN : autOn (K ⊔ Q) V' ≤ Subgroup.normalizer (Cn : Set (MulAut ↥V')) := by
        intro g hg
        refine Subgroup.mem_normalizer_iff.2 fun c => ⟨fun hc => ?_, fun hc => ?_⟩
        · refine ⟨Subgroup.mem_centralizer_iff.2 fun k hk => ?_,
            Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hc.2) (Subgroup.inv_mem _ hg)⟩
          have hk' : g⁻¹ * k * g⁻¹⁻¹ ∈ Ks := hKsN _ (Subgroup.inv_mem _ hg) k hk
          have h1 := Subgroup.mem_centralizer_iff.1 hc.1 _ hk'
          calc k * (g * c * g⁻¹) = g * ((g⁻¹ * k * g⁻¹⁻¹) * c) * g⁻¹ := by group
            _ = g * (c * (g⁻¹ * k * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
            _ = g * c * g⁻¹ * k := by group
        · have hc' : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ ∈ Cn := by
            refine ⟨Subgroup.mem_centralizer_iff.2 fun k hk => ?_,
              Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hg) hc.2)
                (Subgroup.inv_mem _ (Subgroup.inv_mem _ hg))⟩
            have hk' : g * k * g⁻¹ ∈ Ks := hKsN _ hg k hk
            have h1 := Subgroup.mem_centralizer_iff.1 hc.1 _ hk'
            calc k * (g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹)
                = g⁻¹ * ((g * k * g⁻¹) * (g * c * g⁻¹)) * g := by group
              _ = g⁻¹ * ((g * c * g⁻¹) * (g * k * g⁻¹)) * g := by rw [h1]
              _ = g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ * k := by group
          simpa [mul_assoc] using hc'
      have hCnO : Cn ≤ pCoreOf 2 (autOn (K ⊔ Q) V') :=
        le_pCoreOf_of_le_normalizer 2 inf_le_right hCnN hCn2
      rw [hO2] at hCnO
      exact hA.2.1 (le_bot_iff.1 fun a ha => hCnO ⟨hAC ha, hAKQ ha⟩)
    · refine le_antisymm hle fun k hk => ?_
      have : (⟨k, hk⟩ : ↥Ks) ∈ (⁅Ks, A⁆ : Subgroup (MulAut ↥V')).subgroupOf Ks :=
        htop ▸ Subgroup.mem_top _
      exact this
  have hB := (CFSG.Quasithin.InternalSec.b51Hyp_ffJ_autOn hKQV le_sup_left hKQK h2 hO2 hqKs hSKs
    hA hLA).1
  have hV2' : ∀ v : ↥V', v ^ 2 = 1 := fun v => Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hV2.2 v v.2)
  have hPSL : IsPSL 4 2 1 ↥Ks := SLMult.isPSL_of_statedSL_two (m := 4) (by norm_num) eK
  have halt := alt15127_of_b51 h51 hI16 hA8 hV2' hB (Or.inl hPSL)
  have : Finite ↥Ks := Finite.of_equiv _ θc.symm.toEquiv
  have hcardKs : Nat.card ↥Ks = 20160 :=
    (Nat.card_congr eK.toEquiv).trans card_statedSL_four_zmod1527d
  set F : Subgroup ↥V' := (S.vm e).subgroupOf V' with hFdef
  have hFcard : Nat.card ↥F = 16 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVmV').toEquiv).trans S.card_vm
  have hθNV : θ ∈ Subgroup.normalizer (fsuV T I : Set G) := S.hMN (S.L_le_fsuM hc.mem)
  have hVmc := vm_le_commutator hc (y := θ) (m := 1) (by simp) hθNV
  have hFcomm : F ≤ commV Ks := by
    intro x hx
    have hx' : (x : G) ∈ ⁅S.vm e, Subgroup.zpowers θ⁆ := hVmc (Subgroup.mem_subgroupOf.1 hx)
    have hle : ⁅S.vm e, Subgroup.zpowers θ⁆ ≤ (commV Ks).map V'.subtype := by
      rw [Subgroup.commutator_le]
      intro w hw t ht
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 ht
      have hwV' : w ∈ V' := hVmV' hw
      have htK : θ ^ j ∈ K := K.zpow_mem hθK j
      have htN : θ ^ j ∈ Subgroup.normalizer (V' : Set G) := hKV htK
      have hmem : (conjAct V' ⟨θ ^ j, htN⟩ ⟨w, hwV'⟩ * (⟨w, hwV'⟩ : ↥V')⁻¹)⁻¹ ∈ commV Ks :=
        Subgroup.inv_mem _ (Subgroup.subset_closure
          ⟨_, CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨_, htK, rfl⟩, _, rfl⟩)
      refine ⟨_, hmem, ?_⟩
      rw [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, Subgroup.coe_inv,
        CFSG.QuasithinUnique.Setup.coe_conjAct_apply, commutatorElement_def]
      group
    obtain ⟨z, hz, hzx⟩ := hle hx'
    have hzx' : z = x := Subtype.ext hzx
    rw [← hzx']
    exact hz
  have hFfix : F ⊓ fixV Ks = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxF, hxfix⟩
    rw [Subgroup.mem_bot]
    have h1 : (x : G) ∈ Subgroup.centralizer (K : Set G) := by
      refine Subgroup.mem_centralizer_iff.2 fun k hk => ?_
      have h2 := hxfix (conjAct V' ⟨k, hKV hk⟩)
        (CFSG.QuasithinUnique.Setup.mem_autOn_iff.2 ⟨_, hk, rfl⟩)
      have h3 := congrArg Subtype.val h2
      rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply] at h3
      calc k * (x : G) = k * x * k⁻¹ * k := by group
        _ = x * k := by rw [h3]
    exact Subtype.ext (hVmC _ (Subgroup.mem_subgroupOf.1 hxF) h1)
  have hFsc : ∀ k, ∀ u ∈ F, ((θc.symm (scSL k) : ↥Ks) : MulAut ↥V') u = u := by
    intro k u hu
    obtain ⟨a, ha, hak⟩ := Subgroup.mem_map.1 (hcfg.scSL_mem k)
    have hae : θc.symm (scSL k) = a := by
      rw [← hak]
      exact θc.symm_apply_apply a
    rw [hae]
    obtain ⟨g, hgL, hga⟩ :=
      CFSG.QuasithinUnique.Setup.mem_autOn_iff.1 (Subgroup.mem_subgroupOf.1 ha)
    rw [← hga]
    apply Subtype.ext
    rw [CFSG.QuasithinUnique.Setup.coe_conjAct_apply]
    have h1 := Subgroup.mem_centralizer_iff.1 hgL.2 (u : G) (vm_le (Subgroup.mem_subgroupOf.1 hu))
    rw [← h1]
    group
  set f : Fin 4 → MulAut ↥V' := fun k => ((θc.symm (scSL k) : ↥Ks) : MulAut ↥V') with hf
  have hcard8 : Nat.card ↥F ≤ 8 := by
    rcases halt with ⟨Z, hZ, -, hW⟩ | ⟨π, hπ⟩ | ⟨n, hn, π, U₁, U₂, hU, h₁, h₂⟩ |
        ⟨n, hn, k, hk1, hkn, Is, π, -, hind, hsup, hreal⟩
    · have hFZ : F ⊓ Z = ⊥ := by
        rw [eq_bot_iff, ← hFfix]
        exact inf_le_inf_left _ (hZ.trans inf_le_left)
      exact (card_le_wedge θc hW hFcomm hFZ hFsc).trans (by norm_num)
    · exfalso
      have hinj := CFSG.Quasithin.FFC.injective_of_faithful_sec
        (CFSG.Quasithin.FFC.extSq_faithful (by norm_num)) hπ
      have h1 := Nat.card_congr (Equiv.ofBijective π ⟨hinj, hπ.1⟩)
      rw [hcardKs] at h1
      have h2 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) = 9999360 :=
        card_statedSL_five_zmod1527d
      have h3 : Nat.card (FFModel.extSq (ZMod 2) 5).Gam = 9999360 := h2
      omega
    · rcases hn with rfl | rfl
      · have hFU : F ≤ U₁ ⊔ U₂ := hU.1 ▸ hFcomm
        have hinv₁ : ∀ i, ∀ u ∈ U₁, f i u ∈ U₁ := fun i u hu => h₁.2.2.2.1 _ u hu
        have hinv₂ : ∀ i, ∀ u ∈ U₂, f i u ∈ U₂ := fun i u hu => h₂.2.2.2.1 _ u hu
        have hc1 : Nat.card ↥(fixIn U₁ f) ≤ 2 :=
          card_le_nat θc h₁ (fun u hu => (mem_fixIn.1 hu).1) (inf_bot_eq _)
            (fun k u hu => (mem_fixIn.1 hu).2 k)
        have hc2 : Nat.card ↥(fixIn U₂ f) ≤ 2 :=
          card_le_dual θc h₂ (fun u hu => (mem_fixIn.1 hu).1) (inf_bot_eq _)
            (fun k u hu => (mem_fixIn.1 hu).2 k)
        calc Nat.card ↥F ≤ Nat.card ↥(fixIn U₁ f) * Nat.card ↥(fixIn U₂ f) :=
              card_le_mul hU.2 f hinv₁ hinv₂ hFU hFsc
          _ ≤ 2 * 2 := Nat.mul_le_mul hc1 hc2
          _ ≤ 8 := by norm_num
      · exfalso
        have h1 := CFSG.Quasithin.card_eq_of_nat_realizes1527d h₁
        rw [hcardKs] at h1
        have h2 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) = 9999360 :=
          card_statedSL_five_zmod1527d
        omega
    · rcases hn with rfl | rfl
      · have hind' : ∀ j, Is j ⊓ ⨆ (j' : Fin k) (_ : j' ≠ j), Is j' = ⊥ := fun j => by
          simpa using hind j
        have hFI : F ≤ ⨆ j, Is j := by
          rw [bot_sup_eq] at hsup
          rw [hsup]
          exact hFcomm
        have hinv : ∀ i j, ∀ u ∈ Is j, f i u ∈ Is j := fun i j u hu => (hreal j).2.2.2.1 _ u hu
        have hcj : ∀ j, Nat.card ↥(fixIn (Is j) f) ≤ 2 := fun j =>
          card_le_nat θc (hreal j) (fun u hu => (mem_fixIn.1 hu).1) (inf_bot_eq _)
            (fun k u hu => (mem_fixIn.1 hu).2 k)
        calc Nat.card ↥F ≤ ∏ j, Nat.card ↥(fixIn (Is j) f) :=
              card_le_prod Is hind' f hinv hFI hFsc
          _ ≤ ∏ _j : Fin k, 2 := Finset.prod_le_prod fun j _ => hcj j
          _ = 2 ^ k := by rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
          _ ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
          _ = 8 := by norm_num
      · exfalso
        have h1 := CFSG.Quasithin.card_eq_of_nat_realizes1527d (hreal ⟨0, by omega⟩)
        rw [hcardKs] at h1
        have h2 : Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)) = 9999360 :=
          card_statedSL_five_zmod1527d
        omega
  omega

theorem false_of_c27L45
    (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hC24b : ASC24TwoChar G)
    (hA318 : A318Facts) (h36 : A36ForSQTK) (h38 : A38ForSQTK) (h51 : AsB51) (hI16 : AsI16Cover)
    (hA8 : AsI16CoverA8) (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L)
    (h45 : C27L45 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))))) :
    False :=
  C.false_of_excL45 hC27 h443 hC24a hC24b hA318 h36 h38 h51 hI16 hA8 hF hK hKq hKM
    (C.excL45_of_c27L45 hC27 h443 hC24a hC24b hA318 h36 h38 hF hK hKq hKM h45)

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
