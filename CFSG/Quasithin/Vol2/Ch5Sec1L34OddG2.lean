module

public import CFSG.Quasithin.Vol2.Ch5Sec1L34OddF81
public import CFSG.Quasithin.Vol2.Ch6NatRho

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank CFSG.Quasithin.SL2Model
open scoped MatrixGroups

namespace Setup5_1_17Odd

variable {G : Type} [Group G] [Finite G] {T M L V H B D : Subgroup G} {n : ℕ}
variable (s : Setup5_1_17Odd G T M L V H B D n)
include s

theorem mem_Z₁_iff (hI : L2OddInnerFact) {v : G} (hv : v ∈ V) :
    v ∈ quasithinOmegaOneCenter T ⊓ V ↔
      v ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G) := by
  constructor
  · rintro ⟨hvZ, -⟩
    exact Subgroup.centralizer_le (fun x hx => hx.1) (mem_quasithinOmegaOneCenter_iff.mp hvZ).2.1
  · intro hvC
    refine ⟨mem_quasithinOmegaOneCenter_iff.mpr ⟨s.le_T hv, ?_, s.elemAbelian.2 v hv⟩, hv⟩
    rw [Subgroup.mem_centralizer_iff]
    intro t ht
    obtain ⟨l, hl, hlt⟩ := s.exists_inf_conj_eq hI ht
    have h1 : l * v * l⁻¹ = v := by
      rw [Subgroup.mem_centralizer_iff.mp hvC l hl, mul_inv_cancel_right]
    calc t * v = (t * v * t⁻¹) * t := by group
      _ = v * t := by rw [hlt v hv, h1]

theorem exists_line (hI : L2OddInnerFact) (D₀ : NatL2Data L V n) :
    ∃ w : Fin 2 → D₀.K, w ≠ 0 ∧ ∀ v : ↥V, (v : G) ∈ quasithinOmegaOneCenter T ⊓ V ↔
      ∃ c : D₀.K, Multiplicative.toAdd (D₀.E v) = c • w := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := ((T ⊓ L).subgroupOf L).map D₀.rho with hP
  have hTL := s.isSylowTwoOf_inf
  have hP2 : IsPGroup 2 P :=
    (hTL.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTL.1).symm).map D₀.rho
  have h2K : 2 ∣ Nat.card D₀.K := by
    rw [D₀.card]
    exact dvd_pow_self 2 (by have := s.one_le_n; omega)
  have hPne : P ≠ ⊥ := by
    intro h0
    have hodd : ¬ 2 ∣ P.index := fun h2 =>
      hTL.2.2 (h2.trans (Subgroup.index_map_dvd _ D₀.rho_surjective))
    apply hodd
    rw [h0, Subgroup.index_bot, CFSG.GorensteinWalter.sl2_card_formula]
    exact h2K.trans (Dvd.intro _ rfl)
  obtain ⟨w, hw, hfix⟩ := exists_fixed_vector h2K P hP2
  refine ⟨w, hw, fun v => ?_⟩
  rw [s.mem_Z₁_iff hI v.2, D₀.fixed_iff inf_le_right v]
  constructor
  · intro hx
    exact fixed_eq_line P hPne hw hfix fun A hA => by
      obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hA
      exact hx y (Subgroup.mem_subgroupOf.mp hy)
  · rintro ⟨c, hc⟩ x hx
    rw [hc, Matrix.mulVec_smul,
      hfix _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hx))]

theorem isNaturalSL2Module (hI : L2OddInnerFact) :
    IsNaturalSL2Module n L (pCoreOf 2 (L ⊔ T)) V (quasithinOmegaOneCenter T ⊓ V) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D₀⟩ := s.natural.nonempty_data
  have hn : 1 ≤ n := s.one_le_n
  have := Fintype.ofFinite D₀.K
  have hcardF : Nat.card (GaloisField 2 n) = 2 ^ n := GaloisField.card 2 n (by omega)
  have := Fintype.ofFinite (GaloisField 2 n)
  let e : D₀.K ≃+* GaloisField 2 n := FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, D₀.card, hcardF])
  let θ : ↥L →* SL(2, GaloisField 2 n) :=
    (Matrix.SpecialLinearGroup.map e.toRingHom).comp D₀.rho
  let φ : Multiplicative (Fin 2 → D₀.K) ≃* Wm (GaloisField 2 n) :=
    AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => e.toAddEquiv)
  have hφ : ∀ x : Multiplicative (Fin 2 → D₀.K),
      Multiplicative.toAdd (φ x) = e ∘ Multiplicative.toAdd x := fun x => rfl
  let ψ : ↥V ≃* Wm (GaloisField 2 n) := D₀.E.trans φ
  have hmapinj : Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom) := by
    intro A B hAB
    apply Subtype.ext
    ext i j
    have := congrArg (fun C : SL(2, GaloisField 2 n) =>
      (C : Matrix (Fin 2) (Fin 2) (GaloisField 2 n)) i j) hAB
    simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
      Matrix.map_apply] at this
    exact e.injective this
  have hmapsurj : Function.Surjective
      (Matrix.SpecialLinearGroup.map (n := Fin 2) e.toRingHom) := by
    intro B
    refine ⟨Matrix.SpecialLinearGroup.map e.symm.toRingHom B, ?_⟩
    apply Subtype.ext
    ext i j
    simp [Matrix.SpecialLinearGroup.map_apply_coe]
  refine ⟨D₀.le_normalizer, θ, ψ, ?_, ?_, ?_, ?_⟩
  ·
    ext a
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    have h1 : θ a = 1 ↔ D₀.rho a = 1 := by
      constructor
      · intro ha
        apply hmapinj
        rw [map_one]
        exact ha
      · intro ha
        show Matrix.SpecialLinearGroup.map e.toRingHom (D₀.rho a) = 1
        rw [ha, map_one]
    rw [h1, ← MonoidHom.mem_ker, D₀.mem_ker_rho_iff]
    have hCV := s.hyp.hyp.toHyp5_0_1.sup_inf_centralizer_eq s.hyp.module
    constructor
    · intro hc
      rw [← hCV]
      exact ⟨Subgroup.mem_sup_left a.2, hc⟩
    · intro hc
      rw [← hCV] at hc
      exact hc.2
  ·
    have hsurj : Function.Surjective θ := hmapsurj.comp D₀.rho_surjective
    rw [MonoidHom.range_eq_top.mpr hsurj]
    have hn2 : 2 ≤ n := s.hyp.hyp.toHyp5_0_1.two_le
    rcases card_two_or_exists_sq_ne_one (F := GaloisField 2 n) with h2 | ⟨c, hc0, hc1⟩
    · exfalso
      rw [hcardF] at h2
      have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      omega
    · exact (Matrix.SL2.commutator_eq_top hc0 hc1).symm
  ·
    intro a v
    rw [natAct_apply]
    apply Multiplicative.toAdd.injective
    rw [toAdd_ofAdd]
    show Multiplicative.toAdd (φ (D₀.E (conjAct V ⟨a, D₀.le_normalizer a.2⟩ v))) =
      θ a • Multiplicative.toAdd (φ (D₀.E v))
    rw [hφ, hφ, ← D₀.conj_apply, D₀.conj_eq_rho a]
    funext i
    simp only [Function.comp_apply]
    rw [show e (((D₀.rho a : SL(2, D₀.K)) : Matrix (Fin 2) (Fin 2) D₀.K).mulVec
        (Multiplicative.toAdd (D₀.E v)) i) = e.toRingHom
        ((((D₀.rho a : SL(2, D₀.K)) : Matrix (Fin 2) (Fin 2) D₀.K)).mulVec
          (Multiplicative.toAdd (D₀.E v)) i) from rfl, RingHom.map_mulVec e.toRingHom]
    rfl
  ·
    obtain ⟨w, hw, hline⟩ := s.exists_line hI D₀
    refine ⟨e ∘ w, fun h0 => hw ?_, fun v => ?_⟩
    · funext i
      have := congrFun h0 i
      simp only [Function.comp_apply, Pi.zero_apply] at this
      rw [Pi.zero_apply]
      exact (map_eq_zero_iff e e.injective).mp this
    · rw [hline v]
      constructor
      · rintro ⟨c, hc⟩
        refine ⟨e c, ?_⟩
        show Multiplicative.toAdd (φ (D₀.E v)) = e c • (e ∘ w)
        rw [hφ, hc]
        funext i
        simp
      · rintro ⟨c, hc⟩
        refine ⟨e.symm c, ?_⟩
        have hc' : Multiplicative.toAdd (φ (D₀.E v)) = c • (e ∘ w) := hc
        rw [hφ] at hc'
        funext i
        have := congrFun hc' i
        simp only [Function.comp_apply, Pi.smul_apply, smul_eq_mul] at this
        simp only [Pi.smul_apply, smul_eq_mul]
        apply e.injective
        rw [this, map_mul, RingEquiv.apply_symm_apply]

theorem V_eq_conjClosure : V = conjClosure (quasithinOmegaOneCenter T ⊓ V) L := by
  have hW : conjClosure (quasithinOmegaOneCenter T ⊓ V) L ≤ V :=
    CFSG.Quasithin.conjClosure_le fun l hl z hz =>
      (Subgroup.mem_normalizer_iff.mp (s.L_le_normalizer_V hl) z).mp hz.2
  rcases s.natural.irreducible _ hW (le_normalizer_conjClosure _ L) with h0 | h0
  · exfalso
    apply s.Z₁_ne_bot
    rw [eq_bot_iff, ← h0]
    exact le_conjClosure _ _
  · exact h0.symm

theorem D_le_lOne (hI : L2OddInnerFact) : D ≤ lOne L (quasithinOmegaOneCenter T ⊓ V) := by
  have hDL : D ≤ L := s.hyp.notation59.2.1.1.trans inf_le_left
  intro d hd
  refine mem_oTwoUpper_of_odd ⟨hDL hd, s.D_le_normalizer_Z₁ hI hd⟩ ?_
  have h1 : orderOf d ∣ Nat.card D := by
    rw [← Subgroup.orderOf_mk d hd]
    exact orderOf_dvd_natCard _
  exact Odd.of_dvd_nat s.hyp.notation59.2.1.2.1 h1

theorem eq_or_eq_of_D_le_normalizer (hI : L2OddInnerFact) (hF : L2TorusFact) {W : Subgroup G}
    (hW1 : quasithinOmegaOneCenter T ⊓ V ≤ W) (hW2 : W ≤ V)
    (hDW : D ≤ Subgroup.normalizer (W : Set G)) :
    W = quasithinOmegaOneCenter T ⊓ V ∨ W = V := by
  obtain ⟨c⟩ := s.nonempty_coord
  have hmemZ₁ : ∀ v : ↥V, (v : G) ∈ quasithinOmegaOneCenter T ⊓ V ↔ c.ε v 1 = 0 := fun v =>
    ⟨fun h => (s.mem_Z_iff hI c v).mp h.1, fun h => ⟨(s.mem_Z_iff hI c v).mpr h, v.2⟩⟩
  have hεinv : ∀ v w : ↥V, c.ε (v * w⁻¹) = c.ε v - c.ε w := fun v w => by
    have := c.ε_mul (v * w⁻¹) w
    rw [inv_mul_cancel_right] at this
    rw [this]
    abel
  by_cases hWZ : W = quasithinOmegaOneCenter T ⊓ V
  · exact Or.inl hWZ
  right
  obtain ⟨w, hwW, hwZ⟩ : ∃ w ∈ W, w ∉ quasithinOmegaOneCenter T ⊓ V := by
    by_contra hcon
    exact hWZ (le_antisymm (fun w hw => by
      by_contra hw'
      exact hcon ⟨w, hw, hw'⟩) hW1)
  have hwV : w ∈ V := hW2 hwW
  have hw1 : c.ε ⟨w, hwV⟩ 1 ≠ 0 := fun h0 => hwZ ((hmemZ₁ ⟨w, hwV⟩).mpr h0)
  refine le_antisymm hW2 fun v hv => ?_
  by_cases hv1 : c.ε ⟨v, hv⟩ 1 = 0
  · exact hW1 ((hmemZ₁ ⟨v, hv⟩).mpr hv1)
  obtain ⟨d, hdD, hd⟩ := s.exists_D_act_eq hI hF c (div_ne_zero hv1 hw1)
  have hdw : (d : G) * w * (d : G)⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hDW hdD) w).mp hwW
  have hdwV : (d : G) * w * (d : G)⁻¹ ∈ V := hW2 hdw
  have hε : c.ε ⟨(d : G) * w * (d : G)⁻¹, hdwV⟩ 1 = c.ε ⟨v, hv⟩ 1 := by
    have h1 : c.ε ⟨(d : G) * w * (d : G)⁻¹, hdwV⟩ = c.act d (c.ε ⟨w, hwV⟩) := by
      rw [c.act_ε]
      exact congrArg c.ε (Subtype.ext (by rw [conjAct_apply_coe]))
    rw [h1, hd, div_mul_cancel₀ _ hw1]
  have hq : v * ((d : G) * w * (d : G)⁻¹)⁻¹ ∈ W := by
    refine hW1 ((hmemZ₁ ⟨_, V.mul_mem hv (V.inv_mem hdwV)⟩).mpr ?_)
    have := hεinv ⟨v, hv⟩ ⟨_, hdwV⟩
    have e : (⟨v * ((d : G) * w * (d : G)⁻¹)⁻¹, V.mul_mem hv (V.inv_mem hdwV)⟩ : ↥V) =
        ⟨v, hv⟩ * (⟨_, hdwV⟩ : ↥V)⁻¹ := rfl
    rw [e, this, Pi.sub_apply, hε, sub_self]
  have := W.mul_mem hq hdw
  rwa [inv_mul_cancel_right] at this

theorem almostSpecialHyp (hI : L2OddInnerFact) (hF : L2TorusFact) {H₁ : Subgroup G}
    (hH₁ : H ⊔ D ≤ H₁)
    (hH₁N : H₁ ≤ Subgroup.normalizer ((quasithinOmegaOneCenter T ⊓ V : Subgroup G) : Set G)) :
    AlmostSpecialHyp V (quasithinOmegaOneCenter T ⊓ V) L T H₁ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨c⟩ := s.nonempty_coord
  have hh := s.hyp.hyp.toHyp5_0_1
  have hTH : T ≤ H := s.hyp.hyp.hStar.1.1
  have hTH₁ : T ≤ H₁ := hTH.trans (le_sup_left.trans hH₁)
  set Z₁ := quasithinOmegaOneCenter T ⊓ V with hZ₁def
  have hTZ₁ : T ≤ Subgroup.normalizer (Z₁ : Set G) :=
    T_le_centralizer_Z₁.trans (Subgroup.centralizer_le_normalizer _)
  have hlOneN : lOne L Z₁ ≤ L ⊓ Subgroup.normalizer (Z₁ : Set G) := oTwoUpper_le _
  refine
    { elemAbelian := s.elemAbelian
      ne_bot := s.Z₁_ne_bot
      le_V := inf_le_right
      oTwo_eq := ?_
      V_le_T := s.le_T
      T_le_normV₁ := hTZ₁
      T_le_normV := s.T_le_normalizer
      T_le_normL := hh.T_le_normalizer
      sylow_LT := hh.isSylowTwoOf le_sup_right
      H_le := hH₁N
      lOne_sup_le := ?_
      sylow_H := hh.isSylowTwoOf hTH₁
      charTwo := ?_
      irred := ?_ }
  ·
    exact (hh.faithful.2.1 _ (oTwoUpper_le L)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le L)).mpr
        (le_normalizer_oTwoUpper L)) fun x hx => exists_pow_mem_oTwoUpper L hx).symm
  ·
    exact sup_le (hlOneN.trans ((s.inf_normalizer_le hI hF c).trans
      ((sup_le_sup_right hTH D).trans hH₁))) hTH₁
  ·
    refine charTwo_of_inH' hh.qtke hh.sylow ⟨hTH₁, fun hb => ?_⟩
    have hZ₁T : Z₁ ≤ T := inf_le_right.trans s.le_T
    have hZ₁O : Z₁ ≤ pCoreOf 2 H₁ :=
      le_pCoreOf_of_le_normalizer 2 (hZ₁T.trans hTH₁) hH₁N
        ((hh.isSylowTwoOf le_top).2.1.to_le hZ₁T)
    rw [hb] at hZ₁O
    exact s.Z₁_ne_bot (eq_bot_iff.mpr hZ₁O)
  ·
    refine ⟨?_, sup_le ((hlOneN.trans inf_le_left).trans s.L_le_normalizer_V) s.T_le_normalizer,
      sup_le (hlOneN.trans inf_le_right) hTZ₁, fun W hW1 hW2 hWN => ?_⟩
    · refine lt_of_le_of_ne inf_le_right fun heq => ?_
      obtain ⟨v, hv⟩ := c.ε_bij.2 ![0, 1]
      have hvZ : (v : G) ∈ Z₁ := by rw [heq]; exact v.2
      have := (s.mem_Z_iff hI c v).mp hvZ.1
      rw [hv] at this
      exact one_ne_zero this
    · exact s.eq_or_eq_of_D_le_normalizer hI hF hW1 hW2
        ((s.D_le_lOne hI).trans (le_sup_left.trans hWN))

end Setup5_1_17Odd

end CFSG.Quasithin.H13
