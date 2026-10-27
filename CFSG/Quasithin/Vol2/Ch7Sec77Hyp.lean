module

public import CFSG.Quasithin.Vol2.Ch7Sec77Min
public import CFSG.Quasithin.Background.HGL2Comm

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem oTwoUpper_oTwoUpper (X : Subgroup G) : oTwoUpper (oTwoUpper X) = oTwoUpper X :=
  le_antisymm (oTwoUpper_le _) ((Subgroup.closure_le _).mpr fun _ hx =>
    mem_oTwoUpper_of_odd (Subgroup.subset_closure hx) hx.2)

theorem eq_one_of_pow_three_of_pow_two_pow {Ω : Type*} [Monoid Ω] {y : Ω} {n : ℕ}
    (h3 : y ^ 3 = 1) (h2 : y ^ 2 ^ n = 1) : y = 1 := by
  have h : y ^ Nat.gcd 3 (2 ^ n) = 1 := pow_gcd_eq_one.mpr ⟨h3, h2⟩
  rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right n (by norm_num : Nat.Coprime 3 2)),
    pow_one] at h

namespace Setup

variable (S : Setup T L I)
include S

theorem pCoreOf_LT : pCoreOf 2 (L ⊔ T) = T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have h := S.hQ
  rwa [S.fsuL0_eq] at h

theorem fsuV_le_Q : fsuV T I ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) :=
  le_inf S.fsuV_le_T fun v hv => Subgroup.mem_centralizer_iff.mpr fun w hw =>
    congrArg Subtype.val (S.comm.is_comm.comm ⟨w, hw⟩ ⟨v, hv⟩)

theorem Q_ne_bot : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≠ ⊥ := fun h =>
  S.fsuV_ne_bot (le_bot_iff.mp (h ▸ S.fsuV_le_Q))

theorem isPGroup_Q : IsPGroup 2 ↥(T ⊓ Subgroup.centralizer (fsuV T I : Set G)) := by
  rw [← S.pCoreOf_LT]
  exact pCoreOf_isPGroup 2 _

theorem LT_le_normalizer_Q : L ⊔ T ≤ Subgroup.normalizer
    ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) : Set G) := by
  rw [← S.pCoreOf_LT]
  exact le_normalizer_pCoreOf 2 _

theorem normalizer_le_of_le {C : Subgroup G} (hC2 : IsPGroup 2 C) (hC1 : C ≠ ⊥)
    (hLT : L ⊔ T ≤ Subgroup.normalizer (C : Set G)) :
    Subgroup.normalizer (C : Set G) ≤ fsuM T L := by
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (C : Set G))
    ⟨C, hC1, hC2, rfl⟩
  have hEq : M' = fsuM T L := S.uniq.2 M' ⟨hM', hLT.trans hle⟩
  exact hEq ▸ hle

theorem cgsIn_Q_le (H : Subgroup G) :
    cgsIn H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) ≤ fsuM T L ⊓ H := by
  refine iSup_le fun C => iSup_le fun hCQ => iSup_le fun hC1 => iSup_le fun hchar => ?_
  have hCN : Subgroup.normalizer ((T ⊓ Subgroup.centralizer (fsuV T I : Set G) : Subgroup G) :
      Set G) ≤ Subgroup.normalizer (C : Set G) := by
    have h := normalizer_le_normalizer_map_of_characteristic
      (C.subgroupOf (T ⊓ Subgroup.centralizer (fsuV T I : Set G)))
    rwa [Subgroup.map_subgroupOf_eq_of_le hCQ] at h
  have hN : Subgroup.normalizer (C : Set G) ≤ fsuM T L :=
    S.normalizer_le_of_le (S.isPGroup_Q.to_le hCQ) hC1 (S.LT_le_normalizer_Q.trans hCN)
  exact le_inf (inf_le_right.trans hN) inf_le_left

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem le_normalizer_L0 : fsuM T L ⊓ H ≤
    Subgroup.normalizer (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) : Set G) := by
  refine le_trans ?_ (CFSG.Quasithin.normalizer_le_normalizer_oTwoUpper _)
  intro m hm
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨S.fsuM_le_normalizer_L hm.1, Subgroup.le_normalizer (C.conf.hHG hm.2)⟩

theorem centralizer_V_le : Subgroup.centralizer (fsuV T I : Set G) ≤
    Subgroup.centralizer (Vp : Set G) :=
  Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr C.conf.vp_le_V)

theorem Q_le_normalizer_L0 : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤
    Subgroup.normalizer (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) : Set G) := by
  refine le_trans ?_ (CFSG.Quasithin.normalizer_le_normalizer_oTwoUpper _)
  intro q hq
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨S.T_le_normalizer_L hq.1, Subgroup.le_normalizer (C.centralizer_V_le hq.2)⟩

theorem isSylowTwoOf_Q : IsSylowTwoOf (T ⊓ Subgroup.centralizer (fsuV T I : Set G))
    (centralizerSection (fsuM T L ⊓ H) (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)))
      (pCoreOf 2 (oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G))))) := by
  have hc := C.conf.hc
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  set L₀ := oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) with hL₀
  set Tp := T ⊓ Subgroup.centralizer (Vp : Set G) with hTp
  set MH := fsuM T L ⊓ H with hMH
  set C₀ := centralizerSection MH L₀ (pCoreOf 2 L₀) with hC₀
  have hQTp : Q ≤ Tp := inf_le_inf_left _ C.centralizer_V_le
  have hTpH : Tp ≤ H := C.conf.tp_le_H
  have hTpM : Tp ≤ fsuM T L := inf_le_left.trans S.T_le_fsuM
  have hQMH : Q ≤ MH := fun q hq => ⟨hTpM (hQTp hq), hTpH (hQTp hq)⟩
  have hL₀Q : L₀ ≤ Subgroup.normalizer (Q : Set G) :=
    ((oTwoUpper_le _).trans (inf_le_left.trans le_sup_left)).trans S.LT_le_normalizer_Q
  have hQC₀ : Q ≤ C₀ := by
    intro q hq
    have hqN := C.Q_le_normalizer_L0 hq
    refine ⟨hQMH hq, hqN, normalizer_le_normalizer_pCoreOf 2 L₀ hqN, fun y hy => ?_⟩
    have hLQ : L₀ ⊓ Q ≤ pCoreOf 2 L₀ :=
      CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
        (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hg, hL₀Q hg⟩)
        (S.isPGroup_Q.to_le inf_le_right)
    refine hLQ ⟨?_, ?_⟩
    · have e : y * q * y⁻¹ * q⁻¹ = y * (q * y⁻¹ * q⁻¹) := by group
      rw [e]
      exact L₀.mul_mem hy ((Subgroup.mem_normalizer_iff.mp hqN y⁻¹).mp (L₀.inv_mem hy))
    · exact Q.mul_mem ((Subgroup.mem_normalizer_iff.mp (hL₀Q hy) q).mp hq) (Q.inv_mem hq)
  have hTC : Tp ⊓ C₀ ≤ Q := by
    rintro x ⟨hxT, hxC⟩
    refine ⟨hxT.1, ?_⟩
    have hxM : x ∈ fsuM T L := hTpM hxT
    set X := fsuM T L ⊓ Subgroup.centralizer (Vp : Set G) with hX
    have hXM : X ≤ fsuM T L := inf_le_left
    have hVa : S.vec e a1 ∈ Vp := by rw [C.hVp]; exact vec_a1_mem_V0 hc
    have hVb : S.vec e b1 ∈ Vp := by rw [C.hVp]; exact vec_b1_mem_V0 hc
    have hX1 : X ≤ Subgroup.centralizer ({S.vec e a1} : Set G) :=
      inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hVa))
    obtain ⟨φ, hφ⟩ := exists_stabHom hc hXM hX1
    set χ : ↥X →* GL (Fin 2) (ZMod 2) := blkHom.comp φ with hχ
    have hθL₀ : θ ∈ L₀ := S.th_mem_oTwoUpper hc C.conf.vp_le
    have hθX : θ ∈ X := ⟨S.L_le_fsuM hc.mem, ((oTwoUpper_le _) hθL₀).2⟩
    have hφθ : (φ ⟨θ, hθX⟩ : SL32) = th0 := SL3One.rho_injective ((hφ ⟨θ, hθX⟩).trans hc.hθ)
    have hφθ3 : φ ⟨θ, hθX⟩ ^ 3 = 1 := Subtype.ext (by
      rw [SubgroupClass.coe_pow, hφθ, th0_pow_three, OneMemClass.coe_one])
    have hχθ3 : χ ⟨θ, hθX⟩ ^ 3 = 1 := by
      rw [hχ, MonoidHom.comp_apply, ← map_pow, hφθ3, map_one]
    have hχθ1 : χ ⟨θ, hθX⟩ ≠ 1 := by
      intro h
      have h1 : (χ ⟨θ, hθX⟩ : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by rw [h]; rfl
      rw [hχ, MonoidHom.comp_apply, coe_blkHom, hφθ] at h1
      exact blk_th0_ne_one h1
    have hxX : x ∈ X := ⟨hxM, hxT.2⟩
    have hk : θ * x * θ⁻¹ * x⁻¹ ∈ pCoreOf 2 L₀ := hxC.2.2.2 θ hθL₀
    have hkX : θ * x * θ⁻¹ * x⁻¹ ∈ X :=
      ((pCoreOf_le 2 L₀).trans ((oTwoUpper_le _).trans (inf_le_inf_right _ S.L_le_fsuM))) hk
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 L₀ ⟨_, hk⟩
    have hkn : (⟨_, hkX⟩ : ↥X) ^ 2 ^ n = 1 := Subtype.ext (by
      have := congrArg Subtype.val hn
      simpa using this)
    have hkeq : (⟨_, hkX⟩ : ↥X) = ⟨θ, hθX⟩ * ⟨x, hxX⟩ * (⟨θ, hθX⟩ : ↥X)⁻¹ * (⟨x, hxX⟩ : ↥X)⁻¹ :=
      rfl
    have hχk : χ ⟨_, hkX⟩ = 1 := by
      refine eq_one_of_pow_three_of_pow_two_pow (n := n) ?_ ?_
      · rw [hkeq, map_mul, map_mul, map_mul, map_inv, map_inv]
        exact gl2_comm_pow_three _ _
      · rw [← map_pow, hkn, map_one]
    have hcomm : χ ⟨θ, hθX⟩ * χ ⟨x, hxX⟩ = χ ⟨x, hxX⟩ * χ ⟨θ, hθX⟩ := by
      rw [hkeq, map_mul, map_mul, map_mul, map_inv, map_inv] at hχk
      calc χ ⟨θ, hθX⟩ * χ ⟨x, hxX⟩
          = (χ ⟨θ, hθX⟩ * χ ⟨x, hxX⟩ * (χ ⟨θ, hθX⟩)⁻¹ * (χ ⟨x, hxX⟩)⁻¹) *
              (χ ⟨x, hxX⟩ * χ ⟨θ, hθX⟩) := by group
        _ = χ ⟨x, hxX⟩ * χ ⟨θ, hθX⟩ := by rw [hχk, one_mul]
    have hχx3 := gl2_pow_three_of_comm _ _ hχθ3 hχθ1 hcomm
    obtain ⟨m, hm⟩ := C.conf.sylG.2.1 ⟨x, hxT⟩
    have hxm : (⟨x, hxX⟩ : ↥X) ^ 2 ^ m = 1 := Subtype.ext (by
      have := congrArg Subtype.val hm
      simpa using this)
    have hχx : χ ⟨x, hxX⟩ = 1 :=
      eq_one_of_pow_three_of_pow_two_pow hχx3 (by rw [← map_pow, hxm, map_one])
    have hb : blk (φ ⟨x, hxX⟩ : SL32) = 1 := by
      have h1 : (χ ⟨x, hxX⟩ : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by rw [hχx]; rfl
      rwa [hχ, MonoidHom.comp_apply, coe_blkHom] at h1
    exact mem_centralizer_of_blk (S.hMN hxM) (φ ⟨x, hxX⟩).2 hb (hφ ⟨x, hxX⟩).symm
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hVb) hxT.2)
  have hTpMH : IsSylowTwoOf Tp MH :=
    A4.isSylowTwoOf_mono C.conf.sylH (le_inf hTpM hTpH) inf_le_right
  have hC₀MH : C₀ ≤ MH := centralizerSection_le_left MH L₀ _
  have hC₀n : (C₀.subgroupOf MH).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC₀MH).2 (centralizerSection_normal C.le_normalizer_L0)
  have hsyl := RankOneRecog.isSylowTwoOf_inf_of_subnormal hTpMH hC₀MH hC₀n.isSubnormal
  have heq : Tp ⊓ C₀ = Q := le_antisymm hTC (le_inf hQTp hQC₀)
  rwa [heq] at hsyl

theorem hypC23 : HypC23 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) := by
  set Q := T ⊓ Subgroup.centralizer (fsuV T I : Set G) with hQdef
  have hL₀MH : oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G)) ≤ fsuM T L ⊓ H :=
    le_inf ((oTwoUpper_le _).trans (inf_le_left.trans S.L_le_fsuM)) (le_sup_left.trans C.conf.hLH)
  have hL₀n : ((oTwoUpper (L ⊓ Subgroup.centralizer (Vp : Set G))).subgroupOf
      (fsuM T L ⊓ H)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hL₀MH).2 C.le_normalizer_L0
  obtain ⟨hsyl, hrad⟩ := c1_2_four (oTwoUpper_oTwoUpper _).symm hL₀MH hL₀n C.isSylowTwoOf_Q
    S.Q_ne_bot
  have hNQ : Subgroup.normalizer (Q : Set G) ≤ fsuM T L :=
    S.normalizer_le_of_le S.isPGroup_Q S.Q_ne_bot S.LT_le_normalizer_Q
  refine ⟨sqtkGroup_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian
    C.conf.pCoreOf_ne_bot, ⟨hrad.1.trans inf_le_right, hrad.2.1, ?_⟩, inf_le_right,
    S.cgsIn_Q_le H, hsyl⟩
  have e : H ⊓ Subgroup.normalizer (Q : Set G) =
      (fsuM T L ⊓ H) ⊓ Subgroup.normalizer (Q : Set G) := by
    ext g
    exact ⟨fun hg => ⟨⟨hNQ hg.2, hg.1⟩, hg.2⟩, fun hg => ⟨hg.1.2, hg.2⟩⟩
  rw [e]
  exact hrad.2.2

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
