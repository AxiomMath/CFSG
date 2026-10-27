module

public import CFSG.Quasithin.Vol2.Ch12Sec7I77b
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zl

public section

namespace CFSG.Quasithin.H13.S127.I77

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S127.L5 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_thetaOf (K : Subgroup G) :
    K ≤ Subgroup.normalizer (thetaOf K : Set G) := by
  intro k hk
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hle : thetaOf K ≤ (thetaOf K).comap (MulAut.conj k).toMonoidHom := by
    rw [thetaOf, Subgroup.closure_le]
    rintro y ⟨hyK, hy3⟩
    refine Subgroup.subset_closure ⟨K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk), ?_⟩
    have := MulEquiv.orderOf_eq (MulAut.conj k) y
    rw [MulAut.conj_apply] at this
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [this, hy3]
  exact hle hx

namespace Set77

variable {T L V : Subgroup G} {t : G} (s : Set77 G T L V t)
include s

omit [Finite G] s in
theorem thetaOf_le : thetaOf (Kt L t) ≤ Kt L t := by
  rw [thetaOf, Subgroup.closure_le]
  exact fun y hy => hy.1

theorem thetaOf_Kt : thetaOf (Kt L t) = Kt L t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn : ((thetaOf (Kt L t)).subgroupOf (Kt L t)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer thetaOf_le]
    exact le_normalizer_thetaOf _
  have hq : CFSG.IsQuasisimple ↥(Kt L t) :=
    CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple s.comp.2.2
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with htop | hcen
  · exact le_antisymm thetaOf_le (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Kt L t)) 3
      (by rw [s.card_Kt]; norm_num)
    have hyθ : (y : G) ∈ thetaOf (Kt L t) :=
      Subgroup.subset_closure ⟨y.2, by rw [Subgroup.orderOf_coe, hy]⟩
    have hyc : y ∈ Subgroup.center ↥(Kt L t) := hcen (Subgroup.mem_subgroupOf.mpr hyθ)
    have h4 : orderOf (⟨y, hyc⟩ : ↥(Subgroup.center ↥(Kt L t))) ∣ 4 :=
      s.card_center ▸ orderOf_dvd_natCard _
    rw [Subgroup.orderOf_mk, hy] at h4
    norm_num at h4

theorem not_le_M : ¬ Kt L t ≤ Subgroup.normalizer (L : Set G) := by
  intro hKM
  have hle : Kt L t ≤ Lt L t := by
    rw [← s.thetaOf_Kt, s.d.theta, thetaOf, thetaOf]
    exact Subgroup.closure_mono fun x hx => ⟨⟨hKM hx.1, s.le_Gt hx.1⟩, hx.2⟩
  have := Subgroup.card_le_of_le hle
  rw [s.card_Kt, s.card_Lt] at this
  norm_num at this

omit [Finite G] s in
theorem lt_le_L : Lt L t ≤ L := (oTwoUpper_le _).trans inf_le_left

theorem t_mem_L : t ∈ L := lt_le_L (s.d.v_le_lt s.d.mem)

theorem centralizer_L_eq_bot (h331 : Stmt3_3_1) :
    T ⊓ Subgroup.centralizer (L : Set G) = ⊥ := by
  have hyp := s.d.hyp.hyp
  have hT2 : IsPGroup 2 T := hyp.sylow.1
  set W := T ⊓ Subgroup.centralizer (L : Set G) with hW
  have hWK : W ≤ Subgroup.centralizer (Kt L t : Set G) := by
    intro w hw
    have hwt : w ∈ Subgroup.centralizer ({t} : Set G) :=
      Subgroup.centralizer_le (Set.singleton_subset_iff.mpr s.t_mem_L) hw.2
    have hw2 : ∃ n : ℕ, orderOf w = 2 ^ n := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨n, hn⟩ := hT2 ⟨w, hw.1⟩
      have h1 : orderOf w ∣ 2 ^ n := by
        rw [← Subgroup.orderOf_mk w hw.1]
        exact orderOf_dvd_of_pow_eq_one hn
      obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
      exact ⟨k, hk⟩
    exact s.mem_centralizer_of (s.normalizer_Gt hwt) hw2
      (Subgroup.centralizer_le lt_le_L hw.2)
  by_contra hne
  have h3 := (h331 G T hyp.simple hyp.nonabelian hyp.qtke hyp.sylow).2 L hyp.maximal
    hyp.quasisimple
  rw [hyp.conjClosure_eq] at h3
  obtain ⟨⟨-, -, huniq⟩, -⟩ := h3
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
    Subgroup.mem_normalizer_fintype fun w hw => by
      rw [(Subgroup.mem_centralizer_iff.mp hw.2 l hl), mul_inv_cancel_right]
      exact hw
  have hTW : T ≤ Subgroup.normalizer (W : Set G) := fun τ hτ =>
    Subgroup.mem_normalizer_fintype fun w hw => by
      refine ⟨T.mul_mem (T.mul_mem hτ hw.1) (T.inv_mem hτ), ?_⟩
      show τ * w * τ⁻¹ ∈ Subgroup.centralizer (L : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      have hl' : τ⁻¹ * l * τ ∈ L := by
        have := (Subgroup.mem_normalizer_iff.mp (hyp.normalizes (T.inv_mem hτ)) l).mp hl
        simpa using this
      have hc := Subgroup.mem_centralizer_iff.mp hw.2 _ hl'
      calc l * (τ * w * τ⁻¹) = τ * ((τ⁻¹ * l * τ) * w) * τ⁻¹ := by group
        _ = τ * (w * (τ⁻¹ * l * τ)) * τ⁻¹ := by rw [hc]
        _ = τ * w * τ⁻¹ * l := by group
  have hWp : IsPGroup 2 W := hT2.to_le inf_le_left
  obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge (L := Subgroup.normalizer (W : Set G))
    ⟨W, hne, hWp, rfl⟩
  have hM'eq : M' = Subgroup.normalizer (L : Set G) := huniq M' hM' ((sup_le hLW hTW).trans hle)
  apply s.not_le_M
  refine le_trans ?_ (hM'eq ▸ hle)
  intro k hk
  refine Subgroup.mem_normalizer_fintype fun w hw => ?_
  rw [(Subgroup.mem_centralizer_iff.mp (hWK hw) k hk), mul_inv_cancel_right]
  exact hw

theorem inf_le_V : pCoreOf 2 L ⊓ Lt L t ≤ V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hle : (pCoreOf 2 L ⊓ Lt L t).subgroupOf (Lt L t) ≤ CFSG.pCore 2 ↥(Lt L t) := by
    refine le_sSup ⟨?_, ?_⟩
    · rw [Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right]
      intro l hl
      refine Subgroup.mem_normalizer_fintype fun y hy => ⟨?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (lt_le_L hl)) y).mp hy.1
      · exact (Lt L t).mul_mem ((Lt L t).mul_mem hl hy.2) ((Lt L t).inv_mem hl)
    · exact ((pCoreOf_isPGroup 2 L).to_le inf_le_left).of_equiv
        (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
  intro x hx
  have hmem : (⟨x, hx.2⟩ : ↥(Lt L t)) ∈ CFSG.pCore 2 ↥(Lt L t) :=
    hle (Subgroup.mem_subgroupOf.mpr hx)
  rw [s.pCore_Lt, Subgroup.mem_subgroupOf] at hmem
  exact hmem

theorem comm_Lt_le : ∀ q ∈ pCoreOf 2 L, ∀ l ∈ Lt L t, q * l * q⁻¹ * l⁻¹ ∈ V := by
  intro q hq l hl
  have hqLC : q ∈ L ⊓ Subgroup.centralizer ({t} : Set G) := by
    rw [← s.o2L] at hq
    exact ⟨hq.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr s.d.mem) hq.2⟩
  have hqN : q ∈ Subgroup.normalizer (Lt L t : Set G) := le_normalizer_oTwoUpper _ hqLC
  refine s.inf_le_V ⟨?_, ?_⟩
  · have h1 : l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 L (lt_le_L hl)) _).mp
        ((pCoreOf 2 L).inv_mem hq)
    have e : q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 L).mul_mem hq h1
  · have h1 : q * l * q⁻¹ ∈ Lt L t := (Subgroup.mem_normalizer_iff.mp hqN l).mp hl
    exact (Lt L t).mul_mem h1 ((Lt L t).inv_mem hl)

theorem comm_le : ⁅pCoreOf 2 L, L⁆ ≤ V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp := s.d.hyp.hyp
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := le_normalizer_V s.d.hyp
  have hLO : L ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) := le_normalizer_pCoreOf 2 L
  let N : Subgroup G :=
    { carrier := {l | l ∈ L ∧ ∀ q ∈ pCoreOf 2 L, q * l * q⁻¹ * l⁻¹ ∈ V}
      mul_mem' := by
        rintro a b ⟨haL, ha⟩ ⟨hbL, hb⟩
        refine ⟨L.mul_mem haL hbL, fun q hq => ?_⟩
        have e : q * (a * b) * q⁻¹ * (a * b)⁻¹ =
            (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e]
        exact V.mul_mem (ha q hq) ((Subgroup.mem_normalizer_iff.mp (hLV haL) _).mp (hb q hq))
      one_mem' := ⟨L.one_mem, fun q _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haL, ha⟩
        refine ⟨L.inv_mem haL, fun q hq => ?_⟩
        have hq' : a⁻¹ * q * a ∈ pCoreOf 2 L := by
          have := (Subgroup.mem_normalizer_iff.mp (hLO (L.inv_mem haL)) q).mp hq
          simpa using this
        have h1 := ha _ hq'
        have e : q * a⁻¹ * q⁻¹ * a⁻¹⁻¹ =
            ((a⁻¹ * q * a) * a * (a⁻¹ * q * a)⁻¹ * a⁻¹)⁻¹ := by group
        rw [e]
        exact V.inv_mem h1 }
  have hNL : N ≤ L := fun x hx => hx.1
  have hLtN : Lt L t ≤ N := fun l hl => ⟨lt_le_L hl, fun q hq => s.comm_Lt_le q hq l hl⟩
  have hNn : (N.subgroupOf L).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hNL]
    intro m hm
    refine Subgroup.mem_normalizer_fintype fun x hx => ?_
    obtain ⟨hxL, hx⟩ := hx
    refine ⟨L.mul_mem (L.mul_mem hm hxL) (L.inv_mem hm), fun q hq => ?_⟩
    have hq' : m⁻¹ * q * m ∈ pCoreOf 2 L := by
      have := (Subgroup.mem_normalizer_iff.mp (hLO (L.inv_mem hm)) q).mp hq
      simpa using this
    have h1 := hx _ hq'
    have e : q * (m * x * m⁻¹) * q⁻¹ * (m * x * m⁻¹)⁻¹ =
        m * ((m⁻¹ * q * m) * x * (m⁻¹ * q * m)⁻¹ * x⁻¹) * m⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hLV hm) _).mp h1
  have hpow : ∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N := by
    set π := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
    have hn' : ((N.subgroupOf L).map π).Normal :=
      Subgroup.Normal.map hNn π (QuotientGroup.mk'_surjective _)
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hyp.quasisimple hn' with htop | hcen
    · intro x hx
      have hmem : π ⟨x, hx⟩ ∈ (N.subgroupOf L).map π := htop ▸ Subgroup.mem_top _
      obtain ⟨n, hn, hnx⟩ := hmem
      have hq2 : n⁻¹ * ⟨x, hx⟩ ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq]
        exact hnx
      obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hq2⟩
      have hk' : (n⁻¹ * ⟨x, hx⟩) ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      refine ⟨k, ?_⟩
      set ρ := QuotientGroup.mk' (N.subgroupOf L) with hρ
      have hn1 : ρ n = 1 := (QuotientGroup.eq_one_iff _).mpr hn
      have hρx : ρ ⟨x, hx⟩ = ρ (n⁻¹ * ⟨x, hx⟩) := by
        rw [map_mul, map_inv, hn1, inv_one, one_mul]
      have h1 : ρ (⟨x, hx⟩ ^ 2 ^ k) = 1 := by
        rw [map_pow, hρx, ← map_pow, hk', map_one]
      have h2 := (QuotientGroup.eq_one_iff _).mp h1
      rw [Subgroup.mem_subgroupOf] at h2
      simpa using h2
    · exfalso
      obtain ⟨e⟩ := s.d.a5
      have hne : ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
        refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
          ⟨Equiv.swap 1 2 * Equiv.swap 2 3, Equiv.Perm.mem_alternatingGroup.mpr (by decide)⟩,
          fun h => ?_⟩
        have := congrArg Subtype.val h
        revert this
        decide
      obtain ⟨u, v, huv⟩ := hne
      obtain ⟨a', ha'⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(Lt L t)) (e.symm u)
      obtain ⟨b', hb'⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(Lt L t)) (e.symm v)
      have hab : a' * b' * (b' * a')⁻¹ ∉ CFSG.pCore 2 ↥(Lt L t) := by
        intro h
        apply huv
        have h1 := (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥(Lt L t)) _).mpr h
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, mul_inv_eq_one,
          QuotientGroup.mk_mul, QuotientGroup.mk_mul] at h1
        rw [QuotientGroup.mk'_apply] at ha' hb'
        rw [ha', hb'] at h1
        have := congrArg e h1
        simpa using this
      set a : G := ((a' : ↥(Lt L t)) : G) with ha
      set b : G := ((b' : ↥(Lt L t)) : G) with hb
      have haL : a ∈ L := lt_le_L a'.2
      have hbL : b ∈ L := lt_le_L b'.2
      have haN : (⟨a, haL⟩ : ↥L) ∈ N.subgroupOf L := hLtN a'.2
      have hbN : (⟨b, hbL⟩ : ↥L) ∈ N.subgroupOf L := hLtN b'.2
      have hca : π ⟨a, haL⟩ ∈ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := hcen ⟨_, haN, rfl⟩
      have hcomm : π ⟨a, haL⟩ * π ⟨b, hbL⟩ = π ⟨b, hbL⟩ * π ⟨a, haL⟩ :=
        (Subgroup.mem_center_iff.mp hca _).symm
      have hpc : (⟨a, haL⟩ * ⟨b, hbL⟩ * (⟨b, hbL⟩ * ⟨a, haL⟩)⁻¹ : ↥L) ∈ CFSG.pCore 2 ↥L := by
        rw [← QuotientGroup.eq_one_iff]
        change π (⟨a, haL⟩ * ⟨b, hbL⟩ * (⟨b, hbL⟩ * ⟨a, haL⟩)⁻¹) = 1
        rw [map_mul, map_inv, map_mul, map_mul, hcomm, mul_inv_cancel]
      have hpcG : a * b * (b * a)⁻¹ ∈ pCoreOf 2 L := by
        rw [pCoreOf]
        exact ⟨_, hpc, rfl⟩
      have hLt' : a * b * (b * a)⁻¹ ∈ Lt L t :=
        (Lt L t).mul_mem ((Lt L t).mul_mem a'.2 b'.2)
          ((Lt L t).inv_mem ((Lt L t).mul_mem b'.2 a'.2))
      have hV := s.inf_le_V ⟨hpcG, hLt'⟩
      apply hab
      rw [s.pCore_Lt, Subgroup.mem_subgroupOf]
      simpa [ha, hb] using hV
  have hNeq : N = L := hyp.faithful.2.1 N hNL hNn hpow
  rw [Subgroup.commutator_le]
  intro q hq l hl
  have hlN : l ∈ N := hNeq ▸ hl
  rw [commutatorElement_def]
  exact hlN.2 q hq

theorem isHatA6Block
    (h1222 : Stmt12_2_2) : IsHatA6Block L :=
  isHatA6Block_of_comm_le h1222 s.d.hyp s.comm_le

theorem centralizer_V_eq
    (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) (h331 : Stmt3_3_1) :
    Subgroup.centralizer (V : Set G) = V :=
  ((lemma12_7_6_of h1222 h1226 G T L V s.d.hyp (s.isHatA6Block h1222)).2
    (s.centralizer_L_eq_bot h331)).2.2.1

theorem centralizer_Kt_eq
    (h1222 : Stmt12_2_2) (h1226 : Stmt12_2_6) (h331 : Stmt3_3_1) :
    Subgroup.centralizer (Kt L t : Set G) = Vt L t := by
  apply le_antisymm
  · intro c hc
    have hcV : c ∈ Subgroup.centralizer (V : Set G) :=
      Subgroup.centralizer_le (s.d.v_le_lt.trans (lt_le_Kt L t)) hc
    rw [s.centralizer_V_eq h1222 h1226 h331] at hcV
    exact s.d.inf_centralizer_le ⟨hcV, Subgroup.centralizer_le (lt_le_Kt L t) hc⟩
  · intro v hv
    exact (s.mem_vt_iff.mp hv).2

end Set77

end CFSG.Quasithin.H13.S127.I77
