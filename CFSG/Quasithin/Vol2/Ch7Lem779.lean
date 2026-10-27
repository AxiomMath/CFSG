module

public import CFSG.Quasithin.Vol2.Ch7Sec77Weyl
public import CFSG.Quasithin.EmptyFaithful.SBc17Cases
public import CFSG.Quasithin.EmptyFaithful.SBc5BorelLift

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem card_map_le_two {K X R : Subgroup G} {Y : Type*} [Group Y] (α : ↥K →* Y) (hXK : X ≤ K)
    (hR2 : R.relIndex X ≤ 2) (hRα : ∀ k : ↥K, (k : G) ∈ R → α k = 1) :
    Nat.card ((X.subgroupOf K).map α) ≤ 2 := by
  have hker : R.subgroupOf K ≤ α.ker := fun k hk => hRα k hk
  rw [← Subgroup.relIndex_ker]
  have h1 : (R.subgroupOf K).relIndex (X.subgroupOf K) = R.relIndex X :=
    Subgroup.relIndex_subgroupOf hXK
  have h2 := Subgroup.relIndex_dvd_of_le_left (L := X.subgroupOf K) hker
  rw [h1] at h2
  have h0 : R.relIndex X ≠ 0 := Subgroup.index_ne_zero_of_finite
  exact (Nat.le_of_dvd (Nat.pos_of_ne_zero h0) h2).trans hR2

omit [Finite G] in
theorem exists_sylow_of_isBorelIn {K B V : Subgroup G}
    (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hBK : B ≤ K)
    (hC2 : IsPGroup 2 ↥(K ⊓ Subgroup.centralizer (V : Set G)))
    (hCB : K ⊓ Subgroup.centralizer (V : Set G) ≤ B) (hB : IsBorelIn (autOn K V) (autOn B V)) :
    ∃ P : Subgroup G, IsSylowTwoOf P K ∧ B = K ⊓ Subgroup.normalizer (P : Set G) := by
  obtain ⟨S, hS, hBS⟩ := hB
  set ψ := Setup.rho V K hKV with hψ
  have hrange : ψ.range = autOn K V := Setup.range_rho hKV
  refine SBc5.exists_sylow_of_borel_image hBK ψ ?_ (by rw [hrange]; exact hS) ?_ ?_
  · intro x
    have hx : ((x : ↥K) : G) ∈ K ⊓ Subgroup.centralizer (V : Set G) :=
      ⟨(x : ↥K).2, (Setup.rho_eq_one_iff hKV (x : ↥K)).1 x.2⟩
    obtain ⟨n, hn⟩ := hC2 ⟨_, hx⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    have := congrArg Subtype.val hn
    simpa using this
  · intro r
    rw [hrange, ← hBS, Setup.mem_autOn_iff_rho hKV hBK]
  · intro x hx
    exact hCB ⟨x.2, (Setup.rho_eq_one_iff hKV x).1 hx⟩

private theorem two_eq_zero_of_card {F : Type} [Field F] [Fintype F] {n : ℕ}
    (h : Fintype.card F = 2 ^ n) : (2 : F) = 0 := by
  obtain ⟨p, hpc, m, hprime, hm⟩ := FiniteField.card' F
  have hdvd : p ∣ 2 ^ n := by
    rw [← h, hm]
    exact dvd_pow_self p m.pos.ne'
  have hp2 : p = 2 :=
    (Nat.prime_dvd_prime_iff_eq hprime Nat.prime_two).mp (hprime.dvd_of_dvd_pow hdvd)
  subst hp2
  have := hpc
  exact_mod_cast CharP.cast_eq_zero F 2

private theorem eq_one_of_mem_center_sl2 {F : Type} [Field F] (h2 : (2 : F) = 0)
    {A : Matrix.SpecialLinearGroup (Fin 2) F}
    (hA : A ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F)) : A = 1 := by
  obtain ⟨r, hr, hA'⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Fintype.card_fin] at hr
  have hr1 : r = 1 := by
    have h0 : (r - 1) ^ 2 = 0 := by
      calc (r - 1) ^ 2 = r ^ 2 - 2 * r + 1 := by ring
        _ = 0 := by rw [hr]; linear_combination (1 - r) * h2
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h0)
  ext i j
  rw [← hA', hr1]
  simp [Matrix.one_apply]

omit [Finite G] in
theorem oTwoZIn_le_pCoreOf_lin2 {K : Subgroup G} {n : ℕ} (h : IsLin2Type K n) :
    oTwoZIn K ≤ pCoreOf 2 K := by
  obtain ⟨F, hF, hFt, hcard, α, hαs, hαk, -⟩ := h
  intro x hx
  unfold oTwoZIn preimageModTwoCore at hx
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hx
  have hz' : (QuotientGroup.mk z : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center _ := hz
  have hc : α z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) := by
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    obtain ⟨ℓ, rfl⟩ := hαs g
    have h2 := Subgroup.mem_center_iff.mp hz' (QuotientGroup.mk ℓ)
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq] at h2
    have h3 : α ((ℓ * z)⁻¹ * (z * ℓ)) = 1 := by
      rw [← MonoidHom.mem_ker, hαk]
      exact h2
    rw [map_mul, map_inv, map_mul, map_mul, inv_mul_eq_one] at h3
    exact h3
  have h1 : α z = 1 := eq_one_of_mem_center_sl2 (two_eq_zero_of_card hcard) hc
  have hzk : z ∈ α.ker := h1
  rw [hαk] at hzk
  exact ⟨z, by assumption, rfl⟩

theorem inf_centralizer_le_pCoreOf_of_c27 {K R V : Subgroup G}
    (h1b : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K)
    (hZ : oTwoZIn K ≤ pCoreOf 2 K) :
    K ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hx' : x ∈ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K := h1b ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have hZK : oTwoZIn K ≤ K := hZ.trans (pCoreOf_le 2 K)
  have hnorm : oTwoZIn K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    hZK.trans (le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ R)))
  obtain ⟨o, ho, z, hz, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hnorm).1 hx'
  have hzK : z ∈ K := hZK hz
  have hoK : o ∈ K := by
    have e : o = o * z * z⁻¹ := by group
    rw [e]
    exact K.mul_mem hx.1 (K.inv_mem hzK)
  have hOK : K ⊓ pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 (K ⊔ R) (Subgroup.mem_sup_left hk)⟩)
      ((pCoreOf_isPGroup 2 (K ⊔ R)).to_le inf_le_right)
  exact (pCoreOf 2 K).mul_mem (hOK ⟨hoK, ho⟩) (hZ hz)

omit [Finite G] in
theorem le_normalizer_omegaOneCenterOf_sup (K R : Subgroup G) :
    K ≤ Subgroup.normalizer (omegaOneCenterOf (pCoreOf 2 (K ⊔ R)) : Set G) :=
  (le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ R))).trans
    (A4.normalizer_le_normalizer_omegaOneCenterOf _)

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem exists_index_two_Q {X : Subgroup G} (hX : X ≤ T ⊓ Subgroup.centralizer (Vp : Set G)) :
    ∃ R : Subgroup G, R ≤ X ∧ R.relIndex X ≤ 2 ∧
      R ≤ T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  have hc := C.conf.hc
  have hXM : X ≤ fsuM T L := hX.trans (inf_le_left.trans S.T_le_fsuM)
  have hXV0 : ∀ x ∈ X, x ∈ Subgroup.centralizer
      ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) : Subgroup G) : Set G) := fun x hx => by
    have h1 := (hX hx).2
    rwa [C.hVp] at h1
  have hX1 : X ≤ Subgroup.centralizer ({S.vec e a1} : Set G) := fun x hx =>
    Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_a1_mem_V0 hc)) (hXV0 x hx)
  have hX2 : IsPGroup 2 ↥X := C.conf.sylH.2.1.to_le hX
  obtain ⟨R, hRX, hR2, hRg⟩ := exists_index_two hc hXM hX1 hX2
  refine ⟨R, hRX, hR2, fun t ht => ⟨(hX (hRX ht)).1, ?_⟩⟩
  obtain ⟨g, hg1, hgb, hg⟩ := hRg t ht
  have htN : t ∈ Subgroup.normalizer (fsuV T I : Set G) := S.hMN (hXM (hRX ht))
  exact mem_centralizer_of_blk htN hg1 hgb (hg htN)
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_b1_mem_V0 hc)) (hXV0 t (hRX ht)))

theorem not_inf_le_pCoreOf {K : Subgroup G} (hK : K ∈ cComp H)
    (htype : (∃ n, 1 < n ∧ IsLin2Type K n) ∨ IsAltType K 5) :
    ¬ T ⊓ Subgroup.centralizer (fsuV T I : Set G) ⊓ K ≤ pCoreOf 2 K := by
  intro hle
  set X := T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K with hXdef
  have hXK : X ≤ K := inf_le_right
  have hXS : IsSylowTwoOf X K :=
    CFSG.Quasithin.A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) C.conf.sylH
  obtain ⟨R, hRX, hR2, hRQ⟩ := C.exists_index_two_Q (inf_le_left : X ≤ _)
  have hRO : ∀ r ∈ R, r ∈ pCoreOf 2 K := fun r hr => hle ⟨hRQ hr, hXK (hRX hr)⟩
  rcases htype with ⟨n, hn, hlin⟩ | h5
  · obtain ⟨F, hF, hFt, ⟨A⟩⟩ := Lin2.exists_adapted (by omega) hlin hXS
    have h2 := card_map_le_two A.α hXK hR2 fun k hk => (A.mem_pCoreOf_iff k).1 (hRO _ hk)
    have hge : Nat.card (Lin2.slUni F) ≤ Nat.card ((X.subgroupOf K).map A.α) := by
      refine Subgroup.card_le_of_le fun u hu => ?_
      obtain ⟨ℓ, rfl⟩ := A.α_surj u
      exact ⟨ℓ, Subgroup.mem_subgroupOf.mpr ((A.mem_P ℓ).2 hu), rfl⟩
    rw [Lin2.card_slUni, Nat.card_eq_fintype_card, A.card_eq] at hge
    have h4 : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  · obtain ⟨α, hαs, hαk, -⟩ := h5
    have h4 : Nat.card ((X.subgroupOf K).map α) = 4 := card_map_sylow_alt5 α hαs hXS
    have h2 := card_map_le_two α hXK hR2 fun k hk => by
      obtain ⟨k', hk', hkk'⟩ := hRO _ hk
      have e : k' = k := Subtype.ext hkk'
      subst e
      have : k' ∈ α.ker := by rw [hαk]; assumption
      exact this
    omega

theorem not_inf_le_Q (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ fsuM T L) :
    ¬ T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K ≤
      T ⊓ Subgroup.centralizer (fsuV T I : Set G) := by
  intro hle
  apply C.false_of_sylow h443 hC24a hF hK hKq hKM
  have hXS : IsSylowTwoOf (T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K) K :=
    CFSG.Quasithin.A312.isSylowTwoOf_inf_of_subnormal (subnormal_of_mem_cComp hK) C.conf.sylH
  have heq : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ⊓ K =
      T ⊓ Subgroup.centralizer (Vp : Set G) ⊓ K :=
    le_antisymm (inf_le_inf_right _ (inf_le_inf_left _
      (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr C.conf.vp_le_V))))
      (le_inf hle inf_le_right)
  rw [heq]
  exact hXS

theorem c27Cases (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G)
    (hC24b : ASC24TwoChar G) (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L) :
    C27Cases H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) :=
  asc27_cases hC27 C.hypC23 hK hKq
    (CFSG.Quasithin.A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hF)
    (fun h => hKM (h.trans inf_le_left)) (C.Q_le_normalizer h443 hC24a hC24b hF hK hKq hKM) rfl

theorem false_of_c27A5 (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hF : CharTwo H)
    {K V' : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ fsuM T L)
    (hQN : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ Subgroup.normalizer (K : Set G))
    (h : C27A5 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K V') : False := by
  obtain ⟨-, -, hQs, -⟩ := h
  apply C.false_of_sylow h443 hC24a hF hK hKq hKM
  have hKn : (K.subgroupOf (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer hQN)
  exact CFSG.Quasithin.A312.isSylowTwoOf_inf_of_subnormal
    (CFSG.Quasithin.A4.subnormal_of_normal le_sup_left hKn) hQs

theorem false_of_c27L2 (h443 : Stmt4_4_3Orbit') (hF : CharTwo H) {K : Subgroup G}
    (hK : K ∈ cComp H)
    (h1b : (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)) ⊓ Subgroup.centralizer
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))) :
        Set G) ≤ pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)) ⊔ oTwoZIn K)
    (h : C27L2 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
      (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, ⟨n, hn, hlin⟩, -, hB⟩ := h
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hKV := le_normalizer_omegaOneCenterOf_sup K (T ⊓ Subgroup.centralizer (fsuV T I : Set G))
  have hCO := inf_centralizer_le_pCoreOf_of_c27 h1b (oTwoZIn_le_pCoreOf_lin2 hlin)
  have hC2 := (pCoreOf_isPGroup 2 K).to_le hCO
  have hCB : K ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2
      (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G))) : Set G) ≤ fsuM T L ⊓ H ⊓ K :=
    fun x hx => ⟨⟨C.pCoreOf_le_fsuM hK (hCO hx), hKH hx.1⟩, hx.1⟩
  obtain ⟨P, hP, hBeq⟩ := exists_sylow_of_isBorelIn hKV inf_le_right hC2 hCB hB
  have hB1 : K ⊓ fsuM T L ≤ Subgroup.normalizer (P : Set G) := fun x hx => by
    have h1 : x ∈ fsuM T L ⊓ H ⊓ K := ⟨⟨hx.2, hKH hx.1⟩, hx.1⟩
    rw [hBeq] at h1
    exact h1.2
  have hB2 : K ⊓ Subgroup.normalizer (P : Set G) ≤ fsuM T L := fun x hx => by
    rw [← hBeq] at hx
    exact hx.1.1
  exact C.false_of_block h443 hF hK (Or.inl ⟨n, hn, hlin⟩) hP hB1 hB2
    (C.not_inf_le_pCoreOf hK (Or.inl ⟨n, hn, hlin⟩))

theorem c27Cases_rest (hC27 : ASC27Statement G) (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G)
    (hC24b : ASC24TwoChar G) (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) (hKM : ¬ K ≤ fsuM T L) :
    C27A7a H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27A7b H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27Alt H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27Hat6 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27ExcA7 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27A6Sp4 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27G2 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27SL3 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) ∨
      C27L45 H (T ⊓ Subgroup.centralizer (fsuV T I : Set G)) (fsuM T L ⊓ H) K
        (omegaOneCenterOf (pCoreOf 2 (K ⊔ T ⊓ Subgroup.centralizer (fsuV T I : Set G)))) := by
  have hQN := C.Q_le_normalizer h443 hC24a hC24b hF hK hKq hKM
  have hK2 : CharTwo K := CFSG.Quasithin.A4.charTwo_of_subnormal (subnormal_of_mem_cComp hK) hF
  obtain ⟨⟨-, h1b, -⟩, -, -⟩ := hC27 H _ _ K _ C.hypC23 hK hKq hK2
    (fun h => hKM (h.trans inf_le_left)) hQN rfl
  rcases C.c27Cases hC27 h443 hC24a hC24b hF hK hKq hKM with h | h | h
  · exact (C.false_of_c27L2 h443 hF hK h1b h).elim
  · exact (C.false_of_c27A5 h443 hC24a hF hK hKq hKM hQN h).elim
  · exact h

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
