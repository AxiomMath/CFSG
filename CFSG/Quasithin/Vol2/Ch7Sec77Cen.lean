module

public import CFSG.Quasithin.Vol2.Ch7Lem779

public section

namespace CFSG.Quasithin.H13.Sec77

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.S77
  CFSG.Quasithin.H.SL3Pair CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.H.BlkW
  CFSG.Quasithin.SBc17 CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

omit [Finite G] in
theorem conj_pow_mul_inv_mem {K : Subgroup G} {z : G} (hzK : z ∈ K)
    (hz : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ pCoreOf 2 K) {k : G} (hk : k ∈ K) (n : ℕ) :
    k * z ^ n * k⁻¹ * (z ^ n)⁻¹ ∈ pCoreOf 2 K := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hN : z ^ n ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      le_normalizer_pCoreOf 2 K (K.pow_mem hzK n)
    have e : k * z ^ (n + 1) * k⁻¹ * (z ^ (n + 1))⁻¹ =
        (k * z ^ n * k⁻¹ * (z ^ n)⁻¹) * (z ^ n * (k * z * k⁻¹ * z⁻¹) * (z ^ n)⁻¹) := by
      rw [pow_succ]
      group
    rw [e]
    exact (pCoreOf 2 K).mul_mem ih ((Subgroup.mem_normalizer_iff.mp hN _).mp (hz k hk))

theorem exists_mem_normalizer_zpowers {K : Subgroup G} {z : G} (hzK : z ∈ K)
    (hzo : Odd (orderOf z)) (hz : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ pCoreOf 2 K) {k : G}
    (hk : k ∈ K) :
    ∃ o ∈ pCoreOf 2 K, o * k ∈ Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine exists_mem_normalizer_of_conj_le (by rw [Nat.card_zpowers]; exact hzo)
    (pCoreOf_isPGroup 2 K) ((Subgroup.zpowers_le).mpr (le_normalizer_pCoreOf 2 K hzK))
    (le_normalizer_pCoreOf 2 K hk) ?_
  intro a ha
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, z ^ n = a := (mem_powers_iff_mem_zpowers).mpr ha
  have h1 := conj_pow_mul_inv_mem hzK hz hk n
  have e : k * z ^ n * k⁻¹ = (k * z ^ n * k⁻¹ * (z ^ n)⁻¹) * z ^ n := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
    (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) n))

omit [Finite G] in
theorem isMulCommutative_zpowers (z : G) : IsMulCommutative ↥(Subgroup.zpowers z) :=
  ⟨⟨fun a b => Subtype.ext (by
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
    change (a : G) * b = b * a
    rw [← hi, ← hj, ← zpow_add, ← zpow_add, add_comm])⟩⟩

omit [Finite G] in
theorem commutator_mem_of_mem_oTwoZIn {K : Subgroup G} {z : G} (hz : z ∈ oTwoZIn K) {k : G}
    (hk : k ∈ K) : k * z * k⁻¹ * z⁻¹ ∈ pCoreOf 2 K := by
  unfold oTwoZIn preimageModTwoCore at hz
  obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.mp hz
  have hc : (QuotientGroup.mk z' : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center _ := hz'
  have h1 := Subgroup.mem_center_iff.mp hc (QuotientGroup.mk ⟨k, hk⟩)
  have h2 : (⟨k, hk⟩ * z' * (⟨k, hk⟩ : ↥K)⁻¹ * z'⁻¹ : ↥K) ∈ CFSG.pCore 2 ↥K := by
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv, h1]
    group
  exact ⟨_, by assumption, rfl⟩

omit [Finite G] in
theorem pCoreOf_le_oTwoZIn' (K : Subgroup G) : pCoreOf 2 K ≤ oTwoZIn K := by
  rintro _ ⟨x, hx, rfl⟩
  unfold oTwoZIn preimageModTwoCore
  refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
  have hx' : x ∈ CFSG.pCore 2 ↥K := by assumption
  change (QuotientGroup.mk x : ↥K ⧸ CFSG.pCore 2 ↥K) ∈ Subgroup.center _
  rw [(QuotientGroup.eq_one_iff x).mpr hx']
  exact one_mem _

omit [Finite G] in
theorem oTwoZIn_le' (K : Subgroup G) : oTwoZIn K ≤ K := by
  unfold oTwoZIn preimageModTwoCore
  exact Subgroup.map_subtype_le _

theorem inf_centralizer_le_oTwoZIn_of_c27 {K R V : Subgroup G}
    (h1b : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K) :
    K ⊓ Subgroup.centralizer (V : Set G) ≤ oTwoZIn K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro x hx
  have hx' : x ∈ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K := h1b ⟨Subgroup.mem_sup_left hx.1, hx.2⟩
  have hnorm : oTwoZIn K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    (oTwoZIn_le' K).trans (le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ R)))
  obtain ⟨o, ho, z, hz, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hnorm).1 hx'
  have hzK : z ∈ K := oTwoZIn_le' K hz
  have hoK : o ∈ K := by
    have e : o = o * z * z⁻¹ := by group
    rw [e]
    exact K.mul_mem hx.1 (K.inv_mem hzK)
  have hOK : K ⊓ pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 (K ⊔ R) (Subgroup.mem_sup_left hk)⟩)
      ((pCoreOf_isPGroup 2 (K ⊔ R)).to_le inf_le_right)
  exact (oTwoZIn K).mul_mem (pCoreOf_le_oTwoZIn' K (hOK ⟨hoK, ho⟩)) hz

theorem commutator_mem_of_c27 {K R V : Subgroup G} (hR : R ≤ Subgroup.normalizer (K : Set G))
    (h1b : (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K) {c : G}
    (hc : c ∈ (K ⊔ R) ⊓ Subgroup.centralizer (V : Set G)) {k : G} (hk : k ∈ K) :
    c * k * c⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc' : c ∈ pCoreOf 2 (K ⊔ R) ⊔ oTwoZIn K := h1b hc
  have hnorm : oTwoZIn K ≤ Subgroup.normalizer (pCoreOf 2 (K ⊔ R) : Set G) :=
    (oTwoZIn_le' K).trans (le_sup_left.trans (le_normalizer_pCoreOf 2 (K ⊔ R)))
  obtain ⟨o, ho, z, hz, rfl⟩ := (Lin2.mem_sup_iff_of_le_normalizer hnorm).1 hc'
  have hKRN : K ⊔ R ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hR
  have hoKR : o ∈ K ⊔ R := pCoreOf_le 2 (K ⊔ R) ho
  have hoN : o ∈ Subgroup.normalizer (K : Set G) := hKRN hoKR
  have hoN2 : o ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K hoN
  have hzk : z * k * z⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    have h1 := commutator_mem_of_mem_oTwoZIn hz hk
    have e : z * k * z⁻¹ * k⁻¹ = (k * z * k⁻¹ * z⁻¹)⁻¹ := by group
    rw [e]
    exact (pCoreOf 2 K).inv_mem h1
  have hOK : K ⊓ pCoreOf 2 (K ⊔ R) ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, le_normalizer_pCoreOf 2 (K ⊔ R) (Subgroup.mem_sup_left hk)⟩)
      ((pCoreOf_isPGroup 2 (K ⊔ R)).to_le inf_le_right)
  have hok : o * k * o⁻¹ * k⁻¹ ∈ pCoreOf 2 K := by
    refine hOK ⟨K.mul_mem ((Subgroup.mem_normalizer_iff.mp hoN k).mp hk) (K.inv_mem hk), ?_⟩
    have h1 : k * o⁻¹ * k⁻¹ ∈ pCoreOf 2 (K ⊔ R) :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (K ⊔ R)
        (Subgroup.mem_sup_left hk)) _).mp ((pCoreOf 2 (K ⊔ R)).inv_mem ho)
    have e : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
    rw [e]
    exact (pCoreOf 2 (K ⊔ R)).mul_mem ho h1
  have e : o * z * k * (o * z)⁻¹ * k⁻¹ =
      (o * (z * k * z⁻¹ * k⁻¹) * o⁻¹) * (o * k * o⁻¹ * k⁻¹) := by group
  rw [e]
  exact (pCoreOf 2 K).mul_mem ((Subgroup.mem_normalizer_iff.mp hoN2 _).mp hzk) hok

theorem card_map_sylow_eq {K S : Subgroup G} {Y : Type*} [Group Y] [Finite Y] (α : ↥K →* Y)
    (hαs : Function.Surjective α) (hS : IsSylowTwoOf S K) :
    Nat.card ((S.subgroupOf K).map α) = 2 ^ (Nat.card Y).factorization 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hP⟩ := RankOneRecog.isSylowTwoOf_iff_exists.mp hS
  have hPS : (P : Subgroup ↥K) = S.subgroupOf K := by
    rw [← hP]
    exact (Subgroup.comap_map_eq_self_of_injective K.subtype_injective _).symm
  rw [← hPS]
  exact Sylow.card_eq_multiplicity (Sylow.mapSurjective hαs P)

namespace Setup

variable (S : Setup T L I)
include S

variable {S} {e : IntMod (fsuV T I) S.hV ≃* PairMod (ZMod 2)} {θ : G}

theorem mem_centralizer_of_comm_th (hc : S.Coord θ e) {t : G} (htM : t ∈ fsuM T L)
    (ht0 : t ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
      Subgroup G) : Set G)) {k : ℕ} (htk : t ^ 2 ^ k = 1)
    (htθ : t * θ * t⁻¹ * θ⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G)) :
    t ∈ Subgroup.centralizer (fsuV T I : Set G) := by
  set X := fsuM T L ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
    Subgroup G) : Set G) with hX
  have hXM : X ≤ fsuM T L := inf_le_left
  have hX1 : X ≤ Subgroup.centralizer ({S.vec e a1} : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_a1_mem_V0 hc)))
  obtain ⟨φ, hφ⟩ := exists_stabHom hc hXM hX1
  set χ : ↥X →* GL (Fin 2) (ZMod 2) := blkHom.comp φ with hχ
  have hcent : ∀ x : ↥X, χ x = 1 → (x : G) ∈ Subgroup.centralizer (fsuV T I : Set G) := by
    intro x hx
    have hb : blk (φ x : SL32) = 1 := by
      have h1 : (χ x : Matrix (Fin 2) (Fin 2) (ZMod 2)) = 1 := by rw [hx]; rfl
      rwa [hχ, MonoidHom.comp_apply, coe_blkHom] at h1
    exact mem_centralizer_of_blk (S.hMN (hXM x.2)) (φ x).2 hb (hφ x).symm
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (vec_b1_mem_V0 hc)) x.2.2)
  have hθX : θ ∈ X := ⟨S.L_le_fsuM hc.mem, Subgroup.mem_centralizer_iff.mpr fun v hv =>
    Subgroup.mem_centralizer_singleton_iff.mp hv.2⟩
  have htX : t ∈ X := ⟨htM, ht0⟩
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
  have hmem : t * θ * t⁻¹ * θ⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem (X.mul_mem htX hθX) (X.inv_mem htX)) (X.inv_mem hθX)
  have hχc : χ ⟨_, hmem⟩ = 1 := by
    have h1 : φ ⟨_, hmem⟩ = 1 := by
      apply Subtype.ext
      apply SL3One.rho_injective
      rw [hφ ⟨_, hmem⟩, OneMemClass.coe_one, map_one]
      have h2 := (convI_eq_one_iff S.hV ⟨_, S.hMN (hXM hmem)⟩).mpr htθ
      rw [h2, map_one]
      rfl
    rw [hχ, MonoidHom.comp_apply, h1, map_one]
  have e1 : (⟨_, hmem⟩ : ↥X) = ⟨t, htX⟩ * ⟨θ, hθX⟩ * (⟨t, htX⟩ : ↥X)⁻¹ * (⟨θ, hθX⟩ : ↥X)⁻¹ :=
    rfl
  rw [e1, map_mul, map_mul, map_mul, map_inv, map_inv] at hχc
  have hcomm : χ ⟨θ, hθX⟩ * χ ⟨t, htX⟩ = χ ⟨t, htX⟩ * χ ⟨θ, hθX⟩ := by
    have h1 : χ ⟨t, htX⟩ * χ ⟨θ, hθX⟩ = χ ⟨θ, hθX⟩ * χ ⟨t, htX⟩ := by
      calc χ ⟨t, htX⟩ * χ ⟨θ, hθX⟩
          = (χ ⟨t, htX⟩ * χ ⟨θ, hθX⟩ * (χ ⟨t, htX⟩)⁻¹ * (χ ⟨θ, hθX⟩)⁻¹) *
            (χ ⟨θ, hθX⟩ * χ ⟨t, htX⟩) := by group
        _ = χ ⟨θ, hθX⟩ * χ ⟨t, htX⟩ := by rw [hχc, one_mul]
    exact h1.symm
  have h3 := gl2_pow_three_of_comm _ _ hχθ3 hχθ1 hcomm
  have h2k : χ ⟨t, htX⟩ ^ 2 ^ k = 1 := by
    rw [← map_pow]
    have : (⟨t, htX⟩ : ↥X) ^ 2 ^ k = 1 := Subtype.ext (by simpa using htk)
    rw [this, map_one]
  exact hcent ⟨t, htX⟩ (eq_one_of_pow_three_of_pow_two_pow h3 h2k)

namespace MinConf

variable {Vp H : Subgroup G} (C : S.MinConf θ e Vp H)
include C

theorem pCoreOf_le_centralizer (hF : CharTwo H) {K : Subgroup G} (hK : K ∈ cComp H) :
    pCoreOf 2 K ≤ Subgroup.centralizer (fsuV T I : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hred⟩ := C.isTwoReduced_U hF
  have hOH := hred.2.2.2 _ (pCoreOf_le 2 H) (le_normalizer_pCoreOf 2 H) fun d hd => by
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 H ⟨d, hd⟩
    refine ⟨n, ?_⟩
    have h1 : d ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    rw [h1]
    exact one_mem _
  exact (CFSG.Quasithin.A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)).trans
    (hOH.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr C.V_le_U)))

theorem false_of_central (h443 : Stmt4_4_3Orbit') (hC24a : ASC24One G) (hF : CharTwo H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hKq : CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K))
    (hKM : ¬ K ≤ fsuM T L) {z : G} (hzK : z ∈ K) (hzM : z ∈ fsuM T L) (hzo : Odd (orderOf z))
    (hz1 : z ∉ pCoreOf 2 K) (hz : ∀ k ∈ K, k * z * k⁻¹ * z⁻¹ ∈ pCoreOf 2 K) : False := by
  have hc := C.conf.hc
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hO2V := C.pCoreOf_le_centralizer hF hK
  by_cases hzV : z ∈ Subgroup.centralizer (fsuV T I : Set G)
  · have hB1 : Subgroup.zpowers z ≠ ⊥ := by
      intro h
      apply hz1
      have h1 : z = 1 := by
        have h' := Subgroup.mem_zpowers z
        rw [h, Subgroup.mem_bot] at h'
        exact h'
      rw [h1]
      exact one_mem _
    have hN := S.normalizer_le h443 ((Subgroup.zpowers_le).mpr hzM)
      ((Subgroup.zpowers_le).mpr hzV) hB1 (isMulCommutative_zpowers z)
      (by rw [Nat.card_zpowers]; exact hzo)
    apply hKM
    intro k hk
    obtain ⟨o, ho, hok⟩ := exists_mem_normalizer_zpowers hzK hzo hz hk
    have h1 : o * k ∈ fsuM T L := hN hok
    have h2 : o⁻¹ ∈ fsuM T L := (fsuM T L).inv_mem (C.pCoreOf_le_fsuM hK ho)
    have h3 := (fsuM T L).mul_mem h2 h1
    simpa using h3
  · have hz0 : z ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
        Subgroup G) : Set G) := by
      have h1 := C.conf.hHG (hKH hzK)
      rwa [C.hVp] at h1
    obtain ⟨m, hm⟩ := exists_pow_of_odd hc hzM hz0 hzo hzV
    apply C.not_inf_le_Q h443 hC24a hF hK hKq hKM
    intro t ht
    obtain ⟨⟨htT, htVp⟩, htK⟩ := ht
    refine ⟨htT, ?_⟩
    have htM : t ∈ fsuM T L := S.T_le_fsuM htT
    have ht0 : t ∈ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer ({θ} : Set G) :
        Subgroup G) : Set G) := by rwa [C.hVp] at htVp
    obtain ⟨k, hk⟩ := C.conf.sylH.2.1 ⟨t, ⟨htT, htVp⟩⟩
    have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    refine mem_centralizer_of_comm_th hc htM ht0 htk ?_
    set c := θ * (z ^ m)⁻¹ with hcdef
    have hcV : c ∈ Subgroup.centralizer (fsuV T I : Set G) := hm
    have htN : t ∈ Subgroup.normalizer (fsuV T I : Set G) := S.hMN htM
    have htC : t * c * t⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) :=
      conj_mem_centralizer htN hcV
    have hzt : t * z ^ m * t⁻¹ * (z ^ m)⁻¹ ∈ Subgroup.centralizer (fsuV T I : Set G) :=
      hO2V (conj_pow_mul_inv_mem hzK hz htK m)
    have e : t * θ * t⁻¹ * θ⁻¹ = (t * c * t⁻¹) * (t * z ^ m * t⁻¹ * (z ^ m)⁻¹) * c⁻¹ := by
      rw [hcdef]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ htC hzt) (Subgroup.inv_mem _ hcV)

end MinConf

end Setup

end CFSG.Quasithin.H13.Sec77
