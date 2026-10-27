module

public import CFSG.Quasithin.H13.L32A767q
public import CFSG.Quasithin.H13.L32A767o
public import CFSG.Quasithin.H13.L32A767p

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType
open scoped MatrixGroups commutatorElement IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem eq_bot_of_perfect_of_le {K R : Subgroup G} (hKR : K ≤ R) (hR : IsPGroup 2 R)
    (hK : ⁅K, K⁆ = K) : K = ⊥ := by
  have h1 := B1Red.perfect_le_oTwoUpper' (le_refl K) (Subgroup.isPerfect_iff.mpr hK)
  refine eq_bot_iff.mpr (h1.trans ((Subgroup.closure_le _).mpr ?_))
  rintro x ⟨hxK, hodd⟩
  obtain ⟨n, hn⟩ := hR ⟨x, hKR hxK⟩
  have hx2 : x ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have h2 : orderOf x = 1 := Nat.Coprime.eq_one_of_dvd
    (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd)) (orderOf_dvd_of_pow_eq_one hx2)
  rw [orderOf_eq_one_iff] at h2
  rw [h2]
  exact (⊥ : Subgroup G).one_mem

theorem relIndex_eq_relIndex_sup {R K : Subgroup G}
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) : R.relIndex K = R.relIndex (R ⊔ K) := by
  have e1 := L32NSet14.card_sup_mul_card_inf hRK
  have e2 := Subgroup.relIndex_mul_card R K
  have e3 := Subgroup.relIndex_mul_card R (R ⊔ K)
  rw [inf_eq_left.mpr le_sup_left] at e3
  have hpos : 0 < Nat.card ↥(R ⊓ K) * Nat.card ↥R := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc R.relIndex K * (Nat.card ↥(R ⊓ K) * Nat.card ↥R)
      = (R.relIndex K * Nat.card ↥(R ⊓ K)) * Nat.card ↥R := by ring
    _ = Nat.card ↥(R ⊔ K) * Nat.card ↥(R ⊓ K) := by rw [e2, e1, mul_comm]
    _ = R.relIndex (R ⊔ K) * (Nat.card ↥(R ⊓ K) * Nat.card ↥R) := by rw [← e3]; ring

theorem mem_dK_of_odd (h : Hyp147 G T L V) (h63 : Thm14_7_63) {y : G}
    (hy : y ∈ dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hodd : Odd (orderOf y)) :
    y ∈ dK T V := by
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hRD : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (dK T V : Set G) :=
    (hRT.trans ((T_le_hz h h63).trans (le_normalizer_oTwoUpper _))).trans mK_le_normalizer_dK
  rw [sup_comm, ← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRD] at hy
  obtain ⟨r, hr, d, hd, rfl⟩ := hy
  obtain ⟨d', hd', e⟩ := pow_mul_mem_of_le_normalizer (hRD hr) hd (orderOf (r * d))
  rw [pow_orderOf_eq_one] at e
  have hrn : r ^ orderOf (r * d) ∈ dK T V := by
    rw [eq_inv_of_mul_eq_one_left e.symm]
    exact inv_mem hd'
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 _) ⟨r, hr⟩
  have hr2 : r ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
  have hcop : Nat.Coprime (orderOf (r * d)) (orderOf r) :=
    Nat.Coprime.coprime_dvd_right (orderOf_dvd_of_pow_eq_one hr2)
      (Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hodd))
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  have hrD : r ∈ dK T V := hm ▸ pow_mem hrn m
  exact mul_mem hrD hd

theorem mem_cComp_dKT (h : Hyp147 G T L V) (h63 : Thm14_7_63) {K' : Subgroup G}
    (hK' : K' ∈ cComp (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))) :
    K' ∈ cComp (dK T V ⊔ T) := by
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hXN : dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ dK T V ⊔ T :=
    sup_le le_sup_left (hRT.trans le_sup_right)
  have hNX : dK T V ⊔ T ≤ Subgroup.normalizer
      ((dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) : Subgroup G) : Set G) :=
    sup_le (le_sup_left.trans Subgroup.le_normalizer) (T_le_normalizer_dKR1 h h63)
  refine ⟨hK'.1, hK'.2.1, A3.subnormal_trans hK'.2.2.1 (A3.subnormal_of_normal hXN
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hXN).mpr hNX)), ?_⟩
  intro J hJK hJ1 hJp hJN
  exact hK'.2.2.2 J hJK hJ1 hJp
    (A3.subnormal_of_le_of_le hJN ((le_of_lt hJK).trans (A3.subnormal_le hK'.2.2.1)) hXN)

theorem pCoreOf_dKT_ne_bot (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63) :
    pCoreOf 2 (dK T V ⊔ T) ≠ ⊥ := by
  have hDT : dK T V ⊔ T ≤ mK T V :=
    sup_le (fun d hd => hd.1) ((T_le_hz h h63).trans (le_normalizer_oTwoUpper _))
  have hO : pCoreOf 2 (kz T V) ≤ pCoreOf 2 (dK T V ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 (pCoreOf_kz_le_dK.trans le_sup_left)
      (hDT.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  exact fun h0 => pCoreOf_kz_ne_bot h hMod h63 (le_bot_iff.mp (h0 ▸ hO))

theorem faithfulLocal_of_mem_cComp (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) (h36 : A36ForSQTK) {K' : Subgroup G}
    (hK' : K' ∈ cComp (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))) :
    quasithinIsFaithfulLocal T K' := by
  obtain ⟨S, hS⟩ := exists_sylow_of_quasithinIsSylowTwo h.fsu.sylow
  have hInH : InH (S : Subgroup G) (dK T V ⊔ T) :=
    ⟨hS ▸ le_sup_right, pCoreOf_dKT_ne_bot h hMod h63⟩
  have hTFAE := lemma_1_2_10_of_a36 h.fsu.qtke h.fsu.simple h.fsu.nonabelian h36 S hInH
    (mem_cComp_dKT h h63 hK')
  have hchar : CharTwo (dK T V ⊔ T) := charTwo_of_inH h.fsu.qtke.2.1 S hInH
  have hred := (conjClosure_isTwoReducedIn_of_charTwo (isSylowTwoOf_of_le h le_sup_right) hchar
    (inf_le_right : fsuV1 T V ≤ quasithinOmegaOneCenter T)).2.2
  have hVK : ⁅conjClosure (fsuV1 T V) (dK T V ⊔ T), K'⁆ ≠ ⊥ := by
    intro hb
    refine hK'.1 (eq_bot_of_perfect_of_le (R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ?_
      (pCoreOf_isPGroup 2 _) hK'.2.1)
    intro x hx
    refine inf_hz_le_R1 h hMod h63 ⟨A3.subnormal_le hK'.2.2.1 hx,
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have h1 : ⁅v, x⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator (le_conjClosure (fsuV1 T V) (dK T V ⊔ T) hv) hx
      rwa [hb, Subgroup.mem_bot] at this
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have h2 : ∃ W, IsTwoReducedIn (dK T V ⊔ T) W ∧ ⁅W, K'⁆ ≠ ⊥ := ⟨_, hred, hVK⟩
  have hLf : quasithinIsFaithfulLocal (S : Subgroup G) K' := (hTFAE.out 1 2).mpr h2
  rwa [hS] at hLf

theorem sbar_facts {R X K' : Subgroup G} (hSX : IsSylowTwoOf R X) (hKX : K' ≤ X)
    (hRK : R ≤ Subgroup.normalizer (K' : Set G)) (hOR : pCoreOf 2 K' ≤ R) {Q : Type} [Group Q]
    (π : ↥K' →* Q) (hπs : Function.Surjective π) (hπk : π.ker = (pCoreOf 2 K').subgroupOf K') :
    (∀ k : ↥K', π k ∈ (R.subgroupOf K').map π ↔ (k : G) ∈ R) ∧
      IsPGroup 2 ((R.subgroupOf K').map π) ∧ ¬ 2 ∣ ((R.subgroupOf K').map π).index ∧
      ∀ r : ↥R, ∀ s ∈ (R.subgroupOf K').map π,
        autHom π hπs hπk (Subgroup.inclusion hRK r) s ∈ (R.subgroupOf K').map π := by
  have hS : ∀ k : ↥K', π k ∈ (R.subgroupOf K').map π ↔ (k : G) ∈ R := by
    intro k
    constructor
    · rintro ⟨x, hx, hxk⟩
      have hker : x⁻¹ * k ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxk, inv_mul_cancel]
      rw [hπk, Subgroup.mem_subgroupOf] at hker
      have := mul_mem (Subgroup.mem_subgroupOf.mp hx) (hOR hker)
      simpa using this
    · intro hk
      exact ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  refine ⟨hS, (hSX.2.1.comap_of_injective K'.subtype Subtype.val_injective).map π, ?_, ?_⟩
  · have hidx : ¬ 2 ∣ R.relIndex K' := by
      rw [relIndex_eq_relIndex_sup hRK]
      intro h2
      exact hSX.2.2 (h2.trans (Dvd.intro _ (Subgroup.relIndex_mul_relIndex R (R ⊔ K') X
        le_sup_left (sup_le hSX.1 hKX))))
    exact fun h2 => hidx (h2.trans (Subgroup.index_map_dvd _ hπs))
  · rintro r s ⟨x, hx, rfl⟩
    rw [autHom_apply]
    refine (hS _).mpr ?_
    rw [coe_conjOn]
    exact mul_mem (mul_mem r.2 (Subgroup.mem_subgroupOf.mp hx)) (inv_mem r.2)

theorem false_of_normalizing_cfg (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {K' : Subgroup G}
    (hKX : K' ≤ dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) {Q : Type} [Group Q] [Finite Q]
    (π : ↥K' →* Q) (hπs : Function.Surjective π) (hπk : π.ker = (pCoreOf 2 K').subgroupOf K')
    (hRK : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (K' : Set G))
    (hOR : pCoreOf 2 K' ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) {S W : Subgroup Q}
    (hS : ∀ k : ↥K', π k ∈ S ↔ (k : G) ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hWS : W ≤ S)
    {c : Q} (hcW : c ∈ Subgroup.normalizer (W : Set Q)) (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hRW : ∀ r : ↥(pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)), ∀ w ∈ W,
      autHom π hπs hπk (Subgroup.inclusion hRK r) w ∈ W)
    (hcrit : ∀ a b : ↥(pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)),
      autHom π hπs hπk (Subgroup.inclusion hRK a) ∉ W.map MulAut.conj →
      autHom π hπs hπk (Subgroup.inclusion hRK b) ∉ W.map MulAut.conj →
      autHom π hπs hπk (Subgroup.inclusion hRK (a⁻¹ * b)) ∈ W.map MulAut.conj) : False := by
  obtain ⟨P, hPR, hRP, hidx, y, hyK, hy3, hy1, hyP⟩ :=
    exists_normalizing_odd π hπs hπk hRK hOR hS hWS hcW hc3 hc1 hRW hcrit
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hodd : Odd (orderOf y) := by
    rw [orderOf_eq_prime hy3 hy1]
    decide
  exact hy1 (eq_one_of_normalizes h hMod h63 h1222 h1332 h1334 hF hPR hRP hidx
    (mem_dK_of_odd h h63 (hKX hyK) hodd) hyP hodd)

theorem false_of_a5 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {K' : Subgroup G}
    (hKX : K' ≤ dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hRK : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (K' : Set G))
    (hOR : pCoreOf 2 K' ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (e5 : ↥K' ⧸ CFSG.pCore 2 ↥K' ≃* alternatingGroup (Fin 5)) : False := by
  have hSX := isSylowTwoOf_R1_dK h hMod h63
  set π : ↥K' →* alternatingGroup (Fin 5) :=
    e5.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥K')) with hπ
  have hπs : Function.Surjective π := e5.surjective.comp (QuotientGroup.mk'_surjective _)
  have hπk : π.ker = (pCoreOf 2 K').subgroupOf K' := by
    rw [pCoreOf_subgroupOf_self]
    ext x
    rw [MonoidHom.mem_ker, hπ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  obtain ⟨hS, hS2, hSi, hRS⟩ := sbar_facts hSX hKX hRK hOR π hπs hπk
  obtain ⟨⟨c, hcN, hc3, hc1⟩, h2el⟩ := a5_sylow_facts hS2 hSi
  have hinn : ∀ r : ↥(pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)), ∀ q,
      autHom π hπs hπk (Subgroup.inclusion hRK r) = MulAut.conj q →
        q ∈ ((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).subgroupOf K').map π := by
    intro r q hq
    have hqN : q ∈ Subgroup.normalizer
        ((((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).subgroupOf K').map π : Subgroup _) :
          Set (alternatingGroup (Fin 5))) :=
      mem_normalizer_of_forall_conj_mem fun s hs => by
        have := hRS r s hs
        rwa [hq, MulAut.conj_apply] at this
    obtain ⟨n, hn⟩ := hSX.2.1 r
    have hq2 : q ^ 2 ^ n = 1 := by
      apply conj_injective_a5
      have e : (MulAut.conj q) ^ 2 ^ n = 1 := by
        rw [← hq, ← map_pow, ← map_pow, hn, map_one, map_one]
      rw [map_pow, e, map_one]
    exact h2el q hqN (a5_pow_four hq2)
  refine false_of_normalizing_cfg h hMod h63 h1222 h1332 h1334 hF hKX π hπs hπk hRK hOR hS le_rfl
    hcN hc3 hc1 hRS fun a b ha hb => ?_
  have hrange : (MulAut.conj : alternatingGroup (Fin 5) →* MulAut _).range.index = 2 :=
    index_range_conj_a5
  have hna : autHom π hπs hπk (Subgroup.inclusion hRK a) ∉
      (MulAut.conj : alternatingGroup (Fin 5) →* MulAut _).range := by
    rintro ⟨q, hq⟩
    exact ha ⟨q, hinn a q hq.symm, hq⟩
  have hnb : autHom π hπs hπk (Subgroup.inclusion hRK b) ∉
      (MulAut.conj : alternatingGroup (Fin 5) →* MulAut _).range := by
    rintro ⟨q, hq⟩
    exact hb ⟨q, hinn b q hq.symm, hq⟩
  have hab : autHom π hπs hπk (Subgroup.inclusion hRK (a⁻¹ * b)) ∈
      (MulAut.conj : alternatingGroup (Fin 5) →* MulAut _).range := by
    simp only [map_mul, map_inv]
    exact (Subgroup.mul_mem_iff_of_index_two hrange).mpr
      (iff_of_false (by rwa [inv_mem_iff]) hnb)
  obtain ⟨q, hq⟩ := hab
  exact ⟨q, hinn _ q hq.symm, hq⟩

omit [Finite G] in
theorem repV_eq_repV_inclusion {K V : Subgroup G} (hKV : K ≤ Subgroup.normalizer (V : Set G))
    {n : ℕ} (e : ↥V ≃* Multiplicative (Fin n → ZMod 2)) (k : ↥K) :
    repV hKV e k = repV (le_refl _) e (Subgroup.inclusion hKV k) := rfl

theorem false_of_sl3 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {K' : Subgroup G}
    (hKX : K' ≤ dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hRK : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (K' : Set G))
    (hOR : pCoreOf 2 K' ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hTK : T ≤ Subgroup.normalizer (K' : Set G))
    (h3 : LieModel (↥K' ⧸ CFSG.pCore 2 ↥K') .PSL 3 2 1) {VK : Subgroup G}
    (hIrr : IsIrrPlusIn K' (reducedAggregate (K' ⊔ T)) T VK)
    (hTV : T ≤ Subgroup.normalizer (VK : Set G)) [IsMulCommutative ↥VK]
    (hmod : Modules13_3_2 K' VK) : False := by
  have hSX := isSylowTwoOf_R1_dK h hMod h63
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hRV : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ Subgroup.normalizer (VK : Set G) :=
    hRT.trans hTV
  have hKV : K' ≤ Subgroup.normalizer (VK : Set G) := hIrr.2.2.1
  have hne : ¬ K' ≤ Subgroup.centralizer (VK : Set G) := by
    intro hle
    have h1 : ⁅VK, K'⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mp hle)
    exact hIrr.2.1 (hIrr.2.2.2.1.symm.trans h1)
  obtain ⟨hnat, -⟩ := modules13_3_2_of_L32 h3 hKV hne hmod
  obtain ⟨hcard, hsq⟩ := card_and_sq_of_binaryNaturalSL hnat
  have hAut : autOn K' VK = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    refine le_antisymm (Nat.card_le_card_of_injective _ Subtype.val_injective) ?_
    rw [card_eq_of_binaryNaturalSL hnat (by norm_num)]
    exact card_mulAut_le (fun v hv => by simpa using congrArg Subtype.val (hsq ⟨v, hv⟩)) hcard
      (by norm_num)
  obtain ⟨e₀⟩ := Vol2.Ch10.SecA.nonempty_mulEquiv_pi_of_sq_eq_one hsq hcard
  have hπs : Function.Surjective (repV hKV e₀) := repV_surjective hKV e₀ hAut
  have hπk : (repV hKV e₀).ker = (pCoreOf 2 K').subgroupOf K' := by
    obtain ⟨θ₀, hθ₀, hker₀⟩ := exists_surj_SL32_of_lieModel h3
    have hO : pCoreOf 2 K' ≤ pCoreOf 2 (K' ⊔ T) :=
      le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K').trans le_sup_left)
        (sup_le (le_normalizer_pCoreOf 2 K') (hTK.trans (normalizer_le_normalizer_pCoreOf 2 K')))
        (pCoreOf_isPGroup 2 K')
    have hle : (pCoreOf 2 K').subgroupOf K' ≤ (repV hKV e₀).ker := by
      rw [repV_ker]
      intro x hx
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact ((U3.mem_reducedAggregate' (hIrr.1 hv)).2.1 x (hO hx)).symm
    have hcard168 : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) = 168 := SL3.card_SL3
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (repV hKV e₀).ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup θ₀.ker
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hπs).toEquiv,
      hcard168] at h1
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective θ₀ hθ₀).toEquiv,
      hcard168, hker₀] at h2
    exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm
  obtain ⟨hS, hS2, hSi, hRS⟩ := sbar_facts hSX hKX hRK hOR (repV hKV e₀) hπs hπk
  obtain ⟨W, hWS, hSW, hWi, ⟨c, hcW, hc3, hc1⟩, h2el⟩ := sl3_sylow_facts hS2 hSi
  set ρ := repV (le_refl (Subgroup.normalizer (VK : Set G))) e₀ with hρ
  have hΦ : ∀ r : ↥(pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)),
      autHom (repV hKV e₀) hπs hπk (Subgroup.inclusion hRK r) =
        MulAut.conj (ρ ⟨r, hRV r.2⟩) := by
    intro r
    refine MulEquiv.ext fun A => ?_
    obtain ⟨x, rfl⟩ := hπs A
    rw [autHom_apply, MulAut.conj_apply, repV_eq_repV_inclusion hKV e₀ (conjOn K' _ x),
      repV_eq_repV_inclusion hKV e₀ x]
    have e2 : Subgroup.inclusion hKV (conjOn K' (Subgroup.inclusion hRK r) x) =
        (⟨r, hRV r.2⟩ : ↥(Subgroup.normalizer (VK : Set G))) * Subgroup.inclusion hKV x *
          (⟨r, hRV r.2⟩ : ↥(Subgroup.normalizer (VK : Set G)))⁻¹ :=
      Subtype.ext (coe_conjOn K' _ x)
    rw [e2, map_mul, map_mul, map_inv]
  have hρS : ∀ r : ↥(pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)),
      ρ ⟨r, hRV r.2⟩ ∈ ((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).subgroupOf K').map (repV hKV e₀) := by
    intro r
    have hN : ρ ⟨r, hRV r.2⟩ ∈ Subgroup.normalizer
        ((((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).subgroupOf K').map (repV hKV e₀) :
          Subgroup _) : Set (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2))) :=
      mem_normalizer_of_forall_conj_mem fun s hs => by
        have := hRS r s hs
        rwa [hΦ r, MulAut.conj_apply] at this
    obtain ⟨n, hn⟩ := hSX.2.1 r
    have h8 : ρ ⟨r, hRV r.2⟩ ^ 8 = 1 := by
      refine sl3_pow_eight (n := n) ?_
      have e : (⟨r, hRV r.2⟩ : ↥(Subgroup.normalizer (VK : Set G))) ^ 2 ^ n = 1 :=
        Subtype.ext (by simpa using congrArg Subtype.val hn)
      rw [← map_pow, e, map_one]
    exact h2el _ hN h8
  refine false_of_normalizing_cfg h hMod h63 h1222 h1332 h1334 hF hKX (repV hKV e₀) hπs hπk hRK
    hOR hS hWS hcW hc3 hc1 (fun r w hw => ?_) fun a b ha hb => ?_
  · rw [hΦ r, MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp (hSW (hρS r)) w).mp hw
  · have ha' : ρ ⟨a, hRV a.2⟩ ∉ W := fun hw => ha ⟨_, hw, (hΦ a).symm⟩
    have hb' : ρ ⟨b, hRV b.2⟩ ∉ W := fun hw => hb ⟨_, hw, (hΦ b).symm⟩
    have hab : (ρ ⟨a, hRV a.2⟩)⁻¹ * ρ ⟨b, hRV b.2⟩ ∈ W := by
      have hidx2 : (W.subgroupOf
          (((pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)).subgroupOf K').map (repV hKV e₀))).index = 2 :=
        hWi
      have := (Subgroup.mul_mem_iff_of_index_two hidx2
        (a := ⟨(ρ ⟨a, hRV a.2⟩)⁻¹, inv_mem (hρS a)⟩) (b := ⟨ρ ⟨b, hRV b.2⟩, hρS b⟩)).mpr
        (iff_of_false (by rw [Subgroup.mem_subgroupOf]; simpa using ha')
          (by rw [Subgroup.mem_subgroupOf]; exact hb'))
      rw [Subgroup.mem_subgroupOf] at this
      simpa using this
    refine ⟨_, hab, ?_⟩
    rw [hΦ (a⁻¹ * b), ← map_inv, ← map_mul]
    rfl

theorem false_of_mem_cComp (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h36 : A36ForSQTK) (h1434 : Lemma1434One)
    {K' : Subgroup G} (hK' : K' ∈ cComp (dK T V ⊔ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))) :
    False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hSX := isSylowTwoOf_R1_dK h hMod h63
  have hRT : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ≤ T :=
    EscapingLocal.pCoreOf_le_of_isSylowTwoOf (isSylowTwoOf_of_le h le_sup_right)
  have hKX := A3.subnormal_le hK'.2.2.1
  have hLf := faithfulLocal_of_mem_cComp h hMod h63 h36 hK'
  have hL := h1332 G T L h.hyp.h13 K' hLf
  have hTK : T ≤ Subgroup.normalizer (K' : Set G) := hL.2.1.1
  have hOR : pCoreOf 2 K' ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) :=
    (A4.pCoreOf_le_of_subnormal 2 hK'.2.2.1).trans
      (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hSX)
  rcases h1434 G T L h.hyp K' hLf with he5 | h3
  · obtain ⟨e5⟩ := he5
    exact false_of_a5 h hMod h63 h1222 h1332 h1334 hF hKX (hRT.trans hTK) hOR e5
  · obtain ⟨VK, hIrr⟩ := hL.2.2.1.1
    obtain ⟨-, hTV, -, hc, hmod⟩ := hL.2.2.1.2 VK hIrr
    exact false_of_sl3 h hMod h63 h1222 h1332 h1334 hF hKX (hRT.trans hTK) hOR hTK h3 hIrr hTV
      hmod

end CFSG.Quasithin.H13.L32A
