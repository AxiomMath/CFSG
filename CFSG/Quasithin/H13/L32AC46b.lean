module

public import CFSG.Quasithin.H13.L32AC42k
public import CFSG.Quasithin.Recognition.Kleidman.F204.W2FFOrder
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Quasithin.H13.L32AC52c
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.Quasithin.Vol2.Ch11SecA11Setup

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

omit [Finite G] in
theorem commutator_le_of_le_normalizer {U K : Subgroup G}
    (hUK : U ≤ Subgroup.normalizer (K : Set G)) : ⁅U, K⁆ ≤ K := by
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have h1 : u * k * u⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hUK hu) k).mp hk
  rw [commutatorElement_def]
  exact K.mul_mem h1 (K.inv_mem hk)

omit [Finite G] in
theorem commutator_le_left_of_le_normalizer {U K : Subgroup G}
    (hKU : K ≤ Subgroup.normalizer (U : Set G)) : ⁅U, K⁆ ≤ U := by
  rw [Subgroup.commutator_le]
  intro u hu k hk
  have h1 : k * u⁻¹ * k⁻¹ ∈ U := (Subgroup.mem_normalizer_iff.mp (hKU hk) _).mp (inv_mem hu)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc k]
  exact U.mul_mem hu h1

omit [Finite G] in
theorem le_normalizer_commutator_of {X U K : Subgroup G}
    (hXU : X ≤ Subgroup.normalizer (U : Set G)) (hXK : X ≤ Subgroup.normalizer (K : Set G)) :
    X ≤ Subgroup.normalizer ((⁅U, K⁆ : Subgroup G) : Set G) := by
  intro h hh
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXU hh),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hXK hh)]

omit [Finite G] in
theorem commutator_le_pCoreOf {K : Subgroup G} (hKH : K ≤ H)
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) (hF : HypF98 T V L (fsuV1 T V) V H) :
    ⁅conjClosure V H, K⁆ ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hUH : conjClosure V H ≤ H := conjClosure_le fun h hh v hv =>
    H.mul_mem (H.mul_mem hh (hF.toHypF91.Vp_le_H hv)) (H.inv_mem hh)
  have hEK := commutator_le_of_le_normalizer (hUH.trans hKn)
  have hKE := le_normalizer_commutator_of (hKH.trans (le_normalizer_conjClosure V H))
    (Subgroup.le_normalizer (H := K))
  have hEU := commutator_le_left_of_le_normalizer (hKH.trans (le_normalizer_conjClosure V H))
  refine le_pCoreOf_of_le_normalizer 2 hEK hKE fun g => ⟨1, Subtype.ext ?_⟩
  have := hF.F911_3.2 g (hEU g.2)
  simpa using this

theorem sixteen_le_card_commutator {K : Subgroup G} (hK : K ∈ cComp H)
    (hF : HypF98 T V L (fsuV1 T V) V H) (hA5 : IsAlt 5 (cStar K)) :
    16 ≤ Nat.card (⁅conjClosure V H, K⁆ : Subgroup G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  set U := conjClosure V H with hU
  set E := ⁅U, K⁆ with hE
  have hKH := le_of_mem_cComp hK
  have hKU : K ≤ Subgroup.normalizer (U : Set G) := hKH.trans (le_normalizer_conjClosure V H)
  have hEU : E ≤ U := commutator_le_left_of_le_normalizer hKU
  have hE2 : ∀ a ∈ E, a * a = 1 := fun a ha => by
    have := hF.F911_3.2 a (hEU ha)
    rwa [pow_two] at this
  have hKE : K ≤ Subgroup.normalizer (E : Set G) :=
    le_normalizer_commutator_of hKU (Subgroup.le_normalizer (H := K))
  have h60 : Nat.card (cStar K) = 60 := card_of_isAlt_five hA5
  have hK60 : 60 ∣ Nat.card K := by
    rw [← h60]
    exact Subgroup.card_quotient_dvd_card _
  by_contra h16
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 5
    (dvd_trans (by norm_num : 5 ∣ 60) hK60)
  have hx5 : orderOf (x : G) = 5 := by rw [Subgroup.orderOf_coe, hx]
  have hxE : ∀ v ∈ E, Commute (x : G) v := by
    intro v hv
    by_contra hnot
    refine h16 (Kleidman.F204.sixteen_le_card_of_five hE2 (hKE x.2) (fun w _ => ?_) v hv hnot)
    rw [← hx5, pow_orderOf_eq_one]
    exact Commute.one_left w
  set C := K ⊓ Subgroup.centralizer (E : Set G) with hC
  have hCK : C ≤ K := inf_le_left
  have hKC : K ≤ Subgroup.normalizer (C : Set G) := by
    intro k hk
    refine Subgroup.mem_normalizer_fintype fun c hc => ⟨K.mul_mem (K.mul_mem hk hc.1)
      (K.inv_mem hk), Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
    have he' : k⁻¹ * e * k ∈ E := by
      have := (Subgroup.mem_normalizer_iff.mp (hKE (K.inv_mem hk)) e).mp he
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hc.2 _ he'
    calc e * (k * c * k⁻¹) = k * ((k⁻¹ * e * k) * c) * k⁻¹ := by group
      _ = k * (c * (k⁻¹ * e * k)) * k⁻¹ := by rw [h1]
      _ = k * c * k⁻¹ * e := by group
  have hxC : (x : G) ∈ C :=
    ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun v hv => (hxE v hv).symm⟩
  set π := QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K) with hπ
  have hCn : (C.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCK).mpr hKC
  have hCbn : ((C.subgroupOf K).map π).Normal := hCn.map π (QuotientGroup.mk'_surjective _)
  have hsimple : IsSimpleGroup (cStar K) := by
    obtain ⟨e⟩ := hA5
    have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
    exact e.isSimpleGroup
  have hP2 : IsPGroup 2 (pCoreOf 2 K) := pCoreOf_isPGroup 2 K
  have hCtop : (C.subgroupOf K).map π = ⊤ := by
    have := hCbn
    rcases hsimple.eq_bot_or_eq_top_of_normal ((C.subgroupOf K).map π) with hbot | htop
    · exfalso
      have hmem : π x ∈ (C.subgroupOf K).map π := ⟨x, hxC, rfl⟩
      rw [hbot, Subgroup.mem_bot, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
        Subgroup.mem_subgroupOf] at hmem
      obtain ⟨k, hk⟩ := hP2 ⟨_, hmem⟩
      have h1 : (x : G) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have h2 := orderOf_dvd_of_pow_eq_one h1
      rw [hx5] at h2
      exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h2) (by norm_num)
    · exact htop
  have hKCP : K ≤ C ⊔ pCoreOf 2 K := by
    intro k hk
    have hmem : π ⟨k, hk⟩ ∈ (C.subgroupOf K).map π := by rw [hCtop]; exact Subgroup.mem_top _
    obtain ⟨c, hc, hce⟩ := Subgroup.mem_map.mp hmem
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf] at hce
    have e : k = (c : G) * ((c : G)⁻¹ * k) := by group
    rw [e]
    refine Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hc) ?_
    simpa using hce
  have hKeq : K = C := Vol2.Ch11.SecA.eq_of_le_sup_of_perfect hCK (perfect_of_mem_cComp hK) hP2
    ((pCoreOf_le 2 K).trans hKC) hKCP
  have hEK : ⁅E, K⁆ = ⊥ := by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
    exact hKeq.le.trans inf_le_right
  have h3 : ⁅⁅K, K⁆, U⁆ = ⊥ := Subgroup.commutator_commutator_eq_bot_of_rotate
    (by rw [Subgroup.commutator_comm K U]; exact hEK) hEK
  rw [perfect_of_mem_cComp hK, Subgroup.commutator_comm] at h3
  have hKO : K ≤ pCoreOf 2 H := by
    intro k hk
    rw [hF.toHypF91.pCoreOf_eq_centralizerMod]
    refine ⟨hKH hk, hF.toHypF91.H_normalizes_V₁ (hKH hk), fun u hu => ?_⟩
    have hc : k * u * k⁻¹ * u⁻¹ ∈ ⁅U, K⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hk hu
    rw [h3, Subgroup.mem_bot] at hc
    rw [hc]
    exact one_mem _
  have hK2 : IsPGroup 2 K := (pCoreOf_isPGroup 2 H).to_le hKO
  obtain ⟨m, hm⟩ := hK2.exists_card_eq
  rw [hm] at hK60
  have h3m : 3 ∣ 2 ^ m := dvd_trans (by norm_num) hK60
  exact absurd (Nat.Prime.dvd_of_dvd_pow (by norm_num) h3m) (by norm_num)

theorem fsuU_le_pCoreOf_g1 (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h : Hyp147 G T L V) : fsuU T V ≤ pCoreOf 2 (A6.g1 T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨hVe, -, -, -, -⟩ := hMod G T L V h.hyp h.fsu
  have : IsMulCommutative ↥V := hVe.1
  have : IsMulCommutative ↥(fsuU T V) := h.abelian
  have hVG : V ≤ A6.g1 T V := fun v hv => Subgroup.mem_normalizer_fintype fun w hw => by
    have hwV : w ∈ V := hw.1
    have h1 : v * w = w * v := congrArg Subtype.val (mul_comm (⟨v, hv⟩ : ↥V) ⟨w, hwV⟩)
    rw [h1, mul_inv_cancel_right]
    exact hw
  have hUG : fsuU T V ≤ A6.g1 T V := conjClosure_le fun g hg x hx =>
    (A6.g1 T V).mul_mem ((A6.g1 T V).mul_mem hg (hVG hx)) ((A6.g1 T V).inv_mem hg)
  have hcomm : ∀ x ∈ fsuU T V, ∀ y ∈ fsuU T V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥(fsuU T V)) ⟨y, hy⟩)
  have hsq := L32A.sq_eq_one_of_mem_conjClosure hVe.2 hcomm
  exact le_pCoreOf_of_le_normalizer 2 hUG (le_normalizer_conjClosure V _)
    fun g => ⟨1, Subtype.ext (by simpa using hsq g g.2)⟩

theorem borelOf_le_normalizer_V2 (hN1 : LieSylowOver3) (h29 : Thm14_7_29) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (S : Setting147 G T L V H) {K : Subgroup G}
    (hK : K ∈ cComp H) (hq : CFSG.IsQuasisimple (cStar K))
    (hKn : H ≤ Subgroup.normalizer (K : Set G)) {n : ℕ} (hn : 1 < n)
    (hLie : A315.IsLieChar2 n (cStar K ⧸ Subgroup.center (cStar K))) (hl1K : ¬ l1 T L V ≤ K)
    {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂) :
    borelOf K T ≤ Subgroup.normalizer (V₂ : Set G) := by
  classical
  have hKH := le_of_mem_cComp hK
  have hTH : T ≤ H := le_sup_right.trans S.hz.1.1
  have hOT : pCoreOf 2 H ≤ T := L32A.pCoreOf_le_of_le S.hyp hTH
  intro β hβ
  have hβK : β ∈ K := hβ.1
  have hβN : β ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G) := hβ.2
  set Q := ↥H ⧸ CFSG.pCore 2 ↥H with hQ
  set b : Q := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨β, hKH hβK⟩ with hb
  have hbB : b ∈ szB1 T H K := by
    refine ⟨Subgroup.mem_normalizer_fintype fun y hy => ?_, ⟨⟨β, hKH hβK⟩, hβK, rfl⟩⟩
    obtain ⟨t, htT, rfl⟩ := Subgroup.mem_map.mp hy.1
    obtain ⟨k, hkK, hke⟩ := Subgroup.mem_map.mp hy.2
    rw [Subgroup.mem_subgroupOf] at htT hkK
    have hkt : (t : G)⁻¹ * k ∈ pCoreOf 2 H := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hke
      have h2 := (CFSG.Open.pCore 2 ↥H).inv_mem hke
      refine ⟨_, h2, ?_⟩
      simp
    have hkT : (k : G) ∈ T := by
      have e : (k : G) = t * ((t : G)⁻¹ * k) := by group
      rw [e]
      exact T.mul_mem htT (hOT hkt)
    have hβk : β * k * β⁻¹ ∈ T ⊓ K :=
      (Subgroup.mem_normalizer_iff.mp hβN k).mp ⟨hkT, hkK⟩
    rw [← hke]
    refine ⟨⟨⟨β, hKH hβK⟩ * k * ⟨β, hKH hβK⟩⁻¹, hβk.1, ?_⟩,
      ⟨⟨β, hKH hβK⟩ * k * ⟨β, hKH hβK⟩⁻¹, hβk.2, ?_⟩⟩ <;>
      simp only [hb, map_mul, map_inv]
  obtain ⟨-, -, hβc⟩ := mem_trivSub_of_szB1 hN1 h29 h1222 h1332 h1334 S hK hq hKn hn hLie hl1K
    (β := ⟨β, hKH hβK⟩) hbB
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  have h1 := hβc v (hV2.2.1 hv)
  have e : β * v * β⁻¹ = (β * v * β⁻¹ * v⁻¹) * v := by group
  rw [e]
  exact V₂.mul_mem (hV2.1 h1) hv

end CFSG.Quasithin.H13.L32A.C
