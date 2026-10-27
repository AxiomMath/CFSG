module

public import CFSG.Quasithin.Recognition.St84.AppTree
public import CFSG.Quasithin.Recognition.St84.EdgeStab
public import CFSG.GroupTheory.PCore.InfPCoreOf

public section

namespace CFSG.Quasithin.St84

open CFSG.Open

theorem inf_pCoreOf_eq_pCoreOf {G : Type*} [Group G] {M L : Subgroup G}
    (hML : M ≤ L) (hnorm : L ≤ Subgroup.normalizer (M : Set G)) :
    M ⊓ pCoreOf 2 L = pCoreOf 2 M := by
  refine le_antisymm (CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hML) ?_
  ·
    have hp : IsPGroup 2 (pCoreOf 2 M) :=
      (CFSG.pCore_isPGroup (G := ↥M) (p := 2)).map M.subtype
    have hnorm' : L ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      hnorm.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (K := CFSG.pCore 2 M))
    have hN : ((pCoreOf 2 M).subgroupOf L).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hnorm'
    exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 M)
      (CFSG.LieType.BorelTits.le_pCoreOf (r := 2) ((CFSG.LieType.BorelTits.pCoreOf_le 2 M).trans hML)
        hN hp)

theorem pCore_quotient_mulEquiv_of_sup_pCoreOf {G : Type*} [Group G] {M L : Subgroup G}
    (hML : M ≤ L) (hnorm : L ≤ Subgroup.normalizer (M : Set G))
    (hsup : M ⊔ pCoreOf 2 L = L) :
    Nonempty (↥M ⧸ CFSG.pCore 2 ↥M ≃* ↥L ⧸ CFSG.pCore 2 ↥L) := by
  have hinf : M ⊓ pCoreOf 2 L = pCoreOf 2 M := inf_pCoreOf_eq_pCoreOf hML hnorm
  let φ : ↥M →* ↥L ⧸ CFSG.pCore 2 ↥L :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp (Subgroup.inclusion hML)
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have hmem : (l : G) ∈ M ⊔ pCoreOf 2 L := by rw [hsup]; exact l.2
    obtain ⟨m, hm, q, hq, hmq⟩ :=
      (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
        (H := M) (K := pCoreOf 2 L)
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 L).trans hnorm)).mp hmem
    have hqL : (⟨q, (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hq⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
      (Subgroup.mem_map_iff_mem L.subtype_injective).mp hq
    refine ⟨⟨m, hm⟩, ?_⟩
    show QuotientGroup.mk' (CFSG.pCore 2 ↥L) (Subgroup.inclusion hML ⟨m, hm⟩) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥L) l
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply]
    have hl : l = (⟨m, hML hm⟩ : ↥L) *
        ⟨q, (CFSG.LieType.BorelTits.pCoreOf_le 2 L) hq⟩ := by
      ext
      simpa using hmq
    rw [hl, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hqL, mul_one]
    rfl
  have hker : φ.ker = CFSG.pCore 2 ↥M := by
    ext m
    have h1 : (m : G) ∈ pCoreOf 2 L ↔ (Subgroup.inclusion hML m : ↥L) ∈ CFSG.pCore 2 ↥L := by
      have := (Subgroup.mem_map_iff_mem (K := CFSG.pCore 2 ↥L)
        (x := Subgroup.inclusion hML m) L.subtype_injective)
      simpa [pCoreOf] using this
    have h2 : (m : G) ∈ pCoreOf 2 M ↔ m ∈ CFSG.pCore 2 ↥M := by
      have := (Subgroup.mem_map_iff_mem (K := CFSG.pCore 2 ↥M)
        (x := m) M.subtype_injective)
      simpa [pCoreOf] using this
    have h3 : (m : G) ∈ pCoreOf 2 L ↔ (m : G) ∈ pCoreOf 2 M := by
      rw [← hinf]
      exact ⟨fun h => ⟨m.2, h⟩, fun h => h.2⟩
    rw [MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact h1.symm.trans (h3.trans h2)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective φ hφ)⟩

theorem pCoreOf_sup_pCoreOf {G : Type*} [Group G] {M K : Subgroup G}
    (hMK : M ≤ K) (hnorm : K ≤ Subgroup.normalizer (M : Set G)) :
    pCoreOf 2 (M ⊔ pCoreOf 2 K) = pCoreOf 2 K := by
  have hNK : M ⊔ pCoreOf 2 K ≤ K :=
    sup_le hMK (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
  have hKN : K ≤ Subgroup.normalizer ((M ⊔ pCoreOf 2 K : Subgroup G) : Set G) :=
    (le_inf hnorm (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)).trans
      (Subgroup.inf_normalizer_le_normalizer_sup M (pCoreOf 2 K))
  refine le_antisymm ?_ ?_
  ·
    have hp : IsPGroup 2 (pCoreOf 2 (M ⊔ pCoreOf 2 K)) :=
      (CFSG.pCore_isPGroup (G := ↥(M ⊔ pCoreOf 2 K)) (p := 2)).map
        (M ⊔ pCoreOf 2 K).subtype
    have hnorm' : K ≤ Subgroup.normalizer (pCoreOf 2 (M ⊔ pCoreOf 2 K) : Set G) :=
      hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (K := CFSG.pCore 2 ↥(M ⊔ pCoreOf 2 K)))
    have hN : ((pCoreOf 2 (M ⊔ pCoreOf 2 K)).subgroupOf K).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer hnorm'
    exact CFSG.LieType.BorelTits.le_pCoreOf (r := 2)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (M ⊔ pCoreOf 2 K)).trans hNK) hN hp
  ·
    have hp : IsPGroup 2 (pCoreOf 2 K) :=
      (CFSG.pCore_isPGroup (G := ↥K) (p := 2)).map K.subtype
    have hN : ((pCoreOf 2 K).subgroupOf (M ⊔ pCoreOf 2 K)).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer
        (sup_le (hMK.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K))
          Subgroup.le_normalizer)
    exact CFSG.LieType.BorelTits.le_pCoreOf (r := 2) le_sup_right hN hp

theorem pCore_quotient_mulEquiv_of_sup_pCoreOf_of_normal {G : Type*} [Group G]
    {M K : Subgroup G} (hMK : M ≤ K) (hnorm : K ≤ Subgroup.normalizer (M : Set G)) :
    Nonempty (↥(M ⊔ pCoreOf 2 K) ⧸ CFSG.pCore 2 ↥(M ⊔ pCoreOf 2 K) ≃*
      ↥M ⧸ CFSG.pCore 2 ↥M) := by
  have hN : pCoreOf 2 (M ⊔ pCoreOf 2 K) = pCoreOf 2 K := pCoreOf_sup_pCoreOf hMK hnorm
  have hMN : M ≤ M ⊔ pCoreOf 2 K := le_sup_left
  have hnormN : M ⊔ pCoreOf 2 K ≤ Subgroup.normalizer (M : Set G) :=
    sup_le Subgroup.le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hnorm)
  have hsup : M ⊔ pCoreOf 2 (M ⊔ pCoreOf 2 K) = M ⊔ pCoreOf 2 K := by rw [hN]
  obtain ⟨e⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf hMN hnormN hsup
  exact ⟨e.symm⟩

noncomputable def pCoreQuotientMulEquiv {G G' : Type*} [Group G] [Group G'] (p : ℕ) (e : G ≃* G') :
    G ⧸ CFSG.pCore p G ≃* G' ⧸ CFSG.pCore p G' :=
  QuotientGroup.congr (CFSG.pCore p G) (CFSG.pCore p G') e (CFSG.pCore_map_iso p e)

theorem IsLocL2.smul {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}
    (hadj : ∀ (g : G) (u v : V), Γ.Adj (g • u) (g • v) ↔ Γ.Adj u v)
    {v : V} {n : ℕ} {N : Subgroup G} (hN : IsLocL2 Γ G v n N) (g : G) :
    IsLocL2 Γ G (g • v) n (N.map (MulAut.conj g).toMonoidHom) where
  le := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj g v]
    exact Subgroup.map_mono hN.le
  normal := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj g v]
    rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hN.le)]
    intro h k hh hk
    obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp hh
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hk
    have hconj : s * m * s⁻¹ ∈ N :=
      (Subgroup.normal_subgroupOf_iff hN.le).mp hN.normal m s hm hs
    have h1 := Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom hconj
    rwa [map_mul, map_mul, map_inv] at h1
  oTwo_le := by
    rw [MulAction.stabilizer_smul_eq_stabilizer_map_conj g v]
    rw [CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv (r := 2) (e := MulAut.conj g)
      (H := MulAction.stabilizer G v)]
    exact Subgroup.map_mono hN.oTwo_le
  quot := by
    obtain ⟨e⟩ := hN.quot
    exact ⟨(pCoreQuotientMulEquiv 2 (MulEquiv.subgroupMap (MulAut.conj g) N)).symm.trans e⟩
  trans := by
    intro a b ha hb
    have ha' : Γ.Adj v (g⁻¹ • a) := by
      simpa using (hadj g⁻¹ (g • v) a).mpr (by simpa using ha)
    have hb' : Γ.Adj v (g⁻¹ • b) := by
      simpa using (hadj g⁻¹ (g • v) b).mpr (by simpa using hb)
    obtain ⟨m, hm, hma⟩ := hN.trans (g⁻¹ • a) (g⁻¹ • b) ha' hb'
    refine ⟨(MulAut.conj g) m, Subgroup.mem_map_of_mem _ hm, ?_⟩
    rw [MulAut.conj_apply, mul_smul, mul_smul, hma, smul_inv_smul]

theorem pCoreOf_subgroupOf_map {G : Type*} [Group G] {K E : Subgroup G} (hKE : K ≤ E) :
    (CFSG.Open.pCoreOf 2 (K.subgroupOf E)).map E.subtype = CFSG.Open.pCoreOf 2 K := by
  show ((CFSG.pCore 2 ↥(K.subgroupOf E)).map (K.subgroupOf E).subtype).map E.subtype =
    (CFSG.pCore 2 ↥K).map K.subtype
  rw [Subgroup.map_map]
  have hcomp : E.subtype.comp (K.subgroupOf E).subtype =
      K.subtype.comp (Subgroup.subgroupOfEquivOfLe hKE).toMonoidHom := by
    ext x; rfl
  rw [hcomp, ← Subgroup.map_map, CFSG.pCore_map_iso]

end CFSG.Quasithin.St84

namespace CFSG.Quasithin.F112R.St84

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.F112R CFSG.Quasithin.St84
  CFSG.Quasithin.Fan86 CFSG.Quasithin.Fan86.Univ
open scoped Pointwise

variable {H : Type} [Group H] [Finite H]

theorem f112_five_dvd_card_L1 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) : 5 ∣ Nat.card ↥L1 := by
  have hrel : (borelOf L1 S).relIndex L1 = 5 := by
    have h' := index_borelOf_of_psl2 (f := 2) (by norm_num) hF.1.h1.sylow h1
    simpa [Subgroup.relIndex] using h'
  have hcard : 5 * Nat.card ↥(borelOf L1 S) = Nat.card ↥L1 := by
    have h' := Subgroup.relIndex_mul_card (borelOf L1 S) L1
    rw [inf_eq_left.mpr (F1.borelOf_le L1 S), hrel] at h'
    exact h'
  exact ⟨Nat.card ↥(borelOf L1 S), hcard.symm⟩

theorem f112_not_five_dvd_relIndex_L1 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ¬ 5 ∣ L1.relIndex (f112P1 L1 L2 S) := by
  have hcardL1 : 5 * Nat.card ↥(borelOf L1 S) = Nat.card ↥L1 := by
    have hrel : (borelOf L1 S).relIndex L1 = 5 := by
      have h' := index_borelOf_of_psl2 (f := 2) (by norm_num) hF.1.h1.sylow h1
      simpa [Subgroup.relIndex] using h'
    have h' := Subgroup.relIndex_mul_card (borelOf L1 S) L1
    rw [inf_eq_left.mpr (F1.borelOf_le L1 S), hrel] at h'
    exact h'
  have hcardP1 : 5 * Nat.card ↥(bigB L1 L2 S) = Nat.card ↥(f112P1 L1 L2 S) :=
    f112_card_P1 hF h1 h2
  have hrel : L1.relIndex (f112P1 L1 L2 S) * Nat.card ↥L1 =
      Nat.card ↥(f112P1 L1 L2 S) := by
    have h := Subgroup.relIndex_mul_card L1 (f112P1 L1 L2 S)
    rwa [inf_eq_left.mpr le_sup_left] at h
  have hB : Nat.card ↥(bigB L1 L2 S) =
      L1.relIndex (f112P1 L1 L2 S) * Nat.card ↥(borelOf L1 S) := by
    have h' : 5 * (L1.relIndex (f112P1 L1 L2 S) * Nat.card ↥(borelOf L1 S)) =
        5 * Nat.card ↥(bigB L1 L2 S) := by
      rw [hcardP1, ← hrel, ← hcardL1]
      ring
    exact (Nat.mul_left_cancel (by norm_num) h').symm
  rintro ⟨d, hd⟩
  apply f112_not_five_dvd_card_bigB hF h1 h2
  refine ⟨d * Nat.card ↥(borelOf L1 S), ?_⟩
  rw [hB, hd]
  ring

theorem f112_mem_L1_of_orderFive {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) {x : H}
    (hxP : x ∈ f112P1 L1 L2 S) (hx5 : orderOf x = 5) : x ∈ L1 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hnormP1 : f112P1 L1 L2 S ≤ Subgroup.normalizer (L1 : Set H) :=
    sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).1
  let P : Subgroup H := f112P1 L1 L2 S
  let M' : Subgroup ↥P := L1.subgroupOf P
  haveI hM' : M'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnormP1
  have h5 : 5 ∣ Nat.card M' := by
    show 5 ∣ Nat.card ↥(L1.subgroupOf (f112P1 L1 L2 S))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]
    exact f112_five_dvd_card_L1 hF h1
  have hnot5 : ¬ 5 ∣ M'.index := by
    show ¬ 5 ∣ (L1.subgroupOf (f112P1 L1 L2 S)).index
    exact f112_not_five_dvd_relIndex_L1 hF h1 h2
  let q : ↥P →* ↥P ⧸ M' := QuotientGroup.mk' M'
  have hxpow : (⟨x, hxP⟩ : ↥P) ^ 5 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hx5, pow_orderOf_eq_one]
    rfl
  have hq5 : q ⟨x, hxP⟩ ^ 5 = 1 := by
    simpa [← map_pow] using congrArg q hxpow
  have hord : orderOf (q ⟨x, hxP⟩) ∣ 5 := orderOf_dvd_of_pow_eq_one hq5
  have hcarddvd : orderOf (q ⟨x, hxP⟩) ∣ Nat.card (↥P ⧸ M') := orderOf_dvd_natCard _
  have hqcard : Nat.card (↥P ⧸ M') = M'.index := (Subgroup.index_eq_card M').symm
  have hnot5' : ¬ 5 ∣ Nat.card (↥P ⧸ M') := by rw [hqcard]; exact hnot5
  have hcop : Nat.Coprime 5 (Nat.card (↥P ⧸ M')) :=
    Nat.prime_five.coprime_iff_not_dvd.mpr hnot5'
  have hdvd1 : orderOf (q ⟨x, hxP⟩) ∣ 1 := by
    rw [← Nat.coprime_iff_gcd_eq_one.mp hcop]
    exact Nat.dvd_gcd hord hcarddvd
  have hq1 : q ⟨x, hxP⟩ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  have hmem : (⟨x, hxP⟩ : ↥P) ∈ M' := (QuotientGroup.eq_one_iff _).mp hq1
  show x ∈ L1
  exact Subgroup.mem_subgroupOf.mp hmem

theorem f112M1_le_L1 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) : f112M1 L1 L2 S ≤ L1 := by
  rw [f112M1]
  refine (Subgroup.closure_le L1).mpr ?_
  rintro x ⟨hxP, hx5⟩
  exact f112_mem_L1_of_orderFive hF h1 h2 hxP hx5

theorem f112M1_conj_mem {L1 L2 S : Subgroup H} {g x : H}
    (hg : g ∈ f112P1 L1 L2 S) (hx : x ∈ f112M1 L1 L2 S) :
    g * x * g⁻¹ ∈ f112M1 L1 L2 S := by
  have hmap : (f112M1 L1 L2 S).map (MulAut.conj g).toMonoidHom ≤ f112M1 L1 L2 S := by
    rw [f112M1, MonoidHom.map_closure]
    refine (Subgroup.closure_le (f112M1 L1 L2 S)).mpr ?_
    rintro y ⟨x, hx, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · show g * x * g⁻¹ ∈ f112P1 L1 L2 S
      exact (f112P1 L1 L2 S).mul_mem ((f112P1 L1 L2 S).mul_mem hg hx.1)
        ((f112P1 L1 L2 S).inv_mem hg)
    · show orderOf (g * x * g⁻¹) = 5
      have h : orderOf (g * x * g⁻¹) = orderOf x := by
        simpa [MulAut.conj_apply] using
          orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      rw [h]
      exact hx.2
  exact hmap (Subgroup.mem_map_of_mem _ hx)

theorem f112M1_normal (L1 L2 S : Subgroup H) :
    f112P1 L1 L2 S ≤ Subgroup.normalizer (f112M1 L1 L2 S : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact f112M1_conj_mem hg hx
  · intro hx
    have h := f112M1_conj_mem (L2 := L2) (S := S) ((f112P1 L1 L2 S).inv_mem hg) hx
    simpa [mul_assoc] using h

theorem f112M1_normal_L1 (L1 L2 S : Subgroup H) :
    L1 ≤ Subgroup.normalizer (f112M1 L1 L2 S : Set H) :=
  le_sup_left.trans (f112M1_normal L1 L2 S)

theorem f112M1_sup_pCoreOf {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    f112M1 L1 L2 S ⊔ pCoreOf 2 L1 = L1 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hM1L1 : f112M1 L1 L2 S ≤ L1 := f112M1_le_L1 hF h1 h2
  have hnormL1 : L1 ≤ Subgroup.normalizer (f112M1 L1 L2 S : Set H) := f112M1_normal_L1 L1 L2 S
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' 5 (f112_five_dvd_card_L1 hF h1)
  have hx5H : orderOf (x : H) = 5 := by rw [Subgroup.orderOf_coe]; exact hx5
  have hxM1 : (x : H) ∈ f112M1 L1 L2 S :=
    Subgroup.subset_closure ⟨Subgroup.mem_sup_left x.2, hx5H⟩
  let M' : Subgroup ↥L1 := (f112M1 L1 L2 S).subgroupOf L1
  haveI hM' : M'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnormL1
  let π : ↥L1 →* ↥L1 ⧸ CFSG.pCore 2 ↥L1 := QuotientGroup.mk' (CFSG.pCore 2 ↥L1)
  have hM'normal : (M'.map π).Normal := hM'.map π (QuotientGroup.mk'_surjective _)
  have hxM' : x ∈ M' := by
    rw [Subgroup.mem_subgroupOf]; exact hxM1
  have hne : M'.map π ≠ ⊥ := by
    intro hbot
    have hmem : π x ∈ M'.map π := Subgroup.mem_map_of_mem π hxM'
    rw [hbot, Subgroup.mem_bot] at hmem
    have hxpc : x ∈ CFSG.pCore 2 ↥L1 := (QuotientGroup.eq_one_iff _).mp hmem
    have hxpcof : (x : H) ∈ pCoreOf 2 L1 := by
      have h := (Subgroup.mem_map_iff_mem (K := CFSG.pCore 2 ↥L1) (x := x)
        L1.subtype_injective).mpr hxpc
      simpa [pCoreOf] using h
    have hp : IsPGroup 2 (pCoreOf 2 L1) := pCoreOf_isPGroup' L1
    obtain ⟨k, hk⟩ := hp ⟨(x : H), hxpcof⟩
    have hord : orderOf (⟨(x : H), hxpcof⟩ : ↥(pCoreOf 2 L1)) = 5 := by
      rw [Subgroup.orderOf_mk]; exact hx5H
    have hdvd : 5 ∣ 2 ^ k := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hk
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
    norm_num at h52
  haveI hPSL : IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
    apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  haveI : IsSimpleGroup (↥L1 ⧸ CFSG.pCore 2 ↥L1) := by
    obtain ⟨e⟩ := h1
    exact e.isSimpleGroup
  haveI : (M'.map π).Normal := hM'normal
  have htop : M'.map π = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (M'.map π) with h | h
    · exact absurd h hne
    · exact h
  apply le_antisymm
  · exact sup_le hM1L1 (CFSG.LieType.BorelTits.pCoreOf_le 2 L1)
  · intro l hl
    have hmem : π ⟨l, hl⟩ ∈ M'.map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨m', hm', hmm'⟩ := Subgroup.mem_map.mp hmem
    have hm1 : (m' : H) ∈ f112M1 L1 L2 S := Subgroup.mem_subgroupOf.mp hm'
    have hq : (m'⁻¹ * (⟨l, hl⟩ : ↥L1) : ↥L1) ∈ CFSG.pCore 2 ↥L1 := by
      have h : π (m'⁻¹ * (⟨l, hl⟩ : ↥L1)) = 1 := by
        rw [map_mul, map_inv, hmm', inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h
    have hqG : ((m'⁻¹ * (⟨l, hl⟩ : ↥L1) : ↥L1) : H) ∈ pCoreOf 2 L1 := by
      have h := (Subgroup.mem_map_iff_mem (K := CFSG.pCore 2 ↥L1)
        (x := m'⁻¹ * (⟨l, hl⟩ : ↥L1)) L1.subtype_injective).mpr hq
      simpa [pCoreOf] using h
    have hl' : (m' : H) * ((m'⁻¹ * (⟨l, hl⟩ : ↥L1) : ↥L1) : H) = l := by
      simp [mul_assoc]
    have hmem' : (m' : H) * ((m'⁻¹ * (⟨l, hl⟩ : ↥L1) : ↥L1) : H) ∈
        f112M1 L1 L2 S ⊔ pCoreOf 2 L1 :=
      (f112M1 L1 L2 S ⊔ pCoreOf 2 L1).mul_mem (Subgroup.mem_sup_left hm1)
        (Subgroup.mem_sup_right hqG)
    rwa [hl'] at hmem'

theorem f112M1_quot {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    Nonempty (↥(f112M1 L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112M1 L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf (f112M1_le_L1 hF h1 h2)
    (f112M1_normal_L1 L1 L2 S) (f112M1_sup_pCoreOf hF h1 h2)
  obtain ⟨e2⟩ := h1
  exact ⟨e1.trans e2⟩

noncomputable def f112A1 (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  (f112M1 L1 L2 S).subgroupOf (f112P1 L1 L2 S) |>.map (f112Gold L1 L2 S).ofA

noncomputable def f112Nalpha (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  f112E5 L1 L2 S ⊓ (f112Gold L1 L2 S).ofA.range

noncomputable def f112NlocalA (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  f112A1 L1 L2 S ⊔ pCoreOf 2 (f112Nalpha L1 L2 S)

theorem f112A1_le_E {L1 L2 S : Subgroup H} :
    f112A1 L1 L2 S ≤ f112E5 L1 L2 S := by
  let K' : Subgroup ↥(f112P1 L1 L2 S) := (f112E5 L1 L2 S).comap (f112Gold L1 L2 S).ofA
  let KH : Subgroup H := K'.map (f112P1 L1 L2 S).subtype
  have hM1KH : f112M1 L1 L2 S ≤ KH := by
    rw [f112M1]
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    show y ∈ K'.map (f112P1 L1 L2 S).subtype
    have hgen : (⟨y, hy.1⟩ : ↥(f112P1 L1 L2 S)) ∈ K' := by
      show (f112Gold L1 L2 S).ofA ⟨y, hy.1⟩ ∈ f112E5 L1 L2 S
      refine Subgroup.subset_closure ⟨Or.inl ⟨⟨y, hy.1⟩, rfl⟩, ?_⟩
      rw [orderOf_injective (f112Gold L1 L2 S).ofA (f112Gold L1 L2 S).ofA_injective,
        Subgroup.orderOf_mk]
      exact hy.2
    exact Subgroup.mem_map_of_mem (f := (f112P1 L1 L2 S).subtype) (x := ⟨y, hy.1⟩) hgen
  rw [f112A1, Subgroup.map_le_iff_le_comap]
  intro x hx
  have hxKH : (x : H) ∈ KH := hM1KH (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxKH
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx']
  exact hz

theorem f112A1_le_Nalpha {L1 L2 S : Subgroup H} :
    f112A1 L1 L2 S ≤ f112Nalpha L1 L2 S := by
  refine le_inf f112A1_le_E ?_
  rw [f112A1]
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  intro x _
  exact ⟨x, rfl⟩

theorem f112A1_conj_mem {L1 L2 S : Subgroup H} {g a : (f112Gold L1 L2 S).Universal}
    (hg : g ∈ f112Nalpha L1 L2 S) (ha : a ∈ f112A1 L1 L2 S) :
    g * a * g⁻¹ ∈ f112A1 L1 L2 S := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨p, rfl⟩ := hg.2
  have hconj : p * m * p⁻¹ ∈ (f112M1 L1 L2 S).subgroupOf (f112P1 L1 L2 S) := by
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact f112M1_conj_mem p.2 hm
  have heq : (f112Gold L1 L2 S).ofA p * (f112Gold L1 L2 S).ofA m *
      ((f112Gold L1 L2 S).ofA p)⁻¹ = (f112Gold L1 L2 S).ofA (p * m * p⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [heq]
  exact Subgroup.mem_map_of_mem _ hconj

theorem f112A1_normal_Nalpha {L1 L2 S : Subgroup H} :
    f112Nalpha L1 L2 S ≤
      Subgroup.normalizer (f112A1 L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact f112A1_conj_mem hg ha
  · intro ha
    have h := f112A1_conj_mem (L1 := L1) (L2 := L2) (S := S) ((f112Nalpha L1 L2 S).inv_mem hg) ha
    simpa [mul_assoc] using h

theorem f112NlocalA_normal_Nalpha {L1 L2 S : Subgroup H} :
    f112Nalpha L1 L2 S ≤ Subgroup.normalizer
      (f112NlocalA L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (le_inf f112A1_normal_Nalpha
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112Nalpha L1 L2 S))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup (f112A1 L1 L2 S)
      (pCoreOf 2 (f112Nalpha L1 L2 S)))

theorem f112NlocalA_le_Nalpha {L1 L2 S : Subgroup H} :
    f112NlocalA L1 L2 S ≤ f112Nalpha L1 L2 S :=
  sup_le f112A1_le_Nalpha (CFSG.LieType.BorelTits.pCoreOf_le 2 _)

theorem f112NlocalA_le_E {L1 L2 S : Subgroup H} :
    f112NlocalA L1 L2 S ≤ f112E5 L1 L2 S :=
  f112NlocalA_le_Nalpha.trans inf_le_left

theorem f112A1_quot {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    Nonempty (↥(f112A1 L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112A1 L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  obtain ⟨e1⟩ := f112M1_quot hF h1 h2
  let e2 : ↥(f112M1 L1 L2 S) ≃* ↥(f112A1 L1 L2 S) :=
    (Subgroup.subgroupOfEquivOfLe ((f112M1_le_L1 hF h1 h2).trans le_sup_left)).symm.trans
      (Subgroup.equivMapOfInjective
        (H := (f112M1 L1 L2 S).subgroupOf (f112P1 L1 L2 S))
        (f := (f112Gold L1 L2 S).ofA) (f112Gold L1 L2 S).ofA_injective)
  exact ⟨(pCoreQuotientMulEquiv 2 e2).symm.trans e1⟩

theorem f112NlocalA_quot {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    Nonempty (↥(f112NlocalA L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112NlocalA L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf_of_normal
    (M := f112A1 L1 L2 S) (K := f112Nalpha L1 L2 S) f112A1_le_Nalpha f112A1_normal_Nalpha
  obtain ⟨e2⟩ := f112A1_quot hF h1 h2
  exact ⟨e1.trans e2⟩

theorem f112NlocalA_subgroupOf_quot {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    Nonempty (↥((f112NlocalA L1 L2 S).subgroupOf (f112E5 L1 L2 S)) ⧸
        CFSG.pCore 2 ↥((f112NlocalA L1 L2 S).subgroupOf (f112E5 L1 L2 S)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  obtain ⟨e1⟩ := f112NlocalA_quot hF h1 h2
  exact ⟨(pCoreQuotientMulEquiv 2
    (Subgroup.subgroupOfEquivOfLe f112NlocalA_le_E)).trans e1⟩

theorem f112A1_trans {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseA (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112A1 L1 L2 S, g • a = b := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro a b ha hb
  let X := f112Gold L1 L2 S
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' 5 (f112_five_dvd_card_L1 hF h1)
  have hx5H : orderOf (x : H) = 5 := by rw [Subgroup.orderOf_coe]; exact hx5
  have hxM1 : (x : H) ∈ f112M1 L1 L2 S :=
    Subgroup.subset_closure ⟨Subgroup.mem_sup_left x.2, hx5H⟩
  let ax : X.Universal := X.ofA ⟨(x : H), Subgroup.mem_sup_left x.2⟩
  have haxA1 : ax ∈ f112A1 L1 L2 S := by
    show X.ofA ⟨(x : H), Subgroup.mem_sup_left x.2⟩ ∈ f112A1 L1 L2 S
    exact Subgroup.mem_map_of_mem X.ofA (Subgroup.mem_subgroupOf.mpr hxM1)
  have hax5 : orderOf ax = 5 := by
    show orderOf (X.ofA ⟨(x : H), Subgroup.mem_sup_left x.2⟩) = 5
    rw [orderOf_injective X.ofA X.ofA_injective, Subgroup.orderOf_mk]
    exact hx5H
  have haxfix : ax • baseA X = baseA X := by
    have hmem : ax ∈ MulAction.stabilizer X.Universal (baseA X) := by
      rw [stabilizer_baseA]
      exact ⟨⟨(x : H), Subgroup.mem_sup_left x.2⟩, rfl⟩
    exact MulAction.mem_stabilizer_iff.mp hmem
  let P : Subgroup X.Universal := Subgroup.zpowers ax
  have hPle : P ≤ f112A1 L1 L2 S := Subgroup.zpowers_le.mpr haxA1
  have hSfin : (X.treeGraph.neighborSet (baseA X)).Finite :=
    Set.finite_of_ncard_ne_zero (by
      rw [f112_ncard_neighborSet hF h1 h2 (baseA X)]; norm_num)
  have hSncard : (X.treeGraph.neighborSet (baseA X)).ncard = 5 :=
    f112_ncard_neighborSet hF h1 h2 (baseA X)
  have hsub : MulAction.orbit P a ⊆ X.treeGraph.neighborSet (baseA X) := by
    rintro w ⟨p, rfl⟩
    have hpfix : (p : X.Universal) • baseA X = baseA X :=
      smul_eq_self_of_mem_zpowers p.2 haxfix
    show X.treeGraph.Adj (baseA X) ((p : X.Universal) • a)
    rw [← hpfix]
    exact (adj_smul X (p : X.Universal) (baseA X) a).2 ha
  have hidx : (MulAction.stabilizer P a).index ∣ 5 := by
    have h := Subgroup.index_mul_card (MulAction.stabilizer P a)
    have hP5 : Nat.card ↥P = 5 := by
      rw [show P = Subgroup.zpowers ax from rfl, Nat.card_zpowers, hax5]
    rw [hP5] at h
    exact ⟨Nat.card ↥(MulAction.stabilizer P a), h.symm⟩
  have hne : (MulAction.stabilizer P a).index ≠ 1 := by
    intro h1'
    have htop : MulAction.stabilizer P a = ⊤ := Subgroup.index_eq_one.mp h1'
    have haxP : ax ∈ P := Subgroup.mem_zpowers ax
    have hfix : ax • a = a := by
      have hmem : (⟨ax, haxP⟩ : P) ∈ MulAction.stabilizer P a := by
        rw [htop]; exact Subgroup.mem_top _
      simpa using MulAction.mem_stabilizer_iff.mp hmem
    exact f112_orderFive_not_fixed hF (f112_not_five_dvd_card_bigB hF h1 h2)
      ⟨⟨(x : H), Subgroup.mem_sup_left x.2⟩, rfl⟩ hax5 ha hfix
  have hidx5 : (MulAction.stabilizer P a).index = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hidx with h | h
    · exact absurd h hne
    · exact h
  have horbcard : (MulAction.orbit P a).ncard = 5 := by
    rw [← MulAction.index_stabilizer P a, hidx5]
  have heq : MulAction.orbit P a = X.treeGraph.neighborSet (baseA X) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hSncard, horbcard]) hSfin
  have hbO : b ∈ MulAction.orbit P a := by rw [heq]; exact hb
  obtain ⟨p, hp⟩ := hbO
  exact ⟨(p : X.Universal), hPle p.2, hp⟩

theorem f112_localL2_baseA {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∃ N : Subgroup ↥(f112E5 L1 L2 S),
      IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)
        (baseA (f112Gold L1 L2 S)) 2 N := by
  let E := f112E5 L1 L2 S
  let X := f112Gold L1 L2 S
  let N : Subgroup ↥E := (f112NlocalA L1 L2 S).subgroupOf E
  have hstab : MulAction.stabilizer ↥E (baseA X) = (f112Nalpha L1 L2 S).subgroupOf E := by
    rw [← MulAction.stabilizer_subgroupOf E (baseA X), stabilizer_baseA X, f112Nalpha,
      Subgroup.inf_subgroupOf_left]
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hstab]
    exact Subgroup.subgroupOf_mono E f112NlocalA_le_Nalpha
  ·
    rw [hstab]
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hkU : (k : X.Universal) ∈ f112Nalpha L1 L2 S := Subgroup.mem_subgroupOf.mp hk
    constructor
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      exact (Subgroup.mem_normalizer_iff.mp (f112NlocalA_normal_Nalpha hkU)
        (h : X.Universal)).mp hh
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      have hkU' : (k : X.Universal)⁻¹ ∈ f112Nalpha L1 L2 S :=
        (f112Nalpha L1 L2 S).inv_mem hkU
      have hmem := (Subgroup.mem_normalizer_iff.mp (f112NlocalA_normal_Nalpha hkU')
        ((k : X.Universal) * (h : X.Universal) * (k : X.Universal)⁻¹)).mp hh
      simpa [mul_assoc] using hmem
  ·
    rw [hstab]
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hpc := pCoreOf_subgroupOf_map (K := f112Nalpha L1 L2 S) (E := E) inf_le_left
    have hmem : (y : X.Universal) ∈
        (pCoreOf 2 ((f112Nalpha L1 L2 S).subgroupOf E)).map E.subtype :=
      Subgroup.mem_map_of_mem E.subtype hy
    rw [hpc] at hmem
    exact (show pCoreOf 2 (f112Nalpha L1 L2 S) ≤ f112NlocalA L1 L2 S from le_sup_right) hmem
  ·
    obtain ⟨e⟩ := f112NlocalA_subgroupOf_quot hF h1 h2
    exact ⟨e⟩
  ·
    intro a b ha hb
    obtain ⟨g, hgA1, hgab⟩ := f112A1_trans hF h1 h2 a b ha hb
    refine ⟨⟨g, f112A1_le_E hgA1⟩, ?_, ?_⟩
    · show (⟨g, f112A1_le_E hgA1⟩ : ↥E) ∈ N
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left hgA1
    · show g • a = b
      exact hgab

theorem f112_five_dvd_card_L2 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h2 : VA5 L2) : 5 ∣ Nat.card ↥L2 := by
  have hrel : (borelOf L2 S).relIndex L2 = 5 := by
    have h' := index_borelOf_of_psl2 (f := 2) (by norm_num) hF.1.h2.sylow h2
    simpa [Subgroup.relIndex] using h'
  have hcard : 5 * Nat.card ↥(borelOf L2 S) = Nat.card ↥L2 := by
    have h' := Subgroup.relIndex_mul_card (borelOf L2 S) L2
    rw [inf_eq_left.mpr (F1.borelOf_le L2 S), hrel] at h'
    exact h'
  exact ⟨Nat.card ↥(borelOf L2 S), hcard.symm⟩

theorem f112_not_five_dvd_relIndex_L2 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ¬ 5 ∣ L2.relIndex (f112P2 L1 L2 S) := by
  have hcardL2 : 5 * Nat.card ↥(borelOf L2 S) = Nat.card ↥L2 := by
    have hrel : (borelOf L2 S).relIndex L2 = 5 := by
      have h' := index_borelOf_of_psl2 (f := 2) (by norm_num) hF.1.h2.sylow h2
      simpa [Subgroup.relIndex] using h'
    have h' := Subgroup.relIndex_mul_card (borelOf L2 S) L2
    rw [inf_eq_left.mpr (F1.borelOf_le L2 S), hrel] at h'
    exact h'
  have hcardP1 : 5 * Nat.card ↥(bigB L1 L2 S) = Nat.card ↥(f112P2 L1 L2 S) :=
    f112_card_P2 hF h1 h2
  have hrel : L2.relIndex (f112P2 L1 L2 S) * Nat.card ↥L2 =
      Nat.card ↥(f112P2 L1 L2 S) := by
    have h := Subgroup.relIndex_mul_card L2 (f112P2 L1 L2 S)
    rwa [inf_eq_left.mpr le_sup_left] at h
  have hB : Nat.card ↥(bigB L1 L2 S) =
      L2.relIndex (f112P2 L1 L2 S) * Nat.card ↥(borelOf L2 S) := by
    have h' : 5 * (L2.relIndex (f112P2 L1 L2 S) * Nat.card ↥(borelOf L2 S)) =
        5 * Nat.card ↥(bigB L1 L2 S) := by
      rw [hcardP1, ← hrel, ← hcardL2]
      ring
    exact (Nat.mul_left_cancel (by norm_num) h').symm
  rintro ⟨d, hd⟩
  apply f112_not_five_dvd_card_bigB hF h1 h2
  refine ⟨d * Nat.card ↥(borelOf L2 S), ?_⟩
  rw [hB, hd]
  ring

theorem f112_mem_L2_of_orderFive {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) {x : H}
    (hxP : x ∈ f112P2 L1 L2 S) (hx5 : orderOf x = 5) : x ∈ L2 := by
  have hR : Hyp111R L1 L2 S := Hyp111R.of_hyp111 rankOneListedFacts hF.1
  have hnormP1 : f112P2 L1 L2 S ≤ Subgroup.normalizer (L2 : Set H) :=
    sup_le Subgroup.le_normalizer (F1.bigB_le_normalizer_left hR).2
  let P : Subgroup H := f112P2 L1 L2 S
  let M' : Subgroup ↥P := L2.subgroupOf P
  haveI hM' : M'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnormP1
  have h5 : 5 ∣ Nat.card M' := by
    show 5 ∣ Nat.card ↥(L2.subgroupOf (f112P2 L1 L2 S))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv]
    exact f112_five_dvd_card_L2 hF h2
  have hnot5 : ¬ 5 ∣ M'.index := by
    show ¬ 5 ∣ (L2.subgroupOf (f112P2 L1 L2 S)).index
    exact f112_not_five_dvd_relIndex_L2 hF h1 h2
  let q : ↥P →* ↥P ⧸ M' := QuotientGroup.mk' M'
  have hxpow : (⟨x, hxP⟩ : ↥P) ^ 5 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hx5, pow_orderOf_eq_one]
    rfl
  have hq5 : q ⟨x, hxP⟩ ^ 5 = 1 := by
    simpa [← map_pow] using congrArg q hxpow
  have hord : orderOf (q ⟨x, hxP⟩) ∣ 5 := orderOf_dvd_of_pow_eq_one hq5
  have hcarddvd : orderOf (q ⟨x, hxP⟩) ∣ Nat.card (↥P ⧸ M') := orderOf_dvd_natCard _
  have hqcard : Nat.card (↥P ⧸ M') = M'.index := (Subgroup.index_eq_card M').symm
  have hnot5' : ¬ 5 ∣ Nat.card (↥P ⧸ M') := by rw [hqcard]; exact hnot5
  have hcop : Nat.Coprime 5 (Nat.card (↥P ⧸ M')) :=
    Nat.prime_five.coprime_iff_not_dvd.mpr hnot5'
  have hdvd1 : orderOf (q ⟨x, hxP⟩) ∣ 1 := by
    rw [← Nat.coprime_iff_gcd_eq_one.mp hcop]
    exact Nat.dvd_gcd hord hcarddvd
  have hq1 : q ⟨x, hxP⟩ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hdvd1)
  have hmem : (⟨x, hxP⟩ : ↥P) ∈ M' := (QuotientGroup.eq_one_iff _).mp hq1
  show x ∈ L2
  exact Subgroup.mem_subgroupOf.mp hmem

theorem f112M2_le_L2 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) : f112M2 L1 L2 S ≤ L2 := by
  rw [f112M2]
  refine (Subgroup.closure_le L2).mpr ?_
  rintro x ⟨hxP, hx5⟩
  exact f112_mem_L2_of_orderFive hF h1 h2 hxP hx5

theorem f112M2_conj_mem {L1 L2 S : Subgroup H} {g x : H}
    (hg : g ∈ f112P2 L1 L2 S) (hx : x ∈ f112M2 L1 L2 S) :
    g * x * g⁻¹ ∈ f112M2 L1 L2 S := by
  have hmap : (f112M2 L1 L2 S).map (MulAut.conj g).toMonoidHom ≤ f112M2 L1 L2 S := by
    rw [f112M2, MonoidHom.map_closure]
    refine (Subgroup.closure_le (f112M2 L1 L2 S)).mpr ?_
    rintro y ⟨x, hx, rfl⟩
    refine Subgroup.subset_closure ⟨?_, ?_⟩
    · show g * x * g⁻¹ ∈ f112P2 L1 L2 S
      exact (f112P2 L1 L2 S).mul_mem ((f112P2 L1 L2 S).mul_mem hg hx.1)
        ((f112P2 L1 L2 S).inv_mem hg)
    · show orderOf (g * x * g⁻¹) = 5
      have h : orderOf (g * x * g⁻¹) = orderOf x := by
        simpa [MulAut.conj_apply] using
          orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective x
      rw [h]
      exact hx.2
  exact hmap (Subgroup.mem_map_of_mem _ hx)

theorem f112M2_normal (L1 L2 S : Subgroup H) :
    f112P2 L1 L2 S ≤ Subgroup.normalizer (f112M2 L1 L2 S : Set H) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact f112M2_conj_mem hg hx
  · intro hx
    have h := f112M2_conj_mem (L2 := L2) (S := S) ((f112P2 L1 L2 S).inv_mem hg) hx
    simpa [mul_assoc] using h

theorem f112M2_normal_L2 (L1 L2 S : Subgroup H) :
    L2 ≤ Subgroup.normalizer (f112M2 L1 L2 S : Set H) :=
  le_sup_left.trans (f112M2_normal L1 L2 S)

theorem f112M2_sup_pCoreOf {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    f112M2 L1 L2 S ⊔ pCoreOf 2 L2 = L2 := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hM1L2 : f112M2 L1 L2 S ≤ L2 := f112M2_le_L2 hF h1 h2
  have hnormL2 : L2 ≤ Subgroup.normalizer (f112M2 L1 L2 S : Set H) := f112M2_normal_L2 L1 L2 S
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' 5 (f112_five_dvd_card_L2 hF h2)
  have hx5H : orderOf (x : H) = 5 := by rw [Subgroup.orderOf_coe]; exact hx5
  have hxM1 : (x : H) ∈ f112M2 L1 L2 S :=
    Subgroup.subset_closure ⟨Subgroup.mem_sup_left x.2, hx5H⟩
  let M' : Subgroup ↥L2 := (f112M2 L1 L2 S).subgroupOf L2
  haveI hM' : M'.Normal := Subgroup.normal_subgroupOf_of_le_normalizer hnormL2
  let π : ↥L2 →* ↥L2 ⧸ CFSG.pCore 2 ↥L2 := QuotientGroup.mk' (CFSG.pCore 2 ↥L2)
  have hM'normal : (M'.map π).Normal := hM'.map π (QuotientGroup.mk'_surjective _)
  have hxM' : x ∈ M' := by
    rw [Subgroup.mem_subgroupOf]; exact hxM1
  have hne : M'.map π ≠ ⊥ := by
    intro hbot
    have hmem : π x ∈ M'.map π := Subgroup.mem_map_of_mem π hxM'
    rw [hbot, Subgroup.mem_bot] at hmem
    have hxpc : x ∈ CFSG.pCore 2 ↥L2 := (QuotientGroup.eq_one_iff _).mp hmem
    have hxpcof : (x : H) ∈ pCoreOf 2 L2 := by
      have h := (Subgroup.mem_map_iff_mem (K := CFSG.pCore 2 ↥L2) (x := x)
        L2.subtype_injective).mpr hxpc
      simpa [pCoreOf] using h
    have hp : IsPGroup 2 (pCoreOf 2 L2) := pCoreOf_isPGroup' L2
    obtain ⟨k, hk⟩ := hp ⟨(x : H), hxpcof⟩
    have hord : orderOf (⟨(x : H), hxpcof⟩ : ↥(pCoreOf 2 L2)) = 5 := by
      rw [Subgroup.orderOf_mk]; exact hx5H
    have hdvd : 5 ∣ 2 ^ k := by
      rw [← hord]
      exact orderOf_dvd_of_pow_eq_one hk
    have h52 : 5 ∣ 2 := Nat.Prime.dvd_of_dvd_pow Nat.prime_five hdvd
    norm_num at h52
  haveI hPSL : IsSimpleGroup
      (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
    apply Matrix.ProjectiveSpecialLinearGroup.rank_two_simple
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  haveI : IsSimpleGroup (↥L2 ⧸ CFSG.pCore 2 ↥L2) := by
    obtain ⟨e⟩ := h2
    exact e.isSimpleGroup
  haveI : (M'.map π).Normal := hM'normal
  have htop : M'.map π = ⊤ := by
    rcases Subgroup.Normal.eq_bot_or_eq_top (M'.map π) with h | h
    · exact absurd h hne
    · exact h
  apply le_antisymm
  · exact sup_le hM1L2 (CFSG.LieType.BorelTits.pCoreOf_le 2 L2)
  · intro l hl
    have hmem : π ⟨l, hl⟩ ∈ M'.map π := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨m', hm', hmm'⟩ := Subgroup.mem_map.mp hmem
    have hm1 : (m' : H) ∈ f112M2 L1 L2 S := Subgroup.mem_subgroupOf.mp hm'
    have hq : (m'⁻¹ * (⟨l, hl⟩ : ↥L2) : ↥L2) ∈ CFSG.pCore 2 ↥L2 := by
      have h : π (m'⁻¹ * (⟨l, hl⟩ : ↥L2)) = 1 := by
        rw [map_mul, map_inv, hmm', inv_mul_cancel]
      exact (QuotientGroup.eq_one_iff _).mp h
    have hqG : ((m'⁻¹ * (⟨l, hl⟩ : ↥L2) : ↥L2) : H) ∈ pCoreOf 2 L2 := by
      have h := (Subgroup.mem_map_iff_mem (K := CFSG.pCore 2 ↥L2)
        (x := m'⁻¹ * (⟨l, hl⟩ : ↥L2)) L2.subtype_injective).mpr hq
      simpa [pCoreOf] using h
    have hl' : (m' : H) * ((m'⁻¹ * (⟨l, hl⟩ : ↥L2) : ↥L2) : H) = l := by
      simp [mul_assoc]
    have hmem' : (m' : H) * ((m'⁻¹ * (⟨l, hl⟩ : ↥L2) : ↥L2) : H) ∈
        f112M2 L1 L2 S ⊔ pCoreOf 2 L2 :=
      (f112M2 L1 L2 S ⊔ pCoreOf 2 L2).mul_mem (Subgroup.mem_sup_left hm1)
        (Subgroup.mem_sup_right hqG)
    rwa [hl'] at hmem'

theorem f112M2_quot {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    Nonempty (↥(f112M2 L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112M2 L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf (f112M2_le_L2 hF h1 h2)
    (f112M2_normal_L2 L1 L2 S) (f112M2_sup_pCoreOf hF h1 h2)
  obtain ⟨e2⟩ := h2
  exact ⟨e1.trans e2⟩

noncomputable def f112A2 (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  (f112M2 L1 L2 S).subgroupOf (f112P2 L1 L2 S) |>.map (f112Gold L1 L2 S).ofB

noncomputable def f112Nbeta (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  f112E5 L1 L2 S ⊓ (f112Gold L1 L2 S).ofB.range

noncomputable def f112NlocalB (L1 L2 S : Subgroup H) :
    Subgroup (f112Gold L1 L2 S).Universal :=
  f112A2 L1 L2 S ⊔ pCoreOf 2 (f112Nbeta L1 L2 S)

theorem f112A2_le_E {L1 L2 S : Subgroup H} :
    f112A2 L1 L2 S ≤ f112E5 L1 L2 S := by
  let K' : Subgroup ↥(f112P2 L1 L2 S) := (f112E5 L1 L2 S).comap (f112Gold L1 L2 S).ofB
  let KH : Subgroup H := K'.map (f112P2 L1 L2 S).subtype
  have hM1KH : f112M2 L1 L2 S ≤ KH := by
    rw [f112M2]
    refine (Subgroup.closure_le _).mpr ?_
    intro y hy
    show y ∈ K'.map (f112P2 L1 L2 S).subtype
    have hgen : (⟨y, hy.1⟩ : ↥(f112P2 L1 L2 S)) ∈ K' := by
      show (f112Gold L1 L2 S).ofB ⟨y, hy.1⟩ ∈ f112E5 L1 L2 S
      refine Subgroup.subset_closure ⟨Or.inr ⟨⟨y, hy.1⟩, rfl⟩, ?_⟩
      rw [orderOf_injective (f112Gold L1 L2 S).ofB (f112Gold L1 L2 S).ofB_injective,
        Subgroup.orderOf_mk]
      exact hy.2
    exact Subgroup.mem_map_of_mem (f := (f112P2 L1 L2 S).subtype) (x := ⟨y, hy.1⟩) hgen
  rw [f112A2, Subgroup.map_le_iff_le_comap]
  intro x hx
  have hxKH : (x : H) ∈ KH := hM1KH (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.mp hxKH
  have hzx' : z = x := Subtype.ext hzx
  rw [← hzx']
  exact hz

theorem f112A2_le_Nbeta {L1 L2 S : Subgroup H} :
    f112A2 L1 L2 S ≤ f112Nbeta L1 L2 S := by
  refine le_inf f112A2_le_E ?_
  rw [f112A2]
  refine Subgroup.map_le_iff_le_comap.mpr ?_
  intro x _
  exact ⟨x, rfl⟩

theorem f112A2_conj_mem {L1 L2 S : Subgroup H} {g a : (f112Gold L1 L2 S).Universal}
    (hg : g ∈ f112Nbeta L1 L2 S) (ha : a ∈ f112A2 L1 L2 S) :
    g * a * g⁻¹ ∈ f112A2 L1 L2 S := by
  obtain ⟨m, hm, rfl⟩ := Subgroup.mem_map.mp ha
  obtain ⟨p, rfl⟩ := hg.2
  have hconj : p * m * p⁻¹ ∈ (f112M2 L1 L2 S).subgroupOf (f112P2 L1 L2 S) := by
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    exact f112M2_conj_mem p.2 hm
  have heq : (f112Gold L1 L2 S).ofB p * (f112Gold L1 L2 S).ofB m *
      ((f112Gold L1 L2 S).ofB p)⁻¹ = (f112Gold L1 L2 S).ofB (p * m * p⁻¹) := by
    rw [map_mul, map_mul, map_inv]
  rw [heq]
  exact Subgroup.mem_map_of_mem _ hconj

theorem f112A2_normal_Nbeta {L1 L2 S : Subgroup H} :
    f112Nbeta L1 L2 S ≤
      Subgroup.normalizer (f112A2 L1 L2 S : Set (f112Gold L1 L2 S).Universal) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · intro ha
    exact f112A2_conj_mem hg ha
  · intro ha
    have h := f112A2_conj_mem ((f112Nbeta L1 L2 S).inv_mem hg) ha
    simpa [mul_assoc] using h

theorem f112NlocalB_normal_Nbeta {L1 L2 S : Subgroup H} :
    f112Nbeta L1 L2 S ≤ Subgroup.normalizer
      (f112NlocalB L1 L2 S : Set (f112Gold L1 L2 S).Universal) :=
  (le_inf f112A2_normal_Nbeta
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (f112Nbeta L1 L2 S))).trans
    (Subgroup.inf_normalizer_le_normalizer_sup (f112A2 L1 L2 S)
      (pCoreOf 2 (f112Nbeta L1 L2 S)))

theorem f112NlocalB_le_Nbeta {L1 L2 S : Subgroup H} :
    f112NlocalB L1 L2 S ≤ f112Nbeta L1 L2 S :=
  sup_le f112A2_le_Nbeta (CFSG.LieType.BorelTits.pCoreOf_le 2 _)

theorem f112NlocalB_le_E {L1 L2 S : Subgroup H} :
    f112NlocalB L1 L2 S ≤ f112E5 L1 L2 S :=
  f112NlocalB_le_Nbeta.trans inf_le_left

theorem f112A2_quot {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    Nonempty (↥(f112A2 L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112A2 L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  obtain ⟨e1⟩ := f112M2_quot hF h1 h2
  let e2 : ↥(f112M2 L1 L2 S) ≃* ↥(f112A2 L1 L2 S) :=
    (Subgroup.subgroupOfEquivOfLe ((f112M2_le_L2 hF h1 h2).trans le_sup_left)).symm.trans
      (Subgroup.equivMapOfInjective
        (H := (f112M2 L1 L2 S).subgroupOf (f112P2 L1 L2 S))
        (f := (f112Gold L1 L2 S).ofB) (f112Gold L1 L2 S).ofB_injective)
  exact ⟨(pCoreQuotientMulEquiv 2 e2).symm.trans e1⟩

theorem f112NlocalB_quot {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    Nonempty (↥(f112NlocalB L1 L2 S) ⧸ CFSG.pCore 2 ↥(f112NlocalB L1 L2 S) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  obtain ⟨e1⟩ := pCore_quotient_mulEquiv_of_sup_pCoreOf_of_normal
    (M := f112A2 L1 L2 S) (K := f112Nbeta L1 L2 S) f112A2_le_Nbeta f112A2_normal_Nbeta
  obtain ⟨e2⟩ := f112A2_quot hF h1 h2
  exact ⟨e1.trans e2⟩

theorem f112NlocalB_subgroupOf_quot {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    Nonempty (↥((f112NlocalB L1 L2 S).subgroupOf (f112E5 L1 L2 S)) ⧸
        CFSG.pCore 2 ↥((f112NlocalB L1 L2 S).subgroupOf (f112E5 L1 L2 S)) ≃*
      Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 2)) := by
  obtain ⟨e1⟩ := f112NlocalB_quot hF h1 h2
  exact ⟨(pCoreQuotientMulEquiv 2
    (Subgroup.subgroupOfEquivOfLe f112NlocalB_le_E)).trans e1⟩

theorem f112A2_trans {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∀ a b : Vtx (f112Gold L1 L2 S),
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) a →
      (f112Gold L1 L2 S).treeGraph.Adj (baseB (f112Gold L1 L2 S)) b →
      ∃ g ∈ f112A2 L1 L2 S, g • a = b := by
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  intro a b ha hb
  let X := f112Gold L1 L2 S
  obtain ⟨x, hx5⟩ := exists_prime_orderOf_dvd_card' 5 (f112_five_dvd_card_L2 hF h2)
  have hx5H : orderOf (x : H) = 5 := by rw [Subgroup.orderOf_coe]; exact hx5
  have hxM1 : (x : H) ∈ f112M2 L1 L2 S :=
    Subgroup.subset_closure ⟨Subgroup.mem_sup_left x.2, hx5H⟩
  let ax : X.Universal := X.ofB ⟨(x : H), Subgroup.mem_sup_left x.2⟩
  have haxA1 : ax ∈ f112A2 L1 L2 S := by
    show X.ofB ⟨(x : H), Subgroup.mem_sup_left x.2⟩ ∈ f112A2 L1 L2 S
    exact Subgroup.mem_map_of_mem X.ofB (Subgroup.mem_subgroupOf.mpr hxM1)
  have hax5 : orderOf ax = 5 := by
    show orderOf (X.ofB ⟨(x : H), Subgroup.mem_sup_left x.2⟩) = 5
    rw [orderOf_injective X.ofB X.ofB_injective, Subgroup.orderOf_mk]
    exact hx5H
  have haxfix : ax • baseB X = baseB X := by
    have hmem : ax ∈ MulAction.stabilizer X.Universal (baseB X) := by
      rw [stabilizer_baseB]
      exact ⟨⟨(x : H), Subgroup.mem_sup_left x.2⟩, rfl⟩
    exact MulAction.mem_stabilizer_iff.mp hmem
  let P : Subgroup X.Universal := Subgroup.zpowers ax
  have hPle : P ≤ f112A2 L1 L2 S := Subgroup.zpowers_le.mpr haxA1
  have hSfin : (X.treeGraph.neighborSet (baseB X)).Finite :=
    Set.finite_of_ncard_ne_zero (by
      rw [f112_ncard_neighborSet hF h1 h2 (baseB X)]; norm_num)
  have hSncard : (X.treeGraph.neighborSet (baseB X)).ncard = 5 :=
    f112_ncard_neighborSet hF h1 h2 (baseB X)
  have hsub : MulAction.orbit P a ⊆ X.treeGraph.neighborSet (baseB X) := by
    rintro w ⟨p, rfl⟩
    have hpfix : (p : X.Universal) • baseB X = baseB X :=
      smul_eq_self_of_mem_zpowers p.2 haxfix
    show X.treeGraph.Adj (baseB X) ((p : X.Universal) • a)
    rw [← hpfix]
    exact (adj_smul X (p : X.Universal) (baseB X) a).2 ha
  have hidx : (MulAction.stabilizer P a).index ∣ 5 := by
    have h := Subgroup.index_mul_card (MulAction.stabilizer P a)
    have hP5 : Nat.card ↥P = 5 := by
      rw [show P = Subgroup.zpowers ax from rfl, Nat.card_zpowers, hax5]
    rw [hP5] at h
    exact ⟨Nat.card ↥(MulAction.stabilizer P a), h.symm⟩
  have hne : (MulAction.stabilizer P a).index ≠ 1 := by
    intro h1'
    have htop : MulAction.stabilizer P a = ⊤ := Subgroup.index_eq_one.mp h1'
    have haxP : ax ∈ P := Subgroup.mem_zpowers ax
    have hfix : ax • a = a := by
      have hmem : (⟨ax, haxP⟩ : P) ∈ MulAction.stabilizer P a := by
        rw [htop]; exact Subgroup.mem_top _
      simpa using MulAction.mem_stabilizer_iff.mp hmem
    exact f112_orderFive_not_fixed_beta hF (f112_not_five_dvd_card_bigB hF h1 h2)
      ⟨⟨(x : H), Subgroup.mem_sup_left x.2⟩, rfl⟩ hax5 ha hfix
  have hidx5 : (MulAction.stabilizer P a).index = 5 := by
    rcases (Nat.dvd_prime Nat.prime_five).mp hidx with h | h
    · exact absurd h hne
    · exact h
  have horbcard : (MulAction.orbit P a).ncard = 5 := by
    rw [← MulAction.index_stabilizer P a, hidx5]
  have heq : MulAction.orbit P a = X.treeGraph.neighborSet (baseB X) :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hSncard, horbcard]) hSfin
  have hbO : b ∈ MulAction.orbit P a := by rw [heq]; exact hb
  obtain ⟨p, hp⟩ := hbO
  exact ⟨(p : X.Universal), hPle p.2, hp⟩

theorem f112_localL2_baseB {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    ∃ N : Subgroup ↥(f112E5 L1 L2 S),
      IsLocL2 (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S)
        (baseB (f112Gold L1 L2 S)) 2 N := by
  let E := f112E5 L1 L2 S
  let X := f112Gold L1 L2 S
  let N : Subgroup ↥E := (f112NlocalB L1 L2 S).subgroupOf E
  have hstab : MulAction.stabilizer ↥E (baseB X) = (f112Nbeta L1 L2 S).subgroupOf E := by
    rw [← MulAction.stabilizer_subgroupOf E (baseB X), stabilizer_baseB X, f112Nbeta,
      Subgroup.inf_subgroupOf_left]
  refine ⟨N, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hstab]
    exact Subgroup.subgroupOf_mono E f112NlocalB_le_Nbeta
  ·
    rw [hstab]
    refine Subgroup.normal_subgroupOf_of_le_normalizer ?_
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have hkU : (k : X.Universal) ∈ f112Nbeta L1 L2 S := Subgroup.mem_subgroupOf.mp hk
    constructor
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      exact (Subgroup.mem_normalizer_iff.mp (f112NlocalB_normal_Nbeta hkU)
        (h : X.Universal)).mp hh
    · intro hh
      rw [Subgroup.mem_subgroupOf] at hh ⊢
      have hkU' : (k : X.Universal)⁻¹ ∈ f112Nbeta L1 L2 S :=
        (f112Nbeta L1 L2 S).inv_mem hkU
      have hmem := (Subgroup.mem_normalizer_iff.mp (f112NlocalB_normal_Nbeta hkU')
        ((k : X.Universal) * (h : X.Universal) * (k : X.Universal)⁻¹)).mp hh
      simpa [mul_assoc] using hmem
  ·
    rw [hstab]
    intro y hy
    rw [Subgroup.mem_subgroupOf]
    have hpc := pCoreOf_subgroupOf_map (K := f112Nbeta L1 L2 S) (E := E) inf_le_left
    have hmem : (y : X.Universal) ∈
        (pCoreOf 2 ((f112Nbeta L1 L2 S).subgroupOf E)).map E.subtype :=
      Subgroup.mem_map_of_mem E.subtype hy
    rw [hpc] at hmem
    exact (show pCoreOf 2 (f112Nbeta L1 L2 S) ≤ f112NlocalB L1 L2 S from le_sup_right) hmem
  ·
    obtain ⟨e⟩ := f112NlocalB_subgroupOf_quot hF h1 h2
    exact ⟨e⟩
  ·
    intro a b ha hb
    obtain ⟨g, hgA1, hgab⟩ := f112A2_trans hF h1 h2 a b ha hb
    refine ⟨⟨g, f112A2_le_E hgA1⟩, ?_, ?_⟩
    · show (⟨g, f112A2_le_E hgA1⟩ : ↥E) ∈ N
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.mem_sup_left hgA1
    · show g • a = b
      exact hgab

theorem f112_localL2 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) : F112LocalL2 L1 L2 S := by
  intro v
  let X := f112Gold L1 L2 S
  let E := f112E5 L1 L2 S
  have hne : (X.treeGraph.neighborSet v).Nonempty :=
    Set.nonempty_of_ncard_ne_zero (by
      rw [f112_ncard_neighborSet hF h1 h2 v]; norm_num)
  obtain ⟨w, hw⟩ := hne
  obtain ⟨g, -, hcase⟩ := f112_edgeTransitive_top hF h1 h2
    (baseA X) (baseB X) v w (adj_baseA_baseB X) hw
  have hadjE : ∀ (k : ↥E) (u w : Vtx X),
      X.treeGraph.Adj (k • u) (k • w) ↔ X.treeGraph.Adj u w :=
    fun k u w => adj_smul X (k : X.Universal) u w
  rcases hcase with ⟨hga, -⟩ | ⟨-, hgb⟩
  · obtain ⟨N, hN⟩ := f112_localL2_baseA hF h1 h2
    refine ⟨N.map (MulAut.conj g).toMonoidHom, ?_⟩
    have htrans := IsLocL2.smul (Γ := X.treeGraph) hadjE hN g
    rwa [hga] at htrans
  · obtain ⟨N, hN⟩ := f112_localL2_baseB hF h1 h2
    refine ⟨N.map (MulAut.conj g).toMonoidHom, ?_⟩
    have htrans := IsLocL2.smul (Γ := X.treeGraph) hadjE hN g
    rwa [hgb] at htrans

theorem f112_hyp30 {L1 L2 S : Subgroup H}
    (hF : F112HypW L1 L2 S) (h1 : VA5 L1) (h2 : VA5 L2) :
    Hyp30 (f112Gold L1 L2 S).treeGraph ↥(f112E5 L1 L2 S) :=
  f112_hyp30_of_localL2 hF h1 h2 (f112_localL2 hF h1 h2)

end CFSG.Quasithin.F112R.St84
