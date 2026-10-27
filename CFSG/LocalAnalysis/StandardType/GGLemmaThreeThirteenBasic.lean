module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoprime
public import CFSG.LocalAnalysis.ComponentInitial.CommutingBlock
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.ControlCore
public import CFSG.Assembly.Subnormal

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Basic

variable {G : Type} [Group G]

theorem ggAssemblyIsSubnormal_iff {K L : Subgroup G} (hKL : K ≤ L) :
    CFSG.Assembly.IsSubnormal K L ↔ (K.subgroupOf L).IsSubnormal :=
  CFSG.Assembly.IsSubnormal.iff_subgroupOf hKL

theorem ggIsPGroup_zpowers {p : ℕ} {e : G} (he : e ^ p = 1) :
    IsPGroup p (Subgroup.zpowers e) := by
  intro g
  refine ⟨1, Subtype.ext ?_⟩
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
  rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one, ← hn, ← zpow_natCast, ← zpow_mul,
    mul_comm, zpow_mul, zpow_natCast, he, one_zpow]

theorem ggExists_ne_one_of_card {p : ℕ} (hp : p.Prime) {E : Subgroup G}
    (hEcard : Nat.card E = p ^ 2) : ∃ e ∈ E, e ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
  rw [hbot, Subgroup.card_bot] at hEcard
  have h1 : 1 < p ^ 2 := Nat.one_lt_pow (by norm_num) hp.one_lt
  omega

end Basic

section Index

variable {G : Type} [Group G] [Finite G]

theorem ggRelIndex_dvd_of_le_normalizer {R K N : Subgroup G} (hRN : R ≤ N) (hKN : K ≤ N)
    (hRK : R ≤ Subgroup.normalizer (K : Set G)) : R.relIndex K ∣ R.relIndex N := by
  set M := Subgroup.normalizer (K : Set G)
  have hKM : K ≤ M := Subgroup.le_normalizer
  have hnorm : (K.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKM).mpr le_rfl
  have hsup : K.relIndex (R ⊔ K) = K.relIndex R := by
    have h := Subgroup.relIndex_sup_right (H := R.subgroupOf M) (K := K.subgroupOf M)
    rw [← Subgroup.subgroupOf_sup hRK hKM, Subgroup.relIndex_subgroupOf (sup_le hRK hKM),
      Subgroup.relIndex_subgroupOf hRK] at h
    exact h
  have h1 : R.relIndex K * K.relIndex N = (R ⊓ K).relIndex N := by
    have h := Subgroup.relIndex_inf_mul_relIndex (H := R) (K := K) (L := N)
    rwa [inf_eq_left.mpr hKN] at h
  have h2 : K.relIndex R * R.relIndex N = (R ⊓ K).relIndex N := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ (inf_le_left : R ⊓ K ≤ R) hRN
    rwa [Subgroup.inf_relIndex_left] at h
  have h3 : K.relIndex R * (R ⊔ K).relIndex N = K.relIndex N := by
    have h := Subgroup.relIndex_mul_relIndex _ _ _ (le_sup_right : K ≤ R ⊔ K) (sup_le hRN hKN)
    rwa [hsup] at h
  have hpos : 0 < K.relIndex R :=
    Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite (H := K.subgroupOf R))
  have key : K.relIndex R * (R.relIndex K * (R ⊔ K).relIndex N) =
      K.relIndex R * R.relIndex N := by
    rw [h2, ← h1, ← h3]
    ring
  exact Dvd.intro _ (Nat.eq_of_mul_eq_mul_left hpos key)

theorem ggNot_dvd_card_of_central {p : ℕ} [Fact p.Prime] {K R : Subgroup G}
    (hK : commutator K = ⊤) (hRC : R ≤ Subgroup.centralizer (K : Set G))
    (hR : ¬ p ∣ R.relIndex K) : ¬ p ∣ Nat.card K := by
  intro hdvd
  have hZ : R.subgroupOf K ≤ Subgroup.center K := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    have hc := Subgroup.mem_centralizer_iff.mp (hRC (Subgroup.mem_subgroupOf.mp hx)) y y.2
    exact Subtype.ext hc
  have hidx : ¬ p ∣ (Subgroup.center K).index := fun h =>
    hR (h.trans (Subgroup.index_dvd_of_le hZ))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := K) p hdvd
  have hpow : x ^ (Subgroup.center K).index = 1 := by
    have hker : x ∈ (MonoidHom.transferCenterPow K).ker :=
      Abelianization.commutator_subset_ker _ (hK ▸ Subgroup.mem_top x)
    have h1 := congrArg Subtype.val (MonoidHom.mem_ker.mp hker)
    rwa [MonoidHom.transferCenterPow_apply] at h1
  exact hidx (hx ▸ orderOf_dvd_of_pow_eq_one hpow)

theorem ggLe_pPrimeCore_of_isSubnormal {p : ℕ} [Fact p.Prime] {N : Subgroup G}
    (hN : N.IsSubnormal) (hcop : ¬ p ∣ Nat.card N) : N ≤ CFSG.pPrimeCore p G := by
  have hcop' : Nat.Coprime p (Nat.card N) := (Nat.Prime.coprime_iff_not_dvd Fact.out).2 hcop
  have htop : CFSG.pPrimeCore p N = ⊤ :=
    top_unique (le_sSup ⟨inferInstance, by rwa [Subgroup.card_top]⟩)
  have h := CFSG.LocalCores.prime_set_core_subnormal_intersection
    {q : Nat.Primes | q.val ≠ p} hN
  rw [← CFSG.pPrimeCore_eq_piCore, ← CFSG.pPrimeCore_eq_piCore, htop, ← MonoidHom.range_eq_map,
    Subgroup.range_subtype] at h
  exact inf_eq_left.mp h.symm

end Index

section Fusion

variable {G : Type} [Group G] [Finite G] {p : ℕ} {H E : Subgroup G}

namespace GGControlsStrongFusion

theorem le_of_isPGroup [Fact p.Prime] (h : GGControlsStrongFusion H E) {e : G} (he : e ∈ E)
    (he1 : e ≠ 1) {R : Subgroup G} (hR : IsPGroup p R) (heR : e ∈ R) : R ≤ H := by
  have hnil : Group.IsNilpotent R := hR.isNilpotent
  have hle : Subgroup.zpowers e ≤ R := Subgroup.zpowers_le.mpr heR
  have hsn : ((Subgroup.zpowers e).subgroupOf R).IsSubnormal :=
    CFSG.GorensteinWalter.isSubnormal_of_nilpotent hnil _ hle
  exact h.le_of_isSubnormal he he1 (Subgroup.mem_zpowers e)
    (Subgroup.zpowers_le.mpr (h.1 he)) ((ggAssemblyIsSubnormal_iff hle).mpr hsn)

theorem le_of_coprime (hp : p.Prime) (h : GGControlsStrongFusion H E) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) {Q : Subgroup G} (hQ : ¬ p ∣ Nat.card Q)
    (hEQ : E ≤ Subgroup.normalizer (Q : Set G)) : Q ≤ H := by
  rw [CFSG.RankThreeEvenClassification.Helpers.coprime_centralizer_generation_of_plane p hp E Q
    (fun e => Subtype.ext (by simpa using hE.2 e e.2)) hEcard hQ hEQ]
  refine iSup_le fun e => iSup_le fun he1 => ?_
  have he1' : (e : G) ≠ 1 := fun h1 => he1 (Subtype.ext h1)
  exact inf_le_right.trans (h.centralizer_le e.2 he1')

theorem pPrimeCore_le (hp : p.Prime) (h : GGControlsStrongFusion H E) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) : CFSG.pPrimeCore p G ≤ H := by
  have : Fact p.Prime := ⟨hp⟩
  refine h.le_of_coprime hp hE hEcard
    ((hp.coprime_iff_not_dvd).mp CFSG.pPrimeCore_coprime_card) ?_
  have hN : (CFSG.pPrimeCore p G).Normal := CFSG.pPrimeCore_normal
  exact Subgroup.le_normalizer_of_normal

theorem pCore_le (hp : p.Prime) (h : GGControlsStrongFusion H E) (hE : IsElemAbelian p E)
    (hEcard : Nat.card E = p ^ 2) (q : ℕ) [hq : Fact q.Prime] : CFSG.pCore q G ≤ H := by
  have : Fact p.Prime := ⟨hp⟩
  have hN : (CFSG.pCore q G).Normal := CFSG.pCore_normal
  by_cases hqp : q = p
  · subst hqp
    obtain ⟨e, he, he1⟩ := ggExists_ne_one_of_card hp hEcard
    have hR : IsPGroup q ↥(CFSG.pCore q G ⊔ Subgroup.zpowers e) :=
      IsPGroup.to_sup_of_normal_left CFSG.pCore_isPGroup (ggIsPGroup_zpowers (hE.2 e he))
    exact le_sup_left.trans
      (h.le_of_isPGroup he he1 hR (le_sup_right (a := CFSG.pCore q G) (Subgroup.mem_zpowers e)))
  · refine h.le_of_coprime hp hE hEcard ?_ ?_
    · intro hdvd
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := q)).mp (CFSG.pCore_isPGroup (p := q) (G := G))
      rw [hn] at hdvd
      exact hqp ((Nat.prime_dvd_prime_iff_eq hp hq.out).mp (hp.dvd_of_dvd_pow hdvd)).symm
    · exact Subgroup.le_normalizer_of_normal

theorem exists_sylow_le [Fact p.Prime] (h : GGControlsStrongFusion H E) (hE : IsElemAbelian p E)
    {e : G} (he : e ∈ E) (he1 : e ≠ 1) {K : Subgroup G}
    (heK : e ∈ Subgroup.normalizer (K : Set G)) :
    ∃ R : Subgroup G, R ≤ H ⊓ K ∧ IsPGroup p R ∧ ¬ p ∣ R.relIndex K := by
  set N := Subgroup.normalizer (K : Set G)
  let e' : N := ⟨e, heK⟩
  have he'p : e' ^ p = 1 := Subtype.ext (by simpa using hE.2 e he)
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow (ggIsPGroup_zpowers he'p)
  set R₀ : Subgroup G := (P : Subgroup N).map N.subtype
  have hR₀p : IsPGroup p R₀ := P.isPGroup'.map _
  have heR₀ : e ∈ R₀ := ⟨e', hP (Subgroup.mem_zpowers e'), rfl⟩
  have hR₀H : R₀ ≤ H := h.le_of_isPGroup he he1 hR₀p heR₀
  have hR₀N : R₀ ≤ N := Subgroup.map_subtype_le _
  have hidx : ¬ p ∣ R₀.relIndex N := by
    have hsub : R₀.subgroupOf N = (P : Subgroup N) :=
      Subgroup.comap_map_eq_self_of_injective N.subtype_injective _
    rw [Subgroup.relIndex, hsub]
    exact P.not_dvd_index
  refine ⟨R₀ ⊓ K, inf_le_inf_right K hR₀H, hR₀p.to_inf_left, ?_⟩
  rw [Subgroup.inf_relIndex_right]
  exact fun hdvd => hidx (hdvd.trans
    (ggRelIndex_dvd_of_le_normalizer hR₀N Subgroup.le_normalizer hR₀N))

theorem not_inf_le_centralizer [Fact p.Prime] (h : GGControlsStrongFusion H E)
    (hE : IsElemAbelian p E) {e : G} (he : e ∈ E) (he1 : e ≠ 1) {K : Subgroup G}
    (heK : e ∈ Subgroup.normalizer (K : Set G)) (hK : commutator K = ⊤)
    (hKp : p ∣ Nat.card K) : ¬ H ⊓ K ≤ Subgroup.centralizer (K : Set G) := by
  intro hc
  obtain ⟨R, hRHK, -, hR⟩ := h.exists_sylow_le hE he he1 heK
  exact ggNot_dvd_card_of_central hK (hRHK.trans hc) hR hKp

end GGControlsStrongFusion

end Fusion

end CFSG.StandardType
