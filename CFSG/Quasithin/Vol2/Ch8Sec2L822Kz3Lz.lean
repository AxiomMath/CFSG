module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822KzFinal
public import CFSG.Quasithin.Vol2.Ch8Sec2L822R3
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Facts
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3LzCore
public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3LzSyl

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L319
open scoped IsMulCommutative commutatorElement

theorem res822_fix_iff_kz3 {G : Type} [Group G] {V L : Subgroup G} {z : G} (hzV : z ∈ V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (c : ↥L) :
    res822Act hLV c ⟨z, hzV⟩ = ⟨z, hzV⟩ ↔ (c : G) * z = z * (c : G) := by
  constructor
  · intro h
    have h4 := res822Act_apply hLV c ⟨z, hzV⟩
    rw [h] at h4
    have h5 : (c : G) * z * (c : G)⁻¹ = z := h4.symm
    rw [mul_inv_eq_iff_eq_mul] at h5
    exact h5
  · intro h
    apply Subtype.ext
    rw [res822Act_apply]
    show (c : G) * z * (c : G)⁻¹ = z
    calc (c : G) * z * (c : G)⁻¹ = (z * (c : G)) * (c : G)⁻¹ := by rw [h]
      _ = z := by group

theorem isHat_transport_kz3 {G : Type} [Group G] {X Y : Subgroup G} (h : X = Y) {S : Type} [Group S]
    (hN : ((CFSG.Open.pCoreOf 2 X).subgroupOf X).Normal)
    (hN' : ((CFSG.Open.pCoreOf 2 Y).subgroupOf Y).Normal)
    (hX : IsHat (↥X ⧸ (CFSG.Open.pCoreOf 2 X).subgroupOf X) S) :
    IsHat (↥Y ⧸ (CFSG.Open.pCoreOf 2 Y).subgroupOf Y) S := by
  subst h
  exact hX

theorem kzLzInput_kz2_holds
    (h711n : Stmt7_1_1_normal) (h3228 : Stmt3_2_2_eight) (h3cov : Res822ThreeCover)
    (hN1 : KzM22Sub5760_kz3) (hN2 : KzM22Cover17280_kz3) (hN3 : KzCodeHexad5760_kz3) :
    KzLzInput_kz2 := by
  intro G _ _ T L I hyp h731 h821 hc hrow hrowM hnot0 H hH hVH z hz1 hzV _ _ hTz
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := le_normalizer_of_case82 h711n hyp hrow
  have hL0 : fsuL0 T L = L := fsuL0_eq_of_le_normalizer hTL
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    obtain ⟨-, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
    rw [hL0] at hN
    exact le_sup_left.trans hN
  have hM : MathieuCode22 (autOn L (fsuV T I)) ⊤ ⊥ := by
    have h := hrowM
    unfold Row711M22Code at h
    rw [hL0] at h
    exact h
  have hnot : ¬ autOn T (fsuV T I) ≤ autOn L (fsuV T I) := by
    have h := hnot0
    rwa [hL0] at h
  have hLM : L ≤ fsuM T L := by
    show L ≤ Subgroup.normalizer ((fsuL0 T L : Subgroup G) : Set G)
    rw [hL0]
    exact Subgroup.le_normalizer
  have hT2 : quasithinIsSylowTwo T := hyp.fsu.sylow
  have hQ : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L) := hyp.fsu.quasisimple
  obtain ⟨eA⟩ := res822_autOn_iso hM
  have hA : Nonempty (↥(autOn L (fsuV T I)) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) := ⟨eA⟩
  obtain ⟨ψ, hψs, hψker, hψ⟩ := res822_psi_of hLV hA hQ
  have hker := res822_pCore_le_ker' hLV hA
  have hcardA : Nat.card ↥(autOn L (fsuV T I)) = 443520 :=
    (Nat.card_congr eA.toEquiv).trans CFSG.Sporadic.Mathieu.card_M22
  have hRN : autOn T (fsuV T I) ≤ Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
    CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hTL
  have hRp : IsPGroup 2 ↥(autOn T (fsuV T I)) := CFSG.Quasithin.AutOn.isPGroup_autOn hT2.1
  have hSyl : Nat.card ↥(autOn T (fsuV T I) ⊓ autOn L (fsuV T I)) = 128 :=
    card_inf_autOn_kz3 hT2 hTL hLV hcardA
  have hz'ne : (⟨z, hzV⟩ : ↥(fsuV T I)) ≠ 1 := fun h => hz1 (congrArg Subtype.val h)
  have hz'fix : ∀ r ∈ autOn T (fsuV T I), r ⟨z, hzV⟩ = ⟨z, hzV⟩ :=
    fun r hr => autOn_fix_kz3 hTz hzV r hr
  have hK5760 : Nat.card ↥(autOn L (fsuV T I) ⊓ kzFix_kz3 (⟨z, hzV⟩ : ↥(fsuV T I))) = 5760 :=
    hN3 (fsuV T I) (autOn L (fsuV T I)) hM (autOn T (fsuV T I)) hRN hRp hnot hSyl ⟨z, hzV⟩ hz'ne hz'fix
  obtain ⟨Pq, hPqdef⟩ : ∃ P : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L),
      P = (((autOn L (fsuV T I)) ⊓ kzFix_kz3 (⟨z, hzV⟩ : ↥(fsuV T I))).subgroupOf
        (autOn L (fsuV T I))).comap ψ := ⟨_, rfl⟩
  have hS''card : Nat.card ↥(((autOn L (fsuV T I)) ⊓ kzFix_kz3 (⟨z, hzV⟩ : ↥(fsuV T I))).subgroupOf
      (autOn L (fsuV T I))) = 5760 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).trans hK5760
  have hPq_card : Nat.card ↥Pq = Nat.card ↥ψ.ker * 5760 := by
    rw [hPqdef, card_comap_kz3 ψ hψs, hS''card]
  have hPmem : ∀ c : ↥L, (QuotientGroup.mk c : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Pq ↔
      (c : G) * z = z * (c : G) := by
    intro c
    rw [hPqdef, Subgroup.mem_comap, hψ c, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      exact (res822_fix_iff_kz3 hzV hLV c).mp h.2
    · intro h
      exact ⟨(res822Act' hLV c).2, (res822_fix_iff_kz3 hzV hLV c).mpr h⟩
  have hPC : Pq = (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    ext q
    constructor
    · intro hq
      obtain ⟨c, rfl⟩ := QuotientGroup.mk_surjective q
      refine Subgroup.mem_map.mpr ⟨c, ?_, rfl⟩
      exact Subgroup.mem_centralizer_singleton_iff.mpr ((hPmem c).mp hq)
    · intro hq
      obtain ⟨c, hc, hcq⟩ := Subgroup.mem_map.mp hq
      rw [← hcq]
      exact (hPmem c).mpr (Subgroup.mem_centralizer_singleton_iff.mp hc)
  have hM0 : CFSG.pCore 2 ↥L ≤ Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)) := by
    intro m hm
    have h1 : res822Act' hLV m = 1 := MonoidHom.mem_ker.mp (hker hm)
    have h2 : res822Act hLV m = 1 := congrArg Subtype.val h1
    have h3 : res822Act hLV m ⟨z, hzV⟩ = ⟨z, hzV⟩ := by
      rw [h2]
      rfl
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((res822_fix_iff_kz3 hzV hLV m).mp h3)
  by_cases hNT : NoThreeInCV (fsuM T L) (fsuV T I)
  ·
    have hdvd12 : Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) ∣ 12 :=
      schurM22_holds _ hQ _ le_rfl
        ⟨(QuotientGroup.quotientMulEquivOfEq hψker.symm).trans
          ((QuotientGroup.quotientKerEquivOfSurjective ψ hψs).trans eA)⟩
    have hinj := injective_of_noThree_kz3 hLV hLM hNT hQ ψ hψ hψker hdvd12
    have hQM22 : Nonempty ((↥L ⧸ CFSG.pCore 2 ↥L) ≃* CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      ⟨(MulEquiv.ofBijective ψ ⟨hinj, hψs⟩).trans eA⟩
    have hkerbot : ψ.ker = ⊥ := (MonoidHom.ker_eq_bot_iff ψ).mpr hinj
    have hcardP : Nat.card ↥Pq = 5760 := by
      rw [hPq_card, hkerbot, Subgroup.card_bot, one_mul]
    have hne : Pq ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcardP
      norm_num at hcardP
    obtain ⟨hperfP, hA6P⟩ := hN1 _ hQM22 Pq hcardP
    obtain ⟨Lz, hLzC, hLzperf, hLzne, hLzT, eLz⟩ :=
      lz_construct_kz3 L T z hTL hTz Pq hPC hM0 hperfP hne
    obtain ⟨eLz⟩ := eLz
    obtain ⟨eA6⟩ := hA6P
    have hA6Lz : IsAlt 6 (↥Lz ⧸ CFSG.pCore 2 ↥Lz) := ⟨eLz.trans eA6⟩
    have hqs : CFSG.IsQuasisimple (↥Lz ⧸ CFSG.pCore 2 ↥Lz) := by
      obtain ⟨e6⟩ := hA6Lz
      exact isQuasisimple_of_isAlt6_kz3 e6
    have hcc := quasithinIsCComponent_kz3 hLzperf hLzne hLzT hqs
    exact ⟨Lz, hLzC, hLzT, hcc, fun _ => hA6Lz, fun h => absurd hNT h⟩
  ·
    have hCov := h3cov G T L I hyp h731 h821 hc hrow hrowM hnot0 hNT
    obtain ⟨hN0, hIsHat0⟩ := hCov
    have hS : (CFSG.Open.pCoreOf 2 L).subgroupOf L = CFSG.pCore 2 ↥L := by
      unfold CFSG.Open.pCoreOf
      rw [← Subgroup.comap_subtype, Subgroup.comap_map_eq_self_of_injective Subtype.val_injective]
    have hNL : ((CFSG.Open.pCoreOf 2 L).subgroupOf L).Normal := by
      rw [hS]
      infer_instance
    have hIsHatL := isHat_transport_kz3 hL0 hN0 hNL hIsHat0
    have hIsHat : IsHat (↥L ⧸ CFSG.pCore 2 ↥L) (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      IsHat.of_mulEquiv (QuotientGroup.quotientMulEquivOfEq hS) hIsHatL
    have hcenter : Nat.card ↥(Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = 3 := hIsHat.2.1
    have hkerCard : Nat.card ↥ψ.ker = 3 := by
      rw [hψker]
      exact hcenter
    have hcardP : Nat.card ↥Pq = 17280 := by
      rw [hPq_card, hkerCard]
    have hcenPq : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) ≤ Pq := by
      intro x hx
      have hx' : x ∈ ψ.ker := by
        rw [hψker]
        exact hx
      rw [hPqdef, Subgroup.mem_comap, MonoidHom.mem_ker.mp hx']
      exact one_mem _
    obtain ⟨hperfP, hIsHatP⟩ := hN2 _ hIsHat Pq hcenPq hcardP
    have hne : Pq ≠ ⊥ := fun h => by
      rw [h, Subgroup.card_bot] at hcardP
      norm_num at hcardP
    obtain ⟨Lz, hLzC, hLzperf, hLzne, hLzT, eLz⟩ :=
      lz_construct_kz3 L T z hTL hTz Pq hPC hM0 hperfP hne
    obtain ⟨eLz⟩ := eLz
    have hIsHatLz : IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6)) :=
      IsHat.of_mulEquiv eLz.symm hIsHatP
    have hqs : CFSG.IsQuasisimple (↥Lz ⧸ CFSG.pCore 2 ↥Lz) := hIsHatLz.1
    have hcc := quasithinIsCComponent_kz3 hLzperf hLzne hLzT hqs
    exact ⟨Lz, hLzC, hLzT, hcc, fun h => absurd h hNT, fun _ => hIsHatLz⟩

end CFSG.Quasithin.H13
