module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Lz
public import CFSG.Quasithin.Vol2.Ch8Sec2L822R2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H13.L319
open scoped IsMulCommutative commutatorElement

theorem lz_construct_cov {G : Type} [Group G] [Finite G] (L T : Subgroup G) (z : G)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hTz : T ≤ Subgroup.centralizer ({z} : Set G))
    (Pq : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L))
    (hPC : Pq = (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
    (hM0 : CFSG.pCore 2 ↥L ≤ Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)))
    (hperf : ⁅Pq, Pq⁆ = Pq) (hne : Pq ≠ ⊥) :
    ∃ Lz : Subgroup G, Lz ≤ Subgroup.centralizer ({z} : Set G) ∧ Lz ≤ L ∧ ⁅Lz, Lz⁆ = Lz ∧ Lz ≠ ⊥ ∧
      T ≤ Subgroup.normalizer (Lz : Set G) ∧
      Nonempty (↥Lz ⧸ CFSG.pCore 2 ↥Lz ≃* ↥Pq ⧸ CFSG.pCore 2 ↥Pq) ∧
      (∀ x ∈ L, x * z = z * x → Odd (orderOf x) → x ∈ Lz) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hperf' : ⁅(Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
      (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L))⁆ =
      (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))).map
      (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [← hPC]
    exact hperf
  have hsup := sup_perfectCore_eq_kz3 hM0 hperf'
  have hM0f : (CFSG.pCore 2 ↥L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨h, hh, rfl⟩
    rw [Subgroup.mem_bot]
    exact (QuotientGroup.eq_one_iff h).mpr hh
  set Λ := CFSG.Quasithin.perfectCore (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))) with hΛ
  have hΛC : Λ ≤ Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)) :=
    CFSG.Quasithin.perfectCore_le _
  have hPΛ : Pq = Λ.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
    rw [hPC]
    conv_lhs => rw [← hsup]
    rw [Subgroup.map_sup, hM0f, sup_bot_eq]
  have hΛperf : ⁅Λ, Λ⁆ = Λ := CFSG.Quasithin.perfectCore_perfect _
  refine ⟨Λ.map L.subtype, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hx
    exact hΛC hc
  · exact Subgroup.map_subtype_le Λ
  · rw [← Subgroup.map_commutator, hΛperf]
  · intro hL
    apply hne
    have hΛbot : Λ = ⊥ := by
      rw [eq_bot_iff]
      intro c hc
      have h1 : L.subtype c ∈ Λ.map L.subtype := Subgroup.mem_map_of_mem _ hc
      rw [hL, Subgroup.mem_bot] at h1
      rw [Subgroup.mem_bot]
      exact Subtype.ext h1
    rw [hPΛ, hΛbot, Subgroup.map_bot]
  · have hmax : ∀ K : Subgroup G, ⁅K, K⁆ = K → K ≤ L → K ≤ Subgroup.centralizer ({z} : Set G) →
        K ≤ Λ.map L.subtype := by
      intro K hKperf hKL hKC
      have hK'C : K.comap L.subtype ≤ Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)) :=
        fun y hy => hKC hy
      have hK'Λ : K.comap L.subtype ≤ Λ :=
        CFSG.Quasithin.le_perfectCore_of_perfect hK'C (perfect_comap_subtype_kz3 hKL hKperf)
      rw [← map_comap_subtype_eq_kz3 hKL]
      exact Subgroup.map_mono hK'Λ
    have hconj : ∀ t ∈ T, ∀ x ∈ Λ.map L.subtype, t * x * t⁻¹ ∈ Λ.map L.subtype := by
      intro t ht x hx
      have hLzperf : ⁅Λ.map L.subtype, Λ.map L.subtype⁆ = Λ.map L.subtype := by
        rw [← Subgroup.map_commutator, hΛperf]
      have hKperf : ⁅(Λ.map L.subtype).map (MulAut.conj t).toMonoidHom,
          (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom⁆ =
          (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom := by
        rw [← Subgroup.map_commutator, hLzperf]
      have hKL : (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom ≤ L := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨c, _, rfl⟩ := Subgroup.mem_map.mp hy
        have hyL : (c : G) ∈ L := c.2
        exact (Subgroup.mem_normalizer_iff.mp (hTL ht) (c : G)).mp hyL
      have hKC : (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom ≤
          Subgroup.centralizer ({z} : Set G) := by
        rintro _ ⟨y, hy, rfl⟩
        obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hy
        have hcz : (c : G) * z = z * (c : G) := Subgroup.mem_centralizer_singleton_iff.mp (hΛC hc)
        have htz : t * z = z * t := Subgroup.mem_centralizer_singleton_iff.mp (hTz ht)
        have htz' : t⁻¹ * z = z * t⁻¹ := by
          calc t⁻¹ * z = t⁻¹ * (z * t) * t⁻¹ := by group
            _ = t⁻¹ * (t * z) * t⁻¹ := by rw [htz]
            _ = z * t⁻¹ := by group
        apply Subgroup.mem_centralizer_singleton_iff.mpr
        show t * (c : G) * t⁻¹ * z = z * (t * (c : G) * t⁻¹)
        calc t * (c : G) * t⁻¹ * z = t * (c : G) * (t⁻¹ * z) := by group
          _ = t * (c : G) * (z * t⁻¹) := by rw [htz']
          _ = t * ((c : G) * z) * t⁻¹ := by group
          _ = t * (z * (c : G)) * t⁻¹ := by rw [hcz]
          _ = (t * z) * (c : G) * t⁻¹ := by group
          _ = (z * t) * (c : G) * t⁻¹ := by rw [htz]
          _ = z * (t * (c : G) * t⁻¹) := by group
      have hmem := hmax _ hKperf hKL hKC
      have hx' : (MulAut.conj t).toMonoidHom x ∈ (Λ.map L.subtype).map (MulAut.conj t).toMonoidHom :=
        Subgroup.mem_map_of_mem _ hx
      exact hmem hx'
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact hconj t ht x hx
    · intro hx
      have h1 := hconj t⁻¹ (T.inv_mem ht) _ hx
      have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
      rwa [e] at h1
  · have hM0mem : ∀ y : ↥L, (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) y = 1 →
        ∃ n : ℕ, y ^ 2 ^ n = 1 := by
      intro y hy
      have hy' : y ∈ CFSG.pCore 2 ↥L := (QuotientGroup.eq_one_iff y).mp hy
      obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨y, hy'⟩
      exact ⟨n, by simpa using congrArg Subtype.val hn⟩
    let e0 : ↥Λ ≃* ↥(Λ.map L.subtype) := Subgroup.equivMapOfInjective Λ L.subtype L.subtype_injective
    let φ1 : ↥Λ →* ↥Pq := ((QuotientGroup.mk' (CFSG.pCore 2 ↥L)).comp Λ.subtype).codRestrict Pq
      (fun x => by rw [hPΛ]; exact Subgroup.mem_map_of_mem _ x.2)
    have hφ1 : Function.Surjective φ1 := by
      intro q
      have hq : (q : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ Λ.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) := by
        rw [← hPΛ]
        exact q.2
      obtain ⟨x, hx, hxq⟩ := Subgroup.mem_map.mp hq
      exact ⟨⟨x, hx⟩, Subtype.ext hxq⟩
    let φ2 : ↥(Λ.map L.subtype) →* ↥Pq := φ1.comp e0.symm.toMonoidHom
    have hφ2 : Function.Surjective φ2 := hφ1.comp e0.symm.surjective
    have hK : ∀ x : ↥(Λ.map L.subtype), φ2 x = 1 → ∃ k : ℕ, x ^ 2 ^ k = 1 := by
      intro x hx
      have h1 : φ1 (e0.symm x) = 1 := hx
      have hlam : (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) ((e0.symm x : ↥Λ) : ↥L) = 1 :=
        congrArg Subtype.val h1
      obtain ⟨n, hn⟩ := hM0mem _ hlam
      refine ⟨n, ?_⟩
      have h3 : (e0.symm x) ^ 2 ^ n = 1 := by
        apply Subtype.ext
        simpa using hn
      have h4 := congrArg e0 h3
      rw [map_pow, MulEquiv.apply_symm_apply, map_one] at h4
      exact h4
    exact pCore_quot_equiv_kz3 φ2 hφ2 hK
  · intro x hxL hxz hodd
    haveI hNO : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
    have hxC0 : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)) := by
      rw [Subgroup.mem_comap]
      exact Subgroup.mem_centralizer_singleton_iff.mpr hxz
    have hxC := hxC0
    rw [← hsup] at hxC
    obtain ⟨j, hjΛ, o, hoO, hjo⟩ := Subgroup.mem_sup_of_normal_right.mp hxC
    have hSn : ∀ h ∈ Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)), ∀ s ∈ Λ,
        h * s * h⁻¹ ∈ Λ := by
      intro h hh s hs
      have h1 : (⟨s, hΛC hs⟩ : ↥(Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)))) ∈
          Λ.subgroupOf (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G))) :=
        Subgroup.mem_subgroupOf.mpr hs
      have h2 := (CFSG.Quasithin.perfectCore_normal
        (Subgroup.comap L.subtype (Subgroup.centralizer ({z} : Set G)))).conj_mem _ h1 ⟨h, hh⟩
      exact Subgroup.mem_subgroupOf.mp h2
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨o, hoO⟩
    have hok : o ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hodd' : Odd (orderOf (⟨x, hxL⟩ : ↥L)) := by
      rw [← Subgroup.orderOf_coe]
      exact hodd
    have hoΛ : o ∈ Λ :=
      res822_o_mem hΛC hSn hxC0 hjΛ (hM0 hoO) hjo.symm hodd' (pow_orderOf_eq_one _) hok
    have hxΛ : (⟨x, hxL⟩ : ↥L) ∈ Λ := by
      rw [← hjo]
      exact Λ.mul_mem hjΛ hoΛ
    exact ⟨⟨x, hxL⟩, hxΛ, rfl⟩

theorem cov_lz_exists
    (h711n : Stmt7_1_1_normal) (h3228 : Stmt3_2_2_eight)
    (hN2 : KzM22Cover17280_kz3) (hN3 : KzCodeHexad5760_kz3)
    {G : Type} [Group G] [Finite G] {T L I : Subgroup G} (hyp : Hyp7_0_2 G T L I)
    [hc : IsMulCommutative ↥(fsuV T I)] (hrow : Case8_2 T L I) (hrowM : Row711M22Code T L I)
    (hnot0 : ¬ autOn T (fsuV T I) ≤ autOn (fsuL0 T L) (fsuV T I))
    (hcov : CoverM22 T L) {z : G} (hz1 : z ≠ 1) (hzV : z ∈ fsuV T I)
    (hTz : T ≤ Subgroup.centralizer ({z} : Set G)) :
    ∃ Lz : Subgroup G, Lz ≤ Subgroup.centralizer ({z} : Set G) ∧ Lz ≤ L ∧
      T ≤ Subgroup.normalizer (Lz : Set G) ∧ Lz ∈ lFamily T ∧ ⁅Lz, Lz⁆ = Lz ∧
      IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6)) ∧
      (∀ x ∈ L, x * z = z * x → Odd (orderOf x) → x ∈ Lz) := by
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
  obtain ⟨hN0, hIsHat0⟩ := hcov
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
  obtain ⟨Lz, hLzC, hLzL, hLzperf, hLzne, hLzT, eLz, hodd⟩ :=
    lz_construct_cov L T z hTL hTz Pq hPC hM0 hperfP hne
  obtain ⟨eLz⟩ := eLz
  have hIsHatLz : IsHat (↥Lz ⧸ CFSG.pCore 2 ↥Lz) (alternatingGroup (Fin 6)) :=
    IsHat.of_mulEquiv eLz.symm hIsHatP
  have hqs : CFSG.IsQuasisimple (↥Lz ⧸ CFSG.pCore 2 ↥Lz) := hIsHatLz.1
  have hcc := quasithinIsCComponent_kz3 hLzperf hLzne hLzT hqs
  exact ⟨Lz, hLzC, hLzL, hLzT, hcc, hLzperf, hIsHatLz, hodd⟩

end CFSG.Quasithin.H13
