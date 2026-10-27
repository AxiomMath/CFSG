module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822Kz3Steps1b
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Quot

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin

theorem kzMkCommOfComm_kz3 {X : Type} [Group X] {N : Subgroup X} [N.Normal] {a b : X}
    (h : a * b * a⁻¹ * b⁻¹ ∈ N) :
    (QuotientGroup.mk a : X ⧸ N) * QuotientGroup.mk b = QuotientGroup.mk b * QuotientGroup.mk a := by
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
  have hc : (a * b * a⁻¹ * b⁻¹)⁻¹ ∈ N := N.inv_mem h
  have hconj := Subgroup.Normal.conj_mem ‹N.Normal› _ hc (a * b)⁻¹
  convert hconj using 1
  group

theorem kzMemPCoreOfMemPCoreOf_kz3 {G : Type} [Group G] {Gz L : Subgroup G} (hLG : L ≤ Gz)
    (x : ↥L) (hx : (x : G) ∈ pCoreOf 2 Gz) : x ∈ CFSG.pCore 2 ↥L := by
  classical
  let ι : ↥L →* ↥Gz := Subgroup.inclusion hLG
  have hxG : (x : G) ∈ Gz := hLG x.2
  have hPx : (⟨(x : G), hxG⟩ : ↥Gz) ∈ CFSG.pCore 2 ↥Gz :=
    (CFSG.Quasithin.P134.mem_pCoreOf_iff hxG).mp hx
  have hnorm : ((CFSG.pCore 2 ↥Gz).comap ι).Normal := inferInstance
  have hp2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥Gz).comap ι) := by
    intro y
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥Gz)) ⟨ι y, y.2⟩
    refine ⟨n, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    have h1 : ι (y ^ 2 ^ n) = 1 := by
      rw [map_pow]
      have h2 := congrArg Subtype.val hn
      simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2 ⊢
      exact h2
    have h3 := congrArg Subtype.val h1
    simpa [ι] using h3
  have hle : (CFSG.pCore 2 ↥Gz).comap ι ≤ CFSG.pCore 2 ↥L := le_sSup ⟨hnorm, hp2⟩
  apply hle
  exact hPx

theorem kzIsPGroupPCoreOf_kz3 {G : Type} [Group G] (H : Subgroup G) :
    IsPGroup 2 ↥(CFSG.Open.pCoreOf 2 H) := by
  rintro ⟨y, hy⟩
  have hy' : y ∈ (CFSG.pCore 2 ↥H).map H.subtype := hy
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy'
  obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥H)) ⟨z, hz⟩
  refine ⟨n, ?_⟩
  apply Subtype.ext
  have h1 : z ^ 2 ^ n = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  simpa [Subgroup.coe_pow] using congrArg (fun w : ↥H => (w : G)) h1

theorem kzMemModO2Image_kz3 {G : Type} [Group G] {Gz Y : Subgroup G}
    {a : ↥Gz ⧸ CFSG.pCore 2 ↥Gz} :
    a ∈ CFSG.Quasithin.modO2Image Gz Y ↔
      ∃ y ∈ Y, ∃ hy : y ∈ Gz, QuotientGroup.mk' (CFSG.pCore 2 ↥Gz) ⟨y, hy⟩ = a := by
  constructor
  · intro ha
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
    exact ⟨z, Subgroup.mem_subgroupOf.mp hz, z.2, rfl⟩
  · rintro ⟨y, hy, hyG, rfl⟩
    exact CFSG.Quasithin.P134.mk_mem_modO2Image hy hyG

theorem kzKey_kz3 {G : Type} [Group G] [Finite G] {Gz L K0 P : Subgroup G}
    (hrk : CFSG.Open.SQTKTauCeti.StronglyQuasithin (↥Gz ⧸ CFSG.pCore 2 ↥Gz))
    (hLG : L ≤ Gz) (hLK : L ≤ K0) (hK0G : K0 ≤ Gz)
    (hLq : CFSG.Quasithin.IsAlt 6 (↥L ⧸ CFSG.pCore 2 ↥L) ∨
      CFSG.Quasithin.IsHat (↥L ⧸ CFSG.pCore 2 ↥L) (alternatingGroup (Fin 6)))
    (hPG : P ≤ Gz) (hP3 : IsPGroup 3 P) (hPc : Nat.card P = 9) (hPexp : ∀ p ∈ P, p ^ 3 = 1)
    (hcomm : ∀ p ∈ P, ∀ k ∈ K0, p * k * p⁻¹ * k⁻¹ ∈ pCoreOf 2 Gz) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hNL : (CFSG.pCore 2 ↥L).Normal := CFSG.pCore_normal
  haveI hNG : (CFSG.pCore 2 ↥Gz).Normal := CFSG.pCore_normal
  obtain ⟨x, y, hx1, hx3, hy3, hxy, hyx⟩ := kzThreeRank2OfAlt6OrHat_kz3 hLq
  have hXYcomm : ∀ u ∈ ({x, y} : Set (↥L ⧸ CFSG.pCore 2 ↥L)), ∀ v ∈ ({x, y} : Set (↥L ⧸ CFSG.pCore 2 ↥L)),
      u * v = v * u := by
    intro u hu v hv
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu hv
    rcases hu with rfl | rfl <;> rcases hv with rfl | rfl
    · rfl
    · exact hxy
    · exact hxy.symm
    · rfl
  have hXYexp : ∀ u ∈ ({x, y} : Set (↥L ⧸ CFSG.pCore 2 ↥L)), u ^ 3 = 1 := by
    intro u hu
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
    rcases hu with rfl | rfl
    · exact hx3
    · exact hy3
  obtain ⟨hAc, hAcomm, hAexp⟩ := kzClosureCommExp_kz3 hXYcomm hXYexp
  set A : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L) := Subgroup.closure ({x, y} : Set _) with hA
  have hAp : IsPGroup 3 A := fun u => ⟨1, by
    apply Subtype.ext
    simpa using hAexp u.1 u.2⟩
  obtain ⟨m, hm⟩ := (IsPGroup.iff_card).mp hAp
  have hZ : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
  have hZA : Subgroup.zpowers x ≤ A := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hyA : y ∈ A := Subgroup.subset_closure (by simp)
  have hA3 : 3 < Nat.card A := by
    have hle : 3 ≤ Nat.card A := hZ ▸ Subgroup.card_le_of_le hZA
    refine lt_of_le_of_ne hle (fun heq => ?_)
    have hEq : Subgroup.zpowers x = A :=
      Subgroup.eq_of_le_of_card_ge hZA (by rw [hZ, heq])
    apply hyx
    rw [hEq]
    exact hyA
  have hm2 : 2 ≤ m := by
    by_contra h
    have h' : m ≤ 1 := Nat.le_of_lt_succ (Nat.lt_of_not_le h)
    have : 3 ^ m ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) h'
    rw [← hm] at this
    omega
  have hAcard9 : 9 ≤ Nat.card A := by
    rw [hm]
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) hm2
  obtain ⟨S, hSc, hSinf, hSmap⟩ :=
    kzLiftPowThree_kz3 (CFSG.pCore 2 ↥L) CFSG.pCore_isPGroup A m hm
  have hSmem : ∀ s ∈ S, (QuotientGroup.mk s : ↥L ⧸ CFSG.pCore 2 ↥L) ∈ A := by
    intro s hs
    rw [← hSmap]
    exact Subgroup.mem_map_of_mem _ hs
  have hSexp : ∀ s ∈ S, s ^ 3 = 1 := by
    intro s hs
    have h3 : (QuotientGroup.mk (s ^ 3) : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 := by
      rw [QuotientGroup.mk_pow]
      exact hAexp _ (hSmem s hs)
    have hmem : s ^ 3 ∈ S := S.pow_mem hs 3
    have hmem2 : s ^ 3 ∈ S ⊓ CFSG.pCore 2 ↥L :=
      ⟨hmem, (QuotientGroup.eq_one_iff _).mp h3⟩
    rw [hSinf, Subgroup.mem_bot] at hmem2
    exact hmem2
  have hSabel : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s := by
    intro s hs t ht
    have hc := hAcomm _ (hSmem s hs) _ (hSmem t ht)
    have h1 : (QuotientGroup.mk (s * t) : ↥L ⧸ CFSG.pCore 2 ↥L) = QuotientGroup.mk (t * s) := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      exact hc
    have h2 : (s * t)⁻¹ * (t * s) ∈ S ⊓ CFSG.pCore 2 ↥L := by
      refine ⟨S.mul_mem (S.inv_mem (S.mul_mem hs ht)) (S.mul_mem ht hs), ?_⟩
      exact (QuotientGroup.eq).mp h1
    rw [hSinf, Subgroup.mem_bot] at h2
    exact inv_mul_eq_one.mp h2
  let φ : ↥L →* (↥Gz ⧸ CFSG.pCore 2 ↥Gz) :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥Gz)).comp (Subgroup.inclusion hLG)
  have hkerφ : ∀ l : ↥L, φ l = 1 ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 Gz := by
    intro l
    have hl : Subgroup.inclusion hLG l ∈ CFSG.pCore 2 ↥Gz ↔ (l : G) ∈ CFSG.Open.pCoreOf 2 Gz := by
      rw [CFSG.Quasithin.P134.mem_pCoreOf_iff (hLG l.2)]
      rfl
    rw [← hl, ← QuotientGroup.eq_one_iff]
    rfl
  have hφS : ∀ s ∈ S, φ s = 1 → s = 1 := by
    intro s hs hφ1
    have hG : ((s : ↥L) : G) ∈ CFSG.Open.pCoreOf 2 Gz := (hkerφ s).mp hφ1
    have hs3 : ((s : ↥L) : G) ^ 3 = 1 := by
      have := congrArg (fun w : ↥L => (w : G)) (hSexp s hs)
      simpa using this
    have hval : ((s : ↥L) : G) = 1 :=
      kzEqOnePowThreeMem_kz3 (kzIsPGroupPCoreOf_kz3 Gz) hs3 hG
    exact Subtype.ext hval
  have hφinf : S ⊓ φ.ker = ⊥ := by
    rw [eq_bot_iff]
    rintro s ⟨hs, hker⟩
    rw [Subgroup.mem_bot]
    exact hφS s hs hker
  set Ebar : Subgroup (↥Gz ⧸ CFSG.pCore 2 ↥Gz) := S.map φ with hEbar
  have hEcard : Nat.card Ebar = Nat.card S := Ch1Sec3.card_map_of_inf_ker_eq_bot hφinf
  have hEbarcomm : ∀ a ∈ Ebar, ∀ b ∈ Ebar, a * b = b * a := by
    rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, hSabel s hs t ht]
  have hEbarexp : ∀ a ∈ Ebar, a ^ 3 = 1 := by
    rintro _ ⟨s, hs, rfl⟩
    rw [← map_pow, hSexp s hs, map_one]
  have hφK0 : ∀ l : ↥L, φ l ∈ CFSG.Quasithin.modO2Image Gz K0 := fun l =>
    CFSG.Quasithin.P134.mk_mem_modO2Image (hLK l.2) (hLG l.2)
  have hEbarK : ∀ a ∈ Ebar, a ∈ CFSG.Quasithin.modO2Image Gz K0 := by
    rintro _ ⟨s, -, rfl⟩
    exact hφK0 s
  have hPinf : P ⊓ CFSG.Open.pCoreOf 2 Gz = ⊥ := CFSG.Quasithin.P134.inf_pCoreOf_eq_bot hPexp
  have hPbarcard : Nat.card (CFSG.Quasithin.modO2Image Gz P) = 9 := by
    rw [CFSG.Quasithin.P134.card_modO2Image hPG hPinf, hPc]
  have hPcomm : ∀ a b : ↥P, a * b = b * a :=
    IsPGroup.commutative_of_card_eq_prime_sq (p := 3) (by rw [hPc]; norm_num)
  have hPbarcomm : ∀ a ∈ CFSG.Quasithin.modO2Image Gz P, ∀ b ∈ CFSG.Quasithin.modO2Image Gz P,
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨p, hp, hpG, rfl⟩ := kzMemModO2Image_kz3.mp ha
    obtain ⟨q, hq, hqG, rfl⟩ := kzMemModO2Image_kz3.mp hb
    have hpq : (⟨p, hpG⟩ : ↥Gz) * ⟨q, hqG⟩ = ⟨q, hqG⟩ * ⟨p, hpG⟩ := by
      apply Subtype.ext
      have h := congrArg Subtype.val (hPcomm ⟨p, hp⟩ ⟨q, hq⟩)
      exact h
    rw [← map_mul, ← map_mul, hpq]
  have hPbarexp : ∀ a ∈ CFSG.Quasithin.modO2Image Gz P, a ^ 3 = 1 := by
    intro a ha
    obtain ⟨p, hp, hpG, rfl⟩ := kzMemModO2Image_kz3.mp ha
    have h3 : (⟨p, hpG⟩ : ↥Gz) ^ 3 = 1 := Subtype.ext (by simpa using hPexp p hp)
    rw [← map_pow, h3, map_one]
  have hPbarK : ∀ a ∈ CFSG.Quasithin.modO2Image Gz P, ∀ b ∈ CFSG.Quasithin.modO2Image Gz K0,
      a * b = b * a := by
    intro a ha b hb
    obtain ⟨p, hp, hpG, rfl⟩ := kzMemModO2Image_kz3.mp ha
    obtain ⟨k, hk, hkG, rfl⟩ := kzMemModO2Image_kz3.mp hb
    have hcG : p * k * p⁻¹ * k⁻¹ ∈ Gz :=
      Gz.mul_mem (Gz.mul_mem (Gz.mul_mem hpG hkG) (Gz.inv_mem hpG)) (Gz.inv_mem hkG)
    have hN0 := (CFSG.Quasithin.P134.mem_pCoreOf_iff hcG).mp (hcomm p hp k hk)
    have heq : (⟨p, hpG⟩ : ↥Gz) * ⟨k, hkG⟩ * ⟨p, hpG⟩⁻¹ * ⟨k, hkG⟩⁻¹ = ⟨p * k * p⁻¹ * k⁻¹, hcG⟩ :=
      Subtype.ext (by simp)
    exact kzMkCommOfComm_kz3 (by rw [heq]; exact hN0)
  by_cases hA : Ebar ≤ CFSG.Quasithin.modO2Image Gz P
  ·
    have hS9 : 9 ≤ Nat.card S := by
      rw [hSc, ← hm]
      exact hAcard9
    have hEP : Ebar = CFSG.Quasithin.modO2Image Gz P :=
      Subgroup.eq_of_le_of_card_ge hA (by rw [hPbarcard, hEcard]; exact hS9)
    have hcentral : A ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) := by
      rw [← hSmap]
      rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥L) g
      have hφs : φ s ∈ CFSG.Quasithin.modO2Image Gz P := by
        rw [← hEP]
        exact ⟨s, hs, rfl⟩
      have hcomm' : φ s * φ l = φ l * φ s := hPbarK (φ s) hφs (φ l) (hφK0 l)
      have hφc : φ (l * s * l⁻¹ * s⁻¹) = 1 := by
        simp only [map_mul, map_inv]
        rw [← hcomm']
        group
      have hc : l * s * l⁻¹ * s⁻¹ ∈ CFSG.pCore 2 ↥L :=
        kzMemPCoreOfMemPCoreOf_kz3 hLG _ ((hkerφ _).mp hφc)
      exact kzMkCommOfComm_kz3 hc
    have h1 := Subgroup.card_le_of_le hcentral
    have h2 := kzCardCenterLeThree_kz3 hLq
    omega
  ·
    obtain ⟨e, he, hePbar⟩ := SetLike.not_le_iff_exists.mp hA
    set Sset : Set (↥Gz ⧸ CFSG.pCore 2 ↥Gz) :=
      (↑(CFSG.Quasithin.modO2Image Gz P) : Set _) ∪ ↑Ebar with hSset
    have hsc : ∀ u ∈ Sset, ∀ v ∈ Sset, u * v = v * u := by
      intro u hu v hv
      rcases hu with hu | hu <;> rcases hv with hv | hv
      · exact hPbarcomm u hu v hv
      · exact hPbarK u hu v (hEbarK v hv)
      · exact (hPbarK v hv u (hEbarK u hu)).symm
      · exact hEbarcomm u hu v hv
    have hsexp : ∀ u ∈ Sset, u ^ 3 = 1 := by
      intro u hu
      rcases hu with hu | hu
      · exact hPbarexp u hu
      · exact hEbarexp u hu
    obtain ⟨hEc, -, hEexp⟩ := kzClosureCommExp_kz3 hsc hsexp
    have hPE : CFSG.Quasithin.modO2Image Gz P ≤ Subgroup.closure Sset := fun u hu =>
      Subgroup.subset_closure (Or.inl hu)
    have heE : e ∈ Subgroup.closure Sset := Subgroup.subset_closure (Or.inr he)
    have hgt : 9 < Nat.card (Subgroup.closure Sset) := by
      by_contra hle
      have hle' : Nat.card (Subgroup.closure Sset) ≤ 9 := Nat.le_of_not_lt hle
      have heq : CFSG.Quasithin.modO2Image Gz P = Subgroup.closure Sset :=
        Subgroup.eq_of_le_of_card_ge hPE (by rw [hPbarcard]; exact hle')
      exact hePbar (by rw [heq]; exact heE)
    exact kzRankContra_kz3 hrk _ hEc hEexp hgt

end CFSG.Quasithin.H13
