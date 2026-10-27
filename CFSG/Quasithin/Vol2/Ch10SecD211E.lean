module

public import CFSG.Quasithin.Vol2.Ch10SecD211D
public import CFSG.Quasithin.Vol2.Ch10SecD211C
public import CFSG.Quasithin.Vol2.Ch10SecDFacts211
public import CFSG.Quasithin.Vol2.Ch10StatementsE

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem pCore_quotient_eq_bot (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h1013 : Stmt10_1_3) (h1029 : Stmt10_2_9)
    (hXI : FactXIrred) (hX3 : FactXThree) (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I)
    (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G} (hd : IsData10_2_11 T L I t v₁ v₂)
    (hlt : Xz T L (v₁ * v₂) < Kz T L (v₁ * v₂)) {Gz : Subgroup G}
    (hGz : Gz = Subgroup.centralizer ({v₁ * v₂} : Set G)) (K : Subgroup ↥Gz) [K.Normal]
    (hK : ∀ x, x ∈ K ↔ (x : G) ∈ Subgroup.centralizer (Vz v₁ v₂ : Set G)) :
    CFSG.pCore 2 (↥Gz ⧸ K) = ⊥ := by
  set X := Xz T L (v₁ * v₂) with hXdef
  set P := CFSG.pCore 2 (↥Gz ⧸ K) with hP
  set Pt : Subgroup G := (P.comap (QuotientGroup.mk' K)).map Gz.subtype with hPt
  have hTz : T ≤ Gz := hGz ▸ T_le_centralizer_z h37 h38 h h3 hc hd
  have hTs : IsSylowTwoOf T Gz := isSylowTwoOf_of_quasithinIsSylowTwo h.fsu.sylow hTz
  have hPtGz : Pt ≤ Gz := Subgroup.map_subtype_le _
  have hGzPt : Gz ≤ Subgroup.normalizer (Pt : Set G) := le_normalizer_map_comap K P
  have hRs : IsSylowTwoOf (T ⊓ Pt) Pt := A4.isSylowTwoOf_inf_normal hTs hPtGz hGzPt
  have hcov : ∀ p ∈ Pt, ∃ c ∈ Gz ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G),
      ∃ r ∈ T ⊓ Pt, p = c * r := by
    rintro _ ⟨p, hp, rfl⟩
    obtain ⟨c, hcK, r, hrT, hrP, hpcr⟩ := exists_mul_of_mem_preimage_pCore hTs K hp
    exact ⟨c, ⟨c.2, (hK c).mp hcK⟩, r, ⟨hrT, ⟨r, hrP, rfl⟩⟩, by rw [hpcr]; rfl⟩
  have hbot : T ⊓ Pt ≤ Subgroup.centralizer (Vz v₁ v₂ : Set G) → P = ⊥ := by
    intro hRC
    rw [eq_bot_iff]
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K q
    obtain ⟨c, hc, r, hr, hxcr⟩ := hcov x ⟨x, hq, rfl⟩
    have hxC : (x : G) ∈ Subgroup.centralizer (Vz v₁ v₂ : Set G) := by
      rw [hxcr]
      exact Subgroup.mul_mem _ hc.2 (hRC hr)
    rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact (hK x).mpr hxC
  by_cases hR1 : T ⊓ Pt ≤ T1 T L
  · exact hbot (le_centralizer_Vz_of_le_T1 hd hRs (hGz ▸ hPtGz) (hGz ▸ hGzPt) (hGz ▸ hcov) hR1)
  exfalso
  obtain ⟨s, hsR, hsT1⟩ := Set.not_subset.mp hR1
  have hsn : s ∉ Subgroup.normalizer (L : Set G) := fun hn => hsT1 ⟨hsR.1, hn⟩
  have hTX : T ≤ Subgroup.normalizer (X : Set G) :=
    T_le_normalizer_Xz (T_le_centralizer_z h37 h38 h h3 hc hd)
  have hXGz : X ≤ Gz := hGz ▸ (oTwoUpper_le _).trans inf_le_right
  have hO2X : pCoreOf 2 X ≤ X := Subgroup.map_subtype_le _
  have hcommX : ⁅X, T ⊓ Pt⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro x hx r hr
    rw [commutatorElement_def]
    have h1 : r * x⁻¹ * r⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hTX hr.1) x⁻¹).mp
      (X.inv_mem hx)
    simpa [mul_assoc] using X.mul_mem hx h1
  have hTR : T ≤ Subgroup.normalizer ((T ⊓ Pt : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_inf (Subgroup.le_normalizer hx) (hGzPt (hTz hx))
  have hY3 : T ≤ Subgroup.normalizer ((⁅X, T ⊓ Pt⁆ ⊔ pCoreOf 2 X : Subgroup G) : Set G) :=
    fun x hx => mem_normalizer_sup (SecA.le_normalizer_commutator hTX hTR hx)
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X (hTX hx))
  rcases hXI G T L I h h3 hc t v₁ v₂ hd _ le_sup_right (sup_le hcommX hO2X) hY3 with hYO | hYX
  ·
    obtain ⟨x, hxL, hxX, hxo, hxC⟩ := exists_odd_mem_Xz h37 h38 h h3 hc hd
    have hmem : x * s * x⁻¹ * s⁻¹ ∈ pCoreOf 2 X := by
      rw [← hYO]
      refine Subgroup.mem_sup_left ?_
      have := Subgroup.commutator_mem_commutator hxX hsR
      rwa [commutatorElement_def] at this
    obtain ⟨k, hk⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X ⟨_, hmem⟩
    exact not_exists_pow_commutator h37 h38 h hd.1 hd.2.1 hsR.1 hsn hxL hxo hxC
      ⟨k, by simpa using congrArg Subtype.val hk⟩
  set A := P.comap (QuotientGroup.mk' K) with hA
  set B := (pCoreOf 2 X).subgroupOf Gz with hB
  rw [← hXdef] at hYX
  have hXAB : X ≤ (A ⊔ B).map Gz.subtype := by
    refine (le_of_eq hYX.symm).trans (sup_le ?_ ?_)
    · refine le_trans ?_ (Subgroup.map_mono le_sup_left)
      rw [Subgroup.commutator_le]
      intro x hx r hr
      have h1 : x * r * x⁻¹ ∈ Pt :=
        (Subgroup.mem_normalizer_iff.mp (hGzPt (hXGz hx)) r).mp hr.2
      rw [commutatorElement_def]
      exact Pt.mul_mem h1 (Pt.inv_mem hr.2)
    · refine le_trans ?_ (Subgroup.map_mono le_sup_right)
      rw [hB, Subgroup.map_subgroupOf_eq_of_le (hO2X.trans hXGz)]
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup
  have hB2 : IsPGroup 2 (B.map (QuotientGroup.mk' K)) :=
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).comap_of_injective _
      (Subgroup.subtype_injective _)).map _
  have hAB2 : IsPGroup 2 ((A ⊔ B).map (QuotientGroup.mk' K)) := by
    rw [Subgroup.map_sup]
    exact (IsPGroup.to_sup_of_normal_left hP2 hB2).to_le
      (sup_le_sup_right (Subgroup.map_comap_le _ _) _)
  have hXC : X ≤ Gz ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G) := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hx, hxo⟩
    have hxX : x ∈ X := mem_oTwoUpper_of_odd hx hxo
    obtain ⟨y, hy, rfl⟩ := hXAB hxX
    have hmk : QuotientGroup.mk' K y ∈ (A ⊔ B).map (QuotientGroup.mk' K) := ⟨y, hy, rfl⟩
    obtain ⟨k, hk⟩ := hAB2 ⟨_, hmk⟩
    have hk' : (QuotientGroup.mk' K y) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have hdvd1 : orderOf (QuotientGroup.mk' K y) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
    have hdvd2 : orderOf (QuotientGroup.mk' K y) ∣ orderOf y := orderOf_map_dvd _ _
    have hyo : Odd (orderOf y) := by
      change Odd (orderOf (y : G)) at hxo
      rwa [Subgroup.orderOf_coe] at hxo
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd1
    have hodd := Odd.of_dvd_nat hyo hdvd2
    rw [hj] at hodd
    have hj0 : j = 0 := by
      by_contra hne
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hne).mpr even_two)
    rw [hj0, pow_zero, orderOf_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hj
    exact ⟨y.2, (hK y).mp hj⟩
  have hC'M : Gz ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G) ≤ fsuM T L := by
    have h1 := (stmt10_2_11_one h37 h38 h1029 h h3 hc hd).2
    rw [← hGz] at h1
    exact h1.trans inf_le_left
  have h3dvd : 3 ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) := by
    obtain ⟨e⟩ := h3.1
    rw [Nat.card_congr e.toEquiv, card_SL_three_two]
    norm_num
  have hL0 := h1013 G T L I h 3 Nat.prime_three (by norm_num) h3dvd
  have hO3 : oPrimeResidualOf 3 (Gz ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G)) ≤ X := by
    refine oPrimeResidualOf_le_of fun y hy k hk => ?_
    have hyM : y ∈ oPrimeResidualOf 3 (fsuM T L) := Subgroup.subset_closure ⟨hC'M hy, k, hk⟩
    rw [hL0] at hyM
    have hyo : Odd (orderOf y) := by rw [hk]; exact Odd.pow (by decide)
    exact mem_oTwoUpper_of_odd ⟨hyM, hGz ▸ hy.1⟩ hyo
  have hXeq : X = oPrimeResidualOf 3 (Gz ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G)) :=
    le_antisymm ((hX3 G T L I h h3 hc t v₁ v₂ hd).trans (oPrimeResidualOf_mono' 3 hXC)) hO3
  have hGzVz : Gz ≤ Subgroup.normalizer (Vz v₁ v₂ : Set G) := hGz ▸ le_normalizer_conjClosure _ _
  have hGzX : Gz ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    rw [hXeq]
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    refine Subgroup.closure_induction (p := fun y _ => g * y * g⁻¹ ∈
      oPrimeResidualOf 3 (Gz ⊓ Subgroup.centralizer (Vz v₁ v₂ : Set G)))
      (fun y hy => ?_) (by simp) (fun a b _ _ ha hb => ?_) (fun a _ ha => ?_) hx
    · obtain ⟨hyC, k, hk⟩ := hy
      refine Subgroup.subset_closure ⟨⟨Gz.mul_mem (Gz.mul_mem hg hyC.1) (Gz.inv_mem hg),
        conj_mem_centralizer (hGzVz hg) hyC.2⟩, k, ?_⟩
      rw [← hk]
      exact orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective y
    · have := Subgroup.mul_mem _ ha hb
      convert this using 1
      group
    · have := Subgroup.inv_mem _ ha
      convert this using 1
      group
  have hKz : Kz T L (v₁ * v₂) ≤ X := conjClosure_le fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hGzX (hGz ▸ hg)) x).mp hx
  exact absurd hKz (not_le_of_gt hlt)

theorem stmt10_2_11_two (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h1013 : Stmt10_1_3) (h1029 : Stmt10_2_9) (hXI : FactXIrred) (hX3 : FactXThree)
    (h : Hyp10 G T L I) (h3 : Case10_1_1Three T L I) (hc : fsuCVM T L I = ⊥) {t v₁ v₂ : G}
    (hd : IsData10_2_11 T L I t v₁ v₂) (hlt : Xz T L (v₁ * v₂) < Kz T L (v₁ * v₂)) :
    Vz v₁ v₂ ≤ Subgroup.centralizer ({v₁ * v₂} : Set G) ∧
      IsPrimeReduced 2 ((Vz v₁ v₂).subgroupOf (Subgroup.centralizer ({v₁ * v₂} : Set G))) := by
  have hVzGz := Vz_le_Gz h hd
  refine ⟨hVzGz, ?_⟩
  have hnorm : ((Vz v₁ v₂).subgroupOf (Subgroup.centralizer ({v₁ * v₂} : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVzGz).mpr (le_normalizer_conjClosure _ _)
  refine ⟨hnorm, ?_, ?_⟩
  · have hsq := sq_eq_one_of_mem_Vz h37 h38 h1029 h h3 hc hd
    have hab := (stmt10_2_11_one h37 h38 h1029 h h3 hc hd).1
    have hcomm : IsMulCommutative
        ↥((Vz v₁ v₂).subgroupOf (Subgroup.centralizer ({v₁ * v₂} : Set G))) :=
      ⟨⟨fun a b => Subtype.ext (Subtype.ext ((Subgroup.mem_centralizer_iff.mp
        (hab (Subgroup.mem_subgroupOf.mp b.2)).2) _ (hab (Subgroup.mem_subgroupOf.mp a.2)).1))⟩⟩
    exact ⟨Monoid.exponent_dvd_of_forall_pow_eq_one fun g => Subtype.ext (Subtype.ext (by
      simpa using hsq _ (Subgroup.mem_subgroupOf.mp g.2)))⟩
  · exact pCore_quotient_eq_bot h37 h38 h1013 h1029 hXI hX3 h h3 hc hd hlt rfl _
      (mem_centralizer_subgroupOf_iff hVzGz)

end CFSG.Quasithin.Vol2.Ch10.SecD
