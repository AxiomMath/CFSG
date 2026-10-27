module

public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8312A
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8312B
public import CFSG.Quasithin.Vol2.Ch8Sec3Lem8310D
public import CFSG.Quasithin.Background.G2Relaxed

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.H.L3Wr
open scoped IsMulCommutative commutatorElement

namespace Ch8312

variable {G : Type} [Group G]

theorem factorization_3600_three : (3600 : ℕ).factorization 3 = 2 := by
  rw [show (3600 : ℕ) = 3 ^ 2 * 400 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem factorization_60_three : (60 : ℕ).factorization 3 = 1 := by
  rw [show (60 : ℕ) = 3 ^ 1 * 20 by norm_num, Nat.factorization_mul (by norm_num) (by norm_num),
    Finsupp.add_apply, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same,
    Nat.factorization_eq_zero_of_not_dvd (by norm_num), add_zero]

theorem qPi_mem_image_of_mem_sup {G₁ K : Subgroup G} (hKG : K ≤ G₁) {x : G}
    (hx : x ∈ K ⊔ pCoreOf 2 G₁) (hxG : x ∈ G₁) : qPi G₁ ⟨x, hxG⟩ ∈ imageOTwoQuot G₁ K := by
  have hKO : K ≤ Subgroup.normalizer (pCoreOf 2 G₁ : Set G) :=
    hKG.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
  have hx' : x ∈ ((K ⊔ pCoreOf 2 G₁ : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right K _ hKO] at hx'
  obtain ⟨k, hk, o, ho, rfl⟩ := hx'
  obtain ⟨o', ho', rfl⟩ := ho
  refine ⟨⟨k, hKG hk⟩, Subgroup.mem_subgroupOf.mpr hk, ?_⟩
  change qPi G₁ ⟨k, hKG hk⟩ = qPi G₁ (⟨k, hKG hk⟩ * o')
  have h1 : qPi G₁ o' = 1 := (QuotientGroup.eq_one_iff (N := CFSG.Open.pCore 2 ↥G₁) o').mpr ho'
  rw [map_mul, h1, mul_one]

theorem mem_pCoreOf_of_qPi_eq_one {G₁ : Subgroup G} {x : G} (hxG : x ∈ G₁)
    (h : qPi G₁ ⟨x, hxG⟩ = 1) : x ∈ pCoreOf 2 G₁ :=
  ⟨⟨x, hxG⟩, (QuotientGroup.eq_one_iff _).mp h, rfl⟩

theorem inf_sup_le_pCoreOf [Finite G] {G₁ K K' : Subgroup G} (hK : K ∈ cComp G₁)
    (hK' : K' ∈ cComp G₁) (hne : K ≠ K') (hs : IsSimpleGroup ↥(imageOTwoQuot G₁ K))
    (h12 : K' ≤ Subgroup.normalizer (K : Set G)) (h21 : K ≤ Subgroup.normalizer (K' : Set G)) :
    (K ⊔ pCoreOf 2 G₁) ⊓ (K' ⊔ pCoreOf 2 G₁) ≤ pCoreOf 2 G₁ := by
  obtain ⟨-, hdisj⟩ := q_pair_comm_disjoint hK hK' hne hs h12 h21
  rintro x ⟨hx1, hx2⟩
  have hKG := le_of_mem_cComp hK
  have hK'G := le_of_mem_cComp hK'
  have hxG : x ∈ G₁ := sup_le hKG (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hx1
  refine mem_pCoreOf_of_qPi_eq_one hxG ?_
  have h : qPi G₁ ⟨x, hxG⟩ ∈ imageOTwoQuot G₁ K ⊓ imageOTwoQuot G₁ K' :=
    ⟨qPi_mem_image_of_mem_sup hKG hx1 hxG, qPi_mem_image_of_mem_sup hK'G hx2 hxG⟩
  rw [hdisj] at h
  exact h

theorem exists_mem_sup_not_mem [Finite G] {G₁ K K' P : Subgroup G}
    (hK : K ∈ cComp G₁) (hK' : K' ∈ cComp G₁) (hne : K ≠ K')
    (eK : OTwoQuot K ≃* alternatingGroup (Fin 5)) (eK' : OTwoQuot K' ≃* alternatingGroup (Fin 5))
    (h12 : K' ≤ Subgroup.normalizer (K : Set G)) (h21 : K ≤ Subgroup.normalizer (K' : Set G))
    (hPK : P ≤ K ⊔ K') (hP3 : IsPGroup 3 P) (hPc : Nat.card P = 9) :
    ∃ a ∈ P, a ∈ K ⊔ pCoreOf 2 G₁ ∧ a ∉ pCoreOf 2 G₁ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKG := le_of_mem_cComp hK
  have hK'G := le_of_mem_cComp hK'
  have hPG : P ≤ G₁ := hPK.trans (sup_le hKG hK'G)
  set N₁ := imageOTwoQuot G₁ K with hN₁
  set N₂ := imageOTwoQuot G₁ K' with hN₂
  obtain ⟨e₁⟩ := q_oTwoQuot_equiv_image (G₁ := G₁) (subnormal_of_mem_cComp hK)
  obtain ⟨e₂⟩ := q_oTwoQuot_equiv_image (G₁ := G₁) (subnormal_of_mem_cComp hK')
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hs₁ : IsSimpleGroup ↥N₁ := (e₁.symm.trans eK).isSimpleGroup
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [Nat.card_eq_fintype_card]
    decide
  have hN₁c : Nat.card ↥N₁ = 60 := (Nat.card_congr (e₁.symm.trans eK).toEquiv).trans h60
  have hN₂c : Nat.card ↥N₂ = 60 := (Nat.card_congr (e₂.symm.trans eK').toEquiv).trans h60
  obtain ⟨hcomm, hdisj⟩ := q_pair_comm_disjoint hK hK' hne hs₁ h12 h21
  have hN12c : Nat.card ↥(N₁ ⊔ N₂) = 3600 := by
    rw [SBc15.card_sup_eq_mul_of_commute hcomm (disjoint_iff.mpr hdisj), hN₁c, hN₂c]
  set φ : ↥P →* OTwoQuot G₁ := (qPi G₁).comp (Subgroup.inclusion hPG) with hφ
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxO : (x : G) ∈ pCoreOf 2 G₁ := mem_pCoreOf_of_qPi_eq_one (hPG x.2) hx
    have hd := IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 G₁) hP3
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)
    exact Subtype.ext (Subgroup.disjoint_def.mp hd x.2 hxO)
  set Ph := imageOTwoQuot G₁ P with hPh
  have hPhr : φ.range = Ph := q_range_comp_eq_image hPG
  have hPhc : Nat.card ↥Ph = 9 := by
    rw [← hPhr, ← hPc]
    exact (Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv).symm
  have hPhle : Ph ≤ N₁ ⊔ N₂ := by
    rw [hN₁, hN₂, ← q_image_sup hKG hK'G]
    exact Ch8310.image_mono hPK
  have hsyl : IsSylowIn 3 Ph (N₁ ⊔ N₂) := by
    refine isSylowIn_of_card_eq hPhle ?_
    rw [hPhc, hN12c, factorization_3600_three]
    norm_num
  have hN1n : (N₁.subgroupOf (N₁ ⊔ N₂)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le Subgroup.le_normalizer (Ch8310.le_normalizer_of_comm hcomm))
  have hsyl1 := hsyl.inf_normal le_sup_left hN1n
  have hc1 : Nat.card ↥(Ph ⊓ N₁) = 3 := by
    rw [hsyl1.card_eq, hN₁c, factorization_60_three, pow_one]
  obtain ⟨y, hy, hy1⟩ : ∃ y ∈ Ph ⊓ N₁, y ≠ 1 := by
    by_contra h
    push Not at h
    have hbot : Ph ⊓ N₁ = ⊥ := (Subgroup.eq_bot_iff_forall _).mpr h
    rw [hbot, Subgroup.card_bot] at hc1
    exact absurd hc1 (by norm_num)
  obtain ⟨⟨a, haG⟩, ha, rfl⟩ := hy.1
  obtain ⟨⟨k, hkG⟩, hk, hka⟩ := hy.2
  refine ⟨a, Subgroup.mem_subgroupOf.mp ha, ?_, fun haO => hy1 ?_⟩
  · have hk' : k ∈ K := Subgroup.mem_subgroupOf.mp hk
    have hko : k⁻¹ * a ∈ pCoreOf 2 G₁ := by
      have h1 : (⟨k, hkG⟩ : ↥G₁)⁻¹ * ⟨a, haG⟩ ∈ CFSG.Open.pCore 2 ↥G₁ :=
        QuotientGroup.eq.mp hka
      exact ⟨_, h1, rfl⟩
    have e : a = k * (k⁻¹ * a) := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk') (Subgroup.mem_sup_right hko)
  · obtain ⟨o, ho, hoa⟩ := haO
    have : (⟨a, haG⟩ : ↥G₁) = o := Subtype.ext hoa.symm
    rw [this]
    exact (QuotientGroup.eq_one_iff _).mpr ho

theorem eq_or_eq_of_simple {K Q S : Subgroup G} (hs : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hOQ : pCoreOf 2 K ≤ Q) (hKQ : K ≤ Subgroup.normalizer (Q : Set G)) (hQS : Q ≤ S)
    (hSK : S ≤ K ⊔ Q) (hKS : K ≤ Subgroup.normalizer (S : Set G)) : S = Q ∨ S = K ⊔ Q := by
  set N : Subgroup ↥K := (S ⊓ K).subgroupOf K with hNdef
  have hN : N.Normal := by
    refine ⟨fun n hn k => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact ⟨(Subgroup.mem_normalizer_iff.mp (hKS k.2) n).mp hn.1,
      K.mul_mem (K.mul_mem k.2 hn.2) (K.inv_mem k.2)⟩
  set π : ↥K →* ↥K ⧸ CFSG.pCore 2 ↥K := QuotientGroup.mk' _ with hπ
  have hNm : (N.map π).Normal := hN.map π (QuotientGroup.mk'_surjective _)
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map π) with h | h
  · left
    refine le_antisymm (fun x hx => ?_) hQS
    have hx' : x ∈ ((K ⊔ Q : Subgroup G) : Set G) := hSK hx
    rw [Subgroup.coe_mul_of_left_le_normalizer_right K Q hKQ] at hx'
    obtain ⟨k, hk, q, hq, rfl⟩ := hx'
    have hkS : k ∈ S := by
      have := S.mul_mem hx (S.inv_mem (hQS hq))
      simpa using this
    have h1 : π ⟨k, hk⟩ = 1 := by
      have : π ⟨k, hk⟩ ∈ N.map π := ⟨⟨k, hk⟩, Subgroup.mem_subgroupOf.mpr ⟨hkS, hk⟩, rfl⟩
      rw [h] at this
      exact this
    have hkO : k ∈ pCoreOf 2 K := (Vol2.Ch10.SecA.mk_eq_one_iff ⟨k, hk⟩).mp h1
    exact Q.mul_mem (hOQ hkO) hq
  · right
    refine le_antisymm hSK (sup_le (fun k hk => ?_) hQS)
    have : π ⟨k, hk⟩ ∈ N.map π := by rw [h]; trivial
    obtain ⟨n, hn, hnk⟩ := this
    have h2 : n⁻¹ * ⟨k, hk⟩ ∈ CFSG.pCore 2 ↥K := QuotientGroup.eq.mp hnk
    have h3 : ((n⁻¹ * ⟨k, hk⟩ : ↥K) : G) ∈ pCoreOf 2 K := by
      rw [← Vol2.Ch10.SecA.subgroupOf_pCoreOf] at h2
      exact h2
    have h4 := S.mul_mem (Subgroup.mem_subgroupOf.mp hn).1 (hQS (hOQ h3))
    simpa using h4

theorem act_mul_inv {V : Subgroup G} {hV : IsElemAbelian 2 V} (e : IntMod V hV ≃* WMod)
    (g : Subgroup.normalizer (V : Set G)) (w : IntMod V hV) :
    congrHom e (convI hV g) (e w) * (e w)⁻¹ = e (convI hV g w * w⁻¹) ∧
      (convI hV g w * w⁻¹).val = (g : G) * w.val * (g : G)⁻¹ * (w.val)⁻¹ := by
  refine ⟨?_, by rw [IntMod.val_mul, IntMod.val_inv, convI_apply_val]⟩
  rw [congrHom_convI_apply, map_mul, map_inv]

theorem ddW_conj (g x y : MulAut WMod) (X : WMod) :
    ddW (g * x * g⁻¹) (g * y * g⁻¹) X = g (ddW x y (g⁻¹ X)) := by
  obtain ⟨Y, rfl⟩ : ∃ Y, X = g Y := ⟨g⁻¹ X, by rw [MulAut.apply_inv_self]⟩
  have h1 : ∀ (h : MulAut WMod) (Z : WMod), (g * h * g⁻¹) (g Z) = g (h Z) := fun h Z => by
    rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hinv : ∀ (h : MulAut WMod) (A : WMod), h A⁻¹ = (h A)⁻¹ := fun h A => map_inv h A
  have hmul : ∀ (h : MulAut WMod) (A B : WMod), h (A * B) = h A * h B := fun h A B => map_mul h A B
  have h2 : (g * y * g⁻¹) (g Y) * (g Y)⁻¹ = g (y Y * Y⁻¹) := by
    rw [h1, hmul, hinv]
  unfold ddW
  rw [MulAut.inv_apply_self, h2, h1, ← hinv g, ← hmul g]

theorem mem_V5_iff_of_mem_stabE {g : MulAut WMod} (hg : g ∈ stabE) (X : WMod) :
    g X ∈ V5 ↔ X ∈ V5 := by
  refine ⟨fun h => ?_, map_mem_V5_of_mem_stabE hg⟩
  have := map_mem_V5_of_mem_stabE (stabE.inv_mem hg) h
  rwa [MulAut.inv_apply_self] at this

end Ch8312

open Ch8312 in
theorem stmt8_3_12_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h3228 : Stmt3_2_2_eight) (h326 : Stmt3_2_6C) (h8310 : Stmt8_3_10) : Stmt8_3_12 := by
  intro G _ _ T L I hyp h731 hc hrow z hz2 hzV
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hyp.fsu.simple
  obtain ⟨⟨K, s, hsT, hsN, hKC, hKz, F, _, _, hF, ⟨eF⟩⟩, -⟩ :=
    h8310 G T L I hyp h731 hc hrow z hz2 hzV
  obtain ⟨hV, hN⟩ := stmtFSUModule_of_eight h3228 G T L I hyp.fsu
  have hz1 : z ≠ 1 := fun h => by
    rw [h, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hzmem : z ∈ fsuV T I ⊓ Subgroup.centralizer (T : Set G) := by
    rw [hzV]
    exact Subgroup.mem_zpowers z
  have hTz : T ≤ Subgroup.centralizer ({z} : Set G) := fun t ht =>
    Subgroup.mem_centralizer_iff.2 fun h hh => by
      rw [Set.mem_singleton_iff.1 hh]
      exact (Subgroup.mem_centralizer_iff.1 hzmem.2 t ht).symm
  have hsGz : s ∈ Subgroup.centralizer ({z} : Set G) := hTz hsT
  have hTM : T ≤ fsuM T L := le_normalizer_conjClosure L T
  have hVVM := Ch8313.fsuV_eq_fsuVM h326 hyp hrow
  have hMV : fsuM T L ≤ Subgroup.normalizer (fsuV T I : Set G) := by
    have h1 : fsuM T L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
      le_normalizer_conjClosure (fsuV T I) (fsuM T L)
    rwa [← hVVM] at h1
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hVGz : fsuV T I ≤ Subgroup.centralizer ({z} : Set G) := hVT.trans hTz
  have hVM : fsuV T I ≤ fsuM T L := hVT.trans hTM
  have hXL0 : ch83X T L z ≤ fsuL0 T L := (twoResidual_le _).trans inf_le_left
  have hXGz : ch83X T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    (twoResidual_le _).trans inf_le_right
  have hXM : ch83X T L z ≤ fsuM T L := hXL0.trans Subgroup.le_normalizer
  have hXKz : ch83X T L z ≤ ch83Kz T L z := le_conjClosure _ _
  have hKzGz : ch83Kz T L z ≤ Subgroup.centralizer ({z} : Set G) :=
    conjClosure_le fun h hh x hx =>
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hXGz hx)) (Subgroup.inv_mem _ hh)
  have hTGz : IsSylowTwoOf T (Subgroup.centralizer ({z} : Set G)) :=
    Ch837.isSylowTwoOf_of_le hyp.fsu.sylow hTz
  have hzO : Subgroup.zpowers z ≤ pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) :=
    Ch837.zpowers_le_pCoreOf hz2 (Subgroup.mem_centralizer_singleton_iff.mpr rfl) le_rfl
  have hPGz : pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) ≠ ⊥ := fun h => by
    rw [h] at hzO
    exact hz1 (Subgroup.zpowers_eq_bot.mp (le_bot_iff.mp hzO))
  have hKl : LocalSQTK G := (qtkeCore_of_cat hyp.fsu.nonabelian hyp.fsu.qtke).1
  have hSQ : IsSQTKIn (Subgroup.centralizer ({z} : Set G)) :=
    sqtkGroup_of_pCoreOf_ne_bot hyp.fsu.qtke hyp.fsu.simple hyp.fsu.nonabelian hPGz
  have hA3 : A3Orbits G := a3Orbits_of_a37_a38 (a37ForSQTK_of_cat h37) (a38ForSQTK_of_cat h38)
  have hnn := Ch837.not_le_normalizer_of_row hrow
  have hCL0 : fsuL0 T L ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ pCoreOf 2 (fsuL0 T L) := by
    rw [hVVM]
    exact Vol2.Ch10.SecA.fsuL0_inf_centralizer_le_of_fsu h37 h38 hyp.fsu hnn
  set Q := pCoreOf 2 (Subgroup.centralizer ({z} : Set G)) with hQdef
  have hQGz : Q ≤ Subgroup.centralizer ({z} : Set G) := CFSG.LieType.BorelTits.pCoreOf_le 2 _
  have hGzQ : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (Q : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  obtain ⟨e, he, hY, -, hz, hez⟩ := Ch837.exists_model_eW00_T hyp hV hrow hz1 hzV
  by_contra hVQ
  have hg := (almostSpecialHyp e h37 h38 h326 hyp hrow hN hMV hz2 hzV he hY hz hez).g22
  set U := conjClosure (ch83V5 e) (Subgroup.centralizer ({z} : Set G)) with hUdef
  have hV5U : ch83V5 e ≤ U := le_conjClosure _ _
  have hV5Gz : ch83V5 e ≤ Subgroup.centralizer ({z} : Set G) := (ch83V5_le e).trans hVGz
  have hUGz : U ≤ Subgroup.centralizer ({z} : Set G) := conjClosure_le fun h hh x hx =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh (hV5Gz hx)) (Subgroup.inv_mem _ hh)
  have hGzU : Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (U : Set G) :=
    le_normalizer_conjClosure _ _
  have hUT : U ≤ T := hg.three.1
  have hUQ : U ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUGz hGzU
    (hyp.fsu.sylow.1.to_le hUT)
  have hNz : Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) =
      Subgroup.centralizer ({z} : Set G) := Ch8313.normalizer_zpowers_eq hz2
  have hQU : ∀ q ∈ Q, ∀ u ∈ U, dl q u ∈ Subgroup.zpowers z := by
    intro q hq u hu
    have hqN : q ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [hNz]
      exact hQGz hq
    have huN : u ∈ Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [hNz]
      exact hUGz hu
    have hmem := hg.one.2 (secMk_mem_secImg (A := Subgroup.normalizer
      ((Subgroup.zpowers z : Subgroup G) : Set G)) (B := Subgroup.zpowers z) (x := ⟨u, huN⟩) hu)
    have hcomm := mem_centralizer_of_mem_omegaOneCenterOf hmem
      (secMk_mem_secImg (A := Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G))
        (B := Subgroup.zpowers z) (x := ⟨q, hqN⟩) hq)
    exact commutator_mem_of_secMk_commute hcomm
  have hWn : ch83X T L z ⊔ T ≤ Subgroup.normalizer ((fsuV T I ⊓ Q : Subgroup G) : Set G) := by
    intro g hg'
    have hgM : g ∈ fsuM T L := sup_le hXM hTM hg'
    have hgz : g ∈ Subgroup.centralizer ({z} : Set G) := sup_le hXGz hTz hg'
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hMV hgM, hGzQ hgz⟩
  have hVQ5 : fsuV T I ⊓ Q = ch83V5 e := by
    rcases eq_of_ch83V5_le e h37 h38 h326 hyp hrow hN he hY hz hez
        (le_inf (ch83V5_le e) (hV5U.trans hUQ)) inf_le_left hWn with h | h
    · exact h
    · exact absurd (h.symm.le.trans inf_le_right) hVQ
  have hKc : K ∈ cComp (Subgroup.centralizer ({z} : Set G)) := mem_cComp_iff.mpr hKC
  set K' := CFSG.conjugate K s with hK'def
  have hK'eq : conjByElt s⁻¹ K = K' := by
    rw [hK'def, Ch837.conjByElt_eq_conjugate, inv_inv]
  have hK'c : K' ∈ cComp (Subgroup.centralizer ({z} : Set G)) :=
    conjSub_mem_cComp_of_mem hKc (Subgroup.inv_mem _ hsGz)
  have hne : K ≠ K' := fun h => hsN (by
    have h1 : conjByElt s⁻¹ K = K := hK'eq.trans h.symm
    simpa using (Subgroup.normalizer (K : Set G)).inv_mem (A38.map_conj_eq_iff.mp h1))
  have hKz' : ch83Kz T L z = K ⊔ K' := hKz
  have hKGz : K ≤ Subgroup.centralizer ({z} : Set G) := le_of_mem_cComp hKc
  have hK'Gz : K' ≤ Subgroup.centralizer ({z} : Set G) := le_of_mem_cComp hK'c
  have hcommKK' := (Vol2Native.lemma_1_2_1_two hKl h37 hPGz hKc hK'c hne).1
  have hK'NK : K' ≤ Subgroup.normalizer (K : Set G) := Ch837.le_normalizer_of_commutator_le
    (hcommKK'.trans (inf_le_left.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K)))
  have hKNK' : K ≤ Subgroup.normalizer (K' : Set G) := Ch837.le_normalizer_of_commutator_le
    (by
      rw [Subgroup.commutator_comm]
      exact hcommKK'.trans (inf_le_right.trans (CFSG.LieType.BorelTits.pCoreOf_le 2 K')))
  have hOK : pCoreOf 2 K ≤ Q := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hKc)
  have hOK' : pCoreOf 2 K' ≤ Q := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK'c)
  have h12 : ∀ k ∈ K, ∀ k' ∈ K', dl k k' ∈ Q := fun k hk k' hk' => by
    have h1 : ⁅k, k'⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hk hk'
    exact hOK (hcommKK' h1).1
  have h21 : ∀ k' ∈ K', ∀ k ∈ K, dl k' k ∈ Q := fun k' hk' k hk => by
    have h1 : ⁅k, k'⁆ ∈ ⁅K, K'⁆ := Subgroup.commutator_mem_commutator hk hk'
    have h2 := Q.inv_mem (hOK (hcommKK' h1).1)
    have e : dl k' k = ⁅k, k'⁆⁻¹ := by simp only [dl, commutatorElement_def]; group
    rw [e]
    exact h2
  have hc21 := dl_mem_of_mem_sup' hQGz hK'Gz hKGz hGzQ h21
  have hKQ : K ≤ Subgroup.normalizer (Q : Set G) := hKGz.trans hGzQ
  have hK'Q : K' ≤ Subgroup.normalizer (Q : Set G) := hK'Gz.trans hGzQ
  obtain ⟨eA⟩ := Ch8310.a5_of_sl24 hF
  obtain ⟨eKK'⟩ := Ch837.nonempty_quot_conjugate_equiv K s
  have eK : OTwoQuot K ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq (BlueprintB2.pCore_eq_open_pCore 2 ↥K).symm).trans
      (eF.trans eA)
  have eK' : OTwoQuot K' ≃* alternatingGroup (Fin 5) :=
    (QuotientGroup.quotientMulEquivOfEq (BlueprintB2.pCore_eq_open_pCore 2 ↥K').symm).trans
      (eKK'.symm.trans (eF.trans eA))
  have : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup (by simp)
  have hsK : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K) := (eF.trans eA).isSimpleGroup
  have hsK' : IsSimpleGroup (↥K' ⧸ CFSG.pCore 2 ↥K') :=
    (eKK'.symm.trans (eF.trans eA)).isSimpleGroup
  obtain ⟨e₁⟩ := q_oTwoQuot_equiv_image (G₁ := Subgroup.centralizer ({z} : Set G))
    (subnormal_of_mem_cComp hKc)
  have hdisj := inf_sup_le_pCoreOf hKc hK'c hne (e₁.symm.trans eK).isSimpleGroup hK'NK hKNK'
  obtain ⟨horb, hcase⟩ := hA3 _ T K hSQ hTGz hKc
  have hpair : conjSubgroupsBy (Subgroup.centralizer ({z} : Set G)) K = {K, K'} := by
    rcases hcase with hnorm | ⟨t, -, -, hp, -⟩
    · exact absurd (hnorm s hsT) hsN
    · rw [horb, hp]
      have hmem : conjByElt s⁻¹ K ∈ conjSubgroupsBy T K := ⟨s⁻¹, T.inv_mem hsT, rfl⟩
      rw [hp] at hmem
      rcases hmem with h | h
      · exact absurd (h.symm.trans hK'eq) hne
      · have h' : conjByElt s⁻¹ K = conjByElt t K := h
        rw [← h', hK'eq]
  have hmemK : ∀ y ∈ Subgroup.centralizer ({z} : Set G),
      conjByElt y K = K ∨ conjByElt y K = K' := by
    intro y hy
    have h1 : conjByElt y K ∈ conjSubgroupsBy (Subgroup.centralizer ({z} : Set G)) K :=
      ⟨y, hy, rfl⟩
    rw [hpair] at h1
    exact h1
  have hmemK' : ∀ y ∈ Subgroup.centralizer ({z} : Set G),
      conjByElt y K' = K ∨ conjByElt y K' = K' := by
    intro y hy
    have e : conjByElt y K' = conjByElt (y * s⁻¹) K := by
      rw [← hK'eq]
      unfold conjByElt
      rw [Subgroup.map_map]
      congr 1
      ext x
      simp [MulAut.conj_apply, mul_assoc]
    rw [e]
    exact hmemK _ (Subgroup.mul_mem _ hy (Subgroup.inv_mem _ hsGz))
  obtain ⟨-, -, hXi, -, P, hP, hPc, -⟩ := Ch837.xi_data h37 h38 h326 hyp hV hrow hN hz2 hzV
  have hPe : IsElemAbelian 3 P := Ch8310.isElemAbelian_of_isXi hXi hP hPc
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hPX : P ≤ ch83X T L z := hP.le
  have hPKK : P ≤ K ⊔ K' := hPX.trans (hXKz.trans hKz'.le)
  obtain ⟨a, haP, haK, haQ⟩ :=
    exists_mem_sup_not_mem hKc hK'c hne eK eK' hK'NK hKNK' hPKK hP3 hPc
  obtain ⟨b, hbP, hbK, hbQ⟩ := exists_mem_sup_not_mem hK'c hKc hne.symm eK' eK hKNK' hK'NK
    (by rw [sup_comm]; exact hPKK) hP3 hPc
  have haM : a ∈ fsuM T L := hXM (hPX haP)
  have hbM : b ∈ fsuM T L := hXM (hPX hbP)
  have haN : a ∈ Subgroup.normalizer (fsuV T I : Set G) := hMV haM
  have hbN : b ∈ Subgroup.normalizer (fsuV T I : Set G) := hMV hbM
  have hPC : ∀ x ∈ P, x ∈ Subgroup.centralizer (fsuV T I : Set G) → x = 1 := fun x hx hxC => by
    have h1 : x ∈ pCoreOf 2 (fsuL0 T L) := hCL0 ⟨hXL0 (hPX hx), hxC⟩
    exact Subgroup.disjoint_def.mp (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P _ hP3
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _)) hx h1
  have hVK : ∀ v ∈ fsuV T I, v ∈ Subgroup.normalizer (K : Set G) ∧
      v ∈ Subgroup.normalizer (K' : Set G) := by
    intro v hv
    have hvGz := hVGz hv
    have hnotswap : conjByElt v K ≠ K' := by
      intro hsw
      have hy : v * a * v⁻¹ ∈ K' ⊔ Q := by
        have ha' : a ∈ ((K ⊔ Q : Subgroup G) : Set G) := haK
        rw [Subgroup.coe_mul_of_left_le_normalizer_right K Q hKQ] at ha'
        obtain ⟨k, hk, q, hq, hkq⟩ := ha'
        rw [← hkq]
        have hk' : v * k * v⁻¹ ∈ K' := by
          rw [← hsw]
          exact ⟨k, hk, rfl⟩
        have hq' : v * q * v⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hGzQ hvGz) q).mp hq
        have e : v * (k * q) * v⁻¹ = (v * k * v⁻¹) * (v * q * v⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk') (Subgroup.mem_sup_right hq')
      have hw : v * a * v⁻¹ * a⁻¹ ∈ fsuV T I := by
        have h1 : a * v⁻¹ * a⁻¹ ∈ fsuV T I :=
          (Subgroup.mem_normalizer_iff.mp haN _).mp (Subgroup.inv_mem _ hv)
        have e : v * a * v⁻¹ * a⁻¹ = v * (a * v⁻¹ * a⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hv h1
      have hw2 : (v * a * v⁻¹ * a⁻¹) * (v * a * v⁻¹ * a⁻¹) = 1 := by
        have := hV.2 _ hw
        rwa [sq] at this
      have hc : dl (v * a * v⁻¹)⁻¹ a⁻¹ ∈ Q :=
        hc21 _ (Subgroup.inv_mem _ hy) _ (Subgroup.inv_mem _ haK)
      have e : (v * a * v⁻¹ * a⁻¹) * (v * a * v⁻¹ * a⁻¹) =
          (v * a * v⁻¹) * (v * a * v⁻¹) * dl (v * a * v⁻¹)⁻¹ a⁻¹ * (a * a)⁻¹ := by
        simp only [dl]
        group
      rw [hw2] at e
      have haa : a * a = (v * a * v⁻¹) * (v * a * v⁻¹) * dl (v * a * v⁻¹)⁻¹ a⁻¹ :=
        (mul_inv_eq_one.mp e.symm).symm
      have haa' : a * a ∈ Q := by
        refine hdisj ⟨Subgroup.mul_mem _ haK haK, ?_⟩
        rw [haa]
        exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hy) (Subgroup.mem_sup_right hc)
      apply haQ
      have h3 : a * (a * a) = 1 := by rw [← pow_three]; exact hPe.2 a haP
      rw [eq_inv_of_mul_eq_one_left h3]
      exact Q.inv_mem haa'
    have hK1 : conjByElt v K = K := (hmemK v hvGz).resolve_right hnotswap
    refine ⟨A38.map_conj_eq_iff.mp hK1, ?_⟩
    rcases hmemK' v hvGz with h | h
    · exfalso
      exact hne (Subgroup.map_injective (MulAut.conj v).injective (hK1.trans h.symm))
    · exact A38.map_conj_eq_iff.mp h
  have hnsup : ∀ {A B : Subgroup G} {g : G}, g ∈ Subgroup.normalizer (A : Set G) →
      g ∈ Subgroup.normalizer (B : Set G) →
        g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro A B g hA hB
    rw [Subgroup.mem_normalizer_iff_map_conj_eq] at hA hB ⊢
    rw [Subgroup.map_sup, hA, hB]
  have hdl : ∀ c ∈ fsuM T L, ∀ {J : Subgroup G}, c ∈ J ⊔ Q →
      (∀ v ∈ fsuV T I, v ∈ Subgroup.normalizer ((J ⊔ Q : Subgroup G) : Set G)) →
      ∀ v ∈ fsuV T I, dl c v ∈ fsuV T I ⊓ (J ⊔ Q) := by
    intro c hcM J hcJ hVJ v hv
    refine ⟨?_, ?_⟩
    · have : c * v * c⁻¹ ∈ fsuV T I := (Subgroup.mem_normalizer_iff.mp (hMV hcM) v).mp hv
      exact Subgroup.mul_mem _ this (Subgroup.inv_mem _ hv)
    · have h1 : v * c⁻¹ * v⁻¹ ∈ J ⊔ Q :=
        (Subgroup.mem_normalizer_iff.mp (hVJ v hv) _).mp (Subgroup.inv_mem _ hcJ)
      have e : dl c v = c * (v * c⁻¹ * v⁻¹) := by simp only [dl]; group
      rw [e]
      exact Subgroup.mul_mem _ hcJ h1
  have hdlA := hdl a haM haK fun v hv => hnsup (hVK v hv).1 (hGzQ (hVGz hv))
  have hdlB := hdl b hbM hbK fun v hv => hnsup (hVK v hv).2 (hGzQ (hVGz hv))
  have hPN : P ≤ Subgroup.normalizer (fsuV T I : Set G) := fun p hp => hMV (hXM (hPX hp))
  set ψ := Ch837.actOn hV e hPN with hψ
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    rw [Ch837.actOn_apply] at hp
    have h1 := (convI_eq_one_iff hV _).1 (congrHom_injective e (hp.trans (map_one _).symm))
    exact Subtype.ext (hPC _ p.2 h1)
  have hHS : ψ.range ≤ stabE := by
    rintro _ ⟨p, rfl⟩
    exact act_mem_stabE e he hz hez (hPN p.2) (hXM (hPX p.2)) (hXGz (hPX p.2))
  have hHc : Nat.card ψ.range = 9 := by
    rw [← hPc]
    exact (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  obtain ⟨g, hgS, hgE⟩ := exists_conj_mem_E9 hHS hHc
  have hinv : ∀ (h : MulAut WMod) (A : WMod), h A⁻¹ = (h A)⁻¹ := fun h A => map_inv h A
  have hmul : ∀ (h : MulAut WMod) (A B : WMod), h (A * B) = h A * h B :=
    fun h A B => map_mul h A B
  have hmoves : ∀ c ∈ P, ∀ hcN : c ∈ Subgroup.normalizer (fsuV T I : Set G),
      congrHom e (convI hV ⟨c, hcN⟩) ≠ 1 → ∃ v ∈ fsuV T I, dl c v ∉ ch83V5 e := by
    intro c hcP hcN hc1
    set cc : MulAut WMod := congrHom e (convI hV ⟨c, hcN⟩) with hcc
    have hcH : cc ∈ ψ.range := ⟨⟨c, hcP⟩, rfl⟩
    have hc'1 : g * cc * g⁻¹ ≠ 1 := fun h => hc1 (by
      have := conj_eq_one_iff.mp h
      exact this)
    obtain ⟨X', hX'⟩ := exists_not_mem_V5_of_mem_E9 (hgE _ hcH) hc'1
    set w := e.symm (g⁻¹ X') with hw
    refine ⟨w.val, w.val_mem, fun hdl' => hX' ?_⟩
    obtain ⟨w', hw'5, hw'v⟩ := (mem_ch83V5 e).1 hdl'
    obtain ⟨hact1, hact2⟩ := act_mul_inv e ⟨c, hcN⟩ w
    have hw' : w' = convI hV ⟨c, hcN⟩ w * w⁻¹ := IntMod.val_injective (hw'v.trans hact2.symm)
    rw [hw', ← hact1, hw, MulEquiv.apply_symm_apply, ← hcc] at hw'5
    have h2 := map_mem_V5_of_mem_stabE hgS hw'5
    rw [hmul, hinv, MulAut.apply_inv_self] at h2
    exact h2
  set x : MulAut WMod := congrHom e (convI hV ⟨a, haN⟩) with hxdef
  set y : MulAut WMod := congrHom e (convI hV ⟨b, hbN⟩) with hydef
  have hxH : x ∈ ψ.range := ⟨⟨a, haP⟩, rfl⟩
  have hyH : y ∈ ψ.range := ⟨⟨b, hbP⟩, rfl⟩
  have hne1 : ∀ c (hcP : c ∈ P), c ∉ Q → ψ ⟨c, hcP⟩ ≠ 1 := fun c hcP hcQ h => hcQ (by
    have h1 := congrArg Subtype.val (hψinj (h.trans (map_one ψ).symm))
    change c = 1 at h1
    rw [h1]
    exact Q.one_mem)
  have hx1 : x ≠ 1 := hne1 a haP haQ
  have hy1 : y ≠ 1 := hne1 b hbP hbQ
  have hxy : x ∉ Subgroup.zpowers y := by
    rintro ⟨n, hn⟩
    have h1 : ψ (⟨b, hbP⟩ ^ n) = ψ ⟨a, haP⟩ := by
      rw [map_zpow]
      exact hn
    have h2 : b ^ n = a := by simpa using congrArg Subtype.val (hψinj h1)
    apply haQ
    refine hdisj ⟨haK, ?_⟩
    rw [← h2]
    exact Subgroup.zpow_mem _ hbK n
  have hAQ : ¬ fsuV T I ⊓ (K ⊔ Q) ≤ Q := by
    intro h
    obtain ⟨v, hv, hvn⟩ := hmoves a haP haN hx1
    exact hvn (hVQ5 ▸ ⟨(hdlA v hv).1, h (hdlA v hv)⟩)
  have hBQ : ¬ fsuV T I ⊓ (K' ⊔ Q) ≤ Q := by
    intro h
    obtain ⟨v, hv, hvn⟩ := hmoves b hbP hbN hy1
    exact hvn (hVQ5 ▸ ⟨(hdlB v hv).1, h (hdlB v hv)⟩)
  have hZc : Subgroup.centralizer ({z} : Set G) ≤
      Subgroup.centralizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
    intro h hh
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
    have hzh : z * h = h * z := Subgroup.mem_centralizer_iff.mp hh z rfl
    exact ((Commute.zpow_left hzh k).eq)
  have hAB : ∀ u ∈ U, ∀ a' ∈ fsuV T I ⊓ (K ⊔ Q), ∀ b' ∈ fsuV T I ⊓ (K' ⊔ Q),
      dl b' (dl a' u) ∈ Subgroup.zpowers z := by
    intro u hu a' ha' b' hb'
    have huN : u ∈ Subgroup.normalizer (fsuV T I : Set G) := hMV (hTM (hUT hu))
    have h1 : dl a' u ∈ fsuV T I := by
      have h2 : u * a'⁻¹ * u⁻¹ ∈ fsuV T I :=
        (Subgroup.mem_normalizer_iff.mp huN _).mp (Subgroup.inv_mem _ ha'.1)
      have e : dl a' u = a' * (u * a'⁻¹ * u⁻¹) := by simp only [dl]; group
      rw [e]
      exact Subgroup.mul_mem _ ha'.1 h2
    have hcm := B2F.isElemAbelian_comm hV hb'.1 h1
    have e : dl b' (dl a' u) = 1 := by
      simp only [dl] at hcm ⊢
      rw [hcm]
      group
    rw [e]
    exact Subgroup.one_mem _
  have hquad := comm_comm_mem_of_quadratic' (H := Subgroup.centralizer ({z} : Set G)) (U := U)
    (Q := Q) (K₁ := K) (K₂ := K') (A := fsuV T I ⊓ (K ⊔ Q)) (B := fsuV T I ⊓ (K' ⊔ Q))
    (Z := Subgroup.zpowers z) hZc ((Subgroup.zpowers_le).mpr (hV5U (mem_ch83V5_z e hz hez)))
    hUGz hQGz hKGz hK'Gz (inf_le_left.trans hVGz) (inf_le_left.trans hVGz) hGzU hGzQ hQU h12
    inf_le_right inf_le_right hAB
    (fun S h1 h2 h3 => eq_or_eq_of_simple hsK hOK hKQ h1 h2 h3)
    (fun S h1 h2 h3 => eq_or_eq_of_simple hsK' hOK' hK'Q h1 h2 h3) hAQ hBQ
  have hdd : ∀ w : IntMod (fsuV T I) hV, ddW y x (e w) =
      e (convI hV ⟨b, hbN⟩ (convI hV ⟨a, haN⟩ w * w⁻¹) * (convI hV ⟨a, haN⟩ w * w⁻¹)⁻¹) := by
    intro w
    have hxw : x (e w) * (e w)⁻¹ = e (convI hV ⟨a, haN⟩ w * w⁻¹) := (act_mul_inv e ⟨a, haN⟩ w).1
    have hyw : ∀ w' : IntMod (fsuV T I) hV,
        y (e w') * (e w')⁻¹ = e (convI hV ⟨b, hbN⟩ w' * w'⁻¹) :=
      fun w' => (act_mul_inv e ⟨b, hbN⟩ w').1
    unfold ddW
    rw [hxw, hyw]
  have hddv : ∀ w : IntMod (fsuV T I) hV,
      (convI hV ⟨b, hbN⟩ (convI hV ⟨a, haN⟩ w * w⁻¹) * (convI hV ⟨a, haN⟩ w * w⁻¹)⁻¹).val =
        dl b (dl a w.val) := by
    intro w
    rw [(act_mul_inv e ⟨b, hbN⟩ _).2, (act_mul_inv e ⟨a, haN⟩ w).2]
  have h1 : ∀ X, ddW y x X ∈ V5 := by
    intro X
    obtain ⟨w, rfl⟩ : ∃ w, e w = X := ⟨e.symm X, e.apply_symm_apply X⟩
    rw [hdd]
    set w₂ := convI hV ⟨b, hbN⟩ (convI hV ⟨a, haN⟩ w * w⁻¹) * (convI hV ⟨a, haN⟩ w * w⁻¹)⁻¹
      with hw₂
    have hw₂5 : w₂.val ∈ ch83V5 e := by
      rw [hddv, ← hVQ5]
      exact ⟨(hdlB _ (hdlA _ w.val_mem).1).1, hc21 b hbK _ (hdlA _ w.val_mem).2⟩
    have := (mem_ch83V5_iff_of_mem e w₂.val_mem).1 hw₂5
    rwa [mk_val] at this
  have h2 : ∀ X ∈ V5, ddW y x X ∈ Z00 := by
    intro X hX
    obtain ⟨w, rfl⟩ : ∃ w, e w = X := ⟨e.symm X, e.apply_symm_apply X⟩
    have hwV5 : w.val ∈ ch83V5 e := (mem_ch83V5 e).2 ⟨w, hX, rfl⟩
    have hq := hquad w.val (hV5U hwV5) a haK b hbK
    rw [hdd]
    rcases mem_zpowers_of_orderOf_two hz2 hq with h | h
    · rw [← hddv] at h
      rw [IntMod.val_injective (h.trans (IntMod.val_one).symm), map_one]
      exact Z00.one_mem
    · rw [← hddv] at h
      have h' : convI hV ⟨b, hbN⟩ (convI hV ⟨a, haN⟩ w * w⁻¹) * (convI hV ⟨a, haN⟩ w * w⁻¹)⁻¹ =
          IntMod.mk hV ⟨z, hz⟩ := IntMod.val_injective h
      rw [h', hez]
      exact Subgroup.mem_zpowers _
  have hy'1 : g * y * g⁻¹ ≠ 1 := fun h => hy1 (by
    have := congrArg (fun t => g⁻¹ * t * g) h
    simpa [mul_assoc] using this)
  have hx'y' : g * x * g⁻¹ ∉ Subgroup.zpowers (g * y * g⁻¹) := by
    rintro ⟨n, hn⟩
    apply hxy
    refine ⟨n, ?_⟩
    have h3 : g * y ^ n * g⁻¹ = g * x * g⁻¹ := by
      rw [← hn]
      exact conj_zpow.symm
    have h4 := congrArg (fun t => g⁻¹ * t * g) h3
    simpa [mul_assoc] using h4
  apply not_forall_of_mem_E9 (hgE y hyH) (hgE x hxH) hy'1 hx'y'
  refine ⟨fun X => ?_, fun X hX => ?_⟩
  · rw [ddW_conj, mem_V5_iff_of_mem_stabE hgS]
    exact h1 _
  · rw [ddW_conj]
    exact map_mem_Z00_of_mem_stabE hgS (h2 _ (map_mem_V5_of_mem_stabE (stabE.inv_mem hgS) hX))

end CFSG.Quasithin.H13
