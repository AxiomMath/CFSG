module

public import CFSG.Quasithin.H13.L32AC32j
public import CFSG.Quasithin.H13.L32AC35a
public import CFSG.Quasithin.H13.L32ACSk8
public import CFSG.Quasithin.EmptyFaithful.SzN10A5

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

namespace CtxS

variable {K : Subgroup G} {t₀ : G} (C : CtxS T L V H K t₀)
include C

theorem mem_normalizer_of_odd {y : G} (hy : y ∈ H) (hodd : Odd (orderOf y)) :
    y ∈ Subgroup.normalizer (K : Set G) := by
  by_contra hyN
  have h1 := (C.two y hy).resolve_left hyN
  have hy' : y⁻¹ ∉ Subgroup.normalizer (K : Set G) := fun h => hyN (by simpa using inv_mem h)
  have h2 := (C.two y⁻¹ (inv_mem hy)).resolve_left hy'
  have h3 : y * y ∈ Subgroup.normalizer (K : Set G) := by
    have := mul_mem (inv_mem h2) h1
    rwa [show (t₀⁻¹ * y⁻¹)⁻¹ * (t₀⁻¹ * y) = y * y by group] at this
  obtain ⟨k, hk⟩ := hodd
  apply hyN
  have e : y = (y * y) ^ (k + 1) := by
    rw [← sq, ← pow_mul, show 2 * (k + 1) = orderOf y + 1 by omega, pow_succ,
      pow_orderOf_eq_one, one_mul]
  rw [e]
  exact pow_mem h3 _

end CtxS

theorem eq_conjClosure_sup (hA37 : A37ForSQTK) (hA38 : A38ForSQTK)
    (h76 : Lemma14_7_6) (h33 : Lemma14_7_33) (h36 : A36ForSQTK) (hlist : SQTKList3Dvd)
    (S : Setting147 G T L V H)
    {K : Subgroup G} (hK : K ∈ cComp H) (hT : ¬ T ≤ Subgroup.normalizer (K : Set G))
    (hA5 : IsAlt 5 (cStar K)) : H = conjClosure K T ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hKH := le_of_mem_cComp hK
  have hTH := Setting147.TH' S
  have hSH := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.fsu.sylow hTH
  have hmono : ∀ {A B : Subgroup G}, A ≤ B → modO2Image H A ≤ modO2Image H B :=
    fun h => Subgroup.map_mono fun _ hz => h hz
  have h121 := lemma_1_2_1_three S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian hA37 hA38
    S.hz.1.2 hK
  have hyN : ∀ y ∈ l1 T L V, y ^ 3 = 1 → y ∈ Subgroup.normalizer (K : Set G) :=
    fun y hy hy3 =>
      mem_normalizer_of_cube hKH (h121.imp_right fun h => h.1) (Setting147.l1H' S hy) hy3
  obtain ⟨t₀, ht₀T, ht₀N⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (K : Set G) := by
    by_contra h
    push Not at h
    exact hT h
  have ht₀H := hTH ht₀T
  have h2 : (conjSubgroupsBy H K).ncard = 2 := by
    rcases h121 with hn | ⟨h2, -⟩
    · exact absurd ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH).mp hn ht₀H) ht₀N
    · exact h2
  have C : CtxL2 T L V H K t₀ 2 :=
    ⟨⟨S, hK, ht₀T, ht₀N, mem_normalizer_or_of_ncard h2 ht₀H ht₀N, hyN⟩, le_rfl,
      C126.isPSL_two_two_two_of_alternating_five _ hA5⟩
  have hK₀H : conjClosure K T ≤ H := conjClosure_le fun s hs k hk =>
    H.mul_mem (H.mul_mem (hTH hs) (hKH hk)) (H.inv_mem (hTH hs))
  have hK₀n : H ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
    normal_conjClosure_of_pCoreOf_ne_bot S.hyp.fsu.qtke S.hyp.fsu.simple S.hyp.fsu.nonabelian
      hA37 hA38 S.hz.1.2 hSH hK
  have hKt : K.map (MulAut.conj t₀ : G →* G) ≤ conjClosure K T := by
    rintro _ ⟨k, hk, rfl⟩
    simpa using mem_conjClosure ht₀T hk
  have hK₀le : conjClosure K T ≤ K ⊔ K.map (MulAut.conj t₀ : G →* G) := by
    refine conjClosure_le fun s hs k hk => ?_
    rcases C.two s (hTH hs) with h | h
    · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp h k).mp hk)
    · refine Subgroup.mem_sup_right (Subgroup.mem_map.mpr ⟨(t₀⁻¹ * s) * k * (t₀⁻¹ * s)⁻¹,
        (Subgroup.mem_normalizer_iff.mp h k).mp hk, ?_⟩)
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply]
      group
  have hsup : modO2Image H (conjClosure K T) ≤
      modO2Image H K ⊔ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) := by
    refine (hmono hK₀le).trans ?_
    show ((K ⊔ K.map (MulAut.conj t₀ : G →* G)).subgroupOf H).map _ ≤ _
    rw [Subgroup.subgroupOf_sup hKH C.hKtH, Subgroup.map_sup]
    exact le_rfl
  have hK₀bn : (modO2Image H (conjClosure K T)).Normal := by
    have h1 : ((conjClosure K T).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀H).mpr hK₀n
    exact h1.map _ (QuotientGroup.mk'_surjective _)
  have hCbot : Subgroup.centralizer (modO2Image H (conjClosure K T) :
      Set (↥H ⧸ CFSG.pCore 2 ↥H)) = ⊥ := by
    have hC3 : Nat.Coprime 3 (Nat.card ↥(Subgroup.centralizer (modO2Image H (conjClosure K T) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)))) := by
      refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => ?_
      obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card' 3 h3
      have hc3 : (c : ↥H ⧸ CFSG.pCore 2 ↥H) ^ 3 = 1 := by
        rw [← hc, ← Subgroup.orderOf_coe]
        exact pow_orderOf_eq_one _
      have hc1 : (c : ↥H ⧸ CFSG.pCore 2 ↥H) ≠ 1 := fun h => by
        have : c = 1 := Subtype.ext h
        rw [this, orderOf_one] at hc
        omega
      have hcK : ∀ m ∈ modO2Image H K, (c : ↥H ⧸ CFSG.pCore 2 ↥H) * m = m * c := fun m hm =>
        ((Subgroup.mem_centralizer_iff.mp c.2) m (hmono (le_conjClosure K T) hm)).symm
      have hcK' : ∀ m ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)),
          (c : ↥H ⧸ CFSG.pCore 2 ↥H) * m = m * c := fun m hm =>
        ((Subgroup.mem_centralizer_iff.mp c.2) m (hmono hKt hm)).symm
      exact hc1 (eq_one_of_centralizes_two (pRank_three_star_le_two S)
        (fun a ha b hb => C.commute_kb hA37 ha hb) C.center_kb C.center_kt C.three_dvd_kb
        C.three_dvd_kt hcK hcK' hc3)
    have hle : Subgroup.centralizer (modO2Image H (conjClosure K T) :
        Set (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ CFSG.pPrimeCore 3 (↥H ⧸ CFSG.pCore 2 ↥H) :=
      le_sSup (s := {N : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) | N.Normal ∧ Nat.Coprime 3 (Nat.card N)})
        ⟨Subgroup.normal_centralizer, hC3⟩
    rw [pPrimeCore_star_eq_bot h76 h33 h36 hlist S] at hle
    exact eq_bot_iff.mpr hle
  obtain ⟨α, hαs, hαk⟩ : ∃ α : ↥K →* alternatingGroup (Fin 5), Function.Surjective α ∧
      α.ker = CFSG.pCore 2 ↥K := by
    obtain ⟨e⟩ := hA5
    refine ⟨(e.toMonoidHom.comp (cStarEquiv K).symm.toMonoidHom).comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥K)), ?_, ?_⟩
    · exact (e.surjective.comp (cStarEquiv K).symm.surjective).comp
        (QuotientGroup.mk'_surjective _)
    · ext x
      simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have hOK : pCoreOf 2 K ≤ pCoreOf 2 H := A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  have hodd : ∀ y ∈ H, Odd (orderOf y) → y ∈ conjClosure K T ⊔ pCoreOf 2 H := by
    intro y hyH hy
    have hyK := C.mem_normalizer_of_odd hyH hy
    have hy'H : t₀⁻¹ * y * t₀ ∈ H := mul_mem (mul_mem (inv_mem ht₀H) hyH) ht₀H
    have hy' : Odd (orderOf (t₀⁻¹ * y * t₀)) := by
      rw [show t₀⁻¹ * y * t₀ = MulAut.conj t₀⁻¹ y by simp,
        MulEquiv.orderOf_eq]
      exact hy
    have hy'K := C.mem_normalizer_of_odd hy'H hy'
    obtain ⟨x₁, hx₁K, hx₁⟩ := szN10_alt5_inner α hαs hαk hyK hy
    obtain ⟨x', hx'K, hx'⟩ := szN10_alt5_inner α hαs hαk hy'K hy'
    have hx₁H : x₁ ∈ H := hKH hx₁K
    have hx₂ : t₀ * x' * t₀⁻¹ ∈ K.map (MulAut.conj t₀ : G →* G) := ⟨x', hx'K, rfl⟩
    have hx₂H : t₀ * x' * t₀⁻¹ ∈ H := C.hKtH hx₂
    have hzH : (x₁ * (t₀ * x' * t₀⁻¹))⁻¹ * y ∈ H :=
      mul_mem (inv_mem (mul_mem hx₁H hx₂H)) hyH
    set X₁ := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x₁, hx₁H⟩ with hX₁
    set X₂ := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨t₀ * x' * t₀⁻¹, hx₂H⟩ with hX₂
    set Yb := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨y, hyH⟩ with hYb
    have hX₁K : X₁ ∈ modO2Image H K := mem_modO2Image'.mpr ⟨_, hx₁K, rfl⟩
    have hX₂K : X₂ ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) :=
      mem_modO2Image'.mpr ⟨_, hx₂, rfl⟩
    have hF1 : ∀ m ∈ modO2Image H K, m * (X₁⁻¹ * Yb) = (X₁⁻¹ * Yb) * m := by
      intro m hm
      obtain ⟨a, ha, rfl⟩ := mem_modO2Image'.mp hm
      have hbH : x₁⁻¹ * y ∈ H := mul_mem (inv_mem hx₁H) hyH
      have e : X₁⁻¹ * Yb = QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x₁⁻¹ * y, hbH⟩ := by
        rw [hX₁, hYb, ← map_inv, ← map_mul]
        rfl
      rw [e]
      exact Setting147.mk_commute_of_mem a ⟨_, hbH⟩ (hOK (hx₁ a ha))
    have hF2 : ∀ m ∈ modO2Image H (K.map (MulAut.conj t₀ : G →* G)),
        m * (X₂⁻¹ * Yb) = (X₂⁻¹ * Yb) * m := by
      intro m hm
      obtain ⟨a, ha, rfl⟩ := mem_modO2Image'.mp hm
      obtain ⟨b, hb, hab⟩ := Subgroup.mem_map.mp ha
      simp only [MonoidHom.coe_ofClass, MulAut.conj_apply] at hab
      have hbH : (t₀ * x' * t₀⁻¹)⁻¹ * y ∈ H := mul_mem (inv_mem hx₂H) hyH
      have e : X₂⁻¹ * Yb = QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨(t₀ * x' * t₀⁻¹)⁻¹ * y, hbH⟩ := by
        rw [hX₂, hYb, ← map_inv, ← map_mul]
        rfl
      rw [e]
      refine Setting147.mk_commute_of_mem a ⟨_, hbH⟩ ?_
      have h1 := hOK (hx' b hb)
      have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H ht₀H) _).mp h1
      have e2 : t₀ * (b * (x'⁻¹ * (t₀⁻¹ * y * t₀)) * b⁻¹ * (x'⁻¹ * (t₀⁻¹ * y * t₀))⁻¹) * t₀⁻¹ =
          (a : G) * ((t₀ * x' * t₀⁻¹)⁻¹ * y) * (a : G)⁻¹ * ((t₀ * x' * t₀⁻¹)⁻¹ * y)⁻¹ := by
        rw [← hab]
        group
      rw [e2] at h2
      exact h2
    have hZ : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, hzH⟩ = X₂⁻¹ * (X₁⁻¹ * Yb) := by
      rw [hX₁, hX₂, hYb, ← map_inv, ← map_inv, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (by simp [mul_assoc])
    have hc12 : X₁ * X₂ = X₂ * X₁ := C.commute_kb hA37 hX₁K hX₂K
    have hZ' : X₂⁻¹ * (X₁⁻¹ * Yb) = X₁⁻¹ * (X₂⁻¹ * Yb) := by
      have : X₂⁻¹ * X₁⁻¹ = X₁⁻¹ * X₂⁻¹ := by
        rw [← mul_inv_rev, ← mul_inv_rev, hc12]
      rw [← mul_assoc, this, mul_assoc]
    have hcen : modO2Image H K ⊔ modO2Image H (K.map (MulAut.conj t₀ : G →* G)) ≤
        Subgroup.centralizer ({QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, hzH⟩} :
          Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      refine sup_le (fun m hm => ?_) (fun m hm => ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff, hZ]
        have h1 : m * X₂⁻¹ = X₂⁻¹ * m := by
          have := C.commute_kb hA37 hm (inv_mem hX₂K)
          exact this
        calc m * (X₂⁻¹ * (X₁⁻¹ * Yb)) = X₂⁻¹ * (m * (X₁⁻¹ * Yb)) := by
              rw [← mul_assoc, h1, mul_assoc]
          _ = X₂⁻¹ * (X₁⁻¹ * Yb) * m := by rw [hF1 m hm]; group
      · rw [Subgroup.mem_centralizer_singleton_iff, hZ, hZ']
        have h1 : m * X₁⁻¹ = X₁⁻¹ * m := (C.commute_kb hA37 (inv_mem hX₁K) hm).symm
        calc m * (X₁⁻¹ * (X₂⁻¹ * Yb)) = X₁⁻¹ * (m * (X₂⁻¹ * Yb)) := by
              rw [← mul_assoc, h1, mul_assoc]
          _ = X₁⁻¹ * (X₂⁻¹ * Yb) * m := by rw [hF2 m hm]; group
    have hzc : QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨_, hzH⟩ ∈
        Subgroup.centralizer (modO2Image H (conjClosure K T) : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := hcen (hsup hg)
      rw [Subgroup.mem_centralizer_singleton_iff] at this
      exact this
    rw [hCbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      ← pCoreOf_subgroupOf', Subgroup.mem_subgroupOf] at hzc
    have e : y = x₁ * (t₀ * x' * t₀⁻¹) * ((x₁ * (t₀ * x' * t₀⁻¹))⁻¹ * y) := by group
    rw [e]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (le_conjClosure K T hx₁K))
      (Subgroup.mem_sup_left (hKt hx₂))) (Subgroup.mem_sup_right hzc)
  have hNH : conjClosure K T ⊔ pCoreOf 2 H ≤ H := sup_le hK₀H (pCoreOf_le 2 H)
  have hNn : ((conjClosure K T ⊔ pCoreOf 2 H).subgroupOf H).Normal := by
    rw [Subgroup.subgroupOf_sup hK₀H (pCoreOf_le 2 H)]
    have h1 : ((conjClosure K T).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀H).mpr hK₀n
    have h2 : ((pCoreOf 2 H).subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le 2 H)).mpr
        (le_normalizer_pCoreOf 2 H)
    exact Subgroup.sup_normal _ _
  have hQ2 : IsPGroup 2 (↥H ⧸ (conjClosure K T ⊔ pCoreOf 2 H).subgroupOf H) := by
    intro q
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨a, m, hm, ha⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos h).ne'
    refine ⟨a, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    have hho : Odd (orderOf (h ^ 2 ^ a)) := by
      rw [orderOf_pow_of_dvd (by positivity) (by rw [ha]; exact dvd_mul_right _ _), ha,
        Nat.mul_div_cancel_left _ (by positivity)]
      exact hm
    refine hodd _ (h ^ 2 ^ a).2 ?_
    rwa [Subgroup.orderOf_coe]
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQ2
  have hidx : (conjClosure K T ⊔ pCoreOf 2 H).relIndex H = 2 ^ j := by
    rw [Subgroup.relIndex, Subgroup.index_eq_card]
    exact hj
  have hNT : conjClosure K T ⊔ pCoreOf 2 H ⊔ T ≤ H := sup_le hNH hTH
  have h1 : (conjClosure K T ⊔ pCoreOf 2 H ⊔ T).relIndex H ∣ 2 ^ j := by
    rw [← hidx]
    exact ⟨_, (Subgroup.relIndex_mul_relIndex _ _ H le_sup_left hNT).symm.trans
      (mul_comm _ _)⟩
  have h2 : (conjClosure K T ⊔ pCoreOf 2 H ⊔ T).relIndex H ∣ T.relIndex H :=
    ⟨_, (Subgroup.relIndex_mul_relIndex _ _ H le_sup_right hNT).symm.trans (mul_comm _ _)⟩
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  have hi0 : i = 0 := by
    by_contra hne
    exact hSH.2.2 ((hi ▸ dvd_pow_self 2 hne).trans h2)
  rw [hi0, pow_zero, Subgroup.relIndex_eq_one] at hi
  refine le_antisymm (hi.trans (sup_le (sup_le le_sup_left ?_) le_sup_right))
    (sup_le hK₀H hTH)
  exact (L32A.pCoreOf_le_of_le S.hyp hTH).trans le_sup_right

theorem lemma14_7_32_L2_red_of
    (h7 : Lemma14_7_7) (h30 : Lemma14_7_30) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hA39 : A39ForSQTK)
    (h29 : Thm14_7_29) (hSzB : SzAutBorelThree) (hD36 : D36) (hD37 : D37) (hD321 : D321)
    (hI5 : Insp5a) (h128 : Lemma128One) (h76 : Lemma14_7_6) (h36 : A36ForSQTK)
    (hlist : SQTKList3Dvd) : Lemma14_7_32_L2_red := by
  intro G _ _ T L V H S K hK hT hL2
  obtain ⟨hK₁, hA5, hl1⟩ := mem_cComp_g1 h7 h30 h1222 h1332 h1334 hA37 hA38 hA39 h29 hSzB hD36
    hD37 hD321 hI5 h128 S hK hT hL2
  have S₁ := setting_g1 h1332 h1334 S
  have h33 := lemma14_7_33_of h7 h30 h1222 h1332 h1334 hA37 hA38 h29 hSzB
  exact ⟨S₁, hK₁, hT, hA5,
    eq_conjClosure_sup hA37 hA38 h76 h33 h36 hlist S₁ hK₁ hT hA5, hl1⟩

end CFSG.Quasithin.H13.L32A.C
