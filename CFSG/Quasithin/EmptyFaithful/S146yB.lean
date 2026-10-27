module

public import CFSG.Quasithin.EmptyFaithful.S146yCom
public import CFSG.Quasithin.EmptyFaithful.S146xRk
public import CFSG.Quasithin.EmptyFaithful.S146F22

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

section TB

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

local notation "Zz" => quasithinOmegaOneCenter T

omit [Finite G] in
theorem commutator_le_U (T M : Subgroup G) {K : Subgroup G} (hK : K ≤ mcOf T) :
    ⁅uOfL22 T M, K⁆ ≤ uOfL22 T M :=
  S145.commutator_le_of_le_normalizer (hK.trans (le_normalizer_conjClosure _ _))

theorem inf_commutator_le_of_ne (S : Setting146 G T M) (c23 : Conc14623 T M) {K K' : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hK' : K' ∈ cComp (mcOf T)) (hne : K' ≠ K) :
    (⁅uOfL22 T M, K⁆ ⊔ Zz) ⊓ (⁅uOfL22 T M, K'⁆ ⊔ Zz) ≤ Zz := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hKU := commutator_le_U T M (le_of_mem_cComp hK)
  have hKU' := commutator_le_U T M (le_of_mem_cComp hK')
  rintro x ⟨hx1, hx2⟩
  have hxN : x ∈ Subgroup.normalizer (Zz : Set G) := by
    have h1 : ⁅uOfL22 T M, K⁆ ⊔ Zz ≤ Subgroup.normalizer (Zz : Set G) :=
      sup_le (hKU.trans hUN) Subgroup.le_normalizer
    exact h1 hx1
  have hdir := c23.2.2.2 K hK
  have hmem : ∀ K₀ : Subgroup G, ⁅uOfL22 T M, K₀⁆ ≤ uOfL22 T M → x ∈ ⁅uOfL22 T M, K₀⁆ ⊔ Zz →
      secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨x, hxN⟩ ∈ tildeOf Zz ⁅uOfL22 T M, K₀⁆ := by
    intro K₀ hK₀ hx
    have hN : ⁅uOfL22 T M, K₀⁆ ≤ Subgroup.normalizer (Zz : Set G) := hK₀.trans hUN
    have hprod := Subgroup.coe_mul_of_left_le_normalizer_right ⁅uOfL22 T M, K₀⁆ Zz hN
    have hx' : x ∈ ((⁅uOfL22 T M, K₀⁆ ⊔ Zz : Subgroup G) : Set G) := hx
    rw [hprod] at hx'
    obtain ⟨w, hw, z, hz, rfl⟩ := Set.mem_mul.mp hx'
    have hwN : w ∈ Subgroup.normalizer (Zz : Set G) := hN hw
    have h1 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨w * z, hxN⟩ =
        secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨w, hwN⟩ := by
      rw [secMk_eq_secMk_iff]
      simpa using hz
    rw [h1]
    exact secMk_mem_secImg hw
  have h1 := hmem K hKU hx1
  have h2 := hmem K' hKU' hx2
  have h3 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨x, hxN⟩ ∈
      ⨆ K'' ∈ {K'' | K'' ∈ cComp (mcOf T) ∧ K'' ≠ K}, tildeOf Zz ⁅uOfL22 T M, K''⁆ :=
    (le_iSup₂_of_le (f := fun K'' (_ : K'' ∈ {K'' | K'' ∈ cComp (mcOf T) ∧ K'' ≠ K}) =>
      tildeOf Zz ⁅uOfL22 T M, K''⁆) K' ⟨hK', hne⟩ le_rfl) h2
  have h4 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨x, hxN⟩ ∈
      tildeOf Zz ⁅uOfL22 T M, K⁆ ⊓ ⨆ K'' ∈ {K'' | K'' ∈ cComp (mcOf T) ∧ K'' ≠ K},
        tildeOf Zz ⁅uOfL22 T M, K''⁆ := ⟨h1, h3⟩
  rw [hdir] at h4
  exact secMk_eq_one_iff.mp (Subgroup.mem_bot.mp h4)

theorem mem_pCoreOf_of_acts_trivially (S : Setting146 G T M) (c23 : Conc14623 T M)
    {K Kp : Subgroup G} (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) {x : G}
    (hxH : x ∈ mcOf T) (hxK : ∀ y ∈ ⁅uOfL22 T M, K⁆ ⊔ Zz, x * y * x⁻¹ * y⁻¹ ∈ Zz)
    (hxKp : ∀ y ∈ ⁅uOfL22 T M, Kp⁆ ⊔ Zz, x * y * x⁻¹ * y⁻¹ ∈ Zz) :
    x ∈ pCoreOf 2 (mcOf T) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hZU : Zz ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
  have hxcomm : ∀ z ∈ Zz, x * z = z * x := fun z hz => S146T.comm_Z hxH hz
  set Cx : Subgroup G := centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers x) with hCx
  have hcrit : ∀ w ∈ uOfL22 T M, x * w * x⁻¹ * w⁻¹ ∈ Zz → w ∈ Cx := by
    intro w hw h
    have hc : w * x * w⁻¹ * x⁻¹ ∈ Zz := by
      have e : w * x * w⁻¹ * x⁻¹ = (x * w * x⁻¹ * w⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ h
    exact mem_centralizerMod_zpowers hw (hUN hw) hxcomm hc
  have hKle : ∀ K₀ : Subgroup G, ⁅uOfL22 T M, K₀⁆ ≤ uOfL22 T M →
      (∀ y ∈ ⁅uOfL22 T M, K₀⁆ ⊔ Zz, x * y * x⁻¹ * y⁻¹ ∈ Zz) → ⁅uOfL22 T M, K₀⁆ ≤ Cx :=
    fun K₀ hK₀ h w hw => hcrit w (hK₀ hw) (h w (Subgroup.mem_sup_left hw))
  have hZC : Zz ≤ Cx := fun z hz => by
    refine hcrit z (hZU hz) ?_
    have : x * z * x⁻¹ * z⁻¹ = 1 := by rw [hxcomm z hz]; group
    rw [this]
    exact Subgroup.one_mem _
  have hcentC : centralizerMod Zz (uOfL22 T M) (mcOf T) ≤ Cx := by
    intro c hc
    refine ⟨hc.1, hc.2.1, fun v hv => hc.2.2 v ((Subgroup.zpowers_le.mpr hxH) hv)⟩
  have hRHS : (⨆ K' ∈ cComp (mcOf T), tildeOf Zz ⁅uOfL22 T M, K'⁆) ⊔
      tildeOf Zz (centralizerMod Zz (uOfL22 T M) (mcOf T)) ≤ tildeOf Zz Cx := by
    refine sup_le (iSup₂_le fun K' hK' => ?_) (secImg_mono hcentC)
    rcases hcomps K' hK' with rfl | rfl
    · exact secImg_mono (hKle K' (commutator_le_U T M (le_of_mem_cComp hK'))
        (hxK))
    · exact secImg_mono (hKle K' (commutator_le_U T M (le_of_mem_cComp hK')) hxKp)
  have hall : ∀ w ∈ uOfL22 T M, w ∈ Cx := by
    intro w hw
    have h1 : secMk (Subgroup.normalizer (Zz : Set G)) Zz ⟨w, hUN hw⟩ ∈ tildeOf Zz (uOfL22 T M) :=
      secMk_mem_secImg hw
    rw [c23.2.2.1] at h1
    have h2 := hRHS h1
    exact (secMk_mem_secImg_iff hZC).mp h2
  rw [← S.lemma_14_5_15_four hG]
  refine ⟨hxH, S.normalizer_Z.ge hxH, fun w hw => ?_⟩
  have h := (hall w hw).2.2 x (Subgroup.mem_zpowers x)
  have e : x * w * x⁻¹ * w⁻¹ = (w * x * w⁻¹ * x⁻¹)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ h

theorem mem_pCoreOf_of_commutators_mem_pair (S : Setting146 G T M) (hB : HypB146 T M)
    {K Kp : Subgroup G} (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) {x : G}
    (hxH : x ∈ mcOf T) (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (mcOf T))
    (hxKp : ∀ k ∈ Kp, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (mcOf T)) : x ∈ pCoreOf 2 (mcOf T) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(mcOf T)) ⟨x, hxH⟩ = 1 := by
    refine eq_one_of_commute_modO2Image (hB _ hG) fun L hL r hr => ?_
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hr
    have ha' : (a : G) ∈ L := Subgroup.mem_subgroupOf.mp ha
    have hxa : x * (a : G) * x⁻¹ * (a : G)⁻¹ ∈ pCoreOf 2 (mcOf T) := by
      rcases hcomps L hL with rfl | rfl
      · exact hxK _ ha'
      · exact hxKp _ ha'
    obtain ⟨c', hcP, hcc⟩ := Subgroup.mem_map.mp hxa
    have hcab : c' = ⟨x, hxH⟩ * a * ⟨x, hxH⟩⁻¹ * a⁻¹ := Subtype.ext (by simpa using hcc)
    have h2 : (QuotientGroup.mk' (CFSG.pCore 2 ↥(mcOf T)))
        (⟨x, hxH⟩ * a * ⟨x, hxH⟩⁻¹ * a⁻¹) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hcab ▸ (by exact hcP))
    simp only [map_mul, map_inv] at h2
    exact commutatorElement_eq_one_iff_mul_comm.mp (by simpa [commutatorElement_def] using h2)
  have h3 := (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥(mcOf T)) _).mp h1
  exact ⟨_, h3, rfl⟩

omit [Finite G] in
theorem swap_of_not_mem_normalizer {K Kp : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) {x : G} (hxH : x ∈ mcOf T)
    (hxn : x ∉ Subgroup.normalizer (K : Set G)) : conjSub x K = Kp ∧ conjSub x Kp = K := by
  have hinj : ∀ (x : G) (A B : Subgroup G), conjSub x A = conjSub x B → A = B := fun x A B h =>
    Subgroup.map_injective (f := (MulAut.conj x).toMonoidHom) (MulAut.conj x).injective h
  have h1 : conjSub x K = Kp := by
    rcases hcomps _ (map_conj_mem_cComp hK hxH) with h | h
    · exact absurd (mem_normalizer_of_conjSub_eq h) hxn
    · exact h
  refine ⟨h1, ?_⟩
  rcases hcomps _ (map_conj_mem_cComp hKp hxH) with h | h
  · exact h
  · exact absurd (hinj x _ _ (h.trans h1.symm)) hne

theorem conjSub_commutator_sup (S : Setting146 G T M) {K : Subgroup G} {a : G} (haH : a ∈ mcOf T) :
    conjSub a (⁅uOfL22 T M, K⁆ ⊔ Zz) = ⁅uOfL22 T M, conjSub a K⁆ ⊔ Zz := by
  have haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ haH
  rw [conjSub_sup, ← conjSub_commutator, conjSub_eq_of_mem_normalizer haU,
    conjSub_eq_of_mem_normalizer (S.normalizer_Z.ge haH)]

theorem sixtyfour_le_relIndex (S : Setting146 G T M) (c23 : Conc14623 T M) {K Kp : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hrank : mIdx (⁅uOfL22 T M, K⁆ ⊔ Zz) Zz = 6) {a : G} (haH : a ∈ mcOf T)
    (hswa : conjSub a K = Kp) :
    64 ≤ (centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a)).relIndex (uOfL22 T M) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hZU : Zz ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
  have haZ : a ∈ Subgroup.normalizer (Zz : Set G) := S.normalizer_Z.ge haH
  have hUab : IsElemAbelian 2 (uOfL22 T M) := S.lemma_14_5_15_two hG
  set Uk : Subgroup G := ⁅uOfL22 T M, K⁆ ⊔ Zz with hUk
  set Ukp : Subgroup G := ⁅uOfL22 T M, Kp⁆ ⊔ Zz with hUkp
  have hkU : Uk ≤ uOfL22 T M := sup_le (commutator_le_U T M (le_of_mem_cComp hK)) hZU
  have hdir : Uk ⊓ Ukp ≤ Zz := inf_commutator_le_of_ne S c23 hK hKp hne
  have hconj : conjSub a Uk = Ukp := by
    rw [hUk, conjSub_commutator_sup S haH, hswa]
  set Ca : Subgroup G := centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a) with hCa
  have hZCa : Zz ≤ Ca := fun z hz => by
    refine ⟨hZU hz, hUN (hZU hz), fun v hv => ?_⟩
    have hvH : v ∈ mcOf T := (Subgroup.zpowers_le.mpr haH) hv
    have : z * v * z⁻¹ * v⁻¹ = 1 := by rw [← S146T.comm_Z hvH hz]; group
    rw [this]
    exact Subgroup.one_mem _
  have hinf : Ca ⊓ Uk = Zz := by
    refine le_antisymm (fun x hx => ?_) (le_inf hZCa (le_sup_right : Zz ≤ Uk))
    obtain ⟨hxC, hxUk⟩ := hx
    have hz := hxC.2.2 a (Subgroup.mem_zpowers a)
    set z := x * a * x⁻¹ * a⁻¹ with hzdef
    have e : a * x * a⁻¹ = z⁻¹ * x := by rw [hzdef]; group
    have h1 : a * x * a⁻¹ ∈ conjSub a Uk := mul_mem_conjSub hxUk
    rw [hconj] at h1
    have h2 : a * x * a⁻¹ ∈ Uk := by
      rw [e]
      exact Uk.mul_mem (Uk.inv_mem ((le_sup_right : Zz ≤ Uk) hz)) hxUk
    have h3 : a * x * a⁻¹ ∈ Zz := hdir ⟨h2, h1⟩
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ haZ) _).mp h3
    simpa [mul_assoc] using this
  have hpg : IsPGroup 2 Uk := by
    have hQ : IsPGroup 2 (uOfL22 T M) := (isPGroup_of_isElemAbelian hUab)
    exact hQ.to_le hkU
  have h64 : (quasithinOmegaOneCenter T).relIndex Uk = 64 := by
    rw [HypF98.relIndex_eq_two_pow_mIdx hpg, hrank]
    norm_num
  have h1 : Ca.relIndex Uk = 64 := by
    rw [← Subgroup.inf_relIndex_right Ca Uk, hinf, h64]
  have h2 : Ca.relIndex Uk ≤ Ca.relIndex (uOfL22 T M) :=
    Subgroup.relIndex_le_of_le_right hkU (by
      unfold Subgroup.relIndex
      exact Subgroup.index_ne_zero_of_finite)
  omega

theorem relIndex_inf_pCoreOf_le_eight (S : Setting146 G T M) (hB : HypB146 T M) {K Kp A : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (hL3 : KbarIsL3Two K)
    (hAH : A ≤ mcOf T) (hAab : IsElemAbelian 2 A) {a : G} (haA : a ∈ A) (hswa : conjSub a K = Kp) :
    (A ⊓ pCoreOf 2 (mcOf T)).relIndex A ≤ 8 := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  set A₀ : Subgroup G := A ⊓ Subgroup.normalizer (K : Set G) with hA₀
  have hA₀A : A₀ ≤ A := inf_le_left
  have hA₀N : A₀ ≤ Subgroup.normalizer (K : Set G) := inf_le_right
  have hcos : ∀ x ∈ A, x * a ∈ A₀ ∨ x ∈ A₀ := by
    intro x hx
    by_cases hxn : x ∈ Subgroup.normalizer (K : Set G)
    · exact Or.inr ⟨hx, hxn⟩
    · left
      refine ⟨A.mul_mem hx haA, ?_⟩
      obtain ⟨-, h2⟩ := swap_of_not_mem_normalizer hK hKp hne hcomps (hAH hx) hxn
      apply mem_normalizer_of_conjSub_eq
      rw [conjSub_mul, hswa, h2]
  have hdvd2 : A₀.relIndex A ∣ 2 := Subgroup.relIndex_dvd_two_iff.mpr ⟨a, haA, hcos⟩
  have hA₀ab : IsElemAbelian 2 A₀ := isElemAbelian_two_of_le hAab hA₀A
  let Φ : ↥A₀ →* MulAut (KBar K) := (kbarActHom K).comp (Subgroup.inclusion hA₀N)
  have hΦmk : ∀ (x : ↥A₀) (k : ↥K), Φ x (QuotientGroup.mk k) =
      QuotientGroup.mk (conjAutOn K (x : G) (hA₀N x.2) k) := fun x k =>
    kbarActHom_mk K (Subgroup.inclusion hA₀N x) k
  have hcommX : ∀ x y : ↥A₀, x * y = y * x := fun x y =>
    Subtype.ext (isElemAbelian_comm hA₀ab x.2 y.2)
  have hsqX : ∀ x : ↥A₀, x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa using isElemAbelian_pow_eq_one hA₀ab x.2)
  have hEA : CFSG.IsElementaryAbelian 2 ↥(Φ.range) := by
    refine { toIsMulCommutative := ⟨⟨fun a b => ?_⟩⟩, exponent_dvd_p := ?_ }
    · obtain ⟨a, x, rfl⟩ := a
      obtain ⟨b, y, rfl⟩ := b
      apply Subtype.ext
      show Φ x * Φ y = Φ y * Φ x
      rw [← map_mul, ← map_mul, hcommX]
    · refine Monoid.exponent_dvd_iff_forall_pow_eq_one.2 fun a => ?_
      obtain ⟨a, x, rfl⟩ := a
      apply Subtype.ext
      show (Φ x) ^ 2 = 1
      rw [← map_pow, hsqX, map_one]
  have hcard4 : Nat.card Φ.range ≤ 2 ^ 2 := card_le_four_of_kbarIsL3Two hL3 Φ.range
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  set A₂ : Subgroup G := Φ.ker.map A₀.subtype with hA₂
  have hA₂A₀ : A₂ ≤ A₀ := by
    rintro _ ⟨y, -, rfl⟩
    exact y.2
  have hA₂Q : A₂ ≤ A ⊓ pCoreOf 2 (mcOf T) := by
    rintro _ ⟨y, hy, rfl⟩
    have hy1 : Φ y = 1 := hy
    have hyA : (y : G) ∈ A := hA₀A y.2
    refine ⟨hyA, ?_⟩
    have hcommK : ∀ k ∈ K, (y : G) * k * (y : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 (mcOf T) := by
      intro k hk
      have h1 := congrArg (fun α : MulAut (KBar K) => α (QuotientGroup.mk (⟨k, hk⟩ : ↥K))) hy1
      simp only [hΦmk, MulAut.one_apply] at h1
      have h2 := QuotientGroup.eq.mp h1.symm
      have h3 : k⁻¹ * ((y : G) * k * (y : G)⁻¹) ∈ pCoreOf 2 K := Subgroup.mem_subgroupOf.mp h2
      have h4 : k * (k⁻¹ * ((y : G) * k * (y : G)⁻¹)) * k⁻¹ ∈ pCoreOf 2 K :=
        (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 K hk) _).mp h3
      have e : (y : G) * k * (y : G)⁻¹ * k⁻¹ = k * (k⁻¹ * ((y : G) * k * (y : G)⁻¹)) * k⁻¹ := by
        group
      rw [e]
      exact hQK h4
    have haH : a ∈ mcOf T := hAH haA
    have hcommKp : ∀ k' ∈ Kp, (y : G) * k' * (y : G)⁻¹ * k'⁻¹ ∈ pCoreOf 2 (mcOf T) := by
      intro k' hk'
      have hk : a⁻¹ * k' * a ∈ K := by
        rw [← hswa] at hk'
        exact mem_conjSub.mp hk'
      have h1 := hcommK _ hk
      have hya : (y : G) * a = a * (y : G) := isElemAbelian_comm hAab hyA haA
      have h2 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (mcOf T) haH) _).mp h1
      have e1 : a * (y : G) * a⁻¹ = y := by rw [← hya]; group
      have e2 : a * (y : G)⁻¹ * a⁻¹ = (y : G)⁻¹ := by
        have : (y : G)⁻¹ * a = a * (y : G)⁻¹ := (Commute.inv_left (hya : Commute (y : G) a)).eq
        rw [← this]; group
      have e : a * ((y : G) * (a⁻¹ * k' * a) * (y : G)⁻¹ * (a⁻¹ * k' * a)⁻¹) * a⁻¹ =
          (y : G) * k' * (y : G)⁻¹ * k'⁻¹ := by
        calc a * ((y : G) * (a⁻¹ * k' * a) * (y : G)⁻¹ * (a⁻¹ * k' * a)⁻¹) * a⁻¹
            = (a * (y : G) * a⁻¹) * k' * (a * (y : G)⁻¹ * a⁻¹) * k'⁻¹ := by group
          _ = (y : G) * k' * (y : G)⁻¹ * k'⁻¹ := by rw [e1, e2]
      rw [e] at h2
      exact h2
    exact mem_pCoreOf_of_commutators_mem_pair S hB hcomps (hAH hyA) hcommK hcommKp
  have hpos : 0 < Nat.card Φ.range := Nat.card_pos
  have h1 : A₂.relIndex A₀ ≤ 4 := by
    have : A₂.relIndex A₀ = Nat.card Φ.range := by
      unfold Subgroup.relIndex
      rw [hA₂, map_subtype_subgroupOf', Subgroup.index_ker]
    rw [this]
    simpa using hcard4
  have h2 : A₀.relIndex A ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
  have h3 : A₂.relIndex A = A₂.relIndex A₀ * A₀.relIndex A :=
    (Subgroup.relIndex_mul_relIndex A₂ A₀ A hA₂A₀ hA₀A).symm
  have h4 : (A ⊓ pCoreOf 2 (mcOf T)).relIndex A ∣ A₂.relIndex A :=
    Subgroup.relIndex_dvd_of_le_left A hA₂Q
  have h5 : A₂.relIndex A ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h6 := Nat.le_of_dvd (Nat.pos_of_ne_zero h5) h4
  calc (A ⊓ pCoreOf 2 (mcOf T)).relIndex A ≤ A₂.relIndex A := h6
    _ = A₂.relIndex A₀ * A₀.relIndex A := h3
    _ ≤ 4 * 2 := Nat.mul_le_mul h1 h2
    _ = 8 := by norm_num

theorem two_mul_relIndex_le (S : Setting146 G T M) (c23 : Conc14623 T M) {K Kp A : Subgroup G}
    (hK : K ∈ cComp (mcOf T)) (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (hAH : A ≤ mcOf T) (hAab : IsElemAbelian 2 A)
    {a : G} (haA : a ∈ A) (hswa : conjSub a K = Kp)
    (hnd : ¬ (A ⊓ pCoreOf 2 (mcOf T)).relIndex A ∣ 2) :
    2 * (centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a)).relIndex (uOfL22 T M) ≤
      (centralizerMod Zz (uOfL22 T M) A).relIndex (uOfL22 T M) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hUN : uOfL22 T M ≤ Subgroup.normalizer (Zz : Set G) := S.conjClosure_le_normalizer_Z hG
  have hZU : Zz ≤ uOfL22 T M := Z_le_conjClosure_VZ T M (mcOf T)
  have haH : a ∈ mcOf T := hAH haA
  have haZ : a ∈ Subgroup.normalizer (Zz : Set G) := S.normalizer_Z.ge haH
  have haU : a ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ haH
  have hUc : ∀ {x y : G}, x ∈ uOfL22 T M → y ∈ uOfL22 T M → x * y = y * x := fun hx hy =>
    S.comm_of_mem_conjClosure hx hy
  set Uk : Subgroup G := ⁅uOfL22 T M, K⁆ ⊔ Zz with hUk
  set Ukp : Subgroup G := ⁅uOfL22 T M, Kp⁆ ⊔ Zz with hUkp
  have hkU : Uk ≤ uOfL22 T M := sup_le (commutator_le_U T M (le_of_mem_cComp hK)) hZU
  have hdir : Uk ⊓ Ukp ≤ Zz := inf_commutator_le_of_ne S c23 hK hKp hne
  have hconj : conjSub a Uk = Ukp := by
    rw [hUk, conjSub_commutator_sup S haH, hswa]
  have ha2 : a * a = 1 := by simpa [pow_two] using hAab.2 a haA
  have hb : ∃ b ∈ A, b ∈ Subgroup.normalizer (K : Set G) ∧ b ∉ pCoreOf 2 (mcOf T) := by
    have hnd' := hnd
    rw [Subgroup.relIndex_dvd_two_iff] at hnd'
    push Not at hnd'
    obtain ⟨b, hbA, hb1, hb2⟩ := hnd' a haA
    by_cases hbn : b ∈ Subgroup.normalizer (K : Set G)
    · exact ⟨b, hbA, hbn, fun h => hb2 ⟨hbA, h⟩⟩
    · refine ⟨b * a, A.mul_mem hbA haA, ?_, fun h => hb1 ⟨A.mul_mem hbA haA, h⟩⟩
      obtain ⟨-, h2⟩ := swap_of_not_mem_normalizer hK hKp hne hcomps (hAH hbA) hbn
      apply mem_normalizer_of_conjSub_eq
      rw [conjSub_mul, hswa, h2]
  obtain ⟨b, hbA, hbK, hbQ⟩ := hb
  have hbH : b ∈ mcOf T := hAH hbA
  have hbU : b ∈ Subgroup.normalizer (uOfL22 T M : Set G) := le_normalizer_conjClosure _ _ hbH
  have hbZ : b ∈ Subgroup.normalizer (Zz : Set G) := S.normalizer_Z.ge hbH
  have hba : b * a = a * b := isElemAbelian_comm hAab hbA haA
  obtain ⟨x, hxUk, hbx⟩ : ∃ x ∈ Uk, b * x * b⁻¹ * x⁻¹ ∉ Zz := by
    by_contra hcon
    push Not at hcon
    apply hbQ
    refine mem_pCoreOf_of_acts_trivially S c23 hcomps hbH hcon fun y hy => ?_
    have hy' : y ∈ conjSub a Uk := by rw [hconj]; exact hy
    have hk : a⁻¹ * y * a ∈ Uk := mem_conjSub.mp hy'
    have h1 := hcon _ hk
    have h2 := (Subgroup.mem_normalizer_iff.mp haZ _).mp h1
    have e : a * (b * (a⁻¹ * y * a) * b⁻¹ * (a⁻¹ * y * a)⁻¹) * a⁻¹ = b * y * b⁻¹ * y⁻¹ := by
      calc a * (b * (a⁻¹ * y * a) * b⁻¹ * (a⁻¹ * y * a)⁻¹) * a⁻¹
          = (a * b * a⁻¹) * y * (a * b⁻¹ * a⁻¹) * y⁻¹ := by group
        _ = b * y * b⁻¹ * y⁻¹ := by
          have e1 : a * b * a⁻¹ = b := by rw [← hba]; group
          have e2 : a * b⁻¹ * a⁻¹ = b⁻¹ := by
            have : b⁻¹ * a = a * b⁻¹ := (Commute.inv_left (hba : Commute b a)).eq
            rw [← this]; group
          rw [e1, e2]
    rw [e] at h2
    exact h2
  have hxU : x ∈ uOfL22 T M := hkU hxUk
  have haxU : a * x * a⁻¹ ∈ uOfL22 T M := (Subgroup.mem_normalizer_iff.mp haU x).mp hxU
  set w : G := x * (a * x * a⁻¹) with hw
  have hwU : w ∈ uOfL22 T M := (uOfL22 T M).mul_mem hxU haxU
  set Ca : Subgroup G := centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a) with hCa
  set Cb : Subgroup G := centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers b) with hCb
  have hwCa : w ∈ Ca := by
    refine mem_centralizerMod_zpowers hwU (hUN hwU) (fun z hz => S146T.comm_Z haH hz) ?_
    have : a * w * a⁻¹ = w := by
      calc a * w * a⁻¹ = (a * x * a⁻¹) * (a * a * x * (a * a)⁻¹) := by
            rw [hw]; group
        _ = (a * x * a⁻¹) * x := by rw [ha2]; group
        _ = w := hUc haxU hxU
    have e : w * a * w⁻¹ * a⁻¹ = 1 := by
      have : w * a = a * w := by
        calc w * a = (a * w * a⁻¹) * a := by rw [this]
          _ = a * w := by group
      rw [this]; group
    rw [e]
    exact Subgroup.one_mem _
  have hwCb : w ∉ Cb := by
    intro hwb
    have hc := hwb.2.2 b (Subgroup.mem_zpowers b)
    set c : G := b * x * b⁻¹ * x⁻¹ with hc_def
    have hbxUk : b * x * b⁻¹ ∈ Uk := by
      have hcb : conjSub b Uk = Uk := by
        rw [hUk, conjSub_sup, ← conjSub_commutator, conjSub_eq_of_mem_normalizer hbU,
          conjSub_eq_of_mem_normalizer hbK, conjSub_eq_of_mem_normalizer hbZ]
      have h1 : b * x * b⁻¹ ∈ conjSub b Uk := mul_mem_conjSub hxUk
      rwa [hcb] at h1
    have hcUk : c ∈ Uk := Uk.mul_mem hbxUk (Uk.inv_mem hxUk)
    have hcU : c ∈ uOfL22 T M := hkU hcUk
    have hacUkp : a * c * a⁻¹ ∈ Ukp := by
      have := mul_mem_conjSub (g := a) hcUk
      rwa [hconj] at this
    have hbw : b * w * b⁻¹ * w⁻¹ = c * (a * c * a⁻¹) := by
      have hbU' : b * x * b⁻¹ ∈ uOfL22 T M := (Subgroup.mem_normalizer_iff.mp hbU x).mp hxU
      have hx'a : a * (b * x * b⁻¹) * a⁻¹ ∈ uOfL22 T M :=
        (Subgroup.mem_normalizer_iff.mp haU _).mp hbU'
      have e1 : b * (a * x * a⁻¹) * b⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by
        have e2 : a⁻¹ * b⁻¹ = b⁻¹ * a⁻¹ := by
          rw [← mul_inv_rev, ← mul_inv_rev, hba]
        calc b * (a * x * a⁻¹) * b⁻¹ = (b * a) * x * (a⁻¹ * b⁻¹) := by group
          _ = (a * b) * x * (b⁻¹ * a⁻¹) := by rw [hba, e2]
          _ = a * (b * x * b⁻¹) * a⁻¹ := by group
      have hyinv : (a * x * a⁻¹)⁻¹ ∈ uOfL22 T M := (uOfL22 T M).inv_mem haxU
      have hcomm1 : (a * (b * x * b⁻¹) * a⁻¹ * (a * x * a⁻¹)⁻¹) * x⁻¹ =
          x⁻¹ * (a * (b * x * b⁻¹) * a⁻¹ * (a * x * a⁻¹)⁻¹) :=
        hUc ((uOfL22 T M).mul_mem hx'a hyinv) ((uOfL22 T M).inv_mem hxU)
      calc b * w * b⁻¹ * w⁻¹
          = (b * x * b⁻¹) * (b * (a * x * a⁻¹) * b⁻¹) * (a * x * a⁻¹)⁻¹ * x⁻¹ := by
            rw [hw]; group
        _ = (b * x * b⁻¹) * (a * (b * x * b⁻¹) * a⁻¹) * (a * x * a⁻¹)⁻¹ * x⁻¹ := by rw [e1]
        _ = (b * x * b⁻¹) * ((a * (b * x * b⁻¹) * a⁻¹ * (a * x * a⁻¹)⁻¹) * x⁻¹) := by group
        _ = (b * x * b⁻¹) * (x⁻¹ * (a * (b * x * b⁻¹) * a⁻¹ * (a * x * a⁻¹)⁻¹)) := by rw [hcomm1]
        _ = c * (a * c * a⁻¹) := by rw [hc_def]; group
    have hbw' : b * w * b⁻¹ * w⁻¹ ∈ Zz := by
      have e : b * w * b⁻¹ * w⁻¹ = (w * b * w⁻¹ * b⁻¹)⁻¹ := by group
      rw [e]
      exact Subgroup.inv_mem _ hc
    rw [hbw] at hbw'
    have hcUkp : c ∈ Ukp := by
      have e : c = (c * (a * c * a⁻¹)) * (a * c * a⁻¹)⁻¹ := by group
      rw [e]
      exact Ukp.mul_mem ((le_sup_right : Zz ≤ Ukp) hbw') (Ukp.inv_mem hacUkp)
    exact hbx (hdir ⟨hcUk, hcUkp⟩)
  have hCAle : centralizerMod Zz (uOfL22 T M) A ≤ Ca ⊓ Cb :=
    le_inf (centralizerMod_anti_right (uOfL22 T M) (Subgroup.zpowers_le.mpr haA))
      (centralizerMod_anti_right (uOfL22 T M) (Subgroup.zpowers_le.mpr hbA))
  have hlt : Ca ⊓ Cb ≠ Ca := fun h => hwCb (((h.symm.le) hwCa).2)
  have h2 : (Ca ⊓ Cb).relIndex Ca ≠ 1 := fun h => hlt (le_antisymm inf_le_left
    (Subgroup.relIndex_eq_one.mp h))
  have h2' : (Ca ⊓ Cb).relIndex Ca ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hCaU : Ca ≤ uOfL22 T M := fun y hy => hy.1
  have h3 : (Ca ⊓ Cb).relIndex Ca * Ca.relIndex (uOfL22 T M) = (Ca ⊓ Cb).relIndex (uOfL22 T M) :=
    Subgroup.relIndex_mul_relIndex _ _ _ inf_le_left hCaU
  have h4 : (Ca ⊓ Cb).relIndex (uOfL22 T M) ∣
      (centralizerMod Zz (uOfL22 T M) A).relIndex (uOfL22 T M) :=
    Subgroup.relIndex_dvd_of_le_left (uOfL22 T M) hCAle
  have h5 : (centralizerMod Zz (uOfL22 T M) A).relIndex (uOfL22 T M) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have h6 := Nat.le_of_dvd (Nat.pos_of_ne_zero h5) h4
  have h7 : 2 ≤ (Ca ⊓ Cb).relIndex Ca := by omega
  calc 2 * Ca.relIndex (uOfL22 T M) ≤ (Ca ⊓ Cb).relIndex Ca * Ca.relIndex (uOfL22 T M) :=
        Nat.mul_le_mul_right _ h7
    _ = (Ca ⊓ Cb).relIndex (uOfL22 T M) := h3
    _ ≤ _ := h6

theorem false_of_swap (S : Setting146 G T M) (hB : HypB146 T M) (c23 : Conc14623 T M)
    {K Kp A : Subgroup G} (hK : K ∈ cComp (mcOf T)) (hKp : Kp ∈ cComp (mcOf T)) (hne : Kp ≠ K)
    (hcomps : ∀ L ∈ cComp (mcOf T), L = K ∨ L = Kp) (hL3 : KbarIsL3Two K)
    (hrank : mIdx (⁅uOfL22 T M, K⁆ ⊔ Zz) Zz = 6) (hAH : A ≤ mcOf T) (hAab : IsElemAbelian 2 A)
    (hoff : (centralizerMod Zz (uOfL22 T M) A).relIndex (uOfL22 T M) ≤
      ((A ⊓ pCoreOf 2 (mcOf T)).relIndex A) ^ 2)
    {a : G} (haA : a ∈ A) (hanK : a ∉ Subgroup.normalizer (K : Set G)) : False := by
  classical
  have haH : a ∈ mcOf T := hAH haA
  have hswa : conjSub a K = Kp :=
    (swap_of_not_mem_normalizer hK hKp hne hcomps haH hanK).1
  have h64 := sixtyfour_le_relIndex S c23 hK hKp hne hrank haH hswa
  have h8 := relIndex_inf_pCoreOf_le_eight S hB hK hKp hne hcomps hL3 hAH hAab haA hswa
  have hCAle : centralizerMod Zz (uOfL22 T M) A ≤
      centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a) :=
    centralizerMod_anti_right (uOfL22 T M) (Subgroup.zpowers_le.mpr haA)
  have hdvd : (centralizerMod Zz (uOfL22 T M) (Subgroup.zpowers a)).relIndex (uOfL22 T M) ∣
      (centralizerMod Zz (uOfL22 T M) A).relIndex (uOfL22 T M) :=
    Subgroup.relIndex_dvd_of_le_left (uOfL22 T M) hCAle
  have hne0 : (centralizerMod Zz (uOfL22 T M) A).relIndex (uOfL22 T M) ≠ 0 := by
    unfold Subgroup.relIndex
    exact Subgroup.index_ne_zero_of_finite
  have hle := Nat.le_of_dvd (Nat.pos_of_ne_zero hne0) hdvd
  set n := (A ⊓ pCoreOf 2 (mcOf T)).relIndex A with hn
  have hsq : n ^ 2 ≤ 64 := by nlinarith
  have hn8 : n = 8 := by
    have : 64 ≤ n ^ 2 := by omega
    nlinarith
  have hnd : ¬ n ∣ 2 := by
    rw [hn8]
    decide
  have hF := two_mul_relIndex_le S c23 hK hKp hne hcomps hAH hAab haA hswa hnd
  omega

theorem le_commutator_sup_of_not_le {K A : Subgroup G} (hK : K ∈ cComp (mcOf T))
    (hsimple : IsSimpleGroup (KBar K)) (hAN : A ≤ Subgroup.normalizer (K : Set G))
    (hnle : ¬ ⁅K, A⁆ ≤ pCoreOf 2 (mcOf T)) : K ≤ ⁅K, A⁆ ⊔ pCoreOf 2 (mcOf T) := by
  classical
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) :=
    A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK)
  set X : Subgroup G := ⁅K, A⁆ with hX
  have hXK : X ≤ K := by
    rw [hX, Subgroup.commutator_le]
    intro k hk x hx
    have h1 : x * k⁻¹ * x⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hAN hx) _).mp (K.inv_mem hk)
    have e : ⁅k, x⁆ = k * (x * k⁻¹ * x⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact K.mul_mem hk h1
  have hKX : K ≤ Subgroup.normalizer (X : Set G) := Subgroup.normalizer_commutator_ge_left K A
  have hYn : (X.subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKX
  have hbarn : (((X.subgroupOf K)).map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))).Normal :=
    Subgroup.Normal.map hYn _ (QuotientGroup.mk'_surjective _)
  have := hsimple
  have := hbarn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((X.subgroupOf K).map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K))) with h | h
  · exfalso
    apply hnle
    intro y hy
    have hyK : y ∈ K := hXK hy
    have h1 : (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) ⟨y, hyK⟩ ∈
        (X.subgroupOf K).map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) :=
      Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr hy)
    rw [h, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact hQK (Subgroup.mem_subgroupOf.mp h1)
  · intro k hk
    have h1 : (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) ⟨k, hk⟩ ∈
        (X.subgroupOf K).map (QuotientGroup.mk' ((pCoreOf 2 K).subgroupOf K)) := by
      rw [h]; exact Subgroup.mem_top _
    obtain ⟨y, hy, hyk⟩ := Subgroup.mem_map.mp h1
    have h2 : (y : G)⁻¹ * k ∈ pCoreOf 2 K := by
      have := (QuotientGroup.eq (s := (pCoreOf 2 K).subgroupOf K)).mp hyk
      exact Subgroup.mem_subgroupOf.mp this
    have e : k = (y : G) * ((y : G)⁻¹ * k) := by group
    rw [e]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp hy) (hQK h2)

theorem input14624ThreeB_proof : Input14624ThreeB := by
  intro G _ _ T M S hB K U₁ U₂ s u γ γ' g hfull Kp hC
  classical
  obtain ⟨⟨c19, _c20, c23, hK, _c21, _c22, _hdec, _hch⟩, _hall, hgeom⟩ := hfull
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hF98 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2
  have hAH : F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ mcOf T := hF98.Uγ_le_H hgeom.1
  have hAab : IsElemAbelian 2 (F8.Uγ (VZ T M) (mcOf T) (g : G)) := hF98.isElemAbelian_Uγ
  have hle := hgeom.2.2.2.1
  have hpos : 0 < mIdx (F8.Uγ (VZ T M) (mcOf T) (g : G))
      (F8.Dγ (VZ T M) (quasithinOmegaOneCenter T) (mcOf T) (g : G)) :=
    lt_of_lt_of_le hgeom.2.2.1 hle
  have hQ := (hF98.F916_2_aux hgeom.1 hpos hle).1
  have hoff := hQ.2.2.2.2
  have hKQ : ¬ F8.Uγ (VZ T M) (mcOf T) (g : G) ≤ pCoreOf 2 (mcOf T) := hQ.2.2.1
  set A := F8.Uγ (VZ T M) (mcOf T) (g : G) with hA
  have hKp := hC.mem
  have hne := hC.ne
  have hcomps := hC.comps
  have hcomps' : ∀ L ∈ cComp (mcOf T), L = Kp ∨ L = K := fun L hL => (hcomps L hL).symm
  have hAN : A ≤ Subgroup.normalizer (K : Set G) := fun x hx => by
    by_contra hxn
    exact false_of_swap S hB c23 hK hKp hne hcomps hC.l3.1 hC.rank.1 hAH hAab hoff hx hxn
  have hAN' : A ≤ Subgroup.normalizer (Kp : Set G) := fun x hx => by
    by_contra hxn
    exact false_of_swap S hB c23 hKp hK hne.symm hcomps' hC.l3.2 hC.rank.2 hAH hAab hoff hx hxn
  refine ⟨hAN, hAN', ?_⟩
  obtain ⟨x, hxA, hxQ⟩ := Set.not_subset.mp hKQ
  by_cases hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (mcOf T)
  · right
    have hxKp : ¬ ∀ k ∈ Kp, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (mcOf T) := fun h =>
      hxQ (mem_pCoreOf_of_commutators_mem_pair S hB hcomps (hAH hxA) hxK h)
    push Not at hxKp
    obtain ⟨k, hk, hkQ⟩ := hxKp
    refine le_commutator_sup_of_not_le hKp ((c19 (mcOf T) hG).2 Kp hKp) hAN' fun hle' => hkQ ?_
    have h1 : ⁅k, x⁆ ∈ ⁅Kp, A⁆ := Subgroup.commutator_mem_commutator hk hxA
    have h2 := Subgroup.inv_mem _ (hle' h1)
    have e : ⁅k, x⁆⁻¹ = x * k * x⁻¹ * k⁻¹ := by rw [commutatorElement_def]; group
    rwa [e] at h2
  · left
    push Not at hxK
    obtain ⟨k, hk, hkQ⟩ := hxK
    refine le_commutator_sup_of_not_le hK ((c19 (mcOf T) hG).2 K hK) hAN fun hle' => hkQ ?_
    have h1 : ⁅k, x⁆ ∈ ⁅K, A⁆ := Subgroup.commutator_mem_commutator hk hxA
    have h2 := Subgroup.inv_mem _ (hle' h1)
    have e : ⁅k, x⁆⁻¹ = x * k * x⁻¹ * k⁻¹ := by rw [commutatorElement_def]; group
    rwa [e] at h2

end TB

end CFSG.Quasithin
