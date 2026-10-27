module

public import CFSG.Quasithin.EmptyFaithful.S151Statements
public import CFSG.Quasithin.EmptyFaithful.S14117Basic
public import CFSG.Quasithin.Background.D2Conj
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.D2Misc

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

theorem isTwoReducedIn_VZ {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) :
    IsTwoReducedIn M (VZ T M) ∧ VZ T M ≤ T := by
  obtain ⟨S, hS⟩ := h.exists_sylow
  have hSM : (S : Subgroup G) ≤ M := hS ▸ hM.2
  have hF : M ⊓ Subgroup.centralizer (pCoreOf 2 M : Set G) ≤ pCoreOf 2 M :=
    h.qtke.2.1 M hM.1.1 ⟨S, hSM⟩
  have hVred : IsTwoReducedIn M (VZ T M) := by
    have := isTwoReducedIn_conjClosure M S hSM hF le_rfl
    rwa [hS] at this
  refine ⟨hVred, ?_⟩
  have := le_sylow_of_isTwoReducedIn S hSM hVred
  rwa [hS] at this

theorem isElemAbelian_VZ {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : InM T M) :
    IsElemAbelian 2 (VZ T M) :=
  (isTwoReducedIn_VZ h hM).1.2.2.1

omit [Finite G] in
theorem le_normalizer_VZ (T M : Subgroup G) : M ≤ Subgroup.normalizer (VZ T M : Set G) :=
  le_normalizer_conjClosure _ M

omit [Finite G] in
theorem VZ_le_self {T M : Subgroup G} (hTM : T ≤ M) : VZ T M ≤ M :=
  conjClosure_le fun _ hx _ hz =>
    M.mul_mem (M.mul_mem hx (hTM (quasithinOmegaOneCenter_le_center T hz).1)) (M.inv_mem hx)

omit [Finite G] in
theorem thompsonJ_le_self151 (R : Subgroup G) : thompsonJ R ≤ R := iSup₂_le fun _ hA => hA.1

omit [Finite G] in
theorem mem_preOn {M V : Subgroup G} {L : Subgroup (MulAut V)} {x : G} :
    x ∈ preOn M V L ↔
      x ∈ M ∧ ∃ hx : x ∈ Subgroup.normalizer (V : Set G), conjAct V ⟨x, hx⟩ ∈ L := by
  unfold preOn
  simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_comap, Subgroup.coe_subtype]
  constructor
  · rintro ⟨hxM, ⟨y, hy, rfl⟩⟩
    exact ⟨hxM, y.2, hy⟩
  · rintro ⟨hxM, hx, hxL⟩
    exact ⟨hxM, ⟨⟨x, hx⟩, hxL, rfl⟩⟩

omit [Finite G] in
theorem preOn_le (M V : Subgroup G) (L : Subgroup (MulAut V)) : preOn M V L ≤ M := inf_le_left

omit [Finite G] in
theorem centralizer_le_preOn (M V : Subgroup G) (L : Subgroup (MulAut V)) :
    M ⊓ Subgroup.centralizer (V : Set G) ≤ preOn M V L := by
  intro x hx
  have hxN : x ∈ Subgroup.normalizer (V : Set G) := Subgroup.centralizer_le_normalizer _ hx.2
  refine mem_preOn.mpr ⟨hx.1, hxN, ?_⟩
  have : conjAct V ⟨x, hxN⟩ = 1 := A4.conjAct_eq_one_iff.mpr hx.2
  rw [this]
  exact L.one_mem

omit [Finite G] in
theorem autOn_preOn {M V : Subgroup G} {L : Subgroup (MulAut V)} (hL : L ≤ autOn M V) :
    autOn (preOn M V L) V = L := by
  apply le_antisymm
  · intro φ hφ
    obtain ⟨x, hx, hxK, rfl⟩ := mem_autOn_iff_exists.mp hφ
    obtain ⟨-, hxN', hxL⟩ := mem_preOn.mp hxK
    exact hxL
  · intro φ hφ
    obtain ⟨x, hx, hxM, rfl⟩ := mem_autOn_iff_exists.mp (hL hφ)
    exact mem_autOn_iff_exists.mpr ⟨x, hx, mem_preOn.mpr ⟨hxM, hx, hφ⟩, rfl⟩

theorem V154_eq_VZ {T Mc M : Subgroup G} (h : ¬ Case1512Six T Mc M) : V154 T Mc M = VZ T M := by
  unfold V154
  simp [h]

theorem V154_eq_uJ {T Mc M : Subgroup G} (h : Case1512Six T Mc M) : V154 T Mc M = uJ154 T M := by
  unfold V154
  simp [h]

theorem uJ154_le_VZ (T M : Subgroup G) : uJ154 T M ≤ VZ T M := by
  unfold uJ154
  rw [Subgroup.commutator_le]
  intro v hv m hm
  have hmN : m ∈ Subgroup.normalizer (VZ T M : Set G) :=
    le_normalizer_VZ T M (preOn_le _ _ _ hm)
  have h1 : m * v⁻¹ * m⁻¹ ∈ VZ T M :=
    (Subgroup.mem_normalizer_iff.mp hmN _).mp ((VZ T M).inv_mem hv)
  have : v * m * v⁻¹ * m⁻¹ = v * (m * v⁻¹ * m⁻¹) := by group
  show v * m * v⁻¹ * m⁻¹ ∈ VZ T M
  rw [this]
  exact (VZ T M).mul_mem hv h1

theorem V154_le_VZ (T Mc M : Subgroup G) : V154 T Mc M ≤ VZ T M := by
  by_cases h : Case1512Six T Mc M
  · rw [V154_eq_uJ h]
    exact uJ154_le_VZ T M
  · rw [V154_eq_VZ h]

theorem qhatOn_eq {M V : Subgroup G} (hV : IsElemAbelian 2 V) :
    qhatOn M V = qhatInt M V hV := by
  unfold qhatOn
  split_ifs
  rfl

theorem qOn_eq {M V : Subgroup G} (hV : IsElemAbelian 2 V) : qOn M V = qInt M V hV := by
  unfold qOn
  split_ifs
  rfl

theorem qhatInt_le_qInt' (M V : Subgroup G) (hV : IsElemAbelian 2 V) :
    qhatInt M V hV ≤ qInt M V hV :=
  @qhatOf_le_qOf ↥V (commGroupOfElemAbelian hV) inferInstance (autOn M V)

theorem qhatOn_le_qOn {M V : Subgroup G} (hV : IsElemAbelian 2 V) : qhatOn M V ≤ qOn M V := by
  rw [qhatOn_eq hV, qOn_eq hV]
  exact qhatInt_le_qInt' M V hV

theorem qhatInt_congr {M M' V : Subgroup G} (hV : IsElemAbelian 2 V) (h : autOn M V = autOn M' V) :
    qhatInt M V hV = qhatInt M' V hV := by
  unfold qhatInt
  rw [h]

theorem qInt_congr {M M' V : Subgroup G} (hV : IsElemAbelian 2 V) (h : autOn M V = autOn M' V) :
    qInt M V hV = qInt M' V hV := by
  unfold qInt
  rw [h]

omit [Finite G] in
theorem le_normalizer_inf_centralizer' {A K V : Subgroup G}
    (hK : A ≤ Subgroup.normalizer (K : Set G)) (hV : A ≤ Subgroup.normalizer (V : Set G)) :
    A ≤ Subgroup.normalizer ((K ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (hK ha) x
  have h2 := Subgroup.mem_normalizer_iff.mp (A4.mem_normalizer_centralizer (hV ha)) x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, h1, h2]


theorem not_exists_normal_of_isUniqueM {M M₀ H : Subgroup G} (huniq : IsUniqueM M₀ M)
    (hHM : ¬ H ≤ M) :
    ¬ ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
      M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) := by
  rintro ⟨R₀, hR₀, hR₀le, hR₀N⟩
  have hR₀p : IsPGroup 2 R₀ := (pCoreOf_isPGroup 2 M₀).to_le hR₀le
  obtain ⟨K, hK, hNK⟩ :=
    exists_maxTwoLocal_ge (L := Subgroup.normalizer (R₀ : Set G)) ⟨R₀, hR₀, hR₀p, rfl⟩
  have hKM : K = M := huniq.2 K ⟨hK, (le_sup_left.trans hR₀N).trans hNK⟩
  exact hHM ((le_sup_right.trans hR₀N).trans (hNK.trans hKM.le))

theorem JhatOn_eq {M V : Subgroup G} (hV : IsElemAbelian 2 V) :
    JhatOn M V = @Jhat ↥V (commGroupOfElemAbelian hV) inferInstance (autOn M V) := by
  unfold JhatOn
  split_ifs
  rfl

theorem mem_Jhat_conj {W : Type*} [CommGroup W] [Finite W] {X : Subgroup (MulAut W)}
    {g y : MulAut W} (hg : g ∈ X) (hy : y ∈ Jhat X) : g * y * g⁻¹ ∈ Jhat X := by
  have key : (Jhat X).map (MulAut.conj g).toMonoidHom ≤ Jhat X := by
    unfold Jhat
    rw [Subgroup.map_iSup]
    refine iSup_le fun A => ?_
    rw [Subgroup.map_iSup]
    refine iSup_le fun hA => ?_
    exact le_iSup₂_of_le (conjBy g A) (conjBy_mem_QhatStar hA hg) le_rfl
  exact key ⟨y, hy, rfl⟩

theorem JhatOn_normalized {M V : Subgroup G} {g y : MulAut V} (hg : g ∈ autOn M V)
    (hy : y ∈ JhatOn M V) : g * y * g⁻¹ ∈ JhatOn M V := by
  by_cases hV : IsElemAbelian 2 V
  · rw [JhatOn_eq hV] at hy ⊢
    exact @mem_Jhat_conj ↥V (commGroupOfElemAbelian hV) inferInstance (autOn M V) g y hg hy
  · have : JhatOn M V = ⊥ := by
      unfold JhatOn
      split_ifs
      rfl
    rw [this] at hy ⊢
    rw [Subgroup.mem_bot.mp hy]
    simp

omit [Finite G] in
theorem le_normalizer_preOn {M V : Subgroup G} {L : Subgroup (MulAut V)}
    (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hL : ∀ g ∈ autOn M V, ∀ y ∈ L, g * y * g⁻¹ ∈ L) :
    M ≤ Subgroup.normalizer (preOn M V L : Set G) := by
  have key : ∀ m ∈ M, ∀ x ∈ preOn M V L, m * x * m⁻¹ ∈ preOn M V L := by
    intro m hm x hx
    obtain ⟨hxM, hxN, hxL⟩ := mem_preOn.mp hx
    have hmN := hMV hm
    have hmxN : m * x * m⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
      (Subgroup.normalizer (V : Set G)).mul_mem
        ((Subgroup.normalizer (V : Set G)).mul_mem hmN hxN)
        ((Subgroup.normalizer (V : Set G)).inv_mem hmN)
    refine mem_preOn.mpr ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), hmxN, ?_⟩
    rw [conjAct_conj hmN hxN hmxN]
    exact hL _ (mem_autOn_iff_exists.mpr ⟨m, hmN, hm, rfl⟩) _ hxL
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => key m hm x hx, fun hx => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_mJ154 {T M : Subgroup G} (hMV : M ≤ Subgroup.normalizer (VZ T M : Set G)) :
    M ≤ Subgroup.normalizer (mJ154 T M : Set G) :=
  le_normalizer_preOn hMV fun _ hg _ hy => JhatOn_normalized hg hy

theorem le_normalizer_uJ154 (T M : Subgroup G) : M ≤ Subgroup.normalizer (uJ154 T M : Set G) := by
  intro m hm
  exact A4.mem_normalizer_commutator (le_normalizer_VZ T M hm)
    (le_normalizer_mJ154 (le_normalizer_VZ T M) hm)

theorem le_normalizer_V154 (T Mc M : Subgroup G) :
    M ≤ Subgroup.normalizer (V154 T Mc M : Set G) := by
  by_cases h : Case1512Six T Mc M
  · rw [V154_eq_uJ h]
    exact le_normalizer_uJ154 T M
  · rw [V154_eq_VZ h]
    exact le_normalizer_VZ T M

theorem V154_ne_bot {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) :
    V154 T Mc M ≠ ⊥ := by
  by_cases hc : Case1512Six T Mc M
  · rw [V154_eq_uJ hc]
    intro hb
    have := hc.2.2.2.1
    rw [hb, Subgroup.card_bot] at this
    norm_num at this
  · rw [V154_eq_VZ hc]
    exact VZ_ne_bot h.omegaOneCenter_ne_bot


theorem eq_oTwoUpper_sup_of_isSylowTwoOf {H T : Subgroup G} (hT : IsSylowTwoOf T H) :
    H = oTwoUpper H ⊔ T := by
  classical
  have hNH : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
  have hnorm : ((oTwoUpper H).subgroupOf H).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer hNH
  have hQ : IsPGroup 2 (↥H ⧸ (oTwoUpper H).subgroupOf H) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper H x.2
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    exact Subgroup.mem_subgroupOf.mpr hk
  set f : ↥H →* (↥H ⧸ (oTwoUpper H).subgroupOf H) := QuotientGroup.mk' _ with hf
  have hdvd := Subgroup.index_map_dvd (H := T.subgroupOf H) (f := f)
    (QuotientGroup.mk'_surjective _)
  obtain ⟨n, hn⟩ := hQ.index ((T.subgroupOf H).map f)
  have hodd : ¬ 2 ∣ (T.subgroupOf H).index := hT.2.2
  have h1 : ((T.subgroupOf H).map f).index = 1 := by
    rcases n with _ | n
    · simpa using hn
    · exfalso
      refine hodd ?_
      rw [hn] at hdvd
      exact (dvd_pow_self 2 (Nat.succ_ne_zero n)).trans hdvd
  rw [Subgroup.index_eq_one] at h1
  refine le_antisymm (fun x hx => ?_) (sup_le (oTwoUpper_le H) hT.1)
  have hmem : f ⟨x, hx⟩ ∈ (T.subgroupOf H).map f := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨t, ht, hteq⟩ := Subgroup.mem_map.mp hmem
  have h2 : (t : ↥H)⁻¹ * ⟨x, hx⟩ ∈ (oTwoUpper H).subgroupOf H := by
    rw [← QuotientGroup.eq]
    exact hteq
  have h3 : (t : G)⁻¹ * x ∈ oTwoUpper H := Subgroup.mem_subgroupOf.mp h2
  have h4 : x = (t : G) * ((t : G)⁻¹ * x) := by group
  have h5 : x ∈ T ⊔ oTwoUpper H := by
    rw [h4]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mp ht) h3
  rwa [sup_comm] at h5


omit [Finite G] in
theorem le_centralizer_of_commutator_eq_bot {A B : Subgroup G} (h : ⁅A, B⁆ = ⊥) :
    B ≤ Subgroup.centralizer (A : Set G) := by
  rw [Subgroup.commutator_comm] at h
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h

omit [Finite G] in
theorem commutator_eq_bot_of_le_centralizer {A B : Subgroup G}
    (h : B ≤ Subgroup.centralizer (A : Set G)) : ⁅A, B⁆ = ⊥ := by
  rw [Subgroup.commutator_comm]
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr h

theorem one_lt_pRank_of_card {T V : Subgroup G} (hV : IsElemAbelian 2 V) (hVT : V ≤ T)
    (hcard : 4 ≤ Nat.card V) : 1 < CFSG.Open.pRank 2 T := by
  have hp : IsPGroup 2 V := fun x => ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hp
  have hk2 : 2 ≤ k := by
    by_contra hlt
    have h1 : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact lt_of_lt_of_le (by omega) (le_pRank Nat.prime_two hVT hV hk)

theorem pRank_two_map_mulEquiv151 (φ : G ≃* G) (H : Subgroup G) :
    CFSG.Open.pRank 2 (H.map φ.toMonoidHom) = CFSG.Open.pRank 2 H := by
  unfold CFSG.Open.pRank
  have key : ∀ (ψ : G ≃* G) (K : Subgroup G) (k : ℕ),
      (∃ E : Subgroup G, E ≤ K ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k) →
      (∃ E : Subgroup G, E ≤ K.map ψ.toMonoidHom ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ k) := by
    rintro ψ K k ⟨E, hEK, hE, hk⟩
    exact ⟨E.map ψ.toMonoidHom, (map_le_map_mulEquiv_iff ψ).mpr hEK,
      (isElemAbelian_map_mulEquiv ψ).mpr hE, by rw [card_map_mulEquiv, hk]⟩
  congr 1
  ext k
  constructor
  · intro hk
    have := key φ.symm (H.map φ.toMonoidHom) k hk
    rwa [map_map_symm_mulEquiv] at this
  · exact key φ H k

theorem isElemAbelianCorank_map_mulEquiv151 (φ : G ≃* G) {H A : Subgroup G} {i : ℕ} :
    IsElemAbelianCorank (H.map φ.toMonoidHom) i (A.map φ.toMonoidHom) ↔
      IsElemAbelianCorank H i A := by
  unfold IsElemAbelianCorank
  rw [map_le_map_mulEquiv_iff, isElemAbelian_map_mulEquiv, card_map_mulEquiv,
    pRank_two_map_mulEquiv151]

theorem thompsonJi_map_mulEquiv151 (φ : G ≃* G) (H : Subgroup G) (i : ℕ) :
    (thompsonJi H i).map φ.toMonoidHom = thompsonJi (H.map φ.toMonoidHom) i := by
  unfold thompsonJi
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup₂_le fun A hA => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    exact le_iSup₂_of_le
      (f := fun (B : Subgroup G) (_ : IsElemAbelianCorank (H.map φ.toMonoidHom) i B) => B)
      (A.map φ.toMonoidHom) ((isElemAbelianCorank_map_mulEquiv151 φ).mpr hA) le_rfl
  · refine iSup₂_le fun B hB => ?_
    have hB' : IsElemAbelianCorank H i (B.map φ.symm.toMonoidHom) := by
      rw [← isElemAbelianCorank_map_mulEquiv151 φ, map_symm_map_mulEquiv]
      exact hB
    rw [← map_symm_map_mulEquiv φ B]
    exact Subgroup.map_mono (le_iSup₂_of_le
      (f := fun (A : Subgroup G) (_ : IsElemAbelianCorank H i A) => A) _ hB' le_rfl)

theorem normalizer_le_normalizer_thompsonJi151 (S : Subgroup G) (i : ℕ) :
    Subgroup.normalizer (S : Set G) ≤ Subgroup.normalizer (thompsonJi S i : Set G) :=
  normalizer_le_normalizer_of_map_mulEquiv (F := fun X => thompsonJi X i)
    (fun φ X => thompsonJi_map_mulEquiv151 φ X i) S

omit [Finite G] in
theorem isElemAbelian_mono151 {E F : Subgroup G} (hFE : F ≤ E) (hE : IsElemAbelian 2 E) :
    IsElemAbelian 2 F := CFSG.Open.IsElemAbelian.mono hE hFE

omit [Finite G] in
theorem isSylowTwoOf_of_le151 {T H : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) :
    IsSylowTwoOf T H :=
  ⟨hTH, hT.1, fun h => hT.2 (h.trans (by
    simpa [Subgroup.relIndex] using Subgroup.relIndex_dvd_index_of_le hTH))⟩

omit [Finite G] in
theorem le_normalizer_inf151 {S A B : Subgroup G}
    (hA : S ≤ Subgroup.normalizer (A : Set G)) (hB : S ≤ Subgroup.normalizer (B : Set G)) :
    S ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hA hg) x,
    Subgroup.mem_normalizer_iff.mp (hB hg) x]

theorem thompsonJi_one_ne_bot {T : Subgroup G} (hrank : 1 < CFSG.Open.pRank 2 T) :
    thompsonJi T 1 ≠ ⊥ := by
  obtain ⟨A, hA⟩ := exists_isMaxElemAbelian T
  have hc := (isMaxElemAbelian_iff_corank_zero.mp hA).2.2
  rw [pow_zero, mul_one] at hc
  have hAJ : A ≤ thompsonJ T := le_iSup₂_of_le A hA le_rfl
  have hJ : thompsonJ T ≤ thompsonJi T 1 := by
    rw [thompsonJ_eq_thompsonJi_zero]
    exact thompsonJi_mono (Nat.zero_le 1) hrank
  intro hb
  have hAb : A = ⊥ := le_bot_iff.mp ((hAJ.trans hJ).trans hb.le)
  rw [hAb, Subgroup.card_bot] at hc
  have h4 : 2 ^ 2 ≤ 2 ^ CFSG.Open.pRank 2 T := Nat.pow_le_pow_right (by norm_num) hrank
  omega

theorem commutator_inf_centralizer_eq_bot {V D : Subgroup G} (hV : IsElemAbelian 2 V)
    (hD : D ≤ Subgroup.normalizer (V : Set G)) (hodd : Odd (Nat.card (autOn D V))) :
    ⁅V, D⁆ ⊓ (V ⊓ Subgroup.centralizer (D : Set G)) = ⊥ := by
  let _inst : CommGroup ↥V := commGroupOfElemAbelian hV
  have hV2 : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (hV.2 v v.2)
  have hdec := (coprime_decomp (V := ↥V) (P := autOn D V) hodd hV2 (W := ⊤)
    (fun _ _ _ _ => Subgroup.mem_top _)).2
  have hcomm_le : ⁅V, D⁆ ≤ (commSub (⊤ : Subgroup ↥V) (autOn D V)).map V.subtype := by
    rw [Subgroup.commutator_le]
    intro v hv d hd
    have hdN := hD hd
    refine ⟨conjAct V ⟨d, hdN⟩ ⟨v⁻¹, V.inv_mem hv⟩ * (⟨v⁻¹, V.inv_mem hv⟩ : ↥V)⁻¹, ?_, ?_⟩
    · exact Subgroup.subset_closure ⟨conjAct V ⟨d, hdN⟩,
        mem_autOn_iff_exists.mpr ⟨d, hdN, hd, rfl⟩, ⟨v⁻¹, V.inv_mem hv⟩, Subgroup.mem_top _, rfl⟩
    · have hc := congrArg Subtype.val (mul_comm (⟨v, hv⟩ : ↥V)
        (conjAct V ⟨d, hdN⟩ ⟨v⁻¹, V.inv_mem hv⟩))
      have hc' : v * (d * v⁻¹ * d⁻¹) = d * v⁻¹ * d⁻¹ * v := hc
      show d * v⁻¹ * d⁻¹ * (v⁻¹)⁻¹ = v * d * v⁻¹ * d⁻¹
      rw [inv_inv, ← hc']
      group
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  obtain ⟨hzW, hzV, hzC⟩ := hz
  obtain ⟨x, hx, hxz⟩ := Subgroup.mem_map.mp (hcomm_le hzW)
  have hxz' : x = ⟨z, hzV⟩ := Subtype.ext hxz
  have h2 : (⟨z, hzV⟩ : ↥V) ∈ (⊤ : Subgroup ↥V) ⊓ fixV (autOn D V) := by
    refine ⟨Subgroup.mem_top _, fun y hy => ?_⟩
    obtain ⟨d, hdN, hdD, rfl⟩ := mem_autOn_iff_exists.mp hy
    refine Subtype.ext ?_
    show d * z * d⁻¹ = z
    rw [Subgroup.mem_centralizer_iff.mp hzC d hdD]
    group
  have h3 : (⟨z, hzV⟩ : ↥V) ∈ commSub (⊤ : Subgroup ↥V) (autOn D V) ⊓
      ((⊤ : Subgroup ↥V) ⊓ fixV (autOn D V)) := ⟨hxz' ▸ hx, h2⟩
  rw [hdec, Subgroup.mem_bot] at h3
  exact congrArg Subtype.val h3

theorem sixteen_le_card_V154 {T Mc M : Subgroup G} (h157 : Lemma1517Concl T Mc M) :
    16 ≤ Nat.card (V154 T Mc M) := by
  obtain ⟨hcases, -⟩ := h157
  rcases hcases with h | h | h | h | h | ⟨p, -, h⟩ | h
  · rw [h.1]
  · rw [h.1]
  · rw [h.1]
  · rw [h.1]
  · rw [h.1]
  · rw [h.1]
    norm_num
  · rw [h.1]
    norm_num

theorem one_lt_pRank_T {T Mc M : Subgroup G} (h : quasithinQTFE14Cat G T Mc) (hM : IsMf T Mc M)
    (h157 : Lemma1517Concl T Mc M) : 1 < CFSG.Open.pRank 2 T := by
  have hMT : InM T M := hM.1.1
  exact one_lt_pRank_of_card
    (isElemAbelian_mono151 (V154_le_VZ T Mc M) (isElemAbelian_VZ h hMT))
    ((V154_le_VZ T Mc M).trans (isTwoReducedIn_VZ h hMT).2)
    (by have := sixteen_le_card_V154 h157; omega)

theorem exists_isHStar {T M M' : Subgroup G} (hM' : InM T M') (hM : InM T M) (hne : M' ≠ M) :
    ∃ H : Subgroup G, IsHStar T M H := by
  classical
  have hM'M : ¬ M' ≤ M := fun hle => hne (hM'.1.2 M hM.1.1 hle).symm
  have hM'H : InH T M' := inH_of_inM hM'
  obtain ⟨H, ⟨hHH, hHM, hHM'⟩, hmin⟩ := Set.exists_min_image
    {K : Subgroup G | InH T K ∧ ¬ K ≤ M ∧ K ≤ M'} (fun K => Nat.card K) (Set.toFinite _)
    ⟨M', hM'H, hM'M, le_rfl⟩
  refine ⟨H, hHH, hHM, fun Y hY hYH hYM => ?_⟩
  exact Subgroup.eq_of_le_of_card_ge hYH (hmin Y ⟨hY, hYM, hYH.trans hHM'⟩)

end CFSG.Quasithin
