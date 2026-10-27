module

public import CFSG.Quasithin.Background.RonanF918Five
public import CFSG.Quasithin.Background.RonanF918FourCases

public section

namespace CFSG.Quasithin.RonanF918

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open CFSG.Assembly.LowTwoRank CFSG.Blueprint
open scoped Pointwise commutatorElement Matrix

section Iii

attribute [local instance] CFSG.Quasithin.commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem tildeOf_commutator' {V₁ U X : Subgroup G} (hU : U ≤ Subgroup.normalizer (V₁ : Set G))
    (hX : X ≤ Subgroup.normalizer (V₁ : Set G)) :
    tildeOf V₁ ⁅U, X⁆ = ⁅tildeOf V₁ U, tildeOf V₁ X⁆ := by
  have hc : ⁅U, X⁆.subgroupOf (Subgroup.normalizer (V₁ : Set G)) =
      ⁅U.subgroupOf (Subgroup.normalizer (V₁ : Set G)),
        X.subgroupOf (Subgroup.normalizer (V₁ : Set G))⁆ := by
    apply Subgroup.map_injective (Subgroup.normalizer (V₁ : Set G)).subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hU,
      Subgroup.map_subgroupOf_eq_of_le hX,
      Subgroup.map_subgroupOf_eq_of_le (Subgroup.commutator_le.2 fun u hu k hk =>
        Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hU hu) (hX hk))
          (Subgroup.inv_mem _ (hU hu))) (Subgroup.inv_mem _ (hX hk)))]
  unfold tildeOf secImg
  rw [hc, Subgroup.map_commutator]

variable [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))]

theorem map_commV_autIH (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H) {X : Subgroup G}
    (hXH : X ≤ H) :
    (commV (autIH V₁ I H X)).map (tildeOf V₁ (conjClosure I H)).subtype =
      tildeOf V₁ ⁅conjClosure I H, X⁆ := by
  haveI : IsMulCommutative ↥(tildeOf V₁ (conjClosure I H)) := (Fact.out :
    IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))).1
  have hXV : tildeOf V₁ X ≤ Subgroup.normalizer
      ((tildeOf V₁ (conjClosure I H) : Subgroup (GtOf V₁)) : Set (GtOf V₁)) :=
    secImg_le_normalizer_secImg (hXH.trans (le_normalizer_conjClosure I H))
  rw [AutOn.map_commV_autOn_eq hXV, tildeOf_commutator' (h.conjClosure_le_normalizer_V₁ hIU)
    (hXH.trans h.H_le_normalizer_V₁)]

theorem commV_autIH_eq_subM (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {X : Subgroup G} (hXH : X ≤ H) :
    commV (autIH V₁ I H X) = subM V₁ (conjClosure I H) ⁅conjClosure I H, X⁆ := by
  apply Subgroup.map_injective (tildeOf V₁ (conjClosure I H)).subtype_injective
  rw [map_commV_autIH h hIU hXH]
  have hle : tildeOf V₁ ⁅conjClosure I H, X⁆ ≤ tildeOf V₁ (conjClosure I H) := by
    refine secImg_mono ?_
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hXH.trans (le_normalizer_conjClosure I H))
  exact (Subgroup.map_subgroupOf_eq_of_le hle).symm

theorem map_subtype_subM {J : Subgroup G}
    (hle : tildeOf V₁ J ≤ tildeOf V₁ (conjClosure I H)) :
    (subM V₁ (conjClosure I H) J).map (tildeOf V₁ (conjClosure I H)).subtype = tildeOf V₁ J :=
  Subgroup.map_subgroupOf_eq_of_le hle

theorem fixV_autIH_eq (hIU : I ≤ conjClosure Vp H) {Y : Subgroup G} (hYH : Y ≤ H) :
    fixV (autIH V₁ I H Y) =
      (Subgroup.centralizer (tildeOf V₁ Y : Set (GtOf V₁))).subgroupOf (tildeOf V₁ (conjClosure I H)) := by
  haveI : IsMulCommutative ↥(tildeOf V₁ (conjClosure I H)) := (Fact.out :
    IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))).1
  exact AutOn.fixV_autOn_eq (secImg_le_normalizer_secImg (hYH.trans (le_normalizer_conjClosure I H)))

theorem map_actH_subM_of_le (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {J : Subgroup G} (x : ↥H) :
    (subM V₁ (conjClosure I H) J).map
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x).toMonoidHom =
      subM V₁ (conjClosure I H) (conjSub (x : G) J) := by
  have hxN : (x : G) ∈ Subgroup.normalizer (V₁ : Set G) := h.H_le_normalizer_V₁ x.2
  have h1 : tildeOf V₁ (conjSub (x : G) J) =
      (tildeOf V₁ J).map (MulAut.conj (secMk (Subgroup.normalizer (V₁ : Set G)) V₁
        ⟨x, hxN⟩)).toMonoidHom :=
    CFSG.Quasithin.RonanF918.secImg_conjSub (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨x, hxN⟩ J
  ext w
  rw [Subgroup.mem_map_equiv, mem_subM_iff, mem_subM_iff, h1, Subgroup.mem_map_equiv]
  have hsymm : ((actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x).symm w :
      ↥(tildeOf V₁ (conjClosure I H))) =
      actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) x⁻¹ w := by
    rw [map_inv]
    rfl
  have hsec : ∀ hy : ((x⁻¹ : ↥H) : G) ∈ Subgroup.normalizer (V₁ : Set G),
      secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨((x⁻¹ : ↥H) : G), hy⟩ =
        (secMk (Subgroup.normalizer (V₁ : Set G)) V₁ ⟨(x : G), hxN⟩)⁻¹ := fun hy => by
    rw [← map_inv]
    rfl
  rw [hsymm, actH_apply_coe, hsec, MulAut.conj_symm_apply, inv_inv]

theorem conjAutSub_autIH (h : HypF918 T V L V₁ Vp H K) {X : Subgroup G} (hXH : X ≤ H) {t : G}
    (htH : t ∈ H) :
    conjAutSub (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t, htH⟩)
        (autIH V₁ I H X) = autIH V₁ I H (conjSub t X) := by
  have hXtH : conjSub t X ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem htH (hXH hx)) (H.inv_mem htH)
  rw [autIH_eq_map h hXH, autIH_eq_map h hXtH]
  exact conjAutSub_map_subgroupOf (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) htH

theorem hatDSumU_of_isSumMod_commutator (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {t : G} (htH : t ∈ H)
    (hsum : IsSumMod (fixV (autIH V₁ I H (conjClosure K T))) (commV (autIH V₁ I H K))
      ((commV (autIH V₁ I H K)).map
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, H.inv_mem htH⟩).toMonoidHom) ⊤) :
    HatDSumU V₁ Vp H K T (conjClosure I H) ⁅conjClosure I H, K⁆ t := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hJle : ⁅conjClosure I H, K⁆ ≤ conjClosure I H := by
    rw [Subgroup.commutator_comm]
    exact Subgroup.le_normalizer_iff_commutator_le_right.mp (hKH.trans (le_normalizer_conjClosure I H))
  have hQ : conjSub t⁻¹ ⁅conjClosure I H, K⁆ ≤ conjClosure I H := by
    intro y hy
    have h1 := hJle (mem_conjSub.mp hy)
    refine (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure I H htH) y).mpr ?_
    simpa using h1
  rw [commV_autIH_eq_subM h hIU hKH, map_actH_subM_of_le h hIU] at hsum
  have key := map_sup_inf_of_isSumMod (thetaMap h hIU)
    (C := fixV (autIH V₁ I H (conjClosure K T)))
    (fun w => ⟨mem_fixV_of_thetaMap_eq_one h hIU, thetaMap_eq_one_of_mem_fixV h hIU⟩)
    hsum.1 hsum.2
  refine ⟨?_, ?_⟩
  · rw [hat_eq_map_theta h hIU le_rfl, hat_eq_map_theta h hIU hJle, hat_eq_map_theta h hIU hQ,
      subM_self]
    exact key.1
  · rw [hat_eq_map_theta h hIU hJle, hat_eq_map_theta h hIU hQ]
    exact key.2

theorem tilde_commutator_le_centralizer (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    {t : G} (htH : t ∈ H)
    (hcen : commV (autIH V₁ I H K) ≤
      fixV (conjAutSub
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨t⁻¹, H.inv_mem htH⟩)
        (autIH V₁ I H K))) :
    tildeOf V₁ ⁅conjClosure I H, K⁆ ≤ tildeOf V₁ (conjClosure I H) ⊓
      Subgroup.centralizer (tildeOf V₁ (conjSub t⁻¹ K) : Set (GtOf V₁)) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKtH : conjSub t⁻¹ K ≤ H := by
    rintro _ ⟨x, hx, rfl⟩
    exact H.mul_mem (H.mul_mem (H.inv_mem htH) (hKH hx)) (H.inv_mem (H.inv_mem htH))
  rw [conjAutSub_autIH h hKH (H.inv_mem htH), fixV_autIH_eq hIU hKtH] at hcen
  intro y hy
  rw [← map_commV_autIH h hIU hKH] at hy
  obtain ⟨w, hw, rfl⟩ := hy
  exact ⟨w.2, Subgroup.mem_subgroupOf.mp (hcen hw)⟩

theorem mem_hat_iff (h : HypF918 T V L V₁ Vp H K) {X : Subgroup G} (hXH : X ≤ H)
    {y : GhOf V₁ (conjClosure Vp H) (conjClosure K T)} :
    y ∈ hat' V₁ Vp H K T X ↔ ∃ (k : G) (hk : k ∈ X), y = kbarOf h (hXH hk) := by
  constructor
  · intro hy
    obtain ⟨z, hz, rfl⟩ := mem_secImg.mp hy
    obtain ⟨w, hw, hwz⟩ := mem_secImg.mp hz
    refine ⟨(w : G), hw, ?_⟩
    unfold kbarOf
    congr 1
    exact Subtype.ext hwz.symm
  · rintro ⟨k, hk, rfl⟩
    exact kbarOf_mem_hat_of_mem h hXH hk

theorem modelOnU_of_realizes_le (h : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G)) {X : Subgroup G}
    (hXK : X ≤ conjClosure K T)
    (hAV : autIH V₁ I H (conjClosure K T) ≤ stabSub (subM V₁ (conjClosure I H) I)) {D : FFModel}
    (hD : D.Realizes (autIH V₁ I H X) (subM V₁ (conjClosure I H) I)
      (subM V₁ (conjClosure I H) I ⊓ fixV (autIH V₁ I H (conjClosure K T)))) :
    ModelOnU D (hat' V₁ Vp H K T X) (hat' V₁ Vp H K T I) := by
  have hXH : X ≤ H := hXK.trans h.K₀_le_H
  have hXI : X ≤ Subgroup.normalizer (I : Set G) := hXK.trans hKI
  have hel : IsElemAbelian 2 (hat' V₁ Vp H K T I) :=
    isElemAbelian_secImg (h.isElemAbelian_tilde_of_le hIU)
  refine ⟨hatOf_le_normalizer hXI, hel, ?_⟩
  obtain ⟨π, hπ⟩ := hD
  letI : CommGroup ↥(hat' V₁ Vp H K T I) := commGroupOfElemAbelian hel
  have hle : autIH V₁ I H X ≤ autIH V₁ I H (conjClosure K T) :=
    CFSG.Quasithin.AutOn.autOn_mono (secImg_mono hXK)
  let τ0 : ↥(autIH V₁ I H X) →* MulAut ↥(hat' V₁ Vp H K T I) :=
    (tauHat h hIU hAV).comp (Subgroup.inclusion hle)
  have hτmem : ∀ x : ↥(autIH V₁ I H X), τ0 x ∈
      autOn (hat' V₁ Vp H K T X) (hat' V₁ Vp H K T I) := by
    intro x
    have hx : (x : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈
        (X.subgroupOf H).map (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
      rw [← autIH_eq_map h hXH]
      exact x.2
    obtain ⟨⟨y, hyH⟩, hy, hyx⟩ := hx
    have hyX : y ∈ X := Subgroup.mem_subgroupOf.mp hy
    have hyK : y ∈ conjClosure K T := hXK hyX
    have hxA : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨y, h.K₀_le_H hyK⟩ ∈
        autIH V₁ I H (conjClosure K T) := hle (hyx ▸ x.2)
    have hxe : Subgroup.inclusion hle x = ⟨actH h.H_le_normalizer_V₁
        (le_normalizer_conjClosure I H) ⟨y, h.K₀_le_H hyK⟩, hxA⟩ := Subtype.ext hyx.symm
    show tauHat h hIU hAV (Subgroup.inclusion hle x) ∈ _
    rw [hxe, ← conjAct_hat_eq_tauHat h hIU hKI hAV hyK hxA]
    exact CFSG.Quasithin.AutOn.mem_autOn_iff.mpr ⟨_, kbarOf_mem_hat_of_mem h hXH hyX, rfl⟩
  let τ : ↥(autIH V₁ I H X) →*
      ↥(autOn (hat' V₁ Vp H K T X) (hat' V₁ Vp H K T I)) := τ0.codRestrict _ hτmem
  have hτs : Function.Surjective τ := by
    rintro ⟨a, ha⟩
    obtain ⟨n, hnY, rfl⟩ := CFSG.Quasithin.AutOn.mem_autOn_iff.mp ha
    obtain ⟨k, hk, hnk⟩ := (mem_hat_iff h hXH).mp hnY
    have hkK : k ∈ conjClosure K T := hXK hk
    have hxX : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨k, hXH hk⟩ ∈
        autIH V₁ I H X := by
      rw [autIH_eq_map h hXH]
      exact ⟨⟨k, hXH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    have hxA : actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨k, h.K₀_le_H hkK⟩ ∈
        autIH V₁ I H (conjClosure K T) := hle hxX
    refine ⟨⟨_, hxX⟩, Subtype.ext ?_⟩
    have hne : n = ⟨kbarOf h (h.K₀_le_H hkK),
        hatOf_le_normalizer hKI (kbarOf_mem_hat h hkK)⟩ := Subtype.ext hnk
    have hconj : conjAct (hat' V₁ Vp H K T I) n = tauHat h hIU hAV ⟨_, hxA⟩ := by
      rw [hne]
      exact conjAct_hat_eq_tauHat h hIU hKI hAV hkK hxA
    exact hconj.symm
  refine ⟨τ.comp π, realizesVia_transport (H' := autOn (hat' V₁ Vp H K T X)
    (hat' V₁ Vp H K T I)) hπ (thetaV h hIU) (thetaV_surjective h hIU) ?_ τ hτs ?_⟩
  · intro u
    rw [← MonoidHom.mem_ker, ker_thetaV, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun hh => ⟨u.2, hh⟩, fun hh => hh.2⟩
  · intro x u hu
    exact tauHat_thetaV h hIU hAV (Subgroup.inclusion hle x) u hu

@[expose] def NatSzU (Ks : Type) [Group Ks] {X : Type} [Group X] (Y A : Subgroup X) : Prop :=
  ∃ (a : ℕ) (F : Type) (_ : Field F) (_ : Finite F), 1 ≤ a ∧ Nat.card F = 2 ^ (2 * a + 1) ∧
    Nonempty (Ks ≃* ↥(CFSG.Blueprint.suzukiGroup a F)) ∧
    ModelOnU (FFModel.nat (CFSG.Blueprint.suzukiGroup a F)) Y A

@[expose] noncomputable def orthModelU (F : Type) [Field F] (σ : F →+* F) : FFModel where
  Gam := ↥(StatedSL 2 F)
  Amb := Multiplicative (Matrix (Fin 2) (Fin 2) F)
  act g X := Multiplicative.ofAdd
    (((g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) * Multiplicative.toAdd X *
      (((g : Matrix.GeneralLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F).map σ)ᵀ)
  sec := AddSubgroup.toSubgroup (AddMonoidHom.eqLocus (AddMonoidHom.id (Matrix (Fin 2) (Fin 2) F))
    ((AddMonoidHom.mapMatrix σ.toAddMonoidHom).comp
      (Matrix.transposeAddEquiv (Fin 2) (Fin 2) F).toAddMonoidHom))
  ker := ⊥

@[expose] def F918NatChoice5U (V₁ Vp H K T I : Subgroup G) : Prop :=
  (∃ n : ℕ, NatSLU 2 n ↥(autIH V₁ Vp H K) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)) ∨
    NatSzU ↥(autIH V₁ Vp H K) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I) ∨
    (Nonempty (↥(autIH V₁ Vp H K) ≃* alternatingGroup (Fin 5)) ∧
      ModelOnU (FFModel.altDn 5) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)) ∨
    NatSLU 3 1 ↥(autIH V₁ Vp H K) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)

theorem frobPow_sigma {F : Type} [Field F] [Finite F] [CharP F 2] {a : ℕ} (ha : 1 ≤ a)
    (hcard : Nat.card F = 2 ^ (2 * a)) :
    iterateFrobenius F 2 a ≠ RingHom.id F ∧
      ∀ x, iterateFrobenius F 2 a (iterateFrobenius F 2 a x) = x := by
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2 ^ (2 * a) := by rw [← Nat.card_eq_fintype_card]; exact hcard
  refine ⟨fun hid => ?_, fun x => ?_⟩
  · have hall : ∀ x : F, x ^ 2 ^ a = x := fun x => by
      have := congrArg (fun f : F →+* F => f x) hid
      simpa [iterateFrobenius_def] using this
    obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := Fˣ)
    have hg1 : g ^ (2 ^ a - 1) = 1 := by
      have h1 : (g : F) ^ 2 ^ a = g := hall g
      have h2 : g ^ 2 ^ a = g := Units.ext (by simpa using h1)
      have h3 : g ^ (2 ^ a - 1) * g = g := by
        rw [← pow_succ, Nat.sub_add_cancel (Nat.one_le_two_pow)]
        exact h2
      simpa using h3
    have hord : orderOf g = Nat.card Fˣ := orderOf_eq_card_of_forall_mem_zpowers hg
    have hdvd : Nat.card Fˣ ∣ 2 ^ a - 1 := hord ▸ orderOf_dvd_of_pow_eq_one hg1
    have hpos : 0 < 2 ^ a - 1 := by
      have : 2 ≤ 2 ^ a := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
      omega
    have hle := Nat.le_of_dvd hpos hdvd
    rw [Nat.card_units, hcard] at hle
    have : 2 ^ a < 2 ^ (2 * a) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    omega
  · simp only [iterateFrobenius_def]
    calc (x ^ 2 ^ a) ^ 2 ^ a = x ^ (2 ^ (2 * a)) := by
          rw [← pow_mul, ← pow_add, ← two_mul]
      _ = x := by rw [← hcardF]; exact FiniteField.pow_card x

theorem realizes_congr {V : Type*} [CommGroup V] {Gam Amb : Type} [Group Gam] [CommGroup Amb]
    (act act' : Gam → Amb → Amb) (hact : ∀ g m, act g m = act' g m) (sec sec' ker ker' : Subgroup Amb)
    (hsec : sec = sec') (hker : ker = ker') (H : Subgroup (MulAut V)) (U Z : Subgroup V) :
    (FFModel.mk (gamGroup := inferInstance) (ambGroup := inferInstance) Gam Amb act sec ker).Realizes
      H U Z ↔
    (FFModel.mk (gamGroup := inferInstance) (ambGroup := inferInstance) Gam Amb act' sec' ker').Realizes
      H U Z := by
  subst hsec hker
  have : act = act' := funext fun g => funext (hact g)
  subst this
  exact Iff.rfl

theorem realizes_orthModelU_iff {F : Type} [Field F] [CharP F 2] (a : ℕ) {V : Type*} [CommGroup V]
    (H : Subgroup (MulAut V)) (U Z : Subgroup V) :
    (orthModelU F (iterateFrobenius F 2 a)).Realizes H U Z ↔
      (FFModel.twistTensor a (StatedSL 2 F)).Realizes H U Z := by
  refine realizes_congr (V := V) (Gam := ↥(StatedSL 2 F))
    (Amb := Multiplicative (Matrix (Fin 2) (Fin 2) F)) _ _ (fun g m => rfl) _ _ ⊥ ⊥ ?_ rfl H U Z
  ext X
  show Multiplicative.toAdd X = ((Multiplicative.toAdd X)ᵀ).map (iterateFrobenius F 2 a) ↔
    ((Multiplicative.toAdd X).map fun x => x ^ 2 ^ a)ᵀ = Multiplicative.toAdd X
  rw [Matrix.transpose_map, eq_comm]
  rfl

theorem isSimpleGroup_statedSL_two {F : Type} [Field F] [Finite F] {n : ℕ} (hn : 2 ≤ n)
    (hcard : Nat.card F = 2 ^ n) : IsSimpleGroup ↥(StatedSL 2 F) := by
  haveI : CharP F 2 := charP_two_of_card_pow_two hcard
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h22 : 2 ≠ 2 ∨ Nat.card F ≠ 2 := Or.inr (by omega)
  have h23 : 2 ≠ 2 ∨ Nat.card F ≠ 3 := Or.inr (by omega)
  haveI := CFSG.Open.StatedAPI.isSimpleGroup_statedProj_statedSL (d := 2) F le_rfl h22 h23
  exact ((QuotientGroup.quotientMulEquivOfEq
    (CFSG.Open.StatedAPI.statedScalars_subgroupOf_statedSL_two_eq_bot (K := F))).trans
      QuotientGroup.quotientBot).symm.isSimpleGroup

theorem five_iii_a_of_modFiveA (h : HypF918 T V L V₁ Vp H K)
    (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hKI : conjClosure K T ≤ Subgroup.normalizer (I : Set G))
    (hA : ModFiveA (autIH V₁ I H (conjClosure K T)) (autIH V₁ I H K)
      (subM V₁ (conjClosure I H) I)) :
    hat' V₁ Vp H K T ⁅conjClosure I H, K⁆ = hat' V₁ Vp H K T I ∧
      (F918NatChoice5U V₁ Vp H K T I ∨
        ∃ (n : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (σ : F →+* F), Even n ∧
          Nat.card F = 2 ^ n ∧ σ ≠ RingHom.id F ∧ (∀ x, σ (σ x) = x) ∧
          Nonempty (↥(autIH V₁ Vp H K) ≃* ↥(StatedSL 2 F)) ∧
          ModelOnU (orthModelU F σ) (hat' V₁ Vp H K T K) (hat' V₁ Vp H K T I)) := by
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hKK : K ≤ conjClosure K T := le_conjClosure K T
  have hAV := autIH_le_stabSub_subM h hIU hV₁I (le_conjClosure I H) hKI
  obtain ⟨eA⟩ := autIH_equiv h hH hA37 hA38 hK hIU hnt
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map h hKH]
    exact map_K_ne_bot h hIU hnt
  refine ⟨?_, ?_⟩
  · have h1 : subM V₁ (conjClosure I H) ⁅conjClosure I H, K⁆ = subM V₁ (conjClosure I H) I := by
      rw [← commV_autIH_eq_subM h hIU hKH]
      exact hA.1
    have hJle : ⁅conjClosure I H, K⁆ ≤ conjClosure I H := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.le_normalizer_iff_commutator_le_right.mp
        (hKH.trans (le_normalizer_conjClosure I H))
    rw [hat_eq_map_theta h hIU hJle, hat_eq_map_theta h hIU (le_conjClosure I H), h1]
  · rcases hA.2 with ⟨n, F, hF, hFin, hcard, hreal⟩ | ⟨F, hF, hFin, hcard, hreal⟩ |
      ⟨f, a, ha1, hf, F, hF, hFin, hcard, hreal⟩ | ⟨a, ha1, F, hF, hFin, hchar, hcard, hreal⟩ | hreal
    · refine Or.inl (Or.inl ⟨n, F, hF, hFin, hcard, ?_,
        modelOnU_of_realizes_le h hIU hKI hKK hAV hreal⟩)
      obtain ⟨π, hπ⟩ := hreal
      have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
      exact ⟨eA.trans (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩
    · refine Or.inl (Or.inr (Or.inr (Or.inr ⟨F, hF, hFin, hcard, ?_,
        modelOnU_of_realizes_le h hIU hKI hKK hAV hreal⟩)))
      obtain ⟨π, hπ⟩ := hreal
      have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
      exact ⟨eA.trans (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩
    · refine Or.inl (Or.inr (Or.inl ⟨a, F, hF, hFin, ha1, hf ▸ hcard, ?_,
        modelOnU_of_realizes_le h hIU hKI hKK hAV hreal⟩))
      obtain ⟨π, hπ⟩ := hreal
      have hinj := realizesVia_injective_of_faithful (FFModel.nat_faithful _) hπ
      exact ⟨eA.trans (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩
    ·
      right
      have hcard' : Nat.card F = 2 ^ (2 * a) := hcard
      obtain ⟨hσne, hσσ⟩ := frobPow_sigma ha1 hcard'
      refine ⟨2 * a, F, hF, hFin, iterateFrobenius F 2 a, even_two_mul a, hcard', hσne, hσσ, ?_, ?_⟩
      · obtain ⟨π, hπ⟩ := hreal
        haveI hsimp : IsSimpleGroup ↥(StatedSL 2 F) := isSimpleGroup_statedSL_two (n := 2 * a) (by omega) hcard'
        obtain ⟨s, hs⟩ : ∃ s, π s ≠ 1 := by
          obtain ⟨y, hy1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
          obtain ⟨s, hs⟩ := hπ.1 y
          exact ⟨s, fun h1 => hy1 (Subtype.ext (by rw [← hs, h1]))⟩
        have hinj := injective_of_isSimpleGroup (S := ↥(StatedSL 2 F)) π ⟨s, hs⟩
        exact ⟨eA.trans (MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩
      · exact modelOnU_of_realizes_le h hIU hKI hKK hAV ((realizes_orthModelU_iff a _ _ _).mpr hreal)
    · refine Or.inl (Or.inr (Or.inr (Or.inl ⟨?_,
        modelOnU_of_realizes_le h hIU hKI hKK hAV hreal⟩)))
      obtain ⟨π, hπ⟩ := hreal
      obtain ⟨πe⟩ := alt_mulEquiv_of_surj (n := 5) (by norm_num) hne π hπ.1
      exact ⟨eA.trans πe.symm⟩

theorem actH_mem_normalizer_autIH (h : HypF918 T V L V₁ Vp H K) {X : Subgroup G} (hXH : X ≤ H) {s : G}
    (hsH : s ∈ H) (hsX : s ∈ Subgroup.normalizer (X : Set G)) :
    actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) ⟨s, hsH⟩ ∈
      Subgroup.normalizer ((autIH V₁ I H X : Subgroup _) : Set _) := by
  rw [← A38.map_conj_eq_iff]
  have h1 := conjAutSub_autIH (I := I) h hXH hsH
  have h2 : conjSub s X = X := A38.map_conj_eq_iff.mpr hsX
  rw [h2] at h1
  exact h1

theorem five_iii_b_of_modFiveB (h : HypF918 T V L V₁ Vp H K)
    (hH : SQTKGroup ↥H) (hA37 : A37ForSQTK) (hA38 : A38ForSQTK) (hK : conjClosure K T ≠ K)
    (hV₁I : V₁ ≤ I) (hIU : I ≤ conjClosure Vp H)
    (hnt : ¬ ∀ k ∈ conjClosure K T, ∀ i ∈ I, k * i * k⁻¹ * i⁻¹ ∈ V₁)
    (hB : ModFiveB (autIH V₁ I H T) (autIH V₁ I H K) (subM V₁ (conjClosure I H) I)) :
    LieModel ↥(autIH V₁ Vp H K) .PSL 3 2 1 ∧
      (∃ s : G, s ∈ T ∧ s ∈ Subgroup.normalizer (K : Set G) ∧
        s ∉ Subgroup.normalizer (I : Set G)) ∧
      ∀ s : G, s ∈ T → s ∈ Subgroup.normalizer (K : Set G) → s ∉ Subgroup.normalizer (I : Set G) →
        (tildeOf V₁ ⁅conjClosure I H, K⁆ = tildeOf V₁ I ⊔ tildeOf V₁ (conjSub s⁻¹ I) ∧
          tildeOf V₁ I ⊓ tildeOf V₁ (conjSub s⁻¹ I) = ⊥) ∧
        Nat.card ↥(tildeOf V₁ I) = 2 ^ 3 := by
  obtain ⟨hPSL, ⟨s', hs'T, hs'N, hs'V⟩, hdir, hcard⟩ := hB
  have hKH : K ≤ H := le_of_mem_cComp h.K_cComp
  have hIHN := h.conjClosure_le_normalizer_V₁ hIU
  have hIH := le_normalizer_conjClosure I H
  obtain ⟨eA⟩ := autIH_equiv h hH hA37 hA38 hK hIU hnt
  have hprel := five_prelim h hH hK hIU hnt hA37 hA38
  have hle : tildeOf V₁ I ≤ tildeOf V₁ (conjClosure I H) := secImg_mono (le_conjClosure I H)
  refine ⟨lieModel_of_isPSL (isPSL_congr eA.symm hPSL), ?_, ?_⟩
  ·
    have hs'T' : s' ∈ (T.subgroupOf H).map
        (actH h.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)) := by
      rw [← autIH_eq_map h h.T_le_H]
      exact hs'T
    obtain ⟨⟨s, hsH⟩, hsT, rfl⟩ := hs'T'
    have hsT' : s ∈ T := Subgroup.mem_subgroupOf.mp hsT
    refine ⟨s, hsT', ?_, fun hsI => hs'V ?_⟩
    · by_contra hsK
      exact (hprel.2.2 s hsT' hsK).2.1 hs'N
    · exact (actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ hIHN hIH hV₁I (le_conjClosure I H)
        ⟨s, hsH⟩).mpr hsI
  · intro s hsT hsK hsI
    have hsH : s ∈ H := h.T_le_H hsT
    have hsinvT : s⁻¹ ∈ T := T.inv_mem hsT
    have hsinvH : s⁻¹ ∈ H := H.inv_mem hsH
    have hmemT : actH h.H_le_normalizer_V₁ hIH ⟨s⁻¹, hsinvH⟩ ∈ autIH V₁ I H T := by
      rw [autIH_eq_map h h.T_le_H]
      exact ⟨⟨s⁻¹, hsinvH⟩, Subgroup.mem_subgroupOf.mpr hsinvT, rfl⟩
    have hmemN := actH_mem_normalizer_autIH (I := I) h hKH hsinvH
      ((Subgroup.inv_mem_iff _).mpr hsK)
    have hmemV : actH h.H_le_normalizer_V₁ hIH ⟨s⁻¹, hsinvH⟩ ∉
        stabSub (subM V₁ (conjClosure I H) I) := fun hst =>
      hsI ((Subgroup.inv_mem_iff _).mp
        ((actH_mem_stabSub_subM_iff h.H_le_normalizer_V₁ hIHN hIH hV₁I (le_conjClosure I H)
          ⟨s⁻¹, hsinvH⟩).mp hst))
    obtain ⟨hsup, hinf⟩ := hdir _ hmemT hmemN hmemV
    have hmap := map_actH_subM h.H_le_normalizer_V₁ hIHN hIH hV₁I (le_conjClosure I H)
      (⟨s⁻¹, hsinvH⟩ : ↥H)
    have hQ : conjSub s⁻¹ I ≤ conjClosure I H := conjSub_inv_le_conjClosure hsH I
    have hleQ : tildeOf V₁ (conjSub s⁻¹ I) ≤ tildeOf V₁ (conjClosure I H) := secImg_mono hQ
    have hmap' : (subM V₁ (conjClosure I H) I).map
        (actH h.H_le_normalizer_V₁ hIH ⟨s⁻¹, hsinvH⟩).toMonoidHom =
        subM V₁ (conjClosure I H) (conjSub s⁻¹ I) := hmap
    rw [hmap'] at hsup hinf
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · have h1 := congrArg (Subgroup.map (tildeOf V₁ (conjClosure I H)).subtype) hsup
      rw [commV_autIH_eq_subM h hIU hKH, Subgroup.map_sup, map_subtype_subM hle,
        map_subtype_subM hleQ,
        map_subtype_subM (show tildeOf V₁ ⁅conjClosure I H, K⁆ ≤
          tildeOf V₁ (conjClosure I H) from secImg_mono (by
            rw [Subgroup.commutator_comm]
            exact Subgroup.le_normalizer_iff_commutator_le_right.mp
              (hKH.trans hIH)))] at h1
      exact h1.symm
    · have h1 := congrArg (Subgroup.map (tildeOf V₁ (conjClosure I H)).subtype) hinf
      rw [Subgroup.map_inf _ _ _ (tildeOf V₁ (conjClosure I H)).subtype_injective,
        map_subtype_subM hle, map_subtype_subM hleQ, Subgroup.map_bot] at h1
      exact h1
    · rw [← hcard]
      exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv).symm

end Iii

end CFSG.Quasithin.RonanF918
