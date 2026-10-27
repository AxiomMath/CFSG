module

public import CFSG.Sporadic.Recognition.LyonsAS44McLSpec
public import CFSG.Sporadic.Recognition.LyonsLocalThreeA

public section

namespace CFSG.Sporadic.Recognition.McLAS

open Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
  CFSG.Sporadic.Schreier.Native CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native
  CFSG.ComponentClassification.OuterAutomorphisms CFSG.Blueprint
  CFSG.Sporadic.Recognition.LyonsSims

structure NormFacts (K : Type*) [Group K] (y : K) (A : Subgroup K) (Y : Fin 10 → K) : Prop where
  zero : Y 0 = y
  mem_A : ∀ i, Y i ∈ A
  isConj : ∀ i, IsConj y (Y i)
  distinct : ∀ i j, (Y i = Y j ∨ Y i = (Y j)⁻¹) → i = j
  cover : ∀ z ∈ A, IsConj y z → ∃ i, z = Y i ∨ z = (Y i)⁻¹
  trans3 : ∀ a b : Fin 3 → Fin 10, Function.Injective a → Function.Injective b →
    ∃ g ∈ normalizer (A : Set K),
      ∀ i, g * Y (a i) * g⁻¹ = Y (b i) ∨ g * Y (a i) * g⁻¹ = (Y (b i))⁻¹
  sharp3 : ∀ g ∈ normalizer (A : Set K), ∀ a : Fin 3 → Fin 10, Function.Injective a →
    (∀ i, g * Y (a i) * g⁻¹ = Y (a i) ∨ g * Y (a i) * g⁻¹ = (Y (a i))⁻¹) → g ∈ A

structure McLFacts (K : Type) [Group K] (y z : K) (R T A : Subgroup K) (Y : Fin 10 → K) :
    Prop where
  order_y : orderOf y = 3
  card_cent : Nat.card ↥(centralizer ({y} : Set K)) = 29160
  threeCore : ThreeCore y R
  R_exp : ∀ r ∈ R, r ^ 3 = 1
  R_center : R ⊓ centralizer (R : Set K) = zpowers y
  R_le_T : R ≤ T
  A_le_T : A ≤ T
  T_card : Nat.card ↥T = 729
  T_sup : R ⊔ A = T
  A_elem : CFSG.IsElementaryAbelian 3 ↥A
  A_card : Nat.card ↥A = 81
  A_gen : A = closure ((T : Set K) ∩ {w | IsConj y w})
  A_class : ((T : Set K) ∩ {w | IsConj y w}).ncard = 20
  order_three : ∀ w ∈ T, orderOf w = 3 → w ∈ R ∨ w ∈ A
  weakly_closed : ∀ r ∈ R, IsConj y r → r = y ∨ r = y⁻¹
  inverting : ∃ σ : MulAut K, orderOf σ = 2 ∧ σ ∉ inner K ∧ ∀ a ∈ A, σ a = a⁻¹
  z_mem : z ∈ A
  norm : NormFacts K y A Y

section Embedding

variable {K : Type*} [Group K]

theorem normFacts_of_embedding (ι : K →* Equiv.Perm (Fin 275)) (hι : Function.Injective ι)
    (hrange : ι.range = mclP) {Y₀ : Fin 10 → Equiv.Perm (Fin 275)} (h : PinnedNorm Y₀) :
    ∃ Y : Fin 10 → K, (∀ i, ι (Y i) = Y₀ i) ∧ NormFacts K (Y 0) (subA3.comap ι) Y := by
  have hAP : subA3 ≤ ι.range := hrange ▸ h.le
  have hmapA : (subA3.comap ι).map ι = subA3 := Subgroup.map_comap_eq_self hAP
  have hexY : ∀ i, ∃ y : K, ι y = Y₀ i := fun i => hAP (h.mem_A i)
  choose Y hY using hexY
  have hmemA : ∀ i, Y i ∈ subA3.comap ι := fun i => by rw [mem_comap, hY]; exact h.mem_A i
  have hN : ∀ g : K, g ∈ normalizer ((subA3.comap ι : Subgroup K) : Set K) ↔
      ι g ∈ mclP ⊓ normalizer (subA3 : Set (Equiv.Perm (Fin 275))) := by
    intro g
    have := map_normalizer_eq_inf_of_injective hι (subA3.comap ι)
    rw [hmapA, hrange] at this
    constructor
    · intro hg
      rw [← this]
      exact ⟨g, hg, rfl⟩
    · intro hg
      rw [← this] at hg
      obtain ⟨g', hg', hgg'⟩ := hg
      rwa [← hι hgg']
  refine ⟨Y, hY, rfl, hmemA, fun i => ?_, fun i j hij => ?_, fun z hz hzc => ?_, ?_, ?_⟩
  · obtain ⟨c, hc, hci⟩ := h.conj i
    obtain ⟨c', rfl⟩ : c ∈ ι.range := hrange ▸ hc
    refine isConj_iff.2 ⟨c', hι ?_⟩
    rw [map_mul, map_mul, map_inv, hY, hY, hci, h.zero]
  · apply h.distinct
    rcases hij with hij | hij
    · left
      rw [← hY, ← hY, hij]
    · right
      rw [← hY, ← hY, hij, map_inv]
  · have hz' : ι z ∈ subA3 := mem_comap.1 hz
    obtain ⟨c', hc'⟩ := isConj_iff.1 hzc
    have hcls : ι z ∈ conjClass mclP three₁ := by
      refine ⟨ι c', hrange ▸ ⟨c', rfl⟩, ?_⟩
      rw [← hc', map_mul, map_mul, map_inv, hY 0, h.zero]
    obtain ⟨i, hi⟩ := h.cover _ hz' hcls
    refine ⟨i, ?_⟩
    rcases hi with hi | hi
    · left
      exact hι (by rw [hY]; exact hi)
    · right
      exact hι (by rw [map_inv, hY]; exact hi)
  · intro a b ha hb
    obtain ⟨g, hg, hgi⟩ := h.trans3 a b ha hb
    obtain ⟨g', rfl⟩ : g ∈ ι.range := hrange ▸ (mem_inf.1 hg).1
    refine ⟨g', (hN g').2 hg, fun i => ?_⟩
    rcases hgi i with hh | hh
    · left
      apply hι
      rw [map_mul, map_mul, map_inv, hY, hY, hh]
    · right
      apply hι
      rw [map_mul, map_mul, map_inv, map_inv, hY, hY, hh]
  · intro g hg a ha hga
    have hg' := (hN g).1 hg
    refine mem_comap.2 (h.sharp3 (ι g) hg' a ha fun i => ?_)
    rcases hga i with hh | hh
    · left
      have := congrArg ι hh
      rwa [map_mul, map_mul, map_inv, hY] at this
    · right
      have := congrArg ι hh
      rwa [map_mul, map_mul, map_inv, map_inv, hY] at this

end Embedding

theorem threeLocalAut_of_equiv'
    {T : Type*} [Group T] (e : T ≃* mclP)
    (Φ : MulAut T ≃* mclR)
    (hΦ1 : ∀ (σ : MulAut T) (g : T), ((e (σ g) : mclP) : Equiv.Perm (Fin 275)) =
      (Φ σ : Equiv.Perm (Fin 275)) * ((e g : mclP) : Equiv.Perm (Fin 275)) *
        (Φ σ : Equiv.Perm (Fin 275))⁻¹)
    (hΦ2 : ∀ σ : MulAut T, σ ∈ inner T ↔ ((Φ σ : mclR) : Equiv.Perm (Fin 275)) ∈ mclP)
    (hΦ3 : ∀ c : T, ((Φ (MulAut.conj c) : mclR) : Equiv.Perm (Fin 275)) =
      ((e c : mclP) : Equiv.Perm (Fin 275)))
    (hrows : ThreeFacts) (hsyl : sylowThreeOK = true) (h : threeLocalCheck = true) :
    ∃ (x : T) (R T' A : Subgroup T),
      ((e x : mclP) : Equiv.Perm (Fin 275)) = three₁ ∧
      A = subA3.comap (mclP.subtype.comp e.toMonoidHom) ∧ ThreeLocalAut T x R T' A := by
  let ι : T →* Equiv.Perm (Fin 275) := mclP.subtype.comp e.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp e.injective
  have hrange : ι.range = mclP := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr e.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hιe : ∀ g : T, ι g = ((e g : mclP) : Equiv.Perm (Fin 275)) := fun g => rfl
  obtain ⟨x, R, T', A, hxι, hAι, hL, hΔ, hA, hcount⟩ :=
    delta_of_embedding ι hι hrange hrows hsyl h
  have h' := h
  simp only [threeLocalCheck, Bool.and_eq_true] at h'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨he, hg⟩, hin⟩, -⟩, -⟩, -⟩, hAc⟩, hinvc⟩, -⟩, -⟩ := h'
  obtain ⟨hσR, hσP, hσ2, hσinv⟩ := aInvCheck_spec hrows he hin hAc hinvc
  obtain ⟨-, hcardgxh⟩ := card_gx hrows hg
  let ι' : MulAut T →* Equiv.Perm (Fin 275) := mclR.subtype.comp Φ.toMonoidHom
  have hι' : Function.Injective ι' := Subtype.val_injective.comp Φ.injective
  have hrange' : ι'.range = mclR := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr Φ.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have hι'x : ι' (MulAut.conj x) = three₁ := by
    change ((Φ (MulAut.conj x) : mclR) : Equiv.Perm (Fin 275)) = three₁
    rw [hΦ3 x, ← hxι]
    rfl
  refine ⟨x, R, T', A, hxι, hAι, ?_⟩
  refine
    { hL with
      delta_iff := hΔ
      A_eq_delta := hA
      card_delta_inter := hcount
      card_normalizer_aut := ?_
      exists_inverting := ?_ }
  · have hmap := map_normalizer_eq_inf_of_injective hι' (zpowers (MulAut.conj x : MulAut T))
    rw [MonoidHom.map_zpowers, hι'x, hrange'] at hmap
    rw [← Subgroup.card_map_of_injective hι', hmap]
    exact hcardgxh
  · let σ : MulAut T := Φ.symm ⟨tp 275 sigmaTab, hσR⟩
    have hΦσ : ((Φ σ : mclR) : Equiv.Perm (Fin 275)) = tp 275 sigmaTab := by
      simp [σ]
    refine ⟨σ, ?_, ?_, ?_⟩
    · have hord : orderOf ((Φ σ : mclR) : Equiv.Perm (Fin 275)) = orderOf σ := by
        rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq]
      rw [← hord, hΦσ]
      exact hσ2
    · rw [hΦ2, hΦσ]
      exact hσP
    · intro a ha
      apply hι
      have h1 := hΦ1 σ a
      rw [hΦσ] at h1
      have haA : ι a ∈ subA3 := by rw [hAι] at ha; exact ha
      have h2 := hσinv (ι a) haA
      rw [hιe, map_inv]
      rw [h1]
      exact h2

section Align

theorem exists_conj_mem_sylow {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (P : Subgroup G) (hP : Nat.card P = p ^ (Nat.card G).factorization p) {v : G}
    (hv : IsPGroup p (zpowers v)) : ∃ c : G, c⁻¹ * v * c ∈ P := by
  let S : Sylow p G := Sylow.ofCard P hP
  obtain ⟨Q, hQ⟩ := hv.exists_le_sylow
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq G S Q
  refine ⟨c, ?_⟩
  have hvQ : v ∈ (Q : Subgroup G) := hQ (mem_zpowers v)
  rw [← hc, Sylow.coe_subgroup_smul, mem_pointwise_smul_iff_inv_smul_mem] at hvQ
  have : (MulAut.conj c)⁻¹ • v = c⁻¹ * v * c := by
    simp [MulAut.smul_def]
  rw [this] at hvQ
  exact hvQ

theorem exists_conj_mem_A {G : Type} [Group G] [Finite G] {x : G} {R T A : Subgroup G}
    (hL : ThreeLocal G x R T A) (hTC : T ≤ centralizer ({x} : Set G)) {v : G}
    (hv : v ∈ centralizer ({x} : Set G)) (hv3 : orderOf v = 3) (hvc : IsConj x v) :
    ∃ c ∈ centralizer ({x} : Set G), c * v * c⁻¹ ∈ A := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  set Γ : Subgroup G := centralizer ({x} : Set G) with hΓ
  have hfac : (Nat.card ↥Γ).factorization 3 = 6 := by
    rw [hΓ, hL.card_centralizer, show (29160 : ℕ) = 3 ^ 6 * 40 by norm_num,
      Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow (by norm_num : Nat.Prime 3), Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
  have hP : Nat.card ↥(T.subgroupOf Γ) = 3 ^ (Nat.card ↥Γ).factorization 3 := by
    rw [Nat.card_congr (subgroupOfEquivOfLe hTC).toEquiv, hL.card_T, hfac]
    norm_num
  let v' : ↥Γ := ⟨v, hv⟩
  have hv'3 : IsPGroup 3 (zpowers v') := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, Subgroup.orderOf_mk, hv3]
    norm_num
  obtain ⟨c', hc'⟩ := exists_conj_mem_sylow (T.subgroupOf Γ) hP hv'3
  refine ⟨(c'⁻¹ : ↥Γ), (c'⁻¹ : ↥Γ).2, ?_⟩
  have hT : ((c'⁻¹ * v' * c'⁻¹⁻¹ : ↥Γ) : G) ∈ T := by
    have := hc'
    rw [mem_subgroupOf] at this
    simpa using this
  have hconj : IsConj x (((c'⁻¹ : ↥Γ) : G) * v * ((c'⁻¹ : ↥Γ) : G)⁻¹) := by
    refine hvc.trans (isConj_iff.2 ⟨((c'⁻¹ : ↥Γ) : G), rfl⟩)
  rw [hL.A_eq]
  exact subset_closure ⟨by simpa using hT, hconj⟩

end Align

section Facts


theorem mclFacts_of_equiv (hnrm : nrmCheck = true) {T : Type} [Group T] (eT : T ≃* mclP)
    (Φ₀ : MulAut T ≃* mclR)
    (hΦ1₀ : ∀ (σ : MulAut T) (g : T), ((eT (σ g) : mclP) : Equiv.Perm (Fin 275)) =
      (Φ₀ σ : Equiv.Perm (Fin 275)) * ((eT g : mclP) : Equiv.Perm (Fin 275)) *
        (Φ₀ σ : Equiv.Perm (Fin 275))⁻¹)
    (hΦ2₀ : ∀ σ : MulAut T, σ ∈ inner T ↔ ((Φ₀ σ : mclR) : Equiv.Perm (Fin 275)) ∈ mclP)
    (hΦ3₀ : ∀ c : T, ((Φ₀ (MulAut.conj c) : mclR) : Equiv.Perm (Fin 275)) =
      ((eT c : mclP) : Equiv.Perm (Fin 275)))
    {K : Type} [Group K] (e : K ≃* T) {y z : K}
    (hy : ((eT (e y) : mclP) : Equiv.Perm (Fin 275)) = three₁)
    (hz : ((eT (e z) : mclP) : Equiv.Perm (Fin 275)) ∈ subA3) :
    ∃ R T' A Y, McLFacts K y z R T' A Y := by
  have hrows := threeFacts_cert'
  have hsyl := sylowThreeOK_eq_true'
  have hloc := threeLocalCheck_eq_true
  let eP : K ≃* mclP := e.trans eT
  let Φ : MulAut K ≃* mclR := (MulAut.congr e).trans Φ₀
  have hcongr : ∀ (σ : MulAut K) (g : K), MulAut.congr e σ (e g) = e (σ g) := by
    intro σ g
    rw [MulAut.congr_apply]
    simp
  have hΦ1 : ∀ (σ : MulAut K) (g : K), ((eP (σ g) : mclP) : Equiv.Perm (Fin 275)) =
      (Φ σ : Equiv.Perm (Fin 275)) * ((eP g : mclP) : Equiv.Perm (Fin 275)) *
        (Φ σ : Equiv.Perm (Fin 275))⁻¹ := by
    intro σ g
    have h1 := hΦ1₀ (MulAut.congr e σ) (e g)
    rw [hcongr] at h1
    exact h1
  have hΦ2 : ∀ σ : MulAut K, σ ∈ inner K ↔ ((Φ σ : mclR) : Equiv.Perm (Fin 275)) ∈ mclP := by
    intro σ
    change σ ∈ inner K ↔ ((Φ₀ (MulAut.congr e σ) : mclR) : Equiv.Perm (Fin 275)) ∈ mclP
    rw [← hΦ2₀]
    constructor
    · intro hσ
      rw [← inner_map_congr e]
      exact ⟨σ, hσ, rfl⟩
    · intro hσ
      rw [← inner_map_congr e] at hσ
      obtain ⟨τ, hτ, hτσ⟩ := hσ
      have : τ = σ := (MulAut.congr e).injective hτσ
      rwa [← this]
  have hΦ3 : ∀ c : K, ((Φ (MulAut.conj c) : mclR) : Equiv.Perm (Fin 275)) =
      ((eP c : mclP) : Equiv.Perm (Fin 275)) := by
    intro c
    have h1 := hΦ3₀ (e c)
    change ((Φ₀ (MulAut.congr e (MulAut.conj c)) : mclR) : Equiv.Perm (Fin 275)) = _
    rw [congr_conj]
    exact h1
  obtain ⟨x, R, T', A, hx, hA, hL⟩ :=
    threeLocalAut_of_equiv' eP Φ hΦ1 hΦ2 hΦ3 hrows hsyl hloc
  have hxy : x = y := eP.injective (Subtype.ext (hx.trans hy.symm))
  subst hxy
  let ι : K →* Equiv.Perm (Fin 275) := mclP.subtype.comp eP.toMonoidHom
  have hι : Function.Injective ι := Subtype.val_injective.comp eP.injective
  have hrange : ι.range = mclP := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eP.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  obtain ⟨Y₀, hY₀⟩ := nrmCheck_spec hrows hloc hnrm
  obtain ⟨Y, hYι, hN⟩ := normFacts_of_embedding ι hι hrange hY₀
  have hY0 : Y 0 = x := by
    apply hι
    rw [hYι, hY₀.zero]
    exact hx.symm
  rw [hY0, ← hA] at hN
  refine ⟨R, T', A, Y, ?_⟩
  exact
    { order_y := hL.order_x
      card_cent := hL.card_centralizer
      threeCore := ThreeCore.of_threeLocal hL.toThreeLocal
      R_exp := hL.exponent_R
      R_center := hL.center_R
      R_le_T := hL.R_le_T
      A_le_T := hL.A_le_T
      T_card := hL.card_T
      T_sup := hL.sup_eq
      A_elem := hL.A_elementaryAbelian
      A_card := hL.card_A
      A_gen := hL.A_eq
      A_class := hL.card_class_inter
      order_three := hL.order_three
      weakly_closed := hL.weakly_closed
      inverting := hL.exists_inverting
      z_mem := by rw [hA]; exact hz
      norm := hN }

theorem exists_mclFacts_aux (hnrm : nrmCheck = true) {T : Type} [Group T] (eT : T ≃* mclP)
    (Φ₀ : MulAut T ≃* mclR)
    (hΦ1₀ : ∀ (σ : MulAut T) (g : T), ((eT (σ g) : mclP) : Equiv.Perm (Fin 275)) =
      (Φ₀ σ : Equiv.Perm (Fin 275)) * ((eT g : mclP) : Equiv.Perm (Fin 275)) *
        (Φ₀ σ : Equiv.Perm (Fin 275))⁻¹)
    (hΦ2₀ : ∀ σ : MulAut T, σ ∈ inner T ↔ ((Φ₀ σ : mclR) : Equiv.Perm (Fin 275)) ∈ mclP)
    (hΦ3₀ : ∀ c : T, ((Φ₀ (MulAut.conj c) : mclR) : Equiv.Perm (Fin 275)) =
      ((eT c : mclP) : Equiv.Perm (Fin 275)))
    {K : Type} [Group K] (e : K ≃* T) {y z : K} (hy3 : orderOf y = 3)
    (hyc : Nat.card ↥(centralizer ({y} : Set K)) = 29160) (hz3 : orderOf z = 3)
    (hzc : Nat.card ↥(centralizer ({z} : Set K)) = 29160) (hyz : y * z = z * y) :
    ∃ R T' A Y, McLFacts K y z R T' A Y := by
  have hrows := threeFacts_cert'
  have hloc := threeLocalCheck_eq_true
  let ι₀ : T →* Equiv.Perm (Fin 275) := mclP.subtype.comp eT.toMonoidHom
  have hι₀ : Function.Injective ι₀ := Subtype.val_injective.comp eT.injective
  have hrange₀ : ι₀.range = mclP := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eT.surjective,
      ← MonoidHom.range_eq_map, range_subtype]
  have : Finite T := Finite.of_injective ι₀ hι₀
  obtain ⟨x₀, R₀, T₀, A₀, hx₀, hR₀, hT₀, hA₀, hL₀⟩ :=
    threeLocal_of_embedding ι₀ hι₀ hrange₀ hrows hloc
  have hTC : T₀ ≤ centralizer ({x₀} : Set T) := by
    simp only [threeLocalCheck, Bool.and_eq_true] at hloc
    obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨he, -⟩, hin⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩, -⟩ := hloc
    obtain ⟨-, -, -, hTc⟩ := rInTCheck_spec hrows he hin
    intro t ht
    rw [hT₀] at ht
    have h1 : ι₀ t ∈ centralizer ({three₁} : Set (Equiv.Perm (Fin 275))) := hTc ht
    rw [mem_centralizer_singleton_iff] at h1 ⊢
    apply hι₀
    rw [map_mul, map_mul, hx₀]
    exact h1
  obtain ⟨m₁, m₂, o₁, o₂, c₁, c₂, -, -, hnc, hall⟩ :=
    mclP_order_three_classes hrows
  obtain ⟨r₁, r₂, p₁, p₂, k₁, k₂, -, hallT⟩ :=
    exists_two_classes_of_equiv eT m₁ m₂ o₁ o₂ c₁ c₂ hnc hall
  have hu3 : orderOf (e y) = 3 := by rw [MulEquiv.orderOf_eq]; exact hy3
  have hw3 : orderOf (e z) = 3 := by rw [MulEquiv.orderOf_eq]; exact hz3
  have hu : Nat.card ↥(centralizer ({e y} : Set T)) = 29160 := by
    rw [card_centralizer_mulEquiv e y]
    exact hyc
  have hw : Nat.card ↥(centralizer ({e z} : Set T)) = 29160 := by
    rw [card_centralizer_mulEquiv e z]
    exact hzc
  have hconj1 : IsConj (e y) x₀ :=
    isConj_of_card_eq_aux k₂ hallT hu3 hL₀.order_x hu hL₀.card_centralizer
  obtain ⟨g₁, hg₁⟩ := isConj_iff.1 hconj1
  set v₀ : T := g₁ * e z * g₁⁻¹ with hv₀
  have hv₀3 : orderOf v₀ = 3 := by
    rw [hv₀, ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hw3
  have hv₀c : Nat.card ↥(centralizer ({v₀} : Set T)) = 29160 := by
    rw [← card_centralizer_eq_of_isConj (isConj_iff.2 ⟨g₁, rfl⟩ : IsConj (e z) v₀)]
    exact hw
  have hv₀x : v₀ ∈ centralizer ({x₀} : Set T) := by
    rw [mem_centralizer_singleton_iff, ← hg₁, hv₀]
    have hcomm : e y * e z = e z * e y := by rw [← map_mul, ← map_mul, hyz]
    calc g₁ * e z * g₁⁻¹ * (g₁ * e y * g₁⁻¹) = g₁ * (e z * e y) * g₁⁻¹ := by group
      _ = g₁ * (e y * e z) * g₁⁻¹ := by rw [hcomm]
      _ = g₁ * e y * g₁⁻¹ * (g₁ * e z * g₁⁻¹) := by group
  have hv₀conj : IsConj x₀ v₀ :=
    isConj_of_card_eq_aux k₂ hallT hL₀.order_x hv₀3 hL₀.card_centralizer hv₀c
  obtain ⟨c, hcC, hcv⟩ := exists_conj_mem_A hL₀ hTC hv₀x hv₀3 hv₀conj
  have hcx : c * x₀ * c⁻¹ = x₀ := by
    have := mem_centralizer_singleton_iff.1 hcC
    rw [this]
    group
  refine mclFacts_of_equiv hnrm eT Φ₀ hΦ1₀ hΦ2₀ hΦ3₀ (e.trans (MulAut.conj (c * g₁))) (y := y)
    (z := z) ?_ ?_
  · have : (MulAut.conj (c * g₁)) (e y) = x₀ := by
      rw [MulAut.conj_apply]
      calc c * g₁ * e y * (c * g₁)⁻¹ = c * (g₁ * e y * g₁⁻¹) * c⁻¹ := by group
        _ = x₀ := by rw [hg₁, hcx]
    change ((eT ((MulAut.conj (c * g₁)) (e y)) : mclP) : Equiv.Perm (Fin 275)) = three₁
    rw [this]
    exact hx₀
  · have : (MulAut.conj (c * g₁)) (e z) = c * v₀ * c⁻¹ := by
      rw [MulAut.conj_apply, hv₀]
      group
    change ((eT ((MulAut.conj (c * g₁)) (e z)) : mclP) : Equiv.Perm (Fin 275)) ∈ subA3
    rw [this]
    have h1 : c * v₀ * c⁻¹ ∈ A₀ := hcv
    rw [hA₀] at h1
    exact h1

theorem exists_mclFacts (hnrm : nrmCheck = true) {K : Type} [Group K]
    (e : K ≃* NativeSporadic.McL) {y z : K} (hy3 : orderOf y = 3)
    (hyc : Nat.card ↥(centralizer ({y} : Set K)) = 29160) (hz3 : orderOf z = 3)
    (hzc : Nat.card ↥(centralizer ({z} : Set K)) = 29160) (hyz : y * z = z * y) :
    ∃ R T A Y, McLFacts K y z R T A Y := by
  obtain ⟨Φ₀, hΦ1₀, hΦ2₀, hΦ3₀⟩ := exists_aut_model
  exact @exists_mclFacts_aux hnrm NativeSporadic.McL inferInstance
    mclPermEquiv Φ₀ hΦ1₀ hΦ2₀ hΦ3₀ K _ e y z hy3 hyc hz3 hzc hyz

end Facts

end CFSG.Sporadic.Recognition.McLAS
