module

public import CFSG.Walter.Bender1970.S2.Inner
public import CFSG.Walter.Bender1970.S2.PSL2Overgroups
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_19
public import CFSG.Walter.JRFacts
import CFSG.Adapters.GeneralizedFittingTop
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Walter

open CFSG.GorensteinWalter
open scoped MatrixGroups

theorem componentLayerOf_top_eq_layer (Y : Type*) [Group Y] :
    componentLayerOf (⊤ : Subgroup Y) = CFSG.layer Y :=
  (CFSG.Adapters.componentLayerOf_top_eq_componentClassification Y).trans
    (CFSG.layer_eq_componentClassification Y).symm

theorem componentLayerOf_top_le_normalizer {Y : Type*} [Group Y] [Finite Y] {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) :
    componentLayerOf (⊤ : Subgroup Y) ≤ Subgroup.normalizer (L : Set Y) := by
  refine sSup_le fun K hK => ?_
  rcases CFSG.LocalCores.distinct_components_commute
      ((isComponent_iff_isComponentOf_top K).mpr hK)
      ((isComponent_iff_isComponentOf_top L).mpr hL) with rfl | h
  · exact Subgroup.le_normalizer
  · exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h).trans
      (Subgroup.centralizer_le_normalizer _)

theorem exists_mul_ne_mul_of_isQuasisimple {Q : Type*} [Group Q]
    (hQ : GorensteinWalter.IsQuasisimple Q) : ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := IsQuasisimple.exists_mul_ne_mul hQ
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  exact ⟨a, b, fun h => hab (by rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h])⟩

section Normalized

variable {Y : Type*} [Group Y] [Finite Y]

theorem sylow_le_normalizer_and_inf_ne_bot_of_isComponentOf (hY : HasAbelianSylowTwo Y)
    (S : Sylow 2 Y) {E K : Subgroup Y}
    (hSE : (S : Subgroup Y) ≤ Subgroup.normalizer (E : Set Y)) (hK : IsComponentOf K E) :
    (S : Subgroup Y) ≤ Subgroup.normalizer (K : Set Y) ∧ (S : Subgroup Y) ⊓ K ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set N := Subgroup.normalizer (E : Set Y) with hN
  have hEN : E ≤ N := Subgroup.le_normalizer
  have hKN : K ≤ N := hK.1.trans hEN
  set K' := K.subgroupOf N with hK'
  set E' := E.subgroupOf N with hE'
  have hE'n : E'.Normal := Subgroup.normal_in_normalizer
  have hK'E' : K' ≤ E' := fun x hx => hK.1 hx
  have hK'sn : K'.IsSubnormal := by
    have h1 : (K'.subgroupOf E').IsSubnormal := by
      have h2 := hK.2.1.comap (Subgroup.subgroupOfEquivOfLe hEN).toMonoidHom
      convert h2 using 1
      ext x
      exact Iff.rfl
    exact Subgroup.IsSubnormal.trans hK'E' h1 hE'n.isSubnormal
  have hK'q : GorensteinWalter.IsQuasisimple K' :=
    isQuasisimple_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKN).symm hK.2.2
  have hK'c : IsComponentOf K' ⊤ := ⟨le_top, hK'sn.subgroupOf, hK'q⟩
  set S' : Sylow 2 N := S.subtype hSE with hS'
  have h1 := sylow_le_normalizer_of_isComponentOf' (hY.subgroup N) S' hK'c
  have h2 := sylow_inf_ne_bot_of_isSubnormal S' hK'sn (IsQuasisimple.two_dvd_card hK'q)
  have hmemS' : ∀ x : N, x ∈ (S' : Subgroup N) ↔ (x : Y) ∈ (S : Subgroup Y) := fun x => by
    rw [hS', Sylow.coe_subtype, Subgroup.mem_subgroupOf]
  constructor
  · intro s hs
    have h3 := h1 ((hmemS' ⟨s, hSE hs⟩).mpr hs)
    rw [← Subgroup.subgroupOf_normalizer_eq hKN, Subgroup.mem_subgroupOf] at h3
    exact h3
  · obtain ⟨⟨x, hxS, hxK⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h2
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨(x : Y), (hmemS' x).mp hxS, hxK⟩, fun h => hx1 ?_⟩
    have hxY : (x : Y) = 1 := congrArg Subtype.val h
    have hx : x = 1 := Subtype.ext hxY
    exact Subtype.ext hx

end Normalized

section InnerSylow

variable {Y : Type} [Group Y] [Finite Y]

theorem exists_inner_mem_sylow_inf (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y) {L : Subgroup Y}
    (hL : IsComponentOf L ⊤) {s : Y} (hs : s ∈ (S : Subgroup Y)) :
    ∃ ℓ ∈ (S : Subgroup Y) ⊓ L, ∀ x ∈ L, s * x * s⁻¹ = ℓ * x * ℓ⁻¹ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hY S
  obtain ⟨k, hk, hkconj⟩ := exists_inner_of_isComponentOf hY S hL hs
  have hZodd : Odd (Nat.card (Subgroup.center L)) :=
    odd_card_center_of_isQuasisimple hL.2.2 (hY.subgroup L)
  have hSL : (S : Subgroup Y) ≤ Subgroup.normalizer (L : Set Y) :=
    sylow_le_normalizer_of_isComponentOf' hY S hL
  obtain ⟨a, ha⟩ := S.isPGroup'.exists_card_eq
  set n := 2 ^ a with hn
  have hcop : Nat.Coprime (Nat.card (Subgroup.center L)) n :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.mpr hZodd)
  have hpow : ∀ m : ℕ, ∀ x ∈ L, s ^ m * x * (s ^ m)⁻¹ = k ^ m * x * (k ^ m)⁻¹ := by
    intro m
    induction m with
    | zero => intro x _; simp
    | succ m ih =>
      intro x hx
      have hkx : k * x * k⁻¹ ∈ L := L.mul_mem (L.mul_mem hk hx) (L.inv_mem hk)
      calc s ^ (m + 1) * x * (s ^ (m + 1))⁻¹ = s ^ m * (s * x * s⁻¹) * (s ^ m)⁻¹ := by group
        _ = s ^ m * (k * x * k⁻¹) * (s ^ m)⁻¹ := by rw [hkconj x hx]
        _ = k ^ m * (k * x * k⁻¹) * (k ^ m)⁻¹ := ih _ hkx
        _ = k ^ (m + 1) * x * (k ^ (m + 1))⁻¹ := by group
  have hsn : s ^ n = 1 := by
    have h1 := pow_card_eq_one' (G := (S : Subgroup Y)) (x := ⟨s, hs⟩)
    rw [ha] at h1
    exact congrArg Subtype.val h1
  have hkn : k ^ n ∈ L := L.pow_mem hk n
  have hknZ : (⟨k ^ n, hkn⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h1 := hpow n y y.2
    rw [hsn, one_mul, inv_one, mul_one] at h1
    show (y : Y) * k ^ n = k ^ n * y
    calc (y : Y) * k ^ n = (k ^ n * y * (k ^ n)⁻¹) * k ^ n := by rw [← h1]
      _ = k ^ n * y := by group
  set z : Subgroup.center L := ⟨⟨k ^ n, hkn⟩, hknZ⟩ with hz
  set c : Subgroup.center L := (powCoprime hcop).symm z⁻¹ with hcdef
  have hc : c ^ n = z⁻¹ := by
    have h1 := (powCoprime hcop).apply_symm_apply z⁻¹
    rwa [powCoprime_apply] at h1
  have hcL : ((c : L) : Y) ∈ L := (c : L).2
  have hcomm : ∀ y ∈ L, ((c : L) : Y) * y = y * ((c : L) : Y) := fun y hy =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp c.2 ⟨y, hy⟩).symm)
  set ℓ : Y := k * ((c : L) : Y) with hℓdef
  have hℓL : ℓ ∈ L := L.mul_mem hk hcL
  have hℓconj : ∀ x ∈ L, s * x * s⁻¹ = ℓ * x * ℓ⁻¹ := by
    intro x hx
    rw [hkconj x hx]
    have h1 : ((c : L) : Y) * x * ((c : L) : Y)⁻¹ = x := by rw [hcomm x hx, mul_inv_cancel_right]
    calc k * x * k⁻¹ = k * (((c : L) : Y) * x * ((c : L) : Y)⁻¹) * k⁻¹ := by rw [h1]
      _ = ℓ * x * ℓ⁻¹ := by rw [hℓdef]; group
  have hℓn : ℓ ^ n = 1 := by
    have hkc : Commute k ((c : L) : Y) := (hcomm k hk).symm
    rw [hℓdef, hkc.mul_pow]
    have h1 : ((c : L) : Y) ^ n = (k ^ n)⁻¹ :=
      congrArg (fun w : Subgroup.center L => ((w : L) : Y)) hc
    rw [h1, mul_inv_cancel]
  have hℓS : ∀ y ∈ (S : Subgroup Y), y * ℓ * y⁻¹ = ℓ := by
    intro y hy
    have hyL : y * ℓ * y⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hSL hy) ℓ).mp hℓL
    set w := ℓ⁻¹ * (y * ℓ * y⁻¹) with hwdef
    have hwL : w ∈ L := L.mul_mem (L.inv_mem hℓL) hyL
    have hwZ : ∀ x ∈ L, w * x = x * w := by
      intro x hx
      have hyx : y⁻¹ * x * y ∈ L := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (hSL (S.toSubgroup.inv_mem hy)) x).mp hx
        simpa using h1
      have hys : y * s = s * y := setLike_mul_comm hy hs
      have h1 : (y * ℓ * y⁻¹) * x * (y * ℓ * y⁻¹)⁻¹ = ℓ * x * ℓ⁻¹ := by
        calc (y * ℓ * y⁻¹) * x * (y * ℓ * y⁻¹)⁻¹ = y * (ℓ * (y⁻¹ * x * y) * ℓ⁻¹) * y⁻¹ := by
              group
          _ = y * (s * (y⁻¹ * x * y) * s⁻¹) * y⁻¹ := by rw [hℓconj _ hyx]
          _ = (y * s * y⁻¹) * x * (y * s * y⁻¹)⁻¹ := by group
          _ = s * x * s⁻¹ := by rw [hys, mul_inv_cancel_right]
          _ = ℓ * x * ℓ⁻¹ := hℓconj x hx
      calc w * x = ℓ⁻¹ * ((y * ℓ * y⁻¹) * x * (y * ℓ * y⁻¹)⁻¹) * (y * ℓ * y⁻¹) := by
            rw [hwdef]; group
        _ = ℓ⁻¹ * (ℓ * x * ℓ⁻¹) * (y * ℓ * y⁻¹) := by rw [h1]
        _ = x * w := by rw [hwdef]; group
    have hwn : w ^ n = 1 := by
      have h1 : (y * ℓ * y⁻¹) ^ n = 1 := by rw [conj_pow, hℓn, mul_one, mul_inv_cancel]
      have h2 : y * ℓ * y⁻¹ = ℓ * w := by rw [hwdef]; group
      have hcomm' : Commute ℓ w := (hwZ ℓ hℓL).symm
      rw [h2, hcomm'.mul_pow, hℓn, one_mul] at h1
      exact h1
    have hwZ' : (⟨w, hwL⟩ : L) ∈ Subgroup.center L :=
      Subgroup.mem_center_iff.mpr fun x => Subtype.ext (hwZ x x.2).symm
    have hw1 : w = 1 := by
      have hdvd1 : orderOf (⟨⟨w, hwL⟩, hwZ'⟩ : Subgroup.center L) ∣ n :=
        orderOf_dvd_of_pow_eq_one (Subtype.ext (Subtype.ext (by simpa using hwn)))
      have hdvd2 := orderOf_dvd_natCard (⟨⟨w, hwL⟩, hwZ'⟩ : Subgroup.center L)
      have h1 := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hdvd2 hcop) hdvd1
      have h2 := orderOf_eq_one_iff.mp h1
      exact congrArg (fun v : Subgroup.center L => ((v : L) : Y)) h2
    calc y * ℓ * y⁻¹ = ℓ * w := by rw [hwdef]; group
      _ = ℓ := by rw [hw1, mul_one]
  have hℓS' : ℓ ∈ (S : Subgroup Y) := by
    have hℓp : IsPGroup 2 (Subgroup.zpowers ℓ) := by
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hℓn)
      exact IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    have hℓN : Subgroup.zpowers ℓ ≤ Subgroup.normalizer ((S : Subgroup Y) : Set Y) := by
      rw [Subgroup.zpowers_le]
      apply Subgroup.centralizer_le_normalizer
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      calc y * ℓ = (y * ℓ * y⁻¹) * y := by group
        _ = ℓ * y := by rw [hℓS y hy]
    have hsup := S.is_maximal' (hℓp.to_sup_of_normal_right' S.isPGroup' hℓN) le_sup_right
    rw [← hsup]
    exact le_sup_left (a := Subgroup.zpowers ℓ) (Subgroup.mem_zpowers ℓ)
  exact ⟨ℓ, ⟨hℓS', hℓL⟩, hℓconj⟩

theorem exists_mem_iSup_sylow_inf_conj_eq (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y) {s : Y}
    (hs : s ∈ (S : Subgroup Y)) :
    ∃ e ∈ ⨆ (L : Subgroup Y) (_ : IsComponentOf L ⊤), (S : Subgroup Y) ⊓ L,
      ∀ L : Subgroup Y, IsComponentOf L ⊤ → ∀ x ∈ L, e * x * e⁻¹ = s * x * s⁻¹ := by
  classical
  have hfin : Set.Finite {K : Subgroup Y | IsComponentOf K ⊤} := Set.toFinite _
  suffices h : ∀ F : Finset (Subgroup Y), (∀ K ∈ F, IsComponentOf K ⊤) →
      ∃ e ∈ (⨆ K ∈ F, (S : Subgroup Y) ⊓ K), ∀ K ∈ F, ∀ x ∈ K, e * x * e⁻¹ = s * x * s⁻¹ by
    obtain ⟨e, he, hconj⟩ := h hfin.toFinset (fun K hK => hfin.mem_toFinset.mp hK)
    refine ⟨e, ?_, fun K hK => hconj K (hfin.mem_toFinset.mpr hK)⟩
    have hle : (⨆ K ∈ hfin.toFinset, (S : Subgroup Y) ⊓ K) ≤
        ⨆ (L : Subgroup Y) (_ : IsComponentOf L ⊤), (S : Subgroup Y) ⊓ L :=
      iSup₂_le fun K hK => le_iSup₂_of_le
        (f := fun (L : Subgroup Y) (_ : IsComponentOf L ⊤) => (S : Subgroup Y) ⊓ L) K
        (hfin.mem_toFinset.mp hK) le_rfl
    exact hle he
  intro F
  induction F using Finset.induction_on with
  | empty =>
    intro _
    exact ⟨1, one_mem _, fun K hK => absurd hK (Finset.notMem_empty K)⟩
  | insert K₀ F hK₀F ih =>
    intro hF
    obtain ⟨e', he', hconj'⟩ := ih (fun K hK => hF K (Finset.mem_insert_of_mem hK))
    have hK₀ := hF K₀ (Finset.mem_insert_self K₀ F)
    obtain ⟨k₀, hk₀, hk₀conj⟩ := exists_inner_mem_sylow_inf hY S hK₀ hs
    have hcommF : ∀ K ∈ F, (S : Subgroup Y) ⊓ K ≤ Subgroup.centralizer (K₀ : Set Y) := by
      intro K hK
      refine inf_le_right.trans ?_
      rcases CFSG.LocalCores.distinct_components_commute
          ((isComponent_iff_isComponentOf_top K).mpr (hF K (Finset.mem_insert_of_mem hK)))
          ((isComponent_iff_isComponentOf_top K₀).mpr hK₀) with h | h
      · exact absurd (h ▸ hK) hK₀F
      · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have he'C : e' ∈ Subgroup.centralizer (K₀ : Set Y) := (iSup₂_le hcommF) he'
    refine ⟨e' * k₀, ?_, ?_⟩
    · apply mul_mem
      · have hle : (⨆ K ∈ F, (S : Subgroup Y) ⊓ K) ≤ (⨆ K ∈ insert K₀ F, (S : Subgroup Y) ⊓ K) :=
          iSup₂_le fun K hK => le_iSup₂ (f := fun K (_ : K ∈ insert K₀ F) => (S : Subgroup Y) ⊓ K)
            K (Finset.mem_insert_of_mem hK)
        exact hle he'
      · exact (le_iSup₂ (f := fun K (_ : K ∈ insert K₀ F) => (S : Subgroup Y) ⊓ K) K₀
          (Finset.mem_insert_self K₀ F)) hk₀
    · intro K hK x hx
      rcases Finset.mem_insert.mp hK with rfl | hKF
      · rw [hk₀conj x hx]
        have hy : k₀ * x * k₀⁻¹ ∈ K := mul_mem (mul_mem hk₀.2 hx) (inv_mem hk₀.2)
        have hc := (Subgroup.mem_centralizer_iff.mp he'C) _ hy
        calc e' * k₀ * x * (e' * k₀)⁻¹ = e' * (k₀ * x * k₀⁻¹) * e'⁻¹ := by group
          _ = k₀ * x * k₀⁻¹ := by rw [← hc, mul_inv_cancel_right]
      · have hxC : x ∈ Subgroup.centralizer (K₀ : Set Y) := by
          rcases CFSG.LocalCores.distinct_components_commute
              ((isComponent_iff_isComponentOf_top K).mpr (hF K (Finset.mem_insert_of_mem hKF)))
              ((isComponent_iff_isComponentOf_top K₀).mpr hK₀) with h | h
          · exact absurd (h ▸ hKF) hK₀F
          · exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h hx
        have hc := (Subgroup.mem_centralizer_iff.mp hxC) k₀ hk₀.2
        calc e' * k₀ * x * (e' * k₀)⁻¹ = e' * (k₀ * x * k₀⁻¹) * e'⁻¹ := by group
          _ = e' * x * e'⁻¹ := by rw [hc, mul_inv_cancel_right]
          _ = s * x * s⁻¹ := hconj' K hKF x hx

theorem exists_component_not_le_centralizer (hY : HasAbelianSylowTwo Y) (S : Sylow 2 Y)
    {K : Subgroup Y} (hKE : K ≤ componentLayerOf (⊤ : Subgroup Y))
    (hKodd : Odd (Nat.card (Subgroup.center K))) (hSK : (S : Subgroup Y) ⊓ K ≠ ⊥) :
    ∃ L : Subgroup Y, IsComponentOf L ⊤ ∧
      ¬ K ≤ Subgroup.centralizer (((S : Subgroup Y) ⊓ L : Subgroup Y) : Set Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra h
  push Not at h
  obtain ⟨⟨x, hxS, hxK⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hSK
  have hx1' : x ≠ 1 := fun h' => hx1 (Subtype.ext h')
  obtain ⟨e, he, hconj⟩ := exists_mem_iSup_sylow_inf_conj_eq hY S hxS
  have heK : e ∈ Subgroup.centralizer (K : Set Y) := by
    have hle : (⨆ (L : Subgroup Y) (_ : IsComponentOf L ⊤), (S : Subgroup Y) ⊓ L) ≤
        Subgroup.centralizer (K : Set Y) := iSup₂_le fun L hL => by
      rw [← Subgroup.le_centralizer_iff]
      exact h L hL
    exact hle he
  have hcK : e⁻¹ * x ∈ Subgroup.centralizer (K : Set Y) := by
    have hle : componentLayerOf (⊤ : Subgroup Y) ≤ Subgroup.centralizer ({e⁻¹ * x} : Set Y) := by
      refine sSup_le fun L hL y hy => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h1 := hconj L hL y hy
      calc y * (e⁻¹ * x) = e⁻¹ * (e * y * e⁻¹) * x := by group
        _ = e⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
        _ = e⁻¹ * x * y := by group
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (hKE hy))
  have hxC : x ∈ Subgroup.centralizer (K : Set Y) := by
    have : x = e * (e⁻¹ * x) := by group
    rw [this]
    exact mul_mem heK hcK
  have hxZ : (⟨x, hxK⟩ : K) ∈ Subgroup.center K :=
    Subgroup.mem_center_iff.mpr fun y => Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp S.isPGroup') ⟨x, hxS⟩
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hx1' (congrArg Subtype.val hj)
  have h2 : 2 ∣ orderOf (⟨⟨x, hxK⟩, hxZ⟩ : Subgroup.center K) := by
    rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
    rw [Subgroup.orderOf_mk] at hj
    rw [hj]
    exact dvd_pow_self 2 hj0
  exact (Nat.not_even_iff_odd.mpr hKodd) (even_iff_two_dvd.mpr (h2.trans (orderOf_dvd_natCard _)))

end InnerSylow

theorem le_of_not_le_centralizer {Y : Type*} [Group Y] {K L A : Subgroup Y}
    (hK : GorensteinWalter.IsQuasisimple K) (hKL : K ≤ Subgroup.normalizer (L : Set Y))
    (hAL : A ≤ L) (hAK : A ≤ Subgroup.normalizer (K : Set Y))
    (h : ¬ K ≤ Subgroup.centralizer (A : Set Y)) : K ≤ L := by
  have hKq : CFSG.IsQuasisimple K :=
    ⟨Group.isPerfect_def.mpr hK.2.1, hK.2.2, IsQuasisimple.exists_mul_ne_mul hK⟩
  have hN : (L.subgroupOf K).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hKL g.2) n).mp hn⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hKq hN with h1 | h1
  · intro x hx
    have : (⟨x, hx⟩ : K) ∈ L.subgroupOf K := h1 ▸ Subgroup.mem_top _
    exact this
  · exfalso
    apply h
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
    have hcomm : ⁅K, A⁆ ≤ K ⊓ L := by
      rw [Subgroup.commutator_le]
      intro k hk a ha
      rw [commutatorElement_def]
      refine ⟨?_, ?_⟩
      · have h2 : a * k⁻¹ * a⁻¹ ∈ K :=
          (Subgroup.mem_normalizer_iff.mp (hAK ha) k⁻¹).mp (K.inv_mem hk)
        have : k * a * k⁻¹ * a⁻¹ = k * (a * k⁻¹ * a⁻¹) := by group
        rw [this]
        exact K.mul_mem hk h2
      · have h2 : k * a * k⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (hKL hk) a).mp (hAL ha)
        exact L.mul_mem h2 (L.inv_mem (hAL ha))
    apply CFSG.LocalCores.perfect_double_commutator (Group.isPerfect_def.mpr hK.2.1)
    rw [← le_bot_iff, Subgroup.commutator_le]
    intro c hc k hk
    have hcK : c ∈ K := (hcomm hc).1
    have hcZ : (⟨c, hcK⟩ : K) ∈ Subgroup.center K := h1 (hcomm hc).2
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hcZ ⟨k, hk⟩).symm

theorem map_subgroupMap_subgroupOf {G H : Type*} [Group G] [Group H] (f : G →* H)
    {K E : Subgroup G} (hKE : K ≤ E) :
    (K.subgroupOf E).map (f.subgroupMap E) = (K.map f).subgroupOf (E.map f) := by
  ext ⟨y, hy⟩
  rw [Subgroup.mem_subgroupOf]
  constructor
  · rintro ⟨⟨x, hxE⟩, hxK, hxy⟩
    refine ⟨x, hxK, ?_⟩
    have := congrArg Subtype.val hxy
    exact this
  · rintro ⟨x, hxK, hxy⟩
    refine ⟨⟨x, hKE hxK⟩, hxK, ?_⟩
    apply Subtype.ext
    exact hxy

theorem IsTypeJR.isTypeL2Odd_of_isSubnormal {G : Type} [Group G] [Finite G] (hG : IsTypeJR G)
    {u : G} (hu : orderOf u = 2) {A B : Subgroup G}
    (hAC : A ≤ Subgroup.centralizer ({u} : Set G))
    (hCA : Subgroup.centralizer ({u} : Set G) ≤ Subgroup.normalizer (A : Set G))
    (hBA : B ≤ A) (hBq : GorensteinWalter.IsQuasisimple B) (hBsn : (B.subgroupOf A).IsSubnormal) :
    IsTypeL2Odd B ∧ Subgroup.center B = ⊥ := by
  set C := Subgroup.centralizer ({u} : Set G) with hCdef
  obtain ⟨-, p, f, hp, M, hpodd, hf, h5, hMC, hMn, ⟨eM⟩, hCM⟩ := hG.2.2 u hu
  have h8 := hG.mod_eight hu M hpodd hf h5 hMC hMn eM hCM
  have hcardF : 4 ≤ Nat.card (GaloisField p f) := by rw [GaloisField.card p f hf.ne']; omega
  have : IsSimpleGroup PSL(2, GaloisField p f) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple hcardF
  have : IsSimpleGroup M := eM.isSimpleGroup
  have hMnab : ∃ a b : M, a * b ≠ b * a := exists_mul_ne_mul_of_mulEquiv_psl2 hcardF eM
  obtain ⟨b₁, b₂, hb12⟩ := exists_mul_ne_mul_of_isQuasisimple hBq
  have hBM : ¬ B ≤ Subgroup.centralizer (M : Set G) := by
    intro h
    have hle : B ≤ Subgroup.zpowers u := by
      rw [← hCM]
      exact le_inf (hBA.trans hAC) h
    apply hb12
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hle b₁.2)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp (hle b₂.2)
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
  have hMnormC : C ≤ Subgroup.normalizer (M : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMC).mp hMn
  have hMA : M ≤ A := by
    have hMCc : CFSG.IsComponent (M.subgroupOf C) := by
      refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMC).symm
        (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hMnab).1, hMn.isSubnormal⟩
    have hACn : (A.subgroupOf C).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hAC).mpr hCA
    rcases CFSG.LocalCores.component_normal_subgroup hMCc hACn with h | h
    · exact CFSG.LocalCores.le_of_subgroupOf_le hMC h
    · exfalso
      apply hBM
      have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hMC h
      rw [inf_eq_left.mpr hAC] at h1
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 hm
      exact (Subgroup.mem_centralizer_iff.mp h2 x (hBA hx)).symm
  set B' := B.subgroupOf A with hB'
  set M' := M.subgroupOf A with hM'
  have hB'c : CFSG.IsComponent B' := by
    refine ⟨?_, hBsn⟩
    have h1 : CFSG.IsQuasisimple B :=
      ⟨Group.isPerfect_def.mpr hBq.2.1, hBq.2.2, IsQuasisimple.exists_mul_ne_mul hBq⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hBA).symm h1
  have hM'n : M'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMA).mpr (hAC.trans hMnormC)
  have hM'c : CFSG.IsComponent M' := by
    refine ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hMA).symm
      (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hMnab).1, hM'n.isSubnormal⟩
  have hBM' : ⁅B', M'⁆ ≠ ⊥ := by
    intro h
    apply hBM
    have h1 := CFSG.LocalCores.commutator_inf_eq_bot_of_subgroupOf hBA h
    rw [inf_eq_left.mpr hMA] at h1
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1
  have hBMeq : B = M := by
    apply le_antisymm
    · rcases CFSG.LocalCores.component_normal_subgroup hB'c hM'n with h | h
      · exact CFSG.LocalCores.le_of_subgroupOf_le hBA h
      · exact absurd h hBM'
    · rcases CFSG.LocalCores.component_subnormal_subgroup hM'c hBsn with h | h
      · exact CFSG.LocalCores.le_of_subgroupOf_le hMA h
      · exact absurd (by rw [Subgroup.commutator_comm]; exact h) hBM'
  subst hBMeq
  exact ⟨⟨p, f, hp, hpodd, hf, h5, h8, ⟨eM⟩⟩, center_eq_bot_of_isSimpleGroup hMnab⟩

theorem bender1970_2_3 {X : Type} [Group X] [Finite X] (hX : IsAStar X) {t : X}
    (ht : orderOf t = 2) {E : Subgroup X} (hEX : E ≤ componentLayerOf (⊤ : Subgroup X))
    (hEt : Subgroup.centralizer ({t} : Set X) ≤ Subgroup.normalizer (E : Set X))
    {K : Subgroup X} (hK : IsComponentOf K E) :
    ∃ L : Subgroup X, IsComponentOf L ⊤ ∧ K ≤ L ∧
      (K = L ∨ (IsTypeL2Odd (K ⧸ Subgroup.center K) ∧ IsTypeJR (L ⧸ Subgroup.center L) ∧
        K ≤ Subgroup.centralizer ({t} : Set X))) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY := hX.1
  have ht2 : t * t = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have htp : IsPGroup 2 (Subgroup.zpowers t) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht, pow_one])
  obtain ⟨T, hT⟩ := htp.exists_le_sylow
  have htT : t ∈ (T : Subgroup X) := hT (Subgroup.mem_zpowers t)
  have hTab := hY T
  have hTC : (T : Subgroup X) ≤ Subgroup.centralizer ({t} : Set X) := fun s hs =>
    Subgroup.mem_centralizer_singleton_iff.mpr (setLike_mul_comm hs htT)
  obtain ⟨hTK, hTKne⟩ :=
    sylow_le_normalizer_and_inf_ne_bot_of_isComponentOf hY T (hTC.trans hEt) hK
  have hKodd := odd_card_center_of_isQuasisimple hK.2.2 (hY.subgroup K)
  have hKX : K ≤ componentLayerOf (⊤ : Subgroup X) := hK.1.trans hEX
  obtain ⟨L, hL, hKL'⟩ := exists_component_not_le_centralizer hY T hKX hKodd hTKne
  have hKL : K ≤ L := le_of_not_le_centralizer hK.2.2
    (hKX.trans (componentLayerOf_top_le_normalizer hL)) inf_le_right (inf_le_left.trans hTK)
    hKL'
  refine ⟨L, hL, hKL, ?_⟩
  by_cases hKeqL : K = L
  · exact Or.inl hKeqL
  right
  have hLq : CFSG.IsQuasisimple L := ((isComponent_iff_isComponentOf_top L).mpr hL).1
  obtain ⟨k₁, k₂, hk12⟩ := exists_mul_ne_mul_of_isQuasisimple hK.2.2
  set ZL := Subgroup.center L with hZL
  have hKZ : ¬ K.subgroupOf L ≤ ZL := by
    intro h
    apply hk12
    have h1 : (⟨k₁, hKL k₁.2⟩ : L) ∈ ZL := h k₁.2
    exact Subtype.ext (congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 ⟨k₂, hKL k₂.2⟩)).symm
  have hKEL : K.subgroupOf L ≤ E.subgroupOf L := fun x hx => hK.1 hx
  have hLE : ¬ L ≤ E := by
    intro hLE
    have hKsnL : (K.subgroupOf L).IsSubnormal := by
      have h1 := hK.2.1.comap (Subgroup.inclusion hLE)
      convert h1 using 1
      ext x
      exact Iff.rfl
    have hLc : CFSG.IsComponent (⊤ : Subgroup L) :=
      ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hLq,
        Subgroup.IsSubnormal.top⟩
    rcases CFSG.LocalCores.component_subnormal_subgroup hLc hKsnL with h1 | h1
    · exact hKeqL (le_antisymm hKL fun x hx => h1 (Subgroup.mem_top ⟨x, hx⟩))
    · apply hKZ
      intro x hx
      rw [Subgroup.mem_center_iff]
      intro y
      have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h1 (Subgroup.mem_top y)
      exact (Subgroup.mem_centralizer_iff.mp h2 x hx).symm
  obtain ⟨ℓ, hℓ, hℓconj⟩ := exists_inner_of_isComponentOf hY T hL htT
  set π : L →* L ⧸ ZL := QuotientGroup.mk' ZL with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective ZL
  have hZLodd : Odd (Nat.card ZL) := odd_card_center_of_isQuasisimple hL.2.2 (hY.subgroup L)
  set u : L ⧸ ZL := π ⟨ℓ, hℓ⟩ with hu
  have hlift : ∀ x : L, (x : X) ∈ Subgroup.centralizer ({t} : Set X) ↔
      π x ∈ Subgroup.centralizer ({u} : Set (L ⧸ ZL)) := fun x =>
    mem_centralizer_iff_of_inner hZLodd ht2 hℓ hℓconj x
  have hLt : ¬ L ≤ Subgroup.centralizer ({t} : Set X) := by
    intro hLt
    have hN : (E.subgroupOf L).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      exact (Subgroup.mem_normalizer_iff.mp (hEt (hLt g.2)) n).mp hn⟩
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq hN with h1 | h1
    · apply hLE
      intro x hx
      have h2 : (⟨x, hx⟩ : L) ∈ E.subgroupOf L := by rw [h1]; exact Subgroup.mem_top _
      exact h2
    · exact hKZ (hKEL.trans h1)
  have hu2 : orderOf u = 2 := orderOf_mk_eq_two_of_inner ht2 hℓ hℓconj hLt
  set A : Subgroup (L ⧸ ZL) := (E.subgroupOf L).map π with hA
  have hCN : Subgroup.centralizer ({u} : Set (L ⧸ ZL)) ≤
      Subgroup.normalizer (A : Set (L ⧸ ZL)) := by
    have key : ∀ y : L, (y : X) ∈ Subgroup.normalizer (E : Set X) → ∀ w ∈ A,
        π y * w * (π y)⁻¹ ∈ A := by
      rintro y hy _ ⟨a, ha, rfl⟩
      refine ⟨y * a * y⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
      have ha' : (a : X) ∈ E := ha
      show ((y * a * y⁻¹ : L) : X) ∈ E
      rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp hy a).mp ha'
    intro v hv
    obtain ⟨y, rfl⟩ := hπs v
    have hyE : (y : X) ∈ Subgroup.normalizer (E : Set X) := hEt ((hlift y).mpr hv)
    have hyE' : ((y⁻¹ : L) : X) ∈ Subgroup.normalizer (E : Set X) := by
      rw [Subgroup.coe_inv]
      exact (Subgroup.normalizer (E : Set X)).inv_mem hyE
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨key y hyE w, fun hw => ?_⟩
    have h1 := key y⁻¹ hyE' _ hw
    rw [map_inv, inv_inv] at h1
    simpa [mul_assoc] using h1
  have hNA : Subgroup.normalizer (A : Set (L ⧸ ZL)) ≠ ⊤ := by
    intro htop
    have hAn : A.Normal := Subgroup.normalizer_eq_top_iff.mp htop
    have : IsSimpleGroup (L ⧸ ZL) := hL.2.2.2.2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal A with h1 | h1
    · apply hKZ
      refine hKEL.trans ?_
      have h2 := (Subgroup.map_eq_bot_iff _).mp h1
      rwa [hπ, QuotientGroup.ker_mk'] at h2
    · apply hLE
      have h2 : E.subgroupOf L ⊔ ZL = ⊤ := by
        have h3 := congrArg (Subgroup.comap π) h1
        rwa [Subgroup.comap_map_eq, Subgroup.comap_top, hπ, QuotientGroup.ker_mk'] at h3
      have h3 := eq_top_of_sup_center_eq_top hL.2.2.2.1 h2
      intro x hx
      have h4 : (⟨x, hx⟩ : L) ∈ E.subgroupOf L := by rw [h3]; exact Subgroup.mem_top _
      exact h4
  set Kb : Subgroup (L ⧸ ZL) := (K.subgroupOf L).map π with hKb
  have hKbA : Kb ≤ A := Subgroup.map_mono hKEL
  have hKbne : Kb ≠ ⊥ := by
    intro h
    apply hKZ
    have h2 := (Subgroup.map_eq_bot_iff _).mp h
    rwa [hπ, QuotientGroup.ker_mk'] at h2
  have hKLq : GorensteinWalter.IsQuasisimple (K.subgroupOf L) :=
    isQuasisimple_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKL).symm hK.2.2
  have hKbperf : Group.IsPerfect Kb := by
    have : Group.IsPerfect (K.subgroupOf L) := Group.isPerfect_def.mpr hKLq.2.1
    exact Group.IsPerfect.map π
  rcases hX.isTypeL2_or_isTypeJR hL with hL2 | hJR
  ·
    exfalso
    have hsolv := hL2.isSolvable_of_centralizer_le hu2 hCN hNA
    have hKbN : Kb ≤ Subgroup.normalizer (A : Set (L ⧸ ZL)) := hKbA.trans A.le_normalizer
    have : Group.IsSolvable Kb :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hKbN)
    have : Nontrivial Kb := (Subgroup.nontrivial_iff_ne_bot Kb).mpr hKbne
    exact Group.IsPerfect.not_isSolvable Kb inferInstance
  ·
    have hmax := (hJR.2.2 u hu2).1
    have hNC : Subgroup.normalizer (A : Set (L ⧸ ZL)) =
        Subgroup.centralizer ({u} : Set (L ⧸ ZL)) := (hmax.le_iff.mp hCN).resolve_left hNA
    have hAC : A ≤ Subgroup.centralizer ({u} : Set (L ⧸ ZL)) := hNC ▸ A.le_normalizer
    have hKt : K ≤ Subgroup.centralizer ({t} : Set X) := fun k hk =>
      (hlift ⟨k, hKL hk⟩).mpr (hAC ⟨⟨k, hKL hk⟩, hK.1 hk, rfl⟩)
    refine ⟨?_, hJR, hKt⟩
    have hKbq : GorensteinWalter.IsQuasisimple Kb := by
      have h1 : CFSG.IsQuasisimple (K.subgroupOf L) :=
        ⟨Group.isPerfect_def.mpr hKLq.2.1, hKLq.2.2, IsQuasisimple.exists_mul_ne_mul hKLq⟩
      have h2 : ¬ K.subgroupOf L ≤ π.ker := by rw [hπ, QuotientGroup.ker_mk']; exact hKZ
      have h3 := CFSG.LocalCores.isQuasisimple_map h1 π h2
      exact ⟨CFSG.LocalCores.isQuasisimple_nontrivial h3, Group.isPerfect_def.mp h3.1, h3.2.1⟩
    have hKbsn : (Kb.subgroupOf A).IsSubnormal := by
      have h1 : ((K.subgroupOf L).subgroupOf (E.subgroupOf L)).IsSubnormal := by
        let ψ : (E.subgroupOf L) →* E :=
          { toFun := fun x => ⟨((x : L) : X), x.2⟩
            map_one' := rfl
            map_mul' := fun _ _ => rfl }
        have h2 := hK.2.1.comap ψ
        convert h2 using 1
        ext x
        exact Iff.rfl
      have h2 := h1.map (π.subgroupMap_surjective (E.subgroupOf L))
      rwa [map_subgroupMap_subgroupOf π hKEL] at h2
    obtain ⟨hKbtype, hKbZ⟩ := hJR.isTypeL2Odd_of_isSubnormal hu2 hAC (hNC ▸ le_rfl) hKbA hKbq hKbsn
    let φ : K →* Kb := (π.comp (Subgroup.inclusion hKL)).codRestrict Kb
      (fun x => ⟨Subgroup.inclusion hKL x, x.2, rfl⟩)
    have hφ : Function.Surjective φ := by
      rintro ⟨_, ⟨z, hz, rfl⟩⟩
      exact ⟨⟨(z : X), hz⟩, rfl⟩
    have hker : φ.ker = Subgroup.center K := by
      apply le_antisymm
      · intro x hx
        have h1 : Subgroup.inclusion hKL x ∈ ZL := by
          have h2 : π (Subgroup.inclusion hKL x) = 1 := congrArg Subtype.val hx
          rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
        rw [Subgroup.mem_center_iff]
        intro y
        have h2 := congrArg Subtype.val (Subgroup.mem_center_iff.mp h1 (Subgroup.inclusion hKL y))
        exact Subtype.ext h2
      · intro z hz
        have h1 : φ z ∈ Subgroup.center Kb := Subgroup.map_center_le_center hφ ⟨z, hz, rfl⟩
        rw [hKbZ, Subgroup.mem_bot] at h1
        exact h1
    let e : K ⧸ Subgroup.center K ≃* Kb :=
      (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
    obtain ⟨p, f, hp, h1, h2, h3, h4, ⟨e'⟩⟩ := hKbtype
    exact ⟨p, f, hp, h1, h2, h3, h4, ⟨e.trans e'⟩⟩

section Subgroup

variable {G : Type*} [Group G]

theorem isComponentOf_map_subtype {H : Subgroup G} {L : Subgroup H} (hL : IsComponentOf L ⊤) :
    IsComponentOf (L.map H.subtype) H := by
  refine ⟨Subgroup.map_subtype_le L, ?_, ?_⟩
  · have h1 : ((L.map H.subtype).subgroupOf H) = L :=
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective L
    rw [h1]
    exact Subgroup.IsSubnormal.trans le_top hL.2.1 Subgroup.IsSubnormal.top
  · exact isQuasisimple_of_mulEquiv' (L.equivMapOfInjective H.subtype H.subtype_injective) hL.2.2

noncomputable def subgroupOfQuotientCenterEquiv {H K : Subgroup G} (hKH : K ≤ H) :
    K.subgroupOf H ⧸ Subgroup.center (K.subgroupOf H) ≃* K ⧸ Subgroup.center K :=
  QuotientGroup.congr _ _ (Subgroup.subgroupOfEquivOfLe hKH)
    (Subgroup.map_center_eq (Subgroup.subgroupOfEquivOfLe hKH))

end Subgroup

theorem bender1970_2_3_subgroup {G : Type} [Group G] [Finite G] {H : Subgroup G}
    (hH : IsAStar H) {t : G} (htH : t ∈ H) (ht : orderOf t = 2) {E : Subgroup G}
    (hEX : E ≤ componentLayerOf H)
    (hEt : H ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (E : Set G))
    {K : Subgroup G} (hK : IsComponentOf K E) :
    ∃ L : Subgroup G, IsComponentOf L H ∧ K ≤ L ∧
      (K = L ∨ (IsTypeL2Odd (K ⧸ Subgroup.center K) ∧ IsTypeJR (L ⧸ Subgroup.center L) ∧
        K ≤ Subgroup.centralizer ({t} : Set G))) := by
  have hEH : E ≤ H := hEX.trans (componentLayerOf_isNormalIn H).1
  have hKH : K ≤ H := hK.1.trans hEH
  set t' : H := ⟨t, htH⟩
  set E' := E.subgroupOf H
  set K' := K.subgroupOf H
  have ht' : orderOf t' = 2 := by rw [Subgroup.orderOf_mk]; exact ht
  have hEX' : E' ≤ componentLayerOf (⊤ : Subgroup H) := by
    intro x hx
    have hx' : (x : G) ∈ (componentLayerOf (⊤ : Subgroup H)).map H.subtype := by
      rw [componentLayerOf_subgroup_top_eq]
      exact hEX hx
    obtain ⟨y, hy, hyx⟩ := hx'
    have : y = x := Subtype.ext hyx
    rwa [← this]
  have hEt' : Subgroup.centralizer ({t'} : Set H) ≤ Subgroup.normalizer (E' : Set H) := by
    intro x hx
    rw [← Subgroup.subgroupOf_normalizer_eq hEH, Subgroup.mem_subgroupOf]
    apply hEt
    refine ⟨x.2, ?_⟩
    show (x : G) ∈ Subgroup.centralizer ({t} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    exact congrArg Subtype.val hx
  have hK' : IsComponentOf K' E' := by
    refine ⟨fun x hx => hK.1 hx, ?_, ?_⟩
    · have h1 := hK.2.1.comap ((Subgroup.subgroupOfEquivOfLe hEH).toMonoidHom)
      convert h1 using 1
      ext x
      exact Iff.rfl
    · exact isQuasisimple_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hKH).symm hK.2.2
  obtain ⟨L', hL', hKL', hcase⟩ := bender1970_2_3 hH ht' hEX' hEt' hK'
  set L := L'.map H.subtype
  have hK'map : K'.map H.subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hKH]
  have hKL : K ≤ L := hK'map ▸ Subgroup.map_mono hKL'
  refine ⟨L, isComponentOf_map_subtype hL', hKL, ?_⟩
  rcases hcase with h | ⟨h1, h2, h3⟩
  · left
    rw [← hK'map, h]
  · right
    refine ⟨?_, ?_, ?_⟩
    · obtain ⟨p, f, hp, a1, a2, a3, a4, ⟨e⟩⟩ := h1
      exact ⟨p, f, hp, a1, a2, a3, a4, ⟨(subgroupOfQuotientCenterEquiv hKH).symm.trans e⟩⟩
    · have e : L' ≃* L := L'.equivMapOfInjective H.subtype H.subtype_injective
      exact h2.of_mulEquiv (QuotientGroup.congr _ _ e (Subgroup.map_center_eq e))
    · intro x hx
      have h4 := h3 (show (⟨x, hKH hx⟩ : H) ∈ K' from hx)
      rw [Subgroup.mem_centralizer_singleton_iff] at h4 ⊢
      exact congrArg Subtype.val h4

end CFSG.Walter
