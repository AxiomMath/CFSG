module

public import CFSG.RankThree.S4Free.StellmacherThmAGenStep
public import CFSG.RankThree.S4Free.StellmacherHosts
public import CFSG.Open.Defs
import CFSG.RankThree.S4Free.StellmacherThmAGenSz
import CFSG.LocalAnalysis.ComponentClassification.GeneralizedFitting
import CFSG.Quasithin.Background.B1MoreNineA
import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Aux

public section

open scoped IsMulCommutative

namespace CFSG.RankThree.S4Free.Stell

open CFSG.Quasithin

theorem card_sup_of_commute_of_inf_eq_bot {G : Type*} [Group G] {U W : Subgroup G}
    (hUW : ∀ u ∈ U, ∀ w ∈ W, Commute u w) (hinf : U ⊓ W = ⊥) :
    Nat.card ↥(U ⊔ W) = Nat.card U * Nat.card W := by
  let f := MonoidHom.noncommCoprod U.subtype W.subtype (fun u w => hUW u u.2 w w.2)
  have hinj : Function.Injective f := (MonoidHom.noncommCoprod_injective _ _ _).mpr
    ⟨U.subtype_injective, W.subtype_injective, by
      rw [Subgroup.range_subtype, Subgroup.range_subtype, disjoint_iff]
      exact hinf⟩
  have hrange : f.range = U ⊔ W := by
    rw [show f.range = U.subtype.range ⊔ W.subtype.range from
      MonoidHom.noncommCoprod_range _ _ _, Subgroup.range_subtype, Subgroup.range_subtype]
  rw [← hrange, ← SetLike.coe_sort_coe, MonoidHom.coe_range, Nat.card_range_of_injective hinj,
    Nat.card_prod]

@[expose] def SzComponents (G : Type*) [Group G] : Prop :=
  ∀ L : Subgroup G, CFSG.Open.IsComponentOf L ⊤ → ∃ a : ℕ, 1 ≤ a ∧
    ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
      Nonempty (L ⧸ Subgroup.center L ≃* CFSG.Blueprint.suzukiGroup a K)

variable {V : Type*} [CommGroup V] [Finite V]

@[expose] def IsCompOf (H M : Subgroup (MulAut V)) : Prop :=
  ∃ L : Subgroup H, CFSG.Open.IsComponentOf L ⊤ ∧ L.map H.subtype = M

namespace IsCompOf

variable {H M : Subgroup (MulAut V)}

theorem le (hM : IsCompOf H M) : M ≤ H := by
  obtain ⟨L, -, rfl⟩ := hM
  exact Subgroup.map_subtype_le L

theorem conj (hM : IsCompOf H M) {b : MulAut V} (hb : b ∈ H) :
    IsCompOf H (M.map (MulAut.conj b).toMonoidHom) := by
  obtain ⟨L, hL, rfl⟩ := hM
  refine ⟨L.map (MulAut.conj (⟨b, hb⟩ : H)).toMonoidHom,
    (CFSG.ComponentClassification.LocalComponents.equiv_iff (MulAut.conj (⟨b, hb⟩ : H)) L).mpr
      hL, ?_⟩
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem commute {M₁ M₂ : Subgroup (MulAut V)} (h₁ : IsCompOf H M₁) (h₂ : IsCompOf H M₂)
    (hne : M₁ ≠ M₂) {x y : MulAut V} (hx : x ∈ M₁) (hy : y ∈ M₂) : x * y = y * x := by
  obtain ⟨L₁, hL₁, rfl⟩ := h₁
  obtain ⟨L₂, hL₂, rfl⟩ := h₂
  have hLne : L₁ ≠ L₂ := fun h => hne (h ▸ rfl)
  have hc := CFSG.ComponentClassification.LocalComponents.commute_of_ne L₁ L₂ hL₁ hL₂ hLne
  obtain ⟨x', hx', rfl⟩ := hx
  obtain ⟨y', hy', rfl⟩ := hy
  have h1 := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc hx'
  have hxy := Subgroup.mem_centralizer_iff.mp h1 y' hy'
  have := congrArg H.subtype hxy.symm
  simpa using this

theorem odd_orderOf_of_mem_center (hO2 : CFSG.Open.pCoreOf 2 H = ⊥) {L : Subgroup H}
    (hL : CFSG.Open.IsComponentOf L ⊤) {z : L} (hz : z ∈ Subgroup.center L) :
    Odd (orderOf ((z : H) : MulAut V)) := by
  apply B19Aux.odd_orderOf_of_mem_fittingOf hO2
  have h1 : (z : H) ∈ CFSG.ComponentClassification.Layer.subgroup H :=
    CFSG.ComponentClassification.Layer.component_le hL z.2
  have h2 : (z : H) ∈
      Subgroup.centralizer (CFSG.ComponentClassification.Layer.subgroup H : Set H) :=
    CFSG.ComponentClassification.ComponentAutomorphisms.center_le_layer_center L hL ⟨z, hz, rfl⟩
  have h3 : (⟨(z : H), h1⟩ : CFSG.ComponentClassification.Layer.subgroup H) ∈
      Subgroup.center _ := by
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp h2 w w.2)
  have h4 := CFSG.ComponentClassification.GeneralizedFitting.layer_center_le_fitting H
    ⟨_, h3, rfl⟩
  exact ⟨(z : H), h4, rfl⟩

theorem center
    (hO2 : CFSG.Open.pCoreOf 2 H = ⊥) (hSz : SzComponents H) (hM : IsCompOf H M) :
    (∃ a : ℕ, 1 ≤ a ∧ ∃ (K : Type) (_ : Field K) (_ : Finite K), Nat.card K = 2 ^ (2 * a + 1) ∧
      Nonempty (M ≃* CFSG.Blueprint.suzukiGroup a K)) ∧
      M ⊓ Subgroup.centralizer (M : Set (MulAut V)) = ⊥ := by
  obtain ⟨L, hL, rfl⟩ := hM
  obtain ⟨a, ha, K, _, _, hK, ⟨eQ⟩⟩ := hSz L hL
  have : Group.IsPerfect L := ⟨hL.2.2.1⟩
  have hZodd : Odd (Nat.card (Subgroup.center L)) := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.odd_iff, ← Nat.two_dvd_ne_zero]
    intro h2
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 h2
    have hodd := odd_orderOf_of_mem_center hO2 hL z.2
    rw [Subgroup.orderOf_coe, Subgroup.orderOf_coe, Subgroup.orderOf_coe, hz] at hodd
    exact absurd hodd (by decide)
  have hZ : Subgroup.center L = ⊥ := Suzuki.center_eq_bot_of_quotient ha hK eQ hZodd
  have e : L ≃* CFSG.Blueprint.suzukiGroup a K :=
    (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ).symm).trans eQ
  refine ⟨⟨a, ha, K, inferInstance, inferInstance, hK,
    ⟨(L.equivMapOfInjective H.subtype H.subtype_injective).symm.trans e⟩⟩, ?_⟩
  rw [eq_bot_iff]
  rintro _ ⟨⟨l, hl, rfl⟩, hc⟩
  have hlZ : (⟨l, hl⟩ : L) ∈ Subgroup.center L := by
    rw [Subgroup.mem_center_iff]
    intro w
    apply Subtype.ext
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hc _ ⟨w, w.2, rfl⟩
  rw [hZ, Subgroup.mem_bot] at hlZ
  rw [Subgroup.mem_bot]
  have hl1 : l = 1 := congrArg Subtype.val hlZ
  rw [hl1, map_one]

end IsCompOf

theorem exists_isCompOf_not_le {H : Subgroup (MulAut V)} (hO2 : CFSG.Open.pCoreOf 2 H = ⊥)
    {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A) (hA1 : A ≠ ⊥)
    (hF : fittingOf H ≤ Subgroup.centralizer (A : Set (MulAut V))) :
    ∃ M, IsCompOf H M ∧ ¬ M ≤ Subgroup.centralizer (A : Set (MulAut V)) := by
  by_contra hall
  push Not at hall
  obtain ⟨a, ha1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hA1
  set ā : H := ⟨a, hAH a.2⟩ with hā
  have hFit : CFSG.ComponentClassification.Fitting.subgroup H ≤ Subgroup.centralizer {ā} := by
    intro f hf
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hfF : (f : MulAut V) ∈ fittingOf H := ⟨f, hf, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hF hfF) a a.2
    exact Subtype.ext this.symm
  have hLay : CFSG.ComponentClassification.Layer.subgroup H ≤ Subgroup.centralizer {ā} := by
    rw [CFSG.ComponentClassification.Layer.subgroup.eq_sSup]
    refine sSup_le fun L hL l hl => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hM := hall (L.map H.subtype) ⟨L, hL, rfl⟩
    have := Subgroup.mem_centralizer_iff.mp (hM ⟨l, hl, rfl⟩) a a.2
    exact Subtype.ext this.symm
  have hstar : CFSG.ComponentClassification.GeneralizedFitting.subgroup H ≤
      Subgroup.centralizer {ā} := sup_le hFit hLay
  have hmem : ā ∈ Subgroup.centralizer
      (CFSG.ComponentClassification.GeneralizedFitting.subgroup H : Set H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subgroup.mem_centralizer_singleton_iff.mp (hstar hh)
  have hfit := CFSG.ComponentClassification.GeneralizedFitting.centralizer_le_fitting H hmem
  have hodd := B19Aux.odd_orderOf_of_mem_fittingOf hO2 (a : MulAut V) ⟨ā, hfit, rfl⟩
  have h2 : orderOf (a : MulAut V) = 2 :=
    orderOf_eq_prime (hA.2 a a.2) (fun h => ha1 (Subtype.ext h))
  rw [h2] at hodd
  exact absurd hodd (by decide)

theorem map_conj_mul_mulAut (M : Subgroup (MulAut V)) (x y : MulAut V) :
    M.map (MulAut.conj (x * y)).toMonoidHom =
      (M.map (MulAut.conj y).toMonoidHom).map (MulAut.conj x).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1

theorem map_conj_one_mulAut (M : Subgroup (MulAut V)) :
    M.map (MulAut.conj (1 : MulAut V)).toMonoidHom = M := by
  ext g
  simp [MulAut.conj_apply]

theorem exists_diag_of_isCompOf {H M R : Subgroup (MulAut V)} (hM : IsCompOf H M)
    (hMZ : M ⊓ Subgroup.centralizer (M : Set (MulAut V)) = ⊥) (hRH : R ≤ H)
    (hRN : ∀ r ∈ R, r ∈ Subgroup.normalizer (M : Set (MulAut V)) → r = 1)
    {y₀ : MulAut V} (hy₀M : y₀ ∈ M) (hy₀1 : y₀ ≠ 1) {ℓ : ℕ} (hy₀ℓ : y₀ ^ ℓ = 1) :
    ∃ y ∈ H, y ^ ℓ = 1 ∧ y ≠ 1 ∧ (∀ r ∈ R, r * y = y * r) ∧
      (∀ c : MulAut V, (∀ m ∈ M, c * m = m * c) → (∀ r ∈ R, c * r = r * c) → c * y = y * c) ∧
      (∀ b : MulAut V, (∀ r ∈ R, b * r = r * b) → b * y₀ * b⁻¹ = y₀⁻¹ →
        b * y * b⁻¹ = y⁻¹) := by
  classical
  haveI : Fintype R := Fintype.ofFinite R
  set gen : R → MulAut V := fun r => (r : MulAut V) * y₀ * (r : MulAut V)⁻¹ with hgen
  have hgenM : ∀ r : R, gen r ∈ M.map (MulAut.conj (r : MulAut V)).toMonoidHom := fun r =>
    ⟨y₀, hy₀M, by simp [hgen, MulAut.conj_apply]⟩
  have hcomp : ∀ r : R, IsCompOf H (M.map (MulAut.conj (r : MulAut V)).toMonoidHom) :=
    fun r => hM.conj (hRH r.2)
  have hne : ∀ r r' : R, r ≠ r' → M.map (MulAut.conj (r : MulAut V)).toMonoidHom ≠
      M.map (MulAut.conj (r' : MulAut V)).toMonoidHom := by
    intro r r' hrr' heq
    apply hrr'
    have hN : (r' : MulAut V)⁻¹ * r ∈ Subgroup.normalizer (M : Set (MulAut V)) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe,
        map_conj_mul_mulAut, heq, ← map_conj_mul_mulAut, inv_mul_cancel, map_conj_one_mulAut]
    have h1 := hRN _ (R.mul_mem (R.inv_mem r'.2) r.2) hN
    exact Subtype.ext (inv_mul_eq_one.mp h1).symm
  have hcomm : ∀ r r' : R, r ≠ r' → gen r * gen r' = gen r' * gen r := fun r r' h =>
    (hcomp r).commute (hcomp r') (hne r r' h) (hgenM r) (hgenM r')
  set P : Subgroup (MulAut V) := Subgroup.closure (Set.range gen) with hP
  have hpair : (Set.range gen).Pairwise Commute := by
    rintro _ ⟨r, rfl⟩ _ ⟨r', rfl⟩ hne'
    exact hcomm r r' fun h => hne' (h ▸ rfl)
  haveI : IsMulCommutative P := Subgroup.isMulCommutative_closure hpair
  set g' : R → P := fun r => ⟨gen r, Subgroup.subset_closure ⟨r, rfl⟩⟩ with hg'
  set y' : P := ∏ r, g' r with hy'
  have hPH : P ≤ H := by
    rw [hP, Subgroup.closure_le]
    rintro _ ⟨r, rfl⟩
    exact H.mul_mem (H.mul_mem (hRH r.2) (hM.le hy₀M)) (H.inv_mem (hRH r.2))
  have hconj : ∀ b : MulAut V, (∀ r : R, b * gen r * b⁻¹ ∈ P) →
      ∀ x ∈ P, b * x * b⁻¹ ∈ P := by
    intro b hb
    have hle : P ≤ P.comap (MulAut.conj b).toMonoidHom := by
      rw [hP, Subgroup.closure_le]
      rintro _ ⟨r, rfl⟩
      exact hb r
    intro x hx
    exact hle hx
  let κ : ∀ b : MulAut V, (∀ r : R, b * gen r * b⁻¹ ∈ P) → P →* P := fun b hb =>
    ((MulAut.conj b).toMonoidHom.comp P.subtype).codRestrict P fun x => hconj b hb x x.2
  have hκ : ∀ b hb (x : P), ((κ b hb x : P) : MulAut V) = b * x * b⁻¹ := fun _ _ _ => rfl
  refine ⟨y', hPH y'.2, ?_, ?_, ?_, ?_, ?_⟩
  ·
    have h1 : y' ^ ℓ = 1 := by
      rw [hy', ← Finset.prod_pow]
      refine Finset.prod_eq_one fun r _ => Subtype.ext ?_
      simp only [hg', SubgroupClass.coe_pow, OneMemClass.coe_one, hgen]
      rw [conj_pow, hy₀ℓ, mul_one, mul_inv_cancel]
    exact congrArg Subtype.val h1
  ·
    intro hy1
    have hy'1 : y' = 1 := Subtype.ext hy1
    set Q : Subgroup P := (Subgroup.centralizer (M : Set (MulAut V))).comap P.subtype with hQ
    have hgenQ : ∀ r ∈ Finset.univ.erase (1 : R), g' r ∈ Q := by
      intro r hr
      have hr1 : r ≠ 1 := Finset.ne_of_mem_erase hr
      rw [hQ, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
      intro m hm
      have hM1 : M = M.map (MulAut.conj ((1 : R) : MulAut V)).toMonoidHom := by
        rw [OneMemClass.coe_one, map_conj_one_mulAut]
      have hmM : m ∈ M.map (MulAut.conj ((1 : R) : MulAut V)).toMonoidHom := hM1 ▸ hm
      exact ((hcomp 1).commute (hcomp r) (hne 1 r (Ne.symm hr1)) hmM (hgenM r))
    have hprod := Subgroup.prod_mem Q hgenQ
    have hsplit := Finset.mul_prod_erase Finset.univ g' (Finset.mem_univ (1 : R))
    rw [← hy', hy'1] at hsplit
    have h1 : g' 1 = (∏ r ∈ Finset.univ.erase (1 : R), g' r)⁻¹ := eq_inv_of_mul_eq_one_left hsplit
    have hgQ : g' 1 ∈ Q := h1 ▸ Q.inv_mem hprod
    have hy₀C : y₀ ∈ Subgroup.centralizer (M : Set (MulAut V)) := by
      have h2 := hgQ
      rw [hQ, Subgroup.mem_comap] at h2
      have h3 : ((g' 1 : P) : MulAut V) = y₀ := by
        simp [hg', hgen]
      rwa [Subgroup.coe_subtype, h3] at h2
    have : y₀ ∈ M ⊓ Subgroup.centralizer (M : Set (MulAut V)) := ⟨hy₀M, hy₀C⟩
    rw [hMZ, Subgroup.mem_bot] at this
    exact hy₀1 this
  ·
    intro r₀ hr₀
    have hb : ∀ r : R, r₀ * gen r * r₀⁻¹ ∈ P := fun r => by
      have : r₀ * gen r * r₀⁻¹ = gen (⟨r₀, hr₀⟩ * r) := by
        simp only [hgen, Subgroup.coe_mul, mul_inv_rev]
        group
      rw [this]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    have hfix : κ r₀ hb y' = y' := by
      rw [hy', map_prod]
      have hκg : ∀ r : R, κ r₀ hb (g' r) = g' (⟨r₀, hr₀⟩ * r) := fun r => by
        apply Subtype.ext
        change r₀ * gen r * r₀⁻¹ = gen (⟨r₀, hr₀⟩ * r)
        simp only [hgen, Subgroup.coe_mul, mul_inv_rev]
        group
      simp only [hκg]
      exact Fintype.prod_equiv (Equiv.mulLeft (⟨r₀, hr₀⟩ : R)) _ _ (fun _ => rfl)
    have h1 := congrArg Subtype.val hfix
    change r₀ * (y' : MulAut V) * r₀⁻¹ = y' at h1
    calc r₀ * (y' : MulAut V) = r₀ * y' * r₀⁻¹ * r₀ := by group
      _ = y' * r₀ := by rw [h1]
  ·
    intro c hcM hcR
    have hcS : c ∈ Subgroup.centralizer (Set.range gen) := by
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨r, rfl⟩
      have h1 := hcR r r.2
      have h2 := hcM y₀ hy₀M
      simp only [hgen]
      calc (r : MulAut V) * y₀ * (r : MulAut V)⁻¹ * c
          = r * y₀ * (c⁻¹ * (c * (r : MulAut V)⁻¹ * c)) := by group
        _ = c * (r * y₀ * (r : MulAut V)⁻¹) := by
          rw [show c * (r : MulAut V)⁻¹ * c = c * c * (r : MulAut V)⁻¹ by
            rw [mul_assoc, mul_assoc]; congr 1
            calc (r : MulAut V)⁻¹ * c = (r : MulAut V)⁻¹ * (c * r) * (r : MulAut V)⁻¹ := by group
              _ = (r : MulAut V)⁻¹ * (r * c) * (r : MulAut V)⁻¹ := by rw [h1]
              _ = c * (r : MulAut V)⁻¹ := by group]
          calc (r : MulAut V) * y₀ * (c⁻¹ * (c * c * (r : MulAut V)⁻¹))
              = r * (y₀ * c) * (r : MulAut V)⁻¹ := by group
            _ = r * (c * y₀) * (r : MulAut V)⁻¹ := by rw [h2]
            _ = (r * c) * y₀ * (r : MulAut V)⁻¹ := by group
            _ = (c * r) * y₀ * (r : MulAut V)⁻¹ := by rw [h1]
            _ = c * (r * y₀ * (r : MulAut V)⁻¹) := by group
    rw [← Subgroup.centralizer_closure, ← hP] at hcS
    exact (Subgroup.mem_centralizer_iff.mp hcS _ y'.2).symm
  ·
    intro b hbR hby₀
    have hbg : ∀ r : R, b * gen r * b⁻¹ = (gen r)⁻¹ := fun r => by
      have h1 := hbR r r.2
      simp only [hgen, mul_inv_rev, inv_inv]
      calc b * ((r : MulAut V) * y₀ * (r : MulAut V)⁻¹) * b⁻¹
          = (b * r) * y₀ * (b * r)⁻¹ := by group
        _ = (r * b) * y₀ * (r * b)⁻¹ := by rw [h1]
        _ = r * (b * y₀ * b⁻¹) * (r : MulAut V)⁻¹ := by group
        _ = r * y₀⁻¹ * (r : MulAut V)⁻¹ := by rw [hby₀]
    have hb : ∀ r : R, b * gen r * b⁻¹ ∈ P := fun r => by
      rw [hbg r]
      exact P.inv_mem (Subgroup.subset_closure ⟨r, rfl⟩)
    have hinv : κ b hb y' = y'⁻¹ := by
      rw [hy', map_prod, ← Finset.prod_inv_distrib]
      refine Finset.prod_congr rfl fun r _ => Subtype.ext ?_
      change b * gen r * b⁻¹ = (gen r)⁻¹
      exact hbg r
    have h1 := congrArg Subtype.val hinv
    change b * (y' : MulAut V) * b⁻¹ = ((y'⁻¹ : P) : MulAut V) at h1
    rw [h1, InvMemClass.coe_inv]

theorem inner_and_card_le_of_suzuki {M A : Subgroup (MulAut V)}
    (hA : IsElemAbelian2 A) {a : ℕ} (ha : 1 ≤ a) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) (e : M ≃* CFSG.Blueprint.suzukiGroup a K)
    (hMZ : M ⊓ Subgroup.centralizer (M : Set (MulAut V)) = ⊥) :
    (∀ b ∈ A ⊓ Subgroup.normalizer (M : Set (MulAut V)), ∃ g ∈ M,
        (∀ m ∈ M, b * m * b⁻¹ = g * m * g⁻¹) ∧ g ^ 2 = 1) ∧
      Nat.card ↥(A ⊓ Subgroup.normalizer (M : Set (MulAut V))) ≤
        Nat.card ↥(A ⊓ Subgroup.centralizer (M : Set (MulAut V))) * 2 ^ (2 * a + 1) := by
  classical
  set N := A ⊓ Subgroup.normalizer (M : Set (MulAut V)) with hNdef
  have hN : N ≤ Subgroup.normalizer (M : Set (MulAut V)) := inf_le_right
  set φ : N →* MulAut M := M.normalizerMonoidHom.comp (Subgroup.inclusion hN) with hφ
  have hφapp : ∀ (b : N) (m : M), ((φ b m : M) : MulAut V) =
      (b : MulAut V) * (m : MulAut V) * (b : MulAut V)⁻¹ := fun _ _ => rfl
  have hconj : ∀ x : M, MulAut.conj x = 1 → x = 1 := by
    intro x hx
    have hxc : (x : MulAut V) ∈ M ⊓ Subgroup.centralizer (M : Set (MulAut V)) := by
      refine ⟨x.2, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
      have h1 := congrArg (fun σ : MulAut M => ((σ ⟨m, hm⟩ : M) : MulAut V)) hx
      simp only [MulAut.conj_apply, MulAut.one_apply, Subgroup.coe_mul,
        InvMemClass.coe_inv] at h1
      calc m * (x : MulAut V) = (x : MulAut V) * m * (x : MulAut V)⁻¹ * x := by rw [h1]
        _ = x * m := by group
    rw [hMZ, Subgroup.mem_bot] at hxc
    exact Subtype.ext hxc
  have hconjinj : Function.Injective (MulAut.conj : M →* MulAut M) :=
    (injective_iff_map_eq_one _).mpr hconj
  have hinner : ∀ b : N, ∃ g : M, φ b = MulAut.conj g ∧ g * g = 1 := by
    intro b
    have hb2 : b * b = 1 := Subtype.ext (by
      have := hA.2 b b.2.1
      rw [pow_two] at this
      exact this)
    have hφ2 : φ b * φ b = 1 := by rw [← map_mul, hb2, map_one]
    obtain ⟨g, hg⟩ := Suzuki.exists_eq_conj_of_mul_self_eq_one ha hK e hφ2
    refine ⟨g, hg, hconj _ ?_⟩
    rw [map_mul, ← hg, hφ2]
  refine ⟨fun b hb => ?_, ?_⟩
  · obtain ⟨g, hg, hg2⟩ := hinner ⟨b, hb⟩
    refine ⟨g, g.2, fun m hm => ?_, by rw [pow_two]; exact congrArg Subtype.val hg2⟩
    have h1 := congrArg (fun σ : MulAut M => ((σ ⟨m, hm⟩ : M) : MulAut V)) hg
    simp only [MulAut.conj_apply, Subgroup.coe_mul, InvMemClass.coe_inv] at h1
    exact (hφapp ⟨b, hb⟩ ⟨m, hm⟩).symm.trans h1
  ·
    set E : Subgroup M := φ.range.comap (MulAut.conj : M →* MulAut M) with hE
    have hE2 : ∀ x ∈ E, x ^ 2 = 1 := by
      intro x hx
      obtain ⟨b, hb⟩ := hx
      obtain ⟨g, hg, hg2⟩ := hinner b
      have hxg : x = g := by
        have h1 : MulAut.conj (x * g⁻¹) = 1 := by
          rw [map_mul, map_inv, ← hb, hg, mul_inv_cancel]
        exact mul_inv_eq_one.mp (hconj _ h1)
      rw [hxg, pow_two]
      exact hg2
    have hEq : Nat.card φ.range = Nat.card E := by
      have hle : φ.range ≤ (MulAut.conj : M →* MulAut M).range := by
        rintro _ ⟨b, rfl⟩
        obtain ⟨g, hg, -⟩ := hinner b
        exact ⟨g, hg.symm⟩
      have hmap : E.map (MulAut.conj : M →* MulAut M) = φ.range := by
        rw [hE, Subgroup.map_comap_eq, inf_eq_right.mpr hle]
      rw [← hmap, Subgroup.card_map_of_injective hconjinj]
    have hrange : Nat.card φ.range ≤ 2 ^ (2 * a + 1) := by
      rw [hEq]
      exact Suzuki.card_le_of_sq_eq_one ha hK e hE2
    have hCN : A ⊓ Subgroup.centralizer (M : Set (MulAut V)) ≤ N :=
      inf_le_inf_left A (Subgroup.centralizer_le_normalizer _)
    have hker : φ.ker = (A ⊓ Subgroup.centralizer (M : Set (MulAut V))).subgroupOf N := by
      ext b
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      constructor
      · intro hb
        refine ⟨b.2.1, Subgroup.mem_centralizer_iff.mpr fun m hm => ?_⟩
        have h1 := congrArg (fun σ : MulAut M => ((σ ⟨m, hm⟩ : M) : MulAut V)) hb
        simp only [MulAut.one_apply] at h1
        rw [hφapp] at h1
        calc m * (b : MulAut V) = (b : MulAut V) * m * (b : MulAut V)⁻¹ * b := by rw [h1]
          _ = b * m := by group
      · rintro ⟨-, hbc⟩
        refine MulEquiv.ext fun m => Subtype.ext ?_
        rw [hφapp, MulAut.one_apply]
        calc (b : MulAut V) * (m : MulAut V) * (b : MulAut V)⁻¹
            = (m : MulAut V) * b * (b : MulAut V)⁻¹ := by
              rw [Subgroup.mem_centralizer_iff.mp hbc m m.2]
          _ = m := by group
    have hcard := Subgroup.card_mul_index φ.ker
    rw [Subgroup.index_ker, hker,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCN).toEquiv] at hcard
    rw [← hcard]
    exact Nat.mul_le_mul_left _ hrange

theorem inv_mul_mem_normalizer_of_map_conj_eq {M : Subgroup (MulAut V)} {b b' : MulAut V}
    (heq : M.map (MulAut.conj b).toMonoidHom = M.map (MulAut.conj b').toMonoidHom) :
    b⁻¹ * b' ∈ Subgroup.normalizer (M : Set (MulAut V)) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe, map_conj_mul_mulAut,
    ← heq, ← map_conj_mul_mulAut, inv_mul_cancel, map_conj_one_mulAut]

theorem two_mul_rk_le_rkIdx_of_centralizes (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)}
    (hS3 : ∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ → y = 1)
    {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A) {M : Subgroup (MulAut V)}
    (hM : IsCompOf H M) (hMZ : M ⊓ Subgroup.centralizer (M : Set (MulAut V)) = ⊥)
    (hNC : A ⊓ Subgroup.normalizer (M : Set (MulAut V)) ≤
      Subgroup.centralizer (M : Set (MulAut V)))
    (hMA : ¬ M ≤ Subgroup.centralizer (A : Set (MulAut V))) {x : MulAut V} (hxM : x ∈ M)
    {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (hxℓ : orderOf x = ℓ)
    (hIH : ∀ B : Subgroup (MulAut V), B ≤ A → Nat.card B < Nat.card A →
      2 * rk B ≤ rkIdx (fixV B)) :
    2 * rk A ≤ rkIdx (fixV A) := by
  set gen : A → MulAut V := fun b => (b : MulAut V) * x * (b : MulAut V)⁻¹ with hgen
  set X : Subgroup (MulAut V) := Subgroup.closure (Set.range gen) with hX
  have hpair : (Set.range gen).Pairwise Commute := by
    rintro _ ⟨b, rfl⟩ _ ⟨b', rfl⟩ hne
    by_cases heq : M.map (MulAut.conj (b : MulAut V)).toMonoidHom =
      M.map (MulAut.conj (b' : MulAut V)).toMonoidHom
    · exfalso
      apply hne
      have hN := inv_mul_mem_normalizer_of_map_conj_eq heq
      have hC := hNC ⟨A.mul_mem (A.inv_mem b.2) b'.2, hN⟩
      have hcx := Subgroup.mem_centralizer_iff.mp hC x hxM
      simp only [hgen]
      calc (b : MulAut V) * x * (b : MulAut V)⁻¹
          = b * (x * ((b : MulAut V)⁻¹ * b')) * (b' : MulAut V)⁻¹ := by group
        _ = b * (((b : MulAut V)⁻¹ * b') * x) * (b' : MulAut V)⁻¹ := by rw [hcx]
        _ = b' * x * (b' : MulAut V)⁻¹ := by group
    · exact (hM.conj (hAH b.2)).commute (hM.conj (hAH b'.2)) heq ⟨x, hxM, rfl⟩
        ⟨x, hxM, rfl⟩
  haveI : IsMulCommutative X := Subgroup.isMulCommutative_closure hpair
  have hXℓ : ∀ g ∈ X, g ^ ℓ = 1 := by
    intro g hg
    refine Subgroup.closure_induction (p := fun g _ => g ^ ℓ = 1) ?_ ?_ ?_ ?_ hg
    · rintro _ ⟨b, rfl⟩
      simp only [hgen]
      rw [conj_pow, ← hxℓ, pow_orderOf_eq_one, mul_one, mul_inv_cancel]
    · exact one_pow ℓ
    · intro g h hg hh hgℓ hhℓ
      have hcomm : Commute g h := by
        have := mul_comm (⟨g, hg⟩ : X) ⟨h, hh⟩
        exact congrArg Subtype.val this
      rw [hcomm.mul_pow, hgℓ, hhℓ, one_mul]
    · intro g _ hgℓ
      rw [inv_pow, hgℓ, inv_one]
  have hXodd : ∀ g ∈ X, Odd (orderOf g) := by
    intro g hg
    have hdvd := orderOf_dvd_of_pow_eq_one (hXℓ g hg)
    rcases (Nat.dvd_prime hℓ).mp hdvd with h | h
    · rw [h]; exact odd_one
    · rw [h]; exact hℓ.odd_of_ne_two hℓ2
  have hXH : X ≤ H := by
    rw [hX, Subgroup.closure_le]
    rintro _ ⟨b, rfl⟩
    exact H.mul_mem (H.mul_mem (hAH b.2) (hM.le hxM)) (H.inv_mem (hAH b.2))
  have hconj : ∀ c ∈ A, ∀ g ∈ X, c * g * c⁻¹ ∈ X := by
    intro c hc
    have hle : X ≤ X.comap (MulAut.conj c).toMonoidHom := by
      rw [hX, Subgroup.closure_le]
      rintro _ ⟨b, rfl⟩
      show c * gen b * c⁻¹ ∈ X
      have : c * gen b * c⁻¹ = gen ⟨c * b, A.mul_mem hc b.2⟩ := by
        simp only [hgen, Subgroup.coe_mk, mul_inv_rev]
        group
      rw [this]
      exact Subgroup.subset_closure ⟨_, rfl⟩
    exact fun g hg => hle hg
  have hAX : A ≤ Subgroup.normalizer (X : Set (MulAut V)) := by
    intro c hc
    rw [Subgroup.mem_normalizer_iff]
    intro g
    refine ⟨fun hg => hconj c hc g hg, fun hg => ?_⟩
    have := hconj c⁻¹ (A.inv_mem hc) _ hg
    simpa [mul_assoc] using this
  have hxA : ¬ X ≤ Subgroup.centralizer (A : Set (MulAut V)) := by
    intro hle
    obtain ⟨m, hm, hmA⟩ := SetLike.not_le_iff_exists.mp hMA
    obtain ⟨b, hb, hbm⟩ : ∃ b ∈ A, b * m ≠ m * b := by
      by_contra hall
      push Not at hall
      exact hmA (Subgroup.mem_centralizer_iff.mpr fun b hb => hall b hb)
    have hbN : b ∉ Subgroup.normalizer (M : Set (MulAut V)) := fun hbN =>
      hbm (Subgroup.mem_centralizer_iff.mp (hNC ⟨hb, hbN⟩) m hm).symm
    have hne : M.map (MulAut.conj b).toMonoidHom ≠ M := by
      intro h
      apply hbN
      rw [Subgroup.mem_normalizer_iff_map_conj_eq, ← MulEquiv.toMonoidHom_eq_coe, h]
    have hxX : x ∈ X := Subgroup.subset_closure ⟨⟨1, A.one_mem⟩, by simp [hgen]⟩
    have hxb : b * x * b⁻¹ = x := by
      have := Subgroup.mem_centralizer_iff.mp (hle hxX) b hb
      rw [this, mul_inv_cancel_right]
    have hxMb : x ∈ M.map (MulAut.conj b).toMonoidHom := ⟨x, hxM, by
      simp [MulAut.conj_apply, hxb]⟩
    have hxC : x ∈ Subgroup.centralizer (M : Set (MulAut V)) :=
      Subgroup.mem_centralizer_iff.mpr fun m' hm' =>
        ((hM.conj (hAH hb)).commute hM hne hxMb hm').symm
    have : x ∈ M ⊓ Subgroup.centralizer (M : Set (MulAut V)) := ⟨hxM, hxC⟩
    rw [hMZ, Subgroup.mem_bot] at this
    rw [this, orderOf_one] at hxℓ
    exact hℓ.one_lt.ne hxℓ
  exact two_mul_rk_le_rkIdx_of_odd hV hS3 hAH hA hXH hXodd hAX hxA hIH

theorem two_mul_rk_le_rkIdx_of_inner (hV : ∀ v : V, v ^ 2 = 1)
    {H : Subgroup (MulAut V)} {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A)
    {M : Subgroup (MulAut V)} (hM : IsCompOf H M)
    (hMZ : M ⊓ Subgroup.centralizer (M : Set (MulAut V)) = ⊥) {a : ℕ} (ha : 1 ≤ a)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ (2 * a + 1))
    (e : M ≃* CFSG.Blueprint.suzukiGroup a K) {a₀ : MulAut V} (ha₀A : a₀ ∈ A)
    (ha₀N : a₀ ∈ Subgroup.normalizer (M : Set (MulAut V)))
    (ha₀C : a₀ ∉ Subgroup.centralizer (M : Set (MulAut V)))
    (hIH : ∀ B : Subgroup (MulAut V), B ≤ A → Nat.card B < Nat.card A →
      2 * rk B ≤ rkIdx (fixV B)) :
    2 * rk A ≤ rkIdx (fixV A) := by
  classical
  obtain ⟨hinner, hcard⟩ := inner_and_card_le_of_suzuki hA ha hK e hMZ
  set A₁ := A ⊓ Subgroup.normalizer (M : Set (MulAut V)) with hA₁
  set A' := A ⊓ Subgroup.centralizer (M : Set (MulAut V)) with hA'
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := hA.1
  obtain ⟨g, hgM, hg, hg2⟩ := hinner a₀ ⟨ha₀A, ha₀N⟩
  have hg1 : g ≠ 1 := by
    rintro rfl
    apply ha₀C
    rw [Subgroup.mem_centralizer_iff]
    intro m hm
    have h1 := hg m hm
    rw [one_mul, inv_one, mul_one] at h1
    calc m * a₀ = a₀ * m * a₀⁻¹ * a₀ := by rw [h1]
      _ = a₀ * m := by group
  have hgo : orderOf (⟨g, hgM⟩ : M) = 2 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hg2 hg1
  obtain ⟨ℓ, hℓ, hℓ2, hord⟩ :=
    Suzuki.exists_prime_orderOf_two_eq_four_mul (n := 2 * a + 1) (by omega)
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  have hdvd := Suzuki.dvd_card_of_orderOf_two_eq hK e hℓ hord
  obtain ⟨y₁, hy₁, hgy₁⟩ := Suzuki.exists_orderOf_eq_and_inv ha hK e hℓ hℓ2 hdvd hgo
  have hy₀M : (y₁ : MulAut V) ∈ M := y₁.2
  have hy₀ℓ : orderOf (y₁ : MulAut V) = ℓ := by rw [Subgroup.orderOf_coe, hy₁]
  have hy₀1 : (y₁ : MulAut V) ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hy₀ℓ
    exact hℓ.one_lt.ne hy₀ℓ
  have hgy₀ : g * (y₁ : MulAut V) * g⁻¹ = (y₁ : MulAut V)⁻¹ := by
    have h1 := congrArg Subtype.val hgy₁
    simp only [Subgroup.coe_mul, Subgroup.coe_mk, InvMemClass.coe_inv] at h1
    exact h1
  have ha₀y₀ : a₀ * (y₁ : MulAut V) * a₀⁻¹ = (y₁ : MulAut V)⁻¹ := by
    rw [hg _ hy₀M, hgy₀]
  have hAel : CFSG.Open.IsElemAbelian 2 A :=
    ⟨⟨⟨fun x y => Subtype.ext (hA.1 x x.2 y y.2)⟩⟩, hA.2⟩
  obtain ⟨R, hRA, hA₁R, hA₁Rsup⟩ :=
    CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma212.exists_complement_of_isElemAbelian
      Nat.prime_two hAel (inf_le_left : A₁ ≤ A)
  have hRN : ∀ r ∈ R, r ∈ Subgroup.normalizer (M : Set (MulAut V)) → r = 1 := by
    intro r hr hrN
    have h1 : r ∈ A₁ ⊓ R := ⟨⟨hRA hr, hrN⟩, hr⟩
    rw [hA₁R, Subgroup.mem_bot] at h1
    exact h1
  obtain ⟨y, -, hyℓ, hy1, hyR, hyc, hyb⟩ :=
    exists_diag_of_isCompOf hM hMZ (hRA.trans hAH) hRN hy₀M hy₀1
    (show (y₁ : MulAut V) ^ ℓ = 1 by rw [← hy₀ℓ]; exact pow_orderOf_eq_one _)
  set C := A' ⊔ R with hC
  have hCA : C ≤ A := sup_le inf_le_left hRA
  have hyC : ∀ c ∈ C, c * y = y * c := by
    have hle : C ≤ Subgroup.centralizer {y} := by
      refine sup_le ?_ ?_
      · intro c hc
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hyc c (fun m hm => (Subgroup.mem_centralizer_iff.mp hc.2 m hm).symm)
          (fun r hr => hAc c hc.1 r (hRA hr))
      · intro r hr
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact hyR r hr
    intro c hc
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hc)
  have hay : a₀ * y * a₀⁻¹ = y⁻¹ := hyb a₀ (fun r hr => hAc a₀ ha₀A r (hRA hr)) ha₀y₀
  have hyo : orderOf y = ℓ := orderOf_eq_prime hyℓ hy1
  have ha₀C' : a₀ ∉ C := by
    intro hmem
    have hAR : A' ≤ Subgroup.normalizer (R : Set (MulAut V)) := fun c hc =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun r hr =>
        hAc r (hRA hr) c hc.1)
    have hmem' : a₀ ∈ ((A' ⊔ R : Subgroup (MulAut V)) : Set (MulAut V)) := hmem
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A' R hAR] at hmem'
    obtain ⟨c, hc, r, hr, hcr'⟩ := hmem'
    have hcr : c * r = a₀ := hcr'
    have hc' := Subgroup.mem_inf.mp hc
    have hrN : r ∈ Subgroup.normalizer (M : Set (MulAut V)) := by
      have h1 : r = c⁻¹ * a₀ := by rw [← hcr]; group
      rw [h1]
      exact Subgroup.mul_mem _
        (Subgroup.inv_mem _ (Subgroup.centralizer_le_normalizer _ hc'.2)) ha₀N
    have hr1 := hRN r hr hrN
    rw [hr1, mul_one] at hcr
    exact ha₀C (hcr ▸ hc'.2)
  have hcardA : Nat.card A = Nat.card A₁ * Nat.card R := by
    rw [← card_sup_of_commute_of_inf_eq_bot
      (fun u hu w hw => hAc u (Subgroup.mem_inf.mp hu).1 w (hRA hw)) hA₁R, hA₁Rsup]
  have hA'R : A' ⊓ R = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have h1 : z ∈ A₁ ⊓ R :=
      ⟨⟨hz.1.1, Subgroup.centralizer_le_normalizer _ hz.1.2⟩, hz.2⟩
    rwa [hA₁R] at h1
  have hcardC : Nat.card C = Nat.card A' * Nat.card R :=
    card_sup_of_commute_of_inf_eq_bot
      (fun u hu w hw => hAc u (Subgroup.mem_inf.mp hu).1 w (hRA hw)) hA'R
  have hA2 : IsPGroup 2 A := hA.isPGroup
  have hC2 : IsPGroup 2 C := hA2.to_le hCA
  have hrk : rk A ≤ rk C + (2 * a + 1) := by
    have h1 : Nat.card A ≤ Nat.card C * 2 ^ (2 * a + 1) := by
      rw [hcardA, hcardC]
      calc Nat.card A₁ * Nat.card R ≤ Nat.card A' * 2 ^ (2 * a + 1) * Nat.card R :=
            Nat.mul_le_mul_right _ hcard
        _ = Nat.card A' * Nat.card R * 2 ^ (2 * a + 1) := by ring
    rw [card_eq_two_pow_of_isPGroup hA2, card_eq_two_pow_of_isPGroup hC2, ← pow_add] at h1
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h1
  have ha₀N' : a₀ ∈ Subgroup.normalizer (C : Set (MulAut V)) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun c hc =>
      hAc c (hCA hc) a₀ ha₀A)
  have hyN' : y ∈ Subgroup.normalizer (C : Set (MulAut V)) :=
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun c hc => hyC c hc)
  have ha₀W : a₀ ∈ stabSub (fixV C) := FixVLat.le_stabSub_fixV_of_le_normalizer
    (Subgroup.zpowers_le.mpr ha₀N') (Subgroup.mem_zpowers a₀)
  have hyW : y ∈ stabSub (fixV C) := FixVLat.le_stabSub_fixV_of_le_normalizer
    (Subgroup.zpowers_le.mpr hyN') (Subgroup.mem_zpowers y)
  have hnt : ¬ fixV C ≤ fixV (Subgroup.zpowers y) := by
    intro hle
    have hZodd : Odd (Nat.card (Subgroup.zpowers y)) := by
      rw [Nat.card_zpowers, hyo]
      exact hℓ.odd_of_ne_two hℓ2
    have hcomm : ∀ z ∈ Subgroup.zpowers y, ∀ c ∈ C, z * c = c * z := by
      intro z hz c hc
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact Commute.zpow_left (hyC c hc).symm k
    have htop := B1.axb hV hZodd hC2 hcomm (M := ⊤) (fun _ _ _ _ => Subgroup.mem_top _)
      (fun _ _ _ _ => Subgroup.mem_top _) (fun z hz m hm => hle hm.2 z hz)
    apply hy1
    exact MulEquiv.ext fun v => htop (Subgroup.mem_top v) y (Subgroup.mem_zpowers y)
  have hprime := two_mul_le_mRel_of_orderOf_two hV hℓ hℓ2 hord hyo hay ha₀W hyW hnt
  have hmono : mRel (fixV (Subgroup.zpowers a₀)) (fixV C) ≤ mRel (fixV A) (fixV C) := by
    unfold mRel
    exact padicValNat_two_le_of_dvd (relIndex_ne_zero_of_finite _ _)
      (Subgroup.relIndex_dvd_of_le_left (fixV C)
        (B1.fixV_le_fixV (Subgroup.zpowers_le.mpr ha₀A)))
  have hsplit := codimOn_eq_add hCA (⊤ : Subgroup V)
  rw [codimOn_top, codimOn_top, inf_top_eq] at hsplit
  have hIHC := hIH C hCA (Subgroup.card_lt_of_lt (lt_of_le_of_ne hCA fun h => ha₀C' (h ▸ ha₀A)))
  omega

theorem two_mul_rk_le_rkIdx_of_szComponents
    (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    (hO2 : CFSG.Open.pCoreOf 2 H = ⊥)
    (hS3 : ∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ → y = 1)
    (hSz : SzComponents H) {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A) :
    2 * rk A ≤ rkIdx (fixV A) := by
  induction hn : Nat.card A using Nat.strong_induction_on generalizing A with
  | _ n ih =>
  have hIH : ∀ B : Subgroup (MulAut V), B ≤ A → Nat.card B < Nat.card A →
      2 * rk B ≤ rkIdx (fixV B) := fun B hBA hlt =>
    ih _ (hn ▸ hlt) (hBA.trans hAH)
      ⟨fun x hx y hy => hA.1 x (hBA hx) y (hBA hy), fun x hx => hA.2 x (hBA hx)⟩ rfl
  by_cases hA1 : A = ⊥
  · subst hA1
    rw [rk_bot]
    exact Nat.zero_le _
  by_cases hF : fittingOf H ≤ Subgroup.centralizer (A : Set (MulAut V))
  · obtain ⟨M, hM, hMA⟩ := exists_isCompOf_not_le hO2 hAH hA hA1 hF
    obtain ⟨⟨a, ha, K, _, _, hK, ⟨e⟩⟩, hMZ⟩ := hM.center hO2 hSz
    by_cases hNC : A ⊓ Subgroup.normalizer (M : Set (MulAut V)) ≤
        Subgroup.centralizer (M : Set (MulAut V))
    · obtain ⟨ℓ, hℓ, hℓ2, hord⟩ :=
        Suzuki.exists_prime_orderOf_two_eq_four_mul (n := 2 * a + 1) (by omega)
      have hdvd := Suzuki.dvd_card_of_orderOf_two_eq hK e hℓ hord
      have : Fact ℓ.Prime := ⟨hℓ⟩
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' ℓ hdvd
      exact two_mul_rk_le_rkIdx_of_centralizes hV hS3 hAH hA hM hMZ hNC hMA x.2 hℓ hℓ2
        (by rw [Subgroup.orderOf_coe, hx]) hIH
    · obtain ⟨a₀, ⟨ha₀A, ha₀N⟩, ha₀C⟩ := SetLike.not_le_iff_exists.mp hNC
      exact two_mul_rk_le_rkIdx_of_inner hV hAH hA hM hMZ ha hK e ha₀A ha₀N ha₀C hIH
  · have hAF : A ≤ Subgroup.normalizer (fittingOf H : Set (MulAut V)) := by
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro f
      constructor
      · exact conj_mem_fittingOf (hAH ha)
      · intro hf
        have h1 := conj_mem_fittingOf ((hAH ha) |> H.inv_mem) hf
        simpa [mul_assoc] using h1
    exact two_mul_rk_le_rkIdx_of_odd hV hS3 hAH hA (fittingOf_le H)
      (B19Aux.odd_orderOf_of_mem_fittingOf hO2) hAF hF hIH

theorem SzComponents.of_szSections {X : Type*} [Group X] (hX : SzSections X) :
    SzComponents X := by
  intro L hL
  have hsimple : IsSimpleGroup (L ⧸ Subgroup.center L) := hL.2.2.2
  refine hX L (Subgroup.center L) hsimple ?_
  by_contra hab
  push Not at hab
  have hcomm : commutator L ≤ Subgroup.center L := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [commutatorElement_def, ← QuotientGroup.eq_one_iff, QuotientGroup.mk_mul,
      QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_inv,
      hab (x : L ⧸ Subgroup.center L) y]
    group
  have htop : Subgroup.center L = ⊤ := top_le_iff.mp (hL.2.2.1 ▸ hcomm)
  have hsub : Subsingleton (L ⧸ Subgroup.center L) := by
    rw [htop]
    exact QuotientGroup.subsingleton_quotient_top
  exact not_subsingleton (L ⧸ Subgroup.center L) hsub

theorem two_mul_rk_le_rkIdx_of_szSections
    (hV : ∀ v : V, v ^ 2 = 1) {H : Subgroup (MulAut V)}
    (hsz : SzSections H) (hO2 : CFSG.Open.pCoreOf 2 H = ⊥)
    (hS3 : ∀ a ∈ H, ∀ y ∈ H, a ^ 2 = 1 → y ^ 3 = 1 → a * y * a⁻¹ = y⁻¹ → y = 1)
    {A : Subgroup (MulAut V)} (hAH : A ≤ H) (hA : IsElemAbelian2 A) :
    2 * rk A ≤ rkIdx (fixV A) :=
  two_mul_rk_le_rkIdx_of_szComponents hV hO2 hS3 (SzComponents.of_szSections hsz) hAH hA

end CFSG.RankThree.S4Free.Stell
