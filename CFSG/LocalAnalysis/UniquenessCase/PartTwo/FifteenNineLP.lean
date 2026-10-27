module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsHyp
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.Quasithin.Background.B1MoreQuot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]


theorem s15_LP_vtil_sq_eq_one (V₀ V : Subgroup G) (hV : IsElemAbelian 2 V)
    (w : Vtil V₀ V hV) : w ^ 2 = 1 := by
  induction w using QuotientGroup.induction_on with
  | H x =>
    rw [← QuotientGroup.mk_pow, IntMod.sq_eq_one, QuotientGroup.mk_one]

theorem s15_LP_v1Sub_le {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) : v1Sub D.M V₀ V hV L ≤ V := by
  by_cases h0 : V₀ = ⊥
  · rw [v1Sub_of_eq_bot D.M V₀ V hV L h0]
    refine iSup_le fun m => ?_
    intro x hx
    rw [mem_conjSubgroup_iff] at hx
    have hxW : (m : G) * x * (m : G)⁻¹ ∈ wSub V₀ V hV L := hx.1
    have hxV : (m : G) * x * (m : G)⁻¹ ∈ V := preTil_le V₀ V hV _ hxW
    have hm : (m : G) ∈ normalizer (V : Set G) := h.pairFacts.le_normalizer m.2
    exact (Subgroup.mem_normalizer_iff.1 hm x).2 hxV
  · rw [v1Sub_of_ne_bot D.M V₀ V hV L h0]
    exact h.pairFacts.le

theorem s15_LP_le_normalizer_v1Sub {D : Data G} {V₀ V L : Subgroup G} (h : Hyp125 D V₀ V)
    (hV : IsElemAbelian 2 V) : D.M ≤ normalizer (v1Sub D.M V₀ V hV L : Set G) := by
  by_cases h0 : V₀ = ⊥
  · set X : Subgroup G := wSub V₀ V hV L ⊓ centralizer (L : Set G) with hX
    have hV₁ : v1Sub D.M V₀ V hV L = ⨆ m : ↥D.M, conjSubgroup X (m : G) :=
      v1Sub_of_eq_bot D.M V₀ V hV L h0
    have hmain : ∀ x ∈ D.M, conjSubgroup (v1Sub D.M V₀ V hV L) x ≤ v1Sub D.M V₀ V hV L := by
      intro x hx
      rw [hV₁]
      have hmap : conjSubgroup (⨆ m : ↥D.M, conjSubgroup X (m : G)) x =
          ⨆ m : ↥D.M, conjSubgroup (conjSubgroup X (m : G)) x := by
        simpa only [conjSubgroup] using
          (Subgroup.map_iSup (G := G) (N := G)
            (f := (MulAut.conj x⁻¹ : MulAut G).toMonoidHom)
            (s := fun m : ↥D.M => conjSubgroup X (m : G)))
      rw [hmap]
      refine iSup_le fun m => ?_
      rw [conjSubgroup_conjSubgroup]
      exact le_iSup (fun m' : ↥D.M => conjSubgroup X (m' : G)) ⟨(m : G) * x, D.M.mul_mem m.2 hx⟩
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    have h1 : conjSubgroup (v1Sub D.M V₀ V hV L) x ≤ v1Sub D.M V₀ V hV L := hmain x hx
    have h2 : conjSubgroup (v1Sub D.M V₀ V hV L) x⁻¹ ≤ v1Sub D.M V₀ V hV L :=
      hmain x⁻¹ (D.M.inv_mem hx)
    have h3 : conjSubgroup (conjSubgroup (v1Sub D.M V₀ V hV L) x⁻¹) x ≤
        conjSubgroup (v1Sub D.M V₀ V hV L) x := Subgroup.map_mono h2
    have h4 : v1Sub D.M V₀ V hV L ≤ conjSubgroup (v1Sub D.M V₀ V hV L) x := by
      rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h3
      exact h3
    have hEq : conjSubgroup (v1Sub D.M V₀ V hV L) x = v1Sub D.M V₀ V hV L :=
      le_antisymm h1 h4
    intro h
    rw [← mem_conjSubgroup_iff, hEq]
  · rw [v1Sub_of_ne_bot D.M V₀ V hV L h0]
    exact h.pairFacts.le_normalizer₀

theorem s15_LP_isElemAbelian_conj_wSub_sup_v1Sub {D : Data G} {V₀ V L : Subgroup G}
    (h : Hyp125 D V₀ V) (hV : IsElemAbelian 2 V) (g : G) :
    IsElemAbelian 2 (conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g) := by
  have hWV : wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L ≤ V :=
    sup_le (preTil_le V₀ V hV _) (s15_LP_v1Sub_le h hV)
  exact E3.isElemAbelian_conjSubgroup (h.isElemAbelian.mono hWV) g

theorem s15_LP_isPGroup_barSub {V₀ V B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hB : IsPGroup 2 B) : IsPGroup 2 (barSub V₀ V hV B) := by
  have hsub : IsPGroup 2 (B.subgroupOf (stabTil V₀ V)) :=
    IsPGroup.comap_subtype (H := B) (K := stabTil V₀ V) hB
  unfold barSub
  exact IsPGroup.of_card_dvd_pow (hsub.exists_card_eq.choose_spec ▸
    Subgroup.card_map_dvd (H := B.subgroupOf (stabTil V₀ V)) (f := actTil V₀ V hV))

private theorem mQuot_barSub_preBarSub_private {V₀ V B : Subgroup G}
    (hV : IsElemAbelian 2 V) (hB : B ≤ stabTil V₀ V)
    {C : Subgroup (MulAut (Vtil V₀ V hV))} (hC : C ≤ barSub V₀ V hV B) :
    E3.mQuot (barSub V₀ V hV B) C = E3.mQuot B (preBarSub B V₀ V hV C) := by
  let f : B →* MulAut (Vtil V₀ V hV) :=
    { toFun := fun b => actTil V₀ V hV ⟨b.1, hB b.2⟩
      map_one' := by
        show actTil V₀ V hV ⟨(1 : B).1, hB (1 : B).2⟩ = 1
        rw [show (⟨(1 : B).1, hB (1 : B).2⟩ : stabTil V₀ V) = 1 from
          Subtype.ext (Subgroup.coe_one B)]
        exact map_one (actTil V₀ V hV)
      map_mul' := by
        intro a b
        show actTil V₀ V hV ⟨(a * b).1, hB (a * b).2⟩ =
          actTil V₀ V hV ⟨a.1, hB a.2⟩ * actTil V₀ V hV ⟨b.1, hB b.2⟩
        rw [show (⟨(a * b).1, hB (a * b).2⟩ : stabTil V₀ V) =
          ⟨a.1, hB a.2⟩ * ⟨b.1, hB b.2⟩ from Subtype.ext rfl]
        exact map_mul (actTil V₀ V hV) _ _ }
  have hfrange : f.range = barSub V₀ V hV B := by
    ext φ
    constructor
    · rintro ⟨b, rfl⟩
      exact actTil_mem_barSub V₀ V hV b.2 (hB b.2)
    · intro hφ
      obtain ⟨g, hg, hgφ⟩ := (mem_barSub V₀ V hV B φ).1 hφ
      exact ⟨⟨g.1, hg⟩, by simpa [f] using hgφ⟩
  set D : Subgroup G := preBarSub B V₀ V hV C with hDdef
  have hDB : D ≤ B := inf_le_left
  have hmapD : map f (D.subgroupOf B) = barSub V₀ V hV D := by
    ext φ
    constructor
    · rintro ⟨b, hb, rfl⟩
      exact actTil_mem_barSub V₀ V hV hb (hB b.2)
    · intro hφ
      obtain ⟨g, hg, hgφ⟩ := (mem_barSub V₀ V hV D φ).1 hφ
      exact ⟨⟨g.1, hDB hg⟩, hg, by simpa [f] using hgφ⟩
  have hfD : map f (D.subgroupOf B) = C := by
    rw [hmapD, barSub_preBarSub]
    exact inf_eq_left.2 hC
  have hker_le : f.ker ≤ D.subgroupOf B := by
    intro b hb
    rw [Subgroup.mem_subgroupOf]
    refine (mem_preBarSub B V₀ V hV C).2 ⟨b.2, hB b.2, ?_⟩
    have hb' : actTil V₀ V hV ⟨b.1, hB b.2⟩ = 1 := by simpa [f] using hb
    rw [hb']
    exact C.one_mem
  have hr := Subgroup.relIndex_map_map f (D.subgroupOf B) (⊤ : Subgroup B)
  rw [hfD, show map f (⊤ : Subgroup B) = f.range from (MonoidHom.range_eq_map f).symm,
    hfrange] at hr
  rw [sup_eq_left.2 hker_le, top_sup_eq] at hr
  rw [Subgroup.relIndex_top_right] at hr
  unfold E3.mQuot
  rw [hr]
  rfl

theorem s15_LP_mQuot_barSub_preBarSub {V₀ V B : Subgroup G} (hV : IsElemAbelian 2 V)
    (hB : B ≤ stabTil V₀ V) {C : Subgroup (MulAut (Vtil V₀ V hV))}
    (hC : C ≤ barSub V₀ V hV B) :
    E3.mQuot (barSub V₀ V hV B) C = E3.mQuot B (preBarSub B V₀ V hV C) :=
  mQuot_barSub_preBarSub_private hV hB hC

theorem s15_LP_rk_autSub_eq_mQuot {W : Type*} [CommGroup W] [Finite W]
    {A : Subgroup (MulAut W)} {U : Subgroup W} (hA : A ≤ stabSub U) :
    rk ↥(autSub A U) = E3.mQuot A (A ⊓ centSub U) := by
  have h1 := card_autSub_mul hA
  have h2 := Subgroup.relIndex_mul_card (A ⊓ centSub U) A
  rw [inf_eq_left.2 inf_le_left] at h2
  have hpos : 0 < Nat.card ↥(A ⊓ centSub U) := Nat.card_pos
  have heq : Nat.card ↥(autSub A U) = (A ⊓ centSub U).relIndex A :=
    Nat.eq_of_mul_eq_mul_right hpos (by rw [h1, h2])
  unfold rk E3.mQuot
  rw [heq]

private theorem s15_LP_fixV_ne_bot_of_two_group {W : Type*} [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) [Nontrivial W]
    {P : Subgroup (MulAut W)} (hP : IsPGroup 2 ↥P) : fixV P ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmod := hP.card_modEq_card_fixedPoints W
  have hfix : Nat.card (MulAction.fixedPoints ↥P W) = Nat.card (fixV P) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun v => ?_)
    constructor
    · intro h x hx
      exact h ⟨x, hx⟩
    · intro h x
      exact h x x.2
  rw [hfix] at hmod
  have hV2 : IsPGroup 2 W := fun v => ⟨1, by rw [pow_one]; exact hW2 v⟩
  obtain ⟨n, hn⟩ := hV2.exists_card_eq
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hn
    exact (Finite.one_lt_card_iff_nontrivial.mpr inferInstance).ne' hn
  have heven : Nat.card W % 2 = 0 := by
    rw [hn]
    exact Nat.mod_eq_zero_of_dvd (dvd_pow_self 2 hn0)
  intro hbot
  rw [hbot, Subgroup.card_bot] at hmod
  have := hmod.symm
  unfold Nat.ModEq at this
  omega

private theorem s15_LP_exists_fixMod_of_lt {W : Type*} [CommGroup W] [Finite W]
    (hW2 : ∀ w : W, w ^ 2 = 1) {Q : Subgroup (MulAut W)}
    (hQ : IsPGroup 2 ↥Q) {E : Subgroup W} (hQE : Q ≤ stabSub E) (hE : E ≠ ⊤) :
    ∃ w : W, w ∉ E ∧ ∀ q ∈ Q, q w * w⁻¹ ∈ E := by
  classical
  set ψ : ↥Q →* MulAut (W ⧸ E) := (quotHom E).comp (Subgroup.inclusion hQE) with hψ
  have hnt : Nontrivial (W ⧸ E) := by
    obtain ⟨w, hw⟩ : ∃ w : W, w ∉ E := by
      by_contra h
      exact hE (eq_top_iff.mpr fun w _ => by
        by_contra hw
        exact h ⟨w, hw⟩)
    refine ⟨⟨QuotientGroup.mk w, 1, fun h => hw ?_⟩⟩
    rwa [QuotientGroup.eq_one_iff] at h
  have hW2' : ∀ z : W ⧸ E, z ^ 2 = 1 := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_pow, hW2, QuotientGroup.mk_one]
  have hP : IsPGroup 2 ↥ψ.range := hQ.of_surjective ψ.rangeRestrict ψ.rangeRestrict_surjective
  have hfix := s15_LP_fixV_ne_bot_of_two_group hW2' hP
  obtain ⟨z, hzfix, hz1⟩ : ∃ z, z ∈ fixV ψ.range ∧ z ≠ 1 := by
    by_contra h
    exact hfix (eq_bot_iff.mpr fun z hz => (Subgroup.mem_bot).mpr (by
      by_contra hz1
      exact h ⟨z, hz, hz1⟩))
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective z
  refine ⟨w, fun hw => hz1 ((QuotientGroup.eq_one_iff w).mpr hw), fun q hq => ?_⟩
  have h1 : ψ ⟨q, hq⟩ (QuotientGroup.mk w) = QuotientGroup.mk w := hzfix _ ⟨⟨q, hq⟩, rfl⟩
  have h2 : (QuotientGroup.mk (q w) : W ⧸ E) = QuotientGroup.mk w := h1
  exact (CFSG.Quasithin.mk_eq_mk_iff _ _).mp h2

theorem s15_LP_exists_stable_hyperplane {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} (hA : IsPGroup 2 A) {U : Subgroup W}
    (hU : U ≠ ⊥) (hAU : A ≤ stabSub U) :
    ∃ U₀ : Subgroup W, U₀ ≤ U ∧ E3.mQuot U U₀ = 1 ∧ A ≤ stabSub U₀ := by
  classical
  have hAbot : A ≤ stabSub (⊥ : Subgroup W) := by
    intro a _ u
    constructor
    · intro h
      have h1 : a u = 1 := Subgroup.mem_bot.1 h
      have : u = a.symm 1 := by rw [← h1]; simp
      simpa using this
    · intro h
      rw [Subgroup.mem_bot.1 h, map_one]
      exact Subgroup.one_mem _
  let S : Set (Subgroup W) := {H | H ≤ U ∧ H ≠ U ∧ A ≤ stabSub H}
  have hSne : S.Nonempty :=
    ⟨⊥, bot_le, by simpa [eq_comm] using hU, hAbot⟩
  obtain ⟨H, hHmem, hHmax⟩ := (Set.toFinite S).exists_maximal hSne
  obtain ⟨hHU, hHUne, hAH⟩ := hHmem
  have hHtop : H ≠ ⊤ := by
    intro h
    exact hHUne (le_antisymm hHU (by rw [h]; exact le_top))
  have hA' : IsPGroup 2 (autSub A U) := by
    have hsub : IsPGroup 2 (A.subgroupOf (stabSub U)) :=
      IsPGroup.comap_subtype (H := A) (K := stabSub U) hA
    unfold autSub
    exact IsPGroup.of_card_dvd_pow (hsub.exists_card_eq.choose_spec ▸
      Subgroup.card_map_dvd (H := A.subgroupOf (stabSub U)) (f := resHom U))
  have hA'H : autSub A U ≤ stabSub (H.subgroupOf U) := by
    intro φ hφ
    obtain ⟨g, hgA, rfl⟩ := mem_autSub.1 hφ
    refine mem_stabSub.2 fun x => ?_
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply]
    exact mem_stabSub.1 (hAH hgA) (x : W)
  have hHproper : H.subgroupOf U ≠ ⊤ := by
    intro h
    have hUH : U ≤ H := by
      intro x hx
      have hx' : (⟨x, hx⟩ : U) ∈ H.subgroupOf U := by rw [h]; trivial
      exact hx'
    exact hHUne (le_antisymm hHU hUH)
  have hWU : ∀ u : ↥U, u ^ 2 = 1 := by
    intro u
    ext
    simpa using hW (u : W)
  obtain ⟨w, hwH, hwfix⟩ :=
    s15_LP_exists_fixMod_of_lt (W := ↥U) (Q := autSub A U)
      (E := H.subgroupOf U) hWU hA' hA'H hHproper
  have haw_mem : ∀ a ∈ A, (a : MulAut W) (w : W) ∈ H ⊔ Subgroup.zpowers (w : W) := by
    intro a ha
    have hq : resHom U ⟨a, hAU ha⟩ ∈ autSub A U :=
      mem_autSub.2 ⟨⟨a, hAU ha⟩, ha, rfl⟩
    have hmem := hwfix _ hq
    have hmemH : (((resHom U ⟨a, hAU ha⟩) w : U) : W) * (w : W)⁻¹ ∈ H :=
      Subgroup.mem_subgroupOf.1 hmem
    rw [resHom_apply] at hmemH
    have heq : (a : MulAut W) (w : W) = ((a : MulAut W) (w : W) * (w : W)⁻¹) * (w : W) := by
      group
    rw [heq]
    exact Subgroup.mul_mem_sup hmemH (Subgroup.mem_zpowers (w : W))
  let K : Subgroup W := H ⊔ Subgroup.zpowers (w : W)
  have hKle : K ≤ U := sup_le hHU (Subgroup.zpowers_le.2 w.2)
  have hfwd : ∀ a ∈ A, ∀ k ∈ K, (a : MulAut W) k ∈ K := by
    intro a ha k hk
    obtain ⟨h, hh, w', hw', rfl⟩ := Subgroup.mem_sup.1 hk
    have haw : (a : MulAut W) (w : W) ∈ K := haw_mem a ha
    have hw'K : (a : MulAut W) w' ∈ K := by
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hw'
      rw [← hn, map_zpow]
      exact K.zpow_mem haw n
    rw [map_mul]
    exact K.mul_mem (Subgroup.mem_sup_left ((mem_stabSub.1 (hAH ha) h).2 hh)) hw'K
  have hAK : A ≤ stabSub K := by
    intro a ha
    refine mem_stabSub.2 fun k => ?_
    constructor
    · intro hk
      have h1 : (a⁻¹ : MulAut W) ∈ A := A.inv_mem ha
      have h2 := hfwd a⁻¹ h1 _ hk
      simpa using h2
    · exact hfwd a ha k
  have hKU : K = U := by
    by_contra hne
    have hKS : K ∈ S := ⟨hKle, hne, hAK⟩
    have hKH : K ≤ H := hHmax hKS le_sup_left
    exact hwH (Subgroup.mem_subgroupOf.2
      (hKH (Subgroup.mem_sup_right (Subgroup.mem_zpowers (w : W)))))
  have hw1 : (w : W) ≠ 1 := by
    intro h
    exact hwH (Subgroup.mem_subgroupOf.2 (by rw [h]; exact H.one_mem))
  have hcardw : Nat.card (Subgroup.zpowers (w : W)) = 2 := by
    rw [Nat.card_zpowers, orderOf_eq_prime (hW (w : W)) hw1]
  have hcardinf : Nat.card ↥(H ⊓ Subgroup.zpowers (w : W)) = 1 := by
    have hdvd : Nat.card ↥(H ⊓ Subgroup.zpowers (w : W)) ∣ 2 :=
      hcardw ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
    · exact h
    · exfalso
      have htop : H ⊓ Subgroup.zpowers (w : W) = Subgroup.zpowers (w : W) := by
        refine Subgroup.eq_of_le_of_card_ge inf_le_right ?_
        rw [h, hcardw]
      have hwP : (w : W) ∈ H ⊓ Subgroup.zpowers (w : W) := by
        rw [htop]
        exact Subgroup.mem_zpowers (w : W)
      exact hwH (Subgroup.mem_subgroupOf.2 hwP.1)
  have hrelcard : H.relIndex (Subgroup.zpowers (w : W)) = 2 := by
    have h := Subgroup.relIndex_mul_card H (Subgroup.zpowers (w : W))
    rw [hcardinf, hcardw, mul_one] at h
    exact h
  have hidxK : H.relIndex K = 2 := by
    rw [show K = H ⊔ Subgroup.zpowers (w : W) from rfl, Subgroup.relIndex_sup_left]
    exact hrelcard
  have hidxU : H.relIndex U = 2 := by
    rw [← hKU]
    exact hidxK
  refine ⟨H, hHU, ?_, hAH⟩
  unfold E3.mQuot
  rw [hidxU]
  simp

theorem s15_LP_mul_inv_mem_of_mQuot_le_one {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {U N : Subgroup W} (hNU : N ≤ U)
    (hAU : A ≤ stabSub U) (hAN : A ≤ stabSub N) (hq : E3.mQuot U N ≤ 1) :
    ∀ a ∈ A, ∀ u ∈ U, a u * u⁻¹ ∈ N := by
  have hW2 : IsPGroup 2 W := isPGroup_two_of_sq_eq_one hW
  have hU2 : IsPGroup 2 U := hW2.to_subgroup U
  intro a ha u hu
  by_cases hNUeq : N = U
  · rw [hNUeq] at hAN ⊢
    exact Subgroup.mul_mem _ ((mem_stabSub.1 (hAU ha) u).2 hu) (Subgroup.inv_mem _ hu)
  · have hmq : E3.mQuot U N = 1 := by
      have h0 : E3.mQuot U N ≠ 0 := by
        intro h
        exact hNUeq ((E3.mQuot_eq_zero_iff hU2 hNU).1 h)
      omega
    have hidx : N.relIndex U = 2 := by
      rw [E3.relIndex_eq_two_pow hU2 N, hmq, pow_one]
    have hidx' : (N.subgroupOf U).index = 2 := hidx
    by_cases huN : u ∈ N
    · exact N.mul_mem ((mem_stabSub.1 (hAN ha) u).2 huN) (N.inv_mem huN)
    · have hmemu : (⟨u, hu⟩ : U) ∉ N.subgroupOf U := fun h => huN (Subgroup.mem_subgroupOf.1 h)
      have hmemau : (⟨a u, (mem_stabSub.1 (hAU ha) u).2 hu⟩ : U) ∉ N.subgroupOf U := by
        intro h
        exact huN ((mem_stabSub.1 (hAN ha) u).1 (Subgroup.mem_subgroupOf.1 h))
      have hmemu_inv : (⟨u⁻¹, U.inv_mem hu⟩ : U) ∉ N.subgroupOf U := by
        intro h
        exact huN (by simpa using N.inv_mem (Subgroup.mem_subgroupOf.1 h))
      have hmul : (⟨a u, (mem_stabSub.1 (hAU ha) u).2 hu⟩ : U) *
          (⟨u⁻¹, U.inv_mem hu⟩ : U) ∈ N.subgroupOf U :=
        (Subgroup.mul_mem_iff_of_index_two hidx').2
          ⟨fun h => absurd h hmemau, fun h => absurd h hmemu_inv⟩
      have := Subgroup.mem_subgroupOf.1 hmul
      simpa [Subgroup.coe_mul] using this

theorem s15_LP_mQuot_inf_centSub_zpowers_le {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} (hA : IsPGroup 2 A)
    {U U₀ : Subgroup W} (hU₀U : U₀ ≤ U) (hAq : ∀ a ∈ A, ∀ u ∈ U, a u * u⁻¹ ∈ U₀) {u : W}
    (hu : u ∈ U) : E3.mQuot A (A ⊓ centSub (Subgroup.zpowers u)) ≤ rk ↥U₀ := by
  letI : MulAction ↥A W := MulAction.compHom (α := W) A.subtype
  have hstab : MulAction.stabilizer ↥A u =
      (A ⊓ centSub (Subgroup.zpowers u)).subgroupOf A := by
    ext a
    rw [MulAction.mem_stabilizer_iff, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
      MulAction.compHom_smul_def, MulAut.smul_def]
    constructor
    · intro h
      change (a : MulAut W) u = u at h
      refine ⟨a.2, mem_centSub.2 fun z hz => ?_⟩
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hz
      rw [← hn, map_zpow, h]
    · rintro ⟨-, hc⟩
      exact mem_centSub.1 hc u (Subgroup.mem_zpowers u)
  have hIm : ∀ x : MulAction.orbit ↥A u, ((x : W) * u⁻¹) ∈ U₀ := by
    intro x
    obtain ⟨a, ha⟩ := MulAction.mem_orbit_iff.1 x.2
    have ha' : (a : MulAut W) u = (x : W) := by
      simpa [MulAction.compHom_smul_def, MulAut.smul_def] using ha
    rw [← ha']
    exact hAq a a.2 u hu
  let δ : MulAction.orbit ↥A u → ↥U₀ := fun x => ⟨(x : W) * u⁻¹, hIm x⟩
  have hδinj : Function.Injective δ := by
    intro x y hxy
    have h1 : (x : W) * u⁻¹ = (y : W) * u⁻¹ := congrArg Subtype.val hxy
    have h2 : (x : W) = (y : W) := mul_right_cancel h1
    exact Subtype.ext h2
  have hcard : Nat.card (MulAction.orbit ↥A u) ≤ Nat.card U₀ :=
    Nat.card_le_card_of_injective δ hδinj
  have hindex := MulAction.index_stabilizer ↥A u
  have hidxeq : (A ⊓ centSub (Subgroup.zpowers u)).relIndex A =
      Nat.card (MulAction.orbit ↥A u) := by
    rw [show Nat.card (MulAction.orbit ↥A u) = (MulAction.orbit ↥A u).ncard from
      Nat.card_coe_set_eq _]
    rw [← hindex, hstab]
    rfl
  rw [← hidxeq] at hcard
  rw [E3.relIndex_eq_two_pow hA (A ⊓ centSub (Subgroup.zpowers u)),
    card_eq_two_pow hW U₀] at hcard
  exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard

theorem s15_LP_rk_autSub_le_rk_of_trivial {W : Type*} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {A : Subgroup (MulAut W)} {U N : Subgroup W} (hNU : N ≤ U)
    (hA : A ≤ stabSub U) (hAN : A ≤ centSub N) (hAq : ∀ a ∈ A, ∀ u ∈ U, a u * u⁻¹ ∈ N)
    (hq : E3.mQuot U N ≤ 1) : rk ↥(autSub A U) ≤ rk ↥N := by
  by_cases hNUeq : N = U
  · rw [hNUeq] at hAN ⊢
    have hbot : autSub A U = ⊥ := by
      rw [eq_bot_iff]
      intro φ hφ
      obtain ⟨g, hgA, rfl⟩ := mem_autSub.1 hφ
      rw [Subgroup.mem_bot]
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [resHom_apply]
      exact mem_centSub.1 (hAN hgA) (x : W) x.2
    rw [hbot, rk_bot]
    exact Nat.zero_le _
  · have hW2 : IsPGroup 2 W := isPGroup_two_of_sq_eq_one hW
    have hU2 : IsPGroup 2 U := hW2.to_subgroup U
    have hmq : E3.mQuot U N = 1 := by
      have h0 : E3.mQuot U N ≠ 0 := by
        intro h
        exact hNUeq ((E3.mQuot_eq_zero_iff hU2 hNU).1 h)
      omega
    have hidx : N.relIndex U = 2 := by
      rw [E3.relIndex_eq_two_pow hU2 N, hmq, pow_one]
    have hidx' : (N.subgroupOf U).index = 2 := hidx
    obtain ⟨u₀, hu₀U, hu₀N⟩ : ∃ u₀ ∈ U, u₀ ∉ N := by
      by_contra h
      apply hNUeq
      refine le_antisymm hNU fun x hx => ?_
      by_contra hxN
      exact h ⟨x, hx, hxN⟩
    have hxmul : ∀ x : U, (x : W) ∉ N → ((x : W) * u₀⁻¹) ∈ N := by
      intro x hx
      have hx' : x ∉ N.subgroupOf U := fun h => hx (Subgroup.mem_subgroupOf.1 h)
      have hu0' : (⟨u₀⁻¹, U.inv_mem hu₀U⟩ : U) ∉ N.subgroupOf U := by
        intro h
        exact hu₀N (by simpa using N.inv_mem (Subgroup.mem_subgroupOf.1 h))
      have hmul : x * (⟨u₀⁻¹, U.inv_mem hu₀U⟩ : U) ∈ N.subgroupOf U :=
        (Subgroup.mul_mem_iff_of_index_two hidx').2
          ⟨fun h => absurd h hx', fun h => absurd h hu0'⟩
      have := Subgroup.mem_subgroupOf.1 hmul
      simpa [Subgroup.coe_mul] using this
    let δ : ↥(autSub A U) → ↥N := fun φ =>
      ⟨((φ.1 ⟨u₀, hu₀U⟩ : U) : W) * u₀⁻¹, by
        obtain ⟨g, hgA, hgφ⟩ := mem_autSub.1 φ.2
        rw [← hgφ, resHom_apply]
        exact hAq g hgA u₀ hu₀U⟩
    have hδinj : Function.Injective δ := by
      intro φ ψ hφψ
      have hval : ((φ.1 ⟨u₀, hu₀U⟩ : U) : W) * u₀⁻¹ =
          ((ψ.1 ⟨u₀, hu₀U⟩ : U) : W) * u₀⁻¹ := congrArg Subtype.val hφψ
      have hwu : ((φ.1 ⟨u₀, hu₀U⟩ : U) : W) = ((ψ.1 ⟨u₀, hu₀U⟩ : U) : W) :=
        mul_right_cancel hval
      obtain ⟨g, hgA, hgφ⟩ := mem_autSub.1 φ.2
      obtain ⟨g', hg'A, hg'ψ⟩ := mem_autSub.1 ψ.2
      have hwu' : ((resHom U g) ⟨u₀, hu₀U⟩ : U) = ((resHom U g') ⟨u₀, hu₀U⟩ : U) := by
        apply Subtype.ext
        rw [resHom_apply, resHom_apply]
        rw [← hgφ, ← hg'ψ] at hwu
        exact hwu
      have hwuW : ((g : MulAut W) u₀) = ((g' : MulAut W) u₀) := by
        have := congrArg (fun z : U => (z : W)) hwu'
        simpa [resHom_apply] using this
      apply Subtype.ext
      apply MulEquiv.ext
      intro x
      apply Subtype.ext
      rw [← hgφ, ← hg'ψ]
      by_cases hxN : (x : W) ∈ N
      · rw [resHom_apply, resHom_apply,
          mem_centSub.1 (hAN hgA) (x : W) hxN,
          mem_centSub.1 (hAN hg'A) (x : W) hxN]
      · have hxm : (x : W) * u₀⁻¹ ∈ N := hxmul x hxN
        have hxeq : (x : W) = ((x : W) * u₀⁻¹) * u₀ := by group
        calc ((resHom U g x : U) : W)
            = (g : MulAut W) x := by rw [resHom_apply]
          _ = (g : MulAut W) (((x : W) * u₀⁻¹) * u₀) := congrArg _ hxeq
          _ = (g : MulAut W) ((x : W) * u₀⁻¹) * (g : MulAut W) u₀ :=
              map_mul (g : MulAut W) ((x : W) * u₀⁻¹) u₀
          _ = ((x : W) * u₀⁻¹) * (g : MulAut W) u₀ := by
              rw [mem_centSub.1 (hAN hgA) _ hxm]
          _ = ((x : W) * u₀⁻¹) * (g' : MulAut W) u₀ := by rw [hwuW]
          _ = (g' : MulAut W) ((x : W) * u₀⁻¹) * (g' : MulAut W) u₀ := by
              rw [mem_centSub.1 (hAN hg'A) _ hxm]
          _ = (g' : MulAut W) (((x : W) * u₀⁻¹) * u₀) :=
              (map_mul (g' : MulAut W) ((x : W) * u₀⁻¹) u₀).symm
          _ = (g' : MulAut W) x := congrArg _ hxeq.symm
          _ = ((resHom U g' x : U) : W) := by rw [resHom_apply]
    have hcard : Nat.card ↥(autSub A U) ≤ Nat.card ↥N :=
      Nat.card_le_card_of_injective δ hδinj
    have hdvd : 2 ^ rk ↥(autSub A U) ∣ Nat.card ↥(autSub A U) := pow_padicValNat_dvd
    have hcard' : 2 ^ rk ↥(autSub A U) ≤ Nat.card ↥N :=
      (Nat.le_of_dvd Nat.card_pos hdvd).trans hcard
    rw [card_eq_two_pow hW N] at hcard'
    exact (Nat.pow_le_pow_iff_right (by norm_num)).1 hcard' 

theorem s15_LP_preTil_mono {V₀ V : Subgroup G} (hV : IsElemAbelian 2 V)
    {S T : Subgroup (Vtil V₀ V hV)} (h : S ≤ T) :
    preTil V₀ V hV S ≤ preTil V₀ V hV T := by
  intro g hg
  obtain ⟨x, rfl, hx⟩ := (mem_preTil V₀ V hV S).1 hg
  exact (mem_preTil V₀ V hV T).2 ⟨x, rfl, h hx⟩

theorem s15_LP_imgTil_mono {V₀ V N U : Subgroup G} (hV : IsElemAbelian 2 V) (h : N ≤ U) :
    imgTil V₀ V hV N ≤ imgTil V₀ V hV U := by
  intro q hq
  obtain ⟨x, hx, rfl⟩ := (mem_imgTil V₀ V hV N q).1 hq
  exact (mem_imgTil V₀ V hV U _).2 ⟨x, h hx, rfl⟩

theorem s15_LP_imgTil_inf_preTil {V₀ V W : Subgroup G} (hV : IsElemAbelian 2 V) (hW : W ≤ V)
    {S : Subgroup (Vtil V₀ V hV)} (hS : S ≤ imgTil V₀ V hV W) :
    imgTil V₀ V hV (W ⊓ preTil V₀ V hV S) = S := by
  ext q
  rw [mem_imgTil]
  constructor
  · rintro ⟨x, ⟨hxW, hxS⟩, rfl⟩
    obtain ⟨y, hy, hyS⟩ := (mem_preTil V₀ V hV S).1 hxS
    rwa [IntMod.val_injective hy] at hyS
  · intro hq
    obtain ⟨x, hxW, rfl⟩ := (mem_imgTil V₀ V hV W q).1 (hS hq)
    exact ⟨x, ⟨hxW, (mem_preTil_iff_of_mem V₀ V hV S x.val_mem).2 hq⟩, rfl⟩

theorem s15_LP_mQuot_imgTil_le {V₀ V N U : Subgroup G} (hV : IsElemAbelian 2 V) (hNU : N ≤ U)
    (hU : U ≤ V) :
    E3.mQuot (imgTil V₀ V hV U) (imgTil V₀ V hV N) ≤ E3.mQuot U N := by
  let f := mkTil V₀ V hV
  let U' := intSub V hV U
  let N' := intSub V hV N
  have hN'U' : N' ≤ U' := fun x hx => hNU hx
  have hmq : E3.mQuot U N = padicValNat 2 (N'.relIndex U') := by
    unfold E3.mQuot
    dsimp only [U', N', intSub]
    exact congrArg (padicValNat 2)
      (Subgroup.relIndex_subgroupOf (H := N) (K := U) (L := V) hU).symm
  have hstep : E3.mQuot (imgTil V₀ V hV U) (imgTil V₀ V hV N) =
      padicValNat 2 ((N'.map f).relIndex (U'.map f)) := rfl
  rw [hstep, hmq]
  have hKnorm : (N' ⊔ f.ker).Normal := inferInstance
  have hrel : (N'.map f).relIndex (U'.map f) = (N' ⊔ f.ker).relIndex U' := by
    rw [Subgroup.relIndex_map_map]
    have hsup : U' ⊔ f.ker = U' ⊔ (N' ⊔ f.ker) := by
      rw [← sup_assoc, sup_eq_left.2 hN'U']
    rw [hsup, Subgroup.relIndex_sup_right]
  rw [hrel]
  exact padicValNat_two_le_of_dvd (E3.relIndex_ne_zero' U' N')
    (Subgroup.relIndex_dvd_of_le_left (H := N') (K := N' ⊔ f.ker) (L := U') le_sup_left)

theorem s15_LP_barSub_le_centSub_imgTil {V₀ V B N : Subgroup G} (hV : IsElemAbelian 2 V)
    (hB : B ≤ stabTil V₀ V) (hBN : B ≤ centralizer (N : Set G)) :
    barSub V₀ V hV B ≤ centSub (imgTil V₀ V hV N) := by
  intro φ hφ
  obtain ⟨b, hb, rfl⟩ := (mem_barSub V₀ V hV B φ).1 hφ
  refine mem_centSub.2 fun q hq => ?_
  obtain ⟨x, hxN, rfl⟩ := (mem_imgTil V₀ V hV N q).1 hq
  rw [actTil_mk]
  have hcomm : b.1 * x.val = x.val * b.1 :=
    (Subgroup.mem_centralizer_iff.1 (hBN hb) x.val hxN).symm
  have hval : (actStab V₀ V hV b x).val = x.val := by
    rw [actStab_apply_val, hcomm]
    group
  rw [show actStab V₀ V hV b x = x from IntMod.val_injective hval]

theorem s15_LP_barSub_le_stabSub_imgTil {V₀ V B U : Subgroup G} (hV : IsElemAbelian 2 V)
    (hB : B ≤ stabTil V₀ V) (hBU : B ≤ normalizer (U : Set G)) :
    barSub V₀ V hV B ≤ stabSub (imgTil V₀ V hV U) := by
  have hfwd : ∀ (b : stabTil V₀ V), (b : G) ∈ B → ∀ q : Vtil V₀ V hV,
      q ∈ imgTil V₀ V hV U → actTil V₀ V hV b q ∈ imgTil V₀ V hV U := by
    intro b hb q hq
    obtain ⟨x, hxU, rfl⟩ := (mem_imgTil V₀ V hV U q).1 hq
    rw [actTil_mk, mem_imgTil]
    refine ⟨actStab V₀ V hV b x, ?_, rfl⟩
    rw [actStab_apply_val]
    exact (Subgroup.mem_normalizer_iff.1 (hBU hb) x.val).1 hxU
  intro φ hφ
  obtain ⟨b, hb, rfl⟩ := (mem_barSub V₀ V hV B φ).1 hφ
  refine mem_stabSub.2 fun q => ⟨fun hq => ?_, fun hq => ?_⟩
  · have h1 := hfwd (⟨b⁻¹, (stabTil V₀ V).inv_mem b.2⟩ : stabTil V₀ V) (B.inv_mem hb)
      (actTil V₀ V hV b q) hq
    have hprod : (⟨b⁻¹, (stabTil V₀ V).inv_mem b.2⟩ : stabTil V₀ V) * b = 1 := by
      ext
      simp
    have h2 : actTil V₀ V hV ⟨b⁻¹, (stabTil V₀ V).inv_mem b.2⟩
        (actTil V₀ V hV b q) = q := by
      rw [← MulAut.mul_apply, ← map_mul, hprod, map_one]
      rfl
    rwa [h2] at h1
  · exact hfwd b hb q hq

theorem s15_LP_le_normalizer_of_stable {V₀ V B W : Subgroup G} (hV : IsElemAbelian 2 V)
    (hW : W ≤ V) (hB : B ≤ stabTil V₀ V) (hBW : B ≤ normalizer (W : Set G))
    {S : Subgroup (Vtil V₀ V hV)} (hBS : barSub V₀ V hV B ≤ stabSub S) :
    B ≤ normalizer ((W ⊓ preTil V₀ V hV S : Subgroup G) : Set G) := by
  have hfwd : ∀ (b : stabTil V₀ V), (b : G) ∈ B →
      ∀ x ∈ W ⊓ preTil V₀ V hV S, (b : G) * x * (b : G)⁻¹ ∈ W ⊓ preTil V₀ V hV S := by
    intro b hb x hx
    obtain ⟨hxW, hxS⟩ := hx
    have hxV : x ∈ V := hW hxW
    have hxq : mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ S :=
      (mem_preTil_iff_of_mem V₀ V hV S hxV).1 hxS
    have hbV : (b : G) * x * (b : G)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 b.2.1 x).1 hxV
    have hbW : (b : G) * x * (b : G)⁻¹ ∈ W :=
      (Subgroup.mem_normalizer_iff.1 (hBW hb) x).1 hxW
    have hbq : mkTil V₀ V hV (IntMod.mk hV ⟨(b : G) * x * (b : G)⁻¹, hbV⟩) ∈ S := by
      have hφ : actTil V₀ V hV b ∈ barSub V₀ V hV B :=
        actTil_mem_barSub V₀ V hV hb b.2
      have h1 : actTil V₀ V hV b (mkTil V₀ V hV (IntMod.mk hV ⟨x, hxV⟩)) ∈ S :=
        (mem_stabSub.1 (hBS hφ) _).2 hxq
      rw [actTil_mk] at h1
      have heq : actStab V₀ V hV b (IntMod.mk hV ⟨x, hxV⟩) =
          IntMod.mk hV ⟨(b : G) * x * (b : G)⁻¹, hbV⟩ := by
        apply IntMod.val_injective
        rw [actStab_apply_val]
        rfl
      rwa [heq] at h1
    exact ⟨hbW, (mem_preTil_iff_of_mem V₀ V hV S hbV).2 hbq⟩
  intro b hb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hfwd ⟨b, hB hb⟩ hb x
  · intro hx
    have h1 := hfwd ⟨b⁻¹, (stabTil V₀ V).inv_mem (hB hb)⟩ (B.inv_mem hb)
      (b * x * b⁻¹) hx
    convert h1 using 1
    group
theorem fifteen_nine_lp (D : Data G) {V₀ V L : Subgroup G} (h : Hyp151 D V₀ V L)
    (hV : IsElemAbelian 2 V) (hγ : 0 < gamma15 D.M V₀ V hV L) {g : G} {B : Subgroup G}
    (hB : B = conjSubgroup (wSub V₀ V hV L ⊔ v1Sub D.M V₀ V hV L) g) (hBM : B ≤ D.M)
    (hBW : B ≤ normalizer (wSub V₀ V hV L : Set G))
    (hS : gamma15 D.M V₀ V hV L ≤
      rk ↥(autSub (barSub (v1Sub D.M V₀ V hV L) V hV B) (wStar D.M V₀ V hV L)))
    (hQ : ∀ E : Subgroup G, E ≤ B → E3.mQuot B E < gamma15 D.M V₀ V hV L →
      wSub V₀ V hV L ⊓
        preTil (v1Sub D.M V₀ V hV L) V hV (fixV (barSub (v1Sub D.M V₀ V hV L) V hV E)) ≤
          conjSubgroup D.M g)
    (hR : ∀ Y : Subgroup G, Y ≤ wSub V₀ V hV L ⊓ conjSubgroup D.M g →
      B ≤ normalizer (Y : Set G) →
      ∃ N : Subgroup G, N ≤ Y ∧ B ≤ centralizer (N : Set G) ∧ E3.mQuot Y N ≤ 1) :
    False := by
  have h125 : Hyp125 D V₀ V := h.hyp125
  have hMs : D.M ≤ stabTil (v1Sub D.M V₀ V hV L) V :=
    le_stabTil h125.pairFacts.le_normalizer (s15_LP_le_normalizer_v1Sub h125 hV)
  have hB2 : IsPGroup 2 B := by
    rw [hB]
    exact (s15_LP_isElemAbelian_conj_wSub_sup_v1Sub (L := L) h125 hV g).isPGroup
  have hWV : wSub V₀ V hV L ≤ V := preTil_le _ _ _ _
  have hsq := s15_LP_vtil_sq_eq_one (v1Sub D.M V₀ V hV L) V hV
  have hγW : gamma15 D.M V₀ V hV L = rk ↥(wStar D.M V₀ V hV L) := rfl
  set V₁ := v1Sub D.M V₀ V hV L with hV₁
  set W := wSub V₀ V hV L with hWdef
  set Ws := wStar D.M V₀ V hV L with hWsdef
  set γ := gamma15 D.M V₀ V hV L with hγdef
  set Bb := barSub V₁ V hV B with hBbdef
  have hBs : B ≤ stabTil V₁ V := hBM.trans hMs
  have hBb2 : IsPGroup 2 Bb := s15_LP_isPGroup_barSub hV hB2
  have hst : Bb ≤ stabSub Ws := s15_LP_barSub_le_stabSub_imgTil hV hBs hBW
  have hp2 : IsPGroup 2 (Vtil V₁ V hV) := isPGroup_two_of_sq_eq_one hsq
  let 𝒰 : Set (Subgroup (Vtil V₁ V hV)) :=
    {U | U ≤ Ws ∧ Bb ≤ stabSub U ∧ γ ≤ rk ↥(autSub Bb U)}
  have hne : 𝒰.Nonempty := ⟨Ws, le_rfl, hst, hS⟩
  obtain ⟨U, ⟨hUW, hUst, hUγ⟩, hUmin⟩ :=
    Set.exists_min_image 𝒰 (fun U => Nat.card U) (Set.toFinite _) hne
  have hU0 : U ≠ ⊥ := by
    rintro rfl
    have h0 : rk ↥(autSub Bb (⊥ : Subgroup (Vtil V₁ V hV))) = 0 := by
      rw [s15_LP_rk_autSub_eq_mQuot hUst]
      have : Bb ⊓ centSub (⊥ : Subgroup _) = Bb := by
        rw [inf_eq_left]
        intro x _
        rw [mem_centSub]
        intro u hu
        rw [Subgroup.mem_bot.1 hu]
        exact map_one x
      rw [this]
      simp [E3.mQuot]
    omega
  obtain ⟨U₀, hU₀U, hq1, hBU₀⟩ := s15_LP_exists_stable_hyperplane hsq hBb2 hU0 hUst
  have hlt : rk ↥(autSub Bb U₀) < γ := by
    by_contra hge
    have hmem : U₀ ∈ 𝒰 := ⟨hU₀U.trans hUW, hBU₀, not_lt.1 hge⟩
    have hEq : U₀ = U := Subgroup.eq_of_le_of_card_ge hU₀U (hUmin U₀ hmem)
    rw [hEq] at hq1
    have h0 : E3.mQuot U U = 0 := (E3.mQuot_eq_zero_iff (hp2.to_subgroup U) le_rfl).2 rfl
    omega
  have key : ∀ C : Subgroup (MulAut (Vtil V₁ V hV)), C ≤ Bb → E3.mQuot Bb C < γ →
      ∀ x ∈ W, ∀ hx : x ∈ V,
        (∀ φ ∈ C, φ (mkTil V₁ V hV (IntMod.mk hV ⟨x, hx⟩)) =
          mkTil V₁ V hV (IntMod.mk hV ⟨x, hx⟩)) →
        x ∈ conjSubgroup D.M g := by
    intro C hC hCq x hxW hxV hfix
    have hq := s15_LP_mQuot_barSub_preBarSub hV hBs hC
    have hle : preBarSub B V₁ V hV C ≤ B := inf_le_left
    have hbar : barSub V₁ V hV (preBarSub B V₁ V hV C) ≤ C := by
      rw [barSub_preBarSub]
      exact inf_le_left
    refine hQ _ hle (hq ▸ hCq) ⟨hxW, (mem_preTil_iff_of_mem _ _ hV _ hxV).2 ?_⟩
    intro φ hφ
    exact hfix φ (hbar hφ)
  have hrkU : rk ↥U = rk ↥U₀ + 1 := by
    have h1 := E3.card_eq_two_pow_mul (hp2.to_subgroup U) hU₀U
    rw [hq1, card_eq_two_pow hsq U, card_eq_two_pow hsq U₀, pow_one, ← pow_succ'] at h1
    exact Nat.pow_right_injective (le_refl 2) h1
  have hrkγ : rk ↥U ≤ γ := hγW ▸ rk_mono hUW
  have hAq : ∀ a ∈ Bb, ∀ y ∈ U, a y * y⁻¹ ∈ U₀ :=
    s15_LP_mul_inv_mem_of_mQuot_le_one hsq hU₀U hUst hBU₀ (le_of_eq hq1)
  have hUg : W ⊓ preTil V₁ V hV U ≤ conjSubgroup D.M g := by
    rintro x ⟨hxW, hxU⟩
    have hxV : x ∈ V := hWV hxW
    have hxU' := (mem_preTil_iff_of_mem _ _ hV _ hxV).1 hxU
    by_cases hx0 : mkTil V₁ V hV (IntMod.mk hV ⟨x, hxV⟩) ∈ U₀
    · refine key (Bb ⊓ centSub U₀) inf_le_left ?_ x hxW hxV ?_
      · rwa [← s15_LP_rk_autSub_eq_mQuot hBU₀]
      · intro φ hφ
        exact mem_centSub.1 hφ.2 _ hx0
    · refine key (Bb ⊓ centSub (Subgroup.zpowers (mkTil V₁ V hV (IntMod.mk hV ⟨x, hxV⟩))))
        inf_le_left ?_ x hxW hxV ?_
      · exact lt_of_le_of_lt (s15_LP_mQuot_inf_centSub_zpowers_le hsq hBb2 hU₀U hAq hxU')
          (by omega)
      · intro φ hφ
        exact mem_centSub.1 hφ.2 _ (Subgroup.mem_zpowers _)
  have hBn : B ≤ normalizer ((W ⊓ preTil V₁ V hV U : Subgroup G) : Set G) :=
    s15_LP_le_normalizer_of_stable hV hWV hBs hBW hUst
  obtain ⟨N, hNY, hBN, hNq⟩ := hR _ (le_inf inf_le_left hUg) hBn
  have hiY : imgTil V₁ V hV (W ⊓ preTil V₁ V hV U) = U := s15_LP_imgTil_inf_preTil hV hWV hUW
  have hNsU : imgTil V₁ V hV N ≤ U := hiY ▸ s15_LP_imgTil_mono hV hNY
  have hq' : E3.mQuot U (imgTil V₁ V hV N) ≤ 1 := by
    have := s15_LP_mQuot_imgTil_le (V₀ := V₁) hV hNY (inf_le_left.trans hWV)
    rw [hiY] at this
    exact this.trans hNq
  have hcent : Bb ≤ centSub (imgTil V₁ V hV N) := s15_LP_barSub_le_centSub_imgTil hV hBs hBN
  have hAq' : ∀ a ∈ Bb, ∀ y ∈ U, a y * y⁻¹ ∈ imgTil V₁ V hV N :=
    s15_LP_mul_inv_mem_of_mQuot_le_one hsq hNsU hUst (hcent.trans (centSub_le_stabSub _)) hq'
  have hle := s15_LP_rk_autSub_le_rk_of_trivial hsq hNsU hUst hcent hAq' hq'
  by_cases hNU : imgTil V₁ V hV N = U
  · have h0 : rk ↥(autSub Bb U) = 0 := by
      rw [s15_LP_rk_autSub_eq_mQuot hUst, inf_eq_left.2 (hNU ▸ hcent)]
      simp [E3.mQuot]
    omega
  · have hlt' : rk ↥(imgTil V₁ V hV N) < rk ↥U := by
      by_contra hge
      exact hNU (eq_of_le_of_rk_le hsq hNsU (not_lt.1 hge))
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
