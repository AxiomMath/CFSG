module

public import CFSG.Quasithin.Background.E6EighteenHeAut
public import CFSG.Quasithin.Background.E6EighteenHeCtx
public import CFSG.Quasithin.Background.E6EighteenHeRes

public section

namespace CFSG.Quasithin

namespace E6

open CFSG.Open CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)

section Counting

variable {S : Type} [Group S] [Finite S]

theorem finite_mulAut_e618 : Finite (MulAut S) :=
  Finite.of_injective (fun f : MulAut S => (f : S → S)) DFunLike.coe_injective

theorem exists_inner_involution_of_card_eight {V : Type} [Group V] (hV2 : ∀ v : V, v * v = 1)
    (ρ : V →* MulAut S) (hZ : Subgroup.center S = ⊥) (hOut : Nat.card (Outer S) = 2)
    (h8 : Nat.card ρ.range = 8) : ∃ v : V, ∃ x : S, orderOf x = 2 ∧ ρ v = MulAut.conj x := by
  have := finite_mulAut_e618 (S := S)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hidx : (ρ.range ⊓ inner S).relIndex ρ.range ≤ 2 :=
    relIndex_inf_inner_le_two_of_card_outer hOut ρ.range
  have hmul := Subgroup.relIndex_mul_card (ρ.range ⊓ inner S) ρ.range
  rw [inf_eq_left.2 (inf_le_left : ρ.range ⊓ inner S ≤ ρ.range), h8] at hmul
  rcases Subgroup.bot_or_exists_ne_one (ρ.range ⊓ inner S) with hbot | ⟨φ, hφI, hφ1⟩
  · have h1 : Nat.card ↥(ρ.range ⊓ inner S) = 1 := by
      rw [hbot]
      exact Subgroup.card_bot
    rw [h1] at hmul
    omega
  obtain ⟨hφR, hφi⟩ := Subgroup.mem_inf.1 hφI
  obtain ⟨v, hv⟩ := MonoidHom.mem_range.1 hφR
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.1 hφi
  have hx1 : x ≠ 1 := by
    rintro rfl
    rw [map_one] at hx
    exact hφ1 hx.symm
  have hxx : x * x = 1 := by
    apply Id2519.conj_injective_of_center_bot hZ
    rw [map_mul, hx, ← hv, ← map_mul, hV2, map_one, map_one]
  exact ⟨v, x, orderOf_eq_prime (by rw [pow_two, hxx]) hx1, hv.trans hx.symm⟩

theorem card_le_of_isPGroup_comm (hZ : Subgroup.center S = ⊥) (hOut : Nat.card (Outer S) = 2)
    {σ : MulAut S} (hfix : Nat.card (fixedSubgroup σ) = 15120) {P : Subgroup (MulAut S)}
    (hP : IsPGroup 2 P) (hPσ : ∀ τ ∈ P, τ * σ = σ * τ) : Nat.card P ≤ 32 := by
  have := finite_mulAut_e618 (S := S)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFσ : (P ⊓ inner S).comap (MulAut.conj : S →* MulAut S) ≤ fixedSubgroup σ := by
    intro y hy
    have hyP : MulAut.conj y ∈ P := (Subgroup.mem_inf.1 (Subgroup.mem_comap.1 hy)).1
    exact apply_eq_of_conj_comm hZ (hPσ _ hyP)
  have hIF : ((P ⊓ inner S).comap (MulAut.conj : S →* MulAut S)).map
      (MulAut.conj : S →* MulAut S) = P ⊓ inner S := by
    rw [Subgroup.map_comap_eq]
    exact inf_eq_right.2 inf_le_right
  have hcardI : Nat.card ↥(P ⊓ inner S) =
      Nat.card ↥((P ⊓ inner S).comap (MulAut.conj : S →* MulAut S)) := by
    have h : Nat.card ↥(((P ⊓ inner S).comap (MulAut.conj : S →* MulAut S)).map
        (MulAut.conj : S →* MulAut S)) =
        Nat.card ↥((P ⊓ inner S).comap (MulAut.conj : S →* MulAut S)) :=
      Subgroup.card_map_of_injective (Id2519.conj_injective_of_center_bot hZ)
    rwa [hIF] at h
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).1 (hP.to_le (inf_le_left : P ⊓ inner S ≤ P))
  have hdvd : 2 ^ k ∣ 16 * 945 := by
    rw [← hk, hcardI, show (16 * 945 : ℕ) = 15120 by norm_num, ← hfix]
    exact Subgroup.card_dvd_of_le hFσ
  have h16 : 2 ^ k ∣ 16 :=
    (Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 945)).dvd_of_dvd_mul_right hdvd
  have hI16 : Nat.card ↥(P ⊓ inner S) ≤ 16 := by
    rw [hk]
    exact Nat.le_of_dvd (by norm_num) h16
  have hidx : (P ⊓ inner S).relIndex P ≤ 2 := relIndex_inf_inner_le_two_of_card_outer hOut P
  have hmul := Subgroup.relIndex_mul_card (P ⊓ inner S) P
  rw [inf_eq_left.2 (inf_le_left : P ⊓ inner S ≤ P)] at hmul
  rw [← hmul]
  calc (P ⊓ inner S).relIndex P * Nat.card ↥(P ⊓ inner S) ≤ 2 * 16 := Nat.mul_le_mul hidx hI16
    _ = 32 := by norm_num

theorem false_of_perfect_normalizing (hZ : Subgroup.center S = ⊥)
    (hOut : Nat.card (Outer S) = 2) {R : Subgroup (MulAut S)}
    (hRab : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hR8 : Nat.card R = 8) {σ : MulAut S}
    (hσR : σ ∈ R) (hσout : σ ∉ inner S) (hfix : Nat.card (fixedSubgroup σ) = 15120)
    {D : Subgroup S} (hDp : ⁅D, D⁆ = D) (hD64 : 64 ∣ Nat.card D)
    (hDR : ∀ d ∈ D, ∀ τ ∈ R, MulAut.conj d * τ * (MulAut.conj d)⁻¹ ∈ R) : False := by
  have := finite_mulAut_e618 (S := S)
  have hidx : (R ⊓ inner S).relIndex R ≤ 2 := relIndex_inf_inner_le_two_of_card_outer hOut R
  have hidx1 : (R ⊓ inner S).relIndex R ≠ 1 := fun h1 =>
    hσout ((inf_le_right : R ⊓ inner S ≤ inner S) (Subgroup.relIndex_eq_one.1 h1 hσR))
  have hmul := Subgroup.relIndex_mul_card (R ⊓ inner S) R
  rw [inf_eq_left.2 (inf_le_left : R ⊓ inner S ≤ R), hR8] at hmul
  have hI4 : Nat.card ↥(R ⊓ inner S) ≤ 4 := by
    have h0 : (R ⊓ inner S).relIndex R ≠ 0 := fun h0 => by
      rw [h0, zero_mul] at hmul
      omega
    have h2 : (R ⊓ inner S).relIndex R = 2 := by omega
    rw [h2] at hmul
    omega
  have hXp : ⁅D.map (MulAut.conj : S →* MulAut S), D.map (MulAut.conj : S →* MulAut S)⁆ =
      D.map (MulAut.conj : S →* MulAut S) := by
    rw [← Subgroup.map_commutator, hDp]
  have hXR : D.map (MulAut.conj : S →* MulAut S) ≤
      Subgroup.normalizer (R : Set (MulAut S)) := by
    rintro _ ⟨d, hd, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro τ
    refine ⟨fun hτ => hDR d hd τ hτ, fun hτ => ?_⟩
    have h1 := hDR d⁻¹ (D.inv_mem hd) _ hτ
    have e : MulAut.conj d⁻¹ * (MulAut.conj d * τ * (MulAut.conj d)⁻¹) *
        (MulAut.conj d⁻¹)⁻¹ = τ := by
      rw [map_inv]
      group
    rwa [e] at h1
  have hXI : D.map (MulAut.conj : S →* MulAut S) ≤
      Subgroup.normalizer ((R ⊓ inner S : Subgroup (MulAut S)) : Set (MulAut S)) := by
    refine B2F.le_normalizer_inf hXR fun g _ => ?_
    rw [Subgroup.normalizer_eq_top]
    exact Subgroup.mem_top g
  have hXC := le_centralizer_of_perfect_of_index_le_two hRab
    (inf_le_left : R ⊓ inner S ≤ R) hI4 hidx hXp hXR hXI
  have hDσ : D ≤ fixedSubgroup σ := by
    intro d hd
    have hc := Subgroup.mem_centralizer_iff.1 (hXC ⟨d, hd, rfl⟩) σ hσR
    exact apply_eq_of_conj_comm hZ hc.symm
  have h1 := Subgroup.card_dvd_of_le hDσ
  rw [hfix] at h1
  have h2 := hD64.trans h1
  norm_num at h2

end Counting

theorem two_pow_dvd_card_map_of_isSylowIn {G : Type} [Group G] [Finite G] {K Y Q : Subgroup G}
    (hYN : Y ≤ Subgroup.normalizer (K : Set G)) (hQ : IsSylowIn 2 Q Y) {n : ℕ}
    (hn : 2 ^ n ∣ Nat.card (barHomOn hYN).range) :
    2 ^ n ∣ Nat.card ((Q.subgroupOf Y).map (barHomOn hYN)) := by
  set ρ := barHomOn hYN with hρ
  have hsurj : Function.Surjective ρ.rangeRestrict := ρ.rangeRestrict_surjective
  have hidx := Subgroup.index_map_dvd (Q.subgroupOf Y) hsurj
  have hodd : ¬ 2 ∣ (Q.subgroupOf Y).index := hQ.not_dvd_relIndex
  have hodd' : Odd ((Q.subgroupOf Y).map ρ.rangeRestrict).index :=
    Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 fun h2 => hodd (h2.trans hidx))
  have hcard := Subgroup.card_mul_index ((Q.subgroupOf Y).map ρ.rangeRestrict)
  have hmap : (Q.subgroupOf Y).map ρ =
      ((Q.subgroupOf Y).map ρ.rangeRestrict).map ρ.range.subtype := by
    rw [Subgroup.map_map, MonoidHom.subtype_comp_rangeRestrict]
  rw [hmap, Subgroup.card_map_of_injective ρ.range.subtype_injective]
  have hcop : Nat.Coprime (2 ^ n) ((Q.subgroupOf Y).map ρ.rangeRestrict).index :=
    Nat.Coprime.pow_left n (Nat.coprime_two_left.2 hodd')
  rw [← hcard] at hn
  exact hcop.dvd_of_dvd_mul_right hn

theorem conj_mk_mul_barHomOn_mul_inv {G : Type} [Group G] {K V : Subgroup G}
    (hVN : V ≤ Subgroup.normalizer (K : Set G)) (e : ↥K)
    (he : (e : G) ∈ Subgroup.normalizer (V : Set G)) (w : ↥V) :
    MulAut.conj (QuotientGroup.mk e : Bar.Qbar K) * barHomOn hVN w *
        (MulAut.conj (QuotientGroup.mk e : Bar.Qbar K))⁻¹ =
      barHomOn hVN ⟨(e : G) * w * (e : G)⁻¹, (Subgroup.mem_normalizer_iff.1 he w).1 w.2⟩ := by
  rw [← Bar.barHom_of_mem e, barHomOn_apply, barHomOn_apply, ← map_inv, ← map_mul,
    ← map_mul]
  rfl

theorem e618HeResidual_of_invPerfect
    (hP : FactHeInvPerfect) : E618HeResidual := by
  intro G _ _ T M V U L hV h _ _ _ _ hLA7 U' hU' hq hm A K hAU' hA1 hK hU'N hLK hHeK
  classical
  by_contra hU'K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU'V : U' ≤ V := by rw [hU']; exact inf_le_left
  have hV2 : IsPGroup 2 V := h.isPGroup_V
  have hVc : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
    B2F.isElemAbelian_comm h.isElemAbelian ha hb
  have hVsq : ∀ v ∈ V, v * v = 1 := fun v hv => by rw [← pow_two]; exact hV.2 v hv
  have hAV : A ≤ V := hAU'.trans hU'V
  have hA2 : IsPGroup 2 A := hV2.to_le hAV
  have hKq := BenderBranch.isQuasisimple_of_isComponentIn hK
  have hLKle : L ≤ K := hLK.1.trans inf_le_left
  have hLU' : L ≤ Subgroup.centralizer (U' : Set G) := hLK.1.trans inf_le_right
  have hLq := BenderBranch.isQuasisimple_of_isComponentIn hLK
  have hAK : A ≤ Subgroup.centralizer (K : Set G) := Subgroup.le_centralizer_iff.1 hK.1
  obtain ⟨⟨φ7⟩, hZ7⟩ := id hLA7
  obtain ⟨E9, hE9L, hE93, hE9c⟩ := exists_elemAbelian_nine_of_alt7 φ7 hZ7
  have hrank : CFSG.Open.pRank 3 (Subgroup.centralizer (A : Set G)) ≤ 2 :=
    (CFSG.SectionRank.pRank_mono (by norm_num) (Subgroup.centralizer_le_normalizer _)).trans
      ((A1b.pRank_le_evenRank Nat.prime_three (by norm_num) ⟨A, hA1, hA2, rfl⟩).trans
        h.qtke.2.2)
  have hCAN := centralizer_le_normalizer_of_isHeQuot hK hHeK (hE9L.trans hLKle) hE93 hE9c hrank
  have hVCA : V ≤ Subgroup.centralizer (A : Set G) := fun v hv =>
    Subgroup.mem_centralizer_iff.2 fun a ha => hVc a (hAV ha) v hv
  have hVN : V ≤ Subgroup.normalizer (K : Set G) := hVCA.trans hCAN
  obtain ⟨W, hWdef⟩ : ∃ W : Subgroup G, W = V ⊓ Subgroup.centralizer (K : Set G) := ⟨_, rfl⟩
  have hWV : W ≤ V := by rw [hWdef]; exact inf_le_left
  have hWK : W ≤ Subgroup.centralizer (K : Set G) := by rw [hWdef]; exact inf_le_right
  have hAW : A ≤ W := by rw [hWdef]; exact le_inf hAV hAK
  have hU'W : U' ⊓ Subgroup.centralizer (K : Set G) = W := by
    rw [hWdef]
    refine le_antisymm (inf_le_inf_right _ hU'V) (le_inf ?_ inf_le_right)
    rw [hU']
    exact le_inf inf_le_left (inf_le_right.trans (Subgroup.centralizer_le hLKle))
  have hWU' : W ≤ U' := by rw [← hU'W]; exact inf_le_left
  have hP2' : ∀ u ∈ U', u * u = 1 := fun u hu => hVsq u (hU'V hu)
  have hidx := relIndex_inf_centralizer_le_two_of_isHeQuot hKq hHeK hU'N hP2' hLKle hLU' hLq
    hLA7
  rw [hU'W] at hidx
  have hmW : E3.mQuot V W = 3 := by
    have hadd := E3.mQuot_add hWU' hU'V
    have h1 : E3.mQuot U' W ≤ 1 := by
      rw [E3.relIndex_eq_two_pow (hV2.to_le hU'V) W] at hidx
      by_contra hlt
      push Not at hlt
      have : 2 ^ 2 ≤ 2 ^ E3.mQuot U' W := Nat.pow_le_pow_right (by norm_num) hlt
      omega
    have h2 : E3.mQuot U' W ≠ 0 := fun h0 => hU'K (by
      rw [← (E3.mQuot_eq_zero_iff (hV2.to_le hU'V) hWU').1 h0]
      exact hWK)
    omega
  have h8 : Nat.card (barHomOn hVN).range = 8 := by
    rw [card_range_barHomOn hKq hVN, ← hWdef, E3.relIndex_eq_two_pow hV2, hmW]
    norm_num
  obtain ⟨u, huU', huK⟩ : ∃ u ∈ U', u ∉ Subgroup.centralizer (K : Set G) := by
    by_contra hall
    push Not at hall
    exact hU'K hall
  have huV : u ∈ V := hU'V huU'
  obtain ⟨σ, hσdef⟩ : ∃ σ, σ = barHomOn hVN ⟨u, huV⟩ := ⟨_, rfl⟩
  have hσ1 : σ ≠ 1 := fun h1 => huK ((barHomOn_eq_one_iff hKq hVN _).1 (by rw [← hσdef]; exact h1))
  have hσout : σ ∉ inner (Bar.Qbar K) := by
    intro hin
    apply hσ1
    rw [hσdef, barHomOn_apply] at hin ⊢
    exact barHom_eq_one_of_mem_inner hKq hHeK hLKle hLq hLA7 ⟨u, hVN huV⟩ (hVsq u huV)
      (fun l hl => Subgroup.mem_centralizer_iff.1 (hLU' hl) u huU') hin
  have hσ2 : orderOf σ = 2 := by
    refine orderOf_eq_prime ?_ hσ1
    rw [hσdef, pow_two, ← map_mul,
      show (⟨u, huV⟩ : ↥V) * ⟨u, huV⟩ = 1 from Subtype.ext (hVsq u huV), map_one]
  obtain ⟨φ⟩ := nonempty_qbar_mulEquiv_he hKq hHeK
  have hZ : Subgroup.center (Bar.Qbar K) = ⊥ :=
    CFSG.LieType.CurtisTits.center_quotient_center_eq_bot_of_isQuasisimple hKq
  have hOut := card_outer_qbar_of_isHeQuot hKq hHeK
  have hfix : Nat.card (fixedSubgroup σ) = 15120 :=
    CFSG.SeitzReduction.SporadicRefine.he_outer_card_fixedSubgroup φ hσ2 hσout
  have := finite_mulAut_e618 (S := Bar.Qbar K)
  obtain ⟨⟨v, hvV⟩, x, hx2, hvx⟩ := exists_inner_involution_of_card_eight (S := Bar.Qbar K)
    (fun w : ↥V => Subtype.ext (hVsq w w.2)) (barHomOn hVN) hZ hOut h8
  have hvK : v ∉ Subgroup.centralizer (K : Set G) := by
    intro hvC
    have h1 : barHomOn hVN ⟨v, hvV⟩ = 1 := (barHomOn_eq_one_iff hKq hVN _).2 hvC
    rw [hvx] at h1
    have hx1 : x = 1 := Id2519.conj_injective_of_center_bot hZ (h1.trans (map_one _).symm)
    rw [hx1, orderOf_one] at hx2
    omega
  obtain ⟨D, hDx, hDp, hD64⟩ := hP (Bar.Qbar K) ⟨φ⟩ x hx2
  have hv' : Bar.barHom K ⟨v, hVN hvV⟩ = MulAut.conj x := hvx
  have hDfix : ∀ d ∈ D, Bar.barHom K ⟨v, hVN hvV⟩ d = d := by
    intro d hd
    rw [hv', MulAut.conj_apply, ← Subgroup.mem_centralizer_singleton_iff.1 (hDx hd),
      mul_inv_cancel_right]
  obtain ⟨E, hEp, hEmap, hEv⟩ := Bar.exists_lift_comm_of_perfect ⟨v, hVN hvV⟩ hDp hDfix
  obtain ⟨E', hE'def⟩ : ∃ E' : Subgroup G, E' = E.map K.subtype := ⟨_, rfl⟩
  have hE'K : E' ≤ K := by rw [hE'def]; exact Subgroup.map_subtype_le E
  have hmemE' : ∀ e ∈ E, (e : G) ∈ E' := fun e he => by rw [hE'def]; exact ⟨e, he, rfl⟩
  obtain ⟨U2, hU2def⟩ : ∃ U2 : Subgroup G, U2 = W ⊔ Subgroup.zpowers v := ⟨_, rfl⟩
  have hU2V : U2 ≤ V := by rw [hU2def]; exact sup_le hWV (Subgroup.zpowers_le.2 hvV)
  have hWU2 : W ≤ U2 := by rw [hU2def]; exact le_sup_left
  have hvU2 : v ∈ U2 := by rw [hU2def]; exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)
  have hE'U2 : E' ≤ Subgroup.centralizer (U2 : Set G) := by
    rw [Subgroup.le_centralizer_iff, hU2def]
    refine sup_le (hWK.trans (Subgroup.centralizer_le hE'K)) ?_
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro g hg
    rw [hE'def] at hg
    obtain ⟨e, he, rfl⟩ := hg
    exact (hEv e he).symm
  have hU2M : ¬ Subgroup.centralizer (U2 : Set G) ≤ M := by
    intro hle
    have hENV : ∀ e ∈ E, (e : G) ∈ Subgroup.normalizer (V : Set G) := fun e he =>
      inf_centralizer_le_normalizer h hAV hA1
        ⟨hle (hE'U2 (hmemE' e he)), hK.1 (hE'K (hmemE' e he))⟩
    refine false_of_perfect_normalizing hZ hOut (R := (barHomOn hVN).range) ?_ h8
      ⟨⟨u, huV⟩, hσdef.symm⟩ hσout hfix hDp hD64 ?_
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hVc a a.2 b b.2)
    · intro d hd τ hτ
      obtain ⟨w, rfl⟩ := hτ
      have hd' : d ∈ E.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by rw [hEmap]; exact hd
      obtain ⟨e, he, rfl⟩ := hd'
      rw [QuotientGroup.mk'_apply, conj_mk_mul_barHomOn_mul_inv hVN e (hENV e he) w]
      exact ⟨_, rfl⟩
  have hmU2 : E3.mQuot V U2 < 3 := by
    have hadd := E3.mQuot_add hWU2 hU2V
    have hne : E3.mQuot U2 W ≠ 0 := fun h0 => hvK (by
      have hWeq := (E3.mQuot_eq_zero_iff (hV2.to_le hU2V) hWU2).1 h0
      rw [← hWeq] at hvU2
      exact hWK hvU2)
    omega
  have hU21 : U2 ≠ ⊥ := fun h0 => hA1 (le_bot_iff.1 (by rw [← h0]; exact hAW.trans hWU2))
  have hU2Γ := mem_gammaE64_of_mQuot_lt hV h hU2V hU21 hU2M (by rw [hm]; exact hmU2)
  have hQ := e6_5_one h hU2Γ
  obtain ⟨Y, hYdef⟩ : ∃ Y : Subgroup G,
      Y = Subgroup.centralizer (U2 : Set G) ⊓ Subgroup.normalizer (K : Set G) := ⟨_, rfl⟩
  have hYN : Y ≤ Subgroup.normalizer (K : Set G) := by rw [hYdef]; exact inf_le_right
  have hQY : T ⊓ Subgroup.centralizer (V : Set G) ≤ Y := by
    rw [hYdef]
    exact le_inf (inf_le_right.trans (Subgroup.centralizer_le hU2V))
      (inf_le_right.trans ((Subgroup.centralizer_le hAV).trans hCAN))
  have hQs : IsSylowIn 2 (T ⊓ Subgroup.centralizer (V : Set G)) Y :=
    isSylowIn_of_le hQ hQY (by rw [hYdef]; exact inf_le_left)
  have hY64 : 2 ^ 6 ∣ Nat.card (barHomOn hYN).range := by
    have hle : D.map (MulAut.conj : Bar.Qbar K →* MulAut (Bar.Qbar K)) ≤
        (barHomOn hYN).range := by
      rintro _ ⟨d, hd, rfl⟩
      have hd' : d ∈ E.map (QuotientGroup.mk' (Subgroup.center ↥K)) := by rw [hEmap]; exact hd
      obtain ⟨e, he, rfl⟩ := hd'
      have heY : (e : G) ∈ Y := by
        rw [hYdef]
        exact ⟨hE'U2 (hmemE' e he), Subgroup.le_normalizer e.2⟩
      refine ⟨⟨e, heY⟩, ?_⟩
      rw [barHomOn_apply, QuotientGroup.mk'_apply]
      exact Bar.barHom_of_mem e
    have h1 := Subgroup.card_dvd_of_le hle
    rw [Subgroup.card_map_of_injective (Id2519.conj_injective_of_center_bot hZ)] at h1
    have h64 : (2 : ℕ) ^ 6 = 64 := by norm_num
    rw [h64]
    exact hD64.trans h1
  have hQ64 := two_pow_dvd_card_map_of_isSylowIn hYN hQs hY64
  have hQ2 : IsPGroup 2 ↥((T ⊓ Subgroup.centralizer (V : Set G)).subgroupOf Y) :=
    h.isPGroup_Q.of_equiv (Subgroup.subgroupOfEquivOfLe hQY).symm
  have hle32 := card_le_of_isPGroup_comm hZ hOut hfix (hQ2.map (barHomOn hYN)) (by
    rintro _ ⟨q, hq, rfl⟩
    rw [hσdef, barHomOn_apply, barHomOn_apply, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    have hqC : ((q : ↥Y) : G) ∈ Subgroup.centralizer (V : Set G) :=
      (Subgroup.mem_subgroupOf.1 hq).2
    exact (Subgroup.mem_centralizer_iff.1 hqC u huV).symm)
  have hpos : 0 < Nat.card ↥(((T ⊓ Subgroup.centralizer (V : Set G)).subgroupOf Y).map
      (barHomOn hYN)) := Nat.card_pos
  have h3 := Nat.le_of_dvd hpos hQ64
  norm_num at h3
  omega

end E6

end CFSG.Quasithin
