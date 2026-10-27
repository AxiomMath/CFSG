module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAAA1AAAAA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3MixedSL4AAAAB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3FixLift

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
variable {G : Type} [Group G] [Finite G]

private theorem s16h_priv_isElemAbelian_top {A : Type} [Group A] {p : ℕ}
    (hcomm : ∀ a b : A, a * b = b * a) (hpow : ∀ a : A, a ^ p = 1) :
    CFSG.Open.IsElemAbelian p (⊤ : Subgroup A) :=
  ⟨IsMulCommutative.of_comm fun a b => Subtype.ext (hcomm a.1 b.1), fun a _ => hpow a⟩

theorem s16h_sl4_kernel_three_dvd_of_bad
    (D : Data G) (S : s16h_Std D) (hσ : D.sig = D.sig1)
    (hJP : K_JonesParshallH1) {V L : Subgroup G} (h : Setting16 D ⊥ V L)
    (hs2 : s15 D.M ⊥ V h.hyp151.isElemAbelian L = 2)
    {t : MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)} (ht : t ∈ Mbar D.M ⊥ V h.hyp151.isElemAbelian)
    (ht2 : t ^ 2 = 1) (ht1 : t ≠ 1) (htr : rk ↥(commSub ⊤ (zpowers t)) ≤ 3)
    (hW : Conc4_136W (Mbar D.M ⊥ V h.hyp151.isElemAbelian) t (lBar ⊥ V h.hyp151.isElemAbelian L))
    (hcomp : IsComponentOf (lBar ⊥ V h.hyp151.isElemAbelian L)
      (Mbar D.M ⊥ V h.hyp151.isElemAbelian))
    (hthin : ∀ q : ℕ, q.Prime → q ≠ 2 →
      CFSG.Open.pRank q (lBar ⊥ V h.hyp151.isElemAbelian L) ≤ 1)
    (hZ : commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L) ≠ ⊥)
    (hbad : ∀ q ∈ D.sig, ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian q E →
      Nat.card ↥(E ⊓ preBarSub D.M ⊥ V h.hyp151.isElemAbelian
        (centSub (wTil ⊥ V h.hyp151.isElemAbelian L))) < q ^ 2)
    (hrow : s16h_H5RowSL2 (lBar ⊥ V h.hyp151.isElemAbelian L)
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L))
      (commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
        fixV (lBar ⊥ V h.hyp151.isElemAbelian L)) 2)
    (hZ4 : 2 < Nat.card ↥(commSub ⊤ (lBar ⊥ V h.hyp151.isElemAbelian L) ⊓
      fixV (lBar ⊥ V h.hyp151.isElemAbelian L)))
    {x : G} (hxM : x ∈ D.M) (hxn : x ∉ nBar D.M ⊥ V h.hyp151.isElemAbelian L) :
    3 ∣ Nat.card ↥(Mbar D.M ⊥ V h.hyp151.isElemAbelian ⊓
      Subgroup.centralizer (lBar ⊥ V h.hyp151.isElemAbelian L :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian))) ⊓
      Subgroup.centralizer (lBar ⊥ V h.hyp151.isElemAbelian (conjSubgroup L x) :
        Set (MulAut (Vtil ⊥ V h.hyp151.isElemAbelian)))) := by
  have hV := h.hyp151.isElemAbelian
  have hMs : D.M ≤ stabTil ⊥ V :=
    le_stabTil h.hyp151.hyp125.pairFacts.le_normalizer
      h.hyp151.hyp125.pairFacts.le_normalizer₀
  haveI : Finite (MulAut (Vtil ⊥ V hV)) := MulEquiv.finite_left
  have hsig : D.sig = {3} :=
    s16h_sl4_bad_three_mem D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad hrow
      hZ4 hxM hxn
  have h3sig : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have h3rankM : 3 ≤ CFSG.Open.pRank 3 D.M := S.hx.three_le 3 h3sig
  have h3C : ¬ 3 ∣ Nat.card ↥(F11.CTilde D.M ⊥ V) :=
    s16h_sl4_three_not_dvd_kernel D S hσ hJP h hs2 ht ht2 ht1 htr hW hcomp hthin hZ hbad
      hrow hZ4 hxM hxn
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨E, hEM, hEab, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) D.M
  have h27pow : 27 ≤ 3 ^ CFSG.Open.pRank 3 D.M := by
    calc 27 = 3 ^ 3 := by norm_num
      _ ≤ 3 ^ CFSG.Open.pRank 3 D.M := Nat.pow_le_pow_right (by norm_num) h3rankM
  have hE27 : 27 ≤ Nat.card ↥E := by rw [hEcard]; exact h27pow
  obtain ⟨Eb, hEbMbar, hEbab, hEbcard⟩ :=
    s16h_e3_bar_rank_ge D h.hyp151.hyp125 h3C ⟨E, hEM, hEab, hEcard⟩
  have hEb27 : 27 ≤ Nat.card ↥Eb := by rw [hEbcard]; exact h27pow
  have hcardLb : Set.ncard {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV,
        X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} ≤ 2 := by
    have h2 := hs2
    unfold s15 at h2
    simp only [lBar] at h2 ⊢
    omega
  have hψmem : (actTil ⊥ V hV ⟨x, hMs hxM⟩) ∈ Mbar D.M ⊥ V hV :=
    actTil_mem_barSub ⊥ V hV hxM (hMs hxM)
  have hLbx_eq : lBar ⊥ V hV (conjSubgroup L x) =
      (lBar ⊥ V hV L).map
        (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).toMonoidHom :=
    s15_Infra_barSub_conjSubgroup ⊥ V hV (hMs hxM) L
  have hcardLbx : Set.ncard {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
      ∃ φ ∈ Mbar D.M ⊥ V hV,
        X = (lBar ⊥ V hV (conjSubgroup L x)).map (MulAut.conj φ).toMonoidHom} ≤ 2 := by
    have hset : {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
        ∃ φ ∈ Mbar D.M ⊥ V hV,
          X = (lBar ⊥ V hV (conjSubgroup L x)).map (MulAut.conj φ).toMonoidHom} =
        {X : Subgroup (MulAut (Vtil ⊥ V hV)) |
          ∃ φ ∈ Mbar D.M ⊥ V hV,
            X = (lBar ⊥ V hV L).map (MulAut.conj φ).toMonoidHom} := by
      ext X; constructor
      · rintro ⟨φ, hφ, rfl⟩
        refine ⟨φ * (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹,
          (Mbar D.M ⊥ V hV).mul_mem hφ ((Mbar D.M ⊥ V hV).inv_mem hψmem), ?_⟩
        rw [hLbx_eq, ← s15GapFour_map_conj_mul]
      · rintro ⟨χ, hχ, rfl⟩
        refine ⟨χ * actTil ⊥ V hV ⟨x, hMs hxM⟩,
          (Mbar D.M ⊥ V hV).mul_mem hχ hψmem, ?_⟩
        rw [hLbx_eq, ← s15GapFour_map_conj_mul]
        rw [show (χ * actTil ⊥ V hV ⟨x, hMs hxM⟩) *
            (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹ = χ from by group]
    rw [hset]
    exact hcardLb
  have hEbN : Eb ≤ Subgroup.normalizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
    intro y hy
    exact s15GapFour_mem_normalizer_of_odd (Mbar D.M ⊥ V hV) (lBar ⊥ V hV L) hcardLb
      (hEbMbar hy) (by decide : Odd 3) (hEbab.2 y hy)
  have hEbNx : Eb ≤ Subgroup.normalizer
      (lBar ⊥ V hV (conjSubgroup L x) : Set (MulAut (Vtil ⊥ V hV))) := by
    intro y hy
    exact s15GapFour_mem_normalizer_of_odd (Mbar D.M ⊥ V hV)
      (lBar ⊥ V hV (conjSubgroup L x)) hcardLbx (hEbMbar hy) (by decide : Odd 3)
      (hEbab.2 y hy)
  have hAutL : CFSG.Open.pRank 3 (⊤ : Subgroup (MulAut ↥(lBar ⊥ V hV L))) ≤ 1 :=
    s16h_sl4_aut_three_rank_le_one hrow
  have hLbxIso : ↥(lBar ⊥ V hV (conjSubgroup L x)) ≃* ↥(lBar ⊥ V hV L) :=
    (MulEquiv.subgroupCongr hLbx_eq).trans
      (Subgroup.equivMapOfInjective (lBar ⊥ V hV L)
        (MulAut.conj (actTil ⊥ V hV ⟨x, hMs hxM⟩)⁻¹).toMonoidHom
        (MulAut.conj _).injective).symm
  have hAutLx : CFSG.Open.pRank 3
      (⊤ : Subgroup (MulAut ↥(lBar ⊥ V hV (conjSubgroup L x)))) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) (MulAut.congr hLbxIso)]
    exact hAutL
  let φ : ↥Eb →* MulAut ↥(lBar ⊥ V hV L) :=
    (Subgroup.normalizerMonoidHom (H := lBar ⊥ V hV L)).comp (Subgroup.inclusion hEbN)
  have hEbtop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup ↥Eb) :=
    s16h_priv_isElemAbelian_top (fun a b => hEbab.1.is_comm.comm a b)
      (fun a => Subtype.ext (hEbab.2 a.1 a.2))
  have hφrange_ab : CFSG.Open.IsElemAbelian 3 φ.range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.SectionRank.isElemAbelian_map hEbtop φ
  have hφrange_rank : CFSG.Open.pRank 3 φ.range ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top).trans hAutL
  have hφrange_card : Nat.card ↥φ.range ≤ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hφrange_ab)
    have hk1 : k ≤ 1 :=
      (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_rfl hφrange_ab hk).trans hφrange_rank
    calc Nat.card ↥φ.range = 3 ^ k := hk
      _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  have hker1 : 9 ≤ Nat.card ↥φ.ker := by
    have hcard := Subgroup.card_ker_mul_card_range φ
    have hpos : 0 < Nat.card ↥φ.range := Nat.card_pos
    nlinarith [hcard, hφrange_card, hEb27, hpos]
  let E1 : Subgroup (MulAut (Vtil ⊥ V hV)) := φ.ker.map Eb.subtype
  have hE1card : 9 ≤ Nat.card ↥E1 := by
    rw [Subgroup.card_map_of_injective (K := φ.ker) (f := Eb.subtype) Eb.subtype_injective]
    exact hker1
  have hE1_le_Eb : E1 ≤ Eb := Subgroup.map_subtype_le _
  have hE1Nx : E1 ≤ Subgroup.normalizer
      (lBar ⊥ V hV (conjSubgroup L x) : Set (MulAut (Vtil ⊥ V hV))) :=
    hE1_le_Eb.trans hEbNx
  have hE1_cent : E1 ≤ Subgroup.centralizer
      (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    have hu1 : φ u = 1 := MonoidHom.mem_ker.1 hu
    have hval := Subgroup.normalizerMonoidHom_apply_apply_coe (lBar ⊥ V hV L)
      (Subgroup.inclusion hEbN u) ⟨a, ha⟩
    have hval' : ((φ u ⟨a, ha⟩ : ↥(lBar ⊥ V hV L)) : MulAut (Vtil ⊥ V hV)) =
        (u : MulAut (Vtil ⊥ V hV)) * a * (u : MulAut (Vtil ⊥ V hV))⁻¹ := by
      simpa only [φ, MonoidHom.comp_apply, Subgroup.coe_inclusion] using hval
    rw [hu1, MulAut.one_apply] at hval'
    have hval'' : a = (u : MulAut (Vtil ⊥ V hV)) * a * (u : MulAut (Vtil ⊥ V hV))⁻¹ :=
      hval'
    have hu2 : (u : MulAut (Vtil ⊥ V hV)) * a = a * (u : MulAut (Vtil ⊥ V hV)) := by
      have h3 : a * (u : MulAut (Vtil ⊥ V hV)) = (u : MulAut (Vtil ⊥ V hV)) * a := by
        nth_rewrite 1 [hval'']; group
      exact h3.symm
    exact hu2.symm
  let ψ : ↥E1 →* MulAut ↥(lBar ⊥ V hV (conjSubgroup L x)) :=
    (Subgroup.normalizerMonoidHom (H := lBar ⊥ V hV (conjSubgroup L x))).comp
      (Subgroup.inclusion hE1Nx)
  have hE1top : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup ↥E1) :=
    s16h_priv_isElemAbelian_top
      (fun a b => Subtype.ext (congrArg (Subtype.val : ↥Eb → MulAut (Vtil ⊥ V hV))
        (hEbab.1.is_comm.comm ⟨a.1, hE1_le_Eb a.2⟩ ⟨b.1, hE1_le_Eb b.2⟩)))
      (fun a => Subtype.ext (hEbab.2 a.1 (hE1_le_Eb a.2)))
  have hψrange_ab : CFSG.Open.IsElemAbelian 3 ψ.range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.SectionRank.isElemAbelian_map hE1top ψ
  have hψrange_rank : CFSG.Open.pRank 3 ψ.range ≤ 1 :=
    (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) le_top).trans hAutLx
  have hψrange_card : Nat.card ↥ψ.range ≤ 3 := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.Open.IsElemAbelian.isPGroup hψrange_ab)
    have hk1 : k ≤ 1 :=
      (CFSG.SectionRank.le_pRank (by norm_num : 1 < 3) le_rfl hψrange_ab hk).trans hψrange_rank
    calc Nat.card ↥ψ.range = 3 ^ k := hk
      _ ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hk1
      _ = 3 := by norm_num
  have hker2 : 3 ≤ Nat.card ↥ψ.ker := by
    have hcard := Subgroup.card_ker_mul_card_range ψ
    have hpos : 0 < Nat.card ↥ψ.range := Nat.card_pos
    nlinarith [hcard, hψrange_card, hE1card, hpos]
  let P : Subgroup (MulAut (Vtil ⊥ V hV)) := ψ.ker.map E1.subtype
  have hPcard : Nat.card ↥P = Nat.card ↥ψ.ker :=
    Subgroup.card_map_of_injective (K := ψ.ker) (f := E1.subtype) E1.subtype_injective
  have hP_le_Eb : P ≤ Eb := (Subgroup.map_subtype_le ψ.ker).trans hE1_le_Eb
  have hP_centx : P ≤ Subgroup.centralizer
      (lBar ⊥ V hV (conjSubgroup L x) : Set (MulAut (Vtil ⊥ V hV))) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hy
    have hu1 : ψ u = 1 := MonoidHom.mem_ker.1 hu
    have hval := Subgroup.normalizerMonoidHom_apply_apply_coe
      (lBar ⊥ V hV (conjSubgroup L x)) (Subgroup.inclusion hE1Nx u) ⟨a, ha⟩
    have hval' : ((ψ u ⟨a, ha⟩ : ↥(lBar ⊥ V hV (conjSubgroup L x))) :
        MulAut (Vtil ⊥ V hV)) =
        (u : MulAut (Vtil ⊥ V hV)) * a * (u : MulAut (Vtil ⊥ V hV))⁻¹ := by
      simpa only [ψ, MonoidHom.comp_apply, Subgroup.coe_inclusion] using hval
    rw [hu1, MulAut.one_apply] at hval'
    have hval'' : a = (u : MulAut (Vtil ⊥ V hV)) * a * (u : MulAut (Vtil ⊥ V hV))⁻¹ :=
      hval'
    have hu2 : (u : MulAut (Vtil ⊥ V hV)) * a = a * (u : MulAut (Vtil ⊥ V hV)) := by
      have h3 : a * (u : MulAut (Vtil ⊥ V hV)) = (u : MulAut (Vtil ⊥ V hV)) * a := by
        nth_rewrite 1 [hval'']; group
      exact h3.symm
    exact hu2.symm
  have hPleK : P ≤ Mbar D.M ⊥ V hV ⊓
      Subgroup.centralizer (lBar ⊥ V hV L : Set (MulAut (Vtil ⊥ V hV))) ⊓
      Subgroup.centralizer (lBar ⊥ V hV (conjSubgroup L x) : Set (MulAut (Vtil ⊥ V hV))) :=
    le_inf (le_inf (hP_le_Eb.trans hEbMbar)
      ((Subgroup.map_subtype_le ψ.ker).trans hE1_cent)) hP_centx
  have hP3 : 3 ∣ Nat.card ↥P := by
    have hPp : IsPGroup 3 ↥P :=
      (CFSG.Open.IsElemAbelian.isPGroup hEbab).to_le hP_le_Eb
    obtain ⟨j, hj⟩ := IsPGroup.iff_card.1 hPp
    have hj1 : j ≠ 0 := by
      intro h0
      rw [h0, pow_zero] at hj
      have : 3 ≤ Nat.card ↥P := by rw [hPcard]; exact hker2
      omega
    rw [hj]
    exact dvd_pow_self 3 hj1
  exact hP3.trans (Subgroup.card_dvd_of_le hPleK)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
