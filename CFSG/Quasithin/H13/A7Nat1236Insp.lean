module

public import CFSG.Quasithin.H13.A7Nat1236InspCases
public import CFSG.Quasithin.H13.A7Nat1236InspAlt
public import CFSG.Quasithin.H13.A7Nat1236InspLie

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.A7

open Equiv Equiv.Perm Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
  CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G]

theorem not_dvd_card_of_quotient {K : Subgroup G} {m : ℕ}
    (hm : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = m) (h25 : ¬ 25 ∣ m) : ¬ 25 ∣ Nat.card K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.1 (CFSG.pCore_isPGroup (p := 2) (G := ↥K))
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K), hm, hk] at h
  have hc : Nat.Coprime 25 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  exact h25 (hc.dvd_of_dvd_mul_right h)

omit [Finite G] in
theorem card_quotient_of_isHatA6Block {K : Subgroup G} (hK : IsHatA6Block K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 1080 := by
  obtain ⟨-, ⟨-, h3, ⟨e⟩⟩, -⟩ := hK
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (center (↥K ⧸ CFSG.pCore 2 ↥K)),
    Nat.card_congr e.toEquiv, nat_card_alt_six, h3]

omit [Finite G] in
theorem card_quotient_of_alt_seven {K : Subgroup G} {α : ↥K →* alternatingGroup (Fin 7)}
    (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K) :
    Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 2520 := by
  rw [← Nat.card_congr (QuotientGroup.quotientMulEquivOfEq hker).toEquiv,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective α hα).toEquiv,
    nat_card_alternatingGroup, Nat.card_fin]
  decide

omit [Finite G] in
theorem card_autOn_dvd_of_hom {K V : Subgroup G} (hKV : K ≤ normalizer (V : Set G)) {Q : Type*}
    [Group Q] [Finite Q] (α : ↥K →* Q) (hα : Function.Surjective α)
    (hαV : ∀ k : ↥K, α k = 1 → (k : G) ∈ centralizer (V : Set G)) :
    Nat.card (autOn K V) ∣ Nat.card Q := by
  have hrange : (A4.actionOn V K hKV).range = autOn K V := by
    ext a
    rw [MonoidHom.mem_range, A4.mem_autOn_iff hKV]
  obtain ⟨f, hf⟩ := exists_surj_of_ker_le α (θ := (A4.actionOn V K hKV).rangeRestrict)
    (A4.actionOn V K hKV).rangeRestrict_surjective fun k hk =>
      Subtype.ext ((A4.actionOn_eq_one_iff hKV k).2 (hαV k hk))
  have h1 := Subgroup.card_dvd_of_surjective hf
  rw [MonoidHom.range_eq_top.2 hα, Subgroup.card_top] at h1
  rwa [← hrange]

omit [Finite G] in
theorem autOn_eq_of_map_eq_top {K M V : Subgroup G} (hKV : K ≤ normalizer (V : Set G))
    {S : Type*} [Group S] (κ : ↥K →* S)
    (hκV : ∀ k : ↥K, κ k = 1 → (k : G) ∈ centralizer (V : Set G))
    (h : ((M ⊓ K).subgroupOf K).map κ = ⊤) : autOn (M ⊓ K) V = autOn K V := by
  refine le_antisymm (A4.autOn_mono inf_le_right) ?_
  intro a ha
  obtain ⟨k, rfl⟩ := (A4.mem_autOn_iff hKV).1 ha
  have hk : κ k ∈ ((M ⊓ K).subgroupOf K).map κ := by
    rw [h]
    exact mem_top _
  obtain ⟨m, hm, hmk⟩ := hk
  have hMKV : M ⊓ K ≤ normalizer (V : Set G) := inf_le_right.trans hKV
  rw [A4.mem_autOn_iff hMKV]
  refine ⟨⟨(m : G), hm⟩, ?_⟩
  have h2 : A4.actionOn V K hKV (m⁻¹ * k) = 1 :=
    (A4.actionOn_eq_one_iff hKV _).2 (hκV _ (by rw [map_mul, map_inv, hmk, inv_mul_cancel]))
  rw [map_mul, map_inv, inv_mul_eq_one] at h2
  rw [← h2]
  rfl

omit [Finite G] in
theorem range_le_map_inf {K M X : Subgroup G} (hXK : X ≤ K) (hXMK : X ≤ M ⊓ K) {S : Type*}
    [Group S] (κ : ↥K →* S) :
    (κ.comp (Subgroup.inclusion hXK)).range ≤ ((M ⊓ K).subgroupOf K).map κ := by
  rintro _ ⟨x, rfl⟩
  exact ⟨Subgroup.inclusion hXK x, hXMK x.2, rfl⟩

theorem insp1236_proved : Insp1236 := by
  intro G _ _ H R M K V T X hyp hK hq hc hn hR hV hC hT hRT hTK hX hTX hXq ⟨e⟩
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨hC1a, hC1b, -⟩, -, hC3⟩ := hC
  have hKRV : K ⊔ R ≤ normalizer (V : Set G) := by
    rw [hV]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _).trans
      (A4.normalizer_le_normalizer_omegaOneCenterOf _)
  have hKV : K ≤ normalizer (V : Set G) := le_sup_left.trans hKRV
  have hXK : X ≤ K := hX.trans inf_le_left
  have hXMK : X ≤ M ⊓ K := le_inf (hX.trans inf_le_right) hXK
  have hXV : X ≤ normalizer (V : Set G) := hXK.trans hKV
  obtain ⟨θ, hθ, hθc⟩ := exists_theta X e
  obtain ⟨fY, hfY⟩ := exists_surj_autOn_alt_six hR hC1b hXK hXV e
  have hθV : ∀ x : ↥X, (x : G) ∈ centralizer (V : Set G) → θ x = 1 := fun x hx =>
    theta_eq_one_of_mem_centralizer hR hC1b hXK hθc hx
  have hTK0 : QuasithinUnique.IsSylowTwoOf (T ⊓ K) K :=
    A312.isSylowTwoOf_inf_of_subnormal hK.2.2.1 hT
  have hT0X : T ⊓ K ≤ normalizer (X : Set G) := inf_le_left.trans hTX
  have hOV : ∀ k : ↥K, k ∈ CFSG.pCore 2 ↥K → (k : G) ∈ centralizer (V : Set G) := fun k hk =>
    (hC1a (pCoreOf_le_pCoreOf_sup hR (coe_mem_pCoreOf hk))).2
  let actK : ↥K →* ↥(autOn K V) := (A4.actionOn V K hKV).codRestrict (autOn K V) fun k =>
    (A4.mem_autOn_iff hKV).2 ⟨k, rfl⟩
  have hactK : Function.Surjective actK := by
    rintro ⟨a, ha⟩
    obtain ⟨k, rfl⟩ := (A4.mem_autOn_iff hKV).1 ha
    exact ⟨k, rfl⟩
  have hactV : ∀ k : ↥K, actK k = 1 → (k : G) ∈ centralizer (V : Set G) := fun k hk =>
    (A4.actionOn_eq_one_iff hKV k).1 (congrArg Subtype.val hk)
  rcases hC3 with hA | hB | hCc | hD | hE | hF | hGg | hH
  ·
    obtain ⟨-, hA⟩ := hA
    rcases hA with ⟨-, -, S, hS, hSeq⟩ | ⟨-, -, -, S, hS, hSeq⟩ | ⟨-, -, e7, P, hP, hPeq⟩ |
        ⟨-, -, e7, P, hP, hPeq⟩
    · refine false_of_surj_alt_six_of_le_normalizer hS (A4.autOn_mono hXK) ?_ hfY
      exact (A4.autOn_mono hXMK).trans (hSeq.le.trans inf_le_right)
    · refine false_of_surj_alt_six_of_le_normalizer hS (A4.autOn_mono hXK) ?_ hfY
      exact (A4.autOn_mono hXMK).trans (hSeq.le.trans inf_le_right)
    · obtain ⟨hPc, hPB⟩ := card_lt_five_of_isPartitionOfType hP (Or.inl rfl)
      exact false_of_partition (A4.autOn_mono hXMK) (A4.autOn_mono (inf_le_right.trans le_sup_left))
        e7 (by rw [hPeq]; exact inf_le_left) hP.2.2.1 hPc hPB hfY
    · obtain ⟨hPc, hPB⟩ := card_lt_five_of_isPartitionOfType hP (Or.inr rfl)
      exact false_of_partition (A4.autOn_mono hXMK) (A4.autOn_mono (inf_le_right.trans le_sup_left))
        e7 (by rw [hPeq]; exact inf_le_left) hP.2.2.1 hPc hPB hfY
  ·
    obtain ⟨⟨n, α, hn5, hn8, -, hα, t, htR, htV, -, -, σ, hσ, hσα⟩, hMK⟩ := hB
    exact false_of_case_b hR hC1b hKRV hX hTX hTK0 hθ
      (fun x hx => hθc x (commutator_mem_pCore_of_mem hx)) hn5 hn8 hα htR htV hσ hσα hMK
  ·
    obtain ⟨hHat, h15, -⟩ := hCc
    exact false_of_five_sq (not_dvd_card_of_quotient (card_quotient_of_isHatA6Block hHat)
      (by norm_num)) (by rw [h15]; norm_num) hX (dvd_trans (by norm_num) (card_alt_six_dvd hθ))
  ·
    obtain ⟨⟨-, ⟨α, hαs, hαk⟩, -⟩, h35⟩ := hD
    exact false_of_five_sq (not_dvd_card_of_quotient (card_quotient_of_alt_seven hαs hαk)
      (by norm_num)) (by rw [h35]; norm_num) hX (dvd_trans (by norm_num) (card_alt_six_dvd hθ))
  ·
    obtain ⟨hAS, hmax⟩ := hE
    rcases hAS with ⟨-, α, hαs, hαk, -⟩ | ⟨-, F, _, _, hF4, α, hαs, hαk, -⟩
    · have hcard : Nat.card (autOn K V) ∣ 360 := by
        rw [← nat_card_alt_six]
        exact card_autOn_dvd_of_hom hKV α hαs fun k hk => hOV k (hαk ▸ MonoidHom.mem_ker.2 hk)
      exact false_of_card_dvd_of_ne (A4.autOn_mono hXMK) (A4.autOn_mono inf_le_right) hmax.2.1
        hcard hfY
    · have hF' : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF4]; norm_num
      have : CharP F 2 := charP_two_of_card (by norm_num) hF'
      let κ := (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F).comp α
      have hκ : Function.Surjective κ :=
        CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective.comp hαs
      have hκV : ∀ k : ↥K, κ k = 1 → (k : G) ∈ centralizer (V : Set G) := by
        intro k hk
        have h1 : α k = 1 :=
          CFSG.QuasithinUnique.Vol2Native.A312L.proj_injective_charTwo (hk.trans
            (map_one (CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.proj 2 F)).symm)
        exact hOV k (hαk ▸ MonoidHom.mem_ker.2 h1)
      obtain ⟨U, B, hU, hB, hBle, f, hf⟩ :=
        exists_lFamily_of_hom hXK hT0X hTK0 hXq hθ κ hκ fun x hx => hθV x (hκV _ hx)
      refine false_of_sp4 hF4 hU hB (fun htop => hmax.2.1 ?_) hf
      refine autOn_eq_of_map_eq_top hKV κ hκV (eq_top_iff.2 ?_)
      rw [← htop]
      exact hBle.trans (range_le_map_inf hXK hXMK κ)
  ·
    obtain ⟨-, hG2, -⟩ := hF
    exact false_of_card_not_dvd (A4.autOn_mono (hXK.trans le_sup_left))
      (by rw [hG2.1]; norm_num) hfY
  ·
    obtain ⟨⟨n, F, _, _, hn1, hF, ⟨ψ⟩⟩, hmax, -⟩ := hGg
    let κ : ↥K →* Matrix.SpecialLinearGroup (Fin 3) F :=
      ((specialLinearGroupEquivStatedSL 3 F).symm.toMonoidHom.comp ψ.toMonoidHom).comp actK
    have hκ : Function.Surjective κ :=
      ((specialLinearGroupEquivStatedSL 3 F).symm.surjective.comp ψ.surjective).comp hactK
    have hκV : ∀ k : ↥K, κ k = 1 → (k : G) ∈ centralizer (V : Set G) := by
      intro k hk
      have hk' : (specialLinearGroupEquivStatedSL 3 F).symm (ψ (actK k)) = 1 := hk
      rw [map_eq_one_iff _ (specialLinearGroupEquivStatedSL 3 F).symm.injective,
        map_eq_one_iff _ ψ.injective] at hk'
      exact hactV k hk'
    obtain ⟨U, B, hU, hB, hBle, f, hf⟩ :=
      exists_lFamily_of_hom hXK hT0X hTK0 hXq hθ κ hκ fun x hx => hθV x (hκV _ hx)
    refine false_of_sl3 hn1 hF hU hB (fun htop => hmax.2.1 ?_) hf
    refine autOn_eq_of_map_eq_top hKV κ hκV (eq_top_iff.2 ?_)
    rw [← htop]
    exact hBle.trans (range_le_map_inf hXK hXMK κ)
  ·
    obtain ⟨hiso, -, -⟩ := hH
    rcases hiso with hψ | hψ
    · let ψ := hψ.some
      let κ : ↥K →* Matrix.SpecialLinearGroup (Fin 4) (ZMod 2) :=
        ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.toMonoidHom.comp ψ.toMonoidHom).comp
          actK
      have hκ : Function.Surjective κ :=
        ((specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.surjective.comp ψ.surjective).comp
          hactK
      have hκV : ∀ k : ↥K, κ k = 1 → (k : G) ∈ centralizer (V : Set G) := by
        intro k hk
        have hk' : (specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm (ψ (actK k)) = 1 := hk
        rw [map_eq_one_iff _ (specialLinearGroupEquivStatedSL 4 (ZMod 2)).symm.injective,
          map_eq_one_iff _ ψ.injective] at hk'
        exact hactV k hk'
      obtain ⟨U, B, hU, hB, -, f, hf⟩ :=
        exists_lFamily_of_hom hXK hT0X hTK0 hXq hθ κ hκ fun x hx => hθV x (hκV _ hx)
      exact false_of_sl_two (ZMod.card 2) le_rfl (by norm_num) hU hB hf
    · let ψ := hψ.some
      let κ : ↥K →* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
        ((specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm.toMonoidHom.comp ψ.toMonoidHom).comp
          actK
      have hκ : Function.Surjective κ :=
        ((specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm.surjective.comp ψ.surjective).comp
          hactK
      have hκV : ∀ k : ↥K, κ k = 1 → (k : G) ∈ centralizer (V : Set G) := by
        intro k hk
        have hk' : (specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm (ψ (actK k)) = 1 := hk
        rw [map_eq_one_iff _ (specialLinearGroupEquivStatedSL 5 (ZMod 2)).symm.injective,
          map_eq_one_iff _ ψ.injective] at hk'
        exact hactV k hk'
      obtain ⟨U, B, hU, hB, -, f, hf⟩ :=
        exists_lFamily_of_hom hXK hT0X hTK0 hXq hθ κ hκ fun x hx => hθV x (hκV _ hx)
      exact false_of_sl_two (ZMod.card 2) (by norm_num) le_rfl hU hB hf

end CFSG.Quasithin.H13.A7
