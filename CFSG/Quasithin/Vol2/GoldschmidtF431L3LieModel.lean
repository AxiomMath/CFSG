module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpModelLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3Order
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieV1
public import CFSG.Quasithin.Vol2.GoldschmidtF431L3LieV2
import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelL3

public section

namespace CFSG.Quasithin.H13.F431.L3

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Blueprint
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour

section Identify

theorem no_normal_two_subgroup {F : Type} [Field F] [Finite F] :
    ∀ P : Subgroup (projectiveSL 3 F), P.Normal → IsPGroup 2 P → P = ⊥ := by
  intro P hP hp
  have hsimple : IsSimpleGroup (projectiveSL 3 F) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3) (K := F) le_rfl
  rcases hP.eq_bot_or_eq_top with h | h
  · exact h
  · exfalso
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp' : IsPGroup 2 (projectiveSL 3 F) := by
      rw [h] at hp
      exact hp.of_equiv Subgroup.topEquiv
    have hnt : Nontrivial (projectiveSL 3 F) := hsimple.toNontrivial
    have hc := hp'.center_nontrivial
    obtain ⟨⟨z, hz⟩, hz1⟩ := exists_ne (1 : Subgroup.center (projectiveSL 3 F))
    apply hz1
    apply Subtype.ext
    exact CFSG.QuasithinUnique.Fin257.L3.center_trivial_M z
      (fun y => (Subgroup.mem_center_iff.mp hz y).symm)

theorem exists_equiv_projSL3 {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSL 3 2 f) :
    1 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
      Nat.card F = 2 ^ f ∧ Nonempty (D ≃* projectiveSL 3 F) := by
  rcases hD with ⟨-, hM⟩ | ⟨h0, -⟩ | ⟨h0, -⟩ | ⟨h0, -⟩
  · obtain ⟨hadm, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hM
    have hf1 : 1 ≤ f := hadm.2.1
    have hchar : CharP K 2 := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f)
        (by rw [← Nat.card_eq_fintype_card]; exact hKcard)
    exact ⟨hf1, K, hKf, hKfin, hchar, hKcard,
      ⟨e.trans (CFSG.QuasithinUnique.Id2519.projectiveSLEquivStatedProj 3 K).symm⟩⟩
  all_goals exact absurd h0 (by norm_num)

theorem l3Amalgam_borel {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSL 3 2 f)
    (A : LieAmalgamExt D) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (E : D ≃* projectiveSL 3 F),
      Nat.card F = 2 ^ f ∧
      ((A.P1.map E.toMonoidHom = Subgroup.normalizer
          ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
            Set (projectiveSL 3 F)) ∧
        A.P2.map E.toMonoidHom = Subgroup.normalizer
          ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
            Set (projectiveSL 3 F))) ∨
      (A.P1.map E.toMonoidHom = Subgroup.normalizer
          ((CFSG.QuasithinUnique.Fin257.L3.V2 : Subgroup (projectiveSL 3 F)) :
            Set (projectiveSL 3 F)) ∧
        A.P2.map E.toMonoidHom = Subgroup.normalizer
          ((CFSG.QuasithinUnique.Fin257.L3.V1 : Subgroup (projectiveSL 3 F)) :
            Set (projectiveSL 3 F)))) := by
  obtain ⟨-, F, hFf, hFfin, hFchar, hFcard, ⟨e1⟩⟩ := exists_equiv_projSL3 hD
  have hy1 := A.yam.map e1
  have hU := CFSG.QuasithinUnique.Fin257.L3.isSylowTwoOf_U (F := F)
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj hy1.1 hU
  let E : D ≃* projectiveSL 3 F := e1.trans (MulAut.conj h)
  have hy2 : IsYAmalgamPair (projUnitriangular 3 F) (A.P1.map E.toMonoidHom)
      (A.P2.map E.toMonoidHom) := by
    have := A.yam.map E
    have hTD : A.TD.map E.toMonoidHom = projUnitriangular 3 F := by
      rw [hh, Subgroup.map_map]
      rfl
    rwa [hTD] at this
  exact ⟨F, hFf, hFfin, hFchar, E, hFcard,
    CFSG.QuasithinUnique.Borel252.BorelData.yam_cases
      CFSG.QuasithinUnique.Borel252.L3.borelData_L3 no_normal_two_subgroup hy2⟩

end Identify

section Data

open CFSG.QuasithinUnique.Borel252 CFSG.QuasithinUnique.Fin257.L3

theorem l3DData_projectiveSL {F : Type} [Field F] [Finite F] [CharP F 2] (hq : 4 ≤ Nat.card F) :
    L3DData (projUnitriangular 3 F) (V1 : Subgroup (projectiveSL 3 F)) V2 (P3.torus3 F)
      (s₂₃P : projectiveSL 3 F) (s₁₂P : projectiveSL 3 F) := by
  have hq' : 2 < Nat.card F := by omega
  have hK : ∃ s : Finset F, s.card = 4 := by
    have := Fintype.ofFinite F
    obtain ⟨s, -, hs⟩ := Finset.exists_subset_card_eq (s := (Finset.univ : Finset F)) (n := 4)
      (by simpa [Nat.card_eq_fintype_card] using hq)
    exact ⟨s, hs⟩
  refine
    { borel := CFSG.QuasithinUnique.Borel252.L3.borelData_L3
      frame := P3.frame_U
      B₀_le := P3.torus3_le_normalizer
      B₀_odd := P3.torus3_odd
      mul := fun h hh => P3.torus3_mul hh
      trans := fun x hx hx1 y hy hy1 => ?_
      centS := fun x hx hc => P3.torus3_centS hq' hx hc
      cent := fun x hx hx1 => ?_
      half₁ := P3.half_V1 hK hq'
      half₂ := P3.half_V2 hK hq'
      rot := P3.s₂₃_mul_s₁₂_cube
      Z_big := ?_ }
  · rw [P3.centerOf_U] at hx hy
    exact P3.torus3_trans hx hy hx1 hy1
  · rw [P3.centerOf_U] at hx
    exact P3.centralizer_wP_le hx hx1
  · obtain ⟨ω, hω⟩ := P3.exists_unit_ne_one hq'
    have hω0 : (ω : F) ≠ 0 := ω.ne_zero
    have hω1 : (ω : F) ≠ 1 := fun h => hω (Units.ext h)
    refine ⟨wP 1, ?_, wP (ω : F), ?_, ?_, ?_, ?_⟩
    · rw [P3.centerOf_U]; exact ⟨1, rfl⟩
    · rw [P3.centerOf_U]; exact ⟨(ω : F), rfl⟩
    · exact fun h => one_ne_zero ((wP_eq_one_iff _).mp h)
    · exact fun h => hω0 ((wP_eq_one_iff _).mp h)
    · exact fun h => hω1 (wP_injective h).symm

end Data

theorem mem_normalizer_map_equiv {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G')
    (H : Subgroup G) (g : G') :
    g ∈ Subgroup.normalizer ((H.map φ.toMonoidHom : Subgroup G') : Set G') ↔
      φ.symm g ∈ Subgroup.normalizer (H : Set G) := by
  rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
  have e : ∀ x : G, φ.symm (g * φ x * g⁻¹) = φ.symm g * x * (φ.symm g)⁻¹ := fun x => by simp
  constructor
  · intro h x
    have h1 := h (φ x)
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, e] at h1
    exact h1
  · intro h y
    obtain ⟨x, rfl⟩ := φ.surjective y
    rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, e]
    exact h x

end CFSG.Quasithin.H13.F431.L3

namespace CFSG.Quasithin.H13.F431

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open CFSG.Blueprint
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour
  CFSG.QuasithinUnique.Borel252 CFSG.Quasithin.H13.F431.L3

theorem f431ModelFacts_psl3 (f : ℕ) : F431ModelFacts .PSL 3 f := by
  intro D _ hD
  obtain ⟨-, F, hFf, hFfin, hFchar, hFcard, ⟨e⟩⟩ := exists_equiv_projSL3 hD
  refine ⟨Finite.of_injective e e.injective, ?_⟩
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  apply e.injective
  rw [map_one]
  apply CFSG.QuasithinUnique.Fin257.L3.center_trivial_M
  intro y
  obtain ⟨x, rfl⟩ := e.surjective y
  have := Subgroup.mem_center_iff.mp hd x
  rw [← map_mul, ← map_mul, this]

theorem sup_eq_top_psl3 {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSL 3 2 f)
    (A : LieAmalgamExt D) : A.P1 ⊔ A.P2 = ⊤ := by
  obtain ⟨F, hFf, hFfin, hFchar, E, hFcard, hP⟩ := l3Amalgam_borel hD A
  have hmap : (A.P1 ⊔ A.P2).map E.toMonoidHom = ⊤ := by
    rw [Subgroup.map_sup]
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      exact CFSG.QuasithinUnique.Borel252.L3.borelData_L3.sup_norm
    · rw [h1, h2, sup_comm]
      exact CFSG.QuasithinUnique.Borel252.L3.borelData_L3.sup_norm
  rw [eq_top_iff]
  intro x _
  have hx : E x ∈ (A.P1 ⊔ A.P2).map E.toMonoidHom := by rw [hmap]; exact Subgroup.mem_top _
  obtain ⟨y, hy, hyx⟩ := hx
  have : y = x := E.injective hyx
  rwa [this] at hy

theorem f431Generation_psl3 (f : ℕ) : F431Generation .PSL 3 f := by
  intro D _ hD A
  exact range_conj_le_K A (sup_eq_top_psl3 hD A)

theorem f431L3Lie (f : ℕ) : F431L3Lie f := by
  intro hf D _ hD A hodd
  obtain ⟨F, hFf, hFfin, hFchar, E, hFcard, hP⟩ := l3Amalgam_borel hD A
  have hq4 : 4 ≤ Nat.card F := by
    rw [hFcard]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hdata := l3DData_projectiveSL hq4
  obtain ⟨R₁, R₂, s₁, s₂, hdat, h1, h2⟩ : ∃ (R₁ R₂ : Subgroup (projectiveSL 3 F))
      (s₁ s₂ : projectiveSL 3 F), L3DData (projUnitriangular 3 F) R₁ R₂ (P3.torus3 F) s₁ s₂ ∧
      A.P1.map E.toMonoidHom = Subgroup.normalizer (R₁ : Set (projectiveSL 3 F)) ∧
      A.P2.map E.toMonoidHom = Subgroup.normalizer (R₂ : Set (projectiveSL 3 F)) := by
    rcases hP with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨_, _, _, _, hdata, h1, h2⟩
    · exact ⟨_, _, _, _, hdata.swap, h1, h2⟩
  have hfinD : Finite D := Finite.of_injective E E.injective
  have hfinX : Finite (projectiveSL 3 F) := Finite.of_equiv D E.toEquiv
  have hfinAut : Finite (MulAut D) := finite_mulAut_of_finite
  have hgen := f431Generation_psl3 f D hD A
  have hK : ∀ d : D, (MulAut.conj d : MulAut D) ∈ A.K := fun d => hgen ⟨d, rfl⟩
  have hcen := (f431ModelFacts_psl3 f D hD).2
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hdc : d ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut D => φ g) hd
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hcen] at hdc
    exact Subgroup.mem_bot.mp hdc
  set ΦD : D →* ↥A.K := (MulAut.conj : D →* MulAut D).codRestrict A.K hK with hΦD
  set Φ : projectiveSL 3 F →* ↥A.K := ΦD.comp E.symm.toMonoidHom with hΦ
  have hΦD_inj : Function.Injective ΦD := fun a b h => hinj (congrArg Subtype.val h)
  have hΦinj : Function.Injective Φ := hΦD_inj.comp E.symm.injective
  have hrange : Φ.range = ΦD.range := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨E.symm x, rfl⟩
    · rintro ⟨d, rfl⟩
      exact ⟨E d, by simp [hΦ]⟩
  have hnorm : Φ.range.Normal := by
    rw [hrange]
    refine ⟨fun n hn g => ?_⟩
    obtain ⟨d, rfl⟩ := hn
    exact ⟨(g : MulAut D) d, (codRestrict_conj_conj hK g d).symm⟩
  have hindex : Odd Φ.range.index := by
    have hcard := Subgroup.card_mul_index Φ.range
    have hrc : Nat.card Φ.range = Nat.card D := by
      rw [← Nat.card_congr (MonoidHom.ofInjective hΦinj).toEquiv]
      exact Nat.card_congr E.symm.toEquiv
    rw [hrc] at hcard
    have hpos : 0 < Nat.card D := Nat.card_pos
    have : Φ.range.index = Nat.card ↥A.K / Nat.card D := by
      rw [← hcard, Nat.mul_div_cancel_left _ hpos]
    rw [this]
    exact hodd
  have key : ∀ (P : Subgroup D) (r : Subgroup (projectiveSL 3 F)) (N' : Subgroup ↥A.K),
      P.map E.toMonoidHom = Subgroup.normalizer (r : Set (projectiveSL 3 F)) →
      pCoreOf 2 (Subgroup.normalizer (r : Set (projectiveSL 3 F))) = r →
      (∀ x : ↥A.K, x ∈ N' ↔ (x : MulAut D) ∈ autStab P) →
      N' = Subgroup.normalizer ((r.map Φ : Subgroup ↥A.K) : Set ↥A.K) := by
    intro P r N' hP hcore hN'
    set S : Subgroup D := r.map E.symm.toMonoidHom with hS
    have hnS : (Subgroup.normalizer (r : Set (projectiveSL 3 F))).map E.symm.toMonoidHom =
        Subgroup.normalizer (S : Set D) := by
      ext g
      rw [Subgroup.mem_map_equiv, hS, mem_normalizer_map_equiv E.symm r g]
    have hPS : P = Subgroup.normalizer (S : Set D) := by
      rw [← hnS, ← hP, Subgroup.map_map]
      ext g
      simp
    have hcoreS : pCoreOf 2 (Subgroup.normalizer (S : Set D)) = S := by
      rw [← hnS, pCoreOf_map_of_injective E.symm.toMonoidHom E.symm.injective, hcore]
    have hrS : r.map Φ = S.map ΦD := by
      rw [hS, Subgroup.map_map]
    ext x
    rw [hN' x, hrS, mem_normalizer_map_codRestrict_iff hK hinj S x, hPS,
      mem_autStab_iff_of_normalizer hcoreS]
  have hKM : ∀ x : ↥A.K, (x : MulAut D) ∈ A.Mbar := fun x => (sup_le inf_le_left inf_le_left :
    A.K ≤ A.Mbar) x.2
  have hN1 : A.Mb1 = Subgroup.normalizer ((R₁.map Φ : Subgroup ↥A.K) : Set ↥A.K) := by
    refine key A.P1 R₁ A.Mb1 h1 hdat.borel.core₁ ?_
    intro x
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hx => hx.2, fun hx => ⟨hKM x, hx⟩⟩
  have hN2 : A.Mb2 = Subgroup.normalizer ((R₂.map Φ : Subgroup ↥A.K) : Set ↥A.K) := by
    refine key A.P2 R₂ A.Mb2 h2 hdat.borel.core₂ ?_
    intro x
    rw [Subgroup.mem_subgroupOf]
    exact ⟨fun hx => hx.2, fun hx => ⟨hKM x, hx⟩⟩
  have : Φ.range.Normal := hnorm
  exact exists_l3Datum_of_data Φ hΦinj hindex hdat A.Mb1 A.Mb2 hN1 hN2

end CFSG.Quasithin.H13.F431
