module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenL34QuotientModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.CommutatorSectionFaithful
public import CFSG.Quasithin.Background.D2Transport
public import CFSG.Quasithin.Background.HFL3Alpha
public import CFSG.Quasithin.Background.F918Z4bDef

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 CFSG.Open Subgroup
open Matrix
open scoped Matrix

theorem rk_hMod_one {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) : rk (HMod 1 K) = 9 := by
  have h := CFSG.Quasithin.H.L3Nine.card_HMod (n := 1) (K := K) le_rfl hK
  rw [rk, h, padicValNat.prime_pow]

theorem mQuot_sup_eq_rk_map {V Q : Type} [CommGroup V] [CommGroup Q]
    (q : V →* Q) (A Z : Subgroup V) (hker : q.ker = Z) :
    E3.mQuot (A ⊔ Z) Z = rk ↥(A.map q) := by
  have hZmap : Z.map q = ⊥ := by
    rw [Subgroup.map_eq_bot_iff, hker]
  have hrel : Z.relIndex (A ⊔ Z) = Nat.card ↥(A.map q) := by
    rw [← hker, Subgroup.relIndex_ker, Subgroup.map_sup, hker, hZmap, sup_bot_eq]
  unfold E3.mQuot rk
  rw [hrel]

theorem three_le_rk_commSub_hermitian {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {t : MulAut (HMod 1 K)}
    (htN : t ∈ norm hK) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    3 ≤ rk ↥(commSub (⊤ : Subgroup (HMod 1 K)) (Subgroup.zpowers t)) := by
  classical
  have hcard : Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ 2 ^ (6 * 1) :=
    card_fixV_le_of_involution (n := 1) le_rfl hK htN ht2 ht1
  have hfixle : rk ↥(fixV (Subgroup.zpowers t)) ≤ 6 :=
    CFSG.Quasithin.rk_le_of_card_le_two_pow
      ((CFSG.Quasithin.isPGroup_two_of_sq_eq_one
        (fun x => CFSG.Quasithin.H.L3Nine.sq_eq_one_HMod x)).to_subgroup
          (fixV (Subgroup.zpowers t)))
      (by simpa using hcard)
  have hsplit := CFSG.Quasithin.rk_commV_add_rk_fixV (V := HMod 1 K) t
  rw [CFSG.Quasithin.commV_eq_commSub] at hsplit
  have hV := rk_hMod_one (K := K) hK
  omega

theorem exists_twisted_of_rk_le_three {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) {t : MulAut (HMod 1 K)}
    (htN : t ∈ norm hK) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (hrk : rk ↥(commSub (⊤ : Subgroup (HMod 1 K)) (Subgroup.zpowers t)) ≤ 3) :
    ∃ A : GL (Fin 3) K, t = rhoT hK A * fldAut (bar 1) ∧
      ∀ g : SpecialLinearGroup (Fin 3) K,
        t * rho hK g * t⁻¹ =
          rho hK (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation 3 K A
            (SpecialLinearGroup.map (bar 1).toRingHom g)) := by
  classical
  rcases exists_of_involution (n := 1) le_rfl hK htN ht2 with ⟨A, hA | hA⟩
  ·
    exfalso
    have hρ1 : rhoT hK A ≠ 1 := by
      rw [← hA]
      exact ht1
    have hcard := card_fixV_rhoT_le (n := 1) le_rfl hK hρ1
    have hfixle : rk ↥(fixV (Subgroup.zpowers (rhoT hK A))) ≤ 5 :=
      CFSG.Quasithin.rk_le_of_card_le_two_pow
        ((CFSG.Quasithin.isPGroup_two_of_sq_eq_one
          (fun x => CFSG.Quasithin.H.L3Nine.sq_eq_one_HMod x)).to_subgroup
            (fixV (Subgroup.zpowers (rhoT hK A))))
        (by simpa using hcard)
    have hsplit := CFSG.Quasithin.rk_commV_add_rk_fixV (V := HMod 1 K) (rhoT hK A)
    rw [CFSG.Quasithin.commV_eq_commSub] at hsplit
    have hcomm : rk ↥(commSub (⊤ : Subgroup (HMod 1 K))
        (Subgroup.zpowers (rhoT hK A))) ≤ 3 := by
      rw [hA] at hrk
      exact hrk
    have hV := rk_hMod_one (K := K) hK
    omega
  · refine ⟨A, hA, fun g => ?_⟩
    rw [hA]
    exact conj_rho_eq hK A (bar 1) g

theorem ker_rho_eq_center {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = (2 ^ 1) ^ 2) :
    (rho hK).ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
  rw [← CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center]
  ext g
  rw [MonoidHom.mem_ker]
  constructor
  · intro hg
    exact mem_scalars_of_rho_eq_one hK hg
  · intro hg
    obtain ⟨c, hc, hcoe⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.mem_scalars.mp hg
    have hg' : g = CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc :=
      Subtype.ext hcoe
    rw [hg']
    change rhoT hK (SpecialLinearGroup.toGL
      (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc)) = 1
    rw [show SpecialLinearGroup.toGL
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalarElement c hc) = scalGL c from ?_]
    exact CFSG.Quasithin.H.ModelType.rhoT_scalGL_eq_one hK c
    apply Units.ext
    rw [CFSG.Quasithin.H.L3Nine.coe_scalGL,
      Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.coe_scalarElement,
      Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]

theorem isLn_autSub_of_isLn {W : Type} [CommGroup W] {H : Subgroup (MulAut W)}
    {U : Subgroup W} (hHU : H ≤ stabSub U) (hfaith : H ⊓ centSub U = ⊥)
    (hH : IsLn ↥H 3 2) : IsLn ↥(autSub H U) 3 2 :=
  CFSG.Blueprint.LieModel.of_mulEquiv (autSubEquivOfFaithful hHU hfaith) hH

theorem isQuasisimple_open_of_isLn {H : Type} [Group H] (hH : IsLn H 3 2) :
    CFSG.Open.IsQuasisimple H := by
  have h1 := CFSG.Quasithin.H13.E54.isQuasisimple_of_lieModel hH
  exact ⟨Group.isPerfect_def.mp h1.1, h1.2.1⟩

theorem l34_section_mQuot_core
    {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {t : MulAut W}
    (hW : ∀ w : W, w ^ 2 = 1)
    (hH : IsLn ↥H 3 2)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (commSub (⊤ : Subgroup W) H)
      (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 9)
    (htN : t ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (ht2 : t ^ 2 = 1)
    (htU : ∃ u ∈ commSub (⊤ : Subgroup W) H, t u ≠ u) :
    3 ≤ E3.mQuot
        (commSub (commSub (⊤ : Subgroup W) H) (Subgroup.zpowers t) ⊔
          (commSub (⊤ : Subgroup W) H ⊓ fixV H))
        (commSub (⊤ : Subgroup W) H ⊓ fixV H) ∧
      (rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3 →
        E3.mQuot
          (commSub (commSub (⊤ : Subgroup W) H) (Subgroup.zpowers t) ⊔
            (commSub (⊤ : Subgroup W) H ⊓ fixV H))
          (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 3 ∧
        ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
          Nat.card F = 4 ∧
          ∃ π : Matrix.SpecialLinearGroup (Fin 3) F →* ↥H,
            Function.Surjective π ∧
            π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) ∧
            ∃ A : GL (Fin 3) F,
              ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
                t * (π g : MulAut W) * t⁻¹ =
                  (π (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
                    3 F A (Matrix.SpecialLinearGroup.map
                      (CFSG.Quasithin.H.SU3.bar 1 : F ≃+* F).toRingHom g)) : MulAut W)) := by
  classical
  set U : Subgroup W := commSub (⊤ : Subgroup W) H with hU
  set Z : Subgroup W := U ⊓ fixV H with hZ
  have hirr' := hirr
  rw [irrSet, Set.mem_setOf_eq] at hirr'
  obtain ⟨hcommU, hIirr⟩ := hirr'
  have hHU : H ≤ stabSub U := CFSG.Quasithin.le_stabSub_of_forall_mem hIirr.2.1
  have hne : ¬ H ≤ centSub U := by
    intro hHc
    have hUfix : U ≤ fixV H := fun u hu h hh => hHc hh u hu
    have hbot : commSub U H = ⊥ := commSub_eq_bot_iff.mpr hUfix
    rw [hcommU] at hbot
    have hlt := hIirr.1
    rw [hbot] at hlt
    simp only [bot_inf_eq] at hlt
    exact absurd hlt (lt_irrefl _)
  have hsimpleH : IsSimpleGroup ↥H := CFSG.Quasithin.H13.E54.isSimpleGroup_of_lieModel hH
  have hqH : CFSG.Open.IsQuasisimple ↥H := isQuasisimple_open_of_isLn hH
  have hfaith : H ⊓ centSub U = ⊥ := inf_centSub_eq_bot_of_isSimpleGroup hsimpleH hHU hne
  let HU : Subgroup (MulAut U) := autSub H U
  let e : ↥H ≃* ↥HU := autSubEquivOfFaithful hHU hfaith
  have hHUisLn : IsLn ↥HU 3 2 := isLn_autSub_of_isLn hHU hfaith hH
  have htUmem : t ∈ stabSub U := by
    have h := CFSG.Quasithin.FixVLat.mem_stabSub_commV_of_mem_normalizer (X := H) htN
    rwa [commV_eq_commSub] at h
  let tU : MulAut U := resHom U ⟨t, htUmem⟩
  have hWU : ∀ u : U, u ^ 2 = 1 := fun u => Subtype.ext (by simpa using hW (u : W))
  have hcommHU : commSub (⊤ : Subgroup U) HU = ⊤ := commSub_top_autSub_eq_top hHU hcommU
  have hdimHU : E3.mQuot (⊤ : Subgroup U) (fixV HU) = 9 := by
    have hrel := Subgroup.relIndex_map_map_of_injective (fixV HU) (⊤ : Subgroup U)
      U.subtype_injective
    rw [map_subtype_fixV_autSub hHU, Subgroup.map_top, Subgroup.range_subtype] at hrel
    unfold E3.mQuot
    rw [← hrel]
    exact hdim
  have hirrHU : commSub (⊤ : Subgroup U) HU ∈ irrSet HU :=
    mem_irrSet_autSub_of_mem_irrSet hHU hirr
  have hmodel : BinaryNineTensor HU ⊤ (fixV HU) 1 :=
    binaryNineTensor_of_l34_quotient_rank_nine hWU hHUisLn hcommHU hirrHU hdimHU
  have htU2 : tU ^ 2 = 1 := by
    have h2 : (⟨t, htUmem⟩ : ↥(stabSub U)) ^ 2 = 1 := by
      apply Subtype.ext
      simpa [pow_two] using ht2
    calc tU ^ 2 = (resHom U ⟨t, htUmem⟩) ^ 2 := rfl
      _ = resHom U ((⟨t, htUmem⟩ : ↥(stabSub U)) ^ 2) := by rw [map_pow]
      _ = resHom U 1 := by rw [h2]
      _ = 1 := map_one _
  have htU1 : tU ≠ 1 := by
    obtain ⟨u, huU, htu⟩ := htU
    intro h1
    have h2 : tU ⟨u, huU⟩ = ⟨u, huU⟩ := by rw [h1]; rfl
    have h3 : t u = u := by
      have h4 : ((tU ⟨u, huU⟩ : U) : W) = ((⟨u, huU⟩ : U) : W) :=
        congrArg Subtype.val h2
      simpa [tU, resHom_apply] using h4
    exact htu h3
  have htNU : tU ∈ Subgroup.normalizer (HU : Set (MulAut U)) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hHmap : H.map (MulAut.conj t).toMonoidHom = H := by
      simpa using (Subgroup.mem_normalizer_iff_map_conj_eq).mp htN
    have h := CFSG.Quasithin.StabLat.autSub_map_conj_eq (X := H) (U := U) htUmem
    rw [hHmap] at h
    exact h.symm
  have hqHU : CFSG.Open.IsQuasisimple ↥HU := CFSG.Open.IsQuasisimple.of_mulEquiv e.symm hqH
  obtain ⟨Q, hQc, hQf, q, ρ, hqsurj, hqker, hρinj, heq, -, -, -⟩ :=
    s16k_qm_quotMap (W := U) (H := HU) hqHU hcommHU hWU
  have htZ : tU ∈ stabSub (fixV HU) :=
    CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer
      (X := Subgroup.zpowers tU) (K := HU) (Subgroup.zpowers_le.mpr htNU)
      (Subgroup.mem_zpowers tU)
  have hφ : ∀ u : U, q u = 1 ↔ q (tU u) = 1 := by
    intro u
    rw [hqker u, hqker (tU u)]
    exact (mem_stabSub.mp htZ u).symm
  obtain ⟨tQ, htQ⟩ := s16g_exists_induced_aut q hqsurj (φ := tU) hφ
  have htQ2 : tQ * tQ = 1 := by
    ext x
    obtain ⟨u, rfl⟩ := hqsurj x
    rw [MulAut.mul_apply, htQ, htQ]
    have h2 : tU (tU u) = u := by
      have h := congrArg (fun f : MulAut U => f u) htU2
      simpa [pow_two] using h
    rw [h2, MulAut.one_apply]
  have htQinv : ∀ u : U, tQ⁻¹ (q u) = q (tU⁻¹ u) := by
    intro u
    apply tQ.injective
    calc tQ (tQ⁻¹ (q u)) = q u := MulEquiv.apply_symm_apply tQ (q u)
      _ = q (tU (tU⁻¹ u)) := by rw [MulAut.apply_inv_self]
      _ = tQ (q (tU⁻¹ u)) := (htQ (tU⁻¹ u)).symm
  have htQconj : ∀ k : ↥HU, tQ * ρ k * tQ⁻¹ =
      ρ ⟨tU * (k : MulAut U) * tU⁻¹,
        (Subgroup.mem_normalizer_iff.mp htNU k).mp k.2⟩ := by
    intro k
    ext x
    obtain ⟨u, rfl⟩ := hqsurj x
    calc (tQ * ρ k * tQ⁻¹) (q u)
        = tQ (ρ k (tQ⁻¹ (q u))) := by rw [MulAut.mul_apply, MulAut.mul_apply]
      _ = tQ (ρ k (q (tU⁻¹ u))) := by rw [htQinv]
      _ = tQ (q ((k : MulAut U) (tU⁻¹ u))) := by rw [heq k (tU⁻¹ u)]
      _ = q (tU ((k : MulAut U) (tU⁻¹ u))) := htQ _
      _ = q ((tU * k * tU⁻¹) u) := by simp [MulAut.mul_apply]
      _ = ρ ⟨tU * k * tU⁻¹,
            (Subgroup.mem_normalizer_iff.mp htNU k).mp k.2⟩ (q u) :=
          heq ⟨tU * k * tU⁻¹, (Subgroup.mem_normalizer_iff.mp htNU k).mp k.2⟩ u
  have htQ1 : tQ ≠ 1 := by
    intro h1
    have hcentral : ∀ k ∈ HU, tU * k = k * tU := by
      intro k hk
      have hmem : tU * k * tU⁻¹ ∈ HU :=
        (Subgroup.mem_normalizer_iff.mp htNU k).mp hk
      have hconj : ρ ⟨tU * k * tU⁻¹, hmem⟩ = ρ ⟨k, hk⟩ := by
        rw [← htQconj ⟨k, hk⟩, h1]
        simp
      have heqk : (⟨tU * k * tU⁻¹, hmem⟩ : ↥HU) = ⟨k, hk⟩ := hρinj hconj
      have hval := congrArg Subtype.val heqk
      change tU * k * tU⁻¹ = k at hval
      calc tU * k = tU * k * tU⁻¹ * tU := by group
        _ = k * tU := by rw [hval]
    have hfix : ∀ u : U, tU u * u⁻¹ ∈ fixV HU := by
      intro u
      rw [← hqker]
      have h2 : q (tU u * u⁻¹) = 1 := by
        calc q (tU u * u⁻¹) = q (tU u) * (q u)⁻¹ := by rw [map_mul, map_inv]
          _ = tQ (q u) * (q u)⁻¹ := by rw [← htQ u]
          _ = q u * (q u)⁻¹ := by rw [h1, MulAut.one_apply]
          _ = 1 := by simp
      exact h2
    exact htU1 (s16g_eq_one_of_commSub hcommHU hcentral hfix)
  obtain ⟨K, hKfield, hKfin, hKchar, hKcard, hReal⟩ := hmodel
  have hK4 : Nat.card K = 4 := by simpa using hKcard
  have hK' : Nat.card K = (2 ^ 1) ^ 2 := by simpa using hKcard
  have hkerq : q.ker = fixV HU := by
    ext x
    rw [MonoidHom.mem_ker, hqker]
  have hRealQ : (FFModel.twistTensor 1 (StatedSL 3 K)).Realizes (ρ.range) ⊤ ⊥ := by
    have h := s16k_realizes_map (D := FFModel.twistTensor 1 (StatedSL 3 K))
      (H := HU) (H' := ρ.range) (U := ⊤) (Z := fixV HU) hReal q hkerq.le
      ρ.rangeRestrict ρ.rangeRestrict_surjective (fun h u => heq h u)
    have htop : (⊤ : Subgroup U).map q = ⊤ := Subgroup.map_top_of_surjective _ hqsurj
    have hbot : (fixV HU).map q = ⊥ := by
      rw [Subgroup.map_eq_bot_iff]
      intro z hz
      exact (hqker z).mpr hz
    rwa [htop, hbot] at h
  obtain ⟨eQ, heQ⟩ := CFSG.Quasithin.H.L3Nine.exists_model (K := K) (n := 1) hK' hRealQ
  let τ : MulAut (HMod 1 K) := MulAut.congr eQ tQ
  have hτ2 : τ * τ = 1 := by
    show MulAut.congr eQ tQ * MulAut.congr eQ tQ = 1
    rw [← map_mul, htQ2, map_one]
  have hτ1 : τ ≠ 1 := by
    intro h
    apply htQ1
    ext x
    have hx := congrFun (congrArg DFunLike.coe h) (eQ x)
    have h2 : eQ (tQ x) = eQ x := by
      simpa [τ, MulAut.congr_apply] using hx
    exact eQ.injective h2
  have htQN : tQ ∈ Subgroup.normalizer (ρ.range : Set (MulAut Q)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨⟨tU * (k : MulAut U) * tU⁻¹,
        (Subgroup.mem_normalizer_iff.mp htNU k).mp k.2⟩, (htQconj k).symm⟩
    · intro hx
      obtain ⟨k, hk⟩ := hx
      refine ⟨⟨tU * (k : MulAut U) * tU⁻¹,
        (Subgroup.mem_normalizer_iff.mp htNU k).mp k.2⟩, ?_⟩
      have hinv : tQ⁻¹ = tQ := inv_eq_of_mul_eq_one_right htQ2
      calc ρ ⟨tU * (k : MulAut U) * tU⁻¹,
            (Subgroup.mem_normalizer_iff.mp htNU k).mp k.2⟩ = tQ * ρ k * tQ⁻¹ :=
            (htQconj k).symm
        _ = tQ * (tQ * x * tQ⁻¹) * tQ⁻¹ := by rw [hk]
        _ = x := by
          rw [hinv]
          calc tQ * (tQ * x * tQ) * tQ = (tQ * tQ) * x * (tQ * tQ) := by group
            _ = x := by rw [htQ2]; simp
  have hτN : τ ∈ CFSG.Quasithin.H.L3Nine.norm hK' := by
    rw [CFSG.Quasithin.H.L3Nine.norm, ← heQ,
      ← Subgroup.map_equiv_normalizer_eq (ρ.range) (MulAut.congr eQ)]
    exact Subgroup.mem_map_of_mem _ htQN
  have h3τ : 3 ≤ rk ↥(commSub (⊤ : Subgroup (HMod 1 K)) (Subgroup.zpowers τ)) :=
    three_le_rk_commSub_hermitian hK' hτN hτ2 hτ1
  have hA_map : (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)).map q =
      commSub (⊤ : Subgroup Q) (Subgroup.zpowers tQ) := by
    have hcomp : q.comp (commHom tU) = (commHom tQ).comp q := by
      ext u
      simp only [MonoidHom.comp_apply, commHom_apply, map_mul, map_inv, htQ]
    calc (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)).map q
        = (commV (Subgroup.zpowers tU)).map q := by rw [commV_eq_commSub]
      _ = ((⊤ : Subgroup U).map (commHom tU)).map q := by rw [commV_zpowers_eq_map]
      _ = (⊤ : Subgroup U).map (q.comp (commHom tU)) := by rw [Subgroup.map_map]
      _ = (⊤ : Subgroup U).map ((commHom tQ).comp q) := by rw [hcomp]
      _ = ((⊤ : Subgroup U).map q).map (commHom tQ) := by rw [← Subgroup.map_map]
      _ = (⊤ : Subgroup Q).map (commHom tQ) := by
            rw [Subgroup.map_top_of_surjective _ hqsurj]
      _ = commV (Subgroup.zpowers tQ) := by rw [commV_zpowers_eq_map]
      _ = commSub (⊤ : Subgroup Q) (Subgroup.zpowers tQ) := by rw [commV_eq_commSub]
  have hq_tQ : E3.mQuot (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU) ⊔ fixV HU)
      (fixV HU) = rk ↥(commSub (⊤ : Subgroup Q) (Subgroup.zpowers tQ)) := by
    have h := mQuot_sup_eq_rk_map (q := q) (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU))
      (fixV HU) hkerq
    rwa [hA_map] at h
  have hq_restrict : E3.mQuot (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU) ⊔ fixV HU)
      (fixV HU) = E3.mQuot (commSub U (Subgroup.zpowers t) ⊔ Z) Z := by
    have hmapZ : (fixV HU).map U.subtype = Z := by
      rw [map_subtype_fixV_autSub hHU, hZ]
    have hmapK : (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU) ⊔ fixV HU).map
        U.subtype = commSub U (Subgroup.zpowers t) ⊔ Z := by
      rw [Subgroup.map_sup, map_commSub_zpowers_resHom htUmem, hmapZ]
    have hrel := Subgroup.relIndex_map_map_of_injective (fixV HU)
      (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU) ⊔ fixV HU) U.subtype_injective
    rw [hmapZ, hmapK] at hrel
    unfold E3.mQuot
    exact congrArg (padicValNat 2) hrel.symm
  have hq_tau : rk ↥(commSub (⊤ : Subgroup Q) (Subgroup.zpowers tQ)) =
      rk ↥(commSub (⊤ : Subgroup (HMod 1 K)) (Subgroup.zpowers τ)) := by
    have hmapτ : (commSub (⊤ : Subgroup Q) (Subgroup.zpowers tQ)).map eQ.toMonoidHom =
        commSub (⊤ : Subgroup (HMod 1 K)) (Subgroup.zpowers τ) := by
      rw [← CFSG.Quasithin.commSub_map_mulAutCongr eQ (⊤ : Subgroup Q)
          (Subgroup.zpowers tQ),
        Subgroup.map_top_of_surjective eQ.toMonoidHom eQ.surjective,
        MonoidHom.map_zpowers]
      rfl
    unfold rk
    rw [← hmapτ, Subgroup.card_map_of_injective eQ.injective]
  have hq_target : E3.mQuot (commSub U (Subgroup.zpowers t) ⊔ Z) Z =
      rk ↥(commSub (⊤ : Subgroup (HMod 1 K)) (Subgroup.zpowers τ)) := by
    rw [← hq_restrict, hq_tQ, hq_tau]
  refine ⟨?_, ?_⟩
  · rw [hq_target]
    exact h3τ
  · intro hrk
    have hKUrk : rk ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)) =
        rk ↥(commSub U (Subgroup.zpowers t)) := by
      have hcard : Nat.card ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)) =
          Nat.card ↥(commSub U (Subgroup.zpowers t)) := by
        rw [← map_commSub_zpowers_resHom htUmem]
        exact (Subgroup.card_map_of_injective (f := U.subtype)
          (K := commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)) U.subtype_injective).symm
      unfold rk
      rw [hcard]
    have hrk_tQ : rk ↥(commSub (⊤ : Subgroup Q) (Subgroup.zpowers tQ)) ≤ 3 := by
      have hcard := CFSG.Quasithin.B1More.card_map_mul_card_inf_ker
        (commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)) q
      rw [hA_map] at hcard
      have hsplit : rk ↥(commSub (⊤ : Subgroup Q) (Subgroup.zpowers tQ)) +
          rk ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers tU) ⊓ q.ker) =
          rk ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers tU)) := by
        have hpad : padicValNat 2 (Nat.card ↥(commSub (⊤ : Subgroup Q)
            (Subgroup.zpowers tQ)) * Nat.card ↥(commSub (⊤ : Subgroup U)
              (Subgroup.zpowers tU) ⊓ q.ker)) =
            padicValNat 2 (Nat.card ↥(commSub (⊤ : Subgroup U) (Subgroup.zpowers tU))) := by
          rw [hcard]
        rw [padicValNat.mul Nat.card_pos.ne' Nat.card_pos.ne'] at hpad
        simpa [rk] using hpad
      have hle : rk ↥(commSub U (Subgroup.zpowers t)) ≤
          rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) :=
        rk_mono (commSub_mono le_top le_rfl)
      omega
    have hrkτ : rk ↥(commSub (⊤ : Subgroup (HMod 1 K)) (Subgroup.zpowers τ)) ≤ 3 := by
      rw [← hq_tau]
      exact hrk_tQ
    have hq3 : E3.mQuot (commSub U (Subgroup.zpowers t) ⊔ Z) Z = 3 := by
      rw [hq_target]
      exact le_antisymm hrkτ h3τ
    refine ⟨hq3, ?_⟩
    obtain ⟨A, hAτ, hτeq⟩ := exists_twisted_of_rk_le_three hK' hτN hτ2 hτ1 hrkτ
    let eHB : ↥H ≃* ↥(ρ.range) :=
      e.trans (MulEquiv.ofBijective ρ.rangeRestrict
        ⟨fun a b hab => hρinj (congrArg Subtype.val hab), ρ.rangeRestrict_surjective⟩)
    have heHB : ∀ h : ↥H, ((eHB h : ↥(ρ.range)) : MulAut Q) = ρ (e h) := fun _ => rfl
    let eCong : ↥(ρ.range) ≃* ↥(img hK') :=
      (Subgroup.equivMapOfInjective (ρ.range) (CFSG.Quasithin.H.congrHom eQ)
        (CFSG.Quasithin.H.congrHom_injective eQ)).trans (MulEquiv.subgroupCongr heQ)
    have heCong : ∀ b : ↥(ρ.range),
        ((eCong b : ↥(img hK')) : MulAut (HMod 1 K)) =
          CFSG.Quasithin.H.congrHom eQ (b : MulAut Q) := fun _ => rfl
    let π : Matrix.SpecialLinearGroup (Fin 3) K →* ↥H :=
      eHB.symm.toMonoidHom.comp
        (eCong.symm.toMonoidHom.comp (rho hK').rangeRestrict)
    have hleft : ∀ g, eHB (π g) = eCong.symm ((rho hK').rangeRestrict g) := by
      intro g
      show eHB (eHB.symm (eCong.symm ((rho hK').rangeRestrict g))) = _
      rw [MulEquiv.apply_symm_apply]
    have hπsurj : Function.Surjective π := by
      intro h
      obtain ⟨b, hb⟩ := eHB.symm.surjective h
      obtain ⟨g, hg⟩ := MonoidHom.mem_range.mp (eCong b).2
      have hg' : (rho hK').rangeRestrict g = eCong b := Subtype.ext hg
      refine ⟨g, ?_⟩
      calc π g = eHB.symm (eCong.symm ((rho hK').rangeRestrict g)) := rfl
        _ = eHB.symm (eCong.symm (eCong b)) := by rw [hg']
        _ = eHB.symm b := by rw [MulEquiv.symm_apply_apply]
        _ = h := hb
    have hπker : π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) K) := by
      rw [← ker_rho_eq_center (K := K) hK']
      ext g
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      constructor
      · intro hg
        have h2 : (rho hK').rangeRestrict g = 1 := by
          have h3 := congrArg (fun x : ↥H => eHB x) hg
          simpa [π, MonoidHom.comp_apply] using h3
        exact congrArg Subtype.val h2
      · intro hg
        show eHB.symm (eCong.symm ((rho hK').rangeRestrict g)) = 1
        have h2 : (rho hK').rangeRestrict g = 1 := by
          apply Subtype.ext
          simpa using hg
        rw [h2, map_one, map_one]
    refine ⟨K, hKfield, hKfin, hKchar, hK4, π, hπsurj, hπker, A, ?_⟩
    intro g
    let hL : ↥H := ⟨t * (π g : MulAut W) * t⁻¹,
      (Subgroup.mem_normalizer_iff.mp htN (π g)).mp (π g).2⟩
    let hR : ↥H := π (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
      3 K A (Matrix.SpecialLinearGroup.map (bar 1).toRingHom g))
    have hright : eHB hR = eCong.symm
        ((rho hK').rangeRestrict (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
          3 K A (Matrix.SpecialLinearGroup.map (bar 1).toRingHom g))) := by
      show eHB (eHB.symm (eCong.symm ((rho hK').rangeRestrict _))) = _
      rw [MulEquiv.apply_symm_apply]
    have hleft' : ∀ g, CFSG.Quasithin.H.congrHom eQ (eHB (π g) : MulAut Q) =
        rho hK' g := by
      intro g
      rw [hleft g, ← heCong (eCong.symm ((rho hK').rangeRestrict g))]
      exact (congrArg (fun c : ↥(img hK') => (c : MulAut (HMod 1 K)))
        (MulEquiv.apply_symm_apply eCong ((rho hK').rangeRestrict g))).trans rfl
    have hnat' : CFSG.Quasithin.H.congrHom eQ (eHB hL : MulAut Q) =
        τ * rho hK' g * τ⁻¹ := by
      have hmemE : tU * (e (π g) : MulAut U) * tU⁻¹ ∈ HU :=
        (Subgroup.mem_normalizer_iff.mp htNU (e (π g))).mp (e (π g)).2
      have hee : e hL = (⟨tU * (e (π g) : MulAut U) * tU⁻¹, hmemE⟩ : ↥HU) := by
        apply Subtype.ext
        have h := autSubEquivOfFaithful_map_conj hHU hfaith htUmem
          (fun l hl => (Subgroup.mem_normalizer_iff.mp htN l).mp hl) (π g)
        simpa [hL] using h
      have hcoe : (eHB hL : MulAut Q) = tQ * (eHB (π g) : MulAut Q) * tQ⁻¹ := by
        calc (eHB hL : MulAut Q) = ρ (e hL) := rfl
          _ = ρ (⟨tU * (e (π g) : MulAut U) * tU⁻¹, hmemE⟩ : ↥HU) := by rw [hee]
          _ = tQ * ρ (e (π g)) * tQ⁻¹ := (htQconj (e (π g))).symm
          _ = tQ * (eHB (π g) : MulAut Q) * tQ⁻¹ := rfl
      calc CFSG.Quasithin.H.congrHom eQ (eHB hL : MulAut Q)
          = CFSG.Quasithin.H.congrHom eQ (tQ * (eHB (π g) : MulAut Q) * tQ⁻¹) := by
              rw [hcoe]
        _ = CFSG.Quasithin.H.congrHom eQ tQ *
              CFSG.Quasithin.H.congrHom eQ (eHB (π g) : MulAut Q) *
              (CFSG.Quasithin.H.congrHom eQ tQ)⁻¹ := by rw [map_mul, map_mul, map_inv]
        _ = τ * rho hK' g * τ⁻¹ := by rw [hleft' g]; rfl
    have heq' : CFSG.Quasithin.H.congrHom eQ (eHB hL : MulAut Q) =
        CFSG.Quasithin.H.congrHom eQ (eHB hR : MulAut Q) := by
      rw [hnat', hτeq g, hright,
        ← heCong (eCong.symm ((rho hK').rangeRestrict
          (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
            3 K A (Matrix.SpecialLinearGroup.map (bar 1).toRingHom g))))]
      exact (congrArg (fun c : ↥(img hK') => (c : MulAut (HMod 1 K)))
        (MulEquiv.apply_symm_apply eCong ((rho hK').rangeRestrict _))).symm
    have hcoeEq : (eHB hL : MulAut Q) = (eHB hR : MulAut Q) :=
      CFSG.Quasithin.H.congrHom_injective eQ heq'
    have heqH : hL = hR := eHB.injective (Subtype.ext hcoeEq)
    have hval : (hL : MulAut W) = (hR : MulAut W) := congrArg Subtype.val heqH
    exact hval

theorem l34_section_mQuot_eq_three_and_exists_field_action
    {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {t : MulAut W}
    (hW : ∀ w : W, w ^ 2 = 1)
    (hH : IsLn ↥H 3 2)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (hdim : E3.mQuot (commSub (⊤ : Subgroup W) H)
      (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 9)
    (htN : t ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (ht2 : t ^ 2 = 1)
    (htU : ∃ u ∈ commSub (⊤ : Subgroup W) H, t u ≠ u)
    (hrk : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) ≤ 3) :
    E3.mQuot
        (commSub (commSub (⊤ : Subgroup W) H) (Subgroup.zpowers t) ⊔
          (commSub (⊤ : Subgroup W) H ⊓ fixV H))
        (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 3 ∧
      ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2),
        Nat.card F = 4 ∧
        ∃ π : Matrix.SpecialLinearGroup (Fin 3) F →* ↥H,
          Function.Surjective π ∧
          π.ker = Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) ∧
          ∃ A : GL (Fin 3) F,
            ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
              t * (π g : MulAut W) * t⁻¹ =
                (π (CFSG.ComponentClassification.CatalogueBHigherLinearAction.slConjugation
                  3 F A (Matrix.SpecialLinearGroup.map
                    (CFSG.Quasithin.H.SU3.bar 1 : F ≃+* F).toRingHom g)) : MulAut W) :=
  (l34_section_mQuot_core hW hH hirr hdim htN ht2 htU).2 hrk

theorem mem_centralizer_of_l34_section_mQuot_eq_zero
    {W : Type} [CommGroup W] [Finite W]
    {H : Subgroup (MulAut W)} {t : MulAut W}
    (hW : ∀ w : W, w ^ 2 = 1)
    (hH : IsLn ↥H 3 2)
    (hirr : commSub (⊤ : Subgroup W) H ∈ irrSet H)
    (htN : t ∈ Subgroup.normalizer (H : Set (MulAut W)))
    (hzero : E3.mQuot
      (commSub (commSub (⊤ : Subgroup W) H) (Subgroup.zpowers t) ⊔
        (commSub (⊤ : Subgroup W) H ⊓ fixV H))
      (commSub (⊤ : Subgroup W) H ⊓ fixV H) = 0) :
    t ∈ Subgroup.centralizer (H : Set (MulAut W)) :=
  mem_centralizer_of_commSub_sup_fixV_mQuot_eq_zero hW
    (CFSG.Quasithin.H13.E54.isSimpleGroup_of_lieModel hH)
    (isQuasisimple_open_of_isLn hH) hirr htN hzero

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
