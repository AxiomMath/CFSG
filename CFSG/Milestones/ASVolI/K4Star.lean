module

public import CFSG.Milestones.ASVolI.K4
public import CFSG.Quasithin.H13.A5M12Row
public import CFSG.Quasithin.H13.A5M22HatRow
public import CFSG.Quasithin.H13.KGFactJ2Row

public section

namespace CFSG.ASVolI

open CFSG.Open

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem burnsideK4s_star_of_mParam {V : Type} [CommGroup V] [Finite V] {G : Subgroup (MulAut V)}
    (h3 : 3 ≤ E3.mParam G) :
    ∀ T, IsSylowTwoOf T G → ∀ A, IsA2 T A → rAV A ≤ 2 →
      (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) ∧ 1 < rk ↥A := by
  intro T hT A hA hr
  have hAG : IsA2 G A := ⟨hA.1.trans hT.1, hA.2.1, hA.2.2⟩
  have hm : E3.mParam G ≤ rkIdx (fixV A) := E3.e3_2 hAG.1 hAG.isElemAbelian2 hAG.ne_bot
  have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hAG.rk_pos
  have hmul := hAG.rAV_mul
  have h1 : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) :=
    calc (rkIdx (fixV A) : ℚ) = rAV A * (rk ↥A : ℚ) := hmul.symm
      _ ≤ 2 * (rk ↥A : ℚ) := mul_le_mul_of_nonneg_right hr hpos.le
  refine ⟨h1, ?_⟩
  have h2 : ((E3.mParam G : ℕ) : ℚ) ≤ 2 * (rk ↥A : ℚ) := by
    exact le_trans (by exact_mod_cast hm) h1
  have h3' : (3 : ℚ) ≤ 2 * (rk ↥A : ℚ) := le_trans (by exact_mod_cast h3) h2
  have : (1 : ℚ) < (rk ↥A : ℚ) := by linarith
  exact_mod_cast this


open CFSG.Quasithin CFSG.Quasithin.J2Model CFSG.Quasithin.J2Row CFSG.Quasithin.H
  CFSG.CharacterTheory.SteinbergBY CFSG.Blueprint CFSG.QuasithinUnique.Setup.X1 in
theorem burnsideK4s_j2_model
    {V : Type} [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (hHyp : B4Hyp G L) (θ : ↥L ≃* NativeSporadic.Carrier .J2)
    (hcard : Nat.card V < 2 ^ 24) :
    ∃ e : V ≃* W6, L.map (congrHom e) = L6 ∧ Nat.card ↥Γ₆ = 604800 ∧
      Nat.card (MulAut ↥L6) ≤ 2 * Nat.card ↥L6 ∧ Subgroup.center ↥L6 = ⊥ ∧
      G.map (congrHom e) ≤ natNorm Γ₆ := by
  obtain ⟨π, hπ⟩ := J2Mod.j2SmallModules_holds V hV L ⟨θ⟩ hHyp.2.2.2 hcard
  obtain ⟨e, he⟩ := exists_equiv_of_zornQ hπ
  have hL6 : L.map (MulAut.congr e).toMonoidHom = L6 := map_congr_eq_L6 hπ.1 e he
  have hGN := B42L2.le_normalizer_of_b4Hyp hHyp
  let φ : ↥L ≃* ↥L6 := ((MulAut.congr e).subgroupMap L).trans (MulEquiv.subgroupCongr hL6)
  have hJ2 : Nat.card (NativeSporadic.Carrier .J2) = 604800 := CFSG.Sporadic.J2.card_J2
  have hcardL6 : Nat.card ↥L6 = 604800 := by
    rw [← Nat.card_congr φ.toEquiv, Nat.card_congr θ.toEquiv, hJ2]
  have hcardΓ : Nat.card ↥Γ₆ = 604800 := by
    have hinj : Function.Injective (natAut Γ₆) := matHom_injective.comp Subtype.val_injective
    rw [← hcardL6]
    exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  have hAut : Nat.card (MulAut ↥L6) ≤ 2 * Nat.card ↥L6 := by
    obtain ⟨Φ, -⟩ := CFSG.QuasithinUnique.Bridge.J2Excl.j2_aut_model
    have h1 : Nat.card (MulAut ↥L6) = Nat.card (MulAut (NativeSporadic.Carrier .J2)) :=
      Nat.card_congr (MulAut.congr (φ.symm.trans θ)).toEquiv
    have h2 : Nat.card (MulAut (NativeSporadic.Carrier .J2)) = 1209600 := by
      rw [← Nat.card_congr Φ.toEquiv, CFSG.QuasithinUnique.Bridge.J2Excl.card_j2R]
    rw [h1, h2, hcardL6]
  have hZ : Subgroup.center ↥L = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hx' : θ x ∈ Subgroup.center (NativeSporadic.Carrier .J2) := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨z, rfl⟩ := θ.surjective y
      rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.1 hx z)]
    rw [H13.A5.KGJ2.center_carrier_j2, Subgroup.mem_bot] at hx'
    rw [Subgroup.mem_bot]
    exact θ.injective (hx'.trans (map_one θ).symm)
  have hZ6 : Subgroup.center ↥L6 = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    have hz' : φ.symm z ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff] at hz ⊢
      intro y
      apply φ.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz (φ y)]
    rw [hZ, Subgroup.mem_bot] at hz'
    rw [Subgroup.mem_bot, ← MulEquiv.apply_symm_apply φ z, hz', map_one]
  refine ⟨e, hL6, hcardΓ, hAut, hZ6, ?_⟩
  have h := Subgroup.map_mono (f := (MulAut.congr e).toMonoidHom) hGN
  rw [Subgroup.map_equiv_normalizer_eq L (MulAut.congr e), hL6] at h
  exact h

open CFSG.Quasithin CFSG.Quasithin.J2Row CFSG.Quasithin.H CFSG.CharacterTheory.SteinbergBY
  CFSG.CharacterTheory.SteinbergBY.FieldFour in
theorem burnsideK4s_j2_fix_le (hcard : Nat.card ↥Γ₆ = 604800)
    (hAut : Nat.card (MulAut ↥L6) ≤ 2 * Nat.card ↥L6) (hZ : Subgroup.center ↥L6 = ⊥)
    {t : MulAut W6} (htN : t ∈ natNorm Γ₆) (ht2 : t * t = 1) (ht1 : t ≠ 1) :
    Nat.card ↥(fixV (Subgroup.zpowers t)) ≤ 256 := by
  have hord : orderOf t = 2 := orderOf_eq_prime (by rw [sq]; exact ht2) ht1
  set A := Subgroup.zpowers t with hA
  have hcardA : Nat.card A = 2 := by rw [hA, Nat.card_zpowers, hord]
  have hAel : IsElemAbelian2 A := by
    refine ⟨fun a ha b hb => ?_, fun a ha => ?_⟩
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hb
      rw [← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, sq, ht2, one_zpow]
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => by rw [← sq]; exact hAel.2 x hx
  by_cases htL : t ∈ L6
  · have hAL : A ≤ L6 := (Subgroup.zpowers_le).2 htL
    set B₀ := A.comap matHom with hB₀
    have hB₀Γ : B₀ ≤ Γ₆ := comap_matHom_le hAL
    have hB₀c : Nat.card B₀ = Nat.card A := card_comap_matHom hAL
    have hB₀comm : ∀ x ∈ B₀, ∀ y ∈ B₀, x * y = y * x := fun x hx y hy =>
      matHom_injective (by rw [map_mul, map_mul]; exact hAel.1 _ hx _ hy)
    have hB₀sq : ∀ x ∈ B₀, x * x = 1 := fun x hx =>
      matHom_injective (by rw [map_mul, map_one]; exact hsq _ hx)
    obtain ⟨b2, -, -⟩ := inner_bounds hcard hB₀Γ hB₀comm hB₀sq
    exact (card_fixV_le_mFix A).trans (b2 (by rw [hB₀c, hcardA]))
  · obtain ⟨σ, hσ⟩ := exists_semilinear hasScalarCommutant_Γ₆ htN
    have hσω : σ FieldFour.ω ≠ FieldFour.ω := by
      intro h
      have e := eq_refl_of_apply_ω h
      subst e
      exact htL (mem_natImage_of_linear hAut hZ htN hσ ht2)
    have hC : Nat.card ↥(fixV A) ≤
        Nat.card {v : V6 // v ∈ (⊤ : Submodule FieldFour V6) ∧ toAddMap t v = v} := by
      refine Nat.card_le_card_of_injective (fun v => ⟨Multiplicative.toAdd (v : W6),
        Submodule.mem_top, congrArg Multiplicative.toAdd (v.2 t (Subgroup.mem_zpowers t))⟩)
        fun v w h => ?_
      apply Subtype.ext
      have h1 := congrArg Subtype.val h
      exact Multiplicative.toAdd.injective h1
    have hhalf := card_sq_le_of_semilinear (U := ⊤) hσ hσω
    rw [card_top] at hhalf
    exact hC.trans (le_of_sq_le hhalf (by norm_num : 4096 ≤ 64 ^ 2) |>.trans (by norm_num))

open CFSG.Quasithin.J2Row CFSG.Quasithin.J2Bits CFSG.CharacterTheory.SteinbergBY
  CFSG.CharacterTheory.SteinbergBY.FieldFour in
theorem burnsideK4s_j2_card_fixM : 256 ≤ Nat.card ↥(fixM (sEl 4).toMat) := by
  let w : Fin 4 → BV := ![⟨3, 0⟩, ⟨13, 0⟩, ⟨20, 0⟩, ⟨32, 0⟩]
  let vs : Fin 4 → V6 := fun i => (w i).toVec
  have hfix : ∀ i, vs i ∈ fixM (sEl 4).toMat := fun i => by
    have h : ∀ i : Fin 4, ((sEl 4).mv (w i)).eqv (w i) = true := by decide +kernel
    rw [mem_fixM, ← BM.toVec_mv]
    exact (BV.eqv_iff _ _).mp (h i)
  have hli : LinearIndependent FieldFour vs := by
    have key : ∀ g : Fin 4 → FieldFour,
        g 0 • vs 0 + g 1 • vs 1 + g 2 • vs 2 + g 3 • vs 3 = 0 → g = 0 := by
      decide +kernel
    rw [Fintype.linearIndependent_iff]
    intro g hg i
    rw [Fin.sum_univ_four] at hg
    exact congrFun (key g hg) i
  have hle : Submodule.span FieldFour (Set.range vs) ≤ fixM (sEl 4).toMat :=
    Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hfix i)
  have h1 := Nat.card_le_card_of_injective (Submodule.inclusion hle)
    (Submodule.inclusion_injective hle)
  have h2 : Nat.card ↥(Submodule.span FieldFour (Set.range vs)) = 256 := by
    rw [Module.natCard_eq_pow_finrank (K := FieldFour), finrank_span_eq_card hli,
      FieldFour.natCard_eq]
    norm_num
  omega

open CFSG.Quasithin CFSG.Quasithin.J2Row CFSG.Quasithin.J2Bits CFSG.Quasithin.H
  CFSG.CharacterTheory.SteinbergBY CFSG.CharacterTheory.SteinbergBY.FieldFour in
theorem burnsideK4s_j2_exists_inv :
    ∃ t ∈ L6, t * t = 1 ∧ t ≠ 1 ∧ 256 ≤ Nat.card ↥(fixV (Subgroup.zpowers t)) := by
  obtain ⟨x, hx, hxe⟩ := exists_mem_of_sEl 4
  have hxΓ : x ∈ Γ₆ := S₂_le hx
  have hsq : ((sEl 4).mul (sEl 4)).eqv BM.one = true := by decide +kernel
  have hne : (sEl 4).eqv BM.one = false := by decide +kernel
  have hxx : x * x = 1 := by
    apply Units.ext
    rw [Units.val_mul, hxe, ← BM.toMat_mul, toMat_eq_of_eqv hsq, BM.toMat_one, Units.val_one]
  refine ⟨matHom x, ⟨⟨x, hxΓ⟩, rfl⟩, by rw [← map_mul, hxx, map_one], ?_, ?_⟩
  · intro h
    have h1 : x = 1 := matHom_injective (h.trans (map_one _).symm)
    rw [h1, Units.val_one] at hxe
    have h2 := (BM.eqv_iff _ _).mpr (hxe.symm.trans BM.toMat_one.symm)
    rw [hne] at h2
    exact absurd h2 (by decide)
  · have h := burnsideK4s_j2_card_fixM
    rw [← hxe] at h
    have hmem : ∀ v : ↥(fixM (x : M6)),
        Multiplicative.ofAdd v.1 ∈ fixV (Subgroup.zpowers (matHom x)) := fun v => by
      rw [H.Mathieu.mem_fixV_zpowers_iff]
      apply Multiplicative.toAdd.injective
      rw [toAdd_matHom, toAdd_ofAdd]
      exact mem_fixM.1 v.2
    let f : ↥(fixM (x : M6)) → ↥(fixV (Subgroup.zpowers (matHom x))) := fun v =>
      ⟨Multiplicative.ofAdd v.1, hmem v⟩
    have hf : Function.Injective f := by
      intro v w hvw
      apply Subtype.ext
      have h1 := congrArg (fun y : ↥(fixV (Subgroup.zpowers (matHom x))) =>
        Multiplicative.toAdd y.1) hvw
      simpa [f] using h1
    exact h.trans (Nat.card_le_card_of_injective f hf)

open CFSG.Quasithin in
theorem burnsideK4s_card_mul_two_pow {W : Type*} [Group W] [Finite W] {n : ℕ}
    (hW : Nat.card W = 2 ^ n) (U : Subgroup W) : Nat.card U * 2 ^ rkIdx U = 2 ^ n := by
  have hdvd : U.index ∣ 2 ^ n := hW ▸ Subgroup.index_dvd_card U
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  have h := Subgroup.card_mul_index U
  rw [hW, hm] at h
  rw [rkIdx, hm, padicValNat.prime_pow]
  exact h

open CFSG.Quasithin in
theorem burnsideK4s_four_le_rkIdx {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 2 ^ 12)
    (U : Subgroup W) (hU : Nat.card U ≤ 256) : 4 ≤ rkIdx U := by
  have h := burnsideK4s_card_mul_two_pow hW U
  by_contra hlt
  push Not at hlt
  have h8 : 2 ^ rkIdx U ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hpos : 0 < 2 ^ rkIdx U := by positivity
  have : Nat.card U * 2 ^ rkIdx U ≤ 256 * 8 := Nat.mul_le_mul hU (by simpa using h8)
  omega

open CFSG.Quasithin in
theorem burnsideK4s_rkIdx_le_four {W : Type*} [Group W] [Finite W] (hW : Nat.card W = 2 ^ 12)
    (U : Subgroup W) (hU : 256 ≤ Nat.card U) : rkIdx U ≤ 4 := by
  have h := burnsideK4s_card_mul_two_pow hW U
  by_contra hlt
  push Not at hlt
  have h8 : 2 ^ 5 ≤ 2 ^ rkIdx U := Nat.pow_le_pow_right (by norm_num) (by omega)
  have : 256 * 2 ^ 5 ≤ Nat.card U * 2 ^ rkIdx U := Nat.mul_le_mul hU h8
  omega

open CFSG.Quasithin CFSG.Quasithin.H in
theorem burnsideK4s_rkIdx_congr {V W : Type*} [CommGroup V] [CommGroup W] (e : V ≃* W)
    (s : MulAut V) :
    rkIdx (fixV (Subgroup.zpowers (congrHom e s))) = rkIdx (fixV (Subgroup.zpowers s)) :=
  calc rkIdx (fixV (Subgroup.zpowers (congrHom e s)))
      = rkIdx (fixV ((Subgroup.zpowers s).map (congrHom e))) := by rw [MonoidHom.map_zpowers]
    _ = rkIdx (fixV (Subgroup.zpowers s)) := rkIdx_fixV_map_congrHom e _

open CFSG.Quasithin CFSG.Quasithin.J2Row CFSG.Quasithin.H CFSG.QuasithinUnique.Setup.X1
  CFSG.Blueprint CFSG.Quasithin.J2Model CFSG.CharacterTheory.SteinbergBY in
theorem burnsideK4s_j2_mParam
    {V : Type} [CommGroup V] [Finite V] {G L : Subgroup (MulAut V)}
    (hK : CFSG.ASVolI.ChIJK.KSetup V G L) (hJ : IsSporadic .J2 ↥L) (hT : J2Twelve L ⊤ ⊥) :
    E3.mParam G = 4 := by
  obtain ⟨-, hcard12⟩ := H13.A5.KGJ2.j2Twelve_facts hT
  obtain ⟨θ⟩ := hJ
  obtain ⟨e, hL6, hcardΓ, hAut, hZ6, hXN⟩ :=
    burnsideK4s_j2_model hK.elem2 hK.hyp θ (by rw [hcard12]; norm_num)
  obtain ⟨-, -, hLG, hGN⟩ := B45Mat.b4Hyp_facts hK.hyp
  have hW6 : Nat.card W6 = 2 ^ 12 := by rw [card_W6]; norm_num
  obtain ⟨t6, ht6L, ht62, ht61, ht6card⟩ := burnsideK4s_j2_exists_inv
  obtain ⟨t, htL, hte⟩ : t6 ∈ L.map (congrHom e) := hL6 ▸ ht6L
  have ht2 : orderOf t = 2 := by
    have h1 : orderOf (congrHom e t) = 2 := by
      rw [hte]
      exact orderOf_eq_prime (by rw [sq]; exact ht62) ht61
    rw [← h1]
    exact (orderOf_injective _ (congrHom_injective e) t).symm
  have hall : ∀ s ∈ G, orderOf s = 2 → 4 ≤ rkIdx (fixV (Subgroup.zpowers s)) := by
    intro s hsG hs2
    rw [← burnsideK4s_rkIdx_congr e s]
    have hs2' : congrHom e s * congrHom e s = 1 := by
      rw [← map_mul, ← sq, ← hs2, pow_orderOf_eq_one, map_one]
    have hs1' : congrHom e s ≠ 1 := by
      intro h
      have : s = 1 := congrHom_injective e (h.trans (map_one _).symm)
      rw [this, orderOf_one] at hs2
      omega
    exact burnsideK4s_four_le_rkIdx hW6 _
      (burnsideK4s_j2_fix_le hcardΓ hAut hZ6 (hXN ⟨s, hsG, rfl⟩) hs2' hs1')
  have hrkt : rkIdx (fixV (Subgroup.zpowers t)) = 4 := by
    refine le_antisymm ?_ (hall t (hLG htL) ht2)
    rw [← burnsideK4s_rkIdx_congr e t, hte]
    exact burnsideK4s_rkIdx_le_four hW6 _ ht6card
  exact H.Mathieu.mParam_eq_of ⟨hLG, hGN⟩ htL ht2 hrkt hall

section

open CFSG.Quasithin CFSG.QuasithinUnique in
theorem as_K_4_star : K_4_star := by
  intro V _ _ G L hK
  obtain ⟨-, -, hLG, hGN⟩ := B45Mat.b4Hyp_facts hK.hyp
  have hLM : H.Mathieu.IsOver L G := ⟨hLG, hGN⟩
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h3 : 3 ≤ E3.mParam G := by
      rcases h with ⟨-, hc | hc⟩ | ⟨-, hc | hc⟩ | ⟨-, hc | hc⟩ | ⟨-, hm⟩ | hhat
      · have := (H.Mathieu.stmtH14_4 V L G hLM).1 (Or.inr (Or.inl hc))
        omega
      · have := (H.Mathieu.stmtH14_4 V L G hLM).1 (Or.inl hc)
        omega
      · have := (H.Mathieu.stmtH14_4 V L G hLM).1 (Or.inr (Or.inr (Or.inr hc)))
        omega
      · have := (H.Mathieu.stmtH14_4 V L G hLM).1 (Or.inr (Or.inr (Or.inl hc)))
        omega
      · exact (H.Mathieu.stmtH14_4 V L G hLM).2 (Or.inr hc)
      · exact (H.Mathieu.stmtH14_4 V L G hLM).2 (Or.inl hc)
      · have hcard := H13.A5.M12.m12_card hm
        refine H.Mathieu.le_mParam_of (b := 3) ?_
          (fun s hs hs2 => H13.A5.factM12Row1321_holds V G L hLG hGN hm s hs hs2)
        unfold rk
        rw [hcard, padicValNat.prime_pow]
        norm_num
      · obtain ⟨K, _, _, Γ₀, hK4, hHat, -, hReal⟩ := id hhat
        obtain ⟨e, -, -⟩ := H.exists_transport_natural hReal hLG hGN
        have hcard : Nat.card V = 2 ^ 12 := by
          rw [Nat.card_congr e.toEquiv]
          exact H13.A5.M22Hat.card_stdMod_six hK4
        refine H.Mathieu.le_mParam_of (b := 3) ?_
          (fun s hs hs2 => H13.A5.factM22HatRow1321_holds V G L hLG hGN hhat s hs hs2)
        unfold rk
        rw [hcard, padicValNat.prime_pow]
        norm_num
    exact ⟨by exact_mod_cast h3, burnsideK4s_star_of_mParam h3⟩
  · obtain ⟨hJ, hT⟩ := h
    have h4 := burnsideK4s_j2_mParam hK hJ hT
    exact ⟨h4, burnsideK4s_star_of_mParam (by omega)⟩

end

end CFSG.ASVolI
