module

public import CFSG.Quasithin.MS93.S36SpY
public import CFSG.Quasithin.MS93.S6Bridge

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93.MSP
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open CFSG.Quasithin.MS93.S36
open scoped commutatorElement Matrix

section Count

variable {G : Type} [Group G] [Finite G] {F : Type} [Field F] [Finite F] {U : Subgroup G}
  {vec : ↥U →* Multiplicative (V4 F)}

omit [Finite F] in
theorem card_le_fixSp_zpowers (hs : Function.Surjective vec) {t : G} {g : Sp4 F}
    (hg : ActsMat vec t g) :
    Nat.card (V4 F) ≤ Nat.card (fixSp (Subgroup.zpowers g)) *
      (Subgroup.centralizer ({t} : Set G)).relIndex U := by
  set S : Subgroup (Multiplicative (V4 F)) := (fixSp (Subgroup.zpowers g)).toAddSubgroup.toSubgroup
    with hS
  have hK : (Subgroup.centralizer ({t} : Set G)).subgroupOf U ≤ S.comap vec := by
    intro u hu
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_iff] at hu
    have htu : t * u * t⁻¹ = u := by rw [hu t rfl, mul_inv_cancel_right]
    have h1 := hg u u htu.symm
    show Multiplicative.toAdd (vec u) ∈ fixSp (Subgroup.zpowers g)
    have hle : Subgroup.zpowers g ≤ fixer (F ∙ Multiplicative.toAdd (vec u)) := by
      rw [Subgroup.zpowers_le, mem_fixer]
      intro w hw
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
      rw [Matrix.mulVec_smul, ← h1]
    exact le_fixer_iff.1 hle (Submodule.mem_span_singleton_self _)
  have hidx : S.index ≤ (Subgroup.centralizer ({t} : Set G)).relIndex U := by
    rw [← Subgroup.index_comap_of_surjective S hs]
    exact Subgroup.index_antitone hK
  have hcard : Nat.card (V4 F) = Nat.card S * S.index := by
    rw [Subgroup.card_mul_index]
    rfl
  rw [hcard]
  exact Nat.mul_le_mul_left _ hidx

omit [Finite F] in
theorem eq_zero_or_eq_one_of_two [Fintype F] (hF : Fintype.card F = 2) (c : F) :
    c = 0 ∨ c = 1 :=
  PairHyp.eq_zero_or_eq_one_of_card_two hF c

theorem exists_transv_of_card_two [Fintype F] [CharP F 2] (hF : Fintype.card F = 2) {g : Sp4 F}
    (hcard : Nat.card (V4 F) ≤ Nat.card (fixSp (Subgroup.zpowers g)) * 2) (hg1 : g ≠ 1) :
    ∃ v : V4 F, v ≠ 0 ∧ g = transv v 1 := by
  set r := Module.finrank F (fixSp (Subgroup.zpowers g)) with hr
  have hF' : Nat.card F = 2 := by rw [Nat.card_eq_fintype_card, hF]
  rw [card_V4, card_fixSp, hF'] at hcard
  have hr3 : 3 ≤ r := by
    have h1 : 2 ^ 4 ≤ 2 ^ (r + 1) := by rw [pow_succ]; exact hcard
    have := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).1 h1
    omega
  have hr4 : r ≤ 4 := by
    have := Submodule.finrank_le (fixSp (Subgroup.zpowers g))
    rwa [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin] at this
  have hr' : r = 3 := by
    rcases (show r = 3 ∨ r = 4 by omega) with h3 | h4
    · exact h3
    · exfalso
      apply hg1
      have htop : fixSp (Subgroup.zpowers g) = ⊤ := by
        apply Submodule.eq_top_of_finrank_eq
        rw [← hr, h4, Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      have := fixSp_eq_top_iff.1 htop
      rw [Subgroup.zpowers_eq_bot] at this
      exact this
  obtain ⟨p, hp, -, hle⟩ := exists_point_of_finrank_fixSp_three hr'
  obtain ⟨v, hv, rfl⟩ := exists_eq_span_of_isPoint hp
  obtain ⟨c, hc⟩ := (mem_xPoint_span hv).1 (hle (Subgroup.mem_zpowers g))
  refine ⟨v, hv, ?_⟩
  rcases eq_zero_or_eq_one_of_two hF c with rfl | rfl
  · rw [transv_zero] at hc
    exact absurd hc.symm hg1
  · exact hc.symm

end Count

@[expose] noncomputable def sgnSp : ↥(StatedSp 2 (ZMod 2)) →* ℤˣ :=
  Equiv.Perm.sign.comp Sp4Inf.iotaSp.toMonoidHom

theorem sgnSp_transv {v : V4 (ZMod 2)} (hv : v ≠ 0) : sgnSp (transv v 1) = -1 := by
  have hq : Nat.card (ZMod 2) = 2 := by simp
  have ht : transv v 1 ∈ xPoint ((ZMod 2) ∙ v) := transv_mem_xPoint v 1
  have ht1 : transv v 1 ≠ 1 := by
    intro h1
    obtain ⟨w, hw⟩ := exists_form_eq_one hv
    have := congrArg (fun g : Sp4 (ZMod 2) => mat g *ᵥ w) h1
    simp only [transv_mulVec, hw, mul_one, one_smul, mat_one, Matrix.one_mulVec,
      add_eq_left] at this
    exact hv this
  obtain ⟨g, hg⟩ := exists_five_conj_transv_of_card_two hq (isPoint_span hv) ht ht1
  rcases Int.units_eq_one_or (sgnSp (transv v 1)) with h1 | h1
  · exfalso
    have hker : (⊤ : Subgroup (Sp4 (ZMod 2))) ≤ sgnSp.ker := by
      rw [← hg, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_inv, h1, mul_one,
        mul_inv_cancel]
    obtain ⟨x, hx⟩ := Sp4Inf.iotaSp.surjective (Equiv.swap (0 : Fin 6) 1)
    have := hker (Subgroup.mem_top x)
    rw [MonoidHom.mem_ker, sgnSp, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, hx,
      Equiv.Perm.sign_swap (by decide)] at this
    exact absurd this (by decide)
  · exact h1

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem exists_spFrame_of_alt (h : PUHyp M T L) {N : Subgroup ↥L}
    (hA : IsAltNaturalSection L (Uq M T L) (Uq M T L ⊓ Zq M L) N 6) {s : G} (hsT : s ∈ T)
    (hsQ : s ∉ pCoreOf 2 M)
    (hs : (Subgroup.centralizer ({s} : Set G)).relIndex (Uq M T L) ≤ 2) :
    ∃ d : SpFrame h, d.k = 1 := by
  have hMU := le_normalizer_Uq (T := T) h.le_normalizer
  obtain ⟨α, hnat, hsurj | hL⟩ := sp4Two_of_altNaturalSection h.L_le h.le_normalizer hMU
    (le_normalizer_inf hMU (le_normalizer_Zq h.le_normalizer)) inf_le_left hA
  · exact exists_spFrame_of_two h hsurj hnat
  exfalso
  obtain ⟨c⟩ := MSP.nonempty_natCoord hnat
  have hker : ∀ u : ↥(Uq M T L), c.toVec u = 1 ↔ (u : G) ∈ Zq M L := by
    intro u
    rw [← MonoidHom.mem_ker, c.ker_eq, Subgroup.mem_subgroupOf]
    exact ⟨fun h => h.2, fun h => ⟨u.2, h⟩⟩
  have hMact : ∀ m : ↥M, ActsMat c.toVec (m : G) (α m) := fun m u v huv => c.equiv m u v huv
  set s' : ↥M := ⟨s, h.le hsT⟩
  have hs1 : α s' ≠ 1 := by
    intro h1
    have h2 := hMact s'
    rw [h1] at h2
    exact hsQ (mem_pCoreOf_of_mem_trivW h hsT (mem_trivW_of_actsMat_one h hker (h.le hsT) h2))
  have hcard := card_le_fixSp_zpowers c.surj (hMact s')
  obtain ⟨v, hv, hvs⟩ := exists_transv_of_card_two (F := ZMod 2) (by simp) (hcard.trans
    (Nat.mul_le_mul_left _ hs)) hs1
  have hLeven : ∀ l : ↥L, sgnSp (α ⟨l, h.L_le l.2⟩) = 1 := by
    let f : ↥L →* ℤˣ := (sgnSp.comp α).comp (Subgroup.inclusion h.L_le)
    have hle : L ≤ f.ker.map L.subtype := by
      refine (le_of_eq h.perfect.symm).trans ?_
      rw [Subgroup.commutator_le]
      intro x hx y hy
      refine ⟨⟨⁅x, y⁆, ?_⟩, ?_, rfl⟩
      · have := Subgroup.commutator_mem_commutator hx hy
        rwa [h.perfect] at this
      · have e : (⟨⁅x, y⁆, _⟩ : ↥L) = ⁅(⟨x, hx⟩ : ↥L), ⟨y, hy⟩⁆ := rfl
        rw [SetLike.mem_coe, MonoidHom.mem_ker, e, map_commutatorElement,
          commutatorElement_eq_one_iff_mul_comm]
        exact mul_comm _ _
    intro l
    obtain ⟨l', hl', he⟩ := hle l.2
    have : l' = l := Subtype.ext he
    subst this
    exact hl'
  obtain ⟨l, hl⟩ := hL s'
  have h1 := hLeven l
  rw [← hl, hvs, sgnSp_transv hv] at h1
  exact absurd h1 (by decide)

theorem SpFrame.actsMat_of_k_one {h : PUHyp M T L} (d : SpFrame h) (hk : d.k = 1) {t : G}
    (ht : t ∈ M) (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1) : ∃ g, ActsMat d.vec t g := by
  have hF2 : Fintype.card d.F = 2 := by rw [d.card, hk, pow_one]
  obtain ⟨f, hfb, hfn, hf⟩ := d.exists_add ht
  refine d.exists_actsMat ht ht2 hfb hfn hf fun c w => ?_
  rcases eq_zero_or_eq_one_of_two hF2 c with rfl | rfl
  · rw [zero_smul, zero_smul, map_zero]
  · rw [one_smul, one_smul]

omit [Finite G] in
theorem relIndex_centralizer_tImage (χ : MulAut ↥T) {m : G} (hm : m ∈ T) {K : Subgroup G}
    (hK : K ≤ T) :
    (Subgroup.centralizer ({((χ ⟨m, hm⟩ : ↥T) : G)} : Set G)).relIndex (tImage χ K) =
      (Subgroup.centralizer ({m} : Set G)).relIndex K := by
  have e : Subgroup.centralizer ({((χ ⟨m, hm⟩ : ↥T) : G)} : Set G) ⊓ tImage χ K =
      tImage χ (K ⊓ Subgroup.centralizer ({m} : Set G)) := by
    ext x
    rw [Subgroup.mem_inf, tImage_inf, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hx, hxK⟩
      refine ⟨hxK, ?_⟩
      obtain ⟨t, -, rfl⟩ := mem_tImage.1 hxK
      refine apply_mem_tImage χ (Subgroup.mem_centralizer_singleton_iff.2 ?_)
      have h1 : χ (t * ⟨m, hm⟩) = χ (⟨m, hm⟩ * t) := by
        rw [map_mul, map_mul]
        exact Subtype.ext hx
      exact congrArg Subtype.val (χ.injective h1)
    · rintro ⟨hxK, hxC⟩
      refine ⟨?_, hxK⟩
      obtain ⟨t, ht, rfl⟩ := mem_tImage.1 hxC
      have h1 : (t : G) * m = m * t := Subgroup.mem_centralizer_singleton_iff.1 ht
      have h2 : t * ⟨m, hm⟩ = ⟨m, hm⟩ * t := Subtype.ext h1
      have h3 := congrArg (fun y => ((χ y : ↥T) : G)) h2
      simpa only [map_mul, Subgroup.coe_mul] using h3
  rw [← Subgroup.inf_relIndex_right, e, relIndex_tImage χ hK, inf_comm,
    Subgroup.inf_relIndex_right]

theorem false_of_case_one {h : PUHyp M T L} (d : SpFrame h) (hk : d.k = 1) (ψ : MulAut ↥T)
    (hV : Vq M L ≠ Uq M T L) (hXL : ⁅Xq M, L⁆ ≤ Uq M T L)
    (hcrit' : ¬ Z0q M T ≤ tImage ψ⁻¹ (pCoreOf 2 M)) {m₁ m₂ : G} (hm₁ : m₁ ∈ T) (hm₂ : m₂ ∈ T)
    (hc₁ : (Subgroup.centralizer ({m₁} : Set G)).relIndex (tImage ψ (Z0q M T)) = 2)
    (hc₂ : (Subgroup.centralizer ({m₂} : Set G)).relIndex (tImage ψ (Z0q M T)) = 2)
    (h12 : m₁ * m₂⁻¹ ∉ tImage ψ (pCoreOf 2 M))
    (hsup : Z0q M T ⊔ tImage ψ (pCoreOf 2 M) =
      Subgroup.closure ({m₁, m₂} : Set G) ⊔ tImage ψ (pCoreOf 2 M)) : False := by
  set χ := ψ⁻¹ with hχ
  have hZT := Z0q_le_T h
  have hQT := h.pCore_le
  have hF2 : Fintype.card d.F = 2 := by rw [d.card, hk, pow_one]
  have key : ∀ (m : G) (hm : m ∈ T),
      (Subgroup.centralizer ({m} : Set G)).relIndex (tImage ψ (Z0q M T)) = 2 →
      m ∈ Subgroup.closure ({m₁, m₂} : Set G) →
      ∃ v : V4 d.F, v ≠ 0 ∧ ActsMat d.vec ((χ ⟨m, hm⟩ : ↥T) : G) (transv v 1) ∧
        ∃ z ∈ tImage χ (Z0q M T), ActsMat d.vec z (transv v 1) := by
    intro m hm hcm hmcl
    set s : G := ((χ ⟨m, hm⟩ : ↥T) : G) with hs
    have hsT : s ∈ T := (χ ⟨m, hm⟩).2
    have hsM : s ∈ M := h.le hsT
    have hcs : (Subgroup.centralizer ({s} : Set G)).relIndex (Z0q M T) = 2 := by
      have := relIndex_centralizer_tImage χ hm (tImage_le ψ (Z0q M T))
      rwa [hχ, tImage_inv_tImage ψ hZT, hcm] at this
    have hsU : (Subgroup.centralizer ({s} : Set G)).relIndex (Uq M T L) ≤ 2 ^ d.k := by
      rw [hk, pow_one, ← hcs]
      exact Subgroup.relIndex_le_of_le_right (Uq_le_Z0q h.L_le) Subgroup.index_ne_zero_of_finite
    obtain ⟨g, hg⟩ := d.exists_actsMat_of_relIndex hsM (pow_eq_one_of_mem_T h hsT) hsU
    have hg1 : g ≠ 1 := by
      intro h1
      rw [h1] at hg
      have hsQ := mem_pCoreOf_of_mem_trivW h hsT (mem_trivW_of_actsMat_one h d.ker hsM hg)
      have : Z0q M T ≤ Subgroup.centralizer ({s} : Set G) := fun z hz =>
        Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_iff.1 (h.pCoreOf_le_centralizer_Z0q hsQ) z hz)
      rw [Subgroup.relIndex_eq_one.2 this] at hcs
      exact absurd hcs (by norm_num)
    have hcard := (card_le_fixSp_zpowers d.surj hg).trans
      (Nat.mul_le_mul_left _ (hsU.trans (by rw [hk, pow_one])))
    obtain ⟨v, hv, rfl⟩ := exists_transv_of_card_two hF2 hcard hg1
    refine ⟨v, hv, hg, ?_⟩
    have hsup' : tImage χ (Z0q M T) ⊔ pCoreOf 2 M =
        tImage χ (Subgroup.closure ({m₁, m₂} : Set G)) ⊔ pCoreOf 2 M := by
      have := congrArg (tImage χ) hsup
      have hcl : Subgroup.closure ({m₁, m₂} : Set G) ≤ T := by
        rw [Subgroup.closure_le]
        rintro x (rfl | rfl)
        · exact hm₁
        · exact hm₂
      rwa [tImage_sup χ hZT (tImage_le _ _), tImage_sup χ hcl (tImage_le _ _), hχ,
        tImage_inv_tImage ψ hQT] at this
    have hsZQ : s ∈ tImage χ (Z0q M T) ⊔ pCoreOf 2 M := by
      rw [hsup']
      exact Subgroup.mem_sup_left (apply_mem_tImage χ (t := ⟨m, hm⟩) hmcl)
    have hZQn : tImage χ (Z0q M T) ≤ Subgroup.normalizer (pCoreOf 2 M : Set G) :=
      (tImage_le _ _).trans (h.le.trans (le_normalizer_pCoreOf M))
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hZQn,
      Set.mem_mul] at hsZQ
    obtain ⟨z, hz, q, hq, hzq⟩ := hsZQ
    refine ⟨z, hz, fun u w huw => ?_⟩
    have hqc : q ∈ Subgroup.centralizer (Uq M T L : Set G) :=
      h.pCoreOf_le_centralizer_Z0q.trans (Subgroup.centralizer_le (Uq_le_Z0q h.L_le)) hq
    have h1 := hg u w (by
      rw [huw, ← hzq]
      have := Subgroup.mem_centralizer_iff.1 hqc u u.2
      calc z * u * z⁻¹ = z * (q * u * q⁻¹) * z⁻¹ := by
            rw [← this, mul_inv_cancel_right]
        _ = z * q * u * (z * q)⁻¹ := by group)
    exact h1
  obtain ⟨v₁, hv₁, hs₁, z₁, hz₁, hz₁a⟩ := key m₁ hm₁ hc₁ (Subgroup.subset_closure (by simp))
  obtain ⟨v₂, hv₂, hs₂, z₂, hz₂, hz₂a⟩ := key m₂ hm₂ hc₂ (Subgroup.subset_closure (by simp))
  have hv12 : v₁ ≠ v₂ := by
    rintro rfl
    apply h12
    set s₁ := ((χ ⟨m₁, hm₁⟩ : ↥T) : G)
    set s₂ := ((χ ⟨m₂, hm₂⟩ : ↥T) : G)
    have hs₂M : s₂ ∈ M := h.le (χ ⟨m₂, hm₂⟩).2
    have h1 : ActsMat d.vec (s₁ * s₂⁻¹) (transv v₁ 1 * (transv v₁ 1)⁻¹) :=
      actsMat_mul (inv_mem (d.normU hs₂M)) hs₁ (actsMat_inv hs₂)
    rw [mul_inv_cancel] at h1
    have hT12 : s₁ * s₂⁻¹ ∈ T := T.mul_mem (χ ⟨m₁, hm₁⟩).2 (T.inv_mem (χ ⟨m₂, hm₂⟩).2)
    have hQ12 := mem_pCoreOf_of_mem_trivW h hT12
      (mem_trivW_of_actsMat_one h d.ker (h.le hT12) h1)
    have e : s₁ * s₂⁻¹ = ((χ (⟨m₁, hm₁⟩ * ⟨m₂, hm₂⟩⁻¹) : ↥T) : G) := by
      rw [map_mul, map_inv]
      rfl
    rw [e] at hQ12
    have hmem := apply_mem_tImage ψ (t := χ (⟨m₁, hm₁⟩ * ⟨m₂, hm₂⟩⁻¹)) hQ12
    rw [hχ, MulAut.apply_inv_self] at hmem
    simpa using hmem
  have hPM : tImage χ (pCoreOf 2 M) ≤ M := tImage_le_M h χ _
  have hP : ∀ x ∈ tImage χ (pCoreOf 2 M), ∃ g, ActsMat d.vec x g := fun x hx =>
    d.actsMat_of_k_one hk (hPM hx) (pow_eq_one_of_mem_T h (tImage_le _ _ hx))
  have hfix : ∀ (z : G) (v : V4 d.F), z ∈ tImage χ (Z0q M T) → ActsMat d.vec z (transv v 1) →
      v ≠ 0 → v ∈ fixSp (d.img _ hPM hP) := by
    intro z v hz hzv hv
    rw [mem_fixSp]
    intro g hg
    obtain ⟨x, hxP, hxg⟩ := (d.mem_img hPM hP).1 hg
    have hzM := tImage_le_M h χ _ hz
    have hxM := hPM hxP
    have hxz : x * z = z * x :=
      (Subgroup.mem_centralizer_iff.1 (tImage_pCoreOf_le_centralizer h χ hxP) z hz).symm
    have h1 : ActsMat d.vec (x * z) (g * transv v 1) := actsMat_mul (d.normU hzM) hxg hzv
    have h2 : ActsMat d.vec (z * x) (transv v 1 * g) := actsMat_mul (d.normU hxM) hzv hxg
    rw [hxz] at h1
    exact mulVec_eq_of_commute_transv hv
      (actsMat_unique d.surj (d.normU (M.mul_mem hzM hxM)) h1 h2)
  have hv2 : v₂ ∉ d.F ∙ v₁ := by
    intro hmem
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.1 hmem
    rcases eq_zero_or_eq_one_of_two hF2 c with rfl | rfl
    · rw [zero_smul] at hc
      exact hv₂ hc.symm
    · rw [one_smul] at hc
      exact hv12 hc
  have hspan : Submodule.span d.F {v₁, v₂} ≤ fixSp (d.img _ hPM hP) := by
    rw [Submodule.span_le]
    rintro w (rfl | rfl)
    · exact hfix z₁ w hz₁ hz₁a hv₁
    · exact hfix z₂ w hz₂ hz₂a hv₂
  have h2 : 2 ≤ Module.finrank d.F (fixSp (d.img _ hPM hP)) :=
    (finrank_span_pair hv₁ hv2).symm.le.trans (Submodule.finrank_mono hspan)
  have hquad : ¬ commSp (d.img _ hPM hP) ≤ fixSp (d.img _ hPM hP) :=
    not_quadratic_of hV hXL hcrit'
  by_cases hb : d.img _ hPM hP = ⊥
  · apply hquad
    rw [hb, commSp_le_iff]
    intro a ha w
    rw [Subgroup.mem_bot.1 ha, mat_one, Matrix.one_mulVec, sub_self]
    exact Submodule.zero_mem _
  obtain ⟨l, hl, hlfix, hHl⟩ :=
    exists_line_of_two_le_finrank_fixSp (d.isPGroup_img hPM hP (tImage_le χ _)) hb h2
  exact hquad ((commSp_mono hHl).trans ((commSp_qLine_le hl).trans hlfix))

end CFSG.Quasithin.MS93.S36SP
