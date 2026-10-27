module

public import CFSG.Quasithin.EmptyFaithful.S146zWC1
public import CFSG.Quasithin.EmptyFaithful.S153MTwoData
public import CFSG.Quasithin.EmptyFaithful.S1414Group

public section

namespace CFSG.Quasithin.S146zW

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.C2Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

abbrev wY (J J' R : Subgroup G) : Subgroup G := (J ⊔ J') ⊔ R

abbrev wV (J J' R : Subgroup G) : Subgroup G := omegaOneCenterOf (pCoreOf 2 (wY J J' R))

omit [Finite G] in
theorem isElemAbelian_wV (J J' R : Subgroup G) : IsElemAbelian 2 (wV J J' R) :=
  B2F.isElemAbelian_omegaOneCenterOf _

abbrev VMod (J J' R : Subgroup G) : Type := IntMod (wV J J' R) (isElemAbelian_wV J J' R)

@[expose] noncomputable def actY (J J' R : Subgroup G) : ↥(wY J J' R) →* MulAut (VMod J J' R) :=
  convHom (isElemAbelian_wV J J' R) (wY J J' R) Y_le_normalizer_V

omit [Finite G] in
theorem ker_actY (J J' R : Subgroup G) :
    (actY J J' R).ker =
      (wY J J' R ⊓ Subgroup.centralizer (wV J J' R : Set G)).subgroupOf (wY J J' R) :=
  ker_convHom _ _ _

omit [Finite G] in
theorem range_actY (J J' R : Subgroup G) :
    (actY J J' R).range = autI (isElemAbelian_wV J J' R) (wY J J' R) :=
  range_convHom _ _ _

namespace WreathData

variable {H R J J' : Subgroup G} {ρ : G} (d : WreathData H R J J' ρ)

include d

theorem mem_normalizer_of_normalizes_thompsonJ {y : G} (hy : y ∈ (J ⊔ J') ⊔ R)
    (hc : y ∈ Subgroup.normalizer (thompsonJ R : Set G)) : y ∈ Subgroup.normalizer (R : Set G) := by
  have hRp := d.cfg.radical.isPGroup
  have h1 : H ⊓ Subgroup.normalizer (thompsonJ R : Set G) ≤ cgsIn H R :=
    inf_normalizer_le_cgsIn_of_char (C1GN.thompsonJ_le R)
      (S1414.thompsonJ_ne_bot hRp d.cfg.radical.2.1) (S1414.characteristic_thompsonJ R)
  exact (d.cfg.cpu (h1 ⟨d.sup_le_H hy, hc⟩)).2

theorem not_thompsonJ_le_centralizer :
    ¬ thompsonJ R ≤ Subgroup.centralizer (wV J J' R : Set G) := by
  intro h
  have hRY : R ≤ (J ⊔ J') ⊔ R := le_sup_right
  have hJQ : thompsonJ R ≤ pCoreOf 2 ((J ⊔ J') ⊔ R) := fun x hx =>
    d.R_inf_C_le ⟨C1GN.thompsonJ_le R hx, hRY (C1GN.thompsonJ_le R hx), h hx⟩
  have heq : thompsonJ (pCoreOf 2 ((J ⊔ J') ⊔ R)) = thompsonJ R :=
    B6.thompsonJ_eq_of_le hJQ d.pCoreOf_Y_le
  have hYN : (J ⊔ J') ⊔ R ≤ Subgroup.normalizer (thompsonJ R : Set G) := by
    rw [← heq]
    exact (le_normalizer_pCoreOf 2 _).trans (normalizer_le_normalizer_thompsonJ _)
  exact d.not_J_le_normalizer fun x hx =>
    d.mem_normalizer_of_normalizes_thompsonJ ((le_sup_left.trans le_sup_left : J ≤ (J ⊔ J') ⊔ R) hx)
      (hYN ((le_sup_left.trans le_sup_left : J ≤ (J ⊔ J') ⊔ R) hx))

end WreathData

omit [Finite G] in
theorem isQuasisimple_subgroupOf {L Y : Subgroup G} (hLY : L ≤ Y)
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) :
    CFSG.IsQuasisimple (↥(L.subgroupOf Y) ⧸ CFSG.pCore 2 ↥(L.subgroupOf Y)) := by
  let φ : ↥L ≃* ↥(L.subgroupOf Y) := (Subgroup.subgroupOfEquivOfLe hLY).symm
  have e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃*
      (↥(L.subgroupOf Y) ⧸ CFSG.pCore 2 ↥(L.subgroupOf Y)) :=
    QuotientGroup.congr _ _ φ (CFSG.pCore_map_iso 2 φ)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e hq

omit [Finite G] in
theorem map_conj_subgroupOf {J Y : Subgroup G} {ρ : G} (hρ : ρ ∈ Y) :
    (J.subgroupOf Y).map (MulAut.conj (⟨ρ, hρ⟩ : ↥Y)).toMonoidHom =
      (conjByElt ρ J).subgroupOf Y := by
  ext z
  rw [Subgroup.mem_subgroupOf, mem_conjByElt]
  constructor
  · rintro ⟨k, hk, rfl⟩
    have hk' : (k : G) ∈ J := hk
    have e : ρ⁻¹ * (((MulAut.conj (⟨ρ, hρ⟩ : ↥Y)).toMonoidHom k : ↥Y) : G) * ρ = (k : G) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [e]
    exact hk'
  · intro hz
    refine ⟨⟨ρ⁻¹ * z * ρ, Y.mul_mem (Y.mul_mem (Y.inv_mem hρ) z.2) hρ⟩, hz, ?_⟩
    apply Subtype.ext
    simp [MulAut.conj_apply, mul_assoc]

omit [Finite G] in
theorem conjByElt_one_W (K : Subgroup G) : conjByElt 1 K = K := by
  ext z
  simp [mem_conjByElt]

omit [Finite G] in
theorem conjByElt_inv_conjByElt_W (ρ : G) (K : Subgroup G) :
    conjByElt ρ⁻¹ (conjByElt ρ K) = K := by
  rw [← conjByElt_mul_W, inv_mul_cancel, conjByElt_one_W]

omit [Finite G] in
theorem mem_normalizer_subgroupOf {J Y : Subgroup G} {x : ↥Y}
    (h : (x : G) ∈ Subgroup.normalizer (J : Set G)) :
    x ∈ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
  refine Subgroup.mem_normalizer_iff.mpr fun z => ?_
  simpa [Subgroup.mem_subgroupOf] using Subgroup.mem_normalizer_iff.mp h (z : G)

omit [Finite G] in
theorem J_le_wY (J J' R : Subgroup G) : J ≤ wY J J' R :=
  (le_sup_left : J ≤ J ⊔ J').trans le_sup_left

omit [Finite G] in
theorem J'_le_wY (J J' R : Subgroup G) : J' ≤ wY J J' R :=
  (le_sup_right : J' ≤ J ⊔ J').trans le_sup_left

noncomputable abbrev wAut (J J' R S : Subgroup G) : Subgroup (MulAut (VMod J J' R)) :=
  autI (isElemAbelian_wV J J' R) S

@[expose] noncomputable def wTau (J J' R : Subgroup G) {ρ : G} (hρ : ρ ∈ wY J J' R) :
    MulAut (VMod J J' R) :=
  convI (isElemAbelian_wV J J' R) ⟨ρ, Y_le_normalizer_V hρ⟩

omit [Finite G] in
theorem wAut_eq_map {J J' R : Subgroup G} (S : Subgroup G) (hS : S ≤ wY J J' R) :
    wAut J J' R S = (S.subgroupOf (wY J J' R)).map (actY J J' R) :=
  autI_eq_map_convHom _ Y_le_normalizer_V hS

omit [Finite G] in
theorem wV_le_pCoreOf (J J' R : Subgroup G) : wV J J' R ≤ pCoreOf 2 (wY J J' R) :=
  A4.omegaOneCenterOf_le _

omit [Finite G] in
theorem R_le_normalizer_wV (J J' R : Subgroup G) : R ≤ Subgroup.normalizer (wV J J' R : Set G) :=
  (le_sup_right : R ≤ (J ⊔ J') ⊔ R).trans Y_le_normalizer_V

omit [Finite G] in
theorem VMod_sq_eq_one {J J' R : Subgroup G} (v : VMod J J' R) : v ^ 2 = 1 := IntMod.sq_eq_one v

omit [Finite G] in
theorem wAut_le_wAut {J J' R : Subgroup G} (S : Subgroup G) (hS : S ≤ wY J J' R) :
    wAut J J' R S ≤ wAut J J' R (wY J J' R) :=
  autI_mono _ hS

namespace WreathData

variable {H R J J' : Subgroup G} {ρ : G} (d : WreathData H R J J' ρ)

include d

theorem mem_Y : ρ ∈ wY J J' R := Subgroup.mem_sup_right d.mem

theorem moduleFacts :
    CFSG.IsQuasisimple ↥(wAut J J' R J) ∧ CFSG.IsQuasisimple ↥(wAut J J' R J') ∧
    (∀ a ∈ wAut J J' R J, ∀ b ∈ wAut J J' R J', a * b = b * a) ∧
    wAut J J' R J' = (wAut J J' R J).map (MulAut.conj (wTau J J' R d.mem_Y)).toMonoidHom ∧
    (∀ x ∈ wAut J J' R (wY J J' R), ∀ l ∈ wAut J J' R J ⊔ wAut J J' R J',
      x * l * x⁻¹ ∈ wAut J J' R J ⊔ wAut J J' R J') ∧
    (∀ x ∈ wAut J J' R (wY J J' R), ∃ e : ℕ, x ^ 2 ^ e ∈ wAut J J' R J ⊔ wAut J J' R J') ∧
    pCoreOf 2 (wAut J J' R (wY J J' R)) = ⊥ := by
  set Y : Subgroup G := wY J J' R with hYdef
  have hJY : J ≤ Y := J_le_wY J J' R
  have hJ'Y : J' ≤ Y := J'_le_wY J J' R
  set t : ↥Y := ⟨ρ, d.mem_Y⟩ with ht
  have hK₂ : (J.subgroupOf Y).map (MulAut.conj t).toMonoidHom = J'.subgroupOf Y := by
    rw [ht, map_conj_subgroupOf d.mem_Y, ← d.eq]
  have hXY : J ⊔ J' ≤ Y := sup_le hJY hJ'Y
  have hXn : ((J ⊔ J').subgroupOf Y).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr
      (d.sup_le_H.trans d.normalizer_sup)
  have hqK : CFSG.IsQuasisimple (↥(J.subgroupOf Y) ⧸ CFSG.pCore 2 ↥(J.subgroupOf Y)) :=
    isQuasisimple_subgroupOf hJY d.cfg.quasi
  have hKn : (J.subgroupOf Y ⊔ (J.subgroupOf Y).map (MulAut.conj t).toMonoidHom).Normal := by
    rw [hK₂, ← Subgroup.subgroupOf_sup hJY hJ'Y]
    exact hXn
  have hcomm : ⁅J.subgroupOf Y, (J.subgroupOf Y).map (MulAut.conj t).toMonoidHom⁆ ≤
      CFSG.pCore 2 ↥Y := by
    rw [hK₂, Subgroup.commutator_le]
    intro a ha b hb
    rw [Subgroup.mem_subgroupOf] at ha hb
    have h1 : ⁅(a : G), (b : G)⁆ ∈ ⁅J, J'⁆ := Subgroup.commutator_mem_commutator ha hb
    have h2 := d.pCoreOf_H_le_Y (d.comm h1)
    have e : ((⁅a, b⁆ : ↥Y) : G) = ⁅(a : G), (b : G)⁆ := by simp [commutatorElement_def]
    exact (SBc16.mem_pCore_iff_coe _ _).mpr (by rw [e]; exact h2)
  have hQ : CFSG.pCore 2 ↥Y ≤ (actY J J' R).ker := by
    intro x hx
    rw [ker_actY, Subgroup.mem_subgroupOf]
    refine ⟨x.2, pCoreOf_Y_le_centralizer_V ?_⟩
    exact (SBc16.mem_pCore_iff_coe _ x).mp hx
  have h2 : ∀ y : ↥Y, ∃ e : ℕ,
      y ^ 2 ^ e ∈ J.subgroupOf Y ⊔ (J.subgroupOf Y).map (MulAut.conj t).toMonoidHom := by
    rw [hK₂, ← Subgroup.subgroupOf_sup hJY hJ'Y]
    intro y
    obtain ⟨x, hx, r, hr, hyxr⟩ := d.exists_mul_of_mem_Y y.2
    obtain ⟨k, hk⟩ := d.cfg.radical.isPGroup ⟨r, hr⟩
    refine ⟨k, ?_⟩
    have hxY : x ∈ Y := Subgroup.mem_sup_left hx
    have hrY : r ∈ Y := Subgroup.mem_sup_right hr
    have hy : y = ⟨x, hxY⟩ * ⟨r, hrY⟩ := Subtype.ext hyxr
    have hrk : (⟨r, hrY⟩ : ↥Y) ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hxX : (⟨x, hxY⟩ : ↥Y) ∈ (J ⊔ J').subgroupOf Y := hx
    rw [← QuotientGroup.eq_one_iff (N := (J ⊔ J').subgroupOf Y), QuotientGroup.mk_pow, hy,
      QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff _).mpr hxX, one_mul, ← QuotientGroup.mk_pow,
      hrk]
    rfl
  have hperm : ∀ x : ↥Y, x ∈ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) ∨
      t⁻¹ * x ∈ Subgroup.normalizer ((J.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    intro x
    have hxH : (x : G) ∈ H := d.sup_le_H x.2
    rcases d.orb x hxH with h | h
    · exact Or.inl (mem_normalizer_subgroupOf (conjByElt_eq_self_iff.mp h))
    · refine Or.inr (mem_normalizer_subgroupOf ?_)
      have h' : conjByElt (ρ⁻¹ * (x : G)) J = J := by
        rw [conjByElt_mul_W, h, d.eq, conjByElt_inv_conjByElt_W]
      simpa [ht] using conjByElt_eq_self_iff.mp h'
  have hnt : ¬ J.subgroupOf Y ⊔ (J.subgroupOf Y).map (MulAut.conj t).toMonoidHom ≤
      (actY J J' R).ker := by
    intro h
    apply d.not_J_le_centralizer_V
    intro x hx
    have hxY : x ∈ Y := hJY hx
    have hmem : (⟨x, hxY⟩ : ↥Y) ∈ (actY J J' R).ker :=
      h (Subgroup.mem_sup_left (by simpa [Subgroup.mem_subgroupOf] using hx))
    rw [ker_actY, Subgroup.mem_subgroupOf] at hmem
    exact hmem.2
  obtain ⟨hq₁, hq₂, hc, hconj, hn, h2', hO2⟩ :=
    S153M.ar_facts_two (actY J J' R) (J.subgroupOf Y) t hqK hKn hcomm hQ h2 hperm hnt
  rw [← wAut_eq_map J hJY] at hq₁ hc hconj hn h2'
  rw [hK₂, ← wAut_eq_map J' hJ'Y] at hq₂ hc hconj hn h2'
  rw [range_actY] at hn h2' hO2
  refine ⟨hq₁, hq₂, hc, ?_, hn, h2', hO2⟩
  exact hconj

theorem exists_offender_le_R :
    ∃ A : Subgroup (MulAut (VMod J J' R)),
      IsFFStarOffender (wAut J J' R (wY J J' R)) A ∧ A ≤ wAut J J' R R := by
  have hV := isElemAbelian_wV J J' R
  have hVR : wV J J' R ≤ R := (wV_le_pCoreOf J J' R).trans d.pCoreOf_Y_le
  obtain ⟨B, hB⟩ := (offenderImages_nonempty_iff_not_le hV).2 d.not_thompsonJ_le_centralizer
  have h1 := offenderImages_isFFStarOffender hV hVR (R_le_normalizer_wV J J' R) hB
  exact ⟨B, isFFStarOffender_mono (autI_mono hV (le_sup_right : R ≤ (J ⊔ J') ⊔ R)) h1, h1.1⟩

theorem isFFModule_Y : IsFFModule (wAut J J' R (wY J J' R)) := by
  obtain ⟨A, hA, -⟩ := d.exists_offender_le_R
  have hTF := B1_4_5 (fun v : VMod J J' R => VMod_sq_eq_one v) (wAut J J' R (wY J J' R))
  have hiff := hTF.out 1 2
  exact hiff.2 ⟨A, hA⟩

theorem tau_mem : wTau J J' R d.mem_Y ∈ wAut J J' R (wY J J' R) :=
  convI_mem_autI _ d.mem_Y _

theorem twoB56_large (h56 : AsB56) (hA21 : AsA21SQTKSection)
    (hcard : 504 ≤ Nat.card ↥(wAut J J' R J)) :
    S153M.TwoB56 (wAut J J' R (wY J J' R)) (wAut J J' R J) (wAut J J' R J') := by
  obtain ⟨hq₁, hq₂, hc, hconj, hn, h2', hO2⟩ := d.moduleFacts
  have hXr : wAut J J' R (wY J J' R) = (actY J J' R).range := (range_actY J J' R).symm
  have hτX := d.tau_mem
  have hL₁X := wAut_le_wAut J (J_le_wY J J' R)
  have hL₂X := wAut_le_wAut J' (J'_le_wY J J' R)
  have hFF := d.isFFModule_Y
  have hV := fun v : VMod J J' R => VMod_sq_eq_one v
  obtain ⟨hL₁J, hL₂J⟩ := S153M.twoA_le_ffJ hV hτX hL₁X hL₂X hc hn hconj h2' hq₁ hq₂ hO2 hFF
  have hB53 : B53Hyp (ffJ (wAut J J' R (wY J J' R))) := by
    rw [hXr] at hL₁J hL₂J hn h2' hO2 ⊢
    exact S153M.b53Hyp_of_two hA21 d.sqtk_Y (actY J J' R) hq₁ hq₂ hc hL₁J hL₂J hn h2' hO2
  exact S153M.twoB56_of_ffModule h56 hV hτX hL₁X hL₂X hc hn hconj h2' hq₁ hq₂ hcard hO2 hFF hB53

end WreathData

end CFSG.Quasithin.S146zW
