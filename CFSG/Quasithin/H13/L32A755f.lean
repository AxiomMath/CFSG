module

public import CFSG.Quasithin.H13.L32A755e
public import CFSG.Quasithin.H13.L32A755d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.H13.Orbit

namespace M755

theorem zornNorm_add_one' {x : quasithinZorn (ZMod 2)} (hx : x.1 + x.2.2.2 = 0) :
    zornNorm (x + ((1, 0, 0, 1) : quasithinZorn (ZMod 2))) = zornNorm x + 1 := by
  simp only [zornNorm, Prod.fst_add, Prod.snd_add, Pi.add_apply, Pi.zero_apply, add_zero]
  linear_combination hx

theorem zornNorm_xor129 {c : ℕ} (hc : c ∈ o0Codes) :
    zornNorm (decodeZ (c ^^^ 129)) = zornNorm (decodeZ c) + 1 := by
  have h129 : decodeZ 129 = ((1, 0, 0, 1) : quasithinZorn (ZMod 2)) := by decide
  rw [decodeZ_xor, h129]
  exact zornNorm_add_one' ((trace_decodeZ_iff c (mem_o0Codes.1 hc).1).2 (mem_o0Codes.1 hc).2)

theorem zornNorm_o0Act (g : ↥(quasithinG2 (ZMod 2))) (c : O0C) :
    zornNorm (decodeZ (o0Act g c).1) = zornNorm (decodeZ c.1) := by
  change zornNorm (decodeZ (mact (matCode g.1) c.1)) = _
  rw [decodeZ_mact' g.1 (mem_o0Codes.1 c.2).1]
  exact quasithinG2_norm g.2 _

theorem exists_equiv_of_g2WeylDerived {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (h : G2WeylDerived L) :
    ∃ e : W ≃* ModO, L.map (MulAut.congr e).toMonoidHom =
      (g2Derived (ZMod 2)).map (g2OAct (ZMod 2)) := by
  obtain ⟨K, _, _, hK2, hR⟩ := h
  have := charP_two_of_natCard_two hK2
  obtain ⟨π, β, hβ⟩ := (CFSG.Quasithin.H.Mathieu.realizes_iff _ L ⊤ ⊥).1 hR
  let e : W ≃* (zornO0Model (quasithinG2 K)).Mod :=
    realizeEquiv (D := zornO0Model ⁅quasithinG2 K, quasithinG2 K⁆) hβ
  have hLe : L.map (MulAut.congr e).toMonoidHom = (g2Derived K).map (g2OAct K) :=
    map_congr_eq_of_equivariant e π hβ.1 (g2OAct K)
      (fun γ => ⟨γ.1, Subgroup.commutator_le_self _ γ.2⟩) (realizeEquiv_zornO0 hβ) _
      (mem_map_g2Derived_iff (g2OAct K))
  refine ⟨e.trans (modOEquivK hK2).symm, ?_⟩
  have hcongr : (MulAut.congr (e.trans (modOEquivK hK2).symm)).toMonoidHom =
      (MulAut.congr (modOEquivK hK2).symm).toMonoidHom.comp (MulAut.congr e).toMonoidHom :=
    MonoidHom.ext fun x => MulEquiv.ext fun _ => rfl
  rw [hcongr, ← Subgroup.map_map, hLe, Subgroup.map_map, ← map_g2Derived_conjF2Hom hK2,
    Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun g => congr_modOEquivK_symm hK2 g

theorem eq_one_or_eq_of_card_two {M : Type*} [Group M] {Z : Subgroup M} (hZ : Nat.card Z = 2)
    {c v : M} (hc : c ∈ Z) (hc1 : c ≠ 1) (hv : v ∈ Z) : v = 1 ∨ v = c := by
  by_contra h
  push Not at h
  obtain ⟨hv1, hvc⟩ := h
  have hinj : Function.Injective (![⟨1, Z.one_mem⟩, ⟨c, hc⟩, ⟨v, hv⟩] : Fin 3 → Z) := by
    intro i j hij
    have hij' := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;>
      first
      | rfl
      | exact absurd hij'.symm hc1
      | exact absurd hij' hc1
      | exact absurd hij'.symm hv1
      | exact absurd hij' hv1
      | exact absurd hij'.symm hvc
      | exact absurd hij' hvc
  have : Finite Z := Nat.finite_of_card_ne_zero (by rw [hZ]; norm_num)
  have h3 := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_eq_fintype_card, Fintype.card_fin, hZ] at h3
  omega

theorem weyl_eq_of_mem_fixV
    {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (hL : G2WeylDerived L) (hcard : Nat.card (fixV L) = 2) {x : MulAut W}
    (hx : ∀ l, l ∈ L ↔ x * l * x⁻¹ ∈ L) {w : W} (h : x w * w⁻¹ ∈ fixV L) : x w = w := by
  obtain ⟨e, he⟩ := exists_equiv_of_g2WeylDerived hL
  have hφinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  have hxD : MulAut.congr e x ∈ (g2OAct (ZMod 2)).range := by
    refine normalizer_two_O _ fun d => ?_
    obtain ⟨l, rfl⟩ := (MulAut.congr e).surjective d
    rw [← he]
    change (MulAut.congr e).toMonoidHom l ∈ L.map (MulAut.congr e).toMonoidHom ↔
      (MulAut.congr e).toMonoidHom x * (MulAut.congr e).toMonoidHom l *
        ((MulAut.congr e).toMonoidHom x)⁻¹ ∈ L.map (MulAut.congr e).toMonoidHom
    rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_iff_mem hφinj,
      Subgroup.mem_map_iff_mem hφinj]
    exact hx l
  obtain ⟨g, hg⟩ := hxD
  have hfix : ∀ v : W, v ∈ fixV L ↔
      e v ∈ fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) := by
    intro v
    rw [← he]
    constructor
    · rintro hv _ ⟨l, hl, rfl⟩
      change e (l (e.symm (e v))) = e v
      rw [MulEquiv.symm_apply_apply, hv l hl]
    · intro hv l hl
      have h1 := hv _ ⟨l, hl, rfl⟩
      change e (l (e.symm (e v))) = e v at h1
      rw [MulEquiv.symm_apply_apply] at h1
      exact e.injective h1
  have h129 : (129 : ℕ) ∈ o0Codes := by decide
  have hone : codeO ⟨129, h129⟩ ∈ fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2))) := by
    rintro _ ⟨γ, -, rfl⟩
    rw [g2OAct_codeO]
    congr 1
    apply o0Elt_injective
    apply Subtype.ext
    rw [o0Elt_act]
    change Multiplicative.ofAdd (γ.1 (decodeZ 129)) = Multiplicative.ofAdd (decodeZ 129)
    rw [decodeZ_129, (mem_quasithinG2_isZornAuto γ.2).map_one]
  have hne : codeO ⟨129, h129⟩ ≠ 1 := by
    rw [← codeO_zero]
    intro h1
    have h2 : (129 : ℕ) = 0 := congrArg Subtype.val (codeO_injective h1)
    omega
  have hcD : Nat.card (fixV ((g2Derived (ZMod 2)).map (g2OAct (ZMod 2)))) = 2 := by
    refine Eq.trans (Nat.card_congr ?_) hcard
    exact
      { toFun := fun v => ⟨e.symm v, (hfix _).2 (by rw [MulEquiv.apply_symm_apply]; exact v.2)⟩
        invFun := fun v => ⟨e v, (hfix _).1 v.2⟩
        left_inv := fun v => Subtype.ext (by simp)
        right_inv := fun v => Subtype.ext (by simp) }
  rcases eq_one_or_eq_of_card_two hcD hone hne ((hfix _).1 h) with h1 | h1
  · have h2 : x w * w⁻¹ = 1 := e.injective (h1.trans (map_one e).symm)
    exact mul_inv_eq_one.1 h2
  · exfalso
    obtain ⟨a, ha⟩ := codeO_surjective (e w)
    have h2 : e (x w) = e (x w * w⁻¹) * e w := by rw [← map_mul, inv_mul_cancel_right]
    have h3 : e (x w) = g2OAct (ZMod 2) g (e w) := by
      rw [hg]
      change e (x w) = e (x (e.symm (e w)))
      rw [MulEquiv.symm_apply_apply]
    rw [h3, h1, ← ha, g2OAct_codeO, ← codeO_xor] at h2
    have h4 := congrArg Subtype.val (codeO_injective h2)
    have h5 := zornNorm_o0Act g a
    rw [h4] at h5
    change zornNorm (decodeZ (129 ^^^ a.1)) = _ at h5
    rw [Nat.xor_comm, zornNorm_xor129 a.2] at h5
    have h6 : (1 : ZMod 2) = 0 := by linear_combination h5
    exact absurd h6 (by decide)

end M755

namespace Ctx753

variable {G : Type} [Group G] [Finite G] {T L V K : Subgroup G}

@[expose] noncomputable def actHX (C : Ctx753 T L V K) :
    ↥(hz T V) →* ↥(autIH (fsuV1 T V) V (hz T V) (hz T V)) :=
  (actH C.f918.H_le_normalizer_V₁ (le_normalizer_conjClosure V (hz T V))).codRestrict _
    fun h => by
      rw [autIH_eq_map C.f918 le_rfl]
      exact ⟨h, Subgroup.mem_subgroupOf.mpr h.2, rfl⟩

theorem actHX_coe (C : Ctx753 T L V K) (h : ↥(hz T V)) :
    (C.actHX h : MulAut ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V)))) =
      actH C.f918.H_le_normalizer_V₁ (le_normalizer_conjClosure V (hz T V)) h := rfl

theorem autX_le_autH (C : Ctx753 T L V K) {X : Subgroup G} (hXH : X ≤ hz T V) :
    autIH (fsuV1 T V) V (hz T V) X ≤ autIH (fsuV1 T V) V (hz T V) (hz T V) := by
  rw [autIH_eq_map C.f918 hXH, autIH_eq_map C.f918 le_rfl]
  exact Subgroup.map_mono fun x _ => Subgroup.mem_subgroupOf.mpr x.2

attribute [local instance] commGroupOfFact

variable [Fact (IsElemAbelian 2 (tildeOf (fsuV1 T V) (conjClosure V (hz T V))))]

theorem autH_le_stabSub_top (_C : Ctx753 T L V K) :
    autIH (fsuV1 T V) V (hz T V) (hz T V) ≤ stabSub ⊤ := fun x _ v => by simp

theorem autH_le_stabSub_fixV (C : Ctx753 T L V K) :
    autIH (fsuV1 T V) V (hz T V) (hz T V) ≤
      stabSub (fixV (autIH (fsuV1 T V) V (hz T V) K)) :=
  M753.le_stabSub_fixV C.autH_le_normalizer

structure Coord (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) : Prop where
  map_K : (autSec (autIH (fsuV1 T V) V (hz T V) K) ⊤
      (fixV (autIH (fsuV1 T V) V (hz T V) K))).map (MulAut.congr e).toMonoidHom =
    (g2Derived (ZMod 2)).map (g2QAct (ZMod 2))
  mem_H : ∀ x ∈ autSec (autIH (fsuV1 T V) V (hz T V) (hz T V)) ⊤
      (fixV (autIH (fsuV1 T V) V (hz T V) K)), MulAut.congr e x ∈ (g2QAct (ZMod 2)).range
  map_T : (autSec (autIH (fsuV1 T V) V (hz T V) T) ⊤
      (fixV (autIH (fsuV1 T V) V (hz T V) K))).map (MulAut.congr e).toMonoidHom ≤
    sSubG.map (g2QAct (ZMod 2))
  mem_T : ∀ i ∈ M755.innerS, g2QAct (ZMod 2) (sEltG i) ∈
    (autSec (autIH (fsuV1 T V) V (hz T V) T) ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K))).map
      (MulAut.congr e).toMonoidHom
  nt : ∃ k ∈ autIH (fsuV1 T V) V (hz T V) K,
    ∃ v ∈ (⊤ : Subgroup ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V)))),
      k v * v⁻¹ ∉ fixV (autIH (fsuV1 T V) V (hz T V) K)
  weyl : ∀ x ∈ autIH (fsuV1 T V) V (hz T V) (hz T V),
    ∀ w : ↥(tildeOf (fsuV1 T V) (conjClosure V (hz T V))),
      x w * w⁻¹ ∈ fixV (autIH (fsuV1 T V) V (hz T V) K) → x w = w

theorem exists_coord
    (C : Ctx753 T L V K) (h38 : Lemma14_7_38) :
    ∃ e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ, Coord C e := by
  obtain ⟨e, h1, h2, h3, h4⟩ := C.exists_coord755 h38
  refine ⟨e, ⟨h1, h2, h3, h4, (C.natural_sec h38).2.2.2, fun x hx w hw => ?_⟩⟩
  rcases C.lemma14_7_54 h38 with ⟨h0, -⟩ | ⟨h2, -, hW⟩
  · rw [h0, Subgroup.mem_bot, mul_inv_eq_one] at hw
    exact hw
  · exact M755.weyl_eq_of_mem_fixV hW h2
      (fun l => Subgroup.mem_normalizer_iff.mp (C.autH_le_normalizer hx) l) hw

@[expose] noncomputable def θ (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) :
    ↥(conjClosure V (hz T V)) →* ModQ :=
  e.toMonoidHom.comp ((M755.piBar _).comp (tildeHom C.U_le_normalizer))

theorem θ_apply (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) (u : ↥(conjClosure V (hz T V))) :
    C.θ e u = e (M755.piBar _ (modMk C.U_le_normalizer u u.2)) := rfl

theorem θ_surjective (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) :
    Function.Surjective (C.θ e) :=
  e.surjective.comp ((M755.piBar_surjective _).comp (tildeHom_surjective C.U_le_normalizer))

theorem θ_eq_one_iff (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) (u : ↥(conjClosure V (hz T V))) :
    C.θ e u = 1 ↔ modMk C.U_le_normalizer u u.2 ∈ fixV (autIH (fsuV1 T V) V (hz T V) K) := by
  rw [θ_apply, ← map_one e, e.injective.eq_iff]
  exact M755.piBar_eq_one_iff _ _

@[expose] noncomputable def rho (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) :
    ↥(hz T V) →* MulAut ModQ :=
  (MulAut.congr e).toMonoidHom.comp
    ((M753.secHom C.autH_le_stabSub_top C.autH_le_stabSub_fixV).comp C.actHX)

theorem rho_θ (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) (h : ↥(hz T V))
    (u : ↥(conjClosure V (hz T V))) :
    C.rho e h (C.θ e u) = C.θ e ⟨(h : G) * u * (h : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) h.2) u).mp u.2⟩ := by
  rw [θ_apply, θ_apply]
  change e ((M753.secHom C.autH_le_stabSub_top C.autH_le_stabSub_fixV (C.actHX h))
    (e.symm (e (M755.piBar _ (modMk C.U_le_normalizer u u.2))))) = _
  rw [MulEquiv.symm_apply_apply, M755.secHom_piBar, actHX_coe,
    actH_modMk C.f918.H_le_normalizer_V₁ C.U_le_normalizer (le_normalizer_conjClosure V (hz T V))]

theorem rho_mem_range (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h : ↥(hz T V)) : C.rho e h ∈ (g2QAct (ZMod 2)).range := by
  refine E.mem_H _ ?_
  rw [← M753.range_secHom C.autH_le_stabSub_top C.autH_le_stabSub_fixV]
  exact ⟨_, rfl⟩

@[expose] noncomputable def Φ (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e) :
    ↥(hz T V) →* ↥(quasithinG2 (ZMod 2)) :=
  (MonoidHom.ofInjective g2QAct_injective).symm.toMonoidHom.comp
    ((C.rho e).codRestrict _ (C.rho_mem_range E))

theorem g2QAct_Φ (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h : ↥(hz T V)) : g2QAct (ZMod 2) (C.Φ E h) = C.rho e h := by
  have h1 := MonoidHom.ofInjective_apply (f := g2QAct (ZMod 2)) g2QAct_injective (x := C.Φ E h)
  have h2 : MonoidHom.ofInjective g2QAct_injective (C.Φ E h) =
      (C.rho e).codRestrict _ (C.rho_mem_range E) h := by
    simp only [Φ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply]
  rw [h2] at h1
  exact h1.symm

theorem θ_conj (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h : ↥(hz T V)) (u : ↥(conjClosure V (hz T V))) :
    C.θ e ⟨(h : G) * u * (h : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) h.2) u).mp u.2⟩ =
      g2QAct (ZMod 2) (C.Φ E h) (C.θ e u) := by
  rw [g2QAct_Φ, rho_θ]

theorem Φ_eq_one_iff (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h : ↥(hz T V)) : C.Φ E h = 1 ↔ (h : G) ∈ pCoreOf 2 (hz T V) := by
  have hinj := M753.secHom_injective_X C.autK_le_autH C.autH_le_normalizer
    C.autH_inf_centralizer_le C.autH_le_stabSub_top C.autH_le_stabSub_fixV
    (M753.isSimpleGroup_of_b42 C.b42TypeU33_autK) E.nt
  have key : C.Φ E h = 1 ↔ C.actHX h = 1 := by
    constructor
    · intro h1
      have h2 : C.rho e h = 1 := by rw [← g2QAct_Φ C E, h1, map_one]
      have h3 : M753.secHom C.autH_le_stabSub_top C.autH_le_stabSub_fixV (C.actHX h) = 1 :=
        (MulAut.congr e).injective (h2.trans (map_one _).symm)
      exact hinj (h3.trans (map_one _).symm)
    · intro h1
      apply g2QAct_injective
      rw [g2QAct_Φ C E, map_one]
      change (MulAut.congr e).toMonoidHom
        (M753.secHom C.autH_le_stabSub_top C.autH_le_stabSub_fixV (C.actHX h)) = 1
      rw [h1, map_one, map_one]
  rw [key]
  constructor
  · intro h1
    exact mem_pCoreOf_of_actH_eq_one C.f918 (congrArg Subtype.val h1)
  · intro h1
    exact Subtype.ext (C.f918.actH_eq_one_of_mem_pCoreOf (le_conjClosure V (hz T V)) h1)

theorem map_rho (C : Ctx753 T L V K)
    (e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ) {X : Subgroup G}
    (hXH : X ≤ hz T V) :
    (X.subgroupOf (hz T V)).map (C.rho e) =
      (autSec (autIH (fsuV1 T V) V (hz T V) X) ⊤
        (fixV (autIH (fsuV1 T V) V (hz T V) K))).map (MulAut.congr e).toMonoidHom := by
  have hXX := C.autX_le_autH hXH
  have hXJ := hXX.trans C.autH_le_stabSub_top
  have hXC := hXX.trans C.autH_le_stabSub_fixV
  rw [rho, ← Subgroup.map_map]
  congr 1
  rw [← M753.range_secHom hXJ hXC]
  ext φ
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hmem : actH C.f918.H_le_normalizer_V₁ (le_normalizer_conjClosure V (hz T V)) x ∈
        autIH (fsuV1 T V) V (hz T V) X := by
      rw [autIH_eq_map C.f918 hXH]
      exact ⟨x, hx, rfl⟩
    exact ⟨⟨_, hmem⟩, rfl⟩
  · rintro ⟨⟨y, hy⟩, rfl⟩
    have hy' := hy
    rw [autIH_eq_map C.f918 hXH] at hy'
    obtain ⟨x, hx, rfl⟩ := hy'
    exact ⟨x, hx, rfl⟩

theorem map_Φ_K (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e) :
    (K.subgroupOf (hz T V)).map (C.Φ E) = g2Derived (ZMod 2) := by
  apply Subgroup.map_injective g2QAct_injective
  rw [← E.map_K, ← C.map_rho e C.le_hz, Subgroup.map_map]
  congr 1
  exact MonoidHom.ext fun h => C.g2QAct_Φ E h

theorem Φ_mem_sSubG (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    {t : ↥(hz T V)} (ht : (t : G) ∈ T) : C.Φ E t ∈ sSubG := by
  have h1 : C.rho e t ∈ (T.subgroupOf (hz T V)).map (C.rho e) :=
    ⟨t, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  rw [C.map_rho e C.T_le] at h1
  obtain ⟨s, hs, hse⟩ := E.map_T h1
  have h2 : C.Φ E t = s := g2QAct_injective (by rw [g2QAct_Φ]; exact hse.symm)
  rw [h2]
  exact hs

theorem modMk_conj_eq_of_θ (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h : ↥(hz T V)) (u : ↥(conjClosure V (hz T V)))
    (hθ : C.θ e ⟨(h : G) * u * (h : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) h.2) u).mp u.2⟩ =
        C.θ e u) :
    modMk C.U_le_normalizer ((h : G) * u * (h : G)⁻¹)
        ((Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) h.2) u).mp u.2) =
      modMk C.U_le_normalizer u u.2 := by
  have hx : actH C.f918.H_le_normalizer_V₁ (le_normalizer_conjClosure V (hz T V)) h ∈
      autIH (fsuV1 T V) V (hz T V) (hz T V) := (C.actHX h).2
  rw [← actH_modMk C.f918.H_le_normalizer_V₁ C.U_le_normalizer
    (le_normalizer_conjClosure V (hz T V)) h u.2]
  refine E.weyl _ hx _ ?_
  rw [actH_modMk C.f918.H_le_normalizer_V₁ C.U_le_normalizer
    (le_normalizer_conjClosure V (hz T V)) h u.2]
  rw [θ_apply, θ_apply, e.injective.eq_iff] at hθ
  rw [← M755.piBar_eq_one_iff, map_mul, map_inv, hθ, mul_inv_cancel]

theorem comm_mem_V1_of_θ (C : Ctx753 T L V K)
    {e : Sec ⊤ (fixV (autIH (fsuV1 T V) V (hz T V) K)) ≃* ModQ} (E : Coord C e)
    (h : ↥(hz T V)) (u : ↥(conjClosure V (hz T V)))
    (hθ : C.θ e ⟨(h : G) * u * (h : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V (hz T V) h.2) u).mp u.2⟩ =
        C.θ e u) :
    (u : G)⁻¹ * ((h : G) * u * (h : G)⁻¹) ∈ fsuV1 T V := by
  have h1 := C.modMk_conj_eq_of_θ E h u hθ
  exact secMk_eq_secMk_iff.mp (congrArg Subtype.val h1.symm)

end Ctx753

end CFSG.Quasithin.H13.L32A
