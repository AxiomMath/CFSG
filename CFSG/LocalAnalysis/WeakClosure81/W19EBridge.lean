module

public import CFSG.LocalAnalysis.WeakClosure81.W19Hyp197
public import CFSG.GroupTheory.SteinbergBKChiefFactorModule
public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.SignalizerFunctorTheorem.Quadratic
  CFSG.GroupTheory.SteinbergBK
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem le_pCore_of_normal_isPGroup {G : Type*} [Group G] {p : ℕ} {N : Subgroup G}
    (hN : N.Normal) (h : IsPGroup p N) : N ≤ pCore p G := by
  change N ≤ sSup {K : Subgroup G | K.Normal ∧ IsPGroup p K}
  exact le_sSup ⟨hN, h⟩

private theorem pCore_range_eq_bot_of_irreducible_aux {V : Type*} [AddCommGroup V]
    [Module (ZMod 2) V] [Finite V] {G : Type*} [Group G]
    (ρ : G →* (V ≃ₗ[ZMod 2] V)) {d : ℕ}
    (hV : Nat.card V = 2 ^ d) (hd : 1 ≤ d)
    (hirr : ∀ W : Submodule (ZMod 2) V,
      (∀ g : G, ∀ w ∈ W, ρ g w ∈ W) → W = ⊥ ∨ W = ⊤) :
    pCore 2 ρ.range = ⊥ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := pCore 2 ρ.range with hPdef
  let W : Submodule (ZMod 2) V :=
    { carrier := {v | ∀ g ∈ P, ((g : ρ.range) : V ≃ₗ[ZMod 2] V) v = v}
      add_mem' := fun {a b} ha hb g hg => by rw [map_add, ha g hg, hb g hg]
      zero_mem' := fun g _ => map_zero _
      smul_mem' := fun c v hv g hg => by rw [map_smul, hv g hg] }
  have hWinv : ∀ g : G, ∀ w ∈ W, ρ g w ∈ W := by
    intro g' w hw g hg
    have hconj : (⟨ρ g', g', rfl⟩ : ρ.range)⁻¹ * g * ⟨ρ g', g', rfl⟩ ∈ P := by
      have := (CFSG.pCore_normal (p := 2) (G := ρ.range)).conj_mem g hg
        (⟨ρ g', g', rfl⟩ : ρ.range)⁻¹
      simpa using this
    have h := hw _ hconj
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, LinearEquiv.mul_apply] at h
    have h' := congrArg (ρ g') h
    rw [← LinearEquiv.mul_apply, mul_inv_cancel] at h'
    exact h'
  have hWne : W ≠ ⊥ := by
    have hmod := IsPGroup.card_modEq_card_fixedPoints
      (CFSG.pCore_isPGroup (p := 2) (G := ρ.range)) V
    rw [hV] at hmod
    have h0 : (0 : V) ∈ MulAction.fixedPoints P V := fun g => smul_zero _
    have hpos : 0 < Nat.card (MulAction.fixedPoints P V) :=
      Nat.card_pos_iff.2 ⟨⟨_, h0⟩, inferInstance⟩
    have heven : 2 ∣ Nat.card (MulAction.fixedPoints P V) := by
      have h1 : 2 ∣ 2 ^ d := dvd_pow_self 2 (by omega)
      exact (Nat.modEq_zero_iff_dvd.1 (hmod.symm.trans (Nat.modEq_zero_iff_dvd.2 h1)))
    have h2 : 1 < Nat.card (MulAction.fixedPoints P V) := by
      obtain ⟨k, hk⟩ := heven
      omega
    have := Finite.one_lt_card_iff_nontrivial.1 h2
    obtain ⟨⟨v, hv⟩, hv0⟩ := exists_ne (⟨0, h0⟩ : ↥(MulAction.fixedPoints P V))
    intro hbot
    have hvW : v ∈ W := fun g hg => hv ⟨g, hg⟩
    rw [hbot, Submodule.mem_bot] at hvW
    exact hv0 (Subtype.ext hvW)
  rcases hirr W hWinv with h | h
  · exact absurd h hWne
  rw [eq_bot_iff]
  intro g hg
  rw [mem_bot]
  apply Subtype.ext
  apply LinearEquiv.ext
  intro v
  have hv : v ∈ W := h ▸ Submodule.mem_top
  exact hv g hg

private noncomputable def commGroupOfComm' {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) : CommGroup A :=
  { (inferInstance : Group A) with mul_comm := hc }

private noncomputable def elemModule' (p : ℕ) [NeZero p] {A : Type*} [Group A]
    (hc : ∀ a b : A, a * b = b * a) (hp : ∀ a : A, a ^ p = 1) :
    letI := commGroupOfComm' hc
    Module (ZMod p) (Additive A) :=
  letI := commGroupOfComm' hc
  AddCommMonoid.zmodModule fun x => by
    apply Additive.toMul.injective
    rw [toMul_nsmul, toMul_zero]
    exact hp _

theorem exists_rep {H E F : Subgroup G} (hH : Group.IsSolvable ↥H) (hEH : E ≤ H)
    (hE : IsElemAbelian 2 E) (hFE : F < E) (hEn : H ≤ normalizer (E : Set G))
    (hFn : H ≤ normalizer (F : Set G))
    (hirr : ∀ U : Subgroup G, F ≤ U → U ≤ E → H ≤ normalizer (U : Set G) →
      U = F ∨ U = E) :
    ∃ (W : Type) (_ : AddCommGroup W) (_ : Module (ZMod 2) W) (_ : Finite W)
      (ρ : ↥H →* LGL 2 W) (ι : G → W),
      (∀ e ∈ E, ∀ e' ∈ E, ι (e * e') = ι e + ι e') ∧
      (∀ w : W, ∃ e ∈ E, ι e = w) ∧
      (∀ e ∈ E, (ι e = 0 ↔ e ∈ F)) ∧
      (∀ h : ↥H, ∀ e ∈ E, ρ h (ι e) = ι (h * e * h⁻¹)) ∧
      (∀ U : Submodule (ZMod 2) W,
        (∀ h : ↥H, ∀ u ∈ U, ρ h u ∈ U) → U = ⊥ ∨ U = ⊤) ∧
      (∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ centralizerQuot H E F) ∧
      (∀ n : ↥H, (n : G) ∈ pCoreOf 2 H → ρ n = 1) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFH : F ≤ H := hFE.le.trans hEH
  have hX'n : (E.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hEH).2 hEn
  have hY'n : (F.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hFH).2 hFn
  have hYX' : F.subgroupOf H < E.subgroupOf H := by
    refine lt_of_le_of_ne (Subgroup.comap_mono (f := H.subtype) hFE.le) ?_
    intro h
    apply hFE.ne
    have h' := congrArg (Subgroup.map H.subtype) h
    rwa [Subgroup.map_subgroupOf_eq_of_le hFH, Subgroup.map_subgroupOf_eq_of_le hEH] at h'
  have hchief : ∀ Z : Subgroup ↥H, Z.Normal →
      ¬ (F.subgroupOf H < Z ∧ Z < E.subgroupOf H) := by
    rintro Z hZn ⟨hltYZ, hltZX⟩
    have hZU : Z.map H.subtype ≤ E := by
      rw [← Subgroup.map_subgroupOf_eq_of_le hEH]
      exact Subgroup.map_mono hltZX.le
    have hFU : F ≤ Z.map H.subtype := by
      intro f hf
      exact ⟨⟨f, hFH hf⟩, hltYZ.le ((Subgroup.mem_subgroupOf).2 hf), rfl⟩
    have hUn : H ≤ normalizer (Z.map H.subtype : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · rintro ⟨z, hz, rfl⟩
        exact ⟨⟨h, hh⟩ * z * ⟨h, hh⟩⁻¹, hZn.conj_mem z hz ⟨h, hh⟩, rfl⟩
      · rintro ⟨z, hz, hzx⟩
        refine ⟨⟨h, hh⟩⁻¹ * z * ⟨h, hh⟩,
          by simpa using hZn.conj_mem z hz ⟨h, hh⟩⁻¹, ?_⟩
        rw [map_mul, map_mul, map_inv, hzx]
        show (h : G)⁻¹ * (h * x * h⁻¹) * h = x
        group
    rcases hirr (Z.map H.subtype) hFU hZU hUn with hUF | hUE
    · have hZY : Z = F.subgroupOf H := by
        apply Subgroup.map_injective H.subtype_injective
        rw [hUF, Subgroup.map_subgroupOf_eq_of_le hFH]
      exact hltYZ.ne' hZY
    · have hZX : Z = E.subgroupOf H := by
        apply Subgroup.map_injective H.subtype_injective
        rw [hUE, Subgroup.map_subgroupOf_eq_of_le hEH]
      exact hltZX.ne hZX
  obtain ⟨p, d, hp, hd, -, hcard, hc, hpp, -⟩ :=
    solvable_chief_factor_module (X := E.subgroupOf H) (Y := F.subgroupOf H) hH hYX' hchief
  have hEsub : IsElemAbelian 2 (E.subgroupOf H) := hE.comap H.subtype_injective
  have hX'2 : IsPGroup 2 (E.subgroupOf H) := IsElemAbelian.isPGroup hEsub
  have hp2 : p = 2 := by
    have h2 : IsPGroup 2 (chiefQuot (E.subgroupOf H) (F.subgroupOf H)) :=
      hX'2.map (QuotientGroup.mk' (F.subgroupOf H))
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    rw [hcard] at hn
    have hdvd : p ∣ 2 ^ n := hn ▸ dvd_pow_self p (by omega)
    exact (Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow hdvd)
  subst hp2
  letI : CommGroup (chiefQuot (E.subgroupOf H) (F.subgroupOf H)) := commGroupOfComm' hc
  letI : Module (ZMod 2) (Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H))) :=
    elemModule' 2 hc hpp
  let ρf : ↥H → (Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H)) ≃ₗ[ZMod 2]
      Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H))) := fun g =>
    (MulEquiv.toAdditive (chiefConj (E.subgroupOf H) (F.subgroupOf H) g)).toLinearEquiv
      (ZMod.map_smul (MulEquiv.toAdditive (chiefConj (E.subgroupOf H) (F.subgroupOf H) g)))
  have hρf : ∀ (g : ↥H) (a : Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H))),
      ρf g a = Additive.ofMul
        (chiefConj (E.subgroupOf H) (F.subgroupOf H) g (Additive.toMul a)) := fun _ _ => rfl
  let ρ : ↥H →* (Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H)) ≃ₗ[ZMod 2]
      Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H))) :=
    { toFun := ρf
      map_one' := LinearEquiv.ext fun a => by rw [hρf, map_one]; rfl
      map_mul' := fun g h => LinearEquiv.ext fun a => by rw [hρf, map_mul]; rfl }
  have hρ : ∀ (g : ↥H) (a : Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H))),
      ρ g a = Additive.ofMul
        (chiefConj (E.subgroupOf H) (F.subgroupOf H) g (Additive.toMul a)) := fun _ _ => rfl
  let ι : G → Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H)) := fun g =>
    if hg : g ∈ E then
      Additive.ofMul (⟨QuotientGroup.mk' (F.subgroupOf H) ⟨g, hEH hg⟩,
        Subgroup.mem_map_of_mem _ ((Subgroup.mem_subgroupOf).2 hg)⟩ :
          chiefQuot (E.subgroupOf H) (F.subgroupOf H))
    else 0
  have hι_of : ∀ (g : G) (hg : g ∈ E), ι g =
      Additive.ofMul (⟨QuotientGroup.mk' (F.subgroupOf H) ⟨g, hEH hg⟩,
        Subgroup.mem_map_of_mem _ ((Subgroup.mem_subgroupOf).2 hg)⟩ :
          chiefQuot (E.subgroupOf H) (F.subgroupOf H)) := fun g hg => dif_pos hg
  have hι_add : ∀ e ∈ E, ∀ e' ∈ E, ι (e * e') = ι e + ι e' := by
    intro e he e' he'
    have hee' : e * e' ∈ E := E.mul_mem he he'
    rw [hι_of (e * e') hee', hι_of e he, hι_of e' he', ← ofMul_mul]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    show QuotientGroup.mk' (F.subgroupOf H) ⟨e * e', hEH hee'⟩ =
      QuotientGroup.mk' (F.subgroupOf H) ⟨e, hEH he⟩ *
        QuotientGroup.mk' (F.subgroupOf H) ⟨e', hEH he'⟩
    rw [← map_mul]
    rfl
  have hι_surj : ∀ w : Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H)),
      ∃ e ∈ E, ι e = w := by
    intro w
    obtain ⟨u, rfl⟩ : ∃ u : chiefQuot (E.subgroupOf H) (F.subgroupOf H),
        Additive.ofMul u = w := ⟨Additive.toMul w, rfl⟩
    obtain ⟨x, hx, hxu⟩ := Subgroup.mem_map.1 u.2
    have hxE : (x : G) ∈ E := (Subgroup.mem_subgroupOf).1 hx
    refine ⟨(x : G), hxE, ?_⟩
    rw [hι_of (x : G) hxE]
    have hmk : QuotientGroup.mk' (F.subgroupOf H) ⟨(x : G), hEH hxE⟩ =
        QuotientGroup.mk' (F.subgroupOf H) x :=
      congrArg (QuotientGroup.mk' (F.subgroupOf H)) (Subtype.ext rfl)
    have hu : (⟨QuotientGroup.mk' (F.subgroupOf H) ⟨(x : G), hEH hxE⟩,
        Subgroup.mem_map_of_mem _ ((Subgroup.mem_subgroupOf).2 hxE)⟩ :
          chiefQuot (E.subgroupOf H) (F.subgroupOf H)) = u := by
      apply Subtype.ext
      show QuotientGroup.mk' (F.subgroupOf H) ⟨(x : G), hEH hxE⟩ =
        (u : ↥H ⧸ F.subgroupOf H)
      rw [hmk, hxu]
    rw [hu]
  have hι_ker : ∀ e ∈ E, (ι e = 0 ↔ e ∈ F) := by
    intro e he
    rw [hι_of e he, ofMul_eq_zero]
    constructor
    · intro h1
      have h2 : QuotientGroup.mk' (F.subgroupOf H) ⟨e, hEH he⟩ = 1 := by
        simpa using congrArg Subtype.val h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact (Subgroup.mem_subgroupOf).1 h2
    · intro hf
      apply Subtype.ext
      show QuotientGroup.mk' (F.subgroupOf H) ⟨e, hEH he⟩ = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact (Subgroup.mem_subgroupOf).2 hf
  have hι_equiv : ∀ h : ↥H, ∀ e ∈ E, ρ h (ι e) = ι (h * e * h⁻¹) := by
    intro h e he
    have hconj : (h : G) * e * (h : G)⁻¹ ∈ E :=
      ((Subgroup.mem_normalizer_iff.1 (hEn h.2)) e).1 he
    rw [hι_of e he, hρ h]
    simp only [toMul_ofMul]
    rw [chiefConj_mk (E.subgroupOf H) (F.subgroupOf H) h
      ⟨e, hEH he⟩ ((Subgroup.mem_subgroupOf).2 he),
      hι_of ((h : G) * e * ↑(h⁻¹)) hconj]
    apply congrArg Additive.ofMul
    apply Subtype.ext
    rfl
  have hι_irr : ∀ W : Submodule (ZMod 2)
      (Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H))),
      (∀ h : ↥H, ∀ w ∈ W, ρ h w ∈ W) → W = ⊥ ∨ W = ⊤ := by
    intro W hW
    let Wm : Subgroup ↥(chiefQuot (E.subgroupOf H) (F.subgroupOf H)) :=
      AddSubgroup.toSubgroup' W.toAddSubgroup
    have hWm : ∀ x : ↥(chiefQuot (E.subgroupOf H) (F.subgroupOf H)),
        x ∈ Wm ↔ Additive.ofMul x ∈ W := fun _ => Iff.rfl
    let M : Subgroup (↥H ⧸ F.subgroupOf H) :=
      Wm.map (chiefQuot (E.subgroupOf H) (F.subgroupOf H)).subtype
    have hMle : M ≤ chiefQuot (E.subgroupOf H) (F.subgroupOf H) := Subgroup.map_subtype_le _
    have hMinv : ∀ (h : ↥H) (x : ↥(chiefQuot (E.subgroupOf H) (F.subgroupOf H))),
        (↑x : ↥H ⧸ F.subgroupOf H) ∈ M →
        (↑(chiefConj (E.subgroupOf H) (F.subgroupOf H) h x) : ↥H ⧸ F.subgroupOf H) ∈ M := by
      intro h x hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hx
      have hyx' : y = x := Subtype.ext hyx
      subst hyx'
      refine ⟨chiefConj (E.subgroupOf H) (F.subgroupOf H) h y, ?_, rfl⟩
      rw [hWm] at hy
      show Additive.ofMul (chiefConj (E.subgroupOf H) (F.subgroupOf H) h y) ∈ W
      have := hW h (Additive.ofMul y) hy
      rwa [hρ h (Additive.ofMul y), toMul_ofMul] at this
    have hVX : ∀ v : ↥H, QuotientGroup.mk' (F.subgroupOf H) v ∈ M →
        v ∈ E.subgroupOf H := by
      intro v hv
      have hle : QuotientGroup.mk' (F.subgroupOf H) v ∈
          chiefQuot (E.subgroupOf H) (F.subgroupOf H) := hMle hv
      have : v ∈ (chiefQuot (E.subgroupOf H) (F.subgroupOf H)).comap
          (QuotientGroup.mk' (F.subgroupOf H)) :=
        Subgroup.mem_comap.2 hle
      rwa [Subgroup.comap_map_eq, QuotientGroup.ker_mk', sup_eq_left.mpr hYX'.le] at this
    have hFU : F ≤ (M.comap (QuotientGroup.mk' (F.subgroupOf H))).map H.subtype := by
      intro f hf
      refine ⟨⟨f, hFH hf⟩, ?_, rfl⟩
      show QuotientGroup.mk' (F.subgroupOf H) ⟨f, hFH hf⟩ ∈ M
      have hfY : (⟨f, hFH hf⟩ : ↥H) ∈ F.subgroupOf H := (Subgroup.mem_subgroupOf).2 hf
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hfY]
      exact ⟨1, (hWm 1).mpr (by rw [ofMul_one]; exact W.zero_mem), rfl⟩
    have hUE : (M.comap (QuotientGroup.mk' (F.subgroupOf H))).map H.subtype ≤ E := by
      intro x hx
      obtain ⟨v, hv, rfl⟩ := hx
      exact (Subgroup.mem_subgroupOf).1 (hVX v hv)
    have hUinv : ∀ (h : ↥H) (x : G),
        x ∈ (M.comap (QuotientGroup.mk' (F.subgroupOf H))).map H.subtype →
        (h : G) * x * (h : G)⁻¹ ∈
          (M.comap (QuotientGroup.mk' (F.subgroupOf H))).map H.subtype := by
      rintro h x ⟨v, hv, rfl⟩
      have hv' : QuotientGroup.mk' (F.subgroupOf H) v ∈ M := hv
      refine ⟨h * v * h⁻¹, ?_, rfl⟩
      show QuotientGroup.mk' (F.subgroupOf H) (h * v * h⁻¹) ∈ M
      rw [map_mul, map_mul, map_inv]
      exact hMinv h ⟨QuotientGroup.mk' (F.subgroupOf H) v, hMle hv'⟩ hv'
    have hUn : H ≤ normalizer
        ((M.comap (QuotientGroup.mk' (F.subgroupOf H))).map H.subtype : Set G) := by
      intro h hh
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · exact hUinv ⟨h, hh⟩ x
      · intro hx
        have hx' : (h : G)⁻¹ * (h * x * h⁻¹) * (h : G) ∈
            (M.comap (QuotientGroup.mk' (F.subgroupOf H))).map H.subtype := by
          simpa [Subgroup.coe_inv] using hUinv ⟨h, hh⟩⁻¹ (h * x * h⁻¹) hx
        rwa [show (h : G)⁻¹ * (h * x * h⁻¹) * (h : G) = x by group] at hx'
    rcases hirr ((M.comap (QuotientGroup.mk' (F.subgroupOf H))).map H.subtype)
      hFU hUE hUn with hUF | hUE'
    · left
      rw [eq_bot_iff]
      intro w hw
      rw [Submodule.mem_bot]
      apply Additive.toMul.injective
      rw [toMul_zero]
      have hwWm : Additive.toMul w ∈ Wm := (hWm _).mpr (by rwa [ofMul_toMul])
      obtain ⟨v, hv⟩ := QuotientGroup.mk'_surjective (F.subgroupOf H)
        (Additive.toMul w : ↥(chiefQuot (E.subgroupOf H) (F.subgroupOf H)))
      have hvM : (QuotientGroup.mk' (F.subgroupOf H) v : ↥H ⧸ F.subgroupOf H) ∈ M :=
        ⟨(Additive.toMul w : ↥(chiefQuot (E.subgroupOf H) (F.subgroupOf H))), hwWm, hv.symm⟩
      have hvV : v ∈ M.comap (QuotientGroup.mk' (F.subgroupOf H)) := hvM
      have hvU : H.subtype v ∈
          (M.comap (QuotientGroup.mk' (F.subgroupOf H))).map H.subtype := ⟨v, hvV, rfl⟩
      rw [hUF] at hvU
      have hvY : v ∈ F.subgroupOf H := (Subgroup.mem_subgroupOf).2 hvU
      exact Subtype.ext (by rw [← hv]; exact (QuotientGroup.eq_one_iff v).mpr hvY)
    · right
      have hVF : M.comap (QuotientGroup.mk' (F.subgroupOf H)) = E.subgroupOf H := by
        apply Subgroup.map_injective H.subtype_injective
        rw [hUE', Subgroup.map_subgroupOf_eq_of_le hEH]
      have hMtop : M = chiefQuot (E.subgroupOf H) (F.subgroupOf H) := by
        calc M = (M.comap (QuotientGroup.mk' (F.subgroupOf H))).map
              (QuotientGroup.mk' (F.subgroupOf H)) :=
              (Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) M).symm
          _ = (E.subgroupOf H).map (QuotientGroup.mk' (F.subgroupOf H)) := by rw [hVF]
          _ = chiefQuot (E.subgroupOf H) (F.subgroupOf H) := rfl
      have hWm_top : Wm = ⊤ := by
        rw [eq_top_iff]
        intro x _
        have hxM : (↑x : ↥H ⧸ F.subgroupOf H) ∈ M := by
          rw [hMtop]
          exact x.2
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.1 hxM
        have hyx' : y = x := Subtype.ext hyx
        rwa [hyx'] at hy
      rw [eq_top_iff]
      intro w _
      rw [← ofMul_toMul w]
      exact (hWm _).mp (by rw [hWm_top]; exact Subgroup.mem_top _)
  have hι_kerρ : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ centralizerQuot H E F := by
    intro h
    constructor
    · intro h1
      rw [mem_centralizerQuot]
      refine ⟨h.2, hFn h.2, fun e he => ?_⟩
      have hconj : (h : G) * e * (h : G)⁻¹ ∈ E :=
        ((Subgroup.mem_normalizer_iff.1 (hEn h.2)) e).1 he
      have hfix : ρ h (ι e) = ι e := by rw [h1]; rfl
      rw [hι_equiv h e he] at hfix
      have hcomm : (h : G) * e * ↑(h⁻¹) = ⁅(h : G), e⁆ * e := by
        change (h : G) * e * (h : G)⁻¹ = ⁅(h : G), e⁆ * e
        rw [commutatorElement_def]
        group
      rw [hcomm] at hfix
      have hcommE : ⁅(h : G), e⁆ ∈ E := by
        have hce : ⁅(h : G), e⁆ = ((h : G) * e * (h : G)⁻¹) * e⁻¹ := by
          simp only [commutatorElement_def]
        rw [hce]
        exact E.mul_mem hconj (E.inv_mem he)
      have hadd := hι_add ⁅(h : G), e⁆ hcommE e he
      have h3 : ι ⁅(h : G), e⁆ = 0 := by
        have h2 : ι ⁅(h : G), e⁆ + ι e = ι e := by rw [← hadd]; exact hfix
        have h4 := congrArg (fun x => x - ι e) h2
        simpa using h4
      exact (hι_ker ⁅(h : G), e⁆ hcommE).1 h3
    · intro hmem
      rw [mem_centralizerQuot] at hmem
      obtain ⟨-, -, hcommF⟩ := hmem
      apply LinearEquiv.ext
      intro w
      obtain ⟨e, he, rfl⟩ := hι_surj w
      show ρ h (ι e) = ι e
      rw [hι_equiv h e he]
      have hcomm : (h : G) * e * ↑(h⁻¹) = ⁅(h : G), e⁆ * e := by
        change (h : G) * e * (h : G)⁻¹ = ⁅(h : G), e⁆ * e
        rw [commutatorElement_def]
        group
      have hcommE : ⁅(h : G), e⁆ ∈ E := by
        have hce : ⁅(h : G), e⁆ = ((h : G) * e * (h : G)⁻¹) * e⁻¹ := by
          simp only [commutatorElement_def]
        rw [hce]
        exact E.mul_mem (((Subgroup.mem_normalizer_iff.1 (hEn h.2)) e).1 he) (E.inv_mem he)
      rw [hcomm, hι_add ⁅(h : G), e⁆ hcommE e he,
        (hι_ker ⁅(h : G), e⁆ hcommE).2 (hcommF e he), zero_add]
  have hι_O2 : ∀ n : ↥H, (n : G) ∈ pCoreOf 2 H → ρ n = 1 := by
    intro n hn
    have hnP : n ∈ pCore 2 ↥H := by
      obtain ⟨y, hy, hyeq⟩ := Subgroup.mem_map.1 hn
      have hy' : y = n := Subtype.ext hyeq
      rwa [hy'] at hy
    have hPnorm : ((pCore 2 ↥H).map ρ.rangeRestrict).Normal :=
      Subgroup.Normal.map (CFSG.pCore_normal (p := 2) (G := ↥H)) ρ.rangeRestrict
        ρ.rangeRestrict_surjective
    have hPp : IsPGroup 2 ((pCore 2 ↥H).map ρ.rangeRestrict) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map ρ.rangeRestrict
    have hle : (pCore 2 ↥H).map ρ.rangeRestrict ≤ pCore 2 ρ.range :=
      le_pCore_of_normal_isPGroup hPnorm hPp
    have hbot : pCore 2 ρ.range = ⊥ :=
      pCore_range_eq_bot_of_irreducible_aux ρ hcard hd hι_irr
    have hmem : ρ.rangeRestrict n ∈ (pCore 2 ↥H).map ρ.rangeRestrict := ⟨n, hnP, rfl⟩
    have h1 : ρ.rangeRestrict n = 1 := by
      have := hle hmem
      rwa [hbot, Subgroup.mem_bot] at this
    exact congrArg Subtype.val h1
  exact ⟨Additive (chiefQuot (E.subgroupOf H) (F.subgroupOf H)), inferInstance, inferInstance,
    inferInstance, ρ, ι, hι_add, hι_surj, hι_ker, hι_equiv, hι_irr, hι_kerρ, hι_O2⟩

end CFSG.LocalAnalysis.WeakClosure81

end
