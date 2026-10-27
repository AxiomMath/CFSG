module

public import CFSG.RankThree.PartOne.S12.LinAlg
public import CFSG.RankThree.PartOne.S12.InputsLinear
public import CFSG.RankThree.PartOne.S12.BaseNodes
import CFSG.RankThree.PartOne.S12.RowFacts
import CFSG.RankThree.PartOne.S12.Sec126a
import CFSG.RankThree.PartOne.S12.Sec12Three

public section

namespace CFSG.RankThree.PartOne

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

namespace Sec127

theorem torusImage_le_torusWeyl (E Y : Subgroup G) : torusImage E Y ≤ torusWeyl E := by
  rw [torusImage, torusWeyl, MonoidHom.range_eq_map]
  exact Subgroup.map_mono le_top

theorem mem_cNormalizer_of_conj_mem [Finite G] {c w : G}
    (h : w * c * w⁻¹ ∈ Subgroup.zpowers c) : w ∈ cNormalizer c := by
  have hmaps : ∀ y ∈ Subgroup.zpowers c, w * y * w⁻¹ ∈ Subgroup.zpowers c := by
    intro y hy
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    rw [← conj_zpow]
    exact Subgroup.zpow_mem _ h j
  have hinj : Function.Injective (fun y : Subgroup.zpowers c =>
      (⟨w * y * w⁻¹, hmaps y y.2⟩ : Subgroup.zpowers c)) := by
    intro a b hab
    apply Subtype.ext
    simpa using congrArg Subtype.val hab
  have hsurj := Finite.injective_iff_surjective.mp hinj
  rw [cNormalizer, Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => hmaps x hx, fun hx => ?_⟩
  obtain ⟨y, hy⟩ := hsurj ⟨w * x * w⁻¹, hx⟩
  have hyx : (y : G) = x := by
    simpa using congrArg Subtype.val hy
  rw [← hyx]
  exact y.2

section Coordinates

variable {p : ℕ} [Fact p.Prime] {n : ℕ} {E : Subgroup G}
  (f : Multiplicative (Fin n → ZMod p) ≃* E)

theorem mem_weyl_map_iff (g : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) :
    g ∈ (torusWeyl E).map (LinAlg.coordHom f) ↔
      ∃ x : Subgroup.normalizer (E : Set G), LinAlg.wAction f x = g := by
  rw [← LinAlg.range_wAction f, MonoidHom.mem_range]

theorem mem_torusImage_map_iff (Y : Subgroup G)
    (g : (Fin n → ZMod p) ≃ₗ[ZMod p] (Fin n → ZMod p)) :
    g ∈ (torusImage E Y).map (LinAlg.coordHom f) ↔
      ∃ x : Subgroup.normalizer (E : Set G), (x : G) ∈ Y ∧ LinAlg.wAction f x = g := by
  constructor
  · intro h
    obtain ⟨φ, hφ, rfl⟩ := Subgroup.mem_map.mp h
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hφ
    exact ⟨x, hx, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hx)

theorem exists_vec {c : G} (hc : c ∈ E) :
    ∃ v : Fin n → ZMod p, ((f (Multiplicative.ofAdd v) : E) : G) = c :=
  ⟨Multiplicative.toAdd (f.symm ⟨c, hc⟩), by rw [ofAdd_toAdd, MulEquiv.apply_symm_apply]⟩

theorem vec_ne_zero {c : G} (hc1 : c ≠ 1) {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) : v ≠ 0 := by
  rintro rfl
  apply hc1
  rw [← hv]
  simp

theorem bsub_zpowers_eq_span {c : G} {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) :
    LinAlg.bsub f (Subgroup.zpowers c) = Submodule.span (ZMod p) {v} := by
  ext x
  rw [LinAlg.mem_bsub, Submodule.mem_span_singleton]
  constructor
  · intro hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
    refine ⟨(k : ZMod p), ?_⟩
    have h1 : f (Multiplicative.ofAdd ((k : ZMod p) • v)) = f (Multiplicative.ofAdd x) := by
      apply Subtype.ext
      rw [Int.cast_smul_eq_zsmul, ofAdd_zsmul, map_zpow, Subgroup.coe_zpow, hv]
      exact hk
    exact Multiplicative.ofAdd.injective (f.injective h1)
  · rintro ⟨a, rfl⟩
    rw [← ZMod.natCast_zmod_val a, Nat.cast_smul_eq_nsmul, ofAdd_nsmul, map_pow,
      Subgroup.coe_pow, hv]
    exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) _

theorem bsub_inf (B₁ B₂ : Subgroup G) :
    LinAlg.bsub f (B₁ ⊓ B₂) = LinAlg.bsub f B₁ ⊓ LinAlg.bsub f B₂ := by
  ext v
  rw [Submodule.mem_inf, LinAlg.mem_bsub, LinAlg.mem_bsub, LinAlg.mem_bsub, Subgroup.mem_inf]

theorem bsub_sup {B₁ B₂ : Subgroup G} (h₁ : B₁ ≤ E) (h₂ : B₂ ≤ E) :
    LinAlg.bsub f (B₁ ⊔ B₂) = LinAlg.bsub f B₁ ⊔ LinAlg.bsub f B₂ := by
  apply le_antisymm
  · obtain ⟨B₃, h₃, h₃eq⟩ := LinAlg.exists_bsub_eq f (LinAlg.bsub f B₁ ⊔ LinAlg.bsub f B₂)
    have h13 : B₁ ≤ B₃ :=
      (LinAlg.bsub_le_bsub_iff f h₁ h₃).mp (le_sup_left.trans_eq h₃eq.symm)
    have h23 : B₂ ≤ B₃ :=
      (LinAlg.bsub_le_bsub_iff f h₂ h₃).mp (le_sup_right.trans_eq h₃eq.symm)
    exact ((LinAlg.bsub_le_bsub_iff f (sup_le h₁ h₂) h₃).mpr (sup_le h13 h23)).trans_eq h₃eq
  · exact sup_le ((LinAlg.bsub_le_bsub_iff f h₁ (sup_le h₁ h₂)).mpr le_sup_left)
      ((LinAlg.bsub_le_bsub_iff f h₂ (sup_le h₁ h₂)).mpr le_sup_right)

theorem finrank_bsub_add_one {c : G} {B : Subgroup G} {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) (hv0 : v ≠ 0)
    (hcE : Subgroup.zpowers c ≤ E) (hBE : B ≤ E)
    (hsup : E = Subgroup.zpowers c ⊔ B) (hinf : Subgroup.zpowers c ⊓ B = ⊥) :
    Module.finrank (ZMod p) (LinAlg.bsub f B) + 1 = n := by
  have hcompl : IsCompl (LinAlg.bsub f (Subgroup.zpowers c)) (LinAlg.bsub f B) := by
    refine ⟨?_, ?_⟩
    · rw [disjoint_iff, ← bsub_inf, hinf, LinAlg.bsub_bot]
    · rw [codisjoint_iff, ← bsub_sup f hcE hBE, ← hsup, LinAlg.bsub_self]
  have h := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [bsub_zpowers_eq_span f hv, finrank_span_singleton hv0, Module.finrank_fin_fun] at h
  omega

theorem wAction_vec (x : Subgroup.normalizer (E : Set G)) {c : G} {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) :
    ((f (Multiplicative.ofAdd (LinAlg.wAction f x v)) : E) : G) = (x : G) * c * (x : G)⁻¹ := by
  rw [LinAlg.wAction_apply, hv]

theorem mem_cNormalizer_of_stabilizes [Finite G] {c : G} {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) (x : Subgroup.normalizer (E : Set G))
    (hx : LinAlg.wAction f x v ∈ Submodule.span (ZMod p) {v}) : (x : G) ∈ cNormalizer c := by
  apply mem_cNormalizer_of_conj_mem
  rw [← bsub_zpowers_eq_span f hv, LinAlg.mem_bsub, wAction_vec f x hv] at hx
  exact hx

theorem wAction_fixes_vec {c : G} {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) (x : Subgroup.normalizer (E : Set G))
    (hxc : c * (x : G) = (x : G) * c) : LinAlg.wAction f x v = v := by
  apply Multiplicative.ofAdd.injective
  apply f.injective
  apply Subtype.ext
  rw [wAction_vec f x hv, hv, ← hxc, mul_inv_cancel_right]

theorem irreducible_map (hirr : torusIrreducible E) :
    ∀ U : Submodule (ZMod p) (Fin n → ZMod p),
      (∀ g ∈ (torusWeyl E).map (LinAlg.coordHom f), ∀ x ∈ U, g x ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro U hU
  obtain ⟨B, hBE, rfl⟩ := LinAlg.exists_bsub_eq f U
  have hinv : torusInvariant E ⊤ B := by
    rw [LinAlg.torusInvariant_top_iff f hBE]
    intro φ hφ y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    exact hU _ (Subgroup.mem_map_of_mem _ hφ) z hz
  rcases hirr B hBE hinv with rfl | rfl
  · exact Or.inl (LinAlg.bsub_bot f)
  · exact Or.inr (LinAlg.bsub_self f)

theorem pCore_map_eq_bot {Y : Subgroup (MulAut E)} (h : CFSG.pCore p ↥Y = ⊥) :
    CFSG.pCore p ↥(Y.map (LinAlg.coordHom f)) = ⊥ :=
  (LinAlg.pCore_eq_bot_iff_of_mulEquiv p
    (Subgroup.equivMapOfInjective Y (LinAlg.coordHom f) (LinAlg.coordHom_injective f))).mp h

theorem exists_transvection_map (htv : torusHasTransvection p E) :
    ∃ t ∈ (torusWeyl E).map (LinAlg.coordHom f), IsTransvectionLin t := by
  obtain ⟨φ, hφ, ht⟩ := htv
  exact ⟨LinAlg.coordHom f φ, Subgroup.mem_map_of_mem _ hφ,
    (LinAlg.isAutTransvection_iff_of_rank f φ).mp ht⟩

theorem not_stabilizes {c : G} {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) (hcE : c ∈ E)
    (h125 : ¬ torusNormalizer E ≤ cNormalizer c) :
    ¬ ∀ g ∈ (torusWeyl E).map (LinAlg.coordHom f), g v ∈ Submodule.span (ZMod p) {v} := by
  intro hall
  apply h125
  apply torusNormalizer_le_cNormalizer_of_invariant
  rw [LinAlg.torusInvariant_top_iff f (Subgroup.zpowers_le.mpr hcE), bsub_zpowers_eq_span f hv]
  intro φ hφ
  refine (Submodule.map_span_le _ _ _).mpr ?_
  intro m hm
  rw [Set.mem_singleton_iff] at hm
  rw [hm]
  exact hall _ (Subgroup.mem_map_of_mem _ hφ)

theorem normalizes_map [Finite G] {c : G} {L : Subgroup G} {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c)
    (h122b : cNormalizer c ⊓ torusNormalizer E ≤ Subgroup.normalizer (L : Set G)) :
    ∀ g ∈ (torusWeyl E).map (LinAlg.coordHom f), g v ∈ Submodule.span (ZMod p) {v} →
      ∀ l ∈ (torusImage E L).map (LinAlg.coordHom f),
        g * l * g⁻¹ ∈ (torusImage E L).map (LinAlg.coordHom f) := by
  intro g hg hgv l hl
  obtain ⟨w, rfl⟩ := (mem_weyl_map_iff f g).mp hg
  obtain ⟨x, hxL, rfl⟩ := (mem_torusImage_map_iff f L l).mp hl
  have hwH : (w : G) ∈ cNormalizer c := mem_cNormalizer_of_stabilizes f hv w hgv
  have hwL : (w : G) ∈ Subgroup.normalizer (L : Set G) := h122b ⟨hwH, w.2⟩
  have hconj : LinAlg.wAction f w * LinAlg.wAction f x * (LinAlg.wAction f w)⁻¹ =
      LinAlg.wAction f (w * x * w⁻¹) := by simp
  rw [hconj]
  refine (mem_torusImage_map_iff f L _).mpr ⟨w * x * w⁻¹, ?_, rfl⟩
  have := (Subgroup.mem_normalizer_iff.mp hwL (x : G)).mp hxL
  simpa using this

theorem fixes_of_mem_map {c : G} {L : Subgroup G} {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) (hcomm : ∀ l ∈ L, c * l = l * c) :
    ∀ l ∈ (torusImage E L).map (LinAlg.coordHom f), l v = v := by
  intro l hl
  obtain ⟨x, hxL, rfl⟩ := (mem_torusImage_map_iff f L l).mp hl
  exact wAction_fixes_vec f hv x (hcomm _ hxL)

theorem invariant_subspace_cases [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec12Hyp G p A c L E) (h124 : Node124) {v : Fin n → ZMod p}
    (hv : ((f (Multiplicative.ofAdd v) : E) : G) = c) (hv0 : v ≠ 0)
    (U : Submodule (ZMod p) (Fin n → ZMod p))
    (hU : ∀ l ∈ (torusImage E L).map (LinAlg.coordHom f), ∀ x ∈ U, l x ∈ U)
    (hU0 : U ≠ ⊥) (hU1 : U ≠ ⊤) :
    U = Submodule.span (ZMod p) {v} ∨
      Module.finrank (ZMod p) U + 1 = Module.finrank (ZMod p) (Fin n → ZMod p) := by
  obtain ⟨B, hBE, rfl⟩ := LinAlg.exists_bsub_eq f U
  have hinv : torusInvariant E L B := by
    rw [LinAlg.torusInvariant_iff f L hBE]
    intro φ hφ y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    exact hU _ (Subgroup.mem_map_of_mem _ hφ) z hz
  have hB0 : B ≠ ⊥ := by
    rintro rfl
    exact hU0 (LinAlg.bsub_bot f)
  have hBE' : B ≠ E := by
    rintro rfl
    exact hU1 (LinAlg.bsub_self f)
  have hcE : Subgroup.zpowers c ≤ E :=
    Subgroup.zpowers_le.mpr (hv ▸ (f (Multiplicative.ofAdd v)).2)
  obtain ⟨h1, h2⟩ := h124 G p A c L E h
  rcases h1 B hBE hinv hB0 hBE' with rfl | rfl
  · exact Or.inl (bsub_zpowers_eq_span f hv)
  · rcases h2 with ⟨hsup, hinf⟩ | ⟨-, hEE⟩
    · right
      rw [Module.finrank_fin_fun]
      exact finrank_bsub_add_one f hv hv0 hcE hBE hsup hinf
    · exact absurd hEE hBE'

include f in
theorem node127_core [Finite G] (hKF : KF127) {A L : Subgroup G} {c : G}
    (h : Sec12Hyp G p A c L E) (h122b : Node122b) (h124 : Node124) (h125 : Node125)
    (hirr : torusIrreducible E) (hcore : CFSG.pCore p ↥(torusWeyl E) = ⊥)
    (htv : torusHasTransvection p E) (hn : n = 3 ∨ n = 4)
    {r : ℕ} (hr1 : 1 ≤ r) (hr12 : r ≤ 12) (hweyl : RowWeylIso E (torusImage E L) r) : False := by
  have h5 : 5 ≤ p := Sec12Three.five_le h
  have hcE : c ∈ E := h.A_le_E h.c_mem
  obtain ⟨v, hv⟩ := exists_vec f hcE
  have hv0 : v ≠ 0 := vec_ne_zero f h.c_ne_one hv
  have hdim : Module.finrank (ZMod p) (Fin n → ZMod p) = 3 ∨
      Module.finrank (ZMod p) (Fin n → ZMod p) = 4 := by
    rwa [Module.finrank_fin_fun]
  have key := hKF p h5 (Fin n → ZMod p) hdim ((torusWeyl E).map (LinAlg.coordHom f))
    (irreducible_map f hirr) (pCore_map_eq_bot f hcore) (exists_transvection_map f htv) v hv0
    (not_stabilizes f hv hcE (h125 G p A c L E h))
    ((torusImage E L).map (LinAlg.coordHom f))
    (Subgroup.map_mono (torusImage_le_torusWeyl E L))
    (normalizes_map f hv (h122b G p A c L E h))
    (fixes_of_mem_map f hv (Sec12Three.comm_c_L h))
    (pCore_map_eq_bot f (rowWeylIso_pCore_eq_bot hr1 hr12 hweyl h.prime h5))
    (fun U hU hU0 hU1 => invariant_subspace_cases f h h124 hv hv0 U hU hU0 hU1)
  obtain ⟨a, b, hab⟩ := rowWeylIso_nonabelian hr1 hr12 hweyl
  apply hab
  apply Subtype.ext
  apply LinAlg.coordHom_injective f
  have h' := key (LinAlg.coordHom f a) (Subgroup.mem_map_of_mem _ a.2)
    (LinAlg.coordHom f b) (Subgroup.mem_map_of_mem _ b.2)
  rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
  exact h'

end Coordinates

end Sec127

theorem node127_of_inputs (h122b : Node122b) (h123 : Node123) (h124 : Node124)
    (h125 : Node125) (h126 : Node126) (hKF : KF127) : Node127 := by
  intro G _ _ p A c L E h hT htv
  by_contra hne
  have hcore : CFSG.pCore p ↥(torusWeyl E) = ⊥ := by
    by_contra hcore
    exact hne hcore
  have hirr : torusIrreducible E := by
    rcases h126 G p A c L E h with hirr | hP | hfive
    · exact hirr
    · exact absurd hP hne
    · exact absurd hfive hT
  obtain ⟨-, r, hr1, hr12, -, hweyl, hr8, hr9⟩ := h123 G p A c L E h
  have hpf : Fact p.Prime := ⟨h.prime⟩
  have hel := h.E_elem
  by_cases hr : r ≤ 8
  · have hcard : Nat.card E = p ^ 3 := by
      rw [hr8 hr]
      exact h.A_card
    obtain ⟨f⟩ := LinAlg.exists_coords E hcard
    exact Sec127.node127_core f hKF h h122b h124 h125 hirr hcore htv (Or.inl rfl) hr1 hr12 hweyl
  · have hcard : Nat.card E = p ^ 4 := hr9 (by omega)
    obtain ⟨f⟩ := LinAlg.exists_coords E hcard
    exact Sec127.node127_core f hKF h h122b h124 h125 hirr hcore htv (Or.inr rfl) hr1 hr12 hweyl

end CFSG.RankThree.PartOne
