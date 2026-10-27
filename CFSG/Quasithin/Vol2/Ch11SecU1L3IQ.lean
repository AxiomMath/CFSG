module

public import CFSG.Quasithin.Vol2.Ch11SecU1L3IK
public import CFSG.Goldschmidt.Steps.Rank2List

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecU1.L3I

open Matrix CFSG.Quasithin.E2P.Asc80
open scoped MatrixGroups commutatorElement

variable {p : ℕ} [Fact p.Prime]

theorem zc_eq_mk_negDiagSL :
    zc p = QuotientGroup.mk' (Subgroup.center SL(3, ZMod p))
      (CFSG.Goldschmidt.Rank2List.negDiagSL (F := ZMod p)) := by
  show piL p (zt p) = _
  congr 1
  apply Subtype.ext
  rw [coe_zt]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [CFSG.Goldschmidt.Rank2List.negDiagSL, CFSG.Goldschmidt.Rank2List.negDiagMat]

theorem isConj_zc (hp2 : p ≠ 2) {t : PSL3 p} (ht : orderOf t = 2) : IsConj t (zc p) := by
  rw [zc_eq_mk_negDiagSL]
  exact CFSG.Goldschmidt.Rank2List.psl3_isConj (by
    rw [Nat.card_zmod]
    exact (Fact.out : p.Prime).odd_of_ne_two hp2) ht

theorem exists_equiv_zc (hp2 : p ≠ 2) {G : Type} [Group G] {L : Subgroup G} (e : ↥L ≃* PSL3 p)
    {y : G} (hyL : y ∈ L) (hy2 : orderOf y = 2) :
    ∃ e' : ↥L ≃* PSL3 p, e' ⟨y, hyL⟩ = zc p := by
  have ht : orderOf (e ⟨y, hyL⟩) = 2 := by
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hy2]
  obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_zc hp2 ht)
  exact ⟨e.trans (MulAut.conj g), by simpa [MulAut.conj_apply] using hg⟩

omit [Fact p.Prime] in
theorem mem_normalizer_commutator {G : Type} [Group G] {K : Subgroup G} {n : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) :
    n ∈ Subgroup.normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := by
  have key : ∀ m ∈ Subgroup.normalizer (K : Set G), ∀ g ∈ ⁅K, K⁆, m * g * m⁻¹ ∈ ⁅K, K⁆ := by
    intro m hm g hg
    have hle : ⁅K, K⁆ ≤ (⁅K, K⁆ : Subgroup G).comap (MulAut.conj m).toMonoidHom := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      show (MulAut.conj m) ⁅a, b⁆ ∈ ⁅K, K⁆
      rw [map_commutatorElement]
      exact Subgroup.commutator_mem_commutator ((Subgroup.mem_normalizer_iff.mp hm a).mp ha)
        ((Subgroup.mem_normalizer_iff.mp hm b).mp hb)
    exact hle hg
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key n hn g, fun hg => ?_⟩
  have := key n⁻¹ (Subgroup.inv_mem _ hn) _ hg
  simpa [mul_assoc] using this

theorem inf_centralizer_eq_map_leviC (hp2 : p ≠ 2) {G : Type} [Group G] {L : Subgroup G}
    (e' : ↥L ≃* PSL3 p) {y : G} (hyL : y ∈ L) (he' : e' ⟨y, hyL⟩ = zc p) :
    L ⊓ Subgroup.centralizer ({y} : Set G) =
      (leviC p).map (L.subtype.comp e'.symm.toMonoidHom) := by
  set f : PSL3 p →* G := L.subtype.comp e'.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := L.subtype_injective.comp e'.symm.injective
  have hfz : f (zc p) = y := by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he', MulEquiv.symm_apply_apply]
    rfl
  have hfe : ∀ (x : G) (hx : x ∈ L), f (e' ⟨x, hx⟩) = x := fun x hx => by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  ext x
  constructor
  · rintro ⟨hxL, hxy⟩
    have h1 : x * f (zc p) = f (zc p) * x := by
      rw [hfz]
      exact (Subgroup.mem_centralizer_singleton_iff.mp hxy)
    have h2 : e' ⟨x, hxL⟩ * zc p = zc p * e' ⟨x, hxL⟩ := by
      apply hfinj
      rw [map_mul, map_mul, hfe x hxL]
      exact h1
    exact ⟨e' ⟨x, hxL⟩, mem_leviC_of_commute_z hp2 h2, hfe x hxL⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨(e'.symm c).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [← hfz, ← map_mul, ← map_mul, zc_comm_levi hc]

theorem exists_levi_data_L3 (hp5 : 5 ≤ p) (hp4 : p % 4 = 3) {G : Type} [Group G]
    {L : Subgroup G} [L.Normal] (e : ↥L ≃* PSL3 p) {y : G} (hyL : y ∈ L)
    (hy2 : orderOf y = 2) :
    ∃ Y : Subgroup G, Y ≤ L ∧ Y ≤ Subgroup.centralizer ({y} : Set G) ∧
      Subgroup.centralizer ({y} : Set G) ≤ Subgroup.normalizer (Y : Set G) ∧
      Nonempty (↥Y ≃* SL(2, ZMod p)) ∧
      Group.IsSolvable ↥(L ⊓ Subgroup.centralizer (Y : Set G)) ∧
      ∀ x ∈ L, orderOf x = 2 → x * y = y * x → x ≠ y →
        ∀ s ∈ Y, ∀ c ∈ L ⊓ Subgroup.centralizer (Y : Set G), x ≠ s * c := by
  have hp2 : p ≠ 2 := by omega
  obtain ⟨e', he'⟩ := exists_equiv_zc hp2 e hyL hy2
  set f : PSL3 p →* G := L.subtype.comp e'.symm.toMonoidHom with hf
  have hfinj : Function.Injective f := L.subtype_injective.comp e'.symm.injective
  have hfz : f (zc p) = y := by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← he', MulEquiv.symm_apply_apply]
    rfl
  have hfL : ∀ c, f c ∈ L := fun c => (e'.symm c).2
  have hfe : ∀ (x : G) (hx : x ∈ L), f (e' ⟨x, hx⟩) = x := fun x hx => by
    rw [hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.symm_apply_apply]
    rfl
  have hcomm_f : ∀ (x : G) (hx : x ∈ L) (c : PSL3 p),
      x * f c = f c * x ↔ e' ⟨x, hx⟩ * c = c * e' ⟨x, hx⟩ := by
    intro x hx c
    constructor
    · intro h
      apply hfinj
      rw [map_mul, map_mul, hfe x hx]
      exact h
    · intro h
      have h1 := congrArg f h
      rwa [map_mul, map_mul, hfe x hx] at h1
  have hCL : L ⊓ Subgroup.centralizer ({y} : Set G) = (leviC p).map f :=
    inf_centralizer_eq_map_leviC hp2 e' hyL he'
  set Y : Subgroup G := (leviY p).map f with hY
  have hYcomm : Y = ⁅L ⊓ Subgroup.centralizer ({y} : Set G),
      L ⊓ Subgroup.centralizer ({y} : Set G)⁆ := by
    rw [hCL, ← Subgroup.map_commutator, commutator_leviC hp5]
  have hYC0 : Y ≤ L ⊓ Subgroup.centralizer ({y} : Set G) := by
    rw [hCL]
    exact Subgroup.map_mono leviY_le_leviC
  have hCY : L ⊓ Subgroup.centralizer (Y : Set G) =
      (Subgroup.centralizer (leviY p : Set (PSL3 p))).map f := by
    ext x
    constructor
    · rintro ⟨hxL, hxY⟩
      refine ⟨e' ⟨x, hxL⟩, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_, hfe x hxL⟩
      have h1 := Subgroup.mem_centralizer_iff.mp hxY (f s) ⟨s, hs, rfl⟩
      exact ((hcomm_f x hxL s).mp h1.symm).symm
    · rintro ⟨c, hc, rfl⟩
      refine ⟨hfL c, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨s, hs, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hc s hs]
  refine ⟨Y, hYC0.trans inf_le_left, hYC0.trans inf_le_right, fun n hn => ?_, ?_, ?_,
    fun x hxL hx2 hxy hxne s hs c hc hxsc => ?_⟩
  ·
    rw [hYcomm]
    refine mem_normalizer_commutator ?_
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have hgy : ∀ m ∈ Subgroup.centralizer ({y} : Set G), ∀ g ∈
        L ⊓ Subgroup.centralizer ({y} : Set G), m * g * m⁻¹ ∈
          L ⊓ Subgroup.centralizer ({y} : Set G) := by
      rintro m hm g ⟨hgL, hgy⟩
      exact ⟨(inferInstance : L.Normal).conj_mem g hgL m,
        Subgroup.mul_mem _ (Subgroup.mul_mem _ hm hgy) (Subgroup.inv_mem _ hm)⟩
    refine ⟨hgy n hn g, fun h => ?_⟩
    have := hgy n⁻¹ (Subgroup.inv_mem _ hn) _ h
    simpa [mul_assoc] using this
  ·
    have hrange : Y = (f.comp (ofSL2 p)).range := by rw [hY, MonoidHom.range_comp]; rfl
    have hinj : Function.Injective (f.comp (ofSL2 p)) := hfinj.comp (ofSL2_injective (p := p))
    exact ⟨(MulEquiv.subgroupCongr hrange).trans (MonoidHom.ofInjective hinj).symm⟩
  ·
    refine Group.isSolvable_of_comm fun a b => Subtype.ext ?_
    have ha : (a : G) ∈ (Subgroup.centralizer (leviY p : Set (PSL3 p))).map f := by
      rw [← hCY]
      exact a.2
    have hb : (b : G) ∈ (Subgroup.centralizer (leviY p : Set (PSL3 p))).map f := by
      rw [← hCY]
      exact b.2
    obtain ⟨c, hc, hca⟩ := ha
    obtain ⟨d, hd, hdb⟩ := hb
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hca, ← hdb, ← map_mul, ← map_mul,
      centralizer_leviY_comm hp2 hc hd]
  ·
    obtain ⟨s₀, hs₀, rfl⟩ := hs
    rw [hCY] at hc
    obtain ⟨c₀, hc₀, rfl⟩ := hc
    have hx2' : orderOf (e' ⟨x, hxL⟩) = 2 := by
      rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk, hx2]
    have hxz : e' ⟨x, hxL⟩ ≠ zc p := fun h => hxne (by
      rw [← hfe x hxL, h, hfz])
    refine ne_mul_of_leviY hp4 hx2' hxz hs₀ hc₀ (hfinj ?_)
    rw [hfe x hxL, map_mul]
    exact hxsc

end CFSG.Quasithin.Vol2.Ch11.SecU1.L3I
