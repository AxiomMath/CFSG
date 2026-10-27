module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K147L2N
public import CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp.Surv15

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair

open Subgroup CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.QuasithinUnique.Setup.X7b
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
  (slRingEquiv two_mul_le_finrank_of_ne_one)
open scoped MatrixGroups

section Group

variable {G : Type} [Group G]

theorem map_conj_mul (K : Subgroup G) (g h : G) :
    K.map (MulAut.conj (g * h)).toMonoidHom =
      (K.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

theorem map_conj_one (K : Subgroup G) : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
  ext x
  simp

structure IsPair (L L₂ : Subgroup G) : Prop where
  ne : L ≠ L₂
  ex : ∃ g : G, L.map (MulAut.conj g).toMonoidHom = L₂
  conj : ∀ g : G,
    (L.map (MulAut.conj g).toMonoidHom = L ∧ L₂.map (MulAut.conj g).toMonoidHom = L₂) ∨
      (L.map (MulAut.conj g).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj g).toMonoidHom = L)

theorem exists_isPair [Finite G] {L : Subgroup G}
    (h : CFSG.LocalAnalysis.UniquenessCase.UC22.F05.numConj L = 2) :
    ∃ g : G, IsPair L (L.map (MulAut.conj g).toMonoidHom) := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.F05.numConj at h
  obtain ⟨A, B, hAB, hs⟩ := Set.ncard_eq_two.mp h
  have hmem : ∀ g : G, L.map (MulAut.conj g).toMonoidHom = A ∨
      L.map (MulAut.conj g).toMonoidHom = B := by
    intro g
    have : L.map (MulAut.conj g).toMonoidHom ∈
        {K : Subgroup G | ∃ g : G, K = L.map (MulAut.conj g).toMonoidHom} := ⟨g, rfl⟩
    rw [hs] at this
    simpa using this
  have hA : A ∈ {K : Subgroup G | ∃ g : G, K = L.map (MulAut.conj g).toMonoidHom} := by
    rw [hs]
    exact Set.mem_insert A {B}
  have hB : B ∈ {K : Subgroup G | ∃ g : G, K = L.map (MulAut.conj g).toMonoidHom} := by
    rw [hs]
    exact Set.mem_insert_of_mem A rfl
  obtain ⟨a, rfl⟩ := hA
  obtain ⟨b, rfl⟩ := hB
  obtain ⟨g₀, hg₀, hall⟩ : ∃ g₀ : G, L ≠ L.map (MulAut.conj g₀).toMonoidHom ∧
      ∀ g : G, L.map (MulAut.conj g).toMonoidHom = L ∨
        L.map (MulAut.conj g).toMonoidHom = L.map (MulAut.conj g₀).toMonoidHom := by
    rcases hmem 1 with hL | hL <;> rw [map_conj_one] at hL
    · refine ⟨b, fun h => hAB (hL.symm.trans h), fun g => ?_⟩
      rw [← hL] at hmem
      exact hmem g
    · refine ⟨a, fun h => hAB (h.symm.trans hL), fun g => ?_⟩
      rw [← hL] at hmem
      exact (hmem g).symm
  refine ⟨g₀, ⟨hg₀, ⟨g₀, rfl⟩, fun g => ?_⟩⟩
  have hinj : Function.Injective (Subgroup.map (MulAut.conj g).toMonoidHom) :=
    Subgroup.map_injective (MulAut.conj g).injective
  have h2 := hall (g * g₀)
  rw [map_conj_mul] at h2
  rcases hall g with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (hinj (h2.trans h1.symm)).symm hg₀
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (hinj (h2.trans h1.symm)).symm hg₀

namespace IsPair

variable {L L₂ : Subgroup G} (hP : IsPair L L₂)
include hP

theorem symm : IsPair L₂ L := by
  refine ⟨hP.ne.symm, ?_, fun g => (hP.conj g).imp And.symm And.symm⟩
  obtain ⟨g₀, hg₀⟩ := hP.ex
  rcases hP.conj g₀ with ⟨h1, -⟩ | ⟨-, h2⟩
  · exact absurd (h1.symm.trans hg₀) hP.ne
  · exact ⟨g₀, h2⟩

theorem map_conj_of_not_mem {g : G} (hg : g ∉ normalizer (L : Set G)) :
    L.map (MulAut.conj g).toMonoidHom = L₂ ∧ L₂.map (MulAut.conj g).toMonoidHom = L :=
  (hP.conj g).resolve_left fun h => hg (mem_normalizer_iff_map_conj_eq.mpr h.1)

theorem exists_not_mem_normalizer : ∃ g : G, g ∉ normalizer (L : Set G) := by
  obtain ⟨g₀, hg₀⟩ := hP.ex
  exact ⟨g₀, fun hg => hP.ne ((mem_normalizer_iff_map_conj_eq.mp hg).symm.trans hg₀)⟩

theorem conj_mem_of_not_mem {g x : G} (hg : g ∉ normalizer (L : Set G)) (hx : x ∈ L) :
    g * x * g⁻¹ ∈ L₂ := by
  rw [← (hP.map_conj_of_not_mem hg).1]
  exact ⟨x, hx, rfl⟩

theorem map_conj_of_mem {g : G} (hg : g ∈ normalizer (L : Set G)) :
    L.map (MulAut.conj g).toMonoidHom = L ∧ L₂.map (MulAut.conj g).toMonoidHom = L₂ :=
  (hP.conj g).resolve_right fun h =>
    hP.ne ((mem_normalizer_iff_map_conj_eq.mp hg).symm.trans h.1)

theorem mem_normalizer_iff {g : G} :
    g ∈ normalizer (L₂ : Set G) ↔ g ∈ normalizer (L : Set G) := by
  rw [mem_normalizer_iff_map_conj_eq, mem_normalizer_iff_map_conj_eq]
  rcases hP.conj g with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨fun _ => h1, fun _ => h2⟩
  · exact ⟨fun h => absurd (h.symm.trans h2) hP.ne.symm,
      fun h => absurd (h.symm.trans h1) hP.ne⟩

theorem le_normalizer : L ≤ normalizer (L₂ : Set G) := fun _ hx =>
  hP.mem_normalizer_iff.mpr (Subgroup.le_normalizer hx)

theorem inf_eq_bot [Finite G] [IsSimpleGroup ↥L] : L ⊓ L₂ = ⊥ := by
  have hn : ((L ⊓ L₂).subgroupOf L).Normal := by
    refine ⟨fun x hx l => ?_⟩
    rw [mem_subgroupOf] at hx ⊢
    refine ⟨(l * x * l⁻¹).2, ?_⟩
    simp only [coe_mul, coe_inv]
    exact (Subgroup.mem_normalizer_iff.mp (hP.le_normalizer l.2) x).mp hx.2
  haveI := hn
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((L ⊓ L₂).subgroupOf L) with h | h
  · refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : (⟨x, hx.1⟩ : ↥L) ∈ (L ⊓ L₂).subgroupOf L := hx
    rw [h, mem_bot] at hx'
    exact mem_bot.mpr (congrArg Subtype.val hx')
  · exfalso
    have hle : L ≤ L₂ := fun x hx => (subgroupOf_eq_top.mp h hx).2
    obtain ⟨g₀, hg₀⟩ := hP.ex
    have hc : Nat.card ↥L₂ = Nat.card ↥L := by
      rw [← hg₀]
      exact card_map_of_injective (MulAut.conj g₀).injective
    exact hP.ne (eq_of_le_of_card_ge hle hc.le)

theorem commute [Finite G] [IsSimpleGroup ↥L] {x y : G} (hx : x ∈ L) (hy : y ∈ L₂) :
    x * y = y * x := by
  have h1 : x * y * x⁻¹ * y⁻¹ ∈ L := by
    have := (Subgroup.mem_normalizer_iff.mp (hP.symm.le_normalizer hy) x⁻¹).mp (inv_mem hx)
    simpa [mul_assoc] using mul_mem hx this
  have h2 : x * y * x⁻¹ * y⁻¹ ∈ L₂ :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hP.le_normalizer hx) y).mp hy) (inv_mem hy)
  have h3 : x * y * x⁻¹ * y⁻¹ = 1 := by
    have := mem_inf.mpr ⟨h1, h2⟩
    rwa [hP.inf_eq_bot, mem_bot] at this
  calc x * y = x * y * x⁻¹ * y⁻¹ * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

theorem sup_normal : (L ⊔ L₂).Normal := by
  refine ⟨fun x hx g => ?_⟩
  have hmap : (L ⊔ L₂).map (MulAut.conj g).toMonoidHom = L ⊔ L₂ := by
    rw [Subgroup.map_sup]
    rcases hP.conj g with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
    · rw [h1, h2, sup_comm]
  rw [← hmap]
  exact ⟨x, hx, rfl⟩

theorem lgConj_eq : CFSG.LocalAnalysis.UniquenessCase.UC22.Ext.lgConj L = L ⊔ L₂ := by
  unfold CFSG.LocalAnalysis.UniquenessCase.UC22.Ext.lgConj
  apply le_antisymm
  · refine iSup_le fun g => ?_
    rcases hP.conj g with ⟨h1, -⟩ | ⟨h1, -⟩
    · rw [h1]
      exact le_sup_left
    · rw [h1]
      exact le_sup_right
  · obtain ⟨g₀, hg₀⟩ := hP.ex
    refine sup_le ?_ ?_
    · calc L = L.map (MulAut.conj (1 : G)).toMonoidHom := (map_conj_one L).symm
        _ ≤ ⨆ g : G, L.map (MulAut.conj g).toMonoidHom :=
          le_iSup (fun g : G => L.map (MulAut.conj g).toMonoidHom) 1
    · rw [← hg₀]
      exact le_iSup (fun g : G => L.map (MulAut.conj g).toMonoidHom) g₀

theorem nonempty_mulEquiv : Nonempty (↥L₂ ≃* ↥L) := by
  obtain ⟨g₀, hg₀⟩ := hP.ex
  exact ⟨((Subgroup.equivMapOfInjective L (MulAut.conj g₀).toMonoidHom
    (MulAut.conj g₀).injective).trans (MulEquiv.subgroupCongr hg₀)).symm⟩

end IsPair

end Group

section Rep

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

theorem apply_mem_fixSub_map {K : Subgroup G} {v : V} (hv : v ∈ fixSub ρ K) (g : G) :
    ρ g v ∈ fixSub ρ (K.map (MulAut.conj g).toMonoidHom) := by
  rintro _ ⟨k, hk, rfl⟩
  show ρ (g * k * g⁻¹) (ρ g v) = ρ g v
  rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply,
    hv k hk]

variable {ρ} {L L₂ : Subgroup G}

theorem IsPair.apply_mem_inf (hP : IsPair L L₂) (g : G) {v : V}
    (hv : v ∈ fixSub ρ L ⊓ fixSub ρ L₂) : ρ g v ∈ fixSub ρ L ⊓ fixSub ρ L₂ := by
  have h1 := apply_mem_fixSub_map ρ hv.1 g
  have h2 := apply_mem_fixSub_map ρ hv.2 g
  rcases hP.conj g with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at h1
    rw [e2] at h2
    exact ⟨h1, h2⟩
  · rw [e1] at h1
    rw [e2] at h2
    exact ⟨h2, h1⟩

theorem IsPair.apply_mem_sup (hP : IsPair L L₂) (g : G) {v : V}
    (hv : v ∈ fixSub ρ L ⊔ fixSub ρ L₂) : ρ g v ∈ fixSub ρ L ⊔ fixSub ρ L₂ := by
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [map_add]
  have h1 := apply_mem_fixSub_map ρ ha g
  have h2 := apply_mem_fixSub_map ρ hb g
  rcases hP.conj g with ⟨e1, e2⟩ | ⟨e1, e2⟩
  · rw [e1] at h1
    rw [e2] at h2
    exact add_mem (Submodule.mem_sup_left h1) (Submodule.mem_sup_right h2)
  · rw [e1] at h1
    rw [e2] at h2
    exact add_mem (Submodule.mem_sup_right h1) (Submodule.mem_sup_left h2)

theorem IsPair.fixSub_inf_eq_bot (hP : IsPair L L₂) (hirr : ρ.IsIrreducible)
    (hnt : ∃ l ∈ L, ρ l ≠ 1) : fixSub ρ L ⊓ fixSub ρ L₂ = ⊥ := by
  rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2 _
      (fun g v hv => hP.apply_mem_inf g hv) with h | h
  · exact h
  · exfalso
    obtain ⟨l, hl, hne⟩ := hnt
    apply hne
    apply LinearMap.ext
    intro w
    have : w ∈ fixSub ρ L ⊓ fixSub ρ L₂ := h ▸ Submodule.mem_top
    exact this.1 l hl

theorem IsPair.fixSub_sup_eq_top (hP : IsPair L L₂) (hirr : ρ.IsIrreducible)
    (h : fixSub ρ L₂ ≠ ⊥) : fixSub ρ L ⊔ fixSub ρ L₂ = ⊤ := by
  rcases ((CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr).2 _
      (fun g v hv => hP.apply_mem_sup g hv) with h' | h'
  · exfalso
    apply h
    rw [eq_bot_iff, ← h']
    exact le_sup_right
  · exact h'

theorem IsPair.fixSub_eq_bot (hP : IsPair L L₂) (h : fixSub ρ L₂ = ⊥) : fixSub ρ L = ⊥ := by
  obtain ⟨g₀, hg₀⟩ := hP.ex
  refine eq_bot_iff.mpr fun v hv => ?_
  have h1 := apply_mem_fixSub_map ρ hv g₀
  rw [hg₀, h, Submodule.mem_bot] at h1
  rw [Submodule.mem_bot]
  calc v = ρ g₀⁻¹ (ρ g₀ v) := by
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
    _ = 0 := by rw [h1, map_zero]

end Rep

section Bound

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) G V)

theorem two_mul_le_finrank_of_moves {K : Subgroup G} {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : ↥K ≃* SL(2, F)) {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    {Y : Submodule (ZMod 2) V} (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ K Y) (hne : ∃ k ∈ K, ∃ y ∈ Y, ρ k y ≠ y) :
    2 * n ≤ Module.finrank (ZMod 2) Y := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  have h4 : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : IsSimpleGroup SL(2, F) :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.P22y.isSimpleGroup_sl2 h4
  haveI : IsSimpleGroup ↥K := e.isSimpleGroup
  have hper : Group.IsPerfect ↥K := by
    haveI := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card F h4
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  letI : Fintype (GaloisField 2 n) := Fintype.ofFinite _
  have hcard : Fintype.card F = Fintype.card (GaloisField 2 n) := by
    rw [Fintype.card_eq_nat_card, Fintype.card_eq_nat_card, hF, GaloisField.card 2 n (by omega)]
  let eG : ↥K ≃* SL(2, GaloisField 2 n) :=
    e.trans (slRingEquiv (FiniteField.ringEquivOfCardEq hcard))
  let σ : ↥K →* (↥Y ≃ₗ[ZMod 2] ↥Y) :=
    (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) ↥Y).toMonoidHom.comp
      (CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Br.restr ρ hY).asGroupHom
  refine two_mul_le_finrank_of_ne_one hn hper eG σ ?_
  obtain ⟨k, hk, y, hy, hne⟩ := hne
  refine ⟨⟨k, hk⟩, fun h1 => hne ?_⟩
  have h2 := congrArg (fun f : ↥Y ≃ₗ[ZMod 2] ↥Y => ((f ⟨y, hy⟩ : ↥Y) : V)) h1
  simpa [σ, LinearMap.GeneralLinearGroup.coeFn_generalLinearEquiv,
    Representation.asGroupHom_apply] using h2

variable {ρ} {L L₂ : Subgroup G}

theorem IsPair.two_mul_le_finrank (hP : IsPair L L₂) {F : Type} [Field F] [Finite F] [CharP F 2]
    (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hfix : fixSub ρ L ⊓ fixSub ρ L₂ = ⊥) {Y : Submodule (ZMod 2) V}
    (hY : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ (L ⊔ L₂) Y) (h0 : Y ≠ ⊥) : 2 * n ≤ Module.finrank (ZMod 2) Y := by
  obtain ⟨e₂⟩ := hP.nonempty_mulEquiv
  by_cases h1 : ∃ k ∈ L, ∃ y ∈ Y, ρ k y ≠ y
  · exact two_mul_le_finrank_of_moves ρ e hn hF (fun k hk => hY k (mem_sup_left hk)) h1
  by_cases h2 : ∃ k ∈ L₂, ∃ y ∈ Y, ρ k y ≠ y
  · exact two_mul_le_finrank_of_moves ρ (e₂.trans e) hn hF
      (fun k hk => hY k (mem_sup_right hk)) h2
  exfalso
  push Not at h1 h2
  apply h0
  rw [eq_bot_iff, ← hfix]
  exact fun y hy => ⟨fun k hk => h1 k hk y hy, fun k hk => h2 k hk y hy⟩

end Bound

section Disp

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  (ρ : Representation (ZMod 2) G V)

theorem finrank_le_disp {t : G} {Y : Submodule (ZMod 2) V} (hY : ∀ y ∈ Y, ρ t y = y → y = 0) :
    Module.finrank (ZMod 2) Y ≤
      Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) := by
  have hinj : Function.Injective ((ρ t - 1).domRestrict Y) := by
    rw [← LinearMap.ker_eq_bot, eq_bot_iff]
    rintro ⟨w, hw⟩ hw0
    have := LinearMap.mem_ker.mp hw0
    simp only [LinearMap.domRestrict_apply, LinearMap.sub_apply, Module.End.one_apply] at this
    exact (Submodule.mem_bot _).mpr (Subtype.ext (hY w hw (sub_eq_zero.mp this)))
  have h1 := LinearMap.finrank_range_of_inj hinj
  have h2 := Submodule.finrank_mono (LinearMap.range_domRestrict_le_range (ρ t - 1) Y)
  have h3 := LinearMap.finrank_range_add_finrank_ker (ρ t - 1)
  rw [CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm.ker_sub_one_eq_repFixedSpace] at h3
  omega

theorem finrank_repFixedSpace_conj (g t : G) :
    Module.finrank (ZMod 2) (repFixedSpace ρ {g * t * g⁻¹}) =
      Module.finrank (ZMod 2) (repFixedSpace ρ {t}) := by
  have hgg : ∀ v, ρ g (ρ g⁻¹ v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]
  have hinj : Function.Injective (ρ g) := fun v w h => by
    have := congrArg (ρ g⁻¹) h
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at this
  have heq : (repFixedSpace ρ {t}).map (ρ g) = repFixedSpace ρ {g * t * g⁻¹} := by
    ext v
    simp only [Submodule.mem_map, mem_repFixedSpace, Set.mem_singleton_iff, forall_eq]
    constructor
    · rintro ⟨w, hw, rfl⟩
      rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel_right, map_mul, Module.End.mul_apply,
        hw]
    · intro hv
      refine ⟨ρ g⁻¹ v, ?_, hgg v⟩
      calc ρ t (ρ g⁻¹ v) = ρ g⁻¹ (ρ (g * t * g⁻¹) v) := by
            rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
            congr 2
            group
        _ = ρ g⁻¹ v := by rw [hv]
  rw [← heq]
  exact (Submodule.equivMapOfInjective (ρ g) hinj _).symm.finrank_eq

end Disp

section MinInv

variable {G : Type} [Group G] {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  (ρ : Representation (ZMod 2) G V)

@[expose] def IsMinInv (K : Subgroup G) (M : Submodule (ZMod 2) V) : Prop :=
  CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ K M ∧ M ≠ ⊥ ∧ ∀ C ≤ M, CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ K C → C ≠ ⊥ → C = M

theorem exists_isMinInv [Finite V] {K : Subgroup G} {U : Submodule (ZMod 2) V}
    (hU : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ K U) (h0 : U ≠ ⊥) : ∃ M ≤ U, IsMinInv ρ K M := by
  obtain ⟨M, hMU, hM, hM0, hmin⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Norm.exists_min_sub (CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ K) hU h0
  exact ⟨M, hMU, hM, hM0, hmin⟩

variable {ρ}

theorem isInvariant_map {X : Subgroup G} (hX : X.Normal) {M : Submodule (ZMod 2) V}
    (hM : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X M) (g : G) : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X (M.map (ρ g)) := by
  rintro x hx _ ⟨m, hm, rfl⟩
  refine ⟨ρ (g⁻¹ * x * g) m, hM _ (by simpa using hX.conj_mem x hx g⁻¹) m hm, ?_⟩
  show ρ g (ρ (g⁻¹ * x * g) m) = ρ x (ρ g m)
  rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
  congr 2
  group

theorem IsMinInv.map {X : Subgroup G} (hX : X.Normal) {M : Submodule (ZMod 2) V}
    (hM : IsMinInv ρ X M) (g : G) : IsMinInv ρ X (M.map (ρ g)) := by
  have hid : ∀ (h : G) (N : Submodule (ZMod 2) V), (N.map (ρ h)).map (ρ h⁻¹) = N := by
    intro h N
    rw [← Submodule.map_comp, ← Module.End.mul_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    exact Submodule.map_id N
  refine ⟨isInvariant_map hX hM.1 g, fun h => hM.2.1 ?_, fun C hC hCinv hC0 => ?_⟩
  · rw [← hid g M, h, Submodule.map_bot]
  · have hle : C.map (ρ g⁻¹) ≤ M := by
      rw [← hid g M]
      exact Submodule.map_mono hC
    have hne : C.map (ρ g⁻¹) ≠ ⊥ := by
      intro h
      apply hC0
      rw [← hid g⁻¹ C, inv_inv, h, Submodule.map_bot]
    have := hM.2.2 _ hle (isInvariant_map hX hCinv g⁻¹) hne
    have hC' := hid g⁻¹ C
    rw [inv_inv] at hC'
    rw [← hC', this]

theorem IsMinInv.apply_mem [Finite V] {X : Subgroup G} (hX : X.Normal)
    {M : Submodule (ZMod 2) V} (hM : IsMinInv ρ X M) {t : G} (ht : t * t = 1)
    (hd : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) <
      Module.finrank (ZMod 2) M) {m : V} (hm : m ∈ M) : ρ t m ∈ M := by
  have htt : ∀ v, ρ t (ρ t v) = v := fun v => by
    rw [← Module.End.mul_apply, ← map_mul, ht, map_one, Module.End.one_apply]
  have hMt := hM.map hX t
  have hinv : CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF.IsInvariant ρ X (M ⊓ M.map (ρ t)) := fun x hx v hv =>
    ⟨hM.1 x hx v hv.1, hMt.1 x hx v hv.2⟩
  by_cases h0 : M ⊓ M.map (ρ t) = ⊥
  · exfalso
    have := finrank_le_disp ρ (Y := M) fun w hw hw1 => by
      have hw2 : w ∈ M ⊓ M.map (ρ t) := ⟨hw, ⟨w, hw, hw1⟩⟩
      rwa [h0, Submodule.mem_bot] at hw2
    omega
  · have heq := hM.2.2 _ (inf_le_left : M ⊓ M.map (ρ t) ≤ M) hinv h0
    have hle : M ≤ M.map (ρ t) :=
      calc M = M ⊓ M.map (ρ t) := heq.symm
        _ ≤ M.map (ρ t) := inf_le_right
    obtain ⟨m', hm', rfl⟩ := hle hm
    rwa [htt]

theorem exists_isMinInv_moved [Finite V] (hirr : ρ.IsIrreducible) {X : Subgroup G}
    (hX : X.Normal) {t : G} (ht : ρ t ≠ 1) : ∃ M, IsMinInv ρ X M ∧ ∃ m ∈ M, ρ t m ≠ m := by
  by_contra hc
  push Not at hc
  obtain ⟨hVnt, hirr'⟩ := (CFSG.QuasithinUnique.Setup.X7.isIrreducible_iff ρ).mp hirr
  haveI := hVnt
  let 𝒲 : Set (Submodule (ZMod 2) V) := {M | IsMinInv ρ X M}
  have hS : ∀ g : G, ∀ v ∈ sSup 𝒲, ρ g v ∈ sSup 𝒲 := by
    intro g v hv
    have h1 : sSup 𝒲 ≤ (sSup 𝒲).comap (ρ g) := sSup_le fun W hW =>
      Submodule.map_le_iff_le_comap.mp (le_sSup (IsMinInv.map hX hW g))
    exact h1 hv
  rcases hirr' _ hS with h | h
  · obtain ⟨M, -, hM⟩ := exists_isMinInv ρ (K := X) (U := ⊤) (fun _ _ _ _ => Submodule.mem_top)
      top_ne_bot
    exact hM.2.1 (eq_bot_iff.mpr (h ▸ le_sSup (show M ∈ 𝒲 from hM)))
  · apply ht
    have hle : sSup 𝒲 ≤ repFixedSpace ρ {t} := sSup_le fun M hM m hm => by
      rw [mem_repFixedSpace]
      intro a ha
      rw [Set.mem_singleton_iff.mp ha]
      exact hc M hM m hm
    apply LinearMap.ext
    intro v
    have hv : v ∈ repFixedSpace ρ {t} := hle (h ▸ Submodule.mem_top)
    exact (mem_repFixedSpace.mp hv) t rfl

variable {L L₂ : Subgroup G}

theorem IsPair.apply_mem_of_isMinInv [Finite V] (hP : IsPair L L₂) {F : Type} [Field F]
    [Finite F] [CharP F 2] (e : ↥L ≃* SL(2, F)) {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hfix : fixSub ρ L ⊓ fixSub ρ L₂ = ⊥) {M : Submodule (ZMod 2) V}
    (hM : IsMinInv ρ (L ⊔ L₂) M) {t : G} (ht : t * t = 1)
    (hd : Module.finrank (ZMod 2) V - Module.finrank (ZMod 2) (repFixedSpace ρ {t}) ≤ n + 1)
    {m : V} (hm : m ∈ M) : ρ t m ∈ M := by
  have := hP.two_mul_le_finrank e hn hF hfix hM.1 hM.2.1
  exact hM.apply_mem hP.sup_normal ht (by omega) hm

end MinInv

end CFSG.LocalAnalysis.UniquenessCase.UC22.K147L2Pair
