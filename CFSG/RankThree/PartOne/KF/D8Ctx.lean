module

public import CFSG.RankThree.PartOne.KF.WCtx
public import CFSG.RankThree.PartOne.KF.D8Normalizer

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PartOne

abbrev D8Ctx {G : Type} [Group G] (p : ℕ) (K : Type) [Field K] (L F : Subgroup G) : Type :=
  WCtx (d8Act : DihedralGroup 4 →* MulAut (D8Mod p K)) L F

theorem closure_range_sr : Subgroup.closure (Set.range (DihedralGroup.sr : ZMod 4 →
    DihedralGroup 4)) = ⊤ := by
  rw [eq_top_iff]
  rintro (i | i) -
  · have : (DihedralGroup.r i : DihedralGroup 4) = DihedralGroup.sr 0 * DihedralGroup.sr i := by
      rw [DihedralGroup.sr_mul_sr, sub_zero]
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.subset_closure ⟨0, rfl⟩) (Subgroup.subset_closure ⟨i, rfl⟩)
  · exact Subgroup.subset_closure ⟨i, rfl⟩

namespace D8Ctx

variable {G : Type} [Group G] {p : ℕ} {K : Type} [Field K] {L F : Subgroup G}
  (S : D8Ctx p K L F)

include S in
theorem card_F (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : Nat.card F = p ^ 2 := by
  rw [← Nat.card_congr S.tor.toEquiv]
  exact card_D8Mod hp hζ

include S in
theorem actF_injective (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    Function.Injective S.actF := fun _ _ h =>
  d8Act_injective hp hp2 hζ ((MulAut.congr S.tor).injective h)

@[expose] noncomputable def weylEquiv (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : ↥(torusImage F L) ≃* DihedralGroup 4 :=
  (MulEquiv.subgroupCongr S.torusImage_eq_range).trans
    (MonoidHom.ofInjective (S.actF_injective hp hp2 hζ)).symm

theorem autMoved_actF (w : DihedralGroup 4) :
    autMoved F (S.actF w) = (movedV (d8Act (p := p) (K := K) w)).map S.tor.toMonoidHom := by
  unfold autMoved movedV
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨d, rfl⟩ := S.tor.surjective e
    exact ⟨d8Act w d * d⁻¹, ⟨d, rfl⟩, by simp [S.actF_apply, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨S.tor d, by simp [S.actF_apply, map_mul, map_inv]⟩

include S in
theorem isAutReflection_sr (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (i : ZMod 4) : IsAutReflection p F (S.actF (DihedralGroup.sr i)) := by
  refine ⟨?_, ?_⟩
  · rw [orderOf_injective _ (S.actF_injective hp hp2 hζ) _, DihedralGroup.orderOf_sr]
  · rw [autMoved_actF, Subgroup.card_map_of_injective S.tor.injective]
    exact card_movedV_sr hp hp2 hζ i

include S in
theorem torusImage_eq_closure (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    torusImage F L = Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection p F t} := by
  apply le_antisymm
  · have h : torusImage F L = Subgroup.closure (S.actF '' Set.range DihedralGroup.sr) := by
      rw [S.torusImage_eq_range, MonoidHom.range_eq_map, ← closure_range_sr,
        MonoidHom.map_closure]
    calc torusImage F L = Subgroup.closure (S.actF '' Set.range DihedralGroup.sr) := h
      _ ≤ Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection p F t} := by
        refine Subgroup.closure_mono ?_
        rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
        exact ⟨by rw [S.torusImage_eq_range]; exact ⟨_, rfl⟩,
          S.isAutReflection_sr hp hp2 hζ i⟩
  · exact (Subgroup.closure_le _).mpr fun t ht => ht.1

include S in
theorem torusIrreducible (hp : p.Prime) (hp2 : p ≠ 2) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (B : Subgroup G) (hBF : B ≤ F) (hB : torusInvariant F L B) : B = ⊥ ∨ B = F :=
  S.torusIrreducible_of (fun B' hB' => eq_bot_or_eq_top_of_d8Invariant hp hp2 hζ B' hB') B hBF hB

include S in
theorem not_isAutTransvection (hp : p.Prime) (hp2 : p ≠ 2) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (hpow : ∀ a : F, a ^ p = 1) {y : G}
    (hyL : y ∈ Subgroup.normalizer (L : Set G)) (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hyF⟩) := by
  intro hT
  have hφp := hT.pow_eq_one hpow
  set φ : MulAut F := F.normalizerMonoidHom ⟨y, hyF⟩ with hφdef
  have hφV : ((MulAut.congr S.tor).symm φ) ^ p = 1 := by rw [← map_pow, hφp, map_one]
  have h1 : (MulAut.congr S.tor).symm φ = 1 :=
    eq_one_of_normalizes_d8 hp hp2 h5 hζ _ hφV (S.normalizes_act hyL hyF)
  apply hT.1
  have := congrArg (MulAut.congr S.tor) h1
  rwa [MulEquiv.apply_symm_apply, map_one] at this

include S in
theorem rowData {r : ℕ} (hr : r = 5 ∨ r = 6 ∨ r = 7 ∨ r = 8) (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (hmodel : RowModel p L r) : RowData p L F r := by
  have hrank : RowRank r = 2 := by rcases hr with rfl | rfl | rfl | rfl <;> rfl
  have hweyl : RowWeylIso F (torusImage F L) r ↔
      Nonempty (↥(torusImage F L) ≃* DihedralGroup 4) := by
    rcases hr with rfl | rfl | rfl | rfl <;> exact Iff.rfl
  have hne : r ≠ 11 := by rcases hr with rfl | rfl | rfl | rfl <;> norm_num
  exact ⟨hmodel, by rw [hrank]; exact S.card_F hp.pos hζ,
    hweyl.mpr ⟨S.weylEquiv hp hp2 hζ⟩, S.torusImage_eq_closure hp hp2 hζ,
    fun _ B hBF hB => S.torusIrreducible hp hp2 hζ B hBF hB, fun h11 => absurd h11 hne⟩

end D8Ctx

end CFSG.RankThree.PartOne.KFU
