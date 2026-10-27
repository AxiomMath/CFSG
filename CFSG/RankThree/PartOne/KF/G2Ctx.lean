module

public import CFSG.RankThree.PartOne.KF.G2Dih
public import CFSG.RankThree.PartOne.KF.WCtx

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PartOne

abbrev G2Ctx {G : Type} [Group G] (p : ℕ) (K : Type) [Field K] (L F : Subgroup G) : Type :=
  WCtx (g2Dih p K).subtype L F

namespace G2Ctx

variable {G : Type} [Group G] {p : ℕ} {K : Type} [Field K] {L F : Subgroup G}
  (S : G2Ctx p K L F)

include S in
theorem card_F (hp : 0 < p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : Nat.card F = p ^ 2 := by
  rw [← Nat.card_congr S.tor.toEquiv]
  exact card_G2V hp hζ

include S in
theorem actF_injective : Function.Injective S.actF := fun _ _ h =>
  Subtype.ext ((MulAut.congr S.tor).injective h)

@[expose] noncomputable def weylEquiv (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) : ↥(torusImage F L) ≃* DihedralGroup 6 :=
  ((MulEquiv.subgroupCongr S.torusImage_eq_range).trans
    (MonoidHom.ofInjective S.actF_injective).symm).trans (g2Dih_equiv hp h5 hζ).some

theorem autMoved_actF (γ : ↥(g2Dih p K)) :
    autMoved F (S.actF γ) = (movedV (γ : MulAut (G2V p K))).map S.tor.toMonoidHom := by
  unfold autMoved movedV
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨e, rfl⟩
    obtain ⟨d, rfl⟩ := S.tor.surjective e
    exact ⟨(γ : MulAut (G2V p K)) d * d⁻¹, ⟨d, rfl⟩, by simp [S.actF_apply, map_mul, map_inv]⟩
  · rintro ⟨_, ⟨d, rfl⟩, rfl⟩
    exact ⟨S.tor d, by simp [S.actF_apply, map_mul, map_inv]⟩

include S in
theorem isAutReflection_s0 (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    IsAutReflection p F (S.actF ⟨g2s0 p K, g2s0_mem_g2Dih⟩) := by
  refine ⟨?_, ?_⟩
  · rw [orderOf_injective _ S.actF_injective, Subgroup.orderOf_mk]
    exact orderOf_g2s0 hp h5 hζ
  · rw [S.autMoved_actF, Subgroup.card_map_of_injective S.tor.injective]
    exact card_movedV_g2s0 hp h5 hζ

include S in
theorem isAutReflection_s1 (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    IsAutReflection p F (S.actF ⟨g2s1 p K, g2s1_mem_g2Dih⟩) := by
  refine ⟨?_, ?_⟩
  · rw [orderOf_injective _ S.actF_injective, Subgroup.orderOf_mk]
    exact orderOf_g2s1 hp h5 hζ
  · rw [S.autMoved_actF, Subgroup.card_map_of_injective S.tor.injective]
    exact card_movedV_g2s1 hp h5 hζ

include S in
theorem torusImage_eq_closure (hp : p.Prime) (h5 : 5 ≤ p)
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) :
    torusImage F L = Subgroup.closure {t | t ∈ torusImage F L ∧ IsAutReflection p F t} := by
  apply le_antisymm
  · have htop : Subgroup.closure ((Subtype.val : ↥(g2Dih p K) → MulAut (G2V p K)) ⁻¹'
        {g2s0 p K, g2s1 p K}) = ⊤ := Subgroup.closure_closure_coe_preimage
    have h : torusImage F L = Subgroup.closure (S.actF '' ((Subtype.val : ↥(g2Dih p K) →
        MulAut (G2V p K)) ⁻¹' {g2s0 p K, g2s1 p K})) := by
      rw [S.torusImage_eq_range, MonoidHom.range_eq_map, ← htop, MonoidHom.map_closure]
    refine h.le.trans (Subgroup.closure_mono ?_)
    rintro _ ⟨γ, hγ, rfl⟩
    refine ⟨by rw [S.torusImage_eq_range]; exact ⟨γ, rfl⟩, ?_⟩
    rcases hγ with h0 | h1
    · have : γ = ⟨g2s0 p K, g2s0_mem_g2Dih⟩ := Subtype.ext h0
      rw [this]
      exact S.isAutReflection_s0 hp h5 hζ
    · have : γ = ⟨g2s1 p K, g2s1_mem_g2Dih⟩ := Subtype.ext (by simpa using h1)
      rw [this]
      exact S.isAutReflection_s1 hp h5 hζ
  · exact (Subgroup.closure_le _).mpr fun t ht => ht.1

include S in
theorem torusIrreducible (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (B : Subgroup G) (hBF : B ≤ F) (hB : torusInvariant F L B) : B = ⊥ ∨ B = F :=
  S.torusIrreducible_of (fun B' hB' => g2Dih_irreducible hp h5 hζ B'
    (fun γ hγ x hx => hB' ⟨γ, hγ⟩ x hx)) B hBF hB

include S in
theorem not_isAutTransvection (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    (hpow : ∀ a : F, a ^ p = 1) {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ¬ IsAutTransvection p F (F.normalizerMonoidHom ⟨y, hyF⟩) := by
  intro hT
  set φ : MulAut F := F.normalizerMonoidHom ⟨y, hyF⟩ with hφdef
  have hφV : ((MulAut.congr S.tor).symm φ) ^ p = 1 := by
    rw [← map_pow, hT.pow_eq_one hpow, map_one]
  have h1 : (MulAut.congr S.tor).symm φ = 1 :=
    eq_one_of_normalizes_g2Dih hp h5 hζ _ hφV (fun γ hγ => by
      obtain ⟨γ', h⟩ := S.normalizes_act hyL hyF ⟨γ, hγ⟩
      exact h ▸ γ'.2)
  apply hT.1
  have := congrArg (MulAut.congr S.tor) h1
  rwa [MulEquiv.apply_symm_apply, map_one] at this

include S in
theorem rowData (hp : p.Prime) (h5 : 5 ≤ p) (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p)
    {r : ℕ} (hr : r = 2 ∨ r = 3) (hmodel : RowModel p L r) : RowData p L F r := by
  rcases hr with rfl | rfl
  · exact ⟨hmodel, S.card_F hp.pos hζ, ⟨S.weylEquiv hp h5 hζ⟩, S.torusImage_eq_closure hp h5 hζ,
      fun _ B hBF hB => S.torusIrreducible hp h5 hζ B hBF hB, fun h11 => absurd h11 (by norm_num)⟩
  · exact ⟨hmodel, S.card_F hp.pos hζ, ⟨S.weylEquiv hp h5 hζ⟩, S.torusImage_eq_closure hp h5 hζ,
      fun _ B hBF hB => S.torusIrreducible hp h5 hζ B hBF hB, fun h11 => absurd h11 (by norm_num)⟩

end G2Ctx

end CFSG.RankThree.PartOne.KFU
