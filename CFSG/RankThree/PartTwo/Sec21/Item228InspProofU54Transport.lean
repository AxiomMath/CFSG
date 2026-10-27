module

public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU54Model
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
public import CFSG.RankThree.PartTwo.Sec21.Item228InspProofU54

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item228InspProof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.RankThree.PartTwo.Sec21.Item233Res3Proof (K16 card_K16 σ16 SU54 U54 qU
  isCentralPQuot_qU tt tt_mem exists_tt tt_mul projSUEquivU54 tt4 tt_eq_su4Emb
  qU_su4Emb_injective)
open CFSG.RankThree.PartOne.KFU (torus6 torus6_pow_eq_one exists_conj_into_d8Tor_su d8Comb_five
  IsCentralPQuot exists_toral_quot card_center_mulEquiv)
open CFSG.RankThree.PartOne.K1320X (su4Emb)
open CFSG.RankThree.PartTwo.Sec21.U4Lines (mapL embedOf mapL_le mapL_mono card_mapL mapL_inj
  mapL_perfectResidual mapL_perfectResidual_inf mapL_inf_centralizer perfectResidualEquiv
  embedOf_injective)

section Transport

variable {G G' : Type} [Group G] [Group G'] [Finite G] [Finite G'] {X : Subgroup G}
  {X' : Subgroup G'} (e : X ≃* X')

omit [Finite G] [Finite G'] in
theorem mapL_inf (Z₁ Z₂ : Subgroup G) : mapL e (Z₁ ⊓ Z₂) = mapL e Z₁ ⊓ mapL e Z₂ := by
  change ((Z₁ ⊓ Z₂).comap X.subtype).map (embedOf e) =
    (Z₁.comap X.subtype).map (embedOf e) ⊓ (Z₂.comap X.subtype).map (embedOf e)
  rw [Subgroup.comap_inf, Subgroup.map_inf_eq _ _ _ (embedOf_injective e)]

theorem mapL_perfCent_sub {Y ℓ : Subgroup G} (hYX : Y ≤ X) (hℓX : ℓ ≤ X) :
    mapL e (perfCent Y ℓ) = perfCent (mapL e Y) (mapL e ℓ) := by
  have h1 : Y ⊓ Subgroup.centralizer (ℓ : Set G) =
      Y ⊓ (X ⊓ Subgroup.centralizer (ℓ : Set G)) := by
    rw [← inf_assoc, inf_eq_left.mpr hYX]
  have h2 : mapL e (Y ⊓ Subgroup.centralizer (ℓ : Set G)) =
      mapL e Y ⊓ Subgroup.centralizer (mapL e ℓ : Set G') := by
    rw [h1, mapL_inf, mapL_inf_centralizer e hℓX, ← inf_assoc,
      inf_eq_left.mpr (mapL_le e Y)]
  rw [perfCent, perfCent, mapL_perfectResidual e (inf_le_left.trans hYX), h2]

end Transport

theorem exists_model_U54_E9 {G : Type} [Group G] [Finite G] {X T : Subgroup G}
    (eX : X ≃* projSU 5 2 2) (hTX : T ≤ X) (hTe : IsElemAbelian 3 T) (hT9 : Nat.card T = 3 ^ 2) :
    ∃ ε : X ≃* U54, (∀ t ∈ torus6 σ16 3, ((ε.symm (qU t) : X) : G) ∈ T) ∧
      ∀ f (hf : f ∈ T), ∃ t ∈ torus6 σ16 3, ε ⟨f, hTX hf⟩ = qU t := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hZc : Subgroup.center X = ⊥ := by
    have h := card_center_mulEquiv eX
    rw [Sec4.Item434SmallTwoOther.U54.center_U54, Subgroup.card_bot] at h
    exact Subgroup.eq_bot_of_card_eq _ h
  have h27 : ¬ 27 ∣ Nat.card X := by
    rw [Nat.card_congr eX.toEquiv]
    exact not_twentySeven_dvd_card_projSU_five_four
  set eU : X ≃* U54 := eX.trans projSUEquivU54 with heU
  have hε₀ : IsCentralPQuot 3 eU.toMonoidHom := by
    refine ⟨eU.surjective, ?_, ?_⟩
    · intro x hx
      rw [(MonoidHom.ker_eq_bot_iff _).mpr eU.injective] at hx
      rw [Subgroup.mem_bot] at hx
      rw [hx]
      exact Subgroup.one_mem _
    · rw [(MonoidHom.ker_eq_bot_iff _).mpr eU.injective, Subgroup.card_bot]
      norm_num
  have hTcomm : ∀ s ∈ torus6 σ16 3, ∀ t ∈ torus6 σ16 3, s * t = t * s := by
    intro s hs t ht
    obtain ⟨a, b, rfl⟩ := exists_tt hs
    obtain ⟨c, d, rfl⟩ := exists_tt ht
    rw [tt_mul, tt_mul, mul_comm a, mul_comm b]
  have hDiag : ∀ Z : Subgroup SU54, (∀ x ∈ Z, x ^ 3 = 1) →
      (∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x) → ∃ g : SU54, ∀ x ∈ Z, g * x * g⁻¹ ∈ torus6 σ16 3 :=
    fun Z hexp _ => exists_conj_into_d8Tor_su (n := 5) (Or.inr rfl) d8Comb_five card_K16
      Nat.prime_three (by norm_num) (by norm_num) Z hexp
  have hFexp : ∀ f ∈ T, f ^ 3 = 1 := fun f hf => hTe.2 f hf
  have hFcomm : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hTe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hmax : ∀ F' : Subgroup G, F' ≤ X → (∀ x ∈ F', x ^ 3 = 1) →
      (∀ x ∈ F', ∀ y ∈ F', x * y = y * x) → T ≤ F' → F' = T := by
    intro F' hF'X hF'e _ hle
    have hp : IsPGroup 3 F' := fun x => ⟨1, Subtype.ext (by simpa using hF'e x x.2)⟩
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    have hdvd : 3 ^ k ∣ Nat.card X := hk ▸ Subgroup.card_dvd_of_le hF'X
    have hk2 : k ≤ 2 := by
      by_contra h
      exact h27 ((pow_dvd_pow 3 (by omega : 3 ≤ k)).trans hdvd)
    have hle9 : Nat.card F' ≤ 3 ^ 2 := by
      rw [hk]
      exact Nat.pow_le_pow_right (by norm_num) hk2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hT9]; exact hle9)).symm
  obtain ⟨ε, hε, hT1, hT2⟩ := exists_toral_quot qU isCentralPQuot_qU eU.toMonoidHom hε₀
    (fun t ht => torus6_pow_eq_one ht) hTcomm hDiag hTX hFexp hFcomm hmax
  have hinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have := hε.central hx
    rw [hZc] at this
    exact this
  set ε' : X ≃* U54 := MulEquiv.ofBijective ε ⟨hinj, hε.surjective⟩ with hε'
  refine ⟨ε', ?_, ?_⟩
  · intro t ht
    obtain ⟨f, hf⟩ := hT1 t ht
    have h1 : ε'.symm (qU t) = Subgroup.inclusion hTX f := by
      rw [MulEquiv.symm_apply_eq]
      exact hf.symm
    rw [h1]
    exact f.2
  · intro f hf
    obtain ⟨t, ht, h⟩ := hT2 ⟨f, hf⟩
    exact ⟨t, ht, h⟩

theorem u54Torus : U54Torus := by
  intro G _ _ X T ⟨eX⟩ hTX hTe hT9
  obtain ⟨ε, hT1, hT2⟩ := exists_model_U54_E9 eX hTX hTe hT9
  set e : X ≃* (⊤ : Subgroup U54) := ε.trans Subgroup.topEquiv.symm with he
  have hembed : ∀ x : X, embedOf e x = ε x := fun x => rfl
  set ι : ↥(SU σ16 4) →* U54 := qU.comp (su4Emb σ16) with hι
  set θ : ↥(SU σ16 4) →* G := X.subtype.comp (ε.symm.toMonoidHom.comp ι) with hθ
  have hθinj : Function.Injective θ :=
    X.subtype_injective.comp (ε.symm.injective.comp qU_su4Emb_injective)
  have hYX : θ.range ≤ X := by
    rintro _ ⟨y, rfl⟩
    exact (ε.symm (ι y)).2
  have hTY : T ≤ θ.range := by
    intro f hf
    obtain ⟨t, ht, h⟩ := hT2 f hf
    obtain ⟨a, b, rfl⟩ := exists_tt ht
    refine ⟨tt4 a b, ?_⟩
    have h1 : ε.symm (ι (tt4 a b)) = ⟨f, hTX hf⟩ := by
      rw [MulEquiv.symm_apply_eq, h, tt_eq_su4Emb]
      rfl
    change ((ε.symm (ι (tt4 a b)) : X) : G) = f
    rw [h1]
  obtain ⟨e₄⟩ := U4Lines.nonempty_projSU_mulEquiv_SU 2 (by norm_num)
  refine ⟨θ.range, hYX, hTY, ⟨(MonoidHom.ofInjective hθinj).symm.trans e₄.symm⟩,
    fun ℓ hℓ h3 => ?_⟩
  have hℓX := hℓ.trans hTX
  have hmapT : mapL e T = (torus6 σ16 3).map qU := by
    ext z
    constructor
    · rintro ⟨x, hx, rfl⟩
      obtain ⟨t, ht, h⟩ := hT2 x hx
      refine ⟨t, ht, ?_⟩
      rw [hembed, ← h]
    · rintro ⟨t, ht, rfl⟩
      refine ⟨ε.symm (qU t), hT1 t ht, ?_⟩
      rw [hembed, MulEquiv.apply_symm_apply]
  have hmapY : mapL e θ.range = ι.range := by
    ext z
    constructor
    · rintro ⟨x, ⟨y, hy⟩, rfl⟩
      refine ⟨y, ?_⟩
      have h1 : x = ε.symm (ι y) := Subtype.ext hy.symm
      rw [hembed, h1, MulEquiv.apply_symm_apply]
    · rintro ⟨y, rfl⟩
      refine ⟨ε.symm (ι y), ⟨y, rfl⟩, ?_⟩
      rw [hembed, MulEquiv.apply_symm_apply]
  have hline : mapL e ℓ ≤ (torus6 σ16 3).map qU := hmapT ▸ mapL_mono e hℓ
  have hcard : Nat.card (mapL e ℓ) = 3 := by rw [card_mapL e hℓX, h3]
  have hX' : mapL e (perfCent X ℓ) = perfCent ⊤ (mapL e ℓ) := mapL_perfectResidual_inf e hℓX
  have hY' : mapL e (perfCent θ.range ℓ) = perfCent ι.range (mapL e ℓ) := by
    rw [mapL_perfCent_sub e hYX hℓX, hmapY]
  have hPX : perfCent X ℓ ≤ X := (Subgroup.map_subtype_le _).trans inf_le_left
  have hPY : perfCent θ.range ℓ ≤ X := ((Subgroup.map_subtype_le _).trans inf_le_left).trans hYX
  rcases model_U54 hline hcard with h | ⟨hU, hle⟩
  · left
    exact mapL_inj e hPX hPY (by rw [hX', hY', h])
  · right
    refine ⟨CFSG.LieType.CurtisTits.statedClassicalModel_of_mulEquiv
      (perfectResidualEquiv e hℓX).symm hU, ?_⟩
    rintro x ⟨hxT, hxP⟩
    have hxX : x ∈ X := hTX hxT
    have h1 : embedOf e ⟨x, hxX⟩ ∈ (torus6 σ16 3).map qU ⊓ perfCent ⊤ (mapL e ℓ) := by
      refine ⟨hmapT ▸ ⟨⟨x, hxX⟩, hxT, rfl⟩, ?_⟩
      rw [← hX']
      exact ⟨⟨x, hxX⟩, hxP, rfl⟩
    have h2 := hle h1
    rw [← hY'] at h2
    obtain ⟨y, hy, hyx⟩ := h2
    have hyx' : (y : G) = x := congrArg Subtype.val (embedOf_injective e hyx)
    rw [← hyx']
    exact hy

end CFSG.RankThree.PartTwo.Sec21.Item228InspProof
