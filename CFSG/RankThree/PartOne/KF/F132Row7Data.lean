module

public import CFSG.RankThree.PartOne.KF.F132Core
public import CFSG.RankThree.PartOne.KF.F132Sl2
public import CFSG.RankThree.PartOne.KF.R7Levi2
public import CFSG.RankThree.PartOne.KFOUT3.KtySUCtx
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx
public import CFSG.RankThree.PartOne.KF.R7Final

public section

namespace CFSG.RankThree.PartOne.KF132

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

@[expose] noncomputable def torusElt (p : ℕ) {K : Type} [Field K] [CharP K 2] (d : D8Mod p K) :
    ↥(spRev K) :=
  ⟨diagU (d8Vec 4 d), by rw [d8Vec_four]; exact diagU_dvec4_mem_spRev _ _⟩

theorem torusElt_one_z {K : Type} [Field K] [CharP K 2] (z : rootsOfUnity p K) :
    torusElt p ((1 : rootsOfUnity p K), z) = b7 (z : Kˣ) := by
  apply Subtype.ext
  show diagU (d8Vec 4 ((1 : rootsOfUnity p K), z)) = diagU (dvec4 1 (z : Kˣ))
  rw [d8Vec_four]
  rfl

theorem torusElt_same {K : Type} [Field K] [CharP K 2] (z : rootsOfUnity p K) :
    torusElt p (z, z) = b7' (z : Kˣ) := by
  apply Subtype.ext
  show diagU (d8Vec 4 (z, z)) = diagU (dvec4 (z : Kˣ) (z : Kˣ))
  rw [d8Vec_four]

omit [Finite G] in
theorem row7_S {F : Subgroup G} (hp : p.Prime) (hp2 : p ≠ 2) {K : Type} [Field K] [CharP K 2]
    (hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p) (ε : ↥L →* StatedProj (StatedSp 2 K))
    (hε : IsCentralPQuot p ε) (hFL : F ≤ L) (hFexp : ∀ f ∈ F, f ^ p = 1)
    (hFT₁ : ∀ t ∈ (d8Tor p K 4).subgroupOf (spRev K), ∃ x : F,
      ε (Subgroup.inclusion hFL x) = spQ K t)
    (hFT₂ : ∀ x : F, ∃ t ∈ (d8Tor p K 4).subgroupOf (spRev K),
      ε (Subgroup.inclusion hFL x) = spQ K t) :
    ∃ S : D8Ctx p K L F, ∀ d : D8Mod p K,
      ε (Subgroup.inclusion hFL (S.tor d)) = spQ K (torusElt p d) := by
  have hT : ∀ v : D8Mod p K, (diagU (d8Vec 4 v) : GL (Fin 4) K) ∈ spRev K := fun v => by
    rw [d8Vec_four]
    exact diagU_dvec4_mem_spRev _ _
  have hP : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin 4) K) ∈ spRev K := fun τ hτ => by
    rw [mem_spRev_iff]
    simpa [conjTr] using permGL_gram (RingEquiv.refl K) τ hτ
  obtain ⟨SM, hSM⟩ := KFOUT3.exists_d8ctx_tor d8Comb_four d8Comb2_four hp hp2 hζ (spRev K) hT hP
  have hVexp : ∀ d : D8Mod p K, d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  obtain ⟨S, hS⟩ := KFOUT3.wctx_ofCentralQuot' hVexp SM (spQ K) (isCentralPQuot_spQ p) ε hε hFL
    hFexp hFT₁ hFT₂
  refine ⟨S, fun d => ?_⟩
  rw [hS d]
  congr 1
  apply Subtype.ext
  exact hSM d

theorem row7_class0 (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L)) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) (ε : ↥L →* StatedProj (StatedSp 2 K)) (hε : IsCentralPQuot p ε)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K))
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L) (hb : spQ K (b7 ζ) = ε ⟨x, hxL⟩) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E f t ∧
      ((kZero p E t).subgroupOf L).map ε = (spBlock (K := K)).range.map (spQ K) := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hq : IsCentralPQuot p (spQ K) := isCentralPQuot_spQ p
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζ2 : ζ ^ 2 ≠ 1 := by
    apply hζ.pow_ne_one_of_pos_of_lt (by norm_num)
    omega
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : spQ K (b7 ζ) = spQ K 1 := by
      rw [hb, map_one]
      have : (⟨x, hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact b7_ne_one hζ1 (hq.eq_of_map_eq (torus7_pow_eq_one (b7_mem_torus7 hζp)) (one_pow p) h2)
  obtain ⟨K₀, hd, hmod, hmap⟩ := layerCore_of_sl2_cover hp hp2 (IsPGroup.of_card h.A_card) h.A_elem
    h.L_le_centralizer hA ε (spQ K) hε hq hxA hxL hx1 (torus7_pow_eq_one (b7_mem_torus7 hζp)) hb.symm
    (fun t ht => torus7_pow_eq_one ht) hAT hK (by omega) (spBlock (K := K)) spBlock_injective
    (perfectResidual_centralizer_b7 hK4 hζ1 hζ2) (card_torus7_inf_range hp.pos hζex)
    rootU7_le_range isPGroup_rootU7 torus7_le_normalizer_rootU7
    ⟨spBlock (tr2 1), spBlock_tr2_mem_rootU7 1, rho7 ζ, rho7_mem_torus7 hζp,
      spBlock_tr2_one_not_commute_rho7 hζ1⟩
  obtain ⟨t, htL, hr, hfix, hKF, hKz⟩ := exists_reflection_of_core hGA h hEA hcL hd hf3 hmod
  refine ⟨t, htL, hr, hfix, hKF, ?_⟩
  rw [hKz, hd.K_eq, hmap]

theorem row7_class1 (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L)) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) (ε : ↥L →* StatedProj (StatedSp 2 K)) (hε : IsCentralPQuot p ε)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K))
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L) (hb : spQ K (b7' ζ) = ε ⟨x, hxL⟩) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E f t ∧
      ((kZero p E t).subgroupOf L).map ε = (spBlock' (K := K)).range.map (spQ K) := by
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hq : IsCentralPQuot p (spQ K) := isCentralPQuot_spQ p
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  have hζ2 : ζ ^ 2 ≠ 1 := by
    apply hζ.pow_ne_one_of_pos_of_lt (by norm_num)
    omega
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hx1 : x ≠ 1 := by
    intro h1
    have h2 : spQ K (b7' ζ) = spQ K 1 := by
      rw [hb, map_one]
      have : (⟨x, hxL⟩ : ↥L) = 1 := Subtype.ext h1
      rw [this, map_one]
    exact b7'_ne_one hζ1
      (hq.eq_of_map_eq (torus7_pow_eq_one (b7'_mem_torus7 hζp)) (one_pow p) h2)
  obtain ⟨K₀, hd, hmod, hmap⟩ := layerCore_of_sl2_cover hp hp2 (IsPGroup.of_card h.A_card) h.A_elem
    h.L_le_centralizer hA ε (spQ K) hε hq hxA hxL hx1 (torus7_pow_eq_one (b7'_mem_torus7 hζp))
    hb.symm (fun t ht => torus7_pow_eq_one ht) hAT hK (by omega) (spBlock' (K := K))
    spBlock'_injective (perfectResidual_centralizer_b7' hK4 hζ2)
    (card_torus7_inf_range' hp.pos hζex) rootU7'_le_range isPGroup_rootU7'
    torus7_le_normalizer_rootU7'
    ⟨spBlock' (tr2 1), spBlock'_tr2_mem_rootU7' 1, rho7' ζ, rho7'_mem_torus7 hζp,
      spBlock'_tr2_one_not_commute_rho7' hζ1⟩
  obtain ⟨t, htL, hr, hfix, hKF, hKz⟩ := exists_reflection_of_core hGA h hEA hcL hd hf3 hmod
  refine ⟨t, htL, hr, hfix, hKF, ?_⟩
  rw [hKz, hd.K_eq, hmap]

end CFSG.RankThree.PartOne.KF132
