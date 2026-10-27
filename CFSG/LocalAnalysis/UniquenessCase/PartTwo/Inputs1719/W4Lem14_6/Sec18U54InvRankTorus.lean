module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Lem14_6.Sec18U54InvRankDual
public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.HyperplaneOrbit
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit

theorem two_pow_le_index_fixV_of_avoiding {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {A : Subgroup (MulAut W)}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1) (hA : A ≠ ⊥)
    {s : MulAut W} (hs : s ∈ A) {m : ℕ}
    (hconj : ∀ D : Subgroup (MulAut W), D ≤ A → D.relIndex A = p →
      ∃ t : Fin m → MulAut W, (∀ j, t j ∈ Subgroup.normalizer (A : Set (MulAut W))) ∧
        (∀ j, s ∉ conjSub (t j) D) ∧ Function.Injective (fun j => conjSub (t j) D)) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ (fixV (Subgroup.zpowers s)).index := by
  classical
  have hodd : Odd p := (Fact.out : Nat.Prime p).odd_of_ne_two hp2
  have hAodd : Odd (Nat.card A) := odd_card_of_pow_eq_one hodd hAp
  set K : Subgroup W := (normHom A).ker with hK
  have hKA : ∀ a ∈ A, ∀ k ∈ K, a k ∈ K := fun a ha k hk =>
    map_ker_normHom (Subgroup.le_normalizer ha) hk
  have hfix : fixV A ⊓ K = ⊥ := fixV_inf_ker_normHom hW hAodd
  have : Fintype (Subgroup (MulAut W)) := Fintype.ofFinite _
  let 𝒟 : Finset (Subgroup (MulAut W)) :=
    Finset.univ.filter (fun D => D ≤ A ∧ D.relIndex A = p)
  have h𝒟 : ∀ D, D ∈ 𝒟 ↔ D ≤ A ∧ D.relIndex A = p := fun D => by simp [𝒟]
  have hKne : K ≠ ⊥ := by
    intro hK0
    have hcard := card_ker_normHom_mul hW hAodd
    rw [← hK, hK0, Subgroup.card_bot, mul_one] at hcard
    have hfixtop : fixV A = ⊤ := Subgroup.eq_top_of_card_eq _ hcard
    obtain ⟨⟨u, huA⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hA
    apply hu1
    apply Subtype.ext
    apply DFunLike.ext
    intro w
    have : w ∈ fixV A := by rw [hfixtop]; exact Subgroup.mem_top w
    exact mem_fixV.1 this u huA
  have hcardK := card_eq_prod_card_fixV_inf_hyperplanes hW hp2 hAc hAp hKA hfix 𝒟 h𝒟
  obtain ⟨D₀, hD₀𝒟, hD₀ne⟩ : ∃ D ∈ 𝒟, fixV D ⊓ K ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    apply hKne
    apply Subgroup.card_eq_one.1
    rw [hcardK]
    refine Finset.prod_eq_one fun D hD => ?_
    rw [hcon D hD, Subgroup.card_bot]
  obtain ⟨hD₀A, hD₀rel⟩ := (h𝒟 D₀).1 hD₀𝒟
  set K' : Subgroup W := fixV (Subgroup.zpowers s) ⊓ K with hK'
  have hK'A : ∀ a ∈ A, ∀ k ∈ K', a k ∈ K' := by
    intro a ha k hk
    obtain ⟨hks, hkK⟩ := Subgroup.mem_inf.1 hk
    refine Subgroup.mem_inf.2 ⟨?_, hKA a ha k hkK⟩
    rw [mem_fixV]
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    have hcomm : s ^ n * a = a * s ^ n := hAc _ (A.zpow_mem hs n) a ha
    calc (s ^ n) (a k) = (s ^ n * a) k := rfl
      _ = (a * s ^ n) k := by rw [hcomm]
      _ = a ((s ^ n) k) := rfl
      _ = a k := by rw [mem_fixV.1 hks _ (Subgroup.zpow_mem_zpowers s n)]
  have hfix' : fixV A ⊓ K' = ⊥ := by
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvA, hvK'⟩ := Subgroup.mem_inf.1 hv
    have : v ∈ fixV A ⊓ K := Subgroup.mem_inf.2 ⟨hvA, (Subgroup.mem_inf.1 hvK').2⟩
    rwa [hfix] at this
  have hcardK' := card_eq_prod_card_fixV_inf_hyperplanes hW hp2 hAc hAp hK'A hfix' 𝒟 h𝒟
  have hin : ∀ D ∈ 𝒟, s ∈ D → fixV D ⊓ K' = fixV D ⊓ K := by
    intro D _ hsD
    have hle : fixV D ≤ fixV (Subgroup.zpowers s) := fun v hv x hx =>
      hv x ((Subgroup.zpowers_le.2 hsD) hx)
    ext v
    simp only [hK', Subgroup.mem_inf]
    exact ⟨fun ⟨h1, _, h3⟩ => ⟨h1, h3⟩, fun ⟨h1, h3⟩ => ⟨h1, hle h1, h3⟩⟩
  have hout : ∀ D ∈ 𝒟, s ∉ D → fixV D ⊓ K' = ⊥ := by
    intro D hD hsD
    obtain ⟨hDA, hDrel⟩ := (h𝒟 D).1 hD
    have hsup : D ⊔ Subgroup.zpowers s = A := by
      refine eq_of_le_of_relIndex_prime le_sup_left
        (sup_le hDA (Subgroup.zpowers_le.2 hs)) hDrel ?_
      intro h
      apply hsD
      rw [h]
      exact Subgroup.mem_sup_right (Subgroup.mem_zpowers s)
    rw [eq_bot_iff]
    intro v hv
    obtain ⟨hvD, hvK'⟩ := Subgroup.mem_inf.1 hv
    obtain ⟨hvs, hvK⟩ := Subgroup.mem_inf.1 hvK'
    have hvA : v ∈ fixV A := by
      rw [← hsup, CFSG.QuasithinUnique.Setup.X1.fixV_sup]
      exact Subgroup.mem_inf.2 ⟨hvD, hvs⟩
    have : v ∈ fixV A ⊓ K := Subgroup.mem_inf.2 ⟨hvA, hvK⟩
    rwa [hfix] at this
  have hK'prod : Nat.card K' =
      ∏ D ∈ 𝒟.filter (fun D => s ∈ D), Nat.card ↥(fixV D ⊓ K) := by
    rw [hcardK', ← Finset.prod_filter_mul_prod_filter_not 𝒟 (fun D => s ∈ D)]
    have h1 : ∏ D ∈ 𝒟.filter (fun D => ¬ s ∈ D), Nat.card ↥(fixV D ⊓ K') = 1 :=
      Finset.prod_eq_one fun D hD => by
        obtain ⟨hD𝒟, hsD⟩ := Finset.mem_filter.1 hD
        rw [hout D hD𝒟 hsD, Subgroup.card_bot]
    rw [h1, mul_one]
    exact Finset.prod_congr rfl fun D hD => by
      obtain ⟨hD𝒟, hsD⟩ := Finset.mem_filter.1 hD
      rw [hin D hD𝒟 hsD]
  have hKsplit : Nat.card K = Nat.card K' *
      ∏ D ∈ 𝒟.filter (fun D => s ∉ D), Nat.card ↥(fixV D ⊓ K) := by
    rw [hK'prod, hcardK, Finset.prod_filter_mul_prod_filter_not]
  have hrel : (fixV (Subgroup.zpowers s)).relIndex K * Nat.card K' = Nat.card K :=
    (fixV (Subgroup.zpowers s)).relIndex_mul_card K
  have hK'pos : 0 < Nat.card K' := Nat.card_pos
  have hrel' : (fixV (Subgroup.zpowers s)).relIndex K =
      ∏ D ∈ 𝒟.filter (fun D => s ∉ D), Nat.card ↥(fixV D ⊓ K) := by
    rw [hKsplit, mul_comm] at hrel
    exact Nat.eq_of_mul_eq_mul_left hK'pos hrel
  have hle : (fixV (Subgroup.zpowers s)).relIndex K ≤ (fixV (Subgroup.zpowers s)).index := by
    have := Subgroup.relIndex_le_of_le_right (H := fixV (Subgroup.zpowers s))
      (le_top : K ≤ ⊤) (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
    rwa [Subgroup.relIndex_top_right] at this
  obtain ⟨t, htN, hts, htinj⟩ := hconj D₀ hD₀A hD₀rel
  have hD₀cardpos : 0 < Nat.card D₀ := Nat.card_pos
  have hpD₀ : p * Nat.card D₀ = Nat.card A := by
    have := D₀.relIndex_mul_card A
    rwa [hD₀rel, inf_eq_left.2 hD₀A] at this
  have hconjD : ∀ j, conjSub (t j) D₀ ∈ 𝒟 ∧ fixV (conjSub (t j) D₀) ⊓ K ≠ ⊥ := by
    intro j
    have htN' := htN j
    have hle : conjSub (t j) D₀ ≤ A := by
      intro x hx
      rw [mem_conjSub] at hx
      have h1 := hD₀A hx
      have := (Subgroup.mem_set_normalizer_iff.1 htN' ((t j)⁻¹ * x * t j)).1 h1
      have e : t j * ((t j)⁻¹ * x * t j) * (t j)⁻¹ = x := by group
      rwa [e] at this
    have hrelc : (conjSub (t j) D₀).relIndex A = p := by
      have h1 := (conjSub (t j) D₀).relIndex_mul_card A
      rw [inf_eq_left.2 hle, card_conjSub] at h1
      exact Nat.eq_of_mul_eq_mul_right hD₀cardpos (h1.trans hpD₀.symm)
    refine ⟨(h𝒟 _).2 ⟨hle, hrelc⟩, ?_⟩
    obtain ⟨⟨k, hk⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hD₀ne
    obtain ⟨hkD, hkK⟩ := Subgroup.mem_inf.1 hk
    apply Subgroup.ne_bot_iff_exists_ne_one.2
    refine ⟨⟨t j k, Subgroup.mem_inf.2 ⟨?_, map_ker_normHom htN' hkK⟩⟩, ?_⟩
    · rw [mem_fixV]
      intro x hx
      rw [mem_conjSub] at hx
      have hcomm : x * t j = t j * ((t j)⁻¹ * x * t j) := by group
      have hy : ((t j)⁻¹ * x * t j) k = k := mem_fixV.1 hkD _ hx
      calc x (t j k) = (x * t j) k := rfl
        _ = (t j * ((t j)⁻¹ * x * t j)) k := by rw [hcomm]
        _ = t j (((t j)⁻¹ * x * t j) k) := rfl
        _ = t j k := by rw [hy]
    · intro h1
      apply hk1
      have h2 : (t j : MulAut W) k = 1 := congrArg Subtype.val h1
      apply Subtype.ext
      show k = 1
      have : (t j : MulAut W) k = (t j : MulAut W) 1 := by rw [h2, map_one]
      exact (t j : MulAut W).injective this
  let 𝒮 : Finset (Subgroup (MulAut W)) := Finset.univ.image (fun j => conjSub (t j) D₀)
  have h𝒮card : 𝒮.card = m := by
    rw [Finset.card_image_of_injective _ htinj, Finset.card_univ, Fintype.card_fin]
  have h𝒮sub : 𝒮 ⊆ 𝒟.filter (fun D => s ∉ D) := by
    intro D hD
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hD
    exact Finset.mem_filter.2 ⟨(hconjD j).1, hts j⟩
  have h𝒮big : ∀ D ∈ 𝒮, 2 ^ orderOf (2 : ZMod p) ≤ Nat.card ↥(fixV D ⊓ K) := by
    intro D hD
    obtain ⟨j, -, rfl⟩ := Finset.mem_image.1 hD
    obtain ⟨hD𝒟, hDne⟩ := hconjD j
    obtain ⟨hDA, hDrel⟩ := (h𝒟 _).1 hD𝒟
    exact two_pow_le_card_fixV_inf hW hAc hAp hKA hfix hDA hDrel hDne
  calc 2 ^ (m * orderOf (2 : ZMod p)) = (2 ^ orderOf (2 : ZMod p)) ^ 𝒮.card := by
        rw [h𝒮card, mul_comm, pow_mul]
    _ = ∏ _D ∈ 𝒮, 2 ^ orderOf (2 : ZMod p) := by rw [Finset.prod_const]
    _ ≤ ∏ D ∈ 𝒮, Nat.card ↥(fixV D ⊓ K) := Finset.prod_le_prod' h𝒮big
    _ ≤ ∏ D ∈ 𝒟.filter (fun D => s ∉ D), Nat.card ↥(fixV D ⊓ K) :=
        Finset.prod_le_prod_of_subset_of_one_le' h𝒮sub fun D _ _ => Nat.card_pos
    _ = (fixV (Subgroup.zpowers s)).relIndex K := hrel'.symm
    _ ≤ (fixV (Subgroup.zpowers s)).index := hle

@[expose] def gword {G : Type*} [Group G] (g : Fin 4 → G) (w : List (Fin 4)) : G := (w.map g).prod

theorem gword_cons {G : Type*} [Group G] (g : Fin 4 → G) (i : Fin 4) (w : List (Fin 4)) :
    gword g (i :: w) = g i * gword g w := by
  simp [gword]

theorem bword_append (v w : List (Fin 4)) (l : Fin 3 → ZMod 5) :
    Bword (v ++ w) l = Bword v (Bword w l) := by
  simp [Bword, List.foldr_append]

section Torus

variable {G : Type*} [Group G] {φ : Multiplicative (Fin 3 → ZMod 5) →* G} {g : Fin 4 → G}

theorem inv_conj_eq (hg : ∀ i c, g i * φ (.ofAdd c) * (g i)⁻¹ = φ (.ofAdd (Amap i c)))
    (i : Fin 4) (c : Fin 3 → ZMod 5) :
    (g i)⁻¹ * φ (.ofAdd c) * g i = φ (.ofAdd (Amap i c)) := by
  have h1 := hg i (Amap i c)
  rw [amap_amap] at h1
  rw [← h1]
  group

theorem gword_inv_conj (hg : ∀ i c, g i * φ (.ofAdd c) * (g i)⁻¹ = φ (.ofAdd (Amap i c)))
    (w : List (Fin 4)) (c : Fin 3 → ZMod 5) :
    (gword g w)⁻¹ * φ (.ofAdd c) * gword g w = φ (.ofAdd (Aword w c)) := by
  induction w generalizing c with
  | nil => simp [gword, Aword]
  | cons i w ih =>
    rw [gword_cons]
    calc (g i * gword g w)⁻¹ * φ (.ofAdd c) * (g i * gword g w)
        = (gword g w)⁻¹ * ((g i)⁻¹ * φ (.ofAdd c) * g i) * gword g w := by group
      _ = φ (.ofAdd (Aword (i :: w) c)) := by
        rw [inv_conj_eq hg, ih]
        rfl

theorem mem_conjSub_gword_iff (hg : ∀ i c, g i * φ (.ofAdd c) * (g i)⁻¹ = φ (.ofAdd (Amap i c)))
    {D : Subgroup G} {l : Fin 3 → ZMod 5} (hD : ∀ c, φ (.ofAdd c) ∈ D ↔ dual3 l c = 0)
    (w : List (Fin 4)) (c : Fin 3 → ZMod 5) :
    φ (.ofAdd c) ∈ conjSub (gword g w) D ↔ dual3 (Bword w l) c = 0 := by
  rw [mem_conjSub, gword_inv_conj hg, hD, dual3_aword]

theorem gword_mem_normalizer (hg : ∀ i c, g i * φ (.ofAdd c) * (g i)⁻¹ = φ (.ofAdd (Amap i c)))
    (w : List (Fin 4)) : gword g w ∈ Subgroup.normalizer (φ.range : Set G) := by
  have hgi : ∀ i, g i ∈ Subgroup.normalizer (φ.range : Set G) := by
    intro i
    rw [Subgroup.mem_set_normalizer_iff]
    intro x
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨.ofAdd (Amap i (Multiplicative.toAdd c)), (hg i _).symm⟩
    · rintro ⟨c, hc⟩
      refine ⟨.ofAdd (Amap i (Multiplicative.toAdd c)), ?_⟩
      rw [← inv_conj_eq hg]
      change (g i)⁻¹ * φ c * g i = x
      rw [hc]
      group
  induction w with
  | nil => exact Subgroup.one_mem _
  | cons i w ih => rw [gword_cons]; exact Subgroup.mul_mem _ (hgi i) ih

end Torus

theorem twentyFour_le_rkIdx {U : Type} [CommGroup U] [Finite U] (hU : ∀ u : U, u ^ 2 = 1)
    (φ : Multiplicative (Fin 3 → ZMod 5) →* MulAut U) (hφ : φ (.ofAdd cS) ≠ 1)
    (g : Fin 4 → MulAut U)
    (hg : ∀ i c, g i * φ (.ofAdd c) * (g i)⁻¹ = φ (.ofAdd (Amap i c))) :
    24 ≤ rkIdx (fixV (Subgroup.zpowers (φ (.ofAdd cS)))) := by
  classical
  have hord : orderOf (2 : ZMod 5) = 4 := (orderOf_eq_iff (by norm_num)).mpr ⟨by decide, by decide⟩
  have h50 : ((5 : ℕ) : ZMod 5) = 0 := by decide
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h5 : ∀ x : Multiplicative (Fin 3 → ZMod 5), x ^ 5 = 1 := by
    intro x
    apply Multiplicative.toAdd.injective
    funext j
    simp only [toAdd_pow, toAdd_one, Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul]
    rw [h50, zero_mul]
  have hAc : ∀ a ∈ φ.range, ∀ b ∈ φ.range, a * b = b * a := by
    rintro _ ⟨x, rfl⟩ _ ⟨y, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hAp : ∀ a ∈ φ.range, a ^ 5 = 1 := by
    rintro _ ⟨x, rfl⟩
    rw [← map_pow, h5, map_one]
  have hs : φ (.ofAdd cS) ∈ φ.range := ⟨_, rfl⟩
  have hA : φ.range ≠ ⊥ := by
    intro h
    rw [h, Subgroup.mem_bot] at hs
    exact hφ hs
  have hU' : ∀ u : U, u * u = 1 := fun u => by rw [← sq]; exact hU u
  have key := two_pow_le_index_fixV_of_avoiding hU' (p := 5) (by norm_num) hAc hAp hA hs (m := 6)
    (by
      intro D hDA hD
      have hH : (D.comap φ).index = 5 := by rw [Subgroup.index_comap]; exact hD
      obtain ⟨l, hl0, hl⟩ := exists_dual3_of_index_eq_five hH
      have hDl : ∀ c, φ (.ofAdd c) ∈ D ↔ dual3 l c = 0 := fun c => hl c
      obtain ⟨u, -, k, a, ha, hua⟩ := exists_toBase l hl0
      have hmem : ∀ (j : Fin 6) (c : Fin 3 → ZMod 5),
          φ (.ofAdd c) ∈ conjSub (gword g (avoidWords k j ++ u)) D ↔
            dual3 (Bword (avoidWords k j) (baseL k)) c = 0 := by
        intro j c
        rw [mem_conjSub_gword_iff hg hDl, bword_append, hua, bword_smul, dual3_smul,
          mul_eq_zero, or_iff_right ha]
      refine ⟨fun j => gword g (avoidWords k j ++ u), fun j => gword_mem_normalizer hg _,
        fun j hj => avoid_cS k j ((hmem j cS).1 hj), fun j j' hjj' => ?_⟩
      by_contra hne
      obtain ⟨c, hc1, hc2⟩ := avoid_distinct k j j' hne
      have e : φ (.ofAdd c) ∈ conjSub (gword g (avoidWords k j ++ u)) D ↔
          φ (.ofAdd c) ∈ conjSub (gword g (avoidWords k j' ++ u)) D := by
        simp only at hjj'
        rw [hjj']
      rw [hmem, hmem] at e
      exact hc2 (e.1 hc1))
  rw [hord, CFSG.Quasithin.B1.index_eq_two_pow hU] at key
  exact (Nat.pow_le_pow_iff_right (by norm_num)).mp key

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Lem14_6.U54InvRank
