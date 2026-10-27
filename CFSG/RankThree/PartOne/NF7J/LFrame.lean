module

public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KF.F132D8
public import CFSG.RankThree.PartOne.KF.F132Row7Data
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary CFSG.RankThree.PartOne.KF132

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem row7_class0' (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L)) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) (ε : ↥L →* StatedProj (StatedSp 2 K)) (hε : IsCentralPQuot p ε)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K))
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L) (hb : spQ K (b7 ζ) = ε ⟨x, hxL⟩) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E f t ∧ kZero p E t ≤ L ∧
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
  refine ⟨t, htL, hr, hfix, hKF, ?_, ?_⟩
  · rw [hKz, hd.K_eq]
    exact (Subgroup.map_subtype_le _ : kLayer L x ≤ _).trans inf_le_left
  · rw [hKz, hd.K_eq, hmap]

theorem row7_class1' (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L)) (hf3 : 3 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f) {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) (ε : ↥L →* StatedProj (StatedSp 2 K)) (hε : IsCentralPQuot p ε)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K))
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L) (hb : spQ K (b7' ζ) = ε ⟨x, hxL⟩) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E f t ∧ kZero p E t ≤ L ∧
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
  refine ⟨t, htL, hr, hfix, hKF, ?_, ?_⟩
  · rw [hKz, hd.K_eq]
    exact (Subgroup.map_subtype_le _ : kLayer L x ≤ _).trans inf_le_left
  · rw [hKz, hd.K_eq, hmap]


theorem nf7j_frame (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f) :
    Subgroup.center L = ⊥ ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : Nat.card K = 2 ^ f)
        (ε : ↥L →* StatedProj (StatedSp 2 K)), IsCentralPQuot p ε ∧
        ∃ ζ : Kˣ, IsPrimitiveRoot ζ p ∧
        ((A ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K) ∧
        ∃ r₀ r₁ : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧ r₁ ∈ reflectionSet p E ∧
          r₁ ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧ KFAt p E f r₀ ∧ KFAt p E f r₁ ∧
          kZero p E r₀ ≤ L ∧ kZero p E r₁ ≤ L ∧
          ((kZero p E r₀).subgroupOf L).map ε = (spBlock (K := K)).range.map (spQ K) ∧
          ((kZero p E r₁).subgroupOf L).map ε = (spBlock' (K := K)).range.map (spQ K) := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf3 := three_le_of_dvd h5 hf1 hpq
  have hZL : Subgroup.center L = ⊥ := psp_two_center_trivial hGA hf1 hF.isQuasisimple_L hmod
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_of_center_bot hF hZL
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, -, -, hK, ⟨ζ, hζ⟩, hchar, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r7frame_of hcore hf1 hpq hmod
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (torus7 p K).map (spQ K) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    rw [hAL]
    ext y
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨t, ht, hta⟩ := hFT₂ ⟨(a : G), Subgroup.mem_subgroupOf.1 ha⟩
      exact ⟨t, ht, hta.symm⟩
    · rintro ⟨t, ht, rfl⟩
      obtain ⟨x', hx'⟩ := hFT₁ t ht
      exact ⟨Subgroup.inclusion hcore.F_le x', Subgroup.mem_subgroupOf.2 x'.2, hx'⟩
  obtain ⟨S, hS⟩ := row7_S hp hp2 ⟨ζ, hζ⟩ ε hε hcore.F_le hcore.F_exp hFT₁ hFT₂
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R : Sec12Three.Restr c L E (E ⊓ L) := h.restr_of_generic hG
  have hζp : ζ ^ p = 1 := hζ.pow_eq_one
  have hζex : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := ⟨ζ, hζ⟩
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hG.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  have hζ1 : ζ ≠ 1 := hζ.ne_one (by omega)
  set z : rootsOfUnity p K := ⟨ζ, (mem_rootsOfUnity p _).mpr hζp⟩ with hz
  have hz1 : z ≠ 1 := fun h1 => hζ1 (congrArg Subtype.val h1)
  have hz2 : z ^ 2 ≠ 1 := fun h1 => hz1 (eq_one_of_sq_eq_one_of_odd (hp.odd_of_ne_two hp2) h1)
  set d₀ : D8Mod p K := ((1 : rootsOfUnity p K), z) with hd₀
  set d₁ : D8Mod p K := (z, z) with hd₁
  set x₀ : G := ((S.tor d₀ : ↥(E ⊓ L)) : G) with hx₀
  set x₁ : G := ((S.tor d₁ : ↥(E ⊓ L)) : G) with hx₁
  have hx₀E : x₀ ∈ E := (S.tor d₀).2.1
  have hx₀L : x₀ ∈ L := (S.tor d₀).2.2
  have hx₁E : x₁ ∈ E := (S.tor d₁).2.1
  have hx₁L : x₁ ∈ L := (S.tor d₁).2.2
  have hS' : ∀ d : D8Mod p K,
      ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d)) = spQ K (torusElt p d) := hS
  have hb₀ : spQ K (b7 ζ) = ε ⟨x₀, hx₀L⟩ := by
    have h0 := hS' d₀
    rw [torusElt_one_z] at h0
    exact h0.symm
  have hb₁ : spQ K (b7' ζ) = ε ⟨x₁, hx₁L⟩ := by
    have h0 := hS' d₁
    rw [torusElt_same] at h0
    exact h0.symm
  obtain ⟨t₀, ht₀L, hr₀, hfix₀, hKF₀, hle₀, hmap₀⟩ := row7_class0' hGA h hEA hcL hA hf3 hK hζ ε hε hAT
    (hEA ▸ hx₀E) hx₀L hb₀
  obtain ⟨t₁, ht₁L, hr₁, hfix₁, hKF₁, hle₁, hmap₁⟩ := row7_class1' hGA h hEA hcL hA hf3 hK hζ ε hε hAT
    (hEA ▸ hx₁E) hx₁L hb₁
  have hW₀ : weylE S R hp hp2 hζex ⟨t₀, ht₀L⟩ = DihedralGroup.sr 0 :=
    weylE_eq_of_fix S R hp hp2 hζex ht₀L hr₀ (d := d₀) (i₀ := 0) (hfix₀ hx₀E)
      (fun i hi => eq_zero_of_sr_fix_one hz1 hz2 hi)
  have hW₁ : weylE S R hp hp2 hζex ⟨t₁, ht₁L⟩ = DihedralGroup.sr 3 :=
    weylE_eq_of_fix S R hp hp2 hζex ht₁L hr₁ (d := d₁) (i₀ := 3) (hfix₁ hx₁E)
      (fun i hi => eq_three_of_sr_fix_same hz2 hi)
  have hrs₀ : t₀ ∈ reflectionSet p E := ⟨hr₀, L, hF13.inZeroStar, ht₀L⟩
  have hrs₁ : t₁ ∈ reflectionSet p E := ⟨hr₁, L, hF13.inZeroStar, ht₁L⟩
  have hord : orderOf (t₀ * t₁) = 4 := by
    have h1 : orderOf ((⟨t₀, ht₀L⟩ : ↥(torusImage E L)) * ⟨t₁, ht₁L⟩) = orderOf (t₀ * t₁) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [← h1, ← MulEquiv.orderOf_eq (weylE S R hp hp2 hζex), map_mul, hW₀, hW₁,
      DihedralGroup.sr_mul_sr, DihedralGroup.orderOf_r]
    decide
  exact ⟨hZL, K, hKf, hKfin, hchar, hK, ε, hε, ζ, hζ, hAT, t₀, t₁, hrs₀, ht₀L, hrs₁, ht₁L, hord,
    hKF₀, hKF₁, hle₀, hle₁, hmap₀, hmap₁⟩

end CFSG.RankThree.PartOne.NF7J
