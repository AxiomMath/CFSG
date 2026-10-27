module

public import CFSG.RankThree.PartOne.KF.F132SL2Refl
public import CFSG.RankThree.PartOne.KF.F132D8
public import CFSG.RankThree.PartOne.KF.F132Center
public import CFSG.RankThree.PartOne.KF.R8LeviA
public import CFSG.RankThree.PartOne.KFOUT3.KtyRow8
public import CFSG.RankThree.PartOne.S13K.KF132At
public import CFSG.RankThree.PartOne.KF.R8Levi
public import CFSG.RankThree.PartOne.KFOUT3.KtyCore

public section

namespace CFSG.RankThree.PartOne.KF132

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
  CFSG.Assembly.LowTwoRank

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f : ℕ}

theorem row8_classA (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (hZL : Subgroup.center L = ⊥) (hf2 : 2 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p) {z : rootsOfUnity p (Qext K)} (hz1 : z ≠ 1)
    (ε : ↥L →* StatedProj (StatedSL 4 K)) (hε : IsCentralPQuot p ε)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (T8 p K).map (q8 K))
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L) (hx1 : x ≠ 1)
    (hb : ε ⟨x, hxL⟩ = q8 K (bA hp hp2 hpq z)) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E f t ∧ kZero p E t ≤ L ∧
      ((kZero p E t).subgroupOf L).map ε = (blkA (K := K) 0).range.map (q8 K) := by
  have hq : IsCentralPQuot p (q8 K) := isCentralPQuot_m8 p
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hεinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZL]
    exact hε.central
  have hqinj : Function.Injective (q8 K) := (KFOUT3.m8Iso (K := K)).injective
  exact reflection_of_cover_sl2 h hEA hcL ε (q8 K) hε hq hεinj hqinj hxA hxL hx1
    (T8_pow_eq_one (bA_mem_T8 hp hp2 hpq z)) hb (fun t ht => T8_pow_eq_one ht) hAT hK hf2
    (blkA_injective (K := K) 0) (perfectResidual_centralizer_bA hK4 hz1)
    (card_T8_inf_range_blkA hp hp2 hpq hζ)

theorem row8_classB' (h : Sec12Hyp G p A c L E) (hEA : E = A) (hcL : c ∉ L)
    (hZL : Subgroup.center L = ⊥) (hf2 : 2 ≤ f)
    {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2 ^ f)
    (hp : p.Prime) (hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p) {z : (Qext K)ˣ} (hzp : z ^ p = 1)
    (hzK : (z : Qext K) ∉ Set.range (algebraMap K (Qext K)))
    (hmem : torusEquiv ![z, z] ∈ M8 K)
    (ε : ↥L →* StatedProj (StatedSL 4 K)) (hε : IsCentralPQuot p ε)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (T8 p K).map (q8 K))
    {x : G} (hxA : x ∈ A) (hxL : x ∈ L) (hx1 : x ≠ 1) (hb : ε ⟨x, hxL⟩ = q8 K (bM8 z hmem)) :
    ∃ t : MulAut E, t ∈ torusImage E L ∧ IsAutReflection p E t ∧
      (∀ hxE : x ∈ E, ((t ⟨x, hxE⟩ : E) : G) = x) ∧ KFAt p E (2 * f) t ∧ kZero p E t ≤ L ∧
      ((kZero p E t).subgroupOf L).map ε = (blk8M (K := K)).range.map (q8 K) := by
  have hq : IsCentralPQuot p (q8 K) := isCentralPQuot_m8 p
  have hKq : Nat.card (Qext K) = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have hK'4 : 4 ≤ Nat.card (Qext K) := by rw [hKq]; nlinarith
  have hK2 : Nat.card (Qext K) = 2 ^ (2 * f) := by rw [hKq, hK, ← pow_mul, mul_comm]
  have hεinj : Function.Injective ε := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff, ← hZL]
    exact hε.central
  have hqinj : Function.Injective (q8 K) := (KFOUT3.m8Iso (K := K)).injective
  exact reflection_of_cover_sl2 h hEA hcL ε (q8 K) hε hq hεinj hqinj hxA hxL hx1
    (T8_pow_eq_one (bM8_mem_T8 hmem hzp)) hb (fun t ht => T8_pow_eq_one ht) hAT hK2 (by omega)
    (blk8M_injective (K := K)) (perfectResidual_centralizer_b8 hK'4 hzK hmem)
    (card_T8_inf_range hp.pos hζ)

omit [Finite G] in
theorem map_subgroupOf_conjBy {P : Type} [Group P] (ε : ↥L →* P) {K₀ : Subgroup G} (hK₀ : K₀ ≤ L)
    (w : ↥L) :
    ((conjBy (w : G) K₀).subgroupOf L).map ε =
      ((K₀.subgroupOf L).map ε).map (MulAut.conj (ε w)).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨k, hk, hku⟩ := hu
    have hkL : k ∈ L := hK₀ hk
    refine ⟨ε ⟨k, hkL⟩, ⟨⟨k, hkL⟩, hk, rfl⟩, ?_⟩
    have : u = w * ⟨k, hkL⟩ * w⁻¹ := by
      apply Subtype.ext
      have h1 : (w : G) * k * (w : G)⁻¹ = (u : G) := hku
      rw [← h1]
      rfl
    rw [this, map_mul, map_mul, map_inv]
    rfl
  · rintro ⟨_, ⟨v, hv, rfl⟩, rfl⟩
    refine ⟨w * v * w⁻¹, ⟨(v : G), hv, rfl⟩, ?_⟩
    rw [map_mul, map_mul, map_inv]
    rfl

section Main

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem row8_main (h : Sec12Hyp G p A c L E) (hF13 : Sec13Facts G p A c L E) (hEA : E = A)
    (hG : Sec12TwoGeneric p c L E) (hZL : Subgroup.center L = ⊥) (hf2 : 2 ≤ f)
    (hK : Nat.card K = 2 ^ f) (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1)
    (hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p) {z : rootsOfUnity p (Qext K)} (hz1 : z ≠ 1)
    (hzK : (((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ) : Qext K) ∉
      Set.range (algebraMap K (Qext K)))
    (ε : ↥L →* StatedProj (StatedSL 4 K)) (hε : IsCentralPQuot p ε)
    (hAT : ((A ⊓ L).subgroupOf L).map ε = (T8 p K).map (q8 K))
    (S : D8Ctx p (Qext K) L (E ⊓ L))
    (hS : ∀ d : D8Mod p (Qext K), ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d)) =
      q8 K (KFOUT3.T8 hp hp2 hpq d)) :
    (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s ∨ KFAt p E (2 * f) s) ∧
      ∃ r₀ r₁ r₀' : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧
        r₁ ∈ reflectionSet p E ∧ r₁ ∈ torusImage E L ∧ r₀' ∈ reflectionSet p E ∧
        r₀' ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧ KFAt p E f r₀ ∧ KFAt p E (2 * f) r₁ ∧
        KFAt p E f r₀' ∧
        ((kZero p E r₀).subgroupOf L).map ε = (blkA (K := K) 0).range.map (q8 K) ∧
        ((kZero p E r₁).subgroupOf L).map ε = (blk8M (K := K)).range.map (q8 K) ∧
        ((kZero p E r₀').subgroupOf L).map ε = (blkA (K := K) 1).range.map (q8 K) ∧
        (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
          s' ∈ torusImage E L → orderOf (s * s') = 4 →
            ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
              (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
              (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
                s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹)) ∧
        ∃ (w : G) (hwL : w ∈ L) (hwE : w ∈ Subgroup.normalizer (E : Set G)),
          r₀' = conjAut E w hwE * r₀ * (conjAut E w hwE)⁻¹ ∧ ε ⟨w, hwL⟩ = q8 K swapM := by
  classical
  have h5 := Sec12Three.five_le h
  have : Fact p.Prime := ⟨hp⟩
  have hcL : c ∉ L := h.c_not_mem_of_generic hG
  have R : Sec12Three.Restr c L E (E ⊓ L) := h.restr_of_generic hG
  have hA : A ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by
    have hAL : A ⊓ L = E ⊓ L := by rw [hEA]
    calc A = E := hEA.symm
      _ = (E ⊓ L) ⊔ Subgroup.zpowers c := hG.E_eq
      _ ≤ Subgroup.zpowers c ⊔ (A ⊓ L) := by rw [sup_comm, hAL]
  have hz2 : z ^ 2 ≠ 1 := fun h1 => hz1 (eq_one_of_sq_eq_one_of_odd (hp.odd_of_ne_two hp2) h1)
  have hzp : ((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ) ^ p = 1 := (mem_rootsOfUnity p _).mp z.2
  have hzu1 : ((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ) ≠ 1 := fun h1 => hz1 (Subtype.ext h1)
  have hmem : torusEquiv ![((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ),
      ((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ)] ∈ M8 K :=
    d8Emb_mem_M8 hp hp2 hpq (z, z)
  have hζex : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p := hζ
  set d₀ : D8Mod p (Qext K) := ((1 : rootsOfUnity p (Qext K)), z) with hd₀
  set d₁ : D8Mod p (Qext K) := (z, z) with hd₁
  set x₀ : G := ((S.tor d₀ : ↥(E ⊓ L)) : G) with hx₀
  set x₁ : G := ((S.tor d₁ : ↥(E ⊓ L)) : G) with hx₁
  have hx₀E : x₀ ∈ E := (S.tor d₀).2.1
  have hx₀L : x₀ ∈ L := (S.tor d₀).2.2
  have hx₁E : x₁ ∈ E := (S.tor d₁).2.1
  have hx₁L : x₁ ∈ L := (S.tor d₁).2.2
  have hx₀1 : x₀ ≠ 1 := by
    intro h1
    have h2 : S.tor d₀ = 1 := Subtype.ext h1
    have h3 : d₀ = 1 := (map_eq_one_iff S.tor S.tor.injective).1 h2
    exact hz1 (congrArg Prod.snd h3)
  have hx₁1 : x₁ ≠ 1 := by
    intro h1
    have h2 : S.tor d₁ = 1 := Subtype.ext h1
    have h3 : d₁ = 1 := (map_eq_one_iff S.tor S.tor.injective).1 h2
    exact hz1 (congrArg Prod.fst h3)
  have hb₀ : ε ⟨x₀, hx₀L⟩ = q8 K (bA hp hp2 hpq z) := hS d₀
  have hb₁ : ε ⟨x₁, hx₁L⟩ = q8 K (bM8 ((z : rootsOfUnity p (Qext K)) : (Qext K)ˣ) hmem) := hS d₁
  obtain ⟨t₀, ht₀L, hr₀, hfix₀, hKF₀, hK₀L, hmap₀⟩ := row8_classA h hEA hcL hZL hf2 hK hp hp2 hpq hζ
    hz1 ε hε hAT (hEA ▸ hx₀E) hx₀L hx₀1 hb₀
  obtain ⟨t₁, ht₁L, hr₁, hfix₁, hKF₁, hK₁L, hmap₁⟩ := row8_classB' h hEA hcL hZL hf2 hK hp hζ hzp
    hzK hmem ε hε hAT (hEA ▸ hx₁E) hx₁L hx₁1 hb₁
  have hW₀ : weylE S R hp hp2 hζex ⟨t₀, ht₀L⟩ = DihedralGroup.sr 0 :=
    weylE_eq_of_fix S R hp hp2 hζex ht₀L hr₀ (d := d₀) (i₀ := 0) (hfix₀ hx₀E)
      (fun i hi => eq_zero_of_sr_fix_one hz1 hz2 hi)
  have hW₁ : weylE S R hp hp2 hζex ⟨t₁, ht₁L⟩ = DihedralGroup.sr 3 :=
    weylE_eq_of_fix S R hp hp2 hζex ht₁L hr₁ (d := d₁) (i₀ := 3) (hfix₁ hx₁E)
      (fun i hi => eq_three_of_sr_fix_same hz2 hi)
  have hrs₀ : t₀ ∈ reflectionSet p E := ⟨hr₀, L, hF13.inZeroStar, ht₀L⟩
  have hrs₁ : t₁ ∈ reflectionSet p E := ⟨hr₁, L, hF13.inZeroStar, ht₁L⟩
  have hv0 : (0 : ZMod 4).val = 0 := rfl
  have hv3 : (3 : ZMod 4).val = 3 := rfl
  have hall : ∀ s ∈ reflectionSet p E, s ∈ torusImage E L →
      KFAt p E f s ∨ KFAt p E (2 * f) s := by
    intro s hs hsL
    obtain ⟨i, hi⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s, hsL⟩).1 hs.1
    have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · exact Or.inl (kfAt_of_parity S R hp hp2 hζex hW₀ hi (by rw [hv0]; omega) hKF₀)
    · exact Or.inr (kfAt_of_parity S R hp hp2 hζex hW₁ hi (by rw [hv3]; omega) hKF₁)
  obtain ⟨w₀, hw₀⟩ := hε.surjective (q8 K swapM)
  have hexpF : ∀ y : ↥(E ⊓ L), (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) y) ^ p = 1 :=
    fun y => Subtype.ext (Sec12Three.pow_eq_one_of_mem_E h (Subgroup.mem_inf.mp y.2).1)
  have hconj : ∀ l : ↥L, ε l = q8 K swapM → ∀ d : D8Mod p (Qext K),
      (l : G) * ((S.tor d : ↥(E ⊓ L)) : G) * (l : G)⁻¹ =
        ((S.tor (d.2, d.1) : ↥(E ⊓ L)) : G) := by
    intro l hl d
    have hcomm : (swapM : ↥(M8 K)) * KFOUT3.T8 hp hp2 hpq d * (swapM : ↥(M8 K))⁻¹ =
        KFOUT3.T8 hp hp2 hpq (d.2, d.1) := by
      rw [swapM_inv]
      apply Subtype.ext
      exact gSwap_d8Emb d
    have h1 : ε (l * Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d) * l⁻¹) =
        ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor (d.2, d.1))) := by
      rw [map_mul, map_mul, map_inv, hl, hS d, hS (d.2, d.1), ← hcomm, map_mul, map_mul, map_inv]
    have hpow : (l * Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d) * l⁻¹) ^ p = 1 := by
      rw [conj_pow, hexpF, mul_one, mul_inv_cancel]
    have h2 := hε.eq_of_map_eq hpow (hexpF _) h1
    exact congrArg (fun y : ↥L => (y : G)) h2
  have hw₀' : ε w₀⁻¹ = q8 K swapM := by
    rw [map_inv, hw₀, ← map_inv, swapM_inv]
  have hwF : (w₀ : G) ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨d, hd⟩ := S.tor.surjective ⟨y, hy⟩
      have hyd : y = ((S.tor d : ↥(E ⊓ L)) : G) := by rw [hd]
      rw [hyd, hconj w₀ hw₀ d]
      exact (S.tor (d.2, d.1)).2
    · intro hy
      obtain ⟨d, hd⟩ := S.tor.surjective ⟨(w₀ : G) * y * (w₀ : G)⁻¹, hy⟩
      have hyd : (w₀ : G) * y * (w₀ : G)⁻¹ = ((S.tor d : ↥(E ⊓ L)) : G) := by rw [hd]
      have h3 := hconj w₀⁻¹ hw₀' d
      rw [← hyd] at h3
      have h4 : ((w₀⁻¹ : ↥L) : G) * ((w₀ : G) * y * (w₀ : G)⁻¹) * ((w₀⁻¹ : ↥L) : G)⁻¹ = y := by
        simp only [Subgroup.coe_inv, inv_inv]
        group
      rw [h4] at h3
      rw [h3]
      exact (S.tor (d.2, d.1)).2
  have hwE : (w₀ : G) ∈ Subgroup.normalizer (E : Set G) := R.inf_normalizer_ge ⟨w₀.2, hwF⟩
  have hwT : conjAut E (w₀ : G) hwE ∈ torusImage E L :=
    Sec12Three.mem_torusImage_iff.mpr ⟨(w₀ : G), w₀.2, hwE, rfl⟩
  have hrs₀' : conjAut E (w₀ : G) hwE * t₀ * (conjAut E (w₀ : G) hwE)⁻¹ ∈ reflectionSet p E :=
    conj_mem_reflectionSet hp hrs₀ hwE
  have hr₀'L : conjAut E (w₀ : G) hwE * t₀ * (conjAut E (w₀ : G) hwE)⁻¹ ∈ torusImage E L :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hwT ht₀L) (Subgroup.inv_mem _ hwT)
  have hKF₀' : KFAt p E f (conjAut E (w₀ : G) hwE * t₀ * (conjAut E (w₀ : G) hwE)⁻¹) :=
    hKF₀.conj hwE
  have hmap₀' : ((kZero p E (conjAut E (w₀ : G) hwE * t₀ * (conjAut E (w₀ : G) hwE)⁻¹)).subgroupOf
      L).map ε = (blkA (K := K) 1).range.map (q8 K) := by
    rw [kZero_conj p t₀ hwE, map_subgroupOf_conjBy ε hK₀L w₀, hmap₀, hw₀, Subgroup.map_map,
      ← map_conj_swapM_range_blkA, Subgroup.map_map]
    congr 1
    ext x
    simp [MulAut.conj_apply, map_mul, map_inv]
  refine ⟨hall, t₀, t₁, conjAut E (w₀ : G) hwE * t₀ * (conjAut E (w₀ : G) hwE)⁻¹, hrs₀, ht₀L, hrs₁,
    ht₁L, hrs₀', hr₀'L, ?_, hKF₀, hKF₁, hKF₀', hmap₀, hmap₁, hmap₀', ?_,
    (w₀ : G), w₀.2, hwE, rfl, hw₀⟩
  · have h1 : orderOf ((⟨t₀, ht₀L⟩ : ↥(torusImage E L)) * ⟨t₁, ht₁L⟩) = orderOf (t₀ * t₁) := by
      rw [← Subgroup.orderOf_coe]
      rfl
    rw [← h1, ← MulEquiv.orderOf_eq (weylE S R hp hp2 hζex), map_mul, hW₀, hW₁,
      DihedralGroup.sr_mul_sr, DihedralGroup.orderOf_r]
    decide
  · intro s hs hsL s' hs' hs'L hord
    obtain ⟨i, hi⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s, hsL⟩).1 hs.1
    obtain ⟨j, hj⟩ := (isAutReflection_weylE_iff S R hp hp2 hζex ⟨s', hs'L⟩).1 hs'.1
    have hne := parity_ne_of_pair S R hp hp2 hζex hi hj hord
    have hpar : i.val % 2 = 0 ∨ i.val % 2 = 1 := by omega
    rcases hpar with hpar | hpar
    · obtain ⟨x, hxL, hxE, h1, h2⟩ := exists_conj_pair S R hp hp2 hζex hW₀ hW₁ hi hj
        (by rw [hv0]; omega) (by rw [hv3]; omega) hne
      exact ⟨x, hxL, hxE, Or.inl ⟨h1, h2⟩⟩
    · obtain ⟨x, hxL, hxE, h1, h2⟩ := exists_conj_pair S R hp hp2 hζex hW₁ hW₀ hi hj
        (by rw [hv3]; omega) (by rw [hv0]; omega) hne
      exact ⟨x, hxL, hxE, Or.inr ⟨h1, h2⟩⟩

end Main

theorem kf132Row8_frame (hGA : CFSG.Open.GriessAllModelsStatement)
    (h : Sec12Hyp G p A c L E) (hF : Sec12Facts G p A c L E) (hF13 : Sec13Facts G p A c L E)
    (hEA : E = A) (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f + 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSL 4 2 f) :
    Subgroup.center L = ⊥ ∧
      (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → KFAt p E f s ∨ KFAt p E (2 * f) s) ∧
      ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (_ : Nat.card K = 2 ^ f)
        (ε : ↥L →* StatedProj (StatedSL 4 K)), IsCentralPQuot p ε ∧
        ((A ⊓ L).subgroupOf L).map ε = (T8 p K).map (q8 K) ∧
        ∃ r₀ r₁ r₀' : MulAut E, r₀ ∈ reflectionSet p E ∧ r₀ ∈ torusImage E L ∧
          r₁ ∈ reflectionSet p E ∧ r₁ ∈ torusImage E L ∧ r₀' ∈ reflectionSet p E ∧
          r₀' ∈ torusImage E L ∧ orderOf (r₀ * r₁) = 4 ∧ KFAt p E f r₀ ∧ KFAt p E (2 * f) r₁ ∧
          KFAt p E f r₀' ∧
          ((kZero p E r₀).subgroupOf L).map ε = (blkA (K := K) 0).range.map (q8 K) ∧
          ((kZero p E r₁).subgroupOf L).map ε = (blk8M (K := K)).range.map (q8 K) ∧
          ((kZero p E r₀').subgroupOf L).map ε = (blkA (K := K) 1).range.map (q8 K) ∧
          (∀ s ∈ reflectionSet p E, s ∈ torusImage E L → ∀ s' ∈ reflectionSet p E,
            s' ∈ torusImage E L → orderOf (s * s') = 4 →
              ∃ (x : G) (_ : x ∈ L) (hxE : x ∈ Subgroup.normalizer (E : Set G)),
                (s = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹ ∧
                  s' = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹) ∨
                (s = conjAut E x hxE * r₁ * (conjAut E x hxE)⁻¹ ∧
                  s' = conjAut E x hxE * r₀ * (conjAut E x hxE)⁻¹)) ∧
          ∃ (w : G) (hwL : w ∈ L) (hwE : w ∈ Subgroup.normalizer (E : Set G)),
            r₀' = conjAut E w hwE * r₀ * (conjAut E w hwE)⁻¹ ∧ ε ⟨w, hwL⟩ = q8 K swapM := by
  classical
  have hp := h.prime
  have h5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hf2 : 2 ≤ f := by
    by_contra hlt
    have hf : f = 1 := by omega
    subst hf
    have := Nat.le_of_dvd (by norm_num) hpq
    omega
  have hZL : Subgroup.center L = ⊥ := psl_four_center_trivial hGA hf2 hF.isQuasisimple_L hmod
  have hG : Sec12TwoGeneric p c L E := sec12TwoGeneric_of_center_bot hF hZL
  have hcore : Table123Core p L (A ⊓ L) (E ⊓ L) := KFOUT3.table_core_of h hG
  obtain ⟨K, hKf, hKfin, hchar, hK, ε, hε, hFT₁, hFT₂⟩ := exists_r8frame_of hcore hpq hmod
  have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
  have hq : IsCentralPQuot p (q8 K) := isCentralPQuot_m8 (K := K) p
  obtain ⟨m, hmp, hm1, hmK⟩ := exists_root_not_mem hp hp2 hpq'
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_pow hp.ne_zero] at hmp
    exact zero_ne_one hmp
  let zu : (Qext K)ˣ := Units.mk0 m hm0
  have hzup : zu ^ p = 1 := Units.ext (by simpa [zu] using hmp)
  have hzu1 : zu ≠ 1 := fun h1 => hm1 (by simpa [zu] using congrArg Units.val h1)
  let z : rootsOfUnity p (Qext K) := ⟨zu, (mem_rootsOfUnity p _).2 hzup⟩
  have hz1 : z ≠ 1 := fun h1 => hzu1 (congrArg Subtype.val h1)
  have hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p := by
    refine ⟨zu, ?_⟩
    rw [IsPrimitiveRoot.iff_orderOf]
    rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hzup) with h1 | h1
    · exact absurd (orderOf_eq_one_iff.mp h1) hzu1
    · exact h1
  have hAT : ((A ⊓ L).subgroupOf L).map ε = (T8 p K).map (q8 K) := by
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
  obtain ⟨SM, hSM⟩ := KFOUT3.exists_d8ctx_r8' (K := K) hp hp2 hpq'
  have hVexp : ∀ d : D8Mod p (Qext K), d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  obtain ⟨S, hrel⟩ := KFOUT3.wctx_ofCentralQuot' hVexp SM (q8 K) hq ε hε hcore.F_le hcore.F_exp
    hFT₁ hFT₂
  have hS : ∀ d : D8Mod p (Qext K), ε (Subgroup.inclusion (inf_le_right : E ⊓ L ≤ L) (S.tor d)) =
      q8 K (KFOUT3.T8 hp hp2 hpq' d) := fun d => by
    rw [hrel d]
    exact congrArg (q8 K) (hSM d)
  obtain ⟨hall, hrest⟩ := row8_main h hF13 hEA hG hZL hf2 hK hp hp2 hpq' hζ hz1 (by
    intro hmem
    exact hmK (by simpa [zu, z] using hmem)) ε hε hAT S hS
  exact ⟨hZL, hall, K, hKf, hKfin, hchar, hK, ε, hε, hAT, hrest⟩

end CFSG.RankThree.PartOne.KF132

namespace CFSG.RankThree.PartOne.S13K

theorem kf132At_row8 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132At 8 := by
  intro G _ _ p A c L E h hF hF13 hT hr4 hrow hrA hr9 t ht htL
  have hEA : E = A := hrA (by norm_num)
  obtain ⟨f, hf1, hpq, hmod⟩ := hrow
  obtain ⟨-, hall, -⟩ :=
    CFSG.RankThree.PartOne.KF132.kf132Row8_frame hGA h hF hF13 hEA hf1 hpq hmod
  rcases hall t ht htL with h0 | h1
  · exact ⟨f, f, ⟨hf1, hpq, hmod⟩, Or.inl rfl, h0⟩
  · exact ⟨f, 2 * f, ⟨hf1, hpq, hmod⟩, Or.inr rfl, h1⟩

theorem kf132Types_row8 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132Types 8 :=
  kf132Types_of_at (by norm_num) (by norm_num) (by norm_num) (kf132At_row8 hGA)

end CFSG.RankThree.PartOne.S13K
