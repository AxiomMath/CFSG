module

public import CFSG.Quasithin.H13.NQS13410C
public import CFSG.Quasithin.H13.NQS13410E
public import CFSG.Quasithin.H13.NQS1345

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_three_K (h1332 : Stmt13_3_2) (S : A6.Setting134 G T L V) {K W : Subgroup G}
    (hKf : quasithinIsFaithfulLocal T K) (hKW : K ≤ normalizer (W : Set G))
    (hTW : T ≤ normalizer (W : Set G)) (hW1 : W ≠ ⊥) (hW2 : IsPGroup 2 ↥W)
    (hmod : ∃ _ : IsMulCommutative ↥W,
      (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 5 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
        (AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6 ∧ W ⊓ centralizer (K : Set G) = ⊥) ∨
        (Nat.card W = 2 ^ 5 ∧ Nat.card ↥(W ⊓ centralizer (K : Set G)) = 2 ∧
          FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥) ∨
        (LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∧
          BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1 ∧ W ⊓ centralizer (K : Set G) = ⊥)) :
    ∃ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) ∧ y ∉ centralizer (W : Set G) ∧
      y ^ 3 ∈ centralizer (W : Set G) ∧
      ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y := by
  obtain ⟨-, ⟨hTK, -, -, huniqK⟩, -, -⟩ := h1332 G T L S.h13 K hKf
  have hTsyl : IsSylowTwoOf T (K ⊔ T) := ⟨le_sup_right, hKf.1.1, hKf.1.2.2.1⟩
  have hsyl : IsSylowTwoOf (T ⊓ K) K :=
    A4.isSylowTwoOf_inf_normal hTsyl le_sup_left (sup_le le_normalizer hTK)
  have hNL : normalizer (W : Set G) ≤ normalizer (K : Set G) := by
    obtain ⟨M', hM', hle⟩ := exists_maxTwoLocal_ge
      (⟨W, hW1, hW2, rfl⟩ : IsTwoLocal (normalizer (W : Set G)))
    have := huniqK M' hM' ((sup_le hKW hTW).trans hle)
    exact this ▸ hle
  have hT2 : IsPGroup 2 ↥T := S.h13.sylow.1
  obtain ⟨hab, h5 | h6 | hc | hl⟩ := hmod
  · obtain ⟨R⟩ := A5.exists_rawData5_of_nat hKW h5.1
    obtain ⟨F⟩ := A5.exists_frame R hNL hT2 hTW hsyl
    exact exists_three_of_a5Frame F
  · obtain ⟨R⟩ := exists_rawData4 hKW h6.1
    obtain ⟨F⟩ := exists_frame4 R hNL hT2 hTW hsyl
    exact exists_three_of_frame4 F
  · obtain ⟨R⟩ := exists_rawData6 hKW hc.2.2
    obtain ⟨F⟩ := exists_frame5 R hNL hT2 hTW hsyl
    exact exists_three_of_frame5 F
  · exact exists_three_of_l32 hKW hl.2.1 hsyl

omit [Finite G] in
theorem mem_centralizer_Z_of {K W : Subgroup G} (hTW : T ≤ normalizer (W : Set G))
    (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K) {y : G} (hyK : y ∈ K)
    (hy : ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y) :
    y ∈ centralizer (quasithinOmegaOneCenter T : Set G) := by
  have hZT : quasithinOmegaOneCenter T ≤ T := fun x hx => (U3.s134_Z_le_center T hx).1
  have hcN : U3.cZ T K ≤ normalizer (W : Set G) := (inf_le_left.trans hZT).trans hTW
  rw [mem_centralizer_iff]
  intro x hx
  obtain ⟨w, hw, c, hc, rfl⟩ := Vol2.Ch11.SecC.mem_sup_of_le_normalizer hcN (hZW hx)
  have hcZ : c ∈ quasithinOmegaOneCenter T := (mem_inf.1 hc).1
  have hwZ : w ∈ quasithinOmegaOneCenter T := by
    have : w = w * c * c⁻¹ := by group
    rw [this]
    exact mul_mem hx (inv_mem hcZ)
  have hwT : w ∈ centralizer (T : Set G) := (U3.s134_Z_le_center T hwZ).2
  have h1 := hy w hw hwT
  have h2 : c * y = y * c := (mem_centralizer_iff.mp (mem_inf.1 hc).2 y hyK).symm
  calc w * c * y = w * (y * c) := by rw [mul_assoc, ← h2]
    _ = y * (w * c) := by rw [← mul_assoc, ← h1, mul_assoc]

omit [Finite G] in
theorem L1_le_normalizer_inf {K : Subgroup G} (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G))
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G)) :
    L₁Of L (fsuV1 T V) ≤
      normalizer ((K ⊓ centralizer (quasithinOmegaOneCenter T : Set G) : Subgroup G) : Set G) :=
  fun _ hl => inf_normalizer_le_normalizer_inf ⟨hL1K hl, le_normalizer (hL1Z hl)⟩

theorem pow_nine_eq_one {K W : Subgroup G}
    (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G)) {y : G} (hyK : y ∈ K) {m : ℕ} (hm : Odd m)
    (hym : y ^ m = 1) (hy3 : y ^ 3 ∈ centralizer (W : Set G)) : y ^ 3 ^ 2 = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : y ^ 3 ∈ A6.o2Z K := by
    rw [ho2Z]
    exact mem_inf.2 ⟨pow_mem hyK 3, hy3⟩
  have h2 := cube_mem_pCoreOf_of_o2Z hK _ h1
  obtain ⟨s, hs⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K) ⟨_, h2⟩
  have hs' : (y ^ 3 ^ 2) ^ 2 ^ s = 1 := by
    have h9 : y ^ 3 ^ 2 = (y ^ 3) ^ 3 := by rw [← pow_mul]; norm_num
    have := congrArg Subtype.val hs
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at this
    rw [h9]
    exact this
  have hm' : (y ^ 3 ^ 2) ^ m = 1 := by
    rw [← pow_mul, mul_comm, pow_mul, hym, one_pow]
  have h3 : y ^ 3 ^ 2 ∈ (⊥ : Subgroup G) :=
    mem_of_pow_odd_mem hs' hm (by rw [hm']; exact one_mem _)
  exact mem_bot.1 h3

theorem L1_le_of_a6 (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h56 : AsB56) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hHM : ∃ H : Subgroup G, InH T H ∧ ¬ H ≤ normalizer (L : Set G)) {K W : Subgroup G}
    (hK : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)) ∨
      LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 ∨
      Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)) ∨ A6.IsHatA6 K)
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G)) (hTW : T ≤ normalizer (W : Set G))
    (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    (hy : ∃ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) ∧ y ∉ centralizer (W : Set G) ∧
      y ^ 3 ∈ centralizer (W : Set G) ∧
      ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y) :
    L₁Of L (fsuV1 T V) ≤ K ⊓ centralizer (quasithinOmegaOneCenter T : Set G) := by
  obtain ⟨y, hyK, ⟨m, hm, hym⟩, hyW, hy3, hyfix⟩ := hy
  have hyZ := mem_centralizer_Z_of hTW hZW hyK hyfix
  have hy9 := pow_nine_eq_one hK ho2Z hyK hm hym hy3
  have hy1 : y ≠ 1 := fun h => hyW (h ▸ one_mem _)
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S hHM
  exact L1_le_of_pow_three h1332 h1228 S he (L1_le_normalizer_inf hL1K hL1Z)
    (mem_inf.2 ⟨hyK, hyZ⟩) hyZ hy1 hy9

theorem not_isHatA6_of_a6 (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {K W : Subgroup G}
    (hL1K : L₁Of L (fsuV1 T V) ≤ normalizer (K : Set G)) (hTW : T ≤ normalizer (W : Set G))
    (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (ho2Z : A6.o2Z K = K ⊓ centralizer (W : Set G))
    (hy : ∃ y ∈ K, (∃ m : ℕ, Odd m ∧ y ^ m = 1) ∧ y ∉ centralizer (W : Set G) ∧
      y ^ 3 ∈ centralizer (W : Set G) ∧
      ∀ w ∈ W, w ∈ centralizer (T : Set G) → y * w = w * y) :
    ¬ A6.IsHatA6 K := by
  intro hhat
  obtain ⟨y, hyK, ⟨m, hm, hym⟩, hyW, hy3, hyfix⟩ := hy
  obtain ⟨hperf, hz3, he6⟩ := hhat
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnt : Nontrivial ↥(center (↥K ⧸ CFSG.pCore 2 ↥K)) :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [hz3]; norm_num)
  obtain ⟨c, hc1⟩ := exists_ne (1 : ↥(center (↥K ⧸ CFSG.pCore 2 ↥K)))
  have hc3 : c ^ 3 = 1 := by
    rw [← hz3]
    exact pow_card_eq_one'
  obtain ⟨k, hk⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥K) (c : ↥K ⧸ CFSG.pCore 2 ↥K)
  obtain ⟨y₀, ⟨m₀, hm₀, hy₀m⟩, hy₀ρ, -⟩ := exists_odd_part (QuotientGroup.mk' (CFSG.pCore 2 ↥K))
    k (by rw [hk, ← Subgroup.coe_pow, hc3, Subgroup.coe_one])
  rw [hk] at hy₀ρ
  have hy₀o2Z : (y₀ : G) ∈ A6.o2Z K := ⟨y₀, by
    rw [SetLike.mem_coe, Subgroup.mem_comap, hy₀ρ]
    exact c.2, rfl⟩
  have hy₀1 : (y₀ : G) ≠ 1 := by
    intro h
    apply hc1
    apply Subtype.ext
    rw [← hy₀ρ, show y₀ = 1 from Subtype.ext h, map_one, Subgroup.coe_one]
  have hy₀3 : (y₀ : G) ^ 3 ^ 1 = 1 := by
    have h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥K) (y₀ ^ 3) = 1 := by
      rw [map_pow, hy₀ρ, ← Subgroup.coe_pow, hc3, Subgroup.coe_one]
    have h2 : y₀ ^ 3 ∈ CFSG.pCore 2 ↥K := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨s, hs⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥K)) ⟨_, h2⟩
    have hs' : ((y₀ : G) ^ 3) ^ 2 ^ s = 1 := by
      have h4 : (y₀ ^ 3) ^ 2 ^ s = (1 : ↥K) := by
        have := congrArg (fun x : ↥(CFSG.pCore 2 ↥K) => (x : ↥K)) hs
        simpa using this
      have h5 := congrArg (fun x : ↥K => (x : G)) h4
      simpa using h5
    have hm' : ((y₀ : G) ^ 3) ^ m₀ = 1 := by
      rw [← pow_mul, mul_comm, pow_mul, hy₀m, one_pow]
    have h3 : (y₀ : G) ^ 3 ∈ (⊥ : Subgroup G) :=
      mem_of_pow_odd_mem hs' hm₀ (by rw [hm']; exact one_mem _)
    simpa using mem_bot.1 h3
  have hy₀W : (y₀ : G) ∈ centralizer (W : Set G) := by
    rw [ho2Z] at hy₀o2Z
    exact (mem_inf.1 hy₀o2Z).2
  have hy₀Z := mem_centralizer_Z_of hTW hZW (K := K) y₀.2 fun w hw _ =>
    (mem_centralizer_iff.mp hy₀W w hw).symm
  have hL1N : L₁Of L (fsuV1 T V) ≤ normalizer (A6.o2Z K : Set G) :=
    hL1K.trans A6.normalizer_L_le_o2Z
  have hL1 := L1_le_of_pow_three h1332 h1228 S he hL1N hy₀o2Z hy₀Z hy₀1 hy₀3
  have hyZ := mem_centralizer_Z_of hTW hZW hyK hyfix
  have hy9 := pow_nine_eq_one (Or.inr (Or.inr (Or.inr ⟨hperf, hz3, he6⟩))) ho2Z hyK hm hym hy3
  have hyL1 := mem_L1_of_pow_three h1332 h1228 S he hyZ hy9
  have := hL1 hyL1
  rw [ho2Z] at this
  exact hyW (mem_inf.1 this).2

end CFSG.Quasithin.H13.NQS134
