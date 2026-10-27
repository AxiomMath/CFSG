module

public import CFSG.Quasithin.EmptyFaithful.S152He7Mod
public import CFSG.Quasithin.EmptyFaithful.S152He7Aut
public import CFSG.Quasithin.EmptyFaithful.LRed5Plumb
public import CFSG.Quasithin.Vol2.Ch12Sec4L5Rad

public section

namespace CFSG.Quasithin.He7

open CFSG.Quasithin CFSG.Quasithin.He6 CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Open
  CFSG.QuasithinUnique.Setup.X1
open scoped commutatorElement

variable {W : Type} [CommGroup W] [Finite W]

theorem isPerfect_of_simple_noncomm {K : Type*} [Group K] [IsSimpleGroup K]
    (hK : ∃ x y : K, x * y ≠ y * x) : Group.IsPerfect K := by
  rw [Group.isPerfect_def]
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator K) with h | h
  · exfalso
    obtain ⟨x, y, hxy⟩ := hK
    apply hxy
    have hmem : ⁅x, y⁆ ∈ commutator K := by
      rw [commutator_eq_closure]
      exact Subgroup.subset_closure (commutator_mem_commutatorSet x y)
    rw [h, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.mp hmem
  · exact h

theorem not_isPGroup_two_of_card {Λ : Type*} [Group Λ] [Finite Λ]
    (hN : Nat.card Λ = 20160 ∨ Nat.card Λ = 9999360) : ¬ IsPGroup 2 Λ := by
  intro hp
  obtain ⟨m, hm⟩ := hp.exists_card_eq
  have h3 : 3 ∣ Nat.card Λ := by
    rcases hN with h | h <;> rw [h] <;> norm_num
  rw [hm] at h3
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
  omega

theorem pCoreOf_two_eq_bot_of_simple {Y : Type*} [Group Y] [Finite Y] {Λ : Subgroup Y}
    (hs : IsSimpleGroup ↥Λ) (hnot : ¬ IsPGroup 2 ↥Λ) : pCoreOf 2 Λ = ⊥ := by
  have hn : (CFSG.Open.pCore 2 ↥Λ).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  rcases hs.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 ↥Λ) with h | h
  · unfold pCoreOf
    rw [h]
    exact Subgroup.map_bot _
  · exfalso
    apply hnot
    have hp : IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥Λ) := CFSG.LieType.BorelTits.pCore_isPGroup 2
    rw [h] at hp
    exact hp.of_equiv Subgroup.topEquiv

omit [Finite W] in
theorem fixV_bot : fixV (⊥ : Subgroup (MulAut W)) = ⊤ :=
  CFSG.QuasithinUnique.Setup.X1.fixV_bot

theorem isFFStarOffender_of_transvection (hW : ∀ w : W, w * w = 1) {Λ : Subgroup (MulAut W)}
    {ζ : MulAut W} (hζ : ζ ∈ Λ) (hζ1 : ζ ≠ 1) (hζi : (fixV (Subgroup.zpowers ζ)).index = 2) :
    IsFFStarOffender Λ (Subgroup.zpowers ζ) ∧ Nat.card (Subgroup.zpowers ζ) = 2 := by
  have hsq : ζ * ζ = 1 := sq_eq_one_of_index_two hW hζi
  have hord : orderOf ζ = 2 := orderOf_eq_prime (by rw [sq]; exact hsq) hζ1
  have hcard : Nat.card (Subgroup.zpowers ζ) = 2 := by rw [Nat.card_zpowers, hord]
  refine ⟨⟨Subgroup.zpowers_le.2 hζ, ?_, ⟨?_, ?_⟩, ?_⟩, hcard⟩
  · intro h
    exact hζ1 (Subgroup.zpowers_eq_bot.1 h)
  · rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
    exact (Commute.zpow_zpow_self ζ i j).eq
  · rintro a ⟨i, rfl⟩
    have h2 : ζ ^ 2 = 1 := by rw [sq]; exact hsq
    calc (ζ ^ i) ^ 2 = (ζ ^ 2) ^ i := by
          rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, mul_comm]
      _ = 1 := by rw [h2, one_zpow]
  · intro B hBA
    have hBdvd : Nat.card B ∣ Nat.card (Subgroup.zpowers ζ) := Subgroup.card_dvd_of_le hBA
    have hfix : Nat.card (fixV (Subgroup.zpowers ζ)) * 2 = Nat.card W := by
      have := Subgroup.card_mul_index (fixV (Subgroup.zpowers ζ))
      rw [hζi] at this
      exact this
    rcases (Nat.dvd_prime Nat.prime_two).1 (hcard ▸ hBdvd) with h1 | h2
    · have hB : B = ⊥ := Subgroup.card_eq_one.1 h1
      rw [hB, fixV_bot, Subgroup.card_bot, Subgroup.card_top, hcard]
      omega
    · have hBA' : B = Subgroup.zpowers ζ :=
        Subgroup.eq_of_le_of_card_ge hBA (by rw [hcard, h2])
      rw [hBA']

theorem mem_zpowers_eq_one_or {G : Type*} [Group G] {a x : G} (ha : orderOf a = 2)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  have h := zpow_mod_orderOf a k
  have h2 : ((orderOf a : ℕ) : ℤ) = 2 := by rw [ha]; rfl
  rw [h2] at h
  rw [← h]
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · left
    rw [h0, zpow_zero]
  · right
    rw [h1, zpow_one]

theorem exists_two_forms : ∀ v : Fin 5 → ZMod 2, v ≠ 0 →
    ∃ φ₁ φ₂ : Fin 5 → ZMod 2, φ₁ ⬝ᵥ v = 0 ∧ φ₂ ⬝ᵥ v = 0 ∧ Matrix.vecMulVec v φ₁ ≠ 0 ∧
      Matrix.vecMulVec v φ₂ ≠ 0 ∧ Matrix.vecMulVec v φ₁ ≠ Matrix.vecMulVec v φ₂ := by
  decide +kernel

theorem exists_two_vectors : ∀ φ : Fin 5 → ZMod 2, φ ≠ 0 →
    ∃ w₁ w₂ : Fin 5 → ZMod 2, φ ⬝ᵥ w₁ = 0 ∧ φ ⬝ᵥ w₂ = 0 ∧ Matrix.vecMulVec w₁ φ ≠ 0 ∧
      Matrix.vecMulVec w₂ φ ≠ 0 ∧ Matrix.vecMulVec w₁ φ ≠ Matrix.vecMulVec w₂ φ := by
  decide +kernel

theorem card_perm_fin (m : ℕ) : Nat.card (Equiv.Perm (Fin m)) = m.factorial := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]

theorem b42_out_false (hB42 : AsB42) (hW : ∀ w : W, w * w = 1) {Λ : Subgroup (MulAut W)}
    (hN : Nat.card ↥Λ = 20160 ∨ Nat.card ↥Λ = 9999360) (hs : IsSimpleGroup ↥Λ)
    (hSQ : SQTKGroup ↥Λ) (hirr : ∀ U : Subgroup W, (∀ l ∈ Λ, ∀ u ∈ U, l u ∈ U) → U = ⊥ ∨ U = ⊤)
    {ζ : MulAut W} (hζ : ζ ∈ Λ) (hζ1 : ζ ≠ 1) (hζi : (fixV (Subgroup.zpowers ζ)).index = 2)
    {s : MulAut W} (hsΛ : ∀ l ∈ Λ, s * l * s⁻¹ ∈ Λ)
    (hout : ¬ ∃ l ∈ Λ, ∀ x ∈ Λ, s * x * s⁻¹ = l * x * l⁻¹) : False := by
  classical
  have := hs
  have hV2 : ∀ v : W, v ^ 2 = 1 := fun v => by rw [sq]; exact hW v
  have hnc : ∃ a b : ↥Λ, a * b ≠ b * a := by
    by_contra hcomm
    push Not at hcomm
    have : IsMulCommutative ↥Λ := ⟨⟨fun a b => hcomm a b⟩⟩
    have hp := IsSimpleGroup.prime_card (α := ↥Λ)
    rcases hN with h | h <;> rw [h] at hp <;> norm_num at hp
  have hperf : Group.IsPerfect ↥Λ := isPerfect_of_simple_noncomm hnc
  have hq : CFSG.IsQuasisimple ↥Λ := LRed5.isQuasisimple_of_simple_nonabelian hperf hnc
  have hqo : CFSG.Open.IsQuasisimple ↥Λ := ⟨Group.isPerfect_def.1 hperf, hq.2.1⟩
  have hO2 : pCoreOf 2 Λ = ⊥ := pCoreOf_two_eq_bot_of_simple hs (not_isPGroup_two_of_card hN)
  have hfst : quasithinGenFitting Λ = Λ :=
    InternalSec.quasithinGenFitting_eq_of_two_pow le_rfl
      (fun y hy l hl => Λ.mul_mem (Λ.mul_mem hy hl) (Λ.inv_mem hy)) hqo
      (fun y hy => ⟨0, by simpa using hy⟩) hO2
  have hnt : (⊤ : Subgroup W) ≠ ⊥ := fun h => hζ1 (MulEquiv.ext fun w => by
    have : w ∈ (⊥ : Subgroup W) := h ▸ Subgroup.mem_top w
    rw [Subgroup.mem_bot.1 this, map_one]
    rfl)
  have hirrΛ : XMod.IsIrrSec ↥Λ (⊥ : Subgroup W) ⊤ :=
    ⟨bot_lt_iff_ne_bot.2 hnt, fun J hJ _ _ => hirr J (fun l hl u hu => hJ ⟨l, hl⟩ u hu)⟩
  have hb4 : B4Hyp Λ Λ := ⟨hSQ, hfst.symm, hq, hirrΛ⟩
  obtain ⟨hA, hAcard⟩ := isFFStarOffender_of_transvection hW hζ hζ1 hζi
  have hsq : ζ * ζ = 1 := sq_eq_one_of_index_two hW hζi
  have hord : orderOf ζ = 2 := orderOf_eq_prime (by rw [sq]; exact hsq) hζ1
  have hrk : rk ↥(Subgroup.zpowers ζ) = 1 := by
    unfold rk
    rw [hAcard]
    exact padicValNat.self (by norm_num)
  have hffJ : ffJ Λ = Λ := by
    have hle : ffJ Λ ≤ Λ := EmptyFaithfulMultiple.FFL.ffJ_le Λ
    have hA' : Subgroup.zpowers ζ ≤ ffJ Λ := B19.le_ffJ hA
    rcases eq_bot_or_eq_of_normal' hs hle (fun g hg m hm =>
      (Subgroup.mem_normalizer_iff.mp (EmptyFaithfulMultiple.FFL.le_normalizer_ffJ Λ hg) m).mp hm)
      with h | h
    · exfalso
      apply hζ1
      have : ζ ∈ ffJ Λ := hA' (Subgroup.mem_zpowers ζ)
      rw [h, Subgroup.mem_bot] at this
      exact this
    · exact h
  have hconcl := hB42 W hV2 Λ Λ hb4 _ hA
  unfold B42Conclusion B42Case1 B42Case2 B42Case3 B42Case4 B42Case5 B42Case6 B42Case7 B42Case8
    B42Case9 B42Case10 B42Case11 at hconcl
  rcases hconcl with ⟨_, ⟨m, h⟩, _, _⟩ | ⟨_, ⟨m, h⟩, _⟩ | ⟨⟨m, h, _⟩, _⟩ | ⟨⟨m, h, _, _⟩, _⟩ |
    ⟨⟨m, hm, π, hπ, _⟩, _⟩ | ⟨_, h, _, _, _⟩ | ⟨_, _, h, _, _, _⟩ |
    ⟨_, _, _, K, hKF, hKfin, Γ₀, hK4, hdet, hhat, hcen, π, hπ, _⟩ | ⟨_, n, _, h, _⟩ |
    ⟨_, hi | hii⟩ | ⟨_, _, _, _, π, hπ, hrad⟩
  · exact not_binaryNaturalSL_two1527d hN h
  · exact not_binaryNaturalSL_three1527d hN h
  · rw [hffJ] at h
    exact not_binaryNaturalSp4_1527d hN h
  · rw [hffJ] at h
    exact not_g2Natural1527d hN h
  ·
    have h1 : Nat.card ↥(ffJ Λ) ≤ Nat.card (Equiv.Perm (Fin m)) :=
      Nat.card_le_card_of_surjective π hπ.1
    have h2 : Nat.card ↥(ffJ Λ) = Nat.card ↥Λ := by rw [hffJ]
    rw [h2, card_perm_fin] at h1
    rcases hm with rfl | rfl <;> rcases hN with h | h <;> rw [h] at h1 <;>
      norm_num [Nat.factorial] at h1
  · exact not_alternatingNatural1527d (n := 6) (by norm_num)
      (by rcases hN with h | h <;> rw [h] <;> norm_num [Nat.factorial]) h
  · exact not_a7Four1527d hN h
  · exact not_tripleA6Six1527d hN ⟨K, hKF, hKfin, Γ₀, hK4, hdet, hhat, hcen, π, hπ⟩
  ·
    obtain ⟨π, hπ⟩ := FFC.BinaryNaturalSL.exists_zmod h
    refine hout (LRed5.inner_of_natural_section hπ (fun u _ => Subgroup.mem_top _)
      (fun u _ => Subgroup.mem_top _) (fun z hz => ?_) (fun z hz => ?_) hsΛ)
    · rw [Subgroup.mem_bot.1 hz, map_one]
      exact Subgroup.one_mem _
    · rw [Subgroup.mem_bot.1 hz, map_one]
      exact Subgroup.one_mem _
  ·
    obtain ⟨_, _, hrk3, _⟩ := hi
    rw [hrk] at hrk3
    omega
  ·
    obtain ⟨_, ⟨e⟩, _⟩ := hii
    have h1 := Nat.card_congr e.toEquiv
    rw [card_perm_fin] at h1
    rcases hN with h | h <;> rw [h] at h1 <;> norm_num [Nat.factorial] at h1
  ·
    have hinj : Function.Injective π :=
      FFC.injective_of_faithful_sec (FFC.extSq_faithful (by norm_num)) hπ
    have hBmem : ∀ g : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)),
        g ∈ ((Subgroup.zpowers ζ).subgroupOf Λ).comap π → (g = 1 ∨ π g = ⟨ζ, hζ⟩) := by
      intro g hg
      have h1 : ((π g : ↥Λ) : MulAut W) ∈ Subgroup.zpowers ζ := hg
      rcases mem_zpowers_eq_one_or hord h1 with h2 | h2
      · left
        apply hinj
        apply Subtype.ext
        rw [map_one]
        exact h2
      · right
        exact Subtype.ext h2
    have hcontra : ∀ g₁ g₂ : ↥(CFSG.Assembly.LowTwoRank.StatedSL 5 (ZMod 2)),
        g₁ ∈ ((Subgroup.zpowers ζ).subgroupOf Λ).comap π →
        g₂ ∈ ((Subgroup.zpowers ζ).subgroupOf Λ).comap π → g₁ ≠ 1 → g₂ ≠ 1 → g₁ = g₂ := by
      intro g₁ g₂ h₁ h₂ h₁1 h₂1
      rcases hBmem g₁ h₁ with h | h
      · exact absurd h h₁1
      rcases hBmem g₂ h₂ with h' | h'
      · exact absurd h' h₂1
      exact hinj (h.trans h'.symm)
    have hne1 : ∀ X : Matrix (Fin 5) (Fin 5) (ZMod 2), X ≠ 0 →
        (1 + X : Matrix (Fin 5) (Fin 5) (ZMod 2)) ≠ 1 :=
      fun X hX h => hX (by simpa using h)
    rcases hrad with ⟨v, hv, hmem⟩ | ⟨φ, hφ, hmem⟩
    · obtain ⟨φ₁, φ₂, h₁, h₂, hX₁, hX₂, hX₁₂⟩ := exists_two_forms v hv
      have hg₁ : H13.radElt v φ₁ h₁ ∈ ((Subgroup.zpowers ζ).subgroupOf Λ).comap π :=
        (hmem _).2 ⟨φ₁, h₁, H13.mat5_radElt v φ₁ h₁⟩
      have hg₂ : H13.radElt v φ₂ h₂ ∈ ((Subgroup.zpowers ζ).subgroupOf Λ).comap π :=
        (hmem _).2 ⟨φ₂, h₂, H13.mat5_radElt v φ₂ h₂⟩
      have hn₁ : H13.radElt v φ₁ h₁ ≠ 1 := fun h => hne1 _ hX₁ (by
        have := congrArg H13.mat5 h
        rwa [H13.mat5_radElt, H13.mat5_one] at this)
      have hn₂ : H13.radElt v φ₂ h₂ ≠ 1 := fun h => hne1 _ hX₂ (by
        have := congrArg H13.mat5 h
        rwa [H13.mat5_radElt, H13.mat5_one] at this)
      have heq := hcontra _ _ hg₁ hg₂ hn₁ hn₂
      apply hX₁₂
      have := congrArg H13.mat5 heq
      rw [H13.mat5_radElt, H13.mat5_radElt] at this
      exact add_left_cancel this
    · obtain ⟨w₁, w₂, h₁, h₂, hX₁, hX₂, hX₁₂⟩ := exists_two_vectors φ hφ
      have hg₁ : H13.radElt w₁ φ h₁ ∈ ((Subgroup.zpowers ζ).subgroupOf Λ).comap π :=
        (hmem _).2 ⟨w₁, h₁, H13.mat5_radElt' w₁ φ h₁⟩
      have hg₂ : H13.radElt w₂ φ h₂ ∈ ((Subgroup.zpowers ζ).subgroupOf Λ).comap π :=
        (hmem _).2 ⟨w₂, h₂, H13.mat5_radElt' w₂ φ h₂⟩
      have hn₁ : H13.radElt w₁ φ h₁ ≠ 1 := fun h => hne1 _ hX₁ (by
        have := congrArg H13.mat5 h
        rwa [H13.mat5_radElt', H13.mat5_one] at this)
      have hn₂ : H13.radElt w₂ φ h₂ ≠ 1 := fun h => hne1 _ hX₂ (by
        have := congrArg H13.mat5 h
        rwa [H13.mat5_radElt', H13.mat5_one] at this)
      have heq := hcontra _ _ hg₁ hg₂ hn₁ hn₂
      apply hX₁₂
      have := congrArg H13.mat5 heq
      rw [H13.mat5_radElt', H13.mat5_radElt'] at this
      exact add_left_cancel this

end CFSG.Quasithin.He7
