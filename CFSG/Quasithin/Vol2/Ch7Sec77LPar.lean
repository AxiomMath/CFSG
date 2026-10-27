module

public import CFSG.Quasithin.H13.NQCatNNModCore
public import CFSG.LocalAnalysis.ComponentInitial.SteinbergBXBinaryIndexThreeParabolics

public section

namespace CFSG.Quasithin.H13.LPar

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Vol2Native.A312L CFSG.Quasithin.H13.NQCat

@[expose] def s2 : SpecialLinearGroup (Fin 2) (ZMod 2) := ⟨!![0, 1; 1, 0], by decide⟩

theorem sl2_pow (w : SpecialLinearGroup (Fin 2) (ZMod 2)) : w ^ 2 = 1 ∨ w ^ 3 = 1 := by
  revert w
  decide

theorem sl2_inv (w : SpecialLinearGroup (Fin 2) (ZMod 2)) (h : w ^ 3 = 1) :
    s2 * w * s2⁻¹ = w⁻¹ := by
  revert w
  decide

theorem sl2_normal (w : SpecialLinearGroup (Fin 2) (ZMod 2)) (h2 : w ^ 2 = 1) (h1 : w ≠ 1) :
    ∃ G : SpecialLinearGroup (Fin 2) (ZMod 2), (G * w * G⁻¹ * w) ^ 3 = 1 ∧ G * w * G⁻¹ * w ≠ 1 := by
  revert w
  decide

section Blocks

variable {n : ℕ} {I : Set ℕ}

theorem mem_stabilizer_of_blkAt_eq_one {a m : ℕ} (h : a + m ≤ n)
    {g : SpecialLinearGroup (Fin n) (ZMod 2)} (ha : g ∈ stabilizer (flagSpace n (ZMod 2) a))
    (hb : g ∈ stabilizer (flagSpace n (ZMod 2) (a + m)))
    (hg : blkAt a m h (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1) {i : ℕ} (hai : a ≤ i)
    (hib : i ≤ a + m) : g ∈ stabilizer (flagSpace n (ZMod 2) i) := by
  refine mem_stabilizer_of_entries fun k l hk hl => ?_
  by_cases hla : (l : ℕ) < a
  · exact stabilizer_entries ha hla (by omega)
  by_cases hkb : (k : ℕ) < a + m
  · rw [SLk.entry_of_blkAt_eq_one h hg (by omega) hkb (by omega) (by omega),
      Matrix.one_apply_ne (fun h' => by subst h'; omega)]
  · exact stabilizer_entries hb (by omega) (by omega)

@[expose] noncomputable def blk (I : Set ℕ) (a m : ℕ) (h : a + m ≤ n) (ha : a = 0 ∨ a = n ∨ a ∈ I)
    (hb : a + m = 0 ∨ a + m = n ∨ a + m ∈ I) :
    ↥(flagStabilizer n (ZMod 2) I) →* SpecialLinearGroup (Fin m) (ZMod 2) :=
  SLk.blkSL2 _ a m h (blockLeft_of_stabilizer fun _ hg => SLk.mem_stabilizer_of_cut hg ha)
    (blockRight_of_stabilizer fun _ hg => SLk.mem_stabilizer_of_cut hg hb)

theorem coe_blk {a m : ℕ} (h : a + m ≤ n) (ha : a = 0 ∨ a = n ∨ a ∈ I)
    (hb : a + m = 0 ∨ a + m = n ∨ a + m ∈ I) (g : ↥(flagStabilizer n (ZMod 2) I)) :
    ((blk I a m h ha hb g : SpecialLinearGroup (Fin m) (ZMod 2)) :
      Matrix (Fin m) (Fin m) (ZMod 2)) =
      blkAt a m h ((g : SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  rfl

theorem embSL_mem {a m : ℕ} (h : a + m ≤ n) (hcut : ∀ i ∈ I, i ≤ a ∨ a + m ≤ i)
    (M : SpecialLinearGroup (Fin m) (ZMod 2)) : SLk.embSL a m h M ∈ flagStabilizer n (ZMod 2) I :=
  mem_flagStabilizer.2 fun i hi => SLk.embSL_mem_stabilizer a m h M (hcut i hi)

theorem blk_embSL {a m : ℕ} (h : a + m ≤ n) (ha : a = 0 ∨ a = n ∨ a ∈ I)
    (hb : a + m = 0 ∨ a + m = n ∨ a + m ∈ I) (hcut : ∀ i ∈ I, i ≤ a ∨ a + m ≤ i)
    (M : SpecialLinearGroup (Fin m) (ZMod 2)) :
    blk I a m h ha hb ⟨_, embSL_mem h hcut M⟩ = M :=
  Subtype.ext (by rw [coe_blk]; exact SLk.blkAt_embAt h _)

theorem blk_surjective {a m : ℕ} (h : a + m ≤ n) (ha : a = 0 ∨ a = n ∨ a ∈ I)
    (hb : a + m = 0 ∨ a + m = n ∨ a + m ∈ I) (hcut : ∀ i ∈ I, i ≤ a ∨ a + m ≤ i) :
    Function.Surjective (blk I a m h ha hb) := fun M =>
  ⟨⟨_, embSL_mem h hcut M⟩, blk_embSL h ha hb hcut M⟩

theorem blkAt_embAt_of_le {a b m : ℕ} (h : b + m ≤ n) (hab : a + 2 ≤ b)
    (M : Matrix (Fin 2) (Fin 2) (ZMod 2)) :
    blkAt b m h (SLk.embAt (k := n) a 2 M) = 1 := by
  ext i j
  rw [blkAt_apply, SLk.embAt_apply_of_not _ (show ¬ (a ≤ b + (i : ℕ) ∧ b + (i : ℕ) < a + 2) by
    omega), Matrix.one_apply, Matrix.one_apply]
  simp [Fin.ext_iff]

end Blocks

section Config

variable {n : ℕ} {I : Set ℕ}

structure Cfg (n : ℕ) (I : Set ℕ) (X Y : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2)))
    (y : SpecialLinearGroup (Fin n) (ZMod 2)) : Prop where
  hXQ : X ≤ flagStabilizer n (ZMod 2) I
  hQX : flagStabilizer n (ZMod 2) I ≤
    Subgroup.normalizer (X : Set (SpecialLinearGroup (Fin n) (ZMod 2)))
  hYX : Y ≤ X
  hQY : flagStabilizer n (ZMod 2) I ≤
    Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin n) (ZMod 2)))
  hY2 : IsPGroup 2 ↥Y
  hy : y ∈ X
  hy3 : orderOf y = 3
  hXy : X ≤ Y ⊔ Subgroup.zpowers y

namespace Cfg

variable {X Y : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
  {y : SpecialLinearGroup (Fin n) (ZMod 2)} (C : Cfg n I X Y y)
include C

theorem yQ : y ∈ flagStabilizer n (ZMod 2) I := C.hXQ C.hy

theorem YQ : Y ≤ flagStabilizer n (ZMod 2) I := C.hYX.trans C.hXQ

theorem y_pow_three : y ^ 3 = 1 := by
  rw [← C.hy3]
  exact pow_orderOf_eq_one y

theorem exists_mul_zpow {x : SpecialLinearGroup (Fin n) (ZMod 2)} (hx : x ∈ X) :
    ∃ u ∈ Y, ∃ k : ℤ, x = u * y ^ k := by
  have hyN : Subgroup.zpowers y ≤
      Subgroup.normalizer (Y : Set (SpecialLinearGroup (Fin n) (ZMod 2))) :=
    (Subgroup.zpowers_le).2 (C.hQY C.yQ)
  have h1 : x ∈ ((Y ⊔ Subgroup.zpowers y : Subgroup _) : Set _) := C.hXy hx
  rw [Subgroup.coe_mul_of_right_le_normalizer_left Y _ hyN] at h1
  obtain ⟨u, hu, z, hz, rfl⟩ := h1
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ⟨u, hu, k, rfl⟩

theorem not_le_upperTriangular (hn : 1 ≤ n) : ¬ X ≤ upperTriangular n (ZMod 2) := by
  intro h
  have hyU : y ∈ unitriangular n (ZMod 2) := by
    rw [← BinaryParabolic.upperTriangular_eq_unitriangular]
    exact h C.hy
  obtain ⟨k, hk⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) hn ⟨y, hyU⟩
  have hk' : y ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h1 : y ^ Nat.gcd 3 (2 ^ k) = 1 := (pow_gcd_eq_one).2 ⟨C.y_pow_three, hk'⟩
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (by norm_num)), pow_one] at h1
  have := C.hy3
  rw [h1, orderOf_one] at this
  exact absurd this (by norm_num)

section OneBlock

variable {a m : ℕ} (h : a + m ≤ n) (ha : a = 0 ∨ a = n ∨ a ∈ I)
  (hb : a + m = 0 ∨ a + m = n ∨ a + m ∈ I) (hcut : ∀ i ∈ I, i ≤ a ∨ a + m ≤ i)
include h ha hb hcut

omit C in
theorem normal_map_blk {Z : Subgroup (SpecialLinearGroup (Fin n) (ZMod 2))}
    (hZQ : Z ≤ flagStabilizer n (ZMod 2) I)
    (hQZ : flagStabilizer n (ZMod 2) I ≤
      Subgroup.normalizer (Z : Set (SpecialLinearGroup (Fin n) (ZMod 2)))) :
    ((Z.subgroupOf (flagStabilizer n (ZMod 2) I)).map (blk I a m h ha hb)).Normal :=
  ((Subgroup.normal_subgroupOf_iff_le_normalizer hZQ).2 hQZ).map _
    (blk_surjective h ha hb hcut)

theorem blk_Y (hm : m = 2 ∨ m = 3 ∨ m = 4) {u : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hu : u ∈ Y) : blk I a m h ha hb ⟨u, C.YQ hu⟩ = 1 := by
  set N := (Y.subgroupOf (flagStabilizer n (ZMod 2) I)).map (blk I a m h ha hb) with hN
  have hNn : N.Normal := normal_map_blk h ha hb hcut C.YQ C.hQY
  have h2 : ∀ w ∈ N, ∃ k : ℕ, w ^ 2 ^ k = 1 := by
    rintro _ ⟨v, hv, rfl⟩
    obtain ⟨k, hk⟩ := C.hY2 ⟨v, hv⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : v ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    rw [this, map_one]
  have huN : blk I a m h ha hb ⟨u, C.YQ hu⟩ ∈ N := ⟨⟨u, C.YQ hu⟩, hu, rfl⟩
  have hodd : ∀ w ∈ N, ∀ e : ℕ, Odd e → w ^ e = 1 → w = 1 := by
    intro w hw e he hwe
    obtain ⟨k, hk⟩ := h2 w hw
    have h1 : w ^ Nat.gcd e (2 ^ k) = 1 := (pow_gcd_eq_one).2 ⟨hwe, hk⟩
    rwa [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow_right k (Nat.coprime_two_right.2 he)),
      pow_one] at h1
  rcases hm with rfl | hm
  ·
    by_contra hne
    set w := blk I a 2 h ha hb ⟨u, C.YQ hu⟩ with hw
    have hw2 : w ^ 2 = 1 := by
      rcases sl2_pow w with h' | h'
      · exact h'
      · exact absurd (hodd w huN 3 (by decide) h') hne
    obtain ⟨G, h3, h31⟩ := sl2_normal w hw2 hne
    exact h31 (hodd _ (N.mul_mem (hNn.conj_mem w huN G) huN) 3 (by decide) h3)
  ·
    have hs := SLk.isSimpleGroup_sl (n := m) (by omega)
    rcases hNn.eq_bot_or_eq_top with hbot | htop
    · rw [hbot] at huN
      exact (Subgroup.mem_bot).1 huN
    · exfalso
      obtain ⟨z, hz7, hz1⟩ := SLk.exists_seven (by omega : m = 3 ∨ m = 4)
      exact hz1 (hodd z (htop ▸ Subgroup.mem_top z) 7 (by decide) hz7)

theorem blk_X (hm : m = 2 ∨ m = 3 ∨ m = 4) {x : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hx : x ∈ X) : ∃ k : ℤ, blk I a m h ha hb ⟨x, C.hXQ hx⟩ = blk I a m h ha hb ⟨y, C.yQ⟩ ^ k := by
  obtain ⟨u, hu, k, rfl⟩ := C.exists_mul_zpow hx
  refine ⟨k, ?_⟩
  have e : (⟨u * y ^ k, C.hXQ hx⟩ : ↥(flagStabilizer n (ZMod 2) I)) =
      ⟨u, C.YQ hu⟩ * ⟨y, C.yQ⟩ ^ k := Subtype.ext (by simp)
  rw [e, map_mul, map_zpow, C.blk_Y h ha hb hcut hm hu, one_mul]

theorem fix_of_big_block (hm : m = 3 ∨ m = 4) {x : SpecialLinearGroup (Fin n) (ZMod 2)}
    (hx : x ∈ X) {i : ℕ} (hai : a ≤ i) (hib : i ≤ a + m) :
    x ∈ stabilizer (flagSpace n (ZMod 2) i) := by
  have hm' : m = 2 ∨ m = 3 ∨ m = 4 := Or.inr hm
  set β := blk I a m h ha hb with hβ
  have hy1 : β ⟨y, C.yQ⟩ = 1 := by
    by_contra hne
    have hs := SLk.isSimpleGroup_sl (n := m) (by omega)
    set N := (X.subgroupOf (flagStabilizer n (ZMod 2) I)).map β with hN
    have hNn : N.Normal := normal_map_blk h ha hb hcut C.hXQ C.hQX
    have hyN : β ⟨y, C.yQ⟩ ∈ N := ⟨⟨y, C.yQ⟩, C.hy, rfl⟩
    rcases hNn.eq_bot_or_eq_top with hbot | htop
    · rw [hbot] at hyN
      exact hne ((Subgroup.mem_bot).1 hyN)
    · obtain ⟨z, hz7, hz1⟩ := SLk.exists_seven hm
      obtain ⟨⟨v, hvQ⟩, hv, hvz⟩ := htop ▸ Subgroup.mem_top z
      obtain ⟨k, hk⟩ := C.blk_X h ha hb hcut hm' hv
      have hk' : β ⟨v, hvQ⟩ = β ⟨y, C.yQ⟩ ^ k := hk
      have hz3 : z ^ 3 = 1 := by
        rw [← hvz, hk', ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast,
          ← map_pow]
        have : (⟨y, C.yQ⟩ : ↥(flagStabilizer n (ZMod 2) I)) ^ 3 = 1 :=
          Subtype.ext (by simpa using C.y_pow_three)
        rw [this, map_one, _root_.one_zpow]
      have h1 : z ^ Nat.gcd 7 3 = 1 := (pow_gcd_eq_one).2 ⟨hz7, hz3⟩
      rw [show Nat.gcd 7 3 = 1 by norm_num, pow_one] at h1
      exact hz1 h1
  obtain ⟨k, hk⟩ := C.blk_X h ha hb hcut hm' hx
  rw [hy1, _root_.one_zpow] at hk
  have hb1 : blkAt a m h ((x : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
    have := congrArg (fun A : SpecialLinearGroup (Fin m) (ZMod 2) =>
      (A : Matrix (Fin m) (Fin m) (ZMod 2))) hk
    simpa [coe_blk] using this
  exact mem_stabilizer_of_blkAt_eq_one h (SLk.mem_stabilizer_of_cut (C.hXQ hx) ha)
    (SLk.mem_stabilizer_of_cut (C.hXQ hx) hb) hb1 hai hib

end OneBlock

theorem fix_of_two_blocks {a b : ℕ} (hab : a + 2 ≤ b) (hbn : b + 2 ≤ n) (ha : a = 0 ∨ a ∈ I)
    (ha2 : a + 2 ∈ I) (ha1 : a + 1 ∉ I) (hb : b ∈ I) (hb2 : b + 2 = n ∨ b + 2 ∈ I)
    (hb1 : b + 1 ∉ I) :
    (∀ x ∈ X, x ∈ stabilizer (flagSpace n (ZMod 2) (a + 1))) ∨
      ∀ x ∈ X, x ∈ stabilizer (flagSpace n (ZMod 2) (b + 1)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h₁ : a + 2 ≤ n := by omega
  have ha' : a = 0 ∨ a = n ∨ a ∈ I := ha.elim Or.inl fun h => Or.inr (Or.inr h)
  have ha2' : a + 2 = 0 ∨ a + 2 = n ∨ a + 2 ∈ I := Or.inr (Or.inr ha2)
  have hcut₁ : ∀ i ∈ I, i ≤ a ∨ a + 2 ≤ i := fun i hi => by
    have : i ≠ a + 1 := fun e => ha1 (e ▸ hi)
    omega
  have hb' : b = 0 ∨ b = n ∨ b ∈ I := Or.inr (Or.inr hb)
  have hb2' : b + 2 = 0 ∨ b + 2 = n ∨ b + 2 ∈ I :=
    hb2.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr h)
  have hcut₂ : ∀ i ∈ I, i ≤ b ∨ b + 2 ≤ i := fun i hi => by
    have : i ≠ b + 1 := fun e => hb1 (e ▸ hi)
    omega
  have hfix : ∀ (c : ℕ) (hc : c + 2 ≤ n) (hc0 : c = 0 ∨ c = n ∨ c ∈ I)
      (hc2 : c + 2 = 0 ∨ c + 2 = n ∨ c + 2 ∈ I) (hcc : ∀ i ∈ I, i ≤ c ∨ c + 2 ≤ i),
      blk I c 2 hc hc0 hc2 ⟨y, C.yQ⟩ = 1 →
        ∀ x ∈ X, x ∈ stabilizer (flagSpace n (ZMod 2) (c + 1)) := by
    intro c hc hc0 hc2 hcc hy1 x hx
    obtain ⟨k, hk⟩ := C.blk_X hc hc0 hc2 hcc (Or.inl rfl) hx
    rw [hy1, _root_.one_zpow] at hk
    have hb1 : blkAt c 2 hc ((x : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
      have := congrArg (fun A : SpecialLinearGroup (Fin 2) (ZMod 2) =>
        (A : Matrix (Fin 2) (Fin 2) (ZMod 2))) hk
      simpa [coe_blk] using this
    exact mem_stabilizer_of_blkAt_eq_one hc (SLk.mem_stabilizer_of_cut (C.hXQ hx) hc0)
      (SLk.mem_stabilizer_of_cut (C.hXQ hx) hc2) hb1 (by omega) (by omega)
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hc₁, hc₂⟩ := hcon
  push Not at hc₁ hc₂
  obtain ⟨x₁, hx₁, hx₁'⟩ := hc₁
  obtain ⟨x₂, hx₂, hx₂'⟩ := hc₂
  set β₁ := blk I a 2 h₁ ha' ha2' with hβ₁
  set β₂ := blk I b 2 hbn hb' hb2' with hβ₂
  have hy₁ : β₁ ⟨y, C.yQ⟩ ≠ 1 := fun h1 => hx₁' (hfix a h₁ ha' ha2' hcut₁ h1 x₁ hx₁)
  have hy₂ : β₂ ⟨y, C.yQ⟩ ≠ 1 := fun h1 => hx₂' (hfix b hbn hb' hb2' hcut₂ h1 x₂ hx₂)
  have hy3 : (⟨y, C.yQ⟩ : ↥(flagStabilizer n (ZMod 2) I)) ^ 3 = 1 :=
    Subtype.ext (by simpa using C.y_pow_three)
  have h₁3 : β₁ ⟨y, C.yQ⟩ ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  have h₂3 : β₂ ⟨y, C.yQ⟩ ^ 3 = 1 := by rw [← map_pow, hy3, map_one]
  set g : ↥(flagStabilizer n (ZMod 2) I) := ⟨SLk.embSL a 2 h₁ s2, embSL_mem h₁ hcut₁ s2⟩ with hg
  have hg₁ : β₁ g = s2 := blk_embSL h₁ ha' ha2' hcut₁ s2
  have hg₂ : β₂ g = 1 := Subtype.ext (by
    rw [coe_blk]
    exact blkAt_embAt_of_le hbn hab _)
  have hgy : ((g * ⟨y, C.yQ⟩ * g⁻¹ : ↥(flagStabilizer n (ZMod 2) I)) :
      SpecialLinearGroup (Fin n) (ZMod 2)) ∈ X :=
    (Subgroup.mem_normalizer_iff.1 (C.hQX g.2) y).1 C.hy
  obtain ⟨u, hu, k, hk⟩ := C.exists_mul_zpow hgy
  have hk' : g * ⟨y, C.yQ⟩ * g⁻¹ = ⟨u, C.YQ hu⟩ * ⟨y, C.yQ⟩ ^ k :=
    Subtype.ext (by simpa using hk)
  have e₁ := congrArg β₁ hk'
  have e₂ := congrArg β₂ hk'
  rw [map_mul, map_mul, map_inv, hg₁, map_mul, map_zpow, C.blk_Y h₁ ha' ha2' hcut₁ (Or.inl rfl) hu,
    one_mul, sl2_inv _ h₁3] at e₁
  rw [map_mul, map_mul, map_inv, hg₂, one_mul, inv_one, mul_one, map_mul, map_zpow,
    C.blk_Y hbn hb' hb2' hcut₂ (Or.inl rfl) hu, one_mul] at e₂
  have ho₁ : orderOf (β₁ ⟨y, C.yQ⟩) = 3 := orderOf_eq_prime h₁3 hy₁
  have ho₂ : orderOf (β₂ ⟨y, C.yQ⟩) = 3 := orderOf_eq_prime h₂3 hy₂
  have hk1 : ((3 : ℕ) : ℤ) ∣ k - 1 := by
    rw [← ho₂, orderOf_dvd_iff_zpow_eq_one, _root_.zpow_sub_one, ← e₂, mul_inv_cancel]
  have hk1' : β₁ ⟨y, C.yQ⟩ ^ (k - 1) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, ho₁]
    exact hk1
  have e₃ : β₁ ⟨y, C.yQ⟩ ^ k = β₁ ⟨y, C.yQ⟩ := by
    rw [show k = (k - 1) + 1 by ring, _root_.zpow_add_one, hk1', one_mul]
  rw [e₃] at e₁
  have h12 : β₁ ⟨y, C.yQ⟩ ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [← e₁]
    exact mul_inv_cancel _
  have h1 : β₁ ⟨y, C.yQ⟩ ^ Nat.gcd 3 2 = 1 := (pow_gcd_eq_one).2 ⟨h₁3, h12⟩
  rw [show Nat.gcd 3 2 = 1 by norm_num, pow_one] at h1
  exact hy₁ h1

end Cfg

end Config

section Cuts

@[expose] def CombBig (n : ℕ) (I F : Finset ℕ) : Prop :=
  ∀ a ∈ Finset.range (n + 1), ∀ m ∈ Finset.range (n + 1), 3 ≤ m → a + m ≤ n →
    (a = 0 ∨ a ∈ I) → (a + m = n ∨ a + m ∈ I) → (∀ i ∈ I, i ≤ a ∨ a + m ≤ i) →
    ∀ i ∈ Finset.Icc 1 (n - 1), a ≤ i → i ≤ a + m → i ∈ F

@[expose] def CombTwo (n : ℕ) (I F : Finset ℕ) : Prop :=
  ∀ a ∈ Finset.range n, ∀ b ∈ Finset.range n, a + 2 ≤ b → b + 2 ≤ n → (a = 0 ∨ a ∈ I) →
    a + 2 ∈ I → a + 1 ∉ I → b ∈ I → (b + 2 = n ∨ b + 2 ∈ I) → b + 1 ∉ I →
    a + 1 ∈ F ∨ b + 1 ∈ F

@[expose] def CombSym (n : ℕ) (I : Finset ℕ) : Prop := ∀ i ∈ I, n - i ∈ I

instance (n : ℕ) (I F : Finset ℕ) : Decidable (CombBig n I F) := by
  unfold CombBig; infer_instance

instance (n : ℕ) (I F : Finset ℕ) : Decidable (CombTwo n I F) := by
  unfold CombTwo; infer_instance

instance (n : ℕ) (I : Finset ℕ) : Decidable (CombSym n I) := by
  unfold CombSym; infer_instance

theorem comb4 : ∀ I ∈ (Finset.Icc 1 3).powerset, ∀ F ∈ (Finset.Icc 1 3).powerset,
    I.Nonempty → I ⊆ F → F ≠ Finset.Icc 1 3 → CombBig 4 I F → CombTwo 4 I F →
      (∀ j ∈ I, ∃ i ∈ F, i ≠ j) ∧ (CombSym 4 I → CombSym 4 F → I = {1, 3}) := by
  decide

theorem comb5 : ∀ I ∈ (Finset.Icc 1 4).powerset, ∀ F ∈ (Finset.Icc 1 4).powerset,
    I.Nonempty → I ⊆ F → F ≠ Finset.Icc 1 4 → CombBig 5 I F → CombTwo 5 I F →
      (∀ j ∈ I, ∃ i ∈ F, i ≠ j) ∧ (CombSym 5 I → CombSym 5 F → False) := by
  decide

end Cuts

open CFSG.Quasithin.H13.NQCat.NNMod in
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag in
theorem slParabolicThreeFact_holds :
    ∀ n : ℕ, (n = 4 ∨ n = 5) → ∀ I : Set ℕ, (∀ i ∈ I, 1 ≤ i ∧ i < n) → I.Nonempty →
      ∀ (X Y : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)))
        (y : Matrix.SpecialLinearGroup (Fin n) (ZMod 2)),
        X ≤ flagStabilizer n (ZMod 2) I →
        flagStabilizer n (ZMod 2) I ≤ Subgroup.normalizer (X : Set _) →
        Y ≤ X → flagStabilizer n (ZMod 2) I ≤ Subgroup.normalizer (Y : Set _) →
        IsPGroup 2 Y → y ∈ X → orderOf y = 3 → X ≤ Y ⊔ Subgroup.zpowers y →
      ∀ A : Set (MulAut (Matrix.SpecialLinearGroup (Fin n) (ZMod 2))),
        (∀ α ∈ A, (upperTriangular n (ZMod 2)).map α.toMonoidHom = upperTriangular n (ZMod 2)) →
        (∀ α ∈ A, (flagStabilizer n (ZMod 2) I).map α.toMonoidHom = flagStabilizer n (ZMod 2) I) →
        (∀ α ∈ A, X.map α.toMonoidHom = X) →
        (∃ P : Subgroup (Matrix.SpecialLinearGroup (Fin n) (ZMod 2)),
            upperTriangular n (ZMod 2) ≤ P ∧ P ≠ ⊤ ∧ X ≤ P ∧ ¬ P ≤ flagStabilizer n (ZMod 2) I ∧
            ∀ α ∈ A, P.map α.toMonoidHom = P) ∨
          (n = 4 ∧ I = {1, 3} ∧ ∃ α ∈ A, ¬ ∃ x, ∀ g, α g = x * g * x⁻¹) := by
  classical
  intro n hn I hI hIne X Y y hXQ hQX hYX hQY hY2 hy hy3 hXy A hAB hAQ hAX
  have C : Cfg n I X Y y := ⟨hXQ, hQX, hYX, hQY, hY2, hy, hy3, hXy⟩
  have hn3 : 3 ≤ n := by omega
  set F := borelOvergroupCuts (X ⊔ upperTriangular n (ZMod 2)) with hFdef
  have hXB : X ⊔ upperTriangular n (ZMod 2) = flagStabilizer n (ZMod 2) F :=
    (borel_overgroups _ le_sup_right).1
  have hFn : ∀ i ∈ F, 1 ≤ i ∧ i < n := fun i ⟨hi, hin, _⟩ => ⟨hi, hin⟩
  have hXF : X ≤ flagStabilizer n (ZMod 2) F := hXB ▸ le_sup_left
  have hrefl : ∀ (i : ℕ) (hi : 1 ≤ i) (hin : i < n),
      reflection n (ZMod 2) i hi hin ∉ stabilizer (flagSpace n (ZMod 2) i) := by
    intro i hi hin hmem
    exact ((subflag_stabilizer_generation (K := ZMod 2) (n := n) {i}).2.2 i hi hin).1
      (mem_flagStabilizer.2 fun j hj => by rw [Set.mem_singleton_iff.1 hj]; exact hmem) rfl
  have hmemF : ∀ i, 1 ≤ i → i < n → (∀ x ∈ X, x ∈ stabilizer (flagSpace n (ZMod 2) i)) →
      i ∈ F := by
    intro i hi hin hX
    refine ⟨hi, hin, fun hr => hrefl i hi hin ?_⟩
    have hle : X ⊔ upperTriangular n (ZMod 2) ≤ stabilizer (flagSpace n (ZMod 2) i) :=
      sup_le (fun x hx => hX x hx) fun b hb =>
        mem_flagStabilizer.1 (upperTriangular_le_flagStabilizer {i} hb) i (Set.mem_singleton i)
    exact hle hr
  set I' := (Finset.Icc 1 (n - 1)).filter (· ∈ I) with hI'
  set F' := (Finset.Icc 1 (n - 1)).filter (· ∈ F) with hF'
  have hmemI' : ∀ i, i ∈ I' ↔ i ∈ I := fun i => by
    rw [hI', Finset.mem_filter, Finset.mem_Icc]
    refine ⟨fun h => h.2, fun h => ?_⟩
    have := hI i h
    exact ⟨⟨this.1, by omega⟩, h⟩
  have hmemF' : ∀ i, i ∈ F' ↔ i ∈ F := fun i => by
    rw [hF', Finset.mem_filter, Finset.mem_Icc]
    refine ⟨fun h => h.2, fun h => ?_⟩
    have := hFn i h
    exact ⟨⟨this.1, by omega⟩, h⟩
  have hIne' : I'.Nonempty := by
    obtain ⟨j, hj⟩ := hIne
    exact ⟨j, (hmemI' j).2 hj⟩
  have hIF : I' ⊆ F' := fun i hi => by
    have hi' := (hmemI' i).1 hi
    exact (hmemF' i).2 (hmemF i (hI i hi').1 (hI i hi').2 fun x hx =>
      mem_flagStabilizer.1 (hXQ hx) i hi')
  have hFne : F' ≠ Finset.Icc 1 (n - 1) := by
    intro hF
    apply C.not_le_upperTriangular (by omega)
    have hsub : Set.Icc 1 (n - 1) ⊆ F := fun i hi => by
      have : i ∈ F' := by rw [hF]; exact Finset.mem_Icc.2 hi
      exact (hmemF' i).1 this
    rw [BinaryParabolic.upperTriangular_eq_unitriangular, ← BinaryParabolic.flagStabilizer_Icc]
    exact hXF.trans (BinaryParabolic.flagStabilizer_anti hsub)
  have hbig : CombBig n I' F' := by
    intro a _ m _ hm3 ham ha hb hcut i hi hai hib
    rw [Finset.mem_Icc] at hi
    have ha' : a = 0 ∨ a = n ∨ a ∈ I := ha.elim Or.inl fun h => Or.inr (Or.inr ((hmemI' a).1 h))
    have hb' : a + m = 0 ∨ a + m = n ∨ a + m ∈ I :=
      hb.elim (fun h => Or.inr (Or.inl h)) fun h => Or.inr (Or.inr ((hmemI' _).1 h))
    have hcut' : ∀ i ∈ I, i ≤ a ∨ a + m ≤ i := fun i hi => hcut i ((hmemI' i).2 hi)
    have hm : m = 3 ∨ m = 4 := by
      rcases (by omega : m = 3 ∨ m = 4 ∨ m = 5) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exfalso
        obtain ⟨j, hj⟩ := hIne
        have := hI j hj
        rcases hcut' j hj with h' | h' <;> omega
    exact (hmemF' i).2 (hmemF i hi.1 (by omega) fun x hx =>
      C.fix_of_big_block ham ha' hb' hcut' hm hx hai hib)
  have htwo : CombTwo n I' F' := by
    intro a _ b _ hab hbn ha ha2 ha1 hb hb2 hb1
    have ha' : a = 0 ∨ a ∈ I := ha.elim Or.inl fun h => Or.inr ((hmemI' a).1 h)
    have hb2' : b + 2 = n ∨ b + 2 ∈ I := hb2.elim Or.inl fun h => Or.inr ((hmemI' _).1 h)
    rcases C.fix_of_two_blocks hab hbn ha' ((hmemI' _).1 ha2) (fun h => ha1 ((hmemI' _).2 h))
        ((hmemI' _).1 hb) hb2' (fun h => hb1 ((hmemI' _).2 h)) with h | h
    · exact Or.inl ((hmemF' _).2 (hmemF _ (by omega) (by omega) h))
    · exact Or.inr ((hmemF' _).2 (hmemF _ (by omega) (by omega) h))
  have hcomb : (∀ j ∈ I', ∃ i ∈ F', i ≠ j) ∧
      (CombSym n I' → CombSym n F' → n = 4 ∧ I' = {1, 3}) := by
    have hIp : I' ∈ (Finset.Icc 1 (n - 1)).powerset :=
      Finset.mem_powerset.2 (Finset.filter_subset _ _)
    have hFp : F' ∈ (Finset.Icc 1 (n - 1)).powerset :=
      Finset.mem_powerset.2 (Finset.filter_subset _ _)
    rcases hn with rfl | rfl
    · obtain ⟨h1, h2⟩ := comb4 I' hIp F' hFp hIne' hIF hFne hbig htwo
      exact ⟨h1, fun a b => ⟨rfl, h2 a b⟩⟩
    · obtain ⟨h1, h2⟩ := comb5 I' hIp F' hFp hIne' hIF hFne hbig htwo
      exact ⟨h1, fun a b => (h2 a b).elim⟩
  by_cases hinn : ∀ α ∈ A, ∃ x, ∀ g, α g = x * g * x⁻¹
  ·
    left
    obtain ⟨j, hj⟩ := hIne
    obtain ⟨hj1, hjn⟩ := hI j hj
    obtain ⟨i, hiF, hij⟩ := hcomb.1 j ((hmemI' j).2 hj)
    have hiF' := (hmemF' i).1 hiF
    obtain ⟨hi1, hin⟩ := hFn i hiF'
    set P := flagStabilizer n (ZMod 2) (F \ {j}) with hP
    refine ⟨P, upperTriangular_le_flagStabilizer _, fun htop => ?_,
      hXF.trans (BinaryParabolic.flagStabilizer_anti Set.sdiff_subset), fun hle => ?_,
      fun α hα => ?_⟩
    · exact ((subflag_stabilizer_generation (K := ZMod 2) (n := n) (F \ {j})).2.2 i hi1 hin).1
        (by rw [← hP, htop]; exact Subgroup.mem_top _) ⟨hiF', hij⟩
    · have hr : reflection n (ZMod 2) j hj1 hjn ∈ P :=
        ((subflag_stabilizer_generation (K := ZMod 2) (n := n) _).2.2 j hj1 hjn).2
          fun h => h.2 rfl
      exact ((subflag_stabilizer_generation (K := ZMod 2) (n := n) I).2.2 j hj1 hjn).1
        (hle hr) hj
    · obtain ⟨x, hx⟩ := hinn α hα
      have hxN : x ∈ Subgroup.normalizer ((unitriangular n (ZMod 2) : Subgroup _) :
          Set (SpecialLinearGroup (Fin n) (ZMod 2))) := by
        rw [← BinaryParabolic.upperTriangular_eq_unitriangular]
        refine Subgroup.mem_normalizer_iff.2 fun b => ⟨fun hb => ?_, fun hb => ?_⟩
        · have h1 : α b ∈ (upperTriangular n (ZMod 2)).map α.toMonoidHom := ⟨b, hb, rfl⟩
          rw [hAB α hα, hx] at h1
          exact h1
        · have h1 : x * b * x⁻¹ ∈ (upperTriangular n (ZMod 2)).map α.toMonoidHom := by
            rw [hAB α hα]
            exact hb
          obtain ⟨b', hb', e⟩ := h1
          rw [MulEquiv.coe_toMonoidHom, hx] at e
          have : b' = b := by
            have e' := congrArg (fun z => x⁻¹ * z * x) e
            simpa [mul_assoc] using e'
          exact this ▸ hb'
      have hxB : x ∈ upperTriangular n (ZMod 2) := by
        rw [← normalizer_unitriangular]
        exact hxN
      have hxP : x ∈ P := upperTriangular_le_flagStabilizer _ hxB
      ext g
      constructor
      · rintro ⟨p, hp, rfl⟩
        rw [MulEquiv.coe_toMonoidHom, hx]
        exact P.mul_mem (P.mul_mem hxP hp) (P.inv_mem hxP)
      · intro hg
        refine ⟨x⁻¹ * g * x, P.mul_mem (P.mul_mem (P.inv_mem hxP) hg) hxP, ?_⟩
        rw [MulEquiv.coe_toMonoidHom, hx]
        group
  ·
    right
    push Not at hinn
    obtain ⟨α, hα, hni⟩ := hinn
    have hni' : ¬ ∃ x, ∀ g, α g = x * g * x⁻¹ := fun ⟨x, hx⟩ => by
      obtain ⟨g, hg⟩ := hni x
      exact hg (hx g)
    have hαF : (flagStabilizer n (ZMod 2) F).map α.toMonoidHom = flagStabilizer n (ZMod 2) F := by
      rw [← hXB, Subgroup.map_sup, hAX α hα, hAB α hα]
    have hsymI : CombSym n I' := by
      intro i hi
      have hi' := (hmemI' i).1 hi
      obtain ⟨hi1, hin⟩ := hI i hi'
      by_contra hcon
      exact hni' (inner_of_map_flagStabilizer hn3 α (fun j hj => (hI j hj).2) hi1 hin hi'
        (fun h => hcon ((hmemI' _).2 h)) (hAQ α hα))
    have hsymF : CombSym n F' := by
      intro i hi
      have hi' := (hmemF' i).1 hi
      obtain ⟨hi1, hin⟩ := hFn i hi'
      by_contra hcon
      exact hni' (inner_of_map_flagStabilizer hn3 α (fun j hj => (hFn j hj).2) hi1 hin hi'
        (fun h => hcon ((hmemF' _).2 h)) hαF)
    obtain ⟨h4, hI13⟩ := hcomb.2 hsymI hsymF
    refine ⟨h4, Set.ext fun i => ?_, α, hα, hni'⟩
    rw [← hmemI', hI13]
    simp

end CFSG.Quasithin.H13.LPar
