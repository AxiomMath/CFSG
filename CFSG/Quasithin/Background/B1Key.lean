module

public import CFSG.Quasithin.Background.B1Restrict
public import CFSG.Quasithin.Background.B1Coprime
public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Fitting.Centralizer
public import CFSG.Open.LocalVocabulary

public section

open scoped IsMulCommutative

namespace CFSG.Quasithin

variable {V : Type*} [CommGroup V]

namespace B1

theorem exists_hyperplane_trivial (K : Type*) [Group K] [Finite K] [CFSG.IsElementaryAbelian 2 K]
    (F : Type*) [Group F] [Finite F] [MulDistribMulAction K F] (hF : Odd (Nat.card F))
    (hnt : ∃ k : K, ∃ f : F, k • f ≠ f) :
    ∃ Y : Subgroup F, CFSG.IsInvariant K F Y ∧ (∃ k : K, ∃ y ∈ Y, k • y ≠ y) ∧
      ∃ B : Subgroup K, B.index = 2 ∧ ∀ b ∈ B, ∀ y ∈ Y, b • y = y := by
  classical
  have h2 : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let S : Set (Subgroup F) :=
    {Y | CFSG.IsInvariant K F Y ∧ ∃ k : K, ∃ y ∈ Y, k • y ≠ y}
  have hSne : S.Nonempty := by
    obtain ⟨k, f, hf⟩ := hnt
    exact ⟨⊤, ⟨fun a g => by simp⟩, k, f, Subgroup.mem_top f, hf⟩
  obtain ⟨Y, ⟨hYinv, k₀, y₀, hy₀, hk₀⟩, hmin⟩ :=
    Set.exists_min_image S (fun Y => Nat.card Y) (Set.toFinite S) hSne
  refine ⟨Y, hYinv, ⟨k₀, y₀, hy₀, hk₀⟩, ?_⟩
  have hYodd : ¬ 2 ∣ Nat.card Y := by
    intro h
    have h' : 2 ∣ Nat.card F := h.trans (Subgroup.card_subgroup_dvd_card Y)
    exact (Nat.not_even_iff_odd.2 hF) (even_iff_two_dvd.2 h')
  have hnontriv : Nontrivial K := ⟨k₀, 1, fun h => hk₀ (by rw [h, one_smul])⟩
  have hgen := CFSG.SolvableHall.coprime_hyperplane_generation (p := 2) (A := K) (H := Y) hYodd
  by_contra hno
  push Not at hno
  have hle : (⨆ (B : Subgroup K) (_ : B.index = 2), CFSG.fixedPointSubgroup B ↥Y) ≤
      CFSG.fixedPointSubgroup K ↥Y := by
    refine iSup₂_le fun B hB => ?_
    have hBne : CFSG.fixedPointSubgroup B ↥Y ≠ ⊤ := by
      intro htop
      obtain ⟨b, hb, y, hy, hne⟩ := hno B hB
      have hmem : (⟨y, hy⟩ : ↥Y) ∈ CFSG.fixedPointSubgroup B ↥Y := by rw [htop]; trivial
      exact hne (congrArg Subtype.val (hmem ⟨b, hb⟩))
    have : CFSG.IsInvariant K ↥Y (CFSG.fixedPointSubgroup B ↥Y) := by
      refine ⟨fun a g => ?_⟩
      have key : ∀ (a : K) (g : ↥Y), g ∈ CFSG.fixedPointSubgroup B ↥Y →
          a • g ∈ CFSG.fixedPointSubgroup B ↥Y := by
        intro a g hg b
        calc (b : B) • (a • g) = ((b : K) * a) • g := by rw [mul_smul]; rfl
          _ = (a * (b : K)) • g := by rw [mul_comm']
          _ = a • ((b : K) • g) := by rw [mul_smul]
          _ = a • g := by rw [show (b : K) • g = g from hg b]
      refine ⟨key a g, fun h => ?_⟩
      have := key a⁻¹ _ h
      simpa using this
    have hinv' := CFSG.isInvariant_map_subtype (A := K) Y (CFSG.fixedPointSubgroup B ↥Y)
    have hcard : Nat.card (CFSG.fixedPointSubgroup B ↥Y) < Nat.card Y := by
      refine lt_of_le_of_ne (Subgroup.card_le_card_group _) ?_
      intro heq
      exact hBne (Subgroup.eq_top_of_card_eq _ heq)
    have hnotS : (CFSG.fixedPointSubgroup B ↥Y).map Y.subtype ∉ S := by
      intro hS
      have := hmin _ hS
      rw [Subgroup.card_map_of_injective Y.subtype_injective] at this
      exact absurd hcard (not_lt.2 this)
    intro g hg k
    by_contra hne
    exact hnotS ⟨hinv', k, (g : F), ⟨g, hg, rfl⟩, fun h => hne (Subtype.ext h)⟩
  rw [hgen] at hle
  have : (⟨y₀, hy₀⟩ : ↥Y) ∈ CFSG.fixedPointSubgroup K ↥Y := hle trivial
  exact hk₀ (congrArg Subtype.val (this k₀))

@[instance_reducible] def conjActSub {Γ : Type*} [Group Γ] (A F : Subgroup Γ)
    (h : ∀ a ∈ A, ∀ f ∈ F, a * f * a⁻¹ ∈ F) : MulDistribMulAction ↥A ↥F where
  smul a f := ⟨a * f * a⁻¹, h a a.2 f f.2⟩
  one_smul f := Subtype.ext (by
    show ((1 : ↥A) : Γ) * (f : Γ) * ((1 : ↥A) : Γ)⁻¹ = f
    simp)
  mul_smul a b f := Subtype.ext (by
    show ((a * b : ↥A) : Γ) * (f : Γ) * ((a * b : ↥A) : Γ)⁻¹ =
      (a : Γ) * ((b : Γ) * f * (b : Γ)⁻¹) * (a : Γ)⁻¹
    simp [mul_assoc])
  smul_mul a f g := Subtype.ext (by
    show (a : Γ) * ((f : Γ) * g) * (a : Γ)⁻¹ =
      ((a : Γ) * f * (a : Γ)⁻¹) * ((a : Γ) * g * (a : Γ)⁻¹)
    group)
  smul_one a := Subtype.ext (by
    show (a : Γ) * 1 * (a : Γ)⁻¹ = 1
    simp)

theorem isElementaryAbelian_of_isElemAbelian2 {A : Subgroup (MulAut V)} (h : IsElemAbelian2 A) :
    CFSG.IsElementaryAbelian 2 ↥A :=
  { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (h.1 x x.2 y y.2)⟩⟩
    exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
      Subtype.ext (by simpa using h.2 x x.2) }

theorem exists_hyperplane_trivial_sub {Γ : Type*} [Group Γ] [Finite Γ] {A F : Subgroup Γ}
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hFA : ∀ a ∈ A, ∀ f ∈ F, a * f * a⁻¹ ∈ F) (hF : Odd (Nat.card F))
    (hnt : ∃ a ∈ A, ∃ f ∈ F, a * f ≠ f * a) :
    ∃ Y B : Subgroup Γ, Y ≤ F ∧ B ≤ A ∧ Nat.card A = 2 * Nat.card B ∧
      (∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) ∧ (∀ b ∈ B, ∀ y ∈ Y, b * y = y * b) ∧
      (∃ a ∈ A, ∃ y ∈ Y, a * y ≠ y * a) := by
  let _ : MulDistribMulAction ↥A ↥F := conjActSub A F hFA
  have : CFSG.IsElementaryAbelian 2 ↥A :=
    { toIsMulCommutative := ⟨⟨fun x y => Subtype.ext (hAc x x.2 y y.2)⟩⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
        Subtype.ext (by simpa using hA2 x x.2) }
  have hnt' : ∃ k : ↥A, ∃ f : ↥F, k • f ≠ f := by
    obtain ⟨a, ha, f, hf, hne⟩ := hnt
    refine ⟨⟨a, ha⟩, ⟨f, hf⟩, fun h => hne ?_⟩
    have h1 : a * f * a⁻¹ = f := congrArg Subtype.val h
    calc a * f = a * f * a⁻¹ * a := by group
      _ = f * a := by rw [h1]
  obtain ⟨Y, hYinv, ⟨k, y, hy, hk⟩, B, hBi, hB⟩ := exists_hyperplane_trivial ↥A ↥F hF hnt'
  refine ⟨Y.map F.subtype, B.map A.subtype, Subgroup.map_subtype_le Y, Subgroup.map_subtype_le B,
    ?_, ?_, ?_, ?_⟩
  · have h1 := B.card_mul_index
    rw [hBi, Subgroup.card_map_of_injective A.subtype_injective] at *
    have h2 : Nat.card ↥B * 2 = Nat.card ↥A := h1
    omega
  · rintro a ha _ ⟨y, hy, rfl⟩
    have := (hYinv.invariant (⟨a, ha⟩ : ↥A) y).1 hy
    exact ⟨_, this, rfl⟩
  · rintro _ ⟨b, hb, rfl⟩ _ ⟨y, hy, rfl⟩
    have h1 : (b : Γ) * (y : Γ) * (b : Γ)⁻¹ = y := congrArg Subtype.val (hB b hb y hy)
    calc (b : Γ) * y = (b : Γ) * y * (b : Γ)⁻¹ * b := by group
      _ = y * b := by rw [h1]
  · refine ⟨k, k.2, (y : Γ), ⟨y, hy, rfl⟩, fun h => hk ?_⟩
    apply Subtype.ext
    show (k : Γ) * y * (k : Γ)⁻¹ = y
    calc (k : Γ) * y * (k : Γ)⁻¹ = (y * k) * (k : Γ)⁻¹ := by rw [h]
      _ = y := by group

theorem commSub_invariant_of_normalizes {Y Bg : Subgroup (MulAut V)} {M : Subgroup V}
    (hY : ∀ b ∈ Bg, ∀ y ∈ Y, b * y * b⁻¹ ∈ Y) (hM : ∀ b ∈ Bg, ∀ m ∈ M, b m ∈ M) :
    ∀ b ∈ Bg, ∀ c ∈ commSub M Y, b c ∈ commSub M Y := by
  intro b hb c hc
  refine Subgroup.closure_induction (p := fun c _ => b c ∈ commSub M Y) ?_ ?_ ?_ ?_ hc
  · rintro _ ⟨y, hy, w, hw, rfl⟩
    have h1 : b (y w * w⁻¹) = (b * y * b⁻¹) (b w) * (b w)⁻¹ := by
      simp [map_mul, map_inv, MulAut.mul_apply]
    rw [h1]
    exact Subgroup.subset_closure ⟨b * y * b⁻¹, hY b hb y hy, b w, hM b hb w hw, rfl⟩
  · rw [map_one]
    exact (commSub M Y).one_mem
  · intro a a' _ _ ha ha'
    rw [map_mul]
    exact (commSub M Y).mul_mem ha ha'
  · intro a _ ha
    rw [map_inv]
    exact (commSub M Y).inv_mem ha

theorem eq_one_of_fixes_fixV [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {Y B : Subgroup (MulAut V)}
    (hYodd : Odd (Nat.card Y)) (hB : IsPGroup 2 B)
    (hcomm : ∀ y ∈ Y, ∀ b ∈ B, y * b = b * y) {y : MulAut V} (hy : y ∈ Y)
    (hfix : ∀ m ∈ fixV B, y m = m) : y = 1 := by
  have hzY : Subgroup.zpowers y ≤ Y := Subgroup.zpowers_le.2 hy
  have hodd : Odd (Nat.card (Subgroup.zpowers y)) :=
    Odd.of_dvd_nat hYodd (Subgroup.card_dvd_of_le hzY)
  have hcomm' : ∀ y' ∈ Subgroup.zpowers y, ∀ b ∈ B, y' * b = b * y' := by
    intro y' hy' b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy'
    exact ((Commute.zpow_left (hcomm y hy b hb) k).eq)
  have hfix' : ∀ y' ∈ Subgroup.zpowers y, ∀ m ∈ (⊤ : Subgroup V) ⊓ fixV B, y' m = m := by
    intro y' hy' m hm
    have hs : Subgroup.zpowers y ≤ MulAction.stabilizer (MulAut V) m :=
      Subgroup.zpowers_le.2 (by
        rw [MulAction.mem_stabilizer_iff]
        exact hfix m hm.2)
    have := hs hy'
    rw [MulAction.mem_stabilizer_iff] at this
    exact this
  have := axb hV hodd hB hcomm' (M := ⊤) (fun _ _ _ _ => trivial) (fun _ _ _ _ => trivial) hfix'
  refine MulEquiv.ext fun v => ?_
  exact this (Subgroup.mem_top v) y (Subgroup.mem_zpowers y)

theorem eq_bot_of_fixV_eq_top {W : Type*} [CommGroup W] {D : Subgroup (MulAut W)}
    (h : fixV D = ⊤) : D = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun φ hφ => MulEquiv.ext fun u => ?_
  have : u ∈ fixV D := by rw [h]; trivial
  exact this φ hφ

theorem key_mod [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A Y B : Subgroup (MulAut V)}
    (hA : IsFFStarMin X A) (hYodd : Odd (Nat.card Y))
    (hYinv : ∀ a ∈ A, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y) (hBA : B ≤ A)
    (hBcard : Nat.card A = 2 * Nat.card B)
    (hBY : ∀ b ∈ B, ∀ y ∈ Y, b * y = y * b) (hAY : ∃ a ∈ A, ∃ y ∈ Y, a * y ≠ y * a) :
    Nat.card A = 2 := by
  have hA2 : IsElemAbelian2 A := hA.1.2.2.1
  have hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := hA2.1
  have hB2 : IsElemAbelian2 B :=
    ⟨fun a ha b hb => hc a (hBA ha) b (hBA hb), fun a ha => hA2.2 a (hBA ha)⟩
  have hBp : IsPGroup 2 B := hB2.isPGroup
  have hcommYB : ∀ y ∈ Y, ∀ b ∈ B, y * b = b * y := fun y hy b hb => (hBY b hb y hy).symm
  have hMA : ∀ a ∈ A, ∀ m ∈ fixV B, a m ∈ fixV B := by
    intro a ha m hm b hb
    have h1 : b * a = a * b := hc b (hBA hb) a ha
    have h2 : b (a m) = a (b m) := by
      have := congrArg (fun t : MulAut V => t m) h1
      simpa only [MulAut.mul_apply] using this
    rw [h2, hm b hb]
  have hMY : ∀ y ∈ Y, ∀ m ∈ fixV B, y m ∈ fixV B := by
    intro y hy m hm b hb
    have h2 : b (y m) = y (b m) := by
      have := congrArg (fun t : MulAut V => t m) (hcommYB y hy b hb).symm
      simpa only [MulAut.mul_apply] using this
    rw [h2, hm b hb]
  have hYM : ∀ y ∈ Y, (∀ m ∈ fixV B, y m = m) → y = 1 :=
    fun y hy hfix => eq_one_of_fixes_fixV hV hYodd hBp hcommYB hy hfix
  have hWM : commSub (fixV B) Y ≤ fixV B := commSub_le_of_invariant hMY
  have hWA : ∀ a ∈ A, ∀ w ∈ commSub (fixV B) Y, a w ∈ commSub (fixV B) Y :=
    commSub_invariant_of_normalizes hYinv hMA
  have hWY : ∀ y ∈ Y, ∀ w ∈ commSub (fixV B) Y, y w ∈ commSub (fixV B) Y :=
    commSub_invariant_of_normalizes
      (fun b hb y hy => Y.mul_mem (Y.mul_mem hb hy) (Y.inv_mem hb)) hMY
  obtain ⟨hsup, -⟩ := coprime_decomp hV hYodd hMY
  have hYW : ∀ y ∈ Y, (∀ w ∈ commSub (fixV B) Y, y w = w) → y = 1 := by
    intro y hy hfix
    refine hYM y hy fun m hm => ?_
    rw [← hsup] at hm
    obtain ⟨c, hc', w, hw, rfl⟩ := Subgroup.mem_sup.1 hm
    rw [map_mul, hfix w hw, hc'.2 y hy]
  have hAY' : ∀ a ∈ A, (∀ w ∈ commSub (fixV B) Y, a w = w) → ∀ y ∈ Y, a * y = y * a := by
    intro a ha hfix y hy
    have hc1 : y⁻¹ * (a⁻¹ * y * a) ∈ Y := by
      refine Y.mul_mem (Y.inv_mem hy) ?_
      have := hYinv a⁻¹ (A.inv_mem ha) y hy
      simpa using this
    have hfixinv : ∀ w ∈ commSub (fixV B) Y, a⁻¹ w = w := fun w hw => by
      have h1 := hfix w hw
      calc a⁻¹ w = a⁻¹ (a w) := by rw [h1]
        _ = w := by simp
    have hc2 : y⁻¹ * (a⁻¹ * y * a) = 1 := by
      refine hYW _ hc1 fun w hw => ?_
      have h3 : y⁻¹ (a⁻¹ (y (a w))) = w := by
        rw [hfix w hw, hfixinv _ (hWY y hy w hw)]
        simp
      simpa only [MulAut.mul_apply] using h3
    have hc3 : a⁻¹ * y * a = y := by
      have := congrArg (fun t => y * t) hc2
      simpa [mul_assoc] using this
    calc a * y = a * (a⁻¹ * y * a) := by rw [hc3]
      _ = y * a := by group
  have hWA0 : commSub (commSub (fixV B) Y) A ≠ ⊥ := by
    intro h
    obtain ⟨a, ha, y, hy, hne⟩ := hAY
    exact hne (hAY' a ha (fun w hw => (commSub_eq_bot_iff.1 h) hw a ha) y hy)
  have hst : A ≤ stabSub (commSub (fixV B) Y) := le_stabSub_of_invariant hWA
  have hCA : A ⊓ centSub (commSub (fixV B) Y) = B := by
    refine le_antisymm ?_ ?_
    ·
      let B₀ : Subgroup (MulAut V) := A ⊓ Subgroup.centralizer (Y : Set (MulAut V))
      have hBB₀ : B ≤ B₀ := fun b hb =>
        ⟨hBA hb, Subgroup.mem_centralizer_iff.2 fun y hy => (hBY b hb y hy).symm⟩
      have hB₀A : B₀ ≤ A := inf_le_left
      have hB₀ne : B₀ ≠ A := by
        intro h
        obtain ⟨a, ha, y, hy, hne⟩ := hAY
        have : a ∈ B₀ := h ▸ ha
        exact hne ((Subgroup.mem_centralizer_iff.1 this.2 y hy).symm)
      have hBpos : 0 < Nat.card B := Nat.card_pos
      obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBB₀
      have hkdvd : k ∣ 2 := by
        have h1 : Nat.card B₀ ∣ 2 * Nat.card B := hBcard ▸ Subgroup.card_dvd_of_le hB₀A
        rw [hk] at h1
        have h2 : Nat.card B * k ∣ Nat.card B * 2 := by rwa [mul_comm (Nat.card B) 2]
        exact Nat.dvd_of_mul_dvd_mul_left hBpos h2
      have hBeq : B₀ = B := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hkdvd with h1 | h1
        · exact (Subgroup.eq_of_le_of_card_ge hBB₀ (by rw [hk, h1, mul_one])).symm
        · exfalso
          apply hB₀ne
          refine Subgroup.eq_of_le_of_card_ge hB₀A ?_
          rw [hBcard, hk, h1, mul_comm]
      intro a ha
      have hfix : ∀ w ∈ commSub (fixV B) Y, a w = w := fun w hw => ha.2 w hw
      have : a ∈ B₀ := ⟨ha.1, Subgroup.mem_centralizer_iff.2 fun y hy =>
        (hAY' a ha.1 hfix y hy).symm⟩
      rw [← hBeq]
      exact this
    · intro b hb
      exact ⟨hBA hb, fun u hu => hWM hu b hb⟩
  have hcard := card_autSub_mul hst
  rw [hCA] at hcard
  have hBpos : 0 < Nat.card B := Nat.card_pos
  have hcard2 : Nat.card (autSub A (commSub (fixV B) Y)) = 2 := by
    have : Nat.card (autSub A (commSub (fixV B) Y)) * Nat.card B = 2 * Nat.card B := by
      rw [hcard, hBcard]
    exact Nat.eq_of_mul_eq_mul_right hBpos this
  have hW2 := sq_eq_one_sub hV (commSub (fixV B) Y)
  have hAut := B7_1_1 hA.1 hWA hWA0
  have hE2 : IsElemAbelian2 (autSub A (commSub (fixV B) Y)) := hAut.isA2.2.2
  have hrk : rk (autSub A (commSub (fixV B) Y)) = 1 := by
    have h1 := card_elemAbelian hE2
    rw [hcard2] at h1
    exact (Nat.pow_right_injective (le_refl 2) (by simpa using h1.symm : 2 ^ rk (autSub A (commSub (fixV B) Y)) = 2 ^ 1))
  have hle : rkIdx (fixV (autSub A (commSub (fixV B) Y))) ≤ rk (autSub A (commSub (fixV B) Y)) := by
    have := hAut.card_le (bot_le : (⊥ : Subgroup (MulAut (commSub (fixV B) Y))) ≤ _)
    rw [card_bot_mul_card_fixV] at this
    exact (card_le_iff hW2 hE2).1 this
  have hge : 1 ≤ rkIdx (fixV (autSub A (commSub (fixV B) Y))) := by
    have hne : fixV (autSub A (commSub (fixV B) Y)) ≠ ⊤ := fun h =>
      hAut.isA2.2.1 (eq_bot_of_fixV_eq_top h)
    have h1 := index_eq_two_pow hW2 (fixV (autSub A (commSub (fixV B) Y)))
    rcases Nat.eq_zero_or_pos (rkIdx (fixV (autSub A (commSub (fixV B) Y)))) with h0 | h0
    · exfalso
      rw [h0, pow_zero, Subgroup.index_eq_one] at h1
      exact hne h1
    · exact h0
  obtain ⟨hfaith, -⟩ := B7_1_2_faithful hV hA hWA hWA0 (by omega)
  rw [hCA] at hfaith
  rw [hfaith, Subgroup.card_bot] at hBcard
  omega

theorem pCore_eq_bot_of_normal_two_trivial {G : Type*} [Group G] [Finite G]
    (h : ∀ Q : Subgroup G, Q.Normal → IsPGroup 2 Q → Q = ⊥) : CFSG.pCore 2 G = ⊥ := by
  refine le_bot_iff.1 (sSup_le fun K hK => le_bot_iff.2 (h K hK.1 hK.2))

theorem fitting_card_odd {G : Type*} [Group G] [Finite G] (h : CFSG.pCore 2 G = ⊥) :
    Odd (Nat.card (CFSG.fittingSubgroup G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let F := CFSG.fittingSubgroup G
  let P : Sylow 2 ↥F := default
  have h1 : (P : Subgroup ↥F).map F.subtype ≤ CFSG.pCore 2 G :=
    Sylow.map_le_pCore (inferInstance : F.Normal) inferInstance 2 P
  rw [h] at h1
  have hP : (P : Subgroup ↥F) = ⊥ :=
    (Subgroup.map_eq_bot_iff_of_injective _ F.subtype_injective).1 (le_bot_iff.1 h1)
  have h2 := Sylow.card_eq_multiplicity P
  rw [hP, Subgroup.card_bot] at h2
  have h3 : (Nat.card ↥F).factorization 2 = 0 := by
    have : (2 : ℕ) ^ (Nat.card ↥F).factorization 2 = 2 ^ 0 := by rw [← h2]; rfl
    exact Nat.pow_right_injective (le_refl 2) this
  have hne : Nat.card ↥F ≠ 0 := Nat.card_pos.ne'
  have h4 : ¬ 2 ∣ Nat.card ↥F := by
    rw [Nat.Prime.dvd_iff_one_le_factorization Nat.prime_two hne]
    omega
  exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h4)

end B1

theorem key_card_two [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hsolv : Group.IsSolvable ↥X)
    (hO2 : ∀ Q : Subgroup (MulAut V), Q ≤ X → (Q.subgroupOf X).Normal → IsPGroup 2 Q → Q = ⊥)
    (hA : IsFFStarMin X A) : Nat.card A = 2 := by
  have hA2 : IsElemAbelian2 A := hA.1.2.2.1
  have hAX : A ≤ X := hA.1.1
  have hcore : CFSG.pCore 2 ↥X = ⊥ := by
    refine B1.pCore_eq_bot_of_normal_two_trivial fun Q hQ hQp => ?_
    have hQ' : Q.map X.subtype = ⊥ := by
      refine hO2 _ (Subgroup.map_subtype_le Q) ?_ (hQp.map X.subtype)
      have hsub : (Q.map X.subtype).subgroupOf X = Q :=
        Subgroup.comap_map_eq_self_of_injective X.subtype_injective Q
      rw [hsub]
      exact hQ
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).1 hQ'
  let F0 : Subgroup ↥X := CFSG.fittingSubgroup ↥X
  let F : Subgroup (MulAut V) := F0.map X.subtype
  have hFodd : Odd (Nat.card F) := by
    have := B1.fitting_card_odd hcore
    rwa [show Nat.card F = Nat.card F0 from Subgroup.card_map_of_injective X.subtype_injective]
  have hFA : ∀ a ∈ A, ∀ f ∈ F, a * f * a⁻¹ ∈ F := by
    intro a ha f hf
    obtain ⟨f0, hf0, rfl⟩ := hf
    have hconj := (inferInstance : F0.Normal).conj_mem f0 hf0 ⟨a, hAX ha⟩
    exact ⟨_, hconj, by simp⟩
  have hnt : ∃ a ∈ A, ∃ f ∈ F, a * f ≠ f * a := by
    by_contra hno
    push Not at hno
    have hAF : A ≤ F := by
      intro a ha
      have hcent : (⟨a, hAX ha⟩ : ↥X) ∈ Subgroup.centralizer (F0 : Set ↥X) := by
        rw [Subgroup.mem_centralizer_iff]
        intro h hh
        exact Subtype.ext (by
          have := hno a ha (h : MulAut V) ⟨h, hh, rfl⟩
          exact this.symm)
      have := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hsolv hcent
      exact ⟨_, this, rfl⟩
    have h1 : Nat.card A ∣ Nat.card F := Subgroup.card_dvd_of_le hAF
    have h2 : 2 ∣ Nat.card A := by
      rw [B1.card_elemAbelian hA2]
      exact dvd_pow_self 2 (hA2.rk_pos hA.1.2.1).ne'
    exact (Nat.not_even_iff_odd.2 hFodd) (even_iff_two_dvd.2 (h2.trans h1))
  obtain ⟨Y, B, hYF, hBA, hBcard, hYinv, hBY, hAY⟩ :=
    B1.exists_hyperplane_trivial_sub hA2.1 hA2.2 hFA hFodd hnt
  have hYodd : Odd (Nat.card Y) := Odd.of_dvd_nat hFodd (Subgroup.card_dvd_of_le hYF)
  exact B1.key_mod hV hA hYodd hYinv hBA hBcard hBY hAY

end CFSG.Quasithin
