module

public import CFSG.Quasithin.Background.SmithB51P2Coh

public section

namespace CFSG.Quasithin.B5.P2

open CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.Assembly.LowTwoRank

variable {V : Type} [CommGroup V]

theorem card_sup_mul_card_inf [Finite V] (H K : Subgroup V) :
    Nat.card ↥(H ⊔ K) * Nat.card ↥(H ⊓ K) = Nat.card ↥H * Nat.card ↥K := by
  have h1 : H.relIndex (H ⊔ K) = H.relIndex K := Subgroup.relIndex_sup_left K H
  have h2 := Subgroup.relIndex_mul_card H (H ⊔ K)
  have h3 := Subgroup.relIndex_mul_card H K
  rw [inf_sup_self, h1] at h2
  rw [← h2, ← h3]
  ring

theorem inf_fixV_le {A : Subgroup (MulAut V)} {X Y : Subgroup V} (hXY : X ⊓ Y = ⊥)
    (hAX : ∀ g ∈ A, ∀ w ∈ X, g w ∈ X) (hAY : ∀ g ∈ A, ∀ w ∈ Y, g w ∈ Y) :
    (X ⊔ Y) ⊓ fixV A ≤ (fixV A ⊓ X) ⊔ (fixV A ⊓ Y) := by
  rintro v ⟨hvXY, hv⟩
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hvXY
  have hfix : ∀ g ∈ A, g x = x ∧ g y = y := by
    intro g hg
    have h1 : g x * g y = x * y := by rw [← map_mul]; exact hv g hg
    have h2 : g x * x⁻¹ ∈ X ⊓ Y := by
      refine ⟨X.mul_mem (hAX g hg x hx) (X.inv_mem hx), ?_⟩
      have : g x / x = y / g y := by rw [div_eq_div_iff_mul_eq_mul, h1, mul_comm]
      rw [← div_eq_mul_inv, this, div_eq_mul_inv]
      exact Y.mul_mem hy (Y.inv_mem (hAY g hg y hy))
    rw [hXY, Subgroup.mem_bot, mul_inv_eq_one] at h2
    refine ⟨h2, ?_⟩
    rw [h2] at h1
    exact mul_left_cancel h1
  exact Subgroup.mul_mem_sup ⟨fun g hg => (hfix g hg).1, hx⟩ ⟨fun g hg => (hfix g hg).2, hy⟩

theorem card_le_of_index_two [Finite V] (hV : ∀ v : V, v ^ 2 = 1) {A : Subgroup (MulAut V)}
    {X C : Subgroup V} (hCX : C ≤ X) (hidx : Nat.card ↥X = 2 * Nat.card ↥C)
    (hAX : ∀ a ∈ A, ∀ x ∈ X, a x ∈ X) (hAC : ∀ a ∈ A, ∀ c ∈ C, a c = c)
    (hfaith : ∀ a ∈ A, (∀ x ∈ X, a x = x) → a = 1) : Nat.card ↥A ≤ Nat.card ↥C := by
  set H : Subgroup ↥X := C.subgroupOf X
  have hH : Nat.card ↥H = Nat.card ↥C := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCX).toEquiv
  have hCpos : 0 < Nat.card ↥C := Nat.card_pos
  have hidx2 : H.index = 2 := by
    have h1 := Subgroup.card_mul_index H
    rw [hH, hidx, mul_comm 2] at h1
    exact Nat.eq_of_mul_eq_mul_left hCpos h1
  have hmul : ∀ x ∈ X, ∀ y ∈ X, (y * x ∈ C ↔ (y ∈ C ↔ x ∈ C)) := by
    intro x hx y hy
    have h1 := Subgroup.mul_mem_iff_of_index_two hidx2 (a := ⟨y, hy⟩) (b := ⟨x, hx⟩)
    simpa [H, Subgroup.mem_subgroupOf] using h1
  obtain ⟨x₀, hx₀X, hx₀C⟩ : ∃ x₀ ∈ X, x₀ ∉ C := by
    by_contra hcon
    push Not at hcon
    have hle : X ≤ C := fun x hx => hcon x hx
    have h1 := Subgroup.card_le_of_le hle
    omega
  have hinv : ∀ v : V, v⁻¹ = v := fun v => inv_eq_of_mul_eq_one_left (by rw [← sq]; exact hV v)
  have hφ : ∀ a ∈ A, a x₀ * x₀⁻¹ ∈ C := by
    intro a ha
    have hax : a x₀ ∉ C := by
      intro hc
      apply hx₀C
      have h1 := hAC a⁻¹ (A.inv_mem ha) _ hc
      rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply] at h1
      rw [h1]
      exact hc
    rw [hinv]
    exact (hmul x₀ hx₀X _ (hAX a ha x₀ hx₀X)).2 (iff_of_false hax hx₀C)
  let φ : ↥A → ↥C := fun a => ⟨(a : MulAut V) x₀ * x₀⁻¹, hφ a a.2⟩
  have hφi : Function.Injective φ := by
    intro a b hab
    have h1 : (a : MulAut V) x₀ = (b : MulAut V) x₀ := by
      have := congrArg Subtype.val hab
      exact mul_right_cancel this
    set c : MulAut V := (b : MulAut V)⁻¹ * a
    have hcA : c ∈ A := A.mul_mem (A.inv_mem b.2) a.2
    have hcx₀ : c x₀ = x₀ := by
      show (b : MulAut V)⁻¹ ((a : MulAut V) x₀) = x₀
      rw [h1, ← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
    have hc1 : c = 1 := by
      refine hfaith c hcA fun y hy => ?_
      by_cases hyC : y ∈ C
      · exact hAC c hcA y hyC
      · have hyx : y * x₀ ∈ C := (hmul x₀ hx₀X y hy).2 (iff_of_false hyC hx₀C)
        have h2 := hAC c hcA _ hyx
        rw [map_mul, hcx₀] at h2
        exact mul_right_cancel h2
    apply Subtype.ext
    have : (b : MulAut V) * c = (b : MulAut V) := by rw [hc1, mul_one]
    rw [← this]
    show (a : MulAut V) = (b : MulAut V) * ((b : MulAut V)⁻¹ * a)
    rw [mul_inv_cancel_left]
  exact Nat.card_le_card_of_injective φ hφi

theorem sup_fixV_eq_top_of_offender [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {L A : Subgroup (MulAut V)}
    {X Y : Subgroup V} (hXY : X ⊓ Y = ⊥) (hLX : ∀ g ∈ L, ∀ w ∈ X, g w ∈ X)
    (hLY : ∀ g ∈ L, ∀ w ∈ Y, g w ∈ Y) (hX8 : Nat.card ↥X = 8) (hY8 : Nat.card ↥Y = 8)
    (hfX : ∀ g ∈ L, (∀ x ∈ X, g x = x) → g = 1) (hfY : ∀ g ∈ L, (∀ y ∈ Y, g y = y) → g = 1)
    (hAL : A ≤ L) (hA : A ≠ ⊥) (hA8 : Nat.card ↥A ≤ 8)
    (hoff : Nat.card V ≤ Nat.card ↥A * Nat.card ↥(fixV A)) : X ⊔ Y ⊔ fixV A = ⊤ := by
  have hAX : ∀ a ∈ A, ∀ x ∈ X, a x ∈ X := fun a ha => hLX a (hAL ha)
  have hAY : ∀ a ∈ A, ∀ y ∈ Y, a y ∈ Y := fun a ha => hLY a (hAL ha)
  have hproper : ∀ Z : Subgroup V, Nat.card ↥Z = 8 → (∀ g ∈ L, (∀ z ∈ Z, g z = z) → g = 1) →
      Nat.card ↥(fixV A ⊓ Z) ≤ 4 := by
    intro Z hZ8 hfZ
    have hdvd : Nat.card ↥(fixV A ⊓ Z) ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hZ8]
      exact Subgroup.card_dvd_of_le inf_le_right
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    have hk3 : k ≠ 3 := by
      rintro rfl
      apply hA
      rw [eq_bot_iff]
      intro a ha
      have heq : fixV A ⊓ Z = Z :=
        Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [hk', hZ8]; norm_num)
      have h1 : a = 1 := hfZ a (hAL ha) fun z hz => by
        have hz' : z ∈ fixV A ⊓ Z := by rw [heq]; exact hz
        exact hz'.1 a ha
      rw [h1]
      exact Subgroup.one_mem _
    rw [hk']
    have hk2 : k ≤ 2 := by omega
    calc 2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
      _ = 4 := by norm_num
  have hcX := hproper X hX8 hfX
  have hcY := hproper Y hY8 hfY
  have hplane : ∀ Z : Subgroup V, Nat.card ↥Z = 8 → (∀ g ∈ L, ∀ w ∈ Z, g w ∈ Z) →
      (∀ g ∈ L, (∀ z ∈ Z, g z = z) → g = 1) → Nat.card ↥(fixV A ⊓ Z) = 4 →
      Nat.card ↥A ≤ 4 := by
    intro Z hZ8 hLZ hfZ hc4
    rw [← hc4]
    exact card_le_of_index_two hV inf_le_right (by rw [hZ8, hc4])
      (fun a ha => hLZ a (hAL ha)) (fun a ha c hc => hc.1 a ha)
      (fun a ha h => hfZ a (hAL ha) h)
  have hbound : Nat.card ↥A * (Nat.card ↥(fixV A ⊓ X) * Nat.card ↥(fixV A ⊓ Y)) ≤ 64 := by
    by_cases hX4 : Nat.card ↥(fixV A ⊓ X) = 4
    · have h1 := hplane X hX8 hLX hfX hX4
      rw [hX4]
      calc Nat.card ↥A * (4 * Nat.card ↥(fixV A ⊓ Y)) ≤ 4 * (4 * 4) :=
            Nat.mul_le_mul h1 (Nat.mul_le_mul_left 4 hcY)
        _ = 64 := by norm_num
    by_cases hY4 : Nat.card ↥(fixV A ⊓ Y) = 4
    · have h1 := hplane Y hY8 hLY hfY hY4
      rw [hY4]
      calc Nat.card ↥A * (Nat.card ↥(fixV A ⊓ X) * 4) ≤ 4 * (4 * 4) :=
            Nat.mul_le_mul h1 (Nat.mul_le_mul_right 4 hcX)
        _ = 64 := by norm_num
    have hX2 : Nat.card ↥(fixV A ⊓ X) ≤ 2 := by
      have hdvd : Nat.card ↥(fixV A ⊓ X) ∣ 8 := by
        rw [← hX8]; exact Subgroup.card_dvd_of_le inf_le_right
      have : Nat.card ↥(fixV A ⊓ X) ≠ 3 := fun h => by rw [h] at hdvd; norm_num at hdvd
      omega
    have hY2 : Nat.card ↥(fixV A ⊓ Y) ≤ 2 := by
      have hdvd : Nat.card ↥(fixV A ⊓ Y) ∣ 8 := by
        rw [← hY8]; exact Subgroup.card_dvd_of_le inf_le_right
      have : Nat.card ↥(fixV A ⊓ Y) ≠ 3 := fun h => by rw [h] at hdvd; norm_num at hdvd
      omega
    calc Nat.card ↥A * (Nat.card ↥(fixV A ⊓ X) * Nat.card ↥(fixV A ⊓ Y)) ≤ 8 * (2 * 2) :=
          Nat.mul_le_mul hA8 (Nat.mul_le_mul hX2 hY2)
      _ ≤ 64 := by norm_num
  have hU : Nat.card ↥(X ⊔ Y) = 64 := by
    have h1 := card_sup_mul_card_inf X Y
    rw [hXY, Subgroup.card_bot, mul_one, hX8, hY8] at h1
    exact h1
  have hprod := card_sup_mul_card_inf (X ⊔ Y) (fixV A)
  rw [hU] at hprod
  have hinf : Nat.card ↥((X ⊔ Y) ⊓ fixV A) ≤
      Nat.card ↥(fixV A ⊓ X) * Nat.card ↥(fixV A ⊓ Y) := by
    have h1 := Subgroup.card_le_of_le (inf_fixV_le hXY hAX hAY)
    have h2 := card_sup_mul_card_inf (fixV A ⊓ X) (fixV A ⊓ Y)
    have h3 : 0 < Nat.card ↥((fixV A ⊓ X) ⊓ (fixV A ⊓ Y)) := Nat.card_pos
    calc Nat.card ↥((X ⊔ Y) ⊓ fixV A) ≤ Nat.card ↥((fixV A ⊓ X) ⊔ (fixV A ⊓ Y)) := h1
      _ ≤ Nat.card ↥((fixV A ⊓ X) ⊔ (fixV A ⊓ Y)) *
          Nat.card ↥((fixV A ⊓ X) ⊓ (fixV A ⊓ Y)) := Nat.le_mul_of_pos_right _ h3
      _ = _ := h2
  have hP : 0 < Nat.card ↥(fixV A ⊓ X) * Nat.card ↥(fixV A ⊓ Y) :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  have hle : Nat.card V ≤ Nat.card ↥(X ⊔ Y ⊔ fixV A) := by
    refine Nat.le_of_mul_le_mul_right ?_ hP
    calc Nat.card V * (Nat.card ↥(fixV A ⊓ X) * Nat.card ↥(fixV A ⊓ Y))
        ≤ Nat.card ↥A * Nat.card ↥(fixV A) *
            (Nat.card ↥(fixV A ⊓ X) * Nat.card ↥(fixV A ⊓ Y)) := Nat.mul_le_mul_right _ hoff
      _ = (Nat.card ↥A * (Nat.card ↥(fixV A ⊓ X) * Nat.card ↥(fixV A ⊓ Y))) *
            Nat.card ↥(fixV A) := by ring
      _ ≤ 64 * Nat.card ↥(fixV A) := Nat.mul_le_mul_right _ hbound
      _ = Nat.card ↥(X ⊔ Y ⊔ fixV A) * Nat.card ↥((X ⊔ Y) ⊓ fixV A) := hprod.symm
      _ ≤ Nat.card ↥(X ⊔ Y ⊔ fixV A) *
            (Nat.card ↥(fixV A ⊓ X) * Nat.card ↥(fixV A ⊓ Y)) := Nat.mul_le_mul_left _ hinf
  exact Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) hle)

theorem card_of_nat [Finite V] {n : ℕ} {K : Type} [Field K] {L : Subgroup (MulAut V)}
    {W : Subgroup V} {π : ↥(StatedSL n K) →* ↥L}
    (h : (FFModel.nat (StatedSL n K)).RealizesVia L W ⊥ π) : Nat.card ↥W = Nat.card K ^ n := by
  obtain ⟨β, hβs, hβk, -⟩ := FFC.exists_natMap h
  rw [Nat.card_congr (MulEquiv.ofBijective β ⟨injective_of_ker_bot hβk, hβs⟩).toEquiv]
  change Nat.card (Fin n → K) = _
  rw [Nat.card_fun, Nat.card_fin]

theorem faithful_of_nat {n : ℕ} {K : Type} [Field K] {L : Subgroup (MulAut V)}
    {W : Subgroup V} {π : ↥(StatedSL n K) →* ↥L}
    (h : (FFModel.nat (StatedSL n K)).RealizesVia L W ⊥ π) :
    ∀ g ∈ L, (∀ w ∈ W, g w = w) → g = 1 := by
  obtain ⟨β, hβs, -, hβe⟩ := FFC.exists_natMap h
  intro g hg hfix
  obtain ⟨γ₀, hγ₀⟩ := h.1 ⟨g, hg⟩
  let γ : ↥(StatedSL n K) := γ₀
  have hγ : π γ = ⟨g, hg⟩ := hγ₀
  have hγ1 : γ = 1 := by
    refine natAct_faithful _ γ fun m => ?_
    obtain ⟨u, rfl⟩ := hβs m
    have hu : ((π γ : ↥L) : MulAut V) u = u := by rw [hγ]; exact hfix u u.2
    have hmem : ((π γ : ↥L) : MulAut V) u ∈ W := by rw [hu]; exact u.2
    have h1 : (⟨((π γ : ↥L) : MulAut V) u, hmem⟩ : ↥W) = u := Subtype.ext hu
    rw [← hβe γ u hmem, h1, mul_inv_cancel]
  have : (⟨g, hg⟩ : ↥L) = 1 := by rw [← hγ, hγ1, map_one]
  exact congrArg Subtype.val this

theorem sup_fixV_eq_top_L3 [Finite V] (hV : ∀ v : V, v ^ 2 = 1)
    {G L : Subgroup (MulAut V)} (h : B51Hyp G L) (hGL : G = L) {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2 ^ 1) {X Y : Subgroup V} (hXY : X ⊓ Y = ⊥) (hsup : X ⊔ Y = commV L)
    {π : ↥(StatedSL 3 K) →* ↥L} (hX : (FFModel.nat (StatedSL 3 K)).RealizesVia L X ⊥ π)
    (hY : (FFModel.nat (StatedSL 3 K)).RealizesVia L Y ⊥ π) : commV L ⊔ fixV L = ⊤ := by
  have hLX : ∀ g ∈ L, ∀ w ∈ X, g w ∈ X := fun g hg w hw => hX.2.2.2.1 ⟨g, hg⟩ w hw
  have hLY : ∀ g ∈ L, ∀ w ∈ Y, g w ∈ Y := fun g hg w hw => hY.2.2.2.1 ⟨g, hg⟩ w hw
  have hLW : ∀ g ∈ L, ∀ w ∈ commV L, g w ∈ commV L := FFC.commV_invariant_self L
  have hc : ∀ g ∈ L, ∀ v : V, g v * v⁻¹ ∈ commV L := fun g hg v =>
    Subgroup.subset_closure ⟨g, hg, v, rfl⟩
  have hπi : Function.Injective π := FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hX
  have hcardL : Nat.card ↥L = 168 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective π ⟨hπi, hX.1⟩).toEquiv]
    rw [CFSG.SectionRank.OddCover.card_statedSL_three, hK]
    norm_num
  have hLne : L ≠ ⊥ := fun hL => by
    rw [hL, Subgroup.card_bot] at hcardL
    norm_num at hcardL
  obtain ⟨A, hA⟩ : ∃ A, IsFFStarOffender G A := by
    by_contra hcon
    push Not at hcon
    have hJ : ffJ G = ⊥ := le_antisymm (iSup₂_le fun A hA => absurd hA (hcon A)) bot_le
    exact hLne (hGL ▸ h.2.2.2.2.2.trans hJ)
  have hAL : A ≤ L := hGL ▸ hA.1
  have hA8 : Nat.card ↥A ≤ 8 := by
    have hdvd : Nat.card ↥A ∣ 168 := hcardL ▸ Subgroup.card_dvd_of_le hAL
    have hpow : Nat.card ↥A = 2 ^ rk ↥A := card_eq_two_pow_of_isPGroup hA.2.2.1.isPGroup
    have hk : rk ↥A ≤ 3 := by
      by_contra hk
      push Not at hk
      have h16 : 2 ^ 4 ∣ 168 := (Nat.pow_dvd_pow 2 hk).trans (hpow ▸ hdvd)
      norm_num at h16
    rw [hpow]
    calc 2 ^ rk ↥A ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) hk
      _ = 8 := by norm_num
  have hoff : Nat.card V ≤ Nat.card ↥A * Nat.card ↥(fixV A) := by
    have h1 := hA.2.2.2 ⊥ bot_le
    have h2 : fixV (⊥ : Subgroup (MulAut V)) = ⊤ := by
      rw [eq_top_iff]
      intro v _ x hx
      rw [Subgroup.mem_bot.1 hx]
      rfl
    rw [Subgroup.card_bot, one_mul, h2, Subgroup.card_top] at h1
    exact h1
  have hX8 : Nat.card ↥X = 8 := by rw [card_of_nat hX, hK]; norm_num
  have hY8 : Nat.card ↥Y = 8 := by rw [card_of_nat hY, hK]; norm_num
  have hAtop := sup_fixV_eq_top_of_offender hV hXY hLX hLY hX8 hY8 (faithful_of_nat hX)
    (faithful_of_nat hY) hAL hA.2.1 hA8 hoff
  rw [hsup] at hAtop
  have hA2 : ∀ a ∈ A, a ^ 2 = 1 := hA.2.2.1.2
  have hZ : ∀ z ∈ (⊥ : Subgroup V), ∀ g ∈ L, g z = z := fun z hz g _ => by
    rw [Subgroup.mem_bot.1 hz, map_one]
  obtain ⟨DX⟩ := FFC.exists_natQuot3 (H := L) (U := X) (Z := ⊥) ⟨K, inferInstance,
    inferInstance, hK, π, hX⟩
  obtain ⟨DY⟩ := FFC.exists_natQuot3 (H := L) (U := Y) (Z := ⊥) ⟨K, inferInstance,
    inferInstance, hK, π, hY⟩
  have hRX := FFC.NatQuot3.hR DX hZ hAL hA.2.1 hA2 hLX
  have hRY := FFC.NatQuot3.hR DY hZ hAL hA.2.1 hA2 hLY
  exact FFC.sup_fixV_eq_top_of_R hLW hc hAtop (FFC.hR_of_directSum hsup hXY hLX hLY hLW hRX hRY)

end CFSG.Quasithin.B5.P2
