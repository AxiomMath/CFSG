module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteXviiCore
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteXviiRel

public section

namespace CFSG.Quasithin.Fan86.Tutte.Xvii

variable {H : Type*} [Group H] {s : ℕ} {r l ξ : H} {Hs : ℕ → Subgroup H}

theorem swap_mul {x y : H} (hx : x * x = 1) (h : x * y * x = y⁻¹) : x * y = y⁻¹ * x := by
  calc x * y = x * y * x * x := by rw [mul_assoc (x * y) x x, hx, mul_one]
    _ = y⁻¹ * x := by rw [h]

theorem pow_odd_of_sq {e : H} (he : e * e = 1) {k : ℕ} (hk : Odd k) : e ^ k = e := by
  obtain ⟨j, rfl⟩ := hk
  have he2 : e ^ 2 = 1 := by rw [pow_two]; exact he
  rw [pow_succ, pow_mul, he2, one_pow, one_mul]

theorem sq_eq_one_of_lt (B : XviiInput s r l Hs) {i : ℕ} (his : i < s) (hab : Abel Hs (i - 1)) :
    ∀ k : ℕ, 1 ≤ k → k < i → tx r l k * tx r l k = 1 := fun k hk1 hki => by
  have := B.abel_sq_eq_one (by omega : i - 1 < s) hab hk1 (by omega : k ≤ i - 1)
  rwa [pow_two] at this

theorem sq_ne_one (B : XviiInput s r l Hs) {i : ℕ} (hi : 1 ≤ i) (his : i < s)
    (hab : Abel Hs (i - 1)) (hnab : ¬ Abel Hs i) : tx r l i * tx r l i ≠ 1 := by
  intro hz
  apply hnab
  refine (B.abelian_iff hi his).2 fun k hk1 hki => ?_
  rw [pow_two]
  rcases Nat.lt_or_ge k i with hlt | hge
  · exact sq_eq_one_of_lt B his hab k hk1 hlt
  · have : k = i := le_antisymm hki hge
    rw [this]
    exact hz

theorem xvii_support (h : IsTutteSys s r l ξ Hs) (B : XviiInput s r l Hs) {i : ℕ} (hi : 1 ≤ i)
    (his : i < s) (hab : Abel Hs (i - 1)) (hnab : ¬ Abel Hs i) {T : Finset ℕ}
    (hTsub : T ⊆ Finset.Icc 1 (i - 1)) (hTz : tx r l i ^ 2 = pset r l T) (hTeven : Even T.card)
    (hTsym : ∀ t ∈ T, i - t ∈ T) {m : ℕ} (hmT : m ∈ T) (hmle : ∀ t ∈ T, m ≤ t) :
    2 * m < i ∧ s ≤ i + m := by
  have hn : i - 1 < s := by omega
  have hx2 := sq_eq_one_of_lt B his hab
  have hz2ne := sq_ne_one B hi his hab hnab
  have hzT : tx r l i * tx r l i = pset r l T := by rw [← pow_two]; exact hTz
  have hTne : T.Nonempty := ⟨m, hmT⟩
  have hTI : ∀ t ∈ T, 1 ≤ t ∧ t ≤ i - 1 := fun t ht => Finset.mem_Icc.1 (hTsub ht)
  set M := T.max' hTne with hMdef
  have hMT : M ∈ T := Finset.max'_mem T hTne
  have htle : ∀ t ∈ T, t ≤ M := fun t ht => Finset.le_max' T t ht
  have hMeq : M = i - m := by
    have h1 := htle _ (hTsym m hmT)
    have h2 := hmle _ (hTsym M hMT)
    have h3 := hTI M hMT
    have h4 := hTI m hmT
    omega
  have hcard : 2 ≤ T.card := by
    have h0 : 0 < T.card := Finset.card_pos.2 hTne
    obtain ⟨c, hc⟩ := hTeven
    omega
  have hmM : m < M := by
    have := Finset.min'_lt_max'_of_card T (by omega : 1 < T.card)
    have hmin : T.min' hTne = m :=
      le_antisymm (Finset.min'_le T m hmT) (hmle _ (Finset.min'_mem T hTne))
    rwa [hmin] at this
  have hm1 : 1 ≤ m := (hTI m hmT).1
  have h2m : 2 * m < i := by omega
  refine ⟨h2m, ?_⟩
  by_contra hlt
  have hlt' : i + m < s := by omega
  set T₁ := T.erase m with hT₁
  set T₂ := T.erase M with hT₂
  set T₃ := T₂.image (· + m) with hT₃
  have hT₁sub : T₁ ⊆ Finset.Icc 1 (i - 1) := fun t ht => hTsub (Finset.mem_of_mem_erase ht)
  have hT₂sub : T₂ ⊆ Finset.Icc 1 (i - 1 - m) := by
    intro t ht
    have ht' := Finset.mem_of_mem_erase ht
    have hne : t ≠ M := Finset.ne_of_mem_erase ht
    have := htle t ht'
    have := (hTI t ht').1
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hT₂sub' : T₂ ⊆ Finset.Icc 1 (i - 1) := fun t ht => by
    have := Finset.mem_Icc.1 (hT₂sub ht)
    exact Finset.mem_Icc.2 ⟨this.1, by omega⟩
  have hT₃mem : ∀ c ∈ T₃, m < c ∧ c < i := by
    intro c hc
    obtain ⟨t, ht, rfl⟩ := Finset.mem_image.1 hc
    have ht' := Finset.mem_of_mem_erase ht
    have hne : t ≠ M := Finset.ne_of_mem_erase ht
    have h1 := hmle t ht'
    have h2 := htle t ht'
    omega
  have hT₃sub : T₃ ⊆ Finset.Icc 1 (i - 1) := fun c hc => by
    have := hT₃mem c hc
    exact Finset.mem_Icc.2 ⟨by omega, by omega⟩
  have hT₁mem : ∀ c ∈ T₁, m < c ∧ c < i := by
    intro c hc
    have hc' := Finset.mem_of_mem_erase hc
    have hne : c ≠ m := Finset.ne_of_mem_erase hc
    have := hmle c hc'
    have := (hTI c hc').2
    omega
  have hc1 : T₁.card = T.card - 1 := Finset.card_erase_of_mem hmT
  have hc2 : T₂.card = T.card - 1 := Finset.card_erase_of_mem hMT
  have hc3 : T₃.card = T₂.card := Finset.card_image_of_injective _ (add_left_injective m)
  have hTmod : T.card % 2 = 0 := Nat.even_iff.1 hTeven
  have hodd1 : Odd T₁.card := Nat.odd_iff.2 (by omega)
  have hodd2 : Odd T₂.card := Nat.odd_iff.2 (by omega)
  have hodd3 : Odd T₃.card := Nat.odd_iff.2 (by omega)
  have hmi : m < i := by omega
  set z := tx r l i with hz
  set y := tx r l ((i + m : ℕ) : ℤ) with hy
  set e := tx r l m with he
  have hee : e * e = 1 := hx2 m hm1 hmi
  have hmI : m ∈ Finset.Icc 1 (i - 1) := Finset.mem_Icc.2 ⟨hm1, by omega⟩
  have hMI : M ∈ Finset.Icc 1 (i - 1) := hTsub hMT
  have heA : e ∈ Hs (i - 1) := tx_mem_le h (by omega) hn.le
  have hy2 : ∀ c, m < c → c < i → tx r l c * y = y⁻¹ * tx r l c := fun c hmc hci =>
    swap_mul (hx2 c (by omega) hci) (rel_R2 hx2 hmc hci)
  have hz2 : ∀ c, 1 ≤ c → c < i → tx r l c * z = z⁻¹ * tx r l c := fun c hc1 hci =>
    swap_mul (hx2 c hc1 hci) (rel_a hx2 hc1 hci)
  have hR : pset r l T₁ * pset r l T₁ = 1 := pset_mul_self B hn hab hT₁sub
  have hP : pset r l T₃ * pset r l T₃ = 1 := pset_mul_self B hn hab hT₃sub
  have heR : e * pset r l T₁ = pset r l T₁ * e :=
    hab _ heA _ (pset_mem B hn hab h T₁ hT₁sub)
  have hRy : pset r l T₁ * y = y⁻¹ * pset r l T₁ :=
    (pset_conj B hn hab (g := y) T₁ hT₁sub
      (fun c hc => hy2 c (hT₁mem c hc).1 (hT₁mem c hc).2)).2 hodd1
  have hPy : pset r l T₃ * y = y⁻¹ * pset r l T₃ :=
    (pset_conj B hn hab (g := y) T₃ hT₃sub
      (fun c hc => hy2 c (hT₃mem c hc).1 (hT₃mem c hc).2)).2 hodd3
  have hPz : pset r l T₃ * z = z⁻¹ * pset r l T₃ :=
    (pset_conj B hn hab (g := z) T₃ hT₃sub
      (fun c hc => hz2 c (by have := hT₃mem c hc; omega) (hT₃mem c hc).2)).2 hodd3
  have hzR : z * z = e * pset r l T₁ := by
    rw [hzT]
    have h1 := pset_insert B hn hab hmI hT₁sub (Finset.notMem_erase m T)
    rw [Finset.insert_erase hmT] at h1
    exact h1
  have hey : e * y * e * y = pset r l T₃ * z := by
    have h3 := rel_R3 hx2 hm1 hmi
    have hxM : tx r l M * pset r l T₂ = pset r l T := by
      rw [← pset_insert B hn hab hMI hT₂sub' (Finset.notMem_erase M T), Finset.insert_erase hMT]
    have hS := shift_pset B hn hab h hm1 (by omega) hee T₂ hT₂sub
    have hxMs := shift_x r l (M : ℤ) (m : ℤ)
    have hcM : (M : ℤ) + (m : ℤ) = (i : ℤ) := by omega
    rw [hcM, ← inv_tx hx2 hm1 hmi, inv_inv] at hxMs
    have hpow : e ^ T₂.card = e := pow_odd_of_sq hee hodd2
    have hconj : r ^ (-(m : ℤ)) * (z * z) * r ^ (m : ℤ) =
        (r ^ (-(m : ℤ)) * tx r l M * r ^ (m : ℤ)) *
          (r ^ (-(m : ℤ)) * pset r l T₂ * r ^ (m : ℤ)) := by
      rw [hzT, ← hxM]
      group
    rw [hconj, hxMs, hS, hpow] at h3
    calc e * y * e * y = e * y * (e * y) := by group
      _ = e * z * (e * pset r l T₃) := h3
      _ = (e * z * e) * pset r l T₃ := by group
      _ = z⁻¹ * pset r l T₃ := by rw [rel_a hx2 hm1 hmi]
      _ = pset r l T₃ * z := hPz.symm
  have hyK : y ∈ Hs (s - 1) := tx_mem_le h (by omega) (by omega)
  have hord : y ^ (2 ^ (s - 1)) = 1 := by
    have := pow_card_eq_one' (G := Hs (s - 1)) (x := ⟨y, hyK⟩)
    rw [h.card_lt (s - 1) (by omega)] at this
    exact congrArg Subtype.val this
  exact hz2ne (core hee hP hR heR (rel_R1 hx2 hm1 hmi) hRy hPy hey hPz hzR hord)

theorem xvii_of_input (h : IsTutteSys s r l ξ Hs) (B : XviiInput s r l Hs) {i : ℕ} (hi : 1 ≤ i)
    (his : i < s) (hab : Abel Hs (i - 1)) (hnab : ¬ Abel Hs i) :
    ∃ m : ℕ, 1 ≤ m ∧ 2 * m < i ∧ s ≤ i + m := by
  obtain ⟨T, hTsub, hTz, hTeven, hTsym⟩ := B.sq_support hi his hab
  have hTne : T.Nonempty := by
    rcases T.eq_empty_or_nonempty with h0 | h0
    · exfalso
      apply sq_ne_one B hi his hab hnab
      rw [← pow_two, hTz, h0, pset_empty]
    · exact h0
  have hmT : T.min' hTne ∈ T := Finset.min'_mem T hTne
  obtain ⟨h1, h2⟩ := xvii_support h B hi his hab hnab hTsub hTz hTeven hTsym hmT
    (fun t ht => Finset.min'_le T t ht)
  exact ⟨T.min' hTne, (Finset.mem_Icc.1 (hTsub hmT)).1, h1, h2⟩

theorem abel_of_le_two_thirds_of_input (h : IsTutteSys s r l ξ Hs) (B : XviiInput s r l Hs)
    {k : ℕ} (hk : k < s) (h3 : 3 * k ≤ 2 * s) : Abel Hs k := by
  by_contra hnab
  classical
  have hex : ∃ j, ¬ Abel Hs j := ⟨k, hnab⟩
  have hj : ¬ Abel Hs (Nat.find hex) := Nat.find_spec hex
  have hjk : Nat.find hex ≤ k := Nat.find_min' hex hnab
  have hj0 : Nat.find hex ≠ 0 := by
    intro h0
    apply hj
    rw [h0]
    intro a ha b hb
    rw [h.zero, Subgroup.mem_bot] at ha hb
    rw [ha, hb]
  have hprev : Abel Hs (Nat.find hex - 1) := by
    by_contra hcon
    exact Nat.find_min hex (by omega : Nat.find hex - 1 < Nat.find hex) hcon
  obtain ⟨m, hm1, hm2, hsm⟩ := xvii_of_input h B (i := Nat.find hex) (by omega) (by omega) hprev hj
  omega

end CFSG.Quasithin.Fan86.Tutte.Xvii
