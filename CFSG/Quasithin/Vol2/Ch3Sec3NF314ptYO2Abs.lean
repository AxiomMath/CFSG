module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptYO2Psl
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptYO2Split
public import CFSG.Quasithin.Vol2.Ch3Sec3L2qCore

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Quasithin CFSG.GorensteinWalter CFSG.Quasithin.H13

variable {Q : Type} [Group Q] [Finite Q]

theorem yo2_comm_of_two_sub {A A' Rb : Subgroup Q}
    (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥)
    (hA : ∀ R : Subgroup Q, R ≤ A → IsPGroup 2 R → ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hA' : ∀ R : Subgroup Q, R ≤ A' → IsPGroup 2 R → ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hRb : Rb ≤ A ⊔ A') (hR2 : IsPGroup 2 Rb) : ∀ r ∈ Rb, ∀ s ∈ Rb, r * s = s * r := by
  have hc' : ∀ a ∈ A', ∀ b ∈ A, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hi' : A' ⊓ A = ⊥ := by rw [inf_comm]; exact hi
  have hRb' : Rb ≤ A' ⊔ A := by rw [sup_comm]; exact hRb
  let π₂ : ↥(A ⊔ A') →* ↥A' := L2qC.proj2 hc hi
  let π₁ : ↥(A' ⊔ A) →* ↥A := L2qC.proj2 hc' hi'
  let g₂ : ↥Rb →* ↥A' := π₂.comp (Subgroup.inclusion hRb)
  let g₁ : ↥Rb →* ↥A := π₁.comp (Subgroup.inclusion hRb')
  have hdec : ∀ r : ↥Rb, (r : Q) = ((g₁ r : ↥A) : Q) * ((g₂ r : ↥A') : Q) := by
    intro r
    obtain ⟨a, ha, h1⟩ := L2qC.proj2_spec hc hi (Subgroup.inclusion hRb r)
    obtain ⟨a', ha', h2⟩ := L2qC.proj2_spec hc' hi' (Subgroup.inclusion hRb' r)
    have h3 : (a' : Q) * ((π₁ (Subgroup.inclusion hRb' r) : ↥A) : Q) =
        ((π₁ (Subgroup.inclusion hRb' r) : ↥A) : Q) * a' :=
      hc' a' ha' _ (π₁ (Subgroup.inclusion hRb' r)).2
    have h4 : ((π₁ (Subgroup.inclusion hRb' r) : ↥A) : Q) * a' =
        a * ((π₂ (Subgroup.inclusion hRb r) : ↥A') : Q) := by
      have h5 : (r : Q) = a' * ((π₁ (Subgroup.inclusion hRb' r) : ↥A) : Q) := h2
      have h6 : (r : Q) = a * ((π₂ (Subgroup.inclusion hRb r) : ↥A') : Q) := h1
      rw [← h6, h5, h3]
    obtain ⟨e1, -⟩ := BenC.eq_of_mul_eq hi (π₁ (Subgroup.inclusion hRb' r)).2 ha ha'
      (π₂ (Subgroup.inclusion hRb r)).2 h4
    have h6 : (r : Q) = a * ((π₂ (Subgroup.inclusion hRb r) : ↥A') : Q) := h1
    rw [← e1] at h6
    exact h6
  have hg₁2 : IsPGroup 2 g₁.range :=
    hR2.of_surjective g₁.rangeRestrict g₁.rangeRestrict_surjective
  have hg₂2 : IsPGroup 2 g₂.range :=
    hR2.of_surjective g₂.rangeRestrict g₂.rangeRestrict_surjective
  set R₁ : Subgroup Q := g₁.range.map A.subtype with hR₁
  set R₂ : Subgroup Q := g₂.range.map A'.subtype with hR₂
  have hR₁A : R₁ ≤ A := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hR₂A' : R₂ ≤ A' := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hR₁2 : IsPGroup 2 R₁ := hg₁2.map _
  have hR₂2 : IsPGroup 2 R₂ := hg₂2.map _
  intro r hr s hs
  have e1 := hdec ⟨r, hr⟩
  have e2 := hdec ⟨s, hs⟩
  have hab : ((g₁ ⟨r, hr⟩ : ↥A) : Q) * ((g₁ ⟨s, hs⟩ : ↥A) : Q) =
      ((g₁ ⟨s, hs⟩ : ↥A) : Q) * ((g₁ ⟨r, hr⟩ : ↥A) : Q) :=
    hA R₁ hR₁A hR₁2 _ ⟨g₁ ⟨r, hr⟩, ⟨⟨r, hr⟩, rfl⟩, rfl⟩ _ ⟨g₁ ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩, rfl⟩
  have hbb : ((g₂ ⟨r, hr⟩ : ↥A') : Q) * ((g₂ ⟨s, hs⟩ : ↥A') : Q) =
      ((g₂ ⟨s, hs⟩ : ↥A') : Q) * ((g₂ ⟨r, hr⟩ : ↥A') : Q) :=
    hA' R₂ hR₂A' hR₂2 _ ⟨g₂ ⟨r, hr⟩, ⟨⟨r, hr⟩, rfl⟩, rfl⟩ _ ⟨g₂ ⟨s, hs⟩, ⟨⟨s, hs⟩, rfl⟩, rfl⟩
  have hcr := hc _ (g₁ ⟨s, hs⟩).2 _ (g₂ ⟨r, hr⟩).2
  have hcs := hc _ (g₁ ⟨r, hr⟩).2 _ (g₂ ⟨s, hs⟩).2
  set ar : Q := ((g₁ ⟨r, hr⟩ : ↥A) : Q)
  set br : Q := ((g₂ ⟨r, hr⟩ : ↥A') : Q)
  set as : Q := ((g₁ ⟨s, hs⟩ : ↥A) : Q)
  set bs : Q := ((g₂ ⟨s, hs⟩ : ↥A') : Q)
  calc r * s = (ar * br) * (as * bs) := by
        rw [show r = ar * br from e1, show s = as * bs from e2]
    _ = (ar * as) * (br * bs) := by
        calc (ar * br) * (as * bs) = ar * (br * as) * bs := by group
          _ = ar * (as * br) * bs := by rw [← hcr]
          _ = (ar * as) * (br * bs) := by group
    _ = (as * ar) * (bs * br) := by rw [hab, hbb]
    _ = (as * bs) * (ar * br) := by
        calc (as * ar) * (bs * br) = as * (ar * bs) * br := by group
          _ = as * (bs * ar) * br := by rw [← hcs]
          _ = (as * bs) * (ar * br) := by group
    _ = s * r := by
        rw [show r = ar * br from e1, show s = as * bs from e2]

theorem yo2_small_unique {W : Subgroup Q} (hW : Nat.card W ≤ 2) {u v : Q} (hu : u ∈ W)
    (hv : v ∈ W) (hu1 : u ≠ 1) (hv1 : v ≠ 1) : u = v := by
  by_contra huv
  have hsub : ({1, u, v} : Set Q) ⊆ (W : Set Q) := by
    intro g hg
    rcases hg with rfl | rfl | rfl
    · exact W.one_mem
    · exact hu
    · exact hv
  have h3 : ({1, u, v} : Set Q).ncard = 3 :=
    Set.ncard_eq_three.mpr ⟨1, u, v, fun h => hu1 h.symm, fun h => hv1 h.symm, huv, rfl⟩
  have h4 : ({1, u, v} : Set Q).ncard ≤ (W : Set Q).ncard :=
    Set.ncard_le_ncard hsub (Set.toFinite _)
  have h5 : (W : Set Q).ncard = Nat.card W := (Nat.card_coe_set_eq (W : Set Q)).symm
  omega

theorem yo2_small_sq {W : Subgroup Q} (hW : Nat.card W ≤ 2) {u : Q} (hu : u ∈ W) :
    u * u = 1 := by
  have h1 : orderOf u ∣ Nat.card W := Subgroup.orderOf_dvd_natCard W hu
  have h2 : 0 < Nat.card W := Nat.card_pos
  have h3 : orderOf u ∣ 2 := by
    interval_cases hc : Nat.card W
    · exact h1.trans (by norm_num)
    · exact h1
  have := orderOf_dvd_iff_pow_eq_one.mp h3
  simpa [pow_two] using this

theorem yo2_comm_of_small {A A' Rb : Subgroup Q} (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a)
    (hRA : Rb ≤ A ⊔ A') {x : Q} (hxA : x ∈ A) (hx3 : x ^ 3 = 1)
    (hxR : ∀ r ∈ Rb, x * r * x⁻¹ ∈ Rb) (hW : Nat.card ↥(Rb ⊓ A) ≤ 2) :
    ∀ r ∈ Rb, x * r = r * x := by
  intro r hr
  obtain ⟨a, ha, b, hb, hab⟩ := (BenC.mem_sup_iff hc).mp (hRA hr)
  have hxb : x * b = b * x := hc x hxA b hb
  have hxb' : b * x⁻¹ = x⁻¹ * b := by
    calc b * x⁻¹ = x⁻¹ * (x * b) * x⁻¹ := by group
      _ = x⁻¹ * (b * x) * x⁻¹ := by rw [hxb]
      _ = x⁻¹ * b := by group
  set w : Q := x * a * x⁻¹ * a⁻¹ with hw
  have hwA : w ∈ A := A.mul_mem (A.mul_mem (A.mul_mem hxA ha) (A.inv_mem hxA)) (A.inv_mem ha)
  have hcomm : x * r * x⁻¹ * r⁻¹ = w := by
    rw [hab, hw]
    calc x * (a * b) * x⁻¹ * (a * b)⁻¹ = x * a * (b * x⁻¹) * b⁻¹ * a⁻¹ := by group
      _ = x * a * (x⁻¹ * b) * b⁻¹ * a⁻¹ := by rw [hxb']
      _ = x * a * x⁻¹ * a⁻¹ := by group
  have hwR : w ∈ Rb := by
    rw [← hcomm]
    exact Rb.mul_mem (hxR r hr) (Rb.inv_mem hr)
  have hwW : w ∈ Rb ⊓ A := ⟨hwR, hwA⟩
  have hxwW : x * w * x⁻¹ ∈ Rb ⊓ A :=
    ⟨hxR w hwR, A.mul_mem (A.mul_mem hxA hwA) (A.inv_mem hxA)⟩
  have hw1 : w = 1 := by
    by_contra hw1
    have hxw : x * w * x⁻¹ = w := by
      refine yo2_small_unique hW hxwW hwW ?_ hw1
      intro h
      apply hw1
      have : w = x⁻¹ * (x * w * x⁻¹) * x := by group
      rw [this, h]
      group
    have hww := yo2_small_sq hW hwW
    have e1 : x * a * x⁻¹ = w * a := by rw [hw]; group
    have e2 : x * (x * a * x⁻¹) * x⁻¹ = a := by
      rw [e1]
      calc x * (w * a) * x⁻¹ = (x * w * x⁻¹) * (x * a * x⁻¹) := by group
        _ = w * (w * a) := by rw [hxw, e1]
        _ = (w * w) * a := by group
        _ = a := by rw [hww, one_mul]
    have hx3' : x * x * x = 1 := by rw [← pow_three']; exact hx3
    have e3 : x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ = a := by
      calc x * (x * (x * a * x⁻¹) * x⁻¹) * x⁻¹ = (x * x * x) * a * (x * x * x)⁻¹ := by group
        _ = a := by rw [hx3']; group
    rw [e2] at e3
    rw [e1] at e3
    apply hw1
    have : w * a = 1 * a := by rw [e3, one_mul]
    exact mul_right_cancel this
  rw [hw1] at hcomm
  have : x * r * x⁻¹ = r := by
    have h := congrArg (· * r) hcomm
    simpa using h
  exact mul_inv_eq_iff_eq_mul.mp this

theorem yo2_card_symm {A A' Rb : Subgroup Q} {σ : Q} (hσR : ∀ r, r ∈ Rb ↔ σ * r * σ⁻¹ ∈ Rb)
    (hσA : ∀ a, a ∈ A ↔ σ * a * σ⁻¹ ∈ A') : Nat.card ↥(Rb ⊓ A') = Nat.card ↥(Rb ⊓ A) := by
  refine Nat.card_congr
    { toFun := fun v => ⟨σ⁻¹ * v * σ, ?_⟩
      invFun := fun u => ⟨σ * u * σ⁻¹, ?_⟩
      left_inv := fun v => ?_
      right_inv := fun u => ?_ }
  · refine ⟨(hσR _).mpr ?_, (hσA _).mpr ?_⟩
    · have : σ * (σ⁻¹ * (v : Q) * σ) * σ⁻¹ = v := by group
      rw [this]
      exact v.2.1
    · have : σ * (σ⁻¹ * (v : Q) * σ) * σ⁻¹ = v := by group
      rw [this]
      exact v.2.2
  · exact ⟨(hσR _).mp u.2.1, (hσA _).mp u.2.2⟩
  · ext
    show σ * (σ⁻¹ * (v : Q) * σ) * σ⁻¹ = v
    group
  · ext
    show σ⁻¹ * (σ * (u : Q) * σ⁻¹) * σ = u
    group

theorem yo2_abstract {F : Type} [Field F] [Finite F] {q : ℕ}
    (hF : Nat.card F = q) (hq : q.Prime) (hq5 : 5 ≤ q) (h3 : q % 8 = 3 ∨ q % 8 = 5)
    {A A' : Subgroup Q} (eA : ↥A ≃* PSL2 F) (eA' : ↥A' ≃* PSL2 F)
    (hc : ∀ a ∈ A, ∀ b ∈ A', a * b = b * a) (hi : A ⊓ A' = ⊥)
    {Yb Rb Pb : Subgroup Q} (hYb : Yb ≤ A ⊔ A') (hRY : Rb ≤ Yb)
    (hRN : ∀ y ∈ Yb, ∀ r ∈ Rb, y * r * y⁻¹ ∈ Rb) (hR2 : IsPGroup 2 Rb)
    (hPY : Pb ≤ Yb) (hP9 : Nat.card Pb = 9) (hP3 : ∀ y ∈ Pb, y ^ 3 = 1)
    (hYRP : ∀ y ∈ Yb, ∃ r ∈ Rb, ∃ p ∈ Pb, y = r * p)
    {σ : Q} (hσR : ∀ r, r ∈ Rb ↔ σ * r * σ⁻¹ ∈ Rb) (hσA : ∀ a, a ∈ A ↔ σ * a * σ⁻¹ ∈ A') :
    (∀ r ∈ Rb, ∀ y ∈ Yb, r * y = y * r) ∨
      (∀ τ : Q, (∀ r, r ∈ Rb ↔ τ * r * τ⁻¹ ∈ Rb) →
        (∃ k ∈ A, ∀ a ∈ A, τ * a * τ⁻¹ = k * a * k⁻¹) →
        (∃ k ∈ A', ∀ a ∈ A', τ * a * τ⁻¹ = k * a * k⁻¹) → (∃ m : ℕ, τ ^ 2 ^ m = 1) →
        ∀ y ∈ Yb, τ * y * τ⁻¹ * y⁻¹ ∈ Rb) := by
  classical
  have hc' : ∀ a ∈ A', ∀ b ∈ A, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hRA : Rb ≤ A ⊔ A' := hRY.trans hYb
  have hRA' : Rb ≤ A' ⊔ A := by rw [sup_comm]; exact hRA
  have hcyc : ∀ B : Subgroup Q, B ≤ A → IsPGroup 3 B → IsCyclic B := fun B hBA hB =>
    yo2_cyclic_three hF hq hq5 eA B hBA hB
  have hcyc' : ∀ B : Subgroup Q, B ≤ A' → IsPGroup 3 B → IsCyclic B := fun B hBA hB =>
    yo2_cyclic_three hF hq hq5 eA' B hBA hB
  obtain ⟨x₁, hx₁, x₂, hx₂, -, -, hsplit⟩ :=
    yo2_split_nine hc hi hcyc hcyc' (hPY.trans hYb) hP9 hP3
  have hx₁P : x₁ ∈ Pb := hx₁.1
  have hx₁A : x₁ ∈ A := hx₁.2
  have hx₂P : x₂ ∈ Pb := hx₂.1
  have hx₂A : x₂ ∈ A' := hx₂.2
  have hx₁3 : x₁ ^ 3 = 1 := hP3 x₁ hx₁P
  have hx₂3 : x₂ ^ 3 = 1 := hP3 x₂ hx₂P
  have hA2 := fun (R : Subgroup Q) (hR : R ≤ A) (h2 : IsPGroup 2 R) =>
    yo2_psl2_two_sub hF hq hq5 h3 eA hR h2
  have hA2' := fun (R : Subgroup Q) (hR : R ≤ A') (h2 : IsPGroup 2 R) =>
    yo2_psl2_two_sub hF hq hq5 h3 eA' hR h2
  have hRab : ∀ r ∈ Rb, ∀ s ∈ Rb, r * s = s * r :=
    yo2_comm_of_two_sub hc hi (fun R hR h2 => (hA2 R hR h2).2.1) (fun R hR h2 => (hA2' R hR h2).2.1)
      hRA hR2
  have hW2 : IsPGroup 2 ↥(Rb ⊓ A) := hR2.to_inf_left
  have hW2' : IsPGroup 2 ↥(Rb ⊓ A') := hR2.to_inf_left
  have hsymm : Nat.card ↥(Rb ⊓ A') = Nat.card ↥(Rb ⊓ A) := yo2_card_symm hσR hσA
  by_cases hbad : Nat.card ↥(Rb ⊓ A) = 4
  ·
    right
    intro τ hτR hinA hinA' hτ2 y hy
    have hbad' : Nat.card ↥(Rb ⊓ A') = 4 := by rw [hsymm, hbad]
    obtain ⟨k, hkA, hk⟩ := hinA
    obtain ⟨k', hk'A, hk'⟩ := hinA'
    obtain ⟨m, hm⟩ := hτ2
    have key : ∀ (B : Subgroup Q) (e : ↥B ≃* PSL2 F) (hBsub : (Rb ⊓ B) ≤ B) (kk : Q) (hkB : kk ∈ B)
        (hkk : ∀ a ∈ B, τ * a * τ⁻¹ = kk * a * kk⁻¹) (hcard : Nat.card ↥(Rb ⊓ B) = 4)
        (hB2 : ∀ R : Subgroup Q, R ≤ B → IsPGroup 2 R →
          Nat.card R = 4 → ¬ 2 ∣ (R.subgroupOf B).index), kk ∈ Rb := by
      intro B e hBsub kk hkB hkk hcard hB2
      have hkpow : ∀ n : ℕ, ∀ a ∈ B, τ ^ n * a * (τ ^ n)⁻¹ = kk ^ n * a * (kk ^ n)⁻¹ := by
        intro n
        induction n with
        | zero => intro a ha; simp
        | succ n ih =>
          intro a ha
          have h1 : kk ^ n * a * (kk ^ n)⁻¹ ∈ B :=
            B.mul_mem (B.mul_mem (B.pow_mem hkB n) ha) (B.inv_mem (B.pow_mem hkB n))
          calc τ ^ (n + 1) * a * (τ ^ (n + 1))⁻¹
              = τ * (τ ^ n * a * (τ ^ n)⁻¹) * τ⁻¹ := by rw [pow_succ']; group
            _ = τ * (kk ^ n * a * (kk ^ n)⁻¹) * τ⁻¹ := by rw [ih a ha]
            _ = kk * (kk ^ n * a * (kk ^ n)⁻¹) * kk⁻¹ := hkk _ h1
            _ = kk ^ (n + 1) * a * (kk ^ (n + 1))⁻¹ := by rw [pow_succ']; group
      have hk2 : kk ^ 2 ^ m = 1 := by
        refine yo2_center_trivial hF hq hq5 e (B.pow_mem hkB _) ?_
        intro a ha
        have h1 := hkpow (2 ^ m) a ha
        rw [hm] at h1
        simp only [inv_one, one_mul, mul_one] at h1
        have h2 : kk ^ 2 ^ m * a = a * kk ^ 2 ^ m := by
          calc kk ^ 2 ^ m * a = (kk ^ 2 ^ m * a * (kk ^ 2 ^ m)⁻¹) * kk ^ 2 ^ m := by group
            _ = a * kk ^ 2 ^ m := by rw [← h1]
        exact h2
      have hWB : Rb ⊓ B ≤ B := hBsub
      have hnorm : kk ∈ Subgroup.normalizer ((Rb ⊓ B : Subgroup Q) : Set Q) := by
        rw [Subgroup.mem_normalizer_iff]
        intro w
        constructor
        · intro hw
          have hwB : w ∈ B := hw.2
          refine ⟨?_, B.mul_mem (B.mul_mem hkB hwB) (B.inv_mem hkB)⟩
          rw [← hkk w hwB]
          exact (hτR w).mp hw.1
        · intro hw
          have hwB : w ∈ B := by
            have := B.mul_mem (B.mul_mem (B.inv_mem hkB) hw.2) hkB
            simpa [mul_assoc] using this
          refine ⟨?_, hwB⟩
          have h1 := hw.1
          rw [← hkk w hwB] at h1
          exact (hτR w).mpr h1
      have hWB2 : IsPGroup 2 ↥((Rb ⊓ B).subgroupOf B) :=
        (hR2.to_inf_left : IsPGroup 2 ↥(Rb ⊓ B)).of_equiv (Subgroup.subgroupOfEquivOfLe hWB).symm
      have hnorm' : (⟨kk, hkB⟩ : ↥B) ∈
          Subgroup.normalizer (((Rb ⊓ B).subgroupOf B : Subgroup ↥B) : Set ↥B) := by
        rw [Subgroup.mem_normalizer_iff]
        intro g
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
        exact (Subgroup.mem_normalizer_iff.mp hnorm) (g : Q)
      have hmem := yo2_mem_sylow_of_normalizes hWB2 (hB2 (Rb ⊓ B) hWB (hR2.to_inf_left) hcard)
        hnorm' ⟨m, Subtype.ext hk2⟩
      exact (Subgroup.mem_subgroupOf.mp hmem).1
    have hkR : k ∈ Rb :=
      key A eA inf_le_right k hkA hk hbad (fun R hR h2 => (hA2 R hR h2).2.2)
    have hk'R : k' ∈ Rb :=
      key A' eA' inf_le_right k' hk'A hk' hbad' (fun R hR h2 => (hA2' R hR h2).2.2)
    have hcx₁ : τ * x₁ * τ⁻¹ * x₁⁻¹ ∈ Rb := by
      rw [hk x₁ hx₁A]
      have : k * x₁ * k⁻¹ * x₁⁻¹ = k * (x₁ * k⁻¹ * x₁⁻¹) := by group
      rw [this]
      exact Rb.mul_mem hkR (hRN x₁ (hPY hx₁P) k⁻¹ (Rb.inv_mem hkR))
    have hcx₂ : τ * x₂ * τ⁻¹ * x₂⁻¹ ∈ Rb := by
      rw [hk' x₂ hx₂A]
      have : k' * x₂ * k'⁻¹ * x₂⁻¹ = k' * (x₂ * k'⁻¹ * x₂⁻¹) := by group
      rw [this]
      exact Rb.mul_mem hk'R (hRN x₂ (hPY hx₂P) k'⁻¹ (Rb.inv_mem hk'R))
    have hmul : ∀ g h : Q, g ∈ Yb → h ∈ Yb → τ * g * τ⁻¹ * g⁻¹ ∈ Rb → τ * h * τ⁻¹ * h⁻¹ ∈ Rb →
        τ * (g * h) * τ⁻¹ * (g * h)⁻¹ ∈ Rb := by
      intro g h hg hh hcg hch
      have e : τ * (g * h) * τ⁻¹ * (g * h)⁻¹ =
          (τ * g * τ⁻¹ * g⁻¹) * (g * (τ * h * τ⁻¹ * h⁻¹) * g⁻¹) := by group
      rw [e]
      exact Rb.mul_mem hcg (hRN g hg _ hch)
    have hpow₁ : ∀ i : ℕ, x₁ ^ i ∈ Yb ∧ τ * x₁ ^ i * τ⁻¹ * (x₁ ^ i)⁻¹ ∈ Rb := by
      intro i
      induction i with
      | zero => exact ⟨by simpa using Yb.one_mem, by simpa using Rb.one_mem⟩
      | succ i ih =>
        rw [pow_succ']
        exact ⟨Yb.mul_mem (hPY hx₁P) ih.1, hmul _ _ (hPY hx₁P) ih.1 hcx₁ ih.2⟩
    have hpow₂ : ∀ i : ℕ, x₂ ^ i ∈ Yb ∧ τ * x₂ ^ i * τ⁻¹ * (x₂ ^ i)⁻¹ ∈ Rb := by
      intro i
      induction i with
      | zero => exact ⟨by simpa using Yb.one_mem, by simpa using Rb.one_mem⟩
      | succ i ih =>
        rw [pow_succ']
        exact ⟨Yb.mul_mem (hPY hx₂P) ih.1, hmul _ _ (hPY hx₂P) ih.1 hcx₂ ih.2⟩
    obtain ⟨r, hr, p, hp, rfl⟩ := hYRP y hy
    obtain ⟨i, j, rfl⟩ := hsplit p hp
    have hcr : τ * r * τ⁻¹ * r⁻¹ ∈ Rb := Rb.mul_mem ((hτR r).mp hr) (Rb.inv_mem hr)
    have h12 := hmul _ _ (hpow₁ i).1 (hpow₂ j).1 (hpow₁ i).2 (hpow₂ j).2
    exact hmul _ _ (hRY hr) (Yb.mul_mem (hpow₁ i).1 (hpow₂ j).1) hcr h12
  ·
    left
    have hdvd := (hA2 (Rb ⊓ A) inf_le_right hW2).1
    have hle : Nat.card ↥(Rb ⊓ A) ≤ 2 := by
      have h1 : Nat.card ↥(Rb ⊓ A) ∈ Nat.divisors 4 := Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
      have h2 : Nat.divisors 4 = {1, 2, 4} := by decide
      rw [h2] at h1
      simp only [Finset.mem_insert, Finset.mem_singleton] at h1
      omega
    have hle' : Nat.card ↥(Rb ⊓ A') ≤ 2 := by rw [hsymm]; exact hle
    have hx₁c := yo2_comm_of_small hc hRA hx₁A hx₁3 (hRN x₁ (hPY hx₁P)) hle
    have hx₂c := yo2_comm_of_small hc' hRA' hx₂A hx₂3 (hRN x₂ (hPY hx₂P)) hle'
    intro r hr y hy
    obtain ⟨r', hr', p, hp, rfl⟩ := hYRP y hy
    obtain ⟨i, j, rfl⟩ := hsplit p hp
    have h1 : Commute x₁ r := hx₁c r hr
    have h2 : Commute x₂ r := hx₂c r hr
    have h3 : Commute (x₁ ^ i * x₂ ^ j) r := (h1.pow_left i).mul_left (h2.pow_left j)
    calc r * (r' * (x₁ ^ i * x₂ ^ j)) = (r * r') * (x₁ ^ i * x₂ ^ j) := by group
      _ = (r' * r) * (x₁ ^ i * x₂ ^ j) := by rw [hRab r hr r' hr']
      _ = r' * (r * (x₁ ^ i * x₂ ^ j)) := by group
      _ = r' * ((x₁ ^ i * x₂ ^ j) * r) := by rw [h3.symm.eq]
      _ = r' * (x₁ ^ i * x₂ ^ j) * r := by group



end CFSG.Quasithin.H13.NF314pt
