module

public import CFSG.Walter.Bender1970.S38.SmallQ

public section

namespace CFSG.Walter

variable {A Y : Type*} [CommGroup A] [Group Y]

@[expose] noncomputable def restrictOf (ρ : Y →* MulAut A) (Q : Subgroup A) (S : Subgroup Y)
    (hSQ : ∀ s ∈ S, ∀ v ∈ Q, ρ s v ∈ Q) : S →* MulAut Q where
  toFun x :=
    { toFun := fun v => ⟨ρ x v, hSQ x x.2 v v.2⟩
      invFun := fun v => ⟨ρ (x⁻¹ : S) v, hSQ _ (x⁻¹).2 v v.2⟩
      left_inv := fun v => Subtype.ext (by
        simp only [Subgroup.coe_inv, map_inv, MulAut.inv_apply_self])
      right_inv := fun v => Subtype.ext (by
        simp only [Subgroup.coe_inv, map_inv, MulAut.apply_inv_self])
      map_mul' := fun v w => Subtype.ext (map_mul _ _ _) }
  map_one' := by
    ext v
    simp
  map_mul' x y := by
    ext v
    simp [MulAut.mul_apply]

theorem restrictOf_apply {ρ : Y →* MulAut A} {Q : Subgroup A} {S : Subgroup Y}
    {hSQ : ∀ s ∈ S, ∀ v ∈ Q, ρ s v ∈ Q} (x : S) (v : Q) :
    ((restrictOf ρ Q S hSQ x v : Q) : A) = ρ x v := rfl

theorem exists_regular_subgroup [Finite A] [Finite Y] {ρ : Y →* MulAut A}
    (hρ : Function.Injective ρ) (hYodd : Odd (Nat.card Y)) {W Q : Subgroup A}
    (hsq : ∀ a : A, a ^ 2 = 1) (hWQt : W ⊔ Q = ⊤) (hQ4 : 4 ≤ Nat.card Q)
    {X N : Subgroup Y} (hXQ : ∀ x ∈ X, ∀ v ∈ Q, ρ x v ∈ Q) (hNX : N ≤ X)
    (hXN : ∀ x ∈ X, ∀ n ∈ N, x * n * x⁻¹ ∈ N) (hNW : ∀ n ∈ N, ∀ w ∈ W, ρ n w = w)
    (htrans : ∀ u ∈ Q, u ≠ 1 → ∀ v ∈ Q, v ≠ 1 → ∃ n ∈ N, ρ n u = v)
    (hcase : Nat.card Q ≤ 8 ∨ ∃ d ∈ N, (∀ n ∈ N, ∃ m : ℕ, ∀ v ∈ Q, ρ n v = ρ (d ^ m) v) ∧
      (∀ n ∈ N, ∀ u ∈ Q, u ≠ 1 → ρ n u = u → ∀ v ∈ Q, ρ n v = v)) :
    ∃ R : Subgroup Y, R ≤ X ∧ (∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R) ∧ IsCyclic R ∧
      (∀ r ∈ R, ∀ w ∈ W, ρ r w = w) ∧ (∀ r ∈ R, ∀ v ∈ Q, ρ r v = v → v ≠ 1 → r = 1) ∧
      (∀ u ∈ Q, u ≠ 1 → ∀ v ∈ Q, v ≠ 1 → ∃ r ∈ R, ρ r u = v) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdecomp : ∀ a : A, ∃ w ∈ W, ∃ v ∈ Q, w * v = a := fun a =>
    Subgroup.mem_sup.mp (hWQt ▸ Subgroup.mem_top a)
  have hfaith : ∀ n ∈ N, (∀ v ∈ Q, ρ n v = v) → n = 1 := by
    intro n hn hnQ
    apply hρ
    rw [map_one]
    ext a
    obtain ⟨w, hw, v, hv, rfl⟩ := hdecomp a
    rw [map_mul, hNW n hn w hw, hnQ v hv, MulAut.one_apply]
  rcases hcase with h8 | ⟨d, hdN, hcyc, hfree⟩
  ·
    have hQ48 : Nat.card Q = 4 ∨ Nat.card Q = 8 := by
      have hQp : IsPGroup 2 Q := fun a => ⟨1, Subtype.ext (by
        rw [pow_one, Subgroup.coe_pow, hsq, Subgroup.coe_one])⟩
      obtain ⟨b, hb⟩ := hQp.exists_card_eq
      rw [hb] at h8 hQ4 ⊢
      have h1 : 2 ≤ b := by
        by_contra h
        have : 2 ^ b ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      have h2 : b ≤ 3 := by
        by_contra h
        have : 2 ^ 4 ≤ 2 ^ b := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      interval_cases b <;> simp
    set σ := restrictOf ρ Q X hXQ with hσ
    set N' : Subgroup (MulAut Q) := (N.subgroupOf X).map σ with hN'
    have hN'odd : Odd (Nat.card N') := by
      have h1 : Nat.card N' ∣ Nat.card (N.subgroupOf X) := by
        rw [hN']
        exact Subgroup.card_map_dvd _ _
      have h2 : Nat.card (N.subgroupOf X) ∣ Nat.card Y :=
        (Subgroup.card_subgroup_dvd_card _).trans (Subgroup.card_subgroup_dvd_card X)
      exact Odd.of_dvd_nat hYodd (h1.trans h2)
    have hN'trans : ∀ u v : Q, u ≠ 1 → v ≠ 1 → ∃ n ∈ N', n u = v := by
      intro u v hu hv
      obtain ⟨n, hn, hnuv⟩ := htrans u u.2 (fun h => hu (Subtype.ext h)) v v.2
        (fun h => hv (Subtype.ext h))
      exact ⟨σ ⟨n, hNX hn⟩, ⟨⟨n, hNX hn⟩, hn, rfl⟩, Subtype.ext hnuv⟩
    have hQsq : ∀ v : Q, v ^ 2 = 1 := fun v => Subtype.ext (by
      rw [Subgroup.coe_pow, hsq, Subgroup.coe_one])
    obtain ⟨R₀, hR₀N', hR₀cyc, -, hR₀free, hR₀trans, hR₀norm⟩ :=
      exists_regular_of_card_eq hQsq hQ48 hN'odd hN'trans
    set R : Subgroup Y := ((R₀.comap σ) ⊓ N.subgroupOf X).map X.subtype with hR
    have hRX : R ≤ X := Subgroup.map_subtype_le _
    have hmemR : ∀ x : X, (x : Y) ∈ R ↔ σ x ∈ R₀ ∧ (x : Y) ∈ N := by
      intro x
      constructor
      · rintro ⟨y, ⟨hy1, hy2⟩, hyx⟩
        rw [← Subtype.ext hyx]
        exact ⟨hy1, hy2⟩
      · rintro ⟨h1, h2⟩
        exact ⟨x, ⟨h1, h2⟩, rfl⟩
    have hσinj : ∀ x ∈ N.subgroupOf X, σ x = 1 → x = 1 := by
      intro x hx h1
      have h2 : (x : Y) = 1 := hfaith x hx fun v hv => by
        have := congrArg (fun φ : MulAut Q => ((φ ⟨v, hv⟩ : Q) : A)) h1
        exact this
      exact Subtype.ext h2
    refine ⟨R, hRX, fun x hx r hr => ?_, ?_, fun r hr w hw => ?_, fun r hr v hv hrv hv1 => ?_,
      fun u hu hu1 v hv hv1 => ?_⟩
    ·
      obtain ⟨r', ⟨hr'R₀, hr'N⟩, rfl⟩ := hr
      have hxr : x * (r' : Y) * x⁻¹ ∈ N := hXN x hx r' hr'N
      have := (hmemR (⟨x, hx⟩ * r' * ⟨x, hx⟩⁻¹)).mpr ⟨?_, hxr⟩
      · exact this
      · rw [map_mul, map_mul, map_inv]
        refine hR₀norm (σ ⟨x, hx⟩) (fun n hn => ?_) _ hr'R₀
        obtain ⟨m, hm, rfl⟩ := hn
        rw [← map_inv, ← map_mul, ← map_mul]
        exact ⟨_, hXN x hx m hm, rfl⟩
    ·
      have : IsCyclic R₀ := hR₀cyc
      let f : R →* R₀ :=
        { toFun := fun r => ⟨σ ⟨r, hRX r.2⟩, ((hmemR ⟨r, hRX r.2⟩).mp r.2).1⟩
          map_one' := by
            apply Subtype.ext
            simp only [OneMemClass.coe_one]
            convert map_one σ
          map_mul' := fun a b => by
            apply Subtype.ext
            simp only [Subgroup.coe_mul]
            convert map_mul σ ⟨a, hRX a.2⟩ ⟨b, hRX b.2⟩ }
      have hf : Function.Injective f := by
        intro a b hab
        have h1 : σ (⟨a, hRX a.2⟩ * (⟨b, hRX b.2⟩ : X)⁻¹) = 1 := by
          rw [map_mul, map_inv, mul_inv_eq_one]
          exact congrArg Subtype.val hab
        have h2 := hσinj _ (N.mul_mem ((hmemR ⟨a, hRX a.2⟩).mp a.2).2
          (N.inv_mem ((hmemR ⟨b, hRX b.2⟩).mp b.2).2)) h1
        rw [mul_inv_eq_one] at h2
        exact Subtype.ext (congrArg (fun z : X => (z : Y)) h2)
      exact isCyclic_of_injective f hf
    · exact hNW r ((hmemR ⟨r, hRX hr⟩).mp hr).2 w hw
    · have h1 := hR₀free _ ((hmemR ⟨r, hRX hr⟩).mp hr).1 ⟨v, hv⟩ (Subtype.ext hrv)
        (fun h => hv1 (congrArg Subtype.val h))
      have h2 := hσinj ⟨r, hRX hr⟩ ((hmemR ⟨r, hRX hr⟩).mp hr).2 h1
      exact congrArg Subtype.val h2
    · obtain ⟨r₀, hr₀, hr₀uv⟩ := hR₀trans ⟨u, hu⟩ ⟨v, hv⟩ (fun h => hu1 (congrArg Subtype.val h))
        (fun h => hv1 (congrArg Subtype.val h))
      obtain ⟨x, hxN, rfl⟩ := hR₀N' hr₀
      exact ⟨x, (hmemR x).mpr ⟨hr₀, hxN⟩, congrArg Subtype.val hr₀uv⟩
  ·
    refine ⟨N, hNX, hXN, ?_, hNW, fun n hn v hv hnv hv1 => ?_, htrans⟩
    ·
      have hle : N ≤ Subgroup.zpowers d := by
        intro n hn
        obtain ⟨m, hm⟩ := hcyc n hn
        have : n = d ^ m := by
          apply hρ
          ext a
          obtain ⟨w, hw, v, hv, rfl⟩ := hdecomp a
          rw [map_mul, map_mul, hNW n hn w hw, hNW _ (N.pow_mem hdN m) w hw, hm v hv]
        rw [this]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers d) m
      have heq : N = Subgroup.zpowers d :=
        le_antisymm hle ((Subgroup.zpowers_le).mpr hdN)
      rw [heq]
      infer_instance
    · exact hfaith n hn (hfree n hn v hv hv1 hnv)

end CFSG.Walter
