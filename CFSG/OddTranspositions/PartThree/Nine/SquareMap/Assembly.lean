module

public import CFSG.OddTranspositions.PartThree.Nine.SquareMap.Union
public import Mathlib.GroupTheory.SpecificGroups.Cyclic.Basic
public import Mathlib.Tactic.Group

public section

namespace CFSG.OddTranspositions.PartThree.Nine

theorem isMulCommutative_of_two_elementary_and_cyclic_image {G : Type*} [Group G] [Finite G]
    {S V U R A B X : Subgroup G} {u : G} {q : ℕ} {Y : Type*} [Group Y] [Finite Y]
    (hq : 1 < q) (hVS : V ≤ S) (hUV : U ≤ V) (huS : u ∈ S) (hu2 : u * u = 1)
    (hUc : S ≤ Subgroup.centralizer (U : Set G)) (hSq : ∀ s ∈ S, s * s ∈ U)
    (hR : R = V ⊓ Subgroup.centralizer ({u} : Set G))
    (hUcard : Nat.card U = q) (hRcard : Nat.card R = q ^ 2)
    (hRI : ∀ r ∈ R, r * r = 1 → r ∈ U)
    (hAB : A ⊔ B = V) (hAiB : A ⊓ B = U)
    (hA2 : ∀ a ∈ A, a * a = 1) (hB2 : ∀ b ∈ B, b * b = 1)
    (hAcard : Nat.card A = q ^ 2) (hBcard : Nat.card B = q ^ 2)
    (hI : ∀ v ∈ V, v * v = 1 → v ∈ A ∨ v ∈ B)
    (hXV : X ≤ Subgroup.normalizer (V : Set G)) (hXU : X ≤ Subgroup.normalizer (U : Set G))
    (hXu : X ≤ Subgroup.centralizer ({u} : Set G))
    (ρ : X →* Y) (hρ : Function.Surjective ρ) (hYcyc : IsCyclic Y)
    (hYodd : Odd (Nat.card Y))
    (hker : ∀ x : X, ρ x = 1 → (x : G) ∈ Subgroup.centralizer (U : Set G) ∧
      ∀ v ∈ V, v⁻¹ * ((x : G) * v * (x : G)⁻¹) ∈ U)
    (htrans : ∀ z ∈ U, ∀ z' ∈ U, z ≠ 1 → z' ≠ 1 → ∃ x ∈ X, x * z * x⁻¹ = z') :
    IsMulCommutative R := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hYc : ∀ a b : Y, a * b = b * a := fun a b => (IsCyclic.commGroup (α := Y)).mul_comm a b
  have hUA : U ≤ A := hAiB ▸ inf_le_left
  have hUB : U ≤ B := hAiB ▸ inf_le_right
  have hAV : A ≤ V := hAB ▸ le_sup_left
  have hBV : B ≤ V := hAB ▸ le_sup_right
  have hsqA : ∀ a ∈ A, a * a = 1 := hA2
  have hsqB : ∀ b ∈ B, b * b = 1 := hB2
  have hcen : ∀ z ∈ U, ∀ s ∈ S, z * s = s * z := fun z hz s hs =>
    (Subgroup.mem_centralizer_iff.mp (hUc hs) z hz)
  have hcommS : ∀ s ∈ S, ∀ t ∈ S, s * t * s⁻¹ * t⁻¹ ∈ U := by
    intro s hs t ht
    have h1 := hSq _ (S.mul_mem hs ht)
    have h2 := U.inv_mem (hSq s hs)
    have h3 := U.inv_mem (hSq t ht)
    have hc : t⁻¹ * (s * s)⁻¹ = (s * s)⁻¹ * t⁻¹ := (hcen _ h2 _ (S.inv_mem ht)).symm
    have e : s * t * s⁻¹ * t⁻¹ = (s * t * (s * t)) * ((t⁻¹ * (s * s)⁻¹) * t⁻¹) := by group
    rw [e, hc, show (s * s)⁻¹ * t⁻¹ * t⁻¹ = (s * s)⁻¹ * (t * t)⁻¹ by group]
    exact U.mul_mem h1 (U.mul_mem h2 h3)
  set dd : G → G := fun v => u * v * u⁻¹ * v⁻¹ with hdd
  have ddU : ∀ v ∈ V, dd v ∈ U := fun v hv => hcommS u huS v (hVS hv)
  have ddmul : ∀ v ∈ V, ∀ w ∈ V, dd (v * w) = dd v * dd w := by
    intro v hv w hw
    have hc : dd w * v⁻¹ = v⁻¹ * dd w := hcen _ (ddU w hw) _ (S.inv_mem (hVS hv))
    simp only [hdd] at hc ⊢
    calc u * (v * w) * u⁻¹ * (v * w)⁻¹ = u * v * u⁻¹ * ((u * w * u⁻¹ * w⁻¹) * v⁻¹) := by group
      _ = u * v * u⁻¹ * (v⁻¹ * (u * w * u⁻¹ * w⁻¹)) := by rw [hc]
      _ = _ := by group
  have ddone : ∀ z ∈ U, dd z = 1 := by
    intro z hz
    have := hcen z hz u huS
    simp only [hdd]
    rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul, this]
  have ddX : ∀ x ∈ X, ∀ v, dd (x * v * x⁻¹) = x * dd v * x⁻¹ := by
    intro x hx v
    have hxu : x * u = u * x := (Subgroup.mem_centralizer_iff.mp (hXu hx) u rfl).symm
    have hxu' : u = x * u * x⁻¹ := by rw [hxu]; group
    simp only [hdd]
    conv_lhs => rw [hxu']
    group
  have hAnB : ∀ a ∈ A, ∀ b ∈ B, a * b * a⁻¹ ∈ B := by
    intro a ha b hb
    have := hUB (hcommS a (hVS (hAV ha)) b (hVS (hBV hb)))
    have e : a * b * a⁻¹ = (a * b * a⁻¹ * b⁻¹) * b := by group
    rw [e]; exact B.mul_mem this hb
  let T : Subgroup G :=
    { carrier := {v | ∃ a ∈ A, ∃ b ∈ B, v = a * b}
      one_mem' := ⟨1, A.one_mem, 1, B.one_mem, by simp⟩
      mul_mem' := by
        rintro _ _ ⟨a, ha, b, hb, rfl⟩ ⟨a', ha', b', hb', rfl⟩
        refine ⟨a * a', A.mul_mem ha ha', a'⁻¹ * b * a' * b', B.mul_mem ?_ hb', by group⟩
        simpa using hAnB _ (A.inv_mem ha') b hb
      inv_mem' := by
        rintro _ ⟨a, ha, b, hb, rfl⟩
        exact ⟨a⁻¹, A.inv_mem ha, a * b⁻¹ * a⁻¹, hAnB a ha _ (B.inv_mem hb), by group⟩ }
  have hdec : ∀ v ∈ V, ∃ a ∈ A, ∃ b ∈ B, v = a * b := by
    intro v hv
    have hle : A ⊔ B ≤ T := sup_le (fun a ha => ⟨a, ha, 1, B.one_mem, by simp⟩)
      (fun b hb => ⟨1, A.one_mem, b, hb, by simp⟩)
    exact hle (hAB ▸ hv)
  have hAU : ¬ A ≤ U := by
    intro h
    have := Subgroup.card_le_of_le h
    rw [hAcard, hUcard] at this
    nlinarith
  have hBU : ¬ B ≤ U := by
    intro h
    have := Subgroup.card_le_of_le h
    rw [hBcard, hUcard] at this
    nlinarith
  have hmapAB : ∀ x ∈ X, A.map (MulAut.conj x).toMonoidHom = A ∨
      A.map (MulAut.conj x).toMonoidHom = B := fun x hx =>
    map_conj_eq_or_eq_of_involutions_union hAV hA2 (hAcard.trans hBcard.symm) hI (hXV hx)
  have hmapBA : ∀ x ∈ X, B.map (MulAut.conj x).toMonoidHom = B ∨
      B.map (MulAut.conj x).toMonoidHom = A := fun x hx =>
    map_conj_eq_or_eq_of_involutions_union hBV hB2 (hBcard.trans hAcard.symm)
      (fun v hv h1 => (hI v hv h1).symm) (hXV hx)
  have hmemmap : ∀ {C D : Subgroup G} {x : G}, C.map (MulAut.conj x).toMonoidHom = D →
      ∀ c ∈ C, x * c * x⁻¹ ∈ D := by
    intro C D x h c hc
    rw [← h]; exact ⟨c, hc, by simp [MulAut.conj_apply]⟩
  have hkerA : ∀ x : X, ρ x = 1 → ∀ v ∈ A, (x : G) * v * (x : G)⁻¹ ∈ A := by
    intro x hx v hv
    have := (hker x hx).2 v (hAV hv)
    have e : (x : G) * v * (x : G)⁻¹ = v * (v⁻¹ * ((x : G) * v * (x : G)⁻¹)) := by group
    rw [e]; exact A.mul_mem hv (hUA this)
  have hXA : ∀ x ∈ X, ∀ v ∈ A, x * v * x⁻¹ ∈ A := by
    intro x hx
    rcases hmapAB x hx with h | h
    · exact hmemmap h
    exfalso
    have hBA : B.map (MulAut.conj x).toMonoidHom = A := by
      rcases hmapBA x hx with h' | h'
      · exfalso
        have : A = B := Subgroup.map_injective (MulAut.conj x).injective (h.trans h'.symm)
        apply hAU; rw [← hAiB, this, inf_idem]
      · exact h'
    have hpow : ∀ k : ℕ, ∀ v ∈ A, x ^ (2 * k + 1) * v * (x ^ (2 * k + 1))⁻¹ ∈ B := by
      intro k
      induction k with
      | zero => simpa using hmemmap h
      | succ k ih =>
        intro v hv
        have e : x ^ (2 * (k + 1) + 1) * v * (x ^ (2 * (k + 1) + 1))⁻¹ =
            x * (x * (x ^ (2 * k + 1) * v * (x ^ (2 * k + 1))⁻¹) * x⁻¹) * x⁻¹ := by
          rw [show 2 * (k + 1) + 1 = (2 * k + 1) + 1 + 1 by ring, pow_succ, pow_succ]; group
        rw [e]
        exact hmemmap h _ (hmemmap hBA _ (ih v hv))
    set y := ρ ⟨x, hx⟩
    have hodd : Odd (orderOf y) := Odd.of_dvd_nat hYodd (orderOf_dvd_natCard y)
    obtain ⟨k, hk⟩ := hodd
    have hy : ρ (⟨x, hx⟩ ^ (2 * k + 1)) = 1 := by rw [map_pow, ← hk, pow_orderOf_eq_one]
    apply hAU
    intro v hv
    have h1 : x ^ (2 * k + 1) * v * (x ^ (2 * k + 1))⁻¹ ∈ A := by
      simpa using hkerA _ hy v hv
    have h2 := hpow k v hv
    have h3 : x ^ (2 * k + 1) * v * (x ^ (2 * k + 1))⁻¹ ∈ U := hAiB ▸ ⟨h1, h2⟩
    have hcz := (hker _ hy).1
    have hc : (x ^ (2 * k + 1))⁻¹ ∈ Subgroup.centralizer (U : Set G) := by
      have := Subgroup.inv_mem _ hcz; simpa using this
    have := Subgroup.mem_centralizer_iff.mp hc _ h3
    have e : v = (x ^ (2 * k + 1))⁻¹ * (x ^ (2 * k + 1) * v * (x ^ (2 * k + 1))⁻¹) *
        x ^ (2 * k + 1) := by group
    rw [e, ← this]
    simpa using h3
  have hXB : ∀ x ∈ X, ∀ v ∈ B, x * v * x⁻¹ ∈ B := by
    intro x hx
    rcases hmapBA x hx with h | h
    · exact hmemmap h
    exfalso
    rcases hmapAB x hx with h' | h'
    · have : B = A := Subgroup.map_injective (MulAut.conj x).injective (h.trans h'.symm)
      apply hAU; rw [← hAiB, this, inf_idem]
    · have hv : ∀ v ∈ A, x * v * x⁻¹ ∈ A := hXA x hx
      have : A.map (MulAut.conj x).toMonoidHom ≤ A := by
        rintro _ ⟨v, hv', rfl⟩; simpa [MulAut.conj_apply] using hv v hv'
      have hBA : B ≤ A := h' ▸ this
      apply hBU; rw [← hAiB]; exact le_inf hBA le_rfl
  have hRV : R ≤ V := hR ▸ inf_le_left
  have hXuc : ∀ x ∈ X, x * u * x⁻¹ = u := by
    intro x hx
    have : u * x = x * u := Subgroup.mem_centralizer_iff.mp (hXu hx) u rfl
    rw [← this]; group
  have hRu : ∀ r ∈ R, u * r = r * u := by
    intro r hr
    rw [hR] at hr
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hr).2 u rfl
  have hXR : ∀ x ∈ X, ∀ r ∈ R, x * r * x⁻¹ ∈ R := by
    intro x hx r hr
    have hur := hRu r hr
    have hrV := hRV hr
    rw [hR]
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hXV hx) r).mp hrV, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun h hh => ?_
    rw [Set.mem_singleton_iff] at hh
    rw [hh]
    conv_lhs => rw [← hXuc x hx]
    conv_rhs => rw [← hXuc x hx]
    calc x * u * x⁻¹ * (x * r * x⁻¹) = x * (u * r) * x⁻¹ := by group
      _ = x * (r * u) * x⁻¹ := by rw [hur]
      _ = _ := by group
  have hpa : ∀ v, ∃ a : G, v ∈ V → a ∈ A ∧ a⁻¹ * v ∈ B := by
    intro v
    by_cases hv : v ∈ V
    · obtain ⟨a, ha, b, hb, rfl⟩ := hdec v hv
      exact ⟨a, fun _ => ⟨ha, by simpa using hb⟩⟩
    · exact ⟨1, fun h => absurd h hv⟩
  choose pa hpa using hpa
  set F : G → G := fun v => dd (pa v) with hF
  have Fspec : ∀ a ∈ A, ∀ b ∈ B, F (a * b) = dd a := by
    intro a ha b hb
    obtain ⟨ha', hb'⟩ := hpa _ (V.mul_mem (hAV ha) (hBV hb))
    have h1 : a⁻¹ * pa (a * b) ∈ A := A.mul_mem (A.inv_mem ha) ha'
    have h2 : a⁻¹ * pa (a * b) ∈ B := by
      have e : a⁻¹ * pa (a * b) = b * ((pa (a * b))⁻¹ * (a * b))⁻¹ := by group
      rw [e]; exact B.mul_mem hb (B.inv_mem hb')
    have h3 : a⁻¹ * pa (a * b) ∈ U := hAiB ▸ Subgroup.mem_inf.mpr ⟨h1, h2⟩
    show dd (pa (a * b)) = dd a
    calc dd (pa (a * b)) = dd (a * (a⁻¹ * pa (a * b))) := by rw [mul_inv_cancel_left]
      _ = dd a * dd (a⁻¹ * pa (a * b)) := ddmul _ (hAV ha) _ (hAV h1)
      _ = dd a := by rw [ddone _ h3, mul_one]
  have FU' : ∀ r ∈ V, F r ∈ U := by
    intro r hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec r hr
    rw [Fspec a ha b hb]; exact ddU a (hAV ha)
  have Fmul : ∀ r ∈ V, ∀ t ∈ V, F (r * t) = F r * F t := by
    intro r hr t ht
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec r hr
    obtain ⟨a', ha', b', hb', rfl⟩ := hdec t ht
    have hb'' : a'⁻¹ * b * a' * b' ∈ B :=
      B.mul_mem (by simpa using hAnB _ (A.inv_mem ha') b hb) hb'
    rw [show a * b * (a' * b') = (a * a') * (a'⁻¹ * b * a' * b') by group,
      Fspec _ (A.mul_mem ha ha') _ hb'', Fspec a ha b hb, Fspec a' ha' b' hb',
      ddmul _ (hAV ha) _ (hAV ha')]
  have Fker : ∀ r ∈ R, F r = 1 → r ∈ U := by
    intro r hr h
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec r (hRV hr)
    rw [Fspec a ha b hb] at h
    simp only [hdd] at h
    have hua : u * a = a * u := by
      rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h; exact h
    have haR : a ∈ R := by
      rw [hR]
      refine Subgroup.mem_inf.mpr ⟨hAV ha, Subgroup.mem_centralizer_iff.mpr fun h hh => ?_⟩
      rw [Set.mem_singleton_iff] at hh; rw [hh]; exact hua
    have haU : a ∈ U := hRI a haR (hsqA a ha)
    have hbR : b ∈ R := by
      have := R.mul_mem (R.inv_mem haR) hr
      simpa using this
    exact U.mul_mem haU (hRI b hbR (hsqB b hb))
  have FX : ∀ x ∈ X, ∀ r ∈ V, F (x * r * x⁻¹) = x * F r * x⁻¹ := by
    intro x hx r hr
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec r hr
    rw [show x * (a * b) * x⁻¹ = (x * a * x⁻¹) * (x * b * x⁻¹) by group,
      Fspec _ (hXA x hx a ha) _ (hXB x hx b hb), Fspec a ha b hb, ddX x hx]
  have σU : ∀ r ∈ R, ∀ z ∈ U, (r * z) * (r * z) = r * r := by
    intro r hr z hz
    have hzr : z * r = r * z := hcen z hz r (hVS (hRV hr))
    calc (r * z) * (r * z) = r * (z * r) * z := by group
      _ = r * r * (z * z) := by rw [hzr]; group
      _ = r * r := by rw [hsqA z (hUA hz), mul_one]
  have hXcomm : ∀ a ∈ X, ∀ b ∈ X, ∀ z ∈ U,
      (a * b) * z * (a * b)⁻¹ = (b * a) * z * (b * a)⁻¹ := by
    intro a ha b hb z hz
    have hkX : (b * a)⁻¹ * (a * b) ∈ X := X.mul_mem (X.inv_mem (X.mul_mem hb ha)) (X.mul_mem ha hb)
    have hk : ρ ⟨(b * a)⁻¹ * (a * b), hkX⟩ = 1 := by
      have e : (⟨(b * a)⁻¹ * (a * b), hkX⟩ : X) =
          (⟨b, hb⟩ * ⟨a, ha⟩)⁻¹ * (⟨a, ha⟩ * ⟨b, hb⟩) := Subtype.ext rfl
      rw [e, map_mul, map_inv, map_mul, map_mul, hYc (ρ ⟨a, ha⟩) (ρ ⟨b, hb⟩), inv_mul_cancel]
    have hkz : z * ((b * a)⁻¹ * (a * b)) = ((b * a)⁻¹ * (a * b)) * z :=
      Subgroup.mem_centralizer_iff.mp (hker _ hk).1 z hz
    calc (a * b) * z * (a * b)⁻¹
        = (b * a) * (((b * a)⁻¹ * (a * b)) * z) * ((b * a)⁻¹ * (a * b))⁻¹ * (b * a)⁻¹ := by
          group
      _ = (b * a) * (z * ((b * a)⁻¹ * (a * b))) * ((b * a)⁻¹ * (a * b))⁻¹ * (b * a)⁻¹ := by
          rw [hkz]
      _ = _ := by group
  have hsqhom : ∀ r ∈ R, ∀ t ∈ R, (r * t) * (r * t) = (r * r) * (t * t) := by
    by_cases h0 : ∀ r ∈ R, r * r = 1
    · intro r hr t ht; rw [h0 _ (R.mul_mem hr ht), h0 r hr, h0 t ht, one_mul]
    push Not at h0
    obtain ⟨r₀, hr₀, hr₀1⟩ := h0
    have hr₀U : r₀ ∉ U := fun h => hr₀1 (hsqA _ (hUA h))
    have hFr₀ : F r₀ ≠ 1 := fun h => hr₀U (Fker r₀ hr₀ h)
    obtain ⟨c, hc, hcr₀⟩ :=
      htrans _ (FU' r₀ (hRV hr₀)) _ (hSq r₀ (hVS (hRV hr₀))) hFr₀ hr₀1
    have hclaim : ∀ r ∈ R, r * r = c * F r * c⁻¹ := by
      intro r hr
      by_cases hrU : r ∈ U
      · have h1 : F r = 1 := by
          have := Fspec r (hUA hrU) 1 B.one_mem
          rw [mul_one] at this; rw [this, ddone r hrU]
        rw [hsqA r (hUA hrU), h1]; group
      have hFr : F r ≠ 1 := fun h => hrU (Fker r hr h)
      obtain ⟨a, ha, har⟩ := htrans _ (FU' r₀ (hRV hr₀)) _ (FU' r (hRV hr)) hFr₀ hFr
      have hr' : a * r₀ * a⁻¹ ∈ R := hXR a ha r₀ hr₀
      have hFa : F (a * r₀ * a⁻¹) = F r := by rw [FX a ha r₀ (hRV hr₀), har]
      have hz : (a * r₀ * a⁻¹)⁻¹ * r ∈ U := by
        apply Fker _ (R.mul_mem (R.inv_mem hr') hr)
        have := Fmul _ (hRV hr') _ (hRV (R.mul_mem (R.inv_mem hr') hr))
        rw [mul_inv_cancel_left, hFa] at this
        exact (mul_eq_left.mp this.symm)
      have hsq : r * r = (a * r₀ * a⁻¹) * (a * r₀ * a⁻¹) := by
        have e : r = (a * r₀ * a⁻¹) * ((a * r₀ * a⁻¹)⁻¹ * r) := by group
        rw [e]; exact σU _ hr' _ hz
      rw [hsq, show (a * r₀ * a⁻¹) * (a * r₀ * a⁻¹) = a * (r₀ * r₀) * a⁻¹ by group, ← hcr₀,
        ← har]
      calc a * (c * F r₀ * c⁻¹) * a⁻¹ = (a * c) * F r₀ * (a * c)⁻¹ := by group
        _ = (c * a) * F r₀ * (c * a)⁻¹ := hXcomm a ha c hc _ (FU' r₀ (hRV hr₀))
        _ = _ := by group
    intro r hr t ht
    rw [hclaim _ (R.mul_mem hr ht), hclaim r hr, hclaim t ht, Fmul r (hRV hr) t (hRV ht)]
    group
  refine ⟨⟨fun r t => Subtype.ext ?_⟩⟩
  have h := hsqhom r r.2 t t.2
  have h' : (r : G) * (t * (r * t)) = r * (r * (t * t)) := by simpa only [mul_assoc] using h
  have h2 : (t : G) * r * t = r * t * t := by
    have := mul_left_cancel h'
    simpa only [mul_assoc] using this
  exact (mul_right_cancel h2).symm

end CFSG.OddTranspositions.PartThree.Nine
