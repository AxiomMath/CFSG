module

public import CFSG.Quasithin.SteinbergBSConjugateOrbits

public section

namespace CFSG.Quasithin.SteinbergBS

open Subgroup

variable {G : Type*} [Group G]

theorem card_le_two_of_isCyclic {B : Subgroup G} (hc : IsCyclic B) (hB : ∀ x ∈ B, x ^ 2 = 1) :
    Nat.card B ≤ 2 := by
  have h : Monoid.exponent B ∣ 2 := Monoid.exponent_dvd_of_forall_pow_eq_one fun x =>
    Subtype.ext (by simpa using hB x x.2)
  rw [IsCyclic.exponent_eq_card] at h
  exact Nat.le_of_dvd two_pos h

theorem eq_of_card_le_two [Finite G] {B : Subgroup G} (hB : Nat.card B ≤ 2) {x y : G}
    (hx : x ∈ B) (hy : y ∈ B) (hx1 : x ≠ 1) (hy1 : y ≠ 1) : x = y := by
  by_contra hxy
  have h3 : ({1, x, y} : Set G).ncard = 3 := by
    rw [Set.ncard_insert_of_notMem (by simp [hx1.symm, hy1.symm]), Set.ncard_pair hxy]
  have hle : ({1, x, y} : Set G).ncard ≤ (B : Set G).ncard := Set.ncard_le_ncard (by
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rcases hz with rfl | rfl | rfl
    exacts [one_mem B, hx, hy]) (Set.toFinite _)
  have hBc : (B : Set G).ncard = Nat.card B := (Nat.card_coe_set_eq _).symm
  omega

theorem linear_noncentral_hyperplane_faithfulness [Finite G] {V : Subgroup G}
    [IsElementaryAbelian 2 V] {n : ℕ} (hVn : Nat.card V = 2 ^ n) (hn : 4 ≤ n)
    (htrans : ∀ Z₁ : Subgroup G, Z₁ ≤ V → Nat.card Z₁ = 2 → ∀ Z₂ : Subgroup G, Z₂ ≤ V →
      Nat.card Z₂ = 2 → ∃ a ∈ normalizer (V : Set G), conjugate Z₁ a = Z₂)
    (hcent : ∀ B : Subgroup G, B ≤ V → ¬ IsCyclic B →
      centralizer (B : Set G) ≤ normalizer (V : Set G))
    (hhull : ∀ Z : Subgroup G, Z ≤ V → Nat.card Z = 2 →
      ∀ x ∈ ⨆ h ∈ normalizer (Z : Set G), conjugate V h,
        ∀ y ∈ ⨆ h ∈ normalizer (Z : Set G), conjugate V h, x * y = y * x)
    {A D : Subgroup G} (hA : ∃ g : G, A = conjugate V g) (hAV : ¬ A ≤ normalizer (V : Set G))
    (hDA : D ≤ A) (hDi : D.relIndex A = 2) (hDV : D ≤ normalizer (V : Set G))
    (hDV1 : ⁅D, V⁆ ≠ ⊥) (hNVA : V ⊓ normalizer (A : Set G) ≤ normalizer (D : Set G)) :
    D ⊓ centralizer (V : Set G) = ⊥ := by
  classical
  obtain ⟨g, rfl⟩ := hA
  have hVab : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (mul_comm' (⟨x, hx⟩ : V) ⟨y, hy⟩)
  have hV2 : ∀ x ∈ V, x ^ 2 = 1 := fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx
  have hcomm : ∀ {a b : G}, a * b * a⁻¹ * b⁻¹ = 1 → a * b = b * a := fun h =>
    commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h)
  have hAab : ∀ x ∈ conjugate V g, ∀ y ∈ conjugate V g, x * y = y * x := by
    intro x hx y hy
    have h1 := hVab _ (mem_conjugate_iff.1 hx) _ (mem_conjugate_iff.1 hy)
    calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = y * x := by group
  have hA2 : ∀ x ∈ conjugate V g, x ^ 2 = 1 := by
    intro x hx
    have h1 := hV2 _ (mem_conjugate_iff.1 hx)
    rw [conj_pow] at h1
    have h2 : x ^ 2 = g⁻¹ * (g * x ^ 2 * g⁻¹) * g := by group
    rw [h2, h1]
    group
  have hAcard : Nat.card (conjugate V g) = 2 ^ n := by
    rw [conjugate, card_map_of_injective (MulAut.conj g⁻¹).injective, hVn]
  have hD8 : 8 ≤ Nat.card D := by
    have h := relIndex_mul_card D (conjugate V g)
    rw [inf_eq_left.2 hDA, hDi, hAcard] at h
    have h2 : 2 ^ n = 2 * 2 ^ (n - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h3 : 2 ^ 3 ≤ 2 ^ (n - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have hVA : V ⊓ conjugate V g = ⊥ := by
    by_contra hne
    have h := (linear_line_normalizer_conjugate_fusion (p := 2) htrans).2.1 hhull g hne
    apply hDV1
    rw [eq_bot_iff, ← h, commutator_comm V]
    exact commutator_mono hDA le_rfl
  have hND : ∀ v ∈ V, v ∈ normalizer (D : Set G) → ∀ d ∈ D, v * d = d * v := by
    intro v hv hvD d hd
    have h1 : d * v * d⁻¹ * v⁻¹ ∈ V :=
      mul_mem ((mem_normalizer_iff.mp (hDV hd) v).mp hv) (inv_mem hv)
    have h2 : d * v * d⁻¹ * v⁻¹ ∈ D := by
      have := (mem_normalizer_iff.mp hvD d⁻¹).mp (inv_mem hd)
      simpa [mul_assoc] using mul_mem hd this
    have h3 : d * v * d⁻¹ * v⁻¹ ∈ V ⊓ conjugate V g := mem_inf.2 ⟨h1, hDA h2⟩
    rw [hVA, mem_bot] at h3
    exact (hcomm h3).symm
  have hcentA : ∀ B : Subgroup G, B ≤ conjugate V g → ¬ IsCyclic B →
      centralizer (B : Set G) ≤ normalizer (conjugate V g : Set G) := by
    intro B hBA hB x hx
    have hB'V : conjugate B g⁻¹ ≤ V := by
      intro y hy
      rw [mem_conjugate_iff, inv_inv] at hy
      have := mem_conjugate_iff.1 (hBA hy)
      simpa [mul_assoc] using this
    have hB'c : ¬ IsCyclic (conjugate B g⁻¹) := by
      intro hc
      apply hB
      have e := B.equivMapOfInjective (MulAut.conj g⁻¹⁻¹).toMonoidHom (MulAut.conj g⁻¹⁻¹).injective
      exact isCyclic_of_surjective (hH := hc) e.symm e.symm.surjective
    have hxc : g * x * g⁻¹ ∈ centralizer (conjugate B g⁻¹ : Set G) := by
      rw [mem_centralizer_iff]
      intro y hy
      rw [SetLike.mem_coe, mem_conjugate_iff, inv_inv] at hy
      have h1 := (mem_centralizer_iff.1 hx) _ hy
      calc y * (g * x * g⁻¹) = g * ((g⁻¹ * y * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
        _ = g * x * g⁻¹ * y := by group
    have hxN := hcent _ hB'V hB'c hxc
    rw [mem_normalizer_iff]
    intro y
    rw [mem_conjugate_iff, mem_conjugate_iff]
    have h1 := (mem_normalizer_iff.mp hxN) (g * y * g⁻¹)
    rw [show g * (x * y * x⁻¹) * g⁻¹ =
      (g * x * g⁻¹) * (g * y * g⁻¹) * (g * x * g⁻¹)⁻¹ by group]
    exact h1
  have hB : ∀ B : Subgroup G, B ≤ D → ¬ IsCyclic B → ∀ v ∈ V,
      v ∈ centralizer (B : Set G) → ∀ d ∈ D, v * d = d * v := fun B hBD hB v hv hvB =>
    hND v hv (hNVA (mem_inf.2 ⟨hv, hcentA B (hBD.trans hDA) hB hvB⟩))
  set K := D ⊓ centralizer (V : Set G) with hKdef
  have hKV : ∀ k ∈ K, ∀ v ∈ V, v * k = k * v := fun k hk v hv =>
    mem_centralizer_iff.1 (mem_inf.1 hk).2 v hv
  have hDV1' : ∃ d ∈ D, ∃ v ∈ V, v * d ≠ d * v := by
    by_contra h
    push Not at h
    apply hDV1
    rw [commutator_eq_bot_iff_le_centralizer]
    exact fun d hd => mem_centralizer_iff.2 fun v hv => h d hd v hv
  have hKcyc : IsCyclic K := by
    by_contra hc
    obtain ⟨d, hd, v, hv, hvd⟩ := hDV1'
    exact hvd (hB K inf_le_left hc v hv
      (mem_centralizer_iff.2 fun k hk => (hKV k hk v hv).symm) d hd)
  have hK2 : Nat.card K ≤ 2 :=
    card_le_two_of_isCyclic hKcyc fun x hx => hA2 x (hDA (mem_inf.1 hx).1)
  by_contra hK
  obtain ⟨z, hzK, hz1⟩ : ∃ z ∈ K, z ≠ 1 := by
    obtain ⟨⟨z, hz⟩, hz1⟩ := (ne_bot_iff_exists_ne_one).1 hK
    exact ⟨z, hz, fun h => hz1 (Subtype.ext h)⟩
  have hKcard : Nat.card K = 2 := by
    have h1 : Nat.card K ≠ 1 := fun h => hK (card_eq_one.1 h)
    have h0 : 0 < Nat.card K := Nat.card_pos
    omega
  have hJ : ∀ h ∈ normalizer (K : Set G), ∀ x ∈ conjugate V g, ∀ y ∈ conjugate (conjugate V g) h,
      x * y = y * x := by
    intro h hh x hx y hy
    have hZ'V : conjugate K g⁻¹ ≤ V := by
      intro w hw
      rw [mem_conjugate_iff, inv_inv] at hw
      have := mem_conjugate_iff.1 (hDA (mem_inf.1 hw).1)
      simpa [mul_assoc] using this
    have hZ'c : Nat.card (conjugate K g⁻¹) = 2 := by
      rw [conjugate, card_map_of_injective (MulAut.conj _).injective, hKcard]
    have hgh : g * h * g⁻¹ ∈ normalizer (conjugate K g⁻¹ : Set G) := by
      rw [mem_normalizer_iff]
      intro w
      rw [mem_conjugate_iff, mem_conjugate_iff, inv_inv]
      have h1 := (mem_normalizer_iff.mp hh) (g⁻¹ * w * g)
      rw [show g⁻¹ * (g * h * g⁻¹ * w * (g * h * g⁻¹)⁻¹) * g = h * (g⁻¹ * w * g) * h⁻¹ by group]
      exact h1
    have hx' : g * x * g⁻¹ ∈ ⨆ k ∈ normalizer (conjugate K g⁻¹ : Set G), conjugate V k := by
      refine le_iSup₂ (f := fun k (_ : k ∈ normalizer (conjugate K g⁻¹ : Set G)) =>
        conjugate V k) 1 (one_mem _) ?_
      rw [conjugate_one]
      exact mem_conjugate_iff.1 hx
    have hy' : g * y * g⁻¹ ∈ ⨆ k ∈ normalizer (conjugate K g⁻¹ : Set G), conjugate V k := by
      refine le_iSup₂ (f := fun k (_ : k ∈ normalizer (conjugate K g⁻¹ : Set G)) =>
        conjugate V k) _ hgh ?_
      rw [mem_conjugate_iff]
      have h1 := mem_conjugate_iff.1 (mem_conjugate_iff.1 hy)
      rw [show g * h * g⁻¹ * (g * y * g⁻¹) * (g * h * g⁻¹)⁻¹ = g * (h * y * h⁻¹) * g⁻¹ by group]
      exact h1
    have h1 := hhull _ hZ'V hZ'c _ hx' _ hy'
    calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h1]
      _ = y * x := by group
  have hVZ : V ≤ normalizer (K : Set G) := fun v hv =>
    centralizer_le_normalizer _ (mem_centralizer_iff.2 fun k hk => (hKV k hk v hv).symm)
  set R := ⁅V, D⁆ with hRdef
  have hRV : R ≤ V := commutator_le.2 fun v hv d hd => by
    rw [commutatorElement_def]
    have := (mem_normalizer_iff.mp (hDV hd) v⁻¹).mp (inv_mem hv)
    simpa [mul_assoc] using mul_mem hv this
  have hRA : R ≤ centralizer (conjugate V g : Set G) := commutator_le.2 fun v hv d hd => by
    rw [commutatorElement_def, mem_centralizer_iff]
    intro a ha
    have h1 : v * d * v⁻¹ ∈ conjugate (conjugate V g) v⁻¹ := by
      rw [mem_conjugate_iff]
      simpa [mul_assoc] using hDA hd
    have h2 := hJ v⁻¹ (inv_mem (hVZ hv)) a ha _ h1
    have h3 : a * d⁻¹ = d⁻¹ * a := Commute.inv_right (hAab a ha d (hDA hd))
    calc a * (v * d * v⁻¹ * d⁻¹) = (a * (v * d * v⁻¹)) * d⁻¹ := by group
      _ = (v * d * v⁻¹) * (a * d⁻¹) := by rw [h2]; group
      _ = (v * d * v⁻¹) * (d⁻¹ * a) := by rw [h3]
      _ = v * d * v⁻¹ * d⁻¹ * a := by group
  have hRcyc : IsCyclic R := by
    by_contra hc
    exact hAV ((le_centralizer_iff.1 hRA).trans (hcent R hRV hc))
  have hR2 : Nat.card R ≤ 2 := card_le_two_of_isCyclic hRcyc fun x hx => hV2 x (hRV hx)
  have hcR : ∀ d ∈ D, ∀ v ∈ V, d * v * d⁻¹ * v⁻¹ ∈ R := fun d hd v hv => by
    rw [hRdef, commutator_comm]
    have h := commutator_mem_commutator hd hv
    rwa [commutatorElement_def] at h
  obtain ⟨d₀, hd₀D, hd₀K⟩ : ∃ d₀ ∈ D, d₀ ∉ K := by
    by_contra h
    push Not at h
    have := card_le_of_le (show D ≤ K from fun x hx => h x hx)
    omega
  obtain ⟨v₀, hv₀V, hv₀d₀⟩ : ∃ v₀ ∈ V, v₀ * d₀ ≠ d₀ * v₀ := by
    by_contra h
    push Not at h
    exact hd₀K (mem_inf.2 ⟨hd₀D, mem_centralizer_iff.2 fun v hv => h v hv⟩)
  have hB₀D : closure ({z, d₀} : Set G) ≤ D := (closure_le _).2 (by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl
    exacts [(mem_inf.1 hzK).1, hd₀D])
  have hB₀c : ¬ IsCyclic (closure ({z, d₀} : Set G)) := by
    intro hc
    have h2 := card_le_two_of_isCyclic hc fun x hx => hA2 x (hDA (hB₀D hx))
    have hd₀1 : d₀ ≠ 1 := fun h => hd₀K (h ▸ one_mem K)
    have hzd : z = d₀ := eq_of_card_le_two h2 (subset_closure (by simp))
      (subset_closure (by simp)) hz1 hd₀1
    exact hd₀K (hzd ▸ hzK)
  have hd₀ : ∀ v ∈ V, v * d₀ = d₀ * v → ∀ d ∈ D, v * d = d * v := by
    intro v hv hvd
    refine hB _ hB₀D hB₀c v hv ?_
    rw [centralizer_closure, mem_centralizer_iff]
    intro w hw
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hw
    rcases hw with rfl | rfl
    · exact (hKV w hzK v hv).symm
    · exact hvd.symm
  let φ : V →* G :=
    { toFun := fun v => d₀ * v * d₀⁻¹ * (v : G)⁻¹
      map_one' := by simp
      map_mul' := fun v₁ v₂ => by
        have ha₂ : d₀ * v₂ * d₀⁻¹ * (v₂ : G)⁻¹ ∈ V :=
          hRV (hcR d₀ hd₀D v₂ v₂.2)
        have hc := hVab _ ha₂ _ (inv_mem v₁.2)
        show d₀ * ((v₁ : G) * v₂) * d₀⁻¹ * ((v₁ : G) * v₂)⁻¹ =
          (d₀ * v₁ * d₀⁻¹ * (v₁ : G)⁻¹) * (d₀ * v₂ * d₀⁻¹ * (v₂ : G)⁻¹)
        calc d₀ * ((v₁ : G) * v₂) * d₀⁻¹ * ((v₁ : G) * v₂)⁻¹ =
              (d₀ * v₁ * d₀⁻¹) * ((d₀ * v₂ * d₀⁻¹ * (v₂ : G)⁻¹) * (v₁ : G)⁻¹) := by group
          _ = (d₀ * v₁ * d₀⁻¹) * ((v₁ : G)⁻¹ * (d₀ * v₂ * d₀⁻¹ * (v₂ : G)⁻¹)) := by rw [hc]
          _ = _ := by group }
  have hφ : ∀ v : V, φ v = d₀ * v * d₀⁻¹ * (v : G)⁻¹ := fun _ => rfl
  have hhyp : ∀ v ∈ V, v * d₀ = d₀ * v ∨ v * v₀⁻¹ * d₀ = d₀ * (v * v₀⁻¹) := by
    intro v hv
    by_cases hvd : v * d₀ = d₀ * v
    · exact Or.inl hvd
    refine Or.inr ?_
    have hne : ∀ w : V, w * d₀ ≠ d₀ * w → φ w ≠ 1 := fun w hw h1 => hw (hcomm h1).symm
    have heq := eq_of_card_le_two hR2 (hcR d₀ hd₀D v hv) (hcR d₀ hd₀D v₀ hv₀V)
      (hne ⟨v, hv⟩ hvd) (hne ⟨v₀, hv₀V⟩ hv₀d₀)
    have h1 : φ (⟨v, hv⟩ * (⟨v₀, hv₀V⟩ : V)⁻¹) = 1 := by
      rw [map_mul, map_inv]
      change d₀ * v * d₀⁻¹ * v⁻¹ * (d₀ * v₀ * d₀⁻¹ * v₀⁻¹)⁻¹ = 1
      rw [heq, mul_inv_cancel]
    rw [hφ] at h1
    exact (hcomm h1).symm
  let ψ : D →* G :=
    { toFun := fun d => (d : G) * v₀ * (d : G)⁻¹ * v₀⁻¹
      map_one' := by simp
      map_mul' := fun d₁ d₂ => by
        have h1 : (d₁ : G) * ((d₂ : G) * v₀ * (d₂ : G)⁻¹ * v₀⁻¹) =
            ((d₂ : G) * v₀ * (d₂ : G)⁻¹ * v₀⁻¹) * d₁ :=
          mem_centralizer_iff.1 (hRA (hcR d₂ d₂.2 v₀ hv₀V)) d₁ (hDA d₁.2)
        have h2 := hVab _ (hRV (hcR d₁ d₁.2 v₀ hv₀V)) _ (hRV (hcR d₂ d₂.2 v₀ hv₀V))
        show (d₁ : G) * d₂ * v₀ * ((d₁ : G) * d₂)⁻¹ * v₀⁻¹ =
          ((d₁ : G) * v₀ * (d₁ : G)⁻¹ * v₀⁻¹) * ((d₂ : G) * v₀ * (d₂ : G)⁻¹ * v₀⁻¹)
        calc (d₁ : G) * d₂ * v₀ * ((d₁ : G) * d₂)⁻¹ * v₀⁻¹ =
              ((d₁ : G) * ((d₂ : G) * v₀ * (d₂ : G)⁻¹ * v₀⁻¹)) * (v₀ * (d₁ : G)⁻¹ * v₀⁻¹) := by
                group
          _ = ((d₂ : G) * v₀ * (d₂ : G)⁻¹ * v₀⁻¹) * ((d₁ : G) * v₀ * (d₁ : G)⁻¹ * v₀⁻¹) := by
                rw [h1]; group
          _ = _ := h2.symm }
  have hker : ∀ d : D, ψ d = 1 → (d : G) ∈ K := by
    intro d hd
    have hdv₀ : (d : G) * v₀ = v₀ * d := hcomm hd
    refine mem_inf.2 ⟨d.2, mem_centralizer_iff.2 fun v hv => ?_⟩
    rcases hhyp v hv with hvd | hvd
    · exact hd₀ v hv hvd d d.2
    · have h1 := hd₀ (v * v₀⁻¹) (mul_mem hv (inv_mem hv₀V)) hvd d d.2
      calc v * d = (v * v₀⁻¹) * (v₀ * d) := by group
        _ = (v * v₀⁻¹) * (d * v₀) := by rw [hdv₀]
        _ = d * (v * v₀⁻¹) * v₀ := by rw [← mul_assoc, h1]
        _ = d * v := by group
  have hkerK : Nat.card ψ.ker ≤ Nat.card K := by
    refine Nat.card_le_card_of_injective (fun d => (⟨(d : D), hker d d.2⟩ : K)) ?_
    intro x y hxy
    apply Subtype.ext
    apply Subtype.ext
    exact congrArg (fun k : K => (k : G)) hxy
  have hrange : Nat.card ψ.range ≤ Nat.card R := by
    refine card_le_of_le ?_
    rintro _ ⟨d, rfl⟩
    exact hcR d d.2 v₀ hv₀V
  have hD4 : Nat.card D ≤ 4 := calc
    Nat.card D = Nat.card ψ.ker * Nat.card ψ.range := (card_ker_mul_card_range ψ).symm
    _ ≤ Nat.card K * Nat.card R := Nat.mul_le_mul hkerK hrange
    _ ≤ 2 * 2 := Nat.mul_le_mul hK2 hR2
  omega

end CFSG.Quasithin.SteinbergBS
