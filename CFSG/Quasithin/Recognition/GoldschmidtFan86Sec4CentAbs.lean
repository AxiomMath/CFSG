module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec4CentFin

public section

namespace CFSG.Quasithin.Fan86

variable {S C X : Type*} [Group S] [Group C] [Group X]

theorem central_abs (hC : IsPGroup 2 C) (e : X ≃* S × C) (P : S → Prop) (hP1 : P 1)
    (hPm : ∀ v w, P v → P w → P (v * w)) (hPi : ∀ v, P v → P v⁻¹)
    (hPc : ∀ v σ, P v → P (σ * v * σ⁻¹))
    (hF1 : ∀ ξ : S, ξ ^ 3 = 1 → ξ ≠ 1 → ∀ K : Subgroup S, IsPGroup 2 K →
      (∀ k ∈ K, ξ * k * ξ⁻¹ ∈ K) → ∀ k ∈ K, P k)
    (hF2 : ∀ ξ : S, ξ ^ 3 = 1 → ξ ≠ 1 → ∀ v w : S, P v → v ≠ 1 → P w → w ≠ 1 →
      ∃ j : ℕ, ξ ^ j * v * (ξ ^ j)⁻¹ = w)
    {p : X} (hp3 : p ^ 3 = 1) (hp1 : p ≠ 1) {O N : Subgroup X} [O.Normal] (hO : IsPGroup 2 O)
    (hNO : N ≤ O) (hpN : ∀ g ∈ N, p * g * p⁻¹ ∈ N)
    (h5 : ∃ k ∈ O, p * k * p⁻¹ * k⁻¹ ∉ N) : ∀ g ∈ N, p * g = g * p := by
  let φS : X →* S := (MonoidHom.fst S C).comp (e : X →* S × C)
  have hφS : ∀ x, φS x = (e x).1 := fun x => rfl
  have hc : (e p).2 = 1 := by
    have h := congrArg (fun x => (e x).2) hp3
    exact eq_one_of_pow_three_eq_one hC (by simpa [map_pow] using h)
  have hσ3 : (e p).1 ^ 3 = 1 := by
    have h := congrArg (fun x => (e x).1) hp3
    simpa [map_pow] using h
  have hσ1 : (e p).1 ≠ 1 := by
    intro h
    exact hp1 (e.injective (Prod.ext (by simpa using h) (by simpa using hc)))
  have hOP : ∀ g ∈ O, P (e g).1 := by
    intro g hg
    refine hF1 (e p).1 hσ3 hσ1 (O.map φS) (hO.map φS) ?_ _ ⟨g, hg, rfl⟩
    rintro _ ⟨g', hg', rfl⟩
    exact ⟨p * g' * p⁻¹, (inferInstance : O.Normal).conj_mem g' hg' p, by simp [hφS]⟩
  let Vh : Subgroup X :=
    { carrier := {g | P (e g).1 ∧ (e g).2 = 1}
      mul_mem' := fun {g h} hg hh => ⟨by simpa using hPm _ _ hg.1 hh.1, by simp [hg.2, hh.2]⟩
      one_mem' := ⟨by simpa using hP1, by simp⟩
      inv_mem' := fun {g} hg => ⟨by simpa using hPi _ hg.1, by simp [hg.2]⟩ }
  have hVc : ∀ g ∈ Vh, p * g * p⁻¹ ∈ Vh := by
    intro g hg
    refine ⟨by simpa using hPc _ _ hg.1, ?_⟩
    simp [hc, hg.2]
  have hcomm : ∀ k ∈ O, p * k * p⁻¹ * k⁻¹ ∈ Vh := by
    intro k hk
    refine ⟨?_, ?_⟩
    · have h1 := hPm _ _ (hPc _ (e p).1 (hOP k hk)) (hPi _ (hOP k hk))
      simpa using h1
    · simp [hc]
  let W : Subgroup X := N ⊓ Vh
  let WS : Subgroup S := W.map φS
  have hWP : ∀ w ∈ WS, P w := by
    rintro _ ⟨g, hg, rfl⟩
    exact hg.2.1
  have hWc : ∀ w ∈ WS, (e p).1 * w * (e p).1⁻¹ ∈ WS := by
    rintro _ ⟨g, hg, rfl⟩
    exact ⟨p * g * p⁻¹, ⟨hpN g hg.1, hVc g hg.2⟩, by simp [hφS]⟩
  by_cases hWt : ∀ w ∈ WS, w = 1
  · intro g hg
    have hgW : p * g * p⁻¹ * g⁻¹ ∈ W :=
      ⟨N.mul_mem (hpN g hg) (N.inv_mem hg), hcomm g (hNO hg)⟩
    have h1 : (e (p * g * p⁻¹ * g⁻¹)).1 = 1 := hWt _ ⟨_, hgW, rfl⟩
    have h2 : (e (p * g * p⁻¹ * g⁻¹)).2 = 1 := hgW.2.2
    have : p * g * p⁻¹ * g⁻¹ = 1 := e.injective (Prod.ext (by simpa using h1) (by simpa using h2))
    exact commutatorElement_eq_one_iff_mul_comm.1 this
  · exfalso
    push Not at hWt
    obtain ⟨w₀, hw₀, hw₀1⟩ := hWt
    have hall : ∀ v, P v → v ∈ WS := by
      intro v hv
      by_cases hv1 : v = 1
      · subst hv1
        exact WS.one_mem
      · obtain ⟨j, hj⟩ := hF2 (e p).1 hσ3 hσ1 w₀ v (hWP w₀ hw₀) hw₀1 hv hv1
        rw [← hj]
        exact conj_pow_mem hWc hw₀ j
    have hVN : ∀ g ∈ Vh, g ∈ N := by
      intro g hg
      obtain ⟨g', hg', hg'S⟩ := hall _ hg.1
      have : e g' = e g := Prod.ext hg'S (by rw [hg'.2.2, hg.2])
      rw [← e.injective this]
      exact hg'.1
    obtain ⟨k, hkO, hk⟩ := h5
    exact hk (hVN _ (hcomm k hkO))

theorem central_perm {n : ℕ} (hn : n = 3 ∨ n = 4) (hC : IsPGroup 2 C)
    (e : X ≃* Equiv.Perm (Fin n) × C) {p : X} (hp3 : p ^ 3 = 1) (hp1 : p ≠ 1)
    {O N : Subgroup X} [O.Normal] (hO : IsPGroup 2 O) (hNO : N ≤ O)
    (hpN : ∀ g ∈ N, p * g * p⁻¹ ∈ N) (h5 : ∃ k ∈ O, p * k * p⁻¹ * k⁻¹ ∉ N) :
    ∀ g ∈ N, p * g = g * p := by
  rcases hn with rfl | rfl
  · exact central_abs hC e (fun v => v = 1) rfl (fun v w hv hw => by simp [hv, hw])
      (fun v hv => by simp [hv]) (fun v σ hv => by simp [hv])
      (fun ξ h3 h1 K hK hN k hk => eq_one_of_normalized_three h3 h1 hK hN k hk)
      (fun ξ _ _ v w hv hv1 _ _ => absurd hv hv1) hp3 hp1 hO hNO hpN h5
  · exact central_abs hC e IsKlein4 (Or.inl rfl) isKlein4_mul isKlein4_inv
      (fun v σ hv => isKlein4_conj hv σ)
      (fun ξ h3 h1 K hK hN => isKlein4_of_normalized_four h3 h1 hK hN)
      (fun ξ h3 h1 v w hv hv1 hw hw1 => exists_conj_eq_four h3 h1 hv hv1 hw hw1)
      hp3 hp1 hO hNO hpN h5

end CFSG.Quasithin.Fan86
