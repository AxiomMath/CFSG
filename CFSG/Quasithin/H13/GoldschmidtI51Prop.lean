module

public import CFSG.Quasithin.H13.GoldschmidtI51Geom2
public import CFSG.Quasithin.H13.GoldschmidtI51Nbd

public section

namespace CFSG.Quasithin.H13.I51

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {Gs : Fin 3 → Subgroup G}

theorem loc2_fanoB (hD : IsDSystem .C3 Gs) :
    ∀ g ∈ Gs 2, ∃ a ∈ Gs 1 ⊓ Gs 2, ∃ b ∈ Gs 0 ⊓ Gs 2, ∃ c ∈ Gs 1 ⊓ Gs 2, g = a * b * c := by
  obtain ⟨A, B, φ, hM, hφ, hker, hA, hB, hT⟩ := model2 hD
  exact bridge_prod3 φ hker hB hA hB (Q2_le_P12 hD) hM.fanoB

omit [Finite G] in
theorem Nr_mul_left {v u : G} (hv : v ∈ Gs 0 ⊓ Gs 1) (hu : Nr Gs u) : Nr Gs (v * u) := by
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hu
  exact ⟨v * a, (Gs 0 ⊓ Gs 1).mul_mem hv ha, b, hb, c, hc, by group⟩

theorem propagate (hD : IsDSystem .C3 Gs) {s0 f t h : G} (hs0 : s0 ∈ Gs 1) (hs00 : s0 ∉ Gs 0)
    (hf : f ∈ Gs 0) (hnf : ¬ Nr Gs f) (ht : t ∈ Gs 1) (hh : Nr Gs h) :
    ∃ s' ∈ Gs 1, s' ∉ Gs 0 ∧ (f * t)⁻¹ * (s0 * h * s') ∈ Nbd Gs := by
  have hhG0 : h ∈ Gs 0 := by
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hh
    exact (Gs 0).mul_mem ((Gs 0).mul_mem ha.1 hb.1) hc.1
  obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := hh
  obtain ⟨p, hp, x1, hx1, hpx⟩ := loc1_prod2 hD (s0 * a) ((Gs 1).mul_mem hs0 ha.2)
  obtain ⟨c0, hc0, hNr⟩ := (gqLoc hD).gq3 (p⁻¹ * f) ((Gs 0).mul_mem ((Gs 0).inv_mem hp.1) hf)
  have hA : x1 * b ∈ Gs 2 := (Gs 2).mul_mem hx1.2 hb.2
  obtain ⟨x, hx, y, hy, x', hx', hfano⟩ :=
    loc2_fanoB hD ((x1 * b)⁻¹ * c0) ((Gs 2).mul_mem ((Gs 2).inv_mem hA) hc0.2)
  have hs' : c⁻¹ * x ∈ Gs 1 := (Gs 1).mul_mem ((Gs 1).inv_mem hc.2) hx.1
  have hs1 : x'⁻¹ ∈ Gs 1 := (Gs 1).inv_mem hx'.1
  have hc0eq : c0 = (x1 * b) * x * y * x' := by
    have := congrArg (fun w => (x1 * b) * w) hfano
    simpa [mul_assoc] using this
  have E : s0 * (a * b * c) * (c⁻¹ * x) = (p * c0) * x'⁻¹ * y⁻¹ := by
    calc s0 * (a * b * c) * (c⁻¹ * x) = (s0 * a) * b * x := by group
      _ = (p * x1) * b * x := by rw [hpx]
      _ = p * ((x1 * b) * x * y * x') * x'⁻¹ * y⁻¹ := by group
      _ = (p * c0) * x'⁻¹ * y⁻¹ := by rw [hc0eq]
  refine ⟨c⁻¹ * x, hs', ?_, ?_⟩
  · intro hs'0
    have hhs : (a * b * c) * (c⁻¹ * x) ∈ Gs 0 :=
      (Gs 0).mul_mem ((Gs 0).mul_mem ((Gs 0).mul_mem ha.1 hb.1) hc.1) hs'0
    have e2 : s0⁻¹ * (p * c0) * x'⁻¹ = ((a * b * c) * (c⁻¹ * x)) * y := by
      calc s0⁻¹ * (p * c0) * x'⁻¹ = s0⁻¹ * ((p * c0) * x'⁻¹ * y⁻¹) * y := by group
        _ = s0⁻¹ * (s0 * (a * b * c) * (c⁻¹ * x)) * y := by rw [← E]
        _ = ((a * b * c) * (c⁻¹ * x)) * y := by group
    have hrel : s0⁻¹ * (p * c0) * x'⁻¹ ∈ Gs 0 := by
      rw [e2]; exact (Gs 0).mul_mem hhs hy.1
    have hpc0 : p * c0 ∈ Gs 1 := uniq_line hD hs0 hs00 hs1 ((Gs 0).mul_mem hp.1 hc0.1) hrel
    have hP : p * c0 ∈ Gs 0 ⊓ Gs 1 := ⟨(Gs 0).mul_mem hp.1 hc0.1, hpc0⟩
    apply hnf
    have := Nr_mul_left hP hNr
    have e3 : p * c0 * (c0⁻¹ * (p⁻¹ * f)) = f := by group
    rwa [e3] at this
  · have hu : (x'⁻¹)⁻¹ * (c0⁻¹ * (p⁻¹ * f)) * t ∈ Nbd Gs := near_collinear hD hNr hs1 ht
    have e4 : (f * t)⁻¹ * (s0 * (a * b * c) * (c⁻¹ * x)) =
        ((x'⁻¹)⁻¹ * (c0⁻¹ * (p⁻¹ * f)) * t)⁻¹ * y⁻¹ := by
      rw [E]; group
    rw [e4]
    exact Nbd_mul_G0 ((Gs 0).inv_mem hy.1) (Nbd_inv hu)

theorem closure_step (hD : IsDSystem .C3 Gs) {g s1 : G} (hg : g ∉ Nbd Gs) (hs1 : s1 ∈ Gs 1)
    (hs10 : s1 ∉ Gs 0) (hcol : s1⁻¹ * g ∈ Nbd Gs) {h : G} (hh : Nr Gs h) :
    ∃ s' ∈ Gs 1, s' ∉ Gs 0 ∧ g⁻¹ * (h * s') ∈ Nbd Gs := by
  obtain ⟨x, hx, s'', hs'', c, hc, e⟩ := hcol
  have hge : g = s1 * x * s'' * c := by
    have := congrArg (fun w => s1 * w) e
    simpa [mul_assoc] using this
  have hnx : ¬ Nr Gs x := fun hnr => hg (by
    have h1 : (s1⁻¹)⁻¹ * x * s'' ∈ Nbd Gs := near_collinear hD hnr ((Gs 1).inv_mem hs1) hs''
    rw [hge]
    rw [inv_inv] at h1
    exact Nbd_mul_G0 hc (by simpa [mul_assoc] using h1))
  obtain ⟨s', hs', hs'0, hcol'⟩ := propagate hD ((Gs 1).inv_mem hs1)
    (fun h => hs10 (by simpa using (Gs 0).inv_mem h)) hx hnx hs'' hh
  refine ⟨s', hs', hs'0, ?_⟩
  have e' : g⁻¹ * (h * s') = c⁻¹ * ((x * s'')⁻¹ * (s1⁻¹ * h * s')) := by
    rw [hge]; group
  rw [e']
  exact G0_mul_Nbd ((Gs 0).inv_mem hc) hcol'

theorem shift_step (hD : IsDSystem .C3 Gs) {g h1 s : G} (hg : g ∉ Nbd Gs) (hh1 : h1 ∈ Gs 0)
    (hs : s ∈ Gs 1) (hs0 : s ∉ Gs 0) (hcol : g⁻¹ * (h1 * s) ∈ Nbd Gs) {w : G} (hw : Nr Gs w) :
    ∃ s' ∈ Gs 1, s' ∉ Gs 0 ∧ g⁻¹ * (h1 * w * s') ∈ Nbd Gs := by
  have hg' : h1⁻¹ * g ∉ Nbd Gs := fun h => hg (by
    have := G0_mul_Nbd hh1 h
    simpa using this)
  have hcol' : s⁻¹ * (h1⁻¹ * g) ∈ Nbd Gs := by
    have := Nbd_inv hcol
    simpa [mul_assoc] using this
  obtain ⟨s', hs', hs'0, h'⟩ := closure_step hD hg' hs hs0 hcol' hw
  refine ⟨s', hs', hs'0, ?_⟩
  have e : g⁻¹ * (h1 * w * s') = (h1⁻¹ * g)⁻¹ * (w * s') := by group
  rw [e]; exact h'

theorem line_has_point (hD : IsDSystem .C3 Gs) {g a : G} (hg : g ∉ Nbd Gs) (ha : a ∈ Nbd Gs)
    (hag : a⁻¹ * g ∈ Nbd Gs) :
    ∀ h ∈ Gs 0, ∃ s ∈ Gs 1, s ∉ Gs 0 ∧ g⁻¹ * (h * s) ∈ Nbd Gs := by
  obtain ⟨x1, hx1, s1, hs1, c1, hc1, rfl⟩ := ha
  have hs10 : s1 ∉ Gs 0 := fun h => hg (by
    have e : g = (x1 * s1 * c1) * ((x1 * s1 * c1)⁻¹ * g) := by group
    rw [e]
    exact G0_mul_Nbd ((Gs 0).mul_mem ((Gs 0).mul_mem hx1 h) hc1) hag)
  have hcol : g⁻¹ * (x1 * s1) ∈ Nbd Gs := by
    have h1 := Nbd_inv hag
    have h2 := Nbd_mul_G0 ((Gs 0).inv_mem hc1) h1
    have e : (( x1 * s1 * c1)⁻¹ * g)⁻¹ * c1⁻¹ = g⁻¹ * (x1 * s1) := by group
    rwa [e] at h2
  intro h2 hh2
  obtain ⟨c, hc, hNr⟩ := (gqLoc hD).gq3 (x1⁻¹ * h2) ((Gs 0).mul_mem ((Gs 0).inv_mem hx1) hh2)
  have hcNr : Nr Gs c := ⟨1, (Gs 0 ⊓ Gs 1).one_mem, c, hc, 1, (Gs 0 ⊓ Gs 1).one_mem, by group⟩
  obtain ⟨s2, hs2, hs20, hcol2⟩ := shift_step hD hg hx1 hs1 hs10 hcol hcNr
  have hxc : x1 * c ∈ Gs 0 := (Gs 0).mul_mem hx1 hc.1
  obtain ⟨s3, hs3, hs30, hcol3⟩ := shift_step hD hg hxc hs2 hs20 (by
    simpa [mul_assoc] using hcol2) hNr
  refine ⟨s3, hs3, hs30, ?_⟩
  have e : x1 * c * (c⁻¹ * (x1⁻¹ * h2)) * s3 = h2 * s3 := by group
  rwa [e] at hcol3

end CFSG.Quasithin.H13.I51
