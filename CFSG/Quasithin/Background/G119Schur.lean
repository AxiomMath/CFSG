module

public import CFSG.Quasithin.Background.G11BridgeRestrict

public section

namespace CFSG.Quasithin

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

@[expose] def G119IsHEnd (H : Subgroup (GLV V)) (J : Submodule (ZMod 2) V) (f : ↥J →ₗ[ZMod 2] ↥J) :
    Prop :=
  ∀ h ∈ H, ∀ j j' : ↥J, h (j : V) = (j' : V) → h ((f j : ↥J) : V) = ((f j' : ↥J) : V)

section G119IsHEnd

variable {H : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}

theorem G119IsHEnd.sub {f g : ↥J →ₗ[ZMod 2] ↥J} (hf : G119IsHEnd H J f) (hg : G119IsHEnd H J g) :
    G119IsHEnd H J (f - g) := fun h hh j j' hj => by
  have h1 := hf h hh j j' hj
  have h2 := hg h hh j j' hj
  simp only [LinearMap.sub_apply, Submodule.coe_sub, map_sub]
  rw [h1, h2]

theorem g119_isHEnd_id : G119IsHEnd H J LinearMap.id := fun _ _ _ _ hj => hj

theorem G119IsHEnd.invariant_ker (hJ : Invariant H J) {f : ↥J →ₗ[ZMod 2] ↥J}
    (hf : G119IsHEnd H J f) :
    Invariant H ((LinearMap.ker f).map J.subtype) := by
  rintro h hh _ ⟨j, hj, rfl⟩
  have hmem : h (j : V) ∈ J := hJ h hh j j.2
  refine ⟨⟨h (j : V), hmem⟩, ?_, rfl⟩
  have := hf h hh j ⟨h (j : V), hmem⟩ rfl
  rw [LinearMap.mem_ker.1 hj] at this
  simp only [Submodule.coe_zero, map_zero] at this
  exact Subtype.ext this.symm

theorem G119IsHEnd.invariant_range (hJ : Invariant H J) {f : ↥J →ₗ[ZMod 2] ↥J}
    (hf : G119IsHEnd H J f) : Invariant H ((LinearMap.range f).map J.subtype) := by
  rintro h hh _ ⟨_, ⟨j, rfl⟩, rfl⟩
  have hmem : h (j : V) ∈ J := hJ h hh j j.2
  exact ⟨f ⟨h (j : V), hmem⟩, ⟨_, rfl⟩, (hf h hh j ⟨h (j : V), hmem⟩ rfl).symm⟩

theorem G119IsHEnd.ker_eq_bot_or_top (hJ : IsIrr H J) {f : ↥J →ₗ[ZMod 2] ↥J}
    (hf : G119IsHEnd H J f) :
    LinearMap.ker f = ⊥ ∨ LinearMap.ker f = ⊤ := by
  have hle : (LinearMap.ker f).map J.subtype ≤ J := Submodule.map_subtype_le J _
  rcases hJ.eq_bot_or_eq (hf.invariant_ker hJ.1) hle with h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro j hj
    have : (j : V) ∈ (LinearMap.ker f).map J.subtype := ⟨j, hj, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro j _
    have : (j : V) ∈ (LinearMap.ker f).map J.subtype := by rw [h]; exact j.2
    obtain ⟨j', hj', hjj⟩ := this
    have : j' = j := Subtype.ext hjj
    rw [← this]
    exact hj'

theorem G119IsHEnd.range_eq_bot_or_top (hJ : IsIrr H J) {f : ↥J →ₗ[ZMod 2] ↥J}
    (hf : G119IsHEnd H J f) : LinearMap.range f = ⊥ ∨ LinearMap.range f = ⊤ := by
  have hle : (LinearMap.range f).map J.subtype ≤ J := Submodule.map_subtype_le J _
  rcases hJ.eq_bot_or_eq (hf.invariant_range hJ.1) hle with h | h
  · left
    rw [Submodule.eq_bot_iff]
    rintro _ ⟨j, rfl⟩
    have : ((f j : ↥J) : V) ∈ (LinearMap.range f).map J.subtype := ⟨f j, ⟨j, rfl⟩, rfl⟩
    rw [h, Submodule.mem_bot] at this
    exact Subtype.ext this
  · right
    rw [eq_top_iff]
    intro j _
    have : (j : V) ∈ (LinearMap.range f).map J.subtype := by rw [h]; exact j.2
    obtain ⟨j', hj', hjj⟩ := this
    have : j' = j := Subtype.ext hjj
    rw [← this]
    exact hj'

end G119IsHEnd

section Key

variable {H : Subgroup (GLV V)} {J : Submodule (ZMod 2) V}

theorem g119_inv_eq_self_of_mul_self_eq_one {x : GLV V} (hx2 : x * x = 1) : x⁻¹ = x :=
  inv_eq_of_mul_eq_one_right hx2

theorem g119_endo_eq_zero_or_id_of_transvection [Finite V] (hJ : IsIrr H J)
    (hdim : 2 < Module.finrank (ZMod 2) J) {x : GLV V} (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H)
    (hxJ : conjSub x J = J) (hx2 : x * x = 1) (htr : ∃ c : V, InducesTransvection x J c)
    {f : ↥J →ₗ[ZMod 2] ↥J} (hf : G119IsHEnd H J f) : f = 0 ∨ f = LinearMap.id := by
  classical
  have hxx : ∀ v : V, x (x v) = v := fun v => by
    have := congrArg (fun e : GLV V => e v) hx2
    exact this
  set N : ↥J ≃ₗ[ZMod 2] ↥J := restrictEquiv x J hxJ with hN
  set Nn : ↥J →ₗ[ZMod 2] ↥J := commMap x J hxJ with hNn
  have hNN : ∀ j : ↥J, N (N j) = j := fun j => Subtype.ext (hxx (j : V))
  have hNnj : ∀ j : ↥J, Nn j = N j - j := fun j => rfl
  have hfr : Module.finrank (ZMod 2) (LinearMap.range Nn) = 1 :=
    (inducesTransvection_iff_finrank hxJ).1 htr
  set f' : ↥J →ₗ[ZMod 2] ↥J := (N : ↥J →ₗ[ZMod 2] ↥J) ∘ₗ f ∘ₗ (N : ↥J →ₗ[ZMod 2] ↥J) with hf'
  have hf'j : ∀ j : ↥J, f' j = N (f (N j)) := fun j => rfl
  have hf'H : G119IsHEnd H J f' := by
    intro h hh j j' hj
    have hh' : x * h * x ∈ H := by
      have := hxH h hh
      rwa [g119_inv_eq_self_of_mul_self_eq_one hx2] at this
    have h1 : (x * h * x) ((N j : ↥J) : V) = ((N j' : ↥J) : V) := by
      show x (h (x (x (j : V)))) = x (j' : V)
      rw [hxx, hj]
    have h2 := hf (x * h * x) hh' (N j) (N j') h1
    show h (x ((f (N j) : ↥J) : V)) = x ((f (N j') : ↥J) : V)
    rw [← h2]
    show h (x ((f (N j) : ↥J) : V)) = x (x (h (x ((f (N j) : ↥J) : V))))
    rw [hxx]
  have hgH : G119IsHEnd H J (f' - f) := hf'H.sub hf
  have hrank : Module.finrank (ZMod 2) (LinearMap.range (f' - f)) ≤ 2 := by
    have hle : LinearMap.range (f' - f) ≤ LinearMap.range Nn ⊔ (LinearMap.range Nn).map f' := by
      rintro _ ⟨j, rfl⟩
      have key : (f' - f) j = Nn (f j) - f' (Nn j) := by
        have e1 : f' (Nn j) = N (f j) - N (f (N j)) := by
          rw [hNnj, map_sub, hf'j, hf'j, hNN]
        rw [e1, hNnj, LinearMap.sub_apply, hf'j]
        abel
      rw [key]
      exact Submodule.sub_mem _ (Submodule.mem_sup_left ⟨f j, rfl⟩)
        (Submodule.mem_sup_right ⟨Nn j, ⟨j, rfl⟩, rfl⟩)
    calc Module.finrank (ZMod 2) (LinearMap.range (f' - f))
        ≤ Module.finrank (ZMod 2) ↥(LinearMap.range Nn ⊔ (LinearMap.range Nn).map f') :=
          Submodule.finrank_mono hle
      _ ≤ Module.finrank (ZMod 2) (LinearMap.range Nn) +
            Module.finrank (ZMod 2) ↥((LinearMap.range Nn).map f') :=
          Submodule.finrank_add_le_finrank_add_finrank _ _
      _ ≤ 1 + 1 := by
          have := Submodule.finrank_map_le f' (LinearMap.range Nn)
          omega
      _ = 2 := rfl
  have hg0 : f' - f = 0 := by
    rcases hgH.range_eq_bot_or_top hJ with h | h
    · exact LinearMap.range_eq_bot.1 h
    · exfalso
      rw [h, finrank_top] at hrank
      omega
  have hf'f : ∀ j : ↥J, N (f (N j)) = f j := fun j => by
    have := congrArg (fun g : ↥J →ₗ[ZMod 2] ↥J => g j) hg0
    simpa [sub_eq_zero, hf'j] using this
  have hcomm : ∀ j : ↥J, f (N j) = N (f j) := fun j => by
    have h1 := hf'f j
    have h2 := congrArg N h1
    rw [hNN] at h2
    exact h2
  have hcommNn : ∀ j : ↥J, f (Nn j) = Nn (f j) := fun j => by
    rw [hNnj, hNnj, map_sub, hcomm]
  by_cases hf0 : f = 0
  · exact Or.inl hf0
  right
  obtain ⟨j₁, hj₁⟩ : ∃ j₁, f j₁ ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hf0 (LinearMap.ext hcon)
  have hker : LinearMap.ker f = ⊥ := by
    rcases hf.ker_eq_bot_or_top hJ with h | h
    · exact h
    · exfalso
      exact hj₁ (LinearMap.mem_ker.1 (h ▸ Submodule.mem_top))
  have hinj : Function.Injective f := LinearMap.ker_eq_bot.1 hker
  obtain ⟨c, hc0, hc⟩ := finrank_eq_one_iff'.1 hfr
  have hfc : f (c : ↥J) ∈ LinearMap.range Nn := by
    obtain ⟨j₀, hj₀⟩ := c.2
    exact ⟨f j₀, by rw [← hj₀, hcommNn]⟩
  obtain ⟨a, ha⟩ := hc ⟨f (c : ↥J), hfc⟩
  have hc0' : (c : ↥J) ≠ 0 := fun h => hc0 (Subtype.ext h)
  have ha1 : a = 1 := by
    have hz : ∀ a : ZMod 2, a = 0 ∨ a = 1 := zmod2_eq_zero_or_one
    rcases hz a with rfl | rfl
    · exfalso
      have : f (c : ↥J) = 0 := by
        have := congrArg (fun w : ↥(LinearMap.range Nn) => (w : ↥J)) ha
        simpa using this.symm
      exact hc0' (hinj (by rw [this, map_zero]))
    · rfl
  have hfc1 : f (c : ↥J) = c := by
    have := congrArg (fun w : ↥(LinearMap.range Nn) => (w : ↥J)) ha
    simpa [ha1] using this.symm
  have hker1 : LinearMap.ker (f - LinearMap.id) = ⊤ := by
    rcases (hf.sub g119_isHEnd_id).ker_eq_bot_or_top hJ with h | h
    · exfalso
      have hmem : (c : ↥J) ∈ LinearMap.ker (f - LinearMap.id) := by
        rw [LinearMap.mem_ker, LinearMap.sub_apply, hfc1]
        simp
      rw [h, Submodule.mem_bot] at hmem
      exact hc0' hmem
    · exact h
  ext j
  have := LinearMap.mem_ker.1 (hker1 ▸ Submodule.mem_top : j ∈ LinearMap.ker (f - LinearMap.id))
  simpa [sub_eq_zero] using this

theorem g119_commute_of_transvection [Finite V] {I : Submodule (ZMod 2) V} (hJ : IsIrr H J)
    (hI : Invariant H I) (hdim : 2 < Module.finrank (ZMod 2) J) {x : GLV V}
    (hxH : ∀ h ∈ H, x * h * x⁻¹ ∈ H) (hxI : conjSub x I = I) (hxJ : conjSub x J = J)
    (hx2 : x * x = 1) (htr : ∃ c : V, InducesTransvection x J c) (φ : I ≃ₗ[ZMod 2] J)
    (hφ : ∀ k ∈ H, ∀ i j : ↥I, k (i : V) = (j : V) → k ((φ i : ↥J) : V) = ((φ j : ↥J) : V))
    (i : ↥I) : x ((φ i : ↥J) : V) = ((φ (restrictEquiv x I hxI i) : ↥J) : V) := by
  classical
  have hxx : ∀ v : V, x (x v) = v := fun v => by
    have := congrArg (fun e : GLV V => e v) hx2
    exact this
  set M : ↥I ≃ₗ[ZMod 2] ↥I := restrictEquiv x I hxI with hM
  set N : ↥J ≃ₗ[ZMod 2] ↥J := restrictEquiv x J hxJ with hN
  have hMM : ∀ i : ↥I, M (M i) = i := fun i => Subtype.ext (hxx (i : V))
  have hNN : ∀ j : ↥J, N (N j) = j := fun j => Subtype.ext (hxx (j : V))
  set f : ↥J →ₗ[ZMod 2] ↥J := (N : ↥J →ₗ[ZMod 2] ↥J) ∘ₗ (φ : ↥I →ₗ[ZMod 2] ↥J) ∘ₗ
    (M : ↥I →ₗ[ZMod 2] ↥I) ∘ₗ (φ.symm : ↥J →ₗ[ZMod 2] ↥I) with hf
  have hfj : ∀ j : ↥J, f j = N (φ (M (φ.symm j))) := fun j => rfl
  have hfH : G119IsHEnd H J f := by
    intro h hh j j' hj
    set i₁ : ↥I := φ.symm j with hi₁
    set i₁' : ↥I := φ.symm j' with hi₁'
    have hjj : j = φ i₁ := by rw [hi₁, LinearEquiv.apply_symm_apply]
    have hjj' : j' = φ i₁' := by rw [hi₁', LinearEquiv.apply_symm_apply]
    have hmemI : h (i₁ : V) ∈ I := hI h hh i₁ i₁.2
    have h1 := hφ h hh i₁ ⟨h (i₁ : V), hmemI⟩ rfl
    have h2 : φ ⟨h (i₁ : V), hmemI⟩ = φ i₁' := by
      apply Subtype.ext
      rw [← h1, ← hjj, ← hjj']
      exact hj
    have h3 : (⟨h (i₁ : V), hmemI⟩ : ↥I) = i₁' := φ.injective h2
    have h4 : h (i₁ : V) = (i₁' : V) := congrArg Subtype.val h3
    have hh' : x * h * x ∈ H := by
      have := hxH h hh
      rwa [g119_inv_eq_self_of_mul_self_eq_one hx2] at this
    have h5 : (x * h * x) ((M i₁ : ↥I) : V) = ((M i₁' : ↥I) : V) := by
      show x (h (x (x (i₁ : V)))) = x (i₁' : V)
      rw [hxx, h4]
    have h6 := hφ (x * h * x) hh' (M i₁) (M i₁') h5
    rw [hfj, hfj, ← hi₁, ← hi₁']
    show h (x ((φ (M i₁) : ↥J) : V)) = x ((φ (M i₁') : ↥J) : V)
    rw [← h6]
    show h (x ((φ (M i₁) : ↥J) : V)) = x (x (h (x ((φ (M i₁) : ↥J) : V))))
    rw [hxx]
  have hfinj : Function.Injective f := by
    intro a b hab
    simp only [hfj] at hab
    exact φ.symm.injective (M.injective (φ.injective (N.injective hab)))
  rcases g119_endo_eq_zero_or_id_of_transvection hJ hdim hxH hxJ hx2 htr hfH with h0 | hid
  · exfalso
    have hnt : Nontrivial ↥J := Module.nontrivial_of_finrank_pos (R := ZMod 2) (by omega)
    obtain ⟨j, hj⟩ := exists_ne (0 : ↥J)
    exact hj (hfinj (by rw [h0]; simp))
  · have h1 : f (φ i) = φ i := by rw [hid]; rfl
    rw [hfj, LinearEquiv.symm_apply_apply] at h1
    have h2 := congrArg N h1
    rw [hNN] at h2
    exact (congrArg Subtype.val h2).symm

theorem g119_finrank_commMap_eq_of_commute [Finite V] {I : Submodule (ZMod 2) V} {x : GLV V}
    (hxI : conjSub x I = I) (hxJ : conjSub x J = J) (φ : I ≃ₗ[ZMod 2] J)
    (hcomm : ∀ i : ↥I, x ((φ i : ↥J) : V) = ((φ (restrictEquiv x I hxI i) : ↥J) : V)) :
    Module.finrank (ZMod 2) (LinearMap.range (commMap x I hxI)) =
      Module.finrank (ZMod 2) (LinearMap.range (commMap x J hxJ)) := by
  have hcomp : (commMap x J hxJ) ∘ₗ (φ : ↥I →ₗ[ZMod 2] ↥J) =
      (φ : ↥I →ₗ[ZMod 2] ↥J) ∘ₗ (commMap x I hxI) := by
    ext i
    simp only [LinearMap.coe_comp, Function.comp_apply, LinearEquiv.coe_coe]
    rw [coe_commMap]
    have : (commMap x I hxI i : ↥I) = restrictEquiv x I hxI i - i := rfl
    rw [this, map_sub, Submodule.coe_sub, ← hcomm i]
  have h1 : LinearMap.range ((commMap x J hxJ) ∘ₗ (φ : ↥I →ₗ[ZMod 2] ↥J)) =
      LinearMap.range (commMap x J hxJ) :=
    LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range φ)
  have h2 : LinearMap.range ((φ : ↥I →ₗ[ZMod 2] ↥J) ∘ₗ (commMap x I hxI)) =
      (LinearMap.range (commMap x I hxI)).map (φ : ↥I →ₗ[ZMod 2] ↥J) :=
    LinearMap.range_comp _ _
  rw [← h1, hcomp, h2]
  exact (LinearEquiv.finrank_map_eq φ _).symm

end Key

end G11

end CFSG.Quasithin
