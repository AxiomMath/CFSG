module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF2

public section

namespace CFSG.Quasithin.H13.C1294

theorem f3_chain {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (g : I ≃ₗ[ZMod 2] I)
    (hg3 : ∀ x, g (g (g x)) = x) (x : I) (W1 W2 : Submodule (ZMod 2) I)
    (h1 : g x - x ∈ W1) (h2 : ∀ y ∈ W1, g y - y ∈ W2) (h3 : ∀ z ∈ W2, g z = z) : g x = x := by
  obtain ⟨a, ha⟩ : ∃ a : I, a = g x - x := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : I, b = g a - a := ⟨_, rfl⟩
  have ha1 : a ∈ W1 := by rw [ha]; exact h1
  have hb2 : b ∈ W2 := by rw [hb]; exact h2 a ha1
  have hgb : g b = b := h3 b hb2
  have hgx : g x = x + a := by rw [ha]; abel
  have hga : g a = a + b := by rw [hb]; abel
  have haa : a + a = 0 := add_self_eq_zero_zmod2 a
  have e1 : g (g x) = x + b := by
    calc g (g x) = g (x + a) := by rw [hgx]
      _ = g x + g a := map_add g x a
      _ = (x + a) + (a + b) := by rw [hgx, hga]
      _ = x + (a + a) + b := by abel
      _ = x + b := by rw [haa, add_zero]
  have e2 : g (g (g x)) = x + a + b := by
    calc g (g (g x)) = g (x + b) := by rw [e1]
      _ = g x + g b := map_add g x b
      _ = (x + a) + b := by rw [hgx, hgb]
  have hab : a + b = 0 := by
    have h := hg3 x
    rw [e2] at h
    calc a + b = (x + a + b) - x := by abel
      _ = x - x := by rw [h]
      _ = 0 := sub_self x
  have hneg : -a = a := by rw [neg_eq_iff_add_eq_zero]; exact haa
  have hba : b = a := by
    calc b = (a + b) - a := by abel
      _ = -a := by rw [hab, zero_sub]
      _ = a := hneg
  have hga0 : g a = 0 := by
    have h : g a - a = a := by rw [← hb, hba]
    calc g a = (g a - a) + a := by abel
      _ = a + a := by rw [h]
      _ = 0 := haa
  have ha0 : a = 0 := (LinearEquiv.map_eq_zero_iff g).1 hga0
  rw [hgx, ha0, add_zero]

theorem f3_fix1 {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]
    (g : I ≃ₗ[ZMod 2] I)
    {p : Submodule (ZMod 2) I} (hp : Module.finrank (ZMod 2) p = 1)
    (hgp : ∀ x ∈ p, g x ∈ p) : ∀ v ∈ p, g v = v := by
  obtain ⟨e, he0, rfl⟩ := exists_span_singleton_eq hp
  intro v hv
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hv
  obtain ⟨b, hb⟩ := Submodule.mem_span_singleton.1 (hgp e (Submodule.mem_span_singleton_self e))
  have hge : g e ≠ 0 := fun h0 => he0 (g.injective (by rw [h0, map_zero]))
  have hb1 : b = 1 := by
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) b with h | h
    · exact (hge (by rw [← hb, h, zero_smul])).elim
    · exact h
  rw [map_smul, ← hb, hb1, one_smul]

theorem f3_finrank_sup {I : Type} [AddCommGroup I] [Module (ZMod 2) I]
    [FiniteDimensional (ZMod 2) I] {W : Submodule (ZMod 2) I} {x0 : I} (hx0 : x0 ∉ W) :
    Module.finrank (ZMod 2) ↥(W ⊔ Submodule.span (ZMod 2) {x0}) =
      Module.finrank (ZMod 2) W + 1 := by
  have hne : x0 ≠ 0 := fun h => hx0 (by rw [h]; exact W.zero_mem)
  have hinf : W ⊓ Submodule.span (ZMod 2) {x0} = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    obtain ⟨hyW, hyS⟩ := Submodule.mem_inf.1 hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hyS
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) a with h | h
    · rw [h, zero_smul]
    · rw [h, one_smul] at hyW
      exact (hx0 hyW).elim
  have h := Submodule.finrank_sup_add_finrank_inf_eq W (Submodule.span (ZMod 2) {x0})
  rw [hinf, finrank_bot, finrank_span_singleton hne] at h
  omega

theorem f3_ql {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]
    (g : I ≃ₗ[ZMod 2] I) (hg3 : ∀ x, g (g (g x)) = x) {V W : Submodule (ZMod 2) I}
    (hV : ∀ x ∈ V, g x ∈ V) (hW : ∀ x ∈ W, g x ∈ W) (hWV : W ≤ V)
    (hd : Module.finrank (ZMod 2) V = Module.finrank (ZMod 2) W + 1) :
    ∀ x ∈ V, g x - x ∈ W := by
  have hlt : W < V := by
    refine lt_of_le_of_ne hWV fun h => ?_
    rw [h] at hd
    omega
  obtain ⟨x0, hx0V, hx0W⟩ := SetLike.exists_of_lt hlt
  have hS : W ⊔ Submodule.span (ZMod 2) {x0} = V := by
    apply Submodule.eq_of_le_of_finrank_eq
    · exact sup_le hWV ((Submodule.span_singleton_le_iff_mem x0 V).2 hx0V)
    · rw [f3_finrank_sup hx0W, hd]
  have hdec : ∀ x ∈ V, ∃ w ∈ W, ∃ a : ZMod 2, x = w + a • x0 := by
    intro x hx
    rw [← hS] at hx
    obtain ⟨w, hw, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    exact ⟨w, hw, a, rfl⟩
  have hz : g x0 - x0 ∈ W := by
    obtain ⟨w, hw, a, ha⟩ := hdec (g x0 - x0) (V.sub_mem (hV x0 hx0V) hx0V)
    rcases (by decide : ∀ c : ZMod 2, c = 0 ∨ c = 1) a with h | h
    · rw [h, zero_smul, add_zero] at ha
      rw [ha]
      exact hw
    · exfalso
      rw [h, one_smul] at ha
      have hgx0 : g x0 = w := by
        calc g x0 = (g x0 - x0) + x0 := by abel
          _ = (w + x0) + x0 := by rw [ha]
          _ = w + (x0 + x0) := by abel
          _ = w := by rw [add_self_eq_zero_zmod2, add_zero]
      have h1 : g x0 ∈ W := by rw [hgx0]; exact hw
      have h2 : g (g x0) ∈ W := hW _ h1
      have h3 : g (g (g x0)) ∈ W := hW _ h2
      rw [hg3 x0] at h3
      exact hx0W h3
  intro x hx
  obtain ⟨y, hy, a, rfl⟩ := hdec x hx
  have e : g (y + a • x0) - (y + a • x0) = (g y - y) + a • (g x0 - x0) := by
    simp only [map_add, LinearEquiv.map_smul, smul_sub]
    abel
  rw [e]
  exact W.add_mem (W.sub_mem (hW y hy) hy) (W.smul_mem a hz)

theorem f3_fixed_flag {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]
    {p ℓ : Submodule (ZMod 2) I} (hp : Module.finrank (ZMod 2) p = 1)
    (hℓ : Module.finrank (ZMod 2) ℓ = 2) (hpℓ : p ≤ ℓ) (g : I ≃ₗ[ZMod 2] I)
    (hg3 : ∀ x, g (g (g x)) = x) (hgp : g ∈ stabS p) (hgℓ : g ∈ stabS ℓ) :
    ∀ v ∈ ℓ, g v = v := by
  have hfixp := f3_fix1 g hp (fun x hx => (hgp x).1 hx)
  intro v hv
  have hq := f3_ql g hg3 (fun x hx => (hgℓ x).1 hx) (fun x hx => (hgp x).1 hx) hpℓ (by omega)
  refine f3_chain g hg3 v p ⊥ (hq v hv) ?_ ?_
  · intro y hy
    rw [hfixp y hy, sub_self]
    exact Submodule.zero_mem _
  · intro z hz
    rw [(Submodule.mem_bot (ZMod 2)).1 hz, map_zero]

theorem f3_false_of_id {I : Type} [AddCommGroup I] [Module (ZMod 2) I] (g : I ≃ₗ[ZMod 2] I)
    (hid : ∀ x, g x = x) (hord : orderOf g = 3) : False := by
  have h1 : g = 1 := LinearEquiv.ext hid
  rw [h1, orderOf_one] at hord
  exact absurd hord (by norm_num)

theorem f3_not_mem {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]
    (hI : Module.finrank (ZMod 2) I = 4) {ℓ : Submodule (ZMod 2) I}
    (hℓ : Module.finrank (ZMod 2) ℓ = 2) (g : I ≃ₗ[ZMod 2] I) (hg3 : ∀ x, g (g (g x)) = x)
    (hgℓ : g ∈ stabS ℓ) (hfix : ∀ v ∈ ℓ, g v = v) (hord : orderOf g = 3) (v : I)
    (hv : g v - v ∈ ℓ) : v ∈ ℓ := by
  by_contra hvℓ
  have hfinW := f3_finrank_sup (W := ℓ) (x0 := v) hvℓ
  have hWfwd : ∀ x ∈ ℓ ⊔ Submodule.span (ZMod 2) {v}, g x ∈ ℓ ⊔ Submodule.span (ZMod 2) {v} := by
    intro x hx
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 hz
    have e : g (y + a • v) = (g y + a • (g v - v)) + a • v := by
      simp only [map_add, LinearEquiv.map_smul, smul_sub]
      abel
    rw [e]
    exact Submodule.add_mem_sup (ℓ.add_mem ((hgℓ y).1 hy) (ℓ.smul_mem a hv))
      (Submodule.smul_mem _ a (Submodule.mem_span_singleton_self v))
  have hall : ∀ x : I, g x = x := by
    intro x
    refine f3_chain g hg3 x (ℓ ⊔ Submodule.span (ZMod 2) {v}) ℓ ?_ ?_ hfix
    · refine f3_ql g hg3 (V := ⊤) (W := ℓ ⊔ Submodule.span (ZMod 2) {v})
        (fun _ _ => Submodule.mem_top) hWfwd le_top ?_ x Submodule.mem_top
      rw [finrank_top]
      omega
    · intro y hy
      exact f3_ql g hg3 (V := ℓ ⊔ Submodule.span (ZMod 2) {v}) (W := ℓ) hWfwd
        (fun x hx => (hgℓ x).1 hx) le_sup_left (by omega) y hy
  exact f3_false_of_id g hall hord

theorem f3_d0p {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]
    (hI : Module.finrank (ZMod 2) I = 4) {p ℓ : Submodule (ZMod 2) I}
    (hp : Module.finrank (ZMod 2) p = 1) (hℓ : Module.finrank (ZMod 2) ℓ = 2) (hpℓ : p ≤ ℓ)
    (g : I ≃ₗ[ZMod 2] I) (hg3 : ∀ x, g (g (g x)) = x) (hord : orderOf g = 3)
    (hgp : g ∈ stabS p) (hgℓ : g ∈ stabS ℓ) (d : I ≃ₗ[ZMod 2] I) (hd : d ∈ D0p p ℓ)
    (hcomm : g * d * g⁻¹ = d) : d = 1 := by
  obtain ⟨hdℓ, hdp⟩ := (mem_D0p_iff hpℓ d).1 hd
  have hA1 := f3_fixed_flag hp hℓ hpℓ g hg3 hgp hgℓ
  have hfixp := f3_fix1 g hp (fun x hx => (hgp x).1 hx)
  have hgd : g * d = d * g := by
    have h := congrArg (· * g) hcomm
    simpa using h
  have hpt : ∀ x, g (d x) = d (g x) := fun x => congrArg (fun k : I ≃ₗ[ZMod 2] I => k x) hgd
  by_contra hne
  obtain ⟨M, hMdef⟩ : ∃ M : I →ₗ[ZMod 2] I, M = (d : I →ₗ[ZMod 2] I) - LinearMap.id := ⟨_, rfl⟩
  have hMx : ∀ x, M x = d x - x := fun x => by rw [hMdef]; rfl
  have hMp : ∀ x, M x ∈ p := fun x => by rw [hMx]; exact hdp x
  have hMℓ : ∀ v ∈ ℓ, M v = 0 := fun v hv => by rw [hMx, hdℓ v hv, sub_self]
  have hMg : ∀ x, M (g x) = g (M x) := by
    intro x
    rw [hMx, hMx, map_sub, hpt x]
  have hex : ∃ x0, M x0 ≠ 0 := by
    by_contra hcon
    apply hne
    apply LinearEquiv.ext
    intro x
    have h : d x - x = 0 := by
      rw [← hMx]
      by_contra h'
      exact hcon ⟨x, h'⟩
    exact sub_eq_zero.1 h
  obtain ⟨x0, hx0⟩ := hex
  have hRle : LinearMap.range M ≤ p := by
    rintro _ ⟨x, rfl⟩
    exact hMp x
  have hRne : LinearMap.range M ≠ ⊥ := by
    intro h
    apply hx0
    have hmem : M x0 ∈ LinearMap.range M := LinearMap.mem_range_self M x0
    rw [h] at hmem
    exact (Submodule.mem_bot (ZMod 2)).1 hmem
  have hR1 : Module.finrank (ZMod 2) (LinearMap.range M) = 1 := by
    have h1 := Submodule.finrank_mono hRle
    have h0 : Module.finrank (ZMod 2) (LinearMap.range M) ≠ 0 :=
      fun h => hRne (Submodule.finrank_eq_zero.1 h)
    omega
  have hrk := LinearMap.finrank_range_add_finrank_ker M
  have hV : ∀ x ∈ LinearMap.ker M, g x ∈ LinearMap.ker M := by
    intro x hx
    rw [LinearMap.mem_ker] at hx ⊢
    rw [hMg, hx, map_zero]
  have hWV : ℓ ≤ LinearMap.ker M := fun v hv => LinearMap.mem_ker.2 (hMℓ v hv)
  have hQL := f3_ql g hg3 hV (fun x hx => (hgℓ x).1 hx) hWV (by omega)
  have hid : ∀ x, g x = x := by
    intro x
    refine f3_chain g hg3 x (LinearMap.ker M) ℓ ?_ hQL hA1
    rw [LinearMap.mem_ker, map_sub, hMg, hfixp (M x) (hMp x), sub_self]
  exact f3_false_of_id g hid hord

theorem f3_d0P {I : Type} [AddCommGroup I] [Module (ZMod 2) I] [FiniteDimensional (ZMod 2) I]
    (hI : Module.finrank (ZMod 2) I = 4) {ℓ Pl : Submodule (ZMod 2) I}
    (hℓ : Module.finrank (ZMod 2) ℓ = 2) (hPl : Module.finrank (ZMod 2) Pl = 3) (hℓPl : ℓ ≤ Pl)
    (g : I ≃ₗ[ZMod 2] I) (hg3 : ∀ x, g (g (g x)) = x) (hord : orderOf g = 3)
    (hgℓ : g ∈ stabS ℓ) (hgPl : g ∈ stabS Pl) (d : I ≃ₗ[ZMod 2] I) (hd : d ∈ D0P ℓ Pl)
    (hcomm : g * d * g⁻¹ = d) : d = 1 := by
  obtain ⟨hdPl, hdℓ⟩ := (mem_D0P_iff hℓPl d).1 hd
  have hgd : g * d = d * g := by
    have h := congrArg (· * g) hcomm
    simpa using h
  have hpt : ∀ x, g (d x) = d (g x) := fun x => congrArg (fun k : I ≃ₗ[ZMod 2] I => k x) hgd
  by_contra hne
  obtain ⟨M, hMdef⟩ : ∃ M : I →ₗ[ZMod 2] I, M = (d : I →ₗ[ZMod 2] I) - LinearMap.id := ⟨_, rfl⟩
  have hMx : ∀ x, M x = d x - x := fun x => by rw [hMdef]; rfl
  have hMℓ : ∀ x, M x ∈ ℓ := fun x => by rw [hMx]; exact hdℓ x
  have hMPl : ∀ v ∈ Pl, M v = 0 := fun v hv => by rw [hMx, hdPl v hv, sub_self]
  have hMg : ∀ x, M (g x) = g (M x) := by
    intro x
    rw [hMx, hMx, map_sub, hpt x]
  have hex : ∃ x0, M x0 ≠ 0 := by
    by_contra hcon
    apply hne
    apply LinearEquiv.ext
    intro x
    have h : d x - x = 0 := by
      rw [← hMx]
      by_contra h'
      exact hcon ⟨x, h'⟩
    exact sub_eq_zero.1 h
  obtain ⟨x0, hx0⟩ := hex
  have hPlker : Pl ≤ LinearMap.ker M := fun v hv => LinearMap.mem_ker.2 (hMPl v hv)
  have hkerne : LinearMap.ker M ≠ ⊤ := by
    intro h
    apply hx0
    have hmem : x0 ∈ LinearMap.ker M := by rw [h]; exact Submodule.mem_top
    exact LinearMap.mem_ker.1 hmem
  have hk3 : Module.finrank (ZMod 2) (LinearMap.ker M) = 3 := by
    have hlow := Submodule.finrank_mono hPlker
    have hle := Submodule.finrank_le (LinearMap.ker M)
    have hne4 : Module.finrank (ZMod 2) (LinearMap.ker M) ≠ 4 := by
      intro h4
      exact hkerne (Submodule.eq_top_of_finrank_eq (by rw [h4, hI]))
    omega
  have hrk := LinearMap.finrank_range_add_finrank_ker M
  have hR1 : Module.finrank (ZMod 2) (LinearMap.range M) = 1 := by omega
  have hRℓ : LinearMap.range M ≤ ℓ := by
    rintro _ ⟨x, rfl⟩
    exact hMℓ x
  have hRfwd : ∀ x ∈ LinearMap.range M, g x ∈ LinearMap.range M := by
    rintro _ ⟨y, rfl⟩
    exact ⟨g y, hMg y⟩
  have hfixR := f3_fix1 g hR1 hRfwd
  have hA1 : ∀ z ∈ ℓ, g z = z := by
    intro z hz
    refine f3_chain g hg3 z (LinearMap.range M) ⊥ ?_ ?_ ?_
    · exact f3_ql g hg3 (fun x hx => (hgℓ x).1 hx) hRfwd hRℓ (by omega) z hz
    · intro y hy
      rw [hfixR y hy, sub_self]
      exact Submodule.zero_mem _
    · intro w hw
      rw [(Submodule.mem_bot (ZMod 2)).1 hw, map_zero]
  have hid : ∀ x, g x = x := by
    intro x
    refine f3_chain g hg3 x Pl ℓ ?_ ?_ hA1
    · exact f3_ql g hg3 (V := ⊤) (W := Pl) (fun _ _ => Submodule.mem_top)
        (fun x hx => (hgPl x).1 hx) le_top (by rw [finrank_top]; omega) x Submodule.mem_top
    · intro y hy
      exact f3_ql g hg3 (V := Pl) (W := ℓ) (fun x hx => (hgPl x).1 hx)
        (fun x hx => (hgℓ x).1 hx) hℓPl (by omega) y hy
  exact f3_false_of_id g hid hord

theorem factF3_holds : FactF3 := by
  unfold FactF3
  intro I _ _ _ hI p ℓ Pl hp hℓ hPl hpℓ hℓPl g hg
  have h3 : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  rw [hg, pow_three] at h3
  have hg3 : ∀ x, g (g (g x)) = x := fun x =>
    congrArg (fun k : I ≃ₗ[ZMod 2] I => k x) h3
  refine ⟨fun hgp hgℓ => ⟨f3_fixed_flag hp hℓ hpℓ.le g hg3 hgp hgℓ,
      fun v hv => f3_not_mem hI hℓ g hg3 hgℓ (f3_fixed_flag hp hℓ hpℓ.le g hg3 hgp hgℓ) hg v hv,
      fun d hd hcomm => f3_d0p hI hp hℓ hpℓ.le g hg3 hg hgp hgℓ d hd hcomm⟩,
    fun hgℓ hgPl => fun d hd hcomm => f3_d0P hI hℓ hPl hℓPl.le g hg3 hg hgℓ hgPl d hd hcomm⟩

end CFSG.Quasithin.H13.C1294
