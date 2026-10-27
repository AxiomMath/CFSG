module

public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneNinePair
public import CFSG.Quasithin.Background.SimsG4OrthUPrim

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]
  {H : Subgroup (U ≃ₗ[ZMod p] U)} {τ : ZMod p}

def conjSet (H : Subgroup (U ≃ₗ[ZMod p] U)) (g : U ≃ₗ[ZMod p] U) :
    Set (U ≃ₗ[ZMod p] U) :=
  {x | ∃ h : H, x = (h : U ≃ₗ[ZMod p] U) * g * (h : U ≃ₗ[ZMod p] U)⁻¹}

private lemma conjSet_conj_mem {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {h : H} {n : U ≃ₗ[ZMod p] U} (hn : n ∈ Subgroup.closure (conjSet H g)) :
    (h : U ≃ₗ[ZMod p] U) * n * (h : U ≃ₗ[ZMod p] U)⁻¹ ∈ Subgroup.closure (conjSet H g) := by
  refine Subgroup.closure_induction (p := fun n _ =>
    (h : U ≃ₗ[ZMod p] U) * n * (h : U ≃ₗ[ZMod p] U)⁻¹ ∈ Subgroup.closure (conjSet H g))
    ?_ ?_ ?_ ?_ hn
  · rintro x ⟨k, rfl⟩
    refine Subgroup.subset_closure ⟨h * k, ?_⟩
    simp only [Subgroup.coe_mul]
    group
  · simp
  · intro x y hx hy hx' hy'
    convert (Subgroup.closure (conjSet H g)).mul_mem hx' hy' using 1
    group
  · intro x hx hx'
    convert (Subgroup.closure (conjSet H g)).inv_mem hx' using 1
    group

private lemma conjSet_mapsInto [Module.Finite (ZMod p) U] {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {g : U ≃ₗ[ZMod p] U} {W : Submodule (ZMod p) U}
    (hW : ∀ h ∈ H, ∀ w ∈ W, (h * g * h⁻¹) w ∈ W) {n : U ≃ₗ[ZMod p] U}
    (hn : n ∈ Subgroup.closure (conjSet H g)) : ∀ w ∈ W, n w ∈ W := by
  refine Subgroup.closure_induction (p := fun n _ => ∀ w ∈ W, n w ∈ W) ?_ ?_ ?_ ?_ hn
  · rintro x ⟨h, rfl⟩ w hw
    exact hW h h.2 w hw
  · intro w hw; simpa using hw
  · intro x y hx hy hx' hy' w hw
    rw [LinearEquiv.mul_apply]
    exact hx' _ (hy' w hw)
  · intro x hx hx' w hw
    have hle : W.map (x : U →ₗ[ZMod p] U) ≤ W := by
      rintro _ ⟨w', hw', rfl⟩
      exact hx' w' hw'
    have hfr : Module.finrank (ZMod p) ↥(W.map (x : U →ₗ[ZMod p] U)) =
        Module.finrank (ZMod p) ↥W := LinearEquiv.finrank_map_eq x W
    have heq : W.map (x : U →ₗ[ZMod p] U) = W :=
      Submodule.eq_of_le_of_finrank_eq hle hfr
    have hmem : w ∈ W.map (x : U →ₗ[ZMod p] U) := heq.symm ▸ hw
    obtain ⟨w', hw', hw'w⟩ := Submodule.mem_map.mp hmem
    rw [← hw'w]
    simpa using hw'

private lemma conjSet_fixSpace_eq_bot [Module.Finite (ZMod p) U] {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {g : U ≃ₗ[ZMod p] U} {c : U} {φ : Module.Dual (ZMod p) U} {τ : ZMod p}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1) :
    (⨅ n : Subgroup.closure (conjSet H g), LinearMap.ker
      (((n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1)) = ⊥ := by
  classical
  let N := Subgroup.closure (conjSet H g)
  let FixN : Submodule (ZMod p) U :=
    ⨅ n : N, LinearMap.ker (((n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1)
  have mem_FixN : ∀ v : U, v ∈ FixN ↔ ∀ n : N, (n : U ≃ₗ[ZMod p] U) v = v := by
    intro v
    simp only [FixN, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    exact forall_congr' fun n => by simp
  have hFixH : ∀ h ∈ H, ∀ v ∈ FixN, h v ∈ FixN := by
    intro h hh v hv
    rw [mem_FixN] at hv ⊢
    intro n
    have hm : h⁻¹ * (n : U ≃ₗ[ZMod p] U) * h ∈ N :=
      conjSet_conj_mem (H := H) (g := g) (h := ⟨h, hh⟩⁻¹) (by exact n.2)
    have hv' : (h⁻¹ * (n : U ≃ₗ[ZMod p] U) * h) v = v := by
      simpa using hv ⟨_, hm⟩
    have := congrArg h hv'
    simpa [mul_apply] using this
  have hcFix : c ∉ FixN := by
    rw [mem_FixN]
    push Not
    refine ⟨⟨g, Subgroup.subset_closure ⟨1, by simp⟩⟩, ?_⟩
    intro hgc
    have hgc' : g c = τ • c := hh.apply_centre
    have hzero : (τ - 1) • c = 0 := by
      rw [sub_smul, one_smul, ← hgc', hgc, sub_self]
    have hc0 : c ≠ 0 := hh.centre_ne_zero hτ
    rcases smul_eq_zero.mp hzero with h | h
    · exact hτ (sub_eq_zero.mp h)
    · exact hc0 h
  have hFix_bot : FixN = ⊥ := by
    rcases hirr FixN hFixH with h | h
    · exact h
    · exact absurd (h ▸ Submodule.mem_top) hcFix
  simpa only [N, FixN] using hFix_bot

private lemma exists_minimal_invariant [Module.Finite (ZMod p) U] {N : Subgroup (U ≃ₗ[ZMod p] U)}
    {W : Submodule (ZMod p) U} (hW0 : W ≠ ⊥) (hWN : ∀ n ∈ N, ∀ w ∈ W, n w ∈ W) :
    ∃ U₀ : Submodule (ZMod p) U, U₀ ≤ W ∧ U₀ ≠ ⊥ ∧ (∀ n ∈ N, ∀ v ∈ U₀, n v ∈ U₀) ∧
      ∀ V : Submodule (ZMod p) U, V ≤ U₀ → V ≠ ⊥ → (∀ n ∈ N, ∀ v ∈ V, n v ∈ V) → V = U₀ := by
  classical
  have hex : ∃ d, ∃ V : Submodule (ZMod p) U, V ≤ W ∧ V ≠ ⊥ ∧
      (∀ n ∈ N, ∀ v ∈ V, n v ∈ V) ∧ Module.finrank (ZMod p) ↥V = d :=
    ⟨_, W, le_rfl, hW0, hWN, rfl⟩
  obtain ⟨U₀, hU₀W, hU₀0, hU₀inv, hU₀d⟩ := Nat.find_spec hex
  refine ⟨U₀, hU₀W, hU₀0, hU₀inv, fun V hVU₀ hV0 hVinv => ?_⟩
  have hVd : Nat.find hex ≤ Module.finrank (ZMod p) ↥V :=
    Nat.find_min' hex ⟨V, hVU₀.trans hU₀W, hV0, hVinv, rfl⟩
  have hle : Module.finrank (ZMod p) ↥V ≤ Module.finrank (ZMod p) ↥U₀ :=
    Submodule.finrank_mono hVU₀
  exact Submodule.eq_of_le_of_finrank_eq hVU₀ (le_antisymm hle (by rw [hU₀d]; exact hVd))


private noncomputable def translateFamily (H : Subgroup (U ≃ₗ[ZMod p] U))
    (U₀ : Submodule (ZMod p) U) : Set (Submodule (ZMod p) U) :=
  Set.range (fun h : H => U₀.map (h : U →ₗ[ZMod p] U))

private lemma translate_ne_bot {H : Subgroup (U ≃ₗ[ZMod p] U)} {U₀ : Submodule (ZMod p) U}
    (hU₀0 : U₀ ≠ ⊥) (h : H) : U₀.map (h : U →ₗ[ZMod p] U) ≠ ⊥ := by
  intro hbot
  exact hU₀0 ((Submodule.map_eq_bot_iff (e := (h : U ≃ₗ[ZMod p] U))).mp hbot)

private lemma translate_ne_bot' {H : Subgroup (U ≃ₗ[ZMod p] U)} {U₀ : Submodule (ZMod p) U}
    (hU₀0 : U₀ ≠ ⊥) (i : translateFamily H U₀) : (i : Submodule (ZMod p) U) ≠ ⊥ := by
  have hspec : U₀.map ((Classical.choose i.2 : H) : U →ₗ[ZMod p] U) =
      (i : Submodule (ZMod p) U) := Classical.choose_spec i.2
  rw [← hspec]
  exact translate_ne_bot hU₀0 (Classical.choose i.2)

private lemma translate_inv {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {N : Subgroup (U ≃ₗ[ZMod p] U)} (hN : N = Subgroup.closure (conjSet H g))
    {U₀ : Submodule (ZMod p) U} (hU₀inv : ∀ n ∈ N, ∀ v ∈ U₀, n v ∈ U₀) (h : H) :
    ∀ n ∈ N, ∀ v ∈ U₀.map (h : U →ₗ[ZMod p] U), n v ∈ U₀.map (h : U →ₗ[ZMod p] U) := by
  intro n hn v hv
  rw [Submodule.mem_map] at hv ⊢
  obtain ⟨u, hu, rfl⟩ := hv
  have hm : (h : U ≃ₗ[ZMod p] U)⁻¹ * n * (h : U ≃ₗ[ZMod p] U) ∈ N :=
    hN.symm ▸ conjSet_conj_mem (H := H) (g := g) (h := h⁻¹) (hN ▸ hn)
  refine ⟨((h : U ≃ₗ[ZMod p] U)⁻¹ * n * (h : U ≃ₗ[ZMod p] U)) u, hU₀inv _ hm u hu, ?_⟩
  simp

private lemma translate_inv' {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {N : Subgroup (U ≃ₗ[ZMod p] U)} (hN : N = Subgroup.closure (conjSet H g))
    {U₀ : Submodule (ZMod p) U} (hU₀inv : ∀ n ∈ N, ∀ v ∈ U₀, n v ∈ U₀)
    (i : translateFamily H U₀) :
    ∀ n ∈ N, ∀ v ∈ (i : Submodule (ZMod p) U), n v ∈ (i : Submodule (ZMod p) U) := by
  have hspec : U₀.map ((Classical.choose i.2 : H) : U →ₗ[ZMod p] U) =
      (i : Submodule (ZMod p) U) := Classical.choose_spec i.2
  have h := translate_inv hN hU₀inv (Classical.choose i.2)
  rwa [hspec] at h

private lemma translate_minimal [Module.Finite (ZMod p) U] {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {g : U ≃ₗ[ZMod p] U} {N : Subgroup (U ≃ₗ[ZMod p] U)}
    (hN : N = Subgroup.closure (conjSet H g)) {U₀ : Submodule (ZMod p) U}
    (hU₀min : ∀ V : Submodule (ZMod p) U, V ≤ U₀ → V ≠ ⊥ →
      (∀ n ∈ N, ∀ v ∈ V, n v ∈ V) → V = U₀)
    (h : H) {V : Submodule (ZMod p) U} (hV : V ≤ U₀.map (h : U →ₗ[ZMod p] U)) (hV0 : V ≠ ⊥)
    (hVinv : ∀ n ∈ N, ∀ v ∈ V, n v ∈ V) : V = U₀.map (h : U →ₗ[ZMod p] U) := by
  let hi : U ≃ₗ[ZMod p] U := (h : U ≃ₗ[ZMod p] U)⁻¹
  have hV'U₀ : V.map (hi : U →ₗ[ZMod p] U) ≤ U₀ := by
    intro x hx
    rw [Submodule.mem_map] at hx
    obtain ⟨v, hv, rfl⟩ := hx
    have hvT : v ∈ U₀.map (h : U →ₗ[ZMod p] U) := hV hv
    rw [Submodule.mem_map] at hvT
    obtain ⟨u, hu, rfl⟩ := hvT
    simpa [hi] using hu
  have hV'inv : ∀ n ∈ N, ∀ v ∈ V.map (hi : U →ₗ[ZMod p] U),
      n v ∈ V.map (hi : U →ₗ[ZMod p] U) := by
    intro n hn v hv
    rw [Submodule.mem_map] at hv ⊢
    obtain ⟨w, hw, rfl⟩ := hv
    have hm : (h : U ≃ₗ[ZMod p] U) * n * (h : U ≃ₗ[ZMod p] U)⁻¹ ∈ N :=
      hN.symm ▸ conjSet_conj_mem (H := H) (g := g) (h := h) (hN ▸ hn)
    refine ⟨((h : U ≃ₗ[ZMod p] U) * n * (h : U ≃ₗ[ZMod p] U)⁻¹) w, hVinv _ hm w hw, ?_⟩
    simp [hi]
  have hV'0 : V.map (hi : U →ₗ[ZMod p] U) ≠ ⊥ := by
    intro hbot
    exact hV0 ((Submodule.map_eq_bot_iff (e := hi)).mp hbot)
  have hV'eq : V.map (hi : U →ₗ[ZMod p] U) = U₀ := hU₀min _ hV'U₀ hV'0 hV'inv
  have hmap : (V.map (hi : U →ₗ[ZMod p] U)).map (h : U →ₗ[ZMod p] U) = V := by
    rw [← Submodule.map_comp]
    have : (h : U →ₗ[ZMod p] U) ∘ₗ (hi : U →ₗ[ZMod p] U) = LinearMap.id := by
      ext x; simp [hi]
    rw [this, Submodule.map_id]
  rw [hV'eq] at hmap
  exact hmap.symm

private lemma translate_minimal' [Module.Finite (ZMod p) U] {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {g : U ≃ₗ[ZMod p] U} {N : Subgroup (U ≃ₗ[ZMod p] U)}
    (hN : N = Subgroup.closure (conjSet H g)) {U₀ : Submodule (ZMod p) U}
    (hU₀min : ∀ V : Submodule (ZMod p) U, V ≤ U₀ → V ≠ ⊥ →
      (∀ n ∈ N, ∀ v ∈ V, n v ∈ V) → V = U₀)
    (i : translateFamily H U₀) {V : Submodule (ZMod p) U}
    (hV : V ≤ (i : Submodule (ZMod p) U)) (hV0 : V ≠ ⊥)
    (hVinv : ∀ n ∈ N, ∀ v ∈ V, n v ∈ V) : V = (i : Submodule (ZMod p) U) := by
  have hspec : U₀.map ((Classical.choose i.2 : H) : U →ₗ[ZMod p] U) =
      (i : Submodule (ZMod p) U) := Classical.choose_spec i.2
  have h := translate_minimal hN hU₀min (Classical.choose i.2) (by
    rw [hspec]; exact hV) hV0 hVinv
  rwa [hspec] at h

private lemma translate_pair_disjoint [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U} {N : Subgroup (U ≃ₗ[ZMod p] U)}
    (hN : N = Subgroup.closure (conjSet H g)) {U₀ : Submodule (ZMod p) U}
    (hU₀0 : U₀ ≠ ⊥) (hU₀inv : ∀ n ∈ N, ∀ v ∈ U₀, n v ∈ U₀)
    (hU₀min : ∀ V : Submodule (ZMod p) U, V ≤ U₀ → V ≠ ⊥ →
      (∀ n ∈ N, ∀ v ∈ V, n v ∈ V) → V = U₀)
    {i j : translateFamily H U₀} (hij : i ≠ j) :
    (i : Submodule (ZMod p) U) ⊓ (j : Submodule (ZMod p) U) = ⊥ := by
  rcases i with ⟨Vi, ⟨hi, rfl⟩⟩
  rcases j with ⟨Vj, ⟨hj, rfl⟩⟩
  by_contra hne
  have hinv : ∀ n ∈ N, ∀ v ∈ (U₀.map (hi : U →ₗ[ZMod p] U)) ⊓ (U₀.map (hj : U →ₗ[ZMod p] U)),
      n v ∈ (U₀.map (hi : U →ₗ[ZMod p] U)) ⊓ (U₀.map (hj : U →ₗ[ZMod p] U)) := by
    intro n hn v hv
    rw [Submodule.mem_inf] at hv ⊢
    exact ⟨translate_inv hN hU₀inv hi n hn v hv.1, translate_inv hN hU₀inv hj n hn v hv.2⟩
  have hEq : (U₀.map (hi : U →ₗ[ZMod p] U)) ⊓ (U₀.map (hj : U →ₗ[ZMod p] U)) =
      U₀.map (hi : U →ₗ[ZMod p] U) :=
    translate_minimal hN hU₀min hi inf_le_left hne hinv
  have hleji : U₀.map (hi : U →ₗ[ZMod p] U) ≤ U₀.map (hj : U →ₗ[ZMod p] U) := hEq ▸ inf_le_right
  have hEq2 : U₀.map (hi : U →ₗ[ZMod p] U) = U₀.map (hj : U →ₗ[ZMod p] U) :=
    translate_minimal hN hU₀min hj hleji (translate_ne_bot hU₀0 hi) (translate_inv hN hU₀inv hi)
  exact hij (Subtype.ext hEq2)

private lemma translate_exists_conj_act_ne [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U} {N : Subgroup (U ≃ₗ[ZMod p] U)}
    (hN : N = Subgroup.closure (conjSet H g)) {U₀ : Submodule (ZMod p) U} (hU₀0 : U₀ ≠ ⊥)
    (hFix : (⨅ n : N, LinearMap.ker (((n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1)) = ⊥)
    (i : translateFamily H U₀) :
    ∃ h : H, ∃ v ∈ (i : Submodule (ZMod p) U),
      ((h : U ≃ₗ[ZMod p] U) * g * (h : U ≃ₗ[ZMod p] U)⁻¹) v ≠ v := by
  by_contra hc
  push Not at hc
  have hNfix : ∀ n ∈ N, ∀ v ∈ (i : Submodule (ZMod p) U), n v = v := by
    intro n hn
    refine Subgroup.closure_induction (p := fun n _ => ∀ v ∈ (i : Submodule (ZMod p) U), n v = v)
      ?_ ?_ ?_ ?_ (hN ▸ hn)
    · rintro x ⟨k, rfl⟩ v hv
      exact hc k v hv
    · intro v hv; rfl
    · intro x y hx hy hx' hy' v hv
      rw [LinearEquiv.mul_apply, hy' v hv, hx' v hv]
    · intro x hx hx' v hv
      have := congrArg (x⁻¹ : U ≃ₗ[ZMod p] U) (hx' v hv)
      simpa using this.symm
  have hle : (i : Submodule (ZMod p) U) ≤
      (⨅ n : N, LinearMap.ker (((n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1)) := by
    intro v hv
    rw [Submodule.mem_iInf]
    intro n
    rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
    simpa using hNfix n n.2 v hv
  rw [hFix] at hle
  exact translate_ne_bot' hU₀0 i (le_bot_iff.mp hle)

private lemma translate_conj_centre_mem [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U} {c : U}
    {φ : Module.Dual (ZMod p) U} {τ : ZMod p} (hh : IsHomologyWith τ g c φ)
    {N : Subgroup (U ≃ₗ[ZMod p] U)} (hN : N = Subgroup.closure (conjSet H g))
    {U₀ : Submodule (ZMod p) U} (hU₀inv : ∀ n ∈ N, ∀ v ∈ U₀, n v ∈ U₀)
    (i : translateFamily H U₀) {h₀ : H} {v : U} (hv : v ∈ (i : Submodule (ZMod p) U))
    (hvne : ((h₀ : U ≃ₗ[ZMod p] U) * g * (h₀ : U ≃ₗ[ZMod p] U)⁻¹) v ≠ v) :
    (h₀ : U ≃ₗ[ZMod p] U) c ∈ (i : Submodule (ZMod p) U) := by
  let k : U ≃ₗ[ZMod p] U := h₀
  let kinv : U ≃ₗ[ZMod p] U := k⁻¹
  let γ : U ≃ₗ[ZMod p] U := k * g * k⁻¹
  let cγ : U := k c
  let φγ : Module.Dual (ZMod p) U := φ ∘ₗ (kinv : U →ₗ[ZMod p] U)
  have hγS : γ ∈ N := hN.symm ▸ Subgroup.subset_closure ⟨h₀, rfl⟩
  have hγh : IsHomologyWith τ γ cγ φγ := hh.conj k
  have hγvne : γ v ≠ v := hvne
  have hφv : φγ v ≠ 0 := by
    intro h0
    apply hγvne
    have := hγh.2 v
    rw [this, h0, zero_smul, add_zero]
  have hγv : γ v ∈ (i : Submodule (ZMod p) U) := translate_inv' hN hU₀inv i γ hγS v hv
  have hdiff : γ v - v ∈ (i : Submodule (ZMod p) U) :=
    ((i : Submodule (ZMod p) U)).sub_mem hγv hv
  have happ : γ v - v = φγ v • cγ := by
    have := hγh.2 v
    rw [this]; abel
  rw [happ] at hdiff
  have := ((i : Submodule (ZMod p) U)).smul_mem (φγ v)⁻¹ hdiff
  rwa [smul_smul, inv_mul_cancel₀ hφv, one_smul] at this

private lemma translate_conj_orthogonal [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U} {N : Subgroup (U ≃ₗ[ZMod p] U)}
    (hN : N = Subgroup.closure (conjSet H g)) {U₀ : Submodule (ZMod p) U}
    (hU₀0 : U₀ ≠ ⊥) (hU₀inv : ∀ n ∈ N, ∀ v ∈ U₀, n v ∈ U₀)
    (hU₀min : ∀ V : Submodule (ZMod p) U, V ≤ U₀ → V ≠ ⊥ →
      (∀ n ∈ N, ∀ v ∈ V, n v ∈ V) → V = U₀)
    {i : translateFamily H U₀} {γ : U ≃ₗ[ZMod p] U} (hγS : γ ∈ N) {cγ : U}
    (hcγ : cγ ∈ (i : Submodule (ZMod p) U)) (hcγ0 : cγ ≠ 0)
    {φγ : Module.Dual (ZMod p) U} (hγ2 : ∀ v, γ v = v + φγ v • cγ) :
    (∀ j : translateFamily H U₀, j ≠ i → cγ ∉ (j : Submodule (ZMod p) U)) ∧
    (∀ j : translateFamily H U₀, j ≠ i → (j : Submodule (ZMod p) U) ≤ LinearMap.ker φγ) := by
  have hcγj : ∀ j : translateFamily H U₀, j ≠ i → cγ ∉ (j : Submodule (ZMod p) U) := by
    intro j hji hmem
    have : cγ ∈ (i : Submodule (ZMod p) U) ⊓ (j : Submodule (ZMod p) U) :=
      Submodule.mem_inf.mpr ⟨hcγ, hmem⟩
    rw [translate_pair_disjoint hN hU₀0 hU₀inv hU₀min (Ne.symm hji), Submodule.mem_bot] at this
    exact hcγ0 this
  refine ⟨hcγj, fun j hji v hv => ?_⟩
  rw [LinearMap.mem_ker]
  by_contra hφvj
  have hγv : γ v ∈ (j : Submodule (ZMod p) U) := translate_inv' hN hU₀inv j γ hγS v hv
  have hdiff : γ v - v ∈ (j : Submodule (ZMod p) U) :=
    ((j : Submodule (ZMod p) U)).sub_mem hγv hv
  have happ : γ v - v = φγ v • cγ := by rw [hγ2 v]; abel
  rw [happ] at hdiff
  have := ((j : Submodule (ZMod p) U)).smul_mem (φγ v)⁻¹ hdiff
  rw [smul_smul, inv_mul_cancel₀ hφvj, one_smul] at this
  exact hcγj j hji this

private lemma translate_inf_invariant [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U} {N : Subgroup (U ≃ₗ[ZMod p] U)}
    (hN : N = Subgroup.closure (conjSet H g)) {U₀ : Submodule (ZMod p) U}
    (hU₀inv : ∀ n ∈ N, ∀ v ∈ U₀, n v ∈ U₀) (i : translateFamily H U₀) :
    ∀ n ∈ N, ∀ v ∈ (i : Submodule (ZMod p) U) ⊓
      (⨆ (j) (_ : j ≠ i), (j : Submodule (ZMod p) U)),
      n v ∈ (i : Submodule (ZMod p) U) ⊓ (⨆ (j) (_ : j ≠ i), (j : Submodule (ZMod p) U)) := by
  intro n hn v hv
  rw [Submodule.mem_inf] at hv
  rw [Submodule.mem_inf]
  refine ⟨translate_inv' hN hU₀inv i n hn v hv.1, ?_⟩
  have hconv : (⨆ x : {j : translateFamily H U₀ // j ≠ i}, (x : Submodule (ZMod p) U)) =
      ⨆ (j) (_ : j ≠ i), (j : Submodule (ZMod p) U) :=
    (iSup_subtype' (f := fun j (_ : j ≠ i) => (j : Submodule (ZMod p) U))).symm
  rw [← hconv]
  have hv2 : v ∈ (⨆ x : {j : translateFamily H U₀ // j ≠ i}, (x : Submodule (ZMod p) U)) := by
    rw [hconv]; exact hv.2
  refine Submodule.iSup_induction (fun x : {j : translateFamily H U₀ // j ≠ i} =>
    (x : Submodule (ZMod p) U))
    (motive := fun x => n x ∈ (⨆ x : {j : translateFamily H U₀ // j ≠ i},
      (x : Submodule (ZMod p) U))) hv2 ?_ ?_ ?_
  · intro j x hx
    exact le_iSup (fun x : {j : translateFamily H U₀ // j ≠ i} =>
      (x : Submodule (ZMod p) U)) j (translate_inv' hN hU₀inv j.1 n hn x hx)
  · rw [map_zero]
    exact Submodule.zero_mem _
  · intro x y hx hy
    rw [map_add]
    exact Submodule.add_mem _ hx hy

private lemma translate_iSupIndep [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U} {c : U}
    {φ : Module.Dual (ZMod p) U} {τ : ZMod p} (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1)
    {N : Subgroup (U ≃ₗ[ZMod p] U)} (hN : N = Subgroup.closure (conjSet H g))
    {U₀ : Submodule (ZMod p) U} (hU₀0 : U₀ ≠ ⊥)
    (hU₀inv : ∀ n ∈ N, ∀ v ∈ U₀, n v ∈ U₀)
    (hU₀min : ∀ V : Submodule (ZMod p) U, V ≤ U₀ → V ≠ ⊥ →
      (∀ n ∈ N, ∀ v ∈ V, n v ∈ V) → V = U₀)
    (hFix : (⨅ n : N, LinearMap.ker (((n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1)) = ⊥) :
    iSupIndep (fun i : translateFamily H U₀ => (i : Submodule (ZMod p) U)) := by
  classical
  intro i
  rw [disjoint_iff_inf_le]
  obtain ⟨h₀, v, hv, hvne⟩ := translate_exists_conj_act_ne hN hU₀0 hFix i
  have hcγ : (h₀ : U ≃ₗ[ZMod p] U) c ∈ (i : Submodule (ZMod p) U) :=
    translate_conj_centre_mem hh hN hU₀inv i hv hvne
  let γ : U ≃ₗ[ZMod p] U := (h₀ : U ≃ₗ[ZMod p] U) * g * (h₀ : U ≃ₗ[ZMod p] U)⁻¹
  let cγ : U := (h₀ : U ≃ₗ[ZMod p] U) c
  let φγ : Module.Dual (ZMod p) U := φ ∘ₗ (((h₀ : U ≃ₗ[ZMod p] U)⁻¹) : U ≃ₗ[ZMod p] U)
  have hγS : γ ∈ N := hN.symm ▸ Subgroup.subset_closure ⟨h₀, rfl⟩
  have hγh : IsHomologyWith τ γ cγ φγ := hh.conj (h₀ : U ≃ₗ[ZMod p] U)
  have hcγ0 : cγ ≠ 0 := hγh.centre_ne_zero hτ
  obtain ⟨hcγj, hker⟩ :=
    translate_conj_orthogonal hN hU₀0 hU₀inv hU₀min hγS hcγ hcγ0 hγh.2
  have hsupker : (⨆ (j) (_ : j ≠ i), (j : Submodule (ZMod p) U)) ≤ LinearMap.ker φγ :=
    iSup₂_le fun j hj => hker j hj
  have hIntInv := translate_inf_invariant hN hU₀inv i
  have hIntLeKer : (i : Submodule (ZMod p) U) ⊓
      (⨆ (j) (_ : j ≠ i), (j : Submodule (ZMod p) U)) ≤ LinearMap.ker φγ :=
    le_trans inf_le_right hsupker
  have hIntNe : (i : Submodule (ZMod p) U) ⊓
      (⨆ (j) (_ : j ≠ i), (j : Submodule (ZMod p) U)) ≠ (i : Submodule (ZMod p) U) := by
    intro hEq
    have hcγS : cγ ∈ (⨆ (j) (_ : j ≠ i), (j : Submodule (ZMod p) U)) := by
      have : cγ ∈ (i : Submodule (ZMod p) U) ⊓
          (⨆ (j) (_ : j ≠ i), (j : Submodule (ZMod p) U)) := hEq.symm ▸ hcγ
      exact (Submodule.mem_inf.mp this).2
    have hφ0 : φγ cγ = 0 := LinearMap.mem_ker.mp (hsupker hcγS)
    have hφc : φ c = 0 := by simpa [φγ, cγ] using hφ0
    have : τ - 1 = 0 := by rw [← hh.1, hφc]
    exact hτ (sub_eq_zero.mp this)
  have hIntBot : (i : Submodule (ZMod p) U) ⊓
      (⨆ (j) (_ : j ≠ i), (j : Submodule (ZMod p) U)) = ⊥ := by
    by_contra hbot
    exact hIntNe (translate_minimal' hN hU₀min i inf_le_left hbot hIntInv)
  exact le_of_eq hIntBot

private lemma translate_perm {H : Subgroup (U ≃ₗ[ZMod p] U)} {U₀ : Submodule (ZMod p) U}
    (h : H) (i : translateFamily H U₀) :
    ∃ j : translateFamily H U₀,
      ((i : Submodule (ZMod p) U)).map (h : U →ₗ[ZMod p] U) = (j : Submodule (ZMod p) U) := by
  rcases i with ⟨V, ⟨k, rfl⟩⟩
  refine ⟨⟨U₀.map ((h * k : H) : U →ₗ[ZMod p] U), ⟨h * k, rfl⟩⟩, ?_⟩
  rw [← Submodule.map_comp]
  congr 1

private lemma translate_iSup_eq_top {H : Subgroup (U ≃ₗ[ZMod p] U)} {U₀ : Submodule (ZMod p) U}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) →
      W = ⊥ ∨ W = ⊤) (hU₀0 : U₀ ≠ ⊥) :
    (⨆ i : translateFamily H U₀, (i : Submodule (ZMod p) U)) = ⊤ := by
  have hperm : ∀ h ∈ H, ∀ i : translateFamily H U₀, ∃ j : translateFamily H U₀,
      ((i : Submodule (ZMod p) U)).map (h : U →ₗ[ZMod p] U) = (j : Submodule (ZMod p) U) :=
    fun h hh i => translate_perm ⟨h, hh⟩ i
  have hHinv : ∀ h ∈ H, ∀ w ∈ (⨆ i : translateFamily H U₀, (i : Submodule (ZMod p) U)),
      h w ∈ (⨆ i : translateFamily H U₀, (i : Submodule (ZMod p) U)) := by
    intro h hh' w hw
    have hmap : (⨆ i : translateFamily H U₀, (i : Submodule (ZMod p) U)).map
        (h : U →ₗ[ZMod p] U) ≤ ⨆ i : translateFamily H U₀, (i : Submodule (ZMod p) U) := by
      rw [Submodule.map_iSup]
      exact iSup_le fun i => by
        obtain ⟨j, hj⟩ := hperm h hh' i
        rw [hj]; exact le_iSup (fun i : translateFamily H U₀ => (i : Submodule (ZMod p) U)) j
    exact hmap (Submodule.mem_map_of_mem hw)
  rcases hirr _ hHinv with h | h
  · refine absurd (le_bot_iff.mp (h ▸ le_iSup
      (fun i : translateFamily H U₀ => (i : Submodule (ZMod p) U)) ⟨U₀, ⟨1, by simp⟩⟩)) ?_
    exact translate_ne_bot' hU₀0 ⟨U₀, ⟨1, by simp⟩⟩
  · exact h

private lemma translate_card_gt_one [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {W : Submodule (ZMod p) U}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hW1 : W ≠ ⊤) {U₀ : Submodule (ZMod p) U} (hU₀0 : U₀ ≠ ⊥) (hU₀W : U₀ ≤ W) :
    1 < Nat.card (translateFamily H U₀) := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun a b h => LinearEquiv.ext fun x => congrFun h x)
  have : Finite H := Subtype.finite
  rw [Finite.one_lt_card_iff_nontrivial]
  by_contra hsub
  rw [not_nontrivial_iff_subsingleton] at hsub
  have : Subsingleton (translateFamily H U₀) := hsub
  have hAll : ∀ h : H, U₀.map (h : U →ₗ[ZMod p] U) = U₀ := by
    intro h
    have : (⟨U₀.map (h : U →ₗ[ZMod p] U), ⟨h, rfl⟩⟩ : translateFamily H U₀) =
        ⟨U₀, ⟨1, by simp⟩⟩ := Subsingleton.elim _ _
    simpa using congrArg Subtype.val this
  have hHinvU₀ : ∀ h ∈ H, ∀ w ∈ U₀, h w ∈ U₀ := by
    intro h hh' w hw
    have hTh : U₀.map (h : U →ₗ[ZMod p] U) = U₀ := hAll ⟨h, hh'⟩
    rw [← hTh]
    exact Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  rcases hirr U₀ hHinvU₀ with h | h
  · exact hU₀0 h
  · exact hW1 (top_le_iff.mp (h ▸ hU₀W))

theorem eq_bot_or_eq_top_of_conj_invariant [Module.Finite (ZMod p) U]
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV H) {g : U ≃ₗ[ZMod p] U} {c : U}
    {φ : Module.Dual (ZMod p) U} (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1)
    (W : Submodule (ZMod p) U) (hW : ∀ h ∈ H, ∀ w ∈ W, (h * g * h⁻¹) w ∈ W) :
    W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hW0 : W = ⊥
  · exact Or.inl hW0
  by_cases hW1 : W = ⊤
  · exact Or.inr hW1
  exfalso
  let N := Subgroup.closure (conjSet H g)
  have hWN : ∀ n ∈ N, ∀ w ∈ W, n w ∈ W := fun n hn => conjSet_mapsInto hW hn
  have hFix : (⨅ n : N, LinearMap.ker (((n : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - 1)) = ⊥ :=
    conjSet_fixSpace_eq_bot hirr hh hτ
  obtain ⟨U₀, hU₀W, hU₀0, hU₀inv, hU₀min⟩ := exists_minimal_invariant hW0 hWN
  have hcard : 1 < Nat.card (translateFamily H U₀) :=
    translate_card_gt_one hirr hW1 hU₀0 hU₀W
  have hL0 : ∀ i : translateFamily H U₀, (i : Submodule (ZMod p) U) ≠ ⊥ :=
    fun i => translate_ne_bot' hU₀0 i
  have hind : iSupIndep (fun i : translateFamily H U₀ => (i : Submodule (ZMod p) U)) :=
    translate_iSupIndep hh hτ rfl hU₀0 hU₀inv hU₀min hFix
  have hsup : (⨆ i : translateFamily H U₀, (i : Submodule (ZMod p) U)) = ⊤ :=
    translate_iSup_eq_top hirr hU₀0
  have hperm : ∀ h ∈ H, ∀ i : translateFamily H U₀, ∃ j : translateFamily H U₀,
      ((i : Submodule (ZMod p) U)).map (h : U →ₗ[ZMod p] U) = (j : Submodule (ZMod p) U) :=
    fun h hh' i => translate_perm ⟨h, hh'⟩ i
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun a b h => LinearEquiv.ext fun x => congrFun h x)
  have : Finite H := Subtype.finite
  have : Finite (translateFamily H U₀) := Set.finite_range _
  exact hprim (CFSG.Quasithin.SimsG4.isImprimitiveOnV_of_family hcard
    (fun i : translateFamily H U₀ => (i : Submodule (ZMod p) U)) hL0 hind hsup hperm)

private noncomputable def conjRange (H : Subgroup (U ≃ₗ[ZMod p] U)) (g : U ≃ₗ[ZMod p] U) :
    Set (U ≃ₗ[ZMod p] U) :=
  Set.range (fun h : H => (h : U ≃ₗ[ZMod p] U) * g * (h : U ≃ₗ[ZMod p] U)⁻¹)

private noncomputable def conjOf (H : Subgroup (U ≃ₗ[ZMod p] U)) (g : U ≃ₗ[ZMod p] U)
    (i : conjRange H g) : H := Classical.choose i.2

private lemma conjOf_spec (H : Subgroup (U ≃ₗ[ZMod p] U)) (g : U ≃ₗ[ZMod p] U)
    (i : conjRange H g) :
    (conjOf H g i : U ≃ₗ[ZMod p] U) * g * (conjOf H g i : U ≃ₗ[ZMod p] U)⁻¹ = i.val :=
  Classical.choose_spec i.2

private noncomputable def conjCentre (H : Subgroup (U ≃ₗ[ZMod p] U)) (g : U ≃ₗ[ZMod p] U)
    (c : U) (i : conjRange H g) : U := (conjOf H g i : U ≃ₗ[ZMod p] U) c

private noncomputable def conjFunctional (H : Subgroup (U ≃ₗ[ZMod p] U)) (g : U ≃ₗ[ZMod p] U)
    (φ : Module.Dual (ZMod p) U) (i : conjRange H g) : Module.Dual (ZMod p) U :=
  φ ∘ₗ ((conjOf H g i : U ≃ₗ[ZMod p] U)⁻¹ : U ≃ₗ[ZMod p] U)

private noncomputable def conjLine (H : Subgroup (U ≃ₗ[ZMod p] U)) (g : U ≃ₗ[ZMod p] U)
    (c : U) (i : conjRange H g) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) {conjCentre H g c i}

private lemma conjLine_homology {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {c : U} {φ : Module.Dual (ZMod p) U} {τ : ZMod p} (hh : IsHomologyWith τ g c φ)
    (i : conjRange H g) :
    IsHomologyWith τ i.val (conjCentre H g c i) (conjFunctional H g φ i) := by
  have := hh.conj (conjOf H g i : U ≃ₗ[ZMod p] U)
  rwa [conjOf_spec H g i] at this

private lemma conjOf_val_mem {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    (hg : g ∈ H) (i : conjRange H g) : i.val ∈ H := by
  rw [← conjOf_spec H g i]
  exact H.mul_mem (H.mul_mem (conjOf H g i).2 hg) (H.inv_mem (conjOf H g i).2)

private lemma conjOf_commute {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    (hcomm : ∀ h ∈ H, g * (h * g * h⁻¹) = h * g * h⁻¹ * g) (i j : conjRange H g) :
    i.val * j.val = j.val * i.val := by
  have hk := hcomm ((conjOf H g j : U ≃ₗ[ZMod p] U)⁻¹ * (conjOf H g i : U ≃ₗ[ZMod p] U))
    (H.mul_mem (H.inv_mem (conjOf H g j).2) (conjOf H g i).2)
  have hg' : g * ((conjOf H g j : U ≃ₗ[ZMod p] U)⁻¹ * i.val * (conjOf H g j : U ≃ₗ[ZMod p] U)) =
      ((conjOf H g j : U ≃ₗ[ZMod p] U)⁻¹ * i.val * (conjOf H g j : U ≃ₗ[ZMod p] U)) * g := by
    rw [← conjOf_spec H g i]
    convert hk using 1 <;> group
  have hconj := congrArg (fun z => (conjOf H g j : U ≃ₗ[ZMod p] U) * z *
    (conjOf H g j : U ≃ₗ[ZMod p] U)⁻¹) hg'
  rw [← conjOf_spec H g j]
  simpa [mul_assoc] using hconj.symm

private lemma conjLine_eq_span {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {c : U} {φ : Module.Dual (ZMod p) U} {τ : ZMod p} (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1)
    (i : conjRange H g) (h : H)
    (hhi : (h : U ≃ₗ[ZMod p] U) * g * (h : U ≃ₗ[ZMod p] U)⁻¹ = i.val) :
    Submodule.span (ZMod p) {(h : U ≃ₗ[ZMod p] U) c} = conjLine H g c i := by
  have h1 : IsHomologyWith τ i.val ((h : U ≃ₗ[ZMod p] U) c)
      (φ ∘ₗ ((h : U ≃ₗ[ZMod p] U)⁻¹ : U ≃ₗ[ZMod p] U)) := by
    have := hh.conj (h : U ≃ₗ[ZMod p] U)
    rwa [hhi] at this
  have h2 := conjLine_homology hh i
  show Submodule.span (ZMod p) {(h : U ≃ₗ[ZMod p] U) c} =
    Submodule.span (ZMod p) {conjCentre H g c i}
  apply le_antisymm
  · rw [Submodule.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h2.mem_span_of_apply_eq_smul hτ h1.apply_centre
  · rw [Submodule.span_le]
    rintro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    exact h1.mem_span_of_apply_eq_smul hτ h2.apply_centre

private lemma conjLine_ne_bot {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {c : U} {φ : Module.Dual (ZMod p) U} {τ : ZMod p} (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1)
    (i : conjRange H g) : conjLine H g c i ≠ ⊥ := by
  show Submodule.span (ZMod p) {conjCentre H g c i} ≠ ⊥
  intro hbot
  rw [Submodule.span_singleton_eq_bot] at hbot
  exact (conjLine_homology hh i).centre_ne_zero hτ hbot

private lemma conjLine_iSupIndep {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {c : U} {φ : Module.Dual (ZMod p) U} {τ : ZMod p} (hg : g ∈ H)
    (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1) (htv : QTwoLin.TransvectionFree H)
    (hcomm : ∀ h ∈ H, g * (h * g * h⁻¹) = h * g * h⁻¹ * g) :
    iSupIndep (conjLine H g c) := by
  intro i
  rw [disjoint_iff_inf_le]
  have hle : conjLine H g c i ⊓ (⨆ (j) (_ : j ≠ i), conjLine H g c j) ≤
      LinearMap.ker (conjFunctional H g φ i) := by
    refine le_trans inf_le_right ?_
    refine iSup₂_le fun j hj => ?_
    intro v hv
    rw [LinearMap.mem_ker]
    change v ∈ Submodule.span (ZMod p) {conjCentre H g c j} at hv
    have hzero : conjFunctional H g φ i (conjCentre H g c j) = 0 := by
      have hind : conjCentre H g c j ∉ Submodule.span (ZMod p) {conjCentre H g c i} := by
        intro hmem
        have hne : i.val ≠ j.val := fun h => hj (Subtype.ext h).symm
        exact htv (i.val * j.val⁻¹)
          (H.mul_mem (conjOf_val_mem hg i) (H.inv_mem (conjOf_val_mem hg j)))
          (isTransvectionLin_mul_inv_of_mem_span (conjLine_homology hh i) (conjLine_homology hh j)
            hτ hmem hne)
      exact IsHomologyWith.apply_eq_zero_of_commute (conjLine_homology hh i)
        (conjLine_homology hh j) hτ (conjOf_commute hcomm i j) hind
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv
    rw [map_smul, hzero, smul_zero]
  have hLi : conjLine H g c i ⊓ LinearMap.ker (conjFunctional H g φ i) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    rw [Submodule.mem_inf] at hv
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hv.1
    rw [LinearMap.mem_ker, map_smul, (conjLine_homology hh i).1] at hv
    rcases smul_eq_zero.mp hv.2 with ha | hτ'
    · rw [ha, zero_smul]
    · exact absurd (sub_eq_zero.mp hτ') hτ
  exact le_trans (le_inf inf_le_left hle) (le_of_eq hLi)

private lemma conjLine_perm {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {c : U} {φ : Module.Dual (ZMod p) U} {τ : ZMod p} (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1)
    (h : H) (i : conjRange H g) :
    ∃ j : conjRange H g, (conjLine H g c i).map (h : U →ₗ[ZMod p] U) = conjLine H g c j := by
  have hmem : (fun k : H => (k : U ≃ₗ[ZMod p] U) * g * (k : U ≃ₗ[ZMod p] U)⁻¹) (h * conjOf H g i) =
      (h : U ≃ₗ[ZMod p] U) * i.val * (h : U ≃ₗ[ZMod p] U)⁻¹ := by
    have := congrArg (fun z => (h : U ≃ₗ[ZMod p] U) * z * (h : U ≃ₗ[ZMod p] U)⁻¹)
      (conjOf_spec H g i)
    simpa only [Subgroup.coe_mul, mul_inv_rev, mul_assoc] using this
  let j : conjRange H g := ⟨(h : U ≃ₗ[ZMod p] U) * i.val * (h : U ≃ₗ[ZMod p] U)⁻¹,
    ⟨h * conjOf H g i, hmem⟩⟩
  refine ⟨j, ?_⟩
  show (Submodule.span (ZMod p) {conjCentre H g c i}).map (h : U →ₗ[ZMod p] U) = conjLine H g c j
  rw [Submodule.map_span, Set.image_singleton]
  have hthis := conjLine_eq_span hh hτ j (h * conjOf H g i) hmem
  rw [← hthis]
  congr 1

private lemma conjLine_iSup_eq_top {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {c : U} {φ : Module.Dual (ZMod p) U} {τ : ZMod p} (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    (⨆ i : conjRange H g, conjLine H g c i) = ⊤ := by
  have hperm : ∀ h ∈ H, ∀ i : conjRange H g, ∃ j : conjRange H g,
      (conjLine H g c i).map (h : U →ₗ[ZMod p] U) = conjLine H g c j :=
    fun h hh' i => conjLine_perm hh hτ ⟨h, hh'⟩ i
  have hHinv : ∀ h ∈ H, ∀ w ∈ (⨆ i : conjRange H g, conjLine H g c i),
      h w ∈ (⨆ i : conjRange H g, conjLine H g c i) := by
    intro h hh' w hw
    have hmap : (⨆ i : conjRange H g, conjLine H g c i).map (h : U →ₗ[ZMod p] U) ≤
        ⨆ i : conjRange H g, conjLine H g c i := by
      rw [Submodule.map_iSup]
      exact iSup_le fun i => by
        obtain ⟨j, hj⟩ := hperm h hh' i
        rw [hj]; exact le_iSup (conjLine H g c) j
    exact hmap (Submodule.mem_map_of_mem hw)
  rcases hirr _ hHinv with h | h
  · refine absurd (le_bot_iff.mp (h ▸ le_iSup (conjLine H g c) ⟨g, ⟨1, by simp⟩⟩)) ?_
    exact conjLine_ne_bot hh hτ ⟨g, ⟨1, by simp⟩⟩
  · exact h

private lemma conjRange_card_gt_one [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {g : U ≃ₗ[ZMod p] U}
    {c : U} {φ : Module.Dual (ZMod p) U} {τ : ZMod p} (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1)
    (hn : 2 ≤ Module.finrank (ZMod p) U)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤) :
    1 < Nat.card (conjRange H g) := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun a b h => LinearEquiv.ext fun x => congrFun h x)
  have : Finite H := Subtype.finite
  have : Finite (conjRange H g) := Set.finite_range _
  rw [Finite.one_lt_card_iff_nontrivial]
  by_contra hsub
  rw [not_nontrivial_iff_subsingleton] at hsub
  have : Subsingleton (conjRange H g) := hsub
  let i₀ : conjRange H g := ⟨g, ⟨1, by simp⟩⟩
  have hconst : ∀ i : conjRange H g, conjLine H g c i = conjLine H g c i₀ :=
    fun i => by rw [Subsingleton.elim i i₀]
  have hsup := conjLine_iSup_eq_top hh hτ hirr
  have hsup' : (⨆ i : conjRange H g, conjLine H g c i) = conjLine H g c i₀ :=
    le_antisymm (iSup_le fun i => le_of_eq (hconst i)) (le_iSup (conjLine H g c) i₀)
  have htop : conjLine H g c i₀ = ⊤ := hsup'.symm.trans hsup
  have hfr1 : Module.finrank (ZMod p) ↥(conjLine H g c i₀) = 1 := by
    show Module.finrank (ZMod p) ↥(Submodule.span (ZMod p) {conjCentre H g c i₀}) = 1
    rw [finrank_span_singleton]
    exact (conjLine_homology hh i₀).centre_ne_zero hτ
  have hfr2 : Module.finrank (ZMod p) ↥(conjLine H g c i₀) = Module.finrank (ZMod p) U := by
    rw [htop]; simp
  omega

theorem isImprimitiveOnV_of_forall_commute [Module.Finite (ZMod p) U]
    (hn : 2 ≤ Module.finrank (ZMod p) U)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (htv : QTwoLin.TransvectionFree H) {g : U ≃ₗ[ZMod p] U} {c : U}
    {φ : Module.Dual (ZMod p) U} (hg : g ∈ H) (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1)
    (hcomm : ∀ h ∈ H, g * (h * g * h⁻¹) = h * g * h⁻¹ * g) :
    Quasithin.SimsG4.IsImprimitiveOnV H := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun a b h => LinearEquiv.ext fun x => congrFun h x)
  have : Finite H := Subtype.finite
  have : Finite (conjRange H g) := Set.finite_range _
  have hcard : 1 < Nat.card (conjRange H g) := conjRange_card_gt_one hh hτ hn hirr
  have hL0 : ∀ i : conjRange H g, conjLine H g c i ≠ ⊥ := fun i => conjLine_ne_bot hh hτ i
  have hind : iSupIndep (conjLine H g c) := conjLine_iSupIndep hg hh hτ htv hcomm
  have hsup : (⨆ i : conjRange H g, conjLine H g c i) = ⊤ := conjLine_iSup_eq_top hh hτ hirr
  have hperm : ∀ h ∈ H, ∀ i : conjRange H g, ∃ j : conjRange H g,
      (conjLine H g c i).map (h : U →ₗ[ZMod p] U) = conjLine H g c j :=
    fun h hh' i => conjLine_perm hh hτ ⟨h, hh'⟩ i
  exact CFSG.Quasithin.SimsG4.isImprimitiveOnV_of_family hcard (conjLine H g c) hL0 hind hsup hperm

theorem exists_conj_not_commute_of_isHomologyWith [Module.Finite (ZMod p) U]
    (hn : 2 ≤ Module.finrank (ZMod p) U)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (htv : QTwoLin.TransvectionFree H) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV H)
    {g : U ≃ₗ[ZMod p] U} {c : U} {φ : Module.Dual (ZMod p) U} (hg : g ∈ H)
    (hh : IsHomologyWith τ g c φ) (hτ : τ ≠ 1) :
    ∃ h ∈ H, g * (h * g * h⁻¹) ≠ h * g * h⁻¹ * g := by
  by_contra hcon
  push Not at hcon
  exact hprim (isImprimitiveOnV_of_forall_commute hn hirr htv hg hh hτ hcon)

private lemma conjugate_mapsInto_span_pair [Module.Finite (ZMod p) U]
    {H : Subgroup (U ≃ₗ[ZMod p] U)} {τ : ZMod p}
    {α β : U ≃ₗ[ZMod p] U} {cα cβ : U} {φα φβ : Module.Dual (ZMod p) U}
    (htv : QTwoLin.TransvectionFree H) (hα : α ∈ H) (hβ : β ∈ H)
    (hαh : IsHomologyWith τ α cα φα) (hβh : IsHomologyWith τ β cβ φβ) (hτ : τ ≠ 1)
    {h : U ≃ₗ[ZMod p] U} (hh : h ∈ H)
    (hc : h cα ∉ Submodule.span (ZMod p) {cα, cβ} →
      h cα ∈ LinearMap.ker φα ⊓ LinearMap.ker φβ) :
    ∀ w ∈ Submodule.span (ZMod p) {cα, cβ},
      (h * α * h⁻¹) w ∈ Submodule.span (ZMod p) {cα, cβ} := by
  intro w hw
  have hγh : IsHomologyWith τ (h * α * h⁻¹) (h cα)
      (φα ∘ₗ ((h : U ≃ₗ[ZMod p] U)⁻¹ : U ≃ₗ[ZMod p] U)) := hαh.conj (h : U ≃ₗ[ZMod p] U)
  by_cases hcW : h cα ∈ Submodule.span (ZMod p) {cα, cβ}
  · rw [hγh.2]
    exact Submodule.add_mem _ hw (Submodule.smul_mem _ _ hcW)
  · have hcY : h cα ∈ LinearMap.ker φα ⊓ LinearMap.ker φβ := hc hcW
    have hγH : h * α * h⁻¹ ∈ H := H.mul_mem (H.mul_mem hh hα) (H.inv_mem hh)
    have hα0 : φα (h cα) = 0 := (Submodule.mem_inf.mp hcY).1
    have hβ0 : φβ (h cα) = 0 := (Submodule.mem_inf.mp hcY).2
    have hφα : (φα ∘ₗ ((h : U ≃ₗ[ZMod p] U)⁻¹ : U ≃ₗ[ZMod p] U)) cα = 0 :=
      apply_eq_zero_of_apply_eq_zero htv hα hγH hαh hγh hτ hα0
    have hφβ : (φα ∘ₗ ((h : U ≃ₗ[ZMod p] U)⁻¹ : U ≃ₗ[ZMod p] U)) cβ = 0 :=
      apply_eq_zero_of_apply_eq_zero htv hβ hγH hβh hγh hτ hβ0
    have hφw : (φα ∘ₗ ((h : U ≃ₗ[ZMod p] U)⁻¹ : U ≃ₗ[ZMod p] U)) w = 0 := by
      obtain ⟨r, s, rfl⟩ := Submodule.mem_span_pair.mp hw
      rw [map_add, map_smul, map_smul, hφα, hφβ, smul_zero, smul_zero, add_zero]
    rw [hγh.2, hφw, zero_smul, add_zero]
    exact hw

theorem exists_conj_centre_not_mem [Module.Finite (ZMod p) U]
    (hn : 3 ≤ Module.finrank (ZMod p) U)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ h ∈ H, ∀ w ∈ W, h w ∈ W) → W = ⊥ ∨ W = ⊤)
    (htv : QTwoLin.TransvectionFree H) (hprim : ¬ Quasithin.SimsG4.IsImprimitiveOnV H)
    {α β : U ≃ₗ[ZMod p] U} {cα cβ : U} {φα φβ : Module.Dual (ZMod p) U} (hα : α ∈ H)
    (hβ : β ∈ H) (hαh : IsHomologyWith τ α cα φα) (hβh : IsHomologyWith τ β cβ φβ)
    (hτ : τ ≠ 1) :
    ∃ h ∈ H, h cα ∉ Submodule.span (ZMod p) {cα, cβ} ∧
      h cα ∉ LinearMap.ker φα ⊓ LinearMap.ker φβ := by
  classical
  by_contra hcon
  push Not at hcon
  let W : Submodule (ZMod p) U := Submodule.span (ZMod p) {cα, cβ}
  have hW : ∀ h ∈ H, ∀ w ∈ W, (h * α * h⁻¹) w ∈ W :=
    fun h hh w hw => conjugate_mapsInto_span_pair htv hα hβ hαh hβh hτ hh (hcon h hh) w hw
  have hcase := eq_bot_or_eq_top_of_conj_invariant hirr hprim hαh hτ W hW
  rcases hcase with h | h
  · have hcα : cα ∈ W := Submodule.subset_span (by simp)
    rw [h] at hcα
    exact (hαh.centre_ne_zero hτ) (by simpa using hcα)
  · have hfr : Module.finrank (ZMod p) W ≤ 2 := by
      show Module.finrank (ZMod p) (Submodule.span (ZMod p) {cα, cβ}) ≤ 2
      have : Finite U := Module.finite_of_finite (ZMod p)
      have : Fintype U := Fintype.ofFinite U
      have h := finrank_span_le_card (R := ZMod p) ({cα, cβ} : Set U)
      have h2 : ({cα, cβ} : Set U).toFinset.card ≤ 2 := by
        rw [Set.toFinset_insert, Set.toFinset_singleton]
        calc (insert cα ({cβ} : Finset U)).card ≤ ({cβ} : Finset U).card + 1 :=
              Finset.card_insert_le _ _
          _ = 2 := by simp
      exact h.trans h2
    rw [h] at hfr
    rw [finrank_top] at hfr
    omega

end CFSG.StandardType.ZS

end
