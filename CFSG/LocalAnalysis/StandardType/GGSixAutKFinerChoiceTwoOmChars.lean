module

public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoOmBlock
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoChars

public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module Multiplicative QuadraticMap ChoiceTwo

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Commutant

variable {K : Type} [Field K] [CharP K 2]

theorem eq_comb_of_commute (T : (K × K) →ₗ[K] (K × K)) (hT : ∀ c, T (zL K c) = zL K (T c))
    (c : K × K) : T c = c.1 • T (1, 0) + c.2 • zL K (T (1, 0)) := by
  have hc : c = c.1 • ((1 : K), (0 : K)) + c.2 • zL K (1, 0) := by
    ext <;> simp [zL_apply]
  conv_lhs => rw [hc]
  rw [map_add, map_smul, map_smul, hT]

theorem commute_of_zL (T T' : (K × K) →ₗ[K] (K × K)) (hT : ∀ c, T (zL K c) = zL K (T c))
    (hT' : ∀ c, T' (zL K c) = zL K (T' c)) (c : K × K) : T (T' c) = T' (T c) := by
  rw [eq_comb_of_commute T hT (T' c), eq_comb_of_commute T' hT' (T c),
    eq_comb_of_commute T' hT' c, eq_comb_of_commute T hT c]
  set t := T (1, 0)
  set t' := T' (1, 0)
  ext <;> simp [zL_apply] <;> ring

end Commutant

namespace OmCoord

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} (C : OmCoord K Q A)

section Plane

@[expose] noncomputable def planeMap (i : Fin C.s) (g : V ≃ₗ[K] V) : (K × K) →ₗ[K] (K × K) :=
  LinearMap.proj i ∘ₗ LinearMap.fst K _ C.W0 ∘ₗ C.Φ.symm.toLinearMap ∘ₗ g.toLinearMap ∘ₗ
    C.Φ.toLinearMap ∘ₗ LinearMap.inl K _ C.W0 ∘ₗ LinearMap.single K (fun _ => K × K) i

theorem planeMap_apply (i : Fin C.s) (g : V ≃ₗ[K] V) (c : K × K) :
    C.planeMap i g c = (C.Φ.symm (g (C.Φ (Pi.single i c, 0)))).1 i := rfl

theorem apply_plane {i : Fin C.s} {g : V ≃ₗ[K] V}
    (hg : ∀ c, ∃ c', g (C.Φ (Pi.single i c, 0)) = C.Φ (Pi.single i c', 0)) (c : K × K) :
    g (C.Φ (Pi.single i c, 0)) = C.Φ (Pi.single i (C.planeMap i g c), 0) := by
  obtain ⟨c', hc'⟩ := hg c
  rw [hc', planeMap_apply, hc', LinearEquiv.symm_apply_apply]
  simp

theorem single_injective {i : Fin C.s} {c c' : K × K}
    (h : C.Φ (Pi.single i c, 0) = C.Φ (Pi.single i c', 0)) : c = c' := by
  have := congrFun (congrArg Prod.fst (C.Φ.injective h)) i
  simpa using this

theorem preserves_plane {f₀ f₁ : Fin C.s → ZMod 3} {i : Fin C.s} (hf0 : f₀ i = 0)
    (hf1 : f₁ i ≠ 0) (hiso : ∀ l, l ≠ i → f₀ l = 0 → f₁ l = 0) {g : V ≃ₗ[K] V}
    (hg0 : g * C.tor f₀ = C.tor f₀ * g) (hg1 : g * C.tor f₁ = C.tor f₁ * g) (c : K × K) :
    ∃ c', g (C.Φ (Pi.single i c, 0)) = C.Φ (Pi.single i c', 0) := by
  set v := C.Φ (Pi.single i c, 0) with hv
  have hv0 : C.tor f₀ v = v := (C.tor_Φ_eq_iff f₀ _ 0).mpr fun l hl => by
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact hl hf0
  have hv1 : C.tor f₁ (C.tor f₁ v) + C.tor f₁ v + v = 0 :=
    (C.phi3_Φ_eq_zero_iff f₁ _ 0).mpr ⟨rfl, fun l hl => by
      rw [Pi.single_eq_of_ne]
      rintro rfl
      exact hf1 hl⟩
  obtain ⟨⟨d, x⟩, hdx⟩ := C.Φ.surjective (g v)
  have hw0 : C.tor f₀ (g v) = g v := by
    have := congrArg (fun h : V ≃ₗ[K] V => h v) hg0
    simp only [LinearEquiv.mul_apply, hv0] at this
    exact this.symm
  have hw1 : C.tor f₁ (C.tor f₁ (g v)) + C.tor f₁ (g v) + g v = 0 := by
    have e : ∀ w, g (C.tor f₁ w) = C.tor f₁ (g w) := fun w => by
      have := congrArg (fun h : V ≃ₗ[K] V => h w) hg1
      simpa only [LinearEquiv.mul_apply] using this
    rw [← e, ← e, ← map_add, ← map_add, hv1, map_zero]
  rw [← hdx] at hw0 hw1
  have hd0 := (C.tor_Φ_eq_iff f₀ d x).mp hw0
  obtain ⟨rfl, hd1⟩ := (C.phi3_Φ_eq_zero_iff f₁ d x).mp hw1
  refine ⟨d i, ?_⟩
  rw [← hdx]
  congr 2
  funext l
  by_cases hl : l = i
  · subst hl
    rw [Pi.single_eq_same]
  · rw [Pi.single_eq_of_ne hl]
    by_cases h0 : f₀ l = 0
    · exact hd1 l (hiso l hl h0)
    · exact hd0 l h0

theorem tor_single (f : Fin C.s → ZMod 3) (i : Fin C.s) (c : K × K) :
    C.tor f (C.Φ (Pi.single i c, 0)) = C.Φ (Pi.single i (zpow (f i) c), 0) := by
  rw [C.tor_acts]
  congr 2
  funext l
  by_cases hl : l = i
  · subst hl
    simp [torC_apply]
  · simp [torC_apply, Pi.single_eq_of_ne hl]

theorem commute_zL_of_zpow {a : ZMod 3} (ha : a ≠ 0) {T : (K × K) →ₗ[K] (K × K)}
    (hT : ∀ c, T (zpow a c) = zpow a (T c)) (c : K × K) : T (zL K c) = zL K (T c) := by
  rcases zpow_val_cases (K := K) a with ⟨h0, -⟩ | h1 | h2
  · exact absurd h0 ha
  · have := hT c
    rwa [h1] at this
  · have e : ∀ x : K × K, zL K x = (zL K * zL K) ((zL K * zL K) x) := fun x => by
      simp only [LinearEquiv.mul_apply]
      rw [zL_three]
    rw [e, e (T c)]
    have h' : ∀ x, T ((zL K * zL K) x) = (zL K * zL K) (T x) := fun x => by
      have := hT x
      rwa [h2] at this
    rw [h', h']

theorem fix_plane {f₀ f₁ : Fin C.s → ZMod 3} {i : Fin C.s} (hf0 : f₀ i = 0) (hf1 : f₁ i ≠ 0)
    (hiso : ∀ l, l ≠ i → f₀ l = 0 → f₁ l = 0) {J : Subgroup (V ≃ₗ[K] V)} (hJp : ⁅J, J⁆ = J)
    (hJ0 : ∀ g ∈ J, g * C.tor f₀ = C.tor f₀ * g) (hJ1 : ∀ g ∈ J, g * C.tor f₁ = C.tor f₁ * g)
    {g : V ≃ₗ[K] V} (hg : g ∈ J) (c : K × K) :
    g (C.Φ (Pi.single i c, 0)) = C.Φ (Pi.single i c, 0) := by
  have hpres : ∀ h ∈ J, ∀ c, ∃ c', h (C.Φ (Pi.single i c, 0)) = C.Φ (Pi.single i c', 0) :=
    fun h hh => C.preserves_plane hf0 hf1 hiso (hJ0 h hh) (hJ1 h hh)
  have happ : ∀ h ∈ J, ∀ c, h (C.Φ (Pi.single i c, 0)) =
      C.Φ (Pi.single i (C.planeMap i h c), 0) := fun h hh => C.apply_plane (hpres h hh)
  have hz : ∀ h ∈ J, ∀ c, C.planeMap i h (zL K c) = zL K (C.planeMap i h c) := by
    intro h hh
    refine commute_zL_of_zpow hf1 fun c => ?_
    have e := congrArg (fun k : V ≃ₗ[K] V => k (C.Φ (Pi.single i c, 0))) (hJ1 h hh)
    simp only [LinearEquiv.mul_apply, C.tor_single, happ h hh] at e
    exact C.single_injective e
  have hinv : ∀ h ∈ J, ∀ c, C.planeMap i h (C.planeMap i h⁻¹ c) = c := by
    intro h hh c
    have e : h (h⁻¹ (C.Φ (Pi.single i c, 0))) = C.Φ (Pi.single i c, 0) := by
      rw [← LinearEquiv.mul_apply, mul_inv_cancel]
      rfl
    rw [happ _ (J.inv_mem hh), happ h hh] at e
    exact C.single_injective e
  have hS : J ≤ MulAction.stabilizer (V ≃ₗ[K] V) (C.Φ (Pi.single i c, 0)) := by
    rw [← hJp, Subgroup.commutator_le]
    intro h hh k hk
    rw [MulAction.mem_stabilizer_iff, commutatorElement_def]
    change h (k (h⁻¹ (k⁻¹ (C.Φ (Pi.single i c, 0))))) = _
    rw [happ _ (J.inv_mem hk), happ _ (J.inv_mem hh), happ k hk, happ h hh,
      commute_of_zL _ _ (hz k hk) (hz _ (J.inv_mem hh)), hinv h hh, hinv k hk]
  exact hS hg

theorem commute_tor_of_fix {i : Fin C.s} {g : V ≃ₗ[K] V}
    (hgO : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hg : ∀ c, g (C.Φ (Pi.single i c, 0)) = C.Φ (Pi.single i c, 0)) {f : Fin C.s → ZMod 3}
    (hf : ∀ l, l ≠ i → f l = 0) : g * C.tor f = C.tor f * g := by
  have hgQ : ∀ v, Q (g v) = Q v := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hgO
  have htriv : ∀ (d : Fin C.s → K × K) x, d i = 0 → C.tor f (C.Φ (d, x)) = C.Φ (d, x) :=
    fun d x hd => (C.tor_Φ_eq_iff f d x).mpr fun l hl => by
      by_cases hli : l = i
      · rw [hli, hd]
      · exact absurd (hf l hli) hl
  refine C.ext_Φ fun d x => ?_
  obtain ⟨v', hv'⟩ : ∃ v', v' = C.Φ (d - Pi.single i (d i), x) := ⟨_, rfl⟩
  have hsplit : C.Φ (d, x) = C.Φ (Pi.single i (d i), 0) + v' := by
    rw [hv', ← map_add, Prod.mk_add_mk, zero_add, add_sub_cancel]
  have hv'0 : (d - Pi.single i (d i) : Fin C.s → K × K) i = 0 := by simp
  have htv' : C.tor f v' = v' := by rw [hv']; exact htriv _ _ hv'0
  obtain ⟨⟨d'', x''⟩, hd''⟩ := C.Φ.surjective (g v')
  have hperp : ∀ c, polar Q (C.Φ (d'', x'')) (C.Φ (Pi.single i c, 0)) = 0 := by
    intro c
    rw [hd'', ← hg c, polar_map_of_isom hgQ, hv', polar_single, hv'0, pn_zero_left]
  have hd''i := C.coord_eq_zero_of_perp hperp
  have htg : C.tor f (g v') = g v' := by rw [← hd'']; exact htriv _ _ hd''i
  simp only [LinearEquiv.mul_apply]
  rw [hsplit, map_add, map_add, C.tor_single, hg, htv', map_add, hg, map_add, C.tor_single, htg]

theorem pow_card_le (U : Finset (Fin C.s)) {H : Subgroup (V ≃ₗ[K] V)} [Finite H]
    (hU : ∀ i ∈ U, ∀ a, C.tor (Pi.single i a) ∈ H) : 3 ^ U.card ≤ Nat.card H := by
  classical
  set ext : (U → ZMod 3) → Fin C.s → ZMod 3 :=
    fun e l => if h : l ∈ U then e ⟨l, h⟩ else 0 with hext
  have hsum : ∀ e : U → ZMod 3, ext e = ∑ i ∈ U.attach, Pi.single (i : Fin C.s) (e i) := by
    intro e
    funext l
    rw [Finset.sum_apply]
    by_cases hl : l ∈ U
    · rw [Finset.sum_eq_single ⟨l, hl⟩]
      · simp [hext, hl]
      · intro b _ hb
        rw [Pi.single_eq_of_ne]
        intro h
        exact hb (Subtype.ext h.symm)
      · intro h
        exact absurd (Finset.mem_attach _ _) h
    · rw [Finset.sum_eq_zero]
      · simp [hext, hl]
      · intro b _
        rw [Pi.single_eq_of_ne]
        rintro rfl
        exact hl b.2
  have hmem : ∀ e, C.tor (ext e) ∈ H := by
    intro e
    rw [hsum]
    induction (U.attach) using Finset.induction_on with
    | empty =>
      rw [Finset.sum_empty, C.tor_zero]
      exact one_mem _
    | insert a S ha ih =>
      rw [Finset.sum_insert ha, C.tor_add]
      exact mul_mem (hU _ a.2 _) ih
  have hinj : Function.Injective fun e : U → ZMod 3 => (⟨C.tor (ext e), hmem e⟩ : H) := by
    intro e e' h
    have h1 := C.tor_injective (congrArg Subtype.val h)
    funext l
    have := congrFun h1 l
    simpa [hext, l.2] using this
  have := Nat.card_le_card_of_injective _ hinj
  rwa [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := U), Fintype.card_coe] at this

end Plane

section Pair

theorem dot3_self_ne_zero : ∀ x : ZMod 3 × ZMod 3, x ≠ 0 → dot3 x x ≠ 0 := by decide

theorem exists_pair (t₁ t₂ : Fin C.s → ZMod 3) {J : Subgroup (V ≃ₗ[K] V)}
    (hJp : ⁅J, J⁆ = J) (hJO : J ≤ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hJc : ∀ a, ∀ g ∈ J, g * C.tor (comb2 t₁ t₂ a) = C.tor (comb2 t₁ t₂ a) * g)
    (hcount : ∀ U : Finset (Fin C.s),
      (∀ i ∈ U, ∀ a, ∀ g ∈ J, g * C.tor (Pi.single i a) = C.tor (Pi.single i a) * g) →
        U.card + 1 < C.s) :
    ∃ i j, i ≠ j ∧ ∃ b : Bool, ∀ a, comb2 t₁ t₂ a i = sgnZ b (comb2 t₁ t₂ a j) := by
  classical
  set c : Fin C.s → ZMod 3 × ZMod 3 := fun i => (t₁ i, t₂ i) with hc
  have hcomb : ∀ a i, comb2 t₁ t₂ a i = dot3 a (c i) := fun a i => comb2_apply t₁ t₂ a i
  by_contra hno
  push Not at hno
  have hno' : ∀ i j, i ≠ j → c i ≠ c j ∧ c i ≠ -c j := by
    intro i j hij
    refine ⟨fun h => ?_, fun h => ?_⟩
    · obtain ⟨a, ha⟩ := hno i j hij false
      exact ha (by rw [hcomb, hcomb, h, sgnZ_false])
    · obtain ⟨a, ha⟩ := hno i j hij true
      refine ha ?_
      rw [hcomb, hcomb, h, sgnZ_true]
      simp only [dot3, Prod.fst_neg, Prod.snd_neg]
      ring
  set U : Finset (Fin C.s) := Finset.univ.filter fun i => c i ≠ 0 with hU
  have hcent : ∀ i ∈ U, ∀ a, ∀ g ∈ J, g * C.tor (Pi.single i a) = C.tor (Pi.single i a) * g := by
    intro i hi a g hg
    have hci : c i ≠ 0 := (Finset.mem_filter.mp hi).2
    have hf0 : comb2 t₁ t₂ (perp3 (c i)) i = 0 := by rw [hcomb]; exact dot3_perp3_self _
    have hf1 : comb2 t₁ t₂ (c i) i ≠ 0 := by rw [hcomb]; exact dot3_self_ne_zero _ hci
    have hiso : ∀ l, l ≠ i → comb2 t₁ t₂ (perp3 (c i)) l = 0 → comb2 t₁ t₂ (c i) l = 0 := by
      intro l hl h0
      rw [hcomb, dot3_perp3_eq_zero_iff, det2_eq_zero_iff _ _ hci] at h0
      rcases h0 with h | h | h
      · rw [hcomb, h, dot3_zero_right]
      · exact absurd h.symm (hno' i l (Ne.symm hl)).1
      · exact absurd (by rw [h, neg_neg]) (hno' i l (Ne.symm hl)).2
    exact C.commute_tor_of_fix (hJO hg)
      (C.fix_plane hf0 hf1 hiso hJp (hJc _) (hJc _) hg) fun l hl => Pi.single_eq_of_ne hl _
  have h1 := hcount U hcent
  have hZ : (Finset.univ.filter fun i => c i = 0).card ≤ 1 := by
    rw [Finset.card_le_one]
    intro i hi j hj
    by_contra hij
    exact (hno' i j hij).1 (by
      rw [(Finset.mem_filter.mp hi).2, (Finset.mem_filter.mp hj).2])
  have hsplit := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin C.s)))
    (fun i => c i = 0)
  rw [Finset.card_univ, Fintype.card_fin] at hsplit
  have : U.card = (Finset.univ.filter fun i => ¬ c i = 0).card := rfl
  omega

end Pair

end OmCoord

end ChoiceTwoOm

end CFSG.StandardType
