module

public import CFSG.LocalAnalysis.StandardType.GGQ2S08BigDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix TestLin

private lemma ggQ2s08mt_eq_of_smul_basis_eq {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {N : ℕ} (b : Module.Basis (Fin N) (ZMod 3) V) {k k' : Fin N} {ε ε' : ZMod 3} (hε : ε ≠ 0)
    (h : ε • b k = ε' • b k') : k = k' := by
  by_contra hne
  have h1 : b.repr (ε • b k) k = ε := by
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, Finsupp.single_eq_same,
      smul_eq_mul, mul_one]
  have h2 : b.repr (ε' • b k') k = 0 := by
    rw [map_smul, Module.Basis.repr_self, Finsupp.smul_apply,
      Finsupp.single_eq_of_ne hne, smul_zero]
  have hcongr := congrArg (fun x => b.repr x k) h
  rw [h1, h2] at hcongr
  exact hε hcongr

private lemma ggQ2s08mt_perm_unique {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ}
    (b : Module.Basis (Fin N) (ZMod 3) V) {g : V ≃ₗ[ZMod 3] V}
    {σ σ' : Equiv.Perm (Fin N)} {ε ε' : Fin N → ZMod 3}
    (hε : ∀ i, ε i ≠ 0) (h : ∀ i, g (b i) = ε i • b (σ i))
    (hε' : ∀ i, ε' i ≠ 0) (h' : ∀ i, g (b i) = ε' i • b (σ' i)) : σ = σ' := by
  apply Equiv.ext
  intro i
  exact ggQ2s08mt_eq_of_smul_basis_eq b (hε i) (by rw [← h i, h' i])

theorem ggQ2s08_big_mono_trans {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {N : ℕ} (hN : 5 ≤ N)
    (b : Module.Basis (Fin N) (ZMod 3) V) {W : Subgroup (V ≃ₗ[ZMod 3] V)}
    (e : ↥W ≃* Equiv.Perm (Fin N)) (hWm : ∀ w ∈ W, GGQ2S08Mono b w) :
    ∀ i j, ∃ w ∈ W, ∃ ε : ZMod 3, ε ≠ 0 ∧ w (b i) = ε • b j := by
  classical
  let perm : ↥W → Equiv.Perm (Fin N) := fun w => (hWm w w.2).choose
  have perm_spec : ∀ w : ↥W, ∃ ε : Fin N → ZMod 3, (∀ i, ε i ≠ 0) ∧
      ∀ i, (w : V ≃ₗ[ZMod 3] V) (b i) = ε i • b (perm w i) := by
    intro w
    exact ⟨(hWm w w.2).choose_spec.choose,
      (hWm w w.2).choose_spec.choose_spec.1,
      (hWm w w.2).choose_spec.choose_spec.2⟩
  let π : ↥W →* Equiv.Perm (Fin N) :=
    { toFun := perm
      map_one' := by
        obtain ⟨ε, hε, hrepr⟩ := perm_spec (1 : ↥W)
        exact ggQ2s08mt_perm_unique b hε hrepr (fun _ => one_ne_zero) (fun i => by simp)
      map_mul' := by
        intro w w'
        obtain ⟨ε, hε, hrepr⟩ := perm_spec (w * w')
        obtain ⟨εw, hεw, hreprw⟩ := perm_spec w
        obtain ⟨εw', hεw', hreprw'⟩ := perm_spec w'
        refine ggQ2s08mt_perm_unique (ε' := fun i => εw' i * εw (perm w' i)) b hε hrepr ?_ ?_
        · intro i
          exact mul_ne_zero (hεw' i) (hεw (perm w' i))
        · intro i
          calc ((w * w') : V ≃ₗ[ZMod 3] V) (b i)
              = (w : V ≃ₗ[ZMod 3] V) ((w' : V ≃ₗ[ZMod 3] V) (b i)) := rfl
            _ = (w : V ≃ₗ[ZMod 3] V) (εw' i • b (perm w' i)) := by rw [hreprw' i]
            _ = εw' i • (w : V ≃ₗ[ZMod 3] V) (b (perm w' i)) := by rw [map_smul]
            _ = εw' i • (εw (perm w' i) • b (perm w (perm w' i))) := by
                  rw [hreprw (perm w' i)]
            _ = (εw' i * εw (perm w' i)) • b (perm w (perm w' i)) := by rw [smul_smul]
            _ = (εw' i * εw (perm w' i)) • b ((perm w * perm w') i) := by
                  rw [Equiv.Perm.mul_apply] }
  let K : Subgroup (Equiv.Perm (Fin N)) := π.ker.map e.toMonoidHom
  have hKnormal : K.Normal :=
    Subgroup.Normal.map (MonoidHom.normal_ker π) e.toMonoidHom e.surjective
  have hsq : ∀ x : ZMod 3, x ≠ 0 → x * x = 1 := by decide
  have hsqK : ∀ x ∈ K, x * x = 1 := by
    intro x hx
    obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨ε, hε, hrepr⟩ := perm_spec w
    have hper : perm w = 1 := MonoidHom.mem_ker.mp hw
    have hdiag : ∀ i, (w : V ≃ₗ[ZMod 3] V) (b i) = ε i • b i := by
      intro i
      have h := hrepr i
      rw [hper] at h
      simpa using h
    have hww : w * w = 1 := by
      apply Subtype.ext
      rw [← LinearEquiv.toLinearMap_inj]
      apply Module.Basis.ext b
      intro i
      show ((w : V ≃ₗ[ZMod 3] V) * (w : V ≃ₗ[ZMod 3] V)) (b i)
          = (1 : V ≃ₗ[ZMod 3] V) (b i)
      calc ((w : V ≃ₗ[ZMod 3] V) * (w : V ≃ₗ[ZMod 3] V)) (b i)
          = (w : V ≃ₗ[ZMod 3] V) ((w : V ≃ₗ[ZMod 3] V) (b i)) := rfl
        _ = (w : V ≃ₗ[ZMod 3] V) (ε i • b i) := by rw [hdiag i]
        _ = ε i • (w : V ≃ₗ[ZMod 3] V) (b i) := by rw [map_smul]
        _ = ε i • (ε i • b i) := by rw [hdiag i]
        _ = b i := by rw [smul_smul, hsq (ε i) (hε i), one_smul]
        _ = (1 : V ≃ₗ[ZMod 3] V) (b i) := by simp
    rw [← map_mul, hww, map_one]
  have hKbot : K = ⊥ := by
    by_contra hK
    haveI hKnt : Nontrivial K := (Subgroup.nontrivial_iff_ne_bot K).mpr hK
    haveI hKn : K.Normal := hKnormal
    have hAle : alternatingGroup (Fin N) ≤ K :=
      Equiv.Perm.alternatingGroup_le_of_normal (α := Fin N) (by simpa using hN) (ntN := hKnt)
    obtain ⟨a, b, c, hab, hac, hbc⟩ : ∃ a b c : Fin N, a ≠ b ∧ a ≠ c ∧ b ≠ c := by
      refine ⟨⟨0, by omega⟩, ⟨1, by omega⟩, ⟨2, by omega⟩, ?_, ?_, ?_⟩
      · exact Fin.ne_of_lt (Fin.mk_lt_mk.mpr (by omega : (0 : ℕ) < 1))
      · exact Fin.ne_of_lt (Fin.mk_lt_mk.mpr (by omega : (0 : ℕ) < 2))
      · exact Fin.ne_of_lt (Fin.mk_lt_mk.mpr (by omega : (1 : ℕ) < 2))
    let ρ : Equiv.Perm (Fin N) := Equiv.swap a b * Equiv.swap a c
    have hcyc : ρ.IsThreeCycle := Equiv.Perm.isThreeCycle_swap_mul_swap_same hab hac hbc
    have hρK : ρ ∈ K := hAle hcyc.mem_alternatingGroup
    have hρ2 : ρ * ρ = 1 := hsqK ρ hρK
    have hdvd : orderOf ρ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr (by rw [pow_two]; exact hρ2)
    rw [hcyc.orderOf] at hdvd
    exact absurd hdvd (by norm_num)
  have hker : π.ker = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro w hw
    have hmem : e w ∈ K := Subgroup.mem_map.mpr ⟨w, hw, rfl⟩
    rw [hKbot] at hmem
    have hmem1 : e w = 1 := Subgroup.mem_bot.mp hmem
    have h1 : e w = e 1 := by rw [hmem1, map_one]
    exact e.injective h1
  have hπinj : Function.Injective π := (MonoidHom.ker_eq_bot_iff π).mp hker
  have hπbij : Function.Bijective π :=
    hπinj.bijective_of_nat_card_le (by rw [Nat.card_congr e.toEquiv])
  intro i j
  obtain ⟨w, hw⟩ := hπbij.2 (Equiv.swap i j)
  obtain ⟨ε, hε, hrepr⟩ := perm_spec w
  refine ⟨w, w.2, ε i, hε i, ?_⟩
  have hpi : perm w i = j := by
    have h' : perm w = Equiv.swap i j := hw
    rw [h', Equiv.swap_apply_left]
  rw [hrepr i, hpi]

end CFSG.StandardType

end
