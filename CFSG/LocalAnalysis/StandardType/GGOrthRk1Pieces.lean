module

public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Block
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1Defs

public section

open Module Multiplicative

namespace CFSG.StandardType

namespace OrthTorus

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

private lemma tbjOmPieces_toAdd_piMul (f : Fin r → Multiplicative (ZMod p)) (l : Fin r) :
    toAdd (piMul r p f) l = toAdd (f l) := by
  rw [piMul_apply, toAdd_ofAdd]

private lemma tbjOmPieces_mem_reflFixedCoord_single {i j k : Fin r} (hki : k ≠ i) (hkj : k ≠ j) :
    Pi.mulSingle k (ofAdd 1) ∈ reflFixedCoord p r i j := by
  change Pi.mulSingle k (ofAdd 1) ∈ MonoidHom.ker
    (Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) i /
      Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) j)
  rw [MonoidHom.mem_ker, MonoidHom.div_apply, Pi.evalMonoidHom_apply, Pi.evalMonoidHom_apply,
    div_eq_one, Pi.mulSingle_eq_of_ne (Ne.symm hki), Pi.mulSingle_eq_of_ne (Ne.symm hkj)]

omit [Finite K] [FiniteDimensional K V] in
theorem TBJOmData.rk1Block [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r) :
    Rk1Block Δ.c p :=
  ⟨Δ.finrank_D, Fact.out, hp2, Δ.c_pow, Δ.c_fix, Δ.c_twist⟩

omit [Finite K] [FiniteDimensional K V] in
theorem TBJOmData.tau_theta (Δ : TBJOmData Q p A r) (f : Fin r → Multiplicative (ZMod p))
    (k : Fin r) (d : Δ.D) : Δ.τ f (Δ.θ k d) = Δ.θ k ((Δ.c ^ (toAdd (f k)).val) d) := by
  rw [Δ.τ_eq, Δ.θ_act, tbjOmPieces_toAdd_piMul]

omit [Finite K] [FiniteDimensional K V] in
theorem TBJOmData.iSupIndep_U (Δ : TBJOmData Q p A r) : iSupIndep Δ.F.U := by
  rw [iSupIndep_def]
  intro i
  rw [Submodule.disjoint_def]
  intro u hu hu'
  refine Δ.F.nondeg i u hu fun v hv => ?_
  have hle : (⨆ j, ⨆ (_ : j ≠ i), Δ.F.U j) ≤
      LinearMap.ker ((QuadraticMap.polarBilin Q) v) := by
    refine iSup_le fun j => iSup_le fun hj => ?_
    intro w hw
    rw [LinearMap.mem_ker, QuadraticMap.polarBilin_apply_apply]
    exact Δ.F.orth i j (Ne.symm hj) v hv w hw
  have h0 := LinearMap.mem_ker.mp (hle hu')
  simpa [QuadraticMap.polarBilin_apply_apply] using h0

omit [Finite K] in
theorem TBJOmData.iSup_U_eq_top (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) : ⨆ k, Δ.F.U k = ⊤ := by
  let W : Submodule K V := ⨆ k, Δ.F.U k
  let φ : V →ₗ[K] W →ₗ[K] K :=
    ((QuadraticMap.polarBilin Q).flip).compl₁₂ (LinearMap.id) W.subtype
  have hφinj : Function.Injective φ := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro v hv
    have hv0 : φ v = 0 := LinearMap.mem_ker.mp hv
    apply hfix v
    intro a ha
    obtain ⟨s, rfl⟩ := Δ.F.exists_eq ha
    refine (Δ.F.fix s v).mpr fun j hj u hu => ?_
    have huv : φ v ⟨u, Submodule.mem_iSup_of_mem j hu⟩ = 0 := by
      rw [hv0, LinearMap.zero_apply]
    simpa [φ] using huv
  have hle : finrank K V ≤ finrank K W := by
    have h := LinearMap.finrank_le_finrank_of_injective (f := φ) hφinj
    rwa [Subspace.dual_finrank_eq] at h
  exact Submodule.eq_top_of_finrank_eq (le_antisymm (Submodule.finrank_le W) hle)

omit [Finite K] in
private theorem tbjOmPieces_tau_sub_mem [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0)
    (f : Fin r → Multiplicative (ZMod p)) {S : Submodule K V}
    (htriv : ∀ l, ¬ (Δ.F.U l ≤ S) → toAdd (piMul r p f) l = 0) :
    ∀ v : V, Δ.τ f v - v ∈ S := by
  have h : ∀ v : V, Δ.F.ι (piMul r p f) v - v ∈ S := by
    intro v
    have hv : v ∈ ⨆ l, Δ.F.U l := by
      rw [Δ.iSup_U_eq_top hfix]; exact Submodule.mem_top
    refine Submodule.iSup_induction (fun l => Δ.F.U l)
      (motive := fun x => Δ.F.ι (piMul r p f) x - x ∈ S) hv (fun l u hu => ?_) ?_ ?_
    · by_cases hl : Δ.F.U l ≤ S
      · exact S.sub_mem (hl (Δ.F.mapsTo (piMul r p f) l u hu)) (hl hu)
      · rw [Δ.F.triv (piMul r p f) l (htriv l hl) u hu, sub_self]
        exact S.zero_mem
    · rw [map_zero, sub_zero]; exact S.zero_mem
    · intro x y hx hy
      have h2 : Δ.F.ι (piMul r p f) (x + y) - (x + y) =
          (Δ.F.ι (piMul r p f) x - x) + (Δ.F.ι (piMul r p f) y - y) := by
        rw [map_add]; abel
      rw [h2]; exact S.add_mem hx hy
  intro v
  rw [Δ.τ_eq f]
  exact h v

omit [Finite K] in
private theorem tbjOmPieces_tau_surj [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (f : Fin r → Multiplicative (ZMod p)) (l : Fin r)
    (hl : toAdd (piMul r p f) l ≠ 0) :
    ∀ u ∈ Δ.F.U l, ∃ u' ∈ Δ.F.U l, Δ.τ f u' - u' = u := by
  intro u hu
  have hmaps : ∀ x ∈ Δ.F.U l, Δ.τ f x - x ∈ Δ.F.U l := by
    intro x hx
    rw [Δ.τ_eq f]
    exact (Δ.F.U l).sub_mem (Δ.F.mapsTo (piMul r p f) l x hx) hx
  let φ : Δ.F.U l →ₗ[K] Δ.F.U l := ((Δ.τ f).toLinearMap - 1).restrict hmaps
  have hφinj : Function.Injective φ := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨x, hx⟩ hx0
    have h1 : Δ.τ f x - x = 0 := by
      have h3 : (φ ⟨x, hx⟩ : V) = 0 := by rw [hx0]; rfl
      simpa [φ, LinearMap.restrict_apply] using h3
    rw [Δ.τ_eq f] at h1
    exact Subtype.ext (Δ.F.fpf (piMul r p f) l hl x hx (sub_eq_zero.mp h1))
  have hφsurj : Function.Surjective φ := LinearMap.injective_iff_surjective.mp hφinj
  obtain ⟨u', hu'⟩ := hφsurj ⟨u, hu⟩
  refine ⟨u', u'.2, ?_⟩
  have h3 : (φ u' : V) = u := by rw [hu']
  simpa [φ, LinearMap.restrict_apply] using h3

omit [Finite K] [FiniteDimensional K V] in
private theorem tbjOmPieces_mapsTo_of_sub (Δ : TBJOmData Q p A r)
    {f : Fin r → Multiplicative (ZMod p)} {g : V ≃ₗ[K] V}
    (hcomm : Δ.τ f * g = g * Δ.τ f) (S : Submodule K V)
    (hsub : ∀ v : V, Δ.τ f v - v ∈ S)
    (hsurj : ∀ u ∈ S, ∃ u' : V, Δ.τ f u' - u' = u) :
    ∀ u ∈ S, g u ∈ S := by
  intro u hu
  obtain ⟨u', hu'⟩ := hsurj u hu
  have hgy : g (Δ.τ f u') = Δ.τ f (g u') := by
    have h := congrArg (fun e : V ≃ₗ[K] V => e u') hcomm
    simpa [LinearEquiv.mul_apply] using h.symm
  rw [← hu', map_sub, hgy]
  exact hsub (g u')

omit [Finite K] in
theorem TBJOmData.centralizer_mapsTo [Fact p.Prime] (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j : Fin r) {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer (Δ.reflFixed i j : Set (V ≃ₗ[K] V))) :
    (∀ k, k ≠ i → k ≠ j → ∀ u ∈ Δ.F.U k, g u ∈ Δ.F.U k) ∧
      ∀ w ∈ Δ.F.U i ⊔ Δ.F.U j, g w ∈ Δ.F.U i ⊔ Δ.F.U j := by
  classical
  constructor
  · intro k hki hkj
    let f : Fin r → Multiplicative (ZMod p) := Pi.mulSingle k (ofAdd (1 : ZMod p))
    have hfmem : f ∈ reflFixedCoord p r i j := tbjOmPieces_mem_reflFixedCoord_single hki hkj
    have hcomm : Δ.τ f * g = g * Δ.τ f :=
      (Subgroup.mem_centralizer_iff.mp hg) _ (Subgroup.mem_map.mpr ⟨f, hfmem, rfl⟩)
    have htriv : ∀ l, ¬ (Δ.F.U l ≤ Δ.F.U k) → toAdd (piMul r p f) l = 0 := by
      intro l hl
      have hlk : l ≠ k := by rintro rfl; exact hl le_rfl
      rw [tbjOmPieces_toAdd_piMul]
      simp only [f]
      rw [Pi.mulSingle_eq_of_ne hlk, toAdd_one]
    have hsub := tbjOmPieces_tau_sub_mem Δ hfix f htriv
    have hsurj : ∀ u ∈ Δ.F.U k, ∃ u' : V, Δ.τ f u' - u' = u := by
      intro u hu
      obtain ⟨u', -, heq⟩ := tbjOmPieces_tau_surj Δ f k (by
        rw [tbjOmPieces_toAdd_piMul]
        simp only [f]
        rw [Pi.mulSingle_eq_same, toAdd_ofAdd]
        exact one_ne_zero) u hu
      exact ⟨u', heq⟩
    exact tbjOmPieces_mapsTo_of_sub Δ hcomm (Δ.F.U k) hsub hsurj
  · let f : Fin r → Multiplicative (ZMod p) :=
      fun l => if l = i ∨ l = j then ofAdd 1 else 1
    have hfmem : f ∈ reflFixedCoord p r i j := by
      change f ∈ MonoidHom.ker
        (Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) i /
          Pi.evalMonoidHom (fun _ : Fin r => Multiplicative (ZMod p)) j)
      rw [MonoidHom.mem_ker, MonoidHom.div_apply, Pi.evalMonoidHom_apply, Pi.evalMonoidHom_apply,
        div_eq_one]
      change (if i = i ∨ i = j then ofAdd (1 : ZMod p) else 1) =
        (if j = i ∨ j = j then ofAdd (1 : ZMod p) else 1)
      rw [if_pos (Or.inl rfl), if_pos (Or.inr rfl)]
    have hcomm : Δ.τ f * g = g * Δ.τ f :=
      (Subgroup.mem_centralizer_iff.mp hg) _ (Subgroup.mem_map.mpr ⟨f, hfmem, rfl⟩)
    have htriv : ∀ l, ¬ (Δ.F.U l ≤ Δ.F.U i ⊔ Δ.F.U j) → toAdd (piMul r p f) l = 0 := by
      intro l hl
      have hli : l ≠ i := by rintro rfl; exact hl le_sup_left
      have hlj : l ≠ j := by rintro rfl; exact hl le_sup_right
      rw [tbjOmPieces_toAdd_piMul]
      show toAdd (if l = i ∨ l = j then ofAdd (1 : ZMod p) else 1) = 0
      rw [if_neg (by rintro (h | h); exacts [hli h, hlj h]), toAdd_one]
    have hsub := tbjOmPieces_tau_sub_mem Δ hfix f htriv
    have hsi : toAdd (piMul r p f) i ≠ 0 := by
      rw [tbjOmPieces_toAdd_piMul]
      show toAdd (if i = i ∨ i = j then ofAdd (1 : ZMod p) else 1) ≠ 0
      rw [if_pos (Or.inl rfl), toAdd_ofAdd]
      exact one_ne_zero
    have hsj : toAdd (piMul r p f) j ≠ 0 := by
      rw [tbjOmPieces_toAdd_piMul]
      show toAdd (if j = i ∨ j = j then ofAdd (1 : ZMod p) else 1) ≠ 0
      rw [if_pos (Or.inr rfl), toAdd_ofAdd]
      exact one_ne_zero
    have hsurj : ∀ u ∈ Δ.F.U i ⊔ Δ.F.U j, ∃ u' : V, Δ.τ f u' - u' = u := by
      intro u hu
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨a', -, ha'eq⟩ := tbjOmPieces_tau_surj Δ f i hsi a ha
      obtain ⟨b', -, hb'eq⟩ := tbjOmPieces_tau_surj Δ f j hsj b hb
      exact ⟨a' + b', by rw [map_add, add_sub_add_comm, ha'eq, hb'eq]⟩
    exact tbjOmPieces_mapsTo_of_sub Δ hcomm (Δ.F.U i ⊔ Δ.F.U j) hsub hsurj

omit [Finite K] in
theorem TBJOmData.centralizer_two_fix [Fact p.Prime] (hp2 : p ≠ 2) (Δ : TBJOmData Q p A r)
    (hfix : ∀ v : V, (∀ a ∈ A, a v = v) → v = 0) (i j : Fin r) {g : V ≃ₗ[K] V}
    (hg : g ∈ Subgroup.centralizer (Δ.reflFixed i j : Set (V ≃ₗ[K] V))) {m : ℕ}
    (hm : g ^ (2 ^ m) = 1) (k : Fin r) (hki : k ≠ i) (hkj : k ≠ j) :
    ∀ u ∈ Δ.F.U k, g u = u := by
  classical
  have hgmap : ∀ u ∈ Δ.F.U k, g u ∈ Δ.F.U k :=
    (Δ.centralizer_mapsTo hfix i j hg).1 k hki hkj
  let f : Fin r → Multiplicative (ZMod p) := Pi.mulSingle k (ofAdd (1 : ZMod p))
  have hfmem : f ∈ reflFixedCoord p r i j := tbjOmPieces_mem_reflFixedCoord_single hki hkj
  have hcomm : Δ.τ f * g = g * Δ.τ f :=
    (Subgroup.mem_centralizer_iff.mp hg) _ (Subgroup.mem_map.mpr ⟨f, hfmem, rfl⟩)
  have hyθ : ∀ d : Δ.D, Δ.τ f (Δ.θ k d) = Δ.θ k (Δ.c d) := by
    intro d
    have hval : (toAdd (f k)).val = 1 := by
      have hp : p.Prime := Fact.out
      have h1 : toAdd (f k) = (1 : ZMod p) := by
        simp only [f]
        rw [Pi.mulSingle_eq_same, toAdd_ofAdd]
      rw [h1]
      exact ZMod.val_one'' hp.ne_one
    rw [Δ.tau_theta f k d, hval, pow_one]
  let e : Δ.D ≃ₗ[K] LinearMap.range (Δ.θ k) := LinearEquiv.ofInjective (Δ.θ k) (Δ.θ_inj k)
  have hrange : ∀ d : Δ.D, (g.toLinearMap ∘ₗ Δ.θ k) d ∈ LinearMap.range (Δ.θ k) := by
    intro d
    rw [Δ.θ_range k]
    have hd : Δ.θ k d ∈ Δ.F.U k := by
      rw [← Δ.θ_range k]
      exact (LinearMap.mem_range).mpr ⟨d, rfl⟩
    exact hgmap _ hd
  let ψ : Δ.D →ₗ[K] LinearMap.range (Δ.θ k) :=
    LinearMap.codRestrict (LinearMap.range (Δ.θ k)) (g.toLinearMap ∘ₗ Δ.θ k) hrange
  let g' : Module.End K Δ.D := e.symm.toLinearMap ∘ₗ ψ
  have hg' : ∀ d : Δ.D, Δ.θ k (g' d) = g (Δ.θ k d) := by
    intro d
    change Δ.θ k (e.symm (ψ d)) = g (Δ.θ k d)
    rw [LinearEquiv.ofInjective_symm_apply]
    rfl
  have hgc : g' ∘ₗ (Δ.c : Δ.D →ₗ[K] Δ.D) = (Δ.c : Δ.D →ₗ[K] Δ.D) ∘ₗ g' := by
    ext d
    apply Δ.θ_inj k
    calc Δ.θ k ((g' ∘ₗ (Δ.c : Δ.D →ₗ[K] Δ.D)) d)
        = Δ.θ k (g' (Δ.c d)) := rfl
      _ = g (Δ.θ k (Δ.c d)) := hg' (Δ.c d)
      _ = g (Δ.τ f (Δ.θ k d)) := by rw [← hyθ d]
      _ = Δ.τ f (g (Δ.θ k d)) := by
            have h := congrArg (fun e : V ≃ₗ[K] V => e (Δ.θ k d)) hcomm
            simpa [LinearEquiv.mul_apply] using h.symm
      _ = Δ.τ f (Δ.θ k (g' d)) := by rw [← hg' d]
      _ = Δ.θ k (Δ.c (g' d)) := hyθ (g' d)
      _ = Δ.θ k (((Δ.c : Δ.D →ₗ[K] Δ.D) ∘ₗ g') d) := rfl
  have hpow : ∀ n : ℕ, ∀ d : Δ.D, Δ.θ k ((g' ^ n) d) = (g ^ n) (Δ.θ k d) := by
    intro n
    induction n with
    | zero => intro d; simp
    | succ n ih =>
      intro d
      rw [pow_succ, Module.End.mul_apply, ih (g' d), hg' d, ← LinearEquiv.mul_apply, ← pow_succ]
  have hg'pow : g' ^ (2 ^ m) = 1 := by
    ext d
    apply Δ.θ_inj k
    rw [hpow (2 ^ m) d, hm]
    simp
  have hg'one : g' = 1 := (Δ.rk1Block hp2).eq_one_of_commute hgc hg'pow
  intro u hu
  rw [← Δ.θ_range k, LinearMap.mem_range] at hu
  obtain ⟨d, rfl⟩ := hu
  rw [← hg' d, hg'one]
  simp

end OrthTorus

end CFSG.StandardType

end
