module

public import CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6.TBAssembly
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2ExcMonomial

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin.SmithCurtis
  CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Minuscule
  CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisTw
  CFSG.HardMathSupport.Cooperstein.Coordinator.TwE6

section Words

variable {k V ι : Type} [Field k] [AddCommGroup V] [Module k V]

private theorem le_finrank_range_sub_one_of_words [Module.Finite k V] (A : Module.End k V)
    (e : List ι → V) (s : List ι) (L : List (List ι))
    (hli : LinearIndependent k (fun j : Fin (L ++ L.map (s ++ ·)).length =>
      e (L ++ L.map (s ++ ·))[j]))
    (hA : ∀ w, ∃ c : k, A (e w) = c • e (s ++ w)) :
    L.length ≤ Module.finrank k (LinearMap.range (A - 1)) := by
  have hlen : (L ++ L.map (s ++ ·)).length = L.length + L.length := by simp
  let g : Fin L.length ⊕ Fin L.length → Fin (L ++ L.map (s ++ ·)).length
    | Sum.inl i => ⟨i.1, by omega⟩
    | Sum.inr i => ⟨L.length + i.1, by omega⟩
  have hg : Function.Injective g := by
    rintro (i | i) (j | j) h <;> simp only [g, Fin.mk.injEq] at h
    · exact congrArg Sum.inl (Fin.ext h)
    · omega
    · omega
    · exact congrArg Sum.inr (Fin.ext (by omega))
  have hfun : (fun j : Fin (L ++ L.map (s ++ ·)).length => e (L ++ L.map (s ++ ·))[j]) ∘ g =
      Sum.elim (fun i : Fin L.length => e L[i]) (fun i => e (s ++ L[i])) := by
    funext x
    rcases x with i | i
    · simp [g, List.getElem_append_left]
    · simp [g, List.getElem_append_right]
  have hli2 := hli.comp g hg
  rw [hfun] at hli2
  choose c hc using fun i : Fin L.length => hA L[i]
  exact le_finrank_range_sub_one_of_pairs A _ _ hli2 c hc

end Words


variable {f : ℕ} (hf : 1 ≤ f) {K : Type} [Field K] [Finite K] [CharP K 2]
  (hK : Nat.card K = (2 ^ f) ^ 2) (σ : K →+* K) (hσ : ∀ c, σ c = c ^ (2 ^ f))

theorem tw2e6_linearIndependent_translates {k : Type} [Field k] [Finite k] [CharP k 2]
    [Algebra K k] {m : ℕ} {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)}
    (hρ : IsSimpleRep ρ) {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k}
    {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    {v : Fin TwistTag.E6.foldedTag.rank → ℤ}
    (hv : ∀ j : Fin TwistTag.E6.foldedTag.rank, reflect TwistTag.E6.foldedTag j v ≠ v → j ∉ J)
    (L : List (List (Fin TwistTag.E6.foldedTag.rank)))
    (hL : (L.map fun w => w.foldr (reflect TwistTag.E6.foldedTag) v).Nodup) :
    LinearIndependent k (fun i : Fin L.length =>
      ρ ((twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd L[i])) y) := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ (twistedCover_split hf hK σ hσ k)
  let w : Fin L.length → ↥(relWeylTwist TwistTag.E6) :=
    fun i => (relCs TwistTag.E6).wordProd L[i]
  have hfw : ∀ i, foldedWeylEquiv TwistTag.E6 (w i) • v =
      L[i].foldr (reflect TwistTag.E6.foldedTag) v := fun i => by
    show foldedWeylEquiv TwistTag.E6 ((relCs TwistTag.E6).wordProd L[i]) • v = _
    rw [relCs_wordProd, wordProd_smul_foldr]
  have hinj : ∀ i j : Fin L.length, i ≠ j →
      foldedWeylEquiv TwistTag.E6 (w i) • v ≠ foldedWeylEquiv TwistTag.E6 (w j) • v := by
    intro i j hij h
    rw [hfw, hfw] at h
    refine hij (Fin.ext ?_)
    exact (List.Nodup.getElem_inj_iff hL (i := i.1) (j := j.1)
      (hi := by simp) (hj := by simp)).1 (by simpa [List.getElem_map] using h)
  refine CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisExc.linearIndependent_translates
    hρ hμ w (fun i j hij ω hω hωe => ?_)
  have hne : (coxeterSystem TwistTag.E6.foldedTag).wordProd
      (ω : List (Fin TwistTag.E6.foldedTag.rank)) • v ≠ v := by
    intro h
    apply hinj i j hij
    rw [← relCs_wordProd, hωe, map_mul, map_inv, mul_smul] at h
    have := congrArg (fun z => foldedWeylEquiv TwistTag.E6 (w i) • z) h
    simpa [smul_smul] using this.symm
  obtain ⟨l, hl, hlv⟩ := exists_letter_moving hne
  have : Fintype (orbitField TwistTag.E6 K σ l)ˣ := Fintype.ofFinite _
  exact ⟨l, hl, IsCoverType.mu_eq_dScalar (twistedCover_hodd hf hK σ hσ) ht hμ (hv l hlv)⟩

theorem tw2e6_exists_smul_translate {k V : Type} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) V} {y : V}
    {χ : ↥(TwistedE6.fixedGroup K σ) → k} {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    (s : List (Fin TwistTag.E6.foldedTag.rank)) {z : ↥(TwistedE6.fixedGroup K σ)}
    (hz : ((twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd s))⁻¹ * z ∈
      (twistedE6CoverData hf hK σ hσ).datum.H)
    (w : List (Fin TwistTag.E6.foldedTag.rank)) :
    ∃ c : k, ρ z (ρ ((twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd w)) y) =
      c • ρ ((twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd (s ++ w))) y := by
  let ns := (twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd s)
  let nw := (twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd w)
  let h : ↥(TwistedE6.fixedGroup K σ) := ns⁻¹ * z
  have hhH : h ∈ (twistedE6CoverData hf hK σ hσ).datum.H := hz
  let h' : ↥(TwistedE6.fixedGroup K σ) := nw⁻¹ * h * nw
  have hnW : (twistedE6CoverData hf hK σ hσ).datum.nW =
      (twistedE6CoverData hf hK σ hσ).nhatW := rfl
  have hh'H : h' ∈ (twistedE6CoverData hf hK σ hσ).datum.H := by
    have := (twistedE6CoverData hf hK σ hσ).datum.nW_normH
      ((relCs TwistTag.E6).wordProd w) hhH
    rw [hnW] at this
    simpa [h', nw] using this
  have hchi : ρ h' y = χ h' • y := ht.2.2.1 h' hh'H
  have hprod : (twistedE6CoverData hf hK σ hσ).nhatW
      ((relCs TwistTag.E6).wordProd (s ++ w)) = ns * nw := by
    dsimp only [ns, nw]
    rw [twNhatW_wordProd hf K hK σ hσ, twNhatW_wordProd hf K hK σ hσ,
      twNhatW_wordProd hf K hK σ hσ, List.map_append, List.prod_append]
  have hzsplit : z * nw = ns * nw * h' := by
    dsimp only [h', h]
    group
  refine ⟨χ h', ?_⟩
  calc
    ρ z (ρ nw y) = ρ (z * nw) y := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (ns * nw * h') y := by rw [hzsplit]
    _ = ρ (ns * nw) (ρ h' y) := by rw [map_mul, Module.End.mul_apply]
    _ = ρ (ns * nw) (χ h' • y) := by rw [hchi]
    _ = χ h' • ρ (ns * nw) y := by rw [map_smul]
    _ = χ h' • ρ ((twistedE6CoverData hf hK σ hσ).nhatW
        ((relCs TwistTag.E6).wordProd (s ++ w))) y := by rw [hprod]

theorem tw2e6_le_finrank_range_sub_one {k : Type} [Field k] [Finite k] [CharP k 2] [Algebra K k]
    {m : ℕ} {ρ : Representation k ↥(TwistedE6.fixedGroup K σ) (Fin m → k)} (hρ : IsSimpleRep ρ)
    {y : Fin m → k} {χ : ↥(TwistedE6.fixedGroup K σ) → k}
    {J : Finset (Fin TwistTag.E6.foldedTag.rank)}
    (ht : IsCoverType (twistedE6CoverRankOne hf hK σ hσ) ρ y χ J)
    {v : Fin TwistTag.E6.foldedTag.rank → ℤ}
    (hv : ∀ j : Fin TwistTag.E6.foldedTag.rank, reflect TwistTag.E6.foldedTag j v ≠ v → j ∉ J)
    (s : List (Fin TwistTag.E6.foldedTag.rank)) {z : ↥(TwistedE6.fixedGroup K σ)}
    (hz : ((twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd s))⁻¹ * z ∈
      (twistedE6CoverData hf hK σ hσ).datum.H)
    (L : List (List (Fin TwistTag.E6.foldedTag.rank)))
    (hL : (L.map (fun w => w.foldr (reflect TwistTag.E6.foldedTag) v) ++
      L.map (fun w => (s ++ w).foldr (reflect TwistTag.E6.foldedTag) v)).Nodup) :
    L.length ≤ Module.finrank k (LinearMap.range (ρ z - 1)) := by
  have hL' : ((L ++ L.map (s ++ ·)).map fun w =>
      w.foldr (reflect TwistTag.E6.foldedTag) v).Nodup := by
    simpa only [List.map_append, List.map_map, Function.comp_def] using hL
  exact le_finrank_range_sub_one_of_words (ρ z)
    (fun w => ρ ((twistedE6CoverData hf hK σ hσ).nhatW ((relCs TwistTag.E6).wordProd w)) y) s L
    (tw2e6_linearIndependent_translates hf hK σ hσ hρ ht hv _ hL')
    (fun w => tw2e6_exists_smul_translate hf hK σ hσ ht s hz w)

end CFSG.LocalAnalysis.WeakClosure81
