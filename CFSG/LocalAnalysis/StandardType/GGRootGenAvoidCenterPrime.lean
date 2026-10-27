module

public import CFSG.LocalAnalysis.StandardType.GGTorusRootGenAvoidModel
public import CFSG.LocalAnalysis.StandardType.GGTwE6WeylTorusTransferCore
public import CFSG.LocalAnalysis.StandardType.GGRootGenAvoidInduced
public import CFSG.LocalAnalysis.StandardType.GGTorusInducedTransfer
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenCover

public section

namespace CFSG.StandardType

open CFSG.Assembly TableB

private theorem exists_toAddCoords_of_ggTorusModelAt {p : ℕ} {G : Type} [Group G]
    {E : Subgroup G} (h : GGTorusModelAt p E) :
    ∃ (k : ℕ) (τ : Multiplicative (Fin k → ZMod p) →* G) (ι : Type) (w : ι → G)
      (s : ι → MulAut (Multiplicative (Fin k → ZMod p))) (S : ι → Subgroup G),
      Nonempty ι ∧ Function.Injective τ ∧ τ.range = E ∧
      (∀ i f, w i * τ f * (w i)⁻¹ = τ (s i f)) ∧ (∀ i, s i * s i = 1) ∧
      (∀ i, Nat.card {f // s i f = f} * p = p ^ k) ∧ Function.Injective s ∧
      (∀ i, w i ∈ S i) ∧
      (∀ i, IsComponentOf (S i) (Subgroup.centralizer (τ '' {f | s i f = f}))) ∧
      (∀ i, p ∣ Nat.card (S i)) ∧ ∀ j, (⨆ (i : ι) (_ : i ≠ j), S i) = ⊤ := by
  obtain ⟨k, τ, ι, w, s, S, hι, hτ, hτE, hws, hs, hfix, hsinj, hwS, hcomp, hdvd, hgen⟩ := h
  let ε : Multiplicative (Fin k → ZMod p) ≃* (Fin k → Multiplicative (ZMod p)) :=
    MulEquiv.piMultiplicative _
  let τ' : Multiplicative (Fin k → ZMod p) →* G := τ.comp ε.toMonoidHom
  have hrange : τ'.range = τ.range := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr ε.surjective,
      ← MonoidHom.range_eq_map]
  let s' : ι → MulAut (Multiplicative (Fin k → ZMod p)) := fun i => MulAut.congr ε.symm (s i)
  have hs'app : ∀ i f, s' i f = ε.symm (s i (ε f)) := fun i f => rfl
  have hfix' : ∀ i, Nat.card {f // s' i f = f} * p = p ^ k := by
    intro i
    have h1 : Nat.card {f // s' i f = f} = Nat.card {g // s i g = g} := by
      refine Nat.card_congr (Equiv.subtypeEquiv ε.toEquiv fun f => ?_)
      rw [hs'app]
      constructor
      · intro h
        have h2 := congrArg ε h
        rwa [MulEquiv.apply_symm_apply] at h2
      · intro h
        change s i (ε f) = ε f at h
        change ε.symm (s i (ε f)) = f
        rw [h, MulEquiv.symm_apply_apply]
    have h2 : Nat.card (Fin k → Multiplicative (ZMod p)) = p ^ k := by
      rw [← Nat.card_congr ε.toEquiv,
        Nat.card_congr (Multiplicative.toAdd : Multiplicative (Fin k → ZMod p) ≃ _),
        Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card (α := Fin k), Fintype.card_fin]
    rw [h1, hfix i, h2]
  have hset : ∀ i, τ' '' {f | s' i f = f} = τ '' {g | s i g = g} := by
    intro i
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      refine ⟨ε u, ?_, rfl⟩
      simpa [hs'app] using congrArg ε hu
    · rintro ⟨g, hg, rfl⟩
      refine ⟨ε.symm g, ?_, ?_⟩
      · simpa [hs'app] using congrArg ε.symm hg
      · rw [show τ' (ε.symm g) = τ (ε (ε.symm g)) from rfl, MulEquiv.apply_symm_apply]
  refine ⟨k, τ', ι, w, s', S, hι, hτ.comp ε.injective, hrange.trans hτE, fun i f => ?_,
    fun i => ?_, hfix', fun i j h => hsinj ((MulAut.congr ε.symm).injective h), hwS,
    fun i => by rw [hset i]; exact hcomp i, hdvd, hgen⟩
  · change w i * τ (ε f) * (w i)⁻¹ = τ (ε (s' i f))
    rw [hs'app, MulEquiv.apply_symm_apply]
    exact hws i (ε f)
  · ext f
    rw [MulAut.mul_apply, hs'app, hs'app, MulEquiv.apply_symm_apply, ← MulAut.mul_apply, hs i,
      MulAut.one_apply, MulEquiv.symm_apply_apply, MulAut.one_apply]

theorem ggTorusRootGenAvoid_map_conj_of_torusModelAt {p : ℕ} (hp : p.Prime) {G : Type} [Group G]
    [Finite G] (hZ : Subgroup.center G = ⊥) {E : Subgroup G} (h : GGTorusModelAt p E) :
    GGTorusRootGenAvoid p (E.map (MulAut.conj : G →* MulAut G)) := by
  classical
  obtain ⟨k, τ, ι, w, s, S, hι, hτ, hτE, hws, hs, hfix, hsinj, hwS, hcomp, hdvd, hgen⟩ :=
    exists_toAddCoords_of_ggTorusModelAt h
  haveI : Nonempty ι := hι
  let f : ι → (Fin k → ZMod p) → Fin k → ZMod p :=
    fun i t => Multiplicative.toAdd (s i (Multiplicative.ofAdd t))
  have hss : ∀ i u, s i (s i u) = u := by
    intro i u
    have h := congrArg (fun m : MulAut (Multiplicative (Fin k → ZMod p)) => m u) (hs i)
    simpa only [MulAut.mul_apply, MulAut.one_apply] using h
  have harg : ∀ i t, Multiplicative.ofAdd (f i t) = s i (Multiplicative.ofAdd t) :=
    fun i t => ofAdd_toAdd _
  have hw : ∀ i t, w i * τ (Multiplicative.ofAdd t) * (w i)⁻¹ =
      τ (Multiplicative.ofAdd (f i t)) := by
    intro i t
    rw [harg i t]
    exact hws i (Multiplicative.ofAdd t)
  have hinv : ∀ i t, f i (f i t) = t := by
    intro i t
    calc f i (f i t) = Multiplicative.toAdd (s i (Multiplicative.ofAdd (f i t))) := rfl
      _ = Multiplicative.toAdd (s i (s i (Multiplicative.ofAdd t))) := by rw [harg i t]
      _ = Multiplicative.toAdd (Multiplicative.ofAdd t) := by rw [hss i]
      _ = t := toAdd_ofAdd t
  have hinjf : Function.Injective f := by
    intro i j hij
    refine hsinj ?_
    refine MulEquiv.ext fun u => ?_
    have h2 : ∀ t, s i (Multiplicative.ofAdd t) = s j (Multiplicative.ofAdd t) := by
      intro t
      simpa only [f, ofAdd_toAdd] using congrArg Multiplicative.ofAdd (congrFun hij t)
    calc s i u = s i (Multiplicative.ofAdd (Multiplicative.toAdd u)) := by rw [ofAdd_toAdd]
      _ = s j (Multiplicative.ofAdd (Multiplicative.toAdd u)) := h2 _
      _ = s j u := by rw [ofAdd_toAdd]
  have hfixf : ∀ i, Nat.card {t : Fin k → ZMod p // f i t = t} * p = p ^ k := by
    intro i
    have h1 : Nat.card {t : Fin k → ZMod p // f i t = t} =
        Nat.card {u : Multiplicative (Fin k → ZMod p) // s i u = u} := by
      refine Nat.card_congr (Equiv.subtypeEquiv Multiplicative.ofAdd fun t => ?_)
      constructor
      · intro ht
        simpa only [f, ofAdd_toAdd] using congrArg Multiplicative.ofAdd ht
      · intro ht
        simpa only [f, toAdd_ofAdd] using congrArg Multiplicative.toAdd ht
    rw [h1]
    exact hfix i
  have hcompf : ∀ i, IsComponentOf (S i)
      (Subgroup.centralizer (SuSplitRootGen.torusFix τ (f i))) := by
    intro i
    have htor : SuSplitRootGen.torusFix τ (f i) = τ '' {u | s i u = u} := by
      ext x
      constructor
      · rintro ⟨u, hu, rfl⟩
        refine ⟨u, ?_, rfl⟩
        rw [Set.mem_setOf_eq] at hu ⊢
        exact Multiplicative.toAdd.injective (by simpa only [f, ofAdd_toAdd] using hu)
      · rintro ⟨u, hu, rfl⟩
        refine ⟨u, ?_, rfl⟩
        rw [Set.mem_setOf_eq] at hu ⊢
        simpa only [f, hu, ofAdd_toAdd]
    rw [htor]
    exact hcomp i
  have hgenf : ∀ j, (⨆ (i : ι) (_ : f i ≠ f j), S i) = ⊤ := by
    intro j
    refine le_antisymm le_top ?_
    rw [← hgen j]
    refine iSup_le fun i => iSup_le fun hi => ?_
    exact le_iSup_of_le i (le_iSup_of_le (fun h => hi (hinjf h)) le_rfl)
  have hM : SuSplitRootGen.IsCoverTorusModel (MonoidHom.id G) τ
      (E.map (MulAut.conj : G →* MulAut G)) := by
    intro a
    constructor
    · intro ha
      rw [Subgroup.mem_map] at ha
      obtain ⟨e, he, hea⟩ := ha
      have he' : e ∈ τ.range := hτE.symm ▸ he
      obtain ⟨t, ht⟩ := MonoidHom.mem_range.mp he'
      refine ⟨t, ?_⟩
      rw [← hea, ← ht]
      rfl
    · rintro ⟨t, rfl⟩
      rw [Subgroup.mem_map]
      exact ⟨τ t, hτE ▸ MonoidHom.mem_range.mpr ⟨t, rfl⟩, rfl⟩
  have hτc : ∀ t, (MonoidHom.id G) (τ t) ∈ Subgroup.center G → t = 1 := by
    intro t ht
    have h1 : τ t = 1 := by simpa [hZ] using ht
    exact hτ (by rw [h1, map_one])
  refine SuSplitRootGen.ggTorusRootGenAvoid_of_cover (H := G) (L' := G) (s := k) hp
    (φ := MonoidHom.id G) (τ := τ) (A := E.map (MulAut.conj : G →* MulAut G))
    (fun x => ⟨x, rfl⟩) ?_ ?_ hM hτc w f S hw hinv hfixf hwS hcompf hdvd hgenf
  · intro z hz
    have hz1 : z = 1 := by simpa using hz
    rw [hz1]
    exact Subgroup.one_mem _
  · intro z hz _
    simpa using hz

theorem ggTorusRootGenAvoidKG_of_scTorusModel_centerPrime {p r : ℕ} (hp : p.Prime) {G : Type}
    [Group G] [Finite G] {I : Set (MulAut G)} (hZ : Subgroup.center G = ⊥)
    (hIp : GGOutdiagPrime p G I) (hcp : GGCenterPrime p G)
    (hmodel : ∀ E : Subgroup G, IsElemAbelian p E → p ^ r ≤ Nat.card E → p ^ 3 ≤ Nat.card E →
      (∀ g : G, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → GGTorusModelAt p E) :
    GGTorusRootGenAvoidKG p r G I := by
  classical
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap, hAΛ, hEab, hcardE, hscE⟩ :=
    TwE6TB.exists_innerModel hp hZ hIp hcp ψ hψ hker hperf hA hAI hsc
  have hΛn : ∀ x : L', Λ (ψ x) = MulAut.conj x := fun x => hΛeq rfl
  have hmodelE : GGTorusModelAt p (A.comap Λ) :=
    hmodel (A.comap Λ) hEab (by rw [hcardE]; exact hr) (by rw [hcardE]; exact h3) hscE
  have hroot : GGTorusRootGenAvoid p ((A.comap Λ).map (MulAut.conj : G →* MulAut G)) :=
    ggTorusRootGenAvoid_map_conj_of_torusModelAt hp hZ hmodelE
  have hinn : ∀ a ∈ A, ∃ x : L', a = MulAut.conj x := by
    intro a ha
    obtain ⟨e, he⟩ := hAΛ a ha
    obtain ⟨x, hx⟩ := hψ e
    have hxe : Λ e = MulAut.conj x := by rw [← hx]; exact hΛn x
    exact ⟨x, he.symm.trans hxe⟩
  have hsub : TypeA.inducedSub ψ A =
      (A.comap Λ).map (MulAut.conj : G →* MulAut G) :=
    TypeA.inducedSub_eq_map_conj_of_lift hψ Λ hΛmap hAΛ
  have hcomm : ∀ x y : L', MulAut.conj x ∈ A → MulAut.conj y ∈ A → x * y = y * x := by
    intro x y hx hy
    have hxE : ψ x ∈ A.comap Λ := by
      rw [Subgroup.mem_comap]
      rw [hΛn x]
      exact hx
    have hyE : ψ y ∈ A.comap Λ := by
      rw [Subgroup.mem_comap]
      rw [hΛn y]
      exact hy
    have hxy : ψ x * ψ y = ψ y * ψ x :=
      TableB.IsElemAbelian.comm hEab hxE hyE
    have hcpL : ¬ p ∣ Nat.card (Subgroup.center L') := hcp L' ψ hψ hker hperf
    have hyp : (ψ y) ^ p = 1 := hEab.2 (ψ y) hyE
    obtain ⟨y₀, hy₀, hy₀p⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hyp
    have hxy₀ : ψ x * ψ y₀ = ψ y₀ * ψ x := by
      rw [hy₀]
      exact hxy
    have hcomm₀ : x * y₀ = y₀ * x := commute_of_lift_pow_eq_one hp hker hcpL hxy₀ hy₀p
    have hzc : y₀⁻¹ * y ∈ Subgroup.center L' := by
      refine hker ?_
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy₀]
      exact inv_mul_cancel _
    have hxz : x * (y₀⁻¹ * y) = (y₀⁻¹ * y) * x :=
      Subgroup.mem_center_iff.mp hzc x
    calc x * y = x * (y₀ * (y₀⁻¹ * y)) := by group
      _ = (x * y₀) * (y₀⁻¹ * y) := by group
      _ = (y₀ * x) * (y₀⁻¹ * y) := by rw [hcomm₀]
      _ = y₀ * (x * (y₀⁻¹ * y)) := by group
      _ = y₀ * ((y₀⁻¹ * y) * x) := by rw [hxz]
      _ = y * x := by group
  exact ggTorusRootGenAvoid_of_inducedSub hψ hker hperf hA hinn hcomm (hsub.symm ▸ hroot)

end CFSG.StandardType
