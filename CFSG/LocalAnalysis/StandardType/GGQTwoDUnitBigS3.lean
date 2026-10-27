module

public import CFSG.LocalAnalysis.StandardType.GGFrameRoutePortP9Sp
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigAD
public import CFSG.LocalAnalysis.StandardType.GGQTwoDUnitBigS1

public section

namespace CFSG.StandardType.QTwo

open CFSG.Open CFSG.RankThree.Classical

theorem qtwoDB44_generic_fixed {m : ℕ} (hm : 6 ≤ m) {c : Fin m}
    {L : Type} [Field L] [Algebra (ZMod 2) L] {ζ : L} (hζ : IsPrimitiveRoot ζ 3)
    (τ : Multiplicative (DVec m) →* StatedSp (m - 1) (ZMod 2))
    (hτker : ∀ v : DVec m, τ (Multiplicative.ofAdd v) = 1 ↔ ∀ i, i ≠ c → v i = 0)
    (hW : ∀ w ∈ dEvenStab m (Pi.single c 1), ∃ y : StatedSp (m - 1) (ZMod 2),
      ∀ v : DVec m, y * τ (Multiplicative.ofAdd v) * y⁻¹ = τ (Multiplicative.ofAdd (w v)))
    (F : ChoiceTwo.SpFrame (ZMod 2) (m - 1) ζ τ.range) (hs : F.s = m - 1)
    {u : DVec m} (hu : ∀ i, i ≠ c → u i ≠ 0) :
    ∀ x, spEnd (τ (Multiplicative.ofAdd u)) x = x → x = 0 := by
  classical
  have hζ3 : ζ ^ 3 = 1 := hζ.pow_eq_one
  let Λfun : DVec m → (Fin F.s → ZMod 3) := fun u =>
    Classical.choose (F.mem_tor (τ (Multiplicative.ofAdd u))
      (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd u, rfl⟩))
  have hΛfun : ∀ u, F.tor (Λfun u) = τ (Multiplicative.ofAdd u) := fun u =>
    Classical.choose_spec (F.mem_tor (τ (Multiplicative.ofAdd u))
      (MonoidHom.mem_range.mpr ⟨Multiplicative.ofAdd u, rfl⟩))
  let Λ : DVec m →+ (Fin F.s → ZMod 3) :=
    { toFun := Λfun
      map_zero' := by
        apply F.tor_injective hζ
        rw [hΛfun 0, F.tor_zero]
        exact (hτker 0).mpr fun i _ => rfl
      map_add' := fun u u' => by
        apply F.tor_injective hζ
        rw [F.tor_add hζ3, hΛfun (u + u'), hΛfun u, hΛfun u']
        rw [show Multiplicative.ofAdd (u + u') =
          Multiplicative.ofAdd u * Multiplicative.ofAdd u' from rfl, map_mul] }
  have hΛ : ∀ u, F.tor (Λ u) = τ (Multiplicative.ofAdd u) := fun u => hΛfun u
  let Λlin : DVec m →ₗ[ZMod 3] (Fin F.s → ZMod 3) := AddMonoidHom.toZModLinearMap 3 Λ
  let φ : Fin F.s → (DVec m →ₗ[ZMod 3] ZMod 3) := fun j => (LinearMap.proj j).comp Λlin
  have hφ_apply : ∀ (j : Fin F.s) (v : DVec m), φ j v = Λ v j := fun _ _ => rfl
  let H : Fin F.s → Submodule (ZMod 3) (DVec m) := fun j => LinearMap.ker (φ j)
  let I : Finset (Submodule (ZMod 3) (DVec m)) := Finset.univ.image H
  have hker : ∀ v : DVec m, Λ v = 0 ↔ ∀ i, i ≠ c → v i = 0 := by
    intro v
    constructor
    · intro h
      refine (hτker v).mp ?_
      rw [← hΛ v, h]
      exact F.tor_zero
    · intro h
      apply F.tor_injective hζ
      rw [hΛ v, F.tor_zero]
      exact (hτker v).mpr h
  have hsurj : ∀ f : Fin F.s → ZMod 3, ∃ v : DVec m, Λ v = f := by
    intro f
    have hmem : F.tor f ∈ τ.range := F.tor_mem f
    rw [MonoidHom.mem_range] at hmem
    obtain ⟨g, hg⟩ := hmem
    exact ⟨Multiplicative.toAdd g, by
      apply F.tor_injective hζ
      rw [hΛ]
      exact hg⟩
  have hI : ∀ K ∈ I, Pi.single c 1 ∈ K ∧ Module.finrank (ZMod 3) K = m - 1 := by
    intro K hK
    rw [Finset.mem_image] at hK
    obtain ⟨j, _, rfl⟩ := hK
    constructor
    · rw [LinearMap.mem_ker, hφ_apply]
      have h0 : Λ (Pi.single c 1) = 0 :=
        (hker _).mpr fun i hi => by
          simp [Pi.single_eq_of_ne (M := fun _ => ZMod 3) hi 1]
      rw [h0, Pi.zero_apply]
    · have hφj : φ j ≠ 0 := by
        obtain ⟨v, hv⟩ := hsurj (Pi.single j 1)
        intro hzero
        have h1 : φ j v = 0 := by rw [hzero]; rfl
        rw [hφ_apply, hv] at h1
        simpa using h1
      have hfin := Module.Dual.finrank_ker_add_one_of_ne_zero hφj
      rw [show Module.finrank (ZMod 3) (DVec m) = m from
        Module.finrank_fin_fun (ZMod 3)] at hfin
      change Module.finrank (ZMod 3) (LinearMap.ker (φ j)) = m - 1
      omega
  have hHinj : Function.Injective H := by
    intro j k hjk
    by_contra hne
    obtain ⟨v, hv⟩ := hsurj (Pi.single j 1)
    have hvj : v ∉ H j := by
      rw [LinearMap.mem_ker, hφ_apply, hv]
      simp
    have hvk : v ∈ H k := by
      rw [LinearMap.mem_ker, hφ_apply, hv,
        Pi.single_eq_of_ne (M := fun _ => ZMod 3) (Ne.symm hne) 1]
    exact hvj (hjk ▸ hvk)
  have hIcard : I.card = m - 1 := by
    rw [show I = Finset.univ.image H from rfl]
    rw [Finset.card_image_of_injOn (fun a _ b _ h => hHinj h)]
    simpa using hs
  have hinf : ∀ v : DVec m, (∀ K ∈ I, v ∈ K) → ∀ i, i ≠ c → v i = 0 := by
    intro v hv i hi
    have hall : ∀ j, v ∈ H j := fun j =>
      hv (H j) (Finset.mem_image.mpr ⟨j, Finset.mem_univ j, rfl⟩)
    have hΛv : Λ v = 0 := by
      funext j
      have h := hall j
      rw [LinearMap.mem_ker, hφ_apply] at h
      exact h
    exact (hker v).mp hΛv i hi
  have hinv : ∀ w ∈ dEvenStab m (Pi.single c 1), ∀ K ∈ I,
      K.map (w : DVec m ≃ₗ[ZMod 3] DVec m).toLinearMap ∈ I := by
    intro w hw K hK
    rw [Finset.mem_image] at hK
    obtain ⟨j, _, rfl⟩ := hK
    obtain ⟨y, hy⟩ := hW w hw
    let pre : (Fin F.s → ZMod 3) → DVec m := fun f => Classical.choose (hsurj f)
    have hpre : ∀ f, Λ (pre f) = f := fun f => Classical.choose_spec (hsurj f)
    let φ' : (Fin F.s → ZMod 3) → (Fin F.s → ZMod 3) := fun f => Λ (w (pre f))
    have hconj : ∃ g : StatedSp (m - 1) (ZMod 2), ∀ f, g * F.tor f * g⁻¹ = F.tor (φ' f) := by
      refine ⟨y, fun f => ?_⟩
      have hf : F.tor f = τ (Multiplicative.ofAdd (pre f)) := by
        rw [← hΛ (pre f), hpre f]
      rw [hf, hy (pre f), hΛ (w (pre f))]
    obtain ⟨π, η, hπη⟩ := (ChoiceTwo.SpFrame.exists_conj_iff_moveExp hζ F φ').mp hconj
    have hmove : ∀ f, φ' f = ChoiceTwo.moveExp π η f := fun f => congrFun hπη f
    have hfixw : w (Pi.single c 1) = Pi.single c 1 := hw.2
    have hrel : ∀ v : DVec m, Λ (w v) = ChoiceTwo.moveExp π η (Λ v) := by
      intro v
      have hdiff : ∀ i, i ≠ c → (pre (Λ v) - v) i = 0 :=
        (hker (pre (Λ v) - v)).mp (by rw [map_sub, hpre (Λ v), sub_self])
      have hz : Λ (w (pre (Λ v) - v)) = 0 := by
        rw [hker]
        intro i hi
        have hfix : w (pre (Λ v) - v) = pre (Λ v) - v := by
          have hsum : pre (Λ v) - v = ((pre (Λ v) - v) c) • Pi.single c 1 := by
            ext i
            by_cases hic : i = c
            · subst hic; simp
            · rw [hdiff i hic, Pi.smul_apply,
                Pi.single_eq_of_ne (M := fun _ => ZMod 3) hic 1, smul_zero]
          rw [hsum, map_smul, hfixw]
        rw [hfix]
        exact hdiff i hi
      have hmain : Λ (w (pre (Λ v))) = Λ (w v) := by
        rw [← sub_eq_zero, ← map_sub,
          show w (pre (Λ v)) - w v = w (pre (Λ v) - v) by rw [map_sub]]
        exact hz
      rw [← hmain]
      exact hmove (Λ v)
    have hmap : (H j).map (w : DVec m ≃ₗ[ZMod 3] DVec m).toLinearMap = H (π.symm j) := by
      ext v
      rw [Submodule.mem_map]
      constructor
      · rintro ⟨x, hx, rfl⟩
        rw [LinearMap.mem_ker, hφ_apply] at hx ⊢
        have h := congrFun (hrel x) (π.symm j)
        rw [ChoiceTwo.moveExp_apply, Equiv.apply_symm_apply] at h
        exact h.trans (by rw [hx, ChoiceTwo.sgnZ_zero])
      · intro hv
        refine ⟨w.symm v, ?_, ?_⟩
        · rw [LinearMap.mem_ker, hφ_apply]
          have h := congrFun (hrel (w.symm v)) (π.symm j)
          rw [ChoiceTwo.moveExp_apply, Equiv.apply_symm_apply,
            LinearEquiv.apply_symm_apply] at h
          rw [LinearMap.mem_ker, hφ_apply] at hv
          rw [hv] at h
          exact (ChoiceTwo.sgnZ_eq_zero_iff _ _).mp h.symm
        · exact LinearEquiv.apply_symm_apply w v
    rw [hmap]
    exact Finset.mem_image.mpr ⟨π.symm j, Finset.mem_univ _, rfl⟩
  have hcoord : ∀ j : Fin F.s, ∃ i : Fin m, i ≠ c ∧ ∀ v : DVec m, v ∈ H j ↔ v i = 0 :=
    fun j => qtwoDB41_coord_hyperplanes hm I hI hIcard hinf hinv (H j)
      (Finset.mem_image.mpr ⟨j, Finset.mem_univ _, rfl⟩)
  intro x hx
  obtain ⟨d, rfl⟩ := F.Φ.surjective x
  have hd : d = 0 := by
    funext j
    obtain ⟨i, hic, hHi⟩ := hcoord j
    have hnotmem : u ∉ H j := by
      rw [hHi]
      exact hu i hic
    have hval : (Λ u) j ≠ 0 := by
      intro h0
      exact hnotmem (by rw [LinearMap.mem_ker, hφ_apply]; exact h0)
    have h1 : spEnd (F.tor (Λ u)) (F.Φ d) = F.Φ d := by
      rw [hΛ u]
      exact hx
    rw [F.tor_acts] at h1
    have h2 : ChoiceTwo.torE ζ (Λ u) d = d := F.Φ.injective h1
    have h3 : ζ ^ ((Λ u) j).val * d j = d j := by
      have h4 := congrFun h2 j
      simpa [ChoiceTwo.torE_apply] using h4
    have hne0 : ((Λ u) j).val ≠ 0 := (ZMod.val_ne_zero ((Λ u) j)).mpr hval
    have hpow : ζ ^ ((Λ u) j).val ≠ 1 :=
      hζ.pow_ne_one_of_pos_of_lt hne0 (ZMod.val_lt _)
    have hmul : (ζ ^ ((Λ u) j).val - 1) * d j = 0 := by
      rw [sub_mul, one_mul, sub_eq_zero]
      exact h3
    exact (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hpow)
  rw [hd, map_zero]

end CFSG.StandardType.QTwo

end
