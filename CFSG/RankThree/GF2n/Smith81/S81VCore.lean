module

public import CFSG.RankThree.GF2n.Smith81.S81VCoreModel
public import CFSG.RankThree.GF2n.Smith81.S81VModelDim
public import CFSG.RankThree.GF2n.Smith81.S81VIsoGen
public import CFSG.RankThree.GF2n.Smith81.S81VRankOneCore
public import CFSG.RankThree.GF2n.Smith81.S81VCoreChar
public import CFSG.RankThree.GF2n.Smith81.S81VCoreLines
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module Matrix

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K] [Finite K]
  {V : Type} [AddCommGroup V] [Module K V]

theorem core_main_U (hσ : IsUnitaryInvolution σ) (e₀ : K ≃+* Fσ σ) (hq : 4 ≤ Nat.card K)
    (hF : Nat.card F = Nat.card K ^ 2) (hV : finrank K V = 20) (A : SUid σ 6 →* (V ≃ₗ[K] V))
    (β : V →ₗ[K] V →ₗ[K] K) (hβalt : ∀ v, β v v = 0) (hβA : ∀ g u w, β (A g u) (A g w) = β u w)
    (hline : finrank K (fixU σ A) = 1)
    (hspan : ⨆ g : SUid σ 6, (fixU σ A).map (A g : V →ₗ[K] V) = ⊤)
    (hV1 : finrank K (V1U σ A β) ≤ 10) :
    ∃ (e' : K ≃+* Fσ σ) (ψ : V ≃ₗ[K] E3UWspace σ e'),
      (∀ g v, ψ (A g v) = e3uWact σ e' g (ψ v)) ∧
        (fixU σ A).map (ψ : V →ₗ[K] E3UWspace σ e') = Submodule.span K {e3uP0 σ e'} := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  haveI hKchar : CharP K 2 := by
    exact (((Fσ σ).subtype.comp (e₀ : K →+* Fσ σ) : K →+* F).charP_iff_charP 2).2 inferInstance
  obtain ⟨n, -, hKn⟩ := FiniteField.card K 2
  have hKcard : Fintype.card K = 2 ^ (n : ℕ) := hKn
  have hq' : 4 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  have hf2 : 2 ≤ (n : ℕ) := by
    by_contra h
    have : (n : ℕ) ≤ 1 := by omega
    have h1 : 2 ^ (n : ℕ) ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) this
    omega
  have hVpos : 0 < finrank K V := by omega
  haveI : FiniteDimensional K V := Module.finite_of_finrank_pos hVpos
  obtain ⟨b, hf⟩ := exists_frame_T0 hσ
  set R := rootDatumU hσ hf e₀ with hR
  set D := R.toRankOne A with hD
  have hfix_ne : fixU σ A ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hline
    omega
  obtain ⟨v₀, hv₀, hne⟩ : ∃ v₀ ∈ fixU σ A, v₀ ≠ 0 :=
    Submodule.exists_mem_ne_zero_of_ne_bot hfix_ne
  have hfix : D.fix = fixU σ A := toRankOne_fix_eq hσ hf e₀ A
  obtain ⟨k, hk⟩ := D.exists_char (by rw [hfix]; exact hline) (by rw [hfix]; exact hv₀) hne
  have hsv : A (sU hσ.invol hf) v₀ ∉ fixU σ A := sv_U hσ hf A hline hspan (by omega) hv₀ hne
  have hSetup : D.Setup v₀ k :=
    { fix1 := by rw [hfix]; exact hline
      mem := by rw [hfix]; exact hv₀
      ne0 := hne
      sv := by rw [hfix]; exact hsv
      char := hk }
  have hβρ : ∀ n u w, β (D.ρ n u) (D.ρ n w) = β u w := fun n u w => hβA (R.u n) u w
  have hβa : ∀ (g : R.P) u w, β (D.a g u) (D.a g w) = β u w :=
    fun g u w => hβA (g : SUid σ 6) u w
  have hN9 : 9 ≤ finrank K D.N := nine_le_finrank_HermK hσ hF e₀ hf
  have hV1' : finrank K (D.V1 β) ≤ finrank K D.N + 1 := by
    rw [toRankOne_V1_eq hσ hf e₀ A β]
    omega
  have hbraid := R.toRankOne_braid A
  obtain ⟨i, hR1, -, hchar⟩ :=
    RankOneData.rankOne_normalized hKcard hf2 hSetup hβalt hβρ hβa hV1' hbraid
  let φ : K ≃+* K := iterateFrobeniusEquiv K 2 i
  have hφ : ∀ t : K, φ t = t ^ 2 ^ i := fun t => rfl
  let ψ : K ≃+* K := φ.symm
  let e' : K ≃+* Fσ σ := ψ.trans e₀
  have he' : ∀ t, e' t = e₀ (ψ t) := fun t => rfl
  have hψφ : ∀ t : K, (ψ t) ^ 2 ^ i = t := fun t => by
    rw [← hφ]
    exact φ.apply_symm_apply t
  obtain ⟨χV, hχV⟩ := exists_chiV A hline hv₀ hne
  have hχV0 : ∀ g : ↥(Pstab σ (W₀ F)), (g : SUid σ 6) ∈ PtStab σ (W₀ F) → χV g = 1 := by
    intro g hg
    have h1 : A (g : SUid σ 6) v₀ = v₀ := hv₀ _ hg
    have h2 := hχV g
    rw [h1] at h2
    apply Units.ext
    have h3 : ((1 : K)) • v₀ = ((χV g : Kˣ) : K) • v₀ := by rw [one_smul]; exact h2
    exact (smul_left_injective K hne h3).symm
  have htV : ∀ c : Kˣ, χV (dKhom hσ.invol hf e₀ c) = c ^ 2 ^ i := by
    intro c
    apply Units.ext
    have h1 := hchar c
    have h2 := hχV (dKhom hσ.invol hf e₀ c)
    have h3 : ((c : K) ^ 2 ^ i) • v₀ = ((χV (dKhom hσ.invol hf e₀ c) : Kˣ) : K) • v₀ :=
      h1.symm.trans h2
    rw [Units.val_pow_eq_pow_val]
    exact (smul_left_injective K hne h3).symm
  have htM : ∀ c : Kˣ, chiM hσ hf e' (dKhom hσ.invol hf e₀ c) = c ^ 2 ^ i := by
    intro c
    apply Units.ext
    rw [chiM_dKhom hσ hf e₀ e' c, Units.val_pow_eq_pow_val]
    have : e'.symm (e₀ (c : K)) = φ (c : K) := by
      show ψ.symm (e₀.symm (e₀ (c : K))) = φ (c : K)
      rw [e₀.symm_apply_apply]
      rfl
    rw [this, hφ]
  have hchi : χV = chiM hσ hf e' :=
    chi_eq_of_torus hσ hf e₀ χV (chiM hσ hf e') hχV0 (fun g hg => chiM_triv hσ hf e' hg)
      (fun c => by rw [htV, htM])
  have hq3 : 3 ≤ Nat.card (Fσ σ) := by
    have : Nat.card (Fσ σ) = Nat.card K := Nat.card_congr e₀.symm.toEquiv
    omega
  obtain ⟨Pi, hPi20, hGen⟩ := hGen_U hσ hq3
  haveI : Finite (A5Cube.Cube F) := Module.finite_of_finite F
  haveI : Finite (E3UWspace σ e') := (Subtype.finite : Finite (Wform σ))
  haveI : FiniteDimensional K (E3UWspace σ e') := Module.Finite.of_finite
  have hfixspan : fixU σ A = Submodule.span K {v₀} := by
    symm
    apply Submodule.eq_of_le_of_finrank_eq
    · exact (Submodule.span_singleton_le_iff_mem _ _).mpr hv₀
    · rw [hline, finrank_span_singleton hne]
  have hspanV : Submodule.span K (Set.range fun g : SUid σ 6 => A g v₀) = ⊤ := by
    rw [eq_top_iff, ← hspan]
    refine iSup_le fun g => ?_
    rw [hfixspan, Submodule.map_span, Set.image_singleton]
    exact Submodule.span_mono (by
      intro x hx
      rw [Set.mem_singleton_iff] at hx
      exact ⟨g, hx.symm⟩)
  have hR1V : ∀ t : K, A (uK hσ.invol hf (ψ t • n1K σ e₀)) (A (sU hσ.invol hf) v₀) =
      A (sU hσ.invol hf) v₀ + t • v₀ := by
    intro t
    have h1 := hR1 (ψ t)
    rw [hψφ] at h1
    exact h1
  obtain ⟨Ψ, hΨ, hΨp⟩ := iso_of_generation (K := K) (Γ := SUid σ 6) (M := E3UWspace σ e') (V := V)
    (e3uWact σ e') A (e3uP0 σ e') v₀ (Pt := PtU σ) ptU ColU Pi (sU hσ.invol hf)
    (fun t => uK hσ.invol hf (ψ t • n1K σ e₀))
    (hhom_U hσ hf e' A χV hχV hchi)
    (fun x y z hc hxy => hline_U hσ hf e₀ ψ x y z hc hxy)
    (e3u_R1M hσ hf e₀ e' ψ he') hR1V (ptU_surjective hσ) hGen (by omega) hspanV
    (e3u_spanM hσ e') (by rw [hV]; exact e3u_finrank hσ e')
  refine ⟨e', Ψ, hΨ, ?_⟩
  rw [hfixspan, Submodule.map_span, Set.image_singleton]
  congr 1
  simp [hΨp]

end CFSG.RankThree.GF2n.Smith81.S81V
