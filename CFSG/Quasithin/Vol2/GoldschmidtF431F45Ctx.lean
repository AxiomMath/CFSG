module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Lie

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Blueprint

universe u

namespace F45

open SpOut2

theorem exists_f45Ctx {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSp 2 2 f)
    (A : LieAmalgamExt D) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (Φ : antiSp F →* ↥A.K) (ψ : ↥A.K) (k₀ : ℕ) (R : Fin 2 → Subgroup (antiSp F))
      (i : Fin 3 → antiSp F), OutProps Φ ψ k₀ ∧ SpDData (antiUnipotent F) R i ∧
      (∀ j : Fin 2, (![A.Mb1, A.Mb2] : Fin 2 → Subgroup ↥A.K) j =
        Subgroup.normalizer (((R j).map Φ : Subgroup ↥A.K) : Set ↥A.K)) ∧
      ((R = Rrad F ∧ i = iRep F) ∨
        (R = ![radA2 F, radA1 F] ∧ i = ![iRep F 1, iRep F 0, iRep F 2])) ∧
      (∀ j : Fin 2, ψ ∈ Subgroup.normalizer (((R j).map Φ : Subgroup ↥A.K) : Set ↥A.K)) ∧
      (∀ k : ↥A.K, k ∈ Φ.range ↔ (k : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range) := by
  obtain ⟨hf, F, hFf, hFfin, hFchar, E, R, i, hFcard, hRi, hDd, h1, h2⟩ :=
    spAmalgam_data_out hD A
  have hfinD : Finite D := Finite.of_injective E E.injective
  have hfinX : Finite (antiSp F) := Finite.of_equiv D E.toEquiv
  have hfinAut : Finite (MulAut D) := finite_mulAut_of_finite
  have hgen := f431Generation_psp f D hD A
  have hK : ∀ d : D, (MulAut.conj d : MulAut D) ∈ A.K := fun d => hgen ⟨d, rfl⟩
  have hcen := (f431ModelFacts_psp f D hD).2
  have hinj : Function.Injective (MulAut.conj : D →* MulAut D) := by
    rw [injective_iff_map_eq_one]
    intro d hd
    have hdc : d ∈ Subgroup.center D := by
      rw [Subgroup.mem_center_iff]
      intro g
      have := congrArg (fun φ : MulAut D => φ g) hd
      simp only [MulAut.conj_apply, MulAut.one_apply] at this
      rw [mul_inv_eq_iff_eq_mul] at this
      exact this.symm
    rw [hcen] at hdc
    exact Subgroup.mem_bot.mp hdc
  set ΦD : D →* ↥A.K := (MulAut.conj : D →* MulAut D).codRestrict A.K hK with hΦD
  set Φ : antiSp F →* ↥A.K := ΦD.comp E.symm.toMonoidHom with hΦ
  have hΦD_inj : Function.Injective ΦD := fun a b h => hinj (congrArg Subtype.val h)
  have hΦinj : Function.Injective Φ := hΦD_inj.comp E.symm.injective
  have hΦx : ∀ x : antiSp F, Φ x = ΦD (E.symm x) := fun x => rfl
  have key : ∀ (P : Subgroup D) (r : Subgroup (antiSp F)) (N' : Subgroup ↥A.K),
      P.map E.toMonoidHom = Subgroup.normalizer (r : Set (antiSp F)) →
      pCoreOf 2 (Subgroup.normalizer (r : Set (antiSp F))) = r →
      (∀ x : ↥A.K, x ∈ N' ↔ (x : MulAut D) ∈ CFSG.Quasithin.autStab P) →
      N' = Subgroup.normalizer ((r.map Φ : Subgroup ↥A.K) : Set ↥A.K) := by
    intro P r N' hP hcore hN'
    set S : Subgroup D := r.map E.symm.toMonoidHom with hS
    have hnS : (Subgroup.normalizer (r : Set (antiSp F))).map E.symm.toMonoidHom =
        Subgroup.normalizer (S : Set D) := by
      ext g
      rw [Subgroup.mem_map_equiv, hS, mem_normalizer_map E.symm r g]
    have hPS : P = Subgroup.normalizer (S : Set D) := by
      rw [← hnS, ← hP, Subgroup.map_map]
      ext g
      simp
    have hcoreS : pCoreOf 2 (Subgroup.normalizer (S : Set D)) = S := by
      rw [← hnS, pCoreOf_map_of_injective E.symm.toMonoidHom E.symm.injective, hcore]
    have hrS : r.map Φ = S.map ΦD := by
      rw [hS, Subgroup.map_map]
    ext x
    rw [hN' x, hrS, mem_normalizer_map_codRestrict_iff hK hinj S x, hPS,
      mem_autStab_iff_of_normalizer hcoreS]
  have hKM : ∀ x : ↥A.K, (x : MulAut D) ∈ A.Mbar := fun x => (sup_le inf_le_left inf_le_left :
    A.K ≤ A.Mbar) x.2
  have hN : ∀ j : Fin 2, (![A.Mb1, A.Mb2] : Fin 2 → Subgroup ↥A.K) j =
      Subgroup.normalizer ((((R j).map Φ : Subgroup ↥A.K)) : Set ↥A.K) := by
    intro j
    fin_cases j
    · refine key A.P1 (R 0) A.Mb1 h1 hDd.borel.core₁ ?_
      intro x
      rw [Subgroup.mem_subgroupOf]
      exact ⟨fun hx => hx.2, fun hx => ⟨hKM x, hx⟩⟩
    · refine key A.P2 (R 1) A.Mb2 h2 hDd.borel.core₂ ?_
      intro x
      rw [Subgroup.mem_subgroupOf]
      exact ⟨fun hx => hx.2, fun hx => ⟨hKM x, hx⟩⟩
  set θ : MulAut D ≃* MulAut (antiSp F) := MulAut.congr E with hθ
  have hθapp : ∀ (α : MulAut D) (x : antiSp F), θ α x = E (α (E.symm x)) := fun α x => rfl
  have hθconj : ∀ d : D, θ (MulAut.conj d) = MulAut.conj (E d) := by
    intro d
    refine MulEquiv.ext fun x => ?_
    rw [hθapp, MulAut.conj_apply, MulAut.conj_apply]
    simp
  have haut : ∀ α : MulAut (antiSp F),
      ((∀ x, α x ∈ R 0 ↔ x ∈ R 0) ∨ (∀ x, α x ∈ R 1 ↔ x ∈ R 1)) →
        ∃ (g : antiSp F) (k : ℕ), α = MulAut.conj g * frobAut F ^ k := by
    rcases hRi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun α h => aut_form_antiSp (by omega) hFcard α h
    · exact fun α h => aut_form_antiSp (by omega) hFcard α h.symm
  have hstab : ∀ (P : Subgroup D) (r : Subgroup (antiSp F)),
      P.map E.toMonoidHom = Subgroup.normalizer (r : Set (antiSp F)) →
      pCoreOf 2 (Subgroup.normalizer (r : Set (antiSp F))) = r →
      ∀ β : MulAut D, β ∈ CFSG.Quasithin.autStab P → ∀ x, θ β x ∈ r ↔ x ∈ r := by
    intro P r hP hcore β hβ
    have h1 : θ β ∈ CFSG.Quasithin.autStab (Subgroup.normalizer (r : Set (antiSp F))) := by
      intro x
      rw [← hP, Subgroup.mem_map_equiv, Subgroup.mem_map_equiv, hθapp]
      simpa using hβ (E.symm x)
    exact fun x => ((mem_autStab_iff_of_normalizer hcore (θ β)).mp h1 x).symm
  have hmem : ∀ (β : MulAut D), β ∈ A.N1 ∨ β ∈ A.N2 →
      ∃ (g : antiSp F) (k : ℕ), θ β = MulAut.conj g * frobAut F ^ k := by
    intro β hβ
    rcases hβ with hβ | hβ
    · exact haut _ (Or.inl fun x => hstab A.P1 (R 0) h1 hDd.borel.core₁ β hβ.2 x)
    · exact haut _ (Or.inr fun x => hstab A.P2 (R 1) h2 hDd.borel.core₂ β hβ.2 x)
  set L : Subgroup (MulAut (antiSp F)) := (MulAut.conj : antiSp F →* MulAut (antiSp F)).range ⊔
    Subgroup.zpowers (frobAut F) with hL
  have hLmem : ∀ (g : antiSp F) (k : ℕ), (MulAut.conj g * frobAut F ^ k : MulAut (antiSp F)) ∈ L :=
    fun g k => Subgroup.mul_mem _ (Subgroup.mem_sup_left ⟨g, rfl⟩)
      (Subgroup.mem_sup_right (Subgroup.pow_mem _ (Subgroup.mem_zpowers _) k))
  set Kp : Subgroup (MulAut (antiSp F)) := A.K.map θ.toMonoidHom with hKp
  have hInn : ∀ g : antiSp F, MulAut.conj g ∈ Kp := fun g =>
    ⟨MulAut.conj (E.symm g), hK _, by rw [MulEquiv.coe_toMonoidHom, hθconj]; simp⟩
  have hKL : Kp ≤ L := by
    rw [hKp, LieAmalgamExt.K, Subgroup.map_sup]
    refine sup_le ?_ ?_
    · rintro _ ⟨β, hβ, rfl⟩
      obtain ⟨g, k, hgk⟩ := hmem β (Or.inl hβ)
      rw [MulEquiv.coe_toMonoidHom, hgk]
      exact hLmem g k
    · rintro _ ⟨β, hβ, rfl⟩
      obtain ⟨g, k, hgk⟩ := hmem β (Or.inr hβ)
      rw [MulEquiv.coe_toMonoidHom, hgk]
      exact hLmem g k
  obtain ⟨k₀, hk₀, hFrK, hdecomp⟩ := exists_gen_frob (n := f) (by omega) hFcard Kp hInn hKL
  obtain ⟨a, haK, haθ⟩ := hFrK
  set ψ : ↥A.K := ⟨a, haK⟩ with hψ
  have haθ' : θ a = frobAut F ^ k₀ := haθ
  have hψapp : ∀ x : antiSp F, (ψ : MulAut D) (E.symm x) = E.symm ((frobAut F ^ k₀) x) := by
    intro x
    have := hθapp a x
    rw [haθ'] at this
    show a (E.symm x) = _
    rw [this]
    simp
  have hP : OutProps Φ ψ k₀ :=
    { inj := hΦinj
      act := by
        intro x
        rw [hΦx, hΦx, ← hψapp x]
        exact codRestrict_conj_conj hK ψ (E.symm x)
      cen := by
        intro h hh
        have h3 : ∀ d : D, (h : MulAut D) d = d := by
          intro d
          have := hh (E d)
          simp only [hΦx, E.symm_apply_apply] at this
          have h4 := codRestrict_conj_conj hK h d
          rw [h4] at this
          exact hΦD_inj this
        exact Subtype.ext (MulEquiv.ext fun d => h3 d)
      gen := by
        intro h
        have hh : θ (h : MulAut D) ∈ Kp := ⟨h, h.2, rfl⟩
        obtain ⟨g, s, hgs⟩ := hdecomp _ hh
        refine ⟨g, s, Subtype.ext ?_⟩
        apply θ.injective
        have hΦg : ((Φ g : ↥A.K) : MulAut D) = MulAut.conj (E.symm g) := rfl
        have hψa : ((ψ : ↥A.K) : MulAut D) = a := rfl
        rw [hgs, Subgroup.coe_mul, Subgroup.coe_pow, hΦg, hψa, map_mul, map_pow, hθconj,
          E.apply_symm_apply, haθ'] }
  have hRfr : ∀ j : Fin 2, ∀ (k : ℕ) (x : antiSp F), (frobAut F ^ k) x ∈ R j ↔ x ∈ R j := by
    rcases hRi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · intro j k x
      fin_cases j
      · exact frobAut_pow_mem_iff frobAut_mem_radA1_iff k x
      · exact frobAut_pow_mem_iff frobAut_mem_radA2_iff k x
    · intro j k x
      fin_cases j
      · exact frobAut_pow_mem_iff frobAut_mem_radA2_iff k x
      · exact frobAut_pow_mem_iff frobAut_mem_radA1_iff k x
  have hΦr : ∀ k : ↥A.K, k ∈ Φ.range ↔ (k : MulAut D) ∈ (MulAut.conj : D →* MulAut D).range := by
    intro k
    constructor
    · rintro ⟨x, rfl⟩
      exact ⟨E.symm x, rfl⟩
    · rintro ⟨d, hd⟩
      refine ⟨E d, ?_⟩
      apply Subtype.ext
      rw [hΦx, E.symm_apply_apply]
      exact hd
  refine ⟨F, hFf, hFfin, hFchar, Φ, ψ, k₀, R, i, hP, hDd, hN, hRi, fun j => ?_, hΦr⟩
  have := hP.pow_mem_normalizer_map (V := R j) (fun k x => hRfr j k x) 1
  simpa using this

end F45

end CFSG.Quasithin.H13.F431
