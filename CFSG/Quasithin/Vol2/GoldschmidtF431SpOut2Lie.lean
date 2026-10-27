module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Data
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpModelLie
public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Blueprint

universe u

namespace SpOut2

theorem forall_fin3 {α : Type*} {P : α → Prop} {a b c : α} (ha : P a) (hb : P b) (hc : P c) :
    ∀ k : Fin 3, P ((![a, b, c] : Fin 3 → α) k) := by
  intro k
  fin_cases k
  · exact ha
  · exact hb
  · exact hc

theorem forall_swap3 {α : Type*} {P : α → Prop} {a b c : α} (ha : P a) (hb : P b) (hc : P c) :
    ∀ k : Fin 3, P ((![b, a, c] : Fin 3 → α) k) := by
  intro k
  fin_cases k
  · exact hb
  · exact ha
  · exact hc

section Gen

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem innNormal {G : Type} [Group G] : (MulAut.conj : G →* MulAut G).range.Normal := by
  refine ⟨fun n hn g => ?_⟩
  obtain ⟨d, rfl⟩ := hn
  exact ⟨g d, (mulAut_conj_conj g d).symm⟩

theorem exists_gen_frob {n : ℕ} (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (Kp : Subgroup (MulAut (antiSp F))) (hInn : ∀ g : antiSp F, MulAut.conj g ∈ Kp)
    (hKL : Kp ≤ (MulAut.conj : antiSp F →* MulAut (antiSp F)).range ⊔
      Subgroup.zpowers (frobAut F)) :
    ∃ k₀ : ℕ, 0 < k₀ ∧ frobAut F ^ k₀ ∈ Kp ∧ ∀ α ∈ Kp,
      ∃ (g : antiSp F) (s : ℕ), α = MulAut.conj g * (frobAut F ^ k₀) ^ s := by
  classical
  have : Finite (MulAut (antiSp F)) := finite_mulAut_of_finite
  have : (MulAut.conj : antiSp F →* MulAut (antiSp F)).range.Normal := innNormal
  have hex : ∃ k, 0 < k ∧ frobAut F ^ k ∈ Kp :=
    ⟨n, by omega, by rw [frobAut_pow_card hF]; exact Kp.one_mem⟩
  refine ⟨Nat.find hex, (Nat.find_spec hex).1, (Nat.find_spec hex).2, ?_⟩
  set k₀ := Nat.find hex with hk₀
  have hdiv : ∀ k, frobAut F ^ k ∈ Kp → k₀ ∣ k := by
    intro k hk
    have h1 : frobAut F ^ (k % k₀) ∈ Kp := by
      have e : frobAut F ^ k = (frobAut F ^ k₀) ^ (k / k₀) * frobAut F ^ (k % k₀) := by
        rw [← pow_mul, ← pow_add, Nat.div_add_mod]
      have : frobAut F ^ (k % k₀) = ((frobAut F ^ k₀) ^ (k / k₀))⁻¹ * frobAut F ^ k := by
        rw [e]
        group
      rw [this]
      exact Kp.mul_mem (Kp.inv_mem (Kp.pow_mem (Nat.find_spec hex).2 _)) hk
    by_contra hnd
    have hpos : 0 < k % k₀ := Nat.pos_of_ne_zero fun h => hnd (Nat.dvd_of_mod_eq_zero h)
    exact Nat.find_min hex (Nat.mod_lt _ (Nat.find_spec hex).1) ⟨hpos, h1⟩
  intro α hα
  obtain ⟨y, ⟨g, rfl⟩, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_left.mp (hKL hα)
  obtain ⟨k, hk'⟩ : ∃ k : ℕ, frobAut F ^ k = z :=
    (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  subst hk'
  have hk : frobAut F ^ k ∈ Kp := by
    have : frobAut F ^ k = (MulAut.conj g)⁻¹ * α := by rw [← hyz]; group
    rw [this]
    exact Kp.mul_mem (Kp.inv_mem (hInn g)) hα
  obtain ⟨s, hs⟩ := hdiv k hk
  exact ⟨g, s, by rw [← hyz, hs, pow_mul]⟩

end Gen

section Amalgam

open SpModel

theorem spAmalgam_data_out {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSp 2 2 f)
    (A : LieAmalgamExt D) :
    2 ≤ f ∧ ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (E : D ≃* antiSp F)
      (R : Fin 2 → Subgroup (antiSp F)) (i : Fin 3 → antiSp F), Nat.card F = 2 ^ f ∧
      ((R = Rrad F ∧ i = iRep F) ∨
        (R = ![radA2 F, radA1 F] ∧ i = ![iRep F 1, iRep F 0, iRep F 2])) ∧
      SpDData (antiUnipotent F) R i ∧
      A.P1.map E.toMonoidHom = Subgroup.normalizer (R 0 : Set (antiSp F)) ∧
      A.P2.map E.toMonoidHom = Subgroup.normalizer (R 1 : Set (antiSp F)) := by
  obtain ⟨hf, F, hFf, hFfin, hFchar, hFcard, ⟨e1⟩⟩ := exists_equiv_antiSp hD
  have hy1 := A.yam.map e1
  have hU := (borel_antiSp (F := F) hf hFcard).sylow
  obtain ⟨h, -, hh⟩ := IsSylowTwoOf.exists_conj hy1.1 hU
  let E : D ≃* antiSp F := e1.trans (MulAut.conj h)
  have hy2 : IsYAmalgamPair (antiUnipotent F) (A.P1.map E.toMonoidHom)
      (A.P2.map E.toMonoidHom) := by
    have := A.yam.map E
    have hTD : A.TD.map E.toMonoidHom = antiUnipotent F := by
      rw [hh, Subgroup.map_map]
      rfl
    rwa [hTD] at this
  refine ⟨hf, F, hFf, hFfin, hFchar, E, ?_⟩
  rcases yam_antiSp hf hFcard hy2 with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨Rrad F, iRep F, hFcard, Or.inl ⟨rfl, rfl⟩, spDData_antiSp hf hFcard, h1, h2⟩
  · exact ⟨![radA2 F, radA1 F], ![iRep F 1, iRep F 0, iRep F 2], hFcard, Or.inr ⟨rfl, rfl⟩,
      (spDData_antiSp hf hFcard).swap, h1, h2⟩

end Amalgam

section Main

open SpModel

theorem exists_outCtx {D : Type} [Group D] {f : ℕ} (hD : LieModel D .PSp 2 2 f)
    (A : LieAmalgamExt D) (hev : ¬ Odd (Nat.card ↥A.K / Nat.card D)) :
    ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2)
      (Φ : antiSp F →* ↥A.K) (ψ : ↥A.K) (k₀ : ℕ) (R : Fin 2 → Subgroup (antiSp F))
      (i : Fin 3 → antiSp F), f = 2 * m ∧
      OutCtx m Φ ψ k₀ (antiUnipotent F) R i ![A.Mb1, A.Mb2] ∧ Even (orderOf ψ) ∧
      ((R = Rrad F ∧ i = iRep F) ∨
        (R = ![radA2 F, radA1 F] ∧ i = ![iRep F 1, iRep F 0, iRep F 2])) := by
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
  have hn1 : 1 ≤ f := by omega
  have hcard := hP.card_eq hn1 hFcard
  have hDcard : Nat.card D = Nat.card (antiSp F) := Nat.card_congr E.toEquiv
  have hord : Nat.card ↥A.K / Nat.card D = orderOf ψ := by
    rw [hcard, hDcard]
    exact Nat.mul_div_cancel_left _ Nat.card_pos
  have hev' : Even (orderOf ψ) := by
    rw [hord] at hev
    exact Nat.not_odd_iff_even.mp hev
  have hdvd : orderOf ψ ∣ f := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [hP.pow_eq_one_iff, mul_comm, pow_mul, frobAut_pow_card hFcard, one_pow]
  obtain ⟨m, hm⟩ : ∃ m, f = 2 * m := by
    obtain ⟨c, hc⟩ := (even_iff_two_dvd.mp hev').trans hdvd
    exact ⟨c, hc⟩
  have hm1 : 1 ≤ m := by omega
  have hFcard' : Nat.card F = 2 ^ (2 * m) := by rw [← hm]; exact hFcard
  have hX : SpOutXData m (antiUnipotent F) R i := by
    rcases hRi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact spOutXData_antiSp hm1 hFcard'
    · exact (spOutXData_antiSp hm1 hFcard').swap
  exact ⟨m, F, hFf, hFfin, hFchar, Φ, ψ, k₀, R, i, hm, ⟨hm1, hP, hDd, hX, hN⟩, hev', hRi⟩

end Main

end SpOut2

open SpOut2 in
theorem f431SpOutLieProp {f : ℕ} (hf : 3 ≤ f) : F431SpOutLieProp f := by
  intro D _ hD A hev
  have : Finite D := finite_of_lieModel_psp hD
  have : Finite (MulAut D) := finite_mulAut_of_finite
  have : Finite ↥A.K := inferInstance
  obtain ⟨m, F, hFf, hFfin, hFchar, Φ, ψ, k₀, R, i, hm, C, hevψ, hRi⟩ := exists_outCtx hD A hev
  have hm2 : 2 ≤ m := by omega
  refine ⟨spT Φ ψ (antiUnipotent F), (antiUnipotent F).map Φ, spf ψ, spI Φ i, ?_⟩
  have hcomm : ∀ k, i k ∈ ⁅(antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) :
      Subgroup (antiSp F)), (antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) :
      Subgroup (antiSp F))⁆ := by
    rcases hRi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact fun k => iRep_mem_commutator hm2 C.hF k
    · exact forall_swap3 (P := fun x => x ∈ ⁅(antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) :
        Subgroup (antiSp F)), (antiUnipotent F ⊓ fixedSubgroup (frobAut F ^ m) :
        Subgroup (antiSp F))⁆) (iRep_mem_commutator hm2 C.hF 0) (iRep_mem_commutator hm2 C.hF 1)
        (iRep_mem_commutator hm2 C.hF 2)
  exact (C.core hevψ).toOut (C.W_ne hevψ hcomm)

end CFSG.Quasithin.H13.F431
