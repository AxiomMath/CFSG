module

public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBTypeA
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeA
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut

public section

namespace CFSG.StandardType

open CFSG.Assembly

section Transport

variable {p r : ℕ} {R R' : Type} [Group R] [Group R'] {I : Set (MulAut R)}
  {I' : Set (MulAut R')}

theorem card_map_congr (e : R ≃* R') (E : Subgroup (MulAut R)) :
    Nat.card (E.map (MulAut.congr e).toMonoidHom) = Nat.card E :=
  Subgroup.card_map_of_injective (MulAut.congr e).injective

theorem mem_normalizer_map_congr (e : R ≃* R') {E : Subgroup (MulAut R)} {a : MulAut R}
    (ha : a ∈ Subgroup.normalizer (E : Set (MulAut R))) :
    MulAut.congr e a ∈
      Subgroup.normalizer ((E.map (MulAut.congr e).toMonoidHom : Subgroup (MulAut R')) :
        Set (MulAut R')) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  obtain ⟨x, rfl⟩ := (MulAut.congr e).surjective y
  have hx : ∀ z : MulAut R, MulAut.congr e z ∈ E.map (MulAut.congr e).toMonoidHom ↔ z ∈ E :=
    fun z => by
      rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  rw [← map_inv, ← map_mul, ← map_mul, hx, hx]
  exact Subgroup.mem_normalizer_iff.mp ha x

theorem ggNoTransvectionTorus_of_mulEquiv (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGNoTransvectionTorus p r R' I') : GGNoTransvectionTorus p r R I := by
  intro Eh hEhI hEhA hr h3 a htv
  set c := MulAut.congr e with hc
  refine h (Eh.map c.toMonoidHom) (by rintro _ ⟨φ, hφ, rfl⟩; exact hI φ (hEhI hφ))
    (TableB.isElemAbelian_map hEhA _) (by rw [card_map_congr]; exact hr)
    (by rw [card_map_congr]; exact h3) ⟨c a, mem_normalizer_map_congr e a.2⟩
    (GGIsTransvection.of_mulEquiv (Eh.equivMapOfInjective c.toMonoidHom c.injective)
      (fun x => ?_) htv)
  apply Subtype.ext
  change c a * c x * (c a)⁻¹ = c ((a : MulAut R) * (x : MulAut R) * (a : MulAut R)⁻¹)
  rw [map_mul, map_mul, map_inv]

theorem ggCenterCoprime_of_mulEquiv (e : R ≃* R') (h : GGCenterCoprime p R') :
    GGCenterCoprime p R := by
  intro L' _ _ ψ hψ hker hperf
  have h1 := h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ)
    ((TypeA.ker_comp_mulEquiv e ψ).symm ▸ hker) hperf
  rwa [TypeA.ker_comp_mulEquiv] at h1

theorem congr_conj (e : R ≃* R') (w : R) : MulAut.congr e (MulAut.conj w) = MulAut.conj (e w) := by
  ext y
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, MulAut.conj_apply,
    MulAut.conj_apply, map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]

theorem ggNoInvariantLineTorus_of_mulEquiv (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (h : GGNoInvariantLineTorus p r R' I') : GGNoInvariantLineTorus p r R I := by
  intro Eh hEhI hEhA hr h3
  set c := MulAut.congr e with hc
  obtain ⟨hZ, hline⟩ := h (Eh.map c.toMonoidHom)
    (by rintro _ ⟨φ, hφ, rfl⟩; exact hI φ (hEhI hφ)) (TableB.isElemAbelian_map hEhA _)
    (by rw [card_map_congr]; exact hr) (by rw [card_map_congr]; exact h3)
  refine ⟨ggCenterCoprime_of_mulEquiv e hZ, fun Λ hΛ hΛp => ?_⟩
  obtain ⟨w', hw', e', he', hne'⟩ := hline (Λ.map c.toMonoidHom) (Subgroup.map_mono hΛ)
    (by rw [card_map_congr]; exact hΛp)
  have hcw : c (MulAut.conj (e.symm w')) = MulAut.conj w' := by
    rw [hc, congr_conj, MulEquiv.apply_symm_apply]
  have hmemE : ∀ z : MulAut R, c z ∈ Eh.map c.toMonoidHom ↔ z ∈ Eh := fun z => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  have hmemΛ : ∀ z : MulAut R, c z ∈ Λ.map c.toMonoidHom ↔ z ∈ Λ := fun z => by
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
  refine ⟨e.symm w', ?_, ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro x
    rw [← hmemE, ← hmemE, map_mul, map_mul, map_inv, hcw]
    exact Subgroup.mem_normalizer_iff.mp hw' (c x)
  · obtain ⟨e₁, he₁, rfl⟩ := he'
    refine ⟨e₁, he₁, fun hin => hne' ?_⟩
    rw [← hcw]
    have := (hmemΛ _).mpr hin
    rwa [map_mul, map_mul, map_inv] at this

theorem ggInnerDiagBound_of_mulEquiv (e : R ≃* R') (hI : ∀ φ ∈ I, MulAut.congr e φ ∈ I')
    (hI' : ∀ φ : MulAut R, MulAut.congr e φ ∈ I' → φ ∈ I) (h : GGInnerDiagBound p r R' I') :
    GGInnerDiagBound p r R I := by
  intro Eb Eh hEbI hEbA hr h3 hle hEhA hcard hnot
  set c := MulAut.congr e with hc
  obtain ⟨U, hU, hU2, hEU⟩ := h (Eb.map c.toMonoidHom) (Eh.map c.toMonoidHom)
    (by rintro _ ⟨φ, hφ, rfl⟩; exact hI φ (hEbI hφ)) (TableB.isElemAbelian_map hEbA _)
    (by rw [card_map_congr]; exact hr) (by rw [card_map_congr]; exact h3) (Subgroup.map_mono hle)
    (TableB.isElemAbelian_map hEhA _) (by rw [card_map_congr, card_map_congr]; exact hcard)
    (fun hsub => hnot fun φ hφ => hI' φ (hsub ⟨φ, hφ, rfl⟩))
  refine ⟨U.comap e.toMonoidHom, ?_, hU2.comap_of_injective _ e.injective, fun φ hφ u hu => ?_⟩
  · intro hbot
    apply hU
    rw [← Subgroup.map_comap_eq_self_of_surjective (f := e.toMonoidHom) e.surjective U, hbot,
      Subgroup.map_bot]
  · have h1 := hEU (c φ) ⟨φ, hφ, rfl⟩ (e u) hu
    change e (φ u) ∈ U
    have h2 : c φ (e u) = e (φ u) := by
      rw [hc, MulAut.congr_apply]
      change e (φ (e.symm (e u))) = e (φ u)
      rw [MulEquiv.symm_apply_apply]
    rwa [h2] at h1

end Transport

namespace TypeA

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {d : ℕ} {K : Type} [Field K]

theorem mem_of_congr_recipeEquiv_mem {φ : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hφ : MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K)) :
    φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ := by
  obtain ⟨A, hA⟩ := hφ
  refine ⟨A, Set.mem_univ _, fun h h' hh' => ?_⟩
  apply (recipeEquiv d K).injective
  have h1 := congrArg (fun F => F (recipeEquiv d K (LargeEvenProjMk _ h))) hA
  simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h1
  rw [← h1, recipeEquiv_mk, recipeEquiv_mk, conjAut_proj]
  congr 1
  apply Subtype.ext
  rw [coe_slConjugation', coe_slKerEquiv, coe_slKerEquiv, hh', Units.val_mul, Units.val_mul]

variable [Finite K]

theorem not_pow_three_le_of_small {p : ℕ} (hp : p.Prime) (hpK : p ∣ Nat.card K - 1) (hd0 : 0 < d)
    (hd3 : d ≤ 3) (hpd : Nat.Coprime p d) {X : Subgroup (MulAut (projectiveSL d K))}
    (hXI : (X : Set (MulAut (projectiveSL d K))) ⊆ Set.range (conjAut d K))
    (hX : IsElemAbelian p X) : ¬ p ^ 3 ≤ Nat.card X := by
  intro h3
  have h := h3.trans (card_le_of_subset_conjAut hp hpK hd0 hpd hX hXI)
  have := (Nat.pow_le_pow_iff_right hp.one_lt).mp h
  omega

theorem recipeLinear_corFourTwo {d N p : ℕ} (hp : p.Prime) (hpN : p ∣ N - 1)
    (hN : ∃ m, N = 2 ^ m) (hd : 2 ≤ d) (hpd : ¬ p ∣ d) {Q : LargeEvenRawCont}
    (h : LargeEvenRecipeLinear d N Q) :
    LargeEvenRecipeLinear d N fun R _ I F => Q R I F ∧
      ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I ∧ GGNoTransvectionTorus p r R I ∧
        GGNoInvariantLineTorus p r R I := by
  obtain ⟨K, _, _, hK, hQ⟩ := h
  obtain ⟨m, rfl⟩ := hN
  refine ⟨K, inferInstance, inferInstance, hK, hQ, ?_⟩
  have := charP_two_of_card hK
  have hpK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpN
  have hK1 : 1 < Nat.card K := Finite.one_lt_card
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · rw [h0, pow_zero] at hK
      omega
    · exact h0
  have hp2 : p ≠ 2 := prime_ne_two_of_dvd_two_pow_sub_one hm (hK ▸ hpK)
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  have h4 : 4 ≤ Nat.card K := by
    have h1 := Nat.le_of_dvd (by omega) hpK
    omega
  have hpd' : Nat.Coprime p d := (Nat.Prime.coprime_iff_not_dvd hp).mpr hpd
  have hI : ∀ φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ,
      MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) := fun _ hφ =>
    congr_recipeEquiv_mem hφ
  have hI' : ∀ φ, MulAut.congr (recipeEquiv d K) φ ∈ Set.range (conjAut d K) →
      φ ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ :=
    fun _ hφ => mem_of_congr_recipeEquiv_mem hφ
  rcases (show d ≤ 3 ∨ 4 ≤ d by omega) with hd3 | hd4
  · have hv := fun {X : Subgroup (MulAut (projectiveSL d K))} hXI hX =>
      not_pow_three_le_of_small (X := X) hp hpK (by omega) hd3 hpd' hXI hX
    refine ⟨0, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_zero (two_dvd_card_projectiveSL hd)),
      ggInnerDiagBound_of_mulEquiv (recipeEquiv d K) hI hI'
        fun _ _ hEbI hEbA _ h3 _ _ _ _ => absurd h3 (hv hEbI hEbA),
      ggNoTransvectionTorus_of_mulEquiv (recipeEquiv d K) hI
        fun _ hEhI hEhA _ h3 _ _ => absurd h3 (hv hEhI hEhA),
      ggNoInvariantLineTorus_of_mulEquiv (recipeEquiv d K) hI
        fun _ hEhI hEhA _ h3 => absurd h3 (hv hEhI hEhA)⟩
  · have hsec : SLHasSections d K :=
      slHasSections_of_card (by omega) (by omega) (by omega) (by omega)
    exact ⟨d - 1, ggTorusLift_of_mulEquiv (recipeEquiv d K)
        (ggTorusLift_coprime hp hpK hd hpd' hsec),
      ggInnerDiagBound_of_mulEquiv (recipeEquiv d K) hI hI'
        (ggInnerDiagBound_psl hp hp2 hpK (by omega) hpd'),
      ggNoTransvectionTorus_of_mulEquiv (recipeEquiv d K) hI
        (ggNoTransvectionTorus_psl hp hp2 hpK hd4 hpd'),
      ggNoInvariantLineTorus_of_mulEquiv (recipeEquiv d K) hI
        (ggNoInvariantLineTorus_psl hp hpK (by omega) hpd' hsec)⟩

theorem largeEvenLabelAll_corFourTwo_typeA {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTypeALabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I ∧
      GGNoTransvectionTorus p r R I ∧ GGNoInvariantLineTorus p r R I := by
  obtain ⟨t, l, n⟩ := lab
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  rcases h with ⟨h, hpn, hpl⟩ | ⟨h, hl, hpn⟩ | ⟨h, hl, hpn⟩
  · dsimp only at h hpn hpl
    subst h
    have hl1 : 1 ≤ l := hlab.2.1
    exact recipeLinear_corFourTwo hp hpn ⟨n, rfl⟩ (by omega) hpl hQ
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one hn hpn
    refine recipeLinear_corFourTwo hp hpn ⟨n, rfl⟩ (by norm_num) (fun h4 => hp2 ?_) hQ
    have h1 : p ∣ 2 ^ 2 := by norm_num; exact h4
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h1)
  · dsimp only at h hl hpn
    subst h hl
    dsimp only [LargeEvenRawDatum] at hQ ⊢
    rw [ite_eq_left rfl] at hQ ⊢
    have hpn' : p ∣ 2 ^ (2 * n) - 1 := by rw [mul_comm, pow_mul]; exact hpn
    have hp2 := prime_ne_two_of_dvd_two_pow_sub_one (by omega) hpn'
    refine recipeLinear_corFourTwo hp hpn ⟨2 * n, by rw [mul_comm, pow_mul]⟩ le_rfl
      (fun h2 => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2)) hQ

end TypeA

open TypeA

theorem ggBstarInnerDiagLInputOn_typeA : GGBstarInnerDiagLInputOn GGTypeALabel :=
  ggBstarInnerDiagLInputOn_of_labels (fun _ _ h => h.pilot) fun _ _ hp hlab h =>
    (largeEvenLabelAll_corFourTwo_typeA hp hlab h).mono fun _ _ _ _ ⟨r, h1, h2, _⟩ => ⟨r, h1, h2⟩

theorem ggLTransvectionCenterInputOn_typeA : GGLTransvectionCenterInputOn GGTypeALabel :=
  ggLTransvectionCenterInputOn_of_labels (fun _ _ h => h.pilot) fun _ _ hp hlab h =>
    (largeEvenLabelAll_corFourTwo_typeA hp hlab h).mono
      fun _ _ _ _ ⟨r, h1, _, h3, _⟩ => ⟨r, h1, h3⟩

theorem ggLNoInvariantLineInputOn_typeA : GGLNoInvariantLineInputOn GGTypeALabel :=
  ggLNoInvariantLineInputOn_of_labels fun _ _ hp hlab h =>
    (largeEvenLabelAll_corFourTwo_typeA hp hlab h).mono
      fun _ _ _ _ ⟨r, h1, _, _, h4⟩ => ⟨r, h1, h4⟩

@[expose] def GGCorFourTwoRestLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  ¬ GGTypeALabel p lab

theorem ggCor42Input_of_typeA (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoRestLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoRestLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoRestLabel)
    (hnorm : GGBstarNbrNormalInput) (hgraph : GGNbrGraphInput)
    (hfield : GGNbrFieldTransvectionInput) : GGCor42Input :=
  ggCor42Input_of_on (S := fun p lab => GGTypeALabel p lab ∨ GGCorFourTwoRestLabel p lab)
    (fun p lab _ _ => em (GGTypeALabel p lab)) hK (ggBstarInnerDiagLInputOn_typeA.or hLID)
    (ggLTransvectionCenterInputOn_typeA.or hcen) (ggLNoInvariantLineInputOn_typeA.or hline)
    hnorm hgraph hfield

theorem ggNoTransvectionInput_of_typeA (hK : GGKantorReductionInput)
    (hLID : GGBstarInnerDiagLInputOn GGCorFourTwoRestLabel)
    (hcen : GGLTransvectionCenterInputOn GGCorFourTwoRestLabel)
    (hline : GGLNoInvariantLineInputOn GGCorFourTwoRestLabel) : GGNoTransvectionInput :=
  ggNoTransvectionInput_of_on (S := fun p lab => GGTypeALabel p lab ∨ GGCorFourTwoRestLabel p lab)
    (fun p lab _ _ => em (GGTypeALabel p lab)) hK (ggBstarInnerDiagLInputOn_typeA.or hLID)
    (ggLTransvectionCenterInputOn_typeA.or hcen) (ggLNoInvariantLineInputOn_typeA.or hline)

end CFSG.StandardType
