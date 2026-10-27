module

public import CFSG.Timmesfeld.ARS.CaseERoots

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseE

open CaseD4

theorem mem_lambdaSet_of_commuting_of_forall (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) {Y Y' : Subgroup G}
    (hYl : Y ∈ leviSet R A A₀) (hY'l : Y' ∈ leviSet R A A₀) (hYY' : Opposite Y Y')
    {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) (hQX : Commuting Y X) (hs : Special R Y' X)
    (hfix : ∀ T ∈ lambdaStar R A A₀, T ≤ A ⊔ (X ⊔ (⁅Y', X⁆ ⊔ ⁅Y, ⁅Y', X⁆⁆)) →
      Commuting Y' T → Commuting Y T → False) : X ∈ lambdaSet R Y := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hY : Y ∈ R := hYl.1.1
  have hY' : Y' ∈ R := hY'l.1.1
  have hXR : X ∈ R := hX.1.1.1
  set D := ⁅Y', X⁆ with hDdef
  set E := ⁅Y, D⁆ with hEdef
  set N := D ⊔ E with hNdef
  set W := X ⊔ N with hWdef
  set Z := W ⊓ Subgroup.centralizer ((Y ⊔ Y' ⊔ X : Subgroup G) : Set G) with hZdef
  obtain ⟨⟨hDl, hDp, -, hNinv, -⟩, ⟨-, -, hMinv, -, -, -, hNZ'⟩, ⟨-, hFZ, hZiff⟩⟩ :=
    natural_module_of_commuting hR hiso hY hY' hYY' ⟨hXR, hs⟩ hQX (N := N) (M := W) (Z := Z)
      rfl rfl rfl
  rw [← hZiff]
  by_contra hZne
  have hDR : D ∈ R := hDl.1.1
  have hD : D ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hY'l hX hs.symm).1 D hDR
    rw [Subgroup.commutator_comm X Y'] at this
    exact this le_sup_right
  have hDY : Special R D Y := hDp.2.symm
  have hER : E ∈ R := hDp.2.1
  have hNinv' : ∀ x ∈ Y' ⊔ Y, conjSub N x = N := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hY' hY hYY'.symm hDl hDp hx
  have hfixY' : ∀ n ∈ N, (∀ a ∈ Y', Commute a n) → n ∈ D := fun n hn hnA =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hY' hY hYY'.symm hDl hDp hn hnA
  have hE : E ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hYl hD hDY).1 E hER
    rw [Subgroup.commutator_comm D Y] at this
    exact this le_sup_right
  have hDE : D ≠ E := by
    have := hDY.ne_commutator hR
    rwa [Subgroup.commutator_comm D Y] at this
  have hEl : E ∈ lambdaSet R Y :=
    mem_lambdaSet_comm hER (mem_lambdaSet_commutator hR hiso hY hDR hDp.2).1
  have hEN : E ≤ N := le_sup_right
  have hY'N : Y' ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hNinv' y (Subgroup.mem_sup_left hy))
  have hYN : Y ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hNinv' y (Subgroup.mem_sup_right hy))
  have hEs : Special R Y' E := by
    have hnc : ¬ Commuting Y' E := by
      intro hc
      refine hDE (Subgroup.eq_of_le_of_card_ge (fun e he => ?_) (hR.card_eq hDR hER).le).symm
      exact hfixY' e (hEN he) fun y hy => hc y hy e he
    have hne : Y' ≠ E := fun e => hnc (by rw [← e]; exact hR.commuting_self hY')
    rcases hR.rel _ hY' _ hER hne with hc | ho | hs'
    · exact absurd hc hnc
    · exact absurd ho (not_opposite_of_mem_leviSet hR hA hE hY'l)
    · exact hs'
  have hY'E : ⁅Y', E⁆ = D := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hDR hEs.1).le
    have hle : ⁅Y', E⁆ ≤ N := by
      rw [Subgroup.commutator_comm]
      exact commutator_le_of_le_normalizer hEN hY'N
    exact hfixY' x (hle hx) fun y hy => (hEs.2.1 x hx y hy).symm
  have hfixY : ∀ n ∈ N, (∀ a ∈ Y, Commute a n) → n ∈ E := fun n hn hnA => by
    refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hY hY' hYY' hEl ⟨hER, hEs⟩ ?_ hnA
    rw [hY'E, sup_comm]
    exact hn
  have hXN : X ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := fun x hx =>
    conjSub_eq_self_iff.1 (hNinv x (Subgroup.mem_sup_right hx))
  have hCM : ∀ m ∈ W, (∀ y ∈ Y, Commute y m) → m ∈ E ⊔ X := by
    intro m hm hmY
    have hm' : m ∈ ((N ⊔ X : Subgroup G) : Set G) := by rw [sup_comm]; exact hm
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hXN] at hm'
    obtain ⟨n, hn, x, hx, rfl⟩ := hm'
    have hnY : ∀ y ∈ Y, Commute y n := fun y hy => by
      have h1 := hmY y hy
      have h2 : Commute y x := hQX y hy x hx
      have h3 := h1.mul_right h2.inv_right
      rwa [mul_inv_cancel_right] at h3
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hfixY n hn hnY)) (Subgroup.mem_sup_right hx)
  have hZXE : Z ≤ E ⊔ X := fun z hz => hCM z hz.1 fun y hy =>
    (Subgroup.mem_centralizer_iff.1 hz.2) y (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))
  have hXE : X ≠ E := by
    intro e
    apply hZne
    have hMN : W = N := le_antisymm (sup_le (e ▸ hEN) le_rfl) le_sup_right
    have : Z ≤ N ⊓ Z := le_inf (inf_le_left.trans hMN.le) le_rfl
    rw [hNZ'] at this
    exact le_bot_iff.1 this
  have hMMD : W ≤ M R D := by
    refine sup_le (QD.le_M (mem_lambdaSet_commutator hR hiso hY' hXR hs).2)
      (sup_le QD.le_M_self (QD.le_M (mem_lambdaSet_comm hER
        (mem_lambdaSet_commutator hR hiso hY hDR hDp.2).2)))
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
  obtain ⟨g, hg, hge⟩ := Sec3.exists_conj_eq_of_mem_sup hR hiso hY' hY hYY'.symm hDl hDp
    (Subgroup.mem_sup_left hd) hd1 (Subgroup.mem_sup_right he) he1
  have hDg : conjSub D g = E :=
    Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hDR g) hER (hge ▸ conj_mem_conjSub g hd) he he1
  have hMME : W ≤ M R E := by
    rw [← hDg, ← Sec5.conjSub_M hR D g, ← hMinv g (Subgroup.mem_sup_left (sup_comm Y' Y ▸ hg))]
    exact Subgroup.map_mono hMMD
  have hXEl : X ∈ lambdaSet R E := by
    have hmem : X ∈ {B | B ∈ R ∧ B ≤ M R E} := ⟨hXR, le_sup_left.trans hMME⟩
    rw [(Q_eq_M h hER).2.1] at hmem
    exact hmem.resolve_left hXE
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZne
  obtain ⟨T, hTR, hTle, hzT⟩ := hXEl.2 z (hZXE z.2) (fun h1 => hz1 (Subtype.ext h1))
  have hTM : T ≤ W := hTle.trans (sup_le (hEN.trans le_sup_right) le_sup_left)
  have hTZ : T = Z := by
    rcases hFZ T hTR hTM with h1 | h1
    · exfalso
      have : (z : G) ∈ T ⊓ Z := ⟨hzT, z.2⟩
      rw [h1, Subgroup.mem_bot] at this
      exact hz1 (Subtype.ext this)
    · exact h1
  have hZR : Z ∈ R := hTZ ▸ hTR
  have hZYY' : Commuting Y Z ∧ Commuting Y' Z := by
    refine ⟨fun y hy w hw => ?_, fun y hy w hw => ?_⟩
    · exact (Subgroup.mem_centralizer_iff.1 hw.2) y
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))
    · exact (Subgroup.mem_centralizer_iff.1 hw.2) y
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy))
  have hZMA : Z ≤ M R A := hZXE.trans (sup_le (QD.le_M hE.1) (QD.le_M hX.1))
  have hmem : Z ∈ {B | B ∈ R ∧ B ≤ M R A} := ⟨hZR, hZMA⟩
  rw [(Q_eq_M h hA).2.1] at hmem
  rcases hmem with hZA | hZl
  ·
    have hline := sup_eq_of_le_of_commuting hR hiso hER hXR hA hXR hXEl.1.2.2
      (hZA ▸ hZXE) le_sup_right hX.1.1.2.1.symm
    obtain ⟨T', -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hX.1
    exact hXE ((huniq X ⟨hXR, le_sup_right, hX.2⟩).trans
      (huniq E ⟨hER, hline ▸ le_sup_left, hE.2⟩).symm)
  ·
    obtain ⟨T', ⟨hT'R, hT'le, hT'ψ⟩, -⟩ :=
      existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hZl
    have hT'A : T' ≠ A := fun e => hT'ψ.2.not_opposite hR hA₀.1 (e ▸ hA₀.2.symm)
    have hT'l : T' ∈ lambdaSet R A := by
      have hm : T' ∈ {B | B ∈ R ∧ B ≤ M R A} :=
        ⟨hT'R, hT'le.trans (sup_le QD.le_M_self hZMA)⟩
      rw [(Q_eq_M h hA).2.1] at hm
      exact hm.resolve_left hT'A
    have hc : ∀ W : Subgroup G, W ∈ leviSet R A A₀ → Commuting W Z → Commuting W T' :=
      fun W hW hWZ => (Commuting.sup_right hW.1.2.2.symm hWZ).mono le_rfl hT'le
    exact hfix T' ⟨hT'l, hT'ψ⟩ (hT'le.trans (sup_le_sup_left inf_le_left A))
      (hc Y' hY'l hZYY'.2) (hc Y hYl hZYY'.1)

end CaseE

section Roots

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K] {D : UniversalRootDatum K}

theorem linIndepPair_single_of_ht_neg (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hneg : ht γ < 0) {k : Fin D.rank} (hne : γ ≠ -Pi.single k 1) :
    LinIndepPair γ (Pi.single k 1) := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  have hk : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem k
  have hγi := isIndiv_of_divisible_eq_empty hdiv hγ
  have hki : Φ.IsIndiv (Pi.single k 1) := Φ.isIndiv_single k
  by_contra h
  rcases Φ.proportional γ hγ _ hk h with h1 | h1 | h1 | h1 | h1 | h1
  · rw [h1, ht_single] at hneg
    omega
  · exact hne h1
  · rw [h1, ht_nsmul, ht_single] at hneg
    omega
  · exact hγi _ (Φ.neg_mem _ hk) (by rw [h1, smul_neg])
  · exact hki γ hγ h1
  · exact hki (-γ) (Φ.neg_mem _ hγ) (by rw [h1, smul_neg])

theorem exists_ne_lt_zero_of_ht_neg (hdiv : D.divisible = ∅) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hneg : ht γ < 0) {k : Fin D.rank} (hne : γ ≠ -Pi.single k 1) :
    ∃ i, i ≠ k ∧ γ i < 0 := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  by_contra hcon
  simp only [not_exists, not_and, not_lt] at hcon
  have hle : ∀ j, γ j ≤ 0 := by
    rcases Φ.sign γ hγ with h | h
    · exfalso
      have : 0 ≤ ht γ := Finset.sum_nonneg fun j _ => h j
      omega
    · exact h
  have h0 : (1 : ℤ) • γ + (-γ k) • (Pi.single k 1 : Fin D.rank → ℤ) = 0 := by
    funext j
    by_cases hj : j = k
    · subst hj
      simp
    · simp only [Pi.add_apply, Pi.smul_apply, Pi.single_eq_of_ne hj, smul_zero, add_zero,
        one_smul, Pi.zero_apply]
      exact le_antisymm (hle j) (hcon j hj)
  exact one_ne_zero (linIndepPair_single_of_ht_neg hdiv hγ hneg hne 1 (-γ k) h0).1

theorem ht_neg_of_mem_openCone_single (hdiv : D.divisible = ∅) {γ ε : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hneg : ht γ < 0) {k : Fin D.rank} (hne : γ ≠ -Pi.single k 1)
    (hε : ε ∈ openCone D.roots γ (Pi.single k 1)) : ht ε < 0 := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  obtain ⟨i, hik, hi⟩ := exists_ne_lt_zero_of_ht_neg hdiv hγ hneg hne
  obtain ⟨hεr, p, q, hp, -, rfl⟩ := hε
  have hεi : (p • γ + q • (Pi.single k 1 : Fin D.rank → ℤ)) i < 0 := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.single_eq_of_ne hik, smul_zero, add_zero,
      nsmul_eq_mul]
    have : (1 : ℤ) ≤ p := by exact_mod_cast hp
    nlinarith
  refine ht_neg_of_nonpos hεr ?_
  rcases Φ.sign _ hεr with h | h
  · exact absurd (h i) (not_le.2 hεi)
  · exact h

theorem ht_neg_of_mem_openCone_neg_single (hdiv : D.divisible = ∅) {γ ε : Fin D.rank → ℤ}
    (hγ : γ ∈ D.roots) (hneg : ht γ < 0) {k : Fin D.rank} (hne : γ ≠ -Pi.single k 1)
    (hε : ε ∈ openCone D.roots γ (-Pi.single k 1)) : ht ε < 0 ∧ ε ≠ -Pi.single k 1 := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  obtain ⟨i, hik, hi⟩ := exists_ne_lt_zero_of_ht_neg hdiv hγ hneg hne
  obtain ⟨hεr, p, q, hp, -, rfl⟩ := hε
  have hεi : (p • γ + q • (-Pi.single k 1 : Fin D.rank → ℤ)) i < 0 := by
    rw [Pi.add_apply, Pi.smul_apply, Pi.smul_apply, Pi.neg_apply, Pi.single_eq_of_ne hik,
      neg_zero, smul_zero, add_zero, nsmul_eq_mul]
    have : (1 : ℤ) ≤ p := by exact_mod_cast hp
    nlinarith
  refine ⟨ht_neg_of_nonpos hεr ?_, fun e => ?_⟩
  · rcases Φ.sign _ hεr with h | h
    · exact absurd (h i) (not_le.2 hεi)
    · exact h
  · rw [e] at hεi
    simp [Pi.single_eq_of_ne hik] at hεi

end Roots

section Frame

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.RootSystem
  CFSG.LieType.Steinberg

variable {K : Type*} [Group K]

structure CompFrame (R : Set (Subgroup G)) (A A₀ : Subgroup G) (D : UniversalRootDatum K)
    (n : Fin D.rank → K) (H : Fin D.rank → Subgroup K) (Ψ : K →* G) : Prop where
  hct : IsCTGroupDatum (coxeterMatrix D.isFiniteType).toCoxeterSystem
    (weylAction D.isFiniteType) D.roots D.rootGroup n H
  hext : SteinbergExtras D n H
  hdiv : D.divisible = ∅
  mem : ∀ γ ∈ D.roots, (D.rootGroup γ).map Ψ ∈ leviSet R A A₀
  range : ∀ g, Ψ g ∈ levi R A A₀
  surjComp : ∀ v ∈ levi R A A₀, ∃ g c, (∀ y, Commute c (Ψ y)) ∧ v = Ψ g * c
  opp : ∀ k, Opposite ((D.rootGroup (Pi.single k 1)).map Ψ)
    ((D.rootGroup (-Pi.single k 1)).map Ψ)

structure LeviFrame (R : Set (Subgroup G)) (A A₀ : Subgroup G) (D : UniversalRootDatum K)
    (n : Fin D.rank → K) (H : Fin D.rank → Subgroup K) (Ψ : K →* G) : Prop
    extends CompFrame R A A₀ D n H Ψ where
  surj : ∀ v ∈ levi R A A₀, ∃ g, Ψ g = v

variable {A A₀ : Subgroup G} {D : UniversalRootDatum K} {n : Fin D.rank → K}
  {H : Fin D.rank → Subgroup K} {Ψ : K →* G}

theorem map_rootGroup_le_map_negUnipotent {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots)
    (h : ht γ < 0) : (D.rootGroup γ).map Ψ ≤ (negUnipotent D).map Ψ :=
  Subgroup.map_mono (rootGroup_le_negUnipotent hγ h)

private theorem conjSub_conjSub_inv' (X : Subgroup G) (g : G) : conjSub (conjSub X g) g⁻¹ = X := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem mem_lambdaSet_of_commuting_negUnipotent (h : Hyp G R) (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (hF : CompFrame R A A₀ D n H Ψ) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ)) (k : Fin D.rank)
    (hEk : ¬ Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ)) :
    E ∈ lambdaSet R ((D.rootGroup (-Pi.single k 1)).map Ψ) := by
  set Φ := RootSystem.ofCartan D.isFiniteType D.divisible
  set P := (D.rootGroup (Pi.single k 1)).map Ψ with hPdef
  set Q := (D.rootGroup (-Pi.single k 1)).map Ψ with hQdef
  set U := (negUnipotent D).map Ψ with hUdef
  have hk : (Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.single_mem k
  have hk' : (-Pi.single k 1 : Fin D.rank → ℤ) ∈ D.roots := Φ.neg_mem _ hk
  have hkneg : ht (-Pi.single k 1 : Fin D.rank → ℤ) < 0 := by
    rw [ht_neg, ht_single]
    omega
  have hPl : P ∈ leviSet R A A₀ := hF.mem _ hk
  have hQl : Q ∈ leviSet R A A₀ := hF.mem _ hk'
  have hMU : ∀ γ ∈ D.roots, ht γ < 0 → (D.rootGroup γ).map Ψ ≤ U := fun γ hγ h =>
    map_rootGroup_le_map_negUnipotent hγ h
  have hQE : Commuting Q E := (hEU.mono le_rfl (hMU _ hk' hkneg)).symm
  have hs : Special R P E :=
    (special_of_not_commuting_of_mem_leviSet h hA hE hPl hEk).symm
  have hC1 : ∀ ε ∈ D.roots, ht ε < 0 → ε ≠ -Pi.single k 1 →
      Commuting ⁅P, E⁆ ((D.rootGroup ε).map Ψ) := by
    intro ε hε hεn hεk
    refine commuting_iff_commutator_eq_bot.2
      (Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_)
    · rw [commuting_iff_commutator_eq_bot.1 (hEU.mono le_rfl (hMU ε hε hεn)),
        Subgroup.commutator_bot_left]
    · have hle : ⁅(D.rootGroup ε).map Ψ, P⁆ ≤ U :=
        (commutator_map_rootGroup_le hF.hext Ψ hε hk
          (linIndepPair_single_of_ht_neg hF.hdiv hε hεn hεk)).trans
          (iSup₂_le fun ζ hζ => hMU ζ hζ.1 (ht_neg_of_mem_openCone_single hF.hdiv hε hεn hεk hζ))
      exact le_bot_iff.1 ((Subgroup.commutator_mono hle le_rfl).trans
        (commuting_iff_commutator_eq_bot.1 hEU.symm).le)
  have hC2 : ∀ ε ∈ D.roots, ht ε < 0 → ε ≠ -Pi.single k 1 →
      Commuting ⁅Q, ⁅P, E⁆⁆ ((D.rootGroup ε).map Ψ) := by
    intro ε hε hεn hεk
    refine commuting_iff_commutator_eq_bot.2
      (Subgroup.commutator_commutator_eq_bot_of_rotate ?_ ?_)
    · rw [commuting_iff_commutator_eq_bot.1 (hC1 ε hε hεn hεk), Subgroup.commutator_bot_left]
    · have hind : LinIndepPair ε (-Pi.single k 1) := fun a b hab =>
        (linIndepPair_single_of_ht_neg hF.hdiv hε hεn hεk a (-b)
          (by rw [neg_smul, ← smul_neg]; exact hab)).imp_right neg_eq_zero.1
      have hcomm : Commuting ⁅P, E⁆
          (⨆ ζ ∈ openCone D.roots ε (-Pi.single k 1), (D.rootGroup ζ).map Ψ) := by
        rw [commuting_iff_le_centralizer]
        refine iSup₂_le fun ζ hζ => commuting_iff_le_centralizer.1 ?_
        obtain ⟨h1, h2⟩ := ht_neg_of_mem_openCone_neg_single hF.hdiv hε hεn hεk hζ
        exact hC1 ζ hζ.1 h1 h2
      exact le_bot_iff.1 ((Subgroup.commutator_mono
        (commutator_map_rootGroup_le hF.hext Ψ hε hk' hind) le_rfl).trans
        (commuting_iff_commutator_eq_bot.1 hcomm.symm).le)
  refine CaseE.mem_lambdaSet_of_commuting_of_forall h hA hAne hA₀ hQl hPl
    (hF.opp k).symm hE hQE hs ?_
  intro T hT hTle hPT hQT
  have hTU : Commuting T U := by
    refine commuting_map_negUnipotent fun γ hγ hγn => ?_
    by_cases hγk : γ = -Pi.single k 1
    · subst hγk
      exact hQT.symm
    · have h1 : Commuting A ((D.rootGroup γ).map Ψ) := (hF.mem γ hγ).1.2.2
      have h2 : Commuting E ((D.rootGroup γ).map Ψ) := hEU.mono le_rfl (hMU γ hγ hγn)
      exact (h1.sup_left (h2.sup_left ((hC1 γ hγ hγn hγk).sup_left
        (hC2 γ hγ hγn hγk)))).mono hTle le_rfl
  obtain ⟨v, hv, hvT⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hE hT
  obtain ⟨g, c, hc, rfl⟩ := hF.surjComp v hv
  have hcfix : ∀ X : Subgroup K, conjSub (X.map Ψ) c⁻¹ = X.map Ψ := fun X =>
    conjSub_of_forall_commute fun _ ⟨y, _, hy⟩ => hy ▸ (hc y).inv_left
  have hET : conjSub E (Ψ g) = conjSub T c⁻¹ := by
    rw [← hvT, ← (hc g).eq, conjSub_mul, conjSub_conjSub_inv']
  have hEg : Commuting (conjSub E (Ψ g)) U := by
    rw [hET]
    have h1 := hTU.conjSub c⁻¹
    rwa [hUdef, hcfix] at h1
  obtain ⟨t, htT, hte⟩ := exists_mem_map_conjSub_eq hF.hct hF.hext Ψ hEU g hEg
  obtain ⟨s, hs', rfl⟩ := htT
  have hPs : conjSub P (Ψ s) = P := by
    rw [hPdef, map_conjSub_eq,
      (RankOne.map_conj_eq_self_iff).2 (iSup_le_normalizer_rootGroup hF.hct hk hs')]
  apply hEk
  have h1 : Commuting (conjSub E (Ψ s)) (conjSub P (Ψ s)) := by
    rw [hPs, hte, hET]
    have h2 := hPT.symm.conjSub c⁻¹
    rwa [hPdef, hcfix] at h2
  have h2 := h1.conjSub (Ψ s)⁻¹
  rwa [conjSub_conjSub_inv', conjSub_conjSub_inv'] at h2

theorem natural_of_commuting_negUnipotent (h : Hyp G R) (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (hF : CompFrame R A A₀ D n H Ψ) {E : Subgroup G}
    (hE : E ∈ lambdaStar R A A₀) (hEU : Commuting E ((negUnipotent D).map Ψ)) (k : Fin D.rank) :
    Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ) ∨
      (E ∈ lambdaSet R ((D.rootGroup (-Pi.single k 1)).map Ψ) ∧
        Special R E ((D.rootGroup (Pi.single k 1)).map Ψ)) := by
  by_cases hEk : Commuting E ((D.rootGroup (Pi.single k 1)).map Ψ)
  · exact Or.inl hEk
  · refine Or.inr ⟨mem_lambdaSet_of_commuting_negUnipotent h hA hAne hmax hA₀ hF hE hEU k hEk,
      special_of_not_commuting_of_mem_leviSet h hA hE
        (hF.mem _ ((RootSystem.ofCartan D.isFiniteType D.divisible).single_mem k)) hEk⟩

end Frame

end CFSG.Timmesfeld.ARS
