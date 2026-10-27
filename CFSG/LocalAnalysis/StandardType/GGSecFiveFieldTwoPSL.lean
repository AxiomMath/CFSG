module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoCommon
public import CFSG.LocalAnalysis.StandardType.GGSecFiveFieldTwoPSLChart
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.FEPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPSL
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPSL
public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeIRGTyLabelAux
public import CFSG.LocalAnalysis.StandardType.GGSixTCLiftGroup

public section

namespace CFSG.StandardType

namespace FieldTwoPSL

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.LieType.Universal
  CFSG.StandardType.ClassicalPosition CFSG.StandardType.S2MathFi1035Pos
open scoped Matrix

private theorem odd_orderOf_lift {X : Type} [Group X] (m f : ℕ) (hf : 1 ≤ f)
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {p : ℕ} (hp : Odd p) {d : X} (hdp : d ^ p = 1)
    {s : GL (Fin (m + 1)) (GaloisField 2 f)}
    (hs : IsGLLift Matrix.SpecialLinearGroup.toGL ψ s d) : Odd (orderOf s) := by
  have : Fintype (GaloisField 2 f) := Fintype.ofFinite _
  have hsp : IsGLLift Matrix.SpecialLinearGroup.toGL ψ (s ^ p) 1 := by
    have h := hs.pow p
    rwa [hdp] at h
  obtain ⟨c, hc_eq⟩ := isGLLift_unique_PSL m (GaloisField 2 f) ψ hψ hsp isGLLift_one
  have hsmat : ((s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))) ^ p =
      Matrix.scalar (Fin (m + 1)) c := by
    have h := hc_eq
    rw [inv_one, one_mul] at h
    simpa only [Units.val_pow_eq_pow_val] using h
  have hcne : c ≠ 0 := by
    have hunit : IsUnit ((s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) ^ p) :=
      IsUnit.pow p ⟨s, rfl⟩
    have hm : IsUnit ((Matrix.scalar (Fin (m + 1)) c :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)).det) := by
      rw [← hsmat]
      exact (Matrix.isUnit_iff_isUnit_det
        (A := (s : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)) ^ p)).mp hunit
    have hdet : (Matrix.scalar (Fin (m + 1)) c :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f)).det = c ^ (m + 1) := by
      rw [Matrix.scalar_apply, Matrix.det_diagonal]
      simp [Finset.prod_const, Fintype.card_fin]
    rw [hdet] at hm
    exact ((isUnit_pow_iff (a := c) (n := m + 1) (by omega)).mp hm).ne_zero
  let u : (GaloisField 2 f)ˣ := Units.mk0 c hcne
  have hspu : s ^ p = Matrix.GeneralLinearGroup.scalar (Fin (m + 1)) u := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hsmat, Matrix.GeneralLinearGroup.coe_scalar]
    rfl
  have hpow1 : s ^ (p * orderOf u) = 1 := by
    rw [pow_mul, hspu, ← map_pow, pow_orderOf_eq_one, map_one]
  have hdvd : orderOf s ∣ p * orderOf u := orderOf_dvd_iff_pow_eq_one.mpr hpow1
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hoddF : Odd (Nat.card (GaloisField 2 f) - 1) := by
    rw [hcard]
    have h2 : 2 ≤ 2 ^ f := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
    refine ⟨2 ^ (f - 1) - 1, ?_⟩
    have h3 : 2 ^ f = 2 * 2 ^ (f - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    have h4 : 1 ≤ 2 ^ (f - 1) := Nat.one_le_two_pow
    omega
  have hu_pow : u ^ (Nat.card (GaloisField 2 f) - 1) = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, Nat.card_eq_fintype_card]
    exact FiniteField.pow_card_sub_one_eq_one (u : GaloisField 2 f) (Units.ne_zero u)
  have hodd_u : Odd (orderOf u) :=
    Odd.of_dvd_nat hoddF (orderOf_dvd_iff_pow_eq_one.mpr hu_pow)
  exact Odd.of_dvd_nat (Nat.odd_mul.mpr ⟨hp, hodd_u⟩) hdvd

theorem exists_lift_component {X : Type} [Group X] [Finite X] (m f : ℕ) (hf : 1 ≤ f)
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {x : X}
    (hxN : x ∈ Subgroup.normalizer (ψ.range : Set X))
    (hdiag : GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ x) {p : ℕ}
    (hp : Odd p) (hxp : x ^ p = 1)
    {L : Subgroup X} (hL : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x})) :
    ∃ (s : GL (Fin (m + 1)) (GaloisField 2 f))
      (L' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f))),
      L'.map ψ = L ∧
      IsComponentOf L'
        ((Subgroup.centralizer ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f)))).comap
          Matrix.SpecialLinearGroup.toGL) ∧
      Odd (orderOf s) := by
  obtain ⟨s, hsl⟩ := exists_isGLLift_PSL m (GaloisField 2 f) ψ hψ hxN hdiag
  have hodd : Odd (orderOf s) := odd_orderOf_lift m f hf ψ hψ hp hxp hsl
  have hcentD : Subgroup.centralizer (Subgroup.zpowers x : Set X) =
      Subgroup.centralizer ({x} : Set X) := by
    rw [Subgroup.zpowers_eq_closure x]
    exact Subgroup.centralizer_closure ({x} : Set X)
  have hJ : IsComponentOf L (ψ.range ⊓ Subgroup.centralizer (Subgroup.zpowers x : Set X)) := by
    rw [hcentD]
    exact hL
  let P : GL (Fin (m + 1)) (GaloisField 2 f) → Prop := fun s' => ∃ k : ℤ, s' = s ^ k
  let T : Set (GL (Fin (m + 1)) (GaloisField 2 f)) :=
    {s' | P s' ∧ ∃ d ∈ Subgroup.zpowers x, IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' d}
  have hlift : ∀ d ∈ Subgroup.zpowers x,
      ∃ s', P s' ∧ IsGLLift Matrix.SpecialLinearGroup.toGL ψ s' d := by
    intro d hd
    rw [Subgroup.mem_zpowers_iff] at hd
    obtain ⟨k, hk⟩ := hd
    rw [← hk]
    exact ⟨s ^ k, ⟨k, rfl⟩, hsl.zpow_of_injective Matrix.SpecialLinearGroup.toGL_injective k⟩
  obtain ⟨L', hL'comp, hL'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift Matrix.SpecialLinearGroup.toGL
      Matrix.SpecialLinearGroup.toGL_injective ψ hψ P hJ hlift
  have hcentT : Subgroup.centralizer ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f))) =
      Subgroup.centralizer T := by
    apply le_antisymm
    · intro y hy
      have hcomm : Commute s y :=
        (Subgroup.mem_centralizer_iff.mp hy) s (Set.mem_singleton s)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      obtain ⟨⟨k, rfl⟩, -⟩ := ht
      exact (hcomm.zpow_left k).eq
    · intro y hy
      rw [Subgroup.mem_centralizer_iff] at hy ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      rw [hh]
      exact hy s ⟨⟨1, by rw [zpow_one]⟩, x,
        Subgroup.mem_zpowers_iff.mpr ⟨1, by rw [zpow_one]⟩, hsl⟩
  refine ⟨s, L', hL'map, ?_, hodd⟩
  rw [hcentT]
  exact hL'comp

private theorem isSolvable_SL_two_of_card_two {F : Type} [Field F] [Finite F]
    (hcard : Nat.card F = 2) :
    Group.IsSolvable (Matrix.SpecialLinearGroup (Fin 2) F) := by
  have : Fintype F := Fintype.ofFinite F
  have hF : Fintype.card F = 2 := by
    rw [← Nat.card_eq_fintype_card]
    exact hcard
  obtain ⟨e⟩ := TauCeti.nonempty_mulEquiv_permFinThree hF
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) :=
    Equiv.Perm.isSolvable (by norm_num)
  have hGL : Group.IsSolvable (GL (Fin 2) F) :=
    Group.isSolvable_of_surjective (f := e.symm.toMonoidHom) e.symm.surjective
  exact Group.isSolvable_of_isSolvable_injective
    (f := Matrix.SpecialLinearGroup.toGL) Matrix.SpecialLinearGroup.toGL_injective

section Cert


theorem block_of_component {X : Type} [Group X] [Finite X] (m f : ℕ) (hf : 1 ≤ f)
    (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* X)
    (hψ : ψ.ker ≤ Subgroup.center _) {L : Subgroup X}
    (hdet : ∀ {r f' : ℕ}, LieModel (↥L ⧸ Subgroup.center ↥L) .PSL r 2 f' → f' = 1)
    (s : GL (Fin (m + 1)) (GaloisField 2 f))
    (L' : Subgroup (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)))
    (hL'L : L'.map ψ = L)
    (hL' : IsComponentOf L'
      ((Subgroup.centralizer ({s} : Set (GL (Fin (m + 1)) (GaloisField 2 f)))).comap
        Matrix.SpecialLinearGroup.toGL))
    (hodd : Odd (orderOf s)) :
    f = 1 ∧ ∃ (k r' : ℕ) (eidx : Fin (k + 1) ⊕ Fin r' ≃ Fin (m + 1))
      (P Pinv : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 f))
      (hPP : P * Pinv = 1) (hPinvP : Pinv * P = 1),
      2 ≤ k ∧ (bmPSL_embedHom eidx P Pinv hPP hPinvP).range = L' := by
  classical
  set S : Set (GL (Fin (m + 1)) (GaloisField 2 f)) := {s} with hSdef
  have hS : ∀ a ∈ S, ∀ b ∈ S, Commute a b := by
    intro a ha b hb
    rw [hSdef, Set.mem_singleton_iff] at ha hb
    rw [ha, hb]
  have hoddS : ∀ a ∈ S, Odd (orderOf a) := by
    intro a ha
    rw [hSdef, Set.mem_singleton_iff] at ha
    rw [ha]
    exact hodd
  obtain ⟨e, he, hJe⟩ := exists_isComponentOf_glBlockCentralizer_PSL m (GaloisField 2 f) S hS hL'
  by_cases hdeg : 2 ≤ blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e
  · exfalso
    obtain ⟨m'', f', hlt, hLM⟩ := ggSixLSevenFieldExtModel_PSL m f hf ψ hψ S hS hoddS he hJe hdeg
    rw [hL'L] at hLM
    have hf1 : f' = 1 := hdet hLM
    omega
  have hdeg' : blockDegree (Algebra.adjoin (GaloisField 2 f) (Units.val '' S)) e < 2 := by omega
  obtain ⟨k, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hk1, hJ'eq, -⟩ :=
    exists_blockModel_PSL_rank m f S hS he hdeg' hJe
  obtain ⟨r, r', eidx, P, Pinv, hPP, hPinvP, hconv, hrfin, -, -⟩ := bmPSL_exists_conj_diag he.2.1
  have hrange := bmPSL_embedHom_range_eq hS he hdeg' hPP hPinvP hconv rfl
  rw [← hJ'eq] at hrange
  have hrk : r = k + 1 := by rw [hrfin, ← hk1]
  subst hrk
  have hrange' : (ψ.comp (bmPSL_embedHom eidx P Pinv hPP hPinvP)).range = L := by
    rw [MonoidHom.range_comp, hrange, hL'L]
  have hker' : (ψ.comp (bmPSL_embedHom eidx P Pinv hPP hPinvP)).ker ≤
      Subgroup.center (ggU .PSL (k + 1) f).K := by
    intro y hy
    exact Subgroup.comap_center_le_center (f := bmPSL_embedHom eidx P Pinv hPP hPinvP)
      bmPSL_embedHom_injective (hψ hy)
  have hnot22 : ¬ (k = 1 ∧ f = 1) := by
    rintro ⟨rfl, rfl⟩
    have hcard : Nat.card (GaloisField 2 1) = 2 := by
      rw [GaloisField.card 2 1 one_ne_zero]
      norm_num
    have := isSolvable_SL_two_of_card_two hcard
    have : Group.IsSolvable (bmPSL_embedHom eidx P Pinv hPP hPinvP).range :=
      Group.isSolvable_of_surjective (f := (bmPSL_embedHom eidx P Pinv hPP hPinvP).rangeRestrict)
        (bmPSL_embedHom eidx P Pinv hPP hPinvP).rangeRestrict_surjective
    have hsol : Group.IsSolvable L' := hrange ▸ inferInstance
    obtain ⟨-, -, hperf, hsimple⟩ := hL'
    have : Nontrivial (↥L' ⧸ Subgroup.center ↥L') := hsimple.toNontrivial
    have : Nontrivial L' :=
      Function.Surjective.nontrivial (QuotientGroup.mk'_surjective (Subgroup.center L'))
    have : Group.IsPerfect L' := Group.IsPerfect.mk hperf
    exact (Group.IsPerfect.not_isSolvable L') hsol
  rcases Nat.eq_zero_or_pos k with hk0 | hkpos
  ·
    exfalso
    subst hk0
    have hsub : Subsingleton (Matrix.SpecialLinearGroup (Fin 1) (GaloisField 2 f)) := by
      constructor
      intro a b
      have ha : (a : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) default default = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe a
        rwa [Matrix.det_unique] at h
      have hb : (b : Matrix (Fin 1) (Fin 1) (GaloisField 2 f)) default default = 1 := by
        have h := Matrix.SpecialLinearGroup.det_coe b
        rwa [Matrix.det_unique] at h
      ext i j
      rw [Subsingleton.elim i default, Subsingleton.elim j default, ha, hb]
    have hbot : L' = ⊥ := by
      rw [← hrange, eq_bot_iff]
      rintro _ ⟨y, rfl⟩
      have hy : y = 1 := @Subsingleton.elim _ hsub y 1
      rw [hy, map_one]
      exact Subgroup.one_mem _
    have hsimple := hL'.2.2.2
    subst hbot
    exact (not_nontrivial_iff_subsingleton.mpr inferInstance) hsimple.toNontrivial
  have hq2 : 2 ≤ 2 ^ f := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hadm : StatedLieAdmissible .PSL (k + 1) 2 f := by
    refine ⟨Nat.prime_two, hf, by omega, fun h => ?_, fun h => ?_⟩
    · have h1 := (Prod.mk.inj h).1
      have h2 := (Prod.mk.inj h).2
      have hf1 : f = 1 := by
        by_contra hf1
        have : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) (by omega)
        omega
      exact hnot22 ⟨by omega, hf1⟩
    · have h2 := (Prod.mk.inj h).2
      have : (2 : ℕ) ∣ 2 ^ f := dvd_pow_self 2 (by omega)
      omega
  have hLM := RCKRP.irg_lieModel_quot (Or.inl rfl) hadm
    (ψ.comp (bmPSL_embedHom eidx P Pinv hPP hPinvP)) hrange' hker'
  have hf1 : f = 1 := hdet hLM
  refine ⟨hf1, k, r', eidx, P, Pinv, hPP, hPinvP, ?_, hrange⟩
  by_contra hk2
  exact hnot22 ⟨by omega, hf1⟩

theorem ggSecFiveQTwoFieldTwoSelectedAt_PSL : GGSecFiveQTwoFieldTwoSelectedAt .PSL := by
  intro G _ _ B Bs x L D J hC hq n f ψ hpres hdiag
  obtain ⟨⟨hadm, -⟩, ⟨hrange, hker⟩, -, -⟩ := hpres
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by have := hadm.2.2.1; omega⟩
  have hf : 1 ≤ f := hadm.2.1
  let ψ₀ : Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f) →* G := ψ
  have hψ : ψ₀.ker ≤ Subgroup.center _ := hker
  have hdiag' : GGPsiInnerDiag (SpecialLinear.rootDatum m (GaloisField 2 f)) ψ₀ x := hdiag
  have hgen : ⨆ γ ∈ (SpecialLinear.rootDatum m (GaloisField 2 f)).roots,
      (SpecialLinear.rootDatum m (GaloisField 2 f)).rootGroup γ = ⊤ :=
    (SpecialLinear.isCTGroupDatum m (GaloisField 2 f)).iSup_eq_top
  have hxN := mem_normalizer_of_ggPsiInnerDiag hgen hdiag'
  have hsstar := hC.1.2.2.2.2.2.2.1
  have hx3 : x ^ 3 = 1 := hsstar.1.1.2 x hsstar.2.1
  have hL : IsComponentOf L (ψ₀.range ⊓ Subgroup.centralizer {x}) := by
    change IsComponentOf L (ψ.range ⊓ Subgroup.centralizer {x})
    rw [hrange]
    exact hC.isComponentOf_ggG0_inf
  obtain ⟨s, L', hL'L, hL', hodd⟩ :=
    exists_lift_component m f hf ψ₀ hψ hxN hdiag' (by decide) hx3 hL
  obtain ⟨lab, hl, hn1, hne, -, hM⟩ := hC.exists_markedModel_of_qTwo hq
  obtain ⟨hf1, k, r', eidx, P, Pinv, hPP, hPinvP, hk2, hιr⟩ :=
    block_of_component m f hf ψ₀ hψ (fun h => (fieldTwo_typeDet hl hn1 hne hM (Or.inl rfl) h).1)
      s L' hL'L hL' hodd
  subst hf1
  have hm2 : 2 ≤ m := by
    have h := Fintype.card_congr eidx
    simp only [Fintype.card_sum, Fintype.card_fin] at h
    omega
  set ι := bmPSL_embedHom eidx P Pinv hPP hPinvP with hιdef
  have hrangeL : (ψ₀.comp ι).range = L := by rw [MonoidHom.range_comp, hιr, hL'L]
  have hkerL : (ψ₀.comp ι).ker ≤ Subgroup.center (ggU .PSL (k + 1) 1).K := by
    intro y hy
    exact Subgroup.comap_center_le_center (f := ι) bmPSL_embedHom_injective (hψ hy)
  obtain ⟨γ, model₀, hm₀⟩ :=
    exists_selectedModel_PSL_chart (F := GaloisField 2 1) (m := m) (by omega)
  obtain ⟨δ, model₁, hm₁⟩ :=
    exists_selectedModel_PSL_chart (F := GaloisField 2 1) (m := k) (by omega)
  obtain ⟨u₀, hu₀⟩ :=
    exists_conj_embM_eq_embedMat hm2 (by omega : 2 ≤ k + 1) eidx P Pinv hPP hPinvP
  have hpt : ∀ A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 1),
      (MulAut.conj u₀) (model₀.phi A) = ι (model₁.phi A) := by
    intro A
    rw [MulAut.conj_apply]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hm₀]
    change _ = bmPSL_embedMat eidx P Pinv
      ((model₁.phi A : Matrix.SpecialLinearGroup (Fin (k + 1)) (GaloisField 2 1)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (GaloisField 2 1))
    rw [hm₁]
    exact hu₀ _
  refine ⟨.PSL, k + 1, ψ₀.comp ι, ?_, ?_, hkerL, hrangeL, γ, δ, model₀, model₁, u₀, ?_⟩
  · exact ⟨Nat.prime_two, le_rfl, by omega, fun h => by have := (Prod.mk.inj h).1; omega,
      fun h => by have := (Prod.mk.inj h).1; omega⟩
  · show 2 ≤ k
    exact hk2
  · congr 1
    ext A
    exact congrArg ψ₀ (hpt A)

end Cert

end FieldTwoPSL

end CFSG.StandardType

end
