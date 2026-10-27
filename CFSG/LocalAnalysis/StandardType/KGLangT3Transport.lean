module

public import CFSG.LocalAnalysis.StandardType.KGLangT3Defs
public import CFSG.LocalAnalysis.StandardType.GGTriD4LineTransport
import CFSG.LocalAnalysis.StandardType.GGIOneExcLift
import CFSG.LocalAnalysis.StandardType.GGTriD4KnownInputsModel
import CFSG.LocalAnalysis.StandardType.GGTableBExcSmallRestTri
import CFSG.LieType.Simplicity.TrialityD4

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private lemma l02qj8_two_pow_mod_three_odd {n : ℕ} (hn : Odd n) : 2 ^ n % 3 = 2 := by
  obtain ⟨k, rfl⟩ := hn
  rw [pow_succ', pow_mul]
  norm_num [Nat.mul_mod, Nat.pow_mod]

private lemma l02qj8_even_of_three_dvd_two_pow_sub_one {n : ℕ} (h : 3 ∣ 2 ^ n - 1) :
    Even n := by
  rcases Nat.even_or_odd n with hev | hodd
  · exact hev
  · exfalso
    have h1 : 2 ^ n % 3 = 2 := l02qj8_two_pow_mod_three_odd hodd
    have h2 : 2 ^ n % 3 = 1 := by
      have hx : 1 ≤ 2 ^ n := Nat.one_le_two_pow
      have h0 : (2 ^ n - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
      calc 2 ^ n % 3 = (2 ^ n - 1 + 1) % 3 := by rw [Nat.sub_add_cancel hx]
        _ = ((2 ^ n - 1) % 3 + 1 % 3) % 3 := by rw [Nat.add_mod]
        _ = 1 := by simp [h0]
    omega

private lemma l02qj8_quotientCongr_symm_mk {G H : Type*} [Group G] [Group H]
    (G' : Subgroup G) (H' : Subgroup H) [G'.Normal] [H'.Normal]
    (e : G ≃* H) (he : Subgroup.map (e : G →* H) G' = H') (x : H) :
    (QuotientGroup.congr G' H' e he).symm (QuotientGroup.mk' H' x) =
      QuotientGroup.mk' G' (e.symm x) := by
  rw [MulEquiv.symm_apply_eq]
  simp only [QuotientGroup.mk'_apply]
  rw [QuotientGroup.congr_mk, MulEquiv.apply_symm_apply]

private lemma l02qj8_thetaTransport_apply {G H P : Type*} [Group G] [Group H] [Group P]
    (G' : Subgroup G) (H' : Subgroup H) [G'.Normal] [H'.Normal]
    (e : G ≃* H) (he : Subgroup.map (e : G →* H) G' = H')
    (θ : G ⧸ G' ≃* P) (x : H) :
    ((QuotientGroup.congr G' H' e he).symm.trans θ) (QuotientGroup.mk' H' x) =
      θ (QuotientGroup.mk' G' (e.symm x)) := by
  rw [MulEquiv.trans_apply, l02qj8_quotientCongr_symm_mk]

private lemma l02qj8_kgInducedAut_apply {X R : Type*} [Group X] [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (α : MulAut X) (x : X) :
    kgInducedAut θ α (θ (QuotientGroup.mk' (Subgroup.center X) x)) =
      θ (QuotientGroup.mk' (Subgroup.center X) (α x)) := by
  show MulAut.congr θ (centerQuotAut X α) (θ (QuotientGroup.mk' (Subgroup.center X) x)) = _
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rfl

private lemma l02qj8_kgInducedAut_conj {X R : Type*} [Group X] [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (h : X) :
    kgInducedAut θ (MulAut.conj h) =
      MulAut.conj (θ (QuotientGroup.mk' (Subgroup.center X) h)) := by
  ext y
  obtain ⟨q, rfl⟩ := θ.surjective y
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (Subgroup.center X) q
  rw [l02qj8_kgInducedAut_apply]
  simp only [MulAut.conj_apply, map_mul, map_inv]

private lemma l02qj8_map_centralizer_singleton {X R : Type*} [Group X] [Group R]
    (ψ : X →* R) (hψ : Function.Surjective ψ) (hinj : Function.Injective ψ) (a : X) :
    (Subgroup.centralizer ({a} : Set X)).map ψ = Subgroup.centralizer ({ψ a} : Set R) := by
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    simp only [Subgroup.mem_centralizer_iff] at hx ⊢
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    show ψ a * ψ x = ψ x * ψ a
    rw [← map_mul, ← map_mul, hx a (Set.mem_singleton a)]
  · intro y hy
    obtain ⟨x, rfl⟩ := hψ y
    refine Subgroup.mem_map_of_mem ψ ?_
    simp only [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    rw [hz]
    apply hinj
    rw [map_mul, map_mul]
    exact hy (ψ a) (Set.mem_singleton (ψ a))

theorem kgLangT3_cont_of_strong {n : ℕ} (hn : 1 ≤ n) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 3) (h : KGLangT3Strong n K)
    (F : Set (MulAut (GGTriD4R n K))) :
    KGLangAxisT3Cont (GGTriD4R n K) (GGTriD4ID n K) F := by
  have hs : IsSimpleGroup (GGTriD4R n K) := by
    have hmodel : CFSG.Blueprint.ChevalleyExceptionalModel (GGTriD4R n K)
        CFSG.Open.StatedLieTag.trialityD4 2 n :=
      ⟨⟨Nat.prime_two, hn, rfl⟩,
        twistedChevalleyModel_largeEven CFSG.Blueprint.Chevalley.TwistTag.D4 (n := n) hK⟩
    exact (CFSG.LieType.Simplicity.fam_3d4_simplicity (GGTriD4R n K) 2 n hmodel).2
  have hinn : GGTriD4ID n K =
      Set.range (MulAut.conj : GGTriD4R n K →* MulAut (GGTriD4R n K)) :=
    ggTriD4InnDiagInput_holds n hn K hK hs
  have hinn' : GGTriD4ID n K = (kgLangT3Inn n K : Set (MulAut (GGTriD4R n K))) := by
    rw [kgLangT3Inn, MonoidHom.coe_range]
    exact hinn
  intro X _ _ θ hperf A hA hAI α₀ hα₀A hα₀I hg hgne hconjJ₀ J₀ hJ₀ E _ _ θ₀ hAt
  have hZcenter : Subgroup.center X = ⊥ := ggTriD4SchurInput_holds n hn K hK hs X hperf θ
  let ψ : X →* GGTriD4R n K := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center X))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerψ : ψ.ker = ⊥ := by
    have h1 : ψ.ker = (QuotientGroup.mk' (Subgroup.center X)).ker :=
      MonoidHom.ker_comp_of_injective (QuotientGroup.mk' (Subgroup.center X)) θ.toMonoidHom
        θ.injective
    rw [h1, QuotientGroup.ker_mk', hZcenter]
  have hinjψ : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hkerψ
  let ρ : MulAut X →* MulAut (GGTriD4R n K) := kgInducedAut θ
  let A' : Subgroup (MulAut (GGTriD4R n K)) := A.map ρ
  have hA' : IsElemAbelian 3 A' := ggIE_isElemAbelian_map ρ hA
  have hα₀'A : ρ α₀ ∈ A' := Subgroup.mem_map_of_mem ρ hα₀A
  have hα₀'Inn : ρ α₀ ∉ kgLangT3Inn n K := by
    have h' := hα₀I
    rw [hinn'] at h'
    exact h'
  have hψhgne : ψ hg ≠ 1 := by
    intro h1
    exact hgne (hinjψ (by rw [h1, map_one]))
  have hconj' : MulAut.conj (ψ hg) ∈ A' := by
    change MulAut.conj (θ (QuotientGroup.mk' (Subgroup.center X) hg)) ∈ A'
    rw [← l02qj8_kgInducedAut_conj θ hg]
    exact Subgroup.mem_map_of_mem ρ hconjJ₀
  let J' : Subgroup (GGTriD4R n K) := J₀.map ψ
  let eJ : ↥J₀ ≃* ↥J' := Subgroup.equivMapOfInjective J₀ ψ hinjψ
  have hJ' : IsComponentOf J' (Subgroup.centralizer ({ψ hg} : Set (GGTriD4R n K))) := by
    have h1 := isComponentOf_map_of_injective ψ hinjψ hJ₀
    rw [l02qj8_map_centralizer_singleton ψ hψ hinjψ hg] at h1
    exact h1
  let hcJ : Subgroup.map (eJ : ↥J₀ →* ↥J') (Subgroup.center ↥J₀) =
      Subgroup.center ↥J' := Subgroup.map_center_eq eJ
  let θ₀' : ↥J' ⧸ Subgroup.center ↥J' ≃* LargeEvenProj (LargeEvenSLGroup (Fin 3) E) :=
    (QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥J') eJ hcJ).symm.trans θ₀
  have hAt' : ∃ At : Subgroup (GL (Fin 3) E), IsMulCommutative At ∧
      ∀ α' ∈ A', ∃ g ∈ At, ∀ j : ↥J', ∃ j' : ↥J',
        (j' : GGTriD4R n K) = α' j ∧
        θ₀' (QuotientGroup.mk j') =
          TableB.linConjAut (Fin 3) E g (θ₀' (QuotientGroup.mk j)) := by
    obtain ⟨At, hAtcomm, hAt⟩ := hAt
    refine ⟨At, hAtcomm, ?_⟩
    intro α' hα'
    obtain ⟨α, hαA, rfl⟩ := Subgroup.mem_map.mp hα'
    obtain ⟨g, hgAt, hgAt'⟩ := hAt α hαA
    refine ⟨g, hgAt, ?_⟩
    intro j
    obtain ⟨x', hx', hθx⟩ := hgAt' (eJ.symm j)
    refine ⟨eJ x', ?_, ?_⟩
    · have hcoe : ((eJ x' : ↥J') : GGTriD4R n K) =
          θ (QuotientGroup.mk' (Subgroup.center X) (x' : X)) := by
        rw [Subgroup.coe_equivMapOfInjective_apply]
        rfl
      have hjcoe : (j : GGTriD4R n K) =
          θ (QuotientGroup.mk' (Subgroup.center X) ((eJ.symm j : ↥J₀) : X)) := by
        conv_lhs => rw [← MulEquiv.apply_symm_apply eJ j]
        rw [Subgroup.coe_equivMapOfInjective_apply]
        rfl
      rw [hcoe, hjcoe, l02qj8_kgInducedAut_apply θ α ((eJ.symm j : ↥J₀) : X), ← hx']
    · have h1 : θ₀' (QuotientGroup.mk (eJ x')) = θ₀ (QuotientGroup.mk x') := by
        change ((QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥J') eJ hcJ).symm.trans
            θ₀) (QuotientGroup.mk' (Subgroup.center ↥J') (eJ x')) =
          θ₀ (QuotientGroup.mk' (Subgroup.center ↥J₀) x')
        rw [l02qj8_thetaTransport_apply (Subgroup.center ↥J₀) (Subgroup.center ↥J') eJ hcJ θ₀
          (eJ x')]
        rw [MulEquiv.symm_apply_apply]
      have h2 : θ₀' (QuotientGroup.mk j) = θ₀ (QuotientGroup.mk (eJ.symm j)) := by
        change ((QuotientGroup.congr (Subgroup.center ↥J₀) (Subgroup.center ↥J') eJ hcJ).symm.trans
            θ₀) (QuotientGroup.mk' (Subgroup.center ↥J') j) =
          θ₀ (QuotientGroup.mk' (Subgroup.center ↥J₀) (eJ.symm j))
        rw [l02qj8_thetaTransport_apply (Subgroup.center ↥J₀) (Subgroup.center ↥J') eJ hcJ θ₀ j]
      rw [h1, h2]
      exact hθx
  obtain ⟨k', hfix', hlang'⟩ :=
    h A' hA' (ρ α₀) hα₀'A hα₀'Inn (ψ hg) hψhgne hconj' J' hJ' E θ₀' hAt'
  obtain ⟨k, rfl⟩ := hψ k'
  refine ⟨k, ?_, ?_⟩
  · intro α hαA hραI
    have hραInn : ρ α ∈ kgLangT3Inn n K := by
      have h' := hραI
      rw [hinn'] at h'
      exact h'
    have h1 : ρ α (ψ k) = ψ k :=
      hfix' (ρ α) (Subgroup.mem_map_of_mem ρ hαA) hραInn
    apply hinjψ
    change θ (QuotientGroup.mk' (Subgroup.center X) (α k)) =
      θ (QuotientGroup.mk' (Subgroup.center X) k)
    rw [← l02qj8_kgInducedAut_apply θ α k]
    exact h1
  · apply hinjψ
    change θ (QuotientGroup.mk' (Subgroup.center X) (k * (α₀ k)⁻¹)) =
      θ (QuotientGroup.mk' (Subgroup.center X) hg)
    simp only [map_mul, map_inv]
    rw [← l02qj8_kgInducedAut_apply θ α₀ k]
    exact hlang'

theorem kgLangAxisT3Input_of_strong
    (h : ∀ (n : ℕ) (K : Type) [Field K] [Finite K], 2 ≤ n → Even n →
      Nat.card K = (2 ^ n) ^ 3 → KGLangT3Strong n K) :
    KGLangAxisT3Input := by
  intro lab hlab ht h3
  obtain ⟨t, l, n⟩ := lab
  dsimp only at ht
  subst ht
  obtain ⟨hn, -⟩ := hlab
  dsimp only at hn h3
  intro Q hQ
  dsimp only [LargeEvenRawDatum] at hQ ⊢
  obtain ⟨K, _, _, hK, hQK⟩ := hQ
  refine ⟨K, inferInstance, inferInstance, hK, hQK, ?_⟩
  have hn2 : 2 ≤ n := by
    have hn' : 1 ≤ n := hn
    obtain ⟨m, hm⟩ := l02qj8_even_of_three_dvd_two_pow_sub_one h3
    omega
  exact kgLangT3_cont_of_strong hn K hK
    (h n K hn2 (l02qj8_even_of_three_dvd_two_pow_sub_one h3) hK) _

end CFSG.StandardType
