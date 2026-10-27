module

public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5LinWeyl
public import CFSG.LocalAnalysis.StandardType.GGSlNsRootGenModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit
public import CFSG.Adapters.SpecialLinearPerfect

@[expose] public section

namespace CFSG.StandardType.RelA5

open CFSG CFSG.Assembly CFSG.Open CFSG.StandardType.CoordSL CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix Polynomial Multiplicative

theorem ggTorusTorW_relA5_linear {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K + 1) :
    GGTorusTorW p 3 (Nat.card K + 1) 3 (CartanMatrix.C 3) (CoxeterMatrix.B 3)
      (LargeEvenProj (LargeEvenSLGroup (Fin 6) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin 6) K)) Set.univ) := by
  classical
  intro L' _ _ ψ A hTB
  obtain ⟨hψ, hker, hperf, hAe, hAI, hr, h3, hsc⟩ := hTB
  have : Fact p.Prime := ⟨hp⟩
  have : Fintype K := Fintype.ofFinite K
  have hpK' : ¬ p ∣ Nat.card K - 1 := by
    intro hK1
    have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by
      have := Nat.card_pos (α := K)
      omega
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hsub ▸ Nat.dvd_sub hpK hK1))
  have hpK0 : (p : K) ≠ 0 := OrdPNS.natCast_ne_zero_of_charTwo hp hp2
  set e := TypeA.recipeEquiv 6 K
  have hψ' : Function.Surjective (e.toMonoidHom.comp ψ) := e.surjective.comp hψ
  have hker' : (e.toMonoidHom.comp ψ).ker ≤ Subgroup.center L' :=
    (TypeA.ker_comp_mulEquiv e ψ).symm ▸ hker
  have hAI' : ∀ a ∈ A, ∃ φa ∈ Set.range (conjAut 6 K),
      ∀ l, φa ((e.toMonoidHom.comp ψ) l) = (e.toMonoidHom.comp ψ) (a l) := by
    intro a ha
    obtain ⟨φ, hφ, hφa⟩ := hAI a ha
    refine ⟨MulAut.congr e φ, TypeA.congr_recipeEquiv_mem hφ, fun l' => ?_⟩
    change e (φ (e.symm (e (ψ l')))) = e (ψ (a l'))
    rw [MulEquiv.symm_apply_apply, hφa]
  have hne : ¬ IsUnit (cyclotomic p K) := by
    rw [Polynomial.isUnit_iff_degree_eq_zero, degree_eq_natDegree (cyclotomic_ne_zero p _),
      natDegree_cyclotomic, Nat.totient_prime hp]
    have := hp.two_le
    norm_cast
    omega
  obtain ⟨g, hg, hgd⟩ := WfDvdMonoid.exists_irreducible_factor hne (cyclotomic_ne_zero p _)
  have : Fact (Irreducible g) := ⟨hg⟩
  have hC : (rootMat g).det = 1 := det_rootMat hp hpK' hpK0 hgd
  have hCp : rootMat g ^ p = 1 := rootMat_pow_eq_one hp hpK0 hgd
  have hprim : IsPrimitiveRoot (AdjoinRoot.root g) p := root_isPrimitiveRoot hp hpK0 hgd
  have hdim2 : 2 ≤ (rootPB g).dim := LinTwoTv.two_le_rootPB_dim fun c =>
    isUnit_rootMat_pow_sub hp hpK' hpK0 hgd 1 hp.not_dvd_one c
  obtain ⟨s, r, ε, φ, hφs, hφc, hs3, hM⟩ :=
    SlNsRootGen.exists_isBlockTorusModel hp hp2 hpK hgd hC hψ' hker' hperf hAe hAI' h3 hsc
  have hcard : (rootPB g).dim * s + r = 6 := by
    have h1 := Fintype.card_congr ε
    simp only [Fintype.card_fin, Fintype.card_sum, Fintype.card_prod] at h1
    omega
  have hs : s = 3 := by nlinarith
  have hr0 : r = 0 := by nlinarith
  have hdim : (rootPB g).dim = 2 := by subst hs; omega
  subst hs hr0
  have hφker : φ.ker ≤ Subgroup.center (SpecialLinearGroup (Fin 6) K) := fun x hx =>
    hφc x (by rw [MonoidHom.mem_ker.mp hx]; exact Subgroup.one_mem _)
  have hHperf : commutator (SpecialLinearGroup (Fin 6) K) = ⊤ :=
    CFSG.ClassicalModels.specialLinear_commutator_eq_top_of_three_le (by norm_num)
  have hZcard : Nat.card (Subgroup.center (SpecialLinearGroup (Fin 6) K)) ∣ Nat.card K - 1 :=
    card_center_specialLinear_dvd (by norm_num)
  have hZp : ¬ p ∣ Nat.card (Subgroup.center (SpecialLinearGroup (Fin 6) K)) :=
    fun hd => hpK' (hd.trans hZcard)
  have hZm : Nat.Coprime (Nat.card K + 1)
      (Nat.card (Subgroup.center (SpecialLinearGroup (Fin 6) K))) :=
    Nat.Coprime.coprime_dvd_right hZcard coprime_card_add_one_card_sub_one
  let l : muPlus g ≃* Multiplicative (ZMod (Nat.card K + 1)) :=
    mulEquivOfCyclicCardEq (by
      rw [card_muPlus hdim]
      exact (Nat.card_zmod _).symm)
  have hμ : ∀ x : muPlus g, x ^ (Nat.card K + 1) = 1 := fun x =>
    Subtype.ext ((mem_rootsOfUnity _ _).mp x.2)
  obtain ⟨F, hF⟩ := exists_linTorus (K := K) ε
  obtain ⟨TH, hTH⟩ := exists_linFullTorus (K := K) ε
  obtain ⟨ζ, hζr, hζ⟩ := exists_rootMu hprim hpK
  obtain ⟨w, hw⟩ := exists_linWeyl hprim.pow_eq_one hpK hF
  have hA : A = (((embPow ζ hζ.pow_eq_one).range.map F).map φ).map
      (MulAut.conj : L' →* MulAut L') := by
    ext a
    rw [hM.mem_iff hCp]
    constructor
    · rintro ⟨t, rfl⟩
      refine ⟨φ (F (embPow ζ hζ.pow_eq_one fun i => ofAdd (t i))),
        ⟨F (embPow ζ hζ.pow_eq_one fun i => ofAdd (t i)),
          ⟨embPow ζ hζ.pow_eq_one fun i => ofAdd (t i), ⟨_, rfl⟩, rfl⟩, rfl⟩, ?_⟩
      rw [linTorus_embPow hC hCp hF hζ.pow_eq_one hζr]
      rfl
    · rintro ⟨_, ⟨_, ⟨_, ⟨f, rfl⟩, rfl⟩, rfl⟩, rfl⟩
      exact ⟨fun i => toAdd (f i), by rw [linTorus_embPow hC hCp hF hζ.pow_eq_one hζr]⟩
  exact ggTorusTorData_of_relA5Model hp2 odd_card_add_one φ hφs hφker hHperf hZp hZm l hμ F
    (linTorus_eq_one_of_mem_center hF) TH (fun x hx y hy => linFullTorus_commute hTH hx hy)
    (linTorus_mem_linFullTorus hF hTH) (fun t ht htm => exists_eq_linTorus_of_pow hF hTH ht htm)
    (center_le_linFullTorus hTH) (mem_linFullTorus_of_commute hprim hpK hF hTH) w hw ζ hζ
    (fun z hz => (mem_range_embPow_iff_muPlus hζ z).mpr hz)
    (fun x hx => linTorus_signedPerm hpK hgd hC hCp hF hζ hζr x hx) hA

end CFSG.StandardType.RelA5
