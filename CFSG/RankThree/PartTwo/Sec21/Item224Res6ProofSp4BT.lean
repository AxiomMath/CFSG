module

public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofSp4Tools
public import CFSG.RankThree.PartTwo.Sec21.Item224KFactsProofLie
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp48Inner
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofRat
public import CFSG.RankThree.PartTwo.Sec21.Item224Res6ProofSp4Out

public section

namespace CFSG.RankThree.PartTwo.Sec21

open Matrix CFSG.LieType.BorelTits Module
open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec21.Item224Res5Proof CFSG.RankThree.PartTwo.Sec21.Item224KFactsProof
open CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII (ordN ordN_conj ordN_map conj_eq_zero_iff
  ordN_tauSp_eq_zero_iff)
open CFSG.QuasithinUnique.Lin2.Five (tauSp tauAut tauAut_proj)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldEquiv)
open CFSG.Assembly.RankThreeEven (projSp)

namespace Item224Res6Proof

variable {F : Type} [Field F] [Finite F] [CharP F 2]

theorem tau_coset_not_fixed (A : gsp 2 F) (σ : F ≃+* F) {e : StatedSp 2 F} (he3 : e ^ 3 = 1)
    (he1 : e ≠ 1) :
    (conjAut 2 F A * fieldAut 2 F σ * tauAut : MulAut (StatedProj (StatedSp 2 F))) (proj 2 F e) ≠
      proj 2 F e := by
  intro hφe
  rw [MulAut.mul_apply, MulAut.mul_apply, tauAut_proj, fieldAut_proj, conjAut_proj] at hφe
  have he' := proj_injective_of_charTwo hφe
  have hm := congrArg (fun x : StatedSp 2 F =>
    ordN ((x : GL (Fin 2 ⊕ Fin 2) F) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F)) he'
  rw [coe_conjSp, Units.val_mul, Units.val_mul, ordN_conj, coe_fieldSp, ordN_map] at hm
  have hsw := ordN_tauSp_eq_zero_iff he3 he1
  by_cases hN : ordN (((e : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
      Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 0
  · rw [hN, conj_eq_zero_iff] at hm
    have h0 : ordN (((tauSp e : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) = 0 := by
      have h2 := congrArg (fun X => X.map σ.symm) hm
      simp only [Matrix.map_map, Matrix.map_zero, map_zero] at h2
      convert h2 using 1
      ext i j
      simp
    exact (hsw.mp h0) hN
  · rw [(hsw.mpr hN), Matrix.map_zero _ (map_zero σ), Matrix.mul_zero, Matrix.zero_mul] at hm
    exact hN hm.symm

theorem oddFixedBorelTits_sp4 {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 ≤ m) (hme : Even m)
    {E : Subgroup (MulAut (StatedProj (StatedSp 2 F)))} (hE : CFSG.Assembly.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9)
    (hEinn : E ≤ (MulAut.conj : StatedProj (StatedSp 2 F) →*
      MulAut (StatedProj (StatedSp 2 F))).range)
    {T : Subgroup (MulAut (StatedProj (StatedSp 2 F)))} (hT : IsPGroup 2 T)
    (hTE : T ≤ Subgroup.centralizer (E : Set (MulAut (StatedProj (StatedSp 2 F))))) :
    OddFixedBorelTits (StatedProj (StatedSp 2 F)) T := by
  classical
  intro U hU hUN
  have hcinj := conj_injective_sp4 (F := F)
  obtain ⟨ζ, hζ⟩ : ∃ ζ : F, IsPrimitiveRoot ζ 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have h3 : 3 ∣ Nat.card Fˣ := by
      rw [Nat.card_units, hF]
      obtain ⟨k, rfl⟩ := hme
      have hmod : 2 ^ (k + k) % 3 = 1 := by
        rw [← two_mul, pow_mul, Nat.pow_mod]
        norm_num
      exact Nat.dvd_of_mod_eq_zero (Nat.sub_mod_eq_zero_of_mod_eq (by rw [hmod]))
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) 3 h3
    exact ⟨u, by rw [IsPrimitiveRoot.iff_orderOf, orderOf_units, hu]⟩
  set Ē₀ := E.comap (MulAut.conj : StatedProj (StatedSp 2 F) →*
    MulAut (StatedProj (StatedSp 2 F))) with hĒ₀
  have hĒ₀map : Ē₀.map MulAut.conj = E := Subgroup.map_comap_eq_self hEinn
  have hĒ₀9 : Nat.card Ē₀ = 9 := by
    rw [← hE9, ← hĒ₀map, Subgroup.card_map_of_injective hcinj]
  set E₀ := Ē₀.comap (proj 2 F) with hE₀
  have hE₀9 : Nat.card E₀ = 9 := by
    have hmap : E₀.map (proj 2 F) = Ē₀ :=
      Subgroup.map_comap_eq_self_of_surjective proj_surjective _
    rw [← hĒ₀9, ← hmap, Subgroup.card_map_of_injective proj_injective_of_charTwo]
  have hE₀E : ∀ e ∈ E₀, MulAut.conj (proj 2 F e) ∈ E := fun e he => he
  have hE₀3 : ∀ e ∈ E₀, e ^ 3 = 1 := by
    intro e he
    apply proj_injective_of_charTwo
    apply hcinj
    rw [map_pow, map_pow, map_one, map_one]
    exact hE.2 _ (hE₀E e he)
  have hE₀c : ∀ x ∈ E₀, ∀ y ∈ E₀, x * y = y * x := by
    intro x hx y hy
    apply proj_injective_of_charTwo
    apply hcinj
    rw [map_mul, map_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, hE₀E x hx⟩ ⟨_, hE₀E y hy⟩)
  have hTI : T ⊓ (MulAut.conj : StatedProj (StatedSp 2 F) →*
      MulAut (StatedProj (StatedSp 2 F))).range = ⊥ := by
    rw [eq_bot_iff]
    rintro t ⟨htT, x, rfl⟩
    rw [Subgroup.mem_bot]
    obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) x
    have hgc : ∀ e ∈ E₀, g * e = e * g := by
      intro e he
      have h1 := Subgroup.mem_centralizer_iff.mp (hTE htT) _ (hE₀E e he)
      apply proj_injective_of_charTwo
      apply hcinj
      rw [map_mul, map_mul, map_mul, map_mul]
      exact h1.symm
    obtain ⟨k, hk⟩ := hT ⟨MulAut.conj (proj 2 F g), htT⟩
    have hgk : g ^ 2 ^ k = 1 := by
      apply proj_injective_of_charTwo
      apply hcinj
      rw [map_pow, map_pow, map_one, map_one]
      exact congrArg Subtype.val hk
    rw [eq_one_of_commute_E9_sp4 hζ E₀ hE₀9 hE₀3 hE₀c hgc hgk, map_one, map_one]
  have : Fintype F := Fintype.ofFinite F
  have hcardF : Fintype.card F = 2 ^ m := by rw [Fintype.card_eq_nat_card, hF]
  obtain ⟨hcyc, -⟩ := CFSG.QuasithinUnique.Lin2.sp4OutCyclic F m hcardF hm
  have hTcyc : IsCyclic T := outTwoCyclic_of_isCyclic_outer hcyc T hT hTI
  obtain ⟨⟨t₀, ht₀⟩, hgen⟩ := hTcyc.exists_generator
  have hpowT : ∀ t ∈ T, ∃ i : ℤ, t = t₀ ^ i := by
    intro t ht
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp (hgen ⟨t, ht⟩)
    have := congrArg Subtype.val hi
    simp only [SubgroupClass.coe_zpow] at this
    exact ⟨i, this.symm⟩
  have hTfix : ∀ y : StatedProj (StatedSp 2 F), t₀ y = y → ∀ t ∈ T, t y = y := by
    intro y hy t ht
    obtain ⟨i, rfl⟩ := hpowT t ht
    have hstab : t₀ ∈ MulAction.stabilizer (MulAut (StatedProj (StatedSp 2 F))) y := hy
    exact zpow_mem hstab i
  have ht₀E : ∀ e ∈ E₀, t₀ (proj 2 F e) = proj 2 F e := by
    intro e he
    have h1 := Subgroup.mem_centralizer_iff.mp (hTE ht₀) _ (hE₀E e he)
    apply hcinj
    rw [← mul_conj_mul_inv t₀ (proj 2 F e), ← h1, mul_inv_cancel_right]
  obtain ⟨x, hxE₀, hx1⟩ : ∃ x ∈ E₀, x ≠ 1 := by
    by_contra hall
    push Not at hall
    have hbot : E₀ = ⊥ := eq_bot_iff.mpr fun y hy => Subgroup.mem_bot.mpr (hall y hy)
    rw [hbot, Subgroup.card_bot] at hE₀9
    norm_num at hE₀9
  obtain ⟨A, φ, ε, hε, ht₀eq⟩ := exists_eq_conjAut_mul_fieldAut_mul_tauAut_pow t₀
  have hε0 : ε = 0 := by
    rcases (by omega : ε = 0 ∨ ε = 1) with h0 | h1
    · exact h0
    · exfalso
      subst h1
      apply tau_coset_not_fixed A φ (hE₀3 x hxE₀) hx1
      rw [← pow_one (tauAut : MulAut (StatedProj (StatedSp 2 F))), ← ht₀eq]
      exact ht₀E x hxE₀
  obtain ⟨x₁, hx₁⟩ := conjAut_mem_inner_of_charTwo A
  obtain ⟨g, rfl⟩ := proj_surjective (r := 2) (K := F) x₁
  have ht₀' : t₀ = MulAut.conj (proj 2 F g) * fieldAut 2 F φ := by
    rw [ht₀eq, hε0, pow_zero, mul_one, ← hx₁]
  set ψ := semPsi ((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) φ with hψ
  have hψs : ∀ (c : F) (v : Fin 2 ⊕ Fin 2 → F), ψ (c • v) = φ c • ψ v := semPsi_smul _ φ
  have hψβ : ∀ u v, (spForm 2 F).β (ψ u) (ψ v) = φ ((spForm 2 F).β u v) := semPsi_β g φ
  have hgm : spIter g φ (orderOf φ) = 1 := by
    have h1 := conj_field_pow_sp4 g φ (orderOf φ)
    rw [pow_orderOf_eq_one, map_one, mul_one, ← ht₀'] at h1
    have h2 : t₀ ^ orderOf φ ∈ T ⊓ (MulAut.conj : StatedProj (StatedSp 2 F) →*
        MulAut (StatedProj (StatedSp 2 F))).range :=
      ⟨pow_mem ht₀ _, by rw [h1]; exact ⟨_, rfl⟩⟩
    rw [hTI, Subgroup.mem_bot, h1] at h2
    apply proj_injective_of_charTwo
    apply hcinj
    rw [h2, map_one, map_one]
  have hψm : ∀ v, (⇑ψ)^[orderOf φ] v = v := by
    intro v
    rw [hψ, semPsi_iterate, hgm, pow_orderOf_eq_one]
    simp
  have hσφ : ∀ c : F, φ c = c → (spForm 2 F).σ c = c := fun c _ => rfl
  have hWnd : ∀ c ∈ (⊤ : Submodule F (Fin 2 ⊕ Fin 2 → F)),
      (∀ w ∈ (⊤ : Submodule F (Fin 2 ⊕ Fin 2 → F)), (spForm 2 F).β w c = 0) → c = 0 := by
    intro c _ hc
    apply (spForm 2 F).nondeg c
    intro v
    exact (spForm 2 F).refl _ _ (hc v Submodule.mem_top)
  have hdim : 3 ≤ finrank F (⊤ : Submodule F (Fin 2 ⊕ Fin 2 → F)) := by
    rw [finrank_top, Module.finrank_fintype_fun_eq_card]
    decide
  obtain ⟨hadd, hscale, hnd, hhyp, hpair, hspan⟩ := rational_form_props hm hF (spForm 2 F)
    spForm_symm hσφ ψ hψs hψβ hψm ⊤ (fun _ _ => Submodule.mem_top)
    (fun _ _ => Submodule.mem_top) hdim hWnd (fun v _ _ => spForm_self 2 F v)
  set Q := U.comap (proj 2 F) with hQ
  have hQ2 : IsPGroup 2 Q := hU.comap_of_injective _ proj_injective_of_charTwo
  have hQmap : Q.map (proj 2 F) = U := Subgroup.map_comap_eq_self_of_surjective proj_surjective U
  have hNQ : Subgroup.normalizer (Q : Set (StatedSp 2 F)) =
      (Subgroup.normalizer (U : Set (StatedProj (StatedSp 2 F)))).comap (proj 2 F) :=
    (Subgroup.comap_normalizer_eq_of_surjective U proj_surjective).symm
  have hQbot : Q = ⊥ := by
    refine eq_bot_of_tv (spForm 2 F) spForm_symm (natRep (StatedSp 2 F))
      (isIsometric_natRep_statedSp 2 F) (natRep_injective _) Q hQ2
      {v | v ∈ (⊤ : Submodule F (Fin 2 ⊕ Fin 2 → F)) ∧ ψ v = v}
      (fun a _ => spForm_self 2 F a) hadd hscale hnd hhyp hpair ?_ ?_
    · intro a ha e he hae
      obtain ⟨ga, hga⟩ := exists_tvSp a
      obtain ⟨ge, hge⟩ := exists_tvSp e
      have hρ : natRep (StatedSp 2 F) (ga * ge) = tv (spForm 2 F) a * tv (spForm 2 F) e := by
        rw [map_mul, hga, hge]
      refine ⟨ga * ge, ?_, hρ⟩
      rw [hNQ, Subgroup.mem_comap]
      apply hUN
      apply Subgroup.subset_closure
      refine ⟨hTfix _ ?_, ?_⟩
      ·
        rw [ht₀', conj_field_apply_proj]
        congr 1
        apply natRep_injective (StatedSp 2 F)
        refine LinearMap.ext fun v => ?_
        have h1 : ∀ w, ((((ga * ge : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)) :
            Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ w =
              tv (spForm 2 F) a (tv (spForm 2 F) e w) := by
          intro w
          have := congrArg (fun f : Module.End F (Fin 2 ⊕ Fin 2 → F) => f w) hρ
          simpa [natRep_apply] using this
        rw [natRep_apply, natRep_apply]
        change ((((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
          glFieldEquiv (Fin 2 ⊕ Fin 2) φ ((ga * ge : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F) *
            ((g : StatedSp 2 F) : GL (Fin 2 ⊕ Fin 2) F)⁻¹ : GL (Fin 2 ⊕ Fin 2) F) :
          Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) F) *ᵥ v = _
        rw [natRep_conj_semPsi, h1, h1]
        have hψa : ψ a = a := ha.2
        have hψe : ψ e = e := he.2
        calc ψ (tv (spForm 2 F) a (tv (spForm 2 F) e (ψ.symm v))) =
            ψ (tv (spForm 2 F) a (ψ.symm (ψ (tv (spForm 2 F) e (ψ.symm v))))) := by
              rw [AddEquiv.symm_apply_apply]
          _ = tv (spForm 2 F) (ψ a) (ψ (tv (spForm 2 F) e (ψ.symm v))) :=
              semPsi_tv (spForm 2 F) _ φ hψβ a _
          _ = tv (spForm 2 F) (ψ a) (tv (spForm 2 F) (ψ e) v) := by
              rw [semPsi_tv (spForm 2 F) _ φ hψβ e v]
          _ = tv (spForm 2 F) a (tv (spForm 2 F) e v) := by rw [hψa, hψe]
      ·
        have hg3 : (ga * ge) ^ 3 = 1 := by
          apply natRep_injective (StatedSp 2 F)
          rw [map_pow, hρ, map_one]
          exact tv_mul_tv_pow_three (spForm 2 F) spForm_symm (spForm_self 2 F a)
            (spForm_self 2 F e) hae
        have hpi3 : (proj 2 F (ga * ge)) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
        have hd : orderOf (proj 2 F (ga * ge)) ∣ 3 := orderOf_dvd_of_pow_eq_one hpi3
        rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1 <;> rw [h1] <;> decide
    · intro w hw0 hw
      exfalso
      apply hw0
      apply (spForm 2 F).nondeg w
      intro v
      apply (spForm 2 F).refl
      exact hspan w hw v Submodule.mem_top
  rw [← hQmap, hQbot, Subgroup.map_bot]

theorem autTorusBorelTits_sp4 {m : ℕ} (hF : Nat.card F = 2 ^ m) (hm : 1 ≤ m) (hme : Even m) :
    AutTorusBorelTits (StatedProj (StatedSp 2 F)) := by
  intro E hE hE9 hI hx T hT _ hTE
  exact oddFixedBorelTits_sp4 hF hm hme hE hE9 (le_inner_of_innerThreeFixed_sp4 hE hE9 hI hx) hT
    hTE

end Item224Res6Proof

open Item224Res6Proof

theorem ks224Sp4BorelTits : KS224Sp4BorelTits := by
  intro X _ _ n hn he hX
  obtain ⟨e⟩ := hX
  exact autTorusBorelTits_of_mulEquiv
    (e.trans (CFSG.RankThree.PartTwo.Census.statedProjEquivProjImage
      (StatedSp 2 (GaloisField 2 n))).symm)
    (autTorusBorelTits_sp4 (GaloisField.card 2 n hn.ne') hn he)

end CFSG.RankThree.PartTwo.Sec21
