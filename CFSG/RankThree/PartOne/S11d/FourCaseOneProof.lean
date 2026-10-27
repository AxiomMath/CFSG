module

public import CFSG.RankThree.PartOne.S11d.FourMain
public import CFSG.RankThree.PartOne.S11d.FourSeedTheta
public import CFSG.RankThree.PartOne.S11d.FiveClaimAux
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartOne.S10.SelectedPrimeNormalizeThetaComponents

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.Assembly CFSG.Blueprint CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

namespace Sec11Indeed

namespace Sit

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G}
  {a d : G}

theorem sq_le_card_sup (sit : Sit p A c L a d) {f : G} {i j : ℤ} (hij : f = a ^ i * c ^ j)
    (hi : ¬ (p : ℤ) ∣ i) : p ^ 2 ≤ Nat.card (zpowers c ⊔ zpowers f : Subgroup G) := by
  have hp := sit.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcA := sit.c_mem
  have hfA : f ∈ A := by
    rw [hij]
    exact A.mul_mem (A.zpow_mem sit.a_mem i) (A.zpow_mem hcA j)
  have hf1 : f ≠ 1 := fun h => hi (sit.coords_eq_one (x := i) (y := j) (z := 0)
    (by rw [zpow_zero, mul_one, ← hij]; exact h)).1
  have hcf : c ∉ zpowers f := by
    intro h
    apply sit.c_not_mem_sup j hi
    rw [← hij]
    exact Subgroup.mem_sup_left h
  have hlt : zpowers f < zpowers c ⊔ zpowers f := by
    refine lt_of_le_of_ne le_sup_right fun h => hcf ?_
    rw [h]
    exact Subgroup.mem_sup_left (mem_zpowers c)
  have hcardlt := Subgroup.card_lt_of_lt hlt
  rw [Nat.card_zpowers, orderOf_eq_prime (sit.pow_eq_one hfA) hf1] at hcardlt
  have hdvd : Nat.card (zpowers c ⊔ zpowers f : Subgroup G) ∣ p ^ 3 := by
    rw [← sit.setup.2.2.2.2.2.2.2.1]
    exact Subgroup.card_dvd_of_le (sup_le (zpowers_le.mpr hcA) (zpowers_le.mpr hfA))
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).mp hdvd
  rw [hm] at hcardlt ⊢
  have hm2 : 2 ≤ m := by
    by_contra h
    push Not at h
    have h2 := hp.two_le
    interval_cases m
    · simp at hcardlt
      omega
    · simp at hcardlt
  exact Nat.pow_le_pow_right hp.pos hm2

theorem inf_centralizer_coords_eq (sit : Sit p A c L a d) {f b : G} {i j i' j' : ℤ}
    (hij : f = a ^ i * c ^ j) (hi : ¬ (p : ℤ) ∣ i) (hbij : b = a ^ i' * c ^ j')
    (hi' : ¬ (p : ℤ) ∣ i') :
    L ⊓ centralizer ({b} : Set G) = L ⊓ centralizer ({f} : Set G) := by
  have hp := sit.prime
  have hap : a ^ p = 1 := sit.pow_eq_one sit.a_mem
  have key : ∀ (m n : ℤ), ¬ (p : ℤ) ∣ m → ∀ g ∈ L,
      (g ∈ centralizer ({a ^ m * c ^ n} : Set G) ↔ g ∈ centralizer ({a} : Set G)) := by
    intro m n hm g hg
    have hgc : Commute g (c ^ n) :=
      Subgroup.mem_centralizer_iff.mp (sit.zpow_c_mem_centralizer n) g hg
    rw [← S11d.centralizer_zpow_eq (G := G) hp hap hm]
    simp only [Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      have h1 : Commute g (a ^ m * c ^ n) := h
      have h2 : Commute g (a ^ m) := by
        have h3 := h1.mul_right hgc.inv_right
        rwa [mul_assoc, mul_inv_cancel, mul_one] at h3
      exact h2.eq
    · intro h
      exact ((show Commute g (a ^ m) from h).mul_right hgc).eq
  subst hij hbij
  ext g
  simp only [Subgroup.mem_inf]
  constructor
  · rintro ⟨hgL, hgb⟩
    exact ⟨hgL, (key i j hi g hgL).mpr ((key i' j' hi' g hgL).mp hgb)⟩
  · rintro ⟨hgL, hgf⟩
    exact ⟨hgL, (key i' j' hi' g hgL).mpr ((key i j hi g hgL).mp hgf)⟩

end Sit

variable {G : Type} [Group G] [Finite G]

namespace Sit

variable {p : ℕ} {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G}

theorem fixedRes_le_closure (sit : Sit p A c L a d) (hCent : FieldFixedCentralizer)
    (hFix : FieldFixedPElements) {f : G} (hfA : f ∈ A) (hfa : InducesFieldAut p f L) :
    ∀ e ∈ inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)),
      e ∈ Subgroup.closure {y : G |
        y ∈ inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ∧
          ∃ k : ℕ, orderOf y = p ^ k} := by
  have : Fact p.Prime := ⟨sit.prime⟩
  have hdp : ∃ k : ℕ, orderOf d = p ^ k :=
    ⟨1, by rw [pow_one]; exact orderOf_eq_prime (sit.pow_eq_one sit.d_mem) sit.d_ne_one⟩
  have hdE : d ∈ inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) :=
    hFix G p L f (sit.fieldAutSetting hfa) (sit.pow_eq_one hfA) (sit.fieldAutRank hfA) d
      ⟨sit.d_mem_L, Subgroup.mem_centralizer_singleton_iff.mpr (sit.A_comm sit.d_mem hfA)⟩ hdp
  refine FourSeed.le_closure_pElements_of_quasisimple (fixedRes_isQuasisimple hfa) hdE hdp ?_
  by_contra hno
  push Not at hno
  have hDc : (⟨d, sit.d_mem_L⟩ : ↥L) ∈ Subgroup.center ↥L :=
    hCent G p L f (sit.fieldAutSetting hfa) (sit.pow_eq_one hfA) (sit.fieldAutRank hfA)
      ⟨d, sit.d_mem_L⟩ hno
  have h1 := orderOf_dvd_natCard (⟨⟨d, sit.d_mem_L⟩, hDc⟩ : Subgroup.center ↥L)
  have hordd : orderOf d = p := orderOf_eq_prime (sit.pow_eq_one sit.d_mem) sit.d_ne_one
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, hordd] at h1
  exact sit.p_ndvd h1

end Sit

theorem four_seed_false (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hLS : FieldAutCoset) (hFix : FieldFixedPElements)
    (hCent : FieldFixedCentralizer) (hNL : FieldFixedNonLocal) {p : ℕ} {A : Subgroup G} {c : G}
    {L : Subgroup G} {a d : G} (sit : Sit p A c L a d) {f : G} {i j : ℤ}
    (hij : f = a ^ i * c ^ j) (hi : ¬ (p : ℤ) ∣ i) {R : Subgroup G} (hR2 : IsPGroup 2 R)
    (hR1 : R ≠ ⊥) (hAR : A ≤ normalizer (R : Set G))
    (hER : inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ≤
      normalizer (R : Set G)) : False := by
  classical
  have hp := sit.prime
  have hp3 := sit.three_lt
  have hp5 := sit.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hcA := sit.c_mem
  have hcp : c ^ p = 1 := sit.pow_eq_one hcA
  have hcord : orderOf c = p := orderOf_eq_prime hcp sit.c_ne_one
  have he : evenRank G ≤ 3 := (sectionTenSetup_evenRank_eq sit.setup).le
  have hzp : ∀ (e : G) (n : ℤ), e ^ p = 1 → (p : ℤ) ∣ n → e ^ n = 1 := by
    intro e n he' hn
    obtain ⟨u, rfl⟩ := hn
    rw [zpow_mul, zpow_natCast, he', one_zpow]
  have hfA : f ∈ A := by
    rw [hij]
    exact A.mul_mem (A.zpow_mem sit.a_mem i) (A.zpow_mem hcA j)
  have hf1 : f ≠ 1 := fun h => hi (sit.coords_eq_one (x := i) (y := j) (z := 0)
    (by rw [zpow_zero, mul_one, ← hij]; exact h)).1
  have hfa : InducesFieldAut p f L := hij ▸ sit.inducesFieldAut_mul j hi
  have hEq := fixedRes_isQuasisimple hfa
  set E := inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) with hE
  have hEp : Group.IsPerfect ↥E := EmbeddingFixedResidual.isPerfect_inSubgroup_perfectResidual _
  have hEcomm : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.mp hEp
  have hEne : E ≠ ⊥ := Sec125.ne_bot_of_isQuasisimple hEq
  have hEL : E ≤ L := (inSubgroup_perfectResidual_le _).trans inf_le_left
  have hEf : E ≤ centralizer ({f} : Set G) := (inSubgroup_perfectResidual_le _).trans inf_le_right
  have hEc : E ≤ centralizer ({c} : Set G) := hEL.trans sit.L_le_centralizer
  have hEcz : E ≤ centralizer ((zpowers c : Subgroup G) : Set G) := by
    intro e he'
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute c e from
      (Subgroup.mem_centralizer_singleton_iff.mp (hEc he')).symm) k).eq
  have hEcomm' : ⁅E, zpowers c⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hEcz
  have hLF : L ∈ thetaComponentFamily p A :=
    mem_thetaComponentFamily_iff.mpr ⟨c, hcA, sit.c_ne_one, sit.L_mem.2⟩
  have hAL : A ≤ normalizer (L : Set G) :=
    selected_prime_elements_normalize_theta_components.2 G he p hp hp3 A sit.A_elem L hLF
  have hAf : A ≤ centralizer ({f} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (sit.A_comm hx hfA)
  have hAE : A ≤ normalizer (E : Set G) := fun x hx =>
    SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      (L ⊓ centralizer ({f} : Set G))
      (FourSeed.mem_normalizer_inf' (hAL hx) (Subgroup.le_normalizer (hAf hx)))
  have hgenE := sit.fixedRes_le_closure hCent hFix hfA hfa
  have hBA : zpowers c ⊔ zpowers f ≤ A := sup_le (zpowers_le.mpr hcA) (zpowers_le.mpr hfA)
  have hBel : IsElementaryAbelian p (zpowers c ⊔ zpowers f : Subgroup G) :=
    SteinbergBM.isElementaryAbelian_of_le sit.A_elem hBA
  have hBcard := sit.sq_le_card_sup hij hi
  have hBE : zpowers c ⊔ zpowers f ≤ centralizer (E : Set G) := by
    refine sup_le (zpowers_le.mpr ?_) (zpowers_le.mpr ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro e he'
      exact Subgroup.mem_centralizer_singleton_iff.mp (hEc he')
    · rw [Subgroup.mem_centralizer_iff]
      intro e he'
      exact Subgroup.mem_centralizer_singleton_iff.mp (hEf he')
  obtain ⟨b, hbB, hb1, S, hSb, hS2, hS1, hES, hAS, hSE⟩ :=
    FourSeed.exists_stable_two_subgroup sit.setup.2.2.2.1 hp hp2
      (fun x hx y hy => sit.A_comm hx hy) hBA hBel hBcard hBE hEcomm hEne hAE hR2 hR1 hAR hER
  have hbA : b ∈ A := hBA hbB
  have hbp : b ^ p = 1 := sit.pow_eq_one hbA
  have hSEle : S ≤ ⁅S, E⁆ := hSE.ge
  have hSc : ⁅S, zpowers c⁆ ≠ ⊥ := by
    intro h0
    have hSC : S ≤ centralizer ({c} : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr (mem_zpowers c)))
    have hSL : S ≤ L :=
      FourSeed.commutator_le_thetaComponent he hp hp3 sit.L_mem.2 hEL hgenE hSC hSEle
    have h1 := hNL G p L f (sit.fieldAutSetting hfa) (sit.pow_eq_one hfA)
      (sit.fieldAutRank hfA) S hSL hS2 hES
    exact hS1 (hSE.symm.trans h1)
  obtain ⟨s, t, hbst⟩ := (S11d.mem_zpowers_sup_zpowers_iff
    (show Commute c f from sit.A_comm hcA hfA)).mp hbB
  have hac : Commute a c := sit.A_comm sit.a_mem hcA
  have ht : ¬ (p : ℤ) ∣ t := by
    intro hdiv
    have hft : f ^ t = 1 := hzp f t (sit.pow_eq_one hfA) hdiv
    have hbc : b = c ^ s := by rw [hbst, hft, mul_one]
    have hs : ¬ (p : ℤ) ∣ s := by
      intro hds
      apply hb1
      rw [hbc]
      exact hzp c s hcp hds
    have hcent := S11d.centralizer_zpow_eq (G := G) hp hcp hs
    have hSc' : S ≤ centralizer ({c} : Set G) := by
      rw [← hcent, ← hbc]
      exact hSb
    apply hSc
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hrc : r * c = c * r := Subgroup.mem_centralizer_singleton_iff.mp (hSc' hr)
    exact (Commute.zpow_left (show Commute c r from hrc.symm) k).eq
  have hbij : b = a ^ (i * t) * c ^ (s + j * t) := by
    have hft : f ^ t = a ^ (i * t) * c ^ (j * t) := by
      rw [hij, (hac.zpow_zpow i j).mul_zpow, ← zpow_mul, ← zpow_mul]
    rw [hbst, hft]
    have hcomm : c ^ s * a ^ (i * t) = a ^ (i * t) * c ^ s :=
      (hac.symm.zpow_zpow s (i * t)).eq
    calc c ^ s * (a ^ (i * t) * c ^ (j * t))
        = (c ^ s * a ^ (i * t)) * c ^ (j * t) := by rw [mul_assoc]
      _ = (a ^ (i * t) * c ^ s) * c ^ (j * t) := by rw [hcomm]
      _ = a ^ (i * t) * (c ^ s * c ^ (j * t)) := by rw [mul_assoc]
      _ = a ^ (i * t) * c ^ (s + j * t) := by rw [← zpow_add]
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hi' : ¬ (p : ℤ) ∣ i * t := fun h => (hpZ.dvd_mul.mp h).elim hi ht
  have hfab : InducesFieldAut p b L := hbij ▸ sit.inducesFieldAut_mul (s + j * t) hi'
  obtain ⟨Kb, hKb, hEKb⟩ := exists_thetaComponent_ge_fixedRes hS sit.setup hcA sit.c_ne_one hbA hb1
    sit.L_mem.2 (fixedRes_isQuasisimple hfab)
  have hEEb : inSubgroup perfectResidual (L ⊓ centralizer ({b} : Set G)) = E := by
    rw [sit.inf_centralizer_coords_eq hij hi hbij hi']
  have hEKb' : E ≤ Kb := hEEb ▸ hEKb
  set Rb : Subgroup G := ⁅S, zpowers c⁆ with hRb
  have hcS : c ∈ normalizer (S : Set G) := hAS hcA
  have hRbS : Rb ≤ S := Subgroup.le_normalizer_iff_commutator_le_left.mp (zpowers_le.mpr hcS)
  have hRb2 : IsPGroup 2 Rb := hS2.to_le hRbS
  have hAcz : A ≤ centralizer ((zpowers c : Subgroup G) : Set G) := fun x hx => by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact (Commute.zpow_left (show Commute c x from sit.A_comm hcA hx) k).eq
  have hcb : zpowers c ≤ centralizer ({b} : Set G) :=
    zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr (sit.A_comm hcA hbA))
  have hRbCb : Rb ≤ centralizer ({b} : Set G) := by
    rw [hRb, Subgroup.commutator_le]
    intro r hr z hz
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem (hSb hr) (hcb hz)) (inv_mem (hSb hr))) (inv_mem (hcb hz))
  have hRbA : A ≤ normalizer (Rb : Set G) := fun x hx =>
    FourSeed.mem_normalizer_commutator (hAS hx)
      (Subgroup.centralizer_le_normalizer _ (hAcz hx))
  have hRbE : E ≤ normalizer (Rb : Set G) := fun x hx =>
    FourSeed.mem_normalizer_commutator (hES hx)
      (Subgroup.centralizer_le_normalizer _ (hEcz hx))
  have hRbc : ⁅Rb, zpowers c⁆ = Rb :=
    FourSeed.commutator_zpowers_self hp hp2 hcord hS2 hcS
  have hWit : WitnessAt A c b Rb := ⟨hRbCb, hSc, hRb2, hRbA, hRbc.symm⟩
  have hRbE1 : ⁅Rb, E⁆ ≠ ⊥ := by
    intro h0
    apply hSc
    have h1 : ⁅⁅E, zpowers c⁆, S⁆ = ⊥ := by rw [hEcomm', Subgroup.commutator_bot_left]
    have h2 : ⁅⁅zpowers c, S⁆, E⁆ = ⊥ := by
      rw [Subgroup.commutator_comm (zpowers c) S]
      exact h0
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := S) (H₂ := E)
      (H₃ := zpowers c) h1 h2
    rwa [hSE] at h3
  have hmove : ∃ r ∈ Rb, ∃ k ∈ Kb,
      r * k * r⁻¹ * k⁻¹ ∉ inSubgroup (aschbacherSolvableCore p) Kb := by
    by_contra hno
    push Not at hno
    have hRK : ⁅Rb, Kb⁆ ≤ inSubgroup (aschbacherSolvableCore p) Kb := by
      rw [Subgroup.commutator_le]
      intro r hr k hk
      rw [commutatorElement_def]
      exact hno r hr k hk
    have hU : ⁅Rb, E⁆ ≤ inSubgroup (aschbacherSolvableCore p) Kb :=
      (Subgroup.commutator_mono le_rfl hEKb').trans hRK
    have hURb : ⁅Rb, E⁆ ≤ Rb := Subgroup.le_normalizer_iff_commutator_le_left.mp hRbE
    have hU2 : IsPGroup 2 (⁅Rb, E⁆ : Subgroup G) := hRb2.to_le hURb
    have hUA : A ≤ normalizer ((⁅Rb, E⁆ : Subgroup G) : Set G) := fun x hx =>
      FourSeed.mem_normalizer_commutator (hRbA hx) (hAE hx)
    have hUA0 := FourSeed.commutator_centralized_of_le_theta sit.setup hbA hb1 hKb hU hU2 hUA
    have hUc : ⁅⁅Rb, E⁆, zpowers c⁆ = ⊥ :=
      le_bot_iff.mp (hUA0 ▸ Subgroup.commutator_mono le_rfl (zpowers_le.mpr hcA))
    have h1 : ⁅⁅E, zpowers c⁆, Rb⁆ = ⊥ := by rw [hEcomm', Subgroup.commutator_bot_left]
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate (H₁ := zpowers c) (H₂ := Rb)
      (H₃ := E) hUc h1
    rw [Subgroup.commutator_comm (zpowers c) Rb, hRbc] at h3
    exact hRbE1 h3
  obtain ⟨-, -, -, hsetK, hEeq⟩ :=
    four_main hS h112 hbridge hK hLS hFix hCent sit hbij hi' hb1 hWit hKb hEKb hmove
  have hSKb : S ≤ Kb :=
    FourSeed.commutator_le_thetaComponent he hp hp3 hKb hEKb' hgenE hSb hSEle
  have hKbC : Kb ≤ centralizer ({b} : Set G) := (mem_thetaComponentsAt_iff.mp hKb).1
  have hrankK : FieldAutRank p Kb c :=
    ⟨he, b, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      Subgroup.mem_centralizer_singleton_iff.mp (hKbC hg), hb1, hbp, sit.A_comm hcA hbA⟩
  have hnl := hNL G p Kb c hsetK hcp hrankK S hSKb hS2 (by rw [← hEeq, hEEb]; exact hES)
  rw [← hEeq, hEEb] at hnl
  exact hS1 (hSE.symm.trans hnl)

@[expose] def FourCaseOne : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G),
    Sit p A c L a d → ∀ f : G, f ∈ zpowers a ⊔ zpowers c → f ≠ 1 → ∀ R : Subgroup G,
      WitnessAt A c f R → ∀ K₀ ∈ thetaComponentsAt p f,
        inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ≤ K₀ →
          ⁅R, K₀⁆ ≤ inSubgroup (aschbacherSolvableCore p) K₀ → False

@[expose] def FourThetaLift : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L : Subgroup G) (a d : G),
    Sit p A c L a d → ∀ f : G, f ∈ zpowers a ⊔ zpowers c → f ≠ 1 → ∀ R : Subgroup G,
      WitnessAt A c f R → ∀ K₀ ∈ thetaComponentsAt p f,
        inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ≤ K₀ →
          ⁅R, K₀⁆ ≤ inSubgroup (aschbacherSolvableCore p) K₀ →
            ⁅R, inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G))⁆ = ⊥

theorem fourCaseOne_of_lift (hS : SchreierFor InCatalog) (h112 : InSec11Two)
    (hbridge : CFSG.Assembly.CatalogImp InCatalog Catalog)
    (hK : CatalogPrimeTwoAutomorphismsInner) (hLS : FieldAutCoset) (hFix : FieldFixedPElements)
    (hCent : FieldFixedCentralizer) (hNL : FieldFixedNonLocal) (hLift : FourThetaLift) :
    FourCaseOne := by
  intro G _ _ p A c L a d sit f hf hf1 R hR K₀ hK₀ hEK₀ hmove
  obtain ⟨i, j, hij, hi⟩ := sit.exists_coords_of_witness hf hf1 hR
  have hRE := hLift G p A c L a d sit f hf hf1 R hR K₀ hK₀ hEK₀ hmove
  refine four_seed_false hS h112 hbridge hK hLS hFix hCent hNL sit hij hi hR.two hR.ne_bot
    hR.norm ?_
  have hER : inSubgroup perfectResidual (L ⊓ centralizer ({f} : Set G)) ≤
      centralizer (R : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp (by rw [Subgroup.commutator_comm]; exact hRE)
  exact fun x hx => Subgroup.centralizer_le_normalizer _ (hER hx)

end Sec11Indeed

end CFSG.RankThree.PartOne
