module

public import CFSG.RankThree.PartTwo.Sec6.Item64
import CFSG.RankThree.PartTwo.Sec6.Item63
public import CFSG.LocalAnalysis.RankThreeEvenClassification.HallFoundations
import CFSG.RankThree.PartTwo.Sec5.Item37
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.LocalAnalysis.RankThreeEvenClassification.HallContainment
import CFSG.CharacterTheory.Semidihedral.Principal.CoprimeFixedPointLifting
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
import CFSG.RankThree.PartTwo.Source.GammaTwoSubgroups
import CFSG.RankThree.PartTwo.Source.OrderThreeMinimalTwoGroup
public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
public import CFSG.RankThree.PartTwo.Sec6.Item612Basic

public section

namespace CFSG.RankThree.PartTwo.Sec6

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open scoped commutatorElement Pointwise

section ThetaFree

variable {X : Type*} [Group X] [Finite X]

theorem fittingSubgroup_le_pCore_three (hθ : aschbacherSolvableCore 3 X = ⊥) :
    fittingSubgroup X ≤ CFSG.pCore 3 X := by
  rw [fitting_eq_sup_pCore]
  refine iSup_le fun p => ?_
  have hp : (p.1 : ℕ).Prime := Nat.prime_of_mem_primeFactors p.1.2
  by_cases h3 : (p.1 : ℕ) = 3
  · rw [h3]
  · have := (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.2.2.2.2
      p.1 hp h3
    rw [hθ] at this
    exact this.trans bot_le

theorem eq_bot_of_le_centralizer_components (hθ : aschbacherSolvableCore 3 X = ⊥)
    {W : Subgroup X} (hW : IsPGroup 2 W)
    (h3 : W ≤ Subgroup.centralizer (CFSG.pCore 3 X : Set X))
    (hJ : ∀ J : Subgroup X, IsComponent J → W ≤ Subgroup.centralizer (J : Set X)) : W = ⊥ := by
  have hF3 := fittingSubgroup_le_pCore_three hθ
  have hWF : W ≤ Subgroup.centralizer (fittingSubgroup X : Set X) :=
    h3.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hF3))
  have hWE : W ≤ Subgroup.centralizer (layer X : Set X) :=
    Subgroup.le_centralizer_iff.mpr (sSup_le fun J hJ' => Subgroup.le_centralizer_iff.mp (hJ J hJ'))
  have hWF' : W ≤ Subgroup.centralizer (generalizedFitting X : Set X) := by
    rw [generalizedFitting, Source.centralizer_sup_eq]
    exact le_inf hWF hWE
  set Z := Subgroup.centralizer (generalizedFitting X : Set X)
  have hZF : Z ≤ generalizedFitting X := centralizer_generalizedFitting_le X
  have : (generalizedFitting X).Normal := by
    rw [generalizedFitting_eq_componentClassification]
    exact CFSG.ComponentClassification.GeneralizedFitting.normal X
  have hZn : Z.Normal := inferInstance
  have hZc : IsMulCommutative Z := by
    refine ⟨⟨fun a b => Subtype.ext ?_⟩⟩
    show (a : X) * b = b * a
    exact Subgroup.mem_centralizer_iff.mp b.2 a (hZF a.2)
  have hZnil : Group.IsNilpotent Z := CommGroup.isNilpotent
  have hZfit : Z ≤ fittingSubgroup X := le_sSup ⟨hZn, hZnil⟩
  have hW3 : W ≤ CFSG.pCore 3 X := hWF'.trans (hZfit.trans hF3)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hbot := Source.inf_eq_bot_of_isPGroup (p := 2) (q := 3) (by norm_num) hW
    (CFSG.pCore_isPGroup (p := 3) (G := X))
  rwa [inf_eq_left.mpr hW3] at hbot

end ThetaFree


section Hall

variable {X : Type*} [Group X] [Finite X]

open CFSG.RankThreeEvenClassification.Helpers

omit [Finite X] in
theorem isSolvable_sup_of_le_normalizer {N K : Subgroup X}
    (hKN : K ≤ Subgroup.normalizer (N : Set X)) (hN : Group.IsSolvable N)
    (hK : Group.IsSolvable K) : Group.IsSolvable (N ⊔ K : Subgroup X) := by
  set M := N ⊔ K
  have hNM : N ≤ M := le_sup_left
  have hKM : K ≤ M := le_sup_right
  have hMN : M ≤ Subgroup.normalizer (N : Set X) := sup_le Subgroup.le_normalizer hKN
  have hn : (N.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNM).mpr hMN
  set q := QuotientGroup.mk' (N.subgroupOf M)
  have hsurj : Function.Surjective (q.comp (Subgroup.inclusion hKM)) := by
    intro z
    obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective _ z
    have hm : (m : X) ∈ (N : Set X) * (K : Set X) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left N K hKN]
      exact m.2
    obtain ⟨n, hn', k, hk, hnk⟩ := hm
    refine ⟨⟨k, hk⟩, ?_⟩
    simp only [MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    rw [Subgroup.mem_subgroupOf]
    have h1 : k⁻¹ * n * k⁻¹⁻¹ ∈ N := (Subgroup.mem_normalizer_iff.mp (hKN (inv_mem hk)) n).mp hn'
    have h2 : ((Subgroup.inclusion hKM ⟨k, hk⟩)⁻¹ * m : M) = k⁻¹ * n * k⁻¹⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_inclusion, inv_inv]
      rw [← hnk]
      group
    rw [h2]
    exact h1
  have : Group.IsSolvable (M ⧸ N.subgroupOf M) := Group.isSolvable_of_surjective hsurj
  have : Group.IsSolvable (N.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hNM).toMonoidHom) (MulEquiv.injective _)
  exact Group.isSolvable_of_ker_le_range (N.subgroupOf M).subtype q
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem primeSetOrder_of_isPGroup {p : ℕ} [Fact p.Prime] {primes : Set ℕ} (hp : p ∈ primes)
    {P : Subgroup X} (hP : IsPGroup p P) : PrimeSetOrder primes (Nat.card P) := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  rw [hk]
  exact PrimeSetOrder.prime_pow primes p Fact.out hp k

theorem map_le_centralizer_pCore_of_odd {E S : Subgroup X}
    (hθodd : Odd (Nat.card (aschbacherSolvableCore 3 X))) (hE : IsPGroup 3 E) (hS : IsPGroup 2 S)
    (hES : E ≤ Subgroup.normalizer (S : Set X))
    (h : ∀ P : Subgroup X, IsPGroup 3 P → E ⊔ S ≤ Subgroup.normalizer (P : Set X) →
      P ≤ Subgroup.centralizer (S : Set X)) :
    S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) ≤
      Subgroup.centralizer (CFSG.pCore 3 (X ⧸ aschbacherSolvableCore 3 X) :
        Set (X ⧸ aschbacherSolvableCore 3 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 X with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  set Pb := CFSG.pCore 3 (X ⧸ θ) with hPb
  set P := Pb.comap ρ with hP
  obtain ⟨hθsol, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := X) Nat.prime_three
  have hPbn : Pb.Normal := CFSG.pCore_normal
  have hPn : P.Normal := hPbn.comap ρ
  have hθP : θ ≤ P := fun x hx => by
    change ρ x ∈ Pb
    rw [show ρ x = 1 from (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  have hPb3 : IsPGroup 3 Pb := CFSG.pCore_isPGroup
  have hPsol : Group.IsSolvable P := by
    let g : P →* Pb := (ρ.comp P.subtype).codRestrict Pb (fun x => x.2)
    have : Group.IsNilpotent Pb := hPb3.isNilpotent
    have : Group.IsSolvable θ := hθsol
    refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hθP) g ?_
    intro x hx
    have hx1 : ρ x = 1 := congrArg Subtype.val hx
    exact ⟨⟨x, (QuotientGroup.eq_one_iff _).mp hx1⟩, rfl⟩
  set ES := E ⊔ S with hESdef
  have hESsol : Group.IsSolvable ES := by
    have : Group.IsNilpotent S := hS.isNilpotent
    have : Group.IsNilpotent E := hE.isNilpotent
    have h1 := isSolvable_sup_of_le_normalizer hES inferInstance inferInstance
    rwa [sup_comm] at h1
  have hESP : ES ≤ Subgroup.normalizer (P : Set X) := by
    rw [Subgroup.normalizer_eq_top P]
    exact le_top
  set M := P ⊔ ES with hM
  have hMsol : Group.IsSolvable M := isSolvable_sup_of_le_normalizer hESP hPsol hESsol
  have hESM : ES ≤ M := le_sup_right
  have hPM : P ≤ M := le_sup_left
  have hθM : θ ≤ M := hθP.trans hPM
  set π : Set ℕ := {2, 3} with hπ
  have h2π : 2 ∈ π := by rw [hπ]; exact Set.mem_insert 2 _
  have h3π : 3 ∈ π := by rw [hπ]; simp
  have hESπ : PrimeSetOrder π (Nat.card (ES.subgroupOf M)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hESM).toEquiv, hESdef, sup_comm]
    exact normalized_sup_primeSetOrder π S E hES (primeSetOrder_of_isPGroup h2π hS)
      (primeSetOrder_of_isPGroup h3π hE)
  obtain ⟨Hl, hHl, hESHl⟩ := hall_containment_of_solvable π (ES.subgroupOf M) hESπ
  set θM := θ.subgroupOf M with hθMdef
  have hθMn : θM.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hθM).mpr
    (by rw [Subgroup.normalizer_eq_top θ]; exact le_top)
  have hθMcard : Nat.card θM = Nat.card θ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hθM).toEquiv
  have hθπ : PrimeSetOrder πᶜ (Nat.card θM) := by
    intro q hq hqd
    rw [hθMcard] at hqd
    simp only [hπ, Set.mem_compl_iff, Set.mem_insert_iff, Set.mem_singleton_iff, not_or]
    refine ⟨fun h2 => ?_, fun h3 => ?_⟩
    swap
    · rw [h3] at hqd
      exact hθ3 hqd
    rw [h2] at hqd
    exact (Nat.not_even_iff_odd.mpr hθodd) (even_iff_two_dvd.mpr hqd)
  set ρM : M →* X ⧸ θ := ρ.comp M.subtype with hρM
  have hker : ρM.ker = θM := by
    ext x
    rw [MonoidHom.mem_ker, hρM, MonoidHom.comp_apply, Subgroup.coe_subtype,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hrange : ρM.range = M.map ρ := by
    rw [hρM, MonoidHom.range_comp, Subgroup.range_subtype]
  have hcardM : Nat.card M = Nat.card (M.map ρ) * Nat.card θM := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup ρM.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivRange ρM).toEquiv, hrange, hker]
  have hMπ : PrimeSetOrder π (Nat.card (M.map ρ)) := by
    have heq : M.map ρ = Pb ⊔ ES.map ρ := by
      rw [hM, Subgroup.map_sup, hP,
        Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective θ)]
    rw [heq]
    exact normalized_sup_primeSetOrder π Pb (ES.map ρ)
      (by rw [Subgroup.normalizer_eq_top Pb]; exact le_top)
      (primeSetOrder_of_isPGroup h3π hPb3)
      (PrimeSetOrder.of_dvd π _ _ (by
        rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hESM).toEquiv]
        exact hESπ) (Subgroup.card_map_dvd ES ρ))
  have hindex : Hl.index = Nat.card θM := by
    have h1 : Nat.card Hl * Hl.index = Nat.card (M.map ρ) * Nat.card θM := by
      rw [Subgroup.card_mul_index, hcardM]
    have hc1 : (Nat.card Hl).Coprime (Nat.card θM) := PrimeSetOrder.coprime_compl π _ _ hHl.1 hθπ
    have hc2 : (Nat.card (M.map ρ)).Coprime Hl.index :=
      PrimeSetOrder.coprime_compl π _ _ hMπ hHl.2
    apply Nat.dvd_antisymm
    · exact (hc2.symm).dvd_of_dvd_mul_left (h1 ▸ Dvd.intro_left _ rfl)
    · exact (hc1.symm).dvd_of_dvd_mul_left (h1.symm ▸ Dvd.intro_left _ rfl)
  have hdisj : Disjoint Hl θM :=
    Subgroup.disjoint_of_coprime_natCard (PrimeSetOrder.coprime_compl π _ _ hHl.1 hθπ)
  have hsup : Hl ⊔ θM = ⊤ := (Subgroup.isComplement'_of_card_mul_and_disjoint
    (by rw [← hindex, Subgroup.card_mul_index]) hdisj).sup_eq_top
  set PM := P.subgroupOf M with hPMdef
  have hPMn : PM.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hPM).mpr
    (by rw [Subgroup.normalizer_eq_top P]; exact le_top)
  set R := Hl ⊓ PM with hR
  have hθMPM : θM ≤ PM := fun x hx =>
    Subgroup.mem_subgroupOf.mpr (hθP (Subgroup.mem_subgroupOf.mp hx))
  have hRθ : ∀ x ∈ PM, ∃ r ∈ R, ∃ t ∈ θM, r * t = x := by
    intro x hx
    have hx' : x ∈ Hl ⊔ θM := hsup ▸ Subgroup.mem_top x
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
    refine ⟨y, ⟨hy, ?_⟩, z, hz, rfl⟩
    have := PM.mul_mem hx (inv_mem (hθMPM hz))
    simpa using this
  set RX := R.map M.subtype with hRX
  have hRXP : RX ≤ P := by
    rintro _ ⟨r, hr, rfl⟩
    exact Subgroup.mem_subgroupOf.mp hr.2
  have hRX3 : IsPGroup 3 RX := by
    rintro ⟨_, r, hr, rfl⟩
    have hrP : ρ (r : X) ∈ Pb := Subgroup.mem_subgroupOf.mp hr.2
    obtain ⟨k, hk⟩ := hPb3 ⟨_, hrP⟩
    have hk' : ρ ((r : X) ^ (3 ^ k)) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    have hθk : r ^ (3 ^ k) ∈ θM := by
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow]
      exact (QuotientGroup.eq_one_iff _).mp hk'
    have hHk : r ^ (3 ^ k) ∈ Hl := Hl.pow_mem hr.1 _
    have h1 : r ^ (3 ^ k) = 1 := Subgroup.disjoint_def.mp hdisj hHk hθk
    refine ⟨k, Subtype.ext ?_⟩
    simp only [SubmonoidClass.coe_pow, Subgroup.coe_subtype, OneMemClass.coe_one]
    rw [← Subgroup.coe_pow, h1, OneMemClass.coe_one]
  have hRXN : ES ≤ Subgroup.normalizer (RX : Set X) := by
    intro g hg
    set g' : M := ⟨g, hESM hg⟩
    have hg'H : g' ∈ Hl := hESHl (Subgroup.mem_subgroupOf.mpr hg)
    have hg'R : g' ∈ Subgroup.normalizer (R : Set M) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg'H,
        by rw [Subgroup.normalizer_eq_top PM]; exact Subgroup.mem_top _⟩
    exact Subgroup.le_normalizer_map M.subtype ⟨g', hg'R, rfl⟩
  have hRXS : RX ≤ Subgroup.centralizer (S : Set X) := h RX hRX3 hRXN
  rintro _ ⟨s, hs, rfl⟩
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ q
  have hxP : x ∈ P := hq
  obtain ⟨r, hr, t, ht, hrt⟩ := hRθ ⟨x, hPM hxP⟩ (Subgroup.mem_subgroupOf.mpr hxP)
  have hρx : ρ x = ρ (r : X) := by
    have := congrArg (fun m : M => ρ (m : X)) hrt
    simp only [Subgroup.coe_mul, map_mul] at this
    have ht1 : ρ (t : X) = 1 := (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mp ht)
    rw [← this, ht1, mul_one]
  have hrs : s * (r : X) = (r : X) * s :=
    Subgroup.mem_centralizer_iff.mp (hRXS ⟨r, hr, rfl⟩) s hs
  change ρ x * ρ s = ρ s * ρ x
  rw [hρx, ← map_mul, ← map_mul, ← hrs]

theorem exists_centralizer_lift_of_pow_three {E : Subgroup X} (hE : IsPGroup 3 E) (x : X)
    (hx : ∀ e ∈ E, QuotientGroup.mk' (aschbacherSolvableCore 3 X) (e * x * e⁻¹) =
      QuotientGroup.mk' (aschbacherSolvableCore 3 X) x)
    (hx3 : QuotientGroup.mk' (aschbacherSolvableCore 3 X) (x ^ 3) = 1) :
    ∃ d ∈ Subgroup.centralizer (E : Set X), d ^ 3 = 1 ∧
      QuotientGroup.mk' (aschbacherSolvableCore 3 X) d =
        QuotientGroup.mk' (aschbacherSolvableCore 3 X) x := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 X with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  have hθ3 : ¬ 3 ∣ Nat.card θ :=
    (solvable_prime_complement_core_characterization (H := X) Nat.prime_three).2.2.1
  have hxθ : ∀ e ∈ E, x⁻¹ * (e * x * e⁻¹) ∈ θ := fun e he => by
    have := hx e he
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at this
    have h2 := inv_mem this
    simpa using h2
  set α : E →* MulAut X := MulAut.conj.comp E.subtype
  obtain ⟨c, hc, hcfix⟩ := (CFSG.Semidihedral.Principal.coprime_invariant_coset_fixed 3 hE α θ hθ3
    x).2 (by
      intro a y hy
      change x⁻¹ * ((a : X) * y * (a : X)⁻¹) ∈ θ
      have h1 := hxθ a a.2
      have h2 : (a : X) * (x⁻¹ * y) * (a : X)⁻¹ ∈ θ :=
        (aschbacherSolvableCore_normal 3 X).conj_mem _ hy _
      have h3 := θ.mul_mem h1 h2
      rwa [show x⁻¹ * ((a : X) * x * (a : X)⁻¹) * ((a : X) * (x⁻¹ * y) * (a : X)⁻¹) =
        x⁻¹ * ((a : X) * y * (a : X)⁻¹) by group] at h3)
  have hcE : c ∈ Subgroup.centralizer (E : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    have h1 : (e : X) * c * e⁻¹ = c := hcfix ⟨e, he⟩
    calc e * c = (e * c * e⁻¹) * e := by group
      _ = c * e := by rw [h1]
  have hρc : ρ c = ρ x := by
    rw [hρ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have h2 := inv_mem hc
    simpa using h2
  set m := orderOf (c ^ 3)
  have hc3θ : c ^ 3 ∈ θ := by
    rw [← QuotientGroup.eq_one_iff (N := θ)]
    change ρ (c ^ 3) = 1
    rw [map_pow, hρc, ← map_pow]
    exact hx3
  have hm3 : ¬ 3 ∣ m := by
    intro hdvd
    apply hθ3
    exact hdvd.trans (by
      have := Subgroup.orderOf_dvd_natCard θ hc3θ
      exact this)
  have hmm : m * m % 3 = 1 := by
    have h1 : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases h1 with h1 | h1
    · rw [Nat.mul_mod, h1]
    · rw [Nat.mul_mod, h1]
  refine ⟨c ^ (m * m), Subgroup.pow_mem _ hcE _, ?_, ?_⟩
  · rw [← pow_mul, mul_comm, pow_mul, mul_comm, pow_mul, pow_orderOf_eq_one, one_pow]
  · rw [map_pow, hρc]
    have hx3' : ρ x ^ 3 = 1 := by rw [← map_pow]; exact hx3
    rw [← Nat.div_add_mod (m * m) 3, hmm, pow_add, pow_mul, hx3', one_pow, one_mul, pow_one]

theorem map_le_centralizer_pCore_of_omega {E S : Subgroup X}
    (hE : CFSG.Assembly.IsElemAbelian 3 E) (hS : IsPGroup 2 S)
    (hES : E ≤ Subgroup.normalizer (S : Set X))
    (hmax : ∀ x ∈ Subgroup.centralizer (E : Set X), x ^ 3 = 1 → x ∈ E) :
    S.map (QuotientGroup.mk' (aschbacherSolvableCore 3 X)) ≤
      Subgroup.centralizer (CFSG.pCore 3 (X ⧸ aschbacherSolvableCore 3 X) :
        Set (X ⧸ aschbacherSolvableCore 3 X)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 X with hθdef
  set ρ := QuotientGroup.mk' θ with hρ
  set Pb := CFSG.pCore 3 (X ⧸ θ) with hPb
  have hPbn : Pb.Normal := CFSG.pCore_normal
  have hE3 : IsPGroup 3 E := Sec5.isPGroup_of_isElemAbelian hE
  have hEb : CFSG.Assembly.IsElemAbelian 3 (E.map ρ) :=
    CFSG.RankThreeEvenClassification.Helpers.isElemAbelian_map 3 ρ E hE
  have hSb : ¬ 3 ∣ Nat.card (S.map ρ) := by
    intro h3
    have h1 := h3.trans (Subgroup.card_map_dvd S ρ)
    exact Source.not_three_dvd_card_of_isPGroup_two hS h1
  have hESb : E.map ρ ≤ Subgroup.normalizer ((S.map ρ : Subgroup (X ⧸ θ)) : Set (X ⧸ θ)) :=
    (Subgroup.map_mono hES).trans (Subgroup.le_normalizer_map ρ)
  have htop : ∀ K : Subgroup (X ⧸ θ), K ≤ Subgroup.normalizer (Pb : Set (X ⧸ θ)) := fun K => by
    rw [Subgroup.normalizer_eq_top Pb]
    exact le_top
  have hΩ : ∀ y ∈ (E.map ρ ⊔ Pb) ⊓ Subgroup.centralizer ((E.map ρ : Subgroup (X ⧸ θ)) :
      Set (X ⧸ θ)), y ^ 3 = 1 → y ∈ E.map ρ := by
    rintro y ⟨-, hyC⟩ hy3
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective θ y
    change ρ x ∈ Subgroup.centralizer _ at hyC
    have hx : ∀ e ∈ E, ρ (e * x * e⁻¹) = ρ x := by
      intro e he
      have h1 : ρ e * ρ x = ρ x * ρ e := Subgroup.mem_centralizer_iff.mp hyC (ρ e) ⟨e, he, rfl⟩
      rw [map_mul, map_mul, map_inv, h1, mul_inv_cancel_right]
    obtain ⟨d, hdC, hd3, hdx⟩ := exists_centralizer_lift_of_pow_three hE3 x hx
      (by rw [map_pow]; exact hy3)
    exact ⟨d, hmax d hdC hd3, hdx⟩
  have h37 := Sec5.rank3II_3_7 (X ⧸ θ) 3 Nat.prime_three (by norm_num) (E.map ρ) (S.map ρ) Pb
    hEb hSb hESb CFSG.pCore_isPGroup (htop _) (htop _) hΩ
  rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h37
  exact h37

end Hall

section Ambient

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_thetaComponentsAt_not_le {c : G} {V : Subgroup G}
    (hV2 : IsPGroup 2 V) (hVc : V ≤ Subgroup.centralizer ({c} : Set G))
    (hVθ : ¬ V ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)))
    (hV3 : (V.subgroupOf (Subgroup.centralizer ({c} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G)))) ≤
      Subgroup.centralizer (CFSG.pCore 3 (Subgroup.centralizer ({c} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))) :
          Set (Subgroup.centralizer ({c} : Set G) ⧸
            aschbacherSolvableCore 3 (Subgroup.centralizer ({c} : Set G))))) :
    ∃ L ∈ thetaComponentsAt 3 c,
      ¬ ⁅L, V⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({c} : Set G)) := by
  set H := Subgroup.centralizer ({c} : Set G) with hH
  set θH := aschbacherSolvableCore 3 H with hθH
  set ρ := QuotientGroup.mk' θH with hρ
  set W := (V.subgroupOf H).map ρ with hW
  have hW2 : IsPGroup 2 W := (hV2.comap_of_injective H.subtype H.subtype_injective).map ρ
  by_contra hcon
  push Not at hcon
  have hWbot : W = ⊥ := by
    refine eq_bot_of_le_centralizer_components (theta_quotient_core_and_ranks (G := H)).1 hW2 hV3
      fun J hJ => ?_
    obtain ⟨hL', hL'J⟩ := perfectResidual_comap_mem_thetaComponents Nat.prime_three hJ
    set L' := inSubgroup perfectResidual (J.comap ρ)
    have hL : L'.map H.subtype ∈ thetaComponentsAt 3 c := ⟨L', hL', rfl⟩
    have hLV := hcon _ hL
    rintro _ ⟨v, hv, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    rw [← hL'J] at hj
    obtain ⟨l, hl, rfl⟩ := hj
    have hlv : ⁅(l : G), (v : G)⁆ ∈ inSubgroup (aschbacherSolvableCore 3) H :=
      hLV (Subgroup.commutator_mem_commutator ⟨l, hl, rfl⟩ (Subgroup.mem_subgroupOf.mp hv))
    obtain ⟨t, ht, hteq⟩ := hlv
    have ht' : t = ⁅l, v⁆ := Subtype.ext (by simpa [commutatorElement_def] using hteq)
    have h1 : ρ ⁅l, v⁆ = 1 := by
      rw [← ht', hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact ht
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  apply hVθ
  intro v hv
  have hmem : ρ ⟨v, hVc hv⟩ ∈ W := ⟨⟨v, hVc hv⟩, Subgroup.mem_subgroupOf.mpr hv, rfl⟩
  rw [hWbot, Subgroup.mem_bot, hρ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hmem
  exact ⟨_, hmem, rfl⟩

theorem map_le_centralizer_pCore_of_mem_partTwoS (hG : PartTwoStanding G) {A E : Subgroup G}
    (hA : A ∈ partTwoS G) (hE : E ∈ collectionIn (partTwoE G) A) {b : G} (hbE : b ∈ E)
    {S : Subgroup G} (hS2 : IsPGroup 2 S) (hSb : S ≤ Subgroup.centralizer ({b} : Set G))
    (hES : E ≤ Subgroup.normalizer (S : Set G))
    (h64 : ∀ P : Subgroup G, IsPGroup 3 P → E ⊔ S ≤ Subgroup.normalizer (P : Set G) →
      P ≤ Subgroup.centralizer (S : Set G)) :
    (S.subgroupOf (Subgroup.centralizer ({b} : Set G))).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G)))) ≤
      Subgroup.centralizer (CFSG.pCore 3 (Subgroup.centralizer ({b} : Set G) ⧸
        aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G))) :
          Set (Subgroup.centralizer ({b} : Set G) ⧸
            aschbacherSolvableCore 3 (Subgroup.centralizer ({b} : Set G)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.centralizer ({b} : Set G) with hH
  obtain ⟨hEmem, hEA⟩ := hE
  have hAab := hA.1.1
  have hbA : b ∈ A := hEA hbE
  have hAH : A ≤ H := fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr
    (congrArg Subtype.val (hAab.1.is_comm.comm ⟨a, ha⟩ ⟨b, hbA⟩))
  have hEH : E ≤ H := hEA.trans hAH
  have hE3 : IsPGroup 3 (E.subgroupOf H) :=
    (Sec5.isPGroup_of_isElemAbelian hEmem.1).comap_of_injective H.subtype H.subtype_injective
  have hS2' : IsPGroup 2 (S.subgroupOf H) := hS2.comap_of_injective H.subtype H.subtype_injective
  have hES' : E.subgroupOf H ≤ Subgroup.normalizer ((S.subgroupOf H : Subgroup H) : Set H) :=
    subgroupOf_le_normalizer_subgroupOf hES
  by_cases hodd : Odd (Nat.card (aschbacherSolvableCore 3 H))
  · refine map_le_centralizer_pCore_of_odd hodd hE3 hS2' hES' fun P hP3 hPN => ?_
    set PG := P.map H.subtype with hPG
    have hPG3 : IsPGroup 3 PG := hP3.map _
    have hPGN : E ⊔ S ≤ Subgroup.normalizer (PG : Set G) := by
      have hmap : ∀ X : Subgroup G, X ≤ H → X.subgroupOf H ≤ Subgroup.normalizer (P : Set H) →
          X ≤ Subgroup.normalizer (PG : Set G) := by
        intro X hXH hXP x hx
        exact Subgroup.le_normalizer_map H.subtype
          ⟨⟨x, hXH hx⟩, hXP (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
      exact sup_le (hmap E hEH (le_sup_left.trans hPN)) (hmap S hSb (le_sup_right.trans hPN))
    have hPC := h64 PG hPG3 hPGN
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hPC ⟨x, hx, rfl⟩) s
      (Subgroup.mem_subgroupOf.mp hs))
  ·
    have hev : 2 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) H) := by
      rw [inSubgroup, Subgroup.card_map_of_injective H.subtype_injective]
      exact even_iff_two_dvd.mp (Nat.not_odd_iff_even.mp hodd)
    set θG := inSubgroup (aschbacherSolvableCore 3) H with hθG
    have hθ3 : ¬ 3 ∣ Nat.card θG := (theta_solvable_and_not_dvd H).2
    have hAθ : A ≤ Subgroup.normalizer (θG : Set G) :=
      hAH.trans (le_normalizer_map_subtype (aschbacherSolvableCore 3 H))
    obtain ⟨R, hAR⟩ :=
      CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
        3 Nat.prime_three A θG (Sec5.isPGroup_of_isElemAbelian hAab) hθ3 hAθ 2 Nat.prime_two
    have hR1 : (R : Subgroup θG).map θG.subtype ≠ ⊥ := by
      intro hbot
      apply R.ne_bot_of_dvd_card hev
      exact (Subgroup.map_eq_bot_iff_of_injective _ θG.subtype_injective).mp hbot
    have hcard := Sec5.card_le_of_le_normalizer hG.evenRank_eq hR1 (R.isPGroup'.map _) hAab hAR
    have hAE : E = A := Subgroup.eq_of_le_of_card_ge hEA (by rw [hEmem.2.1]; exact hcard)
    have hmax : ∀ x ∈ Subgroup.centralizer ((E.subgroupOf H : Subgroup H) : Set H), x ^ 3 = 1 →
        x ∈ E.subgroupOf H := by
      intro x hx hx3
      rw [Subgroup.mem_subgroupOf, hAE]
      by_contra hxA
      have hxA' : ∀ a ∈ A, a * (x : G) = (x : G) * a := by
        intro a ha
        have := Subgroup.mem_centralizer_iff.mp hx ⟨a, hAH ha⟩
          (Subgroup.mem_subgroupOf.mpr (hAE ▸ ha))
        simpa using (congrArg Subtype.val this)
      obtain ⟨hab', hcard'⟩ := Sec5.isElemAbelian_sup_zpowers hAab hxA
        (by rw [← Subgroup.coe_pow, hx3, OneMemClass.coe_one]) hxA'
      have heq := hA.1.2.1 _ hab' le_sup_left
      have := congrArg (fun K : Subgroup G => Nat.card K) heq
      rw [hcard'] at this
      have hpos : 0 < Nat.card A := Nat.card_pos
      omega
    exact map_le_centralizer_pCore_of_omega (isElemAbelian_subgroupOf hEmem.1) hS2' hES' hmax

end Ambient

end CFSG.RankThree.PartTwo.Sec6
