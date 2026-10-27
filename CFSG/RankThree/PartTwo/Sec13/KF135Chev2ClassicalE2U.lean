module

public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2ClassicalCases
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUUnitary
public import CFSG.RankThree.PartTwo.Sec13.KF135Chev2E2Tools
public import CFSG.RankThree.PartOne.K1214.SylowSU3

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Chev2

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag
open CFSG.SectionRank.OddCover (diagHom coe_diagHom diagHom_injective)
open CFSG.RankThree.PartOne.OutStructure (OutPChain)
open CFSG.LieType.Chevalley (fixSubfield)

section PSU3

variable {e₀ : ℕ} {L : Type} [Field L] [Finite L] [CharP L 2] (h₀ : UnitaryFieldData 2 e₀ L)

theorem exists_involution_commute_psu3 {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ 2 ^ e₀ + 1)
    {B : Subgroup (primeFormP h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L))}
    (hB : CFSG.Open.IsElemAbelian p B) (hBc : p ^ 2 ≤ Nat.card B) :
    ∃ t ∈ B, t ≠ 1 ∧ ∃ s : primeFormP h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L),
      s ≠ 1 ∧ s * s = 1 ∧ s * t = t * s := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set G := gramSU h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) with hGdef
  set N := normOneScalars h₀ G 3 with hNdef
  set π : G →* primeFormP h₀ ((1 : GL (Fin 3) L) : Matrix (Fin 3) (Fin 3) L) :=
    QuotientGroup.mk' N with hπ
  have hNcard : Nat.card N = Nat.gcd 3 (2 ^ e₀ + 1) :=
    CFSG.RankThree.Classical.card_normOneScalars_one h₀ (n := 3) (by norm_num)
  have hnp : ∀ z ∈ π.ker, z ^ p = 1 → z = 1 := by
    intro z hz hzp
    rw [hπ, QuotientGroup.ker_mk'] at hz
    have h1 : orderOf z ∣ p := orderOf_dvd_of_pow_eq_one hzp
    have h2 : orderOf z ∣ 3 :=
      (Subgroup.orderOf_dvd_natCard N hz).trans (hNcard ▸ Nat.gcd_dvd_left 3 _)
    have h4 : Nat.gcd p 3 = 1 := (Nat.coprime_primes hp Nat.prime_three).2 (by omega)
    have h3 : orderOf z ∣ Nat.gcd p 3 := Nat.dvd_gcd h1 h2
    rw [h4, Nat.dvd_one, orderOf_eq_one_iff] at h3
    exact h3
  obtain ⟨At, hAtmap, hAtinj, hAtab, hAtcard⟩ :=
    CFSG.StandardType.TableBUE.exists_lift_of_noTorsion π (QuotientGroup.mk'_surjective N) hp
      hnp hB
  set U := unitarySU 2 e₀ L 3 with hUdef
  have hGU : G = U := (unitarySU_eq_gramSU h₀ 3).symm
  set ε : G ≃* U := MulEquiv.subgroupCongr hGU with hε
  set AU : Subgroup U := At.map ε.toMonoidHom with hAU
  have hAUab : CFSG.Open.IsElemAbelian p AU := CFSG.Open.IsElemAbelian.map hAtab _
  have hAUcard : Nat.card AU = Nat.card At :=
    Subgroup.card_map_of_injective ε.injective
  obtain ⟨P₀, hP₀⟩ := CFSG.StandardType.OrdPInnerSU.exists_su_conj_diag h₀ (n := 3)
    (by norm_num) hp hpq hAUab
  set δ : AU →* GL (Fin 3) L :=
    U.subtype.comp ((MulAut.conj P₀⁻¹).toMonoidHom.comp AU.subtype) with hδ
  have hδapply : ∀ x : AU, δ x = ((P₀⁻¹ * (x : U) * P₀ : U) : GL (Fin 3) L) := fun x => by
    rw [hδ]
    simp [MulAut.conj_apply]
  have hrange : ∀ x : AU, δ x ∈ (diagHom (K := L) 3).range := fun x => by
    obtain ⟨σ, hσ⟩ := hP₀ x x.2
    exact ⟨σ, by rw [hδapply, hσ]⟩
  set ψ : AU →* (Fin 3 → Lˣ) :=
    (MonoidHom.ofInjective (diagHom_injective (K := L) 3)).symm.toMonoidHom.comp
      (δ.codRestrict _ hrange) with hψ
  have hψδ : ∀ x : AU, diagHom 3 (ψ x) = δ x := fun x => by
    have h1 := MonoidHom.ofInjective_apply (diagHom_injective (K := L) 3) (x := ψ x)
    have h2 : MonoidHom.ofInjective (diagHom_injective (K := L) 3) (ψ x) = ⟨δ x, hrange x⟩ :=
      MulEquiv.apply_symm_apply _ _
    rw [h2] at h1
    exact h1.symm
  set χ : AU →* Lˣ := (Pi.evalMonoidHom (fun _ : Fin 3 => Lˣ) 0).comp ψ /
    (Pi.evalMonoidHom (fun _ : Fin 3 => Lˣ) 1).comp ψ with hχ
  have hχp : ∀ x : AU, χ x ^ p = 1 := fun x => by
    rw [← map_pow, hAUab.2 _ x.2 |> fun h => (show x ^ p = 1 from Subtype.ext h), map_one]
  have hrange_le : χ.range ≤ rootsOfUnity p L := by
    rintro _ ⟨x, rfl⟩
    exact (mem_rootsOfUnity p _).2 (hχp x)
  have hcardrange : Nat.card χ.range ≤ p := by
    have h1 := Subgroup.card_le_of_le hrange_le
    have h2 : Nat.card (rootsOfUnity p L) ≤ p := card_rootsOfUnity L p
    omega
  have hker : 1 < Nat.card χ.ker := by
    have h1 := Subgroup.card_mul_index χ.ker
    rw [Subgroup.index_ker] at h1
    have h3 : p ^ 2 ≤ Nat.card AU := by rw [hAUcard, hAtcard]; exact hBc
    by_contra hle
    push Not at hle
    have h4 : Nat.card AU ≤ 1 * p := by
      rw [← h1]
      exact Nat.mul_le_mul hle hcardrange
    have : p < p ^ 2 := by
      calc p = p ^ 1 := (pow_one p).symm
        _ < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hne : χ.ker ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot _).1 hker
  obtain ⟨y, hy1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hne
  set x : AU := (y : AU) with hxdef
  have hxker : x ∈ χ.ker := y.2
  have hx1 : x ≠ 1 := fun h => hy1 (Subtype.ext h)
  have hx01 : ψ x 0 = ψ x 1 := by
    have := MonoidHom.mem_ker.1 hxker
    rw [hχ, MonoidHom.div_apply, div_eq_one] at this
    exact this
  have hsw : CFSG.RankThree.PartTwo.Census.swapGL (K := L) (n := 3) (by norm_num) ∈ U :=
    CFSG.RankThree.PartTwo.Census.swapGL_mem_statedSU h₀ (by norm_num)
  set sw : U := ⟨_, hsw⟩ with hswdef
  have hcomm : δ x * (sw : GL (Fin 3) L) = (sw : GL (Fin 3) L) * δ x := by
    apply Units.ext
    rw [Units.val_mul, Units.val_mul, ← hψδ, coe_diagHom, hswdef,
      CFSG.RankThree.PartTwo.Census.coe_swapGL]
    refine CFSG.RankThree.PartTwo.Census.diagonal_mul_swap fun i j hi hj => ?_
    have hi' : i = 0 ∨ i = 1 := by
      rcases i with ⟨_ | _ | _, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp at hi
    have hj' : j = 0 ∨ j = 1 := by
      rcases j with ⟨_ | _ | _, _⟩
      · exact Or.inl rfl
      · exact Or.inr rfl
      · simp at hj
    rcases hi' with rfl | rfl <;> rcases hj' with rfl | rfl <;> simp [hx01]
  set sU : U := P₀ * sw * P₀⁻¹ with hsU
  have hxs : (x : U) * sU = sU * (x : U) := by
    apply Subtype.ext
    have hxδ : ((x : U) : GL (Fin 3) L) = (P₀ : GL (Fin 3) L) * δ x * (P₀ : GL (Fin 3) L)⁻¹ := by
      rw [hδapply]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    simp only [hsU, Subgroup.coe_mul, Subgroup.coe_inv, hxδ]
    calc (P₀ : GL (Fin 3) L) * δ x * (P₀ : GL (Fin 3) L)⁻¹ *
          ((P₀ : GL (Fin 3) L) * (sw : GL (Fin 3) L) * (P₀ : GL (Fin 3) L)⁻¹)
        = (P₀ : GL (Fin 3) L) * (δ x * (sw : GL (Fin 3) L)) * (P₀ : GL (Fin 3) L)⁻¹ := by group
      _ = (P₀ : GL (Fin 3) L) * ((sw : GL (Fin 3) L) * δ x) * (P₀ : GL (Fin 3) L)⁻¹ := by
        rw [hcomm]
      _ = (P₀ : GL (Fin 3) L) * (sw : GL (Fin 3) L) * (P₀ : GL (Fin 3) L)⁻¹ *
          ((P₀ : GL (Fin 3) L) * δ x * (P₀ : GL (Fin 3) L)⁻¹) := by group
  have hsw2 : sw * sw = 1 := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, hswdef, CFSG.RankThree.PartTwo.Census.coe_swapGL,
      CFSG.RankThree.PartTwo.Census.one_add_mul_one_add
        (CFSG.RankThree.PartTwo.Census.swapBlock_mul_self (by norm_num))]
    rfl
  have hsU2 : sU * sU = 1 := by
    rw [hsU]
    calc P₀ * sw * P₀⁻¹ * (P₀ * sw * P₀⁻¹) = P₀ * (sw * sw) * P₀⁻¹ := by group
      _ = 1 := by rw [hsw2, mul_one, mul_inv_cancel]
  have hsw_ns : ∀ c : Lˣ, (sw : GL (Fin 3) L) ≠ GeneralLinearGroup.scalar (Fin 3) c := by
    intro c hc
    have h00 := congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L) 0 0) hc
    have h22 := congrArg (fun g : GL (Fin 3) L => (g : Matrix (Fin 3) (Fin 3) L) 2 2) hc
    simp only [hswdef, CFSG.RankThree.PartTwo.Census.coe_swapGL, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.add_apply, Matrix.one_apply_eq, Matrix.diagonal_apply_eq,
      CFSG.RankThree.PartTwo.Census.swapBlock, Matrix.of_apply] at h00 h22
    norm_num at h00 h22
    rw [CharTwo.two_eq_zero, ← h22] at h00
    exact zero_ne_one h00
  refine ⟨π (ε.symm x), ?_, ?_, π (ε.symm sU), ?_, ?_, ?_⟩
  · rw [← hAtmap]
    refine ⟨ε.symm x, ?_, rfl⟩
    obtain ⟨y, hy, hyx⟩ := x.2
    rw [← hyx]
    simpa using hy
  · intro h1
    have hxA : ε.symm x ∈ At := by
      obtain ⟨y, hy, hyx⟩ := x.2
      rw [← hyx]
      simpa using hy
    have := hAtinj _ hxA h1
    apply hx1
    apply Subtype.ext
    rw [Subgroup.coe_one, ← ε.apply_symm_apply (x : U), this, map_one]
  · intro h1
    have hmem : ε.symm sU ∈ N := by
      rw [← QuotientGroup.ker_mk' N]
      exact h1
    obtain ⟨c, -, -, hc⟩ := hmem
    apply hsw_ns c
    have hc' : ((sU : U) : GL (Fin 3) L) = GeneralLinearGroup.scalar (Fin 3) c := hc
    have h2 : (sw : GL (Fin 3) L) =
        (P₀ : GL (Fin 3) L)⁻¹ * ((sU : U) : GL (Fin 3) L) * (P₀ : GL (Fin 3) L) := by
      simp only [hsU, Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rw [h2, hc', (commute_scalar c (P₀ : GL (Fin 3) L)⁻¹).eq, mul_assoc, inv_mul_cancel,
      mul_one]
  · rw [← map_mul, ← map_mul, hsU2, map_one, map_one]
  · rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, hxs]

end PSU3

section Main

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2] (h : UnitaryFieldData 2 n K)

abbrev psu3T : Type := primeFormP h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)

theorem false_of_e2_psu3 {p e : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hn2 : 2 ≤ n)
    (hpq : p ∣ 2 ^ n + 1)
    (hshape : CFSG.RankThree.PartOne.K1214.SylowShape p 2 e (psu3T h)) (he : 2 ≤ e)
    (hout : OutPChain p (psu3T h))
    {P : Subgroup (MulAut (psu3T h))} (hP : IsPGroup p P) (hexp : ∀ y ∈ P, y ^ p = 1)
    (hcard : p ^ 3 ≤ Nat.card P) (h2b : H2bFor (psu3T h) p P)
    {α : MulAut (psu3T h)} (hαP : α ∈ P)
    (hαI : α ∉ (MulAut.conj : psu3T h →* MulAut (psu3T h)).range) : False := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hq : ¬(3 = 3 ∧ 2 ^ n = 2) := fun ⟨_, h2⟩ => by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  have hC := isPrimeFormGram_one (n := 3) (K := K)
  obtain ⟨-, -, -, -, hr5, hr6, -, hr8, -, -, -⟩ :=
    unitary_prime_form_full_semilinear_realization h hC le_rfl hq
  have hinj : Function.Injective (MulAut.conj : psu3T h →* MulAut (psu3T h)) :=
    conj_injective_of_simple (CFSG.RankThree.Classical.isSimpleGroup_primeFormP_one h le_rfl hq)
      (CFSG.RankThree.Classical.not_commute_primeFormP_one h le_rfl hq)
  obtain ⟨σ, ⟨A, hαA⟩, -⟩ := hr5 α
  have hσ1 : σ ≠ 1 := by
    intro hσ
    have hαD : α ∈ primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [← hr8, MonoidHom.mem_ker, hαA, hr6, hσ]
    have hcardQ := (unitary_full_diagonal_outer_order h (n := 3) le_rfl hq).2.2.1
    set D := primeFormD h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hD
    set I := (CFSG.ComponentClassification.OuterAutomorphisms.inner (psu3T h)).subgroupOf D
      with hI
    set ab : D ⧸ I := QuotientGroup.mk (⟨α, hαD⟩ : D) with hab
    have h1 : ab ^ p = 1 := by
      rw [hab, ← QuotientGroup.mk_pow]
      have : (⟨α, hαD⟩ : D) ^ p = 1 := Subtype.ext (by simpa using hexp α hαP)
      rw [this, QuotientGroup.mk_one]
    have h2 : orderOf ab ∣ Nat.gcd p (Nat.gcd 3 (2 ^ n + 1)) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (hcardQ ▸ orderOf_dvd_natCard ab)
    have h3 : Nat.gcd p (Nat.gcd 3 (2 ^ n + 1)) = 1 :=
      Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _)
        ((Nat.coprime_primes hp Nat.prime_three).2 (by omega))
    rw [h3, Nat.dvd_one, orderOf_eq_one_iff, hab, QuotientGroup.eq_one_iff] at h2
    exact hαI h2
  have hαp : (primeFormConjHom h _ A * primeFormFieldHom h hC σ) ^ p = 1 := by
    rw [← hαA]
    exact hexp α hαP
  obtain ⟨hσo, H, hH⟩ := CFSG.StandardType.RecipeFieldSpU.primeForm_conj_of_pow_eq_one h
    (d := 3) le_rfl hq hp hp2 A σ hσ1 hαp
  set β : MulAut (psu3T h) := primeFormConjHom h _ H with hβ
  set a : MulAut (psu3T h) := primeFormFieldHom h hC σ with ha
  have hαβ : α = β * a * β⁻¹ := by rw [hαA, hH]
  set P' := P.map (MulAut.congr (β⁻¹ : psu3T h ≃* psu3T h)).toMonoidHom with hP'
  have hcongr : ∀ ψ : MulAut (psu3T h),
      MulAut.congr (β⁻¹ : psu3T h ≃* psu3T h) ψ = β⁻¹ * ψ * β := fun ψ => by
    ext y
    simp [MulAut.congr_apply, MulAut.mul_apply]
  have haP' : a ∈ P' := ⟨α, hαP, by
    change MulAut.congr (β⁻¹ : psu3T h ≃* psu3T h) α = a
    rw [hcongr, hαβ]
    group⟩
  have hexp' : ∀ y ∈ P', y ^ p = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_pow, hexp z hz, map_one]
  have hP'p : IsPGroup p P' := hP.map _
  have hcard' : p ^ 3 ≤ Nat.card P' := by
    rw [hP', Subgroup.card_map_of_injective
      (MulAut.congr (β⁻¹ : psu3T h ≃* psu3T h)).injective]
    exact hcard
  have h2b' : H2bFor (psu3T h) p P' := h2b.map_congr (β⁻¹ : psu3T h ≃* psu3T h)
  have haI : a ∉ (MulAut.conj : psu3T h →* MulAut (psu3T h)).range := by
    rintro ⟨g, hg⟩
    apply hαI
    refine ⟨β g, ?_⟩
    rw [hαβ, ← hg]
    ext y
    simp [MulAut.mul_apply, MulAut.conj_apply]
  set A' := P' ⊓ (MulAut.conj : psu3T h →* MulAut (psu3T h)).range with hA'
  have hA'card : p ^ 2 ≤ Nat.card A' := sq_le_card_inf_inner hp hout hexp' hcard'
  obtain ⟨Q, hQ⟩ := exists_sylow_map_eq hP'p
  obtain ⟨eQ⟩ := hshape Q Q.isPGroup' Q.not_dvd_index
  set BT := A'.comap (MulAut.conj : psu3T h →* MulAut (psu3T h)) with hBT
  have hBTcard : p ^ 2 ≤ Nat.card BT := by
    rw [hBT, KF135Chev2Exc.card_comap_conj hinj inf_le_right]
    exact hA'card
  have hBTp : ∀ t ∈ BT, t ^ p = 1 := fun t ht => hinj (by
    rw [map_pow, map_one]
    exact hexp' _ ht.1)
  have hBTQ : ∀ t ∈ BT, t ∈ Q := fun t ht => mem_of_conj_mem Q (hBTp t ht) (hQ _ ht.1)
  have haBT : ∀ t ∈ BT, a t = t := fun t ht =>
    aut_trivial_mod_p_of_homocyclic (by omega) (Or.inr rfl) he eQ a (hQ a haP') (hexp' a haP')
      (hBTQ t ht) (hBTp t ht)
  have h₀ := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData h hp hp2 hσo
  have hbar := CFSG.RankThree.Classical.fixSubfield_unitaryFieldData_bar h hp hp2 hσo
  haveI : Finite (fixSubfield σ) := h₀.finite
  haveI : CharP (fixSubfield σ) 2 := h₀.charP
  set j := CFSG.RankThree.Classical.subfieldPSU h h₀ hbar 3 with hj
  have hjinj : Function.Injective j :=
    CFSG.RankThree.Classical.subfieldPSU_injective h h₀ hbar 3 (by norm_num)
  have hZ : ¬ p ∣ Nat.card (normOneScalars h
      (gramSU h ((1 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) 3) := by
    rw [CFSG.RankThree.Classical.card_normOneScalars_one h (n := 3) (by norm_num)]
    intro hd
    have := Nat.le_of_dvd (by norm_num) (hd.trans (Nat.gcd_dvd_left 3 _))
    omega
  have hrange := CFSG.RankThree.Classical.range_subfieldPSU h 3 h₀ hbar hp hσo hZ
  have hBTj : ∀ t ∈ BT, t ∈ j.range := fun t ht => by
    rw [hj, hrange]
    exact haBT t ht
  set B₀ := BT.comap j with hB₀
  have hB₀card : p ^ 2 ≤ Nat.card B₀ := by
    have hmap : B₀.map j = BT := Subgroup.map_comap_eq_self fun t ht => hBTj t ht
    rw [← Subgroup.card_map_of_injective hjinj, hmap]
    exact hBTcard
  have hQab : ∀ x ∈ (Q : Subgroup (psu3T h)), ∀ y ∈ (Q : Subgroup (psu3T h)), x * y = y * x :=
    fun x hx y hy => by
      have := KF135Chev2Exc.isMulCommutative_of_sylowShape hshape Q
      exact congrArg Subtype.val (this.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hB₀ab : CFSG.Open.IsElemAbelian p B₀ := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hjinj ?_)⟩⟩, fun x hx => hjinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hQab _ (hBTQ _ x.2) _ (hBTQ _ y.2)
    · rw [map_pow, map_one]
      exact hBTp _ hx
  obtain ⟨hpn, -⟩ := CFSG.RankThree.Classical.dvd_and_card_fixSubfield_unitary h hp hp2 hσo
  have hpq₀ : p ∣ 2 ^ (n / p) + 1 := by
    have hx := dvd_two_pow_add_one_iff.1 hpq
    rw [dvd_two_pow_add_one_iff]
    have hnp : n = n / p * p := (Nat.div_mul_cancel hpn).symm
    have hfermat : ((2 ^ (n / p) : ℕ) : ZMod p) ^ p = ((2 ^ (n / p) : ℕ) : ZMod p) :=
      ZMod.pow_card _
    rw [hnp, pow_mul, Nat.cast_pow, hfermat] at hx
    exact hx
  obtain ⟨t₀, ht₀B, ht₀1, s₀, hs₀1, hs₀2, hs₀t₀⟩ :=
    exists_involution_commute_psu3 h₀ hp (by omega) hpq₀ hB₀ab hB₀card
  have htBT : j t₀ ∈ BT := ht₀B
  have ht1 : j t₀ ≠ 1 := fun h1 => ht₀1 (hjinj (by rw [h1, map_one]))
  have hs1 : j s₀ ≠ 1 := fun h1 => hs₀1 (hjinj (by rw [h1, map_one]))
  have hs2 : j s₀ * j s₀ = 1 := by rw [← map_mul, hs₀2, map_one]
  have has : a (j s₀) = j s₀ := by
    have : j s₀ ∈ j.range := ⟨s₀, rfl⟩
    rw [hj, hrange] at this
    exact this
  have hts : j t₀ * j s₀ = j s₀ * j t₀ := by rw [← map_mul, ← map_mul, hs₀t₀]
  exact false_of_fixed_commute hp hinj hexp' h2b' haP' haI htBT.1 ht1 (haBT _ htBT) hs1 hs2 has
    hts

end Main

theorem two_le_factorization_two_pow_add_one {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpn : p ∣ n) (hpq : p ∣ 2 ^ n + 1) : 2 ≤ (2 ^ n + 1).factorization p := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨k, rfl⟩ := hpn
  have hk : p ∣ 2 ^ k + 1 := by
    have hx := dvd_two_pow_add_one_iff.1 hpq
    rw [dvd_two_pow_add_one_iff]
    rw [mul_comm p k, pow_mul, Nat.cast_pow, ZMod.pow_card] at hx
    exact hx
  have hx : ¬ p ∣ 2 ^ k := fun hd =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow hd))
  have hodd : Odd p := hp.odd_of_ne_two hp2
  have h := padicValNat.pow_add_pow hodd (x := 2 ^ k) (y := 1) hk hx hodd
  rw [one_pow, ← pow_mul, mul_comm k p] at h
  rw [Nat.factorization_def _ hp, h, padicValNat_self]
  have := one_le_padicValNat_of_dvd (by positivity) hk
  omega

section Family

variable {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)} {x u : MulAut S}
  {V : Subgroup (MulAut S)}

open CFSG.Assembly.RankThreeEven (projSU)

theorem false_of_kF135Hyp_projSU_three_e2 {n : ℕ} (hn : 1 ≤ n) (e : S ≃* projSU 3 2 n)
    (h : CFSG.RankThree.PartTwo.Sec13.KF135Proof.KF135Hyp S p P x u V) (hpn : p ∣ n)
    (hx : ((2 ^ n : ℕ) : ZMod p) = -1) : False := by
  have hp := h.prime
  have hp7 := h.seven_le
  have hp2 : p ≠ 2 := by omega
  haveI : Fact p.Prime := ⟨hp⟩
  have hn7 : p ≤ n := Nat.le_of_dvd (by omega) hpn
  have hn2 : 2 ≤ n := by omega
  by_cases hinn : P ≤ (MulAut.conj : S →* MulAut S).range
  · exact KF135Chev2Exc.false_of_rankLE2_inner h hinn
      ((rankLE2_projSU_three hn hp hp2).of_mulEquiv e.symm)
      (fun Q => CFSG.LocalAnalysis.RankFourTheoremC.isMulCommutative_sylow_of_mulEquiv e
        (isMulCommutative_sylow_projSU_three hn hp hp7) Q)
  obtain ⟨φ, hφP, hφI⟩ := SetLike.not_le_iff_exists.1 hinn
  set K := GaloisField 2 (2 * n)
  have hU : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, GaloisField.card 2 (2 * n) (by omega)⟩
  have hq : ¬(3 = 3 ∧ 2 ^ n = 2) := fun ⟨_, h2⟩ => by
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
    omega
  obtain ⟨e₁⟩ := (unitary_full_diagonal_outer_order hU (n := 3) le_rfl hq).1
  set eT : psu3T hU ≃* projSU 3 2 n :=
    e₁.trans (CFSG.RankThree.PartTwo.Sec4.projSUEquivUnitaryPSU 2 n hU).symm with heT
  set ε : S ≃* psu3T hU := e.trans eT.symm with hε
  have hne := CFSG.RankThree.PartTwo.Sec13.F135Last.two_pow_ne_of_two_le' hn2
  have hlie := CFSG.RankThree.PartTwo.Sec4.Census.lieModel_projSU (n := 3) (p := 2) (e := n)
    ⟨Nat.prime_two, by omega, le_refl 3, fun h => hne.1 (Prod.mk.inj h).2⟩
  have hout : OutPChain p (psu3T hU) := CFSG.RankThree.PartTwo.Sec13.F135Last.chain_psu eT hp hp7
    hlie (by norm_num) (CFSG.RankThree.PartTwo.Sec13.F135Last.not_dvd_gcd_of_lt (by norm_num)
      (by omega))
  have hX := CFSG.RankThree.PartTwo.Sec13.F135Last.stated_of_lieModel eT hlie (by norm_num)
  have hpq : p ∣ 2 ^ n + 1 := dvd_two_pow_add_one_iff.2 hx
  have h0 : 2 ^ n + 1 ≠ 0 := by positivity
  have he2 := two_le_factorization_two_pow_add_one hp hp2 hpn hpq
  have hshape := CFSG.RankThree.PartOne.K1214.sylowShape_of_psu3Model hp hp2 (by omega)
    (by omega) (Nat.ordProj_mul_ordCompl_eq_self (2 ^ n + 1) p).symm
    (Nat.not_dvd_ordCompl hp h0) hX
  set PT := P.map (MulAut.congr ε).toMonoidHom with hPT
  have hexpT : ∀ y ∈ PT, y ^ p = 1 := by
    rintro _ ⟨z, hz, rfl⟩
    rw [← map_pow, h.exponent z hz, map_one]
  have hcardT : p ^ 3 ≤ Nat.card PT := by
    rw [hPT, Subgroup.card_map_of_injective (MulAut.congr ε).injective]
    exact h.card
  have h2bT : H2bFor (psu3T hU) p PT := (show H2bFor S p P from h.h2b).map_congr ε
  refine false_of_e2_psu3 hU hp hp7 hn2 hpq hshape he2 hout (h.pgroup.map _) hexpT hcardT h2bT
    (α := MulAut.congr ε φ) ⟨φ, hφP, rfl⟩ ?_
  rintro ⟨g, hg⟩
  apply hφI
  refine ⟨ε.symm g, ?_⟩
  apply (MulAut.congr ε).injective
  rw [← hg]
  have := CFSG.ComponentClassification.OuterAutomorphisms.congr_conj ε (ε.symm g)
  rw [MulEquiv.apply_symm_apply] at this
  exact this

theorem false_of_kF135Hyp_projSU_three {n : ℕ} (hn : 1 ≤ n) (e : S ≃* projSU 3 2 n)
    (h : CFSG.RankThree.PartTwo.Sec13.KF135Proof.KF135Hyp S p P x u V) : False := by
  by_cases hE2 : p ∣ n ∧ ((2 ^ n : ℕ) : ZMod p) = -1
  · exact false_of_kF135Hyp_projSU_three_e2 hn e h hE2.1 hE2.2
  · exact false_of_kF135Hyp_projSU_three_of_not_e2 hn e h hE2

end Family

end CFSG.RankThree.PartTwo.Sec13.KF135Chev2
