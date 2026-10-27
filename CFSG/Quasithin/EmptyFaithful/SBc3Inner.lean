module

public import CFSG.Quasithin.EmptyFaithful.SBc2G27
public import CFSG.LocalAnalysis.ComponentInitial.QTNQRLinearUnitaryOuterDerived
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedImage

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner)
open scoped commutatorElement

namespace SBc3

section Outer

noncomputable def quotientEquivPSL {J : Type} [Group J] {n : ℕ} {K : Type} [Field K]
    (e : J ≃* ↥(StatedSL n K)) :
    J ⧸ Subgroup.center J ≃* Matrix.ProjectiveSpecialLinearGroup (Fin n) K :=
  QuotientGroup.congr _ _ (e.trans (specialLinearGroupEquivStatedSL n K).symm)
    (Subgroup.map_center_eq (e.trans (specialLinearGroupEquivStatedSL n K).symm))

theorem outer_comm_of_statedSL_two {J : Type} [Group J] [Group.IsPerfect J] {K : Type} [Field K]
    [Finite K] (e : J ≃* ↥(StatedSL 2 K)) : ∀ a b : Outer J, a * b = b * a := by
  intro a b
  refine CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_comp_injective J
    (quotientEquivPSL e) ?_
  rw [map_mul, map_mul, CFSG.LocalAnalysis.ComponentInitial.OuterDerived.outer_psl2_mul_comm]

theorem outer_comm_of_statedSL_three {J : Type} [Group J] [Group.IsPerfect J] {K : Type} [Field K]
    [Finite K] {m : ℕ} (hm : Odd m) (hK : Nat.card K = 2 ^ m) (e : J ≃* ↥(StatedSL 3 K)) :
    ∀ a b : Outer J, a * b = b * a := by
  have hmodel : StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 3 2 m := by
    refine ⟨⟨Nat.prime_two, ?_, by norm_num, ?_, ?_⟩, K, inferInstance, inferInstance, hK,
      ⟨(quotientEquivPSL e).trans (projectiveSpecialLinearGroupEquivStatedProj 3 K)⟩⟩
    · obtain ⟨k, rfl⟩ := hm
      omega
    · intro h
      simp at h
    · intro h
      simp at h
  have h1 := (CFSG.LocalAnalysis.ComponentInitial.OuterDerived.linear_perfect_cover_outer_derived_diagonal_bound
    J 3 2 m hmodel).2.1
  have hg : Nat.gcd 3 (2 ^ m - 1) = 1 := by
    obtain ⟨k, rfl⟩ := hm
    have h2 : 2 ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    have h3 : ¬ 3 ∣ 2 ^ (2 * k + 1) - 1 := by
      have : 1 ≤ 2 ^ (2 * k + 1) := Nat.one_le_two_pow
      omega
    exact (Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3)).symm
  rw [hg] at h1
  intro a b
  have hbot : commutator (Outer J) = ⊥ := Subgroup.card_eq_one.1 (Nat.dvd_one.1 h1)
  have hm : ⁅a, b⁆ ∈ commutator (Outer J) := by
    change ⁅a, b⁆ ∈ ⁅(⊤ : Subgroup (Outer J)), (⊤ : Subgroup (Outer J))⁆
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
  rw [hbot, Subgroup.mem_bot] at hm
  exact commutatorElement_eq_one_iff_mul_comm.1 hm

end Outer

section S3

variable {G : Type} [Group G] [Finite G]

theorem exists_commutator_perm_three : ∀ σ : Equiv.Perm (Fin 3), σ ^ 3 = 1 →
    ∃ a b : Equiv.Perm (Fin 3), σ = a * b * a⁻¹ * b⁻¹ := by
  decide +kernel

theorem pow_three_eq_one_of_odd_orderOf_perm {g : Equiv.Perm (Fin 3)} (hg : Odd (orderOf g)) :
    g ^ 3 = 1 := by
  have h6 : g ^ 6 = 1 := by
    have : ∀ x : Equiv.Perm (Fin 3), x ^ 6 = 1 := by decide +kernel
    exact this g
  have hm : g ^ orderOf g = 1 := pow_orderOf_eq_one g
  have hgcd := pow_gcd_eq_one.2 ⟨hm, h6⟩
  obtain ⟨d, hd⟩ : ∃ d, d = Nat.gcd (orderOf g) 6 := ⟨_, rfl⟩
  rw [← hd] at hgcd
  have hd1 : d ∣ 6 := hd ▸ Nat.gcd_dvd_right _ _
  have hd2 : Odd d := hd ▸ hg.of_dvd_nat (Nat.gcd_dvd_left _ _)
  have hd3 : d ∣ 3 := by
    have hle : d ≤ 6 := Nat.le_of_dvd (by norm_num) hd1
    rw [Nat.odd_iff] at hd2
    interval_cases d <;> omega
  obtain ⟨k, hk⟩ := hd3
  have h3 : g ^ 3 = g ^ (d * k) := congrArg (fun n => g ^ n) hk
  rw [pow_mul, hgcd, one_pow] at h3
  exact h3

theorem rho_eq_one_of_s3 {H : Subgroup G} {A : Type} [Group A] (hA : ∀ a b : A, a * b = b * a)
    (ψ : ↥H →* Equiv.Perm (Fin 3)) (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = (pCoreOf 2 H).subgroupOf H) (ρ : ↥H →* A) {y : G} (hy : y ∈ H)
    (hyo : Odd (orderOf y)) : ρ ⟨y, hy⟩ = 1 := by
  classical
  have hord : Odd (orderOf (⟨y, hy⟩ : ↥H)) := by rwa [Subgroup.orderOf_mk]
  have hψ3 : ψ ⟨y, hy⟩ ^ 3 = 1 :=
    pow_three_eq_one_of_odd_orderOf_perm (hord.of_dvd_nat (orderOf_map_dvd ψ _))
  obtain ⟨a, b, hab⟩ := exists_commutator_perm_three _ hψ3
  obtain ⟨a', rfl⟩ := hψs a
  obtain ⟨b', rfl⟩ := hψs b
  obtain ⟨k, hkdef⟩ : ∃ k : ↥H, k = a' * b' * a'⁻¹ * b'⁻¹ := ⟨_, rfl⟩
  have hρk : ρ k = 1 := by
    rw [hkdef, map_mul, map_mul, map_mul, map_inv, map_inv, hA (ρ a') (ρ b')]
    group
  have hr : k⁻¹ * ⟨y, hy⟩ ∈ ψ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hkdef, map_mul, map_mul, map_mul, map_inv, map_inv,
      ← hab]
    group
  rw [hψk, Subgroup.mem_subgroupOf] at hr
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (k⁻¹ * ⟨y, hy⟩) ^ 2 ^ j = 1 := by
    obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 H : IsPGroup 2 ↥(pCoreOf 2 H))
      ⟨((k⁻¹ * ⟨y, hy⟩ : ↥H) : G), hr⟩
    refine ⟨j, Subtype.ext ?_⟩
    have := congrArg Subtype.val hj
    simpa using this
  have hyk : (⟨y, hy⟩ : ↥H) = k * (k⁻¹ * ⟨y, hy⟩) := by group
  have h1 : ρ ⟨y, hy⟩ = ρ (k⁻¹ * ⟨y, hy⟩) := by
    have := congrArg ρ hyk
    rwa [map_mul, hρk, one_mul] at this
  have h2 : ρ ⟨y, hy⟩ ^ 2 ^ j = 1 := by
    rw [h1, ← map_pow, hj, map_one]
  have hordy : Odd (orderOf (ρ ⟨y, hy⟩)) :=
    hord.of_dvd_nat (orderOf_map_dvd ρ _)
  have h3 : orderOf (ρ ⟨y, hy⟩) ∣ 2 ^ j := orderOf_dvd_of_pow_eq_one h2
  have hcop : Nat.Coprime (orderOf (ρ ⟨y, hy⟩)) (2 ^ j) :=
    Nat.Coprime.pow_right j (Nat.coprime_two_left.2 hordy).symm
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop h3)

end S3

section Action

variable {G : Type} [Group G] [Finite G] {U L H I : Subgroup G}

omit [Finite G] in
theorem star_mem_normalizer (hIU : I ≤ Subgroup.normalizer (U : Set G)) (hLI : L ≤ I)
    (hIL : I ≤ Subgroup.normalizer (L : Set G)) {a : MulAut ↥U} (ha : a ∈ autOn I U) :
    a ∈ Subgroup.normalizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) :=
  autOn_le_normalizer_autOn hIU (hLI.trans hIU) hIL ha

noncomputable def actStar (hIU : I ≤ Subgroup.normalizer (U : Set G)) (hLI : L ≤ I)
    (hIL : I ≤ Subgroup.normalizer (L : Set G)) (hHI : H ≤ I) : ↥H →* MulAut ↥(autOn L U) :=
  (autOn L U).normalizerMonoidHom.comp
    ((Setup.rho U H (hHI.trans hIU)).codRestrict
      (Subgroup.normalizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)))
      fun h => star_mem_normalizer hIU hLI hIL
        (autOn_le_autOn U hHI ((Setup.mem_autOn_self_iff (hHI.trans hIU)).mpr ⟨h, rfl⟩)))

omit [Finite G] in
theorem coe_actStar (hIU : I ≤ Subgroup.normalizer (U : Set G)) (hLI : L ≤ I)
    (hIL : I ≤ Subgroup.normalizer (L : Set G)) (hHI : H ≤ I) (h : ↥H) (m : ↥(autOn L U)) :
    ((actStar hIU hLI hIL hHI h m : ↥(autOn L U)) : MulAut ↥U) =
      Setup.rho U H (hHI.trans hIU) h * (m : MulAut ↥U) * (Setup.rho U H (hHI.trans hIU) h)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe (autOn L U) _ m

theorem exists_inner_of_odd (hIU : I ≤ Subgroup.normalizer (U : Set G)) (hLI : L ≤ I)
    (hIL : I ≤ Subgroup.normalizer (L : Set G)) (hHI : H ≤ I)
    (hOut : ∀ a b : Outer ↥(autOn L U), a * b = b * a)
    (ψ : ↥H →* Equiv.Perm (Fin 3)) (hψs : Function.Surjective ψ)
    (hψk : ψ.ker = (pCoreOf 2 H).subgroupOf H) {y : G} (hy : y ∈ H) (hyo : Odd (orderOf y)) :
    ∃ n ∈ autOn L U, ∀ m ∈ autOn L U,
      Setup.rho U H (hHI.trans hIU) ⟨y, hy⟩ * m * (Setup.rho U H (hHI.trans hIU) ⟨y, hy⟩)⁻¹ =
        n * m * n⁻¹ := by
  let ρ : ↥H →* Outer ↥(autOn L U) :=
    (QuotientGroup.mk' (inner ↥(autOn L U))).comp (actStar hIU hLI hIL hHI)
  have h1 : ρ ⟨y, hy⟩ = 1 := rho_eq_one_of_s3 hOut ψ hψs hψk ρ hy hyo
  have h2 : actStar hIU hLI hIL hHI ⟨y, hy⟩ ∈ inner ↥(autOn L U) :=
    (QuotientGroup.eq_one_iff _).mp h1
  obtain ⟨n, hn⟩ := h2
  refine ⟨(n : MulAut ↥U), n.2, fun m hm => ?_⟩
  have h3 := congrArg (fun a : MulAut ↥(autOn L U) => ((a ⟨m, hm⟩ : ↥(autOn L U)) : MulAut ↥U)) hn
  simp only [MulAut.conj_apply, coe_actStar] at h3
  exact h3.symm

end Action

section Star

variable {G : Type} [Group G] [Finite G]

theorem card_OTwoQuot_autOn {Yp U : Subgroup G} (hYU : Yp ≤ Subgroup.normalizer (U : Set G))
    (hcard : Nat.card (OTwoQuot Yp) = 3) (hodd : oTwoUpper Yp = Yp) (hne : autOn Yp U ≠ ⊥) :
    Nat.card (OTwoQuot (autOn Yp U)) = 3 := by
  have hp3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set A : Subgroup (MulAut ↥U) := autOn Yp U with hA
  let π : ↥Yp →* ↥A := S153D.autOnHom hYU
  have hπs : Function.Surjective π := S153D.autOnHom_surjective hYU
  have hmap : CFSG.Open.pCore 2 ↥Yp ≤ (CFSG.Open.pCore 2 ↥A).comap π := by
    have hK : IsPGroup 2 ((CFSG.Open.pCore 2 ↥Yp).map π) :=
      (CFSG.LieType.BorelTits.pCore_isPGroup 2 : IsPGroup 2 (CFSG.Open.pCore 2 ↥Yp)).map π
    have hn : ((CFSG.Open.pCore 2 ↥Yp).map π).Normal :=
      (CFSG.LieType.BorelTits.pCore_normal 2 : (CFSG.Open.pCore 2 ↥Yp).Normal).map π hπs
    have := CFSG.LieType.BorelTits.le_pCore 2 hn hK
    exact fun x hx => this ⟨x, hx, rfl⟩
  let f : OTwoQuot Yp →* OTwoQuot A := QuotientGroup.map _ _ π hmap
  have hfs : Function.Surjective f := by
    intro z
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective z
    obtain ⟨y, rfl⟩ := hπs a
    exact ⟨QuotientGroup.mk y, rfl⟩
  have hdvd : Nat.card (OTwoQuot A) ∣ Nat.card (OTwoQuot Yp) :=
    Subgroup.card_dvd_of_surjective hfs
  rw [hcard] at hdvd
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exfalso
    apply hne
    have hsub : Subsingleton (OTwoQuot A) := (Nat.card_eq_one_iff_unique.mp h1).1
    have hA2 : ∀ a : ↥A, ∃ k : ℕ, a ^ 2 ^ k = 1 := by
      intro a
      have hmem : a ∈ CFSG.Open.pCore 2 ↥A :=
        (QuotientGroup.eq_one_iff a).mp (Subsingleton.elim _ _)
      obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
        IsPGroup 2 (CFSG.Open.pCore 2 ↥A)) ⟨a, hmem⟩
      exact ⟨k, congrArg Subtype.val hk⟩
    have hker : Yp ≤ π.ker.map Yp.subtype := by
      calc Yp = oTwoUpper Yp := hodd.symm
        _ ≤ _ := by
          rw [oTwoUpper, Subgroup.closure_le]
          rintro x ⟨hx, hxo⟩
          refine ⟨⟨x, hx⟩, (show (⟨x, hx⟩ : ↥Yp) ∈ π.ker from ?_), rfl⟩
          rw [MonoidHom.mem_ker]
          obtain ⟨k, hk⟩ := hA2 (π ⟨x, hx⟩)
          have hordo : Odd (orderOf (π ⟨x, hx⟩)) := by
            refine hxo.of_dvd_nat ((orderOf_map_dvd π _).trans ?_)
            rw [Subgroup.orderOf_mk]
          have hd : orderOf (π ⟨x, hx⟩) ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk
          exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd
            (Nat.Coprime.pow_right k (Nat.coprime_two_left.2 hordo).symm) hd)
    refine eq_bot_iff.mpr fun φ hφ => ?_
    obtain ⟨a, ha⟩ := hπs ⟨φ, hφ⟩
    obtain ⟨z, hz, hza⟩ := hker a.2
    have hza' : z = a := Subtype.ext hza
    rw [hza'] at hz
    have : (π a : MulAut ↥U) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hz)
      simpa using this
    rw [Subgroup.mem_bot]
    have h5 : ((π a : ↥A) : MulAut ↥U) = φ := congrArg Subtype.val ha
    rw [← h5]
    exact this
  · exact h3

end Star

section Lift

variable {G : Type} [Group G]

theorem mem_of_autOn_mem {I U MI : Subgroup G} (hUN : I ≤ Subgroup.normalizer (U : Set G))
    (hMI : MI ≤ I) (hcent : I ⊓ Subgroup.centralizer (U : Set G) ≤ MI) {x : G} (hx : x ∈ I)
    (h : Setup.rho U I hUN ⟨x, hx⟩ ∈ autOn MI U) : x ∈ MI := by
  obtain ⟨m, hmM, hm⟩ := (Setup.mem_autOn_iff_rho hUN hMI).mp h
  have h1 : Setup.rho U I hUN (⟨x, hx⟩ * m⁻¹) = 1 := by
    rw [map_mul, map_inv, hm, mul_inv_cancel]
  have h2 : x * (m : G)⁻¹ ∈ Subgroup.centralizer (U : Set G) :=
    (Setup.rho_eq_one_iff hUN (⟨x, hx⟩ * m⁻¹)).mp h1
  have h3 : x * (m : G)⁻¹ ∈ I ⊓ Subgroup.centralizer (U : Set G) :=
    ⟨I.mul_mem hx (I.inv_mem m.2), h2⟩
  have e : x = (x * (m : G)⁻¹) * m := by group
  rw [e]
  exact MI.mul_mem (hcent h3) hmM

end Lift

section Core

variable {G : Type} [Group G] [Finite G]

theorem inv_mul_mem_centralizer_of_inner {Γ : Type*} [Group Γ] {A : Subgroup Γ} {z n : Γ}
    (h : ∀ m ∈ A, z * m * z⁻¹ = n * m * n⁻¹) : n⁻¹ * z ∈ Subgroup.centralizer (A : Set Γ) := by
  refine Subgroup.mem_centralizer_iff.mpr fun m hm => ?_
  have h1 := h m hm
  calc m * (n⁻¹ * z) = n⁻¹ * (n * m * n⁻¹) * z := by group
    _ = n⁻¹ * (z * m * z⁻¹) * z := by rw [h1]
    _ = (n⁻¹ * z) * m := by group

theorem inner_core {U L I Yp S M : Subgroup G}
    (hS : IsSylowTwoOf S I) (hLI : L ≤ I) (hIU : I ≤ Subgroup.normalizer (U : Set G))
    (hIL : I ≤ Subgroup.normalizer (L : Set G)) (hYI : Yp ≤ I)
    (hSN : S ≤ Subgroup.normalizer (Yp : Set G))
    (hgen : ∀ z ∈ M ⊓ I, orderOf z = 3 → z ∈ Yp) (hYpM : Yp ≤ M ⊓ I)
    (hstar : Subgroup.normalizer (autOn Yp U : Set (MulAut ↥U)) ⊓ autOn I U = autOn (M ⊓ I) U)
    (hcent : I ⊓ Subgroup.centralizer (U : Set G) ≤ M ⊓ I) (hLnM : ¬ L ≤ M ⊓ I)
    (hodd : oTwoUpper Yp = Yp) (hcard3 : Nat.card (OTwoQuot Yp) = 3)
    (hpow : ∀ y ∈ Yp, Odd (orderOf y) → y ^ 3 = 1) (hne : autOn Yp U ≠ ⊥)
    (hinner : ∀ (y : G) (hy : y ∈ Yp), Odd (orderOf y) →
      ∃ n ∈ autOn L U, ∀ m ∈ autOn L U,
        Setup.rho U I hIU ⟨y, hYI hy⟩ * m * (Setup.rho U I hIU ⟨y, hYI hy⟩)⁻¹ = n * m * n⁻¹) :
    Yp ≤ L := by
  classical
  have hSI : S ≤ I := hS.1
  have hYU : Yp ≤ Subgroup.normalizer (U : Set G) := hYI.trans hIU
  have hLU : L ≤ Subgroup.normalizer (U : Set G) := hLI.trans hIU
  have hgenYp : ∀ {C : Subgroup G}, (∀ y ∈ Yp, Odd (orderOf y) → y ∈ C) → Yp ≤ C := fun {C} hC => by
    calc Yp = oTwoUpper Yp := hodd.symm
      _ ≤ C := by
        rw [oTwoUpper, Subgroup.closure_le]
        rintro x ⟨hx, ho⟩
        exact hC x hx ho
  have hord3 : ∀ y ∈ Yp, Odd (orderOf y) → y = 1 ∨ orderOf y = 3 := by
    intro y hy ho
    have hd : orderOf y ∣ 3 := orderOf_dvd_of_pow_eq_one (hpow y hy ho)
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h3
    · exact Or.inl (orderOf_eq_one_iff.mp h1)
    · exact Or.inr h3
  have hYsI : autOn Yp U ≤ autOn I U := autOn_le_autOn U hYI
  have hLsI : autOn L U ≤ autOn I U := autOn_le_autOn U hLI
  have hIsL : autOn I U ≤ Subgroup.normalizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) :=
    autOn_le_normalizer_autOn hIU hLU hIL
  have hSyl : IsSylowTwoOf (autOn S U) (autOn I U) := Setup.isSylowTwoOf_autOn hS hIU
  have hSsN : autOn S U ≤ Subgroup.normalizer ((autOn Yp U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) :=
    autOn_le_normalizer_autOn (hSI.trans hIU) hYU hSN
  have hSLs : IsSylowTwoOf (autOn S U ⊓ autOn L U) (autOn L U) :=
    A4.isSylowTwoOf_inf_normal hSyl hLsI hIsL
  have hcardS : Nat.card (OTwoQuot (autOn Yp U)) = 3 := card_OTwoQuot_autOn hYU hcard3 hodd hne
  have hin : autOn Yp U ≤ autOn L U ⊔ Subgroup.centralizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
    have hCst : Yp ≤ Setup.rhoPreimage U I hIU (autOn L U ⊔ Subgroup.centralizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U))) := by
      refine hgenYp fun y hy ho => ?_
      obtain ⟨n, hn, hrel⟩ := hinner y hy ho
      refine ⟨hYI hy, ?_⟩
      have hc := inv_mul_mem_centralizer_of_inner (A := autOn L U) hrel
      have e : Setup.rho U I hIU ⟨y, hYI hy⟩ =
          (n : MulAut ↥U) * (n⁻¹ * Setup.rho U I hIU ⟨y, hYI hy⟩) := by
        group
      rw [e]
      exact Subgroup.mul_mem_sup hn hc
    intro z hz
    obtain ⟨p, hpY, rfl⟩ := (Setup.mem_autOn_iff_rho hIU hYI).mp hz
    exact Setup.mem_rhoPreimage.mp (hCst hpY)
  by_cases hcase : ∀ (y : G) (hy : y ∈ Yp), orderOf y = 3 →
      Setup.rho U I hIU ⟨y, hYI hy⟩ ∈
        Subgroup.centralizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U))
  ·
    exfalso
    have hCst : Yp ≤ Setup.rhoPreimage U I hIU
        (Subgroup.centralizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U))) := by
      refine hgenYp fun y hy ho => ?_
      rcases hord3 y hy ho with h1 | h3
      · rw [h1]
        exact Subgroup.one_mem _
      · exact ⟨hYI hy, hcase y hy h3⟩
    have hYsC : autOn Yp U ≤
        Subgroup.centralizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
      intro z hz
      obtain ⟨p, hpY, rfl⟩ := (Setup.mem_autOn_iff_rho hIU hYI).mp hz
      exact Setup.mem_rhoPreimage.mp (hCst hpY)
    have hLsN : autOn L U ≤
        Subgroup.normalizer ((autOn Yp U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
      intro l hl
      have hlc : l ∈ Subgroup.centralizer
          ((autOn Yp U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
        rw [Subgroup.mem_centralizer_iff]
        intro z hz
        exact (Subgroup.mem_centralizer_iff.mp (hYsC hz) l hl).symm
      exact Subgroup.centralizer_le_normalizer _ hlc
    refine hLnM (S153D.le_of_autOn_le hIU hLI inf_le_right hcent ?_)
    rw [← hstar]
    exact le_inf hLsN hLsI
  · push Not at hcase
    obtain ⟨y, hyY, hy3, hyC⟩ := hcase
    have hyo : Odd (orderOf y) := by rw [hy3]; decide
    obtain ⟨n, hn, hrel⟩ := hinner y hyY hyo
    set ρy : MulAut ↥U := Setup.rho U I hIU ⟨y, hYI hyY⟩ with hρy
    have hc₁ : n⁻¹ * ρy ∈ Subgroup.centralizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) :=
      inv_mul_mem_centralizer_of_inner (A := autOn L U) hrel
    have hρyY : ρy ∈ autOn Yp U :=
      (Setup.mem_autOn_iff_rho hIU hYI).mpr ⟨⟨y, hYI hyY⟩, hyY, rfl⟩
    have hy3' : y ^ 3 = 1 := by
      have := pow_orderOf_eq_one y
      rwa [hy3] at this
    have hρy3 : ρy ^ 3 = 1 := by
      rw [hρy, ← map_pow]
      have : (⟨y, hYI hyY⟩ : ↥I) ^ 3 = 1 := Subtype.ext hy3'
      rw [this, map_one]
    have hρy1 : ρy ≠ 1 := fun h => hyC (h ▸ Subgroup.one_mem _)
    have hcN := SBc.mem_normalizer_of_projection hSyl hYsI hSsN hin hSLs hcardS hρyY hρy3 hρy1 hn hc₁
      (mul_inv_cancel_left n ρy)
    have hnI : n ∈ autOn I U := hLsI hn
    have hc₁I : n⁻¹ * ρy ∈ autOn I U := (autOn I U).mul_mem ((autOn I U).inv_mem hnI) (hYsI hρyY)
    have hc₁M : n⁻¹ * ρy ∈ autOn (M ⊓ I) U := by
      rw [← hstar]
      exact ⟨hcN, hc₁I⟩
    have hρyM : ρy ∈ autOn (M ⊓ I) U :=
      (Setup.mem_autOn_iff_rho hIU (inf_le_right : M ⊓ I ≤ I)).mpr
        ⟨⟨y, hYI hyY⟩, hYpM hyY, rfl⟩
    have hnM : n ∈ autOn (M ⊓ I) U := by
      have e : n = ρy * (n⁻¹ * ρy)⁻¹ := by group
      rw [e]
      exact (autOn (M ⊓ I) U).mul_mem hρyM ((autOn (M ⊓ I) U).inv_mem hc₁M)
    obtain ⟨l, hlL, hl⟩ := (Setup.mem_autOn_iff_rho hIU hLI).mp hn
    have hlM : (l : G) ∈ M ⊓ I :=
      mem_of_autOn_mem hIU inf_le_right hcent l.2 (by
        have h' : Setup.rho U I hIU ⟨(l : G), l.2⟩ = n := hl
        rw [h']
        exact hnM)
    have h3n : 3 ∣ orderOf n := by
      by_contra h3
      have hcomm : Commute n (n⁻¹ * ρy) := Subgroup.mem_centralizer_iff.mp hc₁ n hn
      have hn3 : n ^ 3 ∈ Subgroup.centralizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
        have h1 : (n * (n⁻¹ * ρy)) ^ 3 = 1 := by
          rw [mul_inv_cancel_left]
          exact hρy3
        rw [hcomm.mul_pow] at h1
        have h2 : n ^ 3 = ((n⁻¹ * ρy) ^ 3)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [h2]
        exact Subgroup.inv_mem _ (Subgroup.pow_mem _ hc₁ 3)
      have hn_mem : n ∈ Subgroup.centralizer ((autOn L U : Subgroup (MulAut ↥U)) : Set (MulAut ↥U)) := by
        have hcop : Nat.Coprime 3 (orderOf n) := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 h3
        rcases Nat.lt_or_ge 1 (orderOf n) with h1 | h1
        · obtain ⟨m, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop h1
          have e : n ^ (3 * m) = n := by rw [← pow_mod_orderOf, hm.2, pow_one]
          rw [← e, pow_mul]
          exact Subgroup.pow_mem _ hn3 m
        · have h0 : orderOf n = 1 := by
            have := orderOf_pos n
            omega
          rw [orderOf_eq_one_iff.mp h0]
          exact Subgroup.one_mem _
      apply hyC
      have e : ρy = n * (n⁻¹ * ρy) := by group
      rw [e]
      exact Subgroup.mul_mem _ hn_mem hc₁
    have h3l : 3 ∣ orderOf (l : G) := by
      refine h3n.trans ?_
      have h1 : orderOf (Setup.rho U I hIU l) ∣ orderOf l := orderOf_map_dvd _ l
      have h2 : Setup.rho U I hIU l = n := hl
      rw [h2, ← Subgroup.orderOf_coe] at h1
      exact h1
    have ha3 : orderOf ((l : G) ^ (orderOf (l : G) / 3)) = 3 :=
      orderOf_pow_orderOf_div (orderOf_pos _).ne' h3l
    have haY : (l : G) ^ (orderOf (l : G) / 3) ∈ Yp := hgen _ ((M ⊓ I).pow_mem hlM _) ha3
    have haL : (l : G) ^ (orderOf (l : G) / 3) ∈ L := L.pow_mem hlL _
    refine hgenYp fun b hb ho => ?_
    exact SBc2.mem_of_order_three hcard3 hYI hLI hIL haY ha3 haL hb (hpow b hb ho)

end Core

section Main

theorem input27Inner_holds (h113 : StageLemma14113) : Input27Inner := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hIL _hrank hcases
  classical
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.ctx.hyp
  have hLI' : L ∈ cComp I := S153D.mem_cComp_of_mem_cComp_thompsonJ c.conc.1
  have hLI : L ≤ I := le_of_mem_cComp hLI'
  have hS : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hSI : Sgp153 T V₁ ≤ I := hS.1
  have hHI : Yp ⊔ Sgp153 T V₁ ≤ I := c.ctx.inH.1.1
  have hYI : Yp ≤ I := le_sup_left.trans hHI
  have hIU : I ≤ Subgroup.normalizer (UI153 T I : Set G) := le_normalizer_conjClosure _ I
  have hLq : CFSG.IsQuasisimple ↥(autOn L (UI153 T I)) := c.conc.2.2.2.2.1
  have : Group.IsPerfect ↥(autOn L (UI153 T I)) := hLq.1
  have hOut : ∀ a b : Outer ↥(autOn L (UI153 T I)), a * b = b * a := by
    rcases hcases with ⟨n, K, _, _, hK, ⟨e⟩⟩ | ⟨m, hm, K, _, _, hK, ⟨e⟩⟩
    · exact outer_comm_of_statedSL_two e
    · exact outer_comm_of_statedSL_three hm hK e
  obtain ⟨ψ, hψs, hψk⟩ := c.facts.s3
  have hnorm : I ⊓ Subgroup.normalizer (Yp : Set G) = M ⊓ I := c.facts.norm_eq
  have hSN : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := by
    intro s' hs'
    have hsM : s' ∈ M ⊓ I := ⟨hh.hyp.T_le hs'.1, hSI hs'⟩
    rw [← hnorm] at hsM
    exact hsM.2
  have htheta : Yp = thetaOf (M ⊓ I) := c.facts.theta
  have hgen : ∀ z ∈ M ⊓ I, orderOf z = 3 → z ∈ Yp := fun z hz hzo => by
    rw [htheta]
    exact Subgroup.subset_closure ⟨hz, hzo⟩
  have hYpM : Yp ≤ M ⊓ I := by
    rw [← hnorm]
    exact le_inf hYI Subgroup.le_normalizer
  obtain ⟨y₀, hy₀Y, hy₀3⟩ : ∃ y ∈ Yp, orderOf y = 3 := by
    obtain ⟨E, hEY, hE, hE9⟩ := CFSG.SectionRank.exists_pRank (by norm_num : 1 < 3) Yp
    rw [c.ctx.rank] at hE9
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := ↥E) 3 (by rw [hE9]; norm_num)
    exact ⟨(z : G), hEY z.2, by rw [Subgroup.orderOf_coe, hz]⟩
  have hcard3 : Nat.card (OTwoQuot Yp) = 3 := SBc2.card_OTwoQuot_eq_three h113 hh c.ctx.rank hy₀Y hy₀3
  refine inner_core hS hLI hIU hIL hYI hSN hgen hYpM c.facts.star_norm c.facts.cent_le c.conc.2.1
    hh.oTwoUpper_eq hcard3
    (fun y hy ho => SBc2.pow_three_eq_one_of_odd h113 hh.hyp (hh.Yp_le_Y153 hy) ho)
    c.facts.star_ne ?_
  intro y hy ho
  exact exists_inner_of_odd hIU hLI hIL hHI hOut ψ hψs hψk (Subgroup.mem_sup_left hy) ho

end Main

end SBc3

end CFSG.Quasithin
