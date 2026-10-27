module

public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
public import CFSG.RankThree.PartTwo.Sec14.Notation
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.QuasisimpleOfCentralExtension
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.CharacterTheory.Semidihedral.Local.CoprimeCentralizerQuotient
import CFSG.RankThree.GroupTheory.SteinbergBYHyperplaneResidual
import CFSG.RankThree.PartOne.S10.EmbeddingFixedResidual
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec14

section J2

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem map_subtype_center_eq (P : Subgroup X) :
    (Subgroup.center ↥P).map P.subtype = P ⊓ Subgroup.centralizer (P : Set X) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    have := Subgroup.mem_center_iff.mp hy ⟨z, hz⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxP, hxC⟩
    refine ⟨⟨x, hxP⟩, Subgroup.mem_center_iff.mpr fun z => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hxC z z.2

theorem j2_sylow_facts (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) :
    Nat.card ↥((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) = 3 ∧
      (∀ g : X, conjugate ((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) g ≤
          P → conjugate ((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) g =
            (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) ∧
      Sec4.IsExtOf (Subgroup.centralizer
          (((P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) : Subgroup X) :
            Set X))
        (alternatingGroup (Fin 6)) (Multiplicative (ZMod 3)) := by
  obtain ⟨⟨hHeis, -⟩, -, ⟨hwc, hext, -⟩, -⟩ := h415 X hX P _ rfl _ rfl
  refine ⟨?_, hwc, hext⟩
  rw [← map_subtype_center_eq, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact hHeis.1.2.2.2

omit [Finite X] in
theorem coe_sylow_smul_eq_map {p : ℕ} (P : Sylow p X) (g : X) :
    ((g • P : Sylow p X) : Subgroup X) = (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def]
  rfl

theorem j2_zpowers_eq (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {z : X}
    (hz1 : z ≠ 1) (hzP : z ∈ (P : Subgroup X))
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    Subgroup.zpowers z = (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) := by
  obtain ⟨P', hzP', hP'z⟩ := hz
  obtain ⟨-, hwc, -⟩ := j2_sylow_facts h415 hX P
  obtain ⟨h3', -, -⟩ := j2_sylow_facts h415 hX P'
  set Z := (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X) with hZ
  set Z' := (P' : Subgroup X) ⊓ Subgroup.centralizer ((P' : Subgroup X) : Set X) with hZ'
  have hzZ' : Subgroup.zpowers z ≤ Z' :=
    Subgroup.zpowers_le.mpr ⟨hzP', Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hP'z hy)⟩
  have hzeq : Subgroup.zpowers z = Z' := by
    refine Subgroup.eq_of_le_of_card_ge hzZ' ?_
    have hdvd : Nat.card (Subgroup.zpowers z) ∣ 3 := h3' ▸ Subgroup.card_dvd_of_le hzZ'
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
    · exfalso
      apply hz1
      rw [Nat.card_zpowers, orderOf_eq_one_iff] at h1
      exact h1
    · rw [h3, h3']
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X P P'
  have hP' : (P' : Subgroup X) = (P : Subgroup X).map (MulAut.conj g).toMonoidHom := by
    rw [← hg, coe_sylow_smul_eq_map]
  have hZ'Z : Z' = conjugate Z g⁻¹ := by
    rw [hZ', hP', conjugate, inv_inv, hZ, Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective,
      map_conj_centralizer]
  have hle : conjugate Z g⁻¹ ≤ P := by
    rw [← hZ'Z, ← hzeq]
    exact Subgroup.zpowers_le.mpr hzP
  rw [hzeq, hZ'Z, hwc g⁻¹ hle]

theorem j2_zpowers_eq_of_mem (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {E : Subgroup X}
    (hE : IsPGroup 3 E) {z₁ z₂ : X} (h₁E : z₁ ∈ E) (h₂E : z₂ ∈ E) (h₁ : z₁ ≠ 1) (h₂ : z₂ ≠ 1)
    (hz₁ : ∃ P' : Sylow 3 X, z₁ ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z₁} : Set X))
    (hz₂ : ∃ P' : Sylow 3 X, z₂ ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z₂} : Set X)) :
    Subgroup.zpowers z₁ = Subgroup.zpowers z₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hEP⟩ := hE.exists_le_sylow
  rw [j2_zpowers_eq h415 hX P h₁ (hEP h₁E) hz₁, j2_zpowers_eq h415 hX P h₂ (hEP h₂E) hz₂]

theorem alternatingGroup_six_isPerfect : Group.IsPerfect (alternatingGroup (Fin 6)) := by
  have hs : IsSimpleGroup (alternatingGroup (Fin 6)) :=
    alternatingGroup.isSimpleGroup (by norm_num)
  have hc : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  refine ⟨?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (alternatingGroup (Fin 6)))
    with h | h
  · exfalso
    have htop : (⊤ : Subgroup (alternatingGroup (Fin 6))) ≤
        Subgroup.centralizer ((⊤ : Subgroup (alternatingGroup (Fin 6))) : Set _) := by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact h
    rw [Subgroup.coe_top, Subgroup.centralizer_univ, hc, top_le_iff] at htop
    have : Nontrivial (alternatingGroup (Fin 6)) := hs.toNontrivial
    exact (bot_ne_top htop).elim
  · exact h

theorem center_eq_bot_of_mulEquiv_alternating_six {Q : Type*} [Group Q]
    (e : Q ≃* alternatingGroup (Fin 6)) : Subgroup.center Q = ⊥ := by
  have hc : Subgroup.center (alternatingGroup (Fin 6)) = ⊥ :=
    alternatingGroup.center_eq_bot (by norm_num)
  refine eq_bot_iff.mpr fun x hx => ?_
  have hex : e x ∈ Subgroup.center (alternatingGroup (Fin 6)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨y', rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, (Subgroup.mem_center_iff.mp hx y')]
  rw [hc, Subgroup.mem_bot] at hex
  rw [Subgroup.mem_bot]
  exact e.injective (by rw [hex, map_one])

theorem j2_centralizer_residual_quasisimple (h415 : Sec4.Item4_15)
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) {z : X} (hz1 : z ≠ 1)
    (hz : ∃ P' : Sylow 3 X, z ∈ (P' : Subgroup X) ∧
      (P' : Subgroup X) ≤ Subgroup.centralizer ({z} : Set X)) :
    IsQuasisimple ↥(perfectResidual ↥(Subgroup.centralizer ({z} : Set X))) := by
  obtain ⟨P', hzP', hP'z⟩ := hz
  have hZ := j2_zpowers_eq h415 hX P' hz1 hzP' ⟨P', hzP', hP'z⟩
  obtain ⟨hZ3, -, hext⟩ := j2_sylow_facts h415 hX P'
  rw [← hZ] at hext hZ3
  have hCz : Subgroup.centralizer ((Subgroup.zpowers z : Subgroup X) : Set X) =
      Subgroup.centralizer ({z} : Set X) := by
    rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure]
  rw [hCz] at hext
  set C := Subgroup.centralizer ({z} : Set X) with hC
  obtain ⟨N, hN, ⟨e₁⟩, ⟨e₂⟩⟩ := hext
  have hZC : Subgroup.zpowers z ≤ C := Subgroup.zpowers_le.mpr
    (Subgroup.mem_centralizer_singleton_iff.mpr rfl)
  set ZT := (Subgroup.zpowers z).subgroupOf C with hZT
  have hZTc : ZT ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hx)
    have hy := Subgroup.mem_centralizer_singleton_iff.mp y.2
    change (y : X) * (x : X) = (x : X) * y
    rw [← hk]
    exact (Commute.zpow_right hy k).eq
  have hZT3 : Nat.card ZT = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZC).toEquiv]
    exact hZ3
  have hN3 : Nat.card N = 3 := by
    rw [Nat.card_congr e₁.toEquiv, Nat.card_eq_fintype_card, Fintype.card_multiplicative,
      ZMod.card]
  have hNZ : N = ZT := by
    by_contra hne
    have hinf : N ⊓ ZT = ⊥ := by
      have hdvd : Nat.card ↥(N ⊓ ZT) ∣ 3 := hN3 ▸ Subgroup.card_dvd_of_le inf_le_left
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
      · exact Subgroup.eq_bot_of_card_eq _ h1
      · exfalso
        apply hne
        have h1 : N ⊓ ZT = N := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h3, hN3])
        have h2 : N ⊓ ZT = ZT := Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h3, hZT3])
        rw [← h1, h2]
    obtain ⟨⟨x, hxZ⟩, hx1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
      (fun h : ZT = ⊥ => by rw [h, Subgroup.card_bot] at hZT3; exact absurd hZT3 (by norm_num))
    have hxN : x ∉ N := fun hxN => hx1 (Subtype.ext (by
      have : x ∈ N ⊓ ZT := ⟨hxN, hxZ⟩
      rw [hinf, Subgroup.mem_bot] at this
      exact this))
    have hcen : (QuotientGroup.mk' N x) ∈ Subgroup.center (↥C ⧸ N) := by
      rw [Subgroup.mem_center_iff]
      intro q
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective N q
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp (hZTc hxZ) y]
    rw [center_eq_bot_of_mulEquiv_alternating_six e₂, Subgroup.mem_bot,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    exact hxN hcen
  have hNc : N ≤ Subgroup.center ↥C := hNZ ▸ hZTc
  set R := perfectResidual ↥C with hR
  have hRperf : Group.IsPerfect ↥R := (perfect_residual_characterization (G := ↥C)).2.2.1
  have hA6 := alternatingGroup_six_isPerfect
  have hQperf : Group.IsPerfect (↥C ⧸ N) :=
    Group.IsPerfect.ofSurjective (f := e₂.symm.toMonoidHom) e₂.symm.surjective
  let f : ↥R →* alternatingGroup (Fin 6) :=
    e₂.toMonoidHom.comp ((QuotientGroup.mk' N).comp R.subtype)
  have hRmap : R.map (QuotientGroup.mk' N) = ⊤ := by
    have h : (perfectResidual ↥C).map (QuotientGroup.mk' N) = perfectResidual (↥C ⧸ N) :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq _
        (QuotientGroup.mk'_surjective N)
    rw [hR, h]
    refine top_le_iff.mp ((perfect_residual_transport (MonoidHom.id (↥C ⧸ N))).2.2 ⊤ ?_)
    exact Group.IsPerfect.top_iff.mpr hQperf
  have hf : Function.Surjective f := by
    intro a
    obtain ⟨q, rfl⟩ := e₂.surjective a
    have hq : q ∈ R.map (QuotientGroup.mk' N) := hRmap ▸ Subgroup.mem_top q
    obtain ⟨r, hr, rfl⟩ := hq
    exact ⟨⟨r, hr⟩, rfl⟩
  have hker : f.ker ≤ Subgroup.center ↥R := by
    intro r hr
    have hrN : (r : ↥C) ∈ N := by
      have h1 : e₂ (QuotientGroup.mk' N (r : ↥C)) = 1 := hr
      rw [map_eq_one_iff _ e₂.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    rw [Subgroup.mem_center_iff]
    intro s
    exact Subtype.ext (Subgroup.mem_center_iff.mp (hNc hrN) s)
  have hnt : Nontrivial ↥R := by
    have : Nontrivial (alternatingGroup (Fin 6)) :=
      (alternatingGroup.isSimpleGroup (α := Fin 6) (by norm_num)).toNontrivial
    exact hf.nontrivial
  obtain ⟨-, hcomm, hsimple⟩ :=
    CFSG.GorensteinWalter.isQuasisimple_of_perfect_of_ker_le_center_of_surjective_simple f hf
      hnt hRperf (alternatingGroup.isSimpleGroup (by norm_num)) hker
  exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥R).mp
    ⟨hcomm, hsimple⟩

end J2

theorem isQuasisimple_quotient_theta_of_surjective {J Q : Type*} [Group J] [Group Q] [Finite J]
    [Finite Q] (hQ : IsQuasisimple Q) (ρ : J →* Q) (hρ : Function.Surjective ρ)
    (hks : Group.IsSolvable ρ.ker) (hk3 : ¬ 3 ∣ Nat.card ρ.ker) :
    IsQuasisimple (J ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J) := by
  obtain ⟨hθs, hθc, -, hθmax, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := J)
      Nat.prime_three
  set θ := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 J
  have hkθ : ρ.ker ≤ θ := hθmax _ (MonoidHom.normal_ker ρ) hks hk3
  set M := θ.map ρ
  have hMn : M.Normal := (Subgroup.normal_of_characteristic θ).map ρ hρ
  have hqo : CFSG.Open.IsQuasisimple Q :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hQ
  have hMc : M ≤ Subgroup.center Q := by
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hqo M with h | h
    · exact h
    · exfalso
      have hsol : Group.IsSolvable ↥M := by
        have := hθs
        exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective θ)
      have hsol' : Group.IsSolvable Q := by
        rw [h] at hsol
        exact Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup Q) ≃* Q).toMonoidHom) (MulEquiv.surjective _)
      have : Group.IsPerfect Q := hQ.1
      have : Nontrivial Q := CFSG.ComponentClassification.Quasisimple.nontrivial hqo
      exact (Group.IsPerfect.not_isSolvable Q) hsol'
  have hker : ((QuotientGroup.mk' M).comp ρ).ker = θ := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', Subgroup.comap_map_eq, sup_eq_left.mpr hkθ]
  have hsurj : Function.Surjective ((QuotientGroup.mk' M).comp ρ) :=
    (QuotientGroup.mk'_surjective M).comp hρ
  let e : J ⧸ θ ≃* Q ⧸ M := (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)
  have hQM : IsQuasisimple (Q ⧸ M) :=
    (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      (CFSG.ComponentClassification.Quasisimple.central_quotient hqo M hMc)
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hQM

section Lift

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

omit [Finite G] in
theorem eq_one_of_mem_pCore_two_of_pow {x : ↥L} (hx : x ∈ CFSG.pCore 2 ↥L) {k : ℕ}
    (hk : x ^ 3 ^ k = 1) : x = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨x, hx⟩
  have h2 : x ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
  have hdvd : orderOf x ∣ Nat.gcd (3 ^ k) (2 ^ m) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hk) (orderOf_dvd_of_pow_eq_one h2)
  rw [Nat.Coprime.gcd_eq_one (Nat.Coprime.pow k m (by norm_num)), Nat.dvd_one,
    orderOf_eq_one_iff] at hdvd
  exact hdvd

theorem zpowers_eq_of_central_of_j2 (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {E : Subgroup G} (hE : IsPGroup 3 E) {d₁ d₂ : G} (h₁E : d₁ ∈ E) (h₂E : d₂ ∈ E)
    (h₁L : d₁ ∈ L) (h₂L : d₂ ∈ L) (h₁ : d₁ ≠ 1) (h₂ : d₂ ≠ 1)
    (hc₁ : ∃ S : Sylow 3 ↥L, (⟨d₁, h₁L⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d₁, h₁L⟩ : ↥L)})
    (hc₂ : ∃ S : Sylow 3 ↥L, (⟨d₂, h₂L⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d₂, h₂L⟩ : ↥L)}) :
    Subgroup.zpowers d₁ = Subgroup.zpowers d₂ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 2 ↥L
  set π := QuotientGroup.mk' O
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  set E' := (E.subgroupOf L).map π
  have hE' : IsPGroup 3 E' :=
    (hE.comap_of_injective L.subtype L.subtype_injective).map π
  have h3 : ∀ x : ↥L, (x : G) ∈ E → ∃ k : ℕ, x ^ 3 ^ k = 1 := fun x hx => by
    obtain ⟨k, hk⟩ := hE ⟨x, hx⟩
    exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
  have hne : ∀ x : ↥L, (x : G) ∈ E → (x : G) ≠ 1 → π x ≠ 1 := fun x hx hx1 h => by
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨k, hk⟩ := h3 x hx
    exact hx1 (congrArg Subtype.val (eq_one_of_mem_pCore_two_of_pow h hk))
  have hcen : ∀ (x : ↥L), (∃ S : Sylow 3 ↥L, x ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {x}) →
      ∃ S' : Sylow 3 (↥L ⧸ O), π x ∈ (S' : Subgroup (↥L ⧸ O)) ∧
        (S' : Subgroup (↥L ⧸ O)) ≤ Subgroup.centralizer {π x} := by
    rintro x ⟨S, hxS, hSx⟩
    refine ⟨S.mapSurjective hπs, ?_, ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem π hxS
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨y, hy, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp (hSx hy)]
  have hbar := j2_zpowers_eq_of_mem h415 hJ2 hE'
    (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr h₁E))
    (Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr h₂E))
    (hne _ h₁E h₁) (hne _ h₂E h₂) (hcen _ hc₁) (hcen _ hc₂)
  have lift : ∀ {x y : G} (hxE : x ∈ E) (hyE : y ∈ E) (hxL : x ∈ L) (hyL : y ∈ L),
      π ⟨y, hyL⟩ ∈ Subgroup.zpowers (π ⟨x, hxL⟩) → y ∈ Subgroup.zpowers x := by
    intro x y hxE hyE hxL hyL hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hO : (⟨x, hxL⟩ : ↥L) ^ (-k) * ⟨y, hyL⟩ ∈ O := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_zpow, ← hk,
        ← zpow_add, neg_add_cancel, zpow_zero]
    have hEz : ((⟨x, hxL⟩ : ↥L) ^ (-k) * ⟨y, hyL⟩ : ↥L).1 ∈ E := by
      simpa using E.mul_mem (E.zpow_mem hxE (-k)) hyE
    obtain ⟨j, hj⟩ := h3 _ hEz
    have h1 := eq_one_of_mem_pCore_two_of_pow hO hj
    have h1' : x ^ (-k) * y = 1 := by simpa using congrArg Subtype.val h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    calc x ^ k = x ^ k * (x ^ (-k) * y) := by rw [h1', mul_one]
      _ = y := by rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
  apply le_antisymm
  · exact Subgroup.zpowers_le.mpr (lift h₂E h₁E h₂L h₁L (hbar ▸ Subgroup.mem_zpowers _))
  · exact Subgroup.zpowers_le.mpr (lift h₁E h₂E h₁L h₂L (hbar.symm ▸ Subgroup.mem_zpowers _))

theorem center_sylow_eq_zpowers_of_j2 (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) {d : G}
    (hdL : d ∈ L) (hd1 : d ≠ 1) (S : Sylow 3 ↥L) (hdS : (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L))
    (hSd : (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hdL⟩ : ↥L)}) :
    CFSG.ABGLocalTools.IsSylowOf 3 ((S : Subgroup ↥L).map L.subtype) L ∧
      (Subgroup.center ↥((S : Subgroup ↥L).map L.subtype)).map
          ((S : Subgroup ↥L).map L.subtype).subtype = Subgroup.zpowers d := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.pCore 2 ↥L
  set π := QuotientGroup.mk' O
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  set d' : ↥L := ⟨d, hdL⟩
  set ZS := (S : Subgroup ↥L) ⊓ Subgroup.centralizer ((S : Subgroup ↥L) : Set ↥L) with hZS
  set S' := S.mapSurjective hπs
  obtain ⟨hZ3, -, -⟩ := j2_sylow_facts h415 hJ2 S'
  have hinjS : ∀ x ∈ (S : Subgroup ↥L), ∀ y ∈ (S : Subgroup ↥L), π x = π y → x = y := by
    intro x hx y hy hxy
    have hO : x⁻¹ * y ∈ O := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, map_mul, map_inv, hxy,
        inv_mul_cancel]
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨x⁻¹ * y, (S : Subgroup ↥L).mul_mem (inv_mem hx) hy⟩
    have h1 := eq_one_of_mem_pCore_two_of_pow hO (k := k)
      (by simpa using congrArg Subtype.val hk)
    rw [inv_mul_eq_one] at h1
    exact h1
  have hZSle : Nat.card ZS ≤ 3 := by
    rw [← hZ3]
    refine Nat.card_le_card_of_injective (fun z : ZS => (⟨π z, ?_⟩ :
      ↥((S' : Subgroup (↥L ⧸ O)) ⊓ Subgroup.centralizer ((S' : Subgroup (↥L ⧸ O)) : Set _))))
      fun z z' h => Subtype.ext (hinjS _ z.2.1 _ z'.2.1 (congrArg Subtype.val h))
    refine ⟨?_, Subgroup.mem_centralizer_iff.mpr ?_⟩
    · rw [Sylow.coe_mapSurjective]
      exact Subgroup.mem_map_of_mem π z.2.1
    · rw [Sylow.coe_mapSurjective]
      rintro _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp z.2.2 y hy]
  have hdZ : Subgroup.zpowers d' ≤ ZS :=
    Subgroup.zpowers_le.mpr ⟨hdS, Subgroup.mem_centralizer_iff.mpr fun y hy =>
      Subgroup.mem_centralizer_singleton_iff.mp (hSd hy)⟩
  have hd'1 : d' ≠ 1 := fun h => hd1 (congrArg Subtype.val h)
  have hZSp : IsPGroup 3 ZS := S.isPGroup'.to_le inf_le_left
  have hdeq : Subgroup.zpowers d' = ZS := by
    refine Subgroup.eq_of_le_of_card_ge hdZ ?_
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (hZSp.to_le hdZ)
    have hn1 : n ≠ 0 := by
      rintro rfl
      rw [pow_zero, Nat.card_zpowers, orderOf_eq_one_iff] at hn
      exact hd'1 hn
    have h3 : 3 ≤ Nat.card (Subgroup.zpowers d') := by
      rw [hn]
      calc 3 = 3 ^ 1 := by norm_num
        _ ≤ 3 ^ n := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hn1)
    omega
  set SG := (S : Subgroup ↥L).map L.subtype
  have hmap : (Subgroup.center ↥SG).map SG.subtype = ZS.map L.subtype := by
    rw [map_subtype_center_eq]
    ext x
    constructor
    · rintro ⟨⟨s, hs, rfl⟩, hxC⟩
      refine ⟨s, ⟨hs, Subgroup.mem_centralizer_iff.mpr fun y hy => Subtype.ext ?_⟩, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp hxC (y : G) ⟨y, hy, rfl⟩
    · rintro ⟨s, ⟨hs, hsC⟩, rfl⟩
      refine ⟨⟨s, hs, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨y, hy, rfl⟩
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hsC y hy)
  refine ⟨⟨S, rfl⟩, ?_⟩
  rw [hmap, ← hdeq, MonoidHom.map_zpowers]
  rfl

theorem aschbacherSolvableCore_eq_pCore_two
    (hq : IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L))
    (hc : Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) = ⊥) :
    CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥L = CFSG.pCore 2 ↥L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hθs, hθc, -, hθmax, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
  set O := CFSG.pCore 2 ↥L
  set θ := CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥L
  set π := QuotientGroup.mk' O
  refine le_antisymm ?_ ?_
  · have hn : (θ.map π).Normal :=
      (Subgroup.normal_of_characteristic θ).map π (QuotientGroup.mk'_surjective O)
    have hqo : CFSG.Open.IsQuasisimple (↥L ⧸ O) :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hq
    rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hqo (θ.map π)
      with h | h
    · rw [hc] at h
      have h' := le_bot_iff.mp h
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at h'
      exact h'
    · exfalso
      have hsol : Group.IsSolvable ↥(θ.map π) := by
        have := hθs
        exact Group.isSolvable_of_surjective (π.subgroupMap_surjective θ)
      have hsol' : Group.IsSolvable (↥L ⧸ O) := by
        rw [h] at hsol
        exact Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup (↥L ⧸ O)) ≃* (↥L ⧸ O)).toMonoidHom)
          (MulEquiv.surjective _)
      have : Group.IsPerfect (↥L ⧸ O) := hq.1
      have : Nontrivial (↥L ⧸ O) := CFSG.ComponentClassification.Quasisimple.nontrivial hqo
      exact (Group.IsPerfect.not_isSolvable (↥L ⧸ O)) hsol'
  · refine hθmax O CFSG.pCore_normal ?_ ?_
    · have : Group.IsNilpotent ↥O := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).isNilpotent
      infer_instance
    · intro h3
      obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
      rw [hn] at h3
      exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)) (by norm_num)

noncomputable def quotThetaEquiv {A B : Type*} [Group A] [Group B] [Finite A] (e : A ≃* B) :
    A ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 A ≃*
      B ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 B :=
  QuotientGroup.congr _ _ e (CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three e)

theorem residual_inf_centralizer_quasisimple (h415 : Sec4.Item4_15)
    (hJ2 : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) {d : G}
    (hdL : d ∈ L) (hd1 : d ≠ 1)
    (hc : ∃ S : Sylow 3 ↥L, (⟨d, hdL⟩ : ↥L) ∈ (S : Subgroup ↥L) ∧
      (S : Subgroup ↥L) ≤ Subgroup.centralizer {(⟨d, hdL⟩ : ↥L)}) :
    IsQuasisimple (↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G))) ⧸
      CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
        ↥(inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set O := CFSG.pCore 2 ↥L with hO
  set π := QuotientGroup.mk' O with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective O
  set d' : ↥L := ⟨d, hdL⟩ with hd'
  set CL := Subgroup.centralizer ({d'} : Set ↥L) with hCL
  set J' := inSubgroup perfectResidual CL with hJ'
  have hJ : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) =
      J'.map L.subtype := by
    rw [hJ', CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_perfectResidual_of_injective
      L.subtype L.subtype_injective, hCL,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton]
  obtain ⟨S, hdS, hSd⟩ := hc
  have hd3 : IsPGroup 3 (Subgroup.zpowers d') := S.isPGroup'.to_le (Subgroup.zpowers_le.mpr hdS)
  have hO3 : ¬ 3 ∣ Nat.card O := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
    rw [hn] at h3
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)) (by norm_num)
  have hCmap : CL.map π = Subgroup.centralizer ({π d'} : Set (↥L ⧸ O)) := by
    have h := CFSG.Semidihedral.Local.map_centralizer_eq_of_coprime 3 O hO3 (Subgroup.zpowers d')
      hd3
    rw [MonoidHom.map_zpowers, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
      Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure] at h
    exact h
  set Cbar := Subgroup.centralizer ({π d'} : Set (↥L ⧸ O)) with hCbar
  set Q := inSubgroup perfectResidual Cbar with hQ
  have hJQ : J'.map π = Q := by
    let ψ : ↥CL →* ↥Cbar := (π.comp CL.subtype).codRestrict Cbar fun c =>
      hCmap ▸ Subgroup.mem_map_of_mem π c.2
    have hψ : Function.Surjective ψ := by
      rintro ⟨q, hq⟩
      rw [← hCmap] at hq
      obtain ⟨c, hc, rfl⟩ := hq
      exact ⟨⟨c, hc⟩, rfl⟩
    have h : (perfectResidual ↥CL).map ψ = perfectResidual ↥Cbar :=
      CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq ψ hψ
    rw [hJ', hQ, inSubgroup, inSubgroup, ← h, Subgroup.map_map, Subgroup.map_map]
    rfl
  have hd'O : π d' ≠ 1 := by
    intro h
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h
    obtain ⟨k, hk⟩ := S.isPGroup' ⟨d', hdS⟩
    exact hd1 (congrArg Subtype.val (eq_one_of_mem_pCore_two_of_pow h (k := k)
      (by simpa using congrArg Subtype.val hk)))
  have hQqs : IsQuasisimple ↥Q := by
    have h := j2_centralizer_residual_quasisimple h415 hJ2 hd'O
      ⟨S.mapSurjective hπs, by
        rw [Sylow.coe_mapSurjective]
        exact Subgroup.mem_map_of_mem π hdS, by
        rw [Sylow.coe_mapSurjective]
        rintro _ ⟨y, hy, rfl⟩
        rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
          Subgroup.mem_centralizer_singleton_iff.mp (hSd hy)]⟩
    exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      ((perfectResidual ↥Cbar).equivMapOfInjective Cbar.subtype Cbar.subtype_injective) h
  let ρ : ↥J' →* ↥Q := (π.comp J'.subtype).codRestrict Q fun x =>
    hJQ ▸ Subgroup.mem_map_of_mem π x.2
  have hρ : Function.Surjective ρ := by
    rintro ⟨q, hq⟩
    rw [← hJQ] at hq
    obtain ⟨x, hx, rfl⟩ := hq
    exact ⟨⟨x, hx⟩, rfl⟩
  have hk2 : IsPGroup 2 ρ.ker := by
    intro x
    have hx : ((x : ↥J') : ↥L) ∈ O := by
      have h1 : ρ x = 1 := x.2
      have h2 : π ((x : ↥J') : ↥L) = 1 := congrArg Subtype.val h1
      rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      exact h2
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)) ⟨_, hx⟩
    refine ⟨m, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hm
  have hks : Group.IsSolvable ρ.ker := by
    have : Group.IsNilpotent ρ.ker := hk2.isNilpotent
    infer_instance
  have hk3 : ¬ 3 ∣ Nat.card ρ.ker := by
    intro h3
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hk2
    rw [hn] at h3
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
      (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)) (by norm_num)
  have hJ'q := isQuasisimple_quotient_theta_of_surjective hQqs ρ hρ hks hk3
  rw [hJ]
  exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (quotThetaEquiv (J'.equivMapOfInjective L.subtype L.subtype_injective)) hJ'q

theorem exists_mem_thetaComponentsAt_of_residual {b d : G} (hbd : b * d = d * b)
    {W : Subgroup G} (hW : W ∈ CFSG.RankThree.thetaComponentsAt 3 b)
    (hJ : IsQuasisimple (↥(inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G))) ⧸
      CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
        ↥(inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G))))) :
    ∃ T ∈ CFSG.RankThree.thetaComponentsAt 3
        (⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbd⟩ :
          ↥(Subgroup.centralizer ({d} : Set G))),
      T.map (Subgroup.centralizer ({d} : Set G)).subtype =
        inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G)) := by
  set J := inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G)) with hJdef
  set C₁ := Subgroup.centralizer ({b} : Set G) with hC₁
  set C₂ := Subgroup.centralizer ({d} : Set G) with hC₂
  set d₁ : ↥C₁ := ⟨d, Subgroup.mem_centralizer_singleton_iff.mpr hbd.symm⟩ with hd₁
  set x : ↥C₂ := ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbd⟩ with hx
  set Z₁ := Subgroup.centralizer ({d₁} : Set ↥C₁) with hZ₁
  set Z₂ := Subgroup.centralizer ({x} : Set ↥C₂) with hZ₂
  have hZ₁map : Z₁.map C₁.subtype = C₁ ⊓ C₂ :=
    CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton C₁ d₁
  have hZ₂map : Z₂.map C₂.subtype = C₂ ⊓ C₁ :=
    CFSG.RankThree.GroupTheory.SteinbergBY.map_subtype_centralizer_singleton C₂ x
  have hZ : Z₁.map C₁.subtype = Z₂.map C₂.subtype := by rw [hZ₁map, hZ₂map, inf_comm]
  obtain ⟨hWC, hW₀⟩ := CFSG.RankThree.PartOne.mem_thetaComponentsAt_iff.mp hW
  have hJW : J ≤ W ⊓ C₂ := Subgroup.map_subtype_le _
  have hJC₁ : J ≤ C₁ := hJW.trans (inf_le_left.trans hWC)
  have hJZ : J.subgroupOf C₁ ≤ Z₁ := by
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    rw [hZ₁, Subgroup.mem_centralizer_singleton_iff]
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hJW hy).2)
  set T₁ := (J.subgroupOf C₁).subgroupOf Z₁ with hT₁
  have hmemT₁ : ∀ z : ↥Z₁, z ∈ T₁ ↔ ((z : ↥C₁) : G) ∈ J := fun z => by
    rw [hT₁, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
  let e : ↥T₁ ≃* ↥J := (Subgroup.subgroupOfEquivOfLe hJZ).trans
    (Subgroup.subgroupOfEquivOfLe hJC₁)
  have hJperf : Group.IsPerfect ↥J := by
    have h := (perfect_residual_characterization
      (G := ↥(W ⊓ Subgroup.centralizer ({d} : Set G)))).2.2.1
    exact Group.IsPerfect.ofSurjective
      (f := ((perfectResidual ↥(W ⊓ C₂)).equivMapOfInjective _
        (Subgroup.subtype_injective _)).toMonoidHom) (MulEquiv.surjective _)
  have hT₁ : T₁ ∈ CFSG.RankThree.thetaComponents 3 ↥Z₁ := by
    refine ⟨Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective, ?_,
      CFSG.LocalCores.isQuasisimple_of_mulEquiv (quotThetaEquiv e.symm) hJ⟩
    set V := (W.subgroupOf C₁).subgroupOf Z₁ with hV
    have hVsn : V.IsSubnormal := hW₀.2.1.subgroupOf
    have hTV : T₁ ≤ V := fun z hz => by
      rw [hV, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      exact (hJW ((hmemT₁ z).mp hz)).1
    have hNJ : W ⊓ C₂ ≤ Subgroup.normalizer (J : Set G) :=
      Subgroup.le_normalizer.trans
        (CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
          (W ⊓ C₂))
    have hVN : V ≤ Subgroup.normalizer (T₁ : Set ↥Z₁) := by
      intro v hv
      have hvW : ((v : ↥C₁) : G) ∈ W := by
        rw [hV, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at hv
        exact hv
      have hvC : ((v : ↥C₁) : G) ∈ C₂ := by
        have h1 : (v : ↥C₁) * d₁ = d₁ * (v : ↥C₁) :=
          Subgroup.mem_centralizer_singleton_iff.mp v.2
        exact Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val h1)
      have hvN := hNJ ⟨hvW, hvC⟩
      rw [Subgroup.mem_normalizer_iff]
      intro z
      rw [hmemT₁, hmemT₁]
      simpa using (Subgroup.mem_normalizer_iff.mp hvN ((z : ↥C₁) : G))
    have hTVn : (T₁.subgroupOf V).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hTV).mpr hVN
    exact Subgroup.IsSubnormal.trans hTV hTVn.isSubnormal hVsn
  obtain ⟨T₂, hT₂, hT₂eq⟩ :=
    CFSG.RankThree.PartOne.EmbeddingFixedResidual.exists_mem_thetaComponents_of_map_eq
      Nat.prime_three hZ hT₁
  refine ⟨T₂.map Z₂.subtype, ⟨T₂, hT₂, rfl⟩, ?_⟩
  rw [hT₂eq, Subgroup.map_subgroupOf_eq_of_le hJZ, Subgroup.map_subgroupOf_eq_of_le hJC₁]

theorem exists_mem_thetaComponentsAt_le_residual (h48 : Sec4.Item4_8) {A : Subgroup G} {b d : G}
    (hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)))
    (hA : CFSG.RankThree.PartTwo.Late.IsE27 A) (hbA : b ∈ A) (hdA : d ∈ A) (hb1 : b ≠ 1)
    {W : Subgroup G} (hW : W ∈ CFSG.RankThree.thetaComponentsAt 3 b)
    (hJ : IsQuasisimple (↥(inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G))) ⧸
      CFSG.RankThree.LocalRank.aschbacherSolvableCore 3
        ↥(inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G))))) :
    ∃ K ∈ CFSG.RankThree.thetaComponentsAt 3 d,
      inSubgroup perfectResidual (W ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hbd : b * d = d * b := hcomm b hbA d hdA
  have hAC : A ≤ Subgroup.centralizer ({d} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm y hy d hdA)
  have hA' : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf (Subgroup.centralizer ({d} : Set G))) := by
    refine ⟨⟨⟨fun y z => Subtype.ext (Subtype.ext ?_)⟩⟩, fun y hy => ?_⟩
    · exact hcomm _ (Subgroup.mem_subgroupOf.mp y.2) _ (Subgroup.mem_subgroupOf.mp z.2)
    · exact Subtype.ext (by simpa using hA.1.2 _ (Subgroup.mem_subgroupOf.mp hy))
  have h27 : ∃ n : ℕ, 3 ≤ n ∧
      Nat.card (A.subgroupOf (Subgroup.centralizer ({d} : Set G))) = 3 ^ n :=
    ⟨3, le_rfl, by rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAC).toEquiv, hA.2]; norm_num⟩
  obtain ⟨T, hT, hTJ⟩ := exists_mem_thetaComponentsAt_of_residual hbd hW hJ
  obtain ⟨K', hK', hTK'⟩ := h48 ↥(Subgroup.centralizer ({d} : Set G)) hG4
    (A.subgroupOf (Subgroup.centralizer ({d} : Set G))) hA' h27
    ⟨b, Subgroup.mem_centralizer_singleton_iff.mpr hbd⟩ (Subgroup.mem_subgroupOf.mpr hbA)
    (fun h => hb1 (congrArg Subtype.val h)) T hT
  exact ⟨K'.map (Subgroup.centralizer ({d} : Set G)).subtype, ⟨K', hK', rfl⟩,
    hTJ ▸ Subgroup.map_mono hTK'⟩

end Lift

end CFSG.RankThree.PartTwo.Sec14
