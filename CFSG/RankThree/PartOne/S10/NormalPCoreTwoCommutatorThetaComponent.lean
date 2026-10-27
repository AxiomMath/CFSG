module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.GroupTheory.CentralLineDetection
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator
public import CFSG.LocalAnalysis.ComponentInitial.CoprimeCommutatorFactorization
public import CFSG.GroupTheory.LocalCores.Fitting

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem actionCommutator_top_eq_top_of_moving_theta_quotient {p : ℕ} (hp : p.Prime)
    {L A : Type*} [Group L] [Finite L] [Group A] [MulDistribMulAction A L]
    (hLperf : Group.IsPerfect L) (hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore p L))
    (a : A) (g : L)
    (hnt : ((a • g : L) : L ⧸ aschbacherSolvableCore p L) ≠
      (g : L ⧸ aschbacherSolvableCore p L)) :
    actionCommutator A (⊤ : Subgroup L) = ⊤ := by
  classical
  set N := aschbacherSolvableCore p L with hN
  obtain ⟨hNs, hNchar, hNp, hNmax, -⟩ := solvable_prime_complement_core_characterization
    (H := L) hp
  have := hNchar
  have : N.Normal := inferInstance
  set π := QuotientGroup.mk' N with hπ
  set V := actionCommutator A (⊤ : Subgroup L) with hV
  have hVn : V.Normal := actionCommutator_top_normal
  have hVπ : V.map π = ⊤ := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hLq
      (hVn.map π (QuotientGroup.mk'_surjective N)) with h | h
    · exact h
    · exfalso
      have := hLq.1
      set σ : MulAut (L ⧸ N) := mulAutQuotientHom N (MulDistribMulAction.toMulEquiv L a) with hσ
      have hσmk : ∀ x : L, σ (x : L ⧸ N) = ((a • x : L) : L ⧸ N) := fun x => rfl
      have hid :=
        CFSG.ComponentClassification.PerfectAutomorphisms.hom_eq_id_of_central_displacement
        σ.toMonoidHom (fun q => by
          obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
          have hx : x⁻¹ * (a • x) ∈ V := gen_mem_actionCommutator (mem_top x) a
          have hmem := h (Subgroup.mem_map_of_mem π hx)
          have e : ((x : L ⧸ N))⁻¹ * σ.toMonoidHom (x : L ⧸ N) = π (x⁻¹ * (a • x)) := by
            rw [map_mul, map_inv]
            rfl
          rw [e]
          exact hmem)
      apply hnt
      have := congrArg (fun φ : (L ⧸ N) →* (L ⧸ N) => φ (g : L ⧸ N)) hid
      simpa [hσmk] using this
  have hVN : V ⊔ N = ⊤ := by
    have h := comap_map_eq π V
    rw [hVπ, comap_top, QuotientGroup.ker_mk'] at h
    exact h.symm
  have hsurj : Function.Surjective ((QuotientGroup.mk' V).comp N.subtype) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective V q
    have hg : x ∈ ((V ⊔ N : Subgroup L) : Set L) := hVN ▸ mem_top x
    rw [normal_mul] at hg
    obtain ⟨m, hm, o, ho, rfl⟩ := hg
    refine ⟨⟨o, ho⟩, ?_⟩
    have hm1 : QuotientGroup.mk' V m = 1 := (QuotientGroup.eq_one_iff m).mpr hm
    rw [MonoidHom.comp_apply, map_mul, hm1, one_mul]
    rfl
  have hsolv : Group.IsSolvable (L ⧸ V) := Group.isSolvable_of_surjective hsurj
  have htop : commutator (L ⧸ V) = ⊤ := by
    rw [_root_.commutator_def, ← map_top_of_surjective _ (QuotientGroup.mk'_surjective V),
      ← map_commutator, ← _root_.commutator_def, Group.IsPerfect.commutator_eq_top]
  have hsub : Subsingleton (L ⧸ V) := by
    by_contra hnt'
    rw [not_subsingleton_iff_nontrivial] at hnt'
    exact (Group.IsSolvable.commutator_lt_top_of_nontrivial (G := L ⧸ V)).ne htop
  refine eq_top_iff.mpr fun x _ => ?_
  exact (QuotientGroup.eq_one_iff x).mp (Subsingleton.elim _ _)

theorem commutator_le_centralizer_of_normalizes {X : Type*} [Group X] {Q K S : Subgroup X}
    (hQK : Q ≤ normalizer (K : Set X)) (hSK : S ≤ Subgroup.centralizer (K : Set X)) :
    ⁅Q, S⁆ ≤ Subgroup.centralizer (K : Set X) := by
  rw [Subgroup.commutator_le]
  intro q hq s hs
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : q⁻¹ * k * q ∈ K := by
    have := (Subgroup.mem_normalizer_iff.mp (hQK (Q.inv_mem hq)) k).mp hk
    simpa using this
  have h1 : s * (q⁻¹ * k * q) = (q⁻¹ * k * q) * s :=
    (Subgroup.mem_centralizer_iff.mp (hSK hs) _ hk').symm
  have h2 : s * k = k * s := (Subgroup.mem_centralizer_iff.mp (hSK hs) _ hk).symm
  have h2' : k * s⁻¹ = s⁻¹ * k := by
    have h3 : s⁻¹ * (s * k) * s⁻¹ = s⁻¹ * (k * s) * s⁻¹ := by rw [h2]
    simpa [mul_assoc] using h3
  calc k * ⁅q, s⁆ = q * ((q⁻¹ * k * q) * s) * q⁻¹ * s⁻¹ := by
        simp only [commutatorElement_def]; group
    _ = q * (s * (q⁻¹ * k * q)) * q⁻¹ * s⁻¹ := by rw [h1]
    _ = q * s * q⁻¹ * (k * s⁻¹) := by group
    _ = q * s * q⁻¹ * (s⁻¹ * k) := by rw [h2']
    _ = ⁅q, s⁆ * k := by simp only [commutatorElement_def]; group

theorem commutator_le_left_of_normalizes {X : Type*} [Group X] {Q S : Subgroup X}
    (hSQ : S ≤ normalizer (Q : Set X)) : ⁅Q, S⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro q hq s hs
  have h := (Subgroup.mem_normalizer_iff.mp (hSQ hs) q).mp hq
  have h' := (Subgroup.mem_normalizer_iff.mp (hSQ (S.inv_mem hs)) q).mp hq
  rw [commutatorElement_def]
  have e : q * s * q⁻¹ * s⁻¹ = q * (s * q⁻¹ * s⁻¹) := by group
  rw [e]
  refine Q.mul_mem hq ?_
  have := Q.inv_mem ((Subgroup.mem_normalizer_iff.mp (hSQ hs) q).mp hq)
  simpa [mul_assoc] using this

theorem eq_bot_of_centralizes_pcore_and_layer {X : Type*} [Group X] [Finite X] {p : ℕ}
    (hp : p.Prime) (hθ : aschbacherSolvableCore p X = ⊥) {T : Subgroup X} (hT : ¬ p ∣ Nat.card T)
    (hTP : T ≤ Subgroup.centralizer (pCore p X : Set X))
    (hTE : T ≤ Subgroup.centralizer (layer X : Set X)) : T = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have hTF : T ≤ Subgroup.centralizer (fittingSubgroup X : Set X) :=
    hTP.trans (Subgroup.centralizer_le (fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot
      hp hθ))
  have hTstar : T ≤ Subgroup.centralizer (generalizedFitting X : Set X) := by
    rw [Subgroup.le_centralizer_iff, generalizedFitting, sup_le_iff]
    exact ⟨Subgroup.le_centralizer_iff.mp hTF, Subgroup.le_centralizer_iff.mp hTE⟩
  set Cs := Subgroup.centralizer (generalizedFitting X : Set X)
  have hCsle : Cs ≤ generalizedFitting X := centralizer_generalizedFitting_le X
  have hchar := (CFSG.LocalCores.generalized_fitting_characteristic (G := X)).1
  have hCsn : Cs.Normal := Subgroup.normal_centralizer
  have hCscomm : IsMulCommutative Cs := ⟨⟨fun x y => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp x.2 y (hCsle y.2)).symm⟩⟩
  have hCsF : Cs ≤ fittingSubgroup X :=
    CFSG.LocalCores.fitting_characteristic.2.2 Cs hCsn inferInstance
  have hTP' : T ≤ pCore p X :=
    hTstar.trans (hCsF.trans (fittingSubgroup_le_pCore_of_aschbacherSolvableCore_eq_bot hp hθ))
  have hTp : IsPGroup p T := pCore_isPGroup.to_le hTP'
  rcases hTp.card_eq_or_dvd with h1 | hdvd
  · exact Subgroup.card_eq_one.mp h1
  · exact absurd hdvd hT

theorem normal_p_core_centralizing_two_commutator_produces_theta_component_of
    (hB5 : SelectedPrimeElementsNormalizeThetaComponents) :
    NormalPCoreCentralizingTwoCommutatorProducesThetaComponent := by
  intro H _ _ he p hp hp3 A hA Q hQ2 hAQ hQA hQN hQO a ha hQa
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hNs, hNchar, hNp, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set N := aschbacherSolvableCore p H with hN
  have := hNchar
  have : N.Normal := inferInstance
  set π := QuotientGroup.mk' N with hπ
  have hθX : aschbacherSolvableCore p (H ⧸ N) = ⊥ :=
    (solvable_prime_complement_core_quotient_centralizers (G := H) hp N hNs hNp).2.2.1
  have hAnorm : ∀ x ∈ A, ∀ L ∈ thetaComponents p H, x ∈ normalizer (L : Set H) := by
    intro x hx L hL
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨x, hx⟩
    exact hB5.1 H he p hp hp3 x ⟨k, (Subgroup.orderOf_coe (⟨x, hx⟩ : A)).trans hk⟩ L hL
  have hcomp : ∀ x ∈ A, ∀ J : Subgroup (H ⧸ N), IsComponent J →
      π x ∈ normalizer (J : Set (H ⧸ N)) :=
    fun x hx J hJ => EmbeddingTransport.mk_mem_normalizer_of_mem_normalizer_thetaComponents hp
      (fun L hL => hAnorm x hx L hL) hJ
  have hAbar : ∀ J : Subgroup (H ⧸ N), IsComponent J → A.map π ≤ normalizer (J : Set (H ⧸ N)) := by
    rintro J hJ _ ⟨x, hx, rfl⟩
    exact hcomp x hx J hJ
  have hQbar : ∀ J : Subgroup (H ⧸ N), IsComponent J → Q.map π ≤ normalizer (J : Set (H ⧸ N)) := by
    intro J hJ
    have h : ⁅Q.map π, A.map π⁆ = Q.map π := by
      rw [← Subgroup.map_commutator, hQA]
    have h2 := commutator_le_normalizer_of_components (H := Q.map π) (B := A.map π) hAbar hJ
    rwa [h] at h2
  have hzA : Subgroup.zpowers a ≤ A := Subgroup.zpowers_le.mpr ha
  have hzQ : Subgroup.zpowers a ≤ normalizer (Q : Set H) := hzA.trans hAQ
  have hodd : ¬ 2 ∣ Nat.card (Subgroup.zpowers a) := by
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hA ⟨a, ha⟩
    have hk' : orderOf a = p ^ k := (Subgroup.orderOf_coe (⟨a, ha⟩ : A)).trans hk
    intro h2
    rw [Nat.card_zpowers, hk'] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      (Nat.prime_two.dvd_of_dvd_pow h2)).symm
  have hid : ⁅⁅Q, Subgroup.zpowers a⁆, Subgroup.zpowers a⁆ = ⁅Q, Subgroup.zpowers a⁆ := by
    let _ : MulDistribMulAction (Subgroup.zpowers a) Q := conjActionOn hzQ
    have h := (coprime_pgroup_commutator_factorization (p := 2) Nat.prime_two (Q := Q)
      (A := Subgroup.zpowers a) hQ2 hodd).2
    have e1 := SteinbergBM.map_actionCommutator_conj hzQ (⊤ : Subgroup Q)
    have e2 := SteinbergBM.map_actionCommutator_conj hzQ
      (actionCommutator (Subgroup.zpowers a) (⊤ : Subgroup Q))
    have hTopQ : (⊤ : Subgroup Q).map Q.subtype = Q := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    rw [hTopQ] at e1
    rw [h, e1] at e2
    exact e2.symm
  have hTne : ⁅Q.map π, Subgroup.zpowers (π a)⁆ ≠ ⊥ := by
    intro h0
    have hD1 : ⁅Q, Subgroup.zpowers a⁆ ≤ N := by
      have h1 : (⁅Q, Subgroup.zpowers a⁆).map π = ⊥ := by
        rw [Subgroup.map_commutator, MonoidHom.map_zpowers]
        exact h0
      rw [Subgroup.map_eq_bot_iff] at h1
      exact h1.trans (QuotientGroup.ker_mk' N).le
    have hDQN : ⁅Q, Subgroup.zpowers a⁆ ≤ Q ⊓ N :=
      le_inf (commutator_le_left_of_normalizes hzQ) hD1
    have hcenQN : ⁅Q ⊓ N, Subgroup.zpowers a⁆ = ⊥ := by
      have h1 := Subgroup.commutator_mono (le_refl (Q ⊓ N)) hzA
      rw [Subgroup.commutator_comm (Q ⊓ N) A] at h1
      exact le_bot_iff.mp (h1.trans hQN.le)
    apply hQa
    rw [← hid]
    exact le_bot_iff.mp ((Subgroup.commutator_mono hDQN le_rfl).trans hcenQN.le)
  have hmoved : ∃ J : Subgroup (H ⧸ N), IsComponent J ∧
      π a ∉ Subgroup.centralizer (J : Set (H ⧸ N)) := by
    by_contra hcon
    push Not at hcon
    have hzπ : Subgroup.zpowers (π a) ≤ normalizer (Q.map π : Set (H ⧸ N)) := by
      rw [Subgroup.zpowers_le]
      exact Subgroup.le_normalizer_map π
        (Subgroup.mem_map_of_mem π (hzQ (Subgroup.mem_zpowers a)))
    set T := ⁅Q.map π, Subgroup.zpowers (π a)⁆ with hT
    have hTQ : T ≤ Q.map π := commutator_le_left_of_normalizes hzπ
    have hTE : T ≤ Subgroup.centralizer (layer (H ⧸ N) : Set (H ⧸ N)) := by
      rw [le_centralizer_layer_iff]
      intro J hJ
      exact commutator_le_centralizer_of_normalizes (hQbar J hJ)
        (Subgroup.zpowers_le.mpr (hcon J hJ))
    have hTP : T ≤ Subgroup.centralizer (pCore p (H ⧸ N) : Set (H ⧸ N)) :=
      hTQ.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQO)
    have hT2 : IsPGroup 2 T := (hQ2.map π).to_le hTQ
    have hTp : ¬ p ∣ Nat.card T := by
      obtain ⟨n, hn⟩ := (IsPGroup.iff_card).mp hT2
      rw [hn]
      intro h
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h))
    exact hTne (eq_bot_of_centralizes_pcore_and_layer hp hθX hTp hTP hTE)
  obtain ⟨J, hJ, hnc⟩ := hmoved
  obtain ⟨hLmem, hLJ⟩ := perfectResidual_comap_mem_thetaComponents hp hJ
  set L := inSubgroup perfectResidual (J.comap π) with hLdef
  refine ⟨L, hLmem, fun x hx => hAnorm x hx L hLmem, ?_⟩
  have hzL : Subgroup.zpowers a ≤ normalizer (L : Set H) :=
    Subgroup.zpowers_le.mpr (hAnorm a ha L hLmem)
  obtain ⟨j, hjJ, hj⟩ : ∃ j ∈ J, j * π a ≠ π a * j := by
    by_contra hcon'
    push Not at hcon'
    exact hnc (Subgroup.mem_centralizer_iff.mpr hcon')
  rw [← hLJ] at hjJ
  obtain ⟨l, hlL, rfl⟩ := hjJ
  let _ : MulDistribMulAction (Subgroup.zpowers a) L := conjActionOn hzL
  have hsmul : ∀ (b : Subgroup.zpowers a) (g : L), ((b • g : L) : H) = (b : H) * g * (b : H)⁻¹ :=
    fun _ _ => rfl
  have hcore := solvable_prime_complement_core_subnormal_intersection hp hLmem.2.1
  have hnt : (((⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) • (⟨l, hlL⟩ : L) : L) :
      L ⧸ aschbacherSolvableCore p L) ≠ ((⟨l, hlL⟩ : L) : L ⧸ aschbacherSolvableCore p L) := by
    intro h
    rw [QuotientGroup.eq] at h
    have hmem : (((⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) • (⟨l, hlL⟩ : L) : L)⁻¹ *
        ⟨l, hlL⟩ : L) ∈ aschbacherSolvableCore p L := h
    have hmemH : ((((⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) • (⟨l, hlL⟩ : L) : L)⁻¹ *
        ⟨l, hlL⟩ : L) : H) ∈ inSubgroup (aschbacherSolvableCore p) L :=
      ⟨_, hmem, rfl⟩
    rw [hcore] at hmemH
    have h1 : π ((a * l * a⁻¹)⁻¹ * l) = 1 := by
      exact (QuotientGroup.eq_one_iff _).mpr hmemH.2
    apply hj
    rw [map_mul, map_inv, map_mul, map_mul, map_inv, inv_mul_eq_one] at h1
    calc π l * π a = (π a * π l * (π a)⁻¹) * π a := by rw [h1]
      _ = π a * π l := by group
  have hA1 := actionCommutator_top_eq_top_of_moving_theta_quotient hp hLmem.1 hLmem.2.2
    (⟨a, Subgroup.mem_zpowers a⟩ : Subgroup.zpowers a) (⟨l, hlL⟩ : L) hnt
  have h := SteinbergBM.map_actionCommutator_conj hzL (⊤ : Subgroup L)
  have hTopL : (⊤ : Subgroup L).map L.subtype = L := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  rw [hA1, hTopL] at h
  exact h.symm

end CFSG.RankThree.PartOne
