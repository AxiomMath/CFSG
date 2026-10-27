module

public import CFSG.RankThree.PartOne.S10.ThetaContract
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
import CFSG.RankThree.PartOne.S10.NormalPCoreTwoCommutatorThetaComponent
import CFSG.RankThree.GroupTheory.CentralLineDetection
import CFSG.RankThree.LocalRank.ThetaCoreQuotients
import CFSG.RankThree.GroupTheory.SteinbergBMSimplePlaneFixedTwoCommutator

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.LocalAnalysis.ComponentInitial
open scoped commutatorElement

theorem select_moved_component {H : Type} [Group H] [Finite H]
    (hB5 : SelectedPrimeElementsNormalizeThetaComponents) (he : CFSG.Assembly.evenRank H ≤ 3)
    {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) {A Q : Subgroup H} (hA : IsPGroup p A)
    (hQ2 : IsPGroup 2 Q) (hAQ : A ≤ normalizer (Q : Set H)) (hQA : ⁅Q, A⁆ = Q)
    (hQN : ⁅A, Q ⊓ aschbacherSolvableCore p H⁆ = ⊥)
    (hQO : ⁅Q.map (QuotientGroup.mk' (aschbacherSolvableCore p H)),
      pCore p (H ⧸ aschbacherSolvableCore p H)⁆ = ⊥)
    {a : H} (ha : a ∈ A) (hQa : ⁅Q, Subgroup.zpowers a⁆ ≠ ⊥) :
    ∃ J : Subgroup (H ⧸ aschbacherSolvableCore p H), IsComponent J ∧
      Q.map (QuotientGroup.mk' (aschbacherSolvableCore p H)) ≤ normalizer (J : Set _) ∧
      A.map (QuotientGroup.mk' (aschbacherSolvableCore p H)) ≤ normalizer (J : Set _) ∧
      ¬ ⁅Q.map (QuotientGroup.mk' (aschbacherSolvableCore p H)),
          Subgroup.zpowers (QuotientGroup.mk' (aschbacherSolvableCore p H) a)⁆ ≤
        Subgroup.centralizer (J : Set _) := by
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
  have hzπ : Subgroup.zpowers (π a) ≤ normalizer (Q.map π : Set (H ⧸ N)) := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.le_normalizer_map π
      (Subgroup.mem_map_of_mem π (hzQ (Subgroup.mem_zpowers a)))
  set T := ⁅Q.map π, Subgroup.zpowers (π a)⁆ with hT
  have hTQ : T ≤ Q.map π := commutator_le_left_of_normalizes hzπ
  have hmoved : ∃ J : Subgroup (H ⧸ N), IsComponent J ∧ ¬ T ≤ Subgroup.centralizer (J : Set _) := by
    by_contra hcon
    push Not at hcon
    have hTE : T ≤ Subgroup.centralizer (layer (H ⧸ N) : Set (H ⧸ N)) := by
      rw [le_centralizer_layer_iff]
      intro J hJ
      exact hcon J hJ
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
  exact ⟨J, hJ, hQbar J hJ, hAbar J hJ, hnc⟩

end CFSG.RankThree.PartOne
