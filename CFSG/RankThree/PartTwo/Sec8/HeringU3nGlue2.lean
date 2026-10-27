module

import CFSG.RankThree.PartTwo.Sec8.Item86ResProofCenter
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofLink
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item68
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof85

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open scoped commutatorElement


theorem local_facts (h45 : Sec4.Item4_5) (hInd : KF83Indep) (hO : KF84OuterL2)
    (hR : KF84FieldReeStd)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n)
    {e : G} (heB : e ∈ Subgroup.closure ({c, d} : Set G)) (he1 : e ≠ 1)
    {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 e)
    (hKY : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ Y)
    {s : G}
    (hsK : s ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))
    (hs1 : s ≠ 1) (hs2 : s ^ 2 = 1) :
    A ≤ Subgroup.normalizer (Y : Set G) ∧
    inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({e, s} : Set G)) ≤
      Subgroup.normalizer (Y : Set G) ∧
    (∀ C : Subgroup G, IsPGroup 2 C → C ≤ Sec4.thetaQuotCentralizer Y →
      Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (C : Set G) → C = ⊥) ∧
    Odd (Nat.card
      (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd := h.data83
  have hG : TheoremFourHyp G := h.toTheoremFourHyp
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := h.mem_partTwoF.1
  have hA81 : Nat.card A = 81 := hd.card_eq
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have h3 : ∀ x ∈ A, x ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := h.mem_A
  have haA : a ∈ A := h.a_mem
  have hdA : d ∈ A := hd.d_mem
  have hcL : L ≤ Subgroup.centralizer ({c} : Set G) :=
    Sec6.le_centralizer_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcy : ∀ y ∈ L, c * y = y * c := fun y hy =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hcL hy)).symm
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hKdef
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKd : K ≤ Subgroup.centralizer ({d} : Set G) :=
    (Item87Proof.residual_le _).trans inf_le_right
  have hcK : ∀ k ∈ K, c * k = k * c := fun k hk => hcy k (hKL hk)
  have hdK : ∀ k ∈ K, d * k = k * d := fun k hk =>
    (Subgroup.mem_centralizer_singleton_iff.mp (hKd hk)).symm
  have hAL : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hG hAe hcA h.ne_one L h.mem_thetaComponentsAt
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := by
    intro x hx
    have hxC : x ∈ Subgroup.normalizer (Subgroup.centralizer ({d} : Set G) : Set G) :=
      Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx d hdA))
    have hxLd : x ∈ Subgroup.normalizer
        ((L ⊓ Subgroup.centralizer {d} : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      rw [Subgroup.mem_inf, Subgroup.mem_inf, (Subgroup.mem_normalizer_iff.mp (hAL hx) y),
        (Subgroup.mem_normalizer_iff.mp hxC y)]
    exact CFSG.RankThree.GroupTheory.SteinbergBY.normalizer_le_normalizer_inSubgroup_perfectResidual
      _ hxLd
  have hdΓ := isGammaIndex_of_data83 hd
  have hn1 : 1 ≤ n := hdΓ.2.2.1
  have hdc : d ∉ Subgroup.zpowers c :=
    not_mem_zpowers_of_isGammaIndex h.mem_thetaComponentsAt hdΓ
  have hloc : CFSG.Assembly.RankThreeEven.localRank 3 G ≤ 3 := hG.localRank_three.le
  have hθ3 : ∀ Y : Subgroup G, ¬ 3 ∣ Nat.card (inSubgroup (aschbacherSolvableCore 3) Y) := by
    intro Y
    rw [inSubgroup, Subgroup.card_map_of_injective Y.subtype_injective]
    exact KFacts.not_three_dvd_card_aschbacherSolvableCore Y
  have hθKodd := odd_card_of_le_normalizer hloc hAe hA81 (hθ3 K)
    (hAK.trans (Sec6.normalizer_le_normalizer_theta K))
  have hNT : NoThetaNormal (K ⧸ aschbacherSolvableCore 3 K) := by
    rcases Item87Res2Proof.quot_cases_of_isGammaIndex hdΓ with ⟨-, F, hF, hFf, hFc, ⟨φ⟩⟩ | hφ
    · exact Item87Proof.NoThetaNormal.of_mulEquiv φ
        (Item87Proof.noThetaNormal_statedSU hFc (by omega))
    · obtain ⟨φ⟩ := hφ
      exact Item87Proof.NoThetaNormal.of_mulEquiv φ
        (Item87Proof.noThetaNormal_projSL_two (by omega))
  set B := Subgroup.closure ({c, d} : Set G) with hBdef
  have hBA : B ≤ A := by
    rw [hBdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcA
    · exact hdA
  have heA : e ∈ A := hBA heB
  have he3 : e ^ 3 = 1 := h3 e heA
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  have hAe' : A ≤ Subgroup.centralizer ({e} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx e heA)
  have hAY : A ≤ Subgroup.normalizer (Y : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG he3 he1 hA3 hAe' Y hY
  have hBK : B ≤ Subgroup.centralizer (K : Set G) := by
    rw [hBdef, Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.mpr fun k hk => (hcK k hk).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun k hk => (hdK k hk).symm
  have hKe : K ≤ Subgroup.centralizer ({e} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (hBK heB) k hk)
  have hzK : Subgroup.zpowers s ≤ K := by
    rw [Subgroup.zpowers_le]
    exact hsK
  have hz1 : Subgroup.zpowers s ≠ ⊥ := by
    rwa [Ne, Subgroup.zpowers_eq_bot]
  have hz2 : IsPGroup 2 (Subgroup.zpowers s) := by
    have : orderOf s = 2 := orderOf_eq_prime hs2 hs1
    exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, this, pow_one])
  have hKTK : ⁅K, Subgroup.zpowers s⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk t ht
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk (hzK ht)) (K.inv_mem hk)) (K.inv_mem (hzK ht))
  have hKT : ¬ ⁅K, Subgroup.zpowers s⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G)) := by
    intro hle
    have h1 : ⁅K, Subgroup.zpowers s⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K :=
      (le_inf hKTK hle).trans (inf_theta_le_theta hKe)
    exact hz1 (eq_bot_of_isPGroup_two_of_le hz2 (le_theta_of_commutator_le hzK hz2 hNT h1)
      hθKodd)
  have hR1 : inSubgroup (CFSG.pCore 2) (Subgroup.centralizer ({e, s} : Set G)) ≤
      Subgroup.normalizer (Y : Set G) := by
    intro g hg
    have hg' : g ∈ Subgroup.centralizer ({e, s} : Set G) := Subgroup.map_subtype_le _ hg
    have hge : g ∈ Subgroup.centralizer ({e} : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun y hy => by
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact Subgroup.mem_centralizer_iff.mp hg' y (by simp)
    have hgs : g * s = s * g := by
      have := Subgroup.mem_centralizer_iff.mp hg' s (by simp)
      exact this.symm
    have hY' := Sec6.map_conj_mem_thetaComponentsAt hge hY
    have hsY' : Subgroup.zpowers s ≤ Y.map (MulAut.conj g).toMonoidHom := by
      rw [Subgroup.zpowers_le]
      refine ⟨s, hKY hsK, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [hgs, mul_inv_cancel_right]
    have heq := Item87Proof.eq_of_not_commutator_le hY hY' hKY hsY' hKT
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
  have hR3 : Odd (Nat.card (inSubgroup (aschbacherSolvableCore 3)
      (Subgroup.centralizer ({e} : Set G)))) := by
    refine odd_card_of_le_normalizer hloc hAe hA81 (hθ3 _) ?_
    exact fun x hx => Sec6.le_normalizer_theta _ (hAe' hx)
  refine ⟨hAY, hR1, ?_, hR3⟩
  intro C hC2 hCθ hEC
  by_contra hC1
  have hCθN : C ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) Y : Set G) :=
    fun v hv => Sec6.normalizer_le_normalizer_theta Y
      (Sec6.mem_thetaQuotCentralizer_iff.mp (hCθ hv)).1
  set P := inSubgroup (aschbacherSolvableCore 3) Y ⊔ C with hPdef
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3P
    have h1 := h3P.trans (card_sup_dvd_mul_of_le_normalizer _ C hCθN)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
    · exact hθ3 Y h2
    · obtain ⟨k, hk⟩ := hC2.exists_card_eq
      rw [hk] at h2
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
      omega
  have hP2 : 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := hC2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hC1 (Subgroup.eq_bot_of_card_eq C hk)
    have h1 := Subgroup.card_dvd_of_le (le_sup_right : C ≤ P)
    rw [hk] at h1
    exact (dvd_pow_self 2 hk0).trans h1
  obtain ⟨hout, y, hya, hy3, hyc⟩ :=
    exists_pow_three_noncentral_of hO hR h.toHyp81 (lt_card_of_sec8Std h) hd
  set E := Subgroup.closure ({c, a, d} : Set G) with hEdef
  have hyE : (y : G) ∉ E :=
    not_mem_closure_triple hcK hdK (hcomm a haA c hcA) (hcomm a haA d hdA) (h3 a haA) hout y.2
      hyc
  have hE27 : Nat.card E = 27 := card_closure_of_sec8Std hInd h
  have hEA : E ≤ A := closure_le_of_sec8Std h
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := Sec5.isElemAbelian_of_le hAe hEA
  have hEy : E ≤ Subgroup.centralizer ({(y : G)} : Set G) := by
    rw [hEdef, Subgroup.closure_le]
    rintro _ (rfl | rfl | rfl)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hcK y y.2)
    · exact Subgroup.mem_centralizer_singleton_iff.mpr hya.symm
    · exact Subgroup.mem_centralizer_singleton_iff.mpr (hdK y y.2)
  have hy3' : (y : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, hy3]
    rfl
  have hy1 : (y : G) ≠ 1 := fun h1 => hyE (h1 ▸ E.one_mem)
  set E' := E ⊔ Subgroup.zpowers (y : G) with hE'def
  have hE'e : CFSG.Assembly.IsElemAbelian 3 E' :=
    Item82OneProof.isElemAbelian_sup_zpowers hEe hy3' fun x hx =>
      Subgroup.mem_centralizer_singleton_iff.mp (hEy hx)
  have hyN : Subgroup.zpowers (y : G) ≤ Subgroup.normalizer (E : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun x hx => ?_)
    exact Subgroup.mem_centralizer_singleton_iff.mp (hEy hx)
  have hoy : orderOf (y : G) = 3 := orderOf_eq_prime hy3' hy1
  have hdisj : Disjoint E (Subgroup.zpowers (y : G)) := by
    have hI : Nat.card (Subgroup.zpowers (y : G) ⊓ E : Subgroup G) ∣ 3 := by
      rw [← hoy, ← Nat.card_zpowers]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hI with h1 | h1
    · rw [disjoint_comm, disjoint_iff]
      exact (Subgroup.eq_bot_of_card_eq _ h1)
    · exfalso
      apply hyE
      have heq : Subgroup.zpowers (y : G) ⊓ E = Subgroup.zpowers (y : G) :=
        Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, Nat.card_zpowers, hoy])
      have hmem : (y : G) ∈ Subgroup.zpowers (y : G) ⊓ E := by
        rw [heq]
        exact Subgroup.mem_zpowers _
      exact hmem.2
  have hE'81 : Nat.card E' = 81 := by
    rw [hE'def, CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer E _ hyN hdisj,
      hE27, Nat.card_zpowers, hoy]
  have hEN : E ≤ Subgroup.normalizer (P : Set G) := by
    intro e' he'
    have heθ := Sec6.normalizer_le_normalizer_theta Y (hAY (hEA he'))
    exact mem_normalizer_sup heθ (hEC he')
  have hyP : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
    have hyX : (y : G) ∈ Y := hKY y.2
    have hyθ := Sec6.le_normalizer_theta Y hyX
    refine mem_normalizer_of_conj_mem fun p hp => ?_
    have hle : P ≤ P.comap (MulAut.conj (y : G)).toMonoidHom := by
      refine sup_le (fun t ht => ?_) (fun v hv => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hyθ t).mp ht)
      · obtain ⟨-, hvθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hCθ hv)
        have h1 := hvθ (y : G)⁻¹ (Y.inv_mem hyX)
        have e : (MulAut.conj (y : G)).toMonoidHom v =
            ((y : G)⁻¹⁻¹ * (v * (y : G)⁻¹ * v⁻¹)) * v := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [Subgroup.mem_comap, e]
        exact Subgroup.mul_mem _ (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right hv)
    exact hle hp
  have hE'N : E' ≤ Subgroup.normalizer (P : Set G) := sup_le hEN (Subgroup.zpowers_le.mpr hyP)
  have hodd := odd_card_of_le_normalizer hloc hE'e hE'81 hP3 hE'N
  exact (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr hP2)

end CFSG.RankThree.PartTwo.Sec8.Item86ResProof
