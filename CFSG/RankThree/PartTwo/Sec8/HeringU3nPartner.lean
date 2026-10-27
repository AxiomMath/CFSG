module

import CFSG.RankThree.PartTwo.Sec8.Item86ResProofCenter
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofLink
import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.Source.MinimalFaithfulCentralProduct
public import CFSG.RankThree.PartTwo.Sec8.Item86Res2Proof85

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item86ResProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof
open scoped commutatorElement


theorem exists_partner_of_commutator (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8)
    (hKB : KF83KBarTwo) (hInd : KF83Indep) (hO : KF84OuterL2) (hR : KF84FieldReeStd)
    {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n) {T : Subgroup G}
    (hTK : T ≤ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)))
    (hT1 : T ≠ ⊥) (hT2 : IsPGroup 2 T)
    (hET : Subgroup.closure ({c, a, d} : Set G) ≤ Subgroup.normalizer (T : Set G))
    {b : G} (hbB : b ∈ Subgroup.closure ({c, d} : Set G)) (hb1 : b ≠ 1)
    (hV : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (T : Set G)) ⊓
      Subgroup.centralizer ({b} : Set G), Subgroup.zpowers c⁆ ≠ ⊥) :
    ∃ X : Subgroup G, PairRel A c L b X := by
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
  set B := Subgroup.closure ({c, d} : Set G) with hBdef
  have hBA : B ≤ A := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact hcA
    · exact hdA
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := Sec5.isElemAbelian_of_le hAe hBA
  have hB9 : 9 ≤ Nat.card B :=
    (CFSG.RankThree.Asc83Table.card_closure_pair_eq_nine (h3 c hcA) (h3 d hdA)
      (hcomm c hcA d hdA) h.ne_one hdc).ge
  have hBT : B ≤ Subgroup.centralizer (T : Set G) := by
    rw [Subgroup.closure_le]
    rintro _ (rfl | rfl)
    · exact Subgroup.mem_centralizer_iff.mpr fun t ht => (hcK t (hTK ht)).symm
    · exact Subgroup.mem_centralizer_iff.mpr fun t ht => (hdK t (hTK ht)).symm
  have hcB : Subgroup.zpowers c ≤ B := by
    rw [Subgroup.zpowers_le]
    exact Subgroup.subset_closure (by simp)
  have hc1' : Subgroup.zpowers c ≠ ⊥ := fun h1 => h.ne_one (by
    have := Subgroup.mem_zpowers c
    rwa [h1, Subgroup.mem_bot] at this)
  set Q := inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (T : Set G)) with hQ
  set R := Q ⊓ Subgroup.centralizer ({b} : Set G) with hRdef
  set V := ⁅R, Subgroup.zpowers c⁆ with hVdef
  obtain ⟨i, j, hi, hj, hbij⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair
    (hcomm c hcA d hdA) (h3 c hcA) (h3 d hdA) hbB
  have hj0 : j ≠ 0 := by
    rintro rfl
    rw [pow_zero, mul_one] at hbij
    have hi0 : ¬ 3 ∣ i := by
      intro hi3
      have : i = 0 := by omega
      apply hb1
      rw [hbij, this, pow_zero]
    have hcmem : c ∈ Subgroup.zpowers b :=
      hbij ▸ Item82OneProof.mem_zpowers_pow_of_not_three_dvd (h3 c hcA) hi0
    apply hV
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro r hr
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hrb : r * b = b * r := Subgroup.mem_centralizer_singleton_iff.mp hr.2
    obtain ⟨m, hm⟩ := hcmem
    have hrc : Commute r c := by
      rw [← hm]
      exact Commute.zpow_right hrb m
    exact (hrc.zpow_right k).eq.symm
  have hLb : L ⊓ Subgroup.centralizer ({b} : Set G) = L ⊓ Subgroup.centralizer ({d} : Set G) := by
    rw [hbij]
    exact inf_centralizer_mul_pow_eq hcy (h3 d hdA) i (by omega)
  have hbA : b ∈ A := hBA hbB
  have hbΓ : IsGammaIndex A L b n := by
    obtain ⟨-, -, -, hcases⟩ := hdΓ
    exact ⟨hbA, hb1, hn1, by rw [hLb]; exact hcases⟩
  obtain ⟨hKmem, -, -⟩ := Item87Proof.residual_of_isGammaIndex h.mem_thetaComponentsAt hbΓ
  rw [hLb] at hKmem
  have hKmem' : K ∈ thetaComponentsIn
      (Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({c} : Set G)) := by
    rwa [inf_comm]
  obtain ⟨X, hX, hKX⟩ := Item87Proof.exists_mem_thetaComponentsAt_of_mem_inf h48 hG hAe
    ⟨4, by norm_num, by rw [hA81]; norm_num⟩ hbA hcA hb1 h.ne_one hKmem'
  refine ⟨X, mem_pairOmega_of_sec8Std hKB hInd h, ⟨n, hbΓ⟩, hX, ?_, ?_⟩
  · rw [hLb]
    exact hKX
  rw [hLb]
  intro hXeq
  have hb3 : b ^ 3 = 1 := h3 b hbA
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using h3 x x.2)⟩
  have hAb : A ≤ Subgroup.centralizer ({b} : Set G) := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hcomm x hx b hbA)
  have hAX : A ≤ Subgroup.normalizer (X : Set G) :=
    Sec11.le_normalizer_of_isPGroup_of_le_centralizer h45 hG hb3 hb1 hA3 hAb X hX
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
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) :=
    (Item87Proof.residual_le _).trans (hLb ▸ inf_le_right)
  have hKTK : ⁅K, T⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk t ht
    rw [commutatorElement_def]
    exact K.mul_mem (K.mul_mem (K.mul_mem hk (hTK ht)) (K.inv_mem hk)) (K.inv_mem (hTK ht))
  have hKT : ¬ ⁅K, T⁆ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({b} : Set G)) := by
    intro hle
    have h1 : ⁅K, T⁆ ≤ inSubgroup (aschbacherSolvableCore 3) K :=
      (le_inf hKTK hle).trans (inf_theta_le_theta hKb)
    exact hT1 (eq_bot_of_isPGroup_two_of_le hT2 (le_theta_of_commutator_le hTK hT2 hNT h1)
      hθKodd)
  have hcθ : c ∈ Sec4.thetaQuotCentralizer X :=
    mem_thetaQuotCentralizer_of_eq_sup (hAX hcA) hcK hKX hXeq
  have hQT : Q ≤ Subgroup.centralizer (T : Set G) := Subgroup.map_subtype_le _
  have hRX : R ≤ Subgroup.normalizer (X : Set G) := by
    intro g hg
    have hgb : g ∈ Subgroup.centralizer ({b} : Set G) := hg.2
    have hgT : g ∈ Subgroup.centralizer (T : Set G) := hQT hg.1
    have hX' := Sec6.map_conj_mem_thetaComponentsAt hgb hX
    have hTX' : T ≤ X.map (MulAut.conj g).toMonoidHom := by
      intro t ht
      have hgt : t * g = g * t := Subgroup.mem_centralizer_iff.mp hgT t ht
      refine ⟨t, hKX (hTK ht), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [← hgt, mul_inv_cancel_right]
    have heq := Item87Proof.eq_of_not_commutator_le hX hX' hKX hTX' hKT
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm
  have hVX : V ≤ Sec4.thetaQuotCentralizer X := by
    rw [hVdef, Subgroup.commutator_le]
    intro r hr z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hck : c ^ k ∈ Sec4.thetaQuotCentralizer X := Subgroup.zpow_mem _ hcθ k
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (Sec6.conj_mem_thetaQuotCentralizer hck (hRX hr))
      (Subgroup.inv_mem _ hck)
  have hVθ : V ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) X : Set G) :=
    fun v hv => Sec6.normalizer_le_normalizer_theta X (Sec6.mem_thetaQuotCentralizer_iff.mp
      (hVX hv)).1
  have hcT : c ∈ Subgroup.centralizer (T : Set G) := hBT (Subgroup.subset_closure (by simp))
  have hcR : c ∈ Subgroup.normalizer (R : Set G) := by
    have hcQ : c ∈ Subgroup.normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (T : Set G))) (Subgroup.le_normalizer hcT)
    have hcb : c ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
      Subgroup.le_normalizer (hAb hcA)
    exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hcQ, hcb⟩
  have hVR : V ≤ R :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp (Subgroup.zpowers_le.mpr hcR)
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hV2 : IsPGroup 2 V := hQ2.to_le (hVR.trans inf_le_left)
  set P := inSubgroup (aschbacherSolvableCore 3) X ⊔ V with hPdef
  have hP3 : ¬ 3 ∣ Nat.card P := by
    intro h3P
    have h1 := h3P.trans (card_sup_dvd_mul_of_le_normalizer _ V hVθ)
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
    · exact hθ3 X h2
    · obtain ⟨k, hk⟩ := hV2.exists_card_eq
      rw [hk] at h2
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h2
      omega
  have hP2 : 2 ∣ Nat.card P := by
    obtain ⟨k, hk⟩ := hV2.exists_card_eq
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hk
      exact hV (Subgroup.eq_bot_of_card_eq V hk)
    have h1 := Subgroup.card_dvd_of_le (le_sup_right : V ≤ P)
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
    intro e he
    have heA : e ∈ A := hEA he
    have heθ := Sec6.normalizer_le_normalizer_theta X (hAX heA)
    have heCT : e ∈ Subgroup.normalizer (Subgroup.centralizer (T : Set G) : Set G) :=
      Source.mem_normalizer_centralizer (hET he)
    have heQ : e ∈ Subgroup.normalizer (Q : Set G) :=
      CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (CFSG.pCore 2 (Subgroup.centralizer (T : Set G))) heCT
    have heCb : e ∈ Subgroup.normalizer (Subgroup.centralizer ({b} : Set G) : Set G) :=
      Subgroup.le_normalizer (hAb heA)
    have heR : e ∈ Subgroup.normalizer (R : Set G) :=
      Subgroup.inf_normalizer_le_normalizer_inf ⟨heQ, heCb⟩
    have hec : e ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) := by
      refine Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => ?_)
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_left (hcomm c hcA e heA) k).eq
    exact mem_normalizer_sup heθ (Source.mem_normalizer_commutator heR hec)
  have hyP : (y : G) ∈ Subgroup.normalizer (P : Set G) := by
    have hyX : (y : G) ∈ X := hKX y.2
    have hyθ := Sec6.le_normalizer_theta X hyX
    refine mem_normalizer_of_conj_mem fun p hp => ?_
    have hle : P ≤ P.comap (MulAut.conj (y : G)).toMonoidHom := by
      refine sup_le (fun t ht => ?_) (fun v hv => ?_)
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hyθ t).mp ht)
      · obtain ⟨-, hvθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp (hVX hv)
        have h1 := hvθ (y : G)⁻¹ (X.inv_mem hyX)
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
