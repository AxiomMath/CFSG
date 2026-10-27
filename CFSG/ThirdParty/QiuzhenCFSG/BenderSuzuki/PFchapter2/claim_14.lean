module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_13
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_2_a
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.claim_1
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_5

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter2

open PFchapter1section1 PFAppendixIII
open PFchapter1section3
open scoped Pointwise

/-!
# Peterfalvi, Part II, Chapter II, Claim (14)
-/

private lemma claim14_centralizer_le_normalizer
    {G : Type*} [Group G] (R : Subgroup G) :
    Subgroup.centralizer (R : Set G) ≤ Subgroup.normalizer (R : Set G) := by
  intro x hxC
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have hxy : y * x = x * y := (Subgroup.mem_centralizer_iff.mp hxC) y hy
    have hconj : x * y * x⁻¹ = y := by
      calc
        x * y * x⁻¹ = (x * y) * x⁻¹ := by simp [mul_assoc]
        _ = (y * x) * x⁻¹ := by rw [hxy.symm]
        _ = y := by simp [mul_assoc]
    simpa [hconj] using hy
  · intro hy
    have hxinvC : x⁻¹ ∈ Subgroup.centralizer (R : Set G) :=
      (Subgroup.inv_mem_iff (H := Subgroup.centralizer (R : Set G))).2 hxC
    have hy' : x⁻¹ * (x * y * x⁻¹) * x ∈ R := by
      have hyc : x * y * x⁻¹ ∈ R := hy
      have hxy : (x * y * x⁻¹) * x⁻¹ = x⁻¹ * (x * y * x⁻¹) :=
        (Subgroup.mem_centralizer_iff.mp hxinvC) (x * y * x⁻¹) hyc
      have hconj : x⁻¹ * (x * y * x⁻¹) * x = x * y * x⁻¹ := by
        calc
          x⁻¹ * (x * y * x⁻¹) * x =
              (x⁻¹ * (x * y * x⁻¹)) * x := by simp [mul_assoc]
          _ = ((x * y * x⁻¹) * x⁻¹) * x := by rw [hxy]
          _ = x * y * x⁻¹ := by simp [mul_assoc]
      simpa [hconj] using hyc
    simpa [mul_assoc] using hy'

private lemma claim14_mem_normalizer_centralizer_of_mem_normalizer
    {G : Type*} [Group G] (P : Subgroup G) {x : G}
    (hx : x ∈ Subgroup.normalizer (P : Set G)) :
    x ∈ Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  constructor
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hzP
    have hzP' : x⁻¹ * z * x ∈ P := by
      apply (hx (x⁻¹ * z * x)).mpr
      simpa [mul_assoc] using hzP
    calc
      z * (x * y * x⁻¹) = x * ((x⁻¹ * z * x) * y) * x⁻¹ := by
        simp [mul_assoc]
      _ = x * (y * (x⁻¹ * z * x)) * x⁻¹ := by rw [hy _ hzP']
      _ = (x * y * x⁻¹) * z := by simp [mul_assoc]
  · intro hy
    rw [Subgroup.mem_centralizer_iff] at hy ⊢
    intro z hzP
    have hxzxP : x * z * x⁻¹ ∈ P := (hx z).mp hzP
    have hcomm := hy (x * z * x⁻¹) hxzxP
    have hcancel := congrArg (fun w : G => x⁻¹ * w * x) hcomm
    simpa [mul_assoc] using hcancel

private lemma claim14_conjugate_mem_sup_of_normalizes
    {G : Type*} [Group G] {A B : Subgroup G} {x y : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G))
    (hy : y ∈ A ⊔ B) :
    x * y * x⁻¹ ∈ A ⊔ B := by
  rw [Subgroup.sup_eq_closure] at hy ⊢
  refine Subgroup.closure_induction ?_ ?_ ?_ ?_ hy
  · intro z hz
    rcases hz with hzA | hzB
    · exact
        Subgroup.subset_closure
          (Or.inl ((Subgroup.mem_normalizer_iff.mp hA z).1 hzA))
    · exact
        Subgroup.subset_closure
          (Or.inr ((Subgroup.mem_normalizer_iff.mp hB z).1 hzB))
  · simp
  · intro a b _ha _hb hca hcb
    simpa [mul_assoc] using
      (Subgroup.closure ((A : Set G) ∪ (B : Set G))).mul_mem hca hcb
  · intro a _ha hca
    simpa [mul_assoc] using
      (Subgroup.closure ((A : Set G) ∪ (B : Set G))).inv_mem hca

private lemma claim14_mem_normalizer_sup_of_normalizes
    {G : Type*} [Group G] {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G))
    (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · exact claim14_conjugate_mem_sup_of_normalizes hA hB
  · intro hy
    have hAinv : x⁻¹ ∈ Subgroup.normalizer (A : Set G) :=
      (Subgroup.normalizer (A : Set G)).inv_mem hA
    have hBinv : x⁻¹ ∈ Subgroup.normalizer (B : Set G) :=
      (Subgroup.normalizer (B : Set G)).inv_mem hB
    have h :=
      claim14_conjugate_mem_sup_of_normalizes (A := A) (B := B)
        (x := x⁻¹) (y := x * y * x⁻¹) hAinv hBinv hy
    simpa [mul_assoc] using h

private lemma claim14_rightConjugate_eq_self_of_mem_normalizer
    {G : Type*} [Group G] {H : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (H : Set G)) :
    rightConjugate H g = H := by
  ext x
  constructor
  · intro hx
    rcases hx with ⟨y, hy, rfl⟩
    have hg_inv : g⁻¹ ∈ Subgroup.normalizer (H : Set G) :=
      (Subgroup.normalizer (H : Set G)).inv_mem hg
    exact (Subgroup.mem_normalizer_iff.mp hg_inv y).1 hy
  · intro hx
    refine ⟨g * x * g⁻¹, ?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp hg x).1 hx
    · calc
        (MulAut.conj g⁻¹) (g * x * g⁻¹) =
            g⁻¹ * (g * x * g⁻¹) * (g⁻¹)⁻¹ := rfl
        _ = x := by group

private lemma claim14_sigma_le_normalizer_R_of_R_structure
    {G : Type*} [Group G]
    (Q W P Sigma R : Subgroup G) (p : ℕ)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hR : ∃ T : Subgroup G,
      R = T ⊔ P ∧
        Disjoint T P ∧
          T ≤ Subgroup.centralizer (P : Set G) ∧
            (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
              W ⊓ Subgroup.centralizer (P : Set G)) ≤
                Subgroup.normalizer (T : Set G) ∧
              Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
                ∀ A B : Subgroup G,
                  A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
                    ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
                      ∃! c : G,
                        c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                          B = rightConjugate A c) :
    Sigma ≤ Subgroup.normalizer (R : Set G) := by
  rcases hR with
    ⟨T, hR_eq, _hT_disj_P, _hT_le_CP, hQW_norm_T, _hT_disj_CQ,
      _horder_p_regular⟩
  intro x hx
  have hxSigma : x ∈ W ⊓ Subgroup.centralizer (P : Set G) := by
    simpa [hSigma] using hx
  have hx_norm_T : x ∈ Subgroup.normalizer (T : Set G) := by
    exact hQW_norm_T (Subgroup.mem_sup_right hxSigma)
  have hx_norm_P : x ∈ Subgroup.normalizer (P : Set G) :=
    claim14_centralizer_le_normalizer P hxSigma.2
  have hx_norm_sup :
      x ∈ Subgroup.normalizer ((T ⊔ P : Subgroup G) : Set G) :=
    claim14_mem_normalizer_sup_of_normalizes hx_norm_T hx_norm_P
  simpa [hR_eq] using hx_norm_sup

/-- Claim (2)(b) chooses the same distinguished involution inside `C_G(P)`:
the uniqueness in Chapter I, Proposition 4(b), identifies its local pair with
the chapter pair `(s, r)`. -/
private lemma claim14_s_mem_centralizer_P
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p)) :
    s ∈ Subgroup.centralizer (P : Set G) := by
  classical
  let C : Subgroup G := Subgroup.centralizer (P : Set G)
  let ΩP : Type _ := {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω P}
  letI : MulAction C ΩP := fixedPointCentralizerAction G Ω P
  let HP : Subgroup C := H.comap C.subtype
  let DP : Subgroup C := D.comap C.subtype
  let QP : Subgroup C := Q.comap C.subtype
  let tP : C :=
    ⟨t, t_mem_centralizer_of_le_peterfalviV D V P t hch.B1.P_le_V
      hch.section3.section2.V_eq⟩
  have h2a := claim_2_a H D Q K V W Q0 S Q1 P t s p hch
  have hA1P : HypothesisA1 C ΩP HP DP QP tP := by
    simpa [C, ΩP, HP, DP, QP, tP] using h2a.1
  obtain ⟨pair, hpair, _hpair_unique⟩ := proposition_4_b HP DP QP tP hA1P
  obtain ⟨globalPair, _hglobalPair, hglobalUnique⟩ :=
    proposition_4_b H D Q t hch.section3.section2.hA.A1
  obtain ⟨r, hrQ, hrelation⟩ := hch.section3.2.2.2
  have horiginal : (s, r) = globalPair :=
    hglobalUnique (s, r)
      ⟨hch.section3.2.1, hch.section3.2.2.1, hrQ, hrelation⟩
  let pairG : G × G := ((pair.1 : C), (pair.2 : C))
  have hpairGData :
      pairG.1 ∈ H ∧ PFAppendixIII.IsInvolution pairG.1 ∧ pairG.2 ∈ Q ∧
        t * pairG.1 * t = pairG.2⁻¹ * t * pairG.2 := by
    refine ⟨hpair.1, ?_, hpair.2.2.1, ?_⟩
    · constructor
      · intro hone
        exact hpair.2.1.ne_one (Subtype.ext hone)
      · exact congrArg C.subtype hpair.2.1.sq_eq_one
    · simpa [pairG, tP] using congrArg C.subtype hpair.2.2.2
  have hpairGlobal : pairG = globalPair :=
    hglobalUnique pairG hpairGData
  have hpairFirst : (pair.1 : G) = s :=
    congrArg Prod.fst (hpairGlobal.trans horiginal.symm)
  rw [← hpairFirst]
  exact pair.1.property


/-- The inverse image of `A₃` under the three-point normalizer action is the
normal 3-subgroup lying one factor of three above the action kernel. -/
private lemma claim14_exists_a3_preimage
    {G : Type*} [Group G] [Finite G]
    (K N : Subgroup G) (hK_le_N : K ≤ N)
    (phi : N →* Equiv.Perm (Fin 3)) (hphi : Function.Surjective phi)
    (hker : MonoidHom.ker phi = K.subgroupOf N) (hKp : IsPGroup 3 K)
    (s : G) (hsN : s ∈ N) (hsI : PFAppendixIII.IsInvolution s) :
    ∃ R1 : Subgroup G,
      IsPGroup 3 R1 ∧
        K ≤ R1 ∧
          R1 ≤ N ∧
            N ≤ Subgroup.normalizer (R1 : Set G) ∧
              (K.subgroupOf R1).index = 3 ∧
                (R1.subgroupOf N).index = 2 ∧
                  N = R1 ⊔ Subgroup.closure ({s} : Set G) ∧
                    Disjoint R1 (Subgroup.closure ({s} : Set G)) := by
  classical
  let A3 : Subgroup (Equiv.Perm (Fin 3)) := alternatingGroup (Fin 3)
  let L : Subgroup N := A3.comap phi
  let R1 : Subgroup G := L.map N.subtype
  have hA3card : Nat.card A3 = 3 := by
    calc
      Nat.card A3 = (Nat.card (Fin 3)).factorial / 2 := by
        dsimp [A3]
        exact nat_card_alternatingGroup
      _ = 3 := by norm_num [Nat.factorial]
  have hA3p : IsPGroup 3 A3 :=
    IsPGroup.of_card (n := 1) (by simpa using hA3card)
  have hKsubp : IsPGroup 3 (K.subgroupOf N) :=
    hKp.of_equiv (Subgroup.subgroupOfEquivOfLe hK_le_N).symm
  have hkerp : IsPGroup 3 (MonoidHom.ker phi) := by
    rw [hker]
    exact hKsubp
  have hLp : IsPGroup 3 L :=
    hA3p.comap_of_ker_isPGroup phi hkerp
  have hR1p : IsPGroup 3 R1 := hLp.map N.subtype
  have hker_le_L : MonoidHom.ker phi ≤ L := by
    exact Subgroup.ker_le_comap phi A3
  have hKsub_le_L : K.subgroupOf N ≤ L := by
    rw [← hker]
    exact hker_le_L
  have hK_le_R1 : K ≤ R1 := by
    have hmap :
        (K.subgroupOf N).map N.subtype ≤ L.map N.subtype :=
      Subgroup.map_mono hKsub_le_L
    rw [Subgroup.map_subgroupOf_eq_of_le hK_le_N] at hmap
    exact hmap
  have hR1_le_N : R1 ≤ N := by
    exact Subgroup.map_subtype_le L
  have hR1sub_eq : R1.subgroupOf N = L := by
    ext x
    constructor
    · intro hx
      change (x : G) ∈ L.map N.subtype at hx
      rcases hx with ⟨y, hyL, hyx⟩
      have hyx' : y = x := Subtype.ext hyx
      simpa [hyx'] using hyL
    · intro hx
      change (x : G) ∈ L.map N.subtype
      exact ⟨x, hx, rfl⟩
  have hLnormal : L.Normal := by
    dsimp [L]
    infer_instance
  have hN_le_norm : N ≤ Subgroup.normalizer (R1 : Set G) := by
    apply (Subgroup.normal_subgroupOf_iff_le_normalizer hR1_le_N).mp
    rw [hR1sub_eq]
    exact hLnormal
  have hmapL : L.map phi = A3 := by
    exact Subgroup.map_comap_eq_self_of_surjective hphi A3
  have hlocal_rel : (K.subgroupOf N).relIndex L = 3 := by
    calc
      (K.subgroupOf N).relIndex L = (MonoidHom.ker phi).relIndex L := by rw [hker]
      _ = Nat.card (L.map phi) := Subgroup.relIndex_ker L phi
      _ = Nat.card A3 := by rw [hmapL]
      _ = 3 := hA3card
  have hKindex : (K.subgroupOf R1).index = 3 := by
    calc
      (K.subgroupOf R1).index = K.relIndex R1 := rfl
      _ = ((K.subgroupOf N).map N.subtype).relIndex (L.map N.subtype) := by
        change K.relIndex (L.map N.subtype) = _
        rw [Subgroup.map_subgroupOf_eq_of_le hK_le_N]
      _ = (K.subgroupOf N).relIndex L :=
        Subgroup.relIndex_map_map_of_injective
          (K.subgroupOf N) L Subtype.coe_injective
      _ = 3 := hlocal_rel
  have hR1index : (R1.subgroupOf N).index = 2 := by
    rw [hR1sub_eq]
    exact (Subgroup.index_comap_of_surjective (H := A3) hphi).trans
      alternatingGroup.index_eq_two
  let sN : N := ⟨s, hsN⟩
  have hs_not_R1 : s ∉ R1 := by
    intro hsR1
    let sR1 : R1 := ⟨s, hsR1⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hR1p) sR1
    have hs_order : orderOf s = 2 :=
      orderOf_eq_prime hsI.sq_eq_one hsI.ne_one
    have hpow : 2 = 3 ^ k := by
      calc
        2 = orderOf s := hs_order.symm
        _ = orderOf sR1 := by
          simp [sR1]
        _ = 3 ^ k := hk
    cases k with
    | zero => norm_num at hpow
    | succ k =>
        rw [pow_succ] at hpow
        have hpos : 0 < 3 ^ k := pow_pos (by decide) k
        omega
  have hsN_not_L : sN ∉ L := by
    intro hsL
    apply hs_not_R1
    have hsLocal : sN ∈ R1.subgroupOf N := by
      rw [hR1sub_eq]
      exact hsL
    exact hsLocal
  have hs_sign_ne : Equiv.Perm.sign (phi sN) ≠ 1 := by
    intro hsSign
    apply hsN_not_L
    change phi sN ∈ A3
    exact Equiv.Perm.mem_alternatingGroup.mpr hsSign
  have hs_sign : Equiv.Perm.sign (phi sN) = -1 := by
    rcases Int.units_eq_one_or (Equiv.Perm.sign (phi sN)) with hsOne | hsNeg
    · exact (hs_sign_ne hsOne).elim
    · exact hsNeg
  have hsplit : N = R1 ⊔ Subgroup.closure ({s} : Set G) := by
    apply le_antisymm
    · intro n hnN
      let nN : N := ⟨n, hnN⟩
      by_cases hnL : nN ∈ L
      · apply Subgroup.mem_sup_left
        have hnLocal : nN ∈ R1.subgroupOf N := by
          rw [hR1sub_eq]
          exact hnL
        exact hnLocal
      · have hn_sign_ne : Equiv.Perm.sign (phi nN) ≠ 1 := by
          intro hnSign
          apply hnL
          change phi nN ∈ A3
          exact Equiv.Perm.mem_alternatingGroup.mpr hnSign
        have hn_sign : Equiv.Perm.sign (phi nN) = -1 := by
          rcases Int.units_eq_one_or (Equiv.Perm.sign (phi nN)) with hnOne | hnNeg
          · exact (hn_sign_ne hnOne).elim
          · exact hnNeg
        have hnsL : nN * sN ∈ L := by
          change phi (nN * sN) ∈ A3
          rw [Equiv.Perm.mem_alternatingGroup, map_mul, map_mul,
            hn_sign, hs_sign]
          exact Int.units_mul_self (-1)
        have hnsR1 : n * s ∈ R1 := by
          have hnsLocal : nN * sN ∈ R1.subgroupOf N := by
            rw [hR1sub_eq]
            exact hnsL
          exact hnsLocal
        have hsClosure : s ∈ Subgroup.closure ({s} : Set G) :=
          Subgroup.subset_closure (Set.mem_singleton s)
        have hprod :
            (n * s) * s ∈ R1 ⊔ Subgroup.closure ({s} : Set G) :=
          (R1 ⊔ Subgroup.closure ({s} : Set G)).mul_mem
            (Subgroup.mem_sup_left hnsR1) (Subgroup.mem_sup_right hsClosure)
        have hss : s * s = 1 := by simpa [pow_two] using hsI.sq_eq_one
        simpa [mul_assoc, hss] using hprod
    · exact sup_le hR1_le_N
        ((Subgroup.closure_le N).2 (by simpa [Set.singleton_subset_iff] using hsN))
  have hclosure2 : IsPGroup 2 (Subgroup.closure ({s} : Set G)) := by
    have hzpowers2 : IsPGroup 2 (Subgroup.zpowers s) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, orderOf_eq_prime hsI.sq_eq_one hsI.ne_one,
        pow_one]
    rw [Subgroup.zpowers_eq_closure] at hzpowers2
    exact hzpowers2
  letI : Fact (Nat.Prime 2) := ⟨by decide⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hdisjoint : Disjoint R1 (Subgroup.closure ({s} : Set G)) :=
    IsPGroup.disjoint_of_ne 3 2 (by decide) R1
      (Subgroup.closure ({s} : Set G)) hR1p hclosure2
  exact ⟨R1, hR1p, hK_le_R1, hR1_le_N, hN_le_norm, hKindex,
    hR1index, hsplit, hdisjoint⟩

private lemma claim14_s_mem_normalizer_R
    {G : Type*} [Group G]
    (T P R : Subgroup G) (s : G)
    (hsI : PFAppendixIII.IsInvolution s)
    (hsC : s ∈ Subgroup.centralizer (P : Set G))
    (hT_inverted : ∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹)
    (hR : R = T ⊔ P) :
    s ∈ Subgroup.normalizer (R : Set G) := by
  have hs_inv : s⁻¹ = s := hsI.inv_eq_self
  have hs_norm_T : s ∈ Subgroup.normalizer (T : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hyT
      have hinv := hT_inverted y hyT
      have hconj : s * y * s⁻¹ = y⁻¹ := by
        simpa [rightConjugateElem, hs_inv] using hinv
      rw [hconj]
      exact T.inv_mem hyT
    · intro hconjT
      have hinv := hT_inverted (s * y * s⁻¹) hconjT
      have hy_eq : y = (s * y * s⁻¹)⁻¹ := by
        calc
          y = s⁻¹ * (s * y * s⁻¹) * s := by simp [mul_assoc]
          _ = (s * y * s⁻¹)⁻¹ := hinv
      rw [hy_eq]
      exact T.inv_mem hconjT
  have hs_norm_P : s ∈ Subgroup.normalizer (P : Set G) :=
    claim14_centralizer_le_normalizer P hsC
  have hs_norm_R :
      s ∈ Subgroup.normalizer ((T ⊔ P : Subgroup G) : Set G) :=
    claim14_mem_normalizer_sup_of_normalizes hs_norm_T hs_norm_P
  simpa [hR] using hs_norm_R

private lemma claim14_s_mem_normalizer_R_sup_Sigma
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q V W P Sigma R : Subgroup G) (t s : G)
    (hA1 : PFchapter1section1.HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : PFAppendixIII.IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)
    (hV : V = PFchapter1section1.peterfalviV D t)
    (hW_le_V : W ≤ V)
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hsC : s ∈ Subgroup.centralizer (P : Set G))
    (hs_norm_R : s ∈ Subgroup.normalizer (R : Set G)) :
    s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) := by
  have hV_eq : V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
    calc
      V = PFchapter1section1.peterfalviV D t := hV
      _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
        (proposition_5 H D Q t s hA1 hsH hsI hsStructure).1
  have hsC_W : s ∈ Subgroup.centralizer (W : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro w hwW
    have hwCs : w ∈ Subgroup.centralizer ({s} : Set G) := by
      have hwV : w ∈ V := hW_le_V hwW
      rw [hV_eq] at hwV
      exact hwV.2
    exact Subgroup.mem_centralizer_singleton_iff.mp hwCs
  have hs_norm_W : s ∈ Subgroup.normalizer (W : Set G) :=
    claim14_centralizer_le_normalizer W hsC_W
  have hs_norm_P : s ∈ Subgroup.normalizer (P : Set G) :=
    claim14_centralizer_le_normalizer P hsC
  have hs_norm_CP :
      s ∈ Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) :=
    claim14_mem_normalizer_centralizer_of_mem_normalizer P hs_norm_P
  have hs_norm_Sigma : s ∈ Subgroup.normalizer (Sigma : Set G) := by
    have hs_inf :
        s ∈ Subgroup.normalizer (W : Set G) ⊓
          Subgroup.normalizer (Subgroup.centralizer (P : Set G) : Set G) :=
      ⟨hs_norm_W, hs_norm_CP⟩
    have := Subgroup.inf_normalizer_le_normalizer_inf hs_inf
    simpa [hSigma] using this
  exact claim14_mem_normalizer_sup_of_normalizes hs_norm_R hs_norm_Sigma

private lemma claim14_normalizer_le_normalizer_map_subtype_of_characteristic
    {G : Type*} [Group G] (H : Subgroup G) (K : Subgroup H)
    [K.Characteristic] :
    Subgroup.normalizer (H : Set G) ≤
      Subgroup.normalizer (K.map H.subtype : Set G) := by
  classical
  refine subgroup_le_normalizer_of_conj_mem (K.map H.subtype)
    (Subgroup.normalizer (H : Set G)) ?_
  intro g x hx
  rcases Subgroup.mem_map.mp hx with ⟨xH, hxK, rfl⟩
  let gH : Subgroup.normalizer (H : Set G) := ⟨g, g.property⟩
  have hfix :
      Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K = K :=
    (inferInstance : K.Characteristic).fixed (Subgroup.normalizerMonoidHom H gH)
  have hxComap :
      xH ∈ Subgroup.comap (Subgroup.normalizerMonoidHom H gH).toMonoidHom K := by
    rw [hfix]
    exact hxK
  have hxImage : (Subgroup.normalizerMonoidHom H gH) xH ∈ K := hxComap
  exact ⟨(Subgroup.normalizerMonoidHom H gH) xH, hxImage, by
    simp [gH, mul_assoc, Subgroup.normalizerMonoidHom_apply_apply_coe]⟩

private lemma claim14_pgroup_le_centralizer_of_commutator_eq
    {G : Type*} [Group G] [Finite G]
    (K Z R1 : Subgroup G) (hZcard : Nat.card Z = 3)
    (hcomm : ⁅K, K⁆ = Z) (hR1p : IsPGroup 3 R1)
    (hR1_norm_K : R1 ≤ Subgroup.normalizer (K : Set G)) :
    R1 ≤ Subgroup.centralizer (Z : Set G) := by
  classical
  have hnorm_comm :
      Subgroup.normalizer (K : Set G) ≤
        Subgroup.normalizer ((⁅K, K⁆ : Subgroup G) : Set G) := by
    haveI : (_root_.commutator K).Characteristic := by infer_instance
    have hnorm :=
      claim14_normalizer_le_normalizer_map_subtype_of_characteristic
        K (_root_.commutator K)
    rw [Subgroup.map_subtype_commutator] at hnorm
    exact hnorm
  have hR1_norm_Z : R1 ≤ Subgroup.normalizer (Z : Set G) := by
    rw [← hcomm]
    exact hR1_norm_K.trans hnorm_comm
  let incl : R1 →* Subgroup.normalizer (Z : Set G) :=
    Subgroup.inclusion hR1_norm_Z
  let autHom : R1 →* MulAut Z := Z.normalizerMonoidHom.comp incl
  let A : Subgroup (MulAut Z) := autHom.range
  have hAp : IsPGroup 3 A :=
    hR1p.of_surjective autHom.rangeRestrict autHom.rangeRestrict_surjective
  have hZcyclic : IsCyclic Z := by
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    exact isCyclic_of_prime_card hZcard
  have hAutCard : Nat.card (MulAut Z) = 2 := by
    rw [hZcyclic.card_mulAut, hZcard, Nat.totient_prime (by decide)]
  have hA_dvd_two : Nat.card A ∣ 2 := by
    simpa [hAutCard] using A.card_subgroup_dvd_card
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  obtain ⟨k, hAcard⟩ := hAp.exists_card_eq
  have hAcard_one : Nat.card A = 1 := by
    cases k with
    | zero => simpa using hAcard
    | succ k =>
        have hle : 3 ^ (k + 1) ≤ 2 := by
          apply Nat.le_of_dvd (by decide)
          rw [← hAcard]
          exact hA_dvd_two
        rw [pow_succ] at hle
        have hpos : 0 < 3 ^ k := pow_pos (by decide) k
        omega
  have hAbot : A = ⊥ := Subgroup.card_eq_one.mp hAcard_one
  intro r hrR1
  let rR1 : R1 := ⟨r, hrR1⟩
  let rN : Subgroup.normalizer (Z : Set G) := ⟨r, hR1_norm_Z hrR1⟩
  have hact_mem : autHom rR1 ∈ A := by
    exact ⟨rR1, rfl⟩
  have hact : autHom rR1 = 1 := by
    rw [hAbot] at hact_mem
    exact Subgroup.mem_bot.mp hact_mem
  have hrNker : rN ∈ Z.normalizerMonoidHom.ker := by
    rw [MonoidHom.mem_ker]
    change Z.normalizerMonoidHom (incl rR1) = 1 at hact
    have hincl_eq : incl rR1 = rN := by
      apply Subtype.ext
      rfl
    rw [hincl_eq] at hact
    exact hact
  rw [Subgroup.normalizerMonoidHom_ker] at hrNker
  exact hrNker

private lemma claim14_center_R_contains_Z1_sup_P
    {G F : Type*} [Group G] [PFAppendixII.RightNearField F]
    (T P Z1 R : Subgroup G)
    (addEquiv : Multiplicative F ≃* T)
    (hPcard : Nat.card P = 3)
    (hT_le_CP : T ≤ Subgroup.centralizer (P : Set G))
    (hR : R = T ⊔ P) (hZ1_le_T : Z1 ≤ T) :
    Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) := by
  letI : IsMulCommutative T :=
    ⟨⟨fun x y => by
      obtain ⟨a, rfl⟩ := addEquiv.surjective x
      obtain ⟨b, rfl⟩ := addEquiv.surjective y
      rw [← map_mul, ← map_mul, mul_comm]⟩⟩
  letI : Fact (Nat.Prime 3) := ⟨by decide⟩
  letI : IsMulCommutative P :=
    (isCyclic_of_prime_card hPcard).isMulCommutative
  have hT_le_CT : T ≤ Subgroup.centralizer (T : Set G) := by
    intro x hxT
    rw [Subgroup.mem_centralizer_iff]
    intro y hyT
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := T)).comm ⟨y, hyT⟩ ⟨x, hxT⟩)
  have hP_le_CP : P ≤ Subgroup.centralizer (P : Set G) := by
    intro x hxP
    rw [Subgroup.mem_centralizer_iff]
    intro y hyP
    exact congrArg Subtype.val
      ((IsMulCommutative.is_comm (M := P)).comm ⟨y, hyP⟩ ⟨x, hxP⟩)
  have hP_le_CT : P ≤ Subgroup.centralizer (T : Set G) := by
    intro x hxP
    rw [Subgroup.mem_centralizer_iff]
    intro y hyT
    exact ((Subgroup.mem_centralizer_iff.mp (hT_le_CP hyT)) x hxP).symm
  have hT_le_center_sup :
      T ≤ Subgroup.centralizer ((T ⊔ P : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_sup_of_le_centralizers hT_le_CT hT_le_CP
  have hP_le_center_sup :
      P ≤ Subgroup.centralizer ((T ⊔ P : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_sup_of_le_centralizers hP_le_CT hP_le_CP
  have hR_le_center : R ≤ Subgroup.centralizer (R : Set G) := by
    rw [hR]
    exact sup_le hT_le_center_sup hP_le_center_sup
  have hT_le_R : T ≤ R := by
    rw [hR]
    exact le_sup_left
  have hP_le_R : P ≤ R := by
    rw [hR]
    exact le_sup_right
  apply sup_le
  · intro z hzZ1
    have hzR : z ∈ R := hT_le_R (hZ1_le_T hzZ1)
    exact ⟨hzR, hR_le_center hzR⟩
  · intro z hzP
    have hzR : z ∈ R := hP_le_R hzP
    exact ⟨hzR, hR_le_center hzR⟩

private theorem claim14_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
    {G : Type*} [Group G] (A B : Subgroup G)
    (hnorm : B ≤ Subgroup.normalizer (A : Set G))
    (hdisj : Disjoint A B) :
    Nat.card (A ⊔ B : Subgroup G) = Nat.card A * Nat.card B := by
  let toSup : A × B → ↥(A ⊔ B) := fun z =>
    ⟨(z.1 : G) * (z.2 : G),
      Subgroup.mul_mem_sup z.1.property z.2.property⟩
  have hinj : Function.Injective toSup := by
    intro x y hxy
    apply Subgroup.mul_injective_of_disjoint hdisj
    exact congrArg Subtype.val hxy
  have hsurj : Function.Surjective toSup := by
    intro x
    have hx : (x : G) ∈ (A : Set G) * (B : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left A B hnorm]
      exact x.property
    rcases hx with ⟨a, ha, b, hb, hab⟩
    exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), Subtype.ext hab⟩
  calc
    Nat.card (A ⊔ B : Subgroup G) = Nat.card (A × B) :=
      Nat.card_congr (Equiv.ofBijective toSup ⟨hinj, hsurj⟩).symm
    _ = Nat.card A * Nat.card B := Nat.card_prod A B

private theorem claim14_center_eq_of_index_nine_of_noncomm
    {G : Type*} [Group G] [Finite G] (X C0 : Subgroup G)
    (hC0center : C0 ≤ X ⊓ Subgroup.centralizer (X : Set G))
    (hindex : (C0.subgroupOf X).index = 9)
    (hnoncomm : ¬ IsMulCommutative X) :
    X ⊓ Subgroup.centralizer (X : Set G) = C0 := by
  let C0X : Subgroup X := C0.subgroupOf X
  let Z : Subgroup X := Subgroup.center X
  have hC0X_le_Z : C0X ≤ Z := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hC0center hx).2) y y.property
  have hZindex_dvd : Z.index ∣ 9 := by
    rw [← hindex]
    exact Subgroup.index_dvd_of_le hC0X_le_Z
  have hZindex_dvd_pow : Z.index ∣ 3 ^ 2 := by
    norm_num at hZindex_dvd ⊢
    exact hZindex_dvd
  obtain ⟨k, hk, hZindex_pow⟩ :=
    (Nat.dvd_prime_pow Nat.prime_three).mp hZindex_dvd_pow
  have hk_cases : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  have hZindex : Z.index = 9 := by
    rcases hk_cases with rfl | rfl | rfl
    · have hZtop : Z = ⊤ := Subgroup.index_eq_one.mp (by
        simpa using hZindex_pow)
      exfalso
      apply hnoncomm
      refine ⟨⟨fun a b => ?_⟩⟩
      have hbZ : b ∈ Z := by rw [hZtop]; exact Subgroup.mem_top b
      exact Subgroup.mem_center_iff.mp hbZ a
    · have hZthree : Z.index = 3 := by simpa using hZindex_pow
      letI : Z.Normal := by dsimp [Z]; infer_instance
      have hquot_card : Nat.card (X ⧸ Z) = 3 := by
        simpa only [Subgroup.index] using hZthree
      letI : IsCyclic (X ⧸ Z) :=
        isCyclic_of_prime_card hquot_card
      exfalso
      apply hnoncomm
      refine ⟨⟨fun a b => ?_⟩⟩
      exact
        ((QuotientGroup.mk' Z).isMulCommutative_of_isCyclic_of_ker_le_center
          (by rw [QuotientGroup.ker_mk'])).is_comm.comm a b
    · simpa using hZindex_pow
  have hrel_one : C0X.relIndex Z = 1 := by
    have hmul := Subgroup.relIndex_mul_index hC0X_le_Z
    rw [hZindex, hindex] at hmul
    omega
  have hZ_le_C0X : Z ≤ C0X := Subgroup.relIndex_eq_one.mp hrel_one
  have hC0X_eq_Z : C0X = Z := le_antisymm hC0X_le_Z hZ_le_C0X
  apply le_antisymm
  · intro x hx
    let xX : X := ⟨x, hx.1⟩
    have hxZ : xX ∈ Z := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hx.2) y y.property
    rw [← hC0X_eq_Z] at hxZ
    exact hxZ
  · exact hC0center

private theorem claim14_commutator_eq_of_two_index_nine
    {G : Type*} [Group G] [Finite G]
    (X C0 T Z0 : Subgroup G)
    (hC0center : C0 ≤ X ⊓ Subgroup.centralizer (X : Set G))
    (hC0index : (C0.subgroupOf X).index = 9)
    (_hT_le_X : T ≤ X)
    (hT_norm : X ≤ Subgroup.normalizer (T : Set G))
    (hTindex : (T.subgroupOf X).index = 9)
    (hinter : T ⊓ C0 = Z0)
    (hZ0_le_X : Z0 ≤ X) (hZ0card : Nat.card Z0 = 3)
    (hnoncomm : ¬ IsMulCommutative X) :
    ⁅X, X⁆ = Z0 := by
  let C0X : Subgroup X := C0.subgroupOf X
  let TX : Subgroup X := T.subgroupOf X
  let Z0X : Subgroup X := Z0.subgroupOf X
  have hC0X_le_center : C0X ≤ Subgroup.center X := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hC0center hx).2) y y.property
  letI : C0X.Normal := ⟨by
    intro n hn g
    have hnZ := hC0X_le_center hn
    have hcomm := Subgroup.mem_center_iff.mp hnZ g
    have hconj : g * n * g⁻¹ = n := by
      calc
        g * n * g⁻¹ = (g * n) * g⁻¹ := by simp [mul_assoc]
        _ = (n * g) * g⁻¹ := by rw [hcomm]
        _ = n := by simp [mul_assoc]
    rw [hconj]
    exact hn⟩
  letI : TX.Normal := ⟨by
    intro n hn g
    exact (Subgroup.mem_normalizer_iff.mp (hT_norm g.property) n).1 hn⟩
  have hC0quot_card : Nat.card (X ⧸ C0X) = 3 ^ 2 := by
    simpa [C0X, Subgroup.index] using hC0index
  have hTquot_card : Nat.card (X ⧸ TX) = 3 ^ 2 := by
    simpa [TX, Subgroup.index] using hTindex
  have hC0quot_comm : IsMulCommutative (X ⧸ C0X) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hC0quot_card
  have hTquot_comm : IsMulCommutative (X ⧸ TX) :=
    IsPGroup.isMulCommutative_of_card_eq_prime_sq hTquot_card
  have hcomm_le_C0X : _root_.commutator X ≤ C0X :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hC0quot_comm
  have hcomm_le_TX : _root_.commutator X ≤ TX :=
    Subgroup.Normal.quotient_commutative_iff_commutator_le.mp hTquot_comm
  have hInf : C0X ⊓ TX = Z0X := by
    ext x
    change ((x : G) ∈ C0 ∧ (x : G) ∈ T) ↔ (x : G) ∈ Z0
    have hx := congrArg (fun A : Subgroup G => (x : G) ∈ A) hinter
    simpa [and_comm] using hx
  have hcomm_le_Z0X : _root_.commutator X ≤ Z0X := by
    rw [← hInf]
    exact le_inf hcomm_le_C0X hcomm_le_TX
  have hcomm_ne_bot : _root_.commutator X ≠ ⊥ := by
    intro hbot
    have hcenter_top : Subgroup.center X = ⊤ :=
      (commutator_eq_bot_iff_center_eq_top (G := X)).mp hbot
    apply hnoncomm
    refine ⟨⟨fun a b => ?_⟩⟩
    have hbZ : b ∈ Subgroup.center X := by
      rw [hcenter_top]
      exact Subgroup.mem_top b
    exact Subgroup.mem_center_iff.mp hbZ a
  have hZ0Xcard : Nat.card Z0X = 3 := by
    calc
      Nat.card Z0X = Nat.card Z0 :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ0_le_X).toEquiv
      _ = 3 := hZ0card
  letI : Fact (Nat.card Z0X).Prime := ⟨by
    rw [hZ0Xcard]
    exact Nat.prime_three⟩
  let D0 : Subgroup Z0X := (_root_.commutator X).subgroupOf Z0X
  have hD0_ne_bot : D0 ≠ ⊥ := by
    intro hD0bot
    apply hcomm_ne_bot
    ext x
    constructor
    · intro hx
      have hxD0 : (⟨x, hcomm_le_Z0X hx⟩ : Z0X) ∈ D0 := hx
      rw [hD0bot] at hxD0
      exact congrArg Subtype.val (Subgroup.mem_bot.mp hxD0)
    · intro hx
      have hxOne : x = 1 := Subgroup.mem_bot.mp hx
      rw [hxOne]
      exact (_root_.commutator X).one_mem
  have hD0top : D0 = ⊤ :=
    (D0.eq_bot_or_eq_top_of_prime_card).resolve_left hD0_ne_bot
  have hZ0X_le_comm : Z0X ≤ _root_.commutator X := by
    intro z hz
    let zZ : Z0X := ⟨z, hz⟩
    have hzTop : zZ ∈ (⊤ : Subgroup Z0X) := Subgroup.mem_top zZ
    rw [← hD0top] at hzTop
    exact hzTop
  have hcomm_eq_Z0X : _root_.commutator X = Z0X :=
    le_antisymm hcomm_le_Z0X hZ0X_le_comm
  calc
    ⁅X, X⁆ = (_root_.commutator X).map X.subtype := by
      rw [Subgroup.map_subtype_commutator]
    _ = Z0X.map X.subtype := by rw [hcomm_eq_Z0X]
    _ = Z0 := Subgroup.map_subgroupOf_eq_of_le hZ0_le_X

private lemma claim14_prime_card_subgroup_eq_closure_of_mem_ne_one
    {G : Type*} [Group G] [Finite G] (A : Subgroup G) {p : ℕ}
    (hp : Nat.Prime p) (hAcard : Nat.card A = p)
    {x : G} (hxA : x ∈ A) (hxne : x ≠ 1) :
    A = Subgroup.closure ({x} : Set G) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hAcard' : Nat.card A = p := by
    simpa [Nat.card, Nat.card_coe_set_eq] using hAcard
  apply le_antisymm
  · intro y hyA
    let xA : A := ⟨x, hxA⟩
    let yA : A := ⟨y, hyA⟩
    have hxA_ne : xA ≠ 1 := by
      intro h
      exact hxne (congrArg Subtype.val h)
    have hy_zpow : yA ∈ Subgroup.zpowers xA :=
      mem_zpowers_of_prime_card (G := A) hAcard' hxA_ne
    rcases Subgroup.mem_zpowers_iff.mp hy_zpow with ⟨n, hn⟩
    have hy_eq : x ^ n = y := by
      simpa [xA, yA] using congrArg Subtype.val hn
    have hx_closure : x ∈ Subgroup.closure ({x} : Set G) :=
      Subgroup.subset_closure (by simp)
    simpa [← hy_eq] using
      (Subgroup.closure ({x} : Set G)).zpow_mem hx_closure n
  · rw [← Subgroup.zpowers_eq_closure]
    exact Subgroup.zpowers_le.mpr hxA

private lemma claim14_prime_card_subgroups_eq_of_common_nontrivial
    {G : Type*} [Group G] [Finite G] (A B : Subgroup G) {p : ℕ}
    (hp : Nat.Prime p) (hAcard : Nat.card A = p)
    (hBcard : Nat.card B = p)
    {x : G} (hxA : x ∈ A) (hxB : x ∈ B) (hxne : x ≠ 1) :
    A = B := by
  calc
    A = Subgroup.closure ({x} : Set G) :=
      claim14_prime_card_subgroup_eq_closure_of_mem_ne_one
        A hp hAcard hxA hxne
    _ = B :=
      (claim14_prime_card_subgroup_eq_closure_of_mem_ne_one
        B hp hBcard hxB hxne).symm

private lemma claim14_punctured_type_card
    {G : Type*} [Group G] [Finite G] :
    Nat.card {x : G // x ≠ 1} = Nat.card G - 1 := by
  classical
  letI : Fintype G := Fintype.ofFinite G
  letI : Fintype {x : G // x ≠ 1} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  simp

private lemma claim14_order_three_subgroups_card
    {G : Type*} [Group G] [Finite G]
    (hGcard : Nat.card G = 9) (hcube : ∀ x : G, x ^ 3 = 1) :
    Nat.card {A : Subgroup G // Nat.card A = 3} = 4 := by
  classical
  let Lines := {A : Subgroup G // Nat.card A = 3}
  let Piece := Σ A : Lines, {x : A.1 // (x : G) ≠ 1}
  let Punctured := {x : G // x ≠ 1}
  let decode : Piece → Punctured := fun y => ⟨(y.2.1 : G), y.2.2⟩
  have hdecode : Function.Bijective decode := by
    constructor
    · intro a b hab
      rcases a with ⟨A, x⟩
      rcases b with ⟨B, y⟩
      have hxy : (x.1 : G) = (y.1 : G) := by
        simpa [decode] using congrArg Subtype.val hab
      have hAB : A.1 = B.1 :=
        claim14_prime_card_subgroups_eq_of_common_nontrivial
          A.1 B.1 Nat.prime_three A.2 B.2 x.1.2
            (by
              rw [hxy]
              exact y.1.2) x.2
      have hAeqB : A = B := Subtype.ext hAB
      subst B
      have hxeqy : x = y := by
        apply Subtype.ext
        apply Subtype.ext
        exact hxy
      subst y
      rfl
    · intro x
      have hxorder : orderOf x.1 = 3 := orderOf_eq_prime (hcube x.1) x.2
      let A : Subgroup G := Subgroup.zpowers x.1
      have hAcard : Nat.card A = 3 := by
        simpa [A, Nat.card_zpowers] using hxorder
      let ALines : Lines := ⟨A, hAcard⟩
      let xA : A := ⟨x.1, Subgroup.mem_zpowers x.1⟩
      refine ⟨⟨ALines, ⟨xA, x.2⟩⟩, ?_⟩
      rfl
  let e : Piece ≃ Punctured := Equiv.ofBijective decode hdecode
  have hPieceCard : Nat.card Piece = Nat.card Lines * 2 := by
    letI : Fintype Lines := Fintype.ofFinite Lines
    letI (A : Lines) : Fintype {x : A.1 // (x : G) ≠ 1} := Fintype.ofFinite _
    have hFiberCard (A : Lines) :
        Nat.card {x : A.1 // (x : G) ≠ 1} = 2 := by
      let eA : {x : A.1 // (x : G) ≠ 1} ≃ {x : A.1 // x ≠ 1} :=
        Equiv.subtypeEquivRight fun x => by
          constructor
          · intro hx h
            exact hx (congrArg Subtype.val h)
          · intro hx h
            apply hx
            apply Subtype.ext
            exact h
      calc
        Nat.card {x : A.1 // (x : G) ≠ 1} = Nat.card {x : A.1 // x ≠ 1} :=
          Nat.card_congr eA
        _ = Nat.card A.1 - 1 := claim14_punctured_type_card
        _ = 2 := by rw [A.2]
    change Nat.card (Σ A : Lines, {x : A.1 // (x : G) ≠ 1}) = _
    rw [Nat.card_sigma]
    simp_rw [hFiberCard]
    simp
  have hPuncturedCard : Nat.card Punctured = 8 := by
    calc
      Nat.card Punctured = Nat.card G - 1 := claim14_punctured_type_card
      _ = 8 := by rw [hGcard]
  have hcardEq : Nat.card Lines * 2 = 8 := by
    calc
      Nat.card Lines * 2 = Nat.card Piece := hPieceCard.symm
      _ = Nat.card Punctured := Nat.card_congr e
      _ = 8 := hPuncturedCard
  change Nat.card Lines = 4
  omega

private lemma claim14_A2_card
    {G : Type*} [Group G] [Finite G]
    (Z : Subgroup G) (hZcard : Nat.card Z = 3)
    (hGcard : Nat.card G = 9) (hcube : ∀ x : G, x ^ 3 = 1) :
    Nat.card {A : {A : Subgroup G // Nat.card A = 3} // A.1 ≠ Z} = 3 := by
  classical
  let Lines := {A : Subgroup G // Nat.card A = 3}
  let zLine : Lines := ⟨Z, hZcard⟩
  letI : Fintype Lines := Fintype.ofFinite Lines
  letI : Fintype {A : Lines // A ≠ zLine} := Fintype.ofFinite _
  have hLines : Nat.card Lines = 4 :=
    claim14_order_three_subgroups_card hGcard hcube
  have hneCard : Nat.card {A : Lines // A ≠ zLine} = Nat.card Lines - 1 := by
    rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
    simp
  calc
    Nat.card {A : {A : Subgroup G // Nat.card A = 3} // A.1 ≠ Z} =
        Nat.card {A : Lines // A ≠ zLine} := by
      exact Nat.card_congr (Equiv.subtypeEquivRight fun A => by
        constructor
        · intro hA hEq
          exact hA (congrArg Subtype.val hEq)
        · intro hA hEq
          apply hA
          apply Subtype.ext
          exact hEq)
    _ = Nat.card Lines - 1 := hneCard
    _ = 3 := by rw [hLines]

private lemma claim14_inf_centralizer_eq_of_local_sylow
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact (Nat.Prime p)]
    (P X Y : Subgroup G)
    (hX_le_CP : X ≤ Subgroup.centralizer (P : Set G))
    (hXsylow :
      ∃ XC : Sylow p (Subgroup.centralizer (P : Set G)),
        (XC : Subgroup (Subgroup.centralizer (P : Set G))) =
          X.subgroupOf (Subgroup.centralizer (P : Set G)))
    (hX_le_Y : X ≤ Y) (hYp : IsPGroup p Y) :
    Y ⊓ Subgroup.centralizer (P : Set G) = X := by
  let CP : Subgroup G := Subgroup.centralizer (P : Set G)
  obtain ⟨XC, hXC⟩ := hXsylow
  let YC : Subgroup CP := (Y ⊓ CP).subgroupOf CP
  have hYCp : IsPGroup p YC := by
    have hInfp : IsPGroup p (Y ⊓ CP : Subgroup G) :=
      IsPGroup.to_inf_left (K := CP) hYp
    exact hInfp.of_equiv
      (Subgroup.subgroupOfEquivOfLe (show Y ⊓ CP ≤ CP from inf_le_right)).symm
  have hXC_le_YC : (XC : Subgroup CP) ≤ YC := by
    rw [hXC]
    intro x hx
    exact ⟨hX_le_Y hx, x.property⟩
  have hYC_eq_XC : YC = (XC : Subgroup CP) :=
    XC.is_maximal' hYCp hXC_le_YC
  have hYC_eq_Xsub : YC = X.subgroupOf CP := hYC_eq_XC.trans hXC
  have hmap := congrArg (fun A : Subgroup CP => A.map CP.subtype) hYC_eq_Xsub
  dsimp [YC] at hmap
  rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right,
    Subgroup.map_subgroupOf_eq_of_le (by simpa [CP] using hX_le_CP)] at hmap
  simpa [CP] using hmap

private lemma claim14_center_map_subtype
    {G : Type*} [Group G] (Y : Subgroup G) :
    (Subgroup.center Y).map Y.subtype =
      Y ⊓ Subgroup.centralizer (Y : Set G) := by
  ext g
  constructor
  · rintro ⟨gY, hgY, rfl⟩
    refine ⟨gY.property, ?_⟩
    change ∀ y : G, y ∈ Y → y * (gY : G) = (gY : G) * y
    intro y hyY
    exact congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hgY ⟨y, hyY⟩)
  · intro hg
    let gY : Y := ⟨g, hg.1⟩
    refine ⟨gY, ?_, rfl⟩
    apply Subgroup.mem_center_iff.mpr
    intro y
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp hg.2) y y.property

/- Source interface for Claim (14): construct the `S_3` quotient data and a
subgroup `R1` above `RΣ`, with `R2` fixed as `C_G(Z1)`, exposing only the
fields needed by the checked assembly below. -/
private theorem chapter2_claim14_center_action_sylow_source_interface
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R T : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hExceptionalCase : p = 3 ∧ Nat.card Sigma = 3 ∧
      Nat.card (nearFieldStar Q P) = 8 ∧ IsCyclic W ∧
        (Nat.card W = 3 ∨ Nat.card W = 9) ∧
          (∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
            Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u) ∧
            ∃ (F : Type*) (_ : PFAppendixII.RightNearField F) (_ : Finite F)
                (_ : Nontrivial F),
              PFAppendixII.IsDicksonIndexTwoModel F 3 1 ∧
                Nonempty (nearFieldStar Q P ≃* Fˣ))
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hCZ1 : ∃ n : ℕ, Nat.card (Subgroup.centralizer (Z1 : Set G)) = 3 ^ n)
    (hR : R = T ⊔ P ∧
      Disjoint T P ∧
        T ≤ Subgroup.centralizer (P : Set G) ∧
          (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
            W ⊓ Subgroup.centralizer (P : Set G)) ≤
              Subgroup.normalizer (T : Set G) ∧
            Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
              ∀ A B : Subgroup G,
                A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
                  ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
                    ∃! c : G,
                      c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                        B = rightConjugate A c)
    (hModel :
      ∃ (N : Subgroup G) (F : Type*) (_ : PFAppendixII.RightNearField F)
          (_ : Finite F) (_ : Nontrivial F)
          (addEquiv : Multiplicative F ≃* ↥T)
          (unitEquiv : Fˣ ≃* ↥(Q ⊓ Subgroup.centralizer (P : Set G))),
        N = D ⊓
            Subgroup.centralizer
              ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
            Subgroup.centralizer (P : Set G) ∧
          R ≤ Subgroup.centralizer (P : Set G) ∧
            (∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
              (g ∈ R ↔ ∃ x : F,
                g * (((addEquiv (Multiplicative.ofAdd x) : T) : G))⁻¹ ∈ N)) ∧
              (∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹) ∧
                s * t ∈ T ∧
                (∀ a : F, ∀ b : Fˣ,
                  rightConjugateElem
                      (((addEquiv (Multiplicative.ofAdd a) : T) : G))
                      (((unitEquiv b : ↥(Q ⊓
                        Subgroup.centralizer (P : Set G))) : G)) =
                    (((addEquiv (Multiplicative.ofAdd (a * (b : F))) : T) : G))) ∧
                  addOrderOf (1 : F) = orderOf (s * t) ∧
                    (p = 3 →
                      Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 3 →
                      Nat.card (nearFieldStar Q P) = 8 →
                      let Sigma0 : Subgroup G :=
                        W ⊓ Subgroup.centralizer (P : Set G)
                      Disjoint R Sigma0 ∧
                        Nat.card (R ⊔ Sigma0 : Subgroup G) = 3 ^ 4 ∧
                          ¬ IsMulCommutative (R ⊔ Sigma0 : Subgroup G) ∧
                            (∃ XC : Sylow 3 (Subgroup.centralizer (P : Set G)),
                              (XC : Subgroup (Subgroup.centralizer (P : Set G))) =
                                (R ⊔ Sigma0).subgroupOf
                                  (Subgroup.centralizer (P : Set G))) ∧
                              ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
                                ∃ r q w : G, r ∈ R ∧
                                  q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                                    w ∈ Sigma0 ∧ g = r * q * w) ∧
                    (∀ m' : ℕ,
                      Nat.card (nearFieldStar Q P) + 1 = p ^ m' →
                      ¬ p ∣ Nat.card
                        (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) →
                      Subgroup.centralizer (P : Set G) ≤
                          Subgroup.normalizer (R : Set G) ∧
                        Nat.card R = p ^ (m' + 1) ∧
                          Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
                            p ^ m' ∧
                            ∃ RC : Sylow p (Subgroup.centralizer (P : Set G)),
                              (RC : Subgroup (Subgroup.centralizer (P : Set G))) =
                                R.subgroupOf
                                  (Subgroup.centralizer (P : Set G)))) :
      (R ⊔ Sigma) ⊓
              Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
            Z1 ⊔ P ∧
              ⁅(R ⊔ Sigma : Subgroup G), (R ⊔ Sigma : Subgroup G)⁆ = Z1 ∧
              ∃ phi : (Subgroup.normalizer
                    ((R ⊔ Sigma : Subgroup G) : Set G)) →*
                  Equiv.Perm (Fin 3),
                Function.Surjective phi ∧
                  MonoidHom.ker phi =
                    (R ⊔ Sigma).subgroupOf
                      (Subgroup.normalizer
                        ((R ⊔ Sigma : Subgroup G) : Set G)) ∧
                    ∀ R1 : Subgroup G,
                      IsPGroup 3 R1 →
                        R ⊔ Sigma ≤ R1 →
                          R1 ≤ Subgroup.normalizer
                            ((R ⊔ Sigma : Subgroup G) : Set G) →
                            Subgroup.normalizer
                                ((R ⊔ Sigma : Subgroup G) : Set G) ≤
                              Subgroup.normalizer (R1 : Set G) →
                              ((R ⊔ Sigma).subgroupOf R1).index = 3 →
                                (R1.subgroupOf (Subgroup.normalizer
                                  ((R ⊔ Sigma : Subgroup G) : Set G))).index = 2 →
                                ∃ R2s : Sylow 3 G,
                                  R1 ≤ (R2s : Subgroup G) ∧
                                    ((R1.subgroupOf (R2s : Subgroup G)).index = 1 ∨
                                      (R1.subgroupOf (R2s : Subgroup G)).index = 3) ∧
                                      R1 ⊓ Subgroup.centralizer (R1 : Set G) = Z1 ∧
                                        (R2s : Subgroup G) ⊓
                                            Subgroup.centralizer
                                              ((R2s : Subgroup G) : Set G) = Z1 ∧
                                          (R2s : Subgroup G) ⊓
                                              Subgroup.centralizer (P : Set G) =
                                            R ⊔ Sigma := by
  rcases hModel with
    ⟨_N, F, hFnear, hFfinite, hFnontrivial, addEquiv, unitEquiv,
      _hN, _hRcentral, _hinverse, hT_inverted, hst_mem_T, _hconjugation,
      hchar_order, h11ExceptionalLocal, _h11CaseOneLocal⟩
  letI : PFAppendixII.RightNearField F := hFnear
  letI : Finite F := hFfinite
  letI : Nontrivial F := hFnontrivial
  have hunit_card : Nat.card Fˣ = 8 := by
    calc
      Nat.card Fˣ =
          Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :=
        Nat.card_congr unitEquiv.toEquiv
      _ = 8 := by
        simpa [nearFieldStar] using hExceptionalCase.2.2.1
  have hFcard : Nat.card F = 9 := by
    calc
      Nat.card F = Nat.card Fˣ + 1 := Nat.card_eq_card_units_add_one F
      _ = 9 := by rw [hunit_card]
  have hTcard : Nat.card T = 9 := by
    calc
      Nat.card T = Nat.card (Multiplicative F) :=
        (Nat.card_congr addEquiv.toEquiv).symm
      _ = Nat.card F := rfl
      _ = 9 := hFcard
  have hPcard : Nat.card P = 3 := by
    rw [hch.B1.P_card, hExceptionalCase.1]
  have hZ1_le_T : Z1 ≤ T := by
    rw [hZ1]
    exact Subgroup.zpowers_le.mpr hst_mem_T
  have hchar_three : addOrderOf (1 : F) = 3 := by
    have hprime := PFAppendixII.rightNearField_addOrderOf_one_prime (F := F)
    have hdiv : addOrderOf (1 : F) ∣ 3 ^ 2 := by
      have hchar_dvd_nine : addOrderOf (1 : F) ∣ 9 := by
        simpa [hFcard] using addOrderOf_dvd_natCard (1 : F)
      simpa using hchar_dvd_nine
    exact Nat.prime_eq_prime_of_dvd_pow hprime Nat.prime_three hdiv
  have hZ1card : Nat.card Z1 = 3 := by
    rw [hZ1, Nat.card_zpowers, ← hchar_order, hchar_three]
  have hSigmaCardRaw :
      Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 3 := by
    simpa [hSigma] using hExceptionalCase.2.1
  have h11LocalRaw :=
    h11ExceptionalLocal hExceptionalCase.1 hSigmaCardRaw
      hExceptionalCase.2.2.1
  rw [← hSigma] at h11LocalRaw
  have h11Local :
      Disjoint R Sigma ∧ Nat.card (R ⊔ Sigma : Subgroup G) = 3 ^ 4 ∧
        ¬ IsMulCommutative (R ⊔ Sigma : Subgroup G) :=
    ⟨h11LocalRaw.1, h11LocalRaw.2.1, h11LocalRaw.2.2.1⟩
  have hRSigmaSylowCP := h11LocalRaw.2.2.2.1
  have hCPdecomp := h11LocalRaw.2.2.2.2
  have hlocal_center_data :
      Z1 ⊔ P ≤
          (R ⊔ Sigma) ⊓
            Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
        (((Z1 ⊔ P).subgroupOf (R ⊔ Sigma : Subgroup G)).index = 9) ∧
          ¬ IsMulCommutative (R ⊔ Sigma : Subgroup G) := by
    have hV_eq_Cs : V = D ⊓ Subgroup.centralizer ({s} : Set G) := by
      calc
        V = peterfalviV D t := hch.section3.section2.V_eq
        _ = D ⊓ Subgroup.centralizer ({s} : Set G) :=
          (proposition_5 H D Q t s hch.section3.section2.hA.A1
            hch.section3.s_mem_H hch.section3.s_involution
            hch.section3.s_conjugate).1
    have hW_le_Cst : W ≤ Subgroup.centralizer ({s * t} : Set G) := by
      intro w hwW
      have hwV : w ∈ V := hch.section3.section2.W_le_V hwW
      have hwDt : w ∈ D ⊓ Subgroup.centralizer ({t} : Set G) := by
        simpa [peterfalviV, hch.section3.section2.V_eq] using hwV
      have hwDs : w ∈ D ⊓ Subgroup.centralizer ({s} : Set G) := by
        rw [← hV_eq_Cs]
        exact hwV
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hsw : Commute s w :=
        (Subgroup.mem_centralizer_singleton_iff.mp hwDs.2).symm
      have htw : Commute t w :=
        (Subgroup.mem_centralizer_singleton_iff.mp hwDt.2).symm
      exact (hsw.mul_left htw).eq.symm
    have hW_le_CZ1 : W ≤ Subgroup.centralizer (Z1 : Set G) := by
      rw [hZ1, Subgroup.zpowers_eq_closure,
        Subgroup.centralizer_closure]
      exact hW_le_Cst
    have hSigma_le_CZ1 : Sigma ≤ Subgroup.centralizer (Z1 : Set G) := by
      rw [hSigma]
      exact inf_le_left.trans hW_le_CZ1
    have hZ1_le_CSigma : Z1 ≤ Subgroup.centralizer (Sigma : Set G) :=
      Subgroup.le_centralizer_iff.mpr hSigma_le_CZ1
    have hSigma_le_CP : Sigma ≤ Subgroup.centralizer (P : Set G) := by
      rw [hSigma]
      exact inf_le_right
    have hP_le_CSigma : P ≤ Subgroup.centralizer (Sigma : Set G) :=
      Subgroup.le_centralizer_iff.mpr hSigma_le_CP
    have hC0_le_CSigma :
        Z1 ⊔ P ≤ Subgroup.centralizer (Sigma : Set G) :=
      sup_le hZ1_le_CSigma hP_le_CSigma
    have hC0_le_center_R :
        Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) :=
      claim14_center_R_contains_Z1_sup_P T P Z1 R addEquiv hPcard
        hR.2.2.1 hR.1 hZ1_le_T
    have hC0_le_X : Z1 ⊔ P ≤ R ⊔ Sigma :=
      hC0_le_center_R.trans inf_le_left |>.trans le_sup_left
    have hC0_le_CX :
        Z1 ⊔ P ≤ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) :=
      Subgroup.le_centralizer_sup_of_le_centralizers
        (hC0_le_center_R.trans inf_le_right) hC0_le_CSigma
    have hC0center :
        Z1 ⊔ P ≤
          (R ⊔ Sigma) ⊓
            Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) :=
      fun x hx => ⟨hC0_le_X hx, hC0_le_CX hx⟩
    have hZ1_disj_P : Disjoint Z1 P := hR.2.1.mono hZ1_le_T le_rfl
    have hZ1_le_CP : Z1 ≤ Subgroup.centralizer (P : Set G) :=
      hZ1_le_T.trans hR.2.2.1
    have hP_le_CZ1 : P ≤ Subgroup.centralizer (Z1 : Set G) :=
      Subgroup.le_centralizer_iff.mpr hZ1_le_CP
    have hP_norm_Z1 : P ≤ Subgroup.normalizer (Z1 : Set G) :=
      hP_le_CZ1.trans (claim14_centralizer_le_normalizer Z1)
    have hC0card : Nat.card (Z1 ⊔ P : Subgroup G) = 9 := by
      rw [claim14_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
        Z1 P hP_norm_Z1 hZ1_disj_P, hZ1card, hPcard]
    have hC0subcard :
        Nat.card ((Z1 ⊔ P).subgroupOf (R ⊔ Sigma : Subgroup G)) = 9 := by
      calc
        Nat.card ((Z1 ⊔ P).subgroupOf (R ⊔ Sigma : Subgroup G)) =
            Nat.card (Z1 ⊔ P : Subgroup G) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC0_le_X).toEquiv
        _ = 9 := hC0card
    have hC0index :
        ((Z1 ⊔ P).subgroupOf (R ⊔ Sigma : Subgroup G)).index = 9 := by
      have hmul :=
        ((Z1 ⊔ P).subgroupOf (R ⊔ Sigma : Subgroup G)).index_mul_card
      rw [hC0subcard, h11Local.2.1] at hmul
      norm_num at hmul ⊢
      omega
    have hnoncomm : ¬ IsMulCommutative (R ⊔ Sigma : Subgroup G) :=
      h11Local.2.2
    exact ⟨hC0center, hC0index, hnoncomm⟩
  have hcenter :
      (R ⊔ Sigma) ⊓
          Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
        Z1 ⊔ P :=
    claim14_center_eq_of_index_nine_of_noncomm
      (R ⊔ Sigma) (Z1 ⊔ P) hlocal_center_data.1
        hlocal_center_data.2.1 hlocal_center_data.2.2
  have hderived :
      ⁅(R ⊔ Sigma : Subgroup G), (R ⊔ Sigma : Subgroup G)⁆ = Z1 := by
    have hlocal_derived_data :
        T ≤ R ⊔ Sigma ∧
          R ⊔ Sigma ≤ Subgroup.normalizer (T : Set G) ∧
            ((T.subgroupOf (R ⊔ Sigma : Subgroup G)).index = 9) ∧
              T ⊓ (Z1 ⊔ P) = Z1 ∧
                Z1 ≤ R ⊔ Sigma ∧ Nat.card Z1 = 3 := by
      have hT_le_R : T ≤ R := by
        rw [hR.1]
        exact le_sup_left
      have hT_le_X : T ≤ R ⊔ Sigma := hT_le_R.trans le_sup_left
      have hP_le_CT : P ≤ Subgroup.centralizer (T : Set G) :=
        Subgroup.le_centralizer_iff.mpr hR.2.2.1
      have hP_norm_T : P ≤ Subgroup.normalizer (T : Set G) :=
        hP_le_CT.trans (claim14_centralizer_le_normalizer T)
      have hR_norm_T : R ≤ Subgroup.normalizer (T : Set G) := by
        rw [hR.1]
        exact sup_le Subgroup.le_normalizer hP_norm_T
      have hSigma_norm_T : Sigma ≤ Subgroup.normalizer (T : Set G) := by
        rw [hSigma]
        exact le_sup_right.trans hR.2.2.2.1
      have hX_norm_T :
          R ⊔ Sigma ≤ Subgroup.normalizer (T : Set G) :=
        sup_le hR_norm_T hSigma_norm_T
      have hTsubcard :
          Nat.card (T.subgroupOf (R ⊔ Sigma : Subgroup G)) = 9 := by
        calc
          Nat.card (T.subgroupOf (R ⊔ Sigma : Subgroup G)) = Nat.card T :=
            Nat.card_congr (Subgroup.subgroupOfEquivOfLe hT_le_X).toEquiv
          _ = 9 := hTcard
      have hTindex :
          (T.subgroupOf (R ⊔ Sigma : Subgroup G)).index = 9 := by
        have hmul :=
          (T.subgroupOf (R ⊔ Sigma : Subgroup G)).index_mul_card
        rw [hTsubcard, h11Local.2.1] at hmul
        norm_num at hmul ⊢
        omega
      have hZ1_disj_P : Disjoint Z1 P := hR.2.1.mono hZ1_le_T le_rfl
      have hZ1_le_CP : Z1 ≤ Subgroup.centralizer (P : Set G) :=
        hZ1_le_T.trans hR.2.2.1
      have hP_le_CZ1 : P ≤ Subgroup.centralizer (Z1 : Set G) :=
        Subgroup.le_centralizer_iff.mpr hZ1_le_CP
      have hP_norm_Z1 : P ≤ Subgroup.normalizer (Z1 : Set G) :=
        hP_le_CZ1.trans (claim14_centralizer_le_normalizer Z1)
      have hinter : T ⊓ (Z1 ⊔ P) = Z1 := by
        apply le_antisymm
        · intro x hx
          have hxProd : x ∈ (Z1 : Set G) * (P : Set G) := by
            rw [← Subgroup.coe_mul_of_right_le_normalizer_left
              Z1 P hP_norm_Z1]
            exact hx.2
          rcases hxProd with ⟨z, hzZ1, q, hqP, hzq⟩
          have hqT : q ∈ T := by
            have hzT : z ∈ T := hZ1_le_T hzZ1
            have hcalc : z⁻¹ * x = q := by
              calc
                z⁻¹ * x = z⁻¹ * (z * q) := by rw [hzq.symm]
                _ = q := by simp
            rw [← hcalc]
            exact T.mul_mem (T.inv_mem hzT) hx.1
          have hqOne : q = 1 := Subgroup.mem_bot.mp
            ((Subgroup.disjoint_def.mp hR.2.1) hqT hqP)
          rw [← hzq, hqOne]
          change z * 1 ∈ Z1
          simpa using hzZ1
        · intro z hzZ1
          exact ⟨hZ1_le_T hzZ1, Subgroup.mem_sup_left hzZ1⟩
      have hZ1_le_X : Z1 ≤ R ⊔ Sigma := hZ1_le_T.trans hT_le_X
      exact ⟨hT_le_X, hX_norm_T, hTindex, hinter, hZ1_le_X, hZ1card⟩
    exact claim14_commutator_eq_of_two_index_nine
      (R ⊔ Sigma) (Z1 ⊔ P) T Z1 hlocal_center_data.1
        hlocal_center_data.2.1 hlocal_derived_data.1
        hlocal_derived_data.2.1 hlocal_derived_data.2.2.1
        hlocal_derived_data.2.2.2.1 hlocal_derived_data.2.2.2.2.1
        hlocal_derived_data.2.2.2.2.2 hlocal_center_data.2.2
  refine ⟨hcenter, hderived, ?_⟩
  have haction :
      ∃ phi : (Subgroup.normalizer
            ((R ⊔ Sigma : Subgroup G) : Set G)) →*
          Equiv.Perm (Fin 3),
        Function.Surjective phi ∧
          MonoidHom.ker phi =
            (R ⊔ Sigma).subgroupOf
              (Subgroup.normalizer
                ((R ⊔ Sigma : Subgroup G) : Set G)) := by
    classical
    let X : Subgroup G := R ⊔ Sigma
    let C0 : Subgroup G := Z1 ⊔ P
    let N : Subgroup G := Subgroup.normalizer (X : Set G)
    let Z0 : Subgroup C0 := Z1.subgroupOf C0
    have hC0_le_X : C0 ≤ X := by
      simpa [C0, X] using hlocal_center_data.1.trans inf_le_left
    have hcenterMap : (Subgroup.center X).map X.subtype = C0 := by
      change (Subgroup.center (R ⊔ Sigma : Subgroup G)).map
          (R ⊔ Sigma : Subgroup G).subtype = Z1 ⊔ P
      rw [← hcenter]
      ext g
      constructor
      · rintro ⟨gX, hgX, rfl⟩
        refine ⟨gX.property, ?_⟩
        change ∀ y : G, y ∈ R ⊔ Sigma → y * (gX : G) = (gX : G) * y
        intro y hyX
        exact congrArg Subtype.val
          (Subgroup.mem_center_iff.mp hgX ⟨y, hyX⟩)
      · intro hg
        let gX : X := ⟨g, hg.1⟩
        refine ⟨gX, ?_, rfl⟩
        apply Subgroup.mem_center_iff.mpr
        intro y
        apply Subtype.ext
        exact (Subgroup.mem_centralizer_iff.mp hg.2) y y.property
    have hN_norm_C0 : N ≤ Subgroup.normalizer (C0 : Set G) := by
      haveI : (Subgroup.center X).Characteristic := by infer_instance
      have hnorm :=
        claim14_normalizer_le_normalizer_map_subtype_of_characteristic
          X (Subgroup.center X)
      simpa [N, hcenterMap] using hnorm
    have hN_norm_Z1 : N ≤ Subgroup.normalizer (Z1 : Set G) := by
      haveI : (_root_.commutator X).Characteristic := by infer_instance
      have hnorm :=
        claim14_normalizer_le_normalizer_map_subtype_of_characteristic
          X (_root_.commutator X)
      rw [Subgroup.map_subtype_commutator] at hnorm
      simpa [N, X, hderived] using hnorm
    have hC0card : Nat.card C0 = 9 := by
      have hP_norm_Z1 : P ≤ Subgroup.normalizer (Z1 : Set G) := by
        have hZ1_le_CP : Z1 ≤ Subgroup.centralizer (P : Set G) :=
          hZ1_le_T.trans hR.2.2.1
        exact (Subgroup.le_centralizer_iff.mpr hZ1_le_CP).trans
          (claim14_centralizer_le_normalizer Z1)
      calc
        Nat.card C0 = Nat.card Z1 * Nat.card P := by
          simpa [C0] using
            claim14_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
              Z1 P hP_norm_Z1 (hR.2.1.mono hZ1_le_T le_rfl)
        _ = 9 := by rw [hZ1card, hPcard]
    have hC0cube : ∀ x : C0, x ^ 3 = 1 := by
      intro x
      have hZ1_le_CP : Z1 ≤ Subgroup.centralizer (P : Set G) :=
        hZ1_le_T.trans hR.2.2.1
      have hP_norm_Z1 : P ≤ Subgroup.normalizer (Z1 : Set G) :=
        (Subgroup.le_centralizer_iff.mpr hZ1_le_CP).trans
          (claim14_centralizer_le_normalizer Z1)
      have hxProd : (x : G) ∈ (Z1 : Set G) * (P : Set G) := by
        rw [← Subgroup.coe_mul_of_right_le_normalizer_left Z1 P hP_norm_Z1]
        exact x.property
      rcases hxProd with ⟨z, hzZ1, q, hqP, hzq⟩
      have hzCube : z ^ 3 = 1 := by
        have hzPow := pow_card_eq_one' (x := (⟨z, hzZ1⟩ : Z1))
        rw [hZ1card] at hzPow
        exact congrArg Subtype.val hzPow
      have hqCube : q ^ 3 = 1 := by
        have hqPow := pow_card_eq_one' (x := (⟨q, hqP⟩ : P))
        rw [hPcard] at hqPow
        exact congrArg Subtype.val hqPow
      have hzqComm : Commute z q := by
        exact ((Subgroup.mem_centralizer_iff.mp (hZ1_le_CP hzZ1)) q hqP).symm
      apply Subtype.ext
      change (x : G) ^ 3 = 1
      rw [← hzq, hzqComm.mul_pow, hzCube, hqCube, one_mul]
    have hZ0card : Nat.card Z0 = 3 := by
      calc
        Nat.card Z0 = Nat.card Z1 :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
            dsimp [C0]
            exact le_sup_left)).toEquiv
        _ = 3 := hZ1card
    have hA2cardFlat :
        Nat.card {A : Subgroup C0 // Nat.card A = 3 ∧ A ≠ Z0} = 3 := by
      let eFlat :
          {A : {A : Subgroup C0 // Nat.card A = 3} // A.1 ≠ Z0} ≃
            {A : Subgroup C0 // Nat.card A = 3 ∧ A ≠ Z0} :=
        Equiv.subtypeSubtypeEquivSubtypeInter
          (fun A : Subgroup C0 => Nat.card A = 3) (fun A => A ≠ Z0)
      calc
        Nat.card {A : Subgroup C0 // Nat.card A = 3 ∧ A ≠ Z0} =
            Nat.card {A : {A : Subgroup C0 // Nat.card A = 3} // A.1 ≠ Z0} :=
          Nat.card_congr eFlat.symm
        _ = 3 := claim14_A2_card Z0 hZ0card hC0card hC0cube
    let incl : N →* Subgroup.normalizer (C0 : Set G) :=
      Subgroup.inclusion hN_norm_C0
    let autHom : N →* MulAut C0 := C0.normalizerMonoidHom.comp incl
    letI : MulAction N (Subgroup C0) := MulAction.compHom _ autHom
    have hZ0fixed (n : N) : n • Z0 = Z0 := by
      apply Subgroup.eq_of_le_of_card_ge
      · intro z hz
        change z ∈ Z0.map (autHom n).toMonoidHom at hz
        rcases hz with ⟨y, hyZ0, rfl⟩
        change ((autHom n y : C0) : G) ∈ Z1
        have hconj :=
          (Subgroup.mem_normalizer_iff.mp (hN_norm_Z1 n.property) (y : G)).1 hyZ0
        simpa [autHom, incl, Subgroup.normalizerMonoidHom_apply_apply_coe,
          mul_assoc] using hconj
      · have hmapCard : Nat.card (n • Z0 : Subgroup C0) = Nat.card Z0 := by
          change Nat.card ((autHom n) • Z0 : Subgroup C0) = Nat.card Z0
          exact Nat.card_congr ((autHom n).subgroupMap Z0).toEquiv.symm
        exact hmapCard.symm.le
    let A2Sub : SubMulAction N (Subgroup C0) :=
      { carrier := {A | Nat.card A = 3 ∧ A ≠ Z0}
        smul_mem' := by
          intro n A hA
          constructor
          · calc
              Nat.card (n • A : Subgroup C0) = Nat.card A := by
                change Nat.card ((autHom n) • A : Subgroup C0) = Nat.card A
                exact Nat.card_congr ((autHom n).subgroupMap A).toEquiv.symm
              _ = 3 := hA.1
          · intro hEq
            apply hA.2
            have hback := congrArg (fun B : Subgroup C0 => n⁻¹ • B) hEq
            simpa [hZ0fixed] using hback }
    have hNormalizer_of_fixed (g : N) (A : Subgroup C0)
        (hfix : g • A = A) :
        (g : G) ∈ Subgroup.normalizer (A.map C0.subtype : Set G) := by
      have hforward (a : N) (ha : a • A = A) :
          ∀ y : G, y ∈ A.map C0.subtype →
            (a : G) * y * (a : G)⁻¹ ∈ A.map C0.subtype := by
        intro y hy
        rcases hy with ⟨y0, hyA, rfl⟩
        have hyMap : autHom a y0 ∈ A.map (autHom a).toMonoidHom :=
          Subgroup.mem_map_of_mem (autHom a).toMonoidHom hyA
        change A.map (autHom a).toMonoidHom = A at ha
        rw [ha] at hyMap
        refine ⟨autHom a y0, hyMap, ?_⟩
        simp [autHom, incl, Subgroup.normalizerMonoidHom_apply_apply_coe,
          mul_assoc]
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · exact hforward g hfix y
      · intro hy
        have hfixInv : g⁻¹ • A = A := by
          calc
            g⁻¹ • A = g⁻¹ • (g • A) := by rw [hfix]
            _ = A := inv_smul_smul g A
        have hback := hforward g⁻¹ hfixInv (g * y * g⁻¹) hy
        simpa [mul_assoc] using hback
    let A2 := A2Sub
    have hA2card : Nat.card A2 = 3 := by
      change Nat.card {A : Subgroup C0 // Nat.card A = 3 ∧ A ≠ Z0} = 3
      exact hA2cardFlat
    let rho : N →* Equiv.Perm A2 := MulAction.toPermHom N A2
    let eA2 : A2 ≃ Fin 3 := Finite.equivFinOfCardEq hA2card
    let phi : N →* Equiv.Perm (Fin 3) :=
      (Equiv.permCongrHom eA2).toMonoidHom.comp rho
    have hAut_of_mem_X (x : N) (hxX : (x : G) ∈ X) : autHom x = 1 := by
      ext c
      have hcCentral : (c : G) ∈ Subgroup.centralizer (X : Set G) :=
        (hlocal_center_data.1 c.property).2
      have hcomm : (x : G) * (c : G) = (c : G) * (x : G) :=
        Subgroup.mem_centralizer_iff.mp hcCentral (x : G) hxX
      change (x : G) * (c : G) * (x : G)⁻¹ = (c : G)
      calc
        (x : G) * (c : G) * (x : G)⁻¹ =
            (c : G) * (x : G) * (x : G)⁻¹ := by rw [hcomm]
        _ = (c : G) := by simp [mul_assoc]
    let P0 : Subgroup C0 := P.subgroupOf C0
    have hP0card : Nat.card P0 = 3 := by
      calc
        Nat.card P0 = Nat.card P :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by
            dsimp [C0]
            exact le_sup_right)).toEquiv
        _ = 3 := hPcard
    have hP0neZ0 : P0 ≠ Z0 := by
      intro hEq
      have hmap := congrArg (fun A : Subgroup C0 => A.map C0.subtype) hEq
      have hPZ : P = Z1 := by
        simpa [P0, Z0, C0, Subgroup.map_subgroupOf_eq_of_le] using hmap
      have hdisj : Disjoint Z1 P := hR.2.1.mono hZ1_le_T le_rfl
      have hPbot : P = ⊥ := by
        apply le_antisymm
        · intro x hxP
          have hxZ : x ∈ Z1 := by rw [← hPZ]; exact hxP
          exact hdisj.le_bot ⟨hxZ, hxP⟩
        · exact bot_le
      have hPone : Nat.card P = 1 := by simp [hPbot]
      omega
    let Pline : A2 := ⟨P0, hP0card, hP0neZ0⟩
    have hkerRho : MonoidHom.ker rho = X.subgroupOf N := by
      apply le_antisymm
      · intro n hn
        rw [MonoidHom.mem_ker] at hn
        have hnAct (A : A2) : n • A = A := by
          have hpoint := congrArg (fun e : Equiv.Perm A2 => e A) hn
          simpa [rho] using hpoint
        have hnP : n • (P0 : Subgroup C0) = P0 := by
          exact congrArg Subtype.val (hnAct Pline)
        have hnNormP : (n : G) ∈ Subgroup.normalizer (P : Set G) := by
          have hnNormPmap := hNormalizer_of_fixed n P0 hnP
          simpa [P0, C0, Subgroup.map_subgroupOf_eq_of_le] using hnNormPmap
        have hnCP : (n : G) ∈ Subgroup.centralizer (P : Set G) := by
          rw [← (claim_1 H D Q K V W Q0 S Q1 P t s p hch).2.2.1]
          exact hnNormP
        rcases hCPdecomp (n : G) hnCP with
          ⟨r, q, w, hrR, hqCQ, hwSigma, hnDecompG⟩
        have hrX : r ∈ X := by
          dsimp [X]
          exact Subgroup.mem_sup_left hrR
        have hwX : w ∈ X := by
          dsimp [X]
          exact Subgroup.mem_sup_right hwSigma
        have hrNmem : r ∈ N := by
          simpa [N] using Subgroup.le_normalizer hrX
        have hwNmem : w ∈ N := by
          simpa [N] using Subgroup.le_normalizer hwX
        have hqNmem : q ∈ N := by
          have hqEq : q = r⁻¹ * (n : G) * w⁻¹ := by
            rw [hnDecompG]
            group
          rw [hqEq]
          exact N.mul_mem (N.mul_mem (N.inv_mem hrNmem) n.property)
            (N.inv_mem hwNmem)
        let rN : N := ⟨r, hrNmem⟩
        let qN : N := ⟨q, hqNmem⟩
        let wN : N := ⟨w, hwNmem⟩
        have hnDecomp : n = rN * qN * wN := Subtype.ext hnDecompG
        have hAutEq : autHom n = autHom qN := by
          calc
            autHom n = autHom (rN * qN * wN) := congrArg autHom hnDecomp
            _ = autHom rN * autHom qN * autHom wN := by rw [map_mul, map_mul]
            _ = autHom qN := by
              rw [hAut_of_mem_X rN hrX, hAut_of_mem_X wN hwX]
              simp
        haveI : Nontrivial A2 :=
          Finite.one_lt_card_iff_nontrivial.mp (by rw [hA2card]; norm_num)
        obtain ⟨Aline, hAline_ne⟩ := exists_ne Pline
        let A : Subgroup G := Aline.1.map C0.subtype
        have hAcard : Nat.card A = 3 := by
          calc
            Nat.card A = Nat.card Aline.1 := by
              exact Nat.card_congr
                (Subgroup.equivMapOfInjective Aline.1 C0.subtype C0.subtype_injective).symm
            _ = 3 := Aline.property.1
        have hA_le_C0 : A ≤ C0 := by
          dsimp [A]
          exact Subgroup.map_subtype_le Aline.1
        have hA_ne_Z1 : A ≠ Z1 := by
          intro hAZ
          apply Aline.property.2
          apply Subgroup.map_subtype_inj.mp
          change A = Z0.map C0.subtype
          rw [Subgroup.map_subgroupOf_eq_of_le (by
            dsimp [C0]
            exact le_sup_left)]
          exact hAZ
        have hA_ne_P : A ≠ P := by
          intro hAP
          apply hAline_ne
          apply Subtype.ext
          apply Subgroup.map_subtype_inj.mp
          change A = P0.map C0.subtype
          rw [Subgroup.map_subgroupOf_eq_of_le (by
            dsimp [C0]
            exact le_sup_right)]
          exact hAP
        have hA_le_R : A ≤ R := by
          refine hA_le_C0.trans ?_
          dsimp [C0]
          apply sup_le
          · exact hZ1_le_T.trans (by rw [hR.1]; exact le_sup_left)
          · rw [hR.1]
            exact le_sup_right
        have hTinfC0 : T ⊓ C0 = Z1 := by
          apply le_antisymm
          · intro x hx
            have hZ1_le_CP : Z1 ≤ Subgroup.centralizer (P : Set G) :=
              hZ1_le_T.trans hR.2.2.1
            have hP_norm_Z1 : P ≤ Subgroup.normalizer (Z1 : Set G) :=
              (Subgroup.le_centralizer_iff.mpr hZ1_le_CP).trans
                (claim14_centralizer_le_normalizer Z1)
            have hxProd : x ∈ (Z1 : Set G) * (P : Set G) := by
              rw [← Subgroup.coe_mul_of_right_le_normalizer_left Z1 P hP_norm_Z1]
              exact hx.2
            rcases hxProd with ⟨z, hzZ1, u, huP, hzu⟩
            have huT : u ∈ T := by
              have hzT : z ∈ T := hZ1_le_T hzZ1
              have hcalc : z⁻¹ * x = u := by
                calc
                  z⁻¹ * x = z⁻¹ * (z * u) := by rw [hzu.symm]
                  _ = u := by simp
              rw [← hcalc]
              exact T.mul_mem (T.inv_mem hzT) hx.1
            have huOne : u = 1 := Subgroup.mem_bot.mp
              ((Subgroup.disjoint_def.mp hR.2.1) huT huP)
            rw [← hzu, huOne]
            simpa using hzZ1
          · intro z hzZ1
            exact ⟨hZ1_le_T hzZ1, by
              dsimp [C0]
              exact Subgroup.mem_sup_left hzZ1⟩
        have hA_not_le_T : ¬ A ≤ T := by
          intro hAT
          have hA_le_Z1 : A ≤ Z1 := by
            rw [← hTinfC0]
            exact le_inf hAT hA_le_C0
          have hAZ : A = Z1 :=
            Subgroup.eq_of_le_of_card_ge hA_le_Z1 (by rw [hAcard, hZ1card])
          exact hA_ne_Z1 hAZ
        have hnA : n • (Aline.1 : Subgroup C0) = Aline.1 := by
          exact congrArg Subtype.val (hnAct Aline)
        have hqA : qN • (Aline.1 : Subgroup C0) = Aline.1 := by
          change (autHom qN) • (Aline.1 : Subgroup C0) = Aline.1
          rw [← hAutEq]
          exact hnA
        have hqNormA : q ∈ Subgroup.normalizer (A : Set G) := by
          simpa [A] using hNormalizer_of_fixed qN Aline.1 hqA
        have hAcardp : Nat.card A = p := by
          rw [hExceptionalCase.1]
          exact hAcard
        rcases hR.2.2.2.2.2 A A hA_le_R hA_le_R hAcardp hAcardp
            hA_not_le_T hA_not_le_T hA_ne_P hA_ne_P with
          ⟨c, hc, hcUnique⟩
        have hqWitness :
            q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
              A = rightConjugate A q :=
          ⟨hqCQ, (claim14_rightConjugate_eq_self_of_mem_normalizer hqNormA).symm⟩
        have honeWitness :
            (1 : G) ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
              A = rightConjugate A 1 := by
          exact ⟨by simp,
            (claim14_rightConjugate_eq_self_of_mem_normalizer
              (show (1 : G) ∈ Subgroup.normalizer (A : Set G) by simp)).symm⟩
        have hqEqC : q = c := hcUnique q hqWitness
        have hOneEqC : (1 : G) = c := hcUnique 1 honeWitness
        have hqOne : q = 1 := hqEqC.trans hOneEqC.symm
        change (n : G) ∈ X
        have hrwX : r * w ∈ X := X.mul_mem hrX hwX
        simpa [hnDecompG, hqOne] using hrwX
      · intro n hnX
        rw [MonoidHom.mem_ker]
        apply Equiv.ext
        intro A
        apply Subtype.ext
        change (autHom n) • (A.1 : Subgroup C0) = A.1
        rw [hAut_of_mem_X n hnX]
        simp
    have hkerPhi : MonoidHom.ker phi = X.subgroupOf N := by
      rw [← hkerRho]
      ext n
      simp only [MonoidHom.mem_ker]
      constructor
      · intro hn
        exact (Equiv.permCongrHom eA2).map_eq_one_iff.mp
          (by simpa [phi] using hn)
      · intro hn
        have h := (Equiv.permCongrHom eA2).map_eq_one_iff.mpr hn
        simpa [phi] using h
    have hphi : Function.Surjective phi := by
      letI : Fact (Nat.Prime 3) := ⟨by decide⟩
      have hXcard : Nat.card X = 3 ^ 4 := by
        simpa [X] using h11Local.2.1
      have hthree_pow_five_dvd_G : 3 ^ (4 + 1) ∣ Nat.card G := by
        obtain ⟨_k, u, _hglobalPow, hGcard, _hu⟩ :=
          hExceptionalCase.2.2.2.2.2.1
        rcases hExceptionalCase.2.2.2.2.1 with hWcard | hWcard
        · refine ⟨u, ?_⟩
          simp [hGcard, hWcard]
        · refine ⟨3 * u, ?_⟩
          simp [hGcard, hWcard]
          ring
      have hthree_dvd_range : 3 ∣ Nat.card phi.range := by
        have hindex_eq_range :
            (X.subgroupOf N).index = Nat.card phi.range := by
          rw [← hkerPhi, Subgroup.index_ker]
        have hthree_dvd_index : 3 ∣ (X.subgroupOf N).index := by
          rw [Subgroup.index_eq_card]
          change 3 ∣ Nat.card
            (Subgroup.normalizer (X : Set G) ⧸
              X.comap (Subgroup.normalizer (X : Set G)).subtype)
          exact Sylow.prime_dvd_card_quotient_normalizer
            hthree_pow_five_dvd_G hXcard
        rwa [hindex_eq_range] at hthree_dvd_index
      have hsC : s ∈ Subgroup.centralizer (P : Set G) :=
        claim14_s_mem_centralizer_P H D Q K V W Q0 S Q1 P t s p hch
      have hs_norm_R : s ∈ Subgroup.normalizer (R : Set G) :=
        claim14_s_mem_normalizer_R T P R s hch.section3.2.2.1 hsC
          hT_inverted hR.1
      have hs_norm_X : s ∈ Subgroup.normalizer (X : Set G) := by
        simpa [X] using
          claim14_s_mem_normalizer_R_sup_Sigma H D Q V W P Sigma R t s
            hch.section3.section2.hA.A1 hch.section3.2.1
            hch.section3.2.2.1 hch.section3.2.2.2
            hch.section3.section2.V_eq hch.section3.section2.W_le_V
            hSigma hsC hs_norm_R
      let sN : N := ⟨s, by simpa [N] using hs_norm_X⟩
      have hs_not_X : s ∉ X := by
        intro hsX
        have hXp : IsPGroup 3 X := IsPGroup.of_card hXcard
        let sX : X := ⟨s, hsX⟩
        obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hXp) sX
        have hs_order : orderOf s = 2 :=
          orderOf_eq_prime hch.section3.2.2.1.sq_eq_one
            hch.section3.2.2.1.ne_one
        have hpow : 2 = 3 ^ k := by
          calc
            2 = orderOf s := hs_order.symm
            _ = orderOf sX := by
              simp [sX]
            _ = 3 ^ k := hk
        cases k with
        | zero => norm_num at hpow
        | succ k =>
            rw [pow_succ] at hpow
            have hpos : 0 < 3 ^ k := pow_pos (by decide) k
            omega
      have hphi_s_ne : phi sN ≠ 1 := by
        intro hphi_s
        have hsKer : sN ∈ MonoidHom.ker phi := by
          rw [MonoidHom.mem_ker]
          exact hphi_s
        rw [hkerPhi] at hsKer
        exact hs_not_X hsKer
      let y : phi.range := ⟨phi sN, ⟨sN, rfl⟩⟩
      have hy_ne : y ≠ 1 := by
        intro hy
        apply hphi_s_ne
        exact congrArg Subtype.val hy
      have hsN_sq : sN ^ 2 = 1 := by
        apply Subtype.ext
        exact hch.section3.2.2.1.sq_eq_one
      have hy_sq : y ^ 2 = 1 := by
        apply Subtype.ext
        change (phi sN) ^ 2 = 1
        rw [← map_pow, hsN_sq, map_one]
      have hy_order : orderOf y = 2 := orderOf_eq_prime hy_sq hy_ne
      have htwo_dvd_range : 2 ∣ Nat.card phi.range := by
        have hy_dvd := orderOf_dvd_natCard y
        rwa [hy_order] at hy_dvd
      have hrange_dvd_six : Nat.card phi.range ∣ 6 := by
        have hperm_card : Nat.card (Equiv.Perm (Fin 3)) = 6 := by
          rw [Nat.card_perm, Nat.card_fin]
          norm_num [Nat.factorial]
        rw [← hperm_card]
        exact phi.range.card_subgroup_dvd_card
      have hrange_card : Nat.card phi.range = 6 := by
        have hsix_dvd_range : 6 ∣ Nat.card phi.range := by
          simpa using
            (show Nat.Coprime 2 3 by norm_num).mul_dvd_of_dvd_of_dvd
              htwo_dvd_range hthree_dvd_range
        exact Nat.dvd_antisymm hrange_dvd_six hsix_dvd_range
      have hrange_top : phi.range = ⊤ := by
        apply Subgroup.eq_top_of_card_eq
        rw [hrange_card, Nat.card_perm, Nat.card_fin]
        norm_num [Nat.factorial]
      exact MonoidHom.range_eq_top.mp hrange_top
    exact ⟨phi, hphi, by simpa [N, X] using hkerPhi⟩
  obtain ⟨phi, hphi_surjective, hphi_ker⟩ := haction
  refine ⟨phi, hphi_surjective, hphi_ker, ?_⟩
  intro R1 hR1_p hRSigma_le hR1_le hnormalizes hindex_three hindex_two
  have hsylow_completion :
      ∃ R2s : Sylow 3 G,
        R1 ≤ (R2s : Subgroup G) ∧
          ((R1.subgroupOf (R2s : Subgroup G)).index = 1 ∨
            (R1.subgroupOf (R2s : Subgroup G)).index = 3) ∧
            R1 ⊓ Subgroup.centralizer (R1 : Set G) = Z1 ∧
              (R2s : Subgroup G) ⊓
                  Subgroup.centralizer
                    ((R2s : Subgroup G) : Set G) = Z1 ∧
                (R2s : Subgroup G) ⊓ Subgroup.centralizer (P : Set G) =
                  R ⊔ Sigma := by
    classical
    letI : Fact (Nat.Prime 3) := ⟨by decide⟩
    let X : Subgroup G := R ⊔ Sigma
    let CP : Subgroup G := Subgroup.centralizer (P : Set G)
    let C0 : Subgroup G := Z1 ⊔ P
    have hXcard : Nat.card X = 3 ^ 4 := by
      simpa [X] using h11Local.2.1
    have hX_le_R1 : X ≤ R1 := by
      simpa [X] using hRSigma_le
    have hX_index_R1 : (X.subgroupOf R1).index = 3 := by
      simpa [X] using hindex_three
    have hXsubR1card : Nat.card (X.subgroupOf R1) = 3 ^ 4 := by
      calc
        Nat.card (X.subgroupOf R1) = Nat.card X :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe hX_le_R1).toEquiv
        _ = 3 ^ 4 := hXcard
    have hR1card : Nat.card R1 = 3 ^ 5 := by
      have hmul := (X.subgroupOf R1).index_mul_card
      rw [hX_index_R1, hXsubR1card] at hmul
      norm_num at hmul ⊢
      omega
    obtain ⟨R2s, hR1_le_R2s⟩ := hR1_p.exists_le_sylow
    let R2g : Subgroup G := (R2s : Subgroup G)
    have hR1_le_R2g : R1 ≤ R2g := by
      simpa [R2g] using hR1_le_R2s
    have hR2p : IsPGroup 3 R2g := by
      simpa [R2g] using R2s.isPGroup'
    have hR1subR2card : Nat.card (R1.subgroupOf R2g) = 3 ^ 5 := by
      calc
        Nat.card (R1.subgroupOf R2g) = Nat.card R1 :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (by
              exact hR1_le_R2g)).toEquiv
        _ = 3 ^ 5 := hR1card
    obtain ⟨_globalK, u, _hglobalPow, hGcard, hu⟩ :=
      hExceptionalCase.2.2.2.2.2.1
    have hu_ne : u ≠ 0 := by
      intro hu0
      apply hu
      rw [hu0]
      exact dvd_zero 3
    have hR2index :
        (R1.subgroupOf R2g).index = 1 ∨
          (R1.subgroupOf R2g).index = 3 := by
      rcases hExceptionalCase.2.2.2.2.1 with hWcard | hWcard
      · left
        have hGcard' : Nat.card G = 3 ^ 5 * u := by
          rw [hGcard, hWcard]
          norm_num
        have hfac : (Nat.card G).factorization 3 = 5 := by
          rw [hGcard', Nat.factorization_mul (by norm_num) hu_ne,
            Nat.factorization_pow]
          simp [Nat.prime_three.factorization,
            Nat.factorization_eq_zero_of_not_dvd hu]
        have hR2card : Nat.card R2g = 3 ^ 5 := by
          simpa [R2g, hfac] using R2s.card_eq_multiplicity
        have hmul := (R1.subgroupOf R2g).index_mul_card
        rw [hR1subR2card, hR2card] at hmul
        norm_num at hmul ⊢
        omega
      · right
        have hGcard' : Nat.card G = 3 ^ 6 * u := by
          rw [hGcard, hWcard]
          norm_num
        have hfac : (Nat.card G).factorization 3 = 6 := by
          rw [hGcard', Nat.factorization_mul (by norm_num) hu_ne,
            Nat.factorization_pow]
          simp [Nat.prime_three.factorization,
            Nat.factorization_eq_zero_of_not_dvd hu]
        have hR2card : Nat.card R2g = 3 ^ 6 := by
          simpa [R2g, hfac] using R2s.card_eq_multiplicity
        have hmul := (R1.subgroupOf R2g).index_mul_card
        rw [hR1subR2card, hR2card] at hmul
        norm_num at hmul ⊢
        omega
    have hC0_le_X : C0 ≤ X := by
      simpa [C0, X] using hlocal_center_data.1.trans inf_le_left
    have hP_le_CX : P ≤ Subgroup.centralizer (X : Set G) := by
      intro q hqP
      have hqC0 : q ∈ C0 := by
        dsimp [C0]
        exact Subgroup.mem_sup_right hqP
      have hqCenter : q ∈ X ⊓ Subgroup.centralizer (X : Set G) := by
        simpa [C0, X, hcenter] using hqC0
      exact hqCenter.2
    have hX_le_CP : X ≤ CP := by
      dsimp [CP]
      exact Subgroup.le_centralizer_iff.mpr hP_le_CX
    have hR1_inf_CP : R1 ⊓ CP = X := by
      simpa [CP, X] using
        claim14_inf_centralizer_eq_of_local_sylow P X R1
          (by simpa [CP] using hX_le_CP) hRSigmaSylowCP hX_le_R1 hR1_p
    have hX_le_R2 : X ≤ R2g := by
      exact hX_le_R1.trans (by simpa [R2g] using hR1_le_R2s)
    have hR2_inf_CP : R2g ⊓ CP = X := by
      simpa [CP, X] using
        claim14_inf_centralizer_eq_of_local_sylow P X R2g
          (by simpa [CP] using hX_le_CP) hRSigmaSylowCP hX_le_R2 hR2p
    have hZ1_le_X : Z1 ≤ X := le_sup_left.trans hC0_le_X
    have hR1_norm_X : R1 ≤ Subgroup.normalizer (X : Set G) := by
      simpa [X] using hR1_le
    have hcommX : ⁅X, X⁆ = Z1 := by
      simpa [X] using hderived
    have hR1_le_CZ1 : R1 ≤ Subgroup.centralizer (Z1 : Set G) :=
      claim14_pgroup_le_centralizer_of_commutator_eq
        X Z1 R1 hZ1card hcommX hR1_p hR1_norm_X
    let C1 : Subgroup G := R1 ⊓ Subgroup.centralizer (R1 : Set G)
    have hZ1_le_C1 : Z1 ≤ C1 := by
      apply le_inf (hZ1_le_X.trans hX_le_R1)
      exact Subgroup.le_centralizer_iff.mpr hR1_le_CZ1
    have hC1_le_X : C1 ≤ X := by
      intro c hc
      have hcCP : c ∈ CP := by
        dsimp [CP]
        have hP_le_R1 : P ≤ R1 := by
          have hP_le_X : P ≤ X := by
            exact (show P ≤ C0 by
              dsimp [C0]
              exact le_sup_right).trans hC0_le_X
          exact hP_le_X.trans hX_le_R1
        exact Subgroup.centralizer_le
          hP_le_R1 hc.2
      have hcInf : c ∈ R1 ⊓ CP := ⟨hc.1, hcCP⟩
      rw [hR1_inf_CP] at hcInf
      exact hcInf
    have hC1_le_C0 : C1 ≤ C0 := by
      intro c hc
      have hcCX : c ∈ Subgroup.centralizer (X : Set G) :=
        Subgroup.centralizer_le hX_le_R1 hc.2
      have hcCenter : c ∈ X ⊓ Subgroup.centralizer (X : Set G) :=
        ⟨hC1_le_X hc, hcCX⟩
      simpa [C0, X, hcenter] using hcCenter
    have hZ1_disj_P : Disjoint Z1 P := hR.2.1.mono hZ1_le_T le_rfl
    have hZ1_le_CP : Z1 ≤ Subgroup.centralizer (P : Set G) :=
      hZ1_le_T.trans hR.2.2.1
    have hP_norm_Z1 : P ≤ Subgroup.normalizer (Z1 : Set G) :=
      (Subgroup.le_centralizer_iff.mpr hZ1_le_CP).trans
        (claim14_centralizer_le_normalizer Z1)
    have hC0card : Nat.card C0 = 9 := by
      calc
        Nat.card C0 = Nat.card Z1 * Nat.card P := by
          simpa [C0] using
            claim14_natCard_sup_eq_mul_of_disjoint_of_le_normalizer
              Z1 P hP_norm_Z1 hZ1_disj_P
        _ = 9 := by rw [hZ1card, hPcard]
    have hZ1subC0card : Nat.card (Z1.subgroupOf C0) = 3 := by
      calc
        Nat.card (Z1.subgroupOf C0) = Nat.card Z1 :=
          Nat.card_congr
            (Subgroup.subgroupOfEquivOfLe (by
              dsimp [C0]
              exact le_sup_left)).toEquiv
        _ = 3 := hZ1card
    have hZ1relC0 : Z1.relIndex C0 = 3 := by
      change (Z1.subgroupOf C0).index = 3
      have hmul := (Z1.subgroupOf C0).index_mul_card
      rw [hZ1subC0card, hC0card] at hmul
      omega
    have hC1_cases : C1 = Z1 ∨ C1 = C0 := by
      have hprod := Subgroup.relIndex_mul_relIndex Z1 C1 C0
        hZ1_le_C1 hC1_le_C0
      rw [hZ1relC0] at hprod
      have hdvd : Z1.relIndex C1 ∣ 3 :=
        ⟨C1.relIndex C0, hprod.symm⟩
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with hidx | hidx
      · left
        exact le_antisymm (Subgroup.relIndex_eq_one.mp hidx) hZ1_le_C1
      · right
        have hlast : C1.relIndex C0 = 1 := by
          rw [hidx] at hprod
          omega
        exact le_antisymm hC1_le_C0
          (Subgroup.relIndex_eq_one.mp hlast)
    have hcenter_R1 : C1 = Z1 := by
      rcases hC1_cases with hEq | hEq
      · exact hEq
      · exfalso
        have hP_le_C1 : P ≤ C1 := by
          rw [hEq]
          dsimp [C0]
          exact le_sup_right
        have hP_le_CR1 : P ≤ Subgroup.centralizer (R1 : Set G) :=
          hP_le_C1.trans inf_le_right
        have hR1_le_CP : R1 ≤ CP := by
          dsimp [CP]
          exact Subgroup.le_centralizer_iff.mpr hP_le_CR1
        have hR1_le_X : R1 ≤ X := by
          intro r hr
          have hrInf : r ∈ R1 ⊓ CP := ⟨hr, hR1_le_CP hr⟩
          rw [hR1_inf_CP] at hrInf
          exact hrInf
        have hindex_one : (X.subgroupOf R1).index = 1 := by
          apply Subgroup.index_eq_one.mpr
          exact Subgroup.subgroupOf_eq_top.mpr hR1_le_X
        omega
    let C2 : Subgroup G := R2g ⊓ Subgroup.centralizer (R2g : Set G)
    have hC2_le_X : C2 ≤ X := by
      intro c hc
      have hcCP : c ∈ CP := by
        dsimp [CP]
        have hP_le_R2 : P ≤ R2g := by
          have hP_le_X : P ≤ X := by
            exact (show P ≤ C0 by
              dsimp [C0]
              exact le_sup_right).trans hC0_le_X
          exact hP_le_X.trans hX_le_R2
        exact Subgroup.centralizer_le
          hP_le_R2 hc.2
      have hcInf : c ∈ R2g ⊓ CP := ⟨hc.1, hcCP⟩
      rw [hR2_inf_CP] at hcInf
      exact hcInf
    have hC2_le_Z1 : C2 ≤ Z1 := by
      intro c hc
      have hcC1 : c ∈ C1 := by
        refine ⟨hX_le_R1 (hC2_le_X hc), ?_⟩
        exact Subgroup.centralizer_le
          hR1_le_R2g hc.2
      rw [hcenter_R1] at hcC1
      exact hcC1
    have hR1_ne_bot : R1 ≠ ⊥ := by
      intro hbot
      rw [hbot] at hR1card
      norm_num at hR1card
    have hR2_ne_bot : R2g ≠ ⊥ := by
      intro hbot
      apply hR1_ne_bot
      apply le_antisymm
      · intro r hr
        have : r ∈ R2g := hR1_le_R2g hr
        rw [hbot] at this
        exact this
      · exact bot_le
    letI : Nontrivial R2g :=
      (Subgroup.nontrivial_iff_ne_bot R2g).mpr hR2_ne_bot
    have hcenter_internal_ne : Subgroup.center R2g ≠ ⊥ :=
      (Subgroup.nontrivial_iff_ne_bot (Subgroup.center R2g)).mp
        hR2p.center_nontrivial
    have hcenter_map :
        (Subgroup.center R2g).map R2g.subtype = C2 := by
      simpa [C2] using claim14_center_map_subtype R2g
    have hC2_ne_bot : C2 ≠ ⊥ := by
      intro hC2bot
      have hmapbot : (Subgroup.center R2g).map R2g.subtype = ⊥ := by
        rw [hcenter_map, hC2bot]
      have hcenterbot : Subgroup.center R2g = ⊥ :=
        (Subgroup.map_eq_bot_iff_of_injective
          (Subgroup.center R2g) R2g.subtype_injective).mp hmapbot
      exact hcenter_internal_ne hcenterbot
    have hC2p : IsPGroup 3 C2 := by
      exact IsPGroup.to_inf_left (K := Subgroup.centralizer (R2g : Set G)) hR2p
    have hC2card_ne_one : Nat.card C2 ≠ 1 := by
      intro hcard
      apply hC2_ne_bot
      exact Subgroup.card_eq_one.mp hcard
    have hthree_dvd_C2 : 3 ∣ Nat.card C2 :=
      hC2p.card_eq_or_dvd.resolve_left hC2card_ne_one
    have hthree_le_C2 : 3 ≤ Nat.card C2 :=
      Nat.le_of_dvd Nat.card_pos hthree_dvd_C2
    have hcenter_R2 : C2 = Z1 :=
      Subgroup.eq_of_le_of_card_ge hC2_le_Z1 (by
        rw [hZ1card]
        exact hthree_le_C2)
    exact ⟨R2s, hR1_le_R2s, by simpa [R2g] using hR2index,
      by simpa [C1] using hcenter_R1, by simpa [R2g, C2] using hcenter_R2,
      by simpa [R2g, CP, X] using hR2_inf_CP⟩
  exact hsylow_completion

public theorem claim_14
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q K V W Q0 S Q1 P Sigma Z1 R T : Subgroup G) (t s : G) (p : ℕ)
    (hch : (((_root_.CFSG.BenderSuzuki.PFchapter1section1.HypothesisA G Ω H D Q t ∧
  K ≤ D ∧
    (∀ x : G, x ∈ K ↔ x ∈ D ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.rightConjugateElem x t = x⁻¹) ∧
      V = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviV D t ∧
        W ≤ V ∧
          W = _root_.CFSG.BenderSuzuki.PFchapter1section1.peterfalviW V (K : Set G) ∧
            Q0 ≤ Q ∧
              (∀ x : G, x ∈ Q0 ↔ x = 1 ∨ (x ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution x)) ∧
                S ≤ Q ∧
                  Q1 ≤ Q ∧
                    (∃ P : Sylow 2 Q, S = (P : Subgroup Q).map Q.subtype) ∧
                      Odd (Nat.card Q1) ∧
                        Disjoint S Q1 ∧
                          (∀ s : G, s ∈ S → ∀ q1 : G, q1 ∈ Q1 → s * q1 = q1 * s) ∧
                            S ⊔ Q1 = Q) ∧
  s ∈ H ∧ _root_.CFSG.BenderSuzuki.PFAppendixIII.IsInvolution s ∧
    ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) ∧
  _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB1 G V P p ∧
    _root_.CFSG.BenderSuzuki.PFchapter2.HypothesisB2 G p))
    (hSigma : Sigma = W ⊓ Subgroup.centralizer (P : Set G))
    (hExceptionalCase : p = 3 ∧ Nat.card Sigma = 3 ∧
      Nat.card (nearFieldStar Q P) = 8 ∧ IsCyclic W ∧
        (Nat.card W = 3 ∨ Nat.card W = 9) ∧
          (∃ k u : ℕ, 3 ^ 4 * Nat.card W = 3 ^ k ∧
            Nat.card G = (3 ^ 4 * Nat.card W) * u ∧ ¬ 3 ∣ u) ∧
            ∃ (F : Type*) (_ : PFAppendixII.RightNearField F) (_ : Finite F)
                (_ : Nontrivial F),
              PFAppendixII.IsDicksonIndexTwoModel F 3 1 ∧
                Nonempty (nearFieldStar Q P ≃* Fˣ))
    (hZ1 : Z1 = Subgroup.zpowers (s * t))
    (hCZ1 : ∃ n : ℕ, Nat.card (Subgroup.centralizer (Z1 : Set G)) = 3 ^ n)
    (hR : R = T ⊔ P ∧
      Disjoint T P ∧
        T ≤ Subgroup.centralizer (P : Set G) ∧
          (Q ⊓ Subgroup.centralizer (P : Set G) ⊔
            W ⊓ Subgroup.centralizer (P : Set G)) ≤
              Subgroup.normalizer (T : Set G) ∧
            Disjoint T (Q ⊓ Subgroup.centralizer (P : Set G)) ∧
              ∀ A B : Subgroup G,
                A ≤ R → B ≤ R → Nat.card A = p → Nat.card B = p →
                  ¬ A ≤ T → ¬ B ≤ T → A ≠ P → B ≠ P →
                    ∃! c : G,
                      c ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                        B = rightConjugate A c)
    (hModel :
      ∃ (N : Subgroup G) (F : Type*) (_ : PFAppendixII.RightNearField F)
          (_ : Finite F) (_ : Nontrivial F)
          (addEquiv : Multiplicative F ≃* ↥T)
          (unitEquiv : Fˣ ≃* ↥(Q ⊓ Subgroup.centralizer (P : Set G))),
        N = D ⊓
            Subgroup.centralizer
              ((Q ⊓ Subgroup.centralizer (P : Set G)) : Set G) ⊓
            Subgroup.centralizer (P : Set G) ∧
          R ≤ Subgroup.centralizer (P : Set G) ∧
            (∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
              (g ∈ R ↔ ∃ x : F,
                g * (((addEquiv (Multiplicative.ofAdd x) : T) : G))⁻¹ ∈ N)) ∧
              (∀ x : G, x ∈ T → rightConjugateElem x s = x⁻¹) ∧
                s * t ∈ T ∧
                (∀ a : F, ∀ b : Fˣ,
                  rightConjugateElem
                      (((addEquiv (Multiplicative.ofAdd a) : T) : G))
                      (((unitEquiv b : ↥(Q ⊓
                        Subgroup.centralizer (P : Set G))) : G)) =
                    (((addEquiv (Multiplicative.ofAdd (a * (b : F))) : T) : G))) ∧
                  addOrderOf (1 : F) = orderOf (s * t) ∧
                    (p = 3 →
                      Nat.card (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) = 3 →
                      Nat.card (nearFieldStar Q P) = 8 →
                      let Sigma0 : Subgroup G :=
                        W ⊓ Subgroup.centralizer (P : Set G)
                      Disjoint R Sigma0 ∧
                        Nat.card (R ⊔ Sigma0 : Subgroup G) = 3 ^ 4 ∧
                          ¬ IsMulCommutative (R ⊔ Sigma0 : Subgroup G) ∧
                            (∃ XC : Sylow 3 (Subgroup.centralizer (P : Set G)),
                              (XC : Subgroup (Subgroup.centralizer (P : Set G))) =
                                (R ⊔ Sigma0).subgroupOf
                                  (Subgroup.centralizer (P : Set G))) ∧
                              ∀ g : G, g ∈ Subgroup.centralizer (P : Set G) →
                                ∃ r q w : G, r ∈ R ∧
                                  q ∈ Q ⊓ Subgroup.centralizer (P : Set G) ∧
                                    w ∈ Sigma0 ∧ g = r * q * w) ∧
                    (∀ m' : ℕ,
                      Nat.card (nearFieldStar Q P) + 1 = p ^ m' →
                      ¬ p ∣ Nat.card
                        (W ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) →
                      Subgroup.centralizer (P : Set G) ≤
                          Subgroup.normalizer (R : Set G) ∧
                        Nat.card R = p ^ (m' + 1) ∧
                          Nat.card (Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) + 1 =
                            p ^ m' ∧
                            ∃ RC : Sylow p (Subgroup.centralizer (P : Set G)),
                              (RC : Subgroup (Subgroup.centralizer (P : Set G))) =
                                R.subgroupOf
                                  (Subgroup.centralizer (P : Set G)))) :
    ∃ R1 R2 : Subgroup G,
      (Sigma ≤ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer (R : Set G) ∧
          s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
            Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
              (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
                Z1 ⊔ P ∧
                R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                  R ⊔ Sigma ≤ R1 ∧
                    R2 = Subgroup.centralizer (Z1 : Set G) ∧
                      R1 ≤ R2) ∧
      (IsPGroup 3 R1 ∧
        (∃ R2s : Sylow 3 G, (R2s : Subgroup G) = R2) ∧
          (∃ phi : (Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G)) →*
                Equiv.Perm (Fin 3),
            Function.Surjective phi ∧
              MonoidHom.ker phi =
                (R ⊔ Sigma).subgroupOf
                  (Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G))) ∧
            Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              R1 ⊔ Subgroup.closure ({s} : Set G) ∧
              Disjoint R1 (Subgroup.closure ({s} : Set G)) ∧
                Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ≤
                  Subgroup.normalizer (R1 : Set G) ∧
                  ((R1.subgroupOf R2).index = 1 ∨ (R1.subgroupOf R2).index = 3) ∧
                    R1 ⊓ Subgroup.centralizer (R1 : Set G) = Z1 ∧
                      R2 ⊓ Subgroup.centralizer (R2 : Set G) = Z1 ∧
                        ⁅(R ⊔ Sigma : Subgroup G), (R ⊔ Sigma : Subgroup G)⁆ = Z1 ∧
                          R2 ⊓ Subgroup.centralizer (P : Set G) = R ⊔ Sigma) := by
  have hsC : s ∈ Subgroup.centralizer (P : Set G) :=
    claim14_s_mem_centralizer_P H D Q K V W Q0 S Q1 P t s p hch
  have hModelSource := hModel
  rcases hModel with
    ⟨_N, F, hFnear, hFfinite, hFnontrivial, addEquiv, unitEquiv,
      _hN, _hRcentral, _hinverse, hT_inverted, hst_mem_T, _hconjugation,
      hchar_order, h11ExceptionalLocal, _h11CaseOneLocal⟩
  letI : PFAppendixII.RightNearField F := hFnear
  letI : Finite F := hFfinite
  letI : Nontrivial F := hFnontrivial
  have hunit_card : Nat.card Fˣ = 8 := by
    calc
      Nat.card Fˣ = Nat.card ↥(Q ⊓ Subgroup.centralizer (P : Set G) : Subgroup G) :=
        Nat.card_congr unitEquiv.toEquiv
      _ = 8 := by
        simpa [nearFieldStar] using hExceptionalCase.2.2.1
  have hFcard : Nat.card F = 9 := by
    calc
      Nat.card F = Nat.card Fˣ + 1 := Nat.card_eq_card_units_add_one F
      _ = 9 := by rw [hunit_card]
  have hTcard : Nat.card T = 9 := by
    calc
      Nat.card T = Nat.card (Multiplicative F) :=
        (Nat.card_congr addEquiv.toEquiv).symm
      _ = Nat.card F := rfl
      _ = 9 := hFcard
  have hT3 : IsPGroup 3 T :=
    IsPGroup.of_card (n := 2) (by norm_num [hTcard])
  have hP3 : IsPGroup 3 P :=
    IsPGroup.of_card (n := 1) (by
      rw [pow_one, hch.B1.P_card, hExceptionalCase.1])
  have hP_norm_T : P ≤ Subgroup.normalizer (T : Set G) := by
    intro x hxP
    apply claim14_centralizer_le_normalizer T
    rw [Subgroup.mem_centralizer_iff]
    intro y hyT
    exact
      ((Subgroup.mem_centralizer_iff.mp (hR.2.2.1 hyT)) x hxP).symm
  have hR3 : IsPGroup 3 R := by
    have hTP3 := IsPGroup.to_sup_of_normal_left' hT3 hP3 hP_norm_T
    rw [← hR.1] at hTP3
    exact hTP3
  have hSigma3 : IsPGroup 3 Sigma :=
    IsPGroup.of_card (n := 1) (by
      rw [pow_one, hExceptionalCase.2.1])
  have hSigma_norm_R : Sigma ≤ Subgroup.normalizer (R : Set G) :=
    claim14_sigma_le_normalizer_R_of_R_structure Q W P Sigma R p hSigma ⟨T, hR⟩
  have hRSigma_p : IsPGroup 3 (R ⊔ Sigma : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' hR3 hSigma3 hSigma_norm_R
  have hs_norm_R : s ∈ Subgroup.normalizer (R : Set G) :=
    claim14_s_mem_normalizer_R T P R s hch.section3.2.2.1 hsC
      hT_inverted hR.1
  have hs_norm_RSigma :
      s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) :=
    claim14_s_mem_normalizer_R_sup_Sigma H D Q V W P Sigma R t s
      hch.section3.section2.hA.A1 hch.section3.2.1 hch.section3.2.2.1
      hch.section3.2.2.2 hch.section3.section2.V_eq
      hch.section3.section2.W_le_V hSigma hsC hs_norm_R
  have hZ1_le_T : Z1 ≤ T := by
    rw [hZ1]
    exact Subgroup.zpowers_le.mpr hst_mem_T
  rcases
    chapter2_claim14_center_action_sylow_source_interface
      H D Q K V W Q0 S Q1 P Sigma Z1 R T t s p
      hch hSigma hExceptionalCase hZ1 hCZ1 hR hModelSource with
    ⟨hcenter_eq, hcommutator_eq,
      phi, hphi, hker, hsource_endpoint⟩
  have hcenter_contains :
      Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) :=
    claim14_center_R_contains_Z1_sup_P T P Z1 R addEquiv
      (by rw [hch.B1.P_card, hExceptionalCase.1]) hR.2.2.1 hR.1 hZ1_le_T
  rcases
    claim14_exists_a3_preimage
      (R ⊔ Sigma) (Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G))
      Subgroup.le_normalizer phi hphi hker hRSigma_p s hs_norm_RSigma
      hch.section3.2.2.1 with
    ⟨R1, hR1p, hRSigma_le_R1, hR1_norm_RSigma, hnormalizer_norm_R1,
      hRSigma_index, hR1_normalizer_index, hnormalizer_split, hR1_disjoint_s⟩
  have hchar_dvd_nine : addOrderOf (1 : F) ∣ 9 := by
    simpa [hFcard] using addOrderOf_dvd_natCard (1 : F)
  have hchar_three : addOrderOf (1 : F) = 3 := by
    have hprime := PFAppendixII.rightNearField_addOrderOf_one_prime (F := F)
    have hdiv : addOrderOf (1 : F) ∣ 3 ^ 2 := by
      simpa using hchar_dvd_nine
    exact Nat.prime_eq_prime_of_dvd_pow hprime Nat.prime_three hdiv
  have hZ1card : Nat.card Z1 = 3 := by
    rw [hZ1, Nat.card_zpowers, ← hchar_order, hchar_three]
  have hR1_le_CZ1 : R1 ≤ Subgroup.centralizer (Z1 : Set G) :=
    claim14_pgroup_le_centralizer_of_commutator_eq
      (R ⊔ Sigma) Z1 R1 hZ1card hcommutator_eq hR1p hR1_norm_RSigma
  rcases
    hsource_endpoint R1 hR1p hRSigma_le_R1 hR1_norm_RSigma
      hnormalizer_norm_R1 hRSigma_index hR1_normalizer_index with
    ⟨R2s, hR1_le_R2s, hR2_index_source, hcenter_R1, hcenter_R2_source,
      hR2_inf_CP_source⟩
  have hZ1_le_CR2s :
      Z1 ≤ Subgroup.centralizer ((R2s : Subgroup G) : Set G) := by
    rw [← hcenter_R2_source]
    exact inf_le_right
  have hR2s_le_CZ1 :
      (R2s : Subgroup G) ≤ Subgroup.centralizer (Z1 : Set G) :=
    Subgroup.le_centralizer_iff.mpr hZ1_le_CR2s
  obtain ⟨nCZ1, hCZ1card⟩ := hCZ1
  have hCZ1p : IsPGroup 3 (Subgroup.centralizer (Z1 : Set G)) :=
    IsPGroup.of_card hCZ1card
  have hR2s_eq_CZ1 :
      (R2s : Subgroup G) = Subgroup.centralizer (Z1 : Set G) :=
    (R2s.is_maximal' hCZ1p hR2s_le_CZ1).symm
  let R2 : Subgroup G := Subgroup.centralizer (Z1 : Set G)
  have hR1_le_R2 : R1 ≤ R2 := by
    simpa [R2] using hR1_le_CZ1
  have hR2s' : ∃ R2s : Sylow 3 G, (R2s : Subgroup G) = R2 := by
    exact ⟨R2s, by simpa [R2] using hR2s_eq_CZ1⟩
  have hR2_index' :
      (R1.subgroupOf R2).index = 1 ∨ (R1.subgroupOf R2).index = 3 := by
    have hR2_index_source' := hR2_index_source
    rw [hR2s_eq_CZ1] at hR2_index_source'
    simpa [R2] using hR2_index_source'
  have hcenter_R2' : R2 ⊓ Subgroup.centralizer (R2 : Set G) = Z1 := by
    simpa [R2, hR2s_eq_CZ1] using hcenter_R2_source
  have hR2_inf_CP' :
      R2 ⊓ Subgroup.centralizer (P : Set G) = R ⊔ Sigma := by
    simpa [R2, hR2s_eq_CZ1] using hR2_inf_CP_source
  have hOld : Sigma ≤ Subgroup.normalizer (R : Set G) ∧
      s ∈ Subgroup.normalizer (R : Set G) ∧
        s ∈ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
          Z1 ⊔ P ≤ R ⊓ Subgroup.centralizer (R : Set G) ∧
            (R ⊔ Sigma) ⊓ Subgroup.centralizer ((R ⊔ Sigma : Subgroup G) : Set G) =
              Z1 ⊔ P ∧
              R1 ≤ Subgroup.normalizer ((R ⊔ Sigma : Subgroup G) : Set G) ∧
                R ⊔ Sigma ≤ R1 ∧
                  R2 = Subgroup.centralizer (Z1 : Set G) ∧
                    R1 ≤ R2 :=
    ⟨hSigma_norm_R, hs_norm_R, hs_norm_RSigma, hcenter_contains, hcenter_eq,
      hR1_norm_RSigma, hRSigma_le_R1, rfl, hR1_le_R2⟩
  exact ⟨R1, R2, hOld, hR1p, hR2s', ⟨phi, hphi, hker⟩,
    hnormalizer_split, hR1_disjoint_s, hnormalizer_norm_R1, hR2_index',
    hcenter_R1, hcenter_R2', hcommutator_eq, hR2_inf_CP'⟩

end PFchapter2
end CFSG.BenderSuzuki
