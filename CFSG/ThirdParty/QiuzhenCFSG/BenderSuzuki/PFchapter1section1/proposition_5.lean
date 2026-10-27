module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.lemma_a
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_b

namespace CFSG
end CFSG
open CFSG

namespace CFSG.BenderSuzuki
namespace PFchapter1section1

open PFAppendixIII

/-!
# Peterfalvi, Part II, Chapter I, Section 1, Proposition 5
-/


private theorem mul_comm_of_mem_centralizer_singleton
    {G : Type*} [Group G] {x y : G}
    (hx : x ∈ Subgroup.centralizer ({y} : Set G)) :
    x * y = y * x := by
  exact ((Subgroup.mem_centralizer_iff.mp hx) y (by simp)).symm

private theorem rightConjugateElem_eq_self_iff_mem_centralizer_singleton
    {G : Type*} [Group G] {s v : G} :
    rightConjugateElem s v = s ↔ v ∈ Subgroup.centralizer ({s} : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc
      v * s = v * rightConjugateElem s v := by rw [h]
      _ = s * v := by simp [rightConjugateElem, mul_assoc]
  · intro hv
    have hcomm : v * s = s * v := mul_comm_of_mem_centralizer_singleton hv
    calc
      rightConjugateElem s v = v⁻¹ * s * v := rfl
      _ = (v⁻¹ * v) * s := by
            simp [← hcomm, mul_assoc]
      _ = s := by group

private theorem eq_one_of_sq_eq_one_mem_odd_subgroup
    {G : Type*} [Group G] [Finite G] (D : Subgroup G)
    (hDodd : Odd (Nat.card D)) {x : G} (hxD : x ∈ D) (hx2 : x ^ 2 = 1) :
    x = 1 := by
  by_contra hxne
  let xD : D := ⟨x, hxD⟩
  have hxD_sq : xD ^ 2 = 1 := by
    ext
    simpa [xD] using hx2
  have hxD_ne : xD ≠ 1 := by
    intro h
    exact hxne (Subtype.ext_iff.mp h)
  have htwo_dvd : 2 ∣ orderOf xD := by
    rw [orderOf_eq_prime hxD_sq hxD_ne]
  have horder_dvd : orderOf xD ∣ Nat.card D :=
    orderOf_dvd_natCard xD
  have horder_odd : Odd (orderOf xD) :=
    Odd.of_dvd_nat hDodd horder_dvd
  exact horder_odd.not_two_dvd_nat htwo_dvd

private theorem rightConjugateElem_mem_D_of_mem_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) {d : G} (hd : d ∈ D) :
    rightConjugateElem d t ∈ D := by
  classical
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  have hd' : d ∈ H ⊓ rightConjugate H t := by
    simpa [hA1.D_eq] using hd
  rw [hA1.D_eq]
  refine ⟨?_, ?_⟩
  · rcases hd'.2 with ⟨h, hhH, hhd⟩
    have tht : t * h * t = d := by
      simpa [MulAut.conj, htinv, mul_assoc] using hhd
    have hconj_eq : rightConjugateElem d t = h := by
      calc
        rightConjugateElem d t = t * d * t := by simp [rightConjugateElem, htinv]
        _ = t * (t * h * t) * t := by rw [← tht]
        _ = (t * t) * h * (t * t) := by simp [mul_assoc]
        _ = h := by simp [htt]
    rw [hconj_eq]
    exact hhH
  · refine ⟨d, hd'.1, ?_⟩
    simp [rightConjugateElem]

/-- The distinguished involution normalizes the two-point stabilizer `D`. -/
public theorem proposition_5_involution_t_mem_normalizer_D
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t : G)
    (hA1 : HypothesisA1 G Ω H D Q t) :
    t ∈ Subgroup.normalizer (D : Set G) := by
  have htinv : t⁻¹ = t := hA1.involution_t.inv_eq_self
  have htt : t * t = 1 := by
    simpa [pow_two] using hA1.involution_t.sq_eq_one
  rw [Subgroup.mem_normalizer_iff'']
  intro d
  constructor
  · intro hd
    simpa [rightConjugateElem, htinv] using
      (rightConjugateElem_mem_D_of_mem_D H D Q t hA1 (d := d) hd)
  · intro hd
    have hmem :=
      rightConjugateElem_mem_D_of_mem_D H D Q t hA1
        (d := t⁻¹ * d * t) hd
    have htd : t * (t * d) = d := by
      calc
        t * (t * d) = (t * t) * d := by simp [mul_assoc]
        _ = 1 * d := by rw [htt]
        _ = d := by simp
    have hmem' : t * (t * d) ∈ D := by
      simpa [rightConjugateElem, htinv, htt, mul_assoc] using hmem
    simpa [htd] using hmem'

private theorem peterfalviV_le_centralizer_distinguished
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) :
    peterfalviV D t ≤ D ⊓ Subgroup.centralizer ({s} : Set G) := by
  classical
  intro v hv
  change v ∈ D ⊓ Subgroup.centralizer ({t} : Set G) at hv
  rcases hsStructure with ⟨r, hrQ, hstr⟩
  obtain ⟨p, _hp, hpuniq⟩ := proposition_4_b H D Q t hA1
  have hs_pair : (s, r) = p :=
    hpuniq (s, r) ⟨hsH, hsI, hrQ, hstr⟩
  have hvD : v ∈ D := hv.1
  have hvH : v ∈ H := hA1.D_le_H hvD
  have hv_cent_t : v ∈ Subgroup.centralizer ({t} : Set G) := hv.2
  have hvt : v * t = t * v := mul_comm_of_mem_centralizer_singleton hv_cent_t
  have hsvH : rightConjugateElem s v ∈ H := by
    exact H.mul_mem (H.mul_mem (H.inv_mem hvH) hsH) hvH
  have hsvI : IsInvolution (rightConjugateElem s v) :=
    isInvolution_rightConjugateElem hsI
  have hrvQ : rightConjugateElem r v ∈ Q := by
    let rH : H := ⟨r, hA1.Q_le_H hrQ⟩
    let vH : H := ⟨v, hvH⟩
    have hrQsub : rH ∈ Q.subgroupOf H := by
      simpa [rH, Subgroup.mem_subgroupOf] using hrQ
    have hmem := hA1.Q_normal_in_H.conj_mem rH hrQsub vH⁻¹
    simpa [rH, vH, Subgroup.mem_subgroupOf, rightConjugateElem, mul_assoc] using hmem
  have hstrv :
      t * rightConjugateElem s v * t =
        (rightConjugateElem r v)⁻¹ * t * rightConjugateElem r v := by
    unfold rightConjugateElem
    have hvt_inv : t * v⁻¹ = v⁻¹ * t := by
      calc
        t * v⁻¹ = v⁻¹ * (v * t) * v⁻¹ := by group
        _ = v⁻¹ * (t * v) * v⁻¹ := by rw [hvt]
        _ = v⁻¹ * t := by group
    calc
      t * (v⁻¹ * s * v) * t =
          t * v⁻¹ * s * v * t := by group
      _ = v⁻¹ * t * s * v * t := by rw [hvt_inv]
      _ = v⁻¹ * t * s * (v * t) := by group
      _ = v⁻¹ * t * s * (t * v) := by rw [hvt]
      _ = v⁻¹ * t * s * t * v := by group
      _ = v⁻¹ * (t * s * t) * v := by group
      _ = v⁻¹ * (r⁻¹ * t * r) * v := by rw [hstr]
      _ = v⁻¹ * r⁻¹ * t * r * v := by group
      _ = (v⁻¹ * r * v)⁻¹ * t * (v⁻¹ * r * v) := by
            have hvt_conj : v * t * v⁻¹ = t := by
              calc
                v * t * v⁻¹ = (t * v) * v⁻¹ := by rw [hvt]
                _ = t := by group
            calc
              v⁻¹ * r⁻¹ * t * r * v = v⁻¹ * r⁻¹ * (v * t * v⁻¹) * r * v := by
                rw [hvt_conj]
              _ = (v⁻¹ * r * v)⁻¹ * t * (v⁻¹ * r * v) := by group
  have hsv_eq : rightConjugateElem s v = s := by
    have hsv_pair : (rightConjugateElem s v, rightConjugateElem r v) = p :=
      hpuniq (rightConjugateElem s v, rightConjugateElem r v)
        ⟨hsvH, hsvI, hrvQ, hstrv⟩
    exact congrArg Prod.fst (hsv_pair.trans hs_pair.symm)
  exact ⟨hvD, (rightConjugateElem_eq_self_iff_mem_centralizer_singleton.mp hsv_eq)⟩

public theorem proposition_5
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r) :
    peterfalviV D t = D ⊓ Subgroup.centralizer ({s} : Set G) ∧
      peterfalviW (peterfalviV D t) (peterfalviKSet D t) =
        D ⊓ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) := by
  classical
  have hV_le_CD_s :=
    peterfalviV_le_centralizer_distinguished H D Q t s hA1 hsH hsI hsStructure
  have hD_decomp :
      Set.BijOn
        (fun p : (peterfalviV D t) × {x : G // x ∈ peterfalviKSet D t} =>
          (p.1 : G) * (p.2 : G))
        Set.univ (D : Set G) := by
    have hlemma :=
      lemma_a (M := G) t D hA1.involution_t hA1.D_odd
        (proposition_5_involution_t_mem_normalizer_D H D Q t hA1)
    have hleft := hlemma.1
    change Set.BijOn
      (fun p : (peterfalviV D t) × {x : G // x ∈ peterfalviKSet D t} =>
        (p.1 : G) * (p.2 : G)) Set.univ (D : Set G) at hleft
    exact hleft
  have hprop3 := proposition_3 H D Q t hA1
  let S : Set G := {x : G | x ∈ H ∧ IsInvolution x}
  let phi : {x : G // x ∈ peterfalviKSet D t} → {x : G // x ∈ S} := fun k =>
    ⟨rightConjugateElem s (k : G), by
      simpa [S] using
        (hprop3.2 s hsH hsI (rightConjugateElem s (k : G))).2
          ⟨k, k.property, rfl⟩⟩
  have hphi_surj : Function.Surjective phi := by
    rintro ⟨y, hyS⟩
    rcases (hprop3.2 s hsH hsI y).1 (by simpa [S] using hyS) with
      ⟨k, hkK, hk_eq⟩
    refine ⟨⟨k, hkK⟩, ?_⟩
    apply Subtype.ext
    simpa [phi, S] using hk_eq
  have hphi_inj : Function.Injective phi := by
    exact
      (hphi_surj.bijective_of_nat_card_le
        (by simpa [S] using le_of_eq hprop3.1)).1
  have hV_eq : peterfalviV D t = D ⊓ Subgroup.centralizer ({s} : Set G) := by
    apply le_antisymm hV_le_CD_s
    intro d hd
    have hdD : d ∈ D := hd.1
    obtain ⟨p, _hp, hp_eq⟩ := hD_decomp.surjOn hdD
    rcases p with ⟨v, k⟩
    have hvV : (v : G) ∈ peterfalviV D t := v.property
    have hkK : (k : G) ∈ peterfalviKSet D t := k.property
    have hvCs : (v : G) ∈ Subgroup.centralizer ({s} : Set G) :=
      (hV_le_CD_s hvV).2
    have hsd : rightConjugateElem s d = s :=
      (rightConjugateElem_eq_self_iff_mem_centralizer_singleton).2 hd.2
    have hsv_eq : rightConjugateElem s (v : G) = s :=
      (rightConjugateElem_eq_self_iff_mem_centralizer_singleton).2 hvCs
    have hk_eq_s : rightConjugateElem s (k : G) = s := by
      have hprod : (v : G) * (k : G) = d := by simpa using hp_eq
      calc
        rightConjugateElem s (k : G) =
            rightConjugateElem (rightConjugateElem s (v : G)) (k : G) := by
              rw [hsv_eq]
        _ = rightConjugateElem s ((v : G) * (k : G)) := by
              rw [rightConjugateElem_comp]
        _ = rightConjugateElem s d := by rw [hprod]
        _ = s := hsd
    have honeK : (1 : G) ∈ peterfalviKSet D t := by
      simp [peterfalviKSet, rightConjugateElem]
    have hsS : s ∈ S := by
      exact ⟨hsH, hsI⟩
    have hphi_k :
        phi ⟨(k : G), hkK⟩ = ⟨s, hsS⟩ := by
      apply Subtype.ext
      simpa [phi] using hk_eq_s
    have hphi_one :
        phi ⟨1, honeK⟩ = ⟨s, hsS⟩ := by
      apply Subtype.ext
      simp [phi, rightConjugateElem]
    have hk_eq_one_sub :
        (⟨(k : G), hkK⟩ : {x : G // x ∈ peterfalviKSet D t}) = ⟨1, honeK⟩ :=
      hphi_inj (hphi_k.trans hphi_one.symm)
    have hk_one : (k : G) = 1 := congrArg Subtype.val hk_eq_one_sub
    have hd_eq_v : d = (v : G) := by
      calc
        d = (v : G) * (k : G) := hp_eq.symm
        _ = (v : G) := by simp [hk_one]
    simp [hd_eq_v, hvV]
  refine ⟨hV_eq, ?_⟩
  apply le_antisymm
  · intro d hd
    change d ∈ peterfalviV D t ⊓ Subgroup.centralizer (peterfalviKSet D t) at hd
    have hdV : d ∈ peterfalviV D t := hd.1
    have hdK : d ∈ Subgroup.centralizer (peterfalviKSet D t) := hd.2
    have hdDs : d ∈ D ⊓ Subgroup.centralizer ({s} : Set G) := by
      rw [← hV_eq]
      exact hdV
    refine ⟨hdDs.1, ?_⟩
    change d ∈ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x})
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    rcases (hprop3.2 s hsH hsI y).1 hy with ⟨k, hkK, rfl⟩
    have hds : s * d = d * s :=
      (mul_comm_of_mem_centralizer_singleton hdDs.2).symm
    have hdk : k * d = d * k :=
      (Subgroup.mem_centralizer_iff.mp hdK) k hkK
    have hdk_inv : k⁻¹ * d = d * k⁻¹ := by
      calc
        k⁻¹ * d = k⁻¹ * (d * k) * k⁻¹ := by group
        _ = k⁻¹ * (k * d) * k⁻¹ := by rw [← hdk]
        _ = d * k⁻¹ := by group
    calc
      rightConjugateElem s k * d = k⁻¹ * s * (k * d) := by
        simp [rightConjugateElem, mul_assoc]
      _ = k⁻¹ * s * (d * k) := by rw [hdk]
      _ = k⁻¹ * (s * d) * k := by group
      _ = k⁻¹ * (d * s) * k := by rw [hds]
      _ = (k⁻¹ * d) * s * k := by group
      _ = (d * k⁻¹) * s * k := by rw [hdk_inv]
      _ = d * k⁻¹ * s * k := by group
      _ = d * (k⁻¹ * s * k) := by group
      _ = d * rightConjugateElem s k := by rfl
  · intro d hd
    have hdD : d ∈ D := hd.1
    have hdI : d ∈ Subgroup.centralizer ({x : G | x ∈ H ∧ IsInvolution x}) := hd.2
    have hds : s * d = d * s :=
      (Subgroup.mem_centralizer_iff.mp hdI) s ⟨hsH, hsI⟩
    have hdCs : d ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Commute.symm (show Commute s d from hds)
    have hdV : d ∈ peterfalviV D t := by
      rw [hV_eq]
      exact ⟨hdD, hdCs⟩
    refine ⟨hdV, ?_⟩
    change d ∈ Subgroup.centralizer (peterfalviKSet D t)
    rw [Subgroup.mem_centralizer_iff]
    intro k hkK
    have hsk_mem : rightConjugateElem s k ∈ {x : G | x ∈ H ∧ IsInvolution x} := by
      exact (hprop3.2 s hsH hsI (rightConjugateElem s k)).2
        ⟨k, hkK, rfl⟩
    have hdsk : rightConjugateElem s k * d = d * rightConjugateElem s k :=
      (Subgroup.mem_centralizer_iff.mp hdI) (rightConjugateElem s k) hsk_mem
    have hdk : d * k * d⁻¹ ∈ peterfalviKSet D t := by
      refine ⟨D.mul_mem (D.mul_mem hdD hkK.1) (D.inv_mem hdD), ?_⟩
      have hdCt : d ∈ Subgroup.centralizer ({t} : Set G) := by
        change d ∈ D ⊓ Subgroup.centralizer ({t} : Set G) at hdV
        exact hdV.2
      have hdt_comm : Commute d t := by
        rw [Subgroup.mem_centralizer_singleton_iff] at hdCt
        exact hdCt
      have htd_inv : t⁻¹ * d = d * t⁻¹ := hdt_comm.symm.inv_left.eq
      have hdinv_t : d⁻¹ * t = t * d⁻¹ := hdt_comm.inv_left.eq
      calc
        rightConjugateElem (d * k * d⁻¹) t = t⁻¹ * (d * k * d⁻¹) * t := by rfl
        _ = (t⁻¹ * d) * k * (d⁻¹ * t) := by simp [mul_assoc]
        _ = (d * t⁻¹) * k * (t * d⁻¹) := by rw [htd_inv, hdinv_t]
        _ = d * (t⁻¹ * k * t) * d⁻¹ := by group
        _ = d * k⁻¹ * d⁻¹ := by
              simpa [rightConjugateElem, mul_assoc] using
                congrArg (fun z => d * z * d⁻¹) hkK.2
        _ = (d * k * d⁻¹)⁻¹ := by group
    have hphi_eq :
        phi ⟨d * k * d⁻¹, hdk⟩ = phi ⟨k, hkK⟩ := by
      apply Subtype.ext
      have hds_comm : Commute s d := by
        exact hds
      have hd_conj_s : d⁻¹ * s * d = s := by
        calc
          d⁻¹ * s * d = s * (d⁻¹ * d) := by
            rw [hds_comm.symm.inv_left.eq]
            simp [mul_assoc]
          _ = s := by simp
      calc
        rightConjugateElem s (d * k * d⁻¹) =
            d * rightConjugateElem s k * d⁻¹ := by
              calc
                rightConjugateElem s (d * k * d⁻¹) = d * k⁻¹ * d⁻¹ * s * d * k * d⁻¹ := by
                  simp [rightConjugateElem, mul_assoc]
                _ = d * k⁻¹ * (d⁻¹ * s * d) * k * d⁻¹ := by simp [mul_assoc]
                _ = d * k⁻¹ * s * k * d⁻¹ := by rw [hd_conj_s]
                _ = d * rightConjugateElem s k * d⁻¹ := by simp [rightConjugateElem, mul_assoc]
        _ = rightConjugateElem s k := by
              calc
                d * rightConjugateElem s k * d⁻¹ =
                    rightConjugateElem s k * d * d⁻¹ := by rw [← hdsk]
                _ = rightConjugateElem s k := by group
    have hdk_eq : (⟨d * k * d⁻¹, hdk⟩ : {x : G // x ∈ peterfalviKSet D t}) = ⟨k, hkK⟩ :=
      hphi_inj hphi_eq
    have hdk_val : d * k * d⁻¹ = k := congrArg Subtype.val hdk_eq
    have hkd : k * d = d * k := by
      calc
        k * d = (d * k * d⁻¹) * d := by rw [hdk_val]
        _ = d * k := by group
    exact hkd

public theorem proposition_5_involution_mem_D_conjugacy_orbit
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s y : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)
    (hyH : y ∈ H) (hyI : IsInvolution y) :
    ∃ d : D, y = (d : G) * s * (d : G)⁻¹ := by
  classical
  letI : MulAction D G := {
    smul := fun d x => (d : G) * x * (d : G)⁻¹
    one_smul := by
      intro x
      change ((1 : D) : G) * x * (((1 : D) : G))⁻¹ = x
      simp
    mul_smul := by
      intro a b x
      change (((a * b : D) : G) * x * (((a * b : D) : G))⁻¹) =
        ((a : G) * (((b : G) * x * (b : G)⁻¹)) * (a : G)⁻¹)
      simp [mul_assoc]
  }
  let S : Set G := {x : G | x ∈ H ∧ IsInvolution x}
  have hV_eq := (proposition_5 H D Q t s hA1 hsH hsI hsStructure).1
  have hlemma :=
    lemma_a (M := G) t D hA1.involution_t hA1.D_odd
      (proposition_5_involution_t_mem_normalizer_D H D Q t hA1)
  have hD_card :
      Nat.card D =
        Nat.card (peterfalviV D t) *
          Nat.card {x : G // x ∈ peterfalviKSet D t} := by
    calc
      Nat.card D = Nat.card (peterfalviV D t) * (peterfalviKSet D t).ncard := by
        simpa [peterfalviV, peterfalviKSet] using hlemma.2.2
      _ = Nat.card (peterfalviV D t) *
          Nat.card {x : G // x ∈ peterfalviKSet D t} := by
        rw [Nat.card_coe_set_eq]
  have hK_card :
      Nat.card {x : G // x ∈ peterfalviKSet D t} = Nat.card S := by
    calc
      Nat.card {x : G // x ∈ peterfalviKSet D t} = (peterfalviKSet D t).ncard :=
        Nat.card_coe_set_eq _
      _ = Nat.card {x : G // x ∈ H ∧ IsInvolution x} :=
        (proposition_3 H D Q t hA1).1
      _ = Nat.card S := by rfl
  have hOrbit_subset : MulAction.orbit D s ⊆ S := by
    intro z hz
    rcases (MulAction.mem_orbit_iff.mp hz) with ⟨d, rfl⟩
    constructor
    · exact
        H.mul_mem
          (H.mul_mem (hA1.D_le_H d.property) hsH)
          (H.inv_mem (hA1.D_le_H d.property))
    · change IsInvolution ((d : G) * s * (d : G)⁻¹)
      simpa [rightConjugateElem] using
        (isInvolution_rightConjugateElem (x := s) (g := ((d : G)⁻¹)) hsI)
  have hstab_card :
      Nat.card (MulAction.stabilizer D s) = Nat.card (peterfalviV D t) := by
    let e : MulAction.stabilizer D s ≃ peterfalviV D t := {
      toFun d := by
        refine ⟨(d : D), ?_⟩
        rw [hV_eq]
        refine ⟨d.1.property, ?_⟩
        change (d : G) ∈ Subgroup.centralizer ({s} : Set G)
        rw [Subgroup.mem_centralizer_singleton_iff]
        have hd : (d : G) * s * (d : G)⁻¹ = s := d.property
        calc
          (d : G) * s = ((d : G) * s * (d : G)⁻¹) * (d : G) := by group
          _ = s * (d : G) := by rw [hd]
      invFun v := by
        have hv :
            (v : G) ∈ D ⊓ Subgroup.centralizer ({s} : Set G) := by
          simpa [hV_eq] using v.property
        refine ⟨⟨(v : G), hv.1⟩, ?_⟩
        have hcomm : (v : G) * s = s * (v : G) :=
          mul_comm_of_mem_centralizer_singleton hv.2
        change (v : G) * s * (v : G)⁻¹ = s
        calc
          (v : G) * s * (v : G)⁻¹ = (s * (v : G)) * (v : G)⁻¹ := by rw [hcomm]
          _ = s := by group
      left_inv d := by
        ext
        rfl
      right_inv v := by
        ext
        rfl
    }
    exact Nat.card_congr e
  letI := Fintype.ofFinite D
  letI := Fintype.ofFinite (MulAction.orbit D s)
  letI := Fintype.ofFinite (MulAction.stabilizer D s)
  have horbit_stabilizer :
      Nat.card (MulAction.orbit D s) * Nat.card (MulAction.stabilizer D s) =
        Nat.card D := by
    simpa [Nat.card_eq_fintype_card] using
      (MulAction.card_orbit_mul_card_stabilizer_eq_card_group D s)
  have hV_pos : 0 < Nat.card (peterfalviV D t) := Nat.card_pos
  have hOrbit_card :
      Nat.card (MulAction.orbit D s) = Nat.card S := by
    have hmul :
        Nat.card (MulAction.orbit D s) * Nat.card (peterfalviV D t) =
          Nat.card S * Nat.card (peterfalviV D t) := by
      calc
        Nat.card (MulAction.orbit D s) * Nat.card (peterfalviV D t) =
            Nat.card (MulAction.orbit D s) * Nat.card (MulAction.stabilizer D s) := by
              rw [hstab_card]
        _ = Nat.card D := horbit_stabilizer
        _ =
            Nat.card (peterfalviV D t) *
              Nat.card {x : G // x ∈ peterfalviKSet D t} := hD_card
        _ = Nat.card (peterfalviV D t) * Nat.card S := by rw [hK_card]
        _ = Nat.card S * Nat.card (peterfalviV D t) := by rw [Nat.mul_comm]
    exact Nat.mul_right_cancel hV_pos hmul
  have hSfinite : S.Finite := Set.toFinite S
  have hOrbit_eq_S : MulAction.orbit D s = S :=
    hSfinite.eq_of_subset_of_card_le hOrbit_subset (by rw [hOrbit_card])
  have hyOrbit : y ∈ MulAction.orbit D s := by
    rw [hOrbit_eq_S]
    exact ⟨hyH, hyI⟩
  rcases (MulAction.mem_orbit_iff.mp hyOrbit) with ⟨d, hd⟩
  exact ⟨d, hd.symm⟩

public theorem proposition_5_conjugate_into_V_of_centralized_involution
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q X : Subgroup G) (t s y : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)
    (hX_le_D : X ≤ D)
    (hyH : y ∈ H) (hyI : IsInvolution y)
    (hX_le_Cy : X ≤ Subgroup.centralizer ({y} : Set G)) :
    ∃ d : D, rightConjugate X (d : G) ≤ peterfalviV D t := by
  classical
  rcases
    proposition_5_involution_mem_D_conjugacy_orbit H D Q t s y hA1 hsH hsI hsStructure hyH hyI with
    ⟨d, hy_eq⟩
  have hV_eq := (proposition_5 H D Q t s hA1 hsH hsI hsStructure).1
  refine ⟨d, ?_⟩
  intro z hz
  rcases hz with ⟨x, hxX, rfl⟩
  have hxD : x ∈ D := hX_le_D hxX
  rw [hV_eq]
  refine ⟨?_, ?_⟩
  · have hdinv_inv : ((d : G)⁻¹)⁻¹ ∈ D := by simp
    exact D.mul_mem (D.mul_mem (D.inv_mem d.property) hxD) hdinv_inv
  · have hxCs : rightConjugateElem x (d : G) ∈ Subgroup.centralizer ({s} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hcomm_y : y * x = x * y :=
        (mul_comm_of_mem_centralizer_singleton (hX_le_Cy hxX)).symm
      rw [hy_eq] at hcomm_y
      calc
        rightConjugateElem x (d : G) * s =
            (d : G)⁻¹ * (x * ((d : G) * s * (d : G)⁻¹)) * (d : G) := by
              simp [rightConjugateElem, mul_assoc]
        _ = (d : G)⁻¹ * (((d : G) * s * (d : G)⁻¹) * x) * (d : G) := by
              rw [hcomm_y]
        _ = s * rightConjugateElem x (d : G) := by
              simp [rightConjugateElem, mul_assoc]
    simpa [rightConjugateElem, MulAut.conj_apply] using hxCs

private theorem proposition_5_fixed_point_triple
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q X : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)
    (hX_le_V : X ≤ peterfalviV D t) :
    ∃ base_point : Ω,
      H = MulAction.stabilizer G base_point ∧
        (∀ x : G, x ∈ X → x • base_point = base_point) ∧
          (∀ x : G, x ∈ X → x • (t⁻¹ • base_point) = t⁻¹ • base_point) ∧
            (∀ x : G, x ∈ X →
              x • ((t * s)⁻¹ • base_point) = (t * s)⁻¹ • base_point) ∧
              base_point ≠ t⁻¹ • base_point ∧
                base_point ≠ (t * s)⁻¹ • base_point ∧
                  t⁻¹ • base_point ≠ (t * s)⁻¹ • base_point := by
  classical
  obtain ⟨hV_eq, _hW_eq⟩ := proposition_5 H D Q t s hA1 hsH hsI hsStructure
  obtain ⟨base, hHbase⟩ := hA1.point_stabilizer
  have hfix_base : ∀ x : G, x ∈ X → x • base = base := by
    intro x hx
    have hxV : x ∈ peterfalviV D t := hX_le_V hx
    change x ∈ D ⊓ Subgroup.centralizer ({t} : Set G) at hxV
    have hxH : x ∈ H := hA1.D_le_H hxV.1
    have hxStab : x ∈ MulAction.stabilizer G base := by
      simpa [hHbase] using hxH
    simpa using hxStab
  have hfix_t : ∀ x : G, x ∈ X → x • (t⁻¹ • base) = t⁻¹ • base := by
    intro x hx
    have hxV : x ∈ peterfalviV D t := hX_le_V hx
    change x ∈ D ⊓ Subgroup.centralizer ({t} : Set G) at hxV
    have htx : x * t = t * x := mul_comm_of_mem_centralizer_singleton hxV.2
    have hx_t_inv : x * t⁻¹ = t⁻¹ * x := by
      calc
        x * t⁻¹ = t⁻¹ * (t * x) * t⁻¹ := by group
        _ = t⁻¹ * (x * t) * t⁻¹ := by rw [htx]
        _ = t⁻¹ * x := by group
    calc
      x • (t⁻¹ • base) = (x * t⁻¹) • base := by rw [mul_smul]
      _ = (t⁻¹ * x) • base := by rw [hx_t_inv]
      _ = t⁻¹ • (x • base) := by rw [mul_smul]
      _ = t⁻¹ • base := by rw [hfix_base x hx]
  have hfix_ts :
      ∀ x : G, x ∈ X → x • ((t * s)⁻¹ • base) = (t * s)⁻¹ • base := by
    intro x hx
    have hxV : x ∈ peterfalviV D t := hX_le_V hx
    have hxVs : x ∈ D ⊓ Subgroup.centralizer ({s} : Set G) := by
      rw [← hV_eq]
      exact hxV
    change x ∈ D ⊓ Subgroup.centralizer ({t} : Set G) at hxV
    have htx : x * t = t * x := mul_comm_of_mem_centralizer_singleton hxV.2
    have hsx : x * s = s * x := mul_comm_of_mem_centralizer_singleton hxVs.2
    have hx_t_inv : x * t⁻¹ = t⁻¹ * x := by
      calc
        x * t⁻¹ = t⁻¹ * (t * x) * t⁻¹ := by group
        _ = t⁻¹ * (x * t) * t⁻¹ := by rw [htx]
        _ = t⁻¹ * x := by group
    have hx_s_inv : x * s⁻¹ = s⁻¹ * x := by
      calc
        x * s⁻¹ = s⁻¹ * (s * x) * s⁻¹ := by group
        _ = s⁻¹ * (x * s) * s⁻¹ := by rw [hsx]
        _ = s⁻¹ * x := by group
    have hx_ts_inv : x * (t * s)⁻¹ = (t * s)⁻¹ * x := by
      calc
        x * (t * s)⁻¹ = x * (s⁻¹ * t⁻¹) := by rw [mul_inv_rev]
        _ = (x * s⁻¹) * t⁻¹ := by group
        _ = (s⁻¹ * x) * t⁻¹ := by rw [hx_s_inv]
        _ = s⁻¹ * (x * t⁻¹) := by group
        _ = s⁻¹ * (t⁻¹ * x) := by rw [hx_t_inv]
        _ = (t * s)⁻¹ * x := by rw [mul_inv_rev]; group
    calc
      x • ((t * s)⁻¹ • base) = (x * (t * s)⁻¹) • base := by rw [mul_smul]
      _ = ((t * s)⁻¹ * x) • base := by rw [hx_ts_inv]
      _ = (t * s)⁻¹ • (x • base) := by rw [mul_smul]
      _ = (t * s)⁻¹ • base := by rw [hfix_base x hx]
  have hbase_ne_t : base ≠ t⁻¹ • base := by
    intro h
    have ht_inv_H : t⁻¹ ∈ H := by
      have ht_inv_stab : t⁻¹ ∈ MulAction.stabilizer G base := by
        exact h.symm
      simpa [hHbase] using ht_inv_stab
    have htH : t ∈ H := by
      simpa using H.inv_mem ht_inv_H
    exact hA1.t_not_mem_H htH
  have hbase_ne_ts : base ≠ (t * s)⁻¹ • base := by
    intro h
    have hts_inv_H : (t * s)⁻¹ ∈ H := by
      have hts_inv_stab : (t * s)⁻¹ ∈ MulAction.stabilizer G base := by
        exact h.symm
      simpa [hHbase] using hts_inv_stab
    have htsH : t * s ∈ H := by
      simpa using H.inv_mem hts_inv_H
    have htH : t ∈ H := by
      have hts_sinv : (t * s) * s⁻¹ ∈ H :=
        H.mul_mem htsH (H.inv_mem hsH)
      simpa [mul_assoc] using hts_sinv
    exact hA1.t_not_mem_H htH
  have ht_ne_ts : t⁻¹ • base ≠ (t * s)⁻¹ • base := by
    intro h
    have hs_inv_fix_tbase : s⁻¹ • (t⁻¹ • base) = t⁻¹ • base := by
      simpa [mul_inv_rev, mul_smul] using h.symm
    have hconj_s_inv_H : t * s⁻¹ * t⁻¹ ∈ H := by
      have hstab : t * s⁻¹ * t⁻¹ ∈ MulAction.stabilizer G base := by
        change (t * s⁻¹ * t⁻¹) • base = base
        calc
          (t * s⁻¹ * t⁻¹) • base = t • (s⁻¹ • (t⁻¹ • base)) := by
            simp [mul_smul, mul_assoc]
          _ = t • (t⁻¹ • base) := by rw [hs_inv_fix_tbase]
          _ = base := by simp
      simpa [hHbase] using hstab
    have hs_inv_right : s⁻¹ ∈ rightConjugate H t := by
      refine ⟨t * s⁻¹ * t⁻¹, hconj_s_inv_H, ?_⟩
      simp [mul_assoc]
    have hs_right : s ∈ rightConjugate H t := by
      simpa using (rightConjugate H t).inv_mem hs_inv_right
    have hsD : s ∈ D := by
      rw [hA1.D_eq]
      exact ⟨hsH, hs_right⟩
    exact hsI.ne_one
      (eq_one_of_sq_eq_one_mem_odd_subgroup D hA1.D_odd hsD hsI.sq_eq_one)
  exact ⟨base, hHbase, hfix_base, hfix_t, hfix_ts,
    hbase_ne_t, hbase_ne_ts, ht_ne_ts⟩
/--
Peterfalvi-shaped fixed-point consequence used in Chapter I, Section 3,
Proposition 1(a): if `X ≤ V`, then the three points `H`, `H^t`, and `H^{ts}`
from the Peterfalvi proof give at least three fixed points of `X`.
-/
public theorem proposition_5_fixed_point_card_ge_three
    {G Ω : Type*} [Group G] [Finite G] [MulAction G Ω] [Finite Ω]
    (H D Q : Subgroup G) (t s : G)
    (hA1 : HypothesisA1 G Ω H D Q t)
    (hsH : s ∈ H) (hsI : IsInvolution s)
    (hsStructure : ∃ r : G, r ∈ Q ∧ t * s * t = r⁻¹ * t * r)
    (X : Subgroup G) (hX_ne : X ≠ ⊥) (hX_le_V : X ≤ peterfalviV D t) :
    3 ≤ Nat.card {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} := by
  classical
  have _ := hX_ne
  rcases proposition_5_fixed_point_triple H D Q X t s hA1 hsH hsI hsStructure hX_le_V with
    ⟨base, _hHbase, hfix_base, hfix_t, hfix_ts, hbase_ne_t, hbase_ne_ts, ht_ne_ts⟩
  let p0 : {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} :=
    ⟨base, hfix_base⟩
  let p1 : {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} :=
    ⟨t⁻¹ • base, hfix_t⟩
  let p2 : {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} :=
    ⟨(t * s)⁻¹ • base, hfix_ts⟩
  let f : Fin 3 → {ω : Ω // ω ∈ fixedPointsOfSubgroup G Ω X} := ![p0, p1, p2]
  have hf : Function.Injective f := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exfalso; exact hbase_ne_t (by simpa [f, p0, p1] using hij)
    · exfalso; exact hbase_ne_ts (by simpa [f, p0, p2, mul_inv_rev] using hij)
    · exfalso; exact hbase_ne_t (by simpa [f, p0, p1] using hij.symm)
    · rfl
    · exfalso; exact ht_ne_ts (by simpa [f, p1, p2, mul_inv_rev] using hij)
    · exfalso; exact hbase_ne_ts (by simpa [f, p0, p2, mul_inv_rev] using hij.symm)
    · exfalso; exact ht_ne_ts (by simpa [f, p1, p2, mul_inv_rev] using hij.symm)
    · rfl
  simpa using Nat.card_le_card_of_injective f hf

end PFchapter1section1
end CFSG.BenderSuzuki
