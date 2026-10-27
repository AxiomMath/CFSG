module

public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section9Corollary95
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.II1Section4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.StrongEmbeddingCounting
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Coprime
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.Basic
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition84Sylow
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection11.lemma_11_1_a
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.FinalTheorem
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConj

namespace CFSG
end CFSG
open CFSG

/-!
# Section 9, Corollary 9.6

This file begins the structural package of Corollary 9.6.  The earlier-volume
Peterfalvi Section 4 identities used below are imported from `II1Section4`.
-/

noncomputable section

namespace CFSG.BenderSuzuki

open PFAppendixIII PFchapter1section1
open scoped Pointwise commutatorElement

universe u

set_option maxHeartbeats 1000000

private theorem sylow_normalClosure_of_sylow_of_le
    {G : Type u} [Group G] [Finite G]
    {E D : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hED : E ≤ D) (hEN : (E.subgroupOf D).Normal)
    (P : Sylow p E) :
    let PD : Subgroup D := ((P : Subgroup E).map E.subtype).subgroupOf D
    let K : Subgroup D := Subgroup.normalClosure (PD : Set D)
    ∃ Q : Sylow p K,
      (Q : Subgroup K).map K.subtype = PD := by
  let ED : Subgroup D := E.subgroupOf D
  have hEDcard : Nat.card ED = Nat.card E := by
    simpa [ED] using natCard_subgroupOf_eq E D hED
  let PD : Subgroup D := ((P : Subgroup E).map E.subtype).subgroupOf D
  have hmapD : (P : Subgroup E).map E.subtype ≤ D :=
    (Subgroup.map_subtype_le (P : Subgroup E)).trans hED
  have hPDED : PD ≤ ED := by
    intro x hx
    change (x : G) ∈ E
    exact (Subgroup.map_subtype_le (P : Subgroup E)) hx
  have hPDcard : Nat.card PD =
      p ^ (Nat.card ED).factorization p := by
    calc
      Nat.card PD = Nat.card ((P : Subgroup E).map E.subtype) := by
        simpa [PD] using natCard_subgroupOf_eq
          ((P : Subgroup E).map E.subtype) D hmapD
      _ = Nat.card (P : Subgroup E) := by
        simpa using Subgroup.card_map_of_injective E.subtype_injective
      _ = p ^ (Nat.card E).factorization p := P.card_eq_multiplicity
      _ = p ^ (Nat.card ED).factorization p := by rw [hEDcard]
  let K : Subgroup D := Subgroup.normalClosure (PD : Set D)
  have hKleED : K ≤ ED := by
    dsimp [K]
    exact Subgroup.normalClosure_le_normal hPDED
  have hPDK : PD ≤ K := Subgroup.le_normalClosure
  let PK : Subgroup K := PD.subgroupOf K
  have hfacKleED : (Nat.card K).factorization p ≤
      (Nat.card ED).factorization p := by
    exact Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hKleED) Nat.card_pos.ne' Nat.card_pos.ne'
  have hfacPD : (Nat.card PD).factorization p =
      (Nat.card ED).factorization p := by
    rw [hPDcard, Nat.factorization_pow_self Fact.out]
  have hfacEDleK : (Nat.card ED).factorization p ≤
      (Nat.card K).factorization p := by
    rw [← hfacPD]
    exact Nat.factorization_le_factorization_of_dvd_right
      (Subgroup.card_dvd_of_le hPDK) Nat.card_pos.ne' Nat.card_pos.ne'
  have hfacK : (Nat.card K).factorization p =
      (Nat.card ED).factorization p :=
    le_antisymm hfacKleED hfacEDleK
  have hPKcard : Nat.card PK =
      p ^ (Nat.card K).factorization p := by
    calc
      Nat.card PK = Nat.card PD := by
        simpa [PK] using natCard_subgroupOf_eq PD K hPDK
      _ = p ^ (Nat.card ED).factorization p := hPDcard
      _ = p ^ (Nat.card K).factorization p := by rw [hfacK]
  let Q : Sylow p K := Sylow.ofCard PK hPKcard
  refine ⟨Q, ?_⟩
  change (PD.subgroupOf K).map K.subtype = PD
  exact Subgroup.map_subgroupOf_eq_of_le hPDK

private theorem normalClosure_mul_normalizer_eq_top_of_sylow
    {G : Type u} [Group G] [Finite G]
    {E D : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hED : E ≤ D) (hEN : (E.subgroupOf D).Normal)
    (P : Sylow p E) :
    let PD : Subgroup D := ((P : Subgroup E).map E.subtype).subgroupOf D
    let K : Subgroup D := Subgroup.normalClosure (PD : Set D)
    (K : Set D) * (Subgroup.normalizer (PD : Set D) : Set D) = Set.univ := by
  let PD : Subgroup D := ((P : Subgroup E).map E.subtype).subgroupOf D
  let K : Subgroup D := Subgroup.normalClosure (PD : Set D)
  obtain ⟨Q, hQ⟩ := sylow_normalClosure_of_sylow_of_le hED hEN P
  letI : K.Normal := Subgroup.normalClosure_normal
  have hfrattini : Subgroup.normalizer (PD : Set D) ⊔ K = ⊤ := by
    simpa [K, PD, hQ] using (Sylow.normalizer_sup_eq_top Q)
  change (K : Set D) * (Subgroup.normalizer (PD : Set D) : Set D) = Set.univ
  rw [← Subgroup.normal_mul K (Subgroup.normalizer (PD : Set D))]
  rw [sup_comm, hfrattini]
  rfl

private theorem normalizer_sylow_centralizes_involution
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X} {p : ℕ} [Fact p.Prime]
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hED : E ≤ D)
    (hpAb : p ∣ Nat.card (E ⧸ derivedSubgroup E))
    (P : Sylow p E)
    (hPV : (P : Subgroup E).map E.subtype ≤ peterfalviV D t)
    (hPcentral : PeterfalviCentralizersTrivial D t
      ((P : Subgroup E).map E.subtype)) :
    let PD : Subgroup D := ((P : Subgroup E).map E.subtype).subgroupOf D
    ∀ n : D, n ∈ Subgroup.normalizer (PD : Set D) →
      Commute (n : X) t := by
  let Pamb : Subgroup X := (P : Subgroup E).map E.subtype
  let PD : Subgroup D := Pamb.subgroupOf D
  have hpE : p ∣ Nat.card E :=
    hpAb.trans (Subgroup.card_quotient_dvd_card (s := derivedSubgroup E))
  have hpP : p ∣ Nat.card (P : Subgroup E) :=
    P.dvd_card_of_dvd_card hpE
  obtain ⟨g, hgorder⟩ :=
    exists_prime_orderOf_dvd_card' (G := (P : Subgroup E)) p hpP
  let gX : X := ((g : P) : E)
  have hgPamb : gX ∈ Pamb := by
    exact Subgroup.mem_map_of_mem E.subtype g.property
  have hgD : gX ∈ D := hED (Subgroup.map_subtype_le (P : Subgroup E) hgPamb)
  let gD : D := ⟨gX, hgD⟩
  have hgPD : gD ∈ PD := hgPamb
  have hgXne : gX ≠ 1 := by
    intro hg
    have hgPone : g = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact hg
    have : orderOf g = 1 := by rw [hgPone, orderOf_one]
    exact (Fact.out : Nat.Prime p).ne_one (hgorder.symm.trans this)
  have hgt : Commute gX t := by
    have hgV := hPV hgPamb
    exact Subgroup.mem_centralizer_singleton_iff.mp hgV.2
  change ∀ n : D, n ∈ Subgroup.normalizer (PD : Set D) →
    Commute (n : X) t
  intro n hn
  let qD : D := n⁻¹ * gD * n
  have hqPD : qD ∈ PD := by
    have hninv : n⁻¹ ∈ Subgroup.normalizer (PD : Set D) :=
      (Subgroup.normalizer (PD : Set D)).inv_mem hn
    have := (Subgroup.mem_normalizer_iff.mp hninv gD).mp hgPD
    simpa [qD, mul_assoc] using this
  have hqPamb : (qD : X) ∈ Pamb := hqPD
  have hqt : Commute (qD : X) t := by
    have hqV := hPV hqPamb
    exact Subgroup.mem_centralizer_singleton_iff.mp hqV.2
  let c : X := ⁅(n : X), t⁆
  have hcD : c ∈ D := by
    have hconj : t * (n : X)⁻¹ * t⁻¹ ∈ D :=
      (Subgroup.mem_normalizer_iff.mp hDnorm (n : X)⁻¹).mp
        (D.inv_mem n.property)
    simpa [c, commutatorElement_def, mul_assoc] using
      D.mul_mem n.property hconj
  have hcI : c ∈ peterfalviKSet D t := by
    refine ⟨hcD, ?_⟩
    change t⁻¹ * c * t = c⁻¹
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    simp [c, commutatorElement_def, ht.inv_eq_self, htt, mul_assoc]
  have htginv : t⁻¹ * gX * t = gX := by
    calc
      t⁻¹ * gX * t = t⁻¹ * (gX * t) := by rw [mul_assoc]
      _ = t⁻¹ * (t * gX) := by rw [hgt.eq]
      _ = gX := by simp
  have htq : t * (qD : X) * t⁻¹ = qD := by
    calc
      t * (qD : X) * t⁻¹ = ((qD : X) * t) * t⁻¹ := by
        rw [hqt.symm.eq]
      _ = qD := by simp [mul_assoc]
  have hccomm : c * gX = gX * c := by
    apply (commutatorElement_eq_one_iff_mul_comm.mp ?_)
    change ⁅c, gX⁆ = 1
    rw [commutatorElement_def]
    have hcfix : c * gX * c⁻¹ = gX := by
      calc
        c * gX * c⁻¹ =
            (n : X) * t * (n : X)⁻¹ *
              (t⁻¹ * gX * t) * (n : X) * t⁻¹ * (n : X)⁻¹ := by
          simp [c, commutatorElement_def, mul_assoc]
        _ = (n : X) * t * (n : X)⁻¹ * gX *
              (n : X) * t⁻¹ * (n : X)⁻¹ := by rw [htginv]
        _ = (n : X) * t * (qD : X) * t⁻¹ * (n : X)⁻¹ := by
          simp [qD, gD, gX, mul_assoc]
        _ = (n : X) * (t * (qD : X) * t⁻¹) * (n : X)⁻¹ := by
          group
        _ = (n : X) * (qD : X) * (n : X)⁻¹ := by rw [htq]
        _ = gX := by simp [qD, gD, gX, mul_assoc]
    simp [hcfix]
  have hcone : c = 1 :=
    hPcentral gX hgPamb hgXne c hcI hccomm
  exact commutatorElement_eq_one_iff_commute.mp hcone

private theorem normalClosure_sylow_mem_normalizer
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X} {p : ℕ} [Fact p.Prime]
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (P : Sylow p E)
    (hPV : (P : Subgroup E).map E.subtype ≤ peterfalviV D t) :
    let PD : Subgroup D := ((P : Subgroup E).map E.subtype).subgroupOf D
    let K : Subgroup D := Subgroup.normalClosure (PD : Set D)
    t ∈ Subgroup.normalizer ((K.map D.subtype : Subgroup X) : Set X) := by
  let Pamb : Subgroup X := (P : Subgroup E).map E.subtype
  let PD : Subgroup D := Pamb.subgroupOf D
  let K : Subgroup D := Subgroup.normalClosure (PD : Set D)
  let tn : Subgroup.normalizer (D : Set X) := ⟨t, hDnorm⟩
  let phi : D ≃* D := D.normalizerMonoidHom tn
  have hphi_apply (d : D) : (phi d : X) = t * (d : X) * t⁻¹ := by
    simp [phi, tn, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hphi_fix (d : D) (hd : d ∈ PD) : phi d = d := by
    apply Subtype.ext
    have hdP : (d : X) ∈ Pamb := hd
    have hdt : Commute (d : X) t :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPV hdP).2
    calc
      (phi d : X) = t * (d : X) * t⁻¹ := hphi_apply d
      _ = ((d : X) * t) * t⁻¹ := by rw [hdt.symm.eq]
      _ = d := by simp [mul_assoc]
  have himage : phi '' (PD : Set D) = (PD : Set D) := by
    ext d
    constructor
    · rintro ⟨e, he, rfl⟩
      simpa [hphi_fix e he] using he
    · intro hd
      exact ⟨d, hd, hphi_fix d hd⟩
  have hKmap : K.map phi.toMonoidHom = K := by
    calc
      K.map phi.toMonoidHom =
          Subgroup.normalClosure (phi '' (PD : Set D)) := by
        simpa [K] using
          Subgroup.map_normalClosure (PD : Set D) phi.toMonoidHom phi.surjective
      _ = Subgroup.normalClosure (PD : Set D) := by rw [himage]
      _ = K := rfl
  have hforward {x : X}
      (hx : x ∈ (K.map D.subtype : Subgroup X)) :
      t * x * t⁻¹ ∈ (K.map D.subtype : Subgroup X) := by
    rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
    have hphik : phi k ∈ K := by
      rw [← hKmap]
      exact Subgroup.mem_map_of_mem phi.toMonoidHom hk
    refine ⟨phi k, hphik, ?_⟩
    exact hphi_apply k
  change t ∈ Subgroup.normalizer ((K.map D.subtype : Subgroup X) : Set X)
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward
  · intro hx
    have hback := hforward hx
    rcases Subgroup.mem_map.mp hback with ⟨k, hk, hkval⟩
    refine Subgroup.mem_map.mpr ⟨k, hk, ?_⟩
    have htt : t * t = 1 := by
      simpa [pow_two] using ht.sq_eq_one
    calc
      (D.subtype k : X) = t * (t * x * t⁻¹) * t⁻¹ := hkval
      _ = x := by
        rw [ht.inv_eq_self]
        calc
          t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [htt]; simp

private theorem commutator_zpowers_le_normalClosure_sylow
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X} {p : ℕ} [Fact p.Prime]
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hED : E ≤ D) (hEN : (E.subgroupOf D).Normal)
    (hpAb : p ∣ Nat.card (E ⧸ derivedSubgroup E))
    (P : Sylow p E)
    (hPV : (P : Subgroup E).map E.subtype ≤ peterfalviV D t)
    (hPcentral : PeterfalviCentralizersTrivial D t
      ((P : Subgroup E).map E.subtype)) :
    let PD : Subgroup D := ((P : Subgroup E).map E.subtype).subgroupOf D
    let K : Subgroup D := Subgroup.normalClosure (PD : Set D)
    ⁅D, Subgroup.zpowers t⁆ ≤ (K.map D.subtype : Subgroup X) := by
  let A : Subgroup X := Subgroup.zpowers t
  let Pamb : Subgroup X := (P : Subgroup E).map E.subtype
  let PD : Subgroup D := Pamb.subgroupOf D
  let K : Subgroup D := Subgroup.normalClosure (PD : Set D)
  let Kamb : Subgroup X := K.map D.subtype
  have hfactor :
      (K : Set D) * (Subgroup.normalizer (PD : Set D) : Set D) = Set.univ :=
    normalClosure_mul_normalizer_eq_top_of_sylow hED hEN P
  have hNcentral : ∀ n : D,
      n ∈ Subgroup.normalizer (PD : Set D) → Commute (n : X) t := by
    simpa [PD, Pamb] using normalizer_sylow_centralizes_involution
      ht hDnorm hED hpAb P hPV hPcentral
  have htK : t ∈ Subgroup.normalizer (Kamb : Set X) := by
    simpa [Kamb, K, PD, Pamb] using
      normalClosure_sylow_mem_normalizer ht hDnorm P hPV
  have horder : orderOf t = 2 :=
    (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
  have hAcard : Nat.card A = 2 := by
    simp [A, Nat.card_zpowers, horder]
  let az : A := ⟨t, Subgroup.mem_zpowers t⟩
  have hazne : az ≠ 1 := by
    intro h
    exact ht.ne_one (congrArg Subtype.val h)
  have haCases (a : A) : a = 1 ∨ a = az := by
    by_cases ha : a = 1
    · exact Or.inl ha
    · right
      obtain ⟨other, hother, huniq⟩ :=
        (Nat.card_eq_two_iff' (1 : A)).mp hAcard
      exact (huniq a ha).trans (huniq az hazne).symm
  rw [Subgroup.commutator_le]
  intro d hd a ha
  let aA : A := ⟨a, ha⟩
  rcases haCases aA with haone | hat
  · have ha' : a = 1 := congrArg Subtype.val haone
    subst a
    simp
  · have ha' : a = t := congrArg Subtype.val hat
    subst a
    let dD : D := ⟨d, hd⟩
    have hdprod : dD ∈
        (K : Set D) * (Subgroup.normalizer (PD : Set D) : Set D) := by
      rw [hfactor]
      exact Set.mem_univ dD
    rw [Set.mem_mul] at hdprod
    rcases hdprod with ⟨k, hk, n, hn, hkn⟩
    have hdval : (k : X) * (n : X) = d := by
      simpa [dD] using congrArg Subtype.val hkn
    have hnt : Commute (n : X) t := hNcentral n hn
    have hkamb : (k : X) ∈ Kamb :=
      Subgroup.mem_map_of_mem D.subtype hk
    have hconjK : t * (k : X)⁻¹ * t⁻¹ ∈ Kamb :=
      (Subgroup.mem_normalizer_iff.mp htK (k : X)⁻¹).mp
        (Kamb.inv_mem hkamb)
    have hcommEq : ⁅d, t⁆ = (k : X) * (t * (k : X)⁻¹ * t⁻¹) := by
      rw [commutatorElement_def, ← hdval]
      calc
        ((k : X) * (n : X)) * t * ((k : X) * (n : X))⁻¹ * t⁻¹ =
            (k : X) * ((n : X) * t) * (n : X)⁻¹ * (k : X)⁻¹ * t⁻¹ := by
          group
        _ = (k : X) * (t * (n : X)) * (n : X)⁻¹ *
              (k : X)⁻¹ * t⁻¹ := by rw [hnt.eq]
        _ = (k : X) * (t * (k : X)⁻¹ * t⁻¹) := by group
    rw [hcommEq]
    exact Kamb.mul_mem hkamb hconjK

public theorem closure_peterfalviKSet_le_derived_of_alternativeB
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X} {p : ℕ} [Fact p.Prime]
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hDodd : Odd (Nat.card D))
    (hED : E ≤ D) (hEN : (E.subgroupOf D).Normal)
    (hpAb : p ∣ Nat.card (E ⧸ derivedSubgroup E))
    (hB : Lemma94AlternativeB D E t p) :
    Subgroup.closure (peterfalviKSet D t) ≤
      (derivedSubgroup E).map E.subtype := by
  rcases hB with ⟨P, hPcyclic, hPV, hPcentral⟩
  let A : Subgroup X := Subgroup.zpowers t
  let Pamb : Subgroup X := (P : Subgroup E).map E.subtype
  let PD : Subgroup D := Pamb.subgroupOf D
  let K : Subgroup D := Subgroup.normalClosure (PD : Set D)
  let Kamb : Subgroup X := K.map D.subtype
  have hKleE : Kamb ≤ E := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
    have hPDleE : PD ≤ E.subgroupOf D := by
      intro y hy
      change (y : X) ∈ E
      exact (Subgroup.map_subtype_le (P : Subgroup E)) hy
    have hKle : K ≤ E.subgroupOf D := by
      exact Subgroup.normalClosure_le_normal hPDleE
    exact hKle hk
  have hcommK : ⁅D, A⁆ ≤ Kamb := by
    simpa [A, Kamb, K, PD, Pamb] using
      commutator_zpowers_le_normalClosure_sylow ht hDnorm hED hEN hpAb P
        hPV hPcentral
  have hcommD_t {x : X} (hx : x ∈ D) : ⁅x, t⁆ ∈ Kamb := by
    exact hcommK (Subgroup.commutator_mem_commutator hx
      (Subgroup.mem_zpowers t))
  have htE : t ∈ Subgroup.normalizer (E : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hcx : ⁅x⁻¹, t⁆ ∈ Kamb := hcommD_t (D.inv_mem (hED hx))
      have hcxE : ⁅x⁻¹, t⁆ ∈ E := hKleE hcx
      have hxeq : x * ⁅x⁻¹, t⁆ = t * x * t⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      rw [← hxeq]
      exact E.mul_mem hx hcxE
    · intro hx
      have hforward := (show ∀ y : X, y ∈ E →
          t * y * t⁻¹ ∈ E from by
        intro y hy
        have hcy : ⁅y⁻¹, t⁆ ∈ Kamb := hcommD_t (D.inv_mem (hED hy))
        have hcyE : ⁅y⁻¹, t⁆ ∈ E := hKleE hcy
        have hyeq : y * ⁅y⁻¹, t⁆ = t * y * t⁻¹ := by
          simp [commutatorElement_def, mul_assoc]
        rw [← hyeq]
        exact E.mul_mem hy hcyE) (t * x * t⁻¹) hx
      have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
      have heq : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [ht.inv_eq_self]
        calc
          t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [htt]; simp
      rw [heq] at hforward
      exact hforward
  let Eder : Subgroup E := derivedSubgroup E
  let EderAmb : Subgroup X := Eder.map E.subtype
  have htEder : t ∈ Subgroup.normalizer (EderAmb : Set X) := by
    simpa [Eder, EderAmb] using
      External.hkt_normalizer_le_normalizer_map_subtype_of_characteristic
        E (derivedSubgroup E) htE
  let q : E →* E ⧸ Eder := QuotientGroup.mk' Eder
  letI : IsMulCommutative (E ⧸ Eder) := by
    exact (Subgroup.Normal.quotient_commutative_iff_commutator_le).2 (by rfl)
  let Pbar : Sylow p (E ⧸ Eder) :=
    P.mapSurjective (f := q) (QuotientGroup.mk'_surjective Eder)
  have hPbarNormal : (Pbar : Subgroup (E ⧸ Eder)).Normal := by
    infer_instance
  letI : (Pbar : Subgroup (E ⧸ Eder)).Characteristic :=
    Sylow.characteristic_of_normal Pbar hPbarNormal
  let Hsub : Subgroup E := (Pbar : Subgroup (E ⧸ Eder)).comap q
  have hHchar : Hsub.Characteristic := by
    letI : Eder.Characteristic := by
      simpa [Eder] using
        (inferInstance : (derivedSubgroup E).Characteristic)
    exact Subgroup.Characteristic.comap_quotient_mk
      (inferInstance : (Pbar : Subgroup (E ⧸ Eder)).Characteristic)
  let Hamb : Subgroup X := Hsub.map E.subtype
  have hHambLeD : Hamb ≤ D :=
    (Subgroup.map_subtype_le Hsub).trans hED
  have hHambD : (Hamb.subgroupOf D).Normal := by
    exact normal_subgroupOf_map_of_characteristic_of_normal
      E Hamb D hED hEN Hsub hHchar rfl hHambLeD
  letI : (Hamb.subgroupOf D).Normal := hHambD
  have hPambH : Pamb ≤ Hamb := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨pE, hpE, rfl⟩
    refine Subgroup.mem_map.mpr ⟨pE, ?_, rfl⟩
    change q pE ∈ (Pbar : Subgroup (E ⧸ Eder))
    exact Subgroup.mem_map_of_mem q hpE
  have hPDH : PD ≤ Hamb.subgroupOf D := by
    intro x hx
    exact hPambH hx
  have hKH : Kamb ≤ Hamb := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨k, hk, rfl⟩
    exact Subgroup.normalClosure_le_normal hPDH hk
  have hEderNormalE : (EderAmb.subgroupOf E).Normal := by
    have heq : EderAmb.subgroupOf E = Eder := by
      ext x
      constructor
      · intro hx
        rcases Subgroup.mem_map.mp hx with ⟨y, hy, hyx⟩
        have hyx' : y = x := E.subtype_injective hyx
        simpa [← hyx'] using hy
      · intro hx
        exact Subgroup.mem_map_of_mem E.subtype hx
    rw [heq]
    exact inferInstance
  have hHambcomm : ∀ h : X, h ∈ Hamb → ⁅h, t⁆ ∈ EderAmb := by
    intro h hh
    rcases Subgroup.mem_map.mp hh with ⟨hE, hhE, rfl⟩
    have hqH : q hE ∈ (Pbar : Subgroup (E ⧸ Eder)) := hhE
    rcases Subgroup.mem_map.mp hqH with ⟨pE, hpE, hpEq⟩
    have heE : pE⁻¹ * hE ∈ Eder :=
      QuotientGroup.eq.mp hpEq
    let pX : X := (pE : X)
    let eX : X := ((pE⁻¹ * hE : E) : X)
    have hpX : pX ∈ Pamb := Subgroup.mem_map_of_mem E.subtype hpE
    have hpt : Commute pX t :=
      Subgroup.mem_centralizer_singleton_iff.mp (hPV hpX).2
    have heX : eX ∈ EderAmb :=
      Subgroup.mem_map_of_mem E.subtype heE
    have heconj : t * eX⁻¹ * t⁻¹ ∈ EderAmb :=
      (Subgroup.mem_normalizer_iff.mp htEder eX⁻¹).mp
        (EderAmb.inv_mem heX)
    have hcommE : ⁅eX, t⁆ ∈ EderAmb := by
      simpa [commutatorElement_def, mul_assoc] using
        EderAmb.mul_mem heX heconj
    have hheq : (hE : X) = pX * eX := by
      simp [pX, eX]
    have hpconj : pX * ⁅eX, t⁆ * pX⁻¹ ∈ EderAmb := by
      exact (Subgroup.normal_subgroupOf_iff
        (Subgroup.map_subtype_le Eder)).mp hEderNormalE
          ⁅eX, t⁆ pX hcommE pE.property
    have hcommEq : ⁅(hE : X), t⁆ = pX * ⁅eX, t⁆ * pX⁻¹ := by
      rw [commutatorElement_def, hheq, commutatorElement_def]
      calc
        pX * eX * t * (pX * eX)⁻¹ * t⁻¹ =
            pX * eX * t * eX⁻¹ * pX⁻¹ * t⁻¹ := by group
        _ = pX * eX * t * eX⁻¹ * (pX⁻¹ * t⁻¹) := by group
        _ = pX * eX * t * eX⁻¹ * (t⁻¹ * pX⁻¹) := by
          rw [hpt.inv_inv.eq]
        _ = pX * eX * t * eX⁻¹ * t⁻¹ * pX⁻¹ := by group
        _ = pX * (eX * t * eX⁻¹ * t⁻¹) * pX⁻¹ := by group
    change ⁅(hE : X), t⁆ ∈ EderAmb
    rw [hcommEq]
    exact hpconj
  have hNcentral : ∀ n : D,
      n ∈ Subgroup.normalizer (PD : Set D) → Commute (n : X) t := by
    simpa [PD, Pamb] using normalizer_sylow_centralizes_involution
      ht hDnorm hED hpAb P hPV hPcentral
  have hcommDer : ⁅D, A⁆ ≤ EderAmb := by
    rw [Subgroup.commutator_le]
    intro d hd a ha
    let aA : A := ⟨a, ha⟩
    have horderA : Nat.card A = 2 := by
      have horder : orderOf t = 2 :=
        (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
      simp [A, Nat.card_zpowers, horder]
    let az : A := ⟨t, Subgroup.mem_zpowers t⟩
    have hazne : az ≠ 1 := by
      intro h
      exact ht.ne_one (congrArg Subtype.val h)
    have haCases (b : A) : b = 1 ∨ b = az := by
      by_cases hb : b = 1
      · exact Or.inl hb
      · right
        obtain ⟨other, hother, huniq⟩ :=
          (Nat.card_eq_two_iff' (1 : A)).mp horderA
        exact (huniq b hb).trans (huniq az hazne).symm
    rcases haCases aA with haone | hat
    · have ha' : a = 1 := congrArg Subtype.val haone
      subst a
      simp
    · have ha' : a = t := congrArg Subtype.val hat
      subst a
      let dD : D := ⟨d, hd⟩
      have hdprod : dD ∈
          (K : Set D) * (Subgroup.normalizer (PD : Set D) : Set D) := by
        rw [normalClosure_mul_normalizer_eq_top_of_sylow hED hEN P]
        exact Set.mem_univ dD
      rw [Set.mem_mul] at hdprod
      rcases hdprod with ⟨k, hk, n, hn, hkn⟩
      have hdval : (k : X) * (n : X) = d := by
        simpa [dD] using congrArg Subtype.val hkn
      have hnt : Commute (n : X) t :=
        hNcentral n hn
      have hkH : (k : X) ∈ Hamb := hKH
        (Subgroup.mem_map_of_mem D.subtype hk)
      have hcommEq : ⁅d, t⁆ = ⁅(k : X), t⁆ := by
        rw [commutatorElement_def, ← hdval]
        rw [commutatorElement_def]
        calc
          (k : X) * (n : X) * t * ((k : X) * (n : X))⁻¹ * t⁻¹ =
              (k : X) * ((n : X) * t) * (n : X)⁻¹ *
                (k : X)⁻¹ * t⁻¹ := by group
          _ = (k : X) * (t * (n : X)) * (n : X)⁻¹ *
                (k : X)⁻¹ * t⁻¹ := by rw [hnt.eq]
          _ = (k : X) * t * (k : X)⁻¹ * t⁻¹ := by group
      rw [hcommEq]
      exact hHambcomm (k : X) hkH
  have hclosureEq :=
    closure_peterfalviKSet_eq_commutator_zpowers ht hDnorm hDodd
  change Subgroup.closure (peterfalviKSet D t) ≤ EderAmb
  rw [hclosureEq]
  simpa [A] using hcommDer

public theorem commutator_eq_of_le_of_solvable_coprime
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hED : E ≤ D)
    (hEt : t ∈ Subgroup.normalizer (E : Set X))
    (hDodd : Odd (Nat.card D))
    (hcomm_le : ⁅D, Subgroup.zpowers t⁆ ≤ E) :
    ⁅D, Subgroup.zpowers t⁆ = ⁅E, Subgroup.zpowers t⁆ := by
  let A : Subgroup X := Subgroup.zpowers t
  have hA_norm_D : A ≤ Subgroup.normalizer (D : Set X) := by
    rw [Subgroup.zpowers_le]
    exact hDnorm
  have hA_norm_E : A ≤ Subgroup.normalizer (E : Set X) := by
    rw [Subgroup.zpowers_le]
    exact hEt
  letI : Subgroup.Normalizes A D := ⟨hA_norm_D⟩
  letI : Subgroup.Normalizes A E := ⟨hA_norm_E⟩
  have horder : orderOf t = 2 :=
    (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
  have hAcard : Nat.card A = 2 := by
    simp [A, Nat.card_zpowers, horder]
  have hDcop : Nat.Coprime (Nat.card A) (Nat.card D) := by
    rw [hAcard]
    exact hDodd.coprime_two_left
  have hDsolv : IsSolvable D := odd_order_theorem D hDodd
  have hCE_le_CD : ⁅E, A⁆ ≤ ⁅D, A⁆ :=
    Subgroup.commutator_mono hED le_rfl
  let Csub : Subgroup D := commutatorAction (A := A) (G := D)
  have hCmap : Csub.map D.subtype = ⁅D, A⁆ :=
    commutatorAction_subgroup_conj_map_eq_commutator D A hA_norm_D
  have hC2_le_CE :
      (commutatorAction₂ (A := A) (G := D)).map D.subtype ≤ ⁅E, A⁆ := by
    let S : Set D :=
      {x : D | ∃ a : A, ∃ h : D, h ∈ Csub ∧ x = h⁻¹ * (a • h)}
    calc
      (commutatorAction₂ (A := A) (G := D)).map D.subtype =
          (Subgroup.closure S).map D.subtype := by rfl
      _ = Subgroup.closure (D.subtype '' S) := by
        simpa using (MonoidHom.map_closure (f := D.subtype) S)
      _ ≤ ⁅E, A⁆ := by
        refine (Subgroup.closure_le (K := ⁅E, A⁆)).2 ?_
        rintro _ ⟨y, hy, rfl⟩
        rcases hy with ⟨a, h, hhC, rfl⟩
        have hhD : (h : X) ∈ ⁅D, A⁆ := by
          rw [← hCmap]
          exact Subgroup.mem_map_of_mem D.subtype hhC
        have hhE : (h : X) ∈ E := hcomm_le hhD
        have hmem : ⁅(h : X)⁻¹, (a : X)⁆ ∈ ⁅E, A⁆ :=
          Subgroup.commutator_mem_commutator
            (E.inv_mem hhE) a.property
        simpa [commutatorElement_def,
          Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
          hA_norm_D, mul_assoc] using hmem
  have hDcommEq :
      commutatorAction₂ (A := A) (G := D) =
        commutatorAction (A := A) (G := D) :=
    commutatorAction₂_eq_commutatorAction_of_solvable_coprime
      hDsolv hDcop
  apply le_antisymm
  · intro x hx
    have hxC : x ∈ Csub.map D.subtype := by
      rw [hCmap]
      exact hx
    have hxC2 : x ∈
        (commutatorAction₂ (A := A) (G := D)).map D.subtype := by
      rw [hDcommEq, hCmap]
      exact hx
    exact hC2_le_CE hxC2
  · exact hCE_le_CD

public theorem E_eq_closure_sup_fixed
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (ht : IsInvolution t)
    (hDnorm : t ∈ Subgroup.normalizer (D : Set X))
    (hED : E ≤ D)
    (hEt : t ∈ Subgroup.normalizer (E : Set X))
    (hDodd : Odd (Nat.card D))
    (hcomm_le : ⁅D, Subgroup.zpowers t⁆ ≤ E)
    (hclosure : Subgroup.closure (peterfalviKSet D t) =
      ⁅D, Subgroup.zpowers t⁆) :
    (E : Set X) =
        (Subgroup.closure (peterfalviKSet D t) : Set X) *
          ((E ⊓ peterfalviV D t : Subgroup X) : Set X) ∧
      E = Subgroup.closure (peterfalviKSet D t) ⊔
        (E ⊓ peterfalviV D t) := by
  let A : Subgroup X := Subgroup.zpowers t
  have hA_norm_E : A ≤ Subgroup.normalizer (E : Set X) := by
    rw [Subgroup.zpowers_le]
    exact hEt
  have horder : orderOf t = 2 :=
    (orderOf_eq_prime_iff).2 ⟨ht.sq_eq_one, ht.ne_one⟩
  have hAcard : Nat.card A = 2 := by
    simp [A, Nat.card_zpowers, horder]
  have hEodd : Odd (Nat.card E) := by
    apply Odd.of_dvd_nat hDodd
    exact Subgroup.card_dvd_of_le hED
  have hdecomp := odd_subgroup_eq_commutator_mul_centralizer E A
    hA_norm_E hAcard hEodd
  have hcommEq : ⁅D, A⁆ = ⁅E, A⁆ :=
    commutator_eq_of_le_of_solvable_coprime ht hDnorm hED hEt hDodd hcomm_le
  have hfixEq :
      E ⊓ Subgroup.centralizer (A : Set X) = E ⊓ peterfalviV D t := by
    ext x
    constructor
    · intro hx
      refine ⟨hx.1, hED hx.1, ?_⟩
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      exact (Subgroup.mem_centralizer_iff.mp hx.2
        t (Subgroup.mem_zpowers t)).symm
    · intro hx
      refine ⟨hx.1, ?_⟩
      change x ∈ Subgroup.centralizer (A : Set X)
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      rcases Subgroup.mem_zpowers_iff.mp ha with ⟨n, rfl⟩
      have hxV : x ∈ D ∧ x ∈ Subgroup.centralizer ({t} : Set X) := by
        simpa [peterfalviV] using hx.2
      have hxt : Commute x t :=
        Subgroup.mem_centralizer_singleton_iff.mp hxV.2
      exact (hxt.zpow_right n).eq.symm
  have hset :
      (E : Set X) =
        (Subgroup.closure (peterfalviKSet D t) : Set X) *
          ((E ⊓ peterfalviV D t : Subgroup X) : Set X) := by
    calc
      (E : Set X) = (⁅E, A⁆ : Subgroup X) *
          ((E ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := hdecomp
      _ = (⁅D, A⁆ : Subgroup X) *
          ((E ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
            rw [hcommEq]
      _ = (Subgroup.closure (peterfalviKSet D t) : Set X) *
          ((E ⊓ Subgroup.centralizer (A : Set X) : Subgroup X) : Set X) := by
            rw [hclosure]
      _ = (Subgroup.closure (peterfalviKSet D t) : Set X) *
          ((E ⊓ peterfalviV D t : Subgroup X) : Set X) := by
            rw [hfixEq]
  refine ⟨hset, ?_⟩
  apply le_antisymm
  · intro x hx
    have hxSet : x ∈ (E : Set X) := hx
    rw [hset] at hxSet
    have hx' : x ∈
        (Subgroup.closure (peterfalviKSet D t) : Set X) *
          ((E ⊓ peterfalviV D t : Subgroup X) : Set X) := hxSet
    rcases Set.mem_mul.mp hx' with ⟨k, hk, v, hv, rfl⟩
    exact (Subgroup.closure (peterfalviKSet D t) ⊔
        (E ⊓ peterfalviV D t)).mul_mem
          ((show Subgroup.closure (peterfalviKSet D t) ≤
            Subgroup.closure (peterfalviKSet D t) ⊔
              (E ⊓ peterfalviV D t) from le_sup_left) hk)
          ((show E ⊓ peterfalviV D t ≤
            Subgroup.closure (peterfalviKSet D t) ⊔
              (E ⊓ peterfalviV D t) from le_sup_right) hv)
  · exact sup_le
      ((Subgroup.closure_le (K := E)).2 (fun x hx => hcomm_le
        (by rw [← hclosure]; exact Subgroup.subset_closure hx)))
      inf_le_left

/-!
  Scratch audit for Corollary 9.6(d).  The intended interface is deliberately
  pointwise: a callback supplies the exact Corollary 9.5 alternative for each
  prime in `E / E'`; the conclusion is the source fixed-point-free clause.
-/

public theorem natCard_abelianization_subgroupOf_eq
    {X : Type u} [Group X] [Finite X]
    {H K : Subgroup X} (h : H ≤ K) :
    Nat.card (H.subgroupOf K ⧸ derivedSubgroup (H.subgroupOf K)) =
      Nat.card (H ⧸ derivedSubgroup H) := by
  let A : Subgroup K := H.subgroupOf K
  let e : A ≃* H := Subgroup.subgroupOfEquivOfLe h
  have hmap : (derivedSubgroup A).map e.toMonoidHom = derivedSubgroup H := by
    change (commutator A).map e.toMonoidHom = commutator H
    rw [commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.surjective]
    rfl
  have hAcard : Nat.card A = Nat.card H := Nat.card_congr e.toEquiv
  have hDcard : Nat.card (derivedSubgroup A) =
      Nat.card (derivedSubgroup H) := by
    let ed := Subgroup.equivMapOfInjective (derivedSubgroup A)
      e.toMonoidHom e.injective
    calc
      Nat.card (derivedSubgroup A) =
          Nat.card ((derivedSubgroup A).map e.toMonoidHom) :=
        Nat.card_congr ed.toEquiv
      _ = Nat.card (derivedSubgroup H) := by rw [hmap]
  have hprod : Nat.card (A ⧸ derivedSubgroup A) *
      Nat.card (derivedSubgroup A) =
      Nat.card (H ⧸ derivedSubgroup H) *
        Nat.card (derivedSubgroup H) := by
    calc
      Nat.card (A ⧸ derivedSubgroup A) * Nat.card (derivedSubgroup A) =
          Nat.card A := (Subgroup.card_eq_card_quotient_mul_card_subgroup
            (derivedSubgroup A)).symm
      _ = Nat.card H := hAcard
      _ = Nat.card (H ⧸ derivedSubgroup H) * Nat.card (derivedSubgroup H) :=
        Subgroup.card_eq_card_quotient_mul_card_subgroup
          (derivedSubgroup H)
  apply Nat.eq_of_mul_eq_mul_right (Nat.card_pos :
    0 < Nat.card (derivedSubgroup H))
  rw [hDcard] at hprod
  exact hprod

public theorem corollary_9_5_ambient_abelianization
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X} {p : ℕ} [Fact p.Prime]
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hp : p ∣ Nat.card
      (((W ⊓ (M ⊓ rightConjugate M t) : Subgroup X) : Type u) ⧸
        derivedSubgroup
          ((W ⊓ (M ⊓ rightConjugate M t) : Subgroup X) : Type u)))
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (h43 : II1Lemma43bCyclic (X := X)) :
    Lemma94AlternativeB (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t p := by
  apply corollary_9_5 hM ht htM d83 h84 hW ?_ hIne h43
  rw [natCard_abelianization_subgroupOf_eq inf_le_left]
  exact hp

public theorem corollary96_fixedPointFree_of_corollary95
    {X : Type u} [Group X] [Finite X]
    {D E : Subgroup X} {t : X}
    (h95 : ∀ p : ℕ, Nat.Prime p →
      p ∣ Nat.card (E ⧸ derivedSubgroup E) →
      Lemma94AlternativeB D E t p)
    {x : X}
    (hxEV : x ∈ E ⊓ peterfalviV D t)
    (hxDer : x ∉ (derivedSubgroup E).map E.subtype) :
    ∀ k : X, k ∈ peterfalviKSet D t → k * x = x * k → k = 1 := by
  let xE : E := ⟨x, hxEV.1⟩
  let q : E →* E ⧸ derivedSubgroup E := QuotientGroup.mk' (derivedSubgroup E)
  have hqx_ne : q xE ≠ 1 := by
    intro hqx
    apply hxDer
    exact Subgroup.mem_map_of_mem E.subtype
      ((QuotientGroup.eq_one_iff xE).mp hqx)
  have horderQ_ne_one : orderOf (q xE) ≠ 1 := by
    intro horder
    exact hqx_ne (orderOf_eq_one_iff.mp horder)
  obtain ⟨p, hp, hpQ⟩ := Nat.exists_prime_and_dvd horderQ_ne_one
  have hpAb : p ∣ Nat.card (E ⧸ derivedSubgroup E) :=
    hpQ.trans (orderOf_dvd_natCard (q xE))
  have hpX : p ∣ orderOf xE := hpQ.trans (orderOf_map_dvd q xE)
  letI : Fact p.Prime := ⟨hp⟩
  have hpoword : orderOf (xE ^ (orderOf xE / p)) = p :=
    orderOf_pow_orderOf_div (orderOf_pos xE).ne' hpX
  obtain ⟨P, hPcyc, hPV, hPcentral⟩ := h95 p hp hpAb
  let V : Subgroup X := peterfalviV D t
  let EV : Subgroup X := E ⊓ V
  let EVE : Subgroup E := EV.subgroupOf E
  have hP_EVE : (P : Subgroup E) ≤ EVE := by
    intro a ha
    change (a : X) ∈ EV
    refine ⟨a.property, ?_⟩
    exact hPV (Subgroup.mem_map_of_mem E.subtype ha)
  let PEV : Sylow p EVE := P.subtype hP_EVE
  let xEV : EVE := ⟨xE, hxEV⟩
  let gEV : EVE := xEV ^ (orderOf xE / p)
  have hgord : orderOf gEV = p := by
    calc
      orderOf gEV = orderOf (EVE.subtype gEV) :=
        (orderOf_injective EVE.subtype EVE.subtype_injective gEV).symm
      _ = orderOf (xE ^ (orderOf xE / p)) := by rfl
      _ = p := hpoword
  have hzp : IsPGroup p (Subgroup.zpowers gEV) := by
    apply IsPGroup.of_card
    calc
      Nat.card (Subgroup.zpowers gEV) = orderOf gEV := Nat.card_zpowers gEV
      _ = p := hgord
      _ = p ^ 1 := by simp
  obtain ⟨QEV, hZQ⟩ := hzp.exists_le_sylow
  obtain ⟨v, hvQ⟩ := MulAction.exists_smul_eq EVE QEV PEV
  have hgenQ : gEV ∈ QEV := hZQ (Subgroup.mem_zpowers gEV)
  have hgenP : MulAut.conj v gEV ∈ (PEV : Subgroup EVE) := by
    rw [← hvQ, Sylow.coe_subgroup_smul]
    exact Subgroup.smul_mem_pointwise_smul gEV (MulAut.conj v) QEV hgenQ
  have hgenPE : ((MulAut.conj v gEV : EVE) : E) ∈ (P : Subgroup E) := hgenP
  have hgenPX : ((MulAut.conj v gEV : EVE) : X) ∈
      (P : Subgroup E).map E.subtype :=
    Subgroup.mem_map_of_mem E.subtype hgenPE
  have hgenPX' : (v : X) * (x ^ (orderOf xE / p)) * (v : X)⁻¹ ∈
      (P : Subgroup E).map E.subtype := by
    simpa [gEV, xEV, xE, MulAut.conj_apply] using hgenPX
  have hgen_ne_one : (v : X) * (x ^ (orderOf xE / p)) * (v : X)⁻¹ ≠ 1 := by
    intro h
    have hpowone : x ^ (orderOf xE / p) = 1 := by
      apply (MulAut.conj (v : X)).injective
      simpa [MulAut.conj_apply] using h
    have : (xE ^ (orderOf xE / p)) = 1 := by
      apply Subtype.ext
      simpa [xE] using hpowone
    exact (hp.ne_one) (by simpa [hpoword] using congrArg orderOf this)
  intro k hk hcomm
  have hcommPow : k * x ^ (orderOf xE / p) =
      x ^ (orderOf xE / p) * k := by
    exact (show Commute k x from hcomm).pow_right _ |>.eq
  let k' : X := (v : X) * k * (v : X)⁻¹
  have hk' : k' ∈ peterfalviKSet D t := by
    have hvV : (v : X) ∈ peterfalviV D t := by
      exact v.property.2
    exact peterfalviKSet_conj_mem_of_mem_V hvV hk
  have hcomm' : k' * ((v : X) * x ^ (orderOf xE / p) * (v : X)⁻¹) =
      ((v : X) * x ^ (orderOf xE / p) * (v : X)⁻¹) * k' := by
    dsimp [k']
    simpa [mul_assoc] using congrArg
      (fun z : X => (v : X) * z * (v : X)⁻¹) hcommPow
  have hkone : k' = 1 :=
    hPcentral _ hgenPX' hgen_ne_one _ hk' hcomm'
  have hkone' := congrArg (fun z : X => (v : X)⁻¹ * z * (v : X)) hkone
  simpa [k', mul_assoc] using hkone'

public theorem corollary96_fixedPointFree_of_source
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (h43 : II1Lemma43bCyclic (X := X))
    {x : X}
    (hxEV : x ∈
      (W ⊓ (M ⊓ rightConjugate M t)) ⊓
        peterfalviV (M ⊓ rightConjugate M t) t)
    (hxDer : x ∉
      (derivedSubgroup
        ((W ⊓ (M ⊓ rightConjugate M t) : Subgroup X) : Type u)).map
          (W ⊓ (M ⊓ rightConjugate M t)).subtype) :
    ∀ k : X,
      k ∈ peterfalviKSet (M ⊓ rightConjugate M t) t →
      k * x = x * k → k = 1 := by
  apply corollary96_fixedPointFree_of_corollary95 ?_ hxEV hxDer
  intro p hp hpAb
  letI : Fact p.Prime := ⟨hp⟩
  exact corollary_9_5_ambient_abelianization hM ht htM d83 h84 hW hpAb
    hIne h43

public structure Corollary96Conclusion
    {X : Type u} [Group X] [Finite X]
    (D E : Subgroup X) (t : X) : Prop where
  peterfalviKSet_subset_closure :
    peterfalviKSet D t ⊆ Subgroup.closure (peterfalviKSet D t)
  closure_le_derived :
    Subgroup.closure (peterfalviKSet D t) ≤
      (derivedSubgroup E).map E.subtype
  rightConjugate_eq : rightConjugate E t = E
  eq_mul_fixed :
    (E : Set X) =
      (Subgroup.closure (peterfalviKSet D t) : Set X) *
        ((E ⊓ peterfalviV D t : Subgroup X) : Set X)
  inf_fixed_ne_bot : E ⊓ peterfalviV D t ≠ ⊥
  fixedPointFree :
    ∀ x : X, x ∈ E ⊓ peterfalviV D t →
      x ∉ (derivedSubgroup E).map E.subtype →
      ∀ k : X, k ∈ peterfalviKSet D t →
        k * x = x * k → k = 1

public theorem corollary_9_6
    {X : Type u} [Group X] [Finite X]
    {M W : Subgroup X} {t : X}
    (hM : IsStronglyEmbedded M)
    (ht : IsInvolution t) (htM : t ∉ M)
    (d83 : Lemma83Data M t)
    (h84 : Proposition84Statement M t d83.u)
    (hW : IsMinimalNormalSupplement M
      (M ⊓ rightConjugate M t) W)
    (hEne : W ⊓ (M ⊓ rightConjugate M t) ≠ ⊥)
    (hIne : ∃ x : X,
      x ∈ peterfalviKSet (M ⊓ rightConjugate M t) t ∧ x ≠ 1)
    (h43 : II1Lemma43bCyclic (X := X)) :
    Corollary96Conclusion
      (M ⊓ rightConjugate M t)
      (W ⊓ (M ⊓ rightConjugate M t)) t := by
  classical
  let D : Subgroup X := M ⊓ rightConjugate M t
  let E : Subgroup X := W ⊓ D
  have hDnorm : t ∈ Subgroup.normalizer (D : Set X) := by
    simpa [D] using inf_rightConjugate_mem_normalizer_of_isInvolution M ht
  have hDodd : Odd (Nat.card D) := by
    simpa [D] using hM.inf_rightConjugate_card_odd htM
  have hED : E ≤ D := inf_le_right
  have hEN : (E.subgroupOf D).Normal := by
    simpa [D, E] using hW.inf_normal_in_right inf_le_left
  have hEne' : E ≠ ⊥ := by simpa [D, E] using hEne
  have h95 : ∀ p : ℕ, Nat.Prime p →
      p ∣ Nat.card (E ⧸ derivedSubgroup E) →
      Lemma94AlternativeB D E t p := by
    intro p hp hpAb
    letI : Fact p.Prime := ⟨hp⟩
    simpa [D, E] using
      (corollary_9_5_ambient_abelianization hM ht htM d83 h84 hW
        (by simpa [D, E] using hpAb) hIne h43)
  have hEodd : Odd (Nat.card E) :=
    hDodd.of_dvd_nat (Subgroup.card_dvd_of_le hED)
  have hEsolv : Group.IsSolvable E := odd_order_theorem E hEodd
  letI : Group.IsSolvable E := hEsolv
  haveI : Nontrivial E := (Subgroup.nontrivial_iff_ne_bot E).2 hEne'
  have hcommLt : derivedSubgroup E < ⊤ :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := E)
  have hAbOneLt : 1 < Nat.card (E ⧸ derivedSubgroup E) := by
    have hindex : 1 < (derivedSubgroup E).index :=
      Subgroup.one_lt_index_of_ne_top hcommLt.ne
    simpa [Subgroup.index_eq_card] using hindex
  obtain ⟨p, hp, hpAb⟩ := Nat.exists_prime_and_dvd hAbOneLt.ne'
  letI : Fact p.Prime := ⟨hp⟩
  have hB : Lemma94AlternativeB D E t p := h95 p hp hpAb
  have hKder : Subgroup.closure (peterfalviKSet D t) ≤
      (derivedSubgroup E).map E.subtype :=
    closure_peterfalviKSet_le_derived_of_alternativeB
      ht hDnorm hDodd hED hEN hpAb hB
  have hclosure : Subgroup.closure (peterfalviKSet D t) =
      ⁅D, Subgroup.zpowers t⁆ :=
    closure_peterfalviKSet_eq_commutator_zpowers ht hDnorm hDodd
  have hcomm_le_E : ⁅D, Subgroup.zpowers t⁆ ≤ E := by
    rw [← hclosure]
    exact hKder.trans (Subgroup.map_subtype_le (derivedSubgroup E))
  have hcommD_t {x : X} (hx : x ∈ D) : ⁅x, t⁆ ∈ E :=
    hcomm_le_E (Subgroup.commutator_mem_commutator hx
      (Subgroup.mem_zpowers t))
  have hEt : t ∈ Subgroup.normalizer (E : Set X) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      have hcx : ⁅x⁻¹, t⁆ ∈ E := hcommD_t (D.inv_mem (hED hx))
      have hxeq : x * ⁅x⁻¹, t⁆ = t * x * t⁻¹ := by
        simp [commutatorElement_def, mul_assoc]
      rw [← hxeq]
      exact E.mul_mem hx hcx
    · intro hx
      have hforward := (show ∀ y : X, y ∈ E →
          t * y * t⁻¹ ∈ E from by
        intro y hy
        have hcy : ⁅y⁻¹, t⁆ ∈ E := hcommD_t (D.inv_mem (hED hy))
        have hyeq : y * ⁅y⁻¹, t⁆ = t * y * t⁻¹ := by
          simp [commutatorElement_def, mul_assoc]
        rw [← hyeq]
        exact E.mul_mem hy hcy) (t * x * t⁻¹) hx
      have htt : t * t = 1 := by simpa [pow_two] using ht.sq_eq_one
      have heq : t * (t * x * t⁻¹) * t⁻¹ = x := by
        rw [ht.inv_eq_self]
        calc
          t * (t * x * t) * t = (t * t) * x * (t * t) := by group
          _ = x := by rw [htt]; simp
      rw [heq] at hforward
      exact hforward
  have hEtEq : rightConjugate E t = E := by
    simpa [rightConjugate, ht.inv_eq_self] using
      (section11_conjBy_eq_of_mem_normalizer hEt)
  have hdecomp :
      (E : Set X) =
          (Subgroup.closure (peterfalviKSet D t) : Set X) *
            ((E ⊓ peterfalviV D t : Subgroup X) : Set X) ∧
        E = Subgroup.closure (peterfalviKSet D t) ⊔
          (E ⊓ peterfalviV D t) :=
    E_eq_closure_sup_fixed ht hDnorm hED hEt hDodd hcomm_le_E hclosure
  rcases hB with ⟨P, _hPcyclic, hPV, _hPcentral⟩
  have hpE : p ∣ Nat.card E :=
    hpAb.trans (Subgroup.card_quotient_dvd_card (s := derivedSubgroup E))
  have hPne : (P : Subgroup E) ≠ ⊥ := P.ne_bot_of_dvd_card hpE
  have hPmapne : (P : Subgroup E).map E.subtype ≠ ⊥ := by
    intro hbot
    exact hPne
      ((Subgroup.map_eq_bot_iff_of_injective
        (H := (P : Subgroup E)) (f := E.subtype)
        E.subtype_injective).mp hbot)
  have hPmapEV : (P : Subgroup E).map E.subtype ≤
      E ⊓ peterfalviV D t := by
    intro x hx
    exact ⟨Subgroup.map_subtype_le (P : Subgroup E) hx, hPV hx⟩
  have hEVne : E ⊓ peterfalviV D t ≠ ⊥ := by
    intro hbot
    apply hPmapne
    apply le_antisymm
    · simpa [hbot] using hPmapEV
    · exact bot_le
  refine
    { peterfalviKSet_subset_closure := Subgroup.subset_closure
      closure_le_derived := hKder
      rightConjugate_eq := hEtEq
      eq_mul_fixed := hdecomp.1
      inf_fixed_ne_bot := hEVne
      fixedPointFree := ?_ }
  intro x hxEV hxDer
  simpa [D, E] using
    (corollary96_fixedPointFree_of_source hM ht htM d83 h84 hW hIne
      h43 (x := x) (by simpa [D, E] using hxEV)
      (by simpa [D, E] using hxDer))


end CFSG.BenderSuzuki
