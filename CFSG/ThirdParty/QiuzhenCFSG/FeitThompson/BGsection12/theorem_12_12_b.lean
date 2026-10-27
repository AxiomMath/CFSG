module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection12.theorem_12_12_a

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

/-!
# theorem_12_12_b
-/

section Section12

variable {G : Type*} [Group G] [Finite G] [IsMinCE G]

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_exponent_eq_lcm_of_complement_normal_coprime
    {H K L : Subgroup G}
    (hKL : section12ComplementIn H K L)
    (hKnorm : section10NormalIn K H)
    (hcop : Nat.Coprime (Nat.card K) (Nat.card L)) :
    Monoid.exponent H = Nat.lcm (Monoid.exponent K) (Monoid.exponent L) := by
  classical
  have hKL' := hKL
  rcases hKL with ⟨hKH, hLH, _hHsup, _hdisj⟩
  have hcomp' : (L.subgroupOf H).IsComplement' (K.subgroupOf H) :=
    section12_complementIn_of_normal_isComplement' hKL' hKnorm
  have : (K.subgroupOf H).Normal := hKnorm.2
  have hKsub_exp : Monoid.exponent (K.subgroupOf H) = Monoid.exponent K := by
    simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH)
  have hLsub_exp : Monoid.exponent (L.subgroupOf H) = Monoid.exponent L := by
    simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH)
  have hquot_exp : Monoid.exponent (H ⧸ K.subgroupOf H) = Monoid.exponent L := by
    calc
      Monoid.exponent (H ⧸ K.subgroupOf H) = Monoid.exponent (L.subgroupOf H) := by
        simpa using Monoid.exponent_eq_of_mulEquiv hcomp'.QuotientMulEquiv
      _ = Monoid.exponent L := hLsub_exp
  have hKexp_dvd_H : Monoid.exponent K ∣ Monoid.exponent H := by
    have hsub :
        Monoid.exponent (K.subgroupOf H) ∣ Monoid.exponent H :=
      Monoid.exponent_dvd_of_monoidHom
        (K.subgroupOf H).subtype (K.subgroupOf H).subtype_injective
    simpa [hKsub_exp] using hsub
  have hLexp_dvd_H : Monoid.exponent L ∣ Monoid.exponent H := by
    have hquot : Monoid.exponent (H ⧸ K.subgroupOf H) ∣ Monoid.exponent H :=
      Group.exponent_quotient_dvd (K.subgroupOf H)
    rw [hquot_exp] at hquot
    exact hquot
  have hExpCop :
      Nat.Coprime (Monoid.exponent K) (Monoid.exponent L) := by
    exact hcop.of_dvd Group.exponent_dvd_nat_card Group.exponent_dvd_nat_card
  apply Nat.dvd_antisymm
  · rw [hExpCop.lcm_eq_mul]
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    have hqpow :
        (QuotientGroup.mk' (K.subgroupOf H) g) ^ Monoid.exponent L = 1 := by
      simpa [hquot_exp] using
        (Monoid.pow_exponent_eq_one (QuotientGroup.mk' (K.subgroupOf H) g))
    have hgpowK : g ^ Monoid.exponent L ∈ K.subgroupOf H := by
      apply (QuotientGroup.eq_one_iff (N := K.subgroupOf H)
        (x := g ^ Monoid.exponent L)).1
      simpa using hqpow
    let gK : K.subgroupOf H := ⟨g ^ Monoid.exponent L, hgpowK⟩
    have hgKpow : gK ^ Monoid.exponent K = 1 := by
      have hKpow :
          gK ^ Monoid.exponent (K.subgroupOf H) = 1 :=
        Monoid.pow_exponent_eq_one gK
      simpa [hKsub_exp] using hKpow
    have hgpow : g ^ (Monoid.exponent L * Monoid.exponent K) = 1 := by
      have hcoe :=
        congrArg (fun x : K.subgroupOf H => (x : H)) hgKpow
      simpa [gK, pow_mul] using hcoe
    simpa [Nat.mul_comm] using hgpow
  · exact Nat.lcm_dvd hKexp_dvd_H hLexp_dvd_H

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_exponent_eq_lcm_of_complement_commutative
    {H K L : Subgroup G}
    (hKL : section12ComplementIn H K L)
    (hHcomm : IsMulCommutative H) :
    Monoid.exponent H = Nat.lcm (Monoid.exponent K) (Monoid.exponent L) := by
  classical
  rcases hKL with ⟨hKH, hLH, hHsup, _hdisj⟩
  let : IsMulCommutative H := hHcomm
  let : CommGroup H := IsMulCommutative.instCommGroup
  have hKsub_exp : Monoid.exponent (K.subgroupOf H) = Monoid.exponent K := by
    simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hKH)
  have hLsub_exp : Monoid.exponent (L.subgroupOf H) = Monoid.exponent L := by
    simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLH)
  let n : Nat := Nat.lcm (Monoid.exponent K) (Monoid.exponent L)
  have hKsub_exp_dvd_n : Monoid.exponent (K.subgroupOf H) ∣ n := by
    simpa [n, hKsub_exp] using Nat.dvd_lcm_left (Monoid.exponent K) (Monoid.exponent L)
  have hLsub_exp_dvd_n : Monoid.exponent (L.subgroupOf H) ∣ n := by
    simpa [n, hLsub_exp] using Nat.dvd_lcm_right (Monoid.exponent K) (Monoid.exponent L)
  have hKL_top : K.subgroupOf H ⊔ L.subgroupOf H = ⊤ := by
    calc
      K.subgroupOf H ⊔ L.subgroupOf H = (K ⊔ L).subgroupOf H := by
        symm
        exact Subgroup.subgroupOf_sup (A := K) (A' := L) (B := H) hKH hLH
      _ = ⊤ := by
        apply Subgroup.subgroupOf_eq_top.2
        exact le_of_eq hHsup
  have hKpow (k : K.subgroupOf H) : (k : H) ^ n = 1 := by
    rcases hKsub_exp_dvd_n with ⟨m, hm⟩
    have hkpow : k ^ n = 1 := by
      rw [hm, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
    exact congrArg (fun x : K.subgroupOf H => (x : H)) hkpow
  have hLpow (l : L.subgroupOf H) : (l : H) ^ n = 1 := by
    rcases hLsub_exp_dvd_n with ⟨m, hm⟩
    have hlpow : l ^ n = 1 := by
      rw [hm, pow_mul, Monoid.pow_exponent_eq_one, one_pow]
    exact congrArg (fun x : L.subgroupOf H => (x : H)) hlpow
  have hExp_dvd_lcm : Monoid.exponent H ∣ n := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one ?_
    intro g
    have : (L.subgroupOf H).Normal := by infer_instance
    have hg_sup : g ∈ K.subgroupOf H ⊔ L.subgroupOf H := by
      simp [hKL_top]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := K.subgroupOf H) (t := L.subgroupOf H) (x := g)).1 hg_sup with
      ⟨k, hk, l, hl, hkl⟩
    let kK : K.subgroupOf H := ⟨k, hk⟩
    let lL : L.subgroupOf H := ⟨l, hl⟩
    calc
      g ^ n = (k * l) ^ n := by rw [hkl]
      _ = k ^ n * l ^ n := by rw [mul_pow]
      _ = 1 := by
        simpa [kK, lL] using congrArg₂ (fun a b : H => a * b) (hKpow kK) (hLpow lL)
  have hKexp_dvd_H : Monoid.exponent K ∣ Monoid.exponent H := by
    have hsub :
        Monoid.exponent (K.subgroupOf H) ∣ Monoid.exponent H :=
      Monoid.exponent_dvd_of_monoidHom
        (K.subgroupOf H).subtype (K.subgroupOf H).subtype_injective
    simpa [hKsub_exp] using hsub
  have hLexp_dvd_H : Monoid.exponent L ∣ Monoid.exponent H := by
    have hsub :
        Monoid.exponent (L.subgroupOf H) ∣ Monoid.exponent H :=
      Monoid.exponent_dvd_of_monoidHom
        (L.subgroupOf H).subtype (L.subgroupOf H).subtype_injective
    simpa [hLsub_exp] using hsub
  exact Nat.dvd_antisymm hExp_dvd_lcm (Nat.lcm_dvd hKexp_dvd_H hLexp_dvd_H)

private theorem CFSG.section12_exponent_eq_of_CA_msigma_complement_in_E2
    {M E E₁₂ E₁ E₂ E₃ A P₀ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hSylow : section12HasNonabelianSylowSubgroup p G)
    (hP₀E₂ : P₀ ≤ E₂)
    (hE₂eq : E₂ = subgroupCentralizerIn A (section10Msigma M) ⊔ P₀)
    (hdisj : Disjoint (subgroupCentralizerIn A (section10Msigma M)) P₀) :
    Monoid.exponent P₀ = Monoid.exponent E₂ := by
  classical
  let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
  have : Fact p.val.Prime := ⟨p.2⟩
  have hE₂p : IsPGroup p.val E₂ :=
    section12_E2_isPGroup_of_tau2_singleton
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hCE₂ : C ≤ E₂ := by
    simpa [C] using
      section12_CA_msigma_le_E2_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
  have hcompP₀ : section12ComplementIn E₂ C P₀ := ⟨hCE₂, hP₀E₂, hE₂eq, hdisj⟩
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hCnormE : section10NormalIn C E := by
    simpa [C] using
      section12_CA_msigma_normalIn_E
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) hE hAnorm
  have hE₂E : E₂ ≤ E := hE.2.2.2.1.1.trans hE.2.1.1
  have hE_norm_C : E ≤ Subgroup.normalizer (C : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCnormE.1).1 hCnormE.2
  have hCnormE₂ : section10NormalIn C E₂ := by
    refine ⟨hCE₂, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hCE₂).2 (hE₂E.trans hE_norm_C)
  have hcompP₀' : (P₀.subgroupOf E₂).IsComplement' (C.subgroupOf E₂) :=
    section12_complementIn_of_normal_isComplement' hcompP₀ hCnormE₂
  have : (C.subgroupOf E₂).Normal := hCnormE₂.2
  have hquot_exp_P₀ : Monoid.exponent P₀ = Monoid.exponent (E₂ ⧸ C.subgroupOf E₂) := by
    calc
      Monoid.exponent P₀ = Monoid.exponent (P₀.subgroupOf E₂) := by
        symm
        simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hP₀E₂)
      _ = Monoid.exponent (E₂ ⧸ C.subgroupOf E₂) := by
        symm
        simpa using Monoid.exponent_eq_of_mulEquiv hcompP₀'.QuotientMulEquiv
  obtain ⟨Z, hZE₂, hZcyc, hCdisjZ, hE₂eqZ⟩ :=
    section12_CA_msigma_split_E2_cyclic_factor
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hcompZ : section12ComplementIn E₂ C Z := ⟨hCE₂, hZE₂, hE₂eqZ, hCdisjZ⟩
  have hcompZ' : (Z.subgroupOf E₂).IsComplement' (C.subgroupOf E₂) :=
    section12_complementIn_of_normal_isComplement' hcompZ hCnormE₂
  have hZsub_exp : Monoid.exponent (Z.subgroupOf E₂) = Monoid.exponent Z := by
    simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hZE₂)
  have hquot_exp_Z : Monoid.exponent Z = Monoid.exponent (E₂ ⧸ C.subgroupOf E₂) := by
    calc
      Monoid.exponent Z = Monoid.exponent (Z.subgroupOf E₂) := by
        symm
        simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hZE₂)
      _ = Monoid.exponent (E₂ ⧸ C.subgroupOf E₂) := by
        symm
        simpa using Monoid.exponent_eq_of_mulEquiv hcompZ'.QuotientMulEquiv
  have hE₂_le_centA : E₂ ≤ Subgroup.centralizer (A : Set G) :=
    section12_E2_le_centralizer_rankTwo_tau2_of_theorem_12_7
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA hSylow
  have hCZcent : C ≤ Subgroup.centralizer (Z : Set G) := by
    intro c hc
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzCentA : z ∈ Subgroup.centralizer (A : Set G) :=
      hE₂_le_centA (hZE₂ hz)
    exact (Subgroup.mem_centralizer_iff.mp hzCentA c hc.1).symm
  have hA_le_E₂ : A ≤ E₂ :=
    section12_rankTwo_tau2_le_E2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA
  rcases section12_rankTwo_elementary hA with ⟨hAcard, _hAelem⟩
  have hCcard : Nat.card C = p.val := by
    simpa [C] using
      (theorem_12_7_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA hSylow).1
  have hZne : Z ≠ ⊥ := by
    intro hZbot
    have hAC : A ≤ C := by
      have hE₂C : E₂ = C := by simpa [hZbot] using hE₂eqZ
      rwa [hE₂C] at hA_le_E₂
    have hpow_le : p.val ^ 2 ≤ p.val := by
      have hAdvdC : Nat.card A ∣ Nat.card C := Subgroup.card_dvd_of_le hAC
      exact Nat.le_of_dvd p.2.pos (by simpa [hAcard, hCcard] using hAdvdC)
    nlinarith [p.2.one_lt]
  have hZp : IsPGroup p.val Z := by
    have hZsub_p : IsPGroup p.val (Z.subgroupOf E₂) :=
      hE₂p.to_subgroup (Z.subgroupOf E₂)
    exact hZsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hZE₂)
  have hp_dvd_exp_Z : p.val ∣ Monoid.exponent Z := by
    have : Nontrivial Z := (Subgroup.nontrivial_iff_ne_bot (H := Z)).2 hZne
    rcases (IsPGroup.nontrivial_iff_card (p := p.val) (G := Z) (hG := hZp)).mp
      inferInstance with ⟨n, hn, hcardZ⟩
    have hp_dvd_cardZ : p.val ∣ Nat.card Z := by
      rcases Nat.exists_eq_succ_of_ne_zero (Nat.ne_of_gt hn) with ⟨m, rfl⟩
      refine ⟨p.val ^ m, ?_⟩
      rw [hcardZ, pow_succ']
    rw [hZcyc.exponent_eq_card]
    exact hp_dvd_cardZ
  have hCsub_exp : Monoid.exponent (C.subgroupOf E₂) = p.val := by
    calc
      Monoid.exponent (C.subgroupOf E₂) = Monoid.exponent C := by
        simpa using Monoid.exponent_eq_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hCE₂)
      _ = p.val := by
        have hCcyc : IsCyclic C := isCyclic_of_prime_card hCcard
        rw [hCcyc.exponent_eq_card, hCcard]
  have hExpE₂_dvd_Z : Monoid.exponent E₂ ∣ Monoid.exponent Z := by
    apply Monoid.exponent_dvd_of_forall_pow_eq_one
    intro g
    have hgsup0 : g ∈ (C ⊔ Z).subgroupOf E₂ := by
      show ((g : E₂) : G) ∈ C ⊔ Z
      simpa [C, hE₂eqZ] using g.property
    have hgsup : g ∈ C.subgroupOf E₂ ⊔ Z.subgroupOf E₂ := by
      rwa [Subgroup.subgroupOf_sup (A := C) (A' := Z) (B := E₂) hCE₂ hZE₂] at hgsup0
    have : (C.subgroupOf E₂).Normal := hCnormE₂.2
    rcases (Subgroup.mem_sup_of_normal_left
        (s := C.subgroupOf E₂) (t := Z.subgroupOf E₂) (x := g)).1 hgsup with
      ⟨c, hc, z, hz, hcz⟩
    let cC : C.subgroupOf E₂ := ⟨c, hc⟩
    let zZ : Z.subgroupOf E₂ := ⟨z, hz⟩
    have hcComm : Commute c z := by
      rw [commute_iff_eq]
      apply Subtype.ext
      have hcCG : ((c : E₂) : G) ∈ C := by
        simpa [Subgroup.mem_subgroupOf] using hc
      have hzG : ((z : E₂) : G) ∈ Z := by
        simpa [Subgroup.mem_subgroupOf] using hz
      exact Subgroup.mem_centralizer_iff.mp (hCZcent hcCG)
        ((z : E₂) : G) hzG |>.symm
    have hCsub_dvd_exp_Z : Monoid.exponent (C.subgroupOf E₂) ∣ Monoid.exponent Z := by
      rw [hCsub_exp]
      exact hp_dvd_exp_Z
    have hcPow : (c : E₂) ^ Monoid.exponent Z = 1 := by
      have hcPow' : cC ^ Monoid.exponent Z = 1 := by
        exact (Monoid.exponent_dvd_iff_forall_pow_eq_one).1 hCsub_dvd_exp_Z cC
      exact congrArg (fun x : C.subgroupOf E₂ => (x : E₂)) hcPow'
    have hzPow : (z : E₂) ^ Monoid.exponent Z = 1 := by
      have hzPow' : zZ ^ Monoid.exponent Z = 1 := by
        simpa [hZsub_exp] using Monoid.pow_exponent_eq_one zZ
      exact congrArg (fun x : Z.subgroupOf E₂ => (x : E₂)) hzPow'
    calc
      g ^ Monoid.exponent Z
          = (c * z) ^ Monoid.exponent Z := by rw [← hcz]
      _ = c ^ Monoid.exponent Z * z ^ Monoid.exponent Z := by rw [hcComm.mul_pow]
      _ = 1 := by simp [hcPow, hzPow]
  have hExpZ_dvd_E₂ : Monoid.exponent Z ∣ Monoid.exponent E₂ := by
    have hsub :
        Monoid.exponent (Z.subgroupOf E₂) ∣ Monoid.exponent E₂ :=
      Monoid.exponent_dvd_of_monoidHom
        (Z.subgroupOf E₂).subtype (Z.subgroupOf E₂).subtype_injective
    simpa [hZsub_exp] using hsub
  have hExpZ_eq_E₂ : Monoid.exponent Z = Monoid.exponent E₂ :=
    Nat.dvd_antisymm hExpZ_dvd_E₂ hExpE₂_dvd_Z
  calc
    Monoid.exponent P₀ = Monoid.exponent (E₂ ⧸ C.subgroupOf E₂) := hquot_exp_P₀
    _ = Monoid.exponent Z := by rw [hquot_exp_Z]
    _ = Monoid.exponent E₂ := hExpZ_eq_E₂

omit [IsMinCE G] in
public theorem CFSG.section12_exists_primeOrder_zpowers_of_prime_dvd_card
    {B : Subgroup G} {q : Nat.Primes} (hqB : q.val ∣ Nat.card B) :
    ∃ z : G, z ∈ B ∧ z ≠ 1 ∧
      Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn q B := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  obtain ⟨z₀, hz₀_order⟩ := exists_prime_orderOf_dvd_card' (G := B) q.val hqB
  let z : G := z₀
  have hzB : z ∈ B := z₀.property
  have hz_order : orderOf z = q.val := by
    simpa [z, Subgroup.orderOf_coe] using hz₀_order
  have hz_ne : z ≠ 1 := by
    intro hz1
    have hq_one : q.val = 1 := by
      rw [← hz_order, hz1, orderOf_one]
    exact q.property.ne_one hq_one
  have hX_card : Nat.card (Subgroup.zpowers z) = q.val := by
    rw [Nat.card_zpowers]
    exact hz_order
  exact ⟨z, hzB, hz_ne,
    by
      simpa [section10PrimeOrderSubgroupsIn] using
        (⟨Subgroup.zpowers_le.2 hzB, hX_card⟩ :
          Subgroup.zpowers z ≤ B ∧ Nat.card (Subgroup.zpowers z) = q.val)⟩

private theorem CFSG.section12_tau1_primeSupport_of_centralizer_of_complement
    {M E E₁₂ E₁ E₂ E₃ A E₀ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hE₀comp : section12ComplementIn E
      (subgroupCentralizerIn A (section10Msigma M)) E₀)
    (hSylow : section12HasNonabelianSylowSubgroup p G) :
    ∀ x : G, x ∈ section10Msigma M → x ≠ 1 →
      subgroupPrimeSet (elementCentralizerIn E₀ x) ⊆ section12Tau1Primes M := by
  classical
  intro x hxσ hxne q hqC
  have hE₀E : E₀ ≤ E := hE₀comp.2.1
  have hC_le_E₀ : elementCentralizerIn E₀ x ≤ E₀ := inf_le_left
  obtain ⟨z, hzC, hzne, hZq⟩ :=
    section12_exists_primeOrder_zpowers_of_prime_dvd_card
      (B := elementCentralizerIn E₀ x) (q := q) hqC
  have hzE₀ : z ∈ E₀ := hC_le_E₀ hzC
  have hzE : z ∈ E := hE₀E hzE₀
  have hZ_E : Subgroup.zpowers z ∈ section10PrimeOrderSubgroupsIn q E := by
    rcases (show Subgroup.zpowers z ≤ elementCentralizerIn E₀ x ∧
        Nat.card (Subgroup.zpowers z) = q.val from hZq) with ⟨hZC, hZcard⟩
    exact ⟨hZC.trans (hC_le_E₀.trans hE₀E), hZcard⟩
  have hqτ :
      q ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪ section12Tau3Primes M := by
    have hqE : q ∈ subgroupPrimeSet E := by
      rcases (show Subgroup.zpowers z ≤ E ∧
          Nat.card (Subgroup.zpowers z) = q.val from hZ_E) with ⟨hZE, hZcard⟩
      have hqZ : q.val ∣ Nat.card (Subgroup.zpowers z) := by rw [hZcard]
      exact hqZ.trans (Subgroup.card_dvd_of_le hZE)
    exact section12_prime_mem_tau_union_of_mem_E hM hE.1 hqE
  rcases hqτ with hqτ12 | hqτ3
  · rcases hqτ12 with hqτ1 | hqτ2
    · exact hqτ1
    · have hτ2_single : section12Tau2Primes M = {p} :=
        theorem_12_7_a hM hE hp hA hSylow
      have hq_eq_p : q = p := by
        have hq_single : q ∈ ({p} : Set Nat.Primes) := by
          simpa [hτ2_single] using hqτ2
        simpa using hq_single
      have hZ_ne_A0 : Subgroup.zpowers z ≠ subgroupCentralizerIn A (section10Msigma M) := by
        intro hZ_eq_A0
        have hzA0 : z ∈ subgroupCentralizerIn A (section10Msigma M) := by
          rw [← hZ_eq_A0]
          exact Subgroup.mem_zpowers z
        have hzbot : z ∈ (⊥ : Subgroup G) := by
          have hzinf : z ∈ subgroupCentralizerIn A (section10Msigma M) ⊓ E₀ :=
            ⟨hzA0, hzE₀⟩
          simpa [hE₀comp.2.2.2.eq_bot] using hzinf
        exact hzne (by simpa using hzbot)
      have hZ_Msigma_bot :
          subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers z) = ⊥ :=
        (theorem_12_7_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA hSylow (Subgroup.zpowers z)
          (by simpa [hq_eq_p] using hZ_E) hZ_ne_A0).1
      have hxCz : x ∈ subgroupCentralizerIn (section10Msigma M) (Subgroup.zpowers z) := by
        refine ⟨hxσ, ?_⟩
        have hzCentX : z ∈ Subgroup.centralizer ({x} : Set G) := hzC.2
        change x ∈ Subgroup.centralizer (Subgroup.zpowers z : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rcases Subgroup.mem_zpowers_iff.mp hy with ⟨n, rfl⟩
        have hxz : x * z = z * x := by
          exact (Subgroup.mem_centralizer_iff.mp hzCentX) x (by simp)
        exact (Commute.zpow_right hxz n).eq.symm
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [hZ_Msigma_bot] using hxCz
      exact False.elim (hxne (by simpa using hxbot))
  · have hCx_bot :
        elementCentralizerIn (section10Msigma M) z = ⊥ :=
      corollary_12_6_d hM hE hp hA z ?_ hzne
    · have hxCz : x ∈ elementCentralizerIn (section10Msigma M) z := by
        refine ⟨hxσ, ?_⟩
        have hzCentX : z ∈ Subgroup.centralizer ({x} : Set G) := hzC.2
        change x ∈ Subgroup.centralizer ({z} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst y
        exact ((Subgroup.mem_centralizer_iff.mp hzCentX) x (by simp)).symm
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [hCx_bot] using hxCz
      exact False.elim (hxne (by simpa using hxbot))
    · rcases (show Subgroup.zpowers z ≤ E ∧
          Nat.card (Subgroup.zpowers z) = q.val from hZ_E) with ⟨hZE, hZcard⟩
      have hzE3 : z ∈ E₃ := by
        have hqZ : q.val ∣ Nat.card (Subgroup.zpowers z) := by rw [hZcard]
        have hZp : IsPGroup q.val (Subgroup.zpowers z) := by
          refine IsPGroup.of_card (p := q.val) (G := Subgroup.zpowers z) (n := 1) ?_
          simpa [pow_one] using hZcard
        have hZsubE : (Subgroup.zpowers z).subgroupOf E ≤ E₃.subgroupOf E := by
          have hE3norm : section10NormalIn E₃ E :=
            (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
              (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
          rcases hE with ⟨_hcomp, _hE12, _hE1, _hE2, hE3Hall⟩
          rcases hE3Hall with ⟨hE3E, hHallE3⟩
          have hZsub_p : IsPGroup q.val ((Subgroup.zpowers z).subgroupOf E) :=
            hZp.of_equiv
              (Subgroup.subgroupOfEquivOfLe (H := Subgroup.zpowers z) (K := E) hZE).symm
          have : (E₃.subgroupOf E).Normal := hE3norm.2
          exact section12_pSubgroup_le_normal_hall_of_prime_mem hHallE3 hqτ3 hZsub_p
        have hzsub : (⟨z, hzE⟩ : E) ∈ (Subgroup.zpowers z).subgroupOf E := by
          simp [Subgroup.mem_subgroupOf]
        exact hZsubE hzsub
      exact hzE3

private theorem CFSG.section12_complementToMsigma_ne_bot
    {M E : Subgroup G} (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E) :
    E ≠ ⊥ := by
  classical
  intro hEbot
  let N : Subgroup M := section10MsigmaSubgroup M
  let Ec : Subgroup M := E.subgroupOf M
  have hcomp' : Ec.IsComplement' N :=
    section12_complement_to_msigma_isComplement' (M := M) (E := E) hcomp
  have hEc_bot : Ec = ⊥ := by
    ext x
    constructor
    · intro hx
      change x = 1
      apply Subtype.ext
      have hxbot : (x : G) ∈ (⊥ : Subgroup G) := by
        simpa [Ec, hEbot] using hx
      simpa using hxbot
    · intro hx
      change (x : G) ∈ E
      rw [hEbot]
      change (x : G) = 1
      exact congrArg Subtype.val (by simpa using hx)
  have hNtop : N = ⊤ := by
    have hcomp_bot : (⊥ : Subgroup M).IsComplement' N := by
      simpa [hEc_bot] using hcomp'
    exact Subgroup.isComplement'_bot_left.mp hcomp_bot
  have hder_top : derivedSubgroup M = ⊤ := by
    apply top_le_iff.mp
    rw [← hNtop]
    exact (theorem_10_2_c (M := M) hM).2
  have hM_ne_bot : M ≠ ⊥ := by
    intro hMbot
    have hMsigma_le_M : section10Msigma M ≤ M := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hMsigma_bot : section10Msigma M = ⊥ := by
      exact le_bot_iff.mp (by simpa [hMbot] using hMsigma_le_M)
    exact (theorem_10_2_e (M := M) hM) hMsigma_bot
  have : Nontrivial M := (Subgroup.nontrivial_iff_ne_bot (H := M)).2 hM_ne_bot
  have hsolvM : Group.IsSolvable M :=
    IsMinCE.proper_subgroups_solvable M (lt_top_iff_ne_top.2 hM.1)
  have : Group.IsSolvable M := hsolvM
  have hcomm_lt : commutator M < (⊤ : Subgroup M) :=
    Group.IsSolvable.commutator_lt_top_of_nontrivial (G := M)
  have hcomm_top : commutator M = (⊤ : Subgroup M) := by
    simpa [derivedSubgroup, derivedSeries_one, _root_.commutator_def] using hder_top
  exact hcomm_lt.ne hcomm_top

private theorem CFSG.section12_frobeniusJoinWithKernel_of_trivial_centralizers
    {M E : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E)
    (hcentE :
      ∀ e : G, e ∈ E → e ≠ 1 →
        elementCentralizerIn (section10Msigma M) e = ⊥) :
    section12FrobeniusJoinWithKernel (section10Msigma M) E := by
  classical
  let S : Subgroup G := section10Msigma M ⊔ E
  let K : Subgroup S := (section10Msigma M).subgroupOf S
  let R : Subgroup S := E.subgroupOf S
  have hSleM : S ≤ M := by
    exact sup_le hcomp.1 hcomp.2.1
  have hKnorm : K.Normal := by
    dsimp [K, S]
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact hSleM.trans section12_le_normalizer_msigma
  have hcompS : section12ComplementIn S (section10Msigma M) E := by
    refine ⟨le_sup_left, le_sup_right, rfl, ?_⟩
    exact hcomp.2.2.2
  have hKnormS : section10NormalIn (section10Msigma M) S := ⟨le_sup_left, hKnorm⟩
  have hKR : K.IsComplement' R := by
    exact
      (section12_complementIn_of_normal_isComplement'
        (G := G) (H := S) (K := section10Msigma M) (L := E) hcompS hKnormS).symm
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card K = 1 :=
      (Subgroup.eq_bot_iff_card (H := K)).1 hbot
    have hcardσ : Nat.card (section10Msigma M) = 1 := by
      dsimp [K, S] at hcard
      rw [section12_card_subgroupOf_eq (H := section10Msigma M)
        (K := section10Msigma M ⊔ E) le_sup_left] at hcard
      exact hcard
    exact (theorem_10_2_e (M := M) hM)
      ((Subgroup.eq_bot_iff_card (H := section10Msigma M)).2 hcardσ)
  have hRne : R ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card R = 1 :=
      (Subgroup.eq_bot_iff_card (H := R)).1 hbot
    have hcardE : Nat.card E = 1 := by
      dsimp [R, S] at hcard
      rw [section12_card_subgroupOf_eq (H := E) (K := section10Msigma M ⊔ E)
        le_sup_right] at hcard
      exact hcard
    exact section12_complementToMsigma_ne_bot hM hcomp
      ((Subgroup.eq_bot_iff_card (H := E)).2 hcardE)
  refine (lemma_3_1 (K := K) (R := R) hKne hRne hKnorm hKR).2 ?_
  intro x hxne
  apply le_bot_iff.mp
  intro y hy
  have hxE : (((x : R) : S) : G) ∈ E := by
    change ((x : R) : S) ∈ E.subgroupOf S
    exact x.2
  have hxneG : (((x : R) : S) : G) ≠ 1 := by
    intro hx1
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    exact hx1
  have hyσG : (y : G) ∈ section10Msigma M := by
    simpa [K, S, Subgroup.mem_subgroupOf] using hy.1
  have hyC : (y : G) ∈
      Subgroup.centralizer ({(((x : R) : S) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz_eq : z = (((x : R) : S) : G) := by simpa using hz
    subst z
    exact (congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2)).symm
  have hyCx : (y : G) ∈
      elementCentralizerIn (section10Msigma M) (((x : R) : S) : G) :=
    ⟨hyσG, hyC⟩
  have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
    simpa [hcentE (((x : R) : S) : G) hxE hxneG] using hyCx
  simpa using hybot

private theorem CFSG.section12_frobeniusJoinWithKernel_of_trivial_centralizers_subgroup
    {M E R : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hcomp : section12ComplementToMsigma M E)
    (hRle : R ≤ E) (hRne : R ≠ ⊥)
    (hcentR :
      ∀ r : G, r ∈ R → r ≠ 1 →
        elementCentralizerIn (section10Msigma M) r = ⊥) :
    section12FrobeniusJoinWithKernel (section10Msigma M) R := by
  classical
  let S : Subgroup G := section10Msigma M ⊔ R
  let K : Subgroup S := (section10Msigma M).subgroupOf S
  let L : Subgroup S := R.subgroupOf S
  have hSleM : S ≤ M := by
    exact sup_le hcomp.1 (hRle.trans hcomp.2.1)
  have hKnorm : K.Normal := by
    dsimp [K, S]
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left]
    exact hSleM.trans section12_le_normalizer_msigma
  have hcompS : section12ComplementIn S (section10Msigma M) R := by
    refine ⟨le_sup_left, le_sup_right, rfl, ?_⟩
    exact hcomp.2.2.2.mono_right hRle
  have hKnormS : section10NormalIn (section10Msigma M) S := ⟨le_sup_left, hKnorm⟩
  have hKL : K.IsComplement' L := by
    exact
      (section12_complementIn_of_normal_isComplement'
        (G := G) (H := S) (K := section10Msigma M) (L := R) hcompS hKnormS).symm
  have hKne : K ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card K = 1 :=
      (Subgroup.eq_bot_iff_card (H := K)).1 hbot
    have hcardσ : Nat.card (section10Msigma M) = 1 := by
      dsimp [K, S] at hcard
      rw [section12_card_subgroupOf_eq (H := section10Msigma M)
        (K := section10Msigma M ⊔ R) le_sup_left] at hcard
      exact hcard
    exact (theorem_10_2_e (M := M) hM)
      ((Subgroup.eq_bot_iff_card (H := section10Msigma M)).2 hcardσ)
  have hLne : L ≠ ⊥ := by
    intro hbot
    have hcard : Nat.card L = 1 :=
      (Subgroup.eq_bot_iff_card (H := L)).1 hbot
    have hcardR : Nat.card R = 1 := by
      dsimp [L, S] at hcard
      rw [section12_card_subgroupOf_eq (H := R) (K := section10Msigma M ⊔ R)
        le_sup_right] at hcard
      exact hcard
    exact hRne ((Subgroup.eq_bot_iff_card (H := R)).2 hcardR)
  refine (lemma_3_1 (K := K) (R := L) hKne hLne hKnorm hKL).2 ?_
  intro x hxne
  apply le_bot_iff.mp
  intro y hy
  have hxR : (((x : L) : S) : G) ∈ R := by
    change ((x : L) : S) ∈ R.subgroupOf S
    exact x.2
  have hxneG : (((x : L) : S) : G) ≠ 1 := by
    intro hx1
    apply hxne
    apply Subtype.ext
    apply Subtype.ext
    exact hx1
  have hyσG : (y : G) ∈ section10Msigma M := by
    simpa [K, S, Subgroup.mem_subgroupOf] using hy.1
  have hyC : (y : G) ∈
      Subgroup.centralizer ({(((x : L) : S) : G)} : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz_eq : z = (((x : L) : S) : G) := by simpa using hz
    subst z
    exact (congrArg Subtype.val
      (Subgroup.mem_centralizer_singleton_iff.mp hy.2)).symm
  have hyCx : (y : G) ∈
      elementCentralizerIn (section10Msigma M) (((x : L) : S) : G) :=
    ⟨hyσG, hyC⟩
  have hybot : (y : G) ∈ (⊥ : Subgroup G) := by
    simpa [hcentR (((x : L) : S) : G) hxR hxneG] using hyCx
  simpa using hybot

private theorem CFSG.section12_all_tau2_sylow_comm_of_one
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hpab : ¬ section12HasNonabelianSylowSubgroup p G) :
    ∀ q : Nat.Primes, q ∈ section12Tau2Primes M →
      ¬ section12HasNonabelianSylowSubgroup q G := by
  intro q hq hqnonab
  have hτ2q : section12Tau2Primes M = {q} :=
    theorem_12_7_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hq
      (section12_exists_rankTwo_in_E_of_tau2 hM hE hq).choose_spec
      hqnonab
  have hp_single : p ∈ ({q} : Set Nat.Primes) := by
    simpa [hτ2q] using hp
  have hp_eq_q : p = q := by simpa using hp_single
  exact hpab (hp_eq_q ▸ hqnonab)

private theorem CFSG.section12_tau2_sylow_omegaOne_eq_rankTwo_of_abelian
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    (S : Subgroup G) ≤ E ∧
      section12OmegaOneSubgroup p (S : Subgroup G) = A ∧
      ¬ Subgroup.normalizer ((S : Subgroup G) : Set G) ≤ M := by
  have hC_le_E : Subgroup.centralizer (A : Set G) ≤ E := by
    have h6 :=
      corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
        hM hE hp hA
    intro x hx
    simpa [h6.2.1] using h6.1 hx
  have hSleE : (S : Subgroup G) ≤ E := by
    intro s hs
    exact hC_le_E (by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (setLike_mul_comm
        (s := (S : Subgroup G)) hs (hAS ha)).symm)
  have hSleM : (S : Subgroup G) ≤ M := hSleE.trans hE.1.2.1
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  let SM : Sylow p.val M := S.subtype hSleM
  have hSM_eq_S : section10AmbientSylowSubgroup M SM = (S : Subgroup G) := by
    simpa [SM, section10AmbientSylowSubgroup] using
      (Subgroup.map_subgroupOf_eq_of_le (G := G) (H := (S : Subgroup G)) (K := M)
        hSleM)
  have hA_le_SM : A ≤ section10AmbientSylowSubgroup M SM := by
    simpa [hSM_eq_S] using hAS
  rcases (theorem_12_5_b (G := G) (M := M) (A := A) (p := p) hM hp hA_M).2 SM hA_le_SM with
    ⟨hOmegaS, hNormS_not⟩
  refine ⟨hSleE, ?_, ?_⟩
  · simpa [hSM_eq_S] using hOmegaS
  · simpa [hSM_eq_S] using hNormS_not

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_powMonoidHom_range_characteristic
    {H : Type*} [CommGroup H] (d : Nat) :
    ((powMonoidHom d : H →* H).range).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  intro e
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    rcases MonoidHom.mem_range.mp hy with ⟨z, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨e z, by simp [powMonoidHom_apply]⟩
  · intro hx
    rcases MonoidHom.mem_range.mp hx with ⟨y, rfl⟩
    refine Subgroup.mem_map.mpr ⟨(e.symm y) ^ d, ?_, ?_⟩
    · exact MonoidHom.mem_range.mpr ⟨e.symm y, rfl⟩
    · simp [powMonoidHom_apply]

omit [IsMinCE G] in
private theorem CFSG.section12_primeOrderSubgroupIn_of_ne_bot_ne_self_of_rankTwo
    {A X : Subgroup G} {p : Nat.Primes}
    (hAcard : Nat.card A = p.val ^ 2)
    (hXA : X ≤ A) (hXne : X ≠ ⊥) (hXproper : X ≠ A) :
    X ∈ section10PrimeOrderSubgroupsIn p A := by
  have hXdvd : Nat.card X ∣ p.val ^ 2 := by
    exact (Subgroup.card_dvd_of_le hXA).trans (dvd_rfl.trans (by rw [hAcard]))
  rcases (Nat.dvd_prime_pow p.2).1 hXdvd with ⟨k, hk_le, hk_card⟩
  have hk_ne_zero : k ≠ 0 := by
    intro hk0
    apply hXne
    apply (Subgroup.card_eq_one (H := X)).mp
    simp [hk_card, hk0]
  have hk_ne_two : k ≠ 2 := by
    intro hk2
    have hXsub_card : Nat.card (X.subgroupOf A) = Nat.card A := by
      rw [section12_card_subgroupOf_eq hXA, hAcard, hk_card, hk2]
    have hXsub_top : X.subgroupOf A = ⊤ :=
      Subgroup.eq_top_of_card_eq (H := X.subgroupOf A) hXsub_card
    have hXeqA : X = A := by
      apply le_antisymm hXA
      intro a ha
      have haSub : (⟨a, ha⟩ : A) ∈ X.subgroupOf A := by
        simp [hXsub_top]
      simpa [Subgroup.mem_subgroupOf] using haSub
    exact hXproper hXeqA
  have hk_eq_one : k = 1 := by
    omega
  exact ⟨hXA, by simp [hk_card, hk_eq_one]⟩

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_zpowers_mem_primeOrderSubgroupsIn_of_pow_eq_one
    {B : Subgroup G} {p : Nat.Primes} {x : G}
    (hxB : x ∈ B) (hxpow : x ^ p.val = 1) (hxne : x ≠ 1) :
    Subgroup.zpowers x ∈ section10PrimeOrderSubgroupsIn p B := by
  have : Fact p.val.Prime := ⟨p.2⟩
  have hcard : Nat.card (Subgroup.zpowers x) = p.val := by
    rw [Nat.card_zpowers, orderOf_eq_prime hxpow hxne]
  exact ⟨Subgroup.zpowers_le.2 hxB, hcard⟩

omit [IsMinCE G] in
private theorem CFSG.section12_eq_of_le_primeOrderSubgroupsIn
    {A X Y : Subgroup G} {p : Nat.Primes}
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A)
    (hY : Y ∈ section10PrimeOrderSubgroupsIn p A)
    (hXY : X ≤ Y) :
    X = Y := by
  have hXsub_card : Nat.card (X.subgroupOf Y) = Nat.card Y := by
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hX) with ⟨_hXA, hXcard⟩
    rcases (by simpa [section10PrimeOrderSubgroupsIn] using hY) with ⟨_hYA, hYcard⟩
    rw [section12_card_subgroupOf_eq hXY, hXcard, hYcard]
  have hXsub_top : X.subgroupOf Y = ⊤ :=
    Subgroup.eq_top_of_card_eq (H := X.subgroupOf Y) hXsub_card
  apply le_antisymm hXY
  intro y hy
  have hySub : (⟨y, hy⟩ : Y) ∈ X.subgroupOf Y := by
    simp [hXsub_top]
  simpa [Subgroup.mem_subgroupOf] using hySub

private theorem CFSG.section12_tau2_sylow_le_E2_of_abelian
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    (S : Subgroup G) ≤ E₂ := by
  rcases section12_tau2_sylow_omegaOne_eq_rankTwo_of_abelian
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm with
    ⟨hSleE, _hOmegaS, _hNormS_not⟩
  have h8a :=
    lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have hE2norm : section10NormalIn E₂ E := h8a.2
  have hE2HallIn :
      section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨_hE2E, hHallE2E⟩
  have hSπsingleton : IsPiSubgroup (G := G) ({p} : Set Nat.Primes) (S : Subgroup G) :=
    section8_isPiSubgroup_singleton_of_isPGroup S.isPGroup'
  have hSπ : IsPiSubgroup (G := G) (section12Tau2Primes M) (S : Subgroup G) := by
    intro q hqS
    have hqsingleton : q ∈ ({p} : Set Nat.Primes) := hSπsingleton q hqS
    have hqp : q = p := by simpa using hqsingleton
    simpa [hqp] using hp
  have hSsubπ : IsPiSubgroup (G := E) (section12Tau2Primes M) ((S : Subgroup G).subgroupOf E) :=
    section12_isPiSubgroup_subgroupOf hSπ hSleE
  have : (E₂.subgroupOf E).Normal := hE2norm.2
  have hSsub_le_E2sub :
      (S : Subgroup G).subgroupOf E ≤ E₂.subgroupOf E :=
    section12_piSubgroup_le_normal_hall
      (H := E₂.subgroupOf E) (A := (S : Subgroup G).subgroupOf E)
      hHallE2E hSsubπ
  intro x hxS
  have hxSub : (⟨x, hSleE hxS⟩ : E) ∈ (S : Subgroup G).subgroupOf E := by
    simpa [Subgroup.mem_subgroupOf]
  have hxE2Sub : (⟨x, hSleE hxS⟩ : E) ∈ E₂.subgroupOf E :=
    hSsub_le_E2sub hxSub
  simpa [Subgroup.mem_subgroupOf] using hxE2Sub

private theorem CFSG.section12_exists_tau2_cyclic_factor_of_abelian_sylow_of_theorem_12_12_b
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    ∃ Z : Subgroup G, Z ≤ (S : Subgroup G) ∧ IsCyclic Z ∧
      Monoid.exponent Z = Monoid.exponent (S : Subgroup G) ∧
      subgroupCentralizerIn (section10Msigma M) (section12OmegaOneSubgroup p Z) = ⊥ := by
  classical
  let Ssub : Subgroup G := (S : Subgroup G)
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  rcases section12_tau2_sylow_omegaOne_eq_rankTwo_of_abelian
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm with
    ⟨hSleE, hOmegaS, hNormS_not⟩
  have hAne : A ≠ ⊥ := section12_rankTwo_ne_bot hA
  have hSne : Ssub ≠ ⊥ := by
    intro hSbot
    have hOmegaBot : section12OmegaOneSubgroup p Ssub = ⊥ := by
      rw [hSbot]
      apply le_antisymm
      · intro x hx
        rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
        simp
      · exact bot_le
    have hAbot : A = ⊥ := hOmegaS.symm.trans hOmegaBot
    exact hAne hAbot
  have : Nontrivial Ssub := (Subgroup.nontrivial_iff_ne_bot (H := Ssub)).2 hSne
  have : Fact p.val.Prime := ⟨p.2⟩
  have hSp : IsPGroup p.val Ssub := S.isPGroup'
  let : CommGroup Ssub := IsMulCommutative.instCommGroup
  rcases (IsPGroup.nontrivial_iff_card (p := p.val) (G := Ssub) (hG := hSp)).mp inferInstance with
    ⟨n, hn_pos, hcardS⟩
  have hexp_dvd_card : Monoid.exponent Ssub ∣ p.val ^ n := by
    simpa [hcardS] using (Group.exponent_dvd_nat_card (G := Ssub))
  rcases (Nat.dvd_prime_pow p.2).1 hexp_dvd_card with ⟨k, hk_le, hExpS⟩
  have hExpS_ne_one : Monoid.exponent Ssub ≠ 1 := by
    intro hExp1
    have hsub : Subsingleton Ssub := (Monoid.exp_eq_one_iff).1 hExp1
    let : Subsingleton Ssub := hsub
    have hcard1 : Nat.card Ssub = 1 := by simp
    exact hSne ((Subgroup.eq_bot_iff_card (H := Ssub)).2
      hcard1)
  have hk_pos : 0 < k := by
    cases k with
    | zero =>
        exfalso
        exact hExpS_ne_one (by simp [hExpS])
    | succ k =>
        exact Nat.succ_pos _
  let d : Nat := p.val ^ (k - 1)
  let Isub : Subgroup Ssub := (powMonoidHom d : Ssub →* Ssub).range
  let I : Subgroup G := Isub.map Ssub.subtype
  have hI_le_A : I ≤ A := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hyI, rfl⟩
    rcases MonoidHom.mem_range.mp hyI with ⟨z, rfl⟩
    have hzpow : ((z : Ssub) ^ d : G) ^ p.val = 1 := by
      have hpow : (z : Ssub) ^ (d * p.val) = 1 := by
        have hExp_dvd : Monoid.exponent Ssub ∣ d * p.val := by
          change Monoid.exponent Ssub ∣ p.val ^ (k - 1) * p.val
          refine ⟨1, ?_⟩
          rw [hExpS]
          cases k with
          | zero =>
              cases (Nat.not_lt_zero _ hk_pos)
          | succ k =>
              simp [pow_succ', Nat.mul_comm]
        exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExp_dvd z
      simpa [d, pow_mul] using congrArg Subtype.val hpow
    have hxOmega : ((z : Ssub) ^ d : G) ∈ section12OmegaOneSubgroup p Ssub :=
      section12_mem_omegaOneSubgroup_of_mem_pow_eq_one
        (G := G) (H := Ssub) (p := p) (x := ((z : Ssub) ^ d : G))
        (by exact ((z : Ssub) ^ d).property) hzpow
    simpa [I, Isub, Ssub, powMonoidHom_apply, hOmegaS] using hxOmega
  obtain ⟨t, htord⟩ :=
    Monoid.exists_orderOf_eq_exponent (G := Ssub) Monoid.ExponentExists.of_finite
  have htpow_ne : (t : Ssub) ^ d ≠ 1 := by
    have hd_lt : d < orderOf t := by
      change p.val ^ (k - 1) < orderOf t
      rw [htord, hExpS]
      cases k with
      | zero =>
          cases (Nat.not_lt_zero _ hk_pos)
      | succ k =>
          simpa using Nat.pow_lt_pow_right p.2.one_lt (Nat.pred_lt (Nat.succ_ne_zero k))
    exact pow_ne_one_of_lt_orderOf (pow_ne_zero (k - 1) p.2.ne_zero) hd_lt
  have hIne : I ≠ ⊥ := by
    intro hIbot
    have htbot : Ssub.subtype ((t : Ssub) ^ d) ∈ (⊥ : Subgroup G) := by
      have htI : Ssub.subtype ((t : Ssub) ^ d) ∈ I := by
        refine Subgroup.mem_map.mpr ?_
        refine ⟨(powMonoidHom d) t, ?_, rfl⟩
        exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
      simpa [hIbot] using htI
    exact htpow_ne (by
      apply Subtype.ext
      simpa using htbot)
  have htdpow : (((t : Ssub) ^ d : Ssub) : G) ^ p.val = 1 := by
    have hpow : (t : Ssub) ^ (d * p.val) = 1 := by
      have hExp_dvd : Monoid.exponent Ssub ∣ d * p.val := by
        change Monoid.exponent Ssub ∣ p.val ^ (k - 1) * p.val
        refine ⟨1, ?_⟩
        rw [hExpS]
        cases k with
        | zero =>
            cases (Nat.not_lt_zero _ hk_pos)
        | succ k =>
            simp [pow_succ', Nat.mul_comm]
      exact Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hExp_dvd t
    simpa [d, pow_mul] using congrArg Subtype.val hpow
  have htI : (((t : Ssub) ^ d : Ssub) : G) ∈ I := by
    refine Subgroup.mem_map.mpr ?_
    refine ⟨(powMonoidHom d) t, ?_, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨t, rfl⟩
  rcases section12_rankTwo_elementary hA with ⟨hAcard, _hAelem⟩
  by_cases hIA : I = A
  · obtain ⟨A₁, hA₁prime, hCA₁⟩ :=
      theorem_12_5_f (G := G) (M := M) (A := A) (p := p) hM hp hA_M
    rcases hA₁prime with ⟨hA₁A, hA₁card⟩
    have hA₁prime' : A₁ ∈ section10PrimeOrderSubgroupsIn p A := ⟨hA₁A, hA₁card⟩
    have hA₁ne : A₁ ≠ ⊥ := section12_primeOrder_ne_bot (G := G) hA₁prime'
    rcases Subgroup.ne_bot_iff_exists_ne_one.mp hA₁ne with ⟨aA₁, haA₁ne⟩
    let a : G := aA₁
    have haA₁ : a ∈ A₁ := aA₁.property
    have hane : a ≠ 1 := by
      intro ha1
      exact haA₁ne (Subtype.ext ha1)
    have haI : a ∈ I := by
      simpa [hIA] using hA₁A haA₁
    rcases Subgroup.mem_map.mp haI with ⟨y, hyIsub, hya⟩
    rcases MonoidHom.mem_range.mp hyIsub with ⟨u, hu_pow⟩
    have huda : (((u : Ssub) ^ d : Ssub) : G) = a := by
      calc
        (((u : Ssub) ^ d : Ssub) : G) = (y : G) := by
          simpa [powMonoidHom_apply] using congrArg Subtype.val hu_pow
        _ = a := hya
    let Z : Subgroup G := Subgroup.zpowers (u : G)
    have hZleS : Z ≤ Ssub := Subgroup.zpowers_le.2 u.property
    have hZcyc : IsCyclic Z := by
      dsimp [Z]
      infer_instance
    have huord_dvd : orderOf u ∣ Monoid.exponent Ssub := by
      exact (Monoid.exponent_dvd.mp (dvd_rfl : Monoid.exponent Ssub ∣ Monoid.exponent Ssub)) u
    rcases (Nat.dvd_prime_pow p.2).1 (hExpS ▸ huord_dvd) with ⟨m, hm_le, huord⟩
    have hk_le_m : k ≤ m := by
      by_contra hkm
      have hm_lt_k : m < k := Nat.lt_of_not_ge hkm
      have hudvd : orderOf u ∣ d := by
        rw [huord]
        change p.val ^ m ∣ p.val ^ (k - 1)
        exact Nat.pow_dvd_pow p.val (Nat.le_pred_of_lt hm_lt_k)
      have hu_pow_d_one : (u : Ssub) ^ d = 1 :=
        (orderOf_dvd_iff_pow_eq_one).mp hudvd
      have haone : a = 1 := by
        calc
          a = (((u : Ssub) ^ d : Ssub) : G) := huda.symm
          _ = 1 := by simpa using congrArg Subtype.val hu_pow_d_one
      exact hane haone
    have hm_eq_k : m = k := le_antisymm hm_le hk_le_m
    have huord_eq_exp : orderOf u = Monoid.exponent Ssub := by
      simp [hExpS, huord, hm_eq_k]
    have hZexp : Monoid.exponent Z = Monoid.exponent Ssub := by
      calc
        Monoid.exponent Z = Nat.card Z := hZcyc.exponent_eq_card
        _ = orderOf (u : G) := by
          dsimp [Z]
          rw [Nat.card_zpowers]
        _ = orderOf u := by simp
        _ = Monoid.exponent Ssub := huord_eq_exp
    have hu_ne : (u : G) ≠ 1 := by
      intro hu1
      apply hExpS_ne_one
      rw [← huord_eq_exp, ← Subgroup.orderOf_coe, hu1, orderOf_one]
    have hZne : Z ≠ ⊥ := by
      intro hZbot
      have hu_bot : (u : G) ∈ (⊥ : Subgroup G) := by
        simpa [hZbot, Z] using (Subgroup.mem_zpowers (u : G))
      exact hu_ne (by simpa using hu_bot)
    have hZp : IsPGroup p.val Z := by
      have hZsub_p : IsPGroup p.val (Z.subgroupOf Ssub) := hSp.to_subgroup (Z.subgroupOf Ssub)
      exact hZsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hZleS)
    have hOmegaZ_card : Nat.card (section12OmegaOneSubgroup p Z) = p.val :=
      section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
        (G := G) (H := Z) (p := p) hZp hZcyc hZne
    have haZ : a ∈ Z := by
      rw [← huda]
      dsimp [Z]
      exact Subgroup.mem_zpowers_iff.mpr ⟨d, by simp⟩
    have hapow : a ^ p.val = 1 := by
      have haPowA₁ : (⟨a, haA₁⟩ : A₁) ^ Nat.card A₁ = 1 := pow_card_eq_one'
      simpa [hA₁card] using congrArg Subtype.val haPowA₁
    have haOmegaZ : a ∈ section12OmegaOneSubgroup p Z :=
      section12_mem_omegaOneSubgroup_of_mem_pow_eq_one
        (G := G) (H := Z) (p := p) (x := a) haZ hapow
    have hzaPrime : Subgroup.zpowers a ∈ section10PrimeOrderSubgroupsIn p A₁ :=
      section12_zpowers_mem_primeOrderSubgroupsIn_of_pow_eq_one
        (G := G) (B := A₁) (p := p) haA₁ hapow hane
    have hA₁self : A₁ ∈ section10PrimeOrderSubgroupsIn p A₁ := ⟨le_rfl, hA₁card⟩
    have hza_eq_A₁ : Subgroup.zpowers a = A₁ :=
      section12_eq_of_le_primeOrderSubgroupsIn
        (G := G) (A := A₁) (X := Subgroup.zpowers a) (Y := A₁) (p := p)
        hzaPrime hA₁self (Subgroup.zpowers_le.2 haA₁)
    have hA₁_le_OmegaZ : A₁ ≤ section12OmegaOneSubgroup p Z := by
      rw [← hza_eq_A₁]
      exact Subgroup.zpowers_le.2 haOmegaZ
    have hOmegaZ_le_S : section12OmegaOneSubgroup p Z ≤ Ssub := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨z, hzOmega, rfl⟩
      exact hZleS z.property
    have hOmegaZ_primeS : section12OmegaOneSubgroup p Z ∈ section10PrimeOrderSubgroupsIn p Ssub :=
      ⟨hOmegaZ_le_S, hOmegaZ_card⟩
    have hOmegaZ_le_A : section12OmegaOneSubgroup p Z ≤ A := by
      have hOmegaZ_le_OmegaS :
          section12OmegaOneSubgroup p Z ≤ section12OmegaOneSubgroup p Ssub :=
        section12_primeOrder_le_omegaOneSubgroup_of_le
          (G := G) (H := Ssub) (X := section12OmegaOneSubgroup p Z) hOmegaZ_primeS
      intro x hx
      have hxOmegaS : x ∈ section12OmegaOneSubgroup p Ssub := hOmegaZ_le_OmegaS hx
      rwa [hOmegaS] at hxOmegaS
    have hOmegaZ_primeA : section12OmegaOneSubgroup p Z ∈ section10PrimeOrderSubgroupsIn p A :=
      ⟨hOmegaZ_le_A, hOmegaZ_card⟩
    have hOmegaZ_eq_A₁ : section12OmegaOneSubgroup p Z = A₁ := by
      symm
      exact
        section12_eq_of_le_primeOrderSubgroupsIn
          (G := G) (A := A) (X := A₁) (Y := section12OmegaOneSubgroup p Z) (p := p)
          hA₁prime' hOmegaZ_primeA hA₁_le_OmegaZ
    refine ⟨Z, hZleS, hZcyc, hZexp, ?_⟩
    simpa [hOmegaZ_eq_A₁] using hCA₁
  · have hIprime : I ∈ section10PrimeOrderSubgroupsIn p A :=
      section12_primeOrderSubgroupIn_of_ne_bot_ne_self_of_rankTwo
        (G := G) (A := A) (X := I) (p := p) hAcard hI_le_A hIne hIA
    have hCI : subgroupCentralizerIn (section10Msigma M) I = ⊥ := by
      by_contra hCIne
      have huniq :
          section9MaximalSubgroupsContaining (Subgroup.centralizer (I : Set G)) = {M} :=
        corollary_12_6_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA I hIprime hCIne
      have hNormS_le_NI :
          Subgroup.normalizer (Ssub : Set G) ≤ Subgroup.normalizer (I : Set G) := by
        have : Isub.Characteristic :=
          section12_powMonoidHom_range_characteristic (H := Ssub) d
        simpa [I, Ssub] using
          (section8_normalizer_map_subtype_le_of_characteristic
            (H := Ssub) (K := Isub))
      have hNI_ne_top : Subgroup.normalizer (I : Set G) ≠ ⊤ :=
        section12_normalizer_ne_top_of_ne_bot_ne_top
          (G := G) (Q := I) hIne (section12_primeOrder_ne_top hIprime)
      rcases eq_top_or_exists_le_coatom (Subgroup.normalizer (I : Set G)) with
        htop | ⟨N, hNcoatom, hNle⟩
      · exact hNI_ne_top htop
      have hNmax : N ∈ section9MaximalSubgroups G := hNcoatom
      have hNcont :
          N ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (I : Set G)) := by
        refine ⟨hNmax, ?_⟩
        exact (centralizer_le_normalizer I).trans hNle
      have hN_eq_M : N = M := by
        have hsingle : N ∈ ({M} : Set (Subgroup G)) := by
          simpa [huniq] using hNcont
        simpa using hsingle
      have hNI_le_M : Subgroup.normalizer (I : Set G) ≤ M := by
        simpa [hN_eq_M] using hNle
      exact hNormS_not (hNormS_le_NI.trans hNI_le_M)
    let Z : Subgroup G := Subgroup.zpowers (t : G)
    let T : Subgroup G := Subgroup.zpowers (((t : Ssub) ^ d : Ssub) : G)
    have hZleS : Z ≤ Ssub := Subgroup.zpowers_le.2 t.property
    have hZcyc : IsCyclic Z := by
      dsimp [Z]
      infer_instance
    have hZexp : Monoid.exponent Z = Monoid.exponent Ssub := by
      calc
        Monoid.exponent Z = Nat.card Z := hZcyc.exponent_eq_card
        _ = orderOf (t : G) := by
          dsimp [Z]
          rw [Nat.card_zpowers]
        _ = orderOf t := by simp
        _ = Monoid.exponent Ssub := htord
    have hZne : Z ≠ ⊥ := by
      have htne : (t : G) ≠ 1 := by
        intro ht1
        apply hExpS_ne_one
        rw [← htord, ← Subgroup.orderOf_coe, ht1, orderOf_one]
      intro hZbot
      have htbot : (t : G) ∈ (⊥ : Subgroup G) := by
        simpa [hZbot, Z] using (Subgroup.mem_zpowers (t : G))
      exact htne (by simpa using htbot)
    have hZp : IsPGroup p.val Z := by
      have hZsub_p : IsPGroup p.val (Z.subgroupOf Ssub) := hSp.to_subgroup (Z.subgroupOf Ssub)
      exact hZsub_p.of_equiv (Subgroup.subgroupOfEquivOfLe hZleS)
    have hOmegaZ_card : Nat.card (section12OmegaOneSubgroup p Z) = p.val :=
      section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
        (G := G) (H := Z) (p := p) hZp hZcyc hZne
    have hTprimeI : T ∈ section10PrimeOrderSubgroupsIn p I := by
      have htpow_neG : (((t : Ssub) ^ d : Ssub) : G) ≠ 1 := by
        intro h1
        exact htpow_ne (Subtype.ext h1)
      exact section12_zpowers_mem_primeOrderSubgroupsIn_of_pow_eq_one
        (G := G) (B := I) (p := p) htI htdpow htpow_neG
    have hTZleZ : T ≤ Z := by
      intro x hx
      rcases Subgroup.mem_zpowers_iff.mp hx with ⟨m, rfl⟩
      dsimp [Z]
      refine Subgroup.mem_zpowers_iff.mpr ?_
      refine ⟨m * d, by simpa using (zpow_mul' (t : G) m d)⟩
    have hTprimeZ : T ∈ section10PrimeOrderSubgroupsIn p Z := by
      rcases hTprimeI with ⟨_hTI, hTcard⟩
      exact ⟨hTZleZ, hTcard⟩
    have hTprimeOmegaZ : T ∈ section10PrimeOrderSubgroupsIn p (section12OmegaOneSubgroup p Z) := by
      rcases hTprimeZ with ⟨hTZ, hTcard⟩
      exact ⟨section12_primeOrder_le_omegaOneSubgroup_of_le (G := G) (H := Z) (X := T)
          ⟨hTZ, hTcard⟩,
        hTcard⟩
    have hTI : T = I :=
      section12_eq_of_le_primeOrderSubgroupsIn (G := G) (A := A) (X := T) (Y := I) (p := p)
        (by
          rcases hTprimeI with ⟨hTI, hTcard⟩
          exact ⟨hTI.trans hI_le_A, hTcard⟩)
        hIprime
        (by
          rcases hTprimeI with ⟨hTI, _hTcard⟩
          exact hTI)
    have hTOmegaZ : T = section12OmegaOneSubgroup p Z :=
      section12_eq_of_le_primeOrderSubgroupsIn (G := G) (A := Z)
        (X := T) (Y := section12OmegaOneSubgroup p Z) (p := p)
        (by
          rcases hTprimeI with ⟨hTI, hTcard⟩
          exact ⟨hTZleZ, hTcard⟩)
        (by
          refine ⟨?_, hOmegaZ_card⟩
          intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
          exact y.property)
        (by
          rcases hTprimeOmegaZ with ⟨hTΩ, _hTcard⟩
          exact hTΩ)
    refine ⟨Z, hZleS, hZcyc, hZexp, ?_⟩
    rw [← hTOmegaZ, hTI]
    exact hCI


private theorem CFSG.section12_commutator_eq_bot_of_tau1_primeOrder_trivial_centralizer_abelian_sylow
    {M E E₁₂ E₁ E₂ E₃ A Q : Subgroup G} {p q : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hq : q ∈ section12Tau1Primes M)
    (hQ : Q ∈ section10PrimeOrderSubgroupsIn q E)
    (hCQ : subgroupCentralizerIn (section10Msigma M) Q = ⊥)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    ⁅A, Q⁆ = ⊥ := by
  classical
  have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
    section12_rankTwo_of_EData hE hA
  have hAelem := (section12_rankTwo_elementary hA).2
  by_contra hcomm
  have h_a := corollary_12_9_a hM hE hp hA hq hQ hCQ hcomm
  rcases h_a with ⟨hAQ_prime, hAQ_eq_CMsigma, hAQ_norm_M⟩
  have hAQ_M : ⁅A, Q⁆ ≤ M := hAQ_norm_M.1
  have hAQ_norm := hAQ_norm_M.2
  rcases hE with ⟨hcomp, hE12data_tuple, hE1data_tuple, hE2data, hE3data⟩
  rcases hE12data_tuple with ⟨hE12E, hHallE12⟩
  rcases hE1data_tuple with ⟨hE1E12, hHallE1⟩
  have hE12data :
      section12HallSubgroupIn (section12Tau1Primes M ∪ section12Tau2Primes M) E₁₂ E :=
    ⟨hE12E, hHallE12⟩
  have hE1data : section12HallSubgroupIn (section12Tau1Primes M) E₁ E₁₂ :=
    ⟨hE1E12, hHallE1⟩
  have hE_solv : Group.IsSolvable E := by
    have hEproper : E ≠ ⊤ := by
      intro hEtop
      have htop_le_M : (⊤ : Subgroup G) ≤ M := by
        simpa [hEtop] using hcomp.2.1
      exact hM.1 (top_le_iff.mp htop_le_M)
    exact IsMinCE.proper_subgroups_solvable E (lt_top_iff_ne_top.2 hEproper)
  have : Group.IsSolvable E := hE_solv
  have hE12_solv : Group.IsSolvable E₁₂ :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hE12E)
  have : Group.IsSolvable E₁₂ := hE12_solv
  let π12 : Set Nat.Primes := section12Tau1Primes M ∪ section12Tau2Primes M
  let π1 : Set Nat.Primes := section12Tau1Primes M
  have hQcard : Nat.card Q = q.val := hQ.2
  have hQE : Q ≤ E := hQ.1
  have hQ_pi12 : IsPiSubgroup (G := G) π12 Q := by
    intro r hr
    rw [hQcard] at hr
    have hr_dvd_q : r.val ∣ q.val := hr
    have hr_eq_q_val : r.val = q.val := (Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hr_dvd_q
    have hr_eq_q : r = q := Subtype.ext hr_eq_q_val
    subst hr_eq_q
    exact Set.mem_union_left (section12Tau2Primes M) hq
  let : MulDistribMulAction PUnit.{1} E := {
    smul := fun _ x => x
    one_smul := by intro x; rfl
    mul_smul := by intro a b x; rfl
    smul_mul := by intro a x y; rfl
    smul_one := by intro a; rfl }
  have hcopE : Nat.Coprime (Nat.card PUnit.{1}) (Nat.card E) := by simp
  have hQ_E_pi12 : IsPiSubgroup (G := E) π12 (Q.subgroupOf E) := by
    intro r hr
    have hcard_eq : Nat.card (Q.subgroupOf E) = Nat.card Q :=
      section12_card_subgroupOf_eq hQE
    rw [hcard_eq] at hr
    exact hQ_pi12 r hr
  have hQ_E_inv : IsInvariant PUnit.{1} E (Q.subgroupOf E) :=
    ⟨fun _ _ => ⟨id, id⟩⟩
  rcases proposition_1_5_b hE_solv hcopE π12 (Q.subgroupOf E) hQ_E_pi12 hQ_E_inv with
    ⟨H_E, hH_E_hall, _, hQ_E_le_H⟩
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable hE_solv hH_E_hall hHallE12 with
    ⟨e : E, he⟩
  have hQ_E_conj_le : (Q.subgroupOf E).map (MulAut.conj e).toMonoidHom ≤ E₁₂.subgroupOf E := by
    calc
      (Q.subgroupOf E).map (MulAut.conj e).toMonoidHom ≤
          H_E.map (MulAut.conj e).toMonoidHom := Subgroup.map_mono hQ_E_le_H
      _ = E₁₂.subgroupOf E := by rw [← he]
  let eG : G := (e : E)
  have heG_E : eG ∈ E := (e : E).property
  have hQe_le_E12 : Q.map (MulAut.conj eG).toMonoidHom ≤ E₁₂ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨q0, hq0, rfl⟩
    have hq0E : q0 ∈ E := hQE hq0
    have hq0_E_mem : (⟨q0, hq0E⟩ : E) ∈ Q.subgroupOf E := by
      simpa [Subgroup.mem_subgroupOf] using hq0
    have hconj_mem : (MulAut.conj e) (⟨q0, hq0E⟩ : E) ∈ E₁₂.subgroupOf E :=
      hQ_E_conj_le (Subgroup.mem_map.mpr ⟨⟨q0, hq0E⟩, hq0_E_mem, rfl⟩)
    change (eG * q0 * eG⁻¹ : G) ∈ E₁₂
    change (((e * (⟨q0, hq0E⟩ : E) * e⁻¹ : E) : G) ∈ E₁₂) at hconj_mem
    exact hconj_mem
  have hQe_card : Nat.card (Q.map (MulAut.conj eG).toMonoidHom) = q.val := by
    apply (Nat.card_congr ?_).trans hQcard
    exact (Subgroup.equivMapOfInjective
      (f := (MulAut.conj eG).toMonoidHom) Q (MulAut.conj eG).injective).symm.toEquiv
  have hQe_pi1 : IsPiSubgroup (G := G) π1 (Q.map (MulAut.conj eG).toMonoidHom) := by
    intro r hr
    rw [hQe_card] at hr
    have hr_dvd_q : r.val ∣ q.val := hr
    have hr_eq_q_val : r.val = q.val :=
      (Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hr_dvd_q
    have hr_eq_q : r = q := Subtype.ext hr_eq_q_val
    subst hr_eq_q
    exact hq
  let : MulDistribMulAction PUnit.{1} E₁₂ := {
    smul := fun _ x => x
    one_smul := by intro x; rfl
    mul_smul := by intro a b x; rfl
    smul_mul := by intro a x y; rfl
    smul_one := by intro a; rfl }
  have hcopE12 : Nat.Coprime (Nat.card PUnit.{1}) (Nat.card E₁₂) := by simp
  have hQe_E12_pi1 : IsPiSubgroup (G := E₁₂) π1
      ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂) := by
    intro r hr
    have hcard_eq : Nat.card ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂) =
        Nat.card (Q.map (MulAut.conj eG).toMonoidHom) :=
      section12_card_subgroupOf_eq hQe_le_E12
    rw [hcard_eq] at hr
    exact hQe_pi1 r hr
  have hQe_E12_inv : IsInvariant PUnit.{1} E₁₂
      ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂) :=
    ⟨fun _ _ => ⟨id, id⟩⟩
  rcases proposition_1_5_b hE12_solv hcopE12 π1
    ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂) hQe_E12_pi1 hQe_E12_inv with
    ⟨H_E12, hH_E12_hall, _, hQe_E12_le_H⟩
  rcases exists_conj_eq_of_isHallSubgroup_of_solvable hE12_solv hH_E12_hall hHallE1 with
    ⟨f : E₁₂, hf⟩
  have hQe_E12_conj_le :
      ((Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂).map
        (MulAut.conj f).toMonoidHom ≤ E₁.subgroupOf E₁₂ := by
    calc
      _ ≤ H_E12.map (MulAut.conj f).toMonoidHom := Subgroup.map_mono hQe_E12_le_H
      _ = E₁.subgroupOf E₁₂ := by rw [← hf]
  let fG : G := (f : E₁₂)
  have hfG_E12 : fG ∈ E₁₂ := (f : E₁₂).property
  have hfG_E : fG ∈ E := hE12E hfG_E12
  have hQef_le_E1 : (Q.map (MulAut.conj eG).toMonoidHom).map
      (MulAut.conj fG).toMonoidHom ≤ E₁ := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨q0, hq0, rfl⟩
    have hq0_E12 : q0 ∈ E₁₂ := hQe_le_E12 hq0
    have hq0_E12_mem : (⟨q0, hq0_E12⟩ : E₁₂) ∈
        (Q.map (MulAut.conj eG).toMonoidHom).subgroupOf E₁₂ := by
      simpa [Subgroup.mem_subgroupOf] using hq0
    have hconj_mem : (MulAut.conj f) (⟨q0, hq0_E12⟩ : E₁₂) ∈ E₁.subgroupOf E₁₂ :=
      hQe_E12_conj_le (Subgroup.mem_map.mpr ⟨⟨q0, hq0_E12⟩, hq0_E12_mem, rfl⟩)
    change (fG * q0 * fG⁻¹ : G) ∈ E₁
    change (((f * (⟨q0, hq0_E12⟩ : E₁₂) * f⁻¹ : E₁₂) : G) ∈ E₁) at hconj_mem
    exact hconj_mem
  let g : G := fG * eG
  have hg_E : g ∈ E := Subgroup.mul_mem E hfG_E heG_E
  have h_mulAut_comp : ((MulAut.conj fG) * (MulAut.conj eG)).toMonoidHom =
      (MulAut.conj fG).toMonoidHom.comp (MulAut.conj eG).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply, mul_assoc]
  have hQg_le_E1 : Q.map (MulAut.conj g).toMonoidHom ≤ E₁ := by
    calc
      Q.map (MulAut.conj g).toMonoidHom =
          Q.map (MulAut.conj (fG * eG)).toMonoidHom := rfl
      _ = Q.map ((MulAut.conj fG * MulAut.conj eG).toMonoidHom) := by
        rw [map_mul (MulAut.conj) fG eG]
      _ = Q.map ((MulAut.conj fG).toMonoidHom.comp (MulAut.conj eG).toMonoidHom) := by
        rw [h_mulAut_comp]
      _ = (Q.map (MulAut.conj eG).toMonoidHom).map
            (MulAut.conj fG).toMonoidHom := by rw [Subgroup.map_map]
      _ ≤ E₁ := hQef_le_E1
  have hX_in_E1 : Q.map (MulAut.conj g).toMonoidHom ∈ section12PrimeOrderSubgroups E₁ := by
    rw [section12PrimeOrderSubgroups]
    refine ⟨hQg_le_E1, ?_⟩
    refine ⟨q, ?_⟩
    apply (Nat.card_congr ?_).trans hQcard
    exact (Subgroup.equivMapOfInjective
      (f := (MulAut.conj g).toMonoidHom) Q (MulAut.conj g).injective).symm.toEquiv
  have hg_M : g ∈ M := hcomp.2.1 hg_E
  have hMσ_conj (m : G) (hm : m ∈ M) (x : G) (hx : x ∈ section10Msigma M) :
      m * x * m⁻¹ ∈ section10Msigma M := by
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    have h_conj_sub : (⟨m, hm⟩ * y * ⟨m⁻¹, Subgroup.inv_mem M hm⟩) ∈
        section10MsigmaSubgroup M :=
      (section10MsigmaSubgroup_normal M).conj_mem y hy ⟨m, hm⟩
    exact Subgroup.mem_map.mpr
      ⟨⟨m, hm⟩ * y * ⟨m⁻¹, Subgroup.inv_mem M hm⟩, h_conj_sub, by simp⟩
  have hCQ_Qg : subgroupCentralizerIn (section10Msigma M)
      (Q.map (MulAut.conj g).toMonoidHom) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    rcases Subgroup.mem_inf.mp hx with ⟨hxMσ, hxC⟩
    have hx_conj_Mσ : g⁻¹ * x * g ∈ section10Msigma M := by
      have := hMσ_conj g⁻¹ (Subgroup.inv_mem M hg_M) x hxMσ
      simpa [inv_inv] using this
    have hx_conj_cent_Q : g⁻¹ * x * g ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro q0 hq0
      have hmem : g * q0 * g⁻¹ ∈ Q.map (MulAut.conj g).toMonoidHom :=
        Subgroup.mem_map.mpr ⟨q0, hq0, by simp [MulAut.conj_apply, mul_assoc]⟩
      have hxC_comm := (Subgroup.mem_centralizer_iff.mp hxC) (g * q0 * g⁻¹) hmem
      calc
        q0 * (g⁻¹ * x * g) = g⁻¹ * (g * q0 * g⁻¹ * x) * g := by simp [mul_assoc]
        _ = g⁻¹ * ((g * q0 * g⁻¹) * x) * g := by simp [mul_assoc]
        _ = g⁻¹ * (x * (g * q0 * g⁻¹)) * g := by rw [hxC_comm]
        _ = (g⁻¹ * x * g) * q0 := by simp [mul_assoc]
    have h_bot : g⁻¹ * x * g ∈
        section10Msigma M ⊓ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_inf.mpr ⟨hx_conj_Mσ, hx_conj_cent_Q⟩
    have hCQ_expanded : section10Msigma M ⊓ Subgroup.centralizer (Q : Set G) = ⊥ := by
      calc
        section10Msigma M ⊓ Subgroup.centralizer (Q : Set G) =
            subgroupCentralizerIn (section10Msigma M) Q := rfl
        _ = ⊥ := hCQ
    rw [hCQ_expanded] at h_bot
    have h_one : g⁻¹ * x * g = 1 := Subgroup.mem_bot.mp h_bot
    calc
      x = 1 * x * 1 := by simp
      _ = (g * g⁻¹) * x * (g * g⁻¹) := by simp
      _ = g * (g⁻¹ * x * g) * g⁻¹ := by simp [mul_assoc]
      _ = g * 1 * g⁻¹ := by rw [h_one]
      _ = g * g⁻¹ := by simp
      _ = 1 := by simp
  have h_8e :=
    lemma_12_8_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM ⟨hcomp, hE12data, hE1data, hE2data, hE3data⟩ hp hA hAS hScomm
      (Q.map (MulAut.conj g).toMonoidHom) hX_in_E1 hCQ_Qg
  have hAE : A ≤ E := section12_rankTwo_le hA
  have h_A_Qg_bot : ⁅A, Q.map (MulAut.conj g).toMonoidHom⁆ = ⊥ := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro q0 hq0
    rcases Subgroup.mem_map.mp hq0 with ⟨q', hq', rfl⟩
    have hq_center : MulAut.conj g q' ∈ centerIn (G := G) E :=
      h_8e (Subgroup.mem_map.mpr ⟨q', hq', rfl⟩)
    rcases hq_center with ⟨_hq_E, hq_cent⟩
    exact (hq_cent a (hAE ha)).symm
  have hAnorm : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM ⟨hcomp, hE12data, hE1data, hE2data, hE3data⟩ hp hA).1
  have : (A.subgroupOf E).Normal := hAnorm.2
  have hAg_eq_A : A.map (MulAut.conj g).toMonoidHom = A := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨a, ha, rfl⟩
      have haE : a ∈ E := hAE ha
      let aE : E := ⟨a, haE⟩
      have ha_sub : aE ∈ A.subgroupOf E := by
        simpa [aE, Subgroup.mem_subgroupOf] using ha
      have h_conj : (⟨g, hg_E⟩ * aE * ⟨g, hg_E⟩⁻¹) ∈ A.subgroupOf E :=
        hAnorm.2.conj_mem aE ha_sub ⟨g, hg_E⟩
      change (g * a * g⁻¹ : G) ∈ A
      change (((⟨g, hg_E⟩ * aE * ⟨g, hg_E⟩⁻¹ : E) : G) ∈ A) at h_conj
      exact h_conj
    · intro hx
      have hxE : x ∈ E := hAE hx
      let xE : E := ⟨x, hxE⟩
      have hx_sub : xE ∈ A.subgroupOf E := by
        simpa [xE, Subgroup.mem_subgroupOf] using hx
      have h_conj :
          (⟨g⁻¹, Subgroup.inv_mem E hg_E⟩ * xE * ⟨g⁻¹, Subgroup.inv_mem E hg_E⟩⁻¹) ∈
            A.subgroupOf E :=
        hAnorm.2.conj_mem xE hx_sub ⟨g⁻¹, Subgroup.inv_mem E hg_E⟩
      let a' : G := g⁻¹ * x * g
      have ha'_A : a' ∈ A := by
        simpa [a', Subgroup.mem_subgroupOf] using h_conj
      refine Subgroup.mem_map.mpr ⟨a', ha'_A, ?_⟩
      dsimp [MulAut.conj_apply, a']
      simp [mul_assoc]
  have h_comm_conj : ⁅A, Q.map (MulAut.conj g).toMonoidHom⁆ =
      (⁅A, Q⁆).map (MulAut.conj g).toMonoidHom := by
    calc
      ⁅A, Q.map (MulAut.conj g).toMonoidHom⁆ =
          ⁅A.map (MulAut.conj g).toMonoidHom, Q.map (MulAut.conj g).toMonoidHom⁆ := by
            rw [hAg_eq_A]
      _ = (⁅A, Q⁆).map (MulAut.conj g).toMonoidHom := by
            rw [← Subgroup.map_commutator (f := (MulAut.conj g).toMonoidHom) (H₁ := A) (H₂ := Q)]
  have h_AQ_conj_eq : (⁅A, Q⁆).map (MulAut.conj g).toMonoidHom = ⁅A, Q⁆ := by
    ext x
    constructor
    · intro hx
      rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
      let yM : M := ⟨y, hAQ_M hy⟩
      have hy_sub : yM ∈ (⁅A, Q⁆.subgroupOf M) := by
        simpa [yM, Subgroup.mem_subgroupOf] using hy
      have h_conj : (⟨g, hg_M⟩ * yM * ⟨g, hg_M⟩⁻¹) ∈ (⁅A, Q⁆.subgroupOf M) :=
        hAQ_norm.conj_mem yM hy_sub ⟨g, hg_M⟩
      change (g * y * g⁻¹ : G) ∈ ⁅A, Q⁆
      change (((⟨g, hg_M⟩ * yM * ⟨g, hg_M⟩⁻¹ : M) : G) ∈ ⁅A, Q⁆) at h_conj
      exact h_conj
    · intro hx
      have hxM : x ∈ M := hAQ_M hx
      let xM : M := ⟨x, hxM⟩
      have hx_sub : xM ∈ (⁅A, Q⁆.subgroupOf M) := by
        simpa [xM, Subgroup.mem_subgroupOf] using hx
      have h_conj : (⟨g⁻¹, Subgroup.inv_mem M hg_M⟩ * xM *
          ⟨g⁻¹, Subgroup.inv_mem M hg_M⟩⁻¹) ∈ (⁅A, Q⁆.subgroupOf M) :=
        hAQ_norm.conj_mem xM hx_sub ⟨g⁻¹, Subgroup.inv_mem M hg_M⟩
      let y' : G := g⁻¹ * x * g
      have hy'_AQ : y' ∈ ⁅A, Q⁆ := by
        simpa [y', Subgroup.mem_subgroupOf] using h_conj
      refine Subgroup.mem_map.mpr ⟨y', hy'_AQ, ?_⟩
      dsimp [MulAut.conj_apply, y']
      simp [mul_assoc]
  rw [h_comm_conj, h_AQ_conj_eq] at h_A_Qg_bot
  exact hcomm h_A_Qg_bot

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_exists_quotientPrime_of_normal_proper
    {H K : Subgroup G}
    (hKnorm : section10NormalIn K H) (hKne : K ≠ H) :
    ∃ q : Nat.Primes, q ∈ section12QuotientPrimeSet K H := by
  classical
  let Ksub : Subgroup H := K.subgroupOf H
  have hKsub_ne_top : Ksub ≠ ⊤ := by
    intro htop
    apply hKne
    apply le_antisymm hKnorm.1
    intro x hxH
    have hxKsub : (⟨x, hxH⟩ : H) ∈ Ksub := by
      simp [Ksub, htop]
    simpa [Ksub, Subgroup.mem_subgroupOf] using hxKsub
  have hidx_ne_one : Ksub.index ≠ 1 := by
    intro hidx
    exact hKsub_ne_top ((Subgroup.index_eq_one).mp hidx)
  obtain ⟨q, hqprime, hqdiv⟩ := Nat.exists_prime_and_dvd hidx_ne_one
  exact ⟨⟨q, hqprime⟩, ⟨hKnorm.1, hqdiv⟩⟩

omit [IsMinCE G] in
private theorem CFSG.section12_quotientPrime_of_sylow_not_le_normal
    {E K : Subgroup G} {q : Nat.Primes}
    (hKnorm : section10NormalIn K E)
    (Qe : Sylow q.val E)
    (hQe_not_le : ¬ section10AmbientSylowSubgroup E Qe ≤ K) :
    q ∈ section12QuotientPrimeSet K E := by
  classical
  have : Fact q.val.Prime := ⟨q.property⟩
  let Ksub : Subgroup E := K.subgroupOf E
  have : Ksub.Normal := by simpa [Ksub] using hKnorm.2
  by_contra hqQuot
  have hq_not_dvd : ¬ q.val ∣ Ksub.index := by
    intro hqdiv
    exact hqQuot ⟨hKnorm.1, hqdiv⟩
  let PS : Sylow q.val Ksub := Classical.choice (Sylow.nonempty (p := q.val) (G := Ksub))
  let Pmap : Subgroup E := (PS : Subgroup Ksub).map Ksub.subtype
  have hPmap_p : IsPGroup q.val Pmap := by
    exact IsPGroup.map (p := q.val) (H := (PS : Subgroup Ksub)) PS.isPGroup' Ksub.subtype
  have hPmap_not_dvd : ¬ q.val ∣ Pmap.index := by
    have hPS_not_dvd : ¬ q.val ∣ (PS : Subgroup Ksub).index := PS.not_dvd_index
    rw [show Pmap = (PS : Subgroup Ksub).map Ksub.subtype by rfl]
    rw [Subgroup.index_map_subtype (H := Ksub) (K := (PS : Subgroup Ksub))]
    exact Nat.Prime.not_dvd_mul q.property hPS_not_dvd hq_not_dvd
  let P : Sylow q.val E := IsPGroup.toSylow (p := q.val) hPmap_p hPmap_not_dvd
  have hP_le_Ksub : (P : Subgroup E) ≤ Ksub := by
    intro x hx
    have hxPmap : x ∈ Pmap := by simpa [P] using hx
    rcases Subgroup.mem_map.mp hxPmap with ⟨y, hyPS, rfl⟩
    exact y.property
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq E P Qe
  have hQe_le_Ksub : (Qe : Subgroup E) ≤ Ksub := by
    rw [← hg]
    intro x hx
    have hxconj :
        ∃ a, ∃ haE : a ∈ E, (⟨a, haE⟩ : E) ∈ (P : Subgroup E) ∧
          g * (⟨a, haE⟩ : E) * g⁻¹ = x := by
      simpa [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, Subgroup.conjBy,
        Subgroup.mem_map] using hx
    rcases hxconj with ⟨a, haE, haP, rfl⟩
    exact Subgroup.Normal.conj_mem inferInstance _ (hP_le_Ksub haP) g
  have hQE_le_K : section10AmbientSylowSubgroup E Qe ≤ K := by
    intro x hxQ
    rcases Subgroup.mem_map.mp hxQ with ⟨y, hyQe, rfl⟩
    exact hQe_le_Ksub hyQe
  exact hQe_not_le hQE_le_K

omit [Finite G] [IsMinCE G] in
public noncomputable abbrev CFSG.section12_quotientMulDistribMulActionOfTrivial
    {A M : Type*} [Group A] [Finite A] [Group M] [MulDistribMulAction A M]
    {N : Subgroup A} [N.Normal]
    (hNfix : N ≤ actionCentralizerIn (A := A) (G := M) (⊤ : Subgroup A)) :
    MulDistribMulAction (A ⧸ N) M := by
  let φ : A →* MulAut M := MulDistribMulAction.toMulAut A M
  have hNker : N ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext m
    have hfixn : n ∈ fixingSubgroupOf A M (Set.univ : Set M) := (hNfix hn).2
    exact
      (mem_fixingSubgroup_iff (M := A) (s := (Set.univ : Set M))).1 hfixn m
        (by trivial)
  let φq : A ⧸ N →* MulAut M :=
    (QuotientGroup.mk' N).liftOfSurjective (QuotientGroup.mk'_surjective (N := N)) ⟨φ, by
      simpa [QuotientGroup.ker_mk'] using hNker⟩
  exact
    { smul := fun q m => φq q m
      one_smul := by
        intro m
        change (φq 1) m = m
        simp [φq]
      mul_smul := by
        intro a b m
        change (φq (a * b)) m = (φq a) ((φq b) m)
        simp [φq]
      smul_mul := by
        intro a m₁ m₂
        exact (φq a).map_mul m₁ m₂
      smul_one := by
        intro a
        exact (φq a).map_one }

omit [Finite G] [IsMinCE G] in
private theorem CFSG.section12_quotientMulDistribMulActionOfTrivial_smul_mk'
    {A M : Type*} [Group A] [Finite A] [Group M] [MulDistribMulAction A M]
    {N : Subgroup A} [N.Normal]
    (hNfix : N ≤ actionCentralizerIn (A := A) (G := M) (⊤ : Subgroup A))
    (a : A) (m : M) :
    let :
        MulDistribMulAction (A ⧸ N) M :=
      section12_quotientMulDistribMulActionOfTrivial (A := A) (M := M) hNfix
    (QuotientGroup.mk' N a : A ⧸ N) • m = a • m := by
  let φ : A →* MulAut M := MulDistribMulAction.toMulAut A M
  have hNker : N ≤ φ.ker := by
    intro n hn
    rw [MonoidHom.mem_ker]
    ext x
    have hfixn : n ∈ fixingSubgroupOf A M (Set.univ : Set M) := (hNfix hn).2
    exact
      (mem_fixingSubgroup_iff (M := A) (s := (Set.univ : Set M))).1 hfixn x
        (by trivial)
  let φq : A ⧸ N →* MulAut M :=
    (QuotientGroup.mk' N).liftOfSurjective (QuotientGroup.mk'_surjective (N := N)) ⟨φ, by
      simpa [QuotientGroup.ker_mk'] using hNker⟩
  have hcomp : φq.comp (QuotientGroup.mk' N) = φ := by
    simp [φq]
  change φq (QuotientGroup.mk' N a) m = φ a m
  have hqa : φq (QuotientGroup.mk' N a) = φ a := by
    exact congrArg (fun f : A →* MulAut M => f a) hcomp
  simpa [φ] using congrArg (fun f : MulAut M => f m) hqa

omit [Finite G] [IsMinCE G] in
public theorem CFSG.section12_fixedPointSubgroup_map_mk'_eq_of_trivial
    {A M : Type*} [Group A] [Finite A] [Group M] [MulDistribMulAction A M]
    {N B : Subgroup A} [N.Normal]
    (hNfix : N ≤ actionCentralizerIn (A := A) (G := M) (⊤ : Subgroup A)) :
    let :
        MulDistribMulAction (A ⧸ N) M :=
      section12_quotientMulDistribMulActionOfTrivial (A := A) (M := M) hNfix
    fixedPointSubgroup (↥(B.map (QuotientGroup.mk' N))) M = fixedPointSubgroup (↥B) M := by
  let :
      MulDistribMulAction (A ⧸ N) M :=
    section12_quotientMulDistribMulActionOfTrivial (A := A) (M := M) hNfix
  ext m
  constructor
  · intro hm
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hm ⊢
    intro b
    have hmq :
        (⟨QuotientGroup.mk' N (b : A), ⟨(b : A), b.2, rfl⟩⟩ : B.map (QuotientGroup.mk' N)) •
            m = m :=
      hm ⟨QuotientGroup.mk' N (b : A), ⟨(b : A), b.2, rfl⟩⟩
    calc
      (b : A) • m = (⟨QuotientGroup.mk' N (b : A), ⟨(b : A), b.2, rfl⟩⟩ :
          B.map (QuotientGroup.mk' N)) • m := by
            simpa using
              (section12_quotientMulDistribMulActionOfTrivial_smul_mk'
                (A := A) (M := M) hNfix (a := (b : A)) (m := m)).symm
      _ = m := hmq
  · intro hm
    rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hm ⊢
    intro bq
    rcases Subgroup.mem_map.mp bq.2 with ⟨b, hbB, hbq⟩
    have hmb : (b : A) • m = m := hm ⟨b, hbB⟩
    calc
      bq • m = (b : A) • m := by
        change (bq : A ⧸ N) • m = (b : A) • m
        simpa [hbq] using
          (section12_quotientMulDistribMulActionOfTrivial_smul_mk'
            (A := A) (M := M) hNfix (a := b) (m := m))
      _ = m := hmb


omit [IsMinCE G] in
private noncomputable def CFSG.section12_mulEquiv_iSup_of_pairwise_coprime_order
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y, x ∈ H i → y ∈ H j → Commute x y)
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    (∀ i, H i) ≃* ↥(⨆ i, H i) := by
  classical
  let : ∀ i, Fintype ↥(H i) := fun i => Fintype.ofFinite ↥(H i)
  have hcoprime' : Pairwise fun i j => Nat.Coprime (Fintype.card (H i)) (Fintype.card (H j)) := by
    intro i j hij
    simpa [Nat.card_eq_fintype_card] using hcoprime hij
  have hind : iSupIndep H :=
    Subgroup.independent_of_coprime_order hcomm hcoprime'
  let ϕ := Subgroup.noncommPiCoprod (H := H) (hcomm := hcomm)
  have h_range : ϕ.range = ⨆ i, H i :=
    Subgroup.noncommPiCoprod_range (H := H) (hcomm := hcomm)
  have hinj : Function.Injective ϕ :=
    Subgroup.injective_noncommPiCoprod_of_iSupIndep (H := H) (hcomm := hcomm) hind
  let hcod : ∀ a, ϕ a ∈ ⨆ i, H i := by
    intro a
    rw [← h_range]
    exact ⟨a, rfl⟩
  let ϕ' : (∀ i, H i) →* ↥(⨆ i, H i) := ϕ.codRestrict (⨆ i, H i) hcod
  have hinj' : Function.Injective ϕ' :=
    (ϕ.injective_codRestrict (⨆ i, H i) hcod).mpr hinj
  have hsurj' : Function.Surjective ϕ' := by
    intro x
    have hx : x.1 ∈ ϕ.range := by
      rw [h_range]
      exact x.2
    rcases hx with ⟨a, ha⟩
    exact ⟨a, Subtype.ext ha⟩
  exact MulEquiv.ofBijective ϕ' ⟨hinj', hsurj'⟩


omit [IsMinCE G] in
private theorem CFSG.section12_exponent_eq_iSup_of_pairwise_coprime_order
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcomm : Pairwise fun i j => ∀ x y, x ∈ H i → y ∈ H j → Commute x y)
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    Monoid.exponent ↥(⨆ i, H i) = Finset.lcm Finset.univ (fun i => Monoid.exponent (H i)) := by
  classical
  let : ∀ i, Fintype (H i) := fun i => Fintype.ofFinite (H i)
  let e := section12_mulEquiv_iSup_of_pairwise_coprime_order (G := G) H hcomm hcoprime
  calc
    Monoid.exponent ↥(⨆ i, H i) = Monoid.exponent (∀ i, H i) := by
      simpa using (Monoid.exponent_eq_of_mulEquiv e).symm
    _ = Finset.lcm Finset.univ (fun i => Monoid.exponent (H i)) := by
      simpa using (Monoid.exponent_pi (M := fun i => H i))

omit [IsMinCE G] in
private theorem CFSG.section12_isCyclic_pi_of_pairwise_coprime_cyclic
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcyc : ∀ i, IsCyclic (H i))
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    IsCyclic (∀ i, H i) := by
  classical
  let : ∀ i, Fintype (H i) := fun i => Fintype.ofFinite (H i)
  let : ∀ i, CommGroup (H i) := fun i => IsMulCommutative.instCommGroup
  have hexp_coprime :
      Set.Pairwise (↑(Finset.univ : Finset ι)) (Nat.Coprime.onFun fun i => Monoid.exponent (H i)) := by
    intro i hi j hj hij
    change Nat.Coprime (Monoid.exponent (H i)) (Monoid.exponent (H j))
    rw [show Monoid.exponent (H i) = Fintype.card (H i) by
          rw [(hcyc i).exponent_eq_card, Nat.card_eq_fintype_card]]
    rw [show Monoid.exponent (H j) = Fintype.card (H j) by
          rw [(hcyc j).exponent_eq_card, Nat.card_eq_fintype_card]]
    simpa [Nat.card_eq_fintype_card] using hcoprime hij
  rw [IsCyclic.iff_exponent_eq_card]
  rw [Monoid.exponent_pi]
  rw [Nat.card_eq_fintype_card, Fintype.card_pi]
  rw [Finset.lcm_eq_prod hexp_coprime]
  congr with i
  rw [← Nat.card_eq_fintype_card, (hcyc i).exponent_eq_card]

omit [IsMinCE G] in
private theorem CFSG.section12_isCyclic_iSup_of_pairwise_coprime_cyclic
    {ι : Type*} [Fintype ι] [DecidableEq ι] (H : ι → Subgroup G)
    (hcyc : ∀ i, IsCyclic (H i))
    (hcomm : Pairwise fun i j => ∀ x y, x ∈ H i → y ∈ H j → Commute x y)
    (hcoprime : Pairwise fun i j => Nat.Coprime (Nat.card (H i)) (Nat.card (H j))) :
    IsCyclic ↥(⨆ i, H i) := by
  let e := section12_mulEquiv_iSup_of_pairwise_coprime_order (G := G) H hcomm hcoprime
  exact e.isCyclic.mp
    (section12_isCyclic_pi_of_pairwise_coprime_cyclic (G := G) H hcyc hcoprime)

omit [IsMinCE G] in
private lemma CFSG.unique_subgroup_of_prime_order_in_cyclic
    {G : Type*} [Group G] [Finite G] [IsCyclic G]
    {p : ℕ} [Fact p.Prime] (H K : Subgroup G)
    (hH : Nat.card H = p) (hK : Nat.card K = p) : H = K := by
  have hp_prime : Nat.Prime p := Fact.out
  have hp_pos : 0 < p := Nat.Prime.pos hp_prime
  have hp_dvd_cardG : p ∣ Nat.card G := by
    rw [← hH]
    exact Subgroup.card_subgroup_dvd_card H
  obtain ⟨g, hg⟩ := IsCyclic.exists_monoid_generator (α := G)
  have hg_order : orderOf g = Nat.card G := by
    apply orderOf_eq_card_of_forall_mem_zpowers
    intro x
    have hx := hg x
    rcases (Submonoid.mem_powers_iff _ _).mp hx with ⟨k, hk⟩
    rw [← hk]
    exact ⟨(k : ℤ), by simp⟩
  set d := Nat.card G / p with hd_def
  have hd_mul : d * p = Nat.card G := Nat.div_mul_cancel hp_dvd_cardG
  have hd_dvd : d ∣ Nat.card G := by
    rw [← hd_mul]
    exact ⟨p, rfl⟩
  have hd_pos : 0 < d := by
    by_contra hd0
    have hd0' : d = 0 := Nat.eq_zero_of_not_pos hd0
    rw [hd0', zero_mul] at hd_mul
    have hcard_pos : 0 < Nat.card G := Nat.card_pos_iff.mpr ⟨⟨1⟩, inferInstance⟩
    omega
  set g0 := g ^ d with hg0_def
  have hg0_order : orderOf g0 = p := by
    rw [hg0_def, orderOf_pow, hg_order]
    have h_gcd : Nat.gcd (Nat.card G) d = d := Nat.gcd_eq_right hd_dvd
    rw [h_gcd]
    exact Nat.div_eq_of_eq_mul_right hd_pos hd_mul.symm
  let G0 : Subgroup G := Subgroup.zpowers g0
  have hG0_card : Nat.card G0 = p := by
    rw [Nat.card_zpowers, hg0_order]
  have h_eq_G0 (L : Subgroup G) (hL : Nat.card L = p) : L = G0 := by
    have hL_ne_bot : L ≠ ⊥ := by
      intro hbot
      have hcard1 : Nat.card L = 1 := by
        simp [hbot]
      rw [hL] at hcard1; exact hp_prime.ne_one hcard1
    have : Nontrivial L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL_ne_bot
    obtain ⟨h, hh⟩ := IsCyclic.exists_monoid_generator (α := L)
    have hh_order_L : orderOf (h : L) = p := by
      have h_eq : orderOf (h : L) = Nat.card L :=
        orderOf_eq_card_of_forall_mem_zpowers (by
          intro x; have hx := hh x
          rcases ((Submonoid.mem_powers_iff _ _).mp hx) with ⟨n, hn⟩
          rw [← hn]; exact ⟨(n : ℤ), by simp⟩)
      rw [hL] at h_eq; exact h_eq
    have hh_order_G : orderOf (h : G) = p := by
      rw [Subgroup.orderOf_coe (h : L), hh_order_L]
    have hh_mem : (h : G) ∈ Submonoid.powers g := hg (h : G)
    rcases ((Submonoid.mem_powers_iff _ _).mp hh_mem) with ⟨k, hk⟩
    rw [← hk] at hh_order_G; rw [orderOf_pow, hg_order] at hh_order_G
    set gk := Nat.gcd (Nat.card G) k with hgk_def
    have hgk_dvd_N : gk ∣ Nat.card G := Nat.gcd_dvd_left _ _
    have hN_eq_gk_mul_p : Nat.card G = gk * p := by
      calc
        Nat.card G = gk * (Nat.card G / gk) := (Nat.mul_div_cancel' hgk_dvd_N).symm
        _ = gk * p := by rw [hh_order_G]
    have hgk_eq_d : gk = d := by
      have h_eq : gk * p = d * p := by rw [← hN_eq_gk_mul_p, hd_mul]
      apply Nat.eq_of_mul_eq_mul_right hp_pos
      simpa [mul_comm, mul_left_comm, mul_assoc] using h_eq
    have hd_dvd_k : d ∣ k := by rw [← hgk_eq_d]; exact Nat.gcd_dvd_right _ _
    rcases hd_dvd_k with ⟨m, hm⟩
    have h_mem_G0 : (h : G) ∈ G0 := by
      rw [← hk, hm, pow_mul, ← hg0_def]
      exact Subgroup.mem_zpowers_iff.mpr ⟨(m : ℤ), by simp⟩
    have hL_le_G0 : L ≤ G0 := by
      intro x hx
      have hx_mem : (⟨x, hx⟩ : L) ∈ Submonoid.powers (h : L) := hh ⟨x, hx⟩
      rcases ((Submonoid.mem_powers_iff _ _).mp hx_mem) with ⟨n, hn⟩
      have hx_eq : x = (h : G) ^ n := by simpa using congrArg Subtype.val hn.symm
      rw [hx_eq]; exact Subgroup.pow_mem G0 h_mem_G0 n
    apply Subgroup.eq_of_le_of_card_ge hL_le_G0
    rw [hG0_card, hL]
  exact (h_eq_G0 H hH).trans (h_eq_G0 K hK).symm

omit [IsMinCE G] in
private theorem CFSG.section12_all_sylow_comm_of_one
    {p : Nat.Primes} {S : Sylow p.val G}
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    ∀ P : Sylow p.val G, IsMulCommutative (P : Subgroup G) := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  intro P
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G S P
  have hconj_comm :
      IsMulCommutative ((g • S : Sylow p.val G) : Subgroup G) := by
    let : IsMulCommutative (S : Subgroup G) := hScomm
    rw [Sylow.coe_subgroup_smul]
    exact Subgroup.map_isMulCommutative
      (f := (MulAut.conj g).toMonoidHom) (H := (S : Subgroup G))
  rw [← hg]
  exact hconj_comm

private theorem CFSG.section12_tau2_sylow_comm_of_abelian_sylow
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p q : Nat.Primes}
    {S : Sylow p.val G} (Q : Sylow q.val G)
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (_hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (_hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G))
    (hq : q ∈ section12Tau2Primes M) :
    IsMulCommutative (Q : Subgroup G) := by
  have hpab : ¬ section12HasNonabelianSylowSubgroup p G := by
    intro hpnonab
    rcases hpnonab with ⟨P, hPnoncomm⟩
    exact hPnoncomm (section12_all_sylow_comm_of_one (G := G) (p := p) (S := S) hScomm P)
  have hqab :
      ¬ section12HasNonabelianSylowSubgroup q G :=
    section12_all_tau2_sylow_comm_of_one
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (p := p)
      hM hE hp hpab q hq
  by_contra hQnoncomm
  exact hqab ⟨Q, hQnoncomm⟩

private theorem CFSG.section12_E2_global_hall_of_abelian_sylow
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G)) (hScomm : IsMulCommutative (S : Subgroup G)) :
    IsHallSubgroup (section12Tau2Primes M) E₂ := by
  classical
  have : Fact p.val.Prime := ⟨p.2⟩
  have hE2HallIn :
      section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨hE2E, hHallE2E⟩
  refine isHallSubgroup_of (G := G) (section12Tau2Primes M) E₂ ?_ ?_
  · intro q hqcard
    have hqcard_sub : q.val ∣ Nat.card (E₂.subgroupOf E) := by
      simpa [section12_card_subgroupOf_eq hE2E] using hqcard
    exact hHallE2E.p_in_pi_of_p_dvd_card q hqcard_sub
  · intro q hqτ2 hqidx
    have hmul : E₂.relIndex E * E.index = E₂.index :=
      Subgroup.relIndex_mul_index hE2E
    have hprod : q.val ∣ E₂.relIndex E * E.index := by
      simpa [hmul] using hqidx
    rcases q.2.dvd_mul.mp hprod with hqrel | hqEidx
    · exact (hHallE2E.p_in_pi_of_p_dvd_index q
        (by simpa [Subgroup.relIndex] using hqrel)) hqτ2
    · obtain ⟨B, hB⟩ :=
        section12_exists_rankTwo_in_E_of_tau2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) hM hE hqτ2
      have : Fact q.val.Prime := ⟨q.2⟩
      have hBq : IsPGroup q.val B := by
        have hElem := (section12_rankTwo_elementary hB).2
        have : IsElementaryAbelian q.val B := hElem
        exact IsElementaryAbelian.isPGroup q.val B
      obtain ⟨Q, hB_le_Q⟩ :=
        IsPGroup.exists_le_sylow (G := G) (p := q.val) hBq
      have hQcomm : IsMulCommutative (Q : Subgroup G) :=
        section12_tau2_sylow_comm_of_abelian_sylow
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A)
          (p := p) (q := q) (S := S) Q
          hM hE hp hA hAS hScomm hqτ2
      have hQ_le_CB : (Q : Subgroup G) ≤ Subgroup.centralizer (B : Set G) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro b hb
        exact (setLike_mul_comm
          (s := (Q : Subgroup G)) hx (hB_le_Q hb)).symm
      have hCB_le_E : Subgroup.centralizer (B : Set G) ≤ E := by
        have h6B :=
          corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q)
            hM hE hqτ2 hB
        simpa [h6B.2.1] using h6B.1
      have hQ_le_E : (Q : Subgroup G) ≤ E := hQ_le_CB.trans hCB_le_E
      exact Q.not_dvd_index
        (hqEidx.trans (Subgroup.index_dvd_of_le hQ_le_E))

private theorem CFSG.section12_elementCentralizerIn_E_le_E2_of_abelian
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hcent :
      ∀ e : G, e ∈ E → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    ∀ x : G, x ∈ section10Msigma M → x ≠ 1 → elementCentralizerIn E x ≤ E₂ := by
  have h8a :=
    lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have hE2norm : section10NormalIn E₂ E := h8a.2
  have hE2HallIn :
      section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
    section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
  rcases hE2HallIn with ⟨hE2E, hHallE2E⟩
  have : (E₂.subgroupOf E).Normal := hE2norm.2
  intro x hxσ hxne y hy
  let Y : Subgroup G := Subgroup.zpowers y
  have hYle : Y ≤ elementCentralizerIn E x := Subgroup.zpowers_le.2 hy
  have hYleE : Y ≤ E := hYle.trans inf_le_left
  have hYτ2 :
      subgroupPrimeSet Y ⊆ section12Tau2Primes M := by
    intro q hqY
    have hqE : q ∈ subgroupPrimeSet E :=
      section8_subgroupPrimeSet_mono hYleE hqY
    have hqτ :
        q ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪
          section12Tau3Primes M :=
      section12_prime_mem_tau_union_of_mem_E hM hE.1 hqE
    rcases hqτ with hq12 | hq3
    · rcases hq12 with hq1 | hq2
      · exfalso
        have : Fact q.val.Prime := ⟨q.2⟩
        obtain ⟨z0, hz0_order⟩ :=
          exists_prime_orderOf_dvd_card' (G := Y) q.val hqY
        let z : G := z0
        have hzY : z ∈ Y := z0.property
        have hz_order : orderOf z = q.val := by
          simpa [z, Subgroup.orderOf_coe] using hz0_order
        have hzE : z ∈ E := hYleE hzY
        have hzne : z ≠ 1 := by
          intro hz1
          have hq_one : q.val = 1 := by
            rw [← hz_order, hz1, orderOf_one]
          exact q.2.ne_one hq_one
        have hZτ13 :
            subgroupPrimeSet (Subgroup.zpowers z) ⊆
              section12Tau1Primes M ∪ section12Tau3Primes M := by
          intro r hr
          have hrdiv : r.val ∣ Nat.card (Subgroup.zpowers z) := hr
          rw [Nat.card_zpowers, hz_order] at hrdiv
          have hr_eq_q : r = q := by
            exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hrdiv)
          subst r
          exact Or.inl hq1
        have hzCent : z ∈ Subgroup.centralizer ({x} : Set G) :=
          (hYle hzY).2
        have hxCz : x ∈ elementCentralizerIn (section10Msigma M) z := by
          refine ⟨hxσ, ?_⟩
          change x ∈ Subgroup.centralizer ({z} : Set G)
          rw [Subgroup.mem_centralizer_iff]
          intro w hw
          have hwz : w = z := by simpa using hw
          subst w
          exact (Subgroup.mem_centralizer_iff.mp hzCent x (by simp)).symm
        have hxbot : x ∈ (⊥ : Subgroup G) := by
          simpa [show elementCentralizerIn (section10Msigma M) z = ⊥ by
            exact hcent z hzE hzne hZτ13] using hxCz
        exact hxne (by simpa using hxbot)
      · exact hq2
    · exfalso
      have : Fact q.val.Prime := ⟨q.2⟩
      obtain ⟨z0, hz0_order⟩ :=
        exists_prime_orderOf_dvd_card' (G := Y) q.val hqY
      let z : G := z0
      have hzY : z ∈ Y := z0.property
      have hz_order : orderOf z = q.val := by
        simpa [z, Subgroup.orderOf_coe] using hz0_order
      have hzE : z ∈ E := hYleE hzY
      have hzne : z ≠ 1 := by
        intro hz1
        have hq_one : q.val = 1 := by
          rw [← hz_order, hz1, orderOf_one]
        exact q.2.ne_one hq_one
      have hZτ13 :
          subgroupPrimeSet (Subgroup.zpowers z) ⊆
            section12Tau1Primes M ∪ section12Tau3Primes M := by
        intro r hr
        have hrdiv : r.val ∣ Nat.card (Subgroup.zpowers z) := hr
        rw [Nat.card_zpowers, hz_order] at hrdiv
        have hr_eq_q : r = q := by
          exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hrdiv)
        subst r
        exact Or.inr hq3
      have hzCent : z ∈ Subgroup.centralizer ({x} : Set G) :=
        (hYle hzY).2
      have hxCz : x ∈ elementCentralizerIn (section10Msigma M) z := by
        refine ⟨hxσ, ?_⟩
        change x ∈ Subgroup.centralizer ({z} : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro w hw
        have hwz : w = z := by simpa using hw
        subst w
        exact (Subgroup.mem_centralizer_iff.mp hzCent x (by simp)).symm
      have hxbot : x ∈ (⊥ : Subgroup G) := by
        simpa [show elementCentralizerIn (section10Msigma M) z = ⊥ by
          exact hcent z hzE hzne hZτ13] using hxCz
      exact hxne (by simpa using hxbot)
  have hYπ : IsPiSubgroup (G := G) (section12Tau2Primes M) Y :=
    section8_isPiSubgroup_of_subgroupPrimeSet_subset hYτ2
  have hYsubπ : IsPiSubgroup (G := E) (section12Tau2Primes M) (Y.subgroupOf E) :=
    section12_isPiSubgroup_subgroupOf hYπ hYleE
  have hYsub_le_E2sub :
      Y.subgroupOf E ≤ E₂.subgroupOf E :=
    section12_piSubgroup_le_normal_hall
      (H := E₂.subgroupOf E) (A := Y.subgroupOf E) hHallE2E hYsubπ
  have hyYsub : (⟨y, hy.1⟩ : E) ∈ Y.subgroupOf E := by
    simp [Y, Subgroup.mem_subgroupOf]
  have hyE2sub : (⟨y, hy.1⟩ : E) ∈ E₂.subgroupOf E :=
    hYsub_le_E2sub hyYsub
  simpa [Subgroup.mem_subgroupOf] using hyE2sub


private theorem
    section12_exists_tau1_cyclic_sylow_of_noncentral_sylow_centralizer
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G))
    (hCESne : subgroupCentralizerIn E (S : Subgroup G) ≠ E) :
    ∃ q : Nat.Primes, ∃ Qe : Sylow q.val E,
      q ∈ section12Tau1Primes M ∧
      q ∈ section12QuotientPrimeSet (subgroupCentralizerIn E A) E ∧
      ¬ section10AmbientSylowSubgroup E Qe ≤ subgroupCentralizerIn E (S : Subgroup G) ∧
      ¬ section10AmbientSylowSubgroup E Qe ≤ subgroupCentralizerIn E A ∧
      IsCyclic (section10AmbientSylowSubgroup E Qe) := by
  classical
  let Ssub : Subgroup G := (S : Subgroup G)
  let CEA : Subgroup G := subgroupCentralizerIn E A
  let CES : Subgroup G := subgroupCentralizerIn E Ssub
  let QE : ∀ {q : Nat.Primes}, Sylow q.val E → Subgroup G :=
    fun {_q} Qe => section10AmbientSylowSubgroup E Qe
  have : Fact p.val.Prime := ⟨p.2⟩
  have h8a :=
    lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have h8d :=
    lemma_12_8_d (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  rcases section12_tau2_sylow_omegaOne_eq_rankTwo_of_abelian
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm with
    ⟨hSleE, hOmegaS, _hNormS_not⟩
  have hE2normE : section10NormalIn E₂ E := h8a.2
  have hE_le_NE2 : E ≤ Subgroup.normalizer (E₂ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE2normE.1).1 hE2normE.2
  have hE_le_NS : E ≤ Subgroup.normalizer (Ssub : Set G) := by
    change E ≤ Subgroup.normalizer (((S : Subgroup G) : Set G))
    rw [h8d.2.1]
    exact hE_le_NE2
  have hSnormE : section10NormalIn Ssub E := by
    refine ⟨hSleE, ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer hSleE).2 hE_le_NS
  have hCESnorm : section10NormalIn CES E := by
    simpa [CES, Ssub] using
      section12_subgroupCentralizerIn_normal_of_normal
        (G := G) (E := E) (A := Ssub) hSnormE
  obtain ⟨q, hqQuotCES⟩ :=
    section12_exists_quotientPrime_of_normal_proper
      (G := G) (H := E) (K := CES) hCESnorm hCESne
  have : Fact q.val.Prime := ⟨q.2⟩
  let Qe : Sylow q.val E := Classical.choice (Sylow.nonempty (p := q.val) (G := E))
  have hQE_le_E : QE Qe ≤ E := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hQE_p : IsPGroup q.val (QE Qe) := by
    change IsPGroup q.val ((Qe : Subgroup E).map E.subtype)
    exact IsPGroup.map Qe.isPGroup' E.subtype
  have hQE_not_le_CES : ¬ QE Qe ≤ CES := by
    intro hQE_le_CES
    have hQe_le_CESsub : (Qe : Subgroup E) ≤ CES.subgroupOf E := by
      intro x hx
      have hxQE : ((x : E) : G) ∈ QE Qe := Subgroup.mem_map_of_mem E.subtype hx
      have hxCES : ((x : E) : G) ∈ CES := hQE_le_CES hxQE
      simpa [CES, Subgroup.mem_subgroupOf] using hxCES
    rcases hqQuotCES with ⟨_hCESE, hq_dvd_idx⟩
    exact Qe.not_dvd_index (hq_dvd_idx.trans (Subgroup.index_dvd_of_le hQe_le_CESsub))
  have hq_ne_p : q.val ≠ p.val := by
    intro hqp
    have hQE_pp : IsPGroup p.val (QE Qe) := by simpa [hqp] using hQE_p
    have hJoin_p : IsPGroup p.val (Ssub ⊔ QE Qe : Subgroup G) :=
      IsPGroup.to_sup_of_normal_left' S.isPGroup' hQE_pp (hQE_le_E.trans hE_le_NS)
    obtain ⟨T, hJoin_le_T⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hJoin_p
    have hS_le_T : Ssub ≤ (T : Subgroup G) := le_sup_left.trans hJoin_le_T
    have hT_eq_S : (T : Subgroup G) = Ssub := S.is_maximal' T.isPGroup' hS_le_T
    have hQE_le_S : QE Qe ≤ Ssub := by
      have hQE_le_T : QE Qe ≤ (T : Subgroup G) := le_trans le_sup_right hJoin_le_T
      rwa [hT_eq_S] at hQE_le_T
    have hS_le_CES : Ssub ≤ CES := by
      intro s hs
      refine ⟨hSleE hs, ?_⟩
      change s ∈ Subgroup.centralizer (Ssub : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro t ht
      exact
        (setLike_mul_comm
          (s := Ssub) hs ht).symm
    exact hQE_not_le_CES (hQE_le_S.trans hS_le_CES)
  have hcopQE_S : Nat.Coprime (Nat.card (QE Qe)) (Nat.card Ssub) :=
    IsPGroup.coprime_card_of_ne q.val p.val hq_ne_p (QE Qe) Ssub hQE_p S.isPGroup'
  have hQE_not_le_CEA : ¬ QE Qe ≤ CEA := by
    intro hQE_le_CEA
    have hQE_le_NS : QE Qe ≤ Subgroup.normalizer (Ssub : Set G) := hQE_le_E.trans hE_le_NS
    let : Subgroup.Normalizes (QE Qe) Ssub := ⟨hQE_le_NS⟩
    let : IsMulCommutative Ssub := hScomm
    let : CommGroup Ssub := IsMulCommutative.instCommGroup
    have hfix_eq :
        fixedPointSubgroup (↥(QE Qe)) (↥Ssub) =
          (subgroupCentralizerIn Ssub (QE Qe)).subgroupOf Ssub := by
      simpa [Ssub, QE] using
        fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Ssub (QE Qe) hQE_le_NS
    have hfix :
        ∀ s : Ssub, Nat.Prime (orderOf s) → s ∈ fixedPointSubgroup (↥(QE Qe)) (↥Ssub) := by
      intro s hsprime
      rcases section12_rankTwo_elementary hA with ⟨_hAcard, hAelem⟩
      have : IsElementaryAbelian p.val A := hAelem
      have hs_ne : (s : Ssub) ≠ 1 := by
        intro hs1
        exact hsprime.ne_one (by simp [hs1])
      have hs_order_eq_p : orderOf s = p.val := by
        rcases (IsPGroup.iff_orderOf (p := p.val)).mp S.isPGroup' s with ⟨m, hm_eq⟩
        have hp_dvd_order : p.val ∣ orderOf s := by
          cases m with
          | zero =>
              exfalso
              have hs_ord_one : orderOf s = 1 := by simpa using hm_eq
              exact hsprime.ne_one hs_ord_one
          | succ m =>
              rw [hm_eq]
              refine dvd_trans ?_ (dvd_rfl)
              rw [pow_succ']
              exact dvd_mul_right _ _
        exact ((Nat.prime_dvd_prime_iff_eq p.2 hsprime).mp hp_dvd_order).symm
      have hs_order_eq_pG : orderOf (s : G) = p.val := by
        simpa [Subgroup.orderOf_coe] using hs_order_eq_p
      have hs_pow : (s : G) ^ p.val = 1 := by
        exact (orderOf_dvd_iff_pow_eq_one).mp (by rw [hs_order_eq_pG])
      have hsOmegaS : (s : G) ∈ section12OmegaOneSubgroup p Ssub :=
        section12_mem_omegaOneSubgroup_of_mem_pow_eq_one
          (G := G) (H := Ssub) (p := p) (x := (s : G)) s.property hs_pow
      have hsA : (s : G) ∈ A := by simpa [Ssub, hOmegaS] using hsOmegaS
      rw [hfix_eq]
      exact ⟨s.property, by
        change (s : G) ∈ Subgroup.centralizer (QE Qe : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        have hxCentA : x ∈ Subgroup.centralizer (A : Set G) := (hQE_le_CEA hx).2
        exact (Subgroup.mem_centralizer_iff.mp hxCentA (s : G) hsA).symm⟩
    have hsolvS : Group.IsSolvable Ssub := by infer_instance
    have htrivS : ActsTrivially (A := QE Qe) (G := Ssub) :=
      proposition_1_6_e (G := Ssub) (A := QE Qe) hsolvS hcopQE_S hScomm hfix
    have hQE_le_CES' : QE Qe ≤ CES := by
      intro x hx
      refine ⟨hQE_le_E hx, ?_⟩
      change x ∈ Subgroup.centralizer (Ssub : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro s hs
      have hxfix : (⟨x, hx⟩ : QE Qe) • (⟨s, hs⟩ : Ssub) = ⟨s, hs⟩ :=
        htrivS ⟨x, hx⟩ ⟨s, hs⟩
      have hconj : x * s * x⁻¹ = s := by
        simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe, hQE_le_NS, mul_assoc] using
          congrArg Subtype.val hxfix
      simpa [mul_assoc] using (congrArg (fun y : G => y * x) hconj).symm
    exact hQE_not_le_CES hQE_le_CES'
  have hAnormE : section10NormalIn A E :=
    (corollary_12_6_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).1
  have hCEAnorm : section10NormalIn CEA E := by
    simpa [CEA] using
      section12_subgroupCentralizerIn_normal_of_normal
        (G := G) (E := E) (A := A) hAnormE
  have hqQuotCEA : q ∈ section12QuotientPrimeSet CEA E :=
    section12_quotientPrime_of_sylow_not_le_normal
      (G := G) (E := E) (K := CEA) (q := q) hCEAnorm Qe hQE_not_le_CEA
  have hqτ1 : q ∈ section12Tau1Primes M :=
    (corollary_12_10_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).2.2 hqQuotCEA
  have hqrankE_le_one : primeRank q.val E ≤ 1 := by
    let eE : E.subgroupOf M ≃* E := Subgroup.subgroupOfEquivOfLe hE.1.2.1
    have hqrankE_le_Esub : primeRank q.val E ≤ primeRank q.val (E.subgroupOf M) :=
      section12_primeRank_le_of_equiv (R := E.subgroupOf M) (S := E) q.val eE
    have hqrankEsub_le_M : primeRank q.val (E.subgroupOf M) ≤ primeRank q.val M := by
      exact section8_primeRank_le_of_subgroup (G := M) (E.subgroupOf M) q.val
    have hqrankE_le_M : primeRank q.val E ≤ primeRank q.val M :=
      hqrankE_le_Esub.trans hqrankEsub_le_M
    simpa [hqτ1.2.2] using hqrankE_le_M.trans (le_of_eq hqτ1.2.2)
  have hqE_dvd : q.val ∣ Nat.card E := by
    rcases hqQuotCEA with ⟨_hCEAE, hq_dvd_idx⟩
    exact hq_dvd_idx.trans (CEA.subgroupOf E).index_dvd_card
  have hqG_dvd : q.val ∣ Nat.card G :=
    hqE_dvd.trans (Subgroup.card_subgroup_dvd_card E)
  have hq_odd : q.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hqG_dvd
  have hQe_cyc : IsCyclic (Qe : Subgroup E) :=
    section12_sylow_cyclic_of_primeRank_le_one hq_odd hqrankE_le_one Qe
  have hQE_cyc : IsCyclic (QE Qe) := by
    let eQ : (Qe : Subgroup E) ≃* QE Qe :=
      Subgroup.equivMapOfInjective (f := E.subtype) (Qe : Subgroup E) E.subtype_injective
    exact eQ.isCyclic.mp hQe_cyc
  exact ⟨q, Qe, hqτ1, by simpa [CEA] using hqQuotCEA, hQE_not_le_CES, hQE_not_le_CEA, hQE_cyc⟩

private theorem
    section12_tau1_omegaOne_centralizer_data_of_noncentral_sylow_centralizer
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p q : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hcent :
      ∀ e : G, e ∈ E → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G))
    (hqτ1 : q ∈ section12Tau1Primes M)
    (Qe : Sylow q.val E)
    (hQE_not_le_CEA :
      ¬ section10AmbientSylowSubgroup E Qe ≤ subgroupCentralizerIn E A)
    (hQE_cyc : IsCyclic (section10AmbientSylowSubgroup E Qe)) :
    let QE := section10AmbientSylowSubgroup E Qe
    section12OmegaOneSubgroup q QE ≤ subgroupCentralizerIn E A ∧
      q ∈ subgroupPrimeSet (subgroupCentralizerIn E A) := by
  classical
  let QE : Subgroup G := section10AmbientSylowSubgroup E Qe
  have : Fact q.val.Prime := ⟨q.2⟩
  have hQE_le_E : QE ≤ E := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
    exact y.property
  have hQE_p : IsPGroup q.val QE := by
    change IsPGroup q.val ((Qe : Subgroup E).map E.subtype)
    exact IsPGroup.map Qe.isPGroup' E.subtype
  have hQE_ne_bot : QE ≠ ⊥ := by
    intro hQEbot
    apply hQE_not_le_CEA
    intro x hx
    change x ∈ QE at hx
    have hxone : x = 1 := by simpa [hQEbot] using hx
    subst x
    exact Subgroup.one_mem (subgroupCentralizerIn E A)
  let ΩQ : Subgroup G := section12OmegaOneSubgroup q QE
  have hOmegaQ_le_QE : ΩQ ≤ QE := by
    intro x hx
    rcases Subgroup.mem_map.mp hx with ⟨y, hy, rfl⟩
    exact y.property
  have hOmegaQ_card : Nat.card ΩQ = q.val :=
    section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
      (G := G) (H := QE) (p := q) hQE_p hQE_cyc hQE_ne_bot
  obtain ⟨z, hzOmegaQ, hzne, hZprimeOmegaQ⟩ :=
    section12_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := ΩQ) (q := q) (by rw [hOmegaQ_card])
  have hzE : z ∈ E := hQE_le_E (hOmegaQ_le_QE hzOmegaQ)
  have hzTau13 :
      subgroupPrimeSet (Subgroup.zpowers z) ⊆
        section12Tau1Primes M ∪ section12Tau3Primes M := by
    intro r hr
    have hrdiv : r.val ∣ Nat.card (Subgroup.zpowers z) := hr
    rcases hZprimeOmegaQ with ⟨_hZleOmegaQ, hZcard⟩
    rw [hZcard] at hrdiv
    have hr_eq_q : r = q := by
      exact Subtype.ext ((Nat.prime_dvd_prime_iff_eq r.2 q.2).mp hrdiv)
    subst r
    exact Or.inl hqτ1
  have hCOmegaQ_bot :
      subgroupCentralizerIn (section10Msigma M) ΩQ = ⊥ := by
    apply le_bot_iff.mp
    intro x hx
    have hxCentz : x ∈ elementCentralizerIn (section10Msigma M) z := by
      refine ⟨hx.1, ?_⟩
      change x ∈ Subgroup.centralizer ({z} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwz : w = z := by simpa using hw
      subst w
      exact (Subgroup.mem_centralizer_iff.mp hx.2) z hzOmegaQ
    simpa [hcent z hzE hzne hzTau13] using hxCentz
  have hOmegaQ_primeE : ΩQ ∈ section10PrimeOrderSubgroupsIn q E := by
    exact ⟨hOmegaQ_le_QE.trans hQE_le_E, hOmegaQ_card⟩
  have hAQ_bot : ⁅A, ΩQ⁆ = ⊥ :=
    section12_commutator_eq_bot_of_tau1_primeOrder_trivial_centralizer_abelian_sylow
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (Q := ΩQ) (p := p) (q := q) (S := S)
      hM hE hp hA hqτ1 hOmegaQ_primeE hCOmegaQ_bot hAS hScomm
  have hA_le_centOmegaQ : A ≤ Subgroup.centralizer (ΩQ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAQ_bot
  have hOmegaQ_le_centA : ΩQ ≤ Subgroup.centralizer (A : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact ((Subgroup.mem_centralizer_iff.mp (hA_le_centOmegaQ ha)) x hx).symm
  have hOmegaQ_le_CEA : ΩQ ≤ subgroupCentralizerIn E A := by
    intro x hx
    exact ⟨hOmegaQ_le_QE.trans hQE_le_E hx, hOmegaQ_le_centA hx⟩
  have hqCEA : q ∈ subgroupPrimeSet (subgroupCentralizerIn E A) := by
    have hqOmegaQ : q.val ∣ Nat.card ΩQ := by rw [hOmegaQ_card]
    exact hqOmegaQ.trans (Subgroup.card_dvd_of_le hOmegaQ_le_CEA)
  exact ⟨hOmegaQ_le_CEA, hqCEA⟩

private theorem
    section12_subgroupCentralizerIn_primeOrder_eq_bot_of_normalizer_rankTwo
    {M E E₁₂ E₁ E₂ E₃ A X : Subgroup G} {p : Nat.Primes}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hX : X ∈ section10PrimeOrderSubgroupsIn p A)
    (hNormA_le_NormX :
      Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (X : Set G)) :
    subgroupCentralizerIn (section10Msigma M) X = ⊥ := by
  classical
  by_contra hCX
  have hNormA_not_le_M :
      ¬ Subgroup.normalizer (A : Set G) ≤ M :=
    (corollary_12_6_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA).2.2
  have hXne : X ≠ ⊥ := section12_primeOrder_ne_bot (G := G) (A := A) (X := X) (p := p) hX
  have hXtop : X ≠ ⊤ := section12_primeOrder_ne_top (G := G) (A := A) (X := X) (p := p) hX
  have hNX_ne_top : Subgroup.normalizer (X : Set G) ≠ ⊤ :=
    section12_normalizer_ne_top_of_ne_bot_ne_top hXne hXtop
  obtain ⟨Mstar, hMstar⟩ :=
    section9_exists_maximalSubgroupsContaining_of_ne_top (G := G) hNX_ne_top
  have hMstar_ne : Mstar ≠ M := by
    intro hEq
    apply hNormA_not_le_M
    simpa [hEq] using hNormA_le_NormX.trans hMstar.2
  have huniq :
      section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) = {M} :=
    corollary_12_6_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA X hX hCX
  have hMstar_cent :
      Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.centralizer (X : Set G)) := by
    refine ⟨hMstar.1, ?_⟩
    exact (centralizer_le_normalizer X).trans hMstar.2
  have hMstar_eq : Mstar = M := by
    have : Mstar ∈ ({M} : Set (Subgroup G)) := by
      simpa [huniq] using hMstar_cent
    simpa using this
  exact hMstar_ne hMstar_eq

private theorem
    section12_debug_exists_tau2_normal_cyclic_factor_of_abelian
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hcent :
      ∀ e : G, e ∈ E → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    ∃ Z : Subgroup G, Z ≤ (S : Subgroup G) ∧ Z ≤ E₂ ∧ IsCyclic Z ∧
      Monoid.exponent Z = Monoid.exponent (S : Subgroup G) ∧
      E₁ ≤ Subgroup.normalizer (Z : Set G) ∧
      subgroupCentralizerIn (section10Msigma M) (section12OmegaOneSubgroup p Z) = ⊥ := by
  by_cases hCES : subgroupCentralizerIn E (S : Subgroup G) = E
  · rcases section12_tau2_sylow_omegaOne_eq_rankTwo_of_abelian
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm with
      ⟨hSleE, _hOmegaS, _hNormS_not⟩
    have hSleE2 :=
      section12_tau2_sylow_le_E2_of_abelian
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm
    obtain ⟨Z, hZleS, hZcyc, hZexp, hCZ⟩ :=
      section12_exists_tau2_cyclic_factor_of_abelian_sylow_of_theorem_12_12_b
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm
    have hE₁leE : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
    have hE_le_centS : E ≤ Subgroup.centralizer ((S : Subgroup G) : Set G) := by
      intro e heE
      have heCent : e ∈ subgroupCentralizerIn E (S : Subgroup G) := by
        simpa [hCES] using heE
      exact heCent.2
    have hE_le_normZ : E ≤ Subgroup.normalizer (Z : Set G) := by
      refine hE_le_centS.trans ?_
      exact
        (Subgroup.centralizer_le (show (Z : Set G) ⊆ ((S : Subgroup G) : Set G) from hZleS)).trans
          (centralizer_le_normalizer Z)
    exact ⟨Z, hZleS, hZleS.trans hSleE2, hZcyc, hZexp, hE₁leE.trans hE_le_normZ, hCZ⟩
  · obtain ⟨q, Qe, hqτ1, hqQuotCEA, hQE_not_le_CES, hQE_not_le_CEA, hQE_cyc⟩ :=
      section12_exists_tau1_cyclic_sylow_of_noncentral_sylow_centralizer
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm hCES
    let Ssub : Subgroup G := (S : Subgroup G)
    have hA_M : A ∈ section12RankTwoElementaryAbelianIn p M :=
      section12_rankTwo_of_EData hE hA
    rcases section12_tau2_sylow_omegaOne_eq_rankTwo_of_abelian
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm with
      ⟨hSleE, hOmegaS, hNormS_not⟩
    have hA_ne_bot : A ≠ ⊥ := section12_rankTwo_ne_bot hA
    have hS_ne_bot : Ssub ≠ ⊥ := by
      intro hSbot
      have hOmegaBot : section12OmegaOneSubgroup p Ssub = ⊥ := by
        rw [hSbot]
        apply le_antisymm
        · intro x hx
          rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
          simp
        · exact bot_le
      exact hA_ne_bot (hOmegaS.symm.trans hOmegaBot)
    have : Nontrivial Ssub := (Subgroup.nontrivial_iff_ne_bot (H := Ssub)).2 hS_ne_bot
    let QE : Subgroup G := section10AmbientSylowSubgroup E Qe
    have hOmegaData :=
      section12_tau1_omegaOne_centralizer_data_of_noncentral_sylow_centralizer
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (q := q) (S := S)
        hM hE hcent hp hA hAS hScomm hqτ1 Qe hQE_not_le_CEA hQE_cyc
    rcases hOmegaData with ⟨hOmegaQE_le_CEA, hqCEA⟩
    have h8a :=
      lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm
    have hE2normE : section10NormalIn E₂ E := h8a.2
    have h8d :=
      lemma_12_8_d (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm
    have hE_le_NE2 : E ≤ Subgroup.normalizer (E₂ : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hE2normE.1).1 hE2normE.2
    have hE_le_NS : E ≤ Subgroup.normalizer ((S : Subgroup G) : Set G) := by
      rw [h8d.2.1]
      exact hE_le_NE2
    have hQE_le_E : QE ≤ E := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hQE_le_NS : QE ≤ Subgroup.normalizer (Ssub : Set G) :=
      hQE_le_E.trans hE_le_NS
    let N : Subgroup G := Subgroup.normalizer (Ssub : Set G)
    let QEsub : Subgroup N := QE.subgroupOf N
    have hQEsub_p : IsPGroup q.val QEsub := by
      have hQE_p : IsPGroup q.val QE := by
        change IsPGroup q.val ((Qe : Subgroup E).map E.subtype)
        exact IsPGroup.map Qe.isPGroup' E.subtype
      exact hQE_p.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := QE) (K := N) hQE_le_NS).symm
    obtain ⟨Q, hQEsub_le_Q⟩ := IsPGroup.exists_le_sylow (G := N) (p := q.val) hQEsub_p
    let QG : Subgroup G := section10AmbientSylowSubgroup N Q
    have hQE_le_QG : QE ≤ QG := by
      intro x hx
      exact Subgroup.mem_map.mpr
        ⟨⟨x, hQE_le_NS hx⟩,
          hQEsub_le_Q (by simpa [QEsub, Subgroup.mem_subgroupOf] using hx), rfl⟩
    let Q0 : Subgroup G := subgroupCentralizerIn QG Ssub
    have h8c :=
      lemma_12_8_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
        hM hE hp hA hAS hScomm
    have hQG_p : IsPGroup q.val QG := by
      change IsPGroup q.val ((Q : Subgroup N).map N.subtype)
      exact IsPGroup.map Q.isPGroup' N.subtype
    have hQG_le_N : QG ≤ N := by
      intro x hx
      rcases Subgroup.mem_map.mp hx with ⟨y, _hy, rfl⟩
      exact y.property
    have hQ0_le_QG : Q0 ≤ QG := by
      intro x hx
      exact hx.1
    have hQ0_le_centS : Q0 ≤ Subgroup.centralizer (Ssub : Set G) := by
      intro x hx
      exact hx.2
    have hQ0_le_E : Q0 ≤ E := hQ0_le_centS.trans h8c.2.2.2
    have hQ0_le_QG_inf_E : Q0 ≤ QG ⊓ E := by
      exact le_inf hQ0_le_QG hQ0_le_E
    have hQG_inf_E_eq_QE : QG ⊓ E = QE := by
      let QGE : Subgroup E := (QG ⊓ E).subgroupOf E
      have hQGE_p : IsPGroup q.val QGE := by
        let eQGE : QGE ≃* ((QG ⊓ E).subgroupOf QG) :=
          (Subgroup.subgroupOfEquivOfLe (H := QG ⊓ E) (K := E) inf_le_right).trans
            (Subgroup.subgroupOfEquivOfLe (H := QG ⊓ E) (K := QG) inf_le_left).symm
        have hQGEsub_p : IsPGroup q.val ((QG ⊓ E).subgroupOf QG) :=
          hQG_p.to_subgroup ((QG ⊓ E).subgroupOf QG)
        exact hQGEsub_p.of_equiv eQGE.symm
      have hQe_le_QGE : (Qe : Subgroup E) ≤ QGE := by
        intro x hx
        change ((x : E) : G) ∈ QG ⊓ E
        exact ⟨hQE_le_QG (Subgroup.mem_map_of_mem E.subtype hx), x.property⟩
      have hQGE_eq_Qe : QGE = (Qe : Subgroup E) :=
        Qe.is_maximal' hQGE_p hQe_le_QGE
      calc
        QG ⊓ E = QGE.map E.subtype := by
          symm
          simp [QGE]
        _ = (Qe : Subgroup E).map E.subtype := by rw [hQGE_eq_Qe]
        _ = QE := rfl
    have hQ0_le_QE : Q0 ≤ QE := by
      simpa [hQG_inf_E_eq_QE] using hQ0_le_QG_inf_E
    have hQ0_le_CES : Q0 ≤ subgroupCentralizerIn E Ssub := by
      intro x hx
      exact ⟨hQ0_le_E hx, hQ0_le_centS hx⟩
    have hQ0_ne_QE : Q0 ≠ QE := by
      intro hQ0_eq_QE
      exact hQE_not_le_CES (by simpa [Ssub, hQ0_eq_QE] using hQ0_le_CES)
    have hQ0sub_normal : (Q0.subgroupOf QG).Normal := by
      rw [Subgroup.normal_subgroupOf_iff hQ0_le_QG]
      intro x g hxQ0 hgQG
      refine ⟨?_, ?_⟩
      · exact
          (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hgQG) x).1 hxQ0.1
      · change g * x * g⁻¹ ∈ Subgroup.centralizer (Ssub : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro s hs
        have hgN : g ∈ N := hQG_le_N hgQG
        have hginvN : g⁻¹ ∈ N := Subgroup.inv_mem N hgN
        have hginvsg : g⁻¹ * s * g ∈ Ssub := by
          simpa using (Subgroup.mem_normalizer_iff.mp hginvN s).1 hs
        have hcomm :=
          Subgroup.mem_centralizer_iff.mp hxQ0.2 (g⁻¹ * s * g) hginvsg
        have hconj_comm : g * x * g⁻¹ * s = s * (g * x * g⁻¹) := by
          calc
            g * x * g⁻¹ * s = g * (x * (g⁻¹ * s * g)) * g⁻¹ := by group
            _ = g * ((g⁻¹ * s * g) * x) * g⁻¹ := by rw [hcomm]
            _ = s * (g * x * g⁻¹) := by group
        simpa [mul_assoc] using hconj_comm.symm
    let : Subgroup.Normalizes QG Ssub := ⟨hQG_le_N⟩
    have hQ0_fix_all : (Q0.subgroupOf QG) ≤
        actionCentralizerIn (A := ↥QG) (G := ↥Ssub) (⊤ : Subgroup QG) := by
      intro x hx
      rw [actionCentralizerIn]
      constructor
      · simp
      · change x ∈ fixingSubgroupOf (↥QG) (↥Ssub) Set.univ
        rw [mem_fixingSubgroup_iff]
        intro s _
        apply Subtype.ext
        change (x : G) * (s : G) * (x : G)⁻¹ = (s : G)
        have hxcent : (x : G) ∈ Subgroup.centralizer (Ssub : Set G) :=
          hQ0_le_centS (show (x : G) ∈ Q0 by simpa [Q0, Subgroup.mem_subgroupOf] using hx)
        have hcomm := (Subgroup.mem_centralizer_iff.mp hxcent) (s : G) s.property
        calc
          (x : G) * (s : G) * (x : G)⁻¹ = (s : G) * (x : G) * (x : G)⁻¹ := by rw [hcomm]
          _ = (s : G) := by simp
    have hq_ne_p : q.val ≠ p.val := by
      intro hqp
      have hq_rank' : primeRank p.val M = 1 := by
        simpa [hqp] using hqτ1.2.2
      have h1eq2 : (1 : ℕ) = 2 := hq_rank'.symm.trans hp.2
      omega
    let qQG : QG →* QG ⧸ (Q0.subgroupOf QG) := QuotientGroup.mk' (Q0.subgroupOf QG)
    let : MulDistribMulAction (QG ⧸ (Q0.subgroupOf QG)) Ssub :=
      section12_quotientMulDistribMulActionOfTrivial
        (A := ↥QG) (M := ↥Ssub) hQ0_fix_all
    have : Fact q.val.Prime := ⟨q.2⟩
    have : Fact p.val.Prime := ⟨p.2⟩
    have hq_dvd_E : q.val ∣ Nat.card E := by
      rcases hqQuotCEA with ⟨hCEAE, hq_dvd_idx⟩
      exact hq_dvd_idx.trans ((subgroupCentralizerIn E A).subgroupOf E).index_dvd_card
    have hQE_ne_bot : QE ≠ ⊥ := by
      have hQe_ne_bot : (Qe : Subgroup E) ≠ ⊥ :=
        Sylow.ne_bot_of_dvd_card (G := E) (p := q.val) Qe hq_dvd_E
      intro hQEbot
      apply hQe_ne_bot
      exact (Subgroup.map_eq_bot_iff_of_injective
        (H := (Qe : Subgroup E)) (f := E.subtype) E.subtype_injective).mp
        (by simpa [QE, section10AmbientSylowSubgroup] using hQEbot)
    have hQG_ne_bot : QG ≠ ⊥ := by
      intro hQGbot
      exact hQE_ne_bot (by simpa [hQGbot] using hQE_le_QG)
    have hq_dvd_QG : q.val ∣ Nat.card QG := by
      rcases hQG_p.card_eq_or_dvd with hQG_one | hQG_dvd
      · have hQGbot : QG = ⊥ := (Subgroup.card_eq_one (H := QG)).mp hQG_one
        exact False.elim (hQG_ne_bot hQGbot)
      · exact hQG_dvd
    have hcop_QG_Ssub : Nat.Coprime (Nat.card QG) (Nat.card Ssub) :=
      IsPGroup.coprime_card_of_ne q.val p.val hq_ne_p QG Ssub hQG_p (by simpa [Ssub] using S.isPGroup')
    have hcop_q_Ssub : Nat.Coprime q.val (Nat.card Ssub) :=
      Nat.Coprime.of_dvd_left hq_dvd_QG hcop_QG_Ssub
    have hquot_p : IsPGroup q.val (QG ⧸ (Q0.subgroupOf QG)) :=
      hQG_p.to_quotient (Q0.subgroupOf QG)
    have hreg_or_nonreg :
        ActsRegularly (QG ⧸ (Q0.subgroupOf QG)) ↥Ssub ∨
          ¬ ActsRegularly (QG ⧸ (Q0.subgroupOf QG)) ↥Ssub := by
      by_cases hreg : ActsRegularly (QG ⧸ (Q0.subgroupOf QG)) ↥Ssub
      · exact Or.inl hreg
      · exact Or.inr hreg
    rcases hreg_or_nonreg with hreg | hnonreg
    · have hquot_cyc : IsCyclic (QG ⧸ (Q0.subgroupOf QG)) :=
        proposition_3_9 (p := q.val) (H := ↥Ssub)
          (R := QG ⧸ (Q0.subgroupOf QG)) q.2 (by
            have hqG_dvd : q.val ∣ Nat.card G :=
              hq_dvd_E.trans (Subgroup.card_subgroup_dvd_card E)
            have hq_ne_two : q.val ≠ 2 :=
              Odd.ne_two_of_dvd_nat IsMinCE.odd_order hqG_dvd
            exact q.2.odd_of_ne_two hq_ne_two)
          hcop_q_Ssub hquot_p hreg
      have hQE_p : IsPGroup q.val QE := by
        change IsPGroup q.val ((Qe : Subgroup E).map E.subtype)
        exact IsPGroup.map Qe.isPGroup' E.subtype
      let Q0sub : Subgroup QG := Q0.subgroupOf QG
      let QEsubQG : Subgroup QG := QE.subgroupOf QG
      have hQ0sub_le_QEsub : Q0sub ≤ QEsubQG := by
        intro x hx
        change ((x : QG) : G) ∈ QE
        exact hQ0_le_QE (by simpa [Q0sub, Subgroup.mem_subgroupOf] using hx)
      have hQ0sub_ne_QEsub : Q0sub ≠ QEsubQG := by
        intro hsubeq
        apply hQ0_ne_QE
        calc
          Q0 = Q0sub.map QG.subtype := by
            symm
            simpa [Q0sub] using
              (Subgroup.map_subgroupOf_eq_of_le
                (G := G) (H := Q0) (K := QG) hQ0_le_QG)
          _ = QEsubQG.map QG.subtype := by rw [hsubeq]
          _ = QE := by
            simpa [QEsubQG] using
              (Subgroup.map_subgroupOf_eq_of_le
                (G := G) (H := QE) (K := QG) hQE_le_QG)
      have : Q0sub.Normal := by
        simpa [Q0sub] using hQ0sub_normal
      have hpow_mem_QEsub :
          ∀ x : QG, x ^ q.val = 1 → x ∈ QEsubQG :=
        section12_pow_eq_one_mem_of_cyclic_quotient_nontrivial_image
          (R := QG) (p := q) (K := Q0sub) (L := QEsubQG)
          (by simpa [Q0sub] using hquot_p) hquot_cyc
          hQ0sub_le_QEsub hQ0sub_ne_QEsub
      have hOmegaQG_le_OmegaQE :
          section12OmegaOneSubgroup q QG ≤ section12OmegaOneSubgroup q QE :=
        section12_omegaOneSubgroup_le_of_forall_pow_eq_one_mem
          (G := G) (H := QG) (K := QE) (p := q) hQE_le_QG (by
            intro x hx
            have hxQEsub : x ∈ QEsubQG := hpow_mem_QEsub x hx
            simpa [QEsubQG, Subgroup.mem_subgroupOf] using hxQEsub)
      have hOmegaQE_le_OmegaQG :
          section12OmegaOneSubgroup q QE ≤ section12OmegaOneSubgroup q QG :=
        section12_omegaOneSubgroup_mono (G := G) (p := q) hQE_le_QG
      have hOmegaQG_eq :
          section12OmegaOneSubgroup q QG = section12OmegaOneSubgroup q QE :=
        le_antisymm hOmegaQG_le_OmegaQE hOmegaQE_le_OmegaQG
      have hOmegaQE_card :
          Nat.card (section12OmegaOneSubgroup q QE) = q.val :=
        section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
          (G := G) (H := QE) (p := q) hQE_p hQE_cyc hQE_ne_bot
      have hOmegaQG_card :
          Nat.card (section12OmegaOneSubgroup q QG) = q.val := by
        rw [hOmegaQG_eq]
        exact hOmegaQE_card
      have hq_ne_two : q.val ≠ 2 := by
        have hqG_dvd : q.val ∣ Nat.card G :=
          hq_dvd_E.trans (Subgroup.card_subgroup_dvd_card E)
        exact Odd.ne_two_of_dvd_nat IsMinCE.odd_order hqG_dvd
      have hQG_cyc : IsCyclic QG :=
        section12_isCyclic_of_omegaOneSubgroup_card_eq_prime
          (G := G) (H := QG) (p := q) hQG_p hq_ne_two hOmegaQG_card
      have hQ_cyc : IsCyclic (Q : Subgroup N) := by
        let eQ : (Q : Subgroup N) ≃* QG :=
          Subgroup.equivMapOfInjective (f := N.subtype) (Q : Subgroup N)
            N.subtype_injective
        exact eQ.isCyclic.mpr hQG_cyc
      have hNrank_le_one : primeRank q.val N ≤ 1 :=
        section12_primeRank_le_one_of_cyclic_sylow (p := q.val) (R := N) Q hQ_cyc
      have hSsub_le_N : Ssub ≤ N := by
        simpa [N] using (Subgroup.le_normalizer (H := Ssub))
      have hSsub_ne_top : Ssub ≠ ⊤ := by
        intro hStop
        have hSsub_le_M : Ssub ≤ M := by
          simpa [Ssub] using hSleE.trans hE.1.2.1
        have htop_le_M : (⊤ : Subgroup G) ≤ M := by
          simpa [hStop] using hSsub_le_M
        exact hM.1 (top_le_iff.mp htop_le_M)
      have hN_ne_top : N ≠ ⊤ :=
        section12_normalizer_ne_top_of_ne_bot_ne_top hS_ne_bot hSsub_ne_top
      obtain ⟨Mstar, hMstarN⟩ :=
        section9_exists_maximalSubgroupsContaining_of_ne_top (G := G) hN_ne_top
      have hN_le_Mstar : N ≤ Mstar := hMstarN.2
      have hMstarA :
          Mstar ∈ section9MaximalSubgroupsContaining (Subgroup.normalizer (A : Set G)) := by
        refine ⟨hMstarN.1, ?_⟩
        have hNA_le_N : Subgroup.normalizer (A : Set G) ≤ N := by
          simpa [N, Ssub] using (le_of_eq h8d.1)
        exact hNA_le_N.trans hN_le_Mstar
      rcases lemma_12_11_c (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (Mstar := Mstar)
          (p := p) (q := q) hM hE hp hA hMstarA hqQuotCEA hqCEA with
        ⟨hqτ2star, ⟨Pstar, hPstar_norm⟩, _hQstar⟩
      have hSsub_le_Mstar : Ssub ≤ Mstar := hSsub_le_N.trans hN_le_Mstar
      let SMstar : Sylow p.val Mstar := S.subtype (by
        simpa [Ssub] using hSsub_le_Mstar)
      let PMstar : Sylow p.val Mstar := Pstar.subtype hPstar_norm.1
      have hPMstar_normal : (PMstar : Subgroup Mstar).Normal := by
        change ((Pstar : Subgroup G).subgroupOf Mstar).Normal
        exact hPstar_norm.2
      have : Unique (Sylow p.val Mstar) :=
        Sylow.unique_of_normal PMstar hPMstar_normal
      have hSMstar_eq_PMstar : SMstar = PMstar := Subsingleton.elim SMstar PMstar
      have hSMstar_eq_S : section10AmbientSylowSubgroup Mstar SMstar = Ssub := by
        simpa [SMstar, Ssub, section10AmbientSylowSubgroup] using
          (Subgroup.map_subgroupOf_eq_of_le
            (G := G) (H := (S : Subgroup G)) (K := Mstar)
            (by simpa [Ssub] using hSsub_le_Mstar))
      have hPMstar_eq_P : section10AmbientSylowSubgroup Mstar PMstar = (Pstar : Subgroup G) := by
        simpa [PMstar, section10AmbientSylowSubgroup] using
          (Subgroup.map_subgroupOf_eq_of_le
            (G := G) (H := (Pstar : Subgroup G)) (K := Mstar) hPstar_norm.1)
      have hSsub_eq_Pstar : Ssub = (Pstar : Subgroup G) := by
        calc
          Ssub = section10AmbientSylowSubgroup Mstar SMstar := hSMstar_eq_S.symm
          _ = section10AmbientSylowSubgroup Mstar PMstar := by rw [hSMstar_eq_PMstar]
          _ = (Pstar : Subgroup G) := hPMstar_eq_P
      have hMstar_le_N : Mstar ≤ N := by
        have hMstar_le_normP :
            Mstar ≤ Subgroup.normalizer ((Pstar : Subgroup G) : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hPstar_norm.1).1 hPstar_norm.2
        intro x hx
        have hxnormP := hMstar_le_normP hx
        simpa [N, hSsub_eq_Pstar] using hxnormP
      have hMstar_eq_N : Mstar = N := le_antisymm hMstar_le_N hN_le_Mstar
      have hqτ2N : q ∈ section12Tau2Primes N := by
        simpa [hMstar_eq_N] using hqτ2star
      have hNrank_eq_two : primeRank q.val N = 2 := hqτ2N.2
      exact False.elim (by omega)
    ·
      have hnonreg_exists :
          ∃ a : QG ⧸ (Q0.subgroupOf QG), a ≠ 1 ∧
            fixedPointSubgroup (↥(Subgroup.zpowers a)) ↥Ssub ≠ ⊥ := by
        by_contra h
        apply hnonreg
        intro a ha
        by_contra hfix
        exact h ⟨a, ha, hfix⟩
      rcases hnonreg_exists with ⟨abar, habar_ne, hfix_ne⟩
      rcases QuotientGroup.mk'_surjective (N := Q0.subgroupOf QG) abar with ⟨x, rfl⟩
      let XQ : Subgroup QG := Subgroup.zpowers x
      let X : Subgroup G := XQ.map QG.subtype
      have hx_not_Q0 : x ∉ (Q0.subgroupOf QG) := by
        intro hx
        exact habar_ne ((QuotientGroup.eq_one_iff (N := Q0.subgroupOf QG) x).2 hx)
      have hX_le_QG : X ≤ QG := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
        exact z.property
      have hX_le_N : X ≤ N := hX_le_QG.trans hQG_le_N
      have hX_le_normS : X ≤ Subgroup.normalizer (Ssub : Set G) := by
        simpa [N] using hX_le_N
      let C0 : Subgroup G := subgroupCentralizerIn Ssub X
      let : Subgroup.Normalizes X Ssub := ⟨hX_le_normS⟩
      have hfixed_X_eq_C0 :
          fixedPointSubgroup (↥X) ↥Ssub = C0.subgroupOf Ssub := by
        simpa [C0, X, XQ] using
          fixedPointSubgroup_subgroup_conj_eq_subgroupCentralizerIn Ssub X hX_le_normS
      have hfixed_XQ_eq_X :
          fixedPointSubgroup (↥XQ) ↥Ssub = fixedPointSubgroup (↥X) ↥Ssub := by
        ext s
        constructor
        · intro hs
          rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hs ⊢
          intro xg
          rcases Subgroup.mem_map.mp xg.2 with ⟨xq, hxq, hxg⟩
          have hsxq := hs ⟨xq, hxq⟩
          exact Subtype.ext (by
            have hxg_val : (xg : G) = (xq : G) := by simpa using hxg.symm
            simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
              hQG_le_N, hX_le_normS, hxg_val] using congrArg Subtype.val hsxq)
        · intro hs
          rw [fixedPointSubgroup, FixedPoints.mem_subgroup] at hs ⊢
          intro xq
          have hxX : (xq : G) ∈ X := by
            exact Subgroup.mem_map.mpr ⟨xq, xq.2, rfl⟩
          have hsx := hs ⟨(xq : G), hxX⟩
          apply Subtype.ext
          change ((xq : QG) : G) * (s : G) * ((xq : QG) : G)⁻¹ = (s : G)
          simpa [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe,
            hQG_le_N, hX_le_normS] using congrArg Subtype.val hsx
      have hfixed_quot_eq_XQ :
          fixedPointSubgroup (↥(Subgroup.zpowers (QuotientGroup.mk' (Q0.subgroupOf QG) x))) ↥Ssub =
            fixedPointSubgroup (↥XQ) ↥Ssub := by
        have hmap :
            (XQ.map (QuotientGroup.mk' (Q0.subgroupOf QG))) =
              Subgroup.zpowers (QuotientGroup.mk' (Q0.subgroupOf QG) x) := by
          simp [XQ]
        rw [← hmap]
        exact
          section12_fixedPointSubgroup_map_mk'_eq_of_trivial
            (A := ↥QG) (M := ↥Ssub) (N := Q0.subgroupOf QG) (B := XQ)
            hQ0_fix_all
      have hC0_ne_bot : C0 ≠ ⊥ := by
        intro hC0bot
        apply hfix_ne
        calc
          fixedPointSubgroup (↥(Subgroup.zpowers (QuotientGroup.mk' (Q0.subgroupOf QG) x))) ↥Ssub
              = fixedPointSubgroup (↥XQ) ↥Ssub := hfixed_quot_eq_XQ
          _ = fixedPointSubgroup (↥X) ↥Ssub := hfixed_XQ_eq_X
          _ = C0.subgroupOf Ssub := hfixed_X_eq_C0
          _ = ⊥ := by
            simp [C0, hC0bot]
      have hC0_ne_S : C0 ≠ Ssub := by
        intro hC0_eq
        have hx_cent : (x : G) ∈ Subgroup.centralizer (Ssub : Set G) := by
          rw [Subgroup.mem_centralizer_iff]
          intro s hs
          have hsC0 : s ∈ C0 := by
            simpa [hC0_eq] using hs
          have hs_centX : s ∈ Subgroup.centralizer (X : Set G) := hsC0.2
          have hx_mem_X : (x : G) ∈ X := by
            exact Subgroup.mem_map.mpr ⟨x, by simp [XQ], rfl⟩
          exact (Subgroup.mem_centralizer_iff.mp hs_centX (x : G) hx_mem_X).symm
        have hxQ0 : x ∈ (Q0.subgroupOf QG) := by
          change (x : G) ∈ Q0
          exact ⟨x.property, hx_cent⟩
        exact hx_not_Q0 hxQ0
      let C1 : Subgroup G := ⁅Ssub, X⁆
      have hC0_le_S : C0 ≤ Ssub := by
        intro y hy
        exact hy.1
      have hC1_le_S : C1 ≤ Ssub := by
        simpa [C1] using
          section12_commutator_le_left_of_le_normalizer
            (G := G) (K := Ssub) (A := X) hX_le_normS
      have hcomm_map :
          (commutatorAction (A := ↥X) (G := ↥Ssub)).map Ssub.subtype = C1 := by
        simpa [C1] using
          commutatorAction_subgroup_conj_map_eq_commutator Ssub X hX_le_normS
      have hcomm_local_eq :
          commutatorAction (A := ↥X) (G := ↥Ssub) = C1.subgroupOf Ssub := by
        ext s
        constructor
        · intro hs
          change ((s : Ssub) : G) ∈ C1
          have hsmap :
              ((s : Ssub) : G) ∈
                (commutatorAction (A := ↥X) (G := ↥Ssub)).map Ssub.subtype :=
            Subgroup.mem_map_of_mem Ssub.subtype hs
          simpa [hcomm_map] using hsmap
        · intro hs
          have hsC1 : ((s : Ssub) : G) ∈ C1 := by
            simpa [Subgroup.mem_subgroupOf] using hs
          have hsmap :
              ((s : Ssub) : G) ∈
                (commutatorAction (A := ↥X) (G := ↥Ssub)).map Ssub.subtype := by
            simpa [hcomm_map] using hsC1
          rcases Subgroup.mem_map.mp hsmap with ⟨t, ht, hts⟩
          have hts' : t = s := Subtype.ext hts
          simpa [hts'] using ht
      have hX_p : IsPGroup q.val X := by
        have hXsub_p : IsPGroup q.val (X.subgroupOf QG) :=
          hQG_p.to_subgroup (X.subgroupOf QG)
        exact hXsub_p.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := X) (K := QG) hX_le_QG)
      have hS_p : IsPGroup p.val Ssub := by
        simpa [Ssub] using S.isPGroup'
      have hcop_X_S : Nat.Coprime (Nat.card X) (Nat.card Ssub) :=
        IsPGroup.coprime_card_of_ne q.val p.val hq_ne_p X Ssub hX_p hS_p
      let : IsMulCommutative Ssub := hScomm
      let : CommGroup Ssub := IsMulCommutative.instCommGroup
      have hsolvS : Group.IsSolvable Ssub := by infer_instance
      have hcompl_action :
          IsCompl (fixedPointSubgroup (↥X) (↥Ssub))
            (commutatorAction (A := ↥X) (G := ↥Ssub)) :=
        proposition_1_6_d (G := Ssub) (A := X) hsolvS hcop_X_S hScomm
      have hC0s_C1s_disj :
          Disjoint (C0.subgroupOf Ssub) (C1.subgroupOf Ssub) := by
        rw [disjoint_iff]
        simpa [hfixed_X_eq_C0, hcomm_local_eq] using hcompl_action.inf_eq_bot
      have hC0s_C1s_top :
          C0.subgroupOf Ssub ⊔ C1.subgroupOf Ssub = ⊤ := by
        simpa [hfixed_X_eq_C0, hcomm_local_eq] using hcompl_action.sup_eq_top
      have hC0C1_sup : Ssub = C0 ⊔ C1 := by
        apply le_antisymm
        · intro y hyS
          let yS : Ssub := ⟨y, hyS⟩
          have hySub : yS ∈ (C0 ⊔ C1).subgroupOf Ssub := by
            have hyTop : yS ∈ C0.subgroupOf Ssub ⊔ C1.subgroupOf Ssub := by
              simp [hC0s_C1s_top]
            have hsub :
                C0.subgroupOf Ssub ⊔ C1.subgroupOf Ssub =
                  (C0 ⊔ C1).subgroupOf Ssub := by
              exact (Subgroup.subgroupOf_sup
                (A := C0) (A' := C1) (B := Ssub) hC0_le_S hC1_le_S).symm
            simpa [hsub] using hyTop
          simpa [yS, Subgroup.mem_subgroupOf] using hySub
        · exact sup_le hC0_le_S hC1_le_S
      have hC0C1_disj : Disjoint C0 C1 := by
        rw [Subgroup.disjoint_def]
        intro y hyC0 hyC1
        have hyS : y ∈ Ssub := hC0_le_S hyC0
        let yS : Ssub := ⟨y, hyS⟩
        have hyC0s : yS ∈ C0.subgroupOf Ssub := by
          simpa [yS, Subgroup.mem_subgroupOf] using hyC0
        have hyC1s : yS ∈ C1.subgroupOf Ssub := by
          simpa [yS, Subgroup.mem_subgroupOf] using hyC1
        have hybot : yS ∈ (⊥ : Subgroup Ssub) :=
          Subgroup.disjoint_def.mp hC0s_C1s_disj hyC0s hyC1s
        have hyone : yS = 1 := by
          simpa using hybot
        simpa [yS] using congrArg Subtype.val hyone
      have hC0C1_comp : section12ComplementIn Ssub C0 C1 :=
        ⟨hC0_le_S, hC1_le_S, hC0C1_sup, hC0C1_disj⟩
      have hC1_ne_bot : C1 ≠ ⊥ := by
        intro hC1bot
        apply hC0_ne_S
        calc
          C0 = C0 ⊔ ⊥ := by simp
          _ = C0 ⊔ C1 := by rw [hC1bot]
          _ = Ssub := hC0C1_sup.symm
      have h8f :=
        lemma_12_8_f (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
          hM hE hp hA hAS hScomm X hX_le_normS
      have hC0_norm_N : section10NormalIn C0 N := by
        simpa [C0, N, Ssub] using h8f.1
      have hC1_norm_N : section10NormalIn C1 N := by
        simpa [C1, N, Ssub] using h8f.2
      have hC0_p : IsPGroup p.val C0 := by
        have hC0sub_p : IsPGroup p.val (C0.subgroupOf Ssub) :=
          hS_p.to_subgroup (C0.subgroupOf Ssub)
        exact hC0sub_p.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := C0) (K := Ssub) hC0_le_S)
      have hC1_p : IsPGroup p.val C1 := by
        have hC1sub_p : IsPGroup p.val (C1.subgroupOf Ssub) :=
          hS_p.to_subgroup (C1.subgroupOf Ssub)
        exact hC1sub_p.of_equiv
          (Subgroup.subgroupOfEquivOfLe (H := C1) (K := Ssub) hC1_le_S)
      have hprime_exists :
          ∀ {Y : Subgroup G}, IsPGroup p.val Y → Y ≠ ⊥ →
            ∃ W : Subgroup G, W ∈ section10PrimeOrderSubgroupsIn p Y := by
        intro Y hYp hYne
        have hp_dvd_Y : p.val ∣ Nat.card Y := by
          rcases hYp.card_eq_or_dvd with hYone | hYdvd
          · exact False.elim (hYne ((Subgroup.card_eq_one (H := Y)).mp hYone))
          · exact hYdvd
        obtain ⟨z, _hzY, _hzne, hZprime⟩ :=
          section12_exists_primeOrder_zpowers_of_prime_dvd_card
            (G := G) (B := Y) (q := p) hp_dvd_Y
        exact ⟨Subgroup.zpowers z, hZprime⟩
      obtain ⟨X0p, hX0p_C0⟩ := hprime_exists hC0_p hC0_ne_bot
      obtain ⟨X1p, hX1p_C1⟩ := hprime_exists hC1_p hC1_ne_bot
      have hX0p_ne_bot : X0p ≠ ⊥ :=
        section12_primeOrder_ne_bot (G := G) (A := C0) (X := X0p) (p := p) hX0p_C0
      have hX1p_ne_bot : X1p ≠ ⊥ :=
        section12_primeOrder_ne_bot (G := G) (A := C1) (X := X1p) (p := p) hX1p_C1
      have hOmegaC0_le_C0 : section12OmegaOneSubgroup p C0 ≤ C0 := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
        exact z.property
      have hOmegaC1_le_C1 : section12OmegaOneSubgroup p C1 ≤ C1 := by
        intro y hy
        rcases Subgroup.mem_map.mp hy with ⟨z, _hz, rfl⟩
        exact z.property
      have hOmegaC0_le_A : section12OmegaOneSubgroup p C0 ≤ A := by
        have hmono := section12_omegaOneSubgroup_mono
          (G := G) (H := C0) (K := Ssub) (p := p) hC0_le_S
        simpa [Ssub, hOmegaS] using hmono
      have hOmegaC1_le_A : section12OmegaOneSubgroup p C1 ≤ A := by
        have hmono := section12_omegaOneSubgroup_mono
          (G := G) (H := C1) (K := Ssub) (p := p) hC1_le_S
        simpa [Ssub, hOmegaS] using hmono
      have hX0p_le_OmegaC0 : X0p ≤ section12OmegaOneSubgroup p C0 :=
        section12_primeOrder_le_omegaOneSubgroup_of_le
          (G := G) (H := C0) (X := X0p) (p := p) hX0p_C0
      have hX1p_le_OmegaC1 : X1p ≤ section12OmegaOneSubgroup p C1 :=
        section12_primeOrder_le_omegaOneSubgroup_of_le
          (G := G) (H := C1) (X := X1p) (p := p) hX1p_C1
      have hOmegaC0_ne_bot : section12OmegaOneSubgroup p C0 ≠ ⊥ := by
        intro hbot
        apply hX0p_ne_bot
        apply le_bot_iff.mp
        intro y hy
        simpa [hbot] using hX0p_le_OmegaC0 hy
      have hOmegaC1_ne_bot : section12OmegaOneSubgroup p C1 ≠ ⊥ := by
        intro hbot
        apply hX1p_ne_bot
        apply le_bot_iff.mp
        intro y hy
        simpa [hbot] using hX1p_le_OmegaC1 hy
      have hX0p_le_A : X0p ≤ A := hX0p_le_OmegaC0.trans hOmegaC0_le_A
      have hX1p_le_A : X1p ≤ A := hX1p_le_OmegaC1.trans hOmegaC1_le_A
      have hOmegaC0_ne_A : section12OmegaOneSubgroup p C0 ≠ A := by
        intro hOmega_eq
        apply hX1p_ne_bot
        apply le_bot_iff.mp
        intro y hy
        have hyC0 : y ∈ C0 :=
          hOmegaC0_le_C0 (by simpa [hOmega_eq] using hX1p_le_A hy)
        exact Subgroup.disjoint_def.mp hC0C1_disj hyC0 (hX1p_C1.1 hy)
      have hOmegaC1_ne_A : section12OmegaOneSubgroup p C1 ≠ A := by
        intro hOmega_eq
        apply hX0p_ne_bot
        apply le_bot_iff.mp
        intro y hy
        have hyC1 : y ∈ C1 :=
          hOmegaC1_le_C1 (by simpa [hOmega_eq] using hX0p_le_A hy)
        exact Subgroup.disjoint_def.mp hC0C1_disj (hX0p_C0.1 hy) hyC1
      rcases section12_rankTwo_elementary hA with ⟨hAcard, _hAelem⟩
      have hp_dvd_G : p.val ∣ Nat.card G :=
        (section12_rankTwo_prime_mem (G := G) (M := E) (A := A) (p := p) hA).trans
          (Subgroup.card_subgroup_dvd_card E)
      have hp_odd : p.val ≠ 2 := Odd.ne_two_of_dvd_nat IsMinCE.odd_order hp_dvd_G
      have hOmegaC0_prime :
          section12OmegaOneSubgroup p C0 ∈ section10PrimeOrderSubgroupsIn p A :=
        section12_primeOrderSubgroupIn_of_ne_bot_ne_self_of_rankTwo
          (G := G) (A := A) (X := section12OmegaOneSubgroup p C0) (p := p)
          hAcard hOmegaC0_le_A hOmegaC0_ne_bot hOmegaC0_ne_A
      have hOmegaC1_prime :
          section12OmegaOneSubgroup p C1 ∈ section10PrimeOrderSubgroupsIn p A :=
        section12_primeOrderSubgroupIn_of_ne_bot_ne_self_of_rankTwo
          (G := G) (A := A) (X := section12OmegaOneSubgroup p C1) (p := p)
          hAcard hOmegaC1_le_A hOmegaC1_ne_bot hOmegaC1_ne_A
      have hC0_cyc : IsCyclic C0 :=
        section12_isCyclic_of_omegaOneSubgroup_card_eq_prime
          (G := G) (H := C0) (p := p) hC0_p hp_odd hOmegaC0_prime.2
      have hC1_cyc : IsCyclic C1 :=
        section12_isCyclic_of_omegaOneSubgroup_card_eq_prime
          (G := G) (H := C1) (p := p) hC1_p hp_odd hOmegaC1_prime.2
      have hSexp_lcm :
          Monoid.exponent Ssub = Nat.lcm (Monoid.exponent C0) (Monoid.exponent C1) :=
        section12_exponent_eq_lcm_of_complement_commutative
          (G := G) (H := Ssub) (K := C0) (L := C1) hC0C1_comp hScomm
      have hSleE2 :=
        section12_tau2_sylow_le_E2_of_abelian
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
          (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
          hM hE hp hA hAS hScomm
      have hE₁_le_N : E₁ ≤ N := by
        have hE₁_le_E : E₁ ≤ E := hE.2.2.1.1.trans hE.2.1.1
        simpa [N, Ssub] using hE₁_le_E.trans hE_le_NS
      have hE₁_norm_of_normalIn :
          ∀ {Z : Subgroup G}, section10NormalIn Z N →
            E₁ ≤ Subgroup.normalizer (Z : Set G) := by
        intro Z hZnorm
        exact hE₁_le_N.trans
          ((Subgroup.normal_subgroupOf_iff_le_normalizer hZnorm.1).1 hZnorm.2)
      have hcentralizer_of_normal_factor :
          ∀ {Z : Subgroup G}, Z ≤ Ssub → IsPGroup p.val Z → IsCyclic Z →
            Z ≠ ⊥ → section10NormalIn Z N →
              subgroupCentralizerIn (section10Msigma M) (section12OmegaOneSubgroup p Z) = ⊥ := by
        intro Z hZleS hZp hZcyc hZne hZnorm
        have hOmegaZ_le_A : section12OmegaOneSubgroup p Z ≤ A := by
          have hmono := section12_omegaOneSubgroup_mono
            (G := G) (H := Z) (K := Ssub) (p := p) hZleS
          simpa [Ssub, hOmegaS] using hmono
        have hOmegaZ_card :
            Nat.card (section12OmegaOneSubgroup p Z) = p.val :=
          section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
            (G := G) (H := Z) (p := p) hZp hZcyc hZne
        have hOmegaZ_prime :
            section12OmegaOneSubgroup p Z ∈ section10PrimeOrderSubgroupsIn p A :=
          ⟨hOmegaZ_le_A, hOmegaZ_card⟩
        have hN_le_normZ : N ≤ Subgroup.normalizer (Z : Set G) :=
          (Subgroup.normal_subgroupOf_iff_le_normalizer hZnorm.1).1 hZnorm.2
        have hnormZ_le_normOmega :
            Subgroup.normalizer (Z : Set G) ≤
              Subgroup.normalizer (section12OmegaOneSubgroup p Z : Set G) := by
          have : (omega₁ (G := Z) (p := p.val)).Characteristic :=
            omega₁_characteristic (G := Z) (p := p.val)
          simpa [section12OmegaOneSubgroup] using
            (section8_normalizer_map_subtype_le_of_characteristic
              (G := G) (H := Z) (K := omega₁ (G := Z) (p := p.val)))
        have hNormA_eq_N : Subgroup.normalizer (A : Set G) = N := by
          simpa [N, Ssub] using h8d.1
        have hNormA_le_NormOmega :
            Subgroup.normalizer (A : Set G) ≤
              Subgroup.normalizer (section12OmegaOneSubgroup p Z : Set G) := by
          simpa [hNormA_eq_N] using hN_le_normZ.trans hnormZ_le_normOmega
        exact
          section12_subgroupCentralizerIn_primeOrder_eq_bot_of_normalizer_rankTwo
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
            (E₂ := E₂) (E₃ := E₃) (A := A)
            (X := section12OmegaOneSubgroup p Z) (p := p)
            hM hE hp hA hOmegaZ_prime hNormA_le_NormOmega
      obtain ⟨a, hC0card⟩ := hC0_p.exists_card_eq
      obtain ⟨b, hC1card⟩ := hC1_p.exists_card_eq
      by_cases hab : a ≤ b
      · have hC0exp_dvd_C1exp : Monoid.exponent C0 ∣ Monoid.exponent C1 := by
          rw [hC0_cyc.exponent_eq_card, hC1_cyc.exponent_eq_card, hC0card, hC1card]
          exact Nat.pow_dvd_pow p.val hab
        have hC1exp : Monoid.exponent C1 = Monoid.exponent Ssub := by
          calc
            Monoid.exponent C1 =
                Nat.lcm (Monoid.exponent C0) (Monoid.exponent C1) := by
              rw [Nat.lcm_eq_right hC0exp_dvd_C1exp]
            _ = Monoid.exponent Ssub := hSexp_lcm.symm
        exact ⟨C1, hC1_le_S, hC1_le_S.trans hSleE2, hC1_cyc, hC1exp,
          hE₁_norm_of_normalIn hC1_norm_N,
          hcentralizer_of_normal_factor hC1_le_S hC1_p hC1_cyc hC1_ne_bot hC1_norm_N⟩
      · have hba : b ≤ a := le_of_not_ge hab
        have hC1exp_dvd_C0exp : Monoid.exponent C1 ∣ Monoid.exponent C0 := by
          rw [hC0_cyc.exponent_eq_card, hC1_cyc.exponent_eq_card, hC0card, hC1card]
          exact Nat.pow_dvd_pow p.val hba
        have hC0exp : Monoid.exponent C0 = Monoid.exponent Ssub := by
          calc
            Monoid.exponent C0 =
                Nat.lcm (Monoid.exponent C0) (Monoid.exponent C1) := by
              rw [Nat.lcm_eq_left hC1exp_dvd_C0exp]
            _ = Monoid.exponent Ssub := hSexp_lcm.symm
        exact ⟨C0, hC0_le_S, hC0_le_S.trans hSleE2, hC0_cyc, hC0exp,
          hE₁_norm_of_normalIn hC0_norm_N,
          hcentralizer_of_normal_factor hC0_le_S hC0_p hC0_cyc hC0_ne_bot hC0_norm_N⟩

private theorem CFSG.section12_exists_tau2_regular_full_exponent_subgroup_of_abelian
    {M E E₁₂ E₁ E₂ E₃ A : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hcent :
      ∀ e : G, e ∈ E → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G)) :
    ∃ P₀ : Subgroup G, P₀ ≤ E₂ ∧ IsCyclic P₀ ∧
      Monoid.exponent P₀ = Monoid.exponent E₂ ∧
      E₁ ≤ Subgroup.normalizer (P₀ : Set G) ∧
      ∀ r : G, r ∈ P₀ → r ≠ 1 →
        elementCentralizerIn (section10Msigma M) r = ⊥ := by
  classical
  have h8a :=
    lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  have hE2comm : IsMulCommutative E₂ := h8a.1
  have hE2normE : section10NormalIn E₂ E := h8a.2
  have hHallE2 : IsHallSubgroup (section12Tau2Primes M) E₂ :=
    section12_E2_global_hall_of_abelian_sylow
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
      (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hp hA hAS hScomm
  let ι : Type := (Nat.card E₂).primeFactors
  let qOf : ι → Nat.Primes := fun i => ⟨i.1, Nat.prime_of_mem_primeFactors i.2⟩
  have hZfac_exists :
      ∀ i : ι, ∃ Z : Subgroup G,
        Z ≤ E₂ ∧ IsCyclic Z ∧ IsPGroup (qOf i).val Z ∧
        Monoid.exponent Z =
          Monoid.exponent
            ((((default : Sylow (qOf i).val E₂) : Subgroup E₂).map E₂.subtype) : Subgroup G) ∧
        E₁ ≤ Subgroup.normalizer (Z : Set G) ∧
        subgroupCentralizerIn (section10Msigma M)
          (section12OmegaOneSubgroup (qOf i) Z) = ⊥ := by
    intro i
    let q : Nat.Primes := qOf i
    have hq_dvd_E2 : q.val ∣ Nat.card E₂ :=
      Nat.dvd_of_mem_primeFactors i.2
    have hqτ2 : q ∈ section12Tau2Primes M :=
      hHallE2.p_in_pi_of_p_dvd_card q hq_dvd_E2
    obtain ⟨B, hB⟩ :=
      section12_exists_rankTwo_in_E_of_tau2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE hqτ2
    have hBq : IsPGroup q.val B := by
      have hElem := (section12_rankTwo_elementary hB).2
      have : IsElementaryAbelian q.val B := hElem
      exact IsElementaryAbelian.isPGroup q.val B
    obtain ⟨Q, hB_le_Q⟩ :=
      IsPGroup.exists_le_sylow (G := G) (p := q.val) hBq
    have hQcomm : IsMulCommutative (Q : Subgroup G) :=
      section12_tau2_sylow_comm_of_abelian_sylow
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A)
        (p := p) (q := q) (S := S) Q
        hM hE hp hA hAS hScomm hqτ2
    have hQ_le_E2 : (Q : Subgroup G) ≤ E₂ :=
      section12_tau2_sylow_le_E2_of_abelian
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := B) (p := q) (S := Q)
        hM hE hqτ2 hB hB_le_Q hQcomm
    obtain ⟨Z, hZ_le_Q, hZ_le_E2, hZcyc, hZexp, hZnorm, hCZ⟩ :=
      section12_debug_exists_tau2_normal_cyclic_factor_of_abelian
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂) (E₁ := E₁)
        (E₂ := E₂) (E₃ := E₃) (A := B) (p := q) (S := Q)
        hM hE hcent hqτ2 hB hB_le_Q hQcomm
    have hZsub_p : IsPGroup q.val (Z.subgroupOf (Q : Subgroup G)) :=
      Q.isPGroup'.to_subgroup (Z.subgroupOf (Q : Subgroup G))
    have hZp : IsPGroup q.val Z :=
      hZsub_p.of_equiv
        (Subgroup.subgroupOfEquivOfLe (H := Z) (K := (Q : Subgroup G)) hZ_le_Q)
    have hZexp' :
        Monoid.exponent Z =
          Monoid.exponent
            ((((default : Sylow q.val E₂) : Subgroup E₂).map E₂.subtype) : Subgroup G) := by
      let : IsMulCommutative E₂ := hE2comm
      have : Fact q.val.Prime := ⟨q.2⟩
      let QE2 : Sylow q.val E₂ := Q.subtype hQ_le_E2
      have hQexpE2 :
          Monoid.exponent (Q : Subgroup G) =
            Monoid.exponent ((QE2 : Subgroup E₂) : Subgroup E₂) := by
        symm
        rw [show (QE2 : Subgroup E₂) = (Q : Subgroup G).subgroupOf E₂ by
          simp [QE2]]
        exact Monoid.exponent_eq_of_mulEquiv
          (Subgroup.subgroupOfEquivOfLe
            (H := (Q : Subgroup G)) (K := E₂) hQ_le_E2)
      have hQE2_norm : ((QE2 : Subgroup E₂) : Subgroup E₂).Normal := by infer_instance
      let : Unique (Sylow q.val E₂) := Sylow.unique_of_normal QE2 hQE2_norm
      have hQE2_eq_def : QE2 = default := by
        simpa using (Unique.default_eq QE2).symm
      have hDefexp :
          Monoid.exponent ((QE2 : Subgroup E₂) : Subgroup E₂) =
            Monoid.exponent
              ((((default : Sylow q.val E₂) : Subgroup E₂).map E₂.subtype) : Subgroup G) := by
        rw [hQE2_eq_def]
        simpa using
          (Monoid.exponent_eq_of_mulEquiv
            (Subgroup.equivMapOfInjective
              (f := E₂.subtype)
              ((default : Sylow q.val E₂) : Subgroup E₂)
              E₂.subtype_injective))
      exact hZexp.trans (hQexpE2.trans hDefexp)
    exact ⟨Z, hZ_le_E2, hZcyc, hZp, hZexp', hZnorm, hCZ⟩
  let Zfac : ι → Subgroup G := fun i => Classical.choose (hZfac_exists i)
  have hZfac_le : ∀ i : ι, Zfac i ≤ E₂ := by
    intro i
    exact (Classical.choose_spec (hZfac_exists i)).1
  have hZfac_cyc : ∀ i : ι, IsCyclic (Zfac i) := by
    intro i
    exact (Classical.choose_spec (hZfac_exists i)).2.1
  have hZfac_p : ∀ i : ι, IsPGroup (qOf i).val (Zfac i) := by
    intro i
    exact (Classical.choose_spec (hZfac_exists i)).2.2.1
  have hZfac_exp :
      ∀ i : ι,
        Monoid.exponent (Zfac i) =
          Monoid.exponent
            ((((default : Sylow (qOf i).val E₂) : Subgroup E₂).map E₂.subtype) : Subgroup G) := by
    intro i
    exact (Classical.choose_spec (hZfac_exists i)).2.2.2.1
  have hZfac_norm :
      ∀ i : ι, E₁ ≤ Subgroup.normalizer (Zfac i : Set G) := by
    intro i
    exact (Classical.choose_spec (hZfac_exists i)).2.2.2.2.1
  have hZfac_omega_bot :
      ∀ i : ι,
        subgroupCentralizerIn (section10Msigma M)
          (section12OmegaOneSubgroup (qOf i) (Zfac i)) = ⊥ := by
    intro i
    exact (Classical.choose_spec (hZfac_exists i)).2.2.2.2.2
  let Qfac : ι → Subgroup G := fun i =>
    ((((default : Sylow (qOf i).val E₂) : Subgroup E₂).map E₂.subtype) : Subgroup G)
  have hQfac_sup : (⨆ i, Qfac i) = E₂ := by
    have hsup_top :
        (⨆ i : ι, ((default : Sylow (qOf i).val E₂) : Subgroup E₂)) = ⊤ := by
      simpa [ι, qOf, iSup_subtype] using (Sylow.iSup_sylow_eq_top (G := E₂))
    calc
      (⨆ i, Qfac i) =
          ((⨆ i : ι, ((default : Sylow (qOf i).val E₂) : Subgroup E₂)).map E₂.subtype) := by
        simp [Qfac, Subgroup.map_iSup]
      _ = ((⊤ : Subgroup E₂).map E₂.subtype) := by
        rw [hsup_top]
      _ = E₂.subtype.range := by rw [MonoidHom.range_eq_map]
        _ = E₂ := by simp
  have hZfac_comm :
      Pairwise fun i j => ∀ x y, x ∈ Zfac i → y ∈ Zfac j → Commute x y := by
    intro i j _hij x y hx hy
    exact setLike_mul_comm
      (s := E₂) (hZfac_le i hx) (hZfac_le j hy)
  have hQfac_comm :
      Pairwise fun i j => ∀ x y, x ∈ Qfac i → y ∈ Qfac j → Commute x y := by
    intro i j _hij x y hx hy
    have hxE2 : x ∈ E₂ := by
      rcases Subgroup.mem_map.mp hx with ⟨x', hx', rfl⟩
      exact x'.property
    have hyE2 : y ∈ E₂ := by
      rcases Subgroup.mem_map.mp hy with ⟨y', hy', rfl⟩
      exact y'.property
    exact setLike_mul_comm
      (s := E₂) hxE2 hyE2
  have hZfac_coprime :
      Pairwise fun i j => Nat.Coprime (Nat.card (Zfac i)) (Nat.card (Zfac j)) := by
    intro i j hij
    have : Fact (qOf i).val.Prime := ⟨(qOf i).2⟩
    have : Fact (qOf j).val.Prime := ⟨(qOf j).2⟩
    have hq_ne : (qOf i).val ≠ (qOf j).val := by
      intro hq
      apply hij
      exact Subtype.ext hq
    exact IsPGroup.coprime_card_of_ne
      (qOf i).val (qOf j).val hq_ne (Zfac i) (Zfac j) (hZfac_p i) (hZfac_p j)
  have hQfac_p : ∀ i : ι, IsPGroup (qOf i).val (Qfac i) := by
    intro i
    have : Fact (qOf i).val.Prime := ⟨(qOf i).2⟩
    simpa [Qfac] using
      IsPGroup.map (show IsPGroup (qOf i).val ((default : Sylow (qOf i).val E₂) : Subgroup E₂) from
        (default : Sylow (qOf i).val E₂).isPGroup') E₂.subtype
  have hQfac_coprime :
      Pairwise fun i j => Nat.Coprime (Nat.card (Qfac i)) (Nat.card (Qfac j)) := by
    intro i j hij
    have : Fact (qOf i).val.Prime := ⟨(qOf i).2⟩
    have : Fact (qOf j).val.Prime := ⟨(qOf j).2⟩
    have hq_ne : (qOf i).val ≠ (qOf j).val := by
      intro hq
      apply hij
      exact Subtype.ext hq
    exact IsPGroup.coprime_card_of_ne
      (qOf i).val (qOf j).val hq_ne (Qfac i) (Qfac j) (hQfac_p i) (hQfac_p j)
  let P₀ : Subgroup G := ⨆ i, Zfac i
  have hP₀_le_E2 : P₀ ≤ E₂ := by
    simpa [P₀] using iSup_le hZfac_le
  have hP₀cyc : IsCyclic P₀ :=
    section12_isCyclic_iSup_of_pairwise_coprime_cyclic
      (G := G) Zfac hZfac_cyc hZfac_comm hZfac_coprime
  have hP₀exp :
      Monoid.exponent P₀ =
        Finset.lcm Finset.univ (fun i : ι => Monoid.exponent (Zfac i)) := by
    simpa [P₀] using
      section12_exponent_eq_iSup_of_pairwise_coprime_order
        (G := G) Zfac hZfac_comm hZfac_coprime
  have hE2exp :
      Monoid.exponent E₂ =
        Finset.lcm Finset.univ (fun i : ι => Monoid.exponent (Qfac i)) := by
    calc
      Monoid.exponent E₂ = Monoid.exponent (↥(⨆ i, Qfac i)) := by
        rw [hQfac_sup.symm]
      _ = Finset.lcm Finset.univ (fun i : ι => Monoid.exponent (Qfac i)) := by
        simpa [Qfac] using
          section12_exponent_eq_iSup_of_pairwise_coprime_order
            (G := G) Qfac hQfac_comm hQfac_coprime
  have hP₀expE2 : Monoid.exponent P₀ = Monoid.exponent E₂ := by
    rw [hP₀exp, hE2exp]
    congr with i
    exact hZfac_exp i
  have hE₁normP₀ : E₁ ≤ Subgroup.normalizer (P₀ : Set G) := by
    have hforward (a : E₁) {x : G} (hx : x ∈ P₀) :
        (a : G) * x * (a : G)⁻¹ ∈ P₀ := by
      induction hx using Subgroup.iSup_induction' with
      | hp i x hx =>
          exact le_iSup Zfac i <|
            (Subgroup.mem_normalizer_iff.mp (hZfac_norm i a.property) x).1 hx
      | h1 =>
          simp
      | hmul x y hx hy hx' hy' =>
          simpa [mul_assoc] using P₀.mul_mem hx' hy'
    intro e he
    let e₁ : E₁ := ⟨e, he⟩
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · exact hforward e₁
    · intro hx
      have hx' := hforward (e₁⁻¹) hx
      simpa [e₁, mul_assoc] using hx'
  refine ⟨P₀, hP₀_le_E2, hP₀cyc, hP₀expE2, hE₁normP₀, ?_⟩
  have hMsigma_ne : section10Msigma M ≠ ⊥ := theorem_10_2_e (M := M) hM
  intro r hrP₀ hrne
  apply le_bot_iff.mp
  intro x hx
  by_contra hxne
  let R : Subgroup G := Subgroup.zpowers r
  have hR_le_P₀ : R ≤ P₀ := Subgroup.zpowers_le.2 hrP₀
  have hR_ne : R ≠ ⊥ := by
    intro hRbot
    have hrbot : r ∈ (⊥ : Subgroup G) := by
      simpa [R, hRbot] using (Subgroup.mem_zpowers r)
    exact hrne (by simpa using hrbot)
  have hR_card_ne_one : Nat.card R ≠ 1 := by
    intro hcard
    exact hR_ne ((Subgroup.card_eq_one (H := R)).mp hcard)
  obtain ⟨q0, hq0prime, hq0div⟩ := Nat.exists_prime_and_dvd hR_card_ne_one
  let q : Nat.Primes := ⟨q0, hq0prime⟩
  have : Fact q.val.Prime := ⟨q.2⟩
  obtain ⟨z, hzR, hzne, hXprimeR⟩ :=
    section12_exists_primeOrder_zpowers_of_prime_dvd_card
      (G := G) (B := R) (q := q) hq0div
  let X : Subgroup G := Subgroup.zpowers z
  have hX_le_R : X ≤ R := by
    simpa [X] using hXprimeR.1
  have hX_card : Nat.card X = q.val := by
    simpa [X] using hXprimeR.2
  have hq_dvd_E2 : q.val ∣ Nat.card E₂ :=
    hq0div.trans (Subgroup.card_dvd_of_le (hR_le_P₀.trans hP₀_le_E2))
  have hq_mem_E2 : q.val ∈ (Nat.card E₂).primeFactors := by
    exact Nat.mem_primeFactors.mpr ⟨q.2, hq_dvd_E2, Nat.card_pos.ne'⟩
  let i : ι := ⟨q.val, hq_mem_E2⟩
  have hqOf_i : qOf i = q := by
    apply Subtype.ext
    rfl
  have hZi_p : IsPGroup q.val (Zfac i) := by
    simpa [hqOf_i] using hZfac_p i
  have hOmega_bot :
      subgroupCentralizerIn (section10Msigma M)
        (section12OmegaOneSubgroup q (Zfac i)) = ⊥ := by
    simpa [hqOf_i] using hZfac_omega_bot i
  have hZi_ne : Zfac i ≠ ⊥ := by
    intro hZi_bot
    have hOmega_eq_bot : section12OmegaOneSubgroup q (Zfac i) = ⊥ := by
      rw [hZi_bot]
      apply le_antisymm
      · intro a ha
        rcases Subgroup.mem_map.mp ha with ⟨y, hy, rfl⟩
        simp
      · exact bot_le
    have hCent_one : Subgroup.centralizer ({1} : Set G) = ⊤ := by
      ext a
      rw [Subgroup.mem_centralizer_iff]
      constructor
      · intro _ha
        simp
      · intro _ha b hb
        have hb1 : b = 1 := by simpa using hb
        subst b
        simp
    have hσbot : section10Msigma M = ⊥ := by
      have hσinf :
          section10Msigma M ⊓ Subgroup.centralizer ({1} : Set G) = ⊥ := by
        simpa [subgroupCentralizerIn, hOmega_eq_bot] using hOmega_bot
      have hσinf_top : section10Msigma M ⊓ (⊤ : Subgroup G) = ⊥ := by
        simpa [hCent_one] using hσinf
      simpa using hσinf_top
    exact hMsigma_ne hσbot
  have hOmega_card : Nat.card (section12OmegaOneSubgroup q (Zfac i)) = q.val := by
    simpa [hqOf_i] using
      section12_omegaOneSubgroup_card_eq_prime_of_cyclic_pSubgroup
        (G := G) (H := Zfac i) (p := q) hZi_p (hZfac_cyc i) hZi_ne
  have hOmega_le_P₀ : section12OmegaOneSubgroup q (Zfac i) ≤ P₀ := by
    intro a ha
    rcases Subgroup.mem_map.mp ha with ⟨y, hy, rfl⟩
    exact le_iSup Zfac i y.property
  have hX_le_P₀ : X ≤ P₀ := hX_le_R.trans hR_le_P₀
  let : IsCyclic P₀ := hP₀cyc
  have hXsub_eq_OmegaSub :
      X.subgroupOf P₀ =
        (section12OmegaOneSubgroup q (Zfac i)).subgroupOf P₀ := by
    apply unique_subgroup_of_prime_order_in_cyclic
      (p := q.val)
      (G := P₀)
      (H := X.subgroupOf P₀)
      (K := (section12OmegaOneSubgroup q (Zfac i)).subgroupOf P₀)
    · simpa [section12_card_subgroupOf_eq hX_le_P₀] using hX_card
    · simpa [section12_card_subgroupOf_eq hOmega_le_P₀] using hOmega_card
  have hOmega_le_X : section12OmegaOneSubgroup q (Zfac i) ≤ X := by
    intro a ha
    have haSub : (⟨a, hOmega_le_P₀ ha⟩ : P₀) ∈
        (section12OmegaOneSubgroup q (Zfac i)).subgroupOf P₀ := by
      simpa [Subgroup.mem_subgroupOf] using ha
    have haXSub : (⟨a, hOmega_le_P₀ ha⟩ : P₀) ∈ X.subgroupOf P₀ := by
      rwa [← hXsub_eq_OmegaSub] at haSub
    simpa [Subgroup.mem_subgroupOf] using haXSub
  have hxr : Commute x r := by
    exact show x * r = r * x from
      ((Subgroup.mem_centralizer_iff.mp hx.2) r (by simp)).symm
  have hxz : Commute x z := by
    rcases Subgroup.mem_zpowers_iff.mp hzR with ⟨n, rfl⟩
    exact hxr.zpow_right n
  have hxCX : x ∈ subgroupCentralizerIn (section10Msigma M) X := by
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer (X : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    rcases Subgroup.mem_zpowers_iff.mp ha with ⟨n, rfl⟩
    exact (hxz.zpow_right n).eq.symm
  have hxCOmega : x ∈ subgroupCentralizerIn (section10Msigma M)
      (section12OmegaOneSubgroup q (Zfac i)) := by
    refine ⟨hx.1, ?_⟩
    change x ∈ Subgroup.centralizer (section12OmegaOneSubgroup q (Zfac i) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp hxCX.2) a (hOmega_le_X ha)
  have hxbot : x ∈ (⊥ : Subgroup G) := by
    simpa [hOmega_bot] using hxCOmega
  exact hxne (by simpa using hxbot)

private theorem CFSG.section12_pack_frobenius_from_abelian_tau2_factor
    {M E E₁₂ E₁ E₂ E₃ A P₀ : Subgroup G} {p : Nat.Primes} {S : Sylow p.val G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hcent :
      ∀ e : G, e ∈ E → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥)
    (hp : p ∈ section12Tau2Primes M)
    (hA : A ∈ section12RankTwoElementaryAbelianIn p E)
    (hAS : A ≤ (S : Subgroup G))
    (hScomm : IsMulCommutative (S : Subgroup G))
    (hP₀E₂ : P₀ ≤ E₂)
    (hP₀exp : Monoid.exponent P₀ = Monoid.exponent E₂)
    (hE₁normP₀ : E₁ ≤ Subgroup.normalizer (P₀ : Set G))
    (hP₀reg :
      ∀ r : G, r ∈ P₀ → r ≠ 1 →
        elementCentralizerIn (section10Msigma M) r = ⊥) :
    ∃ E₀ : Subgroup G, E₀ ≤ E ∧ Monoid.exponent E₀ = Monoid.exponent E ∧
      section12FrobeniusJoinWithKernel (section10Msigma M) E₀ := by
  classical
  let D : Subgroup G := E₁ ⊔ P₀
  let E₀ : Subgroup G := D ⊔ E₃
  have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
    (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE
  have hA_le_E₂ : A ≤ E₂ :=
    section12_rankTwo_tau2_le_E2
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
      hM hE hp hA
  have hE₂ne : E₂ ≠ ⊥ := by
    intro hE₂bot
    have hAbot : A = ⊥ := by
      exact le_bot_iff.mp (by rwa [hE₂bot] at hA_le_E₂)
    exact section12_rankTwo_ne_bot hA hAbot
  have hE12E : E₁₂ ≤ E := hE.2.1.1
  have hE1E12 : E₁ ≤ E₁₂ := hE.2.2.1.1
  have hE2E12 : E₂ ≤ E₁₂ := hE.2.2.2.1.1
  have hE3E : E₃ ≤ E := hE.2.2.2.2.1
  have hP₀E12 : P₀ ≤ E₁₂ := hP₀E₂.trans hE2E12
  have hDE12 : D ≤ E₁₂ := by
    simpa [D] using sup_le hE1E12 hP₀E12
  have hDE : D ≤ E := hDE12.trans hE12E
  have hE₀E : E₀ ≤ E := by
    simpa [E₀] using sup_le hDE hE3E
  have hP₀ne : P₀ ≠ ⊥ := by
    intro hP₀bot
    have hExpP₀ : Monoid.exponent P₀ = 1 := by
      have : Subsingleton P₀ := by
        rw [hP₀bot]
        infer_instance
      exact Monoid.exp_eq_one_of_subsingleton
    have hExpOne : Monoid.exponent E₂ = 1 := by
      rw [← hP₀exp, hExpP₀]
    have hE₂bot : E₂ = ⊥ := by
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      let xE₂ : E₂ := ⟨x, hx⟩
      have hsub : Subsingleton E₂ := (Monoid.exp_eq_one_iff).1 hExpOne
      exact congrArg Subtype.val (@Subsingleton.elim E₂ hsub xE₂ 1)
    exact hE₂ne hE₂bot
  have hE1E2_bot : E₁ ⊓ E₂ = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard
      (section12_coprime_card_E1_E2 (G := G) (M := M) (E := E)
        (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE)).eq_bot
  have hE1E2_disj : Disjoint E₁ E₂ := by
    rw [disjoint_iff]
    exact hE1E2_bot
  have hE1P₀_disj : Disjoint E₁ P₀ := hE1E2_disj.mono_right hP₀E₂
  have hP₀normD : section10NormalIn P₀ D := by
    refine ⟨by simp [D], ?_⟩
    simpa [D] using
      (Subgroup.normal_subgroupOf_sup_of_le_normalizer
        (H := E₁) (N := P₀) hE₁normP₀)
  have hcompD : section12ComplementIn D P₀ E₁ := by
    refine ⟨by simp [D], by simp [D], ?_, ?_⟩
    · simp [D, sup_comm]
    · exact hE1P₀_disj.symm
  have hcopP₀E₁ : Nat.Coprime (Nat.card P₀) (Nat.card E₁) := by
    have hcop : Nat.Coprime (Nat.card E₁) (Nat.card E₂) :=
      section12_coprime_card_E1_E2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE
    exact (hcop.of_dvd_right (Subgroup.card_dvd_of_le hP₀E₂)).symm
  have hExpD : Monoid.exponent D = Nat.lcm (Monoid.exponent P₀) (Monoid.exponent E₁) :=
    section12_exponent_eq_lcm_of_complement_normal_coprime
      (G := G) (H := D) (K := P₀) (L := E₁) hcompD hP₀normD hcopP₀E₁
  have hcompE₁₂ : section12ComplementIn E₁₂ E₂ E₁ := by
    refine ⟨hE2E12, hE1E12, ?_, ?_⟩
    · simp [h12.2.1, sup_comm]
    · exact hE1E2_disj.symm
  have hExpE₁₂ :
      Monoid.exponent E₁₂ = Nat.lcm (Monoid.exponent E₂) (Monoid.exponent E₁) :=
    section12_exponent_eq_lcm_of_complement_normal_coprime
      (G := G) (H := E₁₂) (K := E₂) (L := E₁)
      hcompE₁₂ h12.2.2.2
      (section12_coprime_card_E1_E2
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE).symm
  have hE12E3_bot : E₁₂ ⊓ E₃ = ⊥ :=
    (Subgroup.disjoint_of_coprime_natCard
      (section12_coprime_card_E12_E3 (G := G) (M := M) (E := E)
        (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE)).eq_bot
  have hE12E3_disj : Disjoint E₁₂ E₃ := by
    rw [disjoint_iff]
    exact hE12E3_bot
  have hDE3_disj : Disjoint D E₃ := hE12E3_disj.mono_left hDE12
  have hE₃normE : section10NormalIn E₃ E :=
    (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
  have hE_norm_E₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hE₃normE.1).1 hE₃normE.2
  have hE₃normE₀ : section10NormalIn E₃ E₀ := by
    refine ⟨by simp [E₀], ?_⟩
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer (by simp [E₀] : E₃ ≤ E₀)).2
      (hE₀E.trans hE_norm_E₃)
  have hcompE₀ : section12ComplementIn E₀ E₃ D := by
    refine ⟨by simp [E₀], by simp [E₀], ?_, ?_⟩
    · simp [E₀, sup_comm]
    · exact hDE3_disj.symm
  have hcopE₃D : Nat.Coprime (Nat.card E₃) (Nat.card D) := by
    have hcop : Nat.Coprime (Nat.card E₁₂) (Nat.card E₃) :=
      section12_coprime_card_E12_E3
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE
    exact (hcop.of_dvd_left (Subgroup.card_dvd_of_le hDE12)).symm
  have hExpE₀ : Monoid.exponent E₀ = Nat.lcm (Monoid.exponent E₃) (Monoid.exponent D) :=
    section12_exponent_eq_lcm_of_complement_normal_coprime
      (G := G) (H := E₀) (K := E₃) (L := D) hcompE₀ hE₃normE₀ hcopE₃D
  have hEeqE₁₂E₃ : E = E₁₂ ⊔ E₃ := by
    calc
      E = E₁ ⊔ E₂ ⊔ E₃ := h12.1
      _ = E₁₂ ⊔ E₃ := by simp [h12.2.1, sup_assoc]
  have hcompE : section12ComplementIn E E₃ E₁₂ := by
    refine ⟨hE3E, hE12E, ?_, ?_⟩
    · simpa [sup_comm] using hEeqE₁₂E₃
    · exact hE12E3_disj.symm
  have hExpE : Monoid.exponent E = Nat.lcm (Monoid.exponent E₃) (Monoid.exponent E₁₂) :=
    section12_exponent_eq_lcm_of_complement_normal_coprime
      (G := G) (H := E) (K := E₃) (L := E₁₂)
      hcompE hE₃normE
      (section12_coprime_card_E12_E3
        (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE).symm
  have hE₀exp : Monoid.exponent E₀ = Monoid.exponent E := by
    rw [hExpE₀, hExpE, hExpD, hExpE₁₂, hP₀exp]
  have hcentE₂ :
      ∀ x : G, x ∈ section10Msigma M → x ≠ 1 → elementCentralizerIn E x ≤ E₂ :=
    section12_elementCentralizerIn_E_le_E2_of_abelian
      (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
      (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
      hM hE hcent hp hA hAS hScomm
  have hcentE₀ :
      ∀ r : G, r ∈ E₀ → r ≠ 1 →
        elementCentralizerIn (section10Msigma M) r = ⊥ := by
    intro r hrE₀ hrne
    apply le_bot_iff.mp
    intro y hy
    by_contra hyne
    have hrCy : r ∈ elementCentralizerIn E y := by
      refine ⟨hE₀E hrE₀, ?_⟩
      change r ∈ Subgroup.centralizer ({y} : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hwy : w = y := by simpa using hw
      subst w
      exact ((Subgroup.mem_centralizer_iff.mp hy.2) r (by simp)).symm
    have hrE₂ : r ∈ E₂ := (hcentE₂ y hy.1 hyne) hrCy
    have hrE12 : r ∈ E₁₂ := hE2E12 hrE₂
    have hD_norm_E3 : D ≤ Subgroup.normalizer (E₃ : Set G) :=
      hDE.trans hE_norm_E₃
    have : (E₃.subgroupOf E₀).Normal := by
      simpa [E₀] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := D) (N := E₃) hD_norm_E3)
    let r₀ : E₀ := ⟨r, hrE₀⟩
    have hD_E₀ : D ≤ E₀ := by simp [E₀]
    have hE3_E₀ : E₃ ≤ E₀ := by simp [E₀]
    have hDE3_top : D.subgroupOf E₀ ⊔ E₃.subgroupOf E₀ = ⊤ := by
      calc
        D.subgroupOf E₀ ⊔ E₃.subgroupOf E₀ = (D ⊔ E₃).subgroupOf E₀ := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := D) (A' := E₃) (B := E₀) hD_E₀ hE3_E₀
        _ = ⊤ := by simp [E₀]
    have hr₀top : r₀ ∈ D.subgroupOf E₀ ⊔ E₃.subgroupOf E₀ := by
      simp [hDE3_top]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := D.subgroupOf E₀) (t := E₃.subgroupOf E₀) (x := r₀)).1 hr₀top with
      ⟨d₀, hd₀D, z₀, hz₀E3, hdz⟩
    let d : G := d₀
    let z : G := z₀
    have hdD : d ∈ D := by
      simpa [d, D, Subgroup.mem_subgroupOf] using hd₀D
    have hzE3 : z ∈ E₃ := by
      simpa [z, Subgroup.mem_subgroupOf] using hz₀E3
    have hdz_eq_r : d * z = r := by
      simpa [d, z, r₀] using congrArg (fun x : E₀ => (x : G)) hdz
    have hzE12 : z ∈ E₁₂ := by
      have hz_eq : z = d⁻¹ * r := by
        rw [← hdz_eq_r]
        simp
      rw [hz_eq]
      exact E₁₂.mul_mem (E₁₂.inv_mem (hDE12 hdD)) hrE12
    have hz_one : z = 1 := by
      have hzbot : z ∈ (⊥ : Subgroup G) := by
        simpa [hE12E3_bot] using (show z ∈ E₁₂ ⊓ E₃ from ⟨hzE12, hzE3⟩)
      simpa using hzbot
    have hr_eq_d : r = d := by
      rw [← hdz_eq_r, hz_one, mul_one]
    have hdE2 : d ∈ E₂ := by
      simpa [hr_eq_d] using hrE₂
    have : (P₀.subgroupOf D).Normal := by
      simpa [D] using
        (Subgroup.normal_subgroupOf_sup_of_le_normalizer
          (H := E₁) (N := P₀) hE₁normP₀)
    let dD : D := ⟨d, hdD⟩
    have hE1_D : E₁ ≤ D := by simp [D]
    have hP₀_D : P₀ ≤ D := by simp [D]
    have hE1P₀_top : E₁.subgroupOf D ⊔ P₀.subgroupOf D = ⊤ := by
      calc
        E₁.subgroupOf D ⊔ P₀.subgroupOf D = (E₁ ⊔ P₀).subgroupOf D := by
          symm
          exact Subgroup.subgroupOf_sup
            (A := E₁) (A' := P₀) (B := D) hE1_D hP₀_D
        _ = ⊤ := by simp [D]
    have hdDtop : dD ∈ E₁.subgroupOf D ⊔ P₀.subgroupOf D := by
      simp [hE1P₀_top]
    rcases (Subgroup.mem_sup_of_normal_right
        (s := E₁.subgroupOf D) (t := P₀.subgroupOf D) (x := dD)).1 hdDtop with
      ⟨eD, heE1, rD, hrP₀, her⟩
    let e : G := eD
    let r₁ : G := rD
    have heE1' : e ∈ E₁ := by
      simpa [e, Subgroup.mem_subgroupOf] using heE1
    have hr₁P₀ : r₁ ∈ P₀ := by
      simpa [r₁, Subgroup.mem_subgroupOf] using hrP₀
    have her_eq_d : e * r₁ = d := by
      simpa [e, r₁, dD] using congrArg (fun x : D => (x : G)) her
    have heE2 : e ∈ E₂ := by
      have hr₁E2 : r₁ ∈ E₂ := hP₀E₂ hr₁P₀
      have he_eq : e = d * r₁⁻¹ := by
        rw [← her_eq_d]
        simp [mul_assoc]
      rw [he_eq]
      exact E₂.mul_mem hdE2 (E₂.inv_mem hr₁E2)
    have he_one : e = 1 := by
      have hebot : e ∈ (⊥ : Subgroup G) := by
        simpa [hE1E2_bot] using (show e ∈ E₁ ⊓ E₂ from ⟨heE1', heE2⟩)
      simpa using hebot
    have hd_eq_r₁ : d = r₁ := by
      rw [← her_eq_d, he_one, one_mul]
    have hrP₀ : r ∈ P₀ := by
      simpa [hr_eq_d, hd_eq_r₁] using hr₁P₀
    have hybot : y ∈ (⊥ : Subgroup G) := by
      simpa [hP₀reg r hrP₀ hrne] using hy
    exact hyne (by simpa using hybot)
  have hE₀ne : E₀ ≠ ⊥ := by
    have hP₀E₀ : P₀ ≤ E₀ := by
      intro x hx
      have hxD : x ∈ D := by
        simpa [D] using ((show P₀ ≤ E₁ ⊔ P₀ from le_sup_right) hx)
      simpa [E₀] using ((show D ≤ D ⊔ E₃ from le_sup_left) hxD)
    intro hE₀bot
    apply hP₀ne
    exact le_bot_iff.mp (by simpa [hE₀bot] using hP₀E₀)
  refine ⟨E₀, hE₀E, hE₀exp, ?_⟩
  exact
    section12_frobeniusJoinWithKernel_of_trivial_centralizers_subgroup
      (G := G) (M := M) (E := E) (R := E₀)
      hM hE.1 hE₀E hE₀ne hcentE₀

/-- Theorem 12.12(b). -/
public theorem CFSG.theorem_12_12_b
    {M E E₁₂ E₁ E₂ E₃ : Subgroup G}
    (hM : M ∈ section9MaximalSubgroups G)
    (hE : section12EData M E E₁₂ E₁ E₂ E₃)
    (hcent :
      ∀ e : G, e ∈ E → e ≠ 1 →
        subgroupPrimeSet (Subgroup.zpowers e) ⊆
          section12Tau1Primes M ∪ section12Tau3Primes M →
            elementCentralizerIn (section10Msigma M) e = ⊥) :
    ∃ E₀ : Subgroup G, E₀ ≤ E ∧ Monoid.exponent E₀ = Monoid.exponent E ∧
      section12FrobeniusJoinWithKernel (section10Msigma M) E₀ := by
  classical
  by_cases hτ2empty : section12Tau2Primes M = ∅
  · have hcentE :
        ∀ e : G, e ∈ E → e ≠ 1 →
          elementCentralizerIn (section10Msigma M) e = ⊥ := by
      intro e heE hene
      apply hcent e heE hene
      intro q hqE
      have hqτ :
          q ∈ section12Tau1Primes M ∪ section12Tau2Primes M ∪
            section12Tau3Primes M :=
        section12_prime_mem_tau_union_of_mem_E hM hE.1
          (section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 heE) hqE)
      rcases hqτ with hq12 | hq3
      · rcases hq12 with hq1 | hq2
        · exact Or.inl hq1
        · exfalso
          exact (show q ∉ section12Tau2Primes M from by simp [hτ2empty]) hq2
      · exact Or.inr hq3
    refine ⟨E, le_rfl, rfl, ?_⟩
    exact
      section12_frobeniusJoinWithKernel_of_trivial_centralizers
        (G := G) (M := M) (E := E) hM hE.1 hcentE
  · have hτ2nonempty : (section12Tau2Primes M).Nonempty :=
      Set.nonempty_iff_ne_empty.mpr hτ2empty
    rcases hτ2nonempty with ⟨p, hp⟩
    obtain ⟨A, hA⟩ := section12_exists_rankTwo_in_E_of_tau2 hM hE hp
    by_cases hSylow : section12HasNonabelianSylowSubgroup p G
    · let C : Subgroup G := subgroupCentralizerIn A (section10Msigma M)
      obtain ⟨P₀, hP₀E₂, hE₂eq, hdisj, hE₁normP₀⟩ :=
        section12_CA_msigma_complement_in_E2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA hSylow
      let D : Subgroup G := E₁ ⊔ P₀
      let E₀ : Subgroup G := D ⊔ E₃
      have h12 := lemma_12_1_e (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
        (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE
      have hA_le_E₂ : A ≤ E₂ :=
        section12_rankTwo_tau2_le_E2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA
      have hE₂ne : E₂ ≠ ⊥ := by
        intro hE₂bot
        have hAbot : A = ⊥ := by
          exact le_bot_iff.mp (by rwa [hE₂bot] at hA_le_E₂)
        exact section12_rankTwo_ne_bot hA hAbot
      have hE12E : E₁₂ ≤ E := hE.2.1.1
      have hE1E12 : E₁ ≤ E₁₂ := hE.2.2.1.1
      have hE2E12 : E₂ ≤ E₁₂ := hE.2.2.2.1.1
      have hE3E : E₃ ≤ E := hE.2.2.2.2.1
      have hCE2 : C ≤ E₂ := by
        simpa [C] using
          section12_CA_msigma_le_E2_of_tau2
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
            hM hE hp hA
      have hCE : C ≤ E := hCE2.trans (hE2E12.trans hE12E)
      have hP₀E12 : P₀ ≤ E₁₂ := hP₀E₂.trans hE2E12
      have hDE12 : D ≤ E₁₂ := by
        simpa [D] using sup_le hE1E12 hP₀E12
      have hDE : D ≤ E := hDE12.trans hE12E
      have hE₀E : E₀ ≤ E := by
        simpa [E₀] using sup_le hDE hE3E
      have hE₀comp : section12ComplementIn E C E₀ := by
        refine ⟨hCE, hE₀E, ?_, ?_⟩
        · calc
            E = E₁ ⊔ E₂ ⊔ E₃ := h12.1
            _ = E₁ ⊔ (C ⊔ P₀) ⊔ E₃ := by
              simpa [C] using congrArg (fun X : Subgroup G => E₁ ⊔ X ⊔ E₃) hE₂eq
            _ = C ⊔ E₀ := by
              simp [D, E₀, sup_left_comm, sup_comm]
        · rw [Subgroup.disjoint_def]
          intro x hxC hxE₀
          have hxE2 : x ∈ E₂ := hCE2 hxC
          have hxE12 : x ∈ E₁₂ := hE2E12 hxE2
          have hE3norm : section10NormalIn E₃ E :=
            (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
              (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
          have hE_norm_E3 : E ≤ Subgroup.normalizer (E₃ : Set G) :=
            (Subgroup.normal_subgroupOf_iff_le_normalizer hE3norm.1).1 hE3norm.2
          have hD_norm_E3 : D ≤ Subgroup.normalizer (E₃ : Set G) :=
            hDE.trans hE_norm_E3
          have : (E₃.subgroupOf E₀).Normal := by
            simpa [E₀] using
              (Subgroup.normal_subgroupOf_sup_of_le_normalizer
                (H := D) (N := E₃) hD_norm_E3)
          let x₀ : E₀ := ⟨x, hxE₀⟩
          have hD_E₀ : D ≤ E₀ := by simp [E₀]
          have hE3_E₀ : E₃ ≤ E₀ := by simp [E₀]
          have hDE3_top : D.subgroupOf E₀ ⊔ E₃.subgroupOf E₀ = ⊤ := by
            calc
              D.subgroupOf E₀ ⊔ E₃.subgroupOf E₀ = (D ⊔ E₃).subgroupOf E₀ := by
                symm
                exact Subgroup.subgroupOf_sup
                  (A := D) (A' := E₃) (B := E₀) hD_E₀ hE3_E₀
              _ = ⊤ := by simp [E₀]
          have hx₀top : x₀ ∈ D.subgroupOf E₀ ⊔ E₃.subgroupOf E₀ := by
            simp [hDE3_top]
          rcases (Subgroup.mem_sup_of_normal_right
              (s := D.subgroupOf E₀) (t := E₃.subgroupOf E₀) (x := x₀)).1 hx₀top with
            ⟨d₀, hd₀D, z₀, hz₀E3, hdz⟩
          let d : G := d₀
          let z : G := z₀
          have hdD : d ∈ D := by
            simpa [d, D, Subgroup.mem_subgroupOf] using hd₀D
          have hzE3 : z ∈ E₃ := by
            simpa [z, Subgroup.mem_subgroupOf] using hz₀E3
          have hdz_eq_x : d * z = x := by
            simpa [d, z, x₀] using congrArg (fun y : E₀ => (y : G)) hdz
          have hzE12 : z ∈ E₁₂ := by
            have hz_eq : z = d⁻¹ * x := by
              rw [← hdz_eq_x]
              simp
            rw [hz_eq]
            exact E₁₂.mul_mem (E₁₂.inv_mem (hDE12 hdD)) hxE12
          have hE12E3_bot : E₁₂ ⊓ E₃ = ⊥ :=
            (Subgroup.disjoint_of_coprime_natCard
              (section12_coprime_card_E12_E3 (G := G) (M := M) (E := E)
                (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE)).eq_bot
          have hz_one : z = 1 := by
            have hzbot : z ∈ (⊥ : Subgroup G) := by
              simpa [hE12E3_bot] using (show z ∈ E₁₂ ⊓ E₃ from ⟨hzE12, hzE3⟩)
            simpa using hzbot
          have hx_eq_d : x = d := by
            rw [← hdz_eq_x, hz_one, mul_one]
          have hdE2 : d ∈ E₂ := by
            simpa [hx_eq_d] using hxE2
          have : (P₀.subgroupOf D).Normal := by
            simpa [D] using
              (Subgroup.normal_subgroupOf_sup_of_le_normalizer
                (H := E₁) (N := P₀) hE₁normP₀)
          let dD : D := ⟨d, hdD⟩
          have hE1_D : E₁ ≤ D := by simp [D]
          have hP₀_D : P₀ ≤ D := by simp [D]
          have hE1P₀_top : E₁.subgroupOf D ⊔ P₀.subgroupOf D = ⊤ := by
            calc
              E₁.subgroupOf D ⊔ P₀.subgroupOf D = (E₁ ⊔ P₀).subgroupOf D := by
                symm
                exact Subgroup.subgroupOf_sup
                  (A := E₁) (A' := P₀) (B := D) hE1_D hP₀_D
              _ = ⊤ := by simp [D]
          have hdDtop : dD ∈ E₁.subgroupOf D ⊔ P₀.subgroupOf D := by
            simp [hE1P₀_top]
          rcases (Subgroup.mem_sup_of_normal_right
              (s := E₁.subgroupOf D) (t := P₀.subgroupOf D) (x := dD)).1 hdDtop with
            ⟨eD, heE1, rD, hrP₀, her⟩
          let e : G := eD
          let r : G := rD
          have heE1' : e ∈ E₁ := by
            simpa [e, Subgroup.mem_subgroupOf] using heE1
          have hrP₀' : r ∈ P₀ := by
            simpa [r, Subgroup.mem_subgroupOf] using hrP₀
          have her_eq_d : e * r = d := by
            simpa [e, r, dD] using congrArg (fun y : D => (y : G)) her
          have heE2 : e ∈ E₂ := by
            have hrE2 : r ∈ E₂ := hP₀E₂ hrP₀'
            have he_eq : e = d * r⁻¹ := by
              rw [← her_eq_d]
              simp [mul_assoc]
            rw [he_eq]
            exact E₂.mul_mem hdE2 (E₂.inv_mem hrE2)
          have hE1E2_bot : E₁ ⊓ E₂ = ⊥ :=
            (Subgroup.disjoint_of_coprime_natCard
              (section12_coprime_card_E1_E2 (G := G) (M := M) (E := E)
                (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE)).eq_bot
          have he_one : e = 1 := by
            have hebot : e ∈ (⊥ : Subgroup G) := by
              simpa [hE1E2_bot] using (show e ∈ E₁ ⊓ E₂ from ⟨heE1', heE2⟩)
            simpa using hebot
          have hd_eq_r : d = r := by
            rw [← her_eq_d, he_one, one_mul]
          have hxP₀ : x ∈ P₀ := by
            simpa [hx_eq_d, hd_eq_r] using hrP₀'
          exact Subgroup.disjoint_def.mp hdisj hxC hxP₀
      have hP₀exp : Monoid.exponent P₀ = Monoid.exponent E₂ :=
        section12_exponent_eq_of_CA_msigma_complement_in_E2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (P₀ := P₀) (p := p)
          hM hE hp hA hSylow hP₀E₂ hE₂eq hdisj
      have hP₀ne : P₀ ≠ ⊥ := by
        intro hP₀bot
        have hExpP₀ : Monoid.exponent P₀ = 1 := by
          have : Subsingleton P₀ := by
            rw [hP₀bot]
            infer_instance
          exact Monoid.exp_eq_one_of_subsingleton
        have hExpOne : Monoid.exponent E₂ = 1 := by
          rw [← hP₀exp, hExpP₀]
        have hE₂bot : E₂ = ⊥ := by
          rw [Subgroup.eq_bot_iff_forall]
          intro x hx
          let xE₂ : E₂ := ⟨x, hx⟩
          have hsub : Subsingleton E₂ := (Monoid.exp_eq_one_iff).1 hExpOne
          exact congrArg Subtype.val (@Subsingleton.elim E₂ hsub xE₂ 1)
        exact hE₂ne hE₂bot
      have hE1E2_bot : E₁ ⊓ E₂ = ⊥ :=
        (Subgroup.disjoint_of_coprime_natCard
          (section12_coprime_card_E1_E2 (G := G) (M := M) (E := E)
            (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE)).eq_bot
      have hE1E2_disj : Disjoint E₁ E₂ := by
        rw [disjoint_iff]
        exact hE1E2_bot
      have hE1P₀_disj : Disjoint E₁ P₀ := hE1E2_disj.mono_right hP₀E₂
      have hP₀normD : section10NormalIn P₀ D := by
        refine ⟨by simp [D], ?_⟩
        simpa [D] using
          (Subgroup.normal_subgroupOf_sup_of_le_normalizer
            (H := E₁) (N := P₀) hE₁normP₀)
      have hcompD : section12ComplementIn D P₀ E₁ := by
        refine ⟨by simp [D], by simp [D], ?_, ?_⟩
        · simp [D, sup_comm]
        · exact hE1P₀_disj.symm
      have hcopP₀E₁ : Nat.Coprime (Nat.card P₀) (Nat.card E₁) := by
        have hcop : Nat.Coprime (Nat.card E₁) (Nat.card E₂) :=
          section12_coprime_card_E1_E2
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE
        exact (hcop.of_dvd_right (Subgroup.card_dvd_of_le hP₀E₂)).symm
      have hExpD : Monoid.exponent D = Nat.lcm (Monoid.exponent P₀) (Monoid.exponent E₁) :=
        section12_exponent_eq_lcm_of_complement_normal_coprime
          (G := G) (H := D) (K := P₀) (L := E₁) hcompD hP₀normD hcopP₀E₁
      have hcompE₁₂ : section12ComplementIn E₁₂ E₂ E₁ := by
        refine ⟨hE2E12, hE1E12, ?_, ?_⟩
        · simp [h12.2.1, sup_comm]
        · exact hE1E2_disj.symm
      have hExpE₁₂ :
          Monoid.exponent E₁₂ = Nat.lcm (Monoid.exponent E₂) (Monoid.exponent E₁) :=
        section12_exponent_eq_lcm_of_complement_normal_coprime
          (G := G) (H := E₁₂) (K := E₂) (L := E₁)
          hcompE₁₂ h12.2.2.2
          (section12_coprime_card_E1_E2
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE).symm
      have hE12E3_bot : E₁₂ ⊓ E₃ = ⊥ :=
        (Subgroup.disjoint_of_coprime_natCard
          (section12_coprime_card_E12_E3 (G := G) (M := M) (E := E)
            (E₁₂ := E₁₂) (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE)).eq_bot
      have hE12E3_disj : Disjoint E₁₂ E₃ := by
        rw [disjoint_iff]
        exact hE12E3_bot
      have hDE3_disj : Disjoint D E₃ := hE12E3_disj.mono_left hDE12
      have hE₃normE : section10NormalIn E₃ E :=
        (lemma_12_1_b (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hM hE).2
      have hE_norm_E₃ : E ≤ Subgroup.normalizer (E₃ : Set G) :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hE₃normE.1).1 hE₃normE.2
      have hE₃normE₀ : section10NormalIn E₃ E₀ := by
        refine ⟨by simp [E₀], ?_⟩
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer (by simp [E₀] : E₃ ≤ E₀)).2
          (hE₀E.trans hE_norm_E₃)
      have hcompE₀ : section12ComplementIn E₀ E₃ D := by
        refine ⟨by simp [E₀], by simp [E₀], ?_, ?_⟩
        · simp [E₀, sup_comm]
        · exact hDE3_disj.symm
      have hcopE₃D : Nat.Coprime (Nat.card E₃) (Nat.card D) := by
        have hcop : Nat.Coprime (Nat.card E₁₂) (Nat.card E₃) :=
          section12_coprime_card_E12_E3
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE
        exact (hcop.of_dvd_left (Subgroup.card_dvd_of_le hDE12)).symm
      have hExpE₀ : Monoid.exponent E₀ = Nat.lcm (Monoid.exponent E₃) (Monoid.exponent D) :=
        section12_exponent_eq_lcm_of_complement_normal_coprime
          (G := G) (H := E₀) (K := E₃) (L := D) hcompE₀ hE₃normE₀ hcopE₃D
      have hEeqE₁₂E₃ : E = E₁₂ ⊔ E₃ := by
        calc
          E = E₁ ⊔ E₂ ⊔ E₃ := h12.1
          _ = E₁₂ ⊔ E₃ := by simp [h12.2.1, sup_assoc]
      have hcompE : section12ComplementIn E E₃ E₁₂ := by
        refine ⟨hE3E, hE12E, ?_, ?_⟩
        · simpa [sup_comm] using hEeqE₁₂E₃
        · exact hE12E3_disj.symm
      have hExpE : Monoid.exponent E = Nat.lcm (Monoid.exponent E₃) (Monoid.exponent E₁₂) :=
        section12_exponent_eq_lcm_of_complement_normal_coprime
          (G := G) (H := E) (K := E₃) (L := E₁₂)
          hcompE hE₃normE
          (section12_coprime_card_E12_E3
            (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
            (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) hE).symm
      have hE₀exp : Monoid.exponent E₀ = Monoid.exponent E := by
        rw [hExpE₀, hExpE, hExpD, hExpE₁₂, hP₀exp]
      have hE₀tau1 :
          ∀ x : G, x ∈ section10Msigma M → x ≠ 1 →
            subgroupPrimeSet (elementCentralizerIn E₀ x) ⊆ section12Tau1Primes M :=
        section12_tau1_primeSupport_of_centralizer_of_complement
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (E₀ := E₀) (p := p)
          hM hE hp hA hE₀comp hSylow
      have hcentE₀ :
          ∀ r : G, r ∈ E₀ → r ≠ 1 →
            elementCentralizerIn (section10Msigma M) r = ⊥ := by
        intro r hrE₀ hrne
        apply le_bot_iff.mp
        intro y hy
        by_contra hyne
        have hrτ13 :
            subgroupPrimeSet (Subgroup.zpowers r) ⊆
              section12Tau1Primes M ∪ section12Tau3Primes M := by
          intro q hqR
          have hrCy : r ∈ elementCentralizerIn E₀ y := by
            refine ⟨hrE₀, ?_⟩
            change r ∈ Subgroup.centralizer ({y} : Set G)
            rw [Subgroup.mem_centralizer_iff]
            intro w hw
            have hwy : w = y := by simpa using hw
            subst w
            exact ((Subgroup.mem_centralizer_iff.mp hy.2) r (by simp)).symm
          exact Or.inl
            ((hE₀tau1 y hy.1 hyne)
              (section8_subgroupPrimeSet_mono (Subgroup.zpowers_le.2 hrCy) hqR))
        have hybot : y ∈ (⊥ : Subgroup G) := by
          simpa [hcent r (hE₀E hrE₀) hrne hrτ13] using hy
        exact hyne (by simpa using hybot)
      have hE₀ne : E₀ ≠ ⊥ := by
        have hP₀E₀ : P₀ ≤ E₀ := by
          intro x hx
          have hxD : x ∈ D := by
            simpa [D] using ((show P₀ ≤ E₁ ⊔ P₀ from le_sup_right) hx)
          simpa [E₀] using ((show D ≤ D ⊔ E₃ from le_sup_left) hxD)
        intro hE₀bot
        apply hP₀ne
        exact le_bot_iff.mp (by simpa [hE₀bot] using hP₀E₀)
      refine ⟨E₀, hE₀E, hE₀exp, ?_⟩
      exact
        section12_frobeniusJoinWithKernel_of_trivial_centralizers_subgroup
          (G := G) (M := M) (E := E) (R := E₀)
          hM hE.1 hE₀E hE₀ne hcentE₀
    · have hAp : IsPGroup p.val A := by
        have hAelem := (section12_rankTwo_elementary hA).2
        let : IsElementaryAbelian p.val A := hAelem
        exact IsElementaryAbelian.isPGroup p.val A
      obtain ⟨S, hAS⟩ := IsPGroup.exists_le_sylow (G := G) (p := p.val) hAp
      have hScomm : IsMulCommutative (S : Subgroup G) := by
        by_contra hSnoncomm
        exact hSylow ⟨S, hSnoncomm⟩
      have h8a :=
        lemma_12_8_a (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
          hM hE hp hA hAS hScomm
      have hE2comm : IsMulCommutative E₂ := h8a.1
      have hE2normE : section10NormalIn E₂ E := h8a.2
      have hAllTau2Ab :
          ∀ q : Nat.Primes, q ∈ section12Tau2Primes M →
            ¬ section12HasNonabelianSylowSubgroup q G :=
        section12_all_tau2_sylow_comm_of_one
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (p := p) hM hE hp hSylow
      have hE2HallIn :
          section12HallSubgroupIn (section12Tau2Primes M) E₂ E :=
        section12_E2_hall_in_E hE.2.1 hE.2.2.2.1
      rcases hE2HallIn with ⟨hE2E, hHallE2E⟩
      have hA_le_E2 : A ≤ E₂ :=
        section12_rankTwo_tau2_le_E2
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p)
          hM hE hp hA
      have hE2ne : E₂ ≠ ⊥ := by
        intro hE2bot
        have hAbot : A = ⊥ := by
          exact le_bot_iff.mp (by rwa [hE2bot] at hA_le_E2)
        exact section12_rankTwo_ne_bot hA hAbot
      have hcentE2 :
          ∀ x : G, x ∈ section10Msigma M → x ≠ 1 → elementCentralizerIn E x ≤ E₂ :=
        section12_elementCentralizerIn_E_le_E2_of_abelian
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
          hM hE hcent hp hA hAS hScomm
      obtain ⟨P₀, hP₀E₂, _hP₀cyc, hP₀expE₂, hE₁normP₀, hP₀reg⟩ :=
        section12_exists_tau2_regular_full_exponent_subgroup_of_abelian
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (p := p) (S := S)
          hM hE hcent hp hA hAS hScomm
      exact
        section12_pack_frobenius_from_abelian_tau2_factor
          (G := G) (M := M) (E := E) (E₁₂ := E₁₂)
          (E₁ := E₁) (E₂ := E₂) (E₃ := E₃) (A := A) (P₀ := P₀) (p := p) (S := S)
          hM hE hcent hp hA hAS hScomm hP₀E₂ hP₀expE₂ hE₁normP₀ hP₀reg

end Section12
