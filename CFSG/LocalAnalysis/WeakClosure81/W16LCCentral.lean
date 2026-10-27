module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped commutatorElement

private theorem w16l_sylow_sup_of_isPGroup_quotient
    {G : Type*} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {M : Subgroup G} [M.Normal] (P : Sylow p G)
    (h : IsPGroup p (G ⧸ M)) : (P : Subgroup G) ⊔ M = ⊤ := by
  have hπ : Function.Surjective (QuotientGroup.mk' M : G →* G ⧸ M) :=
    QuotientGroup.mk'_surjective M
  have htop : (P : Subgroup G).map (QuotientGroup.mk' M) = ⊤ := by
    have hle := IsPGroup.le_sylow_of_normal (p := p) (N := ⊤)
      (h.of_equiv Subgroup.topEquiv.symm) (P.mapSurjective hπ)
    have htop' : (P.mapSurjective hπ : Subgroup (G ⧸ M)) = ⊤ := top_le_iff.mp hle
    simpa using htop'
  rw [← QuotientGroup.ker_mk' M,
    ← Subgroup.comap_map_eq (QuotientGroup.mk' M) (P : Subgroup G), htop,
    Subgroup.comap_top]

private theorem w16l_le_center_of_two_quotient
    {L : Type*} [Group L] [Finite L]
    (hO2 : CFSG.pCore 2 L ≤ Subgroup.center L)
    {N R : Subgroup L} (hN : N ≤ Subgroup.center L) (hR : R.Normal) (hNR : N ≤ R)
    (htwo : ∀ r ∈ R, ∃ k : ℕ, r ^ 2 ^ k ∈ N) :
    R ≤ Subgroup.center L := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : R.Normal := hR
  have hN' : N.subgroupOf R ≤ Subgroup.center ↥R := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (hN ((Subgroup.mem_subgroupOf).mp hx))) y)
  haveI : (N.subgroupOf R).Normal := Subgroup.normal_of_le_center hN'
  have hp : IsPGroup 2 (↥R ⧸ N.subgroupOf R) := fun q => by
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨k, hk⟩ := htwo x.1 x.2
    exact ⟨k, by
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
      exact hk⟩
  haveI : Group.IsNilpotent (↥R ⧸ N.subgroupOf R) := hp.isNilpotent
  haveI : Group.IsNilpotent ↥R := Subgroup.isNilpotent_of_ker_le_center
    (QuotientGroup.mk' (N.subgroupOf R)) (by rw [QuotientGroup.ker_mk']; exact hN')
  let P : Sylow 2 ↥R := default
  haveI hPchar : (P : Subgroup ↥R).Characteristic :=
    Sylow.characteristic_of_normal P (inferInstance : (P : Subgroup ↥R).Normal)
  have hP'normal : ((P : Subgroup ↥R).map R.subtype).Normal :=
    ConjAct.normal_of_characteristic_of_normal
  have hP'2 : IsPGroup 2 ((P : Subgroup ↥R).map R.subtype) := P.isPGroup'.map R.subtype
  have hP'le : ((P : Subgroup ↥R).map R.subtype) ≤ CFSG.pCore 2 L :=
    le_sSup ⟨hP'normal, hP'2⟩
  have hsup : (P : Subgroup ↥R) ⊔ N.subgroupOf R = ⊤ :=
    w16l_sylow_sup_of_isPGroup_quotient (p := 2) (M := N.subgroupOf R) P hp
  have hReq : (P : Subgroup ↥R).map R.subtype ⊔ N = R := by
    rw [← Subgroup.map_subgroupOf_eq_of_le hNR, ← Subgroup.map_sup, hsup, Subgroup.map_top,
      Subgroup.range_subtype]
  exact hReq ▸ sup_le (hP'le.trans hO2) hN

theorem w16l_central_layers {L : Type*} [Group L] [Finite L]
    (hgen : Subgroup.closure {x : L | x * x = 1} = ⊤)
    (hO2 : CFSG.pCore 2 L ≤ Subgroup.center L)
    {N R₁ R₂ : Subgroup L} (hN : N ≤ Subgroup.center L) (hR₁ : R₁.Normal) (hNR₁ : N ≤ R₁)
    (hR₁two : ∀ r ∈ R₁, ∃ k : ℕ, r ^ 2 ^ k ∈ N)
    (hR₁R₂ : R₁ ≤ R₂)
    (hR₂odd : ∀ r ∈ R₂, ∃ m : ℕ, Odd m ∧ r ^ m ∈ R₁)
    (hR₂comm : ∀ r ∈ R₂, ∀ l : L, ⁅r, l⁆ ∈ R₁) :
    R₂ ≤ Subgroup.center L := by
  classical
  have hR1Z : R₁ ≤ Subgroup.center L :=
    w16l_le_center_of_two_quotient hO2 hN hR₁ hNR₁ hR₁two
  intro r hr
  rw [Subgroup.mem_center_iff]
  intro l
  have hcentral : Subgroup.closure {x : L | x * x = 1} ≤ Subgroup.centralizer ({r} : Set L) := by
    rw [Subgroup.closure_le]
    intro a ha
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst h
    have hcR1 : ⁅r, a⁆ ∈ R₁ := hR₂comm r hr a
    have hcZ : ⁅r, a⁆ ∈ Subgroup.center L := hR1Z hcR1
    have hc2 : ⁅r, a⁆ ^ 2 = 1 := by
      have hcomm : Commute a ⁅r, a⁆ := Subgroup.mem_center_iff.mp hcZ a
      rw [hcomm.commutatorElement_pow_right 2, pow_two, ha, commutatorElement_one_right]
    obtain ⟨m, hm, hrm⟩ := hR₂odd r hr
    have hcm : ⁅r, a⁆ ^ m = 1 := by
      have hcomm : Commute r ⁅r, a⁆ := Subgroup.mem_center_iff.mp hcZ r
      rw [hcomm.commutatorElement_pow_left m]
      exact commutatorElement_eq_one_iff_mul_comm.mpr
        (Subgroup.mem_center_iff.mp (hR1Z hrm) a).symm
    have hc1 : ⁅r, a⁆ = 1 := by
      have hdvd2 : orderOf ⁅r, a⁆ ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hc2
      have hdvdm : orderOf ⁅r, a⁆ ∣ m := orderOf_dvd_iff_pow_eq_one.mpr hcm
      have hgcd : orderOf ⁅r, a⁆ ∣ Nat.gcd 2 m := Nat.dvd_gcd hdvd2 hdvdm
      rw [(Nat.coprime_two_left.mpr hm).gcd_eq_one] at hgcd
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_one hgcd)
    exact commutatorElement_eq_one_iff_mul_comm.mp hc1
  have htop : (⊤ : Subgroup L) ≤ Subgroup.centralizer ({r} : Set L) := hgen ▸ hcentral
  exact (Subgroup.mem_centralizer_iff.mp (htop (Subgroup.mem_top l)) r (by simp)).symm

end CFSG.LocalAnalysis.WeakClosure81

end
