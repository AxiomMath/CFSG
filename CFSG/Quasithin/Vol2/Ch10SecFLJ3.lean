module

public import CFSG.Quasithin.Vol2.Ch10SecFLJ2
public import CFSG.Quasithin.Vol2.Ch10SecERho
public import CFSG.Quasithin.Vol2.Ch10SecFLJ1

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.A5.Delta5 (pact isEven)

variable {G : Type} [Group G] [Finite G]

theorem exists_two_ne_one_of_card_eq_four {Q : Type*} [Group Q] [Finite Q] (h : Nat.card Q = 4) :
    ∃ a b : Q, a ≠ 1 ∧ b ≠ 1 ∧ a ≠ b := by
  classical
  have : Fintype Q := Fintype.ofFinite Q
  have h2 : 2 < Fintype.card Q := by rw [← Nat.card_eq_fintype_card, h]; norm_num
  obtain ⟨a, b, c, hab, hac, hbc⟩ := Fintype.two_lt_card_iff.mp h2
  by_cases ha : a = 1
  · exact ⟨b, c, fun h => hab (ha.trans h.symm), fun h => hac (ha.trans h.symm), hbc⟩
  · by_cases hb : b = 1
    · exact ⟨a, c, ha, fun h => hbc (hb.trans h.symm), hac⟩
    · exact ⟨a, b, ha, hb, hab⟩

theorem false_of_relIndex_eq_three {L Y P : Subgroup G} (hA : IsAltType L 5)
    (hZ : blockZ L = ⊥) (hYL : Y ≤ Subgroup.normalizer (L : Set G)) (hP : IsSylowTwoOf P L)
    (hPY : P ≤ Subgroup.normalizer (Y : Set G)) {v : G} (hv : v ∈ blockU L)
    (hidx : (Subgroup.centralizer (conjClosure (Subgroup.zpowers v) Y : Set G)).relIndex Y = 3) :
    False := by
  obtain ⟨c, π, hcinj, hceven, hcact, hπmul, α, hαs, hαk, hπα⟩ := exists_pi_normalizer hA hZ
  set Nn := Subgroup.normalizer (L : Set G) with hNn
  set Z := conjClosure (Subgroup.zpowers v) Y with hZdef
  set C := Subgroup.centralizer (Z : Set G) with hCdef
  have hNU : Nn ≤ Subgroup.normalizer (blockU L : Set G) := SecA.le_normalizer_commutator
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L) le_rfl
  have hZU : Z ≤ blockU L := conjClosure_le fun y hy z hz =>
    (Subgroup.mem_normalizer_iff.mp (hNU (hYL hy)) z).mp (Subgroup.zpowers_le.mpr hv hz)
  have hYZ : Y ≤ Subgroup.normalizer (Z : Set G) := le_normalizer_conjClosure _ Y
  have hYC : Y ≤ Subgroup.normalizer (C : Set G) := SecA.le_normalizer_centralizer hYZ
  have : (C.subgroupOf Y).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hYC
  obtain ⟨y, hyY, hyC⟩ : ∃ y ∈ Y, y ∉ C := by
    by_contra hcon
    push Not at hcon
    have h1 : C.relIndex Y = 1 := Subgroup.relIndex_eq_one.mpr hcon
    omega
  obtain ⟨p, hpY, hpC, a, hpa⟩ := exists_three_part hidx hyY hyC
  have hpN := hYL hpY
  have hq3 : π p ^ 3 = 1 := by
    refine perm_five_pow_three_pow (π p) a ?_
    rw [← map_pow_of_mul hπmul hpN, hpa, map_one_of_mul hπmul]
  obtain ⟨z, hz, hzp⟩ : ∃ z ∈ Z, z * p ≠ p * z := by
    by_contra hcon
    push Not at hcon
    exact hpC (Subgroup.mem_centralizer_iff.mpr hcon)
  have hzU := hZU hz
  have hpzU : p * z * p⁻¹ ∈ blockU L := (Subgroup.mem_normalizer_iff.mp (hNU hpN) z).mp hzU
  have hcp : c (p * z * p⁻¹) = pact (π p) (c z) := hcact p hpN z hzU
  have hqw : pact (π p) (c z) ≠ c z := by
    intro h
    apply hzp
    have h1 := hcinj _ hpzU z hzU (hcp.trans h)
    calc z * p = (p * z * p⁻¹) * p := by rw [h1]
      _ = p * z := by group
  have hq1 : π p ≠ 1 := fun h => hqw (by rw [h]; rfl)
  have hz1 : p * z * p⁻¹ ∈ Z := (Subgroup.mem_normalizer_iff.mp (hYZ hpY) z).mp hz
  have hz2 : p * (p * z * p⁻¹) * p⁻¹ ∈ Z :=
    (Subgroup.mem_normalizer_iff.mp (hYZ hpY) _).mp hz1
  have hcp2 : c (p * (p * z * p⁻¹) * p⁻¹) = pact (π p) (pact (π p) (c z)) := by
    rw [hcact p hpN _ hpzU, hcp]
  have key : ∀ u ∈ P, π u * π p * (π u)⁻¹ = 1 ∨ π u * π p * (π u)⁻¹ = π p ∨
      π u * π p * (π u)⁻¹ = π p * π p := by
    intro u hu
    have huN : u ∈ Nn := Subgroup.le_normalizer (hP.1 hu)
    have hupu : u * p * u⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hPY hu) p).mp hpY
    obtain ⟨j, hj3, hjC⟩ := exists_pow_inv_mul_mem hidx hpY hpC hupu
    set n := (p ^ j)⁻¹ * (u * p * u⁻¹) with hn
    have hnY : n ∈ Y := Y.mul_mem (Y.inv_mem (Y.pow_mem hpY j)) hupu
    have hnN := hYL hnY
    have hfix : ∀ z' ∈ Z, n * z' * n⁻¹ = z' := fun z' hz' => by
      rw [← Subgroup.mem_centralizer_iff.mp hjC z' hz']
      group
    have hw0 : pact (π n) (c z) = c z := by rw [← hcact n hnN z hzU, hfix z hz]
    have hw1 : pact (π n) (pact (π p) (c z)) = pact (π p) (c z) := by
      rw [← hcp, ← hcact n hnN _ hpzU, hfix _ hz1]
    have hw2 : pact (π n) (pact (π p) (pact (π p) (c z))) = pact (π p) (pact (π p) (c z)) := by
      rw [← hcp2, ← hcact n hnN _ (hZU hz2), hfix _ hz2]
    obtain ⟨hnq, hn2⟩ := stab_three (π p) hq3 (c z) (hceven z hzU) hqw (π n) hw0 hw1 hw2
    have e3 : u * p * u⁻¹ = p ^ j * n := by rw [hn]; group
    have hπ1 : π (u * p * u⁻¹) = π u * π p * (π u)⁻¹ := by
      rw [hπmul _ (Nn.mul_mem huN hpN) _ (Nn.inv_mem huN), hπmul _ huN _ hpN,
        map_inv_of_mul hπmul huN]
    have hπ2 : π (u * p * u⁻¹) = π p ^ j * π n := by
      rw [e3, hπmul _ (Nn.pow_mem hpN j) _ hnN, map_pow_of_mul hπmul hpN]
    have hc' : Commute (π n) (π p) := hnq
    have hc : Commute (π p ^ j) (π n) := hc'.symm.pow_left j
    have hcube : (π p ^ j * π n) ^ 3 = π n := by
      rw [hc.mul_pow, ← pow_mul, show j * 3 = 3 * j by ring, pow_mul, hq3, one_pow, one_mul,
        pow_succ, pow_two, hn2, one_mul]
    have hcube' : (π u * π p * (π u)⁻¹) ^ 3 = 1 := by rw [conj_pow, hq3, mul_one, mul_inv_cancel]
    have hn1 : π n = 1 := by rw [← hcube, ← hπ2, hπ1, hcube']
    have hfinal : π u * π p * (π u)⁻¹ = π p ^ j := by rw [← hπ1, hπ2, hn1, mul_one]
    interval_cases j
    · left; rw [hfinal, pow_zero]
    · right; left; rw [hfinal, pow_one]
    · right; right; rw [hfinal, pow_two]
  have hQsyl := SecE.isSylowTwoOf_map_range'' hP α
  have hrange : α.range = ⊤ := MonoidHom.range_eq_top.mpr hαs
  have hQ4 : Nat.card ↥((P.subgroupOf L).map α) = 4 := SecE.card_eq_four_of_sylow hQsyl
    (by rw [hrange, Subgroup.card_top, SecE.card_alt_five])
  obtain ⟨⟨a₁, ha₁Q⟩, ⟨b₁, hb₁Q⟩, ha₁, hb₁, hab₁⟩ := exists_two_ne_one_of_card_eq_four hQ4
  have hsq : ∀ x ∈ (P.subgroupOf L).map α, (x : Perm (Fin 5)) * x = 1 := by
    intro x hx
    have h4 : (⟨x, hx⟩ : ↥((P.subgroupOf L).map α)) ^ 4 = 1 := by
      rw [← hQ4]
      exact pow_card_eq_one'
    have h4' : (x : Perm (Fin 5)) ^ 4 = 1 := by
      have := congrArg (fun y : ↥((P.subgroupOf L).map α) => ((y : ↥(alternatingGroup (Fin 5))) :
        Perm (Fin 5))) h4
      simpa using this
    exact alt_pow_four _ (Perm.mem_alternatingGroup.mp x.2) h4'
  obtain ⟨ua, hua, rfl⟩ := Subgroup.mem_map.mp ha₁Q
  obtain ⟨ub, hub, rfl⟩ := Subgroup.mem_map.mp hb₁Q
  have hA1 : ((α ua : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) ≠ 1 := fun h =>
    ha₁ (Subtype.ext (Subtype.ext h))
  have hB1 : ((α ub : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) ≠ 1 := fun h =>
    hb₁ (Subtype.ext (Subtype.ext h))
  have hBA : ((α ub : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) ≠ α ua := fun h =>
    hab₁ (Subtype.ext (Subtype.ext h.symm))
  have hAB : ((α ua : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) * α ub = α ub * α ua := by
    have h1 := hsq _ (Subgroup.mul_mem _ ha₁Q hb₁Q)
    have hA2 := hsq _ ha₁Q
    have hB2 := hsq _ hb₁Q
    rw [Subgroup.coe_mul] at h1
    set A : Perm (Fin 5) := ((α ua : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) with hAdef
    set B : Perm (Fin 5) := ((α ub : ↥(alternatingGroup (Fin 5))) : Perm (Fin 5)) with hBdef
    have h2 : B * A = A * B := by
      calc B * A = B * A * ((A * B) * (A * B)) := by rw [h1, mul_one]
        _ = B * (A * A) * B * (A * B) := by group
        _ = A * B := by rw [hA2, mul_one, hB2, one_mul]
    exact h2.symm
  rw [← hπα ua] at hA1 hBA hAB
  rw [← hπα ub] at hB1 hBA hAB
  exact false_of_two_inv (π p) hq3 hq1 (π ua) (by rw [hπα]; exact (α ua).2) hA1
    (by rw [hπα]; exact hsq _ ha₁Q) (key ua hua) (π ub) (by rw [hπα]; exact (α ub).2) hB1 hBA
    (by rw [hπα]; exact hsq _ hb₁Q) hAB (key ub hub)

end CFSG.Quasithin.Vol2.Ch10.SecF
