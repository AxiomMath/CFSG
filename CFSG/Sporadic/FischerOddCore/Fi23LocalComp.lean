module

public import CFSG.Sporadic.FischerOddCore.PairComp
public import CFSG.Sporadic.FischerOddCore.Fi23UniqCheck
public import CFSG.Sporadic.FischerOddCore.Fi23Stab
public import CFSG.Sporadic.Fi23.InvCover

public noncomputable section

namespace CFSG.Sporadic.FischerOddCore

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

open CFSG CFSG.LocalCores
open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Perm.Native CFSG.Sporadic.Fi23.Native

theorem eq_one_or_eq_of_card_two {H : Type*} [Group H] (h2 : Nat.card H = 2) {z : H}
    (hz : z ≠ 1) (c : H) : c = 1 ∨ c = z := by
  by_contra hc
  rw [not_or] at hc
  have h3 : ({1, z, c} : Set H).ncard = 3 :=
    Set.ncard_eq_three.2 ⟨1, z, c, hz.symm, Ne.symm hc.1, Ne.symm hc.2, rfl⟩
  have : Finite H := Nat.finite_of_card_ne_zero (by rw [h2]; norm_num)
  have hle := Set.ncard_le_ncard (Set.subset_univ ({1, z, c} : Set H))
  rw [h3, Set.ncard_univ, h2] at hle
  omega

theorem fi23_d1_mem :
    CFSG.Sporadic.Fi23.d1 ∈ CFSG.Sporadic.Fi23.D23 :=
  (CFSG.Sporadic.Fi23.isConj_d_iff _).2 ⟨⟨1, by norm_num⟩, rfl⟩

theorem fi23_d_mul_d1_not_mem :
    CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d1 ∉
    CFSG.Sporadic.Fi23.D23 := fun h => by
  have := CFSG.Sporadic.Fi23.card_fixed_conj (h : IsConj CFSG.Sporadic.Fi23.d _)
  rw [CFSG.Sporadic.Fi23.card_fixed_d, CFSG.Sporadic.Fi23.card_fixed_d_mul_d1] at this
  omega

open CFSG.Sporadic.Fi23 in
theorem fi23_pair_unique
    (c : J) (hc : c * (d * d1) = d * d1 * c) :
    c * d * c⁻¹ = d ∨ c * d * c⁻¹ = d1 := by
  have hx : c * d * c⁻¹ ∈ D23 := conj_mem_D23 c d (IsConj.refl _)
  obtain ⟨⟨k, hk⟩, hxk0⟩ := (isConj_d_iff _).1 hx
  have hxk : conjPt k = c * d * c⁻¹ := hxk0
  have hdd : d * d1 * d = d * (d * d1) := by rw [mul_assoc, d1_commute]
  have hcc : c⁻¹ * (d * d1) * c = d * d1 := by rw [mul_assoc, ← hc]; group
  have hfix : conjPt k * (d * d1) = d * d1 * conjPt k := by
    rw [hxk]
    calc c * d * c⁻¹ * (d * d1) = c * (d * (c⁻¹ * (d * d1) * c)) * c⁻¹ := by group
      _ = c * (d * (d * d1)) * c⁻¹ := by rw [hcc]
      _ = c * (d * d1 * d) * c⁻¹ := by rw [hdd]
      _ = c * (d * d1) * (d * c⁻¹) := by group
      _ = d * d1 * c * (d * c⁻¹) := by rw [hc]
      _ = d * d1 * (c * d * c⁻¹) := by group
  have hap : ap XBT k = k := ap_eq_of_commute rep_XBT hk hfix
  have hmem : conjPt k * (d * d1) ∈ D23 := by
    rw [hxk]
    have e : c * d * c⁻¹ * (d * d1) = c * d1 * c⁻¹ := by
      calc c * d * c⁻¹ * (d * d1) = c * (d * (c⁻¹ * (d * d1) * c)) * c⁻¹ := by group
        _ = c * (d * (d * d1)) * c⁻¹ := by rw [hcc]
        _ = c * d1 * c⁻¹ := by rw [show d * (d * d1) = d1 by rw [← mul_assoc, d_sq, one_mul]]
    rw [e]
    exact conj_mem_D23 c d1 fi23_d1_mem
  have hcount : CFSG.Sporadic.Fi23.Native.fixCount (compT 31671 (ptT k) XBT) = 3511 := by
    rw [← card_fixed_eq (Rep.compT (rep_ptT k) rep_XBT), ← card_fixed_conj hmem, card_fixed_d]
  have hcert := fi23Uniq_certificate
  unfold fi23UniqOK at hcert
  dsimp only at hcert
  have h := allIn_eq_true.1 hcert k (Nat.zero_le _) hk
  simp only [Bool.or_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h
  rcases h with ((h | h) | h) | h
  · left
    rw [← hxk]
    subst h
    exact conjPt_zero
  · right
    rw [← hxk]
    subst h
    rfl
  · exact absurd hap h
  · exact absurd hcount h

theorem exists_noncomm_fi22J :
    ∃ a b : CFSG.Sporadic.Fi22.J, a * b ≠ b * a :=
  @exists_noncomm_of_isSimpleGroup CFSG.Sporadic.Fi22.J inferInstance
    CFSG.Sporadic.Fi22.isSimpleGroup_J (by rw [CFSG.Sporadic.Fi22.card_J]; norm_num)

theorem isSolvable_ker_fi23Kappa :
    Group.IsSolvable fi23Kappa.ker := by
  rw [ker_fi23Kappa]
  infer_instance

theorem card_quotient_center_of_component_Cd
    {B : Subgroup CFSG.Sporadic.Fi23.Cd}
    (hB : IsComponent B) : Nat.card (B ⧸ Subgroup.center B) = 64561751654400 := by
  rw [@card_quotient_center_of_component_simple CFSG.Sporadic.Fi23.Cd CFSG.Sporadic.Fi22.J
    inferInstance inferInstance inferInstance fi23Kappa fi23Kappa_surjective
    isSolvable_ker_fi23Kappa CFSG.Sporadic.Fi22.isSimpleGroup_J exists_noncomm_fi22J B hB,
    CFSG.Sporadic.Fi22.card_J]

theorem fi23Kappa_eq_one
    {c : CFSG.Sporadic.Fi23.Cd} (hc : fi23Kappa c = 1) :
    (c : CFSG.Sporadic.Fi23.J) = 1 ∨ (c : CFSG.Sporadic.Fi23.J) = CFSG.Sporadic.Fi23.d := by
  have hcZ : c ∈ Subgroup.center CFSG.Sporadic.Fi23.Cd := by
    rw [← ker_fi23Kappa]
    exact hc
  have hdZ : CFSG.Sporadic.Fi23.dCd ∈ Subgroup.center CFSG.Sporadic.Fi23.Cd := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (CFSG.Sporadic.Fi23.mem_Cd.1 g.2)
  have hd1 : (⟨CFSG.Sporadic.Fi23.dCd, hdZ⟩ : Subgroup.center CFSG.Sporadic.Fi23.Cd) ≠ 1 :=
    fun h => by
      have := congrArg (fun z : Subgroup.center CFSG.Sporadic.Fi23.Cd => orderOf z) h
      simp only [orderOf_one] at this
      rw [Subgroup.orderOf_mk, CFSG.Sporadic.Fi23.orderOf_dCd] at this
      omega
  rcases eq_one_or_eq_of_card_two CFSG.Sporadic.Fi23.card_center_C hd1 ⟨c, hcZ⟩ with h | h
  · left
    exact congrArg (fun z : Subgroup.center CFSG.Sporadic.Fi23.Cd =>
      (((z : CFSG.Sporadic.Fi23.Cd) : CFSG.Sporadic.Fi23.J))) h
  · right
    exact congrArg (fun z : Subgroup.center CFSG.Sporadic.Fi23.Cd =>
      (((z : CFSG.Sporadic.Fi23.Cd) : CFSG.Sporadic.Fi23.J))) h

theorem fi23Kappa_star
    {x : CFSG.Sporadic.Fi23.Cd}
    (hx : (x : CFSG.Sporadic.Fi23.J) ∈ CFSG.Sporadic.Fi23.star) :
    fi23Kappa x ∈ CFSG.Sporadic.Fi22.D := by
  obtain ⟨k, hk, hrho⟩ := CFSG.Sporadic.Fi23.rho_star x hx
  have : fi23Kappa x = CFSG.Sporadic.Fi22.conjPt k :=
    CFSG.Sporadic.Fi23.pi22_injective (by
      rw [fi23Kappa_apply, CFSG.Sporadic.Fi23.pi22_quotCenterEquiv, hrho])
  rw [this]
  exact CFSG.Sporadic.Fi22.mem_D_iff.2 ⟨k, hk, rfl⟩

theorem fi23_d1_mem_Cd :
    CFSG.Sporadic.Fi23.d1 ∈ CFSG.Sporadic.Fi23.Cd :=
  CFSG.Sporadic.Fi23.mem_Cd.2 CFSG.Sporadic.Fi23.d1_commute

theorem mul_self_eq_one_of_mem_center {H : Type*} [Group H] (h2 : Nat.card (Subgroup.center H) = 2)
    {y : H} (hy : y ∈ Subgroup.center H) : y * y = 1 := by
  have h := pow_card_eq_one' (G := Subgroup.center H) (x := ⟨y, hy⟩)
  rw [h2, sq] at h
  exact congrArg Subtype.val h

theorem fi22Kappa_eq_one
    {y : CFSG.Sporadic.Fi22.Ca} (hy : fi22Kappa y = 1) : y * y = 1 := by
  have hyZ : y ∈ Subgroup.center CFSG.Sporadic.Fi22.Ca := by
    rw [← ker_fi22Kappa]
    exact hy
  exact @mul_self_eq_one_of_mem_center CFSG.Sporadic.Fi22.Ca inferInstance
    CFSG.Sporadic.Fi22.card_center_Ca y hyZ

theorem exists_hom_fi23_inf :
    ∃ ρ : ↥(Subgroup.centralizer ({CFSG.Sporadic.Fi23.d} : Set CFSG.Sporadic.Fi23.J) ⊓
        Subgroup.centralizer {CFSG.Sporadic.Fi23.d1}) →* CFSG.Fischer.T46,
      Function.Surjective ρ ∧ ∀ u, ρ u = 1 → u * u * (u * u) = 1 :=
  @exists_hom_inf_centralizer CFSG.Sporadic.Fi23.J inferInstance CFSG.Sporadic.Fi23.d
    CFSG.Sporadic.Fi23.d1 CFSG.Sporadic.Fi22.J CFSG.Fischer.T46 inferInstance inferInstance
    CFSG.Sporadic.Fi23.d_sq fi23_d1_mem_Cd fi23Kappa fi23Kappa_surjective
    (fun _ hc => fi23Kappa_eq_one hc)
    (fun c h => fi23_d_mul_d1_not_mem (h ▸ CFSG.Sporadic.Fi23.conj_mem_D23 c _ fi23_d1_mem))
    CFSG.Sporadic.Fi22.a (fi23Kappa_star CFSG.Sporadic.Fi23.d1_mem_localClass) fi22Kappa
    fi22Kappa_surjective (fun _ hy => fi22Kappa_eq_one hy)

theorem fi23_d_ne_d1 :
    CFSG.Sporadic.Fi23.d ≠ CFSG.Sporadic.Fi23.d1 := fun h => by
  have h2 := CFSG.Sporadic.Fi23.orderOf_d_mul_conjPt_one
  rw [show CFSG.Sporadic.Fi23.conjPt 1 = CFSG.Sporadic.Fi23.d1 from rfl, ← h,
    CFSG.Sporadic.Fi23.d_sq, orderOf_one] at h2
  omega

theorem card_quotient_center_of_component_dd1
    {B : Subgroup ↥(Subgroup.centralizer
      ({CFSG.Sporadic.Fi23.d * CFSG.Sporadic.Fi23.d1} : Set CFSG.Sporadic.Fi23.J))}
    (hB : IsComponent B) : Nat.card (B ⧸ Subgroup.center B) = 9196830720 := by
  obtain ⟨ρ, hρ, hρk⟩ := exists_hom_fi23_inf
  have hd1 : CFSG.Sporadic.Fi23.d1 * CFSG.Sporadic.Fi23.d1 = 1 := by
    rw [← sq]
    exact CFSG.Sporadic.Fi23.d1_sq
  rw [@card_quotient_center_of_component_pair CFSG.Sporadic.Fi23.J inferInstance
    CFSG.Sporadic.Fi23.d CFSG.Sporadic.Fi23.d1 inferInstance CFSG.Fischer.T46 inferInstance
    CFSG.Sporadic.Fi23.d_sq hd1 CFSG.Sporadic.Fi23.d1_commute.symm fi23_d_ne_d1
    fi23_pair_unique ρ hρ hρk CFSG.Fischer.isSimpleGroup_T46 exists_noncomm_T46 B hB,
    CFSG.Fischer.card_T46]

end CFSG.Sporadic.FischerOddCore
