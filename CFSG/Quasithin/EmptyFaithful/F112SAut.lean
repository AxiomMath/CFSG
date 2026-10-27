module

public import CFSG.Quasithin.EmptyFaithful.F112STits
public import CFSG.Quasithin.Recognition.CertTwoF4Outer

public section

namespace CFSG.Quasithin.F112S

open CFSG.Open CFSG.Sporadic.Schreier.Tits CFSG.Certificates CFSG.Certificates.Native
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Quasithin

theorem isPGroup_titsS :
    IsPGroup 2 titsS :=
  IsPGroup.of_card (n := 11) (by rw [titsQS_facts.2.2.2]; norm_num)

@[expose] noncomputable def twoF4Q2 :
    Subgroup (Equiv.Perm (Fin 1755)) :=
  extSub titsS tπ tπ_norm_S tπ_sq_S

section Certs


theorem twoF4Q2_le : twoF4Q2 ≤ twoF4M := by
  intro x hx
  rcases hx with hx | hx
  · exact titsS_le_twoF4M hx
  · have : x = (x * tπ⁻¹) * tπ := by group
    rw [this]
    exact twoF4M.mul_mem (titsS_le_twoF4M hx) tπ_mem_twoF4M

theorem titsS_le_twoF4Q2 : titsS ≤ twoF4Q2 := le_extSub

theorem card_twoF4Q2 : Nat.card twoF4Q2 = 4096 := by
  have h1 := Subgroup.card_mul_index (titsS.subgroupOf twoF4Q2)
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe titsS_le_twoF4Q2).toEquiv,
    titsQS_facts.2.2.2] at h1
  have h2 : (titsS.subgroupOf twoF4Q2).index = 2 :=
    relIndex_extSub (fun h => tπ_not_mem_D (titsS_le_titsD h))
  rw [h2] at h1
  omega

theorem isPGroup_twoF4Q2 : IsPGroup 2 twoF4Q2 :=
  isPGroup_extSub isPGroup_titsS

@[expose] noncomputable def twoF4Sylow : Sylow 2 twoF4M :=
  (IsPGroup.of_equiv isPGroup_twoF4Q2 (Subgroup.subgroupOfEquivOfLe twoF4Q2_le).symm :
    IsPGroup 2 (twoF4Q2.subgroupOf twoF4M)).toSylow (by
    have h1 := Subgroup.card_mul_index (twoF4Q2.subgroupOf twoF4M)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe twoF4Q2_le).toEquiv, card_twoF4Q2,
      card_twoF4M, card_titsD] at h1
    have : (twoF4Q2.subgroupOf twoF4M).index = 8775 := by omega
    rw [this]
    decide)

theorem coe_twoF4Sylow :
    (twoF4Sylow : Subgroup twoF4M) = twoF4Q2.subgroupOf twoF4M :=
  IsPGroup.toSylow_coe _ _

theorem no_involution_outer (h : TitsRankCheck) {s : Equiv.Perm (Fin 1755)} (hs : s ∈ titsS) :
    (s * tπ) * (s * tπ) ≠ 1 := by
  obtain ⟨a, ha, hp⟩ := exists_rep_of_all5 (p := fun a =>
    !(eqA 1755 (compA 1755 (compA 1755 a titsPiArr) (compA 1755 a titsPiArr)) (idA 1755)))
    h.2.2.2.2 hs
  intro h1
  have hr : Rep 1755 (compA 1755 a titsPiArr) (s * tπ) := rep_compA ha tπ_rep
  have := (eqA_iff (rep_compA hr hr) rep_idA).2 h1
  simp [this] at hp

theorem mem_titsD_of_sq (h : TitsRankCheck) {x : Equiv.Perm (Fin 1755)} (hx : x ∈ twoF4M)
    (hx2 : x * x = 1) : x ∈ titsD := by
  by_contra hxD
  let x' : twoF4M := ⟨x, hx⟩
  have hx'2 : x' * x' = 1 := Subtype.ext hx2
  have hxp : IsPGroup 2 (Subgroup.zpowers x') := by
    rintro ⟨g, hg⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hg
    refine ⟨1, Subtype.ext ?_⟩
    have h2 : x' ^ (2 : ℤ) = 1 := by rw [zpow_two, hx'2]
    have h3 : (x' ^ n) * (x' ^ n) = 1 := by
      rw [← zpow_add, ← two_mul, zpow_mul, h2, one_zpow]
    simpa [pow_one, sq] using h3
  obtain ⟨m, hm⟩ := exists_conj_le_sylow twoF4Sylow hxp
  have hy := hm x' (Subgroup.mem_zpowers x')
  rw [coe_twoF4Sylow, Subgroup.mem_subgroupOf] at hy
  have hy' : (m : Equiv.Perm (Fin 1755)) * x * (m : Equiv.Perm (Fin 1755))⁻¹ ∈ twoF4Q2 := hy
  rcases hy' with hS | hS
  · apply hxD
    have hD : (m : Equiv.Perm (Fin 1755)) * x * (m : Equiv.Perm (Fin 1755))⁻¹ ∈ titsD :=
      titsS_le_titsD hS
    have hD' : m * x' * m⁻¹ ∈ titsD.subgroupOf twoF4M := hD
    have hn := twoF4D_normal.conj_mem (m * x' * m⁻¹) hD' m⁻¹
    have e : m⁻¹ * (m * x' * m⁻¹) * m⁻¹⁻¹ = x' := by group
    rw [e] at hn
    exact hn
  · have hyy : ((m : Equiv.Perm (Fin 1755)) * x * (m : Equiv.Perm (Fin 1755))⁻¹) *
        ((m : Equiv.Perm (Fin 1755)) * x * (m : Equiv.Perm (Fin 1755))⁻¹) = 1 := by
      calc _ = (m : Equiv.Perm (Fin 1755)) * (x * x) * (m : Equiv.Perm (Fin 1755))⁻¹ := by group
        _ = 1 := by rw [hx2]; group
    refine absurd ?_ (no_involution_outer h hS)
    have e : (((m : Equiv.Perm (Fin 1755)) * x * (m : Equiv.Perm (Fin 1755))⁻¹) * tπ⁻¹) * tπ =
        (m : Equiv.Perm (Fin 1755)) * x * (m : Equiv.Perm (Fin 1755))⁻¹ := by group
    rw [e]
    exact hyy

theorem card_le_twoF4M (h : TitsRankCheck) {F : Subgroup (Equiv.Perm (Fin 1755))}
    (hF : F ≤ twoF4M) (hE : IsElemAbelian 2 F) : Nat.card F ≤ 32 :=
  card_le_titsD h (fun x hx => mem_titsD_of_sq h (hF hx) (by simpa [sq] using hE.2 x hx)) hE

end Certs

end CFSG.Quasithin.F112S
