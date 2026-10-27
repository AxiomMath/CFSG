module

public import CFSG.RankThree.GF2n.Stroth80.Sec11Dihedral
public import CFSG.RankThree.GF2n.Stroth80.Sec11Ebar

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem stroth_11_6 [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {n : ℕ} (hw : Width Q Z n)
    {d : Mbar M Q} (hd : d ∈ Ebar M Q Z B) {τ : Mbar M Q} (hτ : d⁻¹ * τ * d = τ⁻¹)
    (hodd : Odd (orderOf τ)) : orderOf τ ∣ Nat.card Z ^ 2 - 1 := by
  classical
  obtain ⟨⟨e, he, hA2⟩, x, hx⟩ := hd
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective τ
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective x
  subst he
  have hQmem : ∀ u : ↥M, (QuotientGroup.mk u : Mbar M Q) = 1 ↔ (u : G) ∈ Q := fun u => by
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have heH : (e : G) ∈ H0 M Z := by
    obtain ⟨l, hl, hle⟩ := Subgroup.mem_map.mp hx
    have h1 : (QuotientGroup.mk (y * e * y⁻¹) : Mbar M Q) = QuotientGroup.mk l := by
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      exact hle.symm
    have h2 := QuotientGroup.eq.mp h1
    rw [Subgroup.mem_subgroupOf] at h2 hl
    have h3 : ((y * e * y⁻¹ : ↥M) : G) ∈ LB M Q B := by
      have e1 : ((y * e * y⁻¹ : ↥M) : G) =
          (l : G) * (((y * e * y⁻¹ : ↥M) : G)⁻¹ * (l : G))⁻¹ := by group
      rw [e1]
      exact (LB M Q B).mul_mem hl ((LB M Q B).inv_mem (Subgroup.mem_sup_left h2))
    have h4 := hc.conj_mem_H0 (M.inv_mem y.2) (hc.LB_le_H0 h3)
    have e2 : (y : G)⁻¹ * ((y * e * y⁻¹ : ↥M) : G) * ((y : G)⁻¹)⁻¹ = (e : G) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      group
    rwa [e2] at h4
  have heZ : ∀ z ∈ Z, (e : G) * z * (e : G)⁻¹ = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp heH.2 z hz
    rw [← this]
    group
  have heZ' : ∀ z ∈ Z, (e : G)⁻¹ * z * (e : G) = z := fun z hz => by
    have := Subgroup.mem_centralizer_iff.mp heH.2 z hz
    rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
  have hcq : (((e⁻¹ * g * e * g : ↥M)) : G) ∈ Q := by
    rw [← hQmem, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul,
      QuotientGroup.mk_inv, hτ]
    exact inv_mul_cancel _
  have hgm : (((g ^ orderOf (QuotientGroup.mk g : Mbar M Q) : ↥M)) : G) ∈ Q := by
    rw [← hQmem, QuotientGroup.mk_pow, pow_orderOf_eq_one]
  have hcq' : ((e : G)⁻¹ * (g : G) * (e : G) * (g : G)) ∈ Q := by
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hcq
  have hgm' : (g : G) ^ orderOf (QuotientGroup.mk g : Mbar M Q) ∈ Q := by
    simpa only [Subgroup.coe_pow] using hgm
  have hgZ : ∀ z ∈ Z, (g : G) * z * (g : G)⁻¹ = (g : G)⁻¹ * z * (g : G) := by
    intro z hz
    have hgz : (g : G) * z * (g : G)⁻¹ ∈ Z :=
      (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 g.2) z).mp hz
    have hgz' : (g : G)⁻¹ * z * (g : G) ∈ Z := by
      have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 (M.inv_mem g.2)) z).mp hz
      simpa using this
    set u : G := (e : G)⁻¹ * (g : G) * (e : G) with hu
    set cq : G := (e : G)⁻¹ * (g : G) * (e : G) * (g : G) with hcqdef
    have hA : u * z * u⁻¹ = (g : G) * z * (g : G)⁻¹ := by
      have e1 : u * z * u⁻¹ =
          (e : G)⁻¹ * ((g : G) * ((e : G) * z * (e : G)⁻¹) * (g : G)⁻¹) * (e : G) := by
        simp only [hu]
        group
      rw [e1, heZ z hz, heZ' _ hgz]
    have hC : u * z * u⁻¹ = (g : G)⁻¹ * z * (g : G) := by
      have e2 : u = cq * (g : G)⁻¹ := by
        simp only [hu, hcqdef]
        group
      have e3 : u * z * u⁻¹ = cq * ((g : G)⁻¹ * z * (g : G)) * cq⁻¹ := by
        rw [e2]
        group
      rw [e3, hc.conj_Z_of_mem_Q hcq' hgz']
    exact hA.symm.trans hC
  obtain ⟨j, hj⟩ := hodd
  have hgcent : (g : G) ∈ Subgroup.centralizer (Z : Set G) := by
    have hg2 : (g : G) ^ 2 ∈ Subgroup.centralizer (Z : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      have hgz : (g : G) * z * (g : G)⁻¹ ∈ Z :=
        (Subgroup.mem_normalizer_iff.mp (hc.hyp.Z_normal.2 g.2) z).mp hz
      have h1 := hgZ _ hgz
      have e1 : (g : G) ^ 2 * z * ((g : G) ^ 2)⁻¹ =
          (g : G) * ((g : G) * z * (g : G)⁻¹) * (g : G)⁻¹ := by
        rw [pow_two]
        group
      have e2 : (g : G)⁻¹ * ((g : G) * z * (g : G)⁻¹) * (g : G) = z := by group
      have h2 : (g : G) ^ 2 * z * ((g : G) ^ 2)⁻¹ = z := by rw [e1, h1, e2]
      exact (mul_inv_eq_iff_eq_mul.mp h2).symm
    have hgm2 : (g : G) ^ orderOf (QuotientGroup.mk g : Mbar M Q) ∈
        Subgroup.centralizer (Z : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr fun z hz => ?_
      have := hc.conj_Z_of_mem_Q hgm' hz
      exact (mul_inv_eq_iff_eq_mul.mp this).symm
    have e3 : (g : G) = (((g : G) ^ 2)⁻¹) ^ j *
        (g : G) ^ orderOf (QuotientGroup.mk g : Mbar M Q) := by
      rw [hj]
      group
    rw [e3]
    exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.inv_mem _ hg2) j) hgm2
  have hgH : (g : G) ∈ H0 M Z := ⟨g.2, hgcent⟩
  obtain ⟨mK, γ, M₀, hmK, h⟩ := stroth_globalModelDataGF hc.hyp
  obtain ⟨φ, hφπ, hφker, hφiso⟩ := exists_actionHom_H0 hc.hyp h
  set eH : ↥(H0 M Z) := ⟨(e : G), heH⟩ with heHdef
  set gH : ↥(H0 M Z) := ⟨(g : G), hgH⟩ with hgHdef
  set D := φ eH with hDdef
  set T := φ gH with hTdef
  have hD : ∀ x, M₀.Qf (D x) = M₀.Qf x := hφiso eH
  have hT : ∀ x, M₀.Qf (T x) = M₀.Qf x := hφiso gH
  have hDD : D * D = 1 := by
    rw [hDdef, ← map_mul]
    refine (hφker _).mpr ?_
    show (e : G) * (e : G) ∈ Q
    rw [← sq]
    exact hA2.2.2.1
  have hD2 : ∀ x, D (D x) = x := fun x => by
    have := DFunLike.congr_fun hDD x
    simpa using this
  have hrel : D⁻¹ * T * D * T = 1 := by
    have h1 : φ (eH⁻¹ * gH * eH * gH) = 1 := by
      refine (hφker _).mpr ?_
      show (e : G)⁻¹ * (g : G) * (e : G) * (g : G) ∈ Q
      exact hcq'
    simpa [map_mul, map_inv, hDdef, hTdef] using h1
  have hDinv : D⁻¹ = D := inv_eq_of_mul_eq_one_right hDD
  have hDT : ∀ x, D (T x) = T.symm (D x) := by
    intro x
    have h1 := DFunLike.congr_fun hrel x
    rw [hDinv] at h1
    simp only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] at h1
    have h2 : T (D (T x)) = D x := by
      have := congrArg D h1
      rw [hD2] at this
      exact this
    exact (LinearEquiv.eq_symm_apply T).mpr h2
  have hm : Odd (orderOf (QuotientGroup.mk g : Mbar M Q)) := ⟨j, hj⟩
  have hTm : (T : M₀.E →ₗ[GaloisField 2 mK] M₀.E) ^
      orderOf (QuotientGroup.mk g : Mbar M Q) = 1 := by
    refine linearMap_pow_eq_one_of_equiv_pow_eq_one ?_
    rw [hTdef, ← map_pow]
    refine (hφker _).mpr ?_
    show (g : G) ^ orderOf (QuotientGroup.mk g : Mbar M Q) ∈ Q
    exact hgm'
  have hK : 1 < Nat.card (GaloisField 2 mK) := by
    rw [h.card]
    have := hc.hyp.q4
    omega
  have hiff := isA2_iff M₀ h.reg h.card hK D
    (fun x hx => (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 e.2) x).mp hx)
    (fun x hx => by
      have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem e.2)) x).mp hx
      simpa using this)
    (fun x hx => hφπ eH x hx)
  obtain ⟨-, -, hR2, hsing⟩ := hiff.mp hA2
  have hpow := pow_card_sq_sub_one_of_dihedral M₀ hD hT hD2 hDT hm hTm hR2.le hsing
  have hTk : T ^ (Nat.card (GaloisField 2 mK) ^ 2 - 1) = 1 := by
    refine LinearEquiv.ext fun x => ?_
    have h1 := congrArg (fun f : M₀.E →ₗ[GaloisField 2 mK] M₀.E => f x) hpow
    simp only [Module.End.coe_pow] at h1
    rw [LinearEquiv.coe_pow]
    simpa using h1
  have hgk : (g : G) ^ (Nat.card Z ^ 2 - 1) ∈ Q := by
    have h1 : φ (gH ^ (Nat.card (GaloisField 2 mK) ^ 2 - 1)) = 1 := by
      rw [map_pow]
      exact hTk
    have h2 := (hφker _).mp h1
    rw [h.card] at h2
    exact h2
  have hmk : (QuotientGroup.mk g : Mbar M Q) ^ (Nat.card Z ^ 2 - 1) = 1 := by
    rw [← QuotientGroup.mk_pow, hQmem]
    exact hgk
  exact orderOf_dvd_of_pow_eq_one hmk

end CFSG.RankThree.GF2n.Stroth80
