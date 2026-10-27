module

public import CFSG.Sporadic.Co2Smith.QEnum
public import CFSG.Sporadic.Co2Smith.HPLift

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
open CFSG.Certificates.ExtraspecialNF
open scoped Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

noncomputable abbrev FibP :
    Subgroup (Cz × PGcov) := cfgCz.fibSub covMap

theorem rho_cElt
    (e n : ℕ) :
    cfgCz.rho ⟨cElt e n, cElt_mem e n⟩ = ⟨sElt n, sElt_mem_S0 n⟩ := by
  rw [SmithConfig.rho_eq_iff]
  show (⟨sElt n, _⟩ : Cz)⁻¹ * ⟨cElt e n, _⟩ ∈ CFSG.pCore 2 Cz
  rw [pCore_Cz, Subgroup.mem_subgroupOf]
  show (sElt n)⁻¹ * (sElt n * qElt e) ∈ Qsub
  rw [inv_mul_cancel_left]
  exact qElt_mem e

theorem covMap_pLift'
    (n : ℕ) : covMap (pLift n) = ⟨sElt n, sElt_mem_S0 n⟩ :=
  Subtype.ext (covMap_pLift n)

@[expose] noncomputable def fpElt
    (e n : ℕ) : FibP :=
  ⟨(⟨cElt e n, cElt_mem e n⟩, pLift n), by
    rw [SmithConfig.mem_fibSub, rho_cElt, covMap_pLift']⟩

@[expose] noncomputable def hpElt
    (e n : ℕ) : Hprime := QuotientGroup.mk (fpElt e n)

theorem z0_mem_E :
    (⟨z0, z0_mem_Cz⟩ : Cz) ∈ cfgCz.E := by
  show _ ∈ CFSG.pCore 2 Cz
  rw [pCore_Cz, Subgroup.mem_subgroupOf]
  exact Subgroup.subset_closure (Set.mem_insert _ _)

theorem cfgCz_zE :
    ((cfgCz.zE : Cz) : K) = z0 := by
  have hc : (⟨⟨z0, z0_mem_Cz⟩, z0_mem_E⟩ : cfgCz.E) ∈ Subgroup.center cfgCz.E := by
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_singleton_iff.mp g.1.2)
  rcases (cfgCz.mem_center_iff _).mp hc with h | h
  · have := congrArg (fun x : cfgCz.E => ((x : Cz) : K)) h
    exact absurd this z0_ne_one
  · exact (congrArg (fun x : cfgCz.E => ((x : Cz) : K)) h).symm

theorem spinHom_coverZ :
    (spinHom coverZ : Matrix (Fin 8) (Fin 8) ℤ) = -1 := by
  rcases (covMap_eq_one_iff coverX0sq).mp covMap_coverX0sq with h | h
  · exact absurd h coverX0sq_ne_one
  · rw [← h, spinHom_coverX0sq]

theorem coverZ_sq :
    coverZ * coverZ = 1 := by
  rcases (covMap_eq_one_iff (coverZ * coverZ)).mp (by rw [map_mul, covMap_coverZ, one_mul])
    with h | h
  · exact h
  · exact absurd (mul_eq_left.mp h) coverZ_ne_one

theorem coverZ_comm
    (p : PGcov) : p * coverZ = coverZ * p :=
  Subgroup.mem_center_iff.mp (covMap_ker_le_center covMap_coverZ) p

theorem zPair_central
    (u : FibP) :
    u * cfgCz.zPair covMap coverZ covMap_coverZ = cfgCz.zPair covMap coverZ covMap_coverZ * u := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show u.1.1 * (cfgCz.zE : Cz) = (cfgCz.zE : Cz) * u.1.1
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, cfgCz_zE]
    exact (Subgroup.mem_centralizer_singleton_iff.mp u.1.1.2)
  · exact coverZ_comm u.1.2

theorem zPair_sq :
    cfgCz.zPair covMap coverZ covMap_coverZ * cfgCz.zPair covMap coverZ
    covMap_coverZ = 1 := by
  apply Subtype.ext
  refine Prod.ext ?_ ?_
  · show (cfgCz.zE : Cz) * (cfgCz.zE : Cz) = 1
    apply Subtype.ext
    rw [Subgroup.coe_mul, cfgCz_zE]
    exact seedA_mul_self
  · exact coverZ_sq

theorem mem_normalClosure_zPair
    {u : FibP} :
    u ∈ Subgroup.normalClosure {cfgCz.zPair covMap coverZ covMap_coverZ} ↔
      u = 1 ∨ u = cfgCz.zPair covMap coverZ covMap_coverZ := by
  set zp := cfgCz.zPair covMap coverZ covMap_coverZ
  have hn : (Subgroup.zpowers zp).Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [show g * x * g⁻¹ = x by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hc : ∀ m : ℤ, g * zp ^ m = zp ^ m * g := fun m =>
        ((Commute.zpow_right (zPair_central g) m))
      rw [hc k, mul_inv_cancel_right]]
    exact hx
  have hle : Subgroup.normalClosure {zp} ≤ Subgroup.zpowers zp :=
    Subgroup.normalClosure_le_normal (Set.singleton_subset_iff.mpr (Subgroup.mem_zpowers zp))
  constructor
  · intro hu
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (hle hu)
    have h2 : zp ^ (2 : ℤ) = 1 := by rw [zpow_two, zPair_sq]
    rw [zpow_eq_zpow_emod k h2]
    rcases Int.emod_two_eq_zero_or_one k with hk | hk
    · left
      rw [hk, zpow_zero]
    · right
      rw [hk, zpow_one]
  · rintro (rfl | rfl)
    · exact Subgroup.one_mem _
    · exact Subgroup.subset_normalClosure rfl

theorem qElt_mul_z0
    {e : ℕ} (he : e < 512) :
    qElt e * z0 = qElt (if e < 256 then e + 256 else e - 256) := by
  unfold qElt
  rw [nf_mul_z hE_rel]
  split_ifs with h
  · rw [show (e + 256) / 256 = e / 256 + 1 by omega, show (e + 256) % 256 = e % 256 by omega,
      Nat.cast_add, Nat.cast_one]
  · have h1 : e / 256 = 1 := by omega
    rw [show (e - 256) / 256 = 0 by omega, show (e - 256) % 256 = e % 256 by omega, h1]
    simp only [Nat.cast_one, Nat.cast_zero]
    rfl

theorem exists_hpElt
    (y : Hprime) : ∃ e < 512, ∃ n < 1451520, hpElt e n = y := by
  obtain ⟨⟨⟨h, p⟩, hp⟩, rfl⟩ := QuotientGroup.mk_surjective y
  obtain ⟨e, he, n, hn, hcn⟩ := exists_cElt h.2
  have hrho : cfgCz.rho h = ⟨sElt n, sElt_mem_S0 n⟩ := by
    have : h = ⟨cElt e n, cElt_mem e n⟩ := Subtype.ext hcn.symm
    rw [this, rho_cElt]
  have hp' : covMap p = covMap (pLift n) := by
    rw [← (SmithConfig.mem_fibSub _ _ _).mp hp, hrho, covMap_pLift']
  have hker : covMap (p * (pLift n)⁻¹) = 1 := by rw [map_mul, map_inv, hp', mul_inv_cancel]
  rcases (covMap_eq_one_iff _).mp hker with h1 | h1
  · refine ⟨e, he, n, hn, ?_⟩
    rw [hpElt]
    congr 1
    apply Subtype.ext
    refine Prod.ext (Subtype.ext hcn) ?_
    exact (mul_inv_eq_one.mp h1).symm
  · set e' := if e < 256 then e + 256 else e - 256
    refine ⟨e', by simp only [e']; split_ifs <;> omega, n, hn, ?_⟩
    have hq : cElt e' n = cElt e n * z0 := by rw [cElt, cElt, mul_assoc, qElt_mul_z0 he]
    have hval : (⟨(h, p), hp⟩ : FibP) * cfgCz.zPair covMap coverZ covMap_coverZ = fpElt e' n := by
      apply Subtype.ext
      refine Prod.ext (Subtype.ext ?_) ?_
      · show (h : K) * ((cfgCz.zE : Cz) : K) = cElt e' n
        rw [cfgCz_zE, hq, hcn]
      · show p * coverZ = pLift n
        have hp1 : p = coverZ * pLift n := by rw [← h1]; group
        rw [hp1, mul_assoc, coverZ_comm, ← mul_assoc, coverZ_sq, one_mul]
    have hz1 : (QuotientGroup.mk (cfgCz.zPair covMap coverZ covMap_coverZ) : Hprime) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.subset_normalClosure rfl)
    rw [hpElt, ← hval, QuotientGroup.mk_mul, hz1, mul_one]

theorem hpElt_injOn
    {e e' n n' : ℕ} (he : e < 512) (he' : e' < 512) (hn : n < 1451520)
    (hn' : n' < 1451520) (h : hpElt e n = hpElt e' n') : e = e' ∧ n = n' := by
  rw [hpElt, hpElt, QuotientGroup.eq, mem_normalClosure_zPair] at h
  rcases h with h | h
  · have h1 : fpElt e n = fpElt e' n' := inv_mul_eq_one.mp h
    exact cElt_injOn he he' hn hn' (congrArg (fun u : FibP => ((u.1.1 : Cz) : K)) h1)
  · exfalso
    have h1 : fpElt e' n' = fpElt e n * cfgCz.zPair covMap coverZ covMap_coverZ := by
      rw [← h]; group
    have h2 : pLift n' = pLift n * coverZ := congrArg (fun u : FibP => u.1.2) h1
    have h3 : sElt n' = sElt n := by
      have := congrArg (fun p => (covMap p : K)) h2
      simpa only [map_mul, covMap_coverZ, mul_one, covMap_pLift] using this
    have hnn := sElt_injOn hn' hn h3
    subst hnn
    exact coverZ_ne_one (mul_eq_left.mp h2.symm)

end CFSG.Sporadic.Co2Smith
