module

public import CFSG.Certificates.Kernel.B433Alt.Group
public import Certificates.Data.Kernel.B433Alt.Struct
public import Certificates.Kernel.Y442.Model

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.YGroups.Y442Tw CFSG.Certificates.CosetEnumeration
  CertificateChecks.KernelY442

section

theorem card_rho_T : 9904359628800 ≤ Nat.card ((lsub yL).map rho432F) := by
  obtain ⟨h1, h2⟩ := chain_card 9 yLev yPts yOrd yLev_lt yPts_lt yChain_orb yChain_fix
  have hlow := card_ge_of_chain ((lsub yL).map rho432F) 9 _ _ (by
    rintro l hl _ ⟨c, hc, rfl⟩
    exact Subgroup.mem_map_of_mem _ (yGen_mem_lsub (yLev_sub l hl c hc))) h1 _ h2
  have hprod : ∏ l ∈ Finset.range 9, yOrd.getD l 0 = 9904359628800 := by decide
  rwa [hprod] at hlow

theorem stab0 (ρΩ : YGroup 4 3 2 →* Equiv.Perm (Fin 412896))
    (hT : ∀ c ∈ yL, ρΩ (yGen 4 3 2 c) 0 = 0)
    (hF : F432 ∈ ρΩ.ker)
    (htr : ∀ x : Fin 412896, x ∈ MulAction.orbit ρΩ.range (0 : Fin 412896))
    {y : YGroup 4 3 2} (hy : ρΩ y 0 = 0) : ∃ t ∈ lsub yL, rho432F t = rho432F y := by
  have hfin := finite_y432
  classical
  set R := ρΩ.range
  let S0 : Subgroup R := MulAction.stabilizer R (0 : Fin 412896)
  have hS0 : S0.index = 412896 := by
    rw [MulAction.index_stabilizer]
    have : MulAction.orbit R (0 : Fin 412896) = Set.univ := Set.eq_univ_of_forall htr
    rw [this, Set.ncard_univ, Nat.card_eq_fintype_card, Fintype.card_fin]
  set K := S0.comap ρΩ.rangeRestrict
  have hK : K.index = 412896 := by
    rw [Subgroup.index_comap_of_surjective _ ρΩ.rangeRestrict_surjective, hS0]
  have hmemK : ∀ z, z ∈ K ↔ ρΩ z 0 = 0 := fun z => by
    change ρΩ.rangeRestrict z ∈ S0 ↔ _
    rw [MulAction.mem_stabilizer_iff]
    rfl
  set M := ((lsub yL).map rho432F).comap rho432F
  have hkerK : rho432F.ker ≤ ρΩ.ker := by
    rw [ker_rho432F_eq, Subgroup.zpowers_le]
    exact hF
  have hTK : lsub yL ≤ K := by
    rw [lsub, Subgroup.closure_le]
    rintro _ ⟨c, hc, rfl⟩
    exact (hmemK _).2 (hT c hc)
  have hMK : M ≤ K := by
    intro z hz
    obtain ⟨t, ht, he⟩ := hz
    have hk : t⁻¹ * z ∈ rho432F.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, he, inv_mul_cancel]
    have hk' := hkerK hk
    rw [MonoidHom.mem_ker, map_mul, map_inv, inv_mul_eq_one] at hk'
    rw [hmemK, ← hk']
    exact (hmemK t).1 (hTK ht)
  have hM : M.index ≤ 412896 := by
    have h1 : M.index = (((lsub yL).map rho432F).subgroupOf rho432F.range).index := by
      have hMc : M = (((lsub yL).map rho432F).subgroupOf rho432F.range).comap rho432F.rangeRestrict := by
        ext z
        simp [M, Subgroup.mem_subgroupOf]
      rw [hMc, Subgroup.index_comap_of_surjective _ rho432F.rangeRestrict_surjective]
    have h2 := Subgroup.card_mul_index (((lsub yL).map rho432F).subgroupOf rho432F.range)
    rw [card_range_rho432F] at h2
    have h3 : Nat.card (((lsub yL).map rho432F).subgroupOf rho432F.range) =
        Nat.card ((lsub yL).map rho432F) :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (by rintro _ ⟨t, -, rfl⟩; exact ⟨t, rfl⟩)).toEquiv
    rw [h3] at h2
    have h4 := card_rho_T
    rw [h1]
    by_contra hc
    have : 9904359628800 * 412897 ≤ Nat.card ((lsub yL).map rho432F) *
        (((lsub yL).map rho432F).subgroupOf rho432F.range).index :=
      Nat.mul_le_mul h4 (by omega)
    omega
  have hKM : K ≤ M := by
    have h := Subgroup.relIndex_mul_index hMK
    rw [hK] at h
    have hMi : M.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have hpos : 0 < M.relIndex K := Nat.pos_of_ne_zero fun h0 => by
      rw [h0, zero_mul] at h
      exact hMi h.symm
    have h1 : M.relIndex K = 1 := by
      rcases Nat.lt_or_ge 1 (M.relIndex K) with hl | hl
      · have : 2 * 412896 ≤ M.relIndex K * 412896 := Nat.mul_le_mul_right _ hl
        omega
      · omega
    exact Subgroup.relIndex_eq_one.1 h1
  obtain ⟨t, ht, he⟩ := hKM ((hmemK y).2 hy)
  exact ⟨t, ht, he⟩

end

end CertificateChecks.KernelB433

end
