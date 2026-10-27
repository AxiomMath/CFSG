module

public import CFSG.RankThree.PartOne.KF.U4Single
public import CFSG.RankThree.PartOne.KF.U4Model
public import CFSG.RankThree.PartOne.KF.U4Su3
public import CFSG.RankThree.PartOne.S12.InputsCT

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Sec12Three CFSG.LocalAnalysis.ComponentInitial

theorem comm_swap : ∀ a b c d : Fin 4, a ≠ b → c ≠ d →
    Equiv.swap a b * Equiv.swap c d = Equiv.swap c d * Equiv.swap a b →
      Equiv.swap a b ≠ Equiv.swap c d → a ≠ c ∧ a ≠ d ∧ b ≠ c ∧ b ≠ d := by decide

theorem adj_swap : ∀ a b c d : Fin 4, a ≠ b → c ≠ d →
    (Equiv.swap a b * Equiv.swap c d) ^ 3 = 1 → Equiv.swap a b * Equiv.swap c d ≠ 1 →
      (a = c ∧ b ≠ d) ∨ (a = d ∧ b ≠ c) ∨ (b = c ∧ a ≠ d) ∨ (b = d ∧ a ≠ c) := by decide

theorem blk_sup_blk_mulEquiv_su3_of_share {f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 f K)
    (hf : 2 ≤ f) {a b c d : Fin 4} (hab : a ≠ b) (hcd : c ≠ d)
    (hs : (a = c ∧ b ≠ d) ∨ (a = d ∧ b ≠ c) ∨ (b = c ∧ a ≠ d) ∨ (b = d ∧ a ≠ c)) :
    Nonempty (↥(blk h hab ⊔ blk h hcd) ≃* ↥(unitarySU 2 f K 3)) := by
  rcases hs with ⟨rfl, hbd⟩ | ⟨rfl, hbc⟩ | ⟨rfl, had⟩ | ⟨rfl, hac⟩
  ·
    have := blk_sup_blk_mulEquiv_su3 h hf hab.symm hcd hbd
    rwa [blk_symm hab] at this
  ·
    have h1 := blk_sup_blk_mulEquiv_su3 h hf hcd hab hbc.symm
    rwa [sup_comm] at h1
  · exact blk_sup_blk_mulEquiv_su3 h hf hab hcd had
  ·
    have := blk_sup_blk_mulEquiv_su3 h hf hab hcd.symm hac
    rwa [blk_symm hcd] at this

namespace U4Ctx

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f : ℕ} {K : Type} [Field K] (C : U4Ctx p A c L E f K)

theorem refl_conclusions (R : C.Refl) :
    (¬ ∃ f' : ℕ, kExceptional p (kZero p E R.t) f') ∧
    StatedClassicalModel ↥(kZero p E R.t) .PSL 2 2 f ∧
    E ⊓ Subgroup.centralizer (kZero p E R.t : Set G) = autFixedInG E R.t ∧
    autMovedInG E R.t ≤ kZero p E R.t ∧
    ∃ (k : G) (hk : k ∈ Subgroup.normalizer (E : Set G)), k ∈ kZero p E R.t ∧
      E.normalizerMonoidHom ⟨k, hk⟩ = R.t := by
  obtain ⟨hqs, hz, hmod⟩ := blk_model C.hU C.hf2 R.hab
  have hK := R.kZero_eq_blkG hqs hz
  have hmodG : StatedClassicalModel ↥(C.blkG R.hab) .PSL 2 2 f :=
    CFSG.SectionRank.statedClassicalModel_of_mulEquiv (C.blkGEquiv R.hab) hmod
  have hzG : Subgroup.center ↥(C.blkG R.hab) = ⊥ :=
    Refl.center_eq_bot_of_mulEquiv (C.blkGEquiv R.hab) hz
  refine ⟨?_, ?_, R.inf_centralizer_eq hK, ?_, ?_⟩
  · rintro ⟨f', -, -, hf'⟩
    rw [hK] at hf'
    exact not_psu_three_quotient_of_psl_two hmodG hzG hf'
  · rw [hK]
    exact hmodG
  · rw [hK]
    exact R.autMovedInG_le_blkG
  · obtain ⟨k, hk, hkB, hkt⟩ := R.exists_swap_elt
    exact ⟨k, hk, hK ▸ hkB, hkt⟩

include C in
theorem exists_refl {t : MulAut E} (ht : t ∈ reflectionSet p E) (htL : t ∈ torusImage E L) :
    ∃ R : C.Refl, R.t = t := by
  obtain ⟨w, hwL, hwE, rfl⟩ := mem_torusImage_iff.mp htL
  obtain ⟨g, τ, hg, hτ⟩ := C.exists_perm hwL hwE
  obtain ⟨a, b, hab, hτab⟩ := C.exists_swap_of_reflection hwE hg hτ ht.1
  subst hg
  exact ⟨⟨⟨g, τ, hτ, hwE⟩, a, b, hab, hτab⟩, rfl⟩

noncomputable def blkGSupEquiv {a b c' d : Fin 4} (hab : a ≠ b) (hcd : c' ≠ d) :
    ↥(C.blkG hab ⊔ C.blkG hcd) ≃* ↥(blk C.hU hab ⊔ blk C.hU hcd) := by
  have h1 : C.blkG hab ⊔ C.blkG hcd =
      ((blk C.hU hab ⊔ blk C.hU hcd).subgroupOf (unitarySU 2 f K 4)).map C.phi := by
    unfold blkG
    rw [← Subgroup.map_sup, ← Subgroup.subgroupOf_sup (blk_le_unitarySU hab)
      (blk_le_unitarySU hcd)]
  exact (MulEquiv.subgroupCongr h1).trans
    ((Subgroup.equivMapOfInjective _ C.phi C.phi_injective).symm.trans
      (Subgroup.subgroupOfEquivOfLe (sup_le (blk_le_unitarySU hab) (blk_le_unitarySU hcd))))

theorem pair_conclusions (Rs Rt : C.Refl) (hne : Rs.t ≠ Rt.t) :
    (Rs.t * Rt.t = Rt.t * Rs.t → kZero p E Rs.t ≤ Subgroup.centralizer (kZero p E Rt.t : Set G) ∧
      kZero p E Rs.t ⊓ kZero p E Rt.t = ⊥) ∧
    (orderOf (Rs.t * Rt.t) = 3 → CentrallyUThree f ↥(kZero p E Rs.t ⊔ kZero p E Rt.t)) := by
  obtain ⟨hqs, hz, -⟩ := blk_model C.hU C.hf2 Rs.hab
  obtain ⟨hqt, hzt, -⟩ := blk_model C.hU C.hf2 Rt.hab
  have hKs := Rs.kZero_eq_blkG hqs hz
  have hKt := Rt.kZero_eq_blkG hqt hzt
  have hts : (Rs.toPermData.mul Rt.toPermData).t = Rs.t * Rt.t :=
    PermData.t_mul _ _
  have htsr : (Rt.toPermData.mul Rs.toPermData).t = Rt.t * Rs.t :=
    PermData.t_mul _ _
  refine ⟨fun hcomm => ?_, fun hord => ?_⟩
  · have hperm : Equiv.swap Rs.a Rs.b * Equiv.swap Rt.a Rt.b =
        Equiv.swap Rt.a Rt.b * Equiv.swap Rs.a Rs.b := by
      have h1 := (PermData.t_eq_iff C (Rs.toPermData.mul Rt.toPermData)
        (Rt.toPermData.mul Rs.toPermData)).mp (by rw [hts, htsr]; exact hcomm)
      have h2 : Rs.toPermData.τ * Rt.toPermData.τ = Rt.toPermData.τ * Rs.toPermData.τ := h1
      rwa [Rs.hτ', Rt.hτ'] at h2
    have hne' : Equiv.swap Rs.a Rs.b ≠ Equiv.swap Rt.a Rt.b := by
      intro h'
      apply hne
      refine (PermData.t_eq_iff C Rs.toPermData Rt.toPermData).mpr ?_
      rw [Rs.hτ', Rt.hτ']
      exact h'
    obtain ⟨hac, had, hbc, hbd⟩ := comm_swap _ _ _ _ Rs.hab Rt.hab hperm hne'
    rw [hKs, hKt]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨g1, hg1, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨g2, hg2, rfl⟩
      have hg1' : (g1 : GL (Fin 4) K) ∈ blk C.hU Rs.hab := hg1
      have hg2' : (g2 : GL (Fin 4) K) ∈ blk C.hU Rt.hab := hg2
      have hc := blk_comm_of_disjoint Rt.hab Rs.hab hac.symm hbc.symm had.symm hbd.symm hg2' hg1'
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hc
    · rw [eq_bot_iff]
      rintro _ ⟨⟨g1, hg1, rfl⟩, ⟨g2, hg2, h2⟩⟩
      have hg1' : (g1 : GL (Fin 4) K) ∈ blk C.hU Rs.hab := hg1
      have hg2' : (g2 : GL (Fin 4) K) ∈ blk C.hU Rt.hab := hg2
      have h3 : g2 = g1 := C.phi_injective h2
      subst h3
      have hmem : (g2 : GL (Fin 4) K) ∈ blk C.hU Rs.hab ⊓ blk C.hU Rt.hab := ⟨hg1', hg2'⟩
      rw [blk_inf_eq_bot_of_disjoint Rs.hab Rt.hab hac had hbc hbd, Subgroup.mem_bot] at hmem
      have : g2 = 1 := Subtype.ext hmem
      rw [this, map_one]
      exact Subgroup.one_mem _
  · have hord' : orderOf (Equiv.swap Rs.a Rs.b * Equiv.swap Rt.a Rt.b) = 3 := by
      have h1 := PermData.orderOf_t (Rs.toPermData.mul Rt.toPermData)
      rw [hts, hord] at h1
      have h2 : orderOf (Rs.toPermData.τ * Rt.toPermData.τ) = 3 := h1.symm
      rwa [Rs.hτ', Rt.hτ'] at h2
    have hs := adj_swap _ _ _ _ Rs.hab Rt.hab (by rw [← hord']; exact pow_orderOf_eq_one _)
      (by
        intro h1
        rw [h1, orderOf_one] at hord'
        omega)
    obtain ⟨e⟩ := blk_sup_blk_mulEquiv_su3_of_share C.hU C.hf2 Rs.hab Rt.hab hs
    rw [hKs, hKt]
    have hfin : Finite K := C.hU.finite
    refine Or.inl ⟨K, inferInstance, hfin, ?_, ⟨(C.blkGSupEquiv Rs.hab Rt.hab).trans e⟩⟩
    rw [C.hU.card, ← pow_mul, mul_comm]

end U4Ctx

end CFSG.RankThree.PartOne.KFU
