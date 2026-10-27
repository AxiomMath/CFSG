module

public import CFSG.Quasithin.Vol2.Ch10SecCFacts
public import CFSG.Quasithin.Vol2.Ch10SecKHK3D
public import CFSG.Quasithin.Vol2.Ch10SecKHK3E
public import CFSG.Quasithin.Vol2.Ch10SecKHK3C

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC

open CFSG.Open CFSG.Quasithin.H13 CFSG.QuasithinUnique
open CFSG.Assembly.LowTwoRank (StatedSp)

namespace C10KH

theorem isSylowTwoOf_subgroupOf_top {X : Type} [Group X] {S H : Subgroup X}
    (hS : IsSylowTwoOf S H) : IsSylowTwoOf (S.subgroupOf H) ⊤ := by
  refine ⟨le_top, hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm, ?_⟩
  rw [show ((S.subgroupOf H).subgroupOf ⊤).index = (S.subgroupOf H).index from
    Subgroup.relIndex_top_right _]
  exact hS.2.2

end C10KH

open CFSG.Quasithin CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher CFSG.QuasithinUnique.Setup.X7a
  CFSG.QuasithinUnique.Vol2Native.A312L in
theorem factK3Sp4 : FactK3Sp4 := by
  intro Γ _ _ H R J L V₁ n F _ _ _ _ hR hJ hL hLJ hLne _ _ hV₁L hV₁e hLRV hcomm _ hJV _ hn hF
    ⟨ε⟩ _
  have hn2 : 2 ≤ n := hn
  have : CharP F 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hF
  have hK4' : 4 ≤ Nat.card F := by
    rw [hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hK4 : ∃ s : Finset F, s.card = 4 :=
    CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four hK4'
  have hU : IsSylowTwoOf (R ⊓ J) J :=
    CFSG.Quasithin.A312.isSylowTwoOf_inf_of_subnormal
      (CFSG.Quasithin.subnormal_of_mem_cComp hJ) hR
  have hU₀ : IsSylowTwoOf ((R ⊓ J).subgroupOf J) ⊤ := C10KH.isSylowTwoOf_subgroupOf_top hU
  have hL₀ : L.subgroupOf J ∈ CFSG.Quasithin.lFamily ((R ⊓ J).subgroupOf J) := by
    have h1 : L ∈ CFSG.Quasithin.cComp (L ⊔ (R ⊓ J)) :=
      CFSG.Quasithin.cComp_mem_of_le hL le_sup_left (sup_le_sup_left inf_le_left L)
    have h2 := CFSG.Quasithin.A312.mem_cComp_subgroupOf (sup_le hLJ inf_le_right) h1
    rw [Subgroup.subgroupOf_sup hLJ inf_le_right] at h2
    exact h2
  have hL₀top : L.subgroupOf J ≠ ⊤ := by
    intro h
    exact hLne (le_antisymm hLJ (Subgroup.subgroupOf_eq_top.1 h))
  obtain ⟨ψ, j, hψ⟩ := C10KH.exists_equiv_perfectCore_Q2 hF hn2 ε hU₀ hL₀ hL₀top
  have hD : ∃ Xj, C10KH.RadicalData (perfectCore (Q2 F j)) Xj (Nat.card F) := by
    fin_cases j
    · exact ⟨_, C10KH.radicalData_zero hK4⟩
    · exact ⟨_, C10KH.radicalData_one hK4⟩
  obtain ⟨Xj, hXj⟩ := hD
  have hV₁2 : IsPGroup 2 V₁ := fun g => ⟨1, Subtype.ext (by simpa using hV₁e.2 g g.2)⟩
  have hLV : L ≤ Subgroup.normalizer (V₁ : Set Γ) := le_sup_left.trans hLRV
  have hV1 : V₁ ≠ ⊥ := by
    intro hbot
    have hJN : J ≤ Subgroup.normalizer (L : Set Γ) := by
      intro g hg
      refine hJV (Subgroup.mem_inf.2 ⟨hg, ?_⟩)
      rw [hbot, Subgroup.normalizer_eq_top_iff.2 inferInstance]
      exact Subgroup.mem_top g
    have hnorm : (L.subgroupOf J).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLJ).2 hJN
    have hsimp : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSp 2 F)) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F 2 (by norm_num)
        (Or.inl (Or.inr hK4'))
    have hnt : Nontrivial ↥J := (ε.trans C10KH.projEquivSp).toEquiv.nontrivial
    have hJs : IsSimpleGroup ↥J := IsSimpleGroup.isSimpleGroup_of_surjective
      (ε.trans C10KH.projEquivSp).symm.toMonoidHom (ε.trans C10KH.projEquivSp).symm.surjective
    rcases Subgroup.Normal.eq_bot_or_eq_top (L.subgroupOf J) with h | h
    · apply CFSG.Quasithin.ne_bot_of_mem_cComp (show L ∈ CFSG.Quasithin.cComp (L ⊔ R) from hL)
      exact disjoint_self.1 ((Subgroup.subgroupOf_eq_bot.1 h).mono_right hLJ)
    · exact hL₀top h
  obtain ⟨X, hXle, hXc, hXsc, hXfpf⟩ :=
    C10KH.exists_torus_of_radicalData ψ hψ hXj hLJ hV₁L hV₁2 hLV hcomm hV1
  exact ⟨X, hXle, by rw [hXc, hF], hXsc, hXfpf⟩

end CFSG.Quasithin.Vol2.Ch10.SecC
