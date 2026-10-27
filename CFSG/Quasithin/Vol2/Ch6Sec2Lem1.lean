module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19Aux
public import CFSG.Quasithin.Vol2.Ch6StatementsSec2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

namespace Hyp6Sec2

theorem normalizer_V_le (h432 : Stmt4_3_2) (h : Hyp6Sec2 G T M L V) :
    Subgroup.normalizer (V : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_of_isUniqueM_of_le_twoLocal (h.toHyp611.isUniqueM h432)
    h.toHyp611.sup_le_normalizer ⟨V, h.toHyp611.ne_bot,
      B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian, rfl⟩

theorem centralizer_ZS_le_normalizer_V (h : Hyp6Sec2 G T M L V) :
    Subgroup.centralizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  intro x hx
  exact (h.toHyp611Nat.normalizer_le h.toHyp611Nat.ZS_ne_bot inf_le_left
    ⟨h.centralizer_le hx, Subgroup.centralizer_le_normalizer _ hx⟩).2

theorem normalizer_ZS_le (h432 : Stmt4_3_2) (h : Hyp6Sec2 G T M L V) :
    Subgroup.normalizer (ch6ZS T L V : Set G) ≤ Subgroup.normalizer (V : Set G) := by
  rw [(h.toHyp611Nat.normalizer_ZS_eq h432).2]
  exact sup_le h.centralizer_ZS_le_normalizer_V (inf_le_left.trans inf_le_right)

end Hyp6Sec2

theorem stmt6_2_1 (h432 : Stmt4_3_2) : Stmt6_2_1 := fun _ _ _ _ _ _ _ h =>
  ⟨h.normalizer_ZS_le h432, h.normalizer_V_le h432⟩

theorem stmt6_2_3 (h432 : Stmt4_3_2) (h6111 : Stmt6_1_11) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G), Hyp6Sec2 G T M L V →
      ∀ g : G, V ≤ Subgroup.normalizer (conjSubgroup V g : Set G) →
        conjSubgroup V g ≤ Subgroup.normalizer (V : Set G) → ⁅V, conjSubgroup V g⁆ = ⊥ := by
  intro G _ _ T M L V h g hVg hgV
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne
  have hTMV : IsSylowTwoOf T (ch6MV M V) :=
    E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
      (le_inf h.T_le h.toHyp611.T_le_normalizer) le_top
  have hgMV : conjSubgroup V g ≤ ch6MV M V := le_inf (hgV.trans (h.normalizer_V_le h432)) hgV
  have hg2 : IsPGroup 2 (conjSubgroup V g) :=
    (B2F.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).map _
  obtain ⟨m, hm, hle⟩ := F7.isSylowTwoOf_exists_conj_le hTMV hgMV hg2
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hm.2
  have hW : conjSubgroup V (g * m) = conjSub m⁻¹ (conjSubgroup V g) := by
    show conjSub (g * m)⁻¹ V = conjSub m⁻¹ (conjSub g⁻¹ V)
    rw [mul_inv_rev, conjSub_mul]
  have hWT : conjSubgroup V (g * m) ≤ T := by
    rw [hW]
    have := conjSub_mono m⁻¹ hle
    rwa [conjSub_conjSub_inv] at this
  have hVm : conjSub m⁻¹ V = V := conjSub_eq_of_mem_normalizer' (Subgroup.inv_mem _ hmV)
  have hcomm : ⁅V, conjSubgroup V (g * m)⁆ = conjSub m⁻¹ ⁅V, conjSubgroup V g⁆ := by
    rw [hW, conjSub_commutator', hVm]
  have hne' : ⁅V, conjSubgroup V (g * m)⁆ ≠ ⊥ := by
    rw [hcomm]
    intro h0
    apply hne
    have := congrArg (conjSub m) h0
    rw [conjSub_inv_conjSub] at this
    rw [this]
    unfold conjSub
    exact Subgroup.map_bot _
  have hle' : ⁅V, conjSubgroup V (g * m)⁆ ≤ V ⊓ conjSubgroup V (g * m) := by
    have h1 : ⁅V, conjSubgroup V g⁆ ≤ V ⊓ conjSubgroup V g :=
      le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp hgV)
        (Subgroup.le_normalizer_iff_commutator_le_right.mp hVg)
    rw [hcomm, hW]
    have := conjSub_mono m⁻¹ h1
    rwa [conjSub_inf, hVm] at this
  obtain ⟨-, -, c, hc, hcW⟩ := h6111 G T M L V 2 h.toHyp611Nat (g * m) hWT hne' hle'
  have hcV : conjSubgroup V c = V := by
    show conjSub c⁻¹ V = V
    exact conjSub_eq_of_mem_normalizer'
      (Subgroup.inv_mem _ (h.centralizer_ZS_le_normalizer_V hc))
  rw [hcW, hcV] at hne'
  apply hne'
  exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun v hv =>
    Subgroup.mem_centralizer_iff.mpr fun w hw =>
      B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hw hv

end CFSG.Quasithin.H13
