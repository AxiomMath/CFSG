module

public import CFSG.Quasithin.Vol2.Ch6Sec1ZS

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem ZS_le (_h : Hyp611Nat G T M L V n) : ch6ZS T L V ≤ V := inf_le_left

theorem ZS_ne_bot (h : Hyp611Nat G T M L V n) : ch6ZS T L V ≠ ⊥ := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  set x : ↥V := h.data.E.symm (Multiplicative.ofAdd v) with hx
  have hxZ : (x : G) ∈ ch6ZS T L V := (h.mem_ZS_iff_line hv hle x).mpr ⟨1, by simp [hx]⟩
  intro h0
  rw [h0, Subgroup.mem_bot] at hxZ
  apply hv
  have : x = 1 := Subtype.ext hxZ
  have := congrArg (fun y => Multiplicative.toAdd (h.data.E y)) this
  simpa [hx] using this

theorem T_le_normalizer_ZS (h : Hyp611Nat G T M L V n) :
    T ≤ Subgroup.normalizer (ch6ZS T L V : Set G) := by
  have hTV := h.toHyp611.T_le_normalizer
  have hTTL : T ≤ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ht) x
    have h2 := Subgroup.mem_normalizer_iff.mp
      (h.normal (h.T_le ht)) x
    simp only [Subgroup.mem_inf]
    exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro x
  have h1 := Subgroup.mem_normalizer_iff.mp (hTV ht) x
  have h2 := Subgroup.mem_normalizer_iff.mp
    (F7.normalizer_le_normalizer_centralizer _ (hTTL ht)) x
  simp only [Subgroup.mem_inf]
  exact ⟨fun ⟨a, b⟩ => ⟨h1.mp a, h2.mp b⟩, fun ⟨a, b⟩ => ⟨h1.mpr a, h2.mpr b⟩⟩

theorem S_eq_pCore (h : Hyp611Nat G T M L V n) (h511 : ch6Q T V = pCoreOf 2 (L ⊔ T)) :
    ch6S T L V = (T ⊓ L) ⊔ pCoreOf 2 (L ⊔ T) := by
  rw [← h511]; exact h.S_eq

theorem isSylowIn_S (h : Hyp611Nat G T M L V n) :
    IsSylowIn 2 (ch6S T L V) (Subgroup.centralizer (ch6ZS T L V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTN : IsSylowIn 2 T (Subgroup.normalizer (ch6ZS T L V : Set G)) :=
    E6.isSylowIn_of_le ⟨le_top, h.sylow.1, by rw [Subgroup.relIndex_top_right]; exact h.sylow.2⟩
      h.T_le_normalizer_ZS le_top
  have hCN : Subgroup.centralizer (ch6ZS T L V : Set G) ≤
      Subgroup.normalizer (ch6ZS T L V : Set G) := Subgroup.centralizer_le_normalizer _
  have hnorm : ((Subgroup.centralizer (ch6ZS T L V : Set G)).subgroupOf
      (Subgroup.normalizer (ch6ZS T L V : Set G))).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCN]
    exact F7.normalizer_le_normalizer_centralizer _
  exact hTN.inf_normal hCN hnorm

theorem normalizer_S_le (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V n) :
    Subgroup.normalizer (ch6S T L V : Set G) ≤ M := by
  have hSL : ch6S T L V ⊓ L = T ⊓ L := by
    apply le_antisymm (inf_le_inf_right L inf_le_left)
    have hTLS : T ⊓ L ≤ ch6S T L V := by rw [h.S_eq]; exact le_sup_left
    exact le_inf hTLS inf_le_right
  have hsyl := h.toHyp611.isSylowIn_TL
  refine (h432 G T M L h.simple h.nonabelian h.qtke h.sylow h.maxTwoLocal h.T_le h.maximal
    h.faithful h.L_le h.normal ⟨n, h.two_le, h.lie⟩).2 _ inf_le_left ?_
  rw [hSL]
  exact ⟨hsyl.1, hsyl.2.1, hsyl.2.2⟩

theorem charTwo_normalizer_ZS (h : Hyp611Nat G T M L V n) :
    CharTwo (Subgroup.normalizer (ch6ZS T L V : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsSylowTwoOf T ⊤ :=
    ⟨le_top, h.sylow.1, by rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]; exact h.sylow.2⟩
  have hZp : IsPGroup 2 ↥(ch6ZS T L V) :=
    (F7.isPGroup_of_isElemAbelian h.toHyp611.isElemAbelian).to_le inf_le_left
  refine CT.charTwo_normalizer_of_inf_center h.qtke.2.1 hT hZp ?_
  have hne := inf_omegaOneCenter_ne_bot h.sylow.1 h.toHyp611.isElemAbelian h.toHyp611.le_T
    h.toHyp611.T_le_normalizer h.toHyp611.ne_bot
  intro h0
  apply hne
  rw [eq_bot_iff, ← h0]
  intro z hz
  have hzZ : z ∈ T ⊓ Subgroup.centralizer (T : Set G) :=
    (Subgroup.closure_le _).mpr (fun y hy => hy.1) hz.2
  refine ⟨⟨hz.1, ?_⟩, hzZ⟩
  show z ∈ Subgroup.centralizer ((T ⊓ L : Subgroup G) : Set G)
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  exact (Subgroup.mem_centralizer_iff.mp hzZ.2 t ht.1)

theorem V_le_S (h : Hyp611Nat G T M L V n) : V ≤ ch6S T L V := by
  refine le_inf h.toHyp611.le_T ?_
  intro v hv
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  exact B2F.isElemAbelian_comm h.toHyp611.isElemAbelian hz.1 hv

theorem commutator_V_S_le (h : Hyp611Nat G T M L V n) : ⁅V, ch6S T L V⁆ ≤ ch6ZS T L V := by
  obtain ⟨v, hv, hle⟩ := h.exists_line
  have hstab := h.rhoTL_eq_stab hv hle
  rw [Subgroup.commutator_le]
  intro x hx s hs
  obtain ⟨t, ht, hst⟩ := h.exists_mem_TL_of_mem_S hs
  have htL : t ∈ L := ht.2
  have hy : t * x⁻¹ * t⁻¹ ∈ V :=
    (Subgroup.mem_normalizer_iff.mp (h.data.le_normalizer htL) x⁻¹).mp (V.inv_mem hx)
  have hsx : s * x⁻¹ * s⁻¹ = t * x⁻¹ * t⁻¹ := by
    have hc := Subgroup.mem_centralizer_iff.mp hst (t * x⁻¹ * t⁻¹) hy
    calc s * x⁻¹ * s⁻¹ = (s * t⁻¹) * (t * x⁻¹ * t⁻¹) * (s * t⁻¹)⁻¹ := by group
      _ = (t * x⁻¹ * t⁻¹) * (s * t⁻¹) * (s * t⁻¹)⁻¹ := by rw [hc]
      _ = t * x⁻¹ * t⁻¹ := by group
  have hcomm : ⁅x, s⁆ = x * (t * x⁻¹ * t⁻¹) := by
    rw [commutatorElement_def, ← hsx]; group
  have hmem : x * (t * x⁻¹ * t⁻¹) ∈ V := V.mul_mem hx hy
  rw [hcomm]
  have hρ : h.data.rho ⟨t, htL⟩ ∈ sl2Stab v := by
    rw [← hstab]
    exact Subgroup.mem_map.mpr ⟨⟨t, htL⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  obtain ⟨c, hc⟩ := sub_mem_line_of_mem_sl2Stab hv hρ
    (Multiplicative.toAdd (h.data.E ⟨x, hx⟩))
  refine (h.mem_ZS_iff_line hv hle ⟨_, hmem⟩).mpr ⟨-c, ?_⟩
  have hE : h.data.E ⟨x * (t * x⁻¹ * t⁻¹), hmem⟩ =
      h.data.E ⟨x, hx⟩ * h.data.E ⟨t * x⁻¹ * t⁻¹, hy⟩ := by
    rw [← map_mul]; rfl
  have hEt : Multiplicative.toAdd (h.data.E ⟨t * x⁻¹ * t⁻¹, hy⟩) =
      ((h.data.rho ⟨t, htL⟩ : Matrix.SpecialLinearGroup (Fin 2) h.data.K) :
        Matrix (Fin 2) (Fin 2) h.data.K).mulVec
          (Multiplicative.toAdd (h.data.E ⟨x⁻¹, V.inv_mem hx⟩)) := by
    rw [← h.data.conj_eq_rho, h.data.conj_apply]
    congr 2
  have hEinv : Multiplicative.toAdd (h.data.E ⟨x⁻¹, V.inv_mem hx⟩) =
      -Multiplicative.toAdd (h.data.E ⟨x, hx⟩) := by
    rw [show (⟨x⁻¹, V.inv_mem hx⟩ : ↥V) = (⟨x, hx⟩ : ↥V)⁻¹ from rfl, map_inv]
    rfl
  rw [hE, toAdd_mul, hEt, hEinv, Matrix.mulVec_neg, neg_smul, ← hc]
  abel

theorem normalizer_ZS_eq (h432 : Stmt4_3_2) (h : Hyp611Nat G T M L V n) :
    Subgroup.normalizer (ch6ZS T L V : Set G) =
        Subgroup.centralizer (ch6ZS T L V : Set G) ⊔
          (M ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)) ∧
      Subgroup.normalizer (ch6ZS T L V : Set G) =
        Subgroup.centralizer (ch6ZS T L V : Set G) ⊔
          (ch6MV M V ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)) := by
  have hle : ∀ X : Subgroup G, X ≤ Subgroup.normalizer (ch6ZS T L V : Set G) →
      Subgroup.centralizer (ch6ZS T L V : Set G) ⊔ X ≤
        Subgroup.normalizer (ch6ZS T L V : Set G) :=
    fun X hX => sup_le (Subgroup.centralizer_le_normalizer _) hX
  have hS := h.isSylowIn_S
  have hfrat := exists_mul_of_sylow (Subgroup.centralizer_le_normalizer _)
    (F7.normalizer_le_normalizer_centralizer _) hS.le hS.isPGroup hS.not_dvd_relIndex
  have hNS := h.normalizer_S_le h432
  have hMV : M ⊓ Subgroup.normalizer (ch6ZS T L V : Set G) ≤ ch6MV M V :=
    h.normalizer_le h.ZS_ne_bot h.ZS_le
  have key : Subgroup.normalizer (ch6ZS T L V : Set G) ≤
      Subgroup.centralizer (ch6ZS T L V : Set G) ⊔
        (ch6MV M V ⊓ Subgroup.normalizer (ch6ZS T L V : Set G)) := by
    intro x hx
    obtain ⟨m, hm, c, hc, rfl⟩ := hfrat x hx
    rw [sup_comm]
    refine Subgroup.mul_mem_sup ?_ hc
    exact ⟨hMV ⟨hNS hm.2, hm.1⟩, hm.1⟩
  refine ⟨le_antisymm ?_ (hle _ inf_le_right), le_antisymm key (hle _ inf_le_right)⟩
  exact key.trans (sup_le_sup_left (inf_le_inf_right _ inf_le_left) _)

end Hyp611Nat

end CFSG.Quasithin.H13
