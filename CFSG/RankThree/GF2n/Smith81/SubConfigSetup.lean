module

public import CFSG.RankThree.GF2n.Smith81.ERecursion
public import CFSG.RankThree.GF2n.Smith81.SubConfigFrob
public import CFSG.RankThree.GF2n.Smith81.Sec1Width1
public import CFSG.RankThree.GF2n.Smith81.TiSylow

public section

namespace CFSG.RankThree.GF2n.Smith81.SubCfg

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81

variable {G : Type} [Group G]

section Bar

variable {H Q : Subgroup G} [(Q.subgroupOf H).Normal]

theorem bar_mono {S T : Subgroup G} (h : S ≤ T) : bar H Q S ≤ bar H Q T :=
  Subgroup.map_mono fun _ hx => h hx

theorem bar_le_normalizer {S T : Subgroup G} (hST : S ≤ Subgroup.normalizer (T : Set G)) :
    bar H Q S ≤ Subgroup.normalizer (bar H Q T : Set (↥H ⧸ Q.subgroupOf H)) := by
  have h1 : S.subgroupOf H ≤ Subgroup.normalizer ((T.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have := Subgroup.mem_normalizer_iff.mp (hST (Subgroup.mem_subgroupOf.mp hx)) (n : G)
    simpa only [SetLike.mem_coe, Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
      using this
  exact (Subgroup.map_mono h1).trans (Subgroup.le_normalizer_map _)

@[expose] noncomputable def barMap {S : Subgroup G} (hSH : S ≤ H) : ↥S →* ↥(bar H Q S) :=
  ((QuotientGroup.mk' (Q.subgroupOf H)).comp (Subgroup.inclusion hSH)).codRestrict (bar H Q S)
    fun x => Subgroup.mem_map.mpr ⟨Subgroup.inclusion hSH x, x.2, rfl⟩

theorem barMap_surjective {S : Subgroup G} (hSH : S ≤ H) :
    Function.Surjective (barMap (Q := Q) hSH) := by
  rintro ⟨y, hy⟩
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hy
  exact ⟨⟨(x : G), hx⟩, rfl⟩

theorem barMap_mem {S T : Subgroup G} (hSH : S ≤ H) {x : ↥S} (hx : (x : G) ∈ T) :
    ((barMap (Q := Q) hSH x : ↥(bar H Q S)) : ↥H ⧸ Q.subgroupOf H) ∈ bar H Q T :=
  Subgroup.mem_map.mpr ⟨Subgroup.inclusion hSH x, hx, rfl⟩

end Bar

theorem normalizer_le_normalizer_cen {X : Type} [Group X] (P : Subgroup X) :
    Subgroup.normalizer (P : Set X) ≤ Subgroup.normalizer (cen P : Set X) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff] at hx ⊢
  intro y
  simp only [SetLike.mem_coe, cen_eq, Subgroup.mem_inf, Subgroup.mem_centralizer_iff] at hx ⊢
  constructor
  · rintro ⟨hyP, hyC⟩
    refine ⟨(hx y).mp hyP, fun w hw => ?_⟩
    have hw' : x⁻¹ * w * x ∈ P := (hx _).mpr (by simpa [mul_assoc] using hw)
    have h := hyC _ hw'
    calc w * (x * y * x⁻¹) = x * ((x⁻¹ * w * x) * y) * x⁻¹ := by group
      _ = x * (y * (x⁻¹ * w * x)) * x⁻¹ := by rw [h]
      _ = x * y * x⁻¹ * w := by group
  · rintro ⟨hyP, hyC⟩
    refine ⟨(hx y).mpr hyP, fun w hw => ?_⟩
    have h := hyC _ ((hx w).mp hw)
    have h2 : x * (w * y) * x⁻¹ = x * (y * w) * x⁻¹ := by
      calc x * (w * y) * x⁻¹ = x * w * x⁻¹ * (x * y * x⁻¹) := by group
        _ = x * y * x⁻¹ * (x * w * x⁻¹) := h
        _ = x * (y * w) * x⁻¹ := by group
    simpa using h2

theorem semilinAct_normalizer {X : Type} [Group X] {Y : Subgroup X}
    (hF : FrobClause (Subgroup.normalizer (Y : Set X)) Y) :
    SemilinAct (Subgroup.normalizer (Y : Set X)) Y := by
  obtain ⟨⟨K, hK, hfin, -, e, h⟩, -⟩ := hF
  exact ⟨fun m hm y hy => (Subgroup.mem_normalizer_iff.mp hm y).mp hy, K, hK, hfin, e, h⟩

section Setup

variable [Finite G] {M Q Z B : Subgroup G} {t : G}

theorem exists_mem_conj_of_one_lt {L : Subgroup G} (h : 1 < Nat.card (Nt M L t)) :
    ∃ m ∈ M, t ∈ conjSubgroup m L := by
  by_contra hne
  push Not at hne
  have hR : Rt M L t = ⊥ := by
    refine iSup_eq_bot.mpr fun m => iSup_eq_bot.mpr fun hm => iSup_eq_bot.mpr fun ht => ?_
    exact absurd ht (hne m hm)
  have hN : Nt M L t = ⊥ := by
    have hle : Nt M L t ≤ Rt M L t := (inSubgroup_pCore_two (Rt M L t)).2.1
    rw [hR] at hle
    exact le_bot_iff.mp hle
  rw [hN, Subgroup.card_bot] at h
  exact lt_irrefl 1 h

theorem Q_le_Rt_of_mem (H : StrothHyp M Q Z) {L : Subgroup G} (hQL : Q ≤ L) {m : G}
    (hm : m ∈ M) (ht : t ∈ conjSubgroup m L) : Q ≤ Rt M L t := by
  have hQm : Q ≤ conjSubgroup m L := by
    intro x hx
    rw [mem_conjSubgroup]
    refine hQL ?_
    have := (Subgroup.mem_normalizer_iff.mp (H.Q_normal.2 (inv_mem hm)) x).mp hx
    simpa using this
  exact hQm.trans (le_iSup_of_le m (le_iSup_of_le hm (le_iSup_of_le ht le_rfl)))

theorem Q_le_Nt_of (H : StrothHyp M Q Z) {L : Subgroup G} (hRM : Rt M L t ≤ M)
    (hQR : Q ≤ Rt M L t) : Q ≤ Nt M L t := by
  haveI : (Q.subgroupOf (Rt M L t)).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer fun x hx => H.Q_normal.2 (hRM hx)
  have hp : IsPGroup 2 (Q.subgroupOf (Rt M L t)) :=
    (isPGroup_Q' H).comap_of_injective _ (Subgroup.subtype_injective _)
  have hle : Q.subgroupOf (Rt M L t) ≤ CFSG.pCore 2 ↥(Rt M L t) :=
    le_sSup ⟨inferInstance, hp⟩
  calc Q = (Q.subgroupOf (Rt M L t)).map (Rt M L t).subtype :=
        (Subgroup.map_subgroupOf_eq_of_le hQR).symm
    _ ≤ Nt M L t := Subgroup.map_mono hle

theorem Q_le_Nt_of_one_lt (hc : Ctx M Q Z B) (h : 1 < Nat.card (Nt M (LB M Q B) t)) :
    Q ≤ Nt M (LB M Q B) t := by
  obtain ⟨m, hm, ht⟩ := exists_mem_conj_of_one_lt h
  exact Q_le_Nt_of hc.hyp (Rt_le_M hc.LB_le_M t)
    (Q_le_Rt_of_mem hc.hyp le_sup_left hm ht)

theorem Nt_le_Rt (M L : Subgroup G) (t : G) : Nt M L t ≤ Rt M L t :=
  (inSubgroup_pCore_two (Rt M L t)).2.1

theorem Rt_le_H0 (hc : Ctx M Q Z B) (t : G) : Rt M (LB M Q B) t ≤ H0 M Z :=
  (Rt_le_Lgen M (LB M Q B) t).trans (Lgen_le_H0 hc)

variable [(Q.subgroupOf (H0 M Z)).Normal]

theorem bar_Rt_le_subCfgM (L : Subgroup G) (t : G) :
    bar (H0 M Z) Q (Rt M L t) ≤ SubCfgM M Q Z (Nt M L t) :=
  (bar_le_normalizer (inSubgroup_pCore_two (Rt M L t)).2.2).trans
    (normalizer_le_normalizer_cen _)

theorem subCfgQ_le_bar_Rt (L : Subgroup G) (t : G) :
    SubCfgQ M Q Z (Nt M L t) ≤ bar (H0 M Z) Q (Rt M L t) :=
  bar_mono (Nt_le_Rt M L t)

theorem bar_Rt_centralizes (hc : Ctx M Q Z B) (t : G)
    (hF : FrobClause (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    {X : Type} [Group X] (hX : Group.IsPerfect X)
    [((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal]
    (e : ↥(Rt M (LB M Q B) t) ⧸ (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t) ≃* X) :
    ∀ r ∈ bar (H0 M Z) Q (Rt M (LB M Q B) t), ∀ z ∈ SubCfgZ M Q Z (Nt M (LB M Q B) t),
      r * z = z * r := by
  have hRH := Rt_le_H0 hc t
  refine centralizes_of_semilinAct_of_kills (C := SubCfgQ M Q Z (Nt M (LB M Q B) t))
    (semilinAct_normalizer hF) (bar_Rt_le_subCfgM (LB M Q B) t) ?_
    (killsAbelian_of_surjective hX _ e (barMap hRH) (barMap_surjective hRH)
      fun x hx => barMap_mem hRH (Subgroup.mem_subgroupOf.mp hx))
  intro c hc' y hy
  have hy' : y ∈ Subgroup.centralizer ((SubCfgQ M Q Z (Nt M (LB M Q B) t) : Subgroup _) :
      Set _) := by
    have := hy
    rw [SubCfgZ, cen_eq] at this
    exact this.2
  exact Subgroup.mem_centralizer_iff.mp hy' c hc'

theorem card_bar_Rt_eq (hc : Ctx M Q Z B) (t : G) (hQN : Q ≤ Nt M (LB M Q B) t)
    [((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal] :
    Nat.card (bar (H0 M Z) Q (Rt M (LB M Q B) t)) =
      Nat.card (SubCfgQ M Q Z (Nt M (LB M Q B) t)) *
        Nat.card (↥(Rt M (LB M Q B) t) ⧸
          (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) := by
  have hNR := Nt_le_Rt M (LB M Q B) t
  have h1 := bar_card_mul_card_of_le (M := H0 M Z) (hQN.trans hNR) (Rt_le_H0 hc t)
  have h2 := bar_card_mul_card_of_le (M := H0 M Z) hQN (Nt_le_H0 hc t)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup
    ((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t))
  have h4 : Nat.card ((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) =
      Nat.card (Nt M (LB M Q B) t) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNR).toEquiv
  rw [h4, ← h2] at h3
  have hQ : 0 < Nat.card Q := Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hQ ?_
  rw [h1, h3]
  ring

theorem exists_card_quot_dvd_GL (hc : Ctx M Q Z B) (t : G) (hQN : Q ≤ Nt M (LB M Q B) t)
    (hH' : StrothHyp (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgQ M Q Z (Nt M (LB M Q B) t))
      (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    (hF : FrobClause (SubCfgM M Q Z (Nt M (LB M Q B) t)) (SubCfgZ M Q Z (Nt M (LB M Q B) t)))
    {X : Type} [Group X] (hX : Group.IsPerfect X)
    [((Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)).Normal]
    (e : ↥(Rt M (LB M Q B) t) ⧸ (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t) ≃* X) :
    ∃ d : ℕ, Nat.card (SubCfgQ M Q Z (Nt M (LB M Q B) t)) =
        Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)) ^ (d + 1) ∧
      Nat.card (↥(Rt M (LB M Q B) t) ⧸ (Nt M (LB M Q B) t).subgroupOf (Rt M (LB M Q B) t)) ∣
        ∏ i : Fin d, (Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)) ^ d -
          Nat.card (SubCfgZ M Q Z (Nt M (LB M Q B) t)) ^ (i : ℕ)) := by
  classical
  set N := Nt M (LB M Q B) t
  set R := Rt M (LB M Q B) t
  set Q' := SubCfgQ M Q Z N
  set Z' := SubCfgZ M Q Z N
  set M' := SubCfgM M Q Z N
  set R' := bar (H0 M Z) Q R
  obtain ⟨K, _, _, _, γ, M₀, hglob⟩ := stroth_globalModelData hH'
  obtain ⟨φ, -, hφ, -⟩ := exists_actionHom_H0 hH' hglob
  have hRM : R' ≤ M' := bar_Rt_le_subCfgM (LB M Q B) t
  have hRC := bar_Rt_centralizes hc t hF hX e
  have hRH : R' ≤ H0 M' Z' := fun r hr =>
    ⟨hRM hr, Subgroup.mem_centralizer_iff.mpr fun z hz => (hRC r hr z hz).symm⟩
  have hQR : Q' ≤ R' := subCfgQ_le_bar_Rt (LB M Q B) t
  let ψ : ↥R' →* (M₀.E ≃ₗ[K] M₀.E) := φ.comp (Subgroup.inclusion hRH)
  have hker : ψ.ker = Q'.subgroupOf R' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ (Subgroup.inclusion hRH x)
  have hkc : Nat.card ψ.ker = Nat.card Q' := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQR).toEquiv
  have h1 := Subgroup.card_ker_mul_card_range ψ
  rw [hkc, card_bar_Rt_eq hc t hQN] at h1
  have hrange : Nat.card ψ.range =
      Nat.card (↥R ⧸ N.subgroupOf R) :=
    Nat.eq_of_mul_eq_mul_left Nat.card_pos h1
  have hZQ' : Z' ≤ Q' := Subgroup.map_subtype_le _
  have hKZ : Nat.card K = Nat.card Z' := hglob.card
  refine ⟨Module.finrank K M₀.E, ?_, ?_⟩
  · rw [card_Q_eq M₀ hZQ', Module.natCard_eq_pow_finrank (K := K), hKZ, pow_succ]
  · rw [← hrange, ← hKZ, ← card_linearEquiv rfl]
    exact Subgroup.card_subgroup_dvd_card ψ.range

end Setup

end CFSG.RankThree.GF2n.Smith81.SubCfg
