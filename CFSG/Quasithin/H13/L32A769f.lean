module

public import CFSG.Quasithin.H13.L32A769e
public import CFSG.Quasithin.H13.L32A769c
public import CFSG.Quasithin.H13.L32A769d

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem relIndex_conjSub (w : G) (A B : Subgroup G) :
    (conjSub w A).relIndex (conjSub w B) = A.relIndex B :=
  Subgroup.relIndex_map_map_of_injective A B (MulAut.conj w).injective

theorem sup_eq_R1_of_relIndex (h : Hyp147 G T L V) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {W : Subgroup G} (hWR : W ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (h4 : (pCoreOf 2 (hz T V)).relIndex (W ⊔ pCoreOf 2 (hz T V)) = 4) :
    W ⊔ pCoreOf 2 (hz T V) = pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨-, hR4⟩ := R1_le_kz_sup S0 hF h63 h1222 h1332 h1334
  have hQR := pCoreOf_hz_le_R1 h hF
  refine Subgroup.eq_of_le_of_card_ge (sup_le hWR hQR) ?_
  have e1 := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) (W ⊔ pCoreOf 2 (hz T V))
  have e2 := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
  rw [inf_eq_left.mpr le_sup_right, h4] at e1
  rw [inf_eq_left.mpr hQR, hR4] at e2
  omega

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

omit N in
theorem uα_eq (h : Hyp147 G T L V) (hMod : StmtL32NModule) :
    conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) = conjSub ((k : G) * g) (fsuU T V) := by
  rw [conjSub_mul, F8.Uγ, fsuU_eq_conjClosure_hz hMod h]

omit [Finite G] in
theorem dγ_lt : F8.Dγ V (fsuV1 T V) (hz T V) (g : G) < F8.Uγ V (hz T V) (g : G) := by
  refine lt_of_le_of_ne (centralizerMod_le_left _ _ _) fun e => ?_
  have := N.pos
  rw [e] at this
  simp [mIdx] at this

theorem stab_γ (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    stab γ = conjSub (g : G) (hz T V) := by
  rw [← N.setup.edge₁, stab_smul, stab_γ₁ hF.amalgamHypV.le₂]

theorem relIndex_dvd (h : Hyp147 G T L V) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
        pCoreOf 2 (hz T V)) ∣ 4 ∧
      (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
        pCoreOf 2 (hz T V)) ≠ 1 := by
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨-, hR4⟩ := R1_le_kz_sup S0 hF h63 h1222 h1332 h1334
  have hQR := pCoreOf_hz_le_R1 h hF
  have hle := sup_le (N.uα_le hF) hQR
  refine ⟨?_, fun h1 => ?_⟩
  · rw [← hR4, ← Subgroup.relIndex_mul_relIndex _ _ _ le_sup_right hle]
    exact dvd_mul_right _ _
  ·
    have hαQ : conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤ pCoreOf 2 (hz T V) :=
      le_sup_left.trans (Subgroup.relIndex_eq_one.mp h1)
    have hγQ : F8.Uγ V (hz T V) (g : G) ≤ pCoreOf 2 (hz T V) := by
      have := conjSub_mono (k : G)⁻¹ hαQ
      rwa [conjSub_conjSub_inv, conjSub_eq_self_iff.mpr
        (le_normalizer_pCoreOf 2 _ (inv_mem N.mem))] at this
    refine lt_irrefl _ (lt_of_lt_of_le N.dγ_lt fun u hu => ?_)
    have hq := hγQ hu
    rw [hF.pCoreOf_eq_centralizerMod] at hq
    exact ⟨hu, hq.2⟩

theorem conf69 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h64 : Remark14_7_64)
    (h4 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 4) :
    Conf69 G T L V ((k : G) * g) := by
  have hUeq : fsuU T V = conjClosure V (hz T V) := fsuU_eq_conjClosure_hz hMod h
  have hR : conjSub ((k : G) * g) (fsuU T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [← uα_eq (g := g) (k := k) h hMod]
    exact N.uα_le hF
  rw [uα_eq (g := g) (k := k) h hMod] at h4
  have hcomm : ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ≤
      fsuU T V ⊓ conjSub ((k : G) * g) (fsuU T V) := by
    rw [← uα_eq (g := g) (k := k) h hMod, hUeq]
    exact N.commutator_le hF
  have hU : fsuU T V ≤ conjSub ((k : G) * g) (hz T V) := by
    have h1 := (hF.F913_2 N.setup).1.trans ((pCoreOf_le 2 _).trans inf_le_right)
    rw [N.stab_γ hF, ← hUeq] at h1
    have h2 := conjSub_mono (k : G) h1
    rw [hUeq, conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ N.mem), ← hUeq,
      ← conjSub_mul] at h2
    exact h2
  exact ⟨h, hMod, h63, hF, h1222, h1332, h1334, h64, hR,
    sup_eq_R1_of_relIndex h h63 hF h1222 h1332 h1334 hR h4, hcomm, hU⟩

theorem exists_sym69 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h64 : Remark14_7_64) (c : Conf69 G T L V ((k : G) * g)) :
    ∃ x' y : G, Sym69 G T L V ((k : G) * g) x' y := by
  have hyp := hF.amalgamHypV
  have hUeq : fsuU T V = conjClosure V (hz T V) := fsuU_eq_conjClosure_hz hMod h
  have hstabγ₁ : stab (F8.γ₁ T L (hz T V)) = hz T V := stab_γ₁ hyp.le₂
  have hn := hF.not_Vγ_le_ballStab_of_lt N.setup N.dγ_lt
  obtain ⟨δ, δ', k₂, y₀, sk, hy₀γ, hy₀γ₁, hUδ, hUγ, -, -⟩ := hF.exists_symmetric_setup N.setup hn
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ hz T V) (L ⊔ T) (hz T V) V := hF.three_le_b_and_odd.1
  obtain ⟨-, ⟨γ₂, hγ₂nb, hd⟩⟩ :=
    exists_nbrs_of_geodesic hyp.gen sk.critical.geodesic (by omega : 2 ≤ _)
  obtain ⟨h₀, hh₀1, hh₀2⟩ := exists_stab_smul_eq (γ := F8.γ₁ T L (hz T V)) hγ₂nb
    (adj_γ₀_γ₁ (G₀ := (L ⊔ T) ⊔ hz T V) (G₁ := L ⊔ T) (G₂ := hz T V)).symm
  have hh₀H : (h₀ : G) ∈ hz T V := by
    have := mem_stab_of_smul_eq hh₀1
    rwa [hstabγ₁] at this
  have hUH' : ∀ w ∈ hz T V, conjSub w (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    fun w hw => conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ hw)
  have hUH : ∀ w ∈ hz T V, conjSub w (fsuU T V) = fsuU T V := fun w hw => by
    rw [hUeq]
    exact hUH' w hw
  have hQH : ∀ w ∈ hz T V, conjSub w (pCoreOf 2 (hz T V)) = pCoreOf 2 (hz T V) := fun w hw =>
    conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ hw)
  have hHH : ∀ w ∈ hz T V, conjSub w (hz T V) = hz T V := fun w hw =>
    conjSub_eq_self_iff.mpr (Subgroup.le_normalizer hw)
  have hV1H : ∀ w ∈ hz T V, conjSub w (fsuV1 T V) = fsuV1 T V := fun w hw =>
    conjSub_eq_self_iff.mpr (hF.H_normalizes_V₁ hw)
  have hUδ' : conjSub (k₂ : G) (fsuU T V) = conjSub (y₀ : G) (fsuU T V) := by
    rw [hUeq]
    exact hUδ
  have hUγ' : conjSub (y₀ : G)⁻¹ (fsuU T V) = conjSub (g : G) (fsuU T V) := by
    have e := congrArg (conjSub (y₀ : G)⁻¹) hUγ
    rw [conjSub_conjSub_inv] at e
    rw [hUeq]
    exact e.symm
  have hy₀γ' : y₀⁻¹ • F8.γ₁ T L (hz T V) = γ := by rw [← hy₀γ, inv_smul_smul]
  have hy₀δ' : y₀⁻¹ • δ = F8.γ₁ T L (hz T V) := by rw [← hy₀γ₁, inv_smul_smul]
  have hstabδ : stab δ = conjSub (k₂ : G) (hz T V) := by
    rw [← sk.edge₁, stab_smul, hstabγ₁]
  have hgy : (g : G)⁻¹ * (y₀ : G)⁻¹ ∈ hz T V := by
    have h1 : (g⁻¹ * y₀⁻¹) • F8.γ₁ T L (hz T V) = F8.γ₁ T L (hz T V) := by
      rw [mul_smul, hy₀γ', ← N.setup.edge₁, inv_smul_smul]
    have := mem_stab_of_smul_eq h1
    rw [hstabγ₁] at this
    simpa using this
  have hy₀g : (y₀ : G)⁻¹ = (g : G) * ((g : G)⁻¹ * (y₀ : G)⁻¹) := by group
  have hy₀H : conjSub (y₀ : G)⁻¹ (hz T V) = conjSub (g : G) (hz T V) := by
    rw [hy₀g, conjSub_mul, hHH _ hgy]
  have hy₀V1 : conjSub (y₀ : G)⁻¹ (fsuV1 T V) = conjSub (g : G) (fsuV1 T V) := by
    rw [hy₀g, conjSub_mul, hV1H _ hgy]
  have hy₀δ : conjSub (y₀ : G)⁻¹ (conjSub (k₂ : G) (hz T V)) = hz T V := by
    have e := stab_smul y₀⁻¹ δ
    rw [hy₀δ', hstabγ₁, hstabδ] at e
    exact e.symm
  have hW'R : conjSub ((h₀ : G) * k₂) (fsuU T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have h1 := conjSub_mono (h₀ : G) ((hF.F913_2 sk).2 γ₂ hγ₂nb hd)
    rw [← pCoreOf_conjSub, conjSub_inf, ← stab_smul, ← stab_smul, hh₀1, hh₀2, inf_comm,
      hF.F913_1] at h1
    rw [conjSub_mul, hUeq]
    exact h1
  have hWN : conjSub ((h₀ : G) * k₂) (fsuU T V) ≤
      Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    (hW'R.trans ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H)).trans
      (le_normalizer_pCoreOf 2 _)
  have h5 : (conjSub ((k : G) * g) (pCoreOf 2 (hz T V))).relIndex (fsuU T V) = 4 := by
    rw [← Subgroup.inf_relIndex_left, c.inf_QW]
    exact (relIndex_sup_u0 h hMod h63 hF).2
  rw [conjSub_mul, ← hUH _ N.mem, relIndex_conjSub] at h5
  have h4 : (pCoreOf 2 (hz T V)).relIndex (conjSub ((h₀ : G) * k₂) (fsuU T V) ⊔
      pCoreOf 2 (hz T V)) = 4 := by
    rw [A4.relIndex_sup_eq_of_le_normalizer' hWN, conjSub_mul, hUδ', ← conjSub_mul,
      ← relIndex_conjSub ((h₀ : G) * y₀)⁻¹, conjSub_conjSub_inv, mul_inv_rev, conjSub_mul,
      hQH _ (inv_mem hh₀H), ← pCoreOf_conjSub, hy₀H, pCoreOf_conjSub]
    exact h5
  have hW'comm : ⁅fsuU T V, conjSub ((h₀ : G) * k₂) (fsuU T V)⁆ ≤
      fsuU T V ⊓ conjSub ((h₀ : G) * k₂) (fsuU T V) := by
    have h1 := conjSub_mono (h₀ : G) (hF.F913_3 sk (Or.inr rfl) (Or.inr rfl))
    rw [conjSub_inf, ← conjSub_commutator, hUH' _ hh₀H] at h1
    rw [conjSub_mul, hUeq]
    exact h1
  have hW'U : fsuU T V ≤ conjSub ((h₀ : G) * k₂) (hz T V) := by
    have h1 := (hF.F913_2 sk).1.trans ((pCoreOf_le 2 _).trans inf_le_right)
    rw [hstabδ, ← hUeq] at h1
    have h2 := conjSub_mono (h₀ : G) h1
    rw [hUH _ hh₀H, ← conjSub_mul] at h2
    exact h2
  have c' : Conf69 G T L V ((h₀ : G) * k₂) :=
    ⟨h, hMod, h63, hF, h1222, h1332, h1334, h64, hW'R,
      sup_eq_R1_of_relIndex h h63 hF h1222 h1332 h1334 hW'R h4, hW'comm, hW'U⟩
  have hy : (k : G) * (y₀ : G)⁻¹ * (h₀ : G)⁻¹ * ((h₀ : G) * k₂) =
      (k : G) * ((y₀ : G)⁻¹ * k₂) := by group
  refine ⟨(h₀ : G) * k₂, (k : G) * (y₀ : G)⁻¹ * (h₀ : G)⁻¹, c, c', ?_, ?_, ?_, ?_, ?_⟩
  · rw [conjSub_mul, conjSub_mul, hUH _ (inv_mem hh₀H), hUγ', ← conjSub_mul]
  · rw [← conjSub_mul, hy, conjSub_mul, conjSub_mul, hUδ', conjSub_conjSub_inv, hUH _ N.mem]
  · rw [conjSub_mul, conjSub_mul, hHH _ (inv_mem hh₀H), hy₀H, ← conjSub_mul]
  · rw [← conjSub_mul, hy, conjSub_mul, conjSub_mul, hy₀δ, hHH _ N.mem]
  · rw [conjSub_mul, conjSub_mul, hV1H _ (inv_mem hh₀H), hy₀V1, ← conjSub_mul]

theorem relIndex_eq_two (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h64 : Remark14_7_64)
    (h68 : Lemma14_7_68) (h674 : Lemma14_7_67_four) :
    (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hne2
  have h4 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 4 := by
    obtain ⟨hdvd, hne1⟩ := N.relIndex_dvd h h63 hF h1222 h1332 h1334
    obtain ⟨r, hr⟩ : ∃ r, (pCoreOf 2 (hz T V)).relIndex
        (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔ pCoreOf 2 (hz T V)) = r := ⟨_, rfl⟩
    rw [hr] at hdvd hne1 hne2 ⊢
    have hle4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos := Nat.pos_of_dvd_of_pos hdvd (by norm_num)
    interval_cases r <;> omega
  have c := N.conf69 h hMod h63 hF h1222 h1332 h1334 h64 h4
  obtain ⟨x', y, S⟩ := N.exists_sym69 h hMod h63 hF h1222 h1332 h1334 h64 c
  have hV1 := c.not_V1_le h13314
  have hV1' := S.c'.not_V1_le h13314
  have hp : IsPGroup 2 ↥(u0 T V) := (pCoreOf_isPGroup 2 (hz T V)).to_le
    ((centralizerMod_le_left _ _ _).trans
      (by rw [fsuU_eq_conjClosure_hz hMod h]; exact hF.conjClosure_Vp_le_pCoreOf))
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h2le : 2 ≤ Nat.card ↥(u0 T V) := by
    have := Subgroup.card_le_of_le (fsuV1_le_u0 h hMod)
    rwa [hF.card_V₁] at this
  have hle8 : Nat.card ↥(u0 T V) ≤ 8 := (h64 G T L V h).2.2.1
  have hn3 : n ≤ 3 := by
    by_contra hc
    have h16 : 16 ≤ 2 ^ n :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  interval_cases n
  · rw [pow_zero] at hn
    omega
  · rw [pow_one] at hn
    exact S.false_of_u0_eq hV1 (Subgroup.eq_of_le_of_card_ge (fsuV1_le_u0 h hMod)
      (hn.trans hF.card_V₁.symm).le).symm
  · exact S.false_of_card_u0_four h68 h674 hV1 hV1' (by rw [hn]; norm_num)
  · exact S.false_of_card_u0_eight h68 hV1 hV1' (by rw [hn]; norm_num)

end Not1471

end CFSG.Quasithin.H13.L32A
