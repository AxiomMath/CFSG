module

public import CFSG.Quasithin.H13.L32A769f

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem comm_mem_of_pCoreOf (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {q u : G} (hq : q ∈ pCoreOf 2 (hz T V))
    (hu : u ∈ fsuU T V) : q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := by
  have hqC : q ∈ centralizerMod (fsuV1 T V) (hz T V) (conjClosure V (hz T V)) := by
    rw [← hF.pCoreOf_eq_centralizerMod]
    exact hq
  exact hqC.2.2 u (fsuU_eq_conjClosure_hz hMod h ▸ hu)

theorem hz_le_normalizer_U (h : Hyp147 G T L V) (hMod : StmtL32NModule) :
    hz T V ≤ Subgroup.normalizer (fsuU T V : Set G) := by
  rw [fsuU_eq_conjClosure_hz hMod h]
  exact le_normalizer_conjClosure V _

theorem comm_mem_of_R1 (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {r v : G}
    (hr : r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) (hv : v ∈ V) :
    r * v * r⁻¹ * v⁻¹ ∈ fsuV1 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact commutator_le_of_irreducible (pCoreOf_isPGroup 2 _) (pCoreOf_le 2 _)
    hF.L₁T_normalizes_Vp (hF.L₁T_le_H.trans hF.H_normalizes_V₁) (le_normalizer_pCoreOf 2 _)
    hF.V₁_le_Vp hF.isPGroup_Vp
    (HypF91.le_normalizer_of_isElemAbelian_le hF.elemAbelian_Vp hF.V₁_le_Vp) hF.irred r hr v hv

theorem comm_mul_comm (h : Hyp147 G T L V) (hMod : StmtL32NModule) {s : G} (hs : s ∈ hz T V)
    {u₁ u₂ : G} (hu₁ : u₁ ∈ fsuU T V) (hu₂ : u₂ ∈ fsuU T V) :
    u₁ * s * u₁⁻¹ * s⁻¹ * (u₂ * s * u₂⁻¹ * s⁻¹) = u₁ * u₂ * s * (u₁ * u₂)⁻¹ * s⁻¹ := by
  have hcomm : ∀ {a b : G}, a ∈ fsuU T V → b ∈ fsuU T V → a * b = b * a :=
    fun ha hb => F7.isElemAbelian_comm (isElemAbelian_fsuU_of h hMod) ha hb
  have hN := hz_le_normalizer_U h hMod hs
  have ha : s * u₁⁻¹ * s⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp (inv_mem hu₁)
  have hb : s * u₂⁻¹ * s⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp hN _).mp (inv_mem hu₂)
  calc u₁ * s * u₁⁻¹ * s⁻¹ * (u₂ * s * u₂⁻¹ * s⁻¹)
        = u₁ * ((s * u₁⁻¹ * s⁻¹) * u₂) * (s * u₂⁻¹ * s⁻¹) := by group
    _ = u₁ * (u₂ * (s * u₁⁻¹ * s⁻¹)) * (s * u₂⁻¹ * s⁻¹) := by rw [hcomm ha hu₂]
    _ = u₁ * u₂ * ((s * u₁⁻¹ * s⁻¹) * (s * u₂⁻¹ * s⁻¹)) := by group
    _ = u₁ * u₂ * ((s * u₂⁻¹ * s⁻¹) * (s * u₁⁻¹ * s⁻¹)) := by rw [hcomm ha hb]
    _ = u₁ * u₂ * s * (u₁ * u₂)⁻¹ * s⁻¹ := by group

theorem f4_key5 : ∀ a b : Fin 2 → RuType.F4, a + b + -(b + -a) = 0 := by
  decide

theorem exists_comm_mem_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {s : G} (hs : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) {v : G} (hv : v ∈ V) :
    ∃ u ∈ fsuU T V, v * (u * s * u⁻¹ * s⁻¹)⁻¹ ∈ u0 T V := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  obtain ⟨hR1KQ, -⟩ := R1_le_kz_sup S0 hF h63 h1222 h1332 h1334
  obtain ⟨hKU, π, β, -, hπk, hβs, hβk, hβe⟩ := isL24Section_u0 h hMod h63
  have hU0U : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hV1U0 := fsuV1_le_u0 h hMod
  have hHV1 : hz T V ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hQR := pCoreOf_hz_le_R1 h hF
  have hUH := hz_le_normalizer_U h hMod
  have hKQ : kz T V ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
    (oTwoUpper_le _).trans (le_normalizer_pCoreOf 2 _)
  have hs' := hR1KQ hs
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hKQ] at hs'
  obtain ⟨k, hk, q, hq, rfl⟩ := hs'
  have hkH : k ∈ hz T V := oTwoUpper_le _ hk
  have hqH : q ∈ hz T V := pCoreOf_le 2 _ hq
  have hkR : k ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [show k = k * q * q⁻¹ by group]
    exact mul_mem hs (inv_mem (hQR hq))
  have hπ2 : π ⟨k, hk⟩ ^ 2 = 1 := by
    obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V) ⊔ T)) ⟨k, hkR⟩
    have hk2 : k ^ 2 ^ n = 1 := by simpa using congrArg Subtype.val hn
    refine sl24_sq_of_two_pow _ n ?_
    rw [← map_pow]
    have : (⟨k, hk⟩ : ↥(kz T V)) ^ 2 ^ n = 1 := Subtype.ext (by simpa using hk2)
    rw [this, map_one]
  have hπ1 : π ⟨k, hk⟩ ≠ 1 := by
    intro h1
    have h2 : (⟨k, hk⟩ : ↥(kz T V)) ∈ π.ker := h1
    rw [hπk, Subgroup.mem_subgroupOf] at h2
    have hkQ : k ∈ pCoreOf 2 (hz T V) :=
      A4.pCoreOf_le_of_subnormal 2 (A4.subnormal_of_normal (oTwoUpper_le _)
        ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le _)).mpr
          (le_normalizer_oTwoUpper _))) h2
    exact hsQ (mul_mem hkQ hq)
  have hvU := hVU hv
  have hkv : k * v * k⁻¹ * v⁻¹ ∈ fsuV1 T V := by
    have h1 := comm_mem_of_R1 hF hs hv
    have h2 : q⁻¹ * v * q⁻¹⁻¹ * v⁻¹ ∈ fsuV1 T V :=
      comm_mem_of_pCoreOf h hMod hF (inv_mem hq) hvU
    have h3 : (k * q) * (q⁻¹ * v * q⁻¹⁻¹ * v⁻¹) * (k * q)⁻¹ ∈ fsuV1 T V :=
      (Subgroup.mem_normalizer_iff.mp (hHV1 (mul_mem hkH hqH)) _).mp h2
    rw [show k * v * k⁻¹ * v⁻¹ = (k * q) * (q⁻¹ * v * q⁻¹⁻¹ * v⁻¹) * (k * q)⁻¹ *
      (k * q * v * (k * q)⁻¹ * v⁻¹) by group]
    exact mul_mem h3 h1
  have hkv' : k * v * k⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hKU hk) v).mp hvU
  have hfix : (π ⟨k, hk⟩ : Matrix (Fin 2) (Fin 2) RuType.F4).mulVec
      (Multiplicative.toAdd (β ⟨v, hvU⟩)) = Multiplicative.toAdd (β ⟨v, hvU⟩) := by
    have e1 := hβe ⟨k, hk⟩ ⟨v, hvU⟩ ⟨_, hkv'⟩ rfl
    have hc : (⟨k * v * k⁻¹, hkv'⟩ : ↥(fsuU T V)) =
        ⟨k * v * k⁻¹ * v⁻¹, hU0U (hV1U0 hkv)⟩ * ⟨v, hvU⟩ := Subtype.ext (by simp)
    have hc1 : β ⟨k * v * k⁻¹ * v⁻¹, hU0U (hV1U0 hkv)⟩ = 1 :=
      (l24_ker_iff hβk _).mpr (hV1U0 hkv)
    rw [hc, map_mul, hc1, one_mul] at e1
    have := congrArg Multiplicative.toAdd e1
    rw [toAdd_ofAdd] at this
    exact this.symm
  obtain ⟨w, hw⟩ := sl24_fix_comm_exists _ hπ2 hπ1 _ hfix
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd w)
  refine ⟨u, u.2, ?_⟩
  set y : G := q * (u : G)⁻¹ * q⁻¹ with hy
  have hyU : y ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hUH hqH) _).mp (inv_mem u.2)
  have hyu : y * (u : G) ∈ fsuV1 T V := by
    have := comm_mem_of_pCoreOf h hMod hF hq (inv_mem u.2)
    rwa [show q * (u : G)⁻¹ * q⁻¹ * (u : G)⁻¹⁻¹ = y * u by rw [hy, inv_inv]] at this
  have hky : k * y * k⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp (hKU hk) y).mp hyU
  have hβy : β ⟨y, hyU⟩ = (β u)⁻¹ := by
    have e : (⟨y, hyU⟩ : ↥(fsuU T V)) = ⟨y * u, hU0U (hV1U0 hyu)⟩ * u⁻¹ :=
      Subtype.ext (by simp)
    rw [e, map_mul, map_inv, (l24_ker_iff hβk _).mpr (hV1U0 hyu), one_mul]
  have e2 := hβe ⟨k, hk⟩ ⟨y, hyU⟩ ⟨_, hky⟩ rfl
  have hvm : v * ((u : G) * (k * q) * (u : G)⁻¹ * (k * q)⁻¹)⁻¹ ∈ fsuU T V := by
    rw [show (u : G) * (k * q) * (u : G)⁻¹ * (k * q)⁻¹ = u * (k * y * k⁻¹) by rw [hy]; group]
    exact mul_mem hvU (inv_mem (mul_mem u.2 hky))
  refine (l24_ker_iff hβk ⟨_, hvm⟩).mp ?_
  have e3 : (⟨v * ((u : G) * (k * q) * (u : G)⁻¹ * (k * q)⁻¹)⁻¹, hvm⟩ : ↥(fsuU T V)) =
      ⟨v, hvU⟩ * (u * ⟨_, hky⟩)⁻¹ := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hy]
    group
  rw [e3, map_mul, map_inv, map_mul, e2, hβy, hu]
  apply Multiplicative.toAdd.injective
  simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd, toAdd_one, Matrix.mulVec_neg]
  rw [← hw]
  exact f4_key5 _ _

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem uα_le_normalizer (h : Hyp147 G T L V) (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤
      Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
  ((N.uα_le hF).trans ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H)).trans
    (le_normalizer_pCoreOf 2 _)

theorem exists_mem_not_mem (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    ∃ s ∈ conjSub ((k : G) * g) (fsuU T V), s ∉ pCoreOf 2 (hz T V) ∧
      ∀ w ∈ conjSub ((k : G) * g) (fsuU T V),
        w ∈ pCoreOf 2 (hz T V) ∨ s⁻¹ * w ∈ pCoreOf 2 (hz T V) := by
  have hWN := N.uα_le_normalizer h hF
  rw [A4.relIndex_sup_eq_of_le_normalizer' hWN] at h2
  rw [uα_eq (g := g) (k := k) h hMod] at h2
  obtain ⟨s, hsW, hsQ⟩ : ∃ s ∈ conjSub ((k : G) * g) (fsuU T V), s ∉ pCoreOf 2 (hz T V) := by
    by_contra hc
    push Not at hc
    rw [Subgroup.relIndex_eq_one.mpr (fun x hx => hc x hx)] at h2
    exact absurd h2 (by norm_num)
  refine ⟨s, hsW, hsQ, fun w hw => ?_⟩
  by_cases hwQ : w ∈ pCoreOf 2 (hz T V)
  · exact Or.inl hwQ
  · right
    have key := (Subgroup.mul_mem_iff_of_index_two h2 (a := (⟨s, hsW⟩ : ↥(conjSub ((k : G) * g)
      (fsuU T V)))⁻¹) (b := ⟨w, hw⟩)).mpr
    have h3 := key ⟨fun h' => absurd (by
      have := inv_mem (Subgroup.mem_subgroupOf.mp h')
      simpa using this) hsQ, fun h' => absurd (Subgroup.mem_subgroupOf.mp h') hwQ⟩
    rw [Subgroup.mem_subgroupOf] at h3
    simpa using h3

theorem relIndex_DH (h : Hyp147 G T L V) (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    (F8.DH V (fsuV1 T V) (hz T V) (g : G)).relIndex (conjClosure V (hz T V)) = 2 := by
  have hWN := N.uα_le_normalizer h hF
  have hγ : (F8.Dγ V (fsuV1 T V) (hz T V) (g : G)).relIndex (F8.Uγ V (hz T V) (g : G)) = 2 := by
    rw [A4.relIndex_sup_eq_of_le_normalizer' hWN, ← Subgroup.inf_relIndex_left] at h2
    rw [hF.Dγ_eq_inf_pCoreOf N.setup, ← relIndex_conjSub (k : G), conjSub_inf,
      conjSub_eq_self_iff.mpr (le_normalizer_pCoreOf 2 _ N.mem)]
    exact h2
  have hm1 : mIdx (F8.Uγ V (hz T V) (g : G)) (F8.Dγ V (fsuV1 T V) (hz T V) (g : G)) = 1 := by
    unfold mIdx
    rw [hγ]
    simp
  have hUp : IsPGroup 2 ↥(conjClosure V (hz T V)) := isPGroup_of_isElemAbelian hF.F911_3
  have hpos := mIdx_pos_of_lt_of_isPGroup hUp (hF.lemma_14_5_17 N.setup)
  have hle := N.le
  rw [HypF98.relIndex_eq_two_pow_mIdx hUp, show mIdx (conjClosure V (hz T V))
    (F8.DH V (fsuV1 T V) (hz T V) (g : G)) = 1 by omega]
  norm_num

theorem relIndex_D (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    (centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (fsuU T V)
      (conjSub ((k : G) * g) (fsuU T V))).relIndex (fsuU T V) = 2 := by
  have hUeq := fsuU_eq_conjClosure_hz hMod h
  have hUk : conjSub (k : G) (conjClosure V (hz T V)) = conjClosure V (hz T V) :=
    conjSub_eq_self_iff.mpr (le_normalizer_conjClosure V _ N.mem)
  have e : centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (fsuU T V)
      (conjSub ((k : G) * g) (fsuU T V)) =
      conjSub (k : G) (F8.DH V (fsuV1 T V) (hz T V) (g : G)) := by
    rw [F8.DH, conjSub_centralizerMod, F8.A₁, F8.Uγ, ← conjSub_mul, ← conjSub_mul, hUk, hUeq]
  rw [e, hUeq, ← hUk, relIndex_conjSub]
  exact N.relIndex_DH h hF h2

theorem not_mem_hz (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) : (k : G) * g ∉ hz T V := by
  intro hx
  have hgH : (g : G) ∈ hz T V := by
    rw [show (g : G) = (k : G)⁻¹ * ((k : G) * g) by group]
    exact mul_mem (inv_mem N.mem) hx
  have hg1 : g • F8.γ₁ T L (hz T V) = F8.γ₁ T L (hz T V) :=
    smul_eq_of_mem_stab (by rw [stab_γ₁ hF.amalgamHypV.le₂]; exact hgH)
  have hb3 : 3 ≤ critDist ((L ⊔ T) ⊔ hz T V) (L ⊔ T) (hz T V) V := hF.three_le_b_and_odd.1
  have hd := N.setup.critical.dist_eq
  rw [← N.setup.edge₁, hg1, dist_eq_one_iff_adj.mpr adj_γ₀_γ₁] at hd
  omega

theorem zα_not_le_u0 (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h68 : Lemma14_7_68)
    (h : Hyp147 G T L V) : ¬ conjSub ((k : G) * g) (fsuV1 T V) ≤ u0 T V := by
  intro hle
  obtain ⟨z, hz, hz1, hgen⟩ := exists_gen_of_card_two hF.card_V₁
  have hmem : ((k : G) * g) * z * ((k : G) * g)⁻¹ ∈ u0 T V := hle (mul_mem_conjSub hz)
  have e := (h68 G T L V h).1 z hz _ hmem
  apply N.not_mem_hz hF
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  rcases hgen y hy with rfl | rfl
  · group
  · calc y * ((k : G) * g) = ((k : G) * g) * y * ((k : G) * g)⁻¹ * ((k : G) * g) := by rw [e]
      _ = ((k : G) * g) * y := by group

theorem zα_le (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) :
    conjSub ((k : G) * g) (fsuV1 T V) ≤ ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ := by
  obtain ⟨s, hsW, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hsR : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact this hsW
  set D := centralizerMod (conjSub ((k : G) * g) (fsuV1 T V)) (fsuU T V)
    (conjSub ((k : G) * g) (fsuU T V)) with hD
  have hDU : D ≤ fsuU T V := centralizerMod_le_left _ _ _
  have hcard : Nat.card ↥(conjSub ((k : G) * g) (fsuV1 T V)) = 2 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact hF.card_V₁
  have hle : ⁅D, conjSub ((k : G) * g) (fsuU T V)⁆ ≤ conjSub ((k : G) * g) (fsuV1 T V) := by
    rw [Subgroup.commutator_comm]
    exact commutator_centralizerMod_le _ _ _
  rcases HypF98.eq_bot_or_eq_of_card_eq_two hcard hle with hb | he
  ·
    exfalso
    have hDle : D ≤ V ⊔ u0 T V := by
      intro d hd
      refine mem_sup_u0_of_comm_mem h hMod h63 hF h1222 h1332 h1334 hsR hsQ (hDU hd) ?_
      have h1 : ⁅d, s⁆ = 1 := by
        rw [← Subgroup.mem_bot, ← hb]
        exact Subgroup.commutator_mem_commutator hd hsW
      have h2 : s * d * s⁻¹ * d⁻¹ = 1 := by
        rw [commutatorElement_def] at h1
        calc s * d * s⁻¹ * d⁻¹ = (d * s * d⁻¹ * s⁻¹)⁻¹ := by group
          _ = 1 := by rw [h1, inv_one]
      rw [h2]
      exact one_mem _
    have e1 := Subgroup.relIndex_mul_relIndex D (V ⊔ u0 T V) (fsuU T V) hDle
      (sup_le (le_conjClosure V _) (centralizerMod_le_left _ _ _))
    rw [(relIndex_sup_u0 h hMod h63 hF).2, N.relIndex_D h hMod hF h2] at e1
    omega
  · rw [← he]
    exact Subgroup.commutator_mono hDU le_rfl

theorem mem_sup_iff (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {s : G}
    (hsW : s ∈ conjSub ((k : G) * g) (fsuU T V))
    (hW : ∀ w ∈ conjSub ((k : G) * g) (fsuU T V),
      w ∈ pCoreOf 2 (hz T V) ∨ s⁻¹ * w ∈ pCoreOf 2 (hz T V)) {x : G} :
    x ∈ ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊔ fsuV1 T V ↔
      ∃ u ∈ fsuU T V, x * (u * s * u⁻¹ * s⁻¹)⁻¹ ∈ fsuV1 T V := by
  have hsH : s ∈ hz T V := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H) (this hsW)
  have hconj : ∀ c ∈ fsuV1 T V, ∀ y ∈ hz T V, y * c * y⁻¹ = c := fun c hc y hy => by
    rw [← Subgroup.mem_centralizer_iff.mp hy c hc]
    group
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hcomm : ∀ {a b : G}, a ∈ fsuU T V → b ∈ fsuU T V → a * b = b * a :=
    fun ha hb => F7.isElemAbelian_comm (isElemAbelian_fsuU_of h hMod) ha hb
  have hN := hz_le_normalizer_U h hMod hsH
  have hφU : ∀ {u : G}, u ∈ fsuU T V → u * s * u⁻¹ * s⁻¹ ∈ fsuU T V := fun {u} hu => by
    rw [show u * s * u⁻¹ * s⁻¹ = u * (s * u⁻¹ * s⁻¹) by group]
    exact mul_mem hu ((Subgroup.mem_normalizer_iff.mp hN _).mp (inv_mem hu))
  constructor
  · intro hx
    let S : Subgroup G :=
      { carrier := {x | ∃ u ∈ fsuU T V, x * (u * s * u⁻¹ * s⁻¹)⁻¹ ∈ fsuV1 T V}
        one_mem' := ⟨1, one_mem _, by simp⟩
        mul_mem' := by
          rintro a b ⟨u, hu, hau⟩ ⟨v, hv, hbv⟩
          refine ⟨u * v, mul_mem hu hv, ?_⟩
          rw [← comm_mul_comm h hMod hsH hu hv]
          have e : a * b * (u * s * u⁻¹ * s⁻¹ * (v * s * v⁻¹ * s⁻¹))⁻¹ =
              (a * (u * s * u⁻¹ * s⁻¹)⁻¹) * ((u * s * u⁻¹ * s⁻¹) *
                (b * (v * s * v⁻¹ * s⁻¹)⁻¹) * (u * s * u⁻¹ * s⁻¹)⁻¹) := by group
          rw [e, hconj _ hbv _ (hUH (hφU hu))]
          exact mul_mem hau hbv
        inv_mem' := by
          rintro a ⟨u, hu, hau⟩
          refine ⟨u⁻¹, inv_mem hu, ?_⟩
          have hsu : s * u * s⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp hN u).mp hu
          have e2 : u⁻¹ * s * u⁻¹⁻¹ * s⁻¹ = (u * s * u⁻¹ * s⁻¹)⁻¹ :=
            calc u⁻¹ * s * u⁻¹⁻¹ * s⁻¹ = u⁻¹ * (s * u * s⁻¹) := by group
              _ = (s * u * s⁻¹) * u⁻¹ := hcomm (inv_mem hu) hsu
              _ = (u * s * u⁻¹ * s⁻¹)⁻¹ := by group
          rw [e2, inv_inv]
          have e3 := hconj _ hau _ (inv_mem (hUH (hφU hu)))
          have e4 : a⁻¹ * (u * s * u⁻¹ * s⁻¹) = (a * (u * s * u⁻¹ * s⁻¹)⁻¹)⁻¹ :=
            calc a⁻¹ * (u * s * u⁻¹ * s⁻¹) = ((u * s * u⁻¹ * s⁻¹)⁻¹ *
                  (a * (u * s * u⁻¹ * s⁻¹)⁻¹) * (u * s * u⁻¹ * s⁻¹)⁻¹⁻¹)⁻¹ := by group
              _ = (a * (u * s * u⁻¹ * s⁻¹)⁻¹)⁻¹ := by rw [e3]
          rw [e4]
          exact inv_mem hau }
    have hle : ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊔ fsuV1 T V ≤ S := by
      refine sup_le ?_ fun c hc => ⟨1, one_mem _, by simpa using hc⟩
      rw [Subgroup.commutator_le]
      intro u hu w hw
      rw [commutatorElement_def]
      rcases hW w hw with hwQ | hwQ
      · refine ⟨1, one_mem _, ?_⟩
        have := inv_mem (comm_mem_of_pCoreOf h hMod hF hwQ hu)
        simpa [mul_assoc] using this
      · refine ⟨u, hu, ?_⟩
        set d := s⁻¹ * w with hd
        have hc := inv_mem (comm_mem_of_pCoreOf h hMod hF hwQ hu)
        have hc' : s * (u * d * u⁻¹ * d⁻¹) * s⁻¹ ∈ fsuV1 T V := by
          refine (Subgroup.mem_normalizer_iff.mp (hF.H_normalizes_V₁ hsH) _).mp ?_
          rwa [show (d * u * d⁻¹ * u⁻¹)⁻¹ = u * d * u⁻¹ * d⁻¹ by group] at hc
        have hw' : w = s * d := by rw [hd]; group
        rw [hw', show u * (s * d) * u⁻¹ * (s * d)⁻¹ * (u * s * u⁻¹ * s⁻¹)⁻¹ =
          (u * s * u⁻¹ * s⁻¹) * (s * (u * d * u⁻¹ * d⁻¹) * s⁻¹) * (u * s * u⁻¹ * s⁻¹)⁻¹ by
            group, hconj _ hc' _ (hUH (hφU hu))]
        exact hc'
    exact hle hx
  · rintro ⟨u, hu, hxu⟩
    rw [show x = (u * s * u⁻¹ * s⁻¹) * ((u * s * u⁻¹ * s⁻¹)⁻¹ * (x * (u * s * u⁻¹ * s⁻¹)⁻¹) *
      (u * s * u⁻¹ * s⁻¹)⁻¹⁻¹) by group]
    refine mul_mem (Subgroup.mem_sup_left ?_) (Subgroup.mem_sup_right ?_)
    · rw [← commutatorElement_def]
      exact Subgroup.commutator_mem_commutator hu hsW
    · rw [hconj _ hxu _ (inv_mem (hUH (hφU hu)))]
      exact hxu

theorem sup_inf_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h64 : Remark14_7_64) {s : G}
    (hsW : s ∈ conjSub ((k : G) * g) (fsuU T V)) (hsQ : s ∉ pCoreOf 2 (hz T V))
    (hW : ∀ w ∈ conjSub ((k : G) * g) (fsuU T V),
      w ∈ pCoreOf 2 (hz T V) ∨ s⁻¹ * w ∈ pCoreOf 2 (hz T V)) :
    (⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊔ fsuV1 T V) ⊓ u0 T V = fsuV1 T V := by
  have hsR : s ∈ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    have := N.uα_le hF
    rw [uα_eq (g := g) (k := k) h hMod] at this
    exact this hsW
  have hV1U0 := fsuV1_le_u0 h hMod
  refine le_antisymm (fun x hx => ?_) (le_inf le_sup_right hV1U0)
  obtain ⟨hxF, hxU0⟩ := Subgroup.mem_inf.mp hx
  obtain ⟨u, hu, hxu⟩ := (N.mem_sup_iff h hMod hF hsW hW).mp hxF
  have h1 : u * s * u⁻¹ * s⁻¹ ∈ u0 T V := by
    rw [show u * s * u⁻¹ * s⁻¹ = (x * (u * s * u⁻¹ * s⁻¹)⁻¹)⁻¹ * x by group]
    exact mul_mem (inv_mem (hV1U0 hxu)) hxU0
  have h2 := (h64 G T L V h).2.1 s hsR hsQ u hu h1
  rw [show x = (x * (u * s * u⁻¹ * s⁻¹)⁻¹) * (u * s * u⁻¹ * s⁻¹) by group]
  exact mul_mem hxu h2

theorem sup_u0 (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {s : G} (hsW : s ∈ conjSub ((k : G) * g) (fsuU T V))
    (hsQ : s ∉ pCoreOf 2 (hz T V)) :
    ⁅fsuU T V, conjSub ((k : G) * g) (fsuU T V)⁆ ⊔ u0 T V = V ⊔ u0 T V := by
  have hWR : conjSub ((k : G) * g) (fsuU T V) ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
    rw [← uα_eq (g := g) (k := k) h hMod]
    exact N.uα_le hF
  refine le_antisymm (sup_le ((Subgroup.commutator_mono le_rfl hWR).trans
    (commutator_le_sup_u0 h hMod h63 hF h1222 h1332 h1334)) le_sup_right) (sup_le ?_ le_sup_right)
  intro v hv
  obtain ⟨u, hu, hvu⟩ := exists_comm_mem_u0 h hMod h63 hF h1222 h1332 h1334 (hWR hsW) hsQ hv
  rw [show v = (v * (u * s * u⁻¹ * s⁻¹)⁻¹) * (u * s * u⁻¹ * s⁻¹) by group]
  refine mul_mem (Subgroup.mem_sup_right hvu) (Subgroup.mem_sup_left ?_)
  rw [← commutatorElement_def]
  exact Subgroup.commutator_mem_commutator hu hsW

end Not1471

end CFSG.Quasithin.H13.L32A
