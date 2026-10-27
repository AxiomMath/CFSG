module

public import CFSG.LargeExtraspecial.DWTim79.Bridge
public import CFSG.LargeExtraspecial.DWTim79.FusionTransfer

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.RankThree.GF2n.Tim79a

open Subgroup CFSG.Open CFSG.LargeExtraspecial CFSG.LargeExtraspecial.Timmesfeld

theorem setting_of_data {K : Type} [Group K] [Finite K] {z : K} (hz : orderOf z = 2)
    {Q : Subgroup K} (hQz : Q ≤ Subgroup.centralizer ({z} : Set K))
    (hQn : ∀ m ∈ Subgroup.centralizer ({z} : Set K), ∀ q ∈ Q, m * q * m⁻¹ ∈ Q)
    (hext : IsExtraspecial2 Q)
    (hQc : ∀ m ∈ Subgroup.centralizer ({z} : Set K), (∀ q ∈ Q, m * q = q * m) → m ∈ Q)
    (hQmax : ∀ R : Subgroup K, R ≤ Subgroup.centralizer ({z} : Set K) →
      (∀ m ∈ Subgroup.centralizer ({z} : Set K), ∀ r ∈ R, m * r * m⁻¹ ∈ R) →
      IsPGroup 2 R → R ≤ Q) :
    ∃ S : Setting K, S.z = z ∧ S.QG = Q := by
  set M : Subgroup K := Subgroup.centralizer ({z} : Set K)
  have hnormal : (Q.subgroupOf M).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hQn _ g.2 _ hn
  have hQ'ext : CFSG.IsExtraspecialPGroup 2 ↥(Q.subgroupOf M) :=
    CFSG.LargeExtraspecial.isExtraspecialPGroup_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hQz).symm
      ((CFSG.LargeExtraspecial.DWTim79.isExtraspecialPGroup_iff_isExtraspecial2 Q).mpr hext)
  have hcent : Subgroup.centralizer ((Q.subgroupOf M : Subgroup ↥M) : Set ↥M) ≤
      Q.subgroupOf M := by
    intro m hm
    rw [Subgroup.mem_subgroupOf]
    refine hQc (m : K) m.2 (fun q hq => ?_)
    have hq' : (⟨q, hQz hq⟩ : ↥M) ∈ Q.subgroupOf M := Subgroup.mem_subgroupOf.mpr hq
    have h1 := Subgroup.mem_centralizer_iff.mp hm (⟨q, hQz hq⟩ : ↥M) hq'
    have h2 := congrArg (fun x : ↥M => (x : K)) h1
    simp only [Subgroup.coe_mul] at h2
    exact h2.symm
  have hle : ∀ P : Subgroup ↥M, P.Normal → IsPGroup 2 P → P ≤ Q.subgroupOf M := by
    intro P hPn hP
    have hRle : P.map M.subtype ≤ M := by
      rintro _ ⟨x, -, rfl⟩
      exact x.2
    have hRn : ∀ m ∈ M, ∀ r ∈ P.map M.subtype, m * r * m⁻¹ ∈ P.map M.subtype := by
      rintro m hm _ ⟨p, hp, rfl⟩
      refine ⟨(⟨m, hm⟩ : ↥M) * p * (⟨m, hm⟩ : ↥M)⁻¹, hPn.conj_mem p hp _, ?_⟩
      simp
    have hRpg : IsPGroup 2 (P.map M.subtype) :=
      hP.of_equiv (Subgroup.equivMapOfInjective P M.subtype M.subtype_injective)
    intro p hp
    rw [Subgroup.mem_subgroupOf]
    exact hQmax (P.map M.subtype) hRle hRn hRpg (Subgroup.mem_map_of_mem M.subtype hp)
  refine ⟨⟨z, hz, Q.subgroupOf M, hnormal, hQ'ext, hcent, hle⟩, rfl, ?_⟩
  change (Q.subgroupOf M).map M.subtype = Q
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hQz]

theorem no_normal_four_of_data {K : Type} [Group K] [Finite K]
    (hO2 : ∀ (N : Subgroup K) [N.Normal], IsPGroup 2 (K ⧸ N) → N = ⊤) {z : K}
    (hz : orderOf z = 2) {Q T : Subgroup K} (hQz : Q ≤ Subgroup.centralizer ({z} : Set K))
    (hQn : ∀ m ∈ Subgroup.centralizer ({z} : Set K), ∀ q ∈ Q, m * q * m⁻¹ ∈ Q)
    (hext : IsExtraspecial2 Q)
    (hQc : ∀ m ∈ Subgroup.centralizer ({z} : Set K), (∀ q ∈ Q, m * q = q * m) → m ∈ Q)
    (hQmax : ∀ R : Subgroup K, R ≤ Subgroup.centralizer ({z} : Set K) →
      (∀ m ∈ Subgroup.centralizer ({z} : Set K), ∀ r ∈ R, m * r * m⁻¹ ∈ R) →
      IsPGroup 2 R → R ≤ Q) {w : ℕ} (hw : Nat.card Q = 2 ^ (1 + 2 * w)) (hw2 : 2 ≤ w)
    (hTM : T ≤ Subgroup.centralizer ({z} : Set K))
    (hT : ∀ m ∈ Subgroup.centralizer ({z} : Set K), ∀ x ∈ T, m * x * m⁻¹ ∈ T)
    (hT4 : Nat.card T = 4) (hzT : z ∈ T) : False := by
  obtain ⟨S, rfl, hSQ⟩ := setting_of_data hz hQz hQn hext hQc hQmax
  have hcard : Nat.card S.Q = 2 ^ (1 + 2 * w) := by
    rw [← S.card_QG_eq_card_Q, hSQ]
    exact hw
  have hwid : S.width = w := S.width_eq hcard
  exact DW.not_normal_order_four_of_O2 (S := S) hO2 (by omega) hTM hT hT4 hzT

theorem isExtraspecial2_subgroupOf {G : Type} [Group G] [Finite G] {Q G₀ : Subgroup G}
    (hQG : Q ≤ G₀) (h : IsExtraspecial2 Q) : IsExtraspecial2 (Q.subgroupOf G₀) := by
  have h1 : IsExtraspecialPGroup 2 ↥Q := (DWTim79.isExtraspecialPGroup_iff_isExtraspecial2 Q).mpr h
  have h2 : IsExtraspecialPGroup 2 ↥(Q.subgroupOf G₀) :=
    isExtraspecialPGroup_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hQG).symm h1
  exact (DWTim79.isExtraspecialPGroup_iff_isExtraspecial2 (Q.subgroupOf G₀)).mp h2

theorem no_normal_four_in_residual {G : Type} [Group G] [Finite G] (G₀ : Subgroup G)
    (hO2 : ∀ (N : Subgroup ↥G₀) [N.Normal], IsPGroup 2 (↥G₀ ⧸ N) → N = ⊤)
    {aG : G} (haG : orderOf aG = 2) {Q V : Subgroup G} (hQG : Q ≤ G₀)
    (haV : aG ∈ V) (hVQ : V ≤ Q) (hV4 : Nat.card V = 4)
    (hQM : Q ≤ Subgroup.centralizer ({aG} : Set G))
    (hQn : ∀ m ∈ Subgroup.centralizer ({aG} : Set G), ∀ q ∈ Q, m * q * m⁻¹ ∈ Q)
    (hVn : ∀ m ∈ Subgroup.centralizer ({aG} : Set G), ∀ v ∈ V, m * v * m⁻¹ ∈ V)
    (hext : IsExtraspecial2 Q)
    (hQc : ∀ m ∈ Subgroup.centralizer ({aG} : Set G), (∀ q ∈ Q, m * q = q * m) → m ∈ Q)
    (hQmax : ∀ R : Subgroup G, R ≤ Subgroup.centralizer ({aG} : Set G) ⊓ G₀ →
      (∀ m ∈ Subgroup.centralizer ({aG} : Set G) ⊓ G₀, ∀ r ∈ R, m * r * m⁻¹ ∈ R) →
      IsPGroup 2 R → R ≤ Q)
    {w : ℕ} (hw : Nat.card Q = 2 ^ (1 + 2 * w)) (hw2 : 2 ≤ w) : False := by
  have haG₀ : aG ∈ G₀ := hQG (hVQ haV)
  have hVG : V ≤ G₀ := hVQ.trans hQG
  set z : ↥G₀ := ⟨aG, haG₀⟩ with hzdef
  have hzc : ∀ m : ↥G₀, m ∈ Subgroup.centralizer ({z} : Set ↥G₀) ↔
      (m : G) ∈ Subgroup.centralizer ({aG} : Set G) := by
    intro m
    rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  refine no_normal_four_of_data hO2 (z := z) (Q := Q.subgroupOf G₀) (T := V.subgroupOf G₀)
    (by rw [hzdef, orderOf_mk]; exact haG) ?_ ?_ (isExtraspecial2_subgroupOf hQG hext) ?_ ?_
    (w := w) ?_ hw2 ?_ ?_ ?_ ?_
  · intro x hx
    rw [hzc]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hQM (Subgroup.mem_subgroupOf.mp hx)))
  · intro m hm q hq
    rw [hzc] at hm
    exact Subgroup.mem_subgroupOf.mpr (hQn _ hm _ (Subgroup.mem_subgroupOf.mp hq))
  · intro m hm hcomm
    rw [hzc] at hm
    refine Subgroup.mem_subgroupOf.mpr (hQc _ hm fun q hq => ?_)
    have := hcomm ⟨q, hQG hq⟩ (Subgroup.mem_subgroupOf.mpr hq)
    exact congrArg Subtype.val this
  · intro R hR hRn hR2
    have hRG : R.map G₀.subtype ≤ Subgroup.centralizer ({aG} : Set G) ⊓ G₀ := by
      rintro _ ⟨r, hr, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨(hzc r).mp (hR hr), r.2⟩
    have hRn' : ∀ m ∈ Subgroup.centralizer ({aG} : Set G) ⊓ G₀, ∀ r ∈ R.map G₀.subtype,
        m * r * m⁻¹ ∈ R.map G₀.subtype := by
      intro m hm r hr
      obtain ⟨r', hr', rfl⟩ := hr
      have hmC : (⟨m, (Subgroup.mem_inf.mp hm).2⟩ : ↥G₀) ∈ Subgroup.centralizer ({z} : Set ↥G₀) :=
        (hzc _).mpr (Subgroup.mem_inf.mp hm).1
      exact ⟨_, hRn _ hmC _ hr', rfl⟩
    have hR2' : IsPGroup 2 (R.map G₀.subtype) :=
      hR2.of_equiv (Subgroup.equivMapOfInjective R G₀.subtype G₀.subtype_injective)
    intro r hr
    exact Subgroup.mem_subgroupOf.mpr (hQmax _ hRG hRn' hR2' ⟨r, hr, rfl⟩)
  · rw [← hw]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQG).toEquiv
  · intro x hx
    rw [hzc]
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hQM (hVQ (Subgroup.mem_subgroupOf.mp hx))))
  · intro m hm x hx
    rw [hzc] at hm
    exact Subgroup.mem_subgroupOf.mpr (hVn _ hm _ (Subgroup.mem_subgroupOf.mp hx))
  · rw [← hV4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hVG).toEquiv
  · exact Subgroup.mem_subgroupOf.mpr haV

end CFSG.RankThree.GF2n.Tim79a
