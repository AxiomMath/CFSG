module

public import CFSG.Quasithin.Vol2.Ch12Sec8NatL

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem rconj_inf_eq (X Y : Subgroup G) (g : G) : rconj (X ⊓ Y) g = rconj X g ⊓ rconj Y g := by
  ext y
  simp only [mem_rconj, Subgroup.mem_inf]

theorem rconj_eq_of_mem_normalizer {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) : rconj X g = X := by
  ext y
  rw [mem_rconj]
  exact ((Subgroup.mem_normalizer_iff.mp hg y)).symm

theorem card_rconj_eq (X : Subgroup G) (g : G) : Nat.card (rconj X g) = Nat.card X :=
  Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective

theorem le_normalizer_rconj_of {S W : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (S : Set G)) (hS : S ≤ Subgroup.normalizer (W : Set G)) :
    S ≤ Subgroup.normalizer (rconj W g : Set G) := by
  refine le_normalizer_of_conj_mem fun s hs x hx => ?_
  rw [mem_rconj] at hx ⊢
  have hgs : g * s * g⁻¹ ∈ S := (Subgroup.mem_normalizer_iff.mp hg s).mp hs
  have e : g * (s * x * s⁻¹) * g⁻¹ = (g * s * g⁻¹) * (g * x * g⁻¹) * (g * s * g⁻¹)⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp (hS hgs) _).mp hx

theorem rconj_mul_eq_of_mem_normalizer {X : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (X : Set G)) (l : G) : rconj X (t * l) = rconj X l := by
  ext y
  rw [mem_rconj, mem_rconj]
  have e : t * l * y * (t * l)⁻¹ = t * (l * y * l⁻¹) * t⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.mp ht _).symm

variable [Finite G] {T M L : Subgroup G}

structure GoodElt128 (T L : Subgroup G) (g : G) : Prop where
  mem : g ∈ L
  not_mem : g ∉ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G)

theorem exists_sylow_subgroupOf_inf_normal {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ]
    (S : Sylow p Γ) {N : Subgroup Γ} [N.Normal] :
    ∃ P : Sylow p ↥N, (P : Subgroup ↥N) = ((S : Subgroup Γ) ⊓ N).subgroupOf N := by
  classical
  let P : Subgroup ↥N := ((S : Subgroup Γ) ⊓ N).subgroupOf N
  have hP1 : IsPGroup p P := by
    have hSn : IsPGroup p (↥((S : Subgroup Γ) ⊓ N)) := S.isPGroup'.to_inf_left
    exact hSn.of_equiv
      (Subgroup.subgroupOfEquivOfLe (H := (S : Subgroup Γ) ⊓ N) (K := N) inf_le_right).symm
  have hrel1 :
      ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ) *
          (S : Subgroup Γ).relIndex ((S : Subgroup Γ) ⊔ N) =
        ((S : Subgroup Γ) ⊓ N).relIndex ((S : Subgroup Γ) ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (H := (S : Subgroup Γ) ⊓ N)
      (K := (S : Subgroup Γ)) (L := (S : Subgroup Γ) ⊔ N) inf_le_left le_sup_left
  have hrel2 :
      ((S : Subgroup Γ) ⊓ N).relIndex N * N.relIndex ((S : Subgroup Γ) ⊔ N) =
        ((S : Subgroup Γ) ⊓ N).relIndex ((S : Subgroup Γ) ⊔ N) :=
    Subgroup.relIndex_mul_relIndex (H := (S : Subgroup Γ) ⊓ N) (K := N)
      (L := (S : Subgroup Γ) ⊔ N) inf_le_right le_sup_right
  have h2a : N.relIndex ((S : Subgroup Γ) ⊔ N) = N.relIndex (S : Subgroup Γ) :=
    Subgroup.relIndex_sup_right (H := (S : Subgroup Γ)) (K := N)
  have h2a' : N.relIndex (S : Subgroup Γ) = ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ) :=
    (Subgroup.inf_relIndex_left (H := (S : Subgroup Γ)) (K := N)).symm
  have hrel2' :
      ((S : Subgroup Γ) ⊓ N).relIndex N * ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ) =
        ((S : Subgroup Γ) ⊓ N).relIndex ((S : Subgroup Γ) ⊔ N) := by
    simpa [h2a, h2a'] using hrel2
  have hcanc : ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ) ≠ 0 := by
    intro hz
    have hdvd : ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ) ∣
        ((S : Subgroup Γ) ⊓ N).index :=
      Subgroup.relIndex_dvd_index_of_le (H := (S : Subgroup Γ) ⊓ N)
        (K := (S : Subgroup Γ)) inf_le_left
    have hSne : ((S : Subgroup Γ) ⊓ N).index ≠ 0 :=
      (Subgroup.finiteIndex_of_finite (H := (S : Subgroup Γ) ⊓ N)).index_ne_zero
    exact hSne (eq_zero_of_zero_dvd (by simpa [hz] using hdvd))
  have hrel : ((S : Subgroup Γ) ⊓ N).relIndex N =
      (S : Subgroup Γ).relIndex ((S : Subgroup Γ) ⊔ N) := by
    have h' : ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ) *
          (S : Subgroup Γ).relIndex ((S : Subgroup Γ) ⊔ N) =
        ((S : Subgroup Γ) ⊓ N).relIndex N *
          ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ) :=
      hrel1.trans hrel2'.symm
    have h'' : (S : Subgroup Γ).relIndex ((S : Subgroup Γ) ⊔ N) *
          ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ) =
        ((S : Subgroup Γ) ⊓ N).relIndex N *
          ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ) := by
      simpa [mul_comm] using h'
    exact (Nat.mul_right_cancel (m := ((S : Subgroup Γ) ⊓ N).relIndex (S : Subgroup Γ))
      (Nat.pos_of_ne_zero hcanc) h'').symm
  have hP2 : ¬ p ∣ P.index := by
    intro hp
    have hp' : p ∣ (S : Subgroup Γ).relIndex ((S : Subgroup Γ) ⊔ N) := by
      change p ∣ ((S : Subgroup Γ) ⊓ N).relIndex N at hp
      rwa [hrel] at hp
    have hdvd : (S : Subgroup Γ).relIndex ((S : Subgroup Γ) ⊔ N) ∣ (S : Subgroup Γ).index :=
      Subgroup.relIndex_dvd_index_of_le (H := (S : Subgroup Γ))
        (K := (S : Subgroup Γ) ⊔ N) le_sup_left
    exact S.not_dvd_index (hp'.trans hdvd)
  exact ⟨hP1.toSylow hP2, rfl⟩

theorem normalizer_inf_sup_normal_eq_top {p : ℕ} [Fact p.Prime] {Γ : Type*} [Group Γ] [Finite Γ]
    (S : Sylow p Γ) (N : Subgroup Γ) [N.Normal] :
    Subgroup.normalizer (((S : Subgroup Γ) ⊓ N : Subgroup Γ) : Set Γ) ⊔ N = ⊤ := by
  classical
  obtain ⟨P, hP⟩ := exists_sylow_subgroupOf_inf_normal S (N := N)
  have hfr := Sylow.normalizer_sup_eq_top (N := N) (P := P)
  have hmap : (P : Subgroup ↥N).map N.subtype = (S : Subgroup Γ) ⊓ N := by
    rw [hP]
    exact Subgroup.map_subgroupOf_eq_of_le inf_le_right
  rw [hmap] at hfr
  exact hfr



theorem exists_mul_mem_normalizer_inf_of_isSylowTwoOf {H C T : Subgroup G}
    (hHC : H ≤ Subgroup.normalizer (C : Set G)) (hT : IsSylowTwoOf T H) {x : G} (hx : x ∈ H) :
    ∃ c ∈ C, ∃ n ∈ H, n ∈ Subgroup.normalizer ((T ⊓ C : Subgroup G) : Set G) ∧ x = c * n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTp : IsPGroup 2 (T.subgroupOf H) :=
    hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm
  let S : Sylow 2 ↥H := hTp.toSylow hT.2.2
  have : (C.subgroupOf H).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hHC
  have h1 := normalizer_inf_sup_normal_eq_top S (C.subgroupOf H)
  have hS : (S : Subgroup ↥H) = T.subgroupOf H := rfl
  have hmem : (⟨x, hx⟩ : ↥H) ∈
      Subgroup.normalizer (((S : Subgroup ↥H) ⊓ C.subgroupOf H : Subgroup ↥H) : Set ↥H) ⊔
        C.subgroupOf H := by
    rw [h1]
    exact Subgroup.mem_top _
  obtain ⟨n, hn, c, hc, hnc⟩ := Subgroup.mem_sup_of_normal_right.mp hmem
  refine ⟨(n : G) * (c : G) * (n : G)⁻¹, ?_, n, n.2, ?_, ?_⟩
  · have : (n : G) * (c : G) * (n : G)⁻¹ ∈ C := (Subgroup.mem_normalizer_iff.mp (hHC n.2) _).mp hc
    exact this
  · rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have hyH : y ∈ H := hT.1 hy.1
      have hy' : (⟨y, hyH⟩ : ↥H) ∈ (S : Subgroup ↥H) ⊓ C.subgroupOf H := ⟨hy.1, hy.2⟩
      have := (Subgroup.mem_normalizer_iff.mp hn _).mp hy'
      exact ⟨this.1, this.2⟩
    · intro hy
      have hnyH : (n : G) * y * (n : G)⁻¹ ∈ H := hT.1 hy.1
      have hyH : y ∈ H := by
        have := H.mul_mem (H.mul_mem (H.inv_mem n.2) hnyH) n.2
        simpa [mul_assoc] using this
      have hy' : (n * ⟨y, hyH⟩ * n⁻¹ : ↥H) ∈ (S : Subgroup ↥H) ⊓ C.subgroupOf H := ⟨hy.1, hy.2⟩
      have := (Subgroup.mem_normalizer_iff.mp hn ⟨y, hyH⟩).mpr hy'
      exact ⟨this.1, this.2⟩
  · have : (x : G) = (n : G) * (c : G) := by
      have := congrArg Subtype.val hnc
      simpa using this.symm
    rw [this]
    group


omit [Finite G] in
theorem GoodElt128.mem_sup {g : G} (hg : GoodElt128 T L g) (U : Subgroup G) : g ∈ L ⊔ U :=
  Subgroup.mem_sup_left hg.mem

namespace Hyp1281Two

theorem exists_goodElt (h : Hyp1281Two G T M L) {g : G} (hg : g ∈ L ⊔ T)
    (hgH : g ∉ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :
    ∃ t ∈ T, ∃ l : G, GoodElt128 T L l ∧ g = t * l := by
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.inM.2.trans h.normal
  have hmem : g ∈ (T : Set G) * (L : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T L hTL]
    rw [sup_comm] at hg
    exact hg
  obtain ⟨t, ht, l, hl, rfl⟩ := hmem
  have hTN : t ∈ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := by
    rw [h.normalizer_Z_eq_centralizer]
    exact h.almostSpecialHyp_g1.T_le_H ht
  refine ⟨t, ht, l, ⟨hl, fun hlN => hgH ?_⟩, rfl⟩
  rw [← h.normalizer_Z_eq_centralizer]
  exact Subgroup.mul_mem _ hTN hlN


theorem sup_uOfL22_le_LT (h : Hyp1281Two G T M L) : L ⊔ uOfL22 T M ≤ L ⊔ T :=
  sup_le_sup_left h.uOfL22_le_T L

theorem sup_uOfL22_le_normalizer_VZ (h : Hyp1281Two G T M L) :
    L ⊔ uOfL22 T M ≤ Subgroup.normalizer (VZ T M : Set G) :=
  (h.sup_uOfL22_le_LT).trans h.LT_le_normalizer_VZ

theorem sup_rconj_uOfL22_eq (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    uOfL22 T M ⊔ rconj (uOfL22 T M) g = L ⊔ uOfL22 T M :=
  (h.almostSpecialL2Hyp hU).G23_two hg.mem hg.not_mem

theorem VZ_le_inf_rconj (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) : VZ T M ≤ uOfL22 T M ⊓ rconj (uOfL22 T M) g :=
  ((h.almostSpecialL2Hyp hU).G23_four hg.mem hg.not_mem).1

theorem inf_rconj_le_pCoreOf (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) :
    uOfL22 T M ⊓ rconj (uOfL22 T M) g ≤ pCoreOf 2 (L ⊔ uOfL22 T M) := by
  rw [← h.sup_rconj_uOfL22_eq hU hg]
  exact ((h.almostSpecialL2Hyp hU).G23_four hg.mem hg.not_mem).2.1

theorem sup_le_normalizer_inf_rconj (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    L ⊔ uOfL22 T M ≤
      Subgroup.normalizer ((uOfL22 T M ⊓ rconj (uOfL22 T M) g : Subgroup G) : Set G) := by
  rw [← h.sup_rconj_uOfL22_eq hU hg]
  exact ((h.almostSpecialL2Hyp hU).G23_four hg.mem hg.not_mem).2.2.2.2.1

theorem commutator_inf_rconj_le (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    ⁅uOfL22 T M ⊓ rconj (uOfL22 T M) g, L ⊔ uOfL22 T M⁆ ≤ VZ T M := by
  rw [← h.sup_rconj_uOfL22_eq hU hg]
  exact ((h.almostSpecialL2Hyp hU).G23_five hg.mem hg.not_mem).1

theorem isElemAbelian_inf_rconj (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    IsElemAbelian 2 (uOfL22 T M ⊓ rconj (uOfL22 T M) g) :=
  ((h.almostSpecialL2Hyp hU).G23_five hg.mem hg.not_mem).2

theorem pCoreOf_sup_uOfL22_eq (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    pCoreOf 2 (L ⊔ uOfL22 T M) = (L ⊔ uOfL22 T M) ⊓ Subgroup.centralizer (VZ T M : Set G) := by
  apply le_antisymm
  · have hle : pCoreOf 2 (L ⊔ uOfL22 T M) ≤ pCoreOf 2 (L ⊔ T) := by
      rw [← h.sup_rconj_uOfL22_eq hU hg]
      obtain ⟨D⟩ := (h.almostSpecialL2Hyp hU).natural.nonempty_data
      let St : L2Setting 1 (VZ T M) (quasithinOmegaOneCenter T) L T
          (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
        ⟨h.almostSpecialL2Hyp hU, D⟩
      exact St.pCoreOf_I_le_O hg.mem hg.not_mem
    refine le_inf (pCoreOf_le 2 _) ?_
    have : pCoreOf 2 (L ⊔ uOfL22 T M) ≤ (L ⊔ T) ⊓ Subgroup.centralizer (VZ T M : Set G) := by
      rw [h.centralizer]
      exact hle
    exact this.trans inf_le_right
  · have hIN : L ⊔ uOfL22 T M ≤ Subgroup.normalizer (VZ T M : Set G) :=
      h.sup_uOfL22_le_normalizer_VZ
    refine le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · intro x hx
      exact Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hx,
          (normalizer_le_normalizer_centralizer'' _ (hIN hx))⟩
    · have : (L ⊔ uOfL22 T M) ⊓ Subgroup.centralizer (VZ T M : Set G) ≤ pCoreOf 2 (L ⊔ T) := by
        rw [← h.centralizer]
        exact inf_le_inf_right _ h.sup_uOfL22_le_LT
      exact (pCoreOf_isPGroup 2 (L ⊔ T)).to_le this

theorem wOfU_eq_inf_pCoreOf (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    wOfU T M = uOfL22 T M ⊓ pCoreOf 2 (L ⊔ uOfL22 T M) := by
  rw [h.pCoreOf_sup_uOfL22_eq hU hg, ← inf_assoc,
    inf_eq_left.mpr (le_sup_right : uOfL22 T M ≤ L ⊔ uOfL22 T M)]
  rfl

theorem pCoreOf_sup_uOfL22_le_T (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    pCoreOf 2 (L ⊔ uOfL22 T M) ≤ T := by
  have h1 : pCoreOf 2 (L ⊔ uOfL22 T M) ≤ (L ⊔ T) ⊓ Subgroup.centralizer (VZ T M : Set G) := by
    rw [h.pCoreOf_sup_uOfL22_eq hU hg]
    exact inf_le_inf_right _ h.sup_uOfL22_le_LT
  rw [h.centralizer] at h1
  exact h1.trans (pCoreOf_two_le_of_isSylowTwoOf h.almostSpecialHyp_g1.sylow_LT)

theorem pCoreOf_sup_uOfL22_le_normalizer_U (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    pCoreOf 2 (L ⊔ uOfL22 T M) ≤ Subgroup.normalizer (uOfL22 T M : Set G) :=
  (h.pCoreOf_sup_uOfL22_le_T hU hg).trans h.T_le_normalizer_uOfL22

theorem pCoreOf_sup_uOfL22_le_normalizer_W (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    pCoreOf 2 (L ⊔ uOfL22 T M) ≤ Subgroup.normalizer (wOfU T M : Set G) := by
  intro s hs
  have h1 : s ∈ Subgroup.normalizer (Subgroup.centralizer (VZ T M : Set G) : Set G) :=
    normalizer_le_normalizer_centralizer'' _
      (h.sup_uOfL22_le_normalizer_VZ (pCoreOf_le 2 _ hs))
  exact Subgroup.inf_normalizer_le_normalizer_inf ⟨h.pCoreOf_sup_uOfL22_le_normalizer_U hU hg hs, h1⟩

omit [Finite G] in
theorem mem_normalizer_pCoreOf_sup (g : G) (hg : GoodElt128 T L g) (U : Subgroup G) :
    g ∈ Subgroup.normalizer (pCoreOf 2 (L ⊔ U) : Set G) :=
  le_normalizer_pCoreOf 2 _ (hg.mem_sup U)

theorem rconj_wOfU_eq (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    rconj (wOfU T M) g = rconj (uOfL22 T M) g ⊓ pCoreOf 2 (L ⊔ uOfL22 T M) := by
  rw [h.wOfU_eq_inf_pCoreOf hU hg, rconj_inf_eq,
    rconj_eq_of_mem_normalizer (mem_normalizer_pCoreOf_sup g hg _)]

theorem wOfU_inf_rconj_eq (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) :
    wOfU T M ⊓ rconj (wOfU T M) g = uOfL22 T M ⊓ rconj (uOfL22 T M) g := by
  have hS := h.inf_rconj_le_pCoreOf hU hg
  rw [h.rconj_wOfU_eq hU hg, h.wOfU_eq_inf_pCoreOf hU hg]
  apply le_antisymm
  · exact inf_le_inf inf_le_left inf_le_left
  · exact le_inf (le_inf inf_le_left hS) (le_inf inf_le_right hS)

theorem pCoreOf_sup_uOfL22_eq_wOfU_sup (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    pCoreOf 2 (L ⊔ uOfL22 T M) = wOfU T M ⊔ rconj (wOfU T M) g ∧
      ((pCoreOf 2 (L ⊔ uOfL22 T M) : Subgroup G) : Set G) =
        (wOfU T M : Set G) * (rconj (wOfU T M) g : Set G) :=
  (h.almostSpecialL2Hyp hU).G23_three (U := uOfL22 T M) (I := L ⊔ uOfL22 T M)
    (S := pCoreOf 2 (L ⊔ uOfL22 T M)) (W := wOfU T M) rfl hg.mem hg.not_mem
    (h.sup_rconj_uOfL22_eq hU hg).symm rfl (h.wOfU_eq_inf_pCoreOf hU hg)

theorem wOfU_le_pCoreOf (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) : wOfU T M ≤ pCoreOf 2 (L ⊔ uOfL22 T M) := by
  rw [h.wOfU_eq_inf_pCoreOf hU hg]
  exact inf_le_right

theorem rconj_wOfU_le_pCoreOf (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) :
    rconj (wOfU T M) g ≤ pCoreOf 2 (L ⊔ uOfL22 T M) := by
  rw [h.rconj_wOfU_eq hU hg]
  exact inf_le_right

theorem pCoreOf_sup_uOfL22_le_normalizer_X (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    pCoreOf 2 (L ⊔ uOfL22 T M) ≤ Subgroup.normalizer (rconj (wOfU T M) g : Set G) :=
  le_normalizer_rconj_of (mem_normalizer_pCoreOf_sup g hg _)
    (h.pCoreOf_sup_uOfL22_le_normalizer_W hU hg)

theorem commutator_wOfU_rconj_le (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) :
    ⁅wOfU T M, rconj (wOfU T M) g⁆ ≤ wOfU T M ⊓ rconj (wOfU T M) g := by
  rw [Subgroup.commutator_le]
  intro w hw x hx
  have hwS := h.wOfU_le_pCoreOf hU hg hw
  have hxS := h.rconj_wOfU_le_pCoreOf hU hg hx
  refine ⟨?_, ?_⟩
  · have h1 : x * w⁻¹ * x⁻¹ ∈ wOfU T M :=
      (Subgroup.mem_normalizer_iff.mp (h.pCoreOf_sup_uOfL22_le_normalizer_W hU hg hxS) _).mp
        ((wOfU T M).inv_mem hw)
    have e : ⁅w, x⁆ = w * (x * w⁻¹ * x⁻¹) := by simp [commutatorElement_def, mul_assoc]
    rw [e]
    exact (wOfU T M).mul_mem hw h1
  · have h1 : w * x * w⁻¹ ∈ rconj (wOfU T M) g :=
      (Subgroup.mem_normalizer_iff.mp (h.pCoreOf_sup_uOfL22_le_normalizer_X hU hg hwS) _).mp hx
    have e : ⁅w, x⁆ = (w * x * w⁻¹) * x⁻¹ := by simp [commutatorElement_def]
    rw [e]
    exact (rconj (wOfU T M) g).mul_mem h1 ((rconj (wOfU T M) g).inv_mem hx)

def stabCoset128 (E : Subgroup G) (y : G) : Subgroup G where
  carrier := {i | i ∈ Subgroup.normalizer (E : Set G) ∧ i * y * i⁻¹ * y⁻¹ ∈ E}
  one_mem' := ⟨Subgroup.one_mem _, by simp⟩
  mul_mem' := by
    rintro i j ⟨hiN, hi⟩ ⟨hjN, hj⟩
    refine ⟨Subgroup.mul_mem _ hiN hjN, ?_⟩
    have h1 : i * (j * y * j⁻¹ * y⁻¹) * i⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hiN _).mp hj
    have e : i * j * y * (i * j)⁻¹ * y⁻¹ =
        (i * (j * y * j⁻¹ * y⁻¹) * i⁻¹) * (i * y * i⁻¹ * y⁻¹) := by group
    rw [e]
    exact E.mul_mem h1 hi
  inv_mem' := by
    rintro i ⟨hiN, hi⟩
    refine ⟨Subgroup.inv_mem _ hiN, ?_⟩
    have h1 : i⁻¹ * (i * y * i⁻¹ * y⁻¹)⁻¹ * i⁻¹⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hiN) _).mp (E.inv_mem hi)
    have e : i⁻¹ * y * i⁻¹⁻¹ * y⁻¹ = i⁻¹ * (i * y * i⁻¹ * y⁻¹)⁻¹ * i⁻¹⁻¹ := by group
    rw [e]
    exact h1

omit [Finite G] in
theorem mem_stabCoset128 {E : Subgroup G} {y i : G} :
    i ∈ stabCoset128 E y ↔ i ∈ Subgroup.normalizer (E : Set G) ∧ i * y * i⁻¹ * y⁻¹ ∈ E := Iff.rfl

noncomputable def l2Setting128 (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) :
    L2Setting 1 (VZ T M) (quasithinOmegaOneCenter T) L T
      (Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)) :=
  ⟨h.almostSpecialL2Hyp hU, Classical.choice (h.almostSpecialL2Hyp hU).natural.nonempty_data⟩

theorem commutator_rconj_uOfL22_mem_VZ (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) {a b : G}
    (ha : a ∈ rconj (uOfL22 T M) g) (hb : b ∈ rconj (uOfL22 T M) g) :
    a * b * a⁻¹ * b⁻¹ ∈ VZ T M :=
  (h.l2Setting128 hU).V₁_le_rconj_V hg.mem ((h.l2Setting128 hU).rconj_commutator_mem ha hb)

theorem mem_inf_of_commutator_mem (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) {u y : G}
    (hu : u ∈ uOfL22 T M) (huW : u ∉ wOfU T M) (hy : y ∈ rconj (wOfU T M) g)
    (hyu : y * u * y⁻¹ * u⁻¹ ∈ wOfU T M ⊓ rconj (wOfU T M) g) :
    y ∈ wOfU T M ⊓ rconj (wOfU T M) g := by
  set U := uOfL22 T M with hUdef
  set W := wOfU T M with hWdef
  set E := W ⊓ rconj W g with hEdef
  have hE : E = U ⊓ rconj U g := h.wOfU_inf_rconj_eq hU hg
  have hEN : L ⊔ U ≤ Subgroup.normalizer (E : Set G) := by
    rw [hE]
    exact h.sup_le_normalizer_inf_rconj hU hg
  have hEV : VZ T M ≤ E := by
    rw [hE]
    exact h.VZ_le_inf_rconj hU hg
  have hUI : U ≤ L ⊔ U := le_sup_right
  have hWC : W ≤ stabCoset128 E y := by
    intro w hw
    refine ⟨hEN (hUI (wOfU_le_uOfL22 T M hw)), ?_⟩
    have := h.commutator_wOfU_rconj_le hU hg (Subgroup.commutator_mem_commutator hw hy)
    exact this
  have huC : u ∈ stabCoset128 E y := by
    refine ⟨hEN (hUI hu), ?_⟩
    have e : u * y * u⁻¹ * y⁻¹ = (y * u * y⁻¹ * u⁻¹)⁻¹ := by group
    rw [e]
    exact E.inv_mem hyu
  have hUC : U ≤ stabCoset128 E y := by
    intro u' hu'
    by_cases hu'W : u' ∈ W
    · exact hWC hu'W
    · have hmem : u⁻¹ * u' ∈ W := (h.mem_wOfU_or_inv_mul_mem hu hu' huW).resolve_left hu'W
      have : u * (u⁻¹ * u') ∈ stabCoset128 E y := (stabCoset128 E y).mul_mem huC (hWC hmem)
      simpa using this
  have hUgC : rconj U g ≤ stabCoset128 E y := by
    intro a ha
    have haI : a ∈ L ⊔ U := by
      rw [← h.sup_rconj_uOfL22_eq hU hg]
      exact Subgroup.mem_sup_right ha
    have hyUg : y ∈ rconj U g := by
      have : rconj W g ≤ rconj U g := by
        intro z hz
        rw [mem_rconj] at hz ⊢
        exact wOfU_le_uOfL22 T M hz
      exact this hy
    refine ⟨hEN haI, ?_⟩
    exact hEV (h.commutator_rconj_uOfL22_mem_VZ hU hg ha hyUg)
  have hIC : L ⊔ U ≤ stabCoset128 E y := by
    rw [← h.sup_rconj_uOfL22_eq hU hg]
    exact sup_le hUC hUgC
  have hgC : g ∈ stabCoset128 E y := hIC (hg.mem_sup U)
  obtain ⟨-, hgy⟩ := hgC
  have hgyW : g * y * g⁻¹ ∈ W := (mem_rconj).mp hy
  have hgyE : g * y * g⁻¹ ∈ E := by
    refine ⟨hgyW, ?_⟩
    have e : g * y * g⁻¹ = (g * y * g⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact (rconj W g).mul_mem hgy.2 hy
  have hyinv : y⁻¹ ∈ E := by
    have e : y⁻¹ = (g * y * g⁻¹)⁻¹ * (g * y * g⁻¹ * y⁻¹) := by group
    rw [e]
    exact E.mul_mem (E.inv_mem hgyE) hgy
  simpa using E.inv_mem hyinv

theorem omegaOneCenter_le_inf_rconj (h : Hyp1281Two G T M L)
    (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G} (hg : GoodElt128 T L g) :
    quasithinOmegaOneCenter T ≤ wOfU T M ⊓ rconj (wOfU T M) g := by
  rw [h.wOfU_inf_rconj_eq hU hg]
  exact (omegaOneCenter_le_VZ T M).trans (h.VZ_le_inf_rconj hU hg)

theorem lemma_12_8_9_four (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) {y u : G} (hy : y ∈ rconj (wOfU T M) g)
    (hyW : y ∉ wOfU T M) (hu : u ∈ uOfL22 T M)
    (hyu : y * u * y⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T) : u ∈ wOfU T M := by
  by_contra huW
  exact hyW (h.mem_inf_of_commutator_mem hU hg hu huW hy
    (h.omegaOneCenter_le_inf_rconj hU hg hyu)).1

theorem lemma_12_8_9_seven (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) :
    rconj (quasithinOmegaOneCenter T) g ⊓ centerOf (uOfL22 T M) = ⊥ := by
  have hle : rconj (quasithinOmegaOneCenter T) g ≤ VZ T M :=
    (h.l2Setting128 hU).V₁_le_rconj_V hg.mem
  have hTI := (h.l2Setting128 hU).V₁_inf_rconj hg.mem hg.not_mem
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ VZ T M ⊓ centerOf (uOfL22 T M) := ⟨hle hx.1, hx.2⟩
  rw [h.lemma_12_8_8_three hU] at h1
  have h2 : x ∈ quasithinOmegaOneCenter T ⊓ rconj (quasithinOmegaOneCenter T) g := ⟨h1, hx.1⟩
  rw [hTI] at h2
  exact h2

theorem rconj_wOfU_le_T (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) : rconj (wOfU T M) g ≤ T :=
  (h.rconj_wOfU_le_pCoreOf hU hg).trans (h.pCoreOf_sup_uOfL22_le_T hU hg)

theorem lemma_12_8_9_five (h : Hyp1281Two G T M L) (hU : ¬ IsMulCommutative ↥(uOfL22 T M))
    {g : G} (hg : GoodElt128 T L g) :
    centralizerMod (centerOf (uOfL22 T M)) (rconj (wOfU T M) g) (uOfL22 T M) =
        wOfU T M ⊓ rconj (wOfU T M) g ∧
      centralizerMod (quasithinOmegaOneCenter T) (rconj (wOfU T M) g) (uOfL22 T M) =
        wOfU T M ⊓ rconj (wOfU T M) g := by
  set U := uOfL22 T M with hUdef
  set Z := quasithinOmegaOneCenter T with hZdef
  set Zu := centerOf U with hZudef
  set W := wOfU T M with hWdef
  set X := rconj W g with hXdef
  set E := W ⊓ X with hEdef
  set H := Subgroup.centralizer (Z : Set G) with hHdef
  have hA := h.almostSpecialHyp_g1
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := h.g1_le_normalizer_uOfL22
  have hHZu : H ≤ Subgroup.normalizer (Zu : Set G) :=
    hHU.trans (normalizer_le_normalizer_centerOf U)
  have hHN : H ≤ Subgroup.normalizer (Z : Set G) := Subgroup.centralizer_le_normalizer _
  set C := centralizerMod Zu H U with hCdef
  have hHC : H ≤ Subgroup.normalizer (C : Set G) :=
    le_normalizer_centralizerMod hHZu Subgroup.le_normalizer hHU
  set R := T ⊓ C with hRdef
  set F := centralizerMod Z U R with hFdef
  have hUH : U ≤ H := h.uOfL22_le_g1
  have hfr := fun x (hx : x ∈ H) => exists_mul_mem_normalizer_inf_of_isSylowTwoOf hHC hA.sylow_H hx
  have hFn : ∀ n ∈ H, n ∈ Subgroup.normalizer (R : Set G) → n ∈ Subgroup.normalizer (F : Set G) := by
    intro n hn hnR
    have hz : Subgroup.zpowers n ≤ Subgroup.normalizer (F : Set G) :=
      le_normalizer_centralizerMod (V₁ := Z) (X := U) (U := R)
        (Subgroup.zpowers_le.mpr (hHN hn)) (Subgroup.zpowers_le.mpr (hHU hn))
        (Subgroup.zpowers_le.mpr hnR)
    exact hz (Subgroup.mem_zpowers n)
  have hVF : VZ T M ≤ F := by
    intro v hv
    refine ⟨VZ_le_uOfL22 T M hv, hA.V_le_N hv, fun r hr => ?_⟩
    have hrT : r ∈ T := hr.1
    have hrC : r ∈ C := hr.2
    have hrN : r ∈ Subgroup.normalizer (VZ T M : Set G) :=
      (h.inM.2.trans h.isTwoReducedIn.1.2.1) hrT
    have h1 : r * v * r⁻¹ * v⁻¹ ∈ VZ T M :=
      (VZ T M).mul_mem ((Subgroup.mem_normalizer_iff.mp hrN v).mp hv) ((VZ T M).inv_mem hv)
    have h2 : r * v * r⁻¹ * v⁻¹ ∈ Zu := hrC.2.2 v (VZ_le_uOfL22 T M hv)
    have h3 : r * v * r⁻¹ * v⁻¹ ∈ VZ T M ⊓ Zu := ⟨h1, h2⟩
    rw [h.lemma_12_8_8_three hU] at h3
    have e : v * r * v⁻¹ * r⁻¹ = (r * v * r⁻¹ * v⁻¹)⁻¹ := by group
    rw [e]
    exact Z.inv_mem h3
  have hUF : U ≤ F ⊔ Zu := by
    refine conjClosure_le fun x hx v hv => ?_
    obtain ⟨c, hc, n, hnH, hnR, rfl⟩ := hfr x hx
    have hnF : n ∈ Subgroup.normalizer (F : Set G) := hFn n hnH hnR
    have hf : n * v * n⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hnF v).mp (hVF hv)
    have hfU : n * v * n⁻¹ ∈ U := hf.1
    have hcf : c * (n * v * n⁻¹) * c⁻¹ * (n * v * n⁻¹)⁻¹ ∈ Zu := hc.2.2 _ hfU
    have e : c * n * v * (c * n)⁻¹ =
        (c * (n * v * n⁻¹) * c⁻¹ * (n * v * n⁻¹)⁻¹) * (n * v * n⁻¹) := by group
    rw [e]
    have := Subgroup.mul_mem_sup hcf hf
    rwa [sup_comm] at this
  obtain ⟨u, huF, huW⟩ : ∃ u ∈ F, u ∉ W := by
    by_contra hall
    push Not at hall
    apply h.not_le_centralizer_VZ_of_nonabelian hU
    have : U ≤ W := hUF.trans (sup_le (fun u hu => hall u hu) (centerOf_uOfL22_le_wOfU T M))
    exact fun x hx => (this hx).2
  have key : centralizerMod Zu X U ≤ E := by
    intro y hy
    obtain ⟨hyX, hyN, hyc⟩ := hy
    have hyT : y ∈ T := h.rconj_wOfU_le_T hU hg hyX
    have hyH : y ∈ H := hA.T_le_H hyT
    have hyC : y ∈ C := ⟨hyH, hyN, hyc⟩
    have hyR : y ∈ R := ⟨hyT, hyC⟩
    by_contra hyE
    have hyW : y ∉ W := fun hyW => hyE ⟨hyW, hyX⟩
    have hcomm : y * u * y⁻¹ * u⁻¹ ∈ Z := by
      have h1 := huF.2.2 y hyR
      have e : y * u * y⁻¹ * u⁻¹ = (u * y * u⁻¹ * y⁻¹)⁻¹ := by group
      rw [e]
      exact Z.inv_mem h1
    exact huW (h.lemma_12_8_9_four hU hg hyX hyW huF.1 hcomm)
  have hEX : E ≤ X := inf_le_right
  have hEU : ∀ e ∈ E, e ∈ U := fun e he => wOfU_le_uOfL22 T M he.1
  have hE1 : E ≤ centralizerMod Z X U := by
    intro e he
    exact ⟨hEX he, hHN (hUH (hEU e he)), fun u hu =>
      h.commutator_mem_omegaOneCenter (hEU e he) hu⟩
  have hE2 : centralizerMod Z X U ≤ centralizerMod Zu X U := by
    intro y hy
    obtain ⟨hyX, hyN, hyc⟩ := hy
    have hyH : y ∈ H := by
      show y ∈ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G)
      rw [← h.normalizer_Z_eq_centralizer]
      exact hyN
    exact ⟨hyX, hHZu hyH, fun u hu => h.omegaOneCenter_le_centerOf_uOfL22 (hyc u hu)⟩
  exact ⟨le_antisymm key (hE1.trans hE2), le_antisymm ((hE2.trans key)) hE1⟩

end Hyp1281Two

end CFSG.Quasithin
