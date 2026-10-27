module

public import CFSG.LocalAnalysis.WeakClosure81.W172Cal
public import CFSG.LocalAnalysis.WeakClosure81.W172Facts
public import CFSG.LocalAnalysis.WeakClosure81.W18PackG

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (InCalA)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace MinCex172

variable {D : Data G} {V₀ V H : Subgroup G}

private theorem w172_local_normalizer_le_normalizer_centralizer (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer (X : Set G) : Set G) :=
  Subgroup.le_normalizer_of_normal_subgroupOf (H := Subgroup.centralizer (X : Set G))
    (K := Subgroup.normalizer (X : Set G))
    (Subgroup.centralizer_le_normalizer (X : Set G))

private theorem w172_local_relIndex_inf_le_relIndex_sup (A B : Subgroup G) :
    (A ⊓ B).relIndex A ≤ B.relIndex (A ⊔ B) := by
  have hcard : (A ⊓ B).relIndex A = (B.subgroupOf A).index := by
    show ((A ⊓ B).subgroupOf A).index = (B.subgroupOf A).index
    rw [Subgroup.inf_subgroupOf_left]
  rw [hcard]
  exact Finite.card_le_of_embedding
    (Subgroup.quotientSubgroupOfEmbeddingOfLE (α := G) B (le_sup_left : A ≤ A ⊔ B))

private theorem w172_local_padicValNat_two_le_one_of_lt_four {n : ℕ} (hn : n < 4) :
    padicValNat 2 n ≤ 1 := by
  by_contra h
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h2 : 2 ≤ padicValNat 2 n := by omega
  have hn0 : n ≠ 0 := by
    rintro rfl
    simp only [padicValNat_zero_right] at h2
    omega
  have h4 : 2 ^ 2 ∣ n := (padicValNat_dvd_iff_le (p := 2) (a := n) hn0).mpr h2
  have h4' : 4 ∣ n := by simpa using h4
  have : 4 ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero hn0) h4'
  omega

private theorem w172_local_mem_sup_of_le_normalizer {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) {x : G} :
    x ∈ A ⊔ C ↔ ∃ a ∈ A, ∃ c ∈ C, a * c = x := by
  constructor
  · intro hx
    have hx' : x ∈ (A : Set G) * (C : Set G) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right A C hAC]
      exact hx
    exact Set.mem_mul.mp hx'
  · rintro ⟨a, ha, c, hc, rfl⟩
    show a * c ∈ (↑(A ⊔ C) : Set G)
    rw [Subgroup.coe_mul_of_left_le_normalizer_right A C hAC]
    exact Set.mem_mul.mpr ⟨a, ha, c, hc, rfl⟩

private theorem w172_local_conj_mem {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) {a : G} (ha : a ∈ A) {c : G} (hc : c ∈ C) :
    a * c * a⁻¹ ∈ C :=
  (Subgroup.mem_normalizer_iff.mp (hAC ha) c).mp hc

private theorem w172_local_sq_mem_of_mem_sup {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G)) (hA2 : ∀ a ∈ A, a * a = 1) {x : G}
    (hx : x ∈ A ⊔ C) : x * x ∈ C := by
  obtain ⟨a, ha, c, hc, rfl⟩ := (w172_local_mem_sup_of_le_normalizer hAC).mp hx
  have h1 : (a * c) * (a * c) = (a * c * a⁻¹) * (a * a) * c := by group
  rw [h1, hA2 a ha, mul_one]
  exact C.mul_mem (w172_local_conj_mem hAC ha hc) hc

private theorem w172_local_commutator_mem_of_mem_sup {A C : Subgroup G}
    (hAC : A ≤ Subgroup.normalizer (C : Set G))
    (hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a) {x y : G} (hx : x ∈ A ⊔ C)
    (hy : y ∈ A ⊔ C) : x * y * x⁻¹ * y⁻¹ ∈ C := by
  obtain ⟨a, ha, c, hc, rfl⟩ := (w172_local_mem_sup_of_le_normalizer hAC).mp hx
  obtain ⟨a', ha', c', hc', rfl⟩ := (w172_local_mem_sup_of_le_normalizer hAC).mp hy
  have hkey : (a * c) * (a' * c') * (a * c)⁻¹ * (a' * c')⁻¹ =
      (a * c * a⁻¹) * ((a * a') * c' * (a * a')⁻¹) *
        ((a * a') * c⁻¹ * (a * a')⁻¹) *
        ((a * a' * a⁻¹) * c'⁻¹ * (a * a' * a⁻¹)⁻¹) * (a * a' * a⁻¹ * a'⁻¹) := by
    group
  rw [hkey]
  have h1 : a * c * a⁻¹ ∈ C := w172_local_conj_mem hAC ha hc
  have h2 : (a * a') * c' * (a * a')⁻¹ ∈ C :=
    w172_local_conj_mem hAC (A.mul_mem ha ha') hc'
  have h3 : (a * a') * c⁻¹ * (a * a')⁻¹ ∈ C :=
    w172_local_conj_mem hAC (A.mul_mem ha ha') (C.inv_mem hc)
  have h4 : (a * a' * a⁻¹) * c'⁻¹ * (a * a' * a⁻¹)⁻¹ ∈ C :=
    w172_local_conj_mem hAC (A.mul_mem (A.mul_mem ha ha') (A.inv_mem ha)) (C.inv_mem hc')
  have h5 : a * a' * a⁻¹ * a'⁻¹ = 1 := by rw [hAcomm a ha a' ha']; group
  rw [h5, mul_one]
  exact C.mul_mem (C.mul_mem (C.mul_mem h1 h2) h3) h4

theorem w172_inf_ne_bot (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) : eOmegaZ H D.T ⊓ conjSubgroup V₀ g ≠ ⊥ := by
  classical
  set E := eOmegaZ H D.T
  set A := vInH V H g
  set C : Subgroup G := H ⊓ Subgroup.centralizer (E : Set G)
  have hAH : A ≤ H := inf_le_right
  have hAE : A ≤ conjSubgroup V g := inf_le_left
  have hAab : IsElemAbelian 2 A :=
    (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g).mono inf_le_left
  have hCnormH : H ≤ Subgroup.normalizer (C : Set G) := by
    rw [show C = H ⊓ Subgroup.centralizer (E : Set G) from rfl]
    exact (le_inf H.le_normalizer
      ((Hyp183.normalizer_eOmegaZ H D.T).trans
        (w172_local_normalizer_le_normalizer_centralizer E))).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hAC : A ≤ Subgroup.normalizer (C : Set G) := hAH.trans hCnormH
  have hAcomm : ∀ a ∈ A, ∀ a' ∈ A, a * a' = a' * a := fun a ha a' ha' => hAab.comm ha ha'
  have hA2 : ∀ a ∈ A, a * a = 1 := fun a ha => by simpa [pow_two] using hAab.2 a ha
  have hP1 : C ≤ A ⊔ C := le_sup_right
  have hP2 : A ⊔ C ≤ H := sup_le hAH inf_le_left
  have hP3 : ¬ A ⊔ C ≤ Subgroup.centralizer (E : Set G) :=
    fun h => hg.2 (le_sup_left.trans h)
  have hCle : C ≤ Subgroup.centralizer (E : Set G) := inf_le_right
  have hP4 : ∀ x ∈ A ⊔ C, ∀ y ∈ A ⊔ C, x * y * x⁻¹ * y⁻¹ ∈
      Subgroup.centralizer (E : Set G) :=
    fun x hx y hy => hCle (w172_local_commutator_mem_of_mem_sup hAC hAcomm hx hy)
  have hP5 : ∀ x ∈ A ⊔ C, x * x ∈ Subgroup.centralizer (E : Set G) :=
    fun x hx => hCle (w172_local_sq_mem_of_mem_sup hAC hA2 hx)
  have hnotmem : ¬ InCalA 2 H E (A ⊔ C) := (c.ctx188 h162).not_inCalA A hAH hAab
  have hex : ∃ B : Subgroup G, C ≤ B ∧ B ≤ A ⊔ C ∧ B.relIndex (A ⊔ C) < 2 ^ 2 ∧
      E ⊓ Subgroup.centralizer ((A ⊔ C : Subgroup G) : Set G) ≠
        E ⊓ Subgroup.centralizer (B : Set G) := by
    by_contra hcon
    apply hnotmem
    refine ⟨hP1, hP2, hP3, hP4, hP5, fun B hCB hBA hBrel => ?_⟩
    by_contra hne
    exact hcon ⟨B, hCB, hBA, hBrel, hne⟩
  obtain ⟨B, hCB, hBsup, hBrel, hBne⟩ := hex
  have hleCent : E ⊓ Subgroup.centralizer ((A ⊔ C : Subgroup G) : Set G) ≤
      E ⊓ Subgroup.centralizer (B : Set G) :=
    inf_le_inf_left E (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBsup))
  have hltCent : E ⊓ Subgroup.centralizer ((A ⊔ C : Subgroup G) : Set G) <
      E ⊓ Subgroup.centralizer (B : Set G) := lt_of_le_of_ne hleCent hBne
  obtain ⟨e, heB, heA⟩ := SetLike.exists_of_lt hltCent
  have heE : e ∈ E := heB.1
  have heCentB : e ∈ Subgroup.centralizer (B : Set G) := heB.2
  have heNotCent : e ∉ Subgroup.centralizer ((A ⊔ C : Subgroup G) : Set G) :=
    fun h => heA ⟨heE, h⟩
  have hx : ∃ x ∈ (A ⊔ C : Subgroup G), x * e ≠ e * x := by
    by_contra h
    apply heNotCent
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    by_contra hne
    exact h ⟨x, hx, hne⟩
  obtain ⟨x, hx, hxe⟩ := hx
  obtain ⟨a, ha, cc, hcc, rfl⟩ := (w172_local_mem_sup_of_le_normalizer hAC).mp hx
  have hce : cc * e = e * cc := (Subgroup.mem_centralizer_iff.mp hcc.2 e heE).symm
  have hae : a * e ≠ e * a := by
    intro h
    apply hxe
    calc a * cc * e = a * (cc * e) := by group
      _ = a * (e * cc) := by rw [hce]
      _ = e * (a * cc) := by rw [← mul_assoc, h, mul_assoc]
  have hsupAB : A ⊔ B = A ⊔ C :=
    le_antisymm (sup_le le_sup_left hBsup) (sup_le le_sup_left (hCB.trans le_sup_right))
  have hArel : (B ⊓ A).relIndex A ≤ B.relIndex (A ⊔ C) := by
    have h1 := w172_local_relIndex_inf_le_relIndex_sup A B
    rw [inf_comm, hsupAB] at h1
    exact h1
  have hBrel4 : B.relIndex (A ⊔ C) < 4 := by simpa using hBrel
  have hrel4 : (B ⊓ A).relIndex A < 4 := hArel.trans_lt hBrel4
  have hmB : E3.mQuot A (B ⊓ A) ≤ 1 := by
    unfold E3.mQuot
    exact w172_local_padicValNat_two_le_one_of_lt_four hrel4
  have heB' : e ∈ E ⊓ Subgroup.centralizer ((B ⊓ A : Subgroup G) : Set G) :=
    ⟨heE, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr inf_le_left) heCentB⟩
  have hk : 1 + 1 < mBar D.M V₀ V (c.ctx188 h162).hyp.setting.isElemAbelian := by
    have := (c.ctx188 h162).bound
    omega
  have hcomm := (c.ctx188 h162).comm_le (k := 1) hk hg (B := B ⊓ A) inf_le_right hmB
  have hmem : ⁅e, a⁆ ∈ ⁅E ⊓ Subgroup.centralizer ((B ⊓ A : Subgroup G) : Set G), A⁆ :=
    Subgroup.commutator_mem_commutator heB' ha
  have hmem' : ⁅e, a⁆ ∈ E ⊓ conjSubgroup V₀ g := hcomm hmem
  have hcomm_ne : ⁅e, a⁆ ≠ 1 :=
    fun h => hae ((commutatorElement_eq_one_iff_mul_comm).1 h).symm
  intro hbot
  rw [hbot] at hmem'
  exact hcomm_ne (by simpa using hmem')

theorem w172_centralizer_le_conj_M (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) :
    Subgroup.centralizer (eOmegaZ H D.T : Set G) ≤ conjSubgroup D.M g := by
  set E := eOmegaZ H D.T
  have hne := w172_inf_ne_bot h162 c hg
  have hlt : (⊥ : Subgroup G) < E ⊓ conjSubgroup V₀ g := bot_lt_iff_ne_bot.mpr hne
  obtain ⟨w, hw, hwbot⟩ := SetLike.exists_of_lt hlt
  have hw1 : w ≠ 1 := fun h => hwbot (Subgroup.mem_bot.mpr h)
  refine (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hw.1)).trans ?_
  exact w172_centralizer_le_conj c.hyp.setting c.hyp.ne_bot hw.2 hw1

theorem w172_le_conj_M (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) : eOmegaZ H D.T ≤ conjSubgroup D.M g :=
  (Subgroup.le_centralizer_iff_isMulCommutative.mpr
    c.hyp.isElemAbelian_eOmegaZ.1).trans (w172_centralizer_le_conj_M h162 c hg)

theorem w172_quadratic (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g) :
    ⁅⁅eOmegaZ H D.T, vInH V H g⁆, vInH V H g⁆ = ⊥ := by
  set E := eOmegaZ H D.T
  set A := vInH V H g
  have hAE : A ≤ conjSubgroup V g := inf_le_left
  have hMnormg : Subgroup.normalizer (conjSubgroup V g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, c.hyp.setting.normalizer_eq]
  have hEnorm : E ≤ Subgroup.normalizer (conjSubgroup V g : Set G) := by
    rw [hMnormg]
    exact w172_le_conj_M h162 c hg
  have hcomm1 : ⁅E, A⁆ ≤ conjSubgroup V g := by
    refine Subgroup.commutator_le.mpr fun e he a ha => ?_
    have haV : a ∈ conjSubgroup V g := hAE ha
    have h1 : e * a * e⁻¹ ∈ conjSubgroup V g :=
      (Subgroup.mem_normalizer_iff.mp (hEnorm he) a).mp haV
    rw [commutatorElement_def]
    exact (conjSubgroup V g).mul_mem h1 ((conjSubgroup V g).inv_mem haV)
  have hcomm2 : ⁅⁅E, A⁆, A⁆ ≤ ⁅conjSubgroup V g, conjSubgroup V g⁆ :=
    Subgroup.commutator_mono hcomm1 hAE
  have hVg_bot : ⁅conjSubgroup V g, conjSubgroup V g⁆ = ⊥ :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mpr
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr
        (E3.isElemAbelian_conjSubgroup c.hyp.setting.isElemAbelian g).1)
  exact le_bot_iff.mp (hcomm2.trans_eq hVg_bot)

theorem w172_mem_conj_of_inf_ne_bot (c : MinCex172 D V₀ V H) {g h : G}
    (hh : h ∈ H) (hne : (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) ⊓
      conjSubgroup (eOmegaZ H D.T ⊓ conjSubgroup V₀ g) h ≠ ⊥) : h ∈ conjSubgroup D.M g := by
  set E := eOmegaZ H D.T
  have hconj : conjSubgroup (E ⊓ conjSubgroup V₀ g) h = E ⊓ conjSubgroup V₀ (g * h) := by
    rw [E3.conjSubgroup_inf, conjSubgroup_conjSubgroup,
      conjSubgroup_eq_iff_mem_normalizer.mpr (Hyp183.normalizer_eOmegaZ H D.T hh)]
  have hne0 : conjSubgroup V₀ g ⊓ conjSubgroup V₀ (g * h) ≠ ⊥ := by
    intro hbot
    apply hne
    rw [hconj]
    calc (E ⊓ conjSubgroup V₀ g) ⊓ (E ⊓ conjSubgroup V₀ (g * h))
        = E ⊓ (conjSubgroup V₀ g ⊓ conjSubgroup V₀ (g * h)) := by ac_rfl
      _ = E ⊓ ⊥ := by rw [hbot]
      _ = ⊥ := by rw [inf_bot_eq]
  have hTI := c.hyp.conj_eq_of_inf_ne_bot hne0
  have hnorm : h ∈ Subgroup.normalizer (conjSubgroup V₀ g : Set G) :=
    conjSubgroup_eq_iff_mem_normalizer.mp ((conjSubgroup_conjSubgroup V₀ g h).trans hTI.1.symm)
  have hMn : Subgroup.normalizer (conjSubgroup V₀ g : Set G) = conjSubgroup D.M g := by
    rw [← E3.conjSubgroup_normalizer, c.hyp.setting.normalizer₀ c.hyp.ne_bot]
  rwa [hMn] at hnorm

theorem w172_comm_le_of_mQuot_le_one (h162 : W3Thm162Gt2 G) (c : MinCex172 D V₀ V H) {g : G}
    (hg : Gam183 V H (eOmegaZ H D.T) 1 g)
    (hm : E3.mQuot (vInH V H g) (vInH V H g ⊓ Subgroup.centralizer (eOmegaZ H D.T : Set G)) ≤ 1) :
    ⁅eOmegaZ H D.T, vInH V H g⁆ ≤ eOmegaZ H D.T ⊓ conjSubgroup V₀ g := by
  set E := eOmegaZ H D.T
  set A := vInH V H g
  have hk : 1 + 1 < mBar D.M V₀ V (c.ctx188 h162).hyp.setting.isElemAbelian := by
    have := (c.ctx188 h162).bound
    omega
  have hEcent : E ≤ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mpr inf_le_right
  have hB : E ⊓ Subgroup.centralizer
      ((A ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) : Set G) = E :=
    inf_eq_left.mpr hEcent
  have hcomm := (c.ctx188 h162).comm_le (k := 1) hk hg
    (B := A ⊓ Subgroup.centralizer (E : Set G)) inf_le_left hm
  rwa [hB] at hcomm

end MinCex172

end CFSG.LocalAnalysis.WeakClosure81

end
