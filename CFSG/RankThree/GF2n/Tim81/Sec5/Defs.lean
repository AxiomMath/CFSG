module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec45Shape
public import CFSG.RankThree.GroupTheory.SteinbergBYAlphaTransport

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.Quasithin
open CFSG.Quasithin.JonesParshall CFSG.QuasithinUnique.Setup.X7 CFSG.Timmesfeld.Bridge
open CFSG.Timmesfeld
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {M V : Subgroup G}

abbrev omegaSet (V : Subgroup G) : Set (Subgroup G) := Tim79a.omegaOf V ⊤

abbrev hOf (M V : Subgroup G) (g : G) : Subgroup G := Pc M V ⊔ conjSubgroup g (Pc M V)

@[expose] def sigmaSet (M V : Subgroup G) : Set (Subgroup G) :=
  {U | ∃ g : G, U = conjSubgroup g V ∧ IsHMember M V (hOf M V g)}

@[expose] def fSet (M V : Subgroup G) : Set (Subgroup G) :=
  {A | A ≤ Pc M V ∧ Nat.card A = Nat.card V ^ 2 ∧
    ∃ U ∈ sigmaSet M V, ∃ x ∈ Pc M V, A = V ⊔ ⁅U, Subgroup.zpowers x⁆}

@[expose] def IsL2Gen (A B : Subgroup G) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F) (_ : CharP F 2) (φ : ↥(A ⊔ B) ≃* SL(2, F)),
    Nat.card F = Nat.card A ∧
      (A.subgroupOf (A ⊔ B)).map φ.toMonoidHom = utri F ∧
      (B.subgroupOf (A ⊔ B)).map φ.toMonoidHom = ltri F

structure Sec5Hyp (M V : Subgroup G) : Prop where
  root : ∀ a : G, RootHyp (conjSubgroup a M) (conjSubgroup a V)
  sec45 : ∀ a : G, Sec45At (conjSubgroup a M) (conjSubgroup a V)
  le_pCore : ∀ (a : G) (L : Subgroup G),
    IsHMember (conjSubgroup a M) (conjSubgroup a V) L → conjSubgroup a V ≤ inSubgroup (pCore 2) L

theorem Sec5Hyp.toRootHyp (hS : Sec5Hyp M V) : RootHyp M V := by
  simpa [conjSubgroup_one] using hS.root 1

theorem Sec5Hyp.conj (hS : Sec5Hyp M V) (a : G) :
    Sec5Hyp (conjSubgroup a M) (conjSubgroup a V) where
  root b := by
    simp only [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact hS.root (b * a)
  sec45 b := by
    simp only [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    exact hS.sec45 (b * a)
  le_pCore b L hL := by
    simp only [CGT.Timmesfeld75.conjSubgroup_conjSubgroup] at hL ⊢
    exact hS.le_pCore (b * a) L hL

theorem Pc_conjSubgroup (M V : Subgroup G) (a : G) :
    Pc (conjSubgroup a M) (conjSubgroup a V) = conjSubgroup a (Pc M V) := by
  have hp : inSubgroup (pCore 2) (conjSubgroup a M) =
      conjSubgroup a (inSubgroup (pCore 2) M) := by
    have h := CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore 2 (MulAut.conj a) M
    rw [show M.map (MulAut.conj a).toMonoidHom = conjSubgroup a M from rfl] at h
    exact h.symm
  unfold Pc
  rw [hp, centralizer_conjSubgroup_eq, ← conjSubgroup_inf]

theorem isHMember_conjSubgroup_iff (a : G) {M V L : Subgroup G} :
    IsHMember (conjSubgroup a M) (conjSubgroup a V) (conjSubgroup a L) ↔ IsHMember M V L := by
  have hp : inSubgroup (pCore 2) (conjSubgroup a L) =
      conjSubgroup a (inSubgroup (pCore 2) L) := by
    have h := CFSG.RankThree.GroupTheory.SteinbergBY.map_inSubgroup_pCore 2 (MulAut.conj a) L
    rw [show L.map (MulAut.conj a).toMonoidHom = conjSubgroup a L from rfl] at h
    exact h.symm
  unfold IsHMember
  rw [hp, Pc_conjSubgroup]
  constructor
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hbot
      apply h1
      rw [hbot]
      exact conjSubgroup_eq_bot_iff.mpr rfl
    · intro x hx
      have h2' := conjSubgroup_mono (g := a⁻¹) h2
      simp only [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel,
        conjSubgroup_one] at h2'
      exact h2' hx
    · intro hle
      exact h3 (conjSubgroup_mono (g := a) hle)
  · rintro ⟨h1, h2, h3⟩
    refine ⟨?_, ?_, ?_⟩
    · intro hbot
      apply h1
      exact conjSubgroup_eq_bot_iff.mp hbot
    · exact conjSubgroup_mono (g := a) h2
    · intro hle
      have h3' := conjSubgroup_mono (g := a⁻¹) hle
      simp only [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel,
        conjSubgroup_one] at h3'
      exact h3 h3'

theorem mem_sigmaSet_iff (h : Hyp M V) {g : G} :
    conjSubgroup g V ∈ sigmaSet M V ↔ IsHMember M V (hOf M V g) := by
  constructor
  · rintro ⟨g', hEq, hH⟩
    have hV : conjSubgroup (g⁻¹ * g') V = V := by
      have h1 : conjSubgroup g (conjSubgroup (g⁻¹ * g') V) = conjSubgroup g V := by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, show g * (g⁻¹ * g') = g' by group]
        exact hEq.symm
      exact conjSubgroup_inj.mp h1
    have hm : g⁻¹ * g' ∈ M :=
      h.normalizer_eq ▸ mem_normalizer_iff_conjSubgroup_eq.mpr hV
    have hP : conjSubgroup g' (Pc M V) = conjSubgroup g (Pc M V) := by
      rw [show g' = g * (g⁻¹ * g') by group,
        ← CGT.Timmesfeld75.conjSubgroup_conjSubgroup g (g⁻¹ * g') (Pc M V),
        conjSubgroup_eq_self_iff.mpr (h.le_normalizer_Pc hm)]
    rwa [show hOf M V g' = hOf M V g by rw [hOf, hOf, hP]] at hH
  · intro hH
    exact ⟨g, rfl, hH⟩

theorem mem_sigmaSet_conjSubgroup_iff (a : G) {U : Subgroup G} :
    U ∈ sigmaSet (conjSubgroup a M) (conjSubgroup a V) ↔
      conjSubgroup a⁻¹ U ∈ sigmaSet M V := by
  have hOf_conj : ∀ g : G, hOf (conjSubgroup a M) (conjSubgroup a V) g =
      conjSubgroup a (hOf M V (a⁻¹ * g * a)) := by
    intro g
    unfold hOf
    rw [Pc_conjSubgroup,
      conjSubgroup_sup a (Pc M V) (conjSubgroup (a⁻¹ * g * a) (Pc M V))]
    simp only [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    rw [show a * (a⁻¹ * g * a) = g * a by group]
  constructor
  · rintro ⟨g, rfl, hH⟩
    have hH' : IsHMember M V (hOf M V (a⁻¹ * g * a)) :=
      (isHMember_conjSubgroup_iff a).mp (by rw [← hOf_conj]; exact hH)
    refine ⟨a⁻¹ * g * a, ?_, hH'⟩
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
  · rintro ⟨g, hU, hH⟩
    have hU' : U = conjSubgroup (a * g) V := by
      calc U = conjSubgroup a (conjSubgroup a⁻¹ U) := by
            rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, mul_inv_cancel, conjSubgroup_one]
        _ = conjSubgroup a (conjSubgroup g V) := by rw [hU]
        _ = conjSubgroup (a * g) V := CGT.Timmesfeld75.conjSubgroup_conjSubgroup a g V
    have hH' : IsHMember (conjSubgroup a M) (conjSubgroup a V)
        (hOf (conjSubgroup a M) (conjSubgroup a V) (a * g * a⁻¹)) := by
      rw [hOf_conj, show a⁻¹ * (a * g * a⁻¹) * a = g by group]
      exact (isHMember_conjSubgroup_iff a).mpr hH
    refine ⟨a * g * a⁻¹, ?_, hH'⟩
    rw [hU', CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
    congr 1
    group

theorem ne_of_mem_sigmaSet (h : RootHyp M V) {U : Subgroup G} (hU : U ∈ sigmaSet M V) :
    U ≠ V := by
  obtain ⟨g, rfl, hH⟩ := hU
  intro hEq
  have hm : g ∈ M :=
    h.toHyp.normalizer_eq ▸ mem_normalizer_iff_conjSubgroup_eq.mpr hEq
  have hP : conjSubgroup g (Pc M V) = Pc M V :=
    mem_normalizer_iff_conjSubgroup_eq.mp (h.toHyp.le_normalizer_Pc hm)
  apply hH.2.2
  rw [hOf, hP]
  exact sup_le h.toHyp.Pc_le_M h.toHyp.Pc_le_M

theorem Sec5Hyp.le_M_of_mem_sigmaSet (hS : Sec5Hyp M V) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) : U ≤ M ∧ U ≤ Subgroup.centralizer (V : Set G) := by
  obtain ⟨g, rfl, hH⟩ := hU
  have h := hS.toRootHyp
  have hPH : Pc M V ≤ hOf M V g := le_sup_left
  have hVH : V ≤ inSubgroup (pCore 2) (hOf M V g) := by
    simpa [conjSubgroup_one] using
      hS.le_pCore 1 (hOf M V g) (by simpa [conjSubgroup_one] using hH)
  have hW := h.isElemAbelian_xOf hPH hVH
  have hWM : Tim79a.xOf V (hOf M V g) ≤ M := h.xOf_le_M hPH hVH
  obtain ⟨y, hyH, -, hVy, -⟩ := h.exists_mem_conj_eq_of_eq_sup hPH rfl
  have hUx : conjSubgroup g V ≤ Tim79a.xOf V (hOf M V g) := by
    rw [hVy]
    exact Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf hyH)
  have hVx : V ≤ Tim79a.xOf V (hOf M V g) := by
    calc V = conjSubgroup 1 V := (conjSubgroup_one V).symm
      _ ≤ Tim79a.xOf V (hOf M V g) :=
          Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf (H := hOf M V g) (hOf M V g).one_mem)
  refine ⟨hUx.trans hWM, ?_⟩
  intro u hu
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hcomm := hW.1.is_comm.comm
    (⟨v, hVx hv⟩ : ↥(Tim79a.xOf V (hOf M V g)))
    (⟨u, hUx hu⟩ : ↥(Tim79a.xOf V (hOf M V g)))
  exact congrArg Subtype.val hcomm

theorem RootHyp.isHMember_hOf_conj_iff (h : RootHyp M V) {g : G} :
    IsHMember (conjSubgroup g M) (conjSubgroup g V) (hOf M V g) ↔
      IsHMember M V (hOf M V g) := by
  obtain ⟨y, hyH, -, hVy, -⟩ :=
    h.exists_mem_conj_eq_of_eq_sup (le_sup_left : Pc M V ≤ hOf M V g) rfl
  have hgy : g⁻¹ * y ∈ M := by
    have hV : conjSubgroup (g⁻¹ * y) V = V := by
      have h1 : conjSubgroup g (conjSubgroup (g⁻¹ * y) V) = conjSubgroup g V := by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, show g * (g⁻¹ * y) = y by group, hVy]
      exact conjSubgroup_inj.mp h1
    exact h.toHyp.normalizer_eq ▸ mem_normalizer_iff_conjSubgroup_eq.mpr hV
  have hMy : conjSubgroup y M = conjSubgroup g M := by
    calc conjSubgroup y M = conjSubgroup g (conjSubgroup (g⁻¹ * y) M) := by
          rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup]
          congr 1
          group
      _ = conjSubgroup g M := by
          rw [conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hgy)]
  constructor
  · rintro ⟨h1, -, h3⟩
    refine ⟨h1, le_sup_left, ?_⟩
    intro hle
    apply h3
    have hHy : conjSubgroup y (hOf M V g) = hOf M V g :=
      conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hyH)
    have hle' := conjSubgroup_mono (g := y) hle
    rwa [hHy, hMy] at hle'
  · rintro ⟨h1, -, h3⟩
    refine ⟨h1, ?_, ?_⟩
    · rw [Pc_conjSubgroup]
      exact le_sup_right
    · intro hle
      apply h3
      have hHy : conjSubgroup y⁻¹ (hOf M V g) = hOf M V g :=
        conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer ((hOf M V g).inv_mem hyH))
      have hgy' : y⁻¹ * g ∈ M := by
        simpa [mul_inv_rev, inv_inv] using M.inv_mem hgy
      have hMy' : conjSubgroup y⁻¹ (conjSubgroup g M) = M := by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup,
          conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hgy')]
      have hle' := conjSubgroup_mono (g := y⁻¹) hle
      rwa [hHy, hMy'] at hle'

theorem Sec5Hyp.mem_sigmaSet_iff_self_mem (hS : Sec5Hyp M V) {g : G} :
    conjSubgroup g V ∈ sigmaSet M V ↔ V ∈ sigmaSet (conjSubgroup g M) (conjSubgroup g V) := by
  have h := hS.toRootHyp
  have hRHS : (V ∈ sigmaSet (conjSubgroup g M) (conjSubgroup g V)) ↔
      IsHMember (conjSubgroup g M) (conjSubgroup g V) (hOf M V g) := by
    have hV : V = conjSubgroup g⁻¹ (conjSubgroup g V) := by
      rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]
    have hV' : (V ∈ sigmaSet (conjSubgroup g M) (conjSubgroup g V)) =
        (conjSubgroup g⁻¹ (conjSubgroup g V) ∈
          sigmaSet (conjSubgroup g M) (conjSubgroup g V)) :=
      congrArg (fun x => x ∈ sigmaSet (conjSubgroup g M) (conjSubgroup g V)) hV
    rw [hV', mem_sigmaSet_iff (hS.root g).toHyp]
    rw [show hOf (conjSubgroup g M) (conjSubgroup g V) g⁻¹ = hOf M V g by
      unfold hOf
      rw [Pc_conjSubgroup]
      rw [show conjSubgroup g⁻¹ (conjSubgroup g (Pc M V)) = Pc M V by
        rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]]
      exact sup_comm _ _]
  rw [mem_sigmaSet_iff h.toHyp, hRHS]
  exact h.isHMember_hOf_conj_iff.symm

theorem Sec5Hyp.conj_mem_sigmaSet (hS : Sec5Hyp M V) {m : G} (hm : m ∈ M) {U : Subgroup G}
    (hU : U ∈ sigmaSet M V) : conjSubgroup m U ∈ sigmaSet M V := by
  obtain ⟨g, rfl, hH⟩ := hU
  have h := hS.toRootHyp
  have hMm : conjSubgroup m M = M :=
    conjSubgroup_eq_self_iff.mpr (Subgroup.le_normalizer hm)
  have hVm : conjSubgroup m V = V :=
    conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer hm)
  rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup m g V]
  refine (mem_sigmaSet_iff h.toHyp).mpr ?_
  have hHconj : hOf M V (m * g) = conjSubgroup m (hOf M V g) := by
    unfold hOf
    rw [← CGT.Timmesfeld75.conjSubgroup_conjSubgroup m g (Pc M V), conjSubgroup_sup,
      conjSubgroup_eq_self_iff.mpr (h.toHyp.le_normalizer_Pc hm)]
  rw [hHconj]
  have := (isHMember_conjSubgroup_iff (M := M) (V := V) (L := hOf M V g) m).mpr hH
  rwa [hMm, hVm] at this

theorem Sec5Hyp.conj_inv_mem_sigmaSet_iff (hS : Sec5Hyp M V) {g : G} :
    conjSubgroup g V ∈ sigmaSet M V ↔ conjSubgroup g⁻¹ V ∈ sigmaSet M V := by
  have h := hS.toRootHyp
  rw [mem_sigmaSet_iff h.toHyp, mem_sigmaSet_iff h.toHyp]
  have hOf_inv : hOf M V g⁻¹ = conjSubgroup g⁻¹ (hOf M V g) := by
    unfold hOf
    rw [conjSubgroup_sup, CGT.Timmesfeld75.conjSubgroup_conjSubgroup, inv_mul_cancel,
      conjSubgroup_one]
    exact sup_comm _ _
  have h1 : IsHMember M V (hOf M V g⁻¹) ↔
      IsHMember (conjSubgroup g⁻¹ M) (conjSubgroup g⁻¹ V) (hOf M V g⁻¹) :=
    h.isHMember_hOf_conj_iff.symm
  rw [hOf_inv] at h1 ⊢
  exact (h1.trans (isHMember_conjSubgroup_iff g⁻¹)).symm

theorem IsL2Gen.symm {A B : Subgroup G} (h : IsL2Gen A B) : IsL2Gen B A := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, hB⟩ := h
  letI := hField
  letI := hFin
  letI := hCharP
  have hltri_utri : Nat.card (ltri F) = Nat.card (utri F) := by
    rw [← conjSubgroup_wElt_utri]
    exact Subgroup.card_map_of_injective (MulAut.conj wElt).injective
  have hBcard : Nat.card F = Nat.card B := by
    have h1 : Nat.card (B.subgroupOf (A ⊔ B)) = Nat.card (ltri F) := by
      rw [← hB, Subgroup.card_map_of_injective φ.injective]
    rw [hltri_utri, card_utri,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe (le_sup_right : B ≤ A ⊔ B)).toEquiv] at h1
    exact h1.symm
  have hw2 : (wElt : SL(2, F)) * wElt = 1 := by
    rw [← eq_inv_iff_mul_eq_one]
    apply sl2_ext <;>
      simp [CharTwo.neg_eq, inv_apply_00, inv_apply_01, inv_apply_10, inv_apply_11,
        wElt_apply_00, wElt_apply_01, wElt_apply_10, wElt_apply_11]
  have hltri : CGT.Timmesfeld75.conjSubgroup wElt (ltri F) = utri F := by
    have h1 := congrArg (CGT.Timmesfeld75.conjSubgroup (wElt : SL(2, F)))
      conjSubgroup_wElt_utri
    rw [CGT.Timmesfeld75.conjSubgroup_conjSubgroup, hw2, conjSubgroup_one] at h1
    exact h1.symm
  let e : ↥(B ⊔ A) ≃* ↥(A ⊔ B) := MulEquiv.subgroupCongr (sup_comm B A)
  let ψ : ↥(B ⊔ A) ≃* SL(2, F) := e.trans (φ.trans (MulAut.conj wElt))
  have hBe : (B.subgroupOf (B ⊔ A)).map e.toMonoidHom = B.subgroupOf (A ⊔ B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by
        have hy' : (y : G) ∈ B := Subgroup.mem_subgroupOf.mp hy
        exact hy')
    · intro hx
      exact Subgroup.mem_map.mpr
        ⟨⟨(x : G), Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mp hx)⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), Subtype.ext rfl⟩
  have hAe : (A.subgroupOf (B ⊔ A)).map e.toMonoidHom = A.subgroupOf (A ⊔ B) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (by
        have hy' : (y : G) ∈ A := Subgroup.mem_subgroupOf.mp hy
        exact hy')
    · intro hx
      exact Subgroup.mem_map.mpr
        ⟨⟨(x : G), Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mp hx)⟩,
          Subgroup.mem_subgroupOf.mpr (Subgroup.mem_subgroupOf.mp hx), Subtype.ext rfl⟩
  have hψ : ψ.toMonoidHom = (φ.trans (MulAut.conj wElt)).toMonoidHom.comp e.toMonoidHom := by
    ext x
    rfl
  have hconj : (φ.trans (MulAut.conj wElt)).toMonoidHom =
      (MulAut.conj wElt).toMonoidHom.comp φ.toMonoidHom := by
    ext x
    rfl
  have hBmap : (B.subgroupOf (B ⊔ A)).map ψ.toMonoidHom = utri F := by
    rw [hψ, ← Subgroup.map_map, hBe, hconj, ← Subgroup.map_map, hB]
    exact hltri
  have hAmap : (A.subgroupOf (B ⊔ A)).map ψ.toMonoidHom = ltri F := by
    rw [hψ, ← Subgroup.map_map, hAe, hconj, ← Subgroup.map_map, hA]
    exact conjSubgroup_wElt_utri
  exact ⟨F, hField, hFin, hCharP, ψ, hBcard, hBmap, hAmap⟩

theorem IsL2Gen.isL2Pair {A B : Subgroup G} (h : IsL2Gen A B) :
    IsL2Pair ↥(A ⊔ B) (A.subgroupOf (A ⊔ B)) (Nat.card A) := by
  obtain ⟨F, hField, hFin, hCharP, φ, hcard, hA, -⟩ := h
  exact ⟨F, hField, hFin, hCharP, φ, hcard, hA⟩

theorem Sec5Hyp.shape (hS : Sec5Hyp M V) {g : G} (hg : conjSubgroup g V ∈ sigmaSet M V) :
    Sec45Shape M V (hOf M V g) g := by
  have hAt : Sec45At M V := by
    simpa [conjSubgroup_one] using hS.sec45 1
  exact hAt g ((mem_sigmaSet_iff hS.toRootHyp.toHyp).mp hg)

end CFSG.RankThree.GF2n.Tim81
