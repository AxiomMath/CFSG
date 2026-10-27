module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.RegFam.FixedAux
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.L69.Basic
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.Lines
public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Sec6.T614.GenPi

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv

section Generic

variable {Γ : Type*} [Group Γ]

theorem isFStarSimple_of_mem_lcal {X J : Subgroup Γ} (hJ : J ∈ lcal X) :
    L514.IsFStarSimple ↥J := by
  obtain ⟨-, -, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have := hs
  exact L514.isFStarSimple_of_isSimpleGroup hnc

theorem lcal_eq_singleton_self {L : Subgroup Γ} (hs : IsSimpleGroup ↥L)
    (hnc : ¬ IsMulCommutative ↥L) : lcal L = {L} := by
  ext J
  rw [Set.mem_singleton_iff]
  constructor
  · intro hJ
    obtain ⟨hJL, hsub, -, hncJ⟩ := mem_lcal_iff.mp hJ
    rcases Subgroup.IsSubnormal.eq_bot_or_top_of_isSimpleGroup hs hsub with h | h
    · refine absurd ?_ hncJ
      have hJ0 : J = ⊥ := by
        refine (Subgroup.eq_bot_iff_forall J).mpr fun x hx => ?_
        have hmem : (⟨x, hJL hx⟩ : L) ∈ J.subgroupOf L := hx
        rw [h, Subgroup.mem_bot] at hmem
        exact congrArg Subtype.val hmem
      rw [hJ0]
      infer_instance
    · exact le_antisymm hJL (Subgroup.subgroupOf_eq_top.mp h)
  · rintro rfl
    refine mem_lcal_iff.mpr ⟨le_rfl, ?_, hs, hnc⟩
    rw [Subgroup.subgroupOf_self]
    exact Subgroup.Normal.isSubnormal inferInstance

theorem lcal_eq_singleton_of_isFStarSimple [Finite Γ] {L : Subgroup Γ}
    (h : L514.IsFStarSimple ↥L) : lcal L = {CFSG.inSubgroup CFSG.generalizedFitting L} :=
  T515f.lcal_eq_singleton_of_isSimpleGroup ((L514.isFStarSimple_iff_inSubgroup L).mp h).1
    ((L514.isFStarSimple_iff_inSubgroup L).mp h).2

theorem card_lcal_eq_one_of_isFStarSimple [Finite Γ] {L : Subgroup Γ}
    (h : L514.IsFStarSimple ↥L) : Nat.card (lcal L) = 1 := by
  rw [lcal_eq_singleton_of_isFStarSimple h]
  exact Nat.card_unique

theorem lcal_eq_singleton_of_mulEquiv [Finite Γ] {L L' : Subgroup Γ} (e : ↥L ≃* ↥L')
    (h : L514.IsFStarSimple ↥L') : lcal L = {CFSG.inSubgroup CFSG.generalizedFitting L} :=
  lcal_eq_singleton_of_isFStarSimple ((L514.isFStarSimple_congr e).mpr h)

theorem card_lcal_eq_one_of_mulEquiv [Finite Γ] {L L' : Subgroup Γ} (e : ↥L ≃* ↥L')
    (h : L514.IsFStarSimple ↥L') : Nat.card (lcal L) = 1 :=
  card_lcal_eq_one_of_isFStarSimple ((L514.isFStarSimple_congr e).mpr h)

theorem mem_lcal_iff_of_isDirectProduct [Finite Γ] {Ω : Set (Subgroup Γ)} {H : Subgroup Γ}
    (hΩ : IsDirectProduct Ω H) {J : Subgroup Γ} : J ∈ lcal H ↔ ∃ L ∈ Ω, J ∈ lcal L := by
  constructor
  · intro hJ
    obtain ⟨hJH, -, -, hnc⟩ := mem_lcal_iff.mp hJ
    by_contra hno
    have hcent : ∀ L ∈ Ω, J ≤ Subgroup.centralizer (L : Set Γ) := by
      intro L hL
      have hLn : (L.subgroupOf H).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer (hΩ.le hL)).mpr (hΩ.le_normalizer hL)
      rcases T515f.le_or_le_centralizer_of_mem_lcal hJ (hΩ.le hL) hLn with h | h
      · exact absurd ⟨L, hL, L511.mem_lcal_of_le hJ h (hΩ.le hL)⟩ hno
      · exact h
    refine hnc (isMulCommutative_iff.mpr fun x y => ?_)
    have hx : H ≤ Subgroup.centralizer ({(x : Γ)} : Set Γ) := by
      rw [← hΩ.sSup_eq]
      refine sSup_le fun L hL z hz => ?_
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp (hcent L hL x.2) z hz
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hx (hJH y.2))).symm
  · rintro ⟨L, hL, hJL⟩
    obtain ⟨hJL', hsub, hs, hnc⟩ := mem_lcal_iff.mp hJL
    have hLn : (L.subgroupOf H).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (hΩ.le hL)).mpr (hΩ.le_normalizer hL)
    exact mem_lcal_iff.mpr ⟨hJL'.trans (hΩ.le hL),
      T515f.isSubnormal_subgroupOf_trans hJL' (hΩ.le hL) hsub hLn.isSubnormal, hs, hnc⟩

end Generic

namespace IsRegFam

variable {G : Type*} [Group G] {A H N : Subgroup G} {Ω : Set (Subgroup G)}

theorem nonempty_mulEquiv_smear [Finite G] (hΩ : IsRegFam A H Ω N) {F : Subgroup G} (hFA : F ≤ A)
    (hFN : F ⊓ N = ⊥) {L : Subgroup G} (hL : L ∈ Ω) : Nonempty (↥(smear L F) ≃* ↥L) := by
  have hperm : ∀ f ∈ F, ∀ J ∈ Ω, J.map (MulAut.conj f).toMonoidHom ∈ Ω :=
    fun f hf J hJ => hΩ.map_conj_mem f (hFA hf) J hJ
  have hdp := CentralizerK.isDirectProduct_of_subset hΩ.isDirectProduct
    (RegFam.conjOrbit_subset hL hperm)
  rw [← RegFam.orbitClosure_eq_sSup_conjOrbit] at hdp
  refine T614.nonempty_mulEquiv_inf_centralizer hdp ?_ (RegFam.self_mem_conjOrbit L F)
    (fun K hK => hK) ?_
  · rintro b hb _ ⟨f, hf, rfl⟩
    exact ⟨b * f, mul_mem hb hf, Near.Thm210.map_conj_map_conj L f b⟩
  · intro x hx
    obtain ⟨hxF, hxL⟩ := Subgroup.mem_inf.mp hx
    have hxN : x ∈ F ⊓ N := Subgroup.mem_inf.mpr ⟨hxF, by
      rw [← hΩ.stabilizer L hL]
      exact (Subgroup.mem_inf.mpr ⟨hFA hxF, hxL⟩)⟩
    rw [hFN, Subgroup.mem_bot] at hxN
    rw [hxN]
    exact one_mem _

end IsRegFam

namespace Counterexample

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

theorem thetaOf_line_inf_centralizer (h : Counterexample p A θ) {E F : Subgroup G}
    (hE : E ∈ signalizerFunctorEk p 1 A) (hF : F ≤ A) :
    thetaOf θ E ⊓ Subgroup.centralizer (F : Set G) = thetaOf θ (E ⊔ F) := by
  obtain ⟨a, ha, ha1, rfl⟩ := exists_zpowers_eq_of_mem_signalizerFunctorEk_one h.prime hE
  rw [h.isFunctor.thetaOf_zpowers ha ha1]
  exact h.isFunctor.inf_centralizer_eq_thetaOf ha ha1 hF

theorem nonempty_mulEquiv_of_isRegFam (h : Counterexample p A θ) {B N : Subgroup G}
    {Ω : Set (Subgroup G)} (hBA : B ≤ A) (hB : B ≠ ⊥) (hΩ : IsRegFam A (thetaOf θ B) Ω N)
    {L : Subgroup G} (hL : L ∈ Ω) (hN : N ≤ Subgroup.centralizer (L : Set G)) :
    Nonempty (↥L ≃* ↥(thetaOf θ A)) := by
  obtain ⟨e⟩ := T614.nonempty_mulEquiv_inf_centralizer hΩ.isDirectProduct hΩ.map_conj_mem hL
    (hΩ.transitive L hL) (by rw [hΩ.stabilizer L hL]; exact hN)
  exact ⟨e.symm.trans (MulEquiv.subgroupCongr (h.thetaOf_inf_centralizer hBA hB))⟩

theorem le_centralizer_of_mem_lcal (h : Counterexample p A θ) {B L : Subgroup G} (hBA : B ≤ A)
    (hL : L ∈ lcal (thetaOf θ B)) : B ≤ Subgroup.centralizer (L : Set G) :=
  Subgroup.le_centralizer_iff.mp ((lcal_le hL).trans (h.isFunctor.thetaOf_le_centralizer hBA))

theorem le_bN_of_le
    (h : Counterexample p A θ) {B : Subgroup G} (hBA : B ≤ A) (hB : B ≠ ⊥) :
    B ≤ bN A θ B := by
  obtain ⟨L, hL⟩ := h.lcal_thetaOf_nonempty hBA hB
  rw [h.bN_eq_inf_normalizer hBA hB hL]
  exact le_inf hBA fun x hx =>
    Subgroup.centralizer_le_normalizer _ (h.le_centralizer_of_mem_lcal hBA hL hx)

theorem exists_line_le_of_mem_E2 (h : Counterexample p A θ) {B : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) : ∃ F ∈ signalizerFunctorEk p 1 A, F ≤ B := by
  obtain ⟨⟨b, hbB⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (h.ne_bot_of_mem_E2 hB)
  have hb1' : b ≠ 1 := fun h1 => hb1 (Subtype.ext h1)
  exact ⟨Subgroup.zpowers b, h.zpowers_mem_E1 (hB.1 hbB) hb1', Subgroup.zpowers_le.mpr hbB⟩

theorem exists_line_sup_eq_of_mem_E2 (h : Counterexample p A θ) {B F : Subgroup G}
    (hB : B ∈ signalizerFunctorEk p 2 A) (hF : F ∈ signalizerFunctorEk p 1 A) (hFB : F ≤ B) :
    ∃ F' ∈ signalizerFunctorEk p 1 A, F' ≤ B ∧ F' ≠ F ∧ F ⊔ F' = B := by
  have hnle : ¬ B ≤ F := by
    intro hle
    have h1 := Subgroup.card_le_of_le hle
    rw [hB.2, hF.2, pow_one] at h1
    have : p < p ^ 2 := by nlinarith [h.prime.one_lt]
    omega
  obtain ⟨b, hbB, hbF⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have hb1 : b ≠ 1 := fun h1 => hbF (h1 ▸ one_mem F)
  have hF' : Subgroup.zpowers b ∈ signalizerFunctorEk p 1 A := h.zpowers_mem_E1 (hB.1 hbB) hb1
  have hne : Subgroup.zpowers b ≠ F := fun heq => hbF (heq ▸ Subgroup.mem_zpowers b)
  have hle : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hbB
  have hsup := h.sup_mem_E2_of_ne hF hF' hne.symm
  exact ⟨Subgroup.zpowers b, hF', hle, hne,
    Subgroup.eq_of_le_of_card_ge (sup_le hFB hle) (by rw [hB.2, hsup.2])⟩

end Counterexample

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv
