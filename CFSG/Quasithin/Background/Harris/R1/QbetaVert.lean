module

public import CFSG.Quasithin.Recognition.SzR1Vert

public section

namespace CFSG.Quasithin.Background.Harris.R1

open CFSG.Quasithin CFSG.Quasithin.SzR1 CFSG.Quasithin.SzR1.Vert
open scoped commutatorElement

namespace VertT

variable {G : Type*} [Group G] {P S Q W Z M : Subgroup G}

theorem relIndex_conjSub (g : G) {A B : Subgroup G} :
    (conjSub g A).relIndex (conjSub g B) = A.relIndex B := by
  unfold conjSub
  exact Subgroup.relIndex_map_map_of_injective _ _ (MulEquiv.injective _)

theorem inf_conjSub_S (h : Hyp P S Q W Z M) {g y : G} (hg : g ∈ P) (hyg : y ∈ conjSub g S)
    (hyS : y ∉ S) : S ⊓ conjSub g S = Q := by
  have hQg : conjSub g Q = Q := conjSub_eq_of_mem_normalizer (h.qn hg)
  apply le_antisymm
  · intro x hx
    by_contra hxQ
    have h1 : Q ⊔ Subgroup.zpowers x = S :=
      sup_eq_of_relIndex_two h.qs (Subgroup.zpowers_le.mpr hx.1) h.q2
        (fun hle => hxQ (hle (Subgroup.mem_zpowers x)))
    have h2 : conjSub g Q ⊔ Subgroup.zpowers x = conjSub g S :=
      sup_eq_of_relIndex_two (conjSub_mono g h.qs) (Subgroup.zpowers_le.mpr hx.2)
        (by rw [relIndex_conjSub]; exact h.q2)
        (fun hle => hxQ (by rw [hQg] at hle; exact hle (Subgroup.mem_zpowers x)))
    rw [hQg] at h2
    exact hyS (by rw [← h1, h2]; exact hyg)
  · exact le_inf h.qs (hQg ▸ conjSub_mono g h.qs)

theorem sup_conjSub_S (h : Hyp P S Q W Z M) {g y : G} (hg : g ∈ P) (hyg : y ∈ conjSub g S)
    (hyS : y ∉ S) : S ⊔ conjSub g S = P := by
  rcases eq_or_eq_of_relIndex_prime Nat.prime_three h.s3 (H := S ⊔ conjSub g S)
      le_sup_left (sup_le h.sp (conjSub_le_of_mem h.sp hg)) with hh | hh
  · exact absurd (hh.le (Subgroup.mem_sup_right hyg)) hyS
  · exact hh

theorem S_eq (h : Hyp P S Q W Z M) : Q ⊔ W = S := sup_eq_of_relIndex_two h.qs h.ws h.q2 h.wq

variable (h : Hyp P S Q W Z M)
include h

theorem Z_le_W : Z ≤ W := by
  have := h.zw 1 P.one_mem
  rwa [conjSub_one] at this

theorem Z_le_conjSub_W {g : G} (hg : g ∈ P) : Z ≤ conjSub g W :=
  (le_conjSub_iff g).mpr (h.zw g⁻¹ (P.inv_mem hg))

theorem T_le_Q (hMS : M ≤ S) {g y : G} (hg : g ∈ P) (hyg : y ∈ conjSub g S) (hyS : y ∉ S) :
    M ⊓ conjSub g M ≤ Q := by
  rw [← (VertT.inf_conjSub_S h) hg hyg hyS]
  exact le_inf (inf_le_left.trans hMS) (inf_le_right.trans (conjSub_mono g hMS))

theorem Z_le_T {g : G} (hg : g ∈ P) : Z ≤ M ⊓ conjSub g M := by
  refine le_inf ?_ ?_
  · exact (VertT.Z_le_W h).trans h.wm
  · exact ((VertT.Z_le_conjSub_W h) hg).trans (conjSub_mono g h.wm)

theorem Q_le_normalizer_T (hMS : M ≤ S) {g : G} (hg : g ∈ P) :
    Q ≤ Subgroup.normalizer ((M ⊓ conjSub g M : Subgroup G) : Set G) := by
  refine F7.le_normalizer_inf (h.qs.trans h.sm) ?_
  calc Q = conjSub g Q := (conjSub_eq_of_mem_normalizer (h.qn hg)).symm
    _ ≤ conjSub g S := conjSub_mono g h.qs
    _ ≤ Subgroup.normalizer (conjSub g M : Set G) := conjSub_le_normalizer h.sm

theorem W_le_normalizer_T {g : G} (hg : g ∈ P) :
    W ≤ Subgroup.normalizer ((M ⊓ conjSub g M : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro w hw t ht
  obtain ⟨htM, htg⟩ := Subgroup.mem_inf.mp ht
  have hc : ⁅w, t⁆ ∈ Z := by
    have h1 : ⁅t, w⁆ ∈ Z := h.mw (Subgroup.commutator_mem_commutator htM hw)
    have e : ⁅w, t⁆ = ⁅t, w⁆⁻¹ := (commutatorElement_inv t w).symm
    rw [e]
    exact Z.inv_mem h1
  have e : w * t * w⁻¹ = ⁅w, t⁆ * t := by rw [commutatorElement_def]; group
  rw [e]
  exact (M ⊓ conjSub g M).mul_mem ((VertT.Z_le_T h) hg hc) ht

theorem conjSub_W_le_normalizer_T {g : G} (hg : g ∈ P) :
    conjSub g W ≤ Subgroup.normalizer ((M ⊓ conjSub g M : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro w hw t ht
  obtain ⟨htM, htg⟩ := Subgroup.mem_inf.mp ht
  have hc : ⁅w, t⁆ ∈ conjSub g Z := by
    have h1 : ⁅w, t⁆ ∈ conjSub g ⁅W, M⁆ := by
      rw [← conjSub_commutator]
      exact Subgroup.commutator_mem_commutator hw htg
    exact conjSub_mono g (by rw [Subgroup.commutator_comm]; exact h.mw) h1
  have hZ : conjSub g Z ≤ M ⊓ conjSub g M :=
    le_inf ((h.zw g hg).trans h.wm) (conjSub_mono g ((VertT.Z_le_W h).trans h.wm))
  have e : w * t * w⁻¹ = ⁅w, t⁆ * t := by rw [commutatorElement_def]; group
  rw [e]
  exact (M ⊓ conjSub g M).mul_mem (hZ hc) ht

theorem P_le_normalizer_T (hMS : M ≤ S) {g y : G} (hg : g ∈ P) (hyg : y ∈ conjSub g S)
    (hyS : y ∉ S) :
    P ≤ Subgroup.normalizer ((M ⊓ conjSub g M : Subgroup G) : Set G) := by
  have hSN : S ≤ Subgroup.normalizer ((M ⊓ conjSub g M : Subgroup G) : Set G) := by
    rw [← (VertT.S_eq h)]
    exact sup_le ((VertT.Q_le_normalizer_T h) hMS hg) ((VertT.W_le_normalizer_T h) hg)
  have hgS : conjSub g S = Q ⊔ conjSub g W := by
    rw [← (VertT.S_eq h), conjSub_sup, conjSub_eq_of_mem_normalizer (h.qn hg)]
  have hgSN : conjSub g S ≤ Subgroup.normalizer ((M ⊓ conjSub g M : Subgroup G) : Set G) := by
    rw [hgS]
    exact sup_le ((VertT.Q_le_normalizer_T h) hMS hg) ((VertT.conjSub_W_le_normalizer_T h) hg)
  rw [← (VertT.sup_conjSub_S h) hg hyg hyS]
  exact sup_le hSN hgSN

theorem commutator_T_W_le {g : G} : ⁅M ⊓ conjSub g M, W⁆ ≤ Z :=
  (Subgroup.commutator_mono inf_le_left le_rfl).trans h.mw

theorem commutator_T_conjSub_W_le {g : G} : ⁅M ⊓ conjSub g M, conjSub g W⁆ ≤ conjSub g Z := by
  calc ⁅M ⊓ conjSub g M, conjSub g W⁆ ≤ ⁅conjSub g M, conjSub g W⁆ :=
        Subgroup.commutator_mono inf_le_right le_rfl
    _ = conjSub g ⁅M, W⁆ := conjSub_commutator g M W
    _ ≤ conjSub g Z := conjSub_mono g h.mw

theorem commutator_T_V_eq_bot {g : G} (hg : g ∈ P) (hZZ : Z ⊓ conjSub g Z = ⊥) :
    ⁅M ⊓ conjSub g M, Z ⊔ conjSub g Z⁆ = ⊥ := by
  have hZW : Z ⊔ conjSub g Z ≤ W ⊓ conjSub g W :=
    sup_le (le_inf (VertT.Z_le_W h) ((VertT.Z_le_conjSub_W h) hg))
      (le_inf (h.zw g hg) (conjSub_mono g (VertT.Z_le_W h)))
  refine le_antisymm ?_ bot_le
  calc ⁅M ⊓ conjSub g M, Z ⊔ conjSub g Z⁆
      ≤ ⁅M ⊓ conjSub g M, W ⊓ conjSub g W⁆ := Subgroup.commutator_mono le_rfl hZW
    _ ≤ Z ⊓ conjSub g Z := le_inf
        ((Subgroup.commutator_mono le_rfl inf_le_left).trans ((VertT.commutator_T_W_le h)))
        ((Subgroup.commutator_mono le_rfl inf_le_right).trans ((VertT.commutator_T_conjSub_W_le h)))
    _ = ⊥ := hZZ

end VertT

end CFSG.Quasithin.Background.Harris.R1
