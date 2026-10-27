module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB13
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResB12

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem frame_mem_P_iff (h : ConfR δ μ U) (fr : OrthFrame δ μ) (k : ↥(stab δ)) :
    (k : G) ∈ Qv μ ↔ fr.Ψ k ∈ S5That := by
  constructor
  · intro hk
    rw [← fr.mapP]
    exact ⟨k, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
  · intro hk
    rw [← fr.mapP] at hk
    obtain ⟨k', hk', hkk⟩ := hk
    have h1 : fr.Ψ (k'⁻¹ * k) = 1 := by rw [map_mul, map_inv, hkk, inv_mul_cancel]
    have h2 : ((k'⁻¹ * k : ↥(stab δ)) : G) ∈ Qv δ := (fr.ker _).mp h1
    have h3 : (k : G) = (k' : G) * ((k'⁻¹ * k : ↥(stab δ)) : G) := by simp
    rw [h3]
    exact (Qv μ).mul_mem (Subgroup.mem_subgroupOf.mp hk') (h.hQδ h2)

theorem img_conj (fr : OrthFrame δ μ) (k : ↥(stab δ)) (X : Subgroup G) :
    fr.img (conjSub (k : G) X) = (fr.img X).map (MulAut.conj (fr.Ψ k)).toMonoidHom := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hx' : ((k : G))⁻¹ * (x : G) * (k : G) ∈ X := mem_conjSub.mp (Subgroup.mem_subgroupOf.mp hx)
    refine ⟨fr.Ψ (k⁻¹ * x * k), ⟨k⁻¹ * x * k, Subgroup.mem_subgroupOf.mpr ?_, rfl⟩, ?_⟩
    · simpa using hx'
    · show fr.Ψ k * fr.Ψ (k⁻¹ * x * k) * (fr.Ψ k)⁻¹ = fr.Ψ x
      simp only [map_mul, map_inv]; group
  · rintro ⟨_, ⟨x, hx, rfl⟩, rfl⟩
    refine ⟨k * x * k⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by
      show fr.Ψ (k * x * k⁻¹) = fr.Ψ k * fr.Ψ x * (fr.Ψ k)⁻¹
      simp only [map_mul, map_inv]⟩
    have := mul_mem_conjSub (g := (k : G)) (Subgroup.mem_subgroupOf.mp hx)
    simpa using this

theorem inf_Qv_ne (hA : F53Amalgam H M S) (h : ConfR δ μ U) {u w : Geo H M}
    (hu : u ∈ nbrs μ) (hw : w ∈ nbrs μ) (huδ : u ≠ δ) (hwδ : w ≠ δ) (huw : u ≠ w)
    (hall : ∀ x ∈ nbrs μ, x = δ ∨ x = u ∨ x = w) (h2 : aZ δ u = 2) :
    OoOf δ ⊓ Qv u ≠ OoOf δ ⊓ Qv w := by
  obtain ⟨fr⟩ := h.exists_frame hA
  have hδ : δ ∈ nbrs μ := h.sig.adj.symm
  have haw : aZ δ w = 2 := (h.aZ_unif hA hδ hw hδ hu (Ne.symm hwδ) (Ne.symm huδ)).trans h2
  have hcard : ∀ {j : Geo H M}, j ∈ nbrs μ → j ≠ δ → aZ δ j = Nat.card (fr.img (OoOf j)) := by
    intro j hj hjδ
    rw [card_img fr (h.Oo_le_stab_at hA hj), inf_comm, ← h.relIndex_Oo_eq hA hj hjδ,
      ← h.relIndex_Zv_eq_Oo hA hj hjδ]
    rfl
  have hsmall : ∀ {j : Geo H M}, j ∈ nbrs μ → j ≠ δ → aZ δ j = 2 →
      fr.img (OoOf j) = Subgroup.zpowers (swap 0 2) ∨ fr.img (OoOf j) = Subgroup.zpowers (swap 1 3) := by
    intro j hj hjδ hj2
    rcases h.classify hA fr hj hjδ with e | e | e
    · exact Or.inl e
    · exact Or.inr e
    · exfalso
      have := hcard hj hjδ
      rw [hj2, e, O2.card_S5That] at this
      omega
  obtain ⟨s, hsδ, hsμ, hsu⟩ := h.exists_swap_here hA hu hw huδ hwδ huw hall
  have hsP : (s : G) ∉ Qv μ := fun hmem => huw (by
    have := smul_eq_of_mem_stab (g := s) (Qv_le_stab_of_mem_nbrs hA hu hmem)
    rw [hsu] at this; exact this.symm)
  have hO : OoOf w = conjSub (s : G) (OoOf u) := by rw [← hsu, OoOf_smul]
  have hΨs : fr.Ψ ⟨s, hsδ⟩ ∈ S5Syl := by
    rw [← fr.syl]
    exact ⟨⟨s, hsδ⟩, Subgroup.mem_subgroupOf.mpr ⟨hsδ, hsμ⟩, rfl⟩
  have hΨs' : fr.Ψ ⟨s, hsδ⟩ ∉ S5That := fun hh => hsP ((h.frame_mem_P_iff fr ⟨s, hsδ⟩).mpr hh)
  have hBw : fr.img (OoOf w) = (fr.img (OoOf u)).map (MulAut.conj (fr.Ψ ⟨s, hsδ⟩)).toMonoidHom := by
    rw [hO]; exact img_conj fr ⟨s, hsδ⟩ _
  obtain ⟨hc1, hc2⟩ := conj_zpowers_swap hΨs hΨs'
  intro heq
  rw [h.Oo_inf_Qv_eq_map hA fr hu, h.Oo_inf_Qv_eq_map hA fr hw] at heq
  have hfix := Subgroup.map_injective fr.inj heq
  rcases hsmall hu huδ h2 with e | e
  · have e2 : fr.img (OoOf w) = Subgroup.zpowers (swap 1 3) := by rw [hBw, e, hc1]
    rw [e, e2] at hfix
    exact fixW_swap_ne hfix
  · have e2 : fr.img (OoOf w) = Subgroup.zpowers (swap 0 2) := by rw [hBw, e, hc2]
    rw [e, e2] at hfix
    exact fixW_swap_ne hfix.symm

end ConfR

end CFSG.Quasithin.F53
