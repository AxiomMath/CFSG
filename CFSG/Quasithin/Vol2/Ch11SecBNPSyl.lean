module

public import CFSG.Quasithin.Background.E1Param

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Quasithin.A1b

theorem nParam_le_one_of_normal_sylow {G : Type} [Group G] [Finite G] {Y S : Subgroup G}
    (hS2 : IsPGroup 2 S) (hSY : S ≤ Y) (hSn : (S.subgroupOf Y).Normal)
    (hS : ∀ A : Subgroup G, A ≤ Y → IsPGroup 2 A → A ≤ S) : E1.nParam Y ≤ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have key : E1.InE 1 Y := by
    intro T hT Ω hΩ
    refine le_antisymm (sup_le (E1.eGen_le 1 Y T Ω) inf_le_left) ?_
    refine le_sup_of_le_right (le_inf le_rfl ?_)
    have hST : S ≤ T := hT.le_of_normal hSY hSn hS2
    have hpg : ∀ A ∈ Ω, IsPGroup 2 A := fun A hA x => ⟨1, by
      apply Subtype.ext
      simpa using (hΩ.isElemAbelian A hA).2 x x.2⟩
    have hall : ∀ A ∈ Ω, A ≤ T := fun A hA => (hS A (hΩ.le A hA) (hpg A hA)).trans hST
    have hconj : ∀ z ∈ Y, ∀ w ∈ E1.weakClosure T Ω, z * w * z⁻¹ ∈ E1.weakClosure T Ω := by
      intro z hz w hw
      have hle : E1.weakClosure T Ω ≤
          (E1.weakClosure T Ω).comap (MulAut.conj z).toMonoidHom := by
        refine iSup₂_le fun A hA => iSup_le fun _ => ?_
        intro a ha
        have h1 : z * a * z⁻¹ ∈ conjSub z A := mem_conjSub_of_mem ha
        have h2 : conjSub z A ∈ Ω := hΩ.conj A hA z hz
        have h3 : conjSub z A ≤ E1.weakClosure T Ω := by
          unfold E1.weakClosure
          exact le_iSup₂_of_le (conjSub z A) h2 (le_iSup_of_le (hall _ h2) le_rfl)
        exact h3 h1
      exact hle hw
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨fun hw => hconj y hy w hw, fun hw => ?_⟩
    have := hconj y⁻¹ (Y.inv_mem hy) _ hw
    simpa [mul_assoc] using this
  have := (E1.nParam_le_iff (H := Y) (n := 1) Nat.one_pos).mpr key
  simpa using this

end CFSG.Quasithin.Vol2.Ch11.SecB
