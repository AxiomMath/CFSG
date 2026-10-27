module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P62A
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Geo
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec8P1Lab

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem ballStab_conj (F : FanTree Γ G) (g : G) {n : ℕ} {a : V} {h : G}
    (hh : h ∈ ballStab Γ G n a) : g * h * g⁻¹ ∈ ballStab Γ G n (g • a) := by
  refine mem_ballStab.2 fun w hw => ?_
  have hd : Γ.dist a (g⁻¹ • w) ≤ n := by
    have := dist_smul F g⁻¹ (g • a) w
    rw [inv_smul_smul] at this
    rw [this]
    exact hw
  have h1 := mem_ballStab.1 hh _ hd
  calc (g * h * g⁻¹) • w = g • (h • (g⁻¹ • w)) := by simp [mul_smul]
    _ = w := by rw [h1]; simp

theorem ballStab_conj_stab (F : FanTree Γ G) {g : G} {a : V} (hg : g • a = a) {n : ℕ} {h : G}
    (hh : h ∈ ballStab Γ G n a) : g * h * g⁻¹ ∈ ballStab Γ G n a := by
  have := ballStab_conj F g hh
  rwa [hg] at this

variable {F : FanTree Γ G} {L : ZLab Γ G}

theorem zGroup_conj (F : FanTree Γ G) (L : ZLab Γ G) {α : V} {g : G} (hg : g • α = α)
    {v : G} (hv : v ∈ L.zGroup 2 α) : g * v * g⁻¹ ∈ L.zGroup 2 α := by
  have hmem : L.zGroup 2 α ≤ (L.zGroup 2 α).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).2 ?_
    rintro _ ⟨δ, hd, h5, rfl⟩
    refine Subgroup.subset_closure ⟨g • δ, ?_, ?_, ?_⟩
    · have := dist_smul F g α δ
      rw [hg] at this
      rw [this]
      exact hd
    · rw [valence_smul F]; exact h5
    · exact (L.equivariant g δ h5).symm
  exact hmem hv

theorem zGroup_eq_closure_zBall (F : FanTree Γ G) (L : ZLab Γ G) {α : V}
    (hα : valence Γ α = 5) :
    L.zGroup 2 α = Subgroup.closure (zBall Γ α (L.z α) 2) := by
  have hset : L.zSet 2 α = zBall Γ α (L.z α) 2 := by
    ext w
    constructor
    · rintro ⟨δ, hd, h5, rfl⟩
      obtain ⟨g, hg⟩ := P62.exists_smul_of_valence_eq F (u := α) (w := δ) (by rw [h5, hα])
      refine ⟨g, ?_, ?_⟩
      · rw [hg]; exact hd
      · rw [← L.equivariant g α hα, hg]
    · rintro ⟨g, hd, rfl⟩
      refine ⟨g • α, hd, ?_, (L.equivariant g α hα).symm⟩
      rw [valence_smul F]; exact hα
  unfold ZLab.zGroup
  rw [hset]

end P74

end CFSG.Quasithin.Fan86
