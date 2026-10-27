module

public import CFSG.Quasithin.MS93.S512TPair
public import CFSG.Quasithin.MS93.S5B512

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible

namespace S512T

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}
  {k : ℕ} {F : Type} [Field F] [Fintype F] {a : ↥M →* ↥(StatedSp 2 F)}

omit [Fintype F] in
theorem chain_geo (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4) {q : ℕ}
    {α' ν μ₁ μ₂ : Vtx (puAmalgam h.le)} (hch : S5B.IsChain512 h q a α' ν μ₁ μ₂) :
    IsCritical _ (baseA (puAmalgam h.le)) α' ∧ geo _ (baseA (puAmalgam h.le)) α' 1 = baseB _ ∧
      IsCritical _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) ∧
      (∃ y ∈ stab _ (baseA (puAmalgam h.le)), μ₁ = y • geo _ (baseA (puAmalgam h.le)) α' 2) ∧
      (puAmalgam h.le).treeGraph.dist (baseA _) μ₁ = 2 ∧
      geo _ μ₁ (geo _ (baseA (puAmalgam h.le)) α' 2) 2 = baseA _ ∧
      (puAmalgam h.le).treeGraph.Adj (baseB _) (geo _ (baseA (puAmalgam h.le)) α' 2) := by
  obtain ⟨hαβ, -, -, hc, hμ, hcμ, -⟩ := hch
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb4
  have hlamAt : μ₁ ∈ S5B.lamAt h q a (baseA _) α' (geo _ (baseA (puAmalgam h.le)) α' 2) :=
    ⟨1, one_smul _ _, by rw [one_smul, hαβ], by simpa using hμ⟩
  have hstep : S5B.IsLamStep h q a (baseA _) α' μ₁ := ⟨hc, hlamAt, hcμ⟩
  obtain ⟨hdμ, hgeo⟩ := S5B.lamStep_geo h hb4 hstep
  refine ⟨hc, hαβ, hcμ, S5B.exists_mem_stab_of_mem_lam hμ, hdμ, hgeo, ?_⟩
  have := adj_geo _ (u := baseA (puAmalgam h.le)) (w := α') (i := 1) (by omega)
  rwa [hαβ] at this

theorem eq_geo_one_of_adj (h : PUHyp M T L) (hb4 : critDist (puAmalgam h.le) = 4)
    {μ γ α ρ : Vtx (puAmalgam h.le)} (hc : IsCritical _ μ γ) (hmid : geo _ μ γ 2 = α)
    (hαρ : (puAmalgam h.le).treeGraph.Adj α ρ) (hρμ : (puAmalgam h.le).treeGraph.Adj ρ μ) :
    ρ = geo _ μ γ 1 := by
  obtain ⟨-, -, -, hd, -, -, -, -, -, hαγ, -, -⟩ := pair_facts h hb4 hc
  rw [hmid] at hαγ
  have h1 := dist_triangle _ ρ α γ
  have h2 := dist_triangle _ μ ρ γ
  rw [dist_eq_one_of_adj _ hαρ.symm] at h1
  rw [dist_eq_one_of_adj _ hρμ.symm] at h2
  exact eq_geo_one _ hρμ.symm (by omega)

theorem zHat_eq (h : PUHyp M T L) (hd : S5.IsSp4Data M T L k F a)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA (puAmalgam h.le)) α')
    (hq : (Qv _ α').relIndex (ZM _ (baseA (puAmalgam h.le))) = 2 ^ k) :
    S5.zHat _ (baseA (puAmalgam h.le)) α' = ZM _ α' := by
  rcases S33.shape_of_sp4Data h hd hc with ⟨-, hZ, -⟩ | ⟨h1, -, -⟩
  · exact hZ
  · exfalso
    rw [hq] at h1
    have hk : 1 < 2 ^ k := Nat.one_lt_two_pow (by have := hd.1; omega)
    have : 2 ^ k < (2 ^ k) ^ 2 := by nlinarith
    omega

end S512T

end CFSG.Quasithin.MS93
