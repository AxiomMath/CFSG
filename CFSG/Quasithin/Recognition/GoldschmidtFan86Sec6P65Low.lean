module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P65Sur
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6P64Gen
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec6Stmt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P52S

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace P65

section ZBall

variable (F : FanTree Γ G)
include F

theorem conj_mem_zBall {α : V} {z g : G} (hg : g ∈ MulAction.stabilizer G α) :
    ∀ s ∈ zBall Γ α z 2, g * s * g⁻¹ ∈ zBall Γ α z 2 := by
  rintro _ ⟨h, hd, rfl⟩
  refine ⟨g * h, ?_, by group⟩
  have := dist_smul F g α (h • α)
  rw [MulAction.mem_stabilizer_iff.1 hg] at this
  rw [mul_smul, this]
  exact hd

theorem normal_closure_zBall {α : V} {z : G}
    (hW : Subgroup.closure (zBall Γ α z 2) ≤ MulAction.stabilizer G α) :
    ((Subgroup.closure (zBall Γ α z 2)).subgroupOf (MulAction.stabilizer G α)).Normal := by
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hW]
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro w
  refine ⟨fun hw => P64.conj_mem_closure (conj_mem_zBall F hg) w hw, fun hw => ?_⟩
  have := P64.conj_mem_closure (conj_mem_zBall F ((MulAction.stabilizer G α).inv_mem hg)) _ hw
  simpa [mul_assoc] using this

theorem closure_zBall_le_nbrStab (h63 : Fan63 F) (h40 : Fan40 F) {α β : V} {z : G}
    (hz : z ∈ Cinv G α) (hαβ : Γ.Adj α β) :
    Subgroup.closure (zBall Γ α z 2) ≤ nbrStab Γ G β := by
  rw [Subgroup.closure_le]
  rintro _ ⟨g, hd, rfl⟩
  refine mem_nbrStab.2 fun u hu => ?_
  refine mem_ballStab.1 (h63 h40 α z hz g) u ?_
  have h1 := F.isTree.connected.dist_triangle (u := g • α) (v := α) (w := u)
  have h2 := F.isTree.connected.dist_triangle (u := α) (v := β) (w := u)
  have h3 : Γ.dist (g • α) α = Γ.dist α (g • α) := SimpleGraph.dist_comm
  have h4 : Γ.dist α β = 1 := dist_eq_one_iff_adj.2 hαβ
  have h5 : Γ.dist β u = 1 := dist_eq_one_iff_adj.2 hu
  omega

end ZBall

theorem false_of_cover (F : FanTree Γ G) (h33 : Fan33 F) {α β : V} (hv5 : valence Γ α = 5)
    (hαβ : Γ.Adj α β) {x : G} (hx : x ∈ MulAction.stabilizer G α) (hxo : orderOf x = 5)
    {W : Subgroup G} (hWα : W ≤ MulAction.stabilizer G α)
    (hWn : (W.subgroupOf (MulAction.stabilizer G α)).Normal) (hWβ : W ≤ nbrStab Γ G β)
    (hxW : ∀ w ∈ W, x * w * x⁻¹ ∈ W)
    (hcov : ∀ g ∈ nbrStab Γ G α,
      ∃ w ∈ W, ∃ c ∈ Subgroup.centralizer ({x} : Set G) ⊓ nbrStab Γ G α, g = w * c) : False := by
  have hii : Fan33ii Γ α β x := by
    refine ⟨W, hWα, hWn, hWβ, fun g hg => ?_⟩
    obtain ⟨w, hw, c, ⟨hc, -⟩, rfl⟩ := hcov g hg
    have hxc : x * c = c * x := Subgroup.mem_centralizer_iff.1 hc x rfl
    have e1 : x * c * x⁻¹ = c := by rw [hxc]; group
    have e : x * (w * c) * x⁻¹ * (w * c)⁻¹ = (x * w * x⁻¹) * w⁻¹ := by
      calc x * (w * c) * x⁻¹ * (w * c)⁻¹ = (x * w * x⁻¹) * (x * c * x⁻¹) * c⁻¹ * w⁻¹ := by group
        _ = (x * w * x⁻¹) * w⁻¹ := by rw [e1]; group
    rw [e]
    exact W.mul_mem (hxW w hw) (W.inv_mem hw)
  exact F.not_pclosed α ((h33 α β hαβ x hx (by rw [hxo, hv5])).2.1.1 hii)

theorem index_ge (F : FanTree Γ G) (h40 : Fan40 F) (h33 : Fan33 F) (h63 : Fan63 F)
    (h64 : Fan64 F) (h517a : Fan517a F) {α : V} (hv5 : valence Γ α = 5) {z : G}
    (hz : z ∈ Cinv G α) {x : G} (hx : x ∈ MulAction.stabilizer G α) (hxo : orderOf x = 5) :
    256 ≤ (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G α) := by
  obtain ⟨-, -, hW⟩ := h64 h40 α z hz
  have hW16 := hW x hx (by rw [hxo, hv5])
  have hWK : Subgroup.closure (zBall Γ α z 2) ≤ nbrStab Γ G α :=
    (h517a h40 α z (by omega) hz).1
  have hWα : Subgroup.closure (zBall Γ α z 2) ≤ MulAction.stabilizer G α :=
    hWK.trans (F.nbrStab_le_stabilizer α)
  have hxS : x • α = α := MulAction.mem_stabilizer_iff.1 hx
  have hKfin : Finite (nbrStab Γ G α) := F.finite_nbrStab α
  have hK2 : IsPGroup 2 (nbrStab Γ G α) := F.nbrStab_isPGroup α
  have hxK : ∀ k ∈ nbrStab Γ G α, x * k * x⁻¹ ∈ nbrStab Γ G α := fun k hk =>
    nbrStab_conj_mem F hxS hk
  have h16 : 16 ≤ (Subgroup.centralizer ({x} : Set G)).relIndex (nbrStab Γ G α) := by
    have := Subgroup.relIndex_le_of_le_right hWK (FanTree.relIndex_ne_zero_of_finite
      (Subgroup.centralizer ({x} : Set G)) (nbrStab Γ G α))
    rw [hW16] at this
    simpa using this
  refine relIndex_centralizer_ge_256 _ hK2 hxo hxK h16 fun heq => ?_
  obtain ⟨β, hαβ⟩ := F.exists_adj α
  have hcov := exists_mul_of_relIndex_eq (nbrStab Γ G α) (Subgroup.closure (zBall Γ α z 2))
    (Subgroup.centralizer ({x} : Set G)) hWK (by rw [heq, hW16]; norm_num)
  refine false_of_cover F h33 hv5 hαβ hx hxo hWα (normal_closure_zBall F hWα)
    (closure_zBall_le_nbrStab F h63 h40 hz hαβ) ?_ hcov
  exact P64.conj_mem_closure fun s hs => conj_mem_zBall F hx s hs

end P65

end CFSG.Quasithin.Fan86
