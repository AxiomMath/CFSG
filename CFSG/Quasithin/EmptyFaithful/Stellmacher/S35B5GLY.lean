module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5GLY1
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5GLY2
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem comm_Q_of_not_comm_aux {β : Geo H M} (hS : Sit H M S) (hβ : vtype β = false)
    {Y : Subgroup G} (hVY : Vn β ≤ Y) (hYW : Y ≤ Wb β)
    (hsecβ : IsSec (stab β) (Vn β) (Wb β)) (hYc : (Vn β).relIndex Y ≤ 16)
    (hhom5 : ∀ (F : Type) [Group F] [Finite F], Nat.Coprime 5 (Nat.card F) →
      ∀ φ : ↥(Lr β) →* F, φ = 1)
    (hL : Lr β ≤ Subgroup.normalizer (Y : Set G)) (hnot : ¬ ⁅Y, Lr β⁆ ≤ Vn β) :
    ⁅Y, ⁅Qv β, Lr β⁆⁆ ≤ Vn β := by
  have _ := And.intro hβ hVY
  have hQst : Qv β ≤ stab β := pCoreOf_le 2 _
  have hYst : Y ≤ stab β := hYW.trans ((Wb_le_Qv hS β).trans hQst)
  have hLst : Lr β ≤ stab β := oTwoRes_le _
  have hVst : stab β ≤ Subgroup.normalizer (Vn β : Set G) := Vn_normal β
  have hnorm : ((Vn β).subgroupOf Y).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hVst (hYst g.2)) n.1).mp hn⟩
  have hLN : Lr β ≤ Subgroup.normalizer (Y : Set G) ⊓ Subgroup.normalizer (Vn β : Set G) :=
    le_inf hL (hLst.trans hVst)
  let ρ : ↥(Lr β) →* MulAut (↥Y ⧸ (Vn β).subgroupOf Y) :=
    (GLY.convHom Y (Vn β)).comp (Subgroup.inclusion hLN)
  have hρ : ∀ l : ↥(Lr β), ρ l = 1 ↔ ∀ y ∈ Y, ⁅y, (l : G)⁆ ∈ Vn β :=
    fun l => GLY.convHom_eq_one_iff Y (Vn β) _
  have hA : ∀ a : ↥Y ⧸ (Vn β).subgroupOf Y, a * a = 1 := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      simpa [sq] using hsecβ.sq y (hYW y.2)
  have hcard : Nat.card (↥Y ⧸ (Vn β).subgroupOf Y) ≤ 16 := hYc
  set K : Subgroup G := ⁅Qv β, Lr β⁆ with hKdef
  have hKQ : K ≤ Qv β := by
    refine Subgroup.commutator_le.mpr fun q hq l hl => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 (stab β) (hLst hl)) q⁻¹).mp
      (inv_mem hq)
    have : ⁅q, l⁆ = q * (l * q⁻¹ * l⁻¹) := by simp only [commutatorElement_def]; group
    rw [this]
    exact mul_mem hq h1
  have hKL : K ≤ Lr β := by
    refine Subgroup.commutator_le.mpr fun q hq l hl => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoRes (stab β) (hQst hq)) l).mp hl
    have : ⁅q, l⁆ = (q * l * q⁻¹) * l⁻¹ := by simp only [commutatorElement_def]
    rw [this]
    exact mul_mem h1 (inv_mem hl)
  have hKnorm : (K.subgroupOf (Lr β)).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have h1 : ⁅(g : G), (n : G)⁆ ∈ K := by
      have : ⁅(g : G), (n : G)⁆ ∈ ⁅Lr β, K⁆ := Subgroup.commutator_mem_commutator g.2 hn
      rw [Subgroup.commutator_comm] at this
      exact Subgroup.commutator_mono hKQ le_rfl this
    have : (g * n * g⁻¹ : ↥(Lr β)).1 = ⁅(g : G), (n : G)⁆ * n := by
      simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv]; group
    rw [this]
    exact mul_mem h1 hn⟩
  have hK2 : ∀ k ∈ K.subgroupOf (Lr β), ∃ n : ℕ, k ^ 2 ^ n = 1 := by
    intro k hk
    rw [Subgroup.mem_subgroupOf] at hk
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 (stab β) ⟨k.1, hKQ hk⟩
    exact ⟨n, Subtype.ext (by simpa using congrArg Subtype.val hn)⟩
  by_contra hcon
  have hex : ∃ y ∈ Y, ∃ k ∈ K, ⁅y, k⁆ ∉ Vn β := by
    by_contra h
    push Not at h
    exact hcon (Subgroup.commutator_le.mpr h)
  obtain ⟨y, hy, k, hk, hyk⟩ := hex
  have hne : ρ ⟨k, hKL hk⟩ ≠ 1 := fun h =>
    hyk ((hρ ⟨k, hKL hk⟩).mp h y hy)
  have h1 : ρ = 1 :=
    GLY.acts_trivial hhom5 ρ hA hcard (K.subgroupOf (Lr β)) hKnorm hK2
      ⟨⟨k, hKL hk⟩, by rwa [Subgroup.mem_subgroupOf], hne⟩
  apply hnot
  refine Subgroup.commutator_le.mpr fun y hy l hl => ?_
  exact (hρ ⟨l, hl⟩).mp (by rw [h1]; rfl) y hy

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
