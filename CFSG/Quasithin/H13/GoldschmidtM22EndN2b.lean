module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Conj
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C5Counting
public import CFSG.Quasithin.H13.GoldschmidtM22EndCtx

public section

namespace CFSG.Quasithin.H13.GM22

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.E3 CFSG.Quasithin CFSG.QuasithinUnique.C5

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G}

section Conj

variable (h : Hyp6Sec2 G T M L V)

include h in
theorem HH_le_normalizer_CHU (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) :
    HH T ≤ Subgroup.normalizer (CHU T L V : Set G) :=
  le_normalizer_centralizerMod (HH_le_normalizer_Z T) Subgroup.le_normalizer
    (HH_le_normalizer_UU T L V)

include h in
theorem CHU_le_normalizer_conj_ZS (hZ : Nat.card (quasithinOmegaOneCenter T) = 2) {g : G}
    (hg : g ∈ HH T) :
    CHU T L V ≤ Subgroup.normalizer ((conjSubgroup (ch6ZS T L V) g : Subgroup G) : Set G) := by
  have key : ∀ c ∈ CHU T L V, ∀ y ∈ conjSubgroup (ch6ZS T L V) g,
      c * y * c⁻¹ ∈ conjSubgroup (ch6ZS T L V) g := by
    intro c hc y hy
    have hyZS : g * y * g⁻¹ ∈ ch6ZS T L V := mem_conjSubgroup_iff.mp hy
    have hyU : y ∈ UU T L V := by
      have h1 : g * y * g⁻¹ ∈ UU T L V := le_conjClosure _ _ hyZS
      have := (Subgroup.mem_normalizer_iff.mp (HH_le_normalizer_UU T L V ((HH T).inv_mem hg))
        (g * y * g⁻¹)).mp h1
      have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rwa [e] at this
    have hcomm := hc.2.2 y hyU
    have hZK : (c * y * c⁻¹ * y⁻¹) ∈ conjSubgroup (ch6ZS T L V) g := by
      rw [mem_conjSubgroup_iff]
      have hZ' : c * y * c⁻¹ * y⁻¹ ∈ quasithinOmegaOneCenter T := hcomm
      have := Z_central T hg hZ'
      have e : g * (c * y * c⁻¹ * y⁻¹) * g⁻¹ = c * y * c⁻¹ * y⁻¹ := by
        rw [this]; group
      rw [e]
      exact Z_le_ZS h hZ hZ'
    have e2 : c * y * c⁻¹ = (c * y * c⁻¹ * y⁻¹) * y := by group
    rw [e2]
    exact (conjSubgroup (ch6ZS T L V) g).mul_mem hZK hy
  intro c hc
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨fun hy => key c hc y hy, fun hy => ?_⟩
  have := key c⁻¹ ((CHU T L V).inv_mem hc) _ hy
  have e : c⁻¹ * (c * y * c⁻¹) * c⁻¹⁻¹ = y := by group
  rwa [e] at this

include h in
theorem CHU_le_normalizer_conj_V (hZ : Nat.card (quasithinOmegaOneCenter T) = 2)
    (h621 : Stmt6_2_1) {g : G} (hg : g ∈ HH T) :
    CHU T L V ≤ Subgroup.normalizer ((conjSubgroup V g : Subgroup G) : Set G) := by
  refine (CHU_le_normalizer_conj_ZS h hZ hg).trans ?_
  rw [← CFSG.QuasithinUnique.C5.conjSubgroup_normalizer,
    ← CFSG.QuasithinUnique.C5.conjSubgroup_normalizer]
  exact CFSG.QuasithinUnique.C5.conjSubgroup_mono (h621 G T M L V h).1 g

end Conj

end CFSG.Quasithin.H13.GM22
