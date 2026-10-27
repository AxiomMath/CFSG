module

public import CFSG.Quasithin.H13.NQS134EG
public import CFSG.Quasithin.H13.NQS134EF

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem card_le_two_mul_inf {D X : Subgroup G}
    (h : ∀ d ∈ D, ∀ d' ∈ D, d ∉ X → d' ∉ X → d * d' ∈ X) :
    Nat.card D ≤ 2 * Nat.card ↥(D ⊓ X) := by
  classical
  by_cases hDX : ∃ d₀ ∈ D, d₀ ∉ X
  · obtain ⟨d₀, hd₀D, hd₀X⟩ := hDX
    let F : ↥D → ↥(D ⊓ X) ⊕ ↥(D ⊓ X) := fun d =>
      if hd : (d : G) ∈ X then Sum.inl ⟨d, mem_inf.2 ⟨d.2, hd⟩⟩
      else Sum.inr ⟨d₀ * d, mem_inf.2 ⟨mul_mem hd₀D d.2, h _ hd₀D _ d.2 hd₀X hd⟩⟩
    have hF : Function.Injective F := by
      intro a b hab
      by_cases ha : (a : G) ∈ X <;> by_cases hb : (b : G) ∈ X <;>
        simp only [F, ha, hb, dite_true, dite_false, Sum.inl.injEq, Sum.inr.injEq,
          reduceCtorEq] at hab
      · exact Subtype.ext (congrArg (fun x : ↥(D ⊓ X) => (x : G)) hab)
      · exact Subtype.ext (mul_left_cancel (congrArg (fun x : ↥(D ⊓ X) => (x : G)) hab))
    have h1 := Nat.card_le_card_of_injective F hF
    rw [Nat.card_sum] at h1
    omega
  · push Not at hDX
    have hle : D ≤ D ⊓ X := fun d hd => mem_inf.2 ⟨hd, hDX d hd⟩
    have := card_le_of_le hle
    omega

namespace End134

variable (S : A6.Setting134 G T L V)
include S

variable {z : G} (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G))
  (huniq : ∀ z' ∈ quasithinOmegaOneCenter T, z' ≠ 1 →
    ¬ centralizer ({z'} : Set G) ≤ normalizer (L : Set G) → z' = z)
include hz hzL huniq

theorem false_of_all_comm (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (hA : ∀ g : G, conjSub g V ≤ T → conjSub g V ≤ centralizer (V : Set G))
    {P U : Subgroup G} {w₀ : G} (hTP : T ≤ P) (hPM : ¬ P ≤ normalizer (L : Set G))
    (hPU : P ≤ normalizer (U : Set G)) (hPCT : P ⊓ centralizer (U : Set G) ≤ T)
    (hw₀ : w₀ ∈ V) (hw₀1 : w₀ ≠ 1)
    (hw₀w : wtP (S.frame.ψ ⟨w₀, hw₀⟩ : P6) ≠ wtP (S.frame.ψ ⟨z, hz.1⟩ : P6))
    (hF1 : ∀ u ∈ U, ∀ t ∈ T, u * t * u⁻¹ * t⁻¹ = 1 ∨ u * t * u⁻¹ * t⁻¹ = w₀)
    (hF2 : ∀ t ∈ T, ∀ t' ∈ T, t ∉ centralizer (U : Set G) → t' ∉ centralizer (U : Set G) →
      t * t' ∈ centralizer (U : Set G))
    (hKEY : V ≤ centralizer (U : Set G)) : False := by
  set Y := P ⊓ centralizer (U : Set G) with hYdef
  have hYP : Y ≤ P := inf_le_left
  have hY2 : IsPGroup 2 Y := S.h13.sylow.1.to_le hPCT
  have hPY : P ≤ normalizer (Y : Set G) :=
    le_normalizer_inf le_normalizer (hPU.trans (F7.normalizer_le_normalizer_centralizer U))
  obtain ⟨g, hgT, hgY⟩ := exists_conj_not_le S hA hTP hPM hYP hY2 hPY
  set D := conjSub g V with hDdef
  have hDC : ¬ D ≤ centralizer (U : Set G) := fun h =>
    hgY (le_inf (hgT.trans hTP) h)
  have hD16 : 4 < Nat.card ↥(D ⊓ centralizer (U : Set G)) := by
    have h1 := card_le_two_mul_inf (D := D) (X := centralizer (U : Set G))
      fun d hd d' hd' hdX hd'X => hF2 d (hgT hd) d' (hgT hd') hdX hd'X
    rw [card_conj S g] at h1
    omega
  have hUN : U ≤ normalizer (D : Set G) := by
    refine le_trans ?_ (centralizer_le_normalizer_conj S hz hzL huniq h1222
      (inf_le_left : D ⊓ centralizer (U : Set G) ≤ D) hD16)
    intro u hu
    rw [mem_centralizer_iff]
    intro x hx
    exact (mem_centralizer_iff.1 (mem_inf.1 hx).2 u hu).symm
  obtain ⟨d, hdD, hdC⟩ := IsConcreteLE.not_le_iff_exists.1 hDC
  have hex : ∃ u ∈ U, u * d * u⁻¹ * d⁻¹ ≠ 1 := by
    by_contra hcon
    push Not at hcon
    apply hdC
    rw [mem_centralizer_iff]
    intro u hu
    have h1 := hcon u hu
    calc u * d = u * d * u⁻¹ * d⁻¹ * (d * u) := by group
      _ = d * u := by rw [h1, one_mul]
  obtain ⟨u, hu, hc⟩ := hex
  have hcD : u * d * u⁻¹ * d⁻¹ ∈ D :=
    mul_mem ((mem_normalizer_iff.mp (hUN hu) d).mp hdD) (inv_mem hdD)
  have hcw : u * d * u⁻¹ * d⁻¹ = w₀ := (hF1 u hu d (hgT hdD)).resolve_left hc
  rw [hcw] at hcD
  have hDV : D = V := eq_of_mem_conj S hz hzL huniq h331 h1222 hw₀ hw₀1 hw₀w hcD
  exact hdC (hKEY (hDV ▸ hdD))

end End134

end CFSG.Quasithin.H13.NQS134
