module

public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGFixedRealizedConfig
public import CFSG.LocalAnalysis.StandardType.GGRealQFourThree
public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggResI_reflConjSimple {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {Bs L : Subgroup G} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (hWL : GGIsWeylMatrix ML)
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V}
    {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hind : LinearIndependent (ZMod p) fun i : Λ => h (some i))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i))) :
    GGReflConjSimple p (ggAutomizer L Bs) fun i : Λ => φ (some i) := by
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hFT : TauCeti.IsFiniteType CL := isFiniteType_of_ggIsWeylMatrixFixed hWL hCL
  have hRC := ggReflClosed_of_indep hp2 hFT hCL (fun i : Λ => h (some i))
    (fun i : Λ => α (some i)) hL hind (fun i => ggLin (p := p) ι (φ (some i)))
    (fun i => hφ (some i))
  have hmap : (Subgroup.closure (Set.range fun i : Λ => φ (some i))).map (ggLin (p := p) ι) =
      Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ (some i))) := by
    rw [MonoidHom.map_closure, ← Set.range_comp]; rfl
  intro t ht hrefl
  obtain ⟨xv, f, -, hxf⟩ := exists_of_ggIsReflection ι hrefl
  have hr := (ggIsReflection_iff (p := p) ι t).mp hrefl
  have ht1 : ggLin (p := p) ι t ≠ 1 := by
    intro h1
    have hc := hr.2
    rw [h1] at hc
    have he : Nat.card {v : V // (1 : V ≃ₗ[ZMod p] V) v = v} = Nat.card V :=
      Nat.card_congr (Equiv.subtypeUnivEquiv fun v => rfl)
    rw [he] at hc
    have hpos : 0 < Nat.card V := Nat.card_pos
    have : p = 1 := Nat.eq_of_mul_eq_mul_left hpos (by rw [mul_one]; exact hc)
    exact (Fact.out : p.Prime).one_lt.ne' this
  have htW : ggLin (p := p) ι t ∈
      Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ (some i))) := by
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ (hAL ▸ ht)
  obtain ⟨u, hu, i, hui⟩ := hRC _ htW hr.1 ht1 ⟨xv, f, hxf⟩
  rw [← hmap] at hu
  obtain ⟨w, hw, rfl⟩ := hu
  refine ⟨w, hAL ▸ hw, i, ggLin_injective (p := p) ι ?_⟩
  rw [hui, map_mul, map_mul, map_inv]

theorem ggResI_qFour_L {G : Type} [Group G] [Finite G] {p : ℕ} {Bs L : Subgroup G}
    (hInn : GGInnerDiagOn Bs L) (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L) :
    GGInnerDiagOnLabel GGLabQFour p Bs L := by
  rcases (hInn.label GGLabQFour p).elim_or with hq4 | hq2
  · exact hq4
  · exact absurd (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨not_le.mp hP.1, hP.2⟩) hq2) hq

theorem ggResI_mem_of_q8 (hLB : GGLBalanceInput) (hSP : GGStdSubPrimeInput)
    (hReal : GGReflRealizedQFourInputThree) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hp3 : p = 3) (hq : ¬ GGInnerDiagOnLabel GGLabQTwo p Bs L)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hWL : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) {φ : Option Λ → MulAut ↥Bs} {h : Option Λ → V}
    {α : Option Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection p (φ o))
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod p))
    (hind : LinearIndependent (ZMod p) fun i : Λ => h (some i))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hxBs : x ∈ Bs) {R : List (V ≃ₗ[ZMod p] V)}
    (hRgen : ∀ k : Λ, ggLin (p := p) ι (φ (some k)) ∈ R)
    (hRconj : ∀ k : Λ, ∀ r ∈ R,
      ggLin (p := p) ι (φ (some k)) * r * (ggLin (p := p) ι (φ (some k)))⁻¹ ∈ R)
    {ψ : V ≃ₗ[ZMod p] V}
    (hψ : ψ ∈ Subgroup.closure (Set.range fun o => ggLin (p := p) ι (φ o))) {i : Λ}
    (hfix : α (some i) (ψ⁻¹ (ι (Additive.ofMul ⟨x, hxBs⟩))) = 0) :
    ψ * ggLin (p := p) ι (φ (some i)) * ψ⁻¹ ∈ R := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hA := ggResI_sup_eq_closure hAL hAK
  rw [← ggResI_map_sup ι hA] at hψ
  obtain ⟨ψ₀, hψ₀, rfl⟩ := Subgroup.mem_map.mp hψ
  have hψ₀top : ψ₀ ∈ ggAutomizer ⊤ Bs := Subgroup.subset_closure (ggResI_mem_ggInduced_top hψ₀)
  have hRL : GGReflRealizedIn p Bs L := hReal G p B Bs x L D J hH.1 hH.2.2.1 hH.2.2.2.1 hp3 L
    (Or.inl rfl) (ggResI_qFour_L hH.2.2.1.1 hq)
  have hri : φ (some i) ∈ ggAutomizer L Bs := by
    rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩
  have hrR : GGRealized p Bs (φ (some i)) :=
    ggRealized_of_reflRealizedIn_L hSP hH.1 hRL hri (hrefl (some i))
  have h847 : GGFixedRealizedInL p Bs L x := ggFixedRealizedInL_of_config hLB hSP hH.1 hH.2.2.1.1
  have hW := ggResI_reflConjSimple hp2 hWL hCL ι hφ hL hind hAL
  have hx : x ∈ ggFixG Bs (ψ₀ * φ (some i) * ψ₀⁻¹) := by
    refine ⟨⟨x, hxBs⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, mem_ggFix, ggLin_fix_iff (p := p) ι, map_mul, map_mul, map_inv,
      LinearEquiv.mul_apply, LinearEquiv.mul_apply, hφ, hfix, zero_smul, sub_zero,
      LinearEquiv.coe_inv, LinearEquiv.apply_symm_apply]
  have hinv : ∀ k : Λ, (ggLin (p := p) ι (φ (some k)))⁻¹ = ggLin (p := p) ι (φ (some k)) := by
    intro k
    rw [inv_eq_iff_mul_eq_one]
    refine LinearEquiv.ext fun w => ?_
    change ggLin (p := p) ι (φ (some k)) (ggLin (p := p) ι (φ (some k)) w) = w
    have h2 : α (some k) (h (some k)) = 2 := by rw [hL, hCL.1 k]; norm_num
    rw [hφ, hφ, map_sub, map_smul, h2, smul_eq_mul]
    module
  have hcl : ∀ w ∈ Subgroup.closure (Set.range fun k : Λ => ggLin (p := p) ι (φ (some k))),
      ∀ r ∈ R, w * r * w⁻¹ ∈ R := by
    intro w hw
    induction hw using Subgroup.closure_induction_left with
    | one => intro r hr; simpa using hr
    | mul_left s hs w _ ih =>
      obtain ⟨k, rfl⟩ := hs
      intro r hr
      have := hRconj k _ (ih r hr)
      simpa [mul_assoc] using this
    | inv_mul_cancel s hs w _ ih =>
      obtain ⟨k, rfl⟩ := hs
      intro r hr
      have := hRconj k _ (ih r hr)
      rw [hinv k] at this ⊢
      simpa [mul_assoc, hinv k] using this
  by_contra hnot
  refine ggCell_false_of_witness hp h847 hW hψ₀top (hrefl (some i)) hrR hx fun w hw k he => ?_
  apply hnot
  have hwL : ggLin (p := p) ι w ∈
      Subgroup.closure (Set.range fun k : Λ => ggLin (p := p) ι (φ (some k))) := by
    have hmap : (Subgroup.closure (Set.range fun i : Λ => φ (some i))).map (ggLin (p := p) ι) =
        Subgroup.closure (Set.range fun i => ggLin (p := p) ι (φ (some i))) := by
      rw [MonoidHom.map_closure, ← Set.range_comp]; rfl
    rw [← hmap]
    exact Subgroup.mem_map_of_mem _ (hAL ▸ hw)
  have := hcl _ hwL _ (hRgen k)
  rw [← map_inv, ← map_mul, ← map_mul, he, map_mul, map_mul, map_inv]
  exact this

end CFSG.StandardType
