module

public import CFSG.Monster.GMS.S365CentPathSpecBase
public import CFSG.Monster.GMS.S365Embed
import CFSG.Assembly.Defs
import CFSG.Monster.GMS.Leech.OddPhi

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

theorem mem_o2_of_coset {a b ω u : Fin 24 → ZMod 2} (h : FourPattern a b ω)
    (hu : CosetEq a b u ω) : u ∈ co1Orbit 2 := by
  obtain ⟨-, -, -, h4, h5, h6, h7⟩ := h
  rcases hu.cases with rfl | rfl | rfl | rfl <;> assumption

theorem FourPattern.linearIndependent
    {a b ω : Fin 24 → ZMod 2} (h : FourPattern a b ω) :
    LinearIndependent (ZMod 2) ![a, b, ω] := by
  obtain ⟨hx0', hy0', hxy0', hw4', -, -, -⟩ := h
  have hne : ∀ {u : Fin 24 → ZMod 2}, u ∈ co1Orbit 0 → ω ≠ u := by
    intro u hu hh
    exact absurd (Leech.eq_of_mem_co1Orbit hw4' (hh ▸ hu)) (by decide)
  refine Leech.linearIndependent_fin_three (Leech.ne_zero_of_mem_co1Orbit hx0')
    (Leech.ne_zero_of_mem_co1Orbit hy0') (Leech.ne_zero_of_mem_co1Orbit hw4') ?_
    (fun hh => hne hx0' hh.symm) (fun hh => hne hy0' hh.symm) (fun hh => hne hxy0' hh.symm)
  intro hh
  rw [hh, CFSG.Sporadic.Co1.Module.vec_add_self] at hxy0'
  exact Leech.ne_zero_of_mem_co1Orbit hxy0' rfl

variable {G : Type} [Group G] [Finite G] {d₀ : B} {a z₀ : G}

omit [Finite G] in
theorem exists_conj_lift
    {q x y w x' y' w' : G} (L : LeechSystem q) (hx : x ∈ leechQ q)
    (hy : y ∈ leechQ q) (hw : w ∈ leechQ q) (hx' : x' ∈ leechQ q) (hy' : y' ∈ leechQ q)
    (hw' : w' ∈ leechQ q) (g₀ : Co1) (hgx : co1Act g₀ (L.vec x) = L.vec x')
    (hgy : co1Act g₀ (L.vec y) = L.vec y') (hgw : co1Act g₀ (L.vec w) = L.vec w')
    (hind : LinearIndependent (ZMod 2) ![L.vec x', L.vec y', L.vec w']) :
    ∃ g : G, ∃ hgC : g ∈ Subgroup.centralizer ({q} : Set G), L.φ ⟨g, hgC⟩ = g₀ ∧
      g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' ∧ g * w * g⁻¹ = w' := by
  obtain ⟨gh, hgh⟩ := L.φ_surj g₀
  have hghC : (gh : G) ∈ Subgroup.centralizer ({q} : Set G) := gh.2
  have hxv : L.vec ((gh : G) * x * (gh : G)⁻¹) = L.vec x' := by
    rw [L.vec_conj gh x hx, hgh, hgx]
  have hyv : L.vec ((gh : G) * y * (gh : G)⁻¹) = L.vec y' := by
    rw [L.vec_conj gh y hy, hgh, hgy]
  have hwv : L.vec ((gh : G) * w * (gh : G)⁻¹) = L.vec w' := by
    rw [L.vec_conj gh w hw, hgh, hgw]
  have hind' : LinearIndependent (ZMod 2) fun i : Fin 3 => L.vec (![x', y', w'] i) := by
    have e : (fun i : Fin 3 => L.vec (![x', y', w'] i)) = ![L.vec x', L.vec y', L.vec w'] := by
      funext i
      fin_cases i <;> rfl
    rw [e]
    exact hind
  obtain ⟨p, hp, hpa⟩ := L.exists_conj_eq (a := ![(gh : G) * x * (gh : G)⁻¹,
      (gh : G) * y * (gh : G)⁻¹, (gh : G) * w * (gh : G)⁻¹]) (b := ![x', y', w'])
    (fun i => by
      fin_cases i
      exacts [L.conj_mem gh hx, L.conj_mem gh hy, L.conj_mem gh hw])
    (fun i => by fin_cases i; exacts [hx', hy', hw'])
    (fun i => by fin_cases i; exacts [hxv, hyv, hwv]) hind'
  have h0 := hpa 0
  have h1 := hpa 1
  have h2 := hpa 2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons,
    Matrix.tail_cons] at h0 h1 h2
  have hpC : p ∈ Subgroup.centralizer ({q} : Set G) := L.mem_centralizer hp
  have hgC : p * (gh : G) ∈ Subgroup.centralizer ({q} : Set G) := mul_mem hpC hghC
  refine ⟨p * (gh : G), hgC, ?_, ?_, ?_, ?_⟩
  · have h1 : L.φ ⟨p * (gh : G), hgC⟩ = L.φ ⟨p, hpC⟩ * L.φ ⟨(gh : G), hghC⟩ :=
      L.phi_mul hpC hghC
    rw [h1, (L.φ_ker ⟨p, hpC⟩).2 hp, one_mul]
    exact hgh
  · rw [← h0]
    group
  · rw [← h1]
    group
  · rw [← h2]
    group

theorem exists_conj_exact
    (I : GMSInterfaces d₀ G) (hG : GMSF1Type d₀ a z₀) (hT : Co1FourTV)
    {q x y w x' y' w' : G} (h : Embedded a z₀ q x y w) (L : LeechSystem q) (hx' : x' ∈ leechQ q)
    (hy' : y' ∈ leechQ q) (hw' : w' ∈ leechQ q)
    (hP' : FourPattern (L.vec x') (L.vec y') (L.vec w')) :
    ∃ g ∈ Subgroup.centralizer ({q} : Set G), g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' ∧
      g * w * g⁻¹ = w' := by
  have hP := h.fourPattern I hG L
  obtain ⟨g₀, hg₀x, hg₀y, hg₀w⟩ := hT _ _ _ _ _ _ hP hP'
  obtain ⟨g, hgC, -, hgx, hgy, hgw⟩ := exists_conj_lift L h.x_mem h.y_mem h.w_mem hx' hy' hw' g₀
    hg₀x hg₀y hg₀w hP'.linearIndependent
  exact ⟨g, hgC, hgx, hgy, hgw⟩

end S365

end CFSG.Monster.GMS
