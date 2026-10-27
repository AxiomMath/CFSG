module

public import CFSG.Quasithin.Background.C126A5Data
public import CFSG.Quasithin.Background.C126A5Core2

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin Equiv CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G]

open Classical in
@[expose] noncomputable def cv {V : Subgroup G} (hV : IsElemAbelian 2 V) (g : G) :
    MulAut (IntMod V hV) :=
  if h : g ∈ Subgroup.normalizer (V : Set G) then convI hV ⟨g, h⟩ else 1

section CV

variable {V : Subgroup G} (hV : IsElemAbelian 2 V)

theorem cv_of_mem {g : G} (h : g ∈ Subgroup.normalizer (V : Set G)) :
    cv hV g = convI hV ⟨g, h⟩ := by
  simp [cv, h]

theorem cv_one : cv hV (1 : G) = 1 :=
  (cv_of_mem hV (Subgroup.one_mem _)).trans (map_one (convI hV))

theorem cv_mul {g g' : G} (hg : g ∈ Subgroup.normalizer (V : Set G))
    (hg' : g' ∈ Subgroup.normalizer (V : Set G)) : cv hV (g * g') = cv hV g * cv hV g' := by
  rw [cv_of_mem hV hg, cv_of_mem hV hg', cv_of_mem hV (Subgroup.mul_mem _ hg hg')]
  exact (convI hV).map_mul ⟨g, hg⟩ ⟨g', hg'⟩

theorem cv_inv {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    cv hV g⁻¹ = (cv hV g)⁻¹ := by
  rw [cv_of_mem hV hg, cv_of_mem hV (Subgroup.inv_mem _ hg)]
  exact (convI hV).map_inv ⟨g, hg⟩

theorem cv_val {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) (v : IntMod V hV) :
    ((cv hV g) v).val = g * v.val * g⁻¹ := by
  rw [cv_of_mem hV hg]
  exact convI_apply_val hV ⟨g, hg⟩ v

theorem cv_eq_one_iff {g : G} (hg : g ∈ Subgroup.normalizer (V : Set G)) :
    cv hV g = 1 ↔ g ∈ Subgroup.centralizer (V : Set G) := by
  rw [cv_of_mem hV hg]
  exact convI_eq_one_iff hV ⟨g, hg⟩

theorem mem_autI_iff {K : Subgroup G} (hK : K ≤ Subgroup.normalizer (V : Set G))
    {φ : MulAut (IntMod V hV)} : φ ∈ autI hV K ↔ ∃ g ∈ K, cv hV g = φ := by
  rw [mem_autI]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g, hg, cv_of_mem hV g.2⟩
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hK hg⟩, hg, (cv_of_mem hV (hK hg)).symm⟩

end CV

namespace Data

variable {H T V Y : Subgroup G} {hV : IsElemAbelian 2 V} (d : Data H T V Y hV)

open Classical in
@[expose] noncomputable def th (φ : MulAut (IntMod V hV)) : Perm (Fin 5) :=
  if h : φ ∈ d.L then d.θ ⟨φ, h⟩ else 1

theorem th_of_mem {φ : MulAut (IntMod V hV)} (h : φ ∈ d.L) : d.th φ = d.θ ⟨φ, h⟩ := by
  simp [th, h]

theorem th_mul {φ ψ : MulAut (IntMod V hV)} (hφ : φ ∈ d.L) (hψ : ψ ∈ d.L) :
    d.th (φ * ψ) = d.th φ * d.th ψ := by
  rw [d.th_of_mem hφ, d.th_of_mem hψ, d.th_of_mem (d.L.mul_mem hφ hψ)]
  exact d.θ.map_mul ⟨φ, hφ⟩ ⟨ψ, hψ⟩

theorem th_inv {φ : MulAut (IntMod V hV)} (hφ : φ ∈ d.L) : d.th φ⁻¹ = (d.th φ)⁻¹ := by
  rw [d.th_of_mem hφ, d.th_of_mem (d.L.inv_mem hφ)]
  exact d.θ.map_inv ⟨φ, hφ⟩

theorem th_one : d.th 1 = 1 := by
  rw [d.th_of_mem d.L.one_mem]
  exact d.θ.map_one

theorem th_inj {φ ψ : MulAut (IntMod V hV)} (hφ : φ ∈ d.L) (hψ : ψ ∈ d.L)
    (h : d.th φ = d.th ψ) : φ = ψ := by
  rw [d.th_of_mem hφ, d.th_of_mem hψ] at h
  exact congrArg Subtype.val (d.θ.injective h)

theorem exists_of_th {g : Perm (Fin 5)} : ∃ φ ∈ d.L, d.th φ = g := by
  refine ⟨(d.θ.symm g : MulAut (IntMod V hV)), (d.θ.symm g).2, ?_⟩
  rw [d.th_of_mem (d.θ.symm g).2]
  simp

end Data

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} (s : Setting H T M V Y hV)
  (d : Data H T V Y hV)

@[expose] def A₁ : Subgroup G where
  carrier := {g | g ∈ H ∧ cv hV g ∈ d.L}
  one_mem' := ⟨H.one_mem, by
    rw [cv_of_mem hV (Subgroup.one_mem _)]
    exact (show convI hV (1 : Subgroup.normalizer (V : Set G)) = 1 from map_one _) ▸ d.L.one_mem⟩
  mul_mem' := fun {a b} ha hb => ⟨H.mul_mem ha.1 hb.1, by
    rw [cv_mul hV (s.H_le_N ha.1) (s.H_le_N hb.1)]; exact d.L.mul_mem ha.2 hb.2⟩
  inv_mem' := fun {a} ha => ⟨H.inv_mem ha.1, by
    rw [cv_inv hV (s.H_le_N ha.1)]; exact d.L.inv_mem ha.2⟩

variable {s d}

theorem mem_A₁ {g : G} : g ∈ A₁ s d ↔ g ∈ H ∧ cv hV g ∈ d.L := Iff.rfl

theorem A₁_le_H : A₁ s d ≤ H := fun _ hg => hg.1

include s d

theorem Y_le_A₁ : Y ≤ A₁ s d := by
  intro y hy
  have hmem : cv hV y ∈ autI hV Y := (mem_autI_iff hV (s.Y_le.trans s.H_le_N)).2 ⟨y, hy, rfl⟩
  exact ⟨s.Y_le hy, (d.Y_L _ hmem).1⟩

theorem Q_le_A₁ : pCoreOf 2 H ≤ A₁ s d := by
  intro q hq
  refine ⟨(pCoreOf_le 2 H) hq, ?_⟩
  have h1 : cv hV q = 1 :=
    (cv_eq_one_iff hV (s.H_le_N ((pCoreOf_le 2 H) hq))).2 (s.Q_le_C hq)
  rw [h1]
  exact d.L.one_mem

theorem exists_A₁_cv {φ : MulAut (IntMod V hV)} (hφ : φ ∈ d.L) : ∃ a ∈ A₁ s d, cv hV a = φ := by
  obtain ⟨a, ha, rfl⟩ := (mem_autI_iff hV s.H_le_N).1 (d.L_le hφ)
  exact ⟨a, ⟨ha, hφ⟩, rfl⟩

theorem exists_x : ∃ x ∈ Y, orderOf x = 3 ∧ cv hV x ∈ d.L ∧ d.th (cv hV x) = cyc3 d.π := by
  obtain ⟨x₀, hx₀, hx₀3⟩ := s.exists_order_three
  have hYN : Y ≤ Subgroup.normalizer (V : Set G) := s.Y_le.trans s.H_le_N
  have hmem : cv hV x₀ ∈ autI hV Y := (mem_autI_iff hV hYN).2 ⟨x₀, hx₀, rfl⟩
  obtain ⟨hφ, hcl⟩ := d.Y_L _ hmem
  have hc3 : orderOf (cyc3 d.π) = 3 := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    exact orderOf_eq_prime (cyc3_pow_three d.π) (cyc3_ne_one d.π)
  have hne : d.th (cv hV x₀) ≠ 1 := by
    intro h1
    have h2 : cv hV x₀ = 1 := d.th_inj hφ d.L.one_mem (by rw [h1, d.th_one])
    have h3 : x₀ ∈ Subgroup.centralizer (V : Set G) := (cv_eq_one_iff hV (hYN hx₀)).1 h2
    exact s.Y_not_mem_Q hx₀3 (s.Y_C ⟨hx₀, h3⟩)
  rw [d.th_of_mem hφ] at hne
  have hz : d.θ ⟨cv hV x₀, hφ⟩ ∈ Subgroup.zpowers (cyc3 d.π) := by
    rw [Subgroup.zpowers_eq_closure]; exact hcl
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 hz
  have hm' : cyc3 d.π ^ (m % 3) = d.θ ⟨cv hV x₀, hφ⟩ := by
    have := zpow_mod_orderOf (cyc3 d.π) m
    rw [hc3] at this
    simpa [hm] using this
  have hcub : cyc3 d.π ^ 3 = 1 := cyc3_pow_three d.π
  have hcase : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hcase with h0 | h1 | h2
  · rw [h0] at hm'; simp at hm'; exact absurd hm'.symm hne
  · rw [h1] at hm'
    refine ⟨x₀, hx₀, hx₀3, hφ, ?_⟩
    rw [d.th_of_mem hφ, ← hm']; simp
  · rw [h2] at hm'
    have hinv : d.θ ⟨cv hV x₀, hφ⟩ = (cyc3 d.π)⁻¹ := by
      rw [← hm']
      have : cyc3 d.π ^ (2 : ℤ) * cyc3 d.π = 1 := by
        rw [← zpow_add_one]; simpa using hcub
      exact (eq_inv_of_mul_eq_one_left this)
    refine ⟨x₀⁻¹, Y.inv_mem hx₀, by rw [orderOf_inv]; exact hx₀3, ?_, ?_⟩
    · rw [cv_inv hV (hYN hx₀)]; exact d.L.inv_mem hφ
    · rw [cv_inv hV (hYN hx₀), d.th_inv hφ, d.th_of_mem hφ, hinv]; simp

end Lift

end CFSG.Quasithin.C126.A5
