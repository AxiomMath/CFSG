module

public import CFSG.Quasithin.H13.NQS134EC

public section

namespace CFSG.Quasithin.H13.NQS134

open Equiv Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem card_conjSub' (g : G) (H : Subgroup G) : Nat.card (conjSub g H) = Nat.card H :=
  Nat.card_congr (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom
    (MulAut.conj g).injective).toEquiv.symm

namespace End134

variable (S : A6.Setting134 G T L V)
include S

theorem mul_self_of_mem {v : G} (hv : v ∈ V) : v * v = 1 := by
  have h1 : S.frame.ψ (⟨v, hv⟩ * ⟨v, hv⟩) = 1 := Subtype.ext (by rw [map_mul]; exact P6_mul_self _)
  rw [MulEquiv.map_eq_one_iff] at h1
  exact congrArg Subtype.val h1

theorem mul_self_of_mem_conj {g a : G} (ha : a ∈ conjSub g V) : a * a = 1 := by
  have h := mul_self_of_mem S (mem_conjSub.1 ha)
  have e : a * a = g * ((g⁻¹ * a * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
  rw [e, h]
  group

theorem comm_of_mem {u v : G} (hu : u ∈ V) (hv : v ∈ V) : u * v = v * u := by
  have h1 := mul_self_of_mem S (mul_mem hu hv)
  have hui : u⁻¹ = u := inv_eq_of_mul_eq_one_right (mul_self_of_mem S hu)
  have hvi : v⁻¹ = v := inv_eq_of_mul_eq_one_right (mul_self_of_mem S hv)
  have h2 : (u * v)⁻¹ = u * v := inv_eq_of_mul_eq_one_right h1
  rw [mul_inv_rev, hui, hvi] at h2
  exact h2.symm

theorem le_centralizer_self : V ≤ centralizer (V : Set G) := fun _ hu =>
  mem_centralizer_iff.2 fun _ hv => comm_of_mem S hv hu

theorem card_conj (g : G) : Nat.card (conjSub g V) = 32 := by
  rw [card_conjSub', S.card_V]

theorem conj_ne_of_not_le {g : G} (h : ¬ conjSub g V ≤ centralizer (V : Set G)) :
    conjSub g V ≠ V := fun he => h (by rw [he]; exact le_centralizer_self S)

variable {z : G} (hz : z ∈ fsuV1 T V) (hzL : z ∉ centralizer (L : Set G))
  (huniq : ∀ z' ∈ quasithinOmegaOneCenter T, z' ≠ 1 →
    ¬ centralizer ({z'} : Set G) ≤ normalizer (L : Set G) → z' = z)
include hz hzL huniq

theorem wt_comm_of_mem (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {g : G} (hne : conjSub g V ≠ V)
    {x v : G} (hx : x ∈ normalizer (V : Set G)) (hv : v ∈ V)
    (hcg : x * v * x⁻¹ * v⁻¹ ∈ conjSub g V) :
    x * v * x⁻¹ * v⁻¹ = 1 ∨ wtP (G6.permAct 6 (S.frame.ρ ⟨x, hx⟩) (S.frame.ψ ⟨v, hv⟩ : P6) *
      (S.frame.ψ ⟨v, hv⟩ : P6)) = wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
  by_cases h1 : x * v * x⁻¹ * v⁻¹ = 1
  · exact Or.inl h1
  right
  have hcV : x * v * x⁻¹ * v⁻¹ ∈ V :=
    mul_mem ((mem_normalizer_iff.mp hx v).mp hv) (inv_mem hv)
  rw [← comm_psi S hx hv hcV]
  by_contra hw
  exact hne (eq_of_mem_conj S hz hzL huniq h331 h1222 hcV h1 hw hcg)

theorem rho_of_normalizes (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2) {g : G}
    (hAN : conjSub g V ≤ normalizer (V : Set G))
    (hVN : V ≤ normalizer (conjSub g V : Set G))
    (hAC : ¬ conjSub g V ≤ centralizer (V : Set G)) :
    ∃ (a₀ : G) (ha₀ : a₀ ∈ conjSub g V), S.frame.ρ ⟨a₀, hAN ha₀⟩ ≠ 1 ∧
      (∀ (a : G) (ha : a ∈ conjSub g V), S.frame.ρ ⟨a, hAN ha⟩ = 1 ∨
        S.frame.ρ ⟨a, hAN ha⟩ = S.frame.ρ ⟨a₀, hAN ha₀⟩) ∧
      (wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 4 → S.frame.ρ ⟨a₀, hAN ha₀⟩ ∈ fpfList) ∧
      (wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 2 →
        ∃ i j : Fin 6, i ≠ j ∧ S.frame.ρ ⟨a₀, hAN ha₀⟩ = swap i j) := by
  have hne := conj_ne_of_not_le S hAC
  obtain ⟨a₀, ha₀, ha₀C⟩ := IsConcreteLE.not_le_iff_exists.1 hAC
  have ha₀1 : S.frame.ρ ⟨a₀, hAN ha₀⟩ ≠ 1 := fun h => ha₀C ((frame5_ker_iff S.frame _).1 h)
  have hw : wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 2 ∨ wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 4 := by
    rcases psi_z_cases' S hz hzL with h | h
    · rw [h]; exact Or.inr wtP_e0123
    · rw [h]; exact Or.inl wtP_e45
  have hcomm : ∀ (a : G) (ha : a ∈ conjSub g V) (v : G) (hv : v ∈ V), a * v * a⁻¹ * v⁻¹ = 1 ∨
      wtP (G6.permAct 6 (S.frame.ρ ⟨a, hAN ha⟩) (S.frame.ψ ⟨v, hv⟩ : P6) *
        (S.frame.ψ ⟨v, hv⟩ : P6)) = wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) := by
    intro a ha v hv
    refine wt_comm_of_mem S hz hzL huniq h331 h1222 hne (hAN ha) hv ?_
    have h1 : v * a⁻¹ * v⁻¹ ∈ conjSub g V := (mem_normalizer_iff.mp (hVN hv) _).mp (inv_mem ha)
    have e : a * v * a⁻¹ * v⁻¹ = a * (v * a⁻¹ * v⁻¹) := by group
    rw [e]
    exact mul_mem ha h1
  obtain ⟨hρ, h4, h2⟩ := rho_eq_of_comm S hAN (fun a ha => mul_self_of_mem_conj S ha) hw hcomm
    ha₀ ha₀1
  exact ⟨a₀, ha₀, ha₀1, hρ, h4, h2⟩

theorem false_of_normalizes_four (h331 : Stmt3_3_1) (h1222 : Stmt12_2_2)
    (h4 : wtP (S.frame.ψ ⟨z, hz.1⟩ : P6) = 4) {g : G}
    (hAN : conjSub g V ≤ normalizer (V : Set G))
    (hVN : V ≤ normalizer (conjSub g V : Set G))
    (hAC : ¬ conjSub g V ≤ centralizer (V : Set G)) : False := by
  obtain ⟨a₀, ha₀, ha₀1, hρ, -, -⟩ := rho_of_normalizes S hz hzL huniq h331 h1222 hAN hVN hAC
  have hA16 := card_inf_centralizer S hAN ha₀ ha₀1 hρ
  rw [card_conj S g] at hA16
  have hAN' : conjSub g⁻¹ V ≤ normalizer (V : Set G) := by
    rw [conjSub_le_iff, inv_inv, ← conjSub_normalizer]
    exact hVN
  have hVN' : V ≤ normalizer (conjSub g⁻¹ V : Set G) := by
    rw [conjSub_normalizer, ← conjSub_le_iff]
    exact hAN
  have hAC' : ¬ conjSub g⁻¹ V ≤ centralizer (V : Set G) := by
    intro h
    apply hAC
    rw [conjSub_le_iff, inv_inv, ← conjSub_centralizer] at h
    intro a ha
    rw [mem_centralizer_iff]
    intro v hv
    exact (mem_centralizer_iff.1 (h hv) a ha).symm
  obtain ⟨b₀, hb₀, hb₀1, hρ', hfpf, -⟩ :=
    rho_of_normalizes S hz hzL huniq h331 h1222 hAN' hVN' hAC'
  have hV8 := card_V_inf_centralizer S hAN' hb₀ hρ'
  rw [card_fix_fpf _ (hfpf h4)] at hV8
  have hconj : conjSub g (V ⊓ centralizer (conjSub g⁻¹ V : Set G)) =
      conjSub g V ⊓ centralizer (V : Set G) := by
    rw [conjSub_inf, conjSub_centralizer, conjSub_inv_conjSub]
  have h8 := card_conjSub' g (V ⊓ centralizer (conjSub g⁻¹ V : Set G))
  rw [hconj, hV8] at h8
  omega

end End134

end CFSG.Quasithin.H13.NQS134
