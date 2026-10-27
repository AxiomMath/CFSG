module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamDefs
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE9FamTr
public import CFSG.Quasithin.EmptyFaithful.T1521SSp4All

public section

namespace CFSG.Quasithin.E9.SpFour

open CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial CFSG.QuasithinUnique
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFour
open CFSG.LocalAnalysis.ComponentInitial.SymplecticCoverFour
open CFSG.Quasithin.Sp4

section Model

variable {F : Type} [Field F] [Finite F] [CharP F 2]

omit [Finite F] in
theorem comm_of_proj_comm {u t : StatedSp 2 F}
    (h : proj 2 F u * proj 2 F t = proj 2 F t * proj 2 F u) : t * u = u * t :=
  proj_injective (by rw [map_mul, map_mul]; exact h.symm)

omit [Finite F] in
theorem eq_one_of_comm_torus {a : Fˣ} (ha : a ≠ 1) {u : StatedSp 2 F} (hu : u ∈ unipotent 2 F)
    (h1 : SymplecticTorusWeyl.torusHom ![a, 1] * u = u * SymplecticTorusWeyl.torusHom ![a, 1])
    (h2 : SymplecticTorusWeyl.torusHom ![1, a] * u = u * SymplecticTorusWeyl.torusHom ![1, a]) :
    u = 1 := by
  have ha1 : (a : F) ≠ 1 := fun h => ha (Units.ext h)
  have ha2 : (a : F) ^ 2 ≠ 1 := sq_ne_one_of_charTwo ha1
  obtain ⟨C, hC, a', rfl⟩ := mem_unipotent_iff.mp hu
  rw [tau_eq_tauS] at h1 h2 ⊢
  obtain ⟨hb, hc, -, ha'⟩ := coords_of_torus_comm ![a, 1] h1
  obtain ⟨-, -, hd, -⟩ := coords_of_torus_comm ![1, a] h2
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Units.val_one, inv_one,
    mul_one] at hb hc hd ha'
  have hsub : (a : F) - 1 ≠ 0 := sub_ne_zero.mpr ha1
  have hb0 : C 0 0 = 0 := by
    have : ((a : F) ^ 2 - 1) * C 0 0 = 0 := by linear_combination hb
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha2)
  have hc0 : C 0 1 = 0 := by
    have : ((a : F) - 1) * C 0 1 = 0 := by linear_combination hc
    exact (mul_eq_zero.mp this).resolve_left hsub
  have hd0 : C 1 1 = 0 := by
    have : ((a : F) ^ 2 - 1) * C 1 1 = 0 := by linear_combination hd
    exact (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr ha2)
  have ha0 : a' = 0 := by
    have : ((a : F) - 1) * a' = 0 := by linear_combination ha'
    exact (mul_eq_zero.mp this).resolve_left hsub
  rw [hb0, hc0, hd0, ha0, tauS_zero, lam_zero, mul_one]

theorem eq_one_of_fixes {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card F = 2 ^ n) {a : Fˣ} (ha : a ≠ 1)
    (β : MulAut (StatedProj (StatedSp 2 F)))
    (hU : ∀ u ∈ unipotent 2 F, β (proj 2 F u) = proj 2 F u)
    (h1 : β (proj 2 F (SymplecticTorusWeyl.torusHom ![a, 1])) =
      proj 2 F (SymplecticTorusWeyl.torusHom ![a, 1]))
    (h2 : β (proj 2 F (SymplecticTorusWeyl.torusHom ![1, a])) =
      proj 2 F (SymplecticTorusWeyl.torusHom ![1, a])) : β = 1 := by
  have hα : ∀ x, β x ∈ projUnipotent 2 F ↔ x ∈ projUnipotent 2 F :=
    mem_iff_of_forall_mem β _ (by
      rintro _ ⟨u, hu, rfl⟩
      rw [hU u hu]
      exact ⟨u, hu, rfl⟩)
  obtain ⟨l₁, l₂, σ, ε, -, -, hact, hid⟩ := exists_vAct (by omega) hK hα
  have hVfix : ∀ x : F × F, vAct l₁ l₂ σ ε x = x := by
    intro x
    have h1 := hact x
    rw [show vP x.1 x.2 = proj 2 F (tauS x.1 x.2 0) from rfl,
      hU _ (tauS_mem_unipotent _ _ _)] at h1
    have h2 := vP_injective h1.symm
    exact Prod.ext h2.1 h2.2
  obtain ⟨u, hu, hβu⟩ := hid hVfix
  have hcomm : ∀ s : Fin 2 → Fˣ,
      β (proj 2 F (SymplecticTorusWeyl.torusHom s)) =
        proj 2 F (SymplecticTorusWeyl.torusHom s) →
      SymplecticTorusWeyl.torusHom s * u = u * SymplecticTorusWeyl.torusHom s := by
    intro s hs
    rw [hβu, MulAut.conj_apply] at hs
    exact comm_of_proj_comm (mul_inv_eq_iff_eq_mul.mp hs)
  have hu1 : u = 1 := eq_one_of_comm_torus ha hu (hcomm _ h1) (hcomm _ h2)
  rw [hβu, hu1, map_one, map_one]

end Model

section Transport

variable {G : Type} [Group G]

theorem exists_torus [Finite G] {L P : Subgroup G} {n : ℕ} (hn : 3 ≤ n) (hL : IsPSp4 2 n ↥L)
    (hP : IsSylowTwoOf P L) :
    ∃ H : Subgroup G, H ≤ L ⊓ Subgroup.normalizer (P : Set G) ∧ Odd (Nat.card H) ∧
      ∀ H₀ : Subgroup G, H₀ ≤ H → H₀.relIndex H ∣ 3 →
        (∀ v ∈ Subgroup.normalizer (L : Set G), (∀ x ∈ P, v * x = x * v) →
          (∀ h ∈ H₀, v * h = h * v) → ∀ l ∈ L, v * l = l * v) ∧
        (∀ x ∈ P, (∀ h ∈ H₀, x * h = h * x) → x = 1) := by
  obtain ⟨-, K, hKf, hKfin, hK, ⟨φ⟩⟩ := hL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hK
  obtain ⟨g, hg⟩ := Tr.exists_carries hP φ
    (exists_sylow_projUnipotent (K := K) (r := 2) 2 (by norm_num))
  obtain ⟨c, hc⟩ := Tr.exists_unit_cube_ne_one hn hK
  set a : Kˣ := c ^ 3 with ha
  let ψ : (Fin 2 → Kˣ) →* G :=
    (Tr.liftHom L φ g).comp ((proj 2 K).comp SymplecticTorusWeyl.torusHom)
  refine ⟨ψ.range, ?_, ?_, fun H₀ hH₀ hidx => ?_⟩
  · rintro _ ⟨s, rfl⟩
    refine ⟨Tr.liftHom_mem L φ g _, Tr.liftHom_mem_normalizer hP.1 hg ?_⟩
    rw [normalizer_projUnipotent (r := 2) (K := K) 2 (by norm_num)]
    exact ⟨SymplecticTorusWeyl.torusHom s, torus_le_borelSubgroup ⟨s, rfl⟩, rfl⟩
  · have hodd : Odd (Nat.card (Fin 2 → Kˣ)) := by
      rw [Nat.card_pi, Fin.prod_univ_two]
      exact (Tr.odd_card_units (by omega) hK).mul (Tr.odd_card_units (by omega) hK)
    exact hodd.of_dvd_nat (Subgroup.card_range_dvd ψ)
  · have hcomm : ∀ x ∈ ψ.range, ∀ y ∈ ψ.range, x * y = y * x := by
      rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩
      rw [← map_mul, ← map_mul, mul_comm s s']
    have hcube : ∀ s : Fin 2 → Kˣ, ψ (s ^ 3) ∈ H₀ := fun s => by
      rw [map_pow]
      exact pow_three_mem_of_relIndex_dvd_three hcomm hidx _ ⟨s, rfl⟩
    have h1 : ψ ![a, 1] ∈ H₀ := by
      have h := hcube ![c, 1]
      have e : (![c, 1] : Fin 2 → Kˣ) ^ 3 = ![a, 1] := by
        funext i
        fin_cases i <;> simp [ha]
      rwa [e] at h
    have h2 : ψ ![1, a] ∈ H₀ := by
      have h := hcube ![1, c]
      have e : (![1, c] : Fin 2 → Kˣ) ^ 3 = ![1, a] := by
        funext i
        fin_cases i <;> simp [ha]
      rwa [e] at h
    have ha1 : a ≠ 1 := hc
    have hkey : ∀ s : Fin 2 → Kˣ, ψ s ∈ H₀ → ∀ u ∈ unipotent 2 K,
        Tr.liftHom L φ g (proj 2 K u) * ψ s = ψ s * Tr.liftHom L φ g (proj 2 K u) →
        SymplecticTorusWeyl.torusHom s * u = u * SymplecticTorusWeyl.torusHom s := by
      intro s _ u _ h
      refine comm_of_proj_comm (Tr.liftHom_injective L φ g ?_)
      rw [map_mul, map_mul]
      exact h
    refine ⟨fun v hvN hvP hvH l hl => ?_, fun x hx hxH => ?_⟩
    · refine Tr.centralizes_of_conjAut_eq_one φ g hvN ?_ l hl
      refine eq_one_of_fixes (by omega) hK ha1 _ (fun u hu => ?_) ?_ ?_
      · exact Tr.conjAut_apply_of_commute φ g hvN
          (hvP _ (Tr.liftHom_mem_of_mem hg ⟨u, hu, rfl⟩))
      · exact Tr.conjAut_apply_of_commute φ g hvN (hvH _ h1)
      · exact Tr.conjAut_apply_of_commute φ g hvN (hvH _ h2)
    · obtain ⟨y, hy, rfl⟩ := Tr.exists_liftHom_eq hP.1 hg hx
      obtain ⟨u, hu, rfl⟩ := hy
      have hu1 : u = 1 :=
        eq_one_of_comm_torus ha1 hu (hkey _ h1 u hu (hxH _ h1)) (hkey _ h2 u hu (hxH _ h2))
      rw [hu1, map_one, map_one]

end Transport

end CFSG.Quasithin.E9.SpFour

namespace CFSG.Quasithin.E9

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin

variable {G : Type} [Group G] [Finite G]

set_option linter.unusedVariables false in
theorem nrmE9_Sp4_big (h37 : A37ForSQTK) (h38 : A38ForSQTK) {X S L : Subgroup G}
    (hStd : Std1521 X S L) (hc : IsComponentOf L X) (hZ : IsPGroup 2 ↥(Subgroup.center ↥L))
    {n : ℕ} (hn : 3 ≤ n) (hty : IsPSp4 2 n ↥L) : NrmE9 S L := by
  have hJ : thompsonJ S ≤ innerPart1521 S L :=
    thompsonJ_le_innerPart_sp4_of_orbits (a3Orbits_of_a37_a38 h37 h38) (by omega) hty hc hStd
  obtain ⟨H, hHL, hodd, hH⟩ := SpFour.exists_torus hn hty hStd.sylowL
  refine nrmE9_of_inner hJ hHL hodd fun H₀ hH₀ hidx => ?_
  obtain ⟨hEa, hEb⟩ := hH H₀ hH₀ hidx
  refine ⟨fun v _ hvN hvP hvH l hl => hEa v hvN hvP hvH l hl, fun x hx hxH => ?_⟩
  rw [hEb x hx.1 hxH]
  exact (centerOf L).one_mem

end CFSG.Quasithin.E9
