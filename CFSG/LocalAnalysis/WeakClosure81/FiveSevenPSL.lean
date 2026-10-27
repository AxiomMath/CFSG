module

public import CFSG.Holt.PSL2Natural.Basic
public import CFSG.LocalAnalysis.SectionRank.Ccomm.ElementaryAut

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Holt Equiv
open scoped LinearAlgebra.Projectivization

theorem b5_FiveSevenPSL_card_ne {Ω : Type*} [Finite Ω] (a : Ω) :
    Nat.card {x : Ω // x ≠ a} = Nat.card Ω - 1 := by
  classical
  have := Fintype.ofFinite Ω
  rw [Nat.card_eq_fintype_card, Nat.card_eq_fintype_card]
  exact Set.card_ne_eq a

theorem exists_isNaturalPSL2_ge_of_regular {Δ : Type*} [Finite Δ] {m : ℕ} (hm : m ≠ 0)
    (hcard : Nat.card Δ = 2 ^ m + 1) {A : Subgroup (Perm Δ)} (hA : IsElemAbelian 2 A) {α : Δ}
    (hfix : ∀ a ∈ A, a α = α)
    (hreg : ∀ β γ : Δ, β ≠ α → γ ≠ α → ∃! a : ↥A, (a : Perm Δ) β = γ) :
    ∃ K : Subgroup (Perm Δ), IsNaturalPSL2 K m ∧ A ≤ K := by
  classical
  have hm1 : 1 ≤ m := Nat.one_le_iff_ne_zero.mpr hm
  have h2pow : 2 ≤ 2 ^ m := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm1
  have hΔ1 : 1 < Nat.card Δ := by rw [hcard]; omega
  haveI : Nontrivial Δ := Finite.one_lt_card_iff_nontrivial.mp hΔ1
  obtain ⟨β₀, hβ₀⟩ := exists_ne α
  have hmemA : ∀ a : ↥A, (a : Perm Δ) β₀ ≠ α := by
    intro a ha
    exact hβ₀ ((a : Perm Δ).injective (ha.trans (hfix a a.2).symm))
  have hsurjA : Function.Surjective
      (fun a : ↥A => (⟨(a : Perm Δ) β₀, hmemA a⟩ : {y : Δ // y ≠ α})) := by
    rintro ⟨γ, hγ⟩
    obtain ⟨a, ha, -⟩ := hreg β₀ γ hβ₀ hγ
    exact ⟨a, Subtype.ext ha⟩
  have hinjA : Function.Injective
      (fun a : ↥A => (⟨(a : Perm Δ) β₀, hmemA a⟩ : {y : Δ // y ≠ α})) := by
    intro a b hab
    have hab' : (a : Perm Δ) β₀ = (b : Perm Δ) β₀ := congrArg Subtype.val hab
    obtain ⟨c, -, huniq⟩ := hreg β₀ ((a : Perm Δ) β₀) hβ₀ (hmemA a)
    exact (huniq a rfl).trans (huniq b hab'.symm).symm
  let oA : ↥A ≃ {y : Δ // y ≠ α} :=
    Equiv.ofBijective
      (fun a : ↥A => (⟨(a : Perm Δ) β₀, hmemA a⟩ : {y : Δ // y ≠ α}))
      ⟨hinjA, hsurjA⟩
  have hAcard : Nat.card ↥A = 2 ^ m := by
    rw [Nat.card_congr oA, b5_FiveSevenPSL_card_ne α, hcard, Nat.add_sub_cancel]
  obtain ⟨eA⟩ : Nonempty (↥A ≃* Multiplicative (Fin m → ZMod 2)) :=
    CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := ↥A)
      (fun a b => hA.1.is_comm.comm a b)
      (fun a => Subtype.ext (by simpa using hA.2 a a.2)) hAcard
  let F := GaloisField 2 m
  let Δ₀ := ℙ F (Fin 2 → F)
  let K₀ : Subgroup (Perm Δ₀) :=
    (MulAction.toPermHom (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) Δ₀).range
  have hK₀ : IsNaturalPSL2 K₀ m := IsNaturalPSL2.range_toPermHom m
  haveI : Finite Δ₀ := hK₀.finite
  have hΔ₀card : Nat.card Δ₀ = 2 ^ m + 1 := hK₀.card_eq_two_pow_add_one hm
  have hΔ₀pos : 0 < Nat.card Δ₀ := by rw [hΔ₀card]; omega
  haveI : Nonempty Δ₀ := Finite.card_pos_iff.mp hΔ₀pos
  let a₀ : Δ₀ := Classical.arbitrary Δ₀
  have hΔ₀1 : 1 < Nat.card Δ₀ := by rw [hΔ₀card]; omega
  haveI : Nontrivial Δ₀ := Finite.one_lt_card_iff_nontrivial.mp hΔ₀1
  obtain ⟨b₀, hb₀⟩ := exists_ne a₀
  let U₀ : Subgroup ↥K₀ := unipotentRadical ↥K₀ a₀
  have hUfix : ∀ u : ↥U₀, u • a₀ = a₀ := by
    intro u
    exact ((hK₀.mem_unipotentRadical_iff (a := a₀) (g := (u : ↥K₀))).mp u.2).1
  have hUpow : ∀ u : ↥U₀, u ^ 2 = 1 := by
    intro u
    apply Subtype.ext
    simpa using
      ((hK₀.mem_unipotentRadical_iff (a := a₀) (g := (u : ↥K₀))).mp u.2).2
  have hUcomm : ∀ a b : ↥U₀, a * b = b * a := fun a b =>
    (hK₀.isMulCommutative_unipotentRadical (a := a₀)).is_comm.comm a b
  have hUcard : Nat.card ↥U₀ = 2 ^ m :=
    hK₀.card_unipotentRadical_eq_two_pow hm (a := a₀)
  obtain ⟨eU⟩ : Nonempty (↥U₀ ≃* Multiplicative (Fin m → ZMod 2)) :=
    CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (W := ↥U₀)
      hUcomm hUpow hUcard
  let θ : ↥U₀ ≃* ↥A := eU.trans eA.symm
  have hmemU : ∀ u : ↥U₀, u • b₀ ≠ a₀ := by
    intro u h
    exact hb₀ (smul_left_cancel u (h.trans (hUfix u).symm))
  have hsurjU : Function.Surjective
      (fun u : ↥U₀ => (⟨u • b₀, hmemU u⟩ : {x : Δ₀ // x ≠ a₀})) := by
    rintro ⟨γ, hγ⟩
    obtain ⟨u, hu, -⟩ :=
      hK₀.existsUnique_unipotentRadical_smul_eq (a := a₀) (b := b₀) (c := γ) hb₀ hγ
    exact ⟨u, Subtype.ext hu⟩
  have hinjU : Function.Injective
      (fun u : ↥U₀ => (⟨u • b₀, hmemU u⟩ : {x : Δ₀ // x ≠ a₀})) := by
    intro u v huv
    have huv' : u • b₀ = v • b₀ := congrArg Subtype.val huv
    obtain ⟨c, -, huniq⟩ :=
      hK₀.existsUnique_unipotentRadical_smul_eq (a := a₀) (b := b₀) (c := u • b₀) hb₀
        (hmemU u)
    exact (huniq u rfl).trans (huniq v huv'.symm).symm
  let o₀ : ↥U₀ ≃ {x : Δ₀ // x ≠ a₀} :=
    Equiv.ofBijective
      (fun u : ↥U₀ => (⟨u • b₀, hmemU u⟩ : {x : Δ₀ // x ≠ a₀}))
      ⟨hinjU, hsurjU⟩
  have o₀_apply : ∀ u : ↥U₀, o₀ u = (⟨u • b₀, hmemU u⟩ : {x : Δ₀ // x ≠ a₀}) :=
    fun _ => rfl
  let ψ₁ : {x : Δ₀ // x ≠ a₀} ≃ {y : Δ // y ≠ α} := o₀.symm.trans (θ.toEquiv.trans oA)
  let ψ : Δ₀ ≃ Δ :=
    (Equiv.optionSubtypeNe a₀).symm.trans
      ((Equiv.optionCongr ψ₁).trans (Equiv.optionSubtypeNe α))
  have hψα : ψ a₀ = α := by
    dsimp only [ψ]
    rw [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_self]
    rfl
  have hψ_of_ne : ∀ (y : Δ₀) (hy : y ≠ a₀), ψ y = ψ₁ ⟨y, hy⟩ := by
    intro y hy
    dsimp only [ψ]
    rw [Equiv.trans_apply, Equiv.optionSubtypeNe_symm_of_ne hy]
    rfl
  have hψ_smul : ∀ (u : ↥U₀) (x : Δ₀), ψ (u • x) = (θ u : Perm Δ) (ψ x) := by
    intro u x
    by_cases hx : x = a₀
    · subst hx
      rw [hUfix u, hψα]
      exact (hfix (θ u) (θ u).2).symm
    · set v : ↥U₀ := o₀.symm ⟨x, hx⟩ with hv_def
      have hv : v • b₀ = x := by
        have h1 : o₀ v = (⟨x, hx⟩ : {x : Δ₀ // x ≠ a₀}) := by
          rw [hv_def, Equiv.apply_symm_apply]
        have h2 := congrArg Subtype.val h1
        rwa [o₀_apply v] at h2
      have hux_eq : u • x = (u * v) • b₀ := by rw [← hv, mul_smul]
      have hux : u • x ≠ a₀ := by
        rw [hux_eq]
        exact hmemU (u * v)
      have ho : o₀ (u * v) = (⟨u • x, hux⟩ : {x : Δ₀ // x ≠ a₀}) := by
        apply Subtype.ext
        rw [o₀_apply (u * v)]
        exact hux_eq.symm
      have hov : o₀.symm ⟨u • x, hux⟩ = u * v := by
        rw [← ho, Equiv.symm_apply_apply]
      have hψx : ψ x = (θ v : Perm Δ) β₀ := by
        rw [hψ_of_ne x hx]
        dsimp only [ψ₁]
        rw [Equiv.trans_apply, Equiv.trans_apply]
        rfl
      calc
        ψ (u • x) = ψ₁ ⟨u • x, hux⟩ := hψ_of_ne (u • x) hux
        _ = (θ (u * v) : Perm Δ) β₀ := by
              dsimp only [ψ₁]
              rw [Equiv.trans_apply, Equiv.trans_apply, hov]
              rfl
        _ = (θ u : Perm Δ) ((θ v : Perm Δ) β₀) := by
              rw [map_mul, Subgroup.coe_mul, Perm.mul_apply]
        _ = (θ u : Perm Δ) (ψ x) := by rw [hψx]
  refine ⟨K₀.map (ψ.permCongrHom : Perm Δ₀ →* Perm Δ), hK₀.map_permCongrHom ψ, ?_⟩
  intro a ha
  rw [Subgroup.mem_map]
  let u : ↥U₀ := θ.symm ⟨a, ha⟩
  refine ⟨((u : ↥K₀) : Perm Δ₀), (u : ↥K₀).2, ?_⟩
  apply Equiv.ext
  intro y
  change ψ.permCongr ((u : ↥K₀) : Perm Δ₀) y = a y
  rw [Equiv.permCongr_apply]
  rw [show ((u : ↥K₀) : Perm Δ₀) (ψ.symm y) = u • (ψ.symm y) from rfl]
  rw [hψ_smul u (ψ.symm y), Equiv.apply_symm_apply]
  have hu : (θ u : Perm Δ) = a :=
    congrArg Subtype.val (θ.apply_symm_apply (⟨a, ha⟩ : ↥A))
  rw [hu]

end CFSG.LocalAnalysis.WeakClosure81
