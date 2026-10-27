module

public import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesPlan2
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesElem
import CFSG.RankThree.PartTwo.Sec13.RonanStep131bM12MovesLift

public section

namespace CFSG.RankThree.PartTwo.Sec13.RonanStep131b

theorem pow_three_mem_of_commutator_mem {G : Type} [Group G] {Θ : Subgroup G} {x y : G}
    (hx : x ∈ Subgroup.normalizer (Θ : Set G)) (hy : y ∈ Subgroup.normalizer (Θ : Set G))
    (hx3 : x ^ 3 ∈ Θ) (hy3 : y ^ 3 ∈ Θ) (hxy : x * y * x⁻¹ * y⁻¹ ∈ Θ) : (x * y) ^ 3 ∈ Θ := by
  have hconj : ∀ g ∈ Subgroup.normalizer (Θ : Set G), ∀ u ∈ Θ, g * u * g⁻¹ ∈ Θ :=
    fun g hg u hu => (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have e : (x * y) ^ 3 = (x * (x * y * x⁻¹ * y⁻¹)⁻¹ * x⁻¹) *
      ((x * x) * (y * (x * y * x⁻¹ * y⁻¹)⁻¹ * y⁻¹) * (x * x)⁻¹) *
      ((x * x) * (x * y * x⁻¹ * y⁻¹)⁻¹ * (x * x)⁻¹) * (x ^ 3 * y ^ 3) := by
    rw [pow_three' (x * y), pow_three' x, pow_three' y]
    group
  rw [e]
  have hxx : x * x ∈ Subgroup.normalizer (Θ : Set G) := mul_mem hx hx
  exact mul_mem (mul_mem (mul_mem (hconj x hx _ (inv_mem hxy))
    (hconj _ hxx _ (hconj y hy _ (inv_mem hxy)))) (hconj _ hxx _ (inv_mem hxy)))
    (mul_mem hx3 hy3)

theorem normalizer_sup_of_comm {G : Type} [Group G] [Finite G] {Θ E : Subgroup G} {c u : G}
    (hcE : c ∈ E)
    (hu : u ∈ Subgroup.normalizer (Θ : Set G))
    (hE : ∀ e ∈ E, u * e * u⁻¹ * e⁻¹ ∈ Subgroup.zpowers c ⊔ Θ) :
    u ∈ Subgroup.normalizer ((E ⊔ Θ : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hle : E ⊔ Θ ≤ (E ⊔ Θ).comap (MulAut.conj u).toMonoidHom := by
    refine sup_le (fun e he => ?_) (fun θ hθ => ?_)
    · change u * e * u⁻¹ ∈ E ⊔ Θ
      have h := hE e he
      have h2 : u * e * u⁻¹ = (u * e * u⁻¹ * e⁻¹) * e := by group
      rw [h2]
      exact mul_mem (sup_le_sup_right (Subgroup.zpowers_le.mpr hcE) Θ h) (Subgroup.mem_sup_left he)
    · change u * θ * u⁻¹ ∈ E ⊔ Θ
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hu θ).mp hθ)
  exact hle hx

theorem conj_mem_zpowers_sup {G : Type} [Group G] {Θ : Subgroup G} {c u : G}
    (hu : u ∈ Subgroup.normalizer (Θ : Set G))
    (hc : u * c * u⁻¹ * c⁻¹ ∈ Subgroup.zpowers c ⊔ Θ) {z : G}
    (hz : z ∈ Subgroup.zpowers c ⊔ Θ) : u * z * u⁻¹ ∈ Subgroup.zpowers c ⊔ Θ := by
  have hle : Subgroup.zpowers c ⊔ Θ ≤
      (Subgroup.zpowers c ⊔ Θ).comap (MulAut.conj u).toMonoidHom := by
    refine sup_le (fun z hz => ?_) (fun θ hθ => ?_)
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      change u * c ^ k * u⁻¹ ∈ Subgroup.zpowers c ⊔ Θ
      have h1 : u * c * u⁻¹ ∈ Subgroup.zpowers c ⊔ Θ := by
        have h2 : u * c * u⁻¹ = (u * c * u⁻¹ * c⁻¹) * c := by group
        rw [h2]
        exact mul_mem hc (Subgroup.mem_sup_left (Subgroup.mem_zpowers c))
      have h3 : u * c ^ k * u⁻¹ = (u * c * u⁻¹) ^ k := conj_zpow.symm
      rw [h3]
      exact zpow_mem h1 k
    · change u * θ * u⁻¹ ∈ Subgroup.zpowers c ⊔ Θ
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hu θ).mp hθ)
  exact hle hz

theorem s2d_of_lift : S2d := by
  have hlift := s2lift_holds
  intro G _ _ Θ E b c v v' hΘ3 hEe hcE hbE hEN hvN hv'N hv3 hv'3 hvv' hEv hEv' hb hnot
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE3 : IsPGroup 3 E := fun g => ⟨1, Subtype.ext (by simpa using hEe.2 g g.2)⟩
  have hconj : ∀ g ∈ Subgroup.normalizer (Θ : Set G), ∀ u ∈ Θ, g * u * g⁻¹ ∈ Θ :=
    fun g hg u hu => (Subgroup.mem_normalizer_iff.mp hg u).mp hu
  have hcN : c ∈ Subgroup.normalizer (Θ : Set G) := hEN hcE
  have hEΘbot : ∀ x ∈ E, x ∈ Θ → x = 1 := by
    intro x hxE hxΘ
    obtain ⟨k, hk⟩ := hE3 ⟨x, hxE⟩
    exact eq_one_of_mem_of_pow_three_pow hΘ3 hxΘ (by simpa using congrArg Subtype.val hk)
  have hEZ : ∀ x ∈ E, x ∈ Subgroup.zpowers c ⊔ Θ → x ∈ Subgroup.zpowers c := by
    intro x hxE hxZ
    rw [sup_comm] at hxZ
    obtain ⟨θ, hθ, y, hy, hxy⟩ := exists_mul_of_mem_sup
      (Subgroup.zpowers_le.mpr hcN) hxZ
    have hyE : y ∈ E := (Subgroup.zpowers_le.mpr hcE) hy
    have hθE : θ ∈ E := by
      have : θ = x * y⁻¹ := by rw [hxy]; group
      rw [this]
      exact mul_mem hxE (inv_mem hyE)
    have hθ1 := hEΘbot θ hθE hθ
    rw [hxy, hθ1, one_mul]
    exact hy
  have hvM := normalizer_sup_of_comm hcE hvN hEv
  have hv'M := normalizer_sup_of_comm hcE hv'N hEv'
  have hρ'M : v * v' ∈ Subgroup.normalizer ((E ⊔ Θ : Subgroup G) : Set G) := mul_mem hvM hv'M
  have hρ'N : v * v' ∈ Subgroup.normalizer (Θ : Set G) := mul_mem hvN hv'N
  have hρ'3 : (v * v') ^ 3 ∈ Θ := pow_three_mem_of_commutator_mem hvN hv'N hv3 hv'3 hvv'
  obtain ⟨ρ, hρΘ, hρ3, hρE⟩ := hlift G Θ E (v * v') hΘ3 hE3 hEN hρ'N hρ'M hρ'3
  have hρw : ρ = (v * v') * ((v * v')⁻¹ * ρ) := by group
  have hcommρ : ∀ e : G, ρ * e * ρ⁻¹ * e⁻¹ =
      ((v * v') * (((v * v')⁻¹ * ρ) * (e * ((v * v')⁻¹ * ρ)⁻¹ * e⁻¹)) * (v * v')⁻¹) *
        ((v * v') * e * (v * v')⁻¹ * e⁻¹) := by
    intro e
    conv_lhs => rw [hρw]
    group
  have hw : (v * v')⁻¹ * ρ ∈ Θ := hρΘ
  have hΘ1 : ∀ e ∈ E, ((v * v') * (((v * v')⁻¹ * ρ) * (e * ((v * v')⁻¹ * ρ)⁻¹ * e⁻¹)) *
      (v * v')⁻¹) ∈ Θ := by
    intro e he
    have h1 : e * ((v * v')⁻¹ * ρ)⁻¹ * e⁻¹ ∈ Θ :=
      (Subgroup.mem_normalizer_iff.mp (hEN he) _).mp (inv_mem hw)
    exact hconj _ hρ'N _ (mul_mem hw h1)
  refine ⟨ρ, hρΘ, hρ3, hρE, ?_, ?_, ?_⟩
  ·
    have h1 : ρ * b * ρ⁻¹ * b⁻¹ ∈ Θ := by
      rw [hcommρ b]
      exact mul_mem (hΘ1 b hbE) hb
    have h2 : ρ * b * ρ⁻¹ * b⁻¹ ∈ E :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hρE b).mp hbE) (inv_mem hbE)
    have h3 := hEΘbot _ h2 h1
    calc ρ * b = (ρ * b * ρ⁻¹ * b⁻¹) * (b * ρ) := by group
      _ = b * ρ := by rw [h3, one_mul]
  ·
    intro hρE'
    apply hnot
    have : v * v' = ρ * ((v * v')⁻¹ * ρ)⁻¹ := by group
    rw [this]
    exact mul_mem (Subgroup.mem_sup_left hρE') (Subgroup.mem_sup_right (inv_mem hw))
  ·
    intro e he
    have hZmem : ρ * e * ρ⁻¹ * e⁻¹ ∈ Subgroup.zpowers c ⊔ Θ := by
      rw [hcommρ e]
      have h1 : (v * v') * e * (v * v')⁻¹ * e⁻¹ ∈ Subgroup.zpowers c ⊔ Θ := by
        have h2 : (v * v') * e * (v * v')⁻¹ * e⁻¹ =
            (v * (v' * e * v'⁻¹ * e⁻¹) * v⁻¹) * (v * e * v⁻¹ * e⁻¹) := by group
        rw [h2]
        exact mul_mem (conj_mem_zpowers_sup hvN (hEv c hcE) (hEv' e he)) (hEv e he)
      exact mul_mem (Subgroup.mem_sup_right (hΘ1 e he)) h1
    have hEmem : ρ * e * ρ⁻¹ * e⁻¹ ∈ E :=
      mul_mem ((Subgroup.mem_normalizer_iff.mp hρE e).mp he) (inv_mem he)
    exact hEZ _ hEmem hZmem

end CFSG.RankThree.PartTwo.Sec13.RonanStep131b
