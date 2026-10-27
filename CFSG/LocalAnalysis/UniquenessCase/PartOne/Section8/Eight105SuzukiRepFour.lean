module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105SuzukiRepSmall
import CFSG.LieType.TwoRank.PGLFour
import CFSG.Adapters.StatedPSLTwo
import CFSG.RankThree.PartTwo.Sec20.Item20Res11ProofKO3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2

open Subgroup
open CFSG.GH74.Uniqueness.Hering (centralInvolutions conj_mem_centralInvolutions)
open scoped MatrixGroups

theorem card_le_sixteen_of_quotient {L : Type*} [Field L] (h2 : (2 : L) ≠ 0) {V : Type*}
    [AddCommGroup V] [Module L V] [FiniteDimensional L V] (hV : Module.finrank L V = 4)
    {M : Subgroup ((Module.End L V)ˣ ⧸ center (Module.End L V)ˣ)}
    (hMc : ∀ x ∈ M, ∀ y ∈ M, x * y = y * x) (hM2 : ∀ x ∈ M, x ^ 2 = 1) : Nat.card M ≤ 16 := by
  classical
  let b := Module.finBasisOfFinrankEq L V hV
  let e : (Module.End L V)ˣ ≃* GL (Fin 4) L :=
    Units.mapEquiv (LinearMap.toMatrixAlgEquiv b).toMulEquiv
  let ψ : (Module.End L V)ˣ ⧸ center (Module.End L V)ˣ ≃* Matrix.ProjGenLinGroup (Fin 4) L :=
    QuotientGroup.congr (center (Module.End L V)ˣ) (center (GL (Fin 4) L)) e
      (Subgroup.map_center_eq e)
  let A : Subgroup (Matrix.ProjGenLinGroup (Fin 4) L) := M.map ψ.toMonoidHom
  have : CFSG.IsElementaryAbelian 2 A :=
    { is_comm := ⟨fun x y => by
        obtain ⟨x, ⟨a, ha, rfl⟩⟩ := x
        obtain ⟨y, ⟨c, hc, rfl⟩⟩ := y
        exact Subtype.ext (by simp only [Subgroup.coe_mul, ← map_mul, hMc a ha c hc])⟩
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
        obtain ⟨x, ⟨a, ha, rfl⟩⟩ := x
        exact Subtype.ext (by simp only [Subgroup.coe_pow, ← map_pow, hM2 a ha, map_one,
          Subgroup.coe_one]) }
  have hL : ringChar L ≠ 2 := fun h => h2 (by
    have := ringChar.Nat.cast_ringChar (R := L)
    rw [h] at this
    exact_mod_cast this)
  have h := CFSG.LieType.TwoRank.card_le_sixteen_of_isElementaryAbelian_pgl_four hL
    (Fintype.card_fin 4) A
  rwa [show Nat.card A = Nat.card M from Subgroup.card_map_of_injective ψ.injective] at h

section Four


variable {K : Type} [Group K] [Finite K] [Group.IsPerfect K] {m : ℕ}
  {L : Type*} [Field L] [IsAlgClosed L]

theorem rep_eq_one_of_finrank_le_four (hL : UC22.IsL2 (K ⧸ CFSG.pCore 2 K) m) (hm : 4 ≤ m)
    (h2 : (2 : L) ≠ 0) {V : Type*} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (hV : Module.finrank L V ≤ 4) (ρ : Representation L K V) : ρ = 1 := by
  rcases Nat.lt_or_ge (Module.finrank L V) 4 with h4 | h4
  · exact rep_eq_one_of_finrank_le_three hL hm h2 (by omega) ρ
  have hV4 : Module.finrank L V = 4 := by omega
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ hV4
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : IsSimpleGroup (K ⧸ CFSG.pCore 2 K) := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL
  have hnd := not_card_dvd_20160_of_isL2 hL hm
  set ρu := ρ.asGroupHom with hρu
  set Z := center (Module.End L V)ˣ with hZ
  set π := QuotientGroup.mk' Z with hπ
  set Nb : Subgroup ((Module.End L V)ˣ ⧸ Z) := (CFSG.pCore 2 K).map (π.comp ρu) with hNb
  by_cases hNb1 : Nb = ⊥
  · refine rep_eq_one_of_pCore_center hL hm h2 hV ρ fun o ho => ?_
    have h1 : (π.comp ρu) o ∈ Nb := Subgroup.mem_map_of_mem _ ho
    rw [hNb1, Subgroup.mem_bot, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at h1
    exact h1
  have hNbp : IsPGroup 2 Nb := CFSG.pCore_isPGroup.map (π.comp ρu)
  have : Finite Nb := Finite.of_surjective
    (fun o : CFSG.pCore 2 K => (⟨(π.comp ρu) o, Subgroup.mem_map_of_mem _ o.2⟩ : Nb))
    (by rintro ⟨_, o, ho, rfl⟩; exact ⟨⟨o, ho⟩, rfl⟩)
  obtain ⟨xb, hxM, hx1⟩ := exists_mem_centralInvolutions hNbp hNb1
  have hnorm : ∀ k, (π.comp ρu) k ∈ normalizer (Nb : Set ((Module.End L V)ˣ ⧸ Z)) := fun k =>
    Subgroup.le_normalizer_map (π.comp ρu)
      ⟨k, by rw [Subgroup.normalizer_eq_top]; exact Subgroup.mem_top k, rfl⟩
  have hMn : ∀ (k : K), ∀ x ∈ centralInvolutions Nb,
      (π.comp ρu) k * x * ((π.comp ρu) k)⁻¹ ∈ centralInvolutions Nb := fun k x hx =>
    conj_mem_centralInvolutions (hnorm k) hx
  have hMN : centralInvolutions Nb ≤ Nb := fun _ hx => hx.1
  have hMc : ∀ x ∈ centralInvolutions Nb, ∀ y ∈ centralInvolutions Nb, x * y = y * x :=
    fun _ hx y hy => hx.2.1 y hy.1
  have hM2 : ∀ x ∈ centralInvolutions Nb, x ^ 2 = 1 := fun _ hx => hx.2.2
  have : Finite (centralInvolutions Nb) :=
    Finite.of_injective _ (Subgroup.inclusion_injective hMN)
  have hcard : Nat.card (centralInvolutions Nb) ≤ 16 := card_le_sixteen_of_quotient h2 hV4 hMc hM2
  have hfix := conj_eq_of_elementary hS hnd (π.comp ρu) hMc hM2 hcard hMn
  obtain ⟨o, ho, hox⟩ := hMN hxM
  set z := ρu o with hz
  have hcz : ∀ k, ρu k * z * (ρu k)⁻¹ * z⁻¹ ∈ Z := fun k => by
    have h := hfix k hxM
    rw [← hox, MonoidHom.comp_apply, MonoidHom.comp_apply] at h
    have h' : π (ρu k * z * (ρu k)⁻¹ * z⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, h, mul_inv_cancel]
    rwa [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
  let φ : K →* Z :=
    { toFun := fun k => ⟨ρu k * z * (ρu k)⁻¹ * z⁻¹, hcz k⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by
        have hb := Subgroup.mem_center_iff.mp (hcz b)
        change ρu (a * b) * z * (ρu (a * b))⁻¹ * z⁻¹ =
          (ρu a * z * (ρu a)⁻¹ * z⁻¹) * (ρu b * z * (ρu b)⁻¹ * z⁻¹)
        have hb' := hb (ρu a * z * (ρu a)⁻¹ * z⁻¹)
        rw [hb']
        calc ρu (a * b) * z * (ρu (a * b))⁻¹ * z⁻¹
            = ρu a * ((ρu b * z * (ρu b)⁻¹ * z⁻¹) * z) * (ρu a)⁻¹ * z⁻¹ := by
              rw [map_mul]; group
          _ = (ρu b * z * (ρu b)⁻¹ * z⁻¹) * (ρu a * z * (ρu a)⁻¹ * z⁻¹) := by
              have hb2 := hb (ρu a)
              calc ρu a * ((ρu b * z * (ρu b)⁻¹ * z⁻¹) * z) * (ρu a)⁻¹ * z⁻¹
                  = (ρu a * (ρu b * z * (ρu b)⁻¹ * z⁻¹)) * z * (ρu a)⁻¹ * z⁻¹ := by group
                _ = ((ρu b * z * (ρu b)⁻¹ * z⁻¹) * ρu a) * z * (ρu a)⁻¹ * z⁻¹ := by rw [hb2]
                _ = (ρu b * z * (ρu b)⁻¹ * z⁻¹) * (ρu a * z * (ρu a)⁻¹ * z⁻¹) := by group) }
  have hφ := CFSG.RankThree.PartTwo.Sec20.Res11.eq_one_of_commute_image φ
    (fun a b => Subtype.ext (by
      simp only [Subgroup.coe_mul]
      exact Subgroup.mem_center_iff.mp (φ b).2 (φ a)))
  have hzK : ∀ k, Commute (ρ k) (z : Module.End L V) := fun k => by
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hφ k)
    change ρu k * z * (ρu k)⁻¹ * z⁻¹ = 1 at h1
    have h' : ρu k * z = z * ρu k := by
      calc ρu k * z = (ρu k * z * (ρu k)⁻¹ * z⁻¹) * z * ρu k := by group
        _ = z * ρu k := by rw [h1, one_mul]
    have := congrArg Units.val h'
    simpa [hρu, Representation.asGroupHom_apply, Commute, SemiconjBy] using this
  obtain ⟨a, ha⟩ := CFSG.pCore_isPGroup (p := 2) (G := K) ⟨o, ho⟩
  have hza : (z : Module.End L V) ^ 2 ^ a = 1 := by
    have h1 : o ^ 2 ^ a = 1 := by simpa using congrArg Subtype.val ha
    have := congrArg Units.val (show z ^ 2 ^ a = 1 by rw [hz, ← map_pow, h1, map_one])
    simpa using this
  have hzs : ∀ c : L, (z : Module.End L V) ≠ algebraMap L (Module.End L V) c := by
    intro c hc
    apply hx1
    have hzZ : z ∈ Z := Subgroup.mem_center_iff.mpr fun g => Units.ext (by
      rw [Units.val_mul, Units.val_mul, hc]
      exact (Algebra.commutes c (g : Module.End L V)).symm)
    rw [← hox, MonoidHom.comp_apply, ← hz, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hzZ
  obtain ⟨W₁, W₂, hc, hW₁, hW₂, hi₁, hi₂⟩ :=
    exists_isCompl_of_commute hzK (N := 2 ^ a) (by exact_mod_cast pow_ne_zero a h2) hza hzs
  refine eq_one_of_isCompl_of_ih (fun W hW ρ' => ?_) hc hW₁ hW₂ hi₁ hi₂
  exact rep_eq_one_of_finrank_le_three hL hm h2 (by
    have := Submodule.finrank_lt hW
    omega) ρ'

end Four

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2
