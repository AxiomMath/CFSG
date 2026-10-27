module

public import CFSG.Quasithin.MS93.S37RSmall

public section

namespace CFSG.Quasithin.MS93.S37R

open CFSG.Quasithin CFSG.Assembly.LowTwoRank CFSG.Quasithin.MS93 CFSG.Quasithin.MS93.MSP
open CFSG.QuasithinUnique CFSG.Quasithin.MS93.S36 CFSG.Quasithin.Vol2
open CFSG.Quasithin.MS93.S37 CFSG.Quasithin.MS93.S37L
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G} {F : Type} [Field F] [Fintype F]

namespace Dat

variable {C : Cfg M T L F} (D : Dat C)

omit [Fintype F] in
theorem iota_zero : iota ((0 : Fin 2 → F), (0 : F)) = 1 := by
  apply Multiplicative.toAdd.injective
  refine Prod.ext ?_ rfl
  funext i
  rcases i with i | i <;> rfl

section Big

variable (hA : ¬ Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F)
include hA

theorem rad_inj {s : F} (h : D.Ψ (iota (0, s)) = 1) : s = 0 := by
  let f : F → ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) :=
    fun k => ⟨D.Ψ (iota (0, k)), D.Ψ_rad_mem_A k⟩
  have hf : Function.Surjective f := by
    rintro ⟨a, ha⟩
    obtain ⟨w, hw⟩ := D.hs a ha.1
    have h1 : (Multiplicative.toAdd w).1 = 0 := by
      rw [← D.hβ w (D.hU w)]
      have : C.N.co ⟨a, ha.1⟩ = 0 := (C.N.co_eq_zero_iff _).2 ha
      rw [← this]
      exact congrArg C.N.co (Subtype.ext hw)
    refine ⟨(Multiplicative.toAdd w).2, Subtype.ext ?_⟩
    show D.Ψ (iota (0, (Multiplicative.toAdd w).2)) = a
    rw [← hw]
    congr 1
    apply Multiplicative.toAdd.injective
    refine Prod.ext ?_ rfl
    rw [h1]
    funext i
    rcases i with i | i <;> rfl
  have hle : Nat.card F ≤ Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) :=
    not_lt.1 hA
  have hcard : Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card F :=
    Nat.card_le_card_of_surjective f hf
  have hfi : Function.Injective f := by
    have : Nat.card F = Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) :=
      le_antisymm hle hcard
    exact (Function.Surjective.bijective_of_nat_card_le hf this.le).1
  have := hfi (show f s = f 0 from Subtype.ext (by
    show D.Ψ (iota (0, s)) = D.Ψ (iota (0, 0))
    rw [h, iota_zero, map_one]))
  exact this

theorem Ψι_inj {v w : (Fin 2 → F) × F} (h : D.Ψ (iota v) = D.Ψ (iota w)) : v = w := by
  have e : iota v = iota (v - w) * iota w := by rw [← iota_add, sub_add_cancel]
  have h1 : D.Ψ (iota (v - w)) = 1 := by
    have h2 : D.Ψ (iota (v - w)) * D.Ψ (iota w) = 1 * D.Ψ (iota w) := by
      rw [← map_mul, ← e, h, one_mul]
    exact mul_right_cancel h2
  have hfst : v.1 - w.1 = 0 := by
    have := D.hk _ h1
    funext i
    have := congrFun this (.inl i)
    simpa [iota] using this
  have hsnd : v.2 - w.2 = 0 := by
    refine D.rad_inj hA ?_
    rw [← h1]
    congr 1
    apply Multiplicative.toAdd.injective
    refine Prod.ext ?_ rfl
    show Sum.elim (0 : Fin 2 → F) (0 : Fin 2 → F) = Sum.elim (v - w).1 0
    rw [show (v - w).1 = v.1 - w.1 from rfl, hfst]
  exact Prod.ext (sub_eq_zero.1 hfst) (sub_eq_zero.1 hsnd)

end Big

omit [Fintype F] in
theorem closure_eq_top_of_good [CharP F 2] (Φ : (Fin 2 → F) → F × F × F)
    {x₁ x₂ : Fin 2 → F} (hind : x₁ 0 * x₂ 1 - x₁ 1 * x₂ 0 ≠ 0)
    (hg₁ : ∀ a, ∃ y, mv (Φ y) x₁ = a) (hg₂ : ∀ a, ∃ y, mv (Φ y) x₂ = a) :
    AddSubgroup.closure (Set.range fun p : (Fin 2 → F) × (Fin 2 → F) => lc (Φ p.2) p.1) = ⊤ := by
  refine eq_top_iff.2 fun v _ => ?_
  have hΓ : ∀ x, (∀ a, ∃ y, mv (Φ y) x = a) → ∀ a, (a, dot x a) ∈
      AddSubgroup.closure (Set.range fun p : (Fin 2 → F) × (Fin 2 → F) => lc (Φ p.2) p.1) := by
    intro x hx a
    obtain ⟨y, hy⟩ := hx a
    refine AddSubgroup.subset_closure ⟨(x, y), ?_⟩
    simp only [lc, hy, qv_eq_dot]
  have hd : x₂ - x₁ ≠ 0 := fun h => hind (by
    have := sub_eq_zero.1 h
    rw [this]; ring)
  obtain ⟨b, hb⟩ := exists_dot_eq hd (v.2 - dot x₁ v.1)
  have e : v = (v.1 - b, dot x₁ (v.1 - b)) + (b, dot x₂ b) := by
    refine Prod.ext (by simp) ?_
    simp only [Prod.snd_add]
    have : dot (x₂ - x₁) b = dot x₂ b - dot x₁ b := by
      simp only [dot, Pi.sub_apply]; ring
    rw [this] at hb
    have e2 : dot x₁ (v.1 - b) = dot x₁ v.1 - dot x₁ b := by
      simp only [dot, Pi.sub_apply]; ring
    rw [e2]
    linear_combination -hb
  rw [e]
  exact AddSubgroup.add_mem _ (hΓ x₁ hg₁ _) (hΓ x₂ hg₂ _)

variable [CharP F 2]

theorem exists_Θ (v : (Fin 2 → F) × F) : ∃ w : (Fin 2 → F) × F,
    D.Ψ (iota w) = ((D.θ ⟨D.Ψ (iota v), C.Uq_le_T1 (D.hU _)⟩ : ↥(T1 M T L)) : G) := by
  have hr : D.Ψ (iota v) ∈ C.Usub (ln₀ F) := by
    refine (C.mem_Usub).2 ⟨D.hU _, ?_⟩
    rw [D.hβ, mem_ln₀]
    exact ⟨rfl, rfl⟩
  have hθr := D.θ_mem_R₀ hr
  obtain ⟨hθU, hco⟩ := (C.mem_Usub).1 hθr
  obtain ⟨w₀, hw₀⟩ := D.hs _ hθU
  have h1 : (Multiplicative.toAdd w₀).1 = Sum.elim (fun i => C.N.co ⟨_, hθU⟩ (.inl i)) 0 := by
    rw [← eq_elim_of_mem_ln₀ hco, ← D.hβ w₀ (D.hU w₀)]
    exact congrArg C.N.co (Subtype.ext hw₀)
  refine ⟨(fun i => C.N.co ⟨_, hθU⟩ (.inl i), (Multiplicative.toAdd w₀).2), ?_⟩
  refine Eq.trans ?_ hw₀
  congr 1
  apply Multiplicative.toAdd.injective
  exact Prod.ext h1.symm rfl

@[expose] noncomputable def Θf (v : (Fin 2 → F) × F) : (Fin 2 → F) × F :=
  Classical.choose (D.exists_Θ v)

theorem Θf_spec (v : (Fin 2 → F) × F) :
    D.Ψ (iota (D.Θf v)) = ((D.θ ⟨D.Ψ (iota v), C.Uq_le_T1 (D.hU _)⟩ : ↥(T1 M T L)) : G) :=
  Classical.choose_spec (D.exists_Θ v)

section Big2

variable (hA : ¬ Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F)
include hA

theorem Θf_add (v w : (Fin 2 → F) × F) : D.Θf (v + w) = D.Θf v + D.Θf w := by
  refine D.Ψι_inj hA ?_
  rw [D.Θf_spec]
  conv_rhs => rw [iota_add, map_mul, D.Θf_spec, D.Θf_spec]
  have hx : (⟨D.Ψ (iota (v + w)), C.Uq_le_T1 (D.hU _)⟩ : ↥(T1 M T L)) =
      ⟨D.Ψ (iota v), C.Uq_le_T1 (D.hU _)⟩ * ⟨D.Ψ (iota w), C.Uq_le_T1 (D.hU _)⟩ :=
    Subtype.ext (by
      show D.Ψ (iota (v + w)) = D.Ψ (iota v) * D.Ψ (iota w)
      rw [iota_add, map_mul])
  rw [hx, map_mul]
  rfl

theorem Θf_inj {v w : (Fin 2 → F) × F} (h : D.Θf v = D.Θf w) : v = w := by
  refine D.Ψι_inj hA ?_
  have h1 := D.Θf_spec v
  rw [h, D.Θf_spec] at h1
  have := D.θ.injective (Subtype.ext h1)
  exact (congrArg Subtype.val this).symm

@[expose] noncomputable def ΘHom : (Fin 2 → F) × F →+ (Fin 2 → F) × F where
  toFun := D.Θf
  map_zero' := by
    have := D.Θf_add hA 0 0
    rw [add_zero] at this
    exact add_eq_left.1 this.symm
  map_add' := D.Θf_add hA

@[expose] noncomputable def Theta : (Fin 2 → F) × F ≃+ (Fin 2 → F) × F :=
  AddEquiv.ofBijective (D.ΘHom hA) (by
    have hinj : Function.Injective (D.ΘHom hA) := fun v w h => D.Θf_inj hA h
    exact ⟨hinj, Finite.injective_iff_surjective.1 hinj⟩)

theorem Theta_apply (v : (Fin 2 → F) × F) : D.Theta hA v = D.Θf v := rfl

end Big2

section Big3

variable (hA : ¬ Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F)
include D hA

omit [CharP F 2] hA in
theorem inv_Ψ (w : Multiplicative (V4 F × F)) : (D.Ψ w)⁻¹ = D.Ψ w := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← sq]
  exact Sp4L.uq_sq C.h (D.hU w)

theorem Theta_lc (x y : Fin 2 → F) : D.Theta hA (lc (D.Φ' x) y) = lc (D.Φ y) x := by
  refine D.Ψι_inj hA ?_
  rw [Theta_apply, D.Θf_spec]
  have e : (⟨D.Ψ (iota (lc (D.Φ' x) y)), C.Uq_le_T1 (D.hU _)⟩ : ↥(T1 M T L)) =
      ⟨⁅D.zi x, D.u y⁆, D.comm_zi_mem x y⟩ := Subtype.ext (D.comm_zi x y).symm
  rw [e, D.θ_comm_zi, ← commutatorElement_inv, D.comm_z, D.inv_Ψ]

omit [CharP F 2] hA in
theorem exists_diag : ∃ y, (D.ΦHom y).1 ≠ 0 ∨ (D.ΦHom y).2.2 ≠ 0 := by
  by_contra hcon
  push Not at hcon
  have hinj : Function.Injective (fun t : ↥D.E₃ => (t : F × F × F).2.1) := by
    rintro ⟨t, y, rfl⟩ ⟨t', y', rfl⟩ h
    apply Subtype.ext
    exact Prod.ext ((hcon y).1.trans (hcon y').1.symm)
      (Prod.ext h ((hcon y).2.trans (hcon y').2.symm))
  have h1 := Nat.card_le_card_of_injective _ hinj
  rw [D.card_E₃] at h1
  have : 1 < Nat.card F := by have := D.hq; omega
  nlinarith

theorem coc_eq_zero_big {x : G} (hx : x ∈ pCoreOf 2 M) {B : F}
    (hB : ∀ g, C.coc hx g = S5.cform B 0 g) : B = 0 := by
  have hq : 4 < Fintype.card F := by have := D.hq; rw [Nat.card_eq_fintype_card] at this; omega
  obtain ⟨x₁, x₂, hind, hg₁, hg₂⟩ := D.exists_good_pair
  set t'' := D.θ⁻¹ ⟨x, C.pCore_le_T1 hx⟩ with ht''
  set C'' := S5.q1Coord (C.rho ⟨(t'' : G), T1_le_sup t''.2⟩)
  have hBy : ∀ y, (D.Theta hA (lc C'' y)).1 = B • sd (D.ΦHom y) := by
    intro y
    have h1 := D.hβ (iota (D.Theta hA (lc C'' y))) (D.hU _)
    have e : (⟨D.Ψ (iota (lc C'' y)), C.Uq_le_T1 (D.hU _)⟩ : ↥(T1 M T L)) =
        ⁅t'', (⟨D.u y, D.u_mem_T1 y⟩ : ↥(T1 M T L))⁆ := Subtype.ext (D.comm_u t''.2 y).symm
    have hθ : ((D.θ ⁅t'', (⟨D.u y, D.u_mem_T1 y⟩ : ↥(T1 M T L))⁆ : ↥(T1 M T L)) : G) =
        (⁅D.z y, x⁆)⁻¹ := by
      rw [map_commutatorElement, ht'', MulAut.apply_inv_self, commutatorElement_inv]
      rfl
    have hco := D.co_comm_z_pCore y hx hB
    have h2 : C.N.co ⟨_, D.hU (iota (D.Theta hA (lc C'' y)))⟩ =
        Sum.elim (B • sd (D.ΦHom y)) 0 := by
      rw [show (⟨_, D.hU (iota (D.Theta hA (lc C'' y)))⟩ : ↥(Uq M T L)) =
        (⟨⁅D.z y, x⁆, (C.Usub_le _) (D.comm_z_mem_R₀ y hx)⟩ : ↥(Uq M T L))⁻¹ from
        Subtype.ext (by
          show D.Ψ (iota (D.Θf (lc C'' y))) = (⁅D.z y, x⁆)⁻¹
          rw [D.Θf_spec, e, hθ]), C.N.co_inv, hco]
      funext i
      rcases i with i | i <;> simp [CharTwo.neg_eq, D.ΦHom_apply]
    rw [h2] at h1
    funext i
    exact (congrFun h1 (.inl i)).symm
  exact eq_zero_of_scalar hq D.ΦHom D.Φ' (D.Theta hA) (fun x y => D.Theta_lc hA x y)
    (closure_eq_top_of_good _ hind hg₁ hg₂) hind hg₁ hg₂ hBy D.exists_diag

end Big3

section Big4

variable (hA : ¬ Nat.card ↥(Uq M T L ⊓ Subgroup.centralizer (L : Set G)) < Nat.card F)
include D hA

theorem tImage_D_le_big {d : G} (hd : d ∈ Dq M L) :
    ((D.θ ⟨d, C.pCore_le_T1 hd.1⟩ : ↥(T1 M T L)) : G) ∈ pCoreOf 2 M := by
  have hq : 4 < Fintype.card F := by have := D.hq; rw [Nat.card_eq_fintype_card] at this; omega
  obtain ⟨x₁, x₂, hind, hg₁, hg₂⟩ := D.exists_good_pair
  by_contra hQ
  set td := D.θ ⟨d, C.pCore_le_T1 hd.1⟩ with htd
  set C' := S5.q1Coord (C.rho ⟨(td : G), T1_le_sup td.2⟩)
  have hC' : C' ≠ 0 := fun h => hQ (by
    have h1 : C.rho ⟨(td : G), T1_le_sup td.2⟩ = 1 := by
      refine S5.q1Coord_injOn (D.rho_mem_Q₁ td.2) (Subgroup.one_mem _) ?_
      rw [q1Coord_one]
      exact h
    exact (C.rho_eq_one_iff _).1 h1)
  have hA' : ∀ x, ∃ s, lc C' x = D.Theta hA (0, s) := by
    intro x
    have hcA := D.comm_D_mem_A hd (mem_tImage.2 ⟨D.u x, D.u_mem_T1 x, D.u_mem x, rfl⟩)
    obtain ⟨w, hw⟩ := D.hs _ hcA.1
    have hw1 : (Multiplicative.toAdd w).1 = 0 := by
      rw [← D.hβ w (D.hU w)]
      have : C.N.co ⟨_, hcA.1⟩ = 0 := (C.N.co_eq_zero_iff _).2 hcA
      rw [← this]
      exact congrArg C.N.co (Subtype.ext hw)
    refine ⟨(Multiplicative.toAdd w).2, D.Ψι_inj hA ?_⟩
    rw [Theta_apply, D.Θf_spec, ← D.comm_u td.2]
    have hw' : D.Ψ (iota (0, (Multiplicative.toAdd w).2)) = ⁅d, D.zi x⁆ := by
      show _ = ⁅d, ((D.θ⁻¹ ⟨D.u x, D.u_mem_T1 x⟩ : ↥(T1 M T L)) : G)⁆
      rw [← hw]
      congr 1
      apply Multiplicative.toAdd.injective
      refine Prod.ext ?_ rfl
      rw [hw1]
      funext i
      rcases i with i | i <;> rfl
    have e : (⟨D.Ψ (iota (0, (Multiplicative.toAdd w).2)), C.Uq_le_T1 (D.hU _)⟩ :
        ↥(T1 M T L)) = ⁅(⟨d, C.pCore_le_T1 hd.1⟩ : ↥(T1 M T L)),
          D.θ⁻¹ ⟨D.u x, D.u_mem_T1 x⟩⁆ := Subtype.ext hw'
    rw [e, map_commutatorElement, MulAut.apply_inv_self]
    rfl
  exact false_of_scalar hq D.ΦHom D.Φ' (D.Theta hA) (fun x y => D.Theta_lc hA x y)
    (closure_eq_top_of_good _ hind hg₁ hg₂) hind hg₁ hg₂ hC' hA'

theorem rhoIm_eq_big : C.rhoIm (Qt M D.θ) = C.rhoIm (Ut M T L D.θ) := by
  refine D.rhoIm_eq_of (fun x hx => ?_) fun _ hd => D.tImage_D_le_big hA hd
  obtain ⟨v, hv, B, hx', hB⟩ := exists_normal_coc C hx
  have hB0 := D.coc_eq_zero_big hA hx' hB
  refine ⟨v, hv, C.mem_Dq_of_coc_eq_zero hx' fun g => ?_⟩
  rw [hB, hB0]
  simp [S5.cform]

end Big4

end Dat

end CFSG.Quasithin.MS93.S37R
