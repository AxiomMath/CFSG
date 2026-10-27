module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC4Defs
public import CFSG.LocalAnalysis.RankThreeUC.AGL81S16RankA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ClassicalGroups.Unitary CFSG.LocalAnalysis.RankThreeUC Matrix
open CFSG.LieType.Universal.Unitary (SUid)

variable {G : Type} [Group G] [Finite G]

namespace UFrame

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

@[expose] def vec (w : Vtil V₀ V hV) : Fin 4 → F.K := Multiplicative.toAdd (F.β w)

@[expose] def ofVec (x : Fin 4 → F.K) : Vtil V₀ V hV := F.β.symm (Multiplicative.ofAdd x)

@[simp] theorem ofVec_vec (w : Vtil V₀ V hV) : F.ofVec (F.vec w) = w := by
  simp [ofVec, vec]

@[simp] theorem vec_ofVec (x : Fin 4 → F.K) : F.vec (F.ofVec x) = x := by
  simp [ofVec, vec]

theorem vec_injective : Function.Injective (F.vec : Vtil V₀ V hV → Fin 4 → F.K) :=
  fun a b h => by simpa using congrArg F.ofVec h

@[simp] theorem vec_mul (a b : Vtil V₀ V hV) : F.vec (a * b) = F.vec a + F.vec b := by
  simp [vec]

@[simp] theorem vec_one : F.vec (1 : Vtil V₀ V hV) = 0 := by simp [vec]

@[simp] theorem vec_inv (a : Vtil V₀ V hV) : F.vec a⁻¹ = -F.vec a := by simp [vec]

@[simp] theorem ofVec_add (x y : Fin 4 → F.K) : F.ofVec (x + y) = F.ofVec x * F.ofVec y := by
  apply F.vec_injective
  simp

@[simp] theorem ofVec_zero : F.ofVec (0 : Fin 4 → F.K) = 1 := by
  apply F.vec_injective
  simp

theorem vec_action (γ : ↥(SUid F.σ 4)) (w : Vtil V₀ V hV) :
    F.vec ((F.π γ : MulAut (Vtil V₀ V hV)) w) = γ • F.vec w := by
  simp [vec, F.equiv]

@[expose] def Sing (w : Vtil V₀ V hV) : Prop := herm F.σ (F.vec w) (F.vec w) = 0

theorem Sing_one : F.Sing (1 : Vtil V₀ V hV) := by simp [Sing, herm]

theorem Sing_iff_sum (w : Vtil V₀ V hV) :
    F.Sing w ↔ ∑ i, F.vec w i ^ (2 ^ 1 + 1) = 0 := by
  unfold Sing herm
  simp only [pow_one, F.norm_eq]

theorem sigma_apply (c : F.K) : F.σ c = c ^ 2 := by
  by_cases hc : c = 0
  · subst hc
    simp
  · have h := F.norm_eq c
    have h3 : F.σ c * c = c ^ 2 * c := by rw [h]; ring
    exact mul_right_cancel₀ hc h3

theorem suid_eq_statedSU : SUid F.σ 4 = StatedSU 4 (2 ^ 1) F.K := by
  have hK : Nat.card F.K = (2 ^ 1) ^ 2 := by rw [F.card_K]; norm_num
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F.K 2 := charP_of_card_sq (p := 2) (f := 1) hK
  have hσ : F.σ = CFSG.LieType.BorelTits.unitaryInvolution F.K 2 1 := by
    ext c
    rw [sigma_apply, CFSG.LieType.BorelTits.unitaryInvolution_apply]
    norm_num
  rw [hσ]
  exact CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hK 4

@[expose] def rho (φ : MulAut (Vtil V₀ V hV)) : (Fin 4 → F.K) ≃+ (Fin 4 → F.K) where
  toFun x := F.vec (φ (F.ofVec x))
  invFun x := F.vec (φ⁻¹ (F.ofVec x))
  left_inv x := by simp
  right_inv x := by simp
  map_add' x y := by simp

theorem rho_vec (φ : MulAut (Vtil V₀ V hV)) (w : Vtil V₀ V hV) :
    F.rho φ (F.vec w) = F.vec (φ w) := by
  simp [rho]

theorem rho_mul (φ ψ : MulAut (Vtil V₀ V hV)) (x : Fin 4 → F.K) :
    F.rho (φ * ψ) x = F.rho φ (F.rho ψ x) := by
  simp [rho]

@[expose] def addSub (S : Subgroup (Vtil V₀ V hV)) : AddSubgroup (Fin 4 → F.K) where
  carrier := {x | F.ofVec x ∈ S}
  add_mem' {x y} hx hy := by simpa using S.mul_mem hx hy
  zero_mem' := by simpa using S.one_mem
  neg_mem' {x} hx := by
    have : F.ofVec (-x) = (F.ofVec x)⁻¹ := by
      apply F.vec_injective
      simp
    simpa [this] using S.inv_mem hx

theorem mem_addSub (S : Subgroup (Vtil V₀ V hV)) (x : Fin 4 → F.K) :
    x ∈ F.addSub S ↔ F.ofVec x ∈ S := Iff.rfl

theorem vec_mem_addSub (S : Subgroup (Vtil V₀ V hV)) (w : Vtil V₀ V hV) :
    F.vec w ∈ F.addSub S ↔ w ∈ S := by
  simp [mem_addSub]

@[expose] noncomputable def suSub (X : Subgroup (MulAut (Vtil V₀ V hV))) : Subgroup ↥(SUid F.σ 4) :=
  (X.subgroupOf (lBar V₀ V hV L)).comap F.π.toMonoidHom

theorem mem_suSub (X : Subgroup (MulAut (Vtil V₀ V hV))) (γ : ↥(SUid F.σ 4)) :
    γ ∈ F.suSub X ↔ (F.π γ : MulAut (Vtil V₀ V hV)) ∈ X := Iff.rfl

end UFrame

section Transfer

variable {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V} {L : Subgroup G}
  (F : UFrame V₀ V hV L)

theorem UFrame.card_Vtil (F : UFrame V₀ V hV L) : Nat.card (Vtil V₀ V hV) = 2 ^ 8 := by
  calc Nat.card (Vtil V₀ V hV)
      = Nat.card (Multiplicative (Fin 4 → F.K)) := Nat.card_congr F.β.toEquiv
    _ = Nat.card (Fin 4 → F.K) := Nat.card_congr Multiplicative.toAdd
    _ = Nat.card F.K ^ Nat.card (Fin 4) := Nat.card_fun
    _ = 4 ^ 4 := by rw [F.card_K, Nat.card_fin]
    _ = 2 ^ 8 := by norm_num

theorem UFrame.mem_commV_iff_commSp {X : Subgroup (MulAut (Vtil V₀ V hV))}
    (hX : X ≤ lBar V₀ V hV L) (w : Vtil V₀ V hV) :
    w ∈ commV X ↔ F.vec w ∈ commSp (F.suSub X) := by
  constructor
  · intro hw
    change w ∈ Subgroup.closure {y | ∃ x ∈ X, ∃ v : Vtil V₀ V hV, x v * v⁻¹ = y} at hw
    refine Subgroup.closure_induction (p := fun v _ => F.vec v ∈ commSp (F.suSub X))
      ?_ ?_ ?_ ?_ hw
    · rintro y ⟨x, hxX, v, rfl⟩
      obtain ⟨a, ha⟩ := F.π.surjective ⟨x, hX hxX⟩
      have haX : a ∈ F.suSub X := by
        rw [F.mem_suSub]
        simpa [ha] using hxX
      have hxeq : x = (F.π a : MulAut (Vtil V₀ V hV)) := by
        have := congrArg (fun g : ↥(lBar V₀ V hV L) => (g : MulAut (Vtil V₀ V hV))) ha
        simpa using this.symm
      rw [hxeq, F.vec_mul, F.vec_inv, F.vec_action]
      simpa [sub_eq_add_neg] using sub_mem_commSp haX (F.vec v)
    · rw [F.vec_one]
      exact (commSp (F.suSub X)).zero_mem
    · intro a b _ _ ha hb
      rw [F.vec_mul]
      exact (commSp (F.suSub X)).add_mem ha hb
    · intro a _ ha
      rw [F.vec_inv]
      exact (commSp (F.suSub X)).neg_mem ha
  · intro hw
    have key : F.ofVec (F.vec w) ∈ commV X := by
      refine Submodule.closure_induction (p := fun y _ => F.ofVec y ∈ commV X) ?_ ?_ ?_ hw
      · rw [F.ofVec_zero]
        exact Subgroup.one_mem _
      · intro x y _ _ hx hy
        rw [F.ofVec_add]
        exact Subgroup.mul_mem _ hx hy
      · intro r x hx
        obtain ⟨a, ha, z, rfl⟩ := hx
        have haX : (F.π a : MulAut (Vtil V₀ V hV)) ∈ X := (F.mem_suSub X a).1 ha
        have hscale : r • (a • z - z) = a • (r • z) - r • z := by
          rw [smul_sub, ← smul_comm a r z]
        have hkey : F.ofVec (a • (r • z) - r • z) =
            (F.π a : MulAut (Vtil V₀ V hV)) (F.ofVec (r • z)) * (F.ofVec (r • z))⁻¹ := by
          apply F.vec_injective
          simp only [F.vec_ofVec, F.vec_mul, F.vec_inv, F.vec_action, sub_eq_add_neg]
        rw [hscale, hkey]
        exact Subgroup.subset_closure
          ⟨(F.π a : MulAut (Vtil V₀ V hV)), haX, F.ofVec (r • z), rfl⟩
    simpa using key

theorem UFrame.mem_fixV_iff_fixSp {X : Subgroup (MulAut (Vtil V₀ V hV))}
    (hX : X ≤ lBar V₀ V hV L) (w : Vtil V₀ V hV) :
    w ∈ fixV X ↔ F.vec w ∈ fixSp (F.suSub X) := by
  constructor
  · intro hw a ha
    have hπ : (F.π a : MulAut (Vtil V₀ V hV)) ∈ X := (F.mem_suSub X a).1 ha
    have h := (mem_fixV (X := X) (v := w)).1 hw (F.π a) hπ
    rw [← F.vec_action a w, h]
  · intro hw x hx
    let a : ↥(SUid F.σ 4) := F.π.symm ⟨x, hX hx⟩
    have ha : a ∈ F.suSub X := by
      rw [F.mem_suSub]
      simpa [a] using hx
    have hv : a • F.vec w = F.vec w := (mem_fixSp (E := F.suSub X) (x := F.vec w)).1 hw a ha
    have hfix : (F.π a : MulAut (Vtil V₀ V hV)) w = w := by
      apply F.vec_injective
      rw [F.vec_action]
      exact hv
    simpa [a] using hfix

theorem UFrame.card_suSub {X : Subgroup (MulAut (Vtil V₀ V hV))} (hX : X ≤ lBar V₀ V hV L) :
    Nat.card (F.suSub X) = Nat.card X := by
  have h1 : Nat.card (F.suSub X) = Nat.card (X.subgroupOf (lBar V₀ V hV L)) := by
    change Nat.card ((X.subgroupOf (lBar V₀ V hV L)).comap F.π.toMonoidHom) =
      Nat.card (X.subgroupOf (lBar V₀ V hV L))
    rw [Subgroup.comap_equiv_eq_map_symm' F.π]
    exact Nat.card_congr (MulEquiv.subgroupMap F.π.symm _).symm.toEquiv
  exact h1.trans (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX).toEquiv)

theorem UFrame.suSub_sq_comm {X : Subgroup (MulAut (Vtil V₀ V hV))} (hX : X ≤ lBar V₀ V hV L)
    (hX2 : IsElemAbelian2 X) :
    (∀ a ∈ F.suSub X, a * a = 1) ∧ ∀ a ∈ F.suSub X, ∀ b ∈ F.suSub X, a * b = b * a := by
  constructor
  · intro a ha
    have hπa : (F.π a : MulAut (Vtil V₀ V hV)) ^ 2 = 1 :=
      hX2.2 (F.π a) ((F.mem_suSub X a).1 ha)
    apply F.π.injective
    rw [map_mul, map_one]
    exact Subtype.ext (by simpa [pow_two] using hπa)
  · intro a ha b hb
    have hab : (F.π a : MulAut (Vtil V₀ V hV)) * (F.π b) = (F.π b) * (F.π a) :=
      hX2.1 (F.π a) ((F.mem_suSub X a).1 ha) (F.π b) ((F.mem_suSub X b).1 hb)
    apply F.π.injective
    rw [map_mul, map_mul]
    exact Subtype.ext hab

theorem UFrame.exists_subgroup_ptCent (E : Subgroup (GL (Fin 4) F.K)) (hE : E ≤ SUid F.σ 4)
    (x : Fin 4 → F.K)
    (hfix : ∀ g ∈ E, ((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ x = x) :
    ∃ E' : Subgroup (MulAut (Vtil V₀ V hV)), E' ≤ ptCent (lBar V₀ V hV L) (F.ofVec x) ∧
      Nonempty (↥E ≃* ↥E') := by
  let E₁ : Subgroup ↥(SUid F.σ 4) := E.subgroupOf (SUid F.σ 4)
  let E' : Subgroup (MulAut (Vtil V₀ V hV)) :=
    (E₁.map F.π.toMonoidHom).map (lBar V₀ V hV L).subtype
  refine ⟨E', ?_, ?_⟩
  · refine le_inf ?_ ?_
    · exact Subgroup.map_subtype_le _
    · intro φ hφ
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      change φ ∈ (E₁.map F.π.toMonoidHom).map (lBar V₀ V hV L).subtype at hφ
      simp only [Subgroup.mem_map] at hφ
      obtain ⟨ψ, hψ, rfl⟩ := hφ
      obtain ⟨γ, hγ, rfl⟩ := hψ
      apply F.vec_injective
      change F.vec ((F.π γ : MulAut (Vtil V₀ V hV)) (F.ofVec x)) = F.vec (F.ofVec x)
      rw [F.vec_action, F.vec_ofVec]
      have hγE : (γ : GL (Fin 4) F.K) ∈ E := (Subgroup.mem_subgroupOf).1 hγ
      have hfx := hfix (γ : GL (Fin 4) F.K) hγE
      rw [CFSG.ClassicalGroups.Unitary.smul_def, hfx]
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hE).symm.trans
      ((Subgroup.equivMapOfInjective E₁ F.π.toMonoidHom F.π.injective).trans
        (Subgroup.equivMapOfInjective (E₁.map F.π.toMonoidHom) (lBar V₀ V hV L).subtype
          (Subgroup.subtype_injective _)))⟩

theorem UFrame.exists_subgroup_normalizer (E : Subgroup (GL (Fin 4) F.K)) (hE : E ≤ SUid F.σ 4)
    (S : Subgroup (Vtil V₀ V hV))
    (hstab : ∀ g ∈ E, ∀ x ∈ F.addSub S,
      ((g : GL (Fin 4) F.K) : Matrix (Fin 4) (Fin 4) F.K) *ᵥ x ∈ F.addSub S) :
    ∃ E' : Subgroup (MulAut (Vtil V₀ V hV)), E' ≤ lBar V₀ V hV L ∧
      (∀ φ ∈ E', ∀ w ∈ S, φ w ∈ S) ∧ Nonempty (↥E ≃* ↥E') := by
  let E₁ : Subgroup ↥(SUid F.σ 4) := E.subgroupOf (SUid F.σ 4)
  let E' : Subgroup (MulAut (Vtil V₀ V hV)) :=
    (E₁.map F.π.toMonoidHom).map (lBar V₀ V hV L).subtype
  refine ⟨E', Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro φ hφ w hw
    change φ ∈ (E₁.map F.π.toMonoidHom).map (lBar V₀ V hV L).subtype at hφ
    simp only [Subgroup.mem_map] at hφ
    obtain ⟨ψ, hψ, rfl⟩ := hφ
    obtain ⟨γ, hγ, rfl⟩ := hψ
    have hγE : (γ : GL (Fin 4) F.K) ∈ E := (Subgroup.mem_subgroupOf).1 hγ
    have hv : F.vec w ∈ F.addSub S := (F.vec_mem_addSub S w).2 hw
    have hsm := hstab (γ : GL (Fin 4) F.K) hγE (F.vec w) hv
    apply (F.vec_mem_addSub S ((F.π γ : MulAut (Vtil V₀ V hV)) w)).1
    rw [F.vec_action]
    simpa [CFSG.ClassicalGroups.Unitary.smul_def] using hsm
  · exact ⟨(Subgroup.subgroupOfEquivOfLe hE).symm.trans
      ((Subgroup.equivMapOfInjective E₁ F.π.toMonoidHom F.π.injective).trans
        (Subgroup.equivMapOfInjective (E₁.map F.π.toMonoidHom) (lBar V₀ V hV L).subtype
          (Subgroup.subtype_injective _)))⟩

end Transfer

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
