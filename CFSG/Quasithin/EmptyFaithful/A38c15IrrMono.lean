module

public import CFSG.RankThree.SubgroupLists.CliffordPrime
public import Mathlib.GroupTheory.Solvable
import Mathlib.GroupTheory.SpecificGroups.Alternating.Simple

public section

namespace CFSG.Quasithin.A38c15

open Matrix CFSG.RankThree.SubgroupLists

section Lines

variable {K : Type*} [Field K] {n : ℕ}

theorem monoLines_injective {L : Fin n → Submodule K (Fin n → K)} (hL : DirectSum.IsInternal L)
    (hrk : ∀ i, Module.finrank K (L i) = 1) : Function.Injective L := by
  refine hL.submodule_iSupIndep.injective fun i hi => ?_
  have h1 := hrk i
  rw [hi, finrank_bot] at h1
  exact zero_ne_one h1

theorem monoLine_exists_smul {V : Type*} [AddCommGroup V] [Module K V]
    {W : Submodule K V} (hW : Module.finrank K W = 1) {f : V →ₗ[K] V}
    (hf : ∀ x ∈ W, f x ∈ W) : ∃ c : K, ∀ x ∈ W, f x = c • x := by
  obtain ⟨v, -, hv⟩ := finrank_eq_one_iff'.mp hW
  obtain ⟨c, hc⟩ := hv ⟨f v, hf v v.2⟩
  refine ⟨c, fun x hx => ?_⟩
  obtain ⟨d, hd⟩ := hv ⟨x, hx⟩
  have hx' : x = d • (v : V) := (congrArg Subtype.val hd).symm
  have hfv : f v = c • (v : V) := (congrArg Subtype.val hc).symm
  rw [hx', map_smul, hfv, smul_comm]

theorem mono_mul_comm_of_translate_eq {L : Fin n → Submodule K (Fin n → K)}
    (hL : DirectSum.IsInternal L) (hrk : ∀ i, Module.finrank K (L i) = 1)
    {a b : GL (Fin n) K} (ha : ∀ i, translate a (L i) = L i) (hb : ∀ i, translate b (L i) = L i) :
    a * b = b * a := by
  have key : ∀ i, ∀ x ∈ L i, ((a * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
      ((b * a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x := by
    intro i x hx
    obtain ⟨α, hα⟩ := monoLine_exists_smul (hrk i)
      (f := Matrix.toLin' (a : Matrix (Fin n) (Fin n) K)) fun y hy => by
        have := mulVec_mem_translate (g := a) hy
        rwa [ha i] at this
    obtain ⟨β, hβ⟩ := monoLine_exists_smul (hrk i)
      (f := Matrix.toLin' (b : Matrix (Fin n) (Fin n) K)) fun y hy => by
        have := mulVec_mem_translate (g := b) hy
        rwa [hb i] at this
    have h1 : (a : Matrix (Fin n) (Fin n) K) *ᵥ x = α • x := by
      simpa [Matrix.toLin'_apply] using hα x hx
    have h2 : (b : Matrix (Fin n) (Fin n) K) *ᵥ x = β • x := by
      simpa [Matrix.toLin'_apply] using hβ x hx
    rw [gl_mulVec_mul, gl_mulVec_mul, h2, h1, Matrix.mulVec_smul, Matrix.mulVec_smul, h1, h2,
      smul_comm]
  have hall : ∀ x : Fin n → K, ((a * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
      ((b * a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x := by
    intro x
    have hx : x ∈ ⨆ i, L i := by
      rw [hL.submodule_iSup_eq_top]
      trivial
    refine Submodule.iSup_induction L (motive := fun x =>
      ((a * b : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x =
        ((b * a : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) *ᵥ x) hx key (by simp) ?_
    intro y z hy hz
    rw [Matrix.mulVec_add, Matrix.mulVec_add, hy, hz]
  exact Units.ext (Matrix.ext_iff_mulVec.mpr hall)

end Lines

section Action

variable {K : Type*} [Field K] {n : ℕ} {G : Subgroup (GL (Fin n) K)}
  {L : Fin n → Submodule K (Fin n → K)}

noncomputable def monoLineIdx (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) (g : G)
    (i : Fin n) : Fin n :=
  Classical.choose (hperm g g.2 i)

theorem translate_monoLineIdx (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) (g : G)
    (i : Fin n) : translate (g : GL (Fin n) K) (L i) = L (monoLineIdx hperm g i) :=
  Classical.choose_spec (hperm g g.2 i)

theorem monoLineIdx_one (hL : Function.Injective L)
    (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) (i : Fin n) :
    monoLineIdx hperm 1 i = i := by
  apply hL
  rw [← translate_monoLineIdx hperm, OneMemClass.coe_one, translate_one]

theorem monoLineIdx_mul (hL : Function.Injective L)
    (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) (g h : G) (i : Fin n) :
    monoLineIdx hperm (g * h) i = monoLineIdx hperm g (monoLineIdx hperm h i) := by
  apply hL
  rw [← translate_monoLineIdx hperm, ← translate_monoLineIdx hperm,
    ← translate_monoLineIdx hperm, Subgroup.coe_mul, translate_mul]

noncomputable def monoLinePerm (hL : Function.Injective L)
    (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) (g : G) : Equiv.Perm (Fin n) where
  toFun := monoLineIdx hperm g
  invFun := monoLineIdx hperm g⁻¹
  left_inv i := by
    rw [← monoLineIdx_mul hL hperm, inv_mul_cancel, monoLineIdx_one hL hperm]
  right_inv i := by
    rw [← monoLineIdx_mul hL hperm, mul_inv_cancel, monoLineIdx_one hL hperm]

noncomputable def monoLineHom (hL : Function.Injective L)
    (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) : G →* Equiv.Perm (Fin n) where
  toFun := monoLinePerm hL hperm
  map_one' := Equiv.ext fun i => monoLineIdx_one hL hperm i
  map_mul' g h := Equiv.ext fun i => monoLineIdx_mul hL hperm g h i

theorem translate_monoLineHom (hL : Function.Injective L)
    (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) (g : G) (i : Fin n) :
    translate (g : GL (Fin n) K) (L i) = L (monoLineHom hL hperm g i) :=
  translate_monoLineIdx hperm g i

theorem translate_eq_of_mem_monoLineHom_ker (hL : Function.Injective L)
    (hperm : ∀ g ∈ G, ∀ i, ∃ j, translate g (L i) = L j) {g : G}
    (hg : g ∈ (monoLineHom hL hperm).ker) (i : Fin n) :
    translate (g : GL (Fin n) K) (L i) = L i := by
  rw [translate_monoLineHom hL hperm g i, MonoidHom.mem_ker.mp hg]
  rfl

end Action

theorem isSolvable_of_isTransitiveMonomial {K : Type*} [Field K]
    {G : Subgroup (GL (Fin 3) K)} (h : IsTransitiveMonomial G) :
    Group.IsSolvable ↥G := by
  obtain ⟨L, hL, hrk, hperm, -⟩ := h
  have hinj := monoLines_injective hL hrk
  have hcomm : ∀ a b : ↥(monoLineHom hinj hperm).ker, a * b = b * a := fun a b =>
    Subtype.ext (Subtype.ext (mono_mul_comm_of_translate_eq hL hrk
      (translate_eq_of_mem_monoLineHom_ker hinj hperm a.2)
      (translate_eq_of_mem_monoLineHom_ker hinj hperm b.2)))
  have : Group.IsSolvable ↥(monoLineHom hinj hperm).ker := Group.isSolvable_of_comm hcomm
  have : Group.IsSolvable (Equiv.Perm (Fin 3)) := Equiv.Perm.isSolvable (by simp)
  exact Group.isSolvable_of_ker_le_range (monoLineHom hinj hperm).ker.subtype
    (monoLineHom hinj hperm) (Subgroup.range_subtype _).ge

end CFSG.Quasithin.A38c15
