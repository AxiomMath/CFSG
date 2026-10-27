module

public import CFSG.Quasithin.Background.A1cModuleHomog

public section

namespace CFSG.Quasithin.H13.T326

open CFSG.Quasithin
open scoped Pointwise

variable {W : Type} [CommGroup W]

theorem mem_modFix_of_normalizer {X : Subgroup (MulAut W)} {z : MulAut W}
    (hz : z ∈ Subgroup.normalizer (X : Set (MulAut W))) {w : W}
    (hw : w ∈ modFix X (⊤ : Subgroup W)) : z w ∈ modFix X (⊤ : Subgroup W) := by
  refine ⟨trivial, fun a => ?_⟩
  have hb : z⁻¹ * (a : MulAut W) * z ∈ X :=
    (Subgroup.mem_normalizer_iff''.mp hz _).mp a.2
  have h1 : (z⁻¹ * (a : MulAut W) * z) w = w := hw.2 ⟨_, hb⟩
  show (a : MulAut W) (z w) = z w
  calc (a : MulAut W) (z w) = z ((z⁻¹ * (a : MulAut W) * z) w) := by
        simp only [MulAut.mul_apply, MulAut.apply_inv_self]
    _ = z w := by rw [h1]

theorem map_eq_self_of_comm [Finite W] {X Y : Subgroup (MulAut W)}
    (hYX : Y ≤ Subgroup.normalizer (X : Set (MulAut W))) {I : Subgroup W}
    (hI : I ∈ IrrPlusOn X (⊤ : Subgroup W) Y) {n z : MulAut W} (hn : n ∈ Y)
    (hz : z ∈ Subgroup.normalizer (X : Set (MulAut W)))
    (hcomm : ∀ a ∈ X, ∀ v ∈ I, z (a v) = a (z v))
    (hnz : I.map n.toMonoidHom = I.map z.toMonoidHom) :
    I.map n.toMonoidHom = I := by
  have hW : ∀ t ∈ Y, ∀ w ∈ (⊤ : Subgroup W), t • w ∈ (⊤ : Subgroup W) :=
    fun _ _ _ _ => trivial
  have key := (forall_smul_eq_iff_mem_irrPlusOn hYX hW hI.1).2 hI
  refine key n ⟨hn, ?_⟩
  set F := modFix X (⊤ : Subgroup W) with hF
  have hFz : F ≤ F.comap z.toMonoidHom := fun w hw => mem_modFix_of_normalizer hz hw
  set zQ := QuotientGroup.map F F z.toMonoidHom hFz with hzQ
  have hzQmk : ∀ w : W, zQ (QuotientGroup.mk w) = QuotientGroup.mk (z w) := fun w => rfl
  have hinj : Function.Injective zQ := by
    rw [injective_iff_map_eq_one]
    intro q hq
    induction q using QuotientGroup.induction_on with
    | H w =>
      rw [hzQmk, QuotientGroup.eq_one_iff] at hq
      have h1 := mem_modFix_of_normalizer (Subgroup.inv_mem _ hz) hq
      rw [MulAut.inv_apply_self] at h1
      exact (QuotientGroup.eq_one_iff w).mpr h1
  have hmap : (tilde X (⊤ : Subgroup W) I).map zQ = tilde X (⊤ : Subgroup W) (n • I) := by
    rw [show n • I = I.map n.toMonoidHom from rfl, hnz]
    unfold tilde
    rw [Subgroup.map_map, Subgroup.map_map]
    exact congrArg (fun f => I.map f) (MonoidHom.ext fun w => rfl)
  have hequiv : ∀ q ∈ tilde X (⊤ : Subgroup W) I, ∀ a : ↥X, zQ (a • q) = a • zQ q := by
    intro q hq a
    obtain ⟨v, hv, rfl⟩ := mem_tilde_iff.mp hq
    rw [XMod.smul_quotMk, hzQmk, hzQmk, XMod.smul_quotMk]
    exact congrArg QuotientGroup.mk (hcomm a a.2 v hv)
  set ψ := (Subgroup.equivMapOfInjective _ zQ hinj).trans (MulEquiv.subgroupCongr hmap)
    with hψ
  have hψv : ∀ q : ↥(tilde X (⊤ : Subgroup W) I),
      ((ψ q : ↥(tilde X (⊤ : Subgroup W) (n • I))) : W ⧸ F) = zQ q := fun q => rfl
  refine ⟨ψ.symm, fun a l l' hll' => ?_⟩
  apply hinj
  have hl : ((l : ↥(tilde X (⊤ : Subgroup W) (n • I))) : W ⧸ F) = zQ (ψ.symm l) := by
    rw [← hψv, MulEquiv.apply_symm_apply]
  have hl' : ((l' : ↥(tilde X (⊤ : Subgroup W) (n • I))) : W ⧸ F) = zQ (ψ.symm l') := by
    rw [← hψv, MulEquiv.apply_symm_apply]
  rw [hequiv _ (ψ.symm l).2 a, ← hl, ← hl']
  exact hll'

end CFSG.Quasithin.H13.T326
