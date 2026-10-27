module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H30

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F

open Matrix

variable {m k : ℕ}

theorem smul_mem_stdE_of_presStd {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (hg : PresStd (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)))
    {v : Fin (m + k) → ZMod 2} (hv : v ∈ stdE (m + k) m) : g • v ∈ stdE (m + k) m := by
  intro i hi
  obtain ⟨b, rfl⟩ : ∃ b : Fin k, i = Fin.natAdd m b :=
    ⟨⟨(i : ℕ) - m, by omega⟩, Fin.ext (by simp; omega)⟩
  rw [bot_smul hg]
  have h0 : (fun j : Fin k => v (Fin.natAdd m j)) = 0 := funext fun j => hv _ (by simp)
  rw [h0, mulVec_zero]
  rfl

theorem botB_eq_one_of_triv {g : Matrix.SpecialLinearGroup (Fin (m + k)) (ZMod 2)}
    (h : ∀ v, g • v + v ∈ stdE (m + k) m) :
    botB (g : Matrix (Fin (m + k)) (Fin (m + k)) (ZMod 2)) = 1 := by
  ext b d
  have key : ∀ a c : ZMod 2, a + c = 0 → a = c := by decide
  have h1 := h (Pi.single (Fin.natAdd m d) 1) (Fin.natAdd m b) (by simp)
  rw [Pi.add_apply, smul_eq_mulVec', mulVec_single_one] at h1
  have h2 := key _ _ h1
  rw [botB, submatrix_apply, Matrix.one_apply]
  refine h2.trans ?_
  simp [Pi.single_apply, Fin.natAdd_inj]

theorem normalizer_E3 {X : Subgroup (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))}
    (h3 : InvStd X 3) (htriv : ∀ x ∈ X, ∀ v, x • v + v ∈ stdE 5 3)
    (hq : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)))
    {y : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)}
    (hyN : y ∈ Subgroup.normalizer (X : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))))
    (hyc : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) :
    (∀ v ∈ stdE 5 3, y • v ∈ stdE 5 3) ∧ ∀ v ∈ stdE 5 3, y • v = v := by
  obtain ⟨e⟩ := hq
  have hcard := card_eq_o2G_mul X e
  have hyc' : ∀ x ∈ X, y * x * y⁻¹ * x⁻¹ ∈ o2G X := fun x hx => pCoreOf_eq_o2G X ▸ hyc x hx
  have hX : X ≤ stabStd 3 2 := le_stabStd_of_invStd (m := 3) (k := 2) h3
  have hbot : ∀ x : ↥(stabStd 3 2), x.1 ∈ X → botH 3 2 x = 1 := fun x hx =>
    Subtype.ext (botB_eq_one_of_triv (htriv x.1 hx))
  have himg := map_eq_top_of_sq hX (topH 3 2) (fun x hx ht =>
    sq_eq_one_of_blocks x.2 (congrArg Subtype.val ht) (congrArg Subtype.val (hbot x hx))) hcard
  have hyS := mem_stabStd_of_normalizer (k := 2) hX himg hbot hyN
  have htop := eq_one_of_center_section hX (topH 3 2) himg (y := ⟨y, hyS⟩) hyc'
  have hfix : ∀ v ∈ stdE 5 3, y • v = v := fun v hv =>
    smul_eq_of_topB_one hyS (congrArg Subtype.val htop) hv
  exact ⟨fun v hv => (hfix v hv).symm ▸ hv, hfix⟩

end CFSG.Quasithin.Vol2.Ch10.SecC.C10P4F
