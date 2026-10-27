module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}

theorem w135c2_natural_data {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)} (hirr : IsIrrOn L ⊤ ⊥)
    (hreal : (FFModel.nat Γ).Realizes L ⊤ ⊥) :
    Nat.card K ≤ Nat.card ↥(LEnd L) ∧ Nat.card W = Nat.card K ^ Fintype.card ι := by
  classical
  haveI : Fintype K := Fintype.ofFinite K
  rw [FFModel.Realizes] at hreal
  obtain ⟨π, hπ⟩ := hreal
  rw [FFModel.RealizesVia] at hπ
  obtain ⟨hπsurj, hπ2⟩ := hπ
  obtain ⟨-, -, -, -, -, -, β, hβsurj, hβker, hβeq⟩ := hπ2
  have hβinj : Function.Injective β := by
    intro u v huv
    have h1 : β (u * v⁻¹) = 1 := by rw [map_mul, map_inv, huv, mul_inv_cancel]
    have h2 : ((u * v⁻¹ : ↥(⊤ : Subgroup W)) : W) ∈ (⊥ : Subgroup W) :=
      (hβker (u * v⁻¹)).mp h1
    rw [Subgroup.mem_bot] at h2
    have h3 : u * v⁻¹ = 1 := Subtype.ext h2
    calc u = u * v⁻¹ * v := by rw [mul_assoc, inv_mul_cancel, mul_one]
      _ = 1 * v := by rw [h3]
      _ = v := one_mul v
  let q : (↥(FFModel.nat Γ).sec ⧸
        (FFModel.nat Γ).ker.subgroupOf (FFModel.nat Γ).sec) ≃* ↥(FFModel.nat Γ).sec :=
    (QuotientGroup.quotientMulEquivOfEq
        (Subgroup.bot_subgroupOf (FFModel.nat Γ).sec)).trans
      QuotientGroup.quotientBot
  have q_mk : ∀ m : ↥(FFModel.nat Γ).sec, q (QuotientGroup.mk m) = m := by
    intro m
    change QuotientGroup.quotientBot
        (QuotientGroup.quotientMulEquivOfEq
          (Subgroup.bot_subgroupOf (FFModel.nat Γ).sec)
          (QuotientGroup.mk m)) = m
    rw [QuotientGroup.quotientMulEquivOfEq_mk]
    change QuotientGroup.kerLift (MonoidHom.id ↥(FFModel.nat Γ).sec)
        (QuotientGroup.mk m) = m
    rw [QuotientGroup.kerLift_mk]
    rfl
  let f : W →* Multiplicative (ι → K) :=
    { toFun := fun w => (q (β ⟨w, Subgroup.mem_top w⟩) : (FFModel.nat Γ).Amb)
      map_one' := by
        show (q (β ⟨1, Subgroup.mem_top _⟩) : (FFModel.nat Γ).Amb) = 1
        have h1 : (⟨1, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) = 1 := rfl
        rw [h1, map_one, map_one]
        rfl
      map_mul' := by
        intro a b
        show (q (β ⟨a * b, Subgroup.mem_top _⟩) : (FFModel.nat Γ).Amb) =
          (q (β ⟨a, Subgroup.mem_top _⟩) : (FFModel.nat Γ).Amb) *
            (q (β ⟨b, Subgroup.mem_top _⟩) : (FFModel.nat Γ).Amb)
        have hAB : (⟨a * b, Subgroup.mem_top _⟩ : ↥(⊤ : Subgroup W)) =
            ⟨a, Subgroup.mem_top _⟩ * ⟨b, Subgroup.mem_top _⟩ := rfl
        rw [hAB, map_mul, map_mul]
        rfl }
  have hf : Function.Bijective f := by
    constructor
    · intro a b hab
      have hab1 : q (β ⟨a, Subgroup.mem_top a⟩) = q (β ⟨b, Subgroup.mem_top b⟩) :=
        Subtype.coe_injective hab
      have hab2 : β ⟨a, Subgroup.mem_top a⟩ = β ⟨b, Subgroup.mem_top b⟩ :=
        q.injective hab1
      have hab3 : (⟨a, Subgroup.mem_top a⟩ : ↥(⊤ : Subgroup W)) =
          ⟨b, Subgroup.mem_top b⟩ := hβinj hab2
      exact congrArg Subtype.val hab3
    · intro y
      obtain ⟨u, hu⟩ := hβsurj (q.symm ⟨y, Subgroup.mem_top y⟩)
      refine ⟨(u : W), ?_⟩
      change (q (β ⟨(u : W), Subgroup.mem_top (u : W)⟩) : (FFModel.nat Γ).Amb) = y
      have hu' : (⟨(u : W), Subgroup.mem_top (u : W)⟩ : ↥(⊤ : Subgroup W)) = u := rfl
      rw [hu', hu]
      rfl
  let e : W ≃* Multiplicative (ι → K) := MulEquiv.ofBijective f hf
  have hcardW : Nat.card W = Nat.card K ^ Fintype.card ι := by
    rw [Nat.card_congr e.toEquiv, Nat.card_congr (Multiplicative.toAdd (α := ι → K)),
      Nat.card_fun]
    simp only [Nat.card_eq_fintype_card]
  have hWlt : 1 < Nat.card W := by
    have htop : 1 < Nat.card ↥(⊤ : Subgroup W) :=
      (Subgroup.one_lt_card_iff_ne_bot (⊤ : Subgroup W)).mpr (ne_of_gt hirr.1)
    rwa [Subgroup.card_top] at htop
  have e_apply : ∀ (u : ↥(⊤ : Subgroup W)) (m : ↥(FFModel.nat Γ).sec),
      β u = QuotientGroup.mk m → e (u : W) = (m : (FFModel.nat Γ).Amb) := by
    intro u m hm
    change (q (β ⟨(u : W), Subgroup.mem_top (u : W)⟩) : (FFModel.nat Γ).Amb) =
      (m : (FFModel.nat Γ).Amb)
    have hu : (⟨(u : W), Subgroup.mem_top (u : W)⟩ : ↥(⊤ : Subgroup W)) = u := rfl
    rw [hu, hm, q_mk m]
  have e_equiv : ∀ (γ : ↥Γ) (w : Additive W),
      e (((π γ : ↥L) : MulAut W) (Additive.toMul w)) =
        natAct Γ γ (e (Additive.toMul w)) := by
    intro γ w
    let u : ↥(⊤ : Subgroup W) := ⟨Additive.toMul w, Subgroup.mem_top _⟩
    obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β u)
    have hm' : β u = QuotientGroup.mk m := hm.symm
    have he1 : e (Additive.toMul w) = (m : (FFModel.nat Γ).Amb) := by
      have := e_apply u m hm'
      simpa only [u, Subtype.coe_mk] using this
    have hstep : β ⟨((π γ : ↥L) : MulAut W) (Additive.toMul w), Subgroup.mem_top _⟩ =
        QuotientGroup.mk
          ⟨(FFModel.nat Γ).act γ (m : (FFModel.nat Γ).Amb), Subgroup.mem_top _⟩ := by
      have h := hβeq γ u m (Subgroup.mem_top _) (Subgroup.mem_top _) hm'
      simpa only [u, Subtype.coe_mk] using h
    have he2 : e (((π γ : ↥L) : MulAut W) (Additive.toMul w)) =
        ((FFModel.nat Γ).act γ (m : (FFModel.nat Γ).Amb) : Multiplicative (ι → K)) := by
      have := e_apply
        ⟨((π γ : ↥L) : MulAut W) (Additive.toMul w), Subgroup.mem_top _⟩
        ⟨(FFModel.nat Γ).act γ (m : (FFModel.nat Γ).Amb), Subgroup.mem_top _⟩ hstep
      simpa only [Subtype.coe_mk] using this
    rw [he2, he1]
    rfl
  let eA : Additive W ≃+ (ι → K) := MulEquiv.toAdditiveLeft e
  let sc : K → (ι → K) →+ (ι → K) := fun c =>
    { toFun := fun x => c • x
      map_zero' := smul_zero c
      map_add' := fun x y => smul_add c x y }
  have sc_apply : ∀ (c : K) (x : ι → K), sc c x = c • x := fun c x => rfl
  have eA_equiv : ∀ (γ : ↥Γ) (w : Additive W),
      eA (Additive.ofMul (((π γ : ↥L) : MulAut W) (Additive.toMul w))) =
        (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)).mulVec (eA w) := by
    intro γ w
    change Multiplicative.toAdd (e (((π γ : ↥L) : MulAut W) (Additive.toMul w))) =
      (((γ : Matrix.GeneralLinearGroup ι K) : Matrix ι ι K)).mulVec
        (Multiplicative.toAdd (e (Additive.toMul w)))
    rw [e_equiv γ w]
    rfl
  let Φ : K → (Additive W →+ Additive W) := fun c =>
    eA.symm.toAddMonoidHom.comp ((sc c).comp eA.toAddMonoidHom)
  have Φ_apply : ∀ (c : K) (x : Additive W), Φ c x = eA.symm ((sc c) (eA x)) := by
    intro c x
    rfl
  have hmem : ∀ c : K, Φ c ∈ LEnd L := by
    intro c g hg w
    change eA.symm ((sc c) (eA (Additive.ofMul (g (Additive.toMul w))))) =
      Additive.ofMul (g (Additive.toMul (eA.symm ((sc c) (eA w)))))
    apply eA.injective
    rw [AddEquiv.apply_symm_apply]
    obtain ⟨γ, hγ⟩ := hπsurj ⟨g, hg⟩
    have hg' : ((π γ : ↥L) : MulAut W) = g := by
      simpa using congrArg (fun z : ↥L => (z : MulAut W)) hγ
    rw [← hg', eA_equiv γ w, eA_equiv γ (eA.symm ((sc c) (eA w))),
      AddEquiv.apply_symm_apply, sc_apply, sc_apply]
    exact (Matrix.mulVec_smul _ c _).symm
  let φ : K → ↥(LEnd L) := fun c => ⟨Φ c, hmem c⟩
  have hφinj : Function.Injective φ := by
    intro c c' hcc
    have hx : ∀ x : Additive W, eA.symm ((sc c) (eA x)) = eA.symm ((sc c') (eA x)) := by
      intro x
      have h := congrArg (fun ψ : ↥(LEnd L) => ψ.1 x) hcc
      show eA.symm ((sc c) (eA x)) = eA.symm ((sc c') (eA x))
      exact h
    have hneι : Nonempty ι := by
      by_contra h
      rw [not_nonempty_iff] at h
      haveI : IsEmpty ι := h
      have hzero : Fintype.card ι = 0 := Fintype.card_eq_zero_iff.mpr h
      have h1 : Nat.card W = 1 := by rw [hcardW, hzero, pow_zero]
      exact absurd hWlt (not_lt_of_ge (le_of_eq h1))
    obtain ⟨i⟩ := hneι
    have hsc : ∀ d : K,
        (sc d) (eA (eA.symm (Function.const ι (1 : K)))) = Function.const ι d := by
      intro d
      rw [AddEquiv.apply_symm_apply, sc_apply]
      funext j
      simp
    have hx0 := hx (eA.symm (Function.const ι (1 : K)))
    rw [hsc c, hsc c'] at hx0
    have hconst : Function.const ι c = Function.const ι c' := by
      have h := congrArg eA hx0
      rwa [AddEquiv.apply_symm_apply, AddEquiv.apply_symm_apply] at h
    exact congrFun hconst i
  have hcardLE : Nat.card K ≤ Nat.card ↥(LEnd L) := by
    haveI : Finite ↥(LEnd L) := by
      haveI : Finite (AddMonoid.End (Additive W)) := DFunLike.finite _
      infer_instance
    exact Nat.card_le_card_of_injective φ hφinj
  exact ⟨hcardLE, hcardW⟩

theorem w135c2_two_le_card_index {ι K : Type} [Fintype ι] [DecidableEq ι] [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}
    (hreal : (FFModel.nat Γ).Realizes L ⊤ ⊥) (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) :
    2 ≤ Fintype.card ι := by
  classical
  by_contra hlt
  rw [not_le] at hlt
  have hcard : Fintype.card ι ≤ 1 := Nat.le_of_lt_succ hlt
  haveI : Subsingleton ι := Fintype.card_le_one_iff_subsingleton.mp hcard
  have hcommMat : ∀ A B : Matrix ι ι K, A * B = B * A := by
    intro A B
    ext i j
    rw [Subsingleton.elim i j]
    rw [Matrix.mul_apply, Matrix.mul_apply,
      Fintype.sum_subsingleton (fun k => A j k * B k j) j,
      Fintype.sum_subsingleton (fun k => B j k * A k j) j]
    exact mul_comm _ _
  have hcommGL : ∀ a b : Matrix.GeneralLinearGroup ι K, a * b = b * a := by
    intro a b
    apply Units.ext
    rw [Units.val_mul, Units.val_mul]
    exact hcommMat (a : Matrix ι ι K) (b : Matrix ι ι K)
  have hcommΓ : ∀ x y : ↥Γ, x * y = y * x := by
    intro x y
    exact Subtype.ext (hcommGL x y)
  rw [FFModel.Realizes] at hreal
  obtain ⟨π, hπ⟩ := hreal
  rw [FFModel.RealizesVia] at hπ
  have hπsurj : Function.Surjective π := hπ.1
  have hcommL : ∀ a b : ↥L, a * b = b * a := by
    intro a b
    obtain ⟨x, rfl⟩ := hπsurj a
    obtain ⟨y, rfl⟩ := hπsurj b
    rw [← map_mul, ← map_mul]
    exact congrArg π (hcommΓ x y)
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  have hcomm_ab : a * b = b * a := by
    simpa using congrArg (fun z : ↥L => (z : MulAut W)) (hcommL ⟨a, ha⟩ ⟨b, hb⟩)
  exact hab hcomm_ab

end CFSG.LocalAnalysis.WeakClosure81
