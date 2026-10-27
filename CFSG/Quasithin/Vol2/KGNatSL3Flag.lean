module

public import CFSG.Quasithin.Vol2.KGNatSL3Real
public import CFSG.Quasithin.Vol2.KGNatComm
public import CFSG.Quasithin.Vol2.KGNatSL3Std

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Open CFSG.Quasithin Matrix CFSG.ClassicalInvolution.ModelFacts.OddCover
open CFSG.Assembly.LowTwoRank (StatedSL StatedSp specialLinearGroupEquivStatedSL
  specialLinearGroupEquivStatedSL_coe)

namespace IsCoord

variable {D : FFModel} {K M : Type} [Field K] [AddCommGroup M] [Module K M]
  {W : Type*} [CommGroup W] {LM : LinModel D K M} {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : D.Gam →* ↥H} {f : W → M} (hf : IsCoord LM H Z π f)
include hf

@[expose] def pre (S : AddSubgroup M) : Subgroup W where
  carrier := {w | f w ∈ S}
  mul_mem' := fun {a b} ha hb => by
    show f (a * b) ∈ S
    rw [hf.map_mul]
    exact S.add_mem ha hb
  one_mem' := by
    show f 1 ∈ S
    rw [hf.map_one]
    exact S.zero_mem
  inv_mem' := fun {a} ha => by
    show f a⁻¹ ∈ S
    rw [hf.map_inv]
    exact S.neg_mem ha

theorem mem_pre {S : AddSubgroup M} {w : W} : w ∈ hf.pre S ↔ f w ∈ S := Iff.rfl

theorem le_pre (S : AddSubgroup M) : Z ≤ hf.pre S := fun z hz => by
  show f z ∈ S
  rw [(hf.ker z).mpr hz]
  exact S.zero_mem

theorem img_pre (S : AddSubgroup M) : hf.img (hf.pre S) = S := by
  ext x
  constructor
  · rintro ⟨w, hw, rfl⟩
    exact hw
  · intro hx
    obtain ⟨w, rfl⟩ := hf.surj x
    exact ⟨w, hx, rfl⟩

theorem pre_img {U : Subgroup W} (hZU : Z ≤ U) : hf.pre (hf.img U) = U := by
  ext w
  exact (hf.mem_iff hZU w).symm

end IsCoord

variable {K : Type} [Field K]

@[expose] def gmap (g : Matrix.SpecialLinearGroup (Fin 3) K) (S : Submodule K (Fin 3 → K)) :
    Submodule K (Fin 3 → K) :=
  S.map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K))

theorem mem_gmap {g : Matrix.SpecialLinearGroup (Fin 3) K} {S : Submodule K (Fin 3 → K)}
    {x : Fin 3 → K} :
    x ∈ gmap g S ↔
      ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∈ S := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    exact hy
  · intro hx
    refine ⟨_, hx, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem card_gmap (g : Matrix.SpecialLinearGroup (Fin 3) K) (S : Submodule K (Fin 3 → K)) :
    Nat.card (gmap g S) = Nat.card S := by
  have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) K)) := by
    intro x y h
    have := congrArg (Matrix.toLin' ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) h
    rwa [Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.toLin'_apply,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec,
      Matrix.one_mulVec] at this
  exact Nat.card_congr (Submodule.equivMapOfInjective _ hinj S).toEquiv.symm

theorem gmap_gmap_inv (g : Matrix.SpecialLinearGroup (Fin 3) K) (S : Submodule K (Fin 3 → K)) :
    gmap g (gmap g⁻¹ S) = S := by
  ext x
  rw [mem_gmap, mem_gmap, inv_inv, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

@[expose] def UStable (S : Submodule K (Fin 3 → K)) : Prop :=
  ∀ a b c : K, ∀ x ∈ S, uMat a b c *ᵥ x ∈ S

theorem UStable.mem_iff {S : Submodule K (Fin 3 → K)} (hS : UStable S)
    {u : Matrix.SpecialLinearGroup (Fin 3) K} (hu : u ∈ Usl K) (x : Fin 3 → K) :
    (u : Matrix (Fin 3) (Fin 3) K) *ᵥ x ∈ S ↔ x ∈ S := by
  obtain ⟨a, b, c, rfl⟩ := hu
  refine ⟨fun h => ?_, fun h => hS a b c x h⟩
  have hinv : uMat (-a) (a * c - b) (-c) * uMat a b c = (1 : Matrix (Fin 3) (Fin 3) K) := by
    rw [← coe_uSL, ← coe_uSL, ← Matrix.SpecialLinearGroup.coe_mul, ← uSL_inv, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one]
  have := hS (-a) (a * c - b) (-c) _ h
  change uMat (-a) (a * c - b) (-c) *ᵥ (uMat a b c *ᵥ x) ∈ S at this
  rwa [Matrix.mulVec_mulVec, hinv, Matrix.one_mulVec] at this

theorem conj_mulVec (g u : Matrix.SpecialLinearGroup (Fin 3) K) (x : Fin 3 → K) :
    ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((g * u * g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x =
      (u : Matrix (Fin 3) (Fin 3) K) *ᵥ
        ((g⁻¹ : Matrix.SpecialLinearGroup (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ x := by
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    ← Matrix.SpecialLinearGroup.coe_mul, show g⁻¹ * (g * u * g⁻¹) = u * g⁻¹ by group]

section Flag

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z : Subgroup W}
  {π : ↥(StatedSL 3 K) →* ↥H} {f : W → (Fin 3 → K)}

theorem IsCoord.rho3_mem_stabW_iff (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f)
    {U : Subgroup W} (hZU : Z ≤ U) (A : Matrix.SpecialLinearGroup (Fin 3) K) :
    ((rho3 π A : ↥H) : MulAut W) ∈ Ch11.SecA.stabW U ↔
      ∀ y, y ∈ hf.img U ↔ (A : Matrix (Fin 3) (Fin 3) K) *ᵥ y ∈ hf.img U :=
  hf.mem_stabW_iff hZU (specialLinearGroupEquivStatedSL 3 K A)

theorem isFlagW_pre (hW : ∀ w : W, w ^ 2 = 1)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) {P : Subgroup (MulAut W)}
    {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {S : Submodule K (Fin 3 → K)} (hS : UStable S) {i : ℕ} (hcard : Nat.card S = Nat.card K ^ i) :
    Ch11.SecA.IsFlagW H P Z (Nat.card K) i (hf.pre (gmap g S).toAddSubgroup) := by
  refine ⟨hf.le_pre _, ?_, ?_, fun x hx => ?_⟩
  · rw [hf.endStableW_iff hW (fun T hT => commutant_statedSL (by norm_num) T hT) (hf.le_pre _),
      hf.img_pre]
    exact fun c x hx => (gmap g S).smul_mem c hx
  · rw [← hf.card_img, hf.img_pre, ← hcard, ← card_gmap g S]
    rfl
  · obtain ⟨u, hu, rfl⟩ := (hg x).mp hx
    rw [hf.rho3_mem_stabW_iff (hf.le_pre _), hf.img_pre]
    intro y
    change y ∈ gmap g S ↔ _ ∈ gmap g S
    rw [mem_gmap, mem_gmap, conj_mulVec, hS.mem_iff hu]

theorem exists_eq_pre_of_isFlagW (hW : ∀ w : W, w ^ 2 = 1)
    (hf : IsCoord (linModelNat (StatedSL 3 K)) H Z π f) {P : Subgroup (MulAut W)}
    {g : Matrix.SpecialLinearGroup (Fin 3) K}
    (hg : ∀ x : MulAut W, x ∈ P ↔ ∃ u ∈ Usl K, x = ((rho3 π (g * u * g⁻¹) : ↥H) : MulAut W))
    {i : ℕ} {U : Subgroup W} (hU : Ch11.SecA.IsFlagW H P Z (Nat.card K) i U) :
    ∃ S : Submodule K (Fin 3 → K), UStable S ∧ Nat.card S = Nat.card K ^ i ∧
      U = hf.pre (gmap g S).toAddSubgroup := by
  obtain ⟨hZU, hst, hidx, hPU⟩ := hU
  have hsc := (hf.endStableW_iff hW (fun T hT => commutant_statedSL (by norm_num) T hT)
    hZU).mp hst
  let T : Submodule K (Fin 3 → K) :=
    { carrier := hf.img U
      add_mem' := (hf.img U).add_mem
      zero_mem' := (hf.img U).zero_mem
      smul_mem' := fun c x hx => hsc c x hx }
  have hTcard : Nat.card T = Nat.card K ^ i := by
    rw [← hidx, ← hf.card_img]
    rfl
  refine ⟨gmap g⁻¹ T, fun a b c x hx => ?_, by rw [card_gmap, hTcard], ?_⟩
  · rw [mem_gmap, inv_inv] at hx ⊢
    have hp : ((rho3 π (g * uSL a b c * g⁻¹) : ↥H) : MulAut W) ∈ Ch11.SecA.stabW U :=
      hPU ((hg _).mpr ⟨uSL a b c, uSL_mem_Usl a b c, rfl⟩)
    have h1 := ((hf.rho3_mem_stabW_iff hZU _).mp hp _).mp hx
    change _ ∈ T at h1
    rw [Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
      show g * uSL a b c * g⁻¹ * g = g * uSL a b c by group,
      Matrix.SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, coe_uSL] at h1
    exact h1
  · rw [gmap_gmap_inv]
    exact (hf.pre_img hZU).symm

end Flag

theorem factFlagSL3_holds : Ch11.SecA.FactFlagSL3 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  obtain ⟨g, hg⟩ := exists_sylow_eq_conj_Usl hK (by omega) hf hP
  rw [← hK]
  have hL : UStable (stdLine K) := fun a b c _ hx => uMat_mem_stdLine a b c hx
  have hPl : UStable (stdPlane K) := fun a b c _ hx => uMat_mem_stdPlane a b c hx
  have hT : UStable (⊤ : Submodule K (Fin 3 → K)) := fun _ _ _ _ _ => Submodule.mem_top
  refine ⟨_, _, _, isFlagW_pre hW hf hg hL (by rw [card_stdLine, pow_one]),
    isFlagW_pre hW hf hg hPl card_stdPlane, isFlagW_pre hW hf hg hT card_top3,
    fun w hw => Submodule.map_mono stdLine_le_stdPlane hw,
    fun w hw => Submodule.map_mono le_top hw, fun U hU => ?_, fun U hU => ?_, fun U hU => ?_⟩
  · obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW hW hf hg hU
    rw [(eq_std_of_stable hS).1 (by rw [hc, pow_one])]
  · obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW hW hf hg hU
    rw [(eq_std_of_stable hS).2.1 hc]
  · obtain ⟨S, hS, hc, rfl⟩ := exists_eq_pre_of_isFlagW hW hf hg hU
    rw [(eq_std_of_stable hS).2.2 hc]

end CFSG.Quasithin.Vol2.KGNat
