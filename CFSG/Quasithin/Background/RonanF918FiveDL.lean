module

public import CFSG.Quasithin.Background.RonanF918FiveD

public section

namespace CFSG.Quasithin.RonanF918

open Matrix CFSG.Open CFSG.Open.StatedAPI CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.Quasithin.RonanD321.SL2Model
open scoped Matrix

@[expose] def multLineFixedU (F : Type) [Field F]
    (image : Subgroup (Matrix.GeneralLinearGroup (Fin 2) F))
    (line : Submodule F (Fin 2 → F)) : Prop :=
  Module.finrank F line = 1 ∧
    ∀ matrix ∈ image, ∀ vector ∈ line,
      (matrix : Matrix (Fin 2) (Fin 2) F).mulVec vector ∈ line

@[expose] noncomputable def multLineModuleU (F : Type) [Field F]
    (line : Submodule F (Fin 2 → F)) : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)) :=
  { carrier := {matrix | ∀ row, (fun column => Multiplicative.toAdd matrix row column) ∈ line}
    one_mem' := by
      intro row
      change (0 : Fin 2 → F) ∈ line
      exact line.zero_mem
    mul_mem' := by
      intro first second first_mem second_mem row
      exact line.add_mem (first_mem row) (second_mem row)
    inv_mem' := by
      intro matrix matrix_mem row
      exact line.neg_mem (matrix_mem row) }

section LineModule

variable {F : Type} [Field F]

theorem slm_mul_mem_multLineModuleU {line : Submodule F (Fin 2 → F)}
    {X : Multiplicative (Matrix (Fin 2) (Fin 2) F)} (hX : X ∈ multLineModuleU F line)
    (γ : ↥(StatedSL 2 F)) :
    Multiplicative.ofAdd (slm γ * Multiplicative.toAdd X) ∈ multLineModuleU F line := by
  intro i
  have e : (fun j => (slm γ * Multiplicative.toAdd X) i j) =
      ∑ k, slm γ i k • (fun j => Multiplicative.toAdd X k j) := by
    funext j
    simp [Matrix.mul_apply, Finset.sum_apply]
  show (fun j => (slm γ * Multiplicative.toAdd X) i j) ∈ line
  rw [e]
  exact Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (hX k)

theorem exists_gen_line {line : Submodule F (Fin 2 → F)} (hrank : Module.finrank F line = 1) :
    ∃ r : Fin 2 → F, r ≠ 0 ∧ r ∈ line ∧ ∀ v ∈ line, ∃ c : F, v = c • r := by
  obtain ⟨r, hr0, hr⟩ := finrank_eq_one_iff'.mp hrank
  refine ⟨(r : Fin 2 → F), fun h => hr0 (Subtype.ext h), r.2, fun v hv => ?_⟩
  obtain ⟨c, hc⟩ := hr ⟨v, hv⟩
  exact ⟨c, (congrArg Subtype.val hc).symm⟩

theorem mem_multLineModuleU_iff {line : Submodule F (Fin 2 → F)} {r : Fin 2 → F} (hrl : r ∈ line)
    (hgen : ∀ v ∈ line, ∃ c : F, v = c • r) {X : Matrix (Fin 2) (Fin 2) F} :
    Multiplicative.ofAdd X ∈ multLineModuleU F line ↔ ∃ a : Fin 2 → F, X = Matrix.vecMulVec a r := by
  constructor
  · intro hX
    choose a ha using fun i => hgen _ (hX i)
    refine ⟨a, ?_⟩
    ext i j
    have := congrFun (ha i) j
    simpa [Matrix.vecMulVec_apply, mul_comm] using this
  · rintro ⟨a, rfl⟩ i
    have : (fun column => Multiplicative.toAdd (Multiplicative.ofAdd (Matrix.vecMulVec a r)) i column) =
        a i • r := by
      funext j
      simp [Matrix.vecMulVec_apply, mul_comm]
    show (fun column => Multiplicative.toAdd (Multiplicative.ofAdd (Matrix.vecMulVec a r)) i column) ∈ line
    rw [this]
    exact Submodule.smul_mem _ _ hrl

theorem eq_zero_of_fixed_statedSL_two {m : ℕ} (X : Matrix (Fin 2) (Fin m) F)
    (hX : ∀ γ : ↥(StatedSL 2 F), slm γ * X = X) : X = 0 := by
  ext j c
  obtain ⟨i, hij⟩ : ∃ i : Fin 2, i ≠ j := by
    by_cases h0 : j = 0
    · exact ⟨1, by rw [h0]; decide⟩
    · exact ⟨0, fun h => h0 h.symm⟩
  have hdet := Matrix.det_transvection_of_ne i j hij (1 : F)
  have h1 := hX (slOf (Matrix.transvection i j (1 : F)) hdet)
  rw [slm_slOf] at h1
  have h2 := congrFun (congrFun h1 i) c
  rw [Matrix.transvection_mul_apply_same] at h2
  have h4 : X j c = 0 := by
    have := h2
    simp at this
    exact this
  simpa using h4

end LineModule

section LineCoord

variable {W : Type} [CommGroup W] [Finite W] {L Mp : Subgroup (MulAut W)} {F : Type} [Field F]
  (D : CoordData L Mp F) (line : Submodule F (Fin 2 → F))

@[expose] noncomputable def Sline : Subgroup W := ((multLineModuleU F line).comap D.bq).map (commV L).subtype

theorem Sline_le_commV : Sline D line ≤ commV L := by
  rintro _ ⟨u, -, rfl⟩
  exact u.2

theorem mem_Sline_iff (w : ↥(commV L)) :
    (w : W) ∈ Sline D line ↔ D.bq w ∈ multLineModuleU F line := by
  constructor
  · rintro ⟨u, hu, hue⟩
    have : u = w := Subtype.ext hue
    subst this
    exact hu
  · intro h
    exact ⟨w, h, rfl⟩

theorem Sline_invariant {l : MulAut W} (hl : l ∈ L) {s : W} (hs : s ∈ Sline D line) :
    l s ∈ Sline D line := by
  have hsC : s ∈ commV L := Sline_le_commV D line hs
  have hlsC : l s ∈ commV L := apply_mem_commV (Subgroup.le_normalizer hl) hsC
  obtain ⟨γ, hγ⟩ := D.pi_surj ⟨l, hl⟩
  have hπ : ((D.pi γ : ↥L) : MulAut W) = l := congrArg Subtype.val hγ
  subst hπ
  have h1 := D.bq_equiv γ ⟨s, hsC⟩ hlsC
  have h2 := (mem_Sline_iff D line ⟨s, hsC⟩).mp hs
  rw [mem_Sline_iff D line ⟨_, hlsC⟩, h1]
  exact slm_mul_mem_multLineModuleU h2 γ

theorem commSub_invariant {S : Subgroup W} (hS : ∀ l ∈ L, ∀ s ∈ S, l s ∈ S) {l : MulAut W} (hl : l ∈ L)
    {r : W} (hr : r ∈ commSub S L) : l r ∈ commSub S L := by
  induction hr using Subgroup.closure_induction with
  | mem c hc =>
    obtain ⟨x, hx, w, hw, rfl⟩ := hc
    refine Subgroup.subset_closure ⟨l * x * l⁻¹, L.mul_mem (L.mul_mem hl hx) (L.inv_mem hl), l w,
      hS l hl w hw, ?_⟩
    simp [MulAut.mul_apply]
  | one => simpa using (commSub S L).one_mem
  | mul a b ha hb iha ihb => simpa [map_mul] using (commSub S L).mul_mem iha ihb
  | inv a ha ih => simpa [map_inv] using (commSub S L).inv_mem ih

theorem commSub_le_Sline : commSub (Sline D line) L ≤ Sline D line :=
  commSub_le_of_invariant fun _ hl _ hs => Sline_invariant D line hl hs

theorem fixed_iff (hLMp : L ≤ Mp) (u : ↥(commV L)) :
    (∀ a ∈ L, a (u : W) = (u : W)) ↔ D.bq u = 1 := by
  constructor
  · intro hu
    have hfix : ∀ γ : ↥(StatedSL 2 F), slm γ * Multiplicative.toAdd (D.bq u) =
        Multiplicative.toAdd (D.bq u) := by
      intro γ
      have hγu : ((D.pi γ : ↥L) : MulAut W) (u : W) = (u : W) := hu _ (D.pi γ).2
      have h1 := D.bq_equiv γ u (by rw [hγu]; exact u.2)
      have h2 : (⟨((D.pi γ : ↥L) : MulAut W) (u : W), by rw [hγu]; exact u.2⟩ : ↥(commV L)) = u :=
        Subtype.ext hγu
      rw [h2] at h1
      exact (congrArg Multiplicative.toAdd h1).symm
    have h0 := eq_zero_of_fixed_statedSL_two _ hfix
    exact Multiplicative.toAdd.injective h0
  · intro h a ha
    exact ((D.bq_ker u).mp h) a (hLMp ha)

theorem exists_commSub_preimage (hrank : Module.finrank F line = 1) {Y : Multiplicative (Matrix (Fin 2) (Fin 2) F)}
    (hY : Y ∈ multLineModuleU F line) :
    ∃ (r : W) (hrC : r ∈ commV L), r ∈ commSub (Sline D line) L ∧ D.bq ⟨r, hrC⟩ = Y := by
  obtain ⟨r0, hr0, hrl, hgen⟩ := exists_gen_line hrank
  let Rimg : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) F)) :=
    ((commSub (Sline D line) L).comap (commV L).subtype).map D.bq
  suffices hsub : multLineModuleU F line ≤ Rimg by
    obtain ⟨u, hu, hue⟩ := hsub hY
    exact ⟨u, u.2, hu, hue⟩
  have hbasis : ∀ (i : Fin 2) (c : F),
      Multiplicative.ofAdd (Matrix.vecMulVec (Pi.single i c) r0) ∈ Rimg := by
    intro i c
    obtain ⟨j, hji⟩ : ∃ j : Fin 2, j ≠ i := by
      by_cases h0 : i = 0
      · exact ⟨1, by rw [h0]; decide⟩
      · exact ⟨0, fun h => h0 h.symm⟩
    have hYj : Multiplicative.ofAdd (Matrix.vecMulVec (Pi.single j (1 : F)) r0) ∈
        multLineModuleU F line :=
      (mem_multLineModuleU_iff hrl hgen).mpr ⟨_, rfl⟩
    obtain ⟨u, hu⟩ := D.bq_surj (Multiplicative.ofAdd (Matrix.vecMulVec (Pi.single j (1 : F)) r0))
    have huS : (u : W) ∈ Sline D line := (mem_Sline_iff D line u).mpr (hu ▸ hYj)
    have hdet := Matrix.det_transvection_of_ne i j hji.symm c
    set γ := slOf (Matrix.transvection i j c) hdet with hγ
    have hxL : ((D.pi γ : ↥L) : MulAut W) ∈ L := (D.pi γ).2
    have hxuC : ((D.pi γ : ↥L) : MulAut W) (u : W) ∈ commV L :=
      apply_mem_commV (Subgroup.le_normalizer hxL) u.2
    have hgenmem : ((D.pi γ : ↥L) : MulAut W) (u : W) * (u : W)⁻¹ ∈ commSub (Sline D line) L :=
      Subgroup.subset_closure ⟨_, hxL, _, huS, rfl⟩
    refine ⟨⟨_, (commV L).mul_mem hxuC ((commV L).inv_mem u.2)⟩, hgenmem, ?_⟩
    have h1 : D.bq ⟨((D.pi γ : ↥L) : MulAut W) (u : W) * (u : W)⁻¹,
        (commV L).mul_mem hxuC ((commV L).inv_mem u.2)⟩ =
        D.bq ⟨((D.pi γ : ↥L) : MulAut W) (u : W), hxuC⟩ * (D.bq u)⁻¹ := by
      rw [← map_inv, ← map_mul]
      rfl
    rw [h1, D.bq_equiv γ u hxuC, hu, ← ofAdd_neg, ← ofAdd_add]
    congr 1
    rw [slm_slOf]
    ext a b
    by_cases hai : a = i
    · subst hai
      rw [Matrix.add_apply, Matrix.neg_apply, Matrix.transvection_mul_apply_same]
      simp [Matrix.vecMulVec_apply]
    · rw [Matrix.add_apply, Matrix.neg_apply, Matrix.transvection_mul_apply_of_ne _ _ _ _ hai]
      simp [Matrix.vecMulVec_apply, Pi.single_apply, hai]
  intro Y hY
  rw [← ofAdd_toAdd Y] at hY ⊢
  obtain ⟨a, ha⟩ := (mem_multLineModuleU_iff hrl hgen).mp hY
  rw [ha]
  have hsplit : Matrix.vecMulVec a r0 = Matrix.vecMulVec (Pi.single 0 (a 0)) r0 +
      Matrix.vecMulVec (Pi.single 1 (a 1)) r0 := by
    rw [← Matrix.add_vecMulVec]
    congr 1
    ext i
    fin_cases i <;> simp
  rw [hsplit, ofAdd_add]
  exact Rimg.mul_mem (hbasis 0 _) (hbasis 1 _)

theorem comm_ident {V : Type} [CommGroup V] (p q s c : V) :
    (p * q * s⁻¹)⁻¹ * (q * s⁻¹ * c) = (p * c⁻¹)⁻¹ := by
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv]
  abel

theorem commSub_commSub_eq_of_perfect [Group.IsPerfect ↥L] {S : Subgroup W}
    (hS : ∀ l ∈ L, ∀ s ∈ S, l s ∈ S) : commSub (commSub S L) L = commSub S L := by
  apply le_antisymm
  · exact commSub_le_of_invariant fun l hl r hr => commSub_invariant hS hl hr
  · refine (Subgroup.closure_le (commSub (commSub S L) L)).mpr ?_
    rintro _ ⟨x, hx, s, hs, rfl⟩
    set R := commSub S L with hR
    set E := commSub R L with hE
    let Ψ : ↥L →* W ⧸ E :=
      { toFun := fun y => QuotientGroup.mk (((y : MulAut W) s) * s⁻¹)
        map_one' := by simp
        map_mul' := fun y z => by
          show (QuotientGroup.mk ((((y * z : ↥L)) : MulAut W) s * s⁻¹) : W ⧸ E) =
            QuotientGroup.mk (((y : MulAut W) s) * s⁻¹) * QuotientGroup.mk (((z : MulAut W) s) * s⁻¹)
          rw [← QuotientGroup.mk_mul, QuotientGroup.eq]
          have hc : ((z : MulAut W) s * s⁻¹ : W) ∈ R := Subgroup.subset_closure ⟨z, z.2, s, hs, rfl⟩
          have hgen : ((y : MulAut W) ((z : MulAut W) s * s⁻¹)) * ((z : MulAut W) s * s⁻¹)⁻¹ ∈ E :=
            Subgroup.subset_closure ⟨y, y.2, _, hc, rfl⟩
          have e0 : (((y * z : ↥L)) : MulAut W) s = (y : MulAut W) ((z : MulAut W) s) := rfl
          have e1 : (((y * z : ↥L)) : MulAut W) s = (y : MulAut W) ((z : MulAut W) s * s⁻¹) *
              (y : MulAut W) s := by
            rw [e0, map_mul, map_inv, mul_assoc, inv_mul_cancel, mul_one]
          rw [e1, comm_ident]
          exact E.inv_mem hgen }
    have hker : Ψ.ker = ⊤ := by
      have := Abelianization.commutator_subset_ker Ψ
      rw [Group.IsPerfect.commutator_eq_top] at this
      exact top_le_iff.mp this
    have h1 : Ψ ⟨x, hx⟩ = 1 := by
      have : (⟨x, hx⟩ : ↥L) ∈ Ψ.ker := hker ▸ Subgroup.mem_top _
      exact this
    exact (QuotientGroup.eq_one_iff _).mp h1

theorem isIrrSec_commSub (hLMp : L ≤ Mp) (hrank : Module.finrank F line = 1) :
    XMod.IsIrrSec ↥L (XMod.fixed ↥L (commSub (Sline D line) L)) (commSub (Sline D line) L) := by
  obtain ⟨r0, hr0, hrl, hgen⟩ := exists_gen_line hrank
  have hRC : ∀ r ∈ commSub (Sline D line) L, r ∈ commV L := fun r hr =>
    Sline_le_commV D line (commSub_le_Sline D line hr)
  have hfix : ∀ r (hrC : r ∈ commV L), (∀ a : ↥L, a • r = r) ↔ D.bq ⟨r, hrC⟩ = 1 := by
    intro r hrC
    rw [← fixed_iff D hLMp ⟨r, hrC⟩]
    constructor
    · intro h a ha
      exact h ⟨a, ha⟩
    · intro h a
      exact h a a.2
  refine ⟨?_, ?_⟩
  · refine lt_of_le_of_ne (fun r hr => hr.1) fun heq => ?_
    have hY : Multiplicative.ofAdd (Matrix.vecMulVec (Pi.single (0 : Fin 2) (1 : F)) r0) ∈
        multLineModuleU F line := (mem_multLineModuleU_iff hrl hgen).mpr ⟨_, rfl⟩
    obtain ⟨r, hrC, hrR, hbr⟩ := exists_commSub_preimage D line hrank hY
    have hrf : r ∈ XMod.fixed ↥L (commSub (Sline D line) L) := by rw [heq]; exact hrR
    have h1 := (hfix r hrC).mp hrf.2
    rw [hbr] at h1
    have h2 : Matrix.vecMulVec (Pi.single (0 : Fin 2) (1 : F)) r0 = 0 := ofAdd_eq_one.mp h1
    apply hr0
    funext j
    have := congrFun (congrFun h2 0) j
    simpa [Matrix.vecMulVec_apply] using this
  · intro J' hinv hCJ' hJ'R
    by_cases hall : ∀ u (hu : u ∈ J'), D.bq ⟨u, hRC u (hJ'R hu)⟩ = 1
    · left
      refine le_antisymm (fun u hu => ⟨hJ'R hu, fun a => ?_⟩) hCJ'
      exact (hfix u (hRC u (hJ'R hu))).mpr (hall u hu) a
    · right
      push Not at hall
      obtain ⟨u0, hu0, hne⟩ := hall
      let S₀ : AddSubgroup (Fin 2 → F) :=
        { carrier := {a | ∃ u, ∃ hu : u ∈ J', D.bq ⟨u, hRC u (hJ'R hu)⟩ =
            Multiplicative.ofAdd (Matrix.vecMulVec a r0)}
          zero_mem' := ⟨1, J'.one_mem, by
            have : (⟨(1 : W), hRC 1 (hJ'R J'.one_mem)⟩ : ↥(commV L)) = 1 := rfl
            rw [this, map_one, Matrix.zero_vecMulVec, ofAdd_zero]⟩
          add_mem' := by
            rintro a₁ a₂ ⟨u₁, hu₁, h₁⟩ ⟨u₂, hu₂, h₂⟩
            refine ⟨u₁ * u₂, J'.mul_mem hu₁ hu₂, ?_⟩
            have : (⟨u₁ * u₂, hRC _ (hJ'R (J'.mul_mem hu₁ hu₂))⟩ : ↥(commV L)) =
                ⟨u₁, hRC u₁ (hJ'R hu₁)⟩ * ⟨u₂, hRC u₂ (hJ'R hu₂)⟩ := rfl
            rw [this, map_mul, h₁, h₂, ← ofAdd_add, Matrix.add_vecMulVec]
          neg_mem' := by
            rintro a ⟨u, hu, h⟩
            refine ⟨u⁻¹, J'.inv_mem hu, ?_⟩
            have : (⟨u⁻¹, hRC _ (hJ'R (J'.inv_mem hu))⟩ : ↥(commV L)) =
                (⟨u, hRC u (hJ'R hu)⟩ : ↥(commV L))⁻¹ := rfl
            rw [this, map_inv, h, ← ofAdd_neg, Matrix.neg_vecMulVec] }
      have hS₀inv : ∀ g : ↥(StatedSL 2 F), ∀ a ∈ S₀,
          ((g : GL (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ a ∈ S₀ := by
        rintro g a ⟨u, hu, h⟩
        have huC : u ∈ commV L := hRC u (hJ'R hu)
        have hπu : ((D.pi g : ↥L) : MulAut W) u ∈ J' := hinv (D.pi g) u hu
        have hmem : ((D.pi g : ↥L) : MulAut W) u ∈ commV L := hRC _ (hJ'R hπu)
        refine ⟨_, hπu, ?_⟩
        have h1 := D.bq_equiv g ⟨u, huC⟩ hmem
        rw [h] at h1
        rw [h1, toAdd_ofAdd, Matrix.mul_vecMulVec]
      obtain ⟨a0, ha0⟩ : ∃ a0, D.bq ⟨u0, hRC u0 (hJ'R hu0)⟩ =
          Multiplicative.ofAdd (Matrix.vecMulVec a0 r0) := by
        have hmemLM : D.bq ⟨u0, hRC u0 (hJ'R hu0)⟩ ∈ multLineModuleU F line :=
          (mem_Sline_iff D line ⟨u0, hRC u0 (hJ'R hu0)⟩).mp (commSub_le_Sline D line (hJ'R hu0))
        obtain ⟨a, ha⟩ := (mem_multLineModuleU_iff hrl hgen
          (X := Multiplicative.toAdd (D.bq ⟨u0, hRC u0 (hJ'R hu0)⟩))).mp
          (by rw [ofAdd_toAdd]; exact hmemLM)
        exact ⟨a, by rw [← ha, ofAdd_toAdd]⟩
      have ha0ne : a0 ≠ 0 := by
        rintro rfl
        apply hne
        rw [ha0, Matrix.zero_vecMulVec, ofAdd_zero]
      have hS₀top : S₀ = ⊤ := eq_top_of_slMulVec_mem (by norm_num) hS₀inv ⟨u0, hu0, ha0⟩ ha0ne
      refine le_antisymm hJ'R fun r hr => ?_
      have hrC : r ∈ commV L := hRC r hr
      have hrLM : D.bq ⟨r, hrC⟩ ∈ multLineModuleU F line :=
        (mem_Sline_iff D line ⟨r, hrC⟩).mp (commSub_le_Sline D line hr)
      obtain ⟨a, ha⟩ := (mem_multLineModuleU_iff hrl hgen
        (X := Multiplicative.toAdd (D.bq ⟨r, hrC⟩))).mp (by rw [ofAdd_toAdd]; exact hrLM)
      have haS : a ∈ S₀ := hS₀top ▸ AddSubgroup.mem_top a
      obtain ⟨j, hj, hbj⟩ := haS
      have hbr : D.bq ⟨r, hrC⟩ = D.bq ⟨j, hRC j (hJ'R hj)⟩ := by
        rw [hbj, ← ha, ofAdd_toAdd]
      have hrj : r * j⁻¹ ∈ commSub (Sline D line) L :=
        (commSub (Sline D line) L).mul_mem hr ((commSub (Sline D line) L).inv_mem (hJ'R hj))
      have hbq1 : D.bq ⟨r * j⁻¹, hRC _ hrj⟩ = 1 := by
        have : (⟨r * j⁻¹, hRC _ hrj⟩ : ↥(commV L)) =
            ⟨r, hrC⟩ * (⟨j, hRC j (hJ'R hj)⟩ : ↥(commV L))⁻¹ := rfl
        rw [this, map_mul, map_inv, hbr, mul_inv_cancel]
      have hCmem : r * j⁻¹ ∈ XMod.fixed ↥L (commSub (Sline D line) L) :=
        ⟨hrj, (hfix _ (hRC _ hrj)).mpr hbq1⟩
      have hrr : r = (r * j⁻¹) * j := by simp
      rw [hrr]
      exact J'.mul_mem (hCJ' hCmem) hj

end LineCoord

end CFSG.Quasithin.RonanF918
