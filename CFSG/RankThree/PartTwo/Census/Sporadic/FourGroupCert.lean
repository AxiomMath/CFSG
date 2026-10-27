module

public import CFSG.RankThree.PartTwo.Census.Sporadic.RankFourCert

public section

namespace CFSG.RankThree.PartTwo.Census

open CFSG.Blueprint CFSG.SectionRank CFSG.SectionRank.Native
open scoped Matrix

structure V4Data where
  base : Data
  inv₁ : ℕ
  inv₂ : ℕ

namespace V4Data

variable {M V : Type} (O : Ops M V)

@[expose] def conjOK (X T T₁ T₂ : M) : Bool :=
  O.eq (O.mul X T) (O.mul T₁ X) || O.eq (O.mul X T) (O.mul T₂ X) ||
    O.eq (O.mul X T) (O.mul (O.mul T₁ T₂) X)

@[expose] def check [Inhabited M] (D : V4Data) : Bool :=
  let R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  decide (2 ≤ D.base.nregs) && D.base.prog.all (Op.lt D.base.nregs) &&
    D.base.outs.all (decide <| · < D.base.nregs) && decide (D.inv₁ < D.base.nregs) &&
    decide (D.inv₂ < D.base.nregs) &&
    O.elemOK (D.base.outs.map fun r => R[r]!) D.base.tests &&
    O.eq (O.mul R[D.inv₁]! R[D.inv₁]!) O.one && O.eq (O.mul R[D.inv₂]! R[D.inv₂]!) O.one &&
    O.commOK R[D.inv₁]! R[D.inv₂]! &&
    D.base.tests.any (fun k => O.vne (O.vmul (O.unit k) R[D.inv₁]!) (O.unit k)) &&
    D.base.outs.all (fun r => conjOK O R[r]! R[D.inv₁]! R[D.inv₁]! R[D.inv₂]! &&
      conjOK O R[r]! R[D.inv₂]! R[D.inv₁]! R[D.inv₂]!)

end V4Data

namespace FourGroup

variable {G : Type*} [Group G]

theorem isPGroup_closure_pair {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1) (hab : a * b = b * a) :
    IsPGroup 2 (Subgroup.closure ({a, b} : Set G)) := by
  have hcomm : ({a, b} : Set G).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hcc := Subgroup.closure_le_centralizer_centralizer ({a, b} : Set G)
  have hsq : ∀ g ∈ Subgroup.closure ({a, b} : Set G), g ^ 2 = 1 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      rcases hx with rfl | rfl
      · exact ha
      · exact hb
    | one => exact one_pow 2
    | mul x y hx hy ihx ihy =>
      have hxy : Commute x y :=
        Set.centralizer_centralizer_comm_of_comm hcomm _ (hcc hx) _ (hcc hy)
      rw [hxy.mul_pow, ihx, ihy, one_mul]
    | inv x _ ihx => rw [inv_pow, ihx, inv_one]
  intro g
  exact ⟨1, Subtype.ext (by simpa using hsq g g.2)⟩

theorem conj_mem_closure {s : Set G} {g : G} (hg : ∀ x ∈ s, g * x * g⁻¹ ∈ Subgroup.closure s)
    {y : G} (hy : y ∈ Subgroup.closure s) : g * y * g⁻¹ ∈ Subgroup.closure s := by
  induction hy using Subgroup.closure_induction with
  | mem x hx => exact hg x hx
  | one => simp
  | mul x y _ _ hx hy =>
    have e : g * (x * y) * g⁻¹ = g * x * g⁻¹ * (g * y * g⁻¹) := by group
    rw [e]
    exact (Subgroup.closure s).mul_mem hx hy
  | inv x _ hx =>
    have e : g * x⁻¹ * g⁻¹ = (g * x * g⁻¹)⁻¹ := by group
    rw [e]
    exact (Subgroup.closure s).inv_mem hx

theorem mem_normalizer_closure_of_pow_three {s : Set G} {w : G} (hw : w ^ 3 = 1)
    (h : ∀ x ∈ s, w * x * w⁻¹ ∈ Subgroup.closure s) :
    w ∈ Subgroup.normalizer (Subgroup.closure s : Set G) := by
  have hw' : w * w * w = 1 := by rw [← pow_three', hw]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨conj_mem_closure h, fun hy => ?_⟩
  have h1 := conj_mem_closure h (conj_mem_closure h hy)
  have e : w * (w * (w * y * w⁻¹) * w⁻¹) * w⁻¹ = y := by
    have e3 : w * (w * (w * y * w⁻¹) * w⁻¹) * w⁻¹ = w * w * w * y * (w * w * w)⁻¹ := by group
    rw [e3, hw', one_mul, inv_one, mul_one]
  rw [e] at h1
  exact h1

end FourGroup

namespace OpsSpec

variable {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
include Sp

theorem toMat_of_conjOK {X T T₁ T₂ : M} (hX : Sp.WF X) (hT : Sp.WF T) (h₁ : Sp.WF T₁)
    (h₂ : Sp.WF T₂) (h : V4Data.conjOK O X T T₁ T₂ = true) :
    Sp.toMat X * Sp.toMat T = Sp.toMat T₁ * Sp.toMat X ∨
      Sp.toMat X * Sp.toMat T = Sp.toMat T₂ * Sp.toMat X ∨
        Sp.toMat X * Sp.toMat T = Sp.toMat T₁ * Sp.toMat T₂ * Sp.toMat X := by
  unfold V4Data.conjOK at h
  simp only [Bool.or_eq_true] at h
  have hXT := Sp.mul_wf hX hT
  rcases h with (h | h) | h
  · left
    have := Sp.toMat_eq hXT (Sp.mul_wf h₁ hX) h
    rwa [Sp.toMat_mul hX hT, Sp.toMat_mul h₁ hX] at this
  · right; left
    have := Sp.toMat_eq hXT (Sp.mul_wf h₂ hX) h
    rwa [Sp.toMat_mul hX hT, Sp.toMat_mul h₂ hX] at this
  · right; right
    have := Sp.toMat_eq hXT (Sp.mul_wf (Sp.mul_wf h₁ h₂) hX) h
    rwa [Sp.toMat_mul hX hT, Sp.toMat_mul (Sp.mul_wf h₁ h₂) hX, Sp.toMat_mul h₁ h₂] at this

theorem exists_of_v4Check [Inhabited M] (D : V4Data) (h : V4Data.check O D = true) :
    ∃ P E : Subgroup (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ,
      P ≠ ⊥ ∧ IsPGroup 2 P ∧ CFSG.Open.IsElemAbelian 3 E ∧
        Nat.card E = 3 ^ D.base.outs.length ∧ E ≤ Subgroup.normalizer (P : Set _) := by
  set S := NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB
  unfold V4Data.check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hn, hprog⟩, houts⟩, hinv₁⟩, hinv₂⟩, hel⟩, hT₁⟩, hT₂⟩, hT₁₂⟩, hmov⟩, hconj⟩ :=
    h
  have hA : Sp.WF (O.decode D.base.seedA) ∧ Sp.toMat (O.decode D.base.seedA) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert _ _)⟩
  have hB : Sp.WF (O.decode D.base.seedB) ∧ Sp.toMat (O.decode D.base.seedB) ∈ S :=
    ⟨Sp.decode_wf _, by
      rw [Sp.toMat_decode]
      exact Submonoid.subset_closure (Set.mem_insert_of_mem _ rfl)⟩
  obtain ⟨hs0, hok0⟩ := initRegs_regs Sp S hA hB D.base.nregs
  obtain ⟨hs, hok⟩ := run_regs Sp S D.base.prog hok0 (by rw [hs0]; exact hprog)
  set R := O.run D.base.prog
    (O.initRegs (O.decode D.base.seedA) (O.decode D.base.seedB) D.base.nregs)
  rw [hs0] at hs
  obtain ⟨hw₁, hS₁⟩ := hok D.inv₁ (by rw [hs]; exact hinv₁)
  obtain ⟨hw₂, hS₂⟩ := hok D.inv₂ (by rw [hs]; exact hinv₂)
  set T₁ := R[D.inv₁]!
  set T₂ := R[D.inv₂]!
  have hsq : ∀ {T : M}, Sp.WF T → O.eq (O.mul T T) O.one = true →
      Sp.toMat T * Sp.toMat T = 1 := fun {T} hT hT2 => by
    have := Sp.toMat_eq (Sp.mul_wf hT hT) Sp.one_wf hT2
    rwa [Sp.toMat_mul hT hT, Sp.toMat_one] at this
  have hTT₁ := hsq hw₁ hT₁
  have hTT₂ := hsq hw₂ hT₂
  have hc₁₂ : Sp.toMat T₁ * Sp.toMat T₂ = Sp.toMat T₂ * Sp.toMat T₁ := by
    have := Sp.toMat_eq (Sp.mul_wf hw₁ hw₂) (Sp.mul_wf hw₂ hw₁) hT₁₂
    rwa [Sp.toMat_mul hw₁ hw₂, Sp.toMat_mul hw₂ hw₁] at this
  have hTne : Sp.toMat T₁ ≠ 1 := by
    intro h1
    obtain ⟨k, -, hk⟩ := List.any_eq_true.1 hmov
    apply Sp.toVec_ne hk
    rw [Sp.toVec_vmul (Sp.unit_wf k) hw₁, h1, Matrix.vecMul_one]
  have hsq' : ∀ {T : Matrix (Fin d) (Fin d) (ZMod p)} (hT : T ∈ S), T * T = 1 →
      (⟨T, hT⟩ : S) ^ 2 = 1 := fun {T} hT hTT => Subtype.ext (by
    rw [SubmonoidClass.coe_pow, sq]
    exact hTT)
  let τ₁ : Sˣ := Units.ofPowEqOne _ 2 (hsq' hS₁ hTT₁) (by norm_num)
  let τ₂ : Sˣ := Units.ofPowEqOne _ 2 (hsq' hS₂ hTT₂) (by norm_num)
  have hτ₁ : ((τ₁ : S) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat T₁ := rfl
  have hτ₂ : ((τ₂ : S) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat T₂ := rfl
  set P := Subgroup.closure ({τ₁, τ₂} : Set Sˣ)
  have hτ₁P : τ₁ ∈ P := Subgroup.subset_closure (Set.mem_insert _ _)
  have hτ₂P : τ₂ ∈ P := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  have hP : P ≠ ⊥ := by
    intro hbot
    have h1 := hτ₁P
    rw [hbot, Subgroup.mem_bot] at h1
    apply hTne
    rw [← hτ₁, h1]
    rfl
  have hP2 : IsPGroup 2 P :=
    FourGroup.isPGroup_closure_pair (Units.pow_ofPowEqOne _ _) (Units.pow_ofPowEqOne _ _)
      (Units.ext (Subtype.ext hc₁₂))
  set xs := D.base.outs.map fun r => R[r]!
  have hxs : ∀ X ∈ xs, Sp.WF X ∧ Sp.toMat X ∈ S := by
    intro X hX
    obtain ⟨r, hr, rfl⟩ := List.mem_map.1 hX
    exact hok r (by rw [hs]; exact of_decide_eq_true (List.all_eq_true.1 houts r hr))
  have hw : ∀ X ∈ xs, Sp.WF X := fun X hX => (hxs X hX).1
  unfold Ops.elemOK at hel
  simp only [Bool.and_eq_true] at hel
  obtain ⟨⟨hcube, hcomms⟩, hker⟩ := hel
  have hpair := Sp.pairwise_of_commsOK hw hcomms
  have hcubeM : ∀ i : Fin xs.length, Sp.toMat xs[i] ^ 3 = 1 := fun i => by
    have hX := hw _ (List.getElem_mem i.isLt)
    have := Sp.toMat_eq (Sp.mul_wf (Sp.mul_wf hX hX) hX) Sp.one_wf
      (List.all_eq_true.1 hcube _ (List.getElem_mem i.isLt))
    rwa [Sp.toMat_mul (Sp.mul_wf hX hX) hX, Sp.toMat_mul hX hX, Sp.toMat_one, ← pow_two,
      ← pow_succ] at this
  have hconjM : ∀ i : Fin xs.length, ∀ T ∈ ({T₁, T₂} : Set M),
      Sp.toMat xs[i] * Sp.toMat T = Sp.toMat T₁ * Sp.toMat xs[i] ∨
        Sp.toMat xs[i] * Sp.toMat T = Sp.toMat T₂ * Sp.toMat xs[i] ∨
          Sp.toMat xs[i] * Sp.toMat T = Sp.toMat T₁ * Sp.toMat T₂ * Sp.toMat xs[i] :=
    fun i T hT => by
      have hmem : xs[i] ∈ xs := List.getElem_mem i.isLt
      obtain ⟨r, hr, hrx⟩ := List.mem_map.1 hmem
      have hX := hw _ hmem
      have hc := List.all_eq_true.1 hconj r hr
      rw [Bool.and_eq_true] at hc
      rcases hT with rfl | rfl
      · exact toMat_of_conjOK Sp hX hw₁ hw₁ hw₂ (by rw [← hrx]; exact hc.1)
      · exact toMat_of_conjOK Sp hX hw₂ hw₁ hw₂ (by rw [← hrx]; exact hc.2)
  set N := Subgroup.normalizer (P : Set Sˣ)
  have h3 : ∀ i : Fin xs.length, (⟨Sp.toMat xs[i], (hxs _ (List.getElem_mem i.isLt)).2⟩ : S) ^ 3
      = 1 := fun i => Subtype.ext (by rw [SubmonoidClass.coe_pow]; exact hcubeM i)
  let w : Fin xs.length → Sˣ := fun i => Units.ofPowEqOne _ 3 (h3 i) (by norm_num)
  have hwN : ∀ i, w i ∈ N := fun i => by
    refine FourGroup.mem_normalizer_closure_of_pow_three (Units.pow_ofPowEqOne _ _) ?_
    have key : ∀ (τ : Sˣ) (T : M), T ∈ ({T₁, T₂} : Set M) →
        ((τ : S) : Matrix (Fin d) (Fin d) (ZMod p)) = Sp.toMat T → w i * τ * (w i)⁻¹ ∈ P := by
      intro τ T hT hτT
      have hcase : ∀ σ ∈ P, ((σ : S) : Matrix (Fin d) (Fin d) (ZMod p)) * Sp.toMat xs[i] =
          Sp.toMat xs[i] * Sp.toMat T → w i * τ * (w i)⁻¹ ∈ P := by
        intro σ hσ he
        have e : w i * τ = σ * w i := Units.ext (Subtype.ext (by
          change Sp.toMat xs[i] * ((τ : S) : Matrix (Fin d) (Fin d) (ZMod p)) =
            ((σ : S) : Matrix (Fin d) (Fin d) (ZMod p)) * Sp.toMat xs[i]
          rw [hτT]
          exact he.symm))
        rw [e, mul_inv_cancel_right]
        exact hσ
      rcases hconjM i T hT with he | he | he
      · exact hcase τ₁ hτ₁P (by rw [hτ₁, he])
      · exact hcase τ₂ hτ₂P (by rw [hτ₂, he])
      · refine hcase (τ₁ * τ₂) (P.mul_mem hτ₁P hτ₂P) ?_
        simp only [Units.val_mul, Submonoid.coe_mul]
        rw [hτ₁, hτ₂, he]
    rintro x (rfl | rfl)
    · exact key τ₁ T₁ (Set.mem_insert _ _) hτ₁
    · exact key τ₂ T₂ (Set.mem_insert_of_mem _ rfl) hτ₂
  let u : Fin xs.length → N := fun i => ⟨w i, hwN i⟩
  let f : N →* Matrix (Fin d) (Fin d) (ZMod p) :=
    S.subtype.comp ((Units.coeHom S).comp N.subtype)
  have hf : ∀ i (n : ℕ), f (u i ^ n) = Sp.toMat xs[i] ^ n := fun i n => by
    rw [map_pow]
    rfl
  obtain ⟨E', hE', hE'c⟩ := exists_elemAbelian_of_commuting u
    (fun i => Subtype.ext (Units.pow_ofPowEqOne (h3 i) (by norm_num)))
    (fun i j => by
      apply Subtype.ext
      apply Units.ext
      apply Subtype.ext
      change Sp.toMat xs[i] * Sp.toMat xs[j] = Sp.toMat xs[j] * Sp.toMat xs[i]
      rcases lt_trichotomy i j with hij | rfl | hij
      · exact List.pairwise_iff_getElem.1 hpair i j i.isLt j.isLt hij
      · rfl
      · exact (List.pairwise_iff_getElem.1 hpair j i j.isLt i.isLt hij).symm)
    (fun a ha hprod => by
      refine Sp.ne_one_of_kerOK hw hker a ha ?_
      have := congrArg f hprod
      rwa [map_list_prod, List.map_ofFn, map_one, Function.comp_def,
        funext fun i => hf i _] at this)
  refine ⟨P, E'.map N.subtype, hP, hP2, CFSG.SectionRank.isElemAbelian_map hE' _, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective N.subtype_injective, hE'c, List.length_map]
  · rintro _ ⟨y, -, rfl⟩
    exact y.2

theorem le_localRank_three_of_v4Check [Inhabited M] (D : V4Data)
    (h : V4Data.check O D = true)
    [Finite (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ] :
    D.base.outs.length ≤ CFSG.Assembly.RankThreeEven.localRank 3
      (NativeSporadic.seedMonoid p d 1 D.base.seedA D.base.seedB)ˣ := by
  obtain ⟨P, E, hP, hP2, hE, hc, hEN⟩ := exists_of_v4Check Sp D h
  exact le_localRank_of_le_normalizer Nat.prime_three hP hP2 hE hc hEN

end OpsSpec

end CFSG.RankThree.PartTwo.Census
