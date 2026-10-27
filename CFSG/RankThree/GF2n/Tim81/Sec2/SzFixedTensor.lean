module

public import CFSG.RankThree.GF2n.Tim81.Sec2.SzFixedCentre

public section

namespace CFSG.RankThree.GF2n.Tim81.Sec2

open CFSG.Blueprint CFSG.LieType.Ree CFSG.Quasithin CFSG.Quasithin.B45Sz CFSG.Quasithin.B42Sp4
  CFSG.QuasithinUnique.Setup.X7 CFSG.QuasithinUnique.Setup.X7b
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain

namespace SzTensor

section Split

variable {k : Type} [Field k]
variable {K : Type} [Field K] [CharP K 2] [Finite K] [Fintype K]
variable [Algebra K k]

private def subtypeBEquiv {Ω B : Finset ℕ} (hB : B ⊆ Ω) :
    {i : Ω // (i : ℕ) ∈ B} ≃ B :=
  Equiv.subtypeSubtypeEquivSubtype (p := fun i : ℕ => i ∈ Ω) (q := fun i : ℕ => i ∈ B)
    (fun {i} h => hB h)

@[simp] private theorem subtypeBEquiv_apply {Ω B : Finset ℕ} (hB : B ⊆ Ω)
    (i : {i : Ω // (i : ℕ) ∈ B}) :
    subtypeBEquiv hB i = ⟨i.1.1, i.2⟩ := rfl

@[simp] private theorem subtypeBEquiv_symm_apply {Ω B : Finset ℕ} (hB : B ⊆ Ω) (i : B) :
    (subtypeBEquiv hB).symm i = ⟨⟨i.1, hB i.2⟩, i.2⟩ := rfl

private def subtypeCEquiv {Ω B : Finset ℕ} (hB : B ⊆ Ω) :
    {i : Ω // (i : ℕ) ∉ B} ≃ ↥(Ω \ B) :=
  (Equiv.subtypeEquivRight (fun i : Ω => by
      rw [Finset.mem_sdiff]
      exact ⟨fun h => ⟨i.2, h⟩, fun h => h.2⟩)).trans
    (Equiv.subtypeSubtypeEquivSubtype (p := fun i : ℕ => i ∈ Ω)
      (q := fun i : ℕ => i ∈ Ω \ B) (fun {i} h => (Finset.mem_sdiff.mp h).1))

@[simp] private theorem subtypeCEquiv_apply {Ω B : Finset ℕ} (hB : B ⊆ Ω)
    (i : {i : Ω // (i : ℕ) ∉ B}) :
    subtypeCEquiv hB i = ⟨i.1.1, Finset.mem_sdiff.mpr ⟨i.1.2, i.2⟩⟩ := by
  apply Subtype.ext
  rfl

@[simp] private theorem subtypeCEquiv_symm_apply {Ω B : Finset ℕ} (hB : B ⊆ Ω)
    (j : ↥(Ω \ B)) :
    (subtypeCEquiv hB).symm j =
      ⟨⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩, (Finset.mem_sdiff.mp j.2).2⟩ := by
  apply Subtype.ext
  apply Subtype.ext
  rfl

private noncomputable def coordinateSplit {Ω B : Finset ℕ} (hB : B ⊆ Ω) :
    (Ω → Fin 4) ≃ (B → Fin 4) × (↥(Ω \ B) → Fin 4) := by
  classical
  exact (Equiv.piEquivPiSubtypeProd (fun i : Ω => (i : ℕ) ∈ B) (fun _ => Fin 4)).trans
    (Equiv.prodCongr
      (Equiv.arrowCongr (subtypeBEquiv hB) (Equiv.refl (Fin 4)))
      (Equiv.arrowCongr (subtypeCEquiv hB) (Equiv.refl (Fin 4))))

private theorem coordinateSplit_fst {Ω B : Finset ℕ} (hB : B ⊆ Ω) (x : Ω → Fin 4) :
    (coordinateSplit hB x).1 = fun i : B => x ⟨i.1, hB i.2⟩ := by
  classical
  funext i
  simp [coordinateSplit, Equiv.arrowCongr, Equiv.piEquivPiSubtypeProd]

private theorem coordinateSplit_snd {Ω B : Finset ℕ} (hB : B ⊆ Ω) (x : Ω → Fin 4) :
    (coordinateSplit hB x).2 =
      fun j : ↥(Ω \ B) => x ⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩ := by
  classical
  funext j
  simp [coordinateSplit, Equiv.arrowCongr, Equiv.piEquivPiSubtypeProd]

private theorem coordinateSplit_symm_apply {Ω B : Finset ℕ} (hB : B ⊆ Ω)
    (f : B → Fin 4) (g : ↥(Ω \ B) → Fin 4) :
    (coordinateSplit hB).symm (f, g) = fun i : Ω =>
      if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
      else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩ := by
  classical
  funext i
  simp [coordinateSplit, Equiv.arrowCongr, Equiv.piEquivPiSubtypeProd]

private theorem coordinateSplit_symm_fst {Ω B : Finset ℕ} (hB : B ⊆ Ω)
    (f : B → Fin 4) (g : ↥(Ω \ B) → Fin 4) :
    (fun i : B => (coordinateSplit hB).symm (f, g) ⟨i.1, hB i.2⟩) = f := by
  have h := congrArg Prod.fst ((coordinateSplit hB).apply_symm_apply (f, g))
  rw [coordinateSplit_fst] at h
  simpa using h

private theorem coordinateSplit_symm_snd {Ω B : Finset ℕ} (hB : B ⊆ Ω)
    (f : B → Fin 4) (g : ↥(Ω \ B) → Fin 4) :
    (fun j : ↥(Ω \ B) =>
      (coordinateSplit hB).symm (f, g) ⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩) = g := by
  have h := congrArg Prod.snd ((coordinateSplit hB).apply_symm_apply (f, g))
  rw [coordinateSplit_snd] at h
  simpa using h

@[expose] def kronFun {Ω B : Finset ℕ} (hB : B ⊆ Ω) (u : (B → Fin 4) → k)
    (v : (↥(Ω \ B) → Fin 4) → k) : (Ω → Fin 4) → k :=
  fun x => u (fun i : B => x ⟨i.1, hB i.2⟩) *
    v (fun j : ↥(Ω \ B) => x ⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩)

theorem prod_merge_split {Ω B : Finset ℕ} (hB : B ⊆ Ω) (z : antiSp K) (x : Ω → Fin 4)
    (f : B → Fin 4) (g : ↥(Ω \ B) → Fin 4) :
    (∏ i : ↥Ω, natRepS (F := K) k (i : ℕ) z (x i)
      (if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
       else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩)) =
      (∏ i : ↥B, natRepS (F := K) k (i : ℕ) z (x ⟨i.1, hB i.2⟩) (f i)) *
      (∏ j : ↥(Ω \ B), natRepS (F := K) k (j : ℕ) z
        (x ⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩) (g j)) := by
  classical
  let Ψ : ℕ → k := fun i => if hi : i ∈ Ω then
    natRepS (F := K) k i z (x ⟨i, hi⟩)
      (if h : i ∈ B then f ⟨i, h⟩ else g ⟨i, Finset.mem_sdiff.mpr ⟨hi, h⟩⟩) else 1
  have hstep : ∀ (i : ↥Ω), natRepS (F := K) k (i : ℕ) z (x i)
      (if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
       else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩) = Ψ i := by
    intro i
    simp only [Ψ]
    rw [dif_pos i.2]
  have hL : (∏ i : ↥Ω, natRepS (F := K) k (i : ℕ) z (x i)
      (if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
       else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩)) = Ω.prod Ψ := by
    have h1 : (∏ i : ↥Ω, natRepS (F := K) k (i : ℕ) z (x i)
        (if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
         else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩)) =
        ∏ i : ↥Ω, Ψ i := Finset.prod_congr rfl (fun i _ => hstep i)
    rw [h1]
    exact Finset.prod_coe_sort Ω Ψ
  have hB' : (∏ i : ↥B, natRepS (F := K) k (i : ℕ) z (x ⟨i.1, hB i.2⟩) (f i)) =
      B.prod Ψ := by
    have h1 : (∏ i : ↥B, natRepS (F := K) k (i : ℕ) z (x ⟨i.1, hB i.2⟩) (f i)) =
        ∏ i : ↥B, Ψ i := Finset.prod_congr rfl (fun i _ => by
      simp only [Ψ]
      rw [dif_pos (hB i.2), dif_pos i.2])
    rw [h1]
    exact Finset.prod_coe_sort B Ψ
  have hC' : (∏ j : ↥(Ω \ B), natRepS (F := K) k (j : ℕ) z
        (x ⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩) (g j)) = (Ω \ B).prod Ψ := by
    have h1 : (∏ j : ↥(Ω \ B), natRepS (F := K) k (j : ℕ) z
        (x ⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩) (g j)) = ∏ j : ↥(Ω \ B), Ψ j :=
      Finset.prod_congr rfl (fun i _ => by
        simp only [Ψ]
        rw [dif_pos (Finset.mem_sdiff.mp i.2).1, dif_neg (Finset.mem_sdiff.mp i.2).2])
    rw [h1]
    exact Finset.prod_coe_sort (Ω \ B) Ψ
  calc (∏ i : ↥Ω, natRepS (F := K) k (i : ℕ) z (x i)
        (if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
         else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩))
      = Ω.prod Ψ := hL
    _ = (B.prod Ψ) * ((Ω \ B).prod Ψ) := by
        rw [← Finset.prod_sdiff hB, mul_comm]
    _ = (∏ i : ↥B, natRepS (F := K) k (i : ℕ) z (x ⟨i.1, hB i.2⟩) (f i)) *
        (∏ j : ↥(Ω \ B), natRepS (F := K) k (j : ℕ) z
          (x ⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩) (g j)) := by rw [hB', hC']

@[expose] def extractLM {Ω B : Finset ℕ} (hB : B ⊆ Ω)
    (φ : ((↥(Ω \ B) → Fin 4) → k) →ₗ[k] k) :
    ((Ω → Fin 4) → k) →ₗ[k] ((B → Fin 4) → k) where
  toFun w := fun f => φ (fun g => w (fun i : Ω =>
    if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
    else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩))
  map_add' w w' := by
    funext f
    change φ ((fun g => w (fun i : Ω =>
        if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
        else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩)) +
      (fun g => w' (fun i : Ω =>
        if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
        else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩))) = _ + _
    rw [map_add]
  map_smul' c w := by
    funext f
    change φ (c • (fun g => w (fun i : Ω =>
        if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
        else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩))) =
      c • φ (fun g => w (fun i : Ω =>
        if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
        else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩))
    rw [map_smul]

theorem extractLM_kronFun {Ω B : Finset ℕ} (hB : B ⊆ Ω)
    (φ : ((↥(Ω \ B) → Fin 4) → k) →ₗ[k] k)
    (u : (B → Fin 4) → k) (v : (↥(Ω \ B) → Fin 4) → k) :
    extractLM hB φ (kronFun hB u v) = φ v • u := by
  funext f
  have h1 : (fun g => kronFun hB u v (fun i : Ω =>
      if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
      else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩)) = fun g => u f * v g := by
    funext g
    simp only [kronFun]
    have hf : (fun i : B => (fun i : Ω =>
        if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
        else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩) ⟨i.1, hB i.2⟩) = f := by
      funext i
      simp
    have hg : (fun j : ↥(Ω \ B) => (fun i : Ω =>
        if h : (i : ℕ) ∈ B then f ⟨i.1, h⟩
        else g ⟨i.1, Finset.mem_sdiff.mpr ⟨i.2, h⟩⟩) ⟨j.1,
          (Finset.mem_sdiff.mp j.2).1⟩) = g := by
      funext j
      change (if h : (j : ℕ) ∈ B then f ⟨j.1, h⟩
        else g ⟨j.1, Finset.mem_sdiff.mpr ⟨(Finset.mem_sdiff.mp j.2).1, h⟩⟩) = g j
      rw [dif_neg (Finset.mem_sdiff.mp j.2).2]
    rw [hf, hg]
  have h2 : (fun g => u f * v g) = u f • v := by
    funext g
    simp
  simp only [extractLM, LinearMap.coe_mk, AddHom.coe_mk, h1, h2, map_smul, Pi.smul_apply,
    smul_eq_mul]
  exact mul_comm _ _

@[expose] def evalLM {Ω B : Finset ℕ} (g : ↥(Ω \ B) → Fin 4) :
    ((↥(Ω \ B) → Fin 4) → k) →ₗ[k] k :=
  { toFun := fun v => v g
    map_add' := fun v v' => rfl
    map_smul' := fun c v => rfl }

theorem evalLM_apply {Ω B : Finset ℕ} (g : ↥(Ω \ B) → Fin 4)
    (v : (↥(Ω \ B) → Fin 4) → k) :
    evalLM g v = v g := rfl

theorem tensorRepS_mulVec_kronFun {Ω B : Finset ℕ} (hB : B ⊆ Ω) (z : antiSp K)
    (u : (B → Fin 4) → k) (v : (↥(Ω \ B) → Fin 4) → k) :
    (tensorRepS (F := K) k Ω z).mulVec (kronFun hB u v) =
      kronFun hB ((tensorRepS (F := K) k B z).mulVec u)
        ((tensorRepS (F := K) k (Ω \ B) z).mulVec v) := by
  funext x
  have hL : (tensorRepS (F := K) k Ω z).mulVec (kronFun hB u v) x =
      ∑ p : (B → Fin 4) × (↥(Ω \ B) → Fin 4),
        (∏ i : ↥Ω, natRepS (F := K) k (i : ℕ) z (x i)
          ((coordinateSplit hB).symm p i)) * (u p.1 * v p.2) := by
    rw [Matrix.mulVec, dotProduct]
    rw [(Equiv.sum_comp (coordinateSplit hB).symm (fun x' =>
      tensorRepS (F := K) k Ω z x x' * kronFun hB u v x')).symm]
    refine Finset.sum_congr rfl (fun p _ => ?_)
    simp only [tensorRepS_apply, kronFun, coordinateSplit_symm_fst, coordinateSplit_symm_snd]
  have hR : kronFun hB ((tensorRepS (F := K) k B z).mulVec u)
        ((tensorRepS (F := K) k (Ω \ B) z).mulVec v) x =
      (∑ f : ↥B → Fin 4, (∏ i : ↥B,
          natRepS (F := K) k (i : ℕ) z (x ⟨i.1, hB i.2⟩) (f i)) * u f) *
      (∑ g : ↥(Ω \ B) → Fin 4, (∏ j : ↥(Ω \ B),
          natRepS (F := K) k (j : ℕ) z (x ⟨j.1, (Finset.mem_sdiff.mp j.2).1⟩) (g j)) * v g) := by
    simp only [kronFun, Matrix.mulVec, dotProduct, tensorRepS_apply]
  rw [hL, hR, Finset.sum_mul_sum]
  rw [Fintype.sum_prod_type]
  exact Finset.sum_congr rfl (fun f _ => Finset.sum_congr rfl (fun g _ => by
    rw [coordinateSplit_symm_apply hB f g]
    rw [prod_merge_split hB z x f g]
    ring))

theorem kronFun_mem_fixedSub {a : ℕ}
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {Ω : Finset ℕ} (B : Finset ℕ) (hB : B ⊆ Ω)
    {u : (B → Fin 4) → k} {v : (↥(Ω \ B) → Fin 4) → k}
    (hu : u ∈ fixedSub (matRep (szT k hK B)) (szZ a K))
    (hv : v ∈ fixedSub (matRep (szT k hK (Ω \ B))) (szZ a K)) :
    kronFun hB u v ∈ fixedSub (matRep (szT k hK Ω)) (szZ a K) := by
  classical
  rw [mem_fixedSub] at hu hv ⊢
  intro z hz
  have hu' : (tensorRepS (F := K) k B (szIncl hK z)).mulVec u = u := by
    have h := hu z hz
    rwa [matRep_apply, szT_apply] at h
  have hv' : (tensorRepS (F := K) k (Ω \ B) (szIncl hK z)).mulVec v = v := by
    have h := hv z hz
    rwa [matRep_apply, szT_apply] at h
  rw [matRep_apply, szT_apply, tensorRepS_mulVec_kronFun, hu', hv']

end Split

end SzTensor

end CFSG.RankThree.GF2n.Tim81.Sec2
