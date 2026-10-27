module

public import CFSG.RankThree.GF2n.Smith81.Orth52Glue
public import CFSG.RankThree.GF2n.Smith81.OrthMaxTS
public import CFSG.RankThree.GF2n.Smith81.OrthTensorAlg
public import CFSG.RankThree.GF2n.Stroth80.Sec12CaseVIEquiv
public import CFSG.RankThree.GF2n.Stroth80.Sec12LBFlag

public section

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80
open CFSG.ClassicalGroups.Orthogonal (eichler)
open scoped commutatorElement Matrix

variable {G : Type} [Group G]

section Model

variable {M Q Z : Subgroup G} {K : Type} [Field K] [Finite K] {γ : G → K}
  {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]

theorem width_of_tensor (hD : GlobalModelData M Q Z γ M₀) (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)) :
    Width Q Z (Fintype.card ι) := by
  unfold Width
  have h1 := M₀.card_eq (S := Q) le_rfl hD.reg.V_le
  have h2 : Nat.card (M₀.img Q) = Nat.card M₀.E := by
    refine Nat.card_congr
      { toFun := fun x => x.1
        invFun := fun e => ⟨e, ?_⟩
        left_inv := fun x => rfl
        right_inv := fun e => rfl }
    obtain ⟨x, hx, rfl⟩ := M₀.π_surj e
    exact ⟨x, hx, hx, rfl⟩
  have h3 : Nat.card M₀.E = (Nat.card K ^ Fintype.card ι) * (Nat.card K ^ Fintype.card ι) := by
    rw [Nat.card_congr φ.toEquiv, Nat.card_prod, Nat.card_fun, Nat.card_eq_fintype_card (α := ι)]
  rw [h1, h2, h3, ← hD.card]
  ring

end Model

section Line

variable [Finite G] {M Q Z A : Subgroup G} {K : Type} [Field K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

theorem isLineGen_pi (hcA : Ctx M Q Z A) (hD : GlobalModelData M Q Z γ M₀) {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) : IsLineGen M₀ A (M₀.π a) := by
  obtain ⟨g, hg⟩ := hcA.conj
  have hne : conjSubgroup g Z ≠ Z := by rw [← hg]; exact hcA.ne
  have hle : conjSubgroup g Z ≤ Q := by rw [← hg]; exact hcA.le
  obtain ⟨e, he0, he⟩ := hD.line g hne hle
  rw [← hg] at he
  have haQ : a ∈ Q := hcA.le haA
  have hπa0 : M₀.π a ≠ 0 := by
    intro h0
    have haZ : a ∈ Z := (M₀.π_ker a haQ).mp h0
    have hmem : a ∈ Z ⊓ A := ⟨haZ, haA⟩
    rw [hcA.inf_eq_bot, Subgroup.mem_bot] at hmem
    exact ha1 hmem
  obtain ⟨s₀, hs₀⟩ := (he _).mp (M₀.pi_mem_img haA haQ)
  have hs₀0 : s₀ ≠ 0 := by
    rintro rfl
    exact hπa0 (by rw [hs₀, zero_smul])
  intro v
  rw [he v]
  constructor
  · rintro ⟨s, rfl⟩
    refine ⟨s * s₀⁻¹, ?_⟩
    rw [hs₀, smul_smul, mul_assoc, inv_mul_cancel₀ hs₀0, mul_one]
  · rintro ⟨s, rfl⟩
    exact ⟨s * s₀, by rw [hs₀, smul_smul]⟩

end Line

section Alg

variable {K : Type} [Field K] {ι : Type}

@[expose] noncomputable def orthTensorLin (g : Matrix (Fin 2) (Fin 2) K)
    (o : (ι → K) →ₗ[K] (ι → K)) : (ι → K) × (ι → K) →ₗ[K] (ι → K) × (ι → K) where
  toFun := orthTensor g o
  map_add' p p' := by
    refine Prod.ext ?_ ?_ <;> simp only [orthTensor, Prod.fst_add, Prod.snd_add, map_add] <;> module
  map_smul' c p := by
    refine Prod.ext ?_ ?_ <;> simp only [orthTensor, Prod.smul_fst, Prod.smul_snd, map_smul,
      RingHom.id_apply] <;> module

theorem orthTensor_unipotent (β : K) (o : (ι → K) → (ι → K)) (p : (ι → K) × (ι → K)) :
    orthTensor !![1, β; 0, 1] o p = (o p.1 + β • o p.2, o p.2) := by
  simp [orthTensor]

variable [CharP K 2]

theorem diag_eq_one_of_sq_scalar {g : Matrix (Fin 2) (Fin 2) K} (hdet : g.det = 1)
    (h10 : g 1 0 = 0) {κ : K} (hκ : g * g = κ • 1) : g 0 0 = 1 ∧ g 1 1 = 1 := by
  have e00 : g 0 0 * g 0 0 = κ := by
    have := congrFun (congrFun hκ 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h10] using this
  have e11 : g 1 1 * g 1 1 = κ := by
    have := congrFun (congrFun hκ 1) 1
    simpa [Matrix.mul_apply, Fin.sum_univ_two, h10] using this
  have hd : g 0 0 * g 1 1 = 1 := by
    rw [Matrix.det_fin_two, h10] at hdet
    simpa using hdet
  have heq : g 0 0 = g 1 1 := by
    have h : g 0 0 ^ 2 = g 1 1 ^ 2 := by rw [sq, sq, e00, e11]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  have h1 : g 0 0 ^ 2 = 1 ^ 2 := by
    rw [sq, one_pow]
    nth_rewrite 2 [heq]
    exact hd
  have h00 : g 0 0 = 1 := by
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h | h
    · exact h
    · rwa [CharTwo.neg_eq] at h
  exact ⟨h00, heq ▸ h00⟩

end Alg

section Act

variable [Finite G] {M Q Z B A : Subgroup G} {K : Type} [Field K]
  {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι] [DecidableEq ι]
  {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem tensor_mem_img_of_fix (hcA : Ctx M Q Z A) {a : G} (hline : IsLineGen M₀ A (M₀.π a))
    {u : ι → K} (hpa : φ (M₀.π a) = (u, 0)) {s : G} (hs : s ∈ M) {g : Matrix (Fin 2) (Fin 2) K}
    {o : (ι → K) → (ι → K)} (hact : ActsAsTensor Q Z M₀ φ s g o)
    (hfix : ∀ c : K, ∃ b : K, orthTensor g o (c • ((u, 0) : (ι → K) × (ι → K))) = b • (u, 0))
    {p : (ι → K) × (ι → K)} (hp : φ.symm p ∈ M₀.img (Q ⊓ QB A)) :
    φ.symm (orthTensor g o p) ∈ M₀.img (Q ⊓ QB A) := by
  have hpa' : φ.symm (u, 0) = M₀.π a := φ.symm_apply_eq.mpr hpa.symm
  have hsC : conjSubgroup s A ≤ A ⊔ Z := by
    refine conj_le_sup_of_line hcA hline hs (T := fun e => φ.symm (orthTensor g o (φ e))) ?_ ?_
    · intro x hx
      apply φ.injective
      rw [hact x hx, LinearEquiv.apply_symm_apply]
    · intro c
      obtain ⟨b, hb⟩ := hfix c
      refine ⟨b, ?_⟩
      simp only [map_smul, hpa, hb, hpa']
  have h := orthTensor_mem_img_inf_QB hcA hs hsC hact hp
  simpa using h

theorem img_stable_sl (hcB : Ctx M Q Z B) (hcA : Ctx M Q Z A) (hD : GlobalModelData M Q Z γ M₀)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) {u : ι → K} {a : G} (haA : a ∈ A)
    (ha1 : a ≠ 1) (hpa : φ (M₀.π a) = (u, 0)) (μ : K) {p : (ι → K) × (ι → K)}
    (hp : φ.symm p ∈ M₀.img (Q ⊓ QB A)) :
    φ.symm (p.1 + μ • p.2, p.2) ∈ M₀.img (Q ⊓ QB A) := by
  obtain ⟨s, hs, hact⟩ := hAct.sl !![1, μ; 0, 1] (by simp [Matrix.det_fin_two])
  have hsM : s ∈ M := (Lgen_le_H0 hcB hs).1
  have h := tensor_mem_img_of_fix hcA (isLineGen_pi hcA hD haA ha1) hpa hsM hact
    (fun c => ⟨c, by simp [orthTensor]⟩) hp
  have e : orthTensor !![1, μ; 0, 1] (id : (ι → K) → (ι → K)) p = (p.1 + μ • p.2, p.2) := by
    simp [orthTensor]
  rwa [e] at h

theorem img_stable_eichler (hcB : Ctx M Q Z B) (hcA : Ctx M Q Z A)
    (hD : GlobalModelData M Q Z γ M₀) (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)))
    {u : ι → K} {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hpa : φ (M₀.π a) = (u, 0))
    {s w : ι → K} (hs : qU s = 0) (hsw : QuadraticMap.polar qU s w = 0)
    (hsu : QuadraticMap.polar qU s u = 0) (hwu : QuadraticMap.polar qU w u = 0)
    {p : (ι → K) × (ι → K)} (hp : φ.symm p ∈ M₀.img (Q ⊓ QB A)) :
    φ.symm (eichler qU s w p.1, eichler qU s w p.2) ∈ M₀.img (Q ⊓ QB A) := by
  obtain ⟨s', hs', hact⟩ := hAct.eich s w hs hsw
  have hsM : s' ∈ M := (Lgen_le_H0 hcB hs').1
  have hu : eichler qU s w u = u :=
    CFSG.ClassicalGroups.Orthogonal.eichler_apply_of_polar_eq_zero
      (by rw [QuadraticMap.polar_comm]; exact hsu) (by rw [QuadraticMap.polar_comm]; exact hwu)
  have h := tensor_mem_img_of_fix hcA (isLineGen_pi hcA hD haA ha1) hpa hsM hact
    (fun c => ⟨c, by simp [orthTensor, hu]⟩) hp
  have e : orthTensor (1 : Matrix (Fin 2) (Fin 2) K) (eichler qU s w) p =
      (eichler qU s w p.1, eichler qU s w p.2) := by
    simp [orthTensor]
  rwa [e] at h

theorem exists_unipotent_act [Finite K] [CharP K 2] (hcA : Ctx M Q Z A)
    (hLA : LB M Q A ≤ Lgen M (LB M Q B)) (hD : GlobalModelData M Q Z γ M₀)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) {u : ι → K} (hu0 : u ≠ 0) {a : G}
    (haA : a ∈ A) (ha1 : a ≠ 1) (hpa : φ (M₀.π a) = (u, 0)) {t : G} (ht : t ∈ LB M Q A) :
    ∃ (β : K) (o : (ι → K) ≃ₗ[K] (ι → K)), (∀ v, qU (o v) = qU v) ∧ o u = u ∧
      ActsAsTensor Q Z M₀ φ t !![1, β; 0, 1] o ∧
      ∀ e ∈ M₀.img (Q ⊓ QB A), ∃ c : K,
        orthTensor !![1, β; 0, 1] o (φ e) - φ e = c • ((u, 0) : (ι → K) × (ι → K)) := by
  classical
  haveI : Nonempty ι := by
    by_contra h
    exact hu0 (funext fun i => (h ⟨i⟩).elim)
  have htM : t ∈ M := hcA.LB_le_M ht
  obtain ⟨g, o, hdet, hiso, hact⟩ := hAct.act t (hLA ht)
  have hline := isLineGen_pi hcA hD haA ha1
  let T : M₀.E →ₗ[K] M₀.E :=
    φ.symm.toLinearMap ∘ₗ orthTensorLin g (o : (ι → K) →ₗ[K] (ι → K)) ∘ₗ φ.toLinearMap
  have hTapp : ∀ e, T e = φ.symm (orthTensor g o (φ e)) := fun e => rfl
  have hT : ∀ x ∈ Q, M₀.π (t * x * t⁻¹) = T (M₀.π x) := by
    intro x hx
    apply φ.injective
    rw [hTapp, LinearEquiv.apply_symm_apply]
    exact hact x hx
  obtain ⟨hTb, hTD⟩ := hcA.LB_act_fix_line hD hline ht hT
  have hfix : orthTensor g o (u, 0) = (u, 0) := by
    have h1 := congrArg φ hTb
    rw [hTapp, LinearEquiv.apply_symm_apply, hpa] at h1
    exact h1
  have hfix' := Prod.ext_iff.mp hfix
  simp only [orthTensor, map_zero, smul_zero, add_zero] at hfix'
  obtain ⟨hu1, hu2⟩ := hfix'
  have hou : o u ≠ 0 := by
    intro h0
    rw [h0, smul_zero] at hu1
    exact hu0 hu1.symm
  have g10 : g 1 0 = 0 := (smul_eq_zero.mp hu2).resolve_right hou
  have hnorm := hcA.conj_mem_Q_of_mem_M htM
  have hsq : ActsAsTensor Q Z M₀ φ (t ^ 2) (g * g)
      ((o : (ι → K) →ₗ[K] (ι → K)) ∘ₗ (o : (ι → K) →ₗ[K] (ι → K))) := by
    rw [sq]
    exact ActsAsTensor.mul (o := (o : (ι → K) →ₗ[K] (ι → K))) (o' := (o : (ι → K) →ₗ[K] (ι → K)))
      hnorm.1 hact hact
  have hone : ActsAsTensor Q Z M₀ φ (t ^ 2) 1 id := ActsAsTensor.of_mem (hcA.sq_mem_Q_of_mem_LB ht)
  have hall := hsq.orthTensor_eq hone
  obtain ⟨κ, -, hκ, -⟩ := exists_scalar_of_orthTensor_eq_self (g * g)
    ((o : (ι → K) →ₗ[K] (ι → K)) ∘ₗ (o : (ι → K) →ₗ[K] (ι → K)))
    (fun p => by rw [hall p, orthTensor_one_id])
  obtain ⟨g00, g11⟩ := diag_eq_one_of_sq_scalar hdet g10 hκ
  have hg : g = !![1, g 0 1; 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g00, g11, g10]
  refine ⟨g 0 1, o, hiso, ?_, hg ▸ hact, ?_⟩
  · rw [g00, one_smul] at hu1
    exact hu1
  · intro e he
    obtain ⟨c, hc⟩ := hTD e he
    refine ⟨c, ?_⟩
    rw [← hg]
    have h2 := congrArg φ hc
    rw [map_sub, map_smul, hpa, hTapp, LinearEquiv.apply_symm_apply] at h2
    exact h2

end Act

section Count

theorem card_le_mul_card_image_of_fibre [Finite G] {P Q : Subgroup G} {α : Type} [DecidableEq α]
    [Fintype P] (f : P → α) (hf : ∀ t t' : P, f t = f t' → (t : G)⁻¹ * t' ∈ Q) :
    Nat.card P ≤ Nat.card Q * (Finset.univ.image f).card := by
  rw [Nat.card_eq_fintype_card, ← Finset.card_univ]
  refine Finset.card_le_mul_card_image Finset.univ (Nat.card Q) fun b _ => ?_
  by_cases hne : (Finset.univ.filter fun a => f a = b).Nonempty
  · obtain ⟨t₀, ht₀⟩ := hne
    have ht₀b : f t₀ = b := (Finset.mem_filter.mp ht₀).2
    calc (Finset.univ.filter fun a => f a = b).card
        = Nat.card ↥(Finset.univ.filter fun a => f a = b) := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ Nat.card Q := by
          refine Nat.card_le_card_of_injective
            (fun t => (⟨(t₀ : G)⁻¹ * (t.1 : G), hf t₀ t.1
              (ht₀b.trans (Finset.mem_filter.mp t.2).2.symm)⟩ : Q)) ?_
          intro t t' h
          have h' := congrArg Subtype.val h
          apply Subtype.ext
          apply Subtype.ext
          simpa using h'
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    rw [hne, Finset.card_empty]
    exact Nat.zero_le _

end Count

section Main

variable [Finite G] {M Q Z B A : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ι : Type} [Fintype ι]
  [DecidableEq ι] {qU : QuadraticForm K (ι → K)} {φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)}

theorem exists_unipotent_pairs (hcA : Ctx M Q Z A) (hno : NoA2 Q Z (LB M Q A))
    (hLA : LB M Q A ≤ Lgen M (LB M Q B)) (hD : GlobalModelData M Q Z γ M₀)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) (hn : 1 ≤ Fintype.card ι) {u : ι → K}
    (hu0 : u ≠ 0) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1) (hpa : φ (M₀.π a) = (u, 0)) :
    ∃ Γ : Finset (K × ((ι → K) ≃ₗ[K] (ι → K))),
      Nat.card K ^ (Fintype.card ι - 1) ≤ Γ.card ∧
      ∀ t ∈ Γ, (∀ v, qU (t.2 v) = qU v) ∧ t.2 u = u ∧
        ∀ e ∈ M₀.img (Q ⊓ QB A), ∃ c : K,
          (t.2 (φ e).1 + t.1 • t.2 (φ e).2 - (φ e).1, t.2 (φ e).2 - (φ e).2) =
            c • ((u, 0) : (ι → K) × (ι → K)) := by
  classical
  have hdata : ∀ t : LB M Q A, ∃ r : K × ((ι → K) ≃ₗ[K] (ι → K)), (∀ v, qU (r.2 v) = qU v) ∧
      r.2 u = u ∧ ActsAsTensor Q Z M₀ φ t !![1, r.1; 0, 1] r.2 ∧
      ∀ e ∈ M₀.img (Q ⊓ QB A), ∃ c : K,
        orthTensor !![1, r.1; 0, 1] r.2 (φ e) - φ e = c • ((u, 0) : (ι → K) × (ι → K)) := by
    intro t
    obtain ⟨β, o, h1, h2, h3, h4⟩ := exists_unipotent_act hcA hLA hD hAct hu0 haA ha1 hpa t.2
    exact ⟨(β, o), h1, h2, h3, h4⟩
  choose f hfiso hfu hfact hfD using hdata
  haveI : Fintype (LB M Q A) := Fintype.ofFinite _
  have hw := width_of_tensor hD φ
  have hcard33 : Nat.card (LB M Q A) = Nat.card Q * Nat.card K ^ (Fintype.card ι - 1) := by
    rcases stroth_3_3 hcA hw hn with h | ⟨a', ha', hA2⟩
    · rw [h, hD.card]
    · exact absurd hA2 (hno a' ha')
  have hinj : ∀ t t' : LB M Q A, f t = f t' → (t : G)⁻¹ * t' ∈ Q := by
    intro t t' htt
    have htM : (t : G) ∈ M := hcA.LB_le_M t.2
    have ht'M : (t' : G) ∈ M := hcA.LB_le_M t'.2
    have hgg' : (!![1, (f t).1; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, -(f t).1; 0, 1] = 1 := by
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]
    have hg'g : (!![1, -(f t).1; 0, 1] : Matrix (Fin 2) (Fin 2) K) * !![1, (f t).1; 0, 1] = 1 :=
      mul_eq_one_comm.mp hgg'
    have hinv := ActsAsTensor.inv (hcA.conj_mem_Q_of_mem_M htM).2 (hfact t) hgg'
    have hact' : ActsAsTensor Q Z M₀ φ (t' : G) !![1, (f t).1; 0, 1] (f t).2 := by
      have h := hfact t'
      rw [← htt] at h
      exact h
    have hmul := ActsAsTensor.mul (o := ((f t).2.symm : (ι → K) →ₗ[K] (ι → K)))
      (o' := ((f t).2 : (ι → K) →ₗ[K] (ι → K))) (hcA.conj_mem_Q_of_mem_M ht'M).1 hinv hact'
    refine mem_Q_of_pi_conj_eq (M₀ := M₀) hcA.hyp (M.mul_mem (M.inv_mem htM) ht'M) fun x hx => ?_
    apply φ.injective
    rw [hmul x hx, hg'g, orthTensor_one_linear]
    simp
  refine ⟨Finset.univ.image f, ?_, ?_⟩
  · have h := card_le_mul_card_image_of_fibre (P := LB M Q A) (Q := Q) f hinj
    rw [hcard33] at h
    exact Nat.le_of_mul_le_mul_left h Nat.card_pos
  · intro r hr
    obtain ⟨t, -, rfl⟩ := Finset.mem_image.mp hr
    refine ⟨hfiso t, hfu t, fun e he => ?_⟩
    obtain ⟨c, hc⟩ := hfD t e he
    refine ⟨c, ?_⟩
    rw [orthTensor_unipotent] at hc
    rw [← hc]
    refine Prod.ext ?_ ?_ <;> simp [sub_eq_add_neg, add_assoc]

theorem img_inf_QB_eq_perpLine (hcB : Ctx M Q Z B) (hcA : Ctx M Q Z A)
    (hno : NoA2 Q Z (LB M Q A)) (hLA : LB M Q A ≤ Lgen M (LB M Q B))
    (hD : GlobalModelData M Q Z γ M₀) (hF : OrthPreFrame Q Z M₀ qU φ)
    (hAct : OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B))) (hn : 4 ≤ Fintype.card ι) {u : ι → K}
    (hu0 : u ≠ 0) (hqu : qU u = 0) {a : G} (haA : a ∈ A) (ha1 : a ≠ 1)
    (hpa : φ (M₀.π a) = (u, 0)) :
    ∀ e : M₀.E, e ∈ M₀.img (Q ⊓ QB A) ↔ φ e ∈ perpLine qU u := by
  classical
  have hn' : 2 < Fintype.card ι := by omega
  have hw := width_of_tensor hD φ
  obtain ⟨W, hW, hWn, -, hWs⟩ := hcA.lagr hw hn' hno hD
  have hmemD : ∀ p, p ∈ W.map (φ : M₀.E →ₗ[K] (ι → K) × (ι → K)) ↔
      φ.symm p ∈ M₀.img (Q ⊓ QB A) := fun p => by
    rw [hW]
    exact Submodule.mem_map_equiv W (e := φ)
  have hq : 4 ≤ Nat.card K := by
    rw [hD.card]
    exact hcB.hyp.q4
  have huD : ((u, 0) : (ι → K) × (ι → K)) ∈ W.map (φ : M₀.E →ₗ[K] (ι → K) × (ι → K)) := by
    rw [hmemD, φ.symm_apply_eq.mpr hpa.symm]
    exact M₀.pi_mem_img (Subgroup.mem_inf.mpr ⟨hcA.le haA, hcA.B_le_QB haA⟩) (hcA.le haA)
  have hts : ∀ p ∈ W.map (φ : M₀.E →ₗ[K] (ι → K) × (ι → K)),
      QuadraticMap.polar qU p.1 p.2 = 0 := by
    intro p hp
    have h1 := hWs _ ((hW _).mp ((hmemD p).mp hp))
    rwa [hF.qf, LinearEquiv.apply_symm_apply] at h1
  have hdim : Fintype.card ι ≤ Module.finrank K (W.map (φ : M₀.E →ₗ[K] (ι → K) × (ι → K))) := by
    have := LinearEquiv.finrank_map_eq φ W
    omega
  obtain ⟨Γ, hΓcard, hΓ⟩ := exists_unipotent_pairs hcA hno hLA hD hAct (by omega) hu0 haA ha1 hpa
  have hDeq := eq_perpLine_of_stable hF.nondeg hn hq hu0 hqu huD hts hdim
    (fun μ p hp => (hmemD _).mpr
      (img_stable_sl hcB hcA hD hAct haA ha1 hpa μ ((hmemD p).mp hp)))
    (fun s w hs hsw hsu hwu p hp => (hmemD _).mpr
      (img_stable_eichler hcB hcA hD hAct haA ha1 hpa hs hsw hsu hwu ((hmemD p).mp hp)))
    ⟨Γ, hΓcard, fun t ht => by
      obtain ⟨h1, h2, h3⟩ := hΓ t ht
      refine ⟨h1, h2, fun p hp => ?_⟩
      simpa using h3 (φ.symm p) ((hmemD p).mp hp)⟩
  intro e
  rw [← hDeq, hmemD, LinearEquiv.symm_apply_apply]

end Main

end CFSG.RankThree.GF2n.Smith81
