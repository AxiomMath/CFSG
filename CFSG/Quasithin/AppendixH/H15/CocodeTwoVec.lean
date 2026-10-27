module

public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

namespace CFSG.ASVolI.AppH

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Monster.Code

variable {d : ℕ} {a b : Fin 24} {O : Finset (Fin 24)} {Tr S : Finset (Finset (Fin 24))}
  {B : Finset (Fin 24)} {T₀ Γ : Subgroup S24} {V : Type} [CommGroup V] {ρ : ↥Γ →* MulAut V}
  {β : ↥(⊤ : Subgroup V) →* ↥(mathModel false d a b Γ).sec ⧸
    (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec}

theorem mctx_beta_injective (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) : Function.Injective β := by
  obtain ⟨-, -, -, -, -, -, -, -, hβker, -⟩ := hM.real
  rw [injective_iff_map_eq_one]
  intro u hu
  apply Subtype.ext
  have hmem : (u : V) ∈ (⊥ : Subgroup V) := (hβker u).mp hu
  simpa using (Subgroup.mem_bot.mp hmem)

theorem mctx_beta_surjective (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) : Function.Surjective β := by
  obtain ⟨-, -, -, -, -, -, -, hβsurj, -, -⟩ := hM.real
  exact hβsurj

theorem mctx_finite (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) : Finite V := by
  haveI : Finite (mathModel false d a b Γ).Amb := by
    unfold mathModel FFModel.golaySec
    infer_instance
  haveI : Finite ↥(mathModel false d a b Γ).sec := Subtype.finite
  haveI : Finite (↥(mathModel false d a b Γ).sec ⧸
      (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec) :=
    Finite.of_surjective (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
  haveI : Finite ↥(⊤ : Subgroup V) := Finite.of_injective β (mctx_beta_injective hM)
  exact Finite.of_surjective (⊤ : Subgroup V).subtype
    (fun v => ⟨⟨v, Subgroup.mem_top v⟩, rfl⟩)

theorem isVecOf_unique (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {e : PM24} {v w : V}
    (hv : IsVecOf (mathModel false d a b Γ) β e v) (hw : IsVecOf (mathModel false d a b Γ) β e w) :
    v = w := by
  obtain ⟨he, hv⟩ := hv
  obtain ⟨he', hw⟩ := hw
  have h : (⟨v, Subgroup.mem_top v⟩ : ↥(⊤ : Subgroup V)) = ⟨w, Subgroup.mem_top w⟩ :=
    mctx_beta_injective hM (by rw [hv, hw])
  exact congrArg Subtype.val h

theorem isVecOf_congr (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {e f : PM24} {v : V}
    (hv : IsVecOf (mathModel false d a b Γ) β e v) (hf : f ∈ (mathModel false d a b Γ).sec)
    (hef : e * f⁻¹ ∈ (mathModel false d a b Γ).ker) :
    IsVecOf (mathModel false d a b Γ) β f v := by
  obtain ⟨he, hv⟩ := hv
  refine ⟨hf, ?_⟩
  rw [hv]
  apply QuotientGroup.eq.mpr
  rw [Subgroup.mem_subgroupOf]
  change e⁻¹ * f ∈ (mathModel false d a b Γ).ker
  have hmem : (e * f⁻¹)⁻¹ ∈ (mathModel false d a b Γ).ker :=
    (mathModel false d a b Γ).ker.inv_mem hef
  have h := @mul_inv PM24 _ e f⁻¹
  have h_e : (e * f⁻¹)⁻¹ = e⁻¹ * f :=
    h.trans (congrArg (fun z => e⁻¹ * z) (inv_inv f))
  have hmem' : e⁻¹ * f ∈ (mathModel false d a b Γ).ker := by
    unfold mathModel FFModel.golaySec at hmem ⊢
    exact h_e ▸ hmem
  exact hmem' 

theorem isVecOf_eq_one_iff (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {e : PM24} {v : V}
    (hv : IsVecOf (mathModel false d a b Γ) β e v) :
    v = 1 ↔ e ∈ (mathModel false d a b Γ).ker := by
  obtain ⟨he, hv⟩ := hv
  constructor
  · intro h
    have hsub : (⟨v, Subgroup.mem_top v⟩ : ↥(⊤ : Subgroup V)) = 1 := Subtype.ext h
    have h1 : (QuotientGroup.mk (⟨e, he⟩ : ↥(mathModel false d a b Γ).sec) :
        ↥(mathModel false d a b Γ).sec ⧸
          (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec) = 1 := by
      rw [← hv, hsub, map_one]
    have hmem := (QuotientGroup.eq_one_iff (⟨e, he⟩ : ↥(mathModel false d a b Γ).sec)).mp h1
    rw [Subgroup.mem_subgroupOf] at hmem
    unfold mathModel FFModel.golaySec at hmem ⊢
    simpa using hmem
  · intro hek
    have h1 : (QuotientGroup.mk (⟨e, he⟩ : ↥(mathModel false d a b Γ).sec) :
        ↥(mathModel false d a b Γ).sec ⧸
          (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec) = 1 :=
      (QuotientGroup.eq_one_iff (⟨e, he⟩ : ↥(mathModel false d a b Γ).sec)).mpr
        (by
          rw [Subgroup.mem_subgroupOf]
          unfold mathModel FFModel.golaySec at hek ⊢
          simpa using hek)
    have h2 : β ⟨v, Subgroup.mem_top v⟩ = 1 := by rw [hv, h1]
    have h3 : (⟨v, Subgroup.mem_top v⟩ : ↥(⊤ : Subgroup V)) = 1 := by
      apply mctx_beta_injective hM
      rw [h2, map_one]
    simpa using congrArg Subtype.val h3

theorem isVecOf_act (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {e : PM24} {v : V}
    (hv : IsVecOf (mathModel false d a b Γ) β e v) (g : ↥Γ) :
    IsVecOf (mathModel false d a b Γ) β (G6.permAct 24 (g : S24) e) (ρ g v) := by
  obtain ⟨he, hv⟩ := hv
  obtain ⟨-, -, -, -, -, hsec, -, -, -, hact⟩ := hM.real
  have hacteq : (mathModel false d a b Γ).act g e = G6.permAct 24 (g : S24) e := by
    simp [mathModel, FFModel.golaySec, permSubAct]
  have h := hact g ⟨v, Subgroup.mem_top v⟩ ⟨e, he⟩ (Subgroup.mem_top _) (hsec g e he) hv
  refine ⟨by rw [← hacteq]; exact hsec g e he, ?_⟩
  change β ⟨ρ g v, Subgroup.mem_top (ρ g v)⟩ =
      QuotientGroup.mk ⟨(mathModel false d a b Γ).act g e, hsec g e he⟩ at h
  simpa [hacteq] using h

theorem exists_hom_vecOf (hM : MCtx false d a b O Tr S B T₀ Γ ρ β) {G : Type*} [Group G]
    (s : G →* ↥(mathModel false d a b Γ).sec) :
    ∃ φ : G →* V, ∀ x, IsVecOf (mathModel false d a b Γ) β (s x).1 (φ x) := by
  let eβ : ↥(⊤ : Subgroup V) ≃* (↥(mathModel false d a b Γ).sec ⧸
      (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec) :=
    MulEquiv.ofBijective β ⟨mctx_beta_injective hM, mctx_beta_surjective hM⟩
  let q : ↥(mathModel false d a b Γ).sec →*
      (↥(mathModel false d a b Γ).sec ⧸
        (mathModel false d a b Γ).ker.subgroupOf (mathModel false d a b Γ).sec) :=
    QuotientGroup.mk' _
  let φ : G →* V := (⊤ : Subgroup V).subtype.comp (eβ.symm.toMonoidHom.comp (q.comp s))
  refine ⟨φ, fun x => ⟨(s x).2, ?_⟩⟩
  show β ⟨φ x, Subgroup.mem_top (φ x)⟩ = q (s x)
  have hφ : (⟨φ x, Subgroup.mem_top (φ x)⟩ : ↥(⊤ : Subgroup V)) = eβ.symm (q (s x)) :=
    Subtype.ext rfl
  rw [hφ, ← MulEquiv.ofBijective_apply β ⟨mctx_beta_injective hM, mctx_beta_surjective hM⟩]
  exact eβ.apply_symm_apply (q (s x))

end CFSG.ASVolI.AppH
