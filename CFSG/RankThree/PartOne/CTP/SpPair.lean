module

public import CFSG.RankThree.PartOne.CTP.SpPos
public import CFSG.RankThree.PartOne.CTP.SpEven
public import CFSG.RankThree.PartOne.CTP.SpNode

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG.Assembly.LowTwoRank CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.LieType.Universal.Symplectic.SpExtras (mat mat_injective)
open scoped MatrixGroups

variable {K : Type} [Field K]

section Aux

theorem finrank_span_pair_of_not_mem {V : Type*} [AddCommGroup V] [Module K V] {u e : V}
    (hu : u ≠ 0) (he : e ∉ Submodule.span K {u}) :
    Module.finrank K (Submodule.span K {u, e}) = 2 := by
  have hli : LinearIndependent K ![u, e] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    by_cases ht : t = 0
    · subst ht
      rw [zero_smul, add_zero] at hst
      exact ⟨(smul_eq_zero.mp hst).resolve_right hu, rfl⟩
    · exfalso
      apply he
      have h1 : t • e = -(s • u) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hst
      have : e = (-(t⁻¹ * s)) • u := by
        calc e = t⁻¹ • (t • e) := by rw [smul_smul, inv_mul_cancel₀ ht, one_smul]
          _ = t⁻¹ • (-(s • u)) := by rw [h1]
          _ = (-(t⁻¹ * s)) • u := by rw [smul_neg, smul_smul, neg_smul]
      rw [this]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u)
  rw [← Matrix.range_cons_cons_empty u e ![], finrank_span_eq_card hli, Fintype.card_fin]

theorem planeGroup_eq_longBlock_conj {c : StatedSp 2 K} {u w : Fin 2 ⊕ Fin 2 → K}
    (hu : mat 2 K c *ᵥ (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K) = u)
    (hw : mat 2 K c *ᵥ (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → K) = w) :
    planeGroup (Submodule.span K {u, w}) =
      (longBlock K 2 1).range.map (MulAut.conj c).toMonoidHom := by
  rw [← hu, ← hw, planeGroup_span_conj, range_longBlock]
  congr 1
  exact (planeGroup_stdPlane (K := K) (n := 2) 1).trans (longRootSp2_eq_suppGroup 1)

theorem mem_planeGroup_iff {W : Submodule K (Fin 2 ⊕ Fin 2 → K)} {a : StatedSp 2 K} :
    a ∈ planeGroup W ↔ ∀ v ∈ orth W, mat 2 K a *ᵥ v = v :=
  ⟨fun h v hv => h v (mem_orth.mp hv), fun h v hv => h v (mem_orth.mpr hv)⟩

theorem isCompl_orth_of_hyperbolic {W : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hW : IsHyperbolicPlane W) : IsCompl W (orth W) := by
  obtain ⟨hdim, hnd⟩ := isHyperbolicPlane_iff.mp hW
  have hdisj : Disjoint W (orth W) := by
    rw [Submodule.disjoint_def]
    intro v hv hv'
    exact hnd v hv fun u hu => mem_orth.mp hv' u hu
  refine ⟨hdisj, codisjoint_iff.mpr ?_⟩
  have h1 := finrank_orth_add W
  have h2 := Submodule.finrank_sup_add_finrank_inf_eq W (orth W)
  rw [hdisj.eq_bot, finrank_bot] at h2
  refine Submodule.eq_top_of_finrank_eq ?_
  have h4 : Module.finrank K (Fin 2 ⊕ Fin 2 → K) = 4 := by simp
  omega

theorem commute_planeGroup_of_orth {W W' : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hW : IsHyperbolicPlane W) (hle : W' ≤ orth W) {a b : StatedSp 2 K}
    (ha : a ∈ planeGroup W) (hb : b ∈ planeGroup W') : a * b = b * a := by
  have hle' : W ≤ orth W' := fun x hx =>
    mem_orth.mpr fun w hw => form_eq_zero_comm (mem_orth.mp (hle hw) x hx)
  refine mat_injective (Matrix.ext_iff_mulVec.mpr fun v => ?_)
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hv : v ∈ W ⊔ orth W := by
    rw [(isCompl_orth_of_hyperbolic hW).sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨x, hx, y, hy, rfl⟩ := Submodule.mem_sup.mp hv
  have hax : mat 2 K a *ᵥ x ∈ orth W' := by
    refine mem_orth.mpr fun w' hw' => ?_
    have haw' : mat 2 K a *ᵥ w' = w' := mem_planeGroup_iff.mp ha w' (hle hw')
    rw [← haw', form_mulVec]
    exact form_eq_zero_comm (mem_orth.mp (hle hw') x hx)
  have hby : mat 2 K b *ᵥ y ∈ orth W := by
    refine mem_orth.mpr fun w hw => ?_
    have hbw : mat 2 K b *ᵥ w = w := mem_planeGroup_iff.mp hb w (hle' hw)
    rw [← hbw, form_mulVec]
    exact mem_orth.mp hy w hw
  have hbx : mat 2 K b *ᵥ x = x := mem_planeGroup_iff.mp hb x (hle' hx)
  have hay : mat 2 K a *ᵥ y = y := mem_planeGroup_iff.mp ha y hy
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, hbx, hay,
    mem_planeGroup_iff.mp ha _ hby, mem_planeGroup_iff.mp hb _ hax]

end Aux

section Pos

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem false_of_commute_sup_eq_top (hK : 4 ≤ Nat.card K) {A B : Subgroup (StatedSp 2 K)}
    (hA : A ≠ ⊥) (hB : B ≠ ⊥) (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hsup : A ⊔ B = ⊤) :
    False := by
  have hq : IsQuasisimple (StatedSp 2 K) :=
    CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num) (Or.inl (Or.inr hK))
  have hZ : Subgroup.center (StatedSp 2 K) = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    rw [Subgroup.mem_bot]
    exact center_sp_eq_one_of_charTwo hg
  have hnorm : A.Normal := by
    have hle : A ⊔ B ≤ Subgroup.normalizer (A : Set (StatedSp 2 K)) := by
      refine sup_le Subgroup.le_normalizer fun b hb => ?_
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have : b * x * b⁻¹ = x := by
          rw [← hcomm x hx b hb]
          group
        rw [this]
        exact hx
      · intro hy
        have hy' := hcomm _ hy b⁻¹ (B.inv_mem hb)
        have h1 : b⁻¹ * (b * x * b⁻¹) * b = b * x * b⁻¹ := by
          rw [← hy']
          group
        have h2 : x = b * x * b⁻¹ := by
          calc x = b⁻¹ * (b * x * b⁻¹) * b := by group
            _ = b * x * b⁻¹ := h1
        rw [h2]
        exact hy
    rw [hsup, top_le_iff] at hle
    exact Subgroup.normalizer_eq_top_iff.mp hle
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hq A with h | h
  · apply hA
    rw [eq_bot_iff]
    intro x hx
    have := h hx
    rwa [hZ] at this
  · apply hB
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    have hc : b ∈ Subgroup.center (StatedSp 2 K) := by
      rw [Subgroup.mem_center_iff]
      intro g
      have hg : g ∈ A := h ▸ Subgroup.mem_top g
      exact hcomm g hg b hb
    rwa [hZ] at hc

omit [Finite K] [CharP K 2] in
theorem exists_mem_inf_add_of_stable {gB : StatedSp 2 K} {l : K}
    (hzero : ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eig gB μ = ⊥) {S : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hS : S ≤ ⨆ μ, S ⊓ eig gB μ) {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ S) :
    ∃ a ∈ S ⊓ eig gB l, ∃ b ∈ S ⊓ eig gB l⁻¹, a + b = v := by
  have hle : (⨆ μ, S ⊓ eig gB μ) ≤ (S ⊓ eig gB l) ⊔ (S ⊓ eig gB l⁻¹) := by
    refine iSup_le fun μ => ?_
    by_cases h1 : μ = l
    · rw [h1]
      exact le_sup_left
    by_cases h2 : μ = l⁻¹
    · rw [h2]
      exact le_sup_right
    · rw [hzero μ h1 h2, inf_bot_eq]
      exact bot_le
  exact Submodule.mem_sup.mp (hle (hS hv))

omit [Finite K] in
theorem sp_pos_LS {gA gB : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hgB : gB ^ p = 1) (hcom : gB * gA = gA * gB)
    (hyp : IsHyperbolicPlane (eig gA 1)) {l : K} (hl : l ≠ 1)
    (hL2 : Module.finrank K (eig gB l) = 2) (hL2' : Module.finrank K (eig gB l⁻¹) = 2)
    (hcompl : IsCompl (eig gB l) (eig gB l⁻¹))
    (hzero : ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eig gB μ = ⊥) :
    ∃ c : StatedSp 2 K,
      planeGroup (eig gA 1) = (longBlock K 2 1).range.map (MulAut.conj c).toMonoidHom ∧
      Submodule.span K {mat 2 K c *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K),
        mat 2 K c *ᵥ (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K)} = eig gB l ∧
      Submodule.span K {mat 2 K c *ᵥ (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K),
        mat 2 K c *ᵥ (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → K)} = eig gB l⁻¹ := by
  classical
  have hyp' := hyp
  have hl' : l⁻¹ ≠ 1 := fun h => hl (inv_eq_one.mp h)
  have hLiso : ∀ x ∈ eig gB l, ∀ y ∈ eig gB l, form x y = 0 := fun x hx y hy =>
    form_eig_self_eq_zero hl hx hy
  have hL'iso : ∀ x ∈ eig gB l⁻¹, ∀ y ∈ eig gB l⁻¹, form x y = 0 := fun x hx y hy =>
    form_eig_self_eq_zero hl' hx hy
  have hWstab : ∀ v ∈ eig gA 1, mat 2 K gB *ᵥ v ∈ eig gA 1 := fun v hv => mulVec_mem_eig hcom hv
  have hsplit := le_iSup_inf_eig hζ hgB hWstab
  obtain ⟨u0, w0, h0, hWspan⟩ := hyp
  have hu0 : u0 ∈ eig gA 1 := by
    rw [hWspan]
    exact Submodule.subset_span (by simp)
  have hw0 : w0 ∈ eig gA 1 := by
    rw [hWspan]
    exact Submodule.subset_span (by simp)
  obtain ⟨a1, ha1, a2, ha2, hau⟩ := exists_mem_inf_add_of_stable hzero hsplit hu0
  obtain ⟨b1, hb1, b2, hb2, hbw⟩ := exists_mem_inf_add_of_stable hzero hsplit hw0
  have hform : form a1 b2 + form a2 b1 = 1 := by
    have h := h0
    rw [← hau, ← hbw, form_add_left, form_add_right, form_add_right,
      hLiso a1 ha1.2 b1 hb1.2, hL'iso a2 ha2.2 b2 hb2.2] at h
    linear_combination h
  obtain ⟨u, hu, u', hu', huu'⟩ : ∃ u ∈ eig gA 1 ⊓ eig gB l, ∃ u' ∈ eig gA 1 ⊓ eig gB l⁻¹,
      form u u' = 1 := by
    by_cases hc : form a1 b2 = 0
    · refine ⟨b1, hb1, -a2, Submodule.neg_mem _ ha2, ?_⟩
      have h1 : form a2 b1 = 1 := by
        rw [hc, zero_add] at hform
        exact hform
      rw [form_neg_right, form_antisymm, h1]
      norm_num
    · refine ⟨a1, ha1, (form a1 b2)⁻¹ • b2, Submodule.smul_mem _ _ hb2, ?_⟩
      rw [form_smul_right, inv_mul_cancel₀ hc]
  have hu0ne : u ≠ 0 := fun h => by
    rw [h, form_zero_left] at huu'
    exact zero_ne_one huu'
  have hu'0ne : u' ≠ 0 := fun h => by
    rw [h, form_zero_right] at huu'
    exact zero_ne_one huu'
  have hspan : Submodule.span K {u, u'} = eig gA 1 := by
    have hle : Submodule.span K {u, u'} ≤ eig gA 1 := Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact hu.1
      · exact hu'.1)
    exact Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_span_pair huu', (isHyperbolicPlane_iff.mp hyp').1])
  obtain ⟨e, he, heu⟩ : ∃ e ∈ eig gB l, e ∉ Submodule.span K {u} := by
    by_contra hcon
    push Not at hcon
    have hle : eig gB l ≤ Submodule.span K {u} := hcon
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu0ne] at this
    omega
  obtain ⟨f, hf, hfu'⟩ : ∃ f ∈ eig gB l⁻¹, f ∉ Submodule.span K {u'} := by
    by_contra hcon
    push Not at hcon
    have hle : eig gB l⁻¹ ≤ Submodule.span K {u'} := hcon
    have := Submodule.finrank_mono hle
    rw [finrank_span_singleton hu'0ne] at this
    omega
  set e0 : Fin 2 ⊕ Fin 2 → K := e + (-(form e u')) • u with he0def
  have he0L : e0 ∈ eig gB l := Submodule.add_mem _ he (Submodule.smul_mem _ _ hu.2)
  have he0u' : form e0 u' = 0 := by
    rw [he0def, form_add_left, form_smul_left, huu']
    ring
  have he0nu : e0 ∉ Submodule.span K {u} := by
    intro h
    apply heu
    have : e = e0 + (form e u') • u := by
      rw [he0def, add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
    rw [this]
    exact Submodule.add_mem _ h (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u))
  set f0 : Fin 2 ⊕ Fin 2 → K := f + (-(form u f)) • u' with hf0def
  have hf0L' : f0 ∈ eig gB l⁻¹ := Submodule.add_mem _ hf (Submodule.smul_mem _ _ hu'.2)
  have huf0 : form u f0 = 0 := by
    rw [hf0def, form_add_right, form_smul_right, huu']
    ring
  have hf0nu' : f0 ∉ Submodule.span K {u'} := by
    intro h
    apply hfu'
    have : f = f0 + (form u f) • u' := by
      rw [hf0def, add_assoc, ← add_smul, neg_add_cancel, zero_smul, add_zero]
    rw [this]
    exact Submodule.add_mem _ h (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self u'))
  have hLspan : Submodule.span K {u, e0} = eig gB l := by
    have hle : Submodule.span K {u, e0} ≤ eig gB l := Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact hu.2
      · exact he0L)
    exact Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_span_pair_of_not_mem hu0ne he0nu, hL2])
  have hef : form e0 f0 ≠ 0 := by
    intro h
    have hf0 : f0 = 0 := by
      refine eq_zero_of_form_sup hcompl.sup_eq_top (fun x hx => ?_)
        (fun y hy => hL'iso f0 hf0L' y hy)
      rw [← hLspan] at hx
      obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hx
      rw [form_add_right, form_smul_right, form_smul_right, form_eq_zero_comm huf0,
        form_eq_zero_comm h]
      ring
    exact hf0nu' (hf0 ▸ Submodule.zero_mem _)
  set f1 : Fin 2 ⊕ Fin 2 → K := (form e0 f0)⁻¹ • f0 with hf1def
  have hf1L' : f1 ∈ eig gB l⁻¹ := Submodule.smul_mem _ _ hf0L'
  have hef1 : form e0 f1 = 1 := by rw [hf1def, form_smul_right, inv_mul_cancel₀ hef]
  have huf1 : form u f1 = 0 := by rw [hf1def, form_smul_right, huf0, mul_zero]
  have hf1nu' : f1 ∉ Submodule.span K {u'} := by
    intro h
    apply hf0nu'
    have : f0 = (form e0 f0) • f1 := by rw [hf1def, smul_smul, mul_inv_cancel₀ hef, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ h
  have hL'span : Submodule.span K {u', f1} = eig gB l⁻¹ := by
    have hle : Submodule.span K {u', f1} ≤ eig gB l⁻¹ := Submodule.span_le.mpr (by
      rintro _ (rfl | rfl)
      · exact hu'.2
      · exact hf1L')
    exact Submodule.eq_of_le_of_finrank_eq hle (by
      rw [finrank_span_pair_of_not_mem hu'0ne hf1nu', hL2'])
  obtain ⟨c, hc0, hc1, hc2, hc3⟩ := exists_sp_apply_eq_two (m := 0) e0 f1 u u' hef1 huu'
    (hLiso e0 he0L u hu.2) he0u' (form_eq_zero_comm huf1) (hL'iso f1 hf1L' u' hu'.2)
  refine ⟨c, ?_, ?_, ?_⟩
  · rw [← hspan]
    exact planeGroup_eq_longBlock_conj hc2 hc3
  · rw [hc0, hc2, Set.pair_comm]
    exact hLspan
  · rw [hc1, hc3, Set.pair_comm]
    exact hL'span

omit [Finite K] [CharP K 2] in
theorem exists_mem_inf_add_of_stable_one {g : StatedSp 2 K}
    {S : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hS : S ≤ ⨆ μ, S ⊓ eig g μ)
    {v : Fin 2 ⊕ Fin 2 → K} (hv : v ∈ S) :
    ∃ a ∈ S ⊓ eig g 1, ∃ b ∈ S ⊓ mov g, a + b = v := by
  have hle : (⨆ μ, S ⊓ eig g μ) ≤ (S ⊓ eig g 1) ⊔ (S ⊓ mov g) := by
    refine iSup_le fun μ => ?_
    by_cases h1 : μ = 1
    · rw [h1]
      exact le_sup_left
    · exact (inf_le_inf_left S (eig_le_mov h1)).trans le_sup_right
  exact Submodule.mem_sup.mp (hle (hS hv))

omit [Finite K] in
theorem sp_pos_LL {gA gB : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K} (hK : 4 ≤ Nat.card K)
    (hζ : IsPrimitiveRoot ζ p) (hgA : gA ^ p = 1) (hcom : gA * gB = gB * gA)
    (hypA : IsHyperbolicPlane (eig gA 1)) (horthA : orth (eig gA 1) = mov gA)
    (hypB : IsHyperbolicPlane (eig gB 1)) {A B : Subgroup (StatedSp 2 K)}
    (hA : A = planeGroup (eig gA 1)) (hB : B = planeGroup (eig gB 1)) (hA1 : A ≠ ⊥)
    (hB1 : B ≠ ⊥) (hmov : ∃ b ∈ B, gA * b ≠ b * gA) (hgen : A ⊔ B = ⊤)
    (hcA : ∀ a ∈ A, a * gA = gA * a) : False := by
  classical
  have hypB' := hypB
  have hstab : ∀ v ∈ eig gB 1, mat 2 K gA *ᵥ v ∈ eig gB 1 := fun v hv => mulVec_mem_eig hcom hv
  have hsplit := le_iSup_inf_eig hζ hgA hstab
  obtain ⟨u0, w0, h0, hWspan⟩ := hypB
  have hu0 : u0 ∈ eig gB 1 := by
    rw [hWspan]
    exact Submodule.subset_span (by simp)
  have hw0 : w0 ∈ eig gB 1 := by
    rw [hWspan]
    exact Submodule.subset_span (by simp)
  obtain ⟨a1, ha1, a2, ha2, hau⟩ := exists_mem_inf_add_of_stable_one hsplit hu0
  obtain ⟨b1, hb1, b2, hb2, hbw⟩ := exists_mem_inf_add_of_stable_one hsplit hw0
  have hcross1 : form a1 b2 = 0 := by
    have : b2 ∈ orth (eig gA 1) := horthA ▸ hb2.2
    exact form_eq_zero_comm (mem_orth.mp this a1 ha1.2)
  have hcross2 : form a2 b1 = 0 := by
    have : a2 ∈ orth (eig gA 1) := horthA ▸ ha2.2
    exact mem_orth.mp this b1 hb1.2
  have hform : form a1 b1 + form a2 b2 = 1 := by
    have h := h0
    rw [← hau, ← hbw, form_add_left, form_add_right, form_add_right, hcross1, hcross2] at h
    linear_combination h
  have hdimA : Module.finrank K (eig gA 1) = 2 := (isHyperbolicPlane_iff.mp hypA).1
  have hdimB : Module.finrank K (eig gB 1) = 2 := (isHyperbolicPlane_iff.mp hypB').1
  by_cases hc : form a1 b1 = 0
  ·
    have hc' : form a2 b2 ≠ 0 := by
      intro h
      rw [hc, h, zero_add] at hform
      exact zero_ne_one hform
    set w : Fin 2 ⊕ Fin 2 → K := (form a2 b2)⁻¹ • b2 with hwdef
    have hw : form a2 w = 1 := by rw [hwdef, form_smul_right, inv_mul_cancel₀ hc']
    have hspan : Submodule.span K {a2, w} = eig gB 1 := by
      have hle : Submodule.span K {a2, w} ≤ eig gB 1 := Submodule.span_le.mpr (by
        rintro _ (rfl | rfl)
        · exact ha2.1
        · exact Submodule.smul_mem _ _ hb2.1)
      exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_pair hw, hdimB])
    have hle : eig gB 1 ≤ orth (eig gA 1) := by
      rw [← hspan, Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact horthA ▸ ha2.2
      · exact Submodule.smul_mem _ _ (horthA ▸ hb2.2)
    refine false_of_commute_sup_eq_top hK hA1 hB1 (fun a ha b hb => ?_) hgen
    exact commute_planeGroup_of_orth hypA hle (hA ▸ ha) (hB ▸ hb)
  ·
    set w : Fin 2 ⊕ Fin 2 → K := (form a1 b1)⁻¹ • b1 with hwdef
    have hw : form a1 w = 1 := by rw [hwdef, form_smul_right, inv_mul_cancel₀ hc]
    have hspan : Submodule.span K {a1, w} = eig gA 1 := by
      have hle : Submodule.span K {a1, w} ≤ eig gA 1 := Submodule.span_le.mpr (by
        rintro _ (rfl | rfl)
        · exact ha1.2
        · exact Submodule.smul_mem _ _ hb1.2)
      exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_pair hw, hdimA])
    have hle : eig gA 1 ≤ eig gB 1 := by
      rw [← hspan, Submodule.span_le]
      rintro _ (rfl | rfl)
      · exact ha1.1
      · exact Submodule.smul_mem _ _ hb1.1
    have heq : eig gA 1 = eig gB 1 := Submodule.eq_of_le_of_finrank_eq hle (by rw [hdimA, hdimB])
    obtain ⟨b, hb, hbne⟩ := hmov
    apply hbne
    have hbA : b ∈ A := by
      rw [hA, heq, ← hB]
      exact hb
    exact (hcA b hbA).symm

omit [Finite K] [CharP K 2] in
theorem scalar_dual {g : StatedSp 2 K} {L L' : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hc : IsCompl L L') (hL'iso : ∀ x ∈ L', ∀ y ∈ L', form x y = 0)
    (hgL' : ∀ v ∈ L', mat 2 K g *ᵥ v ∈ L') {t : K} (ht : t ≠ 0)
    (hgL : ∀ v ∈ L, mat 2 K g *ᵥ v = t • v) :
    ∀ w ∈ L', mat 2 K g *ᵥ w = t⁻¹ • w := by
  intro w hw
  have hz : mat 2 K g *ᵥ w - t⁻¹ • w ∈ L' := L'.sub_mem (hgL' w hw) (L'.smul_mem _ hw)
  have h0 : mat 2 K g *ᵥ w - t⁻¹ • w = 0 := by
    refine eq_zero_of_form_sup hc.sup_eq_top (fun v hv => ?_) (fun y hy => hL'iso _ hz y hy)
    have h := form_mulVec g v w
    rw [hgL v hv, form_smul_left] at h
    have h2 : form v (mat 2 K g *ᵥ w) = t⁻¹ * form v w := by
      field_simp
      linear_combination h
    rw [form_antisymm, sub_eq_add_neg, form_add_right, form_neg_right, form_smul_right, h2]
    ring
  exact sub_eq_zero.mp h0

omit [Finite K] [CharP K 2] in
theorem commute_of_scalar_of_isCompl {g h : StatedSp 2 K}
    {L L' : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hc : IsCompl L L')
    (hL'iso : ∀ x ∈ L', ∀ y ∈ L', form x y = 0) (hgL' : ∀ v ∈ L', mat 2 K g *ᵥ v ∈ L')
    {t : K} (ht : t ≠ 0) (hgL : ∀ v ∈ L, mat 2 K g *ᵥ v = t • v)
    (hhL : ∀ v ∈ L, mat 2 K h *ᵥ v ∈ L) (hhL' : ∀ v ∈ L', mat 2 K h *ᵥ v ∈ L') :
    g * h = h * g := by
  have hgL'' := scalar_dual hc hL'iso hgL' ht hgL
  refine mat_injective (Matrix.ext_iff_mulVec.mpr fun v => ?_)
  rw [map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have hv : v ∈ L ⊔ L' := by
    rw [hc.sup_eq_top]
    exact Submodule.mem_top
  obtain ⟨p, hp, q, hq, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, hgL p hp,
    hgL'' q hq, hgL _ (hhL p hp), hgL'' _ (hhL' q hq), Matrix.mulVec_smul, Matrix.mulVec_smul]

omit [Finite K] [CharP K 2] in
theorem not_mem_span_of_disjoint {M N : Submodule K (Fin 2 ⊕ Fin 2 → K)} (hd : Disjoint M N)
    {u e : Fin 2 ⊕ Fin 2 → K} (hu : u ∈ M) (he : e ∈ N) (he0 : e ≠ 0) :
    e ∉ Submodule.span K {u} := by
  intro h
  have hM : e ∈ M := (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hu)) h
  exact he0 (Submodule.disjoint_def.mp hd e hM he)

omit [Finite K] [CharP K 2] in
theorem span_pair_eq_of_not_mem {M : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hM : Module.finrank K M = 2) {u e : Fin 2 ⊕ Fin 2 → K} (hu : u ∈ M) (he : e ∈ M)
    (hu0 : u ≠ 0) (hne : e ∉ Submodule.span K {u}) : Submodule.span K {u, e} = M := by
  have hle : Submodule.span K {u, e} ≤ M := Submodule.span_le.mpr (by
    rintro _ (rfl | rfl)
    · exact hu
    · exact he)
  exact Submodule.eq_of_le_of_finrank_eq hle (by rw [finrank_span_pair_of_not_mem hu0 hne, hM])

omit [Finite K] [CharP K 2] in
theorem exists_ne_zero_of_not_scalar {gA : StatedSp 2 K} {l : K}
    (hzero : ∀ μ, μ ≠ l → μ ≠ l⁻¹ → eig gA μ = ⊥) {M : Submodule K (Fin 2 ⊕ Fin 2 → K)}
    (hM : M ≤ ⨆ μ, M ⊓ eig gA μ) (hn1 : ¬ ∀ v ∈ M, mat 2 K gA *ᵥ v = l • v)
    (hn2 : ¬ ∀ v ∈ M, mat 2 K gA *ᵥ v = l⁻¹ • v) :
    (∃ x ∈ M ⊓ eig gA l, x ≠ 0) ∧ ∃ y ∈ M ⊓ eig gA l⁻¹, y ≠ 0 := by
  constructor
  · by_contra h
    push Not at h
    apply hn2
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mem_inf_add_of_stable hzero hM hv
    rw [h a ha, zero_add]
    exact mem_eig.mp hb.2
  · by_contra h
    push Not at h
    apply hn1
    intro v hv
    obtain ⟨a, ha, b, hb, rfl⟩ := exists_mem_inf_add_of_stable hzero hM hv
    rw [h b hb, add_zero]
    exact mem_eig.mp ha.2

omit [Finite K] in
theorem sp_pos_SS_vectors {gA gB : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hgA : gA ^ p = 1) (hcom : gA * gB = gB * gA)
    {lA : K} (hlA : lA ≠ 1) (hlA0 : lA ≠ 0) (hLA2 : Module.finrank K (eig gA lA) = 2)
    (hLA2' : Module.finrank K (eig gA lA⁻¹) = 2)
    (hcomplA : IsCompl (eig gA lA) (eig gA lA⁻¹))
    (hzeroA : ∀ μ, μ ≠ lA → μ ≠ lA⁻¹ → eig gA μ = ⊥)
    {lB : K} (hlB : lB ≠ 1) (hLB2 : Module.finrank K (eig gB lB) = 2)
    (hLB2' : Module.finrank K (eig gB lB⁻¹) = 2)
    (hcomplB : IsCompl (eig gB lB) (eig gB lB⁻¹)) {B : Subgroup (StatedSp 2 K)}
    (hcB : ∀ b ∈ B, b * gB = gB * b) (hmov : ∃ b ∈ B, gA * b ≠ b * gA) :
    ∃ e0 f0 e1 f1 : Fin 2 ⊕ Fin 2 → K, form e0 f0 = 1 ∧ form e1 f1 = 1 ∧ form e0 e1 = 0 ∧
      form e0 f1 = 0 ∧ form f0 e1 = 0 ∧ form f0 f1 = 0 ∧
      Submodule.span K {e0, e1} = eig gB lB ∧ Submodule.span K {f0, f1} = eig gB lB⁻¹ ∧
      Submodule.span K {e0, f1} = eig gA lA ∧ Submodule.span K {f0, e1} = eig gA lA⁻¹ := by
  classical
  have hlA' : lA⁻¹ ≠ 1 := fun h => hlA (inv_eq_one.mp h)
  have hlB' : lB⁻¹ ≠ 1 := fun h => hlB (inv_eq_one.mp h)
  have hAiso : ∀ x ∈ eig gA lA, ∀ y ∈ eig gA lA, form x y = 0 := fun x hx y hy =>
    form_eig_self_eq_zero hlA hx hy
  have hA'iso : ∀ x ∈ eig gA lA⁻¹, ∀ y ∈ eig gA lA⁻¹, form x y = 0 := fun x hx y hy =>
    form_eig_self_eq_zero hlA' hx hy
  have hBiso : ∀ x ∈ eig gB lB, ∀ y ∈ eig gB lB, form x y = 0 := fun x hx y hy =>
    form_eig_self_eq_zero hlB hx hy
  have hB'iso : ∀ x ∈ eig gB lB⁻¹, ∀ y ∈ eig gB lB⁻¹, form x y = 0 := fun x hx y hy =>
    form_eig_self_eq_zero hlB' hx hy
  have hstabB : ∀ v ∈ eig gB lB, mat 2 K gA *ᵥ v ∈ eig gB lB := fun v hv =>
    mulVec_mem_eig hcom hv
  have hstabB' : ∀ v ∈ eig gB lB⁻¹, mat 2 K gA *ᵥ v ∈ eig gB lB⁻¹ := fun v hv =>
    mulVec_mem_eig hcom hv
  have hsplitB := le_iSup_inf_eig hζ hgA hstabB
  have hsplitB' := le_iSup_inf_eig hζ hgA hstabB'
  have hnsB : ∀ t : K, t ≠ 0 → ¬ ∀ v ∈ eig gB lB, mat 2 K gA *ᵥ v = t • v := by
    intro t ht h
    obtain ⟨b, hb, hbne⟩ := hmov
    exact hbne (commute_of_scalar_of_isCompl hcomplB hB'iso hstabB' ht h
      (fun v hv => mulVec_mem_eig (hcB b hb) hv) (fun v hv => mulVec_mem_eig (hcB b hb) hv))
  have hnsB' : ∀ t : K, t ≠ 0 → ¬ ∀ v ∈ eig gB lB⁻¹, mat 2 K gA *ᵥ v = t • v := by
    intro t ht h
    exact hnsB t⁻¹ (inv_ne_zero ht) (scalar_dual hcomplB.symm hBiso hstabB ht h)
  obtain ⟨⟨x, hx, hx0⟩, ⟨y, hy, hy0⟩⟩ :=
    exists_ne_zero_of_not_scalar hzeroA hsplitB (hnsB lA hlA0) (hnsB lA⁻¹ (inv_ne_zero hlA0))
  obtain ⟨⟨x', hx', hx'0⟩, ⟨y', hy', hy'0⟩⟩ :=
    exists_ne_zero_of_not_scalar hzeroA hsplitB' (hnsB' lA hlA0)
      (hnsB' lA⁻¹ (inv_ne_zero hlA0))
  have hdA := hcomplA.disjoint
  have hdB := hcomplB.disjoint
  have hspB : Submodule.span K {x, y} = eig gB lB :=
    span_pair_eq_of_not_mem hLB2 hx.1 hy.1 hx0 (not_mem_span_of_disjoint hdA hx.2 hy.2 hy0)
  have hspB' : Submodule.span K {x', y'} = eig gB lB⁻¹ :=
    span_pair_eq_of_not_mem hLB2' hx'.1 hy'.1 hx'0 (not_mem_span_of_disjoint hdA hx'.2 hy'.2 hy'0)
  have hxy' : form x y' ≠ 0 := by
    intro h
    refine hx0 (eq_zero_of_form_sup hcomplB.sup_eq_top (fun v hv => hBiso x hx.1 v hv)
      (fun w hw => ?_))
    rw [← hspB'] at hw
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [form_add_right, form_smul_right, form_smul_right, h, hAiso x hx.2 x' hx'.2]
    ring
  have hyx' : form y x' ≠ 0 := by
    intro h
    refine hy0 (eq_zero_of_form_sup hcomplB.sup_eq_top (fun v hv => hBiso y hy.1 v hv)
      (fun w hw => ?_))
    rw [← hspB'] at hw
    obtain ⟨s, t, rfl⟩ := Submodule.mem_span_pair.mp hw
    rw [form_add_right, form_smul_right, form_smul_right, h, hA'iso y hy.2 y' hy'.2]
    ring
  set f0 : Fin 2 ⊕ Fin 2 → K := (form x y')⁻¹ • y' with hf0def
  set f1 : Fin 2 ⊕ Fin 2 → K := (form y x')⁻¹ • x' with hf1def
  have hf0 : f0 ≠ 0 := fun h => hy'0 (by
    have := congrArg (fun v => (form x y') • v) h
    simpa [hf0def, smul_smul, mul_inv_cancel₀ hxy'] using this)
  have hf1 : f1 ≠ 0 := fun h => hx'0 (by
    have := congrArg (fun v => (form y x') • v) h
    simpa [hf1def, smul_smul, mul_inv_cancel₀ hyx'] using this)
  have hf0B' : f0 ∈ eig gB lB⁻¹ := Submodule.smul_mem _ _ hy'.1
  have hf1B' : f1 ∈ eig gB lB⁻¹ := Submodule.smul_mem _ _ hx'.1
  have hf0A' : f0 ∈ eig gA lA⁻¹ := Submodule.smul_mem _ _ hy'.2
  have hf1A : f1 ∈ eig gA lA := Submodule.smul_mem _ _ hx'.2
  refine ⟨x, f0, y, f1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hf0def, form_smul_right, inv_mul_cancel₀ hxy']
  · rw [hf1def, form_smul_right, inv_mul_cancel₀ hyx']
  · exact hBiso x hx.1 y hy.1
  · rw [hf1def, form_smul_right, hAiso x hx.2 x' hx'.2, mul_zero]
  · rw [hf0def, form_smul_left, hA'iso y' hy'.2 y hy.2, mul_zero]
  · rw [hf0def, hf1def, form_smul_left, form_smul_right, hB'iso y' hy'.1 x' hx'.1]
    ring
  · exact hspB
  · exact span_pair_eq_of_not_mem hLB2' hf0B' hf1B' hf0
      (not_mem_span_of_disjoint hdA.symm hf0A' hf1A hf1)
  · exact span_pair_eq_of_not_mem hLA2 hx.2 hf1A hx0
      (not_mem_span_of_disjoint hdB hx.1 hf1B' hf1)
  · exact span_pair_eq_of_not_mem hLA2' hf0A' hy.2 hf0
      (not_mem_span_of_disjoint hdB.symm hf0B' hy.1 hy0)

end Pos

section Quad

@[expose] def Qstd (x : Fin 2 ⊕ Fin 2 → K) : K :=
  x (Sum.inl 0) * x (Sum.inr 0) + x (Sum.inl 1) * x (Sum.inr 1)

theorem Qstd_shortBlock (M : SL(2, K)) (x : Fin 2 ⊕ Fin 2 → K) :
    Qstd (mat 2 K (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) M) *ᵥ x) = Qstd x := by
  have hdet : M 0 0 * M 1 1 - M 0 1 * M 1 0 = 1 := by
    have := M.2
    rwa [Matrix.det_fin_two] at this
  rw [mat_shortBlock, blockMat_zero_one, blockMat_zero_one,
    Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
  simp only [Qstd, Matrix.mulVec, dotProduct]
  simp
  linear_combination (x (Sum.inl 0) * x (Sum.inr 0) + x (Sum.inl 1) * x (Sum.inr 1)) * hdet

theorem Qstd_swap {w : StatedSp 2 K}
    (hw0 : mat 2 K w *ᵥ (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) = Pi.single (Sum.inl 0) 1)
    (hw1 : mat 2 K w *ᵥ (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K) = Pi.single (Sum.inr 1) 1)
    (hw2 : mat 2 K w *ᵥ (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K) = Pi.single (Sum.inr 0) 1)
    (hw3 : mat 2 K w *ᵥ (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → K) = Pi.single (Sum.inl 1) 1)
    (x : Fin 2 ⊕ Fin 2 → K) : Qstd (mat 2 K w *ᵥ x) = Qstd x := by
  have hx : x = x (Sum.inl 0) • (Pi.single (Sum.inl 0) 1 : Fin 2 ⊕ Fin 2 → K) +
      x (Sum.inl 1) • (Pi.single (Sum.inl 1) 1 : Fin 2 ⊕ Fin 2 → K) +
      x (Sum.inr 0) • (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K) +
      x (Sum.inr 1) • (Pi.single (Sum.inr 1) 1 : Fin 2 ⊕ Fin 2 → K) := by
    funext b
    rcases b with i | i <;> fin_cases i <;> simp
  conv_lhs => rw [hx]
  rw [Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_add, Matrix.mulVec_smul,
    Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.mulVec_smul, hw0, hw1, hw2, hw3]
  simp only [Qstd, Pi.add_apply, Pi.smul_apply, Pi.single_apply]
  simp
  ring

theorem Qstd_longBlock :
    Qstd (mat 2 K (longBlock K 2 0 (CFSG.LieType.Steinberg.sl2Upper (1 : K))) *ᵥ
      (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K)) = 1 := by
  rw [longBlock_sl2Upper, CFSG.LieType.Universal.Symplectic.SpExtras.mat_elt_positiveLong]
  simp only [Qstd, Matrix.transvection]
  simp

@[expose] def Qstab (c : StatedSp 2 K) : Subgroup (StatedSp 2 K) where
  carrier := {g | ∀ v, Qstd (mat 2 K c⁻¹ *ᵥ (mat 2 K g *ᵥ v)) = Qstd (mat 2 K c⁻¹ *ᵥ v)}
  one_mem' := fun v => by simp
  mul_mem' := fun {g h} hg hh v => by
    rw [map_mul, ← Matrix.mulVec_mulVec, hg (mat 2 K h *ᵥ v), hh v]
  inv_mem' := fun {g} hg v => by
    have := hg (mat 2 K g⁻¹ *ᵥ v)
    rw [mulVec_mulVec_inv] at this
    exact this.symm

end Quad

section SS

variable [Finite K] [CharP K 2]

theorem sp_pos_SS {gA gB : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K}
    (hζ : IsPrimitiveRoot ζ p) (hgA : gA ^ p = 1) (hcom : gA * gB = gB * gA)
    {lA : K} (hlA : lA ≠ 1) (hlA0 : lA ≠ 0) (hLA2 : Module.finrank K (eig gA lA) = 2)
    (hLA2' : Module.finrank K (eig gA lA⁻¹) = 2)
    (hcomplA : IsCompl (eig gA lA) (eig gA lA⁻¹))
    (hzeroA : ∀ μ, μ ≠ lA → μ ≠ lA⁻¹ → eig gA μ = ⊥)
    {lB : K} (hlB : lB ≠ 1) (hLB2 : Module.finrank K (eig gB lB) = 2)
    (hLB2' : Module.finrank K (eig gB lB⁻¹) = 2)
    (hcomplB : IsCompl (eig gB lB) (eig gB lB⁻¹)) {A B : Subgroup (StatedSp 2 K)}
    [Group.IsPerfect A] [Group.IsPerfect B] (hcardA : Nat.card A = Nat.card SL(2, K))
    (hcardB : Nat.card B = Nat.card SL(2, K)) (hcA : ∀ a ∈ A, a * gA = gA * a)
    (hcB : ∀ b ∈ B, b * gB = gB * b) (hmov : ∃ b ∈ B, gA * b ≠ b * gA) (hgen : A ⊔ B = ⊤) :
    False := by
  obtain ⟨e0, f0, e1, f1, h1, h2, o1, o2, o3, o4, hspB, hspB', hspA, hspA'⟩ :=
    sp_pos_SS_vectors hζ hgA hcom hlA hlA0 hLA2 hLA2' hcomplA hzeroA hlB hLB2 hLB2' hcomplB hcB
      hmov
  obtain ⟨c, hc0, hc1, hc2, hc3⟩ := exists_sp_apply_eq_two (m := 0) e0 f0 e1 f1 h1 h2 o1 o2 o3 o4
  have h2' : form f1 e1 = 1 := by
    rw [form_antisymm, h2]
    exact CharTwo.neg_eq 1
  obtain ⟨c', hc'0, hc'1, hc'2, hc'3⟩ :=
    exists_sp_apply_eq_two (m := 0) e0 f0 f1 e1 h1 h2' o2 o1 o4 o3
  have hBeq := eq_shortBlock_conj_of_stab (c := c) B hcardB
    (fun h hh v hv => by
      rw [hc0, hc2, hspB] at hv ⊢
      exact mulVec_mem_eig (hcB h hh) hv)
    (fun h hh v hv => by
      rw [hc1, hc3, hspB'] at hv ⊢
      exact mulVec_mem_eig (hcB h hh) hv)
  have hAeq := eq_shortBlock_conj_of_stab (c := c') A hcardA
    (fun h hh v hv => by
      rw [hc'0, hc'2, hspA] at hv ⊢
      exact mulVec_mem_eig (hcA h hh) hv)
    (fun h hh v hv => by
      rw [hc'1, hc'3, hspA'] at hv ⊢
      exact mulVec_mem_eig (hcA h hh) hv)
  have hw : ∀ (x y : Fin 2 ⊕ Fin 2 → K) (a b : Fin 2 ⊕ Fin 2),
      mat 2 K c *ᵥ (Pi.single b 1 : Fin 2 ⊕ Fin 2 → K) = y →
      mat 2 K c' *ᵥ (Pi.single a 1 : Fin 2 ⊕ Fin 2 → K) = y →
      mat 2 K (c⁻¹ * c') *ᵥ (Pi.single a 1 : Fin 2 ⊕ Fin 2 → K) = Pi.single b 1 := by
    intro x y a b hb ha
    rw [map_mul, ← Matrix.mulVec_mulVec, ha]
    exact ((mulVec_eq_iff c _ _).1 hb).symm
  have hw0 := hw e0 e0 (Sum.inl 0) (Sum.inl 0) hc0 hc'0
  have hw1 := hw f1 f1 (Sum.inl 1) (Sum.inr 1) hc3 hc'2
  have hw2 := hw f0 f0 (Sum.inr 0) (Sum.inr 0) hc1 hc'1
  have hw3 := hw e1 e1 (Sum.inr 1) (Sum.inl 1) hc2 hc'3
  have hswap := Qstd_swap hw0 hw1 hw2 hw3
  have hswap' : ∀ x, Qstd (mat 2 K (c⁻¹ * c')⁻¹ *ᵥ x) = Qstd x := fun x => by
    have := hswap (mat 2 K (c⁻¹ * c')⁻¹ *ᵥ x)
    rw [mulVec_mulVec_inv] at this
    exact this.symm
  have hkey : ∀ (X : StatedSp 2 K) (v : Fin 2 ⊕ Fin 2 → K),
      mat 2 K c⁻¹ *ᵥ (mat 2 K (c * X * c⁻¹) *ᵥ v) = mat 2 K X *ᵥ (mat 2 K c⁻¹ *ᵥ v) := by
    intro X v
    rw [Matrix.mulVec_mulVec, ← map_mul, show c⁻¹ * (c * X * c⁻¹) = X * c⁻¹ by group, map_mul,
      ← Matrix.mulVec_mulVec]
  have hAle : A ≤ Qstab c := by
    rw [hAeq]
    rintro _ ⟨s, ⟨M, rfl⟩, rfl⟩ v
    have e : (MulAut.conj c').toMonoidHom (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) M) =
        c * ((c⁻¹ * c') * shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) M * (c⁻¹ * c')⁻¹) *
          c⁻¹ := by
      simp [MulAut.conj_apply]
      group
    rw [e, hkey, map_mul, map_mul, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hswap,
      Qstd_shortBlock, hswap']
  have hBle : B ≤ Qstab c := by
    rw [hBeq]
    rintro _ ⟨s, ⟨M, rfl⟩, rfl⟩ v
    have e : (MulAut.conj c).toMonoidHom (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) M) =
        c * shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1) M * c⁻¹ := by
      simp [MulAut.conj_apply]
    rw [e, hkey, Qstd_shortBlock]
  have htop : (⊤ : Subgroup (StatedSp 2 K)) ≤ Qstab c := by
    rw [← hgen]
    exact sup_le hAle hBle
  have hmem := htop (Subgroup.mem_top
    (c * longBlock K 2 0 (CFSG.LieType.Steinberg.sl2Upper (1 : K)) * c⁻¹))
  have h0 := hmem (mat 2 K c *ᵥ (Pi.single (Sum.inr 0) 1 : Fin 2 ⊕ Fin 2 → K))
  rw [hkey, mulVec_inv_mulVec, Qstd_longBlock] at h0
  simp [Qstd] at h0

end SS

section Pair

variable [Finite K] [CharP K 2]

theorem sp_pair {gA gB : StatedSp 2 K} {p : ℕ} [NeZero p] {ζ : K} (hK : 4 ≤ Nat.card K)
    (hζ : IsPrimitiveRoot ζ p) (hgA : gA ^ p = 1) (hgB : gB ^ p = 1) (hgA1 : gA ≠ 1)
    (hgB1 : gB ≠ 1) (hcom : gA * gB = gB * gA) {A B : Subgroup (StatedSp 2 K)}
    [Group.IsPerfect A] [Group.IsPerfect B] (hA1 : A ≠ ⊥) (hB1 : B ≠ ⊥)
    (hcardA : Nat.card A = Nat.card SL(2, K)) (hcardB : Nat.card B = Nat.card SL(2, K))
    (hcA : ∀ a ∈ A, a * gA = gA * a) (hcB : ∀ b ∈ B, b * gB = gB * b)
    (hmovB : ∃ b ∈ B, gA * b ≠ b * gA) (hgen : A ⊔ B = ⊤) :
    ∃ c : StatedSp 2 K,
      (A = (longBlock K 2 1).range.map (MulAut.conj c).toMonoidHom ∧
        B = (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
          (MulAut.conj c).toMonoidHom) ∨
      (B = (longBlock K 2 1).range.map (MulAut.conj c).toMonoidHom ∧
        A = (shortBlock K (zero_ne_one : (0 : Fin 2) ≠ 1)).range.map
          (MulAut.conj c).toMonoidHom) := by
  rcases sp_node hζ hgA hgA1 A hA1 hcardA hcA with ⟨hypA, horthA, hA⟩ |
    ⟨lA, hlA, hlA0, hLA2, hLA2', hcomplA, hzeroA⟩ <;>
  rcases sp_node hζ hgB hgB1 B hB1 hcardB hcB with ⟨hypB, horthB, hB⟩ |
    ⟨lB, hlB, hlB0, hLB2, hLB2', hcomplB, hzeroB⟩
  · exact (sp_pos_LL hK hζ hgA hcom hypA horthA hypB hA hB hA1 hB1 hmovB hgen hcA).elim
  ·
    obtain ⟨c, hcA', hsp, hsp'⟩ := sp_pos_LS hζ hgB hcom.symm hypA hlB hLB2 hLB2' hcomplB hzeroB
    refine ⟨c, Or.inl ⟨hA.trans hcA', ?_⟩⟩
    exact eq_shortBlock_conj_of_stab (c := c) B hcardB
      (fun h hh v hv => by
        rw [hsp] at hv ⊢
        exact mulVec_mem_eig (hcB h hh) hv)
      (fun h hh v hv => by
        rw [hsp'] at hv ⊢
        exact mulVec_mem_eig (hcB h hh) hv)
  ·
    obtain ⟨c, hcB', hsp, hsp'⟩ := sp_pos_LS hζ hgA hcom hypB hlA hLA2 hLA2' hcomplA hzeroA
    refine ⟨c, Or.inr ⟨hB.trans hcB', ?_⟩⟩
    exact eq_shortBlock_conj_of_stab (c := c) A hcardA
      (fun h hh v hv => by
        rw [hsp] at hv ⊢
        exact mulVec_mem_eig (hcA h hh) hv)
      (fun h hh v hv => by
        rw [hsp'] at hv ⊢
        exact mulVec_mem_eig (hcA h hh) hv)
  · exact (sp_pos_SS hζ hgA hcom hlA hlA0 hLA2 hLA2' hcomplA hzeroA hlB hLB2 hLB2' hcomplB
      hcardA hcardB hcA hcB hmovB hgen).elim

end Pair

end CFSG.RankThree.PartOne.CTP
