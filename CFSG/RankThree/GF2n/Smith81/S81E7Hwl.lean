module

public import CFSG.RankThree.GF2n.Smith81.S81E7Bruhat

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits


variable {K : Type} [Field K]

@[expose] def Fil (K : Type) [Field K] (i : ℤ) : Set (V K) := {v | ∀ b, pr b theta < i → v b = 0}

@[expose] def Piece (K : Type) [Field K] (i : ℤ) : Set (V K) := {v | ∀ b, pr b theta ≠ i → v b = 0}

@[expose] def PresFil (g : Module.End K (V K)) : Prop :=
  ∀ i v, v ∈ Fil K i → g v ∈ Fil K i

@[expose] def RaisesFil (g : Module.End K (V K)) : Prop :=
  ∀ i v, v ∈ Fil K i → g v - v ∈ Fil K (i + 1)

@[expose] def PresPiece (g : Module.End K (V K)) : Prop :=
  ∀ i v, v ∈ Piece K i → g v ∈ Piece K i

theorem mem_Fil_iff {i : ℤ} {v : V K} : v ∈ Fil K i ↔ ∀ b, pr b theta < i → v b = 0 := Iff.rfl

theorem mem_Piece_iff {i : ℤ} {v : V K} : v ∈ Piece K i ↔ ∀ b, pr b theta ≠ i → v b = 0 :=
  Iff.rfl

theorem Fil_anti {i j : ℤ} (h : i ≤ j) {v : V K} (hv : v ∈ Fil K j) : v ∈ Fil K i :=
  mem_Fil_iff.2 fun b hb => mem_Fil_iff.1 hv b (lt_of_lt_of_le hb h)

theorem zero_mem_Fil (i : ℤ) : (0 : V K) ∈ Fil K i :=
  mem_Fil_iff.2 fun b _ => by simp

theorem add_mem_Fil {i : ℤ} {v w : V K} (hv : v ∈ Fil K i) (hw : w ∈ Fil K i) :
    v + w ∈ Fil K i :=
  mem_Fil_iff.2 fun b hb => by simp [mem_Fil_iff.1 hv b hb, mem_Fil_iff.1 hw b hb]

theorem presFil_of_raises {g : Module.End K (V K)} (hg : RaisesFil g) : PresFil g := by
  intro i v hv
  have h2 : g v - v ∈ Fil K i := Fil_anti (show i ≤ i + 1 by omega) (hg i v hv)
  have h3 := add_mem_Fil h2 hv
  rwa [sub_add_cancel] at h3

theorem raisesFil_mul {F G : Module.End K (V K)} (hF : RaisesFil F) (hG : RaisesFil G) :
    RaisesFil (F * G) := by
  intro i v hv
  have e : (F * G) v - v = (F (G v) - G v) + (G v - v) := by
    rw [Module.End.mul_apply]
    abel
  rw [e]
  exact add_mem_Fil (hF i (G v) (presFil_of_raises hG i v hv)) (hG i v hv)

theorem presFil_mul {F G : Module.End K (V K)} (hF : PresFil F) (hG : PresFil G) :
    PresFil (F * G) := by
  intro i v hv
  rw [Module.End.mul_apply]
  exact hF i _ (hG i v hv)

theorem presPiece_mul {F G : Module.End K (V K)} (hF : PresPiece F) (hG : PresPiece G) :
    PresPiece (F * G) := by
  intro i v hv
  rw [Module.End.mul_apply]
  exact hF i _ (hG i v hv)

theorem raisesFil_one : RaisesFil (1 : Module.End K (V K)) := by
  intro i v _
  rw [Module.End.one_apply, sub_self]
  exact zero_mem_Fil (i + 1)

theorem presFil_one : PresFil (1 : Module.End K (V K)) := by
  intro i v hv
  rw [Module.End.one_apply]
  exact hv

theorem presPiece_one : PresPiece (1 : Module.End K (V K)) := by
  intro i v hv
  rw [Module.End.one_apply]
  exact hv

theorem presFil_of_presPiece {F : Module.End K (V K)} (h : PresPiece F) : PresFil F := by
  intro i v hv
  refine mem_Fil_iff.2 fun b hb => ?_
  have hvi : ∀ a ∈ v.support, i ≤ pr a theta := by
    intro a ha
    by_contra hlt
    exact (Finsupp.mem_support_iff.1 ha) (mem_Fil_iff.1 hv a (by omega))
  have hsum : v = ∑ a ∈ v.support, Finsupp.single a (v a) := (Finsupp.sum_single v).symm
  have e : F v = ∑ a ∈ v.support, F (Finsupp.single a (v a)) := by
    conv_lhs => rw [hsum]
    exact map_sum F _ _
  rw [e, Finsupp.finset_sum_apply]
  refine Finset.sum_eq_zero fun a ha => ?_
  have hmem : Finsupp.single a (v a) ∈ Piece K (pr a theta) := by
    refine mem_Piece_iff.2 fun b' hb' => ?_
    have hab : ¬ (a = b') := fun hab => hb' (by rw [hab])
    rw [Finsupp.single_apply, if_neg hab]
  have hP := h (pr a theta) _ hmem
  exact mem_Piece_iff.1 hP b (fun h' => by have := hvi a ha; omega)

@[expose] def NN (K : Type) [Field K] : Subgroup (Module.End K (V K))ˣ where
  carrier := {g | RaisesFil (g : Module.End K (V K)) ∧ RaisesFil ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    show RaisesFil ((a * b : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      RaisesFil (((a * b)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact raisesFil_mul ha1 hb1
    · rw [mul_inv_rev, Units.val_mul]
      exact raisesFil_mul hb2 ha2
  one_mem' := by
    show RaisesFil ((1 : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      RaisesFil (((1 : (Module.End K (V K))ˣ)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
    rw [inv_one, Units.val_one]
    exact ⟨raisesFil_one, raisesFil_one⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    show RaisesFil ((x⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      RaisesFil (((x⁻¹)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
    rw [inv_inv]
    exact ⟨hx2, hx1⟩

@[expose] def FF (K : Type) [Field K] : Subgroup (Module.End K (V K))ˣ where
  carrier := {g | PresFil (g : Module.End K (V K)) ∧ PresFil ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    show PresFil ((a * b : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      PresFil (((a * b)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact presFil_mul ha1 hb1
    · rw [mul_inv_rev, Units.val_mul]
      exact presFil_mul hb2 ha2
  one_mem' := by
    show PresFil ((1 : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      PresFil (((1 : (Module.End K (V K))ˣ)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
    rw [inv_one, Units.val_one]
    exact ⟨presFil_one, presFil_one⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    show PresFil ((x⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      PresFil (((x⁻¹)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
    rw [inv_inv]
    exact ⟨hx2, hx1⟩

@[expose] def GG (K : Type) [Field K] : Subgroup (Module.End K (V K))ˣ where
  carrier := {g | PresPiece (g : Module.End K (V K)) ∧ PresPiece ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))}
  mul_mem' := by
    rintro a b ⟨ha1, ha2⟩ ⟨hb1, hb2⟩
    show PresPiece ((a * b : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      PresPiece (((a * b)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact presPiece_mul ha1 hb1
    · rw [mul_inv_rev, Units.val_mul]
      exact presPiece_mul hb2 ha2
  one_mem' := by
    show PresPiece ((1 : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      PresPiece (((1 : (Module.End K (V K))ˣ)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
    rw [inv_one, Units.val_one]
    exact ⟨presPiece_one, presPiece_one⟩
  inv_mem' := by
    rintro x ⟨hx1, hx2⟩
    show PresPiece ((x⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
      PresPiece (((x⁻¹)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
    rw [inv_inv]
    exact ⟨hx2, hx1⟩

theorem GG_le_FF : GG K ≤ FF K := by
  intro g hg
  have hg' : PresPiece (g : Module.End K (V K)) ∧
      PresPiece ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := hg
  show PresFil (g : Module.End K (V K)) ∧
    PresFil ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
  exact ⟨presFil_of_presPiece hg'.1, presFil_of_presPiece hg'.2⟩

theorem NN_le_FF : NN K ≤ FF K := by
  intro g hg
  have hg' : RaisesFil (g : Module.End K (V K)) ∧
      RaisesFil ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := hg
  show PresFil (g : Module.End K (V K)) ∧
    PresFil ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
  exact ⟨presFil_of_raises hg'.1, presFil_of_raises hg'.2⟩

theorem raisesFil_conj {F G Q : Module.End K (V K)} (hF : PresFil F) (hG : PresFil G)
    (hFG : F * G = 1) (hQ : RaisesFil Q) : RaisesFil (F * Q * G) := by
  intro i v hv
  have hFv : F (G v) = v := by
    rw [← Module.End.mul_apply, hFG, Module.End.one_apply]
  have e : (F * Q * G) v - v = F (Q (G v) - G v) := by
    rw [map_sub, hFv, Module.End.mul_apply, Module.End.mul_apply]
  rw [e]
  exact hF (i + 1) _ (hQ i (G v) (hG i v hv))

theorem FF_conj_NN {f q : (Module.End K (V K))ˣ} (hf : f ∈ FF K) (hq : q ∈ NN K) :
    f * q * f⁻¹ ∈ NN K := by
  have hf' : PresFil (f : Module.End K (V K)) ∧
      PresFil ((f⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := hf
  have hq' : RaisesFil (q : Module.End K (V K)) ∧
      RaisesFil ((q⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := hq
  have hfinv : (f : Module.End K (V K)) * ((f⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) = 1 :=
    Units.mul_inv f
  have hinv : ((f * q * f⁻¹)⁻¹ : (Module.End K (V K))ˣ) = f * q⁻¹ * f⁻¹ := by
    rw [mul_inv_rev, mul_inv_rev, inv_inv, mul_assoc]
  show RaisesFil ((f * q * f⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
    RaisesFil (((f * q * f⁻¹)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
  refine ⟨?_, ?_⟩
  · rw [Units.val_mul, Units.val_mul]
    exact raisesFil_conj hf'.1 hf'.2 hfinv hq'.1
  · rw [hinv, Units.val_mul, Units.val_mul]
    exact raisesFil_conj hf'.1 hf'.2 hfinv hq'.2

theorem pr_shift_neg_theta{γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) {b : Fin e7Data.d}
    (h : pr b γ = 1) : pr (shift (-γ) b) theta = pr b theta - MinData.toWeight γ ⬝ᵥ theta := by
  have h1 : pr b (-γ) = -1 := by rw [pr_neg, h]
  have h3 := pr_shift (isRoot_neg hγ) h1 theta
  rw [MinData.toWeight_neg, neg_dotProduct] at h3
  omega

theorem xu_inv_eq (γ : Fin (Tag.rank .E7) → ℤ) (c : K) :
    (e7Data_valid.xu K γ c)⁻¹ = e7Data_valid.xu K γ (-c) := by
  apply inv_eq_of_mul_eq_one_right
  rw [← e7Data_valid.xu_add K γ c (-c), add_neg_cancel]
  exact e7Data_valid.xu_zero K γ

theorem xu_raises [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hpos : 0 < MinData.toWeight γ ⬝ᵥ theta) (c : K) :
    RaisesFil ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) := by
  intro i v hv
  refine mem_Fil_iff.2 fun b hb => ?_
  rw [Finsupp.sub_apply, xu_apply_coord hγ c v b]
  by_cases h : pr b γ = 1
  · rw [if_pos h]
    have hlt : pr (shift (-γ) b) theta < i := by
      rw [pr_shift_neg_theta hγ h]
      omega
    rw [mem_Fil_iff.1 hv _ hlt]
    ring
  · rw [if_neg h]
    ring

theorem xu_presPiece [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hzero : MinData.toWeight γ ⬝ᵥ theta = 0) (c : K) :
    PresPiece ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) := by
  intro i v hv
  refine mem_Piece_iff.2 fun b hb => ?_
  rw [xu_apply_coord hγ c v b]
  have hvb : v b = 0 := mem_Piece_iff.1 hv b hb
  by_cases h : pr b γ = 1
  · rw [if_pos h]
    have hsh : pr (shift (-γ) b) theta = pr b theta := by
      rw [pr_shift_neg_theta hγ h, hzero, sub_zero]
    have hv' : v (shift (-γ) b) = 0 :=
      mem_Piece_iff.1 hv (shift (-γ) b) (by rw [hsh]; exact hb)
    rw [hvb, hv', mul_zero, add_zero]
  · rw [if_neg h, mul_zero, add_zero]
    exact hvb

theorem xu_mem_NN [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hpos : 0 < MinData.toWeight γ ⬝ᵥ theta) (c : K) : e7Data_valid.xu K γ c ∈ NN K := by
  show RaisesFil ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
    RaisesFil (((e7Data_valid.xu K γ c)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
  refine ⟨xu_raises hγ hpos c, ?_⟩
  rw [xu_inv_eq]
  exact xu_raises hγ hpos (-c)

theorem xu_mem_GG [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hzero : MinData.toWeight γ ⬝ᵥ theta = 0) (c : K) : e7Data_valid.xu K γ c ∈ GG K := by
  show PresPiece ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) ∧
    PresPiece (((e7Data_valid.xu K γ c)⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
  refine ⟨xu_presPiece hγ hzero c, ?_⟩
  rw [xu_inv_eq]
  exact xu_presPiece hγ hzero (-c)

@[expose] def UL (K : Type) [Field K] : Subgroup (Module.End K (V K))ˣ :=
  Subgroup.closure {g | ∃ β : Fin (Tag.rank .E7) → ℤ, IsRoot .E7 β ∧
    MinData.toWeight β ⬝ᵥ theta = 0 ∧ 0 < height β ∧ ∃ c : K, g = e7Data_valid.xu K β c}

theorem UL_le_GG [CharP K 2] : UL K ≤ GG K := by
  rw [UL, Subgroup.closure_le]
  rintro g ⟨β, hβ, hzero, -, c, rfl⟩
  exact xu_mem_GG hβ hzero c

@[expose] def NUL (K : Type) [Field K] [CharP K 2] : Subgroup (Module.End K (V K))ˣ where
  carrier := {g | ∃ q ∈ NN K, ∃ u' ∈ UL K, g = q * u'}
  mul_mem' := by
    rintro a b ⟨q₁, hq₁, u₁, hu₁, rfl⟩ ⟨q₂, hq₂, u₂, hu₂, rfl⟩
    refine ⟨q₁ * (u₁ * q₂ * u₁⁻¹), mul_mem hq₁ (FF_conj_NN (GG_le_FF (UL_le_GG hu₁)) hq₂),
      u₁ * u₂, mul_mem hu₁ hu₂, ?_⟩
    simp [mul_assoc]
  one_mem' := ⟨1, one_mem _, 1, one_mem _, (mul_one 1).symm⟩
  inv_mem' := by
    rintro x ⟨q, hq, u', hu', rfl⟩
    refine ⟨u'⁻¹ * q⁻¹ * u'⁻¹⁻¹, FF_conj_NN (GG_le_FF (UL_le_GG (inv_mem hu'))) (inv_mem hq),
      u'⁻¹, inv_mem hu', ?_⟩
    simp [mul_assoc]

theorem xm_mem_NUL [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ)
    (hpos : 0 < ht γ) (c : K) : e7Data_valid.xu K γ c ∈ NUL K := by
  have hnn : 0 ≤ MinData.toWeight γ ⬝ᵥ theta := by
    rw [pair_theta]
    rcases hγ.nonneg_or_nonpos with h | h
    · exact h node1
    · exfalso
      have hs : ht γ ≤ 0 := by
        unfold ht
        exact Finset.sum_nonpos fun j _ => h j
      omega
  rcases hnn.lt_or_eq with hp | hz
  · exact ⟨e7Data_valid.xu K γ c, xu_mem_NN hγ hp c, 1, one_mem _, (mul_one _).symm⟩
  · have hmem : e7Data_valid.xu K γ c ∈ {g : (Module.End K (V K))ˣ | ∃ β : Fin (Tag.rank .E7) → ℤ,
        IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 ∧ 0 < height β ∧
          ∃ d : K, g = e7Data_valid.xu K β d} :=
      ⟨γ, hγ, hz.symm, hpos, c, rfl⟩
    exact ⟨1, one_mem _, e7Data_valid.xu K γ c, Subgroup.subset_closure hmem, (one_mul _).symm⟩

theorem uni_decomp [CharP K 2] {u : ↥(e7Data_valid.minGroup K)} (hu : u ∈ Uni K) :
    ∃ q ∈ NN K, ∃ u' ∈ UL K, ((u : (Module.End K (V K))ˣ)) = q * u' := by
  have key : Uni K ≤ (NUL K).comap (e7Data_valid.minGroup K).subtype := by
    unfold Uni CFSG.LieType.Steinberg.posUnipotent
    refine iSup₂_le fun γ hγ => ?_
    obtain ⟨hγr, hγp⟩ : γ ∈ (e7Datum K).roots ∧ 0 < ht γ := hγ
    have hr : IsRoot .E7 γ := (e7Data_valid.mem_minDatum_roots isFiniteType_cartan_E7 K).1 hγr
    rintro x hx
    obtain ⟨c, rfl⟩ := (e7Data_valid.mem_rootGroup K).1 hx
    exact Subgroup.mem_comap.2 (xm_mem_NUL hr hγp c)
  obtain ⟨q, hq, u', hu', e⟩ := Subgroup.mem_comap.1 (key hu)
  exact ⟨q, hq, u', hu', e⟩

theorem piece_mem_fil {i : ℤ} {v : V K} (hv : v ∈ Piece K i) : v ∈ Fil K i :=
  mem_Fil_iff.2 fun b hb => mem_Piece_iff.1 hv b (ne_of_lt hb)

theorem raises_coord_eq {q : Module.End K (V K)} (hq : RaisesFil q) {i : ℤ} {z : V K}
    (hz : z ∈ Piece K i) {b : Fin e7Data.d} (hb : pr b theta = i) :
    (q z) b = z b := by
  have h1 : q z - z ∈ Fil K (i + 1) := hq i z (piece_mem_fil hz)
  have h2 : (q z - z) b = 0 := mem_Fil_iff.1 h1 b (by omega)
  rw [Finsupp.sub_apply] at h2
  exact sub_eq_zero.1 h2

theorem endoE_eq_zero_of {g : ↥(e7Data_valid.minGroup K)} {x : V K} (h0 : endoE g x = 0) :
    x = 0 := by
  have h1 : endoE (g⁻¹) (endoE g x) = x := by
    rw [← Module.End.mul_apply, e7Data_valid.endo_inv_mul, Module.End.one_apply]
  rw [h0, map_zero] at h1
  exact h1.symm

theorem hwVec_V0 [CharP K 2] {g : ↥(e7Data_valid.minGroup K)} (h : endoE g w0 ∈ V0 K) :
    ∃ u' ∈ UL K, ∃ μ ∈ idx0, ∃ c : K, c ≠ 0 ∧
      endoE g w0 = c • (u' : Module.End K (V K)) (Finsupp.single μ 1) := by
  obtain ⟨w, b₁, hb₁, b₂, hb₂, rfl⟩ := bruhat_decomp g
  obtain ⟨c₂, hc₂⟩ := endo_bor_w0 (K := K) hb₂
  obtain ⟨μ', hμ'⟩ := endo_nW_single (K := K) w ⟨0, by decide⟩
  have hμ'' : endoE (nW K w) w0 = Finsupp.single μ' 1 := hμ'
  obtain ⟨u, hu, t, ht, rfl⟩ := bor_eq_mul (K := K) hb₁
  obtain ⟨ct, hct⟩ := endo_tor_single (K := K) ht μ'
  obtain ⟨q, hq, u', hu', huq⟩ := uni_decomp (K := K) hu
  have hqR : RaisesFil (q : Module.End K (V K)) :=
    (show RaisesFil (q : Module.End K (V K)) ∧
      RaisesFil ((q⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) from hq).1
  have hpp : PresPiece (u' : Module.End K (V K)) :=
    (show PresPiece (u' : Module.End K (V K)) ∧
      PresPiece ((u'⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) from
        UL_le_GG (K := K) hu').1
  have hendo_u : ∀ v : V K,
      endoE u v = (q : Module.End K (V K)) ((u' : Module.End K (V K)) v) := by
    intro v
    change ((u : (Module.End K (V K))ˣ) : Module.End K (V K)) v = _
    rw [huq, Units.val_mul, Module.End.mul_apply]
  have hX : endoE (u * t * nW K w * b₂) w0 =
      (c₂ * ct) • (q : Module.End K (V K)) ((u' : Module.End K (V K)) (Finsupp.single μ' 1)) := by
    change endoE u (endoE t (endoE (nW K w) (endoE b₂ w0))) = _
    rw [hc₂, map_smul, hμ'', map_smul, hct, map_smul, map_smul, hendo_u, smul_smul]
  have hw0ne : (w0 : V K) ≠ 0 := Finsupp.single_ne_zero.2 one_ne_zero
  have hc : c₂ * ct ≠ 0 := by
    intro h0
    have hX0 : endoE (u * t * nW K w * b₂) w0 = 0 := by rw [hX, h0, zero_smul]
    exact hw0ne (endoE_eq_zero_of hX0)
  rw [hX] at h
  have hsingle : (Finsupp.single μ' 1 : V K) ∈ Piece K (pr μ' theta) := by
    refine mem_Piece_iff.2 fun b hb => ?_
    have hne : μ' ≠ b := fun hμb => hb (by rw [hμb])
    rw [Finsupp.single_apply, if_neg hne]
  have hz_piece : (u' : Module.End K (V K)) (Finsupp.single μ' 1) ∈ Piece K (pr μ' theta) :=
    hpp (pr μ' theta) _ hsingle
  have hz_ne : (u' : Module.End K (V K)) (Finsupp.single μ' 1) ≠ 0 := by
    intro hz0
    have h2 := congrArg ((u'⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) hz0
    rw [map_zero, ← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply] at h2
    exact (Finsupp.single_ne_zero.2 one_ne_zero) h2
  obtain ⟨b₀, hb₀⟩ : ∃ b₀, ((u' : Module.End K (V K)) (Finsupp.single μ' 1)) b₀ ≠ 0 := by
    by_contra hcon
    refine hz_ne (Finsupp.ext fun b => ?_)
    by_contra hb
    exact hcon ⟨b, by simpa using hb⟩
  have hb₀deg : pr b₀ theta = pr μ' theta := by
    by_contra hne
    exact hb₀ (mem_Piece_iff.1 hz_piece b₀ hne)
  have hXb₀ : ((c₂ * ct) • (q : Module.End K (V K)) ((u' : Module.End K (V K))
      (Finsupp.single μ' 1))) b₀ ≠ 0 := by
    rw [Finsupp.smul_apply, smul_eq_mul, raises_coord_eq hqR hz_piece hb₀deg]
    exact mul_ne_zero hc hb₀
  have hb₀0 : pr b₀ theta = 0 := by
    by_contra hne
    exact hXb₀ (mem_V0.1 h b₀ fun hm => hne (mem_idx0.1 hm))
  have hμ0 : pr μ' theta = 0 := hb₀deg.symm.trans hb₀0
  have hz0 : (u' : Module.End K (V K)) (Finsupp.single μ' 1) ∈ Piece K 0 := by
    rw [← hμ0]
    exact hz_piece
  have hqz : (q : Module.End K (V K)) ((u' : Module.End K (V K)) (Finsupp.single μ' 1)) =
      (u' : Module.End K (V K)) (Finsupp.single μ' 1) := by
    ext b
    by_cases hb : pr b theta = 0
    · have h1 : (q : Module.End K (V K)) ((u' : Module.End K (V K)) (Finsupp.single μ' 1)) -
          (u' : Module.End K (V K)) (Finsupp.single μ' 1) ∈ Fil K (0 + 1) :=
        hqR 0 _ (piece_mem_fil hz0)
      have h2 := mem_Fil_iff.1 h1 b (by omega)
      rw [Finsupp.sub_apply] at h2
      exact sub_eq_zero.1 h2
    · have hXb : ((c₂ * ct) • (q : Module.End K (V K)) ((u' : Module.End K (V K))
          (Finsupp.single μ' 1))) b = 0 :=
        mem_V0.1 h b fun hm => hb (mem_idx0.1 hm)
      rw [Finsupp.smul_apply, smul_eq_mul] at hXb
      have hqb : (q : Module.End K (V K)) ((u' : Module.End K (V K)) (Finsupp.single μ' 1)) b = 0 :=
        (mul_eq_zero.1 hXb).resolve_left hc
      rw [hqb, mem_Piece_iff.1 hz0 b hb]
  exact ⟨u', hu', μ', mem_idx0.2 hμ0, c₂ * ct, hc, by rw [hX, hqz]⟩

end CFSG.RankThree.GF2n.Smith81.E7Model
