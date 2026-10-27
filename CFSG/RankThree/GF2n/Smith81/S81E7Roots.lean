module

public import CFSG.RankThree.GF2n.Smith81.S81E7Hwl
public import CFSG.RankThree.GF2n.Smith81.S81E7Lam
public import CFSG.RankThree.GF2n.Smith81.S81E7Fe3

public noncomputable section

namespace CFSG.RankThree.GF2n.Smith81.E7Model

open CFSG.LieType.Steinberg.Minuscule CFSG.Blueprint.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits


variable {K : Type} [Field K]

theorem tor_conj_xm {t : ↥(e7Data_valid.minGroup K)} (ht : t ∈ Tor K)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) :
    ∃ s : K, s ≠ 0 ∧ ∀ c : K, t * e7Data_valid.xm K γ c * t⁻¹ = e7Data_valid.xm K γ (s * c) := by
  refine Subgroup.iSup_induction (fun i => e7Data_valid.torus K i)
    (C := fun t => ∃ s : K, s ≠ 0 ∧ ∀ c : K,
      t * e7Data_valid.xm K γ c * t⁻¹ = e7Data_valid.xm K γ (s * c)) ht ?_ ?_ ?_
  · intro i x hx
    obtain ⟨s, rfl⟩ := (e7Data_valid.mem_torus K).1 hx
    exact ⟨((s ^ MinData.toWeight γ i : Kˣ) : K), Units.ne_zero _,
      fun c => e7Data_valid.hm_conj_xm K hγ i s c⟩
  · exact ⟨1, one_ne_zero, fun c => by simp⟩
  · rintro x y ⟨sx, hsx, hx⟩ ⟨sy, hsy, hy⟩
    refine ⟨sx * sy, mul_ne_zero hsx hsy, fun c => ?_⟩
    calc x * y * e7Data_valid.xm K γ c * (x * y)⁻¹
        = x * (y * e7Data_valid.xm K γ c * y⁻¹) * x⁻¹ := by group
      _ = x * e7Data_valid.xm K γ (sy * c) * x⁻¹ := by rw [hy c]
      _ = e7Data_valid.xm K γ (sx * (sy * c)) := hx _
      _ = e7Data_valid.xm K γ (sx * sy * c) := by rw [mul_assoc]

theorem NN_inf_GG {g : (Module.End K (V K))ˣ} (h1 : g ∈ NN K) (h2 : g ∈ GG K) : g = 1 := by
  have hR : RaisesFil (g : Module.End K (V K)) :=
    (show RaisesFil (g : Module.End K (V K)) ∧
      RaisesFil ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) from h1).1
  have hP : PresPiece (g : Module.End K (V K)) :=
    (show PresPiece (g : Module.End K (V K)) ∧
      PresPiece ((g⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) from h2).1
  have hfix : ∀ a : Fin e7Data.d,
      (g : Module.End K (V K)) (Finsupp.single a 1) = Finsupp.single a 1 := by
    intro a
    have hs : (Finsupp.single a (1 : K) : V K) ∈ Piece K (pr a theta) := by
      refine mem_Piece_iff.2 fun b hb => ?_
      have hne : a ≠ b := fun hab => hb (by rw [hab])
      rw [Finsupp.single_apply, if_neg hne]
    have hF := hR (pr a theta) _ (piece_mem_fil hs)
    have hPg := hP (pr a theta) _ hs
    refine Finsupp.ext fun b => ?_
    by_cases hb : pr b theta = pr a theta
    · have h3 := mem_Fil_iff.1 hF b (by omega)
      rw [Finsupp.sub_apply, sub_eq_zero] at h3
      exact h3
    · rw [mem_Piece_iff.1 hPg b hb, mem_Piece_iff.1 hs b hb]
  have key : ∀ (a : Fin e7Data.d) (b : K),
      (g : Module.End K (V K)) (Finsupp.single a b) = Finsupp.single a b := by
    intro a b
    have e : (Finsupp.single a b : V K) = b • Finsupp.single a 1 := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    rw [e, map_smul, hfix a]
  apply Units.ext
  rw [Units.val_one]
  apply Finsupp.lhom_ext
  intro a b
  rw [Module.End.one_apply]
  exact key a b

theorem rootElt_form [CharP K 2] {t : (Module.End K (V K))ˣ} (ht : IsRootElt t) :
    ∃ (q u'' : (Module.End K (V K))ˣ) (γ' : Fin (Tag.rank .E7) → ℤ) (c : K),
      q ∈ NN K ∧ u'' ∈ UL K ∧ IsRoot .E7 γ' ∧ c ≠ 0 ∧
        t = q * (u'' * e7Data_valid.xu K γ' c * u''⁻¹) * q⁻¹ := by
  unfold IsRootElt at ht
  obtain ⟨h, hh, γ, c, hγ, hc, rfl⟩ := ht
  set H : ↥(e7Data_valid.minGroup K) := ⟨h, hh⟩ with hH
  have hxG : IsRootEltG (H * e7Data_valid.xm K γ c * H⁻¹) := by
    unfold IsRootEltG
    exact ⟨H, γ, c, hγ, hc, rfl⟩
  obtain ⟨p, c₁, hc₁, hp⟩ := fe3_isRootEltG_conj_theta hxG
  obtain ⟨w, b₁, hb₁, b₂, hb₂, hg⟩ := bruhat_decomp p
  subst hg
  obtain ⟨d', hconj₂, hdd⟩ := bor_conj_xm_theta hb₂ c₁
  obtain ⟨γ', c'', hγ', hconjW, hcc⟩ := nW_conj_xm_theta w d'
  obtain ⟨u, hu, t', ht', rfl⟩ := bor_eq_mul hb₁
  obtain ⟨s, hs, hts⟩ := tor_conj_xm ht' hγ'
  have hc'' : c'' ≠ 0 := hcc (hdd hc₁)
  have hx2 : H * e7Data_valid.xm K γ c * H⁻¹ = u * e7Data_valid.xm K γ' (s * c'') * u⁻¹ := by
    rw [hp, ← hts c'', ← hconjW, ← hconj₂]
    group
  obtain ⟨q, hq, u'', hu'', huq⟩ := uni_decomp (K := K) hu
  refine ⟨q, u'', γ', s * c'', hq, hu'', hγ', mul_ne_zero hs hc'', ?_⟩
  calc h * e7Data_valid.xu K γ c * h⁻¹
      = ((H * e7Data_valid.xm K γ c * H⁻¹ : ↥(e7Data_valid.minGroup K)) :
          (Module.End K (V K))ˣ) := rfl
    _ = ((u * e7Data_valid.xm K γ' (s * c'') * u⁻¹ : ↥(e7Data_valid.minGroup K)) :
          (Module.End K (V K))ˣ) := by rw [hx2]
    _ = (u : (Module.End K (V K))ˣ) * e7Data_valid.xu K γ' (s * c'') *
          (u : (Module.End K (V K))ˣ)⁻¹ := rfl
    _ = (q * u'') * e7Data_valid.xu K γ' (s * c'') * (q * u'')⁻¹ := by rw [huq]
    _ = q * (u'' * e7Data_valid.xu K γ' (s * c'') * u''⁻¹) * q⁻¹ := by group

theorem Lam_le_GG [CharP K 2] : Lam K ≤ GG K := by
  rw [Lam, Subgroup.closure_le]
  rintro g ⟨β, hβ, c, rfl⟩
  have hβ' : IsRoot .E7 β ∧ MinData.toWeight β ⬝ᵥ theta = 0 := hβ
  exact xu_mem_GG hβ'.1 hβ'.2 c

theorem units_inv_apply_apply (u : (Module.End K (V K))ˣ) (x : V K) :
    ((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) ((u : Module.End K (V K)) x) = x := by
  rw [← Module.End.mul_apply, Units.inv_mul, Module.End.one_apply]

theorem units_apply_inv_apply (u : (Module.End K (V K))ˣ) (x : V K) :
    (u : Module.End K (V K)) (((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) x) = x := by
  rw [← Module.End.mul_apply, Units.mul_inv, Module.End.one_apply]

theorem conj_apply_sub (u E : (Module.End K (V K))ˣ) (x : V K) :
    ((u * E * u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) ((u : Module.End K (V K)) x) -
      (u : Module.End K (V K)) x = (u : Module.End K (V K)) ((E : Module.End K (V K)) x - x) := by
  rw [map_sub, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply,
    units_inv_apply_apply]

theorem conj_apply_sub' (u E : (Module.End K (V K))ˣ) (v : V K) :
    ((u * E * u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) v - v =
      (u : Module.End K (V K)) ((E : Module.End K (V K))
        (((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) v) -
          ((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) v) := by
  have h := conj_apply_sub u E (((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) v)
  rw [units_apply_inv_apply] at h
  exact h

theorem xu_sub_coord [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K)
    (x : V K) (b : Fin e7Data.d) :
    ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) x b - x b =
      c * (if pr b γ = 1 then x (shift (-γ) b) else 0) := by
  rw [xu_apply_coord hγ c x b]
  ring

theorem xu_sub_mem_Fil [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K)
    {x : V K} {j : ℤ} (hx : x ∈ Fil K j) :
    ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) x - x ∈
      Fil K (j + MinData.toWeight γ ⬝ᵥ theta) := by
  refine mem_Fil_iff.2 fun b hb => ?_
  rw [Finsupp.sub_apply, xu_sub_coord hγ c x b]
  by_cases h : pr b γ = 1
  · rw [if_pos h]
    have hlt : pr (shift (-γ) b) theta < j := by
      rw [pr_shift_neg_theta hγ h]
      omega
    rw [mem_Fil_iff.1 hx _ hlt, mul_zero]
  · rw [if_neg h, mul_zero]

theorem xu_sub_mem_Piece [CharP K 2] {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K)
    {x : V K} {i : ℤ} (hx : x ∈ Piece K i) :
    ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) x - x ∈
      Piece K (i + MinData.toWeight γ ⬝ᵥ theta) := by
  refine mem_Piece_iff.2 fun b hb => ?_
  rw [Finsupp.sub_apply, xu_sub_coord hγ c x b]
  by_cases h : pr b γ = 1
  · rw [if_pos h]
    have hsh : pr (shift (-γ) b) theta ≠ i := by
      rw [pr_shift_neg_theta hγ h]
      omega
    rw [mem_Piece_iff.1 hx _ hsh, mul_zero]
  · rw [if_neg h, mul_zero]

theorem conj_xu_sub_Fil [CharP K 2] {u : (Module.End K (V K))ˣ} (hu : u ∈ GG K)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) {x : V K} {j : ℤ}
    (hx : x ∈ Fil K j) :
    ((u * e7Data_valid.xu K γ c * u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) x - x ∈
      Fil K (j + MinData.toWeight γ ⬝ᵥ theta) := by
  have hu' : PresPiece (u : Module.End K (V K)) ∧
      PresPiece ((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := hu
  have hf : PresFil (u : Module.End K (V K)) ∧
      PresFil ((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) :=
    ⟨presFil_of_presPiece hu'.1, presFil_of_presPiece hu'.2⟩
  rw [conj_apply_sub']
  exact hf.1 _ _ (xu_sub_mem_Fil hγ c (hf.2 j x hx))

theorem conj_xu_sub_Piece [CharP K 2] {u : (Module.End K (V K))ˣ} (hu : u ∈ GG K)
    {γ : Fin (Tag.rank .E7) → ℤ} (hγ : IsRoot .E7 γ) (c : K) {x : V K} {i : ℤ}
    (hx : x ∈ Piece K i) :
    ((u * e7Data_valid.xu K γ c * u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) x - x ∈
      Piece K (i + MinData.toWeight γ ⬝ᵥ theta) := by
  have hu' : PresPiece (u : Module.End K (V K)) ∧
      PresPiece ((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := hu
  rw [conj_apply_sub']
  exact hu'.1 _ _ (xu_sub_mem_Piece hγ c (hu'.2 i x hx))

theorem single_mem_Piece (a : Fin e7Data.d) :
    (Finsupp.single a (1 : K) : V K) ∈ Piece K (pr a theta) := by
  refine mem_Piece_iff.2 fun b hb => ?_
  have hne : a ≠ b := fun h => hb (by rw [h])
  rw [Finsupp.single_apply, if_neg hne]

theorem degree_core {Q Qi Y Tt : Module.End K (V K)} {k : ℤ} (hk : k ≠ 0) {i : ℤ}
    (hQ : RaisesFil Q) (hQi : RaisesFil Qi) (hQQi : Q * Qi = 1)
    (hY : ∀ (j : ℤ) (v : V K), v ∈ Fil K j → Y v - v ∈ Fil K (j + k))
    (hYP : ∀ v : V K, v ∈ Piece K i → Y v - v ∈ Piece K (i + k))
    (hT : ∀ v : V K, v ∈ Piece K i → Tt v ∈ Piece K i)
    (hTeq : Tt = Q * Y * Qi) {z : V K} (hz : z ∈ Piece K i) :
    Y z - z = 0 := by
  have hQz : Q (Qi z) = z := by
    rw [← Module.End.mul_apply, hQQi, Module.End.one_apply]
  have hr : Qi z - z ∈ Fil K (i + 1) := hQi i z (piece_mem_fil hz)
  have hB : Y (Qi z - z) - (Qi z - z) ∈ Fil K (i + 1 + k) := hY (i + 1) _ hr
  have hA : Y z - z ∈ Piece K (i + k) := hYP z hz
  have hm : Y (Qi z) - Qi z = (Y z - z) + (Y (Qi z - z) - (Qi z - z)) := by
    rw [map_sub]
    abel
  have hmFil : Y (Qi z) - Qi z ∈ Fil K (i + k) := by
    rw [hm]
    exact add_mem_Fil (piece_mem_fil hA) (Fil_anti (show i + k ≤ i + 1 + k by omega) hB)
  have hC : Q (Y (Qi z) - Qi z) - (Y (Qi z) - Qi z) ∈ Fil K (i + k + 1) :=
    hQ (i + k) _ hmFil
  have hTz : Tt z - z = Q (Y (Qi z) - Qi z) := by
    rw [hTeq, Module.End.mul_apply, Module.End.mul_apply, map_sub, hQz]
  have hTz2 : Tt z - z = (Y (Qi z) - Qi z) + (Q (Y (Qi z) - Qi z) - (Y (Qi z) - Qi z)) := by
    rw [hTz]
    abel
  refine Finsupp.ext fun b => ?_
  rw [Finsupp.zero_apply]
  by_cases hb : pr b theta = i + k
  · have hbB : (Y (Qi z - z) - (Qi z - z)) b = 0 := mem_Fil_iff.1 hB b (by omega)
    have hbC : (Q (Y (Qi z) - Qi z) - (Y (Qi z) - Qi z)) b = 0 := mem_Fil_iff.1 hC b (by omega)
    have hmb : (Y (Qi z) - Qi z) b = (Y z - z) b := by
      rw [hm, Finsupp.add_apply, hbB, add_zero]
    have hTb : (Tt z - z) b = 0 := by
      have hbi : pr b theta ≠ i := by omega
      rw [Finsupp.sub_apply, mem_Piece_iff.1 (hT z hz) b hbi, mem_Piece_iff.1 hz b hbi, sub_zero]
    have key : (Tt z - z) b = (Y z - z) b := by
      rw [hTz2, Finsupp.add_apply, hbC, add_zero, hmb]
    exact key.symm.trans hTb
  · exact mem_Piece_iff.1 hA b hb

theorem main_core [CharP K 2] {t q u : (Module.End K (V K))ˣ} {γ : Fin (Tag.rank .E7) → ℤ}
    {c : K} (hq : q ∈ NN K) (hu : u ∈ UL K) (hγ : IsRoot .E7 γ) (hc : c ≠ 0)
    (ht_eq : t = q * (u * e7Data_valid.xu K γ c * u⁻¹) * q⁻¹) (htΛ : t ∈ GG K) :
    MinData.toWeight γ ⬝ᵥ theta = 0 := by
  have hq' : RaisesFil (q : Module.End K (V K)) ∧
      RaisesFil ((q⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := hq
  have huGG : u ∈ GG K := UL_le_GG (K := K) hu
  have htGG : PresPiece (t : Module.End K (V K)) :=
    (show PresPiece (t : Module.End K (V K)) ∧
      PresPiece ((t⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) from htΛ).1
  obtain ⟨Y, hY⟩ : ∃ Y : Module.End K (V K),
      ((u * e7Data_valid.xu K γ c * u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) = Y :=
    ⟨_, rfl⟩
  have hTeq : (t : Module.End K (V K)) =
      (q : Module.End K (V K)) * Y * ((q⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) := by
    rw [← hY, ht_eq]
    simp only [Units.val_mul]
  have hQQi : (q : Module.End K (V K)) * ((q⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K)) = 1 :=
    Units.mul_inv q
  by_contra hk
  have hall : ∀ a : Fin e7Data.d, Y (Finsupp.single a 1) - Finsupp.single a 1 = 0 := fun a =>
    degree_core (Q := (q : Module.End K (V K)))
      (Qi := ((q⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))) (Y := Y)
      (Tt := (t : Module.End K (V K))) (i := pr a theta) hk hq'.1 hq'.2 hQQi
      (fun j v hv => by rw [← hY]; exact conj_xu_sub_Fil huGG hγ c hv)
      (fun v hv => by rw [← hY]; exact conj_xu_sub_Piece huGG hγ c hv)
      (fun v hv => htGG _ v hv) hTeq (single_mem_Piece a)
  have hallv : ∀ v : V K, Y v - v = 0 := by
    intro v
    induction v using Finsupp.induction_linear with
    | zero => simp
    | add f g hf hg =>
      rw [sub_eq_zero] at hf hg ⊢
      rw [map_add, hf, hg]
    | single a c' =>
      have e : (Finsupp.single a c' : V K) = c' • Finsupp.single a 1 := by
        rw [Finsupp.smul_single_one]
      rw [e, map_smul, ← smul_sub, hall a, smul_zero]
  have hEx : ∀ x : V K,
      ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) x - x = 0 := by
    intro x
    have h2 : Y ((u : Module.End K (V K)) x) - (u : Module.End K (V K)) x =
        (u : Module.End K (V K))
          (((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) x - x) := by
      rw [← hY]
      exact conj_apply_sub u _ x
    have h3 := hallv ((u : Module.End K (V K)) x)
    rw [h2] at h3
    calc ((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) x - x
        = ((u⁻¹ : (Module.End K (V K))ˣ) : Module.End K (V K))
            ((u : Module.End K (V K))
              (((e7Data_valid.xu K γ c : (Module.End K (V K))ˣ) : Module.End K (V K)) x - x)) :=
          (units_inv_apply_apply u _).symm
      _ = 0 := by rw [h3, map_zero]
  have hrootOp : ∀ x : V K, e7Data.rootOp K γ x = 0 := by
    intro x
    have h := hEx x
    rw [e7Data_valid.xu_apply] at h
    simpa [hc] using h
  exact e7Data_valid.rootOp_ne_zero (R := K) hγ
    (LinearMap.ext fun x => (hrootOp x).trans (LinearMap.zero_apply x).symm)

theorem rootElt_Lam_form [CharP K 2] {t : (Module.End K (V K))ˣ} (ht : IsRootElt t)
    (hΛ : t ∈ Lam K) :
    ∃ u' ∈ UL K, ∃ β ∈ Perp, ∃ c : K, c ≠ 0 ∧ t = u' * e7Data_valid.xu K β c * u'⁻¹ := by
  obtain ⟨q, u, γ', c, hq, hu, hγ', hc, ht_eq⟩ := rootElt_form ht
  have hk0 : MinData.toWeight γ' ⬝ᵥ theta = 0 :=
    main_core hq hu hγ' hc ht_eq (Lam_le_GG (K := K) hΛ)
  have huGG : u ∈ GG K := UL_le_GG (K := K) hu
  have hyGG : u * e7Data_valid.xu K γ' c * u⁻¹ ∈ GG K :=
    mul_mem (mul_mem huGG (xu_mem_GG hγ' hk0 c)) (inv_mem huGG)
  have hconj : (u * e7Data_valid.xu K γ' c * u⁻¹) * q⁻¹ * (u * e7Data_valid.xu K γ' c * u⁻¹)⁻¹ ∈
      NN K :=
    FF_conj_NN (GG_le_FF hyGG) (inv_mem hq)
  have htK : t * (u * e7Data_valid.xu K γ' c * u⁻¹)⁻¹ = 1 := by
    apply NN_inf_GG
    · have e : t * (u * e7Data_valid.xu K γ' c * u⁻¹)⁻¹ =
          q * ((u * e7Data_valid.xu K γ' c * u⁻¹) * q⁻¹ * (u * e7Data_valid.xu K γ' c * u⁻¹)⁻¹) := by
        rw [ht_eq]
        simp only [mul_assoc]
      rw [e]
      exact mul_mem hq hconj
    · exact mul_mem (Lam_le_GG (K := K) hΛ) (inv_mem hyGG)
  have hperp : γ' ∈ Perp := (⟨hγ', hk0⟩ : IsRoot .E7 γ' ∧ MinData.toWeight γ' ⬝ᵥ theta = 0)
  exact ⟨u, hu, γ', hperp, c, hc, mul_inv_eq_one.1 htK⟩

end CFSG.RankThree.GF2n.Smith81.E7Model
