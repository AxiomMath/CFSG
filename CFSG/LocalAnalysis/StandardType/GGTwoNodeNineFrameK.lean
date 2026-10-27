module

public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepFrameK
public import CFSG.LocalAnalysis.StandardType.GGResTwoNodeIndepTransfer

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem nkF_y_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : y ≠ 1 := by
  intro hy1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hxD : x ∈ D := hpre.2.2.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hxp : x ^ p = 1 := hDea.2 x hxD
  have hDle : D ≤ Subgroup.zpowers x := by
    rw [hDgen, hy1, Subgroup.closure_le]
    intro a ha
    have ha' : a = x ∨ a = 1 := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.mem_zpowers x
    · rw [h]; exact Subgroup.one_mem _
  have hxle : Nat.card (Subgroup.zpowers x) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hxp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers x) := Subgroup.card_le_of_le hDle
      _ ≤ p := hxle
  nlinarith [hcon, hp.two_le]

private theorem nkF_automizer_fixes_y {G : Type} [Group G] [Finite G] {Bs K : Subgroup G}
    {y : G} (hy : y ∈ Bs)
    (hKy : K ≤ Subgroup.centralizer ({y} : Set G)) :
    ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨y, hy⟩ = ⟨y, hy⟩ := by
  have hle : ggAutomizer K Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨y, hy⟩ : ↥Bs) := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro ψ hψ
    obtain ⟨g, hgK, -, hg⟩ := hψ
    have hmem : g ∈ Subgroup.centralizer ({y} : Set G) := hKy hgK
    have hcomm : g * y = y * g :=
      ((Subgroup.mem_centralizer_iff.mp hmem) y (by simp)).symm
    change ψ • (⟨y, hy⟩ : ↥Bs) = (⟨y, hy⟩ : ↥Bs)
    rw [MulAut.smul_def]
    apply Subtype.ext
    have h : ((ψ ⟨y, hy⟩ : ↥Bs) : G) = g * y * g⁻¹ := by
      have h1 := hg (⟨y, hy⟩ : ↥Bs)
      simpa using h1
    rw [h, hcomm]
    group
  intro ψ hψ
  simpa only [MulAction.mem_stabilizer_iff, MulAut.smul_def] using hle hψ

private theorem nkF_alpha_y {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    {Λ : Type} {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α i (h j) = (CK i j : ZMod p))
    (hCK : GGIntCartan MK CK)
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ∀ j : Λ, α j (ι (Additive.ofMul ⟨y, hy⟩)) = 0 := by
  intro j
  have hfix := nkF_automizer_fixes_y hy hH.2.2.2.2.1.1.2.2.2.1
  have hmem : φ j ∈ ggAutomizer K Bs := by
    rw [hAK]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hfixj : φ j ⟨y, hy⟩ = ⟨y, hy⟩ := hfix (φ j) hmem
  have hlin : ggLin (p := p) ι (φ j) (ι (Additive.ofMul ⟨y, hy⟩)) =
      ι (Additive.ofMul ⟨y, hy⟩) :=
    (ggLin_fix_iff (p := p) ι (φ j) ⟨y, hy⟩).mp hfixj
  have h1 := hφ j (ι (Additive.ofMul ⟨y, hy⟩))
  rw [hlin] at h1
  have h2 : α j (ι (Additive.ofMul ⟨y, hy⟩)) • h j = 0 :=
    sub_eq_self.mp h1.symm
  have h3 : α j (α j (ι (Additive.ofMul ⟨y, hy⟩)) • h j) = 0 := by
    rw [h2, map_zero]
  have hpair : α j (h j) = (2 : ZMod p) := by
    rw [hL j j, hCK.1 j]
    norm_num
  rw [map_smul, smul_eq_mul, hpair] at h3
  exact (mul_eq_zero.mp h3).resolve_right (zmod_two_ne_zero hp2)

private theorem nkF_fix_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {Bs K : Subgroup G}
    {y : G} (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    {Λ : Type} [Fintype Λ] {V : Type} [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ)) :
    ∀ v : V, (∀ j : Λ, α j v = 0) →
      v ∈ Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨y, hy⟩)} : Set V) := by
  intro v hα
  let bb : Bs := Additive.toMul (ι.symm v)
  have hbbw : ι (Additive.ofMul bb) = v := by
    dsimp only [bb]
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hbb : ∀ j : Λ, φ j bb = bb := by
    intro j
    refine (ggLin_fix_iff (p := p) ι (φ j) bb).mpr ?_
    rw [hbbw]
    have h1 := hφ j v
    rw [hα j, zero_smul, sub_zero] at h1
    exact h1
  have hfixK : ∀ ψ ∈ ggAutomizer K Bs, ψ bb = bb := by
    rw [hAK]
    exact ggFixed_of_mem_closure φ bb hbb
  have hymem : (bb : G) ∈ Subgroup.zpowers y := hstrong bb hfixK
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hymem
  have hbk : bb = (⟨y, hy⟩ : Bs) ^ k := Subtype.ext (by simpa using hk.symm)
  have hof : Additive.ofMul bb = k • Additive.ofMul (⟨y, hy⟩ : Bs) := by
    rw [hbk, ofMul_zpow]
  have hv : v = k • ι (Additive.ofMul ⟨y, hy⟩) := by
    have h := congrArg ι hof
    simpa [hbbw, map_zsmul] using h
  rw [hv]
  have hmem : ι (Additive.ofMul ⟨y, hy⟩) ∈
      Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨y, hy⟩)} : Set V) :=
    Submodule.subset_span rfl
  have hsm := Submodule.smul_mem (Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨y, hy⟩)} : Set V))
    (k : ZMod p) hmem
  rwa [Int.cast_smul_eq_zsmul] at hsm

private lemma nkF_span_gen_le_image {p : ℕ} [Fact p.Prime] {G : Type} [Group G] {Bs X : Subgroup G}
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V) :
    Submodule.span (ZMod p) (Set.range (fun q : ↥(ggAutomizer X Bs) × V =>
        ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2)) ≤
      (ι '' (Additive.ofMul '' (ggBstarComm X Bs : Set ↥Bs)) : Set V) := by
  let H : Submodule (ZMod p) V :=
    { carrier := ι '' (Additive.ofMul '' (ggBstarComm X Bs : Set ↥Bs))
      zero_mem' := ⟨0, ⟨1, Subgroup.one_mem _, rfl⟩, by simp⟩
      add_mem' := by
        rintro u v ⟨du, hdu, rfl⟩ ⟨dv, hdv, rfl⟩
        obtain ⟨cu, hcu, rfl⟩ := hdu
        obtain ⟨cv, hcv, rfl⟩ := hdv
        exact ⟨Additive.ofMul (cu * cv), ⟨cu * cv, Subgroup.mul_mem _ hcu hcv, rfl⟩, by
          show ι (Additive.ofMul (cu * cv)) = ι (Additive.ofMul cu) + ι (Additive.ofMul cv)
          rw [← map_add, ← ofMul_mul]⟩
      smul_mem' := by
        rintro a u ⟨d, hd, rfl⟩
        obtain ⟨c, hc, rfl⟩ := hd
        refine ⟨Additive.ofMul (c ^ a.val), ⟨c ^ a.val, Subgroup.pow_mem _ hc a.val, rfl⟩, ?_⟩
        show ι (Additive.ofMul (c ^ a.val)) = a • ι (Additive.ofMul c)
        have h1 : a • ι (Additive.ofMul c) = (a.val : ℕ) • ι (Additive.ofMul c) := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
        rw [h1, ← map_nsmul, ofMul_pow] }
  intro v hv
  have hle : Submodule.span (ZMod p) (Set.range (fun q : ↥(ggAutomizer X Bs) × V =>
      ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2)) ≤ H := by
    rw [Submodule.span_le]
    rintro v ⟨q, rfl⟩
    change ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2 ∈ (H : Set V)
    obtain ⟨b, hb⟩ := ι.surjective q.2
    have hb' : q.2 = ι (Additive.ofMul (Additive.toMul b)) := by
      rw [← hb]
      exact congrArg ι (ofMul_toMul b).symm
    rw [hb']
    refine ⟨Additive.ofMul ((Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b)),
      ⟨(Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b), ?_, rfl⟩, ?_⟩
    · exact Subgroup.subset_closure ⟨Additive.toMul b, q.1, q.1.2, rfl⟩
    · show ι (Additive.ofMul ((Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b))) =
        ggLin (p := p) ι (q.1 : MulAut ↥Bs) (ι (Additive.ofMul (Additive.toMul b))) -
          ι (Additive.ofMul (Additive.toMul b))
      rw [ggLin_apply_ofMul]
      have hkeyV : ι (Additive.ofMul ((Additive.toMul b)⁻¹ * (q.1 : MulAut ↥Bs) (Additive.toMul b))) =
          ι (Additive.ofMul ((q.1 : MulAut ↥Bs) (Additive.toMul b))) -
            ι (Additive.ofMul (Additive.toMul b)) := by
        rw [ofMul_mul, ofMul_inv, map_add, map_neg]
        abel
      exact hkeyV
  exact hle hv

theorem ggNineDepK_dep_of_notComm {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    {N : ℕ} (hN : 5 ≤ N) (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {MK : CoxeterMatrix Λ} {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ)
    (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e) (hCK : GGIntCartan MK CK) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hrefl : ∀ i, GGIsReflection p (φ i)) (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hnc : y ∉ (ggBstarComm K Bs).map Bs.subtype) :
    ¬ LinearIndependent (ZMod p) h := by
  intro hind
  have Find := ggXDatumA_indep_frame_K hp2 hH hy hstrong hN hpN e hMK hCK hφ hpair hAK hind
  have hrange : Set.range (fun i : Fin (N - 1) => h (e i)) = Set.range h :=
    e.surjective.range_comp h
  have hymem : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∈ Submodule.span (ZMod p) (Set.range h) := by
    rw [← hrange]
    exact Find.x_mem
  have hspan := l6tr_span_eq (p := p) (X := K) (Bs := Bs) (ι := ι) (φ := φ) (h := h) (α := α)
    hφ hrefl hAK
  have hygen : ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) ∈
      Submodule.span (ZMod p) (Set.range (fun q : ↥(ggAutomizer K Bs) × V =>
        ggLin (p := p) ι (q.1 : MulAut ↥Bs) q.2 - q.2)) := by
    rw [← hspan]
    exact hymem
  have hyH := nkF_span_gen_le_image (p := p) (X := K) (Bs := Bs) ι hygen
  obtain ⟨d, hd, hdv⟩ := hyH
  obtain ⟨c, hc, rfl⟩ := hd
  apply hnc
  refine Subgroup.mem_map.mpr ⟨c, hc, ?_⟩
  have h1 : ι (Additive.ofMul c) = ι (Additive.ofMul (⟨y, hy⟩ : ↥Bs)) := by
    rw [hdv]
  have h2 : Additive.ofMul c = Additive.ofMul (⟨y, hy⟩ : ↥Bs) := ι.injective h1
  exact congrArg Subtype.val (by simpa using h2)

theorem ggXDatumA_depframe_K {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hy : y ∈ Bs)
    (hstrong : ∀ b : ↥Bs, (∀ ψ ∈ ggAutomizer K Bs, ψ b = b) → (b : G) ∈ Subgroup.zpowers y)
    {N : ℕ} (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {MK : CoxeterMatrix Λ}
    {CK : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ) (hMK : MK = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCK : GGIntCartan MK CK) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CK i j : ZMod p))
    (hAK : ggAutomizer K Bs = Subgroup.closure (Set.range φ))
    (hdep : ¬ LinearIndependent (ZMod p) h) :
    GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨y, hy⟩)) := by
  classical
  refine ⟨?_, hpN, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hpair (e i) (e j), ggIndep_cartan_of_reindex e hCK hMK i j]
  · intro h0
    have hy1 : (⟨y, hy⟩ : Bs) ≠ 1 := by
      intro h1
      exact nkF_y_ne_one hH (by simpa using congrArg Subtype.val h1)
    apply hy1
    have h1 : Additive.ofMul (⟨y, hy⟩ : Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨y, hy⟩ : Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  · intro i
    exact nkF_alpha_y hp2 hH hy hφ hpair hCK hAK (e i)
  · intro v hv
    exact nkF_fix_K hy hstrong hφ hAK v (fun j => by
      have hj := hv (e.symm j)
      simpa using hj)
  · intro hli
    exact hdep ((linearIndependent_equiv (R := ZMod p) e).mp hli)

end CFSG.StandardType

end
