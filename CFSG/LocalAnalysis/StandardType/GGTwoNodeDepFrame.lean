module

public import CFSG.LocalAnalysis.StandardType.GGTBXPlumb
public import CFSG.LocalAnalysis.StandardType.GGDepAFrame
public import CFSG.LocalAnalysis.StandardType.GGDepACaseI
public import CFSG.LocalAnalysis.StandardType.GGDepACaseII
public import CFSG.LocalAnalysis.StandardType.GGResKnownGroup
public import CFSG.LocalAnalysis.StandardType.GGResSideDatumDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixDefs
public import CFSG.LocalAnalysis.StandardType.GGTBFixNbrDefs
public import CFSG.LocalAnalysis.StandardType.GGRCWeylConnected
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
public import CFSG.LocalAnalysis.StandardType.GGRCCaseIIBasic
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyDichotomy

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nTC_ggIntCartan_three {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 3) :
    C a b = -1 ∧ C b a = -1 := by
  rcases hC.2 a b hab with ⟨h2, -⟩ | ⟨-, h1, h2⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exfalso; omega
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega

private theorem l05nTC_ggIntCartan_two {ι : Type} {M : CoxeterMatrix ι} {C : Matrix ι ι ℤ}
    (hC : GGIntCartan M C) {a b : ι} (hab : a ≠ b) (hm : M a b = 2) :
    C a b = 0 ∧ C b a = 0 := by
  rcases hC.2 a b hab with ⟨-, h1, h2⟩ | ⟨h3, -, -⟩ | ⟨h4, -, -, -⟩ | ⟨h6, -, -, -⟩
  · exact ⟨h1, h2⟩
  · exfalso; omega
  · exfalso; omega
  · exfalso; omega

private theorem l05nTC_coxeterA_entry (m : ℕ) (i j : Fin m) :
    (CoxeterMatrix.A m) i j =
      if i = j then 1 else if (j : ℕ) + 1 = i ∨ (i : ℕ) + 1 = j then 3 else 2 :=
  rfl

private theorem l05nTC_cartanA_entry (m : ℕ) (i j : Fin m) :
    CartanMatrix.A m i j =
      if i = j then 2 else if i.val + 1 = j.val ∨ j.val + 1 = i.val then -1 else 0 :=
  rfl

private theorem l05nTC_cartan_of_reindex {m : ℕ} {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (eA : Fin m ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = (CoxeterMatrix.A m).reindex eA) :
    ∀ i j : Fin m, CL (eA i) (eA j) = CartanMatrix.A m i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1, l05nTC_cartanA_entry]
    simp
  · have hentryM : ML (eA i) (eA j) = (CoxeterMatrix.A m) i j := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
    have hne : eA i ≠ eA j := fun h => hij (eA.injective h)
    by_cases h3 : (i : ℕ) + 1 = j ∨ (j : ℕ) + 1 = i
    · have hM3 : ML (eA i) (eA j) = 3 := by
        rw [hentryM, l05nTC_coxeterA_entry, if_neg hij]
        rw [if_pos (h3.elim (fun h => Or.inr h) (fun h => Or.inl h))]
      have hthree := l05nTC_ggIntCartan_three hCL hne hM3
      rw [hthree.1, l05nTC_cartanA_entry, if_neg hij, if_pos h3]
    · have hM2 : ML (eA i) (eA j) = 2 := by
        rw [hentryM, l05nTC_coxeterA_entry, if_neg hij]
        rw [if_neg (fun h => h3 (h.elim (fun h => Or.inr h) (fun h => Or.inl h)))]
      have htwo := l05nTC_ggIntCartan_two hCL hne hM2
      rw [htwo.1, l05nTC_cartanA_entry, if_neg hij, if_neg h3]

private theorem l05nTC_two_mul_pred_sub {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N) (hN : 2 ≤ N) :
    (2 : ZMod p) * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) = 0 := by
  have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
  have hcast : ((N : ℕ) : ZMod p) = 2 * ((N - 1 : ℕ) : ZMod p) - ((N - 2 : ℕ) : ZMod p) := by
    have h1 : ((N - 1 : ℕ) : ZMod p) = (N : ZMod p) - 1 := by
      rw [Nat.cast_sub (show 1 ≤ N by omega)]; norm_num
    have h2 : ((N - 2 : ℕ) : ZMod p) = (N : ZMod p) - 2 := by
      rw [Nat.cast_sub (show 2 ≤ N by omega)]; norm_num
    rw [h1, h2]; ring
  rw [← hcast, hNcast]

private theorem l05nTC_A_mul_d {p N : ℕ} [Fact p.Prime] (hpN : p ∣ N)
    (j : Fin (N - 1)) :
    ∑ k : Fin (N - 1), (CartanMatrix.A (N - 1) j k : ZMod p) *
      (((k : ℕ) + 1 : ℕ) : ZMod p) = 0 := by
  let d : Fin (N - 1) → ZMod p := fun k => (((k : ℕ) + 1 : ℕ) : ZMod p)
  change ∑ k, (CartanMatrix.A (N - 1) j k : ZMod p) * d k = 0
  rw [cartanA_row d j]
  have hc' : ∀ m : ℕ, (fun m => if hm : m < N - 1 then d ⟨m, hm⟩ else 0) m =
      (if m < N - 1 then (((m : ℕ) + 1 : ℕ) : ZMod p) else 0) := by
    intro m
    by_cases hm : m < N - 1
    · simp [d, hm]
    · simp [hm]
  have hprev : (j : ℕ) - 1 < N - 1 := by omega
  simp only [hc']
  by_cases hlast : (j : ℕ) + 1 < N - 1
  · rw [if_pos j.isLt, if_pos hlast]
    by_cases hj0 : (j : ℕ) = 0
    · rw [if_pos hj0, hj0]; norm_num
    · rw [if_neg hj0, if_pos hprev]
      have hsub : ((↑j - 1 : ℕ) : ZMod p) = (↑j : ZMod p) - 1 := by
        rw [Nat.cast_sub (by omega : 1 ≤ (j : ℕ))]
        norm_num
      simp only [Nat.cast_add, Nat.cast_one]
      rw [hsub]; ring
  · rw [if_pos j.isLt, if_neg hlast]
    have hlast' : (j : ℕ) + 1 = N - 1 := by omega
    by_cases hj0 : (j : ℕ) = 0
    · rw [if_pos hj0, hj0]
      have hN : N = 2 := by omega
      have h2 : (2 : ZMod p) = 0 := by
        have hNcast : ((N : ℕ) : ZMod p) = 0 := (CharP.cast_eq_zero_iff (ZMod p) p N).2 hpN
        simpa [hN] using hNcast
      norm_num
      exact h2
    · rw [if_neg hj0, if_pos hprev]
      have hjval : (j : ℕ) = N - 2 := by omega
      have e1 : (N - 2 : ℕ) + 1 = N - 1 := by omega
      have e2 : (N - 2 : ℕ) - 1 + 1 = N - 2 := by omega
      rw [hjval, e1, e2]
      convert l05nTC_two_mul_pred_sub (p := p) (N := N) hpN (by omega) using 1
      ring

theorem l05nTC_h_mem_L {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) {Λ : Type} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    ∀ i : Λ, ((Additive.toMul (ι.symm (h i)) : ↥Bs) : G) ∈ L := by
  intro i
  have hφi : φ i ∈ ggAutomizer L Bs := by
    rw [hAL]
    exact Subgroup.subset_closure (Set.mem_range_self i)
  obtain ⟨g, hgL, hgN, hgconj⟩ :=
    (mem_ggAutomizer_iff (H := L) (φ := φ i)).mp hφi
  have hBsN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    GGDichotomy.le_normalizer_of_innerDiagOn hH.2.2.1.1
  have hαii : α i (h i) = 2 := by
    rw [hpair i i, hCL.1]
    norm_num
  let w : V := (-((2 : ZMod p)⁻¹)) • h i
  let b : ↥Bs := Additive.toMul (ι.symm w)
  have hbw : ι (Additive.ofMul b) = w := by
    dsimp only [b]
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hαb : α i (ι (Additive.ofMul b)) = -1 := by
    rw [hbw]
    show α i ((-((2 : ZMod p)⁻¹)) • h i) = -1
    rw [map_smul, smul_eq_mul, hαii, neg_mul, inv_mul_cancel₀ (zmod_two_ne_zero hp2)]
  have h1 : ggLin (p := p) ι (φ i) (ι (Additive.ofMul b)) = ι (Additive.ofMul b) + h i := by
    have hh := hφ i (ι (Additive.ofMul b))
    rw [hαb] at hh
    simpa [neg_smul, one_smul, sub_neg_eq_add] using hh
  have h2 : ι (Additive.ofMul (b⁻¹ * φ i b)) =
      -ι (Additive.ofMul b) + ι (Additive.ofMul (φ i b)) := by
    simp only [ofMul_mul, ofMul_inv, map_add, map_neg]
  have hhi : h i = ι (Additive.ofMul (b⁻¹ * φ i b)) := by
    rw [h2, ← ggLin_apply_ofMul (p := p), h1]
    abel
  have hmemL : ((b⁻¹ * φ i b : ↥Bs) : G) ∈ L := by
    have hconj : ((φ i b : ↥Bs) : G) = g * (b : G) * g⁻¹ := hgconj b
    have hbg : (b : G)⁻¹ * g * (b : G) ∈ L := by
      have hbN : (b : G) ∈ Subgroup.normalizer (L : Set G) := hBsN b.2
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) g).mp hgL
    have hEq2 : ((b⁻¹ * φ i b : ↥Bs) : G) = ((b : G)⁻¹ * g * (b : G)) * g⁻¹ := by
      change (b : G)⁻¹ * ((φ i b : ↥Bs) : G) = ((b : G)⁻¹ * g * (b : G)) * g⁻¹
      rw [hconj]
      group
    rw [hEq2]
    exact L.mul_mem hbg (L.inv_mem hgL)
  have hEq : (Additive.toMul (ι.symm (h i)) : ↥Bs) = b⁻¹ * φ i b := by
    rw [hhi]
    simp
  rw [hEq]
  exact hmemL

theorem ggXDatumA_dep (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) (hxL : x ∉ L)
    {N : ℕ} (hN : 5 ≤ N) (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ)
    (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e) (hCL : GGIntCartan ML CL) {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    ¬ LinearIndependent (ZMod p) h := by
  classical
  intro hli
  let M : AddSubgroup V :=
    { carrier := {w | ∃ b : ↥Bs, (b : G) ∈ L ∧ ι (Additive.ofMul b) = w}
      zero_mem' := by
        refine ⟨1, L.one_mem, ?_⟩
        rw [ofMul_one, map_zero]
      add_mem' := by
        rintro w1 w2 ⟨b1, hb1, rfl⟩ ⟨b2, hb2, rfl⟩
        refine ⟨b1 * b2, L.mul_mem hb1 hb2, ?_⟩
        rw [ofMul_mul, map_add]
      neg_mem' := by
        rintro w ⟨b, hb, rfl⟩
        refine ⟨b⁻¹, L.inv_mem hb, ?_⟩
        rw [ofMul_inv, map_neg] }
  have hM : ∀ i : Λ, h i ∈ M := fun i => by
    refine ⟨Additive.toMul (ι.symm (h i)), l05nTC_h_mem_L hp2 hH hCL hφ hpair hAL i, ?_⟩
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  let v : V := ∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • h (e i)
  let d : Fin (N - 1) → ZMod p := fun i => (((i : ℕ) + 1 : ℕ) : ZMod p)
  have hlie : LinearIndependent (ZMod p) (fun i : Fin (N - 1) => h (e i)) :=
    (linearIndependent_equiv e).mpr hli
  have hv_ne : v ≠ 0 := by
    intro hv
    have hd0 : d = 0 := funext fun i =>
      (Fintype.linearIndependent_iff.mp hlie) d (by simpa [v, d] using hv) i
    have h1 : d ⟨0, by omega⟩ = 0 := congrFun hd0 ⟨0, by omega⟩
    have h2 : (1 : ZMod p) = 0 := by simpa [d] using h1
    exact one_ne_zero h2
  have hαv : ∀ k : Λ, α k v = 0 := by
    intro k
    obtain ⟨j, rfl⟩ := e.surjective k
    have hsum : α (e j) v = ∑ i : Fin (N - 1),
        (((i : ℕ) + 1 : ℕ) : ZMod p) * (CartanMatrix.A (N - 1) j i : ZMod p) := by
      simp only [v, map_sum, map_smul, smul_eq_mul, hpair]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [l05nTC_cartan_of_reindex (m := N - 1) e hCL hML j i]
    rw [hsum]
    have hAd := l05nTC_A_mul_d (p := p) (N := N) hpN j
    calc ∑ i : Fin (N - 1),
          (((i : ℕ) + 1 : ℕ) : ZMod p) * (CartanMatrix.A (N - 1) j i : ZMod p)
        = ∑ i : Fin (N - 1),
          (CartanMatrix.A (N - 1) j i : ZMod p) * (((i : ℕ) + 1 : ℕ) : ZMod p) := by
          refine Finset.sum_congr rfl fun i _ => mul_comm _ _
      _ = 0 := hAd
  let s : ↥Bs := Additive.toMul (ι.symm v)
  have hsv : ι (Additive.ofMul s) = v := by
    dsimp only [s]
    rw [ofMul_toMul, AddEquiv.apply_symm_apply]
  have hs_ne : s ≠ 1 := by
    intro hs1
    apply hv_ne
    have h : ι (Additive.ofMul s) = 0 := by rw [hs1, ofMul_one, map_zero]
    rwa [hsv] at h
  have hfixv : ∀ k : Λ, φ k s = s := by
    intro k
    refine (ggLin_fix_iff (p := p) ι (φ k) s).mpr ?_
    rw [hsv, hφ k v, hαv k, zero_smul, sub_zero]
  have hfixall : ∀ ψ ∈ ggAutomizer L Bs, ψ s = s := by
    rw [hAL]
    exact ggFixed_of_mem_closure φ s hfixv
  have hsx : (s : G) ∈ Subgroup.zpowers x :=
    hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 s hfixall
  have hv_mem : v ∈ M := by
    have hv_sum : v = ∑ i : Fin (N - 1), (((i : ℕ) + 1 : ℕ) : ZMod p) • h (e i) := rfl
    rw [hv_sum]
    refine M.sum_mem fun i _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
    exact M.nsmul_mem (hM (e i)) _
  have hsL : (s : G) ∈ L := by
    obtain ⟨b, hbL, hbw⟩ := hv_mem
    have hbs : b = s := by
      apply Additive.ofMul.injective
      exact ι.injective (hbw.trans hsv.symm)
    rw [← hbs]
    exact hbL
  have hxp : x ^ p = 1 := by
    have hBsE : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
    exact hBsE.2 x hx
  have hx1 : x ≠ 1 := fun h => hxL (by rw [h]; exact L.one_mem)
  have horder_x : orderOf x = p := orderOf_eq_prime hxp hx1
  have horder_s : orderOf (s : G) = p := by
    have hdvd : orderOf (s : G) ∣ p := by
      rw [← horder_x]
      exact orderOf_dvd_of_mem_zpowers hsx
    rcases (Fact.out : p.Prime).eq_one_or_self_of_dvd (orderOf (s : G)) hdvd with h1 | h2
    · exact absurd h1 (by intro h; exact hs_ne (Subtype.ext (orderOf_eq_one_iff.mp h)))
    · exact h2
  have hs_le : Subgroup.zpowers (s : G) ≤ Subgroup.zpowers x := Subgroup.zpowers_le.mpr hsx
  have hcard_s : Nat.card (Subgroup.zpowers (s : G)) = p := by rw [Nat.card_zpowers, horder_s]
  have hcard_x : Nat.card (Subgroup.zpowers x) = p := by rw [Nat.card_zpowers, horder_x]
  have heq : Subgroup.zpowers (s : G) = Subgroup.zpowers x :=
    Subgroup.eq_of_le_of_card_ge hs_le (by rw [hcard_s, hcard_x])
  have hx_zp : x ∈ Subgroup.zpowers (s : G) := by rw [heq]; exact Subgroup.mem_zpowers x
  exact hxL ((Subgroup.zpowers_le.mpr hsL) hx_zp)

private theorem l05nTG_x_ne_one {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J : Subgroup G} {x : G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) : x ≠ 1 := by
  intro hx1
  have hp : p.Prime := hH.1.tableB_facts.1
  have hpre := hH.1.2.2.1
  have hDcard : Nat.card D = p ^ 2 := hpre.2.2.1
  have hDea := hpre.2.1
  have hDgen : D = Subgroup.closure ({x, y} : Set G) := hH.2.2.2.2.1.2.1
  have hyD : y ∈ D := by rw [hDgen]; exact Subgroup.subset_closure (by simp)
  have hyp : y ^ p = 1 := hDea.2 y hyD
  have hDle : D ≤ Subgroup.zpowers y := by
    rw [hDgen, hx1, Subgroup.closure_le]
    intro a ha
    have ha' : a = 1 ∨ a = y := by simpa using ha
    rcases ha' with h | h
    · rw [h]; exact Subgroup.one_mem _
    · rw [h]; exact Subgroup.mem_zpowers y
  have hyle : Nat.card (Subgroup.zpowers y) ≤ p := by
    rw [Nat.card_zpowers]
    exact orderOf_le_of_pow_eq_one hp.pos hyp
  have hcon : p ^ 2 ≤ p := by
    calc p ^ 2 = Nat.card D := hDcard.symm
      _ ≤ Nat.card (Subgroup.zpowers y) := Subgroup.card_le_of_le hDle
      _ ≤ p := hyle
  nlinarith [hcon, hp.two_le]

private theorem l05nTG_automizer_fixes_x {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J) (hxBs : x ∈ Bs) :
    ∀ ψ ∈ ggAutomizer L Bs, ψ ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
  have hcent : L ≤ Subgroup.centralizer ({x} : Set G) := hcfg.tableB_facts.2.2.2.1
  have hle : ggAutomizer L Bs ≤ MulAction.stabilizer (MulAut ↥Bs) (⟨x, hxBs⟩ : ↥Bs) := by
    rw [ggAutomizer, Subgroup.closure_le]
    intro ψ hψ
    obtain ⟨g, hgL, -, hg⟩ := hψ
    have hmem : g ∈ Subgroup.centralizer ({x} : Set G) := hcent hgL
    have hcomm : g * x = x * g :=
      ((Subgroup.mem_centralizer_iff.mp hmem) x (by simp)).symm
    change ψ • (⟨x, hxBs⟩ : ↥Bs) = (⟨x, hxBs⟩ : ↥Bs)
    rw [MulAut.smul_def]
    apply Subtype.ext
    have h : ((ψ ⟨x, hxBs⟩ : ↥Bs) : G) = g * x * g⁻¹ := by
      have h1 := hg (⟨x, hxBs⟩ : ↥Bs)
      simpa using h1
    rw [h, hcomm]
    group
  intro ψ hψ
  simpa only [MulAction.mem_stabilizer_iff, MulAut.smul_def] using hle hψ

private theorem l05nTG_alpha_x {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {Λ : Type} {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs}
    {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α i (h j) = (CL i j : ZMod p))
    (hCL : GGIntCartan ML CL)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    ∀ j : Λ, α j (ι (Additive.ofMul ⟨x, hx⟩)) = 0 := by
  intro j
  have hfix := l05nTG_automizer_fixes_x hH.1 hx
  have hmem : φ j ∈ ggAutomizer L Bs := by
    rw [hAL]
    exact Subgroup.subset_closure ⟨j, rfl⟩
  have hfixj : φ j ⟨x, hx⟩ = ⟨x, hx⟩ := hfix (φ j) hmem
  have hlin : ggLin (p := p) ι (φ j) (ι (Additive.ofMul ⟨x, hx⟩)) =
      ι (Additive.ofMul ⟨x, hx⟩) :=
    (ggLin_fix_iff (p := p) ι (φ j) ⟨x, hx⟩).mp hfixj
  have h1 := hφ j (ι (Additive.ofMul ⟨x, hx⟩))
  rw [hlin] at h1
  have h2 : α j (ι (Additive.ofMul ⟨x, hx⟩)) • h j = 0 :=
    sub_eq_self.mp h1.symm
  have h3 : α j (α j (ι (Additive.ofMul ⟨x, hx⟩)) • h j) = 0 := by
    rw [h2, map_zero]
  have hpair : α j (h j) = (2 : ZMod p) := by
    rw [hL j j, hCL.1 j]
    norm_num
  rw [map_smul, smul_eq_mul, hpair] at h3
  exact (mul_eq_zero.mp h3).resolve_right (zmod_two_ne_zero hp2)

private theorem l05nTG_fix (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs)
    {Λ : Type} [Fintype Λ] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {ι : Additive ↥Bs ≃+ V}
    {φ : Λ → MulAut ↥Bs} {h : Λ → V} {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ o w, ggLin (p := p) ι (φ o) w = w - α o w • h o)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    ∀ v : V, (∀ j : Λ, α j v = 0) →
      v ∈ Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) := by
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
  have hfixL : ∀ ψ ∈ ggAutomizer L Bs, ψ bb = bb := by
    rw [hAL]
    exact ggFixed_of_mem_closure φ bb hbb
  have hxmem : (bb : G) ∈ Subgroup.zpowers x :=
    hFix G p B Bs x L D J hH.1 hH.2.1 hH.2.2.1 hH.2.2.2.1 y K hH.2.2.2.2.1
      hH.2.2.2.2.2.1 hH.2.2.2.2.2.2 bb hfixL
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxmem
  have hbk : bb = (⟨x, hx⟩ : Bs) ^ k := Subtype.ext (by simpa using hk.symm)
  have hof : Additive.ofMul bb = k • Additive.ofMul (⟨x, hx⟩ : Bs) := by
    rw [hbk, ofMul_zpow]
  have hv : v = k • ι (Additive.ofMul ⟨x, hx⟩) := by
    have h := congrArg ι hof
    simpa [hbbw, map_zsmul] using h
  rw [hv]
  have hmem : ι (Additive.ofMul ⟨x, hx⟩) ∈
      Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V) :=
    Submodule.subset_span rfl
  have hsm := Submodule.smul_mem (Submodule.span (ZMod p) ({ι (Additive.ofMul ⟨x, hx⟩)} : Set V))
    (k : ZMod p) hmem
  rwa [Int.cast_smul_eq_zsmul] at hsm

theorem ggXDatumA_frame (hFix : GGTBFixInput) {G : Type} [Group G] [Finite G] {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G}
    {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K) (hx : x ∈ Bs) {N : ℕ} (hN : 5 ≤ N)
    (hpN : p ∣ N) {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ} (e : Fin (N - 1) ≃ Λ) (hML : ML = (CoxeterMatrix.A (N - 1)).reindex e)
    (hCL : GGIntCartan ML CL) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ))
    (hdep : ¬ LinearIndependent (ZMod p) h) :
    GGDepAFrame p N (fun i => h (e i)) (fun i => α (e i)) (ι (Additive.ofMul ⟨x, hx⟩)) := by
  classical
  refine ⟨?_, hpN, ?_, ?_, ?_, ?_⟩
  · intro i j
    rw [hpair (e i) (e j), l05nTC_cartan_of_reindex e hCL hML i j]
  · intro h0
    have hx1 : (⟨x, hx⟩ : Bs) ≠ 1 := by
      intro h1
      exact l05nTG_x_ne_one hH (by simpa using congrArg Subtype.val h1)
    apply hx1
    have h1 : Additive.ofMul (⟨x, hx⟩ : Bs) = 0 := ι.injective (by simpa using h0)
    have h2 : (⟨x, hx⟩ : Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  · intro i
    exact l05nTG_alpha_x hp2 hH hx hφ hpair hCL hAL (e i)
  · intro v hv
    exact l05nTG_fix hFix hH hx hφ hAL v (fun j => by
      have hj := hv (e.symm j)
      simpa using hj)
  · intro hli
    exact hdep ((linearIndependent_equiv (R := ZMod p) e).mp hli)

end CFSG.StandardType
