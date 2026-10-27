module

public import CFSG.LocalAnalysis.StandardType.GGDepED4False
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat1
public import CFSG.LocalAnalysis.StandardType.GGDepED4Pat2
public import CFSG.LocalAnalysis.StandardType.GGDepEFrame
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeDepAssembly
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeIndepDefs
public import CFSG.LocalAnalysis.StandardType.GGDepED4PackDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem l05nEU_sup_eq {G : Type} [Group G] {Bs L K : Subgroup G}
    {Λ Λa : Type} {b₁ b₂ : Λ} (φ : Λ ⊕ Λa → MulAut ↥Bs)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range fun a : Λa => φ (Sum.inr a))) :
    ggAutomizer L Bs ⊔ ggAutomizer K Bs = Subgroup.closure (Set.range φ) := by
  rw [hAL, hAK, ← Subgroup.closure_union]
  congr 1
  ext γ
  constructor
  · rintro (⟨i, rfl⟩ | ⟨j, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨Sum.inl i, rfl⟩
    · exact ⟨Sum.inl j.1, rfl⟩
    · exact ⟨Sum.inr a, rfl⟩
  · rintro ⟨o, rfl⟩
    cases o with
    | inl i => exact Or.inl ⟨i, rfl⟩
    | inr a => exact Or.inr (Or.inr ⟨a, rfl⟩)

theorem l05nEU_exists_psi {G : Type} [Group G] {p : ℕ} [Fact p.Prime]
    {Bs : Subgroup G} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (ι : Additive ↥Bs ≃+ V) {Λ Λa : Type} (φ : Λ ⊕ Λa → MulAut ↥Bs) :
    ∀ g ∈ Subgroup.closure (Set.range fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)),
      ∃ ψ ∈ Subgroup.closure (Set.range φ), ggLin (p := p) ι ψ = g := by
  intro g hg
  have himg : Set.range (fun o : Λ ⊕ Λa => ggLin (p := p) ι (φ o)) =
      (ggLin (p := p) ι) '' Set.range φ := by
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      exact ⟨φ o, ⟨o, rfl⟩, rfl⟩
    · rintro ⟨ψ, ⟨o, rfl⟩, rfl⟩
      exact ⟨o, rfl⟩
  rw [himg, ← MonoidHom.map_closure] at hg
  exact Subgroup.mem_map.mp hg

theorem l05nEU_cartan_of_reindex {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ)
    (hCL : GGIntCartan ML CL) (hML : ML = CoxeterMatrix.E₆.reindex e) :
    ∀ i j : Fin 6, CL (e i) (e j) = CartanMatrix.E 6 i j := by
  intro i j
  by_cases hij : i = j
  · subst hij
    rw [hCL.1]
    fin_cases i <;> decide
  · have heij : e i ≠ e j := fun h => hij (e.injective h)
    have h₂ : GGIntCartan ML (Matrix.reindex e e (CartanMatrix.E 6)) := by
      rw [hML]
      exact GGIntCartan.reindex e ggIntCartan_E₆
    have hMle : ML.M (e i) (e j) ≤ 3 := by
      rw [hML, CoxeterMatrix.reindex_apply, Equiv.symm_apply_apply, Equiv.symm_apply_apply]
      fin_cases i <;> fin_cases j <;> decide
    have h1 := (hCL.pair h₂ heij).2 hMle
    rw [h1.1]
    simp only [Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply]

theorem l05nEU_kernel_row :
    ∀ j : Fin 6, (∑ i : Fin 6, (((![1, 0, 2, 0, 1, 2] : Fin 6 → ℕ) i : ℕ) : ℤ) *
      CartanMatrix.E 6 j i) = 3 * (if j = 0 then 0 else if j = 2 then 1 else if j = 3 then -1
        else if j = 5 then 1 else 0) := by
  decide +kernel

theorem l05nEU_dep {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    (hFix : GGTBFixInput) (hp2 : p ≠ 2) (hp3 : p = 3) {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hx : x ∈ Bs) (hxL : x ∉ L) {Λ : Type} [Fintype Λ] [DecidableEq Λ]
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ} (e : Fin 6 ≃ Λ) (hCL : GGIntCartan ML CL)
    (hML : ML = CoxeterMatrix.E₆.reindex e) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Λ → MulAut ↥Bs} {h : Λ → V}
    {α : Λ → Module.Dual (ZMod p) V}
    (hφ : ∀ i w, ggLin (p := p) ι (φ i) w = w - α i w • h i)
    (hpair : ∀ i j, α i (h j) = (CL i j : ZMod p))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range φ)) :
    ¬ LinearIndependent (ZMod p) h := by
  classical
  intro hli
  have hcart := l05nEU_cartan_of_reindex e hCL hML
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
  let c : Fin 6 → ℕ := ![1, 0, 2, 0, 1, 2]
  let d : Fin 6 → ZMod p := fun i => ((c i : ℕ) : ZMod p)
  let v : V := ∑ i : Fin 6, d i • h (e i)
  have hlie : LinearIndependent (ZMod p) (fun i : Fin 6 => h (e i)) :=
    (linearIndependent_equiv e).mpr hli
  have hv_ne : v ≠ 0 := by
    intro hv
    have hd0 : d = 0 := funext fun i =>
      (Fintype.linearIndependent_iff.mp hlie) d (by simpa [v] using hv) i
    have h1 : d 0 = 0 := congrFun hd0 0
    have h2 : (1 : ZMod p) = 0 := by simpa [d, c] using h1
    exact one_ne_zero h2
  have hαv : ∀ k : Λ, α k v = 0 := by
    intro k
    obtain ⟨j, rfl⟩ := e.surjective k
    have hsum : α (e j) v =
        ∑ i : Fin 6, d i * ((CartanMatrix.E 6 j i : ℤ) : ZMod p) := by
      change α (e j) (∑ i : Fin 6, d i • h (e i)) = _
      rw [map_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_smul, smul_eq_mul, hpair (e j) (e i), hcart j i]
    rw [hsum]
    have hcast : ∑ i : Fin 6, d i * ((CartanMatrix.E 6 j i : ℤ) : ZMod p) =
        ((∑ i : Fin 6, ((c i : ℕ) : ℤ) * CartanMatrix.E 6 j i : ℤ) : ZMod p) := by
      push_cast
      simp [d]
    rw [hcast, l05nEU_kernel_row j]
    have h3p : (3 : ZMod p) = 0 := by
      have h := CharP.cast_eq_zero (ZMod p) p
      have h' : (p : ZMod p) = (3 : ZMod p) := congrArg (fun n : ℕ => (n : ZMod p)) hp3
      rw [h'] at h
      exact h
    push_cast
    rw [h3p, zero_mul]
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
    have hv_sum : v = ∑ i : Fin 6, d i • h (e i) := rfl
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
  have hx_zp : x ∈ Subgroup.zpowers (s : G) := by
    rw [heq]
    exact Subgroup.mem_zpowers x
  exact hxL ((Subgroup.zpowers_le.mpr hsL) hx_zp)

theorem ggDepED4UpCfg_of_aligned (hFix : GGTBFixInput) (hFixK : GGTBFixNbrInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hxL : x ∉ L) {k : ℕ} (hk : k = 1 ∨ k = 2) (hp3 : p = 3) (hCard : Nat.card ↥Bs = 3 ^ 7)
    (hA : GGDepED4Aligned p k Bs L J K) : GGDepED4UpCfg p k Bs L J K := by
  classical
  obtain ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, ML, CL, MK, CK, V, hVadd, hVmod,
    ι, φ, h, α, e, hb1, hb2, hcardΛa, hML, hMLweyl, hCLcartan, hMKweyl, hCKcartan,
    hk2, hform, hrefl, hpairL, hpairK, hAL, hAK, hAJ⟩ := hA
  letI : Fintype Λ := hΛf
  letI : DecidableEq Λ := hΛd
  letI : AddCommGroup V := hVadd
  letI : Module (ZMod p) V := hVmod
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  have hp2 : p ≠ 2 := by
    have hβ : p ∈ LargeEvenBeta 4 G := hH.1.1.2.2.2.2.2.1
    exact hβ.2.1
  have hx : x ∈ Bs := hH.1.tableB_facts.2.2.1
  let xV : V := ι (Additive.ofMul (⟨x, hx⟩ : ↥Bs))
  let ΦK : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa → MulAut ↥Bs := fun o => φ (o.map Subtype.val id)
  have hAKrange : Set.range ΦK =
      Set.range (fun j : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} => φ (Sum.inl j.1)) ∪
        Set.range (fun a : Λa => φ (Sum.inr a)) := by
    ext z
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | inl j => exact Or.inl ⟨j, rfl⟩
      | inr a => exact Or.inr ⟨a, rfl⟩
    · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
      · exact ⟨Sum.inl j, rfl⟩
      · exact ⟨Sum.inr a, rfl⟩
  have hAK' : ggAutomizer K Bs = Subgroup.closure (Set.range ΦK) := by
    rw [hAK, ← hAKrange]
  have hcart := l05nEU_cartan_of_reindex e hCLcartan hML
  have hdep : ¬ LinearIndependent (ZMod p) (fun i : Λ => h (Sum.inl i)) :=
    l05nEU_dep hFix hp2 hp3 hH hx hxL e hCLcartan hML
      (φ := fun i : Λ => φ (Sum.inl i)) (h := fun i : Λ => h (Sum.inl i))
      (α := fun i : Λ => α (Sum.inl i)) (hφ := fun i w => hform (Sum.inl i) w)
      (hpair := fun i j => hpairL i j) (hAL := hAL)
  have hx1 : (⟨x, hx⟩ : ↥Bs) ≠ 1 := by
    intro h1
    exact l05nDD1_x_ne_one hH (by simpa using congrArg Subtype.val h1)
  have hxVne : xV ≠ 0 := by
    intro h0
    apply hx1
    have h1 : Additive.ofMul (⟨x, hx⟩ : ↥Bs) = 0 := ι.injective (by simpa [xV] using h0)
    have h2 : (⟨x, hx⟩ : ↥Bs) = 1 := by
      have := congrArg Additive.toMul h1
      simpa using this
    exact h2
  let φ₀ : Option Λ → MulAut ↥Bs := fun o => φ (Sum.inl (o.getD b₁))
  let h₀ : Option Λ → V := fun o => h (Sum.inl (o.getD b₁))
  let α₀ : Option Λ → Module.Dual (ZMod p) V := fun o => α (Sum.inl (o.getD b₁))
  have hform₀ : ∀ o w, ggLin (p := p) ι (φ₀ o) w = w - α₀ o w • h₀ o :=
    fun o w => hform (Sum.inl (o.getD b₁)) w
  have hpair₀ : ∀ i j : Λ, α₀ (some i) (h₀ (some j)) = (CL i j : ZMod p) := fun i j => hpairL i j
  have hAL₀ : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ₀ (some i)) := by
    simpa [φ₀] using hAL
  have hαx : ∀ i : Fin 6, α (Sum.inl (e i)) xV = 0 := by
    intro i
    have h := l05nDD1_alpha_x (p := p) hp2 hH hx hform₀ hpair₀ hCLcartan hAL₀ (e i)
    simpa [α₀, xV] using h
  have hframe : GGDepEFrame p (fun i => h (Sum.inl (e i))) (fun i => α (Sum.inl (e i))) xV :=
    { p3 := hp3
      pair := fun i j => by
        rw [hpairL (e i) (e j), hcart i j]
      x_ne := hxVne
      x_ker := hαx
      fix := fun v hv =>
        l05nDD1_fix hFix hH hx hform₀ hAL₀ v (fun j => by
          have hj := hv (e.symm j)
          simpa [α₀] using hj)
      dep := fun hli => hdep ((linearIndependent_equiv (R := ZMod p) e).mp hli) }
  have hxker : ∀ i : Λ, α (Sum.inl i) xV = 0 := by
    intro i
    have h := hframe.x_ker (e.symm i)
    simpa using h
  have hfinrank : Module.finrank (ZMod p) V = 7 := by
    haveI : Module.Finite (ZMod p) V := Module.Finite.of_finite
    have hVcard : Nat.card V = p ^ Module.finrank (ZMod p) V := by
      have h := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
      rwa [Nat.card_zmod] at h
    have hcardV : Nat.card V = Nat.card ↥Bs := by
      rw [Nat.card_congr (Additive.ofMul (α := ↥Bs))]
      exact (Nat.card_congr ι.toEquiv).symm
    have heq : p ^ Module.finrank (ZMod p) V = 3 ^ 7 := by
      rw [← hVcard, hcardV, hCard]
    have heq3 : 3 ^ Module.finrank (ZMod p) V = 3 ^ 7 := by
      simpa [hp3] using heq
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) heq3
  refine ⟨Λ, hΛf, hΛd, b₁, b₂, Λa, hΛaf, hΛad, MK, CK, V, hVadd, hVmod, ι, e, φ, h, α,
    xV, ?_⟩
  refine ⟨⟨hb1, hb2, hcardΛa, hMKweyl, hCKcartan, hk2, hform, hframe, hpairK, ?_, ?_, ?_,
    hAJ⟩, hfinrank⟩
  · intro g hg
    obtain ⟨ψ, hψ, hψg⟩ := l05nEU_exists_psi (p := p) ι φ g hg
    rw [← hψg]
    exact ggTT_nt_sup hH ι (by rw [l05nEU_sup_eq φ hAL hAK]; exact hψ)
  · by_contra hno
    push Not at hno
    have hfixgen : ∀ o : {j : Λ // j ≠ b₁ ∧ j ≠ b₂} ⊕ Λa, ΦK o ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro o
      apply (ggLin_fix_iff (p := p) ι (ΦK o) (⟨x, hx⟩ : ↥Bs)).mpr
      cases o with
      | inl j =>
          show ggLin (p := p) ι (φ (Sum.inl j.1)) xV = xV
          rw [hform (Sum.inl j.1) xV, hxker j.1, zero_smul, sub_zero]
      | inr a =>
          show ggLin (p := p) ι (φ (Sum.inr a)) xV = xV
          rw [hform (Sum.inr a) xV, hno a, zero_smul, sub_zero]
    have hfix : ∀ ψ ∈ ggAutomizer K Bs, ψ ⟨x, hx⟩ = ⟨x, hx⟩ := by
      intro ψ hψ
      rw [hAK'] at hψ
      exact ggFixed_of_mem_closure ΦK (⟨x, hx⟩ : ↥Bs) hfixgen ψ hψ
    exact ggTT_not_fixed hFixK hH hx hfix
  · exact l05nEU_sup_eq φ hAL hAK

end CFSG.StandardType

end
