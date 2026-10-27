module

public import CFSG.LocalAnalysis.StandardType.GGQTwoXInLFrameFUni2
public import CFSG.LocalAnalysis.StandardType.GGRoundFourSmallALinearBlock

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LieType.SemisimpleCentralizers.Held CFSG.SectionRank.OddCover
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {R : Type} [Group R]

namespace FrameSign

lemma ne_univ_of_const {n : ℕ} {E D : Subgroup R} (hDE : D ≤ E)
    (hD9 : Nat.card ↥D = 9) {ι : Additive ↥E ≃+ (Fin n → ZMod 3)}
    {I : Finset (Fin n)} {i : Fin n}
    (hconst : ∀ (e : R) (heD : e ∈ D) (j : Fin n), j ∈ I →
      ι (Additive.ofMul ⟨e, hDE heD⟩) j = ι (Additive.ofMul ⟨e, hDE heD⟩) i)
    (hIuniv : I = Finset.univ) : False := by
  have hconst' : ∀ (e : R) (heD : e ∈ D) (j : Fin n),
      ι (Additive.ofMul ⟨e, hDE heD⟩) j = ι (Additive.ofMul ⟨e, hDE heD⟩) i := by
    intro e heD j
    exact hconst e heD j (by rw [hIuniv]; exact Finset.mem_univ j)
  have hinjD : Function.Injective
      (fun e : ↥D => ι (Additive.ofMul ⟨(e : R), hDE e.2⟩) i) := by
    intro e e' h
    have hv : (fun j => ι (Additive.ofMul ⟨(e : R), hDE e.2⟩) j) =
        (fun j => ι (Additive.ofMul ⟨(e' : R), hDE e'.2⟩) j) := by
      funext j
      rw [hconst' (e : R) e.2 j, hconst' (e' : R) e'.2 j]
      exact h
    have hsub : (⟨(e : R), hDE e.2⟩ : ↥E) = ⟨(e' : R), hDE e'.2⟩ := by
      have hi' : Additive.ofMul (⟨(e : R), hDE e.2⟩ : ↥E) =
          Additive.ofMul (⟨(e' : R), hDE e'.2⟩ : ↥E) := ι.injective hv
      exact congrArg (fun x : Additive ↥E => (Additive.toMul x : ↥E)) hi'
    refine Subtype.ext ?_
    exact congrArg (fun x : ↥E => (x : R)) hsub
  have hcard := Nat.card_le_card_of_injective
    (fun e : ↥D => ι (Additive.ofMul ⟨(e : R), hDE e.2⟩) i) hinjD
  have h3 : Nat.card (ZMod 3) = 3 := by rw [Nat.card_eq_fintype_card, ZMod.card]
  omega

lemma compl_le_one {n : ℕ} {M : Type} [Field M] [Finite M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {cU : Mˣ}
    [Finite R]
    {ρ : ↥(heldGU n M τ hτ) →* R} {D : Subgroup R} {I : Finset (Fin n)} {i : Fin n}
    (hi : i ∈ I)
    (hdmem : ∀ v : Fin n → ZMod 3, (∀ j ∈ I, ∀ k ∈ I, v j = v k) →
      ρ (dg hM hτ2 cU v) ∈ D)
    (hρ : Function.Injective ρ)
    (hdg : Function.Injective (fun v : Fin n → ZMod 3 => dg (τ := τ) (hτ := hτ) hM hτ2 cU v))
    (hD9 : Nat.card ↥D = 9) : (Finset.univ \ I).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro j1 hj1 j2 hj2
  by_contra hne
  have hj1I : j1 ∉ I := (Finset.mem_sdiff.mp hj1).2
  have hj2I : j2 ∉ I := (Finset.mem_sdiff.mp hj2).2
  have hi1 : i ≠ j1 := fun h => hj1I (h ▸ hi)
  have hi2 : i ≠ j2 := fun h => hj2I (h ▸ hi)
  let F : ZMod 3 × ZMod 3 × ZMod 3 → ↥D := fun x =>
    ⟨ρ (dg hM hτ2 cU (fun j => if j = j1 then x.2.1 else
        if j = j2 then x.2.2 else if j ∈ I then x.1 else 0)),
      hdmem _ (by
        intro p hp q hq
        have hp1 : p ≠ j1 := fun h => hj1I (h ▸ hp)
        have hp2 : p ≠ j2 := fun h => hj2I (h ▸ hp)
        have hq1 : q ≠ j1 := fun h => hj1I (h ▸ hq)
        have hq2 : q ≠ j2 := fun h => hj2I (h ▸ hq)
        simp only [hp1, hp2, hq1, hq2, if_false, hp, hq, if_true])⟩
  have hFinj : Function.Injective F := by
    intro x y hxy
    have hmat : dg hM hτ2 cU (fun j => if j = j1 then x.2.1 else
        if j = j2 then x.2.2 else if j ∈ I then x.1 else 0) =
        dg hM hτ2 cU (fun j => if j = j1 then y.2.1 else
        if j = j2 then y.2.2 else if j ∈ I then y.1 else 0) :=
      hρ (congrArg Subtype.val hxy)
    have hv := hdg hmat
    have hx1 : x.1 = y.1 := by
      have := congrFun hv i
      simpa [hi1, hi2, hi] using this
    have hx2 : x.2.1 = y.2.1 := by
      have := congrFun hv j1
      simpa using this
    have hx3 : x.2.2 = y.2.2 := by
      have := congrFun hv j2
      simpa [Ne.symm hne] using this
    rcases x with ⟨x1, x2, x3⟩
    rcases y with ⟨y1, y2, y3⟩
    simp only at hx1 hx2 hx3
    simp [hx1, hx2, hx3]
  have h27 : 27 ≤ Nat.card ↥D := by
    have h := Nat.card_le_card_of_injective F hFinj
    simpa [Nat.card_prod, ZMod.card] using h
  omega

lemma map_blockSU_le_centralizer {n : ℕ} {M : Type} [Field M] [Finite M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {cU : Mˣ}
    {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R} {x : R} {L : Subgroup R}
    (hU : GGQTwoUFrame ρ E x L) {hle : unitarySU 2 1 M n ≤ heldGU n M τ hτ}
    {ι : Additive ↥E ≃+ (Fin n → ZMod 3)} {c : M} (hcU : (cU : M) = c)
    (hι : ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
      ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        c ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val)
    {D : Subgroup R} (hDE : D ≤ E) {I : Finset (Fin n)}
    (hcoord : ∀ (e : R) (he : e ∈ E) (_heD : e ∈ D) {j k : Fin n}, j ∈ I → k ∈ I →
      ι (Additive.ofMul ⟨e, he⟩) j = ι (Additive.ofMul ⟨e, he⟩) k)
    (hblock : ∀ (v : Fin n → ZMod 3), (∀ j ∈ I, ∀ k ∈ I, v j = v k) →
      ∀ u : ↥(unitarySU 2 1 M n), u ∈ TableBUE.blockSU I →
      ρ (dg hM hτ2 cU v) * (ρ.comp (Subgroup.inclusion hle)) u =
        (ρ.comp (Subgroup.inclusion hle)) u * ρ (dg hM hτ2 cU v)) :
    Subgroup.map (ρ.comp (Subgroup.inclusion hle)) (TableBUE.blockSU I) ≤
      (ρ.comp (Subgroup.inclusion hle)).range ⊓ Subgroup.centralizer (D : Set R) := by
  refine le_inf (Subgroup.map_le_range _ _) ?_
  intro x hx
  obtain ⟨u, hu, hux⟩ := Subgroup.mem_map.mp hx
  rw [← hux, Subgroup.mem_centralizer_iff]
  intro d hd
  have hdD : d ∈ D := hd
  have hdE : d ∈ E := hDE hdD
  have hvconst : ∀ j ∈ I, ∀ k ∈ I,
      ι (Additive.ofMul ⟨d, hdE⟩) j = ι (Additive.ofMul ⟨d, hdE⟩) k :=
    fun j hj k hk => hcoord d hdE hdD hj hk
  rw [dg_eq_of_mem hM hτ2 hcU hU ι hι hdE]
  exact hblock (ι (Additive.ofMul ⟨d, hdE⟩)) hvconst u hu

lemma isQuasisimple_map_blockSU {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {R : Type} [Group R]
    {ψ : ↥(unitarySU 2 1 M n) →* R}
    (hUF : UnitaryFieldData 2 1 M) (hker : ψ.ker ≤ Subgroup.center ↥(unitarySU 2 1 M n))
    {I : Finset (Fin n)} (hI3 : 3 ≤ I.card) (hSq : (I.card, 2 ^ 1) ≠ (3, 2)) :
    CFSG.Assembly.IsQuasisimple ↥(Subgroup.map ψ (TableBUE.blockSU I)) :=
  SURepair.isQuasisimple_map_of_isQuasisimple hker
    (TableBUE.isQuasisimple_blockSU I hUF (by rw [hM]; norm_num) hI3 hSq)

lemma exists_order_three_block {n : ℕ} {M : Type} [Field M] [Finite M]
    (hM : Nat.card M = 4) {cU : Mˣ} {c : M}
    (hcU : (cU : M) = c) (hcU3 : cU ^ 3 = 1) (hc1 : c ≠ 1)
    {I : Finset (Fin n)} (hI : 5 ≤ I.card) :
    ∃ u : ↥(unitarySU 2 1 M n), u ∈ TableBUE.blockSU I ∧ u ^ 3 = 1 ∧ u ≠ 1 := by
  have hUF : UnitaryFieldData 2 1 M := ⟨Nat.prime_two, le_rfl, by rw [hM]; norm_num⟩
  obtain ⟨j1, hj1I, j2, hj2I, hj12⟩ := Finset.one_lt_card.mp (show 1 < I.card by omega)
  let t : Fin n → Mˣ := Pi.mulSingle j1 cU * Pi.mulSingle j2 (cU ^ 2)
  have ht1 : t j1 = cU := by simp [t, hj12]
  have ht2 : t j2 = cU ^ 2 := by simp [t, Ne.symm hj12]
  have htother : ∀ k, k ≠ j1 → k ≠ j2 → t k = 1 := by
    intro k hk1 hk2
    simp [t, hk1, hk2]
  have ht3 : ∀ k, t k ^ 3 = 1 := by
    intro k
    by_cases hk1 : k = j1
    · rw [hk1, ht1]; exact hcU3
    · by_cases hk2 : k = j2
      · rw [hk2, ht2, ← pow_mul, show 2 * 3 = 3 * 2 from by norm_num, pow_mul, hcU3,
          one_pow]
      · rw [htother k hk1 hk2, one_pow]
  have hprod : ∏ k, t k = 1 := by
    simp only [t, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle']
    rw [show cU * cU ^ 2 = cU ^ 3 from by group, hcU3]
  let u : ↥(unitarySU 2 1 M n) :=
    ⟨diagHom n t, TableBUE.diagHom_mem_unitarySU hUF (by simpa using ht3) hprod⟩
  have huB : u ∈ TableBUE.blockSU I := by
    rw [TableBUE.mem_blockSU]
    intro a b hab
    change (((diagHom n t : GL (Fin n) M) : Matrix (Fin n) (Fin n) M)) a b =
      (1 : Matrix (Fin n) (Fin n) M) a b
    rw [coe_diagHom]
    rcases hab with ha | hb
    · have ha1 : a ≠ j1 := fun h => ha (h ▸ hj1I)
      have ha2 : a ≠ j2 := fun h => ha (h ▸ hj2I)
      by_cases h : a = b
      · subst h
        rw [Matrix.diagonal_apply_eq, htother a ha1 ha2, Matrix.one_apply_eq]
        simp
      · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
    · have hb1 : b ≠ j1 := fun h => hb (h ▸ hj1I)
      have hb2 : b ≠ j2 := fun h => hb (h ▸ hj2I)
      by_cases h : a = b
      · subst h
        rw [Matrix.diagonal_apply_eq, htother a hb1 hb2, Matrix.one_apply_eq]
        simp
      · rw [Matrix.diagonal_apply_ne _ h, Matrix.one_apply_ne h]
  have hu3 : u ^ 3 = 1 := by
    apply Subtype.ext
    show ((u : ↥(unitarySU 2 1 M n)) : GL (Fin n) M) ^ 3 = 1
    show ((diagHom n t : GL (Fin n) M)) ^ 3 = 1
    rw [← map_pow, show t ^ 3 = 1 from funext ht3, map_one]
  have hu1 : u ≠ 1 := by
    intro h
    have hentry : (((u : ↥(unitarySU 2 1 M n)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) j1 j1 = (cU : M) := by
      show ((diagHom n t : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j1 j1 = (cU : M)
      rw [coe_diagHom, Matrix.diagonal_apply_eq, ht1]
    have hone : (((u : ↥(unitarySU 2 1 M n)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) j1 j1 = 1 := by
      rw [h]
      simp
    rw [hentry] at hone
    exact hc1 (by rw [← hcU]; exact hone)
  exact ⟨u, huB, hu3, hu1⟩

private lemma alpha_apply {n : ℕ} {M : Type} [Field M] [Finite M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {cU : Mˣ}
    {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R} {x : R} {L : Subgroup R}
    (hU : GGQTwoUFrame ρ E x L) {ι : Additive ↥E ≃+ (Fin n → ZMod 3)} {c : M}
    (hcU : (cU : M) = c) (hcU3 : cU ^ 3 = 1) (hcU1 : cU ≠ 1)
    (hι : ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
      ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        c ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val)
    {α : MulAut R} {i₀ : Fin n}
    (hα1 : ∀ A A' : ↥(heldGU n M τ hτ),
      (∀ j k, j ≠ k → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
      (∀ j k, j ≠ k → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j k = 0) →
      ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i₀ i₀ =
        τ (((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i₀ i₀) →
      (∀ j, j ≠ i₀ → ((A' : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j =
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j j) →
      α (ρ A) = ρ A')
    {e : R} (he : e ∈ E) :
    α e = ρ (dg hM hτ2 cU (fun j => (if j = i₀ then (-1 : ZMod 3) else 1) *
      ι (Additive.ofMul ⟨e, he⟩) j)) := by
  set v : Fin n → ZMod 3 := ι (Additive.ofMul ⟨e, he⟩) with hv
  set v' : Fin n → ZMod 3 :=
    fun j => (if j = i₀ then (-1 : ZMod 3) else 1) * v j with hv'
  have hsgn : ∀ k : ZMod 3, τ (c ^ k.val) = c ^ (-k).val := by
    intro k
    have := tau_pow (τ := τ) hτ2 hcU3 hcU1 k
    rwa [hcU] at this
  have hii : (((dg hM hτ2 cU v' : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
      Matrix (Fin n) (Fin n) M) i₀ i₀ =
      τ ((((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) i₀ i₀) := by
    rw [dg_apply_eq, dg_apply_eq, hcU]
    rw [show v' i₀ = -(v i₀) from by simp [v']]
    rw [hsgn]
  have hjj : ∀ j, j ≠ i₀ →
      (((dg hM hτ2 cU v' : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) j j =
      (((dg hM hτ2 cU v : ↥(heldGU n M τ hτ)) : GL (Fin n) M) :
        Matrix (Fin n) (Fin n) M) j j := by
    intro j hj
    rw [dg_apply_eq, dg_apply_eq]
    rw [show v' j = v j from by simp [v', hj]]
  have hαe : α e = ρ (dg hM hτ2 cU v') := by
    rw [dg_eq_of_mem hM hτ2 hcU hU ι hι he]
    exact hα1 (dg hM hτ2 cU v) (dg hM hτ2 cU v')
      (fun i j hij => dg_off hM hτ2 cU v hij)
      (fun i j hij => dg_off hM hτ2 cU v' hij) hii hjj
  exact hαe

private lemma alpha_fixes_block {n : ℕ} {M : Type} [Field M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} {ρ : ↥(heldGU n M τ hτ) →* R}
    {hle : unitarySU 2 1 M n ≤ heldGU n M τ hτ}
    {I : Finset (Fin n)} {i₀ : Fin n} {J : Subgroup R} {α : MulAut R}
    (hJeq : J = Subgroup.map (ρ.comp (Subgroup.inclusion hle)) (TableBUE.blockSU I))
    (hImem : ∀ j : Fin n, j ∈ I ↔ j ≠ i₀)
    (hα2 : ∀ A : ↥(heldGU n M τ hτ),
      (∀ j, j ≠ i₀ → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i₀ j = 0 ∧
        ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) j i₀ = 0) →
      ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i₀ i₀ = 1 → α (ρ A) = ρ A) :
    ∀ j ∈ J, α j = j := by
  intro j hj
  rw [hJeq] at hj
  obtain ⟨u, hu, hju⟩ := Subgroup.mem_map.mp hj
  rw [← hju]
  have hmemBlock := TableBUE.mem_blockSU.mp hu
  have hi0not : i₀ ∉ I := fun h => (hImem i₀).mp h rfl
  have hrow : ∀ k, k ≠ i₀ →
      (((⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) :
        GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i₀ k = 0 ∧
      (((⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) :
        GL (Fin n) M) : Matrix (Fin n) (Fin n) M) k i₀ = 0 := by
    intro k hk
    constructor
    · have h := hmemBlock i₀ k (Or.inl hi0not)
      rw [Matrix.one_apply_ne (Ne.symm hk)] at h
      exact h
    · have h := hmemBlock k i₀ (Or.inr hi0not)
      rw [Matrix.one_apply_ne hk] at h
      exact h
  have hdiag : (((⟨u, hle u.2⟩ : ↥(heldGU n M τ hτ)) :
      GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i₀ i₀ = 1 := by
    have h := hmemBlock i₀ i₀ (Or.inl hi0not)
    rwa [Matrix.one_apply_eq] at h
  exact hα2 ⟨u, hle u.2⟩ hrow hdiag

lemma D_description {n : ℕ} {M : Type} [Field M] [Finite M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {cU : Mˣ}
    {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R} {x : R} {L : Subgroup R}
    (hU : GGQTwoUFrame ρ E x L) {ι : Additive ↥E ≃+ (Fin n → ZMod 3)} {c : M}
    (hcU : (cU : M) = c)
    (hι : ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
      ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        c ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val)
    {D : Subgroup R} {I : Finset (Fin n)} {i i₀ : Fin n} (hi : i ∈ I)
    (hImem : ∀ j : Fin n, j ∈ I ↔ j ≠ i₀)
    (hcoord : ∀ (e : R) (he : e ∈ E) (_heD : e ∈ D) {j k : Fin n}, j ∈ I → k ∈ I →
      ι (Additive.ofMul ⟨e, he⟩) j = ι (Additive.ofMul ⟨e, he⟩) k)
    (hdmem : ∀ v : Fin n → ZMod 3, (∀ j ∈ I, ∀ k ∈ I, v j = v k) →
      ρ (dg hM hτ2 cU v) ∈ D) :
    ∀ (e : R) (he : e ∈ E), e ∈ D ↔ ∃ a b : ZMod 3, ι (Additive.ofMul ⟨e, he⟩) =
      fun i => a + if i = i₀ then b else 0 := by
  intro e he
  constructor
  · intro heD
    refine ⟨ι (Additive.ofMul ⟨e, he⟩) i,
      ι (Additive.ofMul ⟨e, he⟩) i₀ - ι (Additive.ofMul ⟨e, he⟩) i, ?_⟩
    funext j
    by_cases hj : j = i₀
    · rw [if_pos hj, hj]
      ring
    · rw [if_neg hj, add_zero]
      exact hcoord e he heD ((hImem j).mpr hj) hi
  · rintro ⟨a, b, hv⟩
    have hee := dg_eq_of_mem hM hτ2 hcU hU ι hι he
    rw [hee]
    refine hdmem _ ?_
    intro j hj k hk
    have hjI : j ≠ i₀ := (hImem j).mp hj
    have hkI : k ≠ i₀ := (hImem k).mp hk
    have h1 : ι (Additive.ofMul ⟨e, he⟩) j = a := by
      rw [hv]
      change a + (if j = i₀ then b else 0) = a
      rw [if_neg hjI, add_zero]
    have h2 : ι (Additive.ofMul ⟨e, he⟩) k = a := by
      rw [hv]
      change a + (if k = i₀ then b else 0) = a
      rw [if_neg hkI, add_zero]
    rw [h1, h2]

lemma exists_alpha_fixes {n : ℕ} {M : Type} [Field M] [Finite M] {τ : M ≃+* M}
    {hτ : ∀ y, τ (τ y) = y} (hM : Nat.card M = 4) (hτ2 : ∀ y, τ y = y ^ 2) {cU : Mˣ} {c : M}
    {ρ : ↥(heldGU n M τ hτ) →* R} {E : Subgroup R} {x : R} {L : Subgroup R}
    (hU : GGQTwoUFrame ρ E x L) {hle : unitarySU 2 1 M n ≤ heldGU n M τ hτ}
    {ι : Additive ↥E ≃+ (Fin n → ZMod 3)} (hcU : (cU : M) = c) (hcU3 : cU ^ 3 = 1)
    (hcU1 : cU ≠ 1)
    (hinj : ∀ a b : ZMod 3, (cU : M) ^ a.val = (cU : M) ^ b.val → a = b)
    (hι : ∀ (A : ↥(heldGU n M τ hτ)) (he : ρ A ∈ E),
      (∀ i j, i ≠ j → ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i j = 0) →
      ∀ i, ((A : GL (Fin n) M) : Matrix (Fin n) (Fin n) M) i i =
        c ^ (ι (Additive.ofMul ⟨ρ A, he⟩) i).val)
    {I : Finset (Fin n)} {i₀ : Fin n} {J : Subgroup R}
    (hJeq : J = Subgroup.map (ρ.comp (Subgroup.inclusion hle)) (TableBUE.blockSU I))
    (hImem : ∀ j : Fin n, j ∈ I ↔ j ≠ i₀) :
    ∃ α : MulAut R, (∀ e ∈ E, α e ∈ E) ∧
      (∀ (e : R) (he : e ∈ E) (hae : α e ∈ E),
        ι (Additive.ofMul ⟨α e, hae⟩) =
          fun i => (if i = i₀ then -1 else 1) * ι (Additive.ofMul ⟨e, he⟩) i) ∧
      ∀ j ∈ J, α j = j := by
  obtain ⟨α, hα1, hα2⟩ := hU.2.2.2.2 i₀
  have hαe : ∀ (e : R) (he : e ∈ E),
      α e = ρ (dg hM hτ2 cU (fun j => (if j = i₀ then (-1 : ZMod 3) else 1) *
        ι (Additive.ofMul ⟨e, he⟩) j)) := by
    intro e he
    exact alpha_apply (hM := hM) (hτ2 := hτ2) (hU := hU) (c := c) hcU hcU3 hcU1 hι hα1 he
  refine ⟨α, ?_, ?_, ?_⟩
  · intro e he
    rw [hαe e he]
    exact dg_mem_E hM hτ2 hU _
  · intro e he hae
    have heq : (⟨α e, hae⟩ : ↥E) =
        ⟨ρ (dg hM hτ2 cU (fun j => (if j = i₀ then (-1 : ZMod 3) else 1) *
          ι (Additive.ofMul ⟨e, he⟩) j)), dg_mem_E hM hτ2 hU _⟩ :=
      Subtype.ext (hαe e he)
    rw [heq]
    exact dg_coord hM hτ2 hcU hinj hU ι hι _
  · exact alpha_fixes_block hJeq hImem hα2

end FrameSign

end CFSG.StandardType

end
