module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Blocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD3Aut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise IsMulCommutative

variable {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)} {r : ℕ}
  {Δ : Fin (r + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (r + 1))}

private theorem s16e_d3_comm_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s16e_d3_pow_eq_one_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) (x : X) : x ^ p = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp

private theorem s16e_d3_card_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card X = Nat.card (Multiplicative (Fin n → ZMod p)) := Nat.card_congr e.toEquiv
  rw [h1, show Nat.card (Multiplicative (Fin n → ZMod p)) = Nat.card (Fin n → ZMod p) from rfl,
    Nat.card_fun]
  simp [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]

private theorem s16e_d3_isElemAbelian {X : Type*} [Group X] {p n : ℕ} {E : Subgroup X}
    (hE : IsElemAbelianOfRank p n ↥E) : IsElemAbelian p E := by
  obtain ⟨e⟩ := hE
  refine ⟨IsMulCommutative.of_comm fun a b => ?_, fun a ha => ?_⟩
  · have h1 : e a * e b = e b * e a := mul_comm _ _
    rw [← map_mul, ← map_mul] at h1
    exact e.injective h1
  · have h1 : e (⟨a, ha⟩ ^ p) = 1 := by
      rw [map_pow]
      apply Multiplicative.toAdd.injective
      rw [toAdd_pow, toAdd_one]
      funext i
      simp
    have h2 := e.injective (h1.trans (map_one e).symm)
    exact congrArg Subtype.val h2

private theorem s16e_d3_pow_val_add {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) {x : X}
    (hx : x ^ p = 1) (a b : ZMod p) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmod : (a + b).val ≡ a.val + b.val [MOD p] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx
  calc x ^ (a + b).val = x ^ (a.val + b.val) := pow_eq_pow_iff_modEq.mpr (hmod.of_dvd hdvd)
    _ = x ^ a.val * x ^ b.val := pow_add x a.val b.val

private theorem s16e_d3_dParam_seven : dParam 7 = 3 := by
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  unfold dParam
  exact orderOf_eq_prime (by decide) (by decide)

private lemma s16e_d3_stab_of_map_eq {U : Subgroup W} {φ : MulAut W}
    (h : U.map φ.toMonoidHom = U) : φ ∈ stabSub U := by
  intro u
  constructor
  · intro hu
    have hu' : φ u ∈ U.map φ.toMonoidHom := by rw [h]; exact hu
    obtain ⟨w, hw, hwu⟩ := Subgroup.mem_map.1 hu'
    have : w = u := φ.injective hwu
    rw [← this]
    exact hw
  · intro hu
    have hu' : φ u ∈ U.map φ.toMonoidHom := Subgroup.mem_map.2 ⟨u, hu, rfl⟩
    rw [h] at hu'
    exact hu'

private lemma s16e_d3_map_eq_of_mem_stab {U : Subgroup W} {φ : MulAut W}
    (h : φ ∈ stabSub U) : U.map φ.toMonoidHom = U := by
  apply le_antisymm
  · rintro _ ⟨u, hu, rfl⟩
    exact (mem_stabSub.mp h u).2 hu
  · intro u hu
    refine Subgroup.mem_map.2 ⟨φ.symm u, ?_, by simp⟩
    exact (mem_stabSub.mp h (φ.symm u)).mp (by simpa using hu)

private lemma s16e_d3_conj_mem_of_map_conj_eq {L : Subgroup (MulAut W)} {n : MulAut W}
    (h : L.map (MulAut.conj n).toMonoidHom = L) {l : MulAut W} (hl : l ∈ L) :
    n * l * n⁻¹ ∈ L := by
  have hm : (MulAut.conj n).toMonoidHom l ∈ L.map (MulAut.conj n).toMonoidHom :=
    Subgroup.mem_map_of_mem _ hl
  rw [h] at hm
  simpa [MulAut.conj_apply] using hm

private def s16e_d3_supp (Δ : Fin (r + 1) → Subgroup W) (l : MulAut W) :
    Set (Fin (r + 1)) :=
  {i | ∃ x ∈ Δ i, l x ≠ x}

private theorem s16e_d3_notMem_supp_iff {Δ : Fin (r + 1) → Subgroup W} {l : MulAut W}
    {i : Fin (r + 1)} : i ∉ s16e_d3_supp Δ l ↔ l ∈ centSub (Δ i) := by
  rw [mem_centSub]
  simp [s16e_d3_supp]

private theorem s16e_d3_cent_of_notMem_supp {Δ : Fin (r + 1) → Subgroup W}
    {l : MulAut W} {i : Fin (r + 1)} (h : i ∉ s16e_d3_supp Δ l) : l ∈ centSub (Δ i) :=
  s16e_d3_notMem_supp_iff.mp h

private theorem s16e_d3_supp_conj {A : Subgroup (MulAut W)}
    {Δ : Fin (r + 1) → Subgroup W}
    {σ : ↥A →* Equiv.Perm (Fin (r + 1))}
    (hσact : ∀ (g : ↥A) (i : Fin (r + 1)),
      (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i))
    (g : ↥A) (l : MulAut W) :
    s16e_d3_supp Δ ((g : MulAut W) * l * (g : MulAut W)⁻¹) = σ g '' s16e_d3_supp Δ l := by
  ext i
  constructor
  · rintro ⟨x, hx, hne⟩
    have hgx : ((g⁻¹ : ↥A) : MulAut W) x ∈ Δ (σ g⁻¹ i) := by
      rw [← hσact g⁻¹ i]
      exact Subgroup.mem_map_of_mem _ hx
    have hly : l (((g⁻¹ : ↥A) : MulAut W) x) ≠ ((g⁻¹ : ↥A) : MulAut W) x := by
      intro h
      apply hne
      calc ((g : MulAut W) * l * (g : MulAut W)⁻¹) x
          = (g : MulAut W) (l (((g⁻¹ : ↥A) : MulAut W) x)) := rfl
        _ = (g : MulAut W) (((g⁻¹ : ↥A) : MulAut W) x) := by rw [h]
        _ = x := by simp
    refine ⟨σ g⁻¹ i, ⟨_, hgx, hly⟩, ?_⟩
    simp
  · rintro ⟨j, ⟨x, hx, hne⟩, rfl⟩
    refine ⟨(g : MulAut W) x, ?_, ?_⟩
    · rw [← hσact g j]
      exact Subgroup.mem_map_of_mem _ hx
    · intro h
      apply hne
      apply (g : MulAut W).injective
      simpa using h

private theorem s16e_d3_eq_one_of_supp_empty {Δ : Fin (r + 1) → Subgroup W}
    (hsup : (⨆ i, Δ i) = ⊤) {l : MulAut W} (h : s16e_d3_supp Δ l = ∅) : l = 1 := by
  apply MulEquiv.ext
  intro x
  show l x = x
  let U : Subgroup W :=
    { carrier := {y | l y = y}
      one_mem' := map_one l
      mul_mem' := fun {a b} ha hb => by
        show l (a * b) = a * b
        rw [map_mul, ha, hb]
      inv_mem' := fun {a} ha => by
        show l a⁻¹ = a⁻¹
        rw [map_inv, ha] }
  have hU : ∀ i, Δ i ≤ U := fun i y hy => by
    show l y = y
    by_contra hne
    exact (Set.eq_empty_iff_forall_notMem.mp h) i ⟨y, hy, hne⟩
  exact (iSup_le hU) (by rw [hsup]; exact Subgroup.mem_top x)

private theorem s16e_d3_dvd_of_pow_mem_centSub [Finite W] {L : Subgroup (MulAut W)} {p r : ℕ}
    (hE : IsElemAbelianOfRank p r ↥L) (hp : p.Prime) {l : MulAut W} (hl : l ∈ L) {e : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {i : Fin (r + 1)}
    (hi : i ∈ s16e_d3_supp Δ l) (he : l ^ e ∈ centSub (Δ i)) : p ∣ e := by
  have hl1 : l ≠ 1 := by
    rintro rfl
    obtain ⟨x, -, hne⟩ := hi
    exact hne rfl
  have hpow : l ^ p = 1 := by
    have h := s16e_d3_pow_eq_one_of_elem hE (⟨l, hl⟩ : ↥L)
    simpa using congrArg Subtype.val h
  have horder : orderOf l = p := by
    have hdvd : orderOf l ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hpow
    rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hdvd with h1 | hp'
    · exact absurd (orderOf_eq_one_iff.mp h1) hl1
    · exact hp'
  have hKdvd : Nat.card ↥(Subgroup.zpowers l ⊓ centSub (Δ i)) ∣
      Nat.card ↥(Subgroup.zpowers l) :=
    Subgroup.card_dvd_of_le inf_le_left
  rw [Nat.card_zpowers, horder] at hKdvd
  have hle : Subgroup.zpowers l ⊓ centSub (Δ i) ≤ Subgroup.zpowers l := inf_le_left
  rcases Nat.Prime.eq_one_or_self_of_dvd hp _ hKdvd with h1 | hp'
  · have hKbot : Subgroup.zpowers l ⊓ centSub (Δ i) = ⊥ := Subgroup.card_eq_one.mp h1
    have hmem : l ^ e ∈ Subgroup.zpowers l ⊓ centSub (Δ i) :=
      ⟨Subgroup.npow_mem_zpowers l e, he⟩
    rw [hKbot] at hmem
    rw [← horder]
    exact orderOf_dvd_iff_pow_eq_one.mpr (Subgroup.mem_bot.mp hmem)
  · exfalso
    have heq : Subgroup.zpowers l ⊓ centSub (Δ i) = Subgroup.zpowers l :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hp', Nat.card_zpowers, horder])
    have hlK : l ∈ Subgroup.zpowers l ⊓ centSub (Δ i) := heq.ge (Subgroup.mem_zpowers l)
    exact (s16e_d3_notMem_supp_iff.mpr hlK.2) hi

private theorem s16e_d3_triangular_card [Finite W] {L : Subgroup (MulAut W)} {p r : ℕ}
    (hp : p.Prime) (hE : IsElemAbelianOfRank p r ↥L) {s : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {v : Fin s → MulAut W} {i : Fin s → Fin (r + 1)}
    (hv : ∀ k, v k ∈ L)
    (hmem : ∀ k, i k ∈ s16e_d3_supp Δ (v k))
    (htri : ∀ k j, k < j → i k ∉ s16e_d3_supp Δ (v j)) :
    p ^ s ≤ Nat.card ↥(Subgroup.closure (Set.range v)) := by
  have hclos_le : Subgroup.closure (Set.range v) ≤ L :=
    (Subgroup.closure_le L).mpr (by rintro _ ⟨k, rfl⟩; exact hv k)
  let x : Fin s → ↥(Subgroup.closure (Set.range v)) := fun k =>
    ⟨v k, Subgroup.subset_closure ⟨k, rfl⟩⟩
  haveI hcomm : IsMulCommutative ↥(Subgroup.closure (Set.range v)) :=
    IsMulCommutative.of_comm fun a b => by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact congrArg Subtype.val (s16e_d3_comm_of_elem hE
        (⟨(a : MulAut W), hclos_le a.2⟩ : ↥L) (⟨(b : MulAut W), hclos_le b.2⟩ : ↥L))
  have hxpow : ∀ k, (x k) ^ p = 1 := fun k => by
    apply Subtype.ext
    show (v k) ^ p = 1
    have h := s16e_d3_pow_eq_one_of_elem hE (⟨v k, hv k⟩ : ↥L)
    simpa using congrArg Subtype.val h
  let φ : Multiplicative (Fin s → ZMod p) →* ↥(Subgroup.closure (Set.range v)) :=
    { toFun := fun e => ∏ k, x k ^ (Multiplicative.toAdd e k).val
      map_one' := by simp
      map_mul' := by
        intro e f
        show (∏ k, x k ^ (Multiplicative.toAdd (e * f) k).val) =
          (∏ k, x k ^ (Multiplicative.toAdd e k).val) *
            (∏ k, x k ^ (Multiplicative.toAdd f k).val)
        rw [← Finset.prod_mul_distrib]
        apply Finset.prod_congr rfl
        intro k _
        have hk : Multiplicative.toAdd (e * f) k =
            Multiplicative.toAdd e k + Multiplicative.toAdd f k := rfl
        rw [hk]
        exact s16e_d3_pow_val_add hp (hxpow k) _ _ }
  have hker : ∀ e : Multiplicative (Fin s → ZMod p), φ e = 1 → e = 1 := by
    intro e he
    by_contra hne
    have hd : Multiplicative.toAdd e ≠ 0 := by
      intro h0
      exact hne (Multiplicative.toAdd.injective (by rw [h0, toAdd_one]))
    let d : Fin s → ZMod p := Multiplicative.toAdd e
    have hdne : d ≠ 0 := hd
    have hex : ∃ k, d k ≠ 0 := by
      by_contra h
      apply hdne
      funext k
      by_contra hk
      exact h ⟨k, hk⟩
    obtain ⟨k0, hk0⟩ := hex
    let S : Finset (Fin s) := Finset.univ.filter (fun k => d k ≠ 0)
    have hSne : S.Nonempty := ⟨k0, Finset.mem_filter.mpr ⟨Finset.mem_univ k0, hk0⟩⟩
    let k : Fin s := S.min' hSne
    have hkmem : d k ≠ 0 := (Finset.mem_filter.mp (Finset.min'_mem S hSne)).2
    have hklt : ∀ j, j < k → d j = 0 := by
      intro j hj
      by_contra hje
      have hjmem : j ∈ S := Finset.mem_filter.mpr ⟨Finset.mem_univ j, hje⟩
      exact absurd (Finset.min'_le S j hjmem) (not_le.mpr hj)
    let A : ↥(Subgroup.closure (Set.range v)) :=
      ∏ j ∈ (Finset.univ : Finset (Fin s)).erase k, x j ^ (d j).val
    have hA_cent : (A : MulAut W) ∈ centSub (Δ (i k)) := by
      have hstep : ∀ j ∈ (Finset.univ : Finset (Fin s)).erase k,
          (((x j ^ (d j).val : ↥(Subgroup.closure (Set.range v))) : MulAut W)) ∈
            centSub (Δ (i k)) := by
        intro j hj
        rw [Finset.mem_erase] at hj
        obtain ⟨hjk, -⟩ := hj
        have hcoe : ((x j ^ (d j).val : ↥(Subgroup.closure (Set.range v))) : MulAut W) =
            (v j) ^ (d j).val := by simp [x]
        rw [hcoe]
        rcases lt_or_gt_of_ne hjk with hlt | hgt
        · rw [hklt j hlt]
          simp [ZMod.val_zero]
        · exact Subgroup.pow_mem _ (s16e_d3_cent_of_notMem_supp (htri k j hgt)) _
      have hprod := Finset.prod_induction (s := (Finset.univ : Finset (Fin s)).erase k)
        (fun j => x j ^ (d j).val)
        (fun y : ↥(Subgroup.closure (Set.range v)) => ((y : MulAut W)) ∈ centSub (Δ (i k)))
        (fun a b ha hb => by
          show (((a * b : ↥(Subgroup.closure (Set.range v))) : MulAut W)) ∈ centSub (Δ (i k))
          rw [Subgroup.coe_mul]
          exact Subgroup.mul_mem _ ha hb)
        (by simp) hstep
      simpa [A] using hprod
    have he' : (∏ j, x j ^ (d j).val) = 1 := he
    have hAB : A * x k ^ (d k).val = 1 := by
      have hprod := Finset.prod_erase_mul (s := (Finset.univ : Finset (Fin s)))
        (f := fun j => x j ^ (d j).val) (a := k) (Finset.mem_univ k)
      show A * x k ^ (d k).val = 1
      rw [hprod]
      exact he'
    have hfk : x k ^ (d k).val = A⁻¹ := eq_inv_of_mul_eq_one_right hAB
    have hcent : (v k) ^ (d k).val ∈ centSub (Δ (i k)) := by
      have h1 : (((x k ^ (d k).val : ↥(Subgroup.closure (Set.range v))) : MulAut W)) ∈
          centSub (Δ (i k)) := by
        rw [hfk, Subgroup.coe_inv]
        exact Subgroup.inv_mem _ hA_cent
      have hcoe : ((x k ^ (d k).val : ↥(Subgroup.closure (Set.range v))) : MulAut W) =
          (v k) ^ (d k).val := by simp [x]
      rwa [hcoe] at h1
    have hdvd := s16e_d3_dvd_of_pow_mem_centSub hE hp (hv k) (hmem k) hcent
    haveI : NeZero p := ⟨hp.ne_zero⟩
    have hval0 : (d k).val = 0 := Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt (d k))
    exact hkmem ((ZMod.val_eq_zero (d k)).mp hval0)
  have hinj : Function.Injective φ := by
    intro e f h
    have h1 : φ (f⁻¹ * e) = 1 := by
      rw [map_mul, h, ← map_mul, inv_mul_cancel, map_one]
    have h2 := hker (f⁻¹ * e) h1
    have h3 : f * (f⁻¹ * e) = f * 1 := by rw [h2]
    rwa [mul_inv_cancel_left, mul_one] at h3
  have hle := Nat.card_le_card_of_injective φ hinj
  have hcard : Nat.card (Multiplicative (Fin s → ZMod p)) = p ^ s := by
    rw [show Nat.card (Multiplicative (Fin s → ZMod p)) = Nat.card (Fin s → ZMod p) from rfl,
      Nat.card_fun]
    simp [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]
  simpa [hcard] using hle

private theorem s16e_d3_supp_not_singleton [Finite W] {A L : Subgroup (MulAut W)} {p r : ℕ}
    (hp : p.Prime) (hE : IsElemAbelianOfRank p r ↥L)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    {Δ : Fin (r + 1) → Subgroup W}
    {σ : ↥A →* Equiv.Perm (Fin (r + 1))}
    (hσsurj : Function.Surjective σ)
    (hσact : ∀ (g : ↥A) (i : Fin (r + 1)),
      (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i))
    {y : MulAut W} (hy : y ∈ L) {c : Fin (r + 1)} (hS : s16e_d3_supp Δ y = {c}) : False := by
  choose g hg using fun k : Fin (r + 1) => hσsurj (Equiv.swap c k)
  let z : Fin (r + 1) → MulAut W := fun k => (g k : MulAut W) * y * (g k : MulAut W)⁻¹
  have hzmem : ∀ k, z k ∈ L := by
    intro k
    have hgA : (g k : MulAut W) ∈ A := (g k).2
    have hconj : (MulAut.conj (g k : MulAut W)) y ∈ L := by
      rw [← hLn (g k : MulAut W) hgA]
      exact Subgroup.mem_map_of_mem _ hy
    simpa [z, MulAut.conj_apply] using hconj
  have hzsupp : ∀ k, s16e_d3_supp Δ (z k) = {k} := by
    intro k
    have h := s16e_d3_supp_conj (A := A) hσact (g k) y
    rw [hS, hg k] at h
    rw [show z k = (g k : MulAut W) * y * (g k : MulAut W)⁻¹ from rfl, h]
    rw [Set.image_singleton, Equiv.swap_apply_left]
  have htri : ∀ k j, k < j → k ∉ s16e_d3_supp Δ (z j) := by
    intro k j hkj
    rw [hzsupp j]
    simp [ne_of_lt hkj]
  have hcard := s16e_d3_triangular_card (L := L) (s := r + 1) (i := fun k => k) hp hE hzmem
    (fun k => by rw [hzsupp k]; simp) htri
  have hclos_le : Subgroup.closure (Set.range z) ≤ L :=
    (Subgroup.closure_le L).mpr (by rintro _ ⟨k, rfl⟩; exact hzmem k)
  have hleL : Nat.card ↥(Subgroup.closure (Set.range z)) ≤ Nat.card ↥L :=
    Subgroup.card_le_of_le hclos_le
  have hLcard : Nat.card ↥L = p ^ r := s16e_d3_card_of_elem hE
  have hlt : p ^ r < p ^ (r + 1) := Nat.pow_lt_pow_succ hp.one_lt
  have : p ^ (r + 1) ≤ p ^ r := le_trans hcard (le_trans hleL (le_of_eq hLcard))
  exact absurd this (not_le.mpr hlt)

theorem s16e_d3_le_ker (h : s16e_d3_Ctx A L r Δ σ) : L ≤ s16e_d3_ker A Δ := by
  intro l hl
  have hlA : (l : MulAut W) ∈ A := h.le hl
  have hpow : (⟨l, hlA⟩ : ↥A) ^ 7 = 1 := by
    have hL := s16e_d3_pow_eq_one_of_elem h.elem (⟨l, hl⟩ : ↥L)
    exact Subtype.ext (by simpa using congrArg Subtype.val hL)
  have hπ7 : σ ⟨l, hlA⟩ ^ 7 = 1 := by
    rw [← map_pow, hpow, map_one]
  have hdvd7 : orderOf (σ ⟨l, hlA⟩) ∣ 7 := orderOf_dvd_iff_pow_eq_one.mpr hπ7
  have hdvdFact : orderOf (σ ⟨l, hlA⟩) ∣ Nat.factorial (r + 1) := by
    have h1 := orderOf_dvd_natCard (σ ⟨l, hlA⟩)
    rwa [Nat.card_perm, Nat.card_fin] at h1
  have hnotdvd : ¬ 7 ∣ Nat.factorial (r + 1) := by
    intro hd
    have hle : 7 ≤ r + 1 := (Nat.Prime.dvd_factorial (by norm_num : Nat.Prime 7)).mp hd
    have hr5 : r ≤ 5 := h.le_five
    omega
  have horder1 : orderOf (σ ⟨l, hlA⟩) = 1 := by
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hdvd7 with h1 | h7
    · exact h1
    · exfalso
      exact hnotdvd (h7 ▸ hdvdFact)
  have hπ1 : σ ⟨l, hlA⟩ = 1 := orderOf_eq_one_iff.mp horder1
  exact (s16e_d3_mem_ker_iff h.cfg).mpr ⟨hlA, hπ1⟩

private theorem s16e_d3_le_stabSub (h : s16e_d3_Ctx A L r Δ σ) (k : Fin (r + 1)) :
    L ≤ stabSub (Δ k) :=
  (s16e_d3_le_ker h).trans (le_trans inf_le_right (iInf_le _ k))

theorem s16e_d3_card_autSub (h : s16e_d3_Ctx A L r Δ σ) (i : Fin (r + 1)) :
    Nat.card (autSub L (Δ i)) = 7 := by
  have hprime : Nat.Prime 7 := by norm_num
  have hLst : L ≤ stabSub (Δ i) := s16e_d3_le_stabSub h i
  have hcardL : Nat.card ↥L = 7 ^ r := s16e_d3_card_of_elem h.elem
  have hdiv : Nat.card (autSub L (Δ i)) ∣ 7 ^ r := by
    have hcm := card_autSub_mul hLst
    rw [hcardL] at hcm
    exact ⟨_, hcm.symm⟩
  have hle7 : Nat.card (autSub L (Δ i)) ≤ 7 := by
    have hidx : Nat.card ↥L ≤ 7 * Nat.card ↥(L ⊓ centSub (Δ i)) :=
      s16n9b_case4_aut_index_le (T := W) (p := 7) (Or.inr rfl) h.sq_eq_one
        (Y := Δ i) (by rw [h.cfg.rk_eq i, s16e_d3_dParam_seven])
        (s16e_d3_isElemAbelian h.elem)
        (fun f hf => s16e_d3_map_eq_of_mem_stab (hLst hf))
    have hCpos : 0 < Nat.card ↥(L ⊓ centSub (Δ i)) := Nat.card_pos
    have hcm := card_autSub_mul hLst
    have : Nat.card (autSub L (Δ i)) * Nat.card ↥(L ⊓ centSub (Δ i)) ≤
        7 * Nat.card ↥(L ⊓ centSub (Δ i)) := by
      rw [hcm]
      exact hidx
    exact Nat.le_of_mul_le_mul_right this hCpos
  have hne1 : Nat.card (autSub L (Δ i)) ≠ 1 := by
    intro hcard1
    have hbot : autSub L (Δ i) = ⊥ := Subgroup.card_eq_one.mp hcard1
    have hfixi : ∀ l ∈ L, ∀ x ∈ Δ i, l x = x := by
      intro l hl x hx
      have hstab : l ∈ stabSub (Δ i) := hLst hl
      have hmem : resHom (Δ i) ⟨l, hstab⟩ ∈ autSub L (Δ i) :=
        mem_autSub.mpr ⟨⟨l, hstab⟩, hl, rfl⟩
      rw [hbot] at hmem
      have h1 : resHom (Δ i) ⟨l, hstab⟩ = 1 := Subgroup.mem_bot.mp hmem
      have h2 := congrArg (fun φ : MulAut ↥(Δ i) => ((φ ⟨x, hx⟩ : ↥(Δ i)) : W)) h1
      simp only [MulAut.one_apply] at h2
      rw [resHom_apply] at h2
      simpa using h2
    have hLbot : L = ⊥ := by
      apply le_bot_iff.mp
      intro l hl
      apply s16e_d3_eq_one_of_forall_fixes h.cfg
      intro j x hx
      obtain ⟨g, hgA, hgmap⟩ := s16e_d3_exists_map_eq h.cfg i j
      have hconj : g⁻¹ * l * g ∈ L :=
        s16e_d3_conj_mem_of_map_conj_eq (h.normal g⁻¹ (A.inv_mem hgA)) hl
      have hgix : g⁻¹ x ∈ Δ i := by
        have hx' : x ∈ (Δ i).map g.toMonoidHom := by rw [hgmap]; exact hx
        obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx'
        have hyy : g⁻¹ x = y := by rw [← hyx]; simp
        rwa [hyy]
      have hfix := hfixi (g⁻¹ * l * g) hconj (g⁻¹ x) hgix
      have hfix' : g⁻¹ (l x) = g⁻¹ x := by
        simpa [MulAut.mul_apply, MulAut.apply_inv_self] using hfix
      exact g⁻¹.injective hfix'
    have h1 : Nat.card ↥L = 1 := by rw [hLbot]; simp
    rw [s16e_d3_card_of_elem h.elem] at h1
    have h2 : 7 ^ 2 ≤ 7 ^ r := Nat.pow_le_pow_right (by norm_num) h.two_le
    have h3 : (49 : ℕ) ≤ 1 := by
      calc (49 : ℕ) = 7 ^ 2 := by norm_num
        _ ≤ 7 ^ r := h2
        _ = 1 := h1
    norm_num at h3
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow hprime).mp hdiv
  have hk_le : k ≤ 1 := by
    by_contra hk1
    have hk2 : 2 ≤ k := by omega
    have h1 : 7 ^ 2 ≤ 7 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have h2 : 7 ^ k ≤ 7 := by rw [← hk]; exact hle7
    have h3 : (49 : ℕ) ≤ 7 := by
      calc (49 : ℕ) = 7 ^ 2 := by norm_num
        _ ≤ 7 ^ k := h1
        _ ≤ 7 := h2
    norm_num at h3
  interval_cases k
  · exact absurd (by rw [hk]; norm_num) hne1
  · rw [hk]; norm_num

theorem s16e_d3_eq_one_of_supp_single (h : s16e_d3_Ctx A L r Δ σ) (i : Fin (r + 1))
    {l : MulAut W} (hl : l ∈ L) (hsupp : ∀ k, k ≠ i → ∀ x ∈ Δ k, l x = x) : l = 1 := by
  by_contra hne
  have hne_supp : s16e_d3_supp Δ l ≠ ∅ := by
    intro hempty
    exact hne (s16e_d3_eq_one_of_supp_empty h.cfg.sup_eq hempty)
  have hsub : s16e_d3_supp Δ l ⊆ {i} := by
    intro k hk
    by_contra hki
    rw [Set.mem_singleton_iff] at hki
    obtain ⟨x, hx, hlx⟩ := hk
    exact hlx (hsupp k hki x hx)
  have hsing : s16e_d3_supp Δ l = {i} := by
    apply Set.Subset.antisymm hsub
    intro w hw
    have hwi : w = i := by simpa using hw
    rw [hwi]
    obtain ⟨k, hk⟩ := Set.nonempty_iff_ne_empty.mpr hne_supp
    have hki : k = i := by
      have := hsub hk
      simpa using this
    rw [hki] at hk
    exact hk
  exact s16e_d3_supp_not_singleton (p := 7) (by norm_num) h.elem h.normal h.cfg.surj
    h.cfg.map_eq hl hsing

theorem s16e_d3_exists_supp_pair (h : s16e_d3_Ctx A L r Δ σ) {i j : Fin (r + 1)} (hij : i ≠ j) :
    ∃ l ∈ L, (∃ x ∈ Δ i, l x ≠ x) ∧ (∃ x ∈ Δ j, l x ≠ x) ∧
      ∀ k, k ≠ i → k ≠ j → ∀ x ∈ Δ k, l x = x := by
  have hprime : Nat.Prime 7 := by norm_num
  let S : Finset (Fin (r + 1)) := (Finset.univ.erase i).erase j
  have hScard : S.card < r := by
    have h1 : (Finset.univ.erase i).card = r := by
      rw [Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ, Fintype.card_fin]
      omega
    have hjmem : j ∈ Finset.univ.erase i :=
      Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩
    show ((Finset.univ.erase i).erase j).card < r
    rw [Finset.card_erase_of_mem hjmem, h1]
    omega
  have hY : ∀ k ∈ S, rk ↥(Δ k) = dParam 7 := fun k _ => by
    rw [h.cfg.rk_eq k, s16e_d3_dParam_seven]
  have hFY : ∀ k ∈ S, ∀ f ∈ L, (Δ k).map f.toMonoidHom = Δ k :=
    fun k _ f hf => s16e_d3_map_eq_of_mem_stab (s16e_d3_le_stabSub h k hf)
  have hL7 : 7 ^ r ≤ Nat.card ↥L := by rw [s16e_d3_card_of_elem h.elem]
  obtain ⟨l, hl, hl7, hlfix⟩ :=
    s16n9b_case4_aut_supp (T := W) (p := 7) (n := r) (Or.inr rfl) h.sq_eq_one
      (s16e_d3_isElemAbelian h.elem) hL7 Δ S hY hFY hScard
  have hmemS : ∀ k, k ≠ i → k ≠ j → k ∈ S := by
    intro k hki hkj
    show k ∈ (Finset.univ.erase i).erase j
    exact Finset.mem_erase.mpr ⟨hkj, Finset.mem_erase.mpr ⟨hki, Finset.mem_univ k⟩⟩
  refine ⟨l, hl, ?_, ?_, ?_⟩
  · by_contra hcon
    have hfixi : ∀ x ∈ Δ i, l x = x := by
      intro x hx
      by_contra hne
      exact hcon ⟨x, hx, hne⟩
    have hsingle : l = 1 := by
      apply s16e_d3_eq_one_of_supp_single h j hl
      intro k hkj x hx
      by_cases hki : k = i
      · subst hki; exact hfixi x hx
      · exact hlfix k (hmemS k hki hkj) x hx
    rw [hsingle, orderOf_one] at hl7
    norm_num at hl7
  · by_contra hcon
    have hfixj : ∀ x ∈ Δ j, l x = x := by
      intro x hx
      by_contra hne
      exact hcon ⟨x, hx, hne⟩
    have hsingle : l = 1 := by
      apply s16e_d3_eq_one_of_supp_single h i hl
      intro k hki x hx
      by_cases hkj : k = j
      · subst hkj; exact hfixj x hx
      · exact hlfix k (hmemS k hki hkj) x hx
    rw [hsingle, orderOf_one] at hl7
    norm_num at hl7
  · intro k hki hkj x hx
    exact hlfix k (hmemS k hki hkj) x hx

theorem s16e_d3_eq_one_of_pow_three (h : s16e_d3_Ctx A L r Δ σ) {g : MulAut W}
    (hg : g ∈ s16e_d3_ker A Δ) (hg3 : g ^ 3 = 1) (i : Fin (r + 1)) (hi : ∀ x ∈ Δ i, g x = x) :
    g = 1 := by
  have hgA : g ∈ A := (Subgroup.mem_inf.mp hg).1
  have hg_stab : ∀ k, g ∈ stabSub (Δ k) := fun k =>
    (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp hg).2) k
  have hclaim : ∀ j, j ≠ i → ∀ y ∈ Δ j, g y = y := by
    intro j hji
    obtain ⟨l, hl, -, hlj, hlfix⟩ := s16e_d3_exists_supp_pair h hji.symm
    have hl7 : l ^ 7 = 1 := by
      have hL := s16e_d3_pow_eq_one_of_elem h.elem (⟨l, hl⟩ : ↥L)
      simpa using congrArg Subtype.val hL
    have hconj : g * l * g⁻¹ ∈ L :=
      s16e_d3_conj_mem_of_map_conj_eq (h.normal g hgA) hl
    have hc_mem : g * l * g⁻¹ * l⁻¹ ∈ L := L.mul_mem hconj (L.inv_mem hl)
    have hc_fix : ∀ k, k ≠ j → ∀ x ∈ Δ k, (g * l * g⁻¹ * l⁻¹) x = x := by
      intro k hkj x hx
      by_cases hki : k = i
      · rw [hki] at hx
        have hlinv : l⁻¹ x ∈ Δ i :=
          (mem_stabSub.mp ((stabSub (Δ i)).inv_mem (s16e_d3_le_stabSub h i hl)) x).mpr hx
        have hginv : g⁻¹ (l⁻¹ x) = l⁻¹ x := by
          apply g.injective
          rw [MulAut.apply_inv_self, hi (l⁻¹ x) hlinv]
        calc (g * l * g⁻¹ * l⁻¹) x = g (l (g⁻¹ (l⁻¹ x))) := by simp [MulAut.mul_apply]
          _ = g (l (l⁻¹ x)) := by rw [hginv]
          _ = g x := by rw [MulAut.apply_inv_self]
          _ = x := hi x hx
      · have hlx : l x = x := hlfix k hki hkj x hx
        have hlinvx : l⁻¹ x = x := by
          apply l.injective
          rw [MulAut.apply_inv_self, hlx]
        have hgx : g⁻¹ x ∈ Δ k :=
          (mem_stabSub.mp ((stabSub (Δ k)).inv_mem (hg_stab k)) x).mpr hx
        calc (g * l * g⁻¹ * l⁻¹) x = g (l (g⁻¹ (l⁻¹ x))) := by simp [MulAut.mul_apply]
          _ = g (l (g⁻¹ x)) := by rw [hlinvx]
          _ = g (g⁻¹ x) := by rw [hlfix k hki hkj (g⁻¹ x) hgx]
          _ = x := by rw [MulAut.apply_inv_self]
    have hc1 : g * l * g⁻¹ * l⁻¹ = 1 :=
      s16e_d3_eq_one_of_supp_single h j hc_mem hc_fix
    have hgl : g * l = l * g := by
      have h1 : g * l * g⁻¹ = l := mul_inv_eq_one.mp hc1
      calc g * l = (g * l * g⁻¹) * g := by
            rw [mul_assoc (g * l) g⁻¹ g, inv_mul_cancel, mul_one]
        _ = l * g := by rw [h1]
    exact s16e_d3_eq_of_commute_on_block h.sq_eq_one (s16e_d3_card_block h j)
      (hg_stab j) (s16e_d3_le_stabSub h j hl) hgl hg3 hl7 hlj
  apply s16e_d3_eq_one_of_forall_fixes h.cfg
  intro k x hx
  by_cases hki : k = i
  · subst hki; exact hi x hx
  · exact hclaim k hki x hx

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
