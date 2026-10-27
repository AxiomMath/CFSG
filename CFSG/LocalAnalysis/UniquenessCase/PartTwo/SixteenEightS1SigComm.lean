module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise IsMulCommutative

variable {W : Type} [CommGroup W]

private theorem s16e_cm_stabSub_top :
    stabSub (⊤ : Subgroup W) = (⊤ : Subgroup (MulAut W)) := by
  ext g
  rw [mem_stabSub]
  simp

private theorem s16e_cm_inf_stabSub_top (A : Subgroup (MulAut W)) :
    A ⊓ stabSub (⊤ : Subgroup W) = A := by
  rw [s16e_cm_stabSub_top, inf_top_eq]

private theorem s16e_cm_comm_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s16e_cm_pow_eq_one_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) (x : X) : x ^ p = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp

private theorem s16e_cm_card_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card X = Nat.card (Multiplicative (Fin n → ZMod p)) := Nat.card_congr e.toEquiv
  rw [h1, show Nat.card (Multiplicative (Fin n → ZMod p)) = Nat.card (Fin n → ZMod p) from rfl,
    Nat.card_fun]
  simp [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]

private theorem s16e_cm_pow_val_add {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) {x : X}
    (hx : x ^ p = 1) (a b : ZMod p) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmod : (a + b).val ≡ a.val + b.val [MOD p] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx
  calc x ^ (a + b).val = x ^ (a.val + b.val) := pow_eq_pow_iff_modEq.mpr (hmod.of_dvd hdvd)
    _ = x ^ a.val * x ^ b.val := pow_add x a.val b.val

private def s16e_cm_supp {r : ℕ} (Δ : Fin (r + 1) → Subgroup W) (l : MulAut W) :
    Set (Fin (r + 1)) :=
  {i | ∃ x ∈ Δ i, l x ≠ x}

private theorem s16e_cm_notMem_supp_iff {r : ℕ} {Δ : Fin (r + 1) → Subgroup W} {l : MulAut W}
    {i : Fin (r + 1)} : i ∉ s16e_cm_supp Δ l ↔ l ∈ centSub (Δ i) := by
  rw [mem_centSub]
  simp [s16e_cm_supp]

private theorem s16e_cm_cent_of_notMem_supp {r : ℕ} {Δ : Fin (r + 1) → Subgroup W}
    {l : MulAut W} {i : Fin (r + 1)} (h : i ∉ s16e_cm_supp Δ l) : l ∈ centSub (Δ i) :=
  s16e_cm_notMem_supp_iff.mp h

private theorem s16e_cm_supp_conj {r : ℕ} {A : Subgroup (MulAut W)}
    {Δ : Fin (r + 1) → Subgroup W}
    {σ : ↥(A ⊓ stabSub (⊤ : Subgroup W)) →* Equiv.Perm (Fin (r + 1))}
    (hσact : ∀ (g : ↥(A ⊓ stabSub (⊤ : Subgroup W))) (i : Fin (r + 1)),
      (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i))
    (g : ↥(A ⊓ stabSub (⊤ : Subgroup W))) (l : MulAut W) :
    s16e_cm_supp Δ ((g : MulAut W) * l * (g : MulAut W)⁻¹) = σ g '' s16e_cm_supp Δ l := by
  ext i
  constructor
  · rintro ⟨x, hx, hne⟩
    have hgx : ((g⁻¹ : ↥(A ⊓ stabSub (⊤ : Subgroup W))) : MulAut W) x ∈ Δ (σ g⁻¹ i) := by
      rw [← hσact g⁻¹ i]
      exact Subgroup.mem_map_of_mem _ hx
    have hly : l (((g⁻¹ : ↥(A ⊓ stabSub (⊤ : Subgroup W))) : MulAut W) x) ≠
        ((g⁻¹ : ↥(A ⊓ stabSub (⊤ : Subgroup W))) : MulAut W) x := by
      intro h
      apply hne
      calc ((g : MulAut W) * l * (g : MulAut W)⁻¹) x
          = (g : MulAut W) (l (((g⁻¹ : ↥(A ⊓ stabSub (⊤ : Subgroup W))) : MulAut W) x)) := rfl
        _ = (g : MulAut W) (((g⁻¹ : ↥(A ⊓ stabSub (⊤ : Subgroup W))) : MulAut W) x) := by
              rw [h]
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

private theorem s16e_cm_eq_one_of_supp_empty {r : ℕ} {Δ : Fin (r + 1) → Subgroup W}
    (hsup : (⨆ i, Δ i) = ⊤) {l : MulAut W} (h : s16e_cm_supp Δ l = ∅) : l = 1 := by
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

private theorem s16e_cm_dvd_of_pow_mem_centSub [Finite W] {L : Subgroup (MulAut W)} {p r : ℕ}
    (hE : IsElemAbelianOfRank p r ↥L) (hp : p.Prime) {l : MulAut W} (hl : l ∈ L) {e : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {i : Fin (r + 1)}
    (hi : i ∈ s16e_cm_supp Δ l) (he : l ^ e ∈ centSub (Δ i)) : p ∣ e := by
  have hl1 : l ≠ 1 := by
    rintro rfl
    obtain ⟨x, -, hne⟩ := hi
    exact hne rfl
  have hpow : l ^ p = 1 := by
    have h := s16e_cm_pow_eq_one_of_elem hE (⟨l, hl⟩ : ↥L)
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
    exact (s16e_cm_notMem_supp_iff.mpr hlK.2) hi

private theorem s16e_cm_exists_commutator_ne_one {G : Type*} [Group G] {L Z : Subgroup G}
    (h : ⁅L, Z⁆ ≠ ⊥) : ∃ l ∈ L, ∃ z ∈ Z, ⁅l, z⁆ ≠ 1 := by
  by_contra h'
  have h'' : ∀ l, l ∈ L → ∀ z, z ∈ Z → ⁅l, z⁆ = 1 := by
    intro l hl z hz
    by_contra hne
    exact h' ⟨l, hl, z, hz, hne⟩
  have hbot : ⁅L, Z⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro l hl z hz
    rw [Subgroup.mem_bot]
    exact h'' l hl z hz
  exact h hbot

private theorem s16e_cm_exists_commutator_ne_one_zpowers {G : Type*} [Group G] {L : Subgroup G}
    {t : G} (h : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) : ∃ l ∈ L, ⁅l, t⁆ ≠ 1 := by
  obtain ⟨l, hl, z, hz, hne⟩ := s16e_cm_exists_commutator_ne_one h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨l, hl, fun hlt => ?_⟩
  refine hne ?_
  rw [← hk]
  exact commutatorElement_eq_one_iff_commute.mpr
    ((commutatorElement_eq_one_iff_commute.mp hlt).zpow_right k)

private theorem s16e_cm_triangular_card [Finite W] {L : Subgroup (MulAut W)} {p r : ℕ}
    (hp : p.Prime) (hE : IsElemAbelianOfRank p r ↥L) {s : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {v : Fin s → MulAut W} {i : Fin s → Fin (r + 1)}
    (hv : ∀ k, v k ∈ L)
    (hmem : ∀ k, i k ∈ s16e_cm_supp Δ (v k))
    (htri : ∀ k j, k < j → i k ∉ s16e_cm_supp Δ (v j)) :
    p ^ s ≤ Nat.card ↥(Subgroup.closure (Set.range v)) := by
  have hclos_le : Subgroup.closure (Set.range v) ≤ L :=
    (Subgroup.closure_le L).mpr (by rintro _ ⟨k, rfl⟩; exact hv k)
  let x : Fin s → ↥(Subgroup.closure (Set.range v)) := fun k =>
    ⟨v k, Subgroup.subset_closure ⟨k, rfl⟩⟩
  haveI hcomm : IsMulCommutative ↥(Subgroup.closure (Set.range v)) :=
    IsMulCommutative.of_comm fun a b => by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact congrArg Subtype.val (s16e_cm_comm_of_elem hE
        (⟨(a : MulAut W), hclos_le a.2⟩ : ↥L) (⟨(b : MulAut W), hclos_le b.2⟩ : ↥L))
  have hxpow : ∀ k, (x k) ^ p = 1 := fun k => by
    apply Subtype.ext
    show (v k) ^ p = 1
    have h := s16e_cm_pow_eq_one_of_elem hE (⟨v k, hv k⟩ : ↥L)
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
        exact s16e_cm_pow_val_add hp (hxpow k) _ _ }
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
        · exact Subgroup.pow_mem _ (s16e_cm_cent_of_notMem_supp (htri k j hgt)) _
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
    have hdvd := s16e_cm_dvd_of_pow_mem_centSub hE hp (hv k) (hmem k) hcent
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

private theorem s16e_cm_supp_not_singleton [Finite W] {A L : Subgroup (MulAut W)} {p r : ℕ}
    (hp : p.Prime) (hE : IsElemAbelianOfRank p r ↥L)
    (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    {Δ : Fin (r + 1) → Subgroup W}
    {σ : ↥(A ⊓ stabSub (⊤ : Subgroup W)) →* Equiv.Perm (Fin (r + 1))}
    (hσsurj : Function.Surjective σ)
    (hσact : ∀ (g : ↥(A ⊓ stabSub (⊤ : Subgroup W))) (i : Fin (r + 1)),
      (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i))
    {y : MulAut W} (hy : y ∈ L) {c : Fin (r + 1)} (hS : s16e_cm_supp Δ y = {c}) : False := by
  choose g hg using fun k : Fin (r + 1) => hσsurj (Equiv.swap c k)
  let z : Fin (r + 1) → MulAut W := fun k => (g k : MulAut W) * y * (g k : MulAut W)⁻¹
  have hzmem : ∀ k, z k ∈ L := by
    intro k
    have hgA : (g k : MulAut W) ∈ A := (Subgroup.mem_inf.mp (g k).2).1
    have hconj : (MulAut.conj (g k : MulAut W)) y ∈ L := by
      rw [← hLn (g k : MulAut W) hgA]
      exact Subgroup.mem_map_of_mem _ hy
    simpa [z, MulAut.conj_apply] using hconj
  have hzsupp : ∀ k, s16e_cm_supp Δ (z k) = {k} := by
    intro k
    have h := s16e_cm_supp_conj (A := A) hσact (g k) y
    rw [hS, hg k] at h
    rw [show z k = (g k : MulAut W) * y * (g k : MulAut W)⁻¹ from rfl, h]
    rw [Set.image_singleton, Equiv.swap_apply_left]
  have htri : ∀ k j, k < j → k ∉ s16e_cm_supp Δ (z j) := by
    intro k j hkj
    rw [hzsupp j]
    simp [ne_of_lt hkj]
  have hcard := s16e_cm_triangular_card (L := L) (s := r + 1) (i := fun k => k) hp hE hzmem
    (fun k => by rw [hzsupp k]; simp) htri
  have hclos_le : Subgroup.closure (Set.range z) ≤ L :=
    (Subgroup.closure_le L).mpr (by rintro _ ⟨k, rfl⟩; exact hzmem k)
  have hleL : Nat.card ↥(Subgroup.closure (Set.range z)) ≤ Nat.card ↥L :=
    Subgroup.card_le_of_le hclos_le
  have hLcard : Nat.card ↥L = p ^ r := s16e_cm_card_of_elem hE
  have hlt : p ^ r < p ^ (r + 1) := Nat.pow_lt_pow_succ hp.one_lt
  have : p ^ (r + 1) ≤ p ^ r := le_trans hcard (le_trans hleL (le_of_eq hLcard))
  exact absurd this (not_le.mpr hlt)

theorem s16e_comm_le_commutator {W : Type} [CommGroup W] [Finite W]
    {A L : Subgroup (MulAut W)} {t : MulAut W} {p r m : ℕ} (hp : p.Prime) (hr : 4 ≤ r)
    (hLA : L ≤ A) (hLn : ∀ g ∈ A, L.map (MulAut.conj g).toMonoidHom = L)
    (hE : IsElemAbelianOfRank p r ↥L) (hLt : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥)
    (hD : DeltaSym A t (⊤ : Subgroup W) r m) : L ≤ ⁅A, A⁆ := by
  obtain ⟨Δ, -, -, -, hsup, σ, hσsurj, hσact, ht, hswap, hfix⟩ := hD
  have hDtop : A ⊓ stabSub (⊤ : Subgroup W) = A := s16e_cm_inf_stabSub_top A
  have hHnorm : (L.subgroupOf (A ⊓ stabSub (⊤ : Subgroup W))).Normal := by
    constructor
    intro n hn g
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    have hg : (g : MulAut W) ∈ A := (Subgroup.mem_inf.mp g.2).1
    have hmem : (MulAut.conj (g : MulAut W)).toMonoidHom (n : MulAut W) ∈
        L.map (MulAut.conj (g : MulAut W)).toMonoidHom := Subgroup.mem_map_of_mem _ hn
    rw [hLn (g : MulAut W) hg] at hmem
    simpa [MulAut.conj_apply] using hmem
  let N : Subgroup (Equiv.Perm (Fin (r + 1))) :=
    (L.subgroupOf (A ⊓ stabSub (⊤ : Subgroup W))).map σ
  have hNnorm : N.Normal := hHnorm.map σ hσsurj
  have hNcomm : ∀ a b : N, a * b = b * a := by
    rintro ⟨a, ha⟩ ⟨b, hb⟩
    obtain ⟨a', ha', rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b', hb', rfl⟩ := Subgroup.mem_map.mp hb
    refine Subtype.ext ?_
    show σ a' * σ b' = σ b' * σ a'
    rw [← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    show (a' : MulAut W) * (b' : MulAut W) = (b' : MulAut W) * (a' : MulAut W)
    exact congrArg Subtype.val (s16e_cm_comm_of_elem hE
      (⟨(a' : MulAut W), Subgroup.mem_subgroupOf.mp ha'⟩ : ↥L)
      (⟨(b' : MulAut W), Subgroup.mem_subgroupOf.mp hb'⟩ : ↥L))
  have hNbot : N = ⊥ := by
    by_contra hne
    have hNntriv : Nontrivial N := (nontrivial_iff_ne_bot N).mpr hne
    haveI : Nontrivial N := hNntriv
    haveI : N.Normal := hNnorm
    have hn5 : 5 ≤ Nat.card (Fin (r + 1)) := by
      simp [Nat.card_eq_fintype_card]
      omega
    have hAlt : alternatingGroup (Fin (r + 1)) ≤ N :=
      Equiv.Perm.alternatingGroup_le_of_normal hn5 hNntriv
    have hAltcomm : IsMulCommutative ↥(alternatingGroup (Fin (r + 1))) :=
      IsMulCommutative.of_comm fun a b => by
        refine Subtype.ext ?_
        simp only [Subgroup.coe_mul]
        exact congrArg Subtype.val (hNcomm ⟨a.1, hAlt a.2⟩ ⟨b.1, hAlt b.2⟩)
    have hcard3 : Nat.card (Fin (r + 1)) ≤ 3 :=
      (alternatingGroup.isMulCommutative_iff_card_le_three).mp hAltcomm
    omega
  have hσL : ∀ d : ↥(A ⊓ stabSub (⊤ : Subgroup W)), (d : MulAut W) ∈ L → σ d = 1 := by
    intro d hd
    have hmem : σ d ∈ N := Subgroup.mem_map_of_mem σ (Subgroup.mem_subgroupOf.mpr hd)
    rw [hNbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  have hmapL : ∀ l ∈ L, ∀ i, (Δ i).map l.toMonoidHom = Δ i := by
    intro l hl i
    have hd : l ∈ A ⊓ stabSub (⊤ : Subgroup W) := by rw [hDtop]; exact hLA hl
    have h := hσact ⟨l, hd⟩ i
    rw [hσL ⟨l, hd⟩ hl, Equiv.Perm.one_apply] at h
    simpa using h
  obtain ⟨l, hlL, hly⟩ := s16e_cm_exists_commutator_ne_one_zpowers hLt
  let y : MulAut W := ⁅l, t⁆
  have hy_ne : y ≠ 1 := hly
  have hyL : y ∈ L := by
    have htA : t ∈ A := (Subgroup.mem_inf.mp ht).1
    have hconj : (MulAut.conj t) l⁻¹ ∈ L := by
      rw [← hLn t htA]
      exact Subgroup.mem_map_of_mem _ (L.inv_mem hlL)
    have hy_eq : y = l * (MulAut.conj t) l⁻¹ := by
      simp [y, commutatorElement_def, MulAut.conj_apply, mul_assoc]
    rw [hy_eq]
    exact L.mul_mem hlL hconj
  obtain ⟨a, b, hab, hσt⟩ := hswap
  have hy_supp_sub : s16e_cm_supp Δ y ⊆ ({a, b} : Set (Fin (r + 1))) := by
    intro k hk
    by_contra hkab
    have hka : k ≠ a := by rintro rfl; exact hkab (by simp)
    have hkb : k ≠ b := by rintro rfl; exact hkab (by simp)
    have hkfix : ∀ x ∈ Δ k, t x = x :=
      hfix (by omega) k (by rw [hσt, Equiv.swap_apply_of_ne_of_ne hka hkb])
    obtain ⟨x, hx, hne⟩ := hk
    apply hne
    have htinv : t⁻¹ x = x := by
      apply t.injective
      simpa [hkfix x hx] using (MulEquiv.apply_symm_apply t x)
    have hlinv : l⁻¹ x ∈ Δ k := by
      have hmap := hmapL l⁻¹ (L.inv_mem hlL) k
      rw [← hmap]
      exact Subgroup.mem_map_of_mem _ hx
    have htx : t (l⁻¹ x) = l⁻¹ x := hkfix _ hlinv
    have hy_eq : y = l * t * l⁻¹ * t⁻¹ := rfl
    rw [hy_eq]
    calc (l * t * l⁻¹ * t⁻¹) x = l (t (l⁻¹ (t⁻¹ x))) := rfl
      _ = l (t (l⁻¹ x)) := by rw [htinv]
      _ = l (l⁻¹ x) := by rw [htx]
      _ = x := by simp
  have hy_supp_ne : s16e_cm_supp Δ y ≠ ∅ := fun h =>
    hy_ne (s16e_cm_eq_one_of_supp_empty hsup h)
  have hy_not_singleton : ¬ ∃ c, s16e_cm_supp Δ y = {c} := by
    rintro ⟨c, hc⟩
    exact s16e_cm_supp_not_singleton hp hE hLn hσsurj hσact hyL hc
  have hy_supp : s16e_cm_supp Δ y = {a, b} := by
    by_cases ha : a ∈ s16e_cm_supp Δ y <;> by_cases hb : b ∈ s16e_cm_supp Δ y
    · exact Set.Subset.antisymm hy_supp_sub (by
        intro w hw
        rcases hw with rfl | rfl
        · exact ha
        · exact hb)
    · exact absurd ⟨a, Set.eq_singleton_iff_unique_mem.mpr ⟨ha, fun z hz => by
        rcases hy_supp_sub hz with hza | hzb
        · exact hza
        · exact absurd (hzb ▸ hz) hb⟩⟩ hy_not_singleton
    · exact absurd ⟨b, Set.eq_singleton_iff_unique_mem.mpr ⟨hb, fun z hz => by
        rcases hy_supp_sub hz with hza | hzb
        · exact absurd (hza ▸ hz) ha
        · exact hzb⟩⟩ hy_not_singleton
    · obtain ⟨x, hx⟩ := Set.nonempty_iff_ne_empty.mpr hy_supp_ne
      rcases hy_supp_sub hx with hxa | hxb
      · exact absurd (hxa ▸ hx) ha
      · exact absurd (hxb ▸ hx) hb
  have hperm : ∀ m : Fin r, ∃ g : ↥(A ⊓ stabSub (⊤ : Subgroup W)),
      σ g = Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m) *
        Equiv.swap a (Fin.castSucc m) := fun m => hσsurj _
  choose g hg using hperm
  let u : Fin r → MulAut W := fun m => (g m : MulAut W) * y * (g m : MulAut W)⁻¹
  have hu_supp : ∀ m : Fin r, s16e_cm_supp Δ (u m) = {Fin.castSucc m, Fin.succ m} := by
    intro m
    have hpc : Fin.castSucc m ≠ Equiv.swap a (Fin.castSucc m) b := by
      intro h
      have h' : a = b := by
        have h2 := congrArg (Equiv.swap a (Fin.castSucc m)) h
        simpa using h2
      exact hab h'
    have hpq : Fin.castSucc m ≠ Fin.succ m := ne_of_lt (Fin.castSucc_lt_succ (i := m))
    have hπa : (Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m) *
        Equiv.swap a (Fin.castSucc m) : Equiv.Perm (Fin (r + 1))) a = Fin.castSucc m := by
      show Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m)
          (Equiv.swap a (Fin.castSucc m) a) = Fin.castSucc m
      rw [Equiv.swap_apply_left, Equiv.swap_apply_of_ne_of_ne hpc hpq]
    have hπb : (Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m) *
        Equiv.swap a (Fin.castSucc m) : Equiv.Perm (Fin (r + 1))) b = Fin.succ m := by
      show Equiv.swap (Equiv.swap a (Fin.castSucc m) b) (Fin.succ m)
          (Equiv.swap a (Fin.castSucc m) b) = Fin.succ m
      rw [Equiv.swap_apply_left]
    have h := s16e_cm_supp_conj (A := A) hσact (g m) y
    rw [hy_supp, hg m] at h
    rw [show u m = (g m : MulAut W) * y * (g m : MulAut W)⁻¹ from rfl, h,
      Set.image_insert_eq, Set.image_singleton, hπa, hπb]
  have huL : ∀ m, u m ∈ L := by
    intro m
    have hgA : (g m : MulAut W) ∈ A := (Subgroup.mem_inf.mp (g m).2).1
    have hconj : (MulAut.conj (g m : MulAut W)) y ∈ L := by
      rw [← hLn (g m : MulAut W) hgA]
      exact Subgroup.mem_map_of_mem _ hyL
    simpa [u, MulAut.conj_apply] using hconj
  have hu_comm : ∀ m, u m ∈ ⁅A, A⁆ := by
    intro m
    have hgA : (g m : MulAut W) ∈ A := (Subgroup.mem_inf.mp (g m).2).1
    have htA : t ∈ A := (Subgroup.mem_inf.mp ht).1
    have hlA : l ∈ A := hLA hlL
    have h1 : (MulAut.conj (g m : MulAut W)) l ∈ A :=
      A.mul_mem (A.mul_mem hgA hlA) (A.inv_mem hgA)
    have h2 : (MulAut.conj (g m : MulAut W)) t ∈ A :=
      A.mul_mem (A.mul_mem hgA htA) (A.inv_mem hgA)
    have hmem : ⁅(MulAut.conj (g m : MulAut W)) l, (MulAut.conj (g m : MulAut W)) t⁆ ∈
        ⁅A, A⁆ := Subgroup.commutator_mem_commutator h1 h2
    have hu_eq : u m = ⁅(MulAut.conj (g m : MulAut W)) l, (MulAut.conj (g m : MulAut W)) t⁆ := by
      have h1 : u m = (MulAut.conj (g m : MulAut W)).toMonoidHom y := rfl
      rw [h1]
      simpa [y] using map_commutatorElement (MulAut.conj (g m : MulAut W)).toMonoidHom l t
    rw [hu_eq]
    exact hmem
  have hu_mem : ∀ m, Fin.castSucc m ∈ s16e_cm_supp Δ (u m) := fun m => by
    rw [hu_supp m]
    exact Set.mem_insert _ _
  have hu_tri : ∀ m j, m < j → Fin.castSucc m ∉ s16e_cm_supp Δ (u j) := by
    intro m j hmj
    rw [hu_supp j]
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rintro (h | h)
    · have := congrArg Fin.val h
      simp only [Fin.val_castSucc] at this
      omega
    · have := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_succ] at this
      omega
  have hcard_u : p ^ r ≤ Nat.card ↥(Subgroup.closure (Set.range u)) :=
    s16e_cm_triangular_card (L := L) (s := r) (i := Fin.castSucc) hp hE huL hu_mem hu_tri
  have hLcard : Nat.card ↥L = p ^ r := s16e_cm_card_of_elem hE
  have hclosure_le_L : Subgroup.closure (Set.range u) ≤ L :=
    (Subgroup.closure_le L).mpr (by rintro _ ⟨m, rfl⟩; exact huL m)
  have hclosure_le_comm : Subgroup.closure (Set.range u) ≤ ⁅A, A⁆ :=
    (Subgroup.closure_le ⁅A, A⁆).mpr (by rintro _ ⟨m, rfl⟩; exact hu_comm m)
  have hcard_le : Nat.card ↥(Subgroup.closure (Set.range u)) ≤ Nat.card ↥L :=
    Subgroup.card_le_of_le hclosure_le_L
  have heq_card : Nat.card ↥(Subgroup.closure (Set.range u)) = Nat.card ↥L :=
    le_antisymm hcard_le (by rw [hLcard]; exact hcard_u)
  have hclosure_eq : Subgroup.closure (Set.range u) = L :=
    Subgroup.eq_of_le_of_card_ge hclosure_le_L (le_of_eq heq_card.symm)
  intro x hx
  exact hclosure_le_comm (hclosure_eq ▸ hx)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
