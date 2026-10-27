module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs16a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped commutatorElement Pointwise IsMulCommutative

variable {W : Type} [CommGroup W]

theorem s16h_dc_comm_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

theorem s16h_dc_pow_eq_one_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) (x : X) : x ^ p = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp

theorem s16h_dc_card_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card X = Nat.card (Multiplicative (Fin n → ZMod p)) := Nat.card_congr e.toEquiv
  rw [h1, show Nat.card (Multiplicative (Fin n → ZMod p)) = Nat.card (Fin n → ZMod p) from rfl,
    Nat.card_fun]
  simp [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]

theorem s16h_dc_pow_val_add {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) {x : X}
    (hx : x ^ p = 1) (a b : ZMod p) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  have hmod : (a + b).val ≡ a.val + b.val [MOD p] := by
    rw [ZMod.val_add]
    exact Nat.mod_modEq _ _
  have hdvd : orderOf x ∣ p := orderOf_dvd_iff_pow_eq_one.mpr hx
  calc x ^ (a + b).val = x ^ (a.val + b.val) := pow_eq_pow_iff_modEq.mpr (hmod.of_dvd hdvd)
    _ = x ^ a.val * x ^ b.val := pow_add x a.val b.val

@[expose] def s16h_dc_supp {r : ℕ} (Δ : Fin (r + 1) → Subgroup W) (l : MulAut W) :
    Set (Fin (r + 1)) :=
  {i | ∃ x ∈ Δ i, l x ≠ x}

theorem s16h_dc_notMem_supp_iff {r : ℕ} {Δ : Fin (r + 1) → Subgroup W} {l : MulAut W}
    {i : Fin (r + 1)} : i ∉ s16h_dc_supp Δ l ↔ l ∈ centSub (Δ i) := by
  rw [mem_centSub]
  simp [s16h_dc_supp]

theorem s16h_dc_cent_of_notMem_supp {r : ℕ} {Δ : Fin (r + 1) → Subgroup W}
    {l : MulAut W} {i : Fin (r + 1)} (h : i ∉ s16h_dc_supp Δ l) : l ∈ centSub (Δ i) :=
  s16h_dc_notMem_supp_iff.mp h

theorem s16h_dc_supp_conj {r : ℕ} {A : Subgroup (MulAut W)} {Wsub : Subgroup W}
    {Δ : Fin (r + 1) → Subgroup W}
    {σ : ↥(A ⊓ stabSub Wsub) →* Equiv.Perm (Fin (r + 1))}
    (hσact : ∀ (g : ↥(A ⊓ stabSub Wsub)) (i : Fin (r + 1)),
      (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i))
    (g : ↥(A ⊓ stabSub Wsub)) (l : MulAut W) :
    s16h_dc_supp Δ ((g : MulAut W) * l * (g : MulAut W)⁻¹) = σ g '' s16h_dc_supp Δ l := by
  ext i
  constructor
  · rintro ⟨x, hx, hne⟩
    have hgx : ((g⁻¹ : ↥(A ⊓ stabSub Wsub)) : MulAut W) x ∈ Δ (σ g⁻¹ i) := by
      rw [← hσact g⁻¹ i]
      exact Subgroup.mem_map_of_mem _ hx
    have hly : l (((g⁻¹ : ↥(A ⊓ stabSub Wsub)) : MulAut W) x) ≠
        ((g⁻¹ : ↥(A ⊓ stabSub Wsub)) : MulAut W) x := by
      intro h
      apply hne
      calc ((g : MulAut W) * l * (g : MulAut W)⁻¹) x
          = (g : MulAut W) (l (((g⁻¹ : ↥(A ⊓ stabSub Wsub)) : MulAut W) x)) := rfl
        _ = (g : MulAut W) (((g⁻¹ : ↥(A ⊓ stabSub Wsub)) : MulAut W) x) := by
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

theorem s16h_dc_eq_one_of_supp_empty {r : ℕ} {Δ : Fin (r + 1) → Subgroup W} {Wsub : Subgroup W}
    {L : Subgroup (MulAut W)} (hsup : (⨆ i, Δ i) = Wsub)
    (hfaith : ∀ l ∈ L, (∀ u ∈ Wsub, l u = u) → l = 1) {l : MulAut W} (hl : l ∈ L)
    (h : s16h_dc_supp Δ l = ∅) : l = 1 := by
  refine hfaith l hl fun x hx => ?_
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
  exact (iSup_le hU) (by rw [hsup]; exact hx)

theorem s16h_dc_dvd_of_pow_mem_centSub [Finite W] {L : Subgroup (MulAut W)} {p r : ℕ}
    (hE : IsElemAbelianOfRank p r ↥L) (hp : p.Prime) {l : MulAut W} (hl : l ∈ L) {e : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {i : Fin (r + 1)}
    (hi : i ∈ s16h_dc_supp Δ l) (he : l ^ e ∈ centSub (Δ i)) : p ∣ e := by
  have hl1 : l ≠ 1 := by
    rintro rfl
    obtain ⟨x, -, hne⟩ := hi
    exact hne rfl
  have hpow : l ^ p = 1 := by
    have h := s16h_dc_pow_eq_one_of_elem hE (⟨l, hl⟩ : ↥L)
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
    exact (s16h_dc_notMem_supp_iff.mpr hlK.2) hi

theorem s16h_dc_exists_commutator_ne_one {G : Type*} [Group G] {L Z : Subgroup G}
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

theorem s16h_dc_exists_commutator_ne_one_zpowers {G : Type*} [Group G] {L : Subgroup G}
    {t : G} (h : ⁅L, Subgroup.zpowers t⁆ ≠ ⊥) : ∃ l ∈ L, ⁅l, t⁆ ≠ 1 := by
  obtain ⟨l, hl, z, hz, hne⟩ := s16h_dc_exists_commutator_ne_one h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
  refine ⟨l, hl, fun hlt => ?_⟩
  refine hne ?_
  rw [← hk]
  exact commutatorElement_eq_one_iff_commute.mpr
    ((commutatorElement_eq_one_iff_commute.mp hlt).zpow_right k)

theorem s16h_dc_triangular_card [Finite W] {L : Subgroup (MulAut W)} {p r : ℕ}
    (hp : p.Prime) (hE : IsElemAbelianOfRank p r ↥L) {s : ℕ}
    {Δ : Fin (r + 1) → Subgroup W} {v : Fin s → MulAut W} {i : Fin s → Fin (r + 1)}
    (hv : ∀ k, v k ∈ L)
    (hmem : ∀ k, i k ∈ s16h_dc_supp Δ (v k))
    (htri : ∀ k j, k < j → i k ∉ s16h_dc_supp Δ (v j)) :
    p ^ s ≤ Nat.card ↥(Subgroup.closure (Set.range v)) := by
  have hclos_le : Subgroup.closure (Set.range v) ≤ L :=
    (Subgroup.closure_le L).mpr (by rintro _ ⟨k, rfl⟩; exact hv k)
  let x : Fin s → ↥(Subgroup.closure (Set.range v)) := fun k =>
    ⟨v k, Subgroup.subset_closure ⟨k, rfl⟩⟩
  haveI hcomm : IsMulCommutative ↥(Subgroup.closure (Set.range v)) :=
    IsMulCommutative.of_comm fun a b => by
      refine Subtype.ext ?_
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      exact congrArg Subtype.val (s16h_dc_comm_of_elem hE
        (⟨(a : MulAut W), hclos_le a.2⟩ : ↥L) (⟨(b : MulAut W), hclos_le b.2⟩ : ↥L))
  have hxpow : ∀ k, (x k) ^ p = 1 := fun k => by
    apply Subtype.ext
    show (v k) ^ p = 1
    have h := s16h_dc_pow_eq_one_of_elem hE (⟨v k, hv k⟩ : ↥L)
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
        exact s16h_dc_pow_val_add hp (hxpow k) _ _ }
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
        · exact Subgroup.pow_mem _ (s16h_dc_cent_of_notMem_supp (htri k j hgt)) _
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
    have hdvd := s16h_dc_dvd_of_pow_mem_centSub hE hp (hv k) (hmem k) hcent
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

theorem s16h_dc_supp_not_singleton [Finite W] {A L : Subgroup (MulAut W)} {Wsub : Subgroup W}
    {p r : ℕ} (hp : p.Prime) (hE : IsElemAbelianOfRank p r ↥L)
    (hLn : ∀ g ∈ A ⊓ stabSub Wsub, L.map (MulAut.conj g).toMonoidHom = L)
    {Δ : Fin (r + 1) → Subgroup W}
    {σ : ↥(A ⊓ stabSub Wsub) →* Equiv.Perm (Fin (r + 1))}
    (hσsurj : Function.Surjective σ)
    (hσact : ∀ (g : ↥(A ⊓ stabSub Wsub)) (i : Fin (r + 1)),
      (Δ i).map (g : MulAut W).toMonoidHom = Δ (σ g i))
    {y : MulAut W} (hy : y ∈ L) {c : Fin (r + 1)} (hS : s16h_dc_supp Δ y = {c}) : False := by
  choose g hg using fun k : Fin (r + 1) => hσsurj (Equiv.swap c k)
  let z : Fin (r + 1) → MulAut W := fun k => (g k : MulAut W) * y * (g k : MulAut W)⁻¹
  have hzmem : ∀ k, z k ∈ L := by
    intro k
    have hconj : (MulAut.conj (g k : MulAut W)) y ∈ L := by
      rw [← hLn (g k : MulAut W) (g k).2]
      exact Subgroup.mem_map_of_mem _ hy
    simpa [z, MulAut.conj_apply] using hconj
  have hzsupp : ∀ k, s16h_dc_supp Δ (z k) = {k} := by
    intro k
    have h := s16h_dc_supp_conj (A := A) hσact (g k) y
    rw [hS, hg k] at h
    rw [show z k = (g k : MulAut W) * y * (g k : MulAut W)⁻¹ from rfl, h]
    rw [Set.image_singleton, Equiv.swap_apply_left]
  have htri : ∀ k j, k < j → k ∉ s16h_dc_supp Δ (z j) := by
    intro k j hkj
    rw [hzsupp j]
    simp [ne_of_lt hkj]
  have hcard := s16h_dc_triangular_card (L := L) (s := r + 1) (i := fun k => k) hp hE hzmem
    (fun k => by rw [hzsupp k]; simp) htri
  have hclos_le : Subgroup.closure (Set.range z) ≤ L :=
    (Subgroup.closure_le L).mpr (by rintro _ ⟨k, rfl⟩; exact hzmem k)
  have hleL : Nat.card ↥(Subgroup.closure (Set.range z)) ≤ Nat.card ↥L :=
    Subgroup.card_le_of_le hclos_le
  have hLcard : Nat.card ↥L = p ^ r := s16h_dc_card_of_elem hE
  have hlt : p ^ r < p ^ (r + 1) := Nat.pow_lt_pow_succ hp.one_lt
  have : p ^ (r + 1) ≤ p ^ r := le_trans hcard (le_trans hleL (le_of_eq hLcard))
  exact absurd this (not_le.mpr hlt)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
