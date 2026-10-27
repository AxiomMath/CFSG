module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermBase

public section

namespace CFSG.StandardType.SpJoin

variable {n p : ℕ}

private def nontrivialCoordinates (a : Fin n → Multiplicative (ZMod p)) : Finset (Fin n) :=
  Finset.univ.filter fun t => a t ≠ 1

private def swapCandidates (i : Fin n) (a : Fin n → Multiplicative (ZMod p)) : Finset (Fin n) :=
  insert i (Finset.univ.filter fun c => c ∉ nontrivialCoordinates a)

private def signedVector (a : Fin n → Multiplicative (ZMod p)) (σ : Equiv.Perm (Fin n))
    (T : Finset (Fin n)) : Fin n → Multiplicative (ZMod p) :=
  fun t => if t ∈ T then (a (σ.symm t))⁻¹ else a (σ.symm t)

private theorem signedVector_mem_orbit
    {H : Subgroup (Equiv.Perm (Fin n → Multiplicative (ZMod p)))}
    (hperm : ∀ σ : Equiv.Perm (Fin n), coordPerm n p σ ∈ H)
    (hinv : ∀ i : Fin n, coordInv n p i ∈ H)
    (a : Fin n → Multiplicative (ZMod p)) (σ : Equiv.Perm (Fin n)) (T : Finset (Fin n)) :
    signedVector a σ T ∈
      (fun h : Equiv.Perm (Fin n → Multiplicative (ZMod p)) => h a) '' (H : Set _) := by
  induction T using Finset.induction_on with
  | empty =>
      refine ⟨coordPerm n p σ, hperm σ, ?_⟩
      funext t
      simp [signedVector]
  | insert t₀ T ht₀ ih =>
      obtain ⟨h, hhH, hh⟩ := ih
      have hh' : h a = signedVector a σ T := hh
      refine ⟨coordInv n p t₀ * h, H.mul_mem (hinv t₀) hhH, ?_⟩
      funext t
      change (coordInv n p t₀ * h) a t = signedVector a σ (insert t₀ T) t
      rw [Equiv.Perm.mul_apply, hh', coordInv_apply]
      by_cases ht : t = t₀
      · rw [ht]
        simp [signedVector, Function.update_apply, ht₀]
      · rw [Function.update_of_ne ht]
        simp [signedVector, ht, ht₀]

private theorem mem_image_iff_symm_mem {α : Type*} [DecidableEq α] (σ : Equiv.Perm α)
    (U : Finset α) (x : α) : x ∈ U.image σ ↔ σ.symm x ∈ U := by
  rw [Finset.mem_image]
  constructor
  · rintro ⟨u, hu, hux⟩
    rwa [← hux, Equiv.symm_apply_apply]
  · intro h
    exact ⟨σ.symm x, h, Equiv.apply_symm_apply σ x⟩

private theorem signedVector_apply_swap_self (a : Fin n → Multiplicative (ZMod p))
    (σ : Equiv.Perm (Fin n)) (U : Finset (Fin n)) (u : Fin n) :
    signedVector a σ (U.image σ) (σ u) = if u ∈ U then (a u)⁻¹ else a u := by
  simp only [signedVector, mem_image_iff_symm_mem, Equiv.symm_apply_apply]

private theorem ite_inv_eq_ite_inv_iff {G : Type*} [Group G] {g : G} (hg : g⁻¹ ≠ g)
    {P Q : Prop} [Decidable P] [Decidable Q] :
    (if P then g⁻¹ else g) = (if Q then g⁻¹ else g) ↔ (P ↔ Q) := by
  have hg' : g ≠ g⁻¹ := fun h => hg h.symm
  by_cases hP : P <;> by_cases hQ : Q <;> simp [hP, hQ, hg, hg']

private theorem inv_ne_self_of_ne_one (hp : p.Prime) (hp2 : p ≠ 2)
    {g : Multiplicative (ZMod p)} (hg : g ≠ 1) : g⁻¹ ≠ g := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  intro h
  have hg2 : g ^ 2 = 1 := by
    have hmul : g * g = g * g⁻¹ := by rw [h]
    rw [pow_two, hmul, mul_inv_cancel]
  have hdvd2 : orderOf g ∣ 2 := orderOf_dvd_iff_pow_eq_one.mpr hg2
  have hdvd_p : orderOf g ∣ p := by
    have := orderOf_dvd_card (x := g)
    simpa [ZMod.card] using this
  have hcop : Nat.Coprime 2 p := by
    rw [Nat.coprime_comm]
    exact Nat.coprime_two_right.mpr (hp.odd_of_ne_two hp2)
  have hgd : Nat.gcd 2 p = 1 := Nat.coprime_iff_gcd_eq_one.mp hcop
  have hone : orderOf g ∣ 1 := by
    rw [← hgd]
    exact Nat.dvd_gcd hdvd2 hdvd_p
  exact hg (orderOf_eq_one_iff.mp (Nat.dvd_one.mp hone))

private theorem eq_of_mem_image_swap {S : Finset (Fin n)} {i c c' : Fin n}
    (hc : c ∈ insert i (Finset.univ.filter fun x => x ∉ S))
    (hc' : c' ∈ insert i (Finset.univ.filter fun x => x ∉ S))
    (hmem : c ∈ S.image (Equiv.swap i c')) : c = c' := by
  by_contra hne
  have hSc : Equiv.swap i c' c ∈ S := by
    have := (mem_image_iff_symm_mem (Equiv.swap i c') S c).mp hmem
    simpa [Equiv.symm_swap] using this
  rcases Finset.mem_insert.mp hc with hci | hcf
  · have hc'S : c' ∈ S := by simpa [hci] using hSc
    rcases Finset.mem_insert.mp hc' with hc'i | hc'f
    · exact hne (hci.trans hc'i.symm)
    · exact (Finset.mem_filter.mp hc'f).2 hc'S
  · have hcS : c ∉ S := (Finset.mem_filter.mp hcf).2
    rcases Finset.mem_insert.mp hc' with hc'i | hc'f
    · have hswap : Equiv.swap i c' c = c := by simp [hc'i]
      exact hcS (hswap ▸ hSc)
    · have hc'S : c' ∉ S := (Finset.mem_filter.mp hc'f).2
      by_cases hci : c = i
      · exact hc'S (by simpa [hci] using hSc)
      · have hswap : Equiv.swap i c' c = c := Equiv.swap_apply_of_ne_of_ne hci hne
        exact hcS (hswap ▸ hSc)

private theorem signedVector_swap_injOn (hp : p.Prime) (hp2 : p ≠ 2)
    (a : Fin n → Multiplicative (ZMod p)) {i : Fin n} (hi : a i ≠ 1) :
    Set.InjOn (fun x : Fin n × Finset (Fin n) =>
        signedVector a (Equiv.swap i x.1) (x.2.image (Equiv.swap i x.1)))
      ↑(swapCandidates i a ×ˢ (nontrivialCoordinates a).powerset) := by
  classical
  rintro ⟨c, U⟩ hx ⟨c', U'⟩ hy hxy
  have hxD : (c, U) ∈ swapCandidates i a ×ˢ (nontrivialCoordinates a).powerset :=
    Finset.mem_coe.mp hx
  have hyD : (c', U') ∈ swapCandidates i a ×ˢ (nontrivialCoordinates a).powerset :=
    Finset.mem_coe.mp hy
  obtain ⟨hc, hUSpow⟩ := Finset.mem_product.mp hxD
  obtain ⟨hc', hU'Spow⟩ := Finset.mem_product.mp hyD
  have hUS : U ⊆ nontrivialCoordinates a := Finset.mem_powerset.mp hUSpow
  have hU'S : U' ⊆ nontrivialCoordinates a := Finset.mem_powerset.mp hU'Spow
  simp only [swapCandidates] at hc hc'
  have hxy' : signedVector a (Equiv.swap i c) (U.image (Equiv.swap i c))
      = signedVector a (Equiv.swap i c') (U'.image (Equiv.swap i c')) := hxy
  have hxval : signedVector a (Equiv.swap i c) (U.image (Equiv.swap i c)) c ≠ 1 := by
    have hsymm : (Equiv.swap i c).symm c = i := by
      rw [Equiv.symm_swap, Equiv.swap_apply_right]
    simp only [signedVector, hsymm]
    split <;> simp [inv_eq_one, hi]
  have hyval : signedVector a (Equiv.swap i c') (U'.image (Equiv.swap i c')) c ≠ 1 := by
    rw [← hxy']; exact hxval
  have hmem' : (Equiv.swap i c').symm c ∈ nontrivialCoordinates a := by
    rw [nontrivialCoordinates, Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    have hval := hyval
    simp only [signedVector] at hval
    by_cases hcond : c ∈ U'.image (Equiv.swap i c')
    · rw [if_pos hcond] at hval
      simpa [inv_eq_one] using hval
    · rw [if_neg hcond] at hval
      exact hval
  have hmem : c ∈ (nontrivialCoordinates a).image (Equiv.swap i c') :=
    (mem_image_iff_symm_mem (Equiv.swap i c') _ c).mpr hmem'
  have hcc : c = c' := eq_of_mem_image_swap hc hc' hmem
  rw [← hcc] at hxy'
  have hUU : U = U' := by
    apply Finset.ext
    intro u
    by_cases hu : u ∈ nontrivialCoordinates a
    · have hval : (if u ∈ U then (a u)⁻¹ else a u) = (if u ∈ U' then (a u)⁻¹ else a u) := by
        have := congrFun hxy' (Equiv.swap i c u)
        rwa [signedVector_apply_swap_self a (Equiv.swap i c) U u,
             signedVector_apply_swap_self a (Equiv.swap i c) U' u] at this
      exact (ite_inv_eq_ite_inv_iff
        (inv_ne_self_of_ne_one hp hp2 (by simpa [nontrivialCoordinates] using hu))).mp hval
    · have huU : u ∉ U := fun h => hu (hUS h)
      have huU' : u ∉ U' := fun h => hu (hU'S h)
      simp [huU, huU']
  rw [hcc, hUU]

private theorem two_mul_add_two_le_two_pow (s : ℕ) (hs : 3 ≤ s) : 2 * s + 2 ≤ 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        2 * (s + 1) + 2 = 2 * s + 4 := by ring
        _ ≤ 4 * s + 4 := by omega
        _ = 2 * (2 * s + 2) := by ring
        _ ≤ 2 * 2 ^ s := by linarith
        _ = 2 ^ (s + 1) := by rw [pow_succ]; ring

private theorem two_mul_add_two_lt_two_pow (s : ℕ) (hs : 4 ≤ s) : 2 * s + 2 < 2 ^ s := by
  induction s, hs using Nat.le_induction with
  | base => norm_num
  | succ s hs ih =>
      calc
        2 * (s + 1) + 2 = 2 * s + 4 := by ring
        _ < 4 * s + 4 := by omega
        _ = 2 * (2 * s + 2) := by ring
        _ < 2 * 2 ^ s := by linarith
        _ = 2 ^ (s + 1) := by rw [pow_succ]; ring

private theorem two_mul_add_two_lt_mul_two_pow (n s : ℕ) (hs : 2 ≤ s) (hsn : s ≤ n) (hn : 4 ≤ n) :
    2 * n + 2 < (n - s + 1) * 2 ^ s := by
  rcases Nat.eq_or_lt_of_le hs with rfl | hs3
  · have hsub : n - 2 + 1 = n - 1 := by omega
    rw [hsub, show (2 : ℕ) ^ 2 = 4 by norm_num]
    omega
  · have hpow : 2 * s + 2 ≤ 2 ^ s := two_mul_add_two_le_two_pow s (by omega)
    rcases Nat.eq_or_lt_of_le (show 1 ≤ n - s + 1 by omega) with h1 | h2
    · have hsn' : s = n := by omega
      have hle : (n - s + 1) * 2 ^ s = 2 ^ n := by
        rw [← hsn']
        simp
      rw [hle]
      exact two_mul_add_two_lt_two_pow n hn
    · set r : ℕ := n - s + 1 with hrdef
      have hr : 2 ≤ r := by omega
      have hn_eq : 2 * n + 2 = 2 * s + 2 * r := by omega
      have hmain : 2 * s + 2 * r < r * (2 * s + 2) := by nlinarith [hs, hr]
      have hmul : r * (2 * s + 2) ≤ r * 2 ^ s := Nat.mul_le_mul_left _ hpow
      rw [hn_eq]
      exact lt_of_lt_of_le hmain hmul

theorem two_mul_add_two_lt_ncard_image
    {H : Subgroup (Equiv.Perm (Fin n → Multiplicative (ZMod p)))} (hp : p.Prime) (hp2 : p ≠ 2)
    (hn : 4 ≤ n) (hperm : ∀ σ : Equiv.Perm (Fin n), coordPerm n p σ ∈ H)
    (hinv : ∀ i : Fin n, coordInv n p i ∈ H) {a : Fin n → Multiplicative (ZMod p)}
    {i j : Fin n} (hij : i ≠ j) (hi : a i ≠ 1) (hj : a j ≠ 1) :
    2 * n + 2 < Set.ncard
      ((fun h : Equiv.Perm (Fin n → Multiplicative (ZMod p)) => h a) '' (H : Set _)) := by
  classical
  haveI : NeZero p := ⟨hp.ne_zero⟩
  set φ : Fin n × Finset (Fin n) → (Fin n → Multiplicative (ZMod p)) :=
    fun x => signedVector a (Equiv.swap i x.1) (x.2.image (Equiv.swap i x.1)) with hφ
  set D : Finset (Fin n × Finset (Fin n)) :=
    swapCandidates i a ×ˢ (nontrivialCoordinates a).powerset with hD
  have hiS : i ∈ nontrivialCoordinates a := by
    simpa [nontrivialCoordinates] using hi
  have hjS : j ∈ nontrivialCoordinates a := by
    simpa [nontrivialCoordinates] using hj
  have hpair : ({i, j} : Finset (Fin n)) ⊆ nontrivialCoordinates a := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rcases hx with rfl | rfl
    · exact hiS
    · exact hjS
  have hs2 : 2 ≤ (nontrivialCoordinates a).card := by
    have := Finset.card_le_card hpair
    rwa [Finset.card_pair_eq_two_iff.mpr hij] at this
  have hsn : (nontrivialCoordinates a).card ≤ n := by
    simpa using (nontrivialCoordinates a).card_le_univ
  have hiC : i ∉ Finset.univ.filter (fun c : Fin n => c ∉ nontrivialCoordinates a) := by
    simp [hiS]
  have hfilter : (Finset.univ.filter (fun c : Fin n => c ∉ nontrivialCoordinates a)).card
      = n - (nontrivialCoordinates a).card := by
    have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin n)))
      (p := fun c : Fin n => c ∉ nontrivialCoordinates a)
    have huniv : (Finset.univ.filter (fun c : Fin n => ¬ (c ∉ nontrivialCoordinates a)))
        = nontrivialCoordinates a := by
      ext c; simp
    rw [huniv, Finset.card_univ, Fintype.card_fin] at h
    omega
  have hCcard : (swapCandidates i a).card = n - (nontrivialCoordinates a).card + 1 := by
    unfold swapCandidates
    rw [Finset.card_insert_of_notMem hiC, hfilter]
  have hDcard : D.card
      = (n - (nontrivialCoordinates a).card + 1) * 2 ^ (nontrivialCoordinates a).card := by
    rw [hD, Finset.card_product, hCcard, Finset.card_powerset]
  have hInj : Set.InjOn φ ↑D := by
    rw [hD, hφ]
    exact signedVector_swap_injOn hp hp2 a hi
  have hDimg : (D.image φ).card
      = (n - (nontrivialCoordinates a).card + 1) * 2 ^ (nontrivialCoordinates a).card := by
    rw [Finset.card_image_of_injOn hInj, hDcard]
  have hmap : ∀ x ∈ D, φ x ∈
      (fun h : Equiv.Perm (Fin n → Multiplicative (ZMod p)) => h a) '' (H : Set _) := by
    intro x hx
    rw [hD] at hx
    simp only [Finset.mem_product, Finset.mem_powerset] at hx
    rw [hφ]
    exact signedVector_mem_orbit hperm hinv a (Equiv.swap i x.1) (x.2.image (Equiv.swap i x.1))
  have hsubset : (↑(D.image φ) : Set (Fin n → Multiplicative (ZMod p))) ⊆
      (fun h : Equiv.Perm (Fin n → Multiplicative (ZMod p)) => h a) '' (H : Set _) := by
    intro v hv
    simp only [Finset.mem_coe, Finset.mem_image] at hv
    obtain ⟨x, hxD, rfl⟩ := hv
    exact hmap x hxD
  have hHfin : (H : Set (Equiv.Perm (Fin n → Multiplicative (ZMod p)))).Finite :=
    Set.finite_univ.subset (Set.subset_univ _)
  have hOrbfin : ((fun h : Equiv.Perm (Fin n → Multiplicative (ZMod p)) => h a) '' (H : Set _)).Finite :=
    hHfin.image _
  have hbound : (D.image φ).card ≤
      Set.ncard ((fun h : Equiv.Perm (Fin n → Multiplicative (ZMod p)) => h a) '' (H : Set _)) := by
    rw [← Set.ncard_coe_finset (D.image φ)]
    exact Set.ncard_le_ncard hsubset hOrbfin
  have harith : 2 * n + 2
      < (n - (nontrivialCoordinates a).card + 1) * 2 ^ (nontrivialCoordinates a).card :=
    two_mul_add_two_lt_mul_two_pow n (nontrivialCoordinates a).card hs2 hsn hn
  calc
    2 * n + 2 < (n - (nontrivialCoordinates a).card + 1) * 2 ^ (nontrivialCoordinates a).card :=
      harith
    _ = (D.image φ).card := hDimg.symm
    _ ≤ Set.ncard ((fun h : Equiv.Perm (Fin n → Multiplicative (ZMod p)) => h a) '' (H : Set _)) :=
      hbound

end CFSG.StandardType.SpJoin
