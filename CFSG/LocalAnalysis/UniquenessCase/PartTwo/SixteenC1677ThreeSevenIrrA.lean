module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeSevenLines

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Two

variable {W : Type} [CommGroup W] [Finite W] {A L : Subgroup (MulAut W)}
  {Δ : Fin (2 + 1) → Subgroup W} {σ : ↥A →* Equiv.Perm (Fin (2 + 1))}

private theorem s168e3_seven_comm_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro a b
  exact e.injective (by rw [map_mul, map_mul, mul_comm])

private theorem s168e3_seven_pow_of_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) (x : X) : x ^ p = 1 := by
  obtain ⟨e⟩ := h
  apply e.injective
  rw [map_pow, map_one]
  apply Multiplicative.toAdd.injective
  rw [toAdd_pow, toAdd_one]
  funext i
  simp

private theorem s168e3_seven_card_elem {X : Type*} [Group X] {p n : ℕ}
    (h : IsElemAbelianOfRank p n X) : Nat.card X = p ^ n := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card X = Nat.card (Multiplicative (Fin n → ZMod p)) := Nat.card_congr e.toEquiv
  rw [h1, show Nat.card (Multiplicative (Fin n → ZMod p)) = Nat.card (Fin n → ZMod p) from rfl,
    Nat.card_fun]
  simp [Nat.card_eq_fintype_card, ZMod.card, Fintype.card_fin]

private theorem s168e3_seven_comm_mem (h : s16e_d3_Ctx A L 2 Δ σ) {a b : MulAut W}
    (ha : a ∈ L) (hb : b ∈ L) : a * b = b * a := by
  have h1 := s168e3_seven_comm_of_elem h.elem ⟨a, ha⟩ ⟨b, hb⟩
  simpa using h1

private theorem s168e3_seven_pow_mem (h : s16e_d3_Ctx A L 2 Δ σ) {a : MulAut W}
    (ha : a ∈ L) : a ^ 7 = 1 := by
  have h1 := s168e3_seven_pow_of_elem h.elem ⟨a, ha⟩
  simpa using h1

private theorem s168e3_seven_card_Ck (h : s16e_d3_Ctx A L 2 Δ σ) (k : Fin (2 + 1)) :
    Nat.card ↥(L ⊓ centSub (Δ k)) = 7 := by
  have h1 := s168e3_seven_card_line h k
  norm_num at h1
  exact h1

theorem s168e3_seven_inf_line (h : s16e_d3_Ctx A L 2 Δ σ) {U : Subgroup (MulAut W)}
    (hUL : U ≤ L) (hU7 : Nat.card U = 7)
    (hUA : ∀ g ∈ A, U.map (MulAut.conj g).toMonoidHom = U) (k : Fin (2 + 1)) :
    ∀ u ∈ U, u ∈ centSub (Δ k) → u = 1 := by
  intro u huU huC
  by_contra hu1
  have huL : u ∈ L := hUL huU
  have hpow : u ^ 7 = 1 := s168e3_seven_pow_mem h huL
  have horder : orderOf u = 7 := by
    have hdvd : orderOf u ∣ 7 := by
      have h1 : orderOf (⟨u, huU⟩ : ↥U) ∣ Nat.card ↥U := orderOf_dvd_natCard _
      rw [← orderOf_coe (⟨u, huU⟩ : ↥U), hU7] at h1
      exact h1
    rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with hh | hh
    · exact absurd (orderOf_eq_one_iff.mp hh) hu1
    · exact hh
  have hUgen : U = Subgroup.zpowers u := by
    have hle : Subgroup.zpowers u ≤ U := Subgroup.zpowers_le.mpr huU
    have hcard : Nat.card U ≤ Nat.card ↥(Subgroup.zpowers u) := by
      rw [Nat.card_zpowers, horder, hU7]
    exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
  have hUCk : U ≤ L ⊓ centSub (Δ k) := by
    rw [hUgen]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mpr ⟨huL, huC⟩)
  have hCk7 : Nat.card ↥(L ⊓ centSub (Δ k)) = 7 := s168e3_seven_card_Ck h k
  have hUeqCk : U = L ⊓ centSub (Δ k) := by
    refine Subgroup.eq_of_le_of_card_ge hUCk ?_
    rw [hCk7, hU7]
  obtain ⟨j, hjk⟩ : ∃ j : Fin (2 + 1), j ≠ k := by
    fin_cases k
    · exact ⟨1, by decide⟩
    · exact ⟨0, by decide⟩
    · exact ⟨0, by decide⟩
  obtain ⟨s, hs2, hσs⟩ := s168e3_seven_exists_sq h k j
  have hsk : σ s k = j := by rw [hσs, Equiv.swap_apply_left]
  have hconj : (s : MulAut W) * u * (s : MulAut W)⁻¹ ∈ L ⊓ centSub (Δ j) := by
    have h1 := s168e3_seven_conj_line h s (Subgroup.mem_inf.mpr ⟨huL, huC⟩)
    rwa [hsk] at h1
  have hconjU : (s : MulAut W) * u * (s : MulAut W)⁻¹ ∈ U := by
    have h1 : (MulAut.conj (s : MulAut W)).toMonoidHom u ∈
        U.map (MulAut.conj (s : MulAut W)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ huU
    rw [hUA (s : MulAut W) s.2] at h1
    simpa [MulAut.conj_apply] using h1
  have hconjCk : (s : MulAut W) * u * (s : MulAut W)⁻¹ ∈ L ⊓ centSub (Δ k) := by
    rw [← hUeqCk]
    exact hconjU
  have hx1 : (s : MulAut W) * u * (s : MulAut W)⁻¹ = 1 :=
    s168e3_seven_line_inf h (Ne.symm hjk) hconjCk (Subgroup.mem_inf.mp hconj).2
  have hu_eq : u = 1 := by
    have h2 := congrArg (fun t : MulAut W => (s : MulAut W)⁻¹ * t * (s : MulAut W)) hx1
    have h3 : (s : MulAut W)⁻¹ * ((s : MulAut W) * u * (s : MulAut W)⁻¹) *
        (s : MulAut W) = u := by group
    rw [h3] at h2
    simpa using h2
  exact hu1 hu_eq

theorem s168e3_seven_dec (h : s16e_d3_Ctx A L 2 Δ σ) {U : Subgroup (MulAut W)}
    (hUL : U ≤ L) (hU7 : Nat.card U = 7) {k : Fin (2 + 1)}
    (hUk : ∀ u ∈ U, u ∈ centSub (Δ k) → u = 1) :
    ∀ x ∈ L, ∃ u ∈ U, ∃ c ∈ L ⊓ centSub (Δ k), x = u * c := by
  have hCk7 : Nat.card ↥(L ⊓ centSub (Δ k)) = 7 := s168e3_seven_card_Ck h k
  have hL49 : Nat.card ↥L = 49 := by
    have h1 := s168e3_seven_card_elem h.elem
    norm_num at h1
    exact h1
  let f : ↥U × ↥(L ⊓ centSub (Δ k)) → ↥L := fun p =>
    ⟨(p.1 : MulAut W) * (p.2 : MulAut W),
      L.mul_mem (hUL p.1.2) (Subgroup.mem_inf.mp p.2.2).1⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨u₁, c₁⟩ ⟨u₂, c₂⟩ heq
    have hval : (u₁ : MulAut W) * (c₁ : MulAut W) = (u₂ : MulAut W) * (c₂ : MulAut W) := by
      simpa only [f] using congrArg (fun x : ↥L => (x : MulAut W)) heq
    have h3 : (u₂ : MulAut W)⁻¹ * (u₁ : MulAut W) * (c₁ : MulAut W) = (c₂ : MulAut W) := by
      calc (u₂ : MulAut W)⁻¹ * (u₁ : MulAut W) * (c₁ : MulAut W)
          = (u₂ : MulAut W)⁻¹ * ((u₁ : MulAut W) * (c₁ : MulAut W)) := by group
        _ = (u₂ : MulAut W)⁻¹ * ((u₂ : MulAut W) * (c₂ : MulAut W)) := by rw [hval]
        _ = (c₂ : MulAut W) := by group
    have hx_eq : (u₂ : MulAut W)⁻¹ * (u₁ : MulAut W) =
        (c₂ : MulAut W) * (c₁ : MulAut W)⁻¹ := by
      calc (u₂ : MulAut W)⁻¹ * (u₁ : MulAut W)
          = (u₂ : MulAut W)⁻¹ * (u₁ : MulAut W) *
              ((c₁ : MulAut W) * (c₁ : MulAut W)⁻¹) := by group
        _ = ((u₂ : MulAut W)⁻¹ * (u₁ : MulAut W) * (c₁ : MulAut W)) *
              (c₁ : MulAut W)⁻¹ := by group
        _ = (c₂ : MulAut W) * (c₁ : MulAut W)⁻¹ := by rw [h3]
    have hxU : (u₂ : MulAut W)⁻¹ * (u₁ : MulAut W) ∈ U :=
      U.mul_mem (U.inv_mem u₂.2) u₁.2
    have hxC : (u₂ : MulAut W)⁻¹ * (u₁ : MulAut W) ∈ L ⊓ centSub (Δ k) := by
      refine Subgroup.mem_inf.mpr ⟨L.mul_mem (L.inv_mem (hUL u₂.2)) (hUL u₁.2), ?_⟩
      rw [hx_eq]
      exact (centSub (Δ k)).mul_mem (Subgroup.mem_inf.mp c₂.2).2
        ((centSub (Δ k)).inv_mem (Subgroup.mem_inf.mp c₁.2).2)
    have hx1 : (u₂ : MulAut W)⁻¹ * (u₁ : MulAut W) = 1 :=
      hUk _ hxU (Subgroup.mem_inf.mp hxC).2
    have hu_eq_val : (u₁ : MulAut W) = (u₂ : MulAut W) := by
      calc (u₁ : MulAut W) = (u₂ : MulAut W) *
            ((u₂ : MulAut W)⁻¹ * (u₁ : MulAut W)) := by group
        _ = (u₂ : MulAut W) := by rw [hx1, mul_one]
    have hu_eq : u₁ = u₂ := Subtype.ext hu_eq_val
    have hc_eq_val : (c₁ : MulAut W) = (c₂ : MulAut W) := by
      have h2 := hval
      rw [hu_eq_val] at h2
      exact mul_left_cancel h2
    have hc_eq : c₁ = c₂ := Subtype.ext hc_eq_val
    exact Prod.ext hu_eq hc_eq
  have hcard : Nat.card (↥U × ↥(L ⊓ centSub (Δ k))) = Nat.card ↥L := by
    rw [Nat.card_prod, hU7, hCk7, hL49]
  have hf_bij : Function.Bijective f :=
    (Nat.bijective_iff_injective_and_card f).mpr ⟨hf_inj, hcard⟩
  intro x hxL
  obtain ⟨p, hp⟩ := hf_bij.2 ⟨x, hxL⟩
  refine ⟨p.1, p.1.2, p.2, p.2.2, ?_⟩
  have h1 := congrArg (fun z : ↥L => (z : MulAut W)) hp
  simpa only [f] using h1.symm

theorem s168e3_seven_cent_of_fix (h : s16e_d3_Ctx A L 2 Δ σ) {U : Subgroup (MulAut W)}
    (hUL : U ≤ L) (hUA : ∀ g ∈ A, U.map (MulAut.conj g).toMonoidHom = U) {k : Fin (2 + 1)}
    (hUk : ∀ u ∈ U, u ∈ centSub (Δ k) → u = 1) {s : ↥A}
    (hfix : ∀ x ∈ Δ k, (s : MulAut W) x = x) :
    ∀ u ∈ U, (s : MulAut W) * u * (s : MulAut W)⁻¹ = u := by
  intro u huU
  have huL : u ∈ L := hUL huU
  have hstab : u ∈ stabSub (Δ k) := by
    have h1 := s16e_d3_le_ker h huL
    exact (Subgroup.mem_iInf.mp (Subgroup.mem_inf.mp h1).2) k
  have hsuU : (s : MulAut W) * u * (s : MulAut W)⁻¹ ∈ U := by
    have h1 : (MulAut.conj (s : MulAut W)).toMonoidHom u ∈
        U.map (MulAut.conj (s : MulAut W)).toMonoidHom :=
      Subgroup.mem_map_of_mem _ huU
    rw [hUA (s : MulAut W) s.2] at h1
    simpa [MulAut.conj_apply] using h1
  have hdU : (s : MulAut W) * u * (s : MulAut W)⁻¹ * u⁻¹ ∈ U :=
    U.mul_mem hsuU (U.inv_mem huU)
  have hdC : (s : MulAut W) * u * (s : MulAut W)⁻¹ * u⁻¹ ∈ centSub (Δ k) := by
    intro x hx
    have hux : u⁻¹ x ∈ Δ k :=
      (mem_stabSub.mp ((stabSub (Δ k)).inv_mem hstab) x).2 hx
    have hs_inv_x : (s : MulAut W)⁻¹ x = x := by
      have h2 := congrArg (fun y => (s : MulAut W)⁻¹ y) (hfix x hx)
      simpa using h2.symm
    have hs_inv_ux : (s : MulAut W)⁻¹ (u⁻¹ x) = u⁻¹ x := by
      have h2 := congrArg (fun y => (s : MulAut W)⁻¹ y) (hfix (u⁻¹ x) hux)
      simpa using h2.symm
    simp only [MulAut.mul_apply]
    rw [hs_inv_ux]
    simp [hfix x hx]
  have hd1 : (s : MulAut W) * u * (s : MulAut W)⁻¹ * u⁻¹ = 1 :=
    hUk _ hdU hdC
  have h2 := congrArg (fun t : MulAut W => t * u) hd1
  simpa using h2

theorem s168e3_seven_inv_line (h : s16e_d3_Ctx A L 2 Δ σ) {U : Subgroup (MulAut W)}
    {k : Fin (2 + 1)} (hdec : ∀ x ∈ L, ∃ u ∈ U, ∃ c ∈ L ⊓ centSub (Δ k), x = u * c) {s : ↥A}
    (hs : s ^ 2 = 1)
    (hsU : ∀ u ∈ U, (s : MulAut W) * u * (s : MulAut W)⁻¹ = u) {i j : Fin (2 + 1)}
    (hij : i ≠ j) (hk : σ s k = k) (hi : σ s i = j) :
    ∀ c ∈ L ⊓ centSub (Δ k), (s : MulAut W) * c * (s : MulAut W)⁻¹ = c⁻¹ := by
  intro c hc
  obtain ⟨hcL, hcC⟩ := Subgroup.mem_inf.mp hc
  have hsval : (s : MulAut W) * (s : MulAut W) = 1 := by
    simpa [pow_two] using congrArg (fun t : ↥A => (t : MulAut W)) hs
  have hsinv2 : (s : MulAut W)⁻¹ * (s : MulAut W)⁻¹ = 1 := by
    rw [← mul_inv_rev, hsval, inv_one]
  have hwc : (s : MulAut W) * c * (s : MulAut W)⁻¹ ∈ L ⊓ centSub (Δ k) := by
    have h1 := s168e3_seven_conj_line h s hc
    rwa [hk] at h1
  have hwcL : (s : MulAut W) * c * (s : MulAut W)⁻¹ ∈ L := (Subgroup.mem_inf.mp hwc).1
  have hwcC : (s : MulAut W) * c * (s : MulAut W)⁻¹ ∈ centSub (Δ k) :=
    (Subgroup.mem_inf.mp hwc).2
  let d : MulAut W := c * ((s : MulAut W) * c * (s : MulAut W)⁻¹)
  have hdL : d ∈ L := by
    simp only [d]
    exact L.mul_mem hcL hwcL
  have hdC : d ∈ centSub (Δ k) := by
    simp only [d]
    exact (centSub (Δ k)).mul_mem hcC hwcC
  have hdCk : d ∈ L ⊓ centSub (Δ k) := Subgroup.mem_inf.mpr ⟨hdL, hdC⟩
  have hsd : (s : MulAut W) * d * (s : MulAut W)⁻¹ = d := by
    have hcomm : ((s : MulAut W) * c * (s : MulAut W)⁻¹) * c =
        c * ((s : MulAut W) * c * (s : MulAut W)⁻¹) :=
      s168e3_seven_comm_mem h hwcL hcL
    have hconj : (s : MulAut W) * ((s : MulAut W) * c * (s : MulAut W)⁻¹) *
        (s : MulAut W)⁻¹ = c := by
      calc (s : MulAut W) * ((s : MulAut W) * c * (s : MulAut W)⁻¹) * (s : MulAut W)⁻¹
          = ((s : MulAut W) * (s : MulAut W)) * c *
              ((s : MulAut W)⁻¹ * (s : MulAut W)⁻¹) := by group
        _ = c := by rw [hsval, hsinv2]; group
    simp only [d]
    calc (s : MulAut W) * (c * ((s : MulAut W) * c * (s : MulAut W)⁻¹)) * (s : MulAut W)⁻¹
        = ((s : MulAut W) * c * (s : MulAut W)⁻¹) *
            ((s : MulAut W) * ((s : MulAut W) * c * (s : MulAut W)⁻¹) *
              (s : MulAut W)⁻¹) := by group
      _ = ((s : MulAut W) * c * (s : MulAut W)⁻¹) * c := by rw [hconj]
      _ = c * ((s : MulAut W) * c * (s : MulAut W)⁻¹) := hcomm
  rcases eq_or_ne d 1 with hd1 | hdne
  · have hx : c * ((s : MulAut W) * c * (s : MulAut W)⁻¹) = 1 := hd1
    have hthis : (s : MulAut W) * c * (s : MulAut W)⁻¹ = c⁻¹ := by
      have h2 := congrArg (fun t : MulAut W => c⁻¹ * t) hx
      simpa [mul_assoc] using h2
    exact hthis
  · exfalso
    have hCk7 : Nat.card ↥(L ⊓ centSub (Δ k)) = 7 := s168e3_seven_card_Ck h k
    have hdvd : orderOf d ∣ 7 := by
      have h1 : orderOf (⟨d, hdCk⟩ : ↥(L ⊓ centSub (Δ k))) ∣
          Nat.card ↥(L ⊓ centSub (Δ k)) := orderOf_dvd_natCard _
      rw [← orderOf_coe (⟨d, hdCk⟩ : ↥(L ⊓ centSub (Δ k))), hCk7] at h1
      exact h1
    have horder : orderOf d = 7 := by
      rcases (Nat.dvd_prime Nat.prime_seven).mp hdvd with hh | hh
      · exact absurd (orderOf_eq_one_iff.mp hh) hdne
      · exact hh
    have hCkeq : L ⊓ centSub (Δ k) = Subgroup.zpowers d := by
      have hle : Subgroup.zpowers d ≤ L ⊓ centSub (Δ k) := Subgroup.zpowers_le.mpr hdCk
      have hcard : Nat.card ↥(L ⊓ centSub (Δ k)) ≤ Nat.card ↥(Subgroup.zpowers d) := by
        rw [hCk7, Nat.card_zpowers, horder]
      exact (Subgroup.eq_of_le_of_card_ge hle hcard).symm
    have hdcomm : d ∈ Subgroup.centralizer ({(s : MulAut W)} : Set (MulAut W)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h1 h1mem
      rw [Set.mem_singleton_iff] at h1mem
      rw [h1mem]
      calc (s : MulAut W) * d = (s : MulAut W) * d * (s : MulAut W)⁻¹ * (s : MulAut W) := by
            group
        _ = d * (s : MulAut W) := by rw [hsd]
    have hCkcent : ∀ x ∈ L ⊓ centSub (Δ k),
        (s : MulAut W) * x * (s : MulAut W)⁻¹ = x := by
      intro x hx
      have hx' : x ∈ Subgroup.zpowers d := by rw [← hCkeq]; exact hx
      have hx'' : x ∈ Subgroup.centralizer ({(s : MulAut W)} : Set (MulAut W)) :=
        Subgroup.zpowers_le.mpr hdcomm hx'
      have hcomm := (Subgroup.mem_centralizer_iff.mp hx'') (s : MulAut W)
        (Set.mem_singleton _)
      calc (s : MulAut W) * x * (s : MulAut W)⁻¹ =
            (x * (s : MulAut W)) * (s : MulAut W)⁻¹ := by rw [hcomm]
        _ = x := by group
    have hcentL : ∀ x ∈ L, (s : MulAut W) * x * (s : MulAut W)⁻¹ = x := by
      intro x hx
      obtain ⟨u, huU, c', hc'Ck, hx_eq⟩ := hdec x hx
      rw [hx_eq]
      calc (s : MulAut W) * (u * c') * (s : MulAut W)⁻¹
          = ((s : MulAut W) * u * (s : MulAut W)⁻¹) *
              ((s : MulAut W) * c' * (s : MulAut W)⁻¹) := by group
        _ = u * c' := by simp [hsU u huU, hCkcent c' hc'Ck]
    have hleCij : L ⊓ centSub (Δ i) ≤ L ⊓ centSub (Δ j) := by
      intro x hx
      have hx' := s168e3_seven_conj_line h s hx
      rw [hi] at hx'
      rwa [hcentL x (Subgroup.mem_inf.mp hx).1] at hx'
    have hCi_bot : L ⊓ centSub (Δ i) = ⊥ := by
      refine le_antisymm ?_ bot_le
      intro x hx
      have hxj : x ∈ L ⊓ centSub (Δ j) := hleCij hx
      rw [Subgroup.mem_bot]
      exact s168e3_seven_line_inf h hij hx (Subgroup.mem_inf.mp hxj).2
    have hcard_i : Nat.card ↥(L ⊓ centSub (Δ i)) = 7 := s168e3_seven_card_Ck h i
    have hcard_one : Nat.card ↥(L ⊓ centSub (Δ i)) = 1 := by
      rw [hCi_bot, Subgroup.card_bot]
    omega

end Two

theorem s168e3_seven_lines_false {H : Type*} [Group H] {L U C₀ C₁ C₂ : Subgroup H}
    (hLc : ∀ x ∈ L, ∀ y ∈ L, x * y = y * x) (h7 : ∀ x ∈ L, x ^ 7 = 1)
    (hUL : U ≤ L) (hC₀L : C₀ ≤ L) (hC₂L : C₂ ≤ L)
    (hdec : ∀ x ∈ L, ∃ u ∈ U, ∃ c ∈ C₂, x = u * c)
    (hUC₁ : ∀ x ∈ U, x ∈ C₁ → x = 1) (hC₀₂ : ∀ x ∈ C₀, x ∈ C₂ → x = 1)
    {c₀ : H} (hc₀ : c₀ ∈ C₀) (hc₀1 : c₀ ≠ 1)
    {s s' : H} (hsU : ∀ u ∈ U, s * u * s⁻¹ = u) (hsC₂ : ∀ c ∈ C₂, s * c * s⁻¹ = c⁻¹)
    (hsC₀ : s * c₀ * s⁻¹ ∈ C₁)
    (hs'U : ∀ u ∈ U, s' * u * s'⁻¹ = u) (hs'c₀ : s' * c₀ * s'⁻¹ = c₀⁻¹)
    (hs'C₂ : ∀ c ∈ C₂, s' * c * s'⁻¹ ∈ C₁) : False := by
  obtain ⟨u, huU, c₂, hc₂, hc₀eq⟩ := hdec c₀ (hC₀L hc₀)
  have huL : u ∈ L := hUL huU
  have hc₂L : c₂ ∈ L := hC₂L hc₂
  have hsc₀ : s * c₀ * s⁻¹ = u * c₂⁻¹ := by
    rw [hc₀eq]
    calc s * (u * c₂) * s⁻¹ = (s * u * s⁻¹) * (s * c₂ * s⁻¹) := by group
      _ = u * c₂⁻¹ := by rw [hsU u huU, hsC₂ c₂ hc₂]
  have huc₂C₁ : u * c₂⁻¹ ∈ C₁ := by rw [← hsc₀]; exact hsC₀
  have h1 : s' * c₀ * s'⁻¹ = u * (s' * c₂ * s'⁻¹) := by
    rw [hc₀eq]
    calc s' * (u * c₂) * s'⁻¹ = (s' * u * s'⁻¹) * (s' * c₂ * s'⁻¹) := by group
      _ = u * (s' * c₂ * s'⁻¹) := by rw [hs'U u huU]
  have h2 : c₀⁻¹ = u⁻¹ * c₂⁻¹ := by
    rw [hc₀eq]
    calc (u * c₂)⁻¹ = c₂⁻¹ * u⁻¹ := mul_inv_rev u c₂
      _ = u⁻¹ * c₂⁻¹ := hLc c₂⁻¹ (L.inv_mem hc₂L) u⁻¹ (L.inv_mem huL)
  have hX_eq : s' * c₂ * s'⁻¹ = u⁻¹ * (u⁻¹ * c₂⁻¹) := by
    have h3 : u * (s' * c₂ * s'⁻¹) = u⁻¹ * c₂⁻¹ := by
      rw [← h1, hs'c₀, h2]
    calc s' * c₂ * s'⁻¹ = u⁻¹ * (u * (s' * c₂ * s'⁻¹)) := by group
      _ = u⁻¹ * (u⁻¹ * c₂⁻¹) := by rw [h3]
  have hXC₁ : u⁻¹ * (u⁻¹ * c₂⁻¹) ∈ C₁ := by rw [← hX_eq]; exact hs'C₂ c₂ hc₂
  have hu3C₁ : u ^ 3 ∈ C₁ := by
    have hprod : (u * c₂⁻¹) * (u⁻¹ * (u⁻¹ * c₂⁻¹))⁻¹ = u ^ 3 := by group
    rw [← hprod]
    exact C₁.mul_mem huc₂C₁ (C₁.inv_mem hXC₁)
  have hu3 : u ^ 3 = 1 := hUC₁ (u ^ 3) (U.pow_mem huU 3) hu3C₁
  have hu7 : u ^ 7 = 1 := h7 u huL
  have hu1 : u = 1 := by
    have h1 : u ^ 7 = u := by
      calc u ^ 7 = (u ^ 3) ^ 2 * u := by group
        _ = u := by rw [hu3]; group
    rw [hu7] at h1
    exact h1.symm
  have hc₂eq : c₀ = c₂ := by rw [hc₀eq, hu1, one_mul]
  have hc₀C₂ : c₀ ∈ C₂ := by rw [hc₂eq]; exact hc₂
  exact hc₀1 (hC₀₂ c₀ hc₀ hc₀C₂)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
