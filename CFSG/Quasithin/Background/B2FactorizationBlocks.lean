module

public import CFSG.Quasithin.Background.B1Solvable
public import CFSG.Quasithin.Background.B2FactorizationOffender

public section

namespace CFSG.Quasithin

variable {W : Type*} [CommGroup W]

namespace IsTransvectionBlocks

section Decomp

variable [Finite W] {J : Subgroup (MulAut W)} {𝓗 : Finset (Subgroup (MulAut W))}

omit [Finite W] in
theorem fixV_sup_commSub (hb : IsTransvectionBlocks J 𝓗) {L : Subgroup (MulAut W)}
    (hL : L ∈ 𝓗) : fixV L ⊔ commSub (⊤ : Subgroup W) L = ⊤ := by
  obtain ⟨C, -, hCsup, hC⟩ := hb.exists_compl L hL
  have hCle : C ≤ fixV L := fun c hc g hg => hC g hg c hc
  exact top_le_iff.1 (hCsup.symm.le.trans (sup_le_sup_right hCle _))

theorem decomp (hW : ∀ w : W, w ^ 2 = 1) (hb : IsTransvectionBlocks J 𝓗)
    (s : Finset (Subgroup (MulAut W))) (hs : s ⊆ 𝓗) :
    fixV (⨆ L ∈ s, L) ⊔ ⨆ L ∈ s, commSub (⊤ : Subgroup W) L = ⊤ ∧
      fixV (⨆ L ∈ s, L) ⊓ ⨆ L ∈ s, commSub (⊤ : Subgroup W) L = ⊥ := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp [B1.fixV_bot]
  | insert a s ha ih =>
    have haH : a ∈ 𝓗 := hs (Finset.mem_insert_self a s)
    obtain ⟨ih1, ih2⟩ := ih ((Finset.subset_insert a s).trans hs)
    rw [Finset.iSup_insert, Finset.iSup_insert, B1.fixV_sup]
    have hWs : (⨆ L ∈ s, commSub (⊤ : Subgroup W) L) ≤ fixV a := by
      refine iSup₂_le fun L hL u hu g hg => ?_
      have hLa : L ≠ a := fun h => ha (h ▸ hL)
      exact hb.triv a haH L (hs (Finset.mem_insert_of_mem hL)) (Ne.symm hLa) g hg u hu
    have hA := hb.fixV_sup_commSub haH
    have hB := hb.fixV_inf_commSub hW haH
    have h1 : fixV a = (⨆ L ∈ s, commSub (⊤ : Subgroup W) L) ⊔
        (fixV (⨆ L ∈ s, L) ⊓ fixV a) := by
      have h := sup_inf_assoc_of_le (fixV (⨆ L ∈ s, L)) hWs
      rw [sup_comm (⨆ L ∈ s, commSub (⊤ : Subgroup W) L) (fixV (⨆ L ∈ s, L)), ih1,
        top_inf_eq] at h
      exact h
    have h2 : (commSub (⊤ : Subgroup W) a ⊔ ⨆ L ∈ s, commSub (⊤ : Subgroup W) L) ⊓ fixV a =
        ⨆ L ∈ s, commSub (⊤ : Subgroup W) L := by
      rw [sup_comm, sup_inf_assoc_of_le _ hWs, inf_comm, hB, sup_bot_eq]
    refine ⟨?_, ?_⟩
    · rw [inf_comm (fixV a)]
      calc fixV (⨆ L ∈ s, L) ⊓ fixV a ⊔
            (commSub (⊤ : Subgroup W) a ⊔ ⨆ L ∈ s, commSub (⊤ : Subgroup W) L)
          = ((⨆ L ∈ s, commSub (⊤ : Subgroup W) L) ⊔ (fixV (⨆ L ∈ s, L) ⊓ fixV a)) ⊔
              commSub (⊤ : Subgroup W) a := by ac_rfl
        _ = fixV a ⊔ commSub (⊤ : Subgroup W) a := by rw [← h1]
        _ = ⊤ := hA
    · calc fixV a ⊓ fixV (⨆ L ∈ s, L) ⊓
            (commSub (⊤ : Subgroup W) a ⊔ ⨆ L ∈ s, commSub (⊤ : Subgroup W) L)
          = fixV (⨆ L ∈ s, L) ⊓ ((commSub (⊤ : Subgroup W) a ⊔
              ⨆ L ∈ s, commSub (⊤ : Subgroup W) L) ⊓ fixV a) := by ac_rfl
        _ = fixV (⨆ L ∈ s, L) ⊓ ⨆ L ∈ s, commSub (⊤ : Subgroup W) L := by rw [h2]
        _ = ⊥ := ih2

end Decomp

section Perm

omit [CommGroup W] in
theorem eq_one_or_eq_of_sq_eq_one {M : Type*} [Group M] {a x : M} (ha : a ^ 2 = 1)
    (hx : x ∈ Subgroup.zpowers a) : x = 1 ∨ x = a := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
  obtain ⟨q, r, hr, hk⟩ : ∃ q r : ℤ, (r = 0 ∨ r = 1) ∧ k = 2 * q + r :=
    ⟨k / 2, k % 2, by omega, by omega⟩
  have h2 : a ^ (2 : ℤ) = 1 := by simpa [zpow_two, pow_two] using ha
  rw [hk, zpow_add, zpow_mul, h2, one_zpow, one_mul]
  rcases hr with rfl | rfl
  · left
    simp
  · right
    simp

omit [CommGroup W] in
theorem not_commuting_involutions {M : Type*} [Group M] [Finite M] {L : Subgroup M}
    (hL : Nat.card L = 6) {a b : M} (ha : a ∈ L) (hb : b ∈ L) (ha2 : a ^ 2 = 1) (hb2 : b ^ 2 = 1)
    (ha1 : a ≠ 1) (hb1 : b ≠ 1) (hab : a ≠ b) (hc : a * b = b * a) : False := by
  have hKL : Subgroup.zpowers a ⊔ Subgroup.zpowers b ≤ L :=
    sup_le (Subgroup.zpowers_le.2 ha) (Subgroup.zpowers_le.2 hb)
  have h1 : Nat.card (Subgroup.zpowers a) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime ha2 ha1
  have h2 : Nat.card (Subgroup.zpowers b) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hb2 hb1
  have hinf : Subgroup.zpowers a ⊓ Subgroup.zpowers b = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    rcases eq_one_or_eq_of_sq_eq_one ha2 hx.1 with h | h
    · exact h
    · exfalso
      rcases eq_one_or_eq_of_sq_eq_one hb2 hx.2 with h' | h'
      · exact ha1 (h.symm.trans h')
      · exact hab (h.symm.trans h')
  have hcomm : ∀ x ∈ Subgroup.zpowers a, ∀ y ∈ Subgroup.zpowers b, x * y = y * x := by
    intro x hx y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact ((Commute.zpow_zpow (show Commute a b from hc) i j).eq)
  have hcard := B2F.card_sup_mul_card_inf_of_commute hcomm
  rw [hinf, Subgroup.card_bot, h1, h2, mul_one] at hcard
  have hdvd := Subgroup.card_dvd_of_le hKL
  rw [hcard, hL] at hdvd
  omega

theorem map_commSub_conjAut (A : Subgroup (MulAut W)) (h : MulAut W) :
    (commSub (⊤ : Subgroup W) A).map h.toMonoidHom =
      commSub (⊤ : Subgroup W) (B1.conjAut h A) := by
  unfold commSub
  rw [MonoidHom.map_closure]
  congr 1
  ext c
  constructor
  · rintro ⟨c', ⟨x, hx, w, -, rfl⟩, rfl⟩
    refine ⟨h * x * h⁻¹, B1.mem_conjAut.2 ?_, h w, Subgroup.mem_top _, ?_⟩
    · simpa [mul_assoc] using hx
    · simp [MulAut.mul_apply, MulAut.inv_apply]
  · rintro ⟨y, hy, w, -, rfl⟩
    have hy' := B1.mem_conjAut.1 hy
    refine ⟨((h⁻¹ * y * h) (h⁻¹ w)) * ((h⁻¹ w))⁻¹,
      ⟨h⁻¹ * y * h, hy', h⁻¹ w, Subgroup.mem_top _, rfl⟩, ?_⟩
    simp [MulAut.mul_apply, MulAut.inv_apply]

end Perm

section Perm2

variable [Finite W] {𝓗 : Finset (Subgroup (MulAut W))} {X : Subgroup (MulAut W)}

theorem exists_conjAut_eq (hV : ∀ w : W, w ^ 2 = 1)
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    {L : Subgroup (MulAut W)} (hL : L ∈ 𝓗) {h : MulAut W} (hh : h ∈ X) :
    ∃ L' ∈ 𝓗, B1.conjAut h L = L' := by
  have hLX : L ≤ X := (hb.le_J hL).trans (B1.closure_transvectionsIn_le X)
  have key : ∀ t ∈ transvectionsIn L,
      h * t * h⁻¹ ∈ transvectionsIn (Subgroup.closure (transvectionsIn X)) := by
    intro t ht
    have htX : t ∈ X := hLX ht.1
    exact ⟨Subgroup.subset_closure ⟨X.mul_mem (X.mul_mem hh htX) (X.inv_mem hh),
      B1.isTransvection_conj ht.2 h⟩, B1.isTransvection_conj ht.2 h⟩
  obtain ⟨t₀, ht₀⟩ := hb.exists_transvection hL
  obtain ⟨B₀, hB₀, hB₀t⟩ := hb.cover _ (key t₀ ht₀)
  refine ⟨B₀, hB₀, ?_⟩
  have hsq : ∀ t ∈ transvectionsIn L, t ^ 2 = 1 := by
    intro t ht
    obtain ⟨-, ht1, w, htw⟩ := ht
    rw [pow_two]
    exact B1.tv_sq hV htw ht1
  have hgen : ∀ t ∈ transvectionsIn L, h * t * h⁻¹ ∈ B₀ := by
    intro t ht
    obtain ⟨B, hB, hBt⟩ := hb.cover _ (key t ht)
    by_cases hBB : B = B₀
    · rw [← hBB]
      exact hBt
    · exfalso
      have hcomm := hb.comm B hB B₀ hB₀ hBB _ hBt _ hB₀t
      have hcomm' : t * t₀ = t₀ * t := by
        have h1 : h * (t * t₀) * h⁻¹ = h * (t₀ * t) * h⁻¹ := by
          calc h * (t * t₀) * h⁻¹ = (h * t * h⁻¹) * (h * t₀ * h⁻¹) := by group
            _ = (h * t₀ * h⁻¹) * (h * t * h⁻¹) := hcomm
            _ = h * (t₀ * t) * h⁻¹ := by group
        exact mul_right_cancel (mul_left_cancel h1)
      have hne : t ≠ t₀ := by
        intro hteq
        rw [hteq] at hBt
        have hle : B ≤ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ B₀), H' :=
          le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut W)) (_ : H' ∈ 𝓗) =>
            ⨆ (_ : H' ≠ B₀), H') B hB (le_iSup (fun _ : B ≠ B₀ => B) hBB)
        have hmem : h * t₀ * h⁻¹ ∈ B₀ ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ B₀), H' := ⟨hB₀t, hle hBt⟩
        rw [hb.inf_biSup_ne_eq_bot hB₀, Subgroup.mem_bot] at hmem
        exact ht₀.2.1 (by simpa using hmem)
      exact not_commuting_involutions (hb.card_eq L hL) ht.1 ht₀.1 (hsq t ht) (hsq t₀ ht₀)
        ht.2.1 ht₀.2.1 hne hcomm'
  have hle : B1.conjAut h L ≤ B₀ := by
    rw [conjAut_eq_map, ← hb.closure_eq L hL, MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨t, ht, rfl⟩
    exact hgen t ht
  exact Subgroup.eq_of_le_of_card_ge hle (by
    rw [B1.card_conjAut, hb.card_eq L hL, hb.card_eq B₀ hB₀])

theorem conjAut_mem (hV : ∀ w : W, w ^ 2 = 1)
    (hb : IsTransvectionBlocks (Subgroup.closure (transvectionsIn X)) 𝓗)
    {I : Finset (Subgroup (MulAut W))} (hI : I ⊆ 𝓗) {h : MulAut W} (hh : h ∈ X)
    (hN : B1.conjAut h (⨆ L ∈ I, L) ≤ ⨆ L ∈ I, L) {L : Subgroup (MulAut W)} (hL : L ∈ I) :
    B1.conjAut h L ∈ I := by
  obtain ⟨B, hB, hBeq⟩ := hb.exists_conjAut_eq hV (hI hL) hh
  rw [hBeq]
  by_contra hBI
  have hLle : L ≤ ⨆ L ∈ I, L := le_iSup₂_of_le (f := fun (K : Subgroup (MulAut W)) (_ : K ∈ I) => K)
    L hL le_rfl
  have hle : B ≤ ⨆ L ∈ I, L := hBeq ▸ (B1.conjAut_le_iff.2 hLle).trans hN
  have hle2 : (⨆ L ∈ I, L) ≤ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ B), H' :=
    iSup₂_le fun K hK =>
      le_iSup₂_of_le (f := fun (H' : Subgroup (MulAut W)) (_ : H' ∈ 𝓗) => ⨆ (_ : H' ≠ B), H') K
        (hI hK) (le_iSup (fun _ : K ≠ B => K) (fun hKB => hBI (hKB ▸ hK)))
  have hbot := hb.inf_biSup_ne_eq_bot hB
  have : B = ⊥ := by
    rw [← hbot]
    exact (le_inf le_rfl (hle.trans hle2)).antisymm inf_le_left
  have hcard := hb.card_eq B hB
  rw [this, Subgroup.card_bot] at hcard
  omega

end Perm2


end IsTransvectionBlocks

end CFSG.Quasithin
