module

import CFSG.LocalAnalysis.EvenSporadicStandard.ReeStd.SylowLe
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG.LocalAnalysis.WeakClosure81

private theorem wrSect_card_le_four {E : Type*} [Group E] {V H : Subgroup E}
    (hcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x) (hsq : ∀ x ∈ V, x ^ 2 = 1) (hHV : H ≤ V)
    {s : Finset E} (hs : s.card ≤ 2) (hcl : Subgroup.closure (s : Set E) = H) :
    Nat.card H ≤ 4 := by
  classical
  have hsH : ∀ x ∈ s, x ∈ H := fun x hx => hcl ▸ Subgroup.subset_closure hx
  obtain ⟨a, ha, b, hb, hsab⟩ : ∃ a ∈ H, ∃ b ∈ H, ∀ x ∈ s, x = a ∨ x = b := by
    have hcases : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
    rcases hcases with h0 | h1 | h2
    · refine ⟨1, one_mem _, 1, one_mem _, fun x hx => ?_⟩
      simp [Finset.card_eq_zero.mp h0] at hx
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp h1
      exact ⟨a, hsH a (by simp), a, hsH a (by simp), fun x hx => Or.inl (by simpa using hx)⟩
    · obtain ⟨a, b, -, rfl⟩ := Finset.card_eq_two.mp h2
      exact ⟨a, hsH a (by simp), b, hsH b (by simp), fun x hx => by simpa using hx⟩
  have haa : a * a = 1 := by simpa [sq] using hsq a (hHV ha)
  have hbb : b * b = 1 := by simpa [sq] using hsq b (hHV hb)
  have hab : a * b = b * a := hcomm a (hHV ha) b (hHV hb)
  have ha_ab : a * (a * b) = b := by rw [← mul_assoc, haa, one_mul]
  have hb_ab : b * (a * b) = a := by rw [hab, ← mul_assoc, hbb, one_mul]
  have hab_a : a * b * a = b := by rw [hab, mul_assoc, haa, mul_one]
  have hab_b : a * b * b = a := by rw [mul_assoc, hbb, mul_one]
  have hab_ab : a * b * (a * b) = 1 := by rw [← mul_assoc, hab_a, hbb]
  have hmem : ∀ x ∈ H, x ∈ ({1, a, b, a * b} : Finset E) := by
    intro x hx
    rw [← hcl] at hx
    refine Subgroup.closure_induction (p := fun x _ => x ∈ ({1, a, b, a * b} : Finset E))
      ?_ ?_ ?_ ?_ hx
    · intro x hx
      rcases hsab x hx with h | h <;> rw [h] <;> simp
    · simp
    · intro x y hx hy ihx ihy
      simp only [Finset.mem_insert, Finset.mem_singleton] at ihx ihy ⊢
      rcases ihx with h | h | h | h <;> rcases ihy with h' | h' | h' | h' <;> rw [h, h'] <;>
        simp [haa, hbb, hab.symm, ha_ab, hb_ab, hab_a, hab_b, hab_ab]
    · intro x hx ihx
      have hxx : x * x = 1 := by simpa [sq] using hsq x (hHV (hcl ▸ hx))
      rwa [inv_eq_of_mul_eq_one_right hxx]
  have hsub : (H : Set E) ⊆ (({1, a, b, a * b} : Finset E) : Set E) := fun x hx => hmem x hx
  calc Nat.card H = (H : Set E).ncard := Nat.card_coe_set_eq _
    _ ≤ (({1, a, b, a * b} : Finset E) : Set E).ncard :=
        Set.ncard_le_ncard hsub (Finset.finite_toSet _)
    _ = ({1, a, b, a * b} : Finset E).card := Set.ncard_coe_finset _
    _ ≤ 4 := Finset.card_le_four

private theorem wrSect_relIndex_map_dvd {G E : Type*} [Group G] [Group E] (π : G →* E)
    (A P : Subgroup G) : (A.map π).relIndex (P.map π) ∣ A.relIndex P := by
  rw [← Subgroup.relIndex_comap]
  exact Subgroup.relIndex_dvd_of_le_left P (Subgroup.le_comap_map π A)

private theorem wrSect_sup_eq {G : Type*} [Group G] {A B P : Subgroup G} (hA : A ≤ P)
    (hB : B ≤ P) (hAi : A.relIndex P = 2) (hBi : B.relIndex P = 2) (hAB : A ≠ B) :
    A ⊔ B = P := by
  have hsup : A ⊔ B ≤ P := sup_le hA hB
  have h1 := Subgroup.relIndex_mul_relIndex A (A ⊔ B) P le_sup_left hsup
  rw [hAi] at h1
  have hd : (A ⊔ B).relIndex P ∣ 2 := Dvd.intro_left _ h1
  rcases (Nat.dvd_prime Nat.prime_two).mp hd with h | h
  · exact le_antisymm hsup (Subgroup.relIndex_eq_one.mp h)
  · rw [h] at h1
    have h3 : A.relIndex (A ⊔ B) = 1 := by omega
    have hBA : B ≤ A := le_sup_right.trans (Subgroup.relIndex_eq_one.mp h3)
    exfalso
    have h4 := Subgroup.relIndex_mul_relIndex B A P hBA hA
    rw [hBi, hAi] at h4
    have h5 : B.relIndex A = 1 := by omega
    exact hAB (le_antisymm (Subgroup.relIndex_eq_one.mp h5) hBA)

private theorem wrSect_card_eq_relIndex_mul {E : Type*} [Group E] {H V : Subgroup E}
    (h : H ≤ V) : Nat.card V = H.relIndex V * Nat.card H := by
  have h1 := Subgroup.relIndex_mul_card (H := H) (K := V)
  rw [inf_of_le_left h] at h1
  exact h1.symm

private theorem wrSect_relIndex_ne_zero {G : Type*} [Group G] [Finite G] (A P : Subgroup G) :
    A.relIndex P ≠ 0 :=
  (Subgroup.finiteIndex_of_finite (H := A.subgroupOf P)).index_ne_zero

private theorem wrSect_core {G E : Type*} [Group G] [Finite G] [Group E] (π : G →* E)
    (hπ : Function.Surjective π)
    (h1 : ∀ P : Subgroup G, IsPGroup 2 P → ∃ A ≤ P, IsMulCommutative A ∧ A.relIndex P ≤ 2)
    (h2 : ∀ A : Subgroup G, IsPGroup 2 A → IsMulCommutative A →
      ∃ s : Finset G, s.card ≤ 2 ∧ Subgroup.closure (s : Set G) = A)
    (V : Subgroup E) (hVc : IsMulCommutative V) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hV8 : 8 ≤ Nat.card V)
    (hc : Nat.card V = 8 → ∃ c ∈ Subgroup.normalizer (V : Set E),
      ∀ U : Subgroup E, U ≤ V → (∀ u ∈ U, c * u * c⁻¹ ∈ U) → U = ⊥ ∨ U = V) :
    False := by
  classical
  have hVcomm : ∀ x ∈ V, ∀ y ∈ V, x * y = y * x := fun x hx y hy => setLike_mul_comm hx hy
  have : Finite V := Nat.finite_of_card_ne_zero (by omega)
  have hV2g : IsPGroup 2 V := fun g => ⟨1, by
    have := hV2 g g.2
    apply Subtype.ext
    simpa using this⟩
  obtain ⟨P₀, hP₀p, -, hP₀V', hodd⟩ :=
    CFSG.EvenSporadicStandard.ReeStd.exists_isPGroup_le_odd_relIndex
      (A := V.comap π) (P := ⊥) IsPGroup.of_bot bot_le
  have hmap : P₀.map π = V := by
    refine le_antisymm (Subgroup.map_le_iff_le_comap.mpr hP₀V') ?_
    have hdvd : (P₀.map π).relIndex V ∣ P₀.relIndex (V.comap π) := by
      have h := wrSect_relIndex_map_dvd π P₀ (V.comap π)
      rwa [Subgroup.map_comap_eq_self_of_surjective hπ] at h
    have hodd' : Odd ((P₀.map π).relIndex V) := Odd.of_dvd_nat hodd hdvd
    obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hV2g
    have hdvd2 : (P₀.map π).relIndex V ∣ 2 ^ k := hk ▸ Subgroup.relIndex_dvd_card _ _
    have hone : (P₀.map π).relIndex V = 1 :=
      Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k (hodd'.coprime_two_right))
        hdvd2
    exact Subgroup.relIndex_eq_one.mp hone
  obtain ⟨A₀, hA₀P, hA₀c, hA₀i⟩ := h1 P₀ hP₀p
  obtain ⟨s, hs, hsA⟩ := h2 A₀ (hP₀p.to_le hA₀P) hA₀c
  have hĀV : A₀.map π ≤ V := hmap ▸ Subgroup.map_mono hA₀P
  have hĀ4 : Nat.card (A₀.map π) ≤ 4 := by
    refine wrSect_card_le_four hVcomm hV2 hĀV (s := s.image π)
      (Finset.card_image_le.trans hs) ?_
    rw [Finset.coe_image, ← MonoidHom.map_closure, hsA]
  have hĀi : (A₀.map π).relIndex V ≤ 2 := by
    have h := wrSect_relIndex_map_dvd π A₀ P₀
    rw [hmap] at h
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (wrSect_relIndex_ne_zero A₀ P₀)) h).trans hA₀i
  have hcardV := wrSect_card_eq_relIndex_mul hĀV
  have hV8' : Nat.card V = 8 := by
    have : Nat.card V ≤ 8 := by
      rw [hcardV]
      exact Nat.mul_le_mul hĀi hĀ4
    omega
  have hĀ4' : Nat.card (A₀.map π) = 4 := by
    rw [hV8'] at hcardV
    generalize (A₀.map π).relIndex V = r at *
    generalize Nat.card (A₀.map π) = m at *
    interval_cases r <;> omega
  have hĀbot : A₀.map π ≠ ⊥ := fun h => by
    rw [h, Subgroup.card_bot] at hĀ4'
    omega
  have hĀtop : A₀.map π ≠ V := fun h => by
    rw [h] at hĀ4'
    omega
  obtain ⟨c, hcN, hcirr⟩ := hc hV8'
  obtain ⟨x, hx⟩ := hπ c
  have hxN : x ∈ Subgroup.normalizer ((V.comap π : Subgroup G) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    simp only [Subgroup.mem_comap, map_mul, map_inv, hx]
    exact Subgroup.mem_normalizer_iff.mp hcN (π y)
  obtain ⟨v, hvV', hvx⟩ :=
    CFSG.EvenSporadicStandard.ReeStd.exists_mul_mem_normalizer_of_sylow hP₀V' hP₀p hodd hxN
  have hπv : π v ∈ V := hvV'
  have hact : ∀ u ∈ V, π (v * x) * u * (π (v * x))⁻¹ = c * u * c⁻¹ := by
    intro u hu
    have hcu : c * u * c⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hcN u).mp hu
    have e : π (v * x) * u * (π (v * x))⁻¹ = π v * (c * u * c⁻¹) * (π v)⁻¹ := by
      rw [map_mul, hx]
      group
    rw [e, hVcomm (π v) hπv _ hcu, mul_inv_cancel_right]
  have hinv : ∀ U : Subgroup E, U ≤ V → (∀ u ∈ U, π (v * x) * u * (π (v * x))⁻¹ ∈ U) →
      U = ⊥ ∨ U = V := by
    intro U hUV hU
    refine hcirr U hUV fun u hu => ?_
    rw [← hact u (hUV hu)]
    exact hU u hu
  clear hact hcirr
  generalize v * x = h at hvx hinv
  have hhP : ∀ y, y ∈ P₀ ↔ h * y * h⁻¹ ∈ P₀ := Subgroup.mem_normalizer_iff.mp hvx
  have hP₀f : P₀.map (MulAut.conj h).toMonoidHom = P₀ :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hvx
  set f : G →* G := (MulAut.conj h).toMonoidHom
  have hf : ∀ g : G, f g = h * g * h⁻¹ := fun g => rfl
  have hfinj : Function.Injective f := (MulAut.conj h).injective
  have := hA₀c
  have hA₁P : A₀.map f ≤ P₀ := (Subgroup.map_mono hA₀P).trans hP₀f.le
  have hA₁i : (A₀.map f).relIndex P₀ = A₀.relIndex P₀ := by
    have h' := Subgroup.relIndex_map_map_of_injective A₀ P₀ hfinj
    rwa [hP₀f] at h'
  have hA₀2 : A₀.relIndex P₀ = 2 := by
    have hne0 := wrSect_relIndex_ne_zero A₀ P₀
    have hne1 : A₀.relIndex P₀ ≠ 1 := fun h1' => by
      have hPA : P₀ ≤ A₀ := Subgroup.relIndex_eq_one.mp h1'
      apply hĀtop
      rw [le_antisymm hA₀P hPA, hmap]
    omega
  have hA₁ne : A₀.map f ≠ A₀ := by
    intro heq
    have hinvĀ : ∀ u ∈ A₀.map π, π h * u * (π h)⁻¹ ∈ A₀.map π := by
      rintro _ ⟨a, ha, rfl⟩
      refine ⟨h * a * h⁻¹, ?_, by simp⟩
      have : h * a * h⁻¹ ∈ A₀.map f := ⟨a, ha, rfl⟩
      rwa [heq] at this
    rcases hinv (A₀.map π) hĀV hinvĀ with h' | h'
    · exact hĀbot h'
    · exact hĀtop h'
  have hjoin : A₀ ⊔ A₀.map f = P₀ := wrSect_sup_eq hA₀P hA₁P hA₀2 (hA₁i.trans hA₀2) hA₁ne.symm
  set B : Subgroup G := A₀ ⊓ A₀.map f
  have hBcent : P₀ ≤ Subgroup.centralizer (B : Set G) := by
    rw [← hjoin]
    exact sup_le ((Subgroup.le_centralizer (H := A₀)).trans (Subgroup.centralizer_le inf_le_left))
      ((Subgroup.le_centralizer (H := A₀.map f)).trans (Subgroup.centralizer_le inf_le_right))
  have hBle : B ≤ Subgroup.centralizer (P₀ : Set G) := Subgroup.le_centralizer_iff.mpr hBcent
  have hBZ : B ≤ P₀ ⊓ Subgroup.centralizer (P₀ : Set G) :=
    le_inf (inf_le_left.trans hA₀P) hBle
  have hBi : B.relIndex P₀ ≤ 4 := by
    have h' := Subgroup.relIndex_inf_le (H := A₀) (K := A₀.map f) (L := P₀)
    rw [hA₁i, hA₀2] at h'
    omega
  have hBV : B.map π ≤ V := hmap ▸ Subgroup.map_mono (inf_le_left.trans hA₀P)
  have hBcard := wrSect_card_eq_relIndex_mul hBV
  have hBimg : (B.map π).relIndex V ≤ 4 := by
    have h' := wrSect_relIndex_map_dvd π B P₀
    rw [hmap] at h'
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (wrSect_relIndex_ne_zero B P₀)) h').trans hBi
  have hBne : B.map π ≠ ⊥ := fun hbot => by
    have h1' : Nat.card (B.map π) = 1 := by rw [hbot]; exact Subgroup.card_bot
    rw [h1'] at hBcard
    omega
  set Z : Subgroup G := P₀ ⊓ Subgroup.centralizer (P₀ : Set G)
  have hZV : Z.map π ≤ V := hmap ▸ Subgroup.map_mono inf_le_left
  have hZinv : ∀ u ∈ Z.map π, π h * u * (π h)⁻¹ ∈ Z.map π := by
    rintro _ ⟨z, ⟨hzP, hzC⟩, rfl⟩
    have hfz : f z ∈ Subgroup.centralizer (P₀ : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy' : h⁻¹ * y * h ∈ P₀ := (Subgroup.mem_normalizer_iff''.mp hvx y).mp hy
      have hcomm := Subgroup.mem_centralizer_iff.mp hzC _ hy'
      rw [hf]
      calc y * (h * z * h⁻¹) = h * ((h⁻¹ * y * h) * z) * h⁻¹ := by group
        _ = h * (z * (h⁻¹ * y * h)) * h⁻¹ := by rw [hcomm]
        _ = (h * z * h⁻¹) * y := by group
    exact ⟨f z, ⟨(hhP z).mp hzP, hfz⟩, by simp [hf]⟩
  have hZeq : Z.map π = V := by
    rcases hinv (Z.map π) hZV hZinv with hbot | htop
    · exact absurd (le_bot_iff.mp (hbot ▸ Subgroup.map_mono hBZ)) hBne
    · exact htop
  have hZc : IsMulCommutative Z := IsMulCommutative.of_setLike_mul_comm fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp ha.2 b hb.1).symm
  obtain ⟨t, ht, htZ⟩ := h2 Z (hP₀p.to_le inf_le_left) hZc
  have hle4 : Nat.card V ≤ 4 := by
    refine wrSect_card_le_four (H := V) hVcomm hV2 le_rfl (s := t.image π)
      (Finset.card_image_le.trans ht) ?_
    rw [Finset.coe_image, ← MonoidHom.map_closure, htZ]
    exact hZeq
  omega

theorem false_of_section_elemAbelian_of_wreathLike {Y : Type} [Group Y] [Finite Y]
    (h1 : ∀ P : Subgroup Y, IsPGroup 2 P → ∃ A ≤ P, IsMulCommutative A ∧ A.relIndex P ≤ 2)
    (h2 : ∀ A : Subgroup Y, IsPGroup 2 A → IsMulCommutative A →
      ∃ s : Finset Y, s.card ≤ 2 ∧ Subgroup.closure (s : Set Y) = A)
    (M : Subgroup Y) (N : Subgroup M) [N.Normal] (V : Subgroup (M ⧸ N))
    (hVc : IsMulCommutative V) (hV2 : ∀ v ∈ V, v ^ 2 = 1) (hV8 : 8 ≤ Nat.card V)
    (hc : Nat.card V = 8 → ∃ c ∈ Subgroup.normalizer (V : Set (M ⧸ N)),
      ∀ U : Subgroup (M ⧸ N), U ≤ V → (∀ u ∈ U, c * u * c⁻¹ ∈ U) → U = ⊥ ∨ U = V) :
    False := by
  refine wrSect_core (QuotientGroup.mk' N) (QuotientGroup.mk'_surjective N) ?_ ?_ V hVc hV2
    hV8 hc
  · intro P hP
    obtain ⟨A, hAP, hAc, hAi⟩ := h1 (P.map M.subtype) (hP.map M.subtype)
    refine ⟨A.comap M.subtype, ?_, ?_, ?_⟩
    · exact (Subgroup.comap_mono hAP).trans
        (Subgroup.comap_map_eq_self_of_injective M.subtype_injective P).le
    · exact Subgroup.comap_injective_isMulCommutative A M.subtype_injective
    · rw [Subgroup.relIndex_comap]
      exact hAi
  · intro A hA hAc
    obtain ⟨s, hs, hcl⟩ := h2 (A.map M.subtype) (hA.map M.subtype) inferInstance
    refine ⟨s.preimage M.subtype M.subtype_injective.injOn, ?_, ?_⟩
    · refine le_trans (Finset.card_le_card_of_injOn M.subtype (fun a ha => ?_)
        M.subtype_injective.injOn) hs
      simpa using ha
    · apply Subgroup.map_injective M.subtype_injective
      have hsub : (s : Set Y) ⊆ Set.range M.subtype := by
        intro y hy
        have : y ∈ A.map M.subtype := hcl ▸ Subgroup.subset_closure hy
        obtain ⟨a, -, rfl⟩ := this
        exact ⟨a, rfl⟩
      rw [MonoidHom.map_closure, Finset.coe_preimage, Set.image_preimage_eq_inter_range,
        Set.inter_eq_left.mpr hsub, hcl]

end CFSG.LocalAnalysis.WeakClosure81

end
