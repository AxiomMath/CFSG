module

public import CFSG.Quasithin.Vol2.KGFactM22HexProof

public section

namespace CFSG.Quasithin.H13.P31Sec.M22Hex

open Equiv CFSG.QuasithinUnique.Vol2Native.A312L CFSG.QuasithinUnique.Vol2Native.A312L.M22Lat
  PermLat CFSG.Quasithin.H13.S126M22

theorem isSylowTwoOf_Ugrp :
    CFSG.QuasithinUnique.IsSylowTwoOf Ugrp ⊤ :=
  cert.isSylowTwoOf_top (rawIsEnc 22) cert_check (k := 7) (m := 3465) (by decide) (by decide)
    (by omega)

theorem card_Mgrp : Nat.card ↥Mgrp = 443520 :=
  cert.card_m (rawIsEnc 22) (LatCert.closedOK_of_check cert_check)
    (LatCert.sizesOK_of_check cert_check)

theorem card_L6 : Nat.card ↥L6 = 5760 := by
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe l6_le_M).toEquiv]
  exact ext6.1

theorem eq_L6_of_Ugrp_le (Y : Subgroup ↥Mgrp) (hUY : Ugrp ≤ Y)
    (hY : Nat.card ↥Y = 5760) : Y = L6 := by
  have hck := cert_check
  have hcl := LatCert.closedOK_of_check hck
  obtain ⟨j, hj, hLM, hBL, hcardj⟩ := cert.overgroup_cases_idx (rawIsEnc 22) hck _ hUY
  have hs : cert.sizes = [128, 384, 1920, 5760, 443520, 384] := rfl
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  have hj6 : j < 6 := hlen ▸ hj
  have hcj : cert.sizes.getD j 0 = 5760 := by
    rw [← hcardj, ← hY, hBL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv]
  rw [hs] at hcj
  have hj3 : j = 3 := by
    interval_cases j <;> first | rfl | exact absurd hcj (by decide)
  subst hj3
  have ha := List.all_eq_true.mp incl6 3 (by simp)
  have h5760 : cert.sizes.getD 3 0 = 5760 := rfl
  simp only [h5760, bne_self_eq_false, Bool.false_or] at ha
  have hlen3 : 3 < (cert.tGens :: cert.lat).length := by rw [hlen]; norm_num
  have hmem : (cert.tGens :: cert.lat)[3] ∈ cert.tGens :: cert.lat := List.getElem_mem hlen3
  have hAL : Subgroup.closure {g | g ∈ l6Gens} ≤
      Subgroup.closure {g | g ∈ (cert.tGens :: cert.lat)[3]} := by
    rw [Subgroup.closure_le]
    intro x hx
    have := List.all_eq_true.mp ha x hx
    rw [List.getD_eq_getElem _ _ hlen3] at this
    exact (mem_closure_iff_H (rawIsEnc 22) _ cert.depth
      (cert.members_closed hcl _ hmem) x).mpr (Std.HashSet.contains_iff_mem.mp this)
  obtain ⟨hAcard, -⟩ := ext6
  have hLA := Subgroup.eq_of_le_of_card_ge hAL (by rw [hcardj, hAcard]; exact h5760.le)
  rw [hBL, ← hLA]

theorem Ugrp_le_L6 : Ugrp ≤ L6 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P₀, hP₀⟩ := Sylow.exists_subgroup_card_pow_prime 2 (G := ↥L6) (n := 7)
    (by rw [card_L6]; norm_num)
  have hPc : Nat.card ↥(P₀.map L6.subtype) = 2 ^ 7 := by
    rw [Subgroup.card_map_of_injective L6.subtype_injective, hP₀]
  have hPs : CFSG.QuasithinUnique.IsSylowTwoOf (P₀.map L6.subtype) ⊤ :=
    isSylowTwoOf_top_of_card hPc (m := 3465) (by rw [card_Mgrp]; norm_num) (by decide)
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf hPs isSylowTwoOf_Ugrp
  have hUY : Ugrp ≤ L6.map (MulAut.conj g).toMonoidHom := by
    rw [← hg]
    exact Subgroup.map_mono (Subgroup.map_subtype_le P₀)
  have hY : Nat.card ↥(L6.map (MulAut.conj g).toMonoidHom) = 5760 := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, card_L6]
  exact hUY.trans (eq_L6_of_Ugrp_le _ hUY hY).le

theorem L6_structure :
    ∃ f : ↥L6 →* ↥(alternatingGroup (Fin 6)), Function.Surjective f ∧
      ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a := by
  obtain ⟨-, V, hVn, hVc, -, -, ⟨e⟩⟩ := ext6
  haveI := hVn
  let e0 : ↥L6 ≃* ↥(Subgroup.closure {g | g ∈ l6Gens}) :=
    Subgroup.subgroupOfEquivOfLe l6_le_M
  let f : ↥L6 →* ↥(alternatingGroup (Fin 6)) :=
    e.toMonoidHom.comp ((QuotientGroup.mk' V).comp e0.toMonoidHom)
  have hf : ∀ y, f y = 1 → e0 y ∈ V := fun y hy => by
    simpa only [f, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] using hy
  refine ⟨f, e.surjective.comp ((QuotientGroup.mk'_surjective V).comp e0.surjective), ?_⟩
  intro a ha b hb
  exact e0.injective (by
    rw [map_mul, map_mul]
    exact hVc _ (hf a ha) _ (hf b hb))

theorem normalizer_L6_le (hs : IsSimpleGroup ↥Mgrp) :
    Subgroup.normalizer (L6 : Set ↥Mgrp) ≤ L6 := by
  have hck := cert_check
  have hLN : L6 ≤ Subgroup.normalizer (L6 : Set ↥Mgrp) := Subgroup.le_normalizer
  obtain ⟨j, hj, hLM, hNL, hcardj⟩ := cert.overgroup_cases_idx (rawIsEnc 22) hck
    (Subgroup.normalizer (L6 : Set ↥Mgrp)) (Ugrp_le_L6.trans hLN)
  have hs' : cert.sizes = [128, 384, 1920, 5760, 443520, 384] := rfl
  have hlen : (cert.tGens :: cert.lat).length = 6 := by simp [cert, lat]
  have hj6 : j < 6 := hlen ▸ hj
  have hcardN : Nat.card ↥(Subgroup.normalizer (L6 : Set ↥Mgrp)) = cert.sizes.getD j 0 := by
    rw [hNL, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLM).toEquiv, hcardj]
  have hdvd : 5760 ∣ cert.sizes.getD j 0 := by
    rw [← hcardN, ← card_L6]
    exact Subgroup.card_dvd_of_le hLN
  rw [hs'] at hdvd
  have hj34 : j = 3 ∨ j = 4 := by
    interval_cases j <;> first | exact Or.inl rfl | exact Or.inr rfl | exact absurd hdvd (by decide)
  rcases hj34 with rfl | rfl
  · have h3 : Nat.card ↥(Subgroup.normalizer (L6 : Set ↥Mgrp)) = 5760 := by
      rw [hcardN]; rfl
    exact (Subgroup.eq_of_le_of_card_ge hLN (by rw [h3, card_L6])).ge
  · have h4 : Nat.card ↥(Subgroup.normalizer (L6 : Set ↥Mgrp)) = Nat.card ↥Mgrp := by
      rw [hcardN, card_Mgrp]; rfl
    have htop : Subgroup.normalizer (L6 : Set ↥Mgrp) = ⊤ := Subgroup.eq_top_of_card_eq _ h4
    haveI : L6.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    exfalso
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal L6 with h | h
    · have := card_L6
      rw [h, Subgroup.card_bot] at this
      omega
    · have := card_L6
      rw [h, Subgroup.card_top, card_Mgrp] at this
      omega

theorem hexad_of_sylow (hs : IsSimpleGroup ↥Mgrp)
    (P : Subgroup ↥Mgrp) (hP : CFSG.QuasithinUnique.IsSylowTwoOf P ⊤) :
    ∃ B : Subgroup ↥Mgrp, P ≤ B ∧
      (∀ Q : Subgroup ↥Mgrp, P ≤ Q → Q.index = B.index → Q = B) ∧
      (∀ x ∈ Subgroup.normalizer (B : Set ↥Mgrp), x ∈ B) ∧
      ∃ f : ↥B →* ↥(alternatingGroup (Fin 6)), Function.Surjective f ∧
        ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a := by
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf isSylowTwoOf_Ugrp hP
  set σ : ↥Mgrp ≃* ↥Mgrp := MulAut.conj g with hσ
  have hL6idx : L6.index = 77 := by
    have h := Subgroup.card_mul_index L6
    rw [card_L6, card_Mgrp] at h
    omega
  have hBidx : (L6.map σ.toMonoidHom).index = 77 :=
    (Subgroup.index_map_equiv L6 σ).trans hL6idx
  refine ⟨L6.map σ.toMonoidHom, ?_, ?_, ?_, ?_⟩
  · rw [← hg]
    exact Subgroup.map_mono Ugrp_le_L6
  · intro Q hPQ hQidx
    rw [hBidx] at hQidx
    have hQcard : Nat.card ↥Q = 5760 := by
      have h := Subgroup.card_mul_index Q
      rw [hQidx, card_Mgrp] at h
      omega
    set Q' : Subgroup ↥Mgrp := Q.map σ.symm.toMonoidHom with hQ'
    have hUQ' : Ugrp ≤ Q' := by
      intro u hu
      have hσu : σ u ∈ Q := hPQ (by rw [← hg]; exact ⟨u, hu, rfl⟩)
      exact ⟨σ u, hσu, by simp⟩
    have hQ'card : Nat.card ↥Q' = 5760 := by
      rw [hQ', Subgroup.card_map_of_injective σ.symm.injective, hQcard]
    have hQ'eq : Q' = L6 := eq_L6_of_Ugrp_le Q' hUQ' hQ'card
    ext y
    rw [Subgroup.mem_map_equiv]
    have h1 : σ.symm y ∈ Q' ↔ y ∈ Q := by
      rw [hQ', Subgroup.mem_map_equiv]
      simp
    rw [← hQ'eq, h1]
  · intro x hx
    rw [Subgroup.mem_normalizer_iff] at hx
    have hy : σ.symm x ∈ Subgroup.normalizer (L6 : Set ↥Mgrp) := by
      rw [Subgroup.mem_normalizer_iff]
      intro h
      have h1 := hx (σ h)
      rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv] at h1
      simpa [map_mul] using h1
    rw [Subgroup.mem_map_equiv]
    exact normalizer_L6_le hs hy
  · obtain ⟨f, hf, hker⟩ := L6_structure
    let e : ↥L6 ≃* ↥(L6.map σ.toMonoidHom) :=
      Subgroup.equivMapOfInjective L6 σ.toMonoidHom σ.injective
    refine ⟨f.comp e.symm.toMonoidHom, hf.comp e.symm.surjective, ?_⟩
    intro a ha b hb
    have ha' : e.symm a ∈ f.ker := ha
    have hb' : e.symm b ∈ f.ker := hb
    apply e.symm.injective
    rw [map_mul, map_mul]
    exact hker _ ha' _ hb'

theorem hexad_of_sylow_of_eq (N : Subgroup (Perm (Fin 22)))
    (hN : Subgroup.closure {g | g ∈ cert.mGens} = N) (hs : IsSimpleGroup ↥N)
    (P : Subgroup ↥N) (hP : CFSG.QuasithinUnique.IsSylowTwoOf P ⊤) :
    ∃ B : Subgroup ↥N, P ≤ B ∧
      (∀ Q : Subgroup ↥N, P ≤ Q → Q.index = B.index → Q = B) ∧
      (∀ x ∈ Subgroup.normalizer (B : Set ↥N), x ∈ B) ∧
      ∃ f : ↥B →* ↥(alternatingGroup (Fin 6)), Function.Surjective f ∧
        ∀ a ∈ f.ker, ∀ b ∈ f.ker, a * b = b * a := by
  subst hN
  exact hexad_of_sylow hs P hP

end CFSG.Quasithin.H13.P31Sec.M22Hex
