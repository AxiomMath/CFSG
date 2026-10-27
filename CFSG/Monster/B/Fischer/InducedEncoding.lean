
module


public import Certificates.Certificate3033

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Fischer

open CFSG.Monster.Code CFSG.Monster.B.Classical.Mog22 CFSG.Monster.B.TwoA CFSG.Sporadic.Mathieu

theorem hexCat_hRep_injective :
    ∀ i < 77, ∀ j < 77, hexCat (hCat i) = hexCat (hCat j) → i = j :=
  Certificates.certificate3033

theorem hexad_hRep_injective {i j : ℕ} (hi : i < 77) (hj : j < 77)
    (h : B₀.map (psiHom (hRep i)).toEmbedding = B₀.map (psiHom (hRep j)).toEmbedding) : i = j := by
  rw [hexad_hRep, hexad_hRep] at h
  exact hexCat_hRep_injective i hi j hj (Finset.map_injective _ h)

theorem exists_hRep
    (k : CFSG.Blueprint.NativeSporadic.M22) :
    ∃ i < 77, B₀.map (psiHom (hRep i)).toEmbedding = B₀.map (psiHom k).toEmbedding := by
  set f : Fin 77 → Finset (Fin 24) := fun i => B₀.map (psiHom (hRep i)).toEmbedding
  have hinj : Function.Injective f := fun i j h => Fin.ext (hexad_hRep_injective i.2 j.2 h)
  have hsub : Finset.univ.image f ⊆ ℬ₀ := fun B hB => by
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hB
    exact hexad_mem_ℬ₀ _
  have heq : Finset.univ.image f = ℬ₀ := Finset.eq_of_subset_of_card_le hsub (by
    rw [card_ℬ₀, Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_fin])
  have := hexad_mem_ℬ₀ k
  rw [← heq] at this
  obtain ⟨i, -, hi⟩ := Finset.mem_image.1 this
  exact ⟨i, i.2, hi⟩

theorem decZ_bijective :
    Function.Bijective decZ := by
  refine ⟨?_, ?_⟩
  · rintro ⟨i, q⟩ ⟨j, q'⟩ h
    have hhex : hexadOf (zMk (hRep i) q) = hexadOf (zMk (hRep j) q') := congrArg hexadOf h
    rw [hexadOf_zMk, hexadOf_zMk] at hhex
    have hij' : i = j := Fin.ext (hexad_hRep_injective i.2 j.2 hhex)
    subst hij'
    obtain ⟨h1, e1, e2⟩ := zMk_eq_iff.1 h
    simp only at e1 e2
    have h1one : h1 = 1 := by
      apply Subtype.ext
      have := e1
      rw [left_eq_mul] at this
      exact this
    subst h1one
    simp only [map_one, Equiv.Perm.one_apply] at e2
    rw [e2]
  · intro z
    obtain ⟨k, q, rfl⟩ := zMk_surj z
    obtain ⟨i, hi, hhex⟩ := exists_hRep k
    have hκ := mem_KB_of_hexad hhex
    refine ⟨(⟨i, hi⟩, affA ⟨_, hκ⟩ q), ?_⟩
    simp only [decZ]
    rw [← zMk_mul]
    congr 1
    simp

@[expose] noncomputable def zEquiv :
    Fin 77 × Q₀ ≃ Z :=
    Equiv.ofBijective decZ decZ_bijective

theorem zEquiv_apply
    (p : Fin 77 × Q₀) : zEquiv p = zMk (hRep p.1)
    p.2 := rfl

instance :
    Finite Z := Finite.of_equiv _ zEquiv

theorem natCard_Z :
    Nat.card Z = 2464 := by
  rw [← Nat.card_congr zEquiv, Nat.card_prod, natCard_Q₀, Nat.card_eq_fintype_card,
    Fintype.card_fin]

@[expose] noncomputable def ι :
    Y → Fin 3510
  | .inl x => ⟨pos x, by have := (pos x).2; omega⟩
  | .inr (.inl w) => ⟨22 + wEquiv.symm w, by have := (wEquiv.symm w).2; omega⟩
  | .inr (.inr z) => ⟨1046 + 32 * (zEquiv.symm z).1 + qEquiv.symm (zEquiv.symm z).2, by
      have := (zEquiv.symm z).1.2
      have := (qEquiv.symm (zEquiv.symm z).2).2
      omega⟩

theorem ι_inl
    (x : X₀) : (ι (.inl x) : ℕ) = pos x := rfl

theorem ι_wv
    {u : ℕ} (hu : u < 1024) : (ι (.inr (.inl (wv u))) : ℕ) =
    22 + u := by
  change 22 + (wEquiv.symm (wv u) : ℕ) = 22 + u
  rw [show wv u = wEquiv ⟨u, hu⟩ from rfl, Equiv.symm_apply_apply]

theorem ι_zMk
    {i q : ℕ} (hi : i < 77) (hq : q < 32) :
    (ι (.inr (.inr (zMk (hRep i) (qv q)))) : ℕ) = 1046 + 32 * i + q := by
  change 1046 + 32 * ((zEquiv.symm (zMk (hRep i) (qv q))).1 : ℕ) +
    (qEquiv.symm (zEquiv.symm (zMk (hRep i) (qv q))).2 : ℕ) = _
  rw [show zMk (hRep i) (qv q) = zEquiv (⟨i, hi⟩, qEquiv ⟨q, hq⟩) from rfl, Equiv.symm_apply_apply,
    Equiv.symm_apply_apply]

theorem decY_ι
    (y : Y) : decY (ι y) = y := by
  rcases y with x | w | z
  · simp only [decY, ι_inl, (pos x).2, ↓reduceDIte]
    congr 1
    exact coordAt_pos x
  · obtain ⟨u, hu, rfl⟩ := wv_surj w
    rw [decY, ι_wv hu]
    have h1 : ¬(22 + u < 22) := by omega
    have h2 : 22 + u < 1046 := by omega
    simp only [h1, h2, ↓reduceDIte, ↓reduceIte, Nat.add_sub_cancel_left]
  · obtain ⟨⟨i, q⟩, rfl⟩ := zEquiv.surjective z
    obtain ⟨m, hm, rfl⟩ := qv_surj q
    rw [zEquiv_apply, ι_zMk i.2 hm, decY]
    have h0 : ¬(1046 + 32 * (i : ℕ) + m < 22) := by omega
    have h0' : ¬(1046 + 32 * (i : ℕ) + m < 1046) := by omega
    have h1 : (1046 + 32 * (i : ℕ) + m - 1046) / 32 = i := by omega
    have h2 : (1046 + 32 * (i : ℕ) + m - 1046) % 32 = m := by omega
    simp only [h0, h0', ↓reduceDIte, ↓reduceIte, h1, h2]

theorem ι_injective :
    Function.Injective ι := fun y y' h => by
  rw [← decY_ι y, ← decY_ι y', h]

theorem natCard_Y :
    Nat.card Y = 3510 := by
  rw [Nat.card_sum, Nat.card_sum, Nat.card_eq_fintype_card (α := X₀), Fintype.card_coe, card_X₀,
    natCard_W₀, natCard_Z]

theorem ι_bijective :
    Function.Bijective ι :=
  ι_injective.bijective_of_nat_card_le (by rw [natCard_Y, Nat.card_eq_fintype_card,
    Fintype.card_fin])

theorem ι_decY
    {n : ℕ} (hn : n < 3510) : (ι (decY n) : ℕ) = n := by
  obtain ⟨y, hy⟩ := ι_bijective.2 ⟨n, hn⟩
  have : decY n = y := by
    have := congrArg (fun m : Fin 3510 => decY m) hy
    simp only [decY_ι] at this
    exact this.symm
  rw [this, hy]

end CFSG.Monster.B.Fischer
