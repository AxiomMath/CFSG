module

public import CFSG.Quasithin.Background.GoldschmidtE23Blocks
public import CFSG.Quasithin.Vol2.Ch3zRank
public import CFSG.Quasithin.Vol2.Ch3zBlocks

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6

namespace GE23

theorem exists_perm3_hom_sl2 :
    ∃ ι : Equiv.Perm (Fin 3) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2),
      Function.Injective ι := by
  have hV' : ∀ v : Multiplicative (Fin 2 → ZMod 2), v ^ 2 = 1 := by
    intro v
    apply Multiplicative.toAdd.injective
    funext i
    simp only [pow_two, toAdd_mul, Pi.add_apply, toAdd_one, Pi.zero_apply]
    exact CharTwo.add_self_eq_zero _
  let π : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →*
      ↥(⊤ : Subgroup (MulAut (Multiplicative (Fin 2 → ZMod 2)))) :=
    B1.slHom.codRestrict (⊤ : Subgroup (MulAut (Multiplicative (Fin 2 → ZMod 2))))
      (fun _ => Subgroup.mem_top _)
  have hN : Ch3z.NatBlockData (V := Multiplicative (Fin 2 → ZMod 2)) ⊤ ⊤ 1 := by
    refine ⟨ZMod 2, inferInstance, inferInstance, by simp, π, Subgroup.subtype _, ?_,
      ⟨Subtype.val_injective, fun y => ⟨⟨y, Subgroup.mem_top _⟩, rfl⟩⟩, ?_⟩
    · intro y
      obtain ⟨g, hg⟩ := B1.slHom_surjective y.1
      exact ⟨g, Subtype.ext hg⟩
    · intro γ u hu
      rfl
  have hS := Ch3z.isSymCore_three_of_natBlock hV' (fun _ _ _ _ => Subgroup.mem_top _) hN
  obtain ⟨θ, -⟩ := hS
  let eSL : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) ≃*
      MulAut (Multiplicative (Fin 2 → ZMod 2)) :=
    MulEquiv.ofBijective B1.slHom ⟨B1.slHom_injective, B1.slHom_surjective⟩
  refine ⟨eSL.symm.toMonoidHom.comp
    ((Subgroup.topEquiv (G := MulAut (Multiplicative (Fin 2 → ZMod 2)))).toMonoidHom.comp
      θ.symm.toMonoidHom), ?_⟩
  intro a b hab
  exact θ.symm.injective (Subgroup.topEquiv.injective (eSL.symm.injective hab))

section Blocks

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def HasS3 (H : Subgroup (MulAut V)) : Prop :=
  ∃ ι : Equiv.Perm (Fin 3) →* MulAut V, Function.Injective ι ∧ ∀ σ, ι σ ∈ H

omit [Finite V] in
theorem SymBlk.hasS3 {X H : Subgroup (MulAut V)} {k : ℕ} (h : SymBlk X H k) : HasS3 H := by
  obtain ⟨L, A, -, -, -, -, rfl, hk, π, -, hreal, -, -⟩ := h
  obtain ⟨θ, -⟩ := Ch3z.isSymCore_of_realizes hreal
  have h3 : 3 * 0 + 3 ≤ 2 * k + 1 := by omega
  exact ⟨Ch3z.blockCopy θ 0 h3, Ch3z.blockCopy_injective θ 0 h3, Ch3z.blockCopy_mem θ 0 h3⟩

omit [Finite V] in
theorem NatBlk.hasS3 {X H : Subgroup (MulAut V)} (h : NatBlk X H) : HasS3 H := by
  obtain ⟨L, e, -, -, rfl, he, ⟨K, instK, instF, hK, π, β, hπs, hβs, hβz, hUinv, hβeq⟩, -⟩ := h
  have h2K : (2 : K) = 0 := two_eq_zero_of_card hK
  have hchar : CharP K 2 := (CharP.charP_iff_prime_eq_zero Nat.prime_two).2 (by exact_mod_cast h2K)
  have hπi : Function.Injective π := NatData.injective_of hβs hUinv hβeq
  obtain ⟨ι₃, hι₃⟩ := exists_perm3_hom_sl2
  let f : ZMod 2 →+* K := ZMod.castHom (dvd_refl 2) K
  have hf : Function.Injective f := f.injective
  let g : Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) →* Matrix.SpecialLinearGroup (Fin 2) K :=
    Matrix.SpecialLinearGroup.map f
  have hg : Function.Injective g := fun a b hab =>
    Subtype.ext (Matrix.map_injective hf (congrArg Subtype.val hab))
  refine ⟨(Subgroup.subtype _).comp (π.comp (g.comp ι₃)), ?_, fun σ => (π (g (ι₃ σ))).2⟩
  intro a b hab
  have : π (g (ι₃ a)) = π (g (ι₃ b)) := Subtype.ext hab
  exact hι₃ (hg (hπi this))

theorem blockHasS3 {X T M : Subgroup (MulAut V)} (hB : B69.BlkCtx X T M)
    {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) : HasS3 H := by
  rcases block_type hB hH with h | ⟨k, h⟩
  · exact h.hasS3
  · exact h.hasS3

variable {X : Subgroup (MulAut V)}

omit [Finite V] in
theorem false_of_three_s3 (hX : Ch3z.IsRankTwoQuotient ↥X) {H₁ H₂ H₃ : Subgroup (MulAut V)}
    (h₁X : H₁ ≤ X) (h₂X : H₂ ≤ X) (h₃X : H₃ ≤ X) (h₁ : HasS3 H₁) (h₂ : HasS3 H₂) (h₃ : HasS3 H₃)
    (h12 : ∀ a ∈ H₁, ∀ b ∈ H₂, a * b = b * a) (h13 : ∀ a ∈ H₁, ∀ b ∈ H₃, a * b = b * a)
    (h23 : ∀ a ∈ H₂, ∀ b ∈ H₃, a * b = b * a)
    (hind : ∀ a ∈ H₁, ∀ b ∈ H₂, ∀ c ∈ H₃, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1) : False := by
  obtain ⟨ι₁, hι₁, hm₁⟩ := h₁
  obtain ⟨ι₂, hι₂, hm₂⟩ := h₂
  obtain ⟨ι₃, hι₃, hm₃⟩ := h₃
  obtain ⟨ψ, hψi, hψ⟩ := Ch3z.exists_cube_hom ι₁ ι₂ ι₃
    (fun a b => h12 _ (hm₁ _) _ (hm₂ _)) (fun a c => h13 _ (hm₁ _) _ (hm₃ _))
    (fun b c => h23 _ (hm₂ _) _ (hm₃ _))
    (fun a b c h => by
      obtain ⟨ha, hb, hc⟩ := hind _ (hm₁ _) _ (hm₂ _) _ (hm₃ _) h
      exact ⟨hι₁ (ha.trans (map_one _).symm), hι₂ (hb.trans (map_one _).symm),
        hι₃ (hc.trans (map_one _).symm)⟩)
  have hmem : ∀ x : Ch3z.Cube, ψ x ∈ X := by
    rintro ⟨a, b, c⟩
    rw [hψ]
    exact X.mul_mem (X.mul_mem (h₁X (hm₁ _)) (h₂X (hm₂ _))) (h₃X (hm₃ _))
  exact Ch3z.false_of_cube hX (ψ.codRestrict X hmem) fun x y hxy => hψi (congrArg Subtype.val hxy)

omit [Finite V] in
theorem independent_three {𝓗 : Finset (Subgroup (MulAut V))}
    (hind : ∀ H ∈ 𝓗, H ⊓ ⨆ H' ∈ 𝓗, ⨆ (_ : H' ≠ H), H' = ⊥)
    {H₁ H₂ H₃ : Subgroup (MulAut V)} (h₁ : H₁ ∈ 𝓗) (h₂ : H₂ ∈ 𝓗) (h₃ : H₃ ∈ 𝓗) (h12 : H₁ ≠ H₂)
    (h13 : H₁ ≠ H₃) (h23 : H₂ ≠ H₃) :
    ∀ a ∈ H₁, ∀ b ∈ H₂, ∀ c ∈ H₃, a * b * c = 1 → a = 1 ∧ b = 1 ∧ c = 1 := by
  have hle : ∀ {H H' : Subgroup (MulAut V)}, H ∈ 𝓗 → H' ∈ 𝓗 → H' ≠ H →
      H' ≤ ⨆ H'' ∈ 𝓗, ⨆ (_ : H'' ≠ H), H'' := fun {H H'} hH hH' hne =>
    le_iSup₂_of_le (f := fun (K : Subgroup (MulAut V)) (_ : K ∈ 𝓗) => ⨆ (_ : K ≠ H), K) H' hH'
      (le_iSup (f := fun (_ : H' ≠ H) => H') hne)
  intro a ha b hb c hc habc
  have hbc : b * c ∈ ⨆ H'' ∈ 𝓗, ⨆ (_ : H'' ≠ H₁), H'' :=
    Subgroup.mul_mem _ (hle h₁ h₂ (Ne.symm h12) hb) (hle h₁ h₃ (Ne.symm h13) hc)
  have ha1 : a = 1 := by
    have h1 : a⁻¹ = b * c := by
      rw [inv_eq_iff_mul_eq_one, ← mul_assoc]
      exact habc
    have : a⁻¹ ∈ H₁ ⊓ ⨆ H'' ∈ 𝓗, ⨆ (_ : H'' ≠ H₁), H'' := ⟨H₁.inv_mem ha, h1 ▸ hbc⟩
    rw [hind H₁ h₁, Subgroup.mem_bot, inv_eq_one] at this
    exact this
  subst ha1
  rw [one_mul] at habc
  have hb1 : b = 1 := by
    have h1 : b = c⁻¹ := eq_inv_of_mul_eq_one_left habc
    have : b ∈ H₂ ⊓ ⨆ H'' ∈ 𝓗, ⨆ (_ : H'' ≠ H₂), H'' :=
      ⟨hb, h1 ▸ (Subgroup.inv_mem _ (hle h₂ h₃ (Ne.symm h23) hc))⟩
    rw [hind H₂ h₂, Subgroup.mem_bot] at this
    exact this
  subst hb1
  rw [one_mul] at habc
  exact ⟨rfl, rfl, habc⟩

variable {T M : Subgroup (MulAut V)}

theorem card_blocks_le_two (hB : B69.BlkCtx X T M) (h : MinParabolic X T M) (hFF : IsFFModule X)
    (hX : Ch3z.IsRankTwoQuotient ↥X) : (B69.blkFamily X).card ≤ 2 := by
  by_contra hlt
  push Not at hlt
  obtain ⟨H₁, H₂, H₃, h₁, h₂, h₃, h12, h13, h23⟩ := Finset.two_lt_card_iff.1 hlt
  have sc := B69.structConcl_of_blkCtx hB h hFF
  exact false_of_three_s3 hX (sc.1 _ h₁) (sc.1 _ h₂) (sc.1 _ h₃) (blockHasS3 hB h₁)
    (blockHasS3 hB h₂) (blockHasS3 hB h₃) (sc.2.2.1 _ h₁ _ h₂ h12) (sc.2.2.1 _ h₁ _ h₃ h13)
    (sc.2.2.1 _ h₂ _ h₃ h23) (independent_three sc.2.2.2.1 h₁ h₂ h₃ h12 h13 h23)

omit [Finite V] in
theorem SymBlk.le_three (hX : Ch3z.IsRankTwoQuotient ↥X) {H : Subgroup (MulAut V)} {k : ℕ}
    (h : SymBlk X H k) : k ≤ 3 := by
  by_contra hk
  push Not at hk
  obtain ⟨L, A, hL, hA, -, -, rfl, -, π, -, hreal, -, -⟩ := h
  obtain ⟨θ, -⟩ := Ch3z.isSymCore_of_realizes hreal
  have hLA : L ⊔ A ≤ X := sup_le hL.1 hA.1.1
  exact Ch3z.false_of_one_block hX hLA θ (by omega)

end Blocks

end GE23

end CFSG.Quasithin
