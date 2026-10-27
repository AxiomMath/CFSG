module

public import CFSG.Quasithin.Background.FFC5S3
public import CFSG.Quasithin.Background.FFC4Small1
public import CFSG.Quasithin.Background.FFC5Res

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank

section Piece

variable {V : Type} [CommGroup V]

theorem B511Split.fixV_inf_comm {G G₁ G₂ : Subgroup (MulAut V)} (h : B511Split G G₁ G₂) :
    fixV G ⊓ commV G₁ = fixV G₁ ⊓ commV G₁ := by
  apply le_antisymm
  · exact inf_le_inf_right _ (B1.fixV_le_fixV h.G₁_le)
  · rintro x ⟨hx1, hx2⟩
    refine ⟨?_, hx2⟩
    rw [← h.sup, fixV_sup]
    exact ⟨hx1, fun b hb => h.triv₁ b hb x hx2⟩

theorem extend_fixV {G G₁ : Subgroup (MulAut V)} (hGG : G₁ ≤ G) {D : FFModel} {U Z : Subgroup V}
    {π : D.Gam →* ↥G₁} (hπ : D.RealizesVia G₁ U Z π) (hUZ : U ⊓ fixV G = Z) :
    D.RealizesVia G₁ (U ⊔ fixV G) (fixV G) π :=
  RealizesVia.extend hπ (fun g c hc => by rw [hc g (hGG g.2)]; exact hc) hUZ

theorem fixV_inf_eq_bot_of_model {D : FFModel} (hker : D.ker = ⊥)
    (hfix : ∀ m ∈ D.sec, (∀ γ : D.Gam, D.act γ m = m) → m = 1) {H : Subgroup (MulAut V)}
    {U : Subgroup V} {π : D.Gam →* ↥H} (h : D.RealizesVia H U ⊥ π) : fixV H ⊓ U = ⊥ := by
  obtain ⟨f, hfs, hfk, hfe⟩ := RealizesVia.secMap hker h
  rw [eq_bot_iff]
  rintro u ⟨hufix, huU⟩
  have hf1 : (f ⟨u, huU⟩ : D.Amb) = 1 := by
    apply hfix _ (f ⟨u, huU⟩).2
    intro γ
    have hmem : ((π γ : ↥H) : MulAut V) u ∈ U := h.2.2.2.1 (π γ) u huU
    have h1 := hfe γ ⟨u, huU⟩ hmem
    have h2 : (⟨((π γ : ↥H) : MulAut V) u, hmem⟩ : ↥U) = ⟨u, huU⟩ :=
      Subtype.ext (hufix _ (π γ).2)
    rw [h2] at h1
    exact h1.symm
  have : f ⟨u, huU⟩ = 1 := Subtype.ext hf1
  have := (hfk ⟨u, huU⟩).1 this
  exact this

theorem eq_one_of_fixed_perm_five (m : G6.PermMod 5) (hm : m ∈ G6.coreMod 5)
    (h : ∀ σ : Equiv.Perm (Fin 5), G6.permAct 5 σ m = m) : m = 1 := by
  have hconst : ∀ i j : Fin 5, Multiplicative.toAdd m i = Multiplicative.toAdd m j := by
    intro i j
    have := congrArg (fun z : G6.PermMod 5 => Multiplicative.toAdd z i) (h (Equiv.swap i j))
    simpa [G6.permAct_apply] using this.symm
  have hs : (∑ i : Fin 5, Multiplicative.toAdd m i) = 0 := hm
  have h0 : Multiplicative.toAdd m 0 = 0 := by
    have hsum : (∑ i : Fin 5, Multiplicative.toAdd m i) = ∑ _i : Fin 5, Multiplicative.toAdd m 0 :=
      Finset.sum_congr rfl fun i _ => hconst i 0
    rw [hsum, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hs
    have h5 : ((5 : ℕ) : ZMod 2) = 1 := by decide
    rwa [h5, one_mul] at hs
  apply Multiplicative.toAdd.injective
  funext i
  rw [hconst i 0, h0]
  rfl

theorem fixV_inf_eq_bot_of_sym5 {H : Subgroup (MulAut V)} {U : Subgroup V}
    {π : Equiv.Perm (Fin 5) →* ↥H} (h : (FFModel.symDn 5).RealizesVia H U ⊥ π) : fixV H ⊓ U = ⊥ :=
  fixV_inf_eq_bot_of_model symDn_ker_five (fun m hm hfix => eq_one_of_fixed_perm_five m hm hfix) h

theorem directSum_extend {L : Subgroup (MulAut V)} {C U : Subgroup V} {K : Type} [Field K]
    {π : ↥(StatedSL 3 K) →* ↥L} (hC : C ≤ fixV L) (I : Fin 2 → Subgroup V)
    (hind : ∀ i, I i ⊓ (⊥ ⊔ ⨆ (j : Fin 2) (_ : j ≠ i), I j) = ⊥) (hsup : (⊥ ⊔ ⨆ i, I i) = U)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 K)).RealizesVia L (I i) ⊥ π) :
    DirectSumOfCopies L (U ⊔ C) C (FFModel.nat (StatedSL 3 K)) 2 := by
  have hinv : ∀ i, ∀ g ∈ L, ∀ x ∈ I i, g x ∈ I i := fun i g hg x hx => (hreal i).2.2.2.1 ⟨g, hg⟩ x hx
  have hCinv : ∀ g : ↥L, ∀ c ∈ C, (g : MulAut V) c ∈ C := fun g c hc => by
    rw [hC hc g g.2]; exact hc
  have hI01 : I 0 ⊓ I 1 = ⊥ := by
    have := hind 0
    rw [iSup_ne_eq, bot_sup_eq] at this
    exact this
  have hIC : ∀ i, I i ⊓ C = ⊥ := fun i => by
    have h0 := fixV_inf_eq_bot_of_nat (by norm_num : 2 ≤ 3) (hreal i)
    rw [eq_bot_iff]
    rintro x ⟨hx1, hx2⟩
    have : x ∈ fixV L ⊓ I i := ⟨hC hx2, hx1⟩
    rw [h0] at this
    exact this
  have hkey : ∀ i j : Fin 2, i ≠ j → I i ⊓ (C ⊔ I j) = ⊥ := by
    intro i j hij
    rw [eq_bot_iff]
    rintro x ⟨hxi, hxj⟩
    obtain ⟨c, hc', y, hy, rfl⟩ := Subgroup.mem_sup.1 hxj
    have hI : I i ⊓ I j = ⊥ := by
      have h01 : ∀ a b : Fin 2, a ≠ b → I a ⊓ I b = ⊥ := by
        intro a b hab
        fin_cases a <;> fin_cases b
        · exact absurd rfl hab
        · exact hI01
        · rw [inf_comm]; exact hI01
        · exact absurd rfl hab
      exact h01 i j hij
    have hcomm : ∀ g ∈ L, g (c * y) * (c * y)⁻¹ ∈ I i ⊓ I j := by
      intro g hg
      refine ⟨(I i).mul_mem (hinv i g hg _ hxi) ((I i).inv_mem hxi), ?_⟩
      have : g (c * y) * (c * y)⁻¹ = g y * y⁻¹ := by
        rw [map_mul, hC hc' g hg, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rw [this]
      exact (I j).mul_mem (hinv j g hg y hy) ((I j).inv_mem hy)
    have hfix : ∀ g ∈ L, g (c * y) = c * y := fun g hg => by
      have := hcomm g hg
      rw [hI, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    have : (c * y) ∈ fixV L ⊓ I i := ⟨fun g hg => hfix g hg, hxi⟩
    rw [fixV_inf_eq_bot_of_nat (by norm_num : 2 ≤ 3) (hreal i), Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  refine ⟨fun i => I i ⊔ C, π, fun i => le_sup_right, ?_, ?_, ?_⟩
  · intro i
    have h1 : (⨆ (j : Fin 2) (_ : j ≠ i), (fun j => I j ⊔ C) j) = I (1 - i) ⊔ C :=
      iSup_ne_eq (fun j => I j ⊔ C) i
    rw [h1]
    have hne : i ≠ 1 - i := (by decide : ∀ i : Fin 2, i ≠ 1 - i) i
    have h2 : C ⊔ (I (1 - i) ⊔ C) = C ⊔ I (1 - i) := by
      rw [sup_comm (I (1 - i)), ← sup_assoc, sup_idem]
    show (I i ⊔ C) ⊓ (C ⊔ (I (1 - i) ⊔ C)) = C
    rw [h2, sup_comm (I i), sup_inf_assoc_of_le _ le_sup_left, hkey i (1 - i) hne, sup_bot_eq]
  · have hU : (⨆ i, I i) = U := by rw [← hsup, bot_sup_eq]
    show C ⊔ ⨆ i, (I i ⊔ C) = U ⊔ C
    apply le_antisymm
    · refine sup_le le_sup_right (iSup_le fun i => sup_le (le_sup_of_le_left ?_) le_sup_right)
      rw [← hU]
      exact le_iSup I i
    · refine sup_le ?_ le_sup_left
      rw [← hU]
      exact iSup_le fun i => (le_sup_left : I i ≤ I i ⊔ C).trans
        ((le_iSup (fun i => I i ⊔ C) i).trans le_sup_right)
  · intro i
    exact RealizesVia.extend (hreal i) hCinv (hIC i)

section Cases

variable {G L A G₂ : Subgroup (MulAut V)}

theorem piece_case1 (h : B511Split G L G₂) {n : ℕ}
    (hn : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 2 n) :
    (B56FactorList ↥L ∧ B56Piece L (commV L ⊔ fixV G) (fixV G)) ∧ S3Elems ↥L := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hUZ : commV L ⊓ fixV G = fixV L ⊓ commV L := by rw [inf_comm]; exact h.fixV_inf_comm
  have hext := extend_fixV h.G₁_le hπ hUZ
  have : CharP K 2 := charP_two_of_card_pow hc
  exact ⟨⟨Or.inl ⟨n, K, hK, hf, one_le_of_card_field hc, hc,
    ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩,
    Or.inl ⟨rfl, Or.inl ⟨n, K, hK, hf, hc, π, hext⟩⟩⟩, s3Elems_statedSL_two.of_injective π hinj⟩

theorem piece_case2 (h : B511Split G (L ⊔ A) G₂) (hc : commV (L ⊔ A) = commV L)
    (hs : Nonempty (↥(L ⊔ A) ≃* Equiv.Perm (Fin 5))) (hsym : SymmetricNatural (L ⊔ A) (commV L) ⊥ 5) :
    (B56FactorList ↥(L ⊔ A) ∧ B56Piece (L ⊔ A) (commV (L ⊔ A) ⊔ fixV G) (fixV G)) ∧
      S3Elems ↥(L ⊔ A) := by
  obtain ⟨π, hπ⟩ : ∃ π : Equiv.Perm (Fin 5) →* ↥(L ⊔ A),
      (FFModel.symDn 5).RealizesVia (L ⊔ A) (commV L) ⊥ π := hsym
  have hbot : fixV (L ⊔ A) ⊓ commV L = ⊥ := fixV_inf_eq_bot_of_sym5 hπ
  have hUZ : commV L ⊓ fixV G = ⊥ := by
    have h1 := h.fixV_inf_comm
    rw [hc, hbot] at h1
    rw [inf_comm]
    exact h1
  have hext := extend_fixV h.G₁_le hπ hUZ
  rw [← hc] at hext
  exact ⟨⟨Or.inr (Or.inl hs), Or.inl ⟨rfl, Or.inr (Or.inl ⟨π, hext⟩)⟩⟩,
    S3Elems.of_mulEquiv hs.some.symm s3Elems_perm_five⟩

theorem piece_case3 (h : B511Split G L G₂) {m : ℕ} {K : Type} [Field K] [Finite K] (hm : Odd m)
    (hc : Nat.card K = 2 ^ m) (hd : DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (StatedSL 3 K)) 2) :
    (B56FactorList ↥L ∧ B56Piece L (commV L ⊔ fixV G) (fixV G)) ∧ S3Elems ↥L := by
  have hCfix : fixV G ≤ fixV L := B1.fixV_le_fixV h.G₁_le
  obtain ⟨I, π, -, hind, hsup, hreal⟩ := hd
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0)
  have : CharP K 2 := charP_two_of_card_pow hc
  have hdir := directSum_extend (π := π) hCfix I hind hsup hreal
  exact ⟨⟨Or.inr (Or.inr ⟨m, K, inferInstance, inferInstance, one_le_of_card_field hc, hm, hc,
    ⟨(MulEquiv.ofBijective π ⟨hinj, (hreal 0).1⟩).symm⟩⟩),
    Or.inr (Or.inl ⟨rfl, m, K, inferInstance, inferInstance, hc, by rw [← hsup] at hdir ⊢; simpa using hdir⟩)⟩,
    s3Elems_statedSL_three.of_injective π hinj⟩

theorem piece_case4 (h : B511Split G L G₂) {m : ℕ} (hm : Odd m)
    (hn : BinaryNaturalSL L (commV L) ⊥ 3 m) :
    (B56FactorList ↥L ∧ B56Piece L (commV L ⊔ fixV G) (fixV G)) ∧ S3Elems ↥L := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
  have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
  have hbot : fixV L ⊓ commV L = ⊥ := fixV_inf_eq_bot_of_nat (by norm_num : 2 ≤ 3) hπ
  have hUZ : commV L ⊓ fixV G = ⊥ := by
    have h1 := h.fixV_inf_comm
    rw [hbot] at h1
    rw [inf_comm]
    exact h1
  have hext := extend_fixV h.G₁_le hπ hUZ
  have : CharP K 2 := charP_two_of_card_pow hc
  exact ⟨⟨Or.inr (Or.inr ⟨m, K, hK, hf, one_le_of_card_field hc, hm, hc,
    ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩),
    Or.inl ⟨rfl, Or.inr (Or.inr ⟨m, K, hK, hf, hc, π, hext⟩)⟩⟩,
    s3Elems_statedSL_three.of_injective π hinj⟩

theorem piece_case5 (h : B511Split G L G₂) (hiso : Nonempty (↥L ≃* ↥(StatedSL 3 (ZMod 2))))
    (hn : BinaryNaturalSL L (commV L) (fixV L ⊓ commV L) 3 1) :
    (B56FactorList ↥L ∧ B56Piece L (commV L ⊔ fixV G) (fixV G)) ∧ S3Elems ↥L := by
  obtain ⟨K, hK, hf, hc, π, hπ⟩ := hn
  have hUZ : commV L ⊓ fixV G = fixV L ⊓ commV L := by rw [inf_comm]; exact h.fixV_inf_comm
  have hext := extend_fixV h.G₁_le hπ hUZ
  exact ⟨⟨Or.inr (Or.inr ⟨1, ZMod 2, inferInstance, inferInstance, le_rfl, odd_one, by simp, hiso⟩),
    Or.inl ⟨rfl, Or.inr (Or.inr ⟨1, K, hK, hf, hc, π, hext⟩)⟩⟩,
    s3Elems_statedSL_three.of_mulEquiv hiso.some.symm⟩

end Cases

end Piece

end FFC

end CFSG.Quasithin
