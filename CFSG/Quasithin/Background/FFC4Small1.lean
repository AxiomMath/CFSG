module

public import CFSG.Quasithin.Background.FFC4Pair
public import CFSG.Quasithin.Background.FFC4Tr2

public section

namespace CFSG.Quasithin

namespace FFC

open CFSG.Assembly.LowTwoRank Matrix

theorem eq_one_of_fixed_nat {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K] (m : Multiplicative (Fin d → K))
    (h : ∀ γ : ↥(StatedSL d K), natAct (StatedSL d K) γ m = m) : m = 1 := by
  by_contra hm
  have hv : Multiplicative.toAdd m ≠ 0 := fun h0 => hm (by rw [← ofAdd_toAdd m, h0]; rfl)
  obtain ⟨j, hj⟩ : ∃ j, Multiplicative.toAdd m j ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hv (funext hcon)
  obtain ⟨i, hij⟩ : ∃ i : Fin d, i ≠ j := by
    by_cases hj0 : j.val = 0
    · exact ⟨⟨1, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
    · exact ⟨⟨0, by omega⟩, fun h' => by have := congrArg Fin.val h'; simp at this; omega⟩
  have hdet : (transvection i j (1 : K)).det = 1 := det_transvection_of_ne i j hij 1
  let γ : ↥(StatedSL d K) := specialLinearGroupEquivStatedSL d K ⟨transvection i j (1 : K), hdet⟩
  have hγ : ((γ : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = transvection i j (1 : K) := rfl
  have h1 := congrArg Multiplicative.toAdd (h γ)
  have h2 := congrFun h1 i
  simp only [natAct, hγ, toAdd_ofAdd, transvection, add_mulVec, one_mulVec, Pi.add_apply,
    add_eq_left] at h2
  apply hj
  simpa [mulVec, dotProduct, Matrix.single_apply] using h2

section Fixed

variable {W : Type*} [CommGroup W]

theorem fixV_inf_eq_bot_of_nat {d : ℕ} (hd : 2 ≤ d) {K : Type} [Field K] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {π : ↥(StatedSL d K) →* ↥L}
    (h : (FFModel.nat (StatedSL d K)).RealizesVia L I ⊥ π) : fixV L ⊓ I = ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hufix, huI⟩
  obtain ⟨-, -, -, hHU, -, hsec, -, β, hβs, hβk, hβe⟩ := h
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨u, huI⟩)
  have hfix : ∀ γ : ↥(StatedSL d K), natAct (StatedSL d K) γ m.1 = m.1 := by
    intro γ
    have hmem : ((π γ : ↥L) : MulAut W) u ∈ I := hHU (π γ) u huI
    have heq : (⟨((π γ : ↥L) : MulAut W) ((⟨u, huI⟩ : ↥I) : W), hmem⟩ : ↥I) = ⟨u, huI⟩ :=
      Subtype.ext (hufix _ (π γ).2)
    have h1 := hβe γ ⟨u, huI⟩ m hmem (hsec γ m m.2) hm.symm
    have h1' : (QuotientGroup.mk m : ↥(FFModel.nat (StatedSL d K)).sec ⧸
        (FFModel.nat (StatedSL d K)).ker.subgroupOf (FFModel.nat (StatedSL d K)).sec) =
        QuotientGroup.mk ⟨(FFModel.nat (StatedSL d K)).act γ m.1, hsec γ m m.2⟩ :=
      hm.trans ((congrArg β heq).symm.trans h1)
    have h2 := QuotientGroup.eq.1 h1'
    rw [Subgroup.mem_subgroupOf] at h2
    have h3 : (m⁻¹ * ⟨(FFModel.nat (StatedSL d K)).act γ m.1, hsec γ m m.2⟩ :
        ↥(FFModel.nat (StatedSL d K)).sec) = 1 := Subtype.ext (Subgroup.mem_bot.1 h2)
    have h4 := congrArg Subtype.val (inv_mul_eq_one.1 h3)
    exact h4.symm
  have hm1 : m.1 = 1 := eq_one_of_fixed_nat hd _ hfix
  have : β ⟨u, huI⟩ = 1 := by
    rw [← hm]
    have : m = 1 := Subtype.ext hm1
    rw [this]
    rfl
  exact Subgroup.mem_bot.2 (by simpa using (hβk _).1 this)


theorem ne_bot_of_nat {d : ℕ} (hd : 1 ≤ d) {K : Type} [Field K] {L : Subgroup (MulAut W)}
    {I : Subgroup W} {π : ↥(StatedSL d K) →* ↥L}
    (h : (FFModel.nat (StatedSL d K)).RealizesVia L I ⊥ π) : I ≠ ⊥ := by
  intro hI
  obtain ⟨-, -, -, -, -, -, -, β, hβs, -, -⟩ := h
  let x : ↥(FFModel.nat (StatedSL d K)).sec :=
    ⟨Multiplicative.ofAdd (Pi.single ⟨0, by omega⟩ (1 : K) : Fin d → K), Subgroup.mem_top _⟩
  obtain ⟨u, hu⟩ := hβs (QuotientGroup.mk x)
  have hu1 : u = 1 := by
    apply Subtype.ext
    have h0 : (u : W) ∈ (⊥ : Subgroup W) := hI ▸ u.2
    exact Subgroup.mem_bot.1 h0
  have h1 : (QuotientGroup.mk x : ↥(FFModel.nat (StatedSL d K)).sec ⧸
      (FFModel.nat (StatedSL d K)).ker.subgroupOf (FFModel.nat (StatedSL d K)).sec) = 1 := by
    rw [← hu, hu1, map_one]
  rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h1
  have h2 : x.1 = 1 := Subgroup.mem_bot.1 h1
  have h3 : (Pi.single (⟨0, by omega⟩ : Fin d) (1 : K) : Fin d → K) = 0 :=
    Multiplicative.ofAdd.injective h2
  have h4 := congrFun h3 ⟨0, by omega⟩
  simp at h4

end Fixed

section CaseII

variable {W : Type} [CommGroup W]

theorem inf_eq_bot_of_indep {I : Fin 2 → Subgroup W} (hind : iSupIndep I) {i j : Fin 2} (hij : i ≠ j) :
    I i ⊓ I j = ⊥ :=
  disjoint_iff.1 (hind.pairwiseDisjoint hij)

theorem iSup_fin_two_eq (I : Fin 2 → Subgroup W) : (⨆ i, I i) = I 0 ⊔ I 1 := by
  refine le_antisymm (iSup_le fun i => ?_) (sup_le (le_iSup I 0) (le_iSup I 1))
  fin_cases i
  · exact le_sup_left
  · exact le_sup_right

theorem iSup_ne_eq (I : Fin 2 → Subgroup W) (i : Fin 2) :
    (⨆ (j : Fin 2) (_ : j ≠ i), I j) = I (1 - i) := by
  have hj : ∀ i j : Fin 2, j ≠ i → j = 1 - i := by decide
  have hne : ∀ i : Fin 2, (1 - i) ≠ i := by decide
  refine le_antisymm (iSup₂_le fun j hj' => ?_)
    (le_iSup₂ (f := fun (j : Fin 2) (_ : j ≠ i) => I j) (1 - i) (hne i))
  rw [hj i j hj']

theorem fixed_of_two_summands {L : Subgroup (MulAut W)} {I₀ I₁ : Subgroup W}
    (hinv₀ : ∀ g ∈ L, ∀ x ∈ I₀, g x ∈ I₀) (hinv₁ : ∀ g ∈ L, ∀ x ∈ I₁, g x ∈ I₁)
    (hinf : I₀ ⊓ I₁ = ⊥) {y z : W} (hy : y ∈ I₀) (hz : z ∈ I₁)
    (hfix : ∀ g ∈ L, g (y * z) = y * z) : ∀ g ∈ L, g y = y ∧ g z = z := by
  intro g hg
  have h1' : g y * g z = y * z := by rw [← map_mul]; exact hfix g hg
  have key : (g y * y⁻¹) * (g z * z⁻¹) = 1 := by
    rw [mul_mul_mul_comm, h1', ← mul_inv, mul_inv_cancel]
  have hinv : g y * y⁻¹ = (g z * z⁻¹)⁻¹ := mul_eq_one_iff_eq_inv.1 key
  have h2 : g y * y⁻¹ ∈ I₀ ⊓ I₁ := by
    refine ⟨I₀.mul_mem (hinv₀ g hg y hy) (I₀.inv_mem hy), ?_⟩
    rw [hinv]
    exact I₁.inv_mem (I₁.mul_mem (hinv₁ g hg z hz) (I₁.inv_mem hz))
  rw [hinf, Subgroup.mem_bot, mul_inv_eq_one] at h2
  refine ⟨h2, ?_⟩
  have h3 : (g z * z⁻¹) = 1 := by
    rw [h2, mul_inv_cancel, one_mul] at key
    exact key
  exact mul_inv_eq_one.1 h3

theorem not_mem_irrPlus_of_two_summands {L : Subgroup (MulAut W)} {I : Fin 2 → Subgroup W} {K : Type}
    [Field K] {π : ↥(StatedSL 3 K) →* ↥L} (hind : iSupIndep I) (hsup : (⨆ i, I i) = commV L)
    (hreal : ∀ i, (FFModel.nat (StatedSL 3 K)).RealizesVia L (I i) ⊥ π) :
    commV L ∉ IrrPlus L ⊤ := by
  rintro ⟨-, -, -, hbot, hirr⟩
  have hinv : ∀ i, XMod.IsInv ↥L (I i) := fun i a l hl => (hreal i).2.2.2.1 a l hl
  have hinv' : ∀ i, ∀ g ∈ L, ∀ x ∈ I i, g x ∈ I i := fun i g hg x hx => hinv i ⟨g, hg⟩ x hx
  have hI01 : I 0 ⊓ I 1 = ⊥ := inf_eq_bot_of_indep hind (by decide)
  have hfixed : XMod.fixed ↥L (commV L) = ⊥ := by
    rw [eq_bot_iff]
    intro l hl
    have hl' : l ∈ I 0 ⊔ I 1 := by rw [← iSup_fin_two_eq, hsup]; exact hl.1
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.1 hl'
    have hyz := fixed_of_two_summands (hinv' 0) (hinv' 1) hI01 hy hz (fun g hg => hl.2 ⟨g, hg⟩)
    have hy1 : y ∈ fixV L ⊓ I 0 :=
      ⟨fun g hg => (hyz g hg).1, hy⟩
    have hz1 : z ∈ fixV L ⊓ I 1 :=
      ⟨fun g hg => (hyz g hg).2, hz⟩
    rw [fixV_inf_eq_bot_of_nat (by norm_num) (hreal 0), Subgroup.mem_bot] at hy1
    rw [fixV_inf_eq_bot_of_nat (by norm_num) (hreal 1), Subgroup.mem_bot] at hz1
    rw [hy1, hz1, mul_one]
    exact Subgroup.one_mem _
  rw [hfixed] at hirr
  rcases hirr (I 0) (hinv 0) bot_le (hsup ▸ le_iSup I 0) with h0 | h0
  · exact ne_bot_of_nat (by norm_num) (hreal 0) h0
  · have h1 : I 1 ≤ I 0 := by
      rw [h0, ← hsup, iSup_fin_two_eq]
      exact le_sup_right
    have : I 1 = ⊥ := by
      rw [eq_bot_iff, ← hI01]
      exact le_inf h1 le_rfl
    exact ne_bot_of_nat (by norm_num) (hreal 1) this


theorem one_le_of_card_field {K : Type} [Field K] [Finite K] {n : ℕ} (h : Nat.card K = 2 ^ n) :
    1 ≤ n := by
  by_contra hn
  have : n = 0 := by omega
  subst this
  have h1 : Nat.card K = 1 := by simpa using h
  have : Nontrivial K := inferInstance
  have := Finite.one_lt_card_iff_nontrivial.2 this
  omega

theorem false_of_case_iii {H L : Subgroup (MulAut W)} (hLH : L ≤ H) (hno : ¬ ThreeRank2 ↥H) {n : ℕ}
    (h : SumNatDual L (commV L) n) : False := by
  obtain ⟨hn, π, U₁, U₂, -, h₁, -⟩ := h
  have hn4 : 4 ≤ n := by omega
  exact hno ((threeRank2_of_realizes (FFModel.nat_faithful _) h₁
    (threeRank2_statedSL hn4)).of_le hLH)

theorem false_of_case_iv {H L : Subgroup (MulAut W)} (hLH : L ≤ H) (hno : ¬ ThreeRank2 ↥H)
    (h : ∃ n : ℕ, (n = 4 ∨ n = 5) ∧ ∃ k : ℕ, 1 ≤ k ∧ k ≤ n - 1 ∧
      DirectSumOfCopies L (commV L) ⊥ (FFModel.nat (StatedSL n (ZMod 2))) k) : False := by
  obtain ⟨n, hn, k, hk1, -, I, π, -, -, -, hreal⟩ := h
  have := hreal ⟨0, by omega⟩
  exact hno ((threeRank2_of_realizes (FFModel.nat_faithful _) this
    (threeRank2_statedSL (by omega))).of_le hLH)

theorem good_of_natural_alpha {H : Subgroup (MulAut W)} {U Z : Subgroup W}
    (hα : U ⊔ fixV H = ⊤) (hUZ : U ⊓ fixV H = Z) (hUc : commV H = U)
    (hnat : (∃ n, BinaryNaturalSL H U Z 2 n) ∨ (∃ m, Odd m ∧ BinaryNaturalSL H U Z 3 m)) :
    GoodFactor H := by
  have hCinv : ∀ g : ↥H, ∀ c ∈ fixV H, (g : MulAut W) c ∈ fixV H := fun g c hc => by
    rw [hc g g.2]; exact hc
  have hT : (⊤ : Subgroup W) = commV H ⊔ fixV H := by rw [hUc, hα]
  rcases hnat with ⟨n, K, hK, hf, hc, π, hπ⟩ | ⟨m, hm, K, hK, hf, hc, π, hπ⟩
  · have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    have hext := RealizesVia.extend hπ hCinv hUZ
    rw [hα] at hext
    refine ⟨Or.inl ⟨n, K, hK, hf, one_le_of_card_field hc, hc,
      ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩, Or.inl ⟨hT, Or.inl ⟨n, K, hK, hf, hc, π, hext⟩⟩⟩
  · have hinj : Function.Injective π := injective_of_faithful_sec (FFModel.nat_faithful _) hπ
    have hext := RealizesVia.extend hπ hCinv hUZ
    rw [hα] at hext
    refine ⟨Or.inr (Or.inr ⟨m, K, hK, hf, one_le_of_card_field hc, hm, hc,
      ⟨(MulEquiv.ofBijective π ⟨hinj, hπ.1⟩).symm⟩⟩),
      Or.inl ⟨hT, Or.inr (Or.inr ⟨m, K, hK, hf, hc, π, hext⟩)⟩⟩


theorem good_of_case_ii [Finite W] {H : Subgroup (MulAut W)} (hno : ¬ ThreeRank2 ↥H)
    (hP5 : commV H ⊔ fixV H = ⊤ ∨ commV H ∈ IrrPlus H ⊤) (h : B51Case1ii H H) : GoodFactor H := by
  obtain ⟨-, n, K, hK, hf, hc, I, π, hind, hsup, hreal, -, -⟩ := h
  have hα : commV H ⊔ fixV H = ⊤ :=
    hP5.resolve_right (not_mem_irrPlus_of_two_summands hind hsup hreal)
  have hπinj : Function.Injective π :=
    injective_of_faithful_sec (FFModel.nat_faithful _) (hreal 0)
  have hnodd : Odd n := by
    by_contra hn
    obtain ⟨ζ, hζ3, hζ1⟩ := exists_unit_order_three hc (Nat.not_odd_iff_even.1 hn)
    exact hno (threeRank2_of_realizes (FFModel.nat_faithful _) (hreal 0)
      (threeRank2_statedSL_three hζ3 hζ1))
  have hinv : ∀ i, ∀ g ∈ H, ∀ x ∈ I i, g x ∈ I i := fun i g hg x hx => (hreal i).2.2.2.1 ⟨g, hg⟩ x hx
  have hCinv : ∀ g : ↥H, ∀ c ∈ fixV H, (g : MulAut W) c ∈ fixV H := fun g c hc => by
    rw [hc g g.2]; exact hc
  have hIC : ∀ i, I i ⊓ fixV H = ⊥ := fun i => by
    rw [inf_comm]; exact fixV_inf_eq_bot_of_nat (by norm_num) (hreal i)
  have hkey : ∀ i j : Fin 2, i ≠ j → I i ⊓ (fixV H ⊔ I j) = ⊥ := by
    intro i j hij
    rw [eq_bot_iff]
    rintro x ⟨hxi, hxj⟩
    obtain ⟨c, hc', y, hy, rfl⟩ := Subgroup.mem_sup.1 hxj
    have hcomm : ∀ g ∈ H, g (c * y) * (c * y)⁻¹ ∈ I i ⊓ I j := by
      intro g hg
      refine ⟨(I i).mul_mem (hinv i g hg _ hxi) ((I i).inv_mem hxi), ?_⟩
      have : g (c * y) * (c * y)⁻¹ = g y * y⁻¹ := by
        rw [map_mul, hc' g hg, mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rw [this]
      exact (I j).mul_mem (hinv j g hg y hy) ((I j).inv_mem hy)
    have hfix : ∀ g ∈ H, g (c * y) = c * y := fun g hg => by
      have := hcomm g hg
      rw [inf_eq_bot_of_indep hind hij, Subgroup.mem_bot, mul_inv_eq_one] at this
      exact this
    have : (c * y) ∈ fixV H ⊓ I i := ⟨fun g hg => hfix g hg, hxi⟩
    rw [fixV_inf_eq_bot_of_nat (by norm_num) (hreal i), Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  have hdirect : DirectSumOfCopies H ⊤ (fixV H) (FFModel.nat (StatedSL 3 K)) 2 := by
    refine ⟨fun i => I i ⊔ fixV H, π, fun i => le_sup_right, ?_, ?_, ?_⟩
    · intro i
      have h1 : (⨆ (j : Fin 2) (_ : j ≠ i), (fun j => I j ⊔ fixV H) j) = I (1 - i) ⊔ fixV H :=
        iSup_ne_eq (fun j => I j ⊔ fixV H) i
      rw [h1]
      have hne : i ≠ 1 - i := (by decide : ∀ i : Fin 2, i ≠ 1 - i) i
      have h2 : fixV H ⊔ (I (1 - i) ⊔ fixV H) = fixV H ⊔ I (1 - i) := by
        rw [sup_comm (I (1 - i)), ← sup_assoc, sup_idem]
      show (I i ⊔ fixV H) ⊓ (fixV H ⊔ (I (1 - i) ⊔ fixV H)) = fixV H
      rw [h2, sup_comm (I i), sup_inf_assoc_of_le _ le_sup_left, hkey i (1 - i) hne, sup_bot_eq]
    · refine le_antisymm le_top ?_
      rw [← hα, ← hsup, iSup_fin_two_eq]
      refine sup_le (sup_le ?_ ?_) ?_
      · exact le_sup_of_le_right (le_iSup_of_le 0 le_sup_left)
      · exact le_sup_of_le_right (le_iSup_of_le 1 le_sup_left)
      · exact le_sup_left
    · intro i
      exact RealizesVia.extend (hreal i) hCinv (hIC i)
  refine ⟨Or.inr (Or.inr ⟨n, K, hK, hf, one_le_of_card_field hc, hnodd, hc,
    ⟨(MulEquiv.ofBijective π ⟨hπinj, (hreal 0).1⟩).symm⟩⟩),
    Or.inr (Or.inl ⟨hα.symm, n, K, hK, hf, hc, hdirect⟩)⟩

end CaseII


end FFC

end CFSG.Quasithin
