module

public import CFSG.Quasithin.EmptyFaithful.S1565L13
public import CFSG.Quasithin.EmptyFaithful.F918C13

public section

namespace CFSG.Quasithin

open CFSG.Assembly.LowTwoRank Matrix

section Conj

variable {W : Type} [CommGroup W]

theorem borel_transport {X : Type} [Group X] {L Q : Subgroup X} (g : X) (hgQ : g ∈ Q)
    (hSQ : ∃ S : Sylow 2 ↥L, ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L), (b : X) ∈ Q) :
    ∃ S₂ : Sylow 2 ↥(L.map (MulAut.conj g).toMonoidHom),
      ∀ b ∈ Subgroup.normalizer ((S₂ : Subgroup ↥(L.map (MulAut.conj g).toMonoidHom)) :
        Set ↥(L.map (MulAut.conj g).toMonoidHom)), (b : X) ∈ Q := by
  obtain ⟨S, hS⟩ := hSQ
  let e : ↥L ≃* ↥(L.map (MulAut.conj g).toMonoidHom) := (MulAut.conj g).subgroupMap L
  let S₂ : Sylow 2 ↥(L.map (MulAut.conj g).toMonoidHom) :=
    S.comapOfInjective e.symm.toMonoidHom e.symm.injective
      (by rw [MonoidHom.range_eq_top.mpr e.symm.surjective]; exact le_top)
  refine ⟨S₂, fun b hb => ?_⟩
  have hmem : ∀ h, h ∈ (S₂ : Subgroup ↥(L.map (MulAut.conj g).toMonoidHom)) ↔
      e.symm h ∈ (S : Subgroup ↥L) := fun h => Iff.rfl
  have hbN : e.symm b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L) := by
    rw [Subgroup.mem_normalizer_iff] at hb ⊢
    intro h
    have := hb (e h)
    rw [hmem, hmem, map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply] at this
    exact this
  have h1 := hS _ hbN
  have h2 : (b : X) = g * ((e.symm b : ↥L) : X) * g⁻¹ := by
    have h3 : ((e (e.symm b) : ↥(L.map (MulAut.conj g).toMonoidHom)) : X) = (b : X) :=
      congrArg Subtype.val (e.apply_symm_apply b)
    rw [← h3]
    show (MulAut.conj g) ((e.symm b : ↥L) : X) = _
    rw [MulAut.conj_apply]
  rw [h2]
  exact Q.mul_mem (Q.mul_mem hgQ h1) (Q.inv_mem hgQ)

end Conj

section Good

variable {W : Type} [CommGroup W] [Finite W]

theorem modFiveIii_good {Mp T L₀ : Subgroup (MulAut W)}
    {V : Subgroup W} {τ : MulAut W} {Q : Subgroup (MulAut W)} (hτQ : τ ∈ Q) (hLMp : L₀ ≤ Mp)
    (hτMp : τ ∈ Subgroup.normalizer (Mp : Set (MulAut W)))
    (hτ2 : ∀ g ∈ L₀, τ⁻¹ * g * τ ∈ conjAutSub τ L₀)
    (hcomm : ∀ g ∈ L₀, ∀ g' ∈ conjAutSub τ L₀, g * g' = g' * g)
    (hSQ : ∃ S : Sylow 2 ↥L₀, ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥L₀) : Set ↥L₀),
      (b : MulAut W) ∈ Q)
    {n : ℕ} (hn3 : 3 ≤ n) (hshape : IsPSL 2 2 n ↥L₀ ∨ IsSz n ↥L₀)
    (hOrth : ¬ ∃ a, 1 ≤ a ∧ BinaryOrthogonalFour L₀ V (V ⊓ fixV Mp) a)
    (h : ModFiveIii Mp T L₀ V τ) :
    ∃ a₀ ∈ Q, ∃ m : ℕ, Odd m ∧ a₀ ^ m = 1 ∧ ∀ w : W, a₀ w * w⁻¹ ∈ fixV Mp → w ∈ fixV Mp := by
  obtain ⟨hsum, hAfix, hcases⟩ := h
  obtain ⟨S, hS⟩ := hSQ
  have h504 := le_card_of_psl2_or_sz hn3 hshape
  have key : ∃ b ∈ Subgroup.normalizer ((S : Subgroup ↥L₀) : Set ↥L₀), ∃ r : ℕ, Odd r ∧ b ^ r = 1 ∧
      ∀ u ∈ commV L₀, ((b : MulAut W) u) * u⁻¹ ∈ commV L₀ ⊓ fixV Mp → u ∈ fixV Mp := by
    rcases hcases with ⟨hA, -⟩ | hB | hD2 | hD3
    · exact exists_natfree_of_modFiveA hn3 hshape hOrth hA S
    · exact absurd (card_eq_168_of_isPSL_three_two hB.1) (by omega)
    · exact absurd (card_eq_168_of_isPSL_three_two hD2.1) (by omega)
    · exact exists_natfree_of_D321Three hLMp h504 hD3 S
  obtain ⟨b, hbN, r, hr, hbr, hnat⟩ := key
  have hbQ : (b : MulAut W) ∈ Q := hS b hbN
  have hs'mem : τ * (b : MulAut W) * τ⁻¹ ∈ conjAutSub τ L₀ :=
    Subgroup.mem_map.mpr ⟨(b : MulAut W), b.2, by simp [MulAut.conj_apply]⟩
  refine ⟨(b : MulAut W) * (τ * (b : MulAut W) * τ⁻¹), ?_, r, hr, ?_, ?_⟩
  · exact Q.mul_mem hbQ (Q.mul_mem (Q.mul_mem hτQ hbQ) (Q.inv_mem hτQ))
  · have hc : Commute (b : MulAut W) (τ * (b : MulAut W) * τ⁻¹) := hcomm _ b.2 _ hs'mem
    have hbr' : (b : MulAut W) ^ r = 1 := by
      have := congrArg Subtype.val hbr
      simpa using this
    rw [hc.mul_pow, hbr', conj_pow, hbr']
    simp
  · exact mod_sum_good hLMp hτMp hτ2 hsum hAfix b.2 hnat

theorem modFive_good {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W}
    {t : MulAut W} {Q : Subgroup (MulAut W)} (htQ : t ∈ Q) (hMp : Mp = L ⊔ conjAutSub t L)
    (htMp : t ∈ Subgroup.normalizer (Mp : Set (MulAut W)))
    (ht2 : t * t ∈ Subgroup.normalizer (L : Set (MulAut W)))
    (hcomm : ∀ g ∈ L, ∀ g' ∈ conjAutSub t L, g * g' = g' * g)
    (hSQ : ∃ S : Sylow 2 ↥L, ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥L) : Set ↥L),
      (b : MulAut W) ∈ Q)
    {n : ℕ} (hn3 : 3 ≤ n) (hshape : IsPSL 2 2 n ↥L ∨ IsSz n ↥L)
    (hOrth : ∀ (L₀ : Subgroup (MulAut W)) (V' C : Subgroup W),
      (IsPSL 2 2 n ↥L₀ ∨ IsSz n ↥L₀) → ¬ ∃ a, 1 ≤ a ∧ BinaryOrthogonalFour L₀ V' C a)
    (hΩ : (V = ⊤ ∧ M ≤ stabSub V ∧ ∃ n', IsPSL 2 2 n' ↥(autSub L V) ∧
        Omega4PlusModule (autSub Mp V) n') →
      ∃ a₀ ∈ Q, ∃ m : ℕ, Odd m ∧ a₀ ^ m = 1 ∧ ∀ w : W, a₀ w * w⁻¹ ∈ fixV Mp → w ∈ fixV Mp)
    (h : ModFive M Mp T L V t) :
    ∃ a₀ ∈ Q, ∃ m : ℕ, Odd m ∧ a₀ ^ m = 1 ∧ ∀ w : W, a₀ w * w⁻¹ ∈ fixV Mp → w ∈ fixV Mp := by
  have hLMp : L ≤ Mp := by rw [hMp]; exact le_sup_left
  have hLtMp : conjAutSub t L ≤ Mp := by rw [hMp]; exact le_sup_right
  have h504 := le_card_of_psl2_or_sz hn3 hshape
  rcases h with h1 | h2 | h3 | h4
  · exact hΩ h1
  · obtain ⟨hV, -, h31, -⟩ := h2
    subst hV
    have h168 := card_eq_168_of_isPSL_three_two h31
    have h2 : Nat.card ↥(autSub L (⊤ : Subgroup W)) = Nat.card ↥L :=
      Nat.card_congr (autSubTopEquiv L).toEquiv
    omega
  · have hτ2 : ∀ g ∈ L, t⁻¹ * g * t ∈ conjAutSub t L := by
      intro g hg
      have hg' : (t * t)⁻¹ * g * (t * t)⁻¹⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht2) g).mp hg
      refine ⟨(t * t)⁻¹ * g * (t * t)⁻¹⁻¹, hg', ?_⟩
      simp [MulAut.conj_apply, mul_assoc]
    exact modFiveIii_good htQ hLMp htMp hτ2 hcomm hSQ hn3 hshape (hOrth L V _ hshape) h3
  · have hconj := conjAutSub_inv_conjAutSub L t
    have hτ2 : ∀ g ∈ conjAutSub t L, (t⁻¹)⁻¹ * g * t⁻¹ ∈ conjAutSub t⁻¹ (conjAutSub t L) := by
      intro g hg
      rw [hconj]
      obtain ⟨l, hl, rfl⟩ := hg
      have hl' : t * t * l * (t * t)⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp ht2 l).mp hl
      have e : (t⁻¹)⁻¹ * (MulAut.conj t).toMonoidHom l * t⁻¹ = t * t * l * (t * t)⁻¹ := by
        simp [MulAut.conj_apply, mul_assoc]
      rw [e]
      exact hl'
    have hcomm' : ∀ g ∈ conjAutSub t L, ∀ g' ∈ conjAutSub t⁻¹ (conjAutSub t L), g * g' = g' * g := by
      intro g hg g' hg'
      rw [hconj] at hg'
      exact (hcomm g' hg' g hg).symm
    obtain ⟨S₂, hS₂⟩ := borel_transport (L := L) t htQ hSQ
    have hSQ₂ : ∃ S : Sylow 2 ↥(conjAutSub t L),
        ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥(conjAutSub t L)) : Set ↥(conjAutSub t L)),
          (b : MulAut W) ∈ Q := ⟨S₂, hS₂⟩
    have hshape₂ : IsPSL 2 2 n ↥(conjAutSub t L) ∨ IsSz n ↥(conjAutSub t L) := by
      let e : ↥L ≃* ↥(conjAutSub t L) := (MulAut.conj t).subgroupMap L
      rcases hshape with hs | hs
      · exact Or.inl (isPSL_congr e hs)
      · exact Or.inr (isSz_congr e hs)
    exact modFiveIii_good (inv_mem htQ) hLtMp (Subgroup.inv_mem _ htMp) hτ2 hcomm' hSQ₂ hn3
      hshape₂ (hOrth _ V _ hshape₂) h4

end Good

end CFSG.Quasithin
