module

public import CFSG.LocalAnalysis.StandardType.GGExcKGInndiagCIUntw
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankE6
public import CFSG.LocalAnalysis.StandardType.GGExcFieldRankTwE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesIsogenyE6
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesIsogenyTwE6

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank CFSG.LieType.Chevalley
  CFSG.LieType.SeitzGeneration CFSG.LieType.Steinberg CFSG.LieType.Steinberg.Exceptional
open CFSG.Open (IsElemAbelian)

private theorem cibComap {K G : Type*} [Group K] [Group G] (ψ : K →* G)
    (hinj : Function.Injective ψ) {p : ℕ} {E : Subgroup G} (hEr : E ≤ ψ.range)
    (hE : IsElemAbelian p E) :
    IsElemAbelian p (E.comap ψ) ∧ Nat.card (E.comap ψ) = Nat.card E := by
  refine ⟨⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩, ?_⟩
  · apply Subtype.ext; apply hinj
    have h := congrArg Subtype.val (hE.1.is_comm.comm ⟨ψ a, a.2⟩ ⟨ψ b, b.2⟩)
    simpa [map_mul] using h
  · apply hinj; rw [map_pow, map_one]; exact hE.2 _ hx
  · have h1 := Nat.card_congr (Subgroup.equivMapOfInjective (E.comap ψ) ψ hinj).toEquiv
    rw [Subgroup.map_comap_eq_self hEr] at h1
    exact h1

private theorem cibCard_le {H G : Type*} [Group H] [Group G] (χ : H →* G)
    (hχ : Function.Injective χ) {p m : ℕ} (hrank : GGElemAbelianRankLE H p m)
    {E : Subgroup G} (hEr : E ≤ χ.range) (hE : IsElemAbelian p E) : Nat.card E ≤ p ^ m := by
  obtain ⟨hc, hcard⟩ := cibComap χ hχ hEr hE
  exact hcard ▸ hrank _ hc

private theorem cibDvdSq {f p : ℕ} (hreg : GGExcRegime p f) : p ∣ (2 ^ f) ^ 2 - 1 := by
  have ha : 1 ≤ 2 ^ f := Nat.one_le_two_pow
  have h1 : (2 ^ f) ^ 2 - 1 = (2 ^ f - 1) * (2 ^ f + 1) := by
    have : 1 ≤ (2 ^ f) ^ 2 := Nat.one_le_pow _ _ (by omega)
    zify [ha, this]; ring
  rw [h1]
  rcases hreg with h | h
  · exact h.mul_right _
  · exact h.mul_left _

private theorem cibOrder_dvd_two {p q : ℕ} (hq : 0 < q) (h : p ∣ q ^ 2 - 1) :
    orderOf ((q : ℕ) : ZMod p) ∣ 2 := by
  have h0 : (((q ^ 2 - 1 : ℕ)) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ p).2 h
  rw [Nat.cast_sub (Nat.one_le_pow _ _ hq), Nat.cast_pow, Nat.cast_one, sub_eq_zero] at h0
  exact orderOf_dvd_of_pow_eq_one h0

private theorem cibOrder_eq_one_iff {f p : ℕ} :
    orderOf (((2 ^ f : ℕ)) : ZMod p) = 1 ↔ p ∣ 2 ^ f - 1 := by
  rw [orderOf_eq_one_iff, ← ZMod.natCast_eq_zero_iff (2 ^ f - 1) p,
    Nat.cast_sub Nat.one_le_two_pow, Nat.cast_one, sub_eq_zero]

private theorem cibFixCard_one {p : ℕ} (hp : p.Prime) (R : ℕ) :
    GGFixCard p (1 : Equiv.Perm (Fin R)) = p ^ R := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  unfold GGFixCard
  have h : Nat.card {z : Fin R → ZMod p // ∀ i, z ((1 : Equiv.Perm (Fin R)) i) = z i} =
      Nat.card (Fin R → ZMod p) :=
    Nat.card_congr (Equiv.subtypeUnivEquiv fun z i => rfl)
  rw [h, Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]

private theorem cibFixCard_gamma {p : ℕ} (hp : p.Prime) :
    p ^ 4 ≤ GGFixCard p (Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4) := by
  haveI : NeZero p := ⟨hp.ne_zero⟩
  unfold GGFixCard
  let g : (Fin 4 → ZMod p) →
      {z : Fin 6 → ZMod p //
        ∀ i, z ((Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4 : Equiv.Perm (Fin 6)) i) = z i} :=
    fun w => ⟨![w 0, w 1, w 2, w 3, w 2, w 0], fun i => by fin_cases i <;> rfl⟩
  have hinj : Function.Injective g := by
    intro w w' h
    have h' := congrArg Subtype.val h
    funext i
    fin_cases i
    · exact congrFun h' 0
    · exact congrFun h' 1
    · exact congrFun h' 2
    · exact congrFun h' 3
  have h4 : Nat.card (Fin 4 → ZMod p) = p ^ 4 := by
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_eq_fintype_card, Fintype.card_fin]
  exact h4 ▸ Nat.card_le_card_of_injective g hinj

private theorem cibBound_E6
    {f : ℕ} (hf : f ≠ 0) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {e : ℕ}
    (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = e) :
    GGElemAbelianRankLE (adjointGroup .E6 (GaloisField 2 f)) p (degCount .E6 e) := by
  have hq : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f hf
  exact rankLE_E6 (K := GaloisField 2 f) hp hp2 (by rw [hq]; exact he)

private theorem cibBound_twistedE6
    {f : ℕ} (hf : 1 ≤ f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {e : ℕ} (he : orderOf (((2 ^ f : ℕ)) : ZMod p) = e) :
    GGElemAbelianRankLE ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f)) p
      (degCountTw e) := by
  have hK : Nat.card (GaloisField 2 (2 * f)) = (2 ^ f) ^ 2 := by
    rw [GaloisField.card 2 (2 * f) (by omega), ← pow_mul, mul_comm]
  set σ : GaloisField 2 (2 * f) ≃+* GaloisField 2 (2 * f) :=
    iterateFrobeniusEquiv (GaloisField 2 (2 * f)) 2 f with hσdef
  have hσ : ∀ c, σ c = c ^ 2 ^ f := fun c => iterateFrobeniusEquiv_def _ 2 f c
  have hσθ : σ.toRingHom = frobQ 2 f := RingHom.ext fun c => by
    change σ c = frobQ 2 f c
    rw [hσ, frobQ_apply]
  have key := rankLE_twistedE6 (ℓ := 2) (f := f) Nat.prime_two hf (GaloisField 2 (2 * f)) hK σ hσ
    hp hp2 he
  have key' : ∀ θ : GaloisField 2 (2 * f) →+* GaloisField 2 (2 * f), σ.toRingHom = θ →
      GGElemAbelianRankLE ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) θ) p
        (degCountTw e) := by
    intro θ hθ
    subst hθ
    exact key
  exact key' _ hσθ

private theorem cibMem_normalizer
    {t : StatedLieTag} {n f : ℕ}
    (hN : ((ggPsiU t n f).range).Normal) (c : GGAutU t n f) :
    c ∈ Subgroup.normalizer ((ggPsiU t n f).range : Set (GGAutU t n f)) := by
  refine Subgroup.mem_normalizer_iff.2 fun h => ⟨fun hh => hN.conj_mem h hh c, fun hh => ?_⟩
  have := hN.conj_mem _ hh c⁻¹
  simpa [mul_assoc] using this

private theorem cibDiagAut_E6
    (f : ℕ) (π : Equiv.Perm (Fin (ggU (absTag .E6) 6 f).D.rank))
    (h : IsDiagAut (ggU (absTag .E6) 6 f).D π) :
    π = 1 ∨ π = Equiv.swap (0 : Fin 6) 5 * Equiv.swap 2 4 :=
  perm_cases_of_cartanE6 π (fun i j => h i j)

theorem ggInnDiagU_mem_range_E6
    {n f : ℕ} (hadm : GGKnownAdm .E6 n f) {p : ℕ} (hp : p.Prime)
    (hp3 : p ≠ 3 ∨ ¬ 3 ∣ Nat.card (GaloisField 2 f) - 1) {c : GGAutU .E6 n f}
    (hcp : c ^ p = 1) (hc : GGInnDiagU .E6 n f c) : c ∈ (ggPsiU .E6 n f).range := by
  haveI : Finite (ggU .E6 n f).K := ggU_finite_exc (Or.inr (Or.inl rfl)) hadm
  haveI : Finite (GGAutU .E6 n f) := GGSFCore.finite_ggAutU
  haveI hN : ((ggPsiU .E6 n f).range).Normal := GGSFCore.normal_range_ggPsiU .E6 n f
  obtain ⟨-, hker, ⟨hcomm, -⟩, hcent⟩ := ggKnownSetting_autU hadm
  exact ExcFrames.mem_range_of_innerDiag_E6 hp hp3 (ggPsiU .E6 n f) hker hcomm hcent
    (cibMem_normalizer hN c) hcp hc

theorem ggInnDiagU_mem_range_twistedE6
    {n f : ℕ} (hadm : GGKnownAdm .twistedE6 n f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h3 : ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1))
    {c : GGAutU .twistedE6 n f} (hcp : c ^ p = 1) (hc : GGInnDiagU .twistedE6 n f c) :
    c ∈ (ggPsiU .twistedE6 n f).range := by
  haveI : Finite (ggU .twistedE6 n f).K :=
    ggU_finite_exc (Or.inr (Or.inr (Or.inr (Or.inr rfl)))) hadm
  haveI : Finite (GGAutU .twistedE6 n f) := GGSFCore.finite_ggAutU
  haveI hN : ((ggPsiU .twistedE6 n f).range).Normal :=
    GGSFCore.normal_range_ggPsiU .twistedE6 n f
  obtain ⟨⟨hadm', -⟩, hker, ⟨hcomm, -⟩, hcent⟩ := ggKnownSetting_autU hadm
  exact ExcFrames.mem_range_of_innerDiag_twistedE6 hp hp2 hadm'.2.1 h3 (ggPsiU .twistedE6 n f)
    hker hcomm hcent (cibMem_normalizer hN c) hcp hc

theorem ggKGInndiagCIa_E6
    (n f : ℕ) (hadm : GGKnownAdm .E6 n f) {p : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    {π : Equiv.Perm (Fin (ggU (absTag .E6) 6 f).D.rank)} (hπ : GGPiCond .E6 p f π)
    (hrow : ¬ (p = 3 ∧ π = 1)) {E : Subgroup (GGAutU .E6 n f)} (hE : IsElemAbelian p E)
    (hdiag : ∀ b ∈ E, GGInnDiagU .E6 n f b) : Nat.card E ≤ GGFixCard p π := by
  have hf : f ≠ 0 := by have := hadm.1.2.1; omega
  have hπE : π = 1 ↔ p ∣ 2 ^ f - 1 := hπ.2.2.1 rfl
  have hp3 : p ≠ 3 ∨ ¬ 3 ∣ Nat.card (GaloisField 2 f) - 1 := by
    by_cases h3 : p = 3
    · right
      have hne : ¬ p ∣ 2 ^ f - 1 := fun hd => hrow ⟨h3, hπE.2 hd⟩
      rw [GaloisField.card 2 f hf]
      rwa [h3] at hne
    · exact Or.inl h3
  obtain ⟨-, hker, -, hcent⟩ := ggKnownSetting_autU hadm
  obtain ⟨χ, hχinj, hχrange⟩ := ExcFrames.exists_injective_factor_E6 (ggPsiU .E6 n f) hker hcent
  have hEr : E ≤ χ.range := by
    rw [hχrange]
    intro b hb
    exact ggInnDiagU_mem_range_E6 hadm hp hp3 (hE.2 b hb) (hdiag b hb)
  have hdvd : orderOf (((2 ^ f : ℕ)) : ZMod p) ∣ 2 :=
    cibOrder_dvd_two (by positivity) (cibDvdSq hreg)
  by_cases h1 : π = 1
  · subst h1
    rw [cibFixCard_one hp]
    have hbound := cibCard_le χ hχinj (cibBound_E6 hf hp hp2 rfl) hEr hE
    have hdeg : degCount .E6 (orderOf (((2 ^ f : ℕ)) : ZMod p)) ≤ 6 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h <;> rw [h] <;> decide
    exact hbound.trans (Nat.pow_le_pow_right hp.pos hdeg)
  · rcases cibDiagAut_E6 f π hπ.1 with h | hγ
    · exact absurd h h1
    · have hne : ¬ p ∣ 2 ^ f - 1 := fun hd => h1 (hπE.2 hd)
      have he2 : orderOf (((2 ^ f : ℕ)) : ZMod p) = 2 := by
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h
        · exact absurd (cibOrder_eq_one_iff.1 h) hne
        · exact h
      have hbound := cibCard_le χ hχinj (cibBound_E6 hf hp hp2 he2) hEr hE
      have h4 : degCount .E6 2 = 4 := by decide
      rw [h4] at hbound
      rw [hγ]
      exact hbound.trans (cibFixCard_gamma hp)

theorem ggKGInndiagCIa_twistedE6
    (n f : ℕ) (hadm : GGKnownAdm .twistedE6 n f) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f)
    {π : Equiv.Perm (Fin (ggU (absTag .twistedE6) 6 f).D.rank)} (hπ : GGPiCond .twistedE6 p f π)
    (hrow : ¬ (p = 3 ∧ π = 1)) {E : Subgroup (GGAutU .twistedE6 n f)} (hE : IsElemAbelian p E)
    (hdiag : ∀ b ∈ E, GGInnDiagU .twistedE6 n f b) : Nat.card E ≤ GGFixCard p π := by
  have hf : 1 ≤ f := hadm.1.2.1
  have hπT : π = 1 ↔ p ∣ 2 ^ f + 1 := hπ.2.2.2 rfl
  have h3 : ¬ (p = 3 ∧ 3 ∣ 2 ^ f + 1) := by
    rintro ⟨h3, hd⟩
    have hd' : p ∣ 2 ^ f + 1 := by rw [h3]; exact hd
    exact hrow ⟨h3, hπT.2 hd'⟩
  obtain ⟨-, hker, -, hcent⟩ := ggKnownSetting_autU hadm
  obtain ⟨χ, hχinj, hχrange⟩ :=
    ExcFrames.exists_injective_factor_twistedE6 hf (ggPsiU .twistedE6 n f) hker hcent
  have hEr : E ≤ χ.range := by
    rw [hχrange]
    intro b hb
    exact ggInnDiagU_mem_range_twistedE6 hadm hp hp2 h3 (hE.2 b hb) (hdiag b hb)
  have hdvd : orderOf (((2 ^ f : ℕ)) : ZMod p) ∣ 2 :=
    cibOrder_dvd_two (by positivity) (cibDvdSq hreg)
  by_cases h1 : π = 1
  · subst h1
    rw [cibFixCard_one hp]
    have hbound := cibCard_le χ hχinj (cibBound_twistedE6 hf hp hp2 rfl) hEr hE
    have hdeg : degCountTw (orderOf (((2 ^ f : ℕ)) : ZMod p)) ≤ 6 := by
      rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h | h <;> rw [h] <;> decide
    exact hbound.trans (Nat.pow_le_pow_right hp.pos hdeg)
  · rcases cibDiagAut_E6 f π hπ.1 with h | hγ
    · exact absurd h h1
    · have hne : ¬ p ∣ 2 ^ f + 1 := fun hd => h1 (hπT.2 hd)
      have he1 : orderOf (((2 ^ f : ℕ)) : ZMod p) = 1 :=
        cibOrder_eq_one_iff.2 (hreg.resolve_right hne)
      have hbound := cibCard_le χ hχinj (cibBound_twistedE6 hf hp hp2 he1) hEr hE
      have h4 : degCountTw 1 = 4 := by decide
      rw [h4] at hbound
      rw [hγ]
      exact hbound.trans (cibFixCard_gamma hp)

theorem ggKGInndiagCIa_E6_twistedE6
    {t : StatedLieTag} (ht : t = .E6 ∨ t = .twistedE6)
    (n f : ℕ) (hadm : GGKnownAdm t n f) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hreg : GGExcRegime p f) {π : Equiv.Perm (Fin (ggU (absTag t) 6 f).D.rank)}
    (hπ : GGPiCond t p f π) (hrow : ¬ (p = 3 ∧ π = 1)) {E : Subgroup (GGAutU t n f)}
    (hE : IsElemAbelian p E) (hdiag : ∀ b ∈ E, GGInnDiagU t n f b) :
    Nat.card E ≤ GGFixCard p π := by
  rcases ht with rfl | rfl
  · exact ggKGInndiagCIa_E6 n f hadm hp hp2 hreg hπ hrow hE hdiag
  · exact ggKGInndiagCIa_twistedE6 n f hadm hp hp2 hreg hπ hrow hE hdiag

end CFSG.StandardType
