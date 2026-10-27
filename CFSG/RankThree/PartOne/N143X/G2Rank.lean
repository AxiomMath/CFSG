module

public import CFSG.RankThree.Chevalley.G2CyclotomicTori
public import CFSG.RankThree.PartOne.KF.G2Sylow
public import CFSG.RankThree.PartOne.N143X.PRankTorus

public section

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.ComponentClassification.UnbalancedCatalog CFSG.Timmesfeld.ExceptionalOrders
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.PartOne.KFU

namespace CFSG.RankThree.PartOne.N143X

theorem exists_twistedTorus_G2
    (K : Type) [Field K] [Finite K] (w : WeylGroup .G2) :
    ∃ (T : Subgroup (adjointGroup .G2 K))
      (S : Subgroup (Fin Tag.G2.rank → (AlgebraicClosure K)ˣ)),
      Nonempty (T ≃* S) ∧
      ∀ c : Fin Tag.G2.rank → (AlgebraicClosure K)ˣ, c ∈ S ↔
        ∀ v, rootChar c (w • v) = rootChar c v ^ Nat.card K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  set q := Nat.card K with hq
  have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
  have : Fact (ringChar K).Prime := ⟨hℓ⟩
  obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
  let L := AlgebraicClosure K
  have : CharP L (ringChar K) := charP_of_injective_algebraMap (algebraMap K L).injective _
  have : ExpChar L (ringChar K) := ExpChar.prime hℓ
  set F : L →+* L := iterateFrobenius L (ringChar K) e
  have hF : ∀ c : L, F c = c ^ q := fun c => by
    rw [iterateFrobenius_def, hq, Nat.card_eq_fintype_card, hqe]
  have hFbij : Function.Bijective F := frobenius_bijective (k := K) F hF
  obtain ⟨S₁, hS, hLang⟩ :=
    (exceptional_all_characteristic_field_Lang_surjectivity (ringChar K) L (e : ℕ) e.pos).1 .G2
  obtain ⟨n, hn, hnG⟩ : ∃ n, n = canonicalRep (coxeterSystem .G2) L w ∧
      n ∈ adjointGroup .G2 L := ⟨_, rfl, canonicalRep_mem_adjointGroup _ L w⟩
  obtain ⟨g₀, hg₀⟩ := hLang ⟨n, hnG⟩
  set g : ModGL .G2 L := (g₀ : ModGL .G2 L) with hgdef
  have hFg : Units.map (entrywiseHom F) g = g * n := by
    have h := congrArg Subtype.val hg₀
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h
    rw [hS] at h
    rw [h, mul_inv_cancel_left]
  have hgG : g ∈ adjointGroup .G2 L := g₀.2
  have hHG : torusGroup .G2 L ≤ adjointGroup .G2 L := torusGroup_le_adjointGroup_G2
  let θ : (Fin Tag.G2.rank → Lˣ) →* ModGL .G2 L := rootDiagUnitHom .G2 L
  have hθ : ∀ c, θ c = rootDiagUnit .G2 c := fun c => rfl
  have hθinj : Function.Injective θ := fun a b h => rootDiagUnit_injective h
  have hθH : ∀ c, θ c ∈ torusGroup .G2 L := fun c => rootDiagUnit_mem_torusGroup_g2 c
  let Φ : ModGL .G2 L →* ModGL .G2 L :=
    (MulAut.conj n).toMonoidHom.comp (Units.map (entrywiseHom F))
  let S : Subgroup (Fin Tag.G2.rank → Lˣ) := MonoidHom.eqLocus (Φ.comp θ) θ
  have hSmem : ∀ c, c ∈ S ↔ ∀ v, rootChar c (w • v) = rootChar c v ^ q := by
    intro c
    rw [← conj_frob_rootDiagUnit_eq_iff F hF w c, ← hn]
    exact Iff.rfl
  set T₀ := S.map θ with hT₀
  have hT₀H : T₀ ≤ torusGroup .G2 L := by
    rintro _ ⟨c, -, rfl⟩
    exact hθH c
  have hT₀fix : ∀ u ∈ T₀, n * Units.map (entrywiseHom F) u * n⁻¹ = u := by
    rintro _ ⟨c, hc, rfl⟩
    exact hc
  set Tc := T₀.map (MulAut.conj g).toMonoidHom with hTc
  obtain ⟨ι, hι⟩ : ∃ ι : adjointGroup .G2 K →* ModGL .G2 L,
      ι = (baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype := ⟨_, rfl⟩
  have hιinj : Function.Injective ι := by
    rw [hι]
    exact (baseChangeGL_injective (τ := .G2) (algebraMap K L)).comp Subtype.val_injective
  have hrange : ι.range = adjointGroup .G2 L ⊓ (Units.map (entrywiseHom F)).eqLocus
      (MonoidHom.id _) := by
    rw [hι, MonoidHom.range_comp, Subgroup.range_subtype,
      frobenius_fixed_eq_map_of_bijective (Or.inl rfl) F hF hFbij]
  have hconjF : ∀ u : ModGL .G2 L, Units.map (entrywiseHom F) (g * u * g⁻¹) =
      g * (n * Units.map (entrywiseHom F) u * n⁻¹) * g⁻¹ := fun u => by
    rw [map_mul, map_mul, map_inv, hFg]
    group
  have hTcι : Tc ≤ ι.range := by
    rintro _ ⟨u, hu, rfl⟩
    rw [hrange]
    refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hgG (hHG (hT₀H hu))) (inv_mem hgG), ?_⟩
    change Units.map (entrywiseHom F) (g * u * g⁻¹) = g * u * g⁻¹
    rw [hconjF, hT₀fix u hu]
  set T := Tc.comap ι with hT
  have eT : T ≃* T₀ :=
    ((Subgroup.equivMapOfInjective T ι hιinj).trans
      (MulEquiv.subgroupCongr (Subgroup.map_comap_eq_self hTcι))).trans
      (Subgroup.equivMapOfInjective T₀ (MulAut.conj g).toMonoidHom
        (MulAut.conj g).injective).symm
  exact ⟨T, S, ⟨eT.trans (Subgroup.equivMapOfInjective S θ hθinj).symm⟩, hSmem⟩


def g2w0 : WeylGroup .G2 :=
  simple .G2 g2ia * simple .G2 g2ir * (simple .G2 g2ia * simple .G2 g2ir) *
    (simple .G2 g2ia * simple .G2 g2ir)

theorem g2w0_g2a : g2w0 • g2a = -g2a := by
  simp only [g2w0, mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem g2w0_g2r : g2w0 • g2r = -g2r := by
  simp only [g2w0, mul_smul, simple_smul]
  exact List.ofFn_injective (by decide +kernel)

theorem g2w0_smul (v : Fin Tag.G2.rank → ℤ) : g2w0 • v = -v := by
  conv_lhs => rw [g2_eq_smul_add v]
  conv_rhs => rw [g2_eq_smul_add v]
  rw [smul_add, smul_comm g2w0 (v g2ia), smul_comm g2w0 (v g2ir), g2w0_g2a, g2w0_g2r,
    smul_neg, smul_neg, neg_add_rev, add_comm]

theorem forall_rootChar_g2w0_iff {L : Type} [Field L] (c : Fin Tag.G2.rank → Lˣ) (q : ℕ) :
    (∀ v, rootChar c (g2w0 • v) = rootChar c v ^ q) ↔ ∀ i, c i ^ (q + 1) = 1 := by
  constructor
  · intro h i
    have h1 := h (Pi.single i 1)
    rw [g2w0_smul, rootChar_neg_eq_inv, rootChar_pi_single] at h1
    rw [pow_succ', ← h1, mul_inv_cancel]
  · intro h v
    rw [g2w0_smul, rootChar_neg_eq_inv]
    have h2 : rootChar c v ^ (q + 1) = 1 :=
      rootChar_pow_of_pow_eq_one (funext fun i => by simpa using h i) v
    exact inv_eq_of_mul_eq_one_right (by rw [← pow_succ']; exact h2)


theorem exists_torus_negOne_G2
    (K : Type) [Field K] [Finite K] :
    ∃ (T : Subgroup (adjointGroup .G2 K))
      (ψ : T →* (Fin Tag.G2.rank → (AlgebraicClosure K)ˣ)),
      Function.Injective ψ ∧ Nat.card T = (Nat.card K + 1) ^ 2 := by
  classical
  obtain ⟨T, S, ⟨e⟩, hS⟩ := exists_twistedTorus_G2 K g2w0
  refine ⟨T, S.subtype.comp e.toMonoidHom, Subtype.val_injective.comp e.injective, ?_⟩
  set q := Nat.card K with hq
  have : Fintype K := Fintype.ofFinite K
  have hSmem : ∀ c, c ∈ S ↔ ∀ i, c i ^ (q + 1) = 1 := fun c => by
    rw [hS c, forall_rootChar_g2w0_iff]
  have hqK : ((q : ℕ) : K) = 0 := by
    rw [hq, Nat.card_eq_fintype_card]
    exact FiniteField.cast_card_eq_zero K
  have hdK : ((q + 1 : ℕ) : K) = 1 := by
    push_cast
    rw [hqK, zero_add]
  have : NeZero ((q + 1 : ℕ) : K) := ⟨by rw [hdK]; exact one_ne_zero⟩
  have : NeZero (q + 1) := ⟨Nat.succ_ne_zero q⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := AlgebraicClosure K) (n := q + 1)
  have hR : Nat.card (rootsOfUnity (q + 1) (AlgebraicClosure K)) = q + 1 := hζ.card_rootsOfUnity
  let f : S ≃ (Fin Tag.G2.rank → rootsOfUnity (q + 1) (AlgebraicClosure K)) :=
    { toFun := fun c i => ⟨c.1 i, (mem_rootsOfUnity _ _).2 ((hSmem c.1).1 c.2 i)⟩
      invFun := fun b => ⟨fun i => (b i : (AlgebraicClosure K)ˣ), (hSmem _).2 fun i =>
        (mem_rootsOfUnity _ _).1 (b i).2⟩
      left_inv := fun c => Subtype.ext rfl
      right_inv := fun b => funext fun i => Subtype.ext rfl }
  rw [Nat.card_congr e.toEquiv, Nat.card_congr f, Nat.card_fun, hR]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl


theorem not_dvd_index_of_card_negOne
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpd : p ∣ Nat.card K + 1) (T : Subgroup (adjointGroup .G2 K))
    (hT : Nat.card T = (Nat.card K + 1) ^ 2) : ¬ p ∣ T.index := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hcard := T.card_mul_index
  rw [hT, card_adjointGroup_G2, CFSG.Open.ordG2] at hcard
  have hcardZ : ((Nat.card K : ℤ) + 1) ^ 2 * T.index =
      (Nat.card K : ℤ) ^ 6 * ((Nat.card K : ℤ) ^ 6 - 1) * ((Nat.card K : ℤ) ^ 2 - 1) := by
    have h6 : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq1
    have h := congrArg (Nat.cast : ℕ → ℤ) hcard
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at h
    exact h
  have hd0 : ((Nat.card K : ℤ) + 1) ^ 2 ≠ 0 := by positivity
  have hidx : (T.index : ℤ) = (Nat.card K : ℤ) ^ 6 * ((Nat.card K : ℤ) - 1) ^ 2 *
      ((Nat.card K : ℤ) ^ 4 + (Nat.card K : ℤ) ^ 2 + 1) := by
    apply mul_left_cancel₀ hd0
    rw [hcardZ]
    ring
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (Nat.card K : ℤ) := ⟨_, rfl⟩
  have hpd' : (p : ℤ) ∣ Q + 1 := by
    rw [hQ]
    exact_mod_cast hpd
  intro hdvd
  have hpi : (p : ℤ) ∣ Q ^ 6 * (Q - 1) ^ 2 * (Q ^ 4 + Q ^ 2 + 1) := by
    rw [hQ, ← hidx]
    exact_mod_cast hdvd
  have hp1 : ¬ (p : ℤ) ∣ 1 := hpZ.not_dvd_one
  have hp2 : ¬ (p : ℤ) ∣ 2 := fun h => by
    have := Int.le_of_dvd (by norm_num) h
    omega
  have hp3' : ¬ (p : ℤ) ∣ 3 := fun h => by
    have := Int.le_of_dvd (by norm_num) h
    omega
  have hq : ¬ (p : ℤ) ∣ Q := fun h => hp1 (by
    have h' := dvd_sub hpd' h
    rwa [show Q + 1 - Q = 1 by ring] at h')
  rcases hpZ.dvd_or_dvd hpi with h | h
  · rcases hpZ.dvd_or_dvd h with h | h
    · exact hq (hpZ.dvd_of_dvd_pow h)
    · have h1 := hpZ.dvd_of_dvd_pow h
      have h' := dvd_sub hpd' h1
      rw [show Q + 1 - (Q - 1) = 2 by ring] at h'
      exact hp2 h'
  · have h' := dvd_sub h (dvd_mul_of_dvd_left hpd' (Q ^ 3 - Q ^ 2 + 2 * Q - 2))
    rw [show Q ^ 4 + Q ^ 2 + 1 - (Q + 1) * (Q ^ 3 - Q ^ 2 + 2 * Q - 2) = 3 by ring] at h'
    exact hp3' h'


theorem card_le_sq_of_conj_into_Tp
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (h5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) (E : Subgroup (adjointGroup .G2 K)) (hE : ∀ x ∈ E, x ^ p = 1) :
    Nat.card E ≤ p ^ 2 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨g, hg⟩ := exists_conj_into_Tp hp h5 hpq E hE
  let φ : E → (Fin Tag.G2.rank → rootsOfUnity p K) := fun x => Classical.choose (hg x x.2)
  have hφ : ∀ x : E, tpM p K (φ x) = g * x * g⁻¹ := fun x => Classical.choose_spec (hg x x.2)
  have hφinj : Function.Injective φ := fun x y h => by
    have h1 : g * (x : adjointGroup .G2 K) * g⁻¹ = g * (y : adjointGroup .G2 K) * g⁻¹ := by
      rw [← hφ x, ← hφ y, h]
    exact Subtype.ext (mul_left_cancel (mul_right_cancel h1))
  have hR : Nat.card (rootsOfUnity p K) ≤ p := card_rootsOfUnity K p
  calc Nat.card E ≤ Nat.card (Fin Tag.G2.rank → rootsOfUnity p K) :=
        Nat.card_le_card_of_injective φ hφinj
    _ = Nat.card (rootsOfUnity p K) ^ 2 := by
        simp only [Nat.card_fun, Nat.card_eq_fintype_card, Fintype.card_fin]
        rfl
    _ ≤ p ^ 2 := Nat.pow_le_pow_left hR 2


theorem false_of_pow_three_G2
    (K : Type) [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p)
    (hpq : ¬ p ∣ Nat.card K) {E : Subgroup (adjointGroup .G2 K)} (hE : ∀ x ∈ E, x ^ p = 1)
    (hcard : Nat.card E = p ^ 3) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hq1 : 1 ≤ Nat.card K := Nat.card_pos
  have hdvdC : p ∣ Nat.card (adjointGroup .G2 K) := by
    have : p ∣ Nat.card E := by rw [hcard]; exact dvd_pow_self p (by norm_num)
    exact this.trans (Subgroup.card_subgroup_dvd_card E)
  rw [card_adjointGroup_G2, CFSG.Open.ordG2] at hdvdC
  obtain ⟨Q, hQ⟩ : ∃ Q : ℤ, Q = (Nat.card K : ℤ) := ⟨_, rfl⟩
  have hpZ : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hdvdZ : (p : ℤ) ∣ Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) := by
    have h6 : 1 ≤ Nat.card K ^ 6 := Nat.one_le_pow _ _ hq1
    have h2 : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ hq1
    have h := Int.natCast_dvd_natCast.2 hdvdC
    push_cast [Nat.cast_sub h6, Nat.cast_sub h2] at h
    rw [hQ]
    exact h
  have hqZ : ¬ (p : ℤ) ∣ Q := fun h => hpq (by rw [hQ] at h; exact_mod_cast h)
  have hfac : Q ^ 6 * (Q ^ 6 - 1) * (Q ^ 2 - 1) = Q ^ 6 * ((Q - 1) * (Q + 1) *
      ((Q ^ 2 + Q + 1) * (Q ^ 2 - Q + 1))) * ((Q - 1) * (Q + 1)) := by ring
  rw [hfac] at hdvdZ
  have key : (p : ℤ) ∣ Q - 1 ∨ (p : ℤ) ∣ Q + 1 ∨ (p : ℤ) ∣ Q ^ 2 + Q + 1 ∨
      (p : ℤ) ∣ Q ^ 2 - Q + 1 := by
    rcases hpZ.dvd_or_dvd hdvdZ with h | h
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact absurd (hpZ.dvd_of_dvd_pow h) hqZ
      · rcases hpZ.dvd_or_dvd h with h | h
        · rcases hpZ.dvd_or_dvd h with h | h
          · exact Or.inl h
          · exact Or.inr (Or.inl h)
        · rcases hpZ.dvd_or_dvd h with h | h
          · exact Or.inr (Or.inr (Or.inl h))
          · exact Or.inr (Or.inr (Or.inr h))
    · rcases hpZ.dvd_or_dvd h with h | h
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
  rcases key with h | h | h | h
  ·
    have hpq1 : p ∣ Nat.card K - 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K - 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hq1]
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    have h1 := card_le_sq_of_conj_into_Tp K hp (by omega) hpq1 E hE
    rw [hcard] at h1
    have : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  ·
    have hpd : p ∣ Nat.card K + 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K + 1 : ℕ) : ℤ) := by
        push_cast
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    obtain ⟨T, ψ, hψ, hT⟩ := exists_torus_negOne_G2 K
    exact false_of_pow_three_of_torus hp (not_dvd_index_of_card_negOne K hp (by omega) hpd T hT) ψ
      hψ hE hcard
  ·
    have hd : ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) =
        (Nat.card K : ℤ) ^ 2 + (2 * 2 - 3) * Nat.card K + 1 := by push_cast; ring
    have hpd : p ∣ Nat.card K ^ 2 + Nat.card K + 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K ^ 2 + Nat.card K + 1 : ℕ) : ℤ) := by
        push_cast
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    obtain ⟨T, hcyc, hTcard, -⟩ := cyclotomic_core K (k := 2) (Or.inr rfl) g2rot_two_g2a
      g2rot_two_g2r _ hd hp (by omega)
    have := hcyc
    exact false_of_pow_three_of_cyclic hp
      (not_dvd_index_of_card_eq K (k := 2) (Or.inr rfl) _ hd hp (by omega) hpd T hTcard) hE hcard
  ·
    have hle : Nat.card K ≤ Nat.card K ^ 2 := Nat.le_self_pow (by norm_num) _
    have hd : ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) =
        (Nat.card K : ℤ) ^ 2 + (2 * 1 - 3) * Nat.card K + 1 := by
      push_cast [Nat.cast_sub hle]
      ring
    have hpd : p ∣ Nat.card K ^ 2 - Nat.card K + 1 := by
      have h' : (p : ℤ) ∣ ((Nat.card K ^ 2 - Nat.card K + 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub hle]
        rw [← hQ]
        exact h
      exact Int.natCast_dvd_natCast.1 h'
    obtain ⟨T, hcyc, hTcard, -⟩ := cyclotomic_core K (k := 1) (Or.inl rfl) g2rot_one_g2a
      g2rot_one_g2r _ hd hp (by omega)
    have := hcyc
    exact false_of_pow_three_of_cyclic hp
      (not_dvd_index_of_card_eq K (k := 1) (Or.inl rfl) _ hd hp (by omega) hpd T hTcard) hE hcard

end CFSG.RankThree.PartOne.N143X
