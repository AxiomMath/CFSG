module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec6.FinalAuxSimple

public section

open CFSG.Open

universe u

namespace CFSG.SignalizerFunctorTheorem.McBride.Near

namespace Sec6S33

variable {p : ℕ} {G : Type u} [Group G] [Finite G] {A : Subgroup G} {θ : G → Subgroup G}

omit [Finite G] in
theorem commute_of_normalizes {S : Set (Subgroup G)} {L : Subgroup G} (hL : IsDirectProduct S L)
    {J₁ J₂ : Subgroup G} (h₁ : J₁ ∈ S) (hne : J₁ ≠ J₂) {T N : Subgroup G}
    (hinj : T ⊓ sSup (S \ {J₂}) = ⊥) (hN : N ≤ J₁)
    (hNT : ∀ n ∈ N, ∀ t ∈ T, n * t * n⁻¹ ∈ T) (hNP : N ≤ projIn S J₁ T) :
    ∀ n ∈ N, ∀ c ∈ N, n * c = c * n := by
  intro n hn c hc
  have hcP := hNP hc
  rw [projIn, mem_proj_iff (hL.commute_sSup_diff h₁)] at hcP
  obtain ⟨hcJ, l, hl, hcl⟩ := hcP
  have hnJ : n ∈ J₁ := hN hn
  have hcJ' : c ∈ J₁ := hN hc
  have hw : n * (c * l) * n⁻¹ * (c * l)⁻¹ ∈ T :=
    mul_mem (hNT n hn _ hcl) (inv_mem hcl)
  have hcomm : n * l = l * n := (hL.commute_sSup_diff h₁ n hnJ l hl).eq
  have hw' : n * (c * l) * n⁻¹ * (c * l)⁻¹ = n * c * n⁻¹ * c⁻¹ := by
    calc n * (c * l) * n⁻¹ * (c * l)⁻¹ = n * c * (l * n⁻¹) * l⁻¹ * c⁻¹ := by group
      _ = n * c * (n⁻¹ * l) * l⁻¹ * c⁻¹ := by
        have : l * n⁻¹ = n⁻¹ * l := by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hcomm, ← mul_assoc, inv_mul_cancel, one_mul]
        rw [this]
      _ = n * c * n⁻¹ * c⁻¹ := by group
  have hwJ : n * c * n⁻¹ * c⁻¹ ∈ J₁ := mul_mem (mul_mem (mul_mem hnJ hcJ') (inv_mem hnJ))
    (inv_mem hcJ')
  have hJ₁le : J₁ ≤ sSup (S \ {J₂}) :=
    le_sSup ⟨h₁, fun hh => hne (Set.mem_singleton_iff.mp hh)⟩
  have hmem : n * c * n⁻¹ * c⁻¹ ∈ T ⊓ sSup (S \ {J₂}) := ⟨hw' ▸ hw, hJ₁le hwJ⟩
  rw [hinj, Subgroup.mem_bot] at hmem
  rw [mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at hmem
  exact hmem

section R0

variable (h : Counterexample p A θ)

include h

theorem exists_zpowers_ge_inf {B V : Subgroup G} (hB : B ∈ signalizerFunctorEk p 2 A)
    (hBV : ¬ B ≤ V) : ∃ u ∈ B, u ≠ 1 ∧ B ⊓ V ≤ Subgroup.zpowers u := by
  have hp := h.hyp.prime
  by_cases hU : B ⊓ V = ⊥
  · have hBne : B ≠ ⊥ := by
      intro hbot
      have := hB.2
      rw [hbot, Subgroup.card_bot] at this
      exact absurd this.symm (Nat.one_lt_pow (by norm_num) hp.one_lt).ne'
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hBne
    exact ⟨u, hu, fun h1 => hu1 (Subtype.ext h1), hU ▸ bot_le⟩
  · have hdvd : Nat.card ↥(B ⊓ V) ∣ p ^ 2 := hB.2 ▸ Subgroup.card_dvd_of_le inf_le_left
    obtain ⟨i, hi, hUi⟩ := (Nat.dvd_prime_pow hp).1 hdvd
    have hi1 : i = 1 := by
      interval_cases i
      · exact absurd (Subgroup.eq_bot_of_card_eq _ (by simpa using hUi)) hU
      · rfl
      · exfalso
        have heq : B ⊓ V = B := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hB.2, hUi])
        exact hBV (heq ▸ inf_le_right)
    have hUE : B ⊓ V ∈ signalizerFunctorEk p 1 A := ⟨inf_le_left.trans hB.1, by rw [hUi, hi1]⟩
    obtain ⟨⟨u, hu⟩, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hU
    have hu1' : u ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
    exact ⟨u, hu.1, hu1', (eq_zpowers_of_mem h hUE hu hu1').le⟩

theorem kOf_inf_centralizer_eq {a : G} (ha : NT A θ a) :
    kOf (θ a) ⊓ Subgroup.centralizer (A : Set G) = dsub A θ ⊓ kOf (θ a) := by
  have hθ := h.hyp.nearFunctor
  have hD : dsub A θ = θ a ⊓ Subgroup.centralizer (A : Set G) :=
    (cenIn_eq_dsub hθ (apply_mem_mtil hθ ha.mem ha.ne_one)).symm
  rw [hD]
  ext x
  constructor
  · rintro ⟨hxK, hxc⟩
    exact ⟨⟨kOf_le _ hxK, hxc⟩, hxK⟩
  · rintro ⟨⟨-, hxc⟩, hxK⟩
    exact ⟨hxK, hxc⟩

theorem kOf_inf_centralizer_eq_of_NT
    {a b : G} (ha : NT A θ a) (hb : NT A θ b) :
    kOf (θ a) ⊓ Subgroup.centralizer (A : Set G) =
      kOf (θ b) ⊓ Subgroup.centralizer (A : Set G) := by
  have hθ := h.hyp.nearFunctor
  have h66 := h.lemma66 (ha.zpowers_mem_rSet h) (hb.zpowers_mem_rSet h)
  rw [hθ.isFunctor.thetaOf_zpowers ha.mem ha.ne_one,
    hθ.isFunctor.thetaOf_zpowers hb.mem hb.ne_one] at h66
  rw [kOf_inf_centralizer_eq h ha, kOf_inf_centralizer_eq h hb, h66]

theorem NT.FN_ne_top
    {a : G} (ha : NT A θ a) : FN A θ a ≠ A := by
  intro hs
  have hθ := h.hyp.nearFunctor
  have hF := hθ.isFunctor
  have hp := h.hyp.prime
  obtain ⟨J, hlc, hKJ⟩ := ha.lcal_eq_singleton h hs
  have hJ : J ∈ lcal (θ a) := hlc ▸ Set.mem_singleton J
  have hAN : ∀ x ∈ A, x ∈ Subgroup.normalizer (J : Set G) := fun x hx =>
    (mem_FN_iff.mp (by rw [hs]; exact hx : x ∈ FN A θ a)).2 J hJ
  obtain ⟨g, hgN, hgc⟩ := ha.exists_noncentral h hJ
  have hgA : g ∈ A := hgN.1
  set B₁ : Subgroup G := A ⊓ Subgroup.centralizer (kOf (θ a) : Set G) with hB₁
  have hgB₁ : g ∉ B₁ := fun hg => hgc (hKJ ▸ hg.2)
  have haB₁ : a ∈ B₁ := by
    refine ⟨ha.mem, ?_⟩
    show a ∈ Subgroup.centralizer (kOf (θ a) : Set G)
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mp
      (hF.le_centralizer a ha.mem ha.ne_one (kOf_le _ hx))
  obtain ⟨x, hxA, hx1, hxn, hxB₁⟩ : ∃ x ∈ A, x ≠ 1 ∧ NT A θ x ∧ x ∉ B₁ := by
    by_contra hcon
    push Not at hcon
    have hsolv : ∀ y ∈ A, y ≠ 1 → y ∉ B₁ → Group.IsSolvable (θ y) := by
      intro y hy hy1 hyB
      by_contra hns
      exact hyB (hcon y hy hy1 ⟨hy, hy1, hns⟩)
    have hgaB : g * a ∉ B₁ := fun hh => hgB₁ (by
      have := mul_mem hh (inv_mem haB₁)
      simpa using this)
    have hga1 : g * a ≠ 1 := fun h1 => hgaB (h1 ▸ one_mem _)
    have hg1 : g ≠ 1 := fun h1 => hgB₁ (h1 ▸ one_mem _)
    have hgaA : g * a ∈ A := mul_mem hgA ha.mem
    have hE₁ := zpowers_mem_E1 h hgA hg1
    have hE₂ := zpowers_mem_E1 h hgaA hga1
    have hn₁ : Subgroup.zpowers g ∉ rSetN p A θ 1 := fun hh =>
      ((h.zpowers_mem_rSetN_one_iff).mp hh).2.2 (hsolv g hgA hg1 hgB₁)
    have hn₂ : Subgroup.zpowers (g * a) ∉ rSetN p A θ 1 := fun hh =>
      ((h.zpowers_mem_rSetN_one_iff).mp hh).2.2 (hsolv (g * a) hgaA hga1 hgaB)
    have heq := eq_of_not_mem_rSetN h hE₁ hE₂ hn₁ hn₂
    have haz : a ∈ Subgroup.zpowers g := by
      have : g * a ∈ Subgroup.zpowers g := heq ▸ Subgroup.mem_zpowers _
      have := mul_mem (inv_mem (Subgroup.mem_zpowers g)) this
      simpa using this
    have hzz := eq_zpowers_of_mem h (zpowers_mem_E1 h hgA hg1) haz ha.ne_one
    have hgz : g ∈ Subgroup.zpowers a := hzz ▸ Subgroup.mem_zpowers g
    exact hgB₁ (Subgroup.zpowers_le.mpr haB₁ hgz)
  obtain ⟨B, hB, hxB⟩ := h.exists_rSetN_two_ge (hxn.zpowers_mem_rSet h)
  have hxB' : x ∈ B := hxB (Subgroup.mem_zpowers x)
  obtain ⟨hB1, hBA, hBns, hBcard⟩ := h.mem_rSetN_iff.mp hB
  have hBE : B ∈ signalizerFunctorEk p 2 A := ⟨hBA, hBcard⟩
  have hBV : ¬ B ≤ B₁ := fun hle => hxB₁ (hle hxB')
  obtain ⟨u, hu, hu1, hUu⟩ := exists_zpowers_ge_inf h hBE hBV
  have hnot := not_forall_simple h hB hu hu1
  push Not at hnot
  obtain ⟨b, hbB, hbu, hbF⟩ := hnot
  have hb1 : b ≠ 1 := fun h1 => hbu (h1 ▸ one_mem _)
  have hbA : b ∈ A := hBA hbB
  have hbn := NT.of_mem_rSetN_two h hB hbB hb1
  have hbB₁ : b ∉ B₁ := fun hb => hbu (hUu ⟨hbB, hb⟩)
  have hbc : b ∉ Subgroup.centralizer (J : Set G) := fun hb => hbB₁ ⟨hbA, by
    show b ∈ Subgroup.centralizer (kOf (θ a) : Set G)
    rw [hKJ]
    exact hb⟩
  have hbN : b ∈ A ⊓ Subgroup.normalizer (J : Set G) := ⟨hbA, hAN b hbA⟩
  have hbFNa : b ∈ FN A θ a := by rw [hs]; exact hbA
  have hΓsol : Group.IsSolvable (thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) :=
    ha.isSolvable_of_mem_FN h hbFNa hJ hbc
  have haFNb : a ∈ FN A θ b := by
    refine hbn.mem_FN_of_isSolvable h ha.mem ha.ne_one ?_
    rw [sup_comm]
    exact hΓsol
  obtain ⟨J₁, hJ₁, J₂, hJ₂, hne12⟩ : ∃ J₁ ∈ lcal (θ b), ∃ J₂ ∈ lcal (θ b), J₁ ≠ J₂ := by
    have hg : ∃ g ∈ A, g ∉ FN A θ b := by
      by_contra hcon
      push Not at hcon
      exact hbF (le_antisymm (FN_le b) (fun x hx => hcon x hx))
    obtain ⟨g', hg'A, hg'⟩ := hg
    have hJ : ∃ J ∈ lcal (θ b), g' ∉ Subgroup.normalizer (J : Set G) := by
      by_contra hcon
      push Not at hcon
      exact hg' (mem_FN_iff.mpr ⟨hg'A, hcon⟩)
    obtain ⟨J₁, hJ₁, hg'J₁⟩ := hJ
    refine ⟨J₁, hJ₁, J₁.map (MulAut.conj g').toMonoidHom, hbn.conj_mem_lcal h hg'A hJ₁,
      fun heq => hg'J₁ ?_⟩
    exact Nonsolv.L69.map_conj_eq_self_iff.mp heq.symm
  have hac : a ∉ Subgroup.centralizer (J₁ : Set G) := by
    intro hac
    have hK : a ∈ Subgroup.centralizer (kOf (θ b) : Set G) :=
      hbn.mem_centralizer_kOf h hJ₁ ha.mem hac
    have hKc : kOf (θ b) ≤ Subgroup.centralizer ({a} : Set G) := fun k hk =>
      Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hK k hk)
    rw [← centralizer_zpowers_eq_singleton] at hKc
    have hle : kOf (θ b) ≤ thetaOf θ (Subgroup.zpowers b ⊔ Subgroup.zpowers a) := by
      rw [← hF.inf_centralizer_eq_thetaOf hbn.mem hbn.ne_one (Subgroup.zpowers_le.mpr ha.mem)]
      exact le_inf (kOf_le _) hKc
    have hsolK : Group.IsSolvable ↥(kOf (θ b)) := by
      rw [sup_comm] at hle
      have : Group.IsSolvable ↥(thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b)) := hΓsol
      exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    exact h.not_isSolvable_kOf (h.apply_mem_cset_bot hbA hb1 hbn.not_solvable) hsolK
  have hL := hbn.isDirectProduct h
  have hA' : ∀ x ∈ A, ∀ J' ∈ lcal (θ b), J'.map (MulAut.conj x).toMonoidHom ∈ lcal (θ b) :=
    fun x hx J' hJ' => hbn.conj_mem_lcal h hx hJ'
  have hTA : J ⊓ Subgroup.centralizer ({b} : Set G) = J ⊓ Subgroup.centralizer (A : Set G) := by
    rw [ha.cenIn_singleton_eq h hJ hbN hbc]
    have : A ⊓ Subgroup.normalizer (J : Set G) = A := inf_eq_left.mpr (fun x hx => hAN x hx)
    rw [this]
  have hTb : J ⊓ Subgroup.centralizer (A : Set G) =
      kOf (θ b) ⊓ Subgroup.centralizer (A : Set G) := by
    rw [← hKJ]
    exact kOf_inf_centralizer_eq_of_NT h ha hbn
  have hΓeq : θ a ⊓ Subgroup.centralizer ({b} : Set G) =
      thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    rw [← centralizer_zpowers_eq_singleton]
    exact hF.inf_centralizer_eq_thetaOf ha.mem ha.ne_one (Subgroup.zpowers_le.mpr hbA)
  have hΓ'eq : θ b ⊓ Subgroup.centralizer ({a} : Set G) =
      thetaOf θ (Subgroup.zpowers a ⊔ Subgroup.zpowers b) := by
    rw [← centralizer_zpowers_eq_singleton, hF.inf_centralizer_eq_thetaOf hbn.mem hbn.ne_one
      (Subgroup.zpowers_le.mpr ha.mem), sup_comm]
  have hNT : ∀ n ∈ J₁ ⊓ Subgroup.centralizer ({a} : Set G),
      ∀ t ∈ J ⊓ Subgroup.centralizer (A : Set G),
        n * t * n⁻¹ ∈ J ⊓ Subgroup.centralizer (A : Set G) := by
    intro n hn t ht
    rw [← hTA] at ht ⊢
    have hn' : n ∈ θ a ⊓ Subgroup.centralizer ({b} : Set G) := by
      rw [hΓeq, ← hΓ'eq]
      exact ⟨lcal_le hJ₁ hn.1, hn.2⟩
    have hnK : n ∈ Subgroup.normalizer (J : Set G) := by
      rw [← hKJ]
      exact Nonsolv.le_normalizer_kOf (θ a) hn'.1
    refine ⟨(Subgroup.mem_normalizer_iff.mp hnK t).mp ht.1, ?_⟩
    show n * t * n⁻¹ ∈ Subgroup.centralizer ({b} : Set G)
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp hn'.2
    have h2 := Subgroup.mem_centralizer_singleton_iff.mp ht.2
    have h3 : n⁻¹ * b = b * n⁻¹ := by
      have := congrArg (fun y => n⁻¹ * y * n⁻¹) h1
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel, mul_one] at this
      exact this.symm
    calc n * t * n⁻¹ * b = n * t * (n⁻¹ * b) := by group
      _ = n * t * (b * n⁻¹) := by rw [h3]
      _ = n * (t * b) * n⁻¹ := by group
      _ = n * (b * t) * n⁻¹ := by rw [h2]
      _ = (n * b) * t * n⁻¹ := by group
      _ = (b * n) * t * n⁻¹ := by rw [h1]
      _ = b * (n * t * n⁻¹) := by group
  have hNP : J₁ ⊓ Subgroup.centralizer ({a} : Set G) ≤
      projIn (lcal (θ b)) J₁ (J ⊓ Subgroup.centralizer (A : Set G)) := by
    rw [hTb, projIn_centralizer_eq hL hA' hJ₁]
    have haN : a ∈ A ⊓ Subgroup.normalizer (J₁ : Set G) := by
      refine ⟨ha.mem, ?_⟩
      have := (mem_FN_iff.mp haFNb).2 J₁ hJ₁
      exact this
    rw [← hbn.cenIn_singleton_eq h hJ₁ haN hac]
  have htrans : ∀ K ∈ lcal (θ b), ∃ x ∈ A, K = J₂.map (MulAut.conj x).toMonoidHom :=
    fun K hK => hbn.exists_conj_A h hJ₂ hK
  have hinj : (J ⊓ Subgroup.centralizer (A : Set G)) ⊓ sSup (lcal (θ b) \ {J₂}) = ⊥ := by
    rw [hTb]
    exact inf_centralizer_inf_sSup_eq_bot_of_transitive hL hA' hJ₂ htrans
  have hcomm := commute_of_normalizes hL hJ₁ hne12 hinj inf_le_left hNT hNP
  have hFr := hbn.cenIn_singleton_eq h hJ₁ (⟨ha.mem, (mem_FN_iff.mp haFNb).2 J₁ hJ₁⟩) hac
  apply hbn.not_isMulCommutative_cenIn_norIn h hJ₁
  rw [← hFr]
  exact isMulCommutative_iff.mpr fun x y => Subtype.ext (hcomm x x.2 y y.2)

end R0

end Sec6S33

end CFSG.SignalizerFunctorTheorem.McBride.Near
