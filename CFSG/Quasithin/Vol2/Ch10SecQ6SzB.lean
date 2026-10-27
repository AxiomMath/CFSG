module

public import CFSG.Quasithin.Vol2.Ch10SecQ6SzA
public import CFSG.LieType.Suzuki.SuzukiOuterCyclic
public import CFSG.LieType.Ree.SuzukiSimple
public import CFSG.Quasithin.Vol2.Ch10SecQ6Rk

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

namespace C10P06

open Matrix CFSG.Blueprint CFSG.LieType.Ree CFSG.Open

variable {W : Type*} [CommGroup W] {a : ℕ} {K : Type} [Field K]

theorem eq_one_of_centralizes_sz [CharP K 2] [Finite K]
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {Λ : Subgroup (MulAut W)} {π : suzukiGroup a K →* Λ}
    {Ψ : W → Fin 4 → K} (hc : IsSzCoord a Λ π Ψ) {e : MulAut W} (he2 : e * e = 1)
    (hec : ∀ l ∈ Λ, e * l = l * e) : e = 1 := by
  obtain ⟨-, hmul, ⟨hinj, honto⟩, heq⟩ := hc
  have hcomm : ∀ γ w, e ((π γ : MulAut W) w) = (π γ : MulAut W) (e w) := fun γ w => by
    rw [← MulAut.mul_apply, hec _ (π γ).2, MulAut.mul_apply]
  have hee : ∀ w, e (e w) = w := fun w => by
    rw [← MulAut.mul_apply, he2]
    rfl
  have hΨ1 : Ψ 1 = 0 := by
    have h := hmul 1 1
    rw [mul_one] at h
    exact add_eq_left.mp h.symm
  obtain ⟨w₄, hw₄⟩ := honto (Pi.single 3 1)
  have hfix : (suzukiS a 1 0).mulVec (Ψ (e w₄)) = Ψ (e w₄) := by
    have h1 : (π (suzukiSElt a K 1 0) : MulAut W) w₄ = w₄ :=
      hinj (by rw [heq, coe_suzukiSElt, hw₄, suzukiS_e4])
    rw [← coe_suzukiSElt a K 1 0, ← heq, ← hcomm, h1]
  have hμ := suzukiS_one_zero_fix hfix
  set μ := Ψ (e w₄) 3 with hμdef
  have hμ0 : μ ≠ 0 := by
    intro h0
    have h1 : e w₄ = 1 := hinj (by rw [hμ, h0, hΨ1, Pi.single_zero])
    have h2 : w₄ = 1 := by rw [← hee w₄, h1, map_one]
    have h3 := congrFun hw₄ 3
    rw [h2, hΨ1] at h3
    simp at h3
  obtain ⟨l, hl⟩ := exists_zpow_eq hK (Units.mk0 μ hμ0)
  have hew : e w₄ = (π (suzukiDElt a K l) : MulAut W) w₄ := hinj (by
    rw [heq, coe_suzukiDElt, hw₄, suzukiD_e4, hl, Units.val_mk0, mul_one]
    exact hμ)
  have h2 : Ψ w₄ = Pi.single 3 (μ * μ) :=
    calc Ψ w₄ = Ψ (e (e w₄)) := by rw [hee]
      _ = Ψ (e ((π (suzukiDElt a K l) : MulAut W) w₄)) := by rw [← hew]
      _ = Ψ ((π (suzukiDElt a K l) : MulAut W) (e w₄)) := by rw [hcomm]
      _ = (suzukiD a l).mulVec (Ψ (e w₄)) := by rw [heq, coe_suzukiDElt]
      _ = (suzukiD a l).mulVec (Pi.single 3 μ) := by rw [hμ]
      _ = Pi.single 3 (μ * μ) := by rw [suzukiD_e4, hl, Units.val_mk0]
  have hμ1 : μ = 1 := by
    have h3 := congrFun (hw₄.symm.trans h2) 3
    simp only [Pi.single_eq_same] at h3
    exact eq_one_of_sq_eq_one_char_two (by rw [sq]; exact h3.symm)
  have hew1 : e w₄ = w₄ := hinj (by rw [hμ, hμ1, hw₄])
  have hfixc : ∀ c : K, ∃ w, Ψ w = Pi.single 3 c ∧ e w = w := by
    intro c
    by_cases hc0 : c = 0
    · exact ⟨1, by rw [hΨ1, hc0, Pi.single_zero], map_one e⟩
    · obtain ⟨l', hl'⟩ := exists_zpow_eq hK (Units.mk0 c hc0)
      exact ⟨(π (suzukiDElt a K l') : MulAut W) w₄, by
        rw [heq, coe_suzukiDElt, hw₄, suzukiD_e4, hl', Units.val_mk0, mul_one], by
        rw [hcomm, hew1]⟩
  have hall : ∀ x, ∃ w, Ψ w = x ∧ e w = w := fun x =>
    sz_induction (P := fun x => ∃ w, Ψ w = x ∧ e w = w)
      (fun x y ⟨w, hw, hew⟩ ⟨w', hw', hew'⟩ =>
        ⟨w * w', by rw [hmul, hw, hw'], by rw [map_mul, hew, hew']⟩)
      (fun g c => by
        obtain ⟨w, hw, hew⟩ := hfixc c
        exact ⟨(π g : MulAut W) w, by rw [heq, hw]; rfl, by rw [hcomm, hew]⟩) x
  ext w
  obtain ⟨w', hw', hew'⟩ := hall (Ψ w)
  rw [← hinj hw']
  exact hew'

theorem center_suzuki_eq_bot [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) : Subgroup.center (suzukiGroup a K) = ⊥ := by
  obtain ⟨-, -, hsimple⟩ := suzuki_simple ha hK
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center (suzukiGroup a K)) with h | h
  · exact h
  · have h1 := (suzuki_perfect ha hK).1
    rw [(commutator_eq_bot_iff_center_eq_top _).2 h] at h1
    exact absurd h1 bot_ne_top

theorem card_le_of_elem_aut_sz [Finite K] (ha : 1 ≤ a)
    (hK : Nat.card K = 2 ^ (2 * a + 1)) {A : Subgroup (MulAut (suzukiGroup a K))}
    (hc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (h2 : ∀ x ∈ A, x * x = 1) :
    Nat.card A ≤ 2 ^ (2 * a + 1) := by
  have : Finite (suzukiGroup a K) := (suzuki_simple ha hK).1
  have hinj : Function.Injective
      (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro g hg
    rw [MonoidHom.mem_ker] at hg
    have hgZ : g ∈ Subgroup.center (suzukiGroup a K) := Subgroup.mem_center_iff.2 fun y => by
      have h1 := congrArg (fun α : MulAut (suzukiGroup a K) => α y) hg
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc y * g = g * y * g⁻¹ * g := by rw [h1]
        _ = g * y := by group
    rw [center_suzuki_eq_bot ha hK, Subgroup.mem_bot] at hgZ
    rw [hgZ, Subgroup.mem_bot]
  have hinner : A ≤ (MulAut.conj : suzukiGroup a K →* MulAut (suzukiGroup a K)).range := by
    intro x hx
    obtain ⟨-, hdvd⟩ := CFSG.LieType.Suzuki.suzukiGroup_outer_isCyclic_card_dvd ha hK
    let q := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner
      (suzukiGroup a K))
    have h1 : orderOf (q x) ∣ 2 := orderOf_dvd_of_pow_eq_one (by
      rw [← map_pow, sq, h2 x hx, map_one])
    have h3 : orderOf (q x) ∣ 2 * a + 1 := (orderOf_dvd_natCard (q x)).trans hdvd
    have h4 : orderOf (q x) = 1 :=
      Nat.eq_one_of_dvd_coprimes (Nat.coprime_two_left.mpr (odd_two_mul_add_one a)) h1 h3
    rw [orderOf_eq_one_iff] at h4
    have h5 : x ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner (suzukiGroup a K) :=
      (QuotientGroup.eq_one_iff x).mp h4
    exact h5
  rw [← Subgroup.map_comap_eq_self hinner, Subgroup.card_map_of_injective hinj]
  have hB : IsElemAbelian 2 (A.comap (MulAut.conj : suzukiGroup a K →* MulAut _)) :=
    ⟨⟨⟨fun x y => Subtype.ext (hinj (by
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hc _ x.2 _ y.2))⟩⟩, fun g hg => hinj (by rw [map_pow, sq, h2 _ hg, map_one])⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp (show IsPGroup 2
    (A.comap (MulAut.conj : suzukiGroup a K →* MulAut _)) from fun g =>
      ⟨1, Subtype.ext (by rw [pow_one, Subgroup.coe_pow]; exact hB.2 _ g.2)⟩)
  have hk' := CFSG.TwoRankLowerBound.Helpers.le_twoRank_of_elementary _ _ hB k hk
  rw [CFSG.ShultStronglyClosedTI.SuzukiModel.twoRank_suzukiGroup hK] at hk'
  rw [hk]
  exact Nat.pow_le_pow_right (by norm_num) hk'

end C10P06

open C10P06 in
theorem fact12Sz : Fact12Sz := by
  intro W _ _ _ Λ n _ _ hSz E hEN hEab
  obtain ⟨a, ha, rfl, K, _, _, hK, hreal⟩ := hSz
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : Finite (CFSG.Blueprint.suzukiGroup a K) := (CFSG.LieType.Ree.suzuki_simple ha hK).1
  obtain ⟨π, Ψ, hc⟩ := exists_isSzCoord hreal
  have hπinj : Function.Injective π := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro γ hγ
    rw [MonoidHom.mem_ker] at hγ
    rw [Subgroup.mem_bot]
    have hfixv : ∀ v, ((γ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K).mulVec v = v := fun v => by
      obtain ⟨w, rfl⟩ := hc.2.2.1.2 v
      rw [← hc.2.2.2 γ w, hγ]
      rfl
    refine Subtype.ext (Units.ext ?_)
    ext i j
    have h1 : ((γ : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) i j =
        (Pi.single j (1 : K) : Fin 4 → K) i := by
      have h2 := congrFun (hfixv (Pi.single j 1)) i
      rw [Matrix.mulVec_single_one] at h2
      exact h2
    rw [h1, Subgroup.coe_one, Units.val_one, Matrix.one_apply, Pi.single_apply]
  obtain ⟨A, hAc, hA2, hEA⟩ := exists_elem_aut (MulEquiv.ofBijective π ⟨hπinj, hc.1⟩)
    (fun x hx2 hxc => eq_one_of_centralizes_sz hK hc hx2 hxc) hEN hEab
  calc Nat.card E ≤ Nat.card A := hEA
    _ ≤ 2 ^ (2 * a + 1) := card_le_of_elem_aut_sz ha hK hAc hA2

end CFSG.Quasithin.Vol2.Ch10.SecD
