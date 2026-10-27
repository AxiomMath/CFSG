module

public import CFSG.Timmesfeld.Orders.Bang
public import CFSG.LieType.Universal.Unitary.Clause0
import CFSG.LinearAlgebra.PrimeOrderFixedPoints
import CFSG.GH74.GLS.Stage2.Final.ModelOrd

public section

namespace CFSG.RankThree.GF2n.Tim81.TIModule

open CFSG.Timmesfeld CFSG.Open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

section Ppd

variable {G W : Type*} [Group G] [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem pow_le_natCard_of_ppd (σ : Representation (ZMod 2) G W) {g : G} {r k : ℕ}
    (hr : IsPrimitivePrimeDivisor r k) (hk : 0 < k) (hg : orderOf g = r) (hσg : σ g ≠ 1) :
    2 ^ k ≤ Nat.card W := by
  obtain ⟨b, hb, hbW, hdvd⟩ := CFSG.LinearAlgebra.exists_prime_dvd_two_pow_sub_one_of_ne_one σ
    hr.prime (hr.ne_two hk) hg hσg
  exact (Nat.pow_le_pow_right (by norm_num)
    (Nat.le_of_dvd hb ((hr.dvd_sub_one_iff hk b).mp hdvd))).trans hbW

theorem eq_one_of_fix_of_sub_mem (σ : Representation (ZMod 2) G W) {g : G}
    (hg : Odd (orderOf g)) {U : Submodule (ZMod 2) W} (h1 : ∀ u ∈ U, σ g u = u)
    (h2 : ∀ w, σ g w - w ∈ U) : σ g = 1 := by
  have hsq : σ g ^ 2 = 1 := by
    refine LinearMap.ext fun w => ?_
    have hu : σ g (σ g w - w) = σ g w - w := h1 _ (h2 w)
    rw [map_sub] at hu
    have h' : σ g (σ g w) = w + ((σ g w - w) + (σ g w - w)) := by
      rw [sub_eq_iff_eq_add.mp hu]
      abel
    rw [pow_two, Module.End.mul_apply, Module.End.one_apply, h', ZModModule.add_self, add_zero]
  obtain ⟨t, ht⟩ := hg
  have hpow : σ g ^ (2 * t + 1) = 1 := by
    rw [← map_pow, ← ht, pow_orderOf_eq_one, map_one]
  rwa [pow_succ, pow_mul, hsq, one_pow, one_mul] at hpow

private theorem natCard_lt_of_ne_top {U : Submodule (ZMod 2) W} (hU : U ≠ ⊤) :
    Nat.card U < Nat.card W := by
  have h : (↑U : Set W) ⊂ Set.univ := by
    rw [Set.ssubset_iff_subset_ne]
    exact ⟨Set.subset_univ _, by simpa using hU⟩
  simpa using Set.Finite.card_lt_card (Set.toFinite (Set.univ : Set W)) h

private theorem natCard_quotient_lt_of_ne_bot {U : Submodule (ZMod 2) W} (hU : U ≠ ⊥) :
    Nat.card (W ⧸ U) < Nat.card W := by
  obtain ⟨x, hx, hx0⟩ : ∃ x : W, x ∈ U ∧ x ≠ 0 := by
    simpa [Submodule.eq_bot_iff] using hU
  haveI : Nontrivial U := ⟨⟨x, hx⟩, ⟨0, U.zero_mem⟩, fun h => hx0 (congrArg Subtype.val h)⟩
  haveI : Finite (W ⧸ U) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective U)
  have h1 : 1 < Nat.card U := Finite.one_lt_card
  rw [Submodule.card_eq_card_quotient_mul_card U]
  exact (Nat.lt_mul_iff_one_lt_left Nat.card_pos).2 h1

variable (σ : Representation (ZMod 2) G W) (hG : IsQuasisimple G) {g : G} {r k : ℕ}
  (hr : IsPrimitivePrimeDivisor r k) (hk : 0 < k) (hg : orderOf g = r)
  (hgZ : g ∉ Subgroup.center G)

include hG hgZ in
private theorem eq_one_of_apply_eq_one {V : Type*} [AddCommGroup V] [Module (ZMod 2) V]
    (τ : Representation (ZMod 2) G V) (hτ : τ g = 1) (x : G) : τ x = 1 := by
  rcases CFSG.LieType.CurtisTits.le_center_or_eq_top_of_isQuasisimple hG τ.ker with h | h
  · exact absurd (h (MonoidHom.mem_ker.mpr hτ)) hgZ
  · exact MonoidHom.mem_ker.mp (h ▸ Subgroup.mem_top x)

private abbrev subrep {U : Submodule (ZMod 2) W} (hU : ∀ x, ∀ u ∈ U, σ x u ∈ U) :
    Subrepresentation σ :=
  { toSubmodule := U, apply_mem_toSubmodule := fun x u hu => hU x u hu }

private theorem fix_of_subrep {U : Submodule (ZMod 2) W} (hU : ∀ x, ∀ u ∈ U, σ x u ∈ U)
    (h : (subrep σ hU).toRepresentation g = 1) (hG : IsQuasisimple G)
    (hgZ : g ∉ Subgroup.center G) : ∀ x, ∀ u ∈ U, σ x u = u := by
  intro x u hu
  have hx := LinearMap.congr_fun (eq_one_of_apply_eq_one hG hgZ _ h x) ⟨u, hu⟩
  exact Subrepresentation.toRepresentation_apply_coe.mp hx

private theorem sub_mem_of_quotient {U : Submodule (ZMod 2) W} (hU : ∀ x, ∀ u ∈ U, σ x u ∈ U)
    (h : (subrep σ hU).quotient g = 1) (hG : IsQuasisimple G)
    (hgZ : g ∉ Subgroup.center G) : ∀ x w, σ x w - w ∈ U := by
  intro x w
  have hx := LinearMap.congr_fun (eq_one_of_apply_eq_one hG hgZ _ h x)
    (Submodule.Quotient.mk w)
  have hmk : (subrep σ hU).quotient x (Submodule.Quotient.mk (p := U) w) =
      (Submodule.Quotient.mk (p := U) (σ x w) : W ⧸ U) :=
    Subrepresentation.quotient_apply_mk (subrep σ hU) x w
  rw [hmk, Module.End.one_apply] at hx
  exact (Submodule.Quotient.eq U).mp hx

include hG hr hk hg hgZ in
theorem fix_or_sub_mem_of_ppd (hW : Nat.card W < 2 ^ (2 * k)) {U : Submodule (ZMod 2) W}
    (hU : ∀ x, ∀ u ∈ U, σ x u ∈ U) :
    (∀ x, ∀ u ∈ U, σ x u = u) ∨ ∀ x w, σ x w - w ∈ U := by
  haveI : Finite (W ⧸ U) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective U)
  by_cases h1 : (subrep σ hU).toRepresentation g = 1
  · exact Or.inl (fix_of_subrep σ hU h1 hG hgZ)
  by_cases h2 : (subrep σ hU).quotient g = 1
  · exact Or.inr (sub_mem_of_quotient σ hU h2 hG hgZ)
  exfalso
  have hU1 : 2 ^ k ≤ Nat.card U := pow_le_natCard_of_ppd _ hr hk hg h1
  have hU2 : 2 ^ k ≤ Nat.card (W ⧸ U) := pow_le_natCard_of_ppd _ hr hk hg h2
  have hle : 2 ^ (2 * k) ≤ Nat.card W := by
    rw [Submodule.card_eq_card_quotient_mul_card U, two_mul, pow_add]
    exact Nat.mul_le_mul hU1 hU2
  omega

include hG hr hk hg hgZ in
theorem apply_ne_one_of_ppd (hσ : ∃ x w, σ x w ≠ w) : σ g ≠ 1 := by
  intro h1
  obtain ⟨x, w, hw⟩ := hσ
  exact hw (by rw [eq_one_of_apply_eq_one hG hgZ σ h1 x, Module.End.one_apply])

include hG hr hk hg hgZ in
theorem eq_bot_or_eq_top_of_ppd (hσ : ∃ x w, σ x w ≠ w) (hW : Nat.card W ≤ 2 ^ k)
    {U : Submodule (ZMod 2) W} (hU : ∀ x, ∀ u ∈ U, σ x u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  haveI : Finite (W ⧸ U) := Finite.of_surjective _ (Submodule.Quotient.mk_surjective U)
  by_cases h1 : (subrep σ hU).toRepresentation g = 1
  · by_cases h2 : (subrep σ hU).quotient g = 1
    · exfalso
      refine apply_ne_one_of_ppd σ hG hr hk hg hgZ hσ (eq_one_of_fix_of_sub_mem σ
        (hg ▸ (hr.prime.odd_of_ne_two (hr.ne_two hk))) (U := U) ?_ ?_)
      · exact fix_of_subrep σ hU h1 hG hgZ g
      · exact sub_mem_of_quotient σ hU h2 hG hgZ g
    · left
      by_contra hne
      have h3 : 2 ^ k ≤ Nat.card (W ⧸ U) := pow_le_natCard_of_ppd _ hr hk hg h2
      have h4 := natCard_quotient_lt_of_ne_bot hne
      omega
  · right
    by_contra hne
    have h3 : 2 ^ k ≤ Nat.card U := pow_le_natCard_of_ppd _ hr hk hg h1
    have h4 := natCard_lt_of_ne_top hne
    omega

include hG hr hk hg hgZ in
theorem pow_le_natCard_of_sub_mem (hσ : ∃ x w, σ x w ≠ w) {U : Submodule (ZMod 2) W}
    (hU : ∀ x, ∀ u ∈ U, σ x u ∈ U) (hsub : ∀ x w, σ x w - w ∈ U) : 2 ^ k ≤ Nat.card U := by
  by_cases h1 : (subrep σ hU).toRepresentation g = 1
  · exfalso
    exact apply_ne_one_of_ppd σ hG hr hk hg hgZ hσ (eq_one_of_fix_of_sub_mem σ
      (hg ▸ (hr.prime.odd_of_ne_two (hr.ne_two hk))) (U := U) (fix_of_subrep σ hU h1 hG hgZ g)
      (hsub g))
  · exact pow_le_natCard_of_ppd _ hr hk hg h1

end Ppd

section SU

variable {F : Type} [Field F] [Finite F] [CharP F 2] {f n : ℕ}

private theorem pair_ne_of_two_le (hf : 2 ≤ f) (n : ℕ) : (n, 2 ^ f) ≠ (3, 2) := by
  intro h
  have h2 : 2 ^ f = 2 ^ 1 := congrArg Prod.snd h
  have := Nat.pow_right_injective (le_refl 2) h2
  omega

theorem isQuasisimple_SU_of_two_le (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hn : 3 ≤ n) :
    IsQuasisimple (SU (unitaryInvolution F 2 f) n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact isQuasisimple_SU hF hn (pair_ne_of_two_le hf n)

private theorem natCard_center_SU (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hn : 3 ≤ n) :
    Nat.card (Subgroup.center (SU (unitaryInvolution F 2 f) n)) = Nat.gcd n (2 ^ f + 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcenterStated : Nat.card (Subgroup.center (StatedSU n (2 ^ f) F)) =
      Nat.gcd n (2 ^ f + 1) := by
    rw [(isQuasisimple_statedSU_of_card (p := 2) (f := f) hF hn (pair_ne_of_two_le hf n)).2]
    exact (CFSG.LinearGroups.unitary_scalar_kernel (p := 2) (f := f) Nat.prime_two hF
      (n := n) (by omega)).2.2
  rw [← hcenterStated, ← Subgroup.map_center_eq (equivStatedSU (p := 2) (f := f) hF n),
    Subgroup.card_map_of_injective (equivStatedSU (p := 2) (f := f) hF n).injective]

private theorem ppd_dvd_natCard_SU (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {i r : ℕ}
    (hi : Odd i) (hi3 : 3 ≤ i) (hin : i ≤ n) (hr : IsPrimitivePrimeDivisor r (2 * f * i)) :
    r ∣ Nat.card (SU (unitaryInvolution F 2 f) n) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hk0 : 0 < 2 * f * i := by positivity
  have hr1 : r ∣ 2 ^ (f * i) + 1 := by
    refine (hr.dvd_add_one_iff hk0 (f * i)).2 ⟨⟨1, by ring⟩, ?_⟩
    exact Nat.not_dvd_of_pos_of_lt (by positivity) (by nlinarith)
  have hud : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 f F :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hcard := CFSG.GH74.GLS.Stage2.Final.ModelOrd.card_statedSU_int hud (n := n) (by omega)
  rw [Nat.card_congr (equivStatedSU (p := 2) (f := f) hF n).toEquiv]
  have hz : ((r : ℕ) : ℤ) ∣ (Nat.card (StatedSU n (2 ^ f) F) : ℤ) := by
    rw [hcard]
    refine Dvd.dvd.mul_left ?_ _
    refine dvd_trans ?_ (Finset.dvd_prod_of_mem _ (Finset.mem_Icc.2 ⟨by omega, hin⟩))
    rw [hi.neg_one_pow, sub_neg_eq_add]
    have hcast : ((2 ^ f : ℕ) : ℤ) ^ i + 1 = ((2 ^ (f * i) + 1 : ℕ) : ℤ) := by
      push_cast
      ring
    rw [hcast]
    exact Int.natCast_dvd_natCast.2 hr1
  exact Int.natCast_dvd_natCast.1 hz

theorem exists_ppd_SU (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) {i : ℕ} (hi : Odd i)
    (hi3 : 3 ≤ i) (hin : i ≤ n) :
    ∃ (r : ℕ) (g : SU (unitaryInvolution F 2 f) n), IsPrimitivePrimeDivisor r (2 * f * i) ∧
      orderOf g = r ∧ g ∉ Subgroup.center (SU (unitaryInvolution F 2 f) n) := by
  have h12 : 12 ≤ 2 * f * i := by nlinarith
  obtain ⟨r, hr⟩ := exists_isPrimitivePrimeDivisor (k := 2 * f * i) (by omega) (by omega)
  haveI : Fact r.Prime := ⟨hr.prime⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' r (ppd_dvd_natCard_SU hF hf hi hi3 hin hr)
  refine ⟨r, g, hr, hg, fun hgZ => ?_⟩
  have hdvd : r ∣ Nat.card (Subgroup.center (SU (unitaryInvolution F 2 f) n)) := by
    have := Subgroup.orderOf_dvd_natCard (Subgroup.center (SU (unitaryInvolution F 2 f) n)) hgZ
    rwa [hg] at this
  rw [natCard_center_SU hF hf (by omega)] at hdvd
  have h1 := (hr.dvd_add_one_iff (by omega) f).1 (hdvd.trans (Nat.gcd_dvd_right _ _))
  have := Nat.le_of_dvd (by omega) h1.1
  nlinarith

variable {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem eq_bot_or_eq_top_SU_of_odd (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hn : 3 ≤ n)
    (hodd : Odd n) (σ : Representation (ZMod 2) (SU (unitaryInvolution F 2 f) n) W)
    (hσ : ∃ x w, σ x w ≠ w) (hW : Nat.card W ≤ (2 ^ f) ^ (2 * n)) {U : Submodule (ZMod 2) W}
    (hU : ∀ x, ∀ u ∈ U, σ x u ∈ U) : U = ⊥ ∨ U = ⊤ := by
  obtain ⟨r, g, hr, hg, hgZ⟩ := exists_ppd_SU hF hf hodd hn le_rfl
  refine eq_bot_or_eq_top_of_ppd σ (isQuasisimple_SU_of_two_le hF hf hn) hr (by positivity) hg
    hgZ hσ ?_ hU
  calc Nat.card W ≤ (2 ^ f) ^ (2 * n) := hW
    _ = 2 ^ (2 * f * n) := by rw [← pow_mul]; ring_nf

theorem fix_or_sub_mem_SU (hF : Nat.card F = (2 ^ f) ^ 2) (hf : 2 ≤ f) (hn : 4 ≤ n)
    (σ : Representation (ZMod 2) (SU (unitaryInvolution F 2 f) n) W)
    (hW : Nat.card W ≤ (2 ^ f) ^ (2 * n)) :
    (∀ {U : Submodule (ZMod 2) W}, (∀ x, ∀ u ∈ U, σ x u ∈ U) →
      (∀ x, ∀ u ∈ U, σ x u = u) ∨ ∀ x w, σ x w - w ∈ U) ∧
    ((∃ x w, σ x w ≠ w) → ∀ {U : Submodule (ZMod 2) W}, (∀ x, ∀ u ∈ U, σ x u ∈ U) →
      (∀ x w, σ x w - w ∈ U) → (2 ^ f) ^ (2 * (n - 1)) ≤ Nat.card U) := by
  obtain ⟨i, hi, hi3, hin, h2i⟩ : ∃ i, Odd i ∧ 3 ≤ i ∧ i ≤ n ∧ n - 1 ≤ i := by
    rcases Nat.even_or_odd n with he | ho
    · exact ⟨n - 1, by
        obtain ⟨j, rfl⟩ := he
        exact ⟨j - 1, by omega⟩, by omega, by omega, le_rfl⟩
    · exact ⟨n, ho, by omega, le_rfl, by omega⟩
  obtain ⟨r, g, hr, hg, hgZ⟩ := exists_ppd_SU hF hf hi hi3 hin
  have hG := isQuasisimple_SU_of_two_le hF hf (by omega : 3 ≤ n)
  have hk : 0 < 2 * f * i := by positivity
  have h2i' : n < 2 * i := by omega
  refine ⟨fun hU => fix_or_sub_mem_of_ppd σ hG hr hk hg hgZ ?_ hU, ?_⟩
  · calc Nat.card W ≤ (2 ^ f) ^ (2 * n) := hW
      _ = 2 ^ (2 * f * n) := by rw [← pow_mul]; ring_nf
      _ < 2 ^ (2 * (2 * f * i)) := Nat.pow_lt_pow_right (by norm_num) (by nlinarith)
  · intro hσ U hU hsub
    calc (2 ^ f) ^ (2 * (n - 1)) = 2 ^ (2 * f * (n - 1)) := by rw [← pow_mul]; ring_nf
      _ ≤ 2 ^ (2 * f * i) := Nat.pow_le_pow_right (by norm_num)
          (Nat.mul_le_mul_left _ h2i)
      _ ≤ Nat.card U := pow_le_natCard_of_sub_mem σ hG hr hk hg hgZ hσ hU hsub

end SU

end CFSG.RankThree.GF2n.Tim81.TIModule
