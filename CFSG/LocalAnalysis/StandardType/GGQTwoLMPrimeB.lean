module

public import CFSG.LocalAnalysis.StandardType.GGQTwoLMFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLCx
public import CFSG.Adapters.LieModelUnitaryOuter

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.Blueprint CFSG.Open CFSG.StandardType.UCoord
open CFSG.ComponentClassification.OuterAutomorphisms

private theorem qTwoLMPrimeB_inner_of_pow_three {X R : Type} [Group X] [Group R]
    {m : ℕ} (hL : LieModel X .PSU m 2 1) (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m)
    (e : X ≃* R) {φ : MulAut R} (hφ : φ ^ 3 = 1) :
    φ ∈ Set.range (MulAut.conj : R →* MulAut R) := by
  classical
  have hq : ¬ (m = 3 ∧ 2 ^ 1 = 2) := by
    rintro ⟨rfl, -⟩
    omega
  have hcop : Nat.Coprime m 3 :=
    ((Nat.prime_three.coprime_iff_not_dvd).mpr h3).symm
  have hg : Nat.gcd m (2 ^ 1 + 1) = 1 := by
    simpa using hcop.gcd_eq_one
  have hout : Nat.card (Outer R) = 2 := by
    rw [← Nat.card_congr (equivalence e).toEquiv,
      LieModel.card_outer_psu hL (by omega) hq, hg]
  let π : MulAut R →* Outer R :=
    QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner R)
  have hπ : π φ ^ 3 = 1 := by
    rw [← map_pow, hφ, map_one]
  have hdvd3 : orderOf (π φ) ∣ 3 := orderOf_dvd_iff_pow_eq_one.mpr hπ
  have hdvd2 : orderOf (π φ) ∣ 2 := by
    rw [← hout]
    exact orderOf_dvd_natCard (π φ)
  have h1 : orderOf (π φ) = 1 :=
    Nat.eq_one_of_dvd_coprimes (by norm_num : Nat.Coprime 3 2) hdvd3 hdvd2
  have h2 : π φ = 1 := orderOf_eq_one_iff.mp h1
  have h3' : φ ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner R :=
    (QuotientGroup.eq_one_iff
      (N := CFSG.ComponentClassification.OuterAutomorphisms.inner R) φ).mp h2
  simpa [CFSG.ComponentClassification.OuterAutomorphisms.inner, MonoidHom.coe_range] using h3'

private theorem qTwoLMPrimeB_permModel {G : Type} [Group G] [Finite G]
    {B Bs L : Subgroup G} {m : ℕ} (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1)
    (M : QTwoUnitaryModel m L)
    (hrank : 3 ^ 3 ≤ Nat.card (ggGamma L hN).range)
    (hsc : GGTorusSelfCent 3 (ggGamma L hN).range) :
    ∃ Θ : ↥(sumZero m 3) ≃* ↥(ggGamma L hN).range,
      (∀ n : ↥L, MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
        GGTorusWeylElt 3 (ggGamma L hN).range n) ∧
      (∀ σ : Equiv.Perm (Fin m), ∃ (n : ↥L) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
        ggConjAut (ggGamma L hN).range hn = MulAut.congr Θ (permAutV σ)) ∧
      ∀ (n : ↥L) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
        ∃ π : Equiv.Perm (Fin m),
          ggConjAut (ggGamma L hN).range hn = MulAut.congr Θ (permAutV π) := by
  classical
  let _ := M.groupR
  have := M.finiteR
  let ψ : ↥L →* M.R :=
    M.theta.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center L))
  have hψker : ψ.ker ≤ Subgroup.center ↥L := by
    intro l hl
    have h1 : M.theta (QuotientGroup.mk' (Subgroup.center L) l) = 1 := by
      simpa [ψ] using hl
    have h2 : QuotientGroup.mk' (Subgroup.center L) l = 1 :=
      M.theta.injective (by simpa using h1)
    exact (QuotientGroup.eq_one_iff (N := Subgroup.center L) l).mp h2
  have hψbij : Function.Bijective ψ := by
    refine ⟨?_, M.theta.surjective.comp (QuotientGroup.mk'_surjective _)⟩
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro l hl
    have h := hψker hl
    rwa [M.centerBot, Subgroup.mem_bot] at h
  let e : ↥L ≃* M.R := MulEquiv.ofBijective ψ hψbij
  have he : ∀ l : ↥L, e l = ψ l := fun l => MulEquiv.ofBijective_apply ψ _ l
  have hZ : Subgroup.center M.R = ⊥ := by
    have h := center_map_equiv e
    rw [M.centerBot, Subgroup.map_bot] at h
    exact h.symm
  have hAB : IsElemAbelian 3 Bs := hBs.2.1
  have hBp : ∀ b : ↥Bs, b ^ 3 = 1 := fun b =>
    Subtype.ext (by simpa using hAB.2 b b.2)
  have hBc : ∀ a b : ↥Bs, a * b = b * a := fun a b =>
    Subtype.ext (CFSG.Open.IsElemAbelian.comm hAB a.2 b.2)
  have hA : IsElemAbelian 3 (ggGamma L hN).range :=
    isElemAbelian_range hBc hBp (ggGamma L hN)
  have hAI : ∀ a ∈ (ggGamma L hN).range,
      ∃ φ ∈ ({φ : MulAut M.R | φ ^ 3 = 1} : Set (MulAut M.R)),
        ∀ l : ↥L, φ (ψ l) = ψ (a l) := by
    rintro a ha
    refine ⟨MulAut.congr e a, ?_, ?_⟩
    · change (MulAut.congr e a) ^ 3 = 1
      rw [← map_pow (MulAut.congr e), hA.2 a ha, map_one]
    · intro l
      rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply]
      have h : e.symm (ψ l) = l := by
        rw [← he l, MulEquiv.symm_apply_apply]
      rw [h, he (a l)]
  have hIp : ∀ φ ∈ ({φ : MulAut M.R | φ ^ 3 = 1} : Set (MulAut M.R)),
      φ ^ 3 = 1 → φ ∈ Set.range (MulAut.conj : M.R →* MulAut M.R) := by
    intro φ hφ _
    exact qTwoLMPrimeB_inner_of_pow_three hL hm h3 M.theta hφ
  exact exists_permModel (p := 3) (d := m) (R := M.R)
    (I := {φ : MulAut M.R | φ ^ 3 = 1}) Nat.prime_three hZ hIp
    M.centerPrime M.torusPerm hψbij.2 hψker M.perfect hA hAI hrank hsc

theorem qTwoLMSkel_prime_theta {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} (_hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (_hMul : PSUTrivialMultiplier m)
    (M : QTwoUnitaryModel m L)
    (hrank : 3 ^ 3 ≤ Nat.card (ggGamma L hN).range)
    (hsc : GGTorusSelfCent 3 (ggGamma L hN).range) :
    ∃ Θ : ↥(sumZero m 3) ≃* ↥(ggGamma L hN).range,
      (∀ (n : ↥L) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
        ∃ π : Equiv.Perm (Fin m),
          ggConjAut (ggGamma L hN).range hn = MulAut.congr Θ (permAutVHom m 3 π)) ∧
      (∀ σ : Equiv.Perm (Fin m), ∃ (n : ↥L) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L))),
        ggConjAut (ggGamma L hN).range hn = MulAut.congr Θ (permAutVHom m 3 σ)) := by
  obtain ⟨Θ, -, hP, hπ⟩ := qTwoLMPrimeB_permModel hBs hN hm h3 hL M hrank hsc
  exact ⟨Θ, hπ, hP⟩

theorem qTwoLMSkel_prime_link {G : Type} [Group G] [Finite G] {B Bs L : Subgroup G} {x : G}
    {m : ℕ} (_hG : GGThmIHyp 3 B x L) (hBs : GGBstar 3 B Bs)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G)) (hm : 5 ≤ m) (h3 : ¬ 3 ∣ m)
    (hL : LieModel (L ⧸ Subgroup.center L) .PSU m 2 1) (_hMul : PSUTrivialMultiplier m)
    (M : QTwoUnitaryModel m L)
    (hrank : 3 ^ 3 ≤ Nat.card (ggGamma L hN).range)
    (hsc : GGTorusSelfCent 3 (ggGamma L hN).range) :
    ∀ n : ↥L, MulAut.conj n ∈
        Subgroup.normalizer ((ggGamma L hN).range : Set (MulAut ↥L)) →
      ∃ n' : ↥L, (n' : G) ∈ Subgroup.normalizer (Bs : Set G) ∧
        MulAut.conj n' = MulAut.conj n := by
  intro n hn
  obtain ⟨-, hW, -, -⟩ := qTwoLMPrimeB_permModel hBs hN hm h3 hL M hrank hsc
  exact ⟨n, mem_normalizer_of_weyl hN hBs.2.2.2 (n := n) (hW n hn), rfl⟩

end CFSG.StandardType.QTwo

end
