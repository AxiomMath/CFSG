module

public import CFSG.Open.Catalog
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.Lemma37.Covers
import CFSG.LocalAnalysis.QuasithinUnique.RankOneRecognitionCover
import CFSG.LocalAnalysis.SectionRank.EvenCover.SLTwo
import CFSG.LocalAnalysis.SectionRank.Framework.Semisimple
import CFSG.SignalizerFunctorTheorem.McBride.Models.NearSolvable.Orders
import CFSG.SignalizerFunctorTheorem.McBride.Models.Suzuki.Local

public section

open CFSG.Open
open scoped MatrixGroups

namespace CFSG.SignalizerFunctorTheorem.McBride

private theorem exists_subgroup_card_two_mul {K : Type*} [Group K] [Finite K] [Nontrivial K]
    (h2 : IsPGroup 2 K) : ∃ M : Subgroup K, Nat.card K = 2 * Nat.card M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  have hm0 : m ≠ 0 := by
    rintro rfl
    have h1 : Nat.card K = 1 := by simpa using hm
    exact (Finite.one_lt_card (α := K)).ne' h1
  obtain ⟨M, hM⟩ := Sylow.exists_subgroup_card_pow_prime_of_le_card (n := m - 1) Nat.prime_two
    h2 (by rw [hm]; exact Nat.pow_le_pow_right (by norm_num) (Nat.sub_le m 1))
  refine ⟨M, ?_⟩
  rw [hm, hM, ← pow_succ', Nat.sub_add_cancel (Nat.pos_of_ne_zero hm0)]

private theorem ker_eq_center_of_center_eq_bot {C J : Type*} [Group C] [Group J]
    (hJ : Subgroup.center J = ⊥) (ψ : C →* J) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center C) : ψ.ker = Subgroup.center C := by
  refine le_antisymm hker fun q hq => ?_
  have hqJ : ψ q ∈ Subgroup.center J := by
    rw [Subgroup.mem_center_iff]
    intro j
    obtain ⟨r, rfl⟩ := hψ j
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hq r]
  rw [hJ, Subgroup.mem_bot] at hqJ
  exact hqJ

private theorem exists_perfect_cover_kernel_card_two
    {J : Type*} [Group J] [Finite J] (hJ : Subgroup.center J = ⊥)
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 π.ker) (hne : π.ker ≠ ⊥) :
    ∃ (C : Type) (_ : Group C) (_ : Finite C) (ψ : C →* J), commutator C = ⊤ ∧
      Function.Surjective ψ ∧ ψ.ker = Subgroup.center C ∧ Nat.card (Subgroup.center C) = 2 := by
  have : Nontrivial π.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨M₀, hM₀⟩ := exists_subgroup_card_two_mul h2
  set M : Subgroup E := M₀.map π.ker.subtype with hMdef
  have hMk : M ≤ π.ker := Subgroup.map_subtype_le M₀
  have hMcard : Nat.card π.ker = 2 * Nat.card M := by
    rw [hM₀, hMdef, Subgroup.card_map_of_injective π.ker.subtype_injective]
  have : M.Normal := Subgroup.normal_of_le_center (hMk.trans hcen)
  let ψQ : E ⧸ M →* J := QuotientGroup.lift M π hMk
  have hψQ : ∀ x : E, ψQ (x : E ⧸ M) = π x := fun x => rfl
  have hsurjQ : Function.Surjective ψQ := by
    intro j
    obtain ⟨x, rfl⟩ := hπ j
    exact ⟨x, hψQ x⟩
  have hkerQ : ψQ.ker ≤ Subgroup.center (E ⧸ M) := by
    intro q hq
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    have hx : x ∈ π.ker := by
      rw [MonoidHom.mem_ker, ← hψQ]
      exact hq
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hcen hx) y]
  have hJpos : 0 < Nat.card J := Nat.card_pos
  have hMpos : 0 < Nat.card M := Nat.card_pos
  have hE := Subgroup.card_ker_mul_card_of_surjective hπ
  have hQ := Subgroup.card_ker_mul_card_of_surjective hsurjQ
  have hEM := Subgroup.card_eq_card_quotient_mul_card_subgroup M
  have hkerQcard : Nat.card ψQ.ker = 2 := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hJpos hMpos) ?_
    calc Nat.card ψQ.ker * (Nat.card J * Nat.card M)
        = (Nat.card ψQ.ker * Nat.card J) * Nat.card M := by ring
      _ = Nat.card E := by rw [hQ, ← hEM]
      _ = Nat.card π.ker * Nat.card J := hE.symm
      _ = 2 * (Nat.card J * Nat.card M) := by rw [hMcard]; ring
  let C := Shrink.{0} (E ⧸ M)
  let eC : C ≃* (E ⧸ M) := Shrink.mulEquiv
  have : Finite C := Finite.of_equiv _ eC.toEquiv.symm
  let ψ : C →* J := ψQ.comp eC.toMonoidHom
  have hψsurj : Function.Surjective ψ := hsurjQ.comp eC.surjective
  have hψcen : ψ.ker ≤ Subgroup.center C := by
    intro c hc
    have h1 : eC c ∈ Subgroup.center (E ⧸ M) := hkerQ hc
    rw [Subgroup.mem_center_iff] at h1 ⊢
    intro g
    apply eC.injective
    rw [map_mul, map_mul]
    exact h1 (eC g)
  have hψker : ψ.ker = Subgroup.center C :=
    ker_eq_center_of_center_eq_bot hJ ψ hψsurj hψcen
  refine ⟨C, inferInstance, inferInstance, ψ, ?_, hψsurj, hψker, ?_⟩
  · have : Group.IsPerfect C :=
      Group.IsPerfect.ofSurjective (f := eC.symm.toMonoidHom) eC.symm.surjective
    exact Group.IsPerfect.commutator_eq_top
  · rw [← hψker]
    have h1 := Subgroup.card_ker_mul_card_of_surjective hψsurj
    have hCQ : Nat.card C = Nat.card (E ⧸ M) := Nat.card_congr eC.toEquiv
    have : Nat.card ψ.ker = Nat.card ψQ.ker := by
      refine Nat.eq_of_mul_eq_mul_right hJpos ?_
      rw [h1, hCQ, hQ]
    rw [this, hkerQcard]

private theorem kernel_eq_bot_of_cyclic_odd_sylow {E S : Type*} [Group E] [Finite E]
    [Group.IsPerfect E] [Group S] (π : E →* S) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hodd : Odd (Nat.card π.ker))
    (hcyc : ∀ r : ℕ, r.Prime → r ≠ 2 → ∀ [Fact r.Prime] (Q : Sylow r S),
      IsCyclic (Q : Subgroup S)) : π.ker = ⊥ := by
  have : Finite S := Finite.of_surjective π hπ
  by_contra hne
  have hnt : Nontrivial π.ker := (Subgroup.nontrivial_iff_ne_bot _).2 hne
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd (Finite.one_lt_card_iff_nontrivial.2 hnt).ne'
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by
    rintro rfl
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 hrd)
  obtain ⟨Cr⟩ := (inferInstance : Nonempty (Sylow r π.ker))
  obtain ⟨Q⟩ := (inferInstance : Nonempty (Sylow r S))
  exact Sylow.ne_bot_of_dvd_card Cr hrd
    (CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot π hπ hcen Cr Q
      (hcyc r hr hr2 Q))

private theorem kernel_eq_bot_psl2Even {p : ℕ} (hp : p.Prime) (hp3 : 3 ≤ p) {J : Type*} [Group J]
    (e : J ≃* PSL(2, GaloisField 2 p)) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* J) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 π.ker) : π.ker = ⊥ := by
  let e' : J ≃* SL(2, GaloisField 2 p) := e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  let π' : E →* SL(2, GaloisField 2 p) := e'.toMonoidHom.comp π
  have hker : π'.ker = π.ker := MonoidHom.ker_comp_of_injective π e'.toMonoidHom e'.injective
  rw [← hker]
  exact CFSG.ShultStronglyClosedTI.large_even_linear_central_two_cover_kernel_eq_bot p hp3
    (GaloisField.card 2 p hp.ne_zero) π' (e'.surjective.comp hπ) (by rw [hker]; exact hcen)
    (by rw [hker]; exact h2)

private theorem kernel_eq_bot_psu3 {p : ℕ} (hp : p.Prime) {J : Type*} [Group J]
    (e : J ≃* PSU3 2 p) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (π : E →* J) (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 π.ker) : π.ker = ⊥ := by
  let π' : E →* PSU3 2 p := e.toMonoidHom.comp π
  have hker : π'.ker = π.ker := MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective
  rw [← hker]
  exact CFSG.ShultStronglyClosedTI.unitaryCover_native_kernel_eq_bot p hp.two_le π'
    (e.surjective.comp hπ) (by rw [hker]; exact hcen) (by rw [hker]; exact h2)

private theorem lt_card_sz
    {n : ℕ} (hn : 2 ≤ n) : 29120 < Nat.card (Sz n) := by
  rw [NearSolvable.card_sz n]
  have hq : 32 ≤ 2 ^ (2 * n + 1) :=
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ (2 * n + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
  generalize 2 ^ (2 * n + 1) = q at hq ⊢
  have hs : 1024 ≤ q ^ 2 := by nlinarith
  have h1 : 1024 * 1 ≤ q ^ 2 * (q ^ 2 + 1) := Nat.mul_le_mul hs (by omega)
  have h2 : 1024 * 1 * 31 ≤ q ^ 2 * (q ^ 2 + 1) * (q - 1) := Nat.mul_le_mul h1 (by omega)
  exact lt_of_lt_of_le (by norm_num) h2

private theorem center_eq_bot_of_mulEquiv_sz {n : ℕ} (hn : 1 ≤ n) {J : Type*} [Group J]
    [Finite J] [Group.IsPerfect J] (e : J ≃* Sz n) : Subgroup.center J = ⊥ := by
  have hB : fusionIsBenderGroup J := Or.inr (Or.inr ⟨n, hn, ⟨e⟩⟩)
  have : IsSimpleGroup J :=
    CFSG.QuasithinUnique.RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  obtain ⟨a, b, hab⟩ := CFSG.QuasithinUnique.RankOneRecog.exists_noncommuting_of_perfect hB
  rcases Subgroup.Normal.eq_bot_or_eq_top (Subgroup.center J) with h | h
  · exact h
  · have hb : b ∈ Subgroup.center J := by
      rw [h]
      exact Subgroup.mem_top b
    exact absurd (Subgroup.mem_center_iff.mp hb a) hab

private theorem false_of_sz_two_kernel
    {n : ℕ} (hn : 2 ≤ n) {J : Type*} [Group J] [Finite J]
    (e : J ≃* Sz n) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 π.ker) (hne : π.ker ≠ ⊥) : False := by
  have : Group.IsPerfect J := Group.IsPerfect.ofSurjective hπ
  have hJc : Subgroup.center J = ⊥ := center_eq_bot_of_mulEquiv_sz (by omega) e
  obtain ⟨C, _, _, ψ, hperf, hψ, hker, hcard⟩ :=
    exists_perfect_cover_kernel_card_two hJc π hπ hcen h2 hne
  let eC : C ⧸ Subgroup.center C ≃* J :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hmodel : ∀ m : ℕ, CFSG.Theory.Comparator.SzModel m = Sz m := fun m => by
    simp only [Sz, SzGenerators, CFSG.Theory.Comparator.SzModel, CFSG.Theory.Comparator.SzGenerators]
  have hB : CFSG.BenderSuzuki.IsBenderGroup (C ⧸ Subgroup.center C) :=
    .isSuzuki n (by omega) (eC.trans (e.trans (MulEquiv.subgroupCongr (hmodel n).symm)))
  have hlt : 29120 < Nat.card (Sz n) := lt_card_sz hn
  have hcardJ : Nat.card (C ⧸ Subgroup.center C) = Nat.card (Sz n) :=
    Nat.card_congr (eC.trans e).toEquiv
  rcases CFSG.ProperTwoGeneratedCore.Lemma37.bender_cover_quotient hperf hcard hB with
    ⟨⟨e1⟩⟩ | ⟨⟨e1⟩⟩
  ·
    have h60 : Nat.card (CFSG.Theory.Comparator.PSL2Model 2) = 60 := by
      rw [NearSolvable.card_psl2_even (by norm_num)]
      norm_num
    rw [Nat.card_congr e1.toEquiv, h60] at hcardJ
    omega
  ·
    have h8 : Nat.card (CFSG.Theory.Comparator.SzModel 1) = 29120 := by
      rw [Nat.card_congr (MulEquiv.subgroupCongr (hmodel 1)).toEquiv, NearSolvable.card_sz 1]
      norm_num
    rw [Nat.card_congr e1.toEquiv, h8] at hcardJ
    omega

theorem schur_two_kernel
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {J : Type*} [Group J] [Finite J]
    (hJ : Nonempty (J ≃* PSL(2, GaloisField 2 p)) ∨
      (∃ n : ℕ, p = 2 * n + 1 ∧ Nonempty (J ≃* Sz n)) ∨ Nonempty (J ≃* PSU3 2 p))
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (h2 : IsPGroup 2 π.ker) (hne : π.ker ≠ ⊥) :
    p = 3 ∧ Nonempty (J ≃* Sz 1) := by
  have hp3 : 3 ≤ p := by
    have := hp.two_le
    omega
  rcases hJ with ⟨⟨e⟩⟩ | ⟨n, hpn, ⟨e⟩⟩ | ⟨⟨e⟩⟩
  · exact absurd (kernel_eq_bot_psl2Even hp hp3 e π hπ hcen h2) hne
  · have hn1 : n = 1 := by
      by_contra hn1
      exact false_of_sz_two_kernel (by omega) e π hπ hcen h2 hne
    subst hn1
    exact ⟨hpn, ⟨e⟩⟩
  · exact absurd (kernel_eq_bot_psu3 hp e π hπ hcen h2) hne

theorem schur_odd_psl2Even
    {p : ℕ} (_hp : p.Prime) (_hp2 : p ≠ 2) {J : Type*} [Group J] [Finite J]
    (hJ : Nonempty (J ≃* PSL(2, GaloisField 2 p)))
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  obtain ⟨e⟩ := hJ
  let e' : J ≃* SL(2, GaloisField 2 p) := e.trans CFSG.Walter.psl2MulEquivSL2OfCharTwo
  let π' : E →* SL(2, GaloisField 2 p) := e'.toMonoidHom.comp π
  have hker : π'.ker = π.ker := MonoidHom.ker_comp_of_injective π e'.toMonoidHom e'.injective
  have hπ' : Function.Surjective π' := e'.surjective.comp hπ
  have hcen' : π'.ker ≤ Subgroup.center E := by
    rw [hker]
    exact hcen
  have hodd' : ¬ 2 ∣ Nat.card π'.ker := by
    rw [hker]
    intro h
    exact (Nat.not_even_iff_odd.2 hodd) (even_iff_two_dvd.2 h)
  obtain ⟨σ, hσ, -⟩ :=
    CFSG.SectionRank.EvenCover.sl2_existsUnique_section (p := 2) hπ' hcen' hodd'
  have hsup : σ.range ⊔ Subgroup.center E = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hz : (σ (π' x))⁻¹ * x ∈ Subgroup.center E := by
      apply hcen'
      rw [MonoidHom.mem_ker, map_mul, map_inv, hσ, inv_mul_cancel]
    have hmem : σ (π' x) ∈ σ.range := ⟨π' x, rfl⟩
    have := Subgroup.mul_mem_sup hmem hz
    rwa [mul_inv_cancel_left] at this
  have hrange : σ.range = ⊤ :=
    (CFSG.SectionRank.perfect_central_supplement inferInstance).1 _ hsup
  rw [eq_bot_iff]
  intro x hx
  rw [← hker] at hx
  have hxr : x ∈ σ.range := by
    rw [hrange]
    exact Subgroup.mem_top x
  obtain ⟨g, rfl⟩ := hxr
  have hg : g = 1 := by
    rw [← hσ g]
    exact hx
  rw [hg, map_one]
  exact Subgroup.one_mem _

theorem schur_odd_sz
    {n : ℕ} (_hn : 0 < n) {J : Type*} [Group J] [Finite J]
    (hJ : Nonempty (J ≃* Sz n))
    {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] (π : E →* J)
    (hπ : Function.Surjective π) (hcen : π.ker ≤ Subgroup.center E)
    (hodd : Odd (Nat.card π.ker)) : π.ker = ⊥ := by
  obtain ⟨e⟩ := hJ
  let π' : E →* Sz n := e.toMonoidHom.comp π
  have hker : π'.ker = π.ker := MonoidHom.ker_comp_of_injective π e.toMonoidHom e.injective
  rw [← hker]
  exact kernel_eq_bot_of_cyclic_odd_sylow π' (e.surjective.comp hπ)
    (by rw [hker]; exact hcen) (by rw [hker]; exact hodd)
    fun r _ hr2 _ Q => CFSG.SignalizerFunctorTheorem.McBride.SzModel.sz_oddSylow_isCyclic hr2 Q

end CFSG.SignalizerFunctorTheorem.McBride
