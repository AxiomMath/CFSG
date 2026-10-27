module

public import CFSG.RankThree.Chevalley.G2CyclotomicTori
public import CFSG.LieType.Ree.SmallReeModelSchreier
public import CFSG.Walter.Ree.Model.PSL2
public import CFSG.LocalAnalysis.SectionRank.OddCover.PSL2
public import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
public import CFSG.LieType.Steinberg.CentralExt.PerfectCover

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.LieType.Ree.ReeTag
open Matrix (ProjectiveSpecialLinearGroup)
open scoped commutatorElement

theorem reeGamma_le_adjointGroup (t : ReeTag) {K : Type} [Field K] [Finite K] [CharP K t.prime]
    (a : ℕ) : t.reeGamma K a ≤ adjointGroup t.tag K :=
  Subgroup.map_subtype_le _

theorem sylow_isCyclic_of_injective {H G : Type*} [Group H] [Group G] [Finite G] {r : ℕ}
    [Fact r.Prime] (φ : H →* G) (hφ : Function.Injective φ) (hr : ¬ r ∣ φ.range.index)
    (hH : ∀ P : Sylow r H, IsCyclic P) (R : Sylow r G) : IsCyclic R := by
  have : Finite H := Finite.of_injective φ hφ
  obtain ⟨P₀⟩ : Nonempty (Sylow r H) := inferInstance
  have hS : IsPGroup r ((P₀ : Subgroup H).map φ) := P₀.isPGroup'.map φ
  have hSi : ¬ r ∣ ((P₀ : Subgroup H).map φ).index := by
    rw [Subgroup.index_map_of_injective _ hφ]
    exact fun h => ((Fact.out : r.Prime).dvd_mul.1 h).elim P₀.not_dvd_index hr
  have := hH P₀
  have hScyc : IsCyclic ((P₀ : Subgroup H).map φ) :=
    isCyclic_of_surjective (φ.subgroupMap _) (φ.subgroupMap_surjective _)
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G R (hS.toSylow hSi)
  have hRS : (R : Subgroup G).map (MulAut.conj g).toMonoidHom = (P₀ : Subgroup H).map φ := by
    have h := congrArg (fun T : Sylow r G => (T : Subgroup G)) hg
    simp only [Sylow.coe_subgroup_smul, IsPGroup.toSylow_coe] at h
    rw [← h, Subgroup.pointwise_smul_def]
    rfl
  let e := (Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective).trans
    (MulEquiv.subgroupCongr hRS)
  exact isCyclic_of_injective e.toMonoidHom e.injective

theorem small_Ree_sylow_isCyclic (a : ℕ) (K : Type) [Field K] [Finite K] [CharP K G2.prime]
    (hK : Nat.card K = 3 ^ (2 * a + 1)) {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (R : Sylow r (G2.reeGamma K a)) : IsCyclic R := by
  classical
  have : Fact r.Prime := ⟨hr⟩
  have hq3 : 3 ≤ 3 ^ (2 * a + 1) := Nat.le_self_pow (by omega) 3
  have hqq : 3 ^ (2 * a + 1) ≤ (3 ^ (2 * a + 1)) ^ 2 := Nat.le_self_pow (by norm_num) _
  by_cases hrd : r ∣ (3 ^ (2 * a + 1)) ^ 2 - 3 ^ (2 * a + 1) + 1
  ·
    have hd : (((3 ^ (2 * a + 1)) ^ 2 - 3 ^ (2 * a + 1) + 1 : ℕ) : ℤ) =
        (Nat.card K : ℤ) ^ 2 + (-1) * Nat.card K + 1 := by
      rw [hK]
      push_cast [Nat.cast_sub hqq]
      ring
    have hodd : Odd (Nat.card K) := by
      rw [hK]
      exact Odd.pow (by decide)
    obtain ⟨-, -, -, -, hcyc, -⟩ := odd_G2_cyclotomic_three_six_tori_and_prime_centralizers K hodd
      (-1) (Or.inl rfl) _ hd hr hr3 hrd
    let ι : G2.reeGamma K a →* adjointGroup G2.tag K :=
      Subgroup.inclusion (reeGamma_le_adjointGroup G2 a)
    have hP : IsCyclic ((R : Subgroup (G2.reeGamma K a)).map ι) := hcyc _ (R.isPGroup'.map ι)
    let e := Subgroup.equivMapOfInjective (R : Subgroup (G2.reeGamma K a)) ι
      (Subgroup.inclusion_injective _)
    exact isCyclic_of_injective e.toMonoidHom e.injective
  ·
    obtain ⟨w₀, hw₀, -⟩ := weyl_longest_element G2.tag
    obtain ⟨ψ, hψmem, -, -, -, -, -, -, ePSL, -⟩ :=
      CFSG.Walter.Ree.Model.small_Ree_involution_centralizer_PSL2_structure a K hK w₀ hw₀
    have hψle : ψ.range ≤ G2.reeGamma K a := by
      rintro _ ⟨g, rfl⟩
      exact (inf_le_left : CFSG.Walter.Ree.Model.smallReeInvCentralizer a K ≤
        G2.reeGamma K a) (hψmem g)
    let φ : ProjectiveSpecialLinearGroup (Fin 2) K →* G2.reeGamma K a :=
      (Subgroup.inclusion hψle).comp ePSL.toMonoidHom
    have hφ : Function.Injective φ := (Subgroup.inclusion_injective hψle).comp ePSL.injective
    obtain ⟨-, -, -, -, -, -, -, -, -, hcardΓ, -⟩ :=
      small_Ree_Borel_coset_Sylow_action a K hK w₀ hw₀
    have hPSL := CFSG.SectionRank.OddCover.card_psl_two (K := K) Nat.prime_three (by norm_num) hK
    have hcofac := (CFSG.SectionRank.OddCover.psl_two_cofactor Nat.prime_three (by norm_num)
      (by omega : 1 ≤ 2 * a + 1)).1
    have hrange : Nat.card φ.range = 3 ^ (2 * a + 1) * (((3 ^ (2 * a + 1)) ^ 2 - 1) / 2) := by
      rw [← hPSL]
      exact (Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv).symm
    have hidx : φ.range.index = 2 * (3 ^ (2 * a + 1)) ^ 2 *
        ((3 ^ (2 * a + 1)) ^ 2 - 3 ^ (2 * a + 1) + 1) := by
      have hmul := φ.range.card_mul_index
      rw [hrange, hcardΓ] at hmul
      have hm0 : 0 < 3 ^ (2 * a + 1) * (((3 ^ (2 * a + 1)) ^ 2 - 1) / 2) := by
        rw [← hPSL]
        exact Nat.card_pos
      refine Nat.eq_of_mul_eq_mul_left hm0 (hmul.trans ?_)
      have h1 : 1 ≤ 3 ^ (2 * a + 1) := by omega
      have h2 : 1 ≤ (3 ^ (2 * a + 1)) ^ 2 := Nat.one_le_pow _ _ (by omega)
      zify [h1, h2, hqq] at hcofac ⊢
      linear_combination (-(3 ^ (2 * a + 1) : ℤ) ^ 3 *
        (((3 ^ (2 * a + 1) : ℤ)) ^ 2 - 3 ^ (2 * a + 1) + 1)) * hcofac
    have hr2 : ¬ r ∣ 2 := fun h => by
      have := Nat.le_of_dvd (by norm_num) h
      omega
    have hrq : ¬ r ∣ 3 ^ (2 * a + 1) := fun h => by
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 (hr.dvd_of_dvd_pow h)
      omega
    have hri : ¬ r ∣ φ.range.index := by
      rw [hidx]
      intro h
      rcases hr.dvd_mul.1 h with h | h
      · rcases hr.dvd_mul.1 h with h | h
        · exact hr2 h
        · exact hrq (hr.dvd_of_dvd_pow h)
      · exact hrd h
    exact sylow_isCyclic_of_injective φ hφ hri
      (CFSG.SectionRank.OddCover.psl_two_sylow_isCyclic Nat.prime_three (by norm_num) hK
        (by omega) (by omega)) R

theorem small_Ree_central_extension_split (a : ℕ) (ha : 1 ≤ a) (K : Type) [Field K] [Finite K]
    [CharP K G2.prime] (hK : Nat.card K = 3 ^ (2 * a + 1)) {E : Type*} [Group E] [Finite E]
    (π : E →* G2.reeGamma K a) (hπ : Function.Surjective π)
    (hcen : π.ker ≤ Subgroup.center E) (hcop : Nat.Coprime (Nat.card π.ker) 6) :
    ∃ s : G2.reeGamma K a →* E, π.comp s = MonoidHom.id _ ∧
      (∀ t : G2.reeGamma K a →* E, π.comp t = MonoidHom.id _ → t = s) ∧
      commutator E = s.range ∧
      ∃ e : π.ker × s.range ≃* E, ∀ c x, e (c, x) = (c : E) * x := by
  classical
  have hperf : Group.IsPerfect (G2.reeGamma K a) :=
    ⟨(ree_generic_fixed_group_perfect G2 a ha K hK).2.1⟩
  obtain ⟨-, hDperf, hDsurj⟩ :=
    CFSG.LocalCores.central_extension_derived_of_surjective π hπ hcen hperf
  have : Group.IsPerfect (commutator E) := hDperf
  set f := π.comp (commutator E).subtype with hf
  have hfcen : f.ker ≤ Subgroup.center (commutator E) := by
    intro x hx
    have hx' : (x : E) ∈ π.ker := hx
    exact Subgroup.mem_center_iff.2 fun y =>
      Subtype.ext (Subgroup.mem_center_iff.1 (hcen hx') y)
  have hfker : f.ker = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    by_contra hx1
    rw [Subgroup.mem_bot] at hx1
    have hne : (⟨x, hx⟩ : f.ker) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
    obtain ⟨r, hr, hrdvd⟩ := Nat.exists_prime_and_dvd
      (Finite.one_lt_card_iff_nontrivial.2 ⟨⟨_, _, hne⟩⟩).ne'
    have : Fact r.Prime := ⟨hr⟩
    obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' r hrdvd
    have hdvdC : Nat.card f.ker ∣ Nat.card π.ker :=
      Subgroup.card_dvd_of_injective
        (MonoidHom.codRestrict ((commutator E).subtype.comp f.ker.subtype) π.ker
          fun z => z.2) fun z z' h =>
        Subtype.ext (Subtype.ext (congrArg (Subtype.val : π.ker → E) h))
    have hr6 : ¬ r ∣ 6 := fun h6 => hr.one_lt.ne'
      (Nat.eq_one_of_dvd_coprimes hcop (hrdvd.trans hdvdC) h6)
    have hr3 : 3 < r := by
      have h2 : r ≠ 2 := fun h => hr6 (h ▸ by norm_num)
      have h3 : r ≠ 3 := fun h => hr6 (h ▸ by norm_num)
      have := hr.two_le
      omega
    obtain ⟨Q⟩ : Nonempty (Sylow r (G2.reeGamma K a)) := inferInstance
    have hyp : IsPGroup r (Subgroup.zpowers y) := IsPGroup.of_card (n := 1)
      (by rw [Nat.card_zpowers, hy, pow_one])
    obtain ⟨C, hC⟩ := hyp.exists_le_sylow
    have hCbot := CFSG.ShultStronglyClosedTI.central_cover_cyclic_sylow_kernel_eq_bot f hDsurj
      hfcen C Q (small_Ree_sylow_isCyclic a K hK hr hr3 Q)
    have hy1 : y = 1 := by
      have := hC (Subgroup.mem_zpowers y)
      rw [hCbot, Subgroup.mem_bot] at this
      exact this
    rw [hy1, orderOf_one] at hy
    exact hr.one_lt.ne hy
  have hfinj : Function.Injective f := (MonoidHom.ker_eq_bot_iff f).1 hfker
  let eD : commutator E ≃* G2.reeGamma K a := MulEquiv.ofBijective f ⟨hfinj, hDsurj⟩
  let s : G2.reeGamma K a →* E := (commutator E).subtype.comp eD.symm.toMonoidHom
  have hsg : ∀ g, π (s g) = g := fun g => eD.apply_symm_apply g
  have hs : π.comp s = MonoidHom.id _ := MonoidHom.ext hsg
  refine ⟨s, hs, fun t ht => ?_, ?_, ?_⟩
  ·
    have htg : ∀ g, π (t g) = g := fun g => DFunLike.congr_fun ht g
    have hcen' : ∀ g, t g * (s g)⁻¹ ∈ Subgroup.center E := fun g => hcen (by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hsg, htg, mul_inv_cancel])
    refine MonoidHom.eq_of_eqOn_dense (s := commutatorSet (G2.reeGamma K a)) ?_ ?_
    · rw [← commutator_eq_closure]
      exact hperf.commutator_eq_top
    · rintro _ ⟨x, y, rfl⟩
      rw [map_commutatorElement, map_commutatorElement]
      have hx : t x = t x * (s x)⁻¹ * s x := by group
      have hy : t y = t y * (s y)⁻¹ * s y := by group
      rw [hx, hy, CFSG.LieType.Steinberg.commutatorElement_mul_mul_of_mem_center (hcen' x)
        (hcen' y)]
  ·
    change commutator E = ((commutator E).subtype.comp eD.symm.toMonoidHom).range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 eD.symm.surjective,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
  ·
    let μ : π.ker × s.range →* E := MonoidHom.noncommCoprod π.ker.subtype s.range.subtype
      fun c x => (Subgroup.mem_center_iff.1 (hcen c.2) x).symm
    have hμ : ∀ c x, μ (c, x) = (c : E) * x := fun c x => rfl
    have hμbij : Function.Bijective μ := by
      constructor
      · rintro ⟨c, x⟩ ⟨c', x'⟩ h
        rw [hμ, hμ] at h
        obtain ⟨g, hg⟩ := MonoidHom.mem_range.1 x.2
        obtain ⟨g', hg'⟩ := MonoidHom.mem_range.1 x'.2
        have hgg : g = g' := by
          have h' := congrArg π h
          rwa [map_mul, map_mul, (MonoidHom.mem_ker).1 c.2, (MonoidHom.mem_ker).1 c'.2, one_mul,
            one_mul, ← hg, ← hg', hsg, hsg] at h'
        have hxx : x = x' := Subtype.ext (by rw [← hg, ← hg', hgg])
        subst hxx
        exact Prod.ext (Subtype.ext (mul_right_cancel h)) rfl
      · intro y
        refine ⟨(⟨y * (s (π y))⁻¹, ?_⟩, ⟨s (π y), π y, rfl⟩), ?_⟩
        · rw [MonoidHom.mem_ker, map_mul, map_inv, hsg, mul_inv_cancel]
        · rw [hμ]
          exact inv_mul_cancel_right y _
    exact ⟨MulEquiv.ofBijective μ hμbij, hμ⟩

theorem small_Ree_model_central_kernel_trivial (S : Type) [Group S] (ℓ e : ℕ)
    (h : ReeTitsModel S .twistedG2 ℓ e) {E : Type*} [Group E] [Finite E] [Group.IsPerfect E]
    (η : E →* S) (hη : Function.Surjective η) (hcen : η.ker ≤ Subgroup.center E)
    (hcop : Nat.Coprime (Nat.card η.ker) 6) : η.ker = ⊥ := by
  obtain ⟨-, -, rfl, ⟨b, hb, heb⟩, hiso⟩ := small_Ree_model_Schreier S ℓ e h
  obtain ⟨-, b', heb', K, _, _, hK, hw⟩ := h
  have hb' : 1 ≤ b' := by omega
  have : Fintype K := Fintype.ofFinite K
  have : CharP K G2.prime := charP_of_card_eq_prime_pow (f := e) (by
    rw [← Nat.card_eq_fintype_card, hK]
    rfl)
  obtain ⟨φ⟩ := hiso b' K heb' hK hw
  have hK' : Nat.card K = 3 ^ (2 * b' + 1) := by rw [hK, heb']
  let π : E →* G2.reeGamma K b' := φ.toMonoidHom.comp η
  have hπ : Function.Surjective π := φ.surjective.comp hη
  have hker : π.ker = η.ker := by
    ext x
    simp only [MonoidHom.mem_ker, π, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff]
  obtain ⟨s, hs, -, hcomm, -⟩ := small_Ree_central_extension_split b' hb' K hK' π hπ
    (hker ▸ hcen) (hker ▸ hcop)
  rw [← hker, eq_bot_iff]
  intro x hx
  have hxs : x ∈ s.range := by
    rw [← hcomm, Group.IsPerfect.commutator_eq_top]
    exact Subgroup.mem_top x
  obtain ⟨g, rfl⟩ := hxs
  have hg : g = 1 := by
    have h1 : π (s g) = g := DFunLike.congr_fun hs g
    rw [← h1]
    exact hx
  rw [hg, map_one]
  exact one_mem _

end CFSG.RankThree.Chevalley
