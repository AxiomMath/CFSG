module

public import CFSG.Quasithin.H13.U3ModelsExclude
public import CFSG.Quasithin.H13.NQTermCommonSylow
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.RankThree.PGroups.SolvableFittingSelfCentralizing
public import CFSG.LocalAnalysis.ComponentInitial.TwoPrimeSolvable
public import CFSG.LocalAnalysis.QuasithinUnique.RankOneModels

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13.NQTerm
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type*} [Group G]

theorem isCyclic_of_le_of_odd [Finite G] {T D B Y : Subgroup G} (hT : IsPGroup 2 T)
    (hTB : T ≤ B) (hTn : (T.subgroupOf B).Normal) (hD : IsCyclic D) (hTD : T ⊔ D = B)
    (hYB : Y ≤ B) (hY : Odd (Nat.card Y)) : IsCyclic Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hDB : D ≤ B := hTD ▸ le_sup_right
  set T' := T.subgroupOf B
  set D' := D.subgroupOf B
  have hD'c : IsCyclic D' := isCyclic_of_surjective (subgroupOfEquivOfLe hDB).symm.toMonoidHom
    (subgroupOfEquivOfLe hDB).symm.surjective
  have htop : T' ⊔ D' = ⊤ := by
    rw [← subgroupOf_sup hTB hDB, hTD, subgroupOf_self]
  have hmap : D'.map (QuotientGroup.mk' T') = ⊤ := by
    have h1 : (T' ⊔ D').map (QuotientGroup.mk' T') = ⊤ := by
      rw [htop, map_top_of_surjective _ (QuotientGroup.mk'_surjective T')]
    rwa [Subgroup.map_sup, (map_eq_bot_iff T').2 (QuotientGroup.ker_mk' T').ge, bot_sup_eq] at h1
  have hsurj : Function.Surjective ((QuotientGroup.mk' T').comp D'.subtype) := by
    intro y
    obtain ⟨d, hd, rfl⟩ := mem_map.1 (hmap ▸ mem_top y)
    exact ⟨⟨d, hd⟩, rfl⟩
  have : IsCyclic (↥B ⧸ T') := isCyclic_of_surjective _ hsurj
  have hYT : Y ⊓ T = ⊥ := by
    obtain ⟨m, hm⟩ := hT.exists_card_eq
    refine disjoint_iff.mp (disjoint_of_coprime_natCard ?_)
    rw [hm]
    exact (Nat.coprime_two_right.2 hY).pow_right m
  set Y' := Y.subgroupOf B
  have hinj : Function.Injective ((QuotientGroup.mk' T').comp Y'.subtype) := by
    rw [injective_iff_map_eq_one]
    intro y hy
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hy
    have hmem : ((y : B) : G) ∈ Y ⊓ T := ⟨y.2, hy⟩
    rw [hYT, mem_bot] at hmem
    exact Subtype.ext (Subtype.ext hmem)
  have : IsCyclic Y' := isCyclic_of_injective _ hinj
  exact isCyclic_of_surjective (subgroupOfEquivOfLe hYB).toMonoidHom
    (subgroupOfEquivOfLe hYB).surjective

theorem centralizer_singleton_le_normalizer_zpowers (a : G) :
    centralizer ({a} : Set G) ≤ normalizer ((zpowers a : Subgroup G) : Set G) := by
  intro c hc
  have hca : c * a = a * c := mem_centralizer_singleton_iff.1 hc
  have hcomm : Commute c a := hca
  rw [mem_normalizer_iff]
  intro x
  have key : ∀ n : ℤ, c * a ^ n * c⁻¹ = a ^ n := fun n => by
    rw [(hcomm.zpow_right n).eq, mul_inv_cancel_right]
  constructor
  · rintro ⟨n, rfl⟩
    exact ⟨n, (key n).symm⟩
  · rintro ⟨n, hn⟩
    refine ⟨n, ?_⟩
    have h1 : c * x * c⁻¹ = c * a ^ n * c⁻¹ := by
      rw [key n]
      exact hn.symm
    simpa using h1.symm

theorem odd_card_fittingSubgroup_of_pCore_eq_bot {H : Type*} [Group H] [Finite H]
    (h : CFSG.pCore 2 H = ⊥) : Odd (Nat.card (CFSG.fittingSubgroup H)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P⟩ : Nonempty (Sylow 2 (CFSG.fittingSubgroup H)) := inferInstance
  have hle := Sylow.map_le_pCore (fittingSubgroup_normal (G := H))
    (fittingSubgroup_nilpotent (G := H)) 2 P
  rw [h, le_bot_iff, map_eq_bot_iff_of_injective _ (subtype_injective _)] at hle
  have hcard := P.card_eq_multiplicity
  rw [hle, card_bot] at hcard
  have hv : (Nat.card (CFSG.fittingSubgroup H)).factorization 2 = 0 := by
    by_contra hv
    have : 2 ≤ 2 ^ (Nat.card (CFSG.fittingSubgroup H)).factorization 2 :=
      Nat.le_self_pow hv 2
    omega
  rw [Nat.factorization_eq_zero_iff] at hv
  rcases hv with h2 | h2 | h2
  · exact absurd Nat.prime_two h2
  · exact Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 h2)
  · exact absurd h2 Nat.card_pos.ne'

theorem le_normalizer_of_isSolvable_of_fusionBenderBorel [Finite G] {q k : ℕ}
    (hB : fusionBenderBorel G q k) (hq : 4 ≤ q) (T : Sylow 2 G) {M : Subgroup G}
    (hTM : (T : Subgroup G) ≤ M) (hM : Group.IsSolvable M) :
    M ≤ normalizer ((T : Subgroup G) : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSE, ⟨D, hDc, -, -, hTDB⟩, hZ2, hZq, -⟩ := hB T
  set B := normalizer ((T : Subgroup G) : Set G) with hBdef
  have hTB : (T : Subgroup G) ≤ B := le_normalizer
  have hloc : ∀ Q : Subgroup G, IsPGroup 2 Q → Q ≠ ⊥ → Q ≤ T → ∀ E : Subgroup G,
      E ≤ normalizer (Q : Set G) → E ≤ B := fun Q hQ hQ1 hQT E hE =>
    U3.le_of_fusionStronglyEmbedded hSE hQ hQ1 (hQT.trans hTB) hE
  have hcyc : ∀ Y : Subgroup G, Y ≤ B → Odd (Nat.card Y) → IsCyclic Y := fun Y hYB hY =>
    isCyclic_of_le_of_odd T.isPGroup' hTB normal_in_normalizer hDc hTDB hYB hY
  let TM : Sylow 2 M := T.subtype hTM
  have hTM' : (TM : Subgroup M) = (T : Subgroup G).subgroupOf M := T.coe_subtype hTM
  have hnorm : ∀ K : Subgroup M, K.Normal → M ≤ normalizer ((K.map M.subtype : Subgroup G) :
      Set G) := fun K hK => by
    rw [← normal_subgroupOf_iff_le_normalizer (map_subtype_le K),
      ← comap_subtype, comap_map_eq_self_of_injective M.subtype_injective]
    exact hK
  by_cases hO2 : CFSG.pCore 2 M = ⊥
  swap
  ·
    have : (CFSG.pCore 2 M).Normal := CFSG.pCore_normal
    refine hloc _ ((CFSG.pCore_isPGroup (p := 2) (G := M)).map M.subtype)
      (fun h => hO2 ((map_eq_bot_iff_of_injective _ M.subtype_injective).1 h)) ?_ M
      (hnorm _ CFSG.pCore_normal)
    rintro _ ⟨x, hx, rfl⟩
    have hxT := IsPGroup.le_sylow_of_normal (CFSG.pCore_isPGroup (p := 2) (G := M)) TM hx
    rw [hTM'] at hxT
    exact hxT
  set F := CFSG.fittingSubgroup M
  set X := F.map M.subtype with hXdef
  have hFodd : Odd (Nat.card F) := odd_card_fittingSubgroup_of_pCore_eq_bot hO2
  have hXodd : Odd (Nat.card X) := by
    rwa [hXdef, card_map_of_injective M.subtype_injective]
  have hMX : M ≤ normalizer (X : Set G) := hnorm F fittingSubgroup_normal
  set A := (center (T : Subgroup G)).map (T : Subgroup G).subtype with hAdef
  have hAT : A ≤ T := map_subtype_le _
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨x', hx', rfl⟩ _ ⟨y', hy', rfl⟩
    simp only [Subgroup.coe_subtype]
    exact congrArg Subtype.val (mem_center_iff.1 hx' y').symm
  have hAel : IsElemAbelian 2 A := by
    refine ⟨⟨⟨fun x y => Subtype.ext (hAcomm x x.2 y y.2)⟩⟩, ?_⟩
    rintro _ ⟨x', hx', rfl⟩
    simp only [Subgroup.coe_subtype]
    rw [← Subgroup.coe_pow, hZ2 x' hx', Subgroup.coe_one]
  have hAcard : 2 ^ 2 ≤ Nat.card A := by
    rw [hAdef, card_map_of_injective (subtype_injective _), hZq]
    omega
  have hgen := SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two hAel
    hAcard ((hAT.trans hTM).trans hMX) (Nat.coprime_two_left.2 hXodd)
  have hXB : X ≤ B := by
    rw [← hgen]
    refine iSup_le fun a => iSup_le fun ha => iSup_le fun ha1 => ?_
    refine inf_le_right.trans (hloc (zpowers a) ?_ ?_ ((zpowers_le.2 ha).trans hAT) _ ?_)
    · refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, pow_one]
      have ha2 : a ^ 2 = 1 := hAel.2 a ha
      exact orderOf_eq_prime ha2 ha1
    · intro h
      exact ha1 ((zpowers_eq_bot).1 h)
    · exact centralizer_singleton_le_normalizer_zpowers a
  have hXc : IsCyclic X := hcyc X hXB hXodd
  have hFc : IsCyclic F := isCyclic_of_surjective (F.equivMapOfInjective M.subtype
    M.subtype_injective).symm.toMonoidHom (MulEquiv.surjective _)
  have hcomm : ∀ m₁ m₂ : M, ⁅m₁, m₂⁆ ∈ F := by
    intro m₁ m₂
    apply RankThree.PGroups.solvable_fitting_self_centralizing M
    rw [mem_centralizer_iff]
    intro x hx
    let φ := MulAut.conjNormal (H := F) (G := M)
    have hab : ∀ α β : MulAut F, α * β = β * α := fun α β => by
      apply (IsCyclic.mulAutMulEquiv (G := F)).injective
      rw [map_mul, map_mul, mul_comm]
    have h1 : φ ⁅m₁, m₂⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hab _ _
    have h2 := congrArg (fun α : MulAut F => ((α ⟨x, hx⟩ : F) : M)) h1
    simp only [φ, MulAut.conjNormal_apply, MulAut.one_apply] at h2
    calc x * ⁅m₁, m₂⁆ = ⁅m₁, m₂⁆ * (⁅m₁, m₂⁆⁻¹ * x * ⁅m₁, m₂⁆) := by group
      _ = ⁅m₁, m₂⁆ * x := by
        congr 1
        have h3 : ⁅m₁, m₂⁆ * x * ⁅m₁, m₂⁆⁻¹ = x := h2
        calc ⁅m₁, m₂⁆⁻¹ * x * ⁅m₁, m₂⁆ = ⁅m₁, m₂⁆⁻¹ * (⁅m₁, m₂⁆ * x * ⁅m₁, m₂⁆⁻¹) *
              ⁅m₁, m₂⁆ := by rw [h3]
          _ = x := by group
  set N := (TM : Subgroup M) ⊔ F with hNdef
  have hN : N.Normal := by
    constructor
    intro n hn g
    have : g * n * g⁻¹ = ⁅g, n⁆ * n := by group
    rw [this]
    exact N.mul_mem (le_sup_right (a := (TM : Subgroup M)) (hcomm g n)) hn
  have hfr := Sylow.normalizer_sup_eq_top' TM (le_sup_left : (TM : Subgroup M) ≤ N)
  intro m hm
  have hmtop : (⟨m, hm⟩ : M) ∈ (⊤ : Subgroup M) := mem_top _
  rw [← hfr] at hmtop
  have hBM : normalizer ((TM : Subgroup M) : Set M) ⊔ N ≤ B.subgroupOf M := by
    refine sup_le ?_ (sup_le ?_ ?_)
    · intro y hy
      rw [mem_subgroupOf, mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        have hxM : x ∈ M := hTM hx
        have h := (mem_normalizer_iff.1 hy ⟨x, hxM⟩).1 (by rw [hTM']; exact hx)
        rw [hTM'] at h
        exact h
      · intro hx
        have hyx : (y : G) * x * (y : G)⁻¹ ∈ M := hTM hx
        have hxM : x ∈ M := by
          have := M.mul_mem (M.mul_mem (M.inv_mem y.2) hyx) y.2
          simpa [mul_assoc] using this
        have h := (mem_normalizer_iff.1 hy ⟨x, hxM⟩).2 (by rw [hTM']; exact hx)
        rw [hTM'] at h
        exact h
    · intro y hy
      rw [hTM'] at hy
      exact hTB hy
    · intro y hy
      exact hXB ⟨y, hy, rfl⟩
  exact hBM hmtop

theorem isCyclic_of_isPGroup_of_not_sq_dvd [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) (h : ¬ p ^ 2 ∣ Nat.card G) : IsCyclic P := by
  obtain ⟨n, hn⟩ := hP.exists_card_eq
  have hdvd : p ^ n ∣ Nat.card G := hn ▸ card_subgroup_dvd_card P
  rcases (show n = 0 ∨ n = 1 ∨ 2 ≤ n by omega) with rfl | rfl | h2
  · rw [pow_zero] at hn
    have : Subsingleton P := by
      rw [← Finite.card_le_one_iff_subsingleton, hn]
    infer_instance
  · exact isCyclic_of_prime_card (hn.trans (pow_one p))
  · exact absurd ((pow_dvd_pow p h2).trans hdvd) h

theorem eq_of_sq_dvd_two_three {p a b q : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) (hq : q.Prime)
    (h : p ^ 2 ∣ 2 ^ a * 3 ^ b * q) : p = q := by
  have hpd : p ∣ 2 ^ a * 3 ^ b * q := (dvd_pow_self p two_ne_zero).trans h
  rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
  · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
      omega
    · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
      omega
  · exact (Nat.prime_dvd_prime_iff_eq hp hq).1 h1


theorem exact_uniqueness_models_have_cyclic_large_prime_sylow_products
    (G : Type) [Group G]
    [Finite G] [IsSimpleGroup G] (_hnonab : ∃ a b : G, a * b ≠ b * a)
    (hG : fusionIsBenderGroup G ∨ UniqueSmallModel G) (T : Sylow 2 G) {p : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (P : Subgroup G) (hP : IsPGroup p P)
    (hPT : (P : Set G) * (T : Set G) = (T : Set G) * (P : Set G)) : IsCyclic P := by
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hG with hB | hS
  ·
    obtain ⟨q, k, hq, hBB⟩ : ∃ q k : ℕ, 4 ≤ q ∧ fusionBenderBorel G q k := by
      rcases hB with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
      · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv G e.toEquiv
        exact ⟨2 ^ f, 1, four_le_two_pow hf,
          (bender_psl2_borel_full f hf).map_mulEquiv e.symm⟩
      · have : Finite (PSU3 2 f) := Finite.of_equiv G e.toEquiv
        exact ⟨2 ^ f, 3, four_le_two_pow hf,
          (bender_psu3_borel_full f hf).map_mulEquiv e.symm⟩
      · have : Finite (Sz a) := Finite.of_equiv G e.toEquiv
        exact ⟨2 ^ (2 * a + 1), 2, four_le_two_pow (by omega),
          (bender_suzuki_borel_full a ha).map_mulEquiv e.symm⟩
    set M := permProd P T hPT
    have hMsolv : Group.IsSolvable M := by
      obtain ⟨d, hdP, hcard⟩ := card_permProd P T hPT
      obtain ⟨m, hm⟩ := T.isPGroup'.exists_card_eq
      obtain ⟨n, hn⟩ := hP.exists_card_eq
      rw [hn] at hdP
      obtain ⟨j, -, rfl⟩ := (Nat.dvd_prime_pow hp).1 hdP
      apply LocalAnalysis.ComponentInitial.isSolvable_of_card_primeFactors_le_two
      rw [hcard, hm]
      have hsub : (2 ^ m * p ^ j).primeFactors ⊆ {2, p} := by
        intro r hr
        obtain ⟨hrp, hrd, -⟩ := Nat.mem_primeFactors.1 hr
        rcases (Nat.Prime.dvd_mul hrp).1 hrd with h | h
        · simp [(Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).1 (hrp.dvd_of_dvd_pow h)]
        · simp [(Nat.prime_dvd_prime_iff_eq hrp hp).1 (hrp.dvd_of_dvd_pow h)]
      exact (Finset.card_le_card hsub).trans ((Finset.card_insert_le _ _).trans (by simp))
    have hMB := le_normalizer_of_isSolvable_of_fusionBenderBorel hBB hq T
      (le_permProd_right P T hPT) hMsolv
    obtain ⟨-, ⟨D, hDc, -, -, hTDB⟩, -⟩ := hBB T
    obtain ⟨n, hn⟩ := hP.exists_card_eq
    exact isCyclic_of_le_of_odd T.isPGroup' le_normalizer normal_in_normalizer hDc hTDB
      ((le_permProd_left P T hPT).trans hMB)
      (by rw [hn]; exact (hp.odd_of_ne_two (by omega)).pow)
  · rcases hS with ⟨p', hp', hp'7, -, ⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
    ·
      have : Fact p'.Prime := ⟨hp'⟩
      have hp'odd : Odd p' := hp'.odd_of_ne_two (by omega)
      have hdata := CFSG.Semidihedral.OddProjectiveCoverKernel.odd_projective_linear_two_Sylow_data
        (ZMod p') hp' hp'odd le_rfl (by rw [Nat.card_zmod, pow_one])
      let φ : G ≃* CFSG.Semidihedral.OddProjectiveCoverKernel.S (ZMod p') :=
        e.trans (CFSG.Semidihedral.ProjectiveSL2Cover.scalarProjectiveEquivNative (ZMod p') 2).symm
      obtain ⟨R, hR⟩ := (hP.map φ.toMonoidHom).exists_le_sylow
      have hRc :
          IsCyclic (R : Subgroup (CFSG.Semidihedral.OddProjectiveCoverKernel.S (ZMod p'))) := by
        by_cases hpp : p = p'
        · subst hpp
          obtain ⟨-, -, -, hUcard, ⟨R₀, hR₀⟩, -⟩ := hdata
          have hcardR : Nat.card R = p := by
            rw [Sylow.card_eq_multiplicity R, ← Sylow.card_eq_multiplicity R₀, hR₀, hUcard,
              pow_one]
          exact isCyclic_of_prime_card hcardR
        · exact hdata.2.2.2.2.2.2 p hp (hp.odd_of_ne_two (by omega)) hpp R
      have : IsCyclic (P.map φ.toMonoidHom) := Subgroup.isCyclic_of_le hR
      exact isCyclic_of_injective (P.equivMapOfInjective φ.toMonoidHom φ.injective).toMonoidHom
        (P.equivMapOfInjective φ.toMonoidHom φ.injective).injective
    ·
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hSL : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) =
          3 ^ (3 * (3 - 1) / 2) * ∏ j ∈ Finset.Icc 2 3, (3 ^ j - 1) :=
        (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.linear_order (K := ZMod 3) 3 3
          (Nat.card_zmod 3) (by norm_num)).2.1
      have hSL' : Nat.card (Matrix.SpecialLinearGroup (Fin 3) (ZMod 3)) = 2 ^ 4 * 3 ^ 3 * 13 := by
        rw [hSL]
        decide
      have hdvd : Nat.card G ∣ 2 ^ 4 * 3 ^ 3 * 13 := by
        rw [Nat.card_congr e.toEquiv, ← hSL']
        exact Subgroup.card_quotient_dvd_card _
      refine isCyclic_of_isPGroup_of_not_sq_dvd hP fun h => ?_
      have h13 := eq_of_sq_dvd_two_three hp hp5 (by norm_num) (h.trans hdvd)
      subst h13
      have := h.trans hdvd
      norm_num at this
    ·
      have hM : Nat.card G = 7920 := by
        rw [Nat.card_congr e.toEquiv,
          ← Nat.card_congr CFSG.Adapters.RankTwoModelTransports.statedM11EquivM11.toEquiv]
        exact CFSG.Semidihedral.GL2Recognition.card_statedM11
      refine isCyclic_of_isPGroup_of_not_sq_dvd hP fun h => ?_
      rw [hM, show (7920 : ℕ) = 2 ^ 4 * 3 ^ 2 * 55 by norm_num] at h
      have hp55 : p ∣ 55 := by
        have hpd : p ∣ 2 ^ 4 * 3 ^ 2 * 55 := (dvd_pow_self p two_ne_zero).trans h
        rcases (Nat.Prime.dvd_mul hp).1 hpd with h1 | h1
        · rcases (Nat.Prime.dvd_mul hp).1 h1 with h2 | h2
          · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h2)
            omega
          · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h2)
            omega
        · exact h1
      have hp' : p = 5 ∨ p = 11 := by
        rw [show (55 : ℕ) = 5 * 11 by norm_num] at hp55
        rcases (Nat.Prime.dvd_mul hp).1 hp55 with h1 | h1
        · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)
        · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 h1)
      rcases hp' with rfl | rfl <;> norm_num at h

end CFSG.Quasithin.H13.NQCat
