module

public import CFSG.LocalAnalysis.UniquenessCase.Lie.BorelSL
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow
public import CFSG.ClassicalGroups.UnitaryFlag.OrderSylow
public import CFSG.ClassicalGroups.UnitaryFlag.ModelTransport
public import CFSG.LieType.Steinberg.CentralExt.PSUMultiplier
public import CFSG.LieType.Steinberg.CentralExt.SUOddClosed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial Subgroup

section Torus

variable {p f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData p f K) {r ε : ℕ}

@[expose] noncomputable def uc22pwliu_ratio (μ : Subgroup Kˣ) (r ε : ℕ) : ((Fin r → μ) × (Fin ε → μ)) →* μ :=
  (((powMonoidHom 2).comp (uc22pwlie_prodHom μ r)).comp (MonoidHom.fst _ _)) *
    ((uc22pwlie_prodHom μ ε).comp (MonoidHom.snd _ _))

theorem uc22pwliu_ratio_apply (μ : Subgroup Kˣ) (r ε : ℕ) (x : (Fin r → μ) × (Fin ε → μ)) :
    uc22pwliu_ratio μ r ε x = (∏ i, x.1 i) ^ 2 * ∏ k, x.2 k := rfl

@[expose] def UC22pwliuInv (μ : Subgroup Kˣ) : Prop :=
  ∀ a : μ, h.bar (((a : Kˣ) : K)) = (((a : Kˣ)⁻¹ : Kˣ) : K)

@[expose] def uc22pwliu_a (μ : Subgroup Kˣ) (x : (Fin r → μ) × (Fin ε → μ)) : Fin r → Kˣ :=
  fun i => ((x.1 i : μ) : Kˣ)

@[expose] def uc22pwliu_d (μ : Subgroup Kˣ) (x : (Fin r → μ) × (Fin ε → μ)) : Fin ε → Kˣ :=
  fun k => ((x.2 k : μ) : Kˣ)

variable {h}

theorem uc22pwliu_norm_one {μ : Subgroup Kˣ} (hμ : UC22pwliuInv h μ) (a : μ) :
    h.norm (((a : Kˣ)) : K) = 1 := by
  rw [UnitaryFieldData.norm, hμ a, ← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem uc22pwliu_torusRatio {μ : Subgroup Kˣ} (hμ : UC22pwliuInv h μ) (x : (Fin r → μ) × (Fin ε → μ)) :
    torusRatio h (uc22pwliu_a μ x) (uc22pwliu_d μ x) =
      (((uc22pwliu_ratio μ r ε x : μ) : Kˣ) : K) := by
  have hψ : ∀ y : μ, (((y : Kˣ)) : K) = ((Units.coeHom K).comp μ.subtype) y := fun y => rfl
  rw [uc22pwliu_ratio_apply, hψ, map_mul, map_pow, map_prod, map_prod, torusRatio]
  have h1 : ∀ i, ((uc22pwliu_a μ x i : Kˣ) : K) / h.bar ((uc22pwliu_a μ x i : Kˣ) : K) =
      ((Units.coeHom K).comp μ.subtype) (x.1 i) * ((Units.coeHom K).comp μ.subtype) (x.1 i) := by
    intro i
    rw [uc22pwliu_a, hμ (x.1 i), Units.val_inv_eq_inv_val, div_inv_eq_mul]
    rfl
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_mul_distrib, sq]
  rfl

variable {μ : Subgroup Kˣ} {r ε : ℕ}

noncomputable def uc22pwliu_elt (hμ : UC22pwliuInv h μ) (x : (uc22pwliu_ratio μ r ε).ker) :
    hypSU h r ε :=
  (torusMat_mem_hypSU h (uc22pwliu_a μ x.1) (d := uc22pwliu_d μ x.1)
    (fun k => uc22pwliu_norm_one hμ (x.1.2 k))
    (by rw [uc22pwliu_torusRatio hμ, MonoidHom.mem_ker.1 x.2]; simp)).choose

theorem uc22pwliu_elt_spec (hμ : UC22pwliuInv h μ) (x : (uc22pwliu_ratio μ r ε).ker) :
    uc22pwliu_elt hμ x ∈ hypTorus h r ε ∧
      ((uc22pwliu_elt hμ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
        Matrix.diagonal (torusEntries h (uc22pwliu_a μ x.1) (uc22pwliu_d μ x.1)) :=
  (torusMat_mem_hypSU h (uc22pwliu_a μ x.1) (d := uc22pwliu_d μ x.1)
    (fun k => uc22pwliu_norm_one hμ (x.1.2 k))
    (by rw [uc22pwliu_torusRatio hμ, MonoidHom.mem_ker.1 x.2]; simp)).choose_spec

noncomputable def uc22pwliu_hom (hμ : UC22pwliuInv h μ) :
    (uc22pwliu_ratio μ r ε).ker →* hypSU h r ε where
  toFun := uc22pwliu_elt hμ
  map_one' := by
    apply Subtype.ext
    apply Units.ext
    rw [(uc22pwliu_elt_spec hμ 1).2]
    change _ = (1 : Matrix (HypIndex r ε) (HypIndex r ε) K)
    rw [← Matrix.diagonal_one]
    congr 1
    funext y
    rcases y with i | k | i <;> simp [torusEntries, uc22pwliu_a, uc22pwliu_d]
  map_mul' x y := by
    apply Subtype.ext
    apply Units.ext
    rw [Subgroup.coe_mul, Units.val_mul, (uc22pwliu_elt_spec hμ x).2, (uc22pwliu_elt_spec hμ y).2,
      (uc22pwliu_elt_spec hμ (x * y)).2, Matrix.diagonal_mul_diagonal]
    congr 1
    funext z
    rcases z with i | k | i <;> simp [torusEntries, uc22pwliu_a, uc22pwliu_d, mul_inv] <;> ring

theorem uc22pwliu_hom_mem_borel (hμ : UC22pwliuInv h μ) (x : (uc22pwliu_ratio μ r ε).ker) :
    uc22pwliu_hom hμ x ∈ hypBorel h r ε :=
  hypTorus_le_hypBorel h (uc22pwliu_elt_spec hμ x).1

theorem uc22pwliu_ker_pow {ℓ : ℕ} (hexp : ∀ a : μ, a ^ ℓ = 1) (x : (uc22pwliu_ratio μ r ε).ker) :
    x ^ ℓ = 1 :=
  Subtype.ext (Prod.ext (funext fun i => hexp _) (funext fun k => hexp _))

theorem uc22pwliu_ratio_surjective {ℓ : ℕ} (hodd : Odd ℓ) (hcard : Nat.card μ = ℓ) (hrε : 1 ≤ r + ε) :
    Function.Surjective (uc22pwliu_ratio μ r ε) := by
  intro z
  rcases Nat.eq_zero_or_pos ε with hε | hε
  · subst hε
    have hr : 1 ≤ r := by omega
    obtain ⟨t, ht⟩ := hodd
    have hz : z ^ ℓ = 1 := by rw [← hcard]; exact pow_card_eq_one'
    refine ⟨(Pi.mulSingle ⟨0, hr⟩ (z ^ (t + 1)), fun k => k.elim0), ?_⟩
    rw [uc22pwliu_ratio_apply]
    have h1 : ∏ i, (Pi.mulSingle (⟨0, hr⟩ : Fin r) (z ^ (t + 1)) : Fin r → μ) i = z ^ (t + 1) := by
      rw [Finset.prod_eq_single (⟨0, hr⟩ : Fin r)]
      · simp
      · intro b _ hb
        simp [Pi.mulSingle_eq_of_ne hb]
      · simp
    have h2 : ∏ k : Fin 0, ((fun k => k.elim0 : Fin 0 → μ) k) = 1 := Fin.prod_univ_zero _
    rw [h1, h2, mul_one, ← pow_mul]
    calc z ^ ((t + 1) * 2) = z ^ (2 * t + 1) * z := by rw [← pow_succ]; congr 1; ring
      _ = z := by rw [← ht, hz, one_mul]
  · refine ⟨(1, Pi.mulSingle ⟨0, hε⟩ z), ?_⟩
    rw [uc22pwliu_ratio_apply]
    have h1 : ∏ k, (Pi.mulSingle (⟨0, hε⟩ : Fin ε) z : Fin ε → μ) k = z := by
      rw [Finset.prod_eq_single (⟨0, hε⟩ : Fin ε)]
      · simp
      · intro b _ hb
        simp [Pi.mulSingle_eq_of_ne hb]
      · simp
    simp [h1]

theorem uc22pwliu_card_ker_ratio {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ) (hcard : Nat.card μ = ℓ)
    (hrε : 1 ≤ r + ε) : Nat.card (uc22pwliu_ratio μ r ε).ker = ℓ ^ (r + ε - 1) := by
  have h1 := Subgroup.card_ker_mul_card_of_surjective (uc22pwliu_ratio_surjective hodd hcard hrε)
  rw [hcard] at h1
  have h2 : Nat.card ((Fin r → μ) × (Fin ε → μ)) = ℓ ^ r * ℓ ^ ε := by
    simp [Nat.card_prod, Nat.card_fun, hcard]
  rw [h2, ← pow_add] at h1
  have h3 : ℓ ^ (r + ε) = ℓ ^ (r + ε - 1) * ℓ := by
    rw [← pow_succ]
    congr 1
    omega
  rw [h3] at h1
  exact Nat.eq_of_mul_eq_mul_right hℓ.pos h1

theorem uc22pwliu_params_const (hμ : UC22pwliuInv h μ) (x : (uc22pwliu_ratio μ r ε).ker) (c : Kˣ)
    (hc : (uc22pwliu_hom hμ x : GL (HypIndex r ε) K) = Matrix.GeneralLinearGroup.scalar (HypIndex r ε) c) :
    (∀ i, ((x.1.1 i : μ) : Kˣ) = c) ∧ ∀ k, ((x.1.2 k : μ) : Kˣ) = c := by
  have hmat : ((uc22pwliu_hom hμ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      Matrix.diagonal (torusEntries h (uc22pwliu_a μ x.1) (uc22pwliu_d μ x.1)) :=
    (uc22pwliu_elt_spec hμ x).2
  have hc' : ((uc22pwliu_hom hμ x : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
      Matrix.scalar (HypIndex r ε) (c : K) := by
    have := congrArg (fun g : GL (HypIndex r ε) K => (g : Matrix (HypIndex r ε) (HypIndex r ε) K)) hc
    simpa [Matrix.GeneralLinearGroup.coe_scalar] using this
  have hdiag : ∀ y : HypIndex r ε, torusEntries h (uc22pwliu_a μ x.1) (uc22pwliu_d μ x.1) y = (c : K) := by
    intro y
    have := congr_fun (congr_fun (hmat.symm.trans hc') y) y
    simpa [Matrix.scalar_apply] using this
  exact ⟨fun i => Units.ext (by simpa [torusEntries, uc22pwliu_a] using hdiag (Sum.inl i)),
    fun k => Units.ext (by simpa [torusEntries, uc22pwliu_d] using hdiag (Sum.inr (Sum.inl k)))⟩

theorem uc22pwliu_eq_one_of_scalar (hμ : UC22pwliuInv h μ) {ℓ : ℕ} (hℓ : ℓ.Prime)
    (hexp : ∀ a : μ, a ^ ℓ = 1) (hr : 1 ≤ r) (hnd : ¬ ℓ ∣ 2 * r + ε) (x : (uc22pwliu_ratio μ r ε).ker)
    (hx : uc22pwliu_hom hμ x ∈ hypScalars h r ε) : x = 1 := by
  obtain ⟨c, -, hcm, hc⟩ := mem_normOneScalars.1 hx
  obtain ⟨hai, hdk⟩ := uc22pwliu_params_const hμ x c hc
  have hcℓ : c ^ ℓ = 1 := by
    have := congrArg (fun a : μ => ((a : Kˣ))) (hexp (x.1.1 ⟨0, hr⟩))
    simpa [hai] using this
  have hc1 : c = 1 := by
    have h1 : orderOf c ∣ ℓ := orderOf_dvd_of_pow_eq_one hcℓ
    rcases (Nat.dvd_prime hℓ).1 h1 with h2 | h2
    · exact orderOf_eq_one_iff.1 h2
    · exact absurd (h2 ▸ orderOf_dvd_of_pow_eq_one hcm) hnd
  refine Subtype.ext (Prod.ext (funext fun i => ?_) (funext fun k => ?_))
  · exact Subtype.ext (by rw [hai i, hc1]; rfl)
  · exact Subtype.ext (by rw [hdk k, hc1]; rfl)

theorem uc22pwliu_eq_one_of_hom_eq_one (hμ : UC22pwliuInv h μ) (x : (uc22pwliu_ratio μ r ε).ker)
    (hx : uc22pwliu_hom hμ x = 1) : x = 1 := by
  obtain ⟨hai, hdk⟩ := uc22pwliu_params_const hμ x 1 (by rw [hx, map_one]; rfl)
  refine Subtype.ext (Prod.ext (funext fun i => ?_) (funext fun k => ?_))
  · exact Subtype.ext (hai i)
  · exact Subtype.ext (hdk k)

theorem uc22pwliu_borelWit_core {f : ℕ} (h : UnitaryFieldData 2 f K) {μ : Subgroup Kˣ}
    (hμ : UC22pwliuInv h μ) {ℓ : ℕ} (hℓ : ℓ.Prime) (hodd : Odd ℓ) (hcard : Nat.card μ = ℓ)
    (hexp : ∀ a : μ, a ^ ℓ = 1) {r ε : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1) {X : Type} [Group X] [Finite X]
    (α : hypSU h r ε →* X) (hα : Function.Surjective α)
    (hinj : ∀ x : (uc22pwliu_ratio μ r ε).ker, α (uc22pwliu_hom hμ x) = 1 → x = 1) :
    uc22p20oBorelWit X ℓ (r + ε - 1) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hφ : Function.Injective (α.comp (uc22pwliu_hom hμ)) :=
    (injective_iff_map_eq_one _).2 fun x hx => hinj x hx
  have hE : IsElemAbelian ℓ (α.comp (uc22pwliu_hom hμ)).range :=
    uc22pwlie_range_isElemAbelian _ fun x => uc22pwliu_ker_pow hexp x
  have hc : Nat.card (α.comp (uc22pwliu_hom hμ)).range = ℓ ^ (r + ε - 1) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact uc22pwliu_card_ker_ratio hℓ hodd hcard (by omega)
  obtain ⟨-, ⟨Q, hQ⟩, -⟩ := unitary_order_and_Sylow h hr hε
  obtain ⟨P₀, hP₀⟩ : ∃ P₀ : Sylow 2 X, (P₀ : Subgroup X) = (hypUnitriangular h r ε).map α :=
    ⟨Q.mapSurjective hα, by rw [Sylow.coe_mapSurjective, hQ]⟩
  have hN : (α.comp (uc22pwliu_hom hμ)).range ≤ normalizer (P₀ : Set X) := by
    have h2 : normalizer (P₀ : Set X) = normalizer (((hypUnitriangular h r ε).map α : Subgroup X) : Set X) := by
      rw [← hP₀]
      rfl
    rw [h2]
    rintro _ ⟨x, rfl⟩
    have hB : uc22pwliu_hom hμ x ∈ normalizer (hypUnitriangular h r ε : Set (hypSU h r ε)) := by
      rw [(UnitaryHigher.unitary_Sylow_normalizers h hr hε).1]
      exact uc22pwliu_hom_mem_borel hμ x
    exact Subgroup.le_normalizer_map α ⟨_, hB, rfl⟩
  exact uc22pwlie_borelWit_of_sylow P₀ _ hN hE hc

end Torus

section Bridge

open CFSG.Blueprint (LieModel)

theorem uc22pwliu_exists_hypPSU {Y : Type} [Group Y] {n r ε : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ 2 * r + ε)
    (hL : LieModel Y .PSU (2 * r + ε) 2 n) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (h : UnitaryFieldData 2 n K), Nonempty (Y ≃* hypPSU h r ε) := by
  obtain ⟨K, _, _, hcard, ⟨e₀⟩⟩ : ∃ (K : Type) (_ : Field K) (_ : Finite K),
      Nat.card K = (2 ^ n) ^ 2 ∧
        Nonempty (Y ≃* Assembly.LowTwoRank.StatedProj
          (Assembly.LowTwoRank.StatedSU (2 * r + ε) (2 ^ n) K)) := by
    rcases hL with ⟨-, hc⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩ | ⟨-, ht, -⟩
    · exact hc.2
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
    · exact absurd ht (by decide)
  have h : UnitaryFieldData 2 n K := ⟨Nat.prime_two, hn, by rw [hcard, ← pow_mul, mul_comm]⟩
  obtain ⟨R₀, hR₀⟩ := exists_isHypTransport (r := r) (ε := ε) h
  exact ⟨K, inferInstance, inferInstance, h, ⟨e₀.trans (hypPSUEquivStatedProj h hR₀ hm).symm⟩⟩

theorem uc22pwliu_closed
    {f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 f K)
    {r ε : ℕ} (hε : ε ≤ 1) (hm : 3 ≤ 2 * r + ε) (hf : 2 ≤ f) {E : Type} [Group E] [Finite E]
    (π : E →* hypSU h r ε) (hπ : Function.Surjective π) (hc : π.ker ≤ center E) :
    ∃ s : hypSU h r ε →* E, ∀ g, π (s g) = g := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := h.charP
  obtain ⟨R, hR⟩ := exists_isHypTransport (r := r) (ε := ε) h
  let Φ : hypSU h r ε ≃* Assembly.LowTwoRank.StatedSU (2 * r + ε) (2 ^ f) K := hypTransport h hR
  have hπ' : Function.Surjective (Φ.toMonoidHom.comp π) := Φ.surjective.comp hπ
  have hker : (Φ.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      map_eq_one_iff _ Φ.injective]
  have hq : 4 ≤ 2 ^ f := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hcard := UnitaryFieldData.card_eq_sq h
  obtain ⟨s, hs⟩ : ∃ s : Assembly.LowTwoRank.StatedSU (2 * r + ε) (2 ^ f) K →* E,
      ∀ g, Φ.toMonoidHom.comp π (s g) = g := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.1 hε with rfl | rfl
    · exact CFSG.LieType.Steinberg.CentralExt.SUClosed.statedSU_exists_section_of_central hcard
        ⟨r, by ring⟩ (by omega) hq hπ' (hker ▸ hc)
    · exact CFSG.LieType.Steinberg.CentralExt.SUOdd.statedSU_odd_exists_section_of_central hcard
        (by omega) (by omega) (by simp) (fun hh => by
          have := congrArg Prod.snd hh
          simp at this
          omega) hπ' (hker ▸ hc)
  refine ⟨s.comp Φ.toMonoidHom, fun g => Φ.injective ?_⟩
  have := hs (Φ g)
  simpa using this

theorem uc22pwliu_exists_cover
    {f : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 f K)
    {r ε : ℕ} (hε : ε ≤ 1) (hm : 3 ≤ 2 * r + ε) (hf : 2 ≤ f) {X : Type} [Group X] [Finite X]
    (hq : CFSG.Open.IsQuasisimple X) (e : X ⧸ center X ≃* hypPSU h r ε) :
    ∃ α : hypSU h r ε →* X, Function.Surjective α ∧ (∀ s, α s = 1 → s ∈ hypScalars h r ε) ∧
      ∀ s, (QuotientGroup.mk (α s) : X ⧸ center X) = e.symm (hypProj h r ε s) := by
  have hρc : (e.symm.toMonoidHom.comp (hypProj h r ε)).ker ≤ center (hypSU h r ε) := by
    intro s hs
    have h1 : hypProj h r ε s = 1 := by
      have : e.symm (hypProj h r ε s) = 1 := hs
      simpa using this
    have h2 : s ∈ hypScalars h r ε := by
      rw [← ker_hypProj]
      exact h1
    exact normOneScalars_le_center h _ _ h2
  obtain ⟨α, hα, -, hαπ⟩ := uc22pwlie_exists_cover_of_closed_fin
    (fun E _ _ π hπ hc => uc22pwliu_closed h hε hm hf π hπ hc)
    hq.1 (QuotientGroup.mk' (center X)) (QuotientGroup.mk'_surjective _)
    (by rw [QuotientGroup.ker_mk']) (e.symm.toMonoidHom.comp (hypProj h r ε))
    (e.symm.surjective.comp (hypProj_surjective h r ε)) hρc
  refine ⟨α, hα, fun s hs => ?_, hαπ⟩
  have h1 : e.symm (hypProj h r ε s) = 1 := by
    have := hαπ s
    rw [hs] at this
    simpa using this.symm
  rw [← ker_hypProj]
  simpa using h1

end Bridge

section Main

open CFSG.Blueprint (LieModel)

theorem uc22pwliu_odd_of_dvd {n ℓ : ℕ} (hn : 1 ≤ n) (hℓ : ℓ.Prime) (h : ℓ ∣ 2 ^ n + 1) : Odd ℓ :=
  hℓ.eq_two_or_odd'.resolve_left (uc22p20v_ne_two_of_dvd_add_one hn hℓ h)

theorem uc22pwliu_exists_mu {n : ℕ} {K : Type} [Field K] [Finite K] (h : UnitaryFieldData 2 n K) {ℓ : ℕ}
    (hℓ : ℓ.Prime) (hℓq : ℓ ∣ 2 ^ n + 1) :
    ∃ μ : Subgroup Kˣ, Nat.card μ = ℓ ∧ (∀ a : μ, a ^ ℓ = 1) ∧ UC22pwliuInv h μ := by
  have hdvd : ℓ ∣ Nat.card K - 1 := by
    have h1 := Nat.sq_sub_sq (2 ^ n) 1
    rw [one_pow] at h1
    rw [UnitaryFieldData.card_eq_sq h, h1]
    exact Dvd.dvd.mul_right hℓq _
  obtain ⟨ζ, hζ⟩ := uc22pwlie_exists_zeta hℓ hdvd
  have hcard : Nat.card (Subgroup.zpowers ζ) = ℓ := by rw [Nat.card_zpowers, hζ]
  have hexp : ∀ a : Subgroup.zpowers ζ, a ^ ℓ = 1 := fun a => by
    have h1 : orderOf a ∣ Nat.card (Subgroup.zpowers ζ) := orderOf_dvd_natCard a
    rw [hcard] at h1
    exact orderOf_dvd_iff_pow_eq_one.1 h1
  refine ⟨Subgroup.zpowers ζ, hcard, hexp, fun a => ?_⟩
  have h1 : ((a : Kˣ)) ^ (2 ^ n + 1) = 1 := by
    obtain ⟨t, ht⟩ := hℓq
    have h2 : (a : Kˣ) ^ ℓ = 1 := by simpa using congrArg (fun y : Subgroup.zpowers ζ => (y : Kˣ)) (hexp a)
    rw [ht, pow_mul, h2, one_pow]
  have h2 : (((a : Kˣ)) : K) ^ (2 ^ n + 1) = 1 := by
    simpa using congrArg (fun y : Kˣ => (y : K)) h1
  rw [UnitaryFieldData.bar_apply, Units.val_inv_eq_inv_val]
  rw [pow_succ] at h2
  exact eq_inv_of_mul_eq_one_left h2

theorem uc22pwliu_two_pow_mod_seven (n : ℕ) : 2 ^ n % 7 = 1 ∨ 2 ^ n % 7 = 2 ∨ 2 ^ n % 7 = 4 := by
  induction n with
  | zero => simp
  | succ k ih =>
    rw [pow_succ]
    generalize 2 ^ k = N at *
    omega

theorem uc22pwliu_not_dvd {n m ℓ : ℕ} (hn : 1 ≤ n) (hℓ : ℓ.Prime) (hℓn : ℓ ∣ 2 ^ n + 1) (hne5 : ℓ ≠ 5)
    (hev : Even n) (hm : m = 5 ∨ m = 6 ∨ m = 7) : ¬ ℓ ∣ m := by
  intro hdvd
  have h2 : ℓ ≠ 2 := uc22p20v_ne_two_of_dvd_add_one hn hℓ hℓn
  have h3 : ℓ ≠ 3 := fun h => uc22p20v_not_three_dvd_add_one hev (h ▸ hℓn)
  have h7 : ℓ ≠ 7 := fun h => by
    have h8 := uc22pwliu_two_pow_mod_seven n
    have h7' : 7 ∣ 2 ^ n + 1 := h ▸ hℓn
    omega
  rcases hm with rfl | rfl | rfl
  · exact hne5 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 hdvd)
  · rcases (Nat.Prime.dvd_mul hℓ).1 (by simpa using hdvd : ℓ ∣ 2 * 3) with h | h
    · exact h2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h)
    · exact h3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h)
  · exact h7 ((Nat.prime_dvd_prime_iff_eq hℓ (by norm_num)).1 hdvd)

theorem uc22pwliu_borelWit_of_lieModel
    {X : Type} [Group X] [Finite X] (hq : CFSG.Open.IsQuasisimple X)
    {r ε n : ℕ} (hr : 1 ≤ r) (hε : ε ≤ 1) (hm : 3 ≤ 2 * r + ε) (hn : 2 ≤ n)
    (hL : LieModel (X ⧸ center X) .PSU (2 * r + ε) 2 n) {ℓ : ℕ} (hℓ : ℓ.Prime) (hℓq : ℓ ∣ 2 ^ n + 1)
    (hℓm : ¬ ℓ ∣ 2 * r + ε) : uc22p20oBorelWit X ℓ (r + ε - 1) := by
  obtain ⟨K, _, _, h, ⟨e⟩⟩ := uc22pwliu_exists_hypPSU (by omega) (by omega) hL
  obtain ⟨α, hα, hker, -⟩ := uc22pwliu_exists_cover h hε hm hn hq e
  obtain ⟨μ, hcard, hexp, hμ⟩ := uc22pwliu_exists_mu h hℓ hℓq
  exact uc22pwliu_borelWit_core h hμ hℓ (uc22pwliu_odd_of_dvd (by omega) hℓ hℓq) hcard hexp hr hε α hα
    fun x hx => uc22pwliu_eq_one_of_scalar hμ hℓ hexp hr hℓm x (hker _ hx)

theorem uc22pwliu_unitary_holds :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Odd (Nat.card (center K)) →
    ∀ m n : ℕ, (m = 5 ∨ m = 6 ∨ m = 7) → 2 < n → Even n → LieModel (K ⧸ center K) .PSU m 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 → p ≠ 5 → uc22p20oBorelWit K p 2 := by
  intro K _ _ hq _ m n hm hn hev h p hp hpq hp5
  have hnd := uc22pwliu_not_dvd (by omega) hp hpq hp5 hev hm
  rcases hm with rfl | rfl | rfl
  · exact uc22p20v_borelWit_mono hp (uc22pwliu_borelWit_of_lieModel (r := 2) (ε := 1) hq (by omega)
      le_rfl (by norm_num) (by omega) h hp hpq hnd) (by norm_num)
  · exact uc22p20v_borelWit_mono hp (uc22pwliu_borelWit_of_lieModel (r := 3) (ε := 0) hq (by omega)
      (by omega) (by norm_num) (by omega) h hp hpq hnd) (by norm_num)
  · exact uc22p20v_borelWit_mono hp (uc22pwliu_borelWit_of_lieModel (r := 3) (ε := 1) hq (by omega)
      le_rfl (by norm_num) (by omega) h hp hpq hnd) (by norm_num)

theorem uc22pwliu_unitary3_holds :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Odd (Nat.card (center K)) →
    ∀ n : ℕ, 2 < n → LieModel (K ⧸ center K) .PSU 3 2 n →
      ∀ p : ℕ, p.Prime → p ∣ 2 ^ n + 1 → p ≠ 3 → uc22p20oBorelWit K p 1 := by
  intro K _ _ hq _ n hn h p hp hpq hp3
  have hnd : ¬ p ∣ 2 * 1 + 1 := fun hd => hp3 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hd)
  exact uc22pwliu_borelWit_of_lieModel (r := 1) (ε := 1) hq le_rfl le_rfl (by norm_num) (by omega) h hp hpq hnd

theorem uc22pwliu_u54_holds :
    ∀ (K : Type) [Group K] [Finite K], CFSG.Open.IsQuasisimple K →
    Odd (Nat.card (center K)) → center K ≠ ⊥ → LieModel (K ⧸ center K) .PSU 5 2 2 →
      uc22p20oBorelWit K 5 2 := by
  intro K _ _ hq _ hc hL
  obtain ⟨F, _, _, h, ⟨e⟩⟩ := uc22pwliu_exists_hypPSU (r := 2) (ε := 1) (n := 2) (by norm_num) (by norm_num) hL
  obtain ⟨α, hα, hker, hαπ⟩ := uc22pwliu_exists_cover h (r := 2) (ε := 1) le_rfl (by norm_num) le_rfl hq e
  obtain ⟨μ, hcard, hexp, hμ⟩ := uc22pwliu_exists_mu h (ℓ := 5) (by norm_num) (by norm_num)
  have hZ : Nat.card (hypScalars h 2 1) = 5 := by
    rw [card_hypScalars h (by norm_num)]
    norm_num
  have hle : α.ker ≤ hypScalars h 2 1 := fun s hs => hker s hs
  have hbot : α.ker = ⊥ := by
    by_contra hne
    apply hc
    have hcardN : Nat.card α.ker = 5 := by
      have hd : Nat.card α.ker ∣ 5 := hZ ▸ Subgroup.card_dvd_of_le hle
      rcases (Nat.dvd_prime (by norm_num)).1 hd with h1 | h5
      · exact absurd (Subgroup.card_eq_one.1 h1) hne
      · exact h5
    have hEq : α.ker = hypScalars h 2 1 := Subgroup.eq_of_le_of_card_ge hle (by rw [hcardN, hZ])
    rw [eq_bot_iff]
    intro z hz
    obtain ⟨s, rfl⟩ := hα z
    have h1 : (QuotientGroup.mk (α s) : K ⧸ center K) = 1 := (QuotientGroup.eq_one_iff _).2 hz
    rw [hαπ s] at h1
    have h2 : hypProj h 2 1 s = 1 := by simpa using h1
    have h3 : s ∈ hypScalars h 2 1 := by
      rw [← ker_hypProj]
      exact h2
    rw [← hEq] at h3
    exact (MonoidHom.mem_ker.1 h3 : α s = 1) ▸ Subgroup.one_mem _
  exact uc22pwliu_borelWit_core h hμ (by norm_num) (by decide) hcard hexp (r := 2) (ε := 1) (by norm_num) le_rfl α hα
    fun x hx => uc22pwliu_eq_one_of_hom_eq_one hμ x (by
      have : uc22pwliu_hom hμ x ∈ α.ker := hx
      rw [hbot] at this
      exact this)

end Main

end CFSG.LocalAnalysis.UniquenessCase.UC22
