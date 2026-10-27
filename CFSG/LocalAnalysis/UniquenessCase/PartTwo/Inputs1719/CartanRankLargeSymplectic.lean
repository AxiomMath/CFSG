module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusInverters
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotSetup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CartanCoverTools
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsC

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
open CFSG.QuasithinUnique (IsSylowTwoOf)
open TauCeti.Subgroup (normalizerQuotient)

private noncomputable def symplecticSplitSet (F : Type) [Field F] (n : ℕ) (s : Finset (Fin n))
    (ζ : Fˣ) : Set (StatedSp n F) :=
  Set.range fun i : {i : Fin n // i ∈ s} => lam (i : Fin n) (sl2Diag ζ)

private theorem symplecticSplitSet_closure {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) (hn4 : 4 ≤ n) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {ζ : Fˣ}
    (hζo : orderOf ζ = r) {s : Finset (Fin n)} (hs : s.card = 4) :
    Nat.card (Subgroup.closure (symplecticSplitSet F n s ζ)) = r ^ 4 ∧
      (∀ y ∈ Subgroup.closure (symplecticSplitSet F n s ζ), y ^ r = 1) ∧
      Subgroup.closure (symplecticSplitSet F n s ζ) ≤
        Subgroup.normalizer (unipotent n F : Set (StatedSp n F)) := by
  have hζ : ζ ^ r = 1 := by rw [← hζo, pow_orderOf_eq_one]
  let H : Subgroup (Fin n → Fˣ) := Subgroup.pi Set.univ (fun i : Fin n =>
    (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup Fˣ))
  have hH : H = Subgroup.closure (Set.range fun i : {i : Fin n // i ∈ s} =>
      Pi.mulSingle (i : Fin n) ζ) := by
    rw [show H = Subgroup.pi Set.univ (fun i : Fin n =>
        (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup Fˣ)) from rfl,
      pi_ite_zpowers_eq_closure]
  have hDmap : Subgroup.closure (symplecticSplitSet F n s ζ) =
      H.map (torusHom (r := n) (k := F)) := by
    rw [hH, MonoidHom.map_closure]
    show Subgroup.closure (Set.range fun i : {i : Fin n // i ∈ s} =>
        lam (i : Fin n) (sl2Diag ζ)) =
      Subgroup.closure (torusHom '' Set.range fun i : {i : Fin n // i ∈ s} =>
        Pi.mulSingle (i : Fin n) ζ)
    congr 1
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨_, ⟨i, rfl⟩, (lam_sl2Diag (i : Fin n) ζ).symm⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, lam_sl2Diag (i : Fin n) ζ⟩
  have hcard : Nat.card (Subgroup.closure (symplecticSplitSet F n s ζ)) = r ^ 4 := by
    rw [hDmap, Subgroup.card_map_of_injective torusHom_injective,
      show H = Subgroup.pi Set.univ (fun i : Fin n =>
        (if i ∈ s then Subgroup.zpowers ζ else ⊥ : Subgroup Fˣ)) from rfl,
      card_pi_ite_zpowers, hζo, hs]
  have hexp : ∀ y ∈ Subgroup.closure (symplecticSplitSet F n s ζ), y ^ r = 1 := by
    intro y hy
    rw [hDmap] at hy
    exact pow_eq_one_of_mem_map_pi_ite_zpowers (m := n) hζo hy
  have hDtorus : Subgroup.closure (symplecticSplitSet F n s ζ) ≤ torus n F := by
    intro y hy
    rw [hDmap] at hy
    obtain ⟨t, -, rfl⟩ := Subgroup.mem_map.mp hy
    exact ⟨t, rfl⟩
  have hDnormalizer : Subgroup.closure (symplecticSplitSet F n s ζ) ≤
      Subgroup.normalizer (unipotent n F : Set (StatedSp n F)) := by
    refine hDtorus.trans ?_
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.normalizer_unipotent]
    exact torus_le_borelSubgroup
  exact ⟨hcard, hexp, hDnormalizer⟩

private theorem symplecticSplitSet_inversion {F : Type} [Field F] [Finite F] [CharP F 2]
    (n : ℕ) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) {ζ : Fˣ} (hζo : orderOf ζ = r)
    {s : Finset (Fin n)} :
    (∀ a ∈ symplecticSplitSet F n s ζ, ∀ b ∈ symplecticSplitSet F n s ζ, Commute a b) ∧
      (∀ a ∈ symplecticSplitSet F n s ζ, Odd (orderOf a)) ∧
      (∀ a ∈ symplecticSplitSet F n s ζ, ∀ b ∈ symplecticSplitSet F n s ζ, a ≠ b →
        (∃ c : StatedSp n F, c * a * c⁻¹ = a⁻¹ ∧ c * b * c⁻¹ = b) ∨
          (∃ c : StatedSp n F, c * b * c⁻¹ = b⁻¹ ∧ c * a * c⁻¹ = a)) := by
  have hζ : ζ ^ r = 1 := by rw [← hζo, pow_orderOf_eq_one]
  have hS_comm : ∀ a ∈ symplecticSplitSet F n s ζ, ∀ b ∈ symplecticSplitSet F n s ζ,
      Commute a b := by
    rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩
    by_cases hij : (i : Fin n) = (j : Fin n)
    · have hsub : i = j := Subtype.ext hij
      subst hsub
      exact Commute.refl _
    · exact commute_lam_lam hij (sl2Diag ζ) (sl2Diag ζ)
  have hS_odd : ∀ a ∈ symplecticSplitSet F n s ζ, Odd (orderOf a) := by
    rintro a ⟨i, rfl⟩
    rw [orderOf_lam_sl2Diag, hζo]
    exact hr.odd_of_ne_two hr2
  have hinv : ∀ a ∈ symplecticSplitSet F n s ζ, ∀ b ∈ symplecticSplitSet F n s ζ, a ≠ b →
      (∃ c : StatedSp n F, c * a * c⁻¹ = a⁻¹ ∧ c * b * c⁻¹ = b) ∨
        (∃ c : StatedSp n F, c * b * c⁻¹ = b⁻¹ ∧ c * a * c⁻¹ = a) := by
    rintro a ⟨i, rfl⟩ b ⟨j, rfl⟩ hab
    have hij : (i : Fin n) ≠ (j : Fin n) := by
      rintro h
      exact hab (by rw [Subtype.ext h])
    refine Or.inl ⟨lam (i : Fin n) sl2W, lam_sl2W_conj_lam_sl2Diag (i : Fin n) ζ, ?_⟩
    have hc : Commute (lam (i : Fin n) sl2W) (lam (j : Fin n) (sl2Diag ζ)) :=
      commute_lam_lam hij sl2W (sl2Diag ζ)
    rw [hc.eq, mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨hS_comm, hS_odd, hinv⟩

theorem k_CartanRankLarge_psp :
    ∀ (K : Type) [Group K] [Finite K] (n f : ℕ),
      CFSG.Open.StatedLieAdmissible .PSp n 2 f → 2 < 2 ^ f →
      CFSG.Blueprint.LieModel (K ⧸ Subgroup.center K) .PSp n 2 f →
      CFSG.Open.IsQuasisimple K → Odd (Nat.card (Subgroup.center K)) →
      ∀ S : Subgroup K, CFSG.QuasithinUnique.IsSylowTwoOf S ⊤ →
        4 ≤ CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank .PSp n →
          ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ∣ 2 ^ f - 1 ∧
            3 < CFSG.Open.pRank r (⊤ : Subgroup (normalizerQuotient S)) := by
  intro K _ _ n f hAdm hq2 hK _ _ S hS hrank
  obtain ⟨F, hF, hFin, hChar, hFcard, ⟨e⟩⟩ :=
    CFSG.SeitzReduction.SymplecticPilot.exists_mulEquiv_statedSp_of_lieModel
      (L := K ⧸ Subgroup.center K) hK
  letI := hF
  letI := hFin
  letI := hChar
  have hn4 : 4 ≤ n := by
    simpa [CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.CS17LieRank] using hrank
  have hf2 : 2 ≤ f := by
    by_contra hf
    interval_cases f <;> norm_num at hq2
  obtain ⟨r, hr, hr2, -, hrdvd⟩ :=
    CFSG.RankThree.PartOne.KFU.exists_odd_prime_dvd_two_pow_sub_one_ne_five hf2
  have hrdvd' : r ∣ Nat.card F - 1 := by rw [hFcard]; exact hrdvd
  haveI : Fact r.Prime := ⟨hr⟩
  obtain ⟨ζ, hζo⟩ := exists_prime_orderOf_dvd_card' (G := Fˣ) r (by rwa [Nat.card_units])
  let e4 : Fin 4 → Fin n := Fin.castLE hn4
  let s : Finset (Fin n) := Finset.univ.image e4
  have hscard : s.card = 4 := by
    rw [show s = Finset.univ.image e4 from rfl,
      Finset.card_image_of_injective _ (Fin.castLE_injective hn4)]
    simp
  let D : Subgroup (StatedSp n F) := Subgroup.closure (symplecticSplitSet F n s ζ)
  obtain ⟨hDcard, hDexp, hDnormalizer⟩ := symplecticSplitSet_closure n hn4 hr hr2 hζo hscard
  obtain ⟨hS_comm, hS_odd, hinv⟩ := symplecticSplitSet_inversion (n := n) hr hr2 hζo (s := s)
  let ψ : K →* K ⧸ Subgroup.center K := QuotientGroup.mk' (Subgroup.center K)
  let φ : K →* StatedSp n F := e.toMonoidHom.comp ψ
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = Subgroup.center K := by
    rw [MonoidHom.ker_comp_of_injective _ _ e.injective, QuotientGroup.ker_mk']
  have hkerle : φ.ker ≤ Subgroup.center K := le_of_eq hker
  have hcommS := CFSG.GroupTheory.comap_closure_comm_of_inverters (φ := φ) hφ hkerle
    hS_comm hS_odd hinv
  have hDcomm : ∀ x ∈ D.comap φ, ∀ y ∈ D.comap φ, x * y = y * x := by
    simpa [D] using hcommS
  have hU : IsSylowTwoOf (unipotent n F) ⊤ := by
    obtain ⟨P, hP⟩ := exists_sylow_unipotent (K := F) 2 n
    exact hP ▸ CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow P
  have hbound := le_pRank_normalizerQuotient_of_comap_comm (φ := φ) hφ hkerle hr hr2 hDexp
    hDcomm (k := 4) (by rw [hDcard]) hU hDnormalizer S hS
  exact ⟨r, hr, hr2, hrdvd, by omega⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
