module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddInner
public import CFSG.LieType.SeitzGeneration.UnitaryHyperScope
import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary
  CFSG.LieType.SeitzGeneration CFSG.Assembly.LowTwoRank CFSG.RankThree.PartOne.CTP

namespace USeitz

variable {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ} {W : Submodule K (Fin n → K)}

theorem eq_one_of_sq_eq_one_uRad {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0} (h2K : (2 : K) ≠ 0)
    {g : SUid σ n} (hg : g ∈ uRad σ W hW) (hg2 : g ^ 2 = 1) : g = 1 := by
  obtain ⟨hg1, hg2', hg3⟩ := hg
  set N : Module.End K (Fin n → K) := actU σ n g - 1 with hNdef
  have hNx : ∀ x, N x = g • x - x := fun x => by simp [hNdef, actU_apply]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ hermOrth σ W := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ W := by rw [hNx]; exact hg2' _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : actU σ n g = 1 + N := by rw [hNdef]; abel
  have hpow := congrArg (actU σ n) hg2
  rw [map_pow, map_one, hg1', unip_pow_of_cube_eq_zero (K := K) hN3 2, Nat.choose_self,
    Nat.cast_one, one_smul, Nat.cast_ofNat, add_assoc] at hpow
  have h0 : (2 : K) • N + N * N = 0 := add_eq_left.1 hpow
  have h3 : N * N = 0 := by
    have h := congrArg (fun X => N * X) h0
    simp only [mul_add, mul_zero, mul_smul_comm, ← mul_assoc, hN3, add_zero] at h
    exact (smul_eq_zero.1 h).resolve_left h2K
  have h4 : N = 0 := by
    rw [h3, add_zero] at h0
    exact (smul_eq_zero.1 h0).resolve_left h2K
  have h5 : actU σ n g = 1 := by rw [hg1', h4, add_zero]
  refine ext_smul σ fun v => ?_
  rw [one_smul]
  exact LinearMap.congr_fun h5 v

theorem not_two_dvd_card_uRad [Finite K] {hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0}
    (h2K : (2 : K) ≠ 0) : ¬ 2 ∣ Nat.card (uRad σ W hW) := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have h1 : (g : SUid σ n) ^ 2 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have h3 : g = 1 := Subtype.ext (eq_one_of_sq_eq_one_uRad h2K g.2 h1)
  rw [h3, orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem top_le_iSup_centralizer_of_isotropic [Finite K] (hσ : IsUnitaryInvolution σ)
    (hn : 2 ≤ n) (h3 : n = 3 → ∃ s : K, s ≠ 0 ∧ σ s * s ≠ 1) {P : Type} [Group P] [Finite P]
    (π : SUid σ n →* P) (hπ : Function.Surjective π) (hker : ∀ g ∈ π.ker, ∃ c : K, matU g = c • 1)
    (h2K : (2 : K) ≠ 0) {E : Subgroup P} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    (hW0 : W ≠ ⊥) (hW : ∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0)
    (hstab : ∀ g : SUid σ n, π g ∈ E → ∀ w ∈ W, g • w ∈ W) :
    (⊤ : Subgroup P) ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ Subgroup.centralizer ({a} : Set P) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 E := hE.isElementaryAbelian
  set Et : Subgroup (SUid σ n) := E.comap π with hEt
  have hEtcard : ((Nat.card Et : ℕ) : K) ≠ 0 :=
    natCast_card_comap_ne_zero (by omega) π hker Nat.prime_two (by exact_mod_cast h2K) hE.2
  have hWs : ∀ g ∈ Et, ∀ w ∈ W, g • w ∈ W := fun g hg w hw => hstab g hg w hw
  obtain ⟨W', hW', hcompl, hW's⟩ := exists_opposite hσ hEtcard hW hWs
  set M : Subgroup P := ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓
    Subgroup.centralizer ({a} : Set P) with hM
  have hrad : ∀ {X : Submodule K (Fin n → K)} (hX : ∀ x ∈ X, ∀ y ∈ X, herm σ x y = 0),
      (∀ g ∈ Et, ∀ w ∈ X, g • w ∈ X) → uRad σ X hX ≤ M.comap π := by
    intro X hX hXs q hq
    have hnorm : E ≤ Subgroup.normalizer (((uRad σ X hX).map π : Subgroup P) : Set P) := by
      intro e he
      rw [Subgroup.mem_normalizer_iff]
      have key : ∀ e ∈ E, ∀ v ∈ (uRad σ X hX).map π, e * v * e⁻¹ ∈ (uRad σ X hX).map π := by
        intro e he v hv
        obtain ⟨a, rfl⟩ := hπ e
        obtain ⟨q', hq', rfl⟩ := hv
        have haEt : a ∈ Et := he
        exact ⟨a * q' * a⁻¹, uRad_conj_mem (fun w hw => hXs a haEt w hw)
          (fun w hw => hXs a⁻¹ (Et.inv_mem haEt) w hw) hq', by simp⟩
      intro h
      refine ⟨key e he h, fun hh => ?_⟩
      have := key e⁻¹ (E.inv_mem he) _ hh
      simpa [mul_assoc] using this
    have hQp : ¬ 2 ∣ Nat.card ((uRad σ X hX).map π) := fun hd =>
      not_two_dvd_card_uRad h2K (hd.trans (Subgroup.card_map_dvd _ π))
    exact CFSG.LieType.Chevalley.le_iSup_inf_centralizer_of_coprime (by omega) hQp hnorm le_top
      (Subgroup.mem_map_of_mem _ hq)
  have htop : M.comap π = ⊤ :=
    eq_top_of_uRad_of_opposite hσ hn h3 hW0 hW hW' hcompl (hrad hW hWs) (hrad hW' hW's)
  intro k _
  obtain ⟨g, rfl⟩ := hπ k
  have hg : g ∈ M.comap π := htop ▸ Subgroup.mem_top g
  exact hg

end USeitz

theorem iSup_centralizer_eq_of_subgroupOf {G : Type*} [Group G] {L E : Subgroup G}
    (h : (⊤ : Subgroup ↥L) ≤ ⨆ a ∈ E.subgroupOf L, ⨆ (_ : a ≠ 1),
      (⊤ : Subgroup ↥L) ⊓ centralizer ({a} : Set ↥L)) :
    (⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G)) = L := by
  refine le_antisymm (iSup₂_le fun x _ => iSup_le fun _ => inf_le_left) ?_
  intro y hy
  have hy' := h (mem_top (⟨y, hy⟩ : ↥L))
  have hle : (⨆ a ∈ E.subgroupOf L, ⨆ (_ : a ≠ 1),
      (⊤ : Subgroup ↥L) ⊓ centralizer ({a} : Set ↥L)) ≤
      (⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G)).comap L.subtype := by
    refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
    intro z hz
    rw [mem_comap]
    have ha1' : (a : G) ≠ 1 := fun h => ha1 (Subtype.ext h)
    have hsub : L ⊓ centralizer ({(a : G)} : Set G) ≤
        ⨆ e ∈ E, ⨆ (_ : e ≠ 1), L ⊓ centralizer ({e} : Set G) :=
      le_iSup₂_of_le (a : G) (mem_subgroupOf.mp ha) (le_iSup_of_le ha1' le_rfl)
    refine hsub ⟨z.2, ?_⟩
    show (z : G) ∈ centralizer ({(a : G)} : Set G)
    have := mem_centralizer_singleton_iff.mp hz.2
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val this
  exact hle hy'

@[expose] def SeitzFourUAniso : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K) (n : ℕ) (P : Type) [Group P] [Finite P]
    (π : SUid σ n →* P), IsUnitaryCover σ π → 3 ≤ n → (2 : K) ≠ 0 → Subgroup.center P = ⊥ →
    ∀ E : Subgroup P, IsElemAbelian 2 E → Nat.card E = 4 →
    (∀ W : Submodule K (Fin n → K), (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) →
      (∀ g : SUid σ n, π g ∈ E → ∀ w ∈ W, g • w ∈ W) → W = ⊥) →
    (⊤ : Subgroup P) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup P) ⊓ centralizer ({a} : Set P)

theorem seitzFourInner_psu_of_aniso (hA : SeitzFourUAniso) :
    SeitzFourInner fun X _ => ∃ n p f : ℕ, 3 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSU n p f := by
  intro G _ _ L E hLn hLs hnab ⟨n, p, f, hn, hp2, hm⟩ hC hE h4 hEL _
  classical
  have hm' : CFSG.Models.LieModel ↥L .PSU n p f := hm
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ :=
    CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) hm'
  have : Fact p.Prime := ⟨hp⟩
  have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    hp (k := 2 * f) (by omega) (by rw [hK, ← pow_mul, mul_comm])
  have hq2 : p ^ f ≠ 2 := by
    intro h
    have : p ∣ 2 := by
      have := dvd_pow_self p (by omega : f ≠ 0)
      rwa [h] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 this)
  have h2K : (2 : K) ≠ 0 := by
    intro h0
    have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  set σ : K ≃+* K := CFSG.LieType.BorelTits.unitaryInvolution K p f with hσ
  let π₀ : SUid σ n →* StatedProj (StatedSU n (p ^ f) K) :=
    (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K))).comp
      (Subgroup.inclusion (le_of_eq (SUid_eq_statedSU hK n)))
  have hπ₀ : Function.Surjective π₀ := by
    intro y
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective y
    exact ⟨⟨g.1, (SUid_eq_statedSU hK n).symm ▸ g.2⟩, rfl⟩
  let π : SUid σ n →* ↥L := eS.symm.toMonoidHom.comp π₀
  have hc : IsUnitaryCover σ π := by
    refine ⟨isUnitaryInvolution_unitaryInvolution hK, by omega,
      fun _ => exists_norm_ne_one hK hq2, eS.symm.surjective.comp hπ₀, fun g hg => ?_⟩
    rw [MonoidHom.mem_ker] at hg
    have h1 : π₀ g = 1 := eS.symm.injective (by rw [map_one]; exact hg)
    have h2 := (QuotientGroup.eq_one_iff _).1 h1
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 h2
    refine ⟨(c : K), ?_⟩
    have : ((g : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        (Matrix.GeneralLinearGroup.scalar (Fin n) c : GL (Fin n) K) := congrArg Units.val hc.symm
    rw [this, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.smul_one_eq_diagonal]
  have hncomm : ¬ IsMulCommutative ↥L := fun h => by
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (h.is_comm.comm a b)
  have hZ : Subgroup.center ↥L = ⊥ :=
    TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hncomm
  have : Finite ↥L := inferInstance
  set E' : Subgroup ↥L := E.subgroupOf L with hE'
  have hE' : IsElemAbelian 2 E' := hE.subgroupOf L
  have h4' : Nat.card E' = 4 := by
    rw [← h4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  apply iSup_centralizer_eq_of_subgroupOf
  by_cases hiso : ∃ W : Submodule K (Fin n → K), W ≠ ⊥ ∧ (∀ x ∈ W, ∀ y ∈ W, herm σ x y = 0) ∧
      ∀ g : SUid σ n, π g ∈ E' → ∀ w ∈ W, g • w ∈ W
  · obtain ⟨W, hW0, hW, hWs⟩ := hiso
    exact USeitz.top_le_iSup_centralizer_of_isotropic hc.involution hc.two_le hc.exists_norm π
      hc.surjective hc.ker_scalar h2K hE' h4' hW0 hW hWs
  · refine hA K σ n ↥L π hc hn h2K hZ E' hE' h4' fun W hW hWs => ?_
    by_contra hne
    exact hiso ⟨W, hne, hW, hWs⟩

end CFSG.LocalAnalysis.WeakClosure81
