module

public import CFSG.Quasithin.Vol2.KGFactC31Orb

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

structure RefData {G₀ : Type} [Group G₀] (U M' : Subgroup G₀) : Prop where
  cent : Subgroup.centralizer (U : Set G₀) ≤ U
  comm : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a
  le : U ≤ M'
  norm : M' ≤ Subgroup.normalizer (U : Set G₀)
  perf : ∀ K : Subgroup G₀, K ≤ Subgroup.normalizer (U : Set G₀) → ⁅K, K⁆ = K → K ≤ M'
  simple : ∀ K : Subgroup G₀, U ≤ K → K ≤ M' → M' ≤ Subgroup.normalizer (K : Set G₀) →
    K = U ∨ K = M'

variable {A : Type} [Group A] {G₀ : Type} [Group G₀]

theorem perf_of_card [Finite G₀] {N M' : Subgroup G₀} (hMN : M' ≤ N)
    (hcard : Nat.card N ≤ 2 * Nat.card M') :
    ∀ K : Subgroup G₀, K ≤ N → ⁅K, K⁆ = K → K ≤ M' := fun K hKN hK => by
  rw [← hK]
  exact (Subgroup.commutator_mono hKN hKN).trans (commutator_le_of_card hMN hcard)

theorem map_comap_eq_of_le_range (ι : G₀ →* A) {K : Subgroup A} (hK : K ≤ ι.range) :
    (K.comap ι).map ι = K := by
  rw [Subgroup.map_comap_eq, inf_eq_right.mpr hK]

theorem config_of_ref [Finite A] [Finite G₀] {S M₀ R M V : Subgroup A} (hS : S.Normal)
    (hA2 : Nat.card A ≤ 2 * Nat.card S) (hM₀S : M₀ ≤ S) (hper : ⁅M₀, M₀⁆ = M₀)
    (hR : IsPGroup 2 ↥R) (hRM : R ≤ M) (hMN : M ≤ Subgroup.normalizer (M₀ : Set A))
    (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hVM₀ : V ≤ M₀) (hV : IsElemAbelian 2 V) (hcomm : ⁅V, M₀⁆ = V)
    (hVc : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R)))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) {y t : A} (hy : y ∈ M₀) (ht : t ∈ V)
    (hyt : y * t * y⁻¹ ≠ t) (ι : G₀ →* A) (hι : Function.Injective ι) (hιS : ι.range = S)
    {U M' : Subgroup G₀} (hd : RefData U M') (hU : orbSub y t = U.map ι) :
    V = U.map ι ∧ pCoreOf 2 M₀ = U.map ι ∧ M₀ = M'.map ι ∧
      (R = U.map ι ∨ R = Subgroup.centralizer ((U.map ι : Subgroup A) : Set A)) ∧
      M₀ ⊓ Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) ≤ U.map ι := by
  obtain ⟨hVO, hOR, hRC, hNRM⟩ :=
    orb_facts hR hRM hMN hM₀R hsyl hVM₀ hV hcomm hVc hNR
  have hM₀V := le_normalizer_of_comm hcomm
  have hUV : U.map ι ≤ V := hU ▸ orbSub_le (hM₀V hy) ht
  have hCS : S ⊓ Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) ≤ U.map ι := by
    rw [← hιS, ← map_centralizer_eq ι hι U]
    exact Subgroup.map_mono hd.cent
  obtain ⟨hVU, hOU⟩ := eq_of_centralizer hUV hVO hOR hRC hM₀S hCS
  have hUS : U.map ι ≤ S := hιS ▸ Subgroup.map_le_range ι U
  have hUC : U.map ι ≤ Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hd.comm a ha b hb]
  have hCU : S ⊓ Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) = U.map ι :=
    le_antisymm hCS (le_inf hUS hUC)
  have hRV : R = U.map ι ∨ R = Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) :=
    eq_or_eq_of_card hS hA2 hCU (hVU ▸ hVO.trans hOR) (hVU ▸ hRC)
  have hNU : Subgroup.normalizer ((U.map ι : Subgroup A) : Set A) ≤
      Subgroup.normalizer (M₀ : Set A) := (normalizer_le_of_eq_or_eq hRV).trans hNRM
  have hN : (Subgroup.normalizer (U : Set G₀)).map ι =
      S ⊓ Subgroup.normalizer ((U.map ι : Subgroup A) : Set A) := by
    rw [← hιS]; exact map_normalizer_eq ι hι U
  have hM₀r : M₀ ≤ ι.range := hιS ▸ hM₀S
  set K₀ := M₀.comap ι with hK₀
  have hK₀map : K₀.map ι = M₀ := map_comap_eq_of_le_range ι hM₀r
  have hK₀perf : ⁅K₀, K₀⁆ = K₀ :=
    Subgroup.map_injective hι (by rw [Subgroup.map_commutator, hK₀map, hper])
  have hK₀N : K₀ ≤ Subgroup.normalizer (U : Set G₀) := by
    intro k hk
    have h1 : ι k ∈ S ⊓ Subgroup.normalizer ((U.map ι : Subgroup A) : Set A) :=
      ⟨hM₀S hk, (hVU ▸ hM₀V) hk⟩
    rw [← hN] at h1
    obtain ⟨k', hk', hkk'⟩ := h1
    rwa [← hι hkk']
  have hM₀M' : M₀ ≤ M'.map ι := by
    rw [← hK₀map]
    exact Subgroup.map_mono (hd.perf K₀ hK₀N hK₀perf)
  have hM'N : M'.map ι ≤ Subgroup.normalizer (M₀ : Set A) :=
    (Subgroup.map_mono hd.norm).trans (by rw [hN]; exact inf_le_right.trans hNU)
  have hsimp : ∀ K : Subgroup A, U.map ι ≤ K → K ≤ M'.map ι →
      M'.map ι ≤ Subgroup.normalizer (K : Set A) → K = U.map ι ∨ K = M'.map ι := by
    intro K hUK hKM hMK
    have hKr : K ≤ ι.range := hKM.trans (Subgroup.map_le_range ι M')
    set K' := K.comap ι with hK'
    have hK : K'.map ι = K := map_comap_eq_of_le_range ι hKr
    have hUK' : U ≤ K' := fun u hu => hUK ⟨u, hu, rfl⟩
    have hKM' : K' ≤ M' := fun k hk => by
      obtain ⟨m, hm, hmk⟩ := hKM hk
      rwa [← hι hmk]
    have hMK' : M' ≤ Subgroup.normalizer (K' : Set G₀) := by
      intro m hm
      rw [Subgroup.mem_normalizer_iff]
      intro k
      have h1 := (Subgroup.mem_normalizer_iff.mp (hMK ⟨m, hm, rfl⟩) (ι k))
      simp only [Subgroup.mem_comap, map_mul, map_inv, hK'] at h1 ⊢
      exact h1
    rcases hd.simple K' hUK' hKM' hMK' with h | h
    · left; rw [← hK, h]
    · right; rw [← hK, h]
  have hne : ¬ M₀ ≤ U.map ι := by
    intro hle
    have hyU : y ∈ V := hVU ▸ hle hy
    have hyt' : y * t = t * y := by
      have := hV.1.is_comm.comm ⟨y, hyU⟩ ⟨t, ht⟩
      simpa using congrArg Subtype.val this
    exact hyt (by rw [hyt', mul_inv_cancel_right])
  have hM : M₀ = M'.map ι := by
    rcases hsimp M₀ (hVU ▸ hVM₀) hM₀M' hM'N with h | h
    · exact absurd h.le hne
    · exact h
  refine ⟨hVU, hOU, hM, hRV, ?_⟩
  calc M₀ ⊓ Subgroup.centralizer ((U.map ι : Subgroup A) : Set A)
      ≤ S ⊓ Subgroup.centralizer ((U.map ι : Subgroup A) : Set A) := inf_le_inf_right _ hM₀S
    _ ≤ U.map ι := hCS

end CFSG.Quasithin.KGC31

end
