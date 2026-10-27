
module

public import CFSG.Quasithin.Vol2.KGFactC31Red

public section

namespace CFSG.Quasithin.KGC31

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {A : Type} [Group A]

@[expose] def orbSub (y t : A) : Subgroup A :=
  Subgroup.closure (Set.range fun j : ℕ => y ^ j * t * (y ^ j)⁻¹)

theorem mem_orbSub (y t : A) : t ∈ orbSub y t :=
  Subgroup.subset_closure ⟨0, by simp⟩

theorem conj_mem_orbSub (y t : A) (j : ℕ) : y ^ j * t * (y ^ j)⁻¹ ∈ orbSub y t :=
  Subgroup.subset_closure ⟨j, rfl⟩

theorem orbSub_le {y t : A} {V : Subgroup A} (hy : y ∈ Subgroup.normalizer (V : Set A))
    (ht : t ∈ V) : orbSub y t ≤ V := by
  rw [orbSub, Subgroup.closure_le]
  rintro _ ⟨j, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hy j) t).mp ht

theorem orbSub_map {B : Type} [Group B] (f : A →* B) (y t : A) :
    (orbSub y t).map f = orbSub (f y) (f t) := by
  rw [orbSub, MonoidHom.map_closure, orbSub]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_range]
  constructor
  · rintro ⟨_, ⟨j, rfl⟩, rfl⟩
    exact ⟨j, by simp⟩
  · rintro ⟨j, rfl⟩
    exact ⟨_, ⟨j, rfl⟩, by simp⟩

theorem not_mem_of_comm {y t : A} {U : Subgroup A} (hU : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a)
    (ht : t ∈ U) (hyt : y * t * y⁻¹ ≠ t) : y ∉ U := fun hy =>
  hyt (by rw [hU y hy t ht, mul_inv_cancel_right])

variable {S M₀ R M V : Subgroup A}

theorem orb_facts [Finite A] (hR : IsPGroup 2 ↥R) (hRM : R ≤ M)
    (hMN : M ≤ Subgroup.normalizer (M₀ : Set A)) (hM₀R : M₀ ≤ Subgroup.normalizer (R : Set A))
    (hsyl : IsSylowTwoOf R (CFSG.Quasithin.centralizerSection M M₀ (pCoreOf 2 M₀)))
    (hVM₀ : V ≤ M₀) (hV : IsElemAbelian 2 V) (hcomm : ⁅V, M₀⁆ = V)
    (hVc : V ≤ CFSG.Quasithin.centerOf (pCoreOf 2 (M₀ ⊔ R)))
    (hNR : Subgroup.normalizer (R : Set A) ≤ M) :
    V ≤ pCoreOf 2 M₀ ∧ pCoreOf 2 M₀ ≤ R ∧ R ≤ Subgroup.centralizer (V : Set A) ∧
      Subgroup.normalizer (R : Set A) ≤ Subgroup.normalizer (M₀ : Set A) := by
  refine ⟨le_pCoreOf_of_comm hV hVM₀ hcomm, pCoreOf_le_of_sylow hR hRM hMN hM₀R hNR hsyl,
    ?_, hNR.trans hMN⟩
  have h := le_centralizer_of_le_centerOf hR hM₀R hVc
  exact Subgroup.le_centralizer_iff.mp h

theorem eq_of_centralizer {U : Subgroup A} (hUV : U ≤ V) (hVO : V ≤ pCoreOf 2 M₀)
    (hOR : pCoreOf 2 M₀ ≤ R) (hRC : R ≤ Subgroup.centralizer (V : Set A)) (hM₀S : M₀ ≤ S)
    (hC : S ⊓ Subgroup.centralizer (U : Set A) ≤ U) : V = U ∧ pCoreOf 2 M₀ = U := by
  have hOU : pCoreOf 2 M₀ ≤ U :=
    (le_inf ((pCoreOf_le 2 M₀).trans hM₀S)
      (hOR.trans (hRC.trans (Subgroup.centralizer_le hUV)))).trans hC
  exact ⟨le_antisymm (hVO.trans hOU) hUV, le_antisymm hOU (hUV.trans hVO)⟩

theorem card_le_card_mulAut [Finite A] (hS : S.Normal)
    (hC : Subgroup.centralizer (S : Set A) = ⊥) : Nat.card A ≤ Nat.card (MulAut ↥S) := by
  have : Finite (MulAut ↥S) := inferInstance
  refine Nat.card_le_card_of_injective (MulAut.conjNormal (H := S)) fun a b hab => ?_
  have hmem : b⁻¹ * a ∈ Subgroup.centralizer (S : Set A) := by
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := congrArg (fun φ : MulAut ↥S => ((φ ⟨s, hs⟩ : ↥S) : A)) hab
    simp only [MulAut.conjNormal_apply] at h1
    calc s * (b⁻¹ * a) = b⁻¹ * (b * s * b⁻¹) * a := by group
      _ = b⁻¹ * (a * s * a⁻¹) * a := by rw [h1]
      _ = b⁻¹ * a * s := by group
  rw [hC, Subgroup.mem_bot] at hmem
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [hmem, mul_one]

theorem eq_or_eq_of_card [Finite A] {U : Subgroup A} (hS : S.Normal)
    (hA : Nat.card A ≤ 2 * Nat.card S)
    (hCU : S ⊓ Subgroup.centralizer (U : Set A) = U) (hUR : U ≤ R)
    (hRC : R ≤ Subgroup.centralizer (U : Set A)) :
    R = U ∨ R = Subgroup.centralizer (U : Set A) := by
  set C := Subgroup.centralizer (U : Set A) with hCdef
  have hSi : S.index ≤ 2 := by
    have h := S.card_mul_index
    have hpos : 0 < Nat.card S := Nat.card_pos
    by_contra hlt
    have hlt' : 3 ≤ S.index := by omega
    have : 3 * Nat.card S ≤ Nat.card A := by
      rw [← h, mul_comm]
      exact Nat.mul_le_mul_left _ hlt'
    omega
  have hUC : U.relIndex C ≤ 2 := by
    have h1 : (S ⊓ C).relIndex C = S.relIndex C := Subgroup.inf_relIndex_right S C
    rw [hCU] at h1
    rw [h1]
    exact (Nat.le_of_dvd (Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite))
      (Subgroup.relIndex_dvd_index_of_normal (H := S) (K := C))).trans hSi
  have hmul := Subgroup.relIndex_mul_relIndex U R C hUR hRC
  have h1 : U.relIndex R ≠ 0 := Subgroup.index_ne_zero_of_finite
  have h2 : R.relIndex C ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases Nat.lt_or_ge (U.relIndex R) 2 with hlt | hge
  · left
    have : U.relIndex R = 1 := by omega
    exact le_antisymm (Subgroup.relIndex_eq_one.mp this) hUR
  · right
    have : R.relIndex C = 1 := by
      rw [← hmul] at hUC
      have : U.relIndex R * R.relIndex C ≥ 2 * R.relIndex C := Nat.mul_le_mul_right _ hge
      omega
    exact le_antisymm hRC (Subgroup.relIndex_eq_one.mp this)

theorem normalizer_le_normalizer_centralizer (U : Subgroup A) :
    Subgroup.normalizer (U : Set A) ≤
      Subgroup.normalizer ((Subgroup.centralizer (U : Set A) : Subgroup A) : Set A) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro c
  simp only [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  constructor
  · intro hc u hu
    have hu' : g⁻¹ * u * g⁻¹⁻¹ ∈ U := by
      have := (hg (g⁻¹ * u * g)).mpr (by simpa [mul_assoc] using hu)
      simpa [mul_assoc] using this
    have h1 := hc _ hu'
    calc u * (g * c * g⁻¹) = g * ((g⁻¹ * u * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * u * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * u := by group
  · intro hc u hu
    have hu' : g * u * g⁻¹ ∈ U := (hg u).mp hu
    have h1 := hc _ hu'
    have h2 : g * (u * c) * g⁻¹ = g * (c * u) * g⁻¹ := by
      calc g * (u * c) * g⁻¹ = (g * u * g⁻¹) * (g * c * g⁻¹) := by group
        _ = (g * c * g⁻¹) * (g * u * g⁻¹) := h1
        _ = g * (c * u) * g⁻¹ := by group
    simpa using h2

theorem normalizer_le_of_eq_or_eq {U : Subgroup A}
    (h : R = U ∨ R = Subgroup.centralizer (U : Set A)) :
    Subgroup.normalizer (U : Set A) ≤ Subgroup.normalizer (R : Set A) := by
  rcases h with rfl | rfl
  · exact le_rfl
  · exact normalizer_le_normalizer_centralizer U

theorem commutator_le_of_card [Finite A] {N M' : Subgroup A} (hMN : M' ≤ N)
    (hcard : Nat.card N ≤ 2 * Nat.card M') : ⁅N, N⁆ ≤ M' := by
  have hi : (M'.subgroupOf N).index ≤ 2 := by
    have h := (M'.subgroupOf N).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv] at h
    have hpos : 0 < Nat.card M' := Nat.card_pos
    by_contra hlt
    have hlt' : 3 ≤ (M'.subgroupOf N).index := by omega
    have : 3 * Nat.card M' ≤ Nat.card N := by
      rw [← h, mul_comm]
      exact Nat.mul_le_mul_left _ hlt'
    omega
  have hpos : (M'.subgroupOf N).index ≠ 0 := Subgroup.index_ne_zero_of_finite
  rcases Nat.lt_or_ge (M'.subgroupOf N).index 2 with h1 | h2
  · have h1' : (M'.subgroupOf N).index = 1 := by omega
    rw [Subgroup.index_eq_one] at h1'
    have hNM : N ≤ M' := by
      intro x hx
      have : (⟨x, hx⟩ : ↥N) ∈ M'.subgroupOf N := by rw [h1']; trivial
      exact this
    refine (Subgroup.commutator_le.mpr fun x hx z hz => ?_).trans hNM
    exact N.mul_mem (N.mul_mem (N.mul_mem hx hz) (N.inv_mem hx)) (N.inv_mem hz)
  · have h2' : (M'.subgroupOf N).index = 2 := le_antisymm hi h2
    have hn : (M'.subgroupOf N).Normal := Subgroup.normal_of_index_eq_two h2'
    rw [Subgroup.commutator_le]
    intro x hx z hz
    have hcard2 : Nat.card (↥N ⧸ M'.subgroupOf N) = 2 := by
      rw [← Subgroup.index_eq_card]; exact h2'
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hcyc := isCyclic_of_prime_card (p := 2) hcard2
    have hc : (⟨x, hx⟩ : ↥N) * ⟨z, hz⟩ * (⟨x, hx⟩ : ↥N)⁻¹ * (⟨z, hz⟩ : ↥N)⁻¹ ∈
        M'.subgroupOf N := by
      rw [← QuotientGroup.eq_one_iff]
      simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
      rw [IsCyclic.commGroup.mul_comm (QuotientGroup.mk (⟨x, hx⟩ : ↥N) : ↥N ⧸ M'.subgroupOf N)]
      group
    exact hc

theorem eq_of_le_normalizer [Finite A] {N M' U : Subgroup A} (hM₀N : M₀ ≤ N)
    (hNM₀ : N ≤ Subgroup.normalizer (M₀ : Set A)) (hper : ⁅M₀, M₀⁆ = M₀) (hMN : M' ≤ N)
    (hcard : Nat.card N ≤ 2 * Nat.card M') (hUM₀ : U ≤ M₀)
    (hsimp : ∀ K : Subgroup A, U ≤ K → K ≤ M' → M' ≤ Subgroup.normalizer (K : Set A) →
      K = U ∨ K = M')
    (hne : ¬ M₀ ≤ U) : M₀ = M' := by
  have hle : M₀ ≤ M' := by
    rw [← hper]
    exact (Subgroup.commutator_mono hM₀N hM₀N).trans (commutator_le_of_card hMN hcard)
  rcases hsimp M₀ hUM₀ hle (hMN.trans hNM₀) with h | h
  · exact absurd h.le hne
  · exact h

theorem forall_eq_of_simple {U M' : Subgroup A} [hn : (U.subgroupOf M').Normal]
    (hs : IsSimpleGroup (↥M' ⧸ U.subgroupOf M')) :
    ∀ K : Subgroup A, U ≤ K → K ≤ M' → M' ≤ Subgroup.normalizer (K : Set A) → K = U ∨ K = M' := by
  intro K hUK hKM hMK
  have hKn : (K.subgroupOf M').Normal := by
    refine ⟨fun x hx g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hMK g.2) x).mp hx
  have hmn : ((K.subgroupOf M').map (QuotientGroup.mk' (U.subgroupOf M'))).Normal :=
    Subgroup.Normal.map hKn _ (QuotientGroup.mk'_surjective _)
  rcases @IsSimpleGroup.eq_bot_or_eq_top_of_normal _ _ hs _ hmn with hb | ht
  · left
    refine le_antisymm (fun k hk => ?_) hUK
    have : (QuotientGroup.mk' (U.subgroupOf M') ⟨k, hKM hk⟩) ∈
        (K.subgroupOf M').map (QuotientGroup.mk' (U.subgroupOf M')) :=
      ⟨⟨k, hKM hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩
    rw [hb, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf] at this
    exact this
  · right
    refine le_antisymm hKM fun m hm => ?_
    have : (QuotientGroup.mk' (U.subgroupOf M') ⟨m, hm⟩) ∈
        (K.subgroupOf M').map (QuotientGroup.mk' (U.subgroupOf M')) := by rw [ht]; trivial
    obtain ⟨k, hk, hkm⟩ := this
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hkm
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hk
    rw [Subgroup.mem_subgroupOf] at hkm
    have hkm' : (k : A)⁻¹ * m ∈ U := by simpa using hkm
    have : m = (k : A) * ((k : A)⁻¹ * m) := by group
    rw [this]
    exact K.mul_mem hk (hUK hkm')

section Map

variable {G₀ : Type} [Group G₀] (ι : G₀ →* A) (hι : Function.Injective ι)

include hι

theorem map_normalizer_eq [Finite A] [Finite G₀] (H : Subgroup G₀) :
    (Subgroup.normalizer (H : Set G₀)).map ι =
      ι.range ⊓ Subgroup.normalizer ((H.map ι : Subgroup A) : Set A) := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, ?_⟩
    have hle : (H.map ι).map (MulAut.conj (ι g)).toMonoidHom ≤ H.map ι := by
      rintro _ ⟨_, ⟨h, hh, rfl⟩, rfl⟩
      refine ⟨g * h * g⁻¹, (Subgroup.mem_normalizer_iff.mp hg h).mp hh, ?_⟩
      simp [MulAut.conj_apply]
    have heq := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (f := (MulAut.conj (ι g)).toMonoidHom)
        (MulAut.conj (ι g)).injective])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq
  · rintro ⟨⟨g, rfl⟩, hg⟩
    refine ⟨g, ?_, rfl⟩
    have hle : H.map (MulAut.conj g).toMonoidHom ≤ H := by
      rintro _ ⟨h, hh, rfl⟩
      have : ι g * ι h * (ι g)⁻¹ ∈ H.map ι :=
        (Subgroup.mem_normalizer_iff.mp hg (ι h)).mp ⟨h, hh, rfl⟩
      obtain ⟨h', hh', he⟩ := this
      have : h' = g * h * g⁻¹ := hι (by rw [he]; simp)
      simpa [MulAut.conj_apply, this] using hh'
    have heq := Subgroup.eq_of_le_of_card_ge hle
      (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem map_centralizer_eq (H : Subgroup G₀) :
    (Subgroup.centralizer (H : Set G₀)).map ι =
      ι.range ⊓ Subgroup.centralizer ((H.map ι : Subgroup A) : Set A) := by
  ext a
  constructor
  · rintro ⟨g, hg, rfl⟩
    refine ⟨⟨g, rfl⟩, Subgroup.mem_centralizer_iff.mpr ?_⟩
    rintro _ ⟨h, hh, rfl⟩
    rw [← map_mul, ← map_mul, Subgroup.mem_centralizer_iff.mp hg h hh]
  · rintro ⟨⟨g, rfl⟩, hg⟩
    refine ⟨g, Subgroup.mem_centralizer_iff.mpr fun h hh => hι ?_, rfl⟩
    rw [map_mul, map_mul]
    exact Subgroup.mem_centralizer_iff.mp hg (ι h) ⟨h, hh, rfl⟩

end Map

end CFSG.Quasithin.KGC31

end
