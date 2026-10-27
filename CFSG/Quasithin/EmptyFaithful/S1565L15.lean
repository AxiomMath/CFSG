module

public import CFSG.Quasithin.EmptyFaithful.S1565L14
public import CFSG.Quasithin.EmptyFaithful.S1565L12

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.S1565

@[expose] def OrthExcl : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (n : ℕ), 3 ≤ n → Odd n → ∀ (L₀ : Subgroup (MulAut W))
    (V C : Subgroup W), (IsPSL 2 2 n ↥L₀ ∨ IsSz n ↥L₀) →
      ¬ ∃ a, 1 ≤ a ∧ BinaryOrthogonalFour L₀ V C a

@[expose] def OmegaGood : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W] (M Mp L : Subgroup (MulAut W)) (V : Subgroup W)
    (t : MulAut W) (Q : Subgroup (MulAut W)) (n : ℕ), 3 ≤ n →
    (IsPSL 2 2 n ↥L ∨ IsSz n ↥L) → Mp = L ⊔ conjAutSub t L →
    (∀ g ∈ L, ∀ g' ∈ conjAutSub t L, g * g' = g' * g) →
    (∃ b ∈ L, b ∈ Q ∧ b ≠ 1 ∧ Odd (orderOf b)) →
    (V = ⊤ ∧ M ≤ stabSub V ∧ ∃ n', IsPSL 2 2 n' ↥(autSub L V) ∧
        Omega4PlusModule (autSub Mp V) n') →
    ∃ a₀ ∈ Q, ∃ m : ℕ, Odd m ∧ a₀ ^ m = 1 ∧ ∀ w : W, a₀ w * w⁻¹ ∈ fixV Mp → w ∈ fixV Mp

theorem exists_odd_borel_element {X : Type} [Group X] [Finite X]
    {n : ℕ} (hn : 3 ≤ n) (h : IsPSL 2 2 n X ∨ IsSz n X) (S : Sylow 2 X) :
    ∃ b ∈ Subgroup.normalizer ((S : Subgroup X) : Set X), b ≠ 1 ∧ Odd (orderOf b) := by
  have hB : E2.IsBorelIn (⊤ : Subgroup X) (⊤ ⊓ Subgroup.normalizer ((S : Subgroup X) : Set X)) := by
    refine ⟨(S : Subgroup X), ⟨le_top, S.isPGroup', ?_⟩, rfl⟩
    show ¬ 2 ∣ (S : Subgroup X).relIndex ⊤
    rw [Subgroup.relIndex_top_right]
    exact S.not_dvd_index
  obtain ⟨r, hr, hr2, y, hy, hyo⟩ : ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧
      ∃ y ∈ (⊤ : Subgroup X) ⊓ Subgroup.normalizer ((S : Subgroup X) : Set X), orderOf y = r := by
    rcases h with h | h
    · exact exists_odd_order_mem_borel_psl2 (by omega) (isPSL_congr Subgroup.topEquiv.symm h) hB
    · exact exists_odd_order_mem_borel_sz (isSz_congr Subgroup.topEquiv.symm h) hB
  refine ⟨y, hy.2, ?_, ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hyo
    exact hr.one_lt.ne hyo
  · rw [hyo]
    exact hr.odd_of_ne_two hr2

section Core

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K : Subgroup G}

theorem typesFive_core
    (hD36 : D36) (hD37 : D37) (hD321 : D321) (hI5 : Insp5a) (hA37 : A37ForSQTK)
    (hA38 : A38ForSQTK) (hOrth : OrthExcl) (hΩ : OmegaGood)
    (hF : HypF918 T V L V₁ Vp H K) (hH : SQTKGroup ↥H) (hHK : H = K ⊔ T)
    (hK : conjClosure K T ≠ K) (M I : Subgroup G) (hTM : T ≤ M) (hV₁I : V₁ ≤ I)
    (hIU : I ≤ conjClosure Vp H) (W : Subgroup ↥(tildeOf V₁ (conjClosure Vp H)))
    (hW : ∀ t ∈ autIH V₁ Vp H T, ∀ w ∈ W, t w ∈ W) (hirr : IsIrrPlusTildeU hF I W)
    (hker : kerIn (H ⊓ M) H = pCoreOf 2 H) {n : ℕ} (hn3 : 3 ≤ n) (hnodd : Odd n)
    (hshape : IsPSL 2 2 n ↥(E2.star (H ⊓ M) H K) ∨ IsSz n ↥(E2.star (H ⊓ M) H K))
    (hB : E2.IsBorelIn (E2.star (H ⊓ M) H K) (E2.star (H ⊓ M) H ((H ⊓ M) ⊓ K))) :
    ChiefFreeBelow15365 hF M I := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hFU := factElem hF (le_conjClosure Vp H)
  have hFI := factElem hF hIU
  have hIT := isIrrPlusTildeT_of_ambient hF hIU W hW hirr
  have hirr' : subM V₁ (conjClosure I H) I ∈ IrrPlusOn (autIH V₁ I H (conjClosure K T))
      (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hIT
  have hnt := hnt_of_irrSec hF hIU hirr'.1.2.2.2.1
  obtain ⟨S, hS⟩ := exists_sylow_borel_acting hF M I hIU hnt hker hshape hB
  have hsimple := isSimpleGroup_of_psl2_or_sz hshape
  have hne : autIH V₁ I H K ≠ ⊥ := by
    rw [autIH_eq_map hF hKH]
    exact map_K_ne_bot hF hIU hnt
  have : Nontrivial ↥(autIH V₁ I H K) := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
  have hker' : ∀ k : ↥K, Subgroup.inclusion hKH k ∈ (kerIn (H ⊓ M) H).subgroupOf H →
      toAutI hF I k = 1 := by
    intro k hk
    rw [Subgroup.mem_subgroupOf, hker] at hk
    exact (toAutI_eq_one_iff hF I k).mpr (hF.actH_eq_one_of_mem_pCoreOf hIU hk)
  obtain ⟨e⟩ := nonempty_mulEquiv_star_of_surjective hKH (toAutI hF I) (toAutI_surjective hF I) hker' hsimple
  have hshapeL : IsPSL 2 2 n ↥(autIH V₁ I H K) ∨ IsSz n ↥(autIH V₁ I H K) := by
    rcases hshape with h | h
    · exact Or.inl (isPSL_congr e h)
    · exact Or.inr (isSz_congr e h)
  obtain ⟨t', ht'T, ht'K⟩ : ∃ t' ∈ T, t' ∉ Subgroup.normalizer (K : Set G) := by
    by_contra hcon
    push Not at hcon
    apply hK
    apply le_antisymm
    · exact conjClosure_le fun t ht z hz => (Subgroup.mem_normalizer_iff.mp (hcon t ht) z).mp hz
    · exact le_conjClosure K T
  obtain ⟨-, hFive⟩ := F918_5' hF hH hK hV₁I hIU W hW hirr hD36 hD37 hD321 hI5 hA37 hA38
  have h5 := hFive t' ht'T ht'K
  obtain ⟨-, -, hprelim⟩ := five_prelim hF hH hK hIU hnt hA37 hA38
  obtain ⟨ht'T', -, hMp, -⟩ := hprelim t' ht'T ht'K
  obtain ⟨-, hdata⟩ := five_group_data hF hH hA37 hA38 hK
  obtain ⟨hKt, -, hcomm0, hcoset⟩ := hdata t' ht'T ht'K
  have htH : t' ∈ H := hF.T_le_H ht'T
  have hKtH : K.map (MulAut.conj t').toMonoidHom ≤ H := le_of_mem_cComp hKt
  set φ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hφ
  set t₁ : MulAut ↥(tildeOf V₁ (conjClosure I H)) := φ ⟨t', htH⟩ with ht₁
  set Q : Subgroup (MulAut ↥(tildeOf V₁ (conjClosure I H))) :=
    ((H ⊓ M).subgroupOf H).map φ with hQ
  have htQ : t₁ ∈ Q :=
    ⟨⟨t', htH⟩, Subgroup.mem_subgroupOf.mpr ⟨htH, hTM ht'T⟩, rfl⟩
  have hconj : conjAutSub t₁ (autIH V₁ I H K) =
      autIH V₁ I H (K.map (MulAut.conj t').toMonoidHom) := by
    rw [autIH_eq_map hF hKH, autIH_eq_map hF hKtH]
    exact conjAutSub_map_subgroupOf φ htH
  have hcomm2 : ⁅autIH V₁ I H K, autIH V₁ I H (K.map (MulAut.conj t').toMonoidHom)⁆ = ⊥ := by
    rw [autIH_eq_map hF hKH, autIH_eq_map hF hKtH, ← Subgroup.map_commutator,
      Subgroup.map_eq_bot_iff]
    intro c hc
    have hc' : (c : G) ∈ ⁅K, K.map (MulAut.conj t').toMonoidHom⁆ := by
      have := Subgroup.mem_map_of_mem H.subtype hc
      rwa [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH,
        Subgroup.map_subgroupOf_eq_of_le hKtH] at this
    exact hF.actH_eq_one_of_mem_pCoreOf hIU (hcomm0 hc')
  have hcomm : ∀ g ∈ autIH V₁ I H K, ∀ g' ∈ conjAutSub t₁ (autIH V₁ I H K), g * g' = g' * g := by
    intro g hg g' hg'
    rw [hconj] at hg'
    have h1 := Subgroup.commutator_mem_commutator hg hg'
    rw [hcomm2, Subgroup.mem_bot] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have ht2 : t₁ * t₁ ∈ Subgroup.normalizer ((autIH V₁ I H K : Subgroup _) : Set _) := by
    have hxH : t' * t' ∈ H := H.mul_mem htH htH
    have hxN : t' * t' ∈ Subgroup.normalizer (K : Set G) := by
      rcases hcoset (t' * t') hxH with h | h
      · exact h
      · rw [inv_mul_cancel_left] at h
        exact absurd h ht'K
    have hxN' : (⟨t' * t', hxH⟩ : ↥H) ∈
        Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      have := Subgroup.mem_normalizer_iff.mp hxN (y : G)
      simpa [Subgroup.mem_subgroupOf] using this
    have h1 := Subgroup.le_normalizer_map φ ⟨_, hxN', rfl⟩
    rw [← autIH_eq_map hF hKH] at h1
    have e2 : φ ⟨t' * t', hxH⟩ = t₁ * t₁ := by
      rw [ht₁, ← map_mul]
      rfl
    rwa [e2] at h1
  have htMp : t₁ ∈ Subgroup.normalizer
      ((autIH V₁ I H (conjClosure K T) : Subgroup _) : Set _) := autIH_T_le_normalizer hF I ht'T'
  have hSQ : ∃ S : Sylow 2 ↥(autIH V₁ I H K),
      ∀ b ∈ Subgroup.normalizer ((S : Subgroup ↥(autIH V₁ I H K)) : Set ↥(autIH V₁ I H K)),
        (b : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈ Q := by
    refine ⟨S, fun b hb => ?_⟩
    obtain ⟨k, hkM, hkb⟩ := hS b hb
    rw [← hkb, toAutI_coe]
    exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr ⟨hKH k.2, hkM⟩, rfl⟩
  have : Finite ↥(autIH V₁ I H K) := Finite.of_surjective _ (toAutI_surjective hF I)
  obtain ⟨b₁, hb₁N, hb₁1, hb₁odd⟩ := exists_odd_borel_element hn3 hshapeL S
  have hb₀ : ∃ b ∈ autIH V₁ I H K, b ∈ Q ∧ b ≠ 1 ∧ Odd (orderOf b) := by
    refine ⟨(b₁ : MulAut ↥(tildeOf V₁ (conjClosure I H))), b₁.2, ?_, ?_, ?_⟩
    · obtain ⟨k, hkM, hkb⟩ := hS b₁ hb₁N
      rw [← hkb, toAutI_coe]
      exact ⟨Subgroup.inclusion hKH k, Subgroup.mem_subgroupOf.mpr ⟨hKH k.2, hkM⟩, rfl⟩
    · intro h1
      exact hb₁1 (Subtype.ext h1)
    · rw [Subgroup.orderOf_coe]
      exact hb₁odd
  obtain ⟨a₀, ha₀, m, hodd, hpow, hgood⟩ :=
    modFive_good (M := autIH V₁ I H H) (T := autIH V₁ I H T)
      (V := subM V₁ (conjClosure I H) I) htQ hMp htMp ht2 hcomm hSQ hn3 hshapeL
      (fun L₀ V' C hs => hOrth _ n hn3 hnodd L₀ V' C hs)
      (hΩ _ _ _ _ _ _ _ n hn3 hshapeL hMp hcomm hb₀) h5
  obtain ⟨t₀, ht₀mem, rfl⟩ := ha₀
  have ht₀M : (t₀ : G) ∈ M := (Subgroup.mem_subgroupOf.mp ht₀mem).2
  exact chiefFreeBelow15365_of_good_tilde hF hHK M hV₁I hIU t₀ ht₀M hodd hpow hgood

end Core

end CFSG.Quasithin
