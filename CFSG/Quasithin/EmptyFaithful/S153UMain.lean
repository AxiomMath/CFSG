module

public import CFSG.Quasithin.EmptyFaithful.S153UDef
public import CFSG.Quasithin.EmptyFaithful.S1469Inputs

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace S153U

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem blockProduct_one {I S : Subgroup G} {K : Fin 1 → Subgroup G} (h : IsBlockProduct I S 1 K) :
    I = S ⊔ K 0 ∧ I ≤ Subgroup.normalizer (K 0 : Set G) := by
  have hI : I = S ⊔ K 0 := by
    have := h.2.2.2.2.1
    rwa [iSup_unique] at this
  refine ⟨hI, ?_⟩
  have hS : S ≤ Subgroup.normalizer (K 0 : Set G) := by
    intro t ht
    obtain ⟨j, hj⟩ := h.2.2.2.2.2.2 t ht 0
    have hj0 : j = 0 := Subsingleton.elim j 0
    subst hj0
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 : t * x * t⁻¹ ∈ B6.conjSub t (K 0) ↔ x ∈ K 0 := by
      rw [B6.mem_conjSub, show t⁻¹ * (t * x * t⁻¹) * t = x by group]
    rw [hj] at h1
    exact h1.symm
  rw [hI]
  exact sup_le hS Subgroup.le_normalizer

omit [Finite G] in
theorem card_eq_three_mul {L : Subgroup G} (h : IsAltType L 3) :
    Nat.card L = 3 * Nat.card (pCoreOf 2 L) := by
  obtain ⟨α, hs, hker, -⟩ := h
  have h1 := Subgroup.card_ker_mul_card_range α
  have h2 : Nat.card α.range = 3 := by
    rw [α.range_eq_top_of_surjective hs, Subgroup.card_top]
    have : Nat.card (alternatingGroup (Fin 3)) = 3 := by
      rw [Nat.card_eq_fintype_card]
      decide
    exact this
  have h3 : Nat.card (pCoreOf 2 L) = Nat.card α.ker := by
    rw [hker]
    have : pCoreOf 2 L = (CFSG.pCore 2 ↥L).map L.subtype := by
      rw [pCoreOf]
    rw [this]
    exact Subgroup.card_map_of_injective L.subtype_injective
  rw [h3, ← h1, h2, mul_comm]

omit [Finite G] in
theorem mem_sup_zpowers_iff {S : Subgroup G} {ρ : G} (hρN : ρ ∈ Subgroup.normalizer (S : Set G))
    (hρ2 : ρ ^ 2 ∈ S) {x : G} : x ∈ S ⊔ Subgroup.zpowers ρ ↔ x ∈ S ∨ ρ⁻¹ * x ∈ S := by
  have hconj : ∀ a ∈ S, ρ⁻¹ * a * ρ ∈ S := fun a ha => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hρN) a).mp ha
    simpa using this
  obtain ⟨T', hT'⟩ : ∃ T' : Subgroup G, ∀ x, x ∈ T' ↔ (x ∈ S ∨ ρ⁻¹ * x ∈ S) :=
    ⟨{ carrier := {x | x ∈ S ∨ ρ⁻¹ * x ∈ S}
       one_mem' := Or.inl S.one_mem
       mul_mem' := by
         rintro a b (ha | ha) (hb | hb)
         · exact Or.inl (S.mul_mem ha hb)
         · right
           have : ρ⁻¹ * (a * b) = (ρ⁻¹ * a * ρ) * (ρ⁻¹ * b) := by group
           rw [this]
           exact S.mul_mem (hconj a ha) hb
         · right
           have : ρ⁻¹ * (a * b) = (ρ⁻¹ * a) * b := by group
           rw [this]
           exact S.mul_mem ha hb
         · left
           have : a * b = ρ ^ 2 * (ρ⁻¹ * (ρ⁻¹ * a) * ρ) * (ρ⁻¹ * b) := by group
           rw [this]
           exact S.mul_mem (S.mul_mem hρ2 (hconj _ ha)) hb
       inv_mem' := by
         rintro a (ha | ha)
         · exact Or.inl (S.inv_mem ha)
         · right
           have : ρ⁻¹ * a⁻¹ = (ρ⁻¹ * (ρ⁻¹ * a)⁻¹ * ρ) * (ρ ^ 2)⁻¹ := by group
           rw [this]
           exact S.mul_mem (hconj _ (S.inv_mem ha)) (S.inv_mem hρ2) }, fun x => Iff.rfl⟩
  constructor
  · intro hx
    have hST : S ≤ T' := fun y hy => (hT' y).mpr (Or.inl hy)
    have hρT : ρ ∈ T' := (hT' ρ).mpr (Or.inr (by simp))
    exact (hT' x).mp ((sup_le hST ((Subgroup.zpowers_le).mpr hρT) : S ⊔ Subgroup.zpowers ρ ≤ T') hx)
  · rintro (hx | hx)
    · exact Subgroup.mem_sup_left hx
    · have : x = ρ * (ρ⁻¹ * x) := by group
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers ρ))
        (Subgroup.mem_sup_left hx)

omit [Finite G] in
theorem relIndex_sup_zpowers {S : Subgroup G} {ρ : G} (hρN : ρ ∈ Subgroup.normalizer (S : Set G))
    (hρS : ρ ∉ S) (hρ2 : ρ ^ 2 ∈ S) : S.relIndex (S ⊔ Subgroup.zpowers ρ) = 2 := by
  have hconj : ∀ a ∈ S, ρ⁻¹ * a * ρ ∈ S := fun a ha => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hρN) a).mp ha
    simpa using this
  have hρT : ρ ∈ S ⊔ Subgroup.zpowers ρ := Subgroup.mem_sup_right (Subgroup.mem_zpowers ρ)
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  refine ⟨⟨ρ, hρT⟩, ?_⟩
  rintro ⟨x, hx⟩
  show Xor (x * ρ ∈ S) (x ∈ S)
  by_cases hxS : x ∈ S
  · refine Or.inr ⟨hxS, fun h => hρS ?_⟩
    have := S.mul_mem (S.inv_mem hxS) h
    simpa [mul_assoc] using this
  · refine Or.inl ⟨?_, hxS⟩
    have h1 : ρ⁻¹ * x ∈ S := ((mem_sup_zpowers_iff hρN hρ2).mp hx).resolve_left hxS
    have : x * ρ = ρ ^ 2 * (ρ⁻¹ * (ρ⁻¹ * x) * ρ) := by group
    rw [this]
    exact S.mul_mem hρ2 (hconj _ h1)

theorem isPGroup_of_relIndex_two {S T : Subgroup G} (hS : IsPGroup 2 S) (hST : S ≤ T)
    (h2 : S.relIndex T = 2) : IsPGroup 2 T := by
  obtain ⟨n, hn⟩ := hS.exists_card_eq
  have h1 := Subgroup.relIndex_mul_card S T
  rw [inf_eq_left.mpr hST, h2, hn] at h1
  exact IsPGroup.of_card (n := n + 1) (by rw [← h1]; ring)

theorem relIndex_eq_three {I S Iz : Subgroup G} {K : Fin 1 → Subgroup G}
    (hmp : MinParabolic I S Iz) (hbp : IsBlockProduct I S 1 K) (hnot : ¬ K 0 ≤ Iz)
    (ha3 : IsAltType (K 0) 3) : S.relIndex I = 3 := by
  obtain ⟨hI, hIN⟩ := blockProduct_one hbp
  have hK0I : K 0 ≤ I := hI ▸ le_sup_right
  have hSI : S ≤ I := hmp.isSylow.1
  have hMem : Iz ∈ maxOver I S := by rw [hmp.uniqueMax]; exact rfl
  have hSIz : S ≤ Iz := hMem.2
  have hSsyl : IsSylowTwoOf (S ⊓ K 0) (K 0) := B6.isSylowTwoOf_inf_normal hmp.isSylow hK0I hIN
  have hP : pCoreOf 2 (K 0) ≤ S ⊓ K 0 := B6.pCoreOf_two_le_of_isSylowTwoOf hSsyl
  have hcore : (pCoreOf 2 (K 0)).relIndex (K 0) = 3 := by
    have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 (K 0)) (K 0)
    rw [inf_eq_left.mpr (pCoreOf_le 2 (K 0))] at h1
    have h2 := card_eq_three_mul ha3
    have hpos : 0 < Nat.card (pCoreOf 2 (K 0)) := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2)
  have htower := Subgroup.relIndex_mul_relIndex (pCoreOf 2 (K 0)) (S ⊓ K 0) (K 0) hP inf_le_right
  rw [hcore] at htower
  have hdvd : (S ⊓ K 0).relIndex (K 0) ∣ 3 := Dvd.intro_left _ htower
  have hne : (S ⊓ K 0).relIndex (K 0) ≠ 1 := by
    intro h1
    have := Subgroup.relIndex_eq_one.mp h1
    exact hnot ((this.trans inf_le_left).trans hSIz)
  have h3 : (S ⊓ K 0).relIndex (K 0) = 3 :=
    ((Nat.dvd_prime Nat.prime_three).mp hdvd).resolve_left hne
  have hSN : S ≤ Subgroup.normalizer (K 0 : Set G) := hSI.trans hIN
  rw [B6.relIndex_inf_eq_relIndex_sup hSN, ← hI] at h3
  exact h3

omit [Finite G] in
theorem eq_or_eq_of_relIndex_three {I S L : Subgroup G} (h3 : S.relIndex I = 3) (hSL : S ≤ L)
    (hLI : L ≤ I) : L = S ∨ L = I := by
  have h := Subgroup.relIndex_mul_relIndex S L I hSL hLI
  rw [h3] at h
  have hd : S.relIndex L ∣ 3 := Dvd.intro _ h
  rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hSL
  · right
    rw [h1] at h
    have : L.relIndex I = 1 := by omega
    exact le_antisymm hLI (Subgroup.relIndex_eq_one.mp this)

omit [Finite G] in
theorem inf_normalizer_eq {I S Iz : Subgroup G} (hmp : MinParabolic I S Iz) (h3 : S.relIndex I = 3) :
    I ⊓ Subgroup.normalizer (S : Set G) = S := by
  have hSle : S ≤ I ⊓ Subgroup.normalizer (S : Set G) := le_inf hmp.isSylow.1 Subgroup.le_normalizer
  rcases eq_or_eq_of_relIndex_three h3 hSle inf_le_left with h | h
  · exact h
  · exact absurd (inf_eq_left.mp h) hmp.not_normal

theorem relIndex_pCore_eq_two_of_index_three {H : Type} [Group H] [Finite H] {P : Subgroup H}
    (hP : IsPGroup 2 P) (hle : CFSG.Open.pCore 2 H ≤ P) (hidx : P.index = 3) (hnorm : ¬ P.Normal) :
    (CFSG.Open.pCore 2 H).relIndex P = 2 := by
  have : P.FiniteIndex := ⟨by rw [hidx]; norm_num⟩
  have hdvd := Subgroup.index_normalCore_dvd_factorial_index P
  rw [hidx] at hdvd
  have hN'p : IsPGroup 2 P.normalCore := hP.to_le (Subgroup.normalCore_le P)
  have hN'P : P.normalCore ≤ CFSG.Open.pCore 2 H :=
    CFSG.LieType.BorelTits.le_pCore 2 inferInstance hN'p
  have h1 : P.normalCore.relIndex P * P.index = P.normalCore.index :=
    Subgroup.relIndex_mul_index (Subgroup.normalCore_le P)
  rw [hidx] at h1
  have hd2 : P.normalCore.relIndex P ∣ 2 := by
    have h36 : Nat.factorial 3 = 2 * 3 := by decide
    have h6 : P.normalCore.relIndex P * 3 ∣ 2 * 3 := by
      rw [h1, ← h36]
      exact hdvd
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h6
  have h2 := Subgroup.relIndex_mul_relIndex P.normalCore (CFSG.Open.pCore 2 H) P hN'P hle
  have hP2 : (CFSG.Open.pCore 2 H).relIndex P ∣ 2 := (Dvd.intro_left _ h2).trans hd2
  have hP1 : (CFSG.Open.pCore 2 H).relIndex P ≠ 1 := by
    intro h
    have hPle : P ≤ CFSG.Open.pCore 2 H := Subgroup.relIndex_eq_one.mp h
    apply hnorm
    have : P = CFSG.Open.pCore 2 H := le_antisymm hPle hle
    rw [this]
    exact CFSG.LieType.BorelTits.pCore_normal 2
  exact ((Nat.dvd_prime Nat.prime_two).mp hP2).resolve_left hP1

theorem relIndex_pCore_eq_two {I S Iz : Subgroup G} (hmp : MinParabolic I S Iz)
    (h3 : S.relIndex I = 3) : (pCoreOf 2 I).relIndex S = 2 := by
  have hSI : S ≤ I := hmp.isSylow.1
  have hP : IsPGroup 2 (S.subgroupOf I) :=
    hmp.isSylow.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hSI).symm
  have hle : CFSG.Open.pCore 2 ↥I ≤ S.subgroupOf I := by
    intro x hx
    have : (x : G) ∈ pCoreOf 2 I := Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow this
  have hnorm : ¬ (S.subgroupOf I).Normal := fun hN =>
    hmp.not_normal ((Subgroup.normal_subgroupOf_iff_le_normalizer hSI).mp hN)
  have key := relIndex_pCore_eq_two_of_index_three hP hle h3 hnorm
  have := Subgroup.relIndex_map_map_of_injective (CFSG.Open.pCore 2 ↥I) (S.subgroupOf I)
    I.subtype_injective
  rw [Subgroup.map_subgroupOf_eq_of_le hSI, key] at this
  exact this

theorem card_le_of_a3_single (hS3 : InputC61S3) {I S Iz : Subgroup G} {K : Fin 1 → Subgroup G}
    {ρ : G} (hsq : IsSQTKTC I) (hchar : CharTwo I) (hmp : MinParabolic I S Iz)
    (hbp : IsBlockProduct I S 1 K) (hnot : ¬ K 0 ≤ Iz) (ha3 : IsAltType (K 0) 3)
    (hρN : ρ ∈ Subgroup.normalizer (S : Set G)) (hρS : ρ ∉ S) (hρ2 : ρ ^ 2 ∈ S)
    (hb : ∀ X : Subgroup G, X ≤ S → X ≠ ⊥ → I ≤ Subgroup.normalizer (X : Set G) →
      (S ⊔ Subgroup.zpowers ρ) ⊓ Subgroup.normalizer (X : Set G) ≤ S) :
    Nat.card S ≤ 2 ^ 9 := by
  have h3 : S.relIndex I = 3 := relIndex_eq_three hmp hbp hnot ha3
  have hSI : S ≤ I := hmp.isSylow.1
  have hTidx : S.relIndex (S ⊔ Subgroup.zpowers ρ) = 2 := relIndex_sup_zpowers hρN hρS hρ2
  have hTp : IsPGroup 2 ↥(S ⊔ Subgroup.zpowers ρ) :=
    isPGroup_of_relIndex_two hmp.isSylow.2.1 le_sup_left hTidx
  have hρT : ρ ∈ S ⊔ Subgroup.zpowers ρ := Subgroup.mem_sup_right (Subgroup.mem_zpowers ρ)
  have hNIS := inf_normalizer_eq hmp h3
  have hTI : (S ⊔ Subgroup.zpowers ρ) ⊓ I = S := by
    refine le_antisymm ?_ (le_inf le_sup_left hSI)
    rintro x ⟨hxT, hxI⟩
    rcases (mem_sup_zpowers_iff hρN hρ2).mp hxT with hx | hx
    · exact hx
    · exfalso
      apply hρS
      have hρI : ρ ∈ I := by
        have : ρ = x * (ρ⁻¹ * x)⁻¹ := by group
        rw [this]
        exact I.mul_mem hxI (I.inv_mem (hSI hx))
      have : ρ ∈ I ⊓ Subgroup.normalizer (S : Set G) := ⟨hρI, hρN⟩
      rwa [hNIS] at this
  have hclaim : ∀ C : Subgroup G, C ≤ S → C ≠ ⊥ →
      S ⊔ Subgroup.zpowers ρ ≤ Subgroup.normalizer (C : Set G) →
      I ⊓ Subgroup.normalizer (C : Set G) ≤ S := by
    intro C hCS hC0 hTC
    have hSL : S ≤ I ⊓ Subgroup.normalizer (C : Set G) := le_inf hSI (le_sup_left.trans hTC)
    rcases eq_or_eq_of_relIndex_three h3 hSL inf_le_left with h | h
    · exact h.le
    · exfalso
      have hIC : I ≤ Subgroup.normalizer (C : Set G) := inf_eq_left.mp h
      exact hρS (hb C hCS hC0 hIC ⟨hρT, hTC hρT⟩)
  have hQ := relIndex_pCore_eq_two hmp h3
  obtain ⟨-, hcard⟩ := hS3 G I (S ⊔ Subgroup.zpowers ρ) S hsq hchar hmp.isSylow hTp le_sup_left
    hTidx hTI hclaim hQ
  have hQS : pCoreOf 2 I ≤ S := B6.pCoreOf_two_le_of_isSylowTwoOf hmp.isSylow
  have h1 := Subgroup.relIndex_mul_card (pCoreOf 2 I) S
  rw [inf_eq_left.mpr hQS, hQ] at h1
  have h16 : Nat.card S ≤ 16 := by omega
  calc Nat.card S ≤ 16 := h16
    _ ≤ 2 ^ 9 := by norm_num

end S153U

@[expose] def Input1469C61Big : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I S Iz : Subgroup G) (r : ℕ) (K : Fin r → Subgroup G) (ρ : G),
    IsSQTKTC I → CharTwo I → MinParabolic I S Iz → IsBlockProduct I S r K →
    (∀ i, ¬ K i ≤ Iz) → (∀ i, IsAltType (K i) 3 ∨ IsAltType (K i) 5) →
    ¬ (r = 2 ∧ ∀ i, IsAltType (K i) 5) → ¬ (r = 1 ∧ ∀ i, IsAltType (K i) 3) →
    ρ ∈ Subgroup.normalizer (S : Set G) → ρ ∉ S → ρ ^ 2 ∈ S →
    (∀ X : Subgroup G, X ≤ S → X ≠ ⊥ → I ≤ Subgroup.normalizer (X : Set G) →
      (S ⊔ Subgroup.zpowers ρ) ⊓ Subgroup.normalizer (X : Set G) ≤ S) →
    Nat.card S ≤ 2 ^ 9

theorem input1469C61_of_s3 (hS3 : InputC61S3) (hBig : Input1469C61Big) : Input1469C61 := by
  intro G _ _ I S Iz r K ρ hsq hchar hmp hbp hnot hAlt hnot2 hρN hρS hρ2 hb
  by_cases h : r = 1 ∧ ∀ i, IsAltType (K i) 3
  · obtain ⟨rfl, h3⟩ := h
    exact S153U.card_le_of_a3_single hS3 hsq hchar hmp hbp (hnot 0) (h3 0) hρN hρS hρ2 hb
  · exact hBig G I S Iz r K ρ hsq hchar hmp hbp hnot hAlt hnot2 h hρN hρS hρ2 hb

end CFSG.Quasithin
