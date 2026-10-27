module

public import CFSG.Quasithin.Vol2.E2SevenKG
public import CFSG.StronglyEmbedded.BenderUnitaryBorel
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel
public import CFSG.Adapters.LinearFieldTransport
public import CFSG.LieType.BorelTits.Suzuki

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique B6

namespace E2

theorem exists_fusionBenderBorel_of_isBenderOf {X : Type} [Group X] [Finite X] {n : ℕ}
    (h : IsBenderOf n X) : ∃ k, fusionBenderBorel X (2 ^ n) k := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hn, h | h | h⟩ := h
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    let e' := e.trans (CFSG.ClassicalModels.statedLinearModelEquivGaloisPSL F 2 2 n (by omega) hF)
    have : Finite (Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 n)) :=
      Finite.of_equiv X e'.toEquiv
    exact ⟨1, (bender_psl2_borel_full n hn).map_mulEquiv e'.symm⟩
  · obtain ⟨-, a, ha, F, _, _, rfl, hcard, ⟨e⟩⟩ := h
    let e' : X ≃* ↥(Sz a) := e.trans ((MulEquiv.subgroupCongr
      (CFSG.LieType.BorelTits.suzukiGroup_eq_glaSzGroup a F)).trans
      (CFSG.ShultStronglyClosedTI.glaSzEquivNative a ha hcard))
    have : Finite ↥(Sz a) := Finite.of_equiv X e'.toEquiv
    exact ⟨2, (bender_suzuki_borel_full a ha).map_mulEquiv e'.symm⟩
  · obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := h
    have hcard : Nat.card F = 2 ^ (2 * n) := by rw [hF, ← pow_mul, mul_comm]
    let e' : X ≃* CFSG.Open.GLAProj (CFSG.Open.GLASUGroup (Fin 3) F (2 ^ n)) := e
    let e'' := e'.trans (CFSG.ShultStronglyClosedTI.glaSU3EquivNative n hn hcard)
    have : Finite ↥(PSU3 2 n) := Finite.of_equiv X e''.toEquiv
    exact ⟨3, (bender_psu3_borel_full n hn).map_mulEquiv e''.symm⟩

theorem sylow_inf_smul_eq_bot {X : Type} [Group X] [Finite X] {q k : ℕ}
    (hB : fusionBenderBorel X q k) (P : Sylow 2 X) {y : X}
    (hy : y ∉ Subgroup.normalizer ((P : Subgroup X) : Set X)) :
    (P : Subgroup X) ⊓ ((y • P : Sylow 2 X) : Subgroup X) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hSE, -⟩ := hB P
  set N := Subgroup.normalizer ((P : Subgroup X) : Set X) with hN
  have hy' : y⁻¹ ∉ N := fun h => hy (by simpa using N.inv_mem h)
  have hodd := hSE.2.2 y⁻¹ hy'
  rw [inv_inv] at hodd
  have hconj : ((y • P : Sylow 2 X) : Subgroup X) =
      (P : Subgroup X).map (MulAut.conj y).toMonoidHom := by
    rw [Sylow.coe_subgroup_smul]
    rfl
  have hle : (P : Subgroup X) ⊓ ((y • P : Sylow 2 X) : Subgroup X) ≤
      N ⊓ N.map (MulAut.conj y).toMonoidHom := by
    refine inf_le_inf Subgroup.le_normalizer ?_
    rw [hconj, hN, Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.le_normalizer
  have h2 : IsPGroup 2 ↥((P : Subgroup X) ⊓ ((y • P : Sylow 2 X) : Subgroup X)) :=
    P.isPGroup'.to_le inf_le_left
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  have hodd' := hodd.of_dvd_nat (Subgroup.card_dvd_of_le hle)
  rw [hm] at hodd'
  have hm0 : m = 0 := by
    by_contra hm0
    exact (Nat.not_even_iff_odd.mpr hodd') (Nat.even_pow.mpr ⟨even_two, hm0⟩)
  rw [hm0, pow_zero, Subgroup.card_eq_one] at hm
  exact hm

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isSylowTwoOf_of_inf_ne_bot {K S S' : Subgroup G} {q k : ℕ}
    (hB : fusionBenderBorel ↥K q k) (hS : IsSylowTwoOf S K) (hS' : IsSylowTwoOf S' K)
    (h : S ⊓ S' ≠ ⊥) : S = S' := by
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq ↥K (toSylow2 hS) (toSylow2 hS')
  by_cases hyN : y ∈ Subgroup.normalizer (((toSylow2 hS) : Subgroup ↥K) : Set ↥K)
  · have h1 := Sylow.smul_eq_iff_mem_normalizer.mpr hyN
    rw [hy] at h1
    have h2 := congrArg (fun P : Sylow 2 ↥K => (P : Subgroup ↥K)) h1
    simp only [toSylow2_coe] at h2
    rw [Subgroup.subgroupOf_inj, inf_of_le_left hS.1, inf_of_le_left hS'.1] at h2
    exact h2.symm
  · exfalso
    apply h
    have h0 := sylow_inf_smul_eq_bot hB (toSylow2 hS) hyN
    rw [hy, toSylow2_coe, toSylow2_coe] at h0
    rw [eq_bot_iff]
    intro x hx
    have hxK : x ∈ K := hS.1 hx.1
    have : (⟨x, hxK⟩ : ↥K) ∈ S.subgroupOf K ⊓ S'.subgroupOf K :=
      ⟨Subgroup.mem_subgroupOf.mpr hx.1, Subgroup.mem_subgroupOf.mpr hx.2⟩
    rw [h0, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val this)

theorem le_of_le_normalizer_of_isSylowTwoOf {K S Q : Subgroup G} (hS : IsSylowTwoOf S K)
    (hQ : IsPGroup 2 Q) (hQK : Q ≤ K) (hQN : Q ≤ Subgroup.normalizer (S : Set G)) : Q ≤ S := by
  have h2 := IsPGroup.to_sup_of_normal_right' hQ hS.2.1 hQN
  exact le_sup_left.trans
    ((A4.isSylowTwoOf_iff_maximal.mp hS).2.2 _ (sup_le hQK hS.1) h2 le_sup_right)

omit [Finite G] in
private theorem mem_normalizer_inf_of_mem' {A B : Subgroup G} {x : G}
    (hA : x ∈ Subgroup.normalizer (A : Set G)) (hB : x ∈ Subgroup.normalizer (B : Set G)) :
    x ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff] at hA hB ⊢
  intro z
  exact and_congr (hA z) (hB z)

omit [Finite G] in
private theorem conjSub_le_of_mem {K X : Subgroup G} {g : G} (hg : g ∈ K) (hX : X ≤ K) :
    conjSub g X ≤ K := by
  intro x hx
  rw [mem_conjSub] at hx
  have := K.mul_mem (K.mul_mem hg (hX hx)) (K.inv_mem hg)
  simpa [mul_assoc] using this

theorem exists_member_of_bender {K S V : Subgroup G} {n : ℕ} (hBen : IsBenderOf n ↥K)
    (hS : IsSylowTwoOf S K) (hVS : V ≤ S) (hV4 : 4 ≤ Nat.card V) {g₀ : G} (hg₀K : g₀ ∈ K)
    (hg₀N : g₀ ∉ Subgroup.normalizer (S : Set G))
    (hb : ∀ g ∈ K, g ∉ Subgroup.normalizer (S : Set G) → ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧
      (IsPSL 2 2 k ↥(V ⊔ conjSub g V) ∨ IsSz k ↥(V ⊔ conjSub g V))) :
    ∃ g ∈ K, g ∉ Subgroup.normalizer (S : Set G) ∧
      IsSylowTwoOf (S ⊓ (V ⊔ conjSub g V)) (V ⊔ conjSub g V) ∧
      (∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧ (IsPSL 2 2 k ↥(V ⊔ conjSub g V) ∨ IsSz k ↥(V ⊔ conjSub g V))) ∧
      K ⊓ Subgroup.normalizer (S : Set G) ⊓ (V ⊔ conjSub g V) =
        (V ⊔ conjSub g V) ⊓
          Subgroup.normalizer ((S ⊓ (V ⊔ conjSub g V) : Subgroup G) : Set G) ∧
      ∃ h ∈ V ⊔ conjSub g V, V ⊔ conjSub g V = V ⊔ conjSub h V := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k₀, hB⟩ := exists_fusionBenderBorel_of_isBenderOf hBen
  have hTI := fun {S₁ S₂ : Subgroup G} => @eq_of_isSylowTwoOf_of_inf_ne_bot G _ _ K S₁ S₂ _ _ hB
  have hVK : V ≤ K := hVS.trans hS.1
  have hV2 : IsPGroup 2 V := hS.2.1.to_le hVS
  have hV1 : V ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hV4
    omega
  have hSyl : ∀ S' : Subgroup G, IsSylowTwoOf S' K → V ≤ S' → S' = S := fun S' hS' hVS' =>
    (hTI hS hS' fun h0 => hV1 (le_bot_iff.mp (h0 ▸ le_inf hVS hVS'))).symm
  have hF0 : ∀ g ∈ K, g ∉ Subgroup.normalizer (S : Set G) →
      ¬ conjSub g V ≤ Subgroup.normalizer (S : Set G) := by
    intro g hgK hgN hle
    have hVg2 : IsPGroup 2 ↥(conjSub g V) := hV2.of_equiv
      (Subgroup.equivMapOfInjective V (MulAut.conj g).toMonoidHom (MulAut.conj g).injective)
    have h1 := le_of_le_normalizer_of_isSylowTwoOf hS hVg2 (conjSub_le_of_mem hgK hVK) hle
    have hSg : IsSylowTwoOf (conjSub g S) K := by
      have := isSylowTwoOf_conjSub hS g
      rwa [conjSub_eq_self (Subgroup.le_normalizer hgK)] at this
    have hVg1 : conjSub g V ≠ ⊥ := fun h0 => hV1 (by
      rw [eq_bot_iff] at h0 ⊢
      intro x hx
      have := h0 (show g * x * g⁻¹ ∈ conjSub g V by rw [mem_conjSub]; simpa [mul_assoc] using hx)
      rw [Subgroup.mem_bot] at this ⊢
      have := congrArg (fun w => g⁻¹ * w * g) this
      simpa [mul_assoc] using this)
    have hSS : S = conjSub g S := hTI hS hSg fun h0 => hVg1 (le_bot_iff.mp
      (h0 ▸ le_inf h1 ((conjSub g).monotone hVS)))
    apply hgN
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have : g * z * g⁻¹ ∈ conjSub g S := by rw [mem_conjSub]; simpa [mul_assoc] using hz
      rwa [← hSS] at this
    · intro hz
      rw [hSS, mem_conjSub] at hz
      simpa [mul_assoc] using hz
  set s : Set G := {g | g ∈ K ∧ g ∉ Subgroup.normalizer (S : Set G)} with hs
  obtain ⟨g₁, ⟨hg₁K, hg₁N⟩, hmin⟩ := Set.exists_min_image s
    (fun g => Nat.card ↥(V ⊔ conjSub g V)) (Set.toFinite s) ⟨g₀, hg₀K, hg₀N⟩
  set I₁ := V ⊔ conjSub g₁ V with hI₁
  have hI₁K : I₁ ≤ K := sup_le hVK (conjSub_le_of_mem hg₁K hVK)
  obtain ⟨h, hhI, hhN⟩ : ∃ h ∈ I₁, h ∉ Subgroup.normalizer (S : Set G) := by
    by_contra hall
    push Not at hall
    exact hF0 g₁ hg₁K hg₁N (le_sup_right.trans hall)
  have hhK : h ∈ K := hI₁K hhI
  have hle : V ⊔ conjSub h V ≤ I₁ := sup_le le_sup_left (by
    intro x hx
    rw [mem_conjSub] at hx
    have := I₁.mul_mem (I₁.mul_mem hhI (le_sup_left (a := V) hx)) (I₁.inv_mem hhI)
    simpa [mul_assoc] using this)
  have heq : V ⊔ conjSub h V = I₁ :=
    Subgroup.eq_of_le_of_card_ge hle (hmin h ⟨hhK, hhN⟩)
  set I := V ⊔ conjSub h V with hIdef
  have hIK : I ≤ K := hle.trans hI₁K
  refine ⟨h, hhK, hhN, ?_, hb h hhK hhN, ?_, h, show h ∈ I from heq ▸ hhI, rfl⟩
  ·
    refine A4.isSylowTwoOf_iff_maximal.mpr ⟨inf_le_right, hS.2.1.to_le inf_le_left, ?_⟩
    intro P hPI hP2 hSP
    obtain ⟨S'', hS'', hPS''⟩ := exists_isSylowTwoOf_ge hP2 (hPI.trans hIK)
    have := hSyl S'' hS'' ((le_inf hVS le_sup_left).trans (hSP.trans hPS''))
    rw [this] at hPS''
    exact le_inf hPS'' hPI
  ·
    apply le_antisymm
    · rintro x ⟨⟨-, hxN⟩, hxI⟩
      exact ⟨hxI, mem_normalizer_inf_of_mem' hxN (Subgroup.le_normalizer hxI)⟩
    · rintro x ⟨hxI, hxN⟩
      have hxK := hIK hxI
      refine ⟨⟨hxK, ?_⟩, hxI⟩
      have hSx : IsSylowTwoOf (conjSub x S) K := by
        have := isSylowTwoOf_conjSub hS x
        rwa [conjSub_eq_self (Subgroup.le_normalizer hxK)] at this
      have hVx : V ≤ conjSub x S := by
        intro v hv
        have hvSI : v ∈ S ⊓ I := ⟨hVS hv, le_sup_left (a := V) hv⟩
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) v).mp hvSI
        rw [mem_conjSub]
        simpa using this.1
      have hSS := hSyl _ hSx hVx
      show x ∈ Subgroup.normalizer (S : Set G)
      rw [Subgroup.mem_normalizer_iff]
      intro z
      constructor
      · intro hz
        have : x * z * x⁻¹ ∈ conjSub x S := by rw [mem_conjSub]; simpa [mul_assoc] using hz
        rwa [hSS] at this
      · intro hz
        rw [← hSS, mem_conjSub] at hz
        simpa [mul_assoc] using hz

theorem kgBenderSub_b_of_parts (hL2 : KGBenderSubL2) (hSz : KGBenderSubSz) (hU3 : KGBenderSubU3)
    {K S V : Subgroup G} {n : ℕ} (hBen : IsBenderOf n ↥K) (hS : IsSylowTwoOf S K) (hVS : V ≤ S)
    (hVC : V ≤ Subgroup.centralizer (S : Set G)) (hV : IsElemAbelian 2 V) (hV4 : 4 ≤ Nat.card V) :
    ∀ g ∈ K, g ∉ Subgroup.normalizer (S : Set G) → ∃ k : ℕ, 2 ≤ k ∧ k ∣ n ∧
      (IsPSL 2 2 k ↥(V ⊔ conjSub g V) ∨ IsSz k ↥(V ⊔ conjSub g V)) := by
  intro g hgK hgN
  obtain ⟨hn, hK | hK | hK⟩ := hBen
  · exact hL2 G K S V n g hn hK hS hVS hVC hV hV4 hgK hgN
  · exact hSz G K S V n g hn hK hS hVS hVC hV hV4 hgK hgN
  · exact hU3 G K S V n g hn hK hS hVS hVC hV hV4 hgK hgN

end E2

end CFSG.Quasithin
