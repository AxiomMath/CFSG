module

public import CFSG.RankThree.PartTwo.Sec15.Item153Push2ProofTools
import CFSG.RankThree.PartTwo.Sec15.Item155Proof
public import CFSG.RankThree.PartTwo.Sec15.Item153PushProof
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating

public section

namespace CFSG.RankThree.PartTwo.Sec15.Push153B

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo Equiv

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_normalizer_range {M : Subgroup G} {K : Type*} [Group K] (ψ : ↥M →* K)
    {S : Subgroup G} (hSM : S ≤ M) {a : ↥M} (ha : (a : G) ∈ Subgroup.normalizer (S : Set G)) :
    ψ a ∈ Subgroup.normalizer ((ψ.comp (Subgroup.inclusion hSM)).range : Set K) := by
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · rintro ⟨s, rfl⟩
    have hs : (a : G) * s * (a : G)⁻¹ ∈ S :=
      (Subgroup.mem_normalizer_iff.mp ha s).mp s.2
    refine ⟨⟨_, hs⟩, ?_⟩
    have e : Subgroup.inclusion hSM ⟨_, hs⟩ = a * Subgroup.inclusion hSM s * a⁻¹ :=
      Subtype.ext rfl
    simp only [MonoidHom.comp_apply, e, map_mul, map_inv]
  · rintro ⟨s, hs⟩
    have hs' : (a : G)⁻¹ * s * (a : G) ∈ S := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) s).mp s.2
      simpa using this
    refine ⟨⟨_, hs'⟩, ?_⟩
    have e : Subgroup.inclusion hSM ⟨_, hs'⟩ = a⁻¹ * Subgroup.inclusion hSM s * a :=
      Subtype.ext rfl
    simp only [MonoidHom.comp_apply] at hs
    simp only [MonoidHom.comp_apply, e, map_mul, map_inv, hs]
    group

omit [Finite G] in
theorem isPGroup_range {p : ℕ} {M : Subgroup G} {K : Type*} [Group K] (ψ : ↥M →* K)
    {S : Subgroup G} (hSM : S ≤ M) (hS : IsPGroup p S) :
    IsPGroup p (ψ.comp (Subgroup.inclusion hSM)).range := by
  rintro ⟨_, s, rfl⟩
  obtain ⟨k, hk⟩ := hS s
  refine ⟨k, Subtype.ext ?_⟩
  simp only [Subgroup.coe_pow, Subgroup.coe_one, ← map_pow, hk, map_one]

omit [Finite G] in
theorem mem_normalizer_map {H : Subgroup G} {Q : Subgroup ↥H} {a : ↥H}
    (ha : a ∈ Subgroup.normalizer (Q : Set ↥H)) :
    (a : G) ∈ Subgroup.normalizer ((Q.map H.subtype : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    exact ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha x).mp hx, rfl⟩
  · rintro ⟨x, hx, hxg⟩
    have hx' : a⁻¹ * x * a ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem ha) x).mp hx
      simpa using this
    refine ⟨a⁻¹ * x * a, hx', ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hxg ⊢
    rw [hxg]
    group

section Alt

variable {n : ℕ} {A Y S : Subgroup G}

theorem mem_pCoreOf_of_permAct_eq_one (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin n))
    (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))
    (hautE : ∀ σ, autE σ = MulAut.conjNormal σ) (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) {h : G} (hh : h ∈ Y ⊔ S)
    (h1 : permAct φ autE ⟨h, sup_le Subgroup.le_normalizer hSY hh⟩ = 1) :
    h ∈ CFSG.Open.pCoreOf 2 (Y ⊔ S) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := Y ⊔ S with hHdef
  have hHN : H ≤ Subgroup.normalizer (Y : Set G) := sup_le Subgroup.le_normalizer hSY
  set f := (permAct φ autE).comp (Subgroup.inclusion hHN) with hf
  set K : Subgroup G := f.ker.map H.subtype with hK
  have hhK : h ∈ K := ⟨⟨h, hh⟩, show f ⟨h, hh⟩ = 1 from h1, rfl⟩
  have hKH : K ≤ H := Subgroup.map_subtype_le _
  have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
    Sec15.le_normalizer_map_of_normal155 (MonoidHom.normal_ker f)
  have hK2 : IsPGroup 2 K := by
    rintro ⟨_, x, hx, rfl⟩
    obtain ⟨a, ha⟩ := Push153.exists_pow_two_mem_of_sup hS2 hSY x.2
    have hxa : permAct φ autE ⟨(x : G) ^ 2 ^ a, Subgroup.le_normalizer ha⟩ = 1 := by
      have e : (⟨(x : G) ^ 2 ^ a, Subgroup.le_normalizer ha⟩ :
          ↥(Subgroup.normalizer (Y : Set G))) = (Subgroup.inclusion hHN x) ^ 2 ^ a :=
        Subtype.ext (by simp)
      have hx' : f x = 1 := hx
      rw [hf, MonoidHom.comp_apply] at hx'
      rw [e, map_pow, hx', one_pow]
    have hV := (permAct_eq_one_iff φ autE hautE _ ha).mp hxa
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y ⟨_, hV⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((x : G) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    simp only [Subgroup.coe_pow, Subgroup.coe_subtype, Subgroup.coe_one, pow_add, pow_mul]
    exact hb'
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hKH hHK hK2 hhK

theorem exists_mem_inf_permAct_eq (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin n))
    (autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)))
    (hautE : ∀ σ, autE σ = MulAut.conjNormal σ) (hAF : A ∈ partTwoF G)
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {z : Perm (Fin n)} (hz3 : z ^ 3 = 1)
    (hzA : ∀ (a : G) (ha : a ∈ A),
      permAct φ autE ⟨a, hAY ha⟩ * z = z * permAct φ autE ⟨a, hAY ha⟩) :
    ∃ (a₀ : G) (ha₀ : a₀ ∈ A ⊓ Y), permAct φ autE ⟨a₀, Subgroup.le_normalizer ha₀.2⟩ = z := by
  have hzA_n : z ∈ alternatingGroup (Fin n) := by
    rw [Equiv.Perm.mem_alternatingGroup]
    have h := congrArg Equiv.Perm.sign hz3
    rw [map_pow, map_one] at h
    rcases Int.units_eq_one_or (Equiv.Perm.sign z) with h1 | h1
    · exact h1
    · rw [h1] at h
      exact absurd h (by decide)
  obtain ⟨y, hy, hψy⟩ := exists_permAct_eq φ autE hautE hzA_n
  have hVfix : ∀ a ∈ A, a * y * a⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 Y := by
    intro a ha
    have hmem : a * y * a⁻¹ * y⁻¹ ∈ Y := by
      refine Y.mul_mem ?_ (Y.inv_mem hy)
      exact (Subgroup.mem_normalizer_iff.mp (hAY ha) y).mp hy
    refine (permAct_eq_one_iff φ autE hautE _ hmem).mp ?_
    have e : (⟨a * y * a⁻¹ * y⁻¹, Subgroup.le_normalizer hmem⟩ :
        ↥(Subgroup.normalizer (Y : Set G))) =
        ⟨a, hAY ha⟩ * ⟨y, Subgroup.le_normalizer hy⟩ * ⟨a, hAY ha⟩⁻¹ *
          ⟨y, Subgroup.le_normalizer hy⟩⁻¹ := Subtype.ext rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv, hψy, hzA a ha]
    group
  have hy3 : y ^ 3 ∈ CFSG.Open.pCoreOf 2 Y := by
    refine (permAct_eq_one_iff φ autE hautE _ (Y.pow_mem hy 3)).mp ?_
    have e : (⟨y ^ 3, Subgroup.le_normalizer (Y.pow_mem hy 3)⟩ :
        ↥(Subgroup.normalizer (Y : Set G))) = ⟨y, Subgroup.le_normalizer hy⟩ ^ 3 :=
      Subtype.ext (by simp)
    rw [e, map_pow, hψy, hz3]
  obtain ⟨a₀, ha₀, hV⟩ := exists_mem_inf_of_fixed hAF hAY hy hVfix hy3
  refine ⟨a₀, ha₀, ?_⟩
  have hmem : a₀ * y⁻¹ ∈ Y := Y.mul_mem ha₀.2 (Y.inv_mem hy)
  have h1 := (permAct_eq_one_iff φ autE hautE _ hmem).mpr hV
  have e : (⟨a₀ * y⁻¹, Subgroup.le_normalizer hmem⟩ : ↥(Subgroup.normalizer (Y : Set G))) =
      ⟨a₀, Subgroup.le_normalizer ha₀.2⟩ * ⟨y, Subgroup.le_normalizer hy⟩⁻¹ := Subtype.ext rfl
  rw [e, map_mul, map_inv, hψy, mul_inv_eq_one] at h1
  exact h1

theorem invA315_of_alt (hn5 : 5 ≤ n) (hn6 : n ≠ 6)
    (hlat : ∀ P : Sylow 3 (Perm (Fin n)), ∀ Q₁ Q₂ : Subgroup (Perm (Fin n)), IsPGroup 2 Q₂ →
      Q₁ ≤ Q₂ → Q₁ ≠ ⊥ → (P : Subgroup (Perm (Fin n))) ≤ Subgroup.normalizer (Q₁ : Set _) →
      (P : Subgroup (Perm (Fin n))) ≤ Subgroup.normalizer (Q₂ : Set _) → Q₂ ≤ Q₁)
    (hcomm : ∀ P : Sylow 3 (Perm (Fin n)), ∀ x ∈ P, ∀ y ∈ P, x * y = y * x)
    (hpow : ∀ P : Sylow 3 (Perm (Fin n)), ∀ x ∈ P, x ^ 3 = 1)
    (hAF : A ∈ partTwoF G) (hAY : A ≤ Subgroup.normalizer (Y : Set G))
    (hAS : A ≤ Subgroup.normalizer (S : Set G)) (hS2 : IsPGroup 2 S)
    (hSY : S ≤ Subgroup.normalizer (Y : Set G)) (hO : CFSG.Open.pCoreOf 2 (Y ⊔ S) ≤ S)
    (hY2 : CFSG.Open.pCoreOf 2 Y ≠ ⊥) (hno : ¬ CharNormal153 Y S)
    (φ : ↥Y ⧸ CFSG.pCore 2 ↥Y ≃* alternatingGroup (Fin n)) : InvA315 (Y ⊔ S) S := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Y ⊔ S with hHdef
  set Nr := Subgroup.normalizer (Y : Set G) with hNr
  have hHN : H ≤ Nr := sup_le Subgroup.le_normalizer hSY
  have hSN : S ≤ Nr := hSY
  let autE : Perm (Fin n) ≃* MulAut (alternatingGroup (Fin n)) :=
    MulEquiv.ofBijective MulAut.conjNormal
      (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn5 hn6)
  have hautE : ∀ σ, autE σ = MulAut.conjNormal σ := fun σ => rfl
  set ψ := permAct φ autE with hψ
  have hA3 : ∀ a ∈ A, a ^ 3 = 1 := hAF.1.2
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hAF.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hinj3 : ∀ (x : G) (hx : x ∈ Y), x ^ 3 = 1 → ψ ⟨x, Subgroup.le_normalizer hx⟩ = 1 →
      x = 1 := by
    intro x hx hx3 h1
    have hV := (permAct_eq_one_iff φ autE hautE x hx).mp h1
    obtain ⟨b, hb⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y ⟨x, hV⟩
    have hb' : x ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have h1' : orderOf x ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb'
    have h3' : orderOf x ∣ 3 := orderOf_dvd_of_pow_eq_one hx3
    have hco : Nat.Coprime (2 ^ b) 3 := Nat.Coprime.pow_left b (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hco h1' h3')
  have hcard3 : ∀ E : Subgroup G, ∀ hEY : E ≤ Y, (∀ x ∈ E, x ^ 3 = 1) →
      Nat.card (ψ.comp (Subgroup.inclusion (hEY.trans Subgroup.le_normalizer))).range =
        Nat.card E := by
    intro E hEY hE3
    have hinj : Function.Injective (ψ.comp (Subgroup.inclusion (hEY.trans
        Subgroup.le_normalizer))) := by
      rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
      intro x hx
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at hx
      rw [Subgroup.mem_bot]
      exact Subtype.ext (hinj3 x (hEY x.2) (hE3 x x.2) hx)
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  set ψA := (ψ.comp (Subgroup.inclusion hAY)).range with hψA
  have hψA3 : IsPGroup 3 ψA :=
    isPGroup_range ψ hAY (fun a => ⟨1, Subtype.ext (by simpa using hA3 a a.2)⟩)
  obtain ⟨P, hψAP⟩ := hψA3.exists_le_sylow
  have hψaP : ∀ (a : G) (ha : a ∈ A), ψ ⟨a, hAY ha⟩ ∈ P := fun a ha =>
    hψAP ⟨⟨a, ha⟩, rfl⟩
  have hlift : ∀ z ∈ P, ∃ (a₀ : G) (ha₀ : a₀ ∈ A ⊓ Y),
      ψ ⟨a₀, Subgroup.le_normalizer ha₀.2⟩ = z := by
    intro z hz
    exact exists_mem_inf_permAct_eq φ autE hautE hAF hAY (hpow P z hz)
      (fun a ha => hcomm P _ (hψaP a ha) z hz)
  set AY := A ⊓ Y with hAYdef
  have hAYY : AY ≤ Y := inf_le_right
  have hAY3 : ∀ x ∈ AY, x ^ 3 = 1 := fun x hx => hA3 x hx.1
  have hψAY : (ψ.comp (Subgroup.inclusion (hAYY.trans Subgroup.le_normalizer))).range =
      (P : Subgroup (Perm (Fin n))) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      exact hψaP x x.2.1
    · intro z hz
      obtain ⟨a₀, ha₀, hza⟩ := hlift z hz
      exact ⟨⟨a₀, ha₀⟩, hza⟩
  have hcardAY : Nat.card AY = Nat.card (P : Subgroup (Perm (Fin n))) := by
    rw [← hcard3 AY hAYY hAY3, hψAY]
  have hAYH : AY ≤ H := hAYY.trans le_sup_left
  refine ⟨AY.subgroupOf H, ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext
    (hAcomm _ (Subgroup.mem_subgroupOf.mp x.2).1 _ (Subgroup.mem_subgroupOf.mp y.2).1))⟩⟩,
    fun x hx => Subtype.ext (hA3 _ (Subgroup.mem_subgroupOf.mp hx).1)⟩, ?_, ?_⟩
  ·
    intro B hB hAB
    set B' := B.map H.subtype with hB'
    have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
      rintro _ ⟨x, hx, rfl⟩
      simpa using congrArg Subtype.val (hB.2 x hx)
    have hB'Y : B' ≤ Y := fun x hx => by
      obtain ⟨x', hx', rfl⟩ := hx
      exact mem_of_pow_three_of_mem_sup hS2 hSY x'.2 (j := 1) (by
        simpa using hB'3 _ ⟨x', hx', rfl⟩)
    have hAYB' : AY ≤ B' := by
      intro x hx
      exact ⟨⟨x, hAYH hx⟩, hAB (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    set ψB := (ψ.comp (Subgroup.inclusion (hB'Y.trans Subgroup.le_normalizer))).range
    have hψB3 : IsPGroup 3 ψB := isPGroup_range ψ _
      (fun b => ⟨1, Subtype.ext (by simpa using hB'3 b b.2)⟩)
    obtain ⟨P', hP'⟩ := hψB3.exists_le_sylow
    have hcardB : Nat.card B' ≤ Nat.card AY := by
      rw [← hcard3 B' hB'Y hB'3, hcardAY, Sylow.card_eq_multiplicity,
        ← Sylow.card_eq_multiplicity P']
      exact Subgroup.card_le_of_le hP'
    have heq : AY = B' := Subgroup.eq_of_le_of_card_ge hAYB' hcardB
    have : B = B'.subgroupOf H := by
      rw [hB', Subgroup.subgroupOf, Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    rw [this, ← heq]
  ·
    have hSH : S ≤ H := le_sup_right
    have hker : ∀ (h : G) (hh : h ∈ H), ψ ⟨h, hHN hh⟩ = 1 → h ∈ S := fun h hh h1 =>
      hO (mem_pCoreOf_of_permAct_eq_one φ autE hautE hS2 hSY hh h1)
    set Q₁ := (ψ.comp (Subgroup.inclusion hSN)).range with hQ₁
    have hQ₁ : Q₁ ≠ ⊥ := by
      intro h0
      have hSO : S ≤ CFSG.Open.pCoreOf 2 H := by
        intro s hs
        have h1 : ψ ⟨s, hSN hs⟩ = 1 := by
          have : ψ ⟨s, hSN hs⟩ ∈ Q₁ := ⟨⟨s, hs⟩, rfl⟩
          rw [h0] at this
          exact (Subgroup.mem_bot).mp this
        exact mem_pCoreOf_of_permAct_eq_one φ autE hautE hS2 hSY (hSH hs) h1
      have hSeq : S = CFSG.Open.pCoreOf 2 H := le_antisymm hSO hO
      apply hno
      have hYO : CFSG.Open.pCoreOf 2 Y ≤ CFSG.Open.pCoreOf 2 H :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
          ((CFSG.LieType.BorelTits.pCoreOf_le 2 Y).trans le_sup_left)
          (hHN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y))
          (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y)
      refine ⟨S, fun hS0 => hY2 (le_bot_iff.mp (hS0 ▸ hYO.trans hSeq.ge)), le_rfl, ?_, ?_⟩
      · rw [Subgroup.subgroupOf_self]
        infer_instance
      · have h := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
        rwa [← hSeq] at h
    refine ⟨⟨le_top, (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (hS2.comap_of_injective H.subtype H.subtype_injective), ?_⟩, ?_⟩
    ·
      intro a ha
      rw [Subgroup.mem_normalizer_iff]
      intro x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
      simpa using Subgroup.mem_normalizer_iff.mp (hAS (Subgroup.mem_subgroupOf.mp ha).1) x
    · intro Q hQ hSQ
      set P' := Q.map H.subtype with hP'
      have hP'H : P' ≤ H := Subgroup.map_subtype_le Q
      have hP'N : P' ≤ Nr := hP'H.trans hHN
      have hP'2 : IsPGroup 2 P' :=
        ((isPiSubgroup_piOf_iff Nat.prime_two Q).mp hQ.2.1).map H.subtype
      have hSP' : S ≤ P' := fun s hs =>
        ⟨⟨s, hSH hs⟩, hSQ (Subgroup.mem_subgroupOf.mpr hs), rfl⟩
      have hAYP' : ∀ a ∈ AY, a ∈ Subgroup.normalizer (P' : Set G) := fun a ha =>
        mem_normalizer_map (H := H) (a := ⟨a, hAYH ha⟩)
          (hQ.2.2 (Subgroup.mem_subgroupOf.mpr ha))
      set Q₂ := (ψ.comp (Subgroup.inclusion hP'N)).range with hQ₂
      have hQ₁₂ : Q₁ ≤ Q₂ := by
        rintro _ ⟨s, rfl⟩
        exact ⟨⟨s, hSP' s.2⟩, rfl⟩
      have hPn : ∀ {T : Subgroup G} (hTN : T ≤ Nr), (∀ a ∈ AY,
          a ∈ Subgroup.normalizer (T : Set G)) → (P : Subgroup (Perm (Fin n))) ≤
            Subgroup.normalizer ((ψ.comp (Subgroup.inclusion hTN)).range : Set (Perm (Fin n))) := by
        intro T hTN hT z hz
        obtain ⟨a₀, ha₀, rfl⟩ := hlift z hz
        exact mem_normalizer_range ψ hTN (hT a₀ ha₀)
      have hle := hlat P Q₁ Q₂ (isPGroup_range ψ hP'N hP'2) hQ₁₂ hQ₁
        (hPn hSN (fun a ha => hAS ha.1)) (hPn hP'N hAYP')
      have hP'S : P' ≤ S := by
        intro p hp
        obtain ⟨s, hs⟩ := hle ⟨⟨p, hp⟩, rfl⟩
        have hsp : (s : G)⁻¹ * p ∈ H := H.mul_mem (H.inv_mem (hSH s.2)) (hP'H hp)
        have h1 : ψ ⟨(s : G)⁻¹ * p, hHN hsp⟩ = 1 := by
          have e : (⟨(s : G)⁻¹ * p, hHN hsp⟩ : ↥Nr) =
              (Subgroup.inclusion hSN s)⁻¹ * Subgroup.inclusion hP'N ⟨p, hp⟩ := Subtype.ext rfl
          simp only [MonoidHom.comp_apply] at hs
          rw [e, map_mul, map_inv, hs, inv_mul_cancel]
        have := hker _ hsp h1
        have e2 : p = (s : G) * ((s : G)⁻¹ * p) := by group
        rw [e2]
        exact S.mul_mem s.2 this
      intro x hx
      exact Subgroup.mem_subgroupOf.mpr (hP'S ⟨x, hx, rfl⟩)

end Alt

end CFSG.RankThree.PartTwo.Sec15.Push153B
