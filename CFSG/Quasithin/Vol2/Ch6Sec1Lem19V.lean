module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19K
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19L

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace L619

open CFSG.LieType.BorelTits CFSG.Quasithin

private theorem card_perm_five : Nat.card (Equiv.Perm (Fin 5)) = 120 := by
  rw [Nat.card_perm, Nat.card_fin]
  rfl

theorem center_perm_five : Subgroup.center (Equiv.Perm (Fin 5)) = ⊥ := by
  have key : ∀ g : Equiv.Perm (Fin 5), g * Equiv.swap 0 1 = Equiv.swap 0 1 * g →
      g * (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) =
        (Equiv.swap 0 1 * Equiv.swap 1 2 * Equiv.swap 2 3 * Equiv.swap 3 4) * g → g = 1 := by
    decide +kernel
  rw [eq_bot_iff]
  intro g hg
  rw [Subgroup.mem_center_iff] at hg
  rw [Subgroup.mem_bot]
  exact key g (hg _).symm (hg _).symm

theorem threePartTop_five : threePartTop (Equiv.Perm (Fin 5)) = alternatingGroup (Fin 5) := by
  refine le_antisymm (threePartTop_le_alternating 5) ?_
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating]
  refine (Subgroup.closure_le _).mpr fun σ hσ => Subgroup.subset_closure ⟨1, ?_⟩
  rw [pow_one, ← hσ.orderOf, pow_orderOf_eq_one]

theorem alternatingGroup_le_commutator {n : ℕ} (hn : n = 3 ∨ n = 5) :
    alternatingGroup (Fin n) ≤ commutator (Equiv.Perm (Fin n)) := by
  rw [← Equiv.Perm.closure_three_cycles_eq_alternating, Subgroup.closure_le]
  intro σ hσ
  have hN := (commutator (Equiv.Perm (Fin n))).normal_of_characteristic
  obtain ⟨c, hcmem, hc3⟩ : ∃ c ∈ commutator (Equiv.Perm (Fin n)), c.IsThreeCycle := by
    rcases hn with rfl | rfl
    · refine ⟨⁅Equiv.swap (0 : Fin 3) 2, Equiv.swap (0 : Fin 3) 1⁆,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
      exact card_support_eq_three_iff.mp (by decide)
    · refine ⟨⁅Equiv.swap (0 : Fin 5) 2, Equiv.swap (0 : Fin 5) 1⁆,
        Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _), ?_⟩
      exact card_support_eq_three_iff.mp (by decide)
  obtain ⟨g, hg⟩ := Equiv.Perm.isConj_of_cycleType_eq (hc3.trans (Set.mem_ofPred_eq ▸ hσ).symm)
  have hσ' : σ = (g : Equiv.Perm (Fin n)) * c * (g : Equiv.Perm (Fin n))⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq]
    exact hg.symm
  rw [SetLike.mem_coe, hσ']
  exact hN.conj_mem c hcmem g

theorem card_sup_of_commute {D : Type*} [Group D] [Finite D] {H K : Subgroup D}
    (hc : ∀ a ∈ H, ∀ b ∈ K, a * b = b * a) (hd : H ⊓ K = ⊥) :
    Nat.card ↥(H ⊔ K) = Nat.card H * Nat.card K := by
  have hHK : H ≤ Subgroup.normalizer (K : Set D) := fun a ha =>
    Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)
  have h1 : K.relIndex (H ⊔ K) = K.relIndex H := A4.relIndex_sup_eq_of_le_normalizer' hHK
  have h2 : K.relIndex (H ⊔ K) * Nat.card ↥(K ⊓ (H ⊔ K)) = Nat.card ↥(H ⊔ K) :=
    Subgroup.relIndex_mul_card _ _
  rw [inf_eq_left.mpr le_sup_right, h1] at h2
  have h3 : K.relIndex H * Nat.card ↥(K ⊓ H) = Nat.card H := Subgroup.relIndex_mul_card _ _
  rw [inf_comm, hd, Subgroup.card_bot, mul_one] at h3
  rw [← h2, h3]

theorem le_sup_sylow_of_prod {D : Type*} [Group D] [Finite D] {D₀ D₁ : Subgroup D}
    (hc : ∀ a ∈ D₀, ∀ b ∈ D₁, a * b = b * a) (hd : D₀ ⊓ D₁ = ⊥) (ht : D₀ ⊔ D₁ = ⊤)
    {p : ℕ} [Fact p.Prime] (P₀ : Sylow p D₀) (P₁ : Sylow p D₁) (R : Subgroup D)
    (hR : IsPGroup p R)
    (hle : (P₀ : Subgroup D₀).map D₀.subtype ⊔ (P₁ : Subgroup D₁).map D₁.subtype ≤ R) :
    R ≤ (P₀ : Subgroup D₀).map D₀.subtype ⊔ (P₁ : Subgroup D₁).map D₁.subtype := by
  set B₀ := (P₀ : Subgroup D₀).map D₀.subtype with hB₀
  set B₁ := (P₁ : Subgroup D₁).map D₁.subtype with hB₁
  have hB₀D : B₀ ≤ D₀ := Subgroup.map_subtype_le _
  have hB₁D : B₁ ≤ D₁ := Subgroup.map_subtype_le _
  have hcB : ∀ a ∈ B₀, ∀ b ∈ B₁, a * b = b * a := fun a ha b hb => hc a (hB₀D ha) b (hB₁D hb)
  have hdB : B₀ ⊓ B₁ = ⊥ := le_bot_iff.mp (hd ▸ inf_le_inf hB₀D hB₁D)
  have hcard₀ : Nat.card B₀ = Nat.card (P₀ : Subgroup D₀) :=
    Subgroup.card_map_of_injective D₀.subtype_injective
  have hcard₁ : Nat.card B₁ = Nat.card (P₁ : Subgroup D₁) :=
    Subgroup.card_map_of_injective D₁.subtype_injective
  have hB : Nat.card ↥(B₀ ⊔ B₁) = Nat.card (P₀ : Subgroup D₀) * Nat.card (P₁ : Subgroup D₁) := by
    rw [card_sup_of_commute hcB hdB, hcard₀, hcard₁]
  have hD : Nat.card D = Nat.card D₀ * Nat.card D₁ := by
    rw [← card_sup_of_commute hc hd, ht, Subgroup.card_top]
  have hBp : IsPGroup p ↥(B₀ ⊔ B₁) := by
    have h₀ : IsPGroup p B₀ := P₀.isPGroup'.map _
    have h₁ : IsPGroup p B₁ := P₁.isPGroup'.map _
    refine h₀.to_sup_of_normal_right' h₁ fun a ha => Subgroup.centralizer_le_normalizer _
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hcB a ha b hb).symm)
  have hidx : (B₀ ⊔ B₁).index = (P₀ : Subgroup D₀).index * (P₁ : Subgroup D₁).index := by
    have h1 := (B₀ ⊔ B₁).index_mul_card
    have h2 := (P₀ : Subgroup D₀).index_mul_card
    have h3 := (P₁ : Subgroup D₁).index_mul_card
    rw [hB, hD, ← h2, ← h3] at h1
    have hpos : 0 < Nat.card (P₀ : Subgroup D₀) * Nat.card (P₁ : Subgroup D₁) :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans (by ring))
  have hnd : ¬ p ∣ (B₀ ⊔ B₁).index := by
    rw [hidx]
    intro h
    rcases (Nat.Prime.dvd_mul Fact.out).mp h with h | h
    · exact P₀.not_dvd_index h
    · exact P₁.not_dvd_index h
  have := (hBp.toSylow hnd).is_maximal' hR hle
  rw [this]
  exact le_rfl


theorem exists_abelian_sylow_of_prod {E D : Type*} [Group E] [Finite E] [Group D] [Finite D]
    (η : E →* D) (hsurj : Function.Surjective η) (hcentral : η.ker ≤ Subgroup.center E)
    {D₀ D₁ : Subgroup D} (hc : ∀ a ∈ D₀, ∀ b ∈ D₁, a * b = b * a) (hd : D₀ ⊓ D₁ = ⊥)
    (ht : D₀ ⊔ D₁ = ⊤) {p : ℕ} [hp : Fact p.Prime] (hcyc₀ : ∀ P : Sylow p D₀, IsCyclic P)
    (hcyc₁ : ∀ P : Sylow p D₁, IsCyclic P)
    (hcomm₀ : ∀ x : D₀, (∃ k : ℕ, x ^ p ^ k = 1) → x ∈ commutator D₀) :
    ∃ P : Sylow p E, IsMulCommutative (P : Subgroup E) := by
  obtain ⟨P₀⟩ := (inferInstance : Nonempty (Sylow p D₀))
  obtain ⟨P₁⟩ := (inferInstance : Nonempty (Sylow p D₁))
  have := hcyc₀ P₀
  have := hcyc₁ P₁
  obtain ⟨g₀, hg₀⟩ := IsCyclic.exists_generator (α := (P₀ : Subgroup D₀))
  obtain ⟨g₁, hg₁⟩ := IsCyclic.exists_generator (α := (P₁ : Subgroup D₁))
  obtain ⟨i, hi⟩ := P₀.isPGroup' g₀
  obtain ⟨j, hj⟩ := P₁.isPGroup' g₁
  have hi' : ((g₀ : D₀) : D) ^ p ^ i = 1 := by
    simpa using congrArg (fun u : (P₀ : Subgroup D₀) => ((u : D₀) : D)) hi
  have hj' : ((g₁ : D₁) : D) ^ p ^ j = 1 := by
    simpa using congrArg (fun u : (P₁ : Subgroup D₁) => ((u : D₁) : D)) hj
  have hx : ((g₀ : D₀) : D) ∈ ⁅D₀, D₀⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨g₀, hcomm₀ _ ⟨i, by simpa using congrArg Subtype.val hi⟩, rfl⟩
  have hzp : ∀ {H : Subgroup D} (Q : Sylow p H) (g : (Q : Subgroup H)),
      (∀ x, x ∈ Subgroup.zpowers g) →
      (Q : Subgroup H).map H.subtype = Subgroup.zpowers ((g : H) : D) := by
    intro H Q g hg
    apply le_antisymm
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
      refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
      have := congrArg (fun u : (Q : Subgroup H) => ((u : H) : D)) hk
      simpa using this
    · rw [Subgroup.zpowers_le]
      exact ⟨g, g.2, rfl⟩
  have hcl : Subgroup.closure ({((g₀ : D₀) : D), ((g₁ : D₁) : D)} : Set D) =
      (P₀ : Subgroup D₀).map D₀.subtype ⊔ (P₁ : Subgroup D₁).map D₁.subtype := by
    rw [hzp P₀ g₀ hg₀, hzp P₁ g₁ hg₁, Subgroup.zpowers_eq_closure, Subgroup.zpowers_eq_closure,
      ← Subgroup.closure_union]
    rfl
  refine exists_abelian_sylow_of_commute η hsurj hcentral hc hx (g₁ : D₁).2 hi' hj' ?_
  intro R hR hle
  rw [hcl] at hle ⊢
  exact le_sup_sylow_of_prod hc hd ht P₀ P₁ R hR hle

theorem sign_eq_one_of_odd {n : ℕ} {σ : Equiv.Perm (Fin n)} (h : Odd (orderOf σ)) :
    Equiv.Perm.sign σ = 1 := by
  have h1 : Equiv.Perm.sign σ ^ orderOf σ = 1 := by rw [← map_pow, pow_orderOf_eq_one, map_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h2 | h2
  · exact h2
  · rw [h2, h.neg_one_pow] at h1
    exact absurd h1 (by decide)

theorem center_eq_bot_of_mulEquiv' {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    (h : Subgroup.center Y = ⊥) : Subgroup.center X = ⊥ := by
  rw [← Subgroup.map_center_eq e.symm, h, Subgroup.map_bot]

structure SmallFacts (Kt : Type) [Group Kt] [Finite Kt] : Prop where
  card : Nat.card Kt = 6 ∨ Nat.card Kt = 168 ∨ Nat.card Kt = 120
  center : Subgroup.center Kt = ⊥
  odd_mem : ∀ x : Kt, Odd (orderOf x) → x ∈ commutator Kt
  simple : ∀ N : Subgroup Kt, N ≤ threePartTop Kt →
    threePartTop Kt ≤ Subgroup.normalizer (N : Set Kt) → N = ⊥ ∨ N = threePartTop Kt
  top_center : Nat.card Kt ≠ 6 → Subgroup.center ↥(threePartTop Kt) = ⊥
  three_dvd : 3 ∣ Nat.card ↥(threePartTop Kt)

theorem smallFacts_perm_three : SmallFacts (Equiv.Perm (Fin 3)) where
  card := Or.inl card_perm_three
  center := center_perm_three
  odd_mem x hx := alternatingGroup_le_commutator (Or.inl rfl)
    (Equiv.Perm.mem_alternatingGroup.mpr (sign_eq_one_of_odd hx))
  simple N hN _ := eq_bot_or_eq_threePartTop_three hN
  top_center h := absurd card_perm_three h
  three_dvd := by rw [card_threePartTop_three]

theorem smallFacts_GL32 : SmallFacts (GL (Fin 3) (ZMod 2)) where
  card := Or.inr (Or.inl card_GL32)
  center := CFSG.QuasithinUnique.Setup.Family.center_GL32
  odd_mem x _ := by
    have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := isSimpleGroup_GL32
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator (GL (Fin 3) (ZMod 2))) with
      h | h
    · exfalso
      have hcomm : ∀ a b : GL (Fin 3) (ZMod 2), a * b = b * a := fun a b => by
        have := commutatorElement_eq_one_iff_mul_comm.mp (by
          have hm : ⁅a, b⁆ ∈ commutator (GL (Fin 3) (ZMod 2)) :=
            Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
          rwa [h, Subgroup.mem_bot] at hm)
        exact this
      have htop : Subgroup.center (GL (Fin 3) (ZMod 2)) = ⊤ :=
        eq_top_iff.mpr fun g _ => Subgroup.mem_center_iff.mpr fun k => hcomm k g
      have hbot := CFSG.QuasithinUnique.Setup.Family.center_GL32
      rw [htop] at hbot
      have := Subgroup.card_top (G := GL (Fin 3) (ZMod 2))
      rw [hbot, Subgroup.card_bot, card_GL32] at this
      omega
    · rw [h]
      exact Subgroup.mem_top x
  simple N _ hN := by
    have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := isSimpleGroup_GL32
    rw [threePartTop_GL32] at hN ⊢
    have : N.Normal := ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.mem_top g))
      n).mp hn⟩
    exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
  top_center _ := by
    rw [threePartTop_GL32]
    exact center_eq_bot_of_mulEquiv' Subgroup.topEquiv
      CFSG.QuasithinUnique.Setup.Family.center_GL32
  three_dvd := by
    rw [threePartTop_GL32, Subgroup.card_top, card_GL32]
    norm_num

theorem smallFacts_perm_five : SmallFacts (Equiv.Perm (Fin 5)) where
  card := Or.inr (Or.inr card_perm_five)
  center := center_perm_five
  odd_mem x hx := alternatingGroup_le_commutator (Or.inr rfl)
    (Equiv.Perm.mem_alternatingGroup.mpr (sign_eq_one_of_odd hx))
  simple N hN hNn := by
    rw [threePartTop_five] at hN hNn ⊢
    have : (N.subgroupOf (alternatingGroup (Fin 5))).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hN).mpr hNn
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf (alternatingGroup (Fin 5))) with
      h | h
    · left
      rw [eq_bot_iff]
      intro x hx
      have hx' : (⟨x, hN hx⟩ : alternatingGroup (Fin 5)) ∈
          N.subgroupOf (alternatingGroup (Fin 5)) := hx
      rw [h, Subgroup.mem_bot] at hx'
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val hx'
    · right
      exact le_antisymm hN (Subgroup.subgroupOf_eq_top.mp h)
  top_center _ := by
    rw [threePartTop_five]
    exact alternatingGroup.center_eq_bot (by rw [Nat.card_fin]; norm_num)
  three_dvd := by
    rw [threePartTop_five, nat_card_alternatingGroup, Nat.card_fin]
    decide

theorem exists_smallFacts {W : Type} [CommGroup W] {Ki : Subgroup (MulAut W)}
    (h : G6.IsSmallG64Type Ki) :
    ∃ (Kt : Type) (_ : Group Kt) (_ : Finite Kt), SmallFacts Kt ∧ Nonempty (↥Ki ≃* Kt) := by
  rcases h with ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩ | ⟨⟨e⟩⟩
  · obtain ⟨e₂⟩ := nonempty_gl2_mulEquiv_perm3'
    exact ⟨Equiv.Perm (Fin 3), inferInstance, inferInstance, smallFacts_perm_three, ⟨e.trans e₂⟩⟩
  · exact ⟨GL (Fin 3) (ZMod 2), inferInstance, inferInstance, smallFacts_GL32, ⟨e⟩⟩
  · exact ⟨Equiv.Perm (Fin 5), inferInstance, inferInstance, smallFacts_perm_five, ⟨e⟩⟩

section Preimage

variable {Γ X : Type*} [Group Γ] [Group X] {P : Subgroup Γ} {K : Subgroup X} (φ : ↥P →* ↥K)

@[expose] def preimg (Q : Subgroup X) : Subgroup Γ := ((Q.subgroupOf K).comap φ).map P.subtype

theorem preimg_le (Q : Subgroup X) : preimg φ Q ≤ P := Subgroup.map_subtype_le _

theorem mem_preimg {Q : Subgroup X} {x : Γ} :
    x ∈ preimg φ Q ↔ ∃ hx : x ∈ P, ((φ ⟨x, hx⟩ : ↥K) : X) ∈ Q := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hQ⟩
    exact ⟨⟨x, hx⟩, hQ, rfl⟩

@[expose] def preimgHom (Q : Subgroup X) (hQ : Q ≤ K) : ↥(preimg φ Q) →* ↥Q :=
  (Subgroup.subgroupOfEquivOfLe hQ).toMonoidHom.comp
    ((φ.comp (Subgroup.inclusion (preimg_le φ Q))).codRestrict (Q.subgroupOf K) fun x =>
      ((mem_preimg φ).mp x.2).2)

theorem preimgHom_coe (Q : Subgroup X) (hQ : Q ≤ K) (x : ↥(preimg φ Q)) :
    ((preimgHom φ Q hQ x : ↥Q) : X) = ((φ ⟨x, preimg_le φ Q x.2⟩ : ↥K) : X) := rfl

theorem preimgHom_surjective (hφ : Function.Surjective φ) (Q : Subgroup X) (hQ : Q ≤ K) :
    Function.Surjective (preimgHom φ Q hQ) := by
  rintro ⟨q, hq⟩
  obtain ⟨x, hx⟩ := hφ ⟨q, hQ hq⟩
  refine ⟨⟨x, (mem_preimg φ).mpr ⟨x.2, by
    rw [show (⟨(x : Γ), x.2⟩ : ↥P) = x from rfl, hx]; exact hq⟩⟩, Subtype.ext ?_⟩
  rw [preimgHom_coe]
  show ((φ x : ↥K) : X) = q
  rw [hx]

theorem preimgHom_eq_one_iff (Q : Subgroup X) (hQ : Q ≤ K) (x : ↥(preimg φ Q)) :
    preimgHom φ Q hQ x = 1 ↔ φ ⟨x, preimg_le φ Q x.2⟩ = 1 := by
  rw [Subtype.ext_iff, preimgHom_coe, Subgroup.coe_one, ← Subgroup.coe_one (H := K),
    Subtype.ext_iff.symm]

end Preimage

@[expose] def oddPart {Γ : Type*} [Group Γ] (I : Subgroup Γ) : Subgroup Γ :=
  Subgroup.closure {x | x ∈ I ∧ Odd (orderOf x)}

theorem oddPart_le {Γ : Type*} [Group Γ] (I : Subgroup Γ) : oddPart I ≤ I :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

omit [Finite G] in
theorem threePart_le_oddPart {X I : Subgroup G} (hXI : X ≤ I) :
    threePart X ≤ oddPart I := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hx, k, hk⟩
  refine Subgroup.subset_closure ⟨hXI hx, ?_⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (orderOf_dvd_of_pow_eq_one hk)
  rw [hj]
  exact Odd.pow (by decide)

theorem mem_normalizer_oddPart {I : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (I : Set G)) :
    g ∈ Subgroup.normalizer (oddPart I : Set G) := by
  refine H13.mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
  have key : oddPart I ≤ (oddPart I).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hy, hodd⟩
    refine Subgroup.subset_closure ⟨(Subgroup.mem_normalizer_iff.mp hg y).mp hy, ?_⟩
    show Odd (orderOf (g * y * g⁻¹))
    rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
    exact hodd
  exact key hx

theorem conjSubgroup_eq_of_odd {X : Type*} [Group X] {K₀ K₁ : Subgroup X} (hne : K₀ ≠ K₁)
    {g : X} (hg : Odd (orderOf g)) (h₀ : conjSubgroup K₀ g = K₀ ∨ conjSubgroup K₀ g = K₁)
    (h₁ : conjSubgroup K₁ g = K₀ ∨ conjSubgroup K₁ g = K₁) : conjSubgroup K₀ g = K₀ := by
  rcases h₀ with h₀ | h₀
  · exact h₀
  exfalso
  have h₁' : conjSubgroup K₁ g = K₀ := by
    rcases h₁ with h₁ | h₁
    · exact h₁
    · exact absurd (G6.conjSubgroup_inj (h₀.trans h₁.symm)) hne
  have h2 : conjSubgroup K₀ (g ^ 2) = K₀ := by
    rw [pow_two, ← conjSubgroup_conjSubgroup, h₀, h₁']
  have heven : ∀ k : ℕ, conjSubgroup K₀ (g ^ (2 * k)) = K₀ := by
    intro k
    induction k with
    | zero => simp [conjSubgroup_one]
    | succ k ih =>
      rw [show 2 * (k + 1) = 2 * k + 2 by ring, pow_add, ← conjSubgroup_conjSubgroup, ih, h2]
  obtain ⟨k, hk⟩ := hg
  have := heven k
  have hodd : conjSubgroup K₀ (g ^ (2 * k + 1)) = K₁ := by
    rw [pow_succ, ← conjSubgroup_conjSubgroup, heven k, h₀]
  rw [← hk, pow_orderOf_eq_one, conjSubgroup_one] at hodd
  exact hne hodd

end L619


namespace L619

theorem mem_commutator_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {x : X}
    (h : e x ∈ commutator Y) : x ∈ commutator X := by
  have hmap : (commutator Y).map e.symm.toMonoidHom = commutator X := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective _ e.symm.surjective]
  rw [← hmap]
  exact ⟨e x, h, by simp⟩

end L619

namespace Dat619

variable {z : G} {T' D' : Subgroup G} (hd : Dat619 T M L V H n y z T' D')
include hd

theorem false_of_comps {J A₁ A₂ : Subgroup G} (hA₁ : L619.ThreeComp J A₁)
    (hA₂ : L619.ThreeComp J A₂) (hinf : A₁ ⊓ A₂ ≤ pCoreOf 2 A₁)
    (hAI : A₁ ⊔ A₂ ≤ ch619I T L V) (hD₁ : D' ≤ Subgroup.normalizer (A₁ : Set G))
    (hD₂ : D' ≤ Subgroup.normalizer (A₂ : Set G)) : False := by
  have h3 := L619.three_le_pRank_of_two_comps hA₁ hA₂ hinf hAI hd.D'_le_I hd.D'_inf hd.card_D'
    hD₁ hD₂
  have hle : A₁ ⊔ A₂ ⊔ D' ≤ Subgroup.normalizer (ch6ZS T L V : Set G) :=
    sup_le (hAI.trans (Subgroup.centralizer_le_normalizer _)) hd.D'_le_ZS
  have := (CFSG.SectionRank.pRank_mono (by norm_num) hle).trans hd.rank
  omega

theorem pCoreOf_of_two (h : Hyp6116 G T M L V n) (h432 : Stmt4_3_2)
    (hW : IsElemAbelian 2 (ch619W T L V z))
    {Ks : Fin 2 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))}
    (hdec : G6.IsTransvectionDecomposition
      (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks) :
    conjClosure (conjSub y V) (ch619I T L V ⊔ T') ⊓ ch619K2 T L V z ≤
      pCoreOf 2 (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) := by
  set K := L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) with hK
  have hKi : ∀ i, Ks i ≤ K := fun i => by rw [← hdec.iSup_eq]; exact le_iSup Ks i
  have hsup : Ks 0 ⊔ Ks 1 = K := by rw [← hdec.iSup_eq, G6.iSup_fin_two]
  have hc : ∀ a ∈ Ks 0, ∀ b ∈ Ks 1, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (hdec.centralize 0 1 (by decide) ha) b hb).symm
  have hdisj : Ks 0 ⊓ Ks 1 = ⊥ :=
    disjoint_iff.mp (hdec.indep.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1))
  have hcard : ∀ i, ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ p ^ 2 ∣ Nat.card ((Ks i).subgroupOf K) := by
    intro i p hp hp2
    obtain ⟨Kt, _, _, hS, ⟨θ⟩⟩ := L619.exists_smallFacts (hdec.small rfl i)
    rw [Nat.card_congr ((Subgroup.subgroupOfEquivOfLe (hKi i)).trans θ).toEquiv]
    exact L619.not_sq_dvd_of_small (hS.card.imp_right Or.symm) hp hp2
  refine hd.cfg.inf_K2_le_pCoreOf_of h h432 hd.z619 hd.isY hW ?_
  intro E _ _ η hηs hηc p hp hp2
  have hcD : ∀ a ∈ (Ks 0).subgroupOf K, ∀ b ∈ (Ks 1).subgroupOf K, a * b = b * a :=
    fun a ha b hb => Subtype.ext (hc _ ha _ hb)
  have hdD : (Ks 0).subgroupOf K ⊓ (Ks 1).subgroupOf K = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : (x : MulAut _) ∈ Ks 0 ⊓ Ks 1 := ⟨hx.1, hx.2⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact Subtype.ext this
  have htD : (Ks 0).subgroupOf K ⊔ (Ks 1).subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (hKi 0) (hKi 1), hsup, Subgroup.subgroupOf_self]
  obtain ⟨Kt₀, _, _, hS₀, ⟨θ₀⟩⟩ := L619.exists_smallFacts (hdec.small rfl 0)
  refine L619.exists_abelian_sylow_of_prod η hηs hηc hcD hdD htD
    (fun P => CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd (hcard 0 p hp.out hp2) P)
    (fun P => CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd (hcard 1 p hp.out hp2) P) ?_
  rintro x ⟨k, hk⟩
  set e := (Subgroup.subgroupOfEquivOfLe (hKi 0)).trans θ₀
  refine L619.mem_commutator_of_mulEquiv e (hS₀.odd_mem _ ?_)
  rw [MulEquiv.orderOf_eq]
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hk)
  rw [hj]
  exact Odd.pow (hp.out.odd_of_ne_two hp2)


theorem false_of_two (h : Hyp6116 G T M L V n) (h432 : Stmt4_3_2)
    (hW : IsElemAbelian 2 (ch619W T L V z))
    {Ks : Fin 2 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))}
    (hdec : G6.IsTransvectionDecomposition
      (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks)
    (hND : L619.NormDec hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) Ks)
    (hcase : (∀ (x : G) (hx : x ∈ L619.normWZX (ch619W T L V z) (ch6ZS T L V)
        (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))), x ∈ ch619I T L V → ∀ i, ∀ k ∈ Ks i,
        L619.act0 hW _ _ ⟨x, hx⟩ * k * (L619.act0 hW _ _ ⟨x, hx⟩)⁻¹ ∈ Ks i) ∨
      (∀ i, Nat.card (Ks i) ≠ 6)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c := hd.cfg
  have hz := hd.z619
  have hY := hd.isY
  revert Ks
  set I := ch619I T L V with hI
  set P := conjClosure (conjSub y V) (I ⊔ T') with hP
  set N := L619.normWZX (ch619W T L V z) (ch6ZS T L V) P with hN
  set K := L619.img0 hW (ch6ZS T L V) P with hKdef
  intro Ks hdec hND hcase
  have hPN : P ≤ N := c.conjClosure_E_le_normWZX hY
  have hIN : I ≤ N := hY.I_le.trans (Cfg619.Y_le_normWZX hY)
  set φ := L619.actOn hW (ch6ZS T L V) P hPN (fun x => L619.act0_mem_img0 hW _ P x.2) with hφ
  have hφs : Function.Surjective φ := L619.actOn_surjective hW _ P hPN
  have hφ1 : ∀ x : ↥P, φ x = 1 ↔ (x : G) ∈ ch619K2 T L V z := by
    intro x
    rw [Subtype.ext_iff]
    exact c.act0_eq_one_iff h h432 hz hY hW (x := Subgroup.inclusion hPN x) x.2
  have hPK2 := hd.pCoreOf_of_two h h432 hW hdec
  have hkerP : ∀ x : ↥P, φ x = 1 → (x : G) ∈ pCoreOf 2 P := fun x hx =>
    hPK2 ⟨x.2, (hφ1 x).mp hx⟩
  have hO2P : IsPGroup 2 (pCoreOf 2 P) := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P
  have hPI : P ≤ I := c.conjClosure_E_le_I hY
  have hIP : I ≤ Subgroup.normalizer (P : Set G) :=
    hY.I_le.trans (le_normalizer_conjClosure _ _)
  have hKi : ∀ i, Ks i ≤ K := fun i => by rw [← hdec.iSup_eq]; exact le_iSup Ks i
  have hdisj : Ks 0 ⊓ Ks 1 = ⊥ :=
    disjoint_iff.mp (hdec.indep.pairwiseDisjoint (by decide : (0 : Fin 2) ≠ 1))
  have hne : Ks 0 ≠ Ks 1 := by
    intro heq
    apply hdec.ne_bot 0
    rw [← inf_idem (Ks 0)]
    nth_rewrite 2 [heq]
    exact hdisj
  have hact : ∀ (x p : G) (hx : x ∈ N) (hp : p ∈ N),
      L619.act0 hW _ P ⟨x * p * x⁻¹, N.mul_mem (N.mul_mem hx hp) (N.inv_mem hx)⟩ =
        L619.act0 hW _ P ⟨x, hx⟩ * L619.act0 hW _ P ⟨p, hp⟩ * (L619.act0 hW _ P ⟨x, hx⟩)⁻¹ := by
    intro x p hx hp
    rw [← map_inv, ← map_mul, ← map_mul]
    rfl
  have hnormX : ∀ i (x : G) (hxI : x ∈ I),
      (∀ k ∈ Ks i, L619.act0 hW _ P ⟨x, hIN hxI⟩ * k * (L619.act0 hW _ P ⟨x, hIN hxI⟩)⁻¹ ∈ Ks i) →
      x ∈ Subgroup.normalizer (L619.preimg φ (Ks i) : Set G) := by
    intro i x hxI hfix
    refine H13.mem_normalizer_of_forall_conj_mem_of_le fun p hp => ?_
    obtain ⟨hpP, hpK⟩ := (L619.mem_preimg φ).mp hp
    have hxp : x * p * x⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp (hIP hxI) p).mp hpP
    refine (L619.mem_preimg φ).mpr ⟨hxp, ?_⟩
    have e := hact x p (hIN hxI) (hPN hpP)
    show L619.act0 hW _ P ⟨x * p * x⁻¹, hPN hxp⟩ ∈ Ks i
    rw [e]
    exact hfix _ hpK
  have hoddfix : ∀ (x : G) (hxI : x ∈ I), Odd (orderOf x) → ∀ i,
      ∀ k ∈ Ks i, L619.act0 hW _ P ⟨x, hIN hxI⟩ * k * (L619.act0 hW _ P ⟨x, hIN hxI⟩)⁻¹ ∈ Ks i := by
    intro x hxI hodd i k hk
    set g := L619.act0 hW _ P ⟨x, hIN hxI⟩ with hg
    have hQ := (hND ⟨x, hIN hxI⟩).1
    have hcase2 : ∀ j : Fin 2, conjSubgroup (Ks j) g = Ks 0 ∨ conjSubgroup (Ks j) g = Ks 1 := by
      intro j
      obtain ⟨l, hl⟩ := hQ j
      fin_cases l
      · exact Or.inl hl
      · exact Or.inr hl
    have hgodd : Odd (orderOf g) := Odd.of_dvd_nat hodd (by
      rw [hg, ← Subgroup.orderOf_mk x (hIN hxI)]
      exact orderOf_map_dvd _ _)
    have hfix : conjSubgroup (Ks i) g = Ks i := by
      fin_cases i
      · exact L619.conjSubgroup_eq_of_odd hne hgodd (hcase2 0) (hcase2 1)
      · exact L619.conjSubgroup_eq_of_odd hne.symm hgodd ((hcase2 1).symm) ((hcase2 0).symm)
    have : k ∈ conjSubgroup (Ks i) g := by rw [hfix]; exact hk
    exact mem_conjSubgroup_iff.mp this
  have hdata : ∀ i : Fin 2, ∃ (Kt : Type) (_ : Group Kt) (_ : Finite Kt)
      (ψ : ↥(L619.preimg φ (Ks i)) →* Kt), L619.SmallFacts Kt ∧ Function.Surjective ψ ∧
      IsPGroup 2 ψ.ker ∧
      (∀ x (hx : x ∈ L619.preimg φ (Ks i)), x ∈ pCoreOf 2 I → ψ ⟨x, hx⟩ = 1) ∧
      Nat.card Kt = Nat.card (Ks i) := by
    intro i
    obtain ⟨Kt, _, _, hS, ⟨θ⟩⟩ := L619.exists_smallFacts (hdec.small rfl i)
    set X := L619.preimg φ (Ks i) with hX
    have hXP : X ≤ P := L619.preimg_le φ (Ks i)
    set ψ : ↥X →* Kt := θ.toMonoidHom.comp (L619.preimgHom φ (Ks i) (hKi i)) with hψ
    have hψs : Function.Surjective ψ :=
      θ.surjective.comp (L619.preimgHom_surjective φ hφs (Ks i) (hKi i))
    have hψ1 : ∀ x : ↥X, ψ x = 1 ↔ φ ⟨x, hXP x.2⟩ = 1 := by
      intro x
      rw [hψ, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulEquiv.map_eq_one_iff,
        L619.preimgHom_eq_one_iff]
    have hker : IsPGroup 2 ψ.ker := by
      rintro ⟨x, hx⟩
      obtain ⟨k, hk⟩ := hO2P ⟨(x : G), hkerP _ ((hψ1 x).mp hx)⟩
      refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
      simpa using congrArg Subtype.val hk
    refine ⟨Kt, inferInstance, inferInstance, ψ, hS, hψs, hker, fun x hx hxO => ?_,
      (Nat.card_congr θ.toEquiv).symm⟩
    exact (hψ1 ⟨x, hx⟩).mpr ((hφ1 ⟨x, hXP hx⟩).mpr (Cfg619.pCoreOf_I_le_K2 h h432 z hxO))
  have hA : ∃ J : Subgroup G, J ≤ I ∧ ∀ i : Fin 2,
      L619.ThreeComp J (L619.threePart (L619.preimg φ (Ks i))) ∧
      D' ≤ Subgroup.normalizer (L619.threePart (L619.preimg φ (Ks i)) : Set G) := by
    rcases hcase with hfix | hnab
    ·
      refine ⟨I, le_rfl, fun i => ?_⟩
      set X := L619.preimg φ (Ks i) with hX
      obtain ⟨Kt, _, _, ψ, hS, hψs, hker, hO, -⟩ := hdata i
      have hXP : X ≤ P := L619.preimg_le φ (Ks i)
      have h9 : ¬ 9 ∣ Nat.card Kt := by rcases hS.card with h | h | h <;> rw [h] <;> decide
      have h3 : 3 ∣ Nat.card Kt := by rcases hS.card with h | h | h <;> rw [h] <;> decide
      have hIX : I ≤ Subgroup.normalizer (X : Set G) := fun x hxI =>
        hnormX i x hxI (hfix x (hIN hxI) hxI i)
      have hAc := L619.threeComp_of ψ ((L619.threePart_le X).trans (hXP.trans hPI)) hIX hψs
        hker hS.simple h9 h3
      have hwit := L619.exists_commutator_not_mem ψ hψs hS.center h3 hO
      refine ⟨hAc, fun d hdD => ?_⟩
      exact mem_normalizer_of_conjSub_le' (L619.ThreeComp.conjSub_eq_of_pRank hd.rank_I hAc
        (hXP.trans hPI) hIX (fun x hx k hk => L619.mem_threePart hx hk) hwit (hd.D'_le_I hdD)
        (hd.pow_three_eq_one hdD)).le
    ·
      set J := L619.oddPart I with hJ
      have hJI : J ≤ I := L619.oddPart_le I
      have hIJ : I ≤ Subgroup.normalizer (J : Set G) := fun x hx =>
        L619.mem_normalizer_oddPart (Subgroup.le_normalizer hx)
      have hrk : CFSG.Open.pRank 3 J ≤ 2 :=
        (CFSG.SectionRank.pRank_mono (by norm_num) hJI).trans hd.rank_I
      refine ⟨J, hJI, fun i => ?_⟩
      set X := L619.preimg φ (Ks i) with hX
      obtain ⟨Kt, _, _, ψ, hS, hψs, hker, hO, hcard⟩ := hdata i
      have hXP : X ≤ P := L619.preimg_le φ (Ks i)
      have h9 : ¬ 9 ∣ Nat.card Kt := by rcases hS.card with h | h | h <;> rw [h] <;> decide
      have h3 : 3 ∣ Nat.card Kt := by rcases hS.card with h | h | h <;> rw [h] <;> decide
      have hJX : J ≤ Subgroup.normalizer (X : Set G) := by
        refine (Subgroup.closure_le _).mpr ?_
        rintro x ⟨hxI, hodd⟩
        exact hnormX i x hxI (hoddfix x hxI hodd i)
      have hAJ : L619.threePart X ≤ J := L619.threePart_le_oddPart (hXP.trans hPI)
      have hAc := L619.threeComp_of ψ hAJ hJX hψs hker hS.simple h9 h3
      have hne6 : Nat.card Kt ≠ 6 := hcard ▸ hnab i
      set A := L619.threePart X with hAdef
      let ψ' : ↥A →* ↥(L619.threePartTop Kt) :=
        (ψ.comp (Subgroup.inclusion (L619.threePart_le X))).codRestrict _ fun a =>
          L619.psi_mem_threePartTop ψ a.2
      have hψ's : Function.Surjective ψ' := by
        rintro ⟨k, hk⟩
        obtain ⟨x, hx, hxk⟩ := L619.exists_preimage_threePartTop ψ hψs hk
        exact ⟨⟨x, hx⟩, Subtype.ext hxk⟩
      have hO' : ∀ x (hx : x ∈ A), x ∈ pCoreOf 2 J → ψ' ⟨x, hx⟩ = 1 := by
        intro x hx hxO
        apply Subtype.ext
        exact hO x (L619.threePart_le X hx) (F7.pCoreOf_mono_of_le_normalizer hJI hIJ hxO)
      obtain ⟨e, he, a, ha, hea⟩ := L619.exists_commutator_not_mem ψ' hψ's (hS.top_center hne6)
        hS.three_dvd hO'
      have hwit : ∃ e ∈ A, ∃ a ∈ A, e * a * e⁻¹ * a⁻¹ ∉ pCoreOf 2 J :=
        ⟨e, he, a, L619.threePart_le A ha, hea⟩
      refine ⟨hAc, fun d hdD => ?_⟩
      exact mem_normalizer_of_conjSub_le' (L619.ThreeComp.conjSub_eq_of_pRank hrk hAc hAJ
        hAc.normal (fun x hx _ _ => hx) hwit (L619.mem_normalizer_oddPart (hd.D'_le_I hdD))
        (hd.pow_three_eq_one hdD)).le
  obtain ⟨J, hJI, hAJ⟩ := hA
  obtain ⟨hA₀, hDA₀⟩ := hAJ 0
  obtain ⟨hA₁, hDA₁⟩ := hAJ 1
  set A₀ := L619.threePart (L619.preimg φ (Ks 0)) with hA₀def
  set A₁ := L619.threePart (L619.preimg φ (Ks 1)) with hA₁def
  have hinf : A₀ ⊓ A₁ ≤ pCoreOf 2 A₀ := by
    have h2 : IsPGroup 2 ↥(A₀ ⊓ A₁) := by
      rintro ⟨x, hx₀, hx₁⟩
      obtain ⟨hxP, hxK₀⟩ := (L619.mem_preimg φ).mp (L619.threePart_le _ hx₀)
      obtain ⟨hxP', hxK₁⟩ := (L619.mem_preimg φ).mp (L619.threePart_le _ hx₁)
      have h1 : ((φ ⟨x, hxP⟩ : ↥K) : MulAut _) ∈ Ks 0 ⊓ Ks 1 := ⟨hxK₀, hxK₁⟩
      rw [hdisj, Subgroup.mem_bot] at h1
      obtain ⟨k, hk⟩ := hO2P ⟨x, hkerP ⟨x, hxP⟩ (Subtype.ext h1)⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ h2
    intro a ha
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer ha, hA₁.normal (hA₀.le ha)⟩
  have hAI : A₀ ⊔ A₁ ≤ I := sup_le (hA₀.le.trans hJI) (hA₁.le.trans hJI)
  exact hd.false_of_comps hA₀ hA₁ hinf hAI hDA₀ hDA₁

end Dat619

end CFSG.Quasithin.H13
