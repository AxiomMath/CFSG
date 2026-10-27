module

public import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432Tools
import CFSG.GroupTheory.Fitting.CharacteristicP
import CFSG.GH74.GLS.AssemblyComponents
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarT
public import CFSG.RankThree.PartTwo.Sec4.Statements

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

@[expose] def Item4_32Comp : Prop :=
  ∀ (G : Type) [Group G] [Finite G], (∀ K : Subgroup G, IsComponent K → SectionFourHyp K) →
    CFSG.pPrimeCore 3 G = ⊥ →
    ∀ Z : Subgroup G, Nat.card Z = 3 →
    (∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) →
      Z.map (MulAut.conj g).toMonoidHom = Z) →
      CFSG.Open.pRank 3 (Subgroup.normalClosure (Z : Set G)) = 1 ∨
        IsoGTwoPrime (Subgroup.normalClosure (Z : Set G)) ∨
        Nonempty (Subgroup.normalClosure (Z : Set G) ≃* Blueprint.NativeSporadic.J2)

@[expose] def K432List : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsQuasisimple L → SectionFourHyp L →
    IsPGroup 3 (Subgroup.center L) →
    ∀ Z : Subgroup L, Nat.card Z = 3 →
    (∀ g : L, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set L) →
      Z.map (MulAut.conj g).toMonoidHom = Z) →
    ¬ Z ≤ Subgroup.center L →
      CFSG.Open.pRank 3 (⊤ : Subgroup L) = 1 ∨ IsoGTwoPrime L ∨
        Nonempty (L ≃* Blueprint.NativeSporadic.J2)

namespace Item432Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem map_subtype_normal_of_characteristic {N : Subgroup G} [N.Normal]
    (K : Subgroup N) [hK : K.Characteristic] : (K.map N.subtype).Normal := by
  refine ⟨fun x hx g => ?_⟩
  obtain ⟨k, hk, rfl⟩ := hx
  have hfix := hK.fixed (MulAut.conjNormal (H := N) g⁻¹)
  have hk' : MulAut.conjNormal (H := N) g k ∈ K := by
    have he : (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom (MulAut.conjNormal (H := N) g k) =
        k := by
      ext
      simp
    have h1 : (MulAut.conjNormal (H := N) g k) ∈
        K.comap (MulAut.conjNormal (H := N) g⁻¹).toMonoidHom := by
      rw [Subgroup.mem_comap, he]
      exact hk
    rwa [hfix] at h1
  exact ⟨_, hk', by simp [MulAut.conjNormal_apply]⟩

omit [Finite G] in
theorem exists_zpowers_eq {Z : Subgroup G} (hZ : Nat.card Z = 3) :
    ∃ z : G, orderOf z = 3 ∧ Subgroup.zpowers z = Z := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcyc : IsCyclic Z := isCyclic_of_prime_card hZ
  obtain ⟨g, hg⟩ := hcyc.exists_generator
  refine ⟨(g : G), ?_, ?_⟩
  · rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers hg, hZ]
  · apply le_antisymm (Subgroup.zpowers_le.mpr g.2)
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    have hx' : (g : G) ^ k = x := by simpa using congrArg Subtype.val hk
    rw [← hx']
    exact Subgroup.zpow_mem_zpowers _ k

theorem pRank_top_eq (L : Subgroup G) :
    CFSG.Open.pRank 3 (⊤ : Subgroup L) = CFSG.Open.pRank 3 L := by
  apply le_antisymm
  · have h := CFSG.SectionRank.pRank_le_map (p := 3) (by norm_num) L.subtype
      L.subtype_injective (⊤ : Subgroup L)
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
  · obtain ⟨E, hEL, hE, hcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
    refine CFSG.SectionRank.le_pRank (by norm_num) le_top ?_ (k := CFSG.Open.pRank 3 L) ?_
      (E := E.subgroupOf L)
    · refine ⟨⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩, fun x hx => ?_⟩
      · show ((x : L) : G) * ((y : L) : G) = ((y : L) : G) * ((x : L) : G)
        exact congrArg Subtype.val (hE.1.is_comm.comm ⟨_, Subgroup.mem_subgroupOf.mp x.2⟩
          ⟨_, Subgroup.mem_subgroupOf.mp y.2⟩)
      · exact Subtype.ext (by simpa using hE.2 _ (Subgroup.mem_subgroupOf.mp hx))
    · rw [← hcard]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv

omit [Finite G] in
theorem isComponent_map_subtype {H : Subgroup G} [hH : H.Normal] {K : Subgroup H}
    (hK : IsComponent K) : IsComponent (K.map H.subtype) :=
  ⟨LocalCores.isQuasisimple_of_mulEquiv (K.equivMapOfInjective H.subtype H.subtype_injective)
      hK.1, hK.2.trans' hH.isSubnormal⟩

theorem pRank_eq_one_of_forall (hO : CFSG.pPrimeCore 3 G = ⊥) {z : G} (hz : orderOf z = 3)
    (hwc : ∀ g : G, (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) →
      (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z)
    (hno : ∀ L : Subgroup G, IsComponent L →
      ¬ L ≤ Subgroup.normalClosure ((Subgroup.zpowers z : Subgroup G) : Set G)) :
    CFSG.Open.pRank 3 (Subgroup.normalClosure ((Subgroup.zpowers z : Subgroup G) : Set G)) =
      1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := Subgroup.zpowers z with hZ
  set H := Subgroup.normalClosure (Z : Set G) with hH
  have hZH : Z ≤ H := Subgroup.le_normalClosure
  have hlayer : layer H = ⊥ := by
    apply sSup_eq_bot.mpr
    intro K hK
    exact (hno _ (isComponent_map_subtype hK) (Subgroup.map_subtype_le K)).elim
  have hcore : CFSG.pPrimeCore 3 H = ⊥ := by
    have hsub : ((CFSG.pPrimeCore 3 H).map H.subtype).IsSubnormal :=
      (CFSG.pPrimeCore_normal (p := 3) (G := H)).isSubnormal.trans'
        (Subgroup.normalClosure_normal).isSubnormal
    have hcop : Nat.Coprime 3 (Nat.card ((CFSG.pPrimeCore 3 H).map H.subtype)) := by
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hle := GH74.GLS.le_pPrimeCore_of_subnormal 3 hsub hcop
    rw [hO, le_bot_iff] at hle
    exact Subgroup.map_injective H.subtype_injective (by rw [hle, Subgroup.map_bot])
  have hchar := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot H 3 hcore hlayer
  set O₃ := (CFSG.pCore 3 H).map H.subtype with hO₃
  have : O₃.Normal := map_subtype_normal_of_characteristic (CFSG.pCore 3 H)
  have hO₃p : IsPGroup 3 O₃ := (CFSG.pCore_isPGroup (p := 3) (G := H)).map _
  have hZp : IsPGroup 3 Z := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hsup : IsPGroup 3 (Z ⊔ O₃ : Subgroup G) := hZp.to_sup_of_normal_right hO₃p
  have hcen := le_centralizer_of_isPGroup hz hwc hsup
    (Subgroup.mem_sup_left (Subgroup.mem_zpowers z))
  have hZO : Z ≤ O₃ := by
    intro x hx
    have hxH : x ∈ H := hZH hx
    have h1 : (⟨x, hxH⟩ : H) ∈ Subgroup.centralizer ((CFSG.pCore 3 H : Subgroup H) : Set H) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      apply Subtype.ext
      have hyO : (y : G) ∈ O₃ := ⟨y, hy, rfl⟩
      have h2 := Subgroup.mem_centralizer_iff.mp (hcen (Subgroup.mem_sup_right hyO)) x hx
      exact h2.symm
    exact ⟨_, hchar h1, rfl⟩
  have hZn : Z.Normal := by
    refine ⟨fun x hx g => ?_⟩
    have hle : Z.map (MulAut.conj g).toMonoidHom ≤ O₃ := by
      rintro _ ⟨y, hy, rfl⟩
      exact this.conj_mem _ (hZO hy) g
    have heq := map_conj_eq_of_le hwc hO₃p hZO hle
    have hmem : g * x * g⁻¹ ∈ Z.map (MulAut.conj g).toMonoidHom := ⟨x, hx, rfl⟩
    rwa [heq] at hmem
  have hHZ : H = Z := Subgroup.normalClosure_eq_self Z
  rw [hHZ]
  apply le_antisymm
  · refine CFSG.SectionRank.pRank_le (by norm_num) fun E hEZ _ => ?_
    calc Nat.card E ≤ Nat.card Z := Subgroup.card_le_of_le hEZ
      _ = 3 ^ 1 := by rw [Nat.card_zpowers, hz, pow_one]
  · refine CFSG.SectionRank.le_pRank (by norm_num) le_rfl ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
      (by rw [Nat.card_zpowers, hz, pow_one])
    · obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        show z ^ 3 = 1 by rw [← hz]; exact pow_orderOf_eq_one z, one_zpow]

omit [Finite G] in
theorem exists_component_not_le_centralizer {Z : Subgroup G} {L₀ : Subgroup G}
    (hL₀ : IsComponent L₀) (hL₀H : L₀ ≤ Subgroup.normalClosure (Z : Set G)) :
    ∃ L : Subgroup G, IsComponent L ∧ L ≤ Subgroup.normalClosure (Z : Set G) ∧
      ¬ Z ≤ Subgroup.centralizer (L : Set G) := by
  by_contra hcon
  push Not at hcon
  have hH : Subgroup.normalClosure (Z : Set G) ≤ Subgroup.centralizer (L₀ : Set G) := by
    rw [Subgroup.normalClosure, Subgroup.closure_le]
    intro y hy
    obtain ⟨a, ha, hay⟩ := Group.mem_conjugatesOfSet_iff.mp hy
    obtain ⟨g, rfl⟩ := isConj_iff.mp hay
    set L' := L₀.map (MulAut.conj g⁻¹).toMonoidHom with hL'
    have hL'c : IsComponent L' := LocalCores.isComponent_map_mulEquiv (MulAut.conj g⁻¹) hL₀
    have hL'H : L' ≤ Subgroup.normalClosure (Z : Set G) := by
      rintro _ ⟨l, hl, rfl⟩
      exact (Subgroup.normalClosure_normal).conj_mem _ (hL₀H hl) g⁻¹
    have haC := hcon L' hL'c hL'H ha
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : g⁻¹ * l * g⁻¹⁻¹ ∈ L' := ⟨l, hl, rfl⟩
    have h1 := Subgroup.mem_centralizer_iff.mp haC _ hl'
    calc l * (g * a * g⁻¹) = g * ((g⁻¹ * l * g⁻¹⁻¹) * a) * g⁻¹ := by group
      _ = g * (a * (g⁻¹ * l * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * a * g⁻¹ * l := by group
  have hab : ∀ x ∈ L₀, ∀ y ∈ L₀, x * y = y * x := fun x hx y hy =>
    (Subgroup.mem_centralizer_iff.mp (hH (hL₀H hy)) x hx)
  obtain ⟨-, -, ⟨u, v, huv⟩⟩ := hL₀.1
  obtain ⟨u', rfl⟩ := QuotientGroup.mk_surjective u
  obtain ⟨v', rfl⟩ := QuotientGroup.mk_surjective v
  apply huv
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
  congr 1
  exact Subtype.ext (hab _ u'.2 _ v'.2)

theorem mem_normalizer_of_le {Z L : Subgroup G}
    (hwc : ∀ g : G, Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) →
      Z.map (MulAut.conj g).toMonoidHom = Z)
    (hL : IsComponent L) (hZL : Z ≤ L) (hZC : ¬ Z ≤ Subgroup.centralizer (L : Set G)) (g : G) :
    g ∈ Subgroup.normalizer (L : Set G) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  by_contra hne
  have hLg : IsComponent (L.map (MulAut.conj g).toMonoidHom) :=
    LocalCores.isComponent_map_mulEquiv (MulAut.conj g) hL
  have hc := (LocalCores.distinct_components_commute hLg hL).resolve_left hne
  have hLgC : L.map (MulAut.conj g).toMonoidHom ≤ Subgroup.centralizer (L : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hc
  have hZg : Z.map (MulAut.conj g).toMonoidHom ≤ L.map (MulAut.conj g).toMonoidHom :=
    Subgroup.map_mono hZL
  have hZgN : Z.map (MulAut.conj g).toMonoidHom ≤ Subgroup.normalizer (Z : Set G) :=
    (hZg.trans hLgC).trans ((Subgroup.centralizer_le hZL).trans
      (Subgroup.centralizer_le_normalizer _))
  have heq := hwc g hZgN
  apply hZC
  calc Z = Z.map (MulAut.conj g).toMonoidHom := heq.symm
    _ ≤ _ := hZg.trans hLgC

omit [Finite G] in
theorem normalizerMonoidHom_eq_conj {L : Subgroup G} (x : L) :
    L.normalizerMonoidHom ⟨x, Subgroup.le_normalizer x.2⟩ = MulAut.conj x := by
  ext y
  rfl

theorem mem_zpowers_of_mem_normalizer {z : G} (hz : orderOf z = 3)
    (hwc : ∀ g : G, (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) →
      (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z)
    {L : Subgroup G} (hzN : z ∈ Subgroup.normalizer (L : Set G)) (x : L)
    (hx : MulAut.conj x * L.normalizerMonoidHom ⟨z, hzN⟩ * (MulAut.conj x)⁻¹ ∈
      Subgroup.normalizer ((Subgroup.zpowers (L.normalizerMonoidHom ⟨z, hzN⟩) :
        Subgroup (MulAut L)) : Set (MulAut L))) :
    MulAut.conj x * L.normalizerMonoidHom ⟨z, hzN⟩ * (MulAut.conj x)⁻¹ ∈
      Subgroup.zpowers (L.normalizerMonoidHom ⟨z, hzN⟩) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Finite (MulAut L) := Finite.of_injective (fun σ : MulAut L => (σ : L → L))
    (fun σ τ h => MulEquiv.ext (congrFun h))
  set N := Subgroup.normalizer (L : Set G) with hN
  set φ := L.normalizerMonoidHom with hφ
  set σ := φ ⟨z, hzN⟩ with hσ
  have hxN : (x : G) ∈ N := Subgroup.le_normalizer x.2
  have hφx : φ ⟨x, hxN⟩ = MulAut.conj x := normalizerMonoidHom_eq_conj x
  set z' := (x : G) * z * (x : G)⁻¹ with hz'
  have hz'N : z' ∈ N := N.mul_mem (N.mul_mem hxN hzN) (N.inv_mem hxN)
  have hσ' : MulAut.conj x * σ * (MulAut.conj x)⁻¹ = φ ⟨z', hz'N⟩ := by
    rw [← hφx, ← map_inv, ← map_mul, ← map_mul]
    rfl
  set σ' := MulAut.conj x * σ * (MulAut.conj x)⁻¹ with hσ'def
  have hz3 : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
  have hσ3 : σ ^ 3 = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨z, hzN⟩ : N) ^ 3 = 1 := Subtype.ext (by simpa using hz3)
    rw [this, map_one]
  have hσ'3 : σ' ^ 3 = 1 := by
    rw [hσ'def, conj_pow, hσ3, mul_one, mul_inv_cancel]
  by_cases hσ1 : σ = 1
  · rw [hσ'def, hσ1, mul_one, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hσo : orderOf σ = 3 := orderOf_eq_prime hσ3 hσ1
  have hcomm : σ' * σ = σ * σ' := commute_of_mem_zpowers hσo ⟨1, by rw [pow_one]; exact hσ'3⟩
    ((Subgroup.mem_normalizer_iff.mp hx σ).mp (Subgroup.mem_zpowers σ))
  set Y := Subgroup.zpowers z ⊔ Subgroup.zpowers z' with hY
  set C : Subgroup G := ((Subgroup.centralizer ({σ} : Set (MulAut L))).comap φ).map N.subtype
    with hC
  have hzC : z ∈ C := ⟨⟨z, hzN⟩, Subgroup.mem_centralizer_singleton_iff.mpr rfl, rfl⟩
  have hz'C : z' ∈ C := ⟨⟨z', hz'N⟩, by
    rw [SetLike.mem_coe, Subgroup.mem_comap, ← hσ', Subgroup.mem_centralizer_singleton_iff]
    exact hcomm, rfl⟩
  have hYC : Y ≤ C := sup_le (Subgroup.zpowers_le.mpr hzC) (Subgroup.zpowers_le.mpr hz'C)
  have hZp : IsPGroup 3 (Subgroup.zpowers z) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz, pow_one])
  have hz'o : orderOf z' = 3 := by
    rw [hz', ← hz, ← MulAut.conj_apply]
    exact MulEquiv.orderOf_eq _ z
  have hZ'p : IsPGroup 3 (Subgroup.zpowers z') :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hz'o, pow_one])
  obtain ⟨S, hS, hZS⟩ := Sec13.Item134SylowBarProof.exists_isSylowOf_le
    (le_sup_left : Subgroup.zpowers z ≤ Y) hZp
  obtain ⟨S', hS', hZ'S'⟩ := Sec13.Item134SylowBarProof.exists_isSylowOf_le
    (le_sup_right : Subgroup.zpowers z' ≤ Y) hZ'p
  obtain ⟨m, hmY, hSm⟩ := Sec13.Item134SylowBarProof.exists_conj_of_isSylowOf hS hS'
  have hle : (Subgroup.zpowers z).map (MulAut.conj (m⁻¹ * (x : G))).toMonoidHom ≤ S := by
    rintro _ ⟨w, hw, rfl⟩
    have hw' : (x : G) * w * (x : G)⁻¹ ∈ Subgroup.zpowers z' := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
      rw [hz', ← conj_zpow]
      exact Subgroup.zpow_mem_zpowers _ k
    have h1 := hZ'S' hw'
    rw [hSm] at h1
    obtain ⟨s, hs, hse⟩ := h1
    have e : (MulAut.conj (m⁻¹ * (x : G))).toMonoidHom w = s := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hse ⊢
      rw [show m⁻¹ * (x : G) * w * (m⁻¹ * (x : G))⁻¹ = m⁻¹ * ((x : G) * w * (x : G)⁻¹) * m by
        group, ← hse]
      group
    rw [e]
    exact hs
  have heq := map_conj_eq_of_le hwc hS.isPGroup hZS hle
  have hmN : m ∈ N := by
    obtain ⟨n, -, hn⟩ := hYC hmY
    rw [← hn]
    exact n.2
  have hmz : (m⁻¹ * (x : G)) * z * (m⁻¹ * (x : G))⁻¹ ∈ Subgroup.zpowers z := by
    have : (m⁻¹ * (x : G)) * z * (m⁻¹ * (x : G))⁻¹ ∈
        (Subgroup.zpowers z).map (MulAut.conj (m⁻¹ * (x : G))).toMonoidHom :=
      ⟨z, Subgroup.mem_zpowers z, rfl⟩
    rwa [heq] at this
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmz
  have hmzN : (m⁻¹ * (x : G)) * z * (m⁻¹ * (x : G))⁻¹ ∈ N := by
    rw [← hk]
    exact N.zpow_mem hzN k
  have hφk : (φ ⟨m, hmN⟩)⁻¹ * σ' * φ ⟨m, hmN⟩ = σ ^ k := by
    have e1 : (⟨m, hmN⟩ : N)⁻¹ * ⟨z', hz'N⟩ * ⟨m, hmN⟩ = ⟨z, hzN⟩ ^ k := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, SubgroupClass.coe_zpow]
      rw [hk, hz']
      group
    rw [hσ', ← map_inv, ← map_mul, ← map_mul, e1, map_zpow]
  have hmC : φ ⟨m, hmN⟩ * σ = σ * φ ⟨m, hmN⟩ := by
    obtain ⟨n, hn, hne⟩ := hYC hmY
    have : n = ⟨m, hmN⟩ := Subtype.ext hne
    rw [this] at hn
    exact Subgroup.mem_centralizer_singleton_iff.mp hn
  have hσ'eq : σ' = σ ^ k := by
    have e2 : σ' = φ ⟨m, hmN⟩ * σ ^ k * (φ ⟨m, hmN⟩)⁻¹ := by
      rw [← hφk]
      group
    rw [e2, ← conj_zpow]
    congr 1
    calc φ ⟨m, hmN⟩ * σ * (φ ⟨m, hmN⟩)⁻¹ = σ * φ ⟨m, hmN⟩ * (φ ⟨m, hmN⟩)⁻¹ := by rw [hmC]
      _ = σ := by group
  rw [hσ'eq]
  exact Subgroup.zpow_mem_zpowers σ k

theorem false_of_not_mem {z : G} (hz : orderOf z = 3)
    (hwc : ∀ g : G, (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
        Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) →
      (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom = Subgroup.zpowers z)
    {L : Subgroup G} (hzN : z ∈ Subgroup.normalizer (L : Set G)) (b t : L)
    (hb : L.normalizerMonoidHom ⟨z, hzN⟩ = MulAut.conj b)
    (ht : t * b * t⁻¹ * b ∈ Subgroup.center L) (hσ1 : L.normalizerMonoidHom ⟨z, hzN⟩ ≠ 1)
    (hzL : z ∉ L) : False := by
  classical
  set a := z * (b : G)⁻¹ with ha
  set c : L := t * b * t⁻¹ * b with hc
  have haC : ∀ l : L, a * l = l * a := by
    intro l
    have h1 := congrArg (fun σ : MulAut L => ((σ (b⁻¹ * l * b) : L) : G)) hb
    simp only [normalizerMonoidHom_apply_coe, MulAut.conj_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    have h2 : z * ((b : G)⁻¹ * l * b) * z⁻¹ = l := by
      rw [h1]
      group
    calc a * l = z * ((b : G)⁻¹ * l * b) * z⁻¹ * (z * (b : G)⁻¹) := by rw [ha]; group
      _ = l * a := by rw [h2]
  have hcZ : ∀ l : L, (c : G) * l = l * c := fun l =>
    congrArg Subtype.val ((Subgroup.mem_center_iff.mp ht l).symm)
  have hzab : z = a * b := by rw [ha]; group
  have htb : (t : G) * b * (t : G)⁻¹ = c * (b : G)⁻¹ := by
    rw [hc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have htz : (t : G) * z * (t : G)⁻¹ = a * (c * (b : G)⁻¹) := by
    rw [hzab, ← htb]
    calc (t : G) * (a * b) * (t : G)⁻¹ = (t * a) * b * (t : G)⁻¹ := by group
      _ = (a * t) * b * (t : G)⁻¹ := by rw [haC t]
      _ = a * ((t : G) * b * (t : G)⁻¹) := by group
  have hcb : (c : G) * b = b * c := hcZ b
  have hab : a * b = b * a := haC b
  have hac : a * c = c * a := haC c
  have hcomm : (t : G) * z * (t : G)⁻¹ * z = z * ((t : G) * z * (t : G)⁻¹) := by
    rw [htz, hzab]
    have hcb' : (c : G) * (b : G)⁻¹ = (b : G)⁻¹ * c := by
      calc (c : G) * (b : G)⁻¹ = (b : G)⁻¹ * (b * c) * (b : G)⁻¹ := by group
        _ = (b : G)⁻¹ * (c * b) * (b : G)⁻¹ := by rw [hcb]
        _ = (b : G)⁻¹ * c := by group
    have hab' : a * (b : G)⁻¹ = (b : G)⁻¹ * a := by
      calc a * (b : G)⁻¹ = (b : G)⁻¹ * (b * a) * (b : G)⁻¹ := by group
        _ = (b : G)⁻¹ * (a * b) * (b : G)⁻¹ := by rw [hab]
        _ = (b : G)⁻¹ * a := by group
    calc a * (c * (b : G)⁻¹) * (a * b) = a * c * ((b : G)⁻¹ * a) * b := by group
      _ = a * c * (a * (b : G)⁻¹) * b := by rw [hab']
      _ = a * (c * a) * ((b : G)⁻¹ * b) := by group
      _ = a * (a * c) := by rw [← hac]; group
      _ = a * (a * c) * (b * (b : G)⁻¹) := by group
      _ = a * b * (a * (c * (b : G)⁻¹)) := by
          calc a * (a * c) * (b * (b : G)⁻¹) = a * a * (c * b) * (b : G)⁻¹ := by group
            _ = a * a * (b * c) * (b : G)⁻¹ := by rw [hcb]
            _ = a * (a * b) * (c * (b : G)⁻¹) := by group
            _ = a * (b * a) * (c * (b : G)⁻¹) := by rw [hab]
            _ = a * b * (a * (c * (b : G)⁻¹)) := by group
  have hZt : (Subgroup.zpowers z).map (MulAut.conj (t : G)).toMonoidHom =
      Subgroup.zpowers ((t : G) * z * (t : G)⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hmem : (t : G) * z * (t : G)⁻¹ ∈ Subgroup.zpowers z := by
    have hle : (Subgroup.zpowers z).map (MulAut.conj (t : G)).toMonoidHom ≤
        Subgroup.normalizer ((Subgroup.zpowers z : Subgroup G) : Set G) := by
      rw [hZt, Subgroup.zpowers_le]
      exact Sec13.Item134SylowBarProof.mem_normalizer_zpowers_of_mem_centralizer
        (Subgroup.mem_centralizer_singleton_iff.mpr hcomm)
    have heq := hwc _ hle
    rw [hZt] at heq
    rw [← heq]
    exact Subgroup.mem_zpowers _
  obtain ⟨j, hj, hjz⟩ := Finset.mem_image.mp (mem_zpowers_iff_mem_range_orderOf.mp hmem)
  rw [hz, Finset.mem_range] at hj
  have hcL : (c : G) ∈ L := c.2
  have hbL : (b : G) ∈ L := b.2
  interval_cases j
  ·
    rw [pow_zero, htz] at hjz
    apply hzL
    have haL : a = b * (c : G)⁻¹ := by
      calc a = a * (c * (b : G)⁻¹) * (b * (c : G)⁻¹) := by group
        _ = b * (c : G)⁻¹ := by rw [← hjz]; group
    rw [hzab, haL]
    exact L.mul_mem (L.mul_mem hbL (L.inv_mem hcL)) hbL
  ·
    rw [pow_one, htz, hzab] at hjz
    have hcb2 : (c : G) = b * b := by
      calc (c : G) = a⁻¹ * (a * b) * b := by
            rw [hjz]
            group
        _ = b * b := by group
    have hb2 : b * b ∈ Subgroup.center L := by
      have : c = b * b := Subtype.ext (by rw [hcb2]; rfl)
      rw [← this]
      exact ht
    apply hσ1
    have hσ2 : (L.normalizerMonoidHom ⟨z, hzN⟩) ^ 2 = 1 := by
      rw [hb, pow_two, ← map_mul]
      ext l
      simp only [MulAut.conj_apply, MulAut.one_apply]
      have := Subgroup.mem_center_iff.mp hb2 l
      rw [← this]
      group
    have hσ3 : (L.normalizerMonoidHom ⟨z, hzN⟩) ^ 3 = 1 := by
      rw [← map_pow]
      have : (⟨z, hzN⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 :=
        Subtype.ext (by simpa using (show z ^ 3 = 1 by rw [← hz]; exact pow_orderOf_eq_one z))
      rw [this, map_one]
    calc L.normalizerMonoidHom ⟨z, hzN⟩
        = (L.normalizerMonoidHom ⟨z, hzN⟩) ^ 3 * ((L.normalizerMonoidHom ⟨z, hzN⟩) ^ 2)⁻¹ := by
          group
      _ = 1 := by rw [hσ2, hσ3]; group
  ·
    rw [htz, hzab] at hjz
    apply hzL
    have haL : a = c * ((b : G) ^ 3)⁻¹ := by
      have e1 : (a * b) ^ 2 = a * a * (b * b) := by
        rw [pow_two]
        calc a * b * (a * b) = a * (b * a) * b := by group
          _ = a * (a * b) * b := by rw [hab]
          _ = a * a * (b * b) := by group
      rw [e1] at hjz
      calc a = a⁻¹ * (a * a * (b * b)) * ((b : G) ^ 3)⁻¹ * b := by
            simp only [pow_succ, pow_zero, one_mul]
            group
        _ = a⁻¹ * (a * (c * (b : G)⁻¹)) * ((b : G) ^ 3)⁻¹ * b := by rw [hjz]
        _ = c * ((b : G) ^ 3)⁻¹ := by
            simp only [pow_succ, pow_zero, one_mul]
            have hcb' : (c : G) * (b : G)⁻¹ = (b : G)⁻¹ * c := by
              calc (c : G) * (b : G)⁻¹ = (b : G)⁻¹ * (b * c) * (b : G)⁻¹ := by group
                _ = (b : G)⁻¹ * (c * b) * (b : G)⁻¹ := by rw [hcb]
                _ = (b : G)⁻¹ * c := by group
            calc a⁻¹ * (a * (c * (b : G)⁻¹)) * (b * b * b : G)⁻¹ * b
                = (c * (b : G)⁻¹) * (b * b * b : G)⁻¹ * b := by group
              _ = c * ((b : G)⁻¹ * (b * b * b : G)⁻¹ * b) := by group
              _ = c * (b * b * b : G)⁻¹ := by group
    rw [hzab, haL]
    exact L.mul_mem (L.mul_mem hcL (L.inv_mem (L.pow_mem hbL 3))) hbL

end Item432Proof

open Item432Proof

end CFSG.RankThree.PartTwo.Sec4
