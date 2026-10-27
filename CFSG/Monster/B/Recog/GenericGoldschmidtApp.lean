module

public import CFSG.Open.GoldschmidtStronglyClosedAbelianMilestoneDefs
public import CFSG.LocalAnalysis.ComponentClassification.Layer
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.LocalCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.GroupTheory.PCore.Defs

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Recog

open CFSG.Open CFSG.ComponentClassification

namespace GoldschmidtApp

variable {G : Type*} [Group G]

theorem goldschmidtOddCore_eq_oddCore (H : Type*) [Group H] :
    goldschmidtOddCore H = CFSG.oddCore H := rfl

theorem openPCore_characteristic (H : Type*) [Group H] :
    (CFSG.Open.pCore 2 H).Characteristic := by
  rw [CFSG.RankThreeCoreUniqueness.Helpers.pCore_eq_sSup]
  exact CFSG.pCore_characteristic (p := 2) (G := H)

theorem natCard_sup_mul_natCard_inf_of_le_normalizer {A B : Subgroup G}
    (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    Nat.card (A ⊔ B : Subgroup G) * Nat.card (A ⊓ B : Subgroup G) = Nat.card A * Nat.card B := by
  have hrel := Subgroup.relIndex_mul_card A B
  have hrel' := Subgroup.relIndex_mul_card A (A ⊔ B)
  rw [inf_eq_left.mpr le_sup_left] at hrel'
  have : (A.subgroupOf (B ⊔ A)).Normal := Subgroup.normal_subgroupOf_sup_of_le_normalizer hB
  have : (A.subgroupOf B).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hB
  have e := QuotientGroup.quotientInfEquivProdNormalizerQuotient B A hB
  have hidx : A.relIndex B = A.relIndex (A ⊔ B) := by
    rw [Subgroup.relIndex, Subgroup.relIndex, Subgroup.index, Subgroup.index, sup_comm]
    exact Nat.card_congr e.toEquiv
  rw [← hrel', ← hrel, hidx]
  ring

theorem conj_mem_centralizer {K : Subgroup G} {n c : G}
    (hn : n ∈ Subgroup.normalizer (K : Set G)) (hc : c ∈ Subgroup.centralizer (K : Set G)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (K : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro k hk
  have hk' : n⁻¹ * k * n ∈ K := by
    have h := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hn) k).1 hk
    rwa [inv_inv] at h
  have e := hc _ hk'
  calc k * (n * c * n⁻¹) = n * ((n⁻¹ * k * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * k * n)) * n⁻¹ := by rw [e]
    _ = n * c * n⁻¹ * k := by group

theorem mem_normalizer_inf [Finite G] {A B : Subgroup G} {n : G}
    (hA : n ∈ Subgroup.normalizer (A : Set G)) (hB : n ∈ Subgroup.normalizer (B : Set G)) :
    n ∈ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) :=
  Subgroup.mem_normalizer_fintype fun x hx =>
    ⟨(Subgroup.mem_normalizer_iff.1 hA x).1 hx.1, (Subgroup.mem_normalizer_iff.1 hB x).1 hx.2⟩

theorem map_center_eq_inf_centralizer (K : Subgroup G) :
    (Subgroup.center K).map K.subtype = K ⊓ Subgroup.centralizer (K : Set G) := by
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    refine ⟨z.2, Subgroup.mem_centralizer_iff.2 fun k hk => ?_⟩
    have := Subgroup.mem_center_iff.1 hz ⟨k, hk⟩
    exact congrArg Subtype.val this
  · rintro ⟨hxK, hxC⟩
    refine ⟨⟨x, hxK⟩, Subgroup.mem_center_iff.2 fun k => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.1 hxC k k.2

theorem exists_sylow_eq_of_normalizer_le [Finite G] {p : ℕ} [Fact p.Prime] {P : Subgroup G}
    (hP : IsPGroup p P) (hN : Subgroup.normalizer (P : Set G) ≤ P) :
    ∃ Q : Sylow p G, (Q : Subgroup G) = P := by
  obtain ⟨Q, hPQ⟩ := hP.exists_le_sylow
  refine ⟨Q, ?_⟩
  have : Group.IsNilpotent Q := Q.isPGroup'.isNilpotent
  have hself : Subgroup.normalizer ((P.subgroupOf Q : Subgroup Q) : Set Q) = P.subgroupOf Q := by
    rw [← Subgroup.subgroupOf_normalizer_eq hPQ]
    ext x
    simp only [Subgroup.mem_subgroupOf]
    exact ⟨fun hx => hN hx, fun hx => P.le_normalizer hx⟩
  have htop := normalizerCondition_iff_only_full_group_self_normalizing.1
    Group.normalizerCondition_of_isNilpotent _ hself
  exact le_antisymm (Subgroup.subgroupOf_eq_top.1 htop) hPQ

theorem card_dvd_card_quotient_center_of_inf_centralizer_eq_bot {Y : Type*} [Group Y] [Finite Y]
    {K : Subgroup Y} (hK : IsComponentOf K ⊤) {H : Subgroup Y} (hHE : H ≤ goldschmidtLayer Y)
    (hHK : H ⊓ Subgroup.centralizer (K : Set Y) = ⊥) :
    Nat.card H ∣ Nat.card (K ⧸ Subgroup.center K) := by
  have hKE : K ≤ goldschmidtLayer Y := Layer.component_le hK
  have hEK : goldschmidtLayer Y ≤ Subgroup.normalizer (K : Set Y) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKE).1 (Layer.normal_component hK)
  have hEC : goldschmidtLayer Y ≤ Subgroup.normalizer
      ((goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) : Set Y) :=
    fun e he => Subgroup.mem_normalizer_fintype fun c hc =>
      ⟨(goldschmidtLayer Y).mul_mem ((goldschmidtLayer Y).mul_mem he hc.1)
        ((goldschmidtLayer Y).inv_mem he), conj_mem_centralizer (hEK he) hc.2⟩
  have hdisj : Disjoint (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)) H := by
    rw [disjoint_iff, ← le_bot_iff, ← hHK]
    exact fun x hx => ⟨hx.2, hx.1.2⟩
  have h1 := CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer _ H
    (hHE.trans hEC) hdisj
  have h1' : Nat.card (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) *
      Nat.card H ∣ Nat.card (goldschmidtLayer Y) :=
    h1 ▸ Subgroup.card_dvd_of_le (sup_le inf_le_left hHE)
  have hsup : (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)) ⊔ K = goldschmidtLayer Y := by
    refine le_antisymm (sup_le inf_le_left hKE) (sSup_le fun K₂ hK₂ => ?_)
    by_cases hne : K₂ = K
    · exact hne ▸ le_sup_right
    · exact le_sup_of_le_left (le_inf (Layer.component_le hK₂)
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
          (LocalComponents.commute_of_ne K₂ K hK₂ hK hne)))
  have hinf : ((goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y)) ⊓ K : Subgroup Y) =
      (Subgroup.center K).map K.subtype := by
    rw [map_center_eq_inf_centralizer, inf_comm, ← inf_assoc, inf_eq_left.mpr hKE]
  have h2 := natCard_sup_mul_natCard_inf_of_le_normalizer (hKE.trans hEC)
  rw [hsup, hinf, Subgroup.card_map_of_injective K.subtype_injective] at h2
  have h3 := (Subgroup.center K).card_mul_index
  obtain ⟨m, hm⟩ := h1'
  have hpos : 0 < Nat.card (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) *
      Nat.card (Subgroup.center K) := Nat.mul_pos Nat.card_pos Nat.card_pos
  refine ⟨m, Nat.eq_of_mul_eq_mul_left hpos ?_⟩
  calc Nat.card (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) *
        Nat.card (Subgroup.center K) * (Subgroup.center K).index =
      Nat.card (goldschmidtLayer Y ⊓ Subgroup.centralizer (K : Set Y) : Subgroup Y) *
        Nat.card K := by
        rw [mul_assoc, h3]
    _ = Nat.card (goldschmidtLayer Y) * Nat.card (Subgroup.center K) := h2.symm
    _ = _ := by rw [hm]; ring

theorem normal_map_of_characteristic {X Y : Type*} [Group X] [Group Y] {M : Subgroup X}
    [M.Normal] (φ : M ≃* Y) {A : Subgroup Y} (hA : A.Characteristic) :
    (A.map (M.subtype.comp φ.symm.toMonoidHom)).Normal := by
  constructor
  rintro _ ⟨y, hy, rfl⟩ x
  have hβ : (φ.symm.trans ((MulAut.conjNormal x).trans φ)) y ∈ A := by
    rw [← Subgroup.characteristic_iff_map_eq.1 hA (φ.symm.trans ((MulAut.conjNormal x).trans φ))]
    exact Subgroup.mem_map_of_mem _ hy
  refine ⟨_, hβ, ?_⟩
  simp [MulAut.conjNormal_apply]

end GoldschmidtApp

open GoldschmidtApp

theorem normal_of_goldschmidt_conclusion {X : Type} [Group X] [Finite X] (S : Sylow 2 X)
    {V : Subgroup X} (hVS : V ≤ S) (hVab : IsMulCommutative V)
    (hGold :
      let M : Subgroup X := Subgroup.normalClosure (V : Set X)
      let π := QuotientGroup.mk' (CFSG.Open.goldschmidtOddCore M)
      let T := ((S : Subgroup X).subgroupOf M).map π ⊓
        CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M)
      CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
          CFSG.Open.goldschmidtLayer (M ⧸ CFSG.Open.goldschmidtOddCore M) = ⊤ ∧
      (V.subgroupOf M).map π =
        CFSG.Open.pCore 2 (M ⧸ CFSG.Open.goldschmidtOddCore M) ⊔
          Subgroup.closure {t | t ∈ T ∧ t ^ 2 = 1} ∧
      ∀ K : Subgroup (M ⧸ CFSG.Open.goldschmidtOddCore M), CFSG.Open.IsComponentOf K ⊤ →
        CFSG.Open.goldschmidtSimpleType (K ⧸ Subgroup.center K))
    (hO : CFSG.oddCore X = ⊥)
    (hQB1 : Subgroup.centralizer (V : Set X) ≤ V)
    (hQB1' : ∀ W : Subgroup X, W ≤ V →
      Subgroup.normalizer (V : Set X) ≤ Subgroup.normalizer (W : Set X) → W = ⊥ ∨ W = V)
    (hQB2 : ∀ R : Subgroup X, V ≤ R → R ≤ Subgroup.normalizer (V : Set X) →
      Subgroup.normalizer (V : Set X) ≤ Subgroup.normalizer (R : Set X) →
        R = V ∨ R = Subgroup.normalizer (V : Set X))
    (hAr : ∀ (L : Type) [Group L] [Finite L], CFSG.Open.goldschmidtSimpleType L →
      Nat.card (Subgroup.normalizer (V : Set X)) ∣ Nat.card L → Nat.card L ∣ Nat.card X → False) :
    V.Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, hGb, hGc⟩ := hGold
  have hOM : goldschmidtOddCore (Subgroup.normalClosure (V : Set X)) = ⊥ := by
    have h := OddCore.normal_intersection X (Subgroup.normalClosure (V : Set X))
    have h' : componentClassificationOddCore X = ⊥ := hO
    rw [h', inf_bot_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h
  set M : Subgroup X := Subgroup.normalClosure (V : Set X) with hM
  have hVM : V ≤ M := Subgroup.le_normalClosure
  have hπ : Function.Injective (QuotientGroup.mk' (goldschmidtOddCore M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOM]
  obtain ⟨φ, hφ⟩ : ∃ φ : M ≃* M ⧸ goldschmidtOddCore M,
      ∀ m, φ m = QuotientGroup.mk' (goldschmidtOddCore M) m :=
    ⟨MulEquiv.ofBijective _ ⟨hπ, QuotientGroup.mk'_surjective _⟩, fun _ => rfl⟩
  obtain ⟨ι, hιdef⟩ : ∃ ι : M ⧸ goldschmidtOddCore M →* X,
      ι = M.subtype.comp φ.symm.toMonoidHom := ⟨_, rfl⟩
  have hι : Function.Injective ι := by
    rw [hιdef]
    exact M.subtype_injective.comp φ.symm.injective
  have hιπ : ∀ m : M, ι (QuotientGroup.mk' (goldschmidtOddCore M) m) = m := by
    intro m
    rw [hιdef, ← hφ]
    simp
  have hιM : ∀ y, ι y ∈ M := by
    intro y
    rw [hιdef]
    exact (φ.symm y).2
  have hnormal : ∀ A : Subgroup (M ⧸ goldschmidtOddCore M), A.Characteristic →
      (A.map ι).Normal := by
    intro A hA
    rw [hιdef]
    exact normal_map_of_characteristic φ hA
  set E := goldschmidtLayer (M ⧸ goldschmidtOddCore M) with hE
  have hEX : (E.map ι).Normal := hnormal E (Layer.characteristic _)
  have hOY : goldschmidtOddCore (M ⧸ goldschmidtOddCore M) = ⊥ := OddCore.quotient_corefree M
  have hV2 : IsPGroup 2 V := S.isPGroup'.to_le hVS
  have hEK : ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
      E ≤ Subgroup.normalizer (K : Set (M ⧸ goldschmidtOddCore M)) := fun K hK =>
    (Subgroup.normal_subgroupOf_iff_le_normalizer (Layer.component_le hK)).1
      (Layer.normal_component hK)
  have hEbot : E = ⊥ := by
    by_contra hE1
    have h2E : 2 ∣ Nat.card E := by
      by_contra hodd
      have hle : E ≤ goldschmidtOddCore (M ⧸ goldschmidtOddCore M) :=
        OddCore.maximal _ E (Layer.normal _) (Nat.odd_iff.2 (Nat.two_dvd_ne_zero.1 hodd))
      rw [hOY] at hle
      exact hE1 (le_bot_iff.1 hle)
    obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' 2 h2E
    have he2 : orderOf (ι (e : M ⧸ goldschmidtOddCore M)) = 2 := by
      rw [orderOf_injective ι hι, Subgroup.orderOf_coe, he]
    have hZ : IsPGroup 2 (Subgroup.zpowers (ι (e : M ⧸ goldschmidtOddCore M))) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he2, pow_one])
    obtain ⟨P, hP⟩ := hZ.exists_le_sylow
    obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S P
    have hmemP : ι (e : M ⧸ goldschmidtOddCore M) ∈ ((g • S : Sylow 2 X) : Subgroup X) :=
      hg ▸ hP (Subgroup.mem_zpowers _)
    rw [Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hmemP
    obtain ⟨s, hsS, hs⟩ := hmemP
    have hs' : g * s * g⁻¹ = ι (e : M ⧸ goldschmidtOddCore M) := hs
    have hsE : s ∈ E.map ι := by
      have h := hEX.conj_mem _ ⟨e, e.2, rfl⟩ g⁻¹
      rwa [← hs', inv_inv, show g⁻¹ * (g * s * g⁻¹) * g = s by group] at h
    have hs2 : orderOf s = 2 := by
      rw [← he2, ← hs', ← MulAut.conj_apply, MulEquiv.orderOf_eq]
    obtain ⟨t, htE, hts⟩ := hsE
    have htT : t ∈ ((S : Subgroup X).subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) ⊓
        E := by
      refine ⟨⟨φ.symm t, ?_, ?_⟩, htE⟩
      · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        have e1 : ((φ.symm t : M) : X) = s := by
          rw [← hts, hιdef]
          rfl
        rw [e1]
        exact hsS
      · rw [← hφ, MulEquiv.apply_symm_apply]
    have ht2 : t ^ 2 = 1 := by
      rw [← orderOf_dvd_iff_pow_eq_one, ← orderOf_injective ι hι, hts, hs2]
    have htV : t ∈ (V.subgroupOf M).map (QuotientGroup.mk' (goldschmidtOddCore M)) := by
      rw [hGb]
      exact Subgroup.mem_sup_right (Subgroup.subset_closure ⟨htT, ht2⟩)
    obtain ⟨v, hv, hvt⟩ := htV
    have hsV : s ∈ V := by
      rw [← hts, ← hvt, hιπ]
      exact hv
    have hs1 : s ≠ 1 := by
      intro h
      rw [h, orderOf_one] at hs2
      exact absurd hs2 (by norm_num)
    have hVne : V ≠ ⊥ := fun h => hs1 ((Subgroup.mem_bot).1 (h ▸ hsV))
    have hnorm : ∀ (A : Subgroup X) [A.Normal] (n : X), n ∈ Subgroup.normalizer (A : Set X) :=
      fun A _ n => (Subgroup.normalizer_eq_top A).symm ▸ Subgroup.mem_top n
    have hVE : V ≤ E.map ι := by
      rcases hQB1' (V ⊓ E.map ι) inf_le_left
          (fun n hn => mem_normalizer_inf hn (hnorm _ n)) with h | h
      · have hmem : s ∈ V ⊓ E.map ι := ⟨hsV, ⟨t, htE, hts⟩⟩
        rw [h, Subgroup.mem_bot] at hmem
        exact absurd hmem hs1
      · exact h ▸ inf_le_right
    have hperf : commutator E = ⊤ := (Layer.perfect _).commutator_eq_top
    have hEnab : ¬ ∀ a b : E, a * b = b * a := by
      intro hab
      apply hE1
      have htop : (⊤ : Subgroup E) = ⊥ := by
        rw [← hperf, eq_bot_iff, commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
        exact hab a b
      rw [eq_bot_iff]
      intro x hx
      have h1 : (⟨x, hx⟩ : E) = 1 := (Subgroup.mem_bot).1 (htop ▸ Subgroup.mem_top _)
      exact (Subgroup.mem_bot).2 (congrArg Subtype.val h1)
    have hVC : V ⊓ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X) = ⊥ := by
      rcases hQB1' _ inf_le_left (fun n hn => mem_normalizer_inf hn
          (hnorm (Subgroup.centralizer ((E.map ι : Subgroup X) : Set X)) n)) with h | h
      · exact h
      · exfalso
        have hle : V ≤ Subgroup.centralizer ((E.map ι : Subgroup X) : Set X) := h ▸ inf_le_right
        have hEV : E.map ι ≤ V := (Subgroup.le_centralizer_iff.1 hle).trans hQB1
        apply hEnab
        intro a b
        apply Subtype.ext
        apply hι
        have ha : ι a ∈ V := hEV ⟨a, a.2, rfl⟩
        have hb : ι b ∈ V := hEV ⟨b, b.2, rfl⟩
        have hc := congrArg Subtype.val (hVab.is_comm.comm ⟨ι a, ha⟩ ⟨ι b, hb⟩)
        simpa only [Subgroup.coe_mul, map_mul] using hc
    have hcommV : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (hVab.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
    have hcomapE : ∀ {A : Subgroup X}, A ≤ E.map ι → A.comap ι ≤ E := by
      intro A hA y hy
      obtain ⟨e', he', he'y⟩ := hA hy
      rw [← hι he'y]
      exact he'
    rcases hQB2 (Subgroup.normalizer (V : Set X) ⊓ E.map ι) (le_inf Subgroup.le_normalizer hVE)
        inf_le_left (fun n hn => mem_normalizer_inf (Subgroup.le_normalizer hn) (hnorm _ n))
      with hRV | hRN
    ·
      have hVYE : V.comap ι ≤ E := hcomapE hVE
      have hP₀ : IsPGroup 2 ((V.comap ι).subgroupOf E) :=
        (hV2.comap_of_injective ι hι).comap_of_injective E.subtype E.subtype_injective
      have hP₀N : Subgroup.normalizer (((V.comap ι).subgroupOf E : Subgroup E) : Set E) ≤
          (V.comap ι).subgroupOf E := by
        intro x hx
        have hxN : ι x ∈ Subgroup.normalizer (V : Set X) := Subgroup.mem_normalizer_fintype
          fun v hv => by
            obtain ⟨y, hyE, hyv⟩ := hVE hv
            have hyP : (⟨y, hyE⟩ : E) ∈ (V.comap ι).subgroupOf E := by
              rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
              exact hyv ▸ hv
            have h := (Subgroup.mem_normalizer_iff.1 hx _).1 hyP
            rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at h
            rw [← hyv]
            simpa [map_mul, map_inv] using h
        have hxR : ι x ∈ Subgroup.normalizer (V : Set X) ⊓ E.map ι := ⟨hxN, ⟨x, x.2, rfl⟩⟩
        rw [hRV] at hxR
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap]
        exact hxR
      obtain ⟨Q, hQ⟩ := exists_sylow_eq_of_normalizer_le hP₀ hP₀N
      have hQcomm : ∀ a ∈ (Q : Subgroup E), ∀ b ∈ (Q : Subgroup E), a * b = b * a := by
        intro a ha b hb
        rw [hQ, Subgroup.mem_subgroupOf, Subgroup.mem_comap] at ha hb
        exact Subtype.ext (hι (by rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul,
          hcommV _ ha _ hb]))
      have hQc : Subgroup.normalizer ((Q : Subgroup E) : Set E) ≤
          Subgroup.centralizer ((Q : Subgroup E) : Set E) := by
        intro x hx
        have hxQ : x ∈ (Q : Subgroup E) := hQ ▸ hP₀N (hQ ▸ hx)
        exact Subgroup.mem_centralizer_iff.2 fun y hy => hQcomm y hy x hxQ
      have hker : commutator E ≤ (MonoidHom.transferSylow Q hQc).ker := by
        rw [commutator_def, Subgroup.commutator_le]
        intro a _ b _
        rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
        exact Subtype.ext (hQcomm _ (MonoidHom.transferSylow Q hQc a).2 _
          (MonoidHom.transferSylow Q hQc b).2)
      rw [hperf] at hker
      have hdisj := MonoidHom.ker_transferSylow_disjoint Q hQc (Q : Subgroup E) Q.isPGroup'
      rw [disjoint_iff, eq_top_iff.2 hker, top_inf_eq] at hdisj
      apply hVne
      rw [eq_bot_iff]
      intro v hv
      obtain ⟨y, hyE, hyv⟩ := hVE hv
      have hyQ : (⟨y, hyE⟩ : E) ∈ (Q : Subgroup E) := by
        rw [hQ, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
        exact hyv ▸ hv
      rw [hdisj, Subgroup.mem_bot] at hyQ
      have hy1 : y = 1 := congrArg Subtype.val hyQ
      rw [Subgroup.mem_bot, ← hyv, hy1, map_one]
    ·
      have hNE : Subgroup.normalizer (V : Set X) ≤ E.map ι := hRN ▸ inf_le_right
      have hNYE : (Subgroup.normalizer (V : Set X)).comap ι ≤ E := hcomapE hNE
      have hK : ∃ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ ∧
          (Subgroup.normalizer (V : Set X)).comap ι ⊓
            Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M)) = ⊥ := by
        by_contra hall
        push Not at hall
        have hKV : ∀ K : Subgroup (M ⧸ goldschmidtOddCore M), IsComponentOf K ⊤ →
            V.comap ι ≤ Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M)) := by
          intro K hK
          have hCK : ∀ n ∈ Subgroup.normalizer (V : Set X), n ∈ Subgroup.normalizer
              (((Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M))).map ι :
                Subgroup X) : Set X) := by
            intro n hn
            obtain ⟨e', he', rfl⟩ := hNE hn
            exact Subgroup.mem_normalizer_fintype fun x hx => by
              obtain ⟨c, hc, rfl⟩ := hx
              exact ⟨e' * c * e'⁻¹, conj_mem_centralizer (hEK K hK he') hc,
                by rw [map_mul, map_mul, map_inv]⟩
          rcases hQB1' (V ⊓ (Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M))).map ι)
              inf_le_left (fun n hn => mem_normalizer_inf hn (hCK n hn)) with hW | hW
          · exfalso
            apply hall K hK
            rw [eq_bot_iff]
            intro y hy
            have hr : ι y ∈ Subgroup.normalizer (V : Set X) := hy.1
            have hrC : ι y ∈
                (Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M))).map ι :=
              ⟨y, hy.2, rfl⟩
            have hcomm : ∀ v ∈ V, v * ι y = ι y * v := by
              intro v hv
              have h1 : ι y * v * (ι y)⁻¹ * v⁻¹ ∈ V :=
                V.mul_mem ((Subgroup.mem_normalizer_iff.1 hr v).1 hv) (V.inv_mem hv)
              have h2 : ι y * v * (ι y)⁻¹ * v⁻¹ ∈
                  (Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M))).map ι := by
                have hvn := hCK v (Subgroup.le_normalizer hv)
                have h3 := (Subgroup.mem_normalizer_iff.1 hvn _).1 (Subgroup.inv_mem _ hrC)
                have h4 := Subgroup.mul_mem _ hrC h3
                rwa [← mul_assoc, ← mul_assoc] at h4
              have h3 : ι y * v * (ι y)⁻¹ * v⁻¹ ∈
                  V ⊓ (Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M))).map ι :=
                ⟨h1, h2⟩
              rw [hW, Subgroup.mem_bot, mul_inv_eq_one, mul_inv_eq_iff_eq_mul] at h3
              exact h3.symm
            have hrV : ι y ∈ V := hQB1 (Subgroup.mem_centralizer_iff.2 hcomm)
            have h4 : ι y ∈
                V ⊓ (Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M))).map ι :=
              ⟨hrV, hrC⟩
            rw [hW, Subgroup.mem_bot] at h4
            exact (Subgroup.mem_bot).2 (hι (h4.trans (map_one ι).symm))
          · intro y hy
            obtain ⟨c, hc, hcy⟩ := (hW ▸ inf_le_right :
              V ≤ (Subgroup.centralizer (K : Set (M ⧸ goldschmidtOddCore M))).map ι) hy
            rw [← hι hcy]
            exact hc
        have hEV : E ≤ Subgroup.centralizer ((V.comap ι : Subgroup _) : Set _) :=
          sSup_le fun K hK => Subgroup.le_centralizer_iff.1 (hKV K hK)
        apply hVne
        rw [eq_bot_iff, ← hVC]
        refine le_inf le_rfl fun v hv => ?_
        rw [Subgroup.mem_centralizer_iff]
        rintro _ ⟨e', he', rfl⟩
        obtain ⟨y, hyE, hyv⟩ := hVE hv
        have hc := Subgroup.mem_centralizer_iff.1 (hEV he') y (show ι y ∈ V from hyv ▸ hv)
        rw [← hyv, ← map_mul, ← map_mul, hc]
      obtain ⟨K, hK, hNK⟩ := hK
      have hdvd := card_dvd_card_quotient_center_of_inf_centralizer_eq_bot hK hNYE hNK
      have hNcard : Nat.card ((Subgroup.normalizer (V : Set X)).comap ι) =
          Nat.card (Subgroup.normalizer (V : Set X)) := by
        rw [← Subgroup.card_map_of_injective hι, Subgroup.map_comap_eq_self]
        exact hNE.trans (Subgroup.map_le_range ι E)
      have hLX : Nat.card (K ⧸ Subgroup.center K) ∣ Nat.card X := by
        refine (Subgroup.index_dvd_card (Subgroup.center K)).trans
          ((Subgroup.card_subgroup_dvd_card K).trans ?_)
        rw [← Nat.card_congr φ.toEquiv]
        exact Subgroup.card_subgroup_dvd_card M
      exact hAr (K ⧸ Subgroup.center K) (hGc K hK) (hNcard ▸ hdvd) hLX
  have hcl : Subgroup.closure {t | t ∈ ((S : Subgroup X).subgroupOf M).map
      (QuotientGroup.mk' (goldschmidtOddCore M)) ⊓ E ∧ t ^ 2 = 1} = ⊥ := by
    rw [Subgroup.closure_eq_bot_iff]
    rintro t ⟨⟨-, htE⟩, -⟩
    rw [hEbot] at htE
    exact Subgroup.mem_bot.1 htE
  rw [hcl, sup_bot_eq] at hGb
  have hVeq : (CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M)).map ι = V := by
    have hcomp : ι.comp (QuotientGroup.mk' (goldschmidtOddCore M)) = M.subtype := by
      ext m
      exact hιπ m
    rw [← hGb, Subgroup.map_map, hcomp, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hVM]
  rw [← hVeq]
  exact hnormal _ (openPCore_characteristic _)

end CFSG.Monster.B.Recog
