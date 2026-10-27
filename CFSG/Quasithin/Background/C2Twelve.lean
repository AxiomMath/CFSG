module

public import CFSG.Quasithin.Background.C2Eleven
public import CFSG.Quasithin.Background.C2Coprime
import CFSG.Quasithin.Background.A1aFStar
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped Pointwise

variable {G : Type} [Group G] [Finite G] {H R M L V T : Subgroup G}

namespace C2Twelve

theorem le_centralizer_of_perfect_of_commutator_le (hC111 : ASC111Statement G) {K A : Subgroup G}
    (hK : IsShort2 K) (hA : ⁅A, A⁆ = A) (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKA : ⁅K, A⁆ ≤ pCoreOf 2 K) : A ≤ Subgroup.centralizer (K : Set G) := by
  obtain ⟨T₀, hT₀, -⟩ := B6.exists_isSylowTwoOf_ge (J := A) (X := ⊥) IsPGroup.of_bot bot_le
  have hT₀A : T₀ ≤ A := hT₀.1
  have hT₀K : T₀ ≤ Subgroup.normalizer (K : Set G) := hT₀A.trans hAK
  set H₁ : Subgroup G := K ⊔ T₀
  have hKH₁ : K ≤ H₁ := le_sup_left
  have hT₀H₁ : T₀ ≤ H₁ := le_sup_right
  have hH₁K : H₁ ≤ Subgroup.normalizer (K : Set G) := sup_le Subgroup.le_normalizer hT₀K
  have hblock : IsBlock2 H₁ K :=
    ⟨hK, hKH₁, ((Subgroup.normal_subgroupOf_iff_le_normalizer hKH₁).mpr hH₁K).isSubnormal⟩
  obtain ⟨S, hS, hT₀S⟩ := B6.exists_isSylowTwoOf_ge hT₀.2.1 hT₀H₁
  have hdecomp : ∀ x ∈ H₁, ∃ k ∈ K, ∃ s ∈ S, x = k * s := by
    intro x hx
    have hx' : x ∈ (K : Set G) * (T₀ : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K T₀ hT₀K]
      exact hx
    obtain ⟨k, hk, t, ht, rfl⟩ := hx'
    exact ⟨k, hk, t, hT₀S ht, rfl⟩
  have hC := hC111 H₁ K S Unit (fun _ => K) inferInstance (fun _ => hblock)
    (fun i j hij => (hij (Subsingleton.elim i j)).elim)
    (iSup_const (ι := Unit)).symm hKH₁ hS hdecomp
  have hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) := le_normalizer_pCoreOf 2 K
  have hT₀Q : T₀ ≤ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
    hT₀K.trans (normalizer_le_normalizer_pCoreOf 2 K)
  have hYp : IsPGroup 2 (pCoreOf 2 K ⊔ T₀ : Subgroup G) :=
    IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 K) hT₀.2.1 hT₀Q
  have hYH₁ : pCoreOf 2 K ⊔ T₀ ≤ H₁ := sup_le ((pCoreOf_le 2 K).trans hKH₁) hT₀H₁
  have hH₁Y : H₁ ≤ Subgroup.normalizer ((pCoreOf 2 K ⊔ T₀ : Subgroup G) : Set G) := by
    refine sup_le ?_ (le_sup_right.trans Subgroup.le_normalizer)
    intro k hk
    refine A4.mem_normalizer_of_conj_mem fun y hy => ?_
    have hy' : y ∈ (pCoreOf 2 K : Set G) * (T₀ : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left (pCoreOf 2 K) T₀ hT₀Q]
      exact hy
    obtain ⟨q, hq, t, ht, rfl⟩ := hy'
    have h1 : k * q * k⁻¹ ∈ pCoreOf 2 K := (Subgroup.mem_normalizer_iff.mp (hKQ hk) q).mp hq
    have h2 : k * t * k⁻¹ * t⁻¹ ∈ pCoreOf 2 K :=
      hKA (Subgroup.commutator_mem_commutator hk (hT₀A ht))
    have : k * (q * t) * k⁻¹ = (k * q * k⁻¹) * (k * t * k⁻¹ * t⁻¹) * t := by group
    rw [this]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left h1)
      (Subgroup.mem_sup_left h2)) (Subgroup.mem_sup_right ht)
  have hT₀O : T₀ ≤ pCoreOf 2 H₁ :=
    le_sup_right.trans (le_pCoreOf_of_le_normalizer 2 hYH₁ hH₁Y hYp)
  rw [← hC] at hT₀O
  have hT₀U : T₀ ≤ Subgroup.centralizer (blockU K : Set G) := fun t ht => (hT₀O ht).2
  have hAU : A ≤ Subgroup.centralizer (blockU K : Set G) := by
    rw [← conjClosure_eq_of_perfect_of_isSylowTwoOf hA hT₀]
    refine conjClosure_le fun a ha t ht => ?_
    have haK : a ∈ Subgroup.normalizer (K : Set G) := hAK ha
    have haQ : a ∈ Subgroup.normalizer (pCoreOf 2 K : Set G) :=
      normalizer_le_normalizer_pCoreOf 2 K haK
    have haU : a ∈ Subgroup.normalizer (blockU K : Set G) := by
      rw [Subgroup.mem_normalizer_iff_map_conj_eq] at haK haQ ⊢
      unfold blockU blockQ
      rw [Subgroup.map_commutator, haQ, haK]
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : a⁻¹ * u * a ∈ blockU K := (Subgroup.mem_normalizer_iff''.mp haU u).mp hu
    have key := Subgroup.mem_centralizer_iff.mp (hT₀U ht) _ hu'
    calc u * (a * t * a⁻¹) = a * ((a⁻¹ * u * a) * t) * a⁻¹ := by group
      _ = a * (t * (a⁻¹ * u * a)) * a⁻¹ := by rw [key]
      _ = a * t * a⁻¹ * u := by group
  exact le_centralizer_of_perfect_of_le_centralizer_blockU hK hA hAK hKA hAU

omit [Finite G] in
theorem commutator_le_pCoreOf {K A S : Subgroup G} (hAK : A ≤ Subgroup.normalizer (K : Set G))
    (hKS : K ≤ Subgroup.normalizer (S : Set G)) (hS : IsPGroup 2 S) (hKAS : ⁅K, A⁆ ≤ S) :
    ⁅K, A⁆ ≤ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h1 : ⁅K, A⁆ ≤ K := Subgroup.le_normalizer_iff_commutator_le_left.mp hAK
  have h3 : K ⊓ S ≤ pCoreOf 2 K :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left
      (fun g hg => Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg, hKS hg⟩)
      (hS.to_le inf_le_right)
  exact (le_inf h1 hKAS).trans h3

theorem pPrimeCore_eq_bot_of_normal {X : Subgroup G} (hXH : X ≤ H)
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) (hO : oddCoreIn H = ⊥) :
    CFSG.pPrimeCore 2 ↥X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set c : Subgroup ↥X := CFSG.pPrimeCore 2 ↥X
  have hcH : c.map X.subtype ≤ H := (Subgroup.map_subtype_le c).trans hXH
  have hnorm : H ≤ Subgroup.normalizer (c.map X.subtype : Set G) :=
    hHX.trans (normalizer_le_normalizer_map_of_characteristic c)
  have hN : ((c.map X.subtype).subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hcH).mpr hnorm
  have hodd : Odd (Nat.card ((c.map X.subtype).subgroupOf H)) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hcH).toEquiv,
      Nat.card_congr (c.equivMapOfInjective X.subtype X.subtype_injective).toEquiv.symm]
    exact Nat.coprime_two_left.mp (CFSG.pPrimeCore_coprime_card (p := 2) (G := ↥X))
  have hle : (c.map X.subtype).subgroupOf H ≤ fusionOddCore ↥H := le_sSup ⟨hN, hodd⟩
  have h1 : c.map X.subtype ≤ oddCoreIn H := by
    have := Subgroup.map_mono (f := H.subtype) hle
    rwa [Subgroup.map_subgroupOf_eq_of_le hcH] at this
  rw [hO, le_bot_iff] at h1
  exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp h1

omit [Finite G] in
theorem isComponentOf_map_of_isComponent {X : Subgroup G} (hXH : X ≤ H)
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) {K : Subgroup ↥X} (hK : CFSG.IsComponent K) :
    IsComponentOf (K.map X.subtype) H := by
  have hKo : IsComponentOf K ⊤ := (CFSG.isComponent_iff_open K).mp hK
  have hsub : (K.map X.subtype).subgroupOf X = K :=
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective K
  have hLX : IsComponentOf (K.map X.subtype) X :=
    isComponentOf_iff_subgroupOf.mpr ⟨Subgroup.map_subtype_le K, by rw [hsub]; exact hKo⟩
  exact ⟨hLX.1.trans hXH, A3.subnormal_trans hLX.2.1
    (A4.subnormal_of_normal hXH ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHX)),
    hLX.2.2⟩

theorem layer_eq_bot (h : HypC28 H R M L V)
    (hHn : H ≤ Subgroup.normalizer (conjClosure L M : Set G)) :
    CFSG.layer ↥(centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M))) = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₀ := conjClosure L M
  set X := centralizerSection H M₀ (pCoreOf 2 M₀)
  have hM₀M : M₀ ≤ M := C2Nine.conjClosure_le_M h
  have hXH : X ≤ H := centralizerSection_le_left _ _ _
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := centralizerSection_normal hHn
  have hS₀X : pCoreOf 2 M₀ ≤ X :=
    (pCoreOf_le_centralizerSection hM₀M).trans (centralizerSection_mono h.le_H _ _)
  have hXS₀ : X ≤ Subgroup.normalizer (pCoreOf 2 M₀ : Set G) :=
    centralizerSection_le_normalizer_right _ _ _
  have hS₀P : pCoreOf 2 M₀ ≤ pCoreOf 2 X :=
    le_pCoreOf_of_le_normalizer 2 hS₀X hXS₀ (pCoreOf_isPGroup 2 M₀)
  refine sSup_eq_bot.mpr fun K hK => ?_
  exfalso
  have hKc : CFSG.IsComponent K := hK
  set L' : Subgroup G := K.map X.subtype
  have hL'H : IsComponentOf L' H := isComponentOf_map_of_isComponent hXH hHX hKc
  have hL'X : L' ≤ X := Subgroup.map_subtype_le K
  have hKR : ⁅K, CFSG.Open.pCore 2 ↥X⁆ = ⊥ := by
    have hR2 : (CFSG.Open.pCore 2 ↥X).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    have hRsolv : Group.IsSolvable (CFSG.Open.pCore 2 ↥X) := by
      have : Group.IsNilpotent (CFSG.Open.pCore 2 ↥X) :=
        (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥X) 2).isNilpotent
      infer_instance
    exact (CFSG.LocalCores.component_solvable_centralizer hRsolv hR2.isSubnormal).1 K hKc
  have hL'P : ⁅L', pCoreOf 2 X⁆ = ⊥ := by
    have := congrArg (Subgroup.map X.subtype) hKR
    rwa [Subgroup.map_commutator, Subgroup.map_bot] at this
  have hL'S : ⁅L', pCoreOf 2 M₀⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅L', pCoreOf 2 M₀⁆ ≤ ⁅L', pCoreOf 2 X⁆ := Subgroup.commutator_mono le_rfl hS₀P
      _ = ⊥ := hL'P
  have hM₀L' : ⁅M₀, L'⁆ ≤ pCoreOf 2 M₀ :=
    ((le_centralizerSection_iff (pCoreOf_le 2 M₀)).mp hL'X).2
  have hL'M₀ : ⁅L', M₀⁆ ≤ pCoreOf 2 M₀ := by
    rw [Subgroup.commutator_comm]
    exact hM₀L'
  have hperf : Group.IsPerfect ↥L' := (A3.isQuasisimple_iff_open.mpr hL'H.2.2).1
  have h1 : ⁅⁅L', M₀⁆, L'⁆ = ⊥ := by
    refine le_bot_iff.mp ?_
    calc ⁅⁅L', M₀⁆, L'⁆ ≤ ⁅pCoreOf 2 M₀, L'⁆ := Subgroup.commutator_mono hL'M₀ le_rfl
      _ = ⊥ := by rw [Subgroup.commutator_comm]; exact hL'S
  have h2 : ⁅L', M₀⁆ = ⊥ := CFSG.LocalCores.perfect_double_commutator hperf h1
  have hL'C : L' ≤ Subgroup.centralizer (M₀ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp h2
  have hL'V : L' ≤ Subgroup.centralizer (V : Set G) :=
    hL'C.trans (Subgroup.centralizer_le h.V_le)
  exact c2_10_two h L' hL'H fun x hx =>
    h.V_norm ⟨hXH (hL'X hx), Subgroup.centralizer_le_normalizer _ (hL'V hx)⟩

theorem charTwo_centralizerSection (h : HypC28 H R M L V)
    (hHn : H ≤ Subgroup.normalizer (conjClosure L M : Set G)) :
    CharTwo (centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M))
  have hXH : X ≤ H := centralizerSection_le_left _ _ _
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := centralizerSection_normal hHn
  have hch := CFSG.isCharacteristicP_of_pPrimeCore_eq_bot_of_layer_eq_bot ↥X 2
    (pPrimeCore_eq_bot_of_normal hXH hHX (c2_10_one h)) (layer_eq_bot h hHn)
  unfold CFSG.IsCharacteristicP at hch
  exact (centralizer_pCore_le_iff_pCoreOf 2 X).mp hch

theorem hypC23_centralizerSection (h : HypC28 H R M L V) :
    HypC23 (centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M))) R
      (M ⊓ centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M))) := by
  set X := centralizerSection H (conjClosure L M) (pCoreOf 2 (conjClosure L M))
  have hXH : X ≤ H := centralizerSection_le_left _ _ _
  have hX3 : IsSylowTwoOf R X := c2_10_three h
  have hRX : R ≤ X := hX3.1
  refine ⟨h.sqtk.mono hXH, isTwoRadicalIn_of_sylow hRX h.pgroup hX3.2.2 (C2Nine.ne_bot_of_hyp h),
    inf_le_right, le_inf ((C2Nine.cgsIn_mono_left hXH R).trans h.cgs) (cgsIn_le X R), ?_⟩
  refine B6.isSylowTwoOf_mono hX3 (le_conjClosure R (M ⊓ X)) (conjClosure_le fun m hm r hr => ?_)
  exact X.mul_mem (X.mul_mem hm.2 (hRX hr)) (X.inv_mem hm.2)

theorem le_of_le_normalizer (hC129 : ASC129Statement G) (hC111 : ASC111Statement G)
    (hC19 : ASC19Statement G) (h : HypC28 H R M L V)
    (hHn : H ≤ Subgroup.normalizer (conjClosure L M : Set G)) : H ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M₀ := conjClosure L M
  set X := centralizerSection H M₀ (pCoreOf 2 M₀)
  have hM₀M : M₀ ≤ M := C2Nine.conjClosure_le_M h
  have hM₀H : M₀ ≤ H := hM₀M.trans h.le_H
  have hXH : X ≤ H := centralizerSection_le_left _ _ _
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := centralizerSection_normal hHn
  have hXS₀ : X ≤ Subgroup.normalizer (pCoreOf 2 M₀ : Set G) :=
    centralizerSection_le_normalizer_right _ _ _
  have hX3 : IsSylowTwoOf R X := c2_10_three h
  have hXM : X ≤ M := by
    by_contra hXM
    obtain ⟨r, Lb, hLb, hprod⟩ :=
      c2_5 hC129 (hypC23_centralizerSection h) hX3 (charTwo_centralizerSection h hHn)
    obtain ⟨i, hi⟩ : ∃ i, ¬ Lb i ≤ M := by
      by_contra hall
      have hall' : ∀ j, Lb j ≤ M := fun j => not_not.mp (not_exists.mp hall j)
      apply hXM
      intro x hx
      obtain ⟨m, hm, y, hy, rfl⟩ := hprod x hx
      refine M.mul_mem hm.1 (Subgroup.list_prod_mem M fun a ha => ?_)
      obtain ⟨j, rfl⟩ := List.mem_ofFn.mp ha
      exact hall' j (hy j)
    have hKchi : IsChi0Block X (Lb i) := hLb i
    have hKX : Lb i ≤ X := hKchi.1.2.1
    have hXHn : IsSubnormal X H :=
      A4.subnormal_of_normal hXH ((Subgroup.normal_subgroupOf_iff_le_normalizer hXH).mpr hHX)
    have hKblock : IsBlock2 H (Lb i) :=
      ⟨hKchi.1.1, hKX.trans hXH, (isSubnormal_iff_subgroupOf (hKX.trans hXH)).mp
        (A3.subnormal_trans (IsBlock2.isSubnormal hKchi.1) hXHn)⟩
    obtain ⟨x, hxK, hxo, hx2, hxc⟩ := exists_noncentral_odd_prime_of_isChi0Block hKchi
    have hM₀K : M₀ ≤ Subgroup.normalizer (Lb i : Set G) :=
      perfect_le_normalizer_of_odd_prime hC19 h.sqtk (c2_10_one h) hM₀H
        (C2Nine.perfect_conjClosure_of_hyp h) hKblock hxK hxo hx2 hxc
    have hKM₀ : ⁅Lb i, M₀⁆ ≤ pCoreOf 2 (Lb i) := by
      refine commutator_le_pCoreOf hM₀K (hKX.trans hXS₀) (pCoreOf_isPGroup 2 M₀) ?_
      rw [Subgroup.commutator_comm]
      exact ((le_centralizerSection_iff (pCoreOf_le 2 M₀)).mp hKX).2
    have hcen : M₀ ≤ Subgroup.centralizer (Lb i : Set G) :=
      le_centralizer_of_perfect_of_commutator_le hC111 hKchi.1.1
        (C2Nine.perfect_conjClosure_of_hyp h) hM₀K hKM₀
    apply hi
    have hKC : Lb i ≤ Subgroup.centralizer (M₀ : Set G) := by
      have h0 := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hcen
      rw [Subgroup.commutator_comm] at h0
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h0
    intro y hy
    exact h.V_norm ⟨hXH (hKX hy), Subgroup.centralizer_le_normalizer _
      (Subgroup.centralizer_le h.V_le (hKC hy))⟩
  exact (B6.frattini_two hXH hHX hX3).trans (sup_le hXM (C2Nine.inf_normalizer_le_M h))

end C2Twelve

theorem c2_12 (hC129 : ASC129Statement G) (hC111 : ASC111Statement G) (hC19 : ASC19Statement G)
    (hA3 : A3Orbits G) (h : HypC28 H R M L V) (hT : IsSylowTwoOf T M) (hRT : R ≤ T) :
    H ⊓ Subgroup.normalizer (conjClosure L M : Set G) = M := by
  have hM₀M : conjClosure L M ≤ M := C2Nine.conjClosure_le_M h
  have hMH : M ≤ H ⊓ Subgroup.normalizer (conjClosure L M : Set G) :=
    le_inf h.le_H (le_normalizer_conjClosure L M)
  refine le_antisymm ?_ hMH
  have hX : conjClosure L M ⊔ T ≤ H ⊓ Subgroup.normalizer (conjClosure L M : Set G) :=
    sup_le (le_inf (hM₀M.trans h.le_H) Subgroup.le_normalizer) (hT.1.trans hMH)
  have h' : HypC28 (H ⊓ Subgroup.normalizer (conjClosure L M : Set G)) R M L V := by
    have := c2_9_three hA3 h hT hRT hX inf_le_left
    rwa [inf_eq_left.mpr hMH] at this
  exact C2Twelve.le_of_le_normalizer hC129 hC111 hC19 h' inf_le_right

end CFSG.Quasithin
