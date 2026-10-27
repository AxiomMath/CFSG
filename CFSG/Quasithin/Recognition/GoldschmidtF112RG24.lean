module

public import CFSG.Quasithin.Recognition.GoldschmidtF112RSp44
public import CFSG.Quasithin.Recognition.GoldschmidtF112RTransport
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsF112PfB
public import CFSG.Quasithin.H13.NQCatG2RadModel
public import CFSG.Sporadic.Recognition.LyonsAS44Frattini
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
public import CFSG.Quasithin.Background.F6GoldschmidtListCat
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtRk2ParG2
public import CFSG.Quasithin.Recognition.F112RShapes
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsModG2Cent

public section

namespace CFSG.Quasithin.F112R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped commutatorElement

section Abstract

variable {G : Type} [Group G]

theorem le_centralizer_of_perfect [Finite G] {L Z : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLZ : L ≤ Subgroup.normalizer (Z : Set G)) (hZ : Nat.card Z ≤ 4) :
    L ≤ Subgroup.centralizer (Z : Set G) := by
  classical
  have := Fintype.ofFinite ↥Z
  let φ : ↥L →* Equiv.Perm ↥Z :=
    { toFun := fun ℓ =>
        { toFun := fun z => ⟨(ℓ : G) * z * (ℓ : G)⁻¹,
            (Subgroup.mem_normalizer_iff.mp (hLZ ℓ.2) z).mp z.2⟩
          invFun := fun z => ⟨(ℓ : G)⁻¹ * z * ℓ, by
            have := (Subgroup.mem_normalizer_iff.mp (hLZ (L.inv_mem ℓ.2)) z).mp z.2
            simpa using this⟩
          left_inv := fun z => Subtype.ext (by simp only; group)
          right_inv := fun z => Subtype.ext (by simp only; group) }
      map_one' := Equiv.ext fun z => Subtype.ext (by simp)
      map_mul' := fun a b => Equiv.ext fun z => Subtype.ext (by
        simp only [Equiv.coe_fn_mk, Equiv.Perm.coe_mul, Function.comp_apply, Subgroup.coe_mul]
        group) }
  haveI : Group.IsPerfect ↥L := Subgroup.isPerfect_iff.mpr hL
  have hsolv : IsSolvable (Equiv.Perm ↥Z) := Equiv.Perm.isSolvable hZ
  obtain ⟨n, hn⟩ := hsolv.solvable
  have htop : ∀ k, derivedSeries ↥L k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
      rw [derivedSeries_succ, ih, ← commutator_def]
      exact Group.IsPerfect.commutator_eq_top
  intro ℓ hℓ
  have h1 : φ ⟨ℓ, hℓ⟩ = 1 := by
    have := map_derivedSeries_le_derivedSeries φ n
    rw [htop, hn] at this
    exact (Subgroup.mem_bot).mp (this ⟨⟨ℓ, hℓ⟩, Subgroup.mem_top _, rfl⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have h2 := congrArg Subtype.val (Equiv.ext_iff.mp h1 ⟨z, hz⟩)
  have h3 : ℓ * z * ℓ⁻¹ = z := h2
  calc z * ℓ = ℓ * z * ℓ⁻¹ * ℓ := by rw [h3]
    _ = ℓ * z := by group

theorem centerOf_eq_map_center (Q : Subgroup G) :
    centerOf Q = (Subgroup.center ↥Q).map Q.subtype := by
  ext x
  constructor
  · rintro ⟨hx, hc⟩
    refine ⟨⟨x, hx⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp hc y y.2
  · rintro ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun z hz => ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨z, hz⟩)

theorem centerOf_le_centralizer [Finite G] {L P S : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLP : L ≤ P) (hct : CharTwo P) (hSP : S ≤ P) (hQS : pCoreOf 2 P ≤ S)
    (hZ : Nat.card (Subgroup.center ↥(pCoreOf 2 P)) ≤ 4) :
    centerOf S ≤ Subgroup.centralizer (L : Set G) := by
  set Q := pCoreOf 2 P with hQ
  have hLZ : L ≤ Subgroup.normalizer (centerOf Q : Set G) := fun ℓ hℓ =>
    CFSG.Quasithin.H13.NQCat.G2Rad.mem_normalizer_centerOf
      (le_normalizer_pCoreOf 2 P (hLP hℓ))
  have hcard : Nat.card (centerOf Q) ≤ 4 := by
    rw [centerOf_eq_map_center, Subgroup.card_map_of_injective Q.subtype_injective]
    exact hZ
  have hLC := le_centralizer_of_perfect hL hLZ hcard
  rintro z ⟨hzS, hzc⟩
  have hzQ : z ∈ Q := hct ⟨hSP hzS, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_iff.mp hzc q (hQS hq)⟩
  have hzZ : z ∈ centerOf Q := ⟨hzQ, Subgroup.mem_centralizer_iff.mpr fun q hq =>
    Subgroup.mem_centralizer_iff.mp hzc q (hQS hq)⟩
  rw [Subgroup.mem_centralizer_iff]
  intro ℓ hℓ
  exact (Subgroup.mem_centralizer_iff.mp (hLC hℓ) z hzZ).symm

theorem pCoreOf_eq_of_odd [Finite G] {L P : Subgroup G} (hLP : L ≤ P)
    (hn : P ≤ Subgroup.normalizer (L : Set G)) (hodd : ¬ 2 ∣ L.relIndex P) :
    pCoreOf 2 P = pCoreOf 2 L := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (L.subgroupOf P).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLP).2 hn
  apply le_antisymm
  · have h1 : pCoreOf 2 P ≤ L := CFSG.Quasithin.H13.Ch9.F112Pf.le_of_isPGroup_of_odd hnorm hodd
      (pCoreOf_le 2 P) (pCoreOf_isPGroup 2 P)
    exact le_pCoreOf_of_le_normalizer 2 h1 (hLP.trans (le_normalizer_pCoreOf 2 P))
      (pCoreOf_isPGroup 2 P)
  · exact le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 L).trans hLP)
      (hn.trans (normalizer_le_normalizer_pCoreOf 2 L)) (pCoreOf_isPGroup 2 L)

theorem pCoreOf_map_inj {H : Type} [Group H] (f : G →* H) (hf : Function.Injective f)
    (X : Subgroup G) : pCoreOf 2 (X.map f) = (pCoreOf 2 X).map f := by
  let e : ↥X ≃* ↥(X.map f) := X.equivMapOfInjective f hf
  ext y
  constructor
  · intro hy
    obtain ⟨x, hx, rfl⟩ := pCoreOf_le 2 _ hy
    exact ⟨x, (mem_pCoreOf_iff_of_mulEquiv e 2 ⟨x, hx⟩).mpr hy, rfl⟩
  · rintro ⟨x, hx, rfl⟩
    exact (mem_pCoreOf_iff_of_mulEquiv e 2 ⟨x, pCoreOf_le 2 X hx⟩).mp hx

theorem nonempty_perfectCore_mulEquiv {H : Type} [Group H] {P : Subgroup G} {N : Subgroup H}
    (ψ : ↥P ≃* ↥N) : Nonempty (↥(perfectCore P) ≃* ↥(perfectCore N)) := by
  let g : ↥P →* H := N.subtype.comp ψ.toMonoidHom
  have hg : Function.Injective g := N.subtype_injective.comp ψ.injective
  have hN : (⊤ : Subgroup ↥P).map g = N := by
    rw [← MonoidHom.range_eq_map, MonoidHom.range_comp,
      MonoidHom.range_eq_top_of_surjective _ ψ.surjective, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  have hP : (⊤ : Subgroup ↥P).map P.subtype = P := by
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
  set X := perfectCore (⊤ : Subgroup ↥P)
  have hN' : perfectCore N = X.map g := by rw [← hN, perfectCore_map_inj g hg]
  have hP' : perfectCore P = X.map P.subtype := by
    have := perfectCore_map_inj P.subtype P.subtype_injective (⊤ : Subgroup ↥P)
    rwa [hP] at this
  exact ⟨(MulEquiv.subgroupCongr hP').trans ((X.equivMapOfInjective _ P.subtype_injective).symm.trans
    ((X.equivMapOfInjective g hg).trans (MulEquiv.subgroupCongr hN'.symm)))⟩

end Abstract

section Model

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.NQCat.G2Rad


variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_N1 : Nat.card (N1 : Subgroup (ModGL Tag.G2 K)) = Nat.card K := by
  refine (Nat.card_congr (Equiv.ofBijective
    (fun c : K => (⟨gX rC c, gX_c_mem_N1 c⟩ : (N1 : Subgroup (ModGL Tag.G2 K)))) ⟨?_, ?_⟩)).symm
  · intro x y h
    exact pinnedX_injective Tag.G2 K rC (congrArg Subtype.val h)
  · rintro ⟨g, hg⟩
    obtain ⟨c, rfl⟩ := exists_of_mem_N1 hg
    exact ⟨c, rfl⟩

theorem card_radical (i : Fin Tag.G2.rank) :
    Nat.card (parabolicRadical Tag.G2 K {i}) = Nat.card K ^ 5 := by
  rw [card_parabolicRadical]
  congr 1
  rcases fin_two_cases i with rfl | rfl
  · rw [radicalRoots_zero]
    have : ({rR, rU, rV, rB, rC} : Set (Fin Tag.G2.rank → ℤ)) =
        ↑({rR, rU, rV, rB, rC} : Finset (Fin Tag.G2.rank → ℤ)) := by simp
    rw [this, Set.ncard_coe_finset]
    decide +kernel
  · rw [radicalRoots_one]
    have : ({rA, rU, rV, rB, rC} : Set (Fin Tag.G2.rank → ℤ)) =
        ↑({rA, rU, rV, rB, rC} : Finset (Fin Tag.G2.rank → ℤ)) := by simp
    rw [this, Set.ncard_coe_finset]
    decide +kernel

theorem coord_one' : coord (1 : ModGL Tag.G2 K) = 0 :=
  (mem_N1_iff (Subgroup.one_mem _)).mp (Subgroup.one_mem _)

theorem coord_inv' {g : ModGL Tag.G2 K} (hg : g ∈ parabolicRadical Tag.G2 K {i1}) :
    coord g⁻¹ = -coord g := by
  have h := coord_mul hg (Subgroup.inv_mem _ hg)
  rw [mul_inv_cancel, coord_one'] at h
  exact eq_neg_of_add_eq_zero_right h.symm

theorem isSpecialPow_radical_one (hK : Nat.card K = 4) :
    IsSpecialPow 2 (2 ^ 2) 2 ↥(parabolicRadical Tag.G2 K {i1}) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := parabolicRadical Tag.G2 K {i1} with hQdef
  have hcQ : Nat.card ↥Q = 2 ^ 10 := by
    rw [card_radical, hK]
    norm_num
  have hP : IsPGroup 2 ↥Q := IsPGroup.of_card hcQ
  have hN1Q : (N1 : Subgroup (ModGL Tag.G2 K)) ≤ Q := by
    rw [← centerOf_parabolicRadical_one]
    exact inf_le_left
  have hmemN : ∀ x : ↥Q, (x : ModGL Tag.G2 K) ∈ (N1 : Subgroup (ModGL Tag.G2 K)) ↔
      coord (x : ModGL Tag.G2 K) = 0 := fun x => mem_N1_iff x.2
  have hZ : Subgroup.center ↥Q = (N1 : Subgroup (ModGL Tag.G2 K)).subgroupOf Q := by
    ext z
    rw [Subgroup.mem_subgroupOf, ← centerOf_parabolicRadical_one, centerOf_eq_map_center]
    exact (Subgroup.mem_map_iff_mem Q.subtype_injective).symm
  have hC : commutator ↥Q = Subgroup.center ↥Q := by
    apply le_antisymm
    · rw [hZ, commutator_def, Subgroup.commutator_le]
      intro x _ y _
      rw [Subgroup.mem_subgroupOf, hmemN, commutatorElement_def]
      push_cast
      rw [coord_mul (Q.mul_mem (Q.mul_mem x.2 y.2) (Q.inv_mem x.2)) (Q.inv_mem y.2),
        coord_mul (Q.mul_mem x.2 y.2) (Q.inv_mem x.2), coord_mul x.2 y.2, coord_inv' x.2,
        coord_inv' y.2]
      abel
    · intro z hz
      have h1 : (z : ModGL Tag.G2 K) ∈ ⁅Q, Q⁆ := by
        apply center_le_one
        rw [← centerOf, centerOf_eq_map_center]
        exact ⟨z, hz, rfl⟩
      rw [← Subgroup.map_subtype_commutator] at h1
      obtain ⟨w, hw, hwz⟩ := h1
      rwa [← Q.subtype_injective hwz]
  refine ⟨⟨hP, Or.inr ⟨hC, ?_, ?_⟩⟩, by rw [hcQ]; norm_num, ?_⟩
  · haveI : (Subgroup.center ↥Q).Normal := inferInstance
    refine CFSG.Sporadic.Recognition.LyonsSims.frattini_eq_of_commutator_eq hP ?_ ?_
    · rw [← commutator_def]
      exact hC
    · intro a
      rw [hZ, Subgroup.mem_subgroupOf, hmemN, pow_two, Subgroup.coe_mul, coord_mul a.2 a.2]
      exact CharTwo.add_self_eq_zero _
  · intro z hz
    rw [hZ, Subgroup.mem_subgroupOf] at hz
    obtain ⟨c, hc⟩ := exists_of_mem_N1 hz
    apply Subtype.ext
    rw [Subgroup.coe_pow, hc, pow_two, gX_self]
    rfl
  · rw [hZ, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hN1Q).toEquiv, card_N1, hK]
    norm_num

theorem nonempty_pCore_equiv {Y : Type} [Group Y] (φ : Y ≃* ↥(adjointGroup Tag.G2 K)) {f : ℕ}
    (hK : Nat.card K = 2 ^ f) (hf : 2 ≤ f) (i : Fin Tag.G2.rank) :
    Nonempty (↥(pCoreOf 2 (perfectCore (((parabolicSubgroup Tag.G2 K {i}).subgroupOf
      (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom))) ≃* ↥(parabolicRadical Tag.G2 K {i})) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hPC := parabolicSubgroup_le_adjointGroup Tag.G2 K {i}
  set X := (parabolicSubgroup Tag.G2 K {i}).subgroupOf (adjointGroup Tag.G2 K)
  set W := pCoreOf 2 (perfectCore X)
  have hX : X.map (adjointGroup Tag.G2 K).subtype = parabolicSubgroup Tag.G2 K {i} :=
    Subgroup.map_subgroupOf_eq_of_le hPC
  have e2 : W.map (adjointGroup Tag.G2 K).subtype = parabolicRadical Tag.G2 K {i} := by
    rw [← pCoreOf_map_inj (adjointGroup Tag.G2 K).subtype (adjointGroup Tag.G2 K).subtype_injective,
      ← perfectCore_map_inj _ (adjointGroup Tag.G2 K).subtype_injective, hX]
    exact pCoreOf_perfectCore_parabolic hK hf i
  have e1 : pCoreOf 2 (perfectCore (X.map φ.symm.toMonoidHom)) = W.map φ.symm.toMonoidHom := by
    rw [perfectCore_map_inj _ φ.symm.injective, pCoreOf_map_inj _ φ.symm.injective]
  exact ⟨(MulEquiv.subgroupCongr e1).trans ((W.equivMapOfInjective _ φ.symm.injective).symm.trans
    ((W.equivMapOfInjective _ (adjointGroup Tag.G2 K).subtype_injective).trans (MulEquiv.subgroupCongr e2)))⟩

end Model

section YSide

open CFSG.Quasithin.H13.Ch9.F112Pf CFSG.QuasithinUnique.Setup.X6

theorem exists_residual_indices {Y : Type} [Group Y] [Finite Y] {T : Subgroup Y}
    {P : Fin 2 → Subgroup Y} (hR : ResidualOvergroupsAt Y T P) (ha : ∀ j, T ≤ perfectCore (P j))
    {M₁ M₂ : Subgroup Y} (hY : IsYAmalgamPair T M₁ M₂) (h1 : ¬ Group.IsSolvable ↥M₁)
    (h2 : ¬ Group.IsSolvable ↥M₂) :
    ∃ j₁ j₂ : Fin 2, j₁ ≠ j₂ ∧ perfectCore M₁ = perfectCore (P j₁) ∧
      perfectCore M₂ = perfectCore (P j₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hT, hne, hiff⟩ := hY
  obtain ⟨hM₁, hN₁⟩ := (hiff M₁).2 (Or.inl rfl)
  obtain ⟨hM₂, hN₂⟩ := (hiff M₂).2 (Or.inr rfl)
  have hT₁ : T ≤ M₁ := Subgroup.le_normalizer.trans hN₁
  have hT₂ : T ≤ M₂ := Subgroup.le_normalizer.trans hN₂
  have htop₁ : M₁ ≠ ⊤ := fun h => hne (hM₂.2 M₁ hM₁.1 (by rw [h]; exact le_top))
  have htop₂ : M₂ ≠ ⊤ := fun h => hne (hM₁.2 M₂ hM₂.1 (by rw [h]; exact le_top)).symm
  obtain ⟨j₁, -, hd₁⟩ := hR.2.2.2.2.1 M₁ hT₁ htop₁ h1
  obtain ⟨j₂, -, hd₂⟩ := hR.2.2.2.2.1 M₂ hT₂ htop₂ h2
  rw [dInf_eq_perfectCore', dInf_eq_perfectCore'] at hd₁ hd₂
  refine ⟨j₁, j₂, ?_, hd₁, hd₂⟩
  intro hjj
  subst hjj
  have hD : perfectCore M₂ = perfectCore M₁ := hd₂.trans hd₁.symm
  obtain ⟨R, hR1, hR2, hRN⟩ := hM₁.1
  have hRM : R ≤ M₁ := by
    rw [hRN]
    exact Subgroup.le_normalizer
  have hRO : R ≤ pCoreOf 2 M₁ := le_pCoreOf_of_le_normalizer 2 hRM hRN.le hR2
  have hOD : pCoreOf 2 M₁ ≤ perfectCore M₁ :=
    le_of_isPGroup_of_odd (perfectCore_normal M₁)
      (not_two_dvd_relIndex hT (by rw [hd₁]; exact ha j₁)) (pCoreOf_le 2 M₁)
      (pCoreOf_isPGroup 2 M₁)
  have hOO : pCoreOf 2 M₁ ≤ pCoreOf 2 (perfectCore M₁) :=
    le_pCoreOf_of_le_normalizer 2 hOD ((perfectCore_le M₁).trans (le_normalizer_pCoreOf 2 M₁))
      (pCoreOf_isPGroup 2 M₁)
  have hne' : pCoreOf 2 (perfectCore M₁) ≠ ⊥ := fun h =>
    hR1 (le_bot_iff.1 (h ▸ hRO.trans hOO))
  have hloc : IsTwoLocal (Subgroup.normalizer (pCoreOf 2 (perfectCore M₁) : Set Y)) :=
    ⟨_, hne', pCoreOf_isPGroup 2 _, rfl⟩
  have hle : ∀ M : Subgroup Y, perfectCore M = perfectCore M₁ →
      M ≤ Subgroup.normalizer (pCoreOf 2 (perfectCore M₁) : Set Y) := by
    intro M hM
    rw [← hM]
    exact (Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore M)).trans
      (normalizer_le_normalizer_pCoreOf 2 _)
  have e1 := hM₁.2 _ hloc (hle M₁ rfl)
  have e2 := hM₂.2 _ hloc (hle M₂ hD)
  exact hne (e1.symm.trans e2)

end YSide

section Main

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2 CFSG.Quasithin.H13.Ch9.F112Pf
  CFSG.QuasithinUnique.Setup.X6


theorem y9G24 : Y9G24 := by
  intro G _ _ L1 L2 S hF h1 h2 hA
  have hMF := hasModelFacts_g2 2 le_rfl
  have hPO := perfectOver_of_hasModelFacts hF.1 h1 h2 hMF hA
  obtain ⟨hB, hV1, hV2⟩ := vFact_of_hasModelFacts h1 h2 hMF hA
  obtain ⟨hB1, hB2⟩ := bigB_le_normalizer hF.1
  have hc1 := perfectCore_vertex hB1 hB hPO.1
  have hc2 := perfectCore_vertex hB2 hB hPO.2.1
  have hn1 : L1 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L1 : Set G) :=
    sup_le Subgroup.le_normalizer hB1
  have hn2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
    sup_le Subgroup.le_normalizer hB2
  have ho1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) = pCoreOf 2 L1 := by
    have := hV1.1
    rw [hc1] at this
    exact pCoreOf_eq_of_odd le_sup_left hn1 this
  have ho2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) = pCoreOf 2 L2 := by
    have := hV2.1
    rw [hc2] at this
    exact pCoreOf_eq_of_odd le_sup_left hn2 this
  have hct1 : CharTwo (L1 ⊔ bigB L1 L2 S) := by
    rw [F1.parabolic_eq]
    exact hF.1.h1.charTwo
  have hct2 : CharTwo (L2 ⊔ bigB L1 L2 S) := by
    rw [← bigB_comm L1 L2 S, F1.parabolic_eq]
    exact hF.1.h2.charTwo
  have hQS : ∀ L : Subgroup G, S ≤ L → IsSylowTwoOf (S ⊓ L) L →
      pCoreOf 2 L ≤ S := by
    intro L hSL hsy
    rw [inf_eq_left.mpr hSL] at hsy
    exact hsy.le_of_normalizes (pCoreOf_le 2 L) (le_normalizer_pCoreOf 2 L)
      (pCoreOf_isPGroup 2 L)
  have hQS1 : pCoreOf 2 (L1 ⊔ bigB L1 L2 S) ≤ S := ho1 ▸ hQS L1 hPO.2.2.1 hF.1.h1.sylow
  have hQS2 : pCoreOf 2 (L2 ⊔ bigB L1 L2 S) ≤ S := ho2 ▸ hQS L2 hPO.2.2.2 hF.1.h2.sylow
  have hp1 : ⁅L1, L1⁆ = L1 := (perfectCore_eq_self_iff L1).mp hPO.1
  have hp2 : ⁅L2, L2⁆ = L2 := (perfectCore_eq_self_iff L2).mp hPO.2.1
  obtain ⟨Y, _, hY, T, M₁, M₂, hp, ⟨iso0⟩⟩ := hA
  obtain ⟨hfinY, -⟩ := hMF Y hY
  have hX : ChevalleyExceptionalModel Y .G2 2 2 := by
    rcases hY with ⟨h, -⟩ | ⟨-, hL⟩
    · omega
    · rcases hL with ⟨h, -⟩ | ⟨-, -, h⟩ | ⟨-, h, -⟩ | ⟨-, h, -⟩
      · exact absurd h (by decide)
      · exact h
      · exact absurd h (by decide)
      · exact absurd h (by decide)
  obtain ⟨K, _, _, _, φ, hK, hφ, hres, -⟩ := even_rank_two_residual_G2 hX hp.1
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  have hT' : T = ((posUnipotent Tag.G2 K).subgroupOf (adjointGroup Tag.G2 K)).map
      φ.symm.toMonoidHom := by
    rw [← hφ, Subgroup.map_map]
    have e : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id Y := by
      ext
      simp
    rw [e, Subgroup.map_id]
  have ha : ∀ j : Fin 2, T ≤ perfectCore (((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf
      (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom) := by
    intro j
    rw [hT', perfectCore_map_inj _ φ.symm.injective]
    apply Subgroup.map_mono
    intro x hx
    rw [CFSG.Quasithin.H13.Sec53F.G2.mem_perfectCore_subgroupOf
      (parabolicSubgroup_le_adjointGroup Tag.G2 K {g2Index j})]
    exact posUnipotent_le_perfectCore_g2 (by rw [hK4]) _ hx
  have hns : ∀ (L : Subgroup G) (M : Subgroup Y), (↥(L ⊔ bigB L1 L2 S) ≃* ↥M) →
      IsL2Quot 2 (oTwoQuot ↥L) → ¬ Group.IsSolvable ↥M := by
    intro L M e hq hs
    apply not_isSolvable_of_isL2Quot_two hq
    have : Group.IsSolvable ↥(L ⊔ bigB L1 L2 S) :=
      Group.isSolvable_of_isSolvable_injective (f := e.toMonoidHom) e.injective
    exact Group.isSolvable_of_isSolvable_injective
      (Subgroup.inclusion_injective (le_sup_left : L ≤ L ⊔ bigB L1 L2 S))
  obtain ⟨j₁, j₂, hj, hd₁, hd₂⟩ := exists_residual_indices hres ha hp
    (hns L1 M₁ iso0.φ1 h1) (hns L2 M₂ iso0.φ2 h2)
  have E : ∀ (L : Subgroup G) (M : Subgroup Y) (j : Fin 2),
      perfectCore (L ⊔ bigB L1 L2 S) = L → (↥(L ⊔ bigB L1 L2 S) ≃* ↥M) →
      perfectCore M = perfectCore (((parabolicSubgroup Tag.G2 K {g2Index j}).subgroupOf
        (adjointGroup Tag.G2 K)).map φ.symm.toMonoidHom) →
      pCoreOf 2 (L ⊔ bigB L1 L2 S) = pCoreOf 2 L →
      Nonempty (↥(pCoreOf 2 (L ⊔ bigB L1 L2 S)) ≃*
        ↥(parabolicRadical Tag.G2 K {g2Index j})) := by
    intro L M j hc ψ hd ho
    obtain ⟨e⟩ := nonempty_perfectCore_mulEquiv ψ
    rw [hc, hd] at e
    obtain ⟨e'⟩ := nonempty_pCore_equiv φ hK le_rfl (g2Index j)
    exact ⟨(MulEquiv.subgroupCongr ho).trans ((pCoreOfMulEquiv e 2).trans e')⟩
  obtain ⟨e1⟩ := E L1 M₁ j₁ hc1 iso0.φ1 hd₁ ho1
  obtain ⟨e2⟩ := E L2 M₂ j₂ hc2 iso0.φ2 hd₂ ho2
  have hcard : ∀ (j : Fin 2) (A : Subgroup G),
      (↥A ≃* ↥(parabolicRadical Tag.G2 K {g2Index j})) → Nat.card A = (2 ^ 2) ^ 5 := by
    intro j A e
    rw [Nat.card_congr e.toEquiv, card_radical, hK4]
    norm_num
  have hspec : ∀ (j : Fin 2) (A : Subgroup G), g2Index j = i1 →
      (↥A ≃* ↥(parabolicRadical Tag.G2 K {g2Index j})) → IsSpecialPow 2 (2 ^ 2) 2 ↥A := by
    intro j A hj e
    rw [hj] at e
    exact IsSpecialPow.of_mulEquiv e.symm (isSpecialPow_radical_one hK4)
  obtain ⟨j, hjI⟩ := g2Index_surjective i1
  have hjj : j = j₁ ∨ j = j₂ :=
    (by decide : ∀ a b c : Fin 2, a ≠ b → c = a ∨ c = b) j₁ j₂ j hj
  refine ⟨?_, hPO⟩
  rcases hjj with rfl | rfl
  · have hs := hspec j _ hjI e1
    refine Or.inl ⟨fun _ => centerOf_le_centralizer hp1 le_sup_left hct1
      (hPO.2.2.1.trans le_sup_left) hQS1 (by rw [hs.2.2]; norm_num), hs, hcard j₂ _ e2⟩
  · have hs := hspec j _ hjI e2
    refine Or.inr ?_
    have hbc : bigB L2 L1 S = bigB L1 L2 S := bigB_comm L1 L2 S
    unfold G24Oriented
    rw [hbc]
    exact ⟨fun _ => centerOf_le_centralizer hp2 le_sup_left hct2
      (hPO.2.2.2.trans le_sup_left) hQS2 (by rw [hs.2.2]; norm_num), hs, hcard j₁ _ e1⟩

end Main

end CFSG.Quasithin.F112R
