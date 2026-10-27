module

public import CFSG.Quasithin.Background.SmithC27RCaseIIG2Par
public import CFSG.Quasithin.Background.SmithC27RTypeDefs
public import CFSG.Quasithin.Background.SmithC27RTypeU33
public import CFSG.Quasithin.Background.SmithC27RLieG2
public import CFSG.Timmesfeld.Orders.ExceptionalUntwisted

public section

namespace CFSG.Quasithin.SmithC27

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.Chevalley CFSG.Blueprint
  CFSG.Blueprint.Chevalley

theorem map_eq_subgroupOf_of_mem_iff {A B : Type} [Group A] [Group B] {J L : Subgroup B}
    {D : Subgroup A} (π : A →* ↥J) (hπ : Function.Surjective π)
    (hmem : ∀ a, ((π a : ↥J) : B) ∈ L ↔ a ∈ D) : D.map π = L.subgroupOf J := by
  ext x
  obtain ⟨a, rfl⟩ := hπ x
  rw [Subgroup.mem_subgroupOf, hmem]
  constructor
  · rintro ⟨a', ha', he⟩
    rw [← hmem, ← he, hmem]
    exact ha'
  · intro ha
    exact ⟨a, ha, rfl⟩

theorem card_le_card_mulAut {Γ : Type} [Group Γ] {X N : Subgroup Γ} [Finite ↥N] (hNX : N ≤ X)
    (hXN : X ≤ Subgroup.normalizer (N : Set Γ))
    (hC : X ⊓ Subgroup.centralizer (N : Set Γ) ≤ N) (hZ : Subgroup.center ↥N = ⊥) :
    Nat.card ↥X ≤ Nat.card (MulAut ↥N) := by
  have : (N.subgroupOf X).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNX).2 hXN
  have hinj : Function.Injective (MulAut.conjNormal (H := N.subgroupOf X)) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have hxC : (x : Γ) ∈ Subgroup.centralizer (N : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro n hn
      have h1 := congrArg (fun f : MulAut ↥(N.subgroupOf X) => ((f ⟨⟨n, hNX hn⟩, hn⟩ : ↥X) : Γ)) hx
      have h2 : (x : Γ) * n * (x : Γ)⁻¹ = n := by
        simpa only [MulAut.conjNormal_apply, MulAut.one_apply, Subgroup.coe_mul,
          Subgroup.coe_inv] using h1
      calc n * (x : Γ) = (x : Γ) * n * (x : Γ)⁻¹ * x := by rw [h2]
        _ = x * n := by group
    have hxN : (x : Γ) ∈ N := hC ⟨x.2, hxC⟩
    have hz : (⟨x, hxN⟩ : ↥N) ∈ Subgroup.center ↥N := by
      rw [Subgroup.mem_center_iff]
      intro n
      exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC n n.2)
    rw [hZ, Subgroup.mem_bot] at hz
    have h3 : (x : Γ) = 1 := congrArg Subtype.val hz
    exact Subtype.ext h3
  have : Finite ↥(N.subgroupOf X) :=
    Finite.of_equiv _ (Subgroup.subgroupOfEquivOfLe hNX).toEquiv.symm
  calc Nat.card ↥X ≤ Nat.card (MulAut ↥(N.subgroupOf X)) := Nat.card_le_card_of_injective _ hinj
    _ = Nat.card (MulAut ↥N) :=
      Nat.card_congr (MulAut.congr (Subgroup.subgroupOfEquivOfLe hNX)).toEquiv

theorem center_eq_bot_of_centralizer_le {Γ : Type} [Group Γ] {X N : Subgroup Γ} (hNX : N ≤ X)
    (hC : X ⊓ Subgroup.centralizer (N : Set Γ) ≤ N) (hZ : Subgroup.center ↥N = ⊥) :
    Subgroup.center ↥X = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hxC : (x : Γ) ∈ Subgroup.centralizer (N : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hx ⟨n, hNX hn⟩)
  have hxN : (x : Γ) ∈ N := hC ⟨x.2, hxC⟩
  have hz : (⟨x, hxN⟩ : ↥N) ∈ Subgroup.center ↥N := by
    rw [Subgroup.mem_center_iff]
    intro n
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 hxC n n.2)
  rw [hZ, Subgroup.mem_bot] at hz
  have h3 : (x : Γ) = 1 := congrArg Subtype.val hz
  exact Subgroup.mem_bot.2 (Subtype.ext h3)

theorem nonempty_quasithinG2_mulEquiv_adjointGroup_two
    {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2) :
    Nonempty (↥(quasithinG2 F) ≃* ↥(adjointGroup .G2 F)) := by
  have : CharP F 2 := FFC.charP_two_of_card_pow (n := 1) (by rw [hF, pow_one])
  have : Finite (ModGL .G2 F) := finite_modGL
  obtain ⟨ψ, -, hψ⟩ := B42G2Id.exists_surjective_adjointGroup_hom_cayleyGroup (F := F)
  have hA : Nat.card ↥(adjointGroup .G2 F) = 12096 := by
    rw [Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hF]
    rfl
  have hC : Nat.card ↥(Explicit.cayleyGroup F) = 12096 := by
    rw [← Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
      card_quasithinG2' (n := 1) (by rw [hF, pow_one]), hF]
    norm_num
  have hbij := hψ.bijective_of_nat_card_le (by rw [hA, hC])
  exact ⟨(MulEquiv.subgroupCongr Bridge.Alt57Model.quasithinG2_eq_cayleyGroup).trans
    (MulEquiv.ofBijective ψ hbij).symm⟩

variable {G : Type} [Group G] [Finite G] {H R M K V : Subgroup G}

omit [Finite G] in
theorem jPStar_le (hV : IsElemAbelian 2 V) : jPStar hV R K ≤ autI hV (K ⊔ R) :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun hA => hA

theorem autI_le_jPStar (hV : IsElemAbelian 2 V)
    (hKT : ∀ T : Subgroup (MulAut (IntMod V hV)), IsSylowTwoOf T (jPStar hV R K) →
      jPStar hV R K = autI hV K ⊔ T) : autI hV K ≤ jPStar hV R K := by
  obtain ⟨T, hT⟩ := exists_isSylowTwoOf (jPStar hV R K)
  rw [hKT T hT]
  exact le_sup_left

theorem g2StarData_of
    (hs : StarHyp R K V) (hV : IsElemAbelian 2 V)
    (hKT : ∀ T : Subgroup (MulAut (IntMod V hV)), IsSylowTwoOf T (jPStar hV R K) →
      jPStar hV R K = autI hV K ⊔ T)
    (hG : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ π : ↥(quasithinG2 F) →* ↥(jPStar hV R K),
        (FFModel.zornQ (quasithinG2 F)).RealizesVia (jPStar hV R K) (commV (autI hV K))
          (fixV (autI hV K) ⊓ commV (autI hV K)) π ∧
        ∀ g : ↥(quasithinG2 F),
          ((π g : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) ∈ autI hV K ↔
            (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆) :
    jPStar hV R K = autI hV (K ⊔ R) ∧ G2StarData R K V := by
  obtain ⟨F, _, _, hF, π, hπ, hmem⟩ := hG
  have : CharP F 2 := FFC.charP_two_of_card_pow (n := 1) (by rw [hF, pow_one])
  let e : ↥(quasithinG2 F) ≃* ↥(jPStar hV R K) :=
    FFC.equivOfRealizes (FFC.zornQ_faithful (quasithinG2 F) le_rfl) hπ
  have hJ : Nat.card ↥(jPStar hV R K) = 12096 := by
    rw [← Nat.card_congr e.toEquiv, card_quasithinG2' (n := 1) (by rw [hF, pow_one]), hF]
    norm_num
  have hKJ := autI_le_jPStar hV hKT
  have hle : ⁅quasithinG2 F, quasithinG2 F⁆ ≤ quasithinG2 F := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    exact (quasithinG2 F).mul_mem ((quasithinG2 F).mul_mem ((quasithinG2 F).mul_mem ha hb)
      ((quasithinG2 F).inv_mem ha)) ((quasithinG2 F).inv_mem hb)
  have hmap : ((⁅quasithinG2 F, quasithinG2 F⁆).subgroupOf (quasithinG2 F)).map e.toMonoidHom =
      (autI hV K).subgroupOf (jPStar hV R K) :=
    map_eq_subgroupOf_of_mem_iff e.toMonoidHom e.surjective fun g => hmem g
  let eK : ↥⁅quasithinG2 F, quasithinG2 F⁆ ≃* ↥(autOn K V) :=
    (((Subgroup.subgroupOfEquivOfLe hle).symm.trans
      (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective)).trans
      (MulEquiv.subgroupCongr hmap)).trans (Subgroup.subgroupOfEquivOfLe hKJ)
  have hpsu : IsPSU 3 3 1 ↥(autOn K V) := isPSU_of_equiv_g2Derived hF eK.symm
  have hZK : Subgroup.center ↥(autOn K V) = ⊥ :=
    SBc11.center_eq_bot_of_list (Or.inr (Or.inr hpsu))
  have hGF : Nat.card (GaloisField 2 1) = 2 := by
    rw [GaloisField.card 2 1 one_ne_zero]
    norm_num
  let eSU : ↥(autOn K V) ≃* CFSG.Assembly.LowTwoRank.StatedSU 3 3 G2U.F9 :=
    eK.symm.trans ((Insp9.g2DerivedEquivZMod2 F hF).trans
      ((Insp9.g2DerivedEquivZMod2 (GaloisField 2 1) hGF).symm.trans
        G11.P3G2.commutatorG2EquivSU))
  have hAut : Nat.card (MulAut ↥(autOn K V)) = 12096 := G11.P3G2.card_mulAut_of_equiv eSU
  have hKX : autOn K V ≤ autOn (K ⊔ R) V := autOn_mono' le_sup_left
  have hX : Nat.card ↥(autOn (K ⊔ R) V) ≤ 12096 :=
    hAut ▸ card_le_card_mulAut hKX hs.normalizes hs.centralizer_le hZK
  have hJX : jPStar hV R K = autI hV (K ⊔ R) :=
    Subgroup.eq_of_le_of_card_ge (jPStar_le hV) (by rw [hJ]; exact hX)
  have hXc : Nat.card ↥(autOn (K ⊔ R) V) = 12096 := by
    have h1 : Nat.card ↥(autI hV (K ⊔ R)) = 12096 := hJX ▸ hJ
    exact h1
  have hidx : ((autOn K V).subgroupOf (autOn (K ⊔ R) V)).index = 2 := by
    have h1 := Subgroup.card_mul_index ((autOn K V).subgroupOf (autOn (K ⊔ R) V))
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKX).toEquiv, hXc,
      SBc11.card_of_isPSU_three_three hpsu] at h1
    omega
  have hg2 : IsG2Two ↥(autOn (K ⊔ R) V) :=
    ⟨hXc, center_eq_bot_of_centralizer_le hKX hs.centralizer_le hZK, _,
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).2 hs.normalizes, hidx,
      isPSU_of_equiv_g2Derived hF ((Subgroup.subgroupOfEquivOfLe hKX).trans eK.symm)⟩
  obtain ⟨eA⟩ := nonempty_quasithinG2_mulEquiv_adjointGroup_two hF
  let eX : ↥(autOn (K ⊔ R) V) ≃* ↥(⊤ : Subgroup ↥(adjointGroup .G2 F)) :=
    (MulEquiv.subgroupCongr hJX.symm).trans (e.symm.trans (eA.trans Subgroup.topEquiv.symm))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (ModGL .G2 F) := finite_modGL
  refine ⟨hJX, hpsu, hg2, ?_, ?_⟩
  · exact (isRadicalParabolic_congr eX).2
      (isRadicalParabolic_top_of_holds (CFSG.LieType.Chevalley.holds_adjointGroup_tag .G2 F 2))
  · exact (maxParabolicMaximal_congr eX).2 maxParabolicMaximal_adjointGroupG2

theorem three_of_residueTypeII_g2_of_radical
    (hC132 : ASInputs.AS_C_1_32) (h : Hyp27 H R M K) (hs : StarHyp R K V)
    (hnS : ¬ IsSylowTwoOf R (K ⊔ R))
    (hrad : pCoreOf 2 (autOn (K ⊔ R) V ⊓ Subgroup.normalizer (autOn R V : Set (MulAut ↥V))) =
      autOn R V)
    (hV : IsElemAbelian 2 V)
    (hKT : ∀ T : Subgroup (MulAut (IntMod V hV)), IsSylowTwoOf T (jPStar hV R K) →
      jPStar hV R K = autI hV K ⊔ T)
    (hG : ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ∧
      ∃ π : ↥(quasithinG2 F) →* ↥(jPStar hV R K),
        (FFModel.zornQ (quasithinG2 F)).RealizesVia (jPStar hV R K) (commV (autI hV K))
          (fixV (autI hV K) ⊓ commV (autI hV K)) π ∧
        ∀ g : ↥(quasithinG2 F),
          ((π g : ↥(jPStar hV R K)) : MulAut (IntMod V hV)) ∈ autI hV K ↔
            (g : quasithinZorn F ≃ₗ[F] quasithinZorn F) ∈ ⁅quasithinG2 F, quasithinG2 F⁆) :
    C27Three H R M K V :=
  (g2StarData_of hs hV hKT hG).2.three hC132 h hs hnS hrad

end CFSG.Quasithin.SmithC27
