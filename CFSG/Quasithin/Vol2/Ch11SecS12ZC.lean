module

public import CFSG.Quasithin.Vol2.Ch11SecSObl
public import CFSG.Quasithin.Vol2.Ch11SecSI3
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11StatementsInputsAS
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch11SecS12K
public import CFSG.Quasithin.Vol2.Ch11SecS12YF
public import CFSG.Quasithin.Vol2.Ch11SecSCartan
public import CFSG.Quasithin.Vol2.Ch11SecSFacts4

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint

@[expose] def FactShapeWeyl : Prop :=
  ∀ (Q : Type) [Group Q] [Finite Q], Shape4 Q → ¬ IsPSL 3 2 2 Q →
    ∀ S : Subgroup Q, QuasithinUnique.IsSylowTwoOf S ⊤ →
    ∀ B₁ B₂ : Subgroup Q, B₁ ≠ B₂ → IsL24Sub S B₁ → IsL24Sub S B₂ →
    ∀ E : Subgroup Q, Nat.card ↥E = 9 → E ≤ Subgroup.normalizer (B₁ : Set Q) →
      E ≤ Subgroup.normalizer (B₂ : Set Q) →
      (∀ H : Subgroup Q, B₂ ≤ H → S ≤ H → E ≤ H →
        H = ⊤ ∨ H ≤ Subgroup.normalizer (B₂ : Set Q)) ∧
      ∀ E₂ : Subgroup Q, E₂ ≤ E ⊓ sectionCentralizer B₂ (pCoreOf 2 B₂) → E₂ ≠ ⊥ →
        ¬ Subgroup.normalizer (E₂ : Set Q) ≤ Subgroup.normalizer (B₂ : Set Q)

end CFSG.Quasithin.Vol2.Ch11.SecS

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G] {T L I V₁ V₂ X K : Subgroup G}

theorem xOne_eq_xOne_two (hC : SecS.CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder)
    (hFb : Facts12b) (h1102 : Stmt11_0_2) (h : SecS.StarHyp G T L I V₁ V₂ X K)
    (hSL3 : KindSL3 L (fsuV T I) 2) : xOne X (LOf L V₁) = xOne X (LOf L V₂) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hc := (SecS.cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  have hSL := isSL3_four_of h1102 h.hyp hSL3
  have hXN₂ : X ≤ Subgroup.normalizer (LOf L V₂ : Set G) :=
    SecS.cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inr rfl) h.v₂ h.cartan
  have hL₂L : LOf L V₂ ≤ L := (perfectCore_le _).trans inf_le_left
  have hO : pCoreOf 2 L ⊓ LOf L V₂ ≤ pCoreOf 2 (LOf L V₂) := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_left)
    intro g hg
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hL₂L hg), Subgroup.le_normalizer hg⟩
  have hle : xOne X (LOf L V₁) ≤ xOne X (LOf L V₂) := by
    intro x hx
    have hxN := hXN₂ hx.1
    refine ⟨hx.1, hxN, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _ hxN,
      fun l hl => hO ⟨SecA.C11P9B.commutator_mem_of_isSL3 hFb hN h1102 h.hyp h.v₁ h.v₂
        h.cartan hSL hx (hL₂L hl), ?_⟩⟩
    have h1 : x * l * x⁻¹ ∈ LOf L V₂ := (Subgroup.mem_normalizer_iff.mp hxN l).mp hl
    exact (LOf L V₂).mul_mem h1 ((LOf L V₂).inv_mem hl)
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hc.cardX₁, hc.cardX₂])

theorem not_normalizer_xOne_le (hW : SecS.FactShapeWeyl) (hAm : SecS.Obl11_1_2StarAmalgam)
    (hSh : SecS.Obl11_1_2StarShape) (hF : SecS.FactL34Parab) (hLevi : SecS.FactL34Levi)
    (hT : SecS.FactPGL34Torus) (hNo : SecS.FactL34NoE9) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hC : SecS.CartanFacts) (hN : NatFacts) (hG2 : FactG2DerivedOrder)
    (hFb : Facts12b) (h1102 : Stmt11_0_2) (h : SecS.StarHyp G T L I V₁ V₂ X K)
    (hSL3 : KindSL3 L (fsuV T I) 2) :
    ¬ Subgroup.normalizer (xOne X (LOf L V₁) : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  intro hle
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have cL := (SecS.cartan_of hC hN hG2 h1102 h.hyp h.v₁ h.v₂ h.cartan).1
  have hL₁ne : LOf L V₁ ≠ ⊥ :=
    ne_bot_of_mem_cComp (lOf_mem_lFamily hN h1102 h.hyp h.v₁ (Or.inl rfl) le_rfl)
  obtain ⟨P₁, P₂, hP⟩ := h.exists_parData hF hL₁ne
  have hIsK0 : SecS.IsK0 T L V₁ K (SecS.k0Of K P₂) :=
    ⟨h.isLocal_k0Of hP, SecS.k0Of_le K P₂, SecS.StarHyp.k0Of_ne_K hP,
      SecS.StarHyp.k0Of_ne_L₁ hP⟩
  have hY := hAm G T L I V₁ V₂ X K _ h hIsK0
  obtain ⟨I₀, hI₀, hTI₀, hK₀I₀, hL₂I₀, hXI₀⟩ := h.exists_cComp_I h37 h38 h39 hN h1102 cL hP hY
  obtain ⟨-, hshape⟩ := hSh G T L I V₁ V₂ X K _ I₀ h hIsK0 hY hI₀ hTI₀ hK₀I₀ hL₂I₀ hXI₀
  have D := h.inspData_k0Of hLevi hT hN h1102 cL hP hTI₀ hK₀I₀ hL₂I₀ hXI₀
  have hnPSL := h.not_isPSL_of_le hNo hLevi hT hN h1102 cL hP hTI₀ hK₀I₀ hL₂I₀ hXI₀
  obtain ⟨hmax, hweyl⟩ := hW _ hshape hnPSL _ D.syl _ _ D.ne ⟨D.ne₁, D.p₁, D.n₁, D.sl₁⟩
    ⟨D.ne₂, D.p₂, D.n₂, D.sl₂⟩ _ D.card D.e₁ D.e₂
  have hSI : QuasithinUnique.IsSylowTwoOf (T ⊓ I₀) I₀ :=
    A4.isSylowTwoOf_inf_normal (isSylowTwoOf_of_quasithinIsSylowTwo h.sylow le_sup_right)
      le_sup_left (sup_le Subgroup.le_normalizer hTI₀)
  have hOI : pCoreOf 2 I₀ ≤ T := (pCoreOf_two_le_of_isSylowTwoOf hSI).trans inf_le_left
  have hL₂M : LOf L V₂ ≤ Subgroup.normalizer (L : Set G) :=
    ((perfectCore_le _).trans inf_le_left).trans Subgroup.le_normalizer
  have hXM : X ≤ Subgroup.normalizer (L : Set G) := fun x hx =>
    Subgroup.le_normalizer (h.cartan.1 hx).1
  have hHtop : modO2Image I₀ (I₀ ⊓ Subgroup.normalizer (L : Set G)) ≠ ⊤ := by
    intro htop
    apply h.k0Of_not_le hP
    exact hK₀I₀.trans ((SecS.le_sup_of_modO2Image_eq_top inf_le_left htop).trans
      (sup_le inf_le_right (hOI.trans h.hyp.normal)))
  have hH := (hmax (modO2Image I₀ (I₀ ⊓ Subgroup.normalizer (L : Set G)))
    (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr ⟨x.2, hL₂M hx⟩)
    (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr ⟨x.2, h.hyp.normal hx.1⟩)
    (Subgroup.map_mono fun x hx => Subgroup.mem_subgroupOf.mpr ⟨x.2, hXM hx⟩)).resolve_left
      hHtop
  have hX₁₂ := xOne_eq_xOne_two hC hN hG2 hFb h1102 h hSL3
  have hX₂I₀ : xOne X (LOf L V₂) ≤ I₀ := inf_le_left.trans hXI₀
  have hcard₂ : Nat.card ↥(modO2Image I₀ (xOne X (LOf L V₂))) = 3 := by
    rw [SecS.card_modO2Image_of_odd hX₂I₀ (by rw [cL.cardX₂]; decide), cL.cardX₂]
  have hE₂le : modO2Image I₀ (xOne X (LOf L V₂)) ≤ modO2Image I₀ X ⊓
      sectionCentralizer (modO2Image I₀ (LOf L V₂)) (pCoreOf 2 (modO2Image I₀ (LOf L V₂))) := by
    rintro _ ⟨⟨x, hxI⟩, hx, rfl⟩
    exact ⟨⟨⟨x, hxI⟩, (Subgroup.mem_subgroupOf.mp hx).1, rfl⟩,
      SecS.mk_mem_sectionCentralizer hL₂I₀ hxI (Subgroup.mem_subgroupOf.mp hx).2⟩
  have hE₂ne : modO2Image I₀ (xOne X (LOf L V₂)) ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcard₂
    norm_num at hcard₂
  obtain ⟨q', hq'E, hq'B⟩ := IsConcreteLE.not_le_iff_exists.mp (hweyl _ hE₂le hE₂ne)
  obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥I₀) q'
  have hN2 : ¬ 3 ∣ Nat.card ↥(QuotientGroup.mk' (CFSG.pCore 2 ↥I₀)).ker := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hp : IsPGroup 2 ↥(QuotientGroup.mk' (CFSG.pCore 2 ↥I₀)).ker := by
      rw [QuotientGroup.ker_mk']
      exact CFSG.LieType.BorelTits.pCore_isPGroup 2
    obtain ⟨k, hk⟩ := hp.exists_card_eq
    rw [hk]
    intro h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  have hX3 : IsPGroup 3 ↥((xOne X (LOf L V₂)).subgroupOf I₀) := IsPGroup.of_card (n := 1) (by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hX₂I₀).toEquiv, cL.cardX₂, pow_one])
  have hw : ((xOne X (LOf L V₂)).subgroupOf I₀).map (MulAut.conj q).toMonoidHom ≤
      (xOne X (LOf L V₂)).subgroupOf I₀ ⊔ (QuotientGroup.mk' (CFSG.pCore 2 ↥I₀)).ker := by
    rw [← Subgroup.comap_map_eq]
    rintro _ ⟨z, hz, rfl⟩
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_mul, map_mul,
      map_inv]
    exact (Subgroup.mem_normalizer_iff.mp hq'E _).mp ⟨z, hz, rfl⟩
  obtain ⟨n, hn, hnq⟩ := C11AmS.S12.exists_mul_mem_normalizer (p := 3) hX3 hN2 hw
  have hgN : ((n * q : ↥I₀) : G) ∈ Subgroup.normalizer (xOne X (LOf L V₂) : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 := (Subgroup.mem_normalizer_iff.mp hnq ⟨z, hX₂I₀ hz⟩).mp
        (Subgroup.mem_subgroupOf.mpr hz)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hz
      have hzI : z ∈ I₀ := by
        have := I₀.mul_mem (I₀.mul_mem (I₀.inv_mem (n * q).2) (hX₂I₀ hz)) (n * q).2
        simpa [mul_assoc] using this
      have h1 := (Subgroup.mem_normalizer_iff.mp hnq ⟨z, hzI⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hz)
      exact Subgroup.mem_subgroupOf.mp h1
  have hgM : ((n * q : ↥I₀) : G) ∈ Subgroup.normalizer (L : Set G) := hle (hX₁₂ ▸ hgN)
  apply hq'B
  have hmem : QuotientGroup.mk' (CFSG.pCore 2 ↥I₀) (n * q) ∈
      modO2Image I₀ (I₀ ⊓ Subgroup.normalizer (L : Set G)) :=
    ⟨n * q, Subgroup.mem_subgroupOf.mpr ⟨(n * q).2, hgM⟩, rfl⟩
  rw [map_mul, (MonoidHom.mem_ker).mp hn, one_mul] at hmem
  exact hH hmem

theorem pCoreOf_normalizer_eq_bot {M X₁ L' : Subgroup G} (hU : IsUniqueM L' M)
    (hL' : L' ≤ Subgroup.normalizer (X₁ : Set G))
    (hnle : ¬ Subgroup.normalizer (X₁ : Set G) ≤ M) :
    pCoreOf 2 (Subgroup.normalizer (X₁ : Set G)) = ⊥ := by
  by_contra hne
  obtain ⟨M', hM', hle⟩ := exists_inM_of_pCoreOf_ne_bot hne
  have := hU.2 M' ⟨hM', hL'.trans hle⟩
  exact hnle (this ▸ hle)

theorem pRank_pCoreOf_le_two (h128 : ASInputs.AS_A_1_28)
    (hqtke : QuasithinUnique.quasithinIsQTKECat G)
    {H E : Subgroup G} (hE : IsElemAbelian 2 E) (hE16 : 16 ≤ Nat.card E) (hEH : E ≤ H)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p (pCoreOf p H) ≤ 2 := by
  by_contra hlt
  push Not at hlt
  have hG0 : ∀ P : Subgroup G, P ≠ ⊥ → IsPGroup 2 P →
      CFSG.pRank p ↥(Subgroup.normalizer (P : Set G)) ≤ 2 := fun P hP h2 => by
    rw [BlueprintB2.pRank_eq_open_pRank]
    exact pRank_le_two_of_isTwoLocal hqtke ⟨P, hP, h2, rfl⟩ hp hp2
  have h3 := (h128 G p hp hp2 hG0 H (by rw [BlueprintB2.pRank_eq_open_pRank]; exact hlt)).1
  rw [BlueprintB2.pRank_eq_open_pRank] at h3
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE2 : IsPGroup 2 ↥E := fun x => ⟨1, Subtype.ext (by simpa using hE.2 x x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hE2
  have hk4 : 4 ≤ k := by
    by_contra hk4
    push Not at hk4
    have : 2 ^ k ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h4 : k ≤ CFSG.Open.pRank 2 H := by
    refine le_csSup ⟨Nat.card G, fun j hj => ?_⟩ ⟨E, hEH, hE, hk⟩
    obtain ⟨E', -, -, hE'⟩ := hj
    have h1 : j < 2 ^ j := Nat.lt_pow_self (by norm_num)
    have h2 : Nat.card E' ≤ Nat.card G := Subgroup.card_le_card_group E'
    omega
  omega

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12
