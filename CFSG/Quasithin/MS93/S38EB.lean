module

public import CFSG.Quasithin.MS93.S38EBNat
public import CFSG.Quasithin.MS93.S38EStmt
public import CFSG.Quasithin.MS93.S38OffDbl

public section

namespace CFSG.Quasithin.MS93.S38EB

open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank Matrix
open CFSG.Quasithin.MS93.S38D CFSG.Quasithin.MS93.S38E
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem exists_two_elt_preimage {K : Type} [Field K] {α : ↥L →* ↥(StatedSL 3 K)}
    (hα : Function.Surjective α) {X : SL3 K} (hX : X * X = 1) :
    ∃ l : ↥L, toSL3 α l = X ∧ ∃ a : ℕ, l ^ 2 ^ a = 1 := by
  obtain ⟨l₀, hl₀⟩ := toSL3_surjective hα X
  obtain ⟨a, b, hb, ho⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos l₀).ne'
  refine ⟨l₀ ^ b, ?_, a, ?_⟩
  · obtain ⟨k, rfl⟩ := hb
    rw [map_pow, hl₀, pow_succ, pow_mul, sq, hX, one_pow, one_mul]
  · rw [← pow_mul, mul_comm, ← ho, pow_orderOf_eq_one]

variable {S : Type} [CommGroup S] {ρ : ↥M →* MulAut S}

theorem map_le_imL (h : PUHyp M T L) (hX : IsDoubleSL3U M T L) {F : Subgroup G}
    (hF : IsXOff M T F) (hρ : IsIrrRep L ρ) : (F.subgroupOf M).map ρ ≤ IsIrrRep.imL L ρ := by
  obtain ⟨-, -, n, K, _, _, α, hK, hα, hnat⟩ := hX
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime_pow hK
  obtain ⟨β, hβ⟩ := exists_isDblCoord hnat
  obtain ⟨-, -, hd, h2, -, -⟩ := offImg_of_isXOff h hβ hα hF
  have hTN := T_le_normalizer_Uq h
  have hFN := hF.1.trans hTN
  have hLN := L_le_normalizer_Uq h
  set N := M ⊓ Subgroup.centralizer (Uq M T L : Set G)
  have hNn : M ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer
      (le_normalizer_centralizer (le_normalizer_Uq h.le_normalizer))
  have hLN' : ¬ L ≤ N := fun hle =>
    h.not_le_centralizer_of_Uq_le le_rfl (hle.trans inf_le_right)
  have hcomm := h.commutator_le_pCoreOf_M inf_le_left hNn hLN'
  rintro _ ⟨m, hm, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hm
  have hmE := cG_mem_cImg β hFN hm
  obtain ⟨X, hXm⟩ := hd hmE
  have hX2 : X * X = 1 := h2 X (by
    show dHom X ∈ cImg β F
    rw [hXm]
    exact hmE)
  obtain ⟨l, hlX, a, hla⟩ := exists_two_elt_preimage hα hX2
  set lM : ↥M := ⟨l, h.L_le l.2⟩
  set c : ↥M := m * lM⁻¹ with hc
  have hcU : (c : G) ∈ Subgroup.centralizer (Uq M T L : Set G) := by
    have hmN := hTN (hF.1 hm)
    have hlN := hLN l.2
    show (m : G) * (l : G)⁻¹ ∈ Subgroup.centralizer (Uq M T L : Set G)
    rw [← cG_eq_one_iff β (mul_mem hmN (inv_mem hlN))]
    rw [cG_mul β hmN (inv_mem hlN), cG_inv β hlN, cG_of_mem_L hβ hLN l.2, ← hXm]
    have : (⟨(l : G), l.2⟩ : ↥L) = l := rfl
    rw [this, hlX, mul_inv_cancel]
  have hcK : ∀ k ∈ IsIrrRep.imL L ρ, ρ c * k = k * ρ c := by
    rintro _ ⟨l', hl', rfl⟩
    have hmem : ((⁅c, l'⁆ : ↥M) : G) ∈ pCoreOf 2 M :=
      hcomm (Subgroup.commutator_mem_commutator ⟨c.2, hcU⟩ (Subgroup.mem_subgroupOf.mp hl'))
    have h1 := hρ.pCore _ hmem
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1
  have hcl : Commute (ρ c) (ρ lM) := hcK _ ⟨lM, Subgroup.mem_subgroupOf.mpr l.2, rfl⟩
  have hρm : ρ m = ρ c * ρ lM := by rw [hc, map_mul, map_inv, inv_mul_cancel_right]
  have hρc : ρ c = ρ m * (ρ lM)⁻¹ := by rw [hρm, mul_inv_cancel_right]
  have hml : Commute (ρ m) (ρ lM)⁻¹ := by
    rw [hρm]
    exact (hcl.mul_left (Commute.refl _)).inv_right
  have hm2 : ρ m ^ 2 = 1 := by
    have : m ^ 2 = 1 := Subtype.ext (by simpa using hF.2.1.2 _ hm)
    rw [← map_pow, this, map_one]
  have hl2 : ρ lM ^ 2 ^ a = 1 := by
    have : lM ^ 2 ^ a = 1 := Subtype.ext (by simpa using congrArg Subtype.val hla)
    rw [← map_pow, this, map_one]
  have hpow : ρ c ^ 2 ^ (a + 1) = 1 := by
    have e1 : ρ m ^ 2 ^ (a + 1) = 1 := by rw [pow_succ', pow_mul, hm2, one_pow]
    have e2 : ρ lM ^ 2 ^ (a + 1) = 1 := by rw [pow_succ, pow_mul, hl2, one_pow]
    rw [hρc, hml.mul_pow, inv_pow, e1, e2, inv_one, one_mul]
  have hc1 := hρ.cent h (ρ c) ⟨c, rfl⟩ hcK (a + 1) hpow
  exact ⟨lM, Subgroup.mem_subgroupOf.mpr l.2, by rw [hρm, hc1, one_mul]⟩

theorem mem_pCoreOf_of_map_eq_one (h : PUHyp M T L) (hρ : IsIrrRep L ρ) {m : ↥M}
    (hmT : (m : G) ∈ T) (hm : ρ m = 1) : (m : G) ∈ pCoreOf 2 M := by
  obtain ⟨e, he⟩ := h.isPGroup ⟨m, hmT⟩
  refine h.mem_pCoreOf_of_rel IsIrrRep.le_normalizer_kerG hρ.not_le_kerG m.2
    ⟨e, by simpa using congrArg Subtype.val he⟩ fun l hl => ⟨⁅m, ⟨l, h.L_le hl⟩⁆, ?_, rfl⟩
  rw [SetLike.mem_coe, MonoidHom.mem_ker, map_commutatorElement, hm,
    commutatorElement_eq_one_iff_mul_comm, one_mul, mul_one]

theorem card_map_eq (h : PUHyp M T L) (hρ : IsIrrRep L ρ) {F : Subgroup G} (hFT : F ≤ T) :
    Nat.card ((F.subgroupOf M).map ρ) = (pCoreOf 2 M).relIndex F := by
  rw [← Subgroup.relIndex_subgroupOf (hFT.trans h.le), ← MonoidHom.domRestrict_range,
    ← Subgroup.index_ker, MonoidHom.ker_domRestrict, Subgroup.relIndex]
  congr 1
  ext x
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, MonoidHom.mem_ker,
    Subgroup.mem_subgroupOf]
  constructor
  · intro hx
    exact mem_pCoreOf_of_map_eq_one h hρ (hFT (Subgroup.mem_subgroupOf.mp x.2)) hx
  · intro hx
    exact hρ.pCore _ hx

theorem pCore_le_ker {K : Type} [Field K] {α : ↥L →* ↥(StatedSL 3 K)}
    {β : ↥(Uq M T L) ≃* Multiplicative (Fin 2 → Fin 3 → K)} (h : PUHyp M T L)
    (hβ : IsDblCoord L (Uq M T L) α β) : CFSG.pCore 2 ↥L ≤ α.ker := by
  intro o ho
  have hoM : (o : G) ∈ pCoreOf 2 M :=
    pCoreOf_le_pCoreOf_of_le_normalizer h.L_le h.le_normalizer (mem_pCoreOf_of_mem_pCore_two ho)
  have h1 := (cG_eq_one_iff_mem_pCoreOf h β (h.pCore_le hoM)).mpr hoM
  rw [cG_of_mem_L hβ (L_le_normalizer_Uq h) o.2, ← map_one dHom] at h1
  have h2 : toSL3 α o = 1 := dHom_injective h1
  rw [MonoidHom.mem_ker]
  exact (MulEquiv.map_eq_one_iff (specialLinearGroupEquivStatedSL 3 K).symm).mp h2

theorem card_field_eq (h : PUHyp M T L) (hρ : IsIrrRep L ρ) {K₀ : Type} [Field K₀] [Fintype K₀]
    {n : ℕ} {α : ↥L →* ↥(StatedSL 3 K₀)} (hK₀ : Fintype.card K₀ = 2 ^ n)
    (hα : Function.Surjective α) (hnat : IsSumOfNaturalModulesVia L (Uq M T L) ⊥ α false 2)
    {Fq : Type} [Field Fq] [Finite Fq] [CharP Fq 2]
    (e : ↥(StatedSL 3 Fq) ≃* ↥(IsIrrRep.imL L ρ)) : Nat.card Fq = Nat.card K₀ := by
  obtain ⟨β, hβ⟩ := exists_isDblCoord hnat
  set αb : ↥L ⧸ CFSG.pCore 2 ↥L →* ↥(StatedSL 3 K₀) :=
    QuotientGroup.lift _ α (pCore_le_ker h hβ)
  have hαbs : Function.Surjective αb := by
    intro y
    obtain ⟨l, rfl⟩ := hα y
    exact ⟨QuotientGroup.mk l, rfl⟩
  have hαbn : ∃ k, αb k ≠ 1 := by
    obtain ⟨k, hk⟩ := hαbs (specialLinearGroupEquivStatedSL 3 K₀ (rootElt 0 1 1))
    refine ⟨k, ?_⟩
    rw [hk, Ne, MulEquiv.map_eq_one_iff, rootElt_eq_one_iff (by decide)]
    exact one_ne_zero
  have e₁ := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple h.quasisimple hαbs
    (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple h.quasisimple hαbn)
  have e₂ := CFSG.LieType.CurtisTits.centralQuotientEquivOfIsQuasisimple h.quasisimple
    (hρ.quotHom_surjective h)
    (CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple h.quasisimple (hρ.quotHom_ne_one h))
  have hK₀' : Nat.card K₀ = 2 ^ n := by rw [Nat.card_eq_fintype_card, hK₀]
  have := Fintype.ofFinite Fq
  obtain ⟨n', -, hn'⟩ := FiniteField.card Fq 2
  have hFq : Nat.card Fq = 2 ^ (n' : ℕ) := by rw [Nat.card_eq_fintype_card, hn']
  obtain ⟨hn1, -, hc₀⟩ := isPSL_quot_of_equiv_statedSL_three hK₀' (MulEquiv.refl _)
  obtain ⟨hn1', -, hcq⟩ := isPSL_quot_of_equiv_statedSL_three hFq e
  have heq : CFSG.Open.ordA 2 (2 ^ n) = CFSG.Open.ordA 2 (2 ^ (n' : ℕ)) := by
    rw [← hc₀, ← hcq]
    exact Nat.card_congr (e₁.symm.trans e₂).toEquiv
  obtain ⟨r, hr, hr'⟩ := CFSG.Quasithin.H13.VolI.two_part_ordA_two hn1
  obtain ⟨s, hs, hs'⟩ := CFSG.Quasithin.H13.VolI.two_part_ordA_two hn1'
  have h3 := CFSG.Timmesfeld.Orders.eq_of_two_pow_mul_odd hr hs (hr'.symm.trans (heq.trans hs'))
  rw [hFq, hK₀']
  congr 1
  omega

end CFSG.Quasithin.MS93.S38EB

namespace CFSG.Quasithin.MS93.S38E

open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.MS93.S38EB

theorem sl3SecBound_holds : SL3SecBound := by
  intro G _ _ M T L h _hcent hX F hF S _ _ ρ hρ Fq _ _ hR
  obtain ⟨I, π, hπ⟩ : ∃ (I : Subgroup S) (π : ↥(StatedSL 3 Fq) →* ↥(IsIrrRep.imL L ρ)),
      (FFModel.nat (StatedSL 3 Fq)).RealizesVia (IsIrrRep.imL L ρ) I ⊥ π := by
    rcases hR with ⟨π, hπ⟩ | ⟨I, π, -, -, -, hI⟩
    · exact ⟨⊤, π, hπ⟩
    · exact ⟨I 0, π, hI 0⟩
  have : CharP Fq 2 := charP_two_of_realizesVia hρ.sq hπ
  have hπb : Function.Bijective π :=
    ⟨FFC.injective_of_faithful_sec (FFModel.nat_faithful _) hπ, hπ.1⟩
  obtain ⟨-, -, n, K₀, _, _, α, hK₀, hα, hnat⟩ := id hX
  have hq : Nat.card Fq = Nat.card K₀ :=
    card_field_eq h hρ hK₀ hα hnat (MulEquiv.ofBijective π hπb)
  have hcardE : Nat.card ((F.subgroupOf M).map ρ) = Nat.card Fq ^ 2 := by
    rw [card_map_eq h hρ hF.1, h.relIndex_of_isXOff_of_doubleNat hK₀ hα hnat hF, hq,
      Nat.card_eq_fintype_card]
  refine card_pow_three_le hπ (map_le_imL h hX hF hρ) ?_ ?_ hcardE
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul]
    congr 1
    have := hF.2.1.1.is_comm.comm ⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩
      ⟨(y : G), Subgroup.mem_subgroupOf.mp hy⟩
    have h' : (x : G) * y = y * x := congrArg Subtype.val this
    exact Subtype.ext h'
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul]
    have : x * x = 1 := Subtype.ext (by simpa [sq] using hF.2.1.2 _ (Subgroup.mem_subgroupOf.mp hx))
    rw [this, map_one]

end CFSG.Quasithin.MS93.S38E
