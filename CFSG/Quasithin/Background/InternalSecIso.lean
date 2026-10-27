module

public import CFSG.Quasithin.H13.StatementsFSU
public import CFSG.Quasithin.H13.StatementsVocab
public import CFSG.Quasithin.Background.InternalSecAutOn
public import CFSG.Quasithin.Background.InternalSecB5

public section

namespace CFSG.Quasithin.InternalSec

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13 CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

section Int

variable {G : Type} [Group G] {V L A B : Subgroup G} [IsMulCommutative ↥V]

omit [IsMulCommutative ↥V] in
theorem autOn_inv_subgroupOf (hLA : L ≤ Subgroup.normalizer (A : Set G)) :
    ∀ k ∈ autOn L V, ∀ w ∈ A.subgroupOf V, k w ∈ A.subgroupOf V := by
  intro k hk w hw
  obtain ⟨g, hg, rfl⟩ := Setup.mem_autOn_iff.1 hk
  rw [Subgroup.mem_subgroupOf, coe_conjAct_apply]
  exact (Subgroup.mem_normalizer_iff.mp (hLA hg) w).mp hw

omit [IsMulCommutative ↥V] in
theorem irr_subgroupOf (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hirr : ∀ J : Subgroup G, J ≤ A → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = A) :
    ∀ J : Subgroup ↥V, J ≤ A.subgroupOf V → (∀ k ∈ autOn L V, ∀ w ∈ J, k w ∈ J) →
      J = ⊥ ∨ J = A.subgroupOf V := by
  intro J hJA hJ
  set J' : Subgroup G := J.map V.subtype with hJ'
  have hmemJ' : ∀ v : ↥V, (v : G) ∈ J' ↔ v ∈ J := fun v =>
    ⟨fun ⟨w, hw, hwv⟩ => (Subtype.ext hwv : w = v) ▸ hw, fun hv => ⟨v, hv, rfl⟩⟩
  have h2 : J' ≤ A := by
    rintro _ ⟨w, hw, rfl⟩
    exact hJA hw
  have hinv : ∀ l ∈ L, ∀ n ∈ J', l * n * l⁻¹ ∈ J' := by
    rintro l hl _ ⟨w, hw, rfl⟩
    refine ⟨_, hJ _ (conjAct_mem_autOn hLV hl) w hw, ?_⟩
    show ((conjAct V ⟨l, hLV hl⟩ w : ↥V) : G) = l * (w : G) * l⁻¹
    rw [coe_conjAct_apply]
  have h3 : L ≤ Subgroup.normalizer (J' : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro n
    refine ⟨fun hn => hinv l hl n hn, fun hn => ?_⟩
    have := hinv l⁻¹ (L.inv_mem hl) _ hn
    simpa [mul_assoc] using this
  rcases hirr J' h2 h3 with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    have := (hmemJ' v).2 hv
    rw [h, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.2 (Subtype.ext this)
  · right
    ext v
    rw [← hmemJ', h, Subgroup.mem_subgroupOf]

theorem not_le_fixV_subgroupOf (hAV : A ≤ V) (hLV : L ≤ Subgroup.normalizer (V : Set G))
    (hne : ¬ A ≤ Subgroup.centralizer (L : Set G)) : ¬ A.subgroupOf V ≤ fixV (autOn L V) := by
  intro h
  apply hne
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h1 := h (show (⟨a, hAV ha⟩ : ↥V) ∈ A.subgroupOf V from ha) _ (conjAct_mem_autOn hLV hl)
  have h2 := congrArg Subtype.val h1
  rw [coe_conjAct_apply] at h2
  calc l * a = (l * a * l⁻¹) * l := by group
    _ = a * l := by rw [show l * a * l⁻¹ = a from h2]

omit [IsMulCommutative ↥V] in
theorem sup_subgroupOf_eq_top (hAV : A ≤ V) (hBV : B ≤ V) (hsum : A ⊔ B = V) :
    A.subgroupOf V ⊔ B.subgroupOf V = ⊤ := by
  apply Subgroup.map_injective V.subtype_injective
  rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hAV,
    Subgroup.map_subgroupOf_eq_of_le hBV, hsum, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

omit [IsMulCommutative ↥V] in
theorem inf_subgroupOf_eq_bot (hinf : A ⊓ B = ⊥) : A.subgroupOf V ⊓ B.subgroupOf V = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have : (x : G) ∈ A ⊓ B := ⟨hx.1, hx.2⟩
  rw [hinf, Subgroup.mem_bot] at this
  exact Subgroup.mem_bot.2 (Subtype.ext this)

omit [IsMulCommutative ↥V] in
@[expose] noncomputable def botQuotEquiv (hAV : A ≤ V) :
    ↥A ⧸ (⊥ : Subgroup G).subgroupOf A ≃* ↥(A.subgroupOf V) :=
  ((QuotientGroup.quotientMulEquivOfEq (Subgroup.bot_subgroupOf A)).trans
    QuotientGroup.quotientBot).trans (Subgroup.subgroupOfEquivOfLe hAV).symm

omit [IsMulCommutative ↥V] in
theorem botQuotEquiv_mk (hAV : A ≤ V) (a : ↥A) :
    (((botQuotEquiv hAV (QuotientGroup.mk a) : ↥(A.subgroupOf V)) : ↥V) : G) = a := rfl

theorem isXSectionIso₂_of_secIsoL (hAV : A ≤ V) (hBV : B ≤ V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hLB : L ≤ Subgroup.normalizer (B : Set G))
    (h : SecIsoL (autOn L V) (A.subgroupOf V) ⊥ (B.subgroupOf V) ⊥) :
    IsXSectionIso₂ L A ⊥ B ⊥ := by
  obtain ⟨e, he⟩ := equiv_of_secIsoL h
  have hnA : ((⊥ : Subgroup G).subgroupOf A).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  have hnB : ((⊥ : Subgroup G).subgroupOf B).Normal := by
    rw [Subgroup.bot_subgroupOf]
    infer_instance
  refine ⟨hnA, hnB, (botQuotEquiv hAV).trans (e.trans (botQuotEquiv hBV).symm), ?_⟩
  intro x hx j k hj hk hjk
  have hjk' :
      e (botQuotEquiv hAV (QuotientGroup.mk j)) = botQuotEquiv hBV (QuotientGroup.mk k) := by
    have := congrArg (botQuotEquiv hBV) hjk
    simpa using this
  set c := conjAct V ⟨x, hLV hx⟩ with hcdef
  have hc : c ∈ autOn L V := conjAct_mem_autOn hLV hx
  set w := botQuotEquiv hAV (QuotientGroup.mk j) with hw
  have hw1 : c w ∈ A.subgroupOf V := autOn_inv_subgroupOf hLA c hc w w.2
  have hw2 : c (e w) ∈ B.subgroupOf V := autOn_inv_subgroupOf hLB c hc _ (e w).2
  have key := he ⟨c, hc⟩ w hw1 hw2
  show (botQuotEquiv hBV).symm (e (botQuotEquiv hAV (QuotientGroup.mk ⟨x * j * x⁻¹, hj⟩))) =
    QuotientGroup.mk ⟨x * k * x⁻¹, hk⟩
  rw [MulEquiv.symm_apply_eq]
  have e1 : botQuotEquiv hAV (QuotientGroup.mk ⟨x * j * x⁻¹, hj⟩) = ⟨c w, hw1⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    show x * (j : G) * x⁻¹ = ((c w : ↥V) : G)
    rw [hcdef, coe_conjAct_apply, hw, botQuotEquiv_mk]
  rw [e1, key]
  apply Subtype.ext
  apply Subtype.ext
  show ((c (e w) : ↥V) : G) = x * (k : G) * x⁻¹
  rw [hcdef, coe_conjAct_apply, hw, hjk', botQuotEquiv_mk]

theorem not_secIsoL_of_not_isXSectionIso₂ (hAV : A ≤ V) (hBV : B ≤ V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hLB : L ≤ Subgroup.normalizer (B : Set G)) (h : ¬ IsXSectionIso₂ L A ⊥ B ⊥) :
    ¬ SecIsoL (autOn L V) (A.subgroupOf V) ⊥ (B.subgroupOf V) ⊥ :=
  fun hs => h (isXSectionIso₂_of_secIsoL hAV hBV hLV hLA hLB hs)

theorem not_secIsoL_of_not_isXSectionIso (hAV : A ≤ V) (hBV : B ≤ V)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hLB : L ≤ Subgroup.normalizer (B : Set G)) (h : ¬ IsXSectionIso L ⊥ A B) :
    ¬ SecIsoL (autOn L V) (A.subgroupOf V) ⊥ (B.subgroupOf V) ⊥ :=
  fun hs => h (isXSectionIso₂_of_secIsoL hAV hBV hLV hLA hLB hs)

end Int

section Sum

variable {G : Type} [Group G] [Finite G] {V L A B : Subgroup G} [IsMulCommutative ↥V]

theorem not_isFFModule_normalizer_autOn_of_sum (h51 : AsB51) (hV2 : ∀ v ∈ V, v ^ 2 = 1)
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hq : CFSG.IsQuasisimple ↥(autOn L V))
    (hS : SQTKGroup ↥(autOn L V)) (hAV : A ≤ V) (hBV : B ≤ V) (hsum : A ⊔ B = V)
    (hinf : A ⊓ B = ⊥) (hLA : L ≤ Subgroup.normalizer (A : Set G))
    (hLB : L ≤ Subgroup.normalizer (B : Set G))
    (hirrA : ∀ J : Subgroup G, J ≤ A → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = A)
    (hirrB : ∀ J : Subgroup G, J ≤ B → L ≤ Subgroup.normalizer (J : Set G) → J = ⊥ ∨ J = B)
    (hntA : ¬ A ≤ Subgroup.centralizer (L : Set G))
    (hntB : ¬ B ≤ Subgroup.centralizer (L : Set G)) (hnoniso : ¬ IsXSectionIso₂ L A ⊥ B ⊥)
    (hLn : ∀ n : ℕ, (n = 4 ∨ n = 5) →
      ∀ π : ↥(StatedSL n (ZMod 2)) →* ↥(autOn L V), ¬ Function.Surjective π) :
    ¬ IsFFModule (Subgroup.normalizer (autOn L V : Set (MulAut ↥V))) := by
  have hV : ∀ v : ↥V, v ^ 2 = 1 := fun v => Subtype.ext (by simpa using hV2 v v.2)
  exact not_isFFModule_normalizer_of_sum h51 hV hq hS (sup_subgroupOf_eq_top hAV hBV hsum)
    (inf_subgroupOf_eq_bot hinf) (autOn_inv_subgroupOf hLA) (autOn_inv_subgroupOf hLB)
    (irr_subgroupOf hLV hirrA) (irr_subgroupOf hLV hirrB) (not_le_fixV_subgroupOf hAV hLV hntA)
    (not_le_fixV_subgroupOf hBV hLV hntB)
    (not_secIsoL_of_not_isXSectionIso₂ hAV hBV hLV hLA hLB hnoniso) hLn

end Sum

end CFSG.Quasithin.InternalSec
