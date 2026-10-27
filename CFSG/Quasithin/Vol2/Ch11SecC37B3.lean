module

public import CFSG.Quasithin.Vol2.Ch11SecC37B2
public import CFSG.Quasithin.Vol2.Ch11SecCB51

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecC

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.Quasithin.InternalSec
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isXSectionIso₂_symm {X J C K D : Subgroup G} (h : IsXSectionIso₂ X J C K D) :
    IsXSectionIso₂ X K D J C := by
  obtain ⟨hC, hD, e, he⟩ := h
  refine ⟨hD, hC, e.symm, fun x hx k j hk hj hkj => ?_⟩
  have h1 : e (j : ↥J ⧸ C.subgroupOf J) = (k : ↥K ⧸ D.subgroupOf K) := by
    rw [← hkj, MulEquiv.apply_symm_apply]
  rw [← he x hx j k hj hk h1, MulEquiv.symm_apply_apply]

omit [Finite G] in
theorem fix_of_mul_fix {W₁ W₂ : Subgroup G} (h12 : W₁ ⊓ W₂ = ⊥) {x : G}
    (h1 : x ∈ Subgroup.normalizer (W₁ : Set G)) (h2 : x ∈ Subgroup.normalizer (W₂ : Set G))
    {a b : G} (ha : a ∈ W₁) (hb : b ∈ W₂) (hx : x * (a * b) * x⁻¹ = a * b) :
    x * a * x⁻¹ = a ∧ x * b * x⁻¹ = b := by
  have ha' : x * a * x⁻¹ ∈ W₁ := (Subgroup.mem_normalizer_iff.mp h1 a).mp ha
  have hb' : x * b * x⁻¹ ∈ W₂ := (Subgroup.mem_normalizer_iff.mp h2 b).mp hb
  have e : a⁻¹ * (x * a * x⁻¹) = b * (x * b * x⁻¹)⁻¹ := by
    have : (x * a * x⁻¹) * (x * b * x⁻¹) = a * b := by rw [← hx]; group
    calc a⁻¹ * (x * a * x⁻¹) = a⁻¹ * ((x * a * x⁻¹) * (x * b * x⁻¹)) * (x * b * x⁻¹)⁻¹ := by
          group
      _ = b * (x * b * x⁻¹)⁻¹ := by rw [this]; group
  have hmem : a⁻¹ * (x * a * x⁻¹) ∈ W₁ ⊓ W₂ :=
    ⟨W₁.mul_mem (W₁.inv_mem ha) ha', e ▸ W₂.mul_mem hb (W₂.inv_mem hb')⟩
  rw [h12, Subgroup.mem_bot] at hmem
  have hxa : x * a * x⁻¹ = a := by
    have := congrArg (a * ·) hmem
    simpa using this
  refine ⟨hxa, ?_⟩
  rw [hmem] at e
  exact (mul_inv_eq_one.mp e.symm).symm

omit [Finite G] in
theorem transfer_fix {L P W₁ W₂ : Subgroup G} (hPL : P ≤ L)
    (hiso : IsXSectionIso₂ L W₁ ⊥ W₂ ⊥) (hL1 : L ≤ Subgroup.normalizer (W₁ : Set G))
    (hL2 : L ≤ Subgroup.normalizer (W₂ : Set G)) {d : G} (hdL : d ∈ L)
    (h : ∀ u ∈ W₁, (∀ p ∈ P, p * u * p⁻¹ = u) → d * u * d⁻¹ = u) :
    ∀ u ∈ W₂, (∀ p ∈ P, p * u * p⁻¹ = u) → d * u * d⁻¹ = u := by
  obtain ⟨_, _, e, he⟩ := hiso
  have hinj1 : ∀ a b : ↥W₁, (a : ↥W₁ ⧸ (⊥ : Subgroup G).subgroupOf W₁) = b → a = b := by
    intro a b hab
    rw [QuotientGroup.eq, Subgroup.bot_subgroupOf, Subgroup.mem_bot, inv_mul_eq_one] at hab
    exact hab
  have hinj2 : ∀ a b : ↥W₂, (a : ↥W₂ ⧸ (⊥ : Subgroup G).subgroupOf W₂) = b → a = b := by
    intro a b hab
    rw [QuotientGroup.eq, Subgroup.bot_subgroupOf, Subgroup.mem_bot, inv_mul_eq_one] at hab
    exact hab
  intro u hu hfix
  obtain ⟨q, hq⟩ := e.surjective (⟨u, hu⟩ : ↥W₂)
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  have hconj : ∀ x ∈ L, ∀ (hj : x * (w : G) * x⁻¹ ∈ W₁) (hk : x * u * x⁻¹ ∈ W₂),
      e ((⟨x * (w : G) * x⁻¹, hj⟩ : ↥W₁) : ↥W₁ ⧸ (⊥ : Subgroup G).subgroupOf W₁) =
        ((⟨x * u * x⁻¹, hk⟩ : ↥W₂) : ↥W₂ ⧸ (⊥ : Subgroup G).subgroupOf W₂) :=
    fun x hx hj hk => he x hx w ⟨u, hu⟩ hj hk hq
  have hwfix : ∀ p ∈ P, p * (w : G) * p⁻¹ = w := by
    intro p hp
    have hj := (Subgroup.mem_normalizer_iff.mp (hL1 (hPL hp)) w).mp w.2
    have hk := (Subgroup.mem_normalizer_iff.mp (hL2 (hPL hp)) u).mp hu
    have h1 := hconj p (hPL hp) hj hk
    have h2 : (⟨p * u * p⁻¹, hk⟩ : ↥W₂) = ⟨u, hu⟩ := Subtype.ext (hfix p hp)
    rw [h2, ← hq] at h1
    exact congrArg Subtype.val (hinj1 _ _ (e.injective h1))
  have hdw := h w w.2 hwfix
  have hj := (Subgroup.mem_normalizer_iff.mp (hL1 hdL) w).mp w.2
  have hk := (Subgroup.mem_normalizer_iff.mp (hL2 hdL) u).mp hu
  have h1 := hconj d hdL hj hk
  have h2 : (⟨d * (w : G) * d⁻¹, hj⟩ : ↥W₁) = w := Subtype.ext hdw
  rw [h2, hq] at h1
  exact (congrArg Subtype.val (hinj2 _ _ h1)).symm

@[expose] def PerDich (L P U : Subgroup G) (d : G) : Prop :=
  (∀ u ∈ U, (∀ p ∈ P, p * u * p⁻¹ = u) →
      d * u * d⁻¹ * u⁻¹ ∈ Subgroup.centralizer (L : Set G)) ∨
    (∀ u ∈ U, (∀ p ∈ P, p * u * p⁻¹ = u) → d * u * d⁻¹ = u →
      u ∈ Subgroup.centralizer (L : Set G))

omit [Finite G] in
theorem commutator_le_W (T L : Subgroup G) : ⁅VZ T (L ⊔ T), L⁆ ≤ VZ T (L ⊔ T) := by
  rw [Subgroup.commutator_le]
  intro w hw l hl
  have := (Subgroup.mem_normalizer_iff.mp (le_normalizer_VZ T (L ⊔ T)
    (le_sup_left (a := L) hl)) w⁻¹).mp ((VZ T (L ⊔ T)).inv_mem hw)
  rw [commutatorElement_def, mul_assoc, mul_assoc, ← mul_assoc l]
  exact (VZ T (L ⊔ T)).mul_mem hw this

omit [Finite G] in
theorem L_le_normalizer_U (T L : Subgroup G) :
    L ≤ Subgroup.normalizer ((⁅VZ T (L ⊔ T), L⁆ : Subgroup G) : Set G) :=
  le_sup_right.trans (A3.sup_le_normalizer_commutator _ L)

namespace Set37

variable {T L I : Subgroup G} {n : ℕ} {V₁ H : Subgroup G} {g : G} (s : Set37 T L I n V₁ H g)
include s

theorem sq_eq_one_U : ∀ u ∈ ⁅VZ T (L ⊔ T), L⁆, u ^ 2 = 1 := fun u hu =>
  s.vzLT.2.1.2 u (commutator_le_W T L hu)

theorem comm_W : ∀ a ∈ VZ T (L ⊔ T), ∀ b ∈ VZ T (L ⊔ T), a * b = b * a := fun a ha b hb =>
  congrArg Subtype.val (s.vzLT.2.1.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)

theorem perDich (h51 : AsB51) (h1102 : Stmt11_0_2) (hKF : KindModuleFacts)
    (hTS : FactTorusLineSL3) (hTP : FactTorusLineSp4) (h1134 : Stmt11_3_4)
    (hJ : L = ⁅L, thompsonJ T⁆)
    (hZL : quasithinOmegaOneCenter T ⊓ Subgroup.centralizer (L : Set G) = ⊥)
    (hVL : fsuV T I ⊓ Subgroup.centralizer (L : Set G) = ⊥) {d : G} (hdL : d ∈ L)
    (hdN : d ∈ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G)) :
    PerDich L (T ⊓ L) ⁅VZ T (L ⊔ T), L⁆ d := by
  obtain ⟨_, hcases⟩ := ffModule_structure_of_two h51 h1102 hKF s.hyp hJ le_rfl
    (sup_le Subgroup.le_normalizer s.hyp.normal) s.vzLT.2.2 (s.fsuV_le_W h1102 hVL)
    (s.commutator_W_ne_bot hZL) s.two_LT
  have hnat : TorusHyp L ⁅VZ T (L ⊔ T), L⁆ (Subgroup.centralizer (L : Set G)) →
      PerDich L (T ⊓ L) ⁅VZ T (L ⊔ T), L⁆ d := by
    intro hT
    rcases torusDich (L_le_normalizer_U T L) s.sylow_TL hT hdL hdN with h | h
    · exact Or.inl h
    · refine Or.inr fun u hu hfix hdu => h u hu hfix ?_
      rw [hdu, mul_inv_cancel]
      exact Subgroup.one_mem _
  rcases hcases with ⟨-, h⟩ | ⟨-, h⟩ | ⟨hk, -⟩ | ⟨-, -, hsum⟩
  · exact hnat (torusHyp_SL3 hTS s.sq_eq_one_U s.two_le h)
  · exact hnat (torusHyp_Sp4 hTP s.sq_eq_one_U s.two_le h)
  · exfalso
    rcases s.kind h1134 with h1 | h1
    · exact SecA.kind_not_SL3_G2 hKF.2.2.2 s.two_le h1 hk
    · exact SecA.kind_not_Sp4_G2 hKF.2.2.2 s.two_le h1 hk
  obtain ⟨W₁, W₂, h1U, h2U, hL1, hL2, h12, h12U, ⟨_, hn1⟩, ⟨_, hn2⟩, hiso⟩ := hsum
  have hT1 : TorusHyp L W₁ ⊥ := torusHyp_SL3 hTS (fun u hu => s.sq_eq_one_U u (h1U hu))
    s.two_le (by rw [Subgroup.bot_subgroupOf]; exact hn1)
  have hT2 : TorusHyp L W₂ ⊥ := torusHyp_SL3 hTS (fun u hu => s.sq_eq_one_U u (h2U hu))
    s.two_le (by rw [Subgroup.bot_subgroupOf]; exact hn2)
  have hPL : T ⊓ L ≤ L := inf_le_right
  have hD : ∀ W' : Subgroup G, L ≤ Subgroup.normalizer (W' : Set G) → TorusHyp L W' ⊥ →
      (∀ u ∈ W', (∀ p ∈ T ⊓ L, p * u * p⁻¹ = u) → d * u * d⁻¹ = u) ∨
      (∀ u ∈ W', (∀ p ∈ T ⊓ L, p * u * p⁻¹ = u) → d * u * d⁻¹ = u → u = 1) := by
    intro W' hLW hT
    rcases torusDich hLW s.sylow_TL hT hdL hdN with h | h
    · refine Or.inl fun u hu hfix => ?_
      have := h u hu hfix
      rwa [Subgroup.mem_bot, mul_inv_eq_one] at this
    · refine Or.inr fun u hu hfix hdu => ?_
      have := h u hu hfix (by rw [hdu, mul_inv_cancel]; exact Subgroup.one_mem _)
      rwa [Subgroup.mem_bot] at this
  have hW21 : W₂ ≤ Subgroup.normalizer (W₁ : Set G) := le_normalizer_of_commute
    fun a ha b hb => s.comm_W a (commutator_le_W T L (h1U ha)) b (commutator_le_W T L (h2U hb))
  have hdec : ∀ u ∈ ⁅VZ T (L ⊔ T), L⁆, ∃ a ∈ W₁, ∃ b ∈ W₂, u = a * b := fun u hu =>
    mem_sup_of_le_normalizer hW21 (h12U ▸ hu)
  have hfix2 : ∀ x ∈ L, ∀ a ∈ W₁, ∀ b ∈ W₂, x * (a * b) * x⁻¹ = a * b →
      x * a * x⁻¹ = a ∧ x * b * x⁻¹ = b :=
    fun x hx a ha b hb h => fix_of_mul_fix h12 (hL1 hx) (hL2 hx) ha hb h
  by_cases hA1 : ∀ u ∈ W₁, (∀ p ∈ T ⊓ L, p * u * p⁻¹ = u) → d * u * d⁻¹ = u
  · have hA2 := transfer_fix hPL hiso hL1 hL2 hdL hA1
    refine Or.inl fun u hu hfix => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec u hu
    have e : d * (a * b) * d⁻¹ = a * b := by
      calc d * (a * b) * d⁻¹ = (d * a * d⁻¹) * (d * b * d⁻¹) := by group
        _ = a * b := by
          rw [hA1 a ha fun p hp => (hfix2 p hp.2 a ha b hb (hfix p hp)).1,
            hA2 b hb fun p hp => (hfix2 p hp.2 a ha b hb (hfix p hp)).2]
    rw [e, mul_inv_cancel]
    exact Subgroup.one_mem _
  · have hB1 := (hD W₁ hL1 hT1).resolve_left hA1
    have hB2 := (hD W₂ hL2 hT2).resolve_left fun hA2 =>
      hA1 (transfer_fix hPL (isXSectionIso₂_symm hiso) hL2 hL1 hdL hA2)
    refine Or.inr fun u hu hfix hdu => ?_
    obtain ⟨a, ha, b, hb, rfl⟩ := hdec u hu
    rw [hB1 a ha (fun p hp => (hfix2 p hp.2 a ha b hb (hfix p hp)).1)
        (hfix2 d hdL a ha b hb hdu).1,
      hB2 b hb (fun p hp => (hfix2 p hp.2 a ha b hb (hfix p hp)).2)
        (hfix2 d hdL a ha b hb hdu).2, one_mul]
    exact Subgroup.one_mem _

end Set37

end CFSG.Quasithin.Vol2.Ch11.SecC
