module

public import CFSG.Quasithin.EmptyFaithful.S146D1
public import CFSG.Quasithin.EmptyFaithful.S146C3
public import CFSG.Quasithin.EmptyFaithful.A10ConfigurationTwelveOut
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Aut
public import CFSG.Quasithin.EmptyFaithful.S146T11

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section OutFacts

@[expose] def OddInner (X : Type*) [Group X] : Prop :=
  ∀ α : MulAut X, Odd (orderOf α) → ∃ k : X, α = MulAut.conj k

theorem OddInner.of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (h : OddInner X) :
    OddInner Y := by
  intro α hα
  have h1 : orderOf ((MulAut.congr e).symm α) = orderOf α :=
    MulEquiv.orderOf_eq (MulAut.congr e).symm α
  obtain ⟨k, hk⟩ := h ((MulAut.congr e).symm α) (h1 ▸ hα)
  refine ⟨e k, ?_⟩
  have h2 : MulAut.congr e ((MulAut.congr e).symm α) = α := (MulAut.congr e).apply_symm_apply α
  rw [← h2, hk, CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]

theorem oddInner_gl32 : OddInner (GL (Fin 3) (ZMod 2)) := by
  intro α hα
  rcases CFSG.QuasithinUnique.Setup.Family.aut_GL32_cases α with ⟨s, hs⟩ | ⟨s, hs⟩
  · exact ⟨s, hs⟩
  · exfalso
    set τ : MulAut (GL (Fin 3) (ZMod 2)) :=
      CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 (ZMod 2) with hτ
    have hττ : τ * τ = 1 := by
      rw [← sq]
      exact CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut_sq 3 (ZMod 2)
    have hτc : ∀ g : GL (Fin 3) (ZMod 2), τ * MulAut.conj g = MulAut.conj (τ g) * τ := fun g =>
      MulEquiv.ext fun x => by
        simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv]
    have hsq : α * α = MulAut.conj (s * τ s) := by
      rw [hs]
      calc MulAut.conj s * τ * (MulAut.conj s * τ)
          = MulAut.conj s * (τ * MulAut.conj s) * τ := by simp only [mul_assoc]
        _ = MulAut.conj s * (MulAut.conj (τ s) * τ) * τ := by rw [hτc]
        _ = MulAut.conj s * MulAut.conj (τ s) * (τ * τ) := by simp only [mul_assoc]
        _ = MulAut.conj (s * τ s) := by rw [hττ, mul_one, map_mul]
    obtain ⟨m, hm⟩ := hα
    have hpow : α ^ (2 * m + 1) = 1 := hm ▸ pow_orderOf_eq_one α
    have h2 : α ^ (2 * m + 1) = MulAut.conj ((s * τ s) ^ m * s) * τ := by
      have : α ^ (2 * m + 1) = (α * α) ^ m * α := by rw [pow_succ, pow_mul, sq]
      rw [this, hsq, ← map_pow, hs, ← mul_assoc, ← map_mul]
    rw [h2] at hpow
    have h3 : τ = (MulAut.conj ((s * τ s) ^ m * s))⁻¹ := eq_inv_of_mul_eq_one_right hpow
    rw [← map_inv] at h3
    exact CFSG.QuasithinUnique.Setup.Family.glGraphAut_ne_conj _ h3

theorem oddInner_sl32 : OddInner (Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  (oddInner_gl32).of_mulEquiv (CFSG.QuasithinUnique.Setup.Family.slEquivGL 3).symm

theorem oddInner_alt6 : OddInner (alternatingGroup (Fin 6)) := by
  intro α hα
  have hle := CFSG.ComponentClassification.CatalogueSchreierAlternating.DegreeSix.outer_card_le_four
  have h2 := CFSG.Quasithin.A10.two_dvd_card_outer_alternating_six
  let b : CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 6)) :=
    QuotientGroup.mk α
  have hb1 : orderOf b ∣ orderOf α :=
    orderOf_map_dvd (QuotientGroup.mk'
      (CFSG.ComponentClassification.OuterAutomorphisms.inner (alternatingGroup (Fin 6)))) α
  have hb2 : orderOf b ∣ Nat.card
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer (alternatingGroup (Fin 6))) :=
    orderOf_dvd_natCard b
  have hpos := Nat.card_pos (α := CFSG.ComponentClassification.OuterAutomorphisms.Outer
    (alternatingGroup (Fin 6)))
  have hodd : Odd (orderOf b) := Odd.of_dvd_nat hα hb1
  have h1 : orderOf b = 1 := by
    obtain ⟨c, hc⟩ := hodd
    obtain ⟨d, hd⟩ := h2
    have : orderOf b ∣ 4 := by
      have : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (alternatingGroup (Fin 6))) = 2 ∨ Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
          (alternatingGroup (Fin 6))) = 4 := by omega
      rcases this with h | h
      · rw [h] at hb2; exact hb2.trans (by norm_num)
      · rw [h] at hb2; exact hb2
    have h4 := Nat.le_of_dvd (by norm_num) this
    interval_cases hb : orderOf b <;> first | rfl | omega
  have hb : b = 1 := orderOf_eq_one_iff.mp h1
  obtain ⟨k, hk⟩ := (QuotientGroup.eq_one_iff α).mp hb
  exact ⟨k, hk.symm⟩

end OutFacts

section Layer

variable {Y : Type*} [Group Y] [Finite Y]

theorem eq_one_of_commute_components (hrad : CFSG.solvableRadical Y = ⊥) {y : Y}
    (hy : ∀ K ∈ cComp (⊤ : Subgroup Y), ∀ r ∈ K, y * r = r * y) : y = 1 := by
  have hcomp := cComp_top_eq_components hrad
  have hfit : CFSG.fittingSubgroup Y = ⊥ := by
    have hsolv : Group.IsSolvable ↥(CFSG.fittingSubgroup Y) := inferInstance
    have h := A3.le_solvableRadical (inferInstance : (CFSG.fittingSubgroup Y).Normal) hsolv
    rw [hrad] at h
    exact le_bot_iff.mp h
  have hlayer : (CFSG.layer Y).Normal := by
    rw [CFSG.layer_eq_componentClassification]
    exact CFSG.ComponentClassification.Layer.normal Y
  have hF : CFSG.generalizedFitting Y = CFSG.layer Y := by
    rw [CFSG.generalizedFitting, hfit, bot_sup_eq]
  have hCle : Subgroup.centralizer (CFSG.layer Y : Set Y) ≤ CFSG.layer Y := by
    have h := CFSG.centralizer_generalizedFitting_le Y
    rwa [hF] at h
  have hCn : (Subgroup.centralizer (CFSG.layer Y : Set Y)).Normal := inferInstance
  have hCs : Group.IsSolvable ↥(Subgroup.centralizer (CFSG.layer Y : Set Y)) := by
    refine Group.isSolvable_of_comm fun a b => ?_
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp b.2 a (hCle a.2)
  have hCbot := A3.le_solvableRadical hCn hCs
  rw [hrad] at hCbot
  have hyC : y ∈ Subgroup.centralizer (CFSG.layer Y : Set Y) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    have hle : CFSG.layer Y ≤ Subgroup.centralizer ({y} : Set Y) := by
      refine sSup_le fun K hK => ?_
      have hK' : K ∈ cComp (⊤ : Subgroup Y) := by rw [hcomp]; exact hK
      intro r hr
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (hy K hK' r hr).symm
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hh)
  exact Subgroup.mem_bot.mp (hCbot hyC)

end Layer

section Odd

variable {G : Type} [Group G] [Finite G]

theorem eq_mul_of_conj_eq_pair {Y : Type*} [Group Y] {R₁ R₂ : Subgroup Y}
    (hc : ∀ a ∈ R₁, ∀ b ∈ R₂, a * b = b * a)
    (hcen : ∀ w : Y, (∀ a ∈ R₁, w * a = a * w) → (∀ b ∈ R₂, w * b = b * w) → w = 1)
    {y r₁ r₂ : Y} (hr₁ : r₁ ∈ R₁) (hr₂ : r₂ ∈ R₂)
    (h₁ : ∀ a ∈ R₁, y * a * y⁻¹ = r₁ * a * r₁⁻¹) (h₂ : ∀ b ∈ R₂, y * b * y⁻¹ = r₂ * b * r₂⁻¹) :
    y = r₁ * r₂ := by
  have c1 : r₁ * r₂ = r₂ * r₁ := hc r₁ hr₁ r₂ hr₂
  have hw : (r₁ * r₂)⁻¹ * y = 1 := by
    apply hcen
    · intro a ha
      have hwa : ((r₁ * r₂)⁻¹ * y) * a * ((r₁ * r₂)⁻¹ * y)⁻¹ = a := by
        have e : ((r₁ * r₂)⁻¹ * y) * a * ((r₁ * r₂)⁻¹ * y)⁻¹ =
            (r₁ * r₂)⁻¹ * (y * a * y⁻¹) * (r₁ * r₂) := by group
        rw [e, h₁ a ha]
        have c2 : a * r₂ = r₂ * a := hc a ha r₂ hr₂
        calc (r₁ * r₂)⁻¹ * (r₁ * a * r₁⁻¹) * (r₁ * r₂) = r₂⁻¹ * (a * r₂) := by group
          _ = r₂⁻¹ * (r₂ * a) := by rw [c2]
          _ = a := by group
      exact mul_inv_eq_iff_eq_mul.mp hwa
    · intro b hb
      have hwb : ((r₁ * r₂)⁻¹ * y) * b * ((r₁ * r₂)⁻¹ * y)⁻¹ = b := by
        have e : ((r₁ * r₂)⁻¹ * y) * b * ((r₁ * r₂)⁻¹ * y)⁻¹ =
            (r₁ * r₂)⁻¹ * (y * b * y⁻¹) * (r₁ * r₂) := by group
        rw [e, h₂ b hb]
        have c2 : r₁ * b = b * r₁ := hc r₁ hr₁ b hb
        calc (r₁ * r₂)⁻¹ * (r₂ * b * r₂⁻¹) * (r₁ * r₂)
            = (r₂ * r₁)⁻¹ * (r₂ * b * r₂⁻¹) * (r₂ * r₁) := by rw [c1]
          _ = r₁⁻¹ * (b * r₁) := by group
          _ = r₁⁻¹ * (r₁ * b) := by rw [← c2]
          _ = b := by group
      exact mul_inv_eq_iff_eq_mul.mp hwb
  exact (inv_mul_eq_one.mp hw).symm

theorem eq_of_conj_eq_single {Y : Type*} [Group Y] {R : Subgroup Y}
    (hcen : ∀ w : Y, (∀ a ∈ R, w * a = a * w) → w = 1) {y r : Y}
    (h₁ : ∀ a ∈ R, y * a * y⁻¹ = r * a * r⁻¹) : y = r := by
  have hw : r⁻¹ * y = 1 := by
    apply hcen
    intro a ha
    have hwa : (r⁻¹ * y) * a * (r⁻¹ * y)⁻¹ = a := by
      have e : (r⁻¹ * y) * a * (r⁻¹ * y)⁻¹ = r⁻¹ * (y * a * y⁻¹) * r := by group
      rw [e, h₁ a ha]
      group
    exact mul_inv_eq_iff_eq_mul.mp hwa
  exact (inv_mul_eq_one.mp hw).symm

theorem solvableRadical_modO2_eq_bot {H : Subgroup G} (h : OddCoreModTwoTrivial H) :
    CFSG.solvableRadical (↥H ⧸ CFSG.pCore 2 ↥H) = ⊥ :=
  solvableRadical_oTwoQuot_eq_bot h

theorem eq_one_of_commute_modO2Image {H : Subgroup G} (h : OddCoreModTwoTrivial H)
    {y : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hy : ∀ L ∈ cComp H, ∀ r ∈ modO2Image H L, y * r = r * y) : y = 1 := by
  refine eq_one_of_commute_components (solvableRadical_modO2_eq_bot h) fun K hK r hr => ?_
  obtain ⟨L, hL, rfl⟩ := exists_cComp_modO2Image_eq hK
  exact hy L hL r hr

omit [Finite G] in
theorem mk_mem_normalizer_modO2Image {H K : Subgroup G} {x : G} (hxH : x ∈ H)
    (hx : x ∈ Subgroup.normalizer (K : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ ∈
      Subgroup.normalizer (modO2Image H K : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
  have h1 : (⟨x, hxH⟩ : ↥H) ∈ Subgroup.normalizer ((K.subgroupOf H : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    have := Subgroup.mem_normalizer_iff.mp hx (z : G)
    simpa using this
  exact Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) ⟨_, h1, rfl⟩

theorem exists_inner_of_odd {H L : Subgroup G} (hL : L ∈ cComp H)
    (hLt : KbarIsL3Two L ∨ KbarIsA6 L) {x : G} (hxH : x ∈ H)
    (hxL : x ∈ Subgroup.normalizer (L : Set G)) (hxo : Odd (orderOf x)) :
    ∃ r ∈ modO2Image H L, ∀ a ∈ modO2Image H L,
      QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ * a *
        (QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩)⁻¹ = r * a * r⁻¹ := by
  set R := modO2Image H L with hR
  have hOI : OddInner ↥R := by
    obtain ⟨e⟩ := nonempty_kbar_mulEquiv_modO2Image hL
    have hK : OddInner (KBar L) := by
      rcases hLt with h | h
      · obtain ⟨φ⟩ := h.nonempty
        exact oddInner_sl32.of_mulEquiv φ.symm
      · obtain ⟨φ⟩ := h.nonempty
        exact oddInner_alt6.of_mulEquiv φ.symm
    exact hK.of_mulEquiv e
  set xs := QuotientGroup.mk' (CFSG.pCore 2 ↥H) ⟨x, hxH⟩ with hxs
  have hn : xs ∈ Subgroup.normalizer (R : Set (↥H ⧸ CFSG.pCore 2 ↥H)) :=
    mk_mem_normalizer_modO2Image hxH hxL
  have hodd : Odd (orderOf (R.normalizerMonoidHom ⟨xs, hn⟩)) := by
    have h1 : orderOf (R.normalizerMonoidHom ⟨xs, hn⟩) ∣ orderOf (⟨xs, hn⟩ :
        ↥(Subgroup.normalizer (R : Set (↥H ⧸ CFSG.pCore 2 ↥H)))) := orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h1
    have h2 : orderOf xs ∣ orderOf (⟨x, hxH⟩ : ↥H) := orderOf_map_dvd _ _
    rw [Subgroup.orderOf_mk] at h2
    exact Odd.of_dvd_nat (Odd.of_dvd_nat hxo h2) h1
  obtain ⟨k, hk⟩ := hOI _ hodd
  refine ⟨(k : ↥H ⧸ CFSG.pCore 2 ↥H), k.2, fun a ha => ?_⟩
  have h1 := congrArg (fun α : MulAut ↥R => ((α ⟨a, ha⟩ : ↥R) : ↥H ⧸ CFSG.pCore 2 ↥H)) hk
  simp only [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply, Subgroup.coe_mul,
    Subgroup.coe_inv] at h1
  exact h1

theorem odd_mem_normalizer_of_mem_cComp (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) (h38 : A38ForSQTK) {H L : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hL : L ∈ cComp H) {x : G} (hxH : x ∈ H) (hxo : Odd (orderOf x)) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  rcases lemma_1_2_1_three hK hs hnab h37 h38 hH hL with hn | ⟨hcard, -⟩
  · exact ((Subgroup.normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hL)).mp hn) hxH
  · by_contra hxn
    have hM : conjSub x L ∈ cComp H := map_conj_mem_cComp hL hxH
    have hML : conjSub x L ≠ L := fun h => hxn (A38.map_conj_eq_iff.mp h)
    have hmemS : ∀ y ∈ H, conjSub y L ∈ conjSubgroupsBy H L := fun y hy => ⟨y, hy, rfl⟩
    have hLS : L ∈ conjSubgroupsBy H L := ⟨1, H.one_mem, (conjSub_one L).symm⟩
    have hNL : conjSub x (conjSub x L) = L := by
      by_contra hNL
      have hNM : conjSub x (conjSub x L) ≠ conjSub x L := fun h => hML ((conjSub_inj x).mp h)
      have h3 : ({L, conjSub x L, conjSub x (conjSub x L)} : Set (Subgroup G)).ncard = 3 :=
        Set.ncard_eq_three.mpr ⟨L, conjSub x L, conjSub x (conjSub x L), hML.symm,
          fun h => hNL h.symm, hNM.symm, rfl⟩
      have hsub : ({L, conjSub x L, conjSub x (conjSub x L)} : Set (Subgroup G)) ⊆
          conjSubgroupsBy H L := by
        intro K hK'
        rcases hK' with rfl | rfl | rfl
        · exact hLS
        · exact hmemS x hxH
        · rw [← conjSub_mul]
          exact hmemS (x * x) (H.mul_mem hxH hxH)
      have hfin : (conjSubgroupsBy H L).Finite := Set.finite_of_ncard_ne_zero (by omega)
      have := Set.ncard_le_ncard hsub hfin
      omega
    have hxx : x * x ∈ Subgroup.normalizer (L : Set G) := by
      apply A38.map_conj_eq_iff.mp
      have : conjSub (x * x) L = L := by rw [conjSub_mul]; exact hNL
      exact this
    obtain ⟨c, hc⟩ := hxo
    have hxpow : x = (x * x) ^ (c + 1) := by
      have h1 : x ^ (orderOf x + 1) = x := by rw [pow_succ, pow_orderOf_eq_one, one_mul]
      calc x = x ^ (orderOf x + 1) := h1.symm
        _ = x ^ (2 * (c + 1)) := by congr 1; omega
        _ = (x * x) ^ (c + 1) := by rw [pow_mul, sq]
    have := Subgroup.pow_mem _ hxx (c + 1)
    rw [← hxpow] at this
    exact hxn this

theorem cComp_subset_pair (hK : quasithinIsQTKECat G) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (h37 : A37ForSQTK) {H K K' : Subgroup G}
    (hH : pCoreOf 2 H ≠ ⊥) (hK₁ : K ∈ cComp H) (hK₂ : K' ∈ cComp H)
    (hper : perfectCore H = K ⊔ K') : ∀ L ∈ cComp H, L = K ∨ L = K' := by
  intro L hL
  by_contra hcon
  push Not at hcon
  obtain ⟨hLK, hLK'⟩ := hcon
  have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hcomm : ∀ L₁ L₂ : Subgroup G, L₁ ∈ cComp H → L₂ ∈ cComp H → L₁ ≠ L₂ →
      L₁ ≤ centralizerMod (pCoreOf 2 H) H L₂ := by
    intro L₁ L₂ h₁ h₂ hne x hx
    refine ⟨le_of_mem_cComp h₁ hx, hQN (le_of_mem_cComp h₁ hx), fun u hu => ?_⟩
    have h2 := lemma_1_2_1_two hK hs hnab h37 hH h₁ h₂ hne
    exact h2.1.trans h2.2 (by
      have := Subgroup.commutator_mem_commutator hx hu
      simpa [commutatorElement_def] using this)
  have hLC : L ≤ centralizerMod (pCoreOf 2 H) H L := by
    have hLper : L ≤ perfectCore H :=
      le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)
    have hsup : perfectCore H ≤ centralizerMod (pCoreOf 2 H) H L := by
      rw [hper]
      exact sup_le (hcomm K L hK₁ hL (Ne.symm hLK)) (hcomm K' L hK₂ hL (Ne.symm hLK'))
    exact hLper.trans hsup
  have hLQ : L ≤ pCoreOf 2 H := by
    have hcomm' : ⁅L, L⁆ ≤ pCoreOf 2 H := by
      rw [Subgroup.commutator_le]
      intro a ha b hb
      have := (hLC ha).2.2 b hb
      simpa [commutatorElement_def] using this
    rwa [perfect_of_mem_cComp hL] at hcomm'
  have : Group.IsSolvable ↥(pCoreOf 2 H) := isSolvable_pCoreOf_two H
  exact not_isSolvable_of_mem_cComp hL
    (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hLQ)
      (Subgroup.inclusion_injective hLQ))

omit [Finite G] in
theorem eq_of_le_cComp {H K L : Subgroup G} (hK : K ∈ cComp H) (hL : L ∈ cComp H) (hLK : L ≤ K) :
    L = K := by
  by_contra hne
  exact not_subnormal_of_mem_cComp hK (lt_of_le_of_ne hLK hne) (ne_bot_of_mem_cComp hL)
    (perfect_of_mem_cComp hL) (subnormal_of_mem_cComp hL)

omit [Finite G] in
theorem mem_perfectCore_of_odd_of_inv_mul_mem [Finite G] {H : Subgroup G} {x a : G} (hxH : x ∈ H)
    (haH : a ∈ perfectCore H) (hq : x⁻¹ * a ∈ pCoreOf 2 H) (hxo : Odd (orderOf x)) :
    x ∈ perfectCore H := by
  have haH' : a ∈ H := perfectCore_le H haH
  obtain ⟨j, hj⟩ : ∃ j : ℕ, (x⁻¹ * a) ^ 2 ^ j = 1 :=
    exists_pow_two_pow_eq_one_of_mem (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hq
  have hN := perfectCore_normal H
  let f : ↥H →* ↥H ⧸ (perfectCore H).subgroupOf H := QuotientGroup.mk' _
  have hfa : f ⟨a, haH'⟩ = 1 := (QuotientGroup.eq_one_iff _).mpr (by
    rw [Subgroup.mem_subgroupOf]; exact haH)
  have hx : (⟨x, hxH⟩ : ↥H) = ⟨a, haH'⟩ * ⟨x⁻¹ * a, H.mul_mem (H.inv_mem hxH) haH'⟩⁻¹ := by
    apply Subtype.ext; simp
  have hpow : (⟨x, hxH⟩ : ↥H) ^ 2 ^ j ∈ (perfectCore H).subgroupOf H := by
    have h1 : f ((⟨x, hxH⟩ : ↥H) ^ 2 ^ j) = 1 := by
      rw [map_pow, hx, map_mul, hfa, one_mul, map_inv, inv_pow, ← map_pow]
      have : (⟨x⁻¹ * a, H.mul_mem (H.inv_mem hxH) haH'⟩ : ↥H) ^ 2 ^ j = 1 :=
        Subtype.ext (by simpa using hj)
      rw [this, map_one, inv_one]
    exact (QuotientGroup.eq_one_iff _).mp h1
  have hpow' : x ^ 2 ^ j ∈ perfectCore H := by
    have := (Subgroup.mem_subgroupOf).mp hpow
    simpa using this
  have hcop : Nat.Coprime (2 ^ j) (orderOf x) :=
    Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hxo)
  exact (Subgroup.zpowers_le.mpr hpow') (A4.mem_zpowers_pow_of_coprime hcop)

omit [Finite G] in
theorem exists_mem_perfectCore_of_mem_sup {H K K' : Subgroup G} (hK : K ≤ perfectCore H)
    (hK' : K' ≤ perfectCore H) {y : ↥H ⧸ CFSG.pCore 2 ↥H}
    (hy : y ∈ modO2Image H K ⊔ modO2Image H K') :
    ∃ a : ↥H, (a : G) ∈ perfectCore H ∧ QuotientGroup.mk' (CFSG.pCore 2 ↥H) a = y := by
  have hle : modO2Image H K ⊔ modO2Image H K' ≤ modO2Image H (perfectCore H) := by
    refine sup_le ?_ ?_ <;>
    · intro z hz
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hz
      exact Subgroup.mem_map.mpr ⟨a, by
        rw [Subgroup.mem_subgroupOf] at ha ⊢
        first | exact hK ha | exact hK' ha, rfl⟩
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp (hle hy)
  exact ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩

theorem mem_perfectCore_of_odd (h37 : A37ForSQTK) (h38 : A38ForSQTK) {T M : Subgroup G}
    (S : Setting146 G T M) (hB : HypB146 T M) (c19 : Conc14619 T M) (c20 : Conc14620 T M)
    (c21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K) {x : G} (hxH : x ∈ mcOf T)
    (hxo : Odd (orderOf x)) : x ∈ perfectCore (mcOf T) := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hpc : pCoreOf 2 (mcOf T) ≠ ⊥ := hHTM.1.2
  have hqtke := S.hyp.qtke
  have hsimp := S.hyp.simple
  have hnab := S.hyp.nonabelian
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hodd : OddCoreModTwoTrivial (mcOf T) := (c19 _ hHTM).1
  have hnsolv : ¬ Group.IsSolvable ↥(mcOf T) := fun hs => hHTM.2 (S.theorem_14_6_18 hB hHTM.1 hs)
  obtain ⟨K, hK, -⟩ := exists_cComp_le_of_not_solvable (H := mcOf T) (X := mcOf T) le_rfl
    (by rw [Subgroup.subgroupOf_self]; exact Subgroup.normal_top) hnsolv
  have hLt : ∀ L ∈ cComp (mcOf T), KbarIsL3Two L ∨ KbarIsA6 L := fun L hL => (c20 _ hHTM L hL).1
  have hle : ∀ L ∈ cComp (mcOf T), L ≤ perfectCore (mcOf T) := fun L hL =>
    le_perfectCore_of_perfect (le_of_mem_cComp hL) (perfect_of_mem_cComp hL)
  have hcomm : ∀ L₁ ∈ cComp (mcOf T), ∀ L₂ ∈ cComp (mcOf T), L₁ ≠ L₂ →
      ⁅L₁, L₂⁆ ≤ pCoreOf 2 (mcOf T) := fun L₁ h₁ L₂ h₂ hne =>
    (lemma_1_2_1_two hqtke hsimp hnab h37 hpc h₁ h₂ hne).1.trans
      (lemma_1_2_1_two hqtke hsimp hnab h37 hpc h₁ h₂ hne).2
  have hnorm : ∀ L ∈ cComp (mcOf T), x ∈ Subgroup.normalizer (L : Set G) := fun L hL =>
    odd_mem_normalizer_of_mem_cComp hqtke hsimp hnab h37 h38 hpc hL hxH hxo
  obtain ⟨K', hK', hall⟩ : ∃ K' ∈ cComp (mcOf T), ∀ L ∈ cComp (mcOf T), L = K ∨ L = K' := by
    rcases c21 K hK with ⟨hper, -⟩ | ⟨⟨t, ht, htn, hper⟩, -⟩ | ⟨Kp, hKp, -, -, -, hper, -, -⟩
    · exact ⟨K, hK, fun L hL => Or.inl (eq_of_le_cComp hK hL (hper ▸ hle L hL))⟩
    · exact ⟨conjSub t K, map_conj_mem_cComp hK (hTH ht),
        cComp_subset_pair hqtke hsimp hnab h37 hpc hK (map_conj_mem_cComp hK (hTH ht)) hper⟩
    · exact ⟨Kp, hKp, cComp_subset_pair hqtke hsimp hnab h37 hpc hK hKp hper⟩
  set xs := QuotientGroup.mk' (CFSG.pCore 2 ↥(mcOf T)) ⟨x, hxH⟩ with hxs
  have hcen : ∀ w : ↥(mcOf T) ⧸ CFSG.pCore 2 ↥(mcOf T),
      (∀ L ∈ cComp (mcOf T), ∀ r ∈ modO2Image (mcOf T) L, w * r = r * w) → w = 1 :=
    fun w hw => eq_one_of_commute_modO2Image hodd hw
  have hmem : xs ∈ modO2Image (mcOf T) K ⊔ modO2Image (mcOf T) K' := by
    by_cases hKK' : K = K'
    · subst hKK'
      obtain ⟨r, hr, hxr⟩ := exists_inner_of_odd hK (hLt K hK) hxH (hnorm K hK) hxo
      have h1 : xs = r := eq_of_conj_eq_single (R := modO2Image (mcOf T) K) (fun w hw =>
        hcen w fun L hL r' hr' => by
          rcases hall L hL with rfl | rfl <;> exact hw r' hr') hxr
      exact Subgroup.mem_sup_left (h1 ▸ hr)
    · obtain ⟨r₁, hr₁, hxr₁⟩ := exists_inner_of_odd hK (hLt K hK) hxH (hnorm K hK) hxo
      obtain ⟨r₂, hr₂, hxr₂⟩ := exists_inner_of_odd hK' (hLt K' hK') hxH (hnorm K' hK') hxo
      have h1 : xs = r₁ * r₂ := eq_mul_of_conj_eq_pair (R₁ := modO2Image (mcOf T) K)
        (R₂ := modO2Image (mcOf T) K') (modO2Image_commute (hcomm K hK K' hK' hKK'))
        (fun w hw₁ hw₂ => hcen w fun L hL r' hr' => by
          rcases hall L hL with rfl | rfl
          · exact hw₁ r' hr'
          · exact hw₂ r' hr') hr₁ hr₂ hxr₁ hxr₂
      rw [h1]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hr₁) (Subgroup.mem_sup_right hr₂)
  obtain ⟨a, haP, hax⟩ := exists_mem_perfectCore_of_mem_sup (hle K hK) (hle K' hK') hmem
  refine mem_perfectCore_of_odd_of_inv_mul_mem hxH haP ?_ hxo
  have h1 : (⟨x, hxH⟩ : ↥(mcOf T))⁻¹ * a ∈ CFSG.pCore 2 ↥(mcOf T) :=
    QuotientGroup.eq.mp hax.symm
  exact ⟨_, h1, rfl⟩

theorem conc14623_one_of_a3 (h37 : A37ForSQTK) (h38 : A38ForSQTK) {T M : Subgroup G}
    (S : Setting146 G T M) (hB : HypB146 T M) (c19 : Conc14619 T M) (c20 : Conc14620 T M)
    (c21 : ∀ K ∈ cComp (mcOf T), Conc14621 T K) :
    perfectCore (mcOf T) = oTwoUpper (mcOf T) ∧ mcOf T = perfectCore (mcOf T) ⊔ T := by
  have hHTM : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hTH : T ≤ mcOf T := hHTM.1.1
  have hTsyl : IsSylowTwoOf T (mcOf T) := isSylowTwoOf_of_quasithinIsSylowTwo S.hyp.sylow hTH
  have hsup : mcOf T = oTwoUpper (mcOf T) ⊔ T := by
    rw [sup_comm, ← F6.twoResidual_eq_oTwoUpper]
    exact (sup_twoResidual_eq hTsyl).symm
  have hge : oTwoUpper (mcOf T) ≤ perfectCore (mcOf T) := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact mem_perfectCore_of_odd h37 h38 S hB c19 c20 c21 hx.1 hx.2
  have hle : perfectCore (mcOf T) ≤ oTwoUpper (mcOf T) := by
    have hT2 : Group.IsSolvable ↥T := by
      have hp : IsPGroup 2 T := S.hyp.sylow.1
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥T := hp.isNilpotent
      infer_instance
    exact perfectCore_le_of_sup_solvable (oTwoUpper_le _)
      ((Subgroup.normal_subgroupOf_iff_le_normalizer (oTwoUpper_le _)).mpr
        (le_normalizer_oTwoUpper _)) hsup hT2
  have heq : perfectCore (mcOf T) = oTwoUpper (mcOf T) := le_antisymm hle hge
  refine ⟨heq, ?_⟩
  rw [heq]
  exact hsup

end Odd

end CFSG.Quasithin
