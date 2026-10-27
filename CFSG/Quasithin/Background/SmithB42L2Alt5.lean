module

public import CFSG.Quasithin.Background.SmithB42L2Nat
public import CFSG.Quasithin.Background.SmithB42Families
public import CFSG.Quasithin.Background.SmithB42L2Sl2

public section

namespace CFSG.Quasithin

namespace B42L2

open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped MatrixGroups

theorem isSwap_of_sq_of_sign {σ : Equiv.Perm (Fin 5)} (h2 : σ ^ 2 = 1)
    (hs : Equiv.Perm.sign σ = -1) : σ.IsSwap := by
  classical
  rw [← Equiv.Perm.card_support_eq_two]
  have hct : ∀ k ∈ σ.cycleType, k = 2 := by
    intro k hk
    have h1 := Equiv.Perm.dvd_of_mem_cycleType hk
    have h3 := Equiv.Perm.two_le_of_mem_cycleType hk
    have h4 : k ≤ 2 := Nat.le_of_dvd two_pos (h1.trans (orderOf_dvd_of_pow_eq_one h2))
    omega
  have hrep : σ.cycleType = Multiset.replicate (Multiset.card σ.cycleType) 2 :=
    Multiset.eq_replicate_card.mpr hct
  have hsum : σ.support.card = Multiset.card σ.cycleType * 2 := by
    rw [← Equiv.Perm.sum_cycleType, hrep, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul]
  have hle : σ.support.card ≤ 5 := (Finset.card_le_univ _).trans (by simp)
  rw [Equiv.Perm.sign_of_cycleType, hrep, Multiset.sum_replicate, Multiset.card_replicate,
    smul_eq_mul] at hs
  set k := Multiset.card σ.cycleType
  have hk : k ≤ 2 := by omega
  interval_cases k
  · exact absurd hs (by decide)
  · omega
  · exact absurd hs (by decide)

theorem closure_diff_eq {M : Type*} [Group M] {K H : Subgroup M} (h : ¬ K ≤ H) :
    Subgroup.closure {x | x ∈ K ∧ x ∉ H} = K := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    exact fun x hx => hx.1
  · obtain ⟨s, hsK, hsH⟩ := Set.not_subset.mp h
    intro k hk
    by_cases hkH : k ∈ H
    · have h1 : k * s ∈ Subgroup.closure {x | x ∈ K ∧ x ∉ H} :=
        Subgroup.subset_closure ⟨K.mul_mem hk hsK, fun h' => hsH (by
          simpa using H.mul_mem (H.inv_mem hkH) h')⟩
      have h2 : s ∈ Subgroup.closure {x | x ∈ K ∧ x ∉ H} := Subgroup.subset_closure ⟨hsK, hsH⟩
      simpa using Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
    · exact Subgroup.subset_closure ⟨hk, hkH⟩

section Real

variable {V : Type} [CommGroup V]

theorem realizesVia_of_secEquiv {D : FFModel} (hD : D.IsActionModel) (hker : D.ker = ⊥)
    {H : Subgroup (MulAut V)} (π : D.Gam →* ↥H) (hπ : Function.Surjective π)
    (β : V ≃* ↥D.sec)
    (hβ : ∀ (γ : D.Gam) (v : V), (β (((π γ : ↥H) : MulAut V) v) : D.Amb) = D.act γ (β v)) :
    D.RealizesVia H ⊤ ⊥ π := by
  refine ⟨hπ, le_top, hD.ker_le, fun _ u _ => trivial,
    fun _ z hz => by simpa using hz, hD.sec_inv, hD.ker_inv, ?_⟩
  refine ⟨(QuotientGroup.mk' (D.ker.subgroupOf D.sec)).comp
    (β.toMonoidHom.comp Subgroup.topEquiv.toMonoidHom), ?_, ?_, ?_⟩
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    exact ⟨⟨β.symm m, trivial⟩, by simp⟩
  · intro u
    show (QuotientGroup.mk (β (u : V)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) = 1 ↔ _
    rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot,
      Subgroup.mem_bot]
    constructor
    · intro h
      have : β (u : V) = 1 := Subtype.ext h
      exact β.injective (by rw [this, map_one])
    · intro h
      rw [h, map_one]
      rfl
  · intro γ u m hu hm hum
    have hu' : (QuotientGroup.mk (β (u : V)) : ↥D.sec ⧸ D.ker.subgroupOf D.sec) =
        QuotientGroup.mk m := hum
    have hbm : β (u : V) = m := by
      have := QuotientGroup.eq.1 hu'
      rw [Subgroup.mem_subgroupOf, hker, Subgroup.mem_bot] at this
      have h2 : ((β (u : V))⁻¹ * m : ↥D.sec) = 1 := Subtype.ext this
      exact inv_mul_eq_one.1 h2
    show (QuotientGroup.mk (β (((π γ : ↥H) : MulAut V) (u : V))) :
      ↥D.sec ⧸ D.ker.subgroupOf D.sec) = QuotientGroup.mk ⟨D.act γ (m : D.Amb), hm⟩
    congr 1
    apply Subtype.ext
    rw [hβ γ (u : V), hbm]

end Real

theorem symDn_five_ker : (FFModel.symDn 5).ker = ⊥ := by
  have h := Explicit.card_dnZ (n := 5) (by norm_num)
  simp only [show ¬ Even 5 from by decide, ↓reduceIte] at h
  exact Subgroup.eq_bot_of_card_eq _ h

section Case5

variable {V : Type} [CommGroup V] [Finite V]

theorem case5_of_deleted (hV : ∀ v : V, v ^ 2 = 1) {G L : Subgroup (MulAut V)}
    (hHyp : B4Hyp G L) (hZ : Subgroup.center ↥L = ⊥)
    (haut : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L)
    (hw : ∀ B, IsFFStarOffender G B → Nat.card B * Nat.card (fixV B) = Nat.card V)
    {Q A : Subgroup (MulAut V)} (hQ : IsFFStarOffender G Q) (hA : IsFFStarOffender G A)
    (hQA : Q ≤ A) (hQL : ¬ Q ≤ L) (σ : ↥(L ⊔ Q) ≃* Equiv.Perm (Fin 5))
    (e : V ≃* ↥(G6.coreMod 5))
    (he : ∀ (y : ↥(L ⊔ Q)) (v : V), e ((y : MulAut V) v) = G6.coreAct 5 (σ y) (e v))
    (hL : ∀ y : ↥(L ⊔ Q), (y : MulAut V) ∈ L ↔ σ y ∈ alternatingGroup (Fin 5)) :
    B42Case5 G A := by
  classical
  obtain ⟨hLG, hLn, hself, -⟩ := FFC.b4hyp_data hHyp
  have hself' : ∀ g ∈ G, (∀ l ∈ L, g * l = l * g) → g = 1 := by
    intro g hg hc
    have hgL := hself g hg hc
    have hcen : (⟨g, hgL⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact Subtype.ext (hc y y.2).symm
    rw [hZ, Subgroup.mem_bot] at hcen
    exact congrArg Subtype.val hcen
  have hne : L ⊔ Q ≠ L := fun h => hQL (h ▸ le_sup_right)
  have hGLQ : G = L ⊔ Q :=
    FFC.eq_of_card_mulAut_le le_sup_left (sup_le hLG hQ.1) hne hLn hself' haut
  have hJ : ffJ G = L ⊔ Q := by
    refine le_antisymm (hGLQ ▸ B6.ffJ_le G) (sup_le (B5.Ln.le_ffJ_of_center hHyp hZ hA) ?_)
    exact B6.le_ffJ hQ
  let κ : ↥(ffJ G) ≃* ↥(L ⊔ Q) := MulEquiv.subgroupCongr hJ
  let π : Equiv.Perm (Fin 5) →* ↥(ffJ G) := (κ.symm.toMonoidHom).comp σ.symm.toMonoidHom
  have hπinj : Function.Injective π := κ.symm.injective.comp σ.symm.injective
  have hπs : Function.Surjective π := κ.symm.surjective.comp σ.symm.surjective
  have hπv : ∀ t, ((π t : ↥(ffJ G)) : MulAut V) = ((σ.symm t : ↥(L ⊔ Q)) : MulAut V) :=
    fun t => rfl
  have hReal : (FFModel.symDn 5).RealizesVia (ffJ G) ⊤ ⊥ π := by
    refine realizesVia_of_secEquiv (FFModel.symDn_isActionModel 5) symDn_five_ker π hπs e ?_
    intro (γ : Equiv.Perm (Fin 5)) v
    show ((e (((π γ : ↥(ffJ G)) : MulAut V) v) : ↥(G6.coreMod 5)) : G6.PermMod 5) =
      G6.permAct 5 γ (e v)
    rw [hπv, he, MulEquiv.apply_symm_apply, G6.coreAct_coe]
  set T : Set (Equiv.Perm (Fin 5)) :=
    {t | ((π t : ↥(ffJ G)) : MulAut V) ∈ A ∧ ((π t : ↥(ffJ G)) : MulAut V) ∉ L} with hT
  have hcommA := hA.2.2.1.1
  have hsqA := hA.2.2.1.2
  have hTsq : ∀ t ∈ T, t ^ 2 = 1 := by
    intro t ht
    apply hπinj
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hsqA _ ht.1
  have hTsign : ∀ t ∈ T, Equiv.Perm.sign t = -1 := by
    intro t ht
    have h1 : σ.symm t ∉ (alternatingGroup (Fin 5)).comap σ.toMonoidHom := by
      intro h
      apply ht.2
      rw [hπv]
      exact (hL _).2 h
    rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulEquiv.apply_symm_apply,
      Equiv.Perm.mem_alternatingGroup] at h1
    rcases Int.units_eq_one_or (Equiv.Perm.sign t) with h | h
    · exact absurd h h1
    · exact h
  refine ⟨⟨5, Or.inl rfl, π, hReal, T, fun t ht => isSwap_of_sq_of_sign (hTsq t ht) (hTsign t ht),
    fun t ht t' ht' _ => ?_, ?_⟩, qOf_eq_one_of_weight hV hA hw⟩
  · apply hπinj
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hcommA _ ht.1 _ ht'.1
  · rw [MonoidHom.map_closure]
    have hAJ : A ≤ ffJ G := B6.le_ffJ hA
    have himg : π '' T = {x | x ∈ A.subgroupOf (ffJ G) ∧ x ∉ L.subgroupOf (ffJ G)} := by
      ext x
      constructor
      · rintro ⟨t, ht, rfl⟩
        exact ⟨ht.1, ht.2⟩
      · rintro ⟨hxA, hxL⟩
        obtain ⟨t, rfl⟩ := hπs x
        exact ⟨t, ⟨hxA, hxL⟩, rfl⟩
    rw [himg, closure_diff_eq]
    intro h
    apply hQL
    intro q hq
    have h1 : (⟨q, hAJ (hQA hq)⟩ : ↥(ffJ G)) ∈ L.subgroupOf (ffJ G) := h (hQA hq)
    exact h1

end Case5

end B42L2

theorem asB42Alt5_holds :
    AsB42Alt5 := by
  intro V _ _ hV G L hHyp hP A hA
  obtain ⟨hZ, ⟨eA⟩, hmodel⟩ := hP
  obtain ⟨F, _, _, hF, ⟨θL⟩⟩ := B42L2.exists_sl2_of_model hZ hmodel
  have hw : ∀ B, IsFFStarOffender G B → Nat.card B * Nat.card (fixV B) = Nat.card V :=
    fun B hB => B42L2.weight_eq_sl2 hV hHyp hZ le_rfl hF θL hB
  obtain ⟨Q, hQA, hQ, hQq, -⟩ := exists_quadratic_offender_le hV hA
  rcases (B42L2.sl2_alt hV hHyp hZ le_rfl hF θL hQ hQq).2 with ⟨-, e, he⟩ |
      ⟨-, hQL, σ, e, he, hL⟩
  · exact Or.inl (B42L2.case1_of_natural hV hHyp hZ (by norm_num) hF θL e he hw hA)
  · let eL : ↥L ≃* ↥(alternatingGroup (Fin 5)) :=
      (QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)).trans eA
    have haut : Nat.card (MulAut ↥L) ≤ 2 * Nat.card ↥L := by
      rw [Nat.card_congr (MulAut.congr eL).toEquiv, Nat.card_congr eL.toEquiv]
      exact FFC.card_mulAut_alternating_le (Or.inl rfl)
    exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (B42L2.case5_of_deleted hV hHyp hZ haut hw hQ hA hQA hQL σ e he hL)))))

end CFSG.Quasithin
