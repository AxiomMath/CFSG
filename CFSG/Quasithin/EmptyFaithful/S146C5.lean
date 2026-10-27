module

public import CFSG.Quasithin.EmptyFaithful.S146C4
public import CFSG.Quasithin.EmptyFaithful.S146C1
public import CFSG.Quasithin.EmptyFaithful.S146C3
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped commutatorElement Pointwise

variable {G : Type} [Group G]

theorem not_kbarIsA6_of_kbarIsL3Two {K : Subgroup G} (h3 : KbarIsL3Two K)
    (h6 : KbarIsA6 K) : False := by
  have h168 := relIndex_pCoreOf_of_kbarIsL3Two h3
  obtain ⟨e⟩ := h6
  have h360 : (pCoreOf 2 K).relIndex K = 360 := by
    have : Nat.card (KBar K) = 360 := by
      rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
      simp [Nat.factorial]
    exact this
  omega

variable [Finite G] {K Z U₁ : Subgroup G}

omit [Finite G] in
theorem Sec8.inf_le_of_not_le (h : Sec8 K Z U₁) {C : Subgroup G}
    (hKC : K ≤ Subgroup.normalizer (C : Set G)) (hZC : Z ≤ C) (hnot : ¬ U₁ ≤ C) : U₁ ⊓ C ≤ Z := by
  have hKW : K ≤ Subgroup.normalizer ((U₁ ⊓ C : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨h.KU hk, hKC hk⟩
  rcases h.irr (U₁ ⊓ C) (le_inf h.le hZC) inf_le_left hKW with hW | hW
  · exact hW.le
  · exact absurd (inf_eq_left.mp hW) hnot

theorem le_sup_of_relIndex_le_eight {U U₁ D Z : Subgroup G}
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x) (hU₁ : U₁ ≤ U) (hD : D ≤ U) (hZU₁ : Z ≤ U₁)
    (hinf : U₁ ⊓ D = Z) (h8 : Z.relIndex U₁ = 8) (hle : D.relIndex U ≤ 8) : U ≤ U₁ ⊔ D := by
  obtain ⟨hc, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute U₁ D
    (fun x hx y hy => hcomm x (hU₁ hx) y (hD hy))
  rw [hinf] at hc
  have e1 := Subgroup.relIndex_mul_card Z U₁
  rw [inf_eq_left.mpr hZU₁, h8] at e1
  have e2 := Subgroup.relIndex_mul_card D (U₁ ⊔ D)
  rw [inf_eq_left.mpr (le_sup_right : D ≤ U₁ ⊔ D)] at e2
  have hZpos : 0 < Nat.card Z := Nat.card_pos
  have hDpos : 0 < Nat.card D := Nat.card_pos
  have hr : D.relIndex (U₁ ⊔ D) = 8 := by
    refine Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hZpos hDpos) ?_
    calc D.relIndex (U₁ ⊔ D) * (Nat.card Z * Nat.card D)
        = (D.relIndex (U₁ ⊔ D) * Nat.card D) * Nat.card Z := by ring
      _ = Nat.card ↥(U₁ ⊔ D) * Nat.card Z := by rw [e2]
      _ = Nat.card U₁ * Nat.card D := hc
      _ = (8 * Nat.card Z) * Nat.card D := by rw [← e1]
      _ = 8 * (Nat.card Z * Nat.card D) := by ring
  have hmul := Subgroup.relIndex_mul_relIndex D (U₁ ⊔ D) U le_sup_right (sup_le hU₁ hD)
  have hpos : 0 < (U₁ ⊔ D).relIndex U := Nat.pos_of_ne_zero (relIndex_ne_zero_fin _ _)
  have h1 : (U₁ ⊔ D).relIndex U = 1 := by
    rw [hr] at hmul
    omega
  exact Subgroup.relIndex_eq_one.mp h1

omit [Finite G] in
theorem normalizer_le_normalizer_centralizer' {Q : Subgroup G} :
    Subgroup.normalizer (Q : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (Q : Set G) : Subgroup G) : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro c
  refine ⟨fun hc => conj_mem_centralizer hg hc, fun hc => ?_⟩
  have h1 := conj_mem_centralizer (Subgroup.inv_mem _ hg) hc
  have e : g⁻¹ * (g * c * g⁻¹) * g⁻¹⁻¹ = c := by group
  rwa [e] at h1

theorem Setting146.four_le_mIdx_of_bdata {T M : Subgroup G} (S : Setting146 G T M) (h5 : Stage1461Five)
    (hB : HypB146 T M) {K U₁ U₂ : Subgroup G} {s u : G} (hd : BData146 T M K U₁ U₂ s u) :
    4 ≤ mIdx (conjClosure (VZ T M) (mcOf T))
      (Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G)) := by
  classical
  have hG : IsHTM T M (mcOf T) := S.isHTM_mcOf
  have hOdd : OddCoreModTwoTrivial (mcOf T) := hB (mcOf T) hG
  obtain ⟨-, hL3, hKeq, -⟩ := hd.c24
  have hKc : K ∈ cComp (mcOf T) := hd.hK
  have hsimple : IsSimpleGroup (KBar K) := (hd.c19 (mcOf T) hG).2 K hKc
  have hKG : K ≤ mcOf T := le_of_mem_cComp hKc
  have hKn : mcOf T ≤ Subgroup.normalizer (K : Set G) := by
    rw [hKeq]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore _)
  have hTG : T ≤ mcOf T := hG.1.1
  have hUab : IsElemAbelian 2 (conjClosure (VZ T M) (mcOf T)) := S.lemma_14_5_15_two hG
  have hUQ : conjClosure (VZ T M) (mcOf T) ≤ pCoreOf 2 (mcOf T) := S.conjClosure_le_pCoreOf hG
  have hQT : pCoreOf 2 (mcOf T) ≤ T := S.pCoreOf_le_T hG
  have hUN : conjClosure (VZ T M) (mcOf T) ≤
      Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := S.conjClosure_le_normalizer_Z hG
  have hZU : quasithinOmegaOneCenter T ≤ conjClosure (VZ T M) (mcOf T) :=
    Z_le_conjClosure_VZ T M (mcOf T)
  have hG₁U : mcOf T ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) :=
    le_normalizer_conjClosure _ _
  have hG₁Z : mcOf T ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := fun x hx =>
    S.normalizer_Z.ge hx
  have hG₁Q : mcOf T ≤ Subgroup.normalizer (pCoreOf 2 (mcOf T) : Set G) :=
    le_normalizer_pCoreOf 2 (mcOf T)
  have hKU : K ≤ Subgroup.normalizer (conjClosure (VZ T M) (mcOf T) : Set G) := hKG.trans hG₁U
  have hsT : s ∈ T := hd.dec.mem.1
  have hsK : s ∈ Subgroup.normalizer (K : Set G) := hd.dec.mem.2
  have hsG : s ∈ mcOf T := hTG hsT
  have hnat : mIdx U₁ (quasithinOmegaOneCenter T) = 3 ∧
      IsIrredOnSection K U₁ (quasithinOmegaOneCenter T) := by
    rcases hd.dec.natural with ⟨-, h3, hirr⟩ | ⟨h6, -⟩
    · exact ⟨h3, hirr⟩
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 h6).elim
  have hout : KbarInducesOuter K s := by
    rcases hd.dec.dynkin with ⟨-, ho⟩ | ⟨h6, -⟩
    · exact ho
    · exact (not_kbarIsA6_of_kbarIsL3Two hL3 h6).elim
  have hsub : IsSubnormal K (mcOf T) := subnormal_of_mem_cComp hKc
  have hsup : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ⊔ quasithinOmegaOneCenter T = U₁ ⊔ U₂ :=
    hd.dec.sup
  have hUU₁ : U₁ ≤ conjClosure (VZ T M) (mcOf T) ∧ U₂ ≤ conjClosure (VZ T M) (mcOf T) := by
    have h1 : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤ conjClosure (VZ T M) (mcOf T) :=
      S145.commutator_le_of_le_normalizer hKU
    have h2 : U₁ ⊔ U₂ ≤ conjClosure (VZ T M) (mcOf T) := by
      rw [← hsup]
      exact sup_le h1 hZU
    exact ⟨le_sup_left.trans h2, le_sup_right.trans h2⟩
  have hU₁2 : IsPGroup 2 U₁ := (pCoreOf_isPGroup 2 (mcOf T)).to_le (hUU₁.1.trans hUQ)
  have hSec : Sec8 K (quasithinOmegaOneCenter T) U₁ :=
    { le := hd.dec.Z₁
      norm := hUU₁.1.trans hUN
      sq := fun a ha => by
        rw [isElemAbelian_pow_eq_one hUab (hUU₁.1 ha)]
        exact Subgroup.one_mem _
      comm := fun a ha b hb => by
        have e : a * b * a⁻¹ * b⁻¹ = 1 := by
          rw [isElemAbelian_comm hUab (hUU₁.1 ha) (hUU₁.1 hb)]
          group
        rw [e]
        exact Subgroup.one_mem _
      card := by rw [HypF98.relIndex_eq_two_pow_mIdx hU₁2, hnat.1]; norm_num
      KZ := hKG.trans hG₁Z
      KU := hnat.2.2.1
      irr := hnat.2.2.2.2 }
  have h91 := (S.lemma_14_5_14 (S.isHz_iff.mpr hG)).2.toHypF91
  have hQK : pCoreOf 2 K ≤ pCoreOf 2 (mcOf T) := A4.pCoreOf_le_of_subnormal 2 hsub
  have hQ' : ∀ p ∈ pCoreOf 2 K, ∀ u ∈ U₁, p * u * p⁻¹ * u⁻¹ ∈ quasithinOmegaOneCenter T := by
    intro p hp u hu
    have h1 := h91.commutator_conjClosure_le u (hUU₁.1 hu) p (hQK hp)
    have e : p * u * p⁻¹ * u⁻¹ = (u * p * u⁻¹ * p⁻¹)⁻¹ := by group
    rw [e]
    exact (quasithinOmegaOneCenter T).inv_mem h1
  have h168 := relIndex_pCoreOf_of_kbarIsL3Two hL3
  have hZC : quasithinOmegaOneCenter T ≤ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) :=
    fun w hw => by
      rw [Subgroup.mem_centralizer_iff]
      intro q hq
      exact (Subgroup.mem_centralizer_iff.mp
        (le_centralizer_quasithinOmegaOneCenter T (hQT hq)) w hw).symm
  have hG₁C := normalizer_le_normalizer_centralizer' (Q := pCoreOf 2 (mcOf T))
  have hKC : K ≤ Subgroup.normalizer
      ((Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) : Subgroup G) : Set G) :=
    fun k hk => hG₁C (hG₁Q (hKG hk))
  have hnot : ¬ U₁ ≤ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
    intro hU₁C
    have hU₂C : U₂ ≤ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
      intro x hx
      have hx' : s⁻¹ * x * s ∈ U₁ := mem_conjSub.mp (hd.dec.conj ▸ hx)
      have h1 := conj_mem_centralizer (hG₁Q hsG) (hU₁C hx')
      have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
      rwa [e] at h1
    have hSC : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤
        Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
      have h1 : ⁅conjClosure (VZ T M) (mcOf T), K⁆ ≤ U₁ ⊔ U₂ := by
        rw [← hsup]
        exact le_sup_left
      exact h1.trans (sup_le hU₁C hU₂C)
    have hne := S.commutator_ne_bot_of_oTwoFstarIn hG (h5 G T M S (mcOf T) hG)
      (ne_bot_of_mem_cComp hKc) (eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hKc)).symm
      (le_oTwoFstarIn_of_mem_cComp hOdd hKc) ((pCoreOf_le 2 (mcOf T)).trans hKn)
    exact hne (Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hSC)
  have hE₁ : U₁ ⊓ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) ≤ quasithinOmegaOneCenter T :=
    hSec.inf_le_of_not_le hKC hZC hnot
  have hE₂ : U₂ ⊓ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) ≤ quasithinOmegaOneCenter T := by
    rintro x ⟨hx2, hxC⟩
    have hx1 : s⁻¹ * x * s ∈ U₁ := mem_conjSub.mp (hd.dec.conj ▸ hx2)
    have hxC' : s⁻¹ * x * s ∈ Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) := by
      have h1 := conj_mem_centralizer (Subgroup.inv_mem _ (hG₁Q hsG)) hxC
      simpa using h1
    have h1 : s⁻¹ * x * s ∈ quasithinOmegaOneCenter T := hE₁ ⟨hx1, hxC'⟩
    have h2 := (Subgroup.mem_normalizer_iff.mp (hG₁Z hsG) _).mp h1
    have e : s * (s⁻¹ * x * s) * s⁻¹ = x := by group
    rwa [e] at h2
  set D : Subgroup G := Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G) ⊓
    conjClosure (VZ T M) (mcOf T) with hD
  have hDU : D ≤ conjClosure (VZ T M) (mcOf T) := inf_le_right
  have hZD : quasithinOmegaOneCenter T ≤ D := le_inf hZC hZU
  have hKD : K ≤ Subgroup.normalizer (D : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hKC hk, hKU hk⟩
  have hDN : D ≤ Subgroup.normalizer (quasithinOmegaOneCenter T : Set G) := hDU.trans hUN
  have hE₁D : U₁ ⊓ D ≤ quasithinOmegaOneCenter T := fun x hx => hE₁ ⟨hx.1, hx.2.1⟩
  have hE₂D : U₂ ⊓ D ≤ quasithinOmegaOneCenter T := fun x hx => hE₂ ⟨hx.1, hx.2.1⟩
  have hinf₁ : U₁ ⊓ D = quasithinOmegaOneCenter T :=
    le_antisymm hE₁D (le_inf hSec.le hZD)
  by_contra hlt
  push Not at hlt
  have hU2 : IsPGroup 2 (conjClosure (VZ T M) (mcOf T)) :=
    (pCoreOf_isPGroup 2 (mcOf T)).to_le hUQ
  have hrel := HypF98.relIndex_eq_two_pow_mIdx
    (Y := Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G)) hU2
  have hDrel : D.relIndex (conjClosure (VZ T M) (mcOf T)) =
      (Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G)).relIndex
        (conjClosure (VZ T M) (mcOf T)) :=
    Subgroup.inf_relIndex_right _ _
  have hle8 : D.relIndex (conjClosure (VZ T M) (mcOf T)) ≤ 8 := by
    rw [hDrel, hrel]
    calc 2 ^ mIdx (conjClosure (VZ T M) (mcOf T))
          (Subgroup.centralizer (pCoreOf 2 (mcOf T) : Set G)) ≤ 2 ^ 3 :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 8 := by norm_num
  have hsup₁ : conjClosure (VZ T M) (mcOf T) ≤ U₁ ⊔ D :=
    le_sup_of_relIndex_le_eight (fun x hx y hy => isElemAbelian_comm hUab hx hy) hUU₁.1 hDU
      hSec.le hinf₁ hSec.card hle8
  have hZU₂ : quasithinOmegaOneCenter T ≤ conjSub s U₁ := hd.dec.conj ▸ hd.dec.Z₂
  have hVU : U₁ ⊔ D ≤ conjClosure (VZ T M) (mcOf T) := sup_le hUU₁.1 hDU
  refine Sec8.false_of_decomp hSec hsimple hQ' h168 hsK (hG₁Z hsG) hout hDN hKD hZU₂ hE₁D
    (by rw [← hd.dec.conj]; exact hE₂D) (by rw [← hd.dec.conj]; exact hUU₁.2.trans hsup₁)
    (fun x hx y hy => ?_) (fun x hx => ?_)
  · have e : x * y * x⁻¹ * y⁻¹ = 1 := by
      rw [isElemAbelian_comm hUab (hVU hx) (hVU hy)]
      group
    rw [e]
    exact Subgroup.one_mem _
  · rw [isElemAbelian_pow_eq_one hUab (hVU hx)]
    exact Subgroup.one_mem _

end CFSG.Quasithin
