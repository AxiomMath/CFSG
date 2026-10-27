module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFiveTrichotomy
public import CFSG.GroupTheory.CoprimeNormalizerSup
public import CFSG.LocalAnalysis.ComponentInitial.InvolutionQuotientLocal
public import CFSG.LocalAnalysis.UniquenessCase.UC1K45W
public import CFSG.GroupTheory.SteinbergBSInvolutoryInvertedCount
public import CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialSstarNormalizerEqCenter
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
public import CFSG.LocalAnalysis.RankThreeUC.Section12.IntermediateSylow.IntermediateSylow
public import CFSG.GroupTheory.IndexTwoNormalizerOdd
public import CFSG.GroupTheory.ThompsonSubgroupIndexTwo
public import CFSG.GroupTheory.IndexTwoCenterOddAction

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

open Subgroup CFSG.Open CFSG.GroupTheory CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement IsMulCommutative
open CFSG.LocalAnalysis.RankThreeUC.Section5.ExtraspecialSstarNormalizerEqCenter

variable {G : Type} [Group G] [Finite G]

private theorem congr_eq_inv_of_fixed_of_ne_one {V : Type} [Group V] [Finite V]
    {L : Subgroup V} [L.Normal] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hLcard : Nat.card L = r) (hquot : Nat.card (V ⧸ L) = r) (σ : MulAut V)
    (hσ2 : σ * σ = 1) (hLfix : ∀ x ∈ L, σ x = x) (hσne : σ ≠ 1)
    (hmap : L.map σ.toMonoidHom = L) :
    ∀ x : V ⧸ L, (QuotientGroup.congr L L σ hmap) x = x⁻¹ := by
  classical
  have hLodd : Odd (Nat.card L) := hLcard ▸ hr.odd_of_ne_two hr2
  have hσσ : ∀ v : V, σ (σ v) = v := fun v => by
    have h := congrArg (fun f : MulAut V => f v) hσ2
    simpa using h
  let z : MulAut (V ⧸ L) := QuotientGroup.congr L L σ hmap
  have hz2 : ∀ x, z (z x) = x := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v =>
      rw [show z (QuotientGroup.mk v) = QuotientGroup.mk (σ v) from
        QuotientGroup.congr_mk L L σ hmap v]
      rw [show z (QuotientGroup.mk (σ v)) = QuotientGroup.mk (σ (σ v)) from
        QuotientGroup.congr_mk L L σ hmap (σ v)]
      rw [hσσ v]
  have hQ : (Nat.card (⊤ : Subgroup (V ⧸ L))).Prime := by
    rw [Subgroup.card_top, hquot]
    exact hr
  rcases forall_eq_or_forall_eq_inv (Q := ⊤) hQ z hz2
      (fun x _ => Subgroup.mem_top x) with hfix | hinv
  · exfalso
    apply hσne
    ext v
    have hzv : z (QuotientGroup.mk v) = QuotientGroup.mk v := hfix _ (Subgroup.mem_top _)
    rw [show z (QuotientGroup.mk v) = QuotientGroup.mk (σ v) from
      QuotientGroup.congr_mk L L σ hmap v] at hzv
    have hmem : σ v / v ∈ L := (QuotientGroup.eq_iff_div_mem).1 hzv
    have hfixmem : σ (σ v / v) = σ v / v := hLfix _ hmem
    have hinvmem : σ (σ v / v) = (σ v / v)⁻¹ := by
      rw [map_div, hσσ v, inv_div]
    have heq : σ v / v = (σ v / v)⁻¹ := hfixmem.symm.trans hinvmem
    have hsq : (σ v / v) ^ 2 = 1 := by
      rw [pow_two]
      nth_rewrite 2 [heq]
      exact mul_inv_cancel (σ v / v)
    have honeL : (⟨σ v / v, hmem⟩ : ↥L) = 1 :=
      CFSG.GroupTheory.SteinbergBS.eq_one_of_sq_eq_one hLodd (by
        apply Subtype.ext
        simpa using hsq)
    have hone : σ v / v = 1 := congrArg Subtype.val honeL
    rwa [div_eq_one] at hone
  · simpa [z] using hinv

private theorem eq_one_of_involution_of_quotient_fixed {V : Type} [Group V] [Finite V]
    {L : Subgroup V} [L.Normal] {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hLcard : Nat.card L = r) (σ : MulAut V) (hσ2 : σ * σ = 1)
    (hLfix : ∀ x ∈ L, σ x = x)
    (hquot : ∀ x : V, QuotientGroup.mk' L (σ x) = QuotientGroup.mk' L x) :
    σ = 1 := by
  classical
  have hLodd : Odd (Nat.card L) := hLcard ▸ hr.odd_of_ne_two hr2
  have hσv : ∀ v : V, σ (σ v) = v := fun v => by
    have h := congrArg (fun f : MulAut V => f v) hσ2
    simpa using h
  ext v
  have hmem : σ v / v ∈ L := (QuotientGroup.eq_iff_div_mem).1 (hquot v)
  have hfixl : σ (σ v / v) = σ v / v := hLfix _ hmem
  have hinv : σ (σ v / v) = (σ v / v)⁻¹ := by
    rw [map_div, hσv, inv_div]
  have heq : σ v / v = (σ v / v)⁻¹ := hfixl.symm.trans hinv
  have hsq : (σ v / v) ^ 2 = 1 := by
    rw [pow_two]
    nth_rewrite 2 [heq]
    exact mul_inv_cancel _
  have honeL : (⟨σ v / v, hmem⟩ : ↥L) = 1 :=
    CFSG.GroupTheory.SteinbergBS.eq_one_of_sq_eq_one hLodd (by
      apply Subtype.ext
      simpa using hsq)
  have hone : σ v / v = 1 := congrArg Subtype.val honeL
  rwa [div_eq_one] at hone

private theorem card_le_two_of_forall_eq_of_ne_one {H : Type} [Group H] [Finite H]
    (h : ∀ x y : H, x ≠ 1 → y ≠ 1 → x = y) : Nat.card H ≤ 2 := by
  classical
  by_cases htriv : ∀ x : H, x = 1
  · haveI : Subsingleton H := ⟨fun a b => (htriv a).trans (htriv b).symm⟩
    have hcard : Nat.card H ≤ 1 :=
      (Finite.card_le_one_iff_subsingleton (α := H)).mpr inferInstance
    omega
  · push Not at htriv
    obtain ⟨a, ha⟩ := htriv
    let f : H → Fin 2 := fun x => if x = 1 then 0 else 1
    have hf : Function.Injective f := by
      intro x y hxy
      by_cases hx : x = 1
      · by_cases hy : y = 1
        · rw [hx, hy]
        · exfalso
          have hx0 : f x = 0 := by simp [f, hx]
          have hy1 : f y = 1 := by simp [f, hy]
          rw [hx0, hy1] at hxy
          exact (by decide : (0 : Fin 2) ≠ 1) hxy
      · by_cases hy : y = 1
        · exfalso
          have hx1 : f x = 1 := by simp [f, hx]
          have hy0 : f y = 0 := by simp [f, hy]
          rw [hx1, hy0] at hxy
          exact (by decide : (1 : Fin 2) ≠ 0) hxy
        · exact h x y hx hy
    have := Nat.card_le_card_of_injective f hf
    simpa using this

private theorem sup_inter_pCore_eq {A O P : Subgroup G}
    (hAnormO : A ≤ normalizer (O : Set G)) (hOleP : O ≤ P) (hAnormP : A ≤ normalizer (P : Set G))
    (hAinfP : A ⊓ P = ⊥) : (A ⊔ O) ⊓ P = O := by
  apply le_antisymm
  · intro x hx
    obtain ⟨hxAO, hxP⟩ := hx
    change x ∈ (A ⊔ O : Subgroup G) at hxAO
    change x ∈ P at hxP
    have hcoe : ((A ⊔ O : Subgroup G) : Set G) = (A : Set G) * (O : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right A O hAnormO
    have hxAO' : x ∈ (A : Set G) * (O : Set G) := by
      rw [← hcoe]
      exact hxAO
    obtain ⟨a, ha, o, ho, rfl⟩ := hxAO'
    have hoP : o ∈ P := hOleP ho
    have haP : a ∈ P := by
      have h : a = (a * o) * o⁻¹ := by group
      rw [h]
      exact P.mul_mem hxP (P.inv_mem hoP)
    have habot : a ∈ (⊥ : Subgroup G) := by
      rw [← hAinfP]
      exact ⟨ha, haP⟩
    have ha1 : a = 1 := Subgroup.mem_bot.mp habot
    simpa [ha1] using ho
  · exact le_inf le_sup_right hOleP

private theorem inf_pCoreOf_eq_bot_of_odd {I A : Subgroup G}
    (hAodd : Odd (Nat.card A)) : A ⊓ pCoreOf 2 I = ⊥ := by
  have h2 : IsPGroup 2 (pCoreOf 2 I) := CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf I
  obtain ⟨k, hk⟩ := h2.exists_card_eq
  refine Subgroup.inf_eq_bot_of_coprime ?_
  rw [hk]
  exact (Nat.coprime_two_right.mpr hAodd).pow_right k

private theorem pCoreOf_inter_le_pCoreOf_of_generic (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (hgen : centralizer (A₀ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L)) :
    pCoreOf 2 (H ⊓ IOf D p L) ≤ pCoreOf 2 (IOf D p L) := by
  let I : Subgroup G := IOf D p L
  let P : Subgroup G := pCoreOf 2 I
  let O : Subgroup G := pCoreOf 2 (H ⊓ I)
  have hAI : A ≤ I := h.ctx22.ctx.hA
  have hOleH : O ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ I)).trans inf_le_left
  have hOleI : O ≤ I := (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ I)).trans inf_le_right
  have hOle : O ≤ A ⊔ P := by
    have h1 : O ≤ centralizer (A₀ : Set G) ⊓ I := by
      refine le_inf ?_ hOleI
      rw [← h.hH]
      exact hOleH
    exact h1.trans hgen
  have hP2 : IsPGroup 2 P := CFSG.LocalAnalysis.UniquenessCase.UC6S846.isPGroup_pCoreOf I
  have hO2 : IsPGroup 2 O :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ I))
  have hAnormP : A ≤ normalizer (P : Set G) :=
    (hAI.trans (Subgroup.le_normalizer)).trans
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf I)
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h.ctx22.ctx
  have h2not : ¬ 2 ∣ Nat.card A := by
    intro h2
    rcases hAodd with ⟨k, hk⟩
    omega
  exact CFSG.GroupTheory.le_of_le_sup_of_isPGroup_of_not_dvd_card Nat.prime_two hAnormP hO2
    (by rwa [sup_comm]) h2not

private theorem isZModSq_torusImage (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r) :
    IsZModSq (barImage (IOf D p L) A) (S17.nOf L) :=
  isZModSq_barImage h.hA (odd_card_of_ctx19_10 h) h.hAcard

private theorem isMulCommutative_torusImage (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r) :
    IsMulCommutative ↥(barImage (IOf D p L) A) :=
  isMulCommutative_of_isZModSq (isZModSq_torusImage D h)

private theorem card_torusImage (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} (h : Ctx19_10 D V₀ V p L A t B r) :
    Nat.card (barImage (IOf D p L) A) = (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) :=
  card_eq_of_isZModSq (isZModSq_torusImage D h)

private theorem fixedLine_le_powTorsion (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    [IsMulCommutative ↥(barImage (IOf D p L) A)] :
    barImage (IOf D p L) A₀ ≤
      (MonoidHom.ker (powMonoidHom r :
        ↥(barImage (IOf D p L) A) →* ↥(barImage (IOf D p L) A))).map
        (barImage (IOf D p L) A).subtype := by
  classical
  let I : Subgroup G := IOf D p L
  have hA₀I : A₀ ≤ I := h.ctx22.hA₀.trans h.ctx22.ctx.hA
  have hA₀A : A₀ ≤ A := h.ctx22.hA₀
  rintro y hy
  obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp hy
  have ha₀A : (a₀ : ↥I) ∈ A.subgroupOf I := by
    rw [Subgroup.mem_subgroupOf]
    exact hA₀A ha₀
  have hdvd : orderOf (a₀ : ↥I) ∣ r := by
    have h1 : orderOf ((a₀ : ↥I) : G) ∣ Nat.card A₀ :=
      Subgroup.orderOf_dvd_natCard A₀ ha₀
    rw [← orderOf_injective I.subtype I.subtype_injective a₀]
    rwa [h.ctx22.hcard] at h1
  have hpow : (a₀ : ↥I) ^ r = 1 := by
    rwa [← orderOf_dvd_iff_pow_eq_one]
  rw [mem_powTorsionSubgroup]
  constructor
  · unfold barImage
    exact Subgroup.mem_map.mpr ⟨a₀, ha₀A, rfl⟩
  · rw [← map_pow, hpow, map_one]

private theorem map_torusImage_rho (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (hHI : H ⊓ IOf D p L = A ⊔ pCoreOf 2 (H ⊓ IOf D p L))
    (hOleP2 : pCoreOf 2 (H ⊓ IOf D p L) ≤ pCoreOf 2 (IOf D p L))
    {s : G} (hsNE : s ∈ normalizer (H ⊓ IOf D p L : Set G))
    (hsNI : s ∈ normalizer (IOf D p L : Set G)) :
    (barImage (IOf D p L) A).map
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL (IOf D p L) ⟨s, hsNI⟩).toMonoidHom =
      barImage (IOf D p L) A := by
  classical
  let I : Subgroup G := IOf D p L
  let O : Subgroup G := pCoreOf 2 (H ⊓ I)
  let E : Subgroup G := A ⊔ O
  let T : Subgroup (Bar2 I) := barImage (IOf D p L) A
  let TE : Subgroup (Bar2 I) := (E.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I))
  let ρ : MulAut (Bar2 I) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨s, hsNI⟩
  have hAI : A ≤ I := h.ctx22.ctx.hA
  have hOleI : O ≤ I :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ I)).trans inf_le_right
  have hEeq : E = H ⊓ I := hHI.symm
  have hEsub : E.subgroupOf I = A.subgroupOf I ⊔ O.subgroupOf I := by
    rw [Subgroup.subgroupOf_sup hAI hOleI]
  have hOsub : O.subgroupOf I ≤ CFSG.pCore 2 ↥I := by
    intro x hx
    have hxO : (x : G) ∈ O := Subgroup.mem_subgroupOf.mp hx
    have hxP : (x : G) ∈ pCoreOf 2 I := hOleP2 hxO
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hxP
    have hyx' : y = x := Subtype.ext hyx
    simpa [hyx'] using hy
  have hOmap : (O.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) = ⊥ := by
    rw [Subgroup.map_eq_bot_iff]
    rw [QuotientGroup.ker_mk']
    exact hOsub
  have hTE : TE = T := by
    change ((E.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I))) =
      ((A.subgroupOf I).map (QuotientGroup.mk' (CFSG.pCore 2 ↥I)))
    rw [hEsub, Subgroup.map_sup, hOmap, sup_bot_eq]
  have hsNE' : s ∈ normalizer (E : Set G) := by
    rw [hEeq]
    exact hsNE
  have hmapE_le : TE.map ρ ≤ TE := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨e, heE, rfl⟩ := Subgroup.mem_map.mp hx
    have heE' : (e : G) ∈ E := Subgroup.mem_subgroupOf.mp heE
    have hseE : s * (e : G) * s⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp hsNE' (e : G)).mp heE'
    have hseI : s * (e : G) * s⁻¹ ∈ I :=
      (Subgroup.mem_normalizer_iff.mp hsNI (e : G)).mp e.2
    refine Subgroup.mem_map.mpr ⟨⟨s * (e : G) * s⁻¹, hseI⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hseE
    · change (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) ⟨s * (e : G) * s⁻¹, hseI⟩ =
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨s, hsNI⟩)
          (QuotientGroup.mk e)
      rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
      congr 1
  have hmapE : TE.map ρ = TE := by
    refine Subgroup.eq_of_le_of_card_ge hmapE_le ?_
    exact le_of_eq (Subgroup.card_map_of_injective (f := ρ.toMonoidHom) ρ.injective).symm
  have hmapT : T.map ρ = T := by
    calc T.map ρ = TE.map ρ := by rw [hTE]
      _ = TE := hmapE
      _ = T := hTE
  exact hmapT

private theorem map_powTorsion_rho (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (hHI : H ⊓ IOf D p L = A ⊔ pCoreOf 2 (H ⊓ IOf D p L))
    (hOleP2 : pCoreOf 2 (H ⊓ IOf D p L) ≤ pCoreOf 2 (IOf D p L))
    {s : G} (hsNE : s ∈ normalizer (H ⊓ IOf D p L : Set G))
    (hsNI : s ∈ normalizer (IOf D p L : Set G))
    [IsMulCommutative ↥(barImage (IOf D p L) A)] :
    ((MonoidHom.ker (powMonoidHom r :
      ↥(barImage (IOf D p L) A) →* ↥(barImage (IOf D p L) A))).map
        (barImage (IOf D p L) A).subtype).map
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL (IOf D p L) ⟨s, hsNI⟩).toMonoidHom =
      (MonoidHom.ker (powMonoidHom r :
        ↥(barImage (IOf D p L) A) →* ↥(barImage (IOf D p L) A))).map
        (barImage (IOf D p L) A).subtype := by
  classical
  let I : Subgroup G := IOf D p L
  let T : Subgroup (Bar2 I) := barImage (IOf D p L) A
  let V : Subgroup (Bar2 I) :=
    (MonoidHom.ker (powMonoidHom r : ↥T →* ↥T)).map T.subtype
  let ρ : MulAut (Bar2 I) :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨s, hsNI⟩
  have hTmap : T.map ρ = T := by
    simpa [T, ρ] using map_torusImage_rho D h hHI hOleP2 hsNE hsNI
  have hle : V.map ρ ≤ V := by
    rintro y ⟨x, hx, rfl⟩
    change x ∈ (MonoidHom.ker (powMonoidHom r : ↥T →* ↥T)).map T.subtype at hx
    change ρ x ∈ (MonoidHom.ker (powMonoidHom r : ↥T →* ↥T)).map T.subtype
    rw [mem_powTorsionSubgroup] at hx ⊢
    constructor
    · have hxT : x ∈ T := hx.1
      have hthis : ρ x ∈ T.map ρ.toMonoidHom := Subgroup.mem_map_of_mem ρ.toMonoidHom hxT
      have hmem : ρ x ∈ T := by simpa [hTmap] using hthis
      simpa [T] using hmem
    · rw [← map_pow, hx.2, map_one]
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  exact le_of_eq (Subgroup.card_map_of_injective (f := ρ.toMonoidHom) ρ.injective).symm

theorem pCoreOf_sup_le_sylow_of_ctx19_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M)) :
    pCoreOf 2 (A ⊔ S) ≤ S := by
  have hAH : A ≤ H := A_le_H_of_ctx19_23 h
  have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h.ctx22.ctx
  have hASM : A ⊔ S ≤ H ⊓ D.M := sup_le (le_inf hAH hAM) hS.le
  exact CFSG.LocalAnalysis.RankThreeUC.Section12.IntermediateSylow.pCoreOf_le_sylow
    (hS.of_le le_sup_right hASM)

theorem isMulCommutative_A_of_ctx19_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) :
    IsMulCommutative ↥A :=
  isMulCommutative_of_isZModSq h.ctx22.ctx.hAcard

theorem odd_card_A_of_ctx19_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H) :
    Odd (Nat.card A) :=
  odd_card_of_ctx19_10 h.ctx22.ctx

theorem three_not_dvd_card_A_of_ctx19_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h) :
    ¬ 3 ∣ Nat.card A := by
  have hcard : Nat.card A = (2 ^ S17.nOf L - 1) * (2 ^ S17.nOf L - 1) :=
    card_eq_of_isZModSq h.ctx22.ctx.hAcard
  rw [hcard, ← pow_two]
  exact fun h3 => CFSG.GH74.Uniqueness.Hering.three_not_dvd_two_pow_sub_one h26
    (Nat.Prime.dvd_of_dvd_pow (p := 3) (n := 2) (by norm_num) h3)

theorem exists_s_of_ctx19_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
    (hQrel : (pCoreOf 2 (A ⊔ S)).relIndex S = 2) :
    ∃ s : G, s ∈ S ∧ s ∉ pCoreOf 2 (A ⊔ S) ∧
      s ∈ normalizer (A : Set G) ∧ s * s ∈ pCoreOf 2 (A ⊔ S) ∧
        ∀ a ∈ A, s * (s * a * s⁻¹) * s⁻¹ = a :=
  exists_mem_normalizer_not_mem_of_relIndex_two
    (odd_card_A_of_ctx19_23 D h) hS.isPGroup (permutes_of_ctx19_23 D h h25 hS) hQrel

theorem not_commutator_zpowers_eq_bot_of_ctx19_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
    (hQrel : (pCoreOf 2 (A ⊔ S)).relIndex S = 2) {s : G} (hsS : s ∈ S)
    (hsQ : s ∉ pCoreOf 2 (A ⊔ S))
    (hB : ⁅A, Subgroup.zpowers s⁆ = ⊥) : False :=
  false_of_commutator_zpowers_eq_bot
    (odd_card_A_of_ctx19_23 D h) hS.isPGroup (permutes_of_ctx19_23 D h h25 hS)
    hQrel hsS hsQ hB

@[expose] def Trichotomy19_28 (D : Data G) (V₀ V : Subgroup G) (p : ℕ) (L A : Subgroup G)
    (t : G) (B : Subgroup G) (r : ℕ) (A₀ H : Subgroup G)
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h) : Prop :=
  ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M) →
    (pCoreOf 2 (A ⊔ S)).relIndex S ≤ 2 →
      ((((Subgroup.center ↥S).map S.subtype : Subgroup G)).subgroupOf (A ⊔ S)).Normal ∨
        (((CFSG.Open.thompsonSubgroup S).subgroupOf (A ⊔ S)).Normal) ∨
          ∃ E : Subgroup G, E ≤ A ∧ CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
            (S ⊓ centralizer (E : Set G)).relIndex S ≤ 2

theorem exists_s_trichotomy_of_ctx19_23 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h) :
    ∀ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M) →
      (pCoreOf 2 (A ⊔ S)).relIndex S = 2 →
        ∃ s : G, s ∈ S ∧ s ∉ pCoreOf 2 (A ⊔ S) ∧ s ∈ normalizer (A : Set G) ∧
          s * s ∈ pCoreOf 2 (A ⊔ S) ∧
          (∀ a ∈ A, s * (s * a * s⁻¹) * s⁻¹ = a) ∧
          (let B₀ : Subgroup G := ⁅A, Subgroup.zpowers s⁆
           let Z : Subgroup G :=
             (Subgroup.center ↥(pCoreOf 2 (A ⊔ S))).map (pCoreOf 2 (A ⊔ S)).subtype
           let ZS : Subgroup G := (Subgroup.center ↥S).map S.subtype
           (((ZS.subgroupOf (A ⊔ S)).Normal) ∨
             (((CFSG.Open.thompsonSubgroup S).subgroupOf (A ⊔ S)).Normal) ∨
             (⁅Z, B₀⁆ = ⊥ ∧
               (ZS ≤ pCoreOf 2 (A ⊔ S) → (ZS.subgroupOf (A ⊔ S)).Normal) ∧
               (¬ ZS ≤ pCoreOf 2 (A ⊔ S) → ⁅pCoreOf 2 (A ⊔ S), B₀⁆ = ⊥) ∧
               (B₀ = ⊥ → (ZS.subgroupOf (A ⊔ S)).Normal)))) := by
  intro S hS hQrel
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let X : Subgroup G := A ⊔ S
  let Q : Subgroup G := pCoreOf 2 X
  let Z : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
  let ZS : Subgroup G := (Subgroup.center ↥S).map S.subtype
  have hAodd : Odd (Nat.card A) := odd_card_A_of_ctx19_23 D h
  haveI hAcomm : IsMulCommutative ↥A := isMulCommutative_A_of_ctx19_23 D h
  have h3A : ¬ 3 ∣ Nat.card A := three_not_dvd_card_A_of_ctx19_23 D h h26
  have hQleS : Q ≤ S := pCoreOf_sup_le_sylow_of_ctx19_23 D h hS
  have hXleNQ : X ≤ Subgroup.normalizer (Q : Set G) := by
    simpa [X, Q] using CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hAQ : A ≤ Subgroup.normalizer (Q : Set G) := le_sup_left.trans hXleNQ
  obtain ⟨s, hsS, hsQ, hsN, hs2Q, hsα⟩ := exists_s_of_ctx19_23 D h h25 hS hQrel
  let B₀ : Subgroup G := ⁅A, Subgroup.zpowers s⁆
  have hBinv : ∀ x ∈ B₀, s * x * s⁻¹ = x⁻¹ :=
    inv_of_mem_commutator_zpowers_of_sq_centralizes hsN hsα
  refine ⟨s, hsS, hsQ, hsN, ?_, hsα, ?_⟩
  · simpa [Q] using hs2Q
  · change ((ZS.subgroupOf X).Normal ∨
      (((CFSG.Open.thompsonSubgroup S).subgroupOf X).Normal) ∨
      (⁅Z, B₀⁆ = ⊥ ∧
        (ZS ≤ Q → (ZS.subgroupOf X).Normal) ∧
        (¬ ZS ≤ Q → ⁅Q, B₀⁆ = ⊥) ∧
        (B₀ = ⊥ → (ZS.subgroupOf X).Normal)))
    by_cases hZB : ⁅Z, B₀⁆ = ⊥
    · refine Or.inr (Or.inr ⟨hZB, ?_, ?_, ?_⟩)
      · intro hZSle
        have hAnormZS : A ≤ Subgroup.normalizer (ZS : Set G) :=
          le_normalizer_center_of_le hAodd hS.isPGroup hQleS hQrel hAQ hsS hsQ hsN
            hAcomm (by simpa [Z, B₀] using hZB) (by simpa [ZS] using hZSle)
        have hSnormZS : S ≤ Subgroup.normalizer (ZS : Set G) :=
          CFSG.ABGLocalTools.le_normalizer_map_subtype S (Subgroup.center ↥S)
        have hXnormZS : X ≤ Subgroup.normalizer (ZS : Set G) := by
          rw [show X = A ⊔ S from rfl]
          exact sup_le hAnormZS hSnormZS
        have hZSleX : ZS ≤ X :=
          (Subgroup.map_subtype_le (Subgroup.center ↥S)).trans le_sup_right
        exact (Subgroup.normal_subgroupOf_iff_le_normalizer hZSleX).mpr hXnormZS
      · intro hZSnotle
        simpa [B₀] using commutator_eq_bot_of_center_not_le hAodd hS.isPGroup hQleS
          hQrel hAQ hsS hsQ hsN hBinv (by simpa [ZS] using hZSnotle)
      · intro hB1
        exact False.elim (not_commutator_zpowers_eq_bot_of_ctx19_23 D h h25 hS hQrel
          hsS hsQ (by simpa [B₀] using hB1))
    · exact Or.inr (Or.inl (thompsonSubgroup_normal_of_commutator_center_ne hAodd h3A
        hS.isPGroup hQleS hQrel hAQ hsS hsQ hsN hBinv (by simpa [Z, B₀] using hZB)
        le_sup_right hXleNQ))

theorem exists_normalU_of_trichotomy19_28 (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx22.ctx)
    {S : Subgroup G} (hS : CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ D.M))
    (htri : ((((Subgroup.center ↥S).map S.subtype : Subgroup G)).subgroupOf (A ⊔ S)).Normal ∨
      (((CFSG.Open.thompsonSubgroup S).subgroupOf (A ⊔ S)).Normal) ∨
        ∃ E : Subgroup G, E ≤ A ∧ CFSG.Open.IsElemAbelian r E ∧ Nat.card E = r ^ 2 ∧
          (S ⊓ centralizer (E : Set G)).relIndex S ≤ 2) :
    ∃ U : Subgroup G, U ≠ ⊥ ∧ U ≤ S ∧
      normalizer (S : Set G) ≤ normalizer (U : Set G) ∧ A ≤ normalizer (U : Set G) := by
  rcases htri with hZ | hJ | ⟨E, hEA, hEel, hEcard, hEidx⟩
  · exact exists_normalU_of_trichotomy D h h12 hS (Or.inl hZ)
  · exact exists_normalU_of_trichotomy D h h12 hS (Or.inr (Or.inl hJ))
  · haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h.ctx22.ctx
    have hV0ne : V₀ ≠ ⊥ := ne_bot_of_one_lt_mSub h.ctx22.ctx.hyp.big
    have hV0data := inCalV0_of_hyp125 h.ctx22.ctx.hyp.hyp125 hV0ne
    have hV0p : IsPGroup 2 V₀ := hV0data.1.2.2.2.isPGroup
    have hV0H : V₀ ≤ H := h.hH ▸ h.ctx22.hV₀
    have hV0M : V₀ ≤ D.M := hV0data.1.2.1
    have hMV0 : D.M ≤ normalizer (V₀ : Set G) := hV0data.1.2.2.1
    have hV0HM : V₀ ≤ H ⊓ D.M := le_inf hV0H hV0M
    have hV0card4 : 4 ≤ Nat.card V₀ := by
      rw [card_eq_two_pow_mSub hV0p]
      have h2 : 2 ≤ mSub V₀ := Nat.succ_le_of_lt h.ctx22.ctx.hyp.big
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ mSub V₀ := Nat.pow_le_pow_right (by norm_num) h2
    let C : Subgroup G := S ⊓ centralizer (E : Set G)
    have hTI : CFSG.CGT.Timmesfeld75.IsTI V₀ := isTI_of_hyp19 h.ctx22.ctx.hyp
    have hEU : E ∈ CFSG.LocalAnalysis.RankThreeUC.uniqueSet D.M := h12 E hEA hEel hEcard
    have key : ∀ g : G, CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ ≤ S →
        CFSG.CGT.Timmesfeld75.conjSubgroup g V₀ = V₀ := by
      intro g hg
      let Vg : Subgroup G := CFSG.CGT.Timmesfeld75.conjSubgroup g V₀
      let X : Subgroup G := Vg ⊓ C
      have hVgcard : Nat.card Vg = Nat.card V₀ :=
        Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
          (MulAut.conj g).injective
      have hXidx : X.relIndex Vg ≤ 2 := by
        have h1 : X.relIndex Vg ≤ Vg.relIndex Vg * C.relIndex Vg := Subgroup.relIndex_inf_le
        rw [Subgroup.relIndex_self, one_mul] at h1
        refine h1.trans ?_
        exact (Subgroup.relIndex_le_of_le_right (H := C) (K := Vg) (L := S) hg (by
          rw [Subgroup.relIndex]
          exact Subgroup.index_ne_zero_of_finite)).trans hEidx
      have hXcard : 1 < Nat.card X := by
        set k := X.relIndex Vg with hk
        have hkpos : 0 < k := by
          rw [hk, Subgroup.relIndex]
          exact Nat.pos_of_ne_zero (Subgroup.index_ne_zero_of_finite)
        have hk2 : k ≤ 2 := hXidx
        have hmul' := Subgroup.relIndex_mul_card X Vg
        rw [inf_eq_left.mpr (show X ≤ Vg from inf_le_left)] at hmul'
        have hmul : k * Nat.card X = Nat.card Vg := by simpa [hk] using hmul'
        rw [hVgcard] at hmul
        have : 2 ≤ Nat.card X := by
          interval_cases k <;> omega
        omega
      haveI : Nontrivial ↥X := Finite.one_lt_card_iff_nontrivial.mp hXcard
      obtain ⟨a, ha1⟩ := exists_ne (1 : ↥X)
      have haX : (a : G) ∈ X := a.2
      have ha1' : (a : G) ≠ 1 := fun h' => ha1 (Subtype.ext h')
      have hXE : E ≤ centralizer (X : Set G) := by
        intro a' ha'
        rw [Subgroup.mem_centralizer_iff]
        intro x hx
        exact (Subgroup.mem_centralizer_iff.mp hx.2.2 a' ha').symm
      have hTIg : CFSG.CGT.Timmesfeld75.IsTI Vg := by
        simpa [Vg] using CFSG.RankThree.GF2n.isTI_conjSubgroup hTI g
      have hXa : centralizer (X : Set G) ≤
          centralizer ((Subgroup.zpowers a : Subgroup G) : Set G) :=
        Subgroup.centralizer_le (Subgroup.zpowers_le.mpr haX)
      have hCXN : centralizer (X : Set G) ≤ normalizer (Vg : Set G) := by
        refine hXa.trans ?_
        intro y hy
        exact CFSG.CGT.PushingUpLit.SolKAb.centralizer_le_normalizer_of_isTI hTIg haX.1 ha1'
          (Subgroup.mem_centralizer_iff.mp hy (a : G) (Subgroup.mem_zpowers (a : G))).symm
      have hEg : E ≤ D.M.map (MulAut.conj g).toMonoidHom := by
        have hMgmax : CFSG.Open.rankThreeIsMaxTwoLocal
            (D.M.map (MulAut.conj g).toMonoidHom) :=
          CFSG.LocalAnalysis.RankThreeTheoremC.rankThreeIsMaxTwoLocal_map D.maxLocal
            (MulAut.conj g)
        have hVgne : Vg ≠ ⊥ := by
          intro hbot
          have hcard1 : Nat.card Vg = 1 := by rw [hbot, Subgroup.card_bot]
          rw [hVgcard] at hcard1
          omega
        have hVgp : IsPGroup 2 Vg := hV0p.map _
        have hMgle : D.M.map (MulAut.conj g).toMonoidHom ≤ normalizer (Vg : Set G) := by
          have h := Subgroup.map_mono (f := (MulAut.conj g).toMonoidHom) hMV0
          rwa [Subgroup.map_equiv_normalizer_eq] at h
        have hNVg : normalizer (Vg : Set G) = D.M.map (MulAut.conj g).toMonoidHom :=
          CFSG.LocalAnalysis.RankThreeUC.normalizer_eq_of_isMaxTwoLocal hMgmax hVgne hVgp hMgle
        rw [← hNVg]
        exact hXE.trans hCXN
      have hMge : D.M.map (MulAut.conj g).toMonoidHom = D.M := hEU.2 g hEg
      have hgM : g ∈ D.M := by
        have hgN : g ∈ normalizer (D.M : Set G) :=
          Subgroup.mem_normalizer_iff_map_conj_eq.mpr hMge
        rwa [CFSG.RankThreeCoreUniqueness.Helpers.maxTwoLocal_self_normalizing D.M D.maxLocal]
          at hgN
      have hgV : g ∈ normalizer (V₀ : Set G) := hMV0 hgM
      have hmap : V₀.map (MulAut.conj g).toMonoidHom = V₀ :=
        Subgroup.mem_normalizer_iff_map_conj_eq.mp hgV
      simpa [Vg, CFSG.CGT.Timmesfeld75.conjSubgroup] using hmap
    obtain ⟨g, -, hgS⟩ :=
      CFSG.CGT.PushingUpLit.A78Sp4.exists_conj_le_of_isSylowOf hS hV0HM hV0p
    have hV0leS : V₀ ≤ S := by
      have h := key g hgS
      rw [← h]
      exact hgS
    refine ⟨V₀, hV0ne, hV0leS, ?_, hAM.trans hMV0⟩
    intro s hs
    have hSs : S.map (MulAut.conj s).toMonoidHom = S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hs
    have hVgs : CFSG.CGT.Timmesfeld75.conjSubgroup s V₀ ≤ S := by
      rw [CFSG.CGT.Timmesfeld75.conjSubgroup]
      calc V₀.map (MulAut.conj s).toMonoidHom ≤ S.map (MulAut.conj s).toMonoidHom :=
            Subgroup.map_mono hV0leS
        _ = S := hSs
    have h := key s hVgs
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
      (by simpa [CFSG.CGT.Timmesfeld75.conjSubgroup] using h)

theorem nineteen_twentyeight_of_gap19_28 (D : Data G) {V₀ V : Subgroup G} {p : ℕ} {L A : Subgroup G}
    {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h)
    (h14 : R19_14At D V₀ V p L A t B r h.ctx22.ctx)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx22.ctx)
    (hgap : Gap19_28 D V₀ V p L A t B r A₀ H h h25 h26)
    (hgapT : Trichotomy19_28 D V₀ V p L A t B r A₀ H h h25 h26) :
    R19_28At D V₀ V p L A t B r A₀ H h := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  change Concl19_28 D A H
  intro S hS
  have hindex : (pCoreOf 2 (A ⊔ S)).relIndex S ≤ 2 :=
    relIndex_le_two_of_gap19_28 D h h25 h26 hgap hS
  refine ⟨permutes_of_ctx19_23 D h h25 hS, hindex, ?_⟩
  have htM : t ∈ D.M :=
    IOf_le_M D p h.ctx22.ctx.hyp.hL.1.1.le h.ctx22.ctx.htA
  have htH : t ∈ normalizer (H : Set G) := by
    rw [h.hH]
    exact CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup A₀
      (UC22.mem_normalizer_of_inverts h.ctx22.hA₀ h.ctx22.ctx.hinv)
  have htK : t ∈ normalizer ((H ⊓ D.M : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf (H := H) (K := D.M)
      ⟨htH, Subgroup.le_normalizer htM⟩
  obtain ⟨S', hS', htS', hcard⟩ :=
    exists_tInvariant_sylow_of_isSylow h.ctx22.ctx.ht2 htK hS
  have hindex' : (pCoreOf 2 (A ⊔ S')).relIndex S' ≤ 2 :=
    relIndex_le_two_of_gap19_28 D h h25 h26 hgap hS'
  obtain ⟨U, hUne, hUle, hNSU, hAU⟩ :=
    exists_normalU_of_trichotomy19_28 D h h12 hS' (hgapT S' hS' hindex')
  have hS'H : CFSG.ABGLocalTools.IsSylowOf 2 S' H :=
    isSylow_of_normalU D h h14 hS' htS' hUne hUle hNSU hAU
  have hcard' : Nat.card S = 2 ^ (Nat.card H).factorization 2 := by
    rw [← hcard]
    exact hS'H.card_eq
  exact CFSG.ABGLocalTools.isSylowOf_of_card (hS.le.trans inf_le_left) hcard'

@[expose] def K_19_28_torusAutomizer : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (n : ℕ), 3 ≤ n → Odd n →
    (IsSp4 X n ∨ IsL2Square X n ∨ IsSzSquare X n) →
    ∀ T : Subgroup X, IsZModSq T n → ∀ σ : MulAut X, (∃ k : ℕ, orderOf σ = 2 ^ k) →
      T.map σ.toMonoidHom = T → (∃ t₀ ∈ T, t₀ ≠ 1 ∧ σ t₀ = t₀) →
        (∀ x ∈ T, σ x = x) ∨ ((∀ x ∈ T, σ (σ x) = x) ∧
          ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 → ∃ x ∈ T, orderOf x = ℓ ∧ σ x = x⁻¹)

theorem gap19_28_of_torusAutomizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h)
    (hgen : centralizer (A₀ : Set G) ⊓ IOf D p L ≤ A ⊔ pCoreOf 2 (IOf D p L))
    (hshape : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∨ IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L))
    (hK : K_19_28_torusAutomizer) :
    Gap19_28 D V₀ V p L A t B r A₀ H h h25 h26 := by
  classical
  intro S hS
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I : Subgroup G := IOf D p L
  let n : ℕ := S17.nOf L
  let O : Subgroup G := pCoreOf 2 (H ⊓ I)
  let P2 : Subgroup G := pCoreOf 2 I
  have hAI : A ≤ I := h.ctx22.ctx.hA
  have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h.ctx22.ctx
  have hIM : I ≤ D.M := IOf_le_M D p h.ctx22.ctx.hyp.hL.1.1.le
  have hSM : S ≤ D.M := hS.le.trans inf_le_right
  have hSH : S ≤ H := hS.le.trans inf_le_left
  have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h.ctx22.ctx
  have hAH : A ≤ H := A_le_H_of_ctx19_23 h
  have hA₀A : A₀ ≤ A := h.ctx22.hA₀
  have hA₀I : A₀ ≤ I := hA₀A.trans hAI
  have hOleI : O ≤ I :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ I)).trans inf_le_right
  have hHI : H ⊓ I = A ⊔ O := inter_eq_sup_pCoreOf_of_generic D h hgen
  have hOleP2 : O ≤ P2 := pCoreOf_inter_le_pCoreOf_of_generic D h hgen
  have hr : r.Prime := h.ctx22.ctx.hr.1
  have hr2 : r ≠ 2 := by
    intro h2
    exact hAodd.not_two_dvd_nat (h2 ▸ h.ctx22.ctx.hr.2)
  have hnodd : Odd n := h26
  have hcardA : Nat.card A = (2 ^ n - 1) * (2 ^ n - 1) :=
    card_eq_of_isZModSq h.ctx22.ctx.hAcard
  have hn3 : 3 ≤ n := three_le_nOf_of_setting1910 h.ctx22.ctx.h1910
  let T : Subgroup (Bar2 I) := barImage (IOf D p L) A
  let Lf : Subgroup (Bar2 I) := barImage (IOf D p L) A₀
  haveI hTcomm : IsMulCommutative ↥T := isMulCommutative_torusImage D h.ctx22.ctx
  let V : Subgroup (Bar2 I) :=
    (MonoidHom.ker (powMonoidHom r : ↥T →* ↥T)).map T.subtype
  have hTz : IsZModSq T n := isZModSq_torusImage D h.ctx22.ctx
  have hLcard : Nat.card Lf = r := card_barImage_of_prime_of_le hr hr2 h.ctx22.hcard hA₀I
  have hLV : Lf ≤ V := fixedLine_le_powTorsion D h
  have hVcard : Nat.card V = r ^ 2 := by
    apply card_powTorsionSubgroup_of_isZModSq hTz hr
    rw [card_torusImage D h.ctx22.ctx]
    simpa [hcardA, n] using h.ctx22.ctx.hr.2
  have hVleT : V ≤ T := fun x hx => (mem_powTorsionSubgroup.mp hx).1
  have hVcomm : IsMulCommutative ↥V := by
    haveI : IsMulCommutative ↥(V.subgroupOf T) := inferInstance
    exact CFSG.LocalAnalysis.UniquenessCase.UCK.UC46.isMulCommutative_of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hVleT).symm inferInstance
  have hsNI : ∀ s ∈ S, s ∈ normalizer (I : Set G) :=
    fun s hs => le_normalizer_IOf D h.ctx22.ctx.hyp.hL.1 (hSM hs)
  have hsNE : ∀ s ∈ S, s ∈ normalizer (H ⊓ I : Set G) :=
    fun s hs => sylow_le_normalizer_inter_IOf D h hS hs
  have hTmap : ∀ s : ↥S, T.map (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
      ⟨s.1, hsNI s.1 s.2⟩).toMonoidHom = T :=
    fun s => map_torusImage_rho D h hHI hOleP2 (hsNE s.1 s.2) (hsNI s.1 s.2)
  let φFun : ↥S → MulAut ↥T := fun s =>
    ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
        ⟨s.1, hsNI s.1 s.2⟩).subgroupMap T).trans
      (MulEquiv.subgroupCongr (hTmap s))
  have φFun_coe : ∀ (s : ↥S) (t : ↥T),
      ((φFun s t : ↥T) : Bar2 I) =
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
          ⟨s.1, hsNI s.1 s.2⟩) (t : Bar2 I) := by
    intro s t
    unfold φFun
    calc ((MulEquiv.subgroupCongr (hTmap s))
          ((MulEquiv.subgroupMap (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
            ⟨s.1, hsNI s.1 s.2⟩) T) t) : Bar2 I)
        = ((MulEquiv.subgroupMap (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
            ⟨s.1, hsNI s.1 s.2⟩) T) t : Bar2 I) :=
          MulEquiv.subgroupCongr_apply (hTmap s) _
      _ = (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
            ⟨s.1, hsNI s.1 s.2⟩) (t : Bar2 I) :=
          MulEquiv.coe_subgroupMap_apply _ _ _
  have φFun_one : φFun 1 = 1 := by
    ext t
    rw [φFun_coe]
    rw [show (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
        ⟨(1 : ↥S).1, hsNI (1 : ↥S).1 (1 : ↥S).2⟩) = 1 from map_one _]
    rfl
  have φFun_mul : ∀ s t : ↥S, φFun (s * t) = φFun s * φFun t := by
    intro s t
    ext x
    rw [φFun_coe]
    rw [MulAut.mul_apply, φFun_coe, φFun_coe]
    rw [show (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
        ⟨(s * t).1, hsNI (s * t).1 (s * t).2⟩) =
        CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨s.1, hsNI s.1 s.2⟩ *
          CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨t.1, hsNI t.1 t.2⟩ from by
      rw [← map_mul]
      congr 1]
    rfl
  let φ : ↥S →* MulAut ↥T :=
    { toFun := φFun
      map_one' := φFun_one
      map_mul' := φFun_mul }
  have hLfix : ∀ (s : ↥S) (y : ↥T), (y : Bar2 I) ∈ Lf → φ s y = y := by
    intro s y hy
    obtain ⟨a, ha, hya⟩ := Subgroup.mem_map.mp hy
    have hya' : QuotientGroup.mk' (CFSG.pCore 2 ↥I) a = (y : Bar2 I) := hya
    have haA₀ : (a : G) ∈ A₀ := Subgroup.mem_subgroupOf.mp ha
    have hsC : s.1 ∈ centralizer (A₀ : Set G) := by
      rw [← h.hH]
      exact hSH s.2
    have hcomm : (a : G) * s.1 = s.1 * (a : G) :=
      (Subgroup.mem_centralizer_iff.mp hsC) (a : G) haA₀
    apply Subtype.ext
    change ((φFun s) y : ↥T).1 = (y : ↥T).1
    rw [φFun_coe]
    rw [← hya']
    change (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
      ⟨s.1, hsNI s.1 s.2⟩) (QuotientGroup.mk' (CFSG.pCore 2 ↥I) a) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥I) a
    rw [show QuotientGroup.mk' (CFSG.pCore 2 ↥I) a = QuotientGroup.mk a from rfl]
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
    congr 1
    apply Subtype.ext
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk_coe]
    rw [← hcomm]
    group
  have hA₀nt : Nontrivial ↥A₀ := by
    apply Finite.one_lt_card_iff_nontrivial.mp
    rw [h.ctx22.hcard]
    exact hr.one_lt
  obtain ⟨a₀, ha₀ne⟩ := exists_ne (1 : ↥A₀)
  let x0 : Bar2 I := QuotientGroup.mk (⟨a₀.1, hA₀I a₀.2⟩ : ↥I)
  have hx0T : x0 ∈ T := by
    change x0 ∈ barImage (IOf D p L) A
    refine Subgroup.mem_map.mpr ⟨⟨a₀.1, hAI (hA₀A a₀.2)⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hA₀A a₀.2
    · rfl
  let t0 : ↥T := ⟨x0, hx0T⟩
  have ht0ne : t0 ≠ 1 := by
    intro h
    have hx1 : x0 = 1 := congrArg Subtype.val h
    have hmemN : (⟨a₀.1, hA₀I a₀.2⟩ : ↥I) ∈ CFSG.pCore 2 ↥I := by
      have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥I) (⟨a₀.1, hA₀I a₀.2⟩ : ↥I) = 1 := by
        simpa [x0] using hx1
      exact (QuotientGroup.eq_one_iff _).1 hq
    have hmemP : (a₀.1 : G) ∈ P2 := Subgroup.mem_map_of_mem I.subtype hmemN
    have hbot : (a₀.1 : G) ∈ (⊥ : Subgroup G) := by
      rw [← inf_pCoreOf_eq_bot_of_odd (I := I) hAodd]
      exact ⟨hA₀A a₀.2, hmemP⟩
    have h1G : (a₀.1 : G) = 1 := Subgroup.mem_bot.mp hbot
    exact ha₀ne (Subtype.ext h1G)
  have hfix0 : ∀ s : ↥S, φ s t0 = t0 := by
    intro s
    have hsC : s.1 ∈ centralizer (A₀ : Set G) := by
      rw [← h.hH]
      exact hSH s.2
    have hcomm : a₀.1 * s.1 = s.1 * a₀.1 :=
      (Subgroup.mem_centralizer_iff.mp hsC) a₀.1 a₀.2
    have hconj : s.1 * a₀.1 * s.1⁻¹ = a₀.1 := by
      rw [← hcomm]
      group
    apply Subtype.ext
    change (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
      ⟨s.1, hsNI s.1 s.2⟩) x0 = x0
    unfold x0
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
    congr 1
    apply Subtype.ext
    exact hconj
  have hkfact : ∀ s : ↥S,
      (∀ t : ↥T, φ s t = t) ∨
        ((∀ t : ↥T, φ s (φ s t) = t) ∧
          ∀ ℓ : ℕ, ℓ.Prime → ℓ ∣ 2 ^ n - 1 →
            ∃ t : ↥T, orderOf t = ℓ ∧ φ s t = t⁻¹) := by
    intro s
    have hord : ∃ k : ℕ, orderOf (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
        ⟨s.1, hsNI s.1 s.2⟩) = 2 ^ k := by
      obtain ⟨k, hk⟩ := hS.isPGroup.exists_orderOf_eq_pow (⟨s.1, s.2⟩ : ↥S)
      have hdvd : orderOf (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
          ⟨s.1, hsNI s.1 s.2⟩) ∣ 2 ^ k := by
        have h1 := orderOf_map_dvd (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I)
          (⟨s.1, hsNI s.1 s.2⟩ : ↥(normalizer (I : Set G)))
        have h2 : orderOf (⟨s.1, hsNI s.1 s.2⟩ : ↥(normalizer (I : Set G))) =
            orderOf (⟨s.1, s.2⟩ : ↥S) := by
          rw [← Subgroup.orderOf_coe (⟨s.1, hsNI s.1 s.2⟩ : ↥(normalizer (I : Set G))),
            ← Subgroup.orderOf_coe (⟨s.1, s.2⟩ : ↥S)]
        rwa [h2, hk] at h1
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
      exact ⟨j, hj⟩
    have hfix0s : ∃ t₀ ∈ T, t₀ ≠ 1 ∧
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
          ⟨s.1, hsNI s.1 s.2⟩) t₀ = t₀ := by
      refine ⟨x0, hx0T, ?_, ?_⟩
      · intro hx; exact ht0ne (Subtype.ext hx)
      · have hsC : s.1 ∈ centralizer (A₀ : Set G) := by
          rw [← h.hH]
          exact hSH s.2
        have hcomm : a₀.1 * s.1 = s.1 * a₀.1 :=
          (Subgroup.mem_centralizer_iff.mp hsC) a₀.1 a₀.2
        have hconj : s.1 * a₀.1 * s.1⁻¹ = a₀.1 := by
          rw [← hcomm]
          group
        unfold x0
        rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
        congr 1
        apply Subtype.ext
        exact hconj
    rcases hK (Bar2 I) n hn3 hnodd hshape T hTz
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨s.1, hsNI s.1 s.2⟩)
        hord (hTmap s) hfix0s with htriv | hrefl
    · left
      intro t
      apply Subtype.ext
      exact htriv t.1 t.2
    · right
      constructor
      · intro t
        apply Subtype.ext
        exact hrefl.1 t.1 t.2
      · intro ℓ hℓ hdvd
        obtain ⟨x, hxT, hxord, hxinv⟩ := hrefl.2 ℓ hℓ hdvd
        refine ⟨⟨x, hxT⟩, ?_, ?_⟩
        · rw [← Subgroup.orderOf_coe]
          exact hxord
        · apply Subtype.ext
          exact hxinv
  have hrdvd2 : r ∣ 2 ^ n - 1 := by
    have hrdvdA : r ∣ (2 ^ n - 1) * (2 ^ n - 1) := by
      simpa [hcardA] using h.ctx22.ctx.hr.2
    exact hr.dvd_of_dvd_pow (by rwa [← pow_two] at hrdvdA)
  let σVs : ↥S → MulAut ↥V := fun s =>
    (((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
        ⟨s.1, hsNI s.1 s.2⟩).subgroupMap V).trans
      (MulEquiv.subgroupCongr (map_powTorsion_rho D h hHI hOleP2
        (hsNE s.1 s.2) (hsNI s.1 s.2))))
  have σVs_coe : ∀ (s : ↥S) (y : ↥V),
      ((σVs s y : ↥V) : Bar2 I) =
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
          ⟨s.1, hsNI s.1 s.2⟩) (y : Bar2 I) := by
    intro s y
    unfold σVs
    calc ((MulEquiv.subgroupCongr (map_powTorsion_rho D h hHI hOleP2
            (hsNE s.1 s.2) (hsNI s.1 s.2)))
          ((MulEquiv.subgroupMap (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
            ⟨s.1, hsNI s.1 s.2⟩) V) y) : Bar2 I)
        = ((MulEquiv.subgroupMap (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
            ⟨s.1, hsNI s.1 s.2⟩) V) y : Bar2 I) :=
          MulEquiv.subgroupCongr_apply _ _
      _ = (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
            ⟨s.1, hsNI s.1 s.2⟩) (y : Bar2 I) :=
          MulEquiv.coe_subgroupMap_apply _ _ _
  have hσVs2 : ∀ (s : ↥S), φ s ≠ 1 → σVs s * σVs s = 1 := by
    intro s hne
    rcases hkfact s with htriv | hrefl
    · refine absurd ?_ hne
      ext t
      exact congrArg Subtype.val (htriv t)
    · ext y
      rw [MulAut.mul_apply, σVs_coe, σVs_coe]
      have h1 : ((φFun s) ((φFun s) ⟨y.1, hVleT y.2⟩) : ↥T) = ⟨y.1, hVleT y.2⟩ := by
        simpa [φ] using hrefl.1 ⟨y.1, hVleT y.2⟩
      have h2 := congrArg Subtype.val h1
      simpa [φFun_coe] using h2
  have hLfixVs : ∀ (s : ↥S) (y : ↥V), y ∈ Lf.subgroupOf V → σVs s y = y := by
    intro s y hy
    apply Subtype.ext
    rw [σVs_coe]
    have hyL : (y : Bar2 I) ∈ Lf := Subgroup.mem_subgroupOf.mp hy
    have h1 : ((φFun s) ⟨y.1, hVleT y.2⟩ : ↥T) = ⟨y.1, hVleT y.2⟩ := by
      simpa [φ] using hLfix s ⟨y.1, hVleT y.2⟩ hyL
    have hv := congrArg Subtype.val h1
    rw [φFun_coe] at hv
    exact hv
  have hσVsne : ∀ (s : ↥S), φ s ≠ 1 → σVs s ≠ 1 := by
    intro s hne h1
    rcases hkfact s with htriv | hrefl
    · refine hne ?_
      ext t
      exact congrArg Subtype.val (htriv t)
    · obtain ⟨t, htord, htinv⟩ := hrefl.2 r hr hrdvd2
      have htord' : orderOf (t : Bar2 I) = r :=
        (Subgroup.orderOf_coe t).trans htord
      have htV : (t : Bar2 I) ∈ V := by
        rw [mem_powTorsionSubgroup]
        exact ⟨t.2, by rw [← orderOf_dvd_iff_pow_eq_one, htord']⟩
      let tV : ↥V := ⟨t.1, htV⟩
      have hfix : σVs s tV = tV := by rw [h1]; rfl
      have hfix' : ((σVs s tV : ↥V) : Bar2 I) = (tV : Bar2 I) :=
        congrArg Subtype.val hfix
      rw [σVs_coe] at hfix'
      have hinv : (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
          ⟨s.1, hsNI s.1 s.2⟩) (t : Bar2 I) = (t : Bar2 I)⁻¹ := by
        have h := congrArg Subtype.val htinv
        change ((φFun s) t : ↥T).1 = ((t⁻¹ : ↥T) : Bar2 I) at h
        rw [φFun_coe] at h
        simpa using h
      rw [hinv] at hfix'
      have h2 : (t : Bar2 I) ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [← hfix']
        exact mul_inv_cancel _
      have hdvd : orderOf (t : Bar2 I) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
      have hdvd' : r ∣ 2 := by rwa [htord'] at hdvd
      have hrle : r ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd'
      exact hr2 (le_antisymm hrle hr.two_le)
  have hLvcard : Nat.card (Lf.subgroupOf V) = r := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hLV).toEquiv, hLcard]
  have hLvquot : Nat.card (↥V ⧸ (Lf.subgroupOf V)) = r := by
    rw [← Subgroup.index_eq_card]
    have h := Subgroup.index_mul_card (Lf.subgroupOf V)
    rw [hLvcard, hVcard, pow_two] at h
    exact Nat.eq_of_mul_eq_mul_right hr.pos h
  have hmapLv : ∀ s : ↥S, (Lf.subgroupOf V).map (σVs s).toMonoidHom =
      Lf.subgroupOf V := by
    intro s
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro x ⟨y, hy, rfl⟩
      have hfix := hLfixVs s y hy
      simpa [hfix] using hy
    · exact le_of_eq (Subgroup.card_map_of_injective
        (f := (σVs s).toMonoidHom) (σVs s).injective).symm
  have hqinv : ∀ (s : ↥S), φ s ≠ 1 →
      ∀ x : ↥V ⧸ (Lf.subgroupOf V),
        (QuotientGroup.congr (Lf.subgroupOf V) (Lf.subgroupOf V)
          (σVs s) (hmapLv s)) x = x⁻¹ := by
    intro s hne
    exact congr_eq_inv_of_fixed_of_ne_one hr hr2 hLvcard hLvquot (σVs s)
      (hσVs2 s hne) (hLfixVs s) (hσVsne s hne) (hmapLv s)
  have hordOf : ∀ s : ↥S, ∃ k : ℕ, orderOf
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
        ⟨s.1, hsNI s.1 s.2⟩) = 2 ^ k := by
    intro s
    obtain ⟨k, hk⟩ := hS.isPGroup.exists_orderOf_eq_pow (⟨s.1, s.2⟩ : ↥S)
    have hdvd : orderOf (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
        ⟨s.1, hsNI s.1 s.2⟩) ∣ 2 ^ k := by
      have h1 := orderOf_map_dvd (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I)
        (⟨s.1, hsNI s.1 s.2⟩ : ↥(normalizer (I : Set G)))
      have h2 : orderOf (⟨s.1, hsNI s.1 s.2⟩ : ↥(normalizer (I : Set G))) =
          orderOf (⟨s.1, s.2⟩ : ↥S) := by
        rw [← Subgroup.orderOf_coe (⟨s.1, hsNI s.1 s.2⟩ : ↥(normalizer (I : Set G))),
          ← Subgroup.orderOf_coe (⟨s.1, s.2⟩ : ↥S)]
      rwa [h2, hk] at h1
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    exact ⟨j, hj⟩
  have hfix0Of : ∀ s : ↥S, ∃ t ∈ T, t ≠ 1 ∧
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
        ⟨s.1, hsNI s.1 s.2⟩) t = t := by
    intro s
    refine ⟨x0, hx0T, ?_, ?_⟩
    · intro hx; exact ht0ne (Subtype.ext hx)
    · have h := congrArg Subtype.val (hfix0 s)
      change ((φFun s) t0 : ↥T).1 = x0 at h
      rw [φFun_coe] at h
      exact h
  have atMostOne : ∀ a b : ↥S, φ a ≠ 1 → φ b ≠ 1 → φ a = φ b := by
    intro a b ha hb
    rcases hkfact a with ha_triv | ha_refl
    · refine absurd ?_ ha
      ext t
      exact congrArg Subtype.val (ha_triv t)
    rcases hkfact b with hb_triv | hb_refl
    · refine absurd ?_ hb
      ext t
      exact congrArg Subtype.val (hb_triv t)
    have hφa2 : φ a * φ a = 1 := by
      ext t
      simpa using congrArg Subtype.val (ha_refl.1 t)
    have hφb2 : φ b * φ b = 1 := by
      ext t
      simpa using congrArg Subtype.val (hb_refl.1 t)
    let c : ↥S := a * b
    have hcφ : φ c = φ a * φ b := by
      change φ (a * b) = φ a * φ b
      exact map_mul φ a b
    rcases hK (Bar2 I) n hn3 hnodd hshape T hTz
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨c.1, hsNI c.1 c.2⟩)
        (hordOf c) (hTmap c) (hfix0Of c) with hc_triv | hc_refl
    · have hc1 : φ c = 1 := by
        ext t
        exact hc_triv t.1 t.2
      have hprod : φ a * φ b = 1 := by rw [← hcφ, hc1]
      calc φ a = φ a * 1 := by rw [mul_one]
        _ = φ a * (φ b * φ b) := by rw [hφb2]
        _ = (φ a * φ b) * φ b := by group
        _ = 1 * φ b := by rw [hprod]
        _ = φ b := by rw [one_mul]
    · exfalso
      let Vc : MulAut ↥V := σVs c
      have hVc2 : Vc * Vc = 1 := by
        ext y
        rw [MulAut.mul_apply, σVs_coe, σVs_coe]
        have h1 : ((φFun c) ((φFun c) ⟨y.1, hVleT y.2⟩) : ↥T) = ⟨y.1, hVleT y.2⟩ := by
          apply Subtype.ext
          have h := hc_refl.1 (y : Bar2 I) (hVleT y.2)
          change ((φFun c) ((φFun c) ⟨y.1, hVleT y.2⟩) : ↥T).1 = (y : Bar2 I)
          simpa [φFun_coe] using h
        have h2 := congrArg Subtype.val h1
        simpa [φFun_coe] using h2
      have hVcfix : ∀ y ∈ Lf.subgroupOf V, Vc y = y := by
        intro y hy
        exact hLfixVs c y hy
      have hquotc : ∀ x : ↥V, QuotientGroup.mk' (Lf.subgroupOf V) (Vc x) =
          QuotientGroup.mk' (Lf.subgroupOf V) x := by
        intro x
        have hσc_eq : Vc x = σVs a (σVs b x) := by
          change (σVs c) x = σVs a (σVs b x)
          apply Subtype.ext
          rw [σVs_coe, σVs_coe, σVs_coe]
          change (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
              ⟨c.1, hsNI c.1 c.2⟩) (x : Bar2 I) =
            (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
              ⟨a.1, hsNI a.1 a.2⟩) ((CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
              ⟨b.1, hsNI b.1 b.2⟩) (x : Bar2 I))
          have hc : (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
              ⟨c.1, hsNI c.1 c.2⟩) =
              CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨a.1, hsNI a.1 a.2⟩ *
                CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨b.1, hsNI b.1 b.2⟩ := by
            rw [← map_mul]
            congr 1
          rw [hc]
          rfl
        rw [hσc_eq]
        have hbq : QuotientGroup.mk' (Lf.subgroupOf V) (σVs b x) =
            (QuotientGroup.mk' (Lf.subgroupOf V) x)⁻¹ := by
          change QuotientGroup.mk (σVs b x) = (QuotientGroup.mk x)⁻¹
          rw [← QuotientGroup.congr_mk (Lf.subgroupOf V) (Lf.subgroupOf V)
            (σVs b) (hmapLv b) x]
          exact hqinv b hb _
        have haq : QuotientGroup.mk' (Lf.subgroupOf V) (σVs a (σVs b x)) =
            (QuotientGroup.mk' (Lf.subgroupOf V) (σVs b x))⁻¹ := by
          change QuotientGroup.mk (σVs a (σVs b x)) = (QuotientGroup.mk (σVs b x))⁻¹
          rw [← QuotientGroup.congr_mk (Lf.subgroupOf V) (Lf.subgroupOf V)
            (σVs a) (hmapLv a) (σVs b x)]
          exact hqinv a ha _
        rw [haq, hbq, inv_inv]
      have hVc1 : Vc = 1 :=
        eq_one_of_involution_of_quotient_fixed hr hr2 hLvcard Vc hVc2 hVcfix hquotc
      obtain ⟨t, htT, htord, htinv⟩ := hc_refl.2 r hr hrdvd2
      have htV : t ∈ V := by
        rw [mem_powTorsionSubgroup]
        exact ⟨htT, by rw [← orderOf_dvd_iff_pow_eq_one, htord]⟩
      let tV : ↥V := ⟨t, htV⟩
      have hσt : σVs c tV = tV := by
        change Vc tV = tV
        rw [hVc1]
        rfl
      have hinv : (σVs c) tV = tV⁻¹ := by
        apply Subtype.ext
        rw [σVs_coe]
        have h := htinv
        change ((φFun c) ⟨t, htT⟩ : ↥T).1 = ((⟨t, htT⟩⁻¹ : ↥T) : Bar2 I) at h
        rw [φFun_coe] at h
        simpa using h
      rw [hσt] at hinv
      have h2 : (tV : ↥V) ^ 2 = 1 := by
        rw [pow_two]
        nth_rewrite 2 [hinv]
        exact mul_inv_cancel _
      have htVord : orderOf tV = r := by
        rw [← Subgroup.orderOf_coe tV]
        simpa [tV] using htord
      have hdvd : r ∣ 2 := by
        have := orderOf_dvd_of_pow_eq_one h2
        rwa [htVord] at this
      have hrle : r ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd
      exact hr2 (le_antisymm hrle hr.two_le)
  have hrange_le_two : Nat.card φ.range ≤ 2 := by
    apply card_le_two_of_forall_eq_of_ne_one
    intro σ τ hσ hτ
    obtain ⟨a, hσa⟩ := MonoidHom.mem_range.mp σ.2
    obtain ⟨b, hτb⟩ := MonoidHom.mem_range.mp τ.2
    have hσ' : φ a ≠ 1 := by
      intro h
      apply hσ
      apply Subtype.ext
      change σ.1 = 1
      rw [← hσa]
      exact h
    have hτ' : φ b ≠ 1 := by
      intro h
      apply hτ
      apply Subtype.ext
      change τ.1 = 1
      rw [← hτb]
      exact h
    apply Subtype.ext
    rw [← hσa, ← hτb]
    exact atMostOne a b hσ' hτ'
  have hAnormO : A ≤ normalizer (O : Set G) :=
    (le_inf hAH hAI).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (H ⊓ I))
  have hAnormP2 : A ≤ normalizer (P2 : Set G) :=
    hAI.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 I)
  have hAinfP2 : A ⊓ P2 = ⊥ := inf_pCoreOf_eq_bot_of_odd (I := I) hAodd
  have hAOinter : (A ⊔ O) ⊓ P2 = O :=
    sup_inter_pCore_eq hAnormO hOleP2 hAnormP2 hAinfP2
  have hker_eq : φ.ker = (S ⊓ ⨅ a ∈ A, centModEl O a).subgroupOf S := by
    ext s
    constructor
    · intro hs
      have hφs : φ s = 1 := MonoidHom.mem_ker.mp hs
      refine Subgroup.mem_subgroupOf.mpr ⟨s.2, ?_⟩
      change s.1 ∈ ⨅ a ∈ A, centModEl O a
      rw [Subgroup.mem_iInf]
      intro a
      rw [Subgroup.mem_iInf]
      intro ha
      have hsNO : s.1 ∈ normalizer (O : Set G) :=
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.normalizer_le_normalizer_pCoreOf (H ⊓ I))
          (by simpa [O] using hsNE s.1 s.2)
      refine ⟨hsNO, ?_⟩
      have hcommHI : s.1 * a * s.1⁻¹ * a⁻¹ ∈ H ⊓ I := by
        constructor
        · exact H.mul_mem (H.mul_mem (H.mul_mem (hSH s.2) (hAH ha)) (H.inv_mem (hSH s.2)))
            (H.inv_mem (hAH ha))
        · have hsI : s.1 ∈ normalizer (I : Set G) := hsNI s.1 s.2
          have hsa : s.1 * a * s.1⁻¹ ∈ I :=
            (Subgroup.mem_normalizer_iff.mp hsI a).mp (hAI ha)
          exact I.mul_mem hsa (I.inv_mem (hAI ha))
      have hcommP : s.1 * a * s.1⁻¹ * a⁻¹ ∈ P2 := by
        have haT : QuotientGroup.mk' (CFSG.pCore 2 ↥I) (⟨a, hAI ha⟩ : ↥I) ∈ T := by
          change QuotientGroup.mk' (CFSG.pCore 2 ↥I) (⟨a, hAI ha⟩ : ↥I) ∈ barImage (IOf D p L) A
          exact Subgroup.mem_map.mpr ⟨⟨a, hAI ha⟩, by
            rw [Subgroup.mem_subgroupOf]; exact ha, rfl⟩
        have hφfix : (φ s) ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥I) (⟨a, hAI ha⟩ : ↥I), haT⟩ =
            ⟨QuotientGroup.mk' (CFSG.pCore 2 ↥I) (⟨a, hAI ha⟩ : ↥I), haT⟩ := by
          rw [hφs]
          rfl
        have hfixval := congrArg Subtype.val hφfix
        change (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
            ⟨s.1, hsNI s.1 s.2⟩) (QuotientGroup.mk' (CFSG.pCore 2 ↥I) (⟨a, hAI ha⟩ : ↥I)) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥I) (⟨a, hAI ha⟩ : ↥I) at hfixval
        exact (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff I
          ⟨s.1, hsNI s.1 s.2⟩ (⟨a, hAI ha⟩ : ↥I)).1 hfixval
      have hcommAO : s.1 * a * s.1⁻¹ * a⁻¹ ∈ A ⊔ O := by
        rwa [hHI] at hcommHI
      have hcommO : s.1 * a * s.1⁻¹ * a⁻¹ ∈ O := by
        have h : s.1 * a * s.1⁻¹ * a⁻¹ ∈ (A ⊔ O) ⊓ P2 := ⟨hcommAO, hcommP⟩
        rwa [hAOinter] at h
      exact hcommO
    · intro hs
      obtain ⟨hsS, hsInf⟩ := Subgroup.mem_subgroupOf.mp hs
      change s.1 ∈ ⨅ a ∈ A, centModEl O a at hsInf
      apply MonoidHom.mem_ker.mpr
      ext t
      obtain ⟨a, ha, hya⟩ := Subgroup.mem_map.mp t.2
      have haA : (a : G) ∈ A := Subgroup.mem_subgroupOf.mp ha
      have hcommO : s.1 * (a : G) * s.1⁻¹ * (a : G)⁻¹ ∈ O := by
        have h1 := (Subgroup.mem_iInf.mp hsInf) (a : G)
        exact ((Subgroup.mem_iInf.mp h1) haA).2
      have hcommP : s.1 * (a : G) * s.1⁻¹ * (a : G)⁻¹ ∈ P2 := hOleP2 hcommO
      have hfixa : (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I
          ⟨s.1, hsNI s.1 s.2⟩) (QuotientGroup.mk' (CFSG.pCore 2 ↥I) a) =
          QuotientGroup.mk' (CFSG.pCore 2 ↥I) a :=
        (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff I
          ⟨s.1, hsNI s.1 s.2⟩ a).2 hcommP
      change ((φFun s) t : ↥T).1 = (t : Bar2 I)
      rw [φFun_coe, ← hya]
      exact hfixa
  have hidxK : φ.ker.index ≤ 2 := by
    apply CFSG.LocalAnalysis.ComponentInitial.index_le_two_of_inv_mul_mem
    intro a b ha hb
    have ha' : φ a ≠ 1 := fun h => ha (MonoidHom.mem_ker.mpr h)
    have hb' : φ b ≠ 1 := fun h => hb (MonoidHom.mem_ker.mpr h)
    have hab : φ a = φ b := atMostOne a b ha' hb'
    rw [MonoidHom.mem_ker]
    calc φ (a⁻¹ * b) = (φ a)⁻¹ * φ b := by rw [map_mul, map_inv]
      _ = (φ a)⁻¹ * φ a := by rw [hab]
      _ = 1 := inv_mul_cancel _
  rw [Subgroup.relIndex]
  rw [← hker_eq]
  exact hidxK

theorem trichotomy19_28_of_torusAutomizer (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h25 : R19_25At D V₀ V p L A t B r A₀ H h)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h)
    (hshape : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∨ IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L))
    (hK : K_19_28_torusAutomizer) :
    Trichotomy19_28 D V₀ V p L A t B r A₀ H h h25 h26 := by
  intro S hS hidx
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let I : Subgroup G := IOf D p L
  let X : Subgroup G := A ⊔ S
  let Q : Subgroup G := pCoreOf 2 X
  let Z : Subgroup G := (Subgroup.center ↥Q).map Q.subtype
  let ZS : Subgroup G := (Subgroup.center ↥S).map S.subtype
  have hAI : A ≤ I := h.ctx22.ctx.hA
  have hAM : A ≤ D.M := A_le_M_of_ctx19_10 D h.ctx22.ctx
  have hIM : I ≤ D.M := IOf_le_M D p h.ctx22.ctx.hyp.hL.1.1.le
  have hSM : S ≤ D.M := hS.le.trans inf_le_right
  have hSH : S ≤ H := hS.le.trans inf_le_left
  have hAX : A ≤ X := le_sup_left
  have hSX : S ≤ X := le_sup_right
  have hXHM : X ≤ H ⊓ D.M :=
    sup_le (le_inf (A_le_H_of_ctx19_23 h) hAM) (le_inf hSH hSM)
  have hSylX : CFSG.ABGLocalTools.IsSylowOf 2 S X := hS.of_le hSX hXHM
  have hQleS : Q ≤ S :=
    CFSG.LocalAnalysis.RankThreeUC.Section12.IntermediateSylow.pCoreOf_le_sylow hSylX
  have hQleX : Q ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hXleNQ : X ≤ Subgroup.normalizer (Q : Set G) := by
    simpa [Q] using CFSG.RankThreeCoreUniqueness.Helpers.localGroup_le_normalizer_pCoreOf 2 X
  by_cases hq1 : Q.relIndex S = 1
  · have hSleQ : S ≤ Q := Subgroup.relIndex_eq_one.mp hq1
    have hQeqS : Q = S := le_antisymm hQleS hSleQ
    have hXleNS : X ≤ Subgroup.normalizer (S : Set G) := by
      simpa [hQeqS] using hXleNQ
    have hZSleX : ZS ≤ X :=
      (Subgroup.map_subtype_le (Subgroup.center ↥S)).trans hSX
    refine Or.inl ?_
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hZSleX]
    exact hXleNS.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic
        (Subgroup.center ↥S))
  · have hq2 : Q.relIndex S = 2 := by
      set k := Q.relIndex S with hk
      have hpos : 0 < k := by
        rw [hk]
        exact Nat.pos_of_ne_zero (by
          rw [Subgroup.relIndex]
          exact Subgroup.index_ne_zero_of_finite)
      have hle : k ≤ 2 := by rw [hk]; exact hidx
      have hne : k ≠ 1 := by rw [hk]; exact hq1
      have hk2 : k = 2 := by interval_cases k <;> simp_all
      exact hk2
    obtain ⟨s, hsS, hsQ, hsN, hs2Q, _, hcase⟩ :=
      exists_s_trichotomy_of_ctx19_23 D h h25 h26 S hS hq2
    simp only [] at hcase
    rcases hcase with hZSnorm | hJnorm | hthird
    · exact Or.inl hZSnorm
    · exact Or.inr (Or.inl hJnorm)
    · obtain ⟨hZB, hZSnormal_of_le, hQB_of_notle, hB1Z⟩ := hthird
      by_cases hZSleQ : ZS ≤ Q
      · exact Or.inl (hZSnormal_of_le hZSleQ)
      · have hQB : ⁅Q, ⁅A, Subgroup.zpowers s⁆⁆ = ⊥ := hQB_of_notle hZSleQ
        by_cases hB1 : ⁅A, Subgroup.zpowers s⁆ = ⊥
        · exact Or.inl (hB1Z hB1)
        ·
          have hAodd : Odd (Nat.card A) := odd_card_of_ctx19_10 h.ctx22.ctx
          haveI hAcomm : IsMulCommutative ↥A :=
            isMulCommutative_of_isZModSq h.ctx22.ctx.hAcard
          let n : ℕ := S17.nOf L
          have hnodd : Odd n := h26
          have hr : r.Prime := h.ctx22.ctx.hr.1
          have hr2 : r ≠ 2 := by
            intro h2
            exact hAodd.not_two_dvd_nat (h2 ▸ h.ctx22.ctx.hr.2)
          have hcardA : Nat.card A = (2 ^ n - 1) * (2 ^ n - 1) :=
            card_eq_of_isZModSq h.ctx22.ctx.hAcard
          have hn3 : 3 ≤ n := three_le_nOf_of_setting1910 h.ctx22.ctx.h1910
          have hrdvd2 : r ∣ 2 ^ n - 1 := by
            have hrdvdA : r ∣ (2 ^ n - 1) * (2 ^ n - 1) := by
              simpa [hcardA] using h.ctx22.ctx.hr.2
            exact hr.dvd_of_dvd_pow (by rwa [← pow_two] at hrdvdA)
          have hsNI : s ∈ Subgroup.normalizer (I : Set G) :=
            le_normalizer_IOf D h.ctx22.ctx.hyp.hL.1 (hSM hsS)
          let T : Subgroup (Bar2 I) := barImage (IOf D p L) A
          have hTz : IsZModSq T n := isZModSq_torusImage D h.ctx22.ctx
          let σ : MulAut (Bar2 I) :=
            CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨s, hsNI⟩
          have hTmap : T.map σ.toMonoidHom = T := by
            apply Subgroup.eq_of_le_of_card_ge
            · rintro y ⟨x, hx, rfl⟩
              obtain ⟨aI, haI, rfl⟩ := Subgroup.mem_map.mp hx
              have haA : (aI : G) ∈ A := Subgroup.mem_subgroupOf.mp haI
              have hconjA : s * (aI : G) * s⁻¹ ∈ A :=
                (Subgroup.mem_normalizer_iff.mp hsN aI).mp haA
              have hconjI : s * (aI : G) * s⁻¹ ∈ I := hAI hconjA
              refine Subgroup.mem_map.mpr ⟨⟨s * (aI : G) * s⁻¹, hconjI⟩, ?_, ?_⟩
              · rw [Subgroup.mem_subgroupOf]
                exact hconjA
              · change (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨s, hsNI⟩)
                    (QuotientGroup.mk aI) =
                  QuotientGroup.mk (⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I)
                rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
                congr 1
            · rw [Subgroup.card_map_of_injective (f := σ.toMonoidHom) σ.injective]
          have hordσ : ∃ k : ℕ, orderOf σ = 2 ^ k := by
            obtain ⟨k, hk⟩ := hS.isPGroup.exists_orderOf_eq_pow (⟨s, hsS⟩ : ↥S)
            have hdvd : orderOf σ ∣ 2 ^ k := by
              have h1 := orderOf_map_dvd
                (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I)
                (⟨s, hsNI⟩ : ↥(Subgroup.normalizer (I : Set G)))
              have h2 : orderOf (⟨s, hsNI⟩ : ↥(Subgroup.normalizer (I : Set G))) =
                  orderOf (⟨s, hsS⟩ : ↥S) := by
                rw [← Subgroup.orderOf_coe
                    (⟨s, hsNI⟩ : ↥(Subgroup.normalizer (I : Set G))),
                  ← Subgroup.orderOf_coe (⟨s, hsS⟩ : ↥S)]
              rwa [h2, hk] at h1
            obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
            exact ⟨j, hj⟩
          have hA₀I : A₀ ≤ I := h.ctx22.hA₀.trans hAI
          have hA₀nt : Nontrivial ↥A₀ := by
            apply Finite.one_lt_card_iff_nontrivial.mp
            rw [h.ctx22.hcard]
            exact hr.one_lt
          obtain ⟨a₀, ha₀ne⟩ := exists_ne (1 : ↥A₀)
          let x0 : Bar2 I := QuotientGroup.mk (⟨a₀.1, hA₀I a₀.2⟩ : ↥I)
          have hx0T : x0 ∈ T := by
            change x0 ∈ barImage (IOf D p L) A
            refine Subgroup.mem_map.mpr ⟨⟨a₀.1, hAI (h.ctx22.hA₀ a₀.2)⟩, ?_, ?_⟩
            · rw [Subgroup.mem_subgroupOf]
              exact h.ctx22.hA₀ a₀.2
            · rfl
          have ht0ne : x0 ≠ 1 := by
            intro hx1
            have hmemN : (⟨a₀.1, hA₀I a₀.2⟩ : ↥I) ∈ CFSG.pCore 2 ↥I := by
              have hq : QuotientGroup.mk' (CFSG.pCore 2 ↥I)
                  (⟨a₀.1, hA₀I a₀.2⟩ : ↥I) = 1 := by
                simpa [x0] using hx1
              exact (QuotientGroup.eq_one_iff _).1 hq
            have hmemP : (a₀.1 : G) ∈ pCoreOf 2 I :=
              Subgroup.mem_map_of_mem I.subtype hmemN
            have hbot : (a₀.1 : G) ∈ (⊥ : Subgroup G) := by
              rw [← inf_pCoreOf_eq_bot_of_odd (I := I) hAodd]
              exact ⟨h.ctx22.hA₀ a₀.2, hmemP⟩
            exact ha₀ne (Subtype.ext (Subgroup.mem_bot.mp hbot))
          have hfix0s : ∃ t₀ ∈ T, t₀ ≠ 1 ∧ σ t₀ = t₀ := by
            refine ⟨x0, hx0T, ht0ne, ?_⟩
            have hsC : s ∈ centralizer (A₀ : Set G) := by
              rw [← h.hH]
              exact hSH hsS
            have hcomm : a₀.1 * s = s * a₀.1 :=
              (Subgroup.mem_centralizer_iff.mp hsC) a₀.1 a₀.2
            have hconj : s * a₀.1 * s⁻¹ = a₀.1 := by
              rw [← hcomm]
              group
            change (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨s, hsNI⟩) x0 = x0
            unfold x0
            rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
            congr 1
            apply Subtype.ext
            exact hconj
          rcases hK (Bar2 I) n hn3 hnodd (by simpa [n] using hshape) T hTz σ hordσ
            hTmap hfix0s with htriv | hrefl
          ·
            have hB0bot : ⁅A, Subgroup.zpowers s⁆ = ⊥ := by
              rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
              intro a ha
              rw [Subgroup.mem_centralizer_iff]
              intro y hy
              obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
              have hcomm : Commute a s := by
                rw [commute_iff_eq]
                have hfix : σ (QuotientGroup.mk' (CFSG.pCore 2 ↥I)
                    (⟨a, hAI ha⟩ : ↥I)) =
                    QuotientGroup.mk' (CFSG.pCore 2 ↥I) (⟨a, hAI ha⟩ : ↥I) :=
                  htriv _ (Subgroup.mem_map.mpr ⟨⟨a, hAI ha⟩, by
                    rw [Subgroup.mem_subgroupOf]; exact ha, rfl⟩)
                have hmem := (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff I
                  ⟨s, hsNI⟩ (⟨a, hAI ha⟩ : ↥I)).1 hfix
                have hmemA : s * a * s⁻¹ * a⁻¹ ∈ A := by
                  have h1 : s * a * s⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hsN a).mp ha
                  exact A.mul_mem h1 (A.inv_mem ha)
                have hbot : s * a * s⁻¹ * a⁻¹ ∈ (⊥ : Subgroup G) := by
                  rw [← inf_pCoreOf_eq_bot_of_odd (I := I) hAodd]
                  exact ⟨hmemA, hmem⟩
                have hone : s * a * s⁻¹ * a⁻¹ = 1 := Subgroup.mem_bot.mp hbot
                have h1 : s * a * s⁻¹ = a := by
                  have h := congrArg (fun z => z * a) hone
                  simpa [mul_assoc] using h
                have hsa : s * a = a * s := by
                  have h := congrArg (fun z => z * s) h1
                  simpa [mul_assoc] using h
                exact hsa.symm
              exact (hcomm.zpow_right k).eq.symm
            exact Or.inl (hB1Z hB0bot)
          ·
            obtain ⟨x, hxT, hxord, hxinv⟩ := hrefl.2 r hr hrdvd2
            obtain ⟨aI, haI, hxeq⟩ := Subgroup.mem_map.mp hxT
            have haA : (aI : G) ∈ A := Subgroup.mem_subgroupOf.mp haI
            have hconjA : s * (aI : G) * s⁻¹ ∈ A :=
              (Subgroup.mem_normalizer_iff.mp hsN aI).mp haA
            have hconjI : s * (aI : G) * s⁻¹ ∈ I := hAI hconjA
            have hpow : aI ^ r = 1 := by
              apply Subtype.ext
              have hmap : QuotientGroup.mk' (CFSG.pCore 2 ↥I) (aI ^ r) = 1 := by
                rw [map_pow]
                calc (QuotientGroup.mk' (CFSG.pCore 2 ↥I) aI) ^ r = x ^ r := by rw [hxeq]
                  _ = 1 := by simpa [hxord] using pow_orderOf_eq_one x
              have hmemN : aI ^ r ∈ CFSG.pCore 2 ↥I :=
                (QuotientGroup.eq_one_iff _).1 hmap
              have hmemP : ((aI ^ r : ↥I) : G) ∈ pCoreOf 2 I :=
                Subgroup.mem_map_of_mem I.subtype hmemN
              have hmemA : ((aI ^ r : ↥I) : G) ∈ A := by
                simpa using A.pow_mem haA r
              have hbot : ((aI ^ r : ↥I) : G) ∈ (⊥ : Subgroup G) := by
                rw [← inf_pCoreOf_eq_bot_of_odd (I := I) hAodd]
                exact ⟨hmemA, hmemP⟩
              simpa using Subgroup.mem_bot.mp hbot
            have hdivd : orderOf aI ∣ r := orderOf_dvd_iff_pow_eq_one.mpr hpow
            have hrdvd : r ∣ orderOf aI := by
              have h1 := orderOf_map_dvd
                (QuotientGroup.mk' (CFSG.pCore 2 ↥I)) aI
              rwa [hxeq, hxord] at h1
            have haIord : orderOf aI = r := Nat.dvd_antisymm hdivd hrdvd
            let a : G := (aI : G)
            have haA : a ∈ A := haA
            have haord : orderOf a = r := by
              dsimp [a]
              exact (Subgroup.orderOf_coe aI).trans haIord
            have hinv_a : s * a * s⁻¹ = a⁻¹ := by
              have hinv_q : QuotientGroup.mk' (CFSG.pCore 2 ↥I)
                  (⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I) =
                  (QuotientGroup.mk' (CFSG.pCore 2 ↥I) aI)⁻¹ := by
                rw [← hxeq] at hxinv
                have hsub : (Subgroup.normalizerMonoidHom I ⟨s, hsNI⟩ aI) =
                    (⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I) := by
                  apply Subtype.ext
                  rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk_coe]
                rw [show (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL I ⟨s, hsNI⟩)
                      (QuotientGroup.mk' (CFSG.pCore 2 ↥I) aI) =
                    QuotientGroup.mk' (CFSG.pCore 2 ↥I)
                      (Subgroup.normalizerMonoidHom I ⟨s, hsNI⟩ aI) from
                  CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk I ⟨s, hsNI⟩ aI] at hxinv
                simpa [hsub] using hxinv
              have hmemN : (⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I) / aI⁻¹ ∈
                  CFSG.pCore 2 ↥I :=
                (QuotientGroup.eq_iff_div_mem).1 hinv_q
              have hmemP : (((⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I) / aI⁻¹ : ↥I) : G) ∈
                  pCoreOf 2 I :=
                Subgroup.mem_map_of_mem I.subtype hmemN
              have hmemA : (((⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I) / aI⁻¹ : ↥I) : G) ∈ A := by
                have h1 : s * (aI : G) * s⁻¹ ∈ A := hconjA
                have h2 : (aI : G)⁻¹ ∈ A := A.inv_mem haA
                have heqdiv : (((⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I) / aI⁻¹ : ↥I) : G) =
                    (s * (aI : G) * s⁻¹) * (aI : G) := by
                  rw [Subgroup.coe_div, Subgroup.coe_inv, div_eq_mul_inv, inv_inv]
                rw [heqdiv]
                exact A.mul_mem h1 haA
              have hbot : (((⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I) / aI⁻¹ : ↥I) : G) ∈
                  (⊥ : Subgroup G) := by
                rw [← inf_pCoreOf_eq_bot_of_odd (I := I) hAodd]
                exact ⟨hmemA, hmemP⟩
              have hone : (((⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I) / aI⁻¹ : ↥I) : G) = 1 :=
                Subgroup.mem_bot.mp hbot
              have heq : (s * (aI : G) * s⁻¹) * (aI : G) = 1 := by
                have heqdiv : (((⟨s * (aI : G) * s⁻¹, hconjI⟩ : ↥I) / aI⁻¹ : ↥I) : G) =
                    (s * (aI : G) * s⁻¹) * (aI : G) := by
                  rw [Subgroup.coe_div, Subgroup.coe_inv, div_eq_mul_inv, inv_inv]
                rw [← heqdiv]
                exact hone
              dsimp [a]
              exact eq_inv_of_mul_eq_one_left heq
            have hB0mem : a ∈ ⁅A, Subgroup.zpowers s⁆ :=
              CFSG.GH74.Uniqueness.SecGap.mem_commutator_of_inverted haA hinv_a
                (Odd.of_dvd_nat hAodd (Subgroup.orderOf_dvd_natCard A haA))
            have hQleS : Q ≤ S := hQleS
            have hQleCA₀ : Q ≤ Subgroup.centralizer (A₀ : Set G) := by
              intro q hq
              rw [Subgroup.mem_centralizer_iff]
              intro x hx
              have hsC : S ≤ Subgroup.centralizer (A₀ : Set G) := by
                rw [← h.hH]
                exact hSH
              exact Subgroup.mem_centralizer_iff.mp (hsC (hQleS hq)) x hx
            have hQlea : Q ≤ Subgroup.centralizer (Subgroup.zpowers a : Set G) := by
              have hQBs : ⁅⁅A, Subgroup.zpowers s⁆, Q⁆ = ⊥ := by
                rwa [Subgroup.commutator_comm]
              have hBleC : ⁅A, Subgroup.zpowers s⁆ ≤
                  Subgroup.centralizer (Q : Set G) :=
                Subgroup.commutator_eq_bot_iff_le_centralizer.mp hQBs
              intro q hq
              rw [Subgroup.mem_centralizer_iff]
              intro y hy
              have hyB : y ∈ ⁅A, Subgroup.zpowers s⁆ := by
                have hya : y ∈ Subgroup.zpowers a := hy
                exact (Subgroup.zpowers_le.mpr hB0mem) hya
              exact (Subgroup.mem_centralizer_iff.mp (hBleC hyB) q hq).symm
            let E : Subgroup G := A₀ ⊔ Subgroup.zpowers a
            have hEA : E ≤ A :=
              sup_le h.ctx22.hA₀ (Subgroup.zpowers_le.mpr haA)
            have hA₀el : IsElemAbelian r A₀ := by
              refine ⟨?_, ?_⟩
              · rw [isMulCommutative_iff]
                intro x y
                apply Subtype.ext
                have hxA : (x : G) ∈ A := h.ctx22.hA₀ x.2
                have hyA : (y : G) ∈ A := h.ctx22.hA₀ y.2
                simpa using congrArg Subtype.val
                  ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨x, hxA⟩ ⟨y, hyA⟩)
              · intro x hx
                have hxr : orderOf x ∣ r :=
                  (Subgroup.orderOf_dvd_natCard A₀ hx).trans (by rw [h.ctx22.hcard])
                exact orderOf_dvd_iff_pow_eq_one.mp hxr
            have har : a ^ r = 1 := by
              simpa [haord] using pow_orderOf_eq_one a
            have hael : IsElemAbelian r (Subgroup.zpowers a) :=
              CFSG.Open.isElemAbelian_zpowers har
            have hEel : IsElemAbelian r E :=
              CFSG.Open.IsElemAbelian.sup_of_commute hA₀el hael (fun x hx y hy => by
                have hxA : x ∈ A := h.ctx22.hA₀ hx
                have hyA : y ∈ A := Subgroup.zpowers_le.mpr haA hy
                simpa using congrArg Subtype.val
                  ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨x, hxA⟩ ⟨y, hyA⟩))
            have hdisj : A₀ ⊓ Subgroup.zpowers a = ⊥ := by
              rw [eq_bot_iff]
              intro x hx
              obtain ⟨hxA₀, hxzp⟩ := Subgroup.mem_inf.mp hx
              have hsC : s ∈ Subgroup.centralizer (A₀ : Set G) := by
                rw [← h.hH]
                exact hSH hsS
              have hcomm : x * s = s * x :=
                (Subgroup.mem_centralizer_iff.mp hsC) x hxA₀
              have hfix : s * x * s⁻¹ = x := by
                rw [← hcomm]
                group
              obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxzp
              have hinvx : s * x * s⁻¹ = x⁻¹ := by
                rw [← hk]
                calc s * a ^ k * s⁻¹ = (s * a * s⁻¹) ^ k := by
                      rw [show s * a ^ k * s⁻¹ = (MulAut.conj s) (a ^ k) from rfl]
                      rw [map_zpow]
                      rfl
                  _ = (a⁻¹) ^ k := by rw [hinv_a]
                  _ = (a ^ k)⁻¹ := by rw [inv_zpow]
              have hxx : x = x⁻¹ := hfix.symm.trans hinvx
              have hx2 : x * x = 1 := by
                nth_rewrite 2 [hxx]
                exact mul_inv_cancel x
              have hodd : Odd (orderOf x) := by
                have hxr : orderOf x ∣ r :=
                  (Subgroup.orderOf_dvd_natCard A₀ hxA₀).trans (by rw [h.ctx22.hcard])
                exact hr.odd_of_ne_two hr2 |>.of_dvd_nat hxr
              have hord2 : orderOf x ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
              have hone : orderOf x = 1 := Nat.eq_one_of_dvd_coprimes
                (Nat.coprime_two_right.mpr hodd) dvd_rfl hord2
              exact Subgroup.mem_bot.mp (orderOf_eq_one_iff.mp hone)
            have hperm : Permutes A₀ (Subgroup.zpowers a) := by
              have hAN : A₀ ≤ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
                rw [Subgroup.le_normalizer_iff]
                intro x hx y hy
                have hxA : x ∈ A := h.ctx22.hA₀ hx
                have hyA : y ∈ A := Subgroup.zpowers_le.mpr haA hy
                have hcomm : x * y = y * x := congrArg Subtype.val
                  ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨x, hxA⟩ ⟨y, hyA⟩)
                rw [hcomm]
                group
                exact hy
              have hBN : Subgroup.zpowers a ≤ Subgroup.normalizer (A₀ : Set G) := by
                rw [Subgroup.le_normalizer_iff]
                intro x hx y hy
                have hxA : x ∈ A := Subgroup.zpowers_le.mpr haA hx
                have hyA : y ∈ A := h.ctx22.hA₀ hy
                have hcomm : x * y = y * x := congrArg Subtype.val
                  ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨x, hxA⟩ ⟨y, hyA⟩)
                rw [hcomm]
                group
                exact hy
              unfold Permutes
              calc (A₀ : Set G) * (Subgroup.zpowers a : Set G) =
                    ((A₀ ⊔ Subgroup.zpowers a : Subgroup G) : Set G) :=
                    (Subgroup.coe_mul_of_left_le_normalizer_right A₀ (Subgroup.zpowers a) hAN).symm
                _ = ((Subgroup.zpowers a ⊔ A₀ : Subgroup G) : Set G) := by rw [sup_comm]
                _ = (Subgroup.zpowers a : Set G) * (A₀ : Set G) :=
                    Subgroup.coe_mul_of_left_le_normalizer_right (Subgroup.zpowers a) A₀ hBN
            have hEcard : Nat.card E = r ^ 2 := by
              rw [show E = A₀ ⊔ Subgroup.zpowers a from rfl,
                CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p2214_card_sup_of_permutes hperm hdisj,
                h.ctx22.hcard, Nat.card_zpowers, haord]
              ring
            refine Or.inr (Or.inr ⟨E, hEA, hEel, hEcard, ?_⟩)
            have hQleCE : Q ≤ S ⊓ Subgroup.centralizer (E : Set G) := by
              refine le_inf hQleS ?_
              intro q hq
              rw [Subgroup.mem_centralizer_iff]
              intro e he
              obtain ⟨x, hx, y, hy, rfl⟩ :=
                CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
                  (A := A₀) (B := Subgroup.zpowers a) (fun u hu v hv => by
                    have huA : u ∈ A := h.ctx22.hA₀ hu
                    have hvA : v ∈ A := Subgroup.zpowers_le.mpr haA hv
                    exact congrArg Subtype.val
                      ((IsMulCommutative.is_comm (M := ↥A)).comm ⟨u, huA⟩ ⟨v, hvA⟩)) he
              have hqx : q * x = x * q := by
                have hxC : x ∈ Subgroup.centralizer (Q : Set G) := by
                  rw [Subgroup.mem_centralizer_iff]
                  intro q' hq'
                  exact (Subgroup.mem_centralizer_iff.mp (hQleCA₀ hq') x hx).symm
                exact Subgroup.mem_centralizer_iff.mp hxC q hq
              have hqy : q * y = y * q := by
                have hyC : y ∈ Subgroup.centralizer (Q : Set G) := by
                  rw [Subgroup.mem_centralizer_iff]
                  intro q' hq'
                  exact (Subgroup.mem_centralizer_iff.mp (hQlea hq') y hy).symm
                exact Subgroup.mem_centralizer_iff.mp hyC q hq
              calc
                (x * y) * q = x * (y * q) := by group
                _ = x * (q * y) := by rw [hqy]
                _ = (x * q) * y := by group
                _ = (q * x) * y := by rw [hqx]
                _ = q * (x * y) := by group
            exact (Subgroup.relIndex_le_of_le_left hQleCE (by
              rw [Subgroup.relIndex]
              exact Subgroup.index_ne_zero_of_finite)).trans hidx

theorem nineteen_twentyeight_of_K
    (D : Data G) {V₀ V : Subgroup G} {p : ℕ}
    {L A : Subgroup G} {t : G} {B : Subgroup G} {r : ℕ} {A₀ H : Subgroup G}
    (h : Ctx19_23 D V₀ V p L A t B r A₀ H)
    (h26 : R19_26At D V₀ V p L A t B r A₀ H h)
    (h14 : R19_14At D V₀ V p L A t B r h.ctx22.ctx)
    (h12 : R19_12At D V₀ V p L A t B r h.ctx22.ctx)
    (h3 : S17.R17_3At D V₀ V) (h42 : S17.R17_42At D V₀ V)
    (h638 : UC6.R6_38 D) (hSg : UC6S846.SigmaStd D)
    (h71 : F07.R71 D) (h72 : F07.R72 D)
    (hK : K_19_25_torusCent) (hKf : K_19_25_noL2SzSection) (hK28 : K_19_28_torusAutomizer) :
    R19_28At D V₀ V p L A t B r A₀ H h := by
  have hodd : Odd (S17.nOf L) := h26
  have hshape : IsSp4 (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsL2Square (Bar2 (IOf D p L)) (S17.nOf L) ∨
      IsSzSquare (Bar2 (IOf D p L)) (S17.nOf L) :=
    shape_of_ctx19_10 D h.ctx22.ctx h42 hodd
  have htri : Trichotomy19_25 D V₀ V p L A t B r h.ctx22.ctx :=
    trichotomy19_25_of D h.ctx22.ctx hodd h3 h42 h638 hSg hK
  have hgen : Subgroup.centralizer (A₀ : Set G) ⊓ IOf D p L ≤
      A ⊔ pCoreOf 2 (IOf D p L) :=
    generic_of_trichotomy D h htri (gap19_25_72_of_sigmaStd D h.ctx22.ctx hSg h71 h72 hKf)
  have h25 : R19_25At D V₀ V p L A t B r A₀ H h := concl19_25_of_generic D h hgen
  exact nineteen_twentyeight_of_gap19_28 D h h25 h26 h14 h12
    (gap19_28_of_torusAutomizer D h h25 h26 hgen hshape hK28)
    (trichotomy19_28_of_torusAutomizer D h h25 h26 hshape hK28)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19

