module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Defs

import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight105Transport
import CFSG.GroupTheory.PCoreJoin
import CFSG.Quasithin.H13.NQBlockSinglePrime
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveConfig

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (calK8104)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem pCoreOf_eq_self {p : ℕ} {H : Subgroup G} (hH : IsPGroup p H) :
    pCoreOf p H = H :=
  le_antisymm (CFSG.LieType.BorelTits.pCoreOf_le p H)
    (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer (r := p) (N := H) (H := H) le_rfl
      (Subgroup.le_normalizer) hH)

private theorem isPGroup_sup_of_le_normalizer {p : ℕ} [Fact p.Prime] {H K : Subgroup G}
    (hH : IsPGroup p H) (hK : IsPGroup p K) (h : K ≤ Subgroup.normalizer (H : Set G)) :
    IsPGroup p ↥(H ⊔ K) := by
  have h1 := CFSG.GroupTheory.pCoreOf_sup_le_pCoreOf_sup (p := p) (Y := K) (U := H) hH h
  rw [pCoreOf_eq_self hK] at h1
  rw [sup_comm H K]
  have heq : K ⊔ H = pCoreOf p (K ⊔ H) :=
    le_antisymm h1 (CFSG.LieType.BorelTits.pCoreOf_le p (K ⊔ H))
  rw [heq]
  exact CFSG.LieType.BorelTits.pCoreOf_isPGroup p (K ⊔ H)

private theorem pCore_le_of_isSylowOf {X H S : Subgroup G} (hX : IsPGroup 2 X) (hXH : X ≤ H)
    (hHX : H ≤ Subgroup.normalizer (X : Set G)) (hS : IsSylowOf 2 S H) : X ≤ S :=
  CFSG.Quasithin.H13.NQBlock.le_of_isSylowOf_of_normalizes hX hXH hHX hS

private def Cen (D : Data G) (L : Subgroup G) : Subgroup G :=
  F08.CentOverO2 D.M L

private noncomputable def barRho (D : Data G) (L : Subgroup G)
    (h : D.M ≤ Subgroup.normalizer (L : Set G)) : ↥D.M →* MulAut (Bar2 L) :=
  (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L).comp (Subgroup.inclusion h)

private theorem mem_cen {D : Data G} {L : Subgroup G} {x : G} :
    x ∈ Cen D L ↔ x ∈ D.M ∧ ∀ l ∈ L, x * l * x⁻¹ * l⁻¹ ∈ pCoreOf 2 L :=
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.mem_centOverO2_iff

private theorem cen_eq_ker {D : Data G} {L : Subgroup G}
    (h : D.M ≤ Subgroup.normalizer (L : Set G)) :
    Cen D L = (MonoidHom.ker (barRho D L h)).map D.M.subtype :=
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.centOverO2_eq_ker_map h

private theorem cen_le {D : Data G} {L : Subgroup G} : Cen D L ≤ D.M :=
  fun _ hx => (mem_cen.mp hx).1

private theorem DM_le_normalizer_cen {D : Data G} {L : Subgroup G}
    (h : D.M ≤ Subgroup.normalizer (L : Set G)) :
    D.M ≤ Subgroup.normalizer (Cen D L : Set G) := by
  have hN : ((Cen D L).subgroupOf D.M).Normal := by
    rw [cen_eq_ker h]
    have heq : ((MonoidHom.ker (barRho D L h)).map D.M.subtype).subgroupOf D.M =
        MonoidHom.ker (barRho D L h) := by
      ext x
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
      constructor
      · rintro ⟨k, hk, hkx⟩
        rwa [Subtype.ext hkx] at hk
      · intro hx
        exact ⟨x, hx, rfl⟩
    rw [heq]
    exact MonoidHom.normal_ker _
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer (cen_le (D := D) (L := L))).mp hN

private theorem pCore_le_cen {D : Data G} {L : Subgroup G} (hL : L ≤ D.M) :
    pCoreOf 2 L ≤ Cen D L :=
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.pCoreOf_le_centOverO2 D hL

private theorem inf_cen_eq_pCore {D : Data G} {L : Subgroup G} (hL : L ≤ D.M)
    (hZ : center (Bar2 L) = ⊥) : L ⊓ Cen D L = pCoreOf 2 L := by
  refine le_antisymm ?_ (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) (pCore_le_cen hL))
  rintro x ⟨hxL, hxC⟩
  have hxcent : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) ∈ center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro q
    induction q using QuotientGroup.induction_on with
    | H l =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq_iff_div_mem]
      have hcoe : (((l * ⟨x, hxL⟩) / (⟨x, hxL⟩ * l) : ↥L) : G) = (x * l * x⁻¹ * l⁻¹)⁻¹ := by
        simp [div_eq_mul_inv, mul_assoc]
      have hG : (((l * ⟨x, hxL⟩) / (⟨x, hxL⟩ * l) : ↥L) : G) ∈ pCoreOf 2 L := by
        rw [hcoe]
        exact (pCoreOf 2 L).inv_mem ((mem_cen.mp hxC).2 l l.2)
      obtain ⟨p, hp, hpeq⟩ := Subgroup.mem_map.mp hG
      have hp_eq : p = (l * ⟨x, hxL⟩) / (⟨x, hxL⟩ * l) := L.subtype_injective hpeq
      rwa [← hp_eq]
  rw [hZ] at hxcent
  have h1 : (⟨x, hxL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
    (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hxcent)
  exact Subgroup.mem_map_of_mem (f := L.subtype) (K := CFSG.pCore 2 ↥L) h1

private theorem commutator_mem_pCore_of_mem_cen {D : Data G} {L K : Subgroup G} (hL : L ≤ D.M)
    (hKL : K ≤ L) {k : G} (hk : k ∈ K) {y : G} (hy : y ∈ Cen D L) :
    k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 L := by
  have hcomm : y * k⁻¹ * y⁻¹ * k ∈ pCoreOf 2 L := by
    simpa using (mem_cen.mp hy).2 k⁻¹ (hKL (K.inv_mem hk))
  have heq : k * y * k⁻¹ * y⁻¹ = k * (y * k⁻¹ * y⁻¹ * k) * k⁻¹ := by group
  rw [heq]
  exact (Subgroup.mem_normalizer_iff.mp
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (hKL hk)) _).1 hcomm

private theorem le_normalizer_of_isSylowOf_cen {D : Data G} {L X S : Subgroup G}
    (hN : D.M ≤ Subgroup.normalizer (L : Set G)) (hL : L ≤ D.M) (hXL : X ≤ L)
    (hS : IsSylowOf 2 S (Cen D L))
    (h : ∀ x ∈ X, ∀ y ∈ Cen D L, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L) :
    X ≤ Subgroup.normalizer (S : Set G) := by
  have hQS : pCoreOf 2 L ≤ S :=
    pCore_le_of_isSylowOf (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) (pCore_le_cen hL)
      (((cen_le (D := D) (L := L)).trans hN).trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L)) hS
  have key : ∀ x ∈ X, ∀ s ∈ S, x * s * x⁻¹ ∈ S := by
    intro x hx s hs
    have hmem : x * s * x⁻¹ * s⁻¹ ∈ pCoreOf 2 L := h x hx s (hS.le hs)
    have heq : x * s * x⁻¹ = (x * s * x⁻¹ * s⁻¹) * s := by group
    rw [heq]
    exact S.mul_mem (hQS hmem) hs
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro s
  constructor
  · exact key x hx s
  · intro hs
    have h1 := key x⁻¹ (X.inv_mem hx) (x * s * x⁻¹) hs
    have h2 : x⁻¹ * (x * s * x⁻¹) * x⁻¹⁻¹ = s := by group
    rwa [h2] at h1

private theorem exists_isSylowOf_normalized {p : ℕ} [Fact p.Prime] {K Q : Subgroup G}
    (hQ : IsPGroup p Q) (hQK : Q ≤ Subgroup.normalizer (K : Set G)) :
    ∃ P : Subgroup G, IsSylowOf p P K ∧ Q ≤ Subgroup.normalizer (P : Set G) := by
  classical
  let : MulAction Q (Sylow p K) := MulAction.compHom (Sylow p K) (Subgroup.inclusion hQK)
  have : Finite (Sylow p K) := Sylow.finite_of_finiteIndex (Classical.choice (Sylow.nonempty))
  obtain ⟨P₀, hP₀fix⟩ :=
    hQ.nonempty_fixed_point_of_prime_not_dvd_card (Sylow p K)
      (not_dvd_card_sylow (p := p) (G := K))
  refine ⟨(P₀ : Subgroup K).map K.subtype, ⟨P₀, rfl⟩, ?_⟩
  have hforward : ∀ q : Q, ∀ x ∈ (P₀ : Subgroup K).map K.subtype,
      (q : G) * x * (q : G)⁻¹ ∈ (P₀ : Subgroup K).map K.subtype := by
    intro q x hx
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hx
    have hfix : (Subgroup.inclusion hQK q) • P₀ = P₀ := by
      simpa only [MulAction.compHom_smul_def] using MulAction.mem_fixedPoints.mp hP₀fix q
    have hsm : (Subgroup.inclusion hQK q) • (P₀ : Subgroup K) = (P₀ : Subgroup K) := by
      rw [← Sylow.pointwise_smul_def, hfix]
    have hmem : (Subgroup.inclusion hQK q) • k ∈ (P₀ : Subgroup K) := by
      rw [← hsm]
      exact Subgroup.smul_mem_pointwise_smul k (Subgroup.inclusion hQK q) (P₀ : Subgroup K) hk
    exact Subgroup.mem_map_of_mem K.subtype hmem
  intro q hq
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · exact hforward ⟨q, hq⟩ x
  · intro hx
    have h := hforward (⟨q, hq⟩ : Q)⁻¹ (q * x * q⁻¹) hx
    have hco : ((⟨q, hq⟩ : Q)⁻¹ : G) = q⁻¹ := rfl
    rw [hco] at h
    simpa [mul_assoc] using h

private theorem le_normalizer_sup_of_le_normalizer {A B C : Subgroup G}
    (hB : A ≤ Subgroup.normalizer (B : Set G)) (hC : A ≤ Subgroup.normalizer (C : Set G)) :
    A ≤ Subgroup.normalizer ((B ⊔ C : Subgroup G) : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB ha),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hC ha)]

private theorem H_le_normalizer_of_isSylowOf_cen {P H K S : Subgroup G}
    (hHset : (H : Set G) = (pCoreOf 2 H : Set G) * (K : Set G) * P)
    (hRN : pCoreOf 2 H ≤ Subgroup.normalizer (S : Set G))
    (hKN : K ≤ Subgroup.normalizer (S : Set G))
    (hPN : P ≤ Subgroup.normalizer (S : Set G)) :
    H ≤ Subgroup.normalizer (S : Set G) := by
  intro h hh
  have hh' : h ∈ (H : Set G) := hh
  rw [hHset] at hh'
  obtain ⟨a, ha, b, hb, hab⟩ := Set.mem_mul.mp hh'
  obtain ⟨r, hr, p, hp, hap⟩ := Set.mem_mul.mp ha
  rw [← hab, ← hap]
  exact (Subgroup.normalizer (S : Set G)).mul_mem
    ((Subgroup.normalizer (S : Set G)).mul_mem (hRN hr) (hKN hp)) (hPN hb)

private theorem inf_cen_isSylow {D : Data G} {L P H K : Subgroup G}
    (hN : D.M ≤ Subgroup.normalizer (L : Set G)) (hL : L ≤ D.M) (hHM : H ≤ D.M)
    (hHset : (H : Set G) = (pCoreOf 2 H : Set G) * (K : Set G) * P)
    (hKH : K ≤ H) (hPH : P ≤ H) (hKL : K ≤ L) (hPL : P ≤ L)
    (hKcomm : ∀ x ∈ K, ∀ y ∈ Cen D L, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L)
    (hPcomm : ∀ x ∈ P, ∀ y ∈ Cen D L, x * y * x⁻¹ * y⁻¹ ∈ pCoreOf 2 L)
    (hR2 : IsPGroup 2 (pCoreOf 2 H))
    (hR : ∀ R' : Subgroup G, R' ≤ D.M → IsPGroup 2 R' → H ≤ Subgroup.normalizer (R' : Set G) →
      pCoreOf 2 H ≤ R' → R' = pCoreOf 2 H) :
    IsSylowOf 2 (pCoreOf 2 H ⊓ Cen D L) (Cen D L) := by
  have hRC : pCoreOf 2 H ≤ Subgroup.normalizer (Cen D L : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans (hHM.trans (DM_le_normalizer_cen hN))
  obtain ⟨S', hS', hRS'⟩ := exists_isSylowOf_normalized hR2 hRC
  have hsup : IsPGroup 2 ↥(S' ⊔ pCoreOf 2 H) :=
    isPGroup_sup_of_le_normalizer (H := S') (K := pCoreOf 2 H) hS'.isPGroup hR2 hRS'
  have hKNS : K ≤ Subgroup.normalizer (S' : Set G) :=
    le_normalizer_of_isSylowOf_cen hN hL hKL hS' hKcomm
  have hPNS : P ≤ Subgroup.normalizer (S' : Set G) :=
    le_normalizer_of_isSylowOf_cen hN hL hPL hS' hPcomm
  have hRN' : pCoreOf 2 H ≤ Subgroup.normalizer ((S' ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer hRS' (Subgroup.le_normalizer)
  have hKN' : K ≤ Subgroup.normalizer ((S' ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer hKNS
      (hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hPN' : P ≤ Subgroup.normalizer ((S' ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer hPNS
      (hPH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
  have hHN : H ≤ Subgroup.normalizer ((S' ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    H_le_normalizer_of_isSylowOf_cen hHset hRN' hKN' hPN'
  have hkey := hR (S' ⊔ pCoreOf 2 H)
    (sup_le (hS'.le.trans (cen_le (D := D) (L := L)))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHM)) hsup hHN le_sup_right
  have hSR : S' ≤ pCoreOf 2 H := le_sup_left.trans hkey.le
  have h2 : IsPGroup 2 ↥(pCoreOf 2 H ⊓ Cen D L) := hR2.to_le inf_le_left
  have hseq : pCoreOf 2 H ⊓ Cen D L = S' :=
    hS'.eq_of_le (le_inf hSR hS'.le) inf_le_right h2
  rw [hseq]
  exact hS'

private noncomputable def Rbar (D : Data G) (L : Subgroup G)
    (h : D.M ≤ Subgroup.normalizer (L : Set G)) (H : Subgroup G) : Subgroup (MulAut (Bar2 L)) :=
  ((pCoreOf 2 H).subgroupOf D.M).map (barRho D L h)

private noncomputable def Uset (D : Data G) (L : Subgroup G)
    (h : D.M ≤ Subgroup.normalizer (L : Set G)) (H : Subgroup G) : Subgroup (Bar2 L) :=
  (Rbar D L h H).comap (MulAut.conj : Bar2 L →* MulAut (Bar2 L))

private theorem mem_Uset {D : Data G} {L H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} {x : Bar2 L} :
    x ∈ Uset D L h H ↔ MulAut.conj x ∈ Rbar D L h H :=
  Iff.rfl

private theorem conj_injective_of_center_eq_bot {L : Subgroup G}
    (hZ : center (Bar2 L) = ⊥) :
    Function.Injective (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) := by
  intro x y hxy
  have h1 : MulAut.conj (y⁻¹ * x) = 1 := by
    rw [map_mul, map_inv, hxy, inv_mul_cancel]
  have h2 : y⁻¹ * x ∈ center (Bar2 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have hg := congrArg (fun f : MulAut (Bar2 L) => f g) h1
    rw [MulAut.conj_apply, MulAut.one_apply] at hg
    have hg' : x * g * x⁻¹ = y * g * y⁻¹ := by
      calc x * g * x⁻¹ = y * ((y⁻¹ * x) * g * ((y⁻¹ * x))⁻¹) * y⁻¹ := by group
        _ = y * g * y⁻¹ := by rw [hg]
    calc g * (y⁻¹ * x) = y⁻¹ * (y * g * y⁻¹) * x := by group
      _ = y⁻¹ * (x * g * x⁻¹) * x := by rw [hg']
      _ = (y⁻¹ * x) * g := by group
  rw [hZ] at h2
  have h3 : y⁻¹ * x = 1 := by simpa using h2
  calc x = y * (y⁻¹ * x) := by group
    _ = y := by rw [h3, mul_one]

private theorem isPGroup_Rbar {D : Data G} {L H : Subgroup G}
    (h : D.M ≤ Subgroup.normalizer (L : Set G)) (hHM : H ≤ D.M) :
    IsPGroup 2 (Rbar D L h H) := by
  have hle : pCoreOf 2 H ≤ D.M := (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHM
  have hR : IsPGroup 2 ↥((pCoreOf 2 H).subgroupOf D.M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).of_equiv
      (Subgroup.subgroupOfEquivOfLe hle).symm
  exact hR.map (barRho D L h)

private theorem isPGroup_Uset {D : Data G} {L H : Subgroup G}
    (h : D.M ≤ Subgroup.normalizer (L : Set G)) (hHM : H ≤ D.M)
    (hZ : center (Bar2 L) = ⊥) : IsPGroup 2 (Uset D L h H) := by
  have hinj := conj_injective_of_center_eq_bot (L := L) hZ
  have hR2 := isPGroup_Rbar (D := D) (L := L) (H := H) h hHM
  have hf : ∀ x : ↥(Uset D L h H),
      ((MulAut.conj : Bar2 L →* MulAut (Bar2 L)).comp (Subgroup.subtype (Uset D L h H))) x ∈
        Rbar D L h H := fun x => x.2
  refine hR2.of_injective
    (((MulAut.conj : Bar2 L →* MulAut (Bar2 L)).comp
      (Subgroup.subtype (Uset D L h H))).codRestrict (Rbar D L h H) hf) ?_
  intro x y hxy
  have h1 : MulAut.conj x.1 = MulAut.conj y.1 := congrArg Subtype.val hxy
  exact Subtype.ext (hinj h1)

private theorem conj_mem_Rbar_iff {D : Data G} {L H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} {f : MulAut (Bar2 L)}
    (hf : f ∈ Rbar D L h H) (x : Bar2 L) :
    MulAut.conj (f x) ∈ Rbar D L h H ↔ MulAut.conj x ∈ Rbar D L h H := by
  have hconj : MulAut.conj (f x) = f * MulAut.conj x * f⁻¹ := by
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  constructor
  · intro hx
    rw [hconj] at hx
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hf) (MulAut.conj x)).mpr hx
  · intro hx
    rw [hconj]
    exact (Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hf) (MulAut.conj x)).mp hx

private theorem conj_mem_Rbar_iff_of_mem_barImage {D : Data G} {L X H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (hXDM : X ≤ D.M) (hXH : X ≤ H)
    {k : ↥L} (hkX : (k : G) ∈ X) {f : MulAut (Bar2 L)} :
    MulAut.conj (QuotientGroup.mk k) * f * (MulAut.conj (QuotientGroup.mk k))⁻¹ ∈ Rbar D L h H ↔
      f ∈ Rbar D L h H := by
  have hconj : ∀ (j : ↥L) (hj : (j : G) ∈ X),
      MulAut.conj (QuotientGroup.mk j) = barRho D L h ⟨(j : G), hXDM hj⟩ := by
    intro j hj
    rw [barRho, MonoidHom.comp_apply]
    exact (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_inner L (j : G) j.2).symm
  have hforward : ∀ (j : ↥L) (hj : (j : G) ∈ X) (g : MulAut (Bar2 L)), g ∈ Rbar D L h H →
      MulAut.conj (QuotientGroup.mk j) * g * (MulAut.conj (QuotientGroup.mk j))⁻¹ ∈
        Rbar D L h H := by
    intro j hj g hg
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.mp hg
    have hmemM : (j : G) * (r : G) * (j : G)⁻¹ ∈ D.M :=
      D.M.mul_mem (D.M.mul_mem (hXDM hj) r.2) (D.M.inv_mem (hXDM hj))
    have hmemR : (j : G) * (r : G) * (j : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hXH hj)) (r : G)).mp hr
    have helem : (⟨(j : G) * (r : G) * (j : G)⁻¹, hmemM⟩ : ↥D.M) =
        ⟨(j : G), hXDM hj⟩ * r * ⟨(j : G), hXDM hj⟩⁻¹ := Subtype.ext rfl
    have hmul : barRho D L h (⟨(j : G) * (r : G) * (j : G)⁻¹, hmemM⟩ : ↥D.M) =
        MulAut.conj (QuotientGroup.mk j) * barRho D L h r *
          (MulAut.conj (QuotientGroup.mk j))⁻¹ := by
      rw [hconj j hj, helem, map_mul, map_mul, map_inv]
    rw [← hmul]
    exact Subgroup.mem_map.mpr ⟨⟨(j : G) * (r : G) * (j : G)⁻¹, hmemM⟩,
      Subgroup.mem_subgroupOf.mpr hmemR, rfl⟩
  have key : ∀ (j : ↥L) (hj : (j : G) ∈ X) (g : MulAut (Bar2 L)),
      MulAut.conj (QuotientGroup.mk j) * g * (MulAut.conj (QuotientGroup.mk j))⁻¹ ∈
        Rbar D L h H ↔ g ∈ Rbar D L h H := by
    intro j hj g
    constructor
    · intro hx
      have h1 := hforward j⁻¹ (X.inv_mem hj) _ hx
      have hc : (QuotientGroup.mk j⁻¹ : Bar2 L) = ((QuotientGroup.mk j : Bar2 L))⁻¹ := by
        rw [← QuotientGroup.mk_inv]
      have heq : (MulAut.conj (QuotientGroup.mk j))⁻¹ *
          (MulAut.conj (QuotientGroup.mk j) * g * (MulAut.conj (QuotientGroup.mk j))⁻¹) *
          MulAut.conj (QuotientGroup.mk j) = g := by group
      rw [hc, map_inv, inv_inv] at h1
      rwa [heq] at h1
    · exact hforward j hj g
  exact key k hkX f

private theorem barImage_le_normalizer_Uset {D : Data G} {L X H : Subgroup G}
    (h : D.M ≤ Subgroup.normalizer (L : Set G)) (hXL : X ≤ L) (hXDM : X ≤ D.M)
    (hXH : X ≤ H) :
    barImage L X ≤ Subgroup.normalizer (Uset D L h H : Set (Bar2 L)) := by
  intro kb hkb
  obtain ⟨k, hk, rfl⟩ := uc22p21c_mem_barImage.1 hkb
  rw [Subgroup.mem_normalizer_iff]
  intro x
  rw [mem_Uset, mem_Uset]
  have hconj : ∀ g : Bar2 L, MulAut.conj ((MulAut.conj g) x) =
      MulAut.conj g * MulAut.conj x * (MulAut.conj g)⁻¹ := by
    intro g
    ext y
    simp [MulAut.conj_apply, mul_assoc]
  rw [← MulAut.conj_apply, hconj]
  exact (conj_mem_Rbar_iff_of_mem_barImage hXDM hXH hk).symm

private theorem commutator_mem_pCore_of_Uset_eq_bot {D : Data G} {L X H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (hXL : X ≤ L) (hXDM : X ≤ D.M)
    (hXH : X ≤ H) {r : G} (hrR : r ∈ pCoreOf 2 H) (hrM : r ∈ D.M)
    (hbot : Uset D L h H = ⊥) {x : G} (hxX : x ∈ X) :
    r * x * r⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
  have hxM : x ∈ D.M := hXDM hxX
  have hxL : x ∈ L := hXL hxX
  have hconjR : x * r⁻¹ * x⁻¹ ∈ pCoreOf 2 H :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hXH hxX)) r⁻¹).mp
      ((pCoreOf 2 H).inv_mem hrR)
  have hcR : r * x * r⁻¹ * x⁻¹ ∈ pCoreOf 2 H := by
    have h2 := (pCoreOf 2 H).mul_mem hrR hconjR
    simpa [mul_assoc] using h2
  have hrxL : r * x * r⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (h hrM) x).mp hxL
  have hcL : r * x * r⁻¹ * x⁻¹ ∈ L := L.mul_mem hrxL (L.inv_mem hxL)
  have hcM : r * x * r⁻¹ * x⁻¹ ∈ D.M :=
    D.M.mul_mem (D.M.mul_mem (D.M.mul_mem hrM hxM) (D.M.inv_mem hrM)) (D.M.inv_mem hxM)
  have hin : (QuotientGroup.mk (⟨r * x * r⁻¹ * x⁻¹, hcL⟩ : ↥L) : Bar2 L) ∈ Uset D L h H := by
    rw [mem_Uset]
    have hconj : MulAut.conj (QuotientGroup.mk (⟨r * x * r⁻¹ * x⁻¹, hcL⟩ : ↥L) : Bar2 L) =
        barRho D L h ⟨r * x * r⁻¹ * x⁻¹, hcM⟩ := by
      rw [barRho, MonoidHom.comp_apply]
      exact (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_inner L _ hcL).symm
    rw [hconj]
    exact Subgroup.mem_map.mpr ⟨⟨r * x * r⁻¹ * x⁻¹, hcM⟩,
      Subgroup.mem_subgroupOf.mpr hcR, rfl⟩
  rw [hbot] at hin
  have h1 : (⟨r * x * r⁻¹ * x⁻¹, hcL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L :=
    (QuotientGroup.eq_one_iff _).mp (Subgroup.mem_bot.mp hin)
  exact Subgroup.mem_map_of_mem (f := L.subtype) (K := CFSG.pCore 2 ↥L) h1

private theorem barRho_eq_of_Uset_eq_bot {D : Data G} {L X H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (hXL : X ≤ L) (hXDM : X ≤ D.M)
    (hXH : X ≤ H) {r : G} (hrR : r ∈ pCoreOf 2 H) (hrM : r ∈ D.M)
    (hbot : Uset D L h H = ⊥) {x : Bar2 L} (hx : x ∈ barImage L X) :
    barRho D L h ⟨r, hrM⟩ x = x := by
  obtain ⟨k, hk, rfl⟩ := uc22p21c_mem_barImage.1 hx
  change barRho D L h ⟨r, hrM⟩ (QuotientGroup.mk k : Bar2 L) = (QuotientGroup.mk k : Bar2 L)
  have hcomm := commutator_mem_pCore_of_Uset_eq_bot hXL hXDM hXH hrR hrM hbot hk
  have hmemL : r * (k : G) * r⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (h hrM) k).mp k.2
  have hval : barRho D L h ⟨r, hrM⟩ (QuotientGroup.mk k : Bar2 L) =
      (QuotientGroup.mk (⟨r * (k : G) * r⁻¹, hmemL⟩ : ↥L) : Bar2 L) := by
    rw [barRho, MonoidHom.comp_apply, CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
    congr 1
  show (QuotientGroup.mk (⟨r * (k : G) * r⁻¹, hmemL⟩ : ↥L) : Bar2 L) =
    (QuotientGroup.mk k : Bar2 L)
  rw [QuotientGroup.eq_iff_div_mem]
  have hmem : ((⟨r * (k : G) * r⁻¹, hmemL⟩ / k : ↥L) : G) =
      r * (k : G) * r⁻¹ * (k : G)⁻¹ := by
    simp [div_eq_mul_inv, mul_assoc]
  have hmemG : ((⟨r * (k : G) * r⁻¹, hmemL⟩ / k : ↥L) : G) ∈ pCoreOf 2 L :=
    hmem.symm ▸ hcomm
  obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmemG
  have hz' : z = (⟨r * (k : G) * r⁻¹, hmemL⟩ / k : ↥L) := L.subtype_injective hzy
  rwa [hz'] at hz

private theorem pCore_le_cen_of_Uset_eq_bot {D : Data G} {L K P H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (hHM : H ≤ D.M)
    (hKL : K ≤ L) (hKDM : K ≤ D.M) (hKH : K ≤ H)
    (hPL : P ≤ L) (hPDM : P ≤ D.M) (hPH : P ≤ H)
    (hF5' : ∀ α : MulAut (Bar2 L), (∃ k : ℕ, α ^ (2 ^ k) = 1) →
      (∀ x ∈ barImage L K, α x = x) → (∀ x ∈ barImage L P, α x = x) → α = 1)
    (hbot : Uset D L h H = ⊥) : pCoreOf 2 H ≤ Cen D L := by
  intro r hrR
  have hrM : r ∈ D.M := hHM ((CFSG.LieType.BorelTits.pCoreOf_le 2 H) hrR)
  have hfixK : ∀ x ∈ barImage L K, barRho D L h ⟨r, hrM⟩ x = x :=
    fun x hx => barRho_eq_of_Uset_eq_bot hKL hKDM hKH hrR hrM hbot hx
  have hfixP : ∀ x ∈ barImage L P, barRho D L h ⟨r, hrM⟩ x = x :=
    fun x hx => barRho_eq_of_Uset_eq_bot hPL hPDM hPH hrR hrM hbot hx
  have hpow : ∃ k : ℕ, barRho D L h ⟨r, hrM⟩ ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) ⟨r, hrR⟩
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have hk1 : (⟨r, hrM⟩ : ↥D.M) ^ (2 ^ k) = 1 := by
      apply Subtype.ext
      simpa using congrArg Subtype.val hk
    rw [hk1, map_one]
  have htriv : barRho D L h ⟨r, hrM⟩ = 1 := hF5' _ hpow hfixK hfixP
  have hrho : (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L)
      ⟨r, h hrM⟩ = 1 := htriv
  rw [mem_cen]
  refine ⟨hrM, fun l hl => ?_⟩
  exact (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_fix_iff L
    ⟨r, h hrM⟩ ⟨l, hl⟩).mp (by rw [hrho, MulAut.one_apply])

private theorem isPGroup_barPreimage {L : Subgroup G} {Y : Subgroup (Bar2 L)}
    (hY : IsPGroup 2 Y) : IsPGroup 2 (barPreimage L Y) := by
  intro x
  have hxL : (x : G) ∈ L := Subgroup.map_subtype_le _ x.2
  have hxY : (uc22p21cPi L ⟨(x : G), hxL⟩) ∈ Y := by
    have h : (uc22p21cPi L ⟨(x : G), hxL⟩) ∈ barImage L (barPreimage L Y) :=
      uc22p21c_mem_barImage.2 ⟨⟨(x : G), hxL⟩, x.2, rfl⟩
    rwa [barImage_barPreimage] at h
  obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp hY ⟨_, hxY⟩
  have hkG : (x : G) ^ (2 ^ k) ∈ pCoreOf 2 L := by
    have h1 : (uc22p21cPi L (⟨(x : G) ^ (2 ^ k), L.pow_mem hxL (2 ^ k)⟩ : ↥L)) = 1 := by
      rw [show (⟨(x : G) ^ (2 ^ k), L.pow_mem hxL (2 ^ k)⟩ : ↥L) =
        ⟨(x : G), hxL⟩ ^ (2 ^ k) from Subtype.ext rfl, map_pow]
      simpa using congrArg Subtype.val hk
    exact Subgroup.mem_map_of_mem (f := L.subtype) (K := CFSG.pCore 2 ↥L)
      ((QuotientGroup.eq_one_iff _).mp h1)
  obtain ⟨j, hj⟩ := isPGroup_iff_pow_pow_eq_one.mp
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) ⟨_, hkG⟩
  have hjG : ((x : G) ^ (2 ^ k)) ^ (2 ^ j) = 1 := by
    simpa using congrArg Subtype.val hj
  refine ⟨k + j, ?_⟩
  apply Subtype.ext
  show (x : G) ^ (2 ^ (k + j)) = 1
  rw [pow_add, pow_mul]
  exact hjG

private theorem cen_le_normalizer_barPreimage {D : Data G} {L : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (Y : Subgroup (Bar2 L)) :
    Cen D L ≤ Subgroup.normalizer (barPreimage L Y : Set G) := by
  intro c hc
  have hcM : c ∈ D.M := cen_le hc
  have hcN : c ∈ Subgroup.normalizer (L : Set G) := h hcM
  have key : ∀ {y : G} (hyL : y ∈ L) (hcyL : c * y * c⁻¹ ∈ L),
      (uc22p21cPi L ⟨y, hyL⟩) = (uc22p21cPi L ⟨c * y * c⁻¹, hcyL⟩) := by
    intro y hyL hcyL
    change (QuotientGroup.mk (⟨y, hyL⟩ : ↥L) : Bar2 L) =
      (QuotientGroup.mk (⟨c * y * c⁻¹, hcyL⟩ : ↥L) : Bar2 L)
    rw [QuotientGroup.eq_iff_div_mem]
    have hcomm : c * y * c⁻¹ * y⁻¹ ∈ pCoreOf 2 L := (mem_cen.mp hc).2 y hyL
    have hcoe : ((⟨y, hyL⟩ / ⟨c * y * c⁻¹, hcyL⟩ : ↥L) : G) = (c * y * c⁻¹ * y⁻¹)⁻¹ := by
      simp [div_eq_mul_inv, mul_assoc]
    have hmemG : ((⟨y, hyL⟩ / ⟨c * y * c⁻¹, hcyL⟩ : ↥L) : G) ∈ pCoreOf 2 L := by
      rw [hcoe]
      exact (pCoreOf 2 L).inv_mem hcomm
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hmemG
    rwa [show z = (⟨y, hyL⟩ / ⟨c * y * c⁻¹, hcyL⟩ : ↥L) from L.subtype_injective hzy] at hz
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [uc22p21c_mem_barPreimage, uc22p21c_mem_barPreimage]
  constructor
  · rintro ⟨hyL, hyY⟩
    have hcyL : c * y * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hcN y).mp hyL
    exact ⟨hcyL, (key hyL hcyL) ▸ hyY⟩
  · rintro ⟨hcyL, hyY⟩
    have hyL : y ∈ L := by
      have h := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem hcN) (c * y * c⁻¹)).mp hcyL
      rwa [show c⁻¹ * (c * y * c⁻¹) * (c⁻¹)⁻¹ = y from by group] at h
    exact ⟨hyL, (key hyL hcyL).symm ▸ hyY⟩

private theorem le_normalizer_barPreimage_of_le_normalizer {L X : Subgroup G}
    {Y : Subgroup (Bar2 L)} (hXL : X ≤ L)
    (hXY : barImage L X ≤ Subgroup.normalizer (Y : Set (Bar2 L))) :
    X ≤ Subgroup.normalizer (barPreimage L Y : Set G) := by
  intro x hx
  have hxL : x ∈ L := hXL hx
  have hxN : uc22p21cPi L ⟨x, hxL⟩ ∈ Subgroup.normalizer (Y : Set (Bar2 L)) :=
    hXY (uc22p21c_mem_barImage.2 ⟨⟨x, hxL⟩, hx, rfl⟩)
  have hiff : ∀ (y : G) (hyL : y ∈ L),
      (uc22p21cPi L ⟨x * y * x⁻¹, L.mul_mem (L.mul_mem hxL hyL) (L.inv_mem hxL)⟩ ∈ Y) ↔
        (uc22p21cPi L ⟨y, hyL⟩ ∈ Y) := by
    intro y hyL
    have heq : uc22p21cPi L ⟨x * y * x⁻¹,
        L.mul_mem (L.mul_mem hxL hyL) (L.inv_mem hxL)⟩ =
        uc22p21cPi L ⟨x, hxL⟩ * uc22p21cPi L ⟨y, hyL⟩ * (uc22p21cPi L ⟨x, hxL⟩)⁻¹ := by
      rw [show (⟨x * y * x⁻¹, L.mul_mem (L.mul_mem hxL hyL) (L.inv_mem hxL)⟩ : ↥L) =
        ⟨x, hxL⟩ * ⟨y, hyL⟩ * ⟨x, hxL⟩⁻¹ from Subtype.ext rfl, map_mul, map_mul, map_inv]
    rw [heq]
    exact (Subgroup.mem_normalizer_iff.mp hxN (uc22p21cPi L ⟨y, hyL⟩)).symm
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [uc22p21c_mem_barPreimage, uc22p21c_mem_barPreimage]
  constructor
  · rintro ⟨hyL, hyY⟩
    exact ⟨L.mul_mem (L.mul_mem hxL hyL) (L.inv_mem hxL), (hiff y hyL).mpr hyY⟩
  · rintro ⟨hxyL, hxyY⟩
    have hyL : y ∈ L := by
      have h := L.mul_mem (L.mul_mem (L.inv_mem hxL) hxyL) hxL
      rwa [show x⁻¹ * (x * y * x⁻¹) * x = y from by group] at h
    exact ⟨hyL, (hiff y hyL).mp hxyY⟩

private theorem barPreimage_bot_eq_pCoreOf (L : Subgroup G) :
    barPreimage L (⊥ : Subgroup (Bar2 L)) = pCoreOf 2 L := by
  ext x
  rw [uc22p21c_mem_barPreimage]
  constructor
  · rintro ⟨hxL, hx1⟩
    exact Subgroup.mem_map_of_mem (f := L.subtype) (K := CFSG.pCore 2 ↥L)
      (by simpa using hx1)
  · rintro ⟨z, hz, hzx⟩
    refine ⟨hzx ▸ z.2, ?_⟩
    have h1 : (⟨x, hzx ▸ z.2⟩ : ↥L) = z := Subtype.ext hzx.symm
    rw [h1]
    simpa using (QuotientGroup.eq_one_iff _).mpr hz

private theorem barImage_pCoreOf_eq_bot (L : Subgroup G) :
    barImage L (pCoreOf 2 L) = ⊥ := by
  rw [← barPreimage_bot_eq_pCoreOf L, barImage_barPreimage]

private theorem autOdd_barImage_KP {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) (hF5 : KU45AutOdd) :
    ∀ α : MulAut (Bar2 L), (∃ k : ℕ, α ^ (2 ^ k) = 1) →
      (∀ x ∈ barImage L (F08.KOf8103 L B), α x = x) →
      (∀ x ∈ barImage L P, α x = x) → α = 1 := by
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hBP : B ≤ P := s.notB.2.1
  have hBL : B ≤ L := hBP.trans hPL
  have hB3 : IsPGroup 3 B := hP3.to_le hBP
  have hPbar2 : IsPGroup 3 (barImage L P) :=
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).1
  have hPbaridx : ¬ 3 ∣ (barImage L P).index :=
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).2
  have hBbar : F08.NotationB8103 ⊤ (barImage L P) n (barImage L B) :=
    (notationB8103_barImage_iff hPL hP3 hBP).mpr s.notB
  intro α hpow hK hP
  have hK' : ∀ x ∈ F08.KOf8103 ⊤ (barImage L B), α x = x := by
    rw [← barImage_kOf8103 hBL hB3]
    exact hK
  exact hF5 (Bar2 L) n s.isU45 (barImage L P) hPbar2 hPbaridx (barImage L B) hBbar α hpow hK' hP

private theorem H_le_normalizer_barPreimage_pCoreOf {D : Data G} {L P B H : Subgroup G}
    (h : D.M ≤ Subgroup.normalizer (L : Set G))
    (hH : H ∈ calK8104 D P (F08.KOf8103 L B)) (hKL : F08.KOf8103 L B ≤ L)
    (hPL : P ≤ L) (hRC : pCoreOf 2 H ≤ Cen D L) {Y : Subgroup (Bar2 L)}
    (hKbar : barImage L (F08.KOf8103 L B) ≤ Y) (hPbar : barImage L P ≤ Y)
    (hYnorm : Y ≤ Subgroup.normalizer (pCoreOf 2 Y : Set (Bar2 L))) :
    H ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 Y) : Set G) := by
  have hKN : F08.KOf8103 L B ≤
      Subgroup.normalizer (barPreimage L (pCoreOf 2 Y) : Set G) :=
    le_normalizer_barPreimage_of_le_normalizer hKL (hKbar.trans hYnorm)
  have hPN : P ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 Y) : Set G) :=
    le_normalizer_barPreimage_of_le_normalizer hPL (hPbar.trans hYnorm)
  have hRN : pCoreOf 2 H ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 Y) : Set G) :=
    hRC.trans (cen_le_normalizer_barPreimage (D := D) (L := L) (h := h) (pCoreOf 2 Y))
  have hHset : (H : Set G) = (pCoreOf 2 H : Set G) * (F08.KOf8103 L B : Set G) * P := by
    have hinf : F08.KOf8103 L B ⊓ H = F08.KOf8103 L B :=
      le_antisymm inf_le_left (le_inf le_rfl hH.2.2.1)
    rw [hH.2.2.2, hinf]
  exact H_le_normalizer_of_isSylowOf_cen hHset hRN hKN hPN

private theorem pCoreOf_eq_bot_of_le_normalizer_barPreimage {D : Data G} {L P B H : Subgroup G}
    {p n : ℕ} (s : Std8105 D L P B p n) (hHM : H ≤ D.M)
    (hR : ∀ R' : Subgroup G, R' ≤ D.M → IsPGroup 2 R' → H ≤ normalizer (R' : Set G) →
      pCoreOf 2 H ≤ R' → R' = pCoreOf 2 H)
    (hRC : pCoreOf 2 H ≤ Cen D L) {Y : Subgroup (Bar2 L)}
    (hHN : H ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 Y) : Set G)) :
    pCoreOf 2 Y = ⊥ := by
  have hLDM : L ≤ D.M := CFSG.Open.IsSubnormal.le s.hyp.1.1
  have hRN : pCoreOf 2 H ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 Y) : Set G) :=
    hRC.trans (cen_le_normalizer_barPreimage (D := D) (L := L) (h := s.normal)
      (pCoreOf 2 Y))
  have hsup : IsPGroup 2 ↥(barPreimage L (pCoreOf 2 Y) ⊔ pCoreOf 2 H) :=
    isPGroup_sup_of_le_normalizer (H := barPreimage L (pCoreOf 2 Y)) (K := pCoreOf 2 H)
      (isPGroup_barPreimage (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hRN
  have hHN' : H ≤ Subgroup.normalizer
      ((barPreimage L (pCoreOf 2 Y) ⊔ pCoreOf 2 H : Subgroup G) : Set G) :=
    le_normalizer_sup_of_le_normalizer hHN
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)
  have hkey := hR (barPreimage L (pCoreOf 2 Y) ⊔ pCoreOf 2 H)
    (sup_le ((uc22p21c_barPreimage_le L (pCoreOf 2 Y)).trans hLDM)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHM)) hsup hHN' le_sup_right
  have hUWQ : barPreimage L (pCoreOf 2 Y) ≤ pCoreOf 2 L := by
    rw [← inf_cen_eq_pCore (D := D) (L := L) hLDM
      (center_bar2_eq_bot_of_hyp8102 s.hyp)]
    exact le_inf (uc22p21c_barPreimage_le L (pCoreOf 2 Y))
      ((le_sup_left.trans hkey.le).trans hRC)
  have hbotY : pCoreOf 2 Y = ⊥ := by
    have h := barImage_mono (M := L) hUWQ
    rw [barImage_barPreimage, barImage_pCoreOf_eq_bot] at h
    exact le_bot_iff.mp h
  exact hbotY

private theorem Uset_ne_bot (hRad : KU45Radical) (hF5 : KU45AutOdd) {D : Data G}
    {L P B H : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n)
    (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    (hR : ∀ R' : Subgroup G, R' ≤ D.M → IsPGroup 2 R' → H ≤ normalizer (R' : Set G) →
      pCoreOf 2 H ≤ R' → R' = pCoreOf 2 H) :
    Uset D L s.normal H ≠ ⊥ := by
  intro hbot
  have hHM : H ≤ D.M := hH.1
  have hKH : F08.KOf8103 L B ≤ H := hH.2.2.1
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hBP : B ≤ P := s.notB.2.1
  have hBL : B ≤ L := hBP.trans hPL
  have hB3 : IsPGroup 3 B := hP3.to_le hBP
  have hKL : F08.KOf8103 L B ≤ L := by
    unfold F08.KOf8103 F08.DerInf8
    exact (Subgroup.map_subtype_le _).trans inf_le_left
  have hPH : P ≤ H := by
    intro x hx
    have hmem : x ∈ ((pCoreOf 2 H : Set G) *
        ((F08.KOf8103 L B ⊓ H : Subgroup G) : Set G) * P) :=
      Set.mem_mul.mpr ⟨1, Set.mem_mul.mpr ⟨1, (pCoreOf 2 H).one_mem, 1,
        (F08.KOf8103 L B ⊓ H).one_mem, by simp⟩, x, hx, by simp⟩
    rwa [← hH.2.2.2] at hmem
  have hPDM : P ≤ D.M := hPH.trans hHM
  have hKDM : F08.KOf8103 L B ≤ D.M := hKH.trans hHM
  have hRC : pCoreOf 2 H ≤ Cen D L :=
    pCore_le_cen_of_Uset_eq_bot hHM hKL hKDM hKH hPL hPDM hPH
      (autOdd_barImage_KP s hF5) hbot
  have hPbar2 : IsPGroup 3 (barImage L P) :=
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).1
  have hPbaridx : ¬ 3 ∣ (barImage L P).index :=
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).2
  have hBbar : F08.NotationB8103 ⊤ (barImage L P) n (barImage L B) :=
    (notationB8103_barImage_iff hPL hP3 hBP).mpr s.notB
  obtain ⟨Y₁, Y₂, hY, -, -, -⟩ :=
    hRad (Bar2 L) n s.isU45 (barImage L P) hPbar2 hPbaridx (barImage L B) hBbar
  obtain ⟨-, -, hKP1, hOne, -, -⟩ := hY Y₁ (by simp)
  have hKbar : barImage L (F08.KOf8103 L B) ≤ Y₁ := by
    rw [barImage_kOf8103 hBL hB3]
    exact le_sup_left.trans hKP1
  have hPbar : barImage L P ≤ Y₁ := le_sup_right.trans hKP1
  have hYnorm : Y₁ ≤ Subgroup.normalizer (pCoreOf 2 Y₁ : Set (Bar2 L)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y₁
  have hHN := H_le_normalizer_barPreimage_pCoreOf s.normal hH hKL hPL hRC hKbar hPbar hYnorm
  exact hOne (pCoreOf_eq_bot_of_le_normalizer_barPreimage s hHM hR hRC hHN)

private theorem holds_bar2 {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) :
    CFSG.LieType.BorelTits.Holds (Bar2 L) 2 := by
  rcases s.isU45 with ⟨h5, -⟩ | ⟨h4, -⟩
  · exact CFSG.LieType.BorelTits.holds_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel h5 (by decide))
  · exact CFSG.LieType.BorelTits.holds_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel h4 (by decide))

private theorem barImage_inf_le_Uset {D : Data G} {L H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (hHM : H ≤ D.M) :
    barImage L (pCoreOf 2 H ⊓ L) ≤ Uset D L h H := by
  intro q hq
  obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hq
  obtain ⟨hmR, -⟩ := Subgroup.mem_inf.mp hm
  have hmH : (m : G) ∈ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hmR
  rw [mem_Uset]
  have hconj : MulAut.conj (uc22p21cPi L m) =
      barRho D L h ⟨(m : G), hHM hmH⟩ := by
    rw [barRho, MonoidHom.comp_apply]
    exact (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_inner L (m : G) m.2).symm
  rw [hconj]
  exact Subgroup.mem_map.mpr
    ⟨⟨(m : G), hHM hmH⟩, Subgroup.mem_subgroupOf.mpr hmR, rfl⟩

private theorem map_Uset_of_mem_Rbar {D : Data G} {L H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} {α : MulAut (Bar2 L)}
    (hα : α ∈ Rbar D L h H) : (Uset D L h H).map α.toMonoidHom = Uset D L h H := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_Uset.mpr ((conj_mem_Rbar_iff hα y).mpr (mem_Uset.mp hy))
  · intro hx
    refine ⟨α⁻¹ x, mem_Uset.mpr ?_, by simp⟩
    have h1 : MulAut.conj (α (α⁻¹ x)) ∈ Rbar D L h H := by
      simpa using mem_Uset.mp hx
    exact (conj_mem_Rbar_iff hα (α⁻¹ x)).mp h1

private theorem map_eq_top_iff_of_mulAut {Y : Type} [Group Y] (α : MulAut Y)
    (X : Subgroup Y) : X.map α.toMonoidHom = ⊤ ↔ X = ⊤ := by
  constructor
  · intro h
    have h2 : (X.map α.toMonoidHom).map (α⁻¹).toMonoidHom =
        (⊤ : Subgroup Y).map (α⁻¹).toMonoidHom := by rw [h]
    have hid : (α⁻¹).toMonoidHom.comp α.toMonoidHom = MonoidHom.id Y := by
      ext y
      simp
    rw [Subgroup.map_map, hid, Subgroup.map_id,
      Subgroup.map_top_of_surjective _ α⁻¹.surjective] at h2
    exact h2
  · rintro rfl
    exact Subgroup.map_top_of_surjective _ α.surjective

private theorem barImage_commutator_le_Uset {D : Data G} {L H K : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (hHM : H ≤ D.M)
    (hKL : K ≤ L) (hKH : K ≤ H) {α : MulAut (Bar2 L)} (hα : α ∈ Rbar D L h H)
    {x : Bar2 L} (hx : x ∈ barImage L K) : α x * x⁻¹ ∈ Uset D L h H := by
  obtain ⟨r, hrR, hrα⟩ := Subgroup.mem_map.mp hα
  obtain ⟨m, hmK, rfl⟩ := uc22p21c_mem_barImage.1 hx
  have hrM : (r : G) ∈ D.M := r.2
  have hmM : (m : G) ∈ D.M := hHM (hKH hmK)
  have hmL : (m : G) ∈ L := hKL hmK
  have hrmL : (r : G) * (m : G) * (r : G)⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp (h hrM) (m : G)).mp hmL
  have hcL : (r : G) * (m : G) * (r : G)⁻¹ * (m : G)⁻¹ ∈ L :=
    L.mul_mem hrmL (L.inv_mem hmL)
  have hrR' : (r : G) ∈ pCoreOf 2 H := Subgroup.mem_subgroupOf.mp hrR
  have hrH : (r : G) ∈ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 H) hrR'
  have hcR : (r : G) * (m : G) * (r : G)⁻¹ * (m : G)⁻¹ ∈ pCoreOf 2 H := by
    have h1 : (m : G) * (r : G)⁻¹ * (m : G)⁻¹ ∈ pCoreOf 2 H :=
      (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hmK)) (r : G)⁻¹).mp
        ((pCoreOf 2 H).inv_mem hrR')
    have h2 := (pCoreOf 2 H).mul_mem hrR' h1
    simpa [mul_assoc] using h2
  have hconj : α (QuotientGroup.mk m : Bar2 L) =
      (QuotientGroup.mk (⟨(r : G) * (m : G) * (r : G)⁻¹, hrmL⟩ : ↥L) : Bar2 L) := by
    rw [← hrα, barRho, MonoidHom.comp_apply,
      CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
    congr 1
  change α (QuotientGroup.mk m : Bar2 L) * (QuotientGroup.mk m : Bar2 L)⁻¹ ∈ Uset D L h H
  rw [hconj, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul]
  refine barImage_inf_le_Uset (D := D) (H := H) hHM ?_
  exact uc22p21c_mem_barImage.2 ⟨⟨_, hcL⟩, Subgroup.mem_inf.mpr ⟨hcR, hcL⟩, rfl⟩

private theorem kOf8103_le (L B : Subgroup G) : F08.KOf8103 L B ≤ L := by
  unfold F08.KOf8103 F08.DerInf8
  exact (Subgroup.map_subtype_le _).trans inf_le_left

private theorem P_le_of_mem_calK8104 {D : Data G} {P K H : Subgroup G}
    (hH : H ∈ calK8104 D P K) : P ≤ H := by
  intro x hx
  have hmem : x ∈ ((pCoreOf 2 H : Set G) * ((K ⊓ H : Subgroup G) : Set G) * P) :=
    Set.mem_mul.mpr ⟨1, Set.mem_mul.mpr ⟨1, (pCoreOf 2 H).one_mem, 1,
      (K ⊓ H).one_mem, by simp⟩, x, hx, by simp⟩
  rwa [← hH.2.2.2] at hmem

private theorem exists_parabolic (hRad : KU45Radical) {D : Data G}
    {L P B H : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n)
    (hH : H ∈ calK8104 D P (F08.KOf8103 L B)) (hU : Uset D L s.normal H ≠ ⊥) :
    ∃ X : Subgroup (Bar2 L),
      X ≠ ⊤ ∧ Subgroup.normalizer (Uset D L s.normal H : Set (Bar2 L)) ≤ X ∧
      Uset D L s.normal H ≤ pCoreOf 2 X ∧
      (∀ T₀ : Sylow 2 (Bar2 L), pCoreOf 2 X ≤ (T₀ : Subgroup (Bar2 L)) →
        Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ X) ∧
      F08.KOf8103 ⊤ (barImage L B) ⊓ pCoreOf 2 X = ⊥ ∧
      (∀ Z : Subgroup (Bar2 L), Z ≠ ⊤ →
        Subgroup.normalizer (Uset D L s.normal H : Set (Bar2 L)) ≤ Z →
        (∃ T₀ : Sylow 2 (Bar2 L),
          Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ Z) → Z = X) := by
  have hHM : H ≤ D.M := hH.1
  have hKH : F08.KOf8103 L B ≤ H := hH.2.2.1
  have hLDM : L ≤ D.M := CFSG.Open.IsSubnormal.le s.hyp.1.1
  have hKL : F08.KOf8103 L B ≤ L := kOf8103_le L B
  have hKDM : F08.KOf8103 L B ≤ D.M := hKH.trans hHM
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hPH : P ≤ H := P_le_of_mem_calK8104 hH
  have hPDM : P ≤ D.M := hPH.trans hHM
  have hBP : B ≤ P := s.notB.2.1
  have hB3 : IsPGroup 3 B := hP3.to_le hBP
  have hBbar : F08.NotationB8103 ⊤ (barImage L P) n (barImage L B) :=
    (notationB8103_barImage_iff hPL hP3 hBP).mpr s.notB
  have hNU : F08.KOf8103 ⊤ (barImage L B) ⊔ barImage L P ≤
      Subgroup.normalizer (Uset D L s.normal H : Set (Bar2 L)) := by
    rw [← barImage_kOf8103 (hBP.trans hPL) hB3]
    exact sup_le (barImage_le_normalizer_Uset s.normal hKL hKDM hKH)
      (barImage_le_normalizer_Uset s.normal hPL hPDM hPH)
  obtain ⟨Y₁, Y₂, hY, hd1, hd2, hlast⟩ := hRad (Bar2 L) n s.isU45 (barImage L P)
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).1
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).2 (barImage L B) hBbar
  obtain ⟨S, X, hXne, hNX, -, hUX, hNS⟩ :=
    holds_bar2 s (Uset D L s.normal H) hU
      (isPGroup_Uset s.normal hHM (center_bar2_eq_bot_of_hyp8102 s.hyp))
  have hKPX : F08.KOf8103 ⊤ (barImage L B) ⊔ barImage L P ≤ X := hNU.trans hNX
  have hXin : X = Y₁ ∨ X = Y₂ := hlast X hXne ⟨S, hNS⟩ hKPX
  have hY1 := hY Y₁ (by simp)
  have hY2 := hY Y₂ (by simp)
  have hfacts : (∀ T₀ : Sylow 2 (Bar2 L), pCoreOf 2 X ≤ (T₀ : Subgroup (Bar2 L)) →
        Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ X) ∧
      F08.KOf8103 ⊤ (barImage L B) ⊓ pCoreOf 2 X = ⊥ := by
    rcases hXin with h | h
    · rw [h]; exact ⟨hY1.2.2.2.2.2, hY1.2.2.2.2.1⟩
    · rw [h]; exact ⟨hY2.2.2.2.2.2, hY2.2.2.2.2.1⟩
  refine ⟨X, hXne, hNX, hUX, hfacts.1, hfacts.2, ?_⟩
  intro Z hZne hNZ hSyl
  have hUZ : Uset D L s.normal H ≤ Z := Subgroup.le_normalizer.trans hNZ
  have hZin : Z = Y₁ ∨ Z = Y₂ := hlast Z hZne hSyl (hNU.trans hNZ)
  rcases hXin with hX1 | hX2 <;> rcases hZin with hZ1 | hZ2
  · rw [hX1, hZ1]
  · exfalso
    have hle : Uset D L s.normal H ≤ pCoreOf 2 Y₁ ⊓ Y₂ := le_inf (hX1 ▸ hUX) (hZ2 ▸ hUZ)
    rw [hd1] at hle
    exact hU (le_bot_iff.mp hle)
  · exfalso
    have hle : Uset D L s.normal H ≤ pCoreOf 2 Y₂ ⊓ Y₁ := le_inf (hX2 ▸ hUX) (hZ1 ▸ hUZ)
    rw [hd2] at hle
    exact hU (le_bot_iff.mp hle)
  · rw [hX2, hZ2]

private theorem map_parabolic_of_mem_Rbar {D : Data G} {L H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} {X : Subgroup (Bar2 L)}
    {S : Sylow 2 (Bar2 L)} (hXne : X ≠ ⊤)
    (hNX : Subgroup.normalizer (Uset D L h H : Set (Bar2 L)) ≤ X)
    (hNS : Subgroup.normalizer ((S : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ X)
    (hunique : ∀ Z : Subgroup (Bar2 L), Z ≠ ⊤ →
      Subgroup.normalizer (Uset D L h H : Set (Bar2 L)) ≤ Z →
      (∃ T₀ : Sylow 2 (Bar2 L),
        Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ Z) → Z = X)
    {α : MulAut (Bar2 L)} (hα : α ∈ Rbar D L h H) :
    X.map α.toMonoidHom = X ∧ (pCoreOf 2 X).map α.toMonoidHom = pCoreOf 2 X := by
  have hUα : (Uset D L h H).map α.toMonoidHom = Uset D L h H := map_Uset_of_mem_Rbar hα
  have htop : X.map α.toMonoidHom ≠ ⊤ := fun htop =>
    hXne ((map_eq_top_iff_of_mulAut α X).mp htop)
  have hNα : Subgroup.normalizer (Uset D L h H : Set (Bar2 L)) ≤ X.map α.toMonoidHom := by
    have h1 : (Subgroup.normalizer (Uset D L h H : Set (Bar2 L))).map α.toMonoidHom =
        Subgroup.normalizer (Uset D L h H : Set (Bar2 L)) := by
      rw [Subgroup.map_equiv_normalizer_eq, hUα]
    rw [← h1]
    exact Subgroup.map_mono hNX
  have hXeq : X.map α.toMonoidHom = X := by
    have hsurj : Function.Surjective ⇑(α.toMonoidHom) := fun x => α.surjective x
    refine hunique _ htop hNα ⟨Sylow.mapSurjective (f := α.toMonoidHom) hsurj S, ?_⟩
    rw [Sylow.coe_mapSurjective (hf := hsurj) (P := S), ← Subgroup.map_equiv_normalizer_eq]
    exact Subgroup.map_mono hNS
  refine ⟨hXeq, ?_⟩
  rw [← CFSG.LieType.BorelTits.pCoreOf_map_mulEquiv 2 α X, hXeq]

private theorem coe_eq_mul_of_mem_calK8104 {D : Data G} {P K H : Subgroup G}
    (hH : H ∈ calK8104 D P K) :
    (H : Set G) = (pCoreOf 2 H : Set G) * (K : Set G) * P := by
  have hinf : K ⊓ H = K := le_antisymm inf_le_left (le_inf le_rfl hH.2.2.1)
  rw [hH.2.2.2, hinf]

private theorem le_normalizer_barPreimage_of_Rbar {D : Data G} {L H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (hHM : H ≤ D.M) {Y : Subgroup (Bar2 L)}
    (hY : ∀ α ∈ Rbar D L h H, Y.map α.toMonoidHom = Y) :
    pCoreOf 2 H ≤ Subgroup.normalizer (barPreimage L Y : Set G) := by
  intro r hr
  have hrM : r ∈ D.M := hHM ((CFSG.LieType.BorelTits.pCoreOf_le 2 H) hr)
  have hYα : Y.map (barRho D L h ⟨r, hrM⟩).toMonoidHom = Y :=
    hY _ (Subgroup.mem_map.mpr ⟨⟨r, hrM⟩, Subgroup.mem_subgroupOf.mpr hr, rfl⟩)
  have hYα' : Y.map ((barRho D L h ⟨r, hrM⟩)⁻¹).toMonoidHom = Y := by
    have h1 := congrArg (Subgroup.map ((barRho D L h ⟨r, hrM⟩)⁻¹).toMonoidHom) hYα
    rw [Subgroup.map_map, show ((barRho D L h ⟨r, hrM⟩)⁻¹).toMonoidHom.comp
      (barRho D L h ⟨r, hrM⟩).toMonoidHom = MonoidHom.id (Bar2 L) from by ext z; simp,
      Subgroup.map_id] at h1
    exact h1.symm
  have hiff : ∀ y : Bar2 L, barRho D L h ⟨r, hrM⟩ y ∈ Y ↔ y ∈ Y := by
    intro y
    constructor
    · intro hy
      have h2 : y ∈ Y.map ((barRho D L h ⟨r, hrM⟩)⁻¹).toMonoidHom := by
        simpa using Subgroup.mem_map_of_mem ((barRho D L h ⟨r, hrM⟩)⁻¹).toMonoidHom hy
      rwa [hYα'] at h2
    · intro hy
      rw [← hYα]
      exact Subgroup.mem_map_of_mem _ hy
  rw [Subgroup.mem_normalizer_iff]
  intro g
  rw [uc22p21c_mem_barPreimage, uc22p21c_mem_barPreimage]
  constructor
  · rintro ⟨hgL, hgY⟩
    have hgL' : r * g * r⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp (h hrM) g).mp hgL
    refine ⟨hgL', ?_⟩
    have heq : uc22p21cPi L ⟨r * g * r⁻¹, hgL'⟩ =
        barRho D L h ⟨r, hrM⟩ (uc22p21cPi L ⟨g, hgL⟩) := by
      change (QuotientGroup.mk (⟨r * g * r⁻¹, hgL'⟩ : ↥L) : Bar2 L) =
        barRho D L h ⟨r, hrM⟩ (QuotientGroup.mk (⟨g, hgL⟩ : ↥L) : Bar2 L)
      rw [barRho, MonoidHom.comp_apply, CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
      congr 1
    rw [heq]
    exact (hiff _).mpr hgY
  · rintro ⟨hgL', hgY⟩
    have hgL : g ∈ L := by
      have h1 := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem (h hrM)) (r * g * r⁻¹)).mp hgL'
      rwa [show r⁻¹ * (r * g * r⁻¹) * (r⁻¹)⁻¹ = g from by group] at h1
    refine ⟨hgL, ?_⟩
    have heq : uc22p21cPi L ⟨r * g * r⁻¹, hgL'⟩ =
        barRho D L h ⟨r, hrM⟩ (uc22p21cPi L ⟨g, hgL⟩) := by
      change (QuotientGroup.mk (⟨r * g * r⁻¹, hgL'⟩ : ↥L) : Bar2 L) =
        barRho D L h ⟨r, hrM⟩ (QuotientGroup.mk (⟨g, hgL⟩ : ↥L) : Bar2 L)
      rw [barRho, MonoidHom.comp_apply, CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
      congr 1
    rw [heq] at hgY
    exact (hiff _).mp hgY

private theorem pCoreOf_parabolic_eq_Uset (hRad : KU45Radical) {D : Data G}
    {L P B H : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n)
    (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    (hR : ∀ R' : Subgroup G, R' ≤ D.M → IsPGroup 2 R' → H ≤ normalizer (R' : Set G) →
      pCoreOf 2 H ≤ R' → R' = pCoreOf 2 H)
    {X : Subgroup (Bar2 L)} (hUX : Uset D L s.normal H ≤ pCoreOf 2 X)
    (hKPX : F08.KOf8103 ⊤ (barImage L B) ⊔ barImage L P ≤ X)
    (hRnorm : ∀ α ∈ Rbar D L s.normal H,
      (pCoreOf 2 X).map α.toMonoidHom = pCoreOf 2 X) :
    pCoreOf 2 X = Uset D L s.normal H := by
  have hHM : H ≤ D.M := hH.1
  have hKH : F08.KOf8103 L B ≤ H := hH.2.2.1
  have hLDM : L ≤ D.M := CFSG.Open.IsSubnormal.le s.hyp.1.1
  have hKL : F08.KOf8103 L B ≤ L := kOf8103_le L B
  have hKDM : F08.KOf8103 L B ≤ D.M := hKH.trans hHM
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hPH : P ≤ H := P_le_of_mem_calK8104 hH
  have hPDM : P ≤ D.M := hPH.trans hHM
  have hBP : B ≤ P := s.notB.2.1
  have hB3 : IsPGroup 3 B := hP3.to_le hBP
  have hKbar : barImage L (F08.KOf8103 L B) ≤ X := by
    rw [barImage_kOf8103 (hBP.trans hPL) hB3]
    exact le_sup_left.trans hKPX
  have hPbar : barImage L P ≤ X := le_sup_right.trans hKPX
  have hXnorm : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set (Bar2 L)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hKY : F08.KOf8103 L B ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 X) : Set G) :=
    le_normalizer_barPreimage_of_le_normalizer hKL (hKbar.trans hXnorm)
  have hPY : P ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 X) : Set G) :=
    le_normalizer_barPreimage_of_le_normalizer hPL (hPbar.trans hXnorm)
  have hRY : pCoreOf 2 H ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 X) : Set G) :=
    le_normalizer_barPreimage_of_Rbar hHM hRnorm
  have hHY : H ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 X) : Set G) :=
    H_le_normalizer_of_isSylowOf_cen (coe_eq_mul_of_mem_calK8104 hH) hRY hKY hPY
  have hY2 : IsPGroup 2 (barPreimage L (pCoreOf 2 X)) :=
    isPGroup_barPreimage (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hsup : IsPGroup 2 ↥(barPreimage L (pCoreOf 2 X) ⊔ pCoreOf 2 H) :=
    isPGroup_sup_of_le_normalizer (H := barPreimage L (pCoreOf 2 X)) (K := pCoreOf 2 H)
      hY2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hRY
  have hkey := hR (barPreimage L (pCoreOf 2 X) ⊔ pCoreOf 2 H)
    (sup_le ((uc22p21c_barPreimage_le L (pCoreOf 2 X)).trans hLDM)
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHM)) hsup
    (le_normalizer_sup_of_le_normalizer hHY (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
    le_sup_right
  refine le_antisymm ?_ hUX
  rw [← barImage_barPreimage L (pCoreOf 2 X)]
  exact (barImage_mono (M := L) (le_inf (le_sup_left.trans hkey.le)
    (uc22p21c_barPreimage_le L (pCoreOf 2 X)))).trans
    (barImage_inf_le_Uset (D := D) (H := H) hHM)

private theorem barPreimage_pCoreOf_le_R (hRad : KU45Radical) {D : Data G}
    {L P B H : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n)
    (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    (hR : ∀ R' : Subgroup G, R' ≤ D.M → IsPGroup 2 R' → H ≤ normalizer (R' : Set G) →
      pCoreOf 2 H ≤ R' → R' = pCoreOf 2 H)
    {X : Subgroup (Bar2 L)}
    (hKPX : F08.KOf8103 ⊤ (barImage L B) ⊔ barImage L P ≤ X)
    (hRnorm : ∀ α ∈ Rbar D L s.normal H,
      (pCoreOf 2 X).map α.toMonoidHom = pCoreOf 2 X) :
    barPreimage L (pCoreOf 2 X) ≤ pCoreOf 2 H := by
  have hHM : H ≤ D.M := hH.1
  have hKH : F08.KOf8103 L B ≤ H := hH.2.2.1
  have hKL : F08.KOf8103 L B ≤ L := kOf8103_le L B
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hPH : P ≤ H := P_le_of_mem_calK8104 hH
  have hBP : B ≤ P := s.notB.2.1
  have hB3 : IsPGroup 3 B := hP3.to_le hBP
  have hKbar : barImage L (F08.KOf8103 L B) ≤ X := by
    rw [barImage_kOf8103 (hBP.trans hPL) hB3]
    exact le_sup_left.trans hKPX
  have hPbar : barImage L P ≤ X := le_sup_right.trans hKPX
  have hXnorm : X ≤ Subgroup.normalizer (pCoreOf 2 X : Set (Bar2 L)) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X
  have hKY : F08.KOf8103 L B ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 X) : Set G) :=
    le_normalizer_barPreimage_of_le_normalizer hKL (hKbar.trans hXnorm)
  have hPY : P ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 X) : Set G) :=
    le_normalizer_barPreimage_of_le_normalizer hPL (hPbar.trans hXnorm)
  have hRY : pCoreOf 2 H ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 X) : Set G) :=
    le_normalizer_barPreimage_of_Rbar hHM hRnorm
  have hHY : H ≤ Subgroup.normalizer (barPreimage L (pCoreOf 2 X) : Set G) :=
    H_le_normalizer_of_isSylowOf_cen (coe_eq_mul_of_mem_calK8104 hH) hRY hKY hPY
  have hY2 : IsPGroup 2 (barPreimage L (pCoreOf 2 X)) :=
    isPGroup_barPreimage (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hsup : IsPGroup 2 ↥(barPreimage L (pCoreOf 2 X) ⊔ pCoreOf 2 H) :=
    isPGroup_sup_of_le_normalizer (H := barPreimage L (pCoreOf 2 X)) (K := pCoreOf 2 H)
      hY2 (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hRY
  have hkey := hR (barPreimage L (pCoreOf 2 X) ⊔ pCoreOf 2 H)
    (sup_le ((uc22p21c_barPreimage_le L (pCoreOf 2 X)).trans
      (CFSG.Open.IsSubnormal.le s.hyp.1.1))
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHM)) hsup
    (le_normalizer_sup_of_le_normalizer hHY (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H))
    le_sup_right
  exact le_sup_left.trans hkey.le

private theorem barImage_P_inf_eq_bot {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) {X : Subgroup (Bar2 L)}
    (hO2 : pCoreOf 2 X = Uset D L s.normal H) :
    barImage L P ⊓ pCoreOf 2 X = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hxP, hxO⟩
  exact Subgroup.mem_bot.mpr (CFSG.Quasithin.A1b.eq_one_of_mem_pGroups (p := 3) (q := 2)
    (by norm_num) (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).1
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X) hxP hxO)

private theorem exists_map_conj_eq_of_isSylowOf {p : ℕ} [Fact p.Prime] {K A B : Subgroup G}
    (hA : IsSylowOf p A K) (hB : IsSylowOf p B K) :
    ∃ k ∈ K, B.map (MulAut.conj k).toMonoidHom = A := by
  obtain ⟨SA, hSA⟩ := hA.exists_sylow_eq_subgroupOf
  obtain ⟨SB, hSB⟩ := hB.exists_sylow_eq_subgroupOf
  obtain ⟨k, hk⟩ := @MulAction.IsPretransitive.exists_smul_eq K (Sylow p K)
    inferInstance inferInstance SB SA
  have hmap : (SB : Subgroup K).map (MulAut.conj k).toMonoidHom = (SA : Subgroup K) := by
    have h := congrArg (fun R : Sylow p K => (R : Subgroup K)) hk
    rw [Sylow.coe_subgroup_smul] at h
    rw [← h]
    ext z
    rw [Subgroup.mem_smul_pointwise_iff_exists, Subgroup.mem_map]
    exact ⟨fun ⟨g, hg, hz⟩ => ⟨g, hg, by simpa [MulAut.smul_def] using hz⟩,
      fun ⟨g, hg, hz⟩ => ⟨g, hg, by simpa [MulAut.smul_def] using hz⟩⟩
  refine ⟨(k : G), k.2, ?_⟩
  have hBeq : B = (SB : Subgroup K).map K.subtype := by
    rw [hSB, Subgroup.map_subgroupOf_eq_of_le hB.le]
  have hAeq : A = (SA : Subgroup K).map K.subtype := by
    rw [hSA, Subgroup.map_subgroupOf_eq_of_le hA.le]
  have hcomp : (MulAut.conj (k : G)).toMonoidHom.comp K.subtype =
      K.subtype.comp (MulAut.conj k).toMonoidHom := by
    ext z
    rfl
  rw [hBeq, hAeq, Subgroup.map_map, ← hmap, Subgroup.map_map, hcomp]

private theorem exists_mul_of_mem_sup {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) {X : Subgroup (Bar2 L)}
    (hPX : barImage L P ≤ X) {y : Bar2 L}
    (hy : y ∈ barImage L P ⊔ pCoreOf 2 X) :
    ∃ u ∈ pCoreOf 2 X, ∃ p ∈ barImage L P, u * p = y := by
  let K : Subgroup (Bar2 L) := barImage L P ⊔ pCoreOf 2 X
  have hPK : barImage L P ≤ K := le_sup_left
  have hUK : pCoreOf 2 X ≤ K := le_sup_right
  have hsup : (pCoreOf 2 X).subgroupOf K ⊔ (barImage L P).subgroupOf K = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (A := pCoreOf 2 X) (A' := barImage L P) (B := K) hUK hPK]
    rw [sup_comm]
    exact Subgroup.subgroupOf_self K
  have hyK : (⟨y, hy⟩ : K) ∈
      (pCoreOf 2 X).subgroupOf K ⊔ (barImage L P).subgroupOf K := by
    rw [hsup]
    trivial
  have hUN : pCoreOf 2 X ≤ Subgroup.normalizer (pCoreOf 2 X : Set (Bar2 L)) :=
    Subgroup.le_normalizer
  have hPN : barImage L P ≤ Subgroup.normalizer (pCoreOf 2 X : Set (Bar2 L)) := by
    intro z hz
    exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X (hPX hz)
  have hKnorm : K ≤ Subgroup.normalizer (pCoreOf 2 X : Set (Bar2 L)) :=
    sup_le hPN hUN
  let : ((pCoreOf 2 X).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUK).mpr hKnorm
  rcases (Subgroup.mem_sup_of_normal_left (s := (pCoreOf 2 X).subgroupOf K)
    (t := (barImage L P).subgroupOf K)).mp hyK with ⟨u, hu, p, hp, hup⟩
  exact ⟨(u : Bar2 L), Subgroup.mem_subgroupOf.mp hu,
    (p : Bar2 L), Subgroup.mem_subgroupOf.mp hp, congrArg Subtype.val hup⟩

private theorem alpha_prime_fixes_P {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    {X : Subgroup (Bar2 L)} (hPX : barImage L P ≤ X)
    (hO2 : pCoreOf 2 X = Uset D L s.normal H)
    {α : MulAut (Bar2 L)} (hα : α ∈ Rbar D L s.normal H)
    {u : Bar2 L} (hu : u ∈ pCoreOf 2 X)
    (hPu : (barImage L P).map (MulAut.conj u).toMonoidHom =
      (barImage L P).map α.toMonoidHom) :
    ∀ x ∈ barImage L P, ((MulAut.conj u)⁻¹ * α) x = x := by
  have hHM : H ≤ D.M := hH.1
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hPH : P ≤ H := P_le_of_mem_calK8104 hH
  have hPα : (barImage L P).map ((MulAut.conj u)⁻¹ * α).toMonoidHom =
      barImage L P := by
    have h1 : ((barImage L P).map (MulAut.conj u).toMonoidHom).map
        ((MulAut.conj u)⁻¹).toMonoidHom =
        ((barImage L P).map α.toMonoidHom).map ((MulAut.conj u)⁻¹).toMonoidHom := by
      rw [hPu]
    rw [Subgroup.map_map, Subgroup.map_map,
      show ((MulAut.conj u)⁻¹).toMonoidHom.comp (MulAut.conj u).toMonoidHom =
        MonoidHom.id _ from by ext z; simp, Subgroup.map_id] at h1
    exact h1.symm
  intro x hx
  have hmem : ((MulAut.conj u)⁻¹ * α) x ∈ barImage L P := by
    rw [← hPα]
    exact Subgroup.mem_map_of_mem _ hx
  have hcommα : α x * x⁻¹ ∈ pCoreOf 2 X := by
    have h := barImage_commutator_le_Uset hHM hPL hPH hα hx
    rwa [← hO2] at h
  have hxu : x * u * x⁻¹ ∈ pCoreOf 2 X := by
    have hxX : x ∈ X := hPX hx
    have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 X : Set (Bar2 L)) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hxX
    exact (Subgroup.mem_normalizer_iff.mp hxN u).mp hu
  have hcomm : ((MulAut.conj u)⁻¹ * α) x * x⁻¹ ∈ pCoreOf 2 X := by
    have hval : ((MulAut.conj u)⁻¹ * α) x = u⁻¹ * (α x) * u := by
      simp [MulAut.conj_apply, mul_assoc]
    rw [hval]
    have heq : u⁻¹ * (α x) * u * x⁻¹ = (u⁻¹ * (α x * x⁻¹)) * (x * u * x⁻¹) := by
      group
    rw [heq]
    exact (pCoreOf 2 X).mul_mem
      ((pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hu) hcommα) hxu
  have hin : ((MulAut.conj u)⁻¹ * α) x * x⁻¹ ∈ barImage L P ⊓ pCoreOf 2 X :=
    ⟨(barImage L P).mul_mem hmem ((barImage L P).inv_mem hx), hcomm⟩
  rw [barImage_P_inf_eq_bot s hO2] at hin
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hin)

private theorem map_eq_of_subgroupOf_characteristic {Y : Type} [Group Y] {H K : Subgroup Y}
    (hKH : K ≤ H) (hK : (K.subgroupOf H).Characteristic) {α : MulAut Y}
    (hH : H.map α.toMonoidHom = H) : K.map α.toMonoidHom = K := by
  let e : ↥H ≃* ↥(H.map α.toMonoidHom) :=
    Subgroup.equivMapOfInjective H α.toMonoidHom α.injective
  let ϕ : ↥H ≃* ↥H := e.trans (MulEquiv.subgroupCongr hH)
  have hϕ : ∀ x : ↥H, (ϕ x : Y) = α x := by
    intro x
    rfl
  have hKmap : (K.subgroupOf H).map ϕ.toMonoidHom = K.subgroupOf H :=
    (Subgroup.characteristic_iff_map_eq.mp hK) ϕ
  have hmap_sub : (K.subgroupOf H).map ϕ.toMonoidHom =
      (K.map α.toMonoidHom).subgroupOf H := by
    ext x
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine Subgroup.mem_subgroupOf.mpr ?_
      show (ϕ k : Y) ∈ Subgroup.map α.toMonoidHom K
      rw [hϕ]
      exact Subgroup.mem_map_of_mem α.toMonoidHom (Subgroup.mem_subgroupOf.mp hk)
    · intro hx
      obtain ⟨k, hk, hkx⟩ := Subgroup.mem_map.mp
        (show (x : Y) ∈ K.map α.toMonoidHom from Subgroup.mem_subgroupOf.mp hx)
      have hkH : k ∈ H := by
        have hxmap : (x : Y) ∈ H.map α.toMonoidHom := by
          rw [hH]; exact x.2
        obtain ⟨h, hh, hαh⟩ := Subgroup.mem_map.mp hxmap
        have : k = h := α.injective (hkx.trans hαh.symm)
        rwa [this]
      refine ⟨⟨k, hkH⟩, ?_, ?_⟩
      · exact Subgroup.mem_subgroupOf.mpr hk
      · exact Subtype.ext (by
          show (ϕ ⟨k, hkH⟩ : Y) = (x : Y)
          rw [hϕ]
          exact hkx)
  have hsub_eq : (K.map α.toMonoidHom).subgroupOf H = K.subgroupOf H := by
    rw [← hmap_sub, hKmap]
  have hKH' : K.map α.toMonoidHom ≤ H := by
    rw [← hH]
    exact Subgroup.map_mono hKH
  calc K.map α.toMonoidHom
      = Subgroup.map H.subtype ((K.map α.toMonoidHom).subgroupOf H) := by
          rw [Subgroup.map_subgroupOf_eq_of_le hKH']
    _ = Subgroup.map H.subtype (K.subgroupOf H) := by rw [hsub_eq]
    _ = K := Subgroup.map_subgroupOf_eq_of_le hKH

private theorem alpha_prime_normalizes_centralizer {D : Data G} {L P B : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) {α : MulAut (Bar2 L)} {u : Bar2 L}
    (hPfix : ∀ x ∈ barImage L P, ((MulAut.conj u)⁻¹ * α) x = x) :
    (Subgroup.centralizer (barImage L B : Set (Bar2 L))).map
        ((MulAut.conj u)⁻¹ * α).toMonoidHom =
      Subgroup.centralizer (barImage L B : Set (Bar2 L)) := by
  let α' : MulAut (Bar2 L) := (MulAut.conj u)⁻¹ * α
  change (Subgroup.centralizer (barImage L B : Set (Bar2 L))).map α'.toMonoidHom =
    Subgroup.centralizer (barImage L B : Set (Bar2 L))
  have hBP : B ≤ P := s.notB.2.1
  have hBbarP : barImage L B ≤ barImage L P := barImage_mono (M := L) hBP
  have hBfix : ∀ b ∈ barImage L B, α' b = b := fun b hb => hPfix b (hBbarP hb)
  have himage : α'.toMonoidHom '' (barImage L B : Set (Bar2 L)) =
      (barImage L B : Set (Bar2 L)) := Set.EqOn.image_eq_self hBfix
  have hBfix_inv : ∀ b ∈ barImage L B, (α'⁻¹) b = b := by
    intro b hb
    calc (α'⁻¹) b = (α'⁻¹) (α' b) := by rw [hBfix b hb]
      _ = b := by simp
  have himage_inv : (α'⁻¹).toMonoidHom '' (barImage L B : Set (Bar2 L)) =
      (barImage L B : Set (Bar2 L)) := Set.EqOn.image_eq_self hBfix_inv
  have hle : (Subgroup.centralizer (barImage L B : Set (Bar2 L))).map α'.toMonoidHom ≤
      Subgroup.centralizer (barImage L B : Set (Bar2 L)) := by
    have h := Subgroup.map_centralizer_le_centralizer_image (barImage L B : Set (Bar2 L))
      α'.toMonoidHom
    rwa [himage] at h
  have hge : Subgroup.centralizer (barImage L B : Set (Bar2 L)) ≤
      (Subgroup.centralizer (barImage L B : Set (Bar2 L))).map α'.toMonoidHom := by
    have h1 : (Subgroup.centralizer (barImage L B : Set (Bar2 L))).map (α'⁻¹).toMonoidHom ≤
        Subgroup.centralizer (barImage L B : Set (Bar2 L)) := by
      have h := Subgroup.map_centralizer_le_centralizer_image (barImage L B : Set (Bar2 L))
        (α'⁻¹).toMonoidHom
      rwa [himage_inv] at h
    have h2 := Subgroup.map_mono h1 (f := α'.toMonoidHom)
    rwa [Subgroup.map_map,
      show α'.toMonoidHom.comp (α'⁻¹).toMonoidHom = MonoidHom.id _ from by ext z; simp,
      Subgroup.map_id] at h2
  exact le_antisymm hle hge

private theorem map_kOf8103_of_map_centralizer {L B : Subgroup G} {β : MulAut (Bar2 L)}
    (hHmap : (Subgroup.centralizer (barImage L B : Set (Bar2 L))).map β.toMonoidHom =
      Subgroup.centralizer (barImage L B : Set (Bar2 L))) :
    (F08.KOf8103 ⊤ (barImage L B)).map β.toMonoidHom =
      F08.KOf8103 ⊤ (barImage L B) := by
  let Hc : Subgroup (Bar2 L) := Subgroup.centralizer (barImage L B : Set (Bar2 L))
  change Hc.map β.toMonoidHom = Hc at hHmap
  have hKdef : F08.KOf8103 ⊤ (barImage L B) =
      Subgroup.map Hc.subtype (CFSG.perfectResidual ↥Hc) := by
    unfold F08.KOf8103 F08.DerInf8 CFSG.perfectResidual
    rw [top_inf_eq]
  have hsub : (Subgroup.map Hc.subtype (CFSG.perfectResidual ↥Hc)).subgroupOf Hc =
      CFSG.perfectResidual ↥Hc := by
    ext x
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_map]
    constructor
    · rintro ⟨k, hk, hkx⟩
      exact (Subtype.ext hkx) ▸ hk
    · intro hx
      exact ⟨x, hx, rfl⟩
  have hKchar : ((F08.KOf8103 ⊤ (barImage L B)).subgroupOf Hc).Characteristic := by
    rw [hKdef, hsub]
    exact CFSG.perfectResidual_characteristic'
  have hKH : F08.KOf8103 ⊤ (barImage L B) ≤ Hc := by
    rw [hKdef]
    exact Subgroup.map_subtype_le _
  exact map_eq_of_subgroupOf_characteristic hKH hKchar hHmap

private theorem alpha_prime_normalizes_K {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    {X : Subgroup (Bar2 L)} (hPX : barImage L P ≤ X)
    (hO2 : pCoreOf 2 X = Uset D L s.normal H)
    {α : MulAut (Bar2 L)} (hα : α ∈ Rbar D L s.normal H)
    {u : Bar2 L} (hu : u ∈ pCoreOf 2 X)
    (hPfix : ∀ x ∈ barImage L P, ((MulAut.conj u)⁻¹ * α) x = x) :
    (F08.KOf8103 ⊤ (barImage L B)).map ((MulAut.conj u)⁻¹ * α).toMonoidHom =
      F08.KOf8103 ⊤ (barImage L B) := by
  exact map_kOf8103_of_map_centralizer (alpha_prime_normalizes_centralizer s hPfix)

private theorem alpha_prime_fixes_K {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    {X : Subgroup (Bar2 L)} (hKbarX : F08.KOf8103 ⊤ (barImage L B) ≤ X)
    (hO2 : pCoreOf 2 X = Uset D L s.normal H)
    (hKbarInf : F08.KOf8103 ⊤ (barImage L B) ⊓ pCoreOf 2 X = ⊥)
    {α : MulAut (Bar2 L)} (hα : α ∈ Rbar D L s.normal H)
    {u : Bar2 L} (hu : u ∈ pCoreOf 2 X)
    (hKn : (F08.KOf8103 ⊤ (barImage L B)).map ((MulAut.conj u)⁻¹ * α).toMonoidHom =
      F08.KOf8103 ⊤ (barImage L B)) :
    ∀ x ∈ F08.KOf8103 ⊤ (barImage L B), ((MulAut.conj u)⁻¹ * α) x = x := by
  let α' : MulAut (Bar2 L) := (MulAut.conj u)⁻¹ * α
  have hHM : H ≤ D.M := hH.1
  have hKH : F08.KOf8103 L B ≤ H := hH.2.2.1
  have hKL : F08.KOf8103 L B ≤ L := kOf8103_le L B
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hBP : B ≤ P := s.notB.2.1
  have hBL : B ≤ L := hBP.trans hPL
  have hB3 : IsPGroup 3 B := s.hyp.2.2.2.2.isPGroup.to_le hBP
  intro x hx
  have hcommα : α x * x⁻¹ ∈ pCoreOf 2 X := by
    have hx' : x ∈ barImage L (F08.KOf8103 L B) := by
      rw [barImage_kOf8103 hBL hB3]
      exact hx
    have h := barImage_commutator_le_Uset hHM hKL hKH hα hx'
    rwa [← hO2] at h
  have hxu : x * u * x⁻¹ ∈ pCoreOf 2 X := by
    have hxX : x ∈ X := hKbarX hx
    have hxN : x ∈ Subgroup.normalizer (pCoreOf 2 X : Set (Bar2 L)) :=
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X hxX
    exact (Subgroup.mem_normalizer_iff.mp hxN u).mp hu
  have hcomm : α' x * x⁻¹ ∈ pCoreOf 2 X := by
    have hval : α' x = u⁻¹ * (α x) * u := by
      simp [α', MulAut.conj_apply, mul_assoc]
    rw [hval]
    have heq : u⁻¹ * (α x) * u * x⁻¹ = (u⁻¹ * (α x * x⁻¹)) * (x * u * x⁻¹) := by
      group
    rw [heq]
    exact (pCoreOf 2 X).mul_mem
      ((pCoreOf 2 X).mul_mem ((pCoreOf 2 X).inv_mem hu) hcommα) hxu
  have hmem : α' x ∈ F08.KOf8103 ⊤ (barImage L B) := by
    rw [← hKn]
    exact Subgroup.mem_map_of_mem α'.toMonoidHom hx
  have hin : α' x * x⁻¹ ∈ F08.KOf8103 ⊤ (barImage L B) ⊓ pCoreOf 2 X :=
    ⟨(F08.KOf8103 ⊤ (barImage L B)).mul_mem hmem
      ((F08.KOf8103 ⊤ (barImage L B)).inv_mem hx), hcomm⟩
  rw [hKbarInf] at hin
  exact mul_inv_eq_one.mp (Subgroup.mem_bot.mp hin)

private theorem exists_conj_P_eq_of_mem_Rbar {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    {X : Subgroup (Bar2 L)} (hPX : barImage L P ≤ X)
    (hO2 : pCoreOf 2 X = Uset D L s.normal H)
    {α : MulAut (Bar2 L)} (hα : α ∈ Rbar D L s.normal H) :
    ∃ u ∈ pCoreOf 2 X, (barImage L P).map (MulAut.conj u).toMonoidHom =
      (barImage L P).map α.toMonoidHom := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hHM : H ≤ D.M := hH.1
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hPH : P ≤ H := P_le_of_mem_calK8104 hH
  have hP3 : IsPGroup 3 (barImage L P) :=
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).1
  have hPidx : ¬ 3 ∣ (barImage L P).index :=
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).2
  have hPsylTop : IsSylowOf 3 (barImage L P) ⊤ := by
    rw [CFSG.ABGLocalTools.isSylowOf_iff]
    exact ⟨le_top, hP3, by simpa using hPidx⟩
  let K : Subgroup (Bar2 L) := barImage L P ⊔ pCoreOf 2 X
  have hPK : barImage L P ≤ K := le_sup_left
  have hPsylK : IsSylowOf 3 (barImage L P) K := hPsylTop.of_le hPK le_top
  have hαP : (barImage L P).map α.toMonoidHom ≤ K := by
    rintro _ ⟨x, hx, rfl⟩
    change α x ∈ K
    have hcomm := barImage_commutator_le_Uset hHM hPL hPH hα hx
    rw [← hO2] at hcomm
    have hx' : α x = (α x * x⁻¹) * x := by group
    rw [hx']
    exact K.mul_mem (Subgroup.mem_sup_right hcomm) (Subgroup.mem_sup_left hx)
  have hαsylK : IsSylowOf 3 ((barImage L P).map α.toMonoidHom) K :=
    CFSG.ABGLocalTools.isSylowOf_of_card hαP
      (by rw [Subgroup.card_map_of_injective α.injective]; exact hPsylK.card_eq)
  obtain ⟨y, hyK, hy⟩ := exists_map_conj_eq_of_isSylowOf hαsylK hPsylK
  obtain ⟨u, hu, p, hp, hup⟩ := exists_mul_of_mem_sup (H := H) s hPX (y := y) hyK
  refine ⟨u, hu, ?_⟩
  have hy' : u * p = y := hup
  have hPconj : (barImage L P).map (MulAut.conj p).toMonoidHom = barImage L P :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hp)
  have hmap : (barImage L P).map (MulAut.conj y).toMonoidHom =
      (barImage L P).map (MulAut.conj (u : Bar2 L)).toMonoidHom := by
    rw [← hy', map_mul]
    change (barImage L P).map ((MulAut.conj u).toMonoidHom.comp
      (MulAut.conj p).toMonoidHom) = _
    rw [← Subgroup.map_map, hPconj]
  exact hmap.symm.trans hy

private theorem isSylowOf_barImage_inf {D : Data G} {L T : Subgroup G}
    (hT : IsSylowOf 2 T D.M) (hL : L ≤ D.M) (hN : D.M ≤ normalizer (L : Set G)) :
    IsSylowOf 2 (barImage L (T ⊓ L)) ⊤ := by
  have hTL : IsSylowOf 2 (T ⊓ L) L := hT.inf_of_le_normalizer hL hN
  have hbar := isPGroup_barImage_of_isSylowOf Nat.prime_two hTL
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff]
  exact ⟨le_top, hbar.1, by simpa using hbar.2⟩

private theorem preimage_Rbar_eq_sup_cen {D : Data G} {L H : Subgroup G}
    (hHM : H ≤ D.M) (h : D.M ≤ normalizer (L : Set G)) :
    ((Rbar D L h H).comap (barRho D L h)).map D.M.subtype =
      pCoreOf 2 H ⊔ Cen D L := by
  have hHle : pCoreOf 2 H ≤ D.M := (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hHM
  have hRbar : Rbar D L h H = ((pCoreOf 2 H).subgroupOf D.M).map (barRho D L h) := rfl
  rw [hRbar, Subgroup.comap_map_eq, Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hHle, (cen_eq_ker h).symm]

private theorem barRho_maps_barImage_inf {D : Data G} {L : Subgroup G}
    {T : Subgroup G} (hT : IsSylowOf 2 T D.M) (hL : L ≤ D.M)
    (hN : D.M ≤ normalizer (L : Set G)) {t : G} (ht : t ∈ T) :
    (barImage L (T ⊓ L)).map (barRho D L hN ⟨t, hT.le ht⟩).toMonoidHom =
      barImage L (T ⊓ L) := by
  have htDM : t ∈ D.M := hT.le ht
  have htN : t ∈ normalizer (L : Set G) := hN htDM
  have hforward : (barImage L (T ⊓ L)).map (barRho D L hN ⟨t, htDM⟩).toMonoidHom ≤
      barImage L (T ⊓ L) := by
    rintro y ⟨x, hx, rfl⟩
    obtain ⟨m, hm, rfl⟩ := uc22p21c_mem_barImage.1 hx
    obtain ⟨hmT, hmL⟩ := Subgroup.mem_inf.mp hm
    have htmL : t * (m : G) * t⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp htN (m : G)).mp hmL
    have htmT : t * (m : G) * t⁻¹ ∈ T := T.mul_mem (T.mul_mem ht hmT) (T.inv_mem ht)
    refine uc22p21c_mem_barImage.2 ⟨⟨t * (m : G) * t⁻¹, htmL⟩,
      Subgroup.mem_inf.mpr ⟨htmT, htmL⟩, ?_⟩
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
        ⟨t * (m : G) * t⁻¹, htmL⟩ =
      (CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL L ⟨t, htN⟩)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L) m)
    rw [show QuotientGroup.mk' (CFSG.pCore 2 ↥L) m =
        QuotientGroup.mk m from rfl]
    rw [CFSG.LocalAnalysis.UniquenessCase.UC6S846.rhoL_mk]
    congr 1
  have hcard : Nat.card ((barImage L (T ⊓ L)).map
      (barRho D L hN ⟨t, htDM⟩).toMonoidHom) = Nat.card (barImage L (T ⊓ L)) :=
    Subgroup.card_map_of_injective (barRho D L hN ⟨t, htDM⟩).injective
  exact Subgroup.eq_of_le_of_card_ge hforward (le_of_eq hcard.symm)

private theorem exists_sylow_ge_R {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) (hH : H ∈ calK8104 D P (F08.KOf8103 L B)) :
    ∃ T : Subgroup G, IsSylowOf 2 T D.M ∧ pCoreOf 2 H ≤ T := by
  have hHDM : pCoreOf 2 H ≤ D.M := (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hH.1
  have hR2 : IsPGroup 2 ((pCoreOf 2 H).subgroupOf D.M) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).of_equiv
      (Subgroup.subgroupOfEquivOfLe hHDM).symm
  obtain ⟨Q, hRQ⟩ := IsPGroup.exists_le_sylow hR2
  refine ⟨Q.map D.M.subtype, ⟨Q, rfl⟩, ?_⟩
  rw [← Subgroup.map_subgroupOf_eq_of_le hHDM]
  exact Subgroup.map_mono hRQ

private theorem exists_conj_eq_of_mem_Rbar {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    (hF5 : KU45AutOdd) {X : Subgroup (Bar2 L)}
    (hPX : barImage L P ≤ X) (hKbarX : F08.KOf8103 ⊤ (barImage L B) ≤ X)
    (hO2 : pCoreOf 2 X = Uset D L s.normal H)
    (hKbarInf : F08.KOf8103 ⊤ (barImage L B) ⊓ pCoreOf 2 X = ⊥)
    {α : MulAut (Bar2 L)} (hα : α ∈ Rbar D L s.normal H) :
    ∃ u ∈ pCoreOf 2 X, α = MulAut.conj u := by
  obtain ⟨u, hu, hPu⟩ := exists_conj_P_eq_of_mem_Rbar s hH hPX hO2 hα
  refine ⟨u, hu, ?_⟩
  let α' : MulAut (Bar2 L) := (MulAut.conj u)⁻¹ * α
  have huc : MulAut.conj u ∈ Rbar D L s.normal H := by
    have hu' : u ∈ Uset D L s.normal H := hO2 ▸ hu
    exact mem_Uset.mp hu'
  have hα' : α' ∈ Rbar D L s.normal H :=
    (Rbar D L s.normal H).mul_mem ((Rbar D L s.normal H).inv_mem huc) hα
  have hPfix : ∀ x ∈ barImage L P, α' x = x :=
    alpha_prime_fixes_P s hH hPX hO2 hα hu hPu
  have hKn : (F08.KOf8103 ⊤ (barImage L B)).map α'.toMonoidHom =
      F08.KOf8103 ⊤ (barImage L B) :=
    alpha_prime_normalizes_K s hH hPX hO2 hα hu hPfix
  have hKfix : ∀ x ∈ F08.KOf8103 ⊤ (barImage L B), α' x = x :=
    alpha_prime_fixes_K s hH hKbarX hO2 hKbarInf hα hu hKn
  have hpow : ∃ k : ℕ, α' ^ (2 ^ k) = 1 := by
    obtain ⟨k, hk⟩ := isPGroup_iff_pow_pow_eq_one.mp
      (isPGroup_Rbar s.normal hH.1) ⟨α', hα'⟩
    refine ⟨k, ?_⟩
    simpa using congrArg Subtype.val hk
  have hPbar2 : IsPGroup 3 (barImage L P) :=
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).1
  have hPbaridx : ¬ 3 ∣ (barImage L P).index :=
    (isPGroup_barImage_of_isSylowOf Nat.prime_three s.hyp.2.2.2.2).2
  have hBbar : F08.NotationB8103 ⊤ (barImage L P) n (barImage L B) :=
    (notationB8103_barImage_iff s.hyp.2.2.2.2.le s.hyp.2.2.2.2.isPGroup s.notB.2.1).mpr
      s.notB
  have hα'1 : α' = 1 :=
    hF5 (Bar2 L) n s.isU45 (barImage L P) hPbar2 hPbaridx (barImage L B) hBbar α' hpow
      hKfix hPfix
  calc α = (MulAut.conj u) * ((MulAut.conj u)⁻¹ * α) := by group
    _ = MulAut.conj u * α' := rfl
    _ = MulAut.conj u * 1 := by rw [hα'1]
    _ = MulAut.conj u := mul_one _


private theorem exists_parabolic_eq (hRad : KU45Radical) (hF5 : KU45AutOdd) {D : Data G}
    {L P B H : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n)
    (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    (hR : ∀ R' : Subgroup G, R' ≤ D.M → IsPGroup 2 R' → H ≤ normalizer (R' : Set G) →
      pCoreOf 2 H ≤ R' → R' = pCoreOf 2 H) :
    ∃ X : Subgroup (Bar2 L),
      barPreimage L (pCoreOf 2 X) ≤ pCoreOf 2 H ∧
      (∀ T₀ : Sylow 2 (Bar2 L), pCoreOf 2 X ≤ (T₀ : Subgroup (Bar2 L)) →
        Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ X) ∧
      Rbar D L s.normal H = (pCoreOf 2 X).map (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hHM : H ≤ D.M := hH.1
  have hKH : F08.KOf8103 L B ≤ H := hH.2.2.1
  have hKL : F08.KOf8103 L B ≤ L := kOf8103_le L B
  have hKDM : F08.KOf8103 L B ≤ D.M := hKH.trans hHM
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hP3 : IsPGroup 3 P := s.hyp.2.2.2.2.isPGroup
  have hPH : P ≤ H := P_le_of_mem_calK8104 hH
  have hPDM : P ≤ D.M := hPH.trans hHM
  have hBP : B ≤ P := s.notB.2.1
  have hBL : B ≤ L := hBP.trans hPL
  have hB3 : IsPGroup 3 B := hP3.to_le hBP
  obtain ⟨X, hXtop, hNUX, hUX, hNS, hKinf, huniq⟩ :=
    exists_parabolic hRad s hH (Uset_ne_bot hRad hF5 s hH hR)
  have hPX : barImage L P ≤ X :=
    (barImage_le_normalizer_Uset s.normal hPL hPDM hPH).trans hNUX
  have hKbarX : F08.KOf8103 ⊤ (barImage L B) ≤ X := by
    rw [← barImage_kOf8103 hBL hB3]
    exact (barImage_le_normalizer_Uset s.normal hKL hKDM hKH).trans hNUX
  have hKPX : F08.KOf8103 ⊤ (barImage L B) ⊔ barImage L P ≤ X := sup_le hKbarX hPX
  obtain ⟨S, hS⟩ := IsPGroup.exists_le_sylow (p := 2)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have hNS' : Subgroup.normalizer ((S : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ X := hNS S hS
  have hRnorm : ∀ α ∈ Rbar D L s.normal H,
      (pCoreOf 2 X).map α.toMonoidHom = pCoreOf 2 X :=
    fun α hα => (map_parabolic_of_mem_Rbar hXtop hNUX hNS' huniq hα).2
  have hO2 : pCoreOf 2 X = Uset D L s.normal H :=
    pCoreOf_parabolic_eq_Uset hRad s hH hR hUX hKPX hRnorm
  have hpre : barPreimage L (pCoreOf 2 X) ≤ pCoreOf 2 H :=
    barPreimage_pCoreOf_le_R hRad s hH hR hKPX hRnorm
  refine ⟨X, hpre, fun T₀ hT₀ => hNS T₀ (hO2 ▸ hT₀), ?_⟩
  ext α
  constructor
  · intro hα
    obtain ⟨u, hu, rfl⟩ := exists_conj_eq_of_mem_Rbar s hH hF5 hPX hKbarX hO2 hKinf hα
    exact Subgroup.mem_map.mpr ⟨u, hO2 ▸ hu, rfl⟩
  · rintro ⟨u, hu, rfl⟩
    exact mem_Uset.mp (hO2 ▸ hu)

private theorem pCoreOf_le_barImage_inf {L R T : Subgroup G} {X : Subgroup (Bar2 L)}
    (hpre : barPreimage L (pCoreOf 2 X) ≤ R) (hRT : R ≤ T) :
    pCoreOf 2 X ≤ barImage L (T ⊓ L) := by
  rw [← barImage_barPreimage L (pCoreOf 2 X)]
  exact barImage_mono (M := L)
    (le_inf (hpre.trans hRT) (uc22p21c_barPreimage_le L (pCoreOf 2 X)))

private theorem map_pCoreOf_parabolic_of_mem_T (hBO : KU45BorelOrders) {D : Data G}
    {L P B T : Subgroup G} {p n : ℕ} (s : Std8105 D L P B p n)
    (hT : IsSylowOf 2 T D.M) {X : Subgroup (Bar2 L)}
    (hX2 : pCoreOf 2 X ≤ barImage L (T ⊓ L))
    (hNS : ∀ T₀ : Sylow 2 (Bar2 L), pCoreOf 2 X ≤ (T₀ : Subgroup (Bar2 L)) →
      Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ X)
    {t : G} (ht : t ∈ T) :
    (pCoreOf 2 X).map (barRho D L s.normal ⟨t, hT.le ht⟩).toMonoidHom = pCoreOf 2 X := by
  have hL : L ≤ D.M := CFSG.Open.IsSubnormal.le s.hyp.1.1
  have hSyl : IsSylowOf 2 (barImage L (T ⊓ L)) ⊤ :=
    isSylowOf_barImage_inf hT hL s.normal
  have hcard : Nat.card (barImage L (T ⊓ L)) =
      2 ^ (Nat.card (Bar2 L)).factorization 2 := by
    rw [CFSG.ABGLocalTools.IsSylowOf.card_eq hSyl, Subgroup.card_top]
  let T₀ : Sylow 2 (Bar2 L) := Sylow.ofCard (barImage L (T ⊓ L)) hcard
  have hT₀ : (T₀ : Subgroup (Bar2 L)) = barImage L (T ⊓ L) := Sylow.coe_ofCard _ _
  have hX2' : pCoreOf 2 X ≤ (T₀ : Subgroup (Bar2 L)) := hT₀.symm ▸ hX2
  have hNX : Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤ X :=
    hNS T₀ hX2'
  let β : MulAut (Bar2 L) := barRho D L s.normal ⟨t, hT.le ht⟩
  have hS0 : (barImage L (T ⊓ L)).map β.toMonoidHom = barImage L (T ⊓ L) :=
    barRho_maps_barImage_inf hT hL s.normal ht
  have hNXβ : Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) ≤
      X.map β.toMonoidHom := by
    have hNβ : (Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L))).map
          β.toMonoidHom = Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
      rw [Subgroup.map_equiv_normalizer_eq (H := (T₀ : Subgroup (Bar2 L))) (f := β), hT₀, hS0]
    intro y hy
    have hNβinv : (Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L))).map
          (β⁻¹).toMonoidHom =
        Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
      have hcomp : (β⁻¹).toMonoidHom.comp β.toMonoidHom = MonoidHom.id (Bar2 L) := by
        ext z
        simp
      have h2 := congrArg (Subgroup.map (β⁻¹).toMonoidHom) hNβ
      rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h2
      exact h2.symm
    have hy' : β⁻¹ y ∈
        Subgroup.normalizer ((T₀ : Subgroup (Bar2 L)) : Set (Bar2 L)) := by
      rw [← hNβinv]
      exact Subgroup.mem_map_of_mem β⁻¹.toMonoidHom hy
    have hmem := Subgroup.mem_map_of_mem (f := β.toMonoidHom) (K := X) (hNX hy')
    simpa using hmem
  have hcardX : Nat.card X = Nat.card (X.map β.toMonoidHom) :=
    (Subgroup.card_map_of_injective (K := X) (f := β.toMonoidHom) β.injective).symm
  have hXeq : X = X.map β.toMonoidHom :=
    hBO (Bar2 L) n s.isU45 T₀ X (X.map β.toMonoidHom) hNX hNXβ hcardX
  have hchar : ((pCoreOf 2 X).subgroupOf X).Characteristic := by
    rw [CFSG.openPCoreOf_subgroupOf]
    exact CFSG.pCore_characteristic
  exact map_eq_of_subgroupOf_characteristic (CFSG.LieType.BorelTits.pCoreOf_le 2 X) hchar hXeq.symm

private theorem barRho_conj_apply {D : Data G} {L : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (u x : ↥D.M) :
    barRho D L h (MulAut.conj u x) =
      MulAut.conj (barRho D L h u) (barRho D L h x) := by
  rw [MulAut.conj_apply, map_mul, map_mul, map_inv, MulAut.conj_apply]

private theorem map_Rbar_inv_of_map_Rbar {D : Data G} {L H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} {β : MulAut (Bar2 L)}
    (hβ : (Rbar D L h H).map (MulAut.conj β).toMonoidHom = Rbar D L h H) :
    (Rbar D L h H).map (MulAut.conj β⁻¹).toMonoidHom = Rbar D L h H := by
  have hcomp : (MulAut.conj β⁻¹).toMonoidHom.comp (MulAut.conj β).toMonoidHom =
      MonoidHom.id (MulAut (Bar2 L)) := by
    ext z x
    simp [MulAut.conj_apply, mul_assoc]
  have h2 := congrArg (Subgroup.map (MulAut.conj β⁻¹).toMonoidHom) hβ
  rw [Subgroup.map_map, hcomp, Subgroup.map_id] at h2
  exact h2.symm

private theorem map_Rbar_of_map_pCoreOf {D : Data G} {L H : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} {X : Subgroup (Bar2 L)}
    (hRX : Rbar D L h H = (pCoreOf 2 X).map (MulAut.conj : Bar2 L →* MulAut (Bar2 L)))
    {β : MulAut (Bar2 L)} (hβ : (pCoreOf 2 X).map β.toMonoidHom = pCoreOf 2 X) :
    (Rbar D L h H).map (MulAut.conj β).toMonoidHom = Rbar D L h H := by
  have hcomp : (MulAut.conj β).toMonoidHom.comp
        (MulAut.conj : Bar2 L →* MulAut (Bar2 L)) =
      (MulAut.conj : Bar2 L →* MulAut (Bar2 L)).comp β.toMonoidHom := by
    ext z x
    simp [MulAut.conj_apply, mul_assoc]
  rw [hRX, Subgroup.map_map, hcomp, ← Subgroup.map_map, hβ]

private theorem le_normalizer_sup_cen {D : Data G} {L H T : Subgroup G}
    {h : D.M ≤ Subgroup.normalizer (L : Set G)} (hHM : H ≤ D.M) (hTM : T ≤ D.M)
    {X : Subgroup (Bar2 L)}
    (hRX : Rbar D L h H = (pCoreOf 2 X).map (MulAut.conj : Bar2 L →* MulAut (Bar2 L)))
    (hTX : ∀ t (ht : t ∈ T),
      (pCoreOf 2 X).map (barRho D L h ⟨t, hTM ht⟩).toMonoidHom = pCoreOf 2 X) :
    T ≤ Subgroup.normalizer ((pCoreOf 2 H ⊔ Cen D L : Subgroup G) : Set G) := by
  have hpre := preimage_Rbar_eq_sup_cen (D := D) (L := L) (H := H) hHM h
  intro t ht
  have htM : t ∈ D.M := hTM ht
  let β : MulAut (Bar2 L) := barRho D L h ⟨t, htM⟩
  have hβ : (Rbar D L h H).map (MulAut.conj β).toMonoidHom = Rbar D L h H :=
    map_Rbar_of_map_pCoreOf hRX (hTX t ht)
  have hβinv : (Rbar D L h H).map (MulAut.conj β⁻¹).toMonoidHom = Rbar D L h H :=
    map_Rbar_inv_of_map_Rbar hβ
  have hSmap : ((Rbar D L h H).comap (barRho D L h)).map
      (MulAut.conj (⟨t, htM⟩ : ↥D.M)).toMonoidHom =
        (Rbar D L h H).comap (barRho D L h) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      change barRho D L h (MulAut.conj (⟨t, htM⟩ : ↥D.M) y) ∈ Rbar D L h H
      rw [barRho_conj_apply (h := h) (⟨t, htM⟩ : ↥D.M) y]
      change MulAut.conj β (barRho D L h y) ∈ Rbar D L h H
      have hf : barRho D L h y ∈ Rbar D L h H := hy
      have hmem := Subgroup.mem_map_of_mem (f := (MulAut.conj β).toMonoidHom)
        (K := Rbar D L h H) hf
      rwa [hβ] at hmem
    · intro hx
      refine ⟨(MulAut.conj (⟨t, htM⟩ : ↥D.M))⁻¹ x, ?_, ?_⟩
      · change barRho D L h ((MulAut.conj (⟨t, htM⟩ : ↥D.M))⁻¹ x) ∈ Rbar D L h H
        have hinv : (MulAut.conj (⟨t, htM⟩ : ↥D.M))⁻¹ =
            MulAut.conj ((⟨t, htM⟩ : ↥D.M)⁻¹) := (map_inv (MulAut.conj) _).symm
        rw [hinv, barRho_conj_apply (h := h) (⟨t, htM⟩ : ↥D.M)⁻¹ x]
        have hβu : barRho D L h ((⟨t, htM⟩ : ↥D.M)⁻¹) = β⁻¹ := by
          rw [map_inv]
        rw [hβu]
        have hf : barRho D L h x ∈ Rbar D L h H := hx
        have hmem := Subgroup.mem_map_of_mem (f := (MulAut.conj β⁻¹).toMonoidHom)
          (K := Rbar D L h H) hf
        rwa [hβinv] at hmem
      · exact MulAut.apply_inv_self (M := ↥D.M) (MulAut.conj (⟨t, htM⟩ : ↥D.M)) x
  have hmem : (⟨t, htM⟩ : ↥D.M) ∈ Subgroup.normalizer
      (((Rbar D L h H).comap (barRho D L h) : Subgroup ↥D.M) : Set ↥D.M) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    exact hSmap
  have hmap : D.M.subtype ⟨t, htM⟩ ∈ Subgroup.normalizer
      (((Rbar D L h H).comap (barRho D L h)).map D.M.subtype : Set G) :=
    (Subgroup.le_normalizer_map (H := (Rbar D L h H).comap (barRho D L h)) D.M.subtype)
      (Subgroup.mem_map_of_mem (f := D.M.subtype) hmem)
  rw [hpre] at hmap
  exact hmap

private theorem inf_cen_isSylow_of_calK {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    (hR : ∀ R' : Subgroup G, R' ≤ D.M → IsPGroup 2 R' → H ≤ normalizer (R' : Set G) →
      pCoreOf 2 H ≤ R' → R' = pCoreOf 2 H) :
    IsSylowOf 2 (pCoreOf 2 H ⊓ Cen D L) (Cen D L) := by
  have hLDM : L ≤ D.M := CFSG.Open.IsSubnormal.le s.hyp.1.1
  have hPL : P ≤ L := s.hyp.2.2.2.2.le
  have hKL : F08.KOf8103 L B ≤ L := kOf8103_le L B
  exact inf_cen_isSylow (K := F08.KOf8103 L B) s.normal hLDM hH.1
    (coe_eq_mul_of_mem_calK8104 hH) hH.2.2.1 (P_le_of_mem_calK8104 hH) hKL hPL
    (fun x hx y hy => commutator_mem_pCore_of_mem_cen hLDM hKL hx hy)
    (fun x hx y hy => commutator_mem_pCore_of_mem_cen hLDM hPL hx hy)
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H) hR

private theorem inf_sup_cen_eq {D : Data G} {L R T : Subgroup G}
    (hN : D.M ≤ Subgroup.normalizer (L : Set G)) (hRM : R ≤ D.M) (hRT : R ≤ T)
    (hT2 : IsPGroup 2 T) (hS : IsSylowOf 2 (R ⊓ Cen D L) (Cen D L)) :
    T ⊓ (R ⊔ Cen D L) = R := by
  have hRN : R ≤ Subgroup.normalizer (Cen D L : Set G) :=
    hRM.trans (DM_le_normalizer_cen hN)
  have hQ2 : IsPGroup 2 ↥(T ⊓ (R ⊔ Cen D L)) :=
    hT2.to_le (K := T) inf_le_left
  have hQinf2 : IsPGroup 2 ↥(T ⊓ (R ⊔ Cen D L) ⊓ Cen D L) :=
    hQ2.to_le (K := T ⊓ (R ⊔ Cen D L)) inf_le_left
  have hle : R ⊓ Cen D L ≤ T ⊓ (R ⊔ Cen D L) ⊓ Cen D L := by
    intro x hx
    exact ⟨⟨hRT hx.1, Subgroup.mem_sup_left hx.1⟩, hx.2⟩
  have hQinf : T ⊓ (R ⊔ Cen D L) ⊓ Cen D L = R ⊓ Cen D L :=
    hS.eq_of_le (P := R ⊓ Cen D L) (K := Cen D L) hle inf_le_right hQinf2
  refine le_antisymm ?_ ?_
  · intro q hq
    have hqT : q ∈ T := hq.1
    have hqsup : q ∈ (R ⊔ Cen D L : Subgroup G) := hq.2
    have hcoe : ((R ⊔ Cen D L : Subgroup G) : Set G) = (R : Set G) * (Cen D L : Set G) :=
      Subgroup.coe_mul_of_left_le_normalizer_right R (Cen D L) hRN
    have hqcoe : q ∈ ((R ⊔ Cen D L : Subgroup G) : Set G) := hqsup
    rw [hcoe] at hqcoe
    obtain ⟨r, hr, c, hc, hqrc⟩ := Set.mem_mul.mp hqcoe
    have hcT : c ∈ T := by
      have hcq : c = r⁻¹ * q := by
        rw [← hqrc]
        group
      rw [hcq]
      exact T.mul_mem (T.inv_mem (hRT hr)) hqT
    have hcQ : c ∈ T ⊓ (R ⊔ Cen D L) ⊓ Cen D L :=
      ⟨⟨hcT, Subgroup.mem_sup_right hc⟩, hc⟩
    rw [hQinf] at hcQ
    rw [← hqrc]
    exact R.mul_mem hr hcQ.1
  · intro x hx
    exact ⟨hRT hx, Subgroup.mem_sup_left hx⟩

theorem exists_sylow_le_normalizer (hRad : KU45Radical) (hBO : KU45BorelOrders)
    (hF5 : KU45AutOdd) {D : Data G} {L P B H : Subgroup G} {p n : ℕ}
    (s : Std8105 D L P B p n) (hH : H ∈ calK8104 D P (F08.KOf8103 L B))
    (hR : ∀ R' : Subgroup G, R' ≤ D.M → IsPGroup 2 R' → H ≤ normalizer (R' : Set G) →
      pCoreOf 2 H ≤ R' → R' = pCoreOf 2 H) :
    ∃ T₁ : Subgroup G, IsSylowOf 2 T₁ D.M ∧ T₁ ≤ normalizer (pCoreOf 2 H : Set G) := by
  obtain ⟨X, hpre, hNS, hRX⟩ := exists_parabolic_eq hRad hF5 s hH hR
  obtain ⟨T, hT, hRT⟩ := exists_sylow_ge_R s hH
  have hTX : ∀ t (ht : t ∈ T), (pCoreOf 2 X).map
      (barRho D L s.normal ⟨t, hT.le ht⟩).toMonoidHom = pCoreOf 2 X := fun t ht =>
    map_pCoreOf_parabolic_of_mem_T hBO s hT (pCoreOf_le_barImage_inf hpre hRT) hNS ht
  have heq : T ⊓ (pCoreOf 2 H ⊔ Cen D L) = pCoreOf 2 H :=
    inf_sup_cen_eq s.normal ((CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hH.1) hRT
      hT.isPGroup (inf_cen_isSylow_of_calK s hH hR)
  have hTN := le_normalizer_sup_cen hH.1 hT.le hRX hTX
  refine ⟨T, hT, fun t ht => ?_⟩
  have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ht)
  have h2 := Subgroup.mem_normalizer_iff.mp (hTN ht)
  rw [← heq, Subgroup.mem_normalizer_iff]
  intro x
  simp only [SetLike.mem_coe, Subgroup.mem_inf] at h1 h2 ⊢
  exact ⟨fun hx => ⟨(h1 x).mp hx.1, (h2 x).mp hx.2⟩,
    fun hx => ⟨(h1 x).mpr hx.1, (h2 x).mpr hx.2⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.R8105
