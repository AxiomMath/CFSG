module

public import CFSG.Quasithin.H13.A6S13821zj
public import CFSG.Quasithin.H13.A6S13821l

public section

namespace CFSG.Quasithin.H13.A6.A6S20

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.F7 CFSG.Quasithin.InternalSec

attribute [local instance] commGroupOfFact

variable {G : Type} [Group G] [Finite G] {T V L V₁ Vp H K I : Subgroup G}

theorem autIH_perfect (hF : HypF918 T V L V₁ Vp H K) (hK₀ : conjClosure K T = K)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] :
    ⁅autIH V₁ I H K, autIH V₁ I H K⁆ = autIH V₁ I H K := by
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  rw [autIH_eq_map hF hKH]
  have hA : ⁅K.subgroupOf H, K.subgroupOf H⁆ = K.subgroupOf H := by
    apply Subgroup.map_injective H.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKH]
    have := hF.K₀_perfect
    rwa [hK₀] at this
  rw [← Subgroup.map_commutator, hA]

theorem cube_facts (hF : HypF918 T V L V₁ Vp H K) (hIU : I ≤ conjClosure Vp H)
    [Fact (IsElemAbelian 2 (tildeOf V₁ (conjClosure I H)))] {x : G} (hxH : x ∈ H)
    (hx3 : x ^ 3 = 1)
    (hθ : ∀ u ∈ conjClosure Vp H, u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) ∈ V₁)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) {t : G} (htH : t ∈ H)
    (htK : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) (htx : t * x * t⁻¹ * x ∈ pCoreOf 2 H)
    {e : ℕ} (ht2 : t ^ 2 ^ e = 1) :
    let ψ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H)
    ψ ⟨x, hxH⟩ ^ 3 = 1 ∧ (∀ w, w * ψ ⟨x, hxH⟩ w * ψ ⟨x, hxH⟩ (ψ ⟨x, hxH⟩ w) = 1) ∧
      ψ ⟨t, htH⟩ ^ 2 ^ e = 1 ∧ ψ ⟨t, htH⟩ * ψ ⟨x, hxH⟩ * (ψ ⟨t, htH⟩)⁻¹ = (ψ ⟨x, hxH⟩)⁻¹ ∧
      (∀ γ ∈ autIH V₁ I H K, γ * ψ ⟨x, hxH⟩ = ψ ⟨x, hxH⟩ * γ) ∧
      ∀ γ ∈ autIH V₁ I H K, γ * ψ ⟨t, htH⟩ = ψ ⟨t, htH⟩ * γ := by
  intro ψ
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hIHN := hF.conjClosure_le_normalizer_V₁ hIU
  have hIHU : conjClosure I H ≤ conjClosure Vp H := conjClosure_le_conjClosure_U hIU le_rfl
  have hIH := le_normalizer_conjClosure I H
  have hcomm : ∀ g : ↥H, (∀ k ∈ K, (g : G) * k * (g : G)⁻¹ * k⁻¹ ∈ pCoreOf 2 H) →
      ∀ γ ∈ autIH V₁ I H K, γ * ψ g = ψ g * γ := by
    intro g hg γ hγ
    rw [autIH_eq_map hF hKH] at hγ
    obtain ⟨k, hk, rfl⟩ := hγ
    have hc := hg k (Subgroup.mem_subgroupOf.mp hk)
    have h0 := hF.actH_eq_one_of_mem_pCoreOf hIU (x := g * k * g⁻¹ * k⁻¹) hc
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h0
    have e : ψ k * ψ g = (ψ g * ψ k * (ψ g)⁻¹ * (ψ k)⁻¹)⁻¹ * (ψ g * ψ k) := by group
    rw [e, h0, inv_one, one_mul]
  refine ⟨?_, ?_, ?_, ?_, hcomm _ hxK, hcomm _ htK⟩
  · have h1 : (⟨x, hxH⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
    rw [← map_pow, h1, map_one]
  · intro w
    obtain ⟨a, haI, haw⟩ := exists_mk_of_mem_tilde w
    have hwa : w = modMk hIHN (a : G) haI := Subtype.ext haw.symm
    have h1 := (Subgroup.mem_normalizer_iff.mp (hIH hxH) _).mp haI
    have h2 := (Subgroup.mem_normalizer_iff.mp (hIH hxH) _).mp h1
    have hθa := hθ (a : G) (hIHU haI)
    rw [hwa, actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hxH⟩ haI,
      actH_modMk hF.H_le_normalizer_V₁ hIHN hIH ⟨x, hxH⟩ h1]
    apply Subtype.ext
    show secMk _ _ ⟨(a : G), _⟩ * secMk _ _ ⟨x * a * x⁻¹, _⟩ *
      secMk _ _ ⟨x * (x * a * x⁻¹) * x⁻¹, _⟩ = 1
    rw [← map_mul, ← map_mul]
    exact (secMk_eq_one_iff (A := Subgroup.normalizer (V₁ : Set G))
      (B := V₁) (x := ⟨_, hIHN ((conjClosure I H).mul_mem
        ((conjClosure I H).mul_mem haI h1) h2)⟩)).mpr hθa
  · have h1 : (⟨t, htH⟩ : ↥H) ^ 2 ^ e = 1 := Subtype.ext (by simpa using ht2)
    rw [← map_pow, h1, map_one]
  · have h0 := hF.actH_eq_one_of_mem_pCoreOf hIU
      (x := ⟨t, htH⟩ * ⟨x, hxH⟩ * ⟨t, htH⟩⁻¹ * ⟨x, hxH⟩) htx
    rw [map_mul, map_mul, map_mul, map_inv] at h0
    exact eq_inv_of_mul_eq_one_left h0

theorem exists_ff_of_cube (hF : HypF918 T V L V₁ Vp H K) (hSQ : SQTKGroup ↥H)
    (hK₀ : conjClosure K T = K) (hD310 : D310) (hD391 : D391) (hI4 : Insp4) {x : G}
    (hxH : x ∈ H) (hx3 : x ^ 3 = 1)
    (hθ : ∀ u ∈ conjClosure Vp H, u * (x * u * x⁻¹) * (x * (x * u * x⁻¹) * x⁻¹) ∈ V₁)
    (hxK : ∀ k ∈ K, x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 H) {t : G} (htH : t ∈ H)
    (htK : ∀ k ∈ K, t * k * t⁻¹ * k⁻¹ ∈ pCoreOf 2 H) (htx : t * x * t⁻¹ * x ∈ pCoreOf 2 H)
    {e : ℕ} (ht2 : t ^ 2 ^ e = 1) :
    ∃ I : Subgroup G, V₁ ≤ I ∧ ∃ hIU : I ≤ conjClosure Vp H, IsIrrPlusTildeT hF hIU ∧
      T ≤ Subgroup.normalizer (I : Set G) ∧
      (haveI := factElem hF hIU
       IsFFModule (autSec (autIH V₁ I H K ⊔ autIH V₁ I H T) (subM V₁ (conjClosure I H) I)
        (fixV (autIH V₁ I H (conjClosure K T))))) := by
  classical
  obtain ⟨I, hV₁I, hIU, W, hW, hirrU⟩ := exists_isIrrPlusTildeU hF
  have hirrT := isIrrPlusTildeT_of_ambient hF hIU W hW hirrU
  have := factElem hF hIU
  have hKH : K ≤ H := le_of_mem_cComp hF.K_cComp
  have hTH : T ≤ H := hF.T_le_H
  have hirr' : subM V₁ (conjClosure I H) I ∈
      IrrPlusOn (autIH V₁ I H (conjClosure K T))
        (orbSup (autIH V₁ I H T) (subM V₁ (conjClosure I H) I)) (autIH V₁ I H T) := hirrT
  have hKI := K₀_le_normalizer_of_isInv hF hIU hV₁I hirr'.1.2.1
  have hKI' : K ≤ Subgroup.normalizer (I : Set G) := hK₀ ▸ hKI
  have hMp : autIH V₁ I H (conjClosure K T) = autIH V₁ I H K := by rw [hK₀]
  set ψ := actH hF.H_le_normalizer_V₁ (le_normalizer_conjClosure I H) with hψ
  obtain ⟨hy3, hcube, hr2, hry, hyL, hrL⟩ :=
    cube_facts hF hIU hxH hx3 hθ hxK htH htK htx ht2
  have hW2 : ∀ w : ↥(tildeOf V₁ (conjClosure I H)), w * w = 1 := by
    intro w
    apply Subtype.ext
    have := (Fact.out : IsElemAbelian 2 (tildeOf V₁ (conjClosure I H))).2 w w.2
    simpa [pow_two] using this
  set Lk := autIH V₁ I H K with hLk
  have hfixC : ∀ u, u ∈ XMod.fixed ↥(autIH V₁ I H (conjClosure K T))
      (subM V₁ (conjClosure I H) I) ↔ u ∈ subM V₁ (conjClosure I H) I ⊓ fixV Lk := fun u => by
    constructor
    · rintro ⟨hu, hf⟩
      exact ⟨hu, fun γ hγ => hf ⟨γ, hMp ▸ hγ⟩⟩
    · rintro ⟨hu, hc⟩
      exact ⟨hu, fun a => hc a (hMp ▸ a.2)⟩
  have hnt : ∃ γ ∈ Lk, ∃ v ∈ subM V₁ (conjClosure I H) I, γ v * v⁻¹ ∉ fixV Lk := by
    by_contra hcon
    push Not at hcon
    have hle : XMod.commOf ↥(autIH V₁ I H (conjClosure K T)) (subM V₁ (conjClosure I H) I) ≤
        subM V₁ (conjClosure I H) I ⊓ fixV Lk := by
      rw [XMod.commOf, Subgroup.closure_le]
      rintro _ ⟨a, l, hl, rfl⟩
      have ha : (a : MulAut ↥(tildeOf V₁ (conjClosure I H))) ∈ Lk := hMp ▸ a.2
      refine ⟨?_, hcon _ ha l hl⟩
      exact (subM V₁ (conjClosure I H) I).mul_mem (hirr'.1.2.1 a l hl)
        ((subM V₁ (conjClosure I H) I).inv_mem hl)
    rw [hirr'.1.2.2.1] at hle
    apply hirr'.1.2.2.2.1.ne
    ext u
    rw [hfixC]
    exact ⟨fun hu => hu.1, fun hu => hle hu⟩
  have h4 := (F918_4' hF hSQ hK₀ hV₁I hIU W hW hirrU hD310 hD391 hI4).2
  rcases h4 with hHI | (⟨hVT, hFF⟩ | h3)
  ·
    exfalso
    have hTI : T ≤ Subgroup.normalizer (I : Set G) := hTH.trans hHI
    have hQ := A6L32.qsec_of_T_le hSQ hF hK₀ hV₁I hIU hirrT hTI
    set U := subM V₁ (conjClosure I H) I with hU
    have hst : ∀ g : ↥H, ψ g ∈ stabSub U := fun g =>
      (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁ (hF.conjClosure_le_normalizer_V₁ hIU)
        (le_normalizer_conjClosure I H) hV₁I (le_conjClosure I H) g).mpr (hHI g.2)
    set gx : ↥(stabSub U) := ⟨ψ ⟨x, hxH⟩, hst _⟩ with hgx
    set gt : ↥(stabSub U) := ⟨ψ ⟨t, htH⟩, hst _⟩ with hgt
    have hcommU : ∀ g : ↥(stabSub U), (∀ γ ∈ Lk, γ * (g : MulAut _) = (g : MulAut _) * γ) →
        ∀ k ∈ autSub Lk U, k * resHom U g = resHom U g * k := by
      intro g hg k hk
      obtain ⟨g', hg'L, rfl⟩ := mem_autSub.mp hk
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hg _ hg'L)
    have hfixU : ∀ g : ↥(stabSub U), (∀ γ ∈ Lk, γ * (g : MulAut _) = (g : MulAut _) * γ) →
        resHom U g ∈ stabSub ((U ⊓ fixV (autIH V₁ I H (conjClosure K T))).subgroupOf U) := by
      intro g hg v
      have hgs : (g : MulAut _) ∈ stabSub (fixV Lk) := L32A.C.mem_stabSub_fixV_of_conj
        (fun m hm => by rw [← hg m hm, mul_inv_cancel_right]; exact hm)
        (fun m hm => by
          have hg' : m * (g : MulAut _)⁻¹ = (g : MulAut _)⁻¹ * m := by
            calc m * (g : MulAut _)⁻¹ = (g : MulAut _)⁻¹ * ((g : MulAut _) * m) *
                (g : MulAut _)⁻¹ := by group
              _ = (g : MulAut _)⁻¹ * (m * (g : MulAut _)) * (g : MulAut _)⁻¹ := by rw [hg m hm]
              _ = (g : MulAut _)⁻¹ * m := by group
          rw [← hg', inv_mul_cancel_right]
          exact hm)
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, resHom_apply, hMp]
      exact ⟨fun h => ⟨v.2, (hgs v).mp h.2⟩, fun h => ⟨(g.2 v).mpr v.2, (hgs v).mpr h.2⟩⟩
    have hV2 : ∀ v : ↥U, v ^ 2 = 1 := fun v => Subtype.ext (by
      rw [sq]
      exact hW2 v)
    refine false_of_qsec_cube hV2 hQ (y := resHom U gx) (s := resHom U gt) (e := e) ?_ ?_
      (hcommU gx hyL) (hcommU gt hrL) ?_ ?_ (hfixU gx hyL) (hfixU gt hrL)
    · have h1 : gx ^ 3 = 1 := Subtype.ext hy3
      rw [← map_pow, h1, map_one]
    · intro v
      apply Subtype.ext
      simp only [Subgroup.coe_mul, resHom_apply]
      exact hcube v
    · have h1 : gt ^ 2 ^ e = 1 := Subtype.ext hr2
      rw [← map_pow, h1, map_one]
    · rw [← map_inv, ← map_mul, ← map_mul, ← map_inv]
      congr 1
      exact Subtype.ext hry
  ·
    refine ⟨I, hV₁I, hIU, hirrT, ?_, hFF⟩
    intro t' ht'
    have hst := A6L32.mem_stabSub_of_eq_orbSup_T hVT
      (actH_mem_autIH_of_mem (I := I) hF hTH ht')
    exact (actH_mem_stabSub_subM_iff hF.H_le_normalizer_V₁
      (hF.conjClosure_le_normalizer_V₁ hIU) (le_normalizer_conjClosure I H) hV₁I
      (le_conjClosure I H) ⟨t', hTH ht'⟩).mp hst
  ·
    exfalso
    have hTK : T ≤ Subgroup.normalizer (K : Set G) := fun s hs =>
      Subgroup.mem_normalizer_fintype fun k' hk' => by
        have := mem_conjClosure hs hk'
        rwa [hK₀] at this
    have hTL : ∀ s ∈ autIH V₁ I H T, ∀ γ ∈ Lk, s * γ * s⁻¹ ∈ Lk := by
      intro s hs γ hγ
      rw [autIH_eq_map hF hTH] at hs
      rw [hLk, autIH_eq_map hF hKH] at hγ ⊢
      obtain ⟨t', ht', rfl⟩ := hs
      obtain ⟨k, hk, rfl⟩ := hγ
      refine ⟨t' * k * t'⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
      exact (Subgroup.mem_normalizer_iff.mp (hTK (Subgroup.mem_subgroupOf.mp ht')) _).mp
        (Subgroup.mem_subgroupOf.mp hk)
    have hTL' : ∀ s ∈ autIH V₁ I H T, ∀ γ ∈ Lk, s⁻¹ * γ * s ∈ Lk := by
      intro s hs γ hγ
      have h1 := hTL s⁻¹ ((autIH V₁ I H T).inv_mem hs) γ hγ
      simpa using h1
    exact false_of_d310Two_cube hW2 hMp hirr'.1.2.2.2
      (A6L32.autIH_le_stabSub_of hF hIU hV₁I hKH hKI') (autIH_perfect hF hK₀) hTL hTL' h3
      hy3 hcube hyL hrL hr2 hry hnt

end CFSG.Quasithin.H13.A6.A6S20
