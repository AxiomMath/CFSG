module

public import CFSG.Quasithin.H13.A6S13824u
public import CFSG.Quasithin.H13.A6S13824r
public import CFSG.Quasithin.H13.A6S13824s
public import CFSG.Quasithin.H13.A6S13824o
public import CFSG.Quasithin.H13.A6S13825f

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

open L13825 S7C in
theorem irrSec_of_S7
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1337 : Stmt13_3_7) [IsMulCommutative ↥(conjClosure S.V3 H)] {W : Subgroup G}
    (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    (hA : ∀ x ∈ pCoreOf 2 (S.L1 ⊔ T), ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V))
    {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H) {ρ : ↥H →* Perm (Fin 7)}
    (hρs : Function.Surjective ρ) (hρk : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H)
    (hρT : ∀ t : ↥H, (t : G) ∈ T → ρ t ∈ T0) (hTρ : ∀ s ∈ T0, ∃ t : ↥H, (t : G) ∈ T ∧ ρ t = s) :
    XMod.IsIrrSec ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
      (W.subgroupOf (conjClosure S.V3 H)))
      (⊥ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
        (W.subgroupOf (conjClosure S.V3 H)))) ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS := hd.hS
  have hH := hd.hH
  have hF := hd.hF.toHypF91
  set U := conjClosure S.V3 H with hU
  have hab := isElemAbelian_UH hS hH
  have hU2 : ∀ u ∈ U, u ^ 2 = 1 := hab.2
  have hHU : H ≤ Subgroup.normalizer (U : Set G) := le_normalizer_conjClosure S.V3 H
  have hL1H : S.L1 ≤ H := hd.hL1K.trans hd.hKH
  have hTH : T ≤ H := hd.hTH
  have hL1TH : S.L1 ⊔ T ≤ H := sup_le hL1H hTH
  have hHV1 : H ≤ Subgroup.normalizer (fsuV1 T V : Set G) := hF.H_normalizes_V₁
  have hsU := hd.secU hV1W hWU.le le_rfl hHU hHW (hd.knt_top hWU)
  set σ := sigmaH (S := S) hH with hσ
  have hσ1 : ∀ h : ↥H, σ h = 1 ↔ (h : G) ∈ pCoreOf 2 H := sigmaH_eq_one_iff hH hF
  have hkerσ : ρ.ker ≤ σ.ker := fun h hh => by
    rw [MonoidHom.mem_ker] at hh ⊢
    exact (hσ1 h).2 ((hρk h).1 hh)
  set Φ := ρ.liftOfRightInverse (Function.surjInv hρs) (Function.rightInverse_surjInv hρs)
    ⟨σ, hkerσ⟩ with hΦdef
  have hΦ : ∀ h : ↥H, Φ (ρ h) = σ h := fun h =>
    ρ.liftOfRightInverse_comp_apply _ _ ⟨σ, hkerσ⟩ h
  obtain ⟨f, hf1, hfσ, hfs⟩ :
      ∃ f : ↥U →* Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U),
        (∀ x, f x = 1 ↔ (x : G) ∈ fsuV1 T V) ∧
        (∀ h u, σ h (f u) = f (Setup.rho U H hHU h u)) ∧ Function.Surjective f :=
    ⟨InternalSec.secMk _, A6Mod.secMk_eq_one_iff, fun _ _ => rfl,
      InternalSec.secMk_surjective _⟩
  have hsq : ∀ x : Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U), x * x = 1 := fun x => by
    rw [← pow_two]
    exact sec_sq_eq_one hU2 x
  have hinv : ∀ x : Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U), x⁻¹ = x :=
    fun x => inv_eq_of_mul_eq_one_right (hsq x)
  have hfeq : ∀ x y : ↥U, f x = f y ↔ (x : G) * (y : G) ∈ fsuV1 T V := by
    intro x y
    rw [← Subgroup.coe_mul, ← hf1, map_mul]
    constructor
    · intro h
      rw [h, hsq]
    · intro h
      rw [← hinv (f y)]
      exact eq_inv_of_mul_eq_one_left h
  have hσρ : ∀ (h : ↥H) (u : ↥U), σ h (f u) = f ⟨(h : G) * u * (h : G)⁻¹,
      (Subgroup.mem_normalizer_iff.mp (hHU h.2) _).mp u.2⟩ := fun h u => by
    rw [hfσ]
    congr 1
  obtain ⟨g, hgL, hg⟩ := S.exists_g012
  have hgH : (g : G) ∈ H := hL1H hgL
  have hg2H : (g : G) * g ∈ H := H.mul_mem hgH hgH
  set v₂ : ↥U := ⟨S.v2, S.v2_mem_UH H⟩ with hv₂
  have hnV1 : ∀ k ∈ H, k * S.v2 * k⁻¹ ∉ fsuV1 T V := by
    intro k hk hmem
    apply S.v2_not_mem_V1
    have := (Subgroup.mem_normalizer_iff.mp (hHV1 (H.inv_mem hk)) _).mp hmem
    simpa [mul_assoc] using this
  set m₀ := f v₂ with hm₀
  have hm₁ : σ ⟨g, hgH⟩ m₀ = f ⟨(g : G) * S.v2 * (g : G)⁻¹, le_conjClosure _ _
      (S.conj_v2_mem_V3 hg)⟩ := hσρ _ _
  have hg2 : ((g ^ 2 : ↥(Subgroup.normalizer (V : Set G))) : G) = (g : G) * g := by
    rw [pow_two]
    rfl
  have hv2g2 := S.v2_mul_conj hg
  rw [hg2] at hv2g2
  have hm₂ : σ ⟨(g : G) * g, hg2H⟩ m₀ = f ⟨(g : G) * g * S.v2 * ((g : G) * g)⁻¹,
      hv2g2 ▸ U.mul_mem (S.v2_mem_UH H) (le_conjClosure _ _ (S.conj_v2_mem_V3 hg))⟩ :=
    hσρ _ _
  set c := ρ ⟨g, hgH⟩ with hcdef
  have hΦc : Φ c m₀ = σ ⟨g, hgH⟩ m₀ := by rw [hcdef, hΦ]
  have hΦcc : Φ (c * c) m₀ = σ ⟨(g : G) * g, hg2H⟩ m₀ := by
    have e : (⟨(g : G) * g, hg2H⟩ : ↥H) = ⟨g, hgH⟩ * ⟨g, hgH⟩ := rfl
    rw [hcdef, ← map_mul, hΦ, e]
  have hv2V1 := S.v2_not_mem_V1
  have hgv : (g : G) * S.v2 * (g : G)⁻¹ ∉ fsuV1 T V := hnV1 _ hgH
  have hggv : (g : G) * g * S.v2 * ((g : G) * g)⁻¹ ∉ fsuV1 T V := hnV1 _ hg2H
  have hcomm2 : ∀ x y : G, x ∈ U → y ∈ U → x * y = y * x := fun x y hx hy =>
    congrArg Subtype.val (mul_comm (⟨x, hx⟩ : ↥U) ⟨y, hy⟩)
  have hvsq : S.v2 * S.v2 = 1 := by
    rw [← pow_two]
    exact hU2 _ (S.v2_mem_UH H)
  have hgvU : (g : G) * S.v2 * (g : G)⁻¹ ∈ U := le_conjClosure _ _ (S.conj_v2_mem_V3 hg)
  have hgvsq : (g : G) * S.v2 * (g : G)⁻¹ * ((g : G) * S.v2 * (g : G)⁻¹) = 1 := by
    rw [← pow_two]
    exact hU2 _ hgvU
  have h1 : Φ c m₀ ≠ m₀ := by
    rw [hΦc, hm₁, hm₀, Ne, hfeq]
    intro h
    apply hggv
    rw [← hv2g2, hcomm2 _ _ (S.v2_mem_UH H) hgvU]
    exact h
  have h2 : Φ (c * c) m₀ ≠ m₀ := by
    rw [hΦcc, hm₂, hm₀, Ne, hfeq]
    intro h
    apply hgv
    have e : (g : G) * g * S.v2 * ((g : G) * g)⁻¹ * S.v2 = (g : G) * S.v2 * (g : G)⁻¹ := by
      rw [← hv2g2, hcomm2 _ _ (S.v2_mem_UH H) hgvU, mul_assoc, hvsq, mul_one]
    rw [← e]
    exact h
  have h12 : Φ c m₀ ≠ Φ (c * c) m₀ := by
    rw [hΦc, hΦcc, hm₁, hm₂, Ne, hfeq]
    intro h
    apply hv2V1
    have e : (g : G) * S.v2 * (g : G)⁻¹ * ((g : G) * g * S.v2 * ((g : G) * g)⁻¹) = S.v2 := by
      rw [← hv2g2, ← mul_assoc, hcomm2 _ _ hgvU (S.v2_mem_UH H), mul_assoc, hgvsq, mul_one]
    rw [← e]
    exact h
  have hcc : m₀ * Φ c m₀ = Φ (c * c) m₀ := by
    rw [hΦc, hΦcc, hm₁, hm₂, hm₀, ← map_mul]
    congr 1
    exact Subtype.ext hv2g2
  have hTfix : ∀ t : ↥H, (t : G) ∈ T → σ t m₀ = m₀ := by
    intro t ht
    rw [hσρ, hm₀, hfeq]
    have hc := S.comm_T_v2 ht
    rwa [inv_eq_of_mul_eq_one_right hvsq] at hc
  have hT : ∀ s : Perm (Fin 7), inT0 (cd s) = true → Φ s m₀ = m₀ := fun s hs => by
    obtain ⟨t, ht, rfl⟩ := hTρ s (mem_T0_iff.mpr hs)
    rw [hΦ]
    exact hTfix t ht
  have hgen : Subgroup.closure (Set.range fun s : Perm (Fin 7) => Φ s m₀) = ⊤ := by
    rw [eq_top_iff]
    rintro y -
    obtain ⟨u, rfl⟩ := hfs y
    have hle : U ≤ ((Subgroup.closure (Set.range fun s : Perm (Fin 7) => Φ s m₀)).comap
        f).map U.subtype := by
      refine conjClosure_le fun h hh z hz => ?_
      refine ⟨⟨h * z * h⁻¹, (Subgroup.mem_normalizer_iff.mp (hHU hh) _).mp
        (le_conjClosure _ _ hz)⟩, ?_, rfl⟩
      rw [SetLike.mem_coe, Subgroup.mem_comap, ← hσρ ⟨h, hh⟩ ⟨z, le_conjClosure _ _ hz⟩]
      have hgen1 : ∀ k : ↥H, σ ⟨h, hh⟩ (σ k m₀) ∈
          Subgroup.closure (Set.range fun s : Perm (Fin 7) => Φ s m₀) := fun k => by
        rw [← MulAut.mul_apply, ← map_mul, ← hΦ]
        exact Subgroup.subset_closure ⟨_, rfl⟩
      rcases S.mem_V3_cases hg hz with hz1 | hz1 | hz1 | hz1
      · rw [(hf1 ⟨z, _⟩).2 hz1, map_one]
        exact Subgroup.one_mem _
      · have : f ⟨z, le_conjClosure _ _ hz⟩ = σ 1 m₀ := by
          rw [map_one, MulAut.one_apply, hm₀, hfeq]
          exact hz1
        rw [this]
        exact hgen1 1
      · have : f ⟨z, le_conjClosure _ _ hz⟩ = σ ⟨g, hgH⟩ m₀ := by
          rw [hm₁, hfeq]
          exact hz1
        rw [this]
        exact hgen1 _
      · have : f ⟨z, le_conjClosure _ _ hz⟩ = σ ⟨(g : G) * g, hg2H⟩ m₀ := by
          rw [hm₂, hfeq]
          rw [hg2] at hz1
          exact hz1
        rw [this]
        exact hgen1 _
    obtain ⟨n, hn, hnu⟩ := hle u.2
    rw [← Subtype.ext hnu]
    exact hn
  have hcube : ∀ (x : G) (hx : x ∈ S.L1), ρ ⟨x, hL1H hx⟩ ^ 3 ∈ T0 := by
    intro x hx
    have h3 : x ^ 3 ∈ pCoreOf 2 S.L1 := by
      by_cases hhat : IsHatA6 L
      · exact S.cube_mem_pCoreOf_L1_hat hhat hx
      · exact S.cube_mem_pCoreOf_L1 hhat hx
    rw [← map_pow]
    exact hρT _ (by simpa using S.O2L1_le_T h3)
  have hgens : ∀ t ∈ [t1c, t2c, t3c], ∃ s : ↥H, (s : G) ∈ T ∧ ρ s = dec t ∧
      (dec t)⁻¹ = dec t := by
    intro t ht
    have hv := valid_of_mem_gens ht
    have hT0 : inT0 t = true ∧ cm t t = idc := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ht
      rcases ht with rfl | rfl | rfl <;> decide
    obtain ⟨s, hs, hst⟩ := hTρ _ (mem_T0_iff.mpr (by rw [cd_dec hv]; exact hT0.1))
    refine ⟨s, hs, hst, inv_eq_of_mul_eq_one_right (cd_injective ?_)⟩
    rw [cd_mul, cd_dec hv, hT0.2, cd_one]
  have hconjL1 : ∀ s : ↥H, (s : G) ∈ T → ∀ x ∈ S.L1, (s : G) * x * (s : G)⁻¹ ∈ S.L1 :=
    fun s hs x hx => (Subgroup.mem_normalizer_iff.mp (S.T_le_normalizer_L1 hs) x).mp hx
  have hcubeC : cubeConds (cd c) = true := by
    refine cubeConds_of (hcube g hgL) fun t ht => ?_
    obtain ⟨s, hsT, hst, hinvt⟩ := hgens t ht
    have hsg := hconjL1 s hsT g hgL
    have e : dec t * c * dec t = ρ (s * ⟨g, hgH⟩ * s⁻¹) := by
      rw [map_mul, map_mul, map_inv, hst, hinvt]
    rw [e, hcdef, ← map_mul, ← map_mul, ← map_mul]
    exact ⟨hcube _ (S.L1.mul_mem hgL hsg), hcube _ (S.L1.mul_mem (S.L1.mul_mem hgL hgL) hsg)⟩
  obtain ⟨Y, hYR, hYc, hY4, hYab⟩ :=
    hd.exists_quadY h36 h139 h1334 h13 h13314 h13315 h1356two hA
  have hYH : Y ≤ H := hYR.trans ((pCoreOf_le 2 _).trans hL1TH)
  set E := (Y.subgroupOf H).map ρ with hEdef
  have hconj : ∀ k x : ↥H, ρ k * ρ x * (ρ k)⁻¹ = ρ (k * x * k⁻¹) := fun k x => by
    rw [map_mul, map_mul, map_inv]
  have hq : IndQuad.QuadOn Φ (E : Set (Perm (Fin 7))) := by
    intro h a ha a' ha' v
    obtain ⟨k, rfl⟩ := hρs h
    obtain ⟨x, hx, rfl⟩ := ha
    obtain ⟨y, hy, rfl⟩ := ha'
    obtain ⟨u, rfl⟩ := hfs v
    rw [hconj, hconj, hΦ, hΦ, hfσ, ← map_inv f u, ← map_mul f, hfσ]
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Setup.rho_apply_coe]
    have hku := (Subgroup.mem_normalizer_iff.mp (hHU (H.inv_mem k.2)) _).mp u.2
    rw [inv_inv] at hku
    exact L4Ind.conj_quad hYc hku (Subgroup.mem_subgroupOf.mp hx) (Subgroup.mem_subgroupOf.mp hy)
  have h4 : 4 ≤ Nat.card E := by
    rw [L4Ind.card_map_subgroupOf ρ hρk hYH]
    exact hY4
  have hRT : ∀ (w : G) (hw : w ∈ pCoreOf 2 (S.L1 ⊔ T)),
      ρ ⟨w, (pCoreOf_le 2 _).trans hL1TH hw⟩ ∈ T0 :=
    fun w hw => hρT _ (pCoreOf_le_of_sylow S.h13.sylow le_sup_right hw)
  have hcoreE : ∀ x ∈ E, ∀ (z : G) (hz : z ∈ S.L1), x ∈ T0 ∧
      ρ ⟨z, hL1H hz⟩ * x * (ρ ⟨z, hL1H hz⟩)⁻¹ ∈ T0 ∧
      (ρ ⟨z, hL1H hz⟩)⁻¹ * x * ρ ⟨z, hL1H hz⟩ ∈ T0 := by
    rintro _ ⟨y, hy, rfl⟩ z hz
    have hyR : (y : G) ∈ pCoreOf 2 (S.L1 ⊔ T) := hYR (Subgroup.mem_subgroupOf.mp hy)
    have hzN : z ∈ Subgroup.normalizer (pCoreOf 2 (S.L1 ⊔ T) : Set G) :=
      le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hz)
    refine ⟨hRT _ hyR, ?_, ?_⟩
    · have hm := (Subgroup.mem_normalizer_iff.mp hzN y).mp hyR
      rw [hconj]
      exact hRT (z * y * z⁻¹) hm
    · have hm := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hzN) y).mp hyR
      rw [inv_inv] at hm
      have e : (ρ ⟨z, hL1H hz⟩)⁻¹ * ρ y * ρ ⟨z, hL1H hz⟩ =
          ρ ((⟨z, hL1H hz⟩ : ↥H)⁻¹ * y * ⟨z, hL1H hz⟩) := by
        rw [map_mul, map_mul, map_inv]
      rw [e]
      exact hRT (z⁻¹ * y * z) hm
  rcases shape hcubeC with hc43 | hcPA
  · exfalso
    have hcT : c ∉ T0 := fun h => h1 (hT c (mem_T0_iff.mp h))
    by_cases hhat : IsHatA6 L
    · obtain ⟨c0, hc0L1, hc0V, hc03, hc01, htn, hcomm, hcub1, hcub2⟩ :=
        hd.hat_data hhat hρk hρT hgens hcube hgL
      have hc0fix : Φ (ρ c0) m₀ = m₀ := by
        rw [hΦ, hσρ, hm₀, hfeq]
        have hcv : (c0 : G) * S.v2 * (c0 : G)⁻¹ = S.v2 := by
          rw [← Subgroup.mem_centralizer_iff.mp hc0V S.v2 S.v2_mem_V, mul_inv_cancel_right]
        show (c0 : G) * S.v2 * (c0 : G)⁻¹ * S.v2 ∈ fsuV1 T V
        rw [hcv, hvsq]
        exact Subgroup.one_mem _
      have h0 := eq_one_case_hat hsq hT hc43 hcubeC h1 h2 h12 hcc hc03 hc01 htn hc0fix hcomm
        hcub1 hcub2 hq h4 fun x hx => ⟨(hcoreE x hx c0 hc0L1).1, (hcoreE x hx c0 hc0L1).2.1,
          (hcoreE x hx c0 hc0L1).2.2, (hcoreE x hx g hgL).2.1, (hcoreE x hx g hgL).2.2⟩
      exact hv2V1 ((hf1 v₂).1 h0)
    · exact hd.false_of_S43 h13 h1334 h1337 hhat hρs hρk hρT hgL hgH hc43 hcT
  · have hcard := card_le_case_PA hsq hT hgen hcPA h1 h2 h12 hcc hq h4
      fun x hx => hcoreE x hx g hgL
    refine hsU.irrK7 hmax hαs hαk ?_
    rw [SecHyp.card_sec]
    calc W.relIndex U ≤ (fsuV1 T V).relIndex U :=
          Subgroup.relIndex_le_of_le_left hV1W (relIndex_ne_zero' _ _)
      _ = Nat.card (Sec (⊤ : Subgroup ↥U) ((fsuV1 T V).subgroupOf U)) := SecHyp.card_sec.symm
      _ ≤ 2 ^ 6 := hcard

end DK

end Setting4

open S7C in
theorem lem13824Red_of (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (h1337 : Stmt13_3_7) :
    ∀ (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (S : Setting4 G T L V),
      S.Hyp138 → ∀ H ∈ S.Hz, ∀ K ∈ cComp H, IsAlt 7 ↥(S.KSt H K) →
      ∀ [IsMulCommutative ↥(conjClosure S.V3 H)] (W : Subgroup G), fsuV1 T V ≤ W →
      W < conjClosure S.V3 H → H ≤ Subgroup.normalizer (W : Set G) →
      (∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
        H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H) →
      (∀ x ∈ pCoreOf 2 (S.L1 ⊔ T), ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) →
      XMod.IsIrrSec ↥(autSec (autOn K (conjClosure S.V3 H)) ⊤
        (W.subgroupOf (conjClosure S.V3 H)))
        (⊥ : Subgroup (Sec (⊤ : Subgroup ↥(conjClosure S.V3 H))
          (W.subgroupOf (conjClosure S.V3 H)))) ⊤ := by
  intro G _ _ T L V S hS H hH K hK h7 _ W hV1W hWU hHW hmax hA
  obtain ⟨hL1K, -, ⟨hKT, -⟩, hUK⟩ := h21 G T L V S hS H hH K hK
  have hKn : H ≤ Subgroup.normalizer (K : Set G) := (h16 G T L V S hS H hH K hK).1.1
  have hKH : K ≤ H := le_of_mem_cComp hK
  obtain ⟨α, hαs, hαk⟩ := S.exists_alpha7 hS hH hKH h7
  have hsimp : IsSimpleGroup ↥(S.KSt H K) := by
    obtain ⟨e⟩ := h7
    have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
      alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
    exact e.isSimpleGroup
  have hnab : ∃ k ∈ K, ∃ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∉ pCoreOf 2 H := by
    obtain ⟨a, ha⟩ := hαs ⟨_, A7F.a7_mem⟩
    obtain ⟨b, hb⟩ := hαs ⟨_, A7F.b7_mem⟩
    refine ⟨a, a.2, b, b.2, fun h => ?_⟩
    have h1 : α (a * b * a⁻¹ * b⁻¹) = 1 := (hαk _).2 (by simpa using h)
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, ha, hb] at h1
    have h2 := congrArg Subtype.val h1
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_one] at h2
    exact A7F.ab7_ne_ba7 (mul_inv_eq_one.1 (by rw [mul_inv_rev, ← mul_assoc]; exact h2))
  have hd : S.DK H K := ⟨hS, hH, hK, hKn, hKT.symm, hL1K, hUK, hsimp, hnab⟩
  obtain ⟨ρ, -, hρα, hρk⟩ := hd.exists_rho7 hαs hαk
  by_cases hodd : ∃ t : ↥H, (t : G) ∈ T ∧ ρ t ∉ alternatingGroup (Fin 7)
  · obtain ⟨ρ', hρ's, hρ'k, hρ'T, hTρ'⟩ := hd.exists_coords7 hαs hρα hρk hodd
    exact hd.irrSec_of_S7 h36 h139 h1334 h13 h13314 h13315 h1356two h1337 hV1W hWU hHW hmax hA
      hαs hαk hρ's hρ'k hρ'T hTρ'
  · push Not at hodd
    have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
    refine hd.irrSec_of_alt hsU hmax hαs hρα hρk fun h => ?_
    have hle : K ⊔ T ≤ ((alternatingGroup (Fin 7)).comap ρ).map H.subtype :=
      sup_le (fun k hk => ⟨⟨k, hKH hk⟩, by
          show ρ ⟨k, hKH hk⟩ ∈ alternatingGroup (Fin 7)
          rw [hρα ⟨k, hk⟩]
          exact (α ⟨k, hk⟩).2, rfl⟩)
        fun t ht => ⟨⟨t, hd.hTH ht⟩, hodd _ ht, rfl⟩
    obtain ⟨h', hh', hh'e⟩ := hle (hd.hHK.le h.2)
    have e : h' = h := Subtype.ext hh'e
    rw [← e]
    exact hh'

theorem lem13824_holds'
    (h1376 : Lem1376Full) (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) (h1337 : Stmt13_3_7) : Lem13824 :=
  lem13824_of h1376 h21 h16 h36 h139 h1334 h13 h13314 h13315 h1356two
    (lem13824Red_of h21 h16 h36 h139 h1334 h13 h13314 h13315 h1356two h1337)

end CFSG.Quasithin.H13.A6
