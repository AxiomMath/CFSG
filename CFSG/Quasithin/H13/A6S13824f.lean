module

public import CFSG.Quasithin.H13.A6S13824e
public import CFSG.Quasithin.H13.A6S13826j
public import CFSG.Quasithin.H13.A6S13824a

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem relIndex_Uγ_eq {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)}
    (s : F8Setup T V L H γ γ' g) :
    (F8.Uγ S.V3 H (g : G) ⊓ pCoreOf 2 H).relIndex (F8.Uγ S.V3 H (g : G)) =
      2 ^ mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) := by
  rw [← hd.hF.Dγ_eq_inf_pCoreOf s]
  exact HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian hd.hF.isElemAbelian_Uγ)

theorem not_Uγ_le {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G)) :
    ¬ F8.Uγ S.V3 H (g : G) ≤ pCoreOf 2 H := fun h =>
  hDγ.ne (by rw [hd.hF.Dγ_eq_inf_pCoreOf s]; exact inf_eq_left.2 h)

theorem triv_of_max7 (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) {α : ↥K →* alternatingGroup (Fin 7)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {ρ : ↥H →* Perm (Fin 7)} (hρk : ∀ k : ↥K, ρ (Subgroup.inclusion hd.hKH k) = α k)
    (hρ1 : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) {W : Subgroup G}
    (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H) :
    ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ * w⁻¹ ∈ fsuV1 T V := by
  by_contra hKW
  push Not at hKW
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hF.F911_3.1
  have hU2 : IsPGroup 2 (conjClosure S.V3 H) := isPGroup_of_isElemAbelian hF.F911_3
  have hW2 : IsPGroup 2 W := hU2.to_le hWU.le
  obtain ⟨-, -, hnt, hdich⟩ :=
    lem13822_holds h21 h16 G T L V S hd.hS H hd.hH K hd.hK W hV1W hWU hHW hKW
  obtain ⟨γ, γ', g, s, hDγ, hDH, hpos, hle, -⟩ := S.case2_of_no_transv hF hnt
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
  have hsW := hd.secU le_rfl hV1W hWU.le hHW hF1.H_normalizes_V₁ hKW
  have hUγH := hF.Uγ_le_H s
  have hVγH := hF.Vγ_le_H s
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have hVγel := hF.isElemAbelian_Vγ (g := g)
  have hr := hd.relIndex_Uγ_eq s
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg (Subtype.val : ↥(conjClosure S.V3 H) → G)
      (hF.F911_3.1.is_comm.comm ⟨a, hWU.le ha⟩ ⟨b, hWU.le hb⟩)
  obtain ⟨W₁, W₂, hV1W₁, hW₁W₂, hW₂W, hHW₁, hHW₂, hirr, hKnt⟩ :=
    exists_chief_sec hd.hKH (perfect_of_mem_cComp hd.hK) hV1W hWc hHW hF1.H_normalizes_V₁ hKW
  have hs₂ := hd.secU hV1W₁ hW₁W₂.le (hW₂W.trans hWU.le) hHW₂ hHW₁ hKnt
  have : IsMulCommutative ↥W₂ := ⟨⟨fun a b => Subtype.ext (hWc a (hW₂W a.2) b (hW₂W b.2))⟩⟩
  have : IsMulCommutative ↥W := ⟨⟨fun a b => Subtype.ext (hWc a a.2 b b.2)⟩⟩
  have hVγ_top : ∀ C : Subgroup G, mIdx (conjClosure S.V3 H) C = 1 →
      C ≤ centralizerMod W (conjClosure S.V3 H) (F8.Uγ V H (g : G)) →
      mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H) ≤ 1 := by
    intro C hC1 hCle
    have h1 := hsU.relIndex_le_index7 hmax hαs hαk hρk hρ1 hVγH
      (A6Gen.comm_mem_of_elem hVγel _) (A6Gen.sq_mem_of_elem hVγel _)
    have h2 := Subgroup.relIndex_le_of_le_left (L := conjClosure S.V3 H) hCle
      (relIndex_ne_zero' _ _)
    rw [HypF98.relIndex_eq_two_pow_mIdx (Y := C) hU2, hC1] at h2
    rw [HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian hVγel)] at h1
    exact A6Gen.le_of_two_pow_le (h1.trans (h2.trans (by norm_num)))
  rcases hdich γ γ' g s hDγ hDH hle with ⟨hA, hi, hieq⟩ | ⟨hA, hj, hjeq⟩
  ·
    rcases hi.lt_or_eq with hi | hi
    ·
      have h1 := hsU.relIndex_le_index7 hmax hαs hαk hρk hρ1 hUγH
        (A6Gen.comm_mem_of_elem hUγel _) (A6Gen.sq_mem_of_elem hUγel _)
      rw [hr, HypF98.relIndex_eq_two_pow_mIdx hU2] at h1
      have := A6Gen.le_of_two_pow_le h1
      omega
    ·
      obtain ⟨a, -, -, hA2⟩ := A6Gen.exists_gen_of_card_two (hF.card_A₁ (g := g))
      have hAN : F8.A₁ (fsuV1 T V) (g : G) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
        (hF.A₁_le_Uγ.trans hUγH).trans hF1.H_normalizes_V₁
      have hcomm := (hieq hi).2
      have hz : ∀ f ∈ F8.Uγ S.V3 H (g : G), ∀ x ∈ W, f * x * f⁻¹ * x⁻¹ ∈ fsuV1 T V ∨
          f * x * f⁻¹ * x⁻¹ * a⁻¹ ∈ fsuV1 T V := by
        intro f hf x hx
        have h1 := (F8.A₁ (fsuV1 T V) (g : G) ⊔ fsuV1 T V).inv_mem
          (hcomm (Subgroup.commutator_mem_commutator hx hf))
        have e : (⁅x, f⁆)⁻¹ = f * x * f⁻¹ * x⁻¹ := by rw [commutatorElement_def]; group
        rw [e] at h1
        exact A6Gen.mem_or_mul_inv_mem_of_sup hAN hA2 h1
      have h2 := hsW.relIndex_le_two_of_transv7 hαs hαk hρk hρ1 hUγH hz
      rw [hr] at h2
      have hr1 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 := by
        have := A6Gen.le_of_two_pow_le (h2.trans (by norm_num : 2 ≤ 2 ^ 1))
        omega
      obtain ⟨⟨-, hC1, -, -, -⟩, hVγ1, h3⟩ := lem13823_holds h21 h16 h36 h139 h1334 h13 h13314
        h13315 h1356two G T L V S hd.hS H hd.hH K hd.hK W hV1W hWU hHW hKW γ γ' g s hDγ hDH
        hle hr1
      rcases h3 with ⟨hA', -⟩ | ⟨-, hcent⟩
      · exact hA' hA
      have hCle : centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G)) ≤
          centralizerMod W (conjClosure S.V3 H) (F8.Uγ V H (g : G)) := by
        intro x hx
        refine ⟨hx.1, hx.2.1, fun v hv => ?_⟩
        have h1 := W.inv_mem (hcent x hx v hv)
        have e : (v * x * v⁻¹ * x⁻¹)⁻¹ = x * v * x⁻¹ * v⁻¹ := by group
        rwa [e] at h1
      have := hVγ_top _ hC1 hCle
      omega
  ·
    rcases hj.lt_or_eq with hj | hj
    ·
      have h1 := hs₂.relIndex_le_index7 hirr hαs hαk hρk hρ1 hUγH
        (A6Gen.comm_mem_of_elem hUγel _) (A6Gen.sq_mem_of_elem hUγel _)
      have hC₁ : (centralizerMod W₁ W₂ (F8.Uγ S.V3 H (g : G))).relIndex W₂ ≤
          (centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G))).relIndex W :=
        relIndex_le_of_inf_le hW₂W fun x hx =>
          ⟨hx.2, hHW₁ (hd.UH_le_H (hWU.le hx.1.1)), fun u hu => hV1W₁ (hx.1.2.2 u hu)⟩
      rw [hr] at h1
      rw [HypF98.relIndex_eq_two_pow_mIdx hW2] at hC₁
      have := A6Gen.le_of_two_pow_le (h1.trans hC₁)
      omega
    ·
      obtain ⟨a, -, -, hA2⟩ := A6Gen.exists_gen_of_card_two (hF.card_A₁ (g := g))
      have hAN : F8.A₁ (fsuV1 T V) (g : G) ≤ Subgroup.normalizer (W : Set G) :=
        (hF.A₁_le_Uγ.trans hUγH).trans hHW
      have hcomm := (hjeq hj).2
      have hz : ∀ f ∈ F8.Uγ S.V3 H (g : G), ∀ x ∈ conjClosure S.V3 H,
          f * x * f⁻¹ * x⁻¹ ∈ W ∨ f * x * f⁻¹ * x⁻¹ * a⁻¹ ∈ W := by
        intro f hf x hx
        have h1 := (F8.A₁ (fsuV1 T V) (g : G) ⊔ W).inv_mem
          (hcomm (Subgroup.commutator_mem_commutator hx hf))
        have e : (⁅x, f⁆)⁻¹ = f * x * f⁻¹ * x⁻¹ := by rw [commutatorElement_def]; group
        rw [e] at h1
        exact A6Gen.mem_or_mul_inv_mem_of_sup hAN hA2 h1
      have h2 := hsU.relIndex_le_two_of_transv7 hαs hαk hρk hρ1 hUγH hz
      rw [hr] at h2
      have hr1 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 := by
        have := A6Gen.le_of_two_pow_le (h2.trans (by norm_num : 2 ≤ 2 ^ 1))
        omega
      obtain ⟨⟨hC1, -, -, -, -⟩, hVγ1, h3⟩ := lem13823_holds h21 h16 h36 h139 h1334 h13 h13314
        h13315 h1356two G T L V S hd.hS H hd.hH K hd.hK W hV1W hWU hHW hKW γ γ' g s hDγ hDH
        hle hr1
      rcases h3 with ⟨-, hcent⟩ | ⟨hA', -⟩
      swap
      · exact hA hA'
      have hC₁ : (centralizerMod W₁ W₂ (F8.Uγ V H (g : G))).relIndex W₂ ≤ 2 := by
        have h1 : (centralizerMod W₁ W₂ (F8.Uγ V H (g : G))).relIndex W₂ ≤
            (centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G))).relIndex W := by
          refine relIndex_le_of_inf_le hW₂W fun x hx => ⟨hx.2, hHW₁ (hd.UH_le_H (hWU.le hx.1.1)),
            fun v hv => ?_⟩
          have h1 := (fsuV1 T V).inv_mem (hcent x hx.1 v hv)
          have e : (v * x * v⁻¹ * x⁻¹)⁻¹ = x * v * x⁻¹ * v⁻¹ := by group
          rw [e] at h1
          exact hV1W₁ h1
        rw [HypF98.relIndex_eq_two_pow_mIdx hW2, hC1] at h1
        simpa using h1
      have h1 := hs₂.relIndex_le_index7 hirr hαs hαk hρk hρ1 hVγH
        (A6Gen.comm_mem_of_elem hVγel _) (A6Gen.sq_mem_of_elem hVγel _)
      rw [HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian hVγel)] at h1
      have := A6Gen.le_of_two_pow_le (h1.trans (hC₁.trans (by norm_num : 2 ≤ 2 ^ 1)))
      omega

end DK

end Setting4

end CFSG.Quasithin.H13.A6
