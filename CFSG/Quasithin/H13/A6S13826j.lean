module

public import CFSG.Quasithin.H13.A6S13826i

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace A6Gen

variable {G : Type} [Group G]

theorem exists_gen_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) :
    ∃ a ∈ A, a ≠ 1 ∧ ∀ b ∈ A, b = 1 ∨ b = a := by
  obtain ⟨y, hy, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥A)).mp hA
  refine ⟨y, y.2, fun h => hy (Subtype.ext h), fun b hb => ?_⟩
  by_cases hb1 : b = 1
  · exact Or.inl hb1
  · right
    exact congrArg Subtype.val (huniq ⟨b, hb⟩ fun e => hb1 (congrArg Subtype.val e))

theorem mem_or_mul_inv_mem_of_sup {A Y : Subgroup G}
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) {a : G} (hA : ∀ b ∈ A, b = 1 ∨ b = a) {x : G}
    (hx : x ∈ A ⊔ Y) : x ∈ Y ∨ x * a⁻¹ ∈ Y := by
  have hx' : x ∈ ((A ⊔ Y : Subgroup G) : Set G) := hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right A Y hAY] at hx'
  obtain ⟨b, hb, y, hy, rfl⟩ := Set.mem_mul.mp hx'
  rcases hA b hb with rfl | rfl
  · left
    simpa using hy
  · right
    have h1 : b * y * b⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hAY hb) y).mp hy
    simpa [mul_assoc] using h1

theorem comm_mem_of_elem {F : Subgroup G} (hF : IsElemAbelian 2 F) (Q : Subgroup G) :
    ∀ f ∈ F, ∀ f' ∈ F, f * f' * f⁻¹ * f'⁻¹ ∈ Q := by
  intro f hf f' hf'
  rw [isElemAbelian_comm hF hf hf']
  simp [mul_assoc]

theorem sq_mem_of_elem {F : Subgroup G} (hF : IsElemAbelian 2 F) (Q : Subgroup G) :
    ∀ f ∈ F, f * f ∈ Q := by
  intro f hf
  rw [← pow_two, isElemAbelian_pow_eq_one hF hf]
  exact Q.one_mem

theorem two_mul_le_of_pow {r i : ℕ} (h : (2 ^ r) ^ 2 ≤ (2 ^ i) ^ 3) : 2 * r ≤ 3 * i := by
  rw [← pow_mul, ← pow_mul] at h
  have := (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 h
  omega

theorem le_of_two_pow_le {r i : ℕ} (h : 2 ^ r ≤ 2 ^ i) : r ≤ i :=
  (pow_le_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 h

end A6Gen

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace D826

variable {H K : Subgroup G} (hd : S.D826 H K)
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

theorem false_of_ia (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hgen : stab γ = conjClosure (conjClosure S.V3 H) (stab γ) ⊔ (stab γ ⊓ stab γ'))
    (hA : F8.A₁ (fsuV1 T V) (g : G) ≤ W)
    (hi : mIdx (conjClosure S.V3 H)
        (centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G))) <
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G))) : False := by
  have hF := hd.hF
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hF.F911_3.1
  have hU2 : IsPGroup 2 (conjClosure S.V3 H) := isPGroup_of_isElemAbelian hF.F911_3
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
    hαs hαk
  have hUγH := hF.Uγ_le_H s
  have hVγH := hF.Vγ_le_H s
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have hVγel := hF.isElemAbelian_Vγ (g := g)
  have hUγQ := hd.not_Uγ_le s hDγ
  have hVγQ : ¬ F8.Uγ V H (g : G) ≤ pCoreOf 2 H := fun h => hUγQ (hF.Uγ_le_Vγ.trans h)
  have hr := hd.relIndex_Uγ_eq s
  have hi' := HypF98.relIndex_eq_two_pow_mIdx
    (Y := centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G))) hU2
  have h16 := hsU.natural_of_le hmax hαs hαk hUγH hUγQ (A6Gen.comm_mem_of_elem hUγel _)
    (A6Gen.sq_mem_of_elem hUγel _)
    (by rw [hi', hr]; exact Nat.pow_le_pow_right (by norm_num) hi.le)
  obtain ⟨hr8, hrk⟩ := hsU.rank hmax hαs hαk h16 hUγH hUγQ (A6Gen.comm_mem_of_elem hUγel _)
    (A6Gen.sq_mem_of_elem hUγel _)
  rw [hr, hi'] at hrk
  rw [hr] at hr8
  have hr3 := A6Gen.le_of_two_pow_le (hr8.trans (by norm_num : 8 ≤ 2 ^ 3))
  have h2r := A6Gen.two_mul_le_of_pow hrk
  obtain ⟨hv8, -⟩ := hsU.rank hmax hαs hαk h16 hVγH hVγQ (A6Gen.comm_mem_of_elem hVγel _)
    (A6Gen.sq_mem_of_elem hVγel _)
  have hr3' : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 3 := by omega
  have hVle := hsU.le_sup_of_relIndex_le hF.Uγ_le_Vγ hVγH (by rw [hr, hr3']; exact hv8)
  have hD2 := hd.relIndex_DH_le_two h13314 h13315 h1356two hαs hαk s hgen hVle
  have hDC : F8.DH S.V3 (fsuV1 T V) H (g : G) ≤
      centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G)) :=
    fun x hx => ⟨hx.1, hHW (hd.UH_le_H hx.1), fun u hu => hA (hx.2.2 u hu)⟩
  have hle := (Subgroup.relIndex_le_of_le_left hDC (relIndex_ne_zero' _ _)).trans hD2
  rw [hi'] at hle
  have := A6Gen.le_of_two_pow_le (hle.trans (by norm_num : 2 ≤ 2 ^ 1))
  omega

theorem false_of_ib (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    (hKW : ∃ k ∈ K, ∃ w ∈ W, k * w * k⁻¹ * w⁻¹ ∉ fsuV1 T V)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hDH : F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H)
    (hle : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (hpos : 0 < mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (hA : F8.A₁ (fsuV1 T V) (g : G) ≤ W)
    (hcomm : ⁅W, F8.Uγ S.V3 H (g : G)⁆ ≤ F8.A₁ (fsuV1 T V) (g : G) ⊔ fsuV1 T V) : False := by
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hF.F911_3.1
  have hU2 : IsPGroup 2 (conjClosure S.V3 H) := isPGroup_of_isElemAbelian hF.F911_3
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
    hαs hαk
  have hUγH := hF.Uγ_le_H s
  have hVγH := hF.Vγ_le_H s
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have hVγel := hF.isElemAbelian_Vγ (g := g)
  have hUγQ := hd.not_Uγ_le s hDγ
  have hVγQ : ¬ F8.Uγ V H (g : G) ≤ pCoreOf 2 H := fun h => hUγQ (hF.Uγ_le_Vγ.trans h)
  have hr := hd.relIndex_Uγ_eq s
  obtain ⟨a, -, -, hA2⟩ := A6Gen.exists_gen_of_card_two (hF.card_A₁ (g := g))
  have hAN : F8.A₁ (fsuV1 T V) (g : G) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hF.A₁_le_Uγ.trans hUγH).trans hF1.H_normalizes_V₁
  have hz : ∀ f ∈ F8.Uγ S.V3 H (g : G), ∀ x ∈ W, f * x * f⁻¹ * x⁻¹ ∈ fsuV1 T V ∨
      f * x * f⁻¹ * x⁻¹ * a⁻¹ ∈ fsuV1 T V := by
    intro f hf x hx
    have h1 := (F8.A₁ (fsuV1 T V) (g : G) ⊔ fsuV1 T V).inv_mem
      (hcomm (Subgroup.commutator_mem_commutator hx hf))
    have e : (⁅x, f⁆)⁻¹ = f * x * f⁻¹ * x⁻¹ := by rw [commutatorElement_def]; group
    rw [e] at h1
    exact A6Gen.mem_or_mul_inv_mem_of_sup hAN hA2 h1
  have h2 := hd.relIndex_le_two_of_U hαs hαk le_rfl hV1W hWU.le hHW hF1.H_normalizes_V₁ hKW
    hUγH (A6Gen.sq_mem_of_elem hUγel _) hz
  rw [hr] at h2
  have hr1 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 := by
    have := A6Gen.le_of_two_pow_le (h2.trans (by norm_num : 2 ≤ 2 ^ 1))
    omega
  obtain ⟨⟨-, hC1, -, -, -⟩, hVγ1, h3⟩ := lem13823_holds h21 h16 h36 h139 h1334 h13 h13314
    h13315 h1356two G T L V S hd.hS H hd.hH K hd.hK W hV1W hWU hHW hKW γ γ' g s hDγ hDH hle hr1
  rcases h3 with ⟨hA', -⟩ | ⟨-, hcent⟩
  · exact hA' hA
  have hCle : centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G)) ≤
      centralizerMod W (conjClosure S.V3 H) (F8.Uγ V H (g : G)) := by
    intro x hx
    refine ⟨hx.1, hx.2.1, fun v hv => ?_⟩
    have h1 := W.inv_mem (hcent x hx v hv)
    have e : (v * x * v⁻¹ * x⁻¹)⁻¹ = x * v * x⁻¹ * v⁻¹ := by group
    rwa [e] at h1
  have hidx : (centralizerMod W (conjClosure S.V3 H) (F8.Uγ V H (g : G))).relIndex
      (conjClosure S.V3 H) ≤ 2 := by
    have h1 := Subgroup.relIndex_le_of_le_left (L := conjClosure S.V3 H) hCle
      (relIndex_ne_zero' _ _)
    rw [HypF98.relIndex_eq_two_pow_mIdx
      (Y := centralizerMod W (conjClosure S.V3 H) (F8.Uγ S.V3 H (g : G))) hU2, hC1] at h1
    simpa using h1
  have hV4 : 4 ≤ (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H).relIndex (F8.Uγ V H (g : G)) := by
    rw [HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian hVγel)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hVγ1
  have h16' := hsU.natural_of_le hmax hαs hαk hVγH hVγQ (A6Gen.comm_mem_of_elem hVγel _)
    (A6Gen.sq_mem_of_elem hVγel _) (hidx.trans (by omega))
  obtain ⟨-, hrk⟩ := hsU.rank hmax hαs hαk h16' hVγH hVγQ (A6Gen.comm_mem_of_elem hVγel _)
    (A6Gen.sq_mem_of_elem hVγel _)
  have h3' := hrk.trans (Nat.pow_le_pow_left hidx 3)
  nlinarith

theorem false_of_iia (h13314 : Stmt13_3_14)
    (h13315 : Stmt13_3_15) (h1356two : Input1356Two) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hKW : ∃ k ∈ K, ∃ w ∈ W, k * w * k⁻¹ * w⁻¹ ∉ fsuV1 T V)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hgen : stab γ = conjClosure (conjClosure S.V3 H) (stab γ) ⊔ (stab γ ⊓ stab γ'))
    (hA : ¬ F8.A₁ (fsuV1 T V) (g : G) ≤ W)
    (hj : mIdx W (centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G))) <
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G))) : False := by
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have hU2 : IsPGroup 2 (conjClosure S.V3 H) := isPGroup_of_isElemAbelian hF.F911_3
  have hW2 : IsPGroup 2 W := hU2.to_le hWU.le
  have hUγH := hF.Uγ_le_H s
  have hVγH := hF.Vγ_le_H s
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have hVγel := hF.isElemAbelian_Vγ (g := g)
  have hUγQ := hd.not_Uγ_le s hDγ
  have hVγQ : ¬ F8.Uγ V H (g : G) ≤ pCoreOf 2 H := fun h => hUγQ (hF.Uγ_le_Vγ.trans h)
  have hr := hd.relIndex_Uγ_eq s
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg (Subtype.val : ↥(conjClosure S.V3 H) → G)
      (hF.F911_3.1.is_comm.comm ⟨a, hWU.le ha⟩ ⟨b, hWU.le hb⟩)
  obtain ⟨W₁, W₂, hV1W₁, hW₁W₂, hW₂W, hHW₁, hHW₂, hirr, hKnt⟩ :=
    exists_chief_sec hd.hKH (perfect_of_mem_cComp hd.hK) hV1W hWc hHW hF1.H_normalizes_V₁ hKW
  have hs := hd.secU hV1W₁ hW₁W₂.le (hW₂W.trans hWU.le) hHW₂ hHW₁ hKnt hαs hαk
  have : IsMulCommutative ↥W₂ := ⟨⟨fun a b => Subtype.ext (hWc a (hW₂W a.2) b (hW₂W b.2))⟩⟩
  have hj' := HypF98.relIndex_eq_two_pow_mIdx
    (Y := centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G))) hW2
  have hC₁ : (centralizerMod W₁ W₂ (F8.Uγ S.V3 H (g : G))).relIndex W₂ ≤
      (centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G))).relIndex W :=
    relIndex_le_of_inf_le hW₂W fun x hx =>
      ⟨hx.2, hHW₁ (hd.UH_le_H (hWU.le hx.1.1)), fun u hu => hV1W₁ (hx.1.2.2 u hu)⟩
  have h16 := hs.natural_of_le hirr hαs hαk hUγH hUγQ (A6Gen.comm_mem_of_elem hUγel _)
    (A6Gen.sq_mem_of_elem hUγel _)
    (hC₁.trans (by rw [hj', hr]; exact Nat.pow_le_pow_right (by norm_num) hj.le))
  obtain ⟨hr8, hrk⟩ := hs.rank hirr hαs hαk h16 hUγH hUγQ (A6Gen.comm_mem_of_elem hUγel _)
    (A6Gen.sq_mem_of_elem hUγel _)
  have hrk' := hrk.trans (Nat.pow_le_pow_left (hC₁.trans hj'.le) 3)
  rw [hr] at hrk' hr8
  have hr3 := A6Gen.le_of_two_pow_le (hr8.trans (by norm_num : 8 ≤ 2 ^ 3))
  have h2r := A6Gen.two_mul_le_of_pow hrk'
  obtain ⟨hv8, -⟩ := hs.rank hirr hαs hαk h16 hVγH hVγQ (A6Gen.comm_mem_of_elem hVγel _)
    (A6Gen.sq_mem_of_elem hVγel _)
  have hr3' : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 3 := by omega
  have hVle := hs.le_sup_of_relIndex_le hF.Uγ_le_Vγ hVγH (by rw [hr, hr3']; exact hv8)
  have hD2 := hd.relIndex_DH_le_two h13314 h13315 h1356two hαs hαk s hgen hVle
  have hAW : F8.A₁ (fsuV1 T V) (g : G) ⊓ W = ⊥ := by
    by_contra hne
    exact hA (le_of_card_eq_two_of_inf_ne_bot (hF.card_A₁ (g := g)) hne)
  have hDW : F8.DH S.V3 (fsuV1 T V) H (g : G) ⊓ W ≤
      centralizerMod (fsuV1 T V) W (F8.Uγ S.V3 H (g : G)) := by
    rintro x ⟨hxD, hxW⟩
    refine ⟨hxW, hF1.H_normalizes_V₁ (hd.UH_le_H hxD.1), fun u hu => ?_⟩
    have h1 : x * u * x⁻¹ * u⁻¹ ∈ W := by
      have hu' : u * x⁻¹ * u⁻¹ ∈ W :=
        (Subgroup.mem_normalizer_iff.mp (hHW (hUγH hu)) _).mp (W.inv_mem hxW)
      have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      rw [e]
      exact W.mul_mem hxW hu'
    have h2 : x * u * x⁻¹ * u⁻¹ ∈ F8.A₁ (fsuV1 T V) (g : G) ⊓ W := ⟨hxD.2.2 u hu, h1⟩
    rw [hAW, Subgroup.mem_bot] at h2
    rw [h2]
    exact (fsuV1 T V).one_mem
  have hle := (relIndex_le_of_inf_le hWU.le hDW).trans hD2
  rw [hj'] at hle
  have := A6Gen.le_of_two_pow_le (hle.trans (by norm_num : 2 ≤ 2 ^ 1))
  omega

theorem false_of_iib (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H)
    (hKW : ∃ k ∈ K, ∃ w ∈ W, k * w * k⁻¹ * w⁻¹ ∉ fsuV1 T V)
    {γ γ' : F8.Geom T L H} {g : ↥((L ⊔ T) ⊔ H)} (s : F8Setup T V L H γ γ' g)
    (hDγ : F8.Dγ S.V3 (fsuV1 T V) H (g : G) < F8.Uγ S.V3 H (g : G))
    (hDH : F8.DH S.V3 (fsuV1 T V) H (g : G) < conjClosure S.V3 H)
    (hle : mIdx (conjClosure S.V3 H) (F8.DH S.V3 (fsuV1 T V) H (g : G)) ≤
      mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (hpos : 0 < mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)))
    (hA : ¬ F8.A₁ (fsuV1 T V) (g : G) ≤ W)
    (hcomm : ⁅conjClosure S.V3 H, F8.Uγ S.V3 H (g : G)⁆ ≤ F8.A₁ (fsuV1 T V) (g : G) ⊔ W) :
    False := by
  have hF := hd.hF
  have hF1 := hF.toHypF91
  have : IsMulCommutative ↥(conjClosure S.V3 H) := hF.F911_3.1
  have hU2 : IsPGroup 2 (conjClosure S.V3 H) := isPGroup_of_isElemAbelian hF.F911_3
  have hW2 : IsPGroup 2 W := hU2.to_le hWU.le
  have hsU := hd.secU hV1W hWU.le le_rfl (le_normalizer_conjClosure _ _) hHW (hd.knt_top hWU)
    hαs hαk
  have hUγH := hF.Uγ_le_H s
  have hVγH := hF.Vγ_le_H s
  have hUγel := hF.isElemAbelian_Uγ (g := g)
  have hVγel := hF.isElemAbelian_Vγ (g := g)
  have hVγQ : ¬ F8.Uγ V H (g : G) ≤ pCoreOf 2 H := fun h =>
    hd.not_Uγ_le s hDγ (hF.Uγ_le_Vγ.trans h)
  have hr := hd.relIndex_Uγ_eq s
  obtain ⟨a, -, -, hA2⟩ := A6Gen.exists_gen_of_card_two (hF.card_A₁ (g := g))
  have hAN : F8.A₁ (fsuV1 T V) (g : G) ≤ Subgroup.normalizer (W : Set G) :=
    (hF.A₁_le_Uγ.trans hUγH).trans hHW
  have hz : ∀ f ∈ F8.Uγ S.V3 H (g : G), ∀ x ∈ conjClosure S.V3 H, f * x * f⁻¹ * x⁻¹ ∈ W ∨
      f * x * f⁻¹ * x⁻¹ * a⁻¹ ∈ W := by
    intro f hf x hx
    have h1 := (F8.A₁ (fsuV1 T V) (g : G) ⊔ W).inv_mem
      (hcomm (Subgroup.commutator_mem_commutator hx hf))
    have e : (⁅x, f⁆)⁻¹ = f * x * f⁻¹ * x⁻¹ := by rw [commutatorElement_def]; group
    rw [e] at h1
    exact A6Gen.mem_or_mul_inv_mem_of_sup hAN hA2 h1
  have h2 := hsU.relIndex_le_two_of_transv hmax hαs hαk hUγH (A6Gen.sq_mem_of_elem hUγel _) hz
  rw [hr] at h2
  have hr1 : mIdx (F8.Uγ S.V3 H (g : G)) (F8.Dγ S.V3 (fsuV1 T V) H (g : G)) = 1 := by
    have := A6Gen.le_of_two_pow_le (h2.trans (by norm_num : 2 ≤ 2 ^ 1))
    omega
  obtain ⟨⟨hC1, -, -, -, -⟩, hVγ1, h3⟩ := lem13823_holds h21 h16 h36 h139 h1334 h13 h13314
    h13315 h1356two G T L V S hd.hS H hd.hH K hd.hK W hV1W hWU hHW hKW γ γ' g s hDγ hDH hle hr1
  rcases h3 with ⟨-, hcent⟩ | ⟨hA', -⟩
  swap
  · exact hA hA'
  have hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    congrArg (Subtype.val : ↥(conjClosure S.V3 H) → G)
      (hF.F911_3.1.is_comm.comm ⟨a, hWU.le ha⟩ ⟨b, hWU.le hb⟩)
  obtain ⟨W₁, W₂, hV1W₁, hW₁W₂, hW₂W, hHW₁, hHW₂, hirr, hKnt⟩ :=
    exists_chief_sec hd.hKH (perfect_of_mem_cComp hd.hK) hV1W hWc hHW hF1.H_normalizes_V₁ hKW
  have hs := hd.secU hV1W₁ hW₁W₂.le (hW₂W.trans hWU.le) hHW₂ hHW₁ hKnt hαs hαk
  have : IsMulCommutative ↥W₂ := ⟨⟨fun a b => Subtype.ext (hWc a (hW₂W a.2) b (hW₂W b.2))⟩⟩
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
  have hV4 : 4 ≤ (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H).relIndex (F8.Uγ V H (g : G)) := by
    rw [HypF98.relIndex_eq_two_pow_mIdx (isPGroup_of_isElemAbelian hVγel)]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) hVγ1
  have h16' := hs.natural_of_le hirr hαs hαk hVγH hVγQ (A6Gen.comm_mem_of_elem hVγel _)
    (A6Gen.sq_mem_of_elem hVγel _) (hC₁.trans (by omega))
  obtain ⟨-, hrk⟩ := hs.rank hirr hαs hαk h16' hVγH hVγQ (A6Gen.comm_mem_of_elem hVγel _)
    (A6Gen.sq_mem_of_elem hVγel _)
  have h3' := hrk.trans (Nat.pow_le_pow_left hC₁ 3)
  nlinarith

theorem triv_of_max (h21 : Lem13821) (h16 : Lem13816)
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9)
    (h1334 : Stmt13_3_4) (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15)
    (h1356two : Input1356Two) {α : ↥K →* alternatingGroup (Fin 6)}
    (hαs : Function.Surjective α) (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    {W : Subgroup G} (hV1W : fsuV1 T V ≤ W) (hWU : W < conjClosure S.V3 H)
    (hHW : H ≤ Subgroup.normalizer (W : Set G))
    (hmax : ∀ W' : Subgroup G, W ≤ W' → W' ≤ conjClosure S.V3 H →
      H ≤ Subgroup.normalizer (W' : Set G) → W' = W ∨ W' = conjClosure S.V3 H) :
    ∀ k ∈ K, ∀ w ∈ W, k * w * k⁻¹ * w⁻¹ ∈ fsuV1 T V := by
  by_contra hKW
  push Not at hKW
  obtain ⟨-, -, hnt, hdich⟩ :=
    lem13822_holds h21 h16 G T L V S hd.hS H hd.hH K hd.hK W hV1W hWU hHW hKW
  obtain ⟨γ, γ', g, s, hDγ, hDH, hpos, hle, -⟩ := S.case2_of_no_transv hd.hF hnt
  have hHKLT : H = K ⊔ (S.L1 ⊔ T) := by
    rw [← sup_assoc, sup_eq_left.2 hd.hL1K]
    exact hd.hHK
  have hgen := lem13818Gen_holds h36 h139 h1334 h13 G T L V S hd.hS H hd.hH K hd.hK hd.hKn
    hHKLT γ γ' g s (conjClosure S.V3 H) le_rfl (fun h => hDH.ne (le_antisymm hDH.le h))
  rcases hdich γ γ' g s hDγ hDH hle with ⟨hA, hi, hieq⟩ | ⟨hA, hj, hjeq⟩
  · rcases hi.lt_or_eq with hi | hi
    · exact hd.false_of_ia h13314 h13315 h1356two hαs hαk hV1W hWU hHW hmax s hDγ hgen hA hi
    · exact hd.false_of_ib h21 h16 h36 h139 h1334 h13 h13314 h13315 h1356two hαs hαk hV1W hWU
        hHW hmax hKW s hDγ hDH hle hpos hA (hieq hi).2
  · rcases hj.lt_or_eq with hj | hj
    · exact hd.false_of_iia h13314 h13315 h1356two hαs hαk hV1W hWU hHW hKW s hDγ hgen hA hj
    · exact hd.false_of_iib h21 h16 h36 h139 h1334 h13 h13314 h13315 h1356two hαs hαk hV1W hWU
        hHW hmax hKW s hDγ hDH hle hpos hA (hjeq hj).2

end D826

end Setting4

end CFSG.Quasithin.H13.A6
