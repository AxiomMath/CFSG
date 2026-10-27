module

public import CFSG.Quasithin.H13.NQS134108A

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem mem_L1T_of_mem_inf (hM : normalizer (L : Set G) = L ⊔ T)
    (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V) {g : G} (hgK : g ∈ K)
    (hgM : g ∈ normalizer (L : Set G)) : g ∈ L₁Of L (fsuV1 T V) ⊔ T := by
  refine centralizer_Z_le_L1T S hM hZV1 ?_
  have hgV : g ∈ normalizer (V : Set G) := by
    rw [hM] at hgM
    exact sup_le S.frame.L_le S.frame.T_le hgM
  rw [hZV1]
  exact mem_centralizer_V1 S D.zV1 D.zL (S.normalizer_V_le_centralizer_ZV hgV)
    (mem_centralizer_singleton_iff.mp (D.Kz hgK))

theorem h2_of_parData (hM : normalizer (L : Set G) = L ⊔ T)
    (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    {Γ : Type} [Group Γ] {ρ : ↥(normalizer (W : Set G)) →* Γ} {Q P B P₂ : Subgroup Γ}
    (DP : ParData K T W (L₁Of L (fsuV1 T V) ⊔ T) ρ Q P) (hPQ : P ≤ Q)
    (hTB : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ T ⊓ K → ρ g ∈ B)
    (hB : ∀ β ∈ B, ∃ g : ↥(normalizer (W : Set G)), (g : G) ∈ T ⊓ K ∧ ρ g = β)
    (hcls : ∀ Y : Subgroup Γ, B ≤ Y → Y ≤ Q → Y = B ∨ Y = P ∨ Y = P₂ ∨ Y = Q)
    (hBP₂ : B ≤ P₂) (hP₂Q : P₂ ≤ Q) (hP₂P : ¬ P₂ ≤ P) (hPP₂ : ¬ P ≤ P₂)
    (hTY : ∀ t : ↥(normalizer (W : Set G)), (t : G) ∈ T → ∀ γ ∈ P₂, ρ t * γ * (ρ t)⁻¹ ∈ P₂)
    (h3 : B.relIndex P₂ = 3) {γ β : Γ} (hγ : γ ∈ P₂) (hβ : β ∈ B) (hγβ : γ * β * γ⁻¹ ∉ B) :
    IsHStar T (normalizer (L : Set G)) (DP.parOf P₂) ∧ DP.parOf P₂ ≤ K ⊔ T ∧
      (∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ K ⊔ T →
        X = DP.parOf P₂) ∧
      quasithinO2QuotientIso (DP.parOf P₂) (Perm (Fin 3)) ∧
      (∀ X : Subgroup G, T ≤ X → X ≤ K ⊔ T →
        X = T ∨ X = L₁Of L (fsuV1 T V) ⊔ T ∨ X = DP.parOf P₂ ∨ X = K ⊔ T) ∧
      ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ DP.parOf P₂ ∧ ¬ DP.parOf P₂ ≤ L₁Of L (fsuV1 T V) ⊔ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set L₁ := L₁Of L (fsuV1 T V) with hL₁
  set H₂ := DP.parOf P₂ with hH₂
  have hcl : ∀ X : Subgroup G, T ≤ X → X ≤ K ⊔ T →
      X = T ∨ X = L₁ ⊔ T ∨ X = H₂ ∨ X = K ⊔ T := fun X hTX hXKT =>
    DP.overgroups hB hcls hTX hXKT
  have himg : DP.img' H₂ ≤ P₂ := DP.img'_parOf_le D.TW hTB hBP₂ hTY
  have himg' : P₂ ≤ DP.img' H₂ := DP.le_img'_parOf hP₂Q
  have hP1 : P ≤ DP.img' (L₁ ⊔ T) := DP.P_le_img' hPQ le_rfl
  have hP1' : DP.img' (L₁ ⊔ T) ≤ P := by
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hgX, hgK⟩ := mem_inf.1 (mem_subgroupOf.1 hg)
    exact (DP.P_iff g hgK).2 hgX
  have hinc1 : ¬ L₁ ⊔ T ≤ H₂ := fun h => hPP₂ (hP1.trans ((DP.img'_mono h).trans himg))
  have hinc2 : ¬ H₂ ≤ L₁ ⊔ T := fun h => hP₂P (himg'.trans ((DP.img'_mono h).trans hP1'))
  have hL1TM : L₁ ⊔ T ≤ normalizer (L : Set G) :=
    sup_le (((oTwoRes_le _).trans inf_le_left).trans le_normalizer) S.T_le_NL
  have hH₂KT : H₂ ≤ K ⊔ T := DP.parOf_le_sup P₂
  have hTH₂ : T ≤ H₂ := DP.T_le_parOf P₂
  have hH₂M : ¬ H₂ ≤ normalizer (L : Set G) := by
    intro h
    apply hP₂P
    refine himg'.trans ?_
    rintro _ ⟨g, hg, rfl⟩
    obtain ⟨hgX, hgK⟩ := mem_inf.1 (mem_subgroupOf.1 hg)
    exact (DP.P_iff g hgK).2 (D.mem_L1T_of_mem_inf hM hZV1 hgK (h hgX))
  have hInH : InH T H₂ := by
    refine ⟨hTH₂, fun h => D.Kf.1.2.2.2 (le_bot_iff.1 ?_)⟩
    rw [← h]
    exact LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf D.isSylowTwoOf).trans hTH₂)
      (hH₂KT.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 _))
      (LieType.BorelTits.pCoreOf_isPGroup 2 _)
  have hstar : IsHStar T (normalizer (L : Set G)) H₂ := by
    refine ⟨hInH, hH₂M, fun Y hY hYH hYM => ?_⟩
    rcases hcl Y hY.1 (hYH.trans hH₂KT) with h | h | h | h
    · exact absurd (h ▸ S.T_le_NL) hYM
    · exact absurd (h ▸ hL1TM) hYM
    · exact h
    · exact le_antisymm hYH (h ▸ hH₂KT)
  refine ⟨hstar, hH₂KT, fun X hX hXKT => ?_, ?_, hcl, hinc1, hinc2⟩
  · rcases hcl X hX.1.1 hXKT with h | h | h | h
    · exact absurd (h ▸ S.T_le_NL) hX.2.1
    · exact absurd (h ▸ hL1TM) hX.2.1
    · exact h
    · exact (hX.2.2 H₂ hInH (h ▸ hH₂KT) hH₂M).symm
  · exact DP.quot_parOf D.TW hTB hB hP₂Q hTY h3 hγ hβ hγβ
      (A5.isSylowTwoOf_of_le S.h13.sylow hTH₂)

theorem exists_h2_l32 (hM : normalizer (L : Set G) = L ⊔ T)
    (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1) :
    ∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ K ⊔ T ∧
      (∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ K ⊔ T → X = H₂) ∧
      quasithinO2QuotientIso H₂ (Perm (Fin 3)) ∧
      (∀ X : Subgroup G, T ≤ X → X ≤ K ⊔ T →
        X = T ∨ X = L₁Of L (fsuV1 T V) ⊔ T ∨ X = H₂ ∨ X = K ⊔ T) ∧
      ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ H₂ ∧ ¬ H₂ ≤ L₁Of L (fsuV1 T V) ⊔ T := by
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  obtain ⟨C₀⟩ := exists_l3Coords hnat
  obtain ⟨C, hCB⟩ := C₀.exists_conj_eq D.Wirr.2.2.1 (S.h13.sylow.1.to_le inf_le_left)
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inl hK3))
  have hCKT : K ⊓ centralizer (W : Set G) ≤ T :=
    (inf_le_inf_right (centralizer (W : Set G)) (le_sup_left : K ≤ K ⊔ T)).trans
      (D.inf_centralizer_le_T hZK)
  obtain ⟨DP, hB⟩ := l32_parData C hCB D.Wirr.2.2.1 D.T_le_K D.isSylowTwoOf_inf hCKT
    (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
    D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW) D.Wirr.2.1 S.h13.sylow.1
    D.TW D.W_le_T
  have hTY : ∀ t : ↥(normalizer (W : Set G)), (t : G) ∈ T → ∀ γ ∈ l3P2,
      C.ρ t * γ * (C.ρ t)⁻¹ ∈ l3P2 := by
    intro t ht γ hγ
    have htB : C.ρ t ∈ l3B := by
      refine l3B_self_normalizing _ fun b hb => ?_
      obtain ⟨s, hs, rfl⟩ := hB b hb
      have h1 : (t : G) * s * (t : G)⁻¹ ∈ T := mul_mem (mul_mem ht (mem_inf.1 hs).1) (inv_mem ht)
      have h2 : (t : G) * s * (t : G)⁻¹ ∈ K :=
        (mem_normalizer_iff.mp (D.T_le_K ht) s).mp (mem_inf.1 hs).2
      have := hCB (t * s * t⁻¹) (mem_inf.2 ⟨h1, h2⟩)
      rwa [map_mul, map_mul, map_inv] at this
    have htP : C.ρ t ∈ l3P2 := l3B_le_P2 _ htB
    exact mul_mem (mul_mem htP hγ) (inv_mem htP)
  obtain ⟨g, hg, b, hb, hgb⟩ := exists_l3P2_conj
  exact ⟨_, D.h2_of_parData hM hZV1 DP le_top hCB hB (fun Y hY _ => l3_overgroups hY)
    (fun x hx => l3B_le_P2 x hx) le_top l3P2_not_le l3Stab_not_le_P2 hTY l3B_relIndex_P2
    (mem_l3P2.2 hg) hb hgb⟩

theorem exists_h2_nat (h1332 : Stmt13_3_2) (hM : normalizer (L : Set G) = L ⊔ T)
    (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hK6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (h6 : AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6) :
    ∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ K ⊔ T ∧
      (∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ K ⊔ T → X = H₂) ∧
      quasithinO2QuotientIso H₂ (Perm (Fin 3)) ∧
      (∀ X : Subgroup G, T ≤ X → X ≤ K ⊔ T →
        X = T ∨ X = L₁Of L (fsuV1 T V) ⊔ T ∨ X = H₂ ∨ X = K ⊔ T) ∧
      ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ H₂ ∧ ¬ H₂ ≤ L₁Of L (fsuV1 T V) ⊔ T := by
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  obtain ⟨R⟩ := exists_rawData4 D.Wirr.2.2.1 h6
  obtain ⟨F⟩ := exists_frame4 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW D.isSylowTwoOf_inf
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
  obtain ⟨DP, hB⟩ := frame4_parData F D.T_le_K (D.inf_centralizer_le_T hZK)
    (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
    D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
  have hTB : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ T ⊓ K → F.ρ g ∈ a6D := fun g hg =>
    (mem_a6D_iff _).2 ⟨F.T_D g (mem_inf.1 hg).1,
      Perm.mem_alternatingGroup.1 ((F.image_L _).1 ⟨g, (mem_inf.1 hg).2, rfl⟩)⟩
  have hTY : ∀ t : ↥(normalizer (W : Set G)), (t : G) ∈ T → ∀ γ ∈ a6P2,
      F.ρ t * γ * (F.ρ t)⁻¹ ∈ a6P2 := fun t ht γ hγ =>
    a6P2_conj_D _ (F.T_D t ht) γ hγ
  obtain ⟨γ, hγ, β, hβ, hγβ⟩ := exists_a6P2_conj
  exact ⟨_, D.h2_of_parData hM hZV1 DP stab45_le_alt hTB hB
    (fun Y hY hYA => a6_overgroups hY hYA)
    (fun x hx => a6D_le_P2 x hx) a6P2_le_alt a6P2_not_le stab45_not_le_P2 hTY a6D_relIndex_P2
    hγ hβ hγβ⟩

theorem exists_h2_core (h1332 : Stmt13_3_2) (hM : normalizer (L : Set G) = L ⊔ T)
    (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hK6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (hc : FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥) :
    ∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ K ⊔ T ∧
      (∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ K ⊔ T → X = H₂) ∧
      quasithinO2QuotientIso H₂ (Perm (Fin 3)) ∧
      (∀ X : Subgroup G, T ≤ X → X ≤ K ⊔ T →
        X = T ∨ X = L₁Of L (fsuV1 T V) ⊔ T ∨ X = H₂ ∨ X = K ⊔ T) ∧
      ¬ L₁Of L (fsuV1 T V) ⊔ T ≤ H₂ ∧ ¬ H₂ ≤ L₁Of L (fsuV1 T V) ⊔ T := by
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  obtain ⟨R⟩ := exists_rawData6 D.Wirr.2.2.1 hc
  obtain ⟨F⟩ := exists_frame5 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW D.isSylowTwoOf_inf
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
  obtain ⟨DP, hB⟩ := frame5_parData F D.T_le_K (D.inf_centralizer_le_T hZK)
    (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
    D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
  have hTB : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ T ⊓ K → F.ρ g ∈ a6D := fun g hg =>
    (mem_a6D_iff _).2 ⟨F.T_D g (mem_inf.1 hg).1,
      Perm.mem_alternatingGroup.1 ((F.image_L _).1 ⟨g, (mem_inf.1 hg).2, rfl⟩)⟩
  have hTY : ∀ t : ↥(normalizer (W : Set G)), (t : G) ∈ T → ∀ γ ∈ a6P2,
      F.ρ t * γ * (F.ρ t)⁻¹ ∈ a6P2 := fun t ht γ hγ =>
    a6P2_conj_D _ (F.T_D t ht) γ hγ
  obtain ⟨γ, hγ, β, hβ, hγβ⟩ := exists_a6P2_conj
  exact ⟨_, D.h2_of_parData hM hZV1 DP stab45_le_alt hTB hB
    (fun Y hY hYA => a6_overgroups hY hYA)
    (fun x hx => a6D_le_P2 x hx) a6P2_le_alt a6P2_not_le stab45_not_le_P2 hTY a6D_relIndex_P2
    hγ hβ hγβ⟩

end Data13410

end CFSG.Quasithin.H13.NQS134
