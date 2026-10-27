module

public import CFSG.Quasithin.H13.NQS13412C
public import CFSG.Quasithin.H13.NQS134108B
public import CFSG.Quasithin.H13.NQS13410Asm5
public import CFSG.Quasithin.H13.NQS13411
public import CFSG.Quasithin.H13.NQS13412B

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem frame4_ker_iff {K W : Subgroup G} (F : Frame4 T K W) (g : ↥(normalizer (W : Set G))) :
    F.ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G) := by
  refine ⟨frame4_ker F g, fun h => act4f_faithful _ fun x hx => ?_⟩
  set w : ↥W := F.ψ.symm ⟨x, hx⟩ with hw
  have h1 := F.equiv g w
  have h2 : conjAct W g w = w := Subtype.ext (by
    rw [A5.conjAct_val, ← mem_centralizer_iff.mp h w w.2, mul_inv_cancel_right])
  rw [h2, hw, MulEquiv.apply_symm_apply] at h1
  have h3 := congrArg Subtype.val h1
  rw [act4_coe] at h3
  exact h3.symm

omit [Finite G] in
theorem frame5_ker_iff {K W : Subgroup G} (F : Frame5 T K W) (g : ↥(normalizer (W : Set G))) :
    F.ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G) := by
  refine ⟨frame5_ker F g, fun h => permAct_core_faithful _ fun x hx => ?_⟩
  set w : ↥W := F.ψ.symm ⟨x, G6.mem_coreMod.2 hx⟩ with hw
  have h1 := F.equiv g w
  have h2 : conjAct W g w = w := Subtype.ext (by
    rw [A5.conjAct_val, ← mem_centralizer_iff.mp h w w.2, mul_inv_cancel_right])
  rw [h2, hw, MulEquiv.apply_symm_apply] at h1
  have h3 := congrArg Subtype.val h1
  rw [G6.coreAct_coe] at h3
  exact h3.symm

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem chief_data {H₂ : Subgroup G} (hH₂KT : H₂ ≤ K ⊔ T) (hTH₂ : T ≤ H₂)
    (hZK : center (↥K ⧸ CFSG.pCore 2 ↥K) = ⊥) :
    oTwoRes H₂ ≤ K ∧ W ≤ normalizer (oTwoRes H₂ : Set G) ∧
      IsPGroup 2 ↥(K ⊓ centralizer (W : Set G)) := by
  refine ⟨(U3.oTwoRes_mono' hH₂KT).trans (oTwoRes_sup_eq_of_faithful D.Kf D.T_le_K).le,
    (D.W_le_T.trans hTH₂).trans (le_normalizer_oTwoRes _), ?_⟩
  rw [← D.o2Z]
  exact (LieType.BorelTits.pCoreOf_isPGroup 2 K).to_le (o2Z_le_pCoreOf_of_center hZK)

theorem chief_h2_l32 (hM : normalizer (L : Set G) = L ⊔ T)
    (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1) {H₂ : Subgroup G}
    (hstar : IsHStar T (normalizer (L : Set G)) H₂) (hH₂KT : H₂ ≤ K ⊔ T) :
    HasTwoNoncentralChiefFactors (oTwoRes H₂) := by
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
      have h1 : (t : G) * s * (t : G)⁻¹ ∈ T :=
        mul_mem (mul_mem ht (mem_inf.1 hs).1) (inv_mem ht)
      have h2 : (t : G) * s * (t : G)⁻¹ ∈ K :=
        (mem_normalizer_iff.mp (D.T_le_K ht) s).mp (mem_inf.1 hs).2
      have := hCB (t * s * t⁻¹) (mem_inf.2 ⟨h1, h2⟩)
      rwa [map_mul, map_mul, map_inv] at this
    have htP : C.ρ t ∈ l3P2 := l3B_le_P2 _ htB
    exact mul_mem (mul_mem htP hγ) (inv_mem htP)
  obtain ⟨g, hg, b, hb, hgb⟩ := exists_l3P2_conj
  obtain ⟨-, -, huniq, -⟩ := D.h2_of_parData hM hZV1 DP le_top hCB hB
    (fun Y hY _ => l3_overgroups hY) (fun x hx => l3B_le_P2 x hx) le_top l3P2_not_le
    l3Stab_not_le_P2 hTY l3B_relIndex_P2 (mem_l3P2.2 hg) hb hgb
  rw [huniq H₂ hstar hH₂KT]
  obtain ⟨hXK, hWX, hKC⟩ := D.chief_data (DP.parOf_le_sup l3P2) (DP.T_le_parOf l3P2) hZK
  have hρP : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ oTwoRes (DP.parOf l3P2) →
      C.ρ g ∈ l3P2 := fun g hg =>
    DP.img'_parOf_le D.TW hCB (fun x hx => l3B_le_P2 x hx) hTY
      (DP.mem_img' (mem_inf.2 ⟨oTwoRes_le _ hg, hXK hg⟩))
  have hlift : ∀ c ∈ l3P2, c ^ 3 = 1 → ∃ k ∈ oTwoRes (DP.parOf l3P2),
      (∃ m : ℕ, Odd m ∧ k ^ m = 1) ∧ ∀ hk : k ∈ normalizer (W : Set G), C.ρ ⟨k, hk⟩ = c := by
    intro c hc hc3
    obtain ⟨g, hgK, hgρ⟩ := DP.img c (mem_top c)
    obtain ⟨y, hyodd, hyρ, j, hyj⟩ := exists_odd_part C.ρ g (by rw [hgρ]; exact hc3)
    have hyK : (y : G) ∈ K := by rw [hyj]; exact pow_mem hgK j
    have hyH : (y : G) ∈ DP.parOf l3P2 := DP.mem_parOf hyK (by rw [hyρ, hgρ]; exact hc)
    exact ⟨y, subset_closure ⟨hyH, hyodd⟩, hyodd, fun _ => by rw [← hgρ, ← hyρ]⟩
  obtain ⟨hc1P, hc2P, hc13, hc23, he1, he2, hnc⟩ := l3c_facts
  obtain ⟨k₁, hk₁, ⟨m₁, hm₁, hk₁m⟩, hk₁ρ⟩ := hlift l3c1 (mem_l3P2.2 hc1P) hc13
  obtain ⟨k₂, hk₂, -, hk₂ρ⟩ := hlift l3c2 (mem_l3P2.2 hc2P) hc23
  have hEmem : ∀ e : L3.Γ, e ∈ l3E4 ↔ L3.act e l3e1 = l3e1 ∧ L3.act e l3e2 = l3e2 := fun e =>
    Iff.rfl
  refine chief_of_action C.ρ (P := l3P2) (E := l3E4) hXK D.Wirr.2.2.1 hWX
    (fun w hw => D.sq_eq_one hw) hKC C.ker hρP (fun γ hγ e he => ?_) (fun e he => ?_) hk₁ hk₂
    hm₁ hk₁m ?_ ?_
  · obtain ⟨h1, h2⟩ := (hEmem e).1 he
    exact (hEmem _).2 (l3E4_normal γ (mem_l3P2.1 hγ) e (l3E4_le_B e h1 h2) h2)
  · obtain ⟨h1, h2⟩ := (hEmem e).1 he
    exact l3E4_sq e (l3E4_le_B e h1 h2) h2
  · rw [hk₁ρ, hk₂ρ]
    exact (hEmem _).2 ⟨he1, he2⟩
  · rw [hk₁ρ, hk₂ρ]
    exact hnc

theorem chief_h2_of_frame (hM : normalizer (L : Set G) = L ⊔ T)
    (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hK6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (ρ : ↥(normalizer (W : Set G)) →* Perm (Fin 6))
    (hρker : ∀ g : ↥(normalizer (W : Set G)), ρ g = 1 ↔ (g : G) ∈ centralizer (W : Set G))
    (hTD : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ T → InD6 (ρ g))
    (DP : ParData K T W (L₁Of L (fsuV1 T V) ⊔ T) ρ (alternatingGroup (Fin 6)) stab45)
    (hB : ∀ β ∈ a6D, ∃ g : ↥(normalizer (W : Set G)), (g : G) ∈ T ⊓ K ∧ ρ g = β)
    {H₂ : Subgroup G} (hstar : IsHStar T (normalizer (L : Set G)) H₂) (hH₂KT : H₂ ≤ K ⊔ T) :
    HasTwoNoncentralChiefFactors (oTwoRes H₂) := by
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
  have hTB : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ T ⊓ K → ρ g ∈ a6D := fun g hg =>
    (mem_a6D_iff _).2 ⟨hTD g (mem_inf.1 hg).1,
      Perm.mem_alternatingGroup.1 (DP.img_le g (mem_inf.1 hg).2)⟩
  have hTY : ∀ t : ↥(normalizer (W : Set G)), (t : G) ∈ T → ∀ γ ∈ a6P2,
      ρ t * γ * (ρ t)⁻¹ ∈ a6P2 := fun t ht γ hγ => a6P2_conj_D _ (hTD t ht) γ hγ
  obtain ⟨γ, hγ, β, hβ, hγβ⟩ := exists_a6P2_conj
  obtain ⟨-, -, huniq, -⟩ := D.h2_of_parData hM hZV1 DP stab45_le_alt hTB hB
    (fun Y hY hYA => a6_overgroups hY hYA) (fun x hx => a6D_le_P2 x hx) a6P2_le_alt a6P2_not_le
    stab45_not_le_P2 hTY a6D_relIndex_P2 hγ hβ hγβ
  rw [huniq H₂ hstar hH₂KT]
  obtain ⟨hXK, hWX, hKC⟩ := D.chief_data (DP.parOf_le_sup a6P2) (DP.T_le_parOf a6P2) hZK
  have hρP : ∀ g : ↥(normalizer (W : Set G)), (g : G) ∈ oTwoRes (DP.parOf a6P2) →
      ρ g ∈ a6P2 := fun g hg =>
    DP.img'_parOf_le D.TW hTB (fun x hx => a6D_le_P2 x hx) hTY
      (DP.mem_img' (mem_inf.2 ⟨oTwoRes_le _ hg, hXK hg⟩))
  have hlift : ∀ c ∈ a6P2, c ^ 3 = 1 → ∃ k ∈ oTwoRes (DP.parOf a6P2),
      (∃ m : ℕ, Odd m ∧ k ^ m = 1) ∧ ∀ hk : k ∈ normalizer (W : Set G), ρ ⟨k, hk⟩ = c := by
    intro c hc hc3
    obtain ⟨g, hgK, hgρ⟩ := DP.img c (a6P2_le_alt hc)
    obtain ⟨y, hyodd, hyρ, j, hyj⟩ := exists_odd_part ρ g (by rw [hgρ]; exact hc3)
    have hyK : (y : G) ∈ K := by rw [hyj]; exact pow_mem hgK j
    have hyH : (y : G) ∈ DP.parOf a6P2 := DP.mem_parOf hyK (by rw [hyρ, hgρ]; exact hc)
    exact ⟨y, subset_closure ⟨hyH, hyodd⟩, hyodd, fun _ => by rw [← hgρ, ← hyρ]⟩
  obtain ⟨hc1P, hc2P⟩ := a6c_mem
  obtain ⟨hc13, hc23⟩ := a6c_cube
  obtain ⟨k₁, hk₁, ⟨m₁, hm₁, hk₁m⟩, hk₁ρ⟩ := hlift a6c1 (mem_a6P2.2 hc1P) hc13
  obtain ⟨k₂, hk₂, -, hk₂ρ⟩ := hlift a6c2 (mem_a6P2.2 hc2P) hc23
  refine chief_of_action ρ (P := a6P2) (E := a6E4) hXK D.Wirr.2.2.1 hWX
    (fun w hw => D.sq_eq_one hw) hKC hρker hρP (fun γ hγ e he => a6E4_normal γ hγ e he)
    (fun e he => a6E4_sq e he) hk₁ hk₂ hm₁ hk₁m ?_ ?_
  · rw [hk₁ρ, hk₂ρ]
    exact a6c_comm
  · rw [hk₁ρ, hk₂ρ]
    exact a6c_nc

theorem chief_h2 (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) {H₂ : Subgroup G} (hstar : IsHStar T (normalizer (L : Set G)) H₂)
    (hH₂H : H₂ ≤ H) : HasTwoNoncentralChiefFactors (oTwoRes H₂) := by
  have hM : normalizer (L : Set G) = L ⊔ T := D.M4.resolve_right hnhat
  obtain ⟨-, hZW, hL1, -, htype⟩ := (D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he).2
  obtain ⟨-, -, -, -, -, -, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  obtain ⟨-, hHKT, -, -⟩ := D.seven hC137 h1332 h1228 hC58 h317 h56 he hnhat
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S D.exists_inH
  have hH₂KT : H₂ ≤ K ⊔ T := hH₂H.trans hHKT.le
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  rcases htype with ⟨hK3, hnat⟩ | ⟨hK6, h6 | hc⟩
  · exact D.chief_h2_l32 hM hZV1 hL1Z hL1 hZW hK3 hnat hstar hH₂KT
  · obtain ⟨R⟩ := exists_rawData4 D.Wirr.2.2.1 h6.1
    obtain ⟨F⟩ := exists_frame4 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW
      D.isSylowTwoOf_inf
    have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
    obtain ⟨DP, hB⟩ := frame4_parData F D.T_le_K (D.inf_centralizer_le_T hZK)
      (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
      D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
    exact D.chief_h2_of_frame hM hZV1 hK6 F.ρ (frame4_ker_iff F) F.T_D DP hB hstar hH₂KT
  · obtain ⟨R⟩ := exists_rawData6 D.Wirr.2.2.1 hc.2.2
    obtain ⟨F⟩ := exists_frame5 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW
      D.isSylowTwoOf_inf
    have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
    obtain ⟨DP, hB⟩ := frame5_parData F D.T_le_K (D.inf_centralizer_le_T hZK)
      (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
      D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
    exact D.chief_h2_of_frame hM hZV1 hK6 F.ρ (frame5_ker_iff F) F.T_D DP hB hstar hH₂KT

end Data13410

end CFSG.Quasithin.H13.NQS134
