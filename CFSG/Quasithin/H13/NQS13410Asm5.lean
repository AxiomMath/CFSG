module

public import CFSG.Quasithin.H13.NQS13410Asm4

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.Quasithin.InternalSec
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem not_lieModel_of_a6 {K : Subgroup G}
    (hK6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6))) :
    ¬ LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1 := fun h3 => by
  obtain ⟨-, c3, c6, -⟩ := card_quot_of_type K
  have h1 := c3 h3
  have h2 := c6 hK6
  omega

namespace Data13410

variable {S : A6.Setting134 G T L V} {z : G} {H K W : Subgroup G} [IsMulCommutative ↥W]
  (D : Data13410 S z H K W)
include D

theorem seven_l32 (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (h56 : AsB56)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hM : normalizer (L : Set G) = L ⊔ T) (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hcZ : U3.cZ T K = zpowers z) (hK3 : LieModel (↥K ⧸ CFSG.pCore 2 ↥K) .PSL 3 2 1)
    (hnat : BinaryNaturalSL (V := ↥W) (autOn K W) ⊤ ⊥ 3 1) :
    H = K ⊔ T ∧ H = centralizer ({z} : Set G) ∧
      (∀ H' : Subgroup G, U3.InHz T L V z H' → H' = centralizer ({z} : Set G)) ∧
      conjClosure (quasithinOmegaOneCenter T) K = conjClosure (quasithinOmegaOneCenter T) H ∧
      (∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ H ∧
        ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ H → X = H₂) := by
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  have htop := autOn_eq_top_of_l32 hnat
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
  exact D.seven_of hC137 h1332 h1228 h56 he hM hZV1 hL1Z hL1 hZW hcZ (Or.inl hK3)
    (fun _ => hnat) (fun _ _ hXW _ hh => exists_mem_sup_of_l32 htop (hXW hh)) DP le_top
    (fun _ hY _ => l3Stab_max (by decide +kernel) hY) hB le_top l3P2_not_le
    (fun _ hBY _ hYP => l3P2_le_of hBY hYP)

theorem seven_nat (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (h56 : AsB56)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hM : normalizer (L : Set G) = L ⊔ T) (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hcZ : U3.cZ T K = zpowers z)
    (hK6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (h6 : AlternatingNatural (V := ↥W) (autOn K W) ⊤ ⊥ 6) :
    H = K ⊔ T ∧ H = centralizer ({z} : Set G) ∧
      (∀ H' : Subgroup G, U3.InHz T L V z H' → H' = centralizer ({z} : Set G)) ∧
      conjClosure (quasithinOmegaOneCenter T) K = conjClosure (quasithinOmegaOneCenter T) H ∧
      (∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ H ∧
        ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ H → X = H₂) := by
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  obtain ⟨R⟩ := exists_rawData4 D.Wirr.2.2.1 h6
  obtain ⟨F⟩ := exists_frame4 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW D.isSylowTwoOf_inf
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
  obtain ⟨DP, hB⟩ := frame4_parData F D.T_le_K (D.inf_centralizer_le_T hZK)
    (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
    D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
  exact D.seven_of hC137 h1332 h1228 h56 he hM hZV1 hL1Z hL1 hZW hcZ (Or.inr hK6)
    (fun h3 => absurd h3 (not_lieModel_of_a6 hK6))
    (fun _ hTX hXW _ hh => exists_mem_sup_of_perm hXW (A5.isSylowTwoOf_of_le S.h13.sylow hTX)
      F.ρ (frame4_ker F) (fun σ hσ => (F.image_L σ).2 hσ) hh)
    DP stab45_le_alt (fun _ hY hYA => stab45_max hY hYA) hB a6P2_le_alt a6P2_not_le
    (fun _ hBY hYA hYP => a6P2_le_of hYA hBY hYP)

theorem seven_core (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (h56 : AsB56)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hM : normalizer (L : Set G) = L ⊔ T) (hZV1 : quasithinOmegaOneCenter T = fsuV1 T V)
    (hL1Z : L₁Of L (fsuV1 T V) ≤ centralizer (quasithinOmegaOneCenter T : Set G))
    (hL1 : L₁Of L (fsuV1 T V) ≤ K) (hZW : quasithinOmegaOneCenter T ≤ W ⊔ U3.cZ T K)
    (hcZ : U3.cZ T K = zpowers z)
    (hK6 : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 6)))
    (hc : FFModel.Realizes (V := ↥W) (altCoreModel 6) (autOn K W) ⊤ ⊥) :
    H = K ⊔ T ∧ H = centralizer ({z} : Set G) ∧
      (∀ H' : Subgroup G, U3.InHz T L V z H' → H' = centralizer ({z} : Set G)) ∧
      conjClosure (quasithinOmegaOneCenter T) K = conjClosure (quasithinOmegaOneCenter T) H ∧
      (∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ H ∧
        ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ H → X = H₂) := by
  have hTZ : T ≤ centralizer (quasithinOmegaOneCenter T : Set G) :=
    le_centralizer_iff.mp ((U3.s134_Z_le_center T).trans inf_le_right)
  obtain ⟨R⟩ := exists_rawData6 D.Wirr.2.2.1 hc
  obtain ⟨F⟩ := exists_frame5 R (D.normalizer_W_le h1332) S.h13.sylow.1 D.TW D.isSylowTwoOf_inf
  have hZK := center_eq_bot_of_simple_types (Or.inr (Or.inr hK6))
  obtain ⟨DP, hB⟩ := frame5_parData F D.T_le_K (D.inf_centralizer_le_T hZK)
    (sup_le_sup_right hL1 T) (centralizer_Z_le_L1T S hM hZV1) (sup_le hL1Z hTZ)
    D.mem_Z_of_mem_centralizer_T (D.mem_centralizer_Z_of_fix hZW)
  exact D.seven_of hC137 h1332 h1228 h56 he hM hZV1 hL1Z hL1 hZW hcZ (Or.inr hK6)
    (fun h3 => absurd h3 (not_lieModel_of_a6 hK6))
    (fun _ hTX hXW _ hh => exists_mem_sup_of_perm hXW (A5.isSylowTwoOf_of_le S.h13.sylow hTX)
      F.ρ (frame5_ker F) (fun σ hσ => (F.image_L σ).2 hσ) hh)
    DP stab45_le_alt (fun _ hY hYA => stab45_max hY hYA) hB a6P2_le_alt a6P2_not_le
    (fun _ hBY hYA hYP => a6P2_le_of hYA hBY hYP)

theorem seven (hC137 : U3.C137StatementFiveZ)
    (h1332 : Stmt13_3_2) (h1228 : Stmt12_2_8) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6)))
    (hnhat : ¬ A6.IsHatA6 L) :
    normalizer (L : Set G) = L ⊔ T ∧ H = K ⊔ T ∧ H = centralizer ({z} : Set G) ∧
      (∀ H' : Subgroup G, U3.InHz T L V z H' → H' = centralizer ({z} : Set G)) ∧
      conjClosure (quasithinOmegaOneCenter T) K = conjClosure (quasithinOmegaOneCenter T) H ∧
      (∃ H₂ : Subgroup G, IsHStar T (normalizer (L : Set G)) H₂ ∧ H₂ ≤ H ∧
        ∀ X : Subgroup G, IsHStar T (normalizer (L : Set G)) X → X ≤ H → X = H₂) := by
  have hM : normalizer (L : Set G) = L ⊔ T := D.M4.resolve_right hnhat
  obtain ⟨-, hZW, hL1, hcZ, htype⟩ := (D.main_of_a6 hC137 h1332 h1228 hC58 h317 h56 he).2
  obtain ⟨-, -, -, -, -, -, hZV1, -⟩ := D.one_six hC137 h1332 h1228 hC58 h317 h56 he
  have hL1Z := U3.s134_L1_le_centralizer_Z h1332 hC58 h317 h56 S D.exists_inH
  refine ⟨hM, ?_⟩
  rcases htype with ⟨hK3, hnat⟩ | ⟨hK6, h6 | hc⟩
  · exact D.seven_l32 hC137 h1332 h1228 h56 he hM hZV1 hL1Z hL1 hZW hcZ hK3 hnat
  · exact D.seven_nat hC137 h1332 h1228 h56 he hM hZV1 hL1Z hL1 hZW hcZ hK6 h6.1
  · exact D.seven_core hC137 h1332 h1228 h56 he hM hZV1 hL1Z hL1 hZW hcZ hK6 hc.2.2

end Data13410

end CFSG.Quasithin.H13.NQS134
