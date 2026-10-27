module

public import CFSG.Quasithin.H13.U3S13473B

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem inf_eq_of_relIndex_three {T P₁ P₂ : Subgroup G} (h₁ : T ≤ P₁) (h₂ : T ≤ P₂)
    (h3₁ : T.relIndex P₁ = 3) (h3₂ : T.relIndex P₂ = 3) (hne : ¬ P₂ ≤ P₁) : P₁ ⊓ P₂ = T := by
  have hm := relIndex_mul_relIndex T (P₁ ⊓ P₂) P₁ (le_inf h₁ h₂) inf_le_left
  rw [h3₁] at hm
  rcases (Nat.dvd_prime Nat.prime_three).1 (Dvd.intro _ hm) with h1 | h3
  · exact le_antisymm (relIndex_eq_one.1 h1) (le_inf h₁ h₂)
  · exfalso
    rw [h3] at hm
    have h1 : (P₁ ⊓ P₂).relIndex P₁ = 1 := by omega
    have hP : P₁ ≤ P₂ := (relIndex_eq_one.1 h1).trans inf_le_right
    have hm2 := relIndex_mul_relIndex T P₁ P₂ h₁ hP
    rw [h3₁, h3₂] at hm2
    exact hne (relIndex_eq_one.1 (by omega))

theorem s1347_Y_triple (hedge : GoldschmidtEdgeBoundS3) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {Y₂ : Subgroup G}
    (h3 : T.relIndex (Y₂ ⊔ T) = 3) (hq : quasithinO2QuotientIso (Y₂ ⊔ T) (Perm (Fin 3)))
    (hY₂M : ¬ Y₂ ≤ normalizer (L : Set G)) :
    (L₁Of L (fsuV1 T V) ⊔ T) ⊓ (Y₂ ⊔ T) = T ∧
      F6.IsGoldschmidtTripleIn ((L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T)) (L₁Of L (fsuV1 T V) ⊔ T)
        (Y₂ ⊔ T) ∧
      InH T ((L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T)) ∧
      ¬ (L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T) ≤ normalizer (L : Set G) := by
  obtain ⟨h3₁, -, hq₁⟩ := s134_L1T_a6 S he
  have hTK : T ≤ normalizer (L₁Of L (fsuV1 T V) : Set G) := s134_T_le_normalizer_L1 S
  have h31 : T.relIndex (L₁Of L (fsuV1 T V) ⊔ T) = 3 := by rw [relIndex_sup_eq hTK, h3₁]
  have hL1M : L₁Of L (fsuV1 T V) ⊔ T ≤ normalizer (L : Set G) :=
    sup_le (((oTwoRes_le _).trans inf_le_left).trans le_normalizer) S.T_le_NL
  have hinf : (L₁Of L (fsuV1 T V) ⊔ T) ⊓ (Y₂ ⊔ T) = T :=
    inf_eq_of_relIndex_three le_sup_right le_sup_right h31 h3 fun hle =>
      hY₂M ((le_sup_left.trans hle).trans hL1M)
  have hiso : ∀ {H : Subgroup G}, quasithinO2QuotientIso H (Perm (Fin 3)) →
      Nonempty (↥H ⧸ Open.pCore 2 ↥H ≃* Perm (Fin 3)) := fun hq => by
    obtain ⟨e⟩ := (quasithinO2QuotientIso_iff _ _).1 hq
    exact ⟨(QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open _ 2).symm).trans e⟩
  have htr : F6.IsGoldschmidtTripleIn ((L₁Of L (fsuV1 T V) ⊔ T) ⊔ (Y₂ ⊔ T))
      (L₁Of L (fsuV1 T V) ⊔ T) (Y₂ ⊔ T) := by
    refine ⟨rfl, hiso hq₁, hiso hq, ?_⟩
    rw [hinf]
    exact A5.isSylowTwoOf_of_le S.h13.sylow (le_sup_right.trans le_sup_left)
  exact ⟨hinf, htr, inH_of_triple hedge S htr hinf, fun hle =>
    hY₂M ((le_sup_left.trans le_sup_right).trans hle)⟩

theorem comm_mem_of_oTwoRes {L₁ Y₂ : Subgroup G} (h3 : (pCoreOf 2 L₁).relIndex L₁ = 3)
    (hY₂ : oTwoRes Y₂ = Y₂) (hN : Y₂ ≤ normalizer (L₁ : Set G)) :
    ∀ y ∈ Y₂, ∀ l ∈ L₁, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁ := by
  have hON : normalizer (L₁ : Set G) ≤ normalizer (pCoreOf 2 L₁ : Set G) :=
    normalizer_le_normalizer_pCoreOf 2 L₁
  let C : Subgroup G :=
    { carrier := {y | y ∈ normalizer (L₁ : Set G) ∧ ∀ l ∈ L₁, y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 L₁}
      one_mem' := ⟨one_mem _, fun l _ => by simp⟩
      mul_mem' := fun {a b} ha hb => by
        refine ⟨mul_mem ha.1 hb.1, fun l hl => ?_⟩
        have h1 := (mem_normalizer_iff.1 (hON ha.1) _).1 (hb.2 l hl)
        have e : a * b * l * (a * b)⁻¹ * l⁻¹ =
            a * (b * l * b⁻¹ * l⁻¹) * a⁻¹ * (a * l * a⁻¹ * l⁻¹) := by group
        rw [e]
        exact mul_mem h1 (ha.2 l hl)
      inv_mem' := fun {a} ha => by
        refine ⟨inv_mem ha.1, fun l hl => ?_⟩
        have hl' : a⁻¹ * l * a ∈ L₁ := by
          have := (mem_normalizer_iff.1 (inv_mem ha.1) l).1 hl
          simpa using this
        have h2 := inv_mem (ha.2 _ hl')
        have e : (a * (a⁻¹ * l * a) * a⁻¹ * (a⁻¹ * l * a)⁻¹)⁻¹ = a⁻¹ * l * a⁻¹⁻¹ * l⁻¹ := by
          group
        rwa [e] at h2 }
  have hle : oTwoRes Y₂ ≤ C := by
    refine (closure_le _).2 fun y hy => ?_
    obtain ⟨hyY, m, hm, hym⟩ := hy
    exact ⟨hN hyY, comm_mem_of_odd h3 (hN hyY) hm hym⟩
  rw [hY₂] at hle
  exact fun y hy => (hle hy).2

theorem s1347_iii_cyclic (S : A6.Setting134 G T L V) {H₁ H₂ : Subgroup G}
    (hH₀ : InH T (H₁ ⊔ H₂)) (hiii : Concl1347iii T H₁ H₂) {Y₂ : Subgroup G}
    (hY₂H : Y₂ ≤ H₁ ⊔ H₂) (hY₂T : Y₂ ⊓ T ≤ centralizer (v0Of T H₁ H₂ : Set G))
    (h3 : T.relIndex (Y₂ ⊔ T) = 3) (hTN : T ≤ normalizer (Y₂ : Set G)) :
    pCoreOf 2 Y₂ = ⊥ → IsCyclic ↥Y₂ := by
  intro hO
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hred := s1347_reduced S hH₀
  have hQT : pCoreOf 2 (H₁ ⊔ H₂) ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (A5.isSylowTwoOf_of_le S.h13.sylow hH₀.1)
  have hinf : Y₂ ⊓ T = Y₂ ⊓ centralizer (v0Of T H₁ H₂ : Set G) := by
    refine le_antisymm (le_inf inf_le_left hY₂T) fun y hy => ⟨hy.1, ?_⟩
    have h1 : y ∈ (H₁ ⊔ H₂) ⊓ centralizer (v0Of T H₁ H₂ : Set G) := ⟨hY₂H hy.1, hy.2⟩
    rw [← hiii.1] at h1
    exact hQT h1
  have hN : Y₂ ≤ normalizer ((Y₂ ⊓ T : Subgroup G) : Set G) := by
    rw [hinf]
    intro g hg
    exact mem_normalizer_inf_of (le_normalizer hg)
      (mem_normalizer_centralizer_of_mem (hred.2.1 (hY₂H hg)))
  have hbot : Y₂ ⊓ T = ⊥ := by
    rw [eq_bot_iff, ← hO]
    exact le_pCoreOf_of_le_normalizer 2 inf_le_left hN (S.h13.sylow.1.to_le inf_le_right)
  have hcard : Nat.card ↥Y₂ = 3 := by
    rw [← h3, relIndex_sup_eq hTN, hbot, relIndex_bot_left]
  exact isCyclic_of_prime_card hcard

theorem e45_ne : e45 ≠ 1 ∧ e45 ≠ G6.allOnes 6 := by decide

theorem s134_e45_not_mem_centralizer (S : A6.Setting134 G T L V) :
    ((S.frame.ψ.symm ⟨e45, e45_mem⟩ : ↥V) : G) ∉ centralizer (L : Set G) := by
  intro hv
  rcases (S.mem_centralizer_L_iff _).1 hv with h1 | h1
  · have h2 := congrArg (fun x => (S.frame.ψ x : P6)) h1
    simp only [MulEquiv.apply_symm_apply, map_one, OneMemClass.coe_one] at h2
    exact e45_ne.1 h2
  · have h2 := congrArg (fun x => (S.frame.ψ x : P6)) h1
    simp only [MulEquiv.apply_symm_apply, S.psi_zV] at h2
    exact e45_ne.2 h2

theorem s1347_Y_cent (h139 : A6.Stmt13_3_9) (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {Y Y₂ : Subgroup G}
    (hY : InH T Y) (hYM : ¬ Y ≤ normalizer (L : Set G)) (hY₂Y : Y₂ ≤ Y)
    (hY₂ : oTwoRes Y₂ = Y₂)
    (hnc : ¬ ∀ y ∈ Y₂, ∀ l ∈ L₁Of L (fsuV1 T V),
      y * l * y⁻¹ * l⁻¹ ∈ pCoreOf 2 (L₁Of L (fsuV1 T V))) :
    IsTwoReducedIn Y (VZ T Y) ∧ Y ⊓ centralizer (VZ T Y : Set G) = pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hred : IsTwoReducedIn Y (VZ T Y) :=
    C1GN.isTwoReducedIn_VZ (s134_charTwo_of_inH S hY) (A5.isSylowTwoOf_of_le S.h13.sylow hY.1)
  refine ⟨hred, le_antisymm ?_ (le_inf (pCoreOf_le 2 Y) (pCoreOf_le_centralizer_of_reduced' hred))⟩
  have hCN : Y ≤ normalizer ((Y ⊓ centralizer (VZ T Y : Set G) : Subgroup G) : Set G) :=
    fun g hg =>
      mem_normalizer_inf_of (le_normalizer hg) (mem_normalizer_centralizer_of_mem (hred.2.1 hg))
  have hYN : Y ≤ normalizer (oTwoRes (Y ⊓ centralizer (VZ T Y : Set G)) : Set G) :=
    hCN.trans (normalizer_le_normalizer_oTwoRes _)
  have hvV1 := s134_e45_mem_V1 S
  have hZY : quasithinOmegaOneCenter T ≤ VZ T Y := le_conjClosure _ _
  have hZV : V ⊓ centralizer (L : Set G) ≤ VZ T Y := by
    rw [S.ZV_eq_zpowers, zpowers_le]
    refine hZY (subset_closure
      ⟨⟨S.V_le_T S.zV_mem_V, mem_centralizer_iff.2 fun t ht => ?_⟩, S.zV_sq⟩)
    have h1 := S.conj_zV ⟨t, S.frame.T_le ht⟩
    calc t * S.zV = t * S.zV * t⁻¹ * t := by group
      _ = S.zV * t := by rw [h1]
  have hCle : oTwoRes (Y ⊓ centralizer (VZ T Y : Set G)) ≤ normalizer (L : Set G) ⊓
      centralizer ({((S.frame.ψ.symm ⟨e45, e45_mem⟩ : ↥V) : G)} : Set G) := by
    refine (oTwoRes_le _).trans (inf_le_right.trans (le_inf ?_ ?_))
    · exact (centralizer_le (SetLike.coe_subset_coe.2 hZV)).trans S.centralizer_ZV_le
    · exact centralizer_le (Set.singleton_subset_iff.2 (hZY (mem_inf.1 hvV1).2))
  rcases h139 G T L V Y _ _ S.h13 S.irr (s134_isA6On S) hY hYM (S14.oTwoRes_idem _)
      ((oTwoRes_le _).trans inf_le_left) hYN hvV1 (s134_e45_not_mem_centralizer S) hCle with
    hbot | ⟨-, hL1, -⟩
  · exact le_pCoreOf_of_le_normalizer 2 inf_le_left hCN (isPGroup_of_oTwoRes_eq_bot hbot)
  · exfalso
    obtain ⟨h3, hO, -⟩ := s134_L1T_a6 S he
    have hYL : Y₂ ≤ normalizer (L₁Of L (fsuV1 T V) : Set G) := by
      have := hY₂Y.trans hYN
      rwa [hL1 he] at this
    exact hnc (comm_mem_of_oTwoRes (by rw [← hO]; exact h3) hY₂ hYL)

end CFSG.Quasithin.H13.U3
