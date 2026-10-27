module

public import CFSG.Quasithin.Recognition.GoldschmidtBasic
public import CFSG.Quasithin.H13.L32A74
public import CFSG.Quasithin.H13.L32NSet14Gen

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

private theorem relIndex_ne_zero_fin (H K : Subgroup G) : H.relIndex K ≠ 0 := by
  intro h0
  have := Subgroup.relIndex_mul_card H K
  rw [h0, zero_mul] at this
  exact (Nat.card_pos (α := ↥K)).ne this

theorem nonempty_quotient_perm_three {A S : Subgroup G} (hSA : S ≤ A) (hS2 : IsPGroup 2 ↥S)
    (h3 : S.relIndex A = 3) (hn : ¬ A ≤ Subgroup.normalizer (S : Set G)) :
    Nonempty (↥A ⧸ CFSG.Open.pCore 2 ↥A ≃* Equiv.Perm (Fin 3)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H := S.subgroupOf A with hH
  have hH3 : H.index = 3 := h3
  have hH2 : IsPGroup 2 ↥H := hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSA).symm
  have hnc : (CFSG.Open.pCore 2 ↥A).Normal := inferInstance
  have hcore : H.normalCore = CFSG.Open.pCore 2 ↥A := by
    refine le_antisymm (le_pCore 2 H.normalCore_normal (hH2.to_le H.normalCore_le)) ?_
    have hsyl : CFSG.Open.pCore 2 ↥A ≤ H :=
      (CFSG.LieType.BorelTits.pCore_isPGroup (G := ↥A) 2).le_sylow_of_normal
        (hH2.toSylow (by rw [hH3]; decide))
    exact Subgroup.normal_le_normalCore.mpr hsyl
  rcases CFSG.Quasithin.gold_normalCore_quotient_equiv hH3 with ⟨hi, -⟩ | ⟨-, ⟨e⟩⟩
  · exfalso
    apply hn
    have hle : H ≤ H.normalCore := by
      have hmul := Subgroup.relIndex_mul_index H.normalCore_le
      rw [hH3, hi] at hmul
      exact Subgroup.relIndex_eq_one.mp (by omega)
    have hconj : ∀ a ∈ A, ∀ s ∈ S, a * s * a⁻¹ ∈ S := by
      intro a ha s hs
      have hsH : (⟨s, hSA hs⟩ : ↥A) ∈ H := Subgroup.mem_subgroupOf.mpr hs
      have := H.normalCore_le (H.normalCore_normal.conj_mem _ (hle hsH) ⟨a, ha⟩)
      rw [hH, Subgroup.mem_subgroupOf] at this
      simpa using this
    intro a ha
    rw [Subgroup.mem_normalizer_iff]
    intro s
    refine ⟨hconj a ha s, fun hs => ?_⟩
    have := hconj a⁻¹ (inv_mem ha) _ hs
    simpa [mul_assoc] using this
  · exact ⟨(QuotientGroup.quotientMulEquivOfEq hcore.symm).trans e⟩

theorem four_le_relIndex_pCoreOf (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    4 ≤ (Subgroup.centralizer (V : Set G)).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  set P := pCoreOf 2 (L₁Of L (fsuV1 T V)) with hP
  set C := Subgroup.centralizer (V : Set G) with hC
  obtain ⟨n, hn⟩ := (pCoreOf_isPGroup 2 (L₁Of L (fsuV1 T V))).exists_card_eq
  have hdvd : C.relIndex P ∣ 2 ^ n := by
    rw [← hn]
    exact Dvd.intro _ (Subgroup.relIndex_mul_card C P)
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  have hPL : P ≤ L₁Of L (fsuV1 T V) := pCoreOf_le 2 _
  have hPH : P ≤ hz T V := hPL.trans (le_sup_left.trans hF.L₁T_le_H)
  have hPN : P ≤ Subgroup.normalizer (V : Set G) :=
    hPL.trans (le_sup_left.trans hF.L₁T_normalizes_Vp)
  have hPC : ¬ P ≤ C := by
    intro hle
    have hc := S14.comm3
    have hb : ⁅V, P⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv p hp
      rw [Subgroup.mem_bot, commutatorElement_def,
        show v * p = p * v from Subgroup.mem_centralizer_iff.mp (hle hp) v hv,
        mul_inv_cancel_right, mul_inv_cancel]
    rw [hb] at hc
    have := hF.card_V₁
    rw [← hc, Subgroup.card_bot] at this
    omega
  rcases j with _ | _ | j
  · exact absurd (Subgroup.relIndex_eq_one.mp (by simpa using hj)) hPC
  · exfalso
    have h2' : C.relIndex P = 2 := by simpa using hj
    have h2 : (C.subgroupOf P).index = 2 := h2'
    obtain ⟨r, hrP, hrC⟩ := Set.not_subset.mp hPC
    obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
    have hzV₂ : z ∈ V₂ := hV2.1 hz0
    have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
    have haV' : a ∈ V := hV2.2.1 ha
    obtain ⟨x, hxL0, hx3, hxz, hxa, hxb⟩ := S14.exists_rot hzV haV' hb
      (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
      (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
      (fun h => hbV (h ▸ mul_mem hzV₂ ha))
    have hxL1 : x ∈ L₁Of L (fsuV1 T V) :=
      Subgroup.subset_closure ⟨⟨hxL0, S14.mem_g1 hz0 hz1 hxz⟩, 3, by decide, hx3⟩
    have hxP : x ∈ Subgroup.normalizer (P : Set G) := le_normalizer_pCoreOf 2 _ hxL1
    have hxV : x ∈ Subgroup.normalizer (V : Set G) :=
      hF.L₁T_normalizes_Vp (Subgroup.mem_sup_left hxL1)
    have hxH : x ∈ hz T V := hF.L₁T_le_H (Subgroup.mem_sup_left hxL1)
    have hxc : ∀ c ∈ fsuV1 T V, x * c * x⁻¹ = c := by
      intro c hc
      rw [← Subgroup.mem_centralizer_iff.mp hxH c hc, mul_inv_cancel_right]
    have hkey : ∀ y ∈ Subgroup.normalizer (P : Set G), y ∈ Subgroup.normalizer (V : Set G) →
        y * r * y⁻¹ * r⁻¹ ∈ C := by
      intro y hyP hyV
      have hyr : y * r * y⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hyP r).mp hrP
      have hyrC : y * r * y⁻¹ ∉ C := by
        intro hc
        apply hrC
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at *
        intro v hv
        have hv' : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV v).mp hv
        have e := hc _ hv'
        calc v * r = y⁻¹ * ((y * v * y⁻¹) * (y * r * y⁻¹)) * y := by group
          _ = y⁻¹ * ((y * r * y⁻¹) * (y * v * y⁻¹)) * y := by rw [e]
          _ = r * v := by group
      have hm := (Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨y * r * y⁻¹, hyr⟩)
        (b := (⟨r, hrP⟩ : ↥P)⁻¹)).mpr (iff_of_false
          (fun h' => hyrC (Subgroup.mem_subgroupOf.mp h'))
          (fun h' => hrC (by simpa using inv_mem (Subgroup.mem_subgroupOf.mp h'))))
      rw [Subgroup.mem_subgroupOf] at hm
      simpa [mul_assoc] using hm
    have hrV : ∀ v ∈ V, r * v * r⁻¹ ∈ V := fun v hv =>
      (Subgroup.mem_normalizer_iff.mp (hPN hrP) v).mp hv
    have hφV1 : ∀ v ∈ V, r * v * r⁻¹ * v⁻¹ ∈ fsuV1 T V := by
      intro v hv
      have hm := Subgroup.commutator_mem_commutator hv hrP
      rw [S14.comm3] at hm
      have := inv_mem hm
      rwa [commutatorElement_def, show (v * r * v⁻¹ * r⁻¹)⁻¹ = r * v * r⁻¹ * v⁻¹ by group]
        at this
    have hrx : ∀ v ∈ V, r * (x * v * x⁻¹) * r⁻¹ = x * (r * v * r⁻¹) * x⁻¹ := by
      intro v hv
      have hc := hkey x⁻¹ (inv_mem hxP) (inv_mem hxV)
      rw [inv_inv] at hc
      have e := Subgroup.mem_centralizer_iff.mp hc (r * v * r⁻¹) (hrV v hv)
      calc r * (x * v * x⁻¹) * r⁻¹ = x * ((x⁻¹ * r * x * r⁻¹) * (r * v * r⁻¹) *
            (x⁻¹ * r * x * r⁻¹)⁻¹) * x⁻¹ := by group
        _ = x * ((r * v * r⁻¹) * (x⁻¹ * r * x * r⁻¹) * (x⁻¹ * r * x * r⁻¹)⁻¹) * x⁻¹ := by
          rw [← e]
        _ = x * (r * v * r⁻¹) * x⁻¹ := by group
    have hφx : ∀ v ∈ V, r * (x * v * x⁻¹) * r⁻¹ * (x * v * x⁻¹)⁻¹ = r * v * r⁻¹ * v⁻¹ := by
      intro v hv
      calc r * (x * v * x⁻¹) * r⁻¹ * (x * v * x⁻¹)⁻¹ =
          x * (r * v * r⁻¹) * x⁻¹ * (x * v * x⁻¹)⁻¹ := by rw [hrx v hv]
        _ = x * (r * v * r⁻¹ * v⁻¹) * x⁻¹ := by group
        _ = r * v * r⁻¹ * v⁻¹ := hxc _ (hφV1 v hv)
    have hbV' : b ∈ V := hb
    have hφb : r * b * r⁻¹ * b⁻¹ = r * a * r⁻¹ * a⁻¹ := by
      rw [← hxa]
      exact hφx a haV'
    have hφab : r * (a * b) * r⁻¹ * (a * b)⁻¹ = r * b * r⁻¹ * b⁻¹ := by
      rw [← hxb]
      exact hφx b hbV'
    have hmul : r * (a * b) * r⁻¹ * (a * b)⁻¹ =
        (r * a * r⁻¹ * a⁻¹) * (r * b * r⁻¹ * b⁻¹) := by
      have hc := S14.comm_V (Subgroup.mem_inf.mp (hφV1 b hbV')).1 (inv_mem haV')
      calc r * (a * b) * r⁻¹ * (a * b)⁻¹ = (r * a * r⁻¹) * ((r * b * r⁻¹ * b⁻¹) * a⁻¹) := by
            group
        _ = (r * a * r⁻¹) * (a⁻¹ * (r * b * r⁻¹ * b⁻¹)) := by rw [hc]
        _ = (r * a * r⁻¹ * a⁻¹) * (r * b * r⁻¹ * b⁻¹) := by group
    have hφa1 : r * a * r⁻¹ * a⁻¹ = 1 := by
      have e : (r * a * r⁻¹ * a⁻¹) * 1 = (r * a * r⁻¹ * a⁻¹) * (r * a * r⁻¹ * a⁻¹) := by
        rw [mul_one]
        calc r * a * r⁻¹ * a⁻¹ = r * b * r⁻¹ * b⁻¹ := hφb.symm
          _ = r * (a * b) * r⁻¹ * (a * b)⁻¹ := hφab.symm
          _ = _ := by rw [hmul, hφb]
      exact (mul_left_cancel e).symm
    have hra : r * a * r⁻¹ = a := mul_inv_eq_one.mp hφa1
    have hrb : r * b * r⁻¹ = b := mul_inv_eq_one.mp (hφb.trans hφa1)
    have hr1 : ∀ w ∈ fsuV1 T V, r * w * r⁻¹ = w := by
      intro w hw
      rw [← Subgroup.mem_centralizer_iff.mp (hPH hrP) w hw, mul_inv_cancel_right]
    have hr2 : ∀ w ∈ V₂, r * w * r⁻¹ = w := by
      intro w hw
      rcases S14.mem_V2 ha haV hw with h' | h'
      · exact hr1 w h'
      · calc r * w * r⁻¹ = (r * a * r⁻¹)⁻¹ * (r * (a * w) * r⁻¹) := by group
          _ = w := by rw [hra, hr1 _ h']; group
    have hr3 : ∀ v ∈ V, r * v * r⁻¹ = v := by
      intro v hv
      rcases S14.mem_V hb hbV hv with h' | h'
      · exact hr2 v h'
      · calc r * v * r⁻¹ = (r * b * r⁻¹)⁻¹ * (r * (b * v) * r⁻¹) := by group
          _ = v := by rw [hrb, hr2 _ h']; group
    apply hrC
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro v hv
    calc v * r = r * v * r⁻¹ * r := by rw [hr3 v hv]
      _ = r * v := by group
  · rw [hj]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (j + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)

omit [Finite G] in
theorem le_normalizer_cT (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    L ⊔ T ≤ Subgroup.normalizer ((T ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) := by
  rw [hF.cT]
  exact le_normalizer_pCoreOf 2 _

theorem eight_le_relIndex_T (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) :
    8 ≤ (Subgroup.centralizer (V : Set G)).relIndex T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  set C := Subgroup.centralizer (V : Set G) with hC
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set P := pCoreOf 2 (L₁Of L (fsuV1 T V)) with hP
  have hRT : R ≤ T := pCoreOf_le_of_le h le_sup_right
  have hPN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (P : Set G) :=
    sup_le (le_normalizer_pCoreOf 2 _) (S14.T_Lp.trans (normalizer_le_normalizer_pCoreOf 2 _))
  have hPR : P ≤ R :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 _).trans le_sup_left) hPN
      (pCoreOf_isPGroup 2 _)
  have hL1L : L₁Of L (fsuV1 T V) ≤ L := L32NSet14.Setting.L1_le.trans inf_le_left
  have hCT : C ⊓ T ≤ R := by
    rw [inf_comm, hF.cT]
    refine le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le_of_le h le_sup_right).trans le_sup_right)
      ?_ (pCoreOf_isPGroup 2 _)
    exact (sup_le_sup_right hL1L T).trans (le_normalizer_pCoreOf 2 _)
  have h4 : 4 ≤ C.relIndex P := four_le_relIndex_pCoreOf h hMod hF h1222 h1332 h1334
  have hPRle : C.relIndex P ≤ C.relIndex R :=
    Subgroup.relIndex_le_of_le_right hPR (relIndex_ne_zero_fin C R)
  have hmul := Subgroup.relIndex_mul_relIndex (C ⊓ T) R T hCT hRT
  have e1 : (C ⊓ T).relIndex R = C.relIndex R := by
    rw [← Subgroup.inf_relIndex_right (C ⊓ T) R, inf_assoc, inf_eq_right.mpr hRT,
      Subgroup.inf_relIndex_right]
  rw [e1, S14.index2_eq, Subgroup.inf_relIndex_right] at hmul
  omega

theorem eq_cT_of_le (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {Q : Subgroup G} (hQ : Q ≤ T ⊓ Subgroup.centralizer (V : Set G))
    (h8 : Q.relIndex T ≤ 8) : Q = T ⊓ Subgroup.centralizer (V : Set G) := by
  have h8' := eight_le_relIndex_T h hMod hF h1222 h1332 h1334
  have hmul := Subgroup.relIndex_mul_relIndex Q (T ⊓ Subgroup.centralizer (V : Set G)) T hQ
    inf_le_left
  rw [inf_comm, Subgroup.inf_relIndex_right] at hmul
  have hpos : Q.relIndex (Subgroup.centralizer (V : Set G) ⊓ T) ≠ 0 := relIndex_ne_zero_fin _ _
  have h1 : Q.relIndex (Subgroup.centralizer (V : Set G) ⊓ T) = 1 := by
    rcases Nat.lt_or_ge (Q.relIndex (Subgroup.centralizer (V : Set G) ⊓ T)) 2 with hl | hl
    · omega
    · nlinarith
  rw [inf_comm]
  exact le_antisymm (inf_comm T _ ▸ hQ) (Subgroup.relIndex_eq_one.mp h1)

end CFSG.Quasithin.H13.L32A
