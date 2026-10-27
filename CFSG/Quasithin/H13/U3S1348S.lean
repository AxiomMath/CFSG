module

public import CFSG.Quasithin.H13.U3S1348R
public import CFSG.Quasithin.H13.U3S1348N

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup Equiv CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem quasithinO2QuotientIso_prod {H A B : Subgroup G} {Q₁ Q₂ : Type*} [Group Q₁]
    [Group Q₂] (hAH : A ≤ H) (hBH : B ≤ H) (hHA : H ≤ normalizer (A : Set G))
    (hHB : H ≤ normalizer (B : Set G)) (hdec : ∀ h ∈ H, ∃ a ∈ A, ∃ b ∈ B, h = a * b)
    (hAB : A ⊓ B ≤ pCoreOf 2 H) (hA : quasithinO2QuotientIso A Q₁)
    (hB : quasithinO2QuotientIso B Q₂) (hOA : pCoreOf 2 A = A ⊓ pCoreOf 2 H)
    (hOB : pCoreOf 2 B = pCoreOf 2 H) : quasithinO2QuotientIso H (Q₁ × Q₂) := by
  obtain ⟨φ₁, hφ₁, hker₁⟩ := hA
  obtain ⟨φ₂, hφ₂, hker₂⟩ := hB
  have hdec' : ∀ h : ↥H, ∃ a : ↥A, ∃ b : ↥B, (h : G) = a * b := fun h => by
    obtain ⟨a, ha, b, hb, e⟩ := hdec h h.2
    exact ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩
  choose aOf bOf hab using hdec'
  have hwd : ∀ (h : ↥H) (a : ↥A) (b : ↥B), (h : G) = a * b →
      φ₁ (aOf h) = φ₁ a ∧ φ₂ (bOf h) = φ₂ b := by
    intro h a b e
    have hc : ((aOf h : G))⁻¹ * a = bOf h * (b : G)⁻¹ := by
      have h1 := hab h
      rw [e] at h1
      calc ((aOf h : G))⁻¹ * a = ((aOf h : G))⁻¹ * (a * b) * (b : G)⁻¹ := by group
        _ = ((aOf h : G))⁻¹ * (aOf h * bOf h) * (b : G)⁻¹ := by rw [h1]
        _ = bOf h * (b : G)⁻¹ := by group
    have hmemA : ((aOf h : G))⁻¹ * a ∈ A ⊓ B :=
      mem_inf.2 ⟨mul_mem (inv_mem (aOf h).2) a.2, hc ▸ mul_mem (bOf h).2 (inv_mem b.2)⟩
    have hO := hAB hmemA
    refine ⟨(map_eq_map_iff_of_ker hker₁ _ _).2 ?_, ?_⟩
    · rw [hOA]
      exact ⟨hmemA.1, hO⟩
    · have hO' : (bOf h : G) * (b : G)⁻¹ ∈ pCoreOf 2 B := by
        rw [hOB, ← hc]
        exact hO
      have h2 : ((b : G))⁻¹ * bOf h ∈ pCoreOf 2 B := by
        have := conj_mem_pCoreOf (le_normalizer (inv_mem b.2)) hO'
        have e2 : (b : G)⁻¹ * (bOf h * (b : G)⁻¹) * (b : G)⁻¹⁻¹ = (b : G)⁻¹ * bOf h := by group
        rwa [e2] at this
      exact ((map_eq_map_iff_of_ker hker₂ _ _).2 h2).symm
  refine ⟨MonoidHom.mk' (fun h => (φ₁ (aOf h), φ₂ (bOf h))) fun x y => ?_, ?_, ?_⟩
  ·
    have ha'' : ((bOf x : G)) * aOf y * ((bOf x : G))⁻¹ ∈ A :=
      (mem_normalizer_iff.mp (hHA (hBH (bOf x).2)) _).mp (aOf y).2
    obtain ⟨h1, h2⟩ := hwd (x * y) ⟨aOf x * (bOf x * aOf y * ((bOf x : G))⁻¹),
      mul_mem (aOf x).2 ha''⟩ (bOf x * bOf y) (by
        rw [Subgroup.coe_mul, hab x, hab y]
        simp only [Subgroup.coe_mul]
        group)
    have hc : ((aOf y : G))⁻¹ * (bOf x * aOf y * ((bOf x : G))⁻¹) ∈ A :=
      mul_mem (inv_mem (aOf y).2) ha''
    have hcomm : (⟨(bOf x : G) * aOf y * ((bOf x : G))⁻¹, ha''⟩ : ↥A) =
        aOf y * ⟨((aOf y : G))⁻¹ * (bOf x * aOf y * ((bOf x : G))⁻¹), hc⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul]; group)
    have hk : φ₁ ⟨((aOf y : G))⁻¹ * (bOf x * aOf y * ((bOf x : G))⁻¹), hc⟩ = 1 := by
      rw [map_eq_one_iff_of_ker hker₁, hOA]
      refine mem_inf.2 ⟨hc, hAB (mem_inf.2 ⟨hc, ?_⟩)⟩
      show ((aOf y : G))⁻¹ * (bOf x * aOf y * ((bOf x : G))⁻¹) ∈ B
      have hb' : ((aOf y : G))⁻¹ * bOf x * aOf y ∈ B := by
        simpa using (mem_normalizer_iff.mp (hHB (inv_mem (hAH (aOf y).2))) _).mp (bOf x).2
      have e : ((aOf y : G))⁻¹ * (bOf x * aOf y * ((bOf x : G))⁻¹) =
          (((aOf y : G))⁻¹ * bOf x * aOf y) * ((bOf x : G))⁻¹ := by group
      rw [e]
      exact mul_mem hb' (inv_mem (bOf x).2)
    simp only [Prod.mk_mul_mk]
    rw [h1, h2]
    have e1 : (⟨aOf x * (bOf x * aOf y * ((bOf x : G))⁻¹), mul_mem (aOf x).2 ha''⟩ : ↥A) =
        aOf x * ⟨(bOf x : G) * aOf y * ((bOf x : G))⁻¹, ha''⟩ := rfl
    rw [e1, map_mul φ₁, hcomm, map_mul φ₁, hk, mul_one, map_mul φ₂]
  ·
    rintro ⟨q₁, q₂⟩
    obtain ⟨a, rfl⟩ := hφ₁ q₁
    obtain ⟨b, rfl⟩ := hφ₂ q₂
    refine ⟨⟨a * b, mul_mem (hAH a.2) (hBH b.2)⟩, ?_⟩
    obtain ⟨h1, h2⟩ := hwd ⟨a * b, mul_mem (hAH a.2) (hBH b.2)⟩ a b rfl
    simp only [MonoidHom.mk'_apply, h1, h2]
  ·
    ext h
    rw [MonoidHom.mem_ker, MonoidHom.mk'_apply, ← coe_mem_pCoreOf_iff,
      Prod.mk_eq_one, map_eq_one_iff_of_ker hker₁, map_eq_one_iff_of_ker hker₂, hOA, hOB]
    constructor
    · rintro ⟨⟨-, ha⟩, hb⟩
      rw [hab h]
      exact mul_mem ha hb
    · intro hh
      have hb : (bOf h : G) ∈ B := (bOf h).2
      have ha : (aOf h : G) ∈ A ⊓ pCoreOf 2 H := by
        refine ⟨(aOf h).2, ?_⟩
        have hB' : (aOf h : G) ∈ B := by
          have e : (aOf h : G) = h * ((bOf h : G))⁻¹ := by rw [hab h]; group
          rw [e]
          exact mul_mem ((pCoreOf_le 2 B) (hOB.symm ▸ hh)) (inv_mem hb)
        exact hAB ⟨(aOf h).2, hB'⟩
      refine ⟨ha, ?_⟩
      have e : (bOf h : G) = ((aOf h : G))⁻¹ * h := by rw [hab h]; group
      rw [e]
      exact mul_mem (inv_mem ha.2) hh

theorem s134_le_normalizer_U {H VH : Subgroup G} (hV : IsElemAbelian 2 VH)
    {K : Subgroup (MulAut (IntMod VH hV))} (hHN : H ≤ normalizer (VH : Set G))
    (hHK : ∀ g ∈ autI hV H, B1.conjAut g K = K) :
    H ≤ normalizer (C124.toG hV (commSub (⊤ : Subgroup (IntMod VH hV)) K) : Set G) := by
  refine A5.le_normalizer_of_forall_conj_mem fun h hh x hx => ?_
  obtain ⟨w, hw, rfl⟩ := (C124.mem_toG hV).1 hx
  have hg := convI_mem_autI hV hh (hHN hh)
  exact (C124.mem_toG hV).2 ⟨convI hV ⟨h, hHN hh⟩ w, mem_commSub_of_conjAut (hHK _ hg) hw,
    convI_apply_val hV ⟨h, hHN hh⟩ w⟩

theorem s134_I_inf_CU_le {VH I : Subgroup G} (hV : IsElemAbelian 2 VH)
    {J : Subgroup (MulAut (IntMod VH hV))} {𝓗 : Finset (Subgroup (MulAut (IntMod VH hV)))}
    (hb : IsTransvectionBlocks J 𝓗) {K : Subgroup (MulAut (IntMod VH hV))} (hK : K ∈ 𝓗)
    (hIK : autI hV I = K) (hIN : I ≤ normalizer (VH : Set G)) :
    I ⊓ centralizer (C124.toG hV (commSub (⊤ : Subgroup (IntMod VH hV)) K) : Set G) ≤
      centralizer (VH : Set G) := by
  intro x hx
  have hxN := hIN hx.1
  have hxK : convI hV ⟨x, hxN⟩ ∈ K := hIK ▸ convI_mem_autI hV hx.1 hxN
  have h1 : convI hV ⟨x, hxN⟩ = 1 := by
    refine blk_eq_one_of_fix hb hK hxK fun w hw => IntMod.val_injective ?_
    rw [convI_apply_val]
    have h2 : w.val * x = x * w.val :=
      mem_centralizer_iff.1 hx.2 _ ((C124.mem_toG_iff_of_mem hV w).2 hw)
    show x * w.val * x⁻¹ = w.val
    rw [← h2]
    group
  exact (convI_eq_one_iff hV _).1 h1

theorem s134_quot_C (S : A6.Setting134 G T L V)
    (he : Nonempty (↥L ⧸ CFSG.pCore 2 ↥L ≃* alternatingGroup (Fin 6))) {z : G}
    {H VH : Subgroup G} (hHz : InHz T L V z H) (hred : IsTwoReducedIn H VH)
    (hcR : r1Of T L V ⊓ centralizer (VH : Set G) = pCoreOf 2 H)
    (hJ : ¬ thompsonJ (r1Of T L V) ≤ centralizer (VH : Set G))
    {J : Subgroup (MulAut (IntMod VH hred.2.2.1))}
    {𝓗 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))} (hb : IsTransvectionBlocks J 𝓗)
    {K : Subgroup (MulAut (IntMod VH hred.2.2.1))} (hK : K ∈ 𝓗)
    (hIK : autI hred.2.2.1 (conjClosure (thompsonJ (r1Of T L V)) H) = K)
    (hHK : ∀ g ∈ autI hred.2.2.1 H, B1.conjAut g K = K)
    {τ : MulAut (IntMod VH hred.2.2.1)} (hτJ : τ ∈ autI hred.2.2.1 (thompsonJ (r1Of T L V)))
    (hτK : τ ∈ K) (hτ1 : τ ≠ 1)
    (hTH9 : T.relIndex H = 9) :
    quasithinO2QuotientIso (H ⊓ centralizer (C124.toG hred.2.2.1
        (commSub (⊤ : Subgroup (IntMod VH hred.2.2.1)) K) : Set G)) (Perm (Fin 3)) ∧
      pCoreOf 2 (H ⊓ centralizer (C124.toG hred.2.2.1
        (commSub (⊤ : Subgroup (IntMod VH hred.2.2.1)) K) : Set G)) = pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set I := conjClosure (thompsonJ (r1Of T L V)) H with hIdef
  set U := C124.toG hred.2.2.1 (commSub (⊤ : Subgroup (IntMod VH hred.2.2.1)) K) with hU
  set C := H ⊓ centralizer (U : Set G) with hC
  obtain ⟨hTsyl, -, -, -, -⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hHN : H ≤ normalizer (VH : Set G) := hred.2.1
  have hJR : thompsonJ (r1Of T L V) ≤ r1Of T L V := iSup₂_le fun _ hA => hA.1
  have hJT : thompsonJ (r1Of T L V) ≤ T := hJR.trans (r1Of_le_T T L V)
  have hIH : I ≤ H := conjClosure_le fun h hh j hj =>
    mul_mem (mul_mem hh (hTH (hJT hj))) (inv_mem hh)
  have hHI : H ≤ normalizer (I : Set G) := le_normalizer_conjClosure _ _
  have hIN : I ≤ normalizer (VH : Set G) := hIH.trans hHN
  have hCH : C ≤ H := inf_le_left
  have hHU := s134_le_normalizer_U hred.2.2.1 hHN hHK
  have hHC : H ≤ normalizer (C : Set G) := fun h hh =>
    mem_normalizer_inf_of (le_normalizer hh) (mem_normalizer_centralizer_of_mem (hHU hh))
  have hUV : U ≤ VH := C124.toG_le hred.2.2.1 _
  have hCV : H ⊓ centralizer (VH : Set G) ≤ C :=
    fun x hx => ⟨hx.1, centralizer_le (SetLike.coe_subset_coe.2 hUV) hx.2⟩
  have hOC : pCoreOf 2 H ≤ C := fun x hx =>
    hCV ⟨pCoreOf_le 2 H hx, pCoreOf_le_centralizer_of_reduced' hred hx⟩
  have hsup : I ⊔ C = H := by
    refine le_antisymm (sup_le hIH hCH) fun h hh => ?_
    obtain ⟨i, hi, hiC⟩ := s134_exists_I_mul hred.2.2.1 hb hK hIK hHN hHK hh
    have e : h = i * (i⁻¹ * h) := by group
    rw [e]
    exact mul_mem (mem_sup_left hi)
      (mem_sup_right (mem_inf.2 ⟨mul_mem (inv_mem (hIH hi)) hh, hiC⟩))
  have hIC : I ⊓ C = I ⊓ centralizer (VH : Set G) :=
    le_antisymm (le_inf inf_le_left fun x hx =>
      s134_I_inf_CU_le hred.2.2.1 hb hK hIK hIN ⟨hx.1, hx.2.2⟩)
      fun x hx => ⟨hx.1, hCV ⟨hIH hx.1, hx.2⟩⟩
  have h6 : C.relIndex H = 6 := by
    have h1 := relIndex_sup_eq (K := I) (T := C) (hCH.trans hHI)
    rw [hsup, hIC] at h1
    rw [h1, ← card_autI_eq hred.2.2.1 hIN, hIK, hb.card_eq K hK]
  have hsylC : IsSylowTwoOf (T ⊓ C) C := A4.isSylowTwoOf_inf_normal hTsyl hCH hHC
  have hm1 := relIndex_mul_relIndex (T ⊓ C) C H inf_le_right hCH
  have hm2 := relIndex_mul_relIndex (T ⊓ C) T H inf_le_left hTH
  rw [h6] at hm1
  rw [hTH9, ← hm1] at hm2
  obtain ⟨n, hn⟩ := hT2.index ((T ⊓ C).subgroupOf T)
  have hrT : (T ⊓ C).relIndex T = 2 ^ n := hn
  have hTC : ¬ T ≤ C := by
    intro hTC
    obtain ⟨⟨t, htN⟩, htJ, rfl⟩ := (mem_autI hred.2.2.1).1 hτJ
    apply hτ1
    refine blk_eq_one_of_fix hb hK hτK fun w hw => IntMod.val_injective ?_
    rw [convI_apply_val]
    have h2 : w.val * t = t * w.val :=
      mem_centralizer_iff.1 (hTC (hJT htJ)).2 _ ((C124.mem_toG_iff_of_mem hred.2.2.1 w).2 hw)
    show t * w.val * t⁻¹ = w.val
    rw [← h2]
    group
  have hn0 : n ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hrT
    exact hTC ((relIndex_eq_one.1 hrT).trans inf_le_right)
  have hodd : ¬ 2 ∣ (T ⊓ C).relIndex C := hsylC.2.2
  rw [hrT] at hm2
  have hn1 : n = 1 := by
    rcases n with _ | _ | n
    · exact absurd rfl hn0
    · rfl
    · exfalso
      rw [pow_succ, pow_succ] at hm2
      generalize 2 ^ n = m at hm2
      apply hodd
      exact ⟨3 * m, by omega⟩
  rw [hn1, pow_one] at hm2 hrT
  have h3 : (T ⊓ C).relIndex C = 3 := by omega
  have hN : ¬ C ≤ normalizer ((T ⊓ C : Subgroup G) : Set G) := by
    intro hN
    have hTO : T ⊓ C ≤ pCoreOf 2 H := by
      refine (CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _
        inf_le_right ?_ (hT2.to_le inf_le_left)).trans (pCoreOf_le_pCoreOf hCH hHC)
      exact (normal_subgroupOf_iff_le_normalizer inf_le_right).2 hN
    have heq : T ⊓ C = pCoreOf 2 H :=
      le_antisymm hTO (le_inf (pCoreOf_two_le_of_isSylowTwoOf hTsyl) hOC)
    rw [heq] at hrT
    have hOR : pCoreOf 2 H ≤ r1Of T L V := hcR ▸ inf_le_left
    have hRT : r1Of T L V ≤ T := r1Of_le_T T L V
    have hm := relIndex_mul_relIndex (pCoreOf 2 H) (r1Of T L V) T hOR hRT
    rw [hrT] at hm
    have h1 : (pCoreOf 2 H).relIndex (r1Of T L V) ≠ 1 := fun h =>
      hJ ((hJR.trans (relIndex_eq_one.1 h)).trans (pCoreOf_le_centralizer_of_reduced' hred))
    have h2 : (r1Of T L V).relIndex T ≠ 1 := fun h =>
      s134_T_ne_r1 S he (le_antisymm (relIndex_eq_one.1 h) hRT)
    rcases (Nat.dvd_prime Nat.prime_two).1 (Dvd.intro _ hm) with ha | ha
    · exact h1 ha
    · rw [ha] at hm
      exact h2 (by omega)
  refine ⟨quot_S3_of_index_three hsylC h3 hN, le_antisymm (pCoreOf_le_pCoreOf hCH hHC) ?_⟩
  refine CFSG.RankThreeEvenClassification.Helpers.normal_pSubgroup_le_pCoreOf 2 _ _ hOC ?_
    (pCoreOf_isPGroup 2 H)
  exact (normal_subgroupOf_iff_le_normalizer hOC).2 (hCH.trans (le_normalizer_pCoreOf 2 H))

end CFSG.Quasithin.H13.U3
