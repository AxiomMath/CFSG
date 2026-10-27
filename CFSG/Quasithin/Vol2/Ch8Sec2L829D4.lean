module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829D4G
public import CFSG.Quasithin.Vol2.Ch8Sec2L829D4Abs
public import CFSG.Quasithin.Vol2.Ch8Sec2L828SBt
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0
public import CFSG.Quasithin.Background.AutOnFixV
public import CFSG.Quasithin.Vol2.Ch8Sec2L828E

public section

namespace CFSG.Quasithin.H13.L829N

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs
open scoped IsMulCommutative commutatorElement

theorem card_autOn_mQuot_sd4 {G : Type} [Group G] [Finite G] {A V : Subgroup G}
    [IsMulCommutative ↥V] {m : ℕ} (hA : A ≤ Subgroup.normalizer (V : Set G))
    (hAp : IsPGroup 2 ↥A) (hm : mQuot A (A ⊓ Subgroup.centralizer (V : Set G)) = m) :
    Nat.card ↥(autOn A V) = 2 ^ m := by
  rw [CFSG.Quasithin.AutOn.card_autOn_eq_relIndex hA]
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hAp
  have hdvd : (A ⊓ Subgroup.centralizer (V : Set G)).relIndex A ∣ Nat.card ↥A :=
    Subgroup.relIndex_dvd_card _ _
  rw [hk] at hdvd
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
  unfold E3.mQuot at hm
  rw [hi, padicValNat.prime_pow] at hm
  rw [hi, ← hm]

theorem card_U_eq_16_sd4 {G : Type} [Group G] [Finite G] {V U : Subgroup G}
    (hV : IsElemAbelian 2 V) (hUV : U ≤ V) (hrk : rk ↥U = 4) : Nat.card ↥U = 2 ^ 4 := by
  have hVp : IsPGroup 2 ↥V := CFSG.Quasithin.F7.isPGroup_of_isElemAbelian hV
  have hp' : IsPGroup 2 ↥(U.subgroupOf V) := IsPGroup.to_subgroup hVp (U.subgroupOf V)
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).mp hp'
  have hc : Nat.card ↥U = 2 ^ k :=
    ((Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUV).toEquiv).symm).trans hk
  have hk4 : k = 4 := by
    unfold rk at hrk
    rw [hc, padicValNat.prime_pow] at hrk
    exact hrk
  rw [hc, hk4]

theorem d4_core_sd4 {G : Type} [Group G] [Finite G] {V L U B : Subgroup G} [IsMulCommutative ↥V]
    (hLV : L ≤ Subgroup.normalizer (V : Set G)) (hUV : U ≤ V) (hBV : B ≤ V)
    {Uv : Subgroup ↥V} (hUv : ∀ u : ↥V, u ∈ Uv ↔ (u : G) ∈ U)
    (hNF : D4NF_sd4 (autOn L V) Uv)
    (hB : ⁅V, CFSG.Quasithin.H13.ch82LU L U⁆ ≤ B)
    (hcardU : Nat.card ↥U = 2 ^ 4) :
    U < ⁅B, CFSG.Quasithin.H13.ch82LU L U⁆ ⊔ U ∧
    (∀ C : Subgroup G, U ≤ C → C ≤ ⁅B, CFSG.Quasithin.H13.ch82LU L U⁆ ⊔ U →
      CFSG.Quasithin.H13.ch82LU L U ≤ Subgroup.normalizer (C : Set G) →
      C = U ∨ C = ⁅B, CFSG.Quasithin.H13.ch82LU L U⁆ ⊔ U) ∧
    mQuot (⁅B, CFSG.Quasithin.H13.ch82LU L U⁆ ⊔ U) U = 4 ∧
    ∃ x ∈ CFSG.Quasithin.H13.ch82LU L U, ∃ y ∈ CFSG.Quasithin.H13.ch82LU L U,
      ∃ b ∈ ⁅B, CFSG.Quasithin.H13.ch82LU L U⁆ ⊔ U, ⁅⁅x, y⁆, b⁆ ∉ U := by
  set LU := CFSG.Quasithin.H13.ch82LU L U with hLUdef
  have hLUV : LU ≤ Subgroup.normalizer (V : Set G) :=
    (CFSG.Quasithin.perfectCore_le _).trans (inf_le_left.trans hLV)
  have hLUaut : autOn LU V = D4P_sd4 (autOn L V) Uv := autOn_LU_sd4 hUv hLV hUV
  obtain ⟨hUN, hcardN, hirr, hnab⟩ := hNF
  set Pv := D4P_sd4 (autOn L V) Uv with hPv
  set Nv := D4N_sd4 (autOn L V) Uv with hNv
  have hUinv : ∀ p ∈ Pv, ∀ u ∈ Uv, p u ∈ Uv := by
    intro p hp u hu
    have hstab : p ∈ stabSub (V := ↥V) Uv := (Subgroup.mem_inf.mp (CFSG.Quasithin.perfectCore_le _ hp)).2
    exact (show ∀ w : ↥V, p w ∈ Uv ↔ w ∈ Uv from hstab) u |>.mpr hu
  have hsup : CFSG.Quasithin.H13.s828CommSub Pv Nv ⊔ Uv = Nv :=
    sup_comm_eq_sd4 hUN rfl hirr hnab hUinv
  have hφU : Uv.map V.subtype = U := by
    ext x
    constructor
    · rintro ⟨u, hu, rfl⟩
      exact (hUv u).mp hu
    · intro hx
      exact ⟨⟨x, hUV hx⟩, (hUv _).mpr hx, rfl⟩
  have hφN : Nv.map V.subtype = ⁅LU, V⁆ := by
    have h1 : Nv = CFSG.Quasithin.H13.s828CommSub (autOn LU V) ⊤ := by
      rw [hLUaut]
      exact comm_sd4_eq_s828_sd4 Pv
    rw [h1, CFSG.Quasithin.H13.s828_map_commSub hLUV ⊤]
    congr 1
    ext x
    simp
  have hB' : ⁅LU, V⁆ ≤ B := by
    rw [Subgroup.commutator_comm]
    exact hB
  have hφB : (CFSG.Quasithin.H13.s828CommSub Pv (B.subgroupOf V)).map V.subtype = ⁅LU, B⁆ := by
    rw [← hLUaut, CFSG.Quasithin.H13.s828_map_commSub hLUV (B.subgroupOf V),
      Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hBV]
  have hNB : Nv ≤ B.subgroupOf V := by
    intro n hn
    rw [Subgroup.mem_subgroupOf]
    have h2 : (n : G) ∈ Nv.map V.subtype := Subgroup.mem_map_of_mem _ hn
    rw [hφN] at h2
    exact hB' h2
  have hsub' : CFSG.Quasithin.H13.s828CommSub Pv (B.subgroupOf V) ≤ Nv :=
    (s828CommSub_mono_sd4 Pv le_top).trans (le_of_eq (comm_sd4_eq_s828_sd4 Pv).symm)
  have hSup : CFSG.Quasithin.H13.s828CommSub Pv (B.subgroupOf V) ⊔ Uv = Nv := by
    apply le_antisymm
    · exact sup_le hsub' hUN
    · rw [← hsup]
      exact sup_le_sup_right (s828CommSub_mono_sd4 Pv hNB) Uv
  have hB1 : ⁅B, LU⁆ ⊔ U = Nv.map V.subtype := by
    rw [Subgroup.commutator_comm, ← hφB, ← hφU, ← Subgroup.map_sup, hSup]
  have hcardUv : Nat.card ↥Uv = 2 ^ 4 := by
    rw [← hcardU, ← hφU, Subgroup.card_map_of_injective V.subtype_injective]
  have hcardNG : Nat.card ↥(Nv.map V.subtype) = 2 ^ 8 := by
    rw [Subgroup.card_map_of_injective V.subtype_injective, hcardN, hcardUv]
    norm_num
  have hUNG : U ≤ Nv.map V.subtype := hφU ▸ Subgroup.map_mono hUN
  refine ⟨?_, ?_, ?_, ?_⟩
  ·
    rw [hB1]
    refine lt_of_le_of_ne hUNG ?_
    intro h
    have h3 : Nat.card ↥U = Nat.card ↥(Nv.map V.subtype) := by rw [h]
    rw [hcardU, hcardNG] at h3
    norm_num at h3
  ·
    intro C hUC hCB hLUC
    rw [hB1] at hCB ⊢
    have hCV : C ≤ V := fun c hc => by
      obtain ⟨n, -, hnc⟩ := Subgroup.mem_map.mp (hCB hc)
      rw [← hnc]
      exact n.2
    have hCeq : (C.subgroupOf V).map V.subtype = C := by
      rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hCV]
    have hUvCv : Uv ≤ C.subgroupOf V := fun u hu => Subgroup.mem_subgroupOf.mpr (hUC ((hUv u).mp hu))
    have hCvN : C.subgroupOf V ≤ Nv := by
      intro c hc
      obtain ⟨n, hn, hnc⟩ := Subgroup.mem_map.mp (hCB (Subgroup.mem_subgroupOf.mp hc))
      have : n = c := Subtype.ext hnc
      rw [← this]
      exact hn
    have hinvCv : ∀ p ∈ Pv, ∀ c ∈ C.subgroupOf V, p c ∈ C.subgroupOf V := by
      intro p hp c hc
      rw [← hLUaut] at hp
      obtain ⟨x, hxN, hxLU, rfl⟩ := AutOn.mem_autOn_iff_exists.mp hp
      rw [Subgroup.mem_subgroupOf] at hc ⊢
      rw [AutOn.coe_conjAct_apply]
      exact (Subgroup.mem_normalizer_iff.mp (hLUC hxLU) _).mp hc
    rcases hirr (C.subgroupOf V) hUvCv hCvN hinvCv with h | h
    · left
      rw [← hCeq, h, hφU]
    · right
      rw [← hCeq, h]
  ·
    have hrel : U.relIndex (Nv.map V.subtype) = 2 ^ 4 := by
      have h1 := Subgroup.relIndex_mul_card (H := U) (K := Nv.map V.subtype)
      rw [inf_eq_left.mpr hUNG, hcardU, hcardNG] at h1
      omega
    rw [hB1]
    unfold E3.mQuot
    rw [hrel, padicValNat.prime_pow]
  ·
    obtain ⟨p, hp, q, hq, n, hn, hne⟩ := hnab
    rw [← hLUaut] at hp hq
    obtain ⟨x0, hx0N, hx0LU, hx0⟩ := AutOn.mem_autOn_iff_exists.mp hp
    obtain ⟨y0, hy0N, hy0LU, hy0⟩ := AutOn.mem_autOn_iff_exists.mp hq
    have hc : ⁅y0, x0⁆ ∈ Subgroup.normalizer (V : Set G) := by
      rw [commutatorElement_def]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hy0N hx0N)
        (Subgroup.inv_mem _ hy0N)) (Subgroup.inv_mem _ hx0N)
    have e1 : (⟨⁅y0, x0⁆, hc⟩ : Subgroup.normalizer (V : Set G)) =
        ⁅(⟨y0, hy0N⟩ : Subgroup.normalizer (V : Set G)), ⟨x0, hx0N⟩⁆ :=
      Subtype.ext rfl
    have hkey : conjAct V ⟨⁅y0, x0⁆, hc⟩ = ⁅p, q⁆⁻¹ := by
      rw [e1, map_commutatorElement, hy0, hx0, commutatorElement_inv]
    have hcoe : ∀ m : ↥V, (((⁅p, q⁆⁻¹ : MulAut ↥V) m : ↥V) : G) = ⁅y0, x0⁆ * (m : G) * (⁅y0, x0⁆)⁻¹ := by
      intro m
      rw [← hkey, AutOn.coe_conjAct_apply]
    refine ⟨y0, hy0LU, x0, hx0LU, (n : G), ?_, ?_⟩
    · rw [hB1]
      exact Subgroup.mem_map_of_mem _ hn
    · intro hcn
      apply hne
      apply (hUv _).mpr
      rw [Subgroup.coe_mul, Subgroup.coe_inv, hcoe, commutatorElement_def]
      rw [commutatorElement_def] at hcn
      exact hcn

theorem stmtD4L3M22_holds
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (h825 : Stmt8_2_5) (h828 : Stmt8_2_8) :
    StmtD4L3M22 := by
  intro G _ _ T L I hyp h731 h821 hc hrow H h k hH hh hC hrow'
  have hC5 := h825 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  have hC8 := h828 G T L I hyp h731 h821 hc hrow H h k hH hh hC
  obtain ⟨hV, hL0, -, hLN, -, hAN, hAL, hAp, hAe, -, -, -, -⟩ :=
    setup_828 hmod h711n hyp hrow hC hC5
  obtain ⟨-, -, -, -, h5⟩ := hC8
  obtain ⟨-, -, -, hL34, hM22, -, -, -⟩ := hC5
  have hUv : ∀ u : ↥(fsuV T I), u ∈ fixV (autOn (ch82A (fsuV T I) h) (fsuV T I)) ↔
      (u : G) ∈ ch82U (fsuV T I) h := by
    intro u
    rw [fixV_autOn_82 hAN, Subgroup.mem_subgroupOf]
    rfl
  have hXN : autOn (ch82A (fsuV T I) h) (fsuV T I) ≤
      Subgroup.normalizer (autOn L (fsuV T I) : Set (MulAut ↥(fsuV T I))) :=
    CFSG.Quasithin.AutOn.autOn_le_normalizer_autOn hAL
  have hXe : IsElemAbelian 2 (autOn (ch82A (fsuV T I) h) (fsuV T I)) :=
    isElemAbelian_autOn_82 (V := fsuV T I) hAe
  have hNF : D4NF_sd4 (autOn L (fsuV T I)) (fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) := by
    rcases hrow' with hL | hM
    · obtain ⟨-, -, hmq, hrk⟩ := hL34 ⟨1, hL⟩
      have hL' : BinaryNineTensor (autOn L (fsuV T I)) ⊤ ⊥ 1 := by
        unfold Row711L3Nine at hL
        rw [hL0] at hL
        exact hL.2
      have hX : Nat.card ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 2 ^ 4 :=
        card_autOn_mQuot_sd4 hAN hAp hmq
      have hfX : Nat.card ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 2 ^ 4 := by
        rw [CFSG.Quasithin.AutOn.card_fixV_autOn_eq hAN]
        exact card_U_eq_16_sd4 hV inf_le_left hrk
      exact D4NF_L34_of_sd4 hL' hXN hXe hX hfX
    · obtain ⟨-, -, hmq, hrk⟩ := hM22 hM
      have hM' : MathieuCode22 (autOn L (fsuV T I)) ⊤ ⊥ := by
        unfold Row711M22Code at hM
        rw [hL0] at hM
        exact hM
      have hX : Nat.card ↥(autOn (ch82A (fsuV T I) h) (fsuV T I)) = 2 ^ 5 :=
        card_autOn_mQuot_sd4 hAN hAp hmq
      have hfX : Nat.card ↥(fixV (autOn (ch82A (fsuV T I) h) (fsuV T I))) = 2 ^ 4 := by
        rw [CFSG.Quasithin.AutOn.card_fixV_autOn_eq hAN]
        exact card_U_eq_16_sd4 hV inf_le_left hrk
      exact D4NF_M22_of_sd4 hM' hXN hXe hX hfX
  have hrkU : rk ↥(ch82U (fsuV T I) h) = 4 := by
    rcases hrow' with hL | hM
    · exact (hL34 ⟨1, hL⟩).2.2.2
    · exact (hM22 hM).2.2.2
  have hcardU : Nat.card ↥(ch82U (fsuV T I) h) = 2 ^ 4 :=
    card_U_eq_16_sd4 hV inf_le_left hrkU
  exact d4_core_sd4 hLN inf_le_left inf_le_left hUv hNF h5 hcardU

end CFSG.Quasithin.H13.L829N
