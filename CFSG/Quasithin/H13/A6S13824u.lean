module

public import CFSG.Quasithin.H13.A6S13824t
public import CFSG.Quasithin.H13.A6S13824h
public import CFSG.Quasithin.H13.A6S13816f
public import CFSG.Quasithin.H13.A6S1372L19b
public import CFSG.Quasithin.H13.A6S13824j
public import CFSG.Quasithin.H13.A6S13824q

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open scoped Pointwise IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

omit [Finite G] in
theorem comm_l0_mem {c x : G} (hc : c ∈ l0 L) (hx : x ∈ L) : c * x * c⁻¹ * x⁻¹ ∈ pCoreOf 2 L :=
  (mem_o2Z_iff.1 (oTwoRes_le _ hc)).2 x hx

namespace DK

variable {H K : Subgroup G} (hd : S.DK H K)
include hd

theorem exists_quadY
    (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat) (h139 : Stmt13_3_9) (h1334 : Stmt13_3_4)
    (h13 : Lem13813) (h13314 : Stmt13_3_14) (h13315 : Stmt13_3_15) (h1356two : Input1356Two)
    (hA : ∀ x ∈ pCoreOf 2 (S.L1 ⊔ T), ¬ InducesTransvMod x (conjClosure S.V3 H) (fsuV1 T V)) :
    ∃ Y : Subgroup G, Y ≤ pCoreOf 2 (S.L1 ⊔ T) ∧ ⁅⁅conjClosure S.V3 H, Y⁆, Y⁆ = ⊥ ∧
      4 ≤ (Y ⊓ pCoreOf 2 H).relIndex Y ∧ IsElemAbelian 2 Y := by
  have hF := hd.hF
  obtain ⟨γ, γ', g, s, hDγ, hDH, -, hle⟩ := S.case2_of_no_transv_loc hF hA
  have hHK' : H = K ⊔ (S.L1 ⊔ T) := by
    rw [← sup_assoc, sup_eq_left.2 hd.hL1K]
    exact hd.hHK
  have hgen := lem13818Gen_holds h36 h139 h1334 h13 G T L V S hd.hS H hd.hH K hd.hK hd.hKn hHK'
    γ γ' g s (conjClosure S.V3 H) le_rfl hDH.not_ge
  have hm := S.lem13818Four_loc hd.hS.hNS h13315 h1356two hd.hH hF h13314 hA s hDγ hDH hle hgen
  obtain ⟨c, hcH, hcR⟩ := exists_conj_Vγ_le hF s
  refine ⟨conjSub c (F8.Uγ V H (g : G)), hcR, ?_, ?_,
    F7.isElemAbelian_conjSub (hF.isElemAbelian_Vγ (g := g))⟩
  · have h1 := congrArg (conjSub c) (S.comm_comm_UH_Vγ hF s)
    rwa [← conjSub_commutator, ← conjSub_commutator,
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_conjClosure S.V3 H hcH), conjSub_bot] at h1
  · have hY2 : IsPGroup 2 (conjSub c (F8.Uγ V H (g : G))) :=
      (pCoreOf_isPGroup 2 _).to_le hcR
    rw [HypF98.relIndex_eq_two_pow_mIdx hY2]
    have hQ : conjSub c (pCoreOf 2 H) = pCoreOf 2 H :=
      F7.conjSub_eq_of_mem_normalizer (le_normalizer_pCoreOf 2 H hcH)
    rw [← hQ, ← conjSub_inf, F9.mIdx_conjSub]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ mIdx (F8.Uγ V H (g : G)) (F8.Uγ V H (g : G) ⊓ pCoreOf 2 H) :=
        Nat.pow_le_pow_right (by norm_num) hm

theorem false_of_S43 (h13 : Lem13813) (h1334 : Stmt13_3_4)
    (h1337 : Stmt13_3_7) (hhat : ¬ IsHatA6 L) {ρ : ↥H →* Perm (Fin 7)}
    (hρs : Function.Surjective ρ) (hρk : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H)
    (hρT : ∀ t : ↥H, (t : G) ∈ T → ρ t ∈ S7C.T0) {x : G} (hxL : x ∈ S.L1) (hxH : x ∈ H)
    (hx43 : ρ ⟨x, hxH⟩ ∈ S7C.S43) (hxT : ρ ⟨x, hxH⟩ ∉ S7C.T0) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1H : S.L1 ≤ H := hd.hL1K.trans hd.hKH
  have hTS : S7C.T0 ≤ S7C.S43 := inf_le_right
  have hO : ∀ (o : G) (ho : o ∈ pCoreOf 2 S.L1), ρ ⟨o, hL1H (pCoreOf_le 2 _ ho)⟩ ∈ S7C.T0 :=
    fun o ho => hρT _ (S.O2L1_le_T ho)
  set c := S.cL1 hhat with hcdef
  have hcL : (c : G) ∈ S.L1 := S.cL1_mem hhat
  have hcH : (c : G) ∈ H := hL1H hcL
  set c' : ↥H := ⟨c, hcH⟩ with hc'
  have hc3 : c' ^ 3 = 1 := Subtype.ext (by simpa using S.cL1_cube hhat)
  have hρc4 : ρ c' = ρ c' ^ 4 := by
    rw [← map_pow, show c' ^ 4 = c' ^ 3 * c' by group, hc3, one_mul]
  have hρc : ρ c' ∈ S7C.S43 := by
    rcases S.L1_decomp hhat hxL with h | h | h
    · exact absurd (hO x h) hxT
    · have e : ρ ⟨(c : G) * c * x, hL1H (pCoreOf_le 2 _ h)⟩ = ρ c' * ρ c' * ρ ⟨x, hxH⟩ := by
        rw [← map_mul, ← map_mul]
        rfl
      have h1 := hO _ h
      rw [e] at h1
      have h2 : ρ c' * ρ c' ∈ S7C.S43 := by
        have := S7C.S43.mul_mem (hTS h1) (S7C.S43.inv_mem hx43)
        rwa [mul_inv_cancel_right] at this
      rw [hρc4, show ρ c' ^ 4 = (ρ c' * ρ c') * (ρ c' * ρ c') by
        simp only [pow_succ, pow_zero, one_mul, mul_assoc]]
      exact S7C.S43.mul_mem h2 h2
    · have e : ρ ⟨(c : G) * x, hL1H (pCoreOf_le 2 _ h)⟩ = ρ c' * ρ ⟨x, hxH⟩ := by
        rw [← map_mul]
        rfl
      have h1 := hO _ h
      rw [e] at h1
      have := S7C.S43.mul_mem (hTS h1) (S7C.S43.inv_mem hx43)
      rwa [mul_inv_cancel_right] at this
  have hL1S : ∀ (y : G) (hy : y ∈ S.L1), ρ ⟨y, hL1H hy⟩ ∈ S7C.S43 := by
    intro y hy
    rcases S.L1_decomp hhat hy with h | h | h
    · exact hTS (hO y h)
    · have e : ρ ⟨y, hL1H hy⟩ = (ρ c' * ρ c')⁻¹ * ρ ⟨(c : G) * c * y, hL1H (pCoreOf_le 2 _ h)⟩ := by
        rw [← map_mul, ← map_inv, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, c']
        group
      rw [e]
      exact S7C.S43.mul_mem (S7C.S43.inv_mem (S7C.S43.mul_mem hρc hρc)) (hTS (hO _ h))
    · have e : ρ ⟨y, hL1H hy⟩ = (ρ c')⁻¹ * ρ ⟨(c : G) * y, hL1H (pCoreOf_le 2 _ h)⟩ := by
        rw [← map_inv, ← map_mul]
        congr 1
        apply Subtype.ext
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, c']
        group
      rw [e]
      exact S7C.S43.mul_mem (S7C.S43.inv_mem hρc) (hTS (hO _ h))
  set Y := (S7C.S43.comap ρ).map H.subtype with hY
  have hL1TY : S.L1 ⊔ T ≤ Y := sup_le (fun y hy => ⟨⟨y, hL1H hy⟩, hL1S y hy, rfl⟩)
    fun t ht => ⟨⟨t, hd.hTH ht⟩, hTS (hρT _ ht), rfl⟩
  have hker2 : IsPGroup 2 ρ.ker := fun k => by
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 H ⟨((k : ↥H) : G), (hρk k).1 k.2⟩
    refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
    simpa using congrArg Subtype.val hn
  have hYsol : Group.IsSolvable Y := by
    have h1 := L2Case.isSolvable_comap ρ (F1.isSolvable_of_isPGroup_two hker2)
      S7C.isSolvable_S43
    exact Group.isSolvable_of_surjective
      (f := ((S7C.S43.comap ρ).equivMapOfInjective _ H.subtype_injective).toMonoidHom)
      (MulEquiv.surjective _)
  have hYG1 : Y ≤ S.G1 := (Subgroup.map_subtype_le _).trans hd.hH.2.1
  have hYM : Y ≤ Subgroup.normalizer (L : Set G) := h13 G T L V S hd.hS Y hL1TY hYG1 hYsol
  have hYV : Y ≤ Subgroup.normalizer (V : Set G) :=
    (le_inf (Subgroup.map_subtype_le _) hYM).trans (S.inf_M_le_NV h1334 hd.hH)
  have h9 : 9 ∣ Nat.card Y := by
    have h1 : Nat.card Y = Nat.card (S7C.S43.comap ρ) :=
      Subgroup.card_map_of_injective H.subtype_injective
    have h2 : Nat.card S7C.S43 ∣ Nat.card (S7C.S43.comap ρ) := by
      have := Subgroup.card_map_dvd (S7C.S43.comap ρ) ρ
      rwa [Subgroup.map_comap_eq_self_of_surjective hρs] at this
    rw [h1]
    rw [S7C.card_S43] at h2
    exact (by norm_num : 9 ∣ 144).trans h2
  exact S.not_nine_dvd_card h1337 hhat hd.hH (Subgroup.map_subtype_le _) hYV h9

open S7C in
theorem hat_data (hhat : IsHatA6 L) {ρ : ↥H →* Perm (Fin 7)}
    (hρk : ∀ h : ↥H, ρ h = 1 ↔ (h : G) ∈ pCoreOf 2 H) (hρT : ∀ t : ↥H, (t : G) ∈ T → ρ t ∈ T0)
    (hgens : ∀ t ∈ [t1c, t2c, t3c], ∃ s : ↥H, (s : G) ∈ T ∧ ρ s = dec t ∧ (dec t)⁻¹ = dec t)
    (hcube : ∀ (x : G) (hx : x ∈ S.L1), ρ ⟨x, (hd.hL1K.trans hd.hKH) hx⟩ ^ 3 ∈ T0)
    {g : G} (hgL : g ∈ S.L1) :
    ∃ c0 : ↥H, (c0 : G) ∈ S.L1 ∧ (c0 : G) ∈ Subgroup.centralizer (V : Set G) ∧
      ρ c0 ^ 3 = 1 ∧ ρ c0 ≠ 1 ∧
      (∀ t ∈ [t1c, t2c, t3c], ρ c0 * ρ c0 * (dec t * ρ c0 * dec t) ∈ T0 ∨
        ρ c0 * (dec t * ρ c0 * dec t) ∈ T0) ∧
      ρ c0 * ρ ⟨g, (hd.hL1K.trans hd.hKH) hgL⟩ * (ρ c0)⁻¹ *
        (ρ ⟨g, (hd.hL1K.trans hd.hKH) hgL⟩)⁻¹ ∈ T0 ∧
      (ρ c0 * ρ ⟨g, (hd.hL1K.trans hd.hKH) hgL⟩) ^ 3 ∈ T0 ∧
      (ρ c0 * (ρ ⟨g, (hd.hL1K.trans hd.hKH) hgL⟩ * ρ ⟨g, (hd.hL1K.trans hd.hKH) hgL⟩)) ^ 3 ∈
        T0 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hL1H : S.L1 ≤ H := hd.hL1K.trans hd.hKH
  obtain ⟨c0, hc0l0, hc03, hc0O, hdec⟩ := l0_decomp hhat
  have hc0L1 : c0 ∈ S.L1 := S.l0_le_L1 hc0l0
  have hgH : g ∈ H := hL1H hgL
  have hO : pCoreOf 2 (l0 L) ≤ T := pCoreOf_l0_le.trans S.pCoreOf_L_le_T
  have h23 : ∀ y : G, y ^ 3 = 1 → y ∈ pCoreOf 2 (l0 L) → y = 1 := fun y hy3 hy => by
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 (l0 L) ⟨y, hy⟩
    exact A7F.eq_one_of_pow_three hy3 (by simpa using congrArg Subtype.val hn)
  refine ⟨⟨c0, hL1H hc0L1⟩, hc0L1, S.o2Z_le_centralizer (oTwoRes_le _ hc0l0), ?_, ?_, ?_, ?_,
    ?_, ?_⟩
  · rw [← map_pow]
    have : (⟨c0, hL1H hc0L1⟩ : ↥H) ^ 3 = 1 := Subtype.ext (by simpa using hc03)
    rw [this, map_one]
  · intro h1
    obtain ⟨n, hn⟩ := pCoreOf_isPGroup 2 H ⟨c0, (hρk _).1 h1⟩
    have h1' : c0 = 1 := A7F.eq_one_of_pow_three hc03 (by simpa using congrArg Subtype.val hn)
    exact hc0O (h1' ▸ Subgroup.one_mem _)
  · intro t ht
    obtain ⟨s, hsT, hst, hinvt⟩ := hgens t ht
    have hsN : (s : G) ∈ Subgroup.normalizer (l0 L : Set G) :=
      S.normalizer_le_l0 (S.frame.T_le hsT)
    have hx : (s : G) * c0 * (s : G)⁻¹ ∈ l0 L := (Subgroup.mem_normalizer_iff.mp hsN c0).mp hc0l0
    have e : dec t * ρ ⟨c0, hL1H hc0L1⟩ * dec t = ρ (s * ⟨c0, hL1H hc0L1⟩ * s⁻¹) := by
      rw [map_mul, map_mul, map_inv, hst, hinvt]
    rw [e]
    rcases hdec _ hx with h | h | h
    · exfalso
      have hx3 : ((s : G) * c0 * (s : G)⁻¹) ^ 3 = 1 := by
        rw [conj_pow, hc03, mul_one, mul_inv_cancel]
      have h1 := h23 _ hx3 h
      apply hc0O
      have : c0 = 1 := by
        have := congrArg (fun y => (s : G)⁻¹ * y * s) h1
        simpa [mul_assoc] using this
      rw [this]
      exact Subgroup.one_mem _
    · left
      have hm := hρT ⟨_, H.mul_mem (H.mul_mem (hL1H hc0L1) (hL1H hc0L1))
        (H.mul_mem (H.mul_mem s.2 (hL1H hc0L1)) (H.inv_mem s.2))⟩ (hO h)
      have e : (⟨c0 * c0 * ((s : G) * c0 * (s : G)⁻¹), H.mul_mem (H.mul_mem (hL1H hc0L1)
          (hL1H hc0L1)) (H.mul_mem (H.mul_mem s.2 (hL1H hc0L1)) (H.inv_mem s.2))⟩ : ↥H) =
          ⟨c0, hL1H hc0L1⟩ * ⟨c0, hL1H hc0L1⟩ * (s * ⟨c0, hL1H hc0L1⟩ * s⁻¹) := rfl
      rw [e, map_mul, map_mul] at hm
      exact hm
    · right
      have hm := hρT ⟨_, H.mul_mem (hL1H hc0L1)
        (H.mul_mem (H.mul_mem s.2 (hL1H hc0L1)) (H.inv_mem s.2))⟩ (hO h)
      have e : (⟨c0 * ((s : G) * c0 * (s : G)⁻¹), H.mul_mem (hL1H hc0L1)
          (H.mul_mem (H.mul_mem s.2 (hL1H hc0L1)) (H.inv_mem s.2))⟩ : ↥H) =
          ⟨c0, hL1H hc0L1⟩ * (s * ⟨c0, hL1H hc0L1⟩ * s⁻¹) := rfl
      rw [e, map_mul] at hm
      exact hm
  · have hm := hρT ⟨_, H.mul_mem (H.mul_mem (H.mul_mem (hL1H hc0L1) hgH) (H.inv_mem (hL1H hc0L1)))
      (H.inv_mem hgH)⟩ (S.pCoreOf_L_le_T (comm_l0_mem hc0l0 (S.L1_le_L hgL)))
    have e : (⟨c0 * g * c0⁻¹ * g⁻¹, H.mul_mem (H.mul_mem (H.mul_mem (hL1H hc0L1) hgH)
        (H.inv_mem (hL1H hc0L1))) (H.inv_mem hgH)⟩ : ↥H) =
        ⟨c0, hL1H hc0L1⟩ * ⟨g, hgH⟩ * (⟨c0, hL1H hc0L1⟩ : ↥H)⁻¹ * (⟨g, hgH⟩ : ↥H)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at hm
    exact hm
  · have hm := hcube _ (S.L1.mul_mem hc0L1 hgL)
    have e : (⟨c0 * g, hL1H (S.L1.mul_mem hc0L1 hgL)⟩ : ↥H) = ⟨c0, hL1H hc0L1⟩ * ⟨g, hgH⟩ := rfl
    rw [e, map_mul] at hm
    exact hm
  · have hm := hcube _ (S.L1.mul_mem hc0L1 (S.L1.mul_mem hgL hgL))
    have e : (⟨c0 * (g * g), hL1H (S.L1.mul_mem hc0L1 (S.L1.mul_mem hgL hgL))⟩ : ↥H) =
        ⟨c0, hL1H hc0L1⟩ * (⟨g, hgH⟩ * ⟨g, hgH⟩) := rfl
    rw [e, map_mul, map_mul] at hm
    exact hm

end DK

end Setting4

end CFSG.Quasithin.H13.A6
