module

public import CFSG.Quasithin.H13.U3S1348M
public import CFSG.Quasithin.Background.C124Dict

public section

namespace CFSG.Quasithin.H13.U3

open Subgroup CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.H13.A6 CFSG.LieType.BorelTits

theorem mem_commSub_of_conjAut {W : Type} [CommGroup W] {K : Subgroup (MulAut W)}
    {g : MulAut W} (hgK : B1.conjAut g K = K) {w : W} (hw : w ∈ commSub (⊤ : Subgroup W) K) :
    g w ∈ commSub (⊤ : Subgroup W) K := by
  have h := IsTransvectionBlocks.map_commSub_conjAut K g
  rw [hgK] at h
  rw [← h]
  exact ⟨w, hw, rfl⟩

variable {G : Type} [Group G] [Finite G]

section Module

variable {H VH I : Subgroup G} (hV : IsElemAbelian 2 VH) {J : Subgroup (MulAut (IntMod VH hV))}
  {𝓗 : Finset (Subgroup (MulAut (IntMod VH hV)))} (hb : IsTransvectionBlocks J 𝓗)
  {K : Subgroup (MulAut (IntMod VH hV))} (hK : K ∈ 𝓗)

include hb hK in
theorem s134_card_U : Nat.card ↥(C124.toG hV (commSub (⊤ : Subgroup (IntMod VH hV)) K)) = 4 := by
  unfold C124.toG
  rw [card_map_of_injective (C124.valHom_injective hV), hb.card_comm K hK]

theorem s134_comm_eq_U (hIN : I ≤ normalizer (VH : Set G)) (hIK : autI hV I = K) :
    ⁅VH, I⁆ = C124.toG hV (commSub (⊤ : Subgroup (IntMod VH hV)) K) := by
  rw [commutator_comm, ← C124.toG_commV hV hIN, commV_eq_commSub, hIK]

include hb hK in
theorem s134_exists_I_mul (hIK : autI hV I = K) (hHN : H ≤ normalizer (VH : Set G))
    (hHK : ∀ g ∈ autI hV H, B1.conjAut g K = K) {h : G} (hh : h ∈ H) :
    ∃ i ∈ I, i⁻¹ * h ∈
      centralizer (C124.toG hV (commSub (⊤ : Subgroup (IntMod VH hV)) K) : Set G) := by
  set g := convI hV ⟨h, hHN hh⟩ with hgdef
  have hg : g ∈ autI hV H := convI_mem_autI hV hh (hHN hh)
  obtain ⟨k, hkK, hk⟩ := blk_exists_res hb hK (g := g)
    (fun w hw => mem_commSub_of_conjAut (hHK g hg) hw)
    (fun w hw => mem_commSub_of_conjAut (hHK _ (inv_mem hg)) hw)
  rw [← hIK] at hkK
  obtain ⟨⟨i, hiN⟩, hiI, rfl⟩ := (mem_autI hV).1 hkK
  refine ⟨i, hiI, mem_centralizer_iff.2 fun x hx => ?_⟩
  obtain ⟨w, hw, rfl⟩ := (C124.mem_toG hV).1 hx
  have e := congrArg IntMod.val (hk w hw)
  rw [hgdef, convI_apply_val, convI_apply_val] at e
  have e' : h * w.val * h⁻¹ = i * w.val * i⁻¹ := e
  calc w.val * (i⁻¹ * h) = i⁻¹ * (i * w.val * i⁻¹) * h := by group
    _ = i⁻¹ * (h * w.val * h⁻¹) * h := by rw [e']
    _ = i⁻¹ * h * w.val := by group

include hb hK in
theorem s134_not_mem_U (hIK : autI hV I = K) (hIH : I ≤ H) {z : G}
    (hHz : H ≤ centralizer ({z} : Set G)) (hz1 : z ≠ 1) :
    z ∉ C124.toG hV (commSub (⊤ : Subgroup (IntMod VH hV)) K) := by
  intro hz
  obtain ⟨u, hu, rfl⟩ := (C124.mem_toG hV).1 hz
  have hW : ∀ w : IntMod VH hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨y, hyK, hy3⟩ := exists_orderOf_three_of_card_six (hb.card_eq K hK)
  have hyK' := hyK
  rw [← hIK] at hyK
  obtain ⟨⟨i, hiN⟩, hiI, rfl⟩ := (mem_autI hV).1 hyK
  have hfix : convI hV ⟨i, hiN⟩ u = u := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    have h1 : i * u.val = u.val * i := mem_centralizer_singleton_iff.1 (hHz (hIH hiI))
    show i * u.val * i⁻¹ = u.val
    rw [h1]
    group
  have hy1 := blk_eq_one_of_cube_fix hW hb hK hyK'
    (by rw [← hy3]; exact pow_orderOf_eq_one _) hu
    (fun h => hz1 (by rw [h, IntMod.val_one])) hfix
  rw [hy1, orderOf_one] at hy3
  omega

include hb hK in
theorem s134_exists_U_Z {T : Subgroup G} (hHN : H ≤ normalizer (VH : Set G))
    (hHK : ∀ g ∈ autI hV H, B1.conjAut g K = K) (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hVT : VH ≤ T) :
    ∃ u ∈ C124.toG hV (commSub (⊤ : Subgroup (IntMod VH hV)) K), u ≠ 1 ∧
      u ∈ quasithinOmegaOneCenter T := by
  have hP : IsPGroup 2 ↥(autI hV T) := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hgT, rfl⟩ := (mem_autI hV).1 hφ
    obtain ⟨k, hk⟩ := hT2 ⟨g, hgT⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : g ^ 2 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    simp only [SubmonoidClass.coe_pow, OneMemClass.coe_one]
    rw [← map_pow, h1, map_one]
  obtain ⟨u, hu, hu1, hfix⟩ := exists_fixed_of_isPGroup (hb.card_comm K hK) hP
    (fun p hp w hw => mem_commSub_of_conjAut (hHK p (autI_mono hV hTH hp)) hw)
  refine ⟨u.val, (C124.mem_toG hV).2 ⟨u, hu, rfl⟩,
    fun h => hu1 (IntMod.val_injective (by rw [h]; rfl)), ?_⟩
  refine mem_quasithinOmegaOneCenter_iff.2 ⟨hVT u.val_mem, mem_centralizer_iff.2 fun t ht => ?_,
    hV.2 _ u.val_mem⟩
  have h1 := congrArg IntMod.val (hfix _ (convI_mem_autI hV ht (hHN (hTH ht))))
  rw [convI_apply_val] at h1
  have h1' : t * u.val * t⁻¹ = u.val := h1
  calc t * u.val = (t * u.val * t⁻¹) * t := by group
    _ = u.val * t := by rw [h1']

include hb hK in
theorem s134_eq_one_of_cent_Z {T : Subgroup G} (hHN : H ≤ normalizer (VH : Set G))
    (hHK : ∀ g ∈ autI hV H, B1.conjAut g K = K) (hTH : T ≤ H) (hT2 : IsPGroup 2 T)
    (hVT : VH ≤ T) {g : G} (hgN : g ∈ normalizer (VH : Set G))
    (hgZ : g ∈ centralizer (quasithinOmegaOneCenter T : Set G))
    (hgK : convI hV ⟨g, hgN⟩ ∈ K) (hg3 : (convI hV ⟨g, hgN⟩) ^ 3 = 1) :
    convI hV ⟨g, hgN⟩ = 1 := by
  have hW : ∀ w : IntMod VH hV, w ^ 2 = 1 := fun w => IntMod.sq_eq_one w
  obtain ⟨u, huU, hu1, huZ⟩ := s134_exists_U_Z hV hb hK hHN hHK hTH hT2 hVT
  obtain ⟨w, hw, rfl⟩ := (C124.mem_toG hV).1 huU
  have hfix : convI hV ⟨g, hgN⟩ w = w := by
    apply IntMod.val_injective
    rw [convI_apply_val]
    have h1 : w.val * g = g * w.val := mem_centralizer_iff.1 hgZ _ huZ
    show g * w.val * g⁻¹ = w.val
    rw [← h1]
    group
  exact blk_eq_one_of_cube_fix hW hb hK hgK hg3 hw
    (fun h => hu1 (by rw [h, IntMod.val_one])) hfix

end Module

variable {T L V : Subgroup G}

theorem s134_centralizer_U_le (h1332 : Stmt13_3_2) (hC58 : TheoremC58) (h317 : AS317Sylow)
    (h56 : AsB56) (S : A6.Setting134 G T L V) {z : G} (hz : z ∈ fsuV1 T V)
    (hzL : z ∉ centralizer (L : Set G)) {H VH I : Subgroup G} (hHz : InHz T L V z H)
    (hred : IsTwoReducedIn H VH) {J : Subgroup (MulAut (IntMod VH hred.2.2.1))}
    {𝓗 : Finset (Subgroup (MulAut (IntMod VH hred.2.2.1)))} (hb : IsTransvectionBlocks J 𝓗)
    {K : Subgroup (MulAut (IntMod VH hred.2.2.1))} (hK : K ∈ 𝓗)
    (hIK : autI hred.2.2.1 I = K) (hIH : I ≤ H)
    (hHK : ∀ g ∈ autI hred.2.2.1 H, B1.conjAut g K = K) :
    H ⊓ centralizer
      (C124.toG hred.2.2.1 (commSub (⊤ : Subgroup (IntMod VH hred.2.2.1)) K) : Set G) ≤
      normalizer (L : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set U := C124.toG hred.2.2.1 (commSub (⊤ : Subgroup (IntMod VH hred.2.2.1)) K) with hU
  obtain ⟨hTsyl, -, hHzC, hO2H, hHM⟩ := s134_inHz_facts S hHz
  have hTH : T ≤ H := hTsyl.1
  have hT2 : IsPGroup 2 T := S.h13.sylow.1
  have hVT : VH ≤ T := (le_pCoreOf_of_reduced hred).trans (pCoreOf_two_le_of_isSylowTwoOf hTsyl)
  obtain ⟨u, huU, hu1, huZ⟩ := s134_exists_U_Z hred.2.2.1 hb hK hred.2.1 hHK hTH hT2 hVT
  set Z := quasithinOmegaOneCenter T with hZdef
  set ZL := Z ⊓ centralizer (L : Set G) with hZLdef
  have hzZ : z ∈ Z := (mem_inf.1 hz).2
  have hz1 : z ≠ 1 := fun h => hzL (h ▸ one_mem _)
  have hzU : z ∉ U := s134_not_mem_U hred.2.2.1 hb hK hIK hIH hHzC hz1
  have huz : u ≠ z := fun h => hzU (h ▸ huU)
  have hz2 : z ^ 2 = 1 := (mem_quasithinOmegaOneCenter_iff.1 hzZ).2.2
  have hcard := s134_card_Z h1332 hC58 h317 h56 S ⟨H, ⟨hTH, hO2H⟩, hHM⟩
  have hidx : (ZL.subgroupOf Z).index = 2 := by
    have h1 := (ZL.subgroupOf Z).index_mul_card
    rw [Nat.card_congr (subgroupOfEquivOfLe (inf_le_left : ZL ≤ Z)).toEquiv, hcard] at h1
    have hpos : 0 < Nat.card ↥ZL := Nat.card_pos
    exact Nat.eq_of_mul_eq_mul_right hpos h1
  have hw : ∃ w ∈ ZL, w ≠ 1 ∧ ∀ x ∈ H ⊓ centralizer (U : Set G), x * w = w * x := by
    have hcu : ∀ x ∈ H ⊓ centralizer (U : Set G), x * u = u * x := fun x hx =>
      (mem_centralizer_iff.1 (mem_inf.1 hx).2 u huU).symm
    have hcz : ∀ x ∈ H ⊓ centralizer (U : Set G), x * z = z * x := fun x hx =>
      mem_centralizer_singleton_iff.1 (hHzC (mem_inf.1 hx).1)
    by_cases hu : u ∈ ZL
    · exact ⟨u, hu, hu1, hcu⟩
    by_cases hz' : z ∈ ZL
    · exact ⟨z, hz', hz1, hcz⟩
    have hm := (mul_mem_iff_of_index_two hidx (a := ⟨u, huZ⟩) (b := ⟨z, hzZ⟩)).2 (by
      simp only [mem_subgroupOf]
      exact ⟨fun h => absurd h hu, fun h => absurd h hz'⟩)
    rw [mem_subgroupOf, Subgroup.coe_mul] at hm
    refine ⟨u * z, hm, fun h => huz ?_, fun x hx => ?_⟩
    · calc u = u * z * z := by rw [mul_assoc, ← pow_two, hz2, mul_one]
        _ = z := by rw [h, one_mul]
    · calc x * (u * z) = (x * u) * z := by group
        _ = (u * x) * z := by rw [hcu x hx]
        _ = u * (x * z) := by group
        _ = u * (z * x) := by rw [hcz x hx]
        _ = u * z * x := by group
  obtain ⟨w, hwZL, hw1, hwc⟩ := hw
  obtain ⟨hwZ, hwL⟩ := mem_inf.1 hwZL
  have hwT : w ∈ T := (mem_quasithinOmegaOneCenter_iff.1 hwZ).1
  have hwCT : w ∈ centralizer (T : Set G) := (mem_quasithinOmegaOneCenter_iff.1 hwZ).2.1
  have hcent : ∀ X : Subgroup G, (∀ x ∈ X, x * w = w * x) →
      X ≤ normalizer ((zpowers w : Subgroup G) : Set G) := by
    intro X hX x hx
    refine centralizer_le_normalizer _ (mem_centralizer_iff.2 fun y hy => ?_)
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hy
    exact ((Commute.zpow_right (hX x hx) k).eq).symm
  have hNM := s134_normalizer_le_M S (X := zpowers w)
    (fun h => hw1 (zpowers_eq_bot.1 h))
    (hT2.to_le (zpowers_le.2 hwT))
    (sup_le (hcent L fun x hx => mem_centralizer_iff.1 hwL x hx)
      (hcent T fun x hx => mem_centralizer_iff.1 hwCT x hx))
  exact (hcent _ hwc).trans hNM

end CFSG.Quasithin.H13.U3
