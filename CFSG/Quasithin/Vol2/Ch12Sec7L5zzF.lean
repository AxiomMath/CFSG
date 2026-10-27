module

public import Certificates.Certificate7255
public import CFSG.Quasithin.Background.SmithC27Star
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
import all CFSG.Quasithin.Vol2.Ch12Sec7L5zz
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzE
import all CFSG.Quasithin.Vol2.Ch12Sec7L5zzE
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zw
public import CFSG.Quasithin.Vol2.Ch12Sec7L5zzC

public section

namespace CFSG.Quasithin.H13.S127.Mod

theorem cert55_stab :
    ∀ c ∈ p1c, c ≠ 0 → (stabC1 c).length ≤ 8 :=
  Certificates.certificate7255.1

theorem cert55_cyc :
    ∀ l ∈ perms6, ∀ b < 7, cycOK b (fl l) = true → cycMoved b (fl l) = true →
      l = List.finRange 6 :=
  Certificates.certificate7255.2

@[expose] def Ecodes : List ℕ := [0, 1, 4, 5, 10, 11, 14, 15, 16, 17, 20, 21, 26, 27, 30, 31]

theorem Ecodes_zero : 0 ∈ Ecodes := by decide

theorem Ecodes_xor : ∀ a ∈ Ecodes, ∀ b ∈ Ecodes, a ^^^ b ∈ Ecodes := by decide

theorem Ecodes_nodup : Ecodes.Nodup := by decide

theorem Ecodes_lt : ∀ c ∈ Ecodes, c < 64 := by decide

theorem Ecodes_length : Ecodes.length = 16 := by decide

theorem Ecodes_split : ∀ c ∈ Ecodes, ∃ a ∈ p1c, ∃ b ∈ wi1, c = a ^^^ b := by decide

theorem p1c_sub_Ecodes : ∀ c ∈ p1c, c ∈ Ecodes := by decide

theorem e8_nodup : e8.Nodup := by decide

theorem e8_length : e8.length = 8 := by decide

theorem e8_fix_E : ∀ B ∈ e8, B ≠ B6.id → (Ecodes.filter fun c => B.app c == c).length ≤ 8 := by
  decide

theorem e8_sum : (e8.toFinset.sum fun B => if B = B6.id then 14 else 8) = 70 := by
  rw [List.sum_toFinset _ e8_nodup]
  decide

theorem p1c_ne_one : ∀ c ∈ p1c, c ≠ 1 := by decide

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.LieType.BorelTits S127 S127.Mod
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem mem_U_of_Ecode
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) (v : ↥V) (hv : C.cd v ∈ Ecodes) :
    (v : G) ∈ U714 T L V z := by
  have h := s.setting.hyp
  obtain ⟨a, ha, b, hb, hab⟩ := Ecodes_split _ hv
  have hva : (C.dc a : G) ∈ U714 T L V z := by
    have h1 : (C.dc a : G) ∈ V1 T L V := by
      rw [V1_eq h hC, C.mem_subG, C.cd_dc a (p1c_lt a ha)]
      exact ha
    exact le_conjClosure _ _ h1
  obtain ⟨c, hc, rfl⟩ := wi1_surj b hb
  obtain ⟨u, huU, huN, hu⟩ := s.exists_U_code h1222 hC hne hT hbig i1_mem_e8
  have hwH : (C.dc c : G) ∈ H714 T L V z := V_le_H714 T L V z (C.dc c).2
  have hUN := s.H_le_normalizer_U h1222 hwH
  have hcomm : u * (C.dc c : G) * u⁻¹ * (C.dc c : G)⁻¹ ∈ U714 T L V z := by
    have h1 : (C.dc c : G) * u⁻¹ * (C.dc c : G)⁻¹ ∈ U714 T L V z :=
      (Subgroup.mem_normalizer_iff.mp hUN u⁻¹).mp (Subgroup.inv_mem _ huU)
    have e : u * (C.dc c : G) * u⁻¹ * (C.dc c : G)⁻¹ =
        u * ((C.dc c : G) * u⁻¹ * (C.dc c : G)⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ huU h1
  set x : ↥V := ⟨u * C.dc c * u⁻¹, (Subgroup.mem_normalizer_iff.1 huN (C.dc c)).1 (C.dc c).2⟩
    with hx
  have hxc : C.cd x = i1.app c := by rw [hx, cd_conj C huN, hu, C.cd_dc c hc]
  have hv' : v = C.dc a * (x * (C.dc c)⁻¹) := by
    apply C.cd_injective
    rw [C.cd_mul, C.cd_mul, C.cd_inv, hxc, C.cd_dc a (p1c_lt a ha), C.cd_dc c hc, hab,
      Nat.xor_comm (i1.app c)]
  rw [hv']
  exact Subgroup.mul_mem _ hva hcomm

theorem mem_U_iff
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) (v : ↥V) :
    (v : G) ∈ U714 T L V z ↔ C.cd v ∈ Ecodes := by
  have h := s.setting.hyp
  set W := U714 T L V z ⊓ V with hWdef
  set E := C.subG Ecodes Ecodes_zero Ecodes_xor with hEdef
  have hEW : E ≤ W := fun x hx => by
    have hxV : x ∈ V := C.subG_le _ _ _ hx
    exact ⟨s.mem_U_of_Ecode h1222 hC hne hT hbig ⟨x, hxV⟩ ((C.mem_subG ⟨x, hxV⟩).1 hx), hxV⟩
  have hE16 : Nat.card E = 16 := by
    rw [C.card_subG Ecodes_nodup Ecodes_lt, Ecodes_length]
  obtain ⟨y, hyL1, hy3⟩ := S127.Mod.idx3_exists (s.relIndex_L1 h1222)
  have hV64 : Nat.card ↥V = 2 ^ 6 := (S127.card_eq_of_1222 h1222 h).2.1
  have hV14 : Nat.card ↥(V1 T L V) = 4 := (S127.Mod.lemma12_7_2_two h1222 h).1.2
  have hV1V : V1 T L V ≤ V := inf_le_left
  have hL1C : L1 T L V ≤ Subgroup.centralizer (V1 T L V : Set G) :=
    (oTwoUpper_le _).trans inf_le_right
  have hV1W : V1 T L V ≤ W := fun v hv => ⟨le_conjClosure _ _ hv, hV1V hv⟩
  have hWV : W ≤ V := inf_le_right
  have hWne : ¬ V ≤ W := fun hle => s.not_le_cTil h1222 (fun x hx =>
    ⟨V_le_H714 T L V z hx, fun u hu => s.comm_mem_U h1222 (hle hx).1 hu⟩)
  have hyH : y ∈ H714 T L V z := (le_sup_left.trans le_sup_right : L1 T L V ≤ _) hyL1
  have hyW : y ∈ Subgroup.normalizer (W : Set G) := by
    refine le_normalizer_of_conj_mem (X := Subgroup.zpowers y) (fun x hx w hw => ?_)
      (Subgroup.mem_zpowers y)
    have hxH : x ∈ H714 T L V z := Subgroup.zpowers_le_of_mem hyH hx
    have hxV : x ∈ Subgroup.normalizer (V : Set G) := Subgroup.zpowers_le_of_mem
      ((S127.Mod.L_le_normalizer h) (((oTwoUpper_le _).trans inf_le_left) hyL1)) hx
    exact ⟨(Subgroup.mem_normalizer_iff.mp (s.H_le_normalizer_U h1222 hxH) w).mp hw.1,
      (Subgroup.mem_normalizer_iff.mp hxV w).mp hw.2⟩
  have hy31 : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
  have hmod := card_modEq_of_fpf hy31
    (fun v hv => (Subgroup.mem_centralizer_iff.mp (hL1C hyL1) v hv).symm) hV1W hyW
    (fun w hw => s.fpf h1222 hyL1 hy3 w (hWV hw))
  rw [hV14] at hmod
  have hd : Nat.card ↥W ∣ 2 ^ 6 := hV64 ▸ Subgroup.card_dvd_of_le hWV
  have h16 : 16 ∣ Nat.card ↥W := hE16 ▸ Subgroup.card_dvd_of_le hEW
  have hne64 : Nat.card ↥W ≠ 2 ^ 6 := fun he =>
    hWne (Subgroup.eq_of_le_of_card_ge hWV (by rw [he, hV64])).ge
  have hW16 : Nat.card ↥W = 16 := by
    obtain ⟨k, hk, hWk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd
    rw [hWk] at hmod h16 hne64 ⊢
    interval_cases k <;> simp_all [Nat.ModEq]
  have hEeq : E = W := Subgroup.eq_of_le_of_card_ge hEW (by rw [hW16, hE16])
  constructor
  · intro hvU
    have hvE : (v : G) ∈ E := hEeq ▸ (⟨hvU, v.2⟩ : (v : G) ∈ W)
    exact (C.mem_subG v).1 hvE
  · exact s.mem_U_of_Ecode h1222 hC hne hT hbig v

theorem card_autOn_U
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) :
    Nat.card ↥(autOn (U714 T L V z) V) = 8 := by
  classical
  set f : ↥(autOn (U714 T L V z) V) → ↥e8.toFinset :=
    fun a => ⟨C.cB a, List.mem_toFinset.2 ((hbig a).1 a.2)⟩ with hf
  have hinj : Function.Injective f := fun a b hab =>
    Subtype.ext (C.cB_injective (congrArg Subtype.val hab))
  have hsurj : Function.Surjective f := by
    rintro ⟨B, hB⟩
    obtain ⟨u, huU, huN, hu⟩ := s.exists_U_code h1222 hC hne hT hbig (List.mem_toFinset.1 hB)
    exact ⟨⟨conjAct V ⟨u, huN⟩, conjAct_mem_autOn huU huN⟩, Subtype.ext hu⟩
  have e := Equiv.ofBijective f ⟨hinj, hsurj⟩
  rw [Nat.card_congr e, Nat.card_eq_finsetCard, List.toFinset_card_of_nodup e8_nodup, e8_length]

theorem U_inf_V_eq
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) :
    U714 T L V z ⊓ V = C.subG Ecodes Ecodes_zero Ecodes_xor :=
  C.eq_subG inf_le_right fun v => ⟨fun h => (s.mem_U_iff h1222 hC hne hT hbig v).1 h.1,
    fun h => ⟨(s.mem_U_iff h1222 hC hne hT hbig v).2 h, v.2⟩⟩

theorem card_U_eq
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8)
    (hCV : Subgroup.centralizer (V : Set G) = V) : Nat.card ↥(U714 T L V z) = 2 ^ 7 := by
  rw [SmithC27.card_eq_card_autOn_mul (s.U_le_normalizer_V h1222), hCV,
    s.card_autOn_U h1222 hC hne hT hbig, s.U_inf_V_eq h1222 hC hne hT hbig,
    C.card_subG Ecodes_nodup Ecodes_lt, Ecodes_length]
  norm_num

theorem ncard_inv_le
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    (hne : s.setting.hyp.hyp.MVbar ≠ autOn L V) (hT : ∀ a ∈ autOn T V, C.cB a ∈ s0p)
    (hbig : ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8)
    (hCV : Subgroup.centralizer (V : Set G) = V) :
    {u : G | u ∈ U714 T L V z ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z}.ncard ≤ 70 := by
  classical
  have h := s.setting.hyp
  have : Fintype G := Fintype.ofFinite G
  have hUN := s.U_le_normalizer_V h1222
  set X : Finset G := Finset.univ.filter fun u => u ∈ U714 T L V z ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z
    with hXdef
  have hXset : {u : G | u ∈ U714 T L V z ∧ u * u = 1 ∧ u ≠ 1 ∧ u ≠ z} = ↑X := by
    ext u
    simp [hXdef]
  rw [hXset, Set.ncard_coe_finset]
  let φ : G → B6 := fun u => if hu : u ∈ Subgroup.normalizer (V : Set G) then
    C.cB (conjAct V ⟨u, hu⟩) else B6.id
  have hφ : ∀ u (hu : u ∈ U714 T L V z), φ u = C.cB (conjAct V ⟨u, hUN hu⟩) := fun u hu => by
    simp only [φ, hUN hu, ↓reduceDIte]
  have hmaps : ∀ u ∈ X, φ u ∈ e8.toFinset := by
    intro u hu
    have huU := (Finset.mem_filter.1 hu).2.1
    rw [List.mem_toFinset, hφ u huU]
    exact (hbig _).1 (conjAct_mem_autOn huU _)
  rw [Finset.card_eq_sum_card_fiberwise hmaps]
  refine (Finset.sum_le_sum fun B hB => ?_).trans e8_sum.le
  have hBe8 : B ∈ e8 := List.mem_toFinset.1 hB
  have hV : ∀ u ∈ U714 T L V z, φ u = B6.id → u ∈ V := by
    intro u hu h1
    rw [hφ u hu] at h1
    have hc : u ∈ Subgroup.centralizer (V : Set G) := (conjAct_eq_one' (hUN hu)).1
      (C.cB_eq_one.1 h1)
    rwa [hCV] at hc
  split_ifs with hBid
  ·
    subst hBid
    have hzV : z ∈ V := s.z_mem_V
    have hzc : C.cd ⟨z, hzV⟩ ∈ p1c := by
      have := s.mem
      rw [V1_eq h hC] at this
      exact (C.mem_subG ⟨z, hzV⟩).1 this
    have hz0 : C.cd ⟨z, hzV⟩ ≠ 0 := fun e =>
      s.ne_one (congrArg Subtype.val (C.cd_eq_zero.1 e))
    let f : G → ℕ := fun u => if hu : u ∈ V then C.cd ⟨u, hu⟩ else 0
    have hinj : Set.InjOn f ↑(X.filter fun u => φ u = B6.id) := by
      intro u hu u' hu' hff
      have hu1 := Finset.mem_filter.1 (Finset.mem_coe.1 hu)
      have hu1' := Finset.mem_filter.1 (Finset.mem_coe.1 hu')
      have huV := hV u (Finset.mem_filter.1 hu1.1).2.1 hu1.2
      have hu'V := hV u' (Finset.mem_filter.1 hu1'.1).2.1 hu1'.2
      simp only [f, huV, hu'V, ↓reduceDIte] at hff
      exact congrArg Subtype.val (C.cd_injective hff)
    have hsub : (X.filter fun u => φ u = B6.id).image f ⊆
        ((Ecodes.toFinset.erase 0).erase (C.cd ⟨z, hzV⟩)) := by
      intro c hc
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hc
      have hu1 := Finset.mem_filter.1 hu
      obtain ⟨huU, -, hu1', huz⟩ := (Finset.mem_filter.1 hu1.1).2
      have huV := hV u huU hu1.2
      simp only [f, huV, ↓reduceDIte]
      refine Finset.mem_erase.2 ⟨fun e => huz ?_, Finset.mem_erase.2 ⟨fun e => hu1' ?_,
        List.mem_toFinset.2 ((s.mem_U_iff h1222 hC hne hT hbig ⟨u, huV⟩).1 huU)⟩⟩
      · exact congrArg Subtype.val (C.cd_injective e)
      · exact congrArg Subtype.val (C.cd_eq_zero.1 e)
    rw [← Finset.card_image_of_injOn hinj]
    refine (Finset.card_le_card hsub).trans ?_
    rw [Finset.card_erase_of_mem, Finset.card_erase_of_mem,
      List.toFinset_card_of_nodup Ecodes_nodup, Ecodes_length]
    · exact List.mem_toFinset.2 (List.mem_of_mem_head? rfl)
    · refine Finset.mem_erase.2 ⟨hz0, List.mem_toFinset.2 (p1c_sub_Ecodes _ hzc)⟩
  ·
    by_cases hne0 : (X.filter fun u => φ u = B).Nonempty
    swap
    · rw [Finset.not_nonempty_iff_eq_empty.1 hne0, Finset.card_empty]
      exact Nat.zero_le _
    obtain ⟨u₀, hu₀⟩ := hne0
    have hu₀' := Finset.mem_filter.1 hu₀
    obtain ⟨hu₀U, hu₀2, -, -⟩ := (Finset.mem_filter.1 hu₀'.1).2
    let f : G → ℕ := fun u => if hu : u₀⁻¹ * u ∈ V then C.cd ⟨u₀⁻¹ * u, hu⟩ else 0
    have hmemV : ∀ u ∈ X.filter (fun u => φ u = B), u₀⁻¹ * u ∈ V := by
      intro u hu
      have hu' := Finset.mem_filter.1 hu
      have huU := (Finset.mem_filter.1 hu'.1).2.1
      refine hV _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₀U) huU) ?_
      have hN : u₀⁻¹ * u ∈ Subgroup.normalizer (V : Set G) :=
        hUN (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₀U) huU)
      have e : (⟨u₀⁻¹ * u, hN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
          (⟨u₀, hUN hu₀U⟩)⁻¹ * ⟨u, hUN huU⟩ := rfl
      have h1 : conjAct V ⟨u₀, hUN hu₀U⟩ = conjAct V ⟨u, hUN huU⟩ :=
        C.cB_injective (by rw [← hφ u₀ hu₀U, ← hφ u huU, hu₀'.2, hu'.2])
      rw [hφ _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₀U) huU), e, map_mul, map_inv, h1,
        inv_mul_cancel, C.cB_one]
    have hinj : Set.InjOn f ↑(X.filter fun u => φ u = B) := by
      intro u hu u' hu' hff
      have h1 := hmemV u (Finset.mem_coe.1 hu)
      have h2 := hmemV u' (Finset.mem_coe.1 hu')
      simp only [f, h1, h2, ↓reduceDIte] at hff
      have := congrArg Subtype.val (C.cd_injective hff)
      simpa using this
    have hsub : (X.filter fun u => φ u = B).image f ⊆
        (Ecodes.filter fun c => B.app c == c).toFinset := by
      intro c hc
      obtain ⟨u, hu, rfl⟩ := Finset.mem_image.1 hc
      have hu' := Finset.mem_filter.1 hu
      obtain ⟨huU, hu2, -, -⟩ := (Finset.mem_filter.1 hu'.1).2
      have heV := hmemV u hu
      simp only [f, heV, ↓reduceDIte]
      set e : G := u₀⁻¹ * u with he
      have heU : e ∈ U714 T L V z := Subgroup.mul_mem _ (Subgroup.inv_mem _ hu₀U) huU
      rw [List.mem_toFinset, List.mem_filter]
      refine ⟨(s.mem_U_iff h1222 hC hne hT hbig ⟨e, heV⟩).1 heU, ?_⟩
      have he2 : e * e = 1 := by
        rw [← pow_two]
        exact S127.sq_eq_one_of_mem h.hyp heV
      have hc : u₀ * e * u₀⁻¹ = e := by
        have hu : u = u₀ * e := by rw [he]; group
        have hinv0 : u₀⁻¹ = u₀ := inv_eq_of_mul_eq_one_right hu₀2
        have hinve : e⁻¹ = e := inv_eq_of_mul_eq_one_right he2
        have h1 : u₀ * e * u₀ * e = 1 := by
          rw [hu] at hu2
          simpa [mul_assoc] using hu2
        calc u₀ * e * u₀⁻¹ = u₀ * e * u₀ := by rw [hinv0]
          _ = e⁻¹ := eq_inv_of_mul_eq_one_left h1
          _ = e := hinve
      have hcode := cd_conj C (hUN hu₀U) ⟨e, heV⟩
      rw [← hφ u₀ hu₀U, hu₀'.2] at hcode
      have h3 : (⟨u₀ * e * u₀⁻¹, (Subgroup.mem_normalizer_iff.1 (hUN hu₀U) e).1 heV⟩ : ↥V) =
          ⟨e, heV⟩ := Subtype.ext hc
      rw [h3] at hcode
      exact beq_iff_eq.2 hcode.symm
    rw [← Finset.card_image_of_injOn hinj]
    refine (Finset.card_le_card hsub).trans ((List.toFinset_card_le _).trans ?_)
    exact e8_fix_E B hBe8 hBid

end CFSG.Quasithin.H13.S127.L715.Set714
