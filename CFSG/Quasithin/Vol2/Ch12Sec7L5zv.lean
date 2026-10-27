module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5w
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch12Sec7Mod10D
public import CFSG.Quasithin.Vol2.Ch12Sec7ModR

public section

namespace CFSG.Quasithin.H13.S127.Mod

@[expose] def e8 : List B6 := r1 ++ r1.map (·.comp i1)

theorem s0p_l1_stable :
    ∀ x ∈ s0p, x ∈ e8 ∨ ∃ g ∈ l1, ∀ x' ∈ s0p, g.comp x ≠ x'.comp g := by decide

theorem s0_l1_stable :
    ∀ x ∈ s0, x ∈ r1 ∨ ∃ g ∈ l1, ∀ x' ∈ s0, g.comp x ≠ x'.comp g := by decide

theorem r1_trans :
    ∀ r ∈ r1, r ≠ B6.id → ∀ r' ∈ r1, r' ≠ B6.id → ∃ g ∈ l1, g.comp r = r'.comp g := by decide

theorem r1i1_trans : ∀ r ∈ r1, r ≠ B6.id → ∀ r' ∈ r1, r' ≠ B6.id →
    ∃ g ∈ l1, g.comp (r.comp i1) = (r'.comp i1).comp g := by decide

theorem r1i1_mul : ∀ r ∈ r1, ∀ r' ∈ r1, (r.comp i1).comp (r'.comp i1) = r.comp r' := by decide

theorem r1_comp_i1 : ∀ r ∈ r1, r.comp (r.comp i1) = i1 := by decide

theorem e8_cases : ∀ x ∈ e8, x = B6.id ∨ x = i1 ∨ (x ∈ r1 ∧ x ≠ B6.id) ∨
    ∃ r ∈ r1, r ≠ B6.id ∧ x = r.comp i1 := by decide

theorem r1_two : ∀ r ∈ r1, r ≠ B6.id → ∃ r' ∈ r1, r' ≠ B6.id ∧ r.comp r' ≠ B6.id := by decide

theorem mem_e8_of_r1 {x : B6} (hx : x ∈ r1) : x ∈ e8 := List.mem_append_left _ hx

theorem comp_i1_mem_e8 {r : B6} (hr : r ∈ r1) : r.comp i1 ∈ e8 :=
  List.mem_append_right _ (List.mem_map.2 ⟨r, hr, rfl⟩)

theorem i1_mem_e8 : i1 ∈ e8 := by decide

theorem e8_r1_or : ∀ x ∈ e8, x ∈ r1 ∨ ∃ r ∈ r1, x = r.comp i1 := by decide

theorem e8_sub_s0p : ∀ x ∈ e8, x ∈ s0p := by decide

end CFSG.Quasithin.H13.S127.Mod

namespace CFSG.Quasithin.H13.S127.L715.Set714

open CFSG.Open CFSG.Blueprint CFSG.Quasithin S127 S127.Mod
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {t z : G} (s : Set714 G T L V t z)
include s

theorem autOn_U_le_T
    (h1222 : Stmt12_2_2) : autOn (U714 T L V z) V ≤ autOn T V :=
  A4.autOn_mono (s.U_le_T h1222).1

theorem conj_mem_autOn_U (h1222 : Stmt12_2_2) {g a : MulAut ↥V}
    (hg : g ∈ autOn (L1 T L V) V) (ha : a ∈ autOn (U714 T L V z) V) :
    g * a * g⁻¹ ∈ autOn (U714 T L V z) V := by
  obtain ⟨l, hlN, hlL, rfl⟩ := mem_autOn'.1 hg
  obtain ⟨u, huN, huU, rfl⟩ := mem_autOn'.1 ha
  have hlH : l ∈ H714 T L V z := (le_sup_left.trans le_sup_right : L1 T L V ≤ _) hlL
  have hm : l * u * l⁻¹ ∈ U714 T L V z :=
    (Subgroup.mem_normalizer_iff.mp (s.H_le_normalizer_U h1222 hlH) u).mp huU
  have hmN : l * u * l⁻¹ ∈ Subgroup.normalizer (V : Set G) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hlN huN) (Subgroup.inv_mem _ hlN)
  refine mem_autOn'.2 ⟨l * u * l⁻¹, hmN, hm, ?_⟩
  have e : (⟨l * u * l⁻¹, hmN⟩ : ↥(Subgroup.normalizer (V : Set G))) =
      ⟨l, hlN⟩ * ⟨u, huN⟩ * ⟨l, hlN⟩⁻¹ := rfl
  rw [e, map_mul, map_mul, map_inv]

theorem autOn_U_ne_bot
    (h1222 : Stmt12_2_2) : autOn (U714 T L V z) V ≠ ⊥ := by
  intro hb
  apply s.not_le_cTil h1222
  intro v hv
  refine ⟨V_le_H714 T L V z hv, fun u hu => ?_⟩
  have huN : u ∈ Subgroup.normalizer (V : Set G) :=
    S127.Mod.T_le_normalizer h1222 s.setting.hyp ((s.U_le_T h1222).1 hu)
  have h1 : conjAct V ⟨u, huN⟩ = 1 := by
    have hm := conjAct_mem_autOn hu huN
    rw [hb, Subgroup.mem_bot] at hm
    exact hm
  have huC := (conjAct_eq_one' huN).1 h1
  have hvu : u * v = v * u := Subgroup.mem_centralizer_iff.mp huC v hv |>.symm
  have e : v * u * v⁻¹ * u⁻¹ = 1 := by
    rw [← hvu]
    group
  rw [e]
  exact Subgroup.one_mem _

theorem exists_conj_code
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    {S : List B6} (hT : ∀ a ∈ autOn T V, C.cB a ∈ S) {a : MulAut ↥V}
    (ha : a ∈ autOn (U714 T L V z) V) {g : B6} (hg : g ∈ l1) :
    ∃ x' ∈ S, g.comp (C.cB a) = x'.comp g := by
  obtain ⟨b, rfl⟩ := hC.1.2 g (l1_sub_gm6 g hg)
  have hbL : b ∈ autOn (L1 T L V) V := (mem_autOn_L1 s.setting.hyp hC b).2 hg
  have hm := s.conj_mem_autOn_U h1222 hbL ha
  refine ⟨C.cB (b * a * b⁻¹), hT _ (s.autOn_U_le_T h1222 hm), ?_⟩
  rw [← C.cB_mul, ← C.cB_mul]
  congr 1
  group

theorem mem_of_conj_code
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    {a b : MulAut ↥V} (ha : a ∈ autOn (U714 T L V z) V) {g : B6} (hg : g ∈ l1)
    (he : g.comp (C.cB a) = (C.cB b).comp g) : b ∈ autOn (U714 T L V z) V := by
  obtain ⟨c, rfl⟩ := hC.1.2 g (l1_sub_gm6 g hg)
  have hcL : c ∈ autOn (L1 T L V) V := (mem_autOn_L1 s.setting.hyp hC c).2 hg
  have hm := s.conj_mem_autOn_U h1222 hcL ha
  have hb : b = c * a * c⁻¹ := by
    apply C.cB_injective
    have h1 : C.cB (c * a) = C.cB (b * c) := by rw [C.cB_mul, C.cB_mul, he]
    have h2 : c * a = b * c := C.cB_injective h1
    rw [show c * a * c⁻¹ = b by rw [h2, mul_inv_cancel_right]]
  rw [hb]
  exact hm

theorem R1_le_of_mem
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L)
    {a : MulAut ↥V} (ha : a ∈ autOn (U714 T L V z) V) (har : C.cB a ∈ r1)
    (ha1 : C.cB a ≠ B6.id) : autOn (R1 T L V) V ≤ autOn (U714 T L V z) V := by
  intro b hb
  have hbr := (mem_autOn_R1_iff h1222 s.setting.hyp hC b).1 hb
  by_cases hb1 : C.cB b = B6.id
  · rw [C.cB_eq_one.1 hb1]
    exact Subgroup.one_mem _
  · obtain ⟨g, hg, he⟩ := r1_trans _ har ha1 _ hbr hb1
    exact s.mem_of_conj_code h1222 hC ha hg he

theorem exists_ne_one_U
    (h1222 : Stmt12_2_2) : ∃ a ∈ autOn (U714 T L V z) V, a ≠ 1 := by
  by_contra hno
  push Not at hno
  exact s.autOn_U_ne_bot h1222 (eq_bot_iff.2 fun a ha => (Subgroup.mem_bot).2 (hno a ha))

theorem exists_R1_code
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2) {C : Coding ↥V} (hC : Std C T L) {r : B6}
    (hr : r ∈ r1) : ∃ ρ ∈ autOn (R1 T L V) V, C.cB ρ = r := by
  obtain ⟨ρ, hρ⟩ := hC.1.2 r (r1_sub r hr).1
  exact ⟨ρ, (mem_autOn_R1_iff h1222 s.setting.hyp hC ρ).2 (hρ ▸ hr), hρ⟩

theorem autOn_U_cases
    [IsMulCommutative ↥V] (h1222 : Stmt12_2_2)
    (hU : autOn (U714 T L V z) V ≠ autOn (R1 T L V) V) :
    s.setting.hyp.hyp.MVbar ≠ autOn L V ∧ ∃ C : Coding ↥V, Std C T L ∧
      (∀ a ∈ autOn T V, C.cB a ∈ s0p) ∧
      ((∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a = B6.id ∨ C.cB a = i1) ∨
        ∀ a, a ∈ autOn (U714 T L V z) V ↔ C.cB a ∈ e8) := by
  have h := s.setting.hyp
  have hne : h.hyp.MVbar ≠ autOn L V := by
    intro heq
    apply hU
    obtain ⟨C, hC⟩ := exists_std h1222 h
    have hT : ∀ a ∈ autOn T V, C.cB a ∈ s0 := by
      intro a ha
      have haM : a ∈ h.hyp.MVbar := A4.autOn_mono (T_le_MV h1222 h) ha
      have haL : a ∈ autOn L V := heq ▸ haM
      have : a ∈ autOn (T ⊓ L) V := autOn_T_inf_L h1222 h ▸ Subgroup.mem_inf.2 ⟨ha, haL⟩
      exact (hC.2 a).1 this
    have hle : autOn (U714 T L V z) V ≤ autOn (R1 T L V) V := by
      intro a ha
      rcases s0_l1_stable _ (hT a (s.autOn_U_le_T h1222 ha)) with hr | ⟨g, hg, hng⟩
      · exact (mem_autOn_R1_iff h1222 h hC a).2 hr
      · obtain ⟨x', hx', he⟩ := s.exists_conj_code h1222 hC hT ha hg
        exact absurd he (hng x' hx')
    obtain ⟨a, ha, ha1⟩ := s.exists_ne_one_U h1222
    have har := (mem_autOn_R1_iff h1222 h hC a).1 (hle ha)
    have hc1 : C.cB a ≠ B6.id := fun he => ha1 (C.cB_eq_one.1 he)
    exact le_antisymm hle (s.R1_le_of_mem h1222 hC ha har hc1)
  refine ⟨hne, ?_⟩
  obtain ⟨C, hC, hT⟩ := exists_coding_T h1222 h hne
  refine ⟨C, hC, hT, ?_⟩
  have he8 : ∀ a ∈ autOn (U714 T L V z) V, C.cB a ∈ e8 := by
    intro a ha
    rcases s0p_l1_stable _ (hT a (s.autOn_U_le_T h1222 ha)) with hr | ⟨g, hg, hng⟩
    · exact hr
    · obtain ⟨x', hx', he⟩ := s.exists_conj_code h1222 hC hT ha hg
      exact absurd he (hng x' hx')
  by_cases hsmall : ∀ a ∈ autOn (U714 T L V z) V, C.cB a = B6.id ∨ C.cB a = i1
  · left
    obtain ⟨a₀, ha₀, ha₀1⟩ := s.exists_ne_one_U h1222
    have hc₀ : C.cB a₀ = i1 :=
      (hsmall a₀ ha₀).resolve_left fun he => ha₀1 (C.cB_eq_one.1 he)
    intro a
    refine ⟨hsmall a, fun hc => ?_⟩
    rcases hc with hc | hc
    · rw [C.cB_eq_one.1 hc]
      exact Subgroup.one_mem _
    · rw [show a = a₀ from C.cB_injective (hc.trans hc₀.symm)]
      exact ha₀
  · right
    push Not at hsmall
    obtain ⟨a, ha, ha1, hai⟩ := hsmall
    have hR : autOn (R1 T L V) V ≤ autOn (U714 T L V z) V := by
      rcases e8_cases _ (he8 a ha) with h1 | h1 | ⟨hr, hr1⟩ | ⟨r, hr, hr1, hx⟩
      · exact absurd h1 ha1
      · exact absurd h1 hai
      · exact s.R1_le_of_mem h1222 hC ha hr hr1
      · obtain ⟨r', hr', hr'1, hrr'⟩ := r1_two r hr hr1
        obtain ⟨g, hg, hge⟩ := r1i1_trans r hr hr1 r' hr' hr'1
        obtain ⟨b, -, hb⟩ := T_surj h1222 h hC hne hT (r'.comp i1)
          (e8_sub_s0p _ (comp_i1_mem_e8 hr'))
        have hbU : b ∈ autOn (U714 T L V z) V :=
          s.mem_of_conj_code h1222 hC ha hg (by rw [hx, hb]; exact hge)
        have hab := Subgroup.mul_mem _ ha hbU
        have hcode : C.cB (a * b) = r.comp r' := by
          rw [C.cB_mul, hx, hb, r1i1_mul r hr r' hr']
        exact s.R1_le_of_mem h1222 hC hab (hcode ▸ r1_closed r hr r' hr') (hcode ▸ hrr')
    obtain ⟨a', ha', ha'R⟩ : ∃ a' ∈ autOn (U714 T L V z) V, a' ∉ autOn (R1 T L V) V := by
      by_contra hno
      push Not at hno
      exact hU (le_antisymm hno hR)
    have ha'c : C.cB a' ∉ r1 := fun h' => ha'R ((mem_autOn_R1_iff h1222 h hC a').2 h')
    obtain ⟨r₀, hr₀, hr₀e⟩ := (e8_r1_or _ (he8 a' ha')).resolve_left ha'c
    obtain ⟨ρ, hρR, hρ⟩ := s.exists_R1_code h1222 hC hr₀
    have hi : ρ * a' ∈ autOn (U714 T L V z) V := Subgroup.mul_mem _ (hR hρR) ha'
    have hic : C.cB (ρ * a') = i1 := by rw [C.cB_mul, hρ, hr₀e, r1_comp_i1 r₀ hr₀]
    intro x
    refine ⟨he8 x, fun hx => ?_⟩
    rcases e8_r1_or _ hx with hxr | ⟨r, hr, hxe⟩
    · exact hR ((mem_autOn_R1_iff h1222 h hC x).2 hxr)
    · obtain ⟨ρ', hρ'R, hρ'⟩ := s.exists_R1_code h1222 hC hr
      have hxx : x = ρ' * (ρ * a') := C.cB_injective (by rw [hxe, C.cB_mul, hρ', hic])
      rw [hxx]
      exact Subgroup.mul_mem _ (hR hρ'R) hi

end CFSG.Quasithin.H13.S127.L715.Set714
