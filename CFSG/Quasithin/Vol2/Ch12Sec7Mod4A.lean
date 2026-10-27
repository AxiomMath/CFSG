module

public import CFSG.Quasithin.Vol2.Ch12Sec7ModCert2
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData
import all CFSG.Quasithin.Vol2.Ch12Sec7ModData2
public import CFSG.Quasithin.Vol2.Ch12Sec7ModL
public import CFSG.Quasithin.Vol2.Ch12Sec7ModS

public section

namespace CFSG.Quasithin.H13.S127.Mod

open CFSG.Open CFSG.Blueprint CFSG.Quasithin
open scoped IsMulCommutative

theorem pt1_zero : 0 ∈ pt1 := by decide

theorem pt1_xor : ∀ a ∈ pt1, ∀ b ∈ pt1, a ^^^ b ∈ pt1 := by decide

theorem pt1_nodup : pt1.Nodup := by decide

theorem pt1_lt : ∀ c ∈ pt1, c < 64 := by decide

theorem zs6_presv_pt1 : ∀ z ∈ zs6, ∀ c ∈ pt1, z.app c ∈ pt1 := by decide

theorem w6_one : w6.app 1 = 2 := by decide

theorem mem_pt1_iff : ∀ c < 64, c ∈ pt1 ↔ c = 0 ∨ c = 1 ∨ c = 2 ∨ c = 3 := by decide

theorem one_xor_two : (1 : ℕ) ^^^ 2 = 3 := by decide

theorem p1c_lt' : ∀ c ∈ p1c, c < 64 := by decide

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} [IsMulCommutative ↥V]

theorem mem_autOn_inf_normalizer {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) {l : List ℕ} {h0 : 0 ∈ l} {hx : ∀ a ∈ l, ∀ b ∈ l, a ^^^ b ∈ l}
    (hl : ∀ c ∈ l, c < 64) (a : MulAut ↥V) :
    a ∈ autOn (L ⊓ Subgroup.normalizer (C.subG l h0 hx : Set G)) V ↔
      C.cB a ∈ gm6 ∧ presv l (C.cB a) = true := by
  rw [presv_iff]
  constructor
  · intro ha
    obtain ⟨x, hxN, hxP, rfl⟩ := mem_autOn'.1 ha
    obtain ⟨hxL, hxW⟩ := Subgroup.mem_inf.1 hxP
    refine ⟨(hC.1 _).1 (conjAct_mem_autOn hxL hxN), fun c hc => ?_⟩
    have hw := (C.mem_subG (h0 := h0) (hx := hx) (C.dc c)).2 (by rw [C.cd_dc c (hl c hc)]; exact hc)
    have hw' := (Subgroup.mem_normalizer_iff.1 hxW _).1 hw
    have hv := (C.mem_subG (h0 := h0) (hx := hx)
      ⟨_, (Subgroup.mem_normalizer_iff.1 hxN _).1 (C.dc c).2⟩).1 hw'
    rw [cd_conj C hxN (C.dc c), C.cd_dc c (hl c hc)] at hv
    exact hv
  · rintro ⟨hgm, hpres⟩
    obtain ⟨y, hyN, hyL, rfl⟩ := mem_autOn'.1 ((hC.1 _).2 hgm)
    refine conjAct_mem_autOn (Subgroup.mem_inf.2 ⟨hyL, ?_⟩) hyN
    apply normalizer_of_maps
    intro w hw
    obtain ⟨hwV, hwl⟩ := hw
    have hm := (Subgroup.mem_normalizer_iff.1 hyN w).1 hwV
    have e : C.cd ⟨y * w * y⁻¹, hm⟩ = (C.cB (conjAct V ⟨y, hyN⟩)).app (C.cd ⟨w, hwV⟩) :=
      cd_conj C hyN ⟨w, hwV⟩
    exact ⟨hm, by rw [e]; exact hpres _ hwl⟩

omit [Finite G] in
theorem mem_autOn_inf_centralizer {C : Coding ↥V}
    (hC : IdentL C (autOn L V)) (v : ↥V) (a : MulAut ↥V) :
    a ∈ autOn (L ⊓ Subgroup.centralizer ({(v : G)} : Set G)) V ↔
      C.cB a ∈ gm6 ∧ (C.cB a).app (C.cd v) = C.cd v := by
  constructor
  · intro ha
    obtain ⟨x, hxN, hxP, rfl⟩ := mem_autOn'.1 ha
    obtain ⟨hxL, hxc⟩ := Subgroup.mem_inf.1 hxP
    refine ⟨(hC.1 _).1 (conjAct_mem_autOn hxL hxN), ?_⟩
    exact (commute_iff_code C hxN v).1 (Subgroup.mem_centralizer_singleton_iff.1 hxc)
  · rintro ⟨hgm, hfix⟩
    obtain ⟨y, hyN, hyL, rfl⟩ := mem_autOn'.1 ((hC.1 _).2 hgm)
    refine conjAct_mem_autOn (Subgroup.mem_inf.2 ⟨hyL, ?_⟩) hyN
    exact Subgroup.mem_centralizer_singleton_iff.2 ((commute_iff_code C hyN v).2 hfix)

omit [Finite G] [IsMulCommutative ↥V] in
theorem t_ne_one {t : G} (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18) :
    t ≠ 1 :=
  ne_one_of_relIndex h18 (by decide)

theorem cd_t_mem_oVecL
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V}
    (hC : Std C T L) {t : G} (ht : t ∈ V)
    (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18) : C.cd ⟨t, ht⟩ ∈ oVecL := by
  by_contra hno
  obtain ⟨z, hzV₁, hz1, -, -, -, -, h45, -, -⟩ := lemma12_7_4_part1_of h1222 h
  have hzV : z ∈ V := (inf_le_left : V1 T L V ≤ V) hzV₁
  have hzc : C.cd ⟨z, hzV⟩ ∈ p1c := by
    have := hzV₁
    rw [V1_eq h hC] at this
    exact (C.mem_subG ⟨z, hzV⟩).1 this
  have hz0 : C.cd ⟨z, hzV⟩ ≠ 0 := fun e => hz1 (congrArg Subtype.val (C.cd_eq_zero.1 e))
  have ht0 : C.cd ⟨t, ht⟩ ≠ 0 := fun e => t_ne_one h18 (congrArg Subtype.val (C.cd_eq_zero.1 e))
  obtain ⟨g, hg, hgt⟩ := cert4_off_trans _ (List.mem_range.2 (C.cd_lt _)) ht0 hno _ hzc hz0
  obtain ⟨a, rfl⟩ := hC.1.2 g hg
  obtain ⟨x, hx, hxL, rfl⟩ := mem_autOn'.1 ((hC.1.1 _).2 hg)
  have hxt : x * t * x⁻¹ = z := by
    have e := cd_conj C hx ⟨t, ht⟩
    rw [hgt] at e
    exact congrArg Subtype.val (C.cd_injective e)
  have h45' := h45
  rw [← hxt, relIndex_centralizer_conj hxL, h18] at h45'
  exact absurd h45' (by norm_num)

theorem exists_coding_t
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {t : G}
    (ht : t ∈ V) (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18) :
    ∃ C : Coding ↥V, IdentL C (autOn L V) ∧ C.cd ⟨t, ht⟩ = 1 := by
  obtain ⟨C, hC⟩ := exists_std h1222 h
  obtain ⟨g, hg, hg1⟩ := cert4_hyp_trans _ (cd_t_mem_oVecL h1222 h hC ht h18)
  obtain ⟨b, rfl⟩ := hC.1.2 g hg
  refine ⟨C.recode b, hC.1.recode ((hC.1.1 b).2 hg), ?_⟩
  rw [C.recode_cd, C.cd_apply, hg1]

theorem Vt_eq
    (h1222 : Stmt12_2_2) (h : Hyp1271 G T L V) {C : Coding ↥V} (hC : IdentL C (autOn L V))
    {t : G} (ht : t ∈ V) (h1 : C.cd ⟨t, ht⟩ = 1) :
    Vt L t = C.subG pt1 pt1_zero pt1_xor := by
  have hXN := XOf_le_normalizer_subG h1222 h hC (l := pt1) (h0 := pt1_zero) (hx := pt1_xor)
    zs6_presv_pt1
  have htS : t ∈ C.subG pt1 pt1_zero pt1_xor :=
    (C.mem_subG ⟨t, ht⟩).2 (by rw [h1]; decide)
  apply le_antisymm
  · rw [Vt, conjClosure, Subgroup.closure_le]
    rintro _ ⟨x, hx, y, hy, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (Subgroup.mem_normalizer_iff.1 (hXN hx) _).1 (Subgroup.zpow_mem _ htS n)
  ·
    obtain ⟨w, hw⟩ := hC.2 w6 w6_gm6
    have hwX : w ∈ autOn (XOf L) V := (mem_autOn_XOf h1222 h hC w).2 (by rw [hw]; decide)
    obtain ⟨x, hxN, hxX, rfl⟩ := mem_autOn'.1 hwX
    have hxt : x * t * x⁻¹ ∈ Vt L t :=
      Subgroup.subset_closure ⟨x, hxX, t, Subgroup.mem_zpowers t, rfl⟩
    have htV : t ∈ Vt L t :=
      Subgroup.subset_closure ⟨1, (XOf L).one_mem, t, Subgroup.mem_zpowers t, by group⟩
    have hc2 : C.cd ⟨x * t * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN t).1 ht⟩ = 2 := by
      rw [cd_conj C hxN ⟨t, ht⟩, hw, h1, w6_one]
    intro g hg
    obtain ⟨hgV, hgc⟩ := hg
    rcases (mem_pt1_iff _ (C.cd_lt _)).1 hgc with e | e | e | e
    · have : (⟨g, hgV⟩ : ↥V) = 1 := C.cd_eq_zero.1 e
      rw [show g = 1 from congrArg Subtype.val this]
      exact (Vt L t).one_mem
    · have : (⟨g, hgV⟩ : ↥V) = ⟨t, ht⟩ := C.cd_injective (by rw [e, h1])
      rw [show g = t from congrArg Subtype.val this]
      exact htV
    · have : (⟨g, hgV⟩ : ↥V) = ⟨x * t * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN t).1 ht⟩ :=
        C.cd_injective (by rw [e, hc2])
      rw [show g = x * t * x⁻¹ from congrArg Subtype.val this]
      exact hxt
    · have : (⟨g, hgV⟩ : ↥V) =
          ⟨t, ht⟩ * ⟨x * t * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN t).1 ht⟩ :=
        C.cd_injective (by rw [e, C.cd_mul, h1, hc2, one_xor_two])
      rw [show g = t * (x * t * x⁻¹) from congrArg Subtype.val this]
      exact (Vt L t).mul_mem htV hxt

end CFSG.Quasithin.H13.S127.Mod

end
