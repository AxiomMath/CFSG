module

public import CFSG.Quasithin.H13.L32NLem1447d
public import CFSG.Quasithin.Background.G25Direct
public import CFSG.Quasithin.Vol2.GoldschmidtL128Four3

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin

namespace L144B.Base

open L1447

variable {G : Type} [Group G] [Finite G] {T L V V₂ : Subgroup G} {g : G}

section

variable (C : Base G T L V V₂ g)
include C

theorem hyp25 (h12213 : Stmt12_2_13) :
    AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V) :=
  (lemma12_8_8_four_of C.h1222 h12213 G T L V 3 (fsuV1 T V) V₂ C.s1282 le_rfl).2

theorem comm_U_mem (hF1 : F1 T V V₂) (hF2 : F2 T V V₂ g) {d : G} (hd : d ∈ dG T V g) {u : G}
    (hu : u ∈ fsuU T V) : u * d * u⁻¹ * d⁻¹ ∈ fsuV1 T V := by
  have hQ := C.dG_le_Q hF1 hF2 hd
  rw [← C.cHat] at hQ
  have h1 : d * u * d⁻¹ * u⁻¹ ∈ fsuV1 T V := C.zU ▸ hQ.2.2 u hu
  have := Subgroup.inv_mem _ h1
  simpa [mul_assoc] using this

theorem exists_st (h12213 : Stmt12_2_13) :
    Nonempty (L3Setting 1 V (fsuV1 T V) L T (l32nH T V)) := by
  obtain ⟨D⟩ := (C.hyp25 h12213).natural.nonempty_data
  exact ⟨⟨C.hyp25 h12213, D⟩⟩

end

namespace Frame

variable {C : Base G T L V V₂ g} (F : Frame C)
include F

abbrev iG : Subgroup G :=
  fsuU T V ⊔ rconj (fsuU T V) F.g₁ ⊔ rconj (fsuU T V) F.l⁻¹

theorem I_eq (h12213 : Stmt12_2_13) : F.iG = L ⊔ fsuU T V :=
  (C.hyp25 h12213).G25_two F.hg₁ (inv_mem F.hl) F.hV

theorem l_mem_Hg : F.l ∈ CFSG.conjugate (l32nH T V) g := C.mem_Hg_of_fix F.hz F.hz1 F.lp

theorem Ug₁ : rconj (fsuU T V) F.g₁ = CFSG.conjugate (fsuU T V) g := C.rconj_U_eq F.hz F.hz1 F.g₁z

theorem I_le_NV (h12213 : Stmt12_2_13) : F.iG ≤ Subgroup.normalizer (V : Set G) := by
  obtain ⟨_, S⟩ := C.set14
  rw [F.I_eq h12213]
  exact sup_le S.LV (C.UT.trans S.TV)

theorem comm_mem_V (hF1 : F1 T V V₂) (hF2 : F2 T V V₂ g) {d : G}
    (hd : d ∈ dG T V g) {x : G} (hx : x ∈ F.iG) : x * d * x⁻¹ * d⁻¹ ∈ V := by
  obtain ⟨_, S⟩ := C.set14
  let Y : Subgroup G :=
    { carrier := {x | x ∈ Subgroup.normalizer (V : Set G) ∧ x * d * x⁻¹ * d⁻¹ ∈ V}
      one_mem' := ⟨one_mem _, by simp⟩
      mul_mem' := by
        rintro x y ⟨hx, hx'⟩ ⟨hy, hy'⟩
        refine ⟨mul_mem hx hy, ?_⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp hx _).mp hy'
        have e : x * y * d * (x * y)⁻¹ * d⁻¹ =
            x * (y * d * y⁻¹ * d⁻¹) * x⁻¹ * (x * d * x⁻¹ * d⁻¹) := by group
        rw [e]
        exact mul_mem h1 hx'
      inv_mem' := by
        rintro x ⟨hx, hx'⟩
        refine ⟨inv_mem hx, ?_⟩
        have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hx) _).mp (inv_mem hx')
        have e : x⁻¹ * d * x⁻¹⁻¹ * d⁻¹ = x⁻¹ * (x * d * x⁻¹ * d⁻¹)⁻¹ * x⁻¹⁻¹ := by group
        rw [e]
        exact h1 }
  have hUN : fsuU T V ≤ Subgroup.normalizer (V : Set G) := C.UT.trans S.TV
  have hUY : fsuU T V ≤ Y := fun u hu =>
    ⟨hUN hu, (Subgroup.mem_inf.mp (C.comm_U_mem hF1 hF2 hd hu)).1⟩
  have hUgY : rconj (fsuU T V) F.g₁ ≤ Y := by
    rw [F.Ug₁]
    intro x hx
    refine ⟨?_, ?_⟩
    · have h1 := hUN (mem_conj.mp hx)
      have := mul_mem (mul_mem (inv_mem C.gV) h1) C.gV
      simpa [mul_assoc] using this
    · have := Subgroup.mem_centralizer_iff.mp hd.2 x hx
      rw [this]
      simp
  have hUlY : rconj (fsuU T V) F.l⁻¹ ≤ Y := by
    intro x hx
    have hu : F.l⁻¹ * x * F.l⁻¹⁻¹ ∈ fsuU T V := mem_rconj.mp hx
    have hlN : F.l ∈ Subgroup.normalizer (V : Set G) := S.LV F.hl
    have hd' : F.l⁻¹ * d * F.l⁻¹⁻¹ ∈ dG T V g := dG_normal (inv_mem F.l_mem_Hg) hd
    refine ⟨?_, ?_⟩
    · have := mul_mem (mul_mem hlN (hUN hu)) (inv_mem hlN)
      simpa [mul_assoc] using this
    · have h1 := (Subgroup.mem_inf.mp (C.comm_U_mem hF1 hF2 hd' hu)).1
      have h2 := (Subgroup.mem_normalizer_iff.mp hlN _).mp h1
      have e : x * d * x⁻¹ * d⁻¹ = F.l * ((F.l⁻¹ * x * F.l⁻¹⁻¹) * (F.l⁻¹ * d * F.l⁻¹⁻¹) *
          (F.l⁻¹ * x * F.l⁻¹⁻¹)⁻¹ * (F.l⁻¹ * d * F.l⁻¹⁻¹)⁻¹) * F.l⁻¹ := by group
      rw [e]
      exact h2
  exact (sup_le (sup_le hUY hUgY) hUlY hx).2

theorem O2_comm_V (h12213 : Stmt12_2_13) {y : G} (hy : y ∈ pCoreOf 2 F.iG) {v : G} (hv : v ∈ V) :
    y * v * y⁻¹ = v := by
  obtain ⟨St⟩ := C.exists_st h12213
  rw [F.I_eq h12213] at hy
  exact St.O_centralizes_V y (St.sxFacts.2.1 hy) v hv

theorem O2_comm (h12213 : Stmt12_2_13) (hF1 : F1 T V V₂) (hF2 : F2 T V V₂ g) {d : G}
    (hd : d ∈ dG T V g) {y : G} (hy : y ∈ pCoreOf 2 F.iG) : y * d = d * y := by
  have hdec := ((C.hyp25 h12213).G25_direct (U := fsuU T V) (I := F.iG)
    (S := pCoreOf 2 F.iG) (W := fsuU T V ⊓ pCoreOf 2 F.iG) rfl F.hg₁ (inv_mem F.hl) F.hV rfl rfl
    rfl).1
  have hWW : ∀ x ∈ fsuU T V ⊓ pCoreOf 2 F.iG, x ∈ l32nW T V V₂ := fun x hx =>
    ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun v hv => by
      have := F.O2_comm_V h12213 hx.2 (C.plane.1.1 hv)
      calc v * x = x * v * x⁻¹ * x := by rw [this]
        _ = x * v := by group⟩
  have hC : pCoreOf 2 F.iG ≤ Subgroup.centralizer ({d} : Set G) := by
    rw [hdec]
    refine sup_le (sup_le (fun x hx => ?_) (fun x hx => ?_)) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_singleton_iff]
      exact (C.dG_comm_W hF1 hF2 hd (hWW x hx)).symm
    · have hxU : x ∈ CFSG.conjugate (fsuU T V) g := by
        rw [← F.Ug₁]
        exact mem_rconj.mpr (Subgroup.mem_inf.mp (mem_rconj.mp hx)).1
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subgroup.mem_centralizer_iff.mp hd.2 x hxU
    · have hw : F.l⁻¹ * x * F.l⁻¹⁻¹ ∈ l32nW T V V₂ := hWW _ (mem_rconj.mp hx)
      have hd' : F.l⁻¹ * d * F.l⁻¹⁻¹ ∈ dG T V g := dG_normal (inv_mem F.l_mem_Hg) hd
      have hc := C.dG_comm_W hF1 hF2 hd' hw
      rw [Subgroup.mem_centralizer_singleton_iff]
      refine (?_ : d * x = x * d).symm
      calc d * x = F.l * ((F.l⁻¹ * d * F.l⁻¹⁻¹) * (F.l⁻¹ * x * F.l⁻¹⁻¹)) * F.l⁻¹ := by group
        _ = F.l * ((F.l⁻¹ * x * F.l⁻¹⁻¹) * (F.l⁻¹ * d * F.l⁻¹⁻¹)) * F.l⁻¹ := by rw [hc]
        _ = x * d := by group
  exact Subgroup.mem_centralizer_singleton_iff.mp (hC hy)

theorem mem_O2_of_cent (h12213 : Stmt12_2_13) {x : G} (hx : x ∈ F.iG)
    (hxV : ∀ v ∈ V, x * v * x⁻¹ = v) : x ∈ pCoreOf 2 F.iG := by
  obtain ⟨_, S⟩ := C.set14
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hIN := F.I_le_NV h12213
  have hILT : F.iG ≤ L ⊔ T := by
    rw [F.I_eq h12213]
    exact sup_le le_sup_left (C.UT.trans le_sup_right)
  set N : Subgroup G := F.iG ⊓ Subgroup.centralizer (V : Set G) with hN
  have hNI : N ≤ F.iG := inf_le_left
  have key : ∀ y ∈ F.iG, ∀ n ∈ N, y * n * y⁻¹ ∈ N := by
    intro y hy n hn
    obtain ⟨hn1, hn2⟩ := Subgroup.mem_inf.mp hn
    refine Subgroup.mem_inf.mpr ⟨F.iG.mul_mem (F.iG.mul_mem hy hn1) (F.iG.inv_mem hy),
      Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hk : y⁻¹ * v * y⁻¹⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (inv_mem (hIN hy)) v).mp hv
    have hc := Subgroup.mem_centralizer_iff.mp hn2 _ hk
    calc v * (y * n * y⁻¹) = y * ((y⁻¹ * v * y⁻¹⁻¹) * n) * y⁻¹ := by group
      _ = y * (n * (y⁻¹ * v * y⁻¹⁻¹)) * y⁻¹ := by rw [hc]
      _ = y * n * y⁻¹ * v := by group
  have hnorm : (N.subgroupOf F.iG).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNI).mpr fun y hy => ?_
    refine Subgroup.mem_normalizer_iff.mpr fun n => ⟨fun hn => key y hy n hn, fun hn => ?_⟩
    have := key _ (inv_mem hy) _ hn
    simpa [mul_assoc] using this
  have hp : IsPGroup 2 N := S.isPGroup_cent_sup.to_le (inf_le_inf_right _ hILT)
  refine CFSG.LieType.BorelTits.le_pCoreOf 2 hNI hnorm hp ⟨hx, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
  calc v * x = x * v * x⁻¹ * x := by rw [hxV v hv]
    _ = x * v := by group

end Frame

end L144B.Base

end CFSG.Quasithin.H13
