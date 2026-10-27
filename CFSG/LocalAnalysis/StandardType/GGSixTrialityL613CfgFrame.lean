module

public import CFSG.LocalAnalysis.StandardType.GGSixBstarOrthFrameD4Frame
public import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613KGTorus

public section

namespace CFSG.StandardType

namespace L613Cfg

open Module Multiplicative CFSG.StandardType.NoOffOm CFSG.StandardType.Triality
  CFSG.StandardType.D4Rank CFSG.StandardType.OrthD4 CFSG.StandardType.L613KG
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Frame

variable {K : Type} [Field K] [Finite K] [CharP K 2] {G : Type} [Group G]

theorem exists_frame8 {Bs : Subgroup G} (hBs : CFSG.Assembly.IsElemAbelian 3 Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    (h81 : 3 ^ 4 ≤ Nat.card Bs) (φ : Om8 K →* G) (hφ : Function.Injective φ)
    (hBφ : Bs ≤ φ.range) :
    ∃ ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K, Function.Injective (φ.comp ι₁) ∧
      (φ.comp ι₁).range = Bs ∧
      (∀ s s' : Fin 4 → ZMod 3,
        (∀ v, act (ι₁ (ofAdd s')) v = v → act (ι₁ (ofAdd s)) v = v) ↔ SuppLE s s') ∧
      ∀ s : Fin 4 → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (supp s).card = 8 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : NeZero (3 : ℕ) := ⟨by norm_num⟩
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 K (by norm_num)
  have hA := genMax_of_orth hnd hT Nat.prime_three (by norm_num) hBs hSC φ hφ hBφ
  obtain ⟨r, ι₀, hinj₀, hrange₀, hsupp₀⟩ := exists_genPieceFrame hA
  have hι₀A : ∀ s, ι₀ s ∈ (Bs.comap φ).map (matrixDerived (coordinateQuadPlus 4 K)).subtype :=
    fun s => hrange₀ ▸ MonoidHom.mem_range.mpr ⟨s, rfl⟩
  have hι₀Γ : ∀ s, ι₀ s ∈ matrixDerived (coordinateQuadPlus 4 K) := fun s => hA.le (hι₀A s)
  set ι₁ : Multiplicative (Fin r → ZMod 3) →* Om8 K := ι₀.codRestrict _ hι₀Γ with hι₁def
  have hι₁ : ∀ s, ((ι₁ s : Om8 K) : GL (Fin (2 * 4)) K) = ι₀ s := fun s => rfl
  have hinj : Function.Injective (φ.comp ι₁) := fun s t hst =>
    hinj₀ (by rw [← hι₁, ← hι₁, hφ hst])
  have hrange : (φ.comp ι₁).range = Bs := by
    ext b
    constructor
    · rintro ⟨s, rfl⟩
      obtain ⟨Y, hY, hYs⟩ := hι₀A s
      have hYι : Y = ι₁ s := Subtype.ext hYs
      rw [MonoidHom.comp_apply, ← hYι]
      exact hY
    · intro hb
      obtain ⟨Y, rfl⟩ := hBφ hb
      have hYA : (Y : GL (Fin (2 * 4)) K) ∈ ι₀.range := by rw [hrange₀]; exact ⟨Y, hb, rfl⟩
      obtain ⟨s, hs⟩ := hYA
      exact ⟨s, by rw [MonoidHom.comp_apply]; exact congrArg φ (Subtype.ext hs)⟩
  have hr4 : 4 ≤ r := by
    have hcard : Nat.card Bs = 3 ^ r := by
      rw [← hrange]
      exact NoOffUO.card_range_eq hinj
    rw [hcard] at h81
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h81
  set d : (Fin r → ZMod 3) → ℕ := fun s => omFixDim (ι₁ (ofAdd s)) with hd
  have hker : ∀ s v, v ∈ LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ↔
      glin (ι₀ (ofAdd s)) v = v := by
    intro s v
    rw [mem_ker_omRep_sub_one, glin_apply, hι₁]
  have hact : ∀ s v, act (ι₁ (ofAdd s)) v = v ↔ glin (ι₀ (ofAdd s)) v = v :=
    fun s v => mem_ker_iff_act.symm.trans (hker s v)
  have hle8 : ∀ s, d s ≤ 8 := fun s => by
    have := Submodule.finrank_le (LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1))
    rwa [Module.finrank_fin_fun] at this
  have h3 : ∀ s, ι₁ s ^ 3 = 1 := fun s => Subtype.ext (by
    rw [SubgroupClass.coe_pow, hι₁, OneMemClass.coe_one]
    exact hA.pow _ (hι₀A s))
  have heven : ∀ s, Even (d s) := fun s => omFixDim_even _ (h3 _)
  have hlt : ∀ s s', SuppLE s s' → ¬ SuppLE s' s → d s' + 2 ≤ d s := by
    intro s s' h1 h2
    have hle : LinearMap.ker (omRep (ι₁ (ofAdd s')) - 1) ≤
        LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) := by
      intro v hv
      rw [hker] at hv ⊢
      exact (hsupp₀ s s').mpr h1 v hv
    have hne : ¬ LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) ≤
        LinearMap.ker (omRep (ι₁ (ofAdd s')) - 1) := by
      intro h
      apply h2
      refine (hsupp₀ s' s).mp fun v hv => ?_
      rw [← hker] at hv ⊢
      exact h hv
    have hlt' : d s' < d s := Submodule.finrank_lt_finrank_of_lt (lt_of_le_not_ge hle hne)
    obtain ⟨a, ha⟩ := heven s
    obtain ⟨b, hb⟩ := heven s'
    omega
  obtain ⟨hr, hcount⟩ := count_eq d hle8 hlt
  obtain rfl : r = 4 := le_antisymm hr hr4
  refine ⟨ι₁, hinj, hrange, fun s s' => ?_, fun s => hcount le_rfl s⟩
  simp only [hact]
  exact hsupp₀ s s'

end Frame

section Fix

variable {K : Type} [Field K]

theorem act_fix_of_commute {g y : Om8 K} (hgy : g * y = y * g) {v : Fin (2 * 4) → K}
    (hv : act y v = v) : act y (act g v) = act g v := by
  rw [← act_mul, ← hgy, act_mul, hv]

theorem act_comm_of_commute {g y : Om8 K} (hgy : g * y = y * g) (w : Fin (2 * 4) → K) :
    act g (act y w - w) = act y (act g w) - act g w := by
  rw [act_sub, ← act_mul, ← act_mul, hgy]

theorem decomp_fix_comm [CharP K 2] {y : Om8 K} (hy3 : y ^ 3 = 1) (v : Fin (2 * 4) → K) :
    act y (v + act y v + act y (act y v)) = v + act y v + act y (act y v) ∧
      v = (v + act y v + act y (act y v)) + (act y (act y v) - act y v) := by
  refine ⟨?_, ?_⟩
  · rw [act_add, act_add, act_cube hy3]
    abel
  · have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    have hb : act y (act y v) + act y (act y v) = 0 := by
      rw [← two_smul K, h2, zero_smul]
    calc v = v + (act y (act y v) + act y (act y v)) := by rw [hb, add_zero]
      _ = (v + act y v + act y (act y v)) + (act y (act y v) - act y v) := by abel

theorem commute_of_fix [CharP K 2] {y g h : Om8 K} (hy3 : y ^ 3 = 1) (hgy : g * y = y * g)
    (hhy : h * y = y * h) (hg : ∀ w, act g (act y w - w) = act y w - w)
    (hh : ∀ v, act y v = v → act h v = v) : g * h = h * g := by
  refine om8_ext fun v => ?_
  obtain ⟨ha, hv⟩ := decomp_fix_comm hy3 v
  generalize v + act y v + act y (act y v) = a at ha hv
  generalize act y v = w at hv
  subst hv
  have hga : act h (act g a) = act g a := hh _ (act_fix_of_commute hgy ha)
  simp only [act_mul, act_add]
  rw [hh a ha, hg w, hga, act_comm_of_commute hhy w, hg (act h w)]

end Fix

section Disjoint

variable {K : Type} [Field K]

theorem supp_add_of_disjoint {s t : Fin 4 → ZMod 3} (hst : ∀ i, s i ≠ 0 → t i = 0) :
    supp (s + t) = supp s ∪ supp t := by
  ext i
  simp only [mem_supp, Finset.mem_union, Pi.add_apply]
  by_cases hs : s i = 0
  · simp [hs]
  · simp [hs, hst i hs]

theorem card_supp_add_of_disjoint {s t : Fin 4 → ZMod 3} (hst : ∀ i, s i ≠ 0 → t i = 0) :
    (supp (s + t)).card = (supp s).card + (supp t).card := by
  rw [supp_add_of_disjoint hst, Finset.card_union_of_disjoint]
  rw [Finset.disjoint_left]
  intro i hi hi'
  exact (mem_supp.mp hi') (hst i (mem_supp.mp hi))

theorem act_comm_of_disjoint {ι₁ : Multiplicative (Fin 4 → ZMod 3) →* Om8 K}
    (hfr : ∀ s s' : Fin 4 → ZMod 3,
      (∀ v, act (ι₁ (ofAdd s')) v = v → act (ι₁ (ofAdd s)) v = v) ↔ SuppLE s s')
    (hdim : ∀ s : Fin 4 → ZMod 3, omFixDim (ι₁ (ofAdd s)) + 2 * (supp s).card = 8)
    {s t : Fin 4 → ZMod 3} (hst : ∀ i, s i ≠ 0 → t i = 0) (w : Fin (2 * 4) → K) :
    act (ι₁ (ofAdd s)) (act (ι₁ (ofAdd t)) w - w) = act (ι₁ (ofAdd t)) w - w := by
  set Fs := LinearMap.ker (omRep (ι₁ (ofAdd s)) - 1) with hFs
  set Ft := LinearMap.ker (omRep (ι₁ (ofAdd t)) - 1) with hFt
  set Fst := LinearMap.ker (omRep (ι₁ (ofAdd (s + t))) - 1) with hFst
  have hcomm : ι₁ (ofAdd s) * ι₁ (ofAdd t) = ι₁ (ofAdd t) * ι₁ (ofAdd s) := by
    rw [← map_mul ι₁, ← map_mul ι₁, mul_comm (ofAdd s)]
  have hle_s : Fst ≤ Fs := by
    intro v hv
    rw [hFst, mem_ker_iff_act] at hv
    rw [hFs, mem_ker_iff_act]
    refine (hfr s (s + t)).mpr (fun i hi => ?_) v hv
    rw [Pi.add_apply, hst i hi, add_zero]
    exact hi
  have hle_t : Fst ≤ Ft := by
    intro v hv
    rw [hFst, mem_ker_iff_act] at hv
    rw [hFt, mem_ker_iff_act]
    refine (hfr t (s + t)).mpr (fun i hi => ?_) v hv
    have hsi : s i = 0 := by
      by_contra hs
      exact hi (hst i hs)
    rw [Pi.add_apply, hsi, zero_add]
    exact hi
  have hinf : Fs ⊓ Ft = Fst := by
    refine le_antisymm (fun v hv => ?_) (le_inf hle_s hle_t)
    obtain ⟨hvs, hvt⟩ := Submodule.mem_inf.mp hv
    rw [hFs, mem_ker_iff_act] at hvs
    rw [hFt, mem_ker_iff_act] at hvt
    rw [hFst, mem_ker_iff_act, ofAdd_add, map_mul, act_mul, hvt, hvs]
  have hds := hdim s
  have hdt := hdim t
  have hdst := hdim (s + t)
  rw [card_supp_add_of_disjoint hst] at hdst
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq Fs Ft
  rw [hinf] at hsum
  have hfs : finrank K Fs = omFixDim (ι₁ (ofAdd s)) := rfl
  have hft : finrank K Ft = omFixDim (ι₁ (ofAdd t)) := rfl
  have hfst : finrank K Fst = omFixDim (ι₁ (ofAdd (s + t))) := rfl
  have htop : Fs ⊔ Ft = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Module.finrank_fin_fun]
    omega
  have hw : w ∈ Fs ⊔ Ft := by rw [htop]; exact Submodule.mem_top
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
  rw [hFs, mem_ker_iff_act] at ha
  rw [hFt, mem_ker_iff_act] at hb
  have e : act (ι₁ (ofAdd t)) (a + b) - (a + b) = act (ι₁ (ofAdd t)) a - a := by
    rw [act_add, hb]
    abel
  rw [e, act_comm_of_commute hcomm, ha]

end Disjoint

end L613Cfg

end CFSG.StandardType
