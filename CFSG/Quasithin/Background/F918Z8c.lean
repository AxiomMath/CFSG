module

public import CFSG.Quasithin.Background.F918Z8Def2
public import CFSG.Quasithin.EmptyFaithful.S153ZQ
public import CFSG.Quasithin.Background.F918P2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

theorem d391ll_perfect_sup {G : Type*} [Group G] {L Lt : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hLt : ⁅Lt, Lt⁆ = Lt) : ⁅L ⊔ Lt, L ⊔ Lt⁆ = L ⊔ Lt := by
  refine le_antisymm ?_ (sup_le ?_ ?_)
  · rw [Subgroup.commutator_le]
    intro a ha b hb
    rw [commutatorElement_def]
    exact (L ⊔ Lt).mul_mem ((L ⊔ Lt).mul_mem ((L ⊔ Lt).mul_mem ha hb) ((L ⊔ Lt).inv_mem ha))
      ((L ⊔ Lt).inv_mem hb)
  · calc L = ⁅L, L⁆ := hL.symm
      _ ≤ ⁅L ⊔ Lt, L ⊔ Lt⁆ := Subgroup.commutator_mono le_sup_left le_sup_left
  · calc Lt = ⁅Lt, Lt⁆ := hLt.symm
      _ ≤ ⁅L ⊔ Lt, L ⊔ Lt⁆ := Subgroup.commutator_mono le_sup_right le_sup_right

theorem d391ll_centralizes_of_mem_kernel {G : Type*} [Group G] {L C : Subgroup G}
    (hq : CFSG.IsQuasisimple ↥L) (hLC : ¬ L ≤ C) (hCn : ∀ g ∈ L, ∀ c ∈ C, g * c * g⁻¹ ∈ C)
    {k : G} (hk : k ∈ C) (hkn : ∀ x ∈ L, k * x * k⁻¹ ∈ L) : ∀ x ∈ L, k * x = x * k := by
  have hperf : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hq.1
    exact Subgroup.commutator_eq_self
  have hKn : (C.subgroupOf L).Normal := by
    refine ⟨fun c hc g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hc ⊢
    simpa using hCn g g.2 c hc
  have hKc : C.subgroupOf L ≤ Subgroup.center ↥L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hKn with h | h
    · exfalso
      apply hLC
      intro l hl
      have : (⟨l, hl⟩ : ↥L) ∈ C.subgroupOf L := by rw [h]; trivial
      exact this
    · exact h
  have hcentral : ∀ z ∈ L ⊓ C, ∀ l ∈ L, z * l = l * z := by
    intro z hz l hl
    have hz' : (⟨z, hz.1⟩ : ↥L) ∈ C.subgroupOf L := hz.2
    have := Subgroup.mem_center_iff.mp (hKc hz') ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  refine B5.commute_of_comm_central hperf hkn hcentral fun x hx => ⟨?_, ?_⟩
  · have h1 := hkn x hx
    rw [commutatorElement_def]
    exact L.mul_mem h1 (L.inv_mem hx)
  · have h1 : x * k⁻¹ * x⁻¹ ∈ C := hCn x hx k⁻¹ (C.inv_mem hk)
    have h2 : ⁅k, x⁆ = k * (x * k⁻¹ * x⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact C.mul_mem hk h1

theorem d391ll_kernel_central {G : Type*} [Group G] {L Lt Mp C : Subgroup G}
    (hMp : Mp = L ⊔ Lt) (hq : CFSG.IsQuasisimple ↥L) (hqt : CFSG.IsQuasisimple ↥Lt)
    (hcomm : ∀ x ∈ L, ∀ y ∈ Lt, x * y = y * x) (hCn : ∀ g ∈ Mp, ∀ c ∈ C, g * c * g⁻¹ ∈ C)
    (hLC : ¬ L ≤ C) (hLtC : ¬ Lt ≤ C) : ∀ k ∈ Mp ⊓ C, ∀ x ∈ Mp, k * x = x * k := by
  subst hMp
  intro k hk
  have hnL : L ⊔ Lt ≤ Subgroup.normalizer (L : Set G) := by
    refine sup_le Subgroup.le_normalizer fun y hy => Subgroup.centralizer_le_normalizer _ ?_
    exact Subgroup.mem_centralizer_iff.2 fun x hx => hcomm x hx y hy
  have hnLt : L ⊔ Lt ≤ Subgroup.normalizer (Lt : Set G) := by
    refine sup_le (fun x hx => Subgroup.centralizer_le_normalizer _ ?_) Subgroup.le_normalizer
    exact Subgroup.mem_centralizer_iff.2 fun y hy => (hcomm x hx y hy).symm
  have hk1 : ∀ x ∈ L, k * x = x * k :=
    d391ll_centralizes_of_mem_kernel hq hLC (fun g hg => hCn g (Subgroup.mem_sup_left hg)) hk.2
      fun x hx => (Subgroup.mem_normalizer_iff.1 (hnL hk.1) x).1 hx
  have hk2 : ∀ x ∈ Lt, k * x = x * k :=
    d391ll_centralizes_of_mem_kernel hqt hLtC (fun g hg => hCn g (Subgroup.mem_sup_right hg)) hk.2
      fun x hx => (Subgroup.mem_normalizer_iff.1 (hnLt hk.1) x).1 hx
  have hle : L ⊔ Lt ≤ Subgroup.centralizer ({k} : Set G) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hk1 x hx).symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (hk2 x hx).symm
  intro x hx
  exact (Subgroup.mem_centralizer_singleton_iff.1 (hle hx)).symm

theorem d391ll_inf_centSec_eq_bot {W : Type} [CommGroup W] {G Mp A : Subgroup (MulAut W)}
    {Y Z : Subgroup W} (hperf : ⁅Mp, Mp⁆ = Mp) (hLG : Mp ≤ G) (hAG : A ≤ G)
    (hN : ∀ g ∈ G, ∀ l ∈ Mp, g * l * g⁻¹ ∈ Mp) (hGY : G ≤ stabSub Y) (hGZ : G ≤ stabSub Z)
    (hKc : ∀ k ∈ Mp ⊓ centSec Y Z, ∀ l ∈ Mp, k * l = l * k)
    (hf : ∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) : A ⊓ centSec Y Z = ⊥ := by
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  refine hf a ha.1 ?_
  refine B5.commute_of_comm_central hperf (fun l hl => hN a (hAG ha.1) l hl) hKc fun l hl => ?_
  refine ⟨?_, ?_⟩
  · have h1 := hN a (hAG ha.1) l hl
    rw [commutatorElement_def]
    exact Mp.mul_mem h1 (Mp.inv_mem hl)
  · have h1 : l * a⁻¹ * l⁻¹ ∈ centSec Y Z :=
      conj_mem_centSec (hGY (hLG hl)) (hGZ (hLG hl)) ((centSec Y Z).inv_mem ha.2)
    have h2 : ⁅a, l⁆ = a * (l * a⁻¹ * l⁻¹) := by
      simp [commutatorElement_def, mul_assoc]
    rw [h2]
    exact (centSec Y Z).mul_mem ha.2 h1

theorem d391ll_isFF_of_faithful {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D31 M Mp T L V)
    (hVT : V = orbSup T V) (htop : ¬ orbSup T V = ⊤)
    (hfaith : ∀ B : Subgroup (MulAut W), B ≤ Mp ⊔ T →
      (∀ b ∈ B, (∀ y ∈ Mp, b * y = y * b) → b = 1) → B ⊓ centSec V (V ⊓ fixV Mp) = ⊥)
    {A : Subgroup (MulAut W)} (hA : IsA2 M A) (hAT : A ≤ T) (hA3 : commSeries A 3 = ⊥)
    (hAr : rAV A ≤ 2) (hAf : ∀ a ∈ A, (∀ x ∈ Mp, a * x = x * a) → a = 1) :
    IsFFModule (autSec (Mp ⊔ T) V (V ⊓ fixV Mp)) := by
  have hexp := hD.exp
  have hG := n1_sup_le_stabSub_sec hD
  rw [← hVT] at hG
  have hGV : Mp ⊔ T ≤ stabSub V := hG.trans inf_le_left
  have hGC : Mp ⊔ T ≤ stabSub (V ⊓ fixV Mp) := hG.trans inf_le_right
  obtain ⟨-, hVcomm, -, -⟩ := mem_irrPlus_top_iff.1 hD.irr
  have hMn : ∀ m ∈ M, ∀ l ∈ Mp, m * l * m⁻¹ ∈ Mp := fun m hm l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hD.Mp_normal hm)) l).1 hl
  have hcommV : commV Mp = ⊤ := Z391.commV_eq_top hMn hVcomm hD.gen
  have hAG : A ≤ Mp ⊔ T := hAT.trans le_sup_right
  have hAV : A ≤ stabSub V := hAG.trans hGV
  have hAC : A ≤ stabSub (V ⊓ fixV Mp) := hAG.trans hGC
  have hf₁ : A ⊓ centSec V (V ⊓ fixV Mp) = ⊥ := hfaith A hAG hAf
  have hrA : 0 < rk ↥A := hA.rk_pos
  have hA2 : IsA2 (Mp ⊔ T) A := ⟨hAG, hA.2.1, hA.2.2⟩
  have hq1 := Z391.qhatOf_autSec_le_rAV hA2 hA3 hAV hAC hf₁
  obtain ⟨q, hq'⟩ := WithTop.ne_top_iff_exists.1 (ne_top_of_le_ne_top WithTop.coe_ne_top hq1)
  have hMpM : Mp ≤ M := by
    rw [hD.Mp_eq]
    exact conjClosure_le fun s hs z hz =>
      M.mul_mem (M.mul_mem (hD.sylow.1 hs) (le_of_mem_cComp hD.comp hz)) (M.inv_mem (hD.sylow.1 hs))
  have hTX : M ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := hD.Mp_normal
  have hWM : ∀ t ∈ M, ∀ w ∈ (⊤ : Subgroup W), t • w ∈ (⊤ : Subgroup W) := fun _ _ _ _ => trivial
  let instQ : MulDistribMulAction ↥M (W ⧸ modFix Mp (⊤ : Subgroup W)) := quotAct hTX hWM
  set π : W →* (W ⧸ modFix Mp (⊤ : Subgroup W)) :=
    QuotientGroup.mk' (modFix Mp (⊤ : Subgroup W)) with hπ
  have hπsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hπM : ∀ (g : ↥M) (w : W), g • π w = π ((g : MulAut W) w) := fun g w => rfl
  have hker : π.ker = fixV Mp := by
    rw [hπ, QuotientGroup.ker_mk']
    exact (fixed_eq_inf_fixV Mp ⊤).trans (top_inf_eq _)
  have hQ : ∀ x : W ⧸ modFix Mp (⊤ : Subgroup W), x ^ 2 = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H v => rw [← QuotientGroup.mk_pow, hexp v, QuotientGroup.mk_one]
  have hirr := (isIrr_tilde hD.irr).1
  let φ : ↥(Mp.subgroupOf M) → ↥Mp := fun l => ⟨((l : ↥M) : MulAut W), l.2⟩
  have hφ : Function.Surjective φ := fun a => ⟨⟨⟨(a : MulAut W), hMpM a.2⟩, a.2⟩, rfl⟩
  have hact : ∀ (l : ↥(Mp.subgroupOf M)) (x : W ⧸ modFix Mp (⊤ : Subgroup W)), l • x = φ l • x := by
    intro l x
    induction x using QuotientGroup.induction_on with
    | H v => rfl
  have hVΛ : XMod.IsIrr ↥(Mp.subgroupOf M) (tilde Mp (⊤ : Subgroup W) V) :=
    Z391.isIrr_of_surj φ hφ hact hirr
  have hΛ : ∀ g : ↥M, ∀ l ∈ Mp.subgroupOf M, g * l * g⁻¹ ∈ Mp.subgroupOf M :=
    fun g l hl => hMn (g : MulAut W) g.2 (l : MulAut W) hl
  have hT : IsSylowTwoOf (T.subgroupOf M) (⊤ : Subgroup ↥M) :=
    Z391.isSylowTwoOf_subgroupOf_top hD.sylow
  have hAT₀ : A.subgroupOf M ≤ T.subgroupOf M := fun x hx => hAT hx
  have hAc : ∀ x ∈ A.subgroupOf M, ∀ y ∈ A.subgroupOf M, x * y = y * x :=
    fun x hx y hy => Subtype.ext (hA.2.2.1 _ hx _ hy)
  have hA2' : ∀ x ∈ A.subgroupOf M, x ^ 2 = 1 := fun x hx =>
    Subtype.ext (by simpa using hA.2.2.2 (x : MulAut W) hx)
  have hVT₀ : ∀ t ∈ T.subgroupOf M,
      t • tilde Mp (⊤ : Subgroup W) V = tilde Mp (⊤ : Subgroup W) V := by
    intro t ht
    have h1 : t • tilde Mp (⊤ : Subgroup W) V = tilde Mp (⊤ : Subgroup W) ((t : MulAut W) • V) :=
      tilde_smul hTX hWM t V
    have h2 : (t : MulAut W) • V = V :=
      map_eq_of_mem_stabSub (hGV ((le_sup_right : T ≤ Mp ⊔ T) ht))
    rw [h1, h2]
  have hgen' : (⨆ g : ↥M, g • tilde Mp (⊤ : Subgroup W) V) = ⊤ := by
    have e : ∀ g : ↥M, g • tilde Mp (⊤ : Subgroup W) V =
        tilde Mp (⊤ : Subgroup W) ((g : MulAut W) • V) := fun g => tilde_smul hTX hWM g V
    rw [iSup_congr e, ← tilde_biSup M V]
    have : (⨆ y ∈ M, y • V) = ⊤ := hD.gen
    rw [this]
    exact Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hne : tilde Mp (⊤ : Subgroup W) V ≠ ⊤ := by
    intro h
    have h1 : V ⊔ modFix Mp (⊤ : Subgroup W) = ⊤ := by
      rw [← comap_tilde, h, Subgroup.comap_top]
    have h2 : modFix Mp (⊤ : Subgroup W) = fixV Mp :=
      (fixed_eq_inf_fixV Mp ⊤).trans (top_inf_eq _)
    rw [h2] at h1
    have h3 : commSub (⊤ : Subgroup W) Mp = V := by
      rw [← h1, commSub_sup_fixV le_rfl, hVcomm]
    rw [← commV_eq_commSub, hcommV] at h3
    exact htop (hVT.symm.trans h3.symm)
  obtain ⟨g, A₁, B, hA₁A, hBdef, hBT, hcount⟩ :=
    Z391.mackey_count (Γ := ↥M) (Q := W ⧸ modFix Mp (⊤ : Subgroup W)) (Λ := Mp.subgroupOf M)
      (T := T.subgroupOf M) (A := A.subgroupOf M) hQ hΛ hT hAT₀ hAc hA2' hVΛ hVT₀ hgen' hne
  have hA₀A : (A.subgroupOf M).map M.subtype = A := Subgroup.map_subgroupOf_eq_of_le hA.1
  have hrkA₀ : rk ↥(A.subgroupOf M) = rk ↥A := by
    unfold rk
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv]
  have hN1 : Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) ≤
      rkIdx (fixV A) := by
    have := Z391.nB_top_le_rkIdx_fixV π hπsurj hπM (A.subgroupOf M)
    rwa [hA₀A] at this
  have hN2 : (rkIdx (fixV A) : ℚ) ≤ 2 * (rk ↥A : ℚ) := by
    have h := hAr
    unfold rAV at h
    have hpos : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
    rwa [div_le_iff₀ hpos] at h
  have hqA : q * (rk ↥A : ℚ) ≤
      (Z391.nB (A.subgroupOf M) (tilde Mp (⊤ : Subgroup W) V) : ℚ) := by
    have h1 := Z391.q_mul_rk_le hA2 hA3 hAV hAC hf₁ hq'
    have h2 := Z391.rkIdx_fixV_autSec_le_nB π hπM (A.subgroupOf M) V
    rw [hA₀A, hker] at h2
    exact h1.trans (by exact_mod_cast h2)
  set B' : Subgroup (MulAut W) := B.map M.subtype with hB'
  have hB'T : B' ≤ T := by
    rintro _ ⟨b, hb, rfl⟩
    exact hBT hb
  have hA₁' : A₁.map M.subtype ≤ A := by
    rintro _ ⟨a, ha, rfl⟩
    exact hA₁A ha
  have hB'eq : B' = (A₁.map M.subtype).map (MulAut.conj ((g : MulAut W)⁻¹)).toMonoidHom := by
    rw [hB', hBdef, Z391.map_subtype_conj]
    rfl
  have hhM : (g : MulAut W)⁻¹ ∈ M := M.inv_mem g.2
  have hmemB' : ∀ x ∈ B', ∃ a ∈ A, x = (g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹ := by
    intro x hx
    rw [hB'eq] at hx
    obtain ⟨y, ⟨a, ha, rfl⟩, rfl⟩ := hx
    exact ⟨(a : MulAut W), hA₁' ⟨a, ha, rfl⟩, rfl⟩
  have hB'ab : IsElemAbelian2 B' := by
    refine ⟨fun x hx y hy => ?_, fun x hx => ?_⟩
    · obtain ⟨a, ha, rfl⟩ := hmemB' x hx
      obtain ⟨b, hb, rfl⟩ := hmemB' y hy
      have := hA.2.2.1 a ha b hb
      calc (g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹ *
            ((g : MulAut W)⁻¹ * b * ((g : MulAut W)⁻¹)⁻¹)
          = (g : MulAut W)⁻¹ * (a * b) * ((g : MulAut W)⁻¹)⁻¹ := by group
        _ = (g : MulAut W)⁻¹ * (b * a) * ((g : MulAut W)⁻¹)⁻¹ := by rw [this]
        _ = (g : MulAut W)⁻¹ * b * ((g : MulAut W)⁻¹)⁻¹ * ((g : MulAut W)⁻¹ * a *
              ((g : MulAut W)⁻¹)⁻¹) := by
          group
    · obtain ⟨a, ha, rfl⟩ := hmemB' x hx
      have := hA.2.2.2 a ha
      calc ((g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹) ^ 2
          = (g : MulAut W)⁻¹ * (a * a) * ((g : MulAut W)⁻¹)⁻¹ := by rw [pow_two]; group
        _ = 1 := by rw [← pow_two, this]; group
  have hB'f : ∀ x ∈ B', (∀ y ∈ Mp, x * y = y * x) → x = 1 := by
    intro x hx hxc
    obtain ⟨a, ha, rfl⟩ := hmemB' x hx
    have ha1 : a = 1 := by
      refine hAf a ha (fun z hz => ?_)
      have hy : (g : MulAut W)⁻¹ * z * ((g : MulAut W)⁻¹)⁻¹ ∈ Mp := hMn _ hhM z hz
      have e := hxc _ hy
      have e' : (g : MulAut W)⁻¹ * (a * z) * ((g : MulAut W)⁻¹)⁻¹ =
          (g : MulAut W)⁻¹ * (z * a) * ((g : MulAut W)⁻¹)⁻¹ := by
        calc (g : MulAut W)⁻¹ * (a * z) * ((g : MulAut W)⁻¹)⁻¹
            = (g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹ *
                ((g : MulAut W)⁻¹ * z * ((g : MulAut W)⁻¹)⁻¹) := by group
          _ = (g : MulAut W)⁻¹ * z * ((g : MulAut W)⁻¹)⁻¹ *
                ((g : MulAut W)⁻¹ * a * ((g : MulAut W)⁻¹)⁻¹) := e
          _ = (g : MulAut W)⁻¹ * (z * a) * ((g : MulAut W)⁻¹)⁻¹ := by group
      exact mul_left_cancel (mul_right_cancel e')
    rw [ha1]
    group
  have hB'3 : commSeries B' 3 = ⊥ := by
    rw [hB'eq, Z391.commSeries_map_conj]
    have : commSeries (A₁.map M.subtype) 3 = ⊥ :=
      le_bot_iff.1 ((commSeries_mono hA₁' 3).trans hA3.le)
    rw [this, Subgroup.map_bot]
  have hGB' : B' ≤ Mp ⊔ T := hB'T.trans le_sup_right
  have hB'V : B' ≤ stabSub V := hGB'.trans hGV
  have hB'C : B' ≤ stabSub (V ⊓ fixV Mp) := hGB'.trans hGC
  have hf₂ : B' ⊓ centSec V (V ⊓ fixV Mp) = ⊥ := hfaith B' hGB' hB'f
  have hrkB' : rk ↥B' = rk ↥A₁ := by
    have h1 : rk ↥B' = rk ↥B := by
      unfold rk
      rw [hB', Subgroup.card_map_of_injective M.subtype_injective]
    rw [h1, hBdef]
    exact Z391.rk_map_conj A₁ g⁻¹
  have hqB : q * (rk ↥A₁ : ℚ) ≤
      (Z391.nB B (tilde Mp (⊤ : Subgroup W) V) : ℚ) := by
    by_cases hz : rk ↥A₁ = 0
    · rw [hz]
      simp
    · have hB'ne : B' ≠ ⊥ := by
        intro hbot
        apply hz
        rw [← hrkB', hbot, rk_bot]
      have hB'A2 : IsA2 (Mp ⊔ T) B' := ⟨hGB', hB'ne, hB'ab⟩
      have h1 := Z391.q_mul_rk_le hB'A2 hB'3 hB'V hB'C hf₂ hq'
      have h2 := Z391.rkIdx_fixV_autSec_le_nB π hπM B V
      rw [hker] at h2
      rw [hrkB'] at h1
      exact h1.trans (by exact_mod_cast h2)
  have hr₁ : rk ↥A₁ ≤ rk ↥(A.subgroupOf M) := rk_mono hA₁A
  have hcountQ : (Z391.nB (A.subgroupOf M) (tilde Mp (⊤ : Subgroup W) V) : ℚ) +
      (Z391.nB B (tilde Mp (⊤ : Subgroup W) V) : ℚ) + (rk ↥A : ℚ) ≤
      (Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) : ℚ) +
        (rk ↥A₁ : ℚ) := by
    have : Z391.nB (A.subgroupOf M) (tilde Mp (⊤ : Subgroup W) V) +
        Z391.nB B (tilde Mp (⊤ : Subgroup W) V) + rk ↥A ≤
        Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) + rk ↥A₁ := by
      omega
    exact_mod_cast this
  have hN1' : (Z391.nB (A.subgroupOf M) (⊤ : Subgroup (W ⧸ modFix Mp (⊤ : Subgroup W))) : ℚ) ≤
      (rkIdx (fixV A) : ℚ) := by exact_mod_cast hN1
  have e3 : q ≤ 1 := by
    have ha : (0 : ℚ) < (rk ↥A : ℚ) := by exact_mod_cast hrA
    have ha₁ : (0 : ℚ) ≤ (rk ↥A₁ : ℚ) := Nat.cast_nonneg _
    by_contra hcon
    have hcon' : 1 < q := not_le.1 hcon
    nlinarith [mul_pos (sub_pos.2 hcon') (add_pos_of_pos_of_nonneg ha ha₁)]
  have hle : qhatOf (autSec (Mp ⊔ T) V (V ⊓ fixV Mp)) ≤ ((1 : ℚ) : WithTop ℚ) := by
    rw [← hq']
    exact_mod_cast e3
  obtain ⟨A', hA'2, -, hA'r⟩ := kq_le_iff.1 hle
  exact (isFFModule_iff (Bridge.sec_sq_eq_one hexp V (V ⊓ fixV Mp))).2 ⟨A', hA'2, hA'r⟩

theorem d391ll_faithful_sec {W : Type} [CommGroup W] [Finite W]
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} (hD : D31 M Mp T L V)
    (hVT : V = orbSup T V) {t : MulAut W} (htT : t ∈ T) (hMp : Mp = L ⊔ conjAutSub t L)
    (hcomm : ⁅L, conjAutSub t L⁆ = ⊥) :
    ∀ B : Subgroup (MulAut W), B ≤ Mp ⊔ T →
      (∀ b ∈ B, (∀ y ∈ Mp, b * y = y * b) → b = 1) → B ⊓ centSec V (V ⊓ fixV Mp) = ⊥ := by
  intro B hBG hBf
  have hTn : T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) := by
    calc T ≤ Subgroup.normalizer (conjClosure L T : Set (MulAut W)) :=
          le_normalizer_conjClosure L T
      _ = Subgroup.normalizer (Mp : Set (MulAut W)) := by rw [← hD.Mp_eq]
  have hGN : Mp ⊔ T ≤ Subgroup.normalizer (Mp : Set (MulAut W)) :=
    sup_le Subgroup.le_normalizer hTn
  have hN : ∀ g ∈ Mp ⊔ T, ∀ l ∈ Mp, g * l * g⁻¹ ∈ Mp := fun g hg l hl =>
    ((Subgroup.mem_normalizer_iff.1 (hGN hg)) l).1 hl
  have hG := n1_sup_le_stabSub_sec hD
  rw [← hVT] at hG
  have hGV : Mp ⊔ T ≤ stabSub V := hG.trans inf_le_left
  have hGC : Mp ⊔ T ≤ stabSub (V ⊓ fixV Mp) := hG.trans inf_le_right
  obtain ⟨-, hVcomm, hVlt, -⟩ := mem_irrPlus_top_iff.1 hD.irr
  have hntV : ¬ Mp ≤ centSec V (V ⊓ fixV Mp) := by
    intro h
    have h1 : commSub V Mp ≤ V ⊓ fixV Mp := by
      rw [commSub, Subgroup.closure_le]
      rintro _ ⟨x, hx, w, hw, rfl⟩
      exact (h hx).2 w hw
    rw [hVcomm] at h1
    exact lt_irrefl _ (lt_of_lt_of_le hVlt h1)
  have hconj : ∀ g ∈ Mp ⊔ T, ∀ c ∈ centSec V (V ⊓ fixV Mp),
      g * c * g⁻¹ ∈ centSec V (V ⊓ fixV Mp) := fun g hg c hc =>
    conj_mem_centSec (hGV hg) (hGC hg) hc
  have htG : t ∈ Mp ⊔ T := (le_sup_right : T ≤ Mp ⊔ T) htT
  have hLtC : L ≤ centSec V (V ⊓ fixV Mp) → conjAutSub t L ≤ centSec V (V ⊓ fixV Mp) := by
    intro h x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact hconj t htG y (h hy)
  have hLC' : conjAutSub t L ≤ centSec V (V ⊓ fixV Mp) → L ≤ centSec V (V ⊓ fixV Mp) := by
    intro h x hx
    have hx' : t * x * t⁻¹ ∈ conjAutSub t L := ⟨x, hx, rfl⟩
    have := hconj t⁻¹ ((Mp ⊔ T).inv_mem htG) _ (h hx')
    have e : t⁻¹ * (t * x * t⁻¹) * t⁻¹⁻¹ = x := by group
    rwa [e] at this
  have hLnot : ¬ L ≤ centSec V (V ⊓ fixV Mp) := fun h =>
    hntV (hMp.le.trans (sup_le h (hLtC h)))
  have hLtnot : ¬ conjAutSub t L ≤ centSec V (V ⊓ fixV Mp) := fun h =>
    hntV (hMp.le.trans (sup_le (hLC' h) h))
  have hcomm' : ∀ x ∈ L, ∀ y ∈ conjAutSub t L, x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.commutator_le.1 hcomm.le x hx y hy
    rwa [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h1
  have hqL : CFSG.IsQuasisimple ↥L := hD.quasi
  have hqLt : CFSG.IsQuasisimple ↥(conjAutSub t L) := (hD.conj htT).quasi
  have hperfL : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hqL.1
    exact Subgroup.commutator_eq_self
  have hperfLt : ⁅conjAutSub t L, conjAutSub t L⁆ = conjAutSub t L := by
    have : Group.IsPerfect ↥(conjAutSub t L) := hqLt.1
    exact Subgroup.commutator_eq_self
  have hperf : ⁅Mp, Mp⁆ = Mp := by
    rw [hMp]
    exact d391ll_perfect_sup hperfL hperfLt
  have hkc := d391ll_kernel_central hMp hqL hqLt hcomm'
    (fun g hg c hc => hconj g ((le_sup_left : Mp ≤ Mp ⊔ T) hg) c hc) hLnot hLtnot
  exact d391ll_inf_centSec_eq_bot hperf le_sup_left hBG hN hGV hGC hkc hBf

theorem d391LLTop_of_notFF (hL38 : D3L38) (hNF : D391NotFFTop) : D391LLTop := by
  intro W _ _ M Mp T L V hD _ t htT htL hMp hVT A hA
  by_contra htop
  obtain ⟨-, hcomm, -, -⟩ := hL38 W M Mp T L V hD t htT htL hMp
  refine hNF W M Mp T L V hD hVT t htT htL hMp ?_
  exact d391ll_isFF_of_faithful hD.hyp hVT htop (d391ll_faithful_sec hD.hyp hVT htT hMp hcomm)
    ⟨hA.le.trans hD.hyp.sylow.1, hA.ne, hA.elem⟩ hA.le
    (commSeries_eq_bot_of_le (by norm_num) hA.quad) hA.rat hA.faithMp

end CFSG.Quasithin
