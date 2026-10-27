module

public import CFSG.Quasithin.MS93.S310Mod
public import CFSG.Quasithin.MS93.S5BL2
public import CFSG.Quasithin.MS93.S5BXZ

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.Fan86.Univ
open CFSG.Open hiding StatedSL StatedSp StatedSU StatedOmega StatedQuadMinus StatedQuadPlus
  StatedQuadOdd StatedScalars StatedClassicalModel StatedLieAdmissible
open scoped commutatorElement

namespace S310

section Group

variable {Γ : Type} [Group Γ]

theorem commutator_sup_left_le {H₁ H₂ A N : Subgroup Γ}
    (hN₁ : H₁ ≤ Subgroup.normalizer (N : Set Γ)) (hN₂ : H₂ ≤ Subgroup.normalizer (N : Set Γ))
    (h₁ : ⁅H₁, A⁆ ≤ N) (h₂ : ⁅H₂, A⁆ ≤ N) : ⁅H₁ ⊔ H₂, A⁆ ≤ N := by
  let S : Subgroup Γ :=
    { carrier := {y | y ∈ Subgroup.normalizer (N : Set Γ) ∧ ∀ x ∈ A, ⁅y, x⁆ ∈ N}
      one_mem' := ⟨one_mem _, fun x _ => by simp⟩
      mul_mem' := by
        rintro y₁ y₂ ⟨hy₁, h₁⟩ ⟨hy₂, h₂⟩
        refine ⟨mul_mem hy₁ hy₂, fun x hx => ?_⟩
        have e : ⁅y₁ * y₂, x⁆ = (y₁ * ⁅y₂, x⁆ * y₁⁻¹) * ⁅y₁, x⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.1 hy₁ _).1 (h₂ x hx)) (h₁ x hx)
      inv_mem' := by
        rintro y ⟨hy, h₁⟩
        refine ⟨inv_mem hy, fun x hx => ?_⟩
        have e : ⁅y⁻¹, x⁆ = y⁻¹ * ⁅y, x⁆⁻¹ * y := by
          simp only [commutatorElement_def]
          group
        rw [e]
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hy) _).1 (inv_mem (h₁ x hx))
        simpa using this }
  have hS : H₁ ⊔ H₂ ≤ S := sup_le
    (fun y hy => ⟨hN₁ hy, fun x hx => h₁ (Subgroup.commutator_mem_commutator hy hx)⟩)
    (fun y hy => ⟨hN₂ hy, fun x hx => h₂ (Subgroup.commutator_mem_commutator hy hx)⟩)
  rw [Subgroup.commutator_le]
  intro y hy x hx
  exact (hS hy).2 x hx

theorem commutator_sup_sup_le {H₁ H₂ N : Subgroup Γ}
    (hN₁ : H₁ ≤ Subgroup.normalizer (N : Set Γ)) (hN₂ : H₂ ≤ Subgroup.normalizer (N : Set Γ))
    (h₁₁ : ⁅H₁, H₁⁆ ≤ N) (h₁₂ : ⁅H₁, H₂⁆ ≤ N) (h₂₂ : ⁅H₂, H₂⁆ ≤ N) :
    ⁅H₁ ⊔ H₂, H₁ ⊔ H₂⁆ ≤ N := by
  refine commutator_sup_left_le hN₁ hN₂ ?_ ?_
  · rw [Subgroup.commutator_comm]
    exact commutator_sup_left_le hN₁ hN₂ h₁₁ (by rw [Subgroup.commutator_comm]; exact h₁₂)
  · rw [Subgroup.commutator_comm]
    exact commutator_sup_left_le hN₁ hN₂ h₁₂ h₂₂

theorem le_normalizer_centralizer {A K : Subgroup Γ} (h : A ≤ Subgroup.normalizer (K : Set Γ)) :
    A ≤ Subgroup.normalizer (Subgroup.centralizer (K : Set Γ) : Set Γ) := by
  have key : ∀ g ∈ A, ∀ x ∈ Subgroup.centralizer (K : Set Γ),
      g * x * g⁻¹ ∈ Subgroup.centralizer (K : Set Γ) := by
    intro g hg x hx
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : g⁻¹ * l * g ∈ K := by
      have := (Subgroup.mem_normalizer_iff.1 (inv_mem (h hg)) l).1 hl
      simpa using this
    have hc := Subgroup.mem_centralizer_iff.1 hx _ hl'
    calc l * (g * x * g⁻¹) = g * ((g⁻¹ * l * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * l * g)) * g⁻¹ := by rw [hc]
      _ = g * x * g⁻¹ * l := by group
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem le_normalizer_inf {A H K : Subgroup Γ} (hH : A ≤ Subgroup.normalizer (H : Set Γ))
    (hK : A ≤ Subgroup.normalizer (K : Set Γ)) :
    A ≤ Subgroup.normalizer ((H ⊓ K : Subgroup Γ) : Set Γ) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  simp only [Subgroup.mem_inf]
  exact and_congr (Subgroup.mem_normalizer_iff.1 (hH hg) x)
    (Subgroup.mem_normalizer_iff.1 (hK hg) x)

end Group

section Base

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem commutator_le_of_two_elt_baseA (h : PUHyp M T L)
    {W Z : Subgroup (puAmalgam h.le).Universal}
    (hW : W ≤ stab _ (baseA (puAmalgam h.le))) (hZ : Z ≤ stab _ (baseA (puAmalgam h.le)))
    (hWn : puTrans h.le L (baseA _) ≤
      Subgroup.normalizer (W : Set (puAmalgam h.le).Universal))
    (hZn : puTrans h.le L (baseA _) ≤
      Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal))
    {y : (puAmalgam h.le).Universal} (hy : y ∈ stab _ (baseA (puAmalgam h.le)))
    (hy2 : ∃ e : ℕ, y ^ 2 ^ e = 1) (hyQ : y ∉ Qv _ (baseA (puAmalgam h.le)))
    (hyZ : y ∈ Subgroup.normalizer (Z : Set (puAmalgam h.le).Universal))
    (hyW : ∀ w ∈ W, y * w * y⁻¹ * w⁻¹ ∈ Z) :
    ⁅W, puTrans h.le L (baseA _)⁆ ≤ Z := by
  have hLα := S5B.puTrans_L_baseA h
  have hQα := S5B.qv_baseA_eq h
  have hstM : stab _ (baseA (puAmalgam h.le)) = (puAmalgam h.le).ofA.range := by
    rw [puAmalgam.stab_baseA, imM, Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map]
  rw [hstM] at hy
  obtain ⟨y₀, rfl⟩ := hy
  have hWn₀ := S5B.le_normalizer_preM h.le h.L_le (hLα ▸ hWn)
  have hZn₀ := S5B.le_normalizer_preM h.le h.L_le (hLα ▸ hZn)
  have hyZ₀ : (y₀ : G) ∈ Subgroup.normalizer (S5B.preM h.le Z : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · rintro ⟨m, hm, rfl⟩
      refine ⟨y₀ * m * y₀⁻¹, ?_, by simp⟩
      show (puAmalgam h.le).ofA (y₀ * m * y₀⁻¹) ∈ Z
      rw [map_mul, map_mul, map_inv]
      exact (Subgroup.mem_normalizer_iff.1 hyZ _).1 hm
    · rintro ⟨m, hm, hmx⟩
      refine ⟨y₀⁻¹ * m * y₀, ?_, ?_⟩
      · show (puAmalgam h.le).ofA (y₀⁻¹ * m * y₀) ∈ Z
        rw [map_mul, map_mul, map_inv]
        have := (Subgroup.mem_normalizer_iff.1 (inv_mem hyZ) _).1 hm
        simpa using this
      · simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv] at hmx ⊢
        rw [hmx]
        group
  have hcore := S5B.commutator_le_of_two_elt h hWn₀ hZn₀ y₀.2 ?_ ?_ hyZ₀ ?_
  · have := (S5B.commutator_imM_le_iff h.le (S5B.preM_le h.le _) h.L_le).2 hcore
    rwa [S5B.imM_preM h.le hW, ← hLα, S5B.imM_preM h.le hZ] at this
  · obtain ⟨e, he⟩ := hy2
    refine ⟨e, ?_⟩
    have := (puAmalgam h.le).ofA_injective
      (show (puAmalgam h.le).ofA (y₀ ^ 2 ^ e) = (puAmalgam h.le).ofA 1 by
        rw [map_pow, he, map_one])
    simpa using congrArg Subtype.val this
  · intro hO
    apply hyQ
    rw [hQα]
    exact ⟨y₀, Subgroup.mem_subgroupOf.2 hO, rfl⟩
  · rintro _ ⟨m, hm, rfl⟩
    refine ⟨y₀ * m * y₀⁻¹ * m⁻¹, ?_, by simp⟩
    show (puAmalgam h.le).ofA (y₀ * m * y₀⁻¹ * m⁻¹) ∈ Z
    simpa [map_mul, map_inv] using hyW _ hm

theorem vv_le_qv_baseA (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le)) :
    Vv (puAmalgam h.le) (baseA _) ≤ Qv _ (baseA (puAmalgam h.le)) := by
  have hα := isMVtx_baseA (puAmalgam h.le)
  refine iSup₂_le fun ρ hρ => ?_
  have hρ' : (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≤ 2 := hρ
  by_cases hρM : IsMVtx _ ρ
  · rw [zv_of_isMVtx _ hρM]
    exact zm_le_qv_of_dist_lt _ hρM (by rw [SimpleGraph.dist_comm]; omega)
  · rw [zv_of_not_isMVtx _ hρM]
    have hd1 : (puAmalgam h.le).treeGraph.dist (baseA _) ρ = 1 := by
      have h0 : (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≠ 0 := fun h0 => by
        rw [(dist_eq_zero_iff _).1 h0] at hα
        exact hρM hα
      have hodd : ¬ Even ((puAmalgam h.le).treeGraph.dist (baseA _) ρ) := fun he =>
        hρM (((even_dist_iff _ _ _).1 he).1 hα)
      have h2 : (puAmalgam h.le).treeGraph.dist (baseA _) ρ ≠ 2 := fun h2 =>
        hodd (h2 ▸ even_two)
      omega
    have hadj : (puAmalgam h.le).treeGraph.Adj (baseA _) ρ :=
      SimpleGraph.dist_eq_one_iff_adj.1 hd1
    exact (zh_le_zm _ hadj).trans (zm_le_qv_self _ hα h.critDist_pos)

theorem commutator_mem_zm_of_mem_bSub (h : PUHyp M T L) (hb : 2 < critDist (puAmalgam h.le))
    {x : (puAmalgam h.le).Universal} (hx : x ∈ S5.bSub h.le L (baseA _))
    {l : (puAmalgam h.le).Universal} (hl : l ∈ puTrans h.le L (baseA _)) :
    ⁅x, l⁆ ∈ ZM _ (baseA (puAmalgam h.le)) := by
  have hst : ∀ g ∈ S5.bSub h.le L (baseA _),
      g ∈ Subgroup.normalizer (ZM _ (baseA (puAmalgam h.le)) : Set _) := by
    intro g hg
    refine stab_le_normalizer_zm _ _ (qv_le_stab _ _ ?_)
    refine (Subgroup.closure_le _).2 ?_ hg
    rintro v ⟨hv, -⟩
    exact vv_le_qv_baseA h hb hv
  have hx' : x ∈ Subgroup.closure {v | v ∈ Vv (puAmalgam h.le) (baseA _) ∧
      ∀ y ∈ puTrans h.le L (baseA _), ⁅v, y⁆ ∈ ZM (puAmalgam h.le) (baseA _)} := hx
  clear hx
  induction hx' using Subgroup.closure_induction with
  | mem v hv => exact hv.2 l hl
  | one => simp
  | mul a b ha _ iha ihb =>
    have e : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hst a ha) _).1 ihb) iha
  | inv a ha iha =>
    have e : ⁅a⁻¹, l⁆ = a⁻¹ * ⁅a, l⁆⁻¹ * a := by
      simp only [commutatorElement_def]
      group
    rw [e]
    have := (Subgroup.mem_normalizer_iff.1 (inv_mem (hst a ha)) _).1 (inv_mem iha)
    simpa using this

theorem exists_mul_of_mem_stab (h : PUHyp M T L) {δ : Vtx (puAmalgam h.le)}
    (hδ : (puAmalgam h.le).treeGraph.Adj (baseA _) δ) {g : (puAmalgam h.le).Universal}
    (hg : g ∈ stab _ (baseA (puAmalgam h.le))) :
    ∃ l ∈ puTrans h.le L (baseA _), ∃ t ∈ Qv _ δ, g = l * t := by
  obtain ⟨g₀, hg₀, hg₀δ⟩ := exists_mem_stab_smul _ (adj_baseA_baseB (puAmalgam h.le)) hδ
  have hQδ : Qv _ δ = (imM h.le T).map (MulAut.conj g₀).toMonoidHom := by
    rw [← hg₀δ, qv_smul, puAmalgam.qv_baseB]
  have hg' : g₀⁻¹ * g * g₀ ∈ stab _ (baseA (puAmalgam h.le)) :=
    mul_mem (mul_mem (inv_mem hg₀) hg) hg₀
  rw [puAmalgam.stab_baseA] at hg'
  obtain ⟨m, -, hm⟩ := hg'
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hsup : L.subgroupOf M ⊔ T.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup h.L_le h.le, ← h.eq_sup, Subgroup.subgroupOf_self]
  have hmem : m ∈ L.subgroupOf M ⊔ T.subgroupOf M := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  refine ⟨g₀ * (puAmalgam h.le).ofA l * g₀⁻¹, ?_, g₀ * (puAmalgam h.le).ofA t * g₀⁻¹, ?_, ?_⟩
  · have hlL : (puAmalgam h.le).ofA l ∈ puTrans h.le L (baseA _) := by
      rw [S5B.puTrans_L_baseA h]
      exact ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_puTrans h.le hLn _ hg₀) _).1 hlL
  · rw [hQδ]
    exact ⟨_, ⟨t, ht, rfl⟩, rfl⟩
  · calc g = g₀ * (g₀⁻¹ * g * g₀) * g₀⁻¹ := by group
      _ = g₀ * ((puAmalgam h.le).ofA l * (puAmalgam h.le).ofA t) * g₀⁻¹ := by
        rw [← hm, ← hlt, map_mul]
      _ = _ := by group

theorem exists_mem_puTrans_of_pow_three (h : PUHyp M T L) {F : Type} [Field F]
    {a : ↥(stab (puAmalgam h.le) (baseA _)) →* MSP.Sp4 F} (ha : Function.Surjective a)
    (g : MSP.Sp4 F) (hg : g ^ 3 = 1) :
    ∃ l : ↥(stab (puAmalgam h.le) (baseA _)), (l : (puAmalgam h.le).Universal) ∈
      puTrans h.le L (baseA _) ∧ a l = g := by
  obtain ⟨m, rfl⟩ := ha g
  have hm : (m : (puAmalgam h.le).Universal) ∈ imM h.le M := by
    rw [← puAmalgam.stab_baseA]
    exact m.2
  obtain ⟨m₀, -, hm₀⟩ := hm
  obtain ⟨e, he⟩ := h.exists_pow_mem_L m₀.2
  refine ⟨m ^ 4 ^ e, ?_, ?_⟩
  · have h1 : (m : (puAmalgam h.le).Universal) ^ 2 ^ e ∈ puTrans h.le L (baseA _) := by
      rw [S5B.puTrans_L_baseA h, ← hm₀, ← map_pow]
      exact ⟨m₀ ^ 2 ^ e, Subgroup.mem_subgroupOf.2 (by simpa using he), rfl⟩
    have h4 : (4 : ℕ) ^ e = 2 ^ e * 2 ^ e := by rw [← mul_pow]; norm_num
    rw [Subgroup.coe_pow, h4, pow_mul]
    exact pow_mem h1 _
  · have hmod : 4 ^ e % 3 = 1 := by
      rw [Nat.pow_mod]
      norm_num
    have hj : 4 ^ e = 3 * (4 ^ e / 3) + 1 := by
      have := Nat.div_add_mod (4 ^ e) 3
      omega
    rw [map_pow, hj, pow_add, pow_mul, hg, one_pow, one_mul, pow_one]

theorem exists_crit_elt (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 4)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α') :
    ∃ y ∈ stab _ (baseA (puAmalgam h.le)), (∃ e : ℕ, y ^ 2 ^ e = 1) ∧
      y ∉ Qv _ (baseA (puAmalgam h.le)) ∧
      y ∈ Subgroup.centralizer (ZM _ (geo _ (baseA _) α' 2) : Set _) := by
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb
  have hα' : IsMVtx _ α' := hc.isMVtx_right _ hyp
  have hγ : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) := isMVtx_geo_two _ hyp hb0 hc
  have hc' := ms22_iii _ hyp hb0 h.centHyp hc
  obtain ⟨y, hyZ, hyQ⟩ := Set.not_subset.1 hc'.2.2
  have hαδ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    adj_geo_one _ (by omega)
  have hδ : ¬ IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    (isMVtx_iff_of_adj _ hαδ).1 (isMVtx_baseA _)
  have hδα' : (puAmalgam h.le).treeGraph.dist (geo _ (baseA (puAmalgam h.le)) α' 1) α' = 3 := by
    rw [dist_geo_right _ (by omega), hd]
  have hyδ : y ∈ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    zm_le_qv_of_dist_lt _ hα' (by rw [SimpleGraph.dist_comm, hδα', hb]; norm_num) hyZ
  refine ⟨y, qv_le_stab_of_isMVtx _ hyp (isMVtx_baseA _) hαδ hyδ, ?_, hyQ, ?_⟩
  · obtain ⟨e, he⟩ := isPGroup_qv _ hyp hδ ⟨y, hyδ⟩
    exact ⟨e, by simpa using congrArg Subtype.val he⟩
  · have hγα' : (puAmalgam h.le).treeGraph.dist (geo _ (baseA (puAmalgam h.le)) α' 2) α' = 2 := by
      rw [dist_geo_right _ (by omega), hd]
    have hyγ : y ∈ Qv _ (geo _ (baseA (puAmalgam h.le)) α' 2) :=
      zm_le_qv_of_dist_lt _ hα' (by rw [SimpleGraph.dist_comm, hγα', hb]; norm_num) hyZ
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    exact ((Subgroup.mem_centralizer_iff.1 (zm_le_centralizer_qv _ hyp hγ hz)) y hyγ).symm

end Base

section Main

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

theorem s310a_core (h : PUHyp M T L) (hb : critDist (puAmalgam h.le) = 4)
    {α' : Vtx (puAmalgam h.le)} (hc : IsCritical _ (baseA _) α') {k : ℕ} {F : Type} [Field F]
    [Fintype F] {a : ↥(stab (puAmalgam h.le) (baseA _)) →* ↥(StatedSp 2 F)}
    (hF : Fintype.card F = 2 ^ k) (ha : Function.Surjective a)
    (hnat : IsSumOfNaturalModulesVia (stab _ (baseA _))
      (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)))
      (S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)) ⊓ S5.bSub h.le L (baseA _))
      a false 1)
    (hV₀D : ⁅⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆,
        ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆⁆ ≤
      S5.dSub h.le L (baseA _)) :
    ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)),
        S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2))⁆ =
      ⁅⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆,
        ⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)), puTrans h.le L (baseA _)⁆⁆ ∧
    Nat.card ↥⁅S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2)),
        S5.nclStab _ (baseA _) (ZM _ (geo _ (baseA _) α' 2))⁆ ≤ 2 ^ k := by
  have : CharP F 2 := S5B.charP_two_of_card hF
  have hyp := h.hyp20
  have hb0 := h.critDist_pos
  have hα := isMVtx_baseA (puAmalgam h.le)
  have hd : (puAmalgam h.le).treeGraph.dist (baseA _) α' = 4 := hc.2.1.trans hb
  have hγM : IsMVtx _ (geo _ (baseA (puAmalgam h.le)) α' 2) := isMVtx_geo_two _ hyp hb0 hc
  have hαγ : (puAmalgam h.le).treeGraph.dist (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 2) = 2 :=
    dist_geo _ (by omega)
  have hαδ : (puAmalgam h.le).treeGraph.Adj (baseA _) (geo _ (baseA (puAmalgam h.le)) α' 1) :=
    adj_geo_one _ (by omega)
  have hδγ : (puAmalgam h.le).treeGraph.Adj (geo _ (baseA (puAmalgam h.le)) α' 1)
      (geo _ (baseA (puAmalgam h.le)) α' 2) := adj_geo _ (by omega)
  set γ := geo _ (baseA (puAmalgam h.le)) α' 2 with hγdef
  set δ := geo _ (baseA (puAmalgam h.le)) α' 1 with hδdef
  let A : Subgroup (puAmalgam h.le).Universal := stab (puAmalgam h.le) (baseA (puAmalgam h.le))
  set Lt := puTrans h.le L (baseA (puAmalgam h.le)) with hLtdef
  set Zγ := ZM (puAmalgam h.le) γ with hZγdef
  set V := S5.nclStab _ (baseA (puAmalgam h.le)) Zγ with hVdef
  set B := S5.bSub h.le L (baseA (puAmalgam h.le)) with hBdef
  set D := S5.dSub h.le L (baseA (puAmalgam h.le)) with hDdef
  set Q := Qv (puAmalgam h.le) (baseA (puAmalgam h.le)) with hQdef
  have hLn : (L.subgroupOf M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer h.L_le).2 h.le_normalizer
  have hLA : Lt ≤ A := puTrans_le_stab h.le L _
  have hALt : A ≤ Subgroup.normalizer (Lt : Set _) := stab_le_normalizer_puTrans h.le hLn _
  have hAV : A ≤ Subgroup.normalizer (V : Set _) := hnat.1
  have hperf : ⁅Lt, Lt⁆ = Lt := by
    rw [hLtdef, S5B.puTrans_L_baseA h, ← imM_commutator h.le h.L_le h.L_le, h.perfect]
  have hQA : Q ≤ A := qv_le_stab _ _
  have hQγ : Q ≤ stab _ γ := qv_le_stab_of_dist_le_two _ hyp hα (by omega)
  have hZγV : Zγ ≤ V := fun z hz =>
    Subgroup.mem_iSup_of_mem (⟨1, one_mem _⟩ : ↥A) ⟨z, hz, by simp⟩
  have hVQ : V ≤ Q := by
    refine iSup_le fun g => ?_
    rw [← zm_smul]
    refine zm_le_qv_of_dist_lt _ ((isMVtx_smul _ _ _).2 hγM) ?_
    have hgα : (g : (puAmalgam h.le).Universal) • baseA (puAmalgam h.le) = baseA _ :=
      (mem_stab _).1 g.2
    calc (puAmalgam h.le).treeGraph.dist ((g : (puAmalgam h.le).Universal) • γ) (baseA _) =
          (puAmalgam h.le).treeGraph.dist ((g : (puAmalgam h.le).Universal) • γ)
            ((g : (puAmalgam h.le).Universal) • baseA _) := by rw [hgα]
      _ = (puAmalgam h.le).treeGraph.dist γ (baseA _) := dist_smul _ _ _ _
      _ < critDist (puAmalgam h.le) := by rw [SimpleGraph.dist_comm, hαγ, hb]; norm_num
  have hVA : V ≤ A := hVQ.trans hQA
  have hVZγ : V ≤ Subgroup.normalizer (Zγ : Set _) :=
    hVQ.trans (hQγ.trans (stab_le_normalizer_zm _ _))
  have hZγab : ⁅Zγ, Zγ⁆ = ⊥ := by
    refine Subgroup.commutator_eq_bot_iff_le_centralizer.2 ?_
    exact (zm_le_centralizer_qv _ hyp hγM).trans
      (Subgroup.centralizer_le (zm_le_qv_self _ hγM hb0))
  have hDC : D ≤ Subgroup.centralizer (Lt : Set _) := inf_le_right
  have hDQ : D ≤ Q := inf_le_left
  have hAD : A ≤ Subgroup.normalizer (D : Set _) :=
    le_normalizer_inf (stab_le_normalizer_qv _ _) (le_normalizer_centralizer hALt)
  set V₀ := ⁅V, Lt⁆ with hV₀def
  have hV₀V : V₀ ≤ V := Subgroup.le_normalizer_iff_commutator_le_left.1 (hLA.trans hAV)
  have hAV₀ : A ≤ Subgroup.normalizer (V₀ : Set _) := le_normalizer_commutator hAV hALt
  have hV₀L : ⁅V₀, Lt⁆ = V₀ := by
    have hn : A ≤ Subgroup.normalizer ((⁅V₀, Lt⁆ : Subgroup _) : Set _) :=
      le_normalizer_commutator hAV₀ hALt
    exact le_antisymm (Subgroup.le_normalizer_iff_commutator_le_left.1 (hLA.trans hAV₀))
      (S5B.commutator_le_of_perfect hperf (hVA.trans hn) (hLA.trans hn) le_rfl le_rfl)
  have hVsup : V ≤ V₀ ⊔ Zγ := by
    refine iSup_le fun g => ?_
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨l, hl, t, ht, hg⟩ := exists_mul_of_mem_stab h hαδ g.2
    have hz' : t * z * t⁻¹ ∈ Zγ :=
      (Subgroup.mem_normalizer_iff.1 (stab_le_normalizer_zm _ _ (qv_le_stab_of_adj _ hδγ ht))
        z).1 hz
    have hc' : ⁅l, t * z * t⁻¹⁆ ∈ V₀ := by
      rw [hV₀def, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hl (hZγV hz')
    have e : (MulAut.conj (g : (puAmalgam h.le).Universal)).toMonoidHom z =
        ⁅l, t * z * t⁻¹⁆ * (t * z * t⁻¹) := by
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hg]
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left hc') (Subgroup.mem_sup_right hz')
  have hV'DZ : ⁅V, V⁆ ≤ D ⊔ Zγ := by
    have hn : V ≤ Subgroup.normalizer ((D ⊔ Zγ : Subgroup _) : Set _) :=
      le_normalizer_sup (hVA.trans hAD) hVZγ
    refine (Subgroup.commutator_mono hVsup hVsup).trans
      (commutator_sup_sup_le (hV₀V.trans hn) (hZγV.trans hn) (hV₀D.trans le_sup_left) ?_
        (by rw [hZγab]; exact bot_le))
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_left.1 (hV₀V.trans hVZγ)).trans le_sup_right
  have hV'D : ⁅V, V⁆ ≤ D := by
    obtain ⟨y, hyA, hy2, hyQ, hyC⟩ := exists_crit_elt h hb hc
    have hW : ⁅V, V⁆ ≤ A := commutator_le_of_le hVA hVA
    have hWn : Lt ≤ Subgroup.normalizer ((⁅V, V⁆ : Subgroup _) : Set _) :=
      hLA.trans (le_normalizer_commutator hAV hAV)
    have hyD : y ∈ Subgroup.normalizer (D : Set _) := hAD hyA
    have hyW : ∀ w ∈ ⁅V, V⁆, y * w * y⁻¹ * w⁻¹ ∈ D := by
      intro w hw
      have hw' := hV'DZ hw
      rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left D Zγ
        (hZγV.trans (hVA.trans hAD))] at hw'
      obtain ⟨d, hdD, z, hz, rfl⟩ := hw'
      have hyz : z * y⁻¹ = y⁻¹ * z :=
        (Commute.inv_right (Subgroup.mem_centralizer_iff.1 hyC z hz)).eq
      have e : y * (d * z) * y⁻¹ * (d * z)⁻¹ = y * d * y⁻¹ * d⁻¹ := by
        calc y * (d * z) * y⁻¹ * (d * z)⁻¹ = y * d * (z * y⁻¹) * z⁻¹ * d⁻¹ := by group
          _ = y * d * (y⁻¹ * z) * z⁻¹ * d⁻¹ := by rw [hyz]
          _ = y * d * y⁻¹ * d⁻¹ := by group
      rw [e]
      exact mul_mem ((Subgroup.mem_normalizer_iff.1 hyD d).1 hdD) (inv_mem hdD)
    have h1 := commutator_le_of_two_elt_baseA h hW (hDQ.trans hQA) hWn (hLA.trans hAD) hyA hy2
      hyQ hyD hyW
    have hbot : Subgroup.normalizer ((⊥ : Subgroup (puAmalgam h.le).Universal) :
        Set (puAmalgam h.le).Universal) = ⊤ := Subgroup.normalizer_eq_top _
    have h2 : ⁅⁅V, V⁆, Lt⁆ ≤ ⊥ :=
      S5B.commutator_le_of_perfect hperf (by rw [hbot]; exact le_top) (by rw [hbot]; exact le_top)
        h1 (le_of_eq (Subgroup.commutator_eq_bot_iff_le_centralizer.2 hDC))
    exact le_inf ((commutator_le_of_le hVQ hVQ))
      (Subgroup.commutator_eq_bot_iff_le_centralizer.1 (le_bot_iff.1 h2))
  have hcomm : ⁅V₀, V ⊓ B⁆ = ⊥ := by
    have hZα : ⁅ZM _ (baseA (puAmalgam h.le)), V₀⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.2 ((zm_le_centralizer_qv _ hyp hα).trans
        (Subgroup.centralizer_le (hV₀V.trans hVQ)))
    have h1 : ⁅⁅Lt, V ⊓ B⁆, V₀⁆ = ⊥ := by
      rw [← le_bot_iff, ← hZα]
      refine Subgroup.commutator_mono ?_ le_rfl
      rw [Subgroup.commutator_comm, Subgroup.commutator_le]
      intro x hx l hl
      exact commutator_mem_zm_of_mem_bSub h (by omega) hx.2 hl
    have h2 : ⁅⁅V ⊓ B, V₀⁆, Lt⁆ = ⊥ := by
      rw [← le_bot_iff]
      calc ⁅⁅V ⊓ B, V₀⁆, Lt⁆ ≤ ⁅⁅V, V⁆, Lt⁆ :=
            Subgroup.commutator_mono (Subgroup.commutator_mono inf_le_left hV₀V) le_rfl
        _ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 (hV'D.trans hDC)
    have := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2
    rwa [hV₀L] at this
  classical
  obtain ⟨-, -, β, hβs, hβk, hβe⟩ := hnat
  let βv : (puAmalgam h.le).Universal → MSP.V4 F := fun x =>
    if hx : x ∈ V then Multiplicative.toAdd (β ⟨x, hx⟩) 0 else 0
  have hβv : ∀ x (hx : x ∈ V), βv x = Multiplicative.toAdd (β ⟨x, hx⟩) 0 := fun x hx => by
    simp [βv, hx]
  have hs : Setup A Lt V (V ⊓ B) a βv := by
    refine ⟨hLA, hALt, hAV, inf_le_left, fun x hx y hy => ?_, fun w => ?_, fun x hx => ?_,
      fun g x hx => ?_, exists_mem_puTrans_of_pow_three h ha⟩
    · rw [hβv x hx, hβv y hy, hβv _ (mul_mem hx hy)]
      rw [show (⟨x * y, mul_mem hx hy⟩ : ↥V) = ⟨x, hx⟩ * ⟨y, hy⟩ from rfl, map_mul, toAdd_mul]
      rfl
    · obtain ⟨x, hx⟩ := hβs (Multiplicative.ofAdd fun _ => w)
      refine ⟨x, x.2, ?_⟩
      rw [hβv _ x.2, Subtype.coe_eta, hx]
      rfl
    · rw [hβv x hx]
      have hker : (⟨x, hx⟩ : ↥V) ∈ β.ker ↔ x ∈ V ⊓ B := by
        rw [hβk, Subgroup.mem_subgroupOf]
      rw [← hker, MonoidHom.mem_ker]
      constructor
      · intro h0
        apply Multiplicative.toAdd.injective
        funext i
        rw [Subsingleton.elim i 0]
        exact h0
      · intro h1
        rw [h1]
        rfl
    · have hgx : (g : (puAmalgam h.le).Universal) * x * (g : (puAmalgam h.le).Universal)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hAV g.2) x).1 hx
      rw [hβv x hx, hβv _ hgx]
      simpa only [moduleAct, Bool.false_eq_true, ↓reduceIte] using hβe g ⟨x, hx⟩ ⟨_, hgx⟩ rfl 0
  have hV'V₀' : ⁅V, V⁆ ≤ ⁅V₀, V₀⁆ := by
    have hn : A ≤ Subgroup.normalizer ((⁅V₀, V₀⁆ : Subgroup _) : Set _) :=
      le_normalizer_commutator hAV₀ hAV₀
    refine (Subgroup.commutator_mono hVsup hVsup).trans
      (commutator_sup_sup_le (hV₀V.trans (hVA.trans hn)) (hZγV.trans (hVA.trans hn)) le_rfl ?_
        (by rw [hZγab]; exact bot_le))
    rw [Subgroup.commutator_le]
    intro u hu z hz
    obtain ⟨w, hw, hwz⟩ := hs.exists_comm_vec (βv z)
    have hb' : w⁻¹ * z ∈ V ⊓ B := by
      refine (hs.ker _ (mul_mem (inv_mem (hV₀V hw)) (hZγV hz))).1 ?_
      rw [hs.map_mul _ (inv_mem (hV₀V hw)) _ (hZγV hz), hs.map_inv (hV₀V hw), hwz,
        neg_add_cancel]
    have hub : ⁅u, w⁻¹ * z⁆ = 1 := by
      have := Subgroup.commutator_mem_commutator hu hb'
      rwa [hcomm, Subgroup.mem_bot] at this
    have e : ⁅u, z⁆ = ⁅u, w⁆ * (w * ⁅u, w⁻¹ * z⁆ * w⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e, hub, mul_one, mul_inv_cancel, mul_one]
    exact Subgroup.commutator_mem_commutator hu hw
  have heq : ⁅V, V⁆ = ⁅V₀, V₀⁆ := le_antisymm hV'V₀' (Subgroup.commutator_mono hV₀V hV₀V)
  refine ⟨heq, ?_⟩
  rw [heq, ← hF]
  exact hs.card_comm_le hcomm (hV₀D.trans hDC) hV₀L

end Main

end S310

end CFSG.Quasithin.MS93
