module

public import CFSG.Milestones.ASVolI.I2
public import CFSG.GroupTheory.TitsSystem.Parabolic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary
public import CFSG.Foundations.Basic
public import TauCeti.GroupTheory.Coxeter.StrongExchange

public section

namespace CFSG.ASVolI

open CFSG.Open

section burnsideI25bBN

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

theorem burnsideI25b_mul_self_mem (h : IsBNPair B N S) {ns : N}
    (hs : (ns : WeylGroup B N) ∈ S) : (ns : G) * ns ∈ B := by
  have h1 : (ns : WeylGroup B N) * ns = 1 := h.mul_self_eq_one hs
  have : ((ns * ns : N) : WeylGroup B N) = 1 := by rw [QuotientGroup.mk_mul]; exact h1
  simpa using mk_eq_one_iff.1 this

theorem burnsideI25b_exists_not_conj_mem (h : IsBNPair B N S) {ns : N}
    (hs : (ns : WeylGroup B N) ∈ S) : ∃ b ∈ B, (ns : G)⁻¹ * b * ns ∉ B := by
  by_contra hcon
  push Not at hcon
  have hsq := burnsideI25b_mul_self_mem h hs
  refine h.ne ns hs (Set.Subset.antisymm ?_ ?_)
  · rintro _ ⟨_, ⟨_, rfl, b, hb, rfl⟩, _, rfl, rfl⟩
    show (ns : G) * b * ns ∈ (B : Set G)
    have e : (ns : G) * b * ns = ((ns : G) * ns) * ((ns : G)⁻¹ * b * ns) := by group
    rw [e]
    exact B.mul_mem hsq (hcon b hb)
  · intro x hx
    refine ⟨(ns : G) * ((ns : G)⁻¹ * x * (ns : G)⁻¹), ⟨ns, rfl, (ns : G)⁻¹ * x * (ns : G)⁻¹, ?_, rfl⟩,
      ns, rfl, by group⟩
    have e : (ns : G)⁻¹ * x * (ns : G)⁻¹ = ((ns : G)⁻¹ * x * ns) * ((ns : G) * ns)⁻¹ := by group
    rw [e]
    exact B.mul_mem (hcon x hx) (B.inv_mem hsq)

theorem burnsideI25b_mem_parabolic_single_iff (h : IsBNPair B N S) {s : WeylGroup B N}
    (hs : s ∈ S) {x : G} : x ∈ parabolic B N {s} ↔ x ∈ B ∨ x ∈ dc B N s := by
  have hJ : ({s} : Set (WeylGroup B N)) ⊆ S := Set.singleton_subset_iff.2 hs
  rw [h.mem_parabolic_iff hJ]
  constructor
  · rintro ⟨w, hw, hx⟩
    rcases eq_one_or_eq_of_mem_closure_singleton (h.mul_self_eq_one hs) hw with rfl | rfl
    · left; exact mem_dc_one.1 hx
    · right; exact hx
  · rintro (hx | hx)
    · exact ⟨1, Subgroup.one_mem _, mem_dc_one.2 hx⟩
    · exact ⟨s, Subgroup.subset_closure rfl, hx⟩

theorem burnsideI25b_mem_parabolic_lift (h : IsBNPair B N S) {ns : N}
    (hs : (ns : WeylGroup B N) ∈ S) : (ns : G) ∈ parabolic B N {(ns : WeylGroup B N)} :=
  (burnsideI25b_mem_parabolic_single_iff h hs).2 (Or.inr (coe_mem_dc ns))

theorem burnsideI25b_stab_panel (h : IsBNPair B N S) {n ns : N} (hs : (ns : WeylGroup B N) ∈ S)
    (hlen : wordLength S (n : WeylGroup B N) <
      wordLength S ((n : WeylGroup B N) * (ns : WeylGroup B N))) :
    ∃ u ∈ B, (n : G)⁻¹ * u * n ∈ B ∧ ((n : G) * ns)⁻¹ * u * ((n : G) * ns) ∉ B := by
  obtain ⟨b₀, hb₀, hb₀'⟩ := burnsideI25b_exists_not_conj_mem h hs
  have hxmem : (n : G) * (b₀ * ns) ∈
      dc B N ((n : WeylGroup B N) * (ns : WeylGroup B N)) := by
    have h1 : (n : G) ∈ dc B N (n : WeylGroup B N) := coe_mem_dc n
    have h2 : b₀ * (ns : G) ∈ dc B N (ns : WeylGroup B N) := by
      have := mul_mem_dc (coe_mem_dc ns) hb₀ B.one_mem
      simpa using this
    rw [← h.dc_mul_dc_of_lt_right hs hlen]
    exact Set.mul_mem_mul h1 h2
  obtain ⟨b₁, hb₁, b₂, hb₂, heq⟩ := (mem_dc_of_lift (n := n * ns)
    (by rw [QuotientGroup.mk_mul])).1 hxmem
  rw [Subgroup.coe_mul] at heq
  have hb₁eq : b₁ = (n : G) * b₀ * ns * b₂⁻¹ * (ns : G)⁻¹ * (n : G)⁻¹ := by
    calc b₁ = (b₁ * ((n : G) * ns) * b₂) * b₂⁻¹ * ((n : G) * ns)⁻¹ := by group
      _ = _ := by rw [← heq]; group
  have hy : (n : G)⁻¹ * b₁ * n = b₀ * ns * b₂⁻¹ * (ns : G)⁻¹ := by
    rw [hb₁eq]; group
  have hyP : (n : G)⁻¹ * b₁ * n ∈ parabolic B N {(ns : WeylGroup B N)} := by
    rw [hy]
    have hP := burnsideI25b_mem_parabolic_lift h hs
    have hBP : B ≤ parabolic B N {(ns : WeylGroup B N)} :=
      h.le_parabolic (Set.singleton_subset_iff.2 hs)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBP hb₀) hP)
      (hBP (B.inv_mem hb₂))) (Subgroup.inv_mem _ hP)
  have hyB : (n : G)⁻¹ * b₁ * n ∈ B := by
    rcases (burnsideI25b_mem_parabolic_single_iff h hs).1 hyP with hB | hdc
    · exact hB
    · exfalso
      have hm1 : (n : G) * ((n : G)⁻¹ * b₁ * n) ∈
          dc B N (n : WeylGroup B N) * dc B N (ns : WeylGroup B N) :=
        Set.mul_mem_mul (coe_mem_dc n) hdc
      rw [h.dc_mul_dc_of_lt_right hs hlen] at hm1
      have hm2 : (n : G) * ((n : G)⁻¹ * b₁ * n) ∈ dc B N (n : WeylGroup B N) := by
        have e : (n : G) * ((n : G)⁻¹ * b₁ * n) = b₁ * n * 1 := by group
        rw [e]
        exact mul_mem_dc (coe_mem_dc n) hb₁ B.one_mem
      have h3 := h.eq_of_mem_dc hm1 hm2
      have h4 : (ns : WeylGroup B N) = 1 := by
        have h5 : (n : WeylGroup B N) * (ns : WeylGroup B N) = (n : WeylGroup B N) * 1 := by
          rw [mul_one]; exact h3
        exact mul_left_cancel h5
      exact h.ne_one hs h4
  refine ⟨b₁, hb₁, hyB, fun hcontra => ?_⟩
  apply hb₀'
  have e : (ns : G)⁻¹ * b₀ * ns = (((n : G) * ns)⁻¹ * b₁ * ((n : G) * ns)) * b₂ := by
    have : ((n : G) * ns)⁻¹ * b₁ * ((n : G) * ns) = (ns : G)⁻¹ * ((n : G)⁻¹ * b₁ * n) * ns := by
      group
    rw [this, hy]; group
  rw [e]
  exact B.mul_mem hcontra hb₂

theorem burnsideI25b_fix_first (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S)
    {ns n'' : N} (hns : (ns : WeylGroup B N) = s)
    (hlen : wordLength S (n'' : WeylGroup B N) < wordLength S (s * (n'' : WeylGroup B N)))
    {u : G} (hu : u ∈ B) (hfix : ((ns : G) * n'')⁻¹ * u * ((ns : G) * n'') ∈ B) :
    (ns : G)⁻¹ * u * ns ∈ B := by
  subst hns
  have hyP : (ns : G)⁻¹ * u * ns ∈ parabolic B N {(ns : WeylGroup B N)} := by
    have hP := burnsideI25b_mem_parabolic_lift h hs
    have hBP : B ≤ parabolic B N {(ns : WeylGroup B N)} :=
      h.le_parabolic (Set.singleton_subset_iff.2 hs)
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hP) (hBP hu)) hP
  rcases (burnsideI25b_mem_parabolic_single_iff h hs).1 hyP with hB | hdc
  · exact hB
  · exfalso
    have hm1 : ((ns : G)⁻¹ * u * ns) * n'' ∈
        dc B N (ns : WeylGroup B N) * dc B N (n'' : WeylGroup B N) :=
      Set.mul_mem_mul hdc (coe_mem_dc n'')
    rw [h.dc_mul_dc_of_lt hs hlen] at hm1
    have hm2 : ((ns : G)⁻¹ * u * ns) * n'' ∈ dc B N (n'' : WeylGroup B N) := by
      have e : ((ns : G)⁻¹ * u * ns) * n'' = 1 * (n'' : G) *
          (((ns : G) * n'')⁻¹ * u * ((ns : G) * n'')) := by group
      rw [e]
      exact mul_mem_dc (coe_mem_dc n'') B.one_mem hfix
    have h3 := h.eq_of_mem_dc hm1 hm2
    have h4 : (ns : WeylGroup B N) = 1 := by
      have h5 : (ns : WeylGroup B N) * (n'' : WeylGroup B N) =
          1 * (n'' : WeylGroup B N) := by rw [one_mul]; exact h3
      exact mul_right_cancel h5
    exact h.ne_one hs h4

theorem burnsideI25b_exists_min_coset (S J : Set (WeylGroup B N)) (w : WeylGroup B N) :
    ∃ x ∈ Subgroup.closure J, ∀ y ∈ Subgroup.closure J,
      wordLength S (x * w) ≤ wordLength S (y * w) := by
  classical
  have hne : ∃ k, ∃ y ∈ Subgroup.closure J, wordLength S (y * w) = k :=
    ⟨_, 1, Subgroup.one_mem _, rfl⟩
  obtain ⟨y₀, hy₀, hy₀k⟩ := Nat.find_spec hne
  refine ⟨y₀, hy₀, fun y hy => ?_⟩
  rw [hy₀k]
  exact Nat.find_min' hne ⟨y, hy, rfl⟩

theorem burnsideI25b_mem_of_fix (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {R : Subgroup G} (hRB : R ≤ B)
    (hRP : ∀ x ∈ parabolic B N J, ∀ r ∈ R, x⁻¹ * r * x ∈ R)
    (hZ : ∀ s ∈ S, s ∉ J → ∀ ns : N, (ns : WeylGroup B N) = s →
      ∃ r ∈ R, (ns : G)⁻¹ * r * ns ∉ B)
    {g : G} (hg : ∀ r ∈ R, g⁻¹ * r * g ∈ B) : g ∈ parabolic B N J := by
  have hBP : B ≤ parabolic B N J := h.le_parabolic hJ
  obtain ⟨w, hw⟩ := h.exists_mem_dc g
  obtain ⟨n, hn, b₁, hb₁, b₂, hb₂, rfl⟩ := mem_dc_iff.1 hw
  have hfixn : ∀ r ∈ R, (n : G)⁻¹ * r * n ∈ B := by
    intro r hr
    have hr' : b₁ * r * b₁⁻¹ ∈ R := by
      have := hRP b₁⁻¹ (hBP (B.inv_mem hb₁)) r hr
      simpa using this
    have h1 := hg _ hr'
    have e : (n : G)⁻¹ * r * n = b₂ *
        ((b₁ * (n : G) * b₂)⁻¹ * (b₁ * r * b₁⁻¹) * (b₁ * (n : G) * b₂)) * b₂⁻¹ := by group
    rw [e]
    exact B.mul_mem (B.mul_mem hb₂ h1) (B.inv_mem hb₂)
  suffices hwJ : (n : WeylGroup B N) ∈ Subgroup.closure J by
    have h1 : (n : G) ∈ parabolic B N J :=
      (h.mem_parabolic_iff_of_mem_dc hJ (coe_mem_dc n)).2 hwJ
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hBP hb₁) h1) (hBP hb₂)
  by_contra hnJ
  obtain ⟨x₀, hx₀, hx₀min⟩ := burnsideI25b_exists_min_coset S J (n : WeylGroup B N)
  obtain ⟨nx, hnx⟩ := QuotientGroup.mk_surjective x₀
  have hnxP : (nx : G) ∈ parabolic B N J := by
    refine (h.mem_parabolic_iff_of_mem_dc hJ (coe_mem_dc nx)).2 ?_
    rw [hnx]; exact hx₀
  obtain ⟨n', hn'⟩ : ∃ n' : N, n' = nx * n := ⟨_, rfl⟩
  have hn'W : (n' : WeylGroup B N) = x₀ * (n : WeylGroup B N) := by
    rw [hn', QuotientGroup.mk_mul, hnx]
  have hfixn' : ∀ r ∈ R, (n' : G)⁻¹ * r * n' ∈ B := by
    intro r hr
    have hr1 : (nx : G)⁻¹ * r * nx ∈ R := hRP _ hnxP r hr
    have h1 := hfixn _ hr1
    have e : (n' : G)⁻¹ * r * n' = (n : G)⁻¹ * ((nx : G)⁻¹ * r * nx) * n := by
      rw [hn', Subgroup.coe_mul]; group
    rw [e]; exact h1
  have hv₀1 : x₀ * (n : WeylGroup B N) ≠ 1 := by
    intro h1
    apply hnJ
    have h2 : (n : WeylGroup B N) = x₀⁻¹ := by
      calc (n : WeylGroup B N) = x₀⁻¹ * (x₀ * (n : WeylGroup B N)) := by group
        _ = x₀⁻¹ := by rw [h1, mul_one]
    rw [h2]; exact Subgroup.inv_mem _ hx₀
  obtain ⟨s, hsS, hdesc⟩ := exists_left_descent h.bnCore.mul_self_eq_one
    (h.mem_closure (x₀ * (n : WeylGroup B N))) hv₀1
  have hsJ : s ∉ J := by
    intro hsJ
    have hmin := hx₀min (s * x₀) (Subgroup.mul_mem _ (Subgroup.subset_closure hsJ) hx₀)
    rw [mul_assoc] at hmin
    omega
  obtain ⟨ns, hns⟩ := QuotientGroup.mk_surjective s
  obtain ⟨n'', hn''⟩ : ∃ n'' : N, n'' = ns⁻¹ * n' := ⟨_, rfl⟩
  have hn''W : (n'' : WeylGroup B N) = s * (x₀ * (n : WeylGroup B N)) := by
    rw [hn'', QuotientGroup.mk_mul, QuotientGroup.mk_inv, hns, hn'W, h.inv_eq_self hsS]
  have hlen : wordLength S (n'' : WeylGroup B N) < wordLength S (s * (n'' : WeylGroup B N)) := by
    have e : s * (s * (x₀ * (n : WeylGroup B N))) = x₀ * (n : WeylGroup B N) := by
      rw [← mul_assoc, h.mul_self_eq_one hsS, one_mul]
    rw [hn''W, e]
    omega
  have hnn'' : (ns : G) * n'' = n' := by
    rw [hn'']; simp
  have hrfix : ∀ r ∈ R, (ns : G)⁻¹ * r * ns ∈ B := by
    intro r hr
    refine burnsideI25b_fix_first h hsS hns hlen (hRB hr) ?_
    rw [hnn'']
    exact hfixn' r hr
  obtain ⟨r, hr, hrn⟩ := hZ s hsS hsJ ns hns
  exact hrn (hrfix r hr)

theorem burnsideI25b_length_lt_mul_right (h : IsBNPair B N S) {J : Set (WeylGroup B N)}
    (hJ : J ⊆ S) {w s : WeylGroup B N} (hw : w ∈ Subgroup.closure J) (hs : s ∈ S) (hsJ : s ∉ J) :
    wordLength S w < wordLength S (w * s) := by
  by_contra hcon
  push Not at hcon
  have hinv : wordLength S (s * w⁻¹) = wordLength S (w * s) := by
    have := h.length_inv (w * s)
    rw [mul_inv_rev, h.inv_eq_self hs] at this
    exact this
  have hor := h.length_mul_eq_or hs w⁻¹
  have hlinv : wordLength S w⁻¹ = wordLength S w := h.length_inv w
  have hne := h.length_mul_ne hs w⁻¹
  have hlt : wordLength S (s * w⁻¹) + 1 = wordLength S w⁻¹ := by omega
  have hwinv : w⁻¹ ∈ Subgroup.closure J := Subgroup.inv_mem _ hw
  obtain ⟨ns, hns⟩ := QuotientGroup.mk_surjective s
  have hdc : ∀ x ∈ dc B N s, x ∈ parabolic B N J := by
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := h.bnCore.dc_subset_mul_inv hs (h.mem_closure w⁻¹) hlt x hx
    exact (parabolic B N J).mul_mem (h.dc_subset_parabolic hJ hwinv ha)
      ((parabolic B N J).inv_mem (h.dc_subset_parabolic hJ hwinv hb))
  have hnsP : (ns : G) ∈ parabolic B N J := hdc _ (hns ▸ coe_mem_dc ns)
  have hsJ' : s ∈ Subgroup.closure J :=
    (h.mem_parabolic_iff_of_mem_dc hJ (hns ▸ coe_mem_dc ns)).1 hnsP
  exact hsJ (h.mem_of_mem_closure hJ hs hsJ')

theorem burnsideI25b_exists_max [Finite G] (S J : Set (WeylGroup B N)) :
    ∃ n : N, (n : WeylGroup B N) ∈ Subgroup.closure J ∧
      ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S (n : WeylGroup B N) := by
  have hfin : (Subgroup.closure J : Set (WeylGroup B N)).Finite := Set.toFinite _
  obtain ⟨w₀, hw₀, hmax⟩ := Set.exists_max_image (Subgroup.closure J : Set (WeylGroup B N))
    (wordLength S) hfin ⟨1, Subgroup.one_mem _⟩
  obtain ⟨n, rfl⟩ := QuotientGroup.mk_surjective w₀
  exact ⟨n, hw₀, fun w hw => hmax w hw⟩

theorem burnsideI25b_conj_mem_H {c x : G} (hc : c ∈ B ⊓ N) (hx : x ∈ N) :
    x * c * x⁻¹ ∈ B ⊓ N := by
  have hmem : (⟨c, (Subgroup.mem_inf.1 hc).2⟩ : N) ∈ (B ⊓ N).subgroupOf N :=
    Subgroup.mem_subgroupOf.2 hc
  have := (inferInstance : ((B ⊓ N).subgroupOf N).Normal).conj_mem _ hmem ⟨x, hx⟩
  exact Subgroup.mem_subgroupOf.1 this

@[expose] def burnsideI25b_LeviAt (p : ℕ) (B N U : Subgroup G) [(cartan B N).Normal]
    (S J : Set (WeylGroup B N)) : Prop :=
  ∀ n : N, (n : WeylGroup B N) ∈ Subgroup.closure J →
    (∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S (n : WeylGroup B N)) →
    ∀ u ∈ U, (n : G)⁻¹ * u * n ∈ B → u ∈ pCoreOf p (parabolic B N J)

@[expose] def burnsideI25b_Levi (p : ℕ) (B N U : Subgroup G) [(cartan B N).Normal]
    (S : Set (WeylGroup B N)) : Prop :=
  ∀ J ⊆ S, burnsideI25b_LeviAt p B N U S J

end burnsideI25bBN

section burnsideI25bPCore

variable {G : Type} [Group G]

theorem burnsideI25b_pCoreOf_le (p : ℕ) (P : Subgroup G) : pCoreOf p P ≤ P :=
  Subgroup.map_subtype_le _

theorem burnsideI25b_pCoreOf_isPGroup (p : ℕ) (P : Subgroup G) : IsPGroup p (pCoreOf p P) :=
  (CFSG.pCore_isPGroup (p := p) (G := P)).map P.subtype

theorem burnsideI25b_pCoreOf_conj_mem (p : ℕ) {P : Subgroup G} {x r : G} (hx : x ∈ P)
    (hr : r ∈ pCoreOf p P) : x * r * x⁻¹ ∈ pCoreOf p P := by
  obtain ⟨r₀, hr₀, rfl⟩ := Subgroup.mem_map.1 hr
  refine Subgroup.mem_map.2 ⟨⟨x, hx⟩ * r₀ * ⟨x, hx⟩⁻¹, ?_, by simp⟩
  exact (CFSG.pCore_normal (p := p) (G := P)).conj_mem r₀ hr₀ ⟨x, hx⟩

theorem burnsideI25b_pCoreOf_le_sylow {p : ℕ} (P : Subgroup G) (V : Sylow p G)
    (hVP : (V : Subgroup G) ≤ P) : pCoreOf p P ≤ V := by
  have hR := burnsideI25b_pCoreOf_isPGroup p P
  have hnorm : (V : Subgroup G) ≤ Subgroup.normalizer (pCoreOf p P) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro r
    constructor
    · intro hr; exact burnsideI25b_pCoreOf_conj_mem p (hVP hv) hr
    · intro hr
      have := burnsideI25b_pCoreOf_conj_mem p (P.inv_mem (hVP hv)) hr
      simpa [mul_assoc] using this
  have hsup := hR.to_sup_of_normal_left' V.isPGroup' hnorm
  have := V.is_maximal' hsup le_sup_right
  exact this ▸ le_sup_left

theorem burnsideI25b_mem_smul_sylow {p : ℕ} (g : G) (P : Sylow p G) (x : G) :
    x ∈ ((g • P : Sylow p G) : Subgroup G) ↔ g⁻¹ * x * g ∈ (P : Subgroup G) := by
  rw [Sylow.coe_subgroup_smul, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
  simp [MulAut.smul_def, MulAut.conj_apply]

theorem burnsideI25b_mem_conjugate {A : Subgroup G} {g x : G} :
    x ∈ CFSG.conjugate A g ↔ g * x * g⁻¹ ∈ A := by
  rw [CFSG.conjugate, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro h
    exact ⟨g * x * g⁻¹, h, by simp [MulAut.conj_apply, mul_assoc]⟩

theorem burnsideI25b_conjugate_conjugate (A : Subgroup G) (x g : G) :
    CFSG.conjugate (CFSG.conjugate A x) g = CFSG.conjugate A (x * g) := by
  ext z
  rw [burnsideI25b_mem_conjugate, burnsideI25b_mem_conjugate, burnsideI25b_mem_conjugate]
  have e : x * (g * z * g⁻¹) * x⁻¹ = (x * g) * z * (x * g)⁻¹ := by group
  rw [e]

theorem burnsideI25b_conjugate_one (A : Subgroup G) : CFSG.conjugate A 1 = A := by
  ext z
  rw [burnsideI25b_mem_conjugate]
  simp

theorem burnsideI25b_conjugate_inj {A A' : Subgroup G} {y : G}
    (h : CFSG.conjugate A y = CFSG.conjugate A' y) : A = A' := by
  calc A = CFSG.conjugate (CFSG.conjugate A y) y⁻¹ := by
        rw [burnsideI25b_conjugate_conjugate, mul_inv_cancel, burnsideI25b_conjugate_one]
    _ = CFSG.conjugate (CFSG.conjugate A' y) y⁻¹ := by rw [h]
    _ = A' := by
        rw [burnsideI25b_conjugate_conjugate, mul_inv_cancel, burnsideI25b_conjugate_one]

theorem burnsideI25b_pCoreOf_map (p : ℕ) (φ : G ≃* G) (H : Subgroup G) :
    pCoreOf p (H.map φ.toMonoidHom) = (pCoreOf p H).map φ.toMonoidHom := by
  set e : H ≃* H.map φ.toMonoidHom :=
    Subgroup.equivMapOfInjective H φ.toMonoidHom φ.injective with he
  have h1 := CFSG.pCore_map_iso p e
  unfold pCoreOf
  rw [← h1, Subgroup.map_map, Subgroup.map_map]
  congr 1

theorem burnsideI25b_pCoreOf_conjugate (p : ℕ) (P : Subgroup G) (x : G) :
    pCoreOf p (CFSG.conjugate P x) = CFSG.conjugate (pCoreOf p P) x :=
  burnsideI25b_pCoreOf_map p (MulAut.conj x⁻¹) P

theorem burnsideI25b_le_pCoreOf (p : ℕ) {P Q : Subgroup G} (hQP : Q ≤ P) (hQp : IsPGroup p Q)
    (hQn : ∀ x ∈ P, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) : Q ≤ pCoreOf p P := by
  have hN : (Q.subgroupOf P).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hQn g g.2 n hn
  have hp : IsPGroup p (Q.subgroupOf P) := hQp.comap_subtype
  have hle : Q.subgroupOf P ≤ CFSG.pCore p P := by
    unfold CFSG.pCore
    exact le_sSup ⟨hN, hp⟩
  intro q hq
  exact Subgroup.mem_map.2 ⟨⟨q, hQP hq⟩, hle (Subgroup.mem_subgroupOf.2 hq), rfl⟩

theorem burnsideI25b_pElem_mem {p : ℕ} (hp : p.Prime) {B U : Subgroup G} (V : Sylow p G)
    (hV : (V : Subgroup G) = U) (hBn : B ≤ Subgroup.normalizer U) {x : G} (hx : x ∈ B)
    (k : ℕ) (hk : x ^ (p ^ k) = 1) : x ∈ U := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : orderOf x ∣ p ^ k := orderOf_dvd_of_pow_eq_one hk
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow hp).1 hdvd
  have hQ : IsPGroup p (Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := m) ?_
    rw [Nat.card_zpowers, hm]
  have hnorm : Subgroup.zpowers x ≤ Subgroup.normalizer U :=
    (Subgroup.zpowers_le.2 (hBn hx))
  have hsup : IsPGroup p (U ⊔ Subgroup.zpowers x : Subgroup G) := by
    refine IsPGroup.to_sup_of_normal_left' ?_ hQ hnorm
    rw [← hV]; exact V.isPGroup'
  have h1 : U ⊔ Subgroup.zpowers x = U := by
    have := V.is_maximal' (Q := U ⊔ Subgroup.zpowers x) (hV ▸ hsup) (hV ▸ le_sup_left)
    rw [hV] at this
    exact this
  have : x ∈ U ⊔ Subgroup.zpowers x := Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rwa [h1] at this

end burnsideI25bPCore

section burnsideI25bMain

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

theorem burnsideI25b_Z_of_levi [Finite G] (h : IsBNPair B N S) {p : ℕ} {U : Subgroup G}
    (hBU : ∀ b ∈ B, ∃ a ∈ U, ∃ c ∈ B ⊓ N, b = a * c)
    (hLevi : burnsideI25b_Levi p B N U S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S) :
    ∀ s ∈ S, s ∉ J → ∀ ns : N, (ns : WeylGroup B N) = s →
      ∃ r ∈ pCoreOf p (parabolic B N J), (ns : G)⁻¹ * r * ns ∉ B := by
  intro s hsS hsJ ns hns
  obtain ⟨n, hnJ, hnmax⟩ := burnsideI25b_exists_max (B := B) (N := N) S J
  have hlen : wordLength S (n : WeylGroup B N) <
      wordLength S ((n : WeylGroup B N) * (ns : WeylGroup B N)) := by
    rw [hns]; exact burnsideI25b_length_lt_mul_right h hJ hnJ hsS hsJ
  have hnsS : (ns : WeylGroup B N) ∈ S := hns ▸ hsS
  obtain ⟨u, hu, hu1, hu2⟩ := burnsideI25b_stab_panel h hnsS hlen
  obtain ⟨a, ha, c, hc, rfl⟩ := hBU u hu
  have hnN : (n : G) ∈ N := n.2
  have hc1 : (n : G)⁻¹ * c⁻¹ * n ∈ B := by
    have := burnsideI25b_conj_mem_H (B := B) (N := N) ((B ⊓ N).inv_mem hc) (N.inv_mem hnN)
    simpa using (Subgroup.mem_inf.1 this).1
  have hn1 : (n : G)⁻¹ * a * n ∈ B := by
    have e : (n : G)⁻¹ * a * n = ((n : G)⁻¹ * (a * c) * n) * ((n : G)⁻¹ * c⁻¹ * n) := by group
    rw [e]; exact B.mul_mem hu1 hc1
  have hnns : (n : G) * ns ∈ N := N.mul_mem hnN ns.2
  have hc2 : ((n : G) * ns)⁻¹ * c * ((n : G) * ns) ∈ B := by
    have := burnsideI25b_conj_mem_H (B := B) (N := N) hc (N.inv_mem hnns)
    simpa using (Subgroup.mem_inf.1 this).1
  have hnotB : ((n : G) * ns)⁻¹ * a * ((n : G) * ns) ∉ B := by
    intro hB
    apply hu2
    have e : ((n : G) * ns)⁻¹ * (a * c) * ((n : G) * ns) =
        (((n : G) * ns)⁻¹ * a * ((n : G) * ns)) * (((n : G) * ns)⁻¹ * c * ((n : G) * ns)) := by
      group
    rw [e]; exact B.mul_mem hB hc2
  have haR : a ∈ pCoreOf p (parabolic B N J) := hLevi J hJ n hnJ hnmax a ha hn1
  have hnP : (n : G) ∈ parabolic B N J :=
    (h.mem_parabolic_iff_of_mem_dc hJ (coe_mem_dc n)).2 hnJ
  refine ⟨(n : G)⁻¹ * a * n, ?_, ?_⟩
  · have := burnsideI25b_pCoreOf_conj_mem p ((parabolic B N J).inv_mem hnP) haR
    simpa using this
  · intro hB
    apply hnotB
    have e : (ns : G)⁻¹ * ((n : G)⁻¹ * a * n) * ns = ((n : G) * ns)⁻¹ * a * ((n : G) * ns) := by
      group
    rw [← e]; exact hB

theorem burnsideI25b_weaklyClosed_std [Finite G] {p : ℕ} [Fact p.Prime] (h : IsBNPair B N S)
    {J : Set (WeylGroup B N)} (hJ : J ⊆ S) (U : Sylow p G) (hUB : (U : Subgroup G) ≤ B)
    (hZ : ∀ s ∈ S, s ∉ J → ∀ ns : N, (ns : WeylGroup B N) = s →
      ∃ r ∈ pCoreOf p (parabolic B N J), (ns : G)⁻¹ * r * ns ∉ B)
    {T : Subgroup G} (hT : IsPGroup p T) (hRT : pCoreOf p (parabolic B N J) ≤ T) :
    ∀ g : G, CFSG.conjugate (pCoreOf p (parabolic B N J)) g ≤ T →
      CFSG.conjugate (pCoreOf p (parabolic B N J)) g = pCoreOf p (parabolic B N J) := by
  have hBP : B ≤ parabolic B N J := h.le_parabolic hJ
  have hUP : (U : Subgroup G) ≤ parabolic B N J := hUB.trans hBP
  have hRU : pCoreOf p (parabolic B N J) ≤ U := burnsideI25b_pCoreOf_le_sylow _ U hUP
  have hRB : pCoreOf p (parabolic B N J) ≤ B := hRU.trans hUB
  have hRP : ∀ x ∈ parabolic B N J, ∀ r ∈ pCoreOf p (parabolic B N J),
      x⁻¹ * r * x ∈ pCoreOf p (parabolic B N J) := by
    intro x hx r hr
    have := burnsideI25b_pCoreOf_conj_mem p ((parabolic B N J).inv_mem hx) hr
    simpa using this
  intro g hg
  obtain ⟨Q, hTQ⟩ := hT.exists_le_sylow
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G U Q
  have hmemQ : ∀ x ∈ T, y⁻¹ * x * y ∈ (U : Subgroup G) := by
    intro x hx
    have : x ∈ ((y • U : Sylow p G) : Subgroup G) := by rw [hy]; exact hTQ hx
    exact (burnsideI25b_mem_smul_sylow y U x).1 this
  have hyP : y ∈ parabolic B N J := by
    refine burnsideI25b_mem_of_fix h hJ hRB hRP hZ (g := y) fun r hr => ?_
    exact hUB (hmemQ r (hRT hr))
  have hgyP : g * y ∈ parabolic B N J := by
    refine burnsideI25b_mem_of_fix h hJ hRB hRP hZ (g := g * y) fun r hr => ?_
    have h1 : g⁻¹ * r * g ∈ CFSG.conjugate (pCoreOf p (parabolic B N J)) g := by
      rw [burnsideI25b_mem_conjugate]
      have e : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
      rw [e]; exact hr
    have h2 := hmemQ _ (hg h1)
    have e : (g * y)⁻¹ * r * (g * y) = y⁻¹ * (g⁻¹ * r * g) * y := by group
    rw [e]
    exact hUB h2
  have hgP : g ∈ parabolic B N J := by
    have := (parabolic B N J).mul_mem hgyP ((parabolic B N J).inv_mem hyP)
    simpa using this
  ext x
  rw [burnsideI25b_mem_conjugate]
  constructor
  · intro hx
    have := hRP g hgP _ hx
    simpa [mul_assoc] using this
  · intro hx
    have := hRP g⁻¹ ((parabolic B N J).inv_mem hgP) x hx
    simpa [mul_assoc] using this

theorem burnsideI25b_weaklyClosed_of_Z [Finite G] {p : ℕ} [Fact p.Prime] (h : IsBNPair B N S)
    (U : Sylow p G) (hUB : Subgroup.normalizer (U : Subgroup G) = B)
    (hZ : ∀ J ⊆ S, ∀ s ∈ S, s ∉ J → ∀ ns : N, (ns : WeylGroup B N) = s →
      ∃ r ∈ pCoreOf p (parabolic B N J), (ns : G)⁻¹ * r * ns ∉ B)
    {P : Subgroup G} (hP : ∃ V : Sylow p G, Subgroup.normalizer (V : Subgroup G) ≤ P)
    {T : Subgroup G} (hT : IsPGroup p T) (hRT : pCoreOf p P ≤ T) :
    ∀ g : G, CFSG.conjugate (pCoreOf p P) g ≤ T →
      CFSG.conjugate (pCoreOf p P) g = pCoreOf p P := by
  obtain ⟨V, hV⟩ := hP
  obtain ⟨y, hy⟩ := MulAction.exists_smul_eq G U V
  have hBP' : B ≤ CFSG.conjugate P y := by
    intro b hb
    rw [burnsideI25b_mem_conjugate]
    apply hV
    rw [Subgroup.mem_normalizer_iff]
    intro v
    have hb' : b ∈ Subgroup.normalizer (U : Subgroup G) := hUB ▸ hb
    rw [Subgroup.mem_normalizer_iff] at hb'
    rw [← hy, burnsideI25b_mem_smul_sylow, burnsideI25b_mem_smul_sylow]
    have h1 := hb' (y⁻¹ * v * y)
    have e : y⁻¹ * (y * b * y⁻¹ * v * (y * b * y⁻¹)⁻¹) * y = b * (y⁻¹ * v * y) * b⁻¹ := by
      group
    rw [e]
    exact h1
  obtain ⟨J, hJ, hPJ⟩ := h.exists_parabolic hBP'
  have hR : pCoreOf p (parabolic B N J) = CFSG.conjugate (pCoreOf p P) y := by
    rw [← hPJ, burnsideI25b_pCoreOf_conjugate]
  have hUB' : (U : Subgroup G) ≤ B := hUB ▸ Subgroup.le_normalizer
  have hT' : IsPGroup p (CFSG.conjugate T y) := hT.map _
  have hRT' : pCoreOf p (parabolic B N J) ≤ CFSG.conjugate T y := by
    rw [hR]; exact Subgroup.map_mono hRT
  have key := burnsideI25b_weaklyClosed_std h hJ U hUB' (hZ J hJ) hT' hRT'
  intro g hg
  have h1 : CFSG.conjugate (pCoreOf p (parabolic B N J)) (y⁻¹ * g * y) ≤ CFSG.conjugate T y := by
    rw [hR, burnsideI25b_conjugate_conjugate]
    have e : y * (y⁻¹ * g * y) = g * y := by group
    rw [e, ← burnsideI25b_conjugate_conjugate]
    exact Subgroup.map_mono hg
  have h2 := key _ h1
  rw [hR, burnsideI25b_conjugate_conjugate] at h2
  have e : y * (y⁻¹ * g * y) = g * y := by group
  rw [e, ← burnsideI25b_conjugate_conjugate] at h2
  exact burnsideI25b_conjugate_inj h2

@[expose] def burnsideI25b_stabIn (B U : Subgroup G) (x : G) : Subgroup G where
  carrier := {c | c ∈ U ∧ x⁻¹ * c * x ∈ B}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨U.mul_mem ha hb, ?_⟩
    have e : x⁻¹ * (a * b) * x = (x⁻¹ * a * x) * (x⁻¹ * b * x) := by group
    rw [e]; exact B.mul_mem ha' hb'
  one_mem' := ⟨U.one_mem, by simpa using B.one_mem⟩
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨U.inv_mem ha, ?_⟩
    have e : x⁻¹ * a⁻¹ * x = (x⁻¹ * a * x)⁻¹ := by group
    rw [e]; exact B.inv_mem ha'

@[expose] def burnsideI25b_RankOne (B N U : Subgroup G) [(cartan B N).Normal]
    (S : Set (WeylGroup B N)) : Prop :=
  ∀ ns : N, (ns : WeylGroup B N) ∈ S → ∀ u ∈ U, ∀ c ∈ burnsideI25b_stabIn B U (ns : G),
    u * c * u⁻¹ ∈ burnsideI25b_stabIn B U (ns : G)

theorem burnsideI25b_levi_at_empty {p : ℕ} {U : Subgroup G} (hUB : U ≤ B) (hUp : IsPGroup p U)
    (hBn : B ≤ Subgroup.normalizer U) : burnsideI25b_LeviAt p B N U S ∅ := by
  intro n hn hmax u hu hun
  rw [parabolic_empty]
  exact burnsideI25b_le_pCoreOf p hUB hUp
    (fun x hx q hq => (Subgroup.mem_normalizer_iff.1 (hBn hx) q).1 hq) hu

theorem burnsideI25b_levi_at_singleton {p : ℕ} (hp : p.Prime) (h : IsBNPair B N S)
    (V : Sylow p G) {U : Subgroup G} (hV : (V : Subgroup G) = U)
    (hBn : B ≤ Subgroup.normalizer U) (hUB : U ≤ B)
    (hBU : ∀ b ∈ B, ∃ a ∈ U, ∃ c ∈ B ⊓ N, b = a * c)
    (hR : burnsideI25b_RankOne B N U S) {s : WeylGroup B N} (hs : s ∈ S) :
    burnsideI25b_LeviAt p B N U S {s} := by
  intro n hnJ hnmax u hu hun
  have hns : (n : WeylGroup B N) = s := by
    rcases eq_one_or_eq_of_mem_closure_singleton (h.mul_self_eq_one hs) hnJ with h1 | h1
    · exfalso
      have hle := hnmax s (Subgroup.subset_closure rfl)
      rw [h1, wordLength_one] at hle
      exact h.ne_one hs ((wordLength_eq_zero_iff h.bnCore.mul_self_eq_one
        (h.mem_closure s)).1 (by omega))
    · exact h1
  have hnS : (n : WeylGroup B N) ∈ S := hns ▸ hs
  have hUp : IsPGroup p U := hV ▸ V.isPGroup'
  have hnn : (n : G) * n ∈ B := burnsideI25b_mul_self_mem h hnS
  have hnN : (n : G) ∈ N := n.2
  have hH : ∀ x ∈ B ⊓ N, ∀ c ∈ burnsideI25b_stabIn B U (n : G),
      x * c * x⁻¹ ∈ burnsideI25b_stabIn B U (n : G) := by
    intro x hx c hc
    refine ⟨(Subgroup.mem_normalizer_iff.1 (hBn (Subgroup.mem_inf.1 hx).1) c).1 hc.1, ?_⟩
    have hx' := burnsideI25b_conj_mem_H (B := B) (N := N) hx (N.inv_mem hnN)
    have e : (n : G)⁻¹ * (x * c * x⁻¹) * n =
        ((n : G)⁻¹ * x * ((n : G)⁻¹)⁻¹) * ((n : G)⁻¹ * c * n) *
          ((n : G)⁻¹ * x * ((n : G)⁻¹)⁻¹)⁻¹ := by group
    rw [e]
    exact B.mul_mem (B.mul_mem (Subgroup.mem_inf.1 hx').1 hc.2)
      (B.inv_mem (Subgroup.mem_inf.1 hx').1)
  have hBnorm : ∀ b ∈ B, ∀ c ∈ burnsideI25b_stabIn B U (n : G),
      b * c * b⁻¹ ∈ burnsideI25b_stabIn B U (n : G) := by
    intro b hb c hc
    obtain ⟨a, ha, x, hx, rfl⟩ := hBU b hb
    have h1 := hH x hx c hc
    have h2 := hR n hnS a ha _ h1
    have e : a * x * c * (a * x)⁻¹ = a * (x * c * x⁻¹) * a⁻¹ := by group
    rw [e]; exact h2
  have hnnorm : ∀ c ∈ burnsideI25b_stabIn B U (n : G),
      (n : G) * c * (n : G)⁻¹ ∈ burnsideI25b_stabIn B U (n : G) := by
    intro c hc
    have hB' : (n : G) * c * (n : G)⁻¹ ∈ B := by
      have e : (n : G) * c * (n : G)⁻¹ =
          ((n : G) * n) * ((n : G)⁻¹ * c * n) * ((n : G) * n)⁻¹ := by group
      rw [e]
      exact B.mul_mem (B.mul_mem hnn hc.2) (B.inv_mem hnn)
    obtain ⟨k, hk⟩ := hUp ⟨c, hc.1⟩
    have hk' : c ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
    have hpow : ((n : G) * c * (n : G)⁻¹) ^ (p ^ k) = 1 := by
      rw [conj_pow, hk']; simp
    have hU' := burnsideI25b_pElem_mem hp V hV hBn hB' k hpow
    refine ⟨hU', ?_⟩
    have e : (n : G)⁻¹ * ((n : G) * c * (n : G)⁻¹) * n = c := by group
    rw [e]; exact hUB hc.1
  have hKP : burnsideI25b_stabIn B U (n : G) ≤ parabolic B N {s} := fun c hc =>
    (h.le_parabolic (Set.singleton_subset_iff.2 hs)) (hUB hc.1)
  have hKn : ∀ x ∈ parabolic B N {s}, ∀ q ∈ burnsideI25b_stabIn B U (n : G),
      x * q * x⁻¹ ∈ burnsideI25b_stabIn B U (n : G) := by
    intro x hx q hq
    rcases (burnsideI25b_mem_parabolic_single_iff h hs).1 hx with hxB | hxd
    · exact hBnorm x hxB q hq
    · obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift (n := n) hns).1 hxd
      have h1 := hBnorm b₂ hb₂ q hq
      have h2 := hnnorm _ h1
      have h3 := hBnorm b₁ hb₁ _ h2
      have e : b₁ * (n : G) * b₂ * q * (b₁ * (n : G) * b₂)⁻¹ =
          b₁ * ((n : G) * (b₂ * q * b₂⁻¹) * (n : G)⁻¹) * b₁⁻¹ := by group
      rw [e]; exact h3
  have hKp : IsPGroup p (burnsideI25b_stabIn B U (n : G)) := by
    intro g
    obtain ⟨k, hk⟩ := hUp ⟨(g : G), g.2.1⟩
    refine ⟨k, Subtype.ext ?_⟩
    have := congrArg Subtype.val hk
    simpa using this
  exact burnsideI25b_le_pCoreOf p hKP hKp hKn ⟨hu, hun⟩

end burnsideI25bMain

section burnsideI25bWrap

open scoped Pointwise

variable {G : Type} [Group G]

theorem burnsideI25b_decomp {B U H : Subgroup G} (hUB : U ≤ B) (hHB : H ≤ B)
    (hUn : (U.subgroupOf B).Normal) (hUH : U ⊔ H = B) :
    ∀ b ∈ B, ∃ a ∈ U, ∃ c ∈ H, b = a * c := by
  intro b hb
  have h1 : (U.subgroupOf B) ⊔ (H.subgroupOf B) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hUB hHB, hUH, Subgroup.subgroupOf_self]
  have hx : (⟨b, hb⟩ : B) ∈ (U.subgroupOf B) ⊔ (H.subgroupOf B) := by rw [h1]; trivial
  have h2 := Subgroup.normal_mul (U.subgroupOf B) (H.subgroupOf B)
  have h3 : (⟨b, hb⟩ : B) ∈ ((U.subgroupOf B : Subgroup B) : Set B) * (H.subgroupOf B : Set B) := by
    rw [← h2]; exact hx
  obtain ⟨a, ha, c, hc, hac⟩ := Set.mem_mul.1 h3
  refine ⟨a, ha, c, hc, ?_⟩
  have := congrArg Subtype.val hac
  simpa using this.symm

end burnsideI25bWrap

section burnsideI25cWeyl

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}

theorem burnsideI25c_cslength_eq (h : IsBNPair B N S)
    (cs : CoxeterSystem (orderMatrix h.orderOf_eq_two) (WeylGroup B N))
    (hcs : ∀ s : S, cs.simple s = s) (w : WeylGroup B N) :
    cs.length w = wordLength S w := by
  apply le_antisymm
  · obtain ⟨l, hl, hlen, hprod⟩ :=
      exists_list_length_eq_wordLength h.bnCore.mul_self_eq_one (h.mem_closure w)
    let ω : List S := l.pmap Subtype.mk hl
    have hω : cs.wordProd ω = w := by
      unfold CoxeterSystem.wordProd
      rw [List.map_congr_left (fun s _ => hcs s)]
      rw [List.map_pmap, List.pmap_eq_map, List.map_id', hprod]
    calc cs.length w = cs.length (cs.wordProd ω) := by rw [hω]
      _ ≤ ω.length := cs.length_wordProd_le ω
      _ = l.length := List.length_pmap
      _ = wordLength S w := hlen
  · obtain ⟨ω, hω, rfl⟩ := cs.exists_isReduced w
    have hl : ∀ s ∈ ω.map Subtype.val, s ∈ S := by
      intro s hs
      obtain ⟨y, -, rfl⟩ := List.mem_map.1 hs
      exact y.2
    have hprod : (ω.map Subtype.val).prod = cs.wordProd ω := by
      unfold CoxeterSystem.wordProd
      rw [List.map_congr_left (fun s _ => hcs s)]
    have := wordLength_le (J := S) hl
    rw [hprod, List.length_map] at this
    rw [hω.eq]
    exact this

theorem burnsideI25c_mem_of_length_one (h : IsBNPair B N S) {w : WeylGroup B N}
    (hw : wordLength S w = 1) : w ∈ S := by
  obtain ⟨l, hl, hlen, hprod⟩ :=
    exists_list_length_eq_wordLength h.bnCore.mul_self_eq_one (h.mem_closure w)
  rw [hw] at hlen
  obtain ⟨a, rfl⟩ := List.length_eq_one_iff.1 hlen
  have : a = w := by simpa using hprod
  rw [← this]
  exact hl a (by simp)

theorem burnsideI25c_wordLength_gen (h : IsBNPair B N S) {s : WeylGroup B N} (hs : s ∈ S) :
    wordLength S s = 1 := by
  have h1 := wordLength_gen_le_one (J := S) hs
  have h2 : wordLength S s ≠ 0 := fun h0 =>
    h.ne_one hs ((wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure s)).1 h0)
  omega

theorem burnsideI25c_prefix_longest (h : IsBNPair B N S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀)
    {x : WeylGroup B N} (hx : x ∈ Subgroup.closure J) :
    wordLength S x + wordLength S (x⁻¹ * w₀) = wordLength S w₀ := by
  obtain ⟨cs, hcs⟩ := h.exists_coxeterSystem
  have hl := burnsideI25c_cslength_eq h cs hcs
  suffices key : ∀ k : ℕ, ∀ x ∈ Subgroup.closure J, wordLength S x = k →
      wordLength S x + wordLength S (x⁻¹ * w₀) = wordLength S w₀ from key _ x hx rfl
  intro k
  induction k with
  | zero =>
    intro x hx hxk
    have : x = 1 :=
      (wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure x)).1 hxk
    subst this
    simp [wordLength_one]
  | succ k ih =>
    intro x hx hxk
    have hx1 : x ≠ 1 := by
      intro h1
      rw [h1, wordLength_one] at hxk
      omega
    obtain ⟨r, hrS, hdesc⟩ :=
      exists_right_descent h.bnCore.mul_self_eq_one (h.mem_closure x) hx1
    have hrJ : r ∈ J := by
      by_contra hrJ
      have := burnsideI25b_length_lt_mul_right h hJ hx hrS hrJ
      omega
    have hrr : r * r = 1 := h.mul_self_eq_one hrS
    set x' := x * r with hx'
    have hx'J : x' ∈ Subgroup.closure J :=
      Subgroup.mul_mem _ hx (Subgroup.subset_closure hrJ)
    have hxx' : x = x' * r := by rw [hx', mul_assoc, hrr, mul_one]
    have hlx' : wordLength S x' = k := by omega
    have IH := ih x' hx'J hlx'
    set v' := x'⁻¹ * w₀ with hv'
    have hw₀eq : x' * v' = w₀ := by rw [hv']; group
    obtain ⟨ω', hω', hω'prod⟩ := cs.exists_isReduced x'
    obtain ⟨ω'', hω'', hω''prod⟩ := cs.exists_isReduced v'
    have hlen' : ω'.length = wordLength S x' := by rw [← hl, ← hω'.eq, ← hω'prod]
    have hlen'' : ω''.length = wordLength S v' := by rw [← hl, ← hω''.eq, ← hω''prod]
    set ω := ω' ++ ω'' with hω
    have hπω : cs.wordProd ω = w₀ := by
      rw [hω, cs.wordProd_append, ← hω'prod, ← hω''prod, hw₀eq]
    set t : WeylGroup B N := x' * r * x'⁻¹ with ht
    have htref : cs.IsReflection t := by
      refine ⟨x', ⟨r, hrS⟩, ?_⟩
      rw [hcs ⟨r, hrS⟩]
    have htw₀ : t * w₀ = x' * (r * v') := by
      rw [ht, ← hw₀eq]; group
    have htinJ : t * w₀ ∈ Subgroup.closure J := by
      rw [htw₀]
      refine Subgroup.mul_mem _ hx'J (Subgroup.mul_mem _ (Subgroup.subset_closure hrJ) ?_)
      rw [hv']
      exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx'J) hw₀
    have hlt : cs.length (t * w₀) < cs.length w₀ := by
      rw [hl, hl]
      have h1 := hmax _ htinJ
      have h2 : cs.length (t * w₀) ≠ cs.length w₀ := htref.length_mul_right_ne w₀
      rw [hl, hl] at h2
      omega
    have hinv : cs.IsLeftInversion (cs.wordProd ω) t := by
      rw [hπω]
      exact ⟨htref, hlt⟩
    obtain ⟨j, hj, hjeq⟩ := CoxeterSystem.strongExchange cs hinv
    rw [hπω] at hjeq
    have hxinv : x⁻¹ * w₀ = r * v' := by
      rw [hxx', mul_inv_rev, h.inv_eq_self hrS, hv', mul_assoc]
    by_cases hjlt : j < ω'.length
    · exfalso
      rw [hω, List.eraseIdx_append_of_lt_length hjlt, cs.wordProd_append, ← hω''prod] at hjeq
      have h1 : t * x' * v' = cs.wordProd (ω'.eraseIdx j) * v' := by
        rw [mul_assoc, hw₀eq]; exact hjeq
      have h2 := mul_right_cancel h1
      have hX : x = cs.wordProd (ω'.eraseIdx j) := by
        calc x = x' * r := hxx'
          _ = t * x' := by rw [ht]; group
          _ = _ := h2
      have h3 := cs.length_wordProd_le (ω'.eraseIdx j)
      rw [← hX, List.length_eraseIdx_of_lt hjlt] at h3
      have h4 : cs.length x = wordLength S x := hl x
      omega
    · have hjge : ω'.length ≤ j := not_lt.1 hjlt
      rw [hω, List.eraseIdx_append_of_length_le hjge, cs.wordProd_append, ← hω'prod] at hjeq
      have h2 : r * v' = cs.wordProd (ω''.eraseIdx (j - ω'.length)) := by
        have : x' * (r * v') = x' * cs.wordProd (ω''.eraseIdx (j - ω'.length)) := by
          rw [← htw₀]; exact hjeq
        exact mul_left_cancel this
      have hj'' : j - ω'.length < ω''.length := by
        have := hj
        rw [hω, List.length_append] at this
        omega
      have h3 := cs.length_wordProd_le (ω''.eraseIdx (j - ω'.length))
      rw [← h2, List.length_eraseIdx_of_lt hj''] at h3
      have h5 : wordLength S (x⁻¹ * w₀) ≤ wordLength S v' - 1 := by
        rw [hxinv, ← hl]
        rw [hlen''] at h3
        exact h3
      have h6 : wordLength S w₀ ≤ wordLength S x + wordLength S (x⁻¹ * w₀) := by
        have := wordLength_mul_le h.bnCore.mul_self_eq_one (h.mem_closure x)
          (h.mem_closure (x⁻¹ * w₀))
        rwa [mul_inv_cancel_left] at this
      omega

end burnsideI25cWeyl

section burnsideI25cSetup

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem

variable {G : Type} [Group G]

structure burnsideI25c_Setup (p : ℕ) (B N U : Subgroup G) [(cartan B N).Normal]
    (S : Set (WeylGroup B N)) : Prop where
  bn : IsBNPair B N S
  prime : p.Prime
  uB : U ≤ B
  pU : IsPGroup p U
  sylow : ∃ V : Sylow p G, (V : Subgroup G) = U
  bnorm : B ≤ Subgroup.normalizer U
  split : ∀ b ∈ B, ∃ a ∈ U, ∃ c ∈ B ⊓ N, b = a * c

end burnsideI25cSetup

section burnsideI25cGroup

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}
  {p : ℕ} {U : Subgroup G}

theorem burnsideI25c_pconj (hS : burnsideI25c_Setup p B N U S) {u : G} (hu : u ∈ U) {g : G}
    (hg : g⁻¹ * u * g ∈ B) : g⁻¹ * u * g ∈ U := by
  obtain ⟨V, hV⟩ := hS.sylow
  obtain ⟨k, hk⟩ := hS.pU ⟨u, hu⟩
  have hk' : u ^ (p ^ k) = 1 := by simpa using congrArg Subtype.val hk
  refine burnsideI25b_pElem_mem hS.prime V hV hS.bnorm hg k ?_
  have : (g⁻¹ * u * g) ^ (p ^ k) = g⁻¹ * u ^ (p ^ k) * g := by
    simpa using conj_pow (a := g⁻¹) (b := u) (i := p ^ k)
  rw [this, hk']
  simp

theorem burnsideI25c_fix_prefix (h : IsBNPair B N S) :
    ∀ (k : ℕ) (n₁ n₂ : N), wordLength S (n₁ : WeylGroup B N) = k →
      wordLength S ((n₁ : WeylGroup B N) * (n₂ : WeylGroup B N)) =
        wordLength S (n₁ : WeylGroup B N) + wordLength S (n₂ : WeylGroup B N) →
      ∀ u ∈ B, ((n₁ : G) * n₂)⁻¹ * u * ((n₁ : G) * n₂) ∈ B → (n₁ : G)⁻¹ * u * n₁ ∈ B := by
  intro k
  induction k with
  | zero =>
    intro n₁ n₂ hk _ u hu _
    have h1 : (n₁ : WeylGroup B N) = 1 :=
      (wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure _)).1 hk
    have h2 : (n₁ : G) ∈ B := mk_eq_one_iff.1 h1
    exact B.mul_mem (B.mul_mem (B.inv_mem h2) hu) h2
  | succ k ih =>
    intro n₁ n₂ hk hadd u hu hfix
    have hne1 : (n₁ : WeylGroup B N) ≠ 1 := by
      intro h1
      rw [h1, wordLength_one] at hk
      omega
    obtain ⟨s, hsS, hdesc⟩ :=
      exists_left_descent h.bnCore.mul_self_eq_one (h.mem_closure _) hne1
    obtain ⟨ns, hns⟩ := QuotientGroup.mk_surjective s
    set n₁' : N := ns⁻¹ * n₁ with hn₁'
    have hW : (n₁' : WeylGroup B N) = s * (n₁ : WeylGroup B N) := by
      rw [hn₁', QuotientGroup.mk_mul, QuotientGroup.mk_inv, hns, h.inv_eq_self hsS]
    have hk' : wordLength S (n₁' : WeylGroup B N) = k := by rw [hW]; omega
    have hss : s * ((n₁' : WeylGroup B N) * (n₂ : WeylGroup B N)) =
        (n₁ : WeylGroup B N) * (n₂ : WeylGroup B N) := by
      rw [hW, ← mul_assoc, ← mul_assoc, h.mul_self_eq_one hsS, one_mul]
    have hadd' : wordLength S ((n₁' : WeylGroup B N) * (n₂ : WeylGroup B N)) =
        wordLength S (n₁' : WeylGroup B N) + wordLength S (n₂ : WeylGroup B N) := by
      have h1 := h.length_mul_le hsS ((n₁' : WeylGroup B N) * (n₂ : WeylGroup B N))
      rw [hss] at h1
      have h2 := wordLength_mul_le h.bnCore.mul_self_eq_one
        (h.mem_closure (n₁' : WeylGroup B N)) (h.mem_closure (n₂ : WeylGroup B N))
      omega
    have hlen : wordLength S ((n₁' * n₂ : N) : WeylGroup B N) <
        wordLength S (s * ((n₁' * n₂ : N) : WeylGroup B N)) := by
      rw [QuotientGroup.mk_mul, hss]
      omega
    have e : (ns : G) * ((n₁' * n₂ : N) : G) = (n₁ : G) * n₂ := by
      rw [hn₁']
      simp [mul_assoc]
    have hu' : (ns : G)⁻¹ * u * ns ∈ B := by
      refine burnsideI25b_fix_first h hsS (ns := ns) (n'' := n₁' * n₂) hns hlen hu ?_
      rw [e]
      exact hfix
    have hfix' : ((n₁' : G) * n₂)⁻¹ * ((ns : G)⁻¹ * u * ns) * ((n₁' : G) * n₂) ∈ B := by
      have e' : (ns : G) * ((n₁' : G) * n₂) = (n₁ : G) * n₂ := by
        rw [← e]; simp
      have e'' : ((n₁' : G) * n₂)⁻¹ * ((ns : G)⁻¹ * u * ns) * ((n₁' : G) * n₂) =
          ((ns : G) * ((n₁' : G) * n₂))⁻¹ * u * ((ns : G) * ((n₁' : G) * n₂)) := by group
      rw [e'', e']
      exact hfix
    have := ih n₁' n₂ hk' hadd' _ hu' hfix'
    have e3 : (n₁' : G)⁻¹ * ((ns : G)⁻¹ * u * ns) * n₁' = (n₁ : G)⁻¹ * u * n₁ := by
      have : (n₁ : G) = ns * n₁' := by rw [hn₁']; simp
      rw [this]; group
    rwa [e3] at this

end burnsideI25cGroup

section burnsideI25cMain

open CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem

variable {G : Type} [Group G] {B N : Subgroup G} [(cartan B N).Normal] {S : Set (WeylGroup B N)}
  {p : ℕ} {U : Subgroup G}

@[expose] def burnsideI25c_C (B N U : Subgroup G) [(cartan B N).Normal]
    (J : Set (WeylGroup B N)) : Subgroup G where
  carrier := {u | u ∈ U ∧ ∀ n : N, (n : WeylGroup B N) ∈ Subgroup.closure J →
    (n : G)⁻¹ * u * n ∈ B}
  mul_mem' := by
    rintro a b ⟨haU, ha⟩ ⟨hbU, hb⟩
    refine ⟨U.mul_mem haU hbU, fun n hn => ?_⟩
    have e : (n : G)⁻¹ * (a * b) * n = ((n : G)⁻¹ * a * n) * ((n : G)⁻¹ * b * n) := by group
    rw [e]
    exact B.mul_mem (ha n hn) (hb n hn)
  one_mem' := ⟨U.one_mem, fun n hn => by simpa using B.one_mem⟩
  inv_mem' := by
    rintro a ⟨haU, ha⟩
    refine ⟨U.inv_mem haU, fun n hn => ?_⟩
    have e : (n : G)⁻¹ * a⁻¹ * n = ((n : G)⁻¹ * a * n)⁻¹ := by group
    rw [e]
    exact B.inv_mem (ha n hn)

theorem burnsideI25c_mem_C_of_fix (hS : burnsideI25c_Setup p B N U S) {J : Set (WeylGroup B N)}
    (hJ : J ⊆ S) {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀) {n₀ : N}
    (hn₀ : (n₀ : WeylGroup B N) = w₀) {u : G} (hu : u ∈ U) (hfix : (n₀ : G)⁻¹ * u * n₀ ∈ B) :
    u ∈ burnsideI25c_C B N U J := by
  refine ⟨hu, fun n hn => ?_⟩
  have hW1 := burnsideI25c_prefix_longest hS.bn hJ hw₀ hmax hn
  set n' : N := n⁻¹ * n₀ with hn'
  have hW : (n' : WeylGroup B N) = (n : WeylGroup B N)⁻¹ * w₀ := by
    rw [hn', QuotientGroup.mk_mul, QuotientGroup.mk_inv, hn₀]
  have hprod : (n : WeylGroup B N) * (n' : WeylGroup B N) = w₀ := by
    rw [hW]; group
  have hadd : wordLength S ((n : WeylGroup B N) * (n' : WeylGroup B N)) =
      wordLength S (n : WeylGroup B N) + wordLength S (n' : WeylGroup B N) := by
    rw [hprod, hW]; omega
  have e : (n : G) * (n' : G) = n₀ := by
    rw [hn']; simp
  refine burnsideI25c_fix_prefix hS.bn _ n n' rfl hadd u (hS.uB hu) ?_
  rw [e]
  exact hfix

theorem burnsideI25c_C_conj {J : Set (WeylGroup B N)} (hS : burnsideI25c_Setup p B N U S)
    {c : G} (hc : c ∈ burnsideI25c_C B N U J) {n : N}
    (hn : (n : WeylGroup B N) ∈ Subgroup.closure J) :
    (n : G)⁻¹ * c * n ∈ burnsideI25c_C B N U J := by
  refine ⟨burnsideI25c_pconj hS hc.1 (hc.2 n hn), fun m hm => ?_⟩
  have h1 := hc.2 (n * m) (by
    rw [QuotientGroup.mk_mul]
    exact Subgroup.mul_mem _ hn hm)
  have e : ((m : G))⁻¹ * ((n : G)⁻¹ * c * n) * m = (((n * m : N) : G))⁻¹ * c * ((n * m : N) : G) := by
    simp [mul_assoc]
  rw [e]
  exact h1

theorem burnsideI25c_C_conj' {J : Set (WeylGroup B N)} (hS : burnsideI25c_Setup p B N U S)
    {c : G} (hc : c ∈ burnsideI25c_C B N U J) {n : N}
    (hn : (n : WeylGroup B N) ∈ Subgroup.closure J) :
    (n : G) * c * (n : G)⁻¹ ∈ burnsideI25c_C B N U J := by
  have := burnsideI25c_C_conj hS hc (n := n⁻¹) (by
    rw [QuotientGroup.mk_inv]
    exact Subgroup.inv_mem _ hn)
  simpa using this

theorem burnsideI25c_C_conj_H {J : Set (WeylGroup B N)} (hS : burnsideI25c_Setup p B N U S)
    {c : G} (hc : c ∈ burnsideI25c_C B N U J) {h : G} (hh : h ∈ B ⊓ N) :
    h * c * h⁻¹ ∈ burnsideI25c_C B N U J := by
  have hhB : h ∈ B := (Subgroup.mem_inf.1 hh).1
  refine ⟨(Subgroup.mem_normalizer_iff.1 (hS.bnorm hhB) c).1 hc.1, fun n hn => ?_⟩
  have h1 := burnsideI25b_conj_mem_H (B := B) (N := N) hh (N.inv_mem n.2)
  have e : (n : G)⁻¹ * (h * c * h⁻¹) * n =
      ((n : G)⁻¹ * h * ((n : G)⁻¹)⁻¹) * ((n : G)⁻¹ * c * n) * ((n : G)⁻¹ * h * ((n : G)⁻¹)⁻¹)⁻¹ := by
    group
  rw [e]
  exact B.mul_mem (B.mul_mem (Subgroup.mem_inf.1 h1).1 (hc.2 n hn))
    (B.inv_mem (Subgroup.mem_inf.1 h1).1)

theorem burnsideI25c_gen_mul_longest (h : IsBNPair B N S) {J : Set (WeylGroup B N)}
    (hJ : J ⊆ S) {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀)
    {s : WeylGroup B N} (hs : s ∈ J) : wordLength S (s * w₀) + 1 = wordLength S w₀ := by
  have h1 := burnsideI25c_prefix_longest h hJ hw₀ hmax (Subgroup.subset_closure hs)
  rw [h.inv_eq_self (hJ hs), burnsideI25c_wordLength_gen h (hJ hs)] at h1
  omega

theorem burnsideI25c_transitive (hS : burnsideI25c_Setup p B N U S) {J : Set (WeylGroup B N)}
    (hJ : J ⊆ S) {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀) {n₀ ns : N}
    (hn₀ : (n₀ : WeylGroup B N) = w₀) {s : WeylGroup B N} (hs : s ∈ J)
    (hns : (ns : WeylGroup B N) = s) :
    ∀ a ∈ U, ∃ t ∈ burnsideI25b_stabIn B U ((ns : G) * n₀),
      ∃ y ∈ burnsideI25b_stabIn B U (ns : G), a = t * y := by
  have h := hS.bn
  have hsS : s ∈ S := hJ hs
  have hnsS : (ns : WeylGroup B N) ∈ S := hns ▸ hsS
  have hlen1 := burnsideI25c_gen_mul_longest h hJ hw₀ hmax hs
  have hss : s * (s * w₀) = w₀ := by rw [← mul_assoc, h.mul_self_eq_one hsS, one_mul]
  have hlt : wordLength S (s * w₀) < wordLength S (s * (s * w₀)) := by rw [hss]; omega
  have hdc := h.dc_mul_dc_of_lt hsS hlt
  rw [hss] at hdc
  have hny : ((ns * n₀ : N) : WeylGroup B N) = s * w₀ := by
    rw [QuotientGroup.mk_mul, hns, hn₀]
  have hsq : (ns : G) * ns ∈ B := burnsideI25b_mul_self_mem h hnsS
  have hsqN : (ns : G) * ns ∈ N := N.mul_mem ns.2 ns.2
  have hsqH : (ns : G) * ns ∈ B ⊓ N := Subgroup.mem_inf.2 ⟨hsq, hsqN⟩
  have he : ((ns : G) * ns)⁻¹ ∈ B ⊓ N := (B ⊓ N).inv_mem hsqH
  intro a ha
  have hvU : a⁻¹ ∈ U := U.inv_mem ha
  have hnyN : ((ns : G) * n₀) ∈ N := N.mul_mem ns.2 n₀.2
  have hnyd : ((ns : G) * n₀) ∈ dc B N (s * w₀) := by
    have := coe_mem_dc (B := B) (ns * n₀)
    rw [hny] at this
    simpa using this
  have hz : (ns : G) * a⁻¹ * ((ns : G) * n₀) ∈ dc B N w₀ := by
    rw [← hdc]
    refine Set.mem_mul.2 ⟨(ns : G), hns ▸ coe_mem_dc ns, a⁻¹ * ((ns : G) * n₀), ?_, by group⟩
    have := mul_mem_dc hnyd (hS.uB hvU) B.one_mem
    simpa using this
  obtain ⟨b₁, hb₁, b₂, hb₂, hz'⟩ := (mem_dc_of_lift hn₀).1 hz
  obtain ⟨y, hy, h₁, hh₁, rfl⟩ := hS.split b₁ hb₁
  have hc₁ : (n₀ : G)⁻¹ * h₁ * n₀ ∈ B ⊓ N := by
    have := burnsideI25b_conj_mem_H (B := B) (N := N) hh₁ (N.inv_mem n₀.2)
    simpa using this
  have hβ : ((n₀ : G)⁻¹ * h₁ * n₀) * b₂ ∈ B :=
    B.mul_mem (Subgroup.mem_inf.1 hc₁).1 hb₂
  set ε : G := (ns : G)⁻¹ * y * ns with hε
  have hkey : a⁻¹ * ((ns : G) * n₀) =
      ε * (((ns : G) * ns)⁻¹ * ((ns : G) * n₀)) * (((n₀ : G)⁻¹ * h₁ * n₀) * b₂) := by
    have h1 : a⁻¹ * ((ns : G) * n₀) = (ns : G)⁻¹ * (y * h₁ * n₀ * b₂) := by
      calc a⁻¹ * ((ns : G) * n₀) = (ns : G)⁻¹ * ((ns : G) * a⁻¹ * ((ns : G) * n₀)) := by group
        _ = _ := by rw [hz']
    rw [h1, hε]
    group
  have hεB : ε ∈ B := by
    have hεP : ε ∈ parabolic B N {s} := by
      have hP := burnsideI25b_mem_parabolic_lift h hnsS
      have hBP : B ≤ parabolic B N {(ns : WeylGroup B N)} :=
        h.le_parabolic (Set.singleton_subset_iff.2 hnsS)
      rw [hε]
      have hP' : (ns : G) ∈ parabolic B N {s} := by simpa [hns] using hP
      have hBP' : B ≤ parabolic B N {s} := by simpa [hns] using hBP
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hP') (hBP' (hS.uB hy))) hP'
    rcases (burnsideI25b_mem_parabolic_single_iff h hsS).1 hεP with hB | hds
    · exact hB
    · exfalso
      have h1 : ε * (((ns : G) * ns)⁻¹ * ((ns : G) * n₀)) ∈ dc B N w₀ := by
        rw [← hdc]
        refine Set.mem_mul.2 ⟨ε, hds, _, ?_, rfl⟩
        have := mul_mem_dc hnyd ((Subgroup.mem_inf.1 he).1) B.one_mem
        simpa using this
      have h2 : ε * (((ns : G) * ns)⁻¹ * ((ns : G) * n₀)) ∈ dc B N (s * w₀) := by
        have e : ε * (((ns : G) * ns)⁻¹ * ((ns : G) * n₀)) =
            a⁻¹ * ((ns : G) * n₀) * (((n₀ : G)⁻¹ * h₁ * n₀) * b₂)⁻¹ := by
          rw [hkey]; group
        rw [e]
        exact mul_mem_dc hnyd (hS.uB hvU) (B.inv_mem hβ)
      have h3 := congrArg (wordLength S) (h.eq_of_mem_dc h1 h2)
      omega
  have hεU : ε ∈ U := burnsideI25c_pconj hS hy hεB
  have hεs : ε ∈ burnsideI25b_stabIn B U (ns : G) := by
    refine ⟨hεU, ?_⟩
    have e : (ns : G)⁻¹ * ε * ns = ((ns : G) * ns)⁻¹ * y * ((ns : G) * ns) := by
      rw [hε]; group
    rw [e]
    exact B.mul_mem (B.mul_mem (B.inv_mem hsq) (hS.uB hy)) hsq
  refine ⟨a * ε, ⟨U.mul_mem ha hεU, ?_⟩, ε⁻¹, (burnsideI25b_stabIn B U (ns : G)).inv_mem hεs, ?_⟩
  · have hε' : (a * ε)⁻¹ * ((ns : G) * n₀) =
        ((ns : G) * ns)⁻¹ * ((ns : G) * n₀) * (((n₀ : G)⁻¹ * h₁ * n₀) * b₂) := by
      calc (a * ε)⁻¹ * ((ns : G) * n₀) = ε⁻¹ * (a⁻¹ * ((ns : G) * n₀)) := by group
        _ = _ := by rw [hkey]; group
    have hε'' : a * ε = ((ns : G) * n₀) * (((n₀ : G)⁻¹ * h₁ * n₀) * b₂)⁻¹ *
        ((ns : G) * n₀)⁻¹ * ((ns : G) * ns) := by
      have := eq_mul_inv_of_mul_eq hε'
      calc a * ε = ((a * ε)⁻¹)⁻¹ := by group
        _ = _ := by rw [this]; group
    have h1 := burnsideI25b_conj_mem_H (B := B) (N := N) hsqH (N.inv_mem hnyN)
    show ((ns : G) * n₀)⁻¹ * (a * ε) * ((ns : G) * n₀) ∈ B
    have e : ((ns : G) * n₀)⁻¹ * (a * ε) * ((ns : G) * n₀) =
        (((n₀ : G)⁻¹ * h₁ * n₀) * b₂)⁻¹ *
          (((ns : G) * n₀)⁻¹ * ((ns : G) * ns) * (((ns : G) * n₀)⁻¹)⁻¹) := by
      rw [hε'']; group
    rw [e]
    exact B.mul_mem (B.inv_mem hβ) (Subgroup.mem_inf.1 h1).1
  · group

theorem burnsideI25c_T_normalizes (hS : burnsideI25c_Setup p B N U S)
    (hR : burnsideI25b_RankOne B N U S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀) {n₀ ns : N}
    (hn₀ : (n₀ : WeylGroup B N) = w₀) {s : WeylGroup B N} (hs : s ∈ J)
    (hns : (ns : WeylGroup B N) = s) {t c : G}
    (ht : t ∈ burnsideI25b_stabIn B U ((ns : G) * n₀)) (hc : c ∈ burnsideI25c_C B N U J) :
    t * c * t⁻¹ ∈ burnsideI25c_C B N U J := by
  have h := hS.bn
  have hsS : s ∈ S := hJ hs
  have hy₀J : s * w₀ ∈ Subgroup.closure J :=
    Subgroup.mul_mem _ (Subgroup.subset_closure hs) hw₀
  have hlen1 := burnsideI25c_gen_mul_longest h hJ hw₀ hmax hs
  have hW1 := burnsideI25c_prefix_longest h hJ hw₀ hmax hy₀J
  have hs'len : wordLength S ((s * w₀)⁻¹ * w₀) = 1 := by omega
  have hs'S : (s * w₀)⁻¹ * w₀ ∈ S := burnsideI25c_mem_of_length_one h hs'len
  obtain ⟨ns', hns'⟩ := QuotientGroup.mk_surjective ((s * w₀)⁻¹ * w₀)
  have hnyW : ((ns * n₀ : N) : WeylGroup B N) = s * w₀ := by
    rw [QuotientGroup.mk_mul, hns, hn₀]
  set m : N := (ns * n₀ * ns')⁻¹ * n₀ with hm
  have hmW : (m : WeylGroup B N) = 1 := by
    rw [hm, QuotientGroup.mk_mul, QuotientGroup.mk_inv, QuotientGroup.mk_mul, hnyW, hns', hn₀]
    group
  have hmB : (m : G) ∈ B := mk_eq_one_iff.1 hmW
  have hn₀eq : (n₀ : G) = ((ns : G) * n₀) * ns' * m := by
    rw [hm]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hnyJ : ((ns * n₀ : N) : WeylGroup B N) ∈ Subgroup.closure J := by rw [hnyW]; exact hy₀J
  have hn₀J : (n₀ : WeylGroup B N) ∈ Subgroup.closure J := by rw [hn₀]; exact hw₀
  have hτ : ((ns : G) * n₀)⁻¹ * t * ((ns : G) * n₀) ∈ U := burnsideI25c_pconj hS ht.1 ht.2
  have hγB : ((ns : G) * n₀)⁻¹ * c * ((ns : G) * n₀) ∈ B := by
    have := hc.2 (ns * n₀) hnyJ
    simpa using this
  have hγ : ((ns : G) * n₀)⁻¹ * c * ((ns : G) * n₀) ∈ U := burnsideI25c_pconj hS hc.1 hγB
  have hcn₀ := hc.2 n₀ hn₀J
  have hγs : ((ns : G) * n₀)⁻¹ * c * ((ns : G) * n₀) ∈ burnsideI25b_stabIn B U (ns' : G) := by
    refine ⟨hγ, ?_⟩
    have e : (ns' : G)⁻¹ * (((ns : G) * n₀)⁻¹ * c * ((ns : G) * n₀)) * ns' =
        (m : G) * ((n₀ : G)⁻¹ * c * n₀) * (m : G)⁻¹ := by
      have e1 : (m : G) * ((((ns : G) * n₀) * ns' * m)⁻¹ * c * (((ns : G) * n₀) * ns' * m)) *
          (m : G)⁻¹ = (ns' : G)⁻¹ * (((ns : G) * n₀)⁻¹ * c * ((ns : G) * n₀)) * ns' := by group
      rw [← hn₀eq] at e1
      exact e1.symm
    rw [e]
    exact B.mul_mem (B.mul_mem hmB hcn₀) (B.inv_mem hmB)
  have hRR := hR ns' (hns' ▸ hs'S) _ hτ _ hγs
  have hU : t * c * t⁻¹ ∈ U := U.mul_mem (U.mul_mem ht.1 hc.1) (U.inv_mem ht.1)
  refine burnsideI25c_mem_C_of_fix hS hJ hw₀ hmax hn₀ hU ?_
  have e : (n₀ : G)⁻¹ * (t * c * t⁻¹) * n₀ =
      (m : G)⁻¹ * ((ns' : G)⁻¹ * ((((ns : G) * n₀)⁻¹ * t * ((ns : G) * n₀)) *
        (((ns : G) * n₀)⁻¹ * c * ((ns : G) * n₀)) *
        (((ns : G) * n₀)⁻¹ * t * ((ns : G) * n₀))⁻¹) * ns') * (m : G) := by
    have e1 : (((ns : G) * n₀) * ns' * m)⁻¹ * (t * c * t⁻¹) * (((ns : G) * n₀) * ns' * m) =
        (m : G)⁻¹ * ((ns' : G)⁻¹ * ((((ns : G) * n₀)⁻¹ * t * ((ns : G) * n₀)) *
          (((ns : G) * n₀)⁻¹ * c * ((ns : G) * n₀)) *
          (((ns : G) * n₀)⁻¹ * t * ((ns : G) * n₀))⁻¹) * ns') * (m : G) := by group
    rw [← hn₀eq] at e1
    exact e1
  rw [e]
  exact B.mul_mem (B.mul_mem (B.inv_mem hmB) hRR.2) hmB

theorem burnsideI25c_conj_stab_mem (hS : burnsideI25c_Setup p B N U S) {J : Set (WeylGroup B N)}
    (hJ : J ⊆ S) {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀) {n₀ ns nx : N}
    {s : WeylGroup B N} (hs : s ∈ J) (hns : (ns : WeylGroup B N) = s)
    (hn₀ : (n₀ : WeylGroup B N) = w₀) (hx : (nx : WeylGroup B N) ∈ Subgroup.closure J)
    (hxs : wordLength S ((nx : WeylGroup B N) * s) = wordLength S (nx : WeylGroup B N) + 1)
    {t : G} (ht : t ∈ burnsideI25b_stabIn B U ((ns : G) * n₀)) :
    (nx : G) * t * (nx : G)⁻¹ ∈ U := by
  have h := hS.bn
  have hsS : s ∈ S := hJ hs
  have hlen1 := burnsideI25c_gen_mul_longest h hJ hw₀ hmax hs
  have hxsJ : (nx : WeylGroup B N) * s ∈ Subgroup.closure J :=
    Subgroup.mul_mem _ hx (Subgroup.subset_closure hs)
  have hW1 := burnsideI25c_prefix_longest h hJ hw₀ hmax (Subgroup.inv_mem _ hxsJ)
  rw [h.length_inv, inv_inv] at hW1
  have hn₁W : ((nx⁻¹ : N) : WeylGroup B N) = (nx : WeylGroup B N)⁻¹ := by
    rw [QuotientGroup.mk_inv]
  have hn₂W : ((nx * (ns * n₀) : N) : WeylGroup B N) = (nx : WeylGroup B N) * (s * w₀) := by
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, hns, hn₀]
  have hprod : ((nx⁻¹ : N) : WeylGroup B N) * ((nx * (ns * n₀) : N) : WeylGroup B N) = s * w₀ := by
    rw [hn₁W, hn₂W]; group
  have hadd : wordLength S (((nx⁻¹ : N) : WeylGroup B N) *
      ((nx * (ns * n₀) : N) : WeylGroup B N)) =
      wordLength S ((nx⁻¹ : N) : WeylGroup B N) +
        wordLength S ((nx * (ns * n₀) : N) : WeylGroup B N) := by
    rw [hprod, hn₁W, hn₂W, h.length_inv]
    have e : (nx : WeylGroup B N) * (s * w₀) = ((nx : WeylGroup B N) * s) * w₀ := by group
    rw [e]
    omega
  have hfix : (((nx⁻¹ : N) : G) * ((nx * (ns * n₀) : N) : G))⁻¹ * t *
      (((nx⁻¹ : N) : G) * ((nx * (ns * n₀) : N) : G)) ∈ B := by
    have e : ((nx⁻¹ : N) : G) * ((nx * (ns * n₀) : N) : G) = (ns : G) * n₀ := by simp
    rw [e]
    exact ht.2
  have := burnsideI25c_fix_prefix h _ (nx⁻¹) (nx * (ns * n₀)) rfl hadd t (hS.uB ht.1) hfix
  have h2 : ((nx⁻¹ : G))⁻¹ * t * ((nx : G)⁻¹) ∈ U := by
    have h3 : ((nx : G)⁻¹)⁻¹ * t * ((nx : G)⁻¹) ∈ B := by simpa using this
    exact burnsideI25c_pconj hS ht.1 h3
  simpa using h2

@[expose] def burnsideI25c_Gen (B N U : Subgroup G) [(cartan B N).Normal]
    (S J : Set (WeylGroup B N)) (n₀ : N) : Set G :=
  {g | ∃ nx ns : N, (nx : WeylGroup B N) ∈ Subgroup.closure J ∧ (ns : WeylGroup B N) ∈ J ∧
    wordLength S ((nx : WeylGroup B N) * (ns : WeylGroup B N)) =
      wordLength S (nx : WeylGroup B N) + 1 ∧
    ∃ t ∈ burnsideI25b_stabIn B U ((ns : G) * n₀), g = (nx : G) * t * (nx : G)⁻¹}

theorem burnsideI25c_gen_normalizes (hS : burnsideI25c_Setup p B N U S)
    (hR : burnsideI25b_RankOne B N U S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀) {n₀ : N}
    (hn₀ : (n₀ : WeylGroup B N) = w₀) :
    ∀ g ∈ Subgroup.closure (burnsideI25c_Gen B N U S J n₀), g ∈ U ∧
      ∀ c ∈ burnsideI25c_C B N U J, g * c * g⁻¹ ∈ burnsideI25c_C B N U J ∧
        g⁻¹ * c * g ∈ burnsideI25c_C B N U J := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨nx, ns, hx1, hs1, hlen, t, ht, rfl⟩ := hx
    refine ⟨burnsideI25c_conj_stab_mem hS hJ hw₀ hmax hs1 rfl hn₀ hx1 hlen ht, fun c hc => ?_⟩
    have h1 := burnsideI25c_C_conj hS hc hx1
    refine ⟨?_, ?_⟩
    · have h2 := burnsideI25c_T_normalizes hS hR hJ hw₀ hmax hn₀ hs1 rfl ht h1
      have h3 := burnsideI25c_C_conj' hS h2 hx1
      have e : (nx : G) * t * (nx : G)⁻¹ * c * ((nx : G) * t * (nx : G)⁻¹)⁻¹ =
          (nx : G) * (t * ((nx : G)⁻¹ * c * nx) * t⁻¹) * (nx : G)⁻¹ := by group
      rw [e]
      exact h3
    · have h2 := burnsideI25c_T_normalizes hS hR hJ hw₀ hmax hn₀ hs1 rfl
        ((burnsideI25b_stabIn B U _).inv_mem ht) h1
      have h3 := burnsideI25c_C_conj' hS h2 hx1
      have e : ((nx : G) * t * (nx : G)⁻¹)⁻¹ * c * ((nx : G) * t * (nx : G)⁻¹) =
          (nx : G) * (t⁻¹ * ((nx : G)⁻¹ * c * nx) * t⁻¹⁻¹) * (nx : G)⁻¹ := by group
      rw [e]
      exact h3
  | one =>
    exact ⟨U.one_mem, fun c hc => ⟨by simpa using hc, by simpa using hc⟩⟩
  | mul x y _ _ hx hy =>
    refine ⟨U.mul_mem hx.1 hy.1, fun c hc => ⟨?_, ?_⟩⟩
    · have e : x * y * c * (x * y)⁻¹ = x * (y * c * y⁻¹) * x⁻¹ := by group
      rw [e]
      exact (hx.2 _ (hy.2 c hc).1).1
    · have e : (x * y)⁻¹ * c * (x * y) = y⁻¹ * (x⁻¹ * c * x) * y := by group
      rw [e]
      exact (hy.2 _ (hx.2 c hc).2).2
  | inv x _ hx =>
    refine ⟨U.inv_mem hx.1, fun c hc => ⟨?_, ?_⟩⟩
    · simpa using (hx.2 c hc).2
    · simpa using (hx.2 c hc).1

theorem burnsideI25c_generation (hS : burnsideI25c_Setup p B N U S) {J : Set (WeylGroup B N)}
    (hJ : J ⊆ S) {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀) {n₀ : N}
    (hn₀ : (n₀ : WeylGroup B N) = w₀) :
    ∀ (k : ℕ) (n : N), wordLength S (n : WeylGroup B N) = k →
      (n : WeylGroup B N) ∈ Subgroup.closure J → ∀ u ∈ U,
      ∃ g ∈ Subgroup.closure (burnsideI25c_Gen B N U S J n₀),
        g⁻¹ * u ∈ burnsideI25b_stabIn B U (n : G) := by
  have h := hS.bn
  intro k
  induction k with
  | zero =>
    intro n hk _ u hu
    have h1 : (n : WeylGroup B N) = 1 :=
      (wordLength_eq_zero_iff h.bnCore.mul_self_eq_one (h.mem_closure _)).1 hk
    have h2 : (n : G) ∈ B := mk_eq_one_iff.1 h1
    refine ⟨1, Subgroup.one_mem _, ?_, ?_⟩
    · simpa using hu
    · simpa using B.mul_mem (B.mul_mem (B.inv_mem h2) (hS.uB hu)) h2
  | succ k ih =>
    intro n hk hnJ u hu
    have hne1 : (n : WeylGroup B N) ≠ 1 := by
      intro h1
      rw [h1, wordLength_one] at hk
      omega
    obtain ⟨r, hrS, hdesc⟩ :=
      exists_right_descent h.bnCore.mul_self_eq_one (h.mem_closure _) hne1
    have hrJ : r ∈ J := by
      by_contra hrJ
      have := burnsideI25b_length_lt_mul_right h hJ hnJ hrS hrJ
      omega
    obtain ⟨nr, hnr⟩ := QuotientGroup.mk_surjective r
    set n' : N := n * nr⁻¹ with hn'
    have hW : (n' : WeylGroup B N) = (n : WeylGroup B N) * r := by
      rw [hn', QuotientGroup.mk_mul, QuotientGroup.mk_inv, hnr, h.inv_eq_self hrS]
    have hn'J : (n' : WeylGroup B N) ∈ Subgroup.closure J := by
      rw [hW]
      exact Subgroup.mul_mem _ hnJ (Subgroup.subset_closure hrJ)
    have hk' : wordLength S (n' : WeylGroup B N) = k := by rw [hW]; omega
    have hrr : (n' : WeylGroup B N) * r = n := by
      rw [hW, mul_assoc, h.mul_self_eq_one hrS, mul_one]
    have hlen' : wordLength S ((n' : WeylGroup B N) * (nr : WeylGroup B N)) =
        wordLength S (n' : WeylGroup B N) + 1 := by
      rw [hnr, hrr]
      omega
    obtain ⟨g₁, hg₁, hg₁u⟩ := ih n' hk' hn'J u hu
    have hnn : (n : G) = n' * nr := by rw [hn']; simp
    obtain ⟨a, haU, hh, hhH, hab⟩ := hS.split _ hg₁u.2
    obtain ⟨t, ht, y, hy, hay⟩ := burnsideI25c_transitive hS hJ hw₀ hmax hn₀ (hnr ▸ hrJ) hnr a haU
    have hg₂ : (n' : G) * t * (n' : G)⁻¹ ∈ burnsideI25c_Gen B N U S J n₀ :=
      ⟨n', nr, hn'J, hnr ▸ hrJ, hlen', t, ht, rfl⟩
    have hg₂U : (n' : G) * t * (n' : G)⁻¹ ∈ U :=
      burnsideI25c_conj_stab_mem hS hJ hw₀ hmax (hnr ▸ hrJ) hnr hn₀ hn'J
        (by rw [← hnr]; exact hlen') ht
    refine ⟨g₁ * ((n' : G) * t * (n' : G)⁻¹),
      Subgroup.mul_mem _ hg₁ (Subgroup.subset_closure hg₂), ?_⟩
    have hu₁ : g₁⁻¹ * u = (n' : G) * (t * y * hh) * (n' : G)⁻¹ := by
      have h1 : (n' : G)⁻¹ * (g₁⁻¹ * u) * n' = t * y * hh := by rw [hab, hay]
      calc g₁⁻¹ * u = (n' : G) * ((n' : G)⁻¹ * (g₁⁻¹ * u) * n') * (n' : G)⁻¹ := by group
        _ = _ := by rw [h1]
    have hexp : (g₁ * ((n' : G) * t * (n' : G)⁻¹))⁻¹ * u = (n' : G) * (y * hh) * (n' : G)⁻¹ := by
      calc (g₁ * ((n' : G) * t * (n' : G)⁻¹))⁻¹ * u =
          ((n' : G) * t * (n' : G)⁻¹)⁻¹ * (g₁⁻¹ * u) := by group
        _ = _ := by rw [hu₁]; group
    refine ⟨?_, ?_⟩
    · have e : (g₁ * ((n' : G) * t * (n' : G)⁻¹))⁻¹ * u =
          ((n' : G) * t * (n' : G)⁻¹)⁻¹ * (g₁⁻¹ * u) := by group
      rw [e]
      exact U.mul_mem (U.inv_mem hg₂U) hg₁u.1
    · rw [hexp]
      have e : (n : G)⁻¹ * ((n' : G) * (y * hh) * (n' : G)⁻¹) * n =
          ((nr : G)⁻¹ * y * nr) * ((nr : G)⁻¹ * hh * nr) := by
        rw [hnn]; group
      rw [e]
      have h1 := burnsideI25b_conj_mem_H (B := B) (N := N) hhH (N.inv_mem nr.2)
      exact B.mul_mem hy.2 (by simpa using (Subgroup.mem_inf.1 h1).1)

theorem burnsideI25c_C_normal_U (hS : burnsideI25c_Setup p B N U S)
    (hR : burnsideI25b_RankOne B N U S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀) {n₀ : N}
    (hn₀ : (n₀ : WeylGroup B N) = w₀) {u c : G} (hu : u ∈ U)
    (hc : c ∈ burnsideI25c_C B N U J) : u * c * u⁻¹ ∈ burnsideI25c_C B N U J := by
  have hw₀' : (n₀ : WeylGroup B N) ∈ Subgroup.closure J := by rw [hn₀]; exact hw₀
  obtain ⟨g, hg, hgu⟩ := burnsideI25c_generation hS hJ hw₀ hmax hn₀ _ n₀ rfl hw₀' u hu
  have hc' : g⁻¹ * u ∈ burnsideI25c_C B N U J :=
    burnsideI25c_mem_C_of_fix hS hJ hw₀ hmax hn₀ hgu.1 hgu.2
  obtain ⟨-, hgN⟩ := burnsideI25c_gen_normalizes hS hR hJ hw₀ hmax hn₀ g hg
  have e : u * c * u⁻¹ = g * ((g⁻¹ * u) * c * (g⁻¹ * u)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (hgN _ ((burnsideI25c_C B N U J).mul_mem ((burnsideI25c_C B N U J).mul_mem hc' hc)
    ((burnsideI25c_C B N U J).inv_mem hc'))).1

theorem burnsideI25c_C_normal_B (hS : burnsideI25c_Setup p B N U S)
    (hR : burnsideI25b_RankOne B N U S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀) {n₀ : N}
    (hn₀ : (n₀ : WeylGroup B N) = w₀) {b c : G} (hb : b ∈ B)
    (hc : c ∈ burnsideI25c_C B N U J) : b * c * b⁻¹ ∈ burnsideI25c_C B N U J := by
  obtain ⟨a, ha, h, hh, rfl⟩ := hS.split b hb
  have e : a * h * c * (a * h)⁻¹ = a * (h * c * h⁻¹) * a⁻¹ := by group
  rw [e]
  exact burnsideI25c_C_normal_U hS hR hJ hw₀ hmax hn₀ ha (burnsideI25c_C_conj_H hS hc hh)

theorem burnsideI25c_C_normal_P (hS : burnsideI25c_Setup p B N U S)
    (hR : burnsideI25b_RankOne B N U S) {J : Set (WeylGroup B N)} (hJ : J ⊆ S)
    {w₀ : WeylGroup B N} (hw₀ : w₀ ∈ Subgroup.closure J)
    (hmax : ∀ w ∈ Subgroup.closure J, wordLength S w ≤ wordLength S w₀) {n₀ : N}
    (hn₀ : (n₀ : WeylGroup B N) = w₀) {g c : G} (hg : g ∈ parabolic B N J)
    (hc : c ∈ burnsideI25c_C B N U J) : g * c * g⁻¹ ∈ burnsideI25c_C B N U J := by
  obtain ⟨w, hw, hgw⟩ := (hS.bn.mem_parabolic_iff hJ).1 hg
  obtain ⟨n, hn⟩ := QuotientGroup.mk_surjective w
  obtain ⟨b₁, hb₁, b₂, hb₂, rfl⟩ := (mem_dc_of_lift hn).1 hgw
  have h1 := burnsideI25c_C_normal_B hS hR hJ hw₀ hmax hn₀ hb₂ hc
  have h2 := burnsideI25c_C_conj' hS h1 (n := n) (hn ▸ hw)
  have h3 := burnsideI25c_C_normal_B hS hR hJ hw₀ hmax hn₀ hb₁ h2
  have e : b₁ * (n : G) * b₂ * c * (b₁ * (n : G) * b₂)⁻¹ =
      b₁ * ((n : G) * (b₂ * c * b₂⁻¹) * (n : G)⁻¹) * b₁⁻¹ := by group
  rw [e]
  exact h3

theorem burnsideI25c_levi_of_setup (hS : burnsideI25c_Setup p B N U S)
    (hR : burnsideI25b_RankOne B N U S) : burnsideI25b_Levi p B N U S := by
  intro J hJ n hnJ hnmax u hu hun
  have hCu := burnsideI25c_mem_C_of_fix hS hJ hnJ hnmax rfl hu hun
  have hP : burnsideI25c_C B N U J ≤ pCoreOf p (parabolic B N J) := by
    refine burnsideI25b_le_pCoreOf p ?_ ?_ ?_
    · intro x hx
      exact hS.bn.le_parabolic hJ (hS.uB hx.1)
    · exact IsPGroup.to_le hS.pU (fun x hx => hx.1)
    · intro x hx q hq
      exact burnsideI25c_C_normal_P hS hR hJ hnJ hnmax rfl hx hq
  exact hP hCu

theorem burnsideI25c_levi_of_rankOne {p : ℕ} (hp : p.Prime) (h : IsBNPair B N S)
    (V : Sylow p G) {U : Subgroup G} (hV : (V : Subgroup G) = U)
    (hBn : B ≤ Subgroup.normalizer U) (hUB : U ≤ B)
    (hBU : ∀ b ∈ B, ∃ a ∈ U, ∃ c ∈ B ⊓ N, b = a * c)
    (hR : burnsideI25b_RankOne B N U S) : burnsideI25b_Levi p B N U S :=
  burnsideI25c_levi_of_setup ⟨h, hp, hUB, hV ▸ V.isPGroup', ⟨V, hV⟩, hBn, hBU⟩ hR

end burnsideI25cMain

section burnsideI25cStar

open CFSG.ASVolI.ChIJK CFSG.GH74.BNPair CFSG.GroupTheory.TitsSystem
open scoped Pointwise

variable {G : Type} [Group G]

theorem burnsideI25c_rankOne_of_isRankOneNormal {B N : Subgroup G} [(cartan B N).Normal]
    {S : Set (WeylGroup B N)} {p : ℕ} (h : IsBNPair B N S) {U : Subgroup G} (hUB : U ≤ B)
    (hUn : (U.subgroupOf B).Normal) (hUp : IsPGroup p U) (hUi : ¬ p ∣ U.index)
    (hRN : IsRankOneNormal p B N) : burnsideI25b_RankOne B N U S := by
  intro ns hns u hu c hc
  have hnsB : (ns : G) ∉ B := fun hB => h.ne_one hns (mk_eq_one_iff.2 hB)
  have hBN3 : ∀ b ∈ B, (ns : G) * b * ns ∈ B ∨
      ∃ b₁ ∈ B, ∃ b₂ ∈ B, (ns : G) * b * ns = b₁ * ns * b₂ := by
    intro b hb
    have hmem : (ns : G) * b * ns ∈ ({(ns : G)} : Set G) * (B : Set G) * {(ns : G)} :=
      Set.mem_mul.2 ⟨(ns : G) * b, Set.mem_mul.2 ⟨ns, rfl, b, hb, rfl⟩, ns, rfl, rfl⟩
    rcases h.mul_subset ns ns hns hmem with h1 | h1
    · obtain ⟨b₁, hb₁, b₂, hb₂, he⟩ :=
        (mem_dc_of_lift (n := ns) (w := (ns : WeylGroup B N)) rfl).1 h1
      exact Or.inr ⟨b₁, hb₁, b₂, hb₂, he⟩
    · left
      rw [h.mul_self_eq_one hns] at h1
      exact mem_dc_one.1 h1
  have key := hRN U hUB hUn hUp hUi ns ns.2 hnsB hBN3 u hu c hc.1 hc.2
  exact ⟨U.mul_mem (U.mul_mem hu hc.1) (U.inv_mem hu), key⟩

theorem burnsideI25c_weaklyClosed_of_rankOne [Finite G] {p : ℕ} (hp : p.Prime)
    {B N : Subgroup G} (hBN : IsSplitBNPair p B N) (hRN : IsRankOneNormal p B N)
    {P : Subgroup G} (hP : ∃ V : Sylow p G, Subgroup.normalizer (V : Subgroup G) ≤ P)
    {T : Subgroup G} (hT : IsPGroup p T) (hRT : pCoreOf p P ≤ T) :
    IsWeaklyClosedIn (pCoreOf p P) T := by
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : (cartan B N).Normal := hBN.normal_inter
  obtain ⟨S, hS⟩ := burnsideI2BN_exists_isBNPair (burnsideI2BN_toPre hBN)
  obtain ⟨V, hV⟩ := IsSplitBNPair.exists_sylow_normalizer hp hBN
  obtain ⟨U₀, hUB, hUn, hUp, hUi, hUN, hUH, hsat⟩ := hBN.split
  let U : Sylow p G := hUp.toSylow hUi
  have hUcoe : (U : Subgroup G) = U₀ := rfl
  have hBnorm : B ≤ Subgroup.normalizer U₀ :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hUB).1 hUn
  have hVB : (V : Subgroup G) ≤ B := hV ▸ Subgroup.le_normalizer
  have hsup := hUp.to_sup_of_normal_left' V.isPGroup' (hVB.trans hBnorm)
  have h1 : U₀ ⊔ (V : Subgroup G) = U₀ := U.is_maximal' hsup le_sup_left
  have h2 : (V : Subgroup G) = U₀ := V.is_maximal' hUp (h1 ▸ le_sup_right) |>.symm
  have hNU : Subgroup.normalizer (U : Subgroup G) = B := by
    rw [hUcoe, ← h2]; exact hV
  have hBU : ∀ b ∈ B, ∃ a ∈ U₀, ∃ c ∈ B ⊓ N, b = a * c :=
    burnsideI25b_decomp hUB inf_le_left hUn hUH
  have hRank : burnsideI25b_RankOne B N U₀ S :=
    burnsideI25c_rankOne_of_isRankOneNormal hS hUB hUn hUp hUi hRN
  have hLevi : burnsideI25b_Levi p B N U₀ S :=
    burnsideI25c_levi_of_rankOne hp hS U hUcoe hBnorm hUB hBU hRank
  exact burnsideI25b_weaklyClosed_of_Z hS U hNU
    (fun J hJ => burnsideI25b_Z_of_levi hS hBU hLevi hJ) hP hT hRT

theorem as_I_2_5 : I_2_5 := by
  intro G _ _ p hp hBN' P hP T hT hRT
  obtain ⟨B, N, hBN, hRN⟩ := hBN'
  exact burnsideI25c_weaklyClosed_of_rankOne hp hBN hRN hP hT hRT

end burnsideI25cStar

end CFSG.ASVolI
