module

public import CFSG.Timmesfeld.Bridge.RootStructN0CycleMain
public import CFSG.Timmesfeld.Bridge.RootStructN0Fix
public import CFSG.Timmesfeld.Bridge.RootStructN0CycleRank

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type} [Group G] {D : Set G}

theorem fixUnique_of (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) : FixUnique D := by
  intro d a e g hd ha hda hdaD haT he hde hdeD heL hg hgd hgL hgN
  obtain ⟨hp, hp2, y, hy, hyg⟩ := hg
  exact existsUnique_conj_mem_rootSet_of_line h hc hs hconn hAll hd ha hda hdaD haT he hde hdeD
    heL hp hp2 hy hyg hgd hgL hgN

theorem uniqueGate_of (h : Hyp G D) (hc : RootClosure D) (hs : SpecialClosure D)
    (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D) (hbad : ThinAllBad D)
    (h3 : ¬ ThreeLines D) : UniqueGate D := by
  intro b x c c' hb hx hbx hoddbx hcD hbc hbcD h4 hc'D hbc' hbc'D h4'
  exact ThinAllBad.mem_rootSet_of_gate h hc hs hconn hAll hbad h3 hb hx hbx hoddbx hcD hbc hbcD
    h4 hc'D hbc' hbc'D h4'

theorem false_of_thinAllBad (hOdd : ∀ (G : Type) [Group G] (D : Set G), Hyp G D → RootClosure D →
    SpecialClosure D → Moufang.ExcCollConnected D → AllLinesTI D → ¬ ThreeLines D → ThinAllBad D →
    FixUnique D → UniqueGate D → ∀ {g : G}, InvTorus D g → ∀ {p : ℤ → G}, TorusPath D g p → ¬
    Commute (p 0) (p 3) → Odd (orderOf (p 0 * p 3)) → ¬ Commute (p 1) (p 4) → Odd (orderOf (p 1 * p
    4)) → ∀ {μ₁ μ₂ t₂ k₁ k₂ u₁ u₂ : G}, μ₁ ∈ D → μ₂ ∈ D → (∀ i, μ₁ * p (3 - i) * μ₁⁻¹ ∈ rootSet D (p
    i)) → (∀ i, μ₂ * p (5 - i) * μ₂⁻¹ ∈ rootSet D (p i)) → InvTorus D t₂ → (∀ i, t₂ * p i * t₂⁻¹ ∈
    rootSet D (p i)) → μ₂ * t₂ * μ₂⁻¹ = t₂⁻¹ → k₁ ∈ rootGroup D (p 0) → u₁ ∈ rootSet D (p 3) → μ₁ =
    k₁ * u₁ * k₁⁻¹ → k₂ ∈ rootGroup D (p 1) → u₂ ∈ rootSet D (p 4) → μ₂ = k₂ * u₂ * k₂⁻¹ → ¬ Commute
    μ₂ μ₁ → Odd (orderOf (μ₂ * μ₁)) → False) (h : Hyp G D) (hc : RootClosure D)
    (hs : SpecialClosure D) (hconn : Moufang.ExcCollConnected D) (hAll : AllLinesTI D)
    (h3 : ¬ ThreeLines D) (hbad : ThinAllBad D) (hl : ∃ d ∈ D, ∃ e ∈ rootSet D d, e ≠ d) :
    False := by
  have hclass := h.isClass
  have hD := h.root
  have := h.finite
  have hFU := fixUnique_of h hc hs hconn hAll
  have hUG := uniqueGate_of h hc hs hconn hAll hbad h3
  obtain ⟨b, hb, x, hx, hbx, hoddbx, h1⟩ := exists_oneOpposite_pair h hconn
  obtain ⟨h₀, -, hp, hp2, hh₀b, hh₀x, -, μ₁, hμ₁D, -, hμ₁h, hμ₁b, hμ₁x, k₁, hk₁, u₁, hu₁,
    hμ₁eq⟩ := exists_weyl_of_oneOpposite h hc hs hl hb hx hbx hoddbx h1
  have hg₀ : InvTorus D h₀ := ⟨hp, hp2, μ₁, hμ₁D, hμ₁h⟩
  obtain ⟨c, hcD, hbc, hbcD, h4xc⟩ := h1
  have hh₀c := conj_mem_rootSet_of_gate h hc hs hUG hb hx hbx hoddbx hcD hbc hbcD h4xc hh₀b hh₀x
  have h4cx : orderOf (c * x) = 4 := by rwa [orderOf_mul_comm_eq]
  have hcT : c ∉ rootSet D b := fun h' => by
    have := (orderOf_mul_eq_four_iff_of_mem_rootSet hD hb h' hx).1 h4cx
    rw [this] at hoddbx
    exact absurd hoddbx (by decide)
  have hcx : ¬ Commute c x :=
    not_commute_of_orderOf_mul_eq_four (hD.mul_self_eq_one hcD) (hD.mul_self_eq_one hx) h4cx
  obtain ⟨hwD, hcw, hxw, -⟩ := sq_mem_of_orderOf_eq_four hD hcD hx h4cx
  have hcwD : c * (c * x) ^ 2 ∈ D := mul_sq_mem_of_orderOf_eq_four hclass hD hcD hx h4cx
  have hxwD : x * (c * x) ^ 2 ∈ D := by
    have := mul_sq_mem_of_orderOf_eq_four hclass hD hx hcD h4xc
    rwa [← mul_sq_eq_mul_sq_comm (hD.mul_self_eq_one hcD) (hD.mul_self_eq_one hx) h4cx] at this
  have hcwT : c ∉ rootSet D ((c * x) ^ 2) := fun h' => hcx ((h'.2 x hx).2 hxw.symm)
  have hxwT : x ∉ rootSet D ((c * x) ^ 2) := fun h' => hcx ((h'.2 c hcD).2 hcw.symm).symm
  have hxL : x ∉ rootGroup D ((c * x) ^ 2) ⊔ rootGroup D c := fun h' =>
    hcx (commute_of_mem_sup_rootGroup hwD hcD hcw.symm (right_mem_line hcD) h')
  have hTwo : ∀ v ∈ D, ∀ u ∈ D, Commute v u → v * u ∈ D → u ∉ rootSet D v →
      ∃ e ∈ D, Commute v e ∧ v * e ∈ D ∧ e ∉ rootSet D v ∧
        e ∉ rootGroup D v ⊔ rootGroup D u := fun v hv u hu hvu hvuD huT =>
    exists_other_line h hc hs h3 hwD hcD hx ⟨hcw.symm, by rw [← hcw.eq]; exact hcwD, hcwT⟩
      ⟨hxw.symm, by rw [← hxw.eq]; exact hxwD, hxwT⟩ hxL hv hu hvu hvuD huT
  obtain ⟨p, hP, hp0, hp1⟩ := exists_torusPath h hc hs h3 hFU hg₀ hTwo hb hcD hbc hbcD
    (fun h' => hcT h') hh₀b hh₀c
  have hp0D := hP.mem 0
  have hp1D := hP.mem 1
  have hp2D := hP.mem 2
  have hp3D := hP.mem 3
  have hp4D := hP.mem 4
  have c01 : Commute (p 0) (p 1) := by simpa using hP.comm 0
  have c12 : Commute (p 1) (p 2) := by simpa using hP.comm 1
  have c23 : Commute (p 2) (p 3) := by simpa using hP.comm 2
  have c34 : Commute (p 3) (p 4) := by simpa using hP.comm 3
  have m01 : p 0 * p 1 ∈ D := by simpa using hP.mul_mem 0
  have m12 : p 1 * p 2 ∈ D := by simpa using hP.mul_mem 1
  have m23 : p 2 * p 3 ∈ D := by simpa using hP.mul_mem 2
  have m34 : p 3 * p 4 ∈ D := by simpa using hP.mul_mem 3
  have n01 : p 1 ∉ rootSet D (p 0) := by simpa using hP.not_mem 0
  have n23 : p 3 ∉ rootSet D (p 2) := by simpa using hP.not_mem 2
  have t3 : p 4 ∉ rootGroup D (p 2) ⊔ rootGroup D (p 3) := by simpa using hP.turn 3
  have h41x : orderOf (p 1 * x) = 4 := by rw [hp1]; exact h4cx
  have hx3 : x ∈ rootSet D (p 3) := by
    rcases hP.mem_rootSet_of_special h hc hs h3 hFU hg₀ hx h41x hh₀x with h' | h'
    · exfalso
      have hc0 : Commute (p (1 - 2)) (p 0) := by
        have := hP.comm_sub 0
        norm_num at this ⊢
        exact this
      have := (h'.2 (p 0) hp0D).2 hc0
      rw [hp0] at this
      exact hbx this.symm
    · simpa using h'
  have hTx : rootSet D x = rootSet D (p 3) := rootSet_eq_of_mem hx3
  have hb0 : p 0 ∈ rootSet D b := by
    rw [hp0]
    exact mem_rootSet_self hb
  obtain ⟨h03, hodd03⟩ := opposite_of_mem_rootSet_of_opposite hD hb hx hb0
    (mem_rootSet_comm hp3D hx3) ⟨hbx, hoddbx⟩
  have hr₁ : ∀ i, μ₁ * p (3 - i) * μ₁⁻¹ ∈ rootSet D (p i) := by
    have hμ1 : μ₁ * p (0 + 3) * μ₁⁻¹ ∈ rootSet D (p 0) := by
      have := conj_mem_rootSet_conj hclass (μ := μ₁) (mem_rootSet_comm hp3D hx3)
      rw [rootSet_eq_of_mem hμ₁x, ← hp0] at this
      rwa [zero_add]
    have hμ2 : μ₁ * p 0 * μ₁⁻¹ ∈ rootSet D (p (0 + 3)) := by
      rw [zero_add, hp0, ← hTx]
      exact hμ₁b
    intro i
    have := hP.reflect h hc hs hconn hAll h3 hFU hUG hg₀ (j := 0) (by rw [zero_add]; exact h03)
      (by rw [zero_add]; exact hodd03) hμ₁h hμ1 hμ2 i
    rwa [show 2 * (0 : ℤ) + 3 - i = 3 - i by ring] at this
  have hper : ∀ {a b' : ℤ}, p b' ∈ rootSet D (p a) → 0 < b' - a → b' - a ≤ 6 → False :=
    fun hab h0 h6 => hP.false_of_isPeriod_le_six h hc hs hconn hAll hbad h3 h03 hodd03
      (hP.isPeriod_of_mem_rootSet h hc hs h3 hFU hg₀ hab) h0 h6
  have hNP : Moufang.NoPolar D :=
    noPolar_of_lineTI h hc hs hconn hp0D hp1D c01 m01 n01 (hAll _ hp0D _ hp1D c01 m01 n01)
  obtain ⟨h14, hodd14⟩ : ¬ Commute (p 1) (p 4) ∧ Odd (orderOf (p 1 * p 4)) := by
    rcases commute_or_orderOf_mul_eq_four_or_odd hD hp1D hp4D with hc14 | h414 | ho
    · exfalso
      by_cases hT : p 4 ∈ rootSet D (p 1)
      · exact hper (a := 1) (b' := 4) hT (by norm_num) (by norm_num)
      · have hne : p 1 ≠ p 4 := fun h' => hT (h' ▸ mem_rootSet_self hp1D)
        rcases hP.mem_rootSet_of_collinear h hc hs h3 hFU hg₀ hp4D hc14
            (hNP _ hp1D _ hp4D hc14 hne) hT (hP.fix 4) with h' | h'
        · exact hper (a := 0) (b' := 4) (by simpa using h') (by norm_num) (by norm_num)
        · exact hper (a := 2) (b' := 4) (by simpa using h') (by norm_num) (by norm_num)
    · exfalso
      rcases hP.mem_rootSet_of_special h hc hs h3 hFU hg₀ hp4D h414 (hP.fix 4) with h' | h'
      · exact hper (a := -1) (b' := 4) (by simpa using h') (by norm_num) (by norm_num)
      · exact hper (a := 3) (b' := 4) (by simpa using h') (by norm_num) (by norm_num)
    · exact ⟨ho.2, ho.1⟩
  have s24 : orderOf (p 2 * p 4) = 4 :=
    orderOf_mul_eq_four_of_path h hc hs hconn hAll hp2D hp3D hp4D c23 m23 n23 c34 m34 t3
  have h442 : orderOf (p 4 * p 2) = 4 := by rw [orderOf_mul_comm_eq]; exact s24
  obtain ⟨t₂, ht₂Y, hpt, hpt2, ht₂1, ht₂4, htor₂, μ₂, hμ₂D, -, hμ₂t, hμ₂1, hμ₂4, k₂, hk₂, u₂,
    hu₂, hμ₂eq⟩ := exists_weyl_of_oneOpposite h hc hs hl hp1D hp4D h14 hodd14
      ⟨p 2, hp2D, c12, m12, h442⟩
  have ht₂ : InvTorus D t₂ := ⟨hpt, hpt2, μ₂, hμ₂D, hμ₂t⟩
  have ht₂2 := conj_mem_rootSet_of_gate h hc hs hUG hp1D hp4D h14 hodd14 hp2D c12 m12 h442 ht₂1
    ht₂4
  have hN1 : ∀ {g : G}, g * p 1 * g⁻¹ ∈ rootSet D (p 1) ↔
      g ∈ Subgroup.normalizer (rootGroup D (p 1) : Set G) := fun {_} =>
    conj_mem_rootSet_iff_mem_normalizer h hc hp1D
  have hN4 : ∀ {g : G}, g * p 4 * g⁻¹ ∈ rootSet D (p 4) ↔
      g ∈ Subgroup.normalizer (rootGroup D (p 4) : Set G) := fun {_} =>
    conj_mem_rootSet_iff_mem_normalizer h hc hp4D
  have hh₀1 := hN1.1 (hP.fix 1)
  have hh₀4 := hN4.1 (hP.fix 4)
  have ht'Y : h₀⁻¹ * t₂ * h₀⁻¹⁻¹ ∈ rootGroup D (p 4) ⊔ rootGroup D (p 1) :=
    conj_mem_sup_of_conj_mem_rootSet hclass (hN4.2 (Subgroup.inv_mem _ hh₀4))
      (hN1.2 (Subgroup.inv_mem _ hh₀1)) ht₂Y
  have ht'1 : (h₀⁻¹ * t₂ * h₀⁻¹⁻¹) * p 1 * (h₀⁻¹ * t₂ * h₀⁻¹⁻¹)⁻¹ ∈ rootSet D (p 1) :=
    hN1.2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh₀1) (hN1.1 ht₂1))
      (Subgroup.inv_mem _ (Subgroup.inv_mem _ hh₀1)))
  have ht'4 : (h₀⁻¹ * t₂ * h₀⁻¹⁻¹) * p 4 * (h₀⁻¹ * t₂ * h₀⁻¹⁻¹)⁻¹ ∈ rootSet D (p 4) :=
    hN4.2 (Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.inv_mem _ hh₀4) (hN4.1 ht₂4))
      (Subgroup.inv_mem _ (Subgroup.inv_mem _ hh₀4)))
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1
    (htor₂ _ ht'Y ht'1 ht'4 (orderOf_conj_eq h₀⁻¹ t₂))
  have hzp : t₂ ∈ Subgroup.zpowers (h₀ * t₂ * h₀⁻¹) := by
    refine Subgroup.mem_zpowers_iff.2 ⟨n, ?_⟩
    rw [conj_zpow, hn]
    group
  have ht₂all : ∀ i, t₂ * p i * t₂⁻¹ ∈ rootSet D (p i) :=
    hP.fix_of_mem_zpowers h hc hs h3 hFU hTwo hg₀ ht₂ (j := 1) ht₂1 (by simpa using ht₂2) hzp
  have hPt₂ : TorusPath D t₂ p := ⟨hP.mem, hP.comm, hP.mul_mem, hP.not_mem, hP.turn, ht₂all⟩
  have hr₂ : ∀ i, μ₂ * p (5 - i) * μ₂⁻¹ ∈ rootSet D (p i) := by
    intro i
    have := hPt₂.reflect h hc hs hconn hAll h3 hFU hUG ht₂ (j := 1)
      (by simpa using h14) (by simpa using hodd14) hμ₂t (by simpa using hμ₂4)
      (by simpa using hμ₂1) i
    rwa [show 2 * (1 : ℤ) + 3 - i = 5 - i by ring] at this
  have hk₁' : k₁ ∈ rootGroup D (p 0) := by rw [hp0]; exact hk₁
  have hu₁' : u₁ ∈ rootSet D (p 3) := by rw [← hTx]; exact hu₁
  rcases commute_or_orderOf_mul_eq_four_or_odd hD hμ₂D hμ₁D with hcm | h4m | ⟨hoddm, hncm⟩
  ·
    have hρ : ∀ i, μ₂ * μ₁ * p i * (μ₂ * μ₁)⁻¹ ∈ rootSet D (p (i + 2)) := by
      intro i
      have h1' := hr₁ (3 - i)
      rw [show (3 : ℤ) - (3 - i) = i by ring] at h1'
      have h2' := hr₂ (i + 2)
      rw [show (5 : ℤ) - (i + 2) = 3 - i by ring] at h2'
      have h3' := conj_mem_rootSet_conj hclass (μ := μ₂) h1'
      rw [rootSet_eq_of_mem h2'] at h3'
      rwa [show μ₂ * μ₁ * p i * (μ₂ * μ₁)⁻¹ = μ₂ * (μ₁ * p i * μ₁⁻¹) * μ₂⁻¹ by group]
    have hρ2 : μ₂ * μ₁ * (μ₂ * μ₁) = 1 := by
      rw [show μ₂ * μ₁ * (μ₂ * μ₁) = μ₂ * (μ₁ * μ₂) * μ₁ by group, ← hcm.eq,
        show μ₂ * (μ₂ * μ₁) * μ₁ = (μ₂ * μ₂) * (μ₁ * μ₁) by group, hD.mul_self_eq_one hμ₂D,
        hD.mul_self_eq_one hμ₁D, one_mul]
    have h1' : μ₂ * μ₁ * p 0 * (μ₂ * μ₁)⁻¹ ∈ rootSet D (p 2) := by
      have := hρ 0
      rwa [zero_add] at this
    have h2' : μ₂ * μ₁ * p 2 * (μ₂ * μ₁)⁻¹ ∈ rootSet D (p 4) := by
      have := hρ 2
      rwa [show (2 : ℤ) + 2 = 4 by norm_num] at this
    have h3' := conj_mem_rootSet_conj hclass (μ := μ₂ * μ₁) h1'
    rw [rootSet_eq_of_mem h2', show μ₂ * μ₁ * (μ₂ * μ₁ * p 0 * (μ₂ * μ₁)⁻¹) * (μ₂ * μ₁)⁻¹ =
      (μ₂ * μ₁ * (μ₂ * μ₁)) * p 0 * (μ₂ * μ₁ * (μ₂ * μ₁))⁻¹ by group, hρ2, one_mul, inv_one,
      mul_one] at h3'
    exact hper (a := 0) (b' := 4) (mem_rootSet_comm hp4D h3') (by norm_num) (by norm_num)
  · exact hP.false_of_four h hc hs hconn hAll h3 hbad h03 hodd03 h14 hodd14 hμ₁D hμ₂D hr₁ hr₂
      hk₁' hu₁' hμ₁eq hk₂ hu₂ hμ₂eq h4m
  · exact hOdd G D h hc hs hconn hAll h3 hbad hFU hUG hg₀ hP h03 hodd03 h14 hodd14 hμ₁D hμ₂D hr₁
      hr₂ ht₂ ht₂all hμ₂t hk₁' hu₁' hμ₁eq hk₂ hu₂ hμ₂eq hncm hoddm

theorem thinAllBadFalse_of_cycleOddStep (H : ∀ (G : Type) [Group G] (D : Set G), Hyp G D →
    RootClosure D → SpecialClosure D → Moufang.ExcCollConnected D → AllLinesTI D → ¬ ThreeLines D →
    ThinAllBad D → FixUnique D → UniqueGate D → ∀ {g : G}, InvTorus D g → ∀ {p : ℤ → G}, TorusPath D
    g p → ¬ Commute (p 0) (p 3) → Odd (orderOf (p 0 * p 3)) → ¬ Commute (p 1) (p 4) → Odd (orderOf
    (p 1 * p 4)) → ∀ {μ₁ μ₂ t₂ k₁ k₂ u₁ u₂ : G}, μ₁ ∈ D → μ₂ ∈ D → (∀ i, μ₁ * p (3 - i) * μ₁⁻¹ ∈
    rootSet D (p i)) → (∀ i, μ₂ * p (5 - i) * μ₂⁻¹ ∈ rootSet D (p i)) → InvTorus D t₂ → (∀ i, t₂ * p
    i * t₂⁻¹ ∈ rootSet D (p i)) → μ₂ * t₂ * μ₂⁻¹ = t₂⁻¹ → k₁ ∈ rootGroup D (p 0) → u₁ ∈ rootSet D (p
    3) → μ₁ = k₁ * u₁ * k₁⁻¹ → k₂ ∈ rootGroup D (p 1) → u₂ ∈ rootSet D (p 4) → μ₂ = k₂ * u₂ * k₂⁻¹ →
    ¬ Commute μ₂ μ₁ → Odd (orderOf (μ₂ * μ₁)) → False) : ThinAllBadFalse :=
  fun _ _ _ h _ hl hc hs hconn h3 hAll hbad => false_of_thinAllBad H h hc hs hconn hAll h3 hbad hl

end CFSG.Timmesfeld.Bridge
