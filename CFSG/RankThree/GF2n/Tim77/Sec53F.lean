module

public import CFSG.RankThree.GF2n.Tim77.Sec53T

public section

namespace CFSG.RankThree.GF2n.Tim77

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Timmesfeld.RootInvolutions Subgroup

variable {G : Type} [Group G]

theorem sec53f_elt [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hq : Section3.q A Abar = 2) {g : G} (hg : g ∈ normalizer (A : Set G))
    (hne : conjSubgroup g (Section3.A0 A Abar) ≠ Section3.A0 A Abar)
    (h2 : Nat.card (Section3.A0 A Abar) ≠ 2) :
    ∃ (F : Subgroup G) (a : G), IsPGroup 2 F ∧ F ≤ normalizer (Section3.A0 A Abar : Set G) ∧
      a ∈ F ∧ a ∈ normalizer (A : Set G) ∧ a * a = 1 ∧ a ≠ 1 ∧
      a ∈ conjSubgroup g (Section3.Abar0 A Abar) ∧
      (∀ x ∈ A, a * x * a * x⁻¹ ∈ Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar)) ∧
      (∀ x ∈ Section3.A0 A Abar,
        (a * x * a = x ↔ x ∈ Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar))) := by
  obtain ⟨F, hF1, hF2, hF3, hF4, hF5⟩ := sec53_hyperplane_sec3 h hq hg hne
  have hFne : F ≠ ⊥ := fun e => h2 (hF5.mp e)
  obtain ⟨⟨a, haF⟩, ha1'⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hFne
  have ha1 : a ≠ 1 := fun e => ha1' (Subtype.ext e)
  have hgA : conjSubgroup g A = A := conjSubgroup_eq_self_iff.mpr hg
  have h' : Sec3Ctx A (conjSubgroup g Abar) (conjSubgroup g S₀) (conjSubgroup g B) := by
    have hc := h.conj g
    rwa [hgA] at hc
  have hA0 : Section3.A0 A (conjSubgroup g Abar) = conjSubgroup g (Section3.A0 A Abar) := by
    have hc := section3_A0_conj A Abar g
    rwa [hgA] at hc
  have hB0 : Section3.Abar0 A (conjSubgroup g Abar) =
      conjSubgroup g (Section3.Abar0 A Abar) := by
    have hc := section3_Abar0_conj A Abar g
    rwa [hgA] at hc
  have S' := h'.setup
  have haLb : a ∈ Section3.Abar0 A (conjSubgroup g Abar) := by
    rw [hB0]
    exact hF1 haF
  have ha2 : a * a = 1 := S'.sq_Ab (S'.Lb_le haLb)
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  refine ⟨F, a, ?_, hF4, haF, (S'.mem_Lb.mp haLb).2, ha2, ha1, hF1 haF, ?_, ?_⟩
  · refine notation_isPGroup_two_of_le S'.elem_Ab (fun x hx => S'.Lb_le ?_)
    rw [hB0]
    exact hF1 hx
  · intro x hx
    have hc := hF3 a haF x hx
    have e : a * x * a * x⁻¹ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by
      calc a * x * a * x⁻¹ = a * x * a⁻¹ * x⁻¹ := by rw [hai]
        _ = (x * a * x⁻¹ * a⁻¹)⁻¹ := by group
    rw [e]
    exact (Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar)).inv_mem hc
  · intro x hx
    have hxA : x ∈ A := h.setup.L_le hx
    constructor
    · intro hxa
      refine Subgroup.mem_inf.mpr ⟨hx, ?_⟩
      by_contra hxL
      have hxL' : x ∉ Section3.A0 A (conjSubgroup g Abar) := by
        rwa [hA0]
      have hcomm : x * a = a * x := by
        calc x * a = (a * x * a) * a := by rw [hxa]
          _ = a * x * (a * a) := by group
          _ = a * x := by rw [ha2, mul_one]
      have hinj := S'.commutator_injective hxA hxL'
      have hmem : (⟨a, haLb⟩ : ↥(Section3.Abar0 A (conjSubgroup g Abar))) = 1 := by
        apply hinj
        apply Subtype.ext
        show x * a * x⁻¹ * a⁻¹ = x * (1 : G) * x⁻¹ * (1 : G)⁻¹
        rw [hcomm]
        group
      exact ha1 (congrArg Subtype.val hmem)
    · intro hxZ
      have hxL' : x ∈ Section3.A0 A (conjSubgroup g Abar) := by
        rw [hA0]
        exact (Subgroup.mem_inf.mp hxZ).2
      have hcomm := S'.comm_L_Lb hxL' haLb
      calc a * x * a = x * a * a := by rw [hcomm]
        _ = x := by rw [mul_assoc, ha2, mul_one]

theorem sec53f_cube [Finite G] {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B)
    (hq : Section3.q A Abar = 2) {y : G} (hyA : y ∈ normalizer (A : Set G))
    (hyAb : y ∈ normalizer (Abar : Set G))
    (hyL : ∃ l ∈ Section3.A0 A Abar, y * l * y⁻¹ ≠ l)
    (hL2 : ∀ l ∈ Section3.A0 A Abar, ∀ l' ∈ Section3.A0 A Abar, y * l * y⁻¹ * l⁻¹ = 1 ∨
      y * l' * y⁻¹ * l'⁻¹ = 1 ∨ y * l * y⁻¹ * l⁻¹ = y * l' * y⁻¹ * l'⁻¹) :
    ∀ a ∈ A, a ∉ Section3.A0 A Abar → ∀ b ∈ Abar, b ∉ Section3.Abar0 A Abar →
      (a * b) ^ 3 = 1 := by
  have S := h.setup
  have hq1 : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← S.relIndex_Lb]
    exact hq
  have hA : ∀ x ∈ A, ∀ z ∈ A, x * z = z * x := fun x hx z hz => S.comm_A hx hz
  have hsqA : ∀ x ∈ A, x * x = 1 := fun x hx => S.sq_A hx
  have hAb : ∀ x ∈ Abar, ∀ z ∈ Abar, x * z = z * x := fun x hx z hz => S.symm.comm_A hx hz
  have hsqAb : ∀ x ∈ Abar, x * x = 1 := fun x hx => S.sq_Ab hx
  have hyA0 : ∀ x ∈ A, y * x * y⁻¹ * x⁻¹ ∈ Section3.A0 A Abar :=
    sec53t_comm_mem S.hL hA hsqA hq1 hyA hyAb
  have hyAb0 : ∀ x ∈ Abar, y * x * y⁻¹ * x⁻¹ ∈ Section3.Abar0 A Abar :=
    sec53t_comm_mem S.hLb hAb hsqAb hq hyAb hyA
  have hyX : y ∈ Subgroup.normalizer ((A ⊔ Abar : Subgroup G) : Set G) :=
    sec53t_mem_normalizer_sup hyA hyAb
  have hyM : ∀ x ∈ A ⊔ Abar, y * x * y⁻¹ * x⁻¹ ∈ Section3.M A Abar := by
    have hnormM : ∀ x ∈ A ⊔ Abar, ∀ m : G, m ∈ Section3.M A Abar ↔
        x * m * x⁻¹ ∈ Section3.M A Abar := fun x hx m =>
      Subgroup.mem_normalizer_iff.mp (S.sup_le_normalizer_M hx) m
    let P : Subgroup G :=
      { carrier := {x | x ∈ A ⊔ Abar ∧ y * x * y⁻¹ * x⁻¹ ∈ Section3.M A Abar}
        mul_mem' := by
          rintro x z ⟨hx, hxM⟩ ⟨hz, hzM⟩
          refine ⟨(A ⊔ Abar).mul_mem hx hz, ?_⟩
          have e : y * (x * z) * y⁻¹ * (x * z)⁻¹ =
              (y * x * y⁻¹ * x⁻¹) * (x * (y * z * y⁻¹ * z⁻¹) * x⁻¹) := by group
          rw [e]
          exact (Section3.M A Abar).mul_mem hxM ((hnormM x hx _).mp hzM)
        one_mem' := ⟨(A ⊔ Abar).one_mem, by simpa using (Section3.M A Abar).one_mem⟩
        inv_mem' := by
          rintro x ⟨hx, hxM⟩
          refine ⟨(A ⊔ Abar).inv_mem hx, ?_⟩
          have e : y * x⁻¹ * y⁻¹ * x⁻¹⁻¹ = x⁻¹ * (y * x * y⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
          rw [e]
          exact (hnormM x⁻¹ ((A ⊔ Abar).inv_mem hx) _).mp ((Section3.M A Abar).inv_mem hxM) }
    have hAP : A ≤ P := fun x hx =>
      ⟨Subgroup.mem_sup_left hx, S.hM ▸ Subgroup.mem_sup_left (hyA0 x hx)⟩
    have hAbP : Abar ≤ P := fun x hx =>
      ⟨Subgroup.mem_sup_right hx, S.hM ▸ Subgroup.mem_sup_right (hyAb0 x hx)⟩
    exact fun x hx => (sup_le hAP hAbP hx).2
  intro a ha haL b hb hbL
  exact sec53_cube_of_inner S hyX hyM hyL hL2 ha haL hb hbL

theorem sec53f_u {A A₀ : Subgroup G}
    (hA : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x) (hsq : ∀ x ∈ A, x * x = 1)
    (hA₀A : A₀ ≤ A) (hq : A₀.relIndex A = 2) {a y t c z : G}
    (haA : a ∈ normalizer (A : Set G)) (haA₀ : a ∈ normalizer (A₀ : Set G))
    (hy0 : ∀ x ∈ A₀, y * x * y⁻¹ = x) (ht : t ∈ A) (htA₀ : t ∉ A₀) (hc : c ∈ A₀)
    (hyt : y * t * y⁻¹ = c * t) (hz : z ∈ A₀) (hac : a * c * a⁻¹ = c * z) :
    (∀ x ∈ A₀, (y * (a * y * a⁻¹)) * x * (y * (a * y * a⁻¹))⁻¹ = x) ∧
    ∀ x ∈ A, x ∉ A₀ → (y * (a * y * a⁻¹)) * x * (y * (a * y * a⁻¹))⁻¹ = x * z := by
  have hcA : c ∈ A := hA₀A hc
  have hcc : c * c = 1 := hsq c hcA
  have hy1 : ∀ x ∈ A, x ∉ A₀ → y * x * y⁻¹ = x * c := by
    intro x hx hxA₀
    have hxt : x * t ∈ A₀ := sec53_mul_mem_of_relIndex_two hA hsq hq hx ht hxA₀ htA₀
    have h1 : y * x * y⁻¹ = (y * (x * t) * y⁻¹) * (y * t * y⁻¹)⁻¹ := by group
    have hct : (c * t)⁻¹ = t⁻¹ * c := by
      rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hcc]
    rw [h1, hy0 _ hxt, hyt, hct]
    group
  have hai : a⁻¹ ∈ normalizer (A : Set G) := inv_mem haA
  have hai0 : a⁻¹ ∈ normalizer (A₀ : Set G) := inv_mem haA₀
  have hconjA : ∀ x ∈ A, a⁻¹ * x * a ∈ A := fun x hx => by
    simpa using (Subgroup.mem_normalizer_iff.mp hai x).mp hx
  have hconjA₀ : ∀ x, x ∈ A₀ ↔ a⁻¹ * x * a ∈ A₀ := fun x => by
    simpa using Subgroup.mem_normalizer_iff.mp hai0 x
  have key : ∀ x : G, (y * (a * y * a⁻¹)) * x * (y * (a * y * a⁻¹))⁻¹ =
      y * (a * (y * (a⁻¹ * x * a) * y⁻¹) * a⁻¹) * y⁻¹ := by
    intro x
    group
  refine ⟨fun x hx => ?_, fun x hx hxn => ?_⟩
  · rw [key, hy0 _ ((hconjA₀ x).mp hx), show a * (a⁻¹ * x * a) * a⁻¹ = x by group, hy0 x hx]
  · have hxA' : a⁻¹ * x * a ∈ A := hconjA x hx
    have hxn' : a⁻¹ * x * a ∉ A₀ := fun h => hxn ((hconjA₀ x).mpr h)
    rw [key, hy1 _ hxA' hxn']
    have e : a * (a⁻¹ * x * a * c) * a⁻¹ = x * (c * z) := by
      calc a * (a⁻¹ * x * a * c) * a⁻¹ = x * (a * c * a⁻¹) := by group
        _ = x * (c * z) := by rw [hac]
    rw [e]
    calc y * (x * (c * z)) * y⁻¹ = (y * x * y⁻¹) * (y * c * y⁻¹) * (y * z * y⁻¹) := by group
      _ = x * c * c * z := by rw [hy1 x hx hxn, hy0 c hc, hy0 z hz]
      _ = x * z := by rw [mul_assoc x c c, hcc, mul_one]

theorem sec53f_hyp {A A₀ A₀' : Subgroup G}
    (hA : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x) (hA₀'A : A₀' ≤ A)
    (hl : ∃ l ∈ A₀', l ∉ A₀) {u z : G} (hz1 : z ≠ 1) (hzA : z ∈ A)
    (hu0 : ∀ x ∈ A₀, u * x * u⁻¹ = x) (hu1 : ∀ x ∈ A, x ∉ A₀ → u * x * u⁻¹ = x * z) :
    (∃ l ∈ A₀', u * l * u⁻¹ ≠ l) ∧ ∀ l ∈ A₀', ∀ l' ∈ A₀', u * l * u⁻¹ * l⁻¹ = 1 ∨
      u * l' * u⁻¹ * l'⁻¹ = 1 ∨ u * l * u⁻¹ * l⁻¹ = u * l' * u⁻¹ * l'⁻¹ := by
  have hcomm1 : ∀ l ∈ A₀', u * l * u⁻¹ * l⁻¹ = 1 ∨ u * l * u⁻¹ * l⁻¹ = z := by
    intro l hl'
    by_cases hlA₀ : l ∈ A₀
    · left
      rw [hu0 l hlA₀]
      group
    · right
      rw [hu1 l (hA₀'A hl') hlA₀]
      calc l * z * l⁻¹ = z * l * l⁻¹ := by rw [hA l (hA₀'A hl') z hzA]
        _ = z := by group
  obtain ⟨l₀, hl₀, hl₀A₀⟩ := hl
  refine ⟨⟨l₀, hl₀, ?_⟩, ?_⟩
  · rw [hu1 l₀ (hA₀'A hl₀) hl₀A₀]
    intro h
    apply hz1
    have h' : l₀ * z = l₀ * 1 := by rw [mul_one]; exact h
    exact mul_left_cancel h'
  · intro l hl l' hl'
    rcases hcomm1 l hl with h | h
    · exact Or.inl h
    rcases hcomm1 l' hl' with h' | h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr (h.trans h'.symm))

theorem sec53f_exists_u [Finite G] {A Ab A₀ Ab₀ M Z W A₀' : Subgroup G}
    (S : Prop24Setup A Ab A₀ Ab₀ M) (hq : A₀.relIndex A = 2) {a : G}
    (haA : a ∈ normalizer (A : Set G)) (haA₀ : a ∈ normalizer (A₀ : Set G)) (ha2 : a * a = 1)
    (hZ : Z ≤ A₀) (hZi : Z.relIndex A₀ = 2) (haZ : ∀ x ∈ A, a * x * a * x⁻¹ ∈ Z)
    (hCa : ∀ x ∈ A₀, (a * x * a = x ↔ x ∈ Z))
    (hcomm : ∀ x ∈ Ab₀, ∀ y ∈ conjSubgroup a Ab₀, x * y = y * x)
    (hWTI : IsTI W) (haW : a ∈ W) (ha1 : a ≠ 1) (hA₀'A : A₀' ≤ A)
    (hl : ∃ l ∈ A₀', l ∉ A₀) :
    ∃ u : G, u ∈ normalizer (A : Set G) ∧ u ∈ normalizer (W : Set G) ∧
      (∃ l ∈ A₀', u * l * u⁻¹ ≠ l) ∧
      ∀ l ∈ A₀', ∀ l' ∈ A₀', u * l * u⁻¹ * l⁻¹ = 1 ∨ u * l' * u⁻¹ * l'⁻¹ = 1 ∨
        u * l * u⁻¹ * l⁻¹ = u * l' * u⁻¹ * l'⁻¹ := by
  have hA : ∀ x ∈ A, ∀ x' ∈ A, x * x' = x' * x := fun x hx x' hx' => S.comm_A hx hx'
  have hsq : ∀ x ∈ A, x * x = 1 := fun x hx => S.sq_A hx
  have hA₀A : A₀ ≤ A := S.L_le
  obtain ⟨t, ht, htL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  have hnot : ¬ A₀ ≤ Z := by
    intro hle
    have h1 : Z.relIndex A₀ = 1 := Subgroup.relIndex_eq_one.mpr hle
    omega
  obtain ⟨c, hc, hcZ⟩ : ∃ c ∈ A₀, c ∉ Z := SetLike.not_le_iff_exists.mp hnot
  obtain ⟨y, hy, hyc⟩ := S.exists_commutator_eq ht htL hc
  have hcA : c ∈ A := hA₀A hc
  have hcc : c * c = 1 := hsq c hcA
  have hyN : y ∈ normalizer (A : Set G) := (S.mem_Lb.mp hy).2
  have hy0 : ∀ x ∈ A₀, y * x * y⁻¹ = x := fun x hx => by
    calc y * x * y⁻¹ = x * y * y⁻¹ := by rw [← S.comm_L_Lb hx hy]
      _ = x := by group
  have hyt : y * t * y⁻¹ = c * t := by
    have hcinv : c⁻¹ = c := inv_eq_of_mul_eq_one_right hcc
    calc y * t * y⁻¹ = (t * y * t⁻¹ * y⁻¹)⁻¹ * t := by group
      _ = c * t := by rw [hyc, hcinv]
  have hzZ : a * c * a * c⁻¹ ∈ Z := haZ c hcA
  have hz1 : a * c * a * c⁻¹ ≠ 1 := by
    intro e
    exact hcZ ((hCa c hc).mp (mul_inv_eq_one.mp e))
  have hzA₀ : a * c * a * c⁻¹ ∈ A₀ := hZ hzZ
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha2
  have hac : a * c * a⁻¹ = c * (a * c * a * c⁻¹) := by
    rw [hai]
    calc a * c * a = (a * c * a * c⁻¹) * c := by group
      _ = c * (a * c * a * c⁻¹) := (hA c hcA _ (hA₀A hzA₀)).symm
  obtain ⟨hu0, hu1⟩ := sec53f_u hA hsq hA₀A hq haA haA₀ hy0 ht htL hc hyt hzA₀ hac
  have hy' : y * (a * y * a⁻¹) = (a * y * a⁻¹) * y :=
    hcomm y hy (a * y * a⁻¹) ((mem_conjSubgroup_conj_t77 a y Ab₀).mpr hy)
  have hua : a * (y * (a * y * a⁻¹)) * a⁻¹ = y * (a * y * a⁻¹) := by
    have e : a * (y * (a * y * a⁻¹)) * a⁻¹ = (a * y * a⁻¹) * (a * (a * y * a⁻¹) * a⁻¹) := by
      group
    have e2 : a * (a * y * a⁻¹) * a⁻¹ = y := by
      calc a * (a * y * a⁻¹) * a⁻¹ = (a * a) * y * (a * a)⁻¹ := by group
        _ = y := by rw [ha2]; group
    rw [e, e2]
    exact hy'.symm
  have hcommu : (y * (a * y * a⁻¹)) * a = a * (y * (a * y * a⁻¹)) := by
    calc (y * (a * y * a⁻¹)) * a = (a * (y * (a * y * a⁻¹)) * a⁻¹) * a := by rw [hua]
      _ = a * (y * (a * y * a⁻¹)) := by group
  refine ⟨y * (a * y * a⁻¹), ?_, mem_normalizer_of_commute_of_isTI hWTI haW ha1 hcommu, ?_⟩
  · exact mul_mem hyN (mul_mem (mul_mem haA hyN) (inv_mem haA))
  · exact sec53f_hyp hA hA₀'A hl hz1 (hA₀A hzA₀) hu0 hu1

theorem sec53f_cube_four
    [Finite G]
    {A Abar S₀ B : Subgroup G} (h : Sec3Ctx A Abar S₀ B) (hq : Section3.q A Abar = 2)
    (hnc : ¬ Sec4A0LeCenterH A Abar) (h4 : Nat.card (Section3.A0 A Abar) = 4) :
    ∀ α ∈ A, α ∉ Section3.A0 A Abar → ∀ β ∈ Abar, β ∉ Section3.Abar0 A Abar →
      (α * β) ^ 3 = 1 := by
  have S := h.setup
  have hq1 : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← S.relIndex_Lb]
    exact hq
  obtain ⟨g, hg, hgn⟩ := tim77Sec50_holds G A Abar S₀ B h hq hnc
  have hne : conjSubgroup g (Section3.A0 A Abar) ≠ Section3.A0 A Abar :=
    fun e => hgn (conjSubgroup_eq_self_iff.mp e)
  have hgA : conjSubgroup g A = A := conjSubgroup_eq_self_iff.mpr hg
  have hq2 : (conjSubgroup g (Section3.A0 A Abar)).relIndex A = 2 := by
    have hc := relIndex_conjSubgroup_t77 g (Section3.A0 A Abar) A
    rw [hgA] at hc
    rw [hc]
    exact hq1
  have hq2A : conjSubgroup g (Section3.A0 A Abar) ≤ A := by
    calc conjSubgroup g (Section3.A0 A Abar) ≤ conjSubgroup g A :=
          (conjSubgroup_le_conj_iff g).2 S.L_le
      _ = A := hgA
  have hZi : (Section3.A0 A Abar ⊓ conjSubgroup g (Section3.A0 A Abar)).relIndex
      (Section3.A0 A Abar) = 2 :=
    sec53t_relIndex_inf (fun x hx y hy => S.comm_A hx hy) (fun x hx => S.sq_A hx) S.L_le hq2A
      hq1 hq2 hne.symm
  obtain ⟨F, a, hF2, hFN, haF, haN, ha2, ha1, haW, haZ, hCa⟩ :=
    sec53f_elt h hq hg hne (by omega)
  obtain ⟨n, hn, hcomm⟩ := sec53t_comm0 h hq hnc hF2 hFN
  have hnA : n ∈ normalizer (A : Set G) := sec51_normalizer_le h.hyp.ti S.L_le S.ne_bot hn
  obtain ⟨k1, k2, k3, k4, k5, k6, k7⟩ :=
    sec53t_conj_data hnA hn haN (hFN haF) ha2 inf_le_left hZi haZ hCa
  obtain ⟨g', hg'⟩ : ∃ g' : G, g' = n⁻¹ * g := ⟨_, rfl⟩
  have hg'A : g' ∈ normalizer (A : Set G) := by
    rw [hg']
    exact mul_mem (inv_mem hnA) hg
  have hg'A' : conjSubgroup g' A = A := conjSubgroup_eq_self_iff.mpr hg'A
  have h' : Sec3Ctx A (conjSubgroup g' Abar) (conjSubgroup g' S₀) (conjSubgroup g' B) := by
    have hc := h.conj g'
    rwa [hg'A'] at hc
  have hA0' : Section3.A0 A (conjSubgroup g' Abar) = conjSubgroup g' (Section3.A0 A Abar) := by
    have hc := section3_A0_conj A Abar g'
    rwa [hg'A'] at hc
  have hB0' : Section3.Abar0 A (conjSubgroup g' Abar) =
      conjSubgroup g' (Section3.Abar0 A Abar) := by
    have hc := section3_Abar0_conj A Abar g'
    rwa [hg'A'] at hc
  have hq' : Section3.q A (conjSubgroup g' Abar) = 2 := by
    have hc := section3_q_conj A Abar g'
    rwa [hg'A', hq] at hc
  have haW' : n⁻¹ * a * n ∈ conjSubgroup g' Abar := by
    rw [mem_conjSubgroup]
    have e : g'⁻¹ * (n⁻¹ * a * n) * g' = g⁻¹ * a * g := by
      rw [hg']
      group
    rw [e]
    exact S.Lb_le (mem_conjSubgroup.mp haW)
  have ha'1 : n⁻¹ * a * n ≠ 1 := by
    intro e
    apply ha1
    have e' : a = n * (n⁻¹ * a * n) * n⁻¹ := by group
    rw [e', e]
    group
  have hA₀'A : conjSubgroup g' (Section3.A0 A Abar) ≤ A := by
    calc conjSubgroup g' (Section3.A0 A Abar) ≤ conjSubgroup g' A :=
          (conjSubgroup_le_conj_iff g').2 S.L_le
      _ = A := hg'A'
  have hA₀'ne : ∃ l ∈ conjSubgroup g' (Section3.A0 A Abar), l ∉ Section3.A0 A Abar := by
    by_contra hcon
    have hle0 : conjSubgroup g' (Section3.A0 A Abar) ≤ Section3.A0 A Abar := fun l hl =>
      Classical.byContradiction fun hlA => hcon ⟨l, hl, hlA⟩
    apply hne
    have hnA₀ : conjSubgroup n⁻¹ (Section3.A0 A Abar) = Section3.A0 A Abar :=
      conjSubgroup_eq_self_iff.mpr (inv_mem hn)
    have e1 : conjSubgroup g' (Section3.A0 A Abar) =
        conjSubgroup n⁻¹ (conjSubgroup g (Section3.A0 A Abar)) := by
      rw [hg', conjSubgroup_mul]
    have hle : conjSubgroup n⁻¹ (conjSubgroup g (Section3.A0 A Abar)) ≤
        conjSubgroup n⁻¹ (Section3.A0 A Abar) := by
      rw [← e1, hnA₀]
      exact hle0
    exact Subgroup.eq_of_le_of_card_ge ((conjSubgroup_le_conj_iff n⁻¹).1 hle)
      (by rw [card_conjSubgroup])
  obtain ⟨u, huA, huW, hyL, hL2⟩ := sec53f_exists_u S hq1 k1 k2 k3 k4 k5 k6 k7
    (hcomm a haF) (isTI_conjSubgroup S.ti_Ab g') haW' ha'1 hA₀'A hA₀'ne
  have hcube := sec53f_cube h' hq' huA huW (by rw [hA0']; exact hyL)
    (by rw [hA0']; exact hL2)
  intro α hα hαL β hβ hβL
  have h1 : g' * α * g'⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg'A α).mp hα
  have h2 : g' * α * g'⁻¹ ∉ Section3.A0 A (conjSubgroup g' Abar) := by
    rw [hA0']
    intro hm
    exact hαL ((mem_conjSubgroup_conj_t77 g' α _).mp hm)
  have h3 : g' * β * g'⁻¹ ∈ conjSubgroup g' Abar := (mem_conjSubgroup_conj_t77 g' β Abar).mpr hβ
  have h4' : g' * β * g'⁻¹ ∉ Section3.Abar0 A (conjSubgroup g' Abar) := by
    rw [hB0']
    intro hm
    exact hβL ((mem_conjSubgroup_conj_t77 g' β _).mp hm)
  have h5 := hcube _ h1 h2 _ h3 h4'
  have e : (g' * α * g'⁻¹) * (g' * β * g'⁻¹) = g' * (α * β) * g'⁻¹ := by group
  rw [e, conj_pow] at h5
  exact (conj_eq_one_iff_t77 g' _).mp h5

theorem sec53_four_holds :
    Tim77Sec53FourStatement := by
  intro G _ _ A Abar S₀ B h hq hnc h4 _inst
  have S := h.setup
  have hq1 : (Section3.A0 A Abar).relIndex A = 2 := by
    rw [← S.relIndex_Lb]
    exact hq
  haveI hN : ((Section3.M A Abar).subgroupOf (A ⊔ Abar)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer S.M_le_X).mpr S.sup_le_normalizer_M
  obtain ⟨a, ha, haL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.L_le S.ne)
  obtain ⟨b, hb, hbL⟩ := SetLike.exists_of_lt (lt_of_le_of_ne S.Lb_le S.Lb_ne)
  exact sec53_dihedral_three S hq1 ha haL hb hbL (sec53f_cube_four h hq hnc h4 a ha haL b hb hbL)

end CFSG.RankThree.GF2n.Tim77
