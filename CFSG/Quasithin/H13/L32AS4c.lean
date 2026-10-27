module

public import CFSG.Quasithin.H13.L32ASecMod
public import CFSG.Quasithin.H13.L32A58a

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Quasithin.H6

variable {G : Type} [Group G]

theorem SecMod.of_nontrivial {L X Y : Subgroup G} {θ : ↥L →* Γ} (hYX : Y ≤ X)
    (hLX : L ≤ Subgroup.normalizer (X : Set G)) (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hcomm : ∀ a ∈ X, ∀ b ∈ X, a * b * a⁻¹ * b⁻¹ ∈ Y) (hsq : ∀ a ∈ X, a ^ 2 ∈ Y)
    (hsurj : Function.Surjective θ)
    (hker : ∀ l : ↥L, θ l = 1 → ∀ x ∈ X, (l : G) * x * (l : G)⁻¹ * x⁻¹ ∈ Y)
    (hnt : ∃ l : ↥L, ∃ x ∈ X, (l : G) * x * (l : G)⁻¹ * x⁻¹ ∉ Y) : SecMod L X Y θ := by
  have hconjY : ∀ g ∈ L, ∀ y ∈ Y, g * y * g⁻¹ ∈ Y := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hLY hg) y).mp hy
  have hconjX : ∀ g ∈ L, ∀ x ∈ X, g * x * g⁻¹ ∈ X := fun g hg x hx =>
    (Subgroup.mem_normalizer_iff.mp (hLX hg) x).mp hx
  have hXY : ∀ a ∈ X, ∀ y ∈ Y, a * y * a⁻¹ ∈ Y := by
    intro a ha y hy
    have h1 := hcomm a ha y (hYX hy)
    have e : a * y * a⁻¹ = (a * y * a⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact Y.mul_mem h1 hy
  let Kact : Subgroup ↥L :=
    { carrier := {l | ∀ x ∈ X, (l : G) * x * (l : G)⁻¹ * x⁻¹ ∈ Y}
      mul_mem' := by
        intro a b ha hb x hx
        have hbx : (b : G) * x * (b : G)⁻¹ ∈ X := hconjX _ b.2 x hx
        have e : ((a * b : ↥L) : G) * x * ((a * b : ↥L) : G)⁻¹ * x⁻¹ =
            ((a : G) * ((b : G) * x * (b : G)⁻¹ * x⁻¹) * (a : G)⁻¹) *
              ((a : G) * x * (a : G)⁻¹ * x⁻¹) := by
          push_cast
          group
        rw [e]
        exact Y.mul_mem (hconjY _ a.2 _ (hb x hx)) (ha x hx)
      one_mem' := by
        intro x hx
        simp
      inv_mem' := by
        intro a ha x hx
        have hax : (a : G)⁻¹ * x * (a : G)⁻¹⁻¹ ∈ X := hconjX _ (L.inv_mem a.2) x hx
        have h1 := ha _ hax
        have e : ((a⁻¹ : ↥L) : G) * x * ((a⁻¹ : ↥L) : G)⁻¹ * x⁻¹ =
            ((a : G) * ((a : G)⁻¹ * x * (a : G)⁻¹⁻¹) * (a : G)⁻¹ *
              ((a : G)⁻¹ * x * (a : G)⁻¹⁻¹)⁻¹)⁻¹ := by
          push_cast
          group
        rw [e]
        exact Y.inv_mem h1 }
  have hKn : Kact.Normal := by
    refine ⟨fun n hn g x hx => ?_⟩
    have hgx : (g : G)⁻¹ * x * (g : G)⁻¹⁻¹ ∈ X := hconjX _ (L.inv_mem g.2) x hx
    have h1 := hn _ hgx
    have e : ((g * n * g⁻¹ : ↥L) : G) * x * ((g * n * g⁻¹ : ↥L) : G)⁻¹ * x⁻¹ =
        (g : G) * ((n : G) * ((g : G)⁻¹ * x * (g : G)⁻¹⁻¹) * (n : G)⁻¹ *
          ((g : G)⁻¹ * x * (g : G)⁻¹⁻¹)⁻¹) * (g : G)⁻¹ := by
      push_cast
      group
    rw [e]
    exact hconjY _ g.2 _ h1
  have hsimp := G58.isSimpleGroup_sl32
  have hNn : (Kact.map θ).Normal := hKn.map θ hsurj
  refine ⟨hYX, hLX, hLY, hcomm, hsq, hsurj, hker, fun l hl => ?_⟩
  rcases hsimp.eq_bot_or_eq_top_of_normal (Kact.map θ) with hb | ht
  · have : θ l ∈ Kact.map θ := Subgroup.mem_map_of_mem θ hl
    rwa [hb, Subgroup.mem_bot] at this
  · exfalso
    obtain ⟨l₀, x, hx, hl₀⟩ := hnt
    have hm : θ l₀ ∈ Kact.map θ := by rw [ht]; exact Subgroup.mem_top _
    obtain ⟨k, hk, hkl⟩ := Subgroup.mem_map.mp hm
    have h1 : θ (k⁻¹ * l₀) = 1 := by rw [map_mul, map_inv, hkl, inv_mul_cancel]
    have h2 := hker _ h1
    have hkx : (k : G)⁻¹ * ((k : G) * (l₀ : G)⁻¹ * x * (l₀ : G) * (k : G)⁻¹) * (k : G) ∈ X := by
      have h3 : (l₀ : G)⁻¹ * x * (l₀ : G)⁻¹⁻¹ ∈ X := hconjX _ (L.inv_mem l₀.2) x hx
      have e : (k : G)⁻¹ * ((k : G) * (l₀ : G)⁻¹ * x * (l₀ : G) * (k : G)⁻¹) * (k : G) =
          (l₀ : G)⁻¹ * x * (l₀ : G)⁻¹⁻¹ := by group
      rw [e]
      exact h3
    have hl₀' : (l₀ : ↥L) ∈ Kact := by
      have e : l₀ = k * (k⁻¹ * l₀) := by group
      rw [e]
      refine Kact.mul_mem hk ?_
      intro y hy
      exact h2 y hy
    exact hl₀ (hl₀' x hx)

theorem eq_closure_of_fpf [Finite G] {A W Y : Subgroup G} (hYW : Y ≤ W)
    (hWY : W ≤ Subgroup.normalizer (Y : Set G)) (hAW : A ≤ Subgroup.normalizer (W : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (h4 : Y.relIndex W = 4)
    (hfpf : ∀ w ∈ W, (∀ a ∈ A, a * w * a⁻¹ * w⁻¹ ∈ Y) → w ∈ Y) {m : G} (hmW : m ∈ W)
    (hmY : m ∉ Y) : W = Subgroup.closure ({y | ∃ a ∈ A, a * m * a⁻¹ = y} ∪ (Y : Set G)) := by
  set W₀ := Subgroup.closure ({y | ∃ a ∈ A, a * m * a⁻¹ = y} ∪ (Y : Set G)) with hW₀
  have hW₀W : W₀ ≤ W := by
    rw [hW₀, Subgroup.closure_le]
    rintro _ (⟨a, ha, rfl⟩ | hy)
    · exact (Subgroup.mem_normalizer_iff.mp (hAW ha) m).mp hmW
    · exact hYW hy
  have hYW₀ : Y ≤ W₀ := fun y hy => Subgroup.subset_closure (Or.inr hy)
  have hmW₀ : m ∈ W₀ := Subgroup.subset_closure (Or.inl ⟨1, A.one_mem, by group⟩)
  have hconj : ∀ a ∈ A, ∀ w ∈ W₀, a * w * a⁻¹ ∈ W₀ := by
    intro a ha w hw
    induction hw using Subgroup.closure_induction with
    | mem w hw =>
      rcases hw with ⟨b, hb, rfl⟩ | hy
      · refine Subgroup.subset_closure (Or.inl ⟨a * b, A.mul_mem ha hb, by group⟩)
      · exact Subgroup.subset_closure (Or.inr ((Subgroup.mem_normalizer_iff.mp (hAY ha) w).mp hy))
    | one => simp
    | mul x y _ _ hx hy =>
      have e : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
      rw [e]
      exact W₀.mul_mem hx hy
    | inv x _ hx =>
      have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
      rw [e]
      exact W₀.inv_mem hx
  have hmul := Subgroup.relIndex_mul_relIndex Y W₀ W hYW₀ hW₀W
  rw [h4] at hmul
  have hne1 : Y.relIndex W₀ ≠ 1 := by
    intro h1
    rw [Subgroup.relIndex_eq_one] at h1
    exact hmY (h1 hmW₀)
  have hdvd : Y.relIndex W₀ ∣ 4 := ⟨_, hmul.symm⟩
  have hne2 : Y.relIndex W₀ ≠ 2 := by
    intro h2
    apply hmY
    refine hfpf m hmW fun a ha => ?_
    have hidx : (Y.subgroupOf W₀).index = 2 := h2
    have hamW₀ : a * m * a⁻¹ ∈ W₀ := hconj a ha m hmW₀
    have hamY : a * m * a⁻¹ ∉ Y := by
      intro h
      apply hmY
      have := (Subgroup.mem_normalizer_iff.mp (hAY (A.inv_mem ha)) _).mp h
      simpa [mul_assoc] using this
    have key : ((⟨m, hmW₀⟩ : ↥W₀)⁻¹ * ⟨a * m * a⁻¹, hamW₀⟩ : ↥W₀) ∈ Y.subgroupOf W₀ := by
      rw [Subgroup.mul_mem_iff_of_index_two hidx]
      simp only [Subgroup.mem_subgroupOf, Subgroup.coe_inv]
      constructor
      · intro h
        exact absurd (by simpa using Y.inv_mem h) hmY
      · intro h
        exact absurd h hamY
    rw [Subgroup.mem_subgroupOf] at key
    have hk : m⁻¹ * (a * m * a⁻¹) ∈ Y := by simpa using key
    have e : a * m * a⁻¹ * m⁻¹ = m * (m⁻¹ * (a * m * a⁻¹)) * m⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hWY hmW) _).mp hk
  have h4' : Y.relIndex W₀ = 4 := by
    have hle : Y.relIndex W₀ ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    interval_cases h : Y.relIndex W₀
    · exact absurd (Nat.zero_dvd.mp hdvd) (by norm_num)
    · exact absurd rfl hne1
    · exact absurd rfl hne2
    · exact absurd hdvd (by norm_num)
    · rfl
  rw [h4'] at hmul
  have h1 : W₀.relIndex W = 1 := by omega
  exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hW₀W

theorem conjClosure_le_closure {A L W Y : Subgroup G} {m : G} (hAL : A ≤ L)
    (hLY : L ≤ Subgroup.normalizer (Y : Set G))
    (hW : W ≤ Subgroup.closure ({y | ∃ a ∈ A, a * m * a⁻¹ = y} ∪ (Y : Set G))) :
    conjClosure W L ≤
      Subgroup.closure ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (Y : Set G)) := by
  set C := Subgroup.closure ({y | ∃ l : ↥L, (l : G) * m * (l : G)⁻¹ = y} ∪ (Y : Set G)) with hC
  refine conjClosure_le fun l hl w hw => ?_
  have key : ∀ y ∈ Subgroup.closure ({y | ∃ a ∈ A, a * m * a⁻¹ = y} ∪ (Y : Set G)),
      l * y * l⁻¹ ∈ C := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with ⟨a, ha, rfl⟩ | hy
      · exact Subgroup.subset_closure (Or.inl ⟨⟨l * a, L.mul_mem hl (hAL ha)⟩, by
          push_cast
          group⟩)
      · exact Subgroup.subset_closure
          (Or.inr ((Subgroup.mem_normalizer_iff.mp (hLY hl) y).mp hy))
    | one => simp
    | mul x y _ _ hx hy =>
      have e : l * (x * y) * l⁻¹ = (l * x * l⁻¹) * (l * y * l⁻¹) := by group
      rw [e]
      exact C.mul_mem hx hy
    | inv x _ hx =>
      have e : l * x⁻¹ * l⁻¹ = (l * x * l⁻¹)⁻¹ := by group
      rw [e]
      exact C.inv_mem hx
  exact key w (hW hw)

end CFSG.Quasithin.H13.L32A
