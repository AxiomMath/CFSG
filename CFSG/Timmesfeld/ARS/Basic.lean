module

public import CFSG.Timmesfeld.ARS.BasicBridge

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement Pointwise

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem eq_one_of_mul_mem_rootElts [Finite G] (hR : IsRootClass R) {A B : Subgroup G}
    (hA : A ∈ R) (h : Opposite A B) {g : G}
    (hg : g ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G)) (hgX : g ∉ A ⊔ B) {x : G}
    (hx : x ∈ A ⊔ B) (hgx : g * x ∈ rootElts R) : x = 1 := by
  by_contra hx1
  obtain ⟨C, hC, hcC, -⟩ := hgx
  have hsqA := hR.mul_self A hA
  obtain ⟨y, hy, hxy⟩ := h.exists_conjSub_ne hsqA hx hx1
  have hA' : conjSub A y ∈ R := hR.conjSub_mem hA y
  have hgfix : ∀ H ≤ A ⊔ B, conjSub H g = H := fun H hH =>
    conjSub_of_forall_commute fun k hk => (Subgroup.mem_centralizer_iff.1 hg k (hH hk)).symm
  have hcA' : conjSub (conjSub A y) (g * x) = conjSub A (x * y) := by
    rw [conjSub_mul, ← conjSub_mul A x y,
      hgfix _ (Opposite.conjSub_le_sup (Subgroup.mul_mem _ hx hy))]
  have hxy' : conjSub A (x * y) ≠ conjSub A y := by
    rw [conjSub_mul]
    exact hxy
  have hcne : conjSub (conjSub A y) (g * x) ≠ conjSub A y := hcA' ▸ hxy'
  have hA'C : conjSub A y ≠ C := by
    intro e
    apply hcne
    rw [e]
    exact conjSub_of_mem hcC
  rcases hR.rel _ hA' C hC hA'C with hcomm | hopp | hspec
  · exact hcne (conjSub_of_forall_commute fun a ha => (hcomm a ha _ hcC).symm)
  · have h1 := hopp.sup_conjSub_eq (hR.mul_self _ hA') (one_mem _) (Subgroup.mem_sup_right hcC)
      (by rw [conjSub_one]; exact hcne.symm)
    rw [conjSub_one, hcA'] at h1
    have h2 := h.sup_conjSub_eq hsqA hy (Subgroup.mul_mem _ hx hy) hxy'.symm
    have hcX : g * x ∈ A ⊔ B := h2 ▸ h1 ▸ Subgroup.mem_sup_right hcC
    apply hgX
    have : g = g * x * x⁻¹ := by group
    rw [this]
    exact Subgroup.mul_mem _ hcX (Subgroup.inv_mem _ hx)
  · obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA'
    have hw : g * x * a * (g * x)⁻¹ ∈ conjSub A (x * y) := hcA' ▸ conj_mem_conjSub _ ha
    have hcomm : Commute a (g * x * a * (g * x)⁻¹) := by
      rw [conj_eq_commutator_mul]
      have hd : Commute ⁅g * x, a⁆ a := by
        refine hspec.2.1 _ ?_ a ha
        rw [Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator hcC ha
      exact hd.symm.mul_right (Commute.refl a)
    exact hxy' (h.conjSub_eq_of_commute hsqA hy (Subgroup.mul_mem _ hx hy) ha ha1 hw
      (fun h1 => ha1 (conj_eq_one_iff.1 h1)) hcomm)

theorem not_commuting_of_opposite_of_mem_lambdaSet [Finite G] (hR : IsRootClass R)
    {A B C : Subgroup G} (hA : A ∈ R) (hAB : Opposite A B) (hC : C ∈ lambdaSet R B) :
    ¬ Commuting A C := by
  intro hAC
  obtain ⟨⟨hCR, -, hBC⟩, hcov⟩ := hC
  have hcent : ∀ c ∈ C, c ∈ Subgroup.centralizer ((A ⊔ B : Subgroup G) : Set G) := by
    intro c hc
    have : Commuting (A ⊔ B) C := Commuting.sup_left hAC hBC
    exact commuting_iff_le_centralizer.1 this hc
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
  by_cases hcX : c ∈ A ⊔ B
  · exact hc1 (hAB.eq_one_of_mem_centralizer (hR.mul_self A hA) hcX (hcent c hc))
  · obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hA
    obtain ⟨b, hb, hb1, -⟩ := hAB.2.1 a ha ha1
    have hne : c * b ≠ 1 := by
      intro e
      apply hcX
      rw [eq_inv_of_mul_eq_one_left e]
      exact Subgroup.mem_sup_right (B.inv_mem hb)
    have hcb : c * b ∈ rootElts R := by
      obtain ⟨E, hE, -, hcbE⟩ :=
        hcov _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right hc) (Subgroup.mem_sup_left hb)) hne
      exact ⟨E, hE, hcbE, hne⟩
    exact hb1 (eq_one_of_mul_mem_rootElts hR hA hAB (hcent c hc) hcX
      (Subgroup.mem_sup_right hb) hcb)

theorem sup_eq_of_le [Finite G] (hR : IsRootClass R) {A B C D : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ R) (hC : C ∈ R) (hCD : Opposite C D) (hAB : A ≠ B) (hle : A ⊔ B ≤ C ⊔ D) :
    A ⊔ B = C ⊔ D := by
  have hsqC := hR.mul_self C hC
  obtain ⟨x, hx, rfl⟩ := hCD.exists_conjSub_eq hsqC (le_sup_left.trans hle) (hR.isPGroup hA)
    (hR.card_eq hA hC)
  obtain ⟨y, hy, rfl⟩ := hCD.exists_conjSub_eq hsqC (le_sup_right.trans hle) (hR.isPGroup hB)
    (hR.card_eq hB hC)
  exact hCD.sup_conjSub_eq hsqC hx hy hAB

theorem exists_conjSub_eq_of_le [Finite G] (hR : IsRootClass R) {A C D : Subgroup G}
    (hA : A ∈ R) (hC : C ∈ R) (hCD : Opposite C D) (hle : A ≤ C ⊔ D) :
    ∃ x ∈ C ⊔ D, A = conjSub C x :=
  hCD.exists_conjSub_eq (hR.mul_self C hC) hle (hR.isPGroup hA) (hR.card_eq hA hC)

theorem eq_one_of_commute_of_special (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) {a₀ b : G} (ha₀ : a₀ ∈ A)
    (ha₀1 : a₀ ≠ 1) (hb : b ∈ B) (hc : Commute a₀ b) : b = 1 := by
  by_contra hb1
  have hCR : ⁅A, B⁆ ∈ R := h.1
  have hBC : B ≠ ⁅A, B⁆ := by
    have := h.symm.ne_commutator hR
    rwa [Subgroup.commutator_comm] at this
  have hbB : conjSub B a₀ = B := by
    by_contra hne
    have hmem : b ∈ B ⊓ conjSub B a₀ := by
      refine ⟨hb, ?_⟩
      have := conj_mem_conjSub a₀ hb
      rwa [hc.eq, mul_inv_cancel_right] at this
    rw [inf_eq_bot hR hiso hB (hR.conjSub_mem hB a₀) (Ne.symm hne), Subgroup.mem_bot] at hmem
    exact hb1 hmem
  have hcent : ∀ b' ∈ B, Commute a₀ b' := by
    intro b' hb'
    have hmem : ⁅a₀, b'⁆ ∈ B ⊓ ⁅A, B⁆ := by
      refine ⟨?_, Subgroup.commutator_mem_commutator ha₀ hb'⟩
      rw [commutatorElement_def]
      refine B.mul_mem ?_ (B.inv_mem hb')
      have := conj_mem_conjSub a₀ hb'
      rwa [hbB] at this
    rw [inf_eq_bot hR hiso hB hCR hBC, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  obtain ⟨b₁, hb₁, hne⟩ : ∃ b₁ ∈ B, conjSub A b₁ ≠ A := by
    by_contra! hall
    have hle : ⁅A, B⁆ ≤ A := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
      refine A.mul_mem hx ?_
      have := conj_mem_conjSub y (A.inv_mem hx)
      rwa [hall y hy] at this
    have hbot := inf_eq_bot hR hiso hA hCR (h.ne_commutator hR)
    rw [inf_eq_right.2 hle] at hbot
    exact hR.ne_bot _ hCR hbot
  have hmem : a₀ ∈ A ⊓ conjSub A b₁ := by
    refine ⟨ha₀, ?_⟩
    have := conj_mem_conjSub b₁ ha₀
    rwa [← (hcent b₁ hb₁).eq, mul_inv_cancel_right] at this
  rw [inf_eq_bot hR hiso hA (hR.conjSub_mem hA b₁) (Ne.symm hne), Subgroup.mem_bot] at hmem
  exact ha₀1 hmem

theorem bijOn_commutator [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) {a₀ : G} (ha₀ : a₀ ∈ A)
    (ha₀1 : a₀ ≠ 1) :
    Set.BijOn (fun b => ⁅a₀, b⁆) (B : Set G) ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have hmaps : Set.MapsTo (fun b => ⁅a₀, b⁆) (B : Set G) ((⁅A, B⁆ : Subgroup G) : Set G) :=
    fun b hb => Subgroup.commutator_mem_commutator ha₀ hb
  have hinj : Set.InjOn (fun b => ⁅a₀, b⁆) (B : Set G) := by
    intro b hb b' hb' heq
    have heq' : ⁅a₀, b⁆ = ⁅a₀, b'⁆ := heq
    have e3 : a₀ * (b'⁻¹ * b) * a₀⁻¹ = b'⁻¹ * b := by
      calc a₀ * (b'⁻¹ * b) * a₀⁻¹ = (a₀ * b' * a₀⁻¹)⁻¹ * (a₀ * b * a₀⁻¹) := by group
        _ = (⁅a₀, b'⁆ * b')⁻¹ * (⁅a₀, b⁆ * b) := by
          rw [conj_eq_commutator_mul, conj_eq_commutator_mul]
        _ = b'⁻¹ * b := by rw [heq']; group
    have key : Commute a₀ (b'⁻¹ * b) := mul_inv_eq_iff_eq_mul.1 e3
    have := eq_one_of_commute_of_special hR hiso hA hB h ha₀ ha₀1
      (B.mul_mem (B.inv_mem hb') hb) key
    rw [inv_mul_eq_one] at this
    exact this.symm
  refine ⟨hmaps, hinj, ?_⟩
  have himg : (fun b => ⁅a₀, b⁆) '' (B : Set G) = ((⁅A, B⁆ : Subgroup G) : Set G) := by
    refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.2 hmaps) ?_ (Set.toFinite _)
    rw [hinj.ncard_image, ← Nat.card_coe_set_eq, ← Nat.card_coe_set_eq]
    exact (hR.card_eq h.1 hB).le
  intro c hc
  rw [← himg] at hc
  exact hc

theorem bijOn_commutator_left [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) {b₀ : G} (hb₀ : b₀ ∈ B)
    (hb₀1 : b₀ ≠ 1) :
    Set.BijOn (fun a => ⁅a, b₀⁆) (A : Set G) ((⁅A, B⁆ : Subgroup G) : Set G) := by
  have h1 := bijOn_commutator hR hiso hB hA h.symm hb₀ hb₀1
  rw [Subgroup.commutator_comm] at h1
  refine h1.congr fun a ha => ?_
  have hmem : ⁅a, b₀⁆ ∈ ⁅A, B⁆ := Subgroup.commutator_mem_commutator ha hb₀
  change ⁅b₀, a⁆ = ⁅a, b₀⁆
  rw [← commutatorElement_inv, hR.inv_eq h.1 hmem]

theorem mem_lambdaSet_commutator_left [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) :
    A ∈ lambdaSet R ⁅A, B⁆ := by
  refine ⟨⟨hA, h.ne_commutator hR, h.2.1⟩, ?_⟩
  intro x hx hx1
  have hle : ⁅A, B⁆ ≤ Subgroup.normalizer (A : Set G) := fun c hc =>
    RankOne.map_conj_eq_self_iff.1 (conjSub_of_forall_commute fun a ha => h.2.1 c hc a ha)
  have hxmem : x ∈ ((⁅A, B⁆ : Subgroup G) : Set G) * (A : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle]
    exact hx
  obtain ⟨c, hc, a, ha, rfl⟩ := hxmem
  by_cases ha1 : a = 1
  · subst ha1
    exact ⟨⁅A, B⁆, h.1, le_sup_left, by simpa using hc⟩
  · obtain ⟨b, hb, hbc⟩ := (bijOn_commutator hR hiso hA hB h ha ha1).surjOn
      (Subgroup.inv_mem _ hc)
    refine ⟨conjSub A b, hR.conjSub_mem hA b, conjSub_le_commutator_sup hb, ?_⟩
    have hba : b * a * b⁻¹ = c * a := by
      have hbc' : ⁅a, b⁆ = c⁻¹ := hbc
      rw [conj_eq_commutator_mul, ← commutatorElement_inv, hbc', inv_inv]
    show c * a ∈ conjSub A b
    rw [← hba]
    exact conj_mem_conjSub b ha

theorem mem_lambdaSet_commutator [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R)
    {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (h : Special R A B) :
    A ∈ lambdaSet R ⁅A, B⁆ ∧ B ∈ lambdaSet R ⁅A, B⁆ := by
  refine ⟨mem_lambdaSet_commutator_left hR hiso hA hB h, ?_⟩
  have := mem_lambdaSet_commutator_left hR hiso hB hA h.symm
  rwa [Subgroup.commutator_comm] at this

end CFSG.Timmesfeld.ARS

