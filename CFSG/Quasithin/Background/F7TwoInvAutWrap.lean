module

public import CFSG.Quasithin.Background.F7TwoInvAltAut
public import CFSG.Quasithin.Background.F7TwoInvBridge
public import CFSG.Quasithin.Background.F7TwoInvComm
public import CFSG.Quasithin.Background.F7TwoInvOdd

public section

namespace CFSG.Quasithin.F7Two

variable {L : Type*} [Group L]

@[expose] def invXiAut (φ : MulAut L) : Set L :=
  {x | ¬ IsPGroup 2 ↥(Subgroup.zpowers (φ x * x⁻¹))}

@[expose] def fixSubgroup (φ : MulAut L) : Subgroup L :=
  MonoidHom.eqLocus (φ : L →* L) (MonoidHom.id L)

theorem mem_fixSubgroup_iff {φ : MulAut L} {x : L} : x ∈ fixSubgroup φ ↔ φ x = x := Iff.rfl

theorem invAutGen_iff_closure_invXiAut (φ : MulAut L) :
    InvAutGen L φ ↔ Subgroup.closure (invXiAut φ) = ⊤ := Iff.rfl

theorem mem_invXiAut_iff {φ : MulAut L} {x : L} :
    x ∈ invXiAut φ ↔ ∀ n : ℕ, (φ x * x⁻¹) ^ 2 ^ n ≠ 1 := by
  show ¬ IsPGroup 2 ↥(Subgroup.zpowers (φ x * x⁻¹)) ↔ _
  rw [isPGroup_two_zpowers_iff, not_exists]

theorem InvAutGen.conj_iff (ψ φ : MulAut L) : InvAutGen L φ ↔ InvAutGen L (ψ * φ * ψ⁻¹) := by
  have key : ∀ ψ φ : MulAut L, InvAutGen L φ → InvAutGen L (ψ * φ * ψ⁻¹) := fun ψ φ h => by
    have h1 := InvAutGen.congr ψ h
    have e : (ψ.symm.trans φ).trans ψ = ψ * φ * ψ⁻¹ := MulEquiv.ext fun _ => rfl
    rwa [e] at h1
  refine ⟨key ψ φ, fun h => ?_⟩
  have h1 := key ψ⁻¹ _ h
  rwa [show ψ⁻¹ * (ψ * φ * ψ⁻¹) * ψ⁻¹⁻¹ = φ by group] at h1

theorem mul_mem_invXiAut_of_fixed {φ : MulAut L} {c x : L} (hc : φ c = c)
    (hx : x ∈ invXiAut φ) : c * x ∈ invXiAut φ := by
  rw [mem_invXiAut_iff] at hx ⊢
  refine fun n hn => hx n ?_
  have e : φ (c * x) * (c * x)⁻¹ = c * (φ x * x⁻¹) * c⁻¹ := by rw [map_mul, hc]; group
  rw [e, conj_pow, mul_inv_eq_one, mul_eq_left] at hn
  exact hn

theorem inv_mem_invXiAut {φ : MulAut L} {x : L} (hx : x ∈ invXiAut φ) : x⁻¹ ∈ invXiAut φ := by
  rw [mem_invXiAut_iff] at hx ⊢
  refine fun n hn => hx n ?_
  have e : φ x⁻¹ * x⁻¹⁻¹ = x⁻¹ * (φ x * x⁻¹)⁻¹ * x⁻¹⁻¹ := by rw [map_inv]; group
  rwa [e, conj_pow, conj_eq_one_iff, inv_pow, inv_eq_one] at hn

theorem map_mem_invXiAut {φ : MulAut L} (hφ2 : φ * φ = 1) {x : L} (hx : x ∈ invXiAut φ) :
    φ x ∈ invXiAut φ := by
  have h2 : φ (φ x) = x := by simpa using MulEquiv.congr_fun hφ2 x
  rw [mem_invXiAut_iff] at hx ⊢
  refine fun n hn => hx n ?_
  rw [h2, show x * (φ x)⁻¹ = (φ x * x⁻¹)⁻¹ by group, inv_pow, inv_eq_one] at hn
  exact hn

theorem fixSubgroup_le_closure_invXiAut {φ : MulAut L} (hne : (invXiAut φ).Nonempty) :
    fixSubgroup φ ≤ Subgroup.closure (invXiAut φ) := by
  obtain ⟨x, hx⟩ := hne
  intro c hc
  have h := Subgroup.mul_mem _
    (Subgroup.subset_closure (mul_mem_invXiAut_of_fixed (mem_fixSubgroup_iff.mp hc) hx))
    (Subgroup.subset_closure (inv_mem_invXiAut hx))
  simpa using h

theorem center_eq_bot_of_isSimpleGroup (hs : IsSimpleGroup L) (hnonab : ∃ x y : L, x * y ≠ y * x) :
    Subgroup.center L = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h1 | h1
  · exact h1
  · exfalso
    obtain ⟨x, y, hxy⟩ := hnonab
    exact hxy ((Subgroup.mem_center_iff.mp (h1 ▸ Subgroup.mem_top y)) x)

theorem innData (hs : IsSimpleGroup L) (hnonab : ∃ x y : L, x * y ≠ y * x) {φ : MulAut L}
    (hφ1 : φ ≠ 1) :
    IsSimpleGroup ↥(MulAut.conj : L →* MulAut L).range ∧
      (∃ x y : ↥(MulAut.conj : L →* MulAut L).range, x * y ≠ y * x) ∧
      (∀ x ∈ (MulAut.conj : L →* MulAut L).range,
        φ * x * φ⁻¹ ∈ (MulAut.conj : L →* MulAut L).range) ∧
      (∃ x ∈ (MulAut.conj : L →* MulAut L).range, φ * x ≠ x * φ) := by
  have := hs
  have hinj := conj_injective_of_center_eq_bot (center_eq_bot_of_isSimpleGroup hs hnonab)
  let eI : L ≃* ↥(MulAut.conj : L →* MulAut L).range := MonoidHom.ofInjective hinj
  refine ⟨eI.symm.isSimpleGroup, ?_, ?_, ?_⟩
  · obtain ⟨x, y, hxy⟩ := hnonab
    refine ⟨eI x, eI y, fun h1 => hxy ?_⟩
    simpa using congrArg eI.symm h1
  · rintro _ ⟨y, rfl⟩
    exact ⟨φ y, (mulAut_mul_conj_mul_inv φ y).symm⟩
  · by_contra hcon
    push Not at hcon
    apply hφ1
    refine MulEquiv.ext fun y => ?_
    have h1 := hcon (MulAut.conj y) ⟨y, rfl⟩
    refine hinj ?_
    rw [← mulAut_mul_conj_mul_inv, h1, mul_inv_cancel_right]
    rfl

theorem invAutGen_of_invGen_inn (hZ : Subgroup.center L = ⊥) {φ : MulAut L}
    (h : InvGen (MulAut.conj : L →* MulAut L).range φ) : InvAutGen L φ :=
  (invAutGen_iff_invGen_range (conj_injective_of_center_eq_bot hZ) (a := φ) (φ := φ)
    fun x => (mulAut_mul_conj_mul_inv φ x).symm).2 h

theorem invXiAut_nonempty [Finite L] (hs : IsSimpleGroup L) (hnonab : ∃ x y : L, x * y ≠ y * x)
    {φ : MulAut L} (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1) : (invXiAut φ).Nonempty := by
  have hinj := conj_injective_of_center_eq_bot (center_eq_bot_of_isSimpleGroup hs hnonab)
  obtain ⟨hsI, hnI, hφN, hφc⟩ := innData hs hnonab hφ1
  obtain ⟨_, ⟨x, rfl⟩, hy⟩ := invXi_nonempty hsI hnI hφ2 hφN hφc
  refine ⟨x, fun hP => hy ?_⟩
  have e : φ * MulAut.conj x * φ⁻¹ * (MulAut.conj x)⁻¹ = MulAut.conj (φ x * x⁻¹) := by
    rw [mulAut_mul_conj_mul_inv, map_mul, map_inv]
  rw [e, isPGroup_zpowers_map_iff _ hinj]
  exact hP

theorem invAutGen_of_odd_iSup [Finite L] (hs : IsSimpleGroup L)
    (hnonab : ∃ x y : L, x * y ≠ y * x) {φ : MulAut L} (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    {ι : Sort*} {U : ι → Subgroup L} (hodd : ∀ i, Odd (Nat.card (U i)))
    (hinv : ∀ i, ∀ x ∈ U i, φ x ∈ U i) (hsup : ⨆ i, U i = ⊤) : InvAutGen L φ := by
  have hZ := center_eq_bot_of_isSimpleGroup hs hnonab
  have hinj := conj_injective_of_center_eq_bot hZ
  obtain ⟨hsI, hnI, hφN, hφc⟩ := innData hs hnonab hφ1
  refine invAutGen_of_invGen_inn hZ ?_
  refine invGen_of_odd_iSup hsI hnI hφ2 hφN hφc
    (U := fun i => (U i).map (MulAut.conj : L →* MulAut L)) (fun i => Subgroup.map_le_range _ _)
    (fun i => ?_) (fun i x hx => ?_) ?_
  · rw [Subgroup.card_map_of_injective hinj]
    exact hodd i
  · obtain ⟨y, hy, rfl⟩ := hx
    exact ⟨φ y, hinv i y hy, (mulAut_mul_conj_mul_inv φ y).symm⟩
  · rw [← Subgroup.map_iSup, hsup, ← MonoidHom.range_eq_map]

theorem invAutGen_of_odd_sup [Finite L] (hs : IsSimpleGroup L)
    (hnonab : ∃ x y : L, x * y ≠ y * x) {φ : MulAut L} (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    {U₁ U₂ : Subgroup L} (hodd₁ : Odd (Nat.card U₁)) (hodd₂ : Odd (Nat.card U₂))
    (hinv₁ : ∀ x ∈ U₁, φ x ∈ U₁) (hinv₂ : ∀ x ∈ U₂, φ x ∈ U₂) (hsup : U₁ ⊔ U₂ = ⊤) :
    InvAutGen L φ := by
  refine invAutGen_of_odd_iSup hs hnonab hφ2 hφ1 (U := fun b : Bool => bif b then U₁ else U₂)
    (fun b => ?_) (fun b => ?_) ?_
  · cases b
    exacts [hodd₂, hodd₁]
  · cases b
    exacts [hinv₂, hinv₁]
  · rw [iSup_bool_eq]
    exact hsup

theorem invAutGen_of_maximal_fix [Finite L] (hs : IsSimpleGroup L)
    (hnonab : ∃ x y : L, x * y ≠ y * x) {φ : MulAut L} (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (hmax : ∀ K : Subgroup L, fixSubgroup φ ≤ K → (∀ x ∈ K, φ x ∈ K) →
      K = fixSubgroup φ ∨ K = ⊤) : InvAutGen L φ := by
  have hne := invXiAut_nonempty hs hnonab hφ2 hφ1
  have hinvar : ∀ x ∈ Subgroup.closure (invXiAut φ), φ x ∈ Subgroup.closure (invXiAut φ) := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact Subgroup.subset_closure (map_mem_invXiAut hφ2 hx)
    | one => rw [map_one]; exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  rcases hmax _ (fixSubgroup_le_closure_invXiAut hne) hinvar with h | h
  · exfalso
    obtain ⟨x, hx⟩ := hne
    have hxK : x ∈ fixSubgroup φ := h ▸ Subgroup.subset_closure hx
    exact mem_invXiAut_iff.mp hx 0 (by rw [mem_fixSubgroup_iff.mp hxK, mul_inv_cancel, one_pow])
  · exact h

theorem invAutGen_of_isCoatom_fix [Finite L] (hs : IsSimpleGroup L)
    (hnonab : ∃ x y : L, x * y ≠ y * x) {φ : MulAut L} (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (hco : IsCoatom (fixSubgroup φ)) : InvAutGen L φ := by
  refine invAutGen_of_maximal_fix hs hnonab hφ2 hφ1 fun K hK _ => ?_
  by_cases h : K = fixSubgroup φ
  · exact Or.inl h
  · exact Or.inr (hco.2 K (lt_of_le_of_ne hK (Ne.symm h)))

theorem invAutGen_of_forall_coatom [Finite L] (hs : IsSimpleGroup L)
    (hnonab : ∃ x y : L, x * y ≠ y * x) {φ : MulAut L} (hφ2 : φ * φ = 1) (hφ1 : φ ≠ 1)
    (h : ∀ M : Subgroup L, IsCoatom M → fixSubgroup φ ≤ M → ∃ x ∈ invXiAut φ, x ∉ M) :
    InvAutGen L φ := by
  have hne := invXiAut_nonempty hs hnonab hφ2 hφ1
  rcases eq_top_or_exists_le_coatom (Subgroup.closure (invXiAut φ)) with htop | ⟨M, hM, hKM⟩
  · exact htop
  · obtain ⟨x, hx, hxM⟩ := h M hM ((fixSubgroup_le_closure_invXiAut hne).trans hKM)
    exact absurd (hKM (Subgroup.subset_closure hx)) hxM

theorem invAutGen_conj_of_abelian_two_subgroups [Finite L] (hs : IsSimpleGroup L)
    (hnonab : ∃ x y : L, x * y ≠ y * x) {g : L} (hg2 : g * g = 1) (hg1 : g ≠ 1)
    (hab : ∀ P : Subgroup L, IsPGroup 2 ↥P → ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) :
    InvAutGen L (MulAut.conj g) := by
  have := hs
  have hZ := center_eq_bot_of_isSimpleGroup hs hnonab
  rw [invAutGen_iff_invGen_range (f := MonoidHom.id L) Function.injective_id (a := g)
    (φ := MulAut.conj g) (fun x => by simp [MulAut.conj_apply]),
    MonoidHom.range_eq_top.mpr Function.surjective_id]
  have hac : ∃ x ∈ (⊤ : Subgroup L), g * x ≠ x * g := by
    by_contra hcon
    push Not at hcon
    apply hg1
    have : g ∈ Subgroup.center L :=
      Subgroup.mem_center_iff.mpr fun x => (hcon x (Subgroup.mem_top x)).symm
    rwa [hZ, Subgroup.mem_bot] at this
  have hnonab' : ∃ x y : ↥(⊤ : Subgroup L), x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := hnonab
    exact ⟨⟨x, Subgroup.mem_top x⟩, ⟨y, Subgroup.mem_top y⟩, fun h => hxy (congrArg Subtype.val h)⟩
  exact invGen_of_abelian_two_subgroups_of_mem Subgroup.topEquiv.isSimpleGroup hnonab' hg2
    (Subgroup.mem_top g) (fun x _ => Subgroup.mem_top _) hac fun P _ hP => hab P hP

end CFSG.Quasithin.F7Two
