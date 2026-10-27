module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPairExtension

public section

namespace CFSG.Monster.B.Classical.UnitaryPanels

open Module CFSG.LocalAnalysis.ComponentInitial CFSG.LinearGroups CFSG.ClassicalGroups.UnitaryFlag
open scoped Pointwise

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

section LinearAlgebra

theorem exists_eq_span_singleton_of_finrank_eq_one {W : Submodule K V} (hW : finrank K W = 1) :
    ∃ v : V, v ≠ 0 ∧ W = Submodule.span K {v} := by
  obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hW
  refine ⟨v, fun h => hv0 (Subtype.ext h), le_antisymm (fun w hw => ?_) ?_⟩
  · obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
    exact Submodule.mem_span_singleton.2 ⟨c, congrArg Subtype.val hc⟩
  · exact (Submodule.span_singleton_le_iff_mem _ _).2 v.2

variable [FiniteDimensional K V]

theorem sup_span_singleton_eq {X Y : Submodule K V} (hXY : X ≤ Y)
    (hd : finrank K Y = finrank K X + 1) {m : V} (hmY : m ∈ Y) (hmX : m ∉ X) :
    X ⊔ Submodule.span K {m} = Y := by
  have hle : X ⊔ Submodule.span K {m} ≤ Y :=
    sup_le hXY ((Submodule.span_singleton_le_iff_mem _ _).2 hmY)
  have hlt : X < X ⊔ Submodule.span K {m} := lt_of_le_of_ne le_sup_left fun h =>
    hmX (h ▸ Submodule.mem_sup_right (Submodule.mem_span_singleton_self m))
  have := Submodule.finrank_lt_finrank_of_lt hlt
  exact Submodule.eq_of_le_of_finrank_le hle (by omega)

theorem map_span_eq_of_forall_mem (g : LinearMap.GeneralLinearGroup K V) {S : Set V}
    (h : ∀ s ∈ S, (g : V →ₗ[K] V) s ∈ Submodule.span K S) :
    (Submodule.span K S).map (g : V →ₗ[K] V) = Submodule.span K S :=
  Submodule.eq_of_le_of_finrank_eq ((Submodule.map_span_le _ _ _).2 h)
    (LinearEquiv.finrank_map_eq (LinearMap.GeneralLinearGroup.generalLinearEquiv K V g) _)

end LinearAlgebra

section Sesq

variable {σ : K →+* K} {B : V →ₛₗ[σ] V →ₗ[K] K}

theorem sesq_eq_zero_of_mem_span {S : Set V} {y : V} (h : ∀ s ∈ S, B s y = 0) {x : V}
    (hx : x ∈ Submodule.span K S) : B x y = 0 := by
  induction hx using Submodule.span_induction with
  | mem z hz => exact h z hz
  | zero => simp
  | add z z' _ _ hz hz' => rw [map_add, LinearMap.add_apply, hz, hz', add_zero]
  | smul a z _ hz => rw [map_smulₛₗ, LinearMap.smul_apply, hz, smul_zero]

theorem sesq_eq_zero_of_mem_span_of_forall {S : Set V} (h : ∀ s ∈ S, ∀ t ∈ S, B s t = 0)
    {x y : V} (hx : x ∈ Submodule.span K S) (hy : y ∈ Submodule.span K S) : B x y = 0 := by
  refine sesq_eq_zero_of_mem_span (fun s hs => ?_) hx
  induction hy using Submodule.span_induction with
  | mem z hz => exact h s hs z hz
  | zero => simp
  | add z z' _ _ hz hz' => rw [map_add, hz, hz', add_zero]
  | smul a z _ hz => rw [map_smul, hz, smul_zero]

theorem exists_eq_smul_of_commute (hBl : B.SeparatingLeft) {v : V} (hv0 : v ≠ 0) {c : K}
    (hc : c ≠ 0) {z : V →ₗ[K] V}
    (hz : ∀ x, z (hermTransvection B v c x) = hermTransvection B v c (z x)) :
    ∃ α : K, z v = α • v := by
  obtain ⟨x, hx⟩ : ∃ x, B v x ≠ 0 := by
    by_contra! h0
    exact hv0 (hBl v h0)
  have := hz x
  rw [hermTransvection_apply, hermTransvection_apply, map_add, map_smul] at this
  have h2 : (c * B v x) • z v = (c * B v (z x)) • v := add_left_cancel this
  refine ⟨(c * B v x)⁻¹ * (c * B v (z x)), ?_⟩
  rw [mul_smul, ← h2, smul_smul, inv_mul_cancel₀ (mul_ne_zero hc hx), one_smul]

end Sesq

section Frame

variable {p f : ℕ} (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}

include h in
theorem frame_fe (hB : B.IsSymm) {e f : Fin 3 → V}
    (hef : ∀ i j, B (e i) (f j) = if i = j then 1 else 0) (i j : Fin 3) :
    B (f i) (e j) = if i = j then 1 else 0 := by
  rw [← hB.eq (e j) (f i), hef j i]
  by_cases hij : i = j
  · subst hij
    simp
  · simp [hij, Ne.symm hij]

theorem exists_frame_of_flag [FiniteDimensional K V] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {R H T : Submodule K V} (hRH : R < H) (hHT : H < T) (hR : finrank K R = 1)
    (hH : finrank K H = 2) (hT : finrank K T = 3) (hTi : ∀ x ∈ T, ∀ y ∈ T, B x y = 0) :
    ∃ e f : Fin 3 → V, (∀ i j, B (e i) (e j) = 0) ∧ (∀ i j, B (f i) (f j) = 0) ∧
      (∀ i j, B (e i) (f j) = if i = j then 1 else 0) ∧ R = Submodule.span K {e 0} ∧
      H = Submodule.span K {e 0, e 1} ∧ T = Submodule.span K {e 0, e 1, e 2} := by
  have hsymm : ∀ x y, B y x = h.bar (B x y) := fun x y => (hB.eq x y).symm
  obtain ⟨a₁, ha₁0, hRa⟩ := exists_eq_span_singleton_of_finrank_eq_one hR
  obtain ⟨a₂, ha₂H, ha₂R⟩ := IsConcreteLE.exists_of_lt hRH
  obtain ⟨a₃, ha₃T, ha₃H⟩ := IsConcreteLE.exists_of_lt hHT
  have ha₁R : a₁ ∈ R := hRa ▸ Submodule.mem_span_singleton_self a₁
  have ha₁H : a₁ ∈ H := hRH.le ha₁R
  have ha₁T : a₁ ∈ T := hHT.le ha₁H
  have ha₂T : a₂ ∈ T := hHT.le ha₂H
  have hHa : H = Submodule.span K {a₁, a₂} := by
    rw [Submodule.span_insert, ← hRa]
    exact (sup_span_singleton_eq hRH.le (by rw [hR, hH]) ha₂H ha₂R).symm
  have hli : LinearIndependent K ![a₁, a₂] := by
    rw [LinearIndependent.pair_iff' ha₁0]
    intro c hc
    apply ha₂R
    rw [← hc]
    exact R.smul_mem _ ha₁R
  obtain ⟨b₁, b₂, h11, h12, h21, h22, hb11, hb12, hb21, hb22, -, -, -, hsep, -⟩ :=
    UnitaryHigher.hermitian_isotropic_pair_extension h hB hBl hli (hTi _ ha₁T _ ha₁T)
      (hTi _ ha₁T _ ha₂T) (hTi _ ha₂T _ ha₁T) (hTi _ ha₂T _ ha₂T)
  set S := Submodule.span K {a₁, a₂, b₁, b₂} with hS
  have hb₁a₁ : B b₁ a₁ = 1 := by rw [hsymm, h11, map_one]
  have hb₁a₂ : B b₁ a₂ = 0 := by rw [hsymm, h21, map_zero]
  have hb₂a₁ : B b₂ a₁ = 0 := by rw [hsymm, h12, map_zero]
  have hb₂a₂ : B b₂ a₂ = 1 := by rw [hsymm, h22, map_one]
  obtain ⟨a₃', ha₃'⟩ : ∃ x : V, x = a₃ - B b₁ a₃ • a₁ - B b₂ a₃ • a₂ := ⟨_, rfl⟩
  have ha₃'T : a₃' ∈ T := by
    rw [ha₃']
    exact T.sub_mem (T.sub_mem ha₃T (T.smul_mem _ ha₁T)) (T.smul_mem _ ha₂T)
  have ha₃'S : a₃' ∈ S.orthogonalBilin B := by
    rw [Submodule.mem_orthogonalBilin]
    intro n hn
    refine sesq_eq_zero_of_mem_span (fun s hs => ?_) hn
    rcases hs with rfl | rfl | rfl | rfl
    · exact hTi _ ha₁T _ ha₃'T
    · exact hTi _ ha₂T _ ha₃'T
    · rw [ha₃']
      simp [hb₁a₁, hb₁a₂]
    · rw [ha₃']
      simp [hb₂a₁, hb₂a₂]
  have ha₃'H : a₃' ∉ H := by
    intro hmem
    apply ha₃H
    have : a₃ = a₃' + B b₁ a₃ • a₁ + B b₂ a₃ • a₂ := by
      rw [ha₃']
      abel
    rw [this]
    exact H.add_mem (H.add_mem hmem (H.smul_mem _ ha₁H)) (H.smul_mem _ ha₂H)
  have ha₃'0 : (⟨a₃', ha₃'S⟩ : S.orthogonalBilin B) ≠ 0 := fun h0 =>
    ha₃'H (by rw [show a₃' = 0 from congrArg Subtype.val h0]; exact H.zero_mem)
  obtain ⟨⟨b₃', hab₃, hb₃b₃⟩, -⟩ := hermitian_hyperbolic_splitting h (hB.domRestrict _) hsep
    ha₃'0 (hTi _ ha₃'T _ ha₃'T)
  have hab₃' : B a₃' b₃' = 1 := hab₃
  have hb₃b₃' : B b₃' b₃' = 0 := hb₃b₃
  have hb₃S : ∀ n ∈ S, B n b₃' = 0 := fun n hn => (Submodule.mem_orthogonalBilin.1 b₃'.2) n hn
  have hmemS : a₁ ∈ S ∧ a₂ ∈ S ∧ b₁ ∈ S ∧ b₂ ∈ S :=
    ⟨Submodule.subset_span (by simp), Submodule.subset_span (by simp),
      Submodule.subset_span (by simp), Submodule.subset_span (by simp)⟩
  have ha₁b₃ : B a₁ b₃' = 0 := hb₃S _ hmemS.1
  have ha₂b₃ : B a₂ b₃' = 0 := hb₃S _ hmemS.2.1
  have hb₁b₃ : B b₁ b₃' = 0 := hb₃S _ hmemS.2.2.1
  have hb₂b₃ : B b₂ b₃' = 0 := hb₃S _ hmemS.2.2.2
  have hb₃b₁ : B b₃' b₁ = 0 := by rw [hsymm, hb₁b₃, map_zero]
  have hb₃b₂ : B b₃' b₂ = 0 := by rw [hsymm, hb₂b₃, map_zero]
  have ha₃b₁ : B a₃' b₁ = 0 := by
    rw [hsymm, (Submodule.mem_orthogonalBilin.1 ha₃'S) _ hmemS.2.2.1, map_zero]
  have ha₃b₂ : B a₃' b₂ = 0 := by
    rw [hsymm, (Submodule.mem_orthogonalBilin.1 ha₃'S) _ hmemS.2.2.2, map_zero]
  have heT : ∀ i, ![a₁, a₂, a₃'] i ∈ T := by
    intro i
    fin_cases i
    exacts [ha₁T, ha₂T, ha₃'T]
  refine ⟨![a₁, a₂, a₃'], ![b₁, b₂, (b₃' : V)], fun i j => hTi _ (heT i) _ (heT j),
    fun i j => ?_, fun i j => ?_, hRa, hHa, ?_⟩
  · fin_cases i <;> fin_cases j <;> simp [hb11, hb12, hb21, hb22, hb₁b₃, hb₂b₃, hb₃b₁, hb₃b₂,
      hb₃b₃']
  · fin_cases i <;> fin_cases j <;> simp [h11, h12, h21, h22, ha₁b₃, ha₂b₃, ha₃b₁, ha₃b₂, hab₃']
  · have hTsup := sup_span_singleton_eq hHT.le (by rw [hH, hT]) ha₃'T ha₃'H
    show T = Submodule.span K {a₁, a₂, a₃'}
    rw [← hTsup, hHa, Submodule.span_insert a₁ {a₂, a₃'}, Submodule.span_insert a₂ {a₃'},
      Submodule.span_insert a₁ {a₂}, sup_assoc]

theorem eq_sum_frame [FiniteDimensional K V] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : finrank K V = 6) {e f : Fin 3 → V} (he : ∀ i j, B (e i) (e j) = 0)
    (hf : ∀ i j, B (f i) (f j) = 0) (hef : ∀ i j, B (e i) (f j) = if i = j then 1 else 0)
    (x : V) : x = ∑ i, (B (f i) x • e i + B (e i) x • f i) := by
  have hfe := frame_fe h hB hef
  let v : Fin 3 ⊕ Fin 3 → V := Sum.elim e f
  have hli : LinearIndependent K v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [v, Sum.elim_inl, Sum.elim_inr] at hg
    have hcoef : ∀ j, B (f j) (∑ i, g (.inl i) • e i + ∑ i, g (.inr i) • f i) = g (.inl j) ∧
        B (e j) (∑ i, g (.inl i) • e i + ∑ i, g (.inr i) • f i) = g (.inr j) := by
      intro j
      constructor <;> simp [map_sum, hfe, hf, he, hef]
    rintro (j | j)
    · have := (hcoef j).1
      rwa [hg, map_zero, eq_comm] at this
    · have := (hcoef j).2
      rwa [hg, map_zero, eq_comm] at this
  have htop : Submodule.span K (Set.range v) = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [finrank_span_eq_card hli, hV]
    simp
  set y := x - ∑ i, (B (f i) x • e i + B (e i) x • f i) with hy
  have hvy : ∀ k, B (v k) y = 0 := by
    rintro (j | j)
    · simp [v, hy, map_sum, he, hef]
    · simp [v, hy, map_sum, hfe, hf]
  have hzy : ∀ z, B z y = 0 := fun z =>
    sesq_eq_zero_of_mem_span (S := Set.range v) (by rintro _ ⟨k, rfl⟩; exact hvy k)
      (htop ▸ Submodule.mem_top)
  have hy0 : y = 0 := hBl y fun z => by rw [← hB.eq z y, hzy, map_zero]
  rw [hy, sub_eq_zero] at hy0
  exact hy0

end Frame

section Center

variable {p f : ℕ} (h : UnitaryFieldData p f K) {B : V →ₛₗ[h.bar] V →ₗ[K] K}

theorem center_eq_smul [FiniteDimensional K V] (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hV : finrank K V = 6) {z : sesqSpecialUnitaryGroup B}
    (hz : z ∈ Subgroup.center (sesqSpecialUnitaryGroup B)) :
    ∃ α : K, α ≠ 0 ∧ ∀ x, ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x = α • x := by
  obtain ⟨zl, hzl⟩ : ∃ zl : V →ₗ[K] V,
      zl = ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) := ⟨_, rfl⟩
  rw [← hzl]
  obtain ⟨r, hr⟩ := h.exists_bar_ne
  have hc0 : h.bar r - r ≠ 0 := sub_ne_zero.2 hr
  have hcE : h.bar r - r ∈ h.traceZero := by
    rw [h.mem_traceZero, UnitaryFieldData.trace, map_sub, h.bar_bar]
    ring
  have heig : ∀ v : V, v ≠ 0 → B v v = 0 → ∃ α : K, zl v = α • v := by
    intro v hv0 hv
    let t : sesqSpecialUnitaryGroup B :=
      ⟨hermTransvectionGL B hv (h.bar r - r), (hermitian_unitary_transvection h hB hv).2.1 _ hcE⟩
    have hcomm := Subgroup.mem_center_iff.1 hz t
    refine exists_eq_smul_of_commute hBl hv0 hc0 fun x => ?_
    have := congrArg (fun g : sesqSpecialUnitaryGroup B =>
      ((g : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) x) hcomm
    simp only [Subgroup.coe_mul, Units.val_mul, Module.End.mul_apply] at this
    rw [hzl]
    exact this.symm
  obtain ⟨w, hw⟩ := exists_hypBasis h hB hBl (r := 3) (ε := 0) (by rw [hV])
  have hdiag : ∀ a : HypIndex 3 0, hypGram 3 0 K a a = 0 := by
    rintro (i | k | i)
    · simp
    · exact k.elim0
    · simp
  choose α hα using fun a => heig (w a) (w.ne_zero a) (by rw [hw, hdiag])
  have hgood : ∀ a b, a ≠ b → hypGram 3 0 K a b = 0 → hypGram 3 0 K b a = 0 → α a = α b := by
    intro a b hab h1 h2
    have hsum0 : w a + w b ≠ 0 := by
      intro h0
      have := congrArg (fun x => w.repr x a) h0
      simp [Ne.symm hab] at this
    have hsumiso : B (w a + w b) (w a + w b) = 0 := by
      simp only [map_add, LinearMap.add_apply, hw, hdiag, h1, h2, add_zero]
    obtain ⟨γ, hγ⟩ := heig _ hsum0 hsumiso
    rw [map_add, hα a, hα b, smul_add] at hγ
    have h1' := congrArg (fun x => w.repr x a) hγ
    have h2' := congrArg (fun x => w.repr x b) hγ
    simp [hab, Ne.symm hab] at h1' h2'
    rw [h1', h2']
  have hall : ∀ a, α a = α (.inl 0) := by
    rintro (i | k | i)
    · fin_cases i
      · rfl
      · exact hgood _ _ (by decide) (by simp) (by simp)
      · exact hgood _ _ (by decide) (by simp) (by simp)
    · exact k.elim0
    · fin_cases i
      · exact (hgood _ (.inl 1) (by decide) (by simp) (by simp)).trans
          (hgood _ _ (by decide) (by simp) (by simp))
      · exact hgood _ _ (by decide) (by simp) (by simp)
      · exact hgood _ _ (by decide) (by simp) (by simp)
  have hzl' : zl = α (.inl 0) • LinearMap.id := w.ext fun a => by
    rw [hα a, hall a]
    rfl
  refine ⟨α (.inl 0), fun h0 => ?_, fun x => by rw [hzl']; rfl⟩
  have h00 := hα (.inl 0)
  rw [h0, zero_smul] at h00
  apply w.ne_zero (.inl 0)
  have hinv := generalLinearGroup_apply_inv_apply (z : LinearMap.GeneralLinearGroup K V)⁻¹
    (w (.inl 0))
  rw [inv_inv, ← hzl, h00, map_zero] at hinv
  exact hinv.symm

theorem center_le_ker_toPermHom [FiniteDimensional K V] (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) (hV : finrank K V = 6) :
    Subgroup.center (sesqSpecialUnitaryGroup B) ≤
      (MulAction.toPermHom (sesqSpecialUnitaryGroup B) (Submodule K V)).ker := by
  intro z hz
  obtain ⟨α, hα0, hα⟩ := center_eq_smul h hB hBl hV hz
  rw [MonoidHom.mem_ker]
  refine Equiv.ext fun W => ?_
  change W.map ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = W
  have : ((z : LinearMap.GeneralLinearGroup K V) : V →ₗ[K] V) = α • LinearMap.id :=
    LinearMap.ext hα
  rw [this, Submodule.map_smul _ _ _ hα0, Submodule.map_id]

end Center

end CFSG.Monster.B.Classical.UnitaryPanels
