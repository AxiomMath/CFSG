module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Curtis
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Thm14_5.SmallSp6Rank1
public import CFSG.Quasithin.Background.SmithParabolic
import all CFSG.LieType.Universal.SymplecticRoots

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.LieType.Universal.Symplectic CFSG.LieType.Universal.Symplectic.SpExtras
  CFSG.LieType.Steinberg CFSG.LieType.RootSystem CFSG.Quasithin.SmithCurtis CFSG.Open
  TauCeti.GLSymplecticFin Module

section Generic

variable {G : Type*} [Group G] {B : Type*} {M : CoxeterMatrix B} {W : Type*} [Group W]
  {cs : CoxeterSystem M W} {p : ℕ} (D : CurtisDatum G cs p)

theorem curtisDatum_Y_normUs (s : B) {y : G} (hy : y ∈ D.Y s) {v : G} (hv : v ∈ D.Us s) :
    y * v * y⁻¹ ∈ D.Us s := by
  have hx := D.n_inv_conjY s hy
  have e : y * v * y⁻¹ = D.n s * (((D.n s)⁻¹ * y * D.n s) *
      ((D.n s)⁻¹ * v * D.n s) * ((D.n s)⁻¹ * y * D.n s)⁻¹) * (D.n s)⁻¹ := by group
  rw [e]
  exact D.n_normUs s _ (D.X_normUs s _ hx _ (D.n_normUs' s v hv))

theorem conj_mem_of_sup {A A' N : Subgroup G} (hA : ∀ a ∈ A, ∀ x ∈ N, a * x * a⁻¹ ∈ N)
    (hA' : ∀ a ∈ A', ∀ x ∈ N, a * x * a⁻¹ ∈ N) {m : G} (hm : m ∈ A ⊔ A') {x : G}
    (hx : x ∈ N) : m * x * m⁻¹ ∈ N := by
  have key : ∀ m ∈ A ⊔ A', ∀ x ∈ N, m * x * m⁻¹ ∈ N ∧ m⁻¹ * x * m ∈ N := by
    intro m hm
    rw [Subgroup.sup_eq_closure] at hm
    induction hm using Subgroup.closure_induction with
    | mem m hm =>
      rcases hm with hm | hm
      · exact fun x hx => ⟨hA m hm x hx, by simpa using hA m⁻¹ (inv_mem hm) x hx⟩
      · exact fun x hx => ⟨hA' m hm x hx, by simpa using hA' m⁻¹ (inv_mem hm) x hx⟩
    | one => exact fun x hx => by simpa using hx
    | mul m m' _ _ hm hm' =>
      intro x hx
      refine ⟨?_, ?_⟩
      · have := (hm _ (hm' x hx).1).1
        simpa [mul_assoc] using this
      · have := (hm' _ (hm x hx).2).2
        simpa [mul_assoc] using this
    | inv m _ hm => exact fun x hx => ⟨by simpa using (hm x hx).2, by simpa using (hm x hx).1⟩
  exact (key m hm x hx).1

variable {k V : Type*} [Field k] [AddCommGroup V] [Module k V]

theorem fixSub_Us_eq_bot_or_eq [Finite G] [Finite W] [Fact p.Prime] [CharP k p]
    (hsplit : SplitOver k D.H) {ρ : Representation k G V} (hρ : IsSimpleRep ρ) (s : B)
    {T : Submodule k V} (hT : T ≤ fixSub ρ (D.Us s))
    (hTP : ∀ m ∈ D.X s ⊔ D.Y s, ∀ v ∈ T, ρ m v ∈ T) : T = ⊥ ∨ T = fixSub ρ (D.Us s) := by
  have hsmith := D.eq_bot_or_fixSub_le hsplit hρ (N := D.Us s) (N' := D.Q s)
    (P := D.X s ⊔ D.Y s)
    (fun m hm x hx => conj_mem_of_sup (D.X_normUs s) (fun y hy v hv =>
      curtisDatum_Y_normUs D s hy hv) hm hx)
    (fun m hm x hx => conj_mem_of_sup (D.X_normQ s) (D.Y_normQ s) hm hx)
    (D.Q_le s)
    (fun u hu => by
      obtain ⟨x, hx, v, hv, rfl⟩ := D.U_eq s u hu
      exact mul_mem (Subgroup.mem_sup_right ⟨D.X_le s hx, Subgroup.mem_sup_left hx⟩)
        (Subgroup.mem_sup_left hv))
    (fun l hl => by
      have hle : D.Y s ⊔ D.Q s ≤ D.Q s ⊔ (D.X s ⊔ D.Y s) :=
        sup_le (le_sup_of_le_right le_sup_right) le_sup_left
      exact hle (D.L_le s hl))
    hT hTP
  rcases hsmith with h | h
  · exact Or.inl h
  · exact Or.inr (le_antisymm hT h)

end Generic

variable {n : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def simpleIdx (i : Fin n) : RootSubgroupIndex n :=
  if h : i.val + 1 < n then .difference i ⟨i.val + 1, h⟩ (ne_succ' h) else .positiveLong i

theorem stdVec_simpleIdx (i : Fin n) : stdVec (simpleIdx i) = toStd n (Pi.single i 1) := by
  unfold simpleIdx
  split_ifs with h
  · rw [toStd_single_of_lt' h]
    rfl
  · rw [toStd_single_of_not_lt' h]
    rfl

theorem mem_X_iff (i : Fin n) {x : StatedSp n K} :
    x ∈ (spCurtisDatum n K).X i ↔ ∃ c : K, x = elt (simpleIdx i) c :=
  mem_rootGroup_iff (stdVec_simpleIdx i)

omit [Finite K] [CharP K 2] in
theorem corootVec_mul (i : Fin n) (a b : Kˣ) :
    corootVec n K i (a * b) = corootVec n K i a * corootVec n K i b := by
  funext j
  simp only [corootVec, Pi.mul_apply]
  split_ifs <;> simp [mul_comm]

@[expose] noncomputable def corootSp (i : Fin n) : Kˣ →* StatedSp n K where
  toFun a := diagHom n K (corootVec n K i a)
  map_one' := by
    rw [show corootVec n K i 1 = 1 from funext fun j => by simp [corootVec], map_one]
  map_mul' a b := by rw [corootVec_mul, map_mul]

omit [Finite K] [CharP K 2] in
theorem corootSp_apply (i : Fin n) (a : Kˣ) :
    corootSp i a = diagHom n K (corootVec n K i a) := rfl

theorem corootSp_mem_H (i : Fin n) (a : Kˣ) : corootSp i a ∈ (spCurtisDatum n K).H :=
  diagHom_corootVec_mem_H i a

omit [Finite K] [CharP K 2] in
theorem corootSp_conj_elt (i : Fin n) (a : Kˣ) (c : K) :
    corootSp i a * elt (simpleIdx i) c * (corootSp i a)⁻¹ =
      elt (simpleIdx i) ((a : K) ^ 2 * c) := by
  rw [corootSp_apply, diagHom_conj_elt, ← character_eq_prod]
  congr 2
  unfold simpleIdx
  split_ifs with h
  · rw [RootSubgroupIndex.character_difference]
    simp [corootVec, sq, Fin.ext_iff]
  · rw [RootSubgroupIndex.character_positiveLong]
    simp [corootVec, sq]

omit [Finite K] [CharP K 2] in
theorem weylRep_conj_corootSp (i : Fin n) (a : Kˣ) :
    weylRep n K i * corootSp i a * (weylRep n K i)⁻¹ = corootSp i a⁻¹ := by
  rw [corootSp_apply, corootSp_apply]
  by_cases h : i.val + 1 < n
  · have hw : weylRep n K i = sw (ne_succ' h) := by
      rw [weylRep_eq, weylElt_of_lt n K h]
      rfl
    rw [hw, sw_conj_diagHom]
    congr 1
    funext b
    simp only [Function.comp_apply, corootVec]
    by_cases hb : b = i
    · subst hb
      simp [Equiv.swap_apply_left, Fin.ext_iff]
    · by_cases hb' : b.val = i.val + 1
      · have hb'' : b = ⟨i.val + 1, h⟩ := Fin.ext hb'
        subst hb''
        simp [Equiv.swap_apply_right, Fin.ext_iff]
      · rw [Equiv.swap_apply_of_ne_of_ne hb (fun e => hb' (by rw [e]))]
        simp [hb, hb']
  · have hw : weylRep n K i = lw i := by
      rw [weylRep_eq, weylElt_of_not_lt n K h]
      rfl
    rw [hw, lw_conj_diagHom]
    congr 1
    funext b
    by_cases hb : b = i
    · subst hb
      simp [corootVec, Function.update]
    · have hb' : ¬ b.val = i.val + 1 := by have := b.isLt; omega
      simp [corootVec, Function.update, hb, hb']

omit [Finite K] [CharP K 2] in
theorem exists_weylRep_sq (i : Fin n) :
    ∃ a₀ : Kˣ, weylRep n K i * weylRep n K i = corootSp i a₀ := by
  have h := weylRep_sq_mem n K i
  rw [sq] at h
  obtain ⟨c, hc⟩ := mem_torus_iff.mp h
  exact ⟨c, hc.trans rfl⟩

theorem corootSp_mem_closure (i : Fin n) (a : Kˣ) :
    corootSp i a ∈ Subgroup.closure (Set.range (elt (F := K) (simpleIdx i)) ∪
      (fun g => weylRep n K i * g * (weylRep n K i)⁻¹) '' Set.range (elt (simpleIdx i))) := by
  have hle := torus_le_rankOne n K i
  have hmem : corootSp i a ∈ CFSG.LieType.CurtisTits.rankOne (rootGroup n K) i :=
    hle (diagonal_mem_torus n K i a)
  have hX : rootGroup n K (Pi.single i 1) ≤ Subgroup.closure (Set.range (elt (F := K)
      (simpleIdx i)) ∪ (fun g => weylRep n K i * g * (weylRep n K i)⁻¹) ''
        Set.range (elt (simpleIdx i))) := by
    intro x hx
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff (stdVec_simpleIdx i)).mp hx
    exact Subgroup.subset_closure (Or.inl ⟨c, rfl⟩)
  have hY : rootGroup n K (-Pi.single i 1) ≤ Subgroup.closure (Set.range (elt (F := K)
      (simpleIdx i)) ∪ (fun g => weylRep n K i * g * (weylRep n K i)⁻¹) ''
        Set.range (elt (simpleIdx i))) := by
    intro y hy
    have hx := (spCurtisDatum n K).n_inv_conjY i hy
    rw [spCurtisDatum_n] at hx
    obtain ⟨c, hc⟩ := (mem_X_iff i).mp hx
    refine Subgroup.subset_closure (Or.inr ⟨elt (simpleIdx i) c, ⟨c, rfl⟩, ?_⟩)
    rw [← hc]
    group
  exact (sup_le hX hY) hmem

instance finite_spWeyl (n : ℕ) (K : Type) [Field K] :
    Finite (coxeterMatrix (rootDatum n K).isFiniteType).Group :=
  finite_group (rootDatum n K).isFiniteType

variable {k V : Type*} [Field k] [CharP k 2] [AddCommGroup V] [Module k V]

omit [CharP k 2] in
theorem elt_mem_fixSub_Us (ρ : Representation k (StatedSp n K) V) (i : Fin n) (c : K)
    {v : V} (hv : v ∈ fixSub ρ ((spCurtisDatum n K).Us i)) :
    ρ (elt (simpleIdx i) c) v ∈ fixSub ρ ((spCurtisDatum n K).Us i) := by
  have hx : elt (simpleIdx i) c ∈ (spCurtisDatum n K).X i := (mem_X_iff i).mpr ⟨c, rfl⟩
  rw [mem_fixSub] at hv ⊢
  intro u hu
  have hu' := (spCurtisDatum n K).X_normUs i _ (inv_mem hx) u hu
  rw [inv_inv] at hu'
  calc ρ u (ρ (elt (simpleIdx i) c) v)
      = ρ (elt (simpleIdx i) c) (ρ ((elt (simpleIdx i) c)⁻¹ * u * elt (simpleIdx i) c) v) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
    _ = ρ (elt (simpleIdx i) c) v := by rw [hv _ hu']

omit [CharP k 2] in
theorem weylRep_mem_fixSub_Us (ρ : Representation k (StatedSp n K) V) (i : Fin n)
    {v : V} (hv : v ∈ fixSub ρ ((spCurtisDatum n K).Us i)) :
    ρ (weylRep n K i) v ∈ fixSub ρ ((spCurtisDatum n K).Us i) := by
  rw [mem_fixSub] at hv ⊢
  intro u hu
  have hu' := (spCurtisDatum n K).n_normUs' i u hu
  rw [spCurtisDatum_n] at hu'
  calc ρ u (ρ (weylRep n K i) v)
      = ρ (weylRep n K i) (ρ ((weylRep n K i)⁻¹ * u * weylRep n K i) v) := by
        rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
        congr 2
        group
    _ = ρ (weylRep n K i) v := by rw [hv _ hu']

theorem spRankOne_of_finrank_le (hK : 4 ≤ Nat.card K) [FiniteDimensional k V]
    (hsplit : SplitOver k (spCurtisDatum n K).H)
    {ρ : Representation k (StatedSp n K) V} (hρ : IsSimpleRep ρ) {y₀ : V}
    {χ : StatedSp n K → k} {μ : Fin n → k} (ht : (spCurtisDatum n K).IsCurtisType ρ y₀ χ μ)
    (i : Fin n) (hdim : finrank k (fixSub ρ ((spCurtisDatum n K).Us i)) ≤ 2) :
    μ i = 0 ∧ ((∀ a, χ (corootSp i a) = 1) ∨
      ∃ φ : K →+* k, ∀ a : Kˣ, χ (corootSp i a) = φ a) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hK' : 4 ≤ Fintype.card K := by rwa [← Nat.card_eq_fintype_card]
  obtain ⟨hyU, hy0, hχ, hμ⟩ := ht
  set D := spCurtisDatum n K with hD
  set S := fixSub ρ (D.Us i) with hS
  have hyS : y₀ ∈ S := fun u hu => hyU u (D.Us_le i hu)
  have hstab : ∀ T : Submodule k V, (∀ c, ∀ v ∈ T, ρ (elt (simpleIdx i) c) v ∈ T) →
      (∀ v ∈ T, ρ (weylRep n K i) v ∈ T) → ∀ m ∈ D.X i ⊔ D.Y i, ∀ v ∈ T, ρ m v ∈ T := by
    intro T hTx hTn m hm
    have hTn' : ∀ v ∈ T, ρ (weylRep n K i)⁻¹ v ∈ T := fun v hv =>
      mem_of_inv_stable ρ T hTn hv
    rw [Subgroup.sup_eq_closure] at hm
    induction hm using Subgroup.closure_induction with
    | mem m hm =>
      rcases hm with hm | hm
      · obtain ⟨c, rfl⟩ := (mem_X_iff i).mp hm
        exact hTx c
      · have hx := D.n_inv_conjY i hm
        rw [spCurtisDatum_n] at hx
        obtain ⟨c, hc⟩ := (mem_X_iff i).mp hx
        intro v hv
        have e : m = weylRep n K i * elt (simpleIdx i) c * (weylRep n K i)⁻¹ := by
          rw [← hc]; group
        rw [e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply]
        exact hTn _ (hTx c _ (hTn' v hv))
    | one =>
      intro v hv
      rw [map_one, Module.End.one_apply]
      exact hv
    | mul m m' _ _ hm hm' =>
      intro v hv
      rw [map_mul, Module.End.mul_apply]
      exact hm _ (hm' v hv)
    | inv m _ hm =>
      intro v hv
      exact mem_of_inv_stable ρ T hm hv
  obtain ⟨hsum, hchar⟩ := hecke_eq_zero_and_char hK' ρ S hdim (elt (simpleIdx i))
    (elt_add (simpleIdx i)) (corootSp i) (weylRep n K i) (corootSp_conj_elt i)
    (weylRep_conj_corootSp i) (exists_weylRep_sq i) (corootSp_mem_closure i)
    (fun c v hv => elt_mem_fixSub_Us ρ i c hv) (fun v hv => weylRep_mem_fixSub_Us ρ i hv)
    (fun T hTS hTx hTn => fixSub_Us_eq_bot_or_eq D hsplit hρ i hTS (hstab T hTx hTn))
    hyS hy0 (fun c => hyU _ (D.X_le i ((mem_X_iff i).mpr ⟨c, rfl⟩)))
    (fun a => χ (corootSp i a)) (fun a => hχ _ (corootSp_mem_H i a))
  refine ⟨?_, hchar⟩
  have : Fintype (D.X i) := Fintype.ofFinite _
  have hT : D.heckeT ρ i y₀ = 0 := by
    erw [CurtisDatum.heckeT_apply D ρ i y₀]
    have hbij : Function.Bijective (fun c : K => (⟨elt (simpleIdx i) c,
        (mem_X_iff i).mpr ⟨c, rfl⟩⟩ : D.X i)) := by
      refine ⟨fun c d hcd => elt_injective _ (congrArg Subtype.val hcd), fun x => ?_⟩
      obtain ⟨c, hc⟩ := (mem_X_iff i).mp x.2
      exact ⟨c, Subtype.ext hc.symm⟩
    rw [← hbij.sum_comp]
    exact hsum
  have h1 := hμ i
  rw [hT] at h1
  exact (smul_eq_zero.mp h1.symm).resolve_right hy0

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5
