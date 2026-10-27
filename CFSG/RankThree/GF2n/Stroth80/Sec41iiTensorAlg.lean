module

public import CFSG.RankThree.GF2n.Stroth80.Sec41iiLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open scoped commutatorElement

section TensorAlg

variable {E : Type*} [AddCommGroup E] {Γ : Type*} [Group Γ]

@[expose] def actImage (ρ : Γ →* Multiplicative (AddAut E)) (g : Γ) (W : AddSubgroup E) :
    AddSubgroup E :=
  W.map (ρ g).toAdd.toAddMonoidHom

structure TensorSide {K : Type*} [Field K] [Module K E] (ρ : Γ →* Multiplicative (AddAut E))
    (b : E) (X P : Subgroup Γ) (W : Submodule K E) (d : ℕ) : Prop where
  le : P ≤ X
  b_mem : b ∈ W
  b_ne : b ≠ 0
  inv : ∀ x ∈ X, ∀ w ∈ W, (ρ x).toAdd w ∈ W
  lin : ∀ x ∈ X, ∀ (c : K) (v : E), (ρ x).toAdd (c • v) = c • (ρ x).toAdd v
  simple : ∀ T : AddSubgroup E, T ≤ W.toAddSubgroup → (∀ x ∈ X, ∀ v ∈ T, (ρ x).toAdd v ∈ T) →
    T = ⊥ ∨ T = W.toAddSubgroup
  card : Nat.card W = Nat.card K ^ d
  fixed : ∀ v ∈ W, ((∀ p ∈ P, (ρ p).toAdd v = v) ↔ v ∈ Submodule.span K {b})
  nontriv : ∃ x ∈ X, ∃ w ∈ W, (ρ x).toAdd w ≠ w
  perfect : ⁅X, X⁆ = X
  three : 3 ≤ d
  pcard : Nat.card P ≤ Nat.card K ^ (d - 1)
  d3 : d = 3 → ∀ p ∈ P, ∀ w ∈ W, (ρ p).toAdd w - w ∈ Submodule.span K {b}


private theorem toAdd_mul_apply (ρ : Γ →* Multiplicative (AddAut E)) (g h : Γ) (x : E) :
    (ρ (g * h)).toAdd x = (ρ g).toAdd ((ρ h).toAdd x) := by
  rw [map_mul, toAdd_mul, AddAut.add_apply]

private theorem toAdd_one_apply (ρ : Γ →* Multiplicative (AddAut E)) (x : E) :
    (ρ 1).toAdd x = x := by
  rw [map_one, toAdd_one, AddAut.zero_apply]

private theorem toAdd_inv_apply (ρ : Γ →* Multiplicative (AddAut E)) (g : Γ) (x : E) :
    (ρ g⁻¹).toAdd ((ρ g).toAdd x) = x := by
  rw [← toAdd_mul_apply, inv_mul_cancel, toAdd_one_apply]

private theorem apply_toAdd_inv_apply (ρ : Γ →* Multiplicative (AddAut E)) (g : Γ) (x : E) :
    (ρ g).toAdd ((ρ g⁻¹).toAdd x) = x := by
  rw [← toAdd_mul_apply, mul_inv_cancel, toAdd_one_apply]

private theorem toAdd_comm_apply (ρ : Γ →* Multiplicative (AddAut E)) {g h : Γ}
    (hgh : g * h = h * g) (x : E) :
    (ρ g).toAdd ((ρ h).toAdd x) = (ρ h).toAdd ((ρ g).toAdd x) := by
  rw [← toAdd_mul_apply, ← toAdd_mul_apply, hgh]

private theorem commute_inv_of_comm {x y : Γ} (h : x * y = y * x) :
    x * y⁻¹ = y⁻¹ * x := by
  calc x * y⁻¹ = y⁻¹ * (y * x) * y⁻¹ := by simp
    _ = y⁻¹ * (x * y) * y⁻¹ := by rw [h]
    _ = y⁻¹ * x := by simp [mul_assoc]

private theorem comp_subtype_apply (ρ : Γ →* Multiplicative (AddAut E)) (X : Subgroup Γ)
    (s : X) : (ρ.comp X.subtype) s = ρ (s : Γ) := by
  first | rfl | simp

theorem mem_actImage_iff (ρ : Γ →* Multiplicative (AddAut E)) (g : Γ) (W : AddSubgroup E)
    (v : E) : v ∈ actImage ρ g W ↔ (ρ g⁻¹).toAdd v ∈ W := by
  unfold actImage
  rw [AddSubgroup.mem_map]
  constructor
  · rintro ⟨x, hx, hxv⟩
    rw [AddEquiv.coe_toAddMonoidHom] at hxv
    rw [← hxv, toAdd_inv_apply]
    exact hx
  · intro hv
    refine ⟨(ρ g⁻¹).toAdd v, hv, ?_⟩
    rw [AddEquiv.coe_toAddMonoidHom]
    exact apply_toAdd_inv_apply ρ g v

theorem card_actImage (ρ : Γ →* Multiplicative (AddAut E)) (g : Γ) (W : AddSubgroup E) :
    Nat.card (actImage ρ g W) = Nat.card W := by
  have hinj : Function.Injective (ρ g).toAdd.toAddMonoidHom := by
    rw [AddEquiv.coe_toAddMonoidHom]
    exact AddEquiv.injective _
  unfold actImage
  exact AddSubgroup.card_map_of_injective hinj

theorem actImage_mul (ρ : Γ →* Multiplicative (AddAut E)) (g h : Γ) (W : AddSubgroup E) :
    actImage ρ (g * h) W = actImage ρ g (actImage ρ h W) := by
  have hfun : (ρ (g * h)).toAdd.toAddMonoidHom =
      (ρ g).toAdd.toAddMonoidHom.comp (ρ h).toAdd.toAddMonoidHom := by
    ext x
    simp only [AddMonoidHom.comp_apply, AddEquiv.coe_toAddMonoidHom]
    exact toAdd_mul_apply ρ g h x
  unfold actImage
  rw [AddSubgroup.map_map, hfun]

theorem actImage_mono (ρ : Γ →* Multiplicative (AddAut E)) (g : Γ) {W W' : AddSubgroup E}
    (h : W ≤ W') : actImage ρ g W ≤ actImage ρ g W' := by
  unfold actImage
  exact AddSubgroup.map_mono h

theorem actImage_eq_bot_iff (ρ : Γ →* Multiplicative (AddAut E)) (g : Γ) (W : AddSubgroup E) :
    actImage ρ g W = ⊥ ↔ W = ⊥ := by
  have hinj : Function.Injective (ρ g).toAdd.toAddMonoidHom := by
    rw [AddEquiv.coe_toAddMonoidHom]
    exact AddEquiv.injective _
  unfold actImage
  exact AddSubgroup.map_eq_bot_iff_of_injective W hinj

private theorem actImage_one (ρ : Γ →* Multiplicative (AddAut E)) (W : AddSubgroup E) :
    actImage ρ 1 W = W := by
  ext v
  rw [mem_actImage_iff, inv_one, toAdd_one_apply]

private theorem actImage_inv_cancel (ρ : Γ →* Multiplicative (AddAut E)) (y : Γ)
    (T : AddSubgroup E) : actImage ρ y (actImage ρ y⁻¹ T) = T := by
  rw [← actImage_mul, mul_inv_cancel, actImage_one]

private theorem actImage_inv_actImage (ρ : Γ →* Multiplicative (AddAut E)) (y : Γ)
    (W : AddSubgroup E) : actImage ρ y⁻¹ (actImage ρ y W) = W := by
  rw [← actImage_mul, inv_mul_cancel, actImage_one]

theorem actImage_invariant (ρ : Γ →* Multiplicative (AddAut E)) {X : Subgroup Γ} {y : Γ}
    (hy : ∀ x ∈ X, x * y = y * x) {W : AddSubgroup E}
    (hW : ∀ x ∈ X, ∀ v ∈ W, (ρ x).toAdd v ∈ W) :
    ∀ x ∈ X, ∀ v ∈ actImage ρ y W, (ρ x).toAdd v ∈ actImage ρ y W := by
  intro x hx v hv
  rw [mem_actImage_iff] at hv ⊢
  have hc : (ρ y⁻¹).toAdd ((ρ x).toAdd v) = (ρ x).toAdd ((ρ y⁻¹).toAdd v) :=
    toAdd_comm_apply ρ (commute_inv_of_comm (hy x hx)).symm v
  rw [hc]
  exact hW x hx _ hv

theorem actImage_simple (ρ : Γ →* Multiplicative (AddAut E)) {X : Subgroup Γ} {y : Γ}
    (hy : ∀ x ∈ X, x * y = y * x) {W : AddSubgroup E}
    (hW : ∀ x ∈ X, ∀ v ∈ W, (ρ x).toAdd v ∈ W)
    (hs : ∀ T : AddSubgroup E, T ≤ W → (∀ x ∈ X, ∀ v ∈ T, (ρ x).toAdd v ∈ T) →
      T = ⊥ ∨ T = W) :
    ∀ T : AddSubgroup E, T ≤ actImage ρ y W → (∀ x ∈ X, ∀ v ∈ T, (ρ x).toAdd v ∈ T) →
      T = ⊥ ∨ T = actImage ρ y W := by
  intro T hT hTinv
  have hy' : ∀ x ∈ X, x * y⁻¹ = y⁻¹ * x := fun x hx => commute_inv_of_comm (hy x hx)
  have hle : actImage ρ y⁻¹ T ≤ W :=
    calc actImage ρ y⁻¹ T ≤ actImage ρ y⁻¹ (actImage ρ y W) := actImage_mono ρ y⁻¹ hT
      _ = W := actImage_inv_actImage ρ y W
  have hinv : ∀ x ∈ X, ∀ v ∈ actImage ρ y⁻¹ T, (ρ x).toAdd v ∈ actImage ρ y⁻¹ T :=
    actImage_invariant ρ hy' hTinv
  rcases hs (actImage ρ y⁻¹ T) hle hinv with h | h
  · left
    calc T = actImage ρ y (actImage ρ y⁻¹ T) := (actImage_inv_cancel ρ y T).symm
      _ = actImage ρ y ⊥ := by rw [h]
      _ = ⊥ := by unfold actImage; exact AddSubgroup.map_bot _
  · right
    calc T = actImage ρ y (actImage ρ y⁻¹ T) := (actImage_inv_cancel ρ y T).symm
      _ = actImage ρ y W := by rw [h]

theorem fixedIn_actImage (ρ : Γ →* Multiplicative (AddAut E)) (X : Subgroup Γ) {y : Γ}
    (hy : ∀ x ∈ X, x * y = y * x) (S : Subgroup ↥X) (W : AddSubgroup E) :
    fixedIn (ρ.comp X.subtype) S (actImage ρ y W) =
      actImage ρ y (fixedIn (ρ.comp X.subtype) S W) := by
  ext v
  constructor
  · rintro ⟨hv, hfix⟩
    have hv' : (ρ y⁻¹).toAdd v ∈ W := (mem_actImage_iff ρ y W v).1 hv
    refine AddSubgroup.mem_map.2 ⟨(ρ y⁻¹).toAdd v, ⟨hv', fun s hs => ?_⟩, ?_⟩
    · have h := hfix s hs
      rw [comp_subtype_apply] at h
      rw [comp_subtype_apply, toAdd_comm_apply ρ (commute_inv_of_comm (hy (s : Γ) s.2)) v, h]
    · rw [AddEquiv.coe_toAddMonoidHom]
      exact apply_toAdd_inv_apply ρ y v
  · intro h
    obtain ⟨w, hw, hwv⟩ := AddSubgroup.mem_map.1 h
    obtain ⟨hwW, hwfix⟩ := hw
    have hwv' : (ρ y).toAdd w = v := by
      rw [AddEquiv.coe_toAddMonoidHom] at hwv
      exact hwv
    subst hwv'
    refine ⟨(mem_actImage_iff ρ y W _).2 ?_, fun s hs => ?_⟩
    · rw [toAdd_inv_apply]
      exact hwW
    · have h' := hwfix s hs
      rw [comp_subtype_apply] at h'
      rw [comp_subtype_apply, toAdd_comm_apply ρ (hy (s : Γ) s.2) w, h']

theorem commIn_actImage (ρ : Γ →* Multiplicative (AddAut E)) (X : Subgroup Γ) {y : Γ}
    (hy : ∀ x ∈ X, x * y = y * x) (S : Subgroup ↥X) (W : AddSubgroup E) :
    commIn (ρ.comp X.subtype) S (actImage ρ y W) =
      actImage ρ y (commIn (ρ.comp X.subtype) S W) := by
  apply le_antisymm
  · unfold commIn
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨s, hs, w', hw', rfl⟩
    obtain ⟨w, hw, hwe⟩ := AddSubgroup.mem_map.1 hw'
    rw [AddEquiv.coe_toAddMonoidHom] at hwe
    subst hwe
    rw [SetLike.mem_coe]
    refine AddSubgroup.mem_map.2 ⟨((ρ.comp X.subtype) s).toAdd w - w,
      AddSubgroup.subset_closure ⟨s, hs, w, hw, rfl⟩, ?_⟩
    rw [AddEquiv.coe_toAddMonoidHom, map_sub, comp_subtype_apply,
      ← toAdd_comm_apply ρ (hy (s : Γ) s.2) w]
  · refine AddSubgroup.map_le_iff_le_comap.2 ?_
    unfold commIn
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨s, hs, w, hw, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap]
    refine AddSubgroup.subset_closure ⟨s, hs, (ρ y).toAdd w, ?_, ?_⟩
    · rw [mem_actImage_iff, toAdd_inv_apply]
      exact hw
    · rw [AddEquiv.coe_toAddMonoidHom, map_sub, comp_subtype_apply,
        toAdd_comm_apply ρ (hy (s : Γ) s.2) w]



theorem smul_mem_actImage {K : Type*} [Field K] [Module K E] (ρ : Γ →* Multiplicative (AddAut E))
    {y : Γ} (hlin : ∀ (c : K) (v : E), (ρ y).toAdd (c • v) = c • (ρ y).toAdd v)
    (W : Submodule K E) {c : K} {v : E} (hv : v ∈ actImage ρ y W.toAddSubgroup) :
    c • v ∈ actImage ρ y W.toAddSubgroup := by
  unfold actImage at hv ⊢
  obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hv
  exact AddSubgroup.mem_map.2 ⟨c • w, W.smul_mem c ((Submodule.mem_toAddSubgroup W).1 hw), hlin c w⟩

theorem smul_mem_iSup_addSubgroup {K : Type*} [Field K] [Module K E] {ι : Sort*}
    (A : ι → AddSubgroup E) (hA : ∀ i (c : K) (v : E), v ∈ A i → c • v ∈ A i) {c : K} {v : E}
    (hv : v ∈ ⨆ i, A i) : c • v ∈ ⨆ i, A i := by
  refine AddSubgroup.iSup_induction A (C := fun u => c • u ∈ ⨆ i, A i) hv ?_ ?_ ?_
  · intro i u hu
    exact AddSubgroup.mem_iSup_of_mem i (hA i c u hu)
  · show c • (0 : E) ∈ ⨆ i, A i
    rw [smul_zero]
    exact AddSubgroup.zero_mem _
  · intro u u' hu hu'
    show c • (u + u') ∈ ⨆ i, A i
    rw [smul_add]
    exact add_mem hu hu'

theorem card_span_singleton {K : Type*} [Field K] [Finite K] [Module K E] {b : E} (hb : b ≠ 0) :
    Nat.card (Submodule.span K {b}) = Nat.card K := by
  have h := Module.natCard_eq_pow_finrank (K := K) (V := Submodule.span K {b})
  rw [finrank_span_singleton hb, pow_one] at h
  exact h

theorem eq_iSup_actImage_span {K : Type*} [Field K] [Module K E]
    (ρ : Γ →* Multiplicative (AddAut E)) {X : Subgroup Γ} {W : Submodule K E} {b : E}
    (hb : b ∈ W) (hb0 : b ≠ 0) (hinv : ∀ x ∈ X, ∀ w ∈ W, (ρ x).toAdd w ∈ W)
    (hlin : ∀ x ∈ X, ∀ (c : K) (v : E), (ρ x).toAdd (c • v) = c • (ρ x).toAdd v)
    (hs : ∀ T : AddSubgroup E, T ≤ W.toAddSubgroup → (∀ x ∈ X, ∀ v ∈ T, (ρ x).toAdd v ∈ T) →
      T = ⊥ ∨ T = W.toAddSubgroup) :
    W.toAddSubgroup = ⨆ y : ↥X, actImage ρ (y : Γ) (Submodule.span K {b}).toAddSubgroup := by
  obtain ⟨T, hT⟩ : ∃ T : AddSubgroup E,
      T = ⨆ y : ↥X, actImage ρ (y : Γ) (Submodule.span K {b}).toAddSubgroup := ⟨_, rfl⟩
  rw [← hT]
  have hle : T ≤ W.toAddSubgroup := by
    rw [hT]
    refine iSup_le fun y => ?_
    intro u hu
    unfold actImage at hu
    obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.1 ((Submodule.mem_toAddSubgroup _).1 hw)
    show (ρ (y : Γ)).toAdd (a • b) ∈ W
    rw [hlin (y : Γ) y.2 a b]
    exact W.smul_mem a (hinv (y : Γ) y.2 b hb)
  have hinvT : ∀ x ∈ X, ∀ v ∈ T, (ρ x).toAdd v ∈ T := by
    intro x hx
    have key : T ≤ AddSubgroup.comap (ρ x).toAdd.toAddMonoidHom T := by
      rw [hT]
      refine iSup_le fun y => ?_
      intro u hu
      rw [AddSubgroup.mem_comap]
      unfold actImage at hu
      obtain ⟨w, hw, rfl⟩ := AddSubgroup.mem_map.1 hu
      have hmul : (ρ x).toAdd.toAddMonoidHom ((ρ (y : Γ)).toAdd.toAddMonoidHom w) =
          (ρ (x * (y : Γ))).toAdd w := by
        rw [map_mul]
        rfl
      rw [hmul]
      refine AddSubgroup.mem_iSup_of_mem (⟨x * (y : Γ), X.mul_mem hx y.2⟩ : ↥X) ?_
      unfold actImage
      exact AddSubgroup.mem_map.2 ⟨w, hw, rfl⟩
    intro v hv
    exact AddSubgroup.mem_comap.1 (key hv)
  have hbT : b ∈ T := by
    rw [hT]
    refine AddSubgroup.mem_iSup_of_mem (1 : ↥X) ?_
    unfold actImage
    refine AddSubgroup.mem_map.2 ⟨b, (Submodule.mem_toAddSubgroup _).2
      (Submodule.mem_span_singleton_self b), ?_⟩
    show (ρ 1).toAdd b = b
    rw [map_one]
    rfl
  rcases hs T hle hinvT with h | h
  · rw [h, AddSubgroup.mem_bot] at hbT
    exact absurd hbT hb0
  · exact h.symm

theorem actImage_span_card {K : Type*} [Field K] [Finite K] [Module K E]
    (ρ : Γ →* Multiplicative (AddAut E)) {y : Γ}
    (hlin : ∀ (c : K) (v : E), (ρ y).toAdd (c • v) = c • (ρ y).toAdd v) {b : E} (hb : b ≠ 0) :
    Nat.card (actImage ρ y (Submodule.span K {b}).toAddSubgroup) = Nat.card K := by
  have h1 : Nat.card (actImage ρ y (Submodule.span K {b}).toAddSubgroup) =
      Nat.card (Submodule.span K {b}).toAddSubgroup :=
    (Nat.card_congr (AddEquiv.addSubgroupMap (ρ y).toAdd
      (Submodule.span K {b}).toAddSubgroup).toEquiv).symm
  have h2 : Nat.card (Submodule.span K {b}).toAddSubgroup = Nat.card (Submodule.span K {b}) :=
    Nat.card_congr (Equiv.subtypeEquivRight fun x => Submodule.mem_toAddSubgroup _)
  rw [h1, h2]
  exact card_span_singleton hb


theorem hyperplane_false {K : Type*} [Field K] [Finite K] [Module K E] [Finite E]
    (f : LinearMap.BilinForm K E) (halt : ∀ v, f v v = 0)
    (hnd : ∀ v, (∀ w, f v w = 0) → v = 0)
    (ρ : Γ →* Multiplicative (AddAut E)) (X : Subgroup Γ) (hperf : ⁅X, X⁆ = X)
    (hlin : ∀ x ∈ X, ∀ (c : K) (v : E), (ρ x).toAdd (c • v) = c • (ρ x).toAdd v)
    (hiso : ∀ x ∈ X, ∀ v w, f ((ρ x).toAdd v) ((ρ x).toAdd w) = f v w)
    (V : Submodule K E) (hV : ∀ x ∈ X, ∀ v ∈ V, (ρ x).toAdd v ∈ V)
    (hcodim : Module.finrank K V + 1 = Module.finrank K E)
    (hfix : Nat.card (fixedIn (ρ.comp X.subtype) ⊤ V.toAddSubgroup) = 1) : False := by
  have hmul : ∀ x y v, (ρ (x * y)).toAdd v = (ρ x).toAdd ((ρ y).toAdd v) := by
    intro x y v
    rw [map_mul, toAdd_mul, AddAut.add_apply]
  have hone : ∀ v, (ρ 1).toAdd v = v := by
    intro v
    rw [map_one, toAdd_one, AddAut.zero_apply]
  have hinv : ∀ x v, (ρ x).toAdd ((ρ x⁻¹).toAdd v) = v := by
    intro x v
    rw [← hmul, mul_inv_cancel, hone]
  have hinv' : ∀ x v, (ρ x⁻¹).toAdd ((ρ x).toAdd v) = v := by
    intro x v
    rw [← hmul, inv_mul_cancel, hone]
  have hrefl : f.IsRefl := LinearMap.BilinForm.IsAlt.isRefl (show f.IsAlt from halt)
  have hsr : ∀ y, (∀ x, f x y = 0) → y = 0 := by
    intro y hy
    apply hnd y
    intro w
    have h1 := halt (y + w)
    simp only [map_add, LinearMap.add_apply] at h1
    linear_combination h1 - halt y - halt w - hy w
  have hnd' : f.Nondegenerate := ⟨hnd, hsr⟩
  have hfin : Module.finrank K (f.orthogonal V) = 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hnd' V]
    omega
  obtain ⟨u₀, hu₀U, hu₀ne, hspanE⟩ : ∃ u₀ : E, u₀ ∈ f.orthogonal V ∧ u₀ ≠ 0 ∧
      ∀ w ∈ f.orthogonal V, ∃ c : K, c • u₀ = w := by
    obtain ⟨u, hu0, hspan0⟩ := finrank_eq_one_iff'.mp hfin
    refine ⟨(u : E), u.2, fun h => hu0 (Submodule.coe_eq_zero.mp h), fun w hw => ?_⟩
    obtain ⟨c, hc⟩ := hspan0 ⟨w, hw⟩
    have hc' : c • (u : E) = w := congrArg Subtype.val hc
    exact ⟨c, hc'⟩
  have hsc : ∀ c : K, c • u₀ = u₀ → c = 1 := by
    intro c hc
    have h0 : (c - 1) • u₀ = 0 := by rw [sub_smul, one_smul, hc, sub_self]
    rcases smul_eq_zero.mp h0 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hu₀ne
  have hp : ∀ p : K, p = 1 → p • u₀ = u₀ := fun p hp1 => by rw [hp1, one_smul]
  have hVU : f.orthogonal (f.orthogonal V) = V :=
    LinearMap.BilinForm.orthogonal_orthogonal hnd' hrefl V
  have hu₀V : u₀ ∈ V := by
    rw [← hVU, LinearMap.BilinForm.mem_orthogonal_iff]
    intro n hn
    obtain ⟨c, rfl⟩ := hspanE n hn
    simp [halt u₀]
  have hline : ∀ x ∈ X, ∃ c : K, (ρ x).toAdd u₀ = c • u₀ := by
    intro x hx
    have hmem : (ρ x).toAdd u₀ ∈ f.orthogonal V := by
      rw [LinearMap.BilinForm.mem_orthogonal_iff]
      intro n hn
      have hn' : (ρ x⁻¹).toAdd n ∈ V := hV x⁻¹ (X.inv_mem hx) n hn
      have h := hiso x hx ((ρ x⁻¹).toAdd n) u₀
      rw [hinv x n] at h
      rw [h]
      exact (LinearMap.BilinForm.mem_orthogonal_iff.mp hu₀U) _ hn'
    obtain ⟨c, hc⟩ := hspanE _ hmem
    exact ⟨c, hc.symm⟩
  obtain ⟨L, hL⟩ : ∃ L : Subgroup Γ, ∀ x, x ∈ L ↔ x ∈ X ∧ (ρ x).toAdd u₀ = u₀ := by
    refine ⟨{ carrier := {x | x ∈ X ∧ (ρ x).toAdd u₀ = u₀}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · intro x y hx hy
      refine ⟨X.mul_mem hx.1 hy.1, ?_⟩
      show (ρ (x * y)).toAdd u₀ = u₀
      rw [hmul, hy.2, hx.2]
    · refine ⟨X.one_mem, ?_⟩
      show (ρ 1).toAdd u₀ = u₀
      rw [hone]
    · intro x hx
      refine ⟨X.inv_mem hx.1, ?_⟩
      show (ρ x⁻¹).toAdd u₀ = u₀
      have h := hinv' x u₀
      rw [hx.2] at h
      exact h
  have hcomm : ⁅X, X⁆ ≤ L := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    have hxy : ⁅x, y⁆ ∈ X := by
      have h := Subgroup.commutator_mem_commutator hx hy
      rwa [hperf] at h
    rw [hL]
    refine ⟨hxy, ?_⟩
    rw [commutatorElement_def, hmul, hmul, hmul]
    obtain ⟨a, ha⟩ := hline x hx
    obtain ⟨b, hb⟩ := hline y hy
    obtain ⟨a', ha'⟩ := hline x⁻¹ (X.inv_mem hx)
    obtain ⟨b', hb'⟩ := hline y⁻¹ (X.inv_mem hy)
    have h1 : a * a' = 1 := by
      apply hsc
      have h := hinv' x u₀
      rw [ha, hlin x⁻¹ (X.inv_mem hx), ha', smul_smul] at h
      exact h
    have h2 : b * b' = 1 := by
      apply hsc
      have h := hinv' y u₀
      rw [hb, hlin y⁻¹ (X.inv_mem hy), hb', smul_smul] at h
      exact h
    rw [hb', hlin x⁻¹ (X.inv_mem hx), ha', hlin y hy, hlin y hy, hb, hlin x hx, hlin x hx,
      hlin x hx, ha]
    simp only [smul_smul]
    apply hp
    linear_combination (a * a') * h2 + h1
  have hXL : X ≤ L := hperf.symm.le.trans hcomm
  have hstab : ∀ x ∈ X, (ρ x).toAdd u₀ = u₀ := fun x hx => ((hL x).mp (hXL hx)).2
  have hfixmem : u₀ ∈ fixedIn (ρ.comp X.subtype) ⊤ V.toAddSubgroup :=
    ⟨hu₀V, fun s _ => hstab s.1 s.2⟩
  obtain ⟨hsub, _⟩ := Nat.card_eq_one_iff_unique.mp hfix
  have h0 := @Subsingleton.elim _ hsub ⟨u₀, hfixmem⟩ 0
  exact hu₀ne (congrArg Subtype.val h0)


theorem tensor_decomp {K : Type*} [Field K] [Finite K] [Module K E] [Finite E]
    (ρ : Γ →* Multiplicative (AddAut E)) {Xa Xb Pa Pb : Subgroup Γ}
    (hcomm : ∀ x ∈ Xa, ∀ y ∈ Xb, x * y = y * x)
    {b : E} {Wa Wb : Submodule K E} {da db : ℕ}
    (Sa : TensorSide ρ b Xa Pa Wa da) (Sb : TensorSide ρ b Xb Pb Wb db) :
    ∃ (k : ℕ) (V : Submodule K E), db ≤ k ∧ Nat.card V = Nat.card K ^ (k * da) ∧
      (∀ x ∈ Xa, ∀ v ∈ V, (ρ x).toAdd v ∈ V) ∧
      Nat.card (fixedIn (ρ.comp Xa.subtype) (Pa.subgroupOf Xa) V.toAddSubgroup) =
        Nat.card K ^ k ∧
      Nat.card (fixedIn (ρ.comp Xa.subtype) ⊤ V.toAddSubgroup) = 1 ∧
      ((∀ p ∈ Pa, ∀ w ∈ Wa, (ρ p).toAdd w - w ∈ Submodule.span K {b}) →
        Nat.card (commIn (ρ.comp Xa.subtype) (Pa.subgroupOf Xa) V.toAddSubgroup) ≤
          Nat.card K ^ k) := by
  classical
  have hq : 1 < Nat.card K := Finite.one_lt_card
  let ρa : ↥Xa →* Multiplicative (AddAut E) := ρ.comp Xa.subtype
  let Wf : ↥Xb → AddSubgroup E := fun y => actImage ρ (y : Γ) Wa.toAddSubgroup
  have hy : ∀ y : ↥Xb, ∀ x ∈ Xa, x * (y : Γ) = (y : Γ) * x := fun y x hx => hcomm x hx y y.2
  have hWa_inv : ∀ x ∈ Xa, ∀ v ∈ Wa.toAddSubgroup, (ρ x).toAdd v ∈ Wa.toAddSubgroup := Sa.inv
  have hinv : ∀ (i : ↥Xb) (h : ↥Xa) (v : E), v ∈ Wf i → (ρa h).toAdd v ∈ Wf i := by
    intro i h v hv
    exact actImage_invariant ρ (hy i) hWa_inv (h : Γ) h.2 v hv
  have hWa0 : Wa.toAddSubgroup ≠ ⊥ := by
    intro h
    have : b ∈ Wa.toAddSubgroup := Sa.b_mem
    rw [h, AddSubgroup.mem_bot] at this
    exact Sa.b_ne this
  have hsimple : ∀ i : ↥Xb, Wf i ≠ ⊥ ∧ ∀ T : AddSubgroup E, T ≤ Wf i →
      (∀ (h : ↥Xa) (v : E), v ∈ T → (ρa h).toAdd v ∈ T) → T = ⊥ ∨ T = Wf i := by
    intro i
    refine ⟨fun h => hWa0 ((actImage_eq_bot_iff ρ _ _).mp h), fun T hT hTinv => ?_⟩
    exact actImage_simple ρ (hy i) hWa_inv Sa.simple T hT
      (fun x hx v hv => hTinv ⟨x, hx⟩ v hv)
  obtain ⟨J, hJfin, hJind, hJsup⟩ := exists_iSupIndep_of_simple ρa Wf hinv hsimple
  haveI : Fintype J := hJfin.fintype
  let A : AddSubgroup E := ⨆ j : J, Wf (j : ↥Xb)
  have hsmulA : ∀ (c : K) (v : E), v ∈ A → c • v ∈ A := by
    intro c v hv
    refine smul_mem_iSup_addSubgroup (fun j : J => Wf (j : ↥Xb)) (fun j c' v' hv' => ?_) hv
    exact smul_mem_actImage ρ (Sb.lin _ (j : ↥Xb).2) Wa hv'
  let V : Submodule K E :=
    { carrier := A
      add_mem' := fun {a b} ha hb => A.add_mem ha hb
      zero_mem' := A.zero_mem
      smul_mem' := fun c v hv => hsmulA c v hv }
  have hVA : V.toAddSubgroup = A := rfl
  have hWa_card : Nat.card ↥Wa.toAddSubgroup = Nat.card K ^ da := Sa.card
  have hcardV : Nat.card V = Nat.card K ^ (Fintype.card J * da) := by
    have h1 : Nat.card V = Nat.card ↥A := rfl
    rw [h1, card_iSup_of_iSupIndep (fun j : J => Wf (j : ↥Xb)) hJind]
    simp only [Wf, card_actImage, hWa_card]
    rw [Finset.prod_const, Finset.card_univ, ← pow_mul, mul_comm]
  have hVinv : ∀ x ∈ Xa, ∀ v ∈ V, (ρ x).toAdd v ∈ V := by
    intro x hx v hv
    have hv' : v ∈ A := hv
    refine AddSubgroup.iSup_induction (fun j : J => Wf (j : ↥Xb))
      (C := fun v => (ρ x).toAdd v ∈ A) hv' ?_ ?_ ?_
    · intro j w hw
      exact AddSubgroup.mem_iSup_of_mem j (hinv j ⟨x, hx⟩ w hw)
    · simp
    · intro u w hu hw
      rw [map_add]
      exact A.add_mem hu hw
  have hfix_span : fixedIn ρa (Pa.subgroupOf Xa) Wa.toAddSubgroup =
      (Submodule.span K {b}).toAddSubgroup := by
    ext v
    constructor
    · rintro ⟨hvW, hvfix⟩
      exact (Sa.fixed v hvW).mp (fun p hp => hvfix ⟨p, Sa.le hp⟩ hp)
    · intro hv
      have hvW : v ∈ Wa := by
        have hb : b ∈ Wa := Sa.b_mem
        exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hb)) hv
      refine ⟨hvW, fun s hs => ?_⟩
      exact (Sa.fixed v hvW).mpr hv _ hs
  have hfixJ : ∀ j : J, Nat.card (fixedIn ρa (Pa.subgroupOf Xa) (Wf (j : ↥Xb))) =
      Nat.card K := by
    intro j
    show Nat.card (fixedIn ρa (Pa.subgroupOf Xa)
      (actImage ρ ((j : ↥Xb) : Γ) Wa.toAddSubgroup)) = _
    rw [fixedIn_actImage ρ Xa (hy j), hfix_span]
    exact actImage_span_card ρ (Sb.lin _ (j : ↥Xb).2) Sb.b_ne
  have hfixV : Nat.card (fixedIn ρa (Pa.subgroupOf Xa) V.toAddSubgroup) =
      Nat.card K ^ Fintype.card J := by
    rw [hVA]
    show Nat.card (fixedIn ρa (Pa.subgroupOf Xa) (⨆ j : J, Wf (j : ↥Xb))) = _
    rw [card_fixedIn_iSup ρa (Pa.subgroupOf Xa) (fun j : J => Wf (j : ↥Xb)) hJind
      (fun j h v hv => hinv j h v hv)]
    simp only [hfixJ]
    rw [Finset.prod_const, Finset.card_univ]
  have hfixTop : fixedIn ρa ⊤ Wa.toAddSubgroup = ⊥ := by
    rcases Sa.simple (fixedIn ρa ⊤ Wa.toAddSubgroup) (fun v hv => hv.1)
      (fun x hx v hv => by
        have h1 : (ρa ⟨x, hx⟩).toAdd v = v := hv.2 ⟨x, hx⟩ (Subgroup.mem_top _)
        have h2 : (ρ x).toAdd v = v := h1
        rw [h2]
        exact hv) with h | h
    · exact h
    · exfalso
      obtain ⟨x, hx, w, hw, hxw⟩ := Sa.nontriv
      have hwT : w ∈ fixedIn ρa ⊤ Wa.toAddSubgroup := by
        rw [h]
        exact hw
      exact hxw (hwT.2 ⟨x, hx⟩ (Subgroup.mem_top _))
  have hfixTopJ : ∀ j : J, Nat.card (fixedIn ρa ⊤ (Wf (j : ↥Xb))) = 1 := by
    intro j
    show Nat.card (fixedIn ρa ⊤ (actImage ρ ((j : ↥Xb) : Γ) Wa.toAddSubgroup)) = 1
    rw [fixedIn_actImage ρ Xa (hy j), hfixTop]
    have h0 : actImage ρ ((j : ↥Xb) : Γ) (⊥ : AddSubgroup E) = ⊥ :=
      (actImage_eq_bot_iff ρ _ _).mpr rfl
    rw [h0]
    exact AddSubgroup.card_bot
  have hfixTopV : Nat.card (fixedIn ρa ⊤ V.toAddSubgroup) = 1 := by
    rw [hVA]
    show Nat.card (fixedIn ρa ⊤ (⨆ j : J, Wf (j : ↥Xb))) = 1
    rw [card_fixedIn_iSup ρa ⊤ (fun j : J => Wf (j : ↥Xb)) hJind
      (fun j h v hv => hinv j h v hv)]
    simp only [hfixTopJ, Finset.prod_const_one]
  have hcommV : (∀ p ∈ Pa, ∀ w ∈ Wa, (ρ p).toAdd w - w ∈ Submodule.span K {b}) →
      Nat.card (commIn ρa (Pa.subgroupOf Xa) V.toAddSubgroup) ≤
        Nat.card K ^ Fintype.card J := by
    intro hd3
    rw [hVA]
    show Nat.card (commIn ρa (Pa.subgroupOf Xa) (⨆ j : J, Wf (j : ↥Xb))) ≤ _
    refine (card_commIn_iSup_le ρa (Pa.subgroupOf Xa) (fun j : J => Wf (j : ↥Xb))).trans ?_
    calc ∏ j : J, Nat.card (commIn ρa (Pa.subgroupOf Xa) (Wf (j : ↥Xb)))
        ≤ ∏ _j : J, Nat.card K := Finset.prod_le_prod' (fun j _ => ?_)
      _ = Nat.card K ^ Fintype.card J := by rw [Finset.prod_const, Finset.card_univ]
    show Nat.card (commIn ρa (Pa.subgroupOf Xa)
      (actImage ρ ((j : ↥Xb) : Γ) Wa.toAddSubgroup)) ≤ _
    rw [commIn_actImage ρ Xa (hy j)]
    have hle : commIn ρa (Pa.subgroupOf Xa) Wa.toAddSubgroup ≤
        (Submodule.span K {b}).toAddSubgroup := by
      refine (AddSubgroup.closure_le _).mpr ?_
      rintro x ⟨s, hs, w, hw, rfl⟩
      exact hd3 (s : Γ) hs w hw
    calc Nat.card ↥(actImage ρ ((j : ↥Xb) : Γ) (commIn ρa (Pa.subgroupOf Xa) Wa.toAddSubgroup))
        ≤ Nat.card ↥(actImage ρ ((j : ↥Xb) : Γ) (Submodule.span K {b}).toAddSubgroup) :=
          AddSubgroup.card_le_of_le (actImage_mono ρ _ hle)
      _ = Nat.card K := actImage_span_card ρ (Sb.lin _ (j : ↥Xb).2) Sb.b_ne
  have hbfix : ∀ p ∈ Pa, (ρ p).toAdd b = b :=
    (Sa.fixed b Sa.b_mem).mpr (Submodule.mem_span_singleton_self b)
  have hdb : db ≤ Fintype.card J := by
    have hWb_gen := eq_iSup_actImage_span ρ Sb.b_mem Sb.b_ne Sb.inv Sb.lin Sb.simple
    have hle : Wb.toAddSubgroup ≤ fixedIn ρa (Pa.subgroupOf Xa) V.toAddSubgroup := by
      rw [hWb_gen]
      refine iSup_le fun y => ?_
      intro v hv
      obtain ⟨w, hw, rfl⟩ := hv
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
      have hcb : c • b ∈ Wa.toAddSubgroup := Wa.smul_mem c Sa.b_mem
      have hmem : (ρ (y : Γ)).toAdd.toAddMonoidHom (c • b) ∈ Wf y := ⟨c • b, hcb, rfl⟩
      refine ⟨?_, fun s hs => ?_⟩
      · have h2 : (ρ (y : Γ)).toAdd.toAddMonoidHom (c • b) ∈ ⨆ i : ↥Xb, Wf i :=
          AddSubgroup.mem_iSup_of_mem y hmem
        rw [← hJsup] at h2
        exact h2
      · have hcomm' : (ρ (s : Γ)).toAdd ((ρ (y : Γ)).toAdd (c • b)) =
            (ρ (y : Γ)).toAdd ((ρ (s : Γ)).toAdd (c • b)) := by
          have := congrArg (fun g => (ρ g).toAdd (c • b)) (hy y (s : Γ) s.2)
          simpa using this
        show (ρ (s : Γ)).toAdd ((ρ (y : Γ)).toAdd (c • b)) = (ρ (y : Γ)).toAdd (c • b)
        rw [hcomm', Sa.lin _ s.2, hbfix (s : Γ) hs]
    have hcard := AddSubgroup.card_le_of_le hle
    have h3 : Nat.card ↥Wb.toAddSubgroup = Nat.card K ^ db := Sb.card
    rw [h3, hfixV] at hcard
    exact (Nat.pow_le_pow_iff_right hq).mp hcard
  exact ⟨Fintype.card J, V, hdb, hcardV, hVinv, hfixV, hfixTopV, hcommV⟩

theorem case34_false {K : Type*} [Field K] [Finite K] [Module K E] [Finite E]
    (f : LinearMap.BilinForm K E) (halt : ∀ v, f v v = 0)
    (hnd : ∀ v, (∀ w, f v w = 0) → v = 0)
    (ρ : Γ →* Multiplicative (AddAut E)) {n : ℕ} (hdim : Module.finrank K E = 2 * n)
    {Xa Xb Pa Pb : Subgroup Γ} (hcomm : ∀ x ∈ Xa, ∀ y ∈ Xb, x * y = y * x)
    {b : E} {Wa Wb : Submodule K E}
    (Sa : TensorSide ρ b Xa Pa Wa 3) (Sb : TensorSide ρ b Xb Pb Wb 4)
    (hisoa : ∀ x ∈ Xa, ∀ v w, f ((ρ x).toAdd v) ((ρ x).toAdd w) = f v w)
    (hn : n + 1 ≤ 7) : False := by
  classical
  have hq : 1 < Nat.card K := Finite.one_lt_card
  haveI : Module.Finite K E := Module.Finite.of_finite
  obtain ⟨k, V, hk, hVc, -, hfixP, -, hcommle⟩ := tensor_decomp ρ hcomm Sa Sb
  have hE : Nat.card E = Nat.card K ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hdim]
  have hle : Nat.card V ≤ Nat.card E := Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [hVc, hE] at hle
  have h3 : k * 3 ≤ 2 * n := (Nat.pow_le_pow_iff_right hq).mp hle
  have hk4 : k = 4 := by omega
  have hn6 : n = 6 := by omega
  subst hk4
  subst hn6
  have hfr : Module.finrank K V = 12 := by
    have h1 := Module.natCard_eq_pow_finrank (K := K) (V := V)
    rw [hVc] at h1
    exact (Nat.pow_right_injective hq h1).symm
  have hVtop : V = ⊤ := Submodule.eq_top_of_finrank_eq (by rw [hfr, hdim])
  have hVtop' : V.toAddSubgroup = ⊤ := by rw [hVtop]; rfl
  rw [hVtop'] at hfixP
  have hcommle' := hcommle (Sa.d3 rfl)
  rw [hVtop'] at hcommle'
  have hE1 := card_commIn_mul_card_fixedIn f halt hnd (ρ.comp Xa.subtype)
    (fun h c v => Sa.lin _ h.2 c v) (fun h v w => hisoa _ h.2 v w) (Pa.subgroupOf Xa)
  rw [hE, hfixP] at hE1
  have h4 : Nat.card K ^ 12 ≤ Nat.card K ^ 4 * Nat.card K ^ 4 := by
    calc Nat.card K ^ 12 = Nat.card ↥(commIn (ρ.comp Xa.subtype) (Pa.subgroupOf Xa) ⊤) *
          Nat.card K ^ 4 := by rw [← hE1]
      _ ≤ Nat.card K ^ 4 * Nat.card K ^ 4 := Nat.mul_le_mul_right _ hcommle'
  rw [← pow_add] at h4
  have := (Nat.pow_le_pow_iff_right hq).mp h4
  omega

theorem tensor_count_false {K : Type*} [Field K] [Finite K] [Module K E] [Finite E]
    (f : LinearMap.BilinForm K E) (halt : ∀ v, f v v = 0)
    (hnd : ∀ v, (∀ w, f v w = 0) → v = 0)
    (ρ : Γ →* Multiplicative (AddAut E)) {n : ℕ} (hdim : Module.finrank K E = 2 * n)
    {X₁ X₂ P₁ P₂ : Subgroup Γ} (hcomm : ∀ x ∈ X₁, ∀ y ∈ X₂, x * y = y * x)
    {b : E} {W₁ W₂ : Submodule K E} {d₁ d₂ : ℕ}
    (S₁ : TensorSide ρ b X₁ P₁ W₁ d₁) (S₂ : TensorSide ρ b X₂ P₂ W₂ d₂)
    (hiso₁ : ∀ x ∈ X₁, ∀ v w, f ((ρ x).toAdd v) ((ρ x).toAdd w) = f v w)
    (hiso₂ : ∀ x ∈ X₂, ∀ v w, f ((ρ x).toAdd v) ((ρ x).toAdd w) = f v w)
    (hn : n + 1 ≤ d₁ + d₂) : False := by
  classical
  have hq : 1 < Nat.card K := Finite.one_lt_card
  haveI : Module.Finite K E := Module.Finite.of_finite
  have hE : Nat.card E = Nat.card K ^ (2 * n) := by
    rw [Module.natCard_eq_pow_finrank (K := K), hdim]
  obtain ⟨k₂, V₂, hk₂, hV₂c, hV₂i, -, hV₂t, -⟩ :=
    tensor_decomp ρ (fun x hx y hy => (hcomm y hy x hx).symm) S₂ S₁
  have hle : Nat.card V₂ ≤ Nat.card E := Nat.card_le_card_of_injective _ Subtype.val_injective
  rw [hV₂c, hE] at hle
  have h2 : k₂ * d₂ ≤ 2 * n := (Nat.pow_le_pow_iff_right hq).mp hle
  have hd1 := S₁.three
  have hd2 := S₂.three
  have hprod : d₁ * d₂ ≤ k₂ * d₂ := Nat.mul_le_mul_right _ hk₂
  have hcases : (d₁ = 3 ∧ d₂ = 3) ∨ (d₁ = 3 ∧ d₂ = 4) ∨ (d₁ = 4 ∧ d₂ = 3) := by
    have e2 : d₁ * d₂ + 2 ≤ 2 * d₁ + 2 * d₂ := by nlinarith
    have hd1' : d₁ ≤ 4 := by
      by_contra h
      have h := not_le.mp h
      nlinarith
    have hd2' : d₂ ≤ 4 := by
      by_contra h
      have h := not_le.mp h
      nlinarith
    interval_cases d₁ <;> interval_cases d₂ <;> omega
  rcases hcases with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · have hk : k₂ = 3 := by omega
    have hn5 : n = 5 := by omega
    subst hk
    subst hn5
    have hfr : Module.finrank K V₂ = 9 := by
      have h1 := Module.natCard_eq_pow_finrank (K := K) (V := V₂)
      rw [hV₂c] at h1
      exact (Nat.pow_right_injective hq h1).symm
    exact hyperplane_false f halt hnd ρ X₂ S₂.perfect S₂.lin hiso₂ V₂ hV₂i (by omega) hV₂t
  · exact case34_false f halt hnd ρ hdim hcomm S₁ S₂ hiso₁ (by omega)
  · exact case34_false f halt hnd ρ hdim (fun x hx y hy => (hcomm y hy x hx).symm) S₂ S₁
      hiso₂ (by omega)

end TensorAlg

end CFSG.RankThree.GF2n.Stroth80
