module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCBar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineCOrbGen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.TC914

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.NFW

theorem exists_compl_of_isElemAbelian {G : Type*} [Group G] {A B : Subgroup G}
    (hA : IsElemAbelian 2 A) (hBA : B ≤ A) : ∃ C : Subgroup G, C ≤ A ∧ C ⊓ B = ⊥ ∧ C ⊔ B = A := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 A := hA.isElementaryAbelian
  obtain ⟨C, hC⟩ := CFSG.IsElementaryAbelian.exists_isCompl 2 A (B.subgroupOf A)
  refine ⟨C.map A.subtype, map_subtype_le _, ?_, ?_⟩
  · rw [← map_subgroupOf_eq_of_le hBA, ← map_inf_eq _ _ _ A.subtype_injective, inf_comm,
      hC.inf_eq_bot, Subgroup.map_bot]
  · rw [← map_subgroupOf_eq_of_le hBA, ← Subgroup.map_sup, sup_comm, hC.sup_eq_top,
      ← MonoidHom.range_eq_map, range_subtype]

variable {X : Type} [Group X] [Finite X] {Lb Tb : Subgroup X} {B : Type} [Group B] [Finite B]
  {π : ↥(tcN1 Lb Tb) →* B} {Es : Subgroup B}

@[expose] def lbHom (π : ↥(tcN1 Lb Tb) →* B) : ↥Lb →* B := π.comp (inclusion le_sup_left)

@[expose] def lbCopy (π : ↥(tcN1 Lb Tb) →* B) (K : Subgroup B) : Subgroup X :=
  (K.comap (lbHom π)).map Lb.subtype

omit [Finite X] [Finite B] in
theorem mem_lbCopy {K : Subgroup B} {x : X} :
    x ∈ lbCopy π K ↔ ∃ hx : x ∈ Lb, π ⟨x, mem_sup_left hx⟩ ∈ K := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y.2, hy⟩
  · rintro ⟨hx, hK⟩
    exact ⟨⟨x, hx⟩, hK, rfl⟩

omit [Finite X] [Finite B] in
theorem coe_mem_lbCopy {K : Subgroup B} {x : ↥Lb} : (x : X) ∈ lbCopy π K ↔ lbHom π x ∈ K :=
  ⟨fun h => by
    obtain ⟨_, hK⟩ := mem_lbCopy.1 h
    exact hK, fun h => mem_lbCopy.2 ⟨x.2, h⟩⟩

omit [Finite X] [Finite B] in
theorem lbCopy_le (K : Subgroup B) : lbCopy π K ≤ Lb := map_subtype_le _

omit [Finite X] [Finite B] in
theorem lbHom_range : (lbHom π).range = barSub π Lb := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨inclusion le_sup_left x, x.2, rfl⟩
  · rintro ⟨n, hn, rfl⟩
    exact ⟨⟨n, hn⟩, rfl⟩

omit [Finite B] in
theorem lbHom_injective (c : TCBar Lb Tb π Es) : Function.Injective (lbHom π) := fun x y h => by
  have h1 := c.eq_of_map_eq (x := inclusion le_sup_left x) (y := inclusion le_sup_left y) x.2 y.2 h
  have h2 := congrArg Subtype.val h1
  exact Subtype.ext h2

omit [Finite B] in
theorem twoPTwoIrred_lbCopy (c : TCBar Lb Tb π Es) {K S Z : Subgroup B} {p : ℕ}
    (h : TwoPTwoIrred K S Z p) (hK : K ≤ barSub π Lb) :
    TwoPTwoIrred (lbCopy π K) (lbCopy π S) (lbCopy π Z) p := by
  have hr : K ≤ (lbHom π).range := by rw [lbHom_range]; exact hK
  rw [lbCopy, lbCopy, lbCopy, twoPTwoIrred_map_iff (ι := Lb.subtype) Lb.subtype_injective,
    ← twoPTwoIrred_map_iff (ι := lbHom π) (lbHom_injective c), map_comap_eq_self hr,
    map_comap_eq_self (h.sylowTwo.le.trans hr), map_comap_eq_self (h.sylowP.le.trans hr)]
  exact h

omit [Finite X] [Finite B] in
theorem lbCopy_inf (K K' : Subgroup B) : lbCopy π (K ⊓ K') = lbCopy π K ⊓ lbCopy π K' := by
  rw [lbCopy, comap_inf, map_inf_eq _ _ _ Lb.subtype_injective]
  rfl

omit [Finite B] in
theorem lbCopy_D (c : TCBar Lb Tb π Es) : lbCopy π (barSub π Tb) = Lb ⊓ Tb := by
  ext x
  rw [mem_lbCopy, mem_inf]
  constructor
  · rintro ⟨hx, hD⟩
    have h : x ∈ liftSub π (barSub π Tb) := mem_liftSub.2 ⟨_, hD⟩
    rw [c.liftSub_barSub_T] at h
    exact ⟨hx, h.1⟩
  · rintro ⟨hx, hT⟩
    exact ⟨hx, mem_barSub_of_mem' (π := π) (x := ⟨x, mem_sup_left hx⟩) hT⟩

omit [Finite B] in
theorem lbCopy_pCoreOf (c : TCBar Lb Tb π Es) {K : Subgroup B} (hK : K ≤ barSub π Lb) :
    lbCopy π (pCoreOf 2 K) = pCoreOf 2 (lbCopy π K) := by
  have hr : K ≤ (lbHom π).range := by rw [lbHom_range]; exact hK
  have h1 : pCoreOf 2 (K.comap (lbHom π)) = (pCoreOf 2 K).comap (lbHom π) := by
    rw [← comap_map_eq_self_of_injective (lbHom_injective c) (pCoreOf 2 (K.comap (lbHom π))),
      NFA6.pCoreOf_map (ι := lbHom π) (lbHom_injective c), map_comap_eq_self hr]
  rw [lbCopy, lbCopy, ← NFA6.pCoreOf_map (ι := Lb.subtype) Lb.subtype_injective, h1]

omit [Finite X] [Finite B] in
theorem mem_normalizer_lbCopy {g : ↥(tcN1 Lb Tb)} {K : Subgroup B}
    (h : π g ∈ normalizer (K : Set B)) : (g : X) ∈ normalizer (lbCopy π K : Set X) := by
  have hgL : (g : X) ∈ normalizer (Lb : Set X) :=
    (sup_le le_normalizer inf_le_right : tcN1 Lb Tb ≤ normalizer (Lb : Set X)) g.2
  rw [mem_normalizer_iff]
  intro x
  rw [mem_lbCopy, mem_lbCopy]
  constructor
  · rintro ⟨hx, hK⟩
    have hx' := (mem_normalizer_iff.1 hgL x).1 hx
    refine ⟨hx', ?_⟩
    have e : (⟨(g : X) * x * (g : X)⁻¹, mem_sup_left hx'⟩ : ↥(tcN1 Lb Tb)) =
        g * ⟨x, mem_sup_left hx⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 h _).1 hK
  · rintro ⟨hx', hK⟩
    have hx := (mem_normalizer_iff.1 hgL x).2 hx'
    refine ⟨hx, ?_⟩
    have e : (⟨(g : X) * x * (g : X)⁻¹, mem_sup_left hx'⟩ : ↥(tcN1 Lb Tb)) =
        g * ⟨x, mem_sup_left hx⟩ * g⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv] at hK
    exact (mem_normalizer_iff.1 h _).2 hK

omit [Finite X] [Finite B] in
theorem lcomm_of (c : TCBar Lb Tb π Es) :
    ∀ g ∈ Tb, g ∉ normalizer (Lb : Set X) → ∀ x ∈ conjSub g Lb, ∀ y ∈ Lb, x * y = y * x := by
  intro g hg hgN x hx y hy
  have hne : conjSubgroup Lb g⁻¹ ≠ conjSubgroup Lb 1 := by
    rw [conjSubgroup_one, Ne, conjSubgroup_eq_iff_mem_normalizer, inv_mem_iff]
    exact hgN
  refine c.comm g⁻¹ (Tb.inv_mem hg) 1 Tb.one_mem hne x ?_ y (by rwa [conjSubgroup_one])
  rw [mem_conjSubgroup_iff, inv_inv]
  exact mem_conjSub.1 hx

omit [Finite X] [Finite B] in
theorem le_normalizer_lbCopy {M : Subgroup X} (hM : M ≤ tcN1 Lb Tb) {K : Subgroup B}
    (h : barSub π M ≤ normalizer (K : Set B)) : M ≤ normalizer (lbCopy π K : Set X) :=
  fun m hm => mem_normalizer_lbCopy (g := ⟨m, hM hm⟩) (h (mem_barSub_of_mem' (x := ⟨m, hM hm⟩) hm))

omit [Finite B] in
theorem twoPTwoIrred_lbCopy_inf (c : TCBar Lb Tb π Es) {H Xh : Subgroup B} {p : ℕ}
    (h : TwoPTwoIrred H (H ⊓ barSub π Tb) Xh p) (hHL : H ≤ barSub π Lb) :
    TwoPTwoIrred (lbCopy π H) (lbCopy π H ⊓ Tb) (lbCopy π Xh) p := by
  have h' := twoPTwoIrred_lbCopy c h hHL
  rwa [lbCopy_inf, lbCopy_D c, ← inf_assoc, inf_eq_left.2 (lbCopy_le H)] at h'

omit [Finite B] in
theorem nontriv_lbCopy (c : TCBar Lb Tb π Es) {H Xh : Subgroup B} (hHL : H ≤ barSub π Lb)
    (hXH : Xh ≤ H) (h : ∃ y ∈ H ⊓ barSub π Tb ⊓ normalizer (Xh : Set B), ∃ x ∈ Xh,
      y * x * y⁻¹ ≠ x) :
    ∃ y ∈ lbCopy π H ⊓ Tb ⊓ normalizer (lbCopy π Xh : Set X), ∃ x ∈ lbCopy π Xh,
      y * x * y⁻¹ ≠ x := by
  have hr : H ≤ (lbHom π).range := by rw [lbHom_range]; exact hHL
  obtain ⟨y, ⟨⟨hyH, hyD⟩, hyN⟩, x, hx, hne⟩ := h
  obtain ⟨y₀, rfl⟩ : y ∈ (lbHom π).range := hr hyH
  obtain ⟨x₀, rfl⟩ : x ∈ (lbHom π).range := hr (hXH hx)
  have hyT : (y₀ : X) ∈ Tb := by
    have h : (y₀ : X) ∈ lbCopy π (barSub π Tb) := coe_mem_lbCopy.2 hyD
    rw [lbCopy_D c] at h
    exact h.2
  refine ⟨y₀, ⟨⟨coe_mem_lbCopy.2 hyH, hyT⟩,
    mem_normalizer_lbCopy (g := inclusion le_sup_left y₀) hyN⟩, x₀, coe_mem_lbCopy.2 hx,
    fun h => hne ?_⟩
  have h' : y₀ * x₀ * y₀⁻¹ = x₀ := Subtype.ext h
  rw [← map_inv, ← map_mul, ← map_mul, h']

omit [Finite B] in
theorem lbCopy_inf_centralizer (c : TCBar Lb Tb π Es) {H : Subgroup B}
    (h : H ⊓ centralizer (barSub π Lb : Set B) = ⊥) :
    lbCopy π H ⊓ centralizer (Lb : Set X) = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxC⟩
  obtain ⟨x₀, hx₀, rfl⟩ := hx
  have h1 : lbHom π x₀ ∈ H ⊓ centralizer (barSub π Lb : Set B) := by
    refine ⟨hx₀, mem_centralizer_iff.2 ?_⟩
    rintro _ ⟨n, hn, rfl⟩
    have e : n * inclusion le_sup_left x₀ = inclusion le_sup_left x₀ * n :=
      Subtype.ext (mem_centralizer_iff.1 hxC _ hn)
    show π n * π (inclusion le_sup_left x₀) = π (inclusion le_sup_left x₀) * π n
    rw [← map_mul, ← map_mul, e]
  rw [h, mem_bot] at h1
  have h2 : x₀ = 1 := lbHom_injective c (h1.trans (map_one _).symm)
  rw [h2, map_one]
  exact one_mem _

omit [Finite B] in
theorem commutator_mem_lbCopy (c : TCBar Lb Tb π Es) {H Xh : Subgroup B}
    (hHL : H ≤ barSub π Lb) {F : Subgroup X} (hFT : F ≤ tcT1 Lb Tb)
    (hFX : ∀ f ∈ barSub π F, ∀ x ∈ Xh, f * x * f⁻¹ * x⁻¹ ∈ pCoreOf 2 H) :
    ∀ f ∈ F, ∀ x ∈ lbCopy π Xh, f * x * f⁻¹ * x⁻¹ ∈ pCoreOf 2 (lbCopy π H) := by
  intro f hf x hx
  rw [← lbCopy_pCoreOf c hHL, mem_lbCopy]
  obtain ⟨hxL, hxX⟩ := mem_lbCopy.1 hx
  have hfN : f ∈ tcN1 Lb Tb := mem_sup_right (hFT hf)
  have hm : f * x * f⁻¹ * x⁻¹ ∈ Lb :=
    mul_mem ((mem_normalizer_iff.1 (hFT hf).2 x).1 hxL) (inv_mem hxL)
  refine ⟨hm, ?_⟩
  have e : (⟨f * x * f⁻¹ * x⁻¹, mem_sup_left hm⟩ : ↥(tcN1 Lb Tb)) =
      ⟨f, hfN⟩ * ⟨x, mem_sup_left hxL⟩ * (⟨f, hfN⟩ : ↥(tcN1 Lb Tb))⁻¹ *
        (⟨x, mem_sup_left hxL⟩ : ↥(tcN1 Lb Tb))⁻¹ := rfl
  rw [e, map_mul, map_mul, map_mul, map_inv, map_inv]
  exact hFX _ (mem_barSub_of_mem' (x := ⟨f, hfN⟩) hf) _ hxX

end CFSG.LocalAnalysis.WeakClosure81.TC914
