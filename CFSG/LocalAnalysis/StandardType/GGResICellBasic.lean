module

public import CFSG.LocalAnalysis.StandardType.GGResICell

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggCard_closure_of_list {G : Type} [Group G] {s : Set G} {es : List G} (hnd : es.Nodup)
    (h1 : (1 : G) ∈ es) (hmul : ∀ x ∈ s, ∀ y ∈ es, x * y ∈ es)
    (hinv : ∀ x ∈ s, ∀ y ∈ es, x⁻¹ * y ∈ es) (hsub : ∀ y ∈ es, y ∈ Subgroup.closure s) :
    Nat.card (Subgroup.closure s) = es.length := by
  classical
  have hset : (Subgroup.closure s : Set G) = (es.toFinset : Set G) := by
    ext y
    simp only [SetLike.mem_coe, List.mem_toFinset]
    refine ⟨fun hy => ?_, hsub y⟩
    induction hy using Subgroup.closure_induction_left with
    | one => exact h1
    | mul_left x hx y _ ih => exact hmul x hx y ih
    | inv_mul_cancel x hx y _ ih => exact hinv x hx y ih
  calc Nat.card (Subgroup.closure s) = Nat.card (es.toFinset : Set G) := by rw [← hset]; rfl
    _ = (es.toFinset : Set G).ncard := Nat.card_coe_set_eq _
    _ = es.toFinset.card := Set.ncard_coe_finset _
    _ = es.length := List.toFinset_card_of_nodup hnd

theorem ggResI_jlEquiv {n r : ℕ} {ib : Fin n} {jl : List (Fin n)} (hlen : jl.length = r)
    (hnd : jl.Nodup) (hne : ∀ j ∈ jl, j ≠ ib) (hall : ∀ j : Fin n, j = ib ∨ j ∈ jl) :
    ∃ e : Fin r ≃ {i : Fin n // i ≠ ib}, ∀ k, (e k).1 = jl.getD k.val ib := by
  have hmem : ∀ k : Fin r, jl.getD k.val ib ∈ jl := fun k => by
    rw [List.getD_eq_getElem _ _ (by omega)]
    exact List.getElem_mem _
  let f : Fin r → {i : Fin n // i ≠ ib} := fun k => ⟨jl.getD k.val ib, hne _ (hmem k)⟩
  have hinj : Function.Injective f := by
    intro k k' hkk
    have h1 : jl.getD k.val ib = jl.getD k'.val ib := congrArg Subtype.val hkk
    rw [List.getD_eq_getElem _ _ (by omega), List.getD_eq_getElem _ _ (by omega)] at h1
    exact Fin.ext ((List.Nodup.getElem_inj_iff hnd).mp h1)
  have hsurj : Function.Surjective f := by
    rintro ⟨j, hj⟩
    obtain ⟨i, hi, hij⟩ := List.getElem_of_mem ((hall j).resolve_left hj)
    refine ⟨⟨i, by omega⟩, Subtype.ext ?_⟩
    change jl.getD i ib = j
    rw [List.getD_eq_getElem _ _ hi, hij]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩, fun k => rfl⟩

section FMat

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  {R : Type} [CommRing R] {φ : R →+* ZMod p} {N : ℕ}
  {T : Fin N → Vector R (N + 1)} {h : Fin N → V} {α : Fin N → Module.Dual (ZMod p) V}
  {g : Fin N → (V ≃ₗ[ZMod p] V)}

theorem ggFMat_apply (hT : GGFTable φ T h 0 α) (hg : ∀ k w, g k w = w - α k w • h k)
    (ws : List (Fin N)) (l : Fin N) :
    (ws.map g).prod (h l) =
      ∑ m : Fin N, φ ((ggFWord T ws (ggFUnit l.castSucc)).get m.castSucc) • h m := by
  rw [← ggFPi_unit (φ := φ) h 0 l, ggFPi_word hT hg, ggFPi_zero]

theorem ggFMat_eq (hT : GGFTable φ T h 0 α) (hg : ∀ k w, g k w = w - α k w • h k)
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤) {ws₁ ws₂ : List (Fin N)}
    (he : ggFMat T ws₁ = ggFMat T ws₂) : (ws₁.map g).prod = (ws₂.map g).prod := by
  have hlm : ∀ l m : Fin N, (ggFWord T ws₁ (ggFUnit l.castSucc)).get m.castSucc =
      (ggFWord T ws₂ (ggFUnit l.castSucc)).get m.castSucc := by
    intro l m
    have h1 := (List.map_inj_left.mp he) l (List.mem_finRange l)
    exact (List.map_inj_left.mp h1) m (List.mem_finRange m)
  apply LinearEquiv.toLinearMap_injective
  apply LinearMap.ext_on_range hspan
  intro l
  simp only [LinearEquiv.coe_coe]
  rw [ggFMat_apply hT hg, ggFMat_apply hT hg]
  simp only [hlm]

theorem ggFMat_eq_iff {T : Fin N → Vector (ZMod p) (N + 1)}
    (hT : GGFTable (RingHom.id (ZMod p)) T h 0 α) (hg : ∀ k w, g k w = w - α k w • h k)
    (hspan : Submodule.span (ZMod p) (Set.range h) = ⊤) (hind : LinearIndependent (ZMod p) h)
    {ws₁ ws₂ : List (Fin N)} :
    ggFMat T ws₁ = ggFMat T ws₂ ↔ (ws₁.map g).prod = (ws₂.map g).prod := by
  refine ⟨ggFMat_eq hT hg hspan, fun he => ?_⟩
  have hlm : ∀ l m : Fin N, (ggFWord T ws₁ (ggFUnit l.castSucc)).get m.castSucc =
      (ggFWord T ws₂ (ggFUnit l.castSucc)).get m.castSucc := by
    intro l
    have h1 : (ws₁.map g).prod (h l) = (ws₂.map g).prod (h l) := by rw [he]
    rw [ggFMat_apply hT hg, ggFMat_apply hT hg, ← sub_eq_zero, ← Finset.sum_sub_distrib] at h1
    simp only [← sub_smul, RingHom.id_apply] at h1
    intro m
    exact sub_eq_zero.mp ((Fintype.linearIndependent_iff.mp hind) _ h1 m)
  unfold ggFMat
  exact List.map_congr_left fun l _ => List.map_congr_left fun m _ => hlm l m

theorem ggF_conjWord_prod (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (t : Fin N × List (Fin N)) :
    ((ggConjWord t).map g).prod = (t.2.map g).prod * g t.1 * ((t.2.map g).prod)⁻¹ := by
  rw [ggConjWord, List.map_append, List.prod_append, List.map_cons, List.prod_cons,
    ggF_word_inv hg h2, mul_assoc]

theorem ggF_root_conj (hT : GGFTable φ T h 0 α) (hg : ∀ k w, g k w = w - α k w • h k)
    (h2 : ∀ k, α k (h k) = 2) (t : Fin N × List (Fin N)) (v : V) :
    α t.1 (((t.2.map g).prod)⁻¹ v) = ggFFun φ α (ggFC T t) v := by
  rw [ggFC, ← ggFFun_word hT hg, ← ggF_word_inv hg h2, ggFFun_unit]

theorem ggFPi_ne_zero (hind : LinearIndependent (ZMod p) h) {z : Vector R (N + 1)} {l : Fin N}
    (hl : φ (z.get l.castSucc) ≠ 0) : ggFPi φ h 0 z ≠ 0 := by
  intro h0
  rw [ggFPi_zero] at h0
  exact hl ((Fintype.linearIndependent_iff.mp hind) _ h0 l)

theorem ggFRefMat_eq_map (T : Fin N → Vector R (N + 1)) (t : Fin N × List (Fin N)) :
    ggFRefMat T t = (List.finRange N).map fun l => (List.finRange N).map fun m =>
      (if l = m then 1 else 0) - ggFDualAt T (ggFC T t) l * (ggFH T t).get m.castSucc := rfl

theorem ggResI_roots_indep {T : Fin N → Vector (ZMod p) (N + 1)}
    (hT : GGFTable (RingHom.id (ZMod p)) T h 0 α) {r : ℕ} (β : Fin r → Fin N)
    (K : Fin N → Fin r → ZMod p)
    (hK : ∀ a c : Fin r, ∑ l : Fin N, (T (β a)).get l.castSucc * K l c = if a = c then 1 else 0) :
    LinearIndependent (ZMod p) (fun a => α (β a)) := by
  rw [Fintype.linearIndependent_iff]
  intro c hc a
  have hab : ∀ b, ∑ l : Fin N, K l a * α (β b) (h l) = if b = a then 1 else 0 := by
    intro b
    rw [← hK b a]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [hT.1, RingHom.id_apply, mul_comm]
  have h1 : (∑ b, c b • α (β b)) (∑ l : Fin N, K l a • h l) =
      ∑ b, c b * ∑ l : Fin N, K l a * α (β b) (h l) := by
    rw [LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [LinearMap.smul_apply, smul_eq_mul, map_sum]
    simp only [map_smul, smul_eq_mul]
  rw [hc, LinearMap.zero_apply] at h1
  simp only [hab, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h1
  exact h1.symm

end FMat

end CFSG.StandardType
