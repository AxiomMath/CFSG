module

public import CFSG.Quasithin.Background.SmithB45MatIndFlag
public import CFSG.Quasithin.Background.SmithB45MatRep

public section

namespace CFSG.Quasithin.B45Mat.Ind

open CFSG.QuasithinUnique.Setup.X3E

@[expose] def blkProj (m d k : ℕ) : Vec (m * d) →ₗ[ZMod 2] Vec d where
  toFun u c := if h : d * k + c.val < m * d then u ⟨d * k + c.val, h⟩ else 0
  map_add' u v := by
    funext c
    simp only [Pi.add_apply]
    split_ifs <;> simp
  map_smul' a u := by
    funext c
    simp only [Pi.smul_apply, RingHom.id_apply]
    split_ifs <;> simp

theorem testBit_shift_block {d Y : ℕ} (hY : Y < 2 ^ d) (a k c : ℕ) (hc : c < d) :
    (Y <<< (d * a)).testBit (d * k + c) = (decide (k = a) && Y.testBit c) := by
  rw [Nat.testBit_shiftLeft]
  rcases lt_trichotomy k a with h | rfl | h
  · have h1 : ¬ d * a ≤ d * k + c := by
      have : d * (k + 1) ≤ d * a := Nat.mul_le_mul_left d h
      rw [Nat.mul_succ] at this
      omega
    simp [h1, Nat.ne_of_lt h]
  · simp
  · have h1 : d * a ≤ d * k + c := by
      have : d * a ≤ d * k := Nat.mul_le_mul_left d h.le
      omega
    have h2 : d ≤ d * k + c - d * a := by
      have : d * (a + 1) ≤ d * k := Nat.mul_le_mul_left d h
      rw [Nat.mul_succ] at this
      omega
    have h3 : Y.testBit (d * k + c - d * a) = false :=
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hY (Nat.pow_le_pow_right (by norm_num) h2))
    simp [h1, h3, Nat.ne_of_gt h]

theorem blkProj_shift {m d Y : ℕ} (hY : Y < 2 ^ d) {a k : ℕ} (hk : k < m) :
    blkProj m d k (toVec (m * d) (Y <<< (d * a))) = if k = a then toVec d Y else 0 := by
  funext c
  have hlt : d * k + c.val < m * d := by
    have : d * (k + 1) ≤ d * m := Nat.mul_le_mul_left d hk
    rw [Nat.mul_succ] at this
    have := c.isLt
    rw [Nat.mul_comm m d]
    omega
  change (if h : d * k + c.val < m * d then toVec (m * d) (Y <<< (d * a)) ⟨d * k + c.val, h⟩
    else 0) = _
  simp only [hlt, ↓reduceDIte, toVec_apply]
  rw [testBit_shift_block hY a k c.val c.isLt]
  split_ifs with h1 h2 <;> simp_all [toVec_apply]

theorem single_eq_toVec_shift {m d : ℕ} (j : Fin (m * d)) :
    (Pi.single j (1 : ZMod 2) : Vec (m * d)) =
      toVec (m * d) ((1 <<< (j.val % d)) <<< (d * (j.val / d))) := by
  rw [← Nat.shiftLeft_add, Nat.mod_add_div, toVec_one_shiftLeft]

section Ind

variable {G X : Type*} [Group G] [AddCommGroup X] [Module (ZMod 2) X]
  (ρ : Representation (ZMod 2) G X)

@[expose] noncomputable def indMap (m d : ℕ) (t : ℕ → G) (ψ : Vec d →ₗ[ZMod 2] X) :
    Vec (m * d) →ₗ[ZMod 2] X :=
  ∑ k ∈ Finset.range m, (ρ (t k)) ∘ₗ ψ ∘ₗ blkProj m d k

@[expose] def indColsG (m d : ℕ) (π : ℕ → ℕ) (Xcol : ℕ → List ℕ) : List ℕ :=
  (List.range (m * d)).map fun j => (Xcol (j / d)).getD (j % d) 0 <<< (d * π (j / d))

theorem indMap_shift {m d : ℕ} (t : ℕ → G) (ψ : Vec d →ₗ[ZMod 2] X) {Y : ℕ} (hY : Y < 2 ^ d)
    {a : ℕ} (ha : a < m) :
    indMap ρ m d t ψ (toVec (m * d) (Y <<< (d * a))) = ρ (t a) (ψ (toVec d Y)) := by
  unfold indMap
  rw [LinearMap.coe_sum, Finset.sum_apply, Finset.sum_eq_single a]
  · rw [LinearMap.comp_apply, LinearMap.comp_apply, blkProj_shift hY ha]
    simp
  · intro k hk hka
    rw [LinearMap.comp_apply, LinearMap.comp_apply, blkProj_shift hY (Finset.mem_range.1 hk)]
    simp [hka]
  · intro h
    exact absurd (Finset.mem_range.2 ha) h

theorem indMap_lin {m d : ℕ} (t : ℕ → G) (ψ : Vec d →ₗ[ZMod 2] X) {g : G} {π : ℕ → ℕ}
    {Xcol : ℕ → List ℕ} (hπ : ∀ k < m, π k < m)
    (hX : ∀ k < m, ∀ c < d, (Xcol k).getD c 0 < 2 ^ d)
    (hrel : ∀ k < m, ∀ v, ρ g (ρ (t k) (ψ v)) = ρ (t (π k)) (ψ (lin d (Xcol k) v)))
    (v : Vec (m * d)) :
    indMap ρ m d t ψ (lin (m * d) (indColsG m d π Xcol) v) = ρ g (indMap ρ m d t ψ v) := by
  suffices h : (indMap ρ m d t ψ).comp (lin (m * d) (indColsG m d π Xcol)) =
      (ρ g).comp (indMap ρ m d t ψ) from LinearMap.congr_fun h v
  refine linearMap_ext_basis fun j => ?_
  have hd : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · subst h
      exact absurd j.isLt (by simp)
    · exact h
  have hk : j.val / d < m := (Nat.div_lt_iff_lt_mul hd).2 j.isLt
  have hc : j.val % d < d := Nat.mod_lt _ hd
  rw [LinearMap.comp_apply, LinearMap.comp_apply, lin_single, indColsG,
    getD_map_range _ _ j.isLt, indMap_shift ρ t ψ (hX _ hk _ hc) (hπ _ hk),
    single_eq_toVec_shift j, indMap_shift ρ t ψ (show 1 <<< (j.val % d) < 2 ^ d by
      rw [Nat.one_shiftLeft]; exact Nat.pow_lt_pow_right (by norm_num) hc) hk, hrel _ hk,
    toVec_one_shiftLeft d _ hc, lin_single]

theorem isInvariant_of_gens [Finite G] {gen : Bool → G}
    (hgen : Subgroup.closure (Set.range gen) = ⊤) {U : Submodule (ZMod 2) X}
    (hU : ∀ z, ∀ u ∈ U, ρ (gen z) u ∈ U) : ∀ g, ∀ u ∈ U, ρ g u ∈ U :=
  forall_of_closure hgen (fun g => ∀ u ∈ U, ρ g u ∈ U)
    (fun u hu => by rw [map_one, Module.End.one_apply]; exact hu)
    (fun s ⟨z, hz⟩ => hz ▸ hU z)
    (fun g h hg hh u hu => by rw [map_mul, Module.End.mul_apply]; exact hg _ (hh u hu))

theorem rep_injective (g : G) : Function.Injective (ρ g) := fun x y h => by
  have h1 := congrArg (ρ g⁻¹) h
  rwa [← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one,
    Module.End.one_apply, Module.End.one_apply] at h1

theorem indMap_surjective [Finite G] {gen : Bool → G}
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hirr : ∀ U : Submodule (ZMod 2) X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {m d : ℕ} (t : ℕ → G) (ψ : Vec d →ₗ[ZMod 2] X) {K : Bool → List ℕ}
    (hK : ∀ z v, indMap ρ m d t ψ (lin (m * d) (K z) v) = ρ (gen z) (indMap ρ m d t ψ v))
    (hψ : ψ ≠ 0) (hm : 0 < m) : Function.Surjective (indMap ρ m d t ψ) := by
  set U := LinearMap.range (indMap ρ m d t ψ)
  have hU : ∀ g, ∀ u ∈ U, ρ g u ∈ U := by
    refine isInvariant_of_gens ρ hgen fun z u hu => ?_
    obtain ⟨v, rfl⟩ := hu
    exact ⟨_, hK z v⟩
  rcases hirr U hU with h | h
  · exfalso
    apply hψ
    refine LinearMap.ext fun v => ?_
    obtain ⟨Y, hY, rfl⟩ := exists_toVec v
    have h1 : indMap ρ m d t ψ (toVec (m * d) (Y <<< (d * 0))) ∈ U := ⟨_, rfl⟩
    rw [h, Submodule.mem_bot, indMap_shift ρ t ψ hY hm] at h1
    exact rep_injective ρ (t 0) (h1.trans (map_zero _).symm)
  · exact LinearMap.range_eq_top.1 h

theorem finrank_le_of_coind [Finite G] [FiniteDimensional (ZMod 2) X] {gen : Bool → G}
    (hgen : Subgroup.closure (Set.range gen) = ⊤)
    (hirr : ∀ U : Submodule (ZMod 2) X, (∀ g, ∀ u ∈ U, ρ g u ∈ U) → U = ⊥ ∨ U = ⊤)
    {m : ℕ} (hm : 0 < m) (t : ℕ → G) (π : Bool → ℕ → ℕ) (hπ : ∀ z, ∀ k < m, π z k < m)
    (hπinj : ∀ z, ∀ k < m, ∀ k' < m, π z k = π z k' → k = k')
    (l : X →ₗ[ZMod 2] ZMod 2) (hl : l ≠ 0)
    (hrel : ∀ z, ∀ k < m, ∀ x, l (ρ (t (π z k))⁻¹ (ρ (gen z) x)) = l (ρ (t k)⁻¹ x)) :
    Module.finrank (ZMod 2) X ≤ m := by
  let Ψ : X →ₗ[ZMod 2] (Fin m → ZMod 2) := LinearMap.pi fun k : Fin m => l ∘ₗ ρ (t k)⁻¹
  have hsurj : ∀ z, ∀ k' < m, ∃ k < m, π z k = k' := by
    intro z k' hk'
    let f : Fin m → Fin m := fun k => ⟨π z k, hπ z k k.isLt⟩
    have hf : Function.Injective f := fun a b hab =>
      Fin.ext (hπinj z a a.isLt b b.isLt (congrArg Fin.val hab))
    obtain ⟨k, hk⟩ := (Finite.injective_iff_surjective.1 hf) ⟨k', hk'⟩
    exact ⟨k, k.isLt, congrArg Fin.val hk⟩
  have hker : ∀ g, ∀ x ∈ LinearMap.ker Ψ, ρ g x ∈ LinearMap.ker Ψ := by
    refine isInvariant_of_gens ρ hgen fun z x hx => ?_
    rw [LinearMap.mem_ker] at hx ⊢
    funext k'
    obtain ⟨k, hk, hkk⟩ := hsurj z k'.val k'.isLt
    obtain rfl : k' = ⟨π z k, hπ z k hk⟩ := Fin.ext hkk.symm
    have h1 := congrFun hx ⟨k, hk⟩
    change l (ρ (t (π z k))⁻¹ (ρ (gen z) x)) = 0
    rw [hrel z k hk]
    exact h1
  rcases hirr _ hker with h | h
  · have hinj : Function.Injective Ψ := fun x y hxy => by
      have h1 : x - y ∈ LinearMap.ker Ψ := by
        rw [LinearMap.mem_ker, map_sub]
        exact sub_eq_zero.2 hxy
      rw [h, Submodule.mem_bot] at h1
      exact sub_eq_zero.1 h1
    have h1 := LinearMap.finrank_le_finrank_of_injective hinj
    rwa [Module.finrank_fin_fun] at h1
  · exfalso
    apply hl
    refine LinearMap.ext fun x => ?_
    have h1 : ρ (t 0) x ∈ LinearMap.ker Ψ := by rw [h]; trivial
    have h2 := congrFun (LinearMap.mem_ker.1 h1) ⟨0, hm⟩
    change l (ρ (t 0)⁻¹ (ρ (t 0) x)) = 0 at h2
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply] at h2

end Ind

end CFSG.Quasithin.B45Mat.Ind
