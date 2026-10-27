module

public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosFacts
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallRankDefs

public section

namespace CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem pcy_getD_eq_getElem {α : Type*} {l : List α} {i : ℕ} {d : α}
    (h : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

private theorem pcy_getD_mem {α : Type*} {l : List α} {i : ℕ} {d : α}
    (h : i < l.length) : l.getD i d ∈ l := by
  rw [pcy_getD_eq_getElem h]
  exact List.mem_iff_getElem.mpr ⟨i, h, rfl⟩

private noncomputable def pcy_conjMulEquiv {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) : (V ≃ₗ[ZMod p] V) ≃* (W ≃ₗ[ZMod p] W) where
  toFun g := e.symm.trans (g.trans e)
  invFun h := e.trans (h.trans e.symm)
  left_inv g := by
    apply LinearEquiv.ext
    intro v
    simp [LinearEquiv.trans_apply]
  right_inv h := by
    apply LinearEquiv.ext
    intro w
    simp [LinearEquiv.trans_apply]
  map_mul' g h := by
    apply LinearEquiv.ext
    intro w
    simp [LinearEquiv.trans_apply]

private theorem pcy_conjMulEquiv_apply {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) :
    pcy_conjMulEquiv e g = e.symm.trans (g.trans e) := rfl

private theorem pcy_conjMulEquiv_apply_e {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) (v : V) :
    pcy_conjMulEquiv e g (e v) = e (g v) := by
  rw [pcy_conjMulEquiv_apply]
  simp [LinearEquiv.trans_apply]

private theorem pcy_conj_refl {p : ℕ} [Fact p.Prime] {V W : Type*}
    [AddCommGroup V] [Module (ZMod p) V] [AddCommGroup W] [Module (ZMod p) W]
    (e : V ≃ₗ[ZMod p] W) (g : V ≃ₗ[ZMod p] V) (h : V) (α : Module.Dual (ZMod p) V)
    (hg : ∀ v, g v = v - α v • h) :
    ∀ w, pcy_conjMulEquiv e g w = w - α (e.symm w) • e h := by
  intro w
  calc pcy_conjMulEquiv e g w = (e.symm.trans (g.trans e)) w := by
        rw [pcy_conjMulEquiv_apply]
    _ = e (g (e.symm w)) := by simp [LinearEquiv.trans_apply]
    _ = e (e.symm w - α (e.symm w) • h) := by rw [hg]
    _ = w - α (e.symm w) • e h := by
        rw [map_sub, map_smul, LinearEquiv.apply_symm_apply]

private theorem pcy_lt_of_cycle {s j n : ℕ} (hs : s ≤ 2) (hsj : s ≤ j)
    (hj : j < s + (n - 2)) : j < n := by
  omega

theorem cycleAt_models {P : Pt} [Fact P.p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod P.p) V] {n : ℕ}
    {e : V ≃ₗ[ZMod P.p] P.V} {h : Fin n → V} {α : Fin n → Module.Dual (ZMod P.p) V} {x ha : V}
    {αa : Module.Dual (ZMod P.p) V} (hM : P.Models e h α x ha αa) (r : Fin n → (V ≃ₗ[ZMod P.p] V))
    (t : V ≃ₗ[ZMod P.p] V) (hr : ∀ i v, r i v = v - α i v • h i) (ht : ∀ v, t v = v - αa v • ha)
    (s : ℕ) (hs : s ≤ 2) (S : Finset (Fin n)) (hS : ∀ i : Fin n, i ∈ S ↔ s ≤ (i : ℕ) ∧ (i : ℕ) < s + (n - 2))
    (hcyc : P.CycleAt s) :
    ¬ CFSG.StandardType.LR6JTriangleBalanced S h α r (CFSG.StandardType.lr6Group r t) := by
  intro hbal
  obtain ⟨hn, hlen, hex, hgen, hha, hαa⟩ := hM
  have hgen_h : ∀ i : Fin n, e (h i) = P.vec (P.gens.getD (i : ℕ) ⟨[], []⟩).h :=
    fun i => (hgen i).1
  have hgen_α : ∀ (i : Fin n) (w : V),
      α i w = P.dot (P.vec (P.gens.getD (i : ℕ) ⟨[], []⟩).f) (e w) :=
    fun i => (hgen i).2
  have hgetD_lt : ∀ i : Fin n, (i : ℕ) < P.gens.length := by
    intro i
    rw [hlen]
    exact Nat.lt_succ_of_lt i.isLt
  have hgen_mem : ∀ i : Fin n, pcy_conjMulEquiv e (r i) ∈ P.genSet := by
    intro i
    refine ⟨P.gens.getD (i : ℕ) ⟨[], []⟩, pcy_getD_mem (hgetD_lt i), ?_⟩
    intro w
    rw [pcy_conj_refl e (r i) (h i) (α i) (hr i)]
    rw [hgen_α i (e.symm w), hgen_h i, LinearEquiv.apply_symm_apply]
  have ht_mem : pcy_conjMulEquiv e t ∈ P.genSet := by
    refine ⟨P.gens.getD n ⟨[], []⟩, ?_, ?_⟩
    · apply pcy_getD_mem
      rw [hlen]
      exact Nat.lt_succ_self n
    · intro w
      rw [pcy_conj_refl e t ha αa ht]
      rw [hαa (e.symm w), hha, LinearEquiv.apply_symm_apply]
  have hsub1 : pcy_conjMulEquiv e '' (Set.range r ∪ {t}) ⊆ P.genSet := by
    rintro z ⟨y, hy, rfl⟩
    rcases hy with ⟨i, rfl⟩ | rfl
    · exact hgen_mem i
    · exact ht_mem
  have hsub2 : P.genSet ⊆ pcy_conjMulEquiv e '' (Set.range r ∪ {t}) := by
    intro z hz
    obtain ⟨r', hr'mem, hr'formula⟩ := hz
    obtain ⟨j0, hj0, hjeq⟩ := List.mem_iff_getElem.mp hr'mem
    have hjle : j0 < n + 1 := by rw [← hlen]; exact hj0
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hjle) with hjlt0 | hjeqjn
    · refine ⟨r ⟨j0, hjlt0⟩, Or.inl ⟨⟨j0, hjlt0⟩, rfl⟩, ?_⟩
      apply LinearEquiv.ext
      intro w
      rw [pcy_conj_refl e (r ⟨j0, hjlt0⟩) (h ⟨j0, hjlt0⟩) (α ⟨j0, hjlt0⟩) (hr ⟨j0, hjlt0⟩)]
      have hgetD : P.gens.getD j0 ⟨[], []⟩ = r' := by
        rw [pcy_getD_eq_getElem hj0, hjeq]
      rw [hgen_α ⟨j0, hjlt0⟩ (e.symm w), hgen_h ⟨j0, hjlt0⟩,
        LinearEquiv.apply_symm_apply, hgetD]
      exact (hr'formula w).symm
    · refine ⟨t, Or.inr rfl, ?_⟩
      apply LinearEquiv.ext
      intro w
      rw [pcy_conj_refl e t ha αa ht]
      have hopt : P.gens[n]? = some r' := by
        rw [← hjeqjn, List.getElem?_eq_getElem hj0, hjeq]
      have hgetD : P.gens.getD n ⟨[], []⟩ = r' := by
        rw [List.getD_eq_getElem?_getD, hopt]
        rfl
      rw [hαa (e.symm w), hha, LinearEquiv.apply_symm_apply, hgetD]
      exact (hr'formula w).symm
  have hset : pcy_conjMulEquiv e '' (Set.range r ∪ {t}) = P.genSet :=
    Set.Subset.antisymm hsub1 hsub2
  have hmap_eq : Subgroup.map (pcy_conjMulEquiv e) (CFSG.StandardType.lr6Group r t) = P.group := by
    rw [CFSG.StandardType.lr6Group, Pt.group, MonoidHom.map_closure]
    exact congrArg Subgroup.closure hset
  obtain ⟨-, ψ, rj, rj', j, j', hψmem, hsj, hjlt, hsj', hj'lt, hjne, hrj, hrj', htP, αtP,
    hψrjform, hαthtP, hnoncomm, hineq⟩ := hcyc
  have hjltn : j < s + (n - 2) := by simpa [hn] using hjlt
  have hj'ltn : j' < s + (n - 2) := by simpa [hn] using hj'lt
  have hjn : j < n := pcy_lt_of_cycle hs hsj hjltn
  have hj'n : j' < n := pcy_lt_of_cycle hs hsj' hj'ltn
  have hjneFin : (⟨j, hjn⟩ : Fin n) ≠ ⟨j', hj'n⟩ := by
    intro heq
    exact hjne (Fin.ext_iff.mp heq)
  have hjS : (⟨j, hjn⟩ : Fin n) ∈ S := (hS ⟨j, hjn⟩).mpr ⟨hsj, hjltn⟩
  have hj'S : (⟨j', hj'n⟩ : Fin n) ∈ S := (hS ⟨j', hj'n⟩).mpr ⟨hsj', hj'ltn⟩
  let E : (V ≃ₗ[ZMod P.p] V) ≃* (P.V ≃ₗ[ZMod P.p] P.V) := pcy_conjMulEquiv e
  let ψ_V : V ≃ₗ[ZMod P.p] V := E.symm ψ
  let ht_V : V := e.symm htP
  let αt_V : Module.Dual (ZMod P.p) V := αtP.comp e.toLinearMap
  have hψV : ψ_V ∈ CFSG.StandardType.lr6Group r t := by
    have hψmap : ψ ∈ Subgroup.map E (CFSG.StandardType.lr6Group r t) := by
      change ψ ∈ Subgroup.map (pcy_conjMulEquiv e) (CFSG.StandardType.lr6Group r t)
      rw [hmap_eq]
      exact hψmem
    obtain ⟨g, hgH, hgE⟩ := Subgroup.mem_map.mp hψmap
    have hg : g = ψ_V := by
      change g = E.symm ψ
      rw [← hgE]
      exact (MulEquiv.symm_apply_apply E g).symm
    rw [← hg]
    exact hgH
  have hE_rj : E (r ⟨j, hjn⟩) = rj := by
    change pcy_conjMulEquiv e (r ⟨j, hjn⟩) = rj
    apply LinearEquiv.ext
    intro w
    rw [pcy_conj_refl e (r ⟨j, hjn⟩) (h ⟨j, hjn⟩) (α ⟨j, hjn⟩) (hr ⟨j, hjn⟩)]
    rw [hgen_α ⟨j, hjn⟩ (e.symm w), hgen_h ⟨j, hjn⟩, LinearEquiv.apply_symm_apply]
    exact (hrj w).symm
  have hE_rj' : E (r ⟨j', hj'n⟩) = rj' := by
    change pcy_conjMulEquiv e (r ⟨j', hj'n⟩) = rj'
    apply LinearEquiv.ext
    intro w
    rw [pcy_conj_refl e (r ⟨j', hj'n⟩) (h ⟨j', hj'n⟩) (α ⟨j', hj'n⟩) (hr ⟨j', hj'n⟩)]
    rw [hgen_α ⟨j', hj'n⟩ (e.symm w), hgen_h ⟨j', hj'n⟩, LinearEquiv.apply_symm_apply]
    exact (hrj' w).symm
  have hαtV_apply : ∀ w, αt_V w = αtP (e w) := by
    intro w
    simp [αt_V]
  have he_htV : e ht_V = htP := by
    simp [ht_V]
  have hE : pcy_conjMulEquiv e (ψ_V * r ⟨j, hjn⟩ * ψ_V⁻¹) = ψ * rj * ψ⁻¹ := by
    change E (ψ_V * r ⟨j, hjn⟩ * ψ_V⁻¹) = ψ * rj * ψ⁻¹
    rw [map_mul, map_mul, map_inv]
    rw [show E ψ_V = ψ from MulEquiv.apply_symm_apply E ψ, hE_rj]
  have hformV : ∀ w, (ψ_V * r ⟨j, hjn⟩ * ψ_V⁻¹) w = w - αt_V w • ht_V := by
    intro w
    apply e.injective
    have h1 : e ((ψ_V * r ⟨j, hjn⟩ * ψ_V⁻¹) w) = (ψ * rj * ψ⁻¹) (e w) := by
      rw [← pcy_conjMulEquiv_apply_e e (ψ_V * r ⟨j, hjn⟩ * ψ_V⁻¹) w]
      rw [hE]
    rw [h1, hψrjform (e w), map_sub, map_smul, hαtV_apply w, he_htV]
  have hαthtV : αt_V ht_V = 2 := by
    rw [hαtV_apply, he_htV, hαthtP]
  have hnoncommV : ψ_V * r ⟨j, hjn⟩ * ψ_V⁻¹ * r ⟨j', hj'n⟩ ≠
      r ⟨j', hj'n⟩ * (ψ_V * r ⟨j, hjn⟩ * ψ_V⁻¹) := by
    intro heq
    apply hnoncomm
    have h := congrArg E heq
    dsimp only [ψ_V] at h
    simp only [map_mul, map_inv, MulEquiv.apply_symm_apply, hE_rj, hE_rj'] at h
    exact h
  have hcontr : P.dot (P.vec (P.gens.getD j ⟨[], []⟩).f) (P.vec (P.gens.getD j' ⟨[], []⟩).h) *
      P.dot (P.vec (P.gens.getD j' ⟨[], []⟩).f) htP * αtP (P.vec (P.gens.getD j ⟨[], []⟩).h) =
      P.dot (P.vec (P.gens.getD j' ⟨[], []⟩).f) (P.vec (P.gens.getD j ⟨[], []⟩).h) *
      αtP (P.vec (P.gens.getD j' ⟨[], []⟩).h) * P.dot (P.vec (P.gens.getD j ⟨[], []⟩).f) htP := by
    have hball := hbal ⟨j, hjn⟩ hjS ⟨j', hj'n⟩ hj'S hjneFin ψ_V hψV ht_V αt_V hformV hαthtV hnoncommV
    simpa only [hαtV_apply, he_htV, hgen_α, hgen_h, LinearEquiv.apply_symm_apply] using hball
  exact hineq hcontr

end CFSG.TwoNodeSmall
