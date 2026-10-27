module

public import CFSG.Quasithin.Background.C35InspL45B
public import CFSG.Quasithin.Background.C48PfFourModPfA8
public import CFSG.Quasithin.Background.C35InspL45A
public import CFSG.Quasithin.Background.C48PfFourModPfMat

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open scoped commutatorElement
open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.C48Pf.FMod

variable {A : Type} [Group A] [Finite A]

omit [Finite A] in
theorem le_normalizer_of_comm {V P₀ : Subgroup A} (hVcomm : ⁅V, P₀⁆ = V) :
    P₀ ≤ Subgroup.normalizer (V : Set A) := by
  have key : ∀ x ∈ P₀, ∀ v ∈ V, x * v * x⁻¹ ∈ V := by
    intro x hx v hv
    have h1 : ⁅v, x⁆ ∈ V := hVcomm ▸ Subgroup.commutator_mem_commutator hv hx
    have h2 : ⁅x, v⁆ ∈ V := by
      rw [← commutatorElement_inv]
      exact V.inv_mem h1
    have e : x * v * x⁻¹ = ⁅x, v⁆ * v := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact V.mul_mem h2 hv
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro v
  refine ⟨key x hx v, fun hv => ?_⟩
  have h1 := key x⁻¹ (P₀.inv_mem hx) _ hv
  have e : x⁻¹ * (x * v * x⁻¹) * x⁻¹⁻¹ = v := by group
  rwa [e] at h1

theorem le_pCoreOf_of_data {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) :
    V ≤ pCoreOf 2 M₀ ∧ pCoreOf 2 M₀ ≤ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hMY : M₀ ≤ Y := hD.eq_perfectCore ▸ perfectCore_le Y
  have hYN : Y ≤ Subgroup.normalizer (M₀ : Set A) := by
    rw [hD.eq_perfectCore]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore Y)
  refine ⟨?_, ?_⟩
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hD.V_le ?_ ?_
    · exact le_normalizer_of_comm hD.V_comm
    · exact fun x => ⟨1, Subtype.ext (by simpa using hD.V_elem.2 x x.2)⟩
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.map_subtype_le _).trans hMY) ?_
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀)
    exact hYN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M₀)

section Config

variable {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K) {n a m : ℕ}
  (h : a + m ≤ n) (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2))
  (α : ↥M₀ →* SpecialLinearGroup (Fin m) (ZMod 2)) (hker : α.ker = CFSG.pCore 2 ↥M₀)
  (hblk : ∀ x : ↥M₀,
    blkAt a m h ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) =
        ((α x : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) ∧
    BlockForm a m ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)))
  (hcross : ∀ (k l : Fin n) (hkl : IsCross a m k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
    θ ⟨p, hM₀K p.2⟩ = SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2))

include hD hker hblk hcross in
theorem data_of_mem {v : A} (hv : v ∈ V) :
    BlockForm a m ((θ ⟨v, hM₀K (hD.V_le hv)⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) ∧
    blkAt a m h ((θ ⟨v, hM₀K (hD.V_le hv)⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1 ∧
    CommCross a m ((θ ⟨v, hM₀K (hD.V_le hv)⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) ∧
    ∀ i, ((θ ⟨v, hM₀K (hD.V_le hv)⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) i i = 1 := by
  obtain ⟨hVO, hOO⟩ := le_pCoreOf_of_data hD
  set x : ↥M₀ := ⟨v, hD.V_le hv⟩ with hx
  have hx1 : α x = 1 := by
    rw [← MonoidHom.mem_ker, hker]
    obtain ⟨y, hy, hyv⟩ := hVO hv
    have : y = x := Subtype.ext hyv
    rw [← this]
    exact hy
  obtain ⟨hb1, hbf⟩ := hblk x
  rw [hx1, Matrix.SpecialLinearGroup.coe_one] at hb1
  set w := ((θ ⟨v, hM₀K (hD.V_le hv)⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2)) with hw
  refine ⟨hbf, hb1, fun k l hkl => ?_, fun i => ?_⟩
  · obtain ⟨p, hp, hpT⟩ := hcross k l hkl
    have hpY : (p : A) ∈ pCoreOf 2 Y := hOO ⟨p, by exact hp, rfl⟩
    have hcomm : (p : A) * v = v * p :=
      Subgroup.mem_centralizer_iff.1 (hD.V_le_center hv).2 _ hpY
    have h1 : θ ⟨p, hM₀K p.2⟩ * θ ⟨v, hM₀K (hD.V_le hv)⟩ =
        θ ⟨v, hM₀K (hD.V_le hv)⟩ * θ ⟨p, hM₀K p.2⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    rw [hpT] at h1
    have h2 := congrArg (fun z : SpecialLinearGroup (Fin n) (ZMod 2) =>
      (z : Matrix (Fin n) (Fin n) (ZMod 2))) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection] at h2
    exact h2.symm
  · by_cases hi : (i : ℕ) < a
    · rw [hbf.2.2.1 i i hi hi, ite_eq_left rfl]
    · by_cases hi' : (i : ℕ) < a + m
      · have := congrFun (congrFun hb1 ⟨(i : ℕ) - a, by omega⟩) ⟨(i : ℕ) - a, by omega⟩
        rw [blkAt_apply, Matrix.one_apply_eq] at this
        have e : (⟨a + ((i : ℕ) - a), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
        rwa [e] at this
      · rw [hbf.2.2.2 i i (by omega) (by omega), ite_eq_left rfl]

include hD hker hblk hcross in
theorem false_of_middle (hθ : Function.Injective θ) (ha : 0 < a) (hm : 1 ≤ m) (hamn : a + m < n) :
    False := by
  apply hD.V_ne
  rw [← hD.V_comm, eq_bot_iff, Subgroup.commutator_le]
  intro v hv x hx
  obtain ⟨hbf, -, hcc, hd⟩ := data_of_mem hD hM₀K h θ α hker hblk hcross hv
  have hsh : Shape (a + m) a ((θ ⟨v, hM₀K (hD.V_le hv)⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) := by
    refine ⟨fun i j hj => ?_, fun i j hi => ?_⟩
    · refine col_std hcc hd j ?_ i
      by_cases hja : (j : ℕ) < a
      · exact Or.inl ⟨hja, hm, by omega⟩
      · exact Or.inr ⟨by omega, hj, hamn⟩
    · refine row_std hcc hd i ?_ j
      by_cases hia : (i : ℕ) < a + m
      · exact Or.inl ⟨hi, hia, ha⟩
      · exact Or.inr ⟨by omega, hm⟩
  have h1 := commute_of_middle (hblk ⟨x, hx⟩).2 hsh
  have h2 : θ ⟨x, hM₀K hx⟩ * θ ⟨v, hM₀K (hD.V_le hv)⟩ =
      θ ⟨v, hM₀K (hD.V_le hv)⟩ * θ ⟨x, hM₀K hx⟩ := by
    apply Subtype.ext
    simp only [Matrix.SpecialLinearGroup.coe_mul]
    exact h1
  rw [← map_mul, ← map_mul] at h2
  have h3 := congrArg Subtype.val (hθ h2)
  simp only [Subgroup.coe_mul] at h3
  rw [Subgroup.mem_bot, commutatorElement_def, show v * x = x * v from h3.symm]
  group

end Config

theorem eq_top_of_transvection_invariant {m : ℕ} (hm : 2 ≤ m)
    (W : AddSubgroup (Fin m → ZMod 2)) (hW : W ≠ ⊥)
    (hinv : ∀ r s : Fin m, r ≠ s → ∀ w ∈ W, (1 + Matrix.single r s (1 : ZMod 2)) *ᵥ w ∈ W) :
    W = ⊤ := by
  have key : ∀ r s : Fin m, r ≠ s → ∀ w ∈ W, Pi.single r (w s) ∈ W := by
    intro r s hrs w hw
    have h1 := W.sub_mem (hinv r s hrs w hw) hw
    rw [Matrix.add_mulVec, Matrix.one_mulVec, add_sub_cancel_left, Matrix.single_mulVec,
      one_mul] at h1
    exact h1
  obtain ⟨w, hw0⟩ := (AddSubgroup.ne_bot_iff_exists_ne_zero).1 hW
  obtain ⟨s, hs⟩ : ∃ s, (w : Fin m → ZMod 2) s ≠ 0 := by
    by_contra h
    exact hw0 (Subtype.ext (funext fun s => by_contra fun hs => h ⟨s, hs⟩))
  have hs1 : (w : Fin m → ZMod 2) s = 1 := by
    rcases zmod2_cases ((w : Fin m → ZMod 2) s) with h | h
    · exact absurd h hs
    · exact h
  have hall : ∀ r : Fin m, (Pi.single r 1 : Fin m → ZMod 2) ∈ W := by
    intro r
    by_cases hr : r = s
    · subst hr
      obtain ⟨t, ht⟩ : ∃ t : Fin m, t ≠ r := by
        by_cases h0 : (r : ℕ) = 0
        · exact ⟨⟨1, by omega⟩, fun h => by rw [← h] at h0; simp at h0⟩
        · exact ⟨⟨0, by omega⟩, fun h => h0 (by rw [← h])⟩
      have h1 := key t r ht _ w.2
      rw [hs1] at h1
      have h2 := key r t (Ne.symm ht) _ h1
      simpa using h2
    · have h1 := key r s hr _ w.2
      rwa [hs1] at h1
  rw [eq_top_iff]
  intro x _
  rw [← Finset.univ_sum_single x]
  refine AddSubgroup.sum_mem _ fun k _ => ?_
  rcases zmod2_cases (x k) with h | h
  · rw [h, Pi.single_zero]
    exact W.zero_mem
  · rw [h]
    exact hall k

omit [Finite A] in
theorem isNaturalSection_of_bij {M₀ V : Subgroup A} {N : Subgroup ↥M₀} {m : ℕ}
    (hMV : M₀ ≤ Subgroup.normalizer (V : Set A))
    (α : ↥M₀ →* SpecialLinearGroup (Fin m) (ZMod 2)) (hα : Function.Surjective α)
    (hker : α.ker = N) (β : ↥V →* Multiplicative (Fin m → ZMod 2)) (hβ : Function.Bijective β)
    (hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = ((α a : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u)) :
    IsNaturalSection M₀ V ⊥ N (StatedSL m (ZMod 2)) := by
  refine ⟨hMV, (specialLinearGroupEquivStatedSL m (ZMod 2)).toMonoidHom.comp α,
    (specialLinearGroupEquivStatedSL m (ZMod 2)).surjective.comp hα, ?_, β, hβ.2, ?_,
    fun a u v huv => hequiv a u v huv⟩
  · rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · rw [Subgroup.bot_subgroupOf, (MonoidHom.ker_eq_bot_iff β).2 hβ.1]

omit [Finite A] in
theorem isNaturalSection_of_bij_dual {M₀ V : Subgroup A} {N : Subgroup ↥M₀} {m : ℕ}
    (hMV : M₀ ≤ Subgroup.normalizer (V : Set A))
    (α : ↥M₀ →* SpecialLinearGroup (Fin m) (ZMod 2)) (hα : Function.Surjective α)
    (hker : α.ker = N) (β : ↥V →* Multiplicative (Fin m → ZMod 2)) (hβ : Function.Bijective β)
    (hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = (((α a)⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2))ᵀ *ᵥ Multiplicative.toAdd (β u)) :
    IsNaturalSection M₀ V ⊥ N (StatedSL m (ZMod 2)) := by
  refine isNaturalSection_of_bij hMV
    ((CFSG.Quasithin.JonesParshall.invTransposeSL m (ZMod 2)).toMonoidHom.comp α)
    ((CFSG.Quasithin.JonesParshall.invTransposeSL m (ZMod 2)).surjective.comp hα) ?_ β hβ ?_
  · rw [← hker]
    ext x
    simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff]
  · intro a u v huv
    rw [hequiv a u v huv]
    rfl

theorem eq_of_colC {n c : ℕ} {w₁ w₂ : Matrix (Fin n) (Fin n) (ZMod 2)} (h₁ : Shape c c w₁)
    (h₂ : Shape c c w₂) (hcol : ∀ j : Fin n, c ≤ (j : ℕ) → colC w₁ j = colC w₂ j) : w₁ = w₂ := by
  ext i j
  by_cases hj : (j : ℕ) < c
  · rw [h₁.1 i j hj, h₂.1 i j hj]
  · have := congrFun (hcol j (by omega)) i
    rw [colC_apply, colC_apply] at this
    exact sub_left_injective this

theorem eq_of_rowC {n r : ℕ} {w₁ w₂ : Matrix (Fin n) (Fin n) (ZMod 2)} (h₁ : Shape r r w₁)
    (h₂ : Shape r r w₂) (hrow : ∀ i : Fin n, (i : ℕ) < r → rowC w₁ i = rowC w₂ i) : w₁ = w₂ := by
  ext i j
  by_cases hi : r ≤ (i : ℕ)
  · rw [h₁.2 i j hi, h₂.2 i j hi]
  · have := congrFun (hrow i (by omega)) j
    rw [rowC_apply, rowC_apply] at this
    exact sub_left_injective this

omit [Finite A] in
theorem isMaxParabolic2_of_flag {K Y : Subgroup A} (hc0 : Subgroup.center ↥K = ⊥) {n : ℕ}
    (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hθ : Function.Bijective θ)
    (hpar : IsParabolic2 K Y) (hYK : Y ≠ K) {c : ℕ} (hc : 1 ≤ c ∧ c < n)
    (hQ : img θ Y = flagStabilizer n (ZMod 2) {c}) : IsMaxParabolic2 K Y := by
  have hZ := centerOf_eq_bot hc0
  have hker : θ.ker ≤ Subgroup.center ↥K := by
    rw [(MonoidHom.ker_eq_bot_iff θ).2 hθ.1]
    exact bot_le
  refine ⟨hpar, hYK, fun Q hQpar hQK hYQ => ?_⟩
  have hQK' : Q ≤ K := hQpar.1
  have hYQ' : img θ Y ≤ img θ Q := Subgroup.map_mono fun x hx => hYQ hx
  have hB : upperTriangular n (ZMod 2) ≤ img θ Q := by
    refine le_trans ?_ hYQ'
    rw [hQ]
    exact upperTriangular_le_flagStabilizer _
  obtain ⟨hQJ, -⟩ := borel_overgroups (img θ Q) hB
  obtain ⟨-, hIu⟩ := borel_overgroups (flagStabilizer n (ZMod 2) {c})
    (upperTriangular_le_flagStabilizer _)
  have hcuts := hIu {c} (by simpa using hc) rfl
  have hJsub : borelOvergroupCuts (img θ Q) ⊆ {c} := by
    intro d hd
    obtain ⟨h1, h2, hr⟩ := hd
    rw [hcuts]
    refine ⟨h1, h2, fun hmem => hr (hYQ' (hQ ▸ hmem))⟩
  rcases Set.subset_singleton_iff_eq.1 hJsub with h | h
  · exfalso
    apply hQK
    refine le_antisymm hQK' fun x hx => ?_
    have : θ ⟨x, hx⟩ ∈ img θ Q := by
      rw [hQJ, h, flagStabilizer_empty]
      exact Subgroup.mem_top _
    exact mem_of_img_mem hker (hZ ▸ bot_le) this
  · refine le_antisymm (fun x hx => ?_) hYQ
    have : θ ⟨x, hQK' hx⟩ ∈ img θ Y := by
      rw [hQ, ← h, ← hQJ]
      exact ⟨⟨x, hQK' hx⟩, hx, rfl⟩
    exact mem_of_img_mem hker (hZ ▸ bot_le) this

section Concl2a

variable {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K) {n : ℕ}
  (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hθ : Function.Bijective θ)

omit [Finite A] in
@[expose] def mV (v : ↥V) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  ((θ ⟨v, hM₀K (hD.V_le v.2)⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2))

omit [Finite A] in
theorem mV_mul (u v : ↥V) : mV hD hM₀K θ (u * v) = mV hD hM₀K θ u * mV hD hM₀K θ v := by
  simp only [mV]
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul]
  rfl

omit [Finite A] in
theorem mV_one : mV hD hM₀K θ 1 = 1 := by
  simp only [mV]
  rw [show (⟨((1 : ↥V) : A), hM₀K (hD.V_le (1 : ↥V).2)⟩ : ↥K) = 1 from rfl, map_one,
    Matrix.SpecialLinearGroup.coe_one]

omit [Finite A] in
theorem mV_conj (a : ↥M₀) (u v : ↥V) (huv : (v : A) = a * u * (a : A)⁻¹) :
    mV hD hM₀K θ v = ((θ ⟨a, hM₀K a.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) * mV hD hM₀K θ u *
        (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) := by
  simp only [mV]
  rw [← Matrix.SpecialLinearGroup.coe_mul, ← Matrix.SpecialLinearGroup.coe_mul, ← map_inv,
    ← map_mul, ← map_mul]
  congr 3

end Concl2a

theorem eq_of_restrictBlk {n m : ℕ} (h0 : 0 + m ≤ n) {w₁ w₂ : Fin n → ZMod 2}
    (h₁ : ∀ i : Fin n, m ≤ (i : ℕ) → w₁ i = 0) (h₂ : ∀ i : Fin n, m ≤ (i : ℕ) → w₂ i = 0)
    (h : restrictBlk 0 m h0 w₁ = restrictBlk 0 m h0 w₂) : w₁ = w₂ := by
  funext i
  by_cases hi : (i : ℕ) < m
  · have := congrFun h ⟨i, hi⟩
    simp only [restrictBlk] at this
    have e : (⟨0 + (i : ℕ), by omega⟩ : Fin n) = i := Fin.ext (by simp)
    rwa [e] at this
  · rw [h₁ i (by omega), h₂ i (by omega)]

theorem shape_one {n c r : ℕ} : Shape c r (1 : Matrix (Fin n) (Fin n) (ZMod 2)) :=
  ⟨fun _ _ _ => Matrix.one_apply, fun _ _ _ => Matrix.one_apply⟩

theorem shape_of_blockForm {n m : ℕ} (h0 : 0 + m ≤ n) {w : Matrix (Fin n) (Fin n) (ZMod 2)}
    (hw : BlockForm 0 m w) (hb : blkAt 0 m h0 w = 1) : Shape m m w := by
  refine ⟨fun i j hj => ?_, fun i j hi => ?_⟩
  · by_cases hi : (i : ℕ) < m
    · have := congrFun (congrFun hb ⟨i, hi⟩) ⟨j, hj⟩
      rw [blkAt_apply, Matrix.one_apply] at this
      have ei : (⟨0 + (i : ℕ), by omega⟩ : Fin n) = i := Fin.ext (by simp)
      have ej : (⟨0 + (j : ℕ), by omega⟩ : Fin n) = j := Fin.ext (by simp)
      rw [ei, ej] at this
      rw [this]
      exact if_congr (by rw [Fin.mk.injEq, Fin.ext_iff]) rfl rfl
    · rw [hw.2.1 i j (by omega) (by omega), ite_eq_right_iff.2 fun h => absurd (h ▸ hj) (by omega)]
  · by_cases hj : (j : ℕ) < m
    · rw [hw.2.1 i j (by omega) (by omega), ite_eq_right_iff.2 fun h => absurd (h ▸ hj) (by omega)]
    · exact hw.2.2.2 i j (by omega) (by omega)

theorem concl2a_nat {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    (hc0 : Subgroup.center ↥K = ⊥) {n m : ℕ} (hn : 4 ≤ n) (hmn : m + 1 = n) (h0 : 0 + m ≤ n)
    (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hθ : Function.Bijective θ)
    (α : ↥M₀ →* SpecialLinearGroup (Fin m) (ZMod 2)) (hαs : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥M₀)
    (hblk : ∀ x : ↥M₀,
      blkAt 0 m h0 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) ∧
      BlockForm 0 m ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)))
    (hcross : ∀ (k l : Fin n) (hkl : IsCross 0 m k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
      θ ⟨p, hM₀K p.2⟩ = SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2))
    (hQ : img θ Y = flagStabilizer n (ZMod 2) {m}) :
    C35Concl2a n K Y M₀ V := by
  classical
  have hm3 : 3 ≤ m := by omega
  set j₀ : Fin n := ⟨m, by omega⟩ with hj₀
  have hsh : ∀ v : ↥V, Shape m m (mV hD hM₀K θ v) := fun v => by
    obtain ⟨-, -, hcc, hd⟩ := data_of_mem hD hM₀K h0 θ α hker hblk hcross v.2
    exact ⟨fun i j hj => col_std hcc hd j (Or.inr ⟨by omega, by omega, by omega⟩) i,
      fun i j hi => row_std hcc hd i (Or.inr ⟨by omega, by omega⟩) j⟩
  have hcol0 : ∀ (v : ↥V) (i : Fin n), m ≤ (i : ℕ) → colC (mV hD hM₀K θ v) j₀ i = 0 :=
    fun v i hi => colC_eq_zero (hsh v) j₀ i hi
  let β : ↥V →* Multiplicative (Fin m → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (restrictBlk 0 m h0 (colC (mV hD hM₀K θ v) j₀))
      map_one' := by
        rw [mV_one]
        apply Multiplicative.toAdd.injective
        funext i
        simp [colC, restrictBlk]
      map_mul' := fun u v => by
        rw [mV_mul, colC_mul (hsh u) (hsh v)]
        rfl }
  have hβv : ∀ v, Multiplicative.toAdd (β v) = restrictBlk 0 m h0 (colC (mV hD hM₀K θ v) j₀) :=
    fun v => rfl
  have hinvM : ∀ x : ↥M₀, ((θ ⟨x, hM₀K x.2⟩)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) =
      θ ⟨(x⁻¹ : ↥M₀), hM₀K x⁻¹.2⟩ := fun x => by rw [← map_inv]; rfl
  have hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = ((α a : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u) := by
    intro a u v huv
    have hg : BlockForm 0 m (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) := by
      rw [hinvM]
      exact (hblk a⁻¹).2
    rw [hβv, hβv, mV_conj hD hM₀K θ a u v huv, colC_conj _ hg (hsh u) j₀ le_rfl,
      ← (hblk a).1]
    exact (mulVec_of_blockForm_blk h0 (hblk a).2 fun j hj => by
      rcases hj with hj | hj
      · omega
      · exact hcol0 u j (by omega)).2
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : colC (mV hD hM₀K θ v) j₀ = colC 1 j₀ := by
      refine eq_of_restrictBlk h0 (hcol0 v) (fun i _ => by simp [colC]) ?_
      have := congrArg Multiplicative.toAdd hv
      rw [hβv] at this
      rw [this]
      funext i
      simp [colC, restrictBlk]
    have h2 : mV hD hM₀K θ v = 1 := eq_of_colC (hsh v) shape_one fun j hj => by
      have : j = j₀ := Fin.ext (by simp [hj₀]; omega)
      rw [this, h1]
    have h3 : θ ⟨v, hM₀K (hD.V_le v.2)⟩ = 1 := Subtype.ext h2
    have h4 := hθ.1 (h3.trans (map_one θ).symm)
    have h5 : (v : A) = 1 := congrArg (fun z : ↥K => (z : A)) h4
    exact Subtype.ext h5
  have hMV := le_normalizer_of_comm hD.V_comm
  have hβs : Function.Surjective β := by
    let W : AddSubgroup (Fin m → ZMod 2) :=
      { carrier := {w | ∃ v, Multiplicative.toAdd (β v) = w}
        add_mem' := by
          rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
          exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
        zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
        neg_mem' := by
          rintro _ ⟨u, rfl⟩
          exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
    have hW : W ≠ ⊥ := by
      intro hW
      apply hD.V_ne
      rw [eq_bot_iff]
      intro v hv
      have h1 : Multiplicative.toAdd (β ⟨v, hv⟩) ∈ W := ⟨⟨v, hv⟩, rfl⟩
      rw [hW, AddSubgroup.mem_bot] at h1
      have h2 : β ⟨v, hv⟩ = β 1 := by
        rw [map_one]
        exact Multiplicative.toAdd.injective h1
      exact congrArg Subtype.val (hβi h2)
    have hinv : ∀ r s : Fin m, r ≠ s → ∀ w ∈ W, (1 + Matrix.single r s (1 : ZMod 2)) *ᵥ w ∈ W := by
      rintro r s hrs _ ⟨u, rfl⟩
      obtain ⟨a, ha⟩ := hαs (SpecialLinearGroup.transvection hrs (1 : ZMod 2))
      have hmem : (a : A) * u * (a : A)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hMV a.2) u).1 u.2
      refine ⟨⟨_, hmem⟩, ?_⟩
      rw [hequiv a u ⟨_, hmem⟩ rfl, ha, CFSG.LinearGroups.coe_transvection]
    have htop := eq_top_of_transvection_invariant (by omega) W hW hinv
    intro y
    have hy : Multiplicative.toAdd y ∈ W := by
      rw [htop]
      exact AddSubgroup.mem_top _
    obtain ⟨v, hv⟩ := hy
    exact ⟨v, Multiplicative.toAdd.injective hv⟩
  have hVO : V = pCoreOf 2 M₀ := by
    refine le_antisymm (le_pCoreOf_of_data hD).1 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ α.ker := by
      rw [hker]
      exact hy
    rw [MonoidHom.mem_ker] at hy'
    have hb := (hblk y).1
    rw [hy', Matrix.SpecialLinearGroup.coe_one] at hb
    have hshy := shape_of_blockForm h0 (hblk y).2 hb
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd (restrictBlk 0 m h0
      (colC ((θ ⟨y, hM₀K y.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) j₀)))
    have h1 : colC (mV hD hM₀K θ v) j₀ = colC ((θ ⟨y, hM₀K y.2⟩ :
        SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) j₀ :=
      eq_of_restrictBlk h0 (hcol0 v) (fun i hi => colC_eq_zero hshy j₀ i hi)
        (congrArg Multiplicative.toAdd hv)
    have h2 : mV hD hM₀K θ v = ((θ ⟨y, hM₀K y.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) := eq_of_colC (hsh v) hshy fun j hj => by
      have : j = j₀ := Fin.ext (by simp [hj₀]; omega)
      rw [this, h1]
    have h3 := hθ.1 (Subtype.ext h2)
    have h4 : (v : A) = y := congrArg Subtype.val h3
    show (y : A) ∈ V
    rw [← h4]
    exact v.2
  obtain rfl : m = n - 1 := by omega
  refine ⟨isPSL_of_mulEquiv_sl (by omega) (MulEquiv.ofBijective θ hθ),
    isMaxParabolic2_of_flag hc0 θ hθ hD.parabolic hD.ne_top ⟨by omega, by omega⟩ hQ,
    isPSL_of_mulEquiv_sl hm3 ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)), hVO,
    isNaturalSection_of_bij hMV α hαs hker β ⟨hβi, hβs⟩ hequiv⟩

theorem eq_of_restrictBlk_last {n a m : ℕ} (h : a + m ≤ n) (hamn : a + m = n)
    {w₁ w₂ : Fin n → ZMod 2}
    (h₁ : ∀ j : Fin n, (j : ℕ) < a → w₁ j = 0) (h₂ : ∀ j : Fin n, (j : ℕ) < a → w₂ j = 0)
    (he : restrictBlk a m h w₁ = restrictBlk a m h w₂) : w₁ = w₂ := by
  funext j
  by_cases hj : (j : ℕ) < a
  · rw [h₁ j hj, h₂ j hj]
  · have := congrFun he ⟨(j : ℕ) - a, by omega⟩
    simp only [restrictBlk] at this
    have e : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
    rwa [e] at this

theorem shape_of_blockForm_last {n a m : ℕ} (h : a + m ≤ n) (hamn : a + m = n)
    {w : Matrix (Fin n) (Fin n) (ZMod 2)} (hw : BlockForm a m w) (hb : blkAt a m h w = 1) :
    Shape a a w := by
  refine ⟨fun i j hj => ?_, fun i j hi => ?_⟩
  · by_cases hi : (i : ℕ) < a
    · exact hw.2.2.1 i j hi hj
    · rw [hw.1 i j (by omega) hj, ite_eq_right_iff.2 fun h => absurd (h ▸ hj) (by omega)]
  · by_cases hj : (j : ℕ) < a
    · rw [hw.1 i j hi hj, ite_eq_right_iff.2 fun h => absurd (h ▸ hj) (by omega)]
    · have := congrFun (congrFun hb ⟨(i : ℕ) - a, by omega⟩) ⟨(j : ℕ) - a, by omega⟩
      rw [blkAt_apply, Matrix.one_apply] at this
      have ei : (⟨a + ((i : ℕ) - a), by omega⟩ : Fin n) = i := Fin.ext (by simp; omega)
      have ej : (⟨a + ((j : ℕ) - a), by omega⟩ : Fin n) = j := Fin.ext (by simp; omega)
      rw [ei, ej] at this
      rw [this]
      exact if_congr (by rw [Fin.mk.injEq, Fin.ext_iff]; omega) rfl rfl

theorem concl2a_dual {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    (hc0 : Subgroup.center ↥K = ⊥) {n m : ℕ} (hn : 4 ≤ n) (hmn : 1 + m = n) (h1 : 1 + m ≤ n)
    (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hθ : Function.Bijective θ)
    (α : ↥M₀ →* SpecialLinearGroup (Fin m) (ZMod 2)) (hαs : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥M₀)
    (hblk : ∀ x : ↥M₀,
      blkAt 1 m h1 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)) ∧
      BlockForm 1 m ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)))
    (hcross : ∀ (k l : Fin n) (hkl : IsCross 1 m k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
      θ ⟨p, hM₀K p.2⟩ = SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2))
    (hQ : img θ Y = flagStabilizer n (ZMod 2) {1}) :
    C35Concl2a n K Y M₀ V := by
  classical
  have hm3 : 3 ≤ m := by omega
  set i₀ : Fin n := ⟨0, by omega⟩ with hi₀
  have hsh : ∀ v : ↥V, Shape 1 1 (mV hD hM₀K θ v) := fun v => by
    obtain ⟨-, -, hcc, hd⟩ := data_of_mem hD hM₀K h1 θ α hker hblk hcross v.2
    exact ⟨fun i j hj => col_std hcc hd j (Or.inl ⟨hj, by omega, by omega⟩) i,
      fun i j hi => row_std hcc hd i (Or.inl ⟨hi, by omega, by omega⟩) j⟩
  have hrow0 : ∀ (v : ↥V) (j : Fin n), (j : ℕ) < 1 → rowC (mV hD hM₀K θ v) i₀ j = 0 :=
    fun v j hj => rowC_eq_zero (hsh v) i₀ j hj
  let β : ↥V →* Multiplicative (Fin m → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (restrictBlk 1 m h1 (rowC (mV hD hM₀K θ v) i₀))
      map_one' := by
        rw [mV_one]
        apply Multiplicative.toAdd.injective
        funext i
        simp [rowC, restrictBlk]
      map_mul' := fun u v => by
        rw [mV_mul, rowC_mul (hsh u) (hsh v)]
        rfl }
  have hβv : ∀ v, Multiplicative.toAdd (β v) = restrictBlk 1 m h1 (rowC (mV hD hM₀K θ v) i₀) :=
    fun v => rfl
  have hinvM : ∀ x : ↥M₀, ((θ ⟨x, hM₀K x.2⟩)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) =
      θ ⟨(x⁻¹ : ↥M₀), hM₀K x⁻¹.2⟩ := fun x => by rw [← map_inv]; rfl
  have hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = (((α a)⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
        Matrix (Fin m) (Fin m) (ZMod 2))ᵀ *ᵥ Multiplicative.toAdd (β u) := by
    intro a u v huv
    have hg : ∀ i j : Fin n, (i : ℕ) < 1 → (j : ℕ) < 1 →
        ((θ ⟨a, hM₀K a.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) i j = if i = j then 1 else 0 :=
      fun i j hi hj => (hblk a).2.2.2.1 i j hi hj
    have hbf : BlockForm 1 m (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) := by
      rw [hinvM]
      exact (hblk a⁻¹).2
    have hbl : blkAt 1 m h1 (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = (((α a)⁻¹ : SpecialLinearGroup (Fin m) (ZMod 2)) :
          Matrix (Fin m) (Fin m) (ZMod 2)) := by
      rw [hinvM, (hblk a⁻¹).1, map_inv]
    rw [hβv, hβv, mV_conj hD hM₀K θ a u v huv, rowC_conj _ hg (hsh u) i₀ (by simp [hi₀]),
      ← hbl]
    exact (transpose_mulVec_of_blockForm_blk h1 hbf fun j hj => by
      rcases hj with hj | hj
      · exact hrow0 u j hj
      · omega).2
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h2 : rowC (mV hD hM₀K θ v) i₀ = rowC 1 i₀ := by
      refine eq_of_restrictBlk_last h1 hmn (hrow0 v) (fun j _ => by simp [rowC]) ?_
      have := congrArg Multiplicative.toAdd hv
      rw [hβv] at this
      rw [this]
      funext i
      simp [rowC, restrictBlk]
    have h3 : mV hD hM₀K θ v = 1 := eq_of_rowC (hsh v) shape_one fun i hi => by
      have : i = i₀ := Fin.ext (by simp [hi₀]; omega)
      rw [this, h2]
    have h4 : θ ⟨v, hM₀K (hD.V_le v.2)⟩ = 1 := Subtype.ext h3
    have h5 := hθ.1 (h4.trans (map_one θ).symm)
    have h6 : (v : A) = 1 := congrArg (fun z : ↥K => (z : A)) h5
    exact Subtype.ext h6
  have hMV := le_normalizer_of_comm hD.V_comm
  have hβs : Function.Surjective β := by
    let W : AddSubgroup (Fin m → ZMod 2) :=
      { carrier := {w | ∃ v, Multiplicative.toAdd (β v) = w}
        add_mem' := by
          rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
          exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
        zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
        neg_mem' := by
          rintro _ ⟨u, rfl⟩
          exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
    have hW : W ≠ ⊥ := by
      intro hW
      apply hD.V_ne
      rw [eq_bot_iff]
      intro v hv
      have h1' : Multiplicative.toAdd (β ⟨v, hv⟩) ∈ W := ⟨⟨v, hv⟩, rfl⟩
      rw [hW, AddSubgroup.mem_bot] at h1'
      have h2 : β ⟨v, hv⟩ = β 1 := by
        rw [map_one]
        exact Multiplicative.toAdd.injective h1'
      exact congrArg Subtype.val (hβi h2)
    have hinv : ∀ r s : Fin m, r ≠ s → ∀ w ∈ W, (1 + Matrix.single r s (1 : ZMod 2)) *ᵥ w ∈ W := by
      rintro r s hrs _ ⟨u, rfl⟩
      obtain ⟨a, ha⟩ := hαs (SpecialLinearGroup.transvection (Ne.symm hrs) (1 : ZMod 2))⁻¹
      have hmem : (a : A) * u * (a : A)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hMV a.2) u).1 u.2
      refine ⟨⟨_, hmem⟩, ?_⟩
      rw [hequiv a u ⟨_, hmem⟩ rfl, ha, inv_inv, CFSG.LinearGroups.coe_transvection,
        Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    have htop := eq_top_of_transvection_invariant (by omega) W hW hinv
    intro y
    have hy : Multiplicative.toAdd y ∈ W := by
      rw [htop]
      exact AddSubgroup.mem_top _
    obtain ⟨v, hv⟩ := hy
    exact ⟨v, Multiplicative.toAdd.injective hv⟩
  have hVO : V = pCoreOf 2 M₀ := by
    refine le_antisymm (le_pCoreOf_of_data hD).1 ?_
    rintro _ ⟨y, hy, rfl⟩
    have hy' : y ∈ α.ker := by
      rw [hker]
      exact hy
    rw [MonoidHom.mem_ker] at hy'
    have hb := (hblk y).1
    rw [hy', Matrix.SpecialLinearGroup.coe_one] at hb
    have hshy := shape_of_blockForm_last h1 hmn (hblk y).2 hb
    obtain ⟨v, hv⟩ := hβs (Multiplicative.ofAdd (restrictBlk 1 m h1
      (rowC ((θ ⟨y, hM₀K y.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) i₀)))
    have h2 : rowC (mV hD hM₀K θ v) i₀ = rowC ((θ ⟨y, hM₀K y.2⟩ :
        SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) i₀ :=
      eq_of_restrictBlk_last h1 hmn (hrow0 v) (fun j hj => rowC_eq_zero hshy i₀ j hj)
        (congrArg Multiplicative.toAdd hv)
    have h3 : mV hD hM₀K θ v = ((θ ⟨y, hM₀K y.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) := eq_of_rowC (hsh v) hshy fun i hi => by
      have : i = i₀ := Fin.ext (by simp [hi₀]; omega)
      rw [this, h2]
    have h4 := hθ.1 (Subtype.ext h3)
    have h5 : (v : A) = y := congrArg Subtype.val h4
    show (y : A) ∈ V
    rw [← h5]
    exact v.2
  obtain rfl : m = n - 1 := by omega
  refine ⟨isPSL_of_mulEquiv_sl (by omega) (MulEquiv.ofBijective θ hθ),
    isMaxParabolic2_of_flag hc0 θ hθ hD.parabolic hD.ne_top ⟨le_rfl, by omega⟩ hQ,
    isPSL_of_mulEquiv_sl hm3 ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective α hαs)), hVO,
    isNaturalSection_of_bij_dual hMV α hαs hker β ⟨hβi, hβs⟩ hequiv⟩

theorem mem_unitriangular_of_upper {n : ℕ} (g : SpecialLinearGroup (Fin n) (ZMod 2))
    (hg : ∀ i j : Fin n, j < i → (g : Matrix (Fin n) (Fin n) (ZMod 2)) i j = 0) :
    g ∈ unitriangular n (ZMod 2) := by
  refine ⟨hg, fun i => ?_⟩
  have hdet : ∏ k, (g : Matrix (Fin n) (Fin n) (ZMod 2)) k k = 1 := by
    rw [← Matrix.det_of_isUpperTriangular (fun a b hab => hg a b hab)]
    exact g.det_coe
  rcases zmod2_cases ((g : Matrix (Fin n) (Fin n) (ZMod 2)) i i) with h | h
  · exfalso
    have h0 := Finset.prod_eq_zero (s := Finset.univ)
      (f := fun k => (g : Matrix (Fin n) (Fin n) (ZMod 2)) k k) (Finset.mem_univ i) h
    rw [h0] at hdet
    exact zero_ne_one hdet
  · exact h

omit [Finite A] in
theorem mem_pCoreOf_of_blkAt {K Y : Subgroup A} (hYK : Y ≤ K)
    {n a m : ℕ} (hn : 1 ≤ n) (h : a + m ≤ n) (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2))
    (hθ : Function.Injective θ) {I : Set ℕ} (hQ : img θ Y = flagStabilizer n (ZMod 2) I)
    (hL : BlockLeft (flagStabilizer n (ZMod 2) I) a m)
    (hR : BlockRight (flagStabilizer n (ZMod 2) I) a m)
    (hut : ∀ g ∈ flagStabilizer n (ZMod 2) I,
      blkAt a m h (g : Matrix (Fin n) (Fin n) (ZMod 2)) = 1 → g ∈ unitriangular n (ZMod 2))
    {y : A} (hyK : y ∈ K) (hy : y ∈ Y)
    (hb : blkAt a m h ((θ ⟨y, hyK⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) = 1) : y ∈ pCoreOf 2 Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hmemQ : ∀ x (hx : x ∈ Y), θ ⟨x, hYK hx⟩ ∈ flagStabilizer n (ZMod 2) I :=
    fun x hx => hQ ▸ ⟨⟨x, hYK hx⟩, hx, rfl⟩
  have hmul : ∀ x z (hx : x ∈ Y) (hz : z ∈ Y),
      blkAt a m h ((θ ⟨x * z, hYK (Y.mul_mem hx hz)⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
        blkAt a m h ((θ ⟨x, hYK hx⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) *
        blkAt a m h ((θ ⟨z, hYK hz⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
          Matrix (Fin n) (Fin n) (ZMod 2)) := by
    intro x z hx hz
    rw [show (⟨x * z, hYK (Y.mul_mem hx hz)⟩ : ↥K) = ⟨x, hYK hx⟩ * ⟨z, hYK hz⟩ from rfl, map_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    exact blkAt_mul a m h _ _ (hL _ (hmemQ x hx)) (hR _ (hmemQ z hz))
  let U : Subgroup A :=
    { carrier := {x | ∃ hx : x ∈ Y, blkAt a m h ((θ ⟨x, hYK hx⟩ :
        SpecialLinearGroup (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)) = 1}
      one_mem' := ⟨Y.one_mem, by
        rw [show (⟨1, hYK Y.one_mem⟩ : ↥K) = 1 from rfl, map_one,
          Matrix.SpecialLinearGroup.coe_one]
        exact blkAt_one a m h⟩
      mul_mem' := fun {x z} ⟨hx, hbx⟩ ⟨hz, hbz⟩ => ⟨Y.mul_mem hx hz, by
        rw [hmul x z hx hz, hbx, hbz, one_mul]⟩
      inv_mem' := fun {x} ⟨hx, hbx⟩ => ⟨Y.inv_mem hx, by
        have h1 := hmul x⁻¹ x (Y.inv_mem hx) hx
        rw [hbx, mul_one] at h1
        rw [← h1]
        rw [show (⟨x⁻¹ * x, hYK (Y.mul_mem (Y.inv_mem hx) hx)⟩ : ↥K) = 1 from
          Subtype.ext (inv_mul_cancel x), map_one, Matrix.SpecialLinearGroup.coe_one]
        exact blkAt_one a m h⟩ }
  have hUY : U ≤ Y := fun x hx => hx.1
  have hN : Y ≤ Subgroup.normalizer (U : Set A) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ Y, ∀ x ∈ U, g * x * g⁻¹ ∈ U := by
      rintro g hg x ⟨hx, hbx⟩
      have hgx := Y.mul_mem hg hx
      refine ⟨Y.mul_mem hgx (Y.inv_mem hg), ?_⟩
      rw [hmul _ _ hgx (Y.inv_mem hg), hmul _ _ hg hx, hbx, mul_one, ← hmul _ _ hg (Y.inv_mem hg)]
      rw [show (⟨g * g⁻¹, hYK (Y.mul_mem hg (Y.inv_mem hg))⟩ : ↥K) = 1 from
        Subtype.ext (mul_inv_cancel g), map_one, Matrix.SpecialLinearGroup.coe_one]
      exact blkAt_one a m h
    intro x
    refine ⟨key g hg x, fun hx => ?_⟩
    have := key g⁻¹ (Y.inv_mem hg) _ hx
    have e : g⁻¹ * (g * x * g⁻¹) * g⁻¹⁻¹ = x := by group
    rwa [e] at this
  have hp : IsPGroup 2 ↥U := by
    rintro ⟨x, hx, hbx⟩
    obtain ⟨k, hk⟩ := isPGroup_unitriangular_charTwo (K := ZMod 2) (n := n) hn
      ⟨_, hut _ (hmemQ x hx) hbx⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : θ (⟨x, hYK hx⟩ ^ 2 ^ k) = θ 1 := by
      rw [map_pow, map_one]
      exact congrArg Subtype.val hk
    have h2 := congrArg Subtype.val (hθ h1)
    simpa using h2
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hUY hN hp ⟨hy, hb⟩

omit [Finite A] in
theorem eq_of_img_eq {K X₁ X₂ : Subgroup A} (hc0 : Subgroup.center ↥K = ⊥) {n : ℕ}
    (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hθ : Function.Injective θ)
    (h₁ : X₁ ≤ K) (h₂ : X₂ ≤ K) (he : img θ X₁ = img θ X₂) : X₁ = X₂ := by
  have hZ := centerOf_eq_bot hc0
  have hker : θ.ker ≤ Subgroup.center ↥K := by
    rw [(MonoidHom.ker_eq_bot_iff θ).2 hθ]
    exact bot_le
  refine le_antisymm (fun x hx => ?_) (fun x hx => ?_)
  · have : θ ⟨x, h₁ hx⟩ ∈ img θ X₂ := he ▸ ⟨⟨x, h₁ hx⟩, hx, rfl⟩
    exact mem_of_img_mem hker (hZ ▸ bot_le) this
  · have : θ ⟨x, h₂ hx⟩ ∈ img θ X₁ := he.symm ▸ ⟨⟨x, h₂ hx⟩, hx, rfl⟩
    exact mem_of_img_mem hker (hZ ▸ bot_le) this

omit [Finite A] in
theorem cuts_subset {K Y Q : Subgroup A} {n : ℕ} (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2))
    {I : Set ℕ} (hIc : ∀ c ∈ I, 1 ≤ c ∧ c < n) (hQ : img θ Y = flagStabilizer n (ZMod 2) I)
    (hYQ : Y ≤ Q) :
    img θ Q = flagStabilizer n (ZMod 2) (borelOvergroupCuts (img θ Q)) ∧
      borelOvergroupCuts (img θ Q) ⊆ I := by
  have hYQ' : img θ Y ≤ img θ Q := Subgroup.map_mono fun x hx => hYQ hx
  have hB : upperTriangular n (ZMod 2) ≤ img θ Q := by
    refine le_trans ?_ hYQ'
    rw [hQ]
    exact upperTriangular_le_flagStabilizer _
  obtain ⟨hQJ, -⟩ := borel_overgroups (img θ Q) hB
  obtain ⟨-, hIu⟩ := borel_overgroups (flagStabilizer n (ZMod 2) I)
    (upperTriangular_le_flagStabilizer _)
  have hcuts := hIu I hIc rfl
  refine ⟨hQJ, fun d hd => ?_⟩
  obtain ⟨h1, h2, hr⟩ := hd
  rw [hcuts]
  exact ⟨h1, h2, fun hmem => hr (hYQ' (hQ ▸ hmem))⟩

theorem perfectCore_eq_of_img {K Q M₀ : Subgroup A} (hc0 : Subgroup.center ↥K = ⊥) {n : ℕ}
    (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hθ : Function.Injective θ) (hQK : Q ≤ K)
    (hM₀K : M₀ ≤ K) (he : img θ M₀ = perfectCore (img θ Q)) : perfectCore Q = M₀ :=
  (eq_of_img_eq hc0 θ hθ ((perfectCore_le Q).trans hQK) hM₀K
    ((img_perfectCore θ hQK).trans he.symm))

theorem forallQ_311 {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    (hc0 : Subgroup.center ↥K = ⊥) (θ : ↥K →* SpecialLinearGroup (Fin 5) (ZMod 2))
    (hθ : Function.Injective θ) (hQ : img θ Y = flagStabilizer 5 (ZMod 2) {3, 4})
    (hM : img θ M₀ = perfectCore (flagStabilizer 5 (ZMod 2) {3, 4})) :
    ∀ Q : Subgroup A, IsParabolic2 K Q → Y ≤ Q → Q ≠ K →
      Q ≤ Subgroup.normalizer (M₀ : Set A) → perfectCore Q = M₀ := by
  classical
  intro Q hQpar hYQ hQK hQN
  have hZ := centerOf_eq_bot hc0
  have hker : θ.ker ≤ Subgroup.center ↥K := by
    rw [(MonoidHom.ker_eq_bot_iff θ).2 hθ]
    exact bot_le
  have hQK' : Q ≤ K := hQpar.1
  have hYK : Y ≤ K := hD.parabolic.1
  have hMY : M₀ ≤ Y := hD.eq_perfectCore ▸ perfectCore_le Y
  obtain ⟨hQJ, hJ⟩ := cuts_subset θ (by intro c hc; rcases hc with rfl | rfl <;> omega) hQ hYQ
  set J := borelOvergroupCuts (img θ Q) with hJdef
  have hMQ : img θ M₀ ≤ img θ Q := Subgroup.map_mono fun x hx => hYQ (hMY hx)
  have hMN : img θ Q ≤
      Subgroup.normalizer (img θ M₀ : Set (SpecialLinearGroup (Fin 5) (ZMod 2))) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨q * x * q⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.1 (hQN hq) x).1 hx
    · rintro ⟨x, hx, hxy⟩
      refine ⟨q⁻¹ * x * q, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hQN (Q.inv_mem hq)) x).1 hx
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        simpa using this
      · rw [map_mul, map_mul, map_inv, hxy]
        group
  have hMp : ⁅img θ M₀, img θ M₀⁆ = img θ M₀ := by
    rw [hM]
    exact perfectCore_perfect _
  have hMne : img θ M₀ ≠ ⊥ := by
    intro hb
    apply hD.ne_bot
    refine eq_of_img_eq hc0 θ hθ hM₀K bot_le (hb.trans ?_)
    simp [img]

  by_cases h3 : 3 ∈ J <;> by_cases h4 : 4 ∈ J
  · have hJe : J = {3, 4} := Set.Subset.antisymm hJ (by
      intro c hc
      rcases hc with rfl | rfl
      · exact h3
      · exact h4)
    have hQY : Q = Y := eq_of_img_eq hc0 θ hθ hQK' hYK (by rw [hQJ, hJe, hQ])
    rw [hQY, ← hD.eq_perfectCore]
  · have hJe : J = {3} := Set.Subset.antisymm (fun c hc => by
      rcases hJ hc with rfl | rfl
      · rfl
      · exact absurd hc h4) (by intro c hc; rw [hc]; exact h3)
    refine perfectCore_eq_of_img hc0 θ hθ hQK' hM₀K ?_
    rw [hQJ, hJe] at hMQ hMN ⊢
    exact eq_perfectCore_of_normal (n := 5) (I := {3}) (a := 0) (m := 3) (by norm_num)
      (by norm_num) (by norm_num) le_rfl (Or.inl rfl) (Or.inr (Set.mem_singleton 3))
      (by intro c hc; rw [hc]; omega) hMQ hMN hMp hMne
  · exfalso
    have hJe : J = {4} := Set.Subset.antisymm (fun c hc => by
      rcases hJ hc with rfl | rfl
      · exact absurd hc h3
      · rfl) (by intro c hc; rw [hc]; exact h4)
    rw [hQJ, hJe] at hMQ hMN
    have he := eq_perfectCore_of_normal (n := 5) (I := {4}) (a := 0) (m := 4) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (Or.inl rfl) (Or.inr (Set.mem_singleton 4))
      (by intro c hc; rw [hc]; omega) hMQ hMN hMp hMne
    have hT := liftT_mem_perfectCore (n := 5) (I := {4}) (a := 0) (m := 4) (by norm_num)
      (by norm_num) (by intro c hc; rw [hc]; omega) (i := 3) (j := 2) (by decide)
    rw [← he, hM] at hT
    have hbf := blockForm_of_mem (by norm_num) (I := {3, 4}) (a := 0) (m := 3) (by norm_num)
      le_rfl (Or.inl rfl) (Or.inr (by simp)) hT
    have := hbf.2.1 ⟨3, by norm_num⟩ ⟨2, by norm_num⟩ (by norm_num) (by norm_num)
    rw [coe_liftT] at this
    exact absurd this (by decide)
  · exfalso
    apply hQK
    have hJe : J = ∅ := Set.eq_empty_of_forall_notMem fun c hc => by
      rcases hJ hc with rfl | rfl
      · exact h3 hc
      · exact h4 hc
    refine le_antisymm hQK' fun x hx => ?_
    have : θ ⟨x, hx⟩ ∈ img θ Q := by
      rw [hQJ, hJe, flagStabilizer_empty]
      exact Subgroup.mem_top _
    exact mem_of_img_mem hker (hZ ▸ bot_le) this

theorem forallQ_113 {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    (hc0 : Subgroup.center ↥K = ⊥) (θ : ↥K →* SpecialLinearGroup (Fin 5) (ZMod 2))
    (hθ : Function.Injective θ) (hQ : img θ Y = flagStabilizer 5 (ZMod 2) {1, 2})
    (hM : img θ M₀ = perfectCore (flagStabilizer 5 (ZMod 2) {1, 2})) :
    ∀ Q : Subgroup A, IsParabolic2 K Q → Y ≤ Q → Q ≠ K →
      Q ≤ Subgroup.normalizer (M₀ : Set A) → perfectCore Q = M₀ := by
  classical
  intro Q hQpar hYQ hQK hQN
  have hZ := centerOf_eq_bot hc0
  have hker : θ.ker ≤ Subgroup.center ↥K := by
    rw [(MonoidHom.ker_eq_bot_iff θ).2 hθ]
    exact bot_le
  have hQK' : Q ≤ K := hQpar.1
  have hYK : Y ≤ K := hD.parabolic.1
  have hMY : M₀ ≤ Y := hD.eq_perfectCore ▸ perfectCore_le Y
  obtain ⟨hQJ, hJ⟩ := cuts_subset θ (by intro c hc; rcases hc with rfl | rfl <;> omega) hQ hYQ
  set J := borelOvergroupCuts (img θ Q) with hJdef
  have hMQ : img θ M₀ ≤ img θ Q := Subgroup.map_mono fun x hx => hYQ (hMY hx)
  have hMN : img θ Q ≤
      Subgroup.normalizer (img θ M₀ : Set (SpecialLinearGroup (Fin 5) (ZMod 2))) := by
    rintro _ ⟨q, hq, rfl⟩
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨q * x * q⁻¹, ?_, by simp⟩
      exact (Subgroup.mem_normalizer_iff.1 (hQN hq) x).1 hx
    · rintro ⟨x, hx, hxy⟩
      refine ⟨q⁻¹ * x * q, ?_, ?_⟩
      · have := (Subgroup.mem_normalizer_iff.1 (hQN (Q.inv_mem hq)) x).1 hx
        rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
        simpa using this
      · rw [map_mul, map_mul, map_inv, hxy]
        group
  have hMp : ⁅img θ M₀, img θ M₀⁆ = img θ M₀ := by
    rw [hM]
    exact perfectCore_perfect _
  have hMne : img θ M₀ ≠ ⊥ := by
    intro hb
    apply hD.ne_bot
    refine eq_of_img_eq hc0 θ hθ hM₀K bot_le (hb.trans ?_)
    simp [img]

  by_cases h1 : 1 ∈ J <;> by_cases h2 : 2 ∈ J
  · have hJe : J = {1, 2} := Set.Subset.antisymm hJ (by
      intro c hc
      rcases hc with rfl | rfl
      · exact h1
      · exact h2)
    have hQY : Q = Y := eq_of_img_eq hc0 θ hθ hQK' hYK (by rw [hQJ, hJe, hQ])
    rw [hQY, ← hD.eq_perfectCore]
  · exfalso
    have hJe : J = {1} := Set.Subset.antisymm (fun c hc => by
      rcases hJ hc with rfl | rfl
      · rfl
      · exact absurd hc h2) (by intro c hc; rw [hc]; exact h1)
    rw [hQJ, hJe] at hMQ hMN
    have he := eq_perfectCore_of_normal (n := 5) (I := {1}) (a := 1) (m := 4) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (Or.inr (Set.mem_singleton 1)) (Or.inl rfl)
      (by intro c hc; rw [hc]; omega) hMQ hMN hMp hMne
    have hT := liftT_mem_perfectCore (n := 5) (I := {1}) (a := 1) (m := 4) (by norm_num)
      (by norm_num) (by intro c hc; rw [hc]; omega) (i := 1) (j := 0) (by decide)
    rw [← he, hM] at hT
    have hbf := blockForm_of_mem (by norm_num) (I := {1, 2}) (a := 2) (m := 3) (by norm_num)
      le_rfl (Or.inr (by simp)) (Or.inl rfl) hT
    have := hbf.1 ⟨2, by norm_num⟩ ⟨1, by norm_num⟩ (by norm_num) (by norm_num)
    rw [coe_liftT] at this
    exact absurd this (by decide)
  · have hJe : J = {2} := Set.Subset.antisymm (fun c hc => by
      rcases hJ hc with rfl | rfl
      · exact absurd hc h1
      · rfl) (by intro c hc; rw [hc]; exact h2)
    refine perfectCore_eq_of_img hc0 θ hθ hQK' hM₀K ?_
    rw [hQJ, hJe] at hMQ hMN ⊢
    exact eq_perfectCore_of_normal (n := 5) (I := {2}) (a := 2) (m := 3) (by norm_num)
      (by norm_num) (by norm_num) le_rfl (Or.inr (Set.mem_singleton 2)) (Or.inl rfl)
      (by intro c hc; rw [hc]; omega) hMQ hMN hMp hMne
  · exfalso
    apply hQK
    have hJe : J = ∅ := Set.eq_empty_of_forall_notMem fun c hc => by
      rcases hJ hc with rfl | rfl
      · exact h1 hc
      · exact h2 hc
    refine le_antisymm hQK' fun x hx => ?_
    have : θ ⟨x, hx⟩ ∈ img θ Q := by
      rw [hQJ, hJe, flagStabilizer_empty]
      exact Subgroup.mem_top _
    exact mem_of_img_mem hker (hZ ▸ bot_le) this

theorem isE2_of_hom {N : Type} [Group N] {d : ℕ} (c : N →* Multiplicative (Fin d → ZMod 2))
    (hc : Function.Injective c) (hs : ∀ k, ∃ x, c x = Multiplicative.ofAdd (Pi.single k 1)) :
    IsE2 d N := by
  classical
  let S : AddSubgroup (Fin d → ZMod 2) :=
    { carrier := {w | ∃ x, Multiplicative.toAdd (c x) = w}
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
      zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
      neg_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
  have hall : ∀ w, w ∈ S := by
    intro w
    rw [← Finset.univ_sum_single w]
    refine AddSubgroup.sum_mem _ fun k _ => ?_
    rcases zmod2_cases (w k) with h | h
    · rw [h, Pi.single_zero]
      exact S.zero_mem
    · rw [h]
      obtain ⟨x, hx⟩ := hs k
      exact ⟨x, by rw [hx]; rfl⟩
  refine ⟨MulEquiv.ofBijective c ⟨hc, fun y => ?_⟩⟩
  obtain ⟨x, hx⟩ := hall (Multiplicative.toAdd y)
  exact ⟨x, Multiplicative.toAdd.injective hx⟩

theorem transvection_entry {n : ℕ} {k l r c : Fin n} (hkl : k ≠ l) (hrc : r ≠ c)
    (h : ¬ (k = r ∧ l = c)) :
    ((SpecialLinearGroup.transvection hkl (1 : ZMod 2) : SpecialLinearGroup (Fin n) (ZMod 2)) :
      Matrix (Fin n) (Fin n) (ZMod 2)) r c = 0 := by
  rw [CFSG.LinearGroups.coe_transvection, Matrix.add_apply, Matrix.one_apply_ne hrc,
    Matrix.single_apply, ite_eq_right_iff.2 fun h' => absurd h' h, add_zero]

omit [Finite A] in
theorem isE2_pCore_311 {K M₀ : Subgroup A} (hM₀K : M₀ ≤ K) (h0 : 0 + 3 ≤ 5)
    (θ : ↥K →* SpecialLinearGroup (Fin 5) (ZMod 2)) (hθ : Function.Injective θ)
    (α : ↥M₀ →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hker : α.ker = CFSG.pCore 2 ↥M₀)
    (hblk : ∀ x : ↥M₀,
      blkAt 0 3 h0 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 0 3 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (hcross : ∀ (k l : Fin 5) (hkl : IsCross 0 3 k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
      θ ⟨p, hM₀K p.2⟩ = SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2)) :
    IsE2 6 ↥(CFSG.pCore 2 ↥M₀) := by
  classical
  set e : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv with he
  let w : ↥(CFSG.pCore 2 ↥M₀) → Matrix (Fin 5) (Fin 5) (ZMod 2) := fun y =>
    ((θ ⟨((y : ↥M₀) : A), hM₀K (y : ↥M₀).2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2))
  have hsh : ∀ y, Shape 3 3 (w y) := by
    intro y
    have hy : α y = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact y.2
    have hb := (hblk y).1
    rw [hy, Matrix.SpecialLinearGroup.coe_one] at hb
    exact shape_of_blockForm h0 (hblk y).2 hb
  have hwmul : ∀ y z, w (y * z) = w y * w z := by
    intro y z
    simp only [w]
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul]
    rfl
  let coord : Matrix (Fin 5) (Fin 5) (ZMod 2) → Fin 6 → ZMod 2 := fun v k =>
    colC v ⟨3 + ((e.symm k).1 : ℕ), by omega⟩ ⟨((e.symm k).2 : ℕ), by omega⟩
  let c : ↥(CFSG.pCore 2 ↥M₀) →* Multiplicative (Fin 6 → ZMod 2) :=
    { toFun := fun y => Multiplicative.ofAdd (coord (w y))
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext k
        simp only [coord, w, toAdd_ofAdd, toAdd_one, Pi.zero_apply]
        rw [show (⟨((1 : ↥(CFSG.pCore 2 ↥M₀)) : ↥M₀).1, hM₀K (1 : ↥M₀).2⟩ : ↥K) = 1 from rfl,
          map_one, Matrix.SpecialLinearGroup.coe_one]
        simp [colC]
      map_mul' := fun y z => by
        apply Multiplicative.toAdd.injective
        funext k
        simp only [coord, toAdd_ofAdd, toAdd_mul, Pi.add_apply]
        rw [hwmul, colC_mul (hsh y) (hsh z)]
        rfl }
  refine isE2_of_hom c ?_ ?_
  · rw [injective_iff_map_eq_one]
    intro y hy
    have hw1 : w y = 1 := eq_of_colC (hsh y) shape_one fun j hj => by
      funext i
      by_cases hi : (i : ℕ) < 3
      · have := congrFun (congrArg Multiplicative.toAdd hy) (e (⟨(j : ℕ) - 3, by omega⟩,
          ⟨i, hi⟩))
        simp only [c, coord, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one,
          Pi.zero_apply, Equiv.symm_apply_apply] at this
        have ej : (⟨3 + ((j : ℕ) - 3), by omega⟩ : Fin 5) = j := Fin.ext (by simp; omega)
        rw [ej] at this
        rw [this]
        simp [colC]
      · rw [colC_eq_zero (hsh y) j i (by omega), colC_eq_zero (shape_one (c := 3) (r := 3)) j i
          (by omega)]
    have h1 : θ ⟨((y : ↥M₀) : A), hM₀K (y : ↥M₀).2⟩ = 1 := Subtype.ext hw1
    have h2 := hθ (h1.trans (map_one θ).symm)
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥K => (z : A)) h2))
  · intro k
    set q := (e.symm k).1
    set r := (e.symm k).2
    have hc : IsCross 0 3 (⟨r, by omega⟩ : Fin 5) ⟨3 + q, by omega⟩ :=
      Or.inr ⟨by simp, by simp, by simp⟩
    obtain ⟨p, hp, hpT⟩ := hcross _ _ hc
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    funext k'
    simp only [c, coord, w, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [hpT, colC_apply]
    set q' := (e.symm k').1
    set r' := (e.symm k').2
    have hne : (⟨r', by omega⟩ : Fin 5) ≠ ⟨3 + q', by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    rw [ite_eq_right_iff.2 fun h => absurd h hne, sub_zero]
    by_cases hkk : k' = k
    · subst hkk
      rw [Pi.single_eq_same, CFSG.LinearGroups.coe_transvection, Matrix.add_apply,
        Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add]
    · rw [Pi.single_eq_of_ne hkk, transvection_entry _ hne]
      intro ⟨h1, h2⟩
      apply hkk
      apply e.symm.injective
      have h1' : r = r' := Fin.ext (by simpa using congrArg Fin.val h1)
      have h2' : q = q' := Fin.ext (by have := congrArg Fin.val h2; simp at this; omega)
      exact Prod.ext h2'.symm h1'.symm

omit [Finite A] in
theorem isE2_pCore_113 {K M₀ : Subgroup A} (hM₀K : M₀ ≤ K) (h2 : 2 + 3 ≤ 5)
    (θ : ↥K →* SpecialLinearGroup (Fin 5) (ZMod 2)) (hθ : Function.Injective θ)
    (α : ↥M₀ →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hker : α.ker = CFSG.pCore 2 ↥M₀)
    (hblk : ∀ x : ↥M₀,
      blkAt 2 3 h2 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 2 3 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (hcross : ∀ (k l : Fin 5) (hkl : IsCross 2 3 k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
      θ ⟨p, hM₀K p.2⟩ = SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2)) :
    IsE2 6 ↥(CFSG.pCore 2 ↥M₀) := by
  classical
  set e : Fin 2 × Fin 3 ≃ Fin 6 := finProdFinEquiv with he
  let w : ↥(CFSG.pCore 2 ↥M₀) → Matrix (Fin 5) (Fin 5) (ZMod 2) := fun y =>
    ((θ ⟨((y : ↥M₀) : A), hM₀K (y : ↥M₀).2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
      Matrix (Fin 5) (Fin 5) (ZMod 2))
  have hsh : ∀ y, Shape 2 2 (w y) := by
    intro y
    have hy : α y = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact y.2
    have hb := (hblk y).1
    rw [hy, Matrix.SpecialLinearGroup.coe_one] at hb
    exact shape_of_blockForm_last h2 rfl (hblk y).2 hb
  have hwmul : ∀ y z, w (y * z) = w y * w z := by
    intro y z
    simp only [w]
    rw [← Matrix.SpecialLinearGroup.coe_mul, ← map_mul]
    rfl
  let coord : Matrix (Fin 5) (Fin 5) (ZMod 2) → Fin 6 → ZMod 2 := fun v k =>
    rowC v ⟨((e.symm k).1 : ℕ), by omega⟩ ⟨2 + ((e.symm k).2 : ℕ), by omega⟩
  let c : ↥(CFSG.pCore 2 ↥M₀) →* Multiplicative (Fin 6 → ZMod 2) :=
    { toFun := fun y => Multiplicative.ofAdd (coord (w y))
      map_one' := by
        apply Multiplicative.toAdd.injective
        funext k
        simp only [coord, w, toAdd_ofAdd, toAdd_one, Pi.zero_apply]
        rw [show (⟨((1 : ↥(CFSG.pCore 2 ↥M₀)) : ↥M₀).1, hM₀K (1 : ↥M₀).2⟩ : ↥K) = 1 from rfl,
          map_one, Matrix.SpecialLinearGroup.coe_one]
        simp [rowC]
      map_mul' := fun y z => by
        apply Multiplicative.toAdd.injective
        funext k
        simp only [coord, toAdd_ofAdd, toAdd_mul, Pi.add_apply]
        rw [hwmul, rowC_mul (hsh y) (hsh z)]
        rfl }
  refine isE2_of_hom c ?_ ?_
  · rw [injective_iff_map_eq_one]
    intro y hy
    have hw1 : w y = 1 := eq_of_rowC (hsh y) shape_one fun i hi => by
      funext j
      by_cases hj : 2 ≤ (j : ℕ)
      · have := congrFun (congrArg Multiplicative.toAdd hy) (e (⟨i, hi⟩,
          ⟨(j : ℕ) - 2, by omega⟩))
        simp only [c, coord, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, toAdd_one,
          Pi.zero_apply, Equiv.symm_apply_apply] at this
        have ej : (⟨2 + ((j : ℕ) - 2), by omega⟩ : Fin 5) = j := Fin.ext (by simp; omega)
        rw [ej] at this
        rw [this]
        simp [rowC]
      · rw [rowC_eq_zero (hsh y) i j (by omega), rowC_eq_zero (shape_one (c := 2) (r := 2)) i j
          (by omega)]
    have h1 : θ ⟨((y : ↥M₀) : A), hM₀K (y : ↥M₀).2⟩ = 1 := Subtype.ext hw1
    have h2 := hθ (h1.trans (map_one θ).symm)
    exact Subtype.ext (Subtype.ext (congrArg (fun z : ↥K => (z : A)) h2))
  · intro k
    set q := (e.symm k).1
    set r := (e.symm k).2
    have hc : IsCross 2 3 (⟨q, by omega⟩ : Fin 5) ⟨2 + r, by omega⟩ :=
      Or.inl ⟨by simp; omega, by simp, by simp; omega⟩
    obtain ⟨p, hp, hpT⟩ := hcross _ _ hc
    refine ⟨⟨p, hp⟩, ?_⟩
    apply Multiplicative.toAdd.injective
    funext k'
    simp only [c, coord, w, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd]
    rw [hpT, rowC_apply]
    set q' := (e.symm k').1
    set r' := (e.symm k').2
    have hne : (⟨q', by omega⟩ : Fin 5) ≠ ⟨2 + r', by omega⟩ := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    rw [ite_eq_right_iff.2 fun h => absurd h hne, sub_zero]
    by_cases hkk : k' = k
    · subst hkk
      rw [Pi.single_eq_same, CFSG.LinearGroups.coe_transvection, Matrix.add_apply,
        Matrix.one_apply_ne hne, Matrix.single_apply_same, zero_add]
    · rw [Pi.single_eq_of_ne hkk, transvection_entry _ hne]
      intro ⟨h1, h2⟩
      apply hkk
      apply e.symm.injective
      have h1' : q = q' := Fin.ext (by simpa using congrArg Fin.val h1)
      have h2' : r = r' := Fin.ext (by have := congrArg Fin.val h2; simp at this; omega)
      exact Prod.ext h1'.symm h2'.symm

theorem concl2b_nat {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    (hc0 : Subgroup.center ↥K = ⊥) (h0 : 0 + 3 ≤ 5)
    (θ : ↥K →* SpecialLinearGroup (Fin 5) (ZMod 2)) (hθ : Function.Bijective θ)
    (α : ↥M₀ →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hαs : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥M₀)
    (hblk : ∀ x : ↥M₀,
      blkAt 0 3 h0 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 0 3 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (hcross : ∀ (k l : Fin 5) (hkl : IsCross 0 3 k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
      θ ⟨p, hM₀K p.2⟩ = SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2))
    (hQ : img θ Y = flagStabilizer 5 (ZMod 2) {3, 4})
    (hM : img θ M₀ = perfectCore (flagStabilizer 5 (ZMod 2) {3, 4})) :
    C35Concl2b K Y M₀ V := by
  classical
  have hYK : Y ≤ K := hD.parabolic.1
  have hZ := centerOf_eq_bot hc0
  have hkerθ : θ.ker ≤ Subgroup.center ↥K := by
    rw [(MonoidHom.ker_eq_bot_iff θ).2 hθ.1]
    exact bot_le
  have h34 : (3 : Fin 5) ≠ 4 := by decide
  obtain ⟨τ, hτ⟩ := hθ.2 (SpecialLinearGroup.transvection h34 (1 : ZMod 2))
  have htQ : SpecialLinearGroup.transvection h34 (1 : ZMod 2) ∈
      flagStabilizer 5 (ZMod 2) {3, 4} := by
    refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
    refine transvection_entry h34 (fun h => by subst h; omega) fun ⟨h1, h2⟩ => ?_
    subst h1 h2
    rcases hc with rfl | rfl <;> simp at hl hk
  have hτY : (τ : A) ∈ Y := mem_of_img_mem hkerθ (hZ ▸ bot_le) (by rw [hτ, hQ]; exact htQ)
  have hτO : (τ : A) ∈ pCoreOf 2 Y := by
    refine mem_pCoreOf_of_blkAt hYK (by norm_num) h0 θ hθ.1 hQ (blockLeft_zero _ 3)
      (blockRight_of_stabilizer fun g hg => mem_flagStabilizer.1 hg 3 (by simp))
      (fun g hg hb => mem_unitriangular_of_upper g fun i j hji => ?_) τ.2 hτY ?_
    · by_cases hi : (i : ℕ) < 3
      · have := congrFun (congrFun hb ⟨i, hi⟩) ⟨j, by omega⟩
        rw [blkAt_apply, Matrix.one_apply_ne (fun h => by
          have := congrArg Fin.val h; simp at this; omega)] at this
        have ei : (⟨0 + (i : ℕ), by omega⟩ : Fin 5) = i := Fin.ext (by simp)
        have ej : (⟨0 + (j : ℕ), by omega⟩ : Fin 5) = j := Fin.ext (by simp)
        rwa [ei, ej] at this
      · by_cases hj : (j : ℕ) < 3
        · exact stabilizer_entries (mem_flagStabilizer.1 hg 3 (by simp)) hj (by omega)
        · exact stabilizer_entries (mem_flagStabilizer.1 hg 4 (by simp))
            (by have := Fin.lt_def.1 hji; omega) (by have := Fin.lt_def.1 hji; omega)
    · show blkAt 0 3 h0 ((θ τ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1
      rw [hτ, CFSG.LinearGroups.coe_transvection]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
  have hsh : ∀ v : ↥V, Shape 3 3 (mV hD hM₀K θ v) := fun v => by
    obtain ⟨-, -, hcc, hd⟩ := data_of_mem hD hM₀K h0 θ α hker hblk hcross v.2
    exact ⟨fun i j hj => col_std hcc hd j (Or.inr ⟨by omega, by omega, by omega⟩) i,
      fun i j hi => row_std hcc hd i (Or.inr ⟨by omega, by omega⟩) j⟩
  have hcol3 : ∀ v : ↥V, colC (mV hD hM₀K θ v) 3 = 0 := by
    intro v
    obtain ⟨-, -, -, hd⟩ := data_of_mem hD hM₀K h0 θ α hker hblk hcross v.2
    have hcomm : (τ : A) * v = v * τ :=
      Subgroup.mem_centralizer_iff.1 (hD.V_le_center v.2).2 _ hτO
    have h1 : θ τ * θ ⟨v, hM₀K (hD.V_le v.2)⟩ = θ ⟨v, hM₀K (hD.V_le v.2)⟩ * θ τ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    rw [hτ] at h1
    have h2 := congrArg (fun z : SpecialLinearGroup (Fin 5) (ZMod 2) =>
      (z : Matrix (Fin 5) (Fin 5) (ZMod 2))) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection] at h2
    have h3 := ((commute_single_iff (mV hD hM₀K θ v)).1 h2.symm).1
    have hd' : mV hD hM₀K θ v 3 3 = 1 := hd 3
    funext i
    rw [colC_apply]
    by_cases hi : i = 3
    · subst hi
      rw [hd', ite_eq_left rfl, sub_self]
      rfl
    · rw [h3 i hi, ite_eq_right_iff.2 fun h => absurd h hi, sub_self]
      rfl
  set j₀ : Fin 5 := 4 with hj₀
  have hcol0 : ∀ (v : ↥V) (i : Fin 5), 3 ≤ (i : ℕ) → colC (mV hD hM₀K θ v) j₀ i = 0 :=
    fun v i hi => colC_eq_zero (hsh v) j₀ i hi
  let β : ↥V →* Multiplicative (Fin 3 → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (restrictBlk 0 3 h0 (colC (mV hD hM₀K θ v) j₀))
      map_one' := by
        rw [mV_one]
        apply Multiplicative.toAdd.injective
        funext i
        simp [colC, restrictBlk]
      map_mul' := fun u v => by
        rw [mV_mul, colC_mul (hsh u) (hsh v)]
        rfl }
  have hβv : ∀ v, Multiplicative.toAdd (β v) = restrictBlk 0 3 h0 (colC (mV hD hM₀K θ v) j₀) :=
    fun v => rfl
  have hinvM : ∀ x : ↥M₀, ((θ ⟨x, hM₀K x.2⟩)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) =
      θ ⟨(x⁻¹ : ↥M₀), hM₀K x⁻¹.2⟩ := fun x => by rw [← map_inv]; rfl
  have hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = ((α a : SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (β u) := by
    intro a u v huv
    have hg : BlockForm 0 3 (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
      rw [hinvM]
      exact (hblk a⁻¹).2
    rw [hβv, hβv, mV_conj hD hM₀K θ a u v huv, colC_conj _ hg (hsh u) j₀ (by simp [hj₀]),
      ← (hblk a).1]
    exact (mulVec_of_blockForm_blk h0 (hblk a).2 fun j hj => by
      rcases hj with hj | hj
      · omega
      · exact hcol0 u j (by omega)).2
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h1 : colC (mV hD hM₀K θ v) j₀ = colC 1 j₀ := by
      refine eq_of_restrictBlk h0 (hcol0 v) (fun i _ => by simp [colC]) ?_
      have := congrArg Multiplicative.toAdd hv
      rw [hβv] at this
      rw [this]
      funext i
      simp [colC, restrictBlk]
    have h2 : mV hD hM₀K θ v = 1 := eq_of_colC (hsh v) shape_one fun j hj => by
      rcases (by omega : (j : ℕ) = 3 ∨ (j : ℕ) = 4) with h | h
      · have : j = 3 := Fin.ext h
        rw [this, hcol3]
        funext i
        simp [colC]
      · have : j = j₀ := Fin.ext h
        rw [this, h1]
    have h3 : θ ⟨v, hM₀K (hD.V_le v.2)⟩ = 1 := Subtype.ext h2
    have h4 := hθ.1 (h3.trans (map_one θ).symm)
    have h5 : (v : A) = 1 := congrArg (fun z : ↥K => (z : A)) h4
    exact Subtype.ext h5
  have hMV := le_normalizer_of_comm hD.V_comm
  have hβs : Function.Surjective β := by
    let W : AddSubgroup (Fin 3 → ZMod 2) :=
      { carrier := {w | ∃ v, Multiplicative.toAdd (β v) = w}
        add_mem' := by
          rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
          exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
        zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
        neg_mem' := by
          rintro _ ⟨u, rfl⟩
          exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
    have hW : W ≠ ⊥ := by
      intro hW
      apply hD.V_ne
      rw [eq_bot_iff]
      intro v hv
      have h1 : Multiplicative.toAdd (β ⟨v, hv⟩) ∈ W := ⟨⟨v, hv⟩, rfl⟩
      rw [hW, AddSubgroup.mem_bot] at h1
      have h2 : β ⟨v, hv⟩ = β 1 := by
        rw [map_one]
        exact Multiplicative.toAdd.injective h1
      exact congrArg Subtype.val (hβi h2)
    have hinv : ∀ r s : Fin 3, r ≠ s → ∀ w ∈ W, (1 + Matrix.single r s (1 : ZMod 2)) *ᵥ w ∈ W := by
      rintro r s hrs _ ⟨u, rfl⟩
      obtain ⟨a, ha⟩ := hαs (SpecialLinearGroup.transvection hrs (1 : ZMod 2))
      have hmem : (a : A) * u * (a : A)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hMV a.2) u).1 u.2
      refine ⟨⟨_, hmem⟩, ?_⟩
      rw [hequiv a u ⟨_, hmem⟩ rfl, ha, CFSG.LinearGroups.coe_transvection]
    have htop := eq_top_of_transvection_invariant (by norm_num) W hW hinv
    intro y
    have hy : Multiplicative.toAdd y ∈ W := by
      rw [htop]
      exact AddSubgroup.mem_top _
    obtain ⟨v, hv⟩ := hy
    exact ⟨v, Multiplicative.toAdd.injective hv⟩
  refine ⟨isPSL_of_mulEquiv_sl (by norm_num) (MulEquiv.ofBijective θ hθ),
    ⟨CFSG.pCore 2 ↥M₀, CFSG.pCore_normal,
      isE2_pCore_311 hM₀K h0 θ hθ.1 α hker hblk hcross,
      isPSL_of_mulEquiv_sl le_rfl ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hαs))⟩,
    isNaturalSection_of_bij hMV α hαs hker β ⟨hβi, hβs⟩ hequiv,
    forallQ_311 hD hM₀K hc0 θ hθ.1 hQ hM⟩

theorem concl2b_dual {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    (hc0 : Subgroup.center ↥K = ⊥) (h2 : 2 + 3 ≤ 5)
    (θ : ↥K →* SpecialLinearGroup (Fin 5) (ZMod 2)) (hθ : Function.Bijective θ)
    (α : ↥M₀ →* SpecialLinearGroup (Fin 3) (ZMod 2)) (hαs : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥M₀)
    (hblk : ∀ x : ↥M₀,
      blkAt 2 3 h2 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ∧
      BlockForm 2 3 ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)))
    (hcross : ∀ (k l : Fin 5) (hkl : IsCross 2 3 k l), ∃ p : ↥M₀, p ∈ CFSG.pCore 2 ↥M₀ ∧
      θ ⟨p, hM₀K p.2⟩ = SpecialLinearGroup.transvection hkl.ne (1 : ZMod 2))
    (hQ : img θ Y = flagStabilizer 5 (ZMod 2) {1, 2})
    (hM : img θ M₀ = perfectCore (flagStabilizer 5 (ZMod 2) {1, 2})) :
    C35Concl2b K Y M₀ V := by
  classical
  have hYK : Y ≤ K := hD.parabolic.1
  have hZ := centerOf_eq_bot hc0
  have hkerθ : θ.ker ≤ Subgroup.center ↥K := by
    rw [(MonoidHom.ker_eq_bot_iff θ).2 hθ.1]
    exact bot_le
  have h01 : (0 : Fin 5) ≠ 1 := by decide
  obtain ⟨τ, hτ⟩ := hθ.2 (SpecialLinearGroup.transvection h01 (1 : ZMod 2))
  have htQ : SpecialLinearGroup.transvection h01 (1 : ZMod 2) ∈
      flagStabilizer 5 (ZMod 2) {1, 2} := by
    refine mem_flagStabilizer_of_entries fun k l c hc hl hk => ?_
    refine transvection_entry h01 (fun h => by subst h; omega) fun ⟨h1, h2⟩ => ?_
    subst h1 h2
    rcases hc with rfl | rfl <;> simp at hl hk
  have hτY : (τ : A) ∈ Y := mem_of_img_mem hkerθ (hZ ▸ bot_le) (by rw [hτ, hQ]; exact htQ)
  have hτO : (τ : A) ∈ pCoreOf 2 Y := by
    refine mem_pCoreOf_of_blkAt hYK (by norm_num) h2 θ hθ.1 hQ
      (blockLeft_of_stabilizer fun g hg => mem_flagStabilizer.1 hg 2 (by simp))
      (blockRight_top _ rfl) (fun g hg hb => mem_unitriangular_of_upper g fun i j hji => ?_)
      τ.2 hτY ?_
    · have hji' := Fin.lt_def.1 hji
      by_cases hi : 2 ≤ (i : ℕ)
      · by_cases hj : 2 ≤ (j : ℕ)
        · have := congrFun (congrFun hb ⟨(i : ℕ) - 2, by omega⟩) ⟨(j : ℕ) - 2, by omega⟩
          rw [blkAt_apply, Matrix.one_apply_ne (fun h => by
            have := congrArg Fin.val h; simp at this; omega)] at this
          have ei : (⟨2 + ((i : ℕ) - 2), by omega⟩ : Fin 5) = i := Fin.ext (by simp; omega)
          have ej : (⟨2 + ((j : ℕ) - 2), by omega⟩ : Fin 5) = j := Fin.ext (by simp; omega)
          rwa [ei, ej] at this
        · exact stabilizer_entries (mem_flagStabilizer.1 hg 2 (by simp)) (by omega) hi
      · exact stabilizer_entries (mem_flagStabilizer.1 hg 1 (by simp)) (by omega) (by omega)
    · show blkAt 2 3 h2 ((θ τ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = 1
      rw [hτ, CFSG.LinearGroups.coe_transvection]
      ext i j
      fin_cases i <;> fin_cases j <;> rfl
  have hsh : ∀ v : ↥V, Shape 2 2 (mV hD hM₀K θ v) := fun v => by
    obtain ⟨-, -, hcc, hd⟩ := data_of_mem hD hM₀K h2 θ α hker hblk hcross v.2
    exact ⟨fun i j hj => col_std hcc hd j (Or.inl ⟨hj, by omega, by omega⟩) i,
      fun i j hi => row_std hcc hd i (Or.inl ⟨hi, by omega, by omega⟩) j⟩
  have hrow1 : ∀ v : ↥V, rowC (mV hD hM₀K θ v) 1 = 0 := by
    intro v
    obtain ⟨-, -, -, hd⟩ := data_of_mem hD hM₀K h2 θ α hker hblk hcross v.2
    have hcomm : (τ : A) * v = v * τ :=
      Subgroup.mem_centralizer_iff.1 (hD.V_le_center v.2).2 _ hτO
    have h1 : θ τ * θ ⟨v, hM₀K (hD.V_le v.2)⟩ = θ ⟨v, hM₀K (hD.V_le v.2)⟩ * θ τ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hcomm
    rw [hτ] at h1
    have h2' := congrArg (fun z : SpecialLinearGroup (Fin 5) (ZMod 2) =>
      (z : Matrix (Fin 5) (Fin 5) (ZMod 2))) h1
    simp only [Matrix.SpecialLinearGroup.coe_mul, CFSG.LinearGroups.coe_transvection] at h2'
    have h3 := ((commute_single_iff (mV hD hM₀K θ v)).1 h2'.symm).2.1
    have hd' : mV hD hM₀K θ v 1 1 = 1 := hd 1
    funext j
    rw [rowC_apply]
    by_cases hj : j = 1
    · subst hj
      rw [hd', ite_eq_left rfl, sub_self]
      rfl
    · rw [h3 j hj, ite_eq_right_iff.2 fun h => absurd h.symm hj, sub_self]
      rfl
  set i₀ : Fin 5 := 0 with hi₀
  have hrow0 : ∀ (v : ↥V) (j : Fin 5), (j : ℕ) < 2 → rowC (mV hD hM₀K θ v) i₀ j = 0 :=
    fun v j hj => rowC_eq_zero (hsh v) i₀ j hj
  let β : ↥V →* Multiplicative (Fin 3 → ZMod 2) :=
    { toFun := fun v => Multiplicative.ofAdd (restrictBlk 2 3 h2 (rowC (mV hD hM₀K θ v) i₀))
      map_one' := by
        rw [mV_one]
        apply Multiplicative.toAdd.injective
        funext i
        simp [rowC, restrictBlk]
      map_mul' := fun u v => by
        rw [mV_mul, rowC_mul (hsh u) (hsh v)]
        rfl }
  have hβv : ∀ v, Multiplicative.toAdd (β v) = restrictBlk 2 3 h2 (rowC (mV hD hM₀K θ v) i₀) :=
    fun v => rfl
  have hinvM : ∀ x : ↥M₀, ((θ ⟨x, hM₀K x.2⟩)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) =
      θ ⟨(x⁻¹ : ↥M₀), hM₀K x⁻¹.2⟩ := fun x => by rw [← map_inv]; rfl
  have hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = (((α a)⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) :
        Matrix (Fin 3) (Fin 3) (ZMod 2))ᵀ *ᵥ Multiplicative.toAdd (β u) := by
    intro a u v huv
    have hg : ∀ i j : Fin 5, (i : ℕ) < 2 → (j : ℕ) < 2 →
        ((θ ⟨a, hM₀K a.2⟩ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
          Matrix (Fin 5) (Fin 5) (ZMod 2)) i j = if i = j then 1 else 0 :=
      fun i j hi hj => (hblk a).2.2.2.1 i j hi hj
    have hbf : BlockForm 2 3 (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) := by
      rw [hinvM]
      exact (hblk a⁻¹).2
    have hbl : blkAt 2 3 h2 (((θ ⟨a, hM₀K a.2⟩)⁻¹ : SpecialLinearGroup (Fin 5) (ZMod 2)) :
        Matrix (Fin 5) (Fin 5) (ZMod 2)) = (((α a)⁻¹ : SpecialLinearGroup (Fin 3) (ZMod 2)) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) := by
      rw [hinvM, (hblk a⁻¹).1, map_inv]
    rw [hβv, hβv, mV_conj hD hM₀K θ a u v huv, rowC_conj _ hg (hsh u) i₀ (by simp [hi₀]),
      ← hbl]
    exact (transpose_mulVec_of_blockForm_blk h2 hbf fun j hj => by
      rcases hj with hj | hj
      · exact hrow0 u j hj
      · omega).2
  have hβi : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro v hv
    have h0' : rowC (mV hD hM₀K θ v) i₀ = rowC 1 i₀ := by
      refine eq_of_restrictBlk_last h2 rfl (hrow0 v) (fun j _ => by simp [rowC]) ?_
      have := congrArg Multiplicative.toAdd hv
      rw [hβv] at this
      rw [this]
      funext i
      simp [rowC, restrictBlk]
    have h3 : mV hD hM₀K θ v = 1 := eq_of_rowC (hsh v) shape_one fun i hi => by
      rcases (by omega : (i : ℕ) = 0 ∨ (i : ℕ) = 1) with h | h
      · have : i = i₀ := Fin.ext h
        rw [this, h0']
      · have : i = 1 := Fin.ext h
        rw [this, hrow1]
        funext j
        simp [rowC]
    have h4 : θ ⟨v, hM₀K (hD.V_le v.2)⟩ = 1 := Subtype.ext h3
    have h5 := hθ.1 (h4.trans (map_one θ).symm)
    have h6 : (v : A) = 1 := congrArg (fun z : ↥K => (z : A)) h5
    exact Subtype.ext h6
  have hMV := le_normalizer_of_comm hD.V_comm
  have hβs : Function.Surjective β := by
    let W : AddSubgroup (Fin 3 → ZMod 2) :=
      { carrier := {w | ∃ v, Multiplicative.toAdd (β v) = w}
        add_mem' := by
          rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
          exact ⟨u * v, by rw [map_mul, toAdd_mul]⟩
        zero_mem' := ⟨1, by rw [map_one, toAdd_one]⟩
        neg_mem' := by
          rintro _ ⟨u, rfl⟩
          exact ⟨u⁻¹, by rw [map_inv, toAdd_inv]⟩ }
    have hW : W ≠ ⊥ := by
      intro hW
      apply hD.V_ne
      rw [eq_bot_iff]
      intro v hv
      have h1' : Multiplicative.toAdd (β ⟨v, hv⟩) ∈ W := ⟨⟨v, hv⟩, rfl⟩
      rw [hW, AddSubgroup.mem_bot] at h1'
      have h2' : β ⟨v, hv⟩ = β 1 := by
        rw [map_one]
        exact Multiplicative.toAdd.injective h1'
      exact congrArg Subtype.val (hβi h2')
    have hinv : ∀ r s : Fin 3, r ≠ s → ∀ w ∈ W, (1 + Matrix.single r s (1 : ZMod 2)) *ᵥ w ∈ W := by
      rintro r s hrs _ ⟨u, rfl⟩
      obtain ⟨a, ha⟩ := hαs (SpecialLinearGroup.transvection (Ne.symm hrs) (1 : ZMod 2))⁻¹
      have hmem : (a : A) * u * (a : A)⁻¹ ∈ V :=
        (Subgroup.mem_normalizer_iff.1 (hMV a.2) u).1 u.2
      refine ⟨⟨_, hmem⟩, ?_⟩
      rw [hequiv a u ⟨_, hmem⟩ rfl, ha, inv_inv, CFSG.LinearGroups.coe_transvection,
        Matrix.transpose_add, Matrix.transpose_one, Matrix.transpose_single]
    have htop := eq_top_of_transvection_invariant (by norm_num) W hW hinv
    intro y
    have hy : Multiplicative.toAdd y ∈ W := by
      rw [htop]
      exact AddSubgroup.mem_top _
    obtain ⟨v, hv⟩ := hy
    exact ⟨v, Multiplicative.toAdd.injective hv⟩
  refine ⟨isPSL_of_mulEquiv_sl (by norm_num) (MulEquiv.ofBijective θ hθ),
    ⟨CFSG.pCore 2 ↥M₀, CFSG.pCore_normal,
      isE2_pCore_113 hM₀K h2 θ hθ.1 α hker hblk hcross,
      isPSL_of_mulEquiv_sl le_rfl ((QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hαs))⟩,
    isNaturalSection_of_bij_dual hMV α hαs hker β ⟨hβi, hβs⟩ hequiv,
    forallQ_113 hD hM₀K hc0 θ hθ.1 hQ hM⟩

theorem false_of_extra {K Y M₀ V : Subgroup A} (hD : C35Data K Y M₀ V) (hM₀K : M₀ ≤ K)
    (hc0 : Subgroup.center ↥K = ⊥) {n a m : ℕ} (h : a + m ≤ n)
    (θ : ↥K →* SpecialLinearGroup (Fin n) (ZMod 2)) (hθ : Function.Bijective θ)
    (α : ↥M₀ →* SpecialLinearGroup (Fin m) (ZMod 2)) (hker : α.ker = CFSG.pCore 2 ↥M₀)
    (hblk : ∀ x : ↥M₀,
      blkAt a m h ((θ ⟨x, hM₀K x.2⟩ : SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
          ((α x : SpecialLinearGroup (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2)))
    {I : Set ℕ} (hQ : img θ Y = flagStabilizer n (ZMod 2) I)
    (hL : BlockLeft (flagStabilizer n (ZMod 2) I) a m)
    (hR : BlockRight (flagStabilizer n (ZMod 2) I) a m)
    (t s : SpecialLinearGroup (Fin n) (ZMod 2)) (htQ : t ∈ flagStabilizer n (ZMod 2) I)
    (hsQ : s ∈ flagStabilizer n (ZMod 2) I)
    (htb : blkAt a m h (t : Matrix (Fin n) (Fin n) (ZMod 2)) = 1) (ht2 : t * t = 1)
    (h3 : (t * (s * t * s⁻¹)) ^ 3 = 1) (h1 : t * (s * t * s⁻¹) ≠ 1) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ := centerOf_eq_bot hc0
  have hkerθ : θ.ker ≤ Subgroup.center ↥K := by
    rw [(MonoidHom.ker_eq_bot_iff θ).2 hθ.1]
    exact bot_le
  have hYK : Y ≤ K := hD.parabolic.1
  have hYN : Y ≤ Subgroup.normalizer (M₀ : Set A) := by
    rw [hD.eq_perfectCore]
    exact Subgroup.le_normalizer.trans (normalizer_le_normalizer_perfectCore Y)
  obtain ⟨τ, hτ⟩ := hθ.2 t
  obtain ⟨σ, hσ⟩ := hθ.2 s
  have hτY : (τ : A) ∈ Y := mem_of_img_mem hkerθ (hZ ▸ bot_le) (by rw [hτ, hQ]; exact htQ)
  have hσY : (σ : A) ∈ Y := mem_of_img_mem hkerθ (hZ ▸ bot_le) (by rw [hσ, hQ]; exact hsQ)
  have hSN : Y ≤ Subgroup.normalizer (pCoreOf 2 Y : Set A) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hτS : (τ : A) ∉ pCoreOf 2 Y := by
    intro hτS
    have h1' : (σ : A) * τ * (σ : A)⁻¹ ∈ pCoreOf 2 Y :=
      (Subgroup.mem_normalizer_iff.1 (hSN hσY) τ).1 hτS
    have hx : (τ : A) * ((σ : A) * τ * (σ : A)⁻¹) ∈ pCoreOf 2 Y := (pCoreOf 2 Y).mul_mem hτS h1'
    set x : ↥K := τ * (σ * τ * σ⁻¹) with hxdef
    have hθx : θ x = t * (s * t * s⁻¹) := by rw [hxdef, map_mul, map_mul, map_mul, map_inv, hτ, hσ]
    have hx3 : x ^ 3 = 1 := hθ.1 (by rw [map_pow, hθx, h3, map_one])
    have hx1 : x ≠ 1 := fun hx1 => h1 (by rw [← hθx, hx1, map_one])
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y) ⟨_, hx⟩
    have hxk : x ^ 2 ^ k = 1 := Subtype.ext (by
      have := congrArg Subtype.val hk
      simpa [hxdef] using this)
    have hdvd : orderOf x ∣ Nat.gcd (2 ^ k) 3 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hxk) (orderOf_dvd_of_pow_eq_one hx3)
    rw [(Nat.Coprime.pow_left k (by norm_num : Nat.Coprime 2 3)), Nat.dvd_one,
      orderOf_eq_one_iff] at hdvd
    exact hx1 hdvd
  have hmemQ : ∀ x (hx : x ∈ Y), θ ⟨x, hYK hx⟩ ∈ flagStabilizer n (ZMod 2) I :=
    fun x hx => hQ ▸ ⟨⟨x, hYK hx⟩, hx, rfl⟩
  have hblkmul : ∀ g g' : SpecialLinearGroup (Fin n) (ZMod 2), g ∈ flagStabilizer n (ZMod 2) I →
      g' ∈ flagStabilizer n (ZMod 2) I →
      blkAt a m h (((g * g' : SpecialLinearGroup (Fin n) (ZMod 2))) :
        Matrix (Fin n) (Fin n) (ZMod 2)) =
        blkAt a m h (g : Matrix (Fin n) (Fin n) (ZMod 2)) *
          blkAt a m h (g' : Matrix (Fin n) (Fin n) (ZMod 2)) := fun g g' hg hg' => by
    rw [Matrix.SpecialLinearGroup.coe_mul]
    exact blkAt_mul a m h _ _ (hL g hg) (hR g' hg')
  have htinv : t⁻¹ = t := by
    rw [inv_eq_iff_mul_eq_one]
    exact ht2
  have hτC : (τ : A) ∈ centralizerSection K M₀ (pCoreOf 2 M₀) := by
    refine ⟨τ.2, hYN hτY, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 M₀ (hYN hτY),
      fun x hx => ?_⟩
    have hMY : M₀ ≤ Y := hD.eq_perfectCore ▸ perfectCore_le Y
    have hxY : x ∈ Y := hMY hx
    have hz : x * (τ : A) * x⁻¹ * (τ : A)⁻¹ ∈ M₀ := by
      have h1' : (τ : A) * x⁻¹ * (τ : A)⁻¹ ∈ M₀ :=
        (Subgroup.mem_normalizer_iff.1 (hYN hτY) x⁻¹).1 (M₀.inv_mem hx)
      have e : x * (τ : A) * x⁻¹ * (τ : A)⁻¹ = x * ((τ : A) * x⁻¹ * (τ : A)⁻¹) := by group
      rw [e]
      exact M₀.mul_mem hx h1'
    have hθz : θ ⟨x * (τ : A) * x⁻¹ * (τ : A)⁻¹, hM₀K hz⟩ =
        θ ⟨x, hYK hxY⟩ * t * θ ⟨x⁻¹, hYK (Y.inv_mem hxY)⟩ * t⁻¹ := by
      rw [← hτ, ← map_inv, ← map_mul, ← map_mul, ← map_mul]
      try rfl
    have hbz : blkAt a m h ((θ ⟨x * (τ : A) * x⁻¹ * (τ : A)⁻¹, hM₀K hz⟩ :
        SpecialLinearGroup (Fin n) (ZMod 2)) :
        Matrix (Fin n) (Fin n) (ZMod 2)) = 1 := by
      have hxQ := hmemQ x hxY
      have hxiQ := hmemQ x⁻¹ (Y.inv_mem hxY)
      rw [hθz, htinv, hblkmul _ _ ((flagStabilizer n (ZMod 2) I).mul_mem
        ((flagStabilizer n (ZMod 2) I).mul_mem hxQ htQ) hxiQ) htQ,
        hblkmul _ _ ((flagStabilizer n (ZMod 2) I).mul_mem hxQ htQ) hxiQ,
        hblkmul _ _ hxQ htQ, htb, mul_one, mul_one, ← hblkmul _ _ hxQ hxiQ, ← map_mul]
      rw [show (⟨x, hYK hxY⟩ * ⟨x⁻¹, hYK (Y.inv_mem hxY)⟩ : ↥K) = 1 from
        Subtype.ext (mul_inv_cancel x), map_one, Matrix.SpecialLinearGroup.coe_one]
      exact blkAt_one a m h
    have hα1 : α ⟨_, hz⟩ = 1 := by
      apply Subtype.ext
      rw [← hblk ⟨_, hz⟩, Matrix.SpecialLinearGroup.coe_one]
      exact hbz
    have hmem : (⟨_, hz⟩ : ↥M₀) ∈ CFSG.Open.pCore 2 ↥M₀ := by
      rw [← hker]
      exact hα1
    exact ⟨_, hmem, rfl⟩
  obtain ⟨hSC, hSp, hidx⟩ := hD.sylow
  have hτN : Subgroup.zpowers (τ : A) ≤ Subgroup.normalizer (pCoreOf 2 Y : Set A) :=
    (Subgroup.zpowers_le_of_mem hτY).trans hSN
  have hτp : IsPGroup 2 ↥(Subgroup.zpowers (τ : A)) := by
    have hτ2 : (τ : A) ^ 2 = 1 := by
      have : θ (τ ^ 2) = θ 1 := by rw [map_pow, hτ, pow_two, ht2, map_one]
      have := congrArg Subtype.val (hθ.1 this)
      simpa using this
    exact IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, orderOf_eq_prime hτ2 (fun h => hτS (h ▸ (pCoreOf 2 Y).one_mem))]
      norm_num)
  have hS'p := IsPGroup.to_sup_of_normal_left' hSp hτp hτN
  have hS'C : pCoreOf 2 Y ⊔ Subgroup.zpowers (τ : A) ≤
      centralizerSection K M₀ (pCoreOf 2 M₀) :=
    sup_le hSC ((Subgroup.zpowers_le_of_mem hτC))
  have hpS : IsPGroup 2 ↥((pCoreOf 2 Y).subgroupOf (centralizerSection K M₀ (pCoreOf 2 M₀))) :=
    hSp.of_equiv (Subgroup.subgroupOfEquivOfLe hSC).symm
  set P := hpS.toSylow hidx
  have hQp : IsPGroup 2 ↥((pCoreOf 2 Y ⊔ Subgroup.zpowers (τ : A)).subgroupOf
      (centralizerSection K M₀ (pCoreOf 2 M₀))) :=
    hS'p.of_equiv (Subgroup.subgroupOfEquivOfLe hS'C).symm
  have hle : (P : Subgroup ↥(centralizerSection K M₀ (pCoreOf 2 M₀))) ≤
      (pCoreOf 2 Y ⊔ Subgroup.zpowers (τ : A)).subgroupOf
        (centralizerSection K M₀ (pCoreOf 2 M₀)) := fun y hy =>
    Subgroup.mem_subgroupOf.2 (le_sup_left (a := pCoreOf 2 Y) (Subgroup.mem_subgroupOf.1 hy))
  have heq := P.is_maximal' hQp hle
  have hτmem : (⟨τ, hτC⟩ : ↥(centralizerSection K M₀ (pCoreOf 2 M₀))) ∈
      (pCoreOf 2 Y ⊔ Subgroup.zpowers (τ : A)).subgroupOf
        (centralizerSection K M₀ (pCoreOf 2 M₀)) :=
    Subgroup.mem_subgroupOf.2 ((le_sup_right : Subgroup.zpowers (τ : A) ≤ pCoreOf 2 Y ⊔ _)
      (Subgroup.mem_zpowers _))
  rw [heq] at hτmem
  exact hτS (Subgroup.mem_subgroupOf.1 hτmem)

end CFSG.Quasithin.C35Pf
