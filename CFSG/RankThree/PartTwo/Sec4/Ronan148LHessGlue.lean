module

public import CFSG.RankThree.PartTwo.Sec4.Ronan148LHessPair
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LHessMats

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open Matrix CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4.Ronan148B
open CFSG.PGLModel (projImage)
open CFSG.Open (pCoreOf)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

section Normalizer

variable {X : Type} [Group X] [Finite X]

theorem mem_normalizer_of_map_conj_eq {H : Subgroup X} {g : X}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ Subgroup.normalizer (H : Set X) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h] at hy
    obtain ⟨z, hz, hzy⟩ := hy
    have hzy' : z = y := (MulAut.conj g).injective (hzy.trans (MulAut.conj_apply g y).symm)
    rwa [← hzy']

theorem map_conj_sup_zpowers (g a b : X) :
    (Subgroup.zpowers a ⊔ Subgroup.zpowers b).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * a * g⁻¹) ⊔ Subgroup.zpowers (g * b * g⁻¹) := by
  rw [Subgroup.map_sup, map_conj_zpowers, map_conj_zpowers]

theorem isPGroup_two_zpowers {t : X} (ht : t * t = 1) : IsPGroup 2 (Subgroup.zpowers t) := by
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  refine ⟨1, Subtype.ext ?_⟩
  change (t ^ k) ^ 2 ^ 1 = 1
  rw [pow_one, ← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, sq, ht,
    _root_.one_zpow]

end Normalizer

@[expose] noncomputable def pimHom (π : Bool) (q : ℕ) (K : Type) [Field K] :
    slPi π 3 q K →* projImage (slPi π 3 q K) :=
  (ProjGenLinGroup.mk.comp (slPi π 3 q K).subtype).codRestrict _
    fun x => Subgroup.mem_map_of_mem _ x.2

theorem hessPair_of_hessPhiMemClosure (hF : HessPhiMemClosure) {X : Type} [Group X] [Finite X]
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hp2 : p ≠ 2) (hiso : Sec4.IsoLThreePi X p e)
    {E : Subgroup X} (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
    (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
      ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
    {b b' : X} (hbE : b ∈ E) (hb1 : b ≠ 1) (hb'E : b' ∈ E) (hb'1 : b' ≠ 1)
    (hbb' : Subgroup.zpowers b ≠ Subgroup.zpowers b') : HessPair E b b' := by
  obtain ⟨π, K, _, hK, hq, τ, hτ, hτ1, dM, cM, hdM, hcM, hdc, hdo, hco, hcd, Φ, hΦE⟩ :=
    Sec14.Res8Hess.exists_hessian_equiv he hiso hEe hE9 htr
  have hπ : π = false → UnitaryFieldData p e K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ e) := fun h => by subst h; exact hq
  have : CharP K p := hK.charP
  have hp3 : 3 < p := three_lt_of_isoLThreePi he hp2 hiso
  have hp5 : 5 ≤ p := by
    have hp4 : p ≠ 4 := fun h => by
      have := (Fact.out : p.Prime)
      rw [h] at this
      norm_num at this
    omega
  have h3 : (3 : K) ≠ 0 := hK.three_ne_zero hq
  have h2 : (2 : K) ≠ 0 := by
    intro h
    have hp2' : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).mp (by exact_mod_cast h)
    have := Nat.le_of_dvd (by norm_num) hp2'
    omega
  have hω : τ ^ 2 + τ + 1 = 0 := by
    have h : (τ - 1) * (τ ^ 2 + τ + 1) = 0 := by linear_combination hτ
    exact (mul_eq_zero.mp h).resolve_left (sub_ne_zero.mpr hτ1)
  set ρ : slPi π 3 (p ^ e) K →* X := Φ.toMonoidHom.comp (pimHom π (p ^ e) K) with hρ
  set dS : slPi π 3 (p ^ e) K := ⟨diagTau hτ, diagTau_mem_slPi hπ hq' hτ⟩ with hdS
  set cS : slPi π 3 (p ^ e) K := ⟨cycThree, cycThree_mem_slPi hπ⟩ with hcS
  set tS : Fin 3 → slPi π 3 (p ^ e) K := fun i => ⟨hessT i, hessT_mem_slPi hπ i⟩ with htS
  set φS : slPi π 3 (p ^ e) K := ⟨hessPhi hω h3, hessPhi_mem_slPi hπ hq' hω h3⟩ with hφS
  have hpd : pimHom π (p ^ e) K dS = dM := Subtype.ext hdM.symm
  have hpc : pimHom π (p ^ e) K cS = cM := Subtype.ext hcM.symm
  set d := Φ dM with hd
  set c := Φ cM with hc
  have hρd : ρ dS = d := by rw [hρ, MonoidHom.comp_apply, hpd]; rfl
  have hρc : ρ cS = c := by rw [hρ, MonoidHom.comp_apply, hpc]; rfl
  set t : Fin 3 → X := fun i => ρ (tS i) with ht
  set n₀ := ρ φS with hn₀
  have hF1 : ∀ i, t i * d = d * t i := fun i => by
    rw [ht, ← hρd, ← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext (hessT_mul_diagTau hτ i))
  have hF2a : c * t 0 = t 1 * c := by
    rw [ht, ← hρc, ← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext cycThree_mul_hessT_zero)
  have hF2b : c * t 1 = t 2 * c := by
    rw [ht, ← hρc, ← map_mul, ← map_mul]
    exact congrArg ρ (Subtype.ext cycThree_mul_hessT_one)
  have hF3 : t 0 * t 1 = t 2 := by
    rw [ht, ← map_mul]
    exact congrArg ρ (Subtype.ext hessT_zero_mul_one)
  have hF3' : t 1 * t 0 = t 2 := by
    rw [ht, ← map_mul]
    exact congrArg ρ (Subtype.ext hessT_one_mul_zero)
  have hF4 : ∀ i, t i * t i = 1 := fun i => by
    rw [ht, ← map_mul]
    have : tS i * tS i = 1 := Subtype.ext (hessT_mul_self i)
    rw [this, map_one]
  have hF5 : t 0 ≠ 1 := by
    intro h
    have h' : pimHom π (p ^ e) K (tS 0) = 1 := by
      apply Φ.injective
      rw [map_one]
      exact h
    exact mk_hessT_zero_ne_one h2 (congrArg Subtype.val h')
  have hF6a : n₀ * d * n₀⁻¹ = c⁻¹ := by
    have hm : pimHom π (p ^ e) K φS * dM * (pimHom π (p ^ e) K φS)⁻¹ = cM⁻¹ := by
      apply Subtype.ext
      change ProjGenLinGroup.mk (hessPhi hω h3) * (dM : ProjGenLinGroup (Fin 3) K) *
        (ProjGenLinGroup.mk (hessPhi hω h3))⁻¹ = (cM : ProjGenLinGroup (Fin 3) K)⁻¹
      rw [hdM, hcM]
      exact mk_hessPhi_conj_diagTau hτ hω h3
    have h := congrArg Φ hm
    rw [map_mul, map_mul, map_inv, map_inv] at h
    exact h
  have hF6b : n₀ * c * n₀⁻¹ = d := by
    have hm : pimHom π (p ^ e) K φS * cM * (pimHom π (p ^ e) K φS)⁻¹ = dM := by
      apply Subtype.ext
      change ProjGenLinGroup.mk (hessPhi hω h3) * (cM : ProjGenLinGroup (Fin 3) K) *
        (ProjGenLinGroup.mk (hessPhi hω h3))⁻¹ = (dM : ProjGenLinGroup (Fin 3) K)
      rw [hdM, hcM]
      exact mk_hessPhi_conj_cycThree hτ hω h3
    have h := congrArg Φ hm
    rw [map_mul, map_mul, map_inv] at h
    exact h
  have hE : E = Subgroup.zpowers d ⊔ Subgroup.zpowers c := by
    rw [← hΦE, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hdcX : d * c = c * d := by rw [hd, hc, ← map_mul, hdc, map_mul]
  have hd3 : d ^ 3 = 1 := by
    have h : dM ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hdo])
    rw [hd, ← map_pow, h, map_one]
  have hc3 : c ^ 3 = 1 := by
    have h : cM ^ 3 = 1 := orderOf_dvd_iff_pow_eq_one.mp (by rw [hco])
    rw [hc, ← map_pow, h, map_one]
  have hd1 : d ≠ 1 := by
    intro h
    have hdM1 : dM = 1 := Φ.injective (by rw [map_one]; exact h)
    rw [hdM1, orderOf_one] at hdo
    omega
  have hdE : d ∈ E := hE ▸ Subgroup.mem_sup_left (Subgroup.mem_zpowers d)
  set W := Subgroup.zpowers (t 0) ⊔ Subgroup.zpowers (t 1) with hW
  have ht2W : t 2 ∈ W := hF3 ▸ W.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
  have hW2 : IsPGroup 2 W := by
    refine IsPGroup.to_sup_of_normal_right' (isPGroup_two_zpowers (hF4 0))
      (isPGroup_two_zpowers (hF4 1)) (Subgroup.zpowers_le.mpr ?_)
    refine mem_normalizer_of_map_conj_eq ?_
    rw [map_conj_zpowers]
    congr 1
    rw [hF3, ← hF3', mul_assoc, mul_inv_cancel, mul_one]
  have hEW : E ≤ Subgroup.normalizer (W : Set X) := by
    rw [hE]
    refine sup_le (Subgroup.zpowers_le.mpr (mem_normalizer_of_map_conj_eq ?_))
      (Subgroup.zpowers_le.mpr (mem_normalizer_of_map_conj_eq ?_))
    · rw [hW, map_conj_sup_zpowers]
      have h0 : d * t 0 * d⁻¹ = t 0 := by rw [← hF1, mul_assoc, mul_inv_cancel, mul_one]
      have h1 : d * t 1 * d⁻¹ = t 1 := by rw [← hF1, mul_assoc, mul_inv_cancel, mul_one]
      rw [h0, h1]
    · rw [hW, map_conj_sup_zpowers]
      have h0 : c * t 0 * c⁻¹ = t 1 := by rw [hF2a, mul_assoc, mul_inv_cancel, mul_one]
      have h1 : c * t 1 * c⁻¹ = t 2 := by rw [hF2b, mul_assoc, mul_inv_cancel, mul_one]
      rw [h0, h1]
      refine le_antisymm (sup_le le_sup_right (Subgroup.zpowers_le.mpr ht2W))
        (sup_le (Subgroup.zpowers_le.mpr ?_) le_sup_left)
      have : t 0 = t 2 * (t 1)⁻¹ := by rw [← hF3, mul_assoc, mul_inv_cancel, mul_one]
      rw [this]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
  obtain ⟨b₀, hb₀E, hb₀1, hWb₀⟩ := hessU_exists he hp2 hiso hEe hE9 htr hW2 hEW
  have hdb₀ : d ∈ Subgroup.zpowers b₀ := by
    by_contra hdb
    refine hF5 (hessU_fixed he hp2 hiso hEe hE9 htr hb₀E hb₀1 hdE hdb (t 0)
      (hWb₀ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))) ?_)
    rw [← hF1, mul_assoc, mul_inv_cancel, mul_one]
  have hzb₀ : Subgroup.zpowers d = Subgroup.zpowers b₀ :=
    TauCeti.zpowers_eq_zpowers_of_mem_zpowers Nat.prime_three (hEe.2 b₀ hb₀E) hd1 hdb₀
  have hWd : W ≤ pCoreOf 2 (Subgroup.centralizer ({d} : Set X)) := by
    rw [centralizer_singleton_eq_of_zpowers_eq hzb₀]
    exact hWb₀
  have htW : ∀ i, t i ∈ W := fun i => by
    fin_cases i
    · exact Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers _)
    · exact ht2W
  have htInv : ∀ i, t i ∈ hessInv d := fun i => ⟨hWd (htW i), by rw [sq]; exact hF4 i⟩
  have hsInv : ∀ k, n₀ * t k * n₀⁻¹ ∈ hessInv c := fun k => by
    have hU : (pCoreOf 2 (Subgroup.centralizer ({d} : Set X))).map
        (MulAut.conj n₀).toMonoidHom = pCoreOf 2 (Subgroup.centralizer ({c} : Set X)) := by
      rw [map_conj_hessU, hF6a, centralizer_singleton_eq_of_zpowers_eq Subgroup.zpowers_inv]
    refine ⟨hU ▸ ⟨t k, (htInv k).1, rfl⟩, ?_⟩
    rw [sq, show n₀ * t k * n₀⁻¹ * (n₀ * t k * n₀⁻¹) = n₀ * (t k * t k) * n₀⁻¹ by group, hF4 k,
      mul_one, mul_inv_cancel]
  have hn₀cl : n₀ ∈ Subgroup.closure (hessInv d ∪ hessInv c) := by
    have hFK := hF K p hp5 τ hω h3
    set Y : Subgroup (GL (Fin 3) K) :=
      ((Subgroup.closure (hessInv d ∪ hessInv c)).comap ρ).map (slPi π 3 (p ^ e) K).subtype
    have hSY : Set.range (hessT (F := K)) ∪
        Set.range (fun k => hessPhi hω h3 * hessT k * (hessPhi hω h3)⁻¹) ⊆ (Y : Set _) := by
      rintro _ (⟨i, rfl⟩ | ⟨k, rfl⟩)
      · exact ⟨tS i, Subgroup.subset_closure (Or.inl (htInv i)), rfl⟩
      · refine ⟨φS * tS k * φS⁻¹, Subgroup.subset_closure (Or.inr ?_), rfl⟩
        rw [map_mul, map_mul, map_inv]
        exact hsInv k
    obtain ⟨y, hy, hyeq⟩ := (Subgroup.closure_le Y).mpr hSY hFK
    have hyφ : y = φS := Subtype.ext hyeq
    rw [hyφ] at hy
    exact hy
  have hn₀N : n₀ ∈ Subgroup.normalizer (E : Set X) := by
    refine mem_normalizer_of_map_conj_eq ?_
    rw [hE, map_conj_sup_zpowers, hF6a, hF6b, Subgroup.zpowers_inv, sup_comm]
  have hbase : HessPair E d c :=
    ⟨n₀, Subgroup.mem_inf.mpr ⟨hn₀cl, hn₀N⟩, by rw [hF6a, Subgroup.zpowers_inv]⟩
  set δ := Sec14.Res8Hess.conjM' hπ (diagOneOneTau_mem_glPi hπ hq' hτ) with hδ
  have hδd : δ dM = dM := by
    apply Subtype.ext
    rw [hδ, Sec14.Res8Hess.coe_conjM', hdM, ← map_mul, ← map_inv, ← map_mul,
      diagOneOneTau_mul_diagTau, mul_assoc, mul_inv_cancel, mul_one]
  have hδc : δ cM = cM * dM := by
    apply Subtype.ext
    rw [hδ, Sec14.Res8Hess.coe_conjM', hcM, Subgroup.coe_mul, hcM, hdM]
    exact mk_diagOneOneTau_conj_cycThree hτ
  set α : MulAut X := (Φ.symm.trans δ).trans Φ with hα
  have hαd : α d = d := by
    rw [hα, hd]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hδd]
  have hαc : α c = c * d := by
    rw [hα, hc, hd]
    simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply, hδc, map_mul]
  have hαE : E.map α.toMonoidHom = E := by
    rw [hE, Subgroup.map_sup, map_mulAut_zpowers, map_mulAut_zpowers, hαd, hαc]
    refine le_antisymm (sup_le le_sup_left (Subgroup.zpowers_le.mpr
      (Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))))
      (sup_le le_sup_left (Subgroup.zpowers_le.mpr ?_))
    have h : c * d * d⁻¹ ∈ Subgroup.zpowers d ⊔ Subgroup.zpowers (c * d) :=
      Subgroup.mul_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))
        (Subgroup.inv_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)))
    rwa [mul_inv_cancel_right] at h
  have hshift : ∀ k : ℕ, HessPair E d (c * d ^ k) := by
    intro k
    induction k with
    | zero => simpa using hbase
    | succ k ih =>
      have h := ih.map α hαE
      rwa [map_mul, map_pow, hαd, hαc, mul_assoc, ← pow_succ'] at h
  exact hessPair_of_transitive hE hdcX hd3 hc3 hd1 htr hshift hbE hb1 hb'E hb'1 hbb'

theorem hessCore_of_hessPhiMemClosure (hF : HessPhiMemClosure) :
    ∀ (X : Type) [Group X] [Finite X] (p e : ℕ) [Fact p.Prime] (he : 1 ≤ e)
      (hp2 : p ≠ 2) (hiso : Sec4.IsoLThreePi X p e) (E : Subgroup X)
      (hEe : CFSG.Assembly.IsElemAbelian 3 E) (hE9 : Nat.card E = 9)
      (htr : ∀ y₀ ∈ E, y₀ ≠ 1 → ∀ y₁ ∈ E, y₁ ≠ 1 →
        ∃ w ∈ Subgroup.normalizer (E : Set X), w * y₀ * w⁻¹ = y₁)
      (b : X) (hbE : b ∈ E) (hb1 : b ≠ 1) (b' : X) (hb'E : b' ∈ E) (hb'1 : b' ≠ 1),
      Subgroup.zpowers b ≠ Subgroup.zpowers b' →
        ∃ n ∈ (layer (pCoreOf 2 (Subgroup.centralizer ({b} : Set X)))
                (hessU_comm he hp2 hiso hEe hE9 htr hbE hb1) 1 ⊔
              layer (pCoreOf 2 (Subgroup.centralizer ({b'} : Set X)))
                (hessU_comm he hp2 hiso hEe hE9 htr hb'E hb'1) 1) ⊓
            Subgroup.normalizer (E : Set X),
          (Subgroup.zpowers b).map (MulAut.conj n).toMonoidHom = Subgroup.zpowers b' := by
  intro X _ _ p e _ he hp2 hiso E hEe hE9 htr b hbE hb1 b' hb'E hb'1 hbb'
  exact (hessPair_of_hessPhiMemClosure hF he hp2 hiso hEe hE9 htr hbE hb1 hb'E hb'1
    hbb').exists_mem_layer _ _

theorem kl3HessTori_of_hessPhiMemClosure (hF : HessPhiMemClosure) : Sec14.KL3HessTori :=
  kl3HessTori_of_core (hessCore_of_hessPhiMemClosure hF)

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
