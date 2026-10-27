module

public import CFSG.LocalAnalysis.StandardType.GGTBJD4Diag
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmCorank
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGCentOmTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmDiag
import CFSG.LocalAnalysis.StandardType.GGSecFiveJRootCoreOmEigen
import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
import CFSG.RankThree.PartOne.KC.OrthogonalFactorization

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne.KCOrthogonal CFSG.RankThree.Classical2
  Polynomial
open CFSG.StandardType.KGCentOm (kgcDiag)

private theorem ggTBJD4_ne_inv {F : Type} [Field F] [CharP F 2] {μ : Fˣ} (hμ : μ ≠ 1) :
    μ ≠ μ⁻¹ := by
  intro h
  have h3 : (μ : F) ^ 2 = 1 ^ 2 := by
    have h' : μ * μ = 1 := by
      nth_rewrite 1 [h]
      exact inv_mul_cancel μ
    rw [sq, sq, ← Units.val_mul, h', Units.val_one, one_mul]
  exact hμ (Units.ext (CharTwo.sq_injective h3))

theorem ggTBJD4_block_mult {p : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2] (hp : p.Prime)
    (hpq : p ∣ Nat.card F - 1) {u : spinGroup (quadPlus 4 F)}
    (hu : u ∈ ggTorus (plusDatum 4 F (by norm_num))) (hup : u ^ p = 1)
    {J : Subgroup (spinGroup (quadPlus 4 F))}
    (huJ : u ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus 4 F)))) {μ : Fˣ} (hμ : μ ≠ 1)
    (hh : X - C (μ : F) ∈ primaryFactors (spinAction (quadPlus 4 F) u).toLinearMap)
    (hJ : ∀ z ∈ J, spinAction (quadPlus 4 F) z ∈
      supportedBlock (quadPlus 4 F) (spinAction (quadPlus 4 F) u) (X - C (μ : F)))
    (hcount : Set.ncard {h | h ∈ ggTorus (plusDatum 4 F (by norm_num)) ∧ h ^ p = 1 ∧
      h ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus 4 F)))} ≤ p) :
    primaryMultiplicity (spinAction (quadPlus 4 F) u).toLinearMap (X - C (μ : F)) = 4 := by
  classical
  have hn4 : 3 ≤ 4 := by norm_num
  obtain ⟨a, hxa⟩ := jcoreOm_diag (n := 4) (F := F) hn4 hu
  set w : Fin 4 ⊕ Fin 4 → F := fun c => ((Sum.elim a (fun k => (a k)⁻¹) c : Fˣ) : F)
    with hw
  have hμinv : μ ≠ μ⁻¹ := ggTBJD4_ne_inv hμ
  have hW : ∀ v : Fin 4 ⊕ Fin 4 → F,
      v ∈ primaryComponent (spinAction (quadPlus 4 F) u).toLinearMap (X - C (μ : F)) ↔
        spinAction (quadPlus 4 F) u v = (μ : F) • v := by
    intro v
    rw [mem_primaryComponent, map_sub, aeval_X, aeval_C, LinearMap.sub_apply,
      Module.algebraMap_end_apply, sub_eq_zero, LinearEquiv.coe_coe]
  have hcard := jcoreOm_finrank_eigen hxa (μ : F) hW
  rw [@finrank_primaryComponent F _ (Fin 4 ⊕ Fin 4 → F) _ _
    (spinAction (quadPlus 4 F) u).toLinearMap (X - C (μ : F)) _ ⟨irreducible_X_sub_C _⟩,
    natDegree_X_sub_C, one_mul] at hcard
  have hcov_imp : (∀ l : Fin 4, a l = μ ∨ a l = μ⁻¹) →
      Nat.card {c : Fin 4 ⊕ Fin 4 // w c = (μ : F)} = 4 := by
    intro hcov
    let f : {c : Fin 4 ⊕ Fin 4 // w c = (μ : F)} → Fin 4 := fun c =>
      match c.1 with
      | Sum.inl l => l
      | Sum.inr l => l
    have hf_inj : Function.Injective f := by
      rintro ⟨c, hc⟩ ⟨c', hc'⟩ h
      rcases c with l | l <;> rcases c' with l' | l' <;> dsimp only [f] at h ⊢
      · subst h
        rfl
      · subst h
        have h1 : a l = μ := Units.ext (by simpa [w] using hc)
        have h2 : (a l)⁻¹ = μ := Units.ext (by simpa [w] using hc')
        have h2' : a l = μ⁻¹ := by rw [← h2, inv_inv]
        exact absurd (h1.symm.trans h2') hμinv
      · subst h
        have h1 : (a l)⁻¹ = μ := Units.ext (by simpa [w] using hc)
        have h2 : a l = μ := Units.ext (by simpa [w] using hc')
        have h1' : a l = μ⁻¹ := by rw [← h1, inv_inv]
        exact absurd (h2.symm.trans h1') hμinv
      · subst h
        rfl
    let g : Fin 4 → {c : Fin 4 ⊕ Fin 4 // w c = (μ : F)} := fun l =>
      if h : a l = μ then
        ⟨Sum.inl l, by simpa [w] using congrArg (fun u : Fˣ => (u : F)) h⟩
      else
        ⟨Sum.inr l, by
          have h' : a l = μ⁻¹ := by
            rcases hcov l with h1 | h1
            · exact absurd h1 h
            · exact h1
          have h2 : (a l)⁻¹ = μ := by rw [h', inv_inv]
          simpa [w] using congrArg (fun u : Fˣ => (u : F)) h2⟩
    have hgf : ∀ l, f (g l) = l := by
      intro l
      dsimp only [g]
      split_ifs with h
      · rfl
      · rfl
    have hbij : Function.Bijective f := ⟨hf_inj, fun l => ⟨g l, hgf l⟩⟩
    have := Nat.card_congr (Equiv.ofBijective f hbij)
    simpa using this
  by_contra hk
  have hk' : Nat.card {c : Fin 4 ⊕ Fin 4 // w c = (μ : F)} ≠ 4 := by
    rw [← hcard]
    exact hk
  have hcov : ¬ ∀ l : Fin 4, a l = μ ∨ a l = μ⁻¹ := fun h => hk' (hcov_imp h)
  push Not at hcov
  obtain ⟨l₀, hl₀μ, hl₀μinv⟩ := hcov
  obtain ⟨-, -, hdvd⟩ := mem_primaryFactors.mp hh
  have hroot : (minpoly F (spinAction (quadPlus 4 F) u).toLinearMap).IsRoot (μ : F) :=
    dvd_iff_isRoot.mp hdvd
  have heig : Module.End.HasEigenvalue (spinAction (quadPlus 4 F) u).toLinearMap (μ : F) :=
    Module.End.hasEigenvalue_iff_isRoot.mpr hroot
  obtain ⟨v, hv⟩ := heig.exists_hasEigenvector
  have hv0 : v ≠ 0 := hv.2
  have hveig : spinAction (quadPlus 4 F) u v = (μ : F) • v := hv.apply_eq_smul
  obtain ⟨c_b, hcb⟩ : ∃ c : Fin 4 ⊕ Fin 4, v c ≠ 0 := by
    by_contra h
    push Not at h
    exact hv0 (funext h)
  have hwcb : w c_b = (μ : F) := by
    have h := (jcoreOm_eigen_iff hxa (μ : F) v).mp hveig
    by_contra hne
    exact hcb (h c_b hne)
  have hdvd_units : p ∣ Nat.card Fˣ := by
    rw [Nat.card_units]
    exact hpq
  obtain ⟨ζ, hζ⟩ := @exists_prime_orderOf_dvd_card' Fˣ _ _ p ⟨hp⟩ hdvd_units
  have hζp : ζ ^ p = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hζ
    exact hp.ne_one hζ.symm
  have hζF1 : (ζ : F) ≠ 1 := fun h => hζ1 (Units.ext h)
  have hζpF : (ζ : F) ^ p = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζp, Units.val_one]
  let c₀ : Fin 4 → Fˣ := fun i => if i = l₀ then ζ else 1
  obtain ⟨t, ht, htv⟩ := KGCentOm.exists_mem_ggTorus_vec_eq_smul (n := 4) (K := F) hn4 c₀
  have hc₀ : c₀ l₀ = ζ := by simp [c₀]
  have hc₀' : ∀ l : Fin 4, l ≠ l₀ → c₀ l = 1 := by
    intro l hl
    simp [c₀, hl]
  have hζt : kgcDiag t (Sum.inl l₀) = (ζ : F) := by
    have h := (htv l₀).1
    rw [hc₀] at h
    have := KGCentOm.kgcDiag_eq_of_smul (k := l₀) (r := true) hn4 h
    rwa [show KGCentOm.kgcIdx l₀ true = Sum.inl l₀ from rfl] at this
  have hζt' : kgcDiag t (Sum.inr l₀) = ((ζ : F)⁻¹) := by
    have h := (htv l₀).2
    rw [hc₀] at h
    have := KGCentOm.kgcDiag_eq_of_smul (k := l₀) (r := false) hn4 h
    rw [show KGCentOm.kgcIdx l₀ false = Sum.inr l₀ from rfl] at this
    simpa using this
  have hother : ∀ c : Fin 4 ⊕ Fin 4, c ≠ Sum.inl l₀ → c ≠ Sum.inr l₀ →
      kgcDiag t c = 1 := by
    intro c h1 h2
    rcases c with l | l
    · have hl : l ≠ l₀ := fun h => h1 (by rw [h])
      have h := (htv l).1
      rw [hc₀' l hl] at h
      have h' : spinAction (quadPlus 4 F) t ((plusFrame 4 F hn4).vec l true) =
          (1 : F) • (plusFrame 4 F hn4).vec l true := by simpa using h
      have := KGCentOm.kgcDiag_eq_of_smul (k := l) (r := true) (c := (1 : F)) hn4 h'
      rwa [show KGCentOm.kgcIdx l true = Sum.inl l from rfl] at this
    · have hl : l ≠ l₀ := fun h => h2 (by rw [h])
      have h := (htv l).2
      rw [hc₀' l hl] at h
      have h' : spinAction (quadPlus 4 F) t ((plusFrame 4 F hn4).vec l false) =
          (1 : F) • (plusFrame 4 F hn4).vec l false := by simpa using h
      have := KGCentOm.kgcDiag_eq_of_smul (k := l) (r := false) (c := (1 : F)) hn4 h'
      rwa [show KGCentOm.kgcIdx l false = Sum.inr l from rfl] at this
  have htp : t ^ p = 1 := by
    refine KGCentOm.pow_eq_one_of_kgcDiag hn4 ht (fun k => ?_)
    by_cases hk : k = l₀
    · subst hk
      rw [hζt, hζpF]
    · have h1 : kgcDiag t (Sum.inl k) = 1 :=
        hother (Sum.inl k) (fun h => hk (by simpa using h)) (by simp)
      rw [h1, one_pow]
  have htJ : t ∈ Subgroup.centralizer (J : Set (spinGroup (quadPlus 4 F))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hzJ := hJ z hz
    have hgx : ∀ v : Fin 4 ⊕ Fin 4 → F,
        spinAction (quadPlus 4 F) z (spinAction (quadPlus 4 F) u v) =
          spinAction (quadPlus 4 F) u (spinAction (quadPlus 4 F) z v) :=
      (mem_isometryCentralizer.mp
        (supportedBlock_le_isometryCentralizer (Q := quadPlus 4 F)
          (x := spinAction (quadPlus 4 F) u) (h := X - C (μ : F)) hzJ)).2
    have hhe : ∀ c : Fin 4 ⊕ Fin 4, w c ∈ ({(μ : F), ((μ : F)⁻¹)} : Set F) →
        kgcDiag t c = 1 := by
      intro c hc
      have h1 : c ≠ Sum.inl l₀ := by
        rintro rfl
        have hc' : (a l₀ : F) = (μ : F) ∨ (a l₀ : F) = ((μ : F)⁻¹) := by
          simpa only [w, Sum.elim_inl, Sum.elim_inr, Set.mem_insert_iff,
            Set.mem_singleton_iff] using hc
        rcases hc' with h | h
        · exact hl₀μ (Units.ext h)
        · exact hl₀μinv (Units.ext (by rwa [← Units.val_inv_eq_inv_val] at h))
      have h2 : c ≠ Sum.inr l₀ := by
        rintro rfl
        have hc' : (((a l₀)⁻¹ : Fˣ) : F) = (μ : F) ∨
            (((a l₀)⁻¹ : Fˣ) : F) = ((μ : F)⁻¹) := by
          simpa only [w, Sum.elim_inl, Sum.elim_inr, Set.mem_insert_iff,
            Set.mem_singleton_iff] using hc
        rcases hc' with h | h
        · have h' : (a l₀)⁻¹ = μ := Units.ext h
          exact hl₀μinv ((inv_eq_iff_eq_inv).mp h')
        · have h' : (a l₀)⁻¹ = μ⁻¹ :=
            Units.ext (by rwa [← Units.val_inv_eq_inv_val] at h)
          exact hl₀μ (inv_inj.mp h')
      exact hother c h1 h2
    have hhg : ∀ c : Fin 4 ⊕ Fin 4, w c ∉ ({(μ : F), ((μ : F)⁻¹)} : Set F) →
        spinAction (quadPlus 4 F) z (Pi.single c 1) = Pi.single c 1 := by
      intro c hc
      have hc' : w c ≠ (μ : F) ∧ w c ≠ ((μ : F)⁻¹) := by
        simpa only [Set.mem_insert_iff, Set.mem_singleton_iff, not_or] using hc
      exact ggTBJD4_supported_fix hxa μ.ne_zero hzJ hc'.1 hc'.2
    have hd : ∀ v c, spinAction (quadPlus 4 F) t v c = kgcDiag t c * v c :=
      fun v c => KGCentOm.spinAction_apply_eq_kgcDiag_mul hn4 ht v c
    have hcomm := ggTBJD4_commute_of_diag (x := spinAction (quadPlus 4 F) u)
      (g := spinAction (quadPlus 4 F) z) (d := spinAction (quadPlus 4 F) t)
      (w := w) (e := kgcDiag t) hxa hd hgx
      (S := ({(μ : F), ((μ : F)⁻¹)} : Set F)) hhe hhg
    have hzt : z * t = t * z := by
      apply RootCentOmega.spinAction_quadPlus_injective
      rw [map_mul, map_mul]
      exact hcomm
    exact hzt
  have hcb_inl : c_b ≠ Sum.inl l₀ := by
    rintro rfl
    have h : w (Sum.inl l₀) = (μ : F) := hwcb
    rw [show w (Sum.inl l₀) = ((a l₀ : Fˣ) : F) from rfl] at h
    exact hl₀μ (Units.ext h)
  have hcb_inr : c_b ≠ Sum.inr l₀ := by
    rintro rfl
    have h : w (Sum.inr l₀) = (μ : F) := hwcb
    rw [show w (Sum.inr l₀) = (((a l₀)⁻¹ : Fˣ) : F) from rfl] at h
    have h' : (a l₀)⁻¹ = μ := Units.ext h
    exact hl₀μinv ((inv_eq_iff_eq_inv).mp h')
  have hx₂ : kgcDiag t c_b = 1 := hother c_b hcb_inl hcb_inr
  have hucb : kgcDiag u c_b = (μ : F) := by
    rw [kgcDiag, hxa, Pi.single_eq_same, mul_one]
    exact hwcb
  have hx₁ : kgcDiag t (Sum.inl l₀) ≠ 1 := by
    rw [hζt]
    exact hζF1
  have hy₂ : kgcDiag u c_b ≠ 1 := by
    rw [hucb]
    exact fun h => hμ (Units.ext h)
  have hle := ggTBJD4_sq_le_ncard (n := 4) (K := F) hn4 hp ht hu htp hup htJ huJ
    (m₁ := Sum.inl l₀) (m₂ := c_b) hx₁ hx₂ hy₂
  have hcontra : p ^ 2 ≤ p := le_trans hle hcount
  have hp2 : 2 ≤ p := hp.two_le
  have h2 : p * 2 ≤ p := by
    calc p * 2 ≤ p * p := Nat.mul_le_mul_left p hp2
      _ = p ^ 2 := (sq p).symm
      _ ≤ p := hcontra
  omega

end CFSG.StandardType

end
