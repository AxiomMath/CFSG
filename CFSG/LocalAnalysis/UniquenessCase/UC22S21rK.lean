module

public import Mathlib.GroupTheory.IsPerfect
public import CFSG.Sporadic.Schreier.RuElemAut
import CFSG.GroupTheory.CyclicSylowNormalOddComplement
import CFSG.LocalAnalysis.ComponentClassification.FooteLitNormalFour
import CFSG.FeitThompson.OddOrderTheorem
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Sporadic.RuSchreier

theorem uc22s21rk_eq_one_or_eq_neg_one {F : Type*} [Field F] (h2 : (2 : F) ≠ 0)
    {g : GL (Fin 2) F} (hdet : g.det = 1) (hsq : g * g = 1) : g = 1 ∨ g = -1 := by
  obtain ⟨a, b, c, d, hA⟩ : ∃ a b c d : F, (g : Matrix (Fin 2) (Fin 2) F) = !![a, b; c, d] :=
    ⟨_, _, _, _, Matrix.eta_fin_two _⟩
  have hd : Matrix.det (g : Matrix (Fin 2) (Fin 2) F) = 1 := by
    have := congrArg (fun u : Fˣ => (u : F)) hdet
    simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
  have hm : (g : Matrix (Fin 2) (Fin 2) F) * g = 1 := by
    have := congrArg (fun u : GL (Fin 2) F => (u : Matrix (Fin 2) (Fin 2) F)) hsq
    simpa using this
  rw [hA] at hd hm
  rw [Matrix.det_fin_two_of] at hd
  have e1 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 0) hm
  have e2 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 0 1) hm
  have e3 := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M 1 0) hm
  simp [Matrix.mul_apply, Fin.sum_univ_two] at e1 e2 e3
  by_cases hs : a + d = 0
  · exfalso
    apply h2
    linear_combination (-1) * e1 - hd + a * hs
  · have hb : b = 0 := by
      have : b * (a + d) = 0 := by linear_combination e2
      exact (mul_eq_zero.mp this).resolve_right hs
    have hc : c = 0 := by
      have : c * (a + d) = 0 := by linear_combination e3
      exact (mul_eq_zero.mp this).resolve_right hs
    subst hb hc
    have haa : a * a = 1 := by simpa using e1
    have had : a * d = 1 := by simpa using hd
    have hda : d = a := by linear_combination (-d) * haa + a * had
    subst hda
    rcases mul_self_eq_one_iff.mp haa with h | h
    · left
      apply Units.ext
      ext i j
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) hA
      fin_cases i <;> fin_cases j <;> simp_all
    · right
      apply Units.ext
      ext i j
      have := congrArg (fun M : Matrix (Fin 2) (Fin 2) F => M i j) hA
      fin_cases i <;> fin_cases j <;> simp_all

theorem uc22s21rk_two_ne_zero {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h
  have h' : ((2 : ℕ) : ZMod q) = 0 := by exact_mod_cast h
  rw [ZMod.natCast_eq_zero_iff] at h'
  exact hq2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp h')

theorem uc22s21rk_map_eq_one_of_perfect {G : Type*} [Group G] [Group.IsPerfect G] {A : Type*}
    [CommGroup A] (f : G →* A) (g : G) : f g = 1 := by
  haveI : Group.IsPerfect f.range := Group.IsPerfect.range f
  exact congrArg Subtype.val (Subsingleton.elim (⟨f g, g, rfl⟩ : f.range) 1)

theorem uc22s21rk_isSolvable_of_cyclic_sylow {K : Type*} [Group K] [Finite K] (P : Sylow 2 K)
    (hP : IsCyclic P) : Group.IsSolvable K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, ⟨hnormal, hodd, hindex, -⟩, -⟩ := cyclic_sylow_normal_odd_complement P hP
  have hs1 : Group.IsSolvable (pPrimeCore 2 K) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
  have : (pPrimeCore 2 K).Normal := hnormal
  have hs2 : Group.IsSolvable (K ⧸ pPrimeCore 2 K) := by
    obtain ⟨n, hn⟩ := P.isPGroup'.exists_card_eq
    have hq : IsPGroup 2 (K ⧸ pPrimeCore 2 K) :=
      IsPGroup.of_card (n := n) (by rw [← Subgroup.index_eq_card, hindex, hn])
    have := hq.isNilpotent
    infer_instance
  exact Group.isSolvable_of_subgroup_quotient (pPrimeCore 2 K)

theorem uc22s21rk_eq_one_of_perfect {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {G : Type*} [Group G]
    [Finite G] [Group.IsPerfect G] (σ : G →* GL (Fin 2) (ZMod q)) (P : Sylow 2 G)
    (hP : ∀ x ∈ P, ∀ y ∈ P, σ x * σ y = σ y * σ x) (g : G) : σ g = 1 := by
  have hdet : ∀ g : G, (σ g).det = 1 := fun g =>
    uc22s21rk_map_eq_one_of_perfect (Matrix.GeneralLinearGroup.det.comp σ) g
  haveI : Group.IsPerfect σ.range := Group.IsPerfect.range σ
  haveI : Finite σ.range := Finite.of_surjective _ σ.rangeRestrict_surjective
  let Pσ : Sylow 2 σ.range := P.mapSurjective σ.rangeRestrict_surjective
  have hcomm : ∀ x y : Pσ, x * y = y * x := by
    rintro ⟨x, hx⟩ ⟨y, hy⟩
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
    apply Subtype.ext
    apply Subtype.ext
    exact hP a ha b hb
  have key : ∀ z : Pσ, z ^ 2 = 1 → z = 1 ∨ ((z : σ.range) : GL (Fin 2) (ZMod q)) = -1 := by
    intro z hz
    have hz' : ((z : σ.range) : GL (Fin 2) (ZMod q)) * ((z : σ.range) : GL (Fin 2) (ZMod q)) =
        1 := by
      have := congrArg (fun w : Pσ => ((w : σ.range) : GL (Fin 2) (ZMod q))) hz
      simpa [pow_two] using this
    obtain ⟨h, hh⟩ := (z : σ.range).2
    have hdetz : ((z : σ.range) : GL (Fin 2) (ZMod q)).det = 1 := by
      rw [← hh]
      exact hdet h
    rcases uc22s21rk_eq_one_or_eq_neg_one (uc22s21rk_two_ne_zero hq2) hdetz hz' with h1 | h1
    · exact Or.inl (Subtype.ext (Subtype.ext h1))
    · exact Or.inr h1
  have hcyc : IsCyclic Pσ := by
    letI : CommGroup Pσ := { (inferInstance : Group Pσ) with mul_comm := hcomm }
    refine CFSG.ComponentClassification.FooteLit.isCyclic_of_unique_involution Pσ.isPGroup' ?_
    intro x y hx hy
    rcases key x hx with h1 | h1
    · exact Or.inl h1
    rcases key y hy with h2 | h2
    · exact Or.inr (Or.inl h2)
    · exact Or.inr (Or.inr (Subtype.ext (Subtype.ext (h1.trans h2.symm))))
  have hsolv : Group.IsSolvable σ.range := uc22s21rk_isSolvable_of_cyclic_sylow Pσ hcyc
  have hsub : Subsingleton σ.range := by
    by_contra hns
    haveI : Nontrivial σ.range := not_subsingleton_iff_nontrivial.mp hns
    exact Group.IsPerfect.not_isSolvable σ.range hsolv
  exact congrArg Subtype.val (Subsingleton.elim (⟨σ g, g, rfl⟩ : σ.range) 1)

theorem uc22s21rk_perfect_le_ker_gl {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {W : Type*} [Group W]
    [Finite W] (σ : W →* GL (Fin 2) (ZMod q)) (S : Sylow 2 W)
    (hS : ∀ s ∈ S, ∀ t ∈ S, σ s * σ t = σ t * σ s) {K : Subgroup W} (hK : ⁅K, K⁆ = K) :
    K ≤ σ.ker := by
  intro k hk
  haveI : Group.IsPerfect K := Subgroup.isPerfect_iff.mpr hK
  obtain ⟨Q⟩ : Nonempty (Sylow 2 K) := inferInstance
  obtain ⟨S', hS'⟩ := (Q.isPGroup'.map K.subtype).exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq W S S'
  have hconj : ∀ x ∈ Q, ∃ s ∈ S, ((x : K) : W) = g * s * g⁻¹ := by
    intro x hx
    have hx' : ((x : K) : W) ∈ (S' : Subgroup W) := hS' (Subgroup.mem_map_of_mem _ hx)
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.mem_smul_pointwise_iff_exists] at hx'
    obtain ⟨s, hs, hsx⟩ := hx'
    exact ⟨s, hs, by simpa [MulAut.conj_apply] using hsx.symm⟩
  have hQ : ∀ x ∈ Q, ∀ y ∈ Q, (σ.comp K.subtype) x * (σ.comp K.subtype) y =
      (σ.comp K.subtype) y * (σ.comp K.subtype) x := by
    intro x hx y hy
    obtain ⟨s, hs, hxs⟩ := hconj x hx
    obtain ⟨t, ht, hyt⟩ := hconj y hy
    have h1 := hS s hs t ht
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, hxs, hyt, map_mul, map_inv]
    calc σ g * σ s * (σ g)⁻¹ * (σ g * σ t * (σ g)⁻¹)
        = σ g * (σ s * σ t) * (σ g)⁻¹ := by group
      _ = σ g * (σ t * σ s) * (σ g)⁻¹ := by rw [h1]
      _ = σ g * σ t * (σ g)⁻¹ * (σ g * σ s * (σ g)⁻¹) := by group
  exact uc22s21rk_eq_one_of_perfect hq2 (σ.comp K.subtype) Q hQ ⟨k, hk⟩

theorem uc22s21rk_perfect_le_ker {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {V : Type*} [CommGroup V]
    [Finite V] (hV : ∀ v : V, v ^ q = 1) (hcard : Nat.card V = q ^ 2) {W : Type*} [Group W]
    [Finite W] (ρ : W →* MulAut V) (S : Sylow 2 W)
    (hS : ∀ s ∈ S, ∀ t ∈ S, ρ s * ρ t = ρ t * ρ s) {K : Subgroup W} (hK : ⁅K, K⁆ = K) :
    K ≤ ρ.ker := by
  obtain ⟨e⟩ := ru_nonempty_mulEquiv_of_elementary (p := q) (fun a b => mul_comm a b) hV hcard
  let Φ : MulAut V ≃* GL (Fin 2) (ZMod q) := (MulAut.congr e).trans (ruMulAutEquivGL 2)
  have hK' := uc22s21rk_perfect_le_ker_gl hq2 (Φ.toMonoidHom.comp ρ) S
    (fun s hs t ht => by
      simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe]
      rw [← map_mul Φ (ρ s) (ρ t), ← map_mul Φ (ρ t) (ρ s), hS s hs t ht]) hK
  intro k hk
  have h1 := MonoidHom.mem_ker.mp (hK' hk)
  simp only [MonoidHom.comp_apply, MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_coe] at h1
  exact MonoidHom.mem_ker.mpr (Φ.injective (h1.trans (map_one Φ).symm))

theorem uc22s21rk_comm_of_two_lines {V : Type*} [CommGroup V] {V₁ V₂ : Subgroup V}
    (h₁ : IsCyclic V₁) (h₂ : IsCyclic V₂) (hsup : V₁ ⊔ V₂ = ⊤) {f g : MulAut V}
    (hf₁ : ∀ v ∈ V₁, f v ∈ V₁) (hf₂ : ∀ v ∈ V₂, f v ∈ V₂)
    (hg₁ : ∀ v ∈ V₁, g v ∈ V₁) (hg₂ : ∀ v ∈ V₂, g v ∈ V₂) : f * g = g * f := by
  have hline : ∀ (U : Subgroup V), IsCyclic U → (∀ v ∈ U, f v ∈ U) → (∀ v ∈ U, g v ∈ U) →
      ∀ v ∈ U, f (g v) = g (f v) := by
    intro U hU hfU hgU v hv
    obtain ⟨c, hc⟩ := hU.exists_generator
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨f c, hfU c c.2⟩)
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨g c, hgU c c.2⟩)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hc ⟨v, hv⟩)
    have hfc : f (c : V) = (c : V) ^ m := by simpa using congrArg Subtype.val hm.symm
    have hgc : g (c : V) = (c : V) ^ n := by simpa using congrArg Subtype.val hn.symm
    have hvk : v = (c : V) ^ k := by simpa using congrArg Subtype.val hk.symm
    rw [hvk]
    simp only [map_zpow, hfc, hgc, ← zpow_mul]
    rw [mul_left_comm m n k]
  ext v
  have hv : v ∈ V₁ ⊔ V₂ := by rw [hsup]; exact Subgroup.mem_top v
  obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup.mp hv
  simp only [MulAut.mul_apply, map_mul]
  rw [hline V₁ h₁ hf₁ hg₁ y hy, hline V₂ h₂ hf₂ hg₂ z hz]

theorem uc22s21rk_perfect_le_ker_of_lines {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) {V : Type*}
    [CommGroup V] [Finite V] (hV : ∀ v : V, v ^ q = 1) (hcard : Nat.card V = q ^ 2)
    {W : Type*} [Group W] [Finite W] (ρ : W →* MulAut V) (S : Sylow 2 W)
    {V₁ V₂ : Subgroup V} (h₁ : IsCyclic V₁) (h₂ : IsCyclic V₂) (hsup : V₁ ⊔ V₂ = ⊤)
    (hS₁ : ∀ s ∈ S, ∀ v ∈ V₁, ρ s v ∈ V₁) (hS₂ : ∀ s ∈ S, ∀ v ∈ V₂, ρ s v ∈ V₂)
    {K : Subgroup W} (hK : ⁅K, K⁆ = K) : K ≤ ρ.ker :=
  uc22s21rk_perfect_le_ker hq2 hV hcard ρ S
    (fun s hs t ht => uc22s21rk_comm_of_two_lines h₁ h₂ hsup (hS₁ s hs) (hS₂ s hs) (hS₁ t ht)
      (hS₂ t ht)) hK

end CFSG.LocalAnalysis.UniquenessCase.UC22
