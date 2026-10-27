module

public import CFSG.RankThree.PartOne.S11d.PSUTwistD
public import CFSG.RankThree.PartOne.S11d.LieGoodConclusion
public import Certificates.Kernel.ThCent.Leaves

public section

namespace CFSG.RankThree.PartOne.TCU

open Matrix Subgroup CFSG CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.ClassicalGroups.UnitaryFlag
  CFSG.RankThree.PartOne.KCUnitaryModel CFSG.RankThree.PartOne.OddIso CFSG.LinearGroups
open CFSG.Blueprint (LieModel)
open scoped commutatorElement

variable {F n p : ℕ} {K : Type} [Field K] {h : UnitaryFieldData 2 F K}

section Core

variable {A : SUn h n} {u : Module.End K (Fin n → K)} {c : K} (S : TwistSetup h n p A u c)

theorem psu_core_explicit (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1)
    (hn1 : 1 ≤ n) (hAp : A ^ p = 1) :
    CFSG.IsQuasisimple ↥(S.D.map (piSU h n)) ∧
      S.D.map (piSU h n) ≤ Subgroup.centralizer ({piSU h n A} : Set (PSUn h n)) ∧
      (∀ g ∈ Subgroup.centralizer ({piSU h n A} : Set (PSUn h n)), ∀ d ∈ S.D.map (piSU h n),
        g * d * g⁻¹ ∈ S.D.map (piSU h n)) ∧
      (∀ g ∈ Subgroup.centralizer ({piSU h n A} : Set (PSUn h n)),
        ∀ g' ∈ Subgroup.centralizer ({piSU h n A} : Set (PSUn h n)),
          ⁅g, g'⁆ ∈ S.D.map (piSU h n)) ∧
      (∀ g ∈ Subgroup.centralizer ({piSU h n A} : Set (PSUn h n)),
        (∃ k : ℕ, orderOf g = 2 ^ k) → g ∈ S.D.map (piSU h n)) := by
  classical
  have : CharP K 2 := h.charP
  have hsurj : Function.Surjective (piSU h n) := QuotientGroup.mk'_surjective _
  have hlift : ∀ y ∈ Subgroup.centralizer ({piSU h n A} : Set (PSUn h n)),
      ∃ g : SUn h n, piSU h n g = y ∧ g ∈ Subgroup.centralizer ({A} : Set (SUn h n)) := by
    intro y hy
    obtain ⟨g, rfl⟩ := hsurj y
    refine ⟨g, rfl, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    exact commute_of_mk_commute h hn1 hZp hAp (Subgroup.mem_centralizer_singleton_iff.mp hy)
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · refine CFSG.LocalCores.isQuasisimple_map S.D_quasisimple (piSU h n) fun hle => ?_
    exact not_le_center_of_isQuasisimple S.D_quasisimple (hle.trans (piSU_ker_le_center h))
  · rintro _ ⟨d, hd, rfl⟩
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (S.D_le_centralizer hd)
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    change piSU h n d * piSU h n A = piSU h n A * piSU h n d
    rw [← map_mul, ← map_mul, h1]
  · rintro y hy _ ⟨d, hd, rfl⟩
    obtain ⟨g, rfl, hg⟩ := hlift y hy
    refine ⟨g * d * g⁻¹, S.D_norm g hg d hd, ?_⟩
    simp only [map_mul, map_inv]
  · intro y hy y' hy'
    obtain ⟨g, rfl, hg⟩ := hlift y hy
    obtain ⟨g', rfl, hg'⟩ := hlift y' hy'
    refine ⟨⁅g, g'⁆, S.D_commutator hg hg', ?_⟩
    simp only [map_commutatorElement]
  · intro y hy hk
    obtain ⟨k, hk⟩ := hk
    have hy2 : y ^ 2 ^ k = 1 := by rw [← hk]; exact pow_orderOf_eq_one y
    obtain ⟨g, hg2, rfl⟩ := exists_lift_two_pow h hn1 hy2
    have hgC : g ∈ Subgroup.centralizer ({A} : Set (SUn h n)) :=
      Subgroup.mem_centralizer_singleton_iff.mpr
        (commute_of_mk_commute h hn1 hZp hAp (Subgroup.mem_centralizer_singleton_iff.mp hy))
    exact ⟨g, S.two_mem_D hgC hg2, rfl⟩

end Core

section Outer

variable (h)

theorem outer_core {σ : K ≃+* K} (hσ2 : ∃ x, σ (σ x) ≠ x) {V₁ : Submodule K (Fin n → K)}
    {a b : Fin n → K} (haV : a ∈ V₁) (hbV : b ∈ V₁) (haa : idForm h n a a = 0)
    (hbb : idForm h n b b = 0) (hab : idForm h n a b = 1) {e : GL (Fin n) K}
    (heU : e ∈ gramSU h (idGram K n))
    (hcon : ∀ v ∈ V₁, ∀ hv : idForm h n v v = 0,
      glAut σ (tvMat h hv 1) = e * tvMat h hv 1 * e⁻¹) : False := by
  have hKc : CharP K 2 := h.charP
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have hBl := idForm_separatingLeft h n
  have hinvE : ∀ v, linOf e⁻¹ (linOf e v) = v := fun v => by simp
  have hσne : ∀ u : Fin n → K, u ≠ 0 → σ ∘ u ≠ 0 := fun u hu e0 =>
    hu (funext fun i => σ.injective (by simpa using congrFun e0 i))
  have hline : ∀ u : Fin n → K, u ∈ V₁ → ∀ hu : idForm h n u u = 0,
      u ≠ 0 → ∃ μ : K, linOf e⁻¹ (σ ∘ u) = μ • u := by
    intro u huV hu hu0
    have hT := hcon u huV hu
    have h1 := congrArg linOf hT
    rw [linOf_glAut_tvMat, map_one, linOf_mul, linOf_mul, linOf_tvMat,
      linOf_conj_tvMat h heU] at h1
    obtain ⟨κ, hκ⟩ := exists_smul_of_hermTransvection_eq hBl one_ne_zero (hσne u hu0) h1
    exact ⟨κ, by rw [hκ, map_smul, hinvE]⟩
  have hba : idForm h n b a = 1 := by rw [← (idForm_isSymm h n).eq a b, hab, map_one]
  have ha0 : a ≠ 0 := fun e0 => by
    rw [e0, map_zero, LinearMap.zero_apply] at hab
    exact zero_ne_one hab
  have hb0 : b ≠ 0 := fun e0 => by rw [e0, map_zero] at hab; exact zero_ne_one hab
  obtain ⟨μa, hμa⟩ := hline a haV haa ha0
  obtain ⟨μb, hμb⟩ := hline b hbV hbb hb0
  have hμa0 : μa ≠ 0 := by
    intro h0
    rw [h0, zero_smul] at hμa
    have := congrArg (linOf e) hμa
    rw [map_zero] at this
    have h3 : linOf e (linOf e⁻¹ (σ ∘ a)) = σ ∘ a := by simp
    exact hσne a ha0 (h3.symm.trans this)
  have hrel : ∀ l : K, h.bar l = l → l ≠ 0 → σ l * μb = μa * l := by
    intro l hl hl0
    have hvV : a + l • b ∈ V₁ := V₁.add_mem haV (V₁.smul_mem _ hbV)
    have hvv : idForm h n (a + l • b) (a + l • b) = 0 := by
      simp only [map_add, map_smulₛₗ, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, haa,
        hbb, hab, hba, hl]
      linear_combination h2 * l
    have hv0 : a + l • b ≠ 0 := by
      intro e0
      have := congrArg (idForm h n a) e0
      simp only [map_add, map_smul, smul_eq_mul, haa, hab, map_zero] at this
      exact hl0 (by simpa using this)
    obtain ⟨μ, hμ⟩ := hline _ hvV hvv hv0
    have hcomp : σ ∘ (a + l • b) = σ ∘ a + σ l • σ ∘ b := by funext i; simp
    rw [hcomp, map_add, map_smul, hμa, hμb] at hμ
    have e1 := congrArg (idForm h n a) hμ
    have e2 := congrArg (idForm h n b) hμ
    simp only [map_add, map_smul, smul_eq_mul, haa, hbb, hab, hba] at e1 e2
    linear_combination e1 - l * e2
  have hμb : μb = μa := by
    have := hrel 1 (by rw [map_one]) one_ne_zero
    rw [map_one] at this
    linear_combination this
  have hfix : ∀ l : K, h.bar l = l → σ l = l := by
    intro l hl
    by_cases hl0 : l = 0
    · rw [hl0, map_zero]
    · have := hrel l hl hl0
      rw [hμb] at this
      exact mul_right_cancel₀ hμa0 (by linear_combination this)
  obtain ⟨x, hx⟩ := hσ2
  exact hx (σ_sq_of_fix h hfix x)

end Outer

section Pair

variable {A : SUn h n} {u : Module.End K (Fin n → K)} {c : K} (S : TwistSetup h n p A u c)

theorem TwistSetup.exists_rational_pair [Finite K] {σ : K ≃+* K} (hp : p.Prime) (hp2 : p ≠ 2)
    (hσ : orderOf σ = p) (hσu : glAut σ S.gl = S.gl) :
    ∃ a b : Fin n → K, a ∈ LinearMap.ker (u - 1) ∧ b ∈ LinearMap.ker (u - 1) ∧
      σ ∘ a = a ∧ σ ∘ b = b ∧ idForm h n a a = 0 ∧ idForm h n b b = 0 ∧
      idForm h n a b ≠ 0 := by
  have hiso : ∀ v w, idForm h n (linOf S.gl v) (linOf S.gl w) = idForm h n v w := by
    rw [S.linOf_gl]
    exact S.hiso
  have hm : 2 ≤ Module.finrank K (LinearMap.ker (linOf S.gl - 1)) := by
    rw [S.linOf_gl]
    exact S.hm
  have := exists_rational_unitary_pair_of_isom h hp hp2 hσ hiso S.gl_pow hσu hm
  rwa [S.linOf_gl] at this

theorem TwistSetup.exists_hyperbolic_pair [Finite K] {σ : K ≃+* K} (hp : p.Prime) (hp2 : p ≠ 2)
    (hσ : orderOf σ = p) (hσu : glAut σ S.gl = S.gl) :
    ∃ a b : Fin n → K, a ∈ LinearMap.ker (u - 1) ∧ b ∈ LinearMap.ker (u - 1) ∧
      idForm h n a a = 0 ∧ idForm h n b b = 0 ∧ idForm h n a b = 1 := by
  obtain ⟨a, b, haV, hbV, -, -, haa, hbb, hab⟩ := S.exists_rational_pair hp hp2 hσ hσu
  refine ⟨a, (idForm h n a b)⁻¹ • b, haV, Submodule.smul_mem _ _ hbV, haa, ?_, ?_⟩
  · rw [idForm_smul_smul, hbb, mul_zero]
  · rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hab]

theorem TwistSetup.outer [Finite K] {σ : K ≃+* K} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hσ : orderOf σ = p) (hσu : glAut σ S.gl = S.gl) :
    ∀ e ∈ S.D.map (piSU h n), ¬ ∀ g ∈ S.D.map (piSU h n), fieldAut h σ g = e * g * e⁻¹ := by
  rintro _ ⟨e₀, he₀, rfl⟩ hcon
  have hH : ∀ b ∈ S.D, primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := n)) σ b =
      e₀ * b * e₀⁻¹ := by
    have := hom_eq_of_div_central S.D_quasisimple.1
      ((primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := n)) σ).toMonoidHom.comp
        S.D.subtype) ((MulAut.conj e₀).toMonoidHom.comp S.D.subtype) (fun q => ?_)
    · intro b hb
      exact congrArg (fun f => f ⟨b, hb⟩) this
    · have h1 := hcon (piSU h n (q : SUn h n)) ⟨q, q.2, rfl⟩
      rw [fieldAut_mk] at h1
      refine mem_center_of_pi_eq_one h ?_
      change piSU h n (primeFormFieldSU h (isPrimeFormGram_idGram (K := K) (n := n)) σ
        (q : SUn h n) * (e₀ * (q : SUn h n) * e₀⁻¹)⁻¹) = 1
      rw [map_mul, map_inv, h1, map_mul, map_mul, map_inv]
      exact mul_inv_cancel _
  obtain ⟨a, b, haV, hbV, haa, hbb, hab⟩ :=
    S.exists_hyperbolic_pair hp (by have := hp5; omega) hσ hσu
  refine outer_core h (sigma_sq_ne' hσ hp5) (V₁ := LinearMap.ker (u - 1)) haV hbV haa hbb hab
    e₀.2 (fun v hv hvv => ?_)
  have := hH (tvSU h hvv) (tvSU_mem_D h S hv hvv)
  exact congrArg Subtype.val this

theorem TwistSetup.pair [Finite K] {σ : K ≃+* K} (hp : p.Prime) (hp2 : p ≠ 2)
    (hσ : orderOf σ = p) (hσu : glAut σ S.gl = S.gl) (hR : LinearMap.range (u - 1) ≠ ⊥) :
    ∃ t₁ ∈ S.D.map (piSU h n), fieldAut h σ t₁ = t₁ ∧ ∃ t₂ ∈ S.D.map (piSU h n),
      fieldAut h σ t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧ (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧
        t₁ * t₂ ≠ t₂ * t₁ := by
  obtain ⟨a, b, haV, hbV, hσa, hσb, haa, hbb, hab⟩ := S.exists_rational_pair hp hp2 hσ hσu
  obtain ⟨⟨hf₁, h₁2, h₁1⟩, ⟨hf₂, h₂2, h₂1⟩, hnc⟩ := tv_pair_facts h hσa hσb haa hbb hab
  have hT₁ : tvSU h haa ∈ S.D := tvSU_mem_D h S haV haa
  have hT₂ : tvSU h hbb ∈ S.D := tvSU_mem_D h S hbV hbb
  have hord : ∀ T : SUn h n, T ∈ S.D → (T : GL (Fin n) K) ^ 2 = 1 → (T : GL (Fin n) K) ≠ 1 →
      ∃ k : ℕ, orderOf (piSU h n T) = 2 ^ k := by
    intro T hT hT2 hT1
    refine ⟨1, ?_⟩
    rw [pow_one]
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    refine orderOf_eq_prime ?_ ?_
    · rw [← map_pow]
      have : T ^ 2 = 1 := Subtype.ext hT2
      rw [this, map_one]
    · intro h1
      have h2 : T = 1 := S.piSU_inj hR hT S.D.one_mem (by rw [h1, map_one])
      exact hT1 (congrArg (fun z : SUn h n => (z : GL (Fin n) K)) h2)
  have hfix : ∀ T : SUn h n, glAut σ (T : GL (Fin n) K) = T →
      fieldAut h σ (piSU h n T) = piSU h n T := by
    intro T hT
    rw [fieldAut_mk]
    congr 1
    exact Subtype.ext hT
  refine ⟨piSU h n (tvSU h haa), ⟨_, hT₁, rfl⟩, hfix _ hf₁, piSU h n (tvSU h hbb),
    ⟨_, hT₂, rfl⟩, hfix _ hf₂, hord _ hT₁ h₁2 h₁1, hord _ hT₂ h₂2 h₂1, ?_⟩
  intro hcomm
  have h1 : piSU h n (tvSU h haa * tvSU h hbb) = piSU h n (tvSU h hbb * tvSU h haa) := by
    rw [map_mul, map_mul]
    exact hcomm
  have h2 := S.piSU_inj hR (mul_mem hT₁ hT₂) (mul_mem hT₂ hT₁) h1
  exact hnc (congrArg (fun z : SUn h n => (z : GL (Fin n) K)) h2)

end Pair

section Good

variable {A : SUn h n} {u : Module.End K (Fin n → K)} {c : K} (S : TwistSetup h n p A u c)

theorem isComponentOf_eq_of_le {G : Type} [Group G] [Finite G] {X E D : Subgroup G}
    (hE : IsComponentOf X E) (hD : IsComponentOf X D) (hED : E ≤ D) : E = D := by
  rcases CFSG.LocalCores.distinct_components_commute (isComponent_subgroupOf_of_isComponentOf hE)
      (isComponent_subgroupOf_of_isComponentOf hD) with h | h
  · exact (inf_eq_left.mpr hE.1).symm.trans
      ((Subgroup.subgroupOf_inj.mp h).trans (inf_eq_left.mpr hD.1))
  · exfalso
    have hcomm : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := by
      intro a ha b hb
      have h1 := commutator_eq_bot_iff_le_centralizer.mp h
      have h2 : (⟨a, hE.1 ha⟩ : ↥X) ∈ E.subgroupOf X := ha
      have h3 := Subgroup.mem_centralizer_iff.mp (h1 h2) ⟨b, hD.1 (hED hb)⟩
        (show (⟨b, hD.1 (hED hb)⟩ : ↥X) ∈ D.subgroupOf X from hED hb)
      exact (congrArg Subtype.val h3).symm
    have hEsolv : Group.IsSolvable ↥E :=
      Group.isSolvable_of_comm fun u v => Subtype.ext (hcomm u u.2 v v.2)
    have : Nontrivial ↥E := CFSG.LocalCores.isQuasisimple_nontrivial hE.2.1
    have : Group.IsPerfect ↥E := hE.2.1.1
    exact Group.IsPerfect.not_isSolvable ↥E hEsolv

theorem TwistSetup.isComponentOf_D
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1) (hn1 : 1 ≤ n)
    (hAp : A ^ p = 1) :
    IsComponentOf (Subgroup.centralizer ({piSU h n A} : Set (PSUn h n)))
      (S.D.map (piSU h n)) := by
  obtain ⟨hq, hC, hn, -, -⟩ := psu_core_explicit S hZp hn1 hAp
  refine ⟨hC, hq, ?_⟩
  have hnormal : ((S.D.map (piSU h n)).subgroupOf
      (Subgroup.centralizer ({piSU h n A} : Set (PSUn h n)))).Normal :=
    ⟨fun x hx g => by
      show (g : PSUn h n) * (x : PSUn h n) * (g : PSUn h n)⁻¹ ∈ S.D.map (piSU h n)
      exact hn g g.2 x hx⟩
  exact hnormal.isSubnormal

theorem TwistSetup.eq_of_isComponentOf [Finite K]
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1) (hn1 : 1 ≤ n)
    (hAp : A ^ p = 1) {E : Subgroup (PSUn h n)}
    (hE : IsComponentOf (Subgroup.centralizer ({piSU h n A} : Set (PSUn h n))) E) :
    E = S.D.map (piSU h n) := by
  have hfinP : Finite (PSUn h n) := finite_primeFormP
  obtain ⟨-, -, -, hcomm, -⟩ := psu_core_explicit S hZp hn1 hAp
  have hD := S.isComponentOf_D hZp hn1 hAp
  refine isComponentOf_eq_of_le hE hD ?_
  have hperf : ⁅E, E⁆ = E := KCUnitary.commutator_eq_of_isPerfect hE.2.1.1
  have hCC : ⁅Subgroup.centralizer ({piSU h n A} : Set (PSUn h n)),
      Subgroup.centralizer ({piSU h n A} : Set (PSUn h n))⁆ ≤ S.D.map (piSU h n) :=
    Subgroup.commutator_le.mpr fun a ha b hb => hcomm a ha b hb
  calc E = ⁅E, E⁆ := hperf.symm
    _ ≤ _ := Subgroup.commutator_mono hE.1 hE.1
    _ ≤ S.D.map (piSU h n) := hCC

theorem goodConclusion_of_twistSetup [Finite K] {σ : K ≃+* K} {f₀ : ℕ} (hf₀ : 1 ≤ f₀)
    (hF : F = p * f₀) (hp : p.Prime) (hp5 : 5 ≤ p) (hσ : orderOf σ = p)
    (hZp : ∀ c : Kˣ, h.norm (c : K) = 1 → c ^ n = 1 → c ^ p = 1 → c = 1) (hn1 : 1 ≤ n)
    (hAp : A ^ p = 1) (hR : LinearMap.range (u - 1) ≠ ⊥) (hσu : glAut σ S.gl = S.gl) :
    GoodConclusion p (PSUn h n) (fieldAut h σ) (piSU h n A) := by
  classical
  have hfinP : Finite (PSUn h n) := finite_primeFormP
  have hcomp := S.isComponentOf_D hZp hn1 hAp
  refine ⟨⟨_, hcomp⟩, fun E hE _ => ?_, fun g hg _ hg2 => ?_⟩
  · rw [S.eq_of_isComponentOf hZp hn1 hAp hE]
    refine ⟨S.outer hp hp5 hσ hσu, ?_, S.pair hp (by omega) hσ hσu hR⟩
    obtain ⟨t', n', hmodel⟩ := S.lieModel_D hR
    exact ⟨t', n', f₀, hf₀, @Eq.rec ℕ F (fun m _ => LieModel (↥(S.D.map (piSU h n)) ⧸
      Subgroup.center ↥(S.D.map (piSU h n))) t' n' 2 m) hmodel (p * f₀) hF⟩
  · have hle : S.D.map (piSU h n) ≤
        inSubgroup layer (Subgroup.centralizer ({piSU h n A} : Set (PSUn h n))) := by
      rw [inSubgroup_layer_eq_sSup]
      exact le_sSup hcomp
    obtain ⟨-, -, -, -, h2⟩ := psu_core_explicit S hZp hn1 hAp
    exact hle (h2 g hg hg2)

end Good

end CFSG.RankThree.PartOne.TCU
