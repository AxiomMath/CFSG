module

public import CFSG.Quasithin.Vol2.Ch3Sec3NFOuter
public import CFSG.Milestones.ASVolI.A4
public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptDefs

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint CFSG.Quasithin
open CFSG.QuasithinUnique.Vol2Native (A37ForSQTKCat A38ForSQTKCat A39ForSQTKCat)
open scoped commutatorElement

section Perfect

variable {G : Type} [Group G] [Finite G]

theorem eq_of_perfect_of_two_power {K N : Subgroup G} (hK : ⁅K, K⁆ = K) (hNK : N ≤ K)
    (hN : (N.subgroupOf K).Normal) (hx : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ N) : N = K := by
  haveI := hN
  set π : K →* K ⧸ N.subgroupOf K := QuotientGroup.mk' _
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hP : IsPGroup 2 (K ⧸ N.subgroupOf K) := by
    intro q
    obtain ⟨x, rfl⟩ := hπs q
    obtain ⟨k, hk⟩ := hx x.1 x.2
    refine ⟨k, ?_⟩
    rw [← map_pow]
    exact (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr (by simpa using hk))
  have hKtop : ⁅(⊤ : Subgroup K), (⊤ : Subgroup K)⁆ = ⊤ := by
    have hmap : Subgroup.map K.subtype (⊤ : Subgroup K) = K := by
      ext x
      simp
    apply Subgroup.map_injective (f := K.subtype) Subtype.val_injective
    rw [Subgroup.map_commutator, hmap]
    exact hK
  have hπt : Subgroup.map π (⊤ : Subgroup K) = ⊤ := by
    rw [eq_top_iff]
    intro q _
    obtain ⟨x, rfl⟩ := hπs q
    exact Subgroup.mem_map.mpr ⟨x, Subgroup.mem_top _, rfl⟩
  have hQ : ⁅(⊤ : Subgroup (K ⧸ N.subgroupOf K)), (⊤ : Subgroup (K ⧸ N.subgroupOf K))⁆ = ⊤ := by
    have h := Subgroup.map_commutator (H₁ := (⊤ : Subgroup K)) (H₂ := (⊤ : Subgroup K)) π
    rw [hKtop, hπt] at h
    exact h.symm
  haveI : Group.IsSolvable (K ⧸ N.subgroupOf K) := by
    haveI := hP.isNilpotent
    infer_instance
  have hsub : Subsingleton (K ⧸ N.subgroupOf K) := by
    by_contra hns
    rw [not_subsingleton_iff_nontrivial] at hns
    have hlt := Group.IsSolvable.commutator_lt_top_of_nontrivial (G := K ⧸ N.subgroupOf K)
    have hc : commutator (K ⧸ N.subgroupOf K) = ⊤ := hQ
    rw [hc] at hlt
    exact lt_irrefl _ hlt
  refine le_antisymm hNK fun x hx => ?_
  have h1 : (QuotientGroup.mk' (N.subgroupOf K) (⟨x, hx⟩ : K) : K ⧸ N.subgroupOf K) = 1 :=
    Subsingleton.elim _ _
  exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h1)

theorem oResidual_two_eq_of_perfect {K : Subgroup G} (hK : ⁅K, K⁆ = K) :
    CFSG.ASVolI.ChA.oResidual {2} K = K := by
  apply le_antisymm
  · have hnorm : (K.subgroupOf K).Normal := by
      rw [Subgroup.subgroupOf_self]
      infer_instance
    have hpow : ∀ x ∈ K, ∃ m : ℕ, 0 < m ∧ (∀ q : ℕ, q.Prime → q ∣ m → q ∈ ({2} : Set ℕ)) ∧
        x ^ m ∈ K := fun x hx =>
      ⟨1, one_pos, fun q hq hd => absurd (Nat.dvd_one.mp hd) hq.one_lt.ne', by simpa using hx⟩
    unfold CFSG.ASVolI.ChA.oResidual
    exact iInf₂_le (f := fun (N : Subgroup G) (_ : N ≤ K ∧ (N.subgroupOf K).Normal ∧
      ∀ x ∈ K, ∃ m : ℕ, 0 < m ∧ (∀ q : ℕ, q.Prime → q ∣ m → q ∈ ({2} : Set ℕ)) ∧ x ^ m ∈ N) => N)
      K ⟨le_rfl, hnorm, hpow⟩
  · unfold CFSG.ASVolI.ChA.oResidual
    refine le_iInf₂ fun N hN => ?_
    obtain ⟨hNK, hNn, hx⟩ := hN
    have hpow : ∀ y ∈ K, ∃ k : ℕ, y ^ 2 ^ k ∈ N := by
      intro y hy
      obtain ⟨m, hm0, hmπ, hym⟩ := hx y hy
      have hm : m = 2 ^ m.primeFactorsList.length :=
        Nat.eq_prime_pow_of_unique_prime_dvd hm0.ne'
          (fun {d} hd hdm => Set.mem_singleton_iff.mp (hmπ d hd hdm))
      refine ⟨m.primeFactorsList.length, ?_⟩
      rw [← hm]
      exact hym
    exact le_of_eq (eq_of_perfect_of_two_power hK hNK hNn hpow).symm

end Perfect

section Config

variable {G : Type} [Group G] [Finite G] {T M L D H K : Subgroup G}

theorem T_le_H₀ (c : NFConfig G T M L D H K) : T ≤ H ⊔ D :=
  c.inH.1.trans le_sup_left

theorem K_le_H₀ (c : NFConfig G T M L D H K) : K ≤ H ⊔ D :=
  CFSG.Quasithin.le_of_mem_cComp c.K_comp

theorem conjClosure_le_H₀ (c : NFConfig G T M L D H K) : conjClosure K T ≤ H ⊔ D :=
  CFSG.Quasithin.conjClosure_le fun t ht k hk =>
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (T_le_H₀ c ht) (K_le_H₀ c hk))
      (Subgroup.inv_mem _ (T_le_H₀ c ht))

theorem conjClosure_le_normalizer_K (c : NFConfig G T M L D H K) :
    conjClosure K T ≤ Subgroup.normalizer (K : Set G) := by
  refine CFSG.Quasithin.conjClosure_le fun t ht k hk => ?_
  have h1 : K.map (MulAut.conj t).toMonoidHom ∈ cComp (H ⊔ D) :=
    CFSG.Quasithin.map_conj_mem_cComp c.K_comp (T_le_H₀ c ht)
  exact CFSG.Quasithin.le_normalizer_of_mem_cComp c.K_comp h1 ⟨k, hk, rfl⟩

theorem sup_le_normalizer_conjClosure (K T : Subgroup G) :
    conjClosure K T ⊔ T ≤ Subgroup.normalizer (conjClosure K T : Set G) :=
  sup_le Subgroup.le_normalizer (CFSG.Quasithin.le_normalizer_conjClosure K T)

theorem pCoreOf_conjClosure_le_H₀ (c : NFConfig G T M L D H K) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) : pCoreOf 2 (conjClosure K T) ≤ pCoreOf 2 (H ⊔ D) :=
  CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    ((CFSG.LieType.BorelTits.pCoreOf_le 2 (conjClosure K T)).trans (conjClosure_le_H₀ c))
    (fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjClosure K T)
      (c.H₀_le_normalizer h37 h38 hg))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure K T))

theorem commutator_mem_pCoreOf_H₀ (c : NFConfig G T M L D H K) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) {x k : G} (hx : x ∈ pCoreOf 2 (conjClosure K T ⊔ T)) (hk : k ∈ K) :
    x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (H ⊔ D) := by
  have hkK₀ : k ∈ conjClosure K T := CFSG.Quasithin.le_conjClosure K T hk
  have hkT : k ∈ conjClosure K T ⊔ T := Subgroup.mem_sup_left hkK₀
  have hxK₀T : x ∈ conjClosure K T ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
  have h1 : k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure K T ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (conjClosure K T ⊔ T) hkT) x⁻¹).mp
      (Subgroup.inv_mem _ hx)
  have h2 : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure K T ⊔ T) := by
    rw [show x * k * x⁻¹ * k⁻¹ = x * (k * x⁻¹ * k⁻¹) by group]
    exact Subgroup.mul_mem _ hx h1
  have h3 : x * k * x⁻¹ ∈ conjClosure K T :=
    (Subgroup.mem_normalizer_iff.mp (sup_le_normalizer_conjClosure K T hxK₀T) k).mp hkK₀
  have h4 : x * k * x⁻¹ * k⁻¹ ∈ conjClosure K T :=
    Subgroup.mul_mem _ h3 (Subgroup.inv_mem _ hkK₀)
  have h5 : x * k * x⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure K T) :=
    CFSG.Quasithin.H13.inf_pCoreOf_le (H₀ := conjClosure K T ⊔ T) le_sup_left ⟨h4, h2⟩
  exact pCoreOf_conjClosure_le_H₀ c h37 h38 h5

theorem mem_pCore_subtype {H' : Subgroup G} {g : G} (hg : g ∈ pCoreOf 2 H') (hgH : g ∈ H') :
    (⟨g, hgH⟩ : ↥H') ∈ CFSG.pCore 2 ↥H' := by
  have hg' : g ∈ (CFSG.pCore 2 ↥H').map H'.subtype := hg
  obtain ⟨y, hy, hyg⟩ := hg'
  have hyeq : y = ⟨g, hgH⟩ := Subtype.ext hyg
  rw [← hyeq]
  exact hy

theorem pCoreOf_sup_le_normalizer_K (c : NFConfig G T M L D H K) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) :
    pCoreOf 2 (conjClosure K T ⊔ T) ≤ Subgroup.normalizer (K : Set G) := by
  intro x hx
  have hxK₀T : x ∈ conjClosure K T ⊔ T := CFSG.LieType.BorelTits.pCoreOf_le 2 _ hx
  have hxH₀ : x ∈ H ⊔ D := (sup_le (conjClosure_le_H₀ c) (T_le_H₀ c)) hxK₀T
  have hxKx : K.map (MulAut.conj x).toMonoidHom ∈ cComp (H ⊔ D) :=
    CFSG.Quasithin.map_conj_mem_cComp c.K_comp hxH₀
  have hfix : ∀ z ∈ CFSG.Quasithin.modO2Image (H ⊔ D) K,
      (MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥(H ⊔ D)) (⟨x, hxH₀⟩ : ↥(H ⊔ D)))).toMonoidHom
        z = z := by
    intro z hz
    obtain ⟨w, hw, rfl⟩ := hz
    have hwK : (w : G) ∈ K := Subgroup.mem_subgroupOf.mp hw
    have hc := commutator_mem_pCoreOf_H₀ c h37 h38 hx (Subgroup.inv_mem _ hwK)
    rw [inv_inv] at hc
    have hgH : x * (w : G)⁻¹ * x⁻¹ * (w : G) ∈ H ⊔ D :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hxH₀
        (Subgroup.inv_mem _ w.2)) (Subgroup.inv_mem _ hxH₀)) w.2
    have hmem := mem_pCore_subtype hc hgH
    show QuotientGroup.mk' (CFSG.pCore 2 ↥(H ⊔ D)) (⟨x, hxH₀⟩ : ↥(H ⊔ D)) *
      QuotientGroup.mk' (CFSG.pCore 2 ↥(H ⊔ D)) w *
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(H ⊔ D)) (⟨x, hxH₀⟩ : ↥(H ⊔ D)))⁻¹ =
        QuotientGroup.mk' (CFSG.pCore 2 ↥(H ⊔ D)) w
    rw [← map_mul, ← map_inv, ← map_mul]
    apply QuotientGroup.eq.mpr
    convert hmem using 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have himg : CFSG.Quasithin.modO2Image (H ⊔ D) (K.map (MulAut.conj x).toMonoidHom) =
      CFSG.Quasithin.modO2Image (H ⊔ D) K := by
    refine (CFSG.Quasithin.modO2Image_conj (⟨x, hxH₀⟩ : ↥(H ⊔ D))).trans ?_
    ext y
    constructor
    · rintro ⟨z, hz, rfl⟩
      rw [hfix z hz]
      exact hz
    · intro hy
      exact ⟨y, hy, hfix y hy⟩
  exact CFSG.Quasithin.A38.map_conj_eq_iff.mp
    (CFSG.Quasithin.modO2Image_injOn (H ⊔ D) hxKx c.K_comp himg)

theorem commutator_omegaOne_le (c : NFConfig G T M L D H K) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) :
    ⁅CFSG.ASVolI.ChA.omegaOne 2 (CFSG.ASVolI.ChA.centerOf (pCoreOf 2 (conjClosure K T ⊔ T))),
      K⁆ ≤ pCoreOf 2 K := by
  have hTK := pCoreOf_sup_le_normalizer_K c h37 h38
  have hK₀T : K ≤ conjClosure K T ⊔ T := (CFSG.Quasithin.le_conjClosure K T).trans le_sup_left
  have hΩ : CFSG.ASVolI.ChA.omegaOne 2 (CFSG.ASVolI.ChA.centerOf (pCoreOf 2 (conjClosure K T ⊔ T)))
      ≤ pCoreOf 2 (conjClosure K T ⊔ T) := by
    unfold CFSG.ASVolI.ChA.omegaOne
    rw [Subgroup.closure_le]
    exact fun x hx => (Subgroup.mem_inf.mp hx.1).1
  refine Subgroup.commutator_le.mpr fun ω hω k hk => ?_
  have hωT : ω ∈ pCoreOf 2 (conjClosure K T ⊔ T) := hΩ hω
  have h1 : ω * k * ω⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hTK hωT) k).mp hk
  have hkN := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (conjClosure K T ⊔ T) (hK₀T hk)
  have h2 : k * ω⁻¹ * k⁻¹ ∈ pCoreOf 2 (conjClosure K T ⊔ T) :=
    (Subgroup.mem_normalizer_iff.mp hkN ω⁻¹).mp (Subgroup.inv_mem _ hωT)
  rw [commutatorElement_def]
  have hmem : ω * k * ω⁻¹ * k⁻¹ ∈ K ⊓ pCoreOf 2 (conjClosure K T ⊔ T) := by
    refine ⟨Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ hk), ?_⟩
    rw [show ω * k * ω⁻¹ * k⁻¹ = ω * (k * ω⁻¹ * k⁻¹) by group]
    exact Subgroup.mul_mem _ hωT h2
  exact CFSG.Quasithin.H13.inf_pCoreOf_le hK₀T hmem

theorem pCoreOf_le_TC (c : NFConfig G T M L D H K) :
    pCoreOf 2 K ≤ pCoreOf 2 (conjClosure K T ⊔ T) := by
  have h1 : pCoreOf 2 K ≤ pCoreOf 2 (conjClosure K T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans (CFSG.Quasithin.le_conjClosure K T))
      (fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K
        (conjClosure_le_normalizer_K c hg))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have h2 : pCoreOf 2 (conjClosure K T) ≤ pCoreOf 2 (conjClosure K T ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 (conjClosure K T)).trans le_sup_left)
      (fun g hg => CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 (conjClosure K T)
        (sup_le_normalizer_conjClosure K T hg))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure K T))
  exact h1.trans h2

theorem isSubnormal_K_sup (c : NFConfig G T M L D H K) :
    CFSG.Open.IsSubnormal K (conjClosure K T ⊔ T) := by
  have hKK₀ : (K.subgroupOf (conjClosure K T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.Quasithin.le_conjClosure K T)).mpr
      (conjClosure_le_normalizer_K c)
  have hK₀ : ((conjClosure K T).subgroupOf (conjClosure K T ⊔ T)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
      (sup_le_normalizer_conjClosure K T)
  exact CFSG.Open.IsSubnormal.step (CFSG.Quasithin.le_conjClosure K T) hKK₀
    (CFSG.Open.IsSubnormal.step le_sup_left hK₀ (CFSG.Open.IsSubnormal.refl _))

end Config

theorem leafS_holds (h128 : Lemma128Two) (h37 : A37ForSQTKCat)
    (h38 : A38ForSQTKCat) (h39 : A39ForSQTKCat) : LeafS := by
  intro G _ _ T M L D H K c e he_mem he_sq he_comm
  have hperf : ⁅K, K⁆ = K := c.K_isLocal.2.1.2.1
  have hgen : CFSG.Open.quasithinGenFitting K = pCoreOf 2 K :=
    CFSG.Quasithin.lemma_1_2_7_two c.hyp.qtke c.hyp.simple c.hyp.nonabelian
      (CFSG.Quasithin.a37ForSQTK_of_cat h37) (CFSG.Quasithin.a39ForSQTK_of_cat h39)
      c.hyp.sylow (c.isMaximalLocal h128)
  have hV2 : CFSG.Open.quasithinV2 K = ⊥ := by
    by_contra hne
    apply c.nonfaithful
    unfold CFSG.Open.quasithinIsFaithfulLocal
    exact ⟨c.K_isLocal, fun N hNK hN hx => eq_of_perfect_of_two_power hperf hNK hN hx, hgen, hne⟩
  have hVY : CFSG.ASVolI.ChA.VY K = ⊥ := hV2
  have hInX : CFSG.ASVolI.ChA.InClassX K := by
    unfold CFSG.ASVolI.ChA.InClassX
    exact ⟨c.K_isLocal.2.1.1, oResidual_two_eq_of_perfect hperf, hgen⟩
  have hR : CFSG.ASVolI.ChA.IsTwoSignalizer (conjClosure K T ⊔ T) K (pCoreOf 2 K) := by
    unfold CFSG.ASVolI.ChA.IsTwoSignalizer
    exact ⟨(CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans
        ((CFSG.Quasithin.le_conjClosure K T).trans le_sup_left),
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K,
      CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K⟩
  have hS : CFSG.ASVolI.ChA.IsTwoSignalizer (conjClosure K T ⊔ T) K
      (pCoreOf 2 (conjClosure K T ⊔ T)) := by
    unfold CFSG.ASVolI.ChA.IsTwoSignalizer
    exact ⟨CFSG.LieType.BorelTits.pCoreOf_le 2 (conjClosure K T ⊔ T),
      CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (conjClosure K T ⊔ T),
      (CFSG.Quasithin.le_conjClosure K T).trans (le_sup_left.trans
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (conjClosure K T ⊔ T)))⟩
  have hVR : CFSG.ASVolI.ChA.VYR K (pCoreOf 2 (conjClosure K T ⊔ T)) ≤ pCoreOf 2 K :=
    commutator_omegaOne_le c h37 h38
  have hRS : pCoreOf 2 K ≤ pCoreOf 2 (conjClosure K T ⊔ T) := pCoreOf_le_TC c
  have hA := CFSG.ASVolI.as_A_4_8 G K (conjClosure K T ⊔ T) (pCoreOf 2 K)
    (pCoreOf 2 (conjClosure K T ⊔ T)) hInX (isSubnormal_K_sup c) hR hS hVR hRS hRS
  have hVR0 : CFSG.ASVolI.ChA.VYR K (pCoreOf 2 (conjClosure K T ⊔ T)) = ⊥ := by
    by_contra h
    exact (hA.2.2.2.2.mp h) hVY
  have hKe : ∀ e' ∈ pCoreOf 2 (conjClosure K T ⊔ T), e' ^ 2 = 1 →
      (∀ x ∈ pCoreOf 2 (conjClosure K T ⊔ T), x * e' = e' * x) → ∀ k ∈ K, e' * k = k * e' := by
    intro e' he' he'sq he'c k hk
    have hcen : e' ∈ CFSG.ASVolI.ChA.centerOf (pCoreOf 2 (conjClosure K T ⊔ T)) :=
      Subgroup.mem_inf.mpr ⟨he', Subgroup.mem_centralizer_iff.mpr he'c⟩
    have hΩ : e' ∈ CFSG.ASVolI.ChA.omegaOne 2
        (CFSG.ASVolI.ChA.centerOf (pCoreOf 2 (conjClosure K T ⊔ T))) :=
      Subgroup.subset_closure (show e' ∈ {x | x ∈ CFSG.ASVolI.ChA.centerOf
        (pCoreOf 2 (conjClosure K T ⊔ T)) ∧ x ^ 2 = 1} from ⟨hcen, he'sq⟩)
    have hc := Subgroup.commutator_mem_commutator hΩ hk
    have hbot : ⁅CFSG.ASVolI.ChA.omegaOne 2
        (CFSG.ASVolI.ChA.centerOf (pCoreOf 2 (conjClosure K T ⊔ T))), K⁆ = ⊥ := hVR0
    rw [hbot, Subgroup.mem_bot, commutatorElement_def] at hc
    exact mul_inv_eq_iff_eq_mul.mp (mul_inv_eq_one.mp hc)
  have hN : conjClosure K T ⊔ T ≤ Subgroup.normalizer
      ((pCoreOf 2 (conjClosure K T ⊔ T) : Subgroup G) : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (conjClosure K T ⊔ T)
  refine CFSG.Quasithin.conjClosure_le fun t ht k hk => ?_
  have ht' : t ∈ conjClosure K T ⊔ T := Subgroup.mem_sup_right ht
  have he'mem : t⁻¹ * e * t ∈ pCoreOf 2 (conjClosure K T ⊔ T) := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hN (Subgroup.inv_mem _ ht')) e).mp he_mem
    rwa [inv_inv] at h1
  have he'sq : (t⁻¹ * e * t) ^ 2 = 1 := by
    rw [show (t⁻¹ * e * t) ^ 2 = t⁻¹ * e ^ 2 * t by rw [pow_two, pow_two]; group, he_sq, mul_one,
      inv_mul_cancel]
  have he'c : ∀ x ∈ pCoreOf 2 (conjClosure K T ⊔ T),
      x * (t⁻¹ * e * t) = t⁻¹ * e * t * x := by
    intro x hx
    have hxt : t * x * t⁻¹ ∈ pCoreOf 2 (conjClosure K T ⊔ T) :=
      (Subgroup.mem_normalizer_iff.mp (hN ht') x).mp hx
    have hcx := he_comm (t * x * t⁻¹) hxt
    calc x * (t⁻¹ * e * t) = t⁻¹ * (t * x * t⁻¹ * e) * t := by group
      _ = t⁻¹ * (e * (t * x * t⁻¹)) * t := by rw [hcx]
      _ = t⁻¹ * e * t * x := by group
  have hkk := hKe (t⁻¹ * e * t) he'mem he'sq he'c k hk
  rw [Subgroup.mem_centralizer_singleton_iff]
  calc t * k * t⁻¹ * e = t * (k * (t⁻¹ * e * t)) * t⁻¹ := by group
    _ = t * (t⁻¹ * e * t * k) * t⁻¹ := by rw [hkk]
    _ = e * (t * k * t⁻¹) := by group

end CFSG.Quasithin.H13.NF314pt

end
