module

public import CFSG.Quasithin.Recognition.F112Crit.BenderRigidDefs
public import CFSG.Quasithin.Recognition.F112Crit.BenderCartan
import CFSG.Quasithin.Recognition.F112Crit.BenderTrichotomy
import CFSG.GH74.Uniqueness.Bender.Aut
import CFSG.GH74.Uniqueness.Bender.SuzukiAut
import CFSG.GH74.Uniqueness.Bender.UnitaryOuterRoot
import CFSG.GH74.Uniqueness.Bender.UnitaryAut
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionNormalTwoFixedPointHull
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionThreePointFullTransport
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureConjugation
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureProperPair
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyData
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureSylowAssemblyProper
import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureTwoCoreGrowthLinearFrobenius
import CFSG.StronglyEmbedded.MatrixGroups.PSL2

public section

namespace CFSG.Quasithin.F112Crit

open CFSG.Open CFSG.GH74.Uniqueness.Bender

section Aux

variable {K : Type*} [Group K]

private theorem autPow_apply_mem {H : Subgroup K} {σ : MulAut K} (hσ : ∀ x ∈ H, σ x ∈ H)
    (m : ℕ) {x : K} (hx : x ∈ H) : (σ ^ m) x ∈ H := by
  induction m with
  | zero => simpa using hx
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply]
    exact hσ _ ih

private theorem autPow_apply_eq {σ : MulAut K} {x : K} (hx : σ x = x) (m : ℕ) :
    (σ ^ m) x = x := by
  induction m with
  | zero => simp
  | succ m ih => rw [pow_succ', MulAut.mul_apply, ih, hx]

private theorem commutator_mem_rootCenter {Q : Subgroup K}
    (hsq : ∀ x ∈ Q, x * x ∈ rootCenter Q) {x y : K} (hx : x ∈ Q) (hy : y ∈ Q) :
    x * y * x⁻¹ * y⁻¹ ∈ rootCenter Q := by
  have h1 : x⁻¹ * x⁻¹ ∈ rootCenter Q := by
    have := (rootCenter Q).inv_mem (hsq x hx)
    rwa [mul_inv_rev] at this
  have h2 : y⁻¹ * y⁻¹ ∈ rootCenter Q := by
    have := (rootCenter Q).inv_mem (hsq y hy)
    rwa [mul_inv_rev] at this
  have hcomm : y⁻¹ * (x⁻¹ * x⁻¹) = (x⁻¹ * x⁻¹) * y⁻¹ :=
    (mem_rootCenter_iff.mp h1).2 y⁻¹ (Q.inv_mem hy)
  have e : x * y * x⁻¹ * y⁻¹ = (x * y * (x * y)) * ((x⁻¹ * x⁻¹) * (y⁻¹ * y⁻¹)) := by
    calc x * y * x⁻¹ * y⁻¹ = (x * y * (x * y)) * (y⁻¹ * (x⁻¹ * x⁻¹)) * y⁻¹ := by group
      _ = (x * y * (x * y)) * ((x⁻¹ * x⁻¹) * y⁻¹) * y⁻¹ := by rw [hcomm]
      _ = (x * y * (x * y)) * ((x⁻¹ * x⁻¹) * (y⁻¹ * y⁻¹)) := by group
  rw [e]
  exact (rootCenter Q).mul_mem (hsq _ (Q.mul_mem hx hy)) ((rootCenter Q).mul_mem h1 h2)

private theorem eq_one_of_forall_conj_mem_of_simple [IsSimpleGroup K] {M : Subgroup K}
    (hM : M ≠ ⊤) {w : K} (hw : ∀ y : K, y⁻¹ * w * y ∈ M) : w = 1 := by
  haveI := Subgroup.normalCore_normal M
  have hnc : M.normalCore = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M.normalCore with h0 | h1
    · exact h0
    · exfalso
      apply hM
      rw [← top_le_iff, ← h1]
      exact Subgroup.normalCore_le M
  have hw' : w ∈ M.normalCore := by
    intro b
    simpa using hw b⁻¹
  rw [hnc, Subgroup.mem_bot] at hw'
  exact hw'

private theorem aut_eq_one_of_eq_conj_cartan [Finite K] {q i e : ℕ} {P : Subgroup K} {t : K}
    (hc : BenderCore q i e P t) (hZ : Subgroup.center K = ⊥) {d₀ : K} (hd₀ : d₀ ∈ cartan P t)
    {σ : MulAut K} (hσ : ∀ x, σ x = d₀ * x * d₀⁻¹) {k : ℕ} (hk : σ ^ 2 ^ k = 1) : σ = 1 := by
  have hσc : σ = MulAut.conj d₀ := MulEquiv.ext fun x => by rw [hσ x]; rfl
  have h1 : MulAut.conj (d₀ ^ 2 ^ k) = 1 := by rw [map_pow, ← hσc, hk]
  have h2 : d₀ ^ 2 ^ k ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := congrArg (fun a : MulAut K => a g) h1
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc g * d₀ ^ 2 ^ k = (d₀ ^ 2 ^ k * g * (d₀ ^ 2 ^ k)⁻¹) * d₀ ^ 2 ^ k := by rw [this]
      _ = d₀ ^ 2 ^ k * g := by group
  rw [hZ, Subgroup.mem_bot] at h2
  have hodd : Odd (orderOf d₀) :=
    Odd.of_dvd_nat hc.odd_card_cartan (Subgroup.orderOf_dvd_natCard (cartan P t) hd₀)
  have hd1 : d₀ = 1 := RonanF13.eq_one_of_odd_orderOf_of_pow' hodd h2
  rw [hσc, hd1, map_one]

end Aux

theorem BenderType.eq_one_of_sq_eq_one_of_cartan_unitary
    {K : Type*} [Group K] [Finite K] {n e : ℕ} (h : BenderType K n 3 e) (Q : Sylow 2 K) {t : K}
    (ht : t * t = 1) (htQ : t ∉ borel (Q : Subgroup K)) (α : MulAut K) (hα : α * α = 1)
    (hαQ : ∀ x ∈ (Q : Subgroup K), α x ∈ (Q : Subgroup K))
    (hαD : ∀ d ∈ cartan (Q : Subgroup K) t, α d = d) : α = 1 := by
  classical
  have hc := h.benderCore Q ht htQ
  have hn2 : 2 ≤ n := h.two_le.2
  have hq4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  have hαα : ∀ y, α (α y) = y := fun y => by
    have := congrArg (fun f : MulAut K => f y) hα
    simpa using this
  by_cases hout : ∃ g : K, ∀ x : K, α x = g * x * g⁻¹
  ·
    obtain ⟨g, hg⟩ := hout
    have hgc : g * g ∈ Subgroup.center K := by
      rw [Subgroup.mem_center_iff]
      intro x
      have h1 := hαα x
      rw [hg, hg] at h1
      calc x * (g * g) = (g * (g * x * g⁻¹) * g⁻¹) * (g * g) := by rw [h1]
        _ = g * g * x := by group
    rw [h.center_eq_bot, Subgroup.mem_bot] at hgc
    have hgM : g ∈ borel (Q : Subgroup K) := by
      show g ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K)
      rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [← hg]
        exact hαQ x hx
      · intro hx
        rw [← hg] at hx
        have := hαQ _ hx
        rwa [hαα] at this
    have hgD : ∀ d ∈ cartan (Q : Subgroup K) t, g * d = d * g := by
      intro d hd
      have h1 := hαD d hd
      rw [hg] at h1
      calc g * d = (g * d * g⁻¹) * g := by group
        _ = d * g := by rw [h1]
    have hg1 : g = 1 := by
      by_contra hne
      have hord : orderOf g = 2 := orderOf_eq_prime (by rw [sq]; exact hgc) hne
      have hgZ := hc.center_of_involution g hgM hord
      exact hne (hc.eq_one_of_forall_commute (by omega) Q.isPGroup' (rootCenter_le _ hgZ) hgD)
    ext x
    rw [hg x, hg1]
    simp
  ·
    exfalso
    obtain ⟨hWQ, hZW, hWcard, -⟩ := h.lemma_3_4_d5_unitary Q α hα hout hαQ
    have hsq : ∀ x ∈ (Q : Subgroup K), x * x ∈ rootCenter (Q : Subgroup K) :=
      fun x hx => h.sq_mem_rootCenter_unitary Q hx
    have hN : ∀ x ∈ (Q : Subgroup K), ∀ y ∈ commutatorAut (Q : Subgroup K) α,
        x * y * x⁻¹ ∈ commutatorAut (Q : Subgroup K) α := by
      intro x hx y hy
      have h1 := commutator_mem_rootCenter hsq hx (hWQ hy)
      have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
      rw [e]
      exact (commutatorAut (Q : Subgroup K) α).mul_mem (hZW h1) hy
    have hD : ∀ d ∈ cartan (Q : Subgroup K) t, ∀ y ∈ commutatorAut (Q : Subgroup K) α,
        d * y * d⁻¹ ∈ commutatorAut (Q : Subgroup K) α := by
      intro d hd y hy
      have hdM : d ∈ borel (Q : Subgroup K) := cartan_le_borel _ _ hd
      have hdα := hαD d hd
      unfold commutatorAut at hy ⊢
      induction hy using Subgroup.closure_induction with
      | mem x hx =>
        obtain ⟨u, hu, rfl⟩ := hx
        refine Subgroup.subset_closure
          ⟨d * u * d⁻¹, (Subgroup.mem_normalizer_iff.mp hdM u).mp hu, ?_⟩
        simp only [autComm, map_mul, map_inv, hdα]
        group
      | one => simp
      | mul x y _ _ hx hy =>
        have e : d * (x * y) * d⁻¹ = d * x * d⁻¹ * (d * y * d⁻¹) := by group
        rw [e]
        exact Subgroup.mul_mem _ hx hy
      | inv x _ hx =>
        have e : d * x⁻¹ * d⁻¹ = (d * x * d⁻¹)⁻¹ := by group
        rw [e]
        exact Subgroup.inv_mem _ hx
    have hq1 : 1 < 2 ^ n := by omega
    rcases h.normal_trichotomy Q hc hWQ hN hD with hW | hW | hW
    · rw [hW, Subgroup.card_bot] at hWcard
      have : 1 < (2 ^ n) ^ 2 := Nat.one_lt_pow (by norm_num) hq1
      omega
    · rw [hW, hc.card_center] at hWcard
      have : 2 ^ n < (2 ^ n) ^ 2 := by
        calc 2 ^ n = (2 ^ n) ^ 1 := (pow_one _).symm
          _ < (2 ^ n) ^ 2 := Nat.pow_lt_pow_right hq1 (by norm_num)
      omega
    · rw [hW, hc.card_eq] at hWcard
      have : (2 ^ n) ^ 2 < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right hq1 (by norm_num)
      omega

theorem BenderType.aut_eq_one_of_cartan {K : Type} [Group K]
    [Finite K] {n i e : ℕ} (h : BenderType K n i e) (Q : Sylow 2 K) {t : K} (ht : t * t = 1)
    (htQ : t ∉ borel (Q : Subgroup K)) (σ : MulAut K) (hσ2 : ∃ k : ℕ, σ ^ 2 ^ k = 1)
    (hσQ : ∀ x ∈ (Q : Subgroup K), σ x ∈ (Q : Subgroup K))
    (hσD : ∀ d ∈ cartan (Q : Subgroup K) t, σ d = d) : σ = 1 := by
  have hc := h.benderCore Q ht htQ
  obtain ⟨k, hk⟩ := hσ2
  rcases h.cases' with ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, -, -⟩
  · obtain ⟨d₀, hd₀, hσ⟩ := BenderType.aut_eq_conj_cartan_linear h Q ht htQ σ hσQ hσD
    exact aut_eq_one_of_eq_conj_cartan hc h.center_eq_bot hd₀ hσ hk
  · obtain ⟨d₀, hd₀, hσ⟩ := BenderType.aut_eq_conj_cartan_suzuki h Q ht htQ σ hσQ hσD
    exact aut_eq_one_of_eq_conj_cartan hc h.center_eq_bot hd₀ hσ hk
  · induction k generalizing σ with
    | zero => simpa using hk
    | succ k ih =>
      have e : 2 ^ (k + 1) = 2 ^ k + 2 ^ k := by ring
      rw [e, pow_add] at hk
      have hα : σ ^ 2 ^ k = 1 :=
        BenderType.eq_one_of_sq_eq_one_of_cartan_unitary h Q ht htQ (σ ^ 2 ^ k) hk
          (fun x hx => autPow_apply_mem hσQ _ hx)
          (fun d hd => autPow_apply_eq (hσD d hd) _)
      exact ih σ hσQ hσD hα

theorem BenderType.isRigidQuot {K : Type} [Group K] [Finite K]
    {n i e : ℕ} (h : BenderType K n i e) : IsRigidQuot K where
  rigid := by
    intro P
    obtain ⟨t, hc⟩ := h.exists_benderCore P
    have hti : t⁻¹ = t := inv_eq_of_mul_self hc.sq_eq_one
    haveI : IsSimpleGroup K := h.isSimple
    have hne : borel (P : Subgroup K) ≠ ⊤ := by
      intro htop
      apply hc.not_mem
      rw [htop]
      exact Subgroup.mem_top t
    have key : ∀ w : K, (∀ y : K, y⁻¹ * w * y ∈ borel (P : Subgroup K)) → w = 1 :=
      fun w hw => eq_one_of_forall_conj_mem_of_simple hne hw
    refine ⟨t, hc.not_mem, ?_⟩
    rintro σ ⟨k, hk⟩ hσM hσD
    have hρ : σ ^ 2 ^ k = 1 := by
      ext y
      have h1 : y⁻¹ * (σ ^ 2 ^ k) y = 1 := by
        apply key
        intro z
        have e : z⁻¹ * (y⁻¹ * (σ ^ 2 ^ k) y) * z =
            ((y * z)⁻¹ * (σ ^ 2 ^ k) (y * z)) * (z⁻¹ * (σ ^ 2 ^ k) z)⁻¹ := by
          rw [map_mul]
          group
        rw [e]
        exact (borel (P : Subgroup K)).mul_mem (hk (y * z))
          ((borel (P : Subgroup K)).inv_mem (hk z))
      rw [MulAut.one_apply]
      exact (inv_mul_eq_one.mp h1).symm
    have hfix : ∀ d ∈ cartan (P : Subgroup K) t, σ d = d := by
      intro d hd
      have hd1 : d ∈ borel (P : Subgroup K) := cartan_le_borel _ _ hd
      have hd2 : t⁻¹ * d * t ∈ borel (P : Subgroup K) := by
        have h1 := mem_conjugate_iff_mul_inv.mp hd.2
        rw [hti] at h1 ⊢
        exact h1
      exact mul_inv_eq_one.mp (key _ (hσD d hd1 hd2))
    have hσP : ∀ x ∈ (P : Subgroup K), σ x ∈ (P : Subgroup K) := by
      intro x hx
      have h2 : IsPGroup 2 ((P : Subgroup K).map σ.toMonoidHom) :=
        P.isPGroup'.map σ.toMonoidHom
      have h3 := IsPGroup.inf_normalizer_sylow h2 P
      have hxm : σ x ∈ (P : Subgroup K).map σ.toMonoidHom :=
        Subgroup.mem_map_of_mem σ.toMonoidHom hx
      have hxn : σ x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) :=
        hσM x (le_borel _ hx)
      have h4 : σ x ∈ (P : Subgroup K).map σ.toMonoidHom ⊓ (P : Subgroup K) := by
        rw [← h3]
        exact ⟨hxm, hxn⟩
      exact h4.2
    have hσ1 : σ = 1 :=
      BenderType.aut_eq_one_of_cartan h P hc.sq_eq_one hc.not_mem σ ⟨k, hρ⟩ hσP hfix
    intro y
    rw [hσ1, MulAut.one_apply, inv_mul_cancel]
    exact (borel (P : Subgroup K)).one_mem

private theorem IsRigidQuot.of_surjective_aux {K K' : Type*} [Group K] [Group K'] [Finite K]
    (f : K →* K') (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center K)
    (hodd : ∀ z ∈ f.ker, Odd (orderOf z))
    (hchar : ∀ (σ : MulAut K), ∀ z ∈ f.ker, σ z ∈ f.ker) (h : IsRigidQuot K') :
    IsRigidQuot K := by
  have hN : ∀ (P : Sylow 2 K) (a : K),
      a ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) ↔
        f a ∈ Subgroup.normalizer (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K') :=
    fun P a => by
      rw [Sylow.coe_mapSurjective]
      exact ⟨fun ha => Subgroup.le_normalizer_map f ⟨a, ha, rfl⟩,
        fun ha => RonanF13.mem_normalizer_of_central_cover f hker hodd P.isPGroup' ha⟩
  refine ⟨fun P => ?_⟩
  obtain ⟨x', hx', hrig⟩ := h.rigid (P.mapSurjective hf)
  obtain ⟨x, rfl⟩ := hf x'
  refine ⟨x, fun hx => hx' ((hN P x).mp hx), ?_⟩
  rintro σ ⟨k, hk⟩ hσM hσD
  obtain ⟨σ', hσ'⟩ := RonanF13.exists_induced_aut f hf σ fun z =>
    ⟨fun hz => by simpa using hchar σ.symm _ hz, fun hz => hchar σ z hz⟩
  have hpow : ∀ (m : ℕ) (y : K), (σ' ^ m) (f y) = f ((σ ^ m) y) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hσ', ih]
  have hA : ∃ k : ℕ, ∀ y' : K', y'⁻¹ * (σ' ^ 2 ^ k) y' ∈
      Subgroup.normalizer (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K') := by
    refine ⟨k, fun y' => ?_⟩
    obtain ⟨y, rfl⟩ := hf y'
    rw [hpow]
    have := (hN P _).mp (hk y)
    simpa [map_mul, map_inv] using this
  have hB : ∀ m' ∈ Subgroup.normalizer
      (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K'),
      σ' m' ∈ Subgroup.normalizer
        (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K') := by
    intro m' hm'
    obtain ⟨m, rfl⟩ := hf m'
    rw [hσ']
    exact (hN P (σ m)).mp (hσM m ((hN P m).mpr hm'))
  have hC : ∀ d' ∈ Subgroup.normalizer
      (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K'),
      (f x)⁻¹ * d' * f x ∈ Subgroup.normalizer
        (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K') →
      ∀ y' : K', y'⁻¹ * (σ' d' * d'⁻¹) * y' ∈ Subgroup.normalizer
        (((P.mapSurjective hf : Sylow 2 K') : Subgroup K') : Set K') := by
    intro d' hd' hxd' y'
    obtain ⟨d, rfl⟩ := hf d'
    obtain ⟨y, rfl⟩ := hf y'
    have hd : d ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) := (hN P d).mpr hd'
    have hxd : x⁻¹ * d * x ∈ Subgroup.normalizer ((P : Subgroup K) : Set K) :=
      (hN P _).mpr (by simpa [map_mul, map_inv] using hxd')
    have := (hN P _).mp (hσD d hd hxd y)
    simpa [map_mul, map_inv, hσ'] using this
  intro y
  have := hrig σ' hA hB hC (f y)
  exact (hN P _).mpr (by simpa [map_mul, map_inv, hσ'] using this)

theorem IsRigidQuot.of_surjective {K K' : Type*} [Group K] [Group K'] [Finite K] (f : K →* K')
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center K)
    (hodd : ∀ z ∈ f.ker, Odd (orderOf z)) (hZ : Subgroup.center K' = ⊥) (h : IsRigidQuot K') :
    IsRigidQuot K := by
  refine IsRigidQuot.of_surjective_aux f hf hker hodd (fun σ z hz => ?_) h
  have hzc : z ∈ Subgroup.center K := hker hz
  have hσz : σ z ∈ Subgroup.center K := by
    rw [Subgroup.mem_center_iff]
    intro g
    have h1 := Subgroup.mem_center_iff.mp hzc (σ.symm g)
    have h2 := congrArg σ h1
    simpa [map_mul] using h2
  have hfz : f (σ z) ∈ Subgroup.center K' := by
    rw [Subgroup.mem_center_iff]
    intro a'
    obtain ⟨a, rfl⟩ := hf a'
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hσz a]
  rw [hZ, Subgroup.mem_bot] at hfz
  exact MonoidHom.mem_ker.mpr hfz

theorem IsRigidQuot.of_mulEquiv {K K' : Type*} [Group K] [Group K'] [Finite K] (e : K ≃* K')
    (h : IsRigidQuot K') : IsRigidQuot K := by
  have hker : ∀ z ∈ e.toMonoidHom.ker, z = 1 := fun z hz => e.injective (by simpa using hz)
  exact IsRigidQuot.of_surjective_aux e.toMonoidHom e.surjective
    (fun z hz => by rw [hker z hz]; exact Subgroup.one_mem _)
    (fun z hz => by rw [hker z hz, orderOf_one]; exact odd_one)
    (fun σ z hz => by rw [hker z hz, map_one]; exact Subgroup.one_mem _) h

theorem isRigidQuot_of_listed {K : Type} [Group K] [Finite K]
    (hK : IsRankOneListed K) (hs : ¬ Group.IsSolvable K) : IsRigidQuot K := by
  rcases cases_of_listed_of_not_isSolvable hK hs with ⟨n, hn, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩ |
    ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩ | ⟨n, hn, F, i1, i2, hF, ⟨e⟩⟩
  · exact BenderType.isRigidQuot (BenderType.linear n hn e)
  · exact BenderType.isRigidQuot
      (BenderType.suzuki a ha (e.trans (MulEquiv.subgroupCongr (szModel_eq_open_sz a).symm)))
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    let π : StatedSU 3 (2 ^ n) F →* StatedProj (StatedSU 3 (2 ^ n) F) :=
      QuotientGroup.mk' ((StatedScalars (Fin 3) F).subgroupOf (StatedSU 3 (2 ^ n) F))
    have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
    haveI : Finite (StatedProj (StatedSU 3 (2 ^ n) F)) := Finite.of_surjective π hπ
    refine IsRigidQuot.of_mulEquiv e (IsRigidQuot.of_surjective π hπ ?_ ?_ hB.center_eq_bot
      (BenderType.isRigidQuot hB))
    · show π.ker ≤ _
      rw [QuotientGroup.ker_mk']
      exact statedSU_scalars_le_center
    · intro z hz
      rw [QuotientGroup.ker_mk'] at hz
      exact statedSU_three_scalars_odd z hz
  · obtain ⟨e', hB⟩ := benderType_statedProj hn hF
    exact BenderType.isRigidQuot (hB.of_mulEquiv e.symm)

end CFSG.Quasithin.F112Crit

end
