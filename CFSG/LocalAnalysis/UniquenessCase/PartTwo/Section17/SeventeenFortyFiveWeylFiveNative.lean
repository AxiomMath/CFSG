module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFiveWeylFiveNativeSplit
import CFSG.LocalAnalysis.RankFourTheoremC.InvariantTwo.KFacts.I294CrossExcToral
import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

private theorem baseChangeGL_conj_entrywise
    {τ : Tag} {K K' : Type} [Field K] [Field K'] (ι : K →+* K') (σ : K ≃+* K)
    (σ' : K' ≃+* K') (hσ : ∀ c, σ' (ι c) = ι (σ c)) (g : ModGL τ K)
    (a : Fin τ.rank → Kˣ) (y : ModGL τ K) :
    baseChangeGL ι ((g * rootDiagUnit τ a) * Units.map (entrywiseHom σ.toRingHom) y *
        (g * rootDiagUnit τ a)⁻¹) =
      (baseChangeGL ι g * rootDiagUnit τ (fun i => Units.map ι.toMonoidHom (a i))) *
        Units.map (entrywiseHom σ'.toRingHom) (baseChangeGL ι y) *
        (baseChangeGL ι g * rootDiagUnit τ (fun i => Units.map ι.toMonoidHom (a i)))⁻¹ := by
  have hcomp : σ'.toRingHom.comp ι = ι.comp σ.toRingHom := RingHom.ext hσ
  have hmid : baseChangeGL ι (Units.map (entrywiseHom σ.toRingHom) y) =
      Units.map (entrywiseHom σ'.toRingHom) (baseChangeGL ι y) := by
    rw [CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      CFSG.RankThree.Chevalley.units_map_entrywiseHom_eq_baseChangeGL_self,
      baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, hcomp]
  simp only [map_mul, map_inv, baseChangeGL_rootDiagUnit, hmid]

theorem weylFive_native
    {τ : Tag} (hτ : τ = .G2 ∨ τ = .D4 ∨ τ = .F4) {K : Type} [Field K]
    [Finite K] (hK : ringChar K ≠ 31) {G : Subgroup (ModGL τ K)} (hG : G ≤ adjointGroup τ K)
    (g : ModGL τ K) (hg : g ∈ adjointGroup τ K) (a : Fin τ.rank → Kˣ) (σ : K ≃+* K)
    (α : MulAut G)
    (hα : ∀ x : G, (α x : ModGL τ K) = (g * rootDiagUnit τ a) *
      Units.map (entrywiseHom σ.toRingHom) (x : ModGL τ K) * (g * rootDiagUnit τ a)⁻¹)
    (E : Subgroup G) (hE : ∀ x ∈ E, x ^ 31 = 1) (hαE : E.map α.toMonoidHom = E) :
    ∃ k : ℕ, ∀ x ∈ E, (α ^ Nat.card (WeylGroup τ)) x = x ^ k := by
  classical
  obtain ⟨ℓ, hℓ⟩ := CharP.exists K
  have : CharP K ℓ := hℓ
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨-, hℓp, -⟩ := FiniteField.card K ℓ
  have : Fact ℓ.Prime := ⟨hℓp⟩
  let : Algebra (ZMod ℓ) K := ZMod.algebra K ℓ
  set f := Module.finrank (ZMod ℓ) K with hf
  have hKf : ℓ ^ f = Nat.card K := by
    rw [hf]
    exact FiniteField.pow_finrank_eq_natCard ℓ K
  have hf0 : f ≠ 0 := by
    rw [hf]
    exact Module.finrank_pos.ne'
  have hfm : f * 30 ≠ 0 := Nat.mul_ne_zero hf0 (by norm_num)
  have hK'card : Nat.card (GaloisField ℓ (f * 30)) = Nat.card K ^ 30 := by
    rw [GaloisField.card ℓ (f * 30) hfm, pow_mul, hKf]
  have h31K : ¬ 31 ∣ Nat.card K := by
    rintro ⟨m, hm⟩
    have hℓ31 : ℓ ≠ 31 := by
      intro h
      exact hK (by rw [ringChar.eq K ℓ, h])
    have h1 : 31 ∣ ℓ ^ f := by
      rw [hKf]
      exact ⟨m, hm⟩
    have h2 : 31 ∣ ℓ := (by norm_num : Nat.Prime 31).dvd_of_dvd_pow h1
    exact hℓ31 ((Nat.prime_dvd_prime_iff_eq (by norm_num : Nat.Prime 31) hℓp).1 h2).symm
  have hdvd : 31 ∣ Nat.card (GaloisField ℓ (f * 30)) - 1 := by
    rw [hK'card]
    exact CFSG.LocalAnalysis.RankFourTheoremC.crossExc_dvd_pow_pred_sub_one (p := 31)
      (q := Nat.card K) (by norm_num) h31K
  obtain ⟨ι⟩ : Nonempty (K →ₐ[ZMod ℓ] GaloisField ℓ (f * 30)) :=
    FiniteField.nonempty_algHom_of_finrank_dvd (F := ZMod ℓ) (K := K)
      (L := GaloisField ℓ (f * 30)) (by
        rw [GaloisField.finrank ℓ hfm, ← hf]
        exact dvd_mul_right f 30)
  let σa : K ≃ₐ[ZMod ℓ] K :=
    { toRingEquiv := σ
      commutes' := fun c => by
        have h : (σ : K →+* K).comp (algebraMap (ZMod ℓ) K) = algebraMap (ZMod ℓ) K :=
          RingHom.ext_zmod _ _
        exact DFunLike.congr_fun h c }
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow (ZMod ℓ) K).2 σa
  let σ' : GaloisField ℓ (f * 30) ≃+* GaloisField ℓ (f * 30) :=
    RingEquiv.ofBijective (iterateFrobenius (GaloisField ℓ (f * 30)) ℓ (n : ℕ))
      ⟨iterateFrobenius_inj (GaloisField ℓ (f * 30)) ℓ (n : ℕ),
        Finite.surjective_of_injective
          (iterateFrobenius_inj (GaloisField ℓ (f * 30)) ℓ (n : ℕ))⟩
  have hσ' : ∀ c : K, σ' (ι c) = ι (σ c) := by
    intro c
    have h1 : σ c = c ^ (ℓ ^ (n : ℕ)) := by
      have h2 : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod ℓ) K ^ (n : ℕ)) c =
          c ^ (Fintype.card (ZMod ℓ) ^ (n : ℕ)) := by
        rw [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate]
      have h3 : (FiniteField.frobeniusAlgEquivOfAlgebraic (ZMod ℓ) K ^ (n : ℕ)) c = σ c := by
        have h4 := congrArg (fun e : K ≃ₐ[ZMod ℓ] K => e c) hn
        simpa [σa] using h4
      rw [h3] at h2
      rw [ZMod.card] at h2
      exact h2
    show iterateFrobenius (GaloisField ℓ (f * 30)) ℓ (n : ℕ) (ι c) = ι (σ c)
    rw [iterateFrobenius_def, ← map_pow, ← h1]
  set a' : Fin τ.rank → (GaloisField ℓ (f * 30))ˣ :=
    fun i => Units.map ι.toRingHom.toMonoidHom (a i) with ha'
  set g' : ModGL τ (GaloisField ℓ (f * 30)) := baseChangeGL ι.toRingHom g with hg'def
  set θ' : ModGL τ (GaloisField ℓ (f * 30)) → ModGL τ (GaloisField ℓ (f * 30)) :=
    fun y => g' * rootDiagUnit τ a' * Units.map (entrywiseHom σ'.toRingHom) y *
      (g' * rootDiagUnit τ a')⁻¹ with hθ'def
  have hsquare : ∀ y : ModGL τ K,
      baseChangeGL ι.toRingHom ((g * rootDiagUnit τ a) *
        Units.map (entrywiseHom σ.toRingHom) y * (g * rootDiagUnit τ a)⁻¹) =
      θ' (baseChangeGL ι.toRingHom y) :=
    fun y => baseChangeGL_conj_entrywise ι.toRingHom σ σ' hσ' g a y
  set E' : Subgroup (ModGL τ (GaloisField ℓ (f * 30))) :=
    (E.map G.subtype).map (baseChangeGL ι.toRingHom) with hE'def
  have hgm' : g' ∈ adjointGroup τ (GaloisField ℓ (f * 30)) := by
    rw [hg'def]
    exact baseChangeGL_mem_adjointGroup ι.toRingHom hg
  have hE'exp : ∀ x ∈ E', x ^ 31 = 1 := by
    intro x hx
    rw [hE'def] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    change (baseChangeGL ι.toRingHom (z : ModGL τ K)) ^ 31 = 1
    have hz31 : (z : ModGL τ K) ^ 31 = 1 := by
      have h := hE z hz
      simpa using congrArg (fun w : G => (w : ModGL τ K)) h
    rw [← map_pow, hz31, map_one]
  have hE'C : E' ≤ adjointGroup τ (GaloisField ℓ (f * 30)) := by
    intro x hx
    rw [hE'def] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    exact baseChangeGL_mem_adjointGroup ι.toRingHom (hG z.2)
  have hE'inv : ∀ y ∈ E.map G.subtype, θ' (baseChangeGL ι.toRingHom y) ∈ E' := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hy
    change θ' (baseChangeGL ι.toRingHom (z : ModGL τ K)) ∈ E'
    have hzα : α z ∈ E := by
      rw [← hαE]
      exact Subgroup.mem_map_of_mem α.toMonoidHom hz
    have hmem : baseChangeGL ι.toRingHom (((α z : G) : ModGL τ K)) ∈ E' := by
      rw [hE'def]
      exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hzα)
    rw [show θ' (baseChangeGL ι.toRingHom (z : ModGL τ K)) =
        baseChangeGL ι.toRingHom (((α z : G) : ModGL τ K)) from by
      rw [← hsquare (z : ModGL τ K), ← hα z]]
    exact hmem
  have hE'θ : ∀ x ∈ E', θ' x ∈ E' := by
    intro x hx
    rw [hE'def] at hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
    exact hE'inv y hy
  obtain ⟨k, hk⟩ := weylFive_native_split (τ := τ) hτ hdvd g' hgm' a' σ' E' hE'C hE'exp hE'θ
  have hk' : ∀ x ∈ E', θ'^[Nat.card (WeylGroup τ)] x = x ^ k := hk
  refine ⟨k, fun x hx => ?_⟩
  apply Subtype.ext
  apply baseChangeGL_injective ι.toRingHom
  have hx' : baseChangeGL ι.toRingHom (x : ModGL τ K) ∈ E' := by
    rw [hE'def]
    exact Subgroup.mem_map_of_mem _ (Subgroup.mem_map_of_mem _ hx)
  have hbase : ∀ (m : ℕ) (y : G),
      baseChangeGL ι.toRingHom (((α ^ m) y : G) : ModGL τ K) =
        θ'^[m] (baseChangeGL ι.toRingHom (y : ModGL τ K)) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      calc baseChangeGL ι.toRingHom (((α ^ (m + 1)) y : G) : ModGL τ K)
          = baseChangeGL ι.toRingHom (((α ^ m) (α y) : G) : ModGL τ K) := by
            rw [pow_succ, MulAut.mul_apply]
        _ = θ'^[m] (baseChangeGL ι.toRingHom (((α y : G) : ModGL τ K))) := ih (α y)
        _ = θ'^[m] (θ' (baseChangeGL ι.toRingHom (y : ModGL τ K))) := by
            rw [← hsquare (y : ModGL τ K), ← hα y]
        _ = θ'^[m + 1] (baseChangeGL ι.toRingHom (y : ModGL τ K)) := by
            rw [Function.iterate_succ_apply]
  rw [hbase (Nat.card (WeylGroup τ)) x, hk' (baseChangeGL ι.toRingHom (x : ModGL τ K)) hx',
    ← map_pow]
  simp

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.SzFive
