module

public import CFSG.LocalAnalysis.StandardType.GGTBE6IndTwistNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTDModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTBE6Witness
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.GroupTheory.ConjKerCenter

public noncomputable section

namespace CFSG.StandardType.TBE6IndTwist

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Minuscule CFSG.LieType.Steinberg.Isogeny
  CFSG.LieType.Steinberg.TwistedE6 CFSG.LieType.Steinberg.CentralExt.MinusculeClosed
  CFSG.StandardType.TwE6Lang CFSG.RankThree.CentralCover
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.StandardType.TableBExc

variable {K L : Type} [Field K] [Finite K] [CharP K 2] [Group L]
  (θ : K ≃+* K) (hθ : ∀ c, θ.toRingHom (θ.toRingHom c) = c)
  (l : K) (hl : θ.toRingHom l = l + 1)
  (φ : fixedGroup K θ.toRingHom →* L)
  (δ : (Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) →* MulAut L)

def scalarRoot {m : ℕ} (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (i : Fin Tag.E6.rank) (τ : MulAut L) : Multiplicative (ZMod m) :=
  e (Function.invFun δ τ i)

def scalarWitness {m : ℕ} (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (A : Subgroup (MulAut L))
    (hn : ∀ i : Fin Tag.E6.rank, MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) ∈
      Subgroup.normalizer (A : Set (MulAut L))) : GGTorusTorWit m 6 L A where
  T := δ.range
  α := scalarRoot θ δ e
  cor i := (φ.comp (langCoroot K θ hθ l hl i)).comp e.symm.toMonoidHom
  n i := φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))
  hn := hn
  Tsc := (φ.comp (langTorusHom K θ hθ l hl)).range

theorem scalarWitness_n {m : ℕ} (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (A : Subgroup (MulAut L))
    (hn : ∀ i : Fin Tag.E6.rank, MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) ∈
      Subgroup.normalizer (A : Set (MulAut L))) :
    (scalarWitness θ hθ l hl φ δ e A hn).n =
      fun i => φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i)) := by
  rfl

theorem scalarRoot_apply {m : ℕ} (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (hδ : Function.Injective δ) (i : Fin Tag.E6.rank)
    (b : Fin Tag.E6.rank → CFSG.LieType.Steinberg.normOne θ) :
    scalarRoot θ δ e i (δ b) = e (b i) := by
  rw [scalarRoot, Function.leftInverse_invFun hδ b]

theorem scalarRoot_mul {m : ℕ} (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (hδ : Function.Injective δ) (i : Fin Tag.E6.rank) {τ υ : MulAut L}
    (hτ : τ ∈ δ.range) (hυ : υ ∈ δ.range) :
    scalarRoot θ δ e i (τ * υ) = scalarRoot θ δ e i τ * scalarRoot θ δ e i υ := by
  obtain ⟨b, rfl⟩ := hτ
  obtain ⟨c, rfl⟩ := hυ
  rw [← map_mul, scalarRoot_apply θ δ e hδ, scalarRoot_apply θ δ e hδ,
    scalarRoot_apply θ δ e hδ]
  exact map_mul e _ _

theorem scalar_torus_comm {τ υ : MulAut L} (hτ : τ ∈ δ.range) (hυ : υ ∈ δ.range) :
    τ * υ = υ * τ := by
  obtain ⟨b, rfl⟩ := hτ
  obtain ⟨c, rfl⟩ := hυ
  rw [← map_mul, ← map_mul, mul_comm]

theorem scalarRoot_separates {m : ℕ} (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (hδ : Function.Injective δ) {τ : MulAut L} (hτ : τ ∈ δ.range)
    (h : ∀ i, scalarRoot θ δ e i τ = 1) : τ = 1 := by
  obtain ⟨b, rfl⟩ := hτ
  have hb : b = 1 := by
    funext i
    apply e.injective
    change e (b i) = e 1
    rw [map_one]
    exact (scalarRoot_apply θ δ e hδ i b).symm.trans (h i)
  rw [hb, map_one]

theorem scalar_descent_formulas {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x)) :
    (∀ b i s, δ b (φ (langCoroot K θ hθ l hl i s)) = φ (langCoroot K θ hθ l hl i s)) ∧
    (∀ b i, δ b (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) =
      φ (langCoroot K θ hθ l hl i (b i)) *
        φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) ∧
    (∀ b u, δ b (φ (langTorusHom K θ hθ l hl u)) = φ (langTorusHom K θ hθ l hl u)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro b i s
    rw [hδ, fixedDiagonalHom_langCoroot]
  · intro b i
    rw [hδ, fixedDiagonalHom_langWeyl_simple, map_mul]
  · intro b u
    rw [hδ, fixedDiagonalHom_langTorusHom]

theorem scalar_descent_conj {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hφs : Function.Surjective φ)
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (i : Fin Tag.E6.rank) (s : CFSG.LieType.Steinberg.normOne θ) :
    δ (fun j => s ^ Tag.E6.cartan i j) = MulAut.conj (φ (langCoroot K θ hθ l hl i s)) := by
  apply MulEquiv.ext
  intro x
  obtain ⟨y, rfl⟩ := hφs x
  rw [hδ, fixedDiagonalHom_eq_conj_langCoroot]
  change φ (langCoroot K θ hθ l hl i s * y * (langCoroot K θ hθ l hl i s)⁻¹) = _
  rw [map_mul, map_mul, map_inv]
  rfl

theorem scalar_descent_injective {f : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (hf : 1 ≤ f) (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hφ : ∀ x, ψ (φ x) = CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x)
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x)) : Function.Injective δ := by
  rw [injective_iff_map_eq_one]
  intro b hb
  have hmove := (scalar_descent_formulas θ hθ l hl φ δ hK hδ).2.1
  have hb1 : b = 1 := by
    funext i
    have he := hmove b i
    rw [hb, MulAut.one_apply] at he
    have hc : φ (langCoroot K θ hθ l hl i (b i)) = 1 := by
      have h' : 1 * φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i)) =
          φ (langCoroot K θ hθ l hl i (b i)) *
            φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i)) := by
        simpa only [one_mul] using he
      exact (mul_right_cancel h').symm
    have hi := cover_langCoroot_injective K θ hθ l hl hf hK hθq φ ψ hφ i
    have hs : b i = 1 := hi (hc.trans (map_one _).symm)
    exact hs
  exact hb1

theorem scalar_holdsOne {f m : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hφ : ∀ x, ψ (φ x) = CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x)
    (hφs : Function.Surjective φ) (hδi : Function.Injective δ)
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (A : Subgroup (MulAut L)) (hA : A ≤ δ.range)
    (hn : ∀ i : Fin Tag.E6.rank, MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) ∈
      Subgroup.normalizer (A : Set (MulAut L))) :
    GGTDHoldsOne (scalarWitness θ hθ l hl φ δ e A hn) CartanMatrix.E₆ := by
  have hconj := scalar_descent_conj θ hθ l hl φ δ hK hφs hδ
  have hfix := (scalar_descent_formulas θ hθ l hl φ δ hK hδ).1
  refine ⟨fun x hx y hy => scalar_torus_comm θ δ hx hy, hA, ?_,
    fun i x hx y hy => scalarRoot_mul θ δ e hδi i hx hy,
    ?_, ?_, ?_, ?_⟩
  · intro i s
    refine ⟨fun j => e.symm s ^ Tag.E6.cartan i j, ?_⟩
    exact hconj i (e.symm s)
  · intro i
    exact (cover_langCoroot_injective K θ hθ l hl hf hK hθq φ ψ hφ i).comp e.symm.injective
  · intro i j s t
    exact (langCoroot_commute K θ hθ l hl i j (e.symm s) (e.symm t)).map φ
  · rintro τ ⟨b, rfl⟩ i s
    exact hfix b i (e.symm s)
  · intro i j s
    change scalarRoot θ δ e i (MulAut.conj (φ (langCoroot K θ hθ l hl j (e.symm s)))) =
      s ^ CartanMatrix.E₆ i j
    rw [← hconj j (e.symm s)]
    have he := scalarRoot_apply θ δ e hδi i (fun j₁ => e.symm s ^ Tag.E6.cartan j j₁)
    rw [he, map_zpow, e.apply_symm_apply]
    congr 1
    change Tag.E6.cartan j i = CartanMatrix.E₆ i j
    calc Tag.E6.cartan j i = Tag.E6.cartan i j := cartan_E6_symm j i
      _ = CartanMatrix.E₆ i j := congrFun (congrFun (cartanE_eq 6) i) j

theorem scalar_holdsTwo {f m : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hδi : Function.Injective δ)
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (A : Subgroup (MulAut L))
    (hroot : ∀ i, ∃ a ∈ A, scalarRoot θ δ e i a ≠ 1)
    (hn : ∀ i : Fin Tag.E6.rank, MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) ∈
      Subgroup.normalizer (A : Set (MulAut L))) :
    GGTDHoldsTwo (scalarWitness θ hθ l hl φ δ e A hn) := by
  have hfix := (scalar_descent_formulas θ hθ l hl φ δ hK hδ).1
  have hmove := (scalar_descent_formulas θ hθ l hl φ δ hK hδ).2.1
  have hcb : ∀ i τ, τ ∈ δ.range →
      φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i)) *
        (τ (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))))⁻¹ =
      (φ (langCoroot K θ hθ l hl i (e.symm (scalarRoot θ δ e i τ))))⁻¹ := by
    rintro i τ ⟨b, rfl⟩
    rw [hmove, scalarRoot_apply θ δ e hδi, e.symm_apply_apply]
    group
  refine ⟨?_, hcb, fun τ hτ => scalarRoot_separates θ δ e hδi hτ, hroot⟩
  intro i τ hτ
  obtain ⟨b, rfl⟩ := hτ
  exact TBE6.reflection_of_coboundary (hfix b i _ ) (hcb i (δ b) ⟨b, rfl⟩)

theorem scalar_iSup_coroot_range {m : ℕ}
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m)) :
    (⨆ i : Fin Tag.E6.rank, (((φ.comp (langCoroot K θ hθ l hl i)).comp e.symm.toMonoidHom)).range) =
      (φ.comp (langTorusHom K θ hθ l hl)).range := by
  have hr : ∀ i : Fin Tag.E6.rank, (((φ.comp (langCoroot K θ hθ l hl i)).comp e.symm.toMonoidHom)).range =
      (φ.comp (langCoroot K θ hθ l hl i)).range := by
    intro i
    ext x
    constructor
    · rintro ⟨s, rfl⟩
      exact ⟨e.symm s, rfl⟩
    · rintro ⟨s, rfl⟩
      exact ⟨e s, by simp⟩
  simp_rw [hr, MonoidHom.range_comp, ← Subgroup.map_iSup, ← range_langTorusHom]

theorem scalar_inner_centralizer {f p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) [NeZero p]
    (hφs : Function.Surjective φ)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (A : Subgroup (MulAut L))
    (hA : ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range).map (MulAut.conj : L →* MulAut L) = A)
    (x : L) (hx : ∀ a ∈ A, MulAut.conj x * a = a * MulAut.conj x) :
    x ∈ (φ.comp (langTorusHom K θ hθ l hl)).range := by
  have hK4 : 4 ≤ Nat.card K := by
    rw [hK]
    have hq : 2 ≤ 2 ^ f := (show 2 ^ 1 ≤ 2 ^ f from Nat.pow_le_pow_right (by decide) hf)
    nlinarith
  let : Group.IsPerfect (fixedGroup K θ.toRingHom) := fixedGroup_isPerfect_of_four_le_card θ.toRingHom hθ hK4
  have hZF : Nat.card (Subgroup.center (fixedGroup K θ.toRingHom)) ∣ 3 := by
    rw [(CFSG.LieType.Steinberg.CentralExt.TwistedE6Closed.card_center_fixedGroup hK hθq).1]
    exact Nat.gcd_dvd_left _ _
  have hcomap := CFSG.ComponentClassification.Quasisimple.center_comap_of_central_kernel φ hφs hφc
  have hZmap : Subgroup.center L = (Subgroup.center (fixedGroup K θ.toRingHom)).map φ := by
    rw [← hcomap, Subgroup.map_comap_eq_self_of_surjective hφs]
  have hZL : Nat.card (Subgroup.center L) ∣ 3 := by
    rw [hZmap]
    exact (Subgroup.card_map_dvd _ _).trans hZF
  have hc : Nat.Coprime p (Nat.card (MulAut.conj : L →* MulAut L).ker) := by
    rw [CFSG.GroupTheory.ker_conj_eq_center]
    exact ((Nat.coprime_primes hp Nat.prime_three).mpr hp3).of_dvd_right hZL
  have hx' : x ∈ Subgroup.centralizer ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range : Set L) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hya : MulAut.conj y ∈ A := hA ▸ Subgroup.mem_map_of_mem _ hy
    have he := hx (MulAut.conj y) hya
    have hmap : MulAut.conj (x * y * x⁻¹) = MulAut.conj y := by
      rw [map_mul, map_mul, map_inv, he, mul_inv_cancel_right]
    have hyp : y ^ p = 1 := by
      obtain ⟨a, rfl⟩ := hy
      rw [← map_pow, pow_eq_one_of_zmod, map_one]
    have hxy : x * y * x⁻¹ = y :=
      CFSG.StandardType.OrthRest.eq_of_lift_of_coprime (by rw [CFSG.GroupTheory.ker_conj_eq_center]) hc hmap
        (by rw [conj_pow, hyp, mul_one, mul_inv_cancel]) hyp
    exact (mul_inv_eq_iff_eq_mul.mp hxy).symm
  exact cover_centralizer_langPFrame_le K θ hθ l hl hf hK hθq hp hp2 hp3 ζ hζ hζo φ hφs hφc hx'

theorem scalar_holdsThree_of_cent {f m : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (A : Subgroup (MulAut L)) (hAD : A ≤ δ.range)
    (hn : ∀ i : Fin Tag.E6.rank, MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) ∈
      Subgroup.normalizer (A : Set (MulAut L)))
    (hcent : ∀ x : L, (∀ a ∈ A, MulAut.conj x * a = a * MulAut.conj x) →
      x ∈ (φ.comp (langTorusHom K θ hθ l hl)).range) :
    GGTDHoldsThree (scalarWitness θ hθ l hl φ δ e A hn) := by
  have hfixed := (scalar_descent_formulas θ hθ l hl φ δ hK hδ).2.2
  have hr := scalar_iSup_coroot_range θ hθ l hl φ e
  refine ⟨?_, ?_, fun x hx => Subgroup.mem_sup_left (hcent x hx), ?_, ?_⟩
  · intro a ha hin
    obtain ⟨x, rfl⟩ := hin
    refine ⟨x, ?_, rfl⟩
    change x ∈ ⨆ i : Fin Tag.E6.rank, (((φ.comp (langCoroot K θ hθ l hl i)).comp e.symm.toMonoidHom)).range
    rw [hr]
    apply hcent x
    intro b hb
    exact scalar_torus_comm θ δ (hAD ha) (hAD hb)
  · intro z hz ho
    apply hcent z
    intro a ha
    have he : MulAut.conj z = 1 := by
      rw [← MonoidHom.mem_ker, CFSG.GroupTheory.ker_conj_eq_center]
      exact hz
    rw [he, one_mul, mul_one]
  · rintro τ ⟨b, rfl⟩ x ⟨u, rfl⟩
    exact hfixed b u
  · intro x hx hxm
    change x ∈ ⨆ i : Fin Tag.E6.rank, (((φ.comp (langCoroot K θ hθ l hl i)).comp e.symm.toMonoidHom)).range
    rw [hr]
    exact hx

theorem scalar_holdsThree {f m p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) [NeZero p]
    (hφs : Function.Surjective φ)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom))
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (A : Subgroup (MulAut L)) (hAD : A ≤ δ.range)
    (hA : ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range).map (MulAut.conj : L →* MulAut L) = A)
    (hn : ∀ i : Fin Tag.E6.rank, MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) ∈
      Subgroup.normalizer (A : Set (MulAut L))) :
    GGTDHoldsThree (scalarWitness θ hθ l hl φ δ e A hn) :=
  scalar_holdsThree_of_cent θ hθ l hl φ δ hK hδ e A hAD hn
    (fun x hx => scalar_inner_centralizer θ hθ l hl φ hf hK hθq hp hp2 hp3 hφs hφc ζ hζ hζo A hA x hx)

theorem scalar_frame_torsion {f p : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp3 : p ≠ 3) [NeZero p]
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (x : L) : x ∈ (φ.comp (langPFrame K θ hθ l hl ζ hζ)).range ↔
      x ^ p = 1 ∧ x ∈ (φ.comp (langTorusHom K θ hθ l hl)).range := by
  constructor
  · rintro ⟨a, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [← map_pow, pow_eq_one_of_zmod, map_one]
    · refine ⟨fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (Multiplicative.toAdd a i)), ?_⟩
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, langPFrame_apply]
  · rintro ⟨hxp, hx⟩
    exact cover_langTorusHom_torsion K θ hθ l hl hK hθq hp hp3 ζ hζ hζo φ hφc hx hxp

theorem scalar_holdsFour {f m p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) [NeZero p]
    (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hφ : ∀ x, ψ (φ x) = CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x)
    (hφs : Function.Surjective φ)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (A : Subgroup (MulAut L))
    (hA : ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range).map (MulAut.conj : L →* MulAut L) = A) :
    ∃ hn : ∀ i : Fin Tag.E6.rank, MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) ∈
      Subgroup.normalizer (A : Set (MulAut L)),
      GGTDHoldsFour (scalarWitness θ hθ l hl φ δ e A hn) CoxeterMatrix.E₆ := by
  let : Fact p.Prime := ⟨hp⟩
  let q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq
  have hqs : Function.Surjective q := CFSG.SeitzReduction.F4Pilot.twistedIsogenyC_surjective hf hK θ.toRingHom hθq
  have hqc : q.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom) :=
    (CFSG.SeitzReduction.F4Pilot.ker_twistedIsogenyC hf hK θ.toRingHom hθq).le
  obtain ⟨hnE, eW, heW⟩ := cover_marked_langPFrame K θ hθ l hl hf hK hθq hp hp2 hp3 ζ hζ hζo q hqs hqc
  let E := (q.comp (langPFrame K θ hθ l hl ζ hζ)).range
  let Λ := ReflInner.liftConj ψ hψ hker
  have hZR : Subgroup.center (graphFixedRootGroup TwistTag.E6 K θ.toRingHom) = ⊥ :=
    center_graphFixedRootGroup_eq_bot θ.surjective
  have hΛ : Function.Injective Λ := ReflInner.liftConj_injective hψ hker hZR
  have hΛn : ∀ x, Λ (ψ x) = MulAut.conj x := fun _ => ReflInner.liftConj_eq hψ hker rfl
  have hEA : E.map Λ = A := by
    rw [← hA]
    change ((q.comp (langPFrame K θ hθ l hl ζ hζ)).range).map Λ = _
    rw [← MonoidHom.range_comp, ← MonoidHom.range_comp]
    apply congrArg MonoidHom.range
    apply MonoidHom.ext
    intro a
    change Λ (q (langPFrame K θ hθ l hl ζ hζ a)) =
      MulAut.conj (φ (langPFrame K θ hθ l hl ζ hζ a))
    rw [← hφ, hΛn]
  obtain ⟨hnA, eA, heA⟩ := markedWeyl_map E Λ hΛ hEA
    (fun i => q (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) hnE eW heW
  have hr : Λ.range = (MulAut.conj : L →* MulAut L).range := by
    ext a
    constructor
    · rintro ⟨x, rfl⟩
      obtain ⟨y, rfl⟩ := hψ x
      exact ⟨y, (hΛn y).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨ψ x, hΛn x⟩
  have hnval : ∀ i, Λ (q (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) =
      MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) := by
    intro i
    rw [← hφ, hΛn]
  have hn : ∀ i : Fin Tag.E6.rank, MulAut.conj (φ (langWeylHom K θ.toRingHom hθ hl (simple .E6 i))) ∈
      Subgroup.normalizer (A : Set (MulAut L)) := by
    intro i
    rw [← hnval i]
    exact hnA i
  let eA' := eA.trans (MulEquiv.subgroupCongr (congrArg (fun I => ggAutomizer I A) hr))
  have hmark : ∀ i, (eA' (simple .E6 i) : MulAut ↥A) = ggConjAut A (hn i) := by
    intro i
    change (eA (simple .E6 i) : MulAut ↥A) = ggConjAut A (hn i)
    apply (heA i).trans
    apply MulEquiv.ext
    intro a
    apply Subtype.ext
    simp only [ggConjAut_apply, hnval]
  let ec : CoxeterMatrix.E₆.Group ≃* ↥(ggAutomizer (MulAut.conj : L →* MulAut L).range A) :=
    ggE6Row_coxeterGroupEquiv.trans eA'
  have hc : ∀ i, (ec (CoxeterMatrix.E₆.simple i) : MulAut ↥A) = ggConjAut A (hn i) := by
    intro i
    rw [MulEquiv.trans_apply, ggE6Row_coxeterGroupEquiv_simple]
    exact hmark i
  refine ⟨hn, ?_, ec, hc⟩
  let ρ : CoxeterMatrix.E₆.Group →* MulAut ↥A :=
    (ggAutomizer (MulAut.conj : L →* MulAut L).range A).subtype.comp ec.toMonoidHom
  have hrho : ρ.range = ggAutomizer (MulAut.conj : L →* MulAut L).range A := by
    ext x
    constructor
    · rintro ⟨w, rfl⟩; exact (ec w).2
    · intro hx
      obtain ⟨w, hw⟩ := ec.surjective ⟨x, hx⟩
      exact ⟨w, congrArg Subtype.val hw⟩
  rw [← hrho, MonoidHom.range_eq_map,
    ← CoxeterMatrix.E₆.toCoxeterSystem.subgroup_closure_range_simple, MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨w, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, (hc i).symm⟩
  · rintro ⟨i, rfl⟩
    exact ⟨CoxeterMatrix.E₆.simple i, ⟨i, rfl⟩, hc i⟩

theorem scalar_inner_torus_le {f m : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hφs : Function.Surjective φ)
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m)) :
    ((φ.comp (langTorusHom K θ hθ l hl)).range).map (MulAut.conj : L →* MulAut L) ≤ δ.range := by
  rw [← scalar_iSup_coroot_range θ hθ l hl φ e, Subgroup.map_iSup]
  refine iSup_le fun i => ?_
  rintro _ ⟨_, ⟨s, rfl⟩, rfl⟩
  exact ⟨fun j => e.symm s ^ Tag.E6.cartan i j,
    scalar_descent_conj θ hθ l hl φ δ hK hφs hδ i (e.symm s)⟩

theorem scalar_frame_le_torus {p : ℕ} [NeZero p]
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) :
    (φ.comp (langPFrame K θ hθ l hl ζ hζ)).range ≤
      (φ.comp (langTorusHom K θ hθ l hl)).range := by
  rintro _ ⟨a, rfl⟩
  refine ⟨fun i => zmodPowHom ζ hζ (Multiplicative.ofAdd (Multiplicative.toAdd a i)), ?_⟩
  rw [MonoidHom.comp_apply, MonoidHom.comp_apply, langPFrame_apply]

theorem scalarRoot_nontrivial_on_frame {f m p : ℕ} (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f)) (hp : p.Prime) (hp3 : p ≠ 3) [NeZero p]
    (hφs : Function.Surjective φ)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom))
    (hδi : Function.Injective δ)
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (A : Subgroup (MulAut L))
    (hA : ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range).map (MulAut.conj : L →* MulAut L) = A) :
    ∀ i, ∃ a ∈ A, scalarRoot θ δ e i a ≠ 1 := by
  intro i
  obtain ⟨j, hj⟩ := neighbour_E6 i
  let x := φ (langCoroot K θ hθ l hl j ζ)
  have hxp : x ^ p = 1 := by
    change (φ (langCoroot K θ hθ l hl j ζ)) ^ p = 1
    rw [← map_pow, ← map_pow, hζ, map_one, map_one]
  have hxt : x ∈ (φ.comp (langTorusHom K θ hθ l hl)).range := by
    refine ⟨Pi.mulSingle j ζ, ?_⟩
    rw [MonoidHom.comp_apply, langTorusHom_mulSingle]
  have hx : x ∈ (φ.comp (langPFrame K θ hθ l hl ζ hζ)).range :=
    (scalar_frame_torsion θ hθ l hl φ hK hθq hp hp3 hφc ζ hζ hζo x).mpr ⟨hxp, hxt⟩
  have hxa : MulAut.conj x ∈ A := hA ▸ Subgroup.mem_map_of_mem _ hx
  refine ⟨MulAut.conj x, hxa, ?_⟩
  change scalarRoot θ δ e i (MulAut.conj (φ (langCoroot K θ hθ l hl j ζ))) ≠ 1
  rw [← scalar_descent_conj θ hθ l hl φ δ hK hφs hδ j ζ,
    scalarRoot_apply θ δ e hδi, hj]
  intro he
  have hζ1 : ζ ^ (-1 : ℤ) = 1 := e.injective (he.trans (map_one e).symm)
  have hz : ζ = 1 := inv_eq_one.mp (by simpa only [zpow_neg_one] using hζ1)
  have hzu : (ζ : Kˣ) = 1 := by simpa using congrArg Subtype.val hz
  rw [hzu, orderOf_one] at hζo
  exact hp.ne_one hζo.symm

theorem scalar_torData_aligned {f m p : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (hθq : ∀ c, θ.toRingHom c = c ^ (2 ^ f))
    (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3) [NeZero p]
    (ψ : L →* graphFixedRootGroup TwistTag.E6 K θ.toRingHom)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L)
    (hφ : ∀ x, ψ (φ x) = CFSG.SeitzReduction.F4Pilot.twistedIsogenyC hf hK θ.toRingHom hθq x)
    (hφs : Function.Surjective φ)
    (hφc : φ.ker ≤ Subgroup.center (fixedGroup K θ.toRingHom))
    (hδ : ∀ b x, δ b (φ x) = φ (fixedDiagonalHom K (f * 2)
      (by rw [hK, ← pow_mul]) θ hθ l hl b x))
    (ζ : CFSG.LieType.Steinberg.normOne θ) (hζ : ζ ^ p = 1) (hζo : orderOf (ζ : Kˣ) = p)
    (e : CFSG.LieType.Steinberg.normOne θ ≃* Multiplicative (ZMod m))
    (A : Subgroup (MulAut L))
    (hA : ((φ.comp (langPFrame K θ hθ l hl ζ hζ)).range).map (MulAut.conj : L →* MulAut L) = A) :
    GGTorusTorData m 6 CartanMatrix.E₆ CoxeterMatrix.E₆ L A := by
  have hδi := scalar_descent_injective θ hθ l hl φ δ hK hθq hf ψ hφ hδ
  have hAD : A ≤ δ.range := by
    rw [← hA]
    exact (Subgroup.map_mono (scalar_frame_le_torus θ hθ l hl φ ζ hζ)).trans
      (scalar_inner_torus_le θ hθ l hl φ δ hK hφs hδ e)
  have hroot := scalarRoot_nontrivial_on_frame θ hθ l hl φ δ hK hθq hp hp3
    hφs hφc hδi hδ ζ hζ hζo e A hA
  obtain ⟨hn, hfour⟩ := scalar_holdsFour θ hθ l hl φ δ hf hK hθq hp hp2 hp3
    ψ hψ hker hφ hφs hφc ζ hζ hζo e A hA
  exact ⟨scalarWitness θ hθ l hl φ δ e A hn, ggTDHolds_of_parts
    (scalar_holdsOne θ hθ l hl φ δ hf hK hθq ψ hφ hφs hδi hδ e A hAD hn)
    (scalar_holdsTwo θ hθ l hl φ δ hK hδi hδ e A hroot hn)
    (scalar_holdsThree θ hθ l hl φ δ hf hK hθq hp hp2 hp3 hφs hφc hδ e ζ hζ hζo A hAD hA hn)
    hfour⟩

end CFSG.StandardType.TBE6IndTwist
