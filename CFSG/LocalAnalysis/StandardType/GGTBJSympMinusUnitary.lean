module

public import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
public import CFSG.LocalAnalysis.StandardType.GGTorCNormalizer
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBShape
public import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameBridge
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryVec
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryCard
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryElt
public import CFSG.LocalAnalysis.StandardType.GGTBJSympMinusUnitaryBlock

public section

namespace CFSG.StandardType.SympMinus

open CFSG.Open CFSG.Assembly CFSG.StandardType.SpJoin CFSG.StandardType.TorC
open CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Multiplicative
open CFSG.StandardType.SpCoord (diagAut permAut)
open Matrix (mulVec)
open scoped Matrix

section Aux

variable {K : Type} [Field K] {p m : ℕ}

theorem commute_spPlaneTorus_of_eq_pow
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    {f₀ : Fin m → Multiplicative (ZMod p)}
    {S : Finset (Fin m)} {n : StatedSp m K}
    (hn : SmuOffFix S ((n : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K))
    (hnc : n * spPlaneTorus m ζ f₀ = spPlaneTorus m ζ f₀ * n) {N : ℕ}
    {f : Fin m → Multiplicative (ZMod p)} (hf : ∀ i ∈ S, f i = f₀ i ^ N) :
    n * spPlaneTorus m ζ f = spPlaneTorus m ζ f * n := by
  set h : Fin m → Multiplicative (ZMod p) := f * (f₀ ^ N)⁻¹ with hh
  have hh1 : ∀ i ∈ S, h i = 1 := by
    intro i hi
    simp [hh, hf i hi]
  have hf' : f = h * f₀ ^ N := by rw [hh]; simp
  have hcomm_h : n * spPlaneTorus m ζ h = spPlaneTorus m ζ h * n := by
    apply Subtype.ext
    apply Units.ext
    change (((n : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        (((spPlaneTorus m ζ h : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) =
      (((spPlaneTorus m ζ h : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
          Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
        ((n : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
    rw [coe_spPlaneTorus]
    exact hn.commute_planeMat (CFSG.Open.StatedAPI.mem_statedSp_iff.mp n.2)
      (fun x hx => by simp [hh1 x hx])
  have c1 : Commute n (spPlaneTorus m ζ h) := hcomm_h
  have c2 : Commute n (spPlaneTorus m ζ f₀) := hnc
  have c3 := c1.mul_right (c2.pow_right N)
  rw [hf', map_mul, map_pow]
  exact c3

theorem toAdd_eq_of_mem {c : Multiplicative (ZMod p)} {f₀ : Fin m → Multiplicative (ZMod p)}
    {S : Finset (Fin m)} (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹) {s : Fin m → ZMod p}
    (hsdef : ∀ i, s i = if f₀ i = c then (1 : ZMod p) else -1) {i : Fin m} (hi : i ∈ S) :
    toAdd (f₀ i) = toAdd c * s i := by
  rw [hsdef i]
  by_cases h : f₀ i = c
  · simp [h]
  · have h' : f₀ i = c⁻¹ := ((hS i).mp hi).resolve_left h
    rw [if_neg h, h']
    simp [toAdd_inv]

theorem smu_exists_pow_eq [Fact p.Prime] {c : Multiplicative (ZMod p)} (hc : c ≠ 1)
    {f₀ : Fin m → Multiplicative (ZMod p)} {S : Finset (Fin m)}
    (hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹) {s : Fin m → ZMod p}
    (hsdef : ∀ i, s i = if f₀ i = c then (1 : ZMod p) else -1) (t : ZMod p) :
    ∃ N : ℕ, ∀ i ∈ S, ofAdd (s i * t) = f₀ i ^ N := by
  have ha : toAdd c ≠ 0 := fun h => hc (toAdd.injective (by simpa using h))
  refine ⟨(t * (toAdd c)⁻¹).val, fun i hi => ?_⟩
  apply toAdd.injective
  rw [toAdd_ofAdd, toAdd_pow, nsmul_eq_mul, ZMod.natCast_zmod_val, toAdd_eq_of_mem hS hsdef hi]
  field_simp

end Aux


theorem sympMinus_block_unitary {K : Type} [Field K] [Finite K] [CharP K 2]
    (hq : 4 ≤ Nat.card K ∨ Nat.card K = 2) {p m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K + 1)
    {ζ : Multiplicative (ZMod p) →* Matrix.SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) (hζW : ∀ a, sl2W * ζ a * sl2W⁻¹ = ζ a⁻¹)
    (f₀ : Fin m → Multiplicative (ZMod p)) {c : Multiplicative (ZMod p)} (hc : c ≠ 1)
    {J₀ : Subgroup (StatedSp m K)}
    (hJ : CFSG.Assembly.IsComponentOf J₀ (Subgroup.centralizer ({spPlaneTorus m ζ f₀} : Set (StatedSp m K))))
    (hsupp : ∀ j ∈ J₀, ∀ x : Fin m, f₀ x ≠ c → f₀ x ≠ c⁻¹ → ∀ y : Fin m,
      blk (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)
        y x = if y = x then 1 else 0) :
    2 ≤ (Finset.univ.filter fun i : Fin m => f₀ i = c ∨ f₀ i = c⁻¹).card ∧
      ∀ hs : (∀ i : Fin m, (if f₀ i = c then (1 : ZMod p) else -1) *
          (if f₀ i = c then (1 : ZMod p) else -1) = 1),
        FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ =
          TypeBDatum.twistedPermAut m p
            (Finset.univ.filter fun i : Fin m => f₀ i = c ∨ f₀ i = c⁻¹)
            (fun i => if f₀ i = c then (1 : ZMod p) else -1) hs ∧
        ∀ f : Fin m → Multiplicative (ZMod p),
          (∀ τ ∈ FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀, τ f = f) →
            ∀ j ∈ J₀, spPlaneTorus m ζ f * j = j * spPlaneTorus m ζ f := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  set S : Finset (Fin m) := Finset.univ.filter fun i : Fin m => f₀ i = c ∨ f₀ i = c⁻¹ with hSdef
  have hS : ∀ i, i ∈ S ↔ f₀ i = c ∨ f₀ i = c⁻¹ := fun i => by simp [hSdef]
  have hsupp' : ∀ j ∈ J₀, SmuOffFix S
      (((j : StatedSp m K) : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
    intro j hj x hx y
    have hx' : f₀ x ≠ c ∧ f₀ x ≠ c⁻¹ := by
      rw [hS] at hx
      exact not_or.mp hx
    exact hsupp j hj x hx'.1 hx'.2 y
  have hcard : 2 ≤ S.card := card_ge_two_of_component hp hp2 hζ f₀ hc hJ hS hsupp'
  refine ⟨hcard, fun hs => ?_⟩
  set s : Fin m → ZMod p := fun i => if f₀ i = c then (1 : ZMod p) else -1 with hsdef
  have hsdef' : ∀ i, s i = if f₀ i = c then (1 : ZMod p) else -1 := fun i => rfl
  have hs' : ∀ i, s i * s i = 1 := hs
  have hsgn : ∀ i, s i = 1 ∨ s i = -1 := fun i => by
    by_cases h : f₀ i = c <;> simp [hsdef', h]
  have hΘinj := spPlaneTorus_injective hζ m
  have hf₀s : ∀ i ∈ S, toAdd (f₀ i) = toAdd c * s i := fun i hi => toAdd_eq_of_mem hS hsdef' hi
  have hcg : ∀ n ∈ J₀, n * spPlaneTorus m ζ f₀ = spPlaneTorus m ζ f₀ * n := fun n hn =>
    Subgroup.mem_centralizer_singleton_iff.mp (hJ.1 hn)
  have hcomm_pow : ∀ (N : ℕ) (f : Fin m → Multiplicative (ZMod p)), (∀ i ∈ S, f i = f₀ i ^ N) →
      ∀ n ∈ J₀, n * spPlaneTorus m ζ f = spPlaneTorus m ζ f * n :=
    fun N f hf n hn => commute_spPlaneTorus_of_eq_pow (hsupp' n hn) (hcg n hn) hf
  have hσ : ∀ a ∈ S, ∀ b ∈ S, ((diagAut s hs' * permAut (Equiv.swap a b) * (diagAut s hs')⁻¹ :
      MulAut (Fin m → Multiplicative (ZMod p))) f₀) = f₀ := by
    intro a ha b hb
    funext i
    rw [twisted_swap_apply hs' a b f₀ i]
    by_cases hia : i = a
    · subst hia
      rw [Equiv.swap_apply_left, hf₀s b hb]
      have h1 : s i * s b * (toAdd c * s b) = toAdd (f₀ i) := by
        rw [hf₀s i ha]
        linear_combination (toAdd c * s i) * hs' b
      rw [h1, ofAdd_toAdd]
    · by_cases hib : i = b
      · subst hib
        rw [Equiv.swap_apply_right, hf₀s a ha]
        have h1 : s i * s a * (toAdd c * s a) = toAdd (f₀ i) := by
          rw [hf₀s i hb]
          linear_combination (toAdd c * s i) * hs' a
        rw [h1, ofAdd_toAdd]
      · rw [Equiv.swap_apply_of_ne_of_ne hia hib]
        have h1 : s i * s i * toAdd (f₀ i) = toAdd (f₀ i) := by rw [hs' i, one_mul]
        rw [h1, ofAdd_toAdd]
  have hgen : ∀ a ∈ S, ∀ b ∈ S, a ≠ b → ∃ n ∈ J₀, ∀ f,
      n * spPlaneTorus m ζ f * n⁻¹ = spPlaneTorus m ζ
        ((diagAut s hs' * permAut (Equiv.swap a b) * (diagAut s hs')⁻¹ :
          MulAut (Fin m → Multiplicative (ZMod p))) f) := by
    intro a ha b hb hab
    have hmemJ : ∀ n : StatedSp m K, n * n = 1 →
        (∀ f, n * spPlaneTorus m ζ f * n⁻¹ = spPlaneTorus m ζ
          ((diagAut s hs' * permAut (Equiv.swap a b) * (diagAut s hs')⁻¹ :
            MulAut (Fin m → Multiplicative (ZMod p))) f)) →
        (∀ v : Fin m ⊕ Fin m → K, (∀ r, WitSpNs.plane r = a ∨ WitSpNs.plane r = b → v r = 0) →
          ((n : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *ᵥ v = v) →
        n ∈ J₀ := by
      intro n hn2 hconj hfixv
      have hnc : n * spPlaneTorus m ζ f₀ = spPlaneTorus m ζ f₀ * n := by
        have h1 := hconj f₀
        rw [hσ a ha b hb] at h1
        exact mul_inv_eq_iff_eq_mul.mp h1
      refine mem_component_of_involution hq hp hp2 hpq hζ f₀ hc hJ hS hsupp' hcard hn2 hnc
        (fun v hv => hfixv v (fun r hr => hv r ?_))
      rcases hr with h | h
      · rw [h]; exact ha
      · rw [h]; exact hb
    have hsab : s a * s b = 1 ∨ s a * s b = -1 := by
      rcases hsgn a with h | h <;> rcases hsgn b with h' | h' <;> simp [h, h']
    rcases hsab with h1 | h1
    · exact ⟨smuPlaneSwap a b, hmemJ _ (smuPlaneSwap_mul_self a b)
        (fun f => smuPlaneSwap_conj_twisted hs' h1 f) (fun v hv => smuPlaneSwap_mulVec a b hv),
        fun f => smuPlaneSwap_conj_twisted hs' h1 f⟩
    · exact ⟨smuPlaneSwapW a b, hmemJ _ (smuPlaneSwapW_mul_self hab)
        (fun f => smuPlaneSwapW_conj_twisted hζW hs' hab h1 f)
        (fun v hv => smuPlaneSwapW_mulVec a b hv),
        fun f => smuPlaneSwapW_conj_twisted hζW hs' hab h1 f⟩
  have hle : ∀ τ ∈ FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀, τ ∈ TypeBDatum.signedAut m p := by
    rintro τ ⟨n, hn, hnτ⟩
    obtain ⟨π, ε, hε, hπ⟩ := exists_signedPerm_of_normalizes hp hp2 hζ n
      (fun f => ⟨τ f, hnτ f⟩)
    exact TypeBDatum.mem_signedAut_of_isSignedPerm ⟨π, ε, hε, fun f i => hπ f (τ f) (hnτ f) i⟩
  obtain ⟨N₁, hN₁⟩ := smu_exists_pow_eq hc hS hsdef' (1 : ZMod p)
  have hfix : ∀ x ∈ J₀, ∀ i ∉ S,
      x * spPlaneTorus m ζ (Pi.mulSingle i (ofAdd (1 : ZMod p))) * x⁻¹ =
        spPlaneTorus m ζ (Pi.mulSingle i (ofAdd 1)) := by
    intro x hx i hi
    refine mul_inv_eq_iff_eq_mul.mpr (hcomm_pow 0 _ (fun i' hi' => ?_) x hx)
    have hne : i' ≠ i := fun h => hi (h ▸ hi')
    simp [Pi.mulSingle_eq_of_ne hne]
  have hvec : ∀ x ∈ J₀,
      x * spPlaneTorus m ζ (fun j => if j ∈ S then ofAdd (s j) else 1) * x⁻¹ =
        spPlaneTorus m ζ (fun j => if j ∈ S then ofAdd (s j) else 1) := by
    intro x hx
    refine mul_inv_eq_iff_eq_mul.mpr (hcomm_pow N₁ _ (fun i' hi' => ?_) x hx)
    have := hN₁ i' hi'
    simp only [hi', if_true]
    rw [← this, mul_one]
  have hEq : FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ =
      TypeBDatum.twistedPermAut m p S s hs :=
    TypeBDatum.sectionFrameAut_eq_twistedPermAut hp hΘinj S s hs hsgn (fun τ hτ => hle τ hτ)
      hfix hvec (fun a ha b hb hab => hgen a ha b hb hab)
  refine ⟨hEq, fun f hf j hj => ?_⟩
  obtain ⟨i₀, hi₀⟩ := Finset.card_pos.mp (by omega : 0 < S.card)
  have hftoAdd : ∀ i ∈ S, toAdd (f i) = s i * (s i₀ * toAdd (f i₀)) := by
    intro i hi
    by_cases hii : i = i₀
    · subst hii
      rw [← mul_assoc, hs' i, one_mul]
    · have hmem : ((diagAut s hs' * permAut (Equiv.swap i i₀) * (diagAut s hs')⁻¹ :
          MulAut (Fin m → Multiplicative (ZMod p)))) ∈
          FrameBs.sectionFrameAut (spPlaneTorus m ζ) J₀ := hgen i hi i₀ hi₀ hii
      have h1 := congrFun (hf _ hmem) i
      rw [twisted_swap_apply hs' i i₀ f i, Equiv.swap_apply_left] at h1
      have h2 := congrArg toAdd h1
      rw [toAdd_ofAdd] at h2
      rw [← h2]
      ring
  obtain ⟨N, hN⟩ := smu_exists_pow_eq hc hS hsdef' (s i₀ * toAdd (f i₀))
  have hfN : ∀ i ∈ S, f i = f₀ i ^ N := by
    intro i hi
    rw [← hN i hi, ← hftoAdd i hi, ofAdd_toAdd]
  exact (hcomm_pow N f hfN j hj).symm

end CFSG.StandardType.SympMinus

end
