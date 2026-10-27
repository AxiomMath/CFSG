module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerUnitaryHypTorus
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenDefs
public import CFSG.Assembly.LargeEvenDefs
public import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenGen
public import CFSG.RankThree.PartTwo.CTU6.Long
import all CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenLine
import all CFSG.LieType.SeitzGeneration.UnitarySplit
import CFSG.LocalAnalysis.StandardType.GGSuSplitRootGenWeyl
import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
import CFSG.LocalAnalysis.SeitzReduction.F4PilotBLift
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.RankThree.PartOne.CTP.SpNode
public import CFSG.RankThree.PartOne.CTP.SpPos

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  Matrix Multiplicative
open scoped commutatorElement MatrixGroups

variable {G : Type} [Group G] {p a : ℕ} {F : Type} [Field F] {h : UnitaryFieldData 2 a F}

section Torus

variable {s : ℕ} {ζ : F} {τ : Multiplicative (Fin s → ZMod p) →* hypSU h s 0}

private theorem hypEntries_eq_splitEntries (t : Fin s → ZMod p) :
    hypEntries ζ t = SuSplitRootGen.splitEntries (ε := 0) ζ t := by
  funext x
  rcases x with i | k | i
  · rfl
  · exact k.elim0
  · rfl

private theorem isSplitTorus_of
    (hτ : ∀ t, (((τ (ofAdd t) : hypSU h s 0) : GL (HypIndex s 0) F) :
      Matrix (HypIndex s 0) (HypIndex s 0) F) = diagonal (hypEntries ζ t)) :
    SuSplitRootGen.IsSplitTorus h ζ τ := fun t => by rw [hτ t, hypEntries_eq_splitEntries]

private theorem eq_of_tau_eq (hp : p.Prime) (hζ : IsPrimitiveRoot ζ p)
    (hτ : ∀ t, (((τ (ofAdd t) : hypSU h s 0) : GL (HypIndex s 0) F) :
      Matrix (HypIndex s 0) (HypIndex s 0) F) = diagonal (hypEntries ζ t))
    {u u' : Fin s → ZMod p} (he : τ (ofAdd u) = τ (ofAdd u')) : u = u' := by
  have : NeZero p := ⟨hp.ne_zero⟩
  funext i
  have hmat : (((τ (ofAdd u) : hypSU h s 0) : GL (HypIndex s 0) F) :
      Matrix (HypIndex s 0) (HypIndex s 0) F) =
      (((τ (ofAdd u') : hypSU h s 0) : GL (HypIndex s 0) F) :
        Matrix (HypIndex s 0) (HypIndex s 0) F) := by rw [he]
  rw [hτ, hτ] at hmat
  have hentry := congrFun (congrFun hmat (.inl i)) (.inl i)
  simp only [diagonal_apply_eq, hypEntries] at hentry
  exact ZMod.val_injective p (hζ.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hentry)

private theorem eq_one_of_commute_lineWeyl (hp : p.Prime) (hp2 : p ≠ 2)
    (hζ : IsPrimitiveRoot ζ p)
    (hτ : ∀ t, (((τ (ofAdd t) : hypSU h s 0) : GL (HypIndex s 0) F) :
      Matrix (HypIndex s 0) (HypIndex s 0) F) = diagonal (hypEntries ζ t))
    {w : Multiplicative (Fin s → ZMod p)}
    (hc : ∀ i, Commute (SuSplitRootGen.lineWeyl h 0 i) (τ w)) : w = 1 := by
  have h0 : toAdd w = 0 := by
    funext i
    have hconj := SuSplitRootGen.lineWeyl_conj h hp hζ.pow_eq_one (isSplitTorus_of hτ) i
      (toAdd w)
    rw [ofAdd_toAdd, (hc i).eq, mul_inv_cancel_right] at hconj
    have he := (eq_of_tau_eq hp hζ hτ (u := toAdd w) hconj).symm
    have : Fact p.Prime := ⟨hp⟩
    exact (SlNsRootGen.negMap_eq_self_iff hp2).mp he
  exact toAdd_eq_zero.mp h0

private theorem exponent_eq_of_conj (hp : p.Prime) (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    (hτ : ∀ t, (((τ (ofAdd t) : hypSU h s 0) : GL (HypIndex s 0) F) :
      Matrix (HypIndex s 0) (HypIndex s 0) F) = diagonal (hypEntries ζ t))
    {κ : hypSU h s 0 →* G} (hκ : Function.Injective κ) {u u' : Fin s → ZMod p}
    (he : ∀ x, κ (τ (ofAdd u) * x * (τ (ofAdd u))⁻¹) =
      κ (τ (ofAdd u') * x * (τ (ofAdd u'))⁻¹)) : u = u' := by
  have hw : (ofAdd u')⁻¹ * ofAdd u = 1 := by
    refine eq_one_of_commute_lineWeyl hp hp2 hζ hτ fun i => ?_
    have h1 := hκ (he (SuSplitRootGen.lineWeyl h 0 i))
    show SuSplitRootGen.lineWeyl h 0 i * τ ((ofAdd u')⁻¹ * ofAdd u) =
      τ ((ofAdd u')⁻¹ * ofAdd u) * SuSplitRootGen.lineWeyl h 0 i
    rw [map_mul, map_inv]
    calc SuSplitRootGen.lineWeyl h 0 i * ((τ (ofAdd u'))⁻¹ * τ (ofAdd u))
        = (τ (ofAdd u'))⁻¹ * (τ (ofAdd u') * SuSplitRootGen.lineWeyl h 0 i *
            (τ (ofAdd u'))⁻¹) * τ (ofAdd u) := by group
      _ = (τ (ofAdd u'))⁻¹ * (τ (ofAdd u) * SuSplitRootGen.lineWeyl h 0 i *
            (τ (ofAdd u))⁻¹) * τ (ofAdd u) := by rw [h1]
      _ = (τ (ofAdd u'))⁻¹ * τ (ofAdd u) * SuSplitRootGen.lineWeyl h 0 i := by group
  exact ofAdd.injective (inv_mul_eq_one.mp hw).symm

private theorem exists_idx_of_not_mem {m : Fin s} {x : HypIndex s 0}
    (hx : x ∉ SuSplitRootGen.lineCoords m) :
    ∃ k, k ≠ m ∧ (x = .inl k ∨ x = .inr (.inr k)) := by
  rcases x with k | z | k
  · exact ⟨k, fun hk => hx (by simp [SuSplitRootGen.lineCoords, hk]), Or.inl rfl⟩
  · exact z.elim0
  · exact ⟨k, fun hk => hx (by simp [SuSplitRootGen.lineCoords, hk]), Or.inr rfl⟩

private theorem hypEntries_single_ne (hp : p.Prime) (hp2 : p ≠ 2) (hζ : IsPrimitiveRoot ζ p)
    {c : ZMod p}
    (hc : c ≠ 0) {k : Fin s} {x x' : HypIndex s 0} (hx : x = .inl k ∨ x = .inr (.inr k))
    (hxx' : x ≠ x') : hypEntries ζ (Pi.single k c) x ≠ hypEntries ζ (Pi.single k c) x' := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hcv : ¬ p ∣ c.val := fun hd =>
    hc ((ZMod.val_eq_zero c).mp (Nat.eq_zero_of_dvd_of_lt hd (ZMod.val_lt c)))
  have hz1 : ζ ^ c.val ≠ 1 := fun he => hcv ((hζ.pow_eq_one_iff_dvd _).mp he)
  have hz0 : ζ ^ c.val ≠ 0 := pow_ne_zero _ (hζ.ne_zero hp.ne_zero)
  have hz2 : ζ ^ c.val ≠ (ζ ^ c.val)⁻¹ := by
    intro he
    have h2 : ζ ^ (c.val + c.val) = 1 := by
      rw [pow_add]
      calc ζ ^ c.val * ζ ^ c.val = ζ ^ c.val * (ζ ^ c.val)⁻¹ := congrArg (ζ ^ c.val * ·) he
        _ = 1 := mul_inv_cancel₀ hz0
    have hd : p ∣ 2 * c.val := by rw [two_mul]; exact (hζ.pow_eq_one_iff_dvd _).mp h2
    rcases (Nat.Prime.dvd_mul hp).mp hd with h2' | h2'
    · exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2')
    · exact hcv h2'
  have hz3 : (ζ ^ c.val)⁻¹ ≠ 1 := inv_ne_one.mpr hz1
  rcases hx with rfl | rfl <;> rcases x' with j | z | j
  · have hjk : j ≠ k := fun hj => hxx' (by rw [hj])
    simpa [hypEntries, Pi.single_apply, hjk] using hz1
  · exact z.elim0
  · by_cases hjk : j = k
    · subst hjk
      simpa [hypEntries] using hz2
    · simpa [hypEntries, Pi.single_apply, hjk] using hz1
  · by_cases hjk : j = k
    · subst hjk
      simpa [hypEntries] using hz2.symm
    · simpa [hypEntries, Pi.single_apply, hjk] using hz3
  · exact z.elim0
  · have hjk : j ≠ k := fun hj => hxx' (by rw [hj])
    simpa [hypEntries, Pi.single_apply, hjk] using hz3

private theorem tau_single_mem_lineBlock
    (hτ : ∀ t, (((τ (ofAdd t) : hypSU h s 0) : GL (HypIndex s 0) F) :
      Matrix (HypIndex s 0) (HypIndex s 0) F) = diagonal (hypEntries ζ t))
    (k : Fin s) (c : ZMod p) : τ (ofAdd (Pi.single k c)) ∈ SuSplitRootGen.lineBlock h k := by
  rw [SuSplitRootGen.lineBlock, SuSplitRootGen.mem_hypBlock]
  intro x x' hxx'
  rw [hτ]
  by_cases he : x = x'
  · subst he
    rw [diagonal_apply_eq, one_apply_eq]
    obtain ⟨j, hjk, hj⟩ := exists_idx_of_not_mem (hxx'.elim id id)
    rcases hj with rfl | rfl <;> simp [hypEntries, hjk]
  · rw [diagonal_apply_ne _ he, one_apply_ne he]

end Torus

section Sep

variable {ι : Type*} [Fintype ι]

private def SepOn (T : Set ι) (M : Matrix ι ι F) : Prop :=
  ∀ x x', x ≠ x' → (x ∉ T ∨ x' ∉ T) → M x x' = 0

private theorem SepOn.mul {T : Set ι} {M N : Matrix ι ι F} (hM : SepOn T M) (hN : SepOn T N) :
    SepOn T (M * N) ∧ ∀ x, x ∉ T → (M * N) x x = M x x * N x x := by
  have key : ∀ x x', x ∉ T → (M * N) x x' = M x x * N x x' := by
    intro x x' hx
    rw [mul_apply, Finset.sum_eq_single x]
    · intro z _ hz
      rw [hM x z (Ne.symm hz) (Or.inl hx), zero_mul]
    · intro hx'
      exact absurd (Finset.mem_univ x) hx'
  have key' : ∀ x x', x' ∉ T → (M * N) x x' = M x x' * N x' x' := by
    intro x x' hx'
    rw [mul_apply, Finset.sum_eq_single x']
    · intro z _ hz
      rw [hN z x' hz (Or.inr hx'), mul_zero]
    · intro hx
      exact absurd (Finset.mem_univ x') hx
  refine ⟨fun x x' hne hT => ?_, fun x hx => key x x hx⟩
  rcases hT with hx | hx'
  · rw [key x x' hx, hN x x' hne (Or.inl hx), mul_zero]
  · rw [key' x x' hx', hM x x' hne (Or.inr hx'), zero_mul]

end Sep

section Commutator

variable {s : ℕ}

private abbrev hmat (x : hypSU h s 0) : Matrix (HypIndex s 0) (HypIndex s 0) F :=
  ((x : GL (HypIndex s 0) F) : Matrix (HypIndex s 0) (HypIndex s 0) F)

private theorem commutator_mem_lineBlock {m : Fin s} {x y : hypSU h s 0}
    (hx : SepOn (SuSplitRootGen.lineCoords m) (hmat x))
    (hx' : SepOn (SuSplitRootGen.lineCoords m) (hmat x⁻¹))
    (hy : SepOn (SuSplitRootGen.lineCoords m) (hmat y))
    (hy' : SepOn (SuSplitRootGen.lineCoords m) (hmat y⁻¹)) :
    ⁅x, y⁆ ∈ SuSplitRootGen.lineBlock h m := by
  have hmul : ∀ u v : hypSU h s 0, hmat (u * v) = hmat u * hmat v := fun u v => by
    simp only [hmat, Subgroup.coe_mul, Units.val_mul]
  have hinv : ∀ u : hypSU h s 0, hmat u * hmat u⁻¹ = 1 := fun u => by
    rw [← hmul, mul_inv_cancel]
    simp only [hmat, Subgroup.coe_one, Units.val_one]
  obtain ⟨hxy, hxy_d⟩ := hx.mul hy
  obtain ⟨hxyx, hxyx_d⟩ := hxy.mul hx'
  obtain ⟨hc, hc_d⟩ := hxyx.mul hy'
  have hxx := (hx.mul hx').2
  have hyy := (hy.mul hy').2
  rw [SuSplitRootGen.lineBlock, SuSplitRootGen.mem_hypBlock]
  have hcm : (((⁅x, y⁆ : hypSU h s 0) : GL (HypIndex s 0) F) :
      Matrix (HypIndex s 0) (HypIndex s 0) F) = hmat x * hmat y * hmat x⁻¹ * hmat y⁻¹ := by
    rw [commutatorElement_def]
    simp only [hmat, Subgroup.coe_mul, Units.val_mul]
  rw [hcm]
  intro z z' hzz'
  by_cases he : z = z'
  · subst he
    have hz : z ∉ SuSplitRootGen.lineCoords m := hzz'.elim id id
    have h1 : hmat x z z * hmat x⁻¹ z z = 1 := by
      rw [← hxx z hz, hinv, one_apply_eq]
    have h2 : hmat y z z * hmat y⁻¹ z z = 1 := by
      rw [← hyy z hz, hinv, one_apply_eq]
    rw [hc_d z hz, hxyx_d z hz, hxy_d z hz, one_apply_eq]
    calc hmat x z z * hmat y z z * hmat x⁻¹ z z * hmat y⁻¹ z z
        = (hmat x z z * hmat x⁻¹ z z) * (hmat y z z * hmat y⁻¹ z z) := by ring
      _ = 1 := by rw [h1, h2, one_mul]
  · rw [hc z z' he hzz', one_apply_ne he]

end Commutator

private abbrev frameExp {n r : ℕ} {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) (π : Fin (r + 2) ≃ Fin n) (c : ZMod p)
    (b : ↥Bs) : Fin (r + 1) → ZMod p :=
  fun i => c * toAdd (eta b (π i.succ))

theorem ggSecFiveBPermSU_singletonComm_K [Finite G] {n r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : UnitaryFieldData 2 a F) (hpq : p ∣ 2 ^ a - 1) (hr : 1 ≤ r)
    {Bs K : Subgroup G} {y : G}
    (hBc : ∀ x ∈ Bs, ∀ z ∈ Bs, x * z = z * x)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {κ : hypSU h (r + 1) 0 →* G} (hκ : Function.Injective κ) (hκK : κ.range = K)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin (r + 1) → ZMod p) →* hypSU h (r + 1) 0}
    (hτ : ∀ t, (((τ (Multiplicative.ofAdd t) : hypSU h (r + 1) 0) : GL (HypIndex (r + 1) 0) F) :
      Matrix (HypIndex (r + 1) 0) (HypIndex (r + 1) 0) F) = Matrix.diagonal (hypEntries ζ t))
    {c : ZMod p} (hc : c ≠ 0)
    (hact : ∀ (b : ↥Bs) (s : hypSU h (r + 1) 0), (b : G) * κ s * (b : G)⁻¹ =
      κ (τ (Multiplicative.ofAdd fun i => c * Multiplicative.toAdd (eta b (π i.succ))) * s *
        (τ (Multiplicative.ofAdd fun i => c * Multiplicative.toAdd (eta b (π i.succ))))⁻¹))
    (m : Fin (r + 1)) :
    ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G), Bs⁆ =
      (SuSplitRootGen.lineBlock h m).map κ := by
  have hτs := isSplitTorus_of hτ
  have hact' : ∀ (b : ↥Bs) (s : hypSU h (r + 1) 0), (b : G) * κ s * (b : G)⁻¹ =
      κ (τ (ofAdd (frameExp eta π c b)) * s * (τ (ofAdd (frameExp eta π c b)))⁻¹) := hact
  have hex : ∀ (b : ↥Bs) {u : Fin (r + 1) → ZMod p},
      (∀ x, (b : G) * κ x * (b : G)⁻¹ = κ (τ (ofAdd u) * x * (τ (ofAdd u))⁻¹)) →
        frameExp eta π c b = u :=
    fun b u hb => exponent_eq_of_conj hp hp2 hζ hτ hκ fun x => (hact' b x).symm.trans (hb x)
  have hcoord : ∀ (b : ↥Bs) (i : Fin (r + 1)), frameExp eta π c b i = 0 →
      eta b (π i.succ) = 1 := by
    intro b i hb
    have : Fact p.Prime := ⟨hp⟩
    exact toAdd_eq_zero.mp ((mul_eq_zero.mp hb).resolve_left hc)
  have htorusB : ∀ u : Fin (r + 1) → ZMod p, κ (τ (ofAdd u)) ∈ Bs := by
    intro u
    refine hBs _ (Subgroup.mem_centralizer_iff.mpr fun b hb => ?_) ?_
    · have h1 := hact' ⟨b, hb⟩ (τ (ofAdd u))
      have hcm : Commute (τ (ofAdd (frameExp eta π c ⟨b, hb⟩))) (τ (ofAdd u)) :=
        (Commute.all _ _).map τ
      rw [hcm.eq, mul_inv_cancel_right] at h1
      calc b * κ (τ (ofAdd u)) = b * κ (τ (ofAdd u)) * b⁻¹ * b := by group
        _ = κ (τ (ofAdd u)) * b := by rw [show b * κ (τ (ofAdd u)) * b⁻¹ = κ (τ (ofAdd u)) from h1]
    · have hpu : (p • u : Fin (r + 1) → ZMod p) = 0 := by
        funext i
        simp
      rw [← map_pow, ← map_pow, ← ofAdd_nsmul, hpu, ofAdd_zero, map_one, map_one]
  have hexT : ∀ u : Fin (r + 1) → ZMod p, frameExp eta π c ⟨κ (τ (ofAdd u)), htorusB u⟩ = u := by
    intro u
    refine hex _ fun x => ?_
    show κ (τ (ofAdd u)) * κ x * (κ (τ (ofAdd u)))⁻¹ = κ (τ (ofAdd u) * x * (τ (ofAdd u))⁻¹)
    rw [map_mul, map_mul, map_inv]
  have hyK : ∀ x, y * κ x * y⁻¹ = κ x := by
    intro x
    have hx : κ x ∈ K := by rw [← hκK]; exact ⟨x, rfl⟩
    have hyx : y * κ x = κ x * y :=
      Subgroup.mem_centralizer_iff.mp (hK.1 hx) y (Set.mem_singleton y)
    rw [hyx, mul_inv_cancel_right]
  have hyH : y ∈ ggBsCoordZero Bs eta (π m.succ) := by
    have h0 : frameExp eta π c ⟨y, hyB⟩ = 0 := hex ⟨y, hyB⟩ fun x => by
      show y * κ x * y⁻¹ = _
      rw [hyK x, ofAdd_zero, map_one, one_mul, inv_one, mul_one]
    exact (coe_mem_ggBsCoordZero (b := ⟨y, hyB⟩)).mpr
      (hcoord ⟨y, hyB⟩ m (by rw [h0]; rfl))
  have htorusH : ∀ d : Fin (r + 1), d ≠ m →
      κ (τ (ofAdd (Pi.single d c))) ∈ ggBsCoordZero Bs eta (π m.succ) := by
    intro d hdm
    refine (coe_mem_ggBsCoordZero (b := ⟨_, htorusB _⟩)).mpr (hcoord _ m ?_)
    rw [hexT]
    exact Pi.single_eq_of_ne (Ne.symm hdm) _
  have hnc : ∀ d : Fin (r + 1), ¬ Commute (SuSplitRootGen.lineWeyl h 0 d)
      (τ (ofAdd (Pi.single d c))) := by
    intro d hcomm
    have hconj := SuSplitRootGen.lineWeyl_conj h hp hζ.pow_eq_one hτs d (Pi.single d c)
    rw [hcomm.eq, mul_inv_cancel_right] at hconj
    have he' := (eq_of_tau_eq hp hζ hτ hconj).symm
    have he : (Pi.single d c : Fin (r + 1) → ZMod p) d = 0 := by
      have : Fact p.Prime := ⟨hp⟩
      exact (SlNsRootGen.negMap_eq_self_iff hp2).mp he'
    rw [Pi.single_eq_same] at he
    exact hc he
  have hcomp := fun d : Fin (r + 1) => SuSplitRootGen.isComponentOf_lineBlock h hp hp2 hpq hζ
    hτs (by norm_num) d
  have hRq : ∀ d : Fin (r + 1), CFSG.IsQuasisimple ↥((SuSplitRootGen.lineBlock h d).map κ) :=
    fun d => CFSG.IsQuasisimple.of_mulEquiv
      ((SuSplitRootGen.lineBlock h d).equivMapOfInjective κ hκ).symm
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
        (hcomp d).2.2)
  have hlineK : ∀ d : Fin (r + 1), (SuSplitRootGen.lineBlock h d).map κ ≤ K := fun d => by
    rw [← hκK]
    exact Subgroup.map_le_range κ _
  have htorusR : ∀ d : Fin (r + 1), κ (τ (ofAdd (Pi.single d c))) ∈
      (SuSplitRootGen.lineBlock h d).map κ :=
    fun d => Subgroup.mem_map_of_mem κ (tau_single_mem_lineBlock hτ d c)
  have hnotC : ∀ d : Fin (r + 1), κ (τ (ofAdd (Pi.single d c))) ∉
      Subgroup.centralizer ((SuSplitRootGen.lineBlock h d).map κ : Set G) := by
    intro d hmem
    have hw : κ (SuSplitRootGen.lineWeyl h 0 d) ∈ (SuSplitRootGen.lineBlock h d).map κ :=
      Subgroup.mem_map_of_mem κ (SuSplitRootGen.lineWeyl_mem_lineBlock h d)
    have h1 := Subgroup.mem_centralizer_iff.mp hmem _ hw
    rw [← map_mul, ← map_mul] at h1
    exact hnc d (hκ h1)
  have htB : κ (τ (ofAdd (Pi.single m c))) ∈ Bs := htorusB _
  have hηt : ∀ i, eta ⟨κ (τ (ofAdd (Pi.single m c))), htB⟩ (π i.succ) =
      if i = m then ofAdd 1 else 1 := by
    intro i
    have hi := congrFun (hexT (Pi.single m c)) i
    by_cases him : i = m
    · rw [if_pos him]
      rw [him, Pi.single_eq_same] at hi
      have h1 : toAdd (eta ⟨κ (τ (ofAdd (Pi.single m c))), htB⟩ (π m.succ)) = 1 := by
        have : Fact p.Prime := ⟨hp⟩
        exact mul_left_cancel₀ hc (hi.trans (mul_one c).symm)
      rw [him]
      exact toAdd.injective (h1.trans (toAdd_ofAdd 1).symm)
    · rw [if_neg him]
      rw [Pi.single_eq_of_ne him] at hi
      exact hcoord _ i hi
  have hgen : ∀ e ∈ Bs, ∃ h' ∈ ggBsCoordZero Bs eta (π m.succ), ∃ k : ℤ,
      e = h' * κ (τ (ofAdd (Pi.single m c))) ^ k := by
    have : Fact p.Prime := ⟨hp⟩
    exact ggSecFiveBHgen_long (Bs := Bs) htB hηt
  have hX : Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G) ≤
      Subgroup.normalizer (K : Set G) := by
    intro g hg
    obtain ⟨d, hdm⟩ : ∃ d : Fin (r + 1), d ≠ m := by
      by_cases hm0 : m = 0
      · refine ⟨⟨1, by omega⟩, fun h10 => ?_⟩
        rw [hm0] at h10
        simp [Fin.ext_iff] at h10
      · exact ⟨0, Ne.symm hm0⟩
    have hgy : g ∈ Subgroup.centralizer ({y} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact Subgroup.mem_centralizer_iff.mp hg y hyH
    have hgr : g * κ (τ (ofAdd (Pi.single d c))) = κ (τ (ofAdd (Pi.single d c))) * g :=
      (Subgroup.mem_centralizer_iff.mp hg _ (htorusH d hdm)).symm
    have hpJ : p ∣ Nat.card ↥((SuSplitRootGen.lineBlock h d).map κ) := by
      rw [Subgroup.card_map_of_injective hκ]
      exact SuSplitRootGen.dvd_card_lineBlock h hp hζ hτs d
    have : Fact p.Prime := ⟨hp⟩
    exact ggMem_normalizer_of_pComponent hK (hlineK d)
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
        (hRq d)) hpJ (htorusR d) (hnotC d) hgy hgr
  have hRC : (SuSplitRootGen.lineBlock h m).map κ ≤
      Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G) := by
    intro z hz
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hbB : b ∈ Bs := ggBsCoordZero_le (π m.succ) hb
    have hη : eta ⟨b, hbB⟩ (π m.succ) = 1 := (coe_mem_ggBsCoordZero (b := ⟨b, hbB⟩)).mp hb
    have hfix : τ (ofAdd (frameExp eta π c ⟨b, hbB⟩)) ∈
        SuSplitRootGen.torusFix τ (SlNsRootGen.negMap m) := by
      refine ⟨ofAdd (frameExp eta π c ⟨b, hbB⟩), ?_, rfl⟩
      show SlNsRootGen.negMap m (frameExp eta π c ⟨b, hbB⟩) = frameExp eta π c ⟨b, hbB⟩
      have h0 : frameExp eta π c ⟨b, hbB⟩ m = 0 := by
        show c * toAdd (eta ⟨b, hbB⟩ (π m.succ)) = 0
        rw [hη, toAdd_one]
        exact mul_zero c
      have : Fact p.Prime := ⟨hp⟩
      exact (SlNsRootGen.negMap_eq_self_iff hp2).mpr h0
    have hxc := Subgroup.mem_centralizer_iff.mp ((hcomp m).1 hx) _ hfix
    have h1 := hact' ⟨b, hbB⟩ x
    rw [hxc, mul_inv_cancel_right] at h1
    calc b * κ x = b * κ x * b⁻¹ * b := by group
      _ = κ x * b := by rw [show b * κ x * b⁻¹ = κ x from h1]
  have hRt : (SuSplitRootGen.lineBlock h m).map κ ≤
      ⁅(SuSplitRootGen.lineBlock h m).map κ,
        Subgroup.zpowers (κ (τ (ofAdd (Pi.single m c))))⁆ :=
    CFSG.SeitzReduction.F4Pilot.le_commutator_zpowers_of_isQuasisimple (hRq m)
      (Subgroup.le_normalizer (htorusR m)) (hnotC m)
  have hRD : (SuSplitRootGen.lineBlock h m).map κ ≤
      K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G) :=
    le_inf (hlineK m) hRC
  have ht : κ (τ (ofAdd (Pi.single m c))) ∈
      ⁅K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G),
        K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G)⁆ :=
    Subgroup.commutator_mono hRD (Subgroup.zpowers_le.mpr (hRD (htorusR m))) (hRt (htorusR m))
  have hsep : ∀ x : hypSU h (r + 1) 0,
      κ x ∈ Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G) →
      SepOn (SuSplitRootGen.lineCoords m) (hmat x) := by
    intro x hx z z' hzz' hT
    have hcomm : ∀ k : Fin (r + 1), k ≠ m → Commute (τ (ofAdd (Pi.single k c))) x := by
      intro k hkm
      have hbη : ∀ i, eta (eta.symm (Pi.mulSingle (π k.succ) (ofAdd 1))) (π i.succ) =
          if i = k then ofAdd 1 else 1 := by
        intro i
        rw [MulEquiv.apply_symm_apply]
        by_cases hik : i = k
        · rw [hik, if_pos rfl, Pi.mulSingle_eq_same]
        · rw [if_neg hik, Pi.mulSingle_eq_of_ne
            (fun he => hik (Fin.succ_inj.mp (π.injective he))) _]
      have hbH : ((eta.symm (Pi.mulSingle (π k.succ) (ofAdd 1)) : ↥Bs) : G) ∈
          ggBsCoordZero Bs eta (π m.succ) := by
        refine (coe_mem_ggBsCoordZero (b := eta.symm (Pi.mulSingle (π k.succ) (ofAdd 1)))).mpr ?_
        rw [hbη, if_neg (Ne.symm hkm)]
      have hexb : frameExp eta π c (eta.symm (Pi.mulSingle (π k.succ) (ofAdd 1))) =
          Pi.single k c := by
        funext i
        show c * toAdd (eta (eta.symm (Pi.mulSingle (π k.succ) (ofAdd 1))) (π i.succ)) =
          (Pi.single k c : Fin (r + 1) → ZMod p) i
        rw [hbη]
        by_cases hik : i = k
        · rw [if_pos hik, hik, toAdd_ofAdd]
          simp
        · rw [if_neg hik, toAdd_one]
          simp [hik]
      have h1 := hact' (eta.symm (Pi.mulSingle (π k.succ) (ofAdd 1))) x
      rw [Subgroup.mem_centralizer_iff.mp hx _ hbH, mul_inv_cancel_right, hexb] at h1
      have h2 := hκ h1
      show τ (ofAdd (Pi.single k c)) * x = x * τ (ofAdd (Pi.single k c))
      calc τ (ofAdd (Pi.single k c)) * x
          = τ (ofAdd (Pi.single k c)) * x * (τ (ofAdd (Pi.single k c)))⁻¹ *
              τ (ofAdd (Pi.single k c)) := by group
        _ = x * τ (ofAdd (Pi.single k c)) := by rw [← h2]
    have hdiag : ∀ k : Fin (r + 1), k ≠ m →
        Commute (diagonal (hypEntries ζ (Pi.single k c))) (hmat x) := by
      intro k hkm
      have h1 := congrArg (fun w : hypSU h (r + 1) 0 => hmat w) (hcomm k hkm).eq
      simp only [hmat, Subgroup.coe_mul, Units.val_mul, hτ] at h1
      exact h1
    rcases hT with hz | hz'
    · obtain ⟨k, hkm, hk⟩ := exists_idx_of_not_mem hz
      exact TauCeti.apply_eq_zero_of_commute_diagonal (hdiag k hkm)
        (hypEntries_single_ne hp hp2 hζ hc hk hzz')
    · obtain ⟨k, hkm, hk⟩ := exists_idx_of_not_mem hz'
      exact TauCeti.apply_eq_zero_of_commute_diagonal (hdiag k hkm)
        (hypEntries_single_ne hp hp2 hζ hc hk (Ne.symm hzz')).symm
  have hDR : ⁅K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G),
      K ⊓ Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G)⁆ ≤
      (SuSplitRootGen.lineBlock h m).map κ := by
    rw [Subgroup.commutator_le]
    intro g₁ hg₁ g₂ hg₂
    obtain ⟨x₁, rfl⟩ : g₁ ∈ κ.range := by rw [hκK]; exact hg₁.1
    obtain ⟨x₂, rfl⟩ : g₂ ∈ κ.range := by rw [hκK]; exact hg₂.1
    have hinvC : ∀ x : hypSU h (r + 1) 0,
        κ x ∈ Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G) →
        κ x⁻¹ ∈ Subgroup.centralizer (ggBsCoordZero Bs eta (π m.succ) : Set G) :=
      fun x hx => by
        rw [map_inv]
        exact Subgroup.inv_mem _ hx
    rw [← map_commutatorElement]
    exact Subgroup.mem_map_of_mem κ (commutator_mem_lineBlock (hsep _ hg₁.2)
      (hsep _ (hinvC _ hg₁.2)) (hsep _ hg₂.2) (hsep _ (hinvC _ hg₂.2)))
  exact ggCommutator_centralizer_eq (E := Bs) (H := ggBsCoordZero Bs eta (π m.succ)) (X := K)
    (R := (SuSplitRootGen.lineBlock h m).map κ) (t := κ (τ (ofAdd (Pi.single m c)))) hBc
    (ggBsCoordZero_le (π m.succ)) htB hgen hX ht hDR hRC hRt

section LongNode

open CFSG.ClassicalInvolution.Phan (blockMat blockMat_apply)
open CFSG.RankThree.PartOne.CTP (embMid)
open CFSG.LieType.SeitzGeneration (hypEquivFin)
open CFSG.LieType.Universal.Unitary (SU)
open CFSG.LieType.BorelTits (unitaryInvolution)

private theorem rL_apply_of_not_mem {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]
    (A : SL(2, CFSG.LieType.Steinberg.fixedSubfield K 2 f)) {u v : Fin 6}
    (huv : (u ≠ 2 ∧ u ≠ 3) ∨ (v ≠ 2 ∧ v ≠ 3)) :
    (((CFSG.RankThree.PartTwo.CTU6.rL K f A : SU (unitaryInvolution K 2 f) 6) :
      GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) u v = (1 : Matrix (Fin 6) (Fin 6) K) u v := by
  show (((CFSG.RankThree.PartTwo.CTU6.embSU4 _ (CFSG.RankThree.PartTwo.CTU6.lbSU4 K f A) :
      SU (unitaryInvolution K 2 f) 6) : GL (Fin 6) K) :
      Matrix (Fin 6) (Fin 6) K) u v = _
  rw [CFSG.RankThree.PartTwo.CTU6.coe_embSU4, CFSG.RankThree.PartTwo.CTU6.coe_lbSU4]
  fin_cases u <;> fin_cases v <;> simp_all [blockMat_apply, embMid]

private theorem mem_lineCoords_two_of_pos {x : HypIndex 3 0}
    (hx : hypEquivFin 3 0 x = 2 ∨ hypEquivFin 3 0 x = 3) :
    x ∈ SuSplitRootGen.lineCoords (ε := 0) (2 : Fin 3) := by
  rcases x with i | k | i
  · have hi := i.isLt
    have hi2 : i = 2 := by
      apply Fin.ext
      rcases hx with hx | hx <;> have := congrArg Fin.val hx <;>
        simp [hypEquivFin, Equiv.ofBijective_apply, fullPos] at this <;> simp <;> omega
    subst hi2
    exact Or.inl rfl
  · exact k.elim0
  · have hi := i.isLt
    have hi2 : i = 2 := by
      apply Fin.ext
      rcases hx with hx | hx <;> have := congrArg Fin.val hx <;>
        simp [hypEquivFin, Equiv.ofBijective_apply, fullPos] at this <;> simp <;> omega
    subst hi2
    exact Or.inr (Or.inr rfl)

theorem lineBlock_two_map_hypSUEquiv {K : Type} [Field K] [Finite K] [CharP K 2] {f : ℕ}
    (h : UnitaryFieldData 2 f K) :
    (SuSplitRootGen.lineBlock (ε := 0) h (2 : Fin 3)).map
        (SuSplitRootGen.hypSUEquiv (r := 3) (ε := 0) h (by decide)).toMonoidHom =
      (CFSG.RankThree.PartTwo.CTU6.rL K f).range := by
  have hε : (0 : ℕ) ≤ 1 := by decide
  refine (Subgroup.eq_of_le_of_card_ge ?_ ?_).symm
  · rintro _ ⟨A, rfl⟩
    rw [Subgroup.mem_map_equiv, SuSplitRootGen.lineBlock, SuSplitRootGen.mem_hypBlock]
    intro x y hxy
    have hM := SuSplitRootGen.coe_hypSUEquiv (r := 3) h hε
      ((SuSplitRootGen.hypSUEquiv (r := 3) h hε).symm (CFSG.RankThree.PartTwo.CTU6.rL K f A))
    rw [MulEquiv.apply_symm_apply] at hM
    have hentry : (((((SuSplitRootGen.hypSUEquiv (r := 3) h hε).symm
        (CFSG.RankThree.PartTwo.CTU6.rL K f A) : hypSU h 3 0) : GL (HypIndex 3 0) K) :
          Matrix (HypIndex 3 0) (HypIndex 3 0) K)) x y =
        (((CFSG.RankThree.PartTwo.CTU6.rL K f A : SU (unitaryInvolution K 2 f) 6) :
          GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) (hypEquivFin 3 0 x) (hypEquivFin 3 0 y) := by
      rw [hM, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
        Equiv.symm_apply_apply]
    have huv : (hypEquivFin 3 0 x ≠ 2 ∧ hypEquivFin 3 0 x ≠ 3) ∨
        (hypEquivFin 3 0 y ≠ 2 ∧ hypEquivFin 3 0 y ≠ 3) := by
      rcases hxy with hx | hy
      · exact Or.inl ⟨fun h2 => hx (mem_lineCoords_two_of_pos (Or.inl h2)),
          fun h3 => hx (mem_lineCoords_two_of_pos (Or.inr h3))⟩
      · exact Or.inr ⟨fun h2 => hy (mem_lineCoords_two_of_pos (Or.inl h2)),
          fun h3 => hy (mem_lineCoords_two_of_pos (Or.inr h3))⟩
    rw [hentry, rL_apply_of_not_mem A huv]
    simp only [Matrix.one_apply, EmbeddingLike.apply_eq_iff_eq]
  · rw [Subgroup.card_map_of_injective (SuSplitRootGen.hypSUEquiv h hε).injective]
    obtain ⟨e1⟩ := SuSplitRootGen.nonempty_lineBlock_mulEquiv (ε := 0) h (2 : Fin 3)
    rw [Nat.card_congr e1.toEquiv,
      Nat.card_congr (SuSplitRootGen.hypSUEquiv h (r := 1) hε).toEquiv,
      ← Nat.card_congr (MonoidHom.ofInjective
        (CFSG.RankThree.PartTwo.CTU6.rL_injective (K := K) (f := f))).toEquiv,
      ← Nat.card_congr (Equiv.ofBijective _
        ⟨CFSG.LieType.Steinberg.hypHom_injective one_ne_zero
          CFSG.RankThree.PartTwo.CTU6.unitaryInvolution_one_eq_neg,
        CFSG.LieType.Steinberg.hypHom_surjective one_ne_zero
          CFSG.RankThree.PartTwo.CTU6.unitaryInvolution_one_eq_neg⟩)]

theorem lineBlock_two_map_eq_range_rL {G : Type} [Group G] {K : Type} [Field K] [Finite K]
    [CharP K 2] {f : ℕ} (h : UnitaryFieldData 2 f K) (κ : hypSU h 3 0 →* G) :
    (SuSplitRootGen.lineBlock h (2 : Fin 3)).map κ =
      ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp
        (CFSG.RankThree.PartTwo.CTU6.rL K f)).range := by
  rw [MonoidHom.range_comp, ← lineBlock_two_map_hypSUEquiv h, Subgroup.map_map]
  congr 1
  ext x
  simp

end LongNode

theorem ggSecFiveBPermSU_singletonComm_K_rL [Finite G] {n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : UnitaryFieldData 2 a (GaloisField 2 (2 * a))) (hpq : p ∣ 2 ^ a - 1)
    {Bs K : Subgroup G} {y : G}
    (hBc : ∀ x ∈ Bs, ∀ z ∈ Bs, x * z = z * x)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hyB : y ∈ Bs) (hK : LargeEvenPComponent p (Subgroup.centralizer {y}) K)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin 4 ≃ Fin n}
    {κ : hypSU h 3 0 →* G} (hκ : Function.Injective κ) (hκK : κ.range = K)
    {ζ : GaloisField 2 (2 * a)} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0}
    (hτ : ∀ t, (((τ (Multiplicative.ofAdd t) : hypSU h 3 0) :
      GL (HypIndex 3 0) (GaloisField 2 (2 * a))) :
        Matrix (HypIndex 3 0) (HypIndex 3 0) (GaloisField 2 (2 * a))) =
          Matrix.diagonal (hypEntries ζ t))
    {c : ZMod p} (hc : c ≠ 0)
    (hact : ∀ (b : ↥Bs) (s : hypSU h 3 0), (b : G) * κ s * (b : G)⁻¹ =
      κ (τ (Multiplicative.ofAdd fun i => c * Multiplicative.toAdd (eta b (π i.succ))) * s *
        (τ (Multiplicative.ofAdd fun i => c * Multiplicative.toAdd (eta b (π i.succ))))⁻¹)) :
    ⁅Subgroup.centralizer (ggBsCoordZero Bs eta (π 3) : Set G), Bs⁆ =
      ((κ.comp (SuSplitRootGen.hypSUEquiv h (by decide)).symm.toMonoidHom).comp
        (CFSG.RankThree.PartTwo.CTU6.rL (GaloisField 2 (2 * a)) a)).range := by
  rw [← lineBlock_two_map_eq_range_rL h κ]
  exact ggSecFiveBPermSU_singletonComm_K (r := 2) hp hp2 h hpq (by norm_num) hBc hBs hyB hK hκ
    hκK hζ hτ hc hact 2

end CFSG.StandardType

end
