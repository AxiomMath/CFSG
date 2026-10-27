module

public import CFSG.LocalAnalysis.StandardType.GGLayerCenterCyclicExcSix
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelKernelCore
public import CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.Lift
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthRestTorus
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.E6ThreeScLift

public section

namespace CFSG.LocalAnalysis.StandardType

namespace GGTBE6Cover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.LieType.Steinberg.Isogeny CFSG.LieType.Steinberg.CentralExt
  CFSG.HardMathSupport.Timmesfeld.CrossChar


noncomputable instance instFiniteMinGroupE6Cover (K : Type) [Field K] [Finite K] :
    Finite ↥(e6Data_valid.minGroup K) :=
  CFSG.LieType.Steinberg.CentralExt.FieldFour.finite_minGroup' (K := K) e6Data_valid

private lemma e6_nm_sq (k : Type) [Field k] [Finite k] [CharP k 2] (i : Fin Tag.E6.rank) :
    e6Data_valid.nm k i * e6Data_valid.nm k i = 1 := by
  rw [← pow_two, e6Data_valid.nm_sq k i]
  have h1 : (-1 : kˣ) = 1 := Units.ext (CharTwo.neg_eq (1 : k))
  rw [h1, e6Data_valid.hm_one]

private lemma e6_nt_sq (k : Type) [Field k] [Finite k] [CharP k 2]
    (i : Fin Tag.E6.rank) (s : kˣ) :
    e6Data_valid.nt k i s * e6Data_valid.nt k i s = 1 := by
  let D : MinData Tag.E6 := e6Data
  let hV : D.Valid := e6Data_valid
  have hStar : e6StarS i (Pi.mulSingle i s) = Pi.mulSingle i s⁻¹ := by
    funext j
    by_cases hj : j = i
    · rw [hj]
      simp only [e6StarS, Pi.mul_apply, Pi.mulSingle_eq_same]
      rw [Finset.prod_eq_single i]
      · rw [Pi.mulSingle_eq_same, Tag.cartan_self]
        rw [show s ^ (-(2 : ℤ)) = s⁻¹ * s⁻¹ by
          rw [← zpow_neg_one s, ← zpow_add]; norm_num]
        group
      · intro b _ hb
        rw [Pi.mulSingle_eq_of_ne hb, one_zpow]
      · intro h
        exact absurd (Finset.mem_univ i) h
    · rw [Pi.mulSingle_eq_of_ne hj]
      simp only [e6StarS, Pi.mul_apply, Pi.mulSingle_eq_of_ne hj, mul_one]
  rw [hV.nt_eq_hm_mul]
  have hconj := nm_conj_minTorus k i (Pi.mulSingle i s)
  have hconj' : hV.nm k i * hV.hm k i s * (hV.nm k i)⁻¹ = hV.hm k i s⁻¹ := by
    simpa only [hStar, CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus_mulSingle]
      using hconj
  have hcomm : hV.nm k i * hV.hm k i s = hV.hm k i s⁻¹ * hV.nm k i := by
    calc hV.nm k i * hV.hm k i s
        = (hV.nm k i * hV.hm k i s * (hV.nm k i)⁻¹) * hV.nm k i := by group
      _ = hV.hm k i s⁻¹ * hV.nm k i := by rw [hconj']
  calc (hV.hm k i s * hV.nm k i) * (hV.hm k i s * hV.nm k i)
      = hV.hm k i s * (hV.nm k i * hV.hm k i s) * hV.nm k i := by group
    _ = hV.hm k i s * (hV.hm k i s⁻¹ * hV.nm k i) * hV.nm k i := by rw [hcomm]
    _ = (hV.hm k i s * hV.hm k i s⁻¹) * (hV.nm k i * hV.nm k i) := by group
    _ = 1 := by rw [← hV.hm_mul, mul_inv_cancel, hV.hm_one, e6_nm_sq k i, one_mul]


private lemma e6Isogeny_nt_mul (K : Type) [Field K] [Finite K] (i : Fin Tag.E6.rank)
    (s : Kˣ) :
    e6Isogeny K (e6Data_valid.nt K i s) =
      torusElement .E6 K i s * weylElement .E6 K i := by
  apply Subtype.ext
  rw [e6Isogeny_nt_eq]
  change weylElt .E6 K i s = torusElt .E6 K i s * weylElt .E6 K i 1
  exact weylElt_eq_torusElt_mul_weylElt_one i s

private lemma rootDiagAut_torusElement (K : Type) [Field K] (b : Fin Tag.E6.rank → Kˣ)
    (i : Fin Tag.E6.rank) (s : Kˣ) :
    rootDiagAutHom .E6 K b (torusElement .E6 K i s) = torusElement .E6 K i s := by
  change rootDiagAut .E6 K b (torusElement .E6 K i s) = torusElement .E6 K i s
  apply Subtype.ext
  change CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 b *
      torusElt .E6 K i s *
      (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 b)⁻¹ =
    torusElt .E6 K i s
  rw [CFSG.LieType.Chevalley.rootDiagUnit_mul_comm_of_mem_torusGroup b
    (CFSG.LieType.Chevalley.torusElt_mem_torusGroup i s)]
  group

private lemma rootDiagAut_weylElement (K : Type) [Field K] (b : Fin Tag.E6.rank → Kˣ)
    (i : Fin Tag.E6.rank) :
    rootDiagAutHom .E6 K b (weylElement .E6 K i) =
      torusElement .E6 K i (b i) * weylElement .E6 K i := by
  change rootDiagAut .E6 K b (weylElement .E6 K i) =
    torusElement .E6 K i (b i) * weylElement .E6 K i
  apply Subtype.ext
  change CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 b *
      weylElt .E6 K i 1 *
      (CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootDiagUnit .E6 b)⁻¹ =
    torusElt .E6 K i (b i) * weylElt .E6 K i 1
  exact CFSG.LieType.Chevalley.rootDiagUnit_conj_weylElt_one b i

private lemma rootDiagAut_nt_mul (K : Type) [Field K] [Finite K]
    (b : Fin Tag.E6.rank → Kˣ) (i : Fin Tag.E6.rank) (s : Kˣ) :
    rootDiagAutHom .E6 K b (e6Isogeny K (e6Data_valid.nt K i s)) =
      e6Isogeny K (e6Data_valid.nt K i (b i * s)) := by
  rw [e6Isogeny_nt_mul, e6Isogeny_nt_mul, map_mul,
    rootDiagAut_torusElement K b i s, rootDiagAut_weylElement K b i]
  have hts : torusElement .E6 K i s * torusElement .E6 K i (b i) =
      torusElement .E6 K i (s * b i) := by
    apply Subtype.ext
    exact (torusElt_mul i s (b i)).symm
  calc torusElement .E6 K i s * (torusElement .E6 K i (b i) * weylElement .E6 K i)
      = (torusElement .E6 K i s * torusElement .E6 K i (b i)) * weylElement .E6 K i := by
        group
    _ = torusElement .E6 K i (s * b i) * weylElement .E6 K i := by rw [hts]
    _ = torusElement .E6 K i (b i * s) * weylElement .E6 K i := by rw [mul_comm]

section Lift

variable (K : Type) [Field K] [Finite K] [CharP K 2]
  (n : ℕ) (hK : Nat.card K = 2 ^ n)
include n hK

omit [CharP K 2] in
private lemma alpha_exists (b : Fin Tag.E6.rank → Kˣ) :
    ∃ α : MulAut ↥(e6Data_valid.minGroup K),
      ∀ x, e6Isogeny K (α x) = rootDiagAutHom .E6 K b (e6Isogeny K x) := by
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact CFSG.HardMathSupport.Cooperstein.Coordinator.CurtisE6.exists_lift_aut
    (e6Isogeny K) (e6Isogeny_surjective K)
    (CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center (F := K))
    (CFSG.LieType.CurtisTits.isPerfect_e6 K).commutator_eq_top
    (fun E _ _ π hπ hcen =>
      CFSG.StandardType.LayerCycExc.e6_minGroup_exists_section hK E π hπ hcen)
    (rootDiagAutHom .E6 K b)

private noncomputable def alpha (b : Fin Tag.E6.rank → Kˣ) :
    MulAut ↥(e6Data_valid.minGroup K) :=
  Classical.choose (alpha_exists K n hK b)

omit [CharP K 2] in
private lemma alpha_spec (b : Fin Tag.E6.rank → Kˣ) (x : ↥(e6Data_valid.minGroup K)) :
    e6Isogeny K (alpha K n hK b x) =
      rootDiagAutHom .E6 K b (e6Isogeny K x) :=
  Classical.choose_spec (alpha_exists K n hK b) x


omit [CharP K 2] in
private lemma alpha_unique (b : Fin Tag.E6.rank → Kˣ)
    {β : MulAut ↥(e6Data_valid.minGroup K)}
    (hβ : ∀ x, e6Isogeny K (β x) = rootDiagAutHom .E6 K b (e6Isogeny K x)) :
    β = alpha K n hK b := by
  apply MulEquiv.toMonoidHom_injective
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : Group.IsPerfect (e6Data_valid.minGroup K) := CFSG.LieType.CurtisTits.isPerfect_e6 K
  have hker : (e6Isogeny K).ker ≤ Subgroup.center (e6Data_valid.minGroup K) := by
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
  apply CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect
    hker
  apply MonoidHom.ext
  intro x
  change e6Isogeny K (β x) = e6Isogeny K (alpha K n hK b x)
  rw [hβ x, alpha_spec K n hK b x]

noncomputable def diagonalHom :
    (Fin Tag.E6.rank → Kˣ) →* MulAut ↥(e6Data_valid.minGroup K) where
  toFun := alpha K n hK
  map_one' := by
    have h : (1 : MulAut ↥(e6Data_valid.minGroup K)) = alpha K n hK 1 :=
      alpha_unique K n hK 1 (by intro x; simp)
    exact h.symm
  map_mul' b c := by
    have h : alpha K n hK b * alpha K n hK c = alpha K n hK (b * c) := by
      apply alpha_unique K n hK (b * c)
      intro x
      rw [MulAut.mul_apply, alpha_spec K n hK b, alpha_spec K n hK c, map_mul,
        MulAut.mul_apply]
    exact h.symm

omit [CharP K 2] in
theorem diagonalHom_isogeny (b : Fin Tag.E6.rank → Kˣ) (x : e6Data_valid.minGroup K) :
    e6Isogeny K (diagonalHom K n hK b x) =
      rootDiagAutHom .E6 K b (e6Isogeny K x) :=
  alpha_spec K n hK b x

theorem diagonalHom_nt (b : Fin Tag.E6.rank → Kˣ)
    (i : Fin Tag.E6.rank) (s : Kˣ) :
    diagonalHom K n hK b (e6Data_valid.nt K i s) =
      e6Data_valid.nt K i (b i * s) := by
  have hker : (e6Isogeny K).ker ≤ Subgroup.center (e6Data_valid.minGroup K) := by
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center]
  have hodd : Nat.Coprime 2 (Nat.card (e6Isogeny K).ker) := by
    obtain ⟨hc, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K
    rw [CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center, hc]
    exact (by decide : Nat.Coprime 2 3).of_dvd_right (Nat.gcd_dvd_left _ _)
  apply CFSG.StandardType.OrthRest.eq_of_lift_of_coprime hker hodd
  · change e6Isogeny K (alpha K n hK b (e6Data_valid.nt K i s)) = _
    rw [alpha_spec, rootDiagAut_nt_mul]
  · change (diagonalHom K n hK b (e6Data_valid.nt K i s)) ^ 2 = 1
    rw [← map_pow, pow_two, e6_nt_sq, map_one]
  · change e6Data_valid.nt K i (b i * s) ^ 2 = 1
    rw [pow_two, e6_nt_sq]

theorem diagonalHom_hm (b : Fin Tag.E6.rank → Kˣ)
    (i : Fin Tag.E6.rank) (s : Kˣ) :
    diagonalHom K n hK b (e6Data_valid.hm K i s) = e6Data_valid.hm K i s := by
  change diagonalHom K n hK b (e6Data_valid.nt K i s * (e6Data_valid.nt K i 1)⁻¹) = _
  rw [map_mul, map_inv, diagonalHom_nt K n hK b i s, diagonalHom_nt K n hK b i 1,
    mul_one, e6Data_valid.nt_eq_hm_mul, e6Data_valid.nt_eq_hm_mul]
  have hmul : e6Data_valid.hm K i (b i * s) =
      e6Data_valid.hm K i s * e6Data_valid.hm K i (b i) := by
    rw [mul_comm (b i) s, e6Data_valid.hm_mul]
  rw [hmul]
  group

theorem diagonalHom_minTorus (b : Fin Tag.E6.rank → Kˣ)
    (u : Fin Tag.E6.rank → Kˣ) :
    diagonalHom K n hK b (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K u) =
      CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K u := by
  induction u using CFSG.LieType.Chevalley.ExceptionalCover.torusVec_induction with
  | h1 => simp
  | hmul t t' ht ht' =>
      rw [map_mul, map_mul, ht, ht']
  | hsingle i s =>
      rw [CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus_mulSingle,
        diagonalHom_hm K n hK b i s]

end Lift


private lemma card_eq_two_pow (K : Type) [Field K] [Finite K] [CharP K 2] :
    ∃ n : ℕ, Nat.card K = 2 ^ n := by
  let : Fintype K := Fintype.ofFinite K
  obtain ⟨n, -, hK⟩ := FiniteField.card K 2
  exact ⟨(n : ℕ), by simpa using hK⟩

theorem exists_cover_phi (K : Type) [Field K] [Finite K] [CharP K 2]
    (L : Type) [Group L] [Finite L]
    (ψ : L →* adjointGroup .E6 K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) :
    ∃ φ : ↥(e6Data_valid.minGroup K) →* L,
      Function.Surjective φ ∧ (∀ x, ψ (φ x) = e6Isogeny K x) ∧
      φ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup K) := by
  obtain ⟨n, hK⟩ := card_eq_two_pow K
  let : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsec : ∀ (E : Type) [Group E] [Finite E]
      (π : E →* ↥(e6Data_valid.minGroup K)), Function.Surjective π →
      π.ker ≤ Subgroup.center E →
        ∃ s : ↥(e6Data_valid.minGroup K) →* E, ∀ g, π (s g) = g :=
    fun E _ _ π hπ hcen =>
      CFSG.StandardType.LayerCycExc.e6_minGroup_exists_section hK E π hπ hcen
  obtain ⟨φ, hφ, hφsurj⟩ :=
    CFSG.StandardType.E6ThreeKernel.exists_surjective_of_split
      (q := e6Isogeny K) (e6Isogeny_surjective K) hsec hψ hker hperf
  refine ⟨φ, hφsurj, hφ, ?_⟩
  intro x hx
  apply CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center
  rw [MonoidHom.mem_ker, ← hφ x, hx, map_one]

theorem exists_cover_and_diagonal_lift (K : Type) [Field K] [Finite K] [CharP K 2]
    (L : Type) [Group L] [Finite L]
    (ψ : L →* adjointGroup .E6 K) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L) (hperf : commutator L = ⊤) :
    ∃ (φ : ↥(e6Data_valid.minGroup K) →* L)
      (δ : (Fin Tag.E6.rank → Kˣ) →* MulAut L),
      Function.Surjective φ ∧ (∀ x, ψ (φ x) = e6Isogeny K x) ∧
      φ.ker ≤ Subgroup.center ↥(e6Data_valid.minGroup K) ∧
      Function.Injective δ ∧
      (∀ b l, ψ (δ b l) = rootDiagAut .E6 K b (ψ l)) ∧
      (∀ (b : Fin Tag.E6.rank → Kˣ) (i : Fin Tag.E6.rank) (s : Kˣ),
        δ b (φ (e6Data_valid.hm K i s)) = φ (e6Data_valid.hm K i s)) ∧
      (∀ (b : Fin Tag.E6.rank → Kˣ) (u : Fin Tag.E6.rank → Kˣ),
        δ b (φ (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K u)) =
          φ (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K u)) ∧
      (∀ (b : Fin Tag.E6.rank → Kˣ) (i : Fin Tag.E6.rank),
        δ b (φ (e6Data_valid.nm K i)) =
          φ (e6Data_valid.hm K i (b i)) * φ (e6Data_valid.nm K i)) := by
  obtain ⟨n, hK⟩ := card_eq_two_pow K
  obtain ⟨φ, hφsurj, hφ, hφker⟩ := exists_cover_phi K L ψ hψ hker hperf
  have hcardZ : Nat.card (Subgroup.center ↥(e6Data_valid.minGroup K)) ∣ 3 := by
    obtain ⟨hc, -⟩ := CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.card_center_e6 K
    rw [hc]
    exact Nat.gcd_dvd_left _ _
  have hker_cases : φ.ker = ⊥ ∨
      φ.ker = Subgroup.center ↥(e6Data_valid.minGroup K) := by
    have hc := (Subgroup.card_dvd_of_le hφker).trans hcardZ
    rcases (Nat.dvd_prime Nat.prime_three).1 hc with hbot | htop
    · left
      exact Subgroup.eq_bot_of_card_le (H := φ.ker) (by rw [hbot])
    · right
      apply Subgroup.eq_of_le_of_card_ge hφker
      rw [htop]
      exact Nat.le_of_dvd (by decide : 0 < 3) hcardZ
  have alpha_mem : ∀ (b : Fin Tag.E6.rank → Kˣ)
      {z : ↥(e6Data_valid.minGroup K)}, z ∈ φ.ker →
      diagonalHom K n hK b z ∈ φ.ker := by
    intro b z hz
    rcases hker_cases with hbot | htop
    · have hz1 : z = 1 := by
        have : z ∈ (⊥ : Subgroup ↥(e6Data_valid.minGroup K)) := by
          simpa [hbot] using hz
        exact Subgroup.mem_bot.mp this
      rw [hz1, map_one]
      exact φ.ker.one_mem
    · have hzZ : z ∈ Subgroup.center ↥(e6Data_valid.minGroup K) := by
        rw [← htop]; exact hz
      have hαZ := CFSG.StandardType.BstarDesc.mulAut_mem_center (diagonalHom K n hK b) hzZ
      simpa [htop] using hαZ
  let deltaHom : (Fin Tag.E6.rank → Kˣ) → L →* L := fun b =>
    (QuotientGroup.lift φ.ker
      (φ.comp (diagonalHom K n hK b).toMonoidHom)
      (by
        intro z hz
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
        exact alpha_mem b hz)).comp
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).symm.toMonoidHom
  have deltaHom_apply : ∀ (b : Fin Tag.E6.rank → Kˣ)
      (x : ↥(e6Data_valid.minGroup K)),
      deltaHom b (φ x) = φ (diagonalHom K n hK b x) := by
    intro b x
    have he : (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).symm (φ x) =
        (QuotientGroup.mk x : ↥(e6Data_valid.minGroup K) ⧸ φ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    change QuotientGroup.lift φ.ker
      (φ.comp (diagonalHom K n hK b).toMonoidHom)
      (by
        intro z hz
        rw [MonoidHom.mem_ker, MonoidHom.comp_apply]
        exact alpha_mem b hz)
      ((QuotientGroup.quotientKerEquivOfSurjective φ hφsurj).symm (φ x)) = _
    rw [he, QuotientGroup.lift_mk]
    rfl
  have deltaHom_surj : ∀ b, Function.Surjective (deltaHom b) := by
    intro b y
    obtain ⟨x, rfl⟩ := hφsurj y
    refine ⟨φ ((diagonalHom K n hK b)⁻¹ x), ?_⟩
    rw [deltaHom_apply]
    simp
  have deltaHom_inj : ∀ b, Function.Injective (deltaHom b) := by
    intro b
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := hφsurj y
    rw [deltaHom_apply] at hy
    have hx : x ∈ φ.ker := by
      have hstep := alpha_mem (b := b⁻¹) hy
      simpa [map_inv] using hstep
    simpa [MonoidHom.mem_ker] using hx
  let delta : (Fin Tag.E6.rank → Kˣ) → MulAut L := fun b =>
    MulEquiv.ofBijective (deltaHom b) ⟨deltaHom_inj b, deltaHom_surj b⟩
  have delta_apply_phi : ∀ (b : Fin Tag.E6.rank → Kˣ)
      (x : ↥(e6Data_valid.minGroup K)),
      delta b (φ x) = φ (diagonalHom K n hK b x) := by
    intro b x
    change deltaHom b (φ x) = _
    exact deltaHom_apply b x
  have delta_comp : ∀ (b : Fin Tag.E6.rank → Kˣ) (l : L),
      ψ (delta b l) = rootDiagAutHom .E6 K b (ψ l) := by
    intro b l
    obtain ⟨x, rfl⟩ := hφsurj l
    rw [delta_apply_phi, hφ, hφ x]
    exact alpha_spec K n hK b x
  have delta_eq : ∀ {b c : Fin Tag.E6.rank → Kˣ},
      (∀ l, ψ (delta b l) = ψ (delta c l)) → delta b = delta c := by
    intro b c h
    have hZ := CFSG.StandardType.BstarDesc.ker_eq_center hψ hker
      (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) (K := K))
    apply CFSG.StandardType.BstarDesc.descAut_injective hψ hZ hperf
    apply MulEquiv.ext
    intro x
    obtain ⟨l, rfl⟩ := hψ x
    rw [CFSG.StandardType.BstarDesc.descAut_apply, CFSG.StandardType.BstarDesc.descAut_apply]
    exact h l
  let δ : (Fin Tag.E6.rank → Kˣ) →* MulAut L :=
    { toFun := delta
      map_one' := by
        apply MulEquiv.toMonoidHom_injective
        let : Group.IsPerfect L := ⟨hperf⟩
        apply CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker
        apply MonoidHom.ext
        intro l
        change ψ (delta 1 l) = ψ l
        rw [delta_comp]
        simp
      map_mul' := by
        intro b c
        apply MulEquiv.toMonoidHom_injective
        let : Group.IsPerfect L := ⟨hperf⟩
        apply CFSG.LieType.Steinberg.eq_of_comp_eq_of_isPerfect hker
        apply MonoidHom.ext
        intro l
        change ψ (delta (b * c) l) = ψ ((delta b * delta c) l)
        rw [delta_comp (b * c) l, MulAut.mul_apply, delta_comp b (delta c l),
          delta_comp c l, map_mul, MulAut.mul_apply] }
  have hδinj : Function.Injective δ := by
    rw [injective_iff_map_eq_one]
    intro b hb
    have hroot : rootDiagAutHom .E6 K b = 1 := by
      apply MulEquiv.ext
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      have h := congrArg (fun f : MulAut L => ψ (f l)) hb
      simpa [δ, delta_comp] using h
    exact rootDiagAutHom_injective (by simpa using hroot)
  have delta_hm : ∀ (b : Fin Tag.E6.rank → Kˣ) (i : Fin Tag.E6.rank) (s : Kˣ),
      δ b (φ (e6Data_valid.hm K i s)) = φ (e6Data_valid.hm K i s) := by
    intro b i s
    change delta b (φ (e6Data_valid.hm K i s)) = _
    rw [delta_apply_phi]
    rw [show diagonalHom K n hK b (e6Data_valid.hm K i s) = e6Data_valid.hm K i s from
      diagonalHom_hm K n hK b i s]
  have delta_minTorus : ∀ (b : Fin Tag.E6.rank → Kˣ) (u : Fin Tag.E6.rank → Kˣ),
      δ b (φ (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K u)) =
        φ (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K u) := by
    intro b u
    change delta b (φ (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K u)) = _
    rw [delta_apply_phi]
    rw [show diagonalHom K n hK b (CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K u) =
      CFSG.LieType.Steinberg.CentralExt.MinusculeClosed.minTorus e6Data_valid K u from
      diagonalHom_minTorus K n hK b u]
  have delta_nm : ∀ (b : Fin Tag.E6.rank → Kˣ) (i : Fin Tag.E6.rank),
      δ b (φ (e6Data_valid.nm K i)) =
        φ (e6Data_valid.hm K i (b i)) * φ (e6Data_valid.nm K i) := by
    intro b i
    change delta b (φ (e6Data_valid.nt K i 1)) = _
    rw [delta_apply_phi]
    have h := diagonalHom_nt K n hK b i 1
    rw [h, mul_one]
    rw [show e6Data_valid.nt K i (b i) =
      e6Data_valid.hm K i (b i) * e6Data_valid.nm K i from
      e6Data_valid.nt_eq_hm_mul K i (b i)]
    rw [map_mul]
  refine ⟨φ, δ, hφsurj, hφ, hφker, hδinj, ?_, delta_hm, delta_minTorus, delta_nm⟩
  intro b l
  change ψ (delta b l) = rootDiagAut .E6 K b (ψ l)
  simpa [rootDiagAutHom] using delta_comp b l


end GGTBE6Cover

end CFSG.LocalAnalysis.StandardType
