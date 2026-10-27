module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSUKToral
public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKAlign
import CFSG.LocalAnalysis.StandardType.GGRealKGUSplitRoot
import CFSG.LocalAnalysis.StandardType.GGTBJFrameBs
import CFSG.LocalAnalysis.StandardType.GGKGPosSUTorus
import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpKCent
import CFSG.ClassicalInvolution.ModelFacts.UnitaryAutLift
import CFSG.LieType.Universal.Unitary.Clause0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Open CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  Matrix Multiplicative

theorem hypSU_eq_one_of_mem_center_of_pow_eq_one {F : Type} [Field F] [Finite F] [CharP F 2]
    {p a : ℕ} (hF : Nat.card F = (2 ^ a) ^ 2) (h : UnitaryFieldData 2 a F)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ a - 1) {z : hypSU h 3 0}
    (hz : z ∈ Subgroup.center (hypSU h 3 0)) (hzp : z ^ p = 1) : z = 1 := by
  let eH : hypSU h 3 0 ≃* SU (unitaryInvolution F 2 a) 6 :=
    SuSplitRootGen.hypSUEquiv h (by decide)
  apply eH.injective
  rw [map_one]
  apply KGPosSU.eq_one_of_mem_center_of_pow_eq_one hF hp hp2 hpq
  · rw [Subgroup.mem_center_iff]
    intro u
    obtain ⟨v, rfl⟩ := eH.surjective u
    simpa only [map_mul] using congrArg eH (Subgroup.mem_center_iff.mp hz v)
  · rw [← map_pow, hzp, map_one]

private theorem tau_pow_eq_one_s6chn {S : Type} [Group S] {p : ℕ}
    (τ : Multiplicative (Fin 3 → ZMod p) →* S) : ∀ t, τ t ^ p = 1 := by
  intro t
  rw [← map_pow]
  have ht : t ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    change p • t.toAdd = 0
    funext i
    change p • t.toAdd i = 0
    simp [nsmul_eq_mul]
  rw [ht, map_one]

private theorem isSplitTorus_s6chn {F : Type} [Field F] {a p : ℕ}
    {h : UnitaryFieldData 2 a F}
    {ζ : F} {τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0}
    (hτ : ∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) F) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) F) = diagonal (hypEntries ζ t)) :
    SuSplitRootGen.IsSplitTorus h ζ τ := by
  intro t
  rw [hτ]
  congr 1
  funext idx
  rcases idx with i | k | i
  · rfl
  · exact k.elim0
  · rfl

private theorem eq_of_conj_eq_s6chn {S G : Type} [Group S] [Group G] [Group.IsPerfect S]
    {p : ℕ} {Bs : Subgroup G} {D : (Fin 3 → Multiplicative (ZMod p)) →* S}
    {κ : S →* G} (hZ : ∀ z ∈ Subgroup.center S, z ^ p = 1 → z = 1)
    (hκ : κ.ker ≤ Subgroup.center S) (hDp : ∀ f, D f ^ p = 1)
    {T : ↥Bs →* (Fin 3 → Multiplicative (ZMod p))}
    (hTD : ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
      κ (D (T b) * u * (D (T b))⁻¹))
    {u : S} {φ : MulAut ↥Bs}
    (hg : ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = κ u * (b : G) * (κ u)⁻¹) (b : ↥Bs) :
    u * D (T b) * u⁻¹ = D (T (φ b)) := by
  have hhom : (MulAut.conj (u * D (T b) * u⁻¹)).toMonoidHom =
      (MulAut.conj (D (T (φ b)))).toMonoidHom := by
    refine CFSG.ClassicalInvolution.ModelFacts.UnitaryAut.hom_eq_of_central_ker_perfect
      hκ _ _ fun s => ?_
    change κ ((u * D (T b) * u⁻¹) * s * (u * D (T b) * u⁻¹)⁻¹) =
      κ (D (T (φ b)) * s * (D (T (φ b)))⁻¹)
    have hu : (u * D (T b) * u⁻¹) * s * (u * D (T b) * u⁻¹)⁻¹ =
        u * (D (T b) * (u⁻¹ * s * u) * (D (T b))⁻¹) * u⁻¹ := by group
    rw [hu]
    conv_lhs => rw [map_mul, map_mul, map_inv]
    rw [← hTD b (u⁻¹ * s * u)]
    calc κ u * ((b : G) * κ (u⁻¹ * s * u) * (b : G)⁻¹) * (κ u)⁻¹
        = (φ b : G) * κ s * (φ b : G)⁻¹ := by
            rw [map_mul, map_mul, map_inv, hg b]
            group
      _ = κ (D (T (φ b)) * s * (D (T (φ b)))⁻¹) := hTD (φ b) s
  exact FrameBs.eq_of_conj_eq_of_center_prime hZ
    (by rw [conj_pow, hDp, mul_one, mul_inv_cancel]) (hDp (T (φ b)))
    (MulEquiv.ext fun s => DFunLike.congr_fun hhom s)

private theorem ker_le_center_comp_mulEquiv_s6chn {H X P : Type*} [Group H] [Group X] [Group P]
    (e : H ≃* X) {φ : X →* P} (hφ : φ.ker ≤ Subgroup.center X) :
    (φ.comp e.toMonoidHom).ker ≤ Subgroup.center H := by
  intro z hz
  have hzc : e z ∈ Subgroup.center X := hφ hz
  rw [Subgroup.mem_center_iff] at hzc ⊢
  intro y
  apply e.injective
  rw [map_mul, map_mul]
  exact hzc (e y)

theorem ggSecFiveBPermSUK_signedPerm_of_mem_automizer
    {G F : Type} [Group G] [Field F] [Finite F] [CharP F 2] {p a : ℕ}
    (hF : Nat.card F = (2 ^ a) ^ 2) (h : UnitaryFieldData 2 a F)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ 2 ^ a - 1)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0}
    (hτ : ∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) F) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) F) = diagonal (hypEntries ζ t))
    {Bs K : Subgroup G} {κ : hypSU h 3 0 →* G} (hκ : κ.ker ≤ Subgroup.center (hypSU h 3 0))
    (hκK : κ.range = K) (T : ↥Bs →* (Fin 3 → Multiplicative (ZMod p)))
    (hTs : Function.Surjective T)
    (hT : ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
      κ (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) * u *
        (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)))⁻¹))
    {φ : MulAut ↥Bs} (hφ : φ ∈ ggAutomizer K Bs) :
    ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ (b : ↥Bs) i, toAdd (T (φ b) (π i)) = ε i * toAdd (T b i) := by
  let eH : hypSU h 3 0 ≃* SU (unitaryInvolution F 2 a) 6 :=
    SuSplitRootGen.hypSUEquiv h (by decide)
  have : Group.IsPerfect (hypSU h 3 0) :=
    (isQuasisimple_of_mulEquiv eH.symm
      (isQuasisimple_SU (p := 2) (f := a) (n := 6) hF (by norm_num) (by simp))).1
  have hZ : ∀ z ∈ Subgroup.center (hypSU h 3 0), z ^ p = 1 → z = 1 :=
    fun _ hz hzp => hypSU_eq_one_of_mem_center_of_pow_eq_one hF h hp hp2 hpq hz hzp
  have hτp := tau_pow_eq_one_s6chn τ
  let eP := MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)
  let D : (Fin 3 → Multiplicative (ZMod p)) →* hypSU h 3 0 :=
    τ.comp eP.symm.toMonoidHom
  have hDp (f : Fin 3 → Multiplicative (ZMod p)) : D f ^ p = 1 := hτp _
  have hTD : ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
      κ (D (T b) * u * (D (T b))⁻¹) := hT
  have hP (f : Fin 3 → Multiplicative (ZMod p)) :
      eP.symm f = ofAdd (fun i => toAdd (f i)) := rfl
  obtain ⟨g, hgK, -, hg⟩ := mem_ggAutomizer_iff.mp hφ
  rw [← hκK] at hgK
  obtain ⟨u, rfl⟩ := MonoidHom.mem_range.mp hgK
  have hkey : ∀ b : ↥Bs, u * D (T b) * u⁻¹ = D (T (φ b)) :=
    fun b => eq_of_conj_eq_s6chn hZ hκ hDp hTD hg b
  have hτsplit : SuSplitRootGen.IsSplitTorus h ζ τ := isSplitTorus_s6chn hτ
  obtain ⟨π, ε, hε, hπ⟩ := RealKGUSplit.exists_signedPerm_of_normalizer h hp hζ hτsplit u
    (fun t => by
      obtain ⟨b, hb⟩ := hTs (fun i => ofAdd (t i))
      refine ⟨fun i => toAdd (T (φ b) i), ?_⟩
      simpa [D, hP, hb] using hkey b)
  refine ⟨π, ε, hε, fun b i => ?_⟩
  apply hπ (fun i => toAdd (T b i)) (fun i => toAdd (T (φ b) i)) _ i
  simpa [D, hP] using hkey b

private theorem kernel_comp_symm_apply_eq_one {G : Type} [Group G] {p n : ℕ} [Fact p.Prime]
    {Bs K : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {i0 : Fin n}
    {T : ↥Bs →* (Fin 3 → Multiplicative (ZMod p))} (hp2 : p ≠ 2)
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    (hker : T.ker.map Bs.subtype = Bs ⊓ Subgroup.centralizer (K : Set G)) :
    ∀ x, T (eta.symm x) = 1 → ∀ j, j ≠ i0 → x j = 1 := by
  intro x hx j hj
  have hb : (eta.symm x : G) ∈ Subgroup.centralizer (K : Set G) := by
    have hmem : (eta.symm x : G) ∈ T.ker.map Bs.subtype :=
      ⟨eta.symm x, MonoidHom.mem_ker.mpr hx, rfl⟩
    rw [hker] at hmem
    exact hmem.2
  have hh := ggSecFiveBPermSpK_eta_eq_one_of_mem_centralizer hp2 hA hb hj
  simpa only [eta.apply_symm_apply] using hh

private theorem signedPerm_comp_symm_of_mem_bCoordinateBlock
    {G F : Type} [Group G] [Field F] [Finite F] [CharP F 2] {p a : ℕ}
    (hF : Nat.card F = (2 ^ a) ^ 2) (h : UnitaryFieldData 2 a F)
    (hp : p.Prime) (hp2 : p ≠ 2) (hpa : p ∣ 2 ^ a - 1)
    {ζ : F} (hζ : IsPrimitiveRoot ζ p)
    {τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0}
    (hτ : ∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) F) :
      Matrix (HypIndex 3 0) (HypIndex 3 0) F) = diagonal (hypEntries ζ t))
    {Bs K : Subgroup G} {κ : hypSU h 3 0 →* G}
    (hκ : κ.ker ≤ Subgroup.center (hypSU h 3 0)) (hκK : κ.range = K)
    (T : ↥Bs →* (Fin 3 → Multiplicative (ZMod p)))
    (hTs : Function.Surjective T)
    (hT : ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
      κ (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)) * u *
        (τ ((MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)).symm (T b)))⁻¹))
    {eta : ↥Bs ≃* (Fin 4 → Multiplicative (ZMod p))} {i0 : Fin 4}
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock 4 p i0) :
    ∀ w ∈ bCoordinateBlock 4 p i0, ∃ (π : Equiv.Perm (Fin 3)) (ε : Fin 3 → ZMod p),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ x i, toAdd ((T.comp eta.symm.toMonoidHom) (w x) (π i)) =
        ε i * toAdd ((T.comp eta.symm.toMonoidHom) x i) := by
  intro w hw
  rw [← hA] at hw
  obtain ⟨φ, hφ, hφeq⟩ := Subgroup.mem_map.mp hw
  obtain ⟨π, ε, hε, hπ⟩ := ggSecFiveBPermSUK_signedPerm_of_mem_automizer
    hF h hp hp2 hpa hζ hτ hκ hκK T hTs hT hφ
  refine ⟨π, ε, hε, fun x i => ?_⟩
  have hwapply : w x = eta (φ (eta.symm x)) := by
    rw [← hφeq]
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  change toAdd (T (eta.symm (w x)) (π i)) = ε i * toAdd (T (eta.symm x) i)
  rw [hwapply, eta.symm_apply_apply]
  exact hπ (eta.symm x) i

private theorem exists_units_of_coord_sign {p : ℕ} {ε : Fin 3 → ZMod p}
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ∃ εu : Fin 3 → (ZMod p)ˣ, (∀ i, (εu i : ZMod p) = ε i) ∧
      ∀ i, εu i ∈ Subgroup.zpowers (-1 : (ZMod p)ˣ) := by
  refine ⟨fun i => if ε i = 1 then 1 else -1, ?_, ?_⟩
  · intro i
    dsimp only
    by_cases hi : ε i = 1
    · rw [if_pos hi]
      simpa using hi.symm
    · rw [if_neg hi]
      have he := (hε i).resolve_left hi
      rw [he]
      rfl
  · intro i
    dsimp only
    by_cases hi : ε i = 1
    · simp only [if_pos hi]
      exact Subgroup.one_mem _
    · simp only [if_neg hi]
      exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩

private theorem conj_torus_eq_of_coord {H : Type} [Group H] {p : ℕ}
    {τ : Multiplicative (Fin 3 → ZMod p) →* H} {w : H}
    {t : Fin 3 → Multiplicative (ZMod p)} {εu : Fin 3 → (ZMod p)ˣ} {ε : Fin 3 → ZMod p}
    {c : ZMod p} {r : Fin 3 → ZMod p}
    (hw : ∀ s : Fin 3 → ZMod p,
      w⁻¹ * τ (ofAdd s) * w = τ (ofAdd fun i => (εu i : ZMod p) * s i))
    (hεu : ∀ i, (εu i : ZMod p) = ε i) (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (hcoord : ∀ i, toAdd (t i) = ε i * c * r i) :
    w⁻¹ * τ (ofAdd fun i => toAdd (t i)) * w = τ (ofAdd fun i => c * r i) := by
  rw [hw]
  congr 1
  funext i
  change (εu i : ZMod p) * toAdd (t i) = c * r i
  rw [hεu, hcoord]
  calc ε i * (ε i * c * r i) = (ε i * ε i) * (c * r i) := by ring
    _ = c * r i := by rw [SpCoord.coord_sign_mul_self (hε i), one_mul]

private theorem exists_conj_chart_calibrated {G F : Type} [Group G] [Field F] [Finite F]
    [CharP F 2] {a p : ℕ} {h : UnitaryFieldData 2 a F} {K : Subgroup G}
    {ψ₀ : SU (unitaryInvolution F 2 a) 6 →* G}
    {τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0}
    {κ : hypSU h 3 0 →* G} {w : hypSU h 3 0}
    {Bs : Subgroup G} {t : ↥Bs → Multiplicative (Fin 3 → ZMod p)}
    {r : ↥Bs → Fin 3 → ZMod p} {c : ZMod p}
    (hκker : κ.ker ≤ Subgroup.center (hypSU h 3 0)) (hκK : κ.range = K)
    (hκrep : ∃ k : SU (unitaryInvolution F 2 a) 6,
      κ = (ψ₀.comp (MulAut.conj k).toMonoidHom).comp
        (SuSplitRootGen.hypSUEquiv h (by decide)).toMonoidHom)
    (hT : ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ = κ (τ (t b) * u * (τ (t b))⁻¹))
    (htor : ∀ b : ↥Bs, w⁻¹ * τ (t b) * w = τ (ofAdd (fun i => c * r b i))) :
    ∃ κ' : hypSU h 3 0 →* G, κ'.ker ≤ Subgroup.center (hypSU h 3 0) ∧ κ'.range = K ∧
      (∃ k : SU (unitaryInvolution F 2 a) 6,
        κ' = (ψ₀.comp (MulAut.conj k).toMonoidHom).comp
          (SuSplitRootGen.hypSUEquiv h (by decide)).toMonoidHom) ∧
      ∀ (b : ↥Bs) u, (b : G) * κ' u * (b : G)⁻¹ =
        κ' (τ (ofAdd (fun i => c * r b i)) * u * (τ (ofAdd (fun i => c * r b i)))⁻¹) := by
  let κ' : hypSU h 3 0 →* G := κ.comp (MulAut.conj w).toMonoidHom
  have hκ'ker : κ'.ker ≤ Subgroup.center (hypSU h 3 0) :=
    ker_le_center_comp_mulEquiv_s6chn (MulAut.conj w) hκker
  have hκ'K : κ'.range = K := by
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 (MulAut.conj w).surjective,
      Subgroup.map_top]
    exact hκK
  refine ⟨κ', hκ'ker, hκ'K, ?_, ?_⟩
  · obtain ⟨k, hk⟩ := hκrep
    let eH : hypSU h 3 0 ≃* SU (unitaryInvolution F 2 a) 6 :=
      SuSplitRootGen.hypSUEquiv h (by decide)
    refine ⟨k * eH w, ?_⟩
    ext u
    change κ (w * u * w⁻¹) = _
    rw [hk]
    change ψ₀ (k * eH (w * u * w⁻¹) * k⁻¹) =
      ψ₀ ((k * eH w) * eH u * (k * eH w)⁻¹)
    apply congrArg ψ₀
    simp only [map_mul, map_inv]
    group
  · intro b u
    change (b : G) * κ (w * u * w⁻¹) * (b : G)⁻¹ =
      κ (w * (τ (ofAdd (fun i => c * r b i)) * u *
        (τ (ofAdd (fun i => c * r b i)))⁻¹) * w⁻¹)
    rw [hT, ← htor]
    apply congrArg κ
    group


theorem ggSecFiveBPermSU_exists_calibrated_frame_of_centralImage {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hMp : GGInnerDiagMpInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n a : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G} {i0 : Fin n}
    (hn : n = 4) (ha : 2 ≤ a) (hpa : p ∣ 2 ^ a - 1) (hK : K ∈ 𝒦)
    (hA : (ggAutomizer K Bs).map (MulAut.congr eta).toMonoidHom = bCoordinateBlock n p i0)
    {ψ₀ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G}
    (hker : ψ₀.ker ≤ Subgroup.center (SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6))
    (hrange : ψ₀.range = K) :
    ∃ h : UnitaryFieldData 2 a (GaloisField 2 (2 * a)),
      ∃ ζ : GaloisField 2 (2 * a), IsPrimitiveRoot ζ p ∧ h.bar ζ = ζ ∧
      ∃ τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0,
        (∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) (GaloisField 2 (2 * a))) :
          Matrix (HypIndex 3 0) (HypIndex 3 0) (GaloisField 2 (2 * a))) =
            diagonal (hypEntries ζ t)) ∧
      ∃ π : Fin 4 ≃ Fin n, π 0 = i0 ∧ ∃ c : ZMod p, c ≠ 0 ∧
      ∃ κ : hypSU h 3 0 →* G,
        κ.ker ≤ Subgroup.center (hypSU h 3 0) ∧ κ.range = K ∧
        (∃ k : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6,
          κ = (ψ₀.comp (MulAut.conj k).toMonoidHom).comp
            (SuSplitRootGen.hypSUEquiv h (by decide)).toMonoidHom) ∧
        ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
          κ (τ (ofAdd (fun i => c * toAdd (eta b (π i.succ)))) * u *
            (τ (ofAdd (fun i => c * toAdd (eta b (π i.succ)))))⁻¹) := by
  obtain rfl := hn
  obtain ⟨hp, hp2⟩ := ggRouteCfg_prime hR
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨h, ζ, hζ, hbar, τ, hτ, κ, hκrep, hκker, hκK, T, hTs, hkerEq, hT⟩ :=
    ggSecFiveBPermSU_exists_toralHom_of_centralImage hMp hR eta rfl ha hpa hK hA hker hrange
  have hF := card_galoisField_two_mul 2 a (by omega)
  let eP := MulEquiv.piMultiplicative (fun _ : Fin 3 => ZMod p)
  let T' := T.comp eta.symm.toMonoidHom
  have hT's : Function.Surjective T' := hTs.comp eta.symm.surjective
  have hker' : ∀ x, T' x = 1 → ∀ j, j ≠ i0 → x j = 1 :=
    kernel_comp_symm_apply_eq_one (T := T) hp2 hA hkerEq
  have hW := signedPerm_comp_symm_of_mem_bCoordinateBlock hF h hp hp2 hpa hζ hτ hκker hκK
    T hTs hT hA
  obtain ⟨π, hπ0, c, hc0, ε, hε, halign⟩ :=
    ggSecFiveBPermSpK_exists_align hp2 (by decide) T' hT's hker' hW
  have hcoord : ∀ (b : ↥Bs) i, toAdd (T b i) = ε i * c * toAdd (eta b (π i.succ)) := by
    intro b i
    simpa only [T', MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      eta.symm_apply_apply] using halign (eta b) i
  obtain ⟨εu, hεu, hεup⟩ := exists_units_of_coord_sign hε
  obtain ⟨w, -, hw⟩ := exists_hypTorus_move h hp hp2 hζ hbar τ hτ (Equiv.refl _) εu hεup
  have htor : ∀ b : ↥Bs, w⁻¹ * τ (eP.symm (T b)) * w =
      τ (ofAdd (fun i => c * toAdd (eta b (π i.succ)))) := by
    intro b
    change w⁻¹ * τ (ofAdd (fun i => toAdd (T b i))) * w =
      τ (ofAdd (fun i => c * toAdd (eta b (π i.succ))))
    exact conj_torus_eq_of_coord (t := T b) hw hεu hε (hcoord b)
  obtain ⟨κ', hκ'ker, hκ'K, hκ'rep, hκ'act⟩ :=
    exists_conj_chart_calibrated (F := GaloisField 2 (2 * a))
      (t := fun b => eP.symm (T b)) (r := fun b i => toAdd (eta b (π i.succ)))
      hκker hκK hκrep hT htor
  exact ⟨h, ζ, hζ, hbar, τ, hτ, π, hπ0, c, hc0, κ', hκ'ker, hκ'K, hκ'rep, hκ'act⟩

theorem ggSecFiveBPermSU_exists_calibrated_frame {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)}
    (hMp : GGInnerDiagMpInput)
    (hR : GGSecFiveRouteCfg p B Bs x L D J 𝒦) {n a : ℕ}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {K : Subgroup G} {i0 : Fin n}
    (hc : GGSecFiveBPermSUCell p Bs L 𝒦 n eta a K i0) :
    ∃ h : UnitaryFieldData 2 a (GaloisField 2 (2 * a)),
      ∃ ζ : GaloisField 2 (2 * a), IsPrimitiveRoot ζ p ∧ h.bar ζ = ζ ∧
      ∃ τ : Multiplicative (Fin 3 → ZMod p) →* hypSU h 3 0,
        (∀ t, (((τ (ofAdd t) : hypSU h 3 0) : GL (HypIndex 3 0) (GaloisField 2 (2 * a))) :
          Matrix (HypIndex 3 0) (HypIndex 3 0) (GaloisField 2 (2 * a))) =
            diagonal (hypEntries ζ t)) ∧
      ∃ π : Fin 4 ≃ Fin n, π 0 = i0 ∧ ∃ c : ZMod p, c ≠ 0 ∧
      ∃ κ : hypSU h 3 0 →* G,
        Function.Injective κ ∧ κ.range = K ∧
        (∃ (eK : ↥K ≃* SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6)
          (k : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6),
          κ = ((K.subtype.comp eK.symm.toMonoidHom).comp (MulAut.conj k).toMonoidHom).comp
            (SuSplitRootGen.hypSUEquiv h (by decide)).toMonoidHom) ∧
        ∀ (b : ↥Bs) u, (b : G) * κ u * (b : G)⁻¹ =
          κ (τ (ofAdd (fun i => c * toAdd (eta b (π i.succ)))) * u *
            (τ (ofAdd (fun i => c * toAdd (eta b (π i.succ)))))⁻¹) := by
  obtain ⟨eK⟩ := hc.2.2.2.2.2.1
  let ψ₀ : SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6 →* G :=
    K.subtype.comp eK.symm.toMonoidHom
  have hψ₀ : Function.Injective ψ₀ := K.subtype_injective.comp eK.symm.injective
  have hker : ψ₀.ker ≤ Subgroup.center
      (SU (unitaryInvolution (GaloisField 2 (2 * a)) 2 a) 6) := by
    rw [(MonoidHom.ker_eq_bot_iff ψ₀).mpr hψ₀]
    exact bot_le
  have hrange : ψ₀.range = K := by
    change (K.subtype.comp eK.symm.toMonoidHom).range = K
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.2 eK.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  obtain ⟨h, ζ, hζ, hbar, τ, hτ, π, hπ0, c, hc0, κ, -, hκK, hκrep, hκact⟩ :=
    ggSecFiveBPermSU_exists_calibrated_frame_of_centralImage hMp hR eta hc.1 hc.2.1 hc.2.2.1
      hc.2.2.2.1 hc.2.2.2.2.2.2 hker hrange
  obtain ⟨k, hk⟩ := hκrep
  have hκinj : Function.Injective κ := by
    rw [hk]
    exact (hψ₀.comp (MulAut.conj k).injective).comp
      (SuSplitRootGen.hypSUEquiv h (by decide)).injective
  exact ⟨h, ζ, hζ, hbar, τ, hτ, π, hπ0, c, hc0, κ, hκinj, hκK,
    ⟨eK, k, hk⟩, hκact⟩

end CFSG.StandardType

end
