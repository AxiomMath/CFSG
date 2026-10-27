module

public import CFSG.RankThree.PartOne.KE6.Tw6Core
public import CFSG.RankThree.PartOne.KE.E8FiveData

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.RankThree.E6 CFSG.RankThree.Chevalley
  CFSG.RankThree.GroupTheory CFSG.RankThree.LocalRank CFSG.RankThree.PartOne
  CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.PartOne.KE (twistedTorusOf mem_twistedTorusOf conj_injective_of_center_eq_bot
  exists_ne_one_ker_of_card_sq twE6Emb twE6Emb_injective twE6Emb_mem)
open CFSG.RankThree.PartOne.KE.CTTorus (rootChar_one rootChar_mul rootChar_pow_eq_one)
open CFSG.RankThree.Classical2 (torusRootKernel torusRootKernel_rootDiagUnit twistE6)
open scoped Matrix MatrixGroups Pointwise

theorem e6_tw_six_I_trivial {ℓ f : ℕ} [Fact ℓ.Prime] (K : Type) [Field K] [Finite K]
    [CharP K ℓ] (hf : 1 ≤ f) (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K ≃+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p)
    (hpq : (p : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) ^ 2 - ((ℓ ^ f : ℕ) : ℤ) + 1)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {B : Subgroup (MulAut (twistedE6RootGroup K σ))}
    (hB : (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)).range ≤ B)
    (A : Subgroup (MulAut (twistedE6RootGroup K σ))) (hA : IsElementaryAbelian p A)
    (hcard : Nat.card A = p ^ 2)
    (hAin : A ≤ (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)).range) :
    autThetaT p B A = ⊥ := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Fintype K := Fintype.ofFinite K
  have : Finite (ModGL TwistTag.E6.tag K) := finite_modGL
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hC : Subgroup.center (twistedE6RootGroup K σ) = ⊥ :=
    exceptional_fixed_center_trivial TwistTag.E6 K σ
  have hIntinj : Function.Injective
      (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) :=
    conj_injective_of_center_eq_bot hC
  obtain ⟨g0, hg0C, hg0, hperf, hconj⟩ := tw6_frame K hf hK σ hσ hp hp3 hpq L
  set A₀ : Subgroup (twistedE6RootGroup K σ) :=
    A.comap (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : twistedE6RootGroup K σ →*
      MulAut (twistedE6RootGroup K σ)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c, hc⟩ := hconj A₀ hpg
  have hpow : ∀ e ∈ A₀, e ^ p = 1 := fun e he => by
    have h1 : (MulAut.conj : twistedE6RootGroup K σ →* MulAut (twistedE6RootGroup K σ)) (e ^ p) =
        1 := by
      rw [map_pow]
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) _ he
    exact hIntinj (h1.trans (map_one _).symm)
  let φ : A₀ →* ModGL Tag.E6 L := (MulAut.conj g0⁻¹).toMonoidHom.comp
    ((twE6Emb K σ L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      g0⁻¹ * twE6Emb K σ L (c * (q : twistedE6RootGroup K σ) * c⁻¹) * g0 :=
    fun q => by simp [φ, MulAut.conj_apply]
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf (tw6N L) (twistE6 L Fr) := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E6.rank → Lˣ, φ q = rootDiagUnit Tag.E6 b)
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := Tag.E6) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hinj0 : Function.Injective (rootDiagUnitHom Tag.E6 L) := rootDiagUnit_injective
  have hcover : ∀ α : Fin Tag.E6.rank → ℤ, IsRoot Tag.E6 α →
      ∃ q : A₀, q ≠ 1 ∧ rootChar (β q) α = 1 := by
    intro α hα
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => rootChar (β q) α
        map_one' := by rw [hβone]; exact rootChar_one α
        map_mul' := fun q q' => by rw [hβmul]; exact rootChar_mul _ _ α }
    refine exists_ne_one_ker_of_card_sq hp hA₀card χ fun q => ?_
    have h1 : rootDiagUnit Tag.E6 (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hpow q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact rootChar_pow_eq_one (fun i => congrFun h2 i) α
  have hker : ∀ (q : A₀) (α : Fin Tag.E6.rank → ℤ), IsRoot Tag.E6 α → rootChar (β q) α = 1 →
      α ∈ torusRootKernel (g0⁻¹ * twE6Emb K σ L
        (c * (q : twistedE6RootGroup K σ) * c⁻¹) * g0) :=
    fun q α hα hqα => by
    rw [← hφ q, hβ q, torusRootKernel_rootDiagUnit]
    exact ⟨hα, hqα⟩
  refine (Subgroup.eq_bot_iff_forall _).2 fun η hη => ?_
  have hηθ : ∀ q : A₀, q ≠ 1 → η ∈ inSubgroup (aschbacherSolvableCore p) (B ⊓
      Subgroup.centralizer ({(MulAut.conj (q : twistedE6RootGroup K σ) :
        MulAut (twistedE6RootGroup K σ))} : Set (MulAut (twistedE6RootGroup K σ)))) := by
    intro q hq
    have hIntA : (MulAut.conj (q : twistedE6RootGroup K σ) :
        MulAut (twistedE6RootGroup K σ)) ∈ A := q.2
    have hne : (MulAut.conj (q : twistedE6RootGroup K σ) : MulAut (twistedE6RootGroup K σ)) ≠ 1 :=
      fun h => hq (Subtype.ext (hIntinj (h.trans (map_one _).symm)))
    have hle : autThetaT p B A ≤ inSubgroup (aschbacherSolvableCore p) (B ⊓
        Subgroup.centralizer ({(MulAut.conj (q : twistedE6RootGroup K σ) :
          MulAut (twistedE6RootGroup K σ))} : Set (MulAut (twistedE6RootGroup K σ)))) :=
      iInf₂_le_of_le _ hIntA (iInf_le_of_le hne le_rfl)
    exact hle hη
  have hordq : ∀ q : A₀, q ≠ 1 → orderOf (q : twistedE6RootGroup K σ) = p := fun q hq =>
    orderOf_eq_prime (hpow q q.2) (fun h => hq (Subtype.ext h))
  have hcore := fun (q : A₀) (hq : q ≠ 1) =>
    tw6_perx_core K hf hK σ hσ hp hp3 hpq L hg0C hg0 hperf hB (hordq q hq) c (hc q q.2)
      (hηθ q hq)
  obtain ⟨q₁, hq₁1, hq₁⟩ := hcover (Pi.single ⟨0, by decide⟩ 1)
    (IsRoot.basis ⟨0, by decide⟩)
  have hne₁ : (torusRootKernel (g0⁻¹ * twE6Emb K σ L
      (c * (q₁ : twistedE6RootGroup K σ) * c⁻¹) * g0)).Nonempty :=
    ⟨Pi.single ⟨0, by decide⟩ 1, hker q₁ _ (IsRoot.basis ⟨0, by decide⟩) hq₁⟩
  obtain ⟨N, hN⟩ := (hcore q₁ hq₁1).2 hne₁
  set T : ModGL Tag.E6 L := (twE6Emb K σ L c)⁻¹ * g0 with hT
  have hroots : ∀ α, IsRoot Tag.E6 α → ∀ t : L,
      (T⁻¹ * N * T) * pinnedX Tag.E6 L α t = pinnedX Tag.E6 L α t * (T⁻¹ * N * T) := by
    intro α hα t
    obtain ⟨q, hq1, hqα⟩ := hcover α hα
    exact ((hcore q hq1).1 N hN α (hker q α hα hqα) t).eq
  have hgen : adjointGroup Tag.E6 L ≤
      Subgroup.centralizer ({T⁻¹ * N * T} : Set (ModGL Tag.E6 L)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro y ⟨i, c', hy | hy⟩
    · have hy' : y = pinnedX Tag.E6 L (Pi.single i 1) c' :=
        Units.ext (by rw [pinnedX_single, coe_xUnit]; exact hy)
      rw [hy']
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hroots _ (IsRoot.basis i) c').symm
    · have hy' : y = pinnedX Tag.E6 L (-Pi.single i 1) c' :=
        Units.ext (by rw [pinnedX_neg_single, coe_yUnit]; exact hy)
      rw [hy']
      exact Subgroup.mem_centralizer_singleton_iff.2
        (hroots _ (IsRoot.neg (IsRoot.basis i)) c').symm
  have hηd : ∀ d : twistedE6RootGroup K σ, η d = d := by
    intro d
    apply twE6Emb_injective (K := K) (σ := σ) (L := L)
    rw [hN d]
    have hmem : T⁻¹ * twE6Emb K σ L d * T ∈ adjointGroup Tag.E6 L := by
      have e : T⁻¹ * twE6Emb K σ L d * T = g0⁻¹ * (twE6Emb K σ L c *
          twE6Emb K σ L d * (twE6Emb K σ L c)⁻¹) * g0 := by
        rw [hT]
        group
      rw [e]
      exact mul_mem (mul_mem (inv_mem hg0C) (mul_mem (mul_mem (twE6Emb_mem c) (twE6Emb_mem d))
        (inv_mem (twE6Emb_mem c)))) hg0C
    have hcy := Subgroup.mem_centralizer_singleton_iff.1 (hgen hmem)
    calc N * twE6Emb K σ L d * N⁻¹
        = T * ((T⁻¹ * N * T) * (T⁻¹ * twE6Emb K σ L d * T) * (T⁻¹ * N * T)⁻¹) * T⁻¹ := by
          group
      _ = T * ((T⁻¹ * twE6Emb K σ L d * T) * (T⁻¹ * N * T) * (T⁻¹ * N * T)⁻¹) * T⁻¹ := by
          rw [← hcy]
      _ = twE6Emb K σ L d := by group
  exact MulEquiv.ext hηd

end CFSG.RankThree.PartOne.KE6
