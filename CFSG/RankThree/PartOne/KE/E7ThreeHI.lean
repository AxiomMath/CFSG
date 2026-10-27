module

public import CFSG.RankThree.PartOne.KE.E7ThreePerX
public import CFSG.RankThree.PartOne.KE.E7FourHI

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.LocalRank
open CFSG.RankThree.PartOne CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix Pointwise MatrixGroups

section Y

variable {K : Type} [Field K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L]

@[expose] def e7ThreeY (g0 : ModGL .E7 L) (cK uK : ModGL .E7 K) : ModGL .E7 L :=
  g0⁻¹ * baseChangeGL (algebraMap K L) (cK * uK * cK⁻¹) * g0

theorem e7ThreeY_mem {g0 : ModGL .E7 L} (hg0C : g0 ∈ adjointGroup .E7 L)
    {cK gK : ModGL .E7 K} (hc : cK ∈ adjointGroup .E7 K) (hg : gK ∈ adjointGroup .E7 K)
    (a : Fin Tag.E7.rank → Kˣ) :
    e7ThreeY g0 cK (gK * rootDiagUnit .E7 a) ∈ adjointGroup .E7 L := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hc' : baseChangeGL (algebraMap K L) cK ∈ adjointGroup .E7 L :=
    adjEmb_mem (⟨cK, hc⟩ : adjointGroup .E7 K)
  have hg' : baseChangeGL (algebraMap K L) gK ∈ adjointGroup .E7 L :=
    adjEmb_mem (⟨gK, hg⟩ : adjointGroup .E7 K)
  have hd : baseChangeGL (algebraMap K L) (rootDiagUnit .E7 a) ∈ adjointGroup .E7 L := by
    rw [baseChangeGL_rootDiagUnit]
    exact torusGroup_le_adjointGroup' (rootDiagUnit_mem_torusGroup _)
  unfold e7ThreeY
  rw [map_mul, map_mul, map_mul, map_inv]
  exact mul_mem (mul_mem (inv_mem hg0C) (mul_mem (mul_mem hc' (mul_mem hg' hd)) (inv_mem hc')))
    hg0C

omit [IsAlgClosure K L] in
theorem e7ThreeY_fixed [Finite K] {Fr : L →+* L} (hFr : ∀ c, Fr c = c ^ Nat.card K)
    {n g0 : ModGL .E7 L} (hg0 : Units.map (entrywiseHom Fr) g0 = g0 * n) (cK uK : ModGL .E7 K) :
    n * Units.map (entrywiseHom Fr) (e7ThreeY g0 cK uK) * n⁻¹ = e7ThreeY g0 cK uK := by
  have hfix := baseChangeGL_frobenius_fixed (τ := .E7) (K := K) (L := L) Fr hFr
    (cK * uK * cK⁻¹)
  unfold e7ThreeY
  rw [map_mul, map_mul, map_inv, hfix, hg0]
  group

omit [IsAlgClosure K L] in
theorem e7ThreeY_commute {g0 : ModGL .E7 L} {cK uK kK : ModGL .E7 K}
    (hk : uK * kK = kK * uK) :
    e7ThreeY g0 cK uK * (g0⁻¹ * baseChangeGL (algebraMap K L) (cK * kK * cK⁻¹) * g0) =
      (g0⁻¹ * baseChangeGL (algebraMap K L) (cK * kK * cK⁻¹) * g0) * e7ThreeY g0 cK uK := by
  have h1 : cK * uK * cK⁻¹ * (cK * kK * cK⁻¹) = (cK * kK * cK⁻¹) * (cK * uK * cK⁻¹) := by
    calc _ = cK * (uK * kK) * cK⁻¹ := by group
      _ = cK * (kK * uK) * cK⁻¹ := by rw [hk]
      _ = _ := by group
  have h2 : baseChangeGL (algebraMap K L) (cK * uK * cK⁻¹) *
      baseChangeGL (algebraMap K L) (cK * kK * cK⁻¹) =
      baseChangeGL (algebraMap K L) (cK * kK * cK⁻¹) *
        baseChangeGL (algebraMap K L) (cK * uK * cK⁻¹) := by
    rw [← map_mul, ← map_mul, h1]
  unfold e7ThreeY
  calc g0⁻¹ * baseChangeGL (algebraMap K L) (cK * uK * cK⁻¹) * g0 *
        (g0⁻¹ * baseChangeGL (algebraMap K L) (cK * kK * cK⁻¹) * g0)
      = g0⁻¹ * (baseChangeGL (algebraMap K L) (cK * uK * cK⁻¹) *
          baseChangeGL (algebraMap K L) (cK * kK * cK⁻¹)) * g0 := by group
    _ = g0⁻¹ * (baseChangeGL (algebraMap K L) (cK * kK * cK⁻¹) *
          baseChangeGL (algebraMap K L) (cK * uK * cK⁻¹)) * g0 := by rw [h2]
    _ = _ := by group

omit [IsAlgClosure K L] in
theorem e7ThreeY_eq_one {g0 : ModGL .E7 L} {cK uK : ModGL .E7 K}
    (h : e7ThreeY g0 cK uK = 1) : uK = 1 := by
  unfold e7ThreeY at h
  have h1 : baseChangeGL (algebraMap K L) (cK * uK * cK⁻¹) = 1 := by
    have := congrArg (fun z => g0 * z * g0⁻¹) h
    simpa [mul_assoc] using this
  have h2 : cK * uK * cK⁻¹ = 1 :=
    baseChangeGL_injective (algebraMap K L) (by rw [h1, map_one])
  have := congrArg (fun z => cK⁻¹ * z * cK) h2
  simpa [mul_assoc] using this

end Y

section HI

variable {K : Type} [Field K] [Finite K] {ℓ f : ℕ} [Fact ℓ.Prime] {p : ℕ}
  {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ] {ε : ℤ}

omit [Finite K] [IsAlgClosure K L] [CharP L ℓ] [Fact ℓ.Prime] in
theorem e7ThreeY_commute_adjEmb {g0 : ModGL .E7 L} (c k : adjointGroup .E7 K)
    {uK : ModGL .E7 K} (hk : uK * (k : ModGL .E7 K) = (k : ModGL .E7 K) * uK) :
    e7ThreeY g0 (c : ModGL .E7 K) uK * (g0⁻¹ * adjEmb .E7 K L (c * k * c⁻¹) * g0) =
      (g0⁻¹ * adjEmb .E7 K L (c * k * c⁻¹) * g0) * e7ThreeY g0 (c : ModGL .E7 K) uK := by
  have e : adjEmb .E7 K L (c * k * c⁻¹) = baseChangeGL (algebraMap K L)
      ((c : ModGL .E7 K) * (k : ModGL .E7 K) * (c : ModGL .E7 K)⁻¹) := by
    rw [adjEmb_apply]
    rfl
  rw [e]
  exact e7ThreeY_commute hk

theorem e7_three_hI (hLay : E7ThreeLayers) (F : E7ThreeFrame K L ℓ f p ε) (hf : 1 ≤ f)
    (hK : Nat.card K = ℓ ^ f) (hp : p.Prime) (hp3 : 3 < p) (hε : ε = 1 ∨ ε = -1)
    (hpf : (p : ℤ) ∣ (Nat.card K : ℤ) ^ 2 + ε * (Nat.card K : ℤ) + 1)
    (hstab : E7StabHyp F.n (iterateFrobenius L ℓ f) p) :
    ∀ B : Subgroup (MulAut (adjointGroup .E7 K)),
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range ≤ B →
      ∀ A : Subgroup (MulAut (adjointGroup .E7 K)), A ≤ B → IsElementaryAbelian p A →
        Nat.card A = p ^ 2 →
        A ≤ (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)).range →
        Odd (Nat.card ↥(autThetaT p B A)) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFr : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK]
    exact iterateFrobenius_def ℓ f c
  intro B hB A hAB hA hcard hAin
  have hC : Subgroup.center (adjointGroup .E7 K) = ⊥ := center_adjointGroup_eq_bot
  have hIntinj : Function.Injective
      (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) :=
    conj_injective_of_center_eq_bot hC
  set A₀ : Subgroup (adjointGroup .E7 K) :=
    A.comap (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) with hA₀
  have hA₀map : A₀.map (MulAut.conj : adjointGroup .E7 K →* MulAut (adjointGroup .E7 K)) = A := by
    rw [hA₀, Subgroup.map_comap_eq]
    exact inf_of_le_right hAin
  have hA₀card : Nat.card A₀ = p ^ 2 := by
    rw [← Subgroup.card_map_of_injective hIntinj, hA₀map, hcard]
  have hpg : IsPGroup p A₀ := IsPGroup.of_card hA₀card
  obtain ⟨c, hc⟩ := F.hconj A₀ hpg
  have hpow : ∀ a ∈ A, a ^ p = 1 := fun a ha =>
    elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) a ha
  have hA₀exp : ∀ q ∈ A₀, q ^ p = 1 := fun q hq => by
    apply hIntinj
    rw [map_pow, map_one]
    exact hpow _ hq
  let φ : A₀ →* ModGL .E7 L := (MulAut.conj F.g0⁻¹).toMonoidHom.comp
    ((adjEmb .E7 K L).comp ((MulAut.conj c).toMonoidHom.comp A₀.subtype))
  have hφ : ∀ q : A₀, φ q =
      F.g0⁻¹ * adjEmb .E7 K L (c * (q : adjointGroup .E7 K) * c⁻¹) * F.g0 := fun q => by
    simp [φ, MulAut.conj_apply]
  have hφinj : Function.Injective φ := by
    intro q q' h
    rw [hφ, hφ] at h
    have h1 := mul_left_cancel (mul_right_cancel h)
    have h2 := adjEmb_injective h1
    have h3 : (q : adjointGroup .E7 K) = q' := by
      have := congrArg (fun z => c⁻¹ * z * c) h2
      simpa [mul_assoc] using this
    exact Subtype.ext h3
  have hφT : ∀ q : A₀, φ q ∈ twistedTorusOf F.n (Units.map (entrywiseHom Fr)) := fun q => by
    rw [hφ]
    exact hc q q.2
  choose β hβ using fun q : A₀ =>
    (exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 (hφT q)).1 :
      ∃ b : Fin Tag.E7.rank → Lˣ, φ q = rootDiagUnit .E7 b)
  have hinj0 : Function.Injective (rootDiagUnitHom .E7 L) := rootDiagUnit_injective
  have hβmul : ∀ q q' : A₀, β (q * q') = β q * β q' := fun q q' => by
    apply rootDiagUnit_injective (τ := .E7) (K := L)
    rw [← hβ, rootDiagUnit_mul, ← hβ, ← hβ, map_mul]
  have hβone : β 1 = 1 := by
    apply rootDiagUnit_injective (τ := .E7) (K := L)
    rw [← hβ, map_one, rootDiagUnit_one]
  have hβfix : ∀ q : A₀, β q ∈ fixedCharTuples (ε • e7T3W) Fr := fun q => by
    have h := hφT q
    rw [F.hT] at h
    obtain ⟨b, hb, hbq⟩ := h
    have : b = β q := hinj0 (hbq.trans (hβ q))
    rw [← this]
    exact hb
  have hβp : ∀ q : A₀, ∀ i, β q i ^ p = 1 := fun q i => by
    have h1 : rootDiagUnit .E7 (β q) ^ p = 1 := by
      rw [← hβ, ← map_pow]
      have : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [this, map_one]
    have h2 : β q ^ p = 1 := by
      apply hinj0
      rw [map_pow, map_one]
      exact h1
    exact congrFun h2 i
  have hβne : ∀ q : A₀, q ≠ 1 → β q ≠ 1 := fun q hq h => by
    apply hq
    apply hφinj
    rw [hβ, h, rootDiagUnit_one, map_one]
  have hroot : ∀ r : {r : Fin Tag.E7.rank → ℤ // IsRoot .E7 r},
      ∃ q : A₀, q ≠ 1 ∧ r.1 ∈ rootCharKernel (β q) := by
    intro r
    let χ : A₀ →* Lˣ :=
      { toFun := fun q => rootChar (β q) r.1
        map_one' := by rw [hβone]; exact CTTorus.rootChar_one r.1
        map_mul' := fun q q' => by rw [hβmul, CTTorus.rootChar_mul] }
    have hχp : ∀ q : A₀, χ q ^ p = 1 := fun q => by
      rw [← map_pow]
      have h3 : q ^ p = 1 := Subtype.ext (hA₀exp q q.2)
      rw [h3, map_one]
    obtain ⟨q₀, hq₀1, hq₀χ⟩ := exists_ne_one_ker_of_card_sq hp hA₀card χ hχp
    exact ⟨q₀, hq₀1, ⟨r.2, hq₀χ⟩⟩
  choose xr hxr1 hxrk using hroot
  have hthetaT_le : ∀ a ∈ A, a ≠ 1 → autThetaT p B A ≤
      inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({a} : Set (MulAut (adjointGroup .E7 K)))) :=
    fun a ha ha1 => by
      refine iInf₂_le_of_le a ha ?_
      exact iInf_le_of_le ha1 le_rfl
  have hxrA : ∀ r, (MulAut.conj (xr r : adjointGroup .E7 K) : MulAut (adjointGroup .E7 K)) ∈ A :=
    fun r => (xr r).2
  have hne1 : ∀ r, (MulAut.conj (xr r : adjointGroup .E7 K) : MulAut (adjointGroup .E7 K)) ≠ 1 :=
    fun r h => (hxr1 r) (Subtype.ext (hIntinj (h.trans (map_one _).symm)))
  have hxrp : ∀ r, orderOf (xr r : adjointGroup .E7 K) = p := fun r =>
    orderOf_eq_prime (hA₀exp _ (xr r).2) (fun h => hxr1 r (Subtype.ext h))
  have hhr : ∀ r, F.g0⁻¹ * adjEmb .E7 K L (c * (xr r : adjointGroup .E7 K) * c⁻¹) * F.g0 ∈
      twistedTorusOf F.n (Units.map (entrywiseHom Fr)) := fun r => hc _ (xr r).2
  have hbhr : ∀ r, rootDiagUnit .E7 (β (xr r)) =
      F.g0⁻¹ * adjEmb .E7 K L (c * (xr r : adjointGroup .E7 K) * c⁻¹) * F.g0 := fun r => by
    rw [← hβ, hφ]
  have hdata := fun r => e7_three_perx hLay F hf hK hp hp3 hε hpf hstab (hxrp r) c (hhr r)
    (hβfix (xr r)) (hβp (xr r)) (hβne (xr r) (hxr1 r)) (hbhr r)
  choose ι' P ψ hfam hψinj hψ hψHQ hψR hψadj hPψ hPnorm hψV hdesc using hdata
  have hbot : autThetaT p B A = ⊥ := by
    rw [eq_bot_iff]
    intro η hη
    have hηj : ∀ r, η ∈ inSubgroup (aschbacherSolvableCore p)
        (B ⊓ Subgroup.centralizer ({(MulAut.conj (xr r : adjointGroup .E7 K) :
          MulAut (adjointGroup .E7 K))} : Set (MulAut (adjointGroup .E7 K)))) :=
      fun r => hthetaT_le _ (hxrA r) (hne1 r) hη
    have hηM : ∀ r, η ∈ B ⊓ Subgroup.centralizer ({(MulAut.conj (xr r : adjointGroup .E7 K) :
        MulAut (adjointGroup .E7 K))} : Set (MulAut (adjointGroup .E7 K))) :=
      fun r => Subgroup.map_subtype_le _ (hηj r)
    have hfix : ∀ r, ∀ i, ∀ k ∈ ((P r i).comap (ψ r)).map
        (Subgroup.centralizer ({(xr r : adjointGroup .E7 K)} :
          Set (adjointGroup .E7 K))).subtype, η k = k := fun r i =>
      core_fixes_of_normal_quasisimple hp hC hB
        (isQuasisimple_map_comap_of_le_range _ (Subgroup.subtype_injective _) (ψ r) (hψinj r)
          (hPψ r i) ((hfam r).2.1 i)) (Subgroup.map_subtype_le _)
        (fun d hd k hk => by
          obtain ⟨k', hk', rfl⟩ := hk
          refine ⟨⟨d, hd⟩ * k' * ⟨d, hd⟩⁻¹, ?_, rfl⟩
          show ψ r (⟨d, hd⟩ * k' * ⟨d, hd⟩⁻¹) ∈ P r i
          rw [map_mul, map_mul, map_inv]
          exact hPnorm r i ⟨d, hd⟩ _ hk') η (hηj r)
    let r₀ : {r : Fin Tag.E7.rank → ℤ // IsRoot .E7 r} := ⟨Pi.single ⟨0, by decide⟩ 1, IsRoot.basis _⟩
    obtain ⟨i₀, m, h₀, hh₀⟩ := hdesc r₀ (hxrk r₀)
    obtain ⟨g, a, hηu⟩ := e7_core_normalForm K L c F.g0 (ψ r₀) (hψ r₀) (hPψ r₀ i₀) m h₀ hh₀ η
      (hfix r₀ i₀)
    set uK : ModGL .E7 K := (g : ModGL .E7 K) * rootDiagUnit .E7 a with huK
    have hcommu : ∀ y : adjointGroup .E7 K, η y = y →
        uK * (y : ModGL .E7 K) = (y : ModGL .E7 K) * uK := by
      intro y hy
      have h1 := hηu y
      rw [hy] at h1
      calc uK * (y : ModGL .E7 K) = (uK * (y : ModGL .E7 K) * uK⁻¹) * uK := by group
        _ = (y : ModGL .E7 K) * uK := by rw [← h1]
    set Y : ModGL .E7 L := e7ThreeY F.g0 (c : ModGL .E7 K) uK with hY
    have hYmem : Y ∈ adjointGroup .E7 L := e7ThreeY_mem F.hg0C c.2 g.2 a
    have hYfix : F.n * Units.map (entrywiseHom Fr) Y * F.n⁻¹ = Y :=
      e7ThreeY_fixed hFr F.hg0 (c : ModGL .E7 K) uK
    have hYcomm : ∀ r, ∀ i, ∀ u ∈ P r i, Y * u = u * Y := by
      intro r i u hu
      obtain ⟨k, hk⟩ := hPψ r i hu
      have hkK : (k : adjointGroup .E7 K) ∈ ((P r i).comap (ψ r)).map
          (Subgroup.centralizer ({(xr r : adjointGroup .E7 K)} :
            Set (adjointGroup .E7 K))).subtype := ⟨k, by
        show ψ r k ∈ P r i
        rw [hk]
        exact hu, rfl⟩
      have h := e7ThreeY_commute_adjEmb (g0 := F.g0) c (k : adjointGroup .E7 K)
        (hcommu _ (hfix r i (k : adjointGroup .E7 K) hkK))
      rw [← hψ r k, hk] at h
      exact h
    have hYsigma : ∀ r, Y ∈ subtorusSigma F.n (Units.map (entrywiseHom Fr))
        (rootCharKernel (β (xr r))) := by
      intro r
      have hηx : η (xr r : adjointGroup .E7 K) = (xr r : adjointGroup .E7 K) := by
        refine fixes_of_commute_conj hC η (xr r : adjointGroup .E7 K) ?_
        have h := Subgroup.mem_centralizer_iff.1 (hηM r).2
          (MulAut.conj (xr r : adjointGroup .E7 K)) rfl
        exact h.symm
      have hcx := e7ThreeY_commute_adjEmb (g0 := F.g0) c (xr r : adjointGroup .E7 K)
        (hcommu _ hηx)
      rw [← hbhr r] at hcx
      have hS : ∀ α ∈ rootCharKernel (β (xr r)), IsRoot .E7 α := fun α hα => hα.1
      have hSn : ∀ α ∈ rootCharKernel (β (xr r)), -α ∈ rootCharKernel (β (xr r)) :=
        fun α hα => ⟨IsRoot.neg hα.1, by rw [rootChar_neg', hα.2, inv_one]⟩
      have hstab' := hstab (β (xr r)) (hβp _) (hβne _ (hxr1 r)) (by rw [← hβ]; exact hφT _)
      have hmul := mem_torus_mul_rootSpan_of_commute_of_stab hstab' hS hSn (fun α hα => hα)
        hYmem hcx
      have hYHQ : Y ∈ torusGroup .E7 L ⊔ rootSpan .E7 L (rootCharKernel (β (xr r))) := by
        rwa [← Subgroup.coe_mul_of_left_le_normalizer_right _ _
          (torusGroup_le_normalizer_rootSpan hS)] at hmul
      obtain ⟨-, -, -, -, -, -, hcent⟩ := hfam r
      exact hcent Y hYHQ hYfix (hYcomm r)
    have hYcent : ∀ α, IsRoot .E7 α → ∀ t : L, pinnedX .E7 L α t * Y = Y * pinnedX .E7 L α t := by
      intro α hα t
      have h := (Subgroup.mem_inf.1 (hYsigma ⟨α, hα⟩)).2
      exact Subgroup.mem_centralizer_iff.1 h _ (pinnedX_mem_rootSpan (hxrk ⟨α, hα⟩) t)
    have hYone : Y = 1 := by
      have hle : adjointGroup .E7 L ≤ Subgroup.centralizer ({Y} : Set (ModGL .E7 L)) := by
        refine (Subgroup.closure_le _).2 ?_
        rintro g ⟨i, t, hg⟩
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        rcases hg with hg | hg
        · have hgx : g = xUnit .E7 L i t := Units.ext hg
          rw [hgx, ← pinnedX_single]
          exact (hYcent (Pi.single i 1) (IsRoot.basis i) t).symm
        · have hgy : g = yUnit .E7 L i t := Units.ext hg
          rw [hgy, ← pinnedX_neg_single]
          exact (hYcent (-Pi.single i 1) (IsRoot.neg (IsRoot.basis i)) t).symm
      have hcen : (⟨Y, hYmem⟩ : adjointGroup .E7 L) ∈ Subgroup.center (adjointGroup .E7 L) := by
        rw [Subgroup.mem_center_iff]
        intro g
        exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hle g.2) Y rfl).symm
      rw [center_adjointGroup_eq_bot_field .E7 L] at hcen
      exact congrArg Subtype.val (Subgroup.mem_bot.1 hcen)
    have hu1 : uK = 1 := e7ThreeY_eq_one hYone
    have hη1 : η = 1 := by
      refine MulEquiv.ext fun y => Subtype.ext ?_
      rw [hηu y, hu1]
      simp
    rw [hη1]
    exact Subgroup.one_mem _
  rw [hbot, Subgroup.card_bot]
  exact odd_one

end HI

end CFSG.RankThree.PartOne.KE
