module

public import CFSG.RankThree.PartOne.KLCE.Engine
public import CFSG.RankThree.PartOne.KLCE.FrameConj
public import CFSG.RankThree.PartOne.KLCE.Frob

public noncomputable section

namespace CFSG.RankThree.PartOne.TCX.E

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.LowTwoRank (StatedLieTag)

open CFSG.Blueprint (LieModel)

open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KE
open CFSG.RankThree.PartOne.KLCE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Chevalley (exhaustionPhi)

open scoped MatrixGroups

section LayerData

@[expose] def LieLayerData1 (p : ℕ) {G : Type} [Group G] (α : MulAut G) (X : Subgroup G) : Prop :=
  ∃ Q : Subgroup G, IsComponentOf X Q ∧
    Group.IsSolvable ↥(X ⊓ Subgroup.centralizer (Q : Set G)) ∧
    (Q.subgroupOf X).Normal ∧ Odd (Q.subgroupOf X).index ∧
    ((∀ g ∈ Q, α g ∈ Q) →
      (∀ e ∈ Q, ¬ ∀ g ∈ Q, α g = e * g * e⁻¹) ∧
      (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
        LieModel (↥Q ⧸ Subgroup.center ↥Q) t' n' 2 (p * f')) ∧
      ∃ t₁ ∈ Q, α t₁ = t₁ ∧ ∃ t₂ ∈ Q, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
        (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁)

theorem LieLayerData1.lieLayerData {p : ℕ} {G : Type} [Group G] {α : MulAut G} {X : Subgroup G}
    (h : LieLayerData1 p α X) : KLC.LieLayerData p α X := by
  obtain ⟨Q, hQ, hsolv, hN, hodd, hdata⟩ := h
  refine ⟨Unit, fun _ => Q, ⟨()⟩, fun _ => hQ, ?_, ?_, ?_, fun _ => hdata⟩
  · show Group.IsSolvable ↥(X ⊓ Subgroup.centralizer ((⨆ _ : Unit, Q : Subgroup G) : Set G))
    rw [iSup_const]
    exact hsolv
  · show ((⨆ _ : Unit, Q : Subgroup G).subgroupOf X).Normal
    rw [iSup_const]
    exact hN
  · show Odd ((⨆ _ : Unit, Q : Subgroup G).subgroupOf X).index
    rw [iSup_const]
    exact hodd

@[expose] def LayerDatum2 (p : ℕ) {M : Type} [Group M] (F₀ : M → M) (P : Subgroup M) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (ψ : G →* M), Function.Injective ψ → P ≤ ψ.range →
    ∀ α : MulAut G, α ^ p = 1 → (∀ g, ψ (α g) = F₀ (ψ g)) →
    (∀ g ∈ P.comap ψ, α g ∈ P.comap ψ) →
    (∀ e ∈ P.comap ψ, ¬ ∀ g ∈ P.comap ψ, α g = e * g * e⁻¹) ∧
    (∃ (t' : StatedLieTag) (n' f' : ℕ), 1 ≤ f' ∧
      LieModel (↥(P.comap ψ) ⧸ Subgroup.center ↥(P.comap ψ)) t' n' 2 (p * f')) ∧
    ∃ t₁ ∈ P.comap ψ, α t₁ = t₁ ∧ ∃ t₂ ∈ P.comap ψ, α t₂ = t₂ ∧ (∃ k : ℕ, orderOf t₁ = 2 ^ k) ∧
      (∃ k : ℕ, orderOf t₂ = 2 ^ k) ∧ t₁ * t₂ ≠ t₂ * t₁

@[expose] def OddJoin {M : Type} [Group M] (Γ P : Subgroup M) : Prop :=
  ∀ y ∈ Γ, ∃ m : ℕ, Odd m ∧ y ^ m ∈ P

theorem OddJoin.of_le {M : Type} [Group M] {Γ P : Subgroup M} (h : Γ ≤ P) : OddJoin Γ P :=
  fun y hy => ⟨1, odd_one, by simpa using h hy⟩

end LayerData

section Sector


@[expose] def FrobSector2 (τ : Tag) (e p₀ : ℕ) : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (p f₀ : ℕ), p.Prime → p₀ < p → 1 ≤ f₀ →
    Nat.card K = 2 ^ (p * f₀) → ∀ σ : K ≃+* K, orderOf σ = p → (∀ a, σ a = a ^ 2 ^ f₀) →
    (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
    ∀ x : adjointGroup τ K, x ^ p = 1 → x ≠ 1 → entrywiseAdjointAut τ σ x = x →
      (∀ g ∈ Subgroup.centralizer ({x} : Set (adjointGroup τ K)),
        ∀ h ∈ Subgroup.centralizer ({x} : Set (adjointGroup τ K)), g * h = h * g) ∨
      LieLayerData1 p (entrywiseAdjointAut τ σ)
        (Subgroup.centralizer ({x} : Set (adjointGroup τ K)))

theorem frobSector2_of_families {τ : Tag} {d : ℕ}
    (hτ : (τ = .E6 ∧ d = 3) ∨ (τ = .E7 ∧ d = 2) ∨ (τ = .E8 ∧ d = 1)) {e p₀ : ℕ} (hp₀ : 3 ≤ p₀)
    (𝒮 : Set (Set (Fin τ.rank → ℤ)))
    (h𝒮 : ∀ S ∈ 𝒮, (∀ α ∈ S, IsRoot τ α) ∧ ∀ α ∈ S, -α ∈ S)
    (R : ∀ (L : Type) [Field L], ModGL τ L → Prop)
    (hframe : ∀ (K₀ L : Type) [Field K₀] [Finite K₀] [Field L] [Algebra K₀ L]
      [IsAlgClosure K₀ L] [CharP L 2] (f₀ p : ℕ), 1 ≤ f₀ → Nat.card K₀ = 2 ^ f₀ → p.Prime →
      p₀ < p → (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) →
      ∃ n₀ : ModGL τ L, n₀ ∈ adjointGroup τ L ∧
        Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ ∧ R L n₀ ∧
        (∀ a : Fin τ.rank → Lˣ, (∀ i, a i ^ p = 1) → a ≠ 1 →
          rootDiagUnit τ a ∈ twistedTorusOf (n₀ ^ p)
            (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p)))) →
          rootCharStabilizer a ⊆ (Subgroup.closure
            {s | ∃ α ∈ rootCharKernel a, s = rootReflection α} : Set (WeylGroup τ))) ∧
        ∃ (Z : Subgroup (ModGL τ L)),
          Z ≤ twistedTorusOf n₀ (Units.map (entrywiseHom (iterateFrobenius L 2 f₀))) ∧
        ∃ N₀ : ℕ, N₀ ≠ 0 ∧ Nat.card Z = N₀ ∧
          p ^ (Nat.card (adjointGroup τ K₀)).factorization p = p ^ N₀.factorization p ∧
          (∀ a : Fin τ.rank → Lˣ, rootDiagUnit τ a ∈ Z →
            orderOf (rootDiagUnit τ a) = p → rootCharKernel a = ∅ ∨ rootCharKernel a ∈ 𝒮))
    (hfamily : ∀ (K₀ K L : Type) [Field K₀] [Finite K₀] [Field K] [Finite K] [CharP K 2]
      [Field L] [Algebra K₀ K] [Algebra K L] [Algebra K₀ L] [IsScalarTower K₀ K L]
      [IsAlgClosure K L] [IsAlgClosure K₀ L] [CharP L 2] (f₀ p : ℕ), p.Prime → p₀ < p →
      1 ≤ f₀ → Nat.card K = 2 ^ (p * f₀) → Nat.card K₀ = 2 ^ f₀ →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K : ℤ) →
      (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) → ∀ σ : K ≃+* K,
      orderOf σ = p → (∀ a, σ a = a ^ 2 ^ f₀) → ∀ n₀ : ModGL τ L, n₀ ∈ adjointGroup τ L →
      Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) n₀ = n₀ → R L n₀ →
      ∀ S ∈ 𝒮, ∃ P : Subgroup (ModGL τ L),
        IsSigmaFamily (n₀ ^ p) (iterateFrobenius L 2 (f₀ * p)) S (fun _ : Unit => P) ∧
        OddJoin (rootSpan τ L S ⊓ twistedFixedPoints (n₀ ^ p)
          (Units.map (entrywiseHom (iterateFrobenius L 2 (f₀ * p))))) P ∧
        LayerDatum2 p
          (fun u => n₀ * Units.map (entrywiseHom (iterateFrobenius L 2 f₀)) u * n₀⁻¹) P) :
    FrobSector2 τ e p₀ := by
  intro K _ _ p f₀ hp hp0 hf₀ hK σ hσord hσ hΦ x hxp hx1 hxσ
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hxord : orderOf x = p := orderOf_eq_prime hxp hx1
  have hpf : 1 ≤ p * f₀ := Nat.mul_pos hp.pos hf₀
  have : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hpf hK
  obtain ⟨K₀, _, _, _, hK₀⟩ := exists_subfield_of_frobenius hp hf₀ hK hσord
  let L := AlgebraicClosure K
  have : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  obtain ⟨_, hst, hac⟩ := exists_tower_algebra (K₀ := K₀) (K := K) (L := L)
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  set Φ₀ : L →+* L := iterateFrobenius L 2 f₀ with hΦ₀def
  set Fr : L →+* L := iterateFrobenius L 2 (f₀ * p) with hFrdef
  have hΦ₀K : ∀ c : K, Φ₀ (algebraMap K L c) = algebraMap K L (σ c) := fun c => by
    rw [hΦ₀def, iterateFrobenius_def, ← map_pow, hσ]
  have hFrc : ∀ c, Fr c = c ^ Nat.card K := fun c => by
    rw [hK, mul_comm p f₀]
    exact iterateFrobenius_def 2 (f₀ * p) c
  have hΦK : ∀ u : ModGL τ L, Units.map (entrywiseHom Fr) u =
      (⇑(Units.map (entrywiseHom Φ₀)))^[p] u := units_map_entrywiseHom_iterateFrobenius_mul f₀ p
  have hcard : (Nat.card K : ℤ) = (Nat.card K₀ : ℤ) ^ p := by
    rw [hK, hK₀]
    push_cast
    rw [← pow_mul, mul_comm]
  have hpf₀ : (p : ℤ) ∣ (exhaustionPhi e).eval (Nat.card K₀ : ℤ) :=
    dvd_eval_of_dvd_eval_pow hp (exhaustionPhi e) (by rwa [hcard] at hΦ)
  obtain ⟨n₀, hn₀C, hn₀fix, hRn₀, hstab, Z, hZle, N₀, hN₀, hZcard, hord, hdich⟩ :=
    hframe K₀ L f₀ p hf₀ hK₀ hp hp0 hpf₀
  obtain ⟨g₀, hg₀C, hg₀, hconj⟩ := frame_conj (K₀ := K₀) (K := K) (L := L) hτ
    hf₀ hK₀ hp (by omega) n₀ hn₀C Z hZle hN₀ hZcard hord
  have hxfix : Units.map (entrywiseHom Φ₀) (adjEmb τ K L x) = adjEmb τ K L x := by
    rw [entrywise_adjEmb hΦ₀K x, hxσ]
  obtain ⟨c, hcfix, hcx⟩ := hconj x hxord hxfix
  have hcσ : entrywiseAdjointAut τ σ c = c := by
    apply adjEmb_injective (τ := τ) (K := K) (L := L)
    rw [← entrywise_adjEmb hΦ₀K c]
    exact hcfix
  have hzZ : g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ ∈ Z :=
    (mem_subtorusImage_iff _ _ _ _).1 hcx
  have hzmem : g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ ∈
      twistedTorusOf n₀ (Units.map (entrywiseHom Φ₀)) := hZle hzZ
  obtain ⟨a, ha⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup (mem_twistedTorusOf.1 hzmem).1
  have hzmem' : rootDiagUnit τ a ∈ Z := by
    rw [← ha]
    exact hzZ
  have hord' : orderOf (rootDiagUnit τ a) = p := by
    rw [← ha, ← psiTilde_apply, orderOf_injective (psiTilde τ K L g₀ c)
      (psiTilde_injective g₀ c) x, hxord]
  have hdich' := hdich a hzmem' hord'
  have hinj0 : Function.Injective (rootDiagUnit τ (K := L)) := rootDiagUnit_injective
  have hap : ∀ i, a i ^ p = 1 := pow_eq_one_of_orderOf_rootDiagUnit hord'
  have ha1 : a ≠ 1 := ne_one_of_orderOf_rootDiagUnit hp hord'
  have hg₀N : Units.map (entrywiseHom Fr) g₀ = g₀ * n₀ ^ p := by
    rw [hΦK, iterate_lang (Units.map (entrywiseHom Φ₀)) hn₀fix hg₀ p]
  have hperf : ∀ Y : Subgroup (ModGL τ L), Finite Y → Y ≤ adjointGroup τ L →
      (∀ y ∈ Y, Units.map (entrywiseHom Fr) y = y) → ⁅Y, Y⁆ = Y → Y ≤ (adjEmb τ K L).range :=
    fun Y hY hYC hYF hYp => by
      rw [adjEmb_range]
      exact (finite_fixed_subgroup_rational_perfect (K := K) d hτ Fr hFrc Y hYC
        hYF).2.2 Y le_rfl hYp
  have hzS : ∀ S : Set (Fin τ.rank → ℤ), rootCharKernel a = S →
      g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ ∈
        subtorusSigma (n₀ ^ p) (Units.map (entrywiseHom Fr)) S := by
    intro S hSeq
    have hsub : S ⊆ rootCharKernel a := fun α hα => by rw [hSeq]; exact hα
    have hle := rootSpan_le_centralizer (K := L) a hsub
    refine Subgroup.mem_inf.2 ⟨twistedTorusOf_le_pow hn₀fix p hΦK hzmem, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    have h1 := Subgroup.mem_centralizer_singleton_iff.1 (hle hg)
    rw [← ha] at h1
    exact h1
  have hkerS : ∀ S : Set (Fin τ.rank → ℤ), rootCharKernel a = S → ∀ a' : Fin τ.rank → Lˣ,
      rootDiagUnit τ a' = g₀⁻¹ * adjEmb τ K L (c * x * c⁻¹) * g₀ → rootCharKernel a' ⊆ S := by
    intro S hSeq a' ha'
    have : a' = a := hinj0 (ha'.trans ha)
    rw [this, hSeq]
  have : Finite (ModGL τ K) := finite_modGL
  rcases hdich' with hA | hS
  ·
    left
    have hspan : rootSpan τ L (∅ : Set (Fin τ.rank → ℤ)) = ⊥ := by simp [rootSpan]
    obtain ⟨ψ, hψinj, -, hψHQ, -, -, -, -⟩ := sigma_embedding_data_of_stab (adjEmb τ K L)
      adjEmb_injective (fun y => adjEmb_mem y) (Units.map (entrywiseHom Fr))
      (adjEmb_frobenius Fr hFrc) (n₀ ^ p) g₀ hg₀C hg₀N hperf hp
      (fun a' hap' ha1' hmem => hstab a' hap' ha1' hmem) (S := ∅)
      (fun α hα => hα.elim) (fun α hα => hα.elim) (ι' := Empty) (fun e => e.elim)
      (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim) (fun e => e.elim)
      (fun e => e.elim) (fun y hy hyR _ => by
        rw [hspan, sup_bot_eq] at hy
        refine Subgroup.mem_inf.2 ⟨mem_twistedTorusOf.2 ⟨hy, hyR⟩, ?_⟩
        rw [Subgroup.mem_centralizer_iff]
        intro g hg
        rw [hspan] at hg
        have : g = 1 := hg
        rw [this, one_mul, mul_one])
      hxord c ((mem_subtorusImage_iff _ _ _ _).2 (hzS ∅ hA)) (hkerS ∅ hA)
    intro g hg h hh
    have hψt : ∀ y : Subgroup.centralizer ({x} : Set (adjointGroup τ K)), ψ y ∈ torusGroup τ L :=
      fun y => by
      have := hψHQ y
      rwa [hspan, sup_bot_eq] at this
    have h2 : ψ ⟨g, hg⟩ * ψ ⟨h, hh⟩ = ψ ⟨h, hh⟩ * ψ ⟨g, hg⟩ :=
      KE.torusGroup_comm (hψt ⟨g, hg⟩) (hψt ⟨h, hh⟩)
    have h3 : (⟨g, hg⟩ : Subgroup.centralizer ({x} : Set (adjointGroup τ K))) * ⟨h, hh⟩ =
        ⟨h, hh⟩ * ⟨g, hg⟩ := by
      apply hψinj
      rw [map_mul, map_mul]
      exact h2
    exact congrArg Subtype.val h3
  ·
    right
    obtain ⟨hSroot, hSneg⟩ := h𝒮 _ hS
    obtain ⟨P, hfam, hjoin, hLD⟩ :=
      hfamily K₀ K L f₀ p hp hp0 hf₀ hK hK₀ hΦ hpf₀ σ hσord hσ n₀ hn₀C hn₀fix hRn₀ _ hS
    have hc : c * x * c⁻¹ ∈ subtorusImage (adjEmb τ K L) g₀
        (subtorusSigma (n₀ ^ p) (Units.map (entrywiseHom Fr)) (rootCharKernel a)) :=
      (mem_subtorusImage_iff _ _ _ _).2 (hzS _ rfl)
    obtain ⟨hPrange, hcomp, hsolv, hnormal, hodd⟩ := layerData_structure_odd hp Fr hFrc (n₀ ^ p) g₀
      hg₀C hg₀N hperf hstab hSroot hSneg (fun _ : Unit => P) hfam
      (fun y hy => by simpa only [iSup_const] using hjoin y hy)
      (fun i j hij => absurd (Subsingleton.elim i j) hij) hxord c hc (hkerS _ rfl)
    have hJ : (⨆ i : Unit, layerComp g₀ c (fun _ : Unit => P) i) =
        layerComp g₀ c (fun _ : Unit => P) () :=
      le_antisymm (iSup_le fun i => by cases i; exact le_rfl)
        (le_iSup (layerComp g₀ c (fun _ : Unit => P)) ())
    rw [hJ] at hsolv hnormal hodd
    refine ⟨layerComp g₀ c (fun _ : Unit => P) (), hcomp (), hsolv, hnormal, hodd, fun hstabQ => ?_⟩
    have hαp : entrywiseAdjointAut τ σ ^ p = 1 := by
      have h1 : σ ^ p = 1 := by rw [← hσord]; exact pow_orderOf_eq_one σ
      have := map_pow (entrywiseAdjointAutHom (τ := τ) (K := K)) σ p
      rw [h1, map_one] at this
      exact this.symm
    exact hLD (adjointGroup τ K) (psiTilde τ K L g₀ c) (psiTilde_injective g₀ c) (hPrange ())
      (entrywiseAdjointAut τ σ) hαp (fun g => (psiTilde_entrywise hΦ₀K hg₀ hcσ g).symm) hstabQ

end Sector

end CFSG.RankThree.PartOne.TCX.E
