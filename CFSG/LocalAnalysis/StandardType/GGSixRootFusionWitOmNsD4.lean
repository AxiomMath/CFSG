module

public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitOmNsFour

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.Universal.Spin
  CFSG.LieType.RootSystem CFSG.Assembly.LowTwoRank

namespace WitOmNs

open Module QuadraticMap CFSG.RankThree.Classical2

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V}

theorem exists_witness_lin_D4 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (h8 : finrank K V = 8)
    (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K + 1) {A : Subgroup (V ≃ₗ[K] V)}
    (hAΩ : A ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAp : ∀ a ∈ A, a ^ p = 1)
    (hAmax : ∀ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, g ^ p = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A)
    (hAcard : p ^ 4 ≤ Nat.card A) {t : V ≃ₗ[K] V}
    (htO : t ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (htt : t * t = 1) (ht1 : t ≠ 1) :
    ∃ d ∈ A, d ≠ 1 ∧ ∃ g ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
      TauCeti.QuadraticMap.orthogonalGroup Q⁆, g * d * g⁻¹ * t = t * (g * d * g⁻¹) ∧
      ∃ Fp Mp : Subgroup (V ≃ₗ[K] V), CFSG.IsQuasisimple Fp ∧
        Nonempty (↥Fp ≃* Matrix.SpecialLinearGroup (Fin 2) K) ∧ Fp ≤ Mp ∧
        (∀ x ∈ Mp, ∀ y ∈ Fp, x * y * x⁻¹ ∈ Fp) ∧
        Mp ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Q, TauCeti.QuadraticMap.orthogonalGroup Q⁆ ∧
        (∀ g ∈ Mp, g * d = d * g) ∧
        ∀ c ∈ TauCeti.QuadraticMap.orthogonalGroup Q, c * d = d * c → ∀ g ∈ Mp,
          c * g * c⁻¹ ∈ Mp := by
  classical
  have hp2 : p ≠ 2 := SpNS.ne_two_of_dvd_card_add_one hpK
  have hAO : ∀ a ∈ A, a ∈ TauCeti.QuadraticMap.orthogonalGroup Q := fun a ha =>
    Subgroup.commutator_le_self _ (hAΩ ha)
  obtain ⟨g, hfact, s, κ, hκ, Φ, β, kf, hζo, hdeg, hβalt, hdecB, hkA⟩ :=
    exists_frame_of_comm hQ hp hpK hAc hAp hAO
  have : Module.Finite K (AdjoinRoot g) := (CoordSL.rootPB g).finite
  set ζ := AdjoinRoot.root g with hζdef
  have hζp : ζ ^ p = 1 := hζo.pow_eq_one
  have hζ1 : ζ ≠ 1 := hζo.ne_one hp.one_lt
  have hL2 : finrank K (AdjoinRoot g) = 2 := by rw [(CoordSL.rootPB g).finrank, hdeg]
  have hdec : ∀ d d' w w', polar Q (Φ (d, w)) (Φ (d', w')) =
      ∑ i, β (d i) (d' i) + polar Q (Φ (0, w)) (Φ (0, w')) := fun d d' w w' => by
    simpa only [polarBilin_apply_apply] using hdecB d d' w w'
  have := LayerCores.finite_linearEquiv (K := K) (V := V)
  have hFA : Function.Injective (fun a : A => ((a : V ≃ₗ[K] V) : V →ₗ[K] V)) :=
    fun a a' h => Subtype.ext (LinearEquiv.toLinearMap_injective h)
  set T : Finset (Fin s) :=
    Finset.univ.filter (fun l => ∃ a ∈ A, ¬ p ∣ kf (a : V →ₗ[K] V) l) with hT'
  have hmemT : ∀ l, l ∈ T ↔ ∃ a ∈ A, ¬ p ∣ kf (a : V →ₗ[K] V) l := fun l => by
    simp only [hT', Finset.mem_filter, Finset.mem_univ, true_and]
  have h1 := card_le_pow_of_supp hp hζp hFA (fun a => hkA a a.2) T (fun a l hl => by
    rw [hmemT] at hl
    push Not at hl
    exact hl a a.2)
  have hT4 : 4 ≤ T.card := by
    by_contra h
    push Not at h
    have h2 := h1.trans (Nat.pow_le_pow_right hp.pos (show T.card ≤ 3 by omega))
    have := Nat.pow_lt_pow_right hp.one_lt (show 3 < 4 by norm_num)
    omega
  obtain ⟨i, hi, j, hj, k, hk, l, hl, hij, hik, hil, hjk, hjl, hkl⟩ := exists_four_of_card hT4
  have hinv : ∀ m ∈ T, ∀ a, Q (blk Φ m (ζ * a)) = Q (blk Φ m a) := by
    intro m hm a
    obtain ⟨a₀, ha₀, hk₀⟩ := (hmemT m).mp hm
    exact quad_blk_mul_eq hp hζp (x := (a₀ : V →ₗ[K] V))
      (fun v => TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp (hAO a₀ ha₀) v) (hkA a₀ ha₀) hk₀ a
  obtain ⟨d, hdA, hd1, hdO, hdp, hdim, hdfix, g', hg', hcommt⟩ :=
    exists_twoPlane_conj hQ hT (by omega) hp hp2 hAO hAmax hζo hdeg hβalt hdecB hkA hij
      ((hmemT i).mp hi) ((hmemT j).mp hj) htO htt ht1
  have hQkl := quad_blk_eq_of_inv hdec hζ1 (hinv k hk) (hinv l hl)
  set ι : AdjoinRoot g →ₗ[K] V :=
    { toFun := fun x => two Φ k l x x
      map_add' := fun x x' => two_add k l x x' x x'
      map_smul' := fun c x => by
        simp only [two, blk_smul, RingHom.id_apply, smul_add] } with hι
  have hιinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro x hz
    rw [LinearMap.mem_ker] at hz
    change two Φ k l x x = 0 at hz
    have h0 : Φ.symm (two Φ k l x x) = 0 := by rw [hz, map_zero]
    simp only [two, blk, map_add, LinearEquiv.symm_apply_apply] at h0
    have hx := congrFun (congrArg Prod.fst h0) k
    simp [hkl] at hx
    exact hx
  obtain ⟨Fp, Mp, hFq, hFe, hFM, hFn, hMΩ, hMd, hMn⟩ := exists_splitComponent hQ hdO hp hp2 hdp
    hK2 hK3 (S := LinearMap.range ι) (by omega)
    (by rw [LinearMap.finrank_range_of_inj hιinj, hL2])
    (by
      rintro _ ⟨x, rfl⟩
      change Q (two Φ k l x x) = 0
      rw [quad_two hdec hkl, ← hQkl, CharTwo.add_self_eq_zero])
    (by
      rintro _ ⟨x, rfl⟩
      change d (two Φ k l x x) = two Φ k l x x
      rw [two, map_add, hdfix k (Ne.symm hik) (Ne.symm hjk), hdfix l (Ne.symm hil) (Ne.symm hjl)])
  exact ⟨d, hdA, hd1, g', hg', hcommt, Fp, Mp, hFq, hFe, hFM, hFn, hMΩ, hMd, hMn⟩

theorem exists_witness_grp_D4 (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (h8 : finrank K V = 8)
    (hK2 : Nat.card K ≠ 2) (hK3 : Nat.card K ≠ 3) {G : Type} [Group G] {p : ℕ} (hp : p.Prime)
    (hpK : p ∣ Nat.card K + 1) {Bs : Subgroup G} (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hcard : p ^ 4 ≤ Nat.card Bs) (φ : ↥(orthDerived Q) →* G) (hφ : Function.Injective φ)
    (hBφ : Bs ≤ φ.range) {s : G} (hs : s ∈ φ.range) (hs2 : orderOf s = 2) :
    ∃ y : G, y * s = s * y ∧ ∃ m ∈ φ.range, m * y * m⁻¹ ∈ Bs ∧ m * y * m⁻¹ ≠ 1 ∧
      ∃ L₁ : Subgroup G, IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer {m * y * m⁻¹}) ∧
        Nonempty (↥L₁ ≃* Matrix.SpecialLinearGroup (Fin 2) K) := by
  classical
  have := LayerCores.finite_linearEquiv (K := K) (V := V)
  set A : Subgroup (V ≃ₗ[K] V) := (Bs.comap φ).map (orthDerived Q).subtype with hA
  have hmemA : ∀ a, a ∈ A ↔ ∃ Y : orthDerived Q, φ Y ∈ Bs ∧ (Y : V ≃ₗ[K] V) = a := fun a =>
    Iff.rfl
  have hAΩ : A ≤ orthDerived Q := Subgroup.map_subtype_le _
  obtain ⟨hAc, hAp, hcardA⟩ := bstar_preimage hBs hφ hBφ
  have hAmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ a ∈ A, g * a = a * g) → g ∈ A := by
    intro g hg hgp hcomm
    refine ⟨⟨g, hg⟩, hSC _ ?_ ?_, rfl⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro b hb
      obtain ⟨Y, rfl⟩ := hBφ hb
      have h1 := hcomm (Y : V ≃ₗ[K] V) ⟨Y, hb, rfl⟩
      have h2 : (⟨g, hg⟩ : orthDerived Q) * Y = Y * ⟨g, hg⟩ := Subtype.ext h1
      rw [← map_mul, ← map_mul, h2]
    · have h1 : (⟨g, hg⟩ : orthDerived Q) ^ p = 1 := Subtype.ext (by
        rw [SubgroupClass.coe_pow]
        exact hgp)
      rw [← map_pow, h1, map_one]
  obtain ⟨v, rfl⟩ := hs
  have hvv : v * v = 1 := by
    have h2 := pow_orderOf_eq_one (φ v)
    rw [hs2, pow_two, ← map_mul] at h2
    exact hφ (by rw [h2, map_one])
  have hv1 : (v : V ≃ₗ[K] V) ≠ 1 := by
    intro h
    have h1 : v = 1 := Subtype.ext h
    rw [h1, map_one, orderOf_one] at hs2
    norm_num at hs2
  obtain ⟨d, hdA, hd1, g, hg, hcommt, Fp, Mp, hFq, ⟨hFe⟩, hFM, hFn, hMΩ, hMd, hMn⟩ :=
    exists_witness_lin_D4 hQ hT h8 hK2 hK3 hp hpK hAΩ hAc hAp hAmax (hcardA ▸ hcard)
      (Subgroup.commutator_le_self _ v.2) (congrArg Subtype.val hvv) hv1
  obtain ⟨d', hd'B, rfl⟩ := (hmemA d).mp hdA
  set g' : orthDerived Q := ⟨g, hg⟩ with hg'
  refine ⟨φ (g' * d' * g'⁻¹), ?_, φ g'⁻¹, ⟨_, rfl⟩, ?_⟩
  · rw [← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext hcommt
  have hconj : φ g'⁻¹ * φ (g' * d' * g'⁻¹) * (φ g'⁻¹)⁻¹ = φ d' := by
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    group
  rw [hconj]
  refine ⟨hd'B, fun h => hd1 (by
    have h2 : d' = 1 := hφ (h.trans (map_one φ).symm)
    rw [h2]
    rfl), ?_⟩
  set L₁ : Subgroup G := (Fp.subgroupOf (orthDerived Q)).map φ with hL₁
  set M₁ : Subgroup G := (Mp.subgroupOf (orthDerived Q)).map φ with hM₁
  have hmem : ∀ (H : Subgroup (V ≃ₗ[K] V)) (x : orthDerived Q),
      x ∈ H.subgroupOf (orthDerived Q) ↔ (x : V ≃ₗ[K] V) ∈ H := fun H x => Subgroup.mem_subgroupOf
  have hLM : L₁ ≤ M₁ := by
    rintro _ ⟨x, hx, rfl⟩
    exact ⟨x, (hmem Mp x).mpr (hFM ((hmem Fp x).mp hx)), rfl⟩
  have hMle : M₁ ≤ φ.range ⊓ Subgroup.centralizer {φ d'} := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨⟨x, rfl⟩, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h1 : x * d' = d' * x := Subtype.ext (hMd _ ((hmem Mp x).mp hx))
    rw [← map_mul, ← map_mul, h1]
  have hFΩ : Fp ≤ orthDerived Q := hFM.trans hMΩ
  have hUq : CFSG.IsQuasisimple ↥(Fp.subgroupOf (orthDerived Q)) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hFΩ).symm hFq
  have hker : φ.ker ≤ Subgroup.center ↥(orthDerived Q) := by
    rw [(MonoidHom.ker_eq_bot_iff φ).mpr hφ]
    exact bot_le
  have hL₁q := SURepair.isQuasisimple_map_of_isQuasisimple hker hUq
  refine ⟨L₁, ⟨hLM.trans hMle, ?_, hL₁q⟩, ⟨((Fp.subgroupOf (orthDerived Q)).equivMapOfInjective
    φ hφ).symm.trans ((Subgroup.subgroupOfEquivOfLe hFΩ).trans hFe)⟩⟩
  refine IsSubnormal.step hLM ?_ (IsSubnormal.step hMle ?_ (IsSubnormal.refl _))
  · rw [Subgroup.normal_subgroupOf_iff hLM]
    rintro _ _ ⟨y, hy, rfl⟩ ⟨x, hx, rfl⟩
    refine ⟨x * y * x⁻¹, (hmem Fp _).mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact hFn _ ((hmem Mp x).mp hx) _ ((hmem Fp y).mp hy)
  · rw [Subgroup.normal_subgroupOf_iff hMle]
    rintro _ k ⟨x, hx, rfl⟩ ⟨⟨c, rfl⟩, hkc⟩
    have hcd : c * d' = d' * c := hφ (by
      have := Subgroup.mem_centralizer_singleton_iff.mp hkc
      rw [map_mul, map_mul]
      exact this)
    refine ⟨c * x * c⁻¹, (hmem Mp _).mpr ?_, by rw [map_mul, map_mul, map_inv]⟩
    exact hMn c (Subgroup.commutator_le_self _ c.2) (congrArg Subtype.val hcd) x
      ((hmem Mp x).mp hx)

section Tags

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

theorem witnessAlt_POmegaPlus_D4 {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {f : ℕ} (hf3 : 3 ≤ f) (hn : 3 ≤ 4)
    {ψ : spinGroup (quadPlus 4 (GaloisField 2 f)) →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (plusDatum 4 (GaloisField 2 f) hn) .POmegaPlus 4 f ψ)
    (s1 : GGSixStepOne p B Bs x L D J) (hpq : p ∣ 2 ^ f + 1) {E : Subgroup G} {r : G}
    {s : G} (hs : s ∈ ggG0 p B x L D J) (hs2 : orderOf s = 2) :
    GGRootFusionWitnessAlt p Bs D E (ggG0 p B x L D J) (ggM p B x L D J) .POmegaPlus f r s := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hψinj : Function.Injective ψ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff,
      ← RootCentOmega.center_spinGroup_quadPlus_eq_bot_charTwo hn]
    exact hker
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hrange]
    exact s1.1
  have hBψ : Bs ≤ ψ.range := by
    intro b hb
    obtain ⟨g, hg, hbg⟩ :=
      PsiDiag.SpinP.exists_mem_centralizer hn ψ hker (hctx.2.2.2.2.2.2.1.2 b hb)
    rw [hC, Subgroup.mem_bot] at hbg
    rw [eq_inv_of_mul_eq_one_left hbg]
    exact ψ.range.inv_mem hg
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadPlus 4 (GaloisField 2 f) hn
  set πe := MulEquiv.ofBijective (AutOm.spinModelPlus (K := GaloisField 2 f) hn)
    ⟨AutOm.spinModelPlus_injective hn, AutOm.spinModelPlus_surjective hn⟩ with hπe
  set e₁ := CFSG.RankThree.PartOne.KCOrthComm.matrixDerivedEquiv
    (coordinateQuadPlus 4 (GaloisField 2 f)) with he₁
  set φ : ↥(orthDerived (coordinateQuadPlus 4 (GaloisField 2 f))) →* G :=
    ψ.comp (πe.symm.toMonoidHom.comp e₁.symm.toMonoidHom) with hφ
  have hφinj : Function.Injective φ := hψinj.comp (πe.symm.injective.comp e₁.symm.injective)
  have hφrange : φ.range = ggG0 p B x L D J := by
    rw [← hrange]
    ext y
    constructor
    · rintro ⟨X, rfl⟩
      exact ⟨_, rfl⟩
    · rintro ⟨u, rfl⟩
      refine ⟨e₁ (πe u), ?_⟩
      simp [hφ]
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq8 : 8 ≤ 2 ^ f := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf3
  have hdim : finrank (GaloisField 2 f) (Fin (2 * 4) → GaloisField 2 f) = 8 :=
    Module.finrank_fin_fun _
  have hcard : p ^ 4 ≤ Nat.card Bs :=
    (GGConfig.tableB_facts (G := G) ⟨hctx.1, hctx.2.1, hctx.2.2.1⟩).2.2.2.2
  obtain ⟨y, hys, m, hm, hb, hb1, L₁, hL₁, ⟨eL⟩⟩ := exists_witness_grp_D4 hnd hT hdim
    (by omega) (by omega) hp (hK ▸ hpq) hctx.2.1.2.1 hctx.2.1.2.2.2 hcard φ hφinj
    (by rw [hφrange, ← hrange]; exact hBψ) (by rw [hφrange]; exact hs) hs2
  rw [hφrange] at hm hL₁
  have hnex : ¬ GGSixSeventeenExcluded p .POmegaPlus f L₁ :=
    WitOm.not_ggSixSeventeenExcluded_SL2 hK (by omega) (by decide) (by decide)
      (fun _ hf2 => by omega) eL
  exact Or.inr (Or.inl ⟨y, hys, m, Subgroup.le_normalizer hm, hb1,
    Or.inr (Or.inr ⟨hb, L₁, hL₁, Or.inr hnex⟩)⟩)

end Tags

end WitOmNs

section Inputs

theorem ggSixRootFusionWitnessOn_POmegaPlusQ1FourBig :
    GGSixRootFusionWitnessOn fun t n f p => t = .POmegaPlus ∧ p ∣ 2 ^ f + 1 ∧ n = 4 ∧ 3 ≤ f := by
  intro G _ _ p B Bs x L D J t n f ψ hP
  obtain ⟨rfl, hpq, rfl, hf3⟩ := hP
  revert ψ
  rw [ggU_POmegaPlus_eq (show 3 ≤ 4 by norm_num)]
  intro ψ hctx s1 _ E r _ _ _ s hs hs2
  exact WitOmNs.witnessAlt_POmegaPlus_D4 hf3 _ hctx s1 hpq hs hs2

end Inputs

end CFSG.StandardType
