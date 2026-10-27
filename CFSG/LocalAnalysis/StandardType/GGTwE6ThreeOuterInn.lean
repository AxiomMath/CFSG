module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeLift
public import CFSG.LocalAnalysis.SeitzReduction.TwistedE6PilotHR4
public import CFSG.LocalAnalysis.StandardType.GGTwE6ToralInner
public import CFSG.LieType.Chevalley.TwistedE6NormalForm
public import CFSG.LieType.Chevalley.TwistedE6NormalFormActors

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.SeitzReduction.TwistedE6Pilot CFSG.StandardType.TableBExc.E6Three


open TableB.TwE6

section Parameters

variable {K : Type} [Field K] {σ : K →+* K}

theorem mem_compat_units_map {b : Fin 6 → Kˣ} (hb : b ∈ compat σ) :
    (fun i => Units.map σ.toMonoidHom (b i)) ∈ compat σ := by
  rw [mem_compat] at hb ⊢
  intro i
  rw [hb i]

theorem mem_compat_pow_card_add_one {q : ℕ} {b : Fin 6 → Kˣ} (hb : b ∈ compat σ) :
    b ^ (q + 1) ∈ compat σ := by
  rw [mem_compat] at hb ⊢
  intro i
  rw [Pi.pow_apply, Pi.pow_apply, hb i, ← map_pow]

theorem mem_torus₀_pow_card_add_one [Finite K] {q : ℕ} (hq : 2 ≤ q)
    (hK : Nat.card K = q ^ 2) (hσ : ∀ c, σ c = c ^ q)
    {b : Fin 6 → Kˣ} (hb : b ∈ compat σ) : b ^ (q + 1) ∈ torus₀ σ := by
  obtain ⟨x, hx⟩ := exists_mul_edge_inv_mem hq hK hσ hb
  set t := b * (edge σ x)⁻¹ with ht
  have hb' : b = t * edge σ x := by rw [ht]; group
  have htT : t ∈ torus₀ σ := hx
  have hfix : σ ((x ^ (q + 1) : Kˣ) : K) = ((x ^ (q + 1) : Kˣ) : K) := by
    rw [hσ, Units.val_pow_eq_pow_val]
    calc ((x : K) ^ (q + 1)) ^ q = (x : K) ^ ((q + 1) * q) := (pow_mul _ _ _).symm
      _ = (x : K) ^ (q ^ 2 + q) := by congr 1; ring
      _ = (x : K) ^ (q ^ 2) * (x : K) ^ q := pow_add _ _ _
      _ = (x : K) * (x : K) ^ q := by rw [TwE6Toral.pow_sq_card_eq hK]
      _ = (x : K) ^ (q + 1) := (pow_succ' _ _).symm
  rw [hb', mul_pow]
  refine mul_mem ((torus₀ σ).pow_mem htT _) ?_
  have he : (edge σ x) ^ (q + 1) = edge σ (x ^ (q + 1)) := (map_pow (edge σ) x (q + 1)).symm
  rw [he]
  exact TwE6Toral.edge_mem_torus₀_of_fixed hq hK hσ hfix

end Parameters

section EtaConj

variable {K : Type} [Field K] [CharP K 2] (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c)

theorem diagramMap_conj_rootDiagUnit {b : Fin 6 → Kˣ} (hb : b ∈ compat σ) :
    diagramMap TwistTag.E6 K * rootDiagUnit TwistTag.E6.tag b * (diagramMap TwistTag.E6 K)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i => Units.map σ.toMonoidHom (b i)) := by
  calc diagramMap TwistTag.E6 K * rootDiagUnit TwistTag.E6.tag b * (diagramMap TwistTag.E6 K)⁻¹ =
      rootDiagUnit TwistTag.E6.tag (fun i : Fin 6 => b (TwistTag.E6.perm.symm i)) := by
        rw [E6_diagramMap_mul_rootDiagUnit]
        group
    _ = rootDiagUnit TwistTag.E6.tag (fun i => Units.map σ.toMonoidHom (b i)) := by
        have hsymm' : (TwistTag.E6.perm.symm : Fin 6 → Fin 6) =
            (LargeEvenRhoE6 : Fin 6 → Fin 6) := by
          rw [show TwistTag.E6.perm = LargeEvenRhoE6 from rfl]
          ext j
          fin_cases j <;> decide
        have hfun : (fun i : Fin 6 => b (TwistTag.E6.perm.symm i)) =
            (fun i => Units.map σ.toMonoidHom (b i)) := by
          funext i
          have hb' := hb i
          rw [congrFun hsymm' i]
          exact hb'
        rw [hfun]
        rfl

theorem etaAut_mul_compatParamAut_mul_inv (b : ↥(compat σ)) :
    etaAut σ hσσ * RootCentExc.compatParamAut σ b * (etaAut σ hσσ)⁻¹ =
      RootCentExc.compatParamAut σ
        ⟨fun i => Units.map σ.toMonoidHom ((b : Fin 6 → Kˣ) i),
          mem_compat_units_map b.2⟩ := by
  have hPconj : (⟨diagramMap TwistTag.E6 K, diagramMap_mem_normalizer σ hσσ⟩ :
        Subgroup.normalizer (graphFixedRootGroup TwistTag.E6 K σ : Set _)) *
      (⟨rootDiagUnit TwistTag.E6.tag ((b : Fin 6 → Kˣ)),
        rootDiagUnit_mem_normalizer_graphFixedRootGroup (σ := σ) (Iff.mp (mem_compat σ) b.2)⟩ :
        Subgroup.normalizer (graphFixedRootGroup TwistTag.E6 K σ : Set _)) *
      (⟨diagramMap TwistTag.E6 K, diagramMap_mem_normalizer σ hσσ⟩ :
        Subgroup.normalizer (graphFixedRootGroup TwistTag.E6 K σ : Set _))⁻¹ =
      (⟨rootDiagUnit TwistTag.E6.tag (fun i => Units.map σ.toMonoidHom ((b : Fin 6 → Kˣ) i)),
        rootDiagUnit_mem_normalizer_graphFixedRootGroup (σ := σ)
          (Iff.mp (mem_compat σ) (mem_compat_units_map b.2))⟩ :
        Subgroup.normalizer (graphFixedRootGroup TwistTag.E6 K σ : Set _)) := by
    refine Subtype.ext ?_
    exact diagramMap_conj_rootDiagUnit σ b.2
  have hη : etaAut σ hσσ =
      (graphFixedRootGroup TwistTag.E6 K σ).normalizerMonoidHom
        ⟨diagramMap TwistTag.E6 K, diagramMap_mem_normalizer σ hσσ⟩ := rfl
  have hΔ : ∀ (c : Fin 6 → Kˣ) (hc : c ∈ compat σ),
      RootCentExc.compatParamAut σ ⟨c, hc⟩ =
        (graphFixedRootGroup TwistTag.E6 K σ).normalizerMonoidHom
          ⟨rootDiagUnit TwistTag.E6.tag c,
            rootDiagUnit_mem_normalizer_graphFixedRootGroup (σ := σ) (Iff.mp (mem_compat σ) hc)⟩ := fun _ _ => rfl
  rw [hη, hΔ b b.2, hΔ _ (mem_compat_units_map b.2), ← map_inv, ← map_mul, ← map_mul]
  exact congrArg _ hPconj

end EtaConj

section Quotient

variable {K : Type} [Field K] [CharP K 2] [Finite K] {q : ℕ}
  (σ : K →+* K) (hσσ : ∀ c, σ (σ c) = c)

theorem etaAut_conj_compatParamAut_mul_inv_quotient (hσ : ∀ c, σ c = c ^ q)
    (hq : 2 ≤ q) (hK : Nat.card K = q ^ 2) (b : ↥(compat σ)) :
    QuotientGroup.mk' (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range
        (etaAut σ hσσ * RootCentExc.compatParamAut σ b * (etaAut σ hσσ)⁻¹) =
      (QuotientGroup.mk' (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range
        (RootCentExc.compatParamAut σ b))⁻¹ := by
  haveI hIn : ((MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
      MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range).Normal :=
    RootCentExc.normal_range_mulAutConj
  have htorus : ((b : Fin 6 → Kˣ) ^ (q + 1)) ∈ torus₀ σ :=
    mem_torus₀_pow_card_add_one hq hK hσ b.2
  have hinner : RootCentExc.compatParamAut σ
      ⟨(b : Fin 6 → Kˣ) ^ (q + 1), mem_compat_pow_card_add_one (q := q) b.2⟩ ∈
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ)).range :=
    RootCentExc.compatParamAut_mem_range_of_mem_torus σ htorus
  have hsplit : (⟨fun i => Units.map σ.toMonoidHom ((b : Fin 6 → Kˣ) i),
        mem_compat_units_map b.2⟩ : ↥(compat σ)) =
      (b : ↥(compat σ))⁻¹ *
        ⟨(b : Fin 6 → Kˣ) ^ (q + 1),
          mem_compat_pow_card_add_one (q := q) b.2⟩ := by
    refine Subtype.ext ?_
    funext i
    apply Units.ext
    simp only [Subtype.coe_mk, Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_pow,
      Pi.mul_apply, Pi.inv_apply, Pi.pow_apply, Units.val_mul, Units.coe_map,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
    change (σ ((b : Fin 6 → Kˣ) i) : K) =
      (((b : Fin 6 → Kˣ) i : K))⁻¹ * ((b : Fin 6 → Kˣ) i : K) ^ (q + 1)
    rw [hσ, pow_succ, mul_comm (((b : Fin 6 → Kˣ) i : K) ^ q) ((b : Fin 6 → Kˣ) i : K),
      ← mul_assoc]
    simp
  have heq : etaAut σ hσσ * RootCentExc.compatParamAut σ b * (etaAut σ hσσ)⁻¹ =
      (RootCentExc.compatParamAut σ b)⁻¹ * RootCentExc.compatParamAut σ
        ⟨(b : Fin 6 → Kˣ) ^ (q + 1),
          mem_compat_pow_card_add_one (q := q) b.2⟩ := by
    rw [etaAut_mul_compatParamAut_mul_inv, hsplit, map_mul, map_inv]
  calc QuotientGroup.mk' _ (etaAut σ hσσ * RootCentExc.compatParamAut σ b *
        (etaAut σ hσσ)⁻¹) =
      QuotientGroup.mk' _ ((RootCentExc.compatParamAut σ b)⁻¹ *
        RootCentExc.compatParamAut σ ⟨(b : Fin 6 → Kˣ) ^ (q + 1),
          mem_compat_pow_card_add_one (q := q) b.2⟩) := by rw [heq]
    _ = (QuotientGroup.mk' _ (RootCentExc.compatParamAut σ b))⁻¹ := by
        have hc1 : QuotientGroup.mk (RootCentExc.compatParamAut σ
            ⟨(b : Fin 6 → Kˣ) ^ (q + 1),
              mem_compat_pow_card_add_one (q := q) b.2⟩) = 1 :=
          (QuotientGroup.eq_one_iff _).2 hinner
        rw [QuotientGroup.mk'_apply, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk'_apply, hc1, mul_one]

end Quotient

section Main

abbrev TwE6GraphFixedGalois (f : ℕ) : Type :=
  ↥(graphFixedRootGroup TwistTag.E6 (GaloisField 2 (2 * f)) (frobQ 2 f))

theorem mem_range_conj_of_mem_twInndiag_of_commute_mk_etaAut {f : ℕ} (hf : 1 ≤ f)
    {x : MulAut (TwE6GraphFixedGalois f)} (hx : x ∈ LayerSixE.twInndiagAut f)
    (hc : Commute
      (QuotientGroup.mk' ((MulAut.conj : TwE6GraphFixedGalois f →*
          MulAut (TwE6GraphFixedGalois f)).range) x)
      (QuotientGroup.mk' ((MulAut.conj : TwE6GraphFixedGalois f →*
          MulAut (TwE6GraphFixedGalois f)).range)
        (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf)))) :
    x ∈ (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range := by
  classical
  set I : Subgroup (MulAut (TwE6GraphFixedGalois f)) :=
    (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range with hI
  haveI hIn : I.Normal := RootCentExc.normal_range_mulAutConj
  have hx' : x ∈ I ⊔ (RootCentExc.compatParamAut (frobQ 2 f)).range := by
    rw [hI]
    exact hx
  obtain ⟨a, ha, d, hd, rfl⟩ := (Subgroup.mem_sup_of_normal_left).1 hx'
  obtain ⟨b, rfl⟩ := hd
  have ha1 : QuotientGroup.mk' I a = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff a).2 ha
  have hcomm : Commute (QuotientGroup.mk' I (RootCentExc.compatParamAut (frobQ 2 f) b))
      (QuotientGroup.mk' I (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf))) := by
    change Commute (QuotientGroup.mk' I a *
      QuotientGroup.mk' I (RootCentExc.compatParamAut (frobQ 2 f) b))
      (QuotientGroup.mk' I (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf))) at hc
    rwa [ha1, one_mul] at hc
  set t := QuotientGroup.mk' I (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf)) with ht
  set g := QuotientGroup.mk' I (RootCentExc.compatParamAut (frobQ 2 f) b) with hg
  have hinv : t * g * t⁻¹ = g⁻¹ := by
    change QuotientGroup.mk' I (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf) *
      RootCentExc.compatParamAut (frobQ 2 f) b *
      (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf))⁻¹) =
      (QuotientGroup.mk' I (RootCentExc.compatParamAut (frobQ 2 f) b))⁻¹
    exact etaAut_conj_compatParamAut_mul_inv_quotient (σ := frobQ 2 f)
      (hσσ := frobQ_frobQ 2 f hf) (frobQ_apply 2 f)
      (TwE6Toral.two_le_two_pow hf) (TwE6Toral.card_galoisField_two_mul f hf) b
  have hg_eq : g = g⁻¹ := by
    calc g = (g * t) * t⁻¹ := by group
      _ = (t * g) * t⁻¹ := congrArg (fun z => z * t⁻¹) hcomm.eq
      _ = t * g * t⁻¹ := by rw [mul_assoc]
      _ = g⁻¹ := hinv
  have hg2 : g ^ 2 = 1 := by
    calc g ^ 2 = g * g := pow_two g
      _ = g * g⁻¹ := congrArg (fun z => g * z) hg_eq
      _ = 1 := mul_inv_cancel g
  have hg3 : g ^ 3 = 1 := by
    change QuotientGroup.mk' I (RootCentExc.compatParamAut (frobQ 2 f) b ^ 3) = 1
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2
      (TwE6Toral.compatParamAut_pow_three_mem (TwE6Toral.two_le_two_pow hf)
        (TwE6Toral.card_galoisField_two_mul f hf) (frobQ_apply 2 f) b)
  have hg1 : g = 1 := by
    have hdvd : orderOf g ∣ 1 := by
      have h2 : orderOf g ∣ 2 := orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hg2)
      have h3 : orderOf g ∣ 3 := orderOf_dvd_of_pow_eq_one hg3
      have := Nat.dvd_gcd h2 h3
      simpa using this
    exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)
  have hdI : RootCentExc.compatParamAut (frobQ 2 f) b ∈ I := by
    rw [hg] at hg1
    exact (QuotientGroup.eq_one_iff _).1 hg1
  exact Subgroup.mul_mem I ha hdI


theorem mem_range_conj_of_mem_twInndiag_of_commute_etaAut {f : ℕ} (hf : 1 ≤ f)
    {x : MulAut (TwE6GraphFixedGalois f)} (hx : x ∈ LayerSixE.twInndiagAut f)
    (hc : Commute x (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf))) :
    x ∈ (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range :=
  mem_range_conj_of_mem_twInndiag_of_commute_mk_etaAut hf hx (hc.map (QuotientGroup.mk' _))

theorem mem_range_conj_of_mem_twInndiag_of_commute_xiAut {f : ℕ} (hf : 1 ≤ f)
    {x : MulAut (TwE6GraphFixedGalois f)} (hx : x ∈ LayerSixE.twInndiagAut f)
    (hc : Commute x (xiAut (frobQ 2 f) (frobQ_frobQ 2 f hf))) :
    x ∈ (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range := by
  classical
  set I : Subgroup (MulAut (TwE6GraphFixedGalois f)) :=
    (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range with hI
  haveI hIn : I.Normal := RootCentExc.normal_range_mulAutConj
  have hmk : QuotientGroup.mk' I (xiAut (frobQ 2 f) (frobQ_frobQ 2 f hf)) =
      QuotientGroup.mk' I (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf)) := by
    have hxi : xiAut (frobQ 2 f) (frobQ_frobQ 2 f hf) =
        MulAut.conj (⟨pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot 1,
          pinnedX_highRoot_one_mem (frobQ 2 f)⟩ :
          TwE6GraphFixedGalois f) *
        etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf) := rfl
    rw [hxi]
    change QuotientGroup.mk' I
        (MulAut.conj (⟨pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot 1,
          pinnedX_highRoot_one_mem (frobQ 2 f)⟩ : TwE6GraphFixedGalois f)) *
      QuotientGroup.mk' I (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf)) =
      QuotientGroup.mk' I (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf))
    have hone : QuotientGroup.mk' I
        (MulAut.conj (⟨pinnedX TwistTag.E6.tag (GaloisField 2 (2 * f)) e6HighestRoot 1,
          pinnedX_highRoot_one_mem (frobQ 2 f)⟩ : TwE6GraphFixedGalois f)) = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff _).2 ⟨_, rfl⟩
    rw [hone, one_mul]
  refine mem_range_conj_of_mem_twInndiag_of_commute_mk_etaAut hf hx ?_
  have := hc.map (QuotientGroup.mk' I)
  rwa [hmk] at this

end Main

section Normal

theorem twInndiagAut_normal {f : ℕ} (hf : 1 ≤ f) :
    (LayerSixE.twInndiagAut f).Normal := by
  let K := GaloisField 2 (2 * f)
  let σE : K ≃+* K := frobQEquiv hf
  have hK : Nat.card K = (2 ^ f) ^ 2 := TwE6Toral.card_galoisField_two_mul f hf
  have hσ : ∀ c : K, σE c = c ^ 2 ^ f := frobQ_apply 2 f
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, hker, -, -, -⟩, -, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf
      K hK σE hσ
  have h : Θ.ker = LayerSixE.twInndiagAut f := by
    rw [hker]
    change twistedE6Inn K σE ⊔ twistedE6Diag K σE =
      (MulAut.conj : twistedE6RootGroup K σE →* MulAut (twistedE6RootGroup K σE)).range ⊔
        (RootCentExc.compatParamAut σE.toRingHom).range
    rw [range_compatParamAut_eq_twistedE6Diag]
    rfl
  rw [← h]
  exact MonoidHom.normal_ker Θ

theorem le_range_conj_of_commute_etaAut {f : ℕ} (hf : 1 ≤ f)
    {X : Subgroup (MulAut (TwE6GraphFixedGalois f))}
    (hX : X ≤ LayerSixE.twInndiagAut f)
    (hc : ∀ x ∈ X, Commute x (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf))) :
    X ≤ (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range :=
  fun _ hx => mem_range_conj_of_mem_twInndiag_of_commute_etaAut hf (hX hx) (hc _ hx)

theorem le_range_conj_of_commute_xiAut {f : ℕ} (hf : 1 ≤ f)
    {X : Subgroup (MulAut (TwE6GraphFixedGalois f))}
    (hX : X ≤ LayerSixE.twInndiagAut f)
    (hc : ∀ x ∈ X, Commute x (xiAut (frobQ 2 f) (frobQ_frobQ 2 f hf))) :
    X ≤ (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range :=
  fun _ hx => mem_range_conj_of_mem_twInndiag_of_commute_xiAut hf (hX hx) (hc _ hx)

theorem mem_range_conj_of_mem_twInndiag_of_commute_conj_etaAut {f : ℕ} (hf : 1 ≤ f)
    (φ : MulAut (TwE6GraphFixedGalois f))
    {x : MulAut (TwE6GraphFixedGalois f)} (hx : x ∈ LayerSixE.twInndiagAut f)
    (hc : Commute x (φ * etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf) * φ⁻¹)) :
    x ∈ (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range := by
  set I : Subgroup (MulAut (TwE6GraphFixedGalois f)) :=
    (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range with hI
  haveI hIn : I.Normal := RootCentExc.normal_range_mulAutConj
  set y := φ⁻¹ * x * φ with hy
  have hy_mem : y ∈ LayerSixE.twInndiagAut f := by
    rw [hy]
    exact (twInndiagAut_normal hf).conj_mem x hx φ⁻¹
  have hy_comm : Commute y (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf)) := by
    have h := hc.map (MulAut.conj φ⁻¹)
    rwa [show (MulAut.conj φ⁻¹) (φ * etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf) * φ⁻¹) =
        etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf) by
      rw [MulAut.conj_apply]
      group] at h
  have hyI : y ∈ I :=
    mem_range_conj_of_mem_twInndiag_of_commute_etaAut hf hy_mem hy_comm
  have hx_eq : φ * y * φ⁻¹ = x := by rw [hy]; group
  rw [← hx_eq]
  exact hIn.conj_mem y hyI φ

theorem mem_range_conj_of_mem_twInndiag_of_commute_conj_xiAut {f : ℕ} (hf : 1 ≤ f)
    (φ : MulAut (TwE6GraphFixedGalois f))
    {x : MulAut (TwE6GraphFixedGalois f)} (hx : x ∈ LayerSixE.twInndiagAut f)
    (hc : Commute x (φ * xiAut (frobQ 2 f) (frobQ_frobQ 2 f hf) * φ⁻¹)) :
    x ∈ (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range := by
  set I : Subgroup (MulAut (TwE6GraphFixedGalois f)) :=
    (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range with hI
  haveI hIn : I.Normal := RootCentExc.normal_range_mulAutConj
  set y := φ⁻¹ * x * φ with hy
  have hy_mem : y ∈ LayerSixE.twInndiagAut f := by
    rw [hy]
    exact (twInndiagAut_normal hf).conj_mem x hx φ⁻¹
  have hy_comm : Commute y (xiAut (frobQ 2 f) (frobQ_frobQ 2 f hf)) := by
    have h := hc.map (MulAut.conj φ⁻¹)
    rwa [show (MulAut.conj φ⁻¹) (φ * xiAut (frobQ 2 f) (frobQ_frobQ 2 f hf) * φ⁻¹) =
        xiAut (frobQ 2 f) (frobQ_frobQ 2 f hf) by
      rw [MulAut.conj_apply]
      group] at h
  have hyI : y ∈ I :=
    mem_range_conj_of_mem_twInndiag_of_commute_xiAut hf hy_mem hy_comm
  have hx_eq : φ * y * φ⁻¹ = x := by rw [hy]; group
  rw [← hx_eq]
  exact hIn.conj_mem y hyI φ

end Normal


theorem pow_three_mk'_eq_one_of_mem_twInndiag {f : ℕ} (hf : 1 ≤ f)
    {x : MulAut (TwE6GraphFixedGalois f)} (hx : x ∈ LayerSixE.twInndiagAut f) :
    (QuotientGroup.mk' ((MulAut.conj : TwE6GraphFixedGalois f →*
        MulAut (TwE6GraphFixedGalois f)).range) x) ^ 3 = 1 := by
  classical
  set I : Subgroup (MulAut (TwE6GraphFixedGalois f)) :=
    (MulAut.conj : TwE6GraphFixedGalois f →* MulAut (TwE6GraphFixedGalois f)).range with hI
  haveI hIn : I.Normal := RootCentExc.normal_range_mulAutConj
  have hx' : x ∈ I ⊔ (RootCentExc.compatParamAut (frobQ 2 f)).range := by
    rw [hI]; exact hx
  obtain ⟨a, ha, d, hd, rfl⟩ := (Subgroup.mem_sup_of_normal_left).1 hx'
  obtain ⟨b, rfl⟩ := hd
  set X : MulAut (TwE6GraphFixedGalois f) :=
    RootCentExc.compatParamAut (frobQ 2 f) b with hX
  have ha1 : QuotientGroup.mk' I a = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff a).2 ha
  have hX3 : X ^ 3 ∈ I := by
    rw [hX]
    exact TwE6Toral.compatParamAut_pow_three_mem (TwE6Toral.two_le_two_pow hf)
      (TwE6Toral.card_galoisField_two_mul f hf) (frobQ_apply 2 f) b
  have hqX3 : QuotientGroup.mk' I (X ^ 3) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hX3
  calc (QuotientGroup.mk' I (a * X)) ^ 3 = (QuotientGroup.mk' I X) ^ 3 := by
        rw [map_mul, ha1, one_mul]
    _ = QuotientGroup.mk' I (X ^ 3) := by rw [← map_pow]
    _ = 1 := hqX3

theorem eta_conj_mk'_eq_inv_of_mem_twInndiag {f : ℕ} (hf : 1 ≤ f)
    {x : MulAut (TwE6GraphFixedGalois f)} (hx : x ∈ LayerSixE.twInndiagAut f) :
    QuotientGroup.mk' ((MulAut.conj : TwE6GraphFixedGalois f →*
        MulAut (TwE6GraphFixedGalois f)).range)
        (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf) * x *
          (etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf))⁻¹) =
      (QuotientGroup.mk' ((MulAut.conj : TwE6GraphFixedGalois f →*
        MulAut (TwE6GraphFixedGalois f)).range) x)⁻¹ := by
  classical
  set I : Subgroup (MulAut (TwE6GraphFixedGalois f)) :=
    (MulAut.conj : TwE6GraphFixedGalois f →* MulAut (TwE6GraphFixedGalois f)).range with hI
  haveI hIn : I.Normal := RootCentExc.normal_range_mulAutConj
  set η : MulAut (TwE6GraphFixedGalois f) :=
    etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf) with hη
  have hx' : x ∈ I ⊔ (RootCentExc.compatParamAut (frobQ 2 f)).range := by
    rw [hI]; exact hx
  obtain ⟨a, ha, d, hd, rfl⟩ := (Subgroup.mem_sup_of_normal_left).1 hx'
  obtain ⟨b, rfl⟩ := hd
  set X : MulAut (TwE6GraphFixedGalois f) :=
    RootCentExc.compatParamAut (frobQ 2 f) b with hX
  have ha1 : QuotientGroup.mk' I a = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff a).2 ha
  have hηa : η * a * η⁻¹ ∈ I := hIn.conj_mem a ha η
  have hηa1 : QuotientGroup.mk' I (η * a * η⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hηa
  have hηX : QuotientGroup.mk' I (η * X * η⁻¹) = (QuotientGroup.mk' I X)⁻¹ := by
    rw [hX]
    exact etaAut_conj_compatParamAut_mul_inv_quotient (σ := frobQ 2 f)
      (hσσ := frobQ_frobQ 2 f hf) (frobQ_apply 2 f)
      (TwE6Toral.two_le_two_pow hf) (TwE6Toral.card_galoisField_two_mul f hf) b
  have hgroup : η * (a * X) * η⁻¹ = (η * a * η⁻¹) * (η * X * η⁻¹) := by group
  calc QuotientGroup.mk' I (η * (a * X) * η⁻¹)
      = QuotientGroup.mk' I ((η * a * η⁻¹) * (η * X * η⁻¹)) :=
        congrArg (QuotientGroup.mk' I) hgroup
    _ = QuotientGroup.mk' I (η * a * η⁻¹) * QuotientGroup.mk' I (η * X * η⁻¹) := by
        rw [map_mul]
    _ = (QuotientGroup.mk' I X)⁻¹ := by rw [hηa1, hηX, one_mul]
    _ = (QuotientGroup.mk' I (a * X))⁻¹ := by rw [map_mul, ha1, one_mul]

theorem diag_conj_mk'_eq_of_mem_compatParamAut {f : ℕ}
    {d : MulAut (TwE6GraphFixedGalois f)}
    (hd : d ∈ (RootCentExc.compatParamAut (frobQ 2 f)).range)
    {x : MulAut (TwE6GraphFixedGalois f)} (hx : x ∈ LayerSixE.twInndiagAut f) :
    QuotientGroup.mk' ((MulAut.conj : TwE6GraphFixedGalois f →*
        MulAut (TwE6GraphFixedGalois f)).range) (d * x * d⁻¹) =
      QuotientGroup.mk' ((MulAut.conj : TwE6GraphFixedGalois f →*
        MulAut (TwE6GraphFixedGalois f)).range) x := by
  classical
  set I : Subgroup (MulAut (TwE6GraphFixedGalois f)) :=
    (MulAut.conj : TwE6GraphFixedGalois f →* MulAut (TwE6GraphFixedGalois f)).range with hI
  haveI hIn : I.Normal := RootCentExc.normal_range_mulAutConj
  obtain ⟨b, rfl⟩ := hd
  set X : MulAut (TwE6GraphFixedGalois f) :=
    RootCentExc.compatParamAut (frobQ 2 f) b with hX
  have hx' : x ∈ I ⊔ (RootCentExc.compatParamAut (frobQ 2 f)).range := by
    rw [hI]; exact hx
  obtain ⟨a, ha, d, hd, rfl⟩ := (Subgroup.mem_sup_of_normal_left).1 hx'
  obtain ⟨c, rfl⟩ := hd
  set Z : MulAut (TwE6GraphFixedGalois f) :=
    RootCentExc.compatParamAut (frobQ 2 f) c with hZ
  have hcomm : X * Z = Z * X := by
    rw [hX, hZ, ← map_mul, ← map_mul]
    congr 1
    refine Subtype.ext ?_
    funext i
    exact mul_comm _ _
  have hXZ : X * Z * X⁻¹ = Z := by
    calc X * Z * X⁻¹ = (X * Z) * X⁻¹ := rfl
      _ = (Z * X) * X⁻¹ := congrArg (fun w => w * X⁻¹) hcomm
      _ = Z := by group
  have hgroup : X * (a * Z) * X⁻¹ = (X * a * X⁻¹) * Z := by
    calc X * (a * Z) * X⁻¹ = (X * a * X⁻¹) * (X * Z * X⁻¹) := by group
      _ = (X * a * X⁻¹) * Z := congrArg (fun w => (X * a * X⁻¹) * w) hXZ
  have hinner : X * a * X⁻¹ ∈ I := hIn.conj_mem a ha X
  have h1 : QuotientGroup.mk' I (X * a * X⁻¹) = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff _).2 hinner
  have h2 : QuotientGroup.mk' I a = 1 := by
    rw [QuotientGroup.mk'_apply]
    exact (QuotientGroup.eq_one_iff a).2 ha
  have hxq : QuotientGroup.mk' I (a * Z) = QuotientGroup.mk' I Z := by
    rw [map_mul, h2, one_mul]
  calc QuotientGroup.mk' I (X * (a * Z) * X⁻¹)
      = QuotientGroup.mk' I ((X * a * X⁻¹) * Z) := congrArg (QuotientGroup.mk' I) hgroup
    _ = QuotientGroup.mk' I (X * a * X⁻¹) * QuotientGroup.mk' I Z := by rw [map_mul]
    _ = 1 * QuotientGroup.mk' I Z := by rw [h1]
    _ = QuotientGroup.mk' I Z := one_mul _
    _ = QuotientGroup.mk' I (a * Z) := hxq.symm


theorem fieldActor_frobQ_eq_etaAut {f : ℕ} (hf : 1 ≤ f) :
    (fieldActor (frobQEquiv hf) (frobQEquiv hf) : MulAut (TwE6GraphFixedGalois f)) =
      etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf) := by
  let K := GaloisField 2 (2 * f)
  let σE : K ≃+* K := frobQEquiv hf
  have hK : Nat.card K = (2 ^ f) ^ 2 := TwE6Toral.card_galoisField_two_mul f hf
  have hσ : ∀ c : K, σE c = c ^ 2 ^ f := frobQ_apply 2 f
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, -, -, -, -, -, -⟩, hfield, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σE hσ
  refine MulEquiv.ext fun g => Subtype.ext ?_
  change ((fieldActor (frobQEquiv hf) (frobQEquiv hf)) g : ModGL TwistTag.E6.tag K) =
    ((etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf)) g : ModGL TwistTag.E6.tag K)
  rw [coe_etaAut (frobQ 2 f) (frobQ_frobQ 2 f hf) g, hfield g]

theorem mem_range_conj_of_mem_twInndiag_of_commute_outer_involution {f : ℕ} (hf : 1 ≤ f)
    {t : MulAut (TwE6GraphFixedGalois f)} (ht2 : t ^ 2 = 1)
    (htI : t ∉ LayerSixE.twInndiagAut f)
    {x : MulAut (TwE6GraphFixedGalois f)} (hx : x ∈ LayerSixE.twInndiagAut f)
    (hxt : t * x = x * t) :
    x ∈ (MulAut.conj : TwE6GraphFixedGalois f →*
      MulAut (TwE6GraphFixedGalois f)).range := by
  classical
  let K := GaloisField 2 (2 * f)
  let σE : K ≃+* K := frobQEquiv hf
  let σ : K →+* K := frobQ 2 f
  set I : Subgroup (MulAut (TwE6GraphFixedGalois f)) :=
    (MulAut.conj : TwE6GraphFixedGalois f →* MulAut (TwE6GraphFixedGalois f)).range with hI
  haveI hIn : I.Normal := RootCentExc.normal_range_mulAutConj
  have hK : Nat.card K = (2 ^ f) ^ 2 := TwE6Toral.card_galoisField_two_mul f hf
  have hσ : ∀ c : K, σE c = c ^ 2 ^ f := frobQ_apply 2 f
  obtain ⟨-, -, -, -, -, -, -, -, ⟨Θ, hΘ, hsurj, hker, hab, hexp, hout⟩, hfield, -, -, -⟩ :=
    twisted_E6_all_characteristic_exact_automorphism_normal_form Nat.prime_two hf K hK σE hσ
  have hker' : Θ.ker = LayerSixE.twInndiagAut f := by
    rw [hker]
    change twistedE6Inn K σE ⊔ twistedE6Diag K σE =
      (MulAut.conj : twistedE6RootGroup K σE →* MulAut (twistedE6RootGroup K σE)).range ⊔
        (RootCentExc.compatParamAut σE.toRingHom).range
    rw [range_compatParamAut_eq_twistedE6Diag]
    rfl
  have htInn : t ∉ twistedE6Inn K σE := by
    intro ht
    apply htI
    have : t ∈ Θ.ker := by
      rw [hker]
      exact Subgroup.mem_sup_left ht
    rwa [hker'] at this
  rcases hout t ht2 with htinn | ⟨hΘt, g, u, ht_eq⟩
  · exact absurd htinn htInn
  · let c : MulAut (TwE6GraphFixedGalois f) := MulAut.conj g
    let d : MulAut (TwE6GraphFixedGalois f) :=
      compatDiagAutHom TwistTag.E6 K σE.toRingHom u
    let η : MulAut (TwE6GraphFixedGalois f) := etaAut σ (frobQ_frobQ 2 f hf)
    have hηeq : (fieldActor σE σE : MulAut (TwE6GraphFixedGalois f)) = η := by
      simpa [η, σ, TwE6GraphFixedGalois] using fieldActor_frobQ_eq_etaAut hf
    have ht_eqC : t = (MulAut.conj g * compatDiagAutHom TwistTag.E6 K σE.toRingHom u *
        (fieldActor σE σE : MulAut (TwE6GraphFixedGalois f))) := by
      apply MulEquiv.ext
      intro y
      exact congrArg (fun f : MulAut ↥(twistedE6RootGroup K σE) => f y) ht_eq
    have ht_eq' : t = c * d * η := by
      rw [ht_eqC, hηeq]
      rfl
    have hd : d ∈ (RootCentExc.compatParamAut σ).range := by
      have hdDiag : d ∈ twistedE6Diag K σE := ⟨u, rfl⟩
      change d ∈ (RootCentExc.compatParamAut σE.toRingHom).range
      rw [range_compatParamAut_eq_twistedE6Diag (K := K) (σ := σE)]
      exact hdDiag
    have hc : c ∈ I := ⟨g, rfl⟩
    have hxη : η * x * η⁻¹ ∈ LayerSixE.twInndiagAut f :=
      (twInndiagAut_normal hf).conj_mem x hx η
    have hηxq : QuotientGroup.mk' I (η * x * η⁻¹) = (QuotientGroup.mk' I x)⁻¹ := by
      simpa [η] using eta_conj_mk'_eq_inv_of_mem_twInndiag hf hx
    have hdiag : QuotientGroup.mk' I (d * (η * x * η⁻¹) * d⁻¹) =
        QuotientGroup.mk' I (η * x * η⁻¹) :=
      diag_conj_mk'_eq_of_mem_compatParamAut hd hxη
    have hc1 : QuotientGroup.mk' I c = 1 := by
      rw [QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff c).2 hc
    have hstep : QuotientGroup.mk' I (c * (d * (η * x * η⁻¹) * d⁻¹) * c⁻¹) =
        QuotientGroup.mk' I (d * (η * x * η⁻¹) * d⁻¹) := by
      simp only [map_mul, map_inv, hc1, one_mul, inv_one, mul_one]
    have hgroup : t * x * t⁻¹ = c * (d * (η * x * η⁻¹) * d⁻¹) * c⁻¹ := by
      rw [ht_eq']
      group
    have hconj : QuotientGroup.mk' I (t * x * t⁻¹) = (QuotientGroup.mk' I x)⁻¹ := by
      calc QuotientGroup.mk' I (t * x * t⁻¹)
          = QuotientGroup.mk' I (c * (d * (η * x * η⁻¹) * d⁻¹) * c⁻¹) :=
            congrArg (QuotientGroup.mk' I) hgroup
        _ = QuotientGroup.mk' I (d * (η * x * η⁻¹) * d⁻¹) := hstep
        _ = QuotientGroup.mk' I (η * x * η⁻¹) := hdiag
        _ = (QuotientGroup.mk' I x)⁻¹ := hηxq
    have hxfix : t * x * t⁻¹ = x := by
      rw [hxt]
      group
    have hclass : QuotientGroup.mk' I x = (QuotientGroup.mk' I x)⁻¹ := by
      rw [← hconj, hxfix]
    have hx2 : (QuotientGroup.mk' I x) ^ 2 = 1 := by
      calc (QuotientGroup.mk' I x) ^ 2 = (QuotientGroup.mk' I x) * (QuotientGroup.mk' I x) :=
            pow_two _
        _ = (QuotientGroup.mk' I x) * (QuotientGroup.mk' I x)⁻¹ :=
            congrArg (fun z => (QuotientGroup.mk' I x) * z) hclass
        _ = 1 := mul_inv_cancel _
    have hx3 : (QuotientGroup.mk' I x) ^ 3 = 1 :=
      pow_three_mk'_eq_one_of_mem_twInndiag hf hx
    have hx1 : QuotientGroup.mk' I x = 1 := by
      have hdvd : orderOf (QuotientGroup.mk' I x) ∣ 1 := by
        have h2 : orderOf (QuotientGroup.mk' I x) ∣ 2 :=
          orderOf_dvd_of_pow_eq_one (by simpa [pow_two] using hx2)
        have h3 : orderOf (QuotientGroup.mk' I x) ∣ 3 :=
          orderOf_dvd_of_pow_eq_one hx3
        have := Nat.dvd_gcd h2 h3
        simpa using this
      exact orderOf_eq_one_iff.1 (Nat.dvd_one.1 hdvd)
    have hxI : x ∈ I := by
      rw [QuotientGroup.mk'_apply] at hx1
      exact (QuotientGroup.eq_one_iff x).1 hx1
    simpa [hI] using hxI

