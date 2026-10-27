module

public import CFSG.LocalAnalysis.StandardType.GGQTwoNbrRecAux
public import CFSG.LocalAnalysis.StandardType.GGTableBRank
public import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType

variable {G Q : Type} [Group G] [Group Q] {K Bs : Subgroup G}

@[expose] def qTwoNbrRec_Kb (q : ↥(K ⊔ Bs) →* Q) : Subgroup Q :=
  (q.comp (Subgroup.inclusion le_sup_left)).range

@[expose] def qTwoNbrRec_kappa (q : ↥(K ⊔ Bs) →* Q) : ↥K →* ↥(qTwoNbrRec_Kb q) :=
  (q.comp (Subgroup.inclusion le_sup_left)).rangeRestrict

theorem qTwoNbrRec_kappa_surjective (q : ↥(K ⊔ Bs) →* Q) :
    Function.Surjective (qTwoNbrRec_kappa q) :=
  MonoidHom.rangeRestrict_surjective _

theorem qTwoNbrRec_kappa_coe (q : ↥(K ⊔ Bs) →* Q) (k : ↥K) :
    ((qTwoNbrRec_kappa q k : ↥(qTwoNbrRec_Kb q)) : Q) = q ⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ :=
  rfl

theorem qTwoNbrRec_kappa_ker (q : ↥(K ⊔ Bs) →* Q)
    (hq : q.ker = (qTwoNbrRec_Delta K).subgroupOf (K ⊔ Bs)) :
    (qTwoNbrRec_kappa q).ker = (qTwoNbrRec_Delta K).subgroupOf K := by
  ext k
  rw [MonoidHom.mem_ker]
  constructor
  · intro h
    rw [Subgroup.mem_subgroupOf]
    have hqk : q ⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ = 1 := by
      have h' := congrArg (fun x : ↥(qTwoNbrRec_Kb q) => (x : Q)) h
      rwa [qTwoNbrRec_kappa_coe, Subgroup.coe_one] at h'
    have hmem : (⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ : ↥(K ⊔ Bs)) ∈ q.ker := by
      rw [MonoidHom.mem_ker]
      exact hqk
    rw [hq] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  · intro h
    rw [Subgroup.mem_subgroupOf] at h
    have hmem : (⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ : ↥(K ⊔ Bs)) ∈ q.ker := by
      rw [hq]
      exact Subgroup.mem_subgroupOf.mpr h
    rw [MonoidHom.mem_ker] at hmem
    apply Subtype.ext
    show (q ⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ : Q) = 1
    exact hmem

theorem qTwoNbrRec_Kb_perfect (q : ↥(K ⊔ Bs) →* Q) (hperf : commutator ↥K = ⊤) :
    commutator ↥(qTwoNbrRec_Kb q) = ⊤ := by
  have hrange : (qTwoNbrRec_kappa q).range = ⊤ :=
    MonoidHom.range_eq_top.mpr (qTwoNbrRec_kappa_surjective q)
  have hmap : (commutator ↥K).map (qTwoNbrRec_kappa q) = commutator ↥(qTwoNbrRec_Kb q) := by
    rw [commutator_def, commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      hrange]
  rw [← hmap, hperf]
  exact Subgroup.map_top_of_surjective _ (qTwoNbrRec_kappa_surjective q)

theorem qTwoNbrRec_exists_psiBar [Finite G] {R : Type} [Group R] (q : ↥(K ⊔ Bs) →* Q)
    (hq : q.ker = (qTwoNbrRec_Delta K).subgroupOf (K ⊔ Bs))
    (θ : ↥K ⧸ Subgroup.center ↥K ≃* R) :
    ∃ ψ : ↥(qTwoNbrRec_Kb q) →* R,
      (∀ k : ↥K, ψ (qTwoNbrRec_kappa q k) = ggQuotHom θ k) ∧ Function.Surjective ψ ∧
        ψ.ker ≤ Subgroup.center ↥(qTwoNbrRec_Kb q) ∧ ∀ y ∈ ψ.ker, y ^ 2 = 1 → y = 1 := by
  have hκker : (qTwoNbrRec_kappa q).ker = (qTwoNbrRec_Delta K).subgroupOf K :=
    qTwoNbrRec_kappa_ker q hq
  have hle : (qTwoNbrRec_kappa q).ker ≤ (ggQuotHom θ).ker := by
    intro z hz
    rw [hκker] at hz
    have hzΔ : (z : G) ∈ qTwoNbrRec_Delta K := Subgroup.mem_subgroupOf.mp hz
    rw [ker_ggQuotHom]
    exact Subgroup.mem_center_iff.mpr
      (fun k => Subtype.ext (qTwoNbrRec_Delta_central hzΔ (k : G) k.2).symm)
  let ψ : ↥(qTwoNbrRec_Kb q) →* R :=
    MonoidHom.liftOfRightInverse (qTwoNbrRec_kappa q)
      (Function.surjInv (qTwoNbrRec_kappa_surjective q))
      (Function.rightInverse_surjInv (qTwoNbrRec_kappa_surjective q)) ⟨ggQuotHom θ, hle⟩
  have hψ : ∀ k : ↥K, ψ (qTwoNbrRec_kappa q k) = ggQuotHom θ k := fun k =>
    MonoidHom.liftOfRightInverse_comp_apply (f := qTwoNbrRec_kappa q)
      (f_inv := Function.surjInv (qTwoNbrRec_kappa_surjective q))
      (Function.rightInverse_surjInv (qTwoNbrRec_kappa_surjective q)) ⟨ggQuotHom θ, hle⟩ k
  refine ⟨ψ, hψ, ?_, ?_, ?_⟩
  · intro r
    obtain ⟨k, hk⟩ := ggQuotHom_surjective θ r
    exact ⟨qTwoNbrRec_kappa q k, by rw [hψ, hk]⟩
  · intro y hy
    obtain ⟨z, rfl⟩ := qTwoNbrRec_kappa_surjective q y
    have hz : z ∈ (ggQuotHom θ).ker := by
      rw [MonoidHom.mem_ker, ← hψ z]
      exact MonoidHom.mem_ker.mp hy
    rw [ker_ggQuotHom] at hz
    rw [Subgroup.mem_center_iff]
    intro w
    obtain ⟨k, rfl⟩ := qTwoNbrRec_kappa_surjective q w
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz k]
  · intro y hy hy2
    obtain ⟨z, rfl⟩ := qTwoNbrRec_kappa_surjective q y
    have hz : z ∈ (ggQuotHom θ).ker := by
      rw [MonoidHom.mem_ker, ← hψ z]
      exact MonoidHom.mem_ker.mp hy
    rw [ker_ggQuotHom] at hz
    have hz2 : z ^ 2 ∈ (qTwoNbrRec_kappa q).ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hy2
    rw [hκker] at hz2
    have hw : (z : G) ^ 2 ∈ qTwoNbrRec_Delta K := Subgroup.mem_subgroupOf.mp hz2
    obtain ⟨n, hn⟩ := (qTwoNbrRec_mem_Delta_iff.mp hw).2.2
    have hc : ∀ k ∈ K, (z : G) * k = k * (z : G) := fun k hk =>
      (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)).symm
    have hzd : (z : G) ∈ qTwoNbrRec_Delta K := by
      refine qTwoNbrRec_mem_Delta_of_pow z.2 hc (n := n + 1) ?_
      have hpow : (z : G) ^ 2 ^ (n + 1) = ((z : G) ^ 2) ^ 2 ^ n := by
        rw [pow_succ, mul_comm, pow_mul]
      rw [hpow, hn]
    have hzmem : z ∈ (qTwoNbrRec_kappa q).ker := by
      rw [hκker]
      exact Subgroup.mem_subgroupOf.mpr hzd
    exact MonoidHom.mem_ker.mp hzmem

theorem qTwoNbrRec_mem_normalizer_Kb (q : ↥(K ⊔ Bs) →* Q)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) {b : G} (hb : b ∈ Bs) :
    q ⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) hb⟩ ∈
      Subgroup.normalizer ((qTwoNbrRec_Kb q : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff]
  intro l
  constructor
  · intro hl
    rw [qTwoNbrRec_Kb, MonoidHom.mem_range] at hl
    obtain ⟨k, rfl⟩ := hl
    rw [qTwoNbrRec_Kb, MonoidHom.mem_range]
    have hmem : b * (k : G) * b⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hN hb) (k : G)).mp k.2
    refine ⟨⟨b * (k : G) * b⁻¹, hmem⟩, ?_⟩
    have harg : (⟨b * (k : G) * b⁻¹, (le_sup_left : K ≤ K ⊔ Bs) hmem⟩ :
          ↥(K ⊔ Bs)) =
        (⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) hb⟩ : ↥(K ⊔ Bs)) *
          (⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ : ↥(K ⊔ Bs)) *
          (⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) hb⟩ : ↥(K ⊔ Bs))⁻¹ :=
      Subtype.ext rfl
    change q (⟨b * (k : G) * b⁻¹, (le_sup_left : K ≤ K ⊔ Bs) hmem⟩ :
        ↥(K ⊔ Bs)) =
      q ⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) hb⟩ *
        q ⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ *
        (q ⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) hb⟩)⁻¹
    rw [harg, map_mul, map_mul, map_inv]
  · intro hl
    rw [qTwoNbrRec_Kb, MonoidHom.mem_range] at hl
    obtain ⟨k, hk⟩ := hl
    rw [qTwoNbrRec_Kb, MonoidHom.mem_range]
    have hmem : b⁻¹ * (k : G) * b ∈ K := by
      simpa using (Subgroup.mem_normalizer_iff.mp (hN (Bs.inv_mem hb)) (k : G)).mp k.2
    refine ⟨⟨b⁻¹ * (k : G) * b, hmem⟩, ?_⟩
    have harg : (⟨b⁻¹ * (k : G) * b, (le_sup_left : K ≤ K ⊔ Bs) hmem⟩ :
          ↥(K ⊔ Bs)) =
        (⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) hb⟩ : ↥(K ⊔ Bs))⁻¹ *
          (⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ : ↥(K ⊔ Bs)) *
          (⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) hb⟩ : ↥(K ⊔ Bs)) :=
      Subtype.ext rfl
    change q (⟨b⁻¹ * (k : G) * b, (le_sup_left : K ≤ K ⊔ Bs) hmem⟩ :
        ↥(K ⊔ Bs)) = l
    rw [harg, map_mul, map_mul, map_inv]
    have hk' : q (⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ : ↥(K ⊔ Bs)) =
        q ⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) hb⟩ * l *
          (q ⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) hb⟩)⁻¹ := hk
    rw [hk']
    group

@[expose] noncomputable def qTwoNbrRec_gammaB (q : ↥(K ⊔ Bs) →* Q)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) : ↥Bs →* MulAut ↥(qTwoNbrRec_Kb q) :=
  (Subgroup.normalizerMonoidHom (qTwoNbrRec_Kb q)).comp
    (MonoidHom.codRestrict (q.comp (Subgroup.inclusion (le_sup_right : Bs ≤ K ⊔ Bs)))
      (Subgroup.normalizer ((qTwoNbrRec_Kb q : Subgroup Q) : Set Q))
      (fun b => qTwoNbrRec_mem_normalizer_Kb q hN b.2))

theorem qTwoNbrRec_gammaB_coe (q : ↥(K ⊔ Bs) →* Q) (hN : Bs ≤ Subgroup.normalizer (K : Set G))
    (b : ↥Bs) (l : ↥(qTwoNbrRec_Kb q)) :
    ((qTwoNbrRec_gammaB q hN b l : ↥(qTwoNbrRec_Kb q)) : Q) =
      q ⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) b.2⟩ * (l : Q) *
        (q ⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) b.2⟩)⁻¹ :=
  rfl

theorem qTwoNbrRec_psiBar_gamma [Finite G] {R : Type} [Group R] (q : ↥(K ⊔ Bs) →* Q)
    (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (θ : ↥K ⧸ Subgroup.center ↥K ≃* R)
    (ψ : ↥(qTwoNbrRec_Kb q) →* R)
    (hψ : ∀ k : ↥K, ψ (qTwoNbrRec_kappa q k) = ggQuotHom θ k) (b : ↥Bs)
    (l : ↥(qTwoNbrRec_Kb q)) :
    ψ (qTwoNbrRec_gammaB q hN b l) = ggBeta K θ hN b (ψ l) := by
  obtain ⟨k, rfl⟩ := qTwoNbrRec_kappa_surjective q l
  have hγ : qTwoNbrRec_gammaB q hN b (qTwoNbrRec_kappa q k) =
      qTwoNbrRec_kappa q (ggGamma K hN b k) := by
    apply Subtype.ext
    rw [qTwoNbrRec_gammaB_coe, qTwoNbrRec_kappa_coe, qTwoNbrRec_kappa_coe]
    have harg : (⟨(ggGamma K hN b k : ↥K),
          (le_sup_left : K ≤ K ⊔ Bs) (ggGamma K hN b k).2⟩ : ↥(K ⊔ Bs)) =
        (⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) b.2⟩ : ↥(K ⊔ Bs)) *
          (⟨k, (le_sup_left : K ≤ K ⊔ Bs) k.2⟩ : ↥(K ⊔ Bs)) *
          (⟨b, (le_sup_right : Bs ≤ K ⊔ Bs) b.2⟩ : ↥(K ⊔ Bs))⁻¹ :=
      Subtype.ext (by
        change ((ggGamma K hN b k : ↥K) : G) = b * (k : G) * b⁻¹
        rw [ggGamma_coe, Subgroup.coe_inv])
    rw [harg, map_mul, map_mul, map_inv]
  rw [hγ]
  rw [hψ (ggGamma K hN b k), hψ k]
  exact (ggBeta_ggQuotHom (L := K) (hBN := hN) θ b k).symm

end CFSG.StandardType.QTwo

end
