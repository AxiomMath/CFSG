module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps6L2Transport
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsHilbert90
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsFieldCentPGL
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofL2
public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonSplitTorusMatrices
public import CFSG.LocalAnalysis.ComponentClassification.AutL2FactsSubfield

public section

namespace CFSG.LocalAnalysis.WeakClosure81.Asch6

open Subgroup CFSG.GorensteinWalter CFSG.ComponentClassification.AutL2Facts
open scoped commutatorElement

private theorem intCast_of_mul_mem {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime)
    {H : AddSubgroup K} (hH : H.index = p) {c : K} (hc : ∀ x ∈ H, c * x ∈ H) :
    ∃ m : ℤ, c = (m : K) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hquot : Nat.card (K ⧸ H) = p := by
    rw [← AddSubgroup.index_eq_card, hH]
  have htop : (⊤ : AddSubgroup K).index = 1 := AddSubgroup.index_top
  have hne_top : H ≠ ⊤ := by
    intro h
    rw [h, htop] at hH
    exact hp.ne_one hH.symm
  obtain ⟨x₀, hx₀⟩ : ∃ x : K, x ∉ H := by
    by_contra h
    push Not at h
    exact hne_top (le_antisymm le_top fun x _ => h x)
  have hx₀q : QuotientAddGroup.mk' H x₀ ≠ 0 := by
    change (x₀ : K ⧸ H) ≠ 0
    exact fun h => hx₀ ((QuotientAddGroup.eq_zero_iff x₀).mp h)
  have hzmultiples : ∀ x : K, ∃ n : ℤ, x - n • x₀ ∈ H := by
    intro x
    have hx : QuotientAddGroup.mk' H x ∈
        AddSubgroup.zmultiples (QuotientAddGroup.mk' H x₀) :=
      mem_zmultiples_of_prime_card hquot hx₀q
    rw [AddSubgroup.mem_zmultiples_iff] at hx
    obtain ⟨n, hn⟩ := hx
    refine ⟨n, ?_⟩
    have h : QuotientAddGroup.mk' H x = QuotientAddGroup.mk' H (n • x₀) := by
      rw [map_zsmul]
      exact hn.symm
    exact QuotientAddGroup.eq_iff_sub_mem.mp h
  have hcx₀ : QuotientAddGroup.mk' H (c * x₀) ∈
      AddSubgroup.zmultiples (QuotientAddGroup.mk' H x₀) :=
    mem_zmultiples_of_prime_card hquot hx₀q
  rw [AddSubgroup.mem_zmultiples_iff] at hcx₀
  obtain ⟨m, hm⟩ := hcx₀
  have hmclass : QuotientAddGroup.mk' H ((m : K) * x₀) =
      QuotientAddGroup.mk' H (c * x₀) := by
    rw [show ((m : K) * x₀) = m • x₀ by rw [zsmul_eq_mul]]
    rw [map_zsmul]
    exact hm
  have hcx₀H : (c - (m : K)) * x₀ ∈ H := by
    have hmem0 : (m : K) * x₀ - c * x₀ ∈ H := QuotientAddGroup.eq_iff_sub_mem.mp hmclass
    have hmem : c * x₀ - (m : K) * x₀ ∈ H := by simpa [neg_sub] using H.neg_mem hmem0
    simpa [sub_mul] using hmem
  have hcsub : ∀ x : K, (c - (m : K)) * x ∈ H := by
    intro x
    obtain ⟨n, hn⟩ := hzmultiples x
    have hxeq : x = n • x₀ + (x - n • x₀) := by abel
    rw [hxeq, mul_add, zsmul_eq_mul]
    have h1 : (n : K) * ((c - (m : K)) * x₀) ∈ H := AddSubgroup.int_mul_mem n hcx₀H
    have hcH : c * (x - n • x₀) ∈ H := hc _ hn
    have hmH : (m : K) * (x - n • x₀) ∈ H := AddSubgroup.int_mul_mem m hn
    have h2 : (c - (m : K)) * (x - n • x₀) ∈ H := by
      rw [sub_mul]
      exact H.sub_mem hcH hmH
    convert AddSubgroup.add_mem _ h1 h2 using 1
    ring
  by_contra hne
  have hne' : c - (m : K) ≠ 0 := sub_ne_zero.mpr fun h => hne ⟨m, h⟩
  apply hne_top
  rw [eq_top_iff]
  intro x _
  have hx : x = (c - (m : K)) * ((c - (m : K))⁻¹ * x) := by field_simp
  rw [hx]
  exact hcsub _

private def scaleAdd {K : Type} [Field K] (c : K) (H : AddSubgroup K) : AddSubgroup K :=
  H.map (AddMonoidHom.mulLeft c)

private theorem scaleAdd_one {K : Type} [Field K] (H : AddSubgroup K) :
    scaleAdd (1 : K) H = H := by
  rw [scaleAdd]
  convert AddSubgroup.map_id H using 2
  ext x
  simp

private theorem scaleAdd_scaleAdd {K : Type} [Field K] (c d : K) (H : AddSubgroup K) :
    scaleAdd c (scaleAdd d H) = scaleAdd (c * d) H := by
  rw [scaleAdd, scaleAdd, scaleAdd, AddSubgroup.map_map]
  congr 1
  ext x
  simp [mul_assoc]

private theorem scaleAdd_map {K : Type} [Field K] (c : K) (σ : K ≃+* K)
    (H : AddSubgroup K) :
    (scaleAdd c H).map σ.toAddMonoidHom =
      scaleAdd (σ c) (H.map σ.toAddMonoidHom) := by
  rw [scaleAdd, scaleAdd, AddSubgroup.map_map]
  rw [AddSubgroup.map_map]
  congr 1
  ext x
  simp

private theorem mul_mem_of_scaleAdd_eq_self {K : Type} [Field K] {c : K} {H : AddSubgroup K}
    (h : scaleAdd c H = H) : ∀ x ∈ H, c * x ∈ H := by
  intro x hx
  have hx' : c * x ∈ scaleAdd c H := by
    exact AddSubgroup.mem_map.mpr ⟨x, hx, rfl⟩
  rwa [h] at hx'

private theorem exists_scale_not_sigma_invariant {K : Type} [Field K] [Finite K]
    {r p : ℕ} (hp : p.Prime) (hr5 : 5 ≤ r) (hKcard : Nat.card K = r ^ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = 2) {K₀ : Subfield K}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (hK₀card : Nat.card K₀ = r)
    {H : AddSubgroup K} (hH : H.index = p) :
    ∃ mu : Kˣ, (scaleAdd (((mu : K) ^ 2)) H).map σ.toAddMonoidHom ≠
      scaleAdd (((mu : K) ^ 2)) H := by
  classical
  by_contra hcontra
  push Not at hcontra
  have hHfix : H.map σ.toAddMonoidHom = H := by
    have h1 := hcontra 1
    have h2 : scaleAdd (((1 : Kˣ) : K) ^ 2) H = H := by
      rw [show (((1 : Kˣ) : K) ^ 2) = (1 : K) by simp, scaleAdd_one]
    rwa [h2] at h1
  have hscale : ∀ mu : Kˣ, scaleAdd (σ ((mu : K) ^ 2)) H =
      scaleAdd ((mu : K) ^ 2) H := by
    intro mu
    have h1 := hcontra mu
    rwa [scaleAdd_map, hHfix] at h1
  have hgscale : ∀ mu : Kˣ, scaleAdd (σ ((mu : K) ^ 2) / (mu : K) ^ 2) H = H := by
    intro mu
    have h1 := hscale mu
    have hb : (mu : K) ^ 2 ≠ 0 := pow_ne_zero 2 (Units.ne_zero mu)
    calc scaleAdd (σ ((mu : K) ^ 2) / (mu : K) ^ 2) H
        = scaleAdd (((mu : K) ^ 2)⁻¹) (scaleAdd (σ ((mu : K) ^ 2)) H) := by
          rw [div_eq_inv_mul, ← scaleAdd_scaleAdd]
      _ = scaleAdd (((mu : K) ^ 2)⁻¹) (scaleAdd ((mu : K) ^ 2) H) := by rw [h1]
      _ = scaleAdd (((mu : K) ^ 2)⁻¹ * (mu : K) ^ 2) H := by rw [scaleAdd_scaleAdd]
      _ = H := by rw [inv_mul_cancel₀ hb, scaleAdd_one]
  have hgmul : ∀ mu : Kˣ, ∀ x ∈ H, (σ ((mu : K) ^ 2) / (mu : K) ^ 2) * x ∈ H :=
    fun mu => mul_mem_of_scaleAdd_eq_self (hgscale mu)
  have hpow4 : ∀ mu : Kˣ, (σ (mu : K) / (mu : K)) ^ 4 = 1 := by
    intro mu
    obtain ⟨m, hm⟩ := intCast_of_mul_mem hp hH (hgmul mu)
    have hσg : σ (σ ((mu : K) ^ 2) / (mu : K) ^ 2) =
        σ ((mu : K) ^ 2) / (mu : K) ^ 2 := by
      rw [hm]
      exact map_intCast σ m
    have hσσ : ∀ x : K, σ (σ x) = x := by
      have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
      intro x
      simpa using congrArg (fun τ : K ≃+* K => τ x) h1
    have hσginv : σ (σ ((mu : K) ^ 2) / (mu : K) ^ 2) =
        (σ ((mu : K) ^ 2) / (mu : K) ^ 2)⁻¹ := by
      rw [map_div₀, hσσ]
      field_simp
    have hginv : σ ((mu : K) ^ 2) / (mu : K) ^ 2 =
        (σ ((mu : K) ^ 2) / (mu : K) ^ 2)⁻¹ := hσg.symm.trans hσginv
    have hb : (mu : K) ^ 2 ≠ 0 := pow_ne_zero 2 (Units.ne_zero mu)
    have hg0 : σ ((mu : K) ^ 2) / (mu : K) ^ 2 ≠ 0 :=
      div_ne_zero ((map_ne_zero σ).mpr (pow_ne_zero 2 (Units.ne_zero mu))) hb
    have hgsq : (σ ((mu : K) ^ 2) / (mu : K) ^ 2) ^ 2 = 1 := by
      rw [pow_two]
      calc (σ ((mu : K) ^ 2) / (mu : K) ^ 2) *
          (σ ((mu : K) ^ 2) / (mu : K) ^ 2)
          = (σ ((mu : K) ^ 2) / (mu : K) ^ 2) *
            (σ ((mu : K) ^ 2) / (mu : K) ^ 2)⁻¹ := by nth_rw 2 [hginv]
        _ = 1 := mul_inv_cancel₀ hg0
    have hsq : σ ((mu : K) ^ 2) / (mu : K) ^ 2 =
        (σ (mu : K) / (mu : K)) ^ 2 := by
      rw [map_pow]
      field_simp
    calc (σ (mu : K) / (mu : K)) ^ 4
        = ((σ (mu : K) / (mu : K)) ^ 2) ^ 2 := by ring
      _ = (σ ((mu : K) ^ 2) / (mu : K) ^ 2) ^ 2 := by rw [hsq]
      _ = 1 := hgsq
  let φ : Kˣ →* Kˣ :=
    (Units.map σ.toRingHom.toMonoidHom) / MonoidHom.id Kˣ
  have hφapply : ∀ u : Kˣ, (φ u : K) = σ (u : K) / (u : K) := by
    intro u
    simp [φ]
  have hker : φ.ker = (Units.map K₀.subtype.toMonoidHom).range := by
    ext u
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro hu
      have hu1 : (φ u : K) = 1 := by rw [hu]; simp
      have hfix : σ (u : K) = (u : K) := by
        have h1 : σ (u : K) / (u : K) = 1 := by rw [← hφapply]; exact hu1
        field_simp at h1
        exact h1
      refine ⟨Units.mk0 ⟨(u : K), (hK₀ _).mpr hfix⟩ ?_, Units.ext rfl⟩
      intro hzero
      exact Units.ne_zero u (congrArg Subtype.val hzero)
    · rintro ⟨v, rfl⟩
      apply Units.ext
      rw [hφapply]
      have hv : σ ((v : K₀) : K) = ((v : K₀) : K) := (hK₀ _).mp (Subtype.mem _)
      have hv0 : ((v : K₀) : K) ≠ 0 := by exact_mod_cast Units.ne_zero v
      change σ ((v : K₀) : K) / ((v : K₀) : K) = 1
      rw [hv, div_self hv0]
  have hker_card : Nat.card φ.ker = r - 1 := by
    have hinj : Function.Injective (Units.map K₀.subtype.toMonoidHom) :=
      Units.map_injective K₀.subtype_injective
    rw [hker, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_units, hK₀card]
  have hrange_le : φ.range ≤ rootsOfUnity 4 K := by
    rintro v ⟨u, rfl⟩
    rw [mem_rootsOfUnity]
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_one, hφapply]
    exact hpow4 u
  have hrange_card : Nat.card φ.range ≤ 4 :=
    (Subgroup.card_le_of_le hrange_le).trans (card_rootsOfUnity K 4)
  have hKunits : Nat.card Kˣ = r ^ 2 - 1 := by
    rw [Nat.card_units, hKcard]
  have hcard := Subgroup.card_ker_mul_card_range φ
  have hle : (r - 1) * (r + 1) ≤ (r - 1) * 4 := by
    calc (r - 1) * (r + 1) = r ^ 2 - 1 := by
          rw [mul_comm, ← Nat.sq_sub_sq r 1, one_pow]
      _ = Nat.card Kˣ := hKunits.symm
      _ = Nat.card φ.ker * Nat.card φ.range := hcard.symm
      _ = (r - 1) * Nat.card φ.range := by rw [hker_card]
      _ ≤ (r - 1) * 4 := Nat.mul_le_mul_left _ hrange_card
  have hpos : 0 < r - 1 := by omega
  have hle4 : r + 1 ≤ 4 := Nat.le_of_mul_le_mul_left hle hpos
  omega

private def rootHom (K : Type) [Field K] : Multiplicative K →* PGammaL2 K :=
  (incl K).comp (psl2UpperUnipotentHom K)

private theorem psl2FieldAut_upperUnipotent {K : Type} [Field K] (σ : K ≃+* K) (x : K) :
    psl2FieldAut K σ (psl2UpperUnipotentHom K (Multiplicative.ofAdd x)) =
      psl2UpperUnipotentHom K (Multiplicative.ofAdd (σ x)) := by
  rw [CFSG.RankThree.PartTwo.Sec8.Item82OneProof.psl2UpperUnipotentHom_ofAdd,
    CFSG.RankThree.PartTwo.Sec8.Item82OneProof.psl2UpperUnipotentHom_ofAdd,
    psl2FieldAut_apply]
  show psl2RingEquiv σ (QuotientGroup.mk' (Subgroup.center
      (Matrix.SpecialLinearGroup (Fin 2) K)) (sl2UpperUnipotent x)) =
    psl2QuotientMap K (sl2UpperUnipotent (σ x))
  rw [psl2RingEquiv_mk]
  congr 1
  ext i j
  change σ ((!![1, x; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j) =
    (!![1, σ x; 0, 1] : Matrix (Fin 2) (Fin 2) K) i j
  fin_cases i <;> fin_cases j <;> simp

private theorem conj_inr_root {K : Type} [Field K] [Finite K] (σ : K ≃+* K) (x : K) :
    SemidirectProduct.inr σ * rootHom K (Multiplicative.ofAdd x) * (SemidirectProduct.inr σ)⁻¹ =
      rootHom K (Multiplicative.ofAdd (σ x)) := by
  change SemidirectProduct.inr σ * incl K (psl2UpperUnipotentHom K
      (Multiplicative.ofAdd x)) * (SemidirectProduct.inr σ)⁻¹ =
    incl K (psl2UpperUnipotentHom K (Multiplicative.ofAdd (σ x)))
  rw [conj_incl,
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inr,
    psl2FieldAut_upperUnipotent]

private theorem conj_diag_root {K : Type} [Field K] [Finite K] (mu : Kˣ) (x : K) :
    incl K (psl2QuotientMap K (CFSG.Glauberman.Dickson.splitTorusSLHom K mu)) *
        rootHom K (Multiplicative.ofAdd x) *
        (incl K (psl2QuotientMap K (CFSG.Glauberman.Dickson.splitTorusSLHom K mu)))⁻¹ =
      rootHom K (Multiplicative.ofAdd ((mu : K) ^ 2 * x)) := by
  change incl K (psl2QuotientMap K (CFSG.Glauberman.Dickson.splitTorusSLHom K mu)) *
        incl K (psl2UpperUnipotentHom K (Multiplicative.ofAdd x)) *
        (incl K (psl2QuotientMap K (CFSG.Glauberman.Dickson.splitTorusSLHom K mu)))⁻¹ =
      incl K (psl2UpperUnipotentHom K (Multiplicative.ofAdd ((mu : K) ^ 2 * x)))
  rw [conj_incl]
  simp only [incl_apply]
  rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inl,
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.pglAction_toPGL,
    MulAut.conj_apply]
  congr 1
  rw [CFSG.RankThree.PartTwo.Sec8.Item82OneProof.psl2UpperUnipotentHom_ofAdd,
    CFSG.RankThree.PartTwo.Sec8.Item82OneProof.psl2UpperUnipotentHom_ofAdd]
  have hB : CFSG.Glauberman.Dickson.splitTorusSLHom K mu ∈ sl2Borel K := by
    rw [sl2Borel, sl2_mem_stabilizer_infinity_iff]
    change ((!![(mu : K), 0; 0, (mu : K)⁻¹] : Matrix (Fin 2) (Fin 2) K)) 1 0 = 0
    simp
  have h := sl2Borel_conj_upperUnipotent hB x
  have h00 : ((CFSG.Glauberman.Dickson.splitTorusSLHom K mu :
      Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) 0 0 =
      (mu : K) := by
    change ((!![(mu : K), 0; 0, (mu : K)⁻¹] : Matrix (Fin 2) (Fin 2) K)) 0 0 = (mu : K)
    simp
  rw [h00] at h
  rw [(Matrix.ProjectiveSpecialLinearGroup.toPGL_injective (n := Fin 2) (R := K)).eq_iff]
  calc psl2QuotientMap K (CFSG.Glauberman.Dickson.splitTorusSLHom K mu) *
      psl2QuotientMap K (sl2UpperUnipotent x) *
      (psl2QuotientMap K (CFSG.Glauberman.Dickson.splitTorusSLHom K mu))⁻¹
      = psl2QuotientMap K (CFSG.Glauberman.Dickson.splitTorusSLHom K mu *
          sl2UpperUnipotent x *
          (CFSG.Glauberman.Dickson.splitTorusSLHom K mu)⁻¹) := by
        rw [map_mul, map_mul, map_inv]
    _ = psl2QuotientMap K (sl2UpperUnipotent ((mu : K) ^ 2 * x)) := by rw [h]

private def psl2SubRange {K : Type} [Field K] (K₀ : Subfield K) : Subgroup (PGammaL2 K) :=
  ((incl K).comp (psl2Sub K₀)).range

private theorem psl2SubRange_groupFacts {K : Type} [Field K] [Finite K]
    {r : ℕ} (hr : IsOddPrimePower r) (hr5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = 2) {K₀ : Subfield K}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (hcard : Nat.card K = Nat.card K₀ ^ 2)
    (hK₀card : Nat.card K₀ = r)
    (h90 : ∀ c : K, c * σ c = 1 → ∃ y : Kˣ, (y : K) / σ y = c) :
    IsSimpleGroup ↥(psl2SubRange K₀) ∧
    psl2SubRange K₀ ≤ pGammaL2PSLRange K ⊓ Subgroup.centralizer {SemidirectProduct.inr σ} ∧
    ((psl2SubRange K₀).subgroupOf (pGammaL2PSLRange K ⊓ Subgroup.centralizer
      {SemidirectProduct.inr σ})).index = 2 ∧
    (pGammaL2PSLRange K ⊓ Subgroup.centralizer {SemidirectProduct.inr σ}) ≤
      Subgroup.normalizer (psl2SubRange K₀ : Set (PGammaL2 K)) ∧
    pGammaL2PSLRange K ⊓ Subgroup.centralizer (psl2SubRange K₀ : Set (PGammaL2 K)) = ⊥ := by
  classical
  obtain ⟨p, a, hp, hpodd, ha, hr_eq⟩ := hr
  have hoddK : IsOddPrimePower (Nat.card K) := by
    refine ⟨p, 2 * a, hp, hpodd, by omega, ?_⟩
    rw [hK, hr_eq]
    rw [show (p ^ a) ^ 2 = p ^ (2 * a) by rw [← pow_mul, Nat.mul_comm]]
  have hK₀odd : IsOddPrimePower (Nat.card K₀) :=
    ⟨p, a, hp, hpodd, ha, by rw [hK₀card, hr_eq]⟩
  have hσ1 : σ ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hσ
    norm_num at hσ
  have hσσ : ∀ x : K, σ (σ x) = x := by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
    intro x
    simpa using congrArg (fun τ : K ≃+* K => τ x) h1
  set v : PGammaL2 K := SemidirectProduct.inr σ with hv
  set L := pGammaL2PSLRange K with hL
  have hLn : L.Normal := pGammaL2PSLRange_normal K hoddK (by rw [hK]; nlinarith)
  set ι : PSL2 K₀ →* PGammaL2 K := (incl K).comp (psl2Sub K₀) with hι
  have hιinj : Function.Injective ι := (incl_injective K).comp (psl2Sub_injective K₀)
  let e : PSL2 K₀ ≃* ↥ι.range := MonoidHom.ofInjective hιinj
  have hsimple : IsSimpleGroup ↥(psl2SubRange K₀) := by
    change IsSimpleGroup ↥ι.range
    have h4 : 4 ≤ Nat.card K₀ := by rw [hK₀card]; omega
    letI : IsSimpleGroup (PSL2 K₀) := Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
    exact e.symm.isSimpleGroup
  have hL₀C : ι.range ≤ Subgroup.centralizer {v} := by
    rintro _ ⟨x, rfl⟩
    change incl K (psl2Sub K₀ x) ∈ Subgroup.centralizer {v}
    rw [Subgroup.mem_centralizer_singleton_iff, eq_comm, commute_incl_iff,
      CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inr]
    simpa [fieldCent] using psl2Sub_mem_fieldCent hK₀ x
  have hL₀L : ι.range ≤ L := by
    rintro _ ⟨x, rfl⟩
    exact ⟨psl2Sub K₀ x, rfl⟩
  set C₀ := L ⊓ Subgroup.centralizer {v} with hC₀def
  have hC₀ : C₀ = (fieldCent σ).map (incl K) := by
    ext z
    constructor
    · rintro ⟨⟨y, rfl⟩, hz⟩
      refine ⟨y, ?_, rfl⟩
      have hcomm : v * incl K y = incl K y * v :=
        (Subgroup.mem_centralizer_singleton_iff.mp hz).symm
      have hfix := (commute_incl_iff v y).mp hcomm
      rw [CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inr] at hfix
      simpa [fieldCent] using hfix
    · rintro ⟨y, hy, rfl⟩
      refine ⟨⟨y, rfl⟩, ?_⟩
      change incl K y ∈ Subgroup.centralizer {v}
      rw [Subgroup.mem_centralizer_singleton_iff, eq_comm, commute_incl_iff,
        CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction_inr]
      simpa [fieldCent] using hy
  have hC₀card : Nat.card C₀ = 2 * Nat.card ι.range := by
    rw [hC₀, Subgroup.card_map_of_injective (incl_injective K),
      card_fieldCent_eq hK₀ h90 hσσ hcard hoddK, pgl2_card_eq_two_mul hK₀odd,
      ← Nat.card_congr e.toEquiv]
  have hL₀C₀ : ι.range ≤ C₀ := le_inf hL₀L hL₀C
  have hperf : Group.IsPerfect (PSL2 K₀) :=
    psl2_isPerfect_of_card_gt_three K₀ (by rw [hK₀card]; omega)
  have hperfL₀ : ⁅ι.range, ι.range⁆ = ι.range := by
    rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← _root_.commutator_def,
      hperf.commutator_eq_top]
  have hidx : (ι.range.subgroupOf C₀).index = 2 := by
    have h := (ι.range.subgroupOf C₀).card_mul_index
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hL₀C₀).toEquiv, hC₀card] at h
    exact Nat.eq_of_mul_eq_mul_left Nat.card_pos (h.trans (mul_comm _ _))
  have hcomm : ⁅C₀, C₀⁆ ≤ ι.range := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have h : ⁅(⟨a, ha⟩ : ↥C₀), ⟨b, hb⟩⁆ ∈ ι.range.subgroupOf C₀ := by
      rw [commutatorElement_def, Subgroup.mul_mem_iff_of_index_two hidx,
        Subgroup.mul_mem_iff_of_index_two hidx, Subgroup.mul_mem_iff_of_index_two hidx,
        inv_mem_iff, inv_mem_iff]
      tauto
    rw [Subgroup.mem_subgroupOf] at h
    simpa [commutatorElement_def] using h
  have hL₀eq : ι.range = ⁅C₀, C₀⁆ := by
    refine le_antisymm ?_ hcomm
    calc ι.range = ⁅ι.range, ι.range⁆ := hperfL₀.symm
      _ ≤ ⁅C₀, C₀⁆ := Subgroup.commutator_mono hL₀C₀ hL₀C₀
  have hmap : ∀ y ∈ Subgroup.centralizer {v}, C₀.map (MulAut.conj y).toMonoidHom ≤ C₀ := by
    rintro y hy _ ⟨z, hz, rfl⟩
    obtain ⟨hzL, hzC⟩ := Subgroup.mem_inf.mp hz
    exact ⟨hLn.conj_mem z hzL y, Subgroup.mul_mem _ (Subgroup.mul_mem _ hy hzC) (inv_mem hy)⟩
  have key : ∀ y ∈ Subgroup.centralizer {v}, ∀ x ∈ ι.range, y * x * y⁻¹ ∈ ι.range := by
    intro y hy x hx
    rw [hL₀eq] at hx ⊢
    have h : (⁅C₀, C₀⁆ : Subgroup (PGammaL2 K)).map (MulAut.conj y).toMonoidHom ≤
        ⁅C₀, C₀⁆ := by
      rw [Subgroup.map_commutator]
      exact Subgroup.commutator_mono (hmap y hy) (hmap y hy)
    exact h ⟨x, hx, rfl⟩
  have hN : Subgroup.centralizer {v} ≤ Subgroup.normalizer (ι.range : Set (PGammaL2 K)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨key g hg x, fun h => by simpa [mul_assoc] using key g⁻¹ (inv_mem hg) _ h⟩
  have hCL : L ⊓ Subgroup.centralizer (ι.range : Set (PGammaL2 K)) = ⊥ := by
    refine le_bot_iff.mp fun z hz => ?_
    obtain ⟨⟨y, rfl⟩, hzC⟩ := Subgroup.mem_inf.mp hz
    have hfix : ∀ g : PSL2 K₀,
        CFSG.ComponentClassification.CatalogueSchreierLinearTwo.semilinearAction K
          (incl K y) (psl2Sub K₀ g) = psl2Sub K₀ g := fun g => by
      rw [← commute_incl_iff]
      exact (Subgroup.mem_centralizer_iff.mp hzC (ι g) ⟨g, rfl⟩).symm
    rcases eq_of_fixes_psl2Sub hσ1 hK₀ hcard _ hfix with h | h
    · exact Subgroup.mem_bot.mpr h
    · exfalso
      have h1 := congrArg SemidirectProduct.right h
      rw [incl_apply, SemidirectProduct.right_inl, SemidirectProduct.right_inr] at h1
      exact hσ1 h1.symm
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact hsimple
  · change ι.range ≤ C₀
    exact hL₀C₀
  · change (ι.range.subgroupOf C₀).index = 2
    exact hidx
  · change C₀ ≤ Subgroup.normalizer (ι.range : Set (PGammaL2 K))
    exact le_trans inf_le_right hN
  · change L ⊓ Subgroup.centralizer (ι.range : Set (PGammaL2 K)) = ⊥
    exact hCL

private theorem rootHom_range_le {K : Type} [Field K] :
    (rootHom K).range ≤ pGammaL2PSLRange K := by
  rintro _ ⟨a, rfl⟩
  exact ⟨psl2UpperUnipotentHom K a, rfl⟩

private theorem rootHom_injective {K : Type} [Field K] : Function.Injective (rootHom K) :=
  (incl_injective K).comp
    (CFSG.RankThree.PartTwo.Sec8.Item82OneProof.psl2UpperUnipotentHom_injective' (K := K))

private theorem rootHom_pow_char {K : Type} [Field K] {p : ℕ} [CharP K p]
    (a : Multiplicative K) : (rootHom K a) ^ p = 1 := by
  rw [← map_pow]
  have ha : a ^ p = 1 := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_pow, toAdd_one, nsmul_eq_mul, CharP.cast_eq_zero, zero_mul]
  rw [ha, map_one]

private theorem psl2SubRange_le_quadY {K : Type} [Field K] [Finite K]
    {r : ℕ} (hr : IsOddPrimePower r) (hr5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = 2) {K₀ : Subfield K}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (hcard : Nat.card K = Nat.card K₀ ^ 2)
    (hK₀card : Nat.card K₀ = r)
    (h90 : ∀ c : K, c * σ c = 1 → ∃ y : Kˣ, (y : K) / σ y = c)
    {t : PGammaL2 K} (htI : t ∈ pGammaL2PSLRange K) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htcomm : t * SemidirectProduct.inr σ = SemidirectProduct.inr σ * t) :
    psl2SubRange K₀ ≤ quadY (closure {t, SemidirectProduct.inr σ} ⊔ pGammaL2PSLRange K)
      (closure {t, SemidirectProduct.inr σ}) (SemidirectProduct.inr σ) := by
  classical
  let v : PGammaL2 K := SemidirectProduct.inr σ
  let B : Subgroup (PGammaL2 K) := closure {t, v}
  let G : Subgroup (PGammaL2 K) := B ⊔ pGammaL2PSLRange K
  let Y : Subgroup (PGammaL2 K) := quadY G B v
  let D : Subgroup (PGammaL2 K) := psl2SubRange K₀
  obtain ⟨hDsimple, hDleC, hDidx, hDnormC, hCDbot⟩ :=
    psl2SubRange_groupFacts hr hr5 hK hσ hK₀ hcard hK₀card h90
  have htCcomm : t * v = v * t := by simpa [v] using htcomm
  have htC₀ : t ∈ pGammaL2PSLRange K ⊓ Subgroup.centralizer {v} :=
    ⟨htI, (Subgroup.mem_centralizer_singleton_iff).mpr htCcomm⟩
  have htN : t ∈ Subgroup.normalizer (D : Set (PGammaL2 K)) := hDnormC htC₀
  have htY : t ∈ Y := by
    change t ∈ quadY G B v
    have htB : t ∈ B := Subgroup.subset_closure (by simp)
    have h1 : t ∈ B.map (MulAut.conj (1 : PGammaL2 K)).toMonoidHom := by
      simpa using htB
    exact Subgroup.mem_iSup_of_mem (1 : PGammaL2 K) (Subgroup.mem_iSup_of_mem (G.one_mem)
      (Subgroup.mem_iSup_of_mem (by simp) h1))
  have hDnormY : ∀ d ∈ D, Y.map (MulAut.conj d).toMonoidHom ≤ Y := by
    intro d hd
    have hdC : d ∈ pGammaL2PSLRange K ⊓ Subgroup.centralizer {v} := hDleC hd
    have hdL : d ∈ pGammaL2PSLRange K := (Subgroup.mem_inf.mp hdC).1
    have hdG : d ∈ G := Subgroup.mem_sup_right hdL
    have hdv : d * v = v * d :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp hdC).2
    have hdvinv : d⁻¹ * v = v * d⁻¹ := by
      have h := congrArg (fun z => d⁻¹ * z * d⁻¹) hdv
      simpa [mul_assoc] using h.symm
    change (quadY G B v).map (MulAut.conj d).toMonoidHom ≤ quadY G B v
    rw [quadY]
    simp_rw [Subgroup.map_iSup]
    refine iSup_le fun x => iSup_le fun hxG => iSup_le fun hxv => ?_
    rw [Subgroup.map_map]
    have hdxG : d * x ∈ G := G.mul_mem hdG hxG
    have hdxv : (d * x) * v = v * (d * x) := by
      rw [mul_assoc, hxv, ← mul_assoc, hdv, mul_assoc]
    refine le_iSup_of_le (d * x) (le_iSup_of_le hdxG (le_iSup_of_le hdxv ?_))
    rintro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    refine Subgroup.mem_map.mpr ⟨z, hz, ?_⟩
    change (d * x) * z * (d * x)⁻¹ = d * (x * z * x⁻¹) * d⁻¹
    group
  let M : Subgroup ↥D := (Y ⊓ D).subgroupOf D
  have hMnormal : M.Normal := by
    constructor
    intro m hm d
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨hmY, hmD⟩ := Subgroup.mem_inf.mp hm
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact hDnormY (d : PGammaL2 K) d.2 ⟨m, hmY, rfl⟩
    · exact D.mul_mem (D.mul_mem d.2 hmD) (D.inv_mem d.2)
  have hMne : M ≠ ⊥ := by
    intro hbot
    have htCD : t ∈ pGammaL2PSLRange K ⊓ Subgroup.centralizer (D : Set (PGammaL2 K)) := by
      refine ⟨htI, ?_⟩
      change t ∈ Subgroup.centralizer (D : Set (PGammaL2 K))
      rw [Subgroup.mem_centralizer_iff]
      intro d hd
      have hYmem : d * t⁻¹ * d⁻¹ ∈ Y := hDnormY d hd ⟨t⁻¹, Y.inv_mem htY, rfl⟩
      have htdY : t * d * t⁻¹ * d⁻¹ ∈ Y := by
        have := Y.mul_mem htY hYmem
        simpa [mul_assoc] using this
      have htdD : t * d * t⁻¹ * d⁻¹ ∈ D := by
        have h1 : t * d * t⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp htN d).mp hd
        exact D.mul_mem h1 (D.inv_mem hd)
      let x : ↥D := ⟨_, htdD⟩
      have hxM : x ∈ M := by
        rw [Subgroup.mem_subgroupOf]
        exact ⟨htdY, htdD⟩
      rw [hbot] at hxM
      have hx1 : t * d * t⁻¹ * d⁻¹ = 1 := congrArg Subtype.val (Subgroup.mem_bot.mp hxM)
      have hdt : t * d = d * t := by
        calc t * d = (t * d * t⁻¹ * d⁻¹) * (d * t) := by group
          _ = d * t := by rw [hx1, one_mul]
      exact hdt.symm
    rw [hCDbot] at htCD
    exact ht1 (Subgroup.mem_bot.mp htCD)
  have hMtop : M = ⊤ := by
    rcases hDsimple.eq_bot_or_eq_top_of_normal M with h | h
    · exact absurd h hMne
    · exact h
  intro d hd
  have hdM : (⟨d, hd⟩ : ↥D) ∈ M := by rw [hMtop]; exact Subgroup.mem_top _
  rw [Subgroup.mem_subgroupOf] at hdM
  exact hdM.1

private def scaleHom {K : Type} [Field K] (c : K) : Multiplicative K →* Multiplicative K where
  toFun a := Multiplicative.ofAdd (c * a.toAdd)
  map_one' := by simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    simp [mul_add]

private def sigmaHom {K : Type} [Field K] (σ : K ≃+* K) :
    Multiplicative K →* Multiplicative K where
  toFun a := Multiplicative.ofAdd (σ a.toAdd)
  map_one' := by simp
  map_mul' a b := by
    apply Multiplicative.toAdd.injective
    simp

private theorem toSubgroup_scaleAdd {K : Type} [Field K] (c : K) (H : AddSubgroup K) :
    (scaleAdd c H).toSubgroup = H.toSubgroup.map (scaleHom c) := by
  ext a
  rw [Multiplicative.mem_toSubgroup]
  constructor
  · intro ha
    rw [scaleAdd] at ha
    obtain ⟨x, hx, hxa⟩ := AddSubgroup.mem_map.mp ha
    refine ⟨Multiplicative.ofAdd x, ?_, ?_⟩
    · simpa using hx
    · apply Multiplicative.toAdd.injective
      simpa [scaleHom] using hxa
  · rintro ⟨b, hb, hba⟩
    rw [scaleAdd]
    refine AddSubgroup.mem_map.mpr ⟨b.toAdd, ?_, ?_⟩
    · simpa using hb
    · simpa [scaleHom] using congrArg Multiplicative.toAdd hba

private theorem toSubgroup_map_sigma {K : Type} [Field K] (σ : K ≃+* K)
    (H : AddSubgroup K) :
    (H.map σ.toAddMonoidHom).toSubgroup = H.toSubgroup.map (sigmaHom σ) := by
  ext a
  rw [Multiplicative.mem_toSubgroup]
  constructor
  · intro ha
    obtain ⟨x, hx, hxa⟩ := AddSubgroup.mem_map.mp ha
    refine ⟨Multiplicative.ofAdd x, ?_, ?_⟩
    · simpa using hx
    · apply Multiplicative.toAdd.injective
      simpa [sigmaHom] using hxa
  · rintro ⟨b, hb, hba⟩
    refine AddSubgroup.mem_map.mpr ⟨b.toAdd, ?_, ?_⟩
    · simpa using hb
    · simpa [sigmaHom] using congrArg Multiplicative.toAdd hba

private theorem conj_diag_comp_root {K : Type} [Field K] [Finite K] (mu : Kˣ) :
    ((MulAut.conj (incl K (psl2QuotientMap K
      (CFSG.Glauberman.Dickson.splitTorusSLHom K mu)))).toMonoidHom).comp (rootHom K) =
      (rootHom K).comp (scaleHom ((mu : K) ^ 2)) := by
  apply MonoidHom.ext
  intro a
  simpa [scaleHom] using conj_diag_root mu a.toAdd

private theorem conj_inr_comp_root {K : Type} [Field K] [Finite K] (σ : K ≃+* K) :
    ((MulAut.conj (SemidirectProduct.inr σ)).toMonoidHom).comp (rootHom K) =
      (rootHom K).comp (sigmaHom σ) := by
  apply MonoidHom.ext
  intro a
  simpa [sigmaHom] using conj_inr_root σ a.toAdd

private theorem fixedRoot_le_quadY {K : Type} [Field K] [Finite K]
    {r : ℕ} (hr : IsOddPrimePower r) (hr5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = 2) {K₀ : Subfield K}
    (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x) (hcard : Nat.card K = Nat.card K₀ ^ 2)
    (hK₀card : Nat.card K₀ = r)
    (h90 : ∀ c : K, c * σ c = 1 → ∃ y : Kˣ, (y : K) / σ y = c)
    {t : PGammaL2 K} (htI : t ∈ pGammaL2PSLRange K) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htcomm : t * SemidirectProduct.inr σ = SemidirectProduct.inr σ * t) :
    (rootHom K).range ⊓ Subgroup.centralizer {SemidirectProduct.inr σ} ≤
      quadY (closure {t, SemidirectProduct.inr σ} ⊔ pGammaL2PSLRange K)
        (closure {t, SemidirectProduct.inr σ}) (SemidirectProduct.inr σ) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let p := ringChar K
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have hchar : CharP K p := ringChar.charP K
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := by
    obtain ⟨n, -, hncard⟩ := FiniteField.card K p
    have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
    have hoddPow : Odd (p ^ (n : ℕ)) := by
      have hoddCard : Odd (Nat.card K) := by
        obtain ⟨p₀, a₀, hp₀, hp₀odd, ha₀, hr₀⟩ := hr
        rw [hK, hr₀]
        exact (hp₀odd.pow).pow
      simpa [hncard] using hoddCard
    exact (Nat.odd_pow_iff hn0).mp hoddPow
  obtain ⟨-, hDleC, hDidx, -, -⟩ :=
    psl2SubRange_groupFacts hr hr5 hK hσ hK₀ hcard hK₀card h90
  have hDleY : psl2SubRange K₀ ≤
      quadY (closure {t, SemidirectProduct.inr σ} ⊔ pGammaL2PSLRange K)
        (closure {t, SemidirectProduct.inr σ}) (SemidirectProduct.inr σ) :=
    psl2SubRange_le_quadY hr hr5 hK hσ hK₀ hcard hK₀card h90 htI ht2 ht1 htcomm
  intro y hy
  obtain ⟨hyU, hyC⟩ := Subgroup.mem_inf.mp hy
  have hyPow : y ^ p = 1 := by
    obtain ⟨a, rfl⟩ := hyU
    exact rootHom_pow_char a
  have hordOdd : Odd (orderOf y) := by
    have hdvd : orderOf y ∣ p := orderOf_dvd_of_pow_eq_one hyPow
    rcases hp.eq_one_or_self_of_dvd (orderOf y) hdvd with h1 | hp'
    · rw [h1]; norm_num
    · rw [hp']; exact hpodd
  have hyL : y ∈ pGammaL2PSLRange K := rootHom_range_le hyU
  have hyC₀ : y ∈ pGammaL2PSLRange K ⊓ Subgroup.centralizer {SemidirectProduct.inr σ} :=
    ⟨hyL, hyC⟩
  obtain ⟨k, hk⟩ := hordOdd
  have hyEq : y = (y ^ (k + 1)) ^ 2 := by
    rw [← pow_mul]
    have h2 : (k + 1) * 2 = orderOf y + 1 := by omega
    rw [h2, pow_succ, pow_orderOf_eq_one, one_mul]
  have hpowD : (y ^ (k + 1)) ^ 2 ∈ psl2SubRange K₀ := by
    have hsq := Subgroup.sq_mem_of_index_two hDidx
      (⟨y ^ (k + 1), Subgroup.pow_mem _ hyC₀ (k + 1)⟩ :
        ↥(pGammaL2PSLRange K ⊓ Subgroup.centralizer {SemidirectProduct.inr σ}))
    rw [Subgroup.mem_subgroupOf] at hsq
    simpa using hsq
  have hyD : y ∈ psl2SubRange K₀ := by
    rwa [← hyEq] at hpowD
  exact hDleY hyD

private theorem map_sigma_eq_self_of_fixed_subfield_le {K : Type} [Field K] {σ : K ≃+* K}
    (hσσ : ∀ x, σ (σ x) = x) {K₀ : Subfield K} (hK₀ : ∀ x, x ∈ K₀ ↔ σ x = x)
    {W : AddSubgroup K} (hKW : K₀.toAddSubgroup ≤ W) : W.map σ.toAddMonoidHom = W := by
  have hWσ : ∀ x ∈ W, σ x ∈ W := by
    intro x hx
    have hfix : x + σ x ∈ K₀ := (hK₀ _).mpr (by rw [map_add, hσσ]; abel)
    have hmem : x + σ x ∈ W := hKW hfix
    simpa using W.sub_mem hmem hx
  refine le_antisymm ?_ ?_
  · rintro y hy
    obtain ⟨x, hx, rfl⟩ := AddSubgroup.mem_map.mp hy
    exact hWσ x hx
  · intro y hy
    exact AddSubgroup.mem_map.mpr ⟨σ y, hWσ y hy, by simpa using hσσ y⟩

private theorem l2CaseIII_inr {K : Type} [Field K] [Finite K]
    {r : ℕ} (hr : IsOddPrimePower r) (hr5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    {σ : K ≃+* K} (hσ : orderOf σ = 2)
    {t : PGammaL2 K} (htI : t ∈ pGammaL2PSLRange K) (ht2 : t * t = 1) (ht1 : t ≠ 1)
    (htcomm : t * SemidirectProduct.inr σ = SemidirectProduct.inr σ * t) :
    L2CaseIII (pGammaL2PSLRange K) t (SemidirectProduct.inr σ) := by
  classical
  letI : Fintype K := Fintype.ofFinite K
  let p := ringChar K
  haveI : Fact p.Prime := ⟨CharP.char_is_prime K p⟩
  have hchar : CharP K p := ringChar.charP K
  have hp : p.Prime := Fact.out
  have hpodd : Odd p := by
    obtain ⟨n, -, hncard⟩ := FiniteField.card K p
    have hn0 : (n : ℕ) ≠ 0 := n.ne_zero
    have hoddPow : Odd (p ^ (n : ℕ)) := by
      have hoddCard : Odd (Nat.card K) := by
        obtain ⟨p₀, a₀, hp₀, hp₀odd, ha₀, hr₀⟩ := hr
        rw [hK, hr₀]
        exact (hp₀odd.pow).pow
      simpa [hncard] using hoddCard
    exact (Nat.odd_pow_iff hn0).mp hoddPow
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hpodd
    exact Nat.not_odd_iff_even.mpr even_two hpodd
  obtain ⟨K₀, hK₀, hcard, h90⟩ := exists_fixed_subfield σ hσ
  have hK₀card : Nat.card K₀ = r := by
    apply Nat.pow_left_injective (by norm_num : 2 ≠ 0)
    change Nat.card K₀ ^ 2 = r ^ 2
    rw [← hcard, hK]
  have hσσ : ∀ x, σ (σ x) = x := by
    have h1 : σ * σ = 1 := by rw [← pow_two, ← hσ, pow_orderOf_eq_one]
    intro x
    simpa using congrArg (fun τ : K ≃+* K => τ x) h1
  let u : Multiplicative K →* PGammaL2 K := rootHom K
  let U : Subgroup (PGammaL2 K) := u.range
  let v : PGammaL2 K := SemidirectProduct.inr σ
  have hUle : U ≤ pGammaL2PSLRange K := rootHom_range_le
  have hUcomm : ∀ x ∈ U, ∀ y ∈ U, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := hx
    obtain ⟨b, rfl⟩ := hy
    rw [← map_mul, ← map_mul, mul_comm]
  have hUpow : ∀ x ∈ U, x ^ p = 1 := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    exact rootHom_pow_char a
  have hUnorm : ∀ x ∈ U, v * x * v⁻¹ ∈ U := by
    intro x hx
    obtain ⟨a, rfl⟩ := hx
    refine ⟨Multiplicative.ofAdd (σ a.toAdd), ?_⟩
    simpa [u, v] using (conj_inr_root σ a.toAdd).symm
  have hUne : U ≠ ⊥ := by
    intro hbot
    have hmemU : u (Multiplicative.ofAdd (1 : K)) ∈ U := ⟨_, rfl⟩
    rw [hbot] at hmemU
    have h1 : u (Multiplicative.ofAdd (1 : K)) = 1 := Subgroup.mem_bot.mp hmemU
    have h2 : Multiplicative.ofAdd (1 : K) = 1 :=
      rootHom_injective (h1.trans (map_one u).symm)
    have h3 : (1 : K) = 0 := congrArg Multiplicative.toAdd h2
    exact one_ne_zero h3
  have hUY : U ⊓ Subgroup.centralizer {v} ≤
      quadY (closure {t, v} ⊔ pGammaL2PSLRange K) (closure {t, v}) v := by
    simpa [u, v] using fixedRoot_le_quadY hr hr5 hK hσ hK₀ hcard hK₀card h90 htI ht2 ht1
      (by simpa [v] using htcomm)
  refine ⟨p, U, hp, hp2, hUle, hUne, hUcomm, hUpow, ?_, ?_, ?_⟩
  · simpa [v] using hUnorm
  · simpa [v] using hUY
  intro H hHU hHidx
  let H' : AddSubgroup K :=
    { carrier := {x | u (Multiplicative.ofAdd x) ∈ H}
      zero_mem' := by simpa using H.one_mem
      add_mem' := by
        intro x y hx hy
        simpa using H.mul_mem hx hy
      neg_mem' := by
        intro x hx
        simpa using H.inv_mem hx }
  have hH'sub : H'.toSubgroup = H.comap u := by
    ext a
    change a.toAdd ∈ H' ↔ u a ∈ H
    simp [H']
  have hH'idx : H'.index = p := by
    calc H'.index = H'.toSubgroup.index := (AddSubgroup.index_toSubgroup H').symm
      _ = (H.comap u).index := by rw [hH'sub]
      _ = H.relIndex u.range := Subgroup.index_comap (H := H) u
      _ = H.relIndex U := rfl
      _ = p := hHidx
  obtain ⟨mu, hmu⟩ := exists_scale_not_sigma_invariant hp hr5 hK hσ hK₀ hK₀card hH'idx
  let W : AddSubgroup K := scaleAdd ((mu : K) ^ 2) H'
  let s : PGammaL2 K := incl K (psl2QuotientMap K
    (CFSG.Glauberman.Dickson.splitTorusSLHom K mu))
  have hK₀_not_le_W : ¬ K₀.toAddSubgroup ≤ W := by
    intro hKW
    exact hmu (map_sigma_eq_self_of_fixed_subfield_le hσσ hK₀ hKW)
  obtain ⟨k, hkK₀, hkW⟩ := Set.not_subset.mp hK₀_not_le_W
  have hH_eq : H = H'.toSubgroup.map u := by
    ext y
    constructor
    · intro hy
      obtain ⟨a, rfl⟩ := hHU hy
      refine ⟨a, ?_, rfl⟩
      change a.toAdd ∈ H'
      simpa [H'] using hy
    · rintro ⟨a, ha, rfl⟩
      change a.toAdd ∈ H' at ha
      simpa [H'] using ha
  have hHmap : H.map (MulAut.conj s).toMonoidHom = W.toSubgroup.map u := by
    rw [hH_eq, Subgroup.map_map, conj_diag_comp_root, ← Subgroup.map_map]
    change (scaleAdd ((mu : K) ^ 2) H').toSubgroup.map u = W.toSubgroup.map u
    rw [toSubgroup_scaleAdd]
  have hfixk : σ k = k := (hK₀ k).mp hkK₀
  have hyfixed : v * u (Multiplicative.ofAdd k) * v⁻¹ = u (Multiplicative.ofAdd k) := by
    simpa [u, v, hfixk] using conj_inr_root σ k
  have hyC : u (Multiplicative.ofAdd k) ∈ Subgroup.centralizer {v} := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have := congrArg (fun z => z * v) hyfixed
    simpa [mul_assoc] using this.symm
  refine ⟨s, ⟨_, rfl⟩, ?_, ?_, ?_⟩
  · intro x hx
    obtain ⟨a, rfl⟩ := hx
    refine ⟨Multiplicative.ofAdd ((mu : K) ^ 2 * a.toAdd), ?_⟩
    simpa [u, s] using (conj_diag_root mu a.toAdd).symm
  · intro hle
    have hyK : u (Multiplicative.ofAdd k) ∈ H.map (MulAut.conj s).toMonoidHom :=
      hle ⟨⟨_, rfl⟩, hyC⟩
    rw [hHmap] at hyK
    have hkSub : Multiplicative.ofAdd k ∈ W.toSubgroup :=
      (Subgroup.mem_map_iff_mem (rootHom_injective (K := K))).mp hyK
    exact hkW (by simpa using hkSub)
  · rw [hHmap]
    intro heq
    have hleft : (W.toSubgroup.map u).map (MulAut.conj v).toMonoidHom =
        (W.map σ.toAddMonoidHom).toSubgroup.map u := by
      calc (W.toSubgroup.map u).map (MulAut.conj v).toMonoidHom
          = W.toSubgroup.map (((MulAut.conj v).toMonoidHom).comp u) := by
            rw [Subgroup.map_map]
        _ = W.toSubgroup.map (u.comp (sigmaHom σ)) := by
            rw [show v = SemidirectProduct.inr σ from rfl, conj_inr_comp_root]
        _ = (W.toSubgroup.map (sigmaHom σ)).map u := by rw [← Subgroup.map_map]
        _ = (W.map σ.toAddMonoidHom).toSubgroup.map u := by
            rw [toSubgroup_map_sigma]
    have heq' : (W.map σ.toAddMonoidHom).toSubgroup.map u = W.toSubgroup.map u :=
      hleft.symm.trans heq
    have hEq : (W.map σ.toAddMonoidHom).toSubgroup = W.toSubgroup :=
      Subgroup.map_injective (rootHom_injective (K := K)) heq'
    exact hmu (AddSubgroup.toSubgroup.injective hEq)

theorem l2CaseIII_pGammaL2 {K : Type} [Field K] [Finite K]
    {r : ℕ} (hr : IsOddPrimePower r) (hr5 : 5 ≤ r) (hK : Nat.card K = r ^ 2)
    {t β : PGammaL2 K} (htI : t ∈ pGammaL2PSLRange K) (hβ : β.right ≠ 1) (ht : t * t = 1)
    (ht1 : t ≠ 1) (hβ2 : β * β = 1) (hcomm : t * β = β * t) :
    L2CaseIII (pGammaL2PSLRange K) t β := by
  classical
  let I : Subgroup (PGammaL2 K) := pGammaL2PSLRange K
  have hoddK : IsOddPrimePower (Nat.card K) := by
    obtain ⟨p, a, hp, hpodd, ha, hr_eq⟩ := hr
    refine ⟨p, 2 * a, hp, hpodd, by omega, ?_⟩
    rw [hK, hr_eq]
    rw [show (p ^ a) ^ 2 = p ^ (2 * a) by rw [← pow_mul, Nat.mul_comm]]
  have hInorm : I.Normal := pGammaL2PSLRange_normal K hoddK (by rw [hK]; nlinarith)
  have hβne : β ≠ 1 := by
    intro h
    exact hβ (by rw [h]; rfl)
  have hβpow : β ^ 2 = 1 := by rw [pow_two]; exact hβ2
  have hβord : orderOf β = 2 := orderOf_eq_prime hβpow hβne
  have hσord : orderOf β.right = 2 := by
    have h3 : β.right ^ 2 = 1 := by
      have h := map_pow (SemidirectProduct.rightHom (φ := pgl2FieldAut K)) β 2
      rw [hβpow, map_one, SemidirectProduct.rightHom_eq_right] at h
      exact h.symm
    exact orderOf_eq_prime h3 hβ
  obtain ⟨C, hC⟩ := exists_conj_inr_of_involution hoddK β hβord hβ
  let g : PGammaL2 K := SemidirectProduct.inl C
  let f : PGammaL2 K →* PGammaL2 K := (MulAut.conj g).toMonoidHom
  let v : PGammaL2 K := SemidirectProduct.inr β.right
  let t' : PGammaL2 K := g⁻¹ * t * g
  have hf : Function.Injective f := (MulAut.conj g).injective
  have hft' : f t' = t := by
    change g * (g⁻¹ * t * g) * g⁻¹ = t
    group
  have hfv : f v = β := by
    have hβeq : β = g * v * g⁻¹ := by
      rw [show v = SemidirectProduct.inr β.right from rfl]
      have := congrArg (fun z => g * z * g⁻¹) hC
      simpa [g, mul_assoc] using this
    change g * v * g⁻¹ = β
    exact hβeq.symm
  have ht'I : t' ∈ I := by
    have h := hInorm.conj_mem t htI g⁻¹
    simpa [t', I] using h
  have ht'2 : t' * t' = 1 := by
    simp only [t']
    calc g⁻¹ * t * g * (g⁻¹ * t * g) = g⁻¹ * (t * t) * g := by group
      _ = 1 := by rw [ht]; group
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    rw [← hft', h, map_one]
  have ht'comm : t' * v = v * t' := by
    apply hf
    calc f (t' * v) = f t' * f v := map_mul f t' v
      _ = t * β := by rw [hft', hfv]
      _ = β * t := hcomm
      _ = f v * f t' := by rw [hfv, hft']
      _ = f (v * t') := (map_mul f v t').symm
  have hnorm : L2CaseIII I t' v :=
    l2CaseIII_inr hr hr5 hK hσord ht'I ht'2 ht'1 ht'comm
  have hmap := L2CaseIII.map hf hnorm
  have hI_map : I.map f = I := by
    simpa [f] using Subgroup.Normal.map_conj_eq I g
  rw [hI_map, hft', hfv] at hmap
  exact hmap

end CFSG.LocalAnalysis.WeakClosure81.Asch6

end
