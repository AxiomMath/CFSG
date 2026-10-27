module

public import CFSG.RankThree.PartOne.KFOUT3.KtyL4
public import CFSG.RankThree.PartOne.KFOUT3.KtyRows
public import CFSG.RankThree.PartOne.KFOUT3.CQuot
public import CFSG.RankThree.PartOne.KF.R11Final
public import CFSG.RankThree.PartOne.KF.R8Model
public import CFSG.RankThree.PartOne.KF.ToralQuot
public import CFSG.RankThree.PartOne.KFOUT3.KtyD8
public import CFSG.RankThree.PartOne.KFOUT3.KtyWCtx

public section

namespace CFSG.RankThree.PartOne.KFOUT3

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KFQ
  CFSG.Assembly.LowTwoRank CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne.N1322

section Model

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

@[expose] noncomputable def m8Iso :
    ↥(M8 K) ≃* (↥(StatedSL 4 K) ⧸ (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)) := by
  have hN : (StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K) = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_subgroupOf] at hx
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    exact scalar_eq_one_of_det hx (mem_statedSL_iff.mp x.2)
  refine MulEquiv.ofBijective
    ((QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K))).comp
      (m8Equiv (K := K)).toMonoidHom) ⟨fun x y hxy => ?_, ?_⟩
  · have h1 : (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf (StatedSL 4 K)))
        (m8Equiv x) = (QuotientGroup.mk' ((StatedScalars (Fin 4) K).subgroupOf
          (StatedSL 4 K))) (m8Equiv y) := hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact m8Equiv.injective h1
  · exact (QuotientGroup.mk'_surjective _).comp m8Equiv.surjective

theorem exists_d8ctx_r8' (hp : p.Prime) (hp2 : p ≠ 2) (hpq : p ∣ Nat.card K + 1) :
    ∃ SM : D8Ctx p (Qext K) (⊤ : Subgroup ↥(M8 K))
      ((d8Emb : D8Mod p (Qext K) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))).range.subgroupOf
        (M8 K)), ∀ d, ((SM.tor d : _) : ↥(M8 K)) = T8 hp hp2 hpq d := by
  classical
  set T : Subgroup (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) := d8Emb.range with hTdef
  have hTM : T ≤ M8 K := by
    rintro _ ⟨v, rfl⟩
    exact d8Emb_mem_M8 hp hp2 hpq v
  let torh : D8Mod p (Qext K) →* ↥(T.subgroupOf (M8 K)) :=
    { toFun := fun v => ⟨⟨d8Emb v, d8Emb_mem_M8 hp hp2 hpq v⟩, ⟨v, rfl⟩⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        exact map_one _
      map_mul' := fun v w => by
        apply Subtype.ext
        apply Subtype.ext
        exact map_mul _ _ _ }
  have hinj : Function.Injective torh := by
    intro v w h
    exact d8Emb_injective (congrArg (fun x : ↥(T.subgroupOf (M8 K)) =>
      ((x : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))) h)
  have hsurj : Function.Surjective torh := by
    rintro ⟨⟨x, hxM⟩, hxT⟩
    obtain ⟨v, hv⟩ := hxT
    refine ⟨v, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hv
  let tor : D8Mod p (Qext K) ≃* ↥(T.subgroupOf (M8 K)) :=
    MulEquiv.ofBijective torh ⟨hinj, hsurj⟩
  refine ⟨{ tor := tor, exists_elt := ?_, induced := ?_ }, fun d => rfl⟩
  · intro γ
    obtain ⟨g, hdet, hr⟩ := exists_realizer (p := p) hpq γ
    set gM : ↥(M8 K) := ⟨g, (mem_M8_iff _).mpr hdet⟩ with hgMdef
    have hg : gM ∈ Subgroup.normalizer
        ((T.subgroupOf (M8 K) : Subgroup ↥(M8 K)) : Set ↥(M8 K)) := by
      rw [mem_normalizer_subgroupOf_iff' hTM]
      refine ⟨fun x hx => ?_, fun x hx => ?_⟩
      · obtain ⟨v, rfl⟩ := hx
        show g * d8Emb v * g⁻¹ ∈ T
        rw [hr v]
        exact ⟨_, rfl⟩
      · obtain ⟨v, rfl⟩ := hx
        show g⁻¹ * d8Emb v * g ∈ T
        rw [realizes_inv hr v]
        exact ⟨_, rfl⟩
    refine ⟨gM, hg, Subgroup.mem_top _, ?_⟩
    refine MulEquiv.ext fun t => ?_
    obtain ⟨v, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    apply Subtype.ext
    exact hr v
  · intro m hm _
    obtain ⟨h1, -⟩ := (mem_normalizer_subgroupOf_iff' hTM m).mp hm
    have hg : ∀ v : D8Mod p (Qext K), ∃ v' : D8Mod p (Qext K),
        (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) * d8Emb v * (m : QV K (Fin 2) ≃ₗ[K] _)⁻¹ =
          d8Emb v' := fun v => by
      obtain ⟨v', hv'⟩ := h1 _ ⟨v, rfl⟩
      exact ⟨v', hv'.symm⟩
    obtain ⟨w, hw⟩ := exists_dihedral_of_normalizes hp hp2 hpq
      (m : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) hg
    refine ⟨w, MulEquiv.ext fun t => ?_⟩
    obtain ⟨v, rfl⟩ := tor.surjective t
    rw [SymCtx.congr_apply_tor]
    apply Subtype.ext
    apply Subtype.ext
    exact hw v

end Model

theorem kf1322KtyRow8_holds :
    KF1322KtyRow 8 := by
  intro G _ _ p A c L E h12 hF12 hF13 hno5 hEA hL3 hmodel t ht s hs hts g hg
  rcases hF12.two with hG | hS
  ·
    have hp := h12.prime
    have h5 := Sec12Three.five_le h12
    have hp2 : p ≠ 2 := by omega
    have : Fact p.Prime := ⟨hp⟩
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hZ := hG.center_pPrime
    obtain ⟨hFexp, hFcomm, hmax⟩ := F_facts h12 hG
    obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
    obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
    have hchar : CharP K 2 := by
      have := Fintype.ofFinite K
      exact charP_of_card_eq_prime_pow (p := 2) (f := f)
        (by rw [Fintype.card_eq_nat_card]; exact hK)
    have hpq' : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    have hq2 : 2 ≤ Nat.card K := by
      have : 1 < Nat.card K := Finite.one_lt_card
      omega
    obtain ⟨m, hmp, hm1, -⟩ := exists_root_not_mem hp hp2 hpq'
    have hζ : ∃ ζ : (Qext K)ˣ, IsPrimitiveRoot ζ p := by
      have hm0 : m ≠ 0 := by
        rintro rfl
        rw [zero_pow hp.ne_zero] at hmp
        exact zero_ne_one hmp
      refine ⟨Units.mk0 m hm0, ?_⟩
      have hu : (Units.mk0 m hm0) ^ p = 1 := Units.ext (by simpa using hmp)
      have hu1 : Units.mk0 m hm0 ≠ 1 := fun h1 => hm1 (by simpa using congrArg Units.val h1)
      rw [IsPrimitiveRoot.iff_orderOf]
      rcases (Nat.dvd_prime hp).mp (orderOf_dvd_of_pow_eq_one hu) with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) hu1
      · exact h1
    have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
      (Nat.Prime.coprime_iff_not_dvd hp).mpr hZ
    have hε₀ := isCentralPQuot_center' (e.trans (m8Iso (K := K)).symm) hcop
    set Tsub : Subgroup ↥(M8 K) :=
      (d8Emb : D8Mod p (Qext K) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2))).range.subgroupOf (M8 K)
      with hTsub
    have hTexp : ∀ t ∈ Tsub, t ^ p = 1 := by
      intro t ht
      obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
      apply Subtype.ext
      show ((t : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) ^ p = 1
      rw [← hv]
      exact d8Emb_pow v
    have hTcomm : ∀ s ∈ Tsub, ∀ t ∈ Tsub, s * t = t * s := by
      intro s hs t ht
      obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
      obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
      apply Subtype.ext
      show ((s : ↥(M8 K)) : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) *
        (t : QV K (Fin 2) ≃ₗ[K] _) = (t : QV K (Fin 2) ≃ₗ[K] _) *
          (s : QV K (Fin 2) ≃ₗ[K] _)
      rw [← hv, ← hw]
      exact d8Emb_comm v w
    obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (T := Tsub) (MonoidHom.id _)
      (isCentralPQuot_id p) _ hε₀ hTexp hTcomm
      (fun X hexp _ => exists_conj_into_T8 hp hp2 hpq' X hexp) (inf_le_right : E ⊓ L ≤ L) hFexp
      hFcomm hmax
    obtain ⟨SM, hSM⟩ := exists_d8ctx_r8' (K := K) hp hp2 hpq'
    have hVexp : ∀ d : D8Mod p (Qext K), d ^ p = 1 := fun d =>
      Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
        (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
    obtain ⟨S, hrel⟩ := wctx_ofCentralQuot' hVexp SM (MonoidHom.id _) (isCentralPQuot_id p) ε hε
      (inf_le_right : E ⊓ L ≤ L) hFexp hFT₁ hFT₂
    have hrel' : ∀ d, ε (Subgroup.inclusion inf_le_right (S.tor d)) = T8 hp hp2 hpq' d := by
      intro d
      rw [hrel d]
      exact hSM d
    have Hconj : ∀ γ : DihedralGroup 4, ∃ m : ↥(M8 K),
        ∀ v, m * T8 hp hp2 hpq' v * m⁻¹ = T8 hp hp2 hpq' (d8Act γ v) := by
      intro γ
      obtain ⟨g', hdet, hr⟩ := exists_realizer (p := p) hpq' γ
      exact ⟨⟨g', (mem_M8_iff _).mpr hdet⟩, fun v => Subtype.ext (hr v)⟩
    exact kty_of_d8 h12 hG hEA hF13 hp2 hζ hε (T8 hp hp2 hpq') S hrel' Hconj
      (fun b hb => smallAt_of_card_le (card_centralizer_le hp hp2 hpq' hb) (small_lt_big hq2))
      (fun a ha => bigAt_diag hp hp2 hpq' ha) t ht s hs hts g hg
  ·
    exfalso
    have hrow := kf123Row11 G p L A E (Sec12Three.table123SU5 h12 hS)
    have hcard : Nat.card E = p ^ 4 := hrow.2.1
    rw [hEA, h12.A_card] at hcard
    have h5 := Sec12Three.five_le h12
    have h1 : p ^ 3 < p ^ 4 := Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega

end CFSG.RankThree.PartOne.KFOUT3
