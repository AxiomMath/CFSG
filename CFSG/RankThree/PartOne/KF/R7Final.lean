module

public import CFSG.RankThree.PartOne.KF.R1Final
public import CFSG.RankThree.PartOne.KF.SpSylow

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank
  CFSG.LieType.Universal.Unitary

variable {G : Type} [Group G]

@[expose] noncomputable def spQ (K : Type) [Field K] : ↥(spRev K) →* StatedProj (StatedSp 2 K) :=
  (QuotientGroup.mk'
    ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K))).comp
    (spRevEquiv K).symm.toMonoidHom

theorem isCentralPQuot_spQ {K : Type} [Field K] [CharP K 2] (p : ℕ) : IsCentralPQuot p (spQ K) := by
  let N : Subgroup ↥(StatedSp 2 K) := (StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)
  have hN : N = ⊥ :=
    CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by norm_num)
  have hqbij : Function.Bijective (spQ K) := by
    refine ⟨fun x y hxy => ?_, (QuotientGroup.mk'_surjective N).comp
      (spRevEquiv K).symm.surjective⟩
    have h1 : (QuotientGroup.mk' N) ((spRevEquiv K).symm x) =
        (QuotientGroup.mk' N) ((spRevEquiv K).symm y) := hxy
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq, hN,
      Subgroup.mem_bot, inv_mul_eq_one] at h1
    exact (spRevEquiv K).symm.injective h1
  exact SymCtx.isCentralPQuot_of_bijective _ hqbij p

theorem exists_r7frame_of [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    {f : ℕ} (hf1 : 1 ≤ f) (hpq : p ∣ 2 ^ f - 1)
    (hmod : StatedClassicalModel (L ⧸ Subgroup.center L) .PSp 2 2 f) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      Nat.card K = 2 ^ f ∧ (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧ CharP K 2 ∧
      ∃ ε : ↥L →* StatedProj (StatedSp 2 K), IsCentralPQuot p ε ∧
        (∀ t ∈ (d8Tor p K 4).subgroupOf (spRev K), ∃ x : F,
          ε (Subgroup.inclusion h.F_le x) = spQ K t) ∧
        ∀ x : F, ∃ t ∈ (d8Tor p K 4).subgroupOf (spRev K),
          ε (Subgroup.inclusion h.F_le x) = spQ K t := by
  classical
  obtain ⟨-, K, hKf, hKfin, hK, ⟨e⟩⟩ := hmod
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hchar : CharP K 2 := by
    have := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (p := 2) (f := f) (by rw [Fintype.card_eq_nat_card]; exact hK)
  have hdvdK : p ∣ Nat.card K - 1 := by rw [hK]; exact hpq
  have hζ : ∃ ζ : Kˣ, IsPrimitiveRoot ζ p := by
    have hdvd : p ∣ Nat.card Kˣ := by rw [Nat.card_units]; exact hdvdK
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' p hdvd
    refine ⟨z, ?_⟩
    have := IsPrimitiveRoot.orderOf z
    rwa [hz] at this
  have hcop : Nat.Coprime p (Nat.card (Subgroup.center ↥L)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr h.center_pPrime
  have hε₀ := isCentralPQuot_center e hcop
  have hq : IsCentralPQuot p (spQ K) := isCentralPQuot_spQ p
  have hTexp : ∀ t ∈ (d8Tor p K 4).subgroupOf (spRev K), t ^ p = 1 := by
    intro t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((t : ↥(spRev K)) : GL (Fin 4) K) ^ p = 1
    rw [← hv]
    show diagU (d8Vec 4 v) ^ p = 1
    rw [diagU_pow, d8Vec_pow_eq_one, diagU_one]
  have hTcomm : ∀ s ∈ (d8Tor p K 4).subgroupOf (spRev K),
      ∀ t ∈ (d8Tor p K 4).subgroupOf (spRev K), s * t = t * s := by
    intro s hs t ht
    obtain ⟨v, hv⟩ := Subgroup.mem_subgroupOf.mp hs
    obtain ⟨w, hw⟩ := Subgroup.mem_subgroupOf.mp ht
    apply Subtype.ext
    show ((s : ↥(spRev K)) : GL (Fin 4) K) * (t : GL (Fin 4) K) =
      (t : GL (Fin 4) K) * (s : GL (Fin 4) K)
    rw [← hv, ← hw]
    show diagU (d8Vec 4 v) * diagU (d8Vec 4 w) = diagU (d8Vec 4 w) * diagU (d8Vec 4 v)
    rw [diagU_mul, diagU_mul, mul_comm]
  obtain ⟨ε, hε, hFT₁, hFT₂⟩ := exists_toral_quot (spQ K) hq _ hε₀ hTexp hTcomm
    (fun X hexp _ => exists_conj_into_d8Tor_sp hp hp2 hdvdK X hexp) h.F_le h.F_exp h.F_comm
    h.maximal
  exact ⟨K, hKf, hKfin, hf1, hpq, hK, hζ, hchar, ε, hε, hFT₁, hFT₂⟩

theorem exists_r7frame [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 7) :
    ∃ (f : ℕ) (K : Type) (_ : Field K) (_ : Finite K), 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
      Nat.card K = 2 ^ f ∧ (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧ CharP K 2 ∧
      ∃ ε : ↥L →* StatedProj (StatedSp 2 K), IsCentralPQuot p ε ∧
        (∀ t ∈ (d8Tor p K 4).subgroupOf (spRev K), ∃ x : F,
          ε (Subgroup.inclusion h.F_le x) = spQ K t) ∧
        ∀ x : F, ∃ t ∈ (d8Tor p K 4).subgroupOf (spRev K),
          ε (Subgroup.inclusion h.F_le x) = spQ K t := by
  obtain ⟨f, hf1, hpq, hmod⟩ := hmodel
  obtain ⟨K, hKf, hKfin, hrest⟩ := exists_r7frame_of h hf1 hpq hmod
  exact ⟨f, K, hKf, hKfin, hrest⟩

theorem exists_r7ctx [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Generic p L A₀ F)
    (hmodel : RowModel p L 7) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (D8Ctx p K L F) := by
  classical
  obtain ⟨f, K, hKf, hKfin, hf1, hpq, hK, hζ, hchar, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r7frame h.toCore hmodel
  have hp := h.prime
  have h5 := h.five_le
  have hp2 : p ≠ 2 := by omega
  have : Fact p.Prime := ⟨hp⟩
  have hT : ∀ v : D8Mod p K, (diagU (d8Vec 4 v) : GL (Fin 4) K) ∈ spRev K := fun v => by
    rw [d8Vec_four]
    exact diagU_dvec4_mem_spRev _ _
  have hP : ∀ τ : Equiv.Perm (Fin 4), (∀ i, τ (Fin.rev i) = Fin.rev (τ i)) →
      (permGL τ : GL (Fin 4) K) ∈ spRev K := fun τ hτ => by
    rw [mem_spRev_iff]
    simpa [conjTr] using permGL_gram (RingEquiv.refl K) τ hτ
  obtain ⟨SM⟩ := exists_d8ctx d8Comb_four d8Comb2_four hp hp2 hζ (spRev K) hT hP
  have hq : IsCentralPQuot p (spQ K) := isCentralPQuot_spQ p
  have hVexp : ∀ d : D8Mod p K, d ^ p = 1 := fun d =>
    Prod.ext (Subtype.ext ((mem_rootsOfUnity p _).mp d.1.2))
      (Subtype.ext ((mem_rootsOfUnity p _).mp d.2.2))
  exact ⟨K, hKf, hKfin, hζ, WCtx.ofCentralQuot hVexp SM (spQ K) hq ε hε h.F_le h.F_exp hFT₁ hFT₂⟩

theorem kf123Row7 : KF123Row 7 := by
  intro G _ _ p L A₀ F h hmodel
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r7ctx h hmodel
  exact S.rowData (Or.inr (Or.inr (Or.inl rfl))) h.prime (by have := h.five_le; omega) hζ hmodel

theorem kf123NTRow7 : KF123NTRow 7 := by
  intro G _ _ p L A₀ F h hmodel y hyL hyF
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r7ctx h hmodel
  have hpowF : ∀ a : F, a ^ p = 1 :=
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp h.F_elem.exponent_dvd_p
  exact S.not_isAutTransvection h.prime (by have := h.five_le; omega) h.five_le hζ hpowF hyL hyF

end CFSG.RankThree.PartOne
