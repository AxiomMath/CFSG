module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore
public import CFSG.Open.LocalVocabulary
import CFSG.Quasithin.H13.L32A767p
import CFSG.Quasithin.H13.L32A767e

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS166

open CFSG.Quasithin.H13.L32A

variable {G : Type*} [Group G]

theorem alt5_exists_inv : ∀ σ : alternatingGroup (Fin 5), σ ^ 3 = 1 → σ ≠ 1 →
    ∃ τ : alternatingGroup (Fin 5), τ * τ = 1 ∧ τ ≠ 1 ∧ (σ * τ) ^ 5 = 1 := by
  decide +kernel

theorem eq_one_of_commute_alt5 {L : Type*} [Group L]
    (φ : L ≃* alternatingGroup (Fin 5)) {x : L}
    (hx : ∀ y, x * y = y * x) : x = 1 := by
  have h : φ x = 1 := by
    refine a5_center (φ x) fun y => ?_
    obtain ⟨z, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hx z]
  exact φ.injective (by rw [h, map_one])

theorem card_mulAut_of_alt5 {L : Type*} [Group L]
    (φ : L ≃* alternatingGroup (Fin 5)) : Nat.card (MulAut L) = 120 := by
  rw [← card_mulAut_a5]
  exact Nat.card_congr (MulAut.congr φ).toEquiv

theorem exists_eq_conj_of_pow_three {L : Type*} [Group L]
    (φ : L ≃* alternatingGroup (Fin 5)) (α : MulAut L) (hα : α ^ 3 = 1) :
    ∃ k : L, α = MulAut.conj k := by
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [injective_iff_map_eq_one]
    intro x hx
    refine eq_one_of_commute_alt5 φ fun y => ?_
    have h := congrArg (fun f : MulAut L => f y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    calc x * y = x * y * x⁻¹ * x := by group
      _ = y * x := by rw [h]
  have hcardL : Nat.card L = 60 := by
    rw [← card_a5]
    exact Nat.card_congr φ.toEquiv
  have hInn : Nat.card (MulAut.conj : L →* MulAut L).range = 60 := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, hcardL]
  have hidx : (MulAut.conj : L →* MulAut L).range.index = 2 := by
    have h := Subgroup.card_mul_index (MulAut.conj : L →* MulAut L).range
    rw [hInn, card_mulAut_of_alt5 φ] at h
    omega
  have hα2 : α ^ 2 ∈ (MulAut.conj : L →* MulAut L).range :=
    Subgroup.sq_mem_of_index_two hidx α
  obtain ⟨k, hk⟩ := hα2
  have hα4 : α ^ 4 = α := by
    rw [show (4 : ℕ) = 3 + 1 from rfl, pow_succ, hα, one_mul]
  have h24 : α = α ^ 2 * α ^ 2 := by
    calc α = α ^ 4 := hα4.symm
      _ = α ^ 2 * α ^ 2 := by
            rw [show (4 : ℕ) = 2 + 2 from rfl, pow_add]
  have hαeq : α = MulAut.conj k * MulAut.conj k := by
    calc α = α ^ 2 * α ^ 2 := h24
      _ = MulAut.conj k * MulAut.conj k := by rw [← hk]
  refine ⟨k * k, ?_⟩
  calc α = MulAut.conj k * MulAut.conj k := hαeq
    _ = MulAut.conj (k * k) := (map_mul (MulAut.conj : L →* MulAut L) k k).symm

theorem card_of_alt5 {K : Subgroup G} (φ : ↥K ≃* alternatingGroup (Fin 5)) :
    Nat.card K = 60 := by
  rw [← card_a5]
  exact Nat.card_congr φ.toEquiv

theorem eq_of_thirty_dvd {K H : Subgroup G} (φ : ↥K ≃* alternatingGroup (Fin 5))
    (hHK : H ≤ K) (h30 : 30 ∣ Nat.card H) : H = K := by
  have hK : Nat.card K = 60 := card_of_alt5 φ
  haveI : Finite ↥K :=
    Finite.of_injective (φ : ↥K → alternatingGroup (Fin 5)) φ.injective
  have hdvd : Nat.card H ∣ Nat.card K := Subgroup.card_dvd_of_le hHK
  have hcardHsub : Nat.card (H.subgroupOf K) = Nat.card H := by
    rw [← Subgroup.card_subtype K (H.subgroupOf K), Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hHK]
  obtain ⟨c, hc⟩ := h30
  obtain ⟨d, hd⟩ := hdvd
  have hcd : c * d = 2 := by
    have h : 30 * (c * d) = 30 * 2 := by
      calc 30 * (c * d) = (30 * c) * d := by ring
        _ = Nat.card H * d := by rw [← hc]
        _ = Nat.card K := hd.symm
        _ = 60 := hK
        _ = 30 * 2 := by norm_num
    exact Nat.eq_of_mul_eq_mul_left (n := 30) (by norm_num) h
  have hc2 : c = 1 ∨ c = 2 :=
    (Nat.dvd_prime Nat.prime_two).mp ⟨d, hcd.symm⟩
  rcases hc2 with rfl | rfl
  · have hcardH1 : Nat.card (H.subgroupOf K) = 30 := by
      rw [hcardHsub, hc]
    have hcard' : Nat.card ((H.subgroupOf K).map φ.toMonoidHom) = 30 := by
      rw [Subgroup.card_map_of_injective φ.injective, hcardH1]
    have hidx : ((H.subgroupOf K).map φ.toMonoidHom).index = 2 := by
      have h := Subgroup.card_mul_index ((H.subgroupOf K).map φ.toMonoidHom)
      rw [hcard', card_a5] at h
      omega
    haveI : ((H.subgroupOf K).map φ.toMonoidHom).Normal :=
      Subgroup.normal_of_index_eq_two hidx
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      ((H.subgroupOf K).map φ.toMonoidHom) with h | h
    · rw [h, Subgroup.card_bot] at hcard'
      omega
    · rw [h, Subgroup.card_top, card_a5] at hcard'
      omega
  · have hcardH : Nat.card H = 60 := by
      rw [hc]
    exact Subgroup.eq_of_le_of_card_ge hHK (by rw [hK, hcardH])

theorem exists_inv_of_pow_three {K : Subgroup G} (φ : ↥K ≃* alternatingGroup (Fin 5))
    {x : G} (hx : x ∈ K) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) :
    ∃ t ∈ K, t * t = 1 ∧ t ≠ 1 ∧ (x * t) ^ 5 = 1 := by
  set xK : ↥K := ⟨x, hx⟩
  have hxK3 : xK ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hxK1 : xK ≠ 1 := by
    intro h
    apply hx1
    have h' : (xK : G) = 1 := by
      rw [h]
      rfl
    exact h'
  have hφ3 : φ xK ^ 3 = 1 := by rw [← map_pow, hxK3, map_one]
  have hφ1 : φ xK ≠ 1 := by
    intro h
    exact hxK1 (φ.injective (by rw [h, map_one]))
  obtain ⟨τ, hτ2, hτ1, hτ5⟩ := alt5_exists_inv (φ xK) hφ3 hφ1
  have ht2K : φ.symm τ * φ.symm τ = 1 := by
    refine φ.injective ?_
    rw [map_mul, map_one, φ.apply_symm_apply, hτ2]
  have ht2 : ((φ.symm τ : ↥K) : G) * ((φ.symm τ : ↥K) : G) = 1 := by
    simpa using congrArg (fun z : ↥K => (z : G)) ht2K
  have ht1K : φ.symm τ ≠ 1 := by
    intro h
    apply hτ1
    calc τ = φ (φ.symm τ) := (φ.apply_symm_apply τ).symm
      _ = φ 1 := by rw [h]
      _ = 1 := map_one φ
  have ht1 : ((φ.symm τ : ↥K) : G) ≠ 1 := by
    intro h
    exact ht1K (Subtype.ext h)
  have h5K : (xK * φ.symm τ) ^ 5 = 1 := by
    refine φ.injective ?_
    rw [map_pow, map_mul, map_one, φ.apply_symm_apply, hτ5]
  have h5 : (x * ((φ.symm τ : ↥K) : G)) ^ 5 = 1 := by
    simpa using congrArg (fun z : ↥K => (z : G)) h5K
  exact ⟨(φ.symm τ : ↥K), (φ.symm τ).2, ht2, ht1, h5⟩

theorem exists_ne_one_mem_centralizer {K E : Subgroup G}
    (φ : ↥K ≃* alternatingGroup (Fin 5)) (hEK : E ≤ Subgroup.normalizer (K : Set G))
    (hE9 : Nat.card E = 9) :
    ∃ e ∈ E, e ≠ 1 ∧ e ∈ Subgroup.centralizer (K : Set G) := by
  let ρ : E →* MulAut ↥K := (Subgroup.normalizerMonoidHom K).comp (Subgroup.inclusion hEK)
  have hrange9 : Nat.card ρ.range ∣ 9 := by
    rw [← hE9]
    exact Subgroup.card_range_dvd ρ
  have hrange120 : Nat.card ρ.range ∣ 120 := by
    rw [← card_mulAut_of_alt5 φ]
    exact Subgroup.card_subgroup_dvd_card ρ.range
  have hrange3 : Nat.card ρ.range ∣ 3 := by
    have h := Nat.dvd_gcd hrange9 hrange120
    rwa [show Nat.gcd 9 120 = 3 from by norm_num] at h
  have hrange_cases : Nat.card ρ.range = 1 ∨ Nat.card ρ.range = 3 :=
    (Nat.dvd_prime Nat.prime_three).mp hrange3
  have hker : Nat.card ρ.ker * Nat.card ρ.range = 9 := by
    rw [Subgroup.card_ker_mul_card_range ρ, hE9]
  have hker_ne : ρ.ker ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_mul] at hker
    rcases hrange_cases with h | h <;> rw [h] at hker <;> omega
  obtain ⟨e, he1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hker_ne
  have hfix : ∀ a : ↥K, (e.1 : G) * (a : G) * (e.1 : G)⁻¹ = (a : G) := by
    intro a
    have h' : ((ρ e.1) a : ↥K) = a := by
      have := congrArg (fun f : MulAut ↥K => f a) (MonoidHom.mem_ker.mp e.2)
      simpa using this
    have := congrArg (fun z : ↥K => (z : G)) h'
    simpa [ρ, Subgroup.normalizerMonoidHom_apply_apply_coe, MonoidHom.comp_apply] using this
  refine ⟨(e.1 : G), e.1.2, ?_, ?_⟩
  · intro h
    exact he1 (Subtype.ext (Subtype.ext h))
  · rw [Subgroup.mem_centralizer_iff]
    intro k hk
    calc k * (e.1 : G) = ((e.1 : G) * k * (e.1 : G)⁻¹) * (e.1 : G) := by
          rw [hfix ⟨k, hk⟩]
      _ = (e.1 : G) * k := by group

theorem not_isPerfect_klein_prod_alt5 : ¬ Group.IsPerfect
    ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) × alternatingGroup (Fin 5)) := by
  intro h
  haveI := h
  let f : ((Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) ×
      alternatingGroup (Fin 5)) →*
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := MonoidHom.fst _ _
  have hV : Group.IsPerfect (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    Group.IsPerfect.ofSurjective (f := f) fun x => ⟨(x, 1), rfl⟩
  haveI : Group.IsPerfect (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) := hV
  have hnc : ¬ IsMulCommutative
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2)) :=
    Group.IsPerfect.not_isMulCommutative
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))
  exact hnc inferInstance

theorem card_eq_sixty_mul_card_pCoreOf {K : Subgroup G}
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5))) :
    Nat.card K = 60 * Nat.card (CFSG.Open.pCoreOf 2 K) := by
  obtain ⟨e⟩ := hKA
  have hq : Nat.card (↥K ⧸ CFSG.pCore 2 ↥K) = 60 := by
    rw [← card_a5]
    exact Nat.card_congr e.toEquiv
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)
  have h2 : Nat.card (CFSG.Open.pCoreOf 2 K) = Nat.card (CFSG.pCore 2 ↥K) :=
    Subgroup.card_subtype K (CFSG.pCore 2 ↥K)
  rw [hq, ← h2] at h1
  exact h1

theorem nonempty_alt5_of_pCore_eq_bot {K : Subgroup G}
    (hKA : Nonempty (↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 5)))
    (h : CFSG.pCore 2 ↥K = ⊥) : Nonempty (↥K ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := hKA
  refine ⟨((QuotientGroup.quotientMulEquivOfEq h).trans
    (QuotientGroup.quotientBot (G := ↥K))).symm.trans e⟩

theorem nonempty_alt5_map {Y : Type*} [Group Y] (ψ : G ≃* Y) {K : Subgroup G}
    (h : Nonempty (↥K ≃* alternatingGroup (Fin 5))) :
    Nonempty (↥(K.map ψ.toMonoidHom) ≃* alternatingGroup (Fin 5)) := by
  obtain ⟨e⟩ := h
  exact ⟨(Subgroup.equivMapOfInjective K ψ.toMonoidHom ψ.injective).symm.trans e⟩

end CFSG.RankThree.PartTwo.KFacts.KS166
