module

public import CFSG.RankThree.PartOne.KF.R7Final
public import CFSG.RankThree.PartOne.KEXC.WeylScalar
public import CFSG.RankThree.PartOne.SP4C.Swap

public section

namespace CFSG.RankThree.PartOne.SP4C

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.RankThree.PartOne.KEXC
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Unitary

variable {G : Type} [Group G]

theorem exists_r7ctx_core [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 7) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), (∃ ζ : Kˣ, IsPrimitiveRoot ζ p) ∧
      Nonempty (D8Ctx p K L F) := by
  classical
  obtain ⟨f, K, hKf, hKfin, hf1, hpq, hK, hζ, hchar, ε, hε, hFT₁, hFT₂⟩ :=
    exists_r7frame h hmodel
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

theorem row7_sq_scalar [Finite G] {p : ℕ} {L A₀ F : Subgroup G} (h : Table123Core p L A₀ F)
    (hmodel : RowModel p L 7) {y : G} (hyL : y ∈ Subgroup.normalizer (L : Set G))
    (hyF : y ∈ Subgroup.normalizer (F : Set G)) :
    ∃ h' : G, h' ∈ L ∧ h' ∈ Subgroup.normalizer (F : Set G) ∧
      ∃ k : ℤ, ∀ f ∈ F, (y * y) * f * (y * y)⁻¹ = h' * f ^ k * h'⁻¹ := by
  obtain ⟨K, hKf, hKfin, hζ, ⟨S⟩⟩ := exists_r7ctx_core h hmodel
  have hp := h.prime
  have hp2 : p ≠ 2 := by have := h.five_le; omega
  have hyy : y * y ∈ Subgroup.normalizer (F : Set G) := Subgroup.mul_mem _ hyF hyF
  have hφ : weylConjAut S hyy = weylConjAut S hyF * weylConjAut S hyF := by
    unfold weylConjAut
    rw [← map_mul]
    congr 1
    rw [← map_mul]
    rfl
  obtain ⟨γ, k, hk⟩ := exists_d8Act_mul_pow_sq hp hp2 hζ (weylConjAut S hyF)
    (S.normalizes_act hyL hyF)
  exact exists_scalar_of_weylConjAut S hyy ⟨γ, k, fun v => by rw [hφ]; exact hk v⟩

end CFSG.RankThree.PartOne.SP4C
