module

public import CFSG.Quasithin.Vol2.Ch11SecOE6E
public import CFSG.Quasithin.Vol2.Ch1Sec3E9Fitting
public import CFSG.Quasithin.Vol2.Ch11SecOE6D

public section

namespace CFSG.Quasithin.Vol2.Ch11.OE6

open CFSG.Open CFSG.Quasithin

theorem conj_eq_of_comm_mem {Γ : Type} [Group Γ] [Finite Γ] {p : ℕ} [hp : Fact p.Prime]
    {F : Subgroup Γ} (hpF : ¬ p ∣ Nat.card F) {x k : Γ} (hxp : x ^ p = 1)
    (hxF : ∀ f ∈ F, x * f = f * x) (hd : x * k⁻¹ * x⁻¹ * k ∈ F) : x * k * x⁻¹ = k := by
  set d := x * k⁻¹ * x⁻¹ * k with hddef
  have hxd : ∀ n : ℕ, x * d⁻¹ ^ n = d⁻¹ ^ n * x := fun n =>
    hxF _ (F.pow_mem (F.inv_mem hd) n)
  have key : ∀ n : ℕ, x ^ n * k * (x ^ n)⁻¹ = k * d⁻¹ ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      calc x ^ (n + 1) * k * (x ^ (n + 1))⁻¹ = x * (x ^ n * k * (x ^ n)⁻¹) * x⁻¹ := by group
        _ = x * k * x⁻¹ * (x * d⁻¹ ^ n * x⁻¹) := by rw [ih]; group
        _ = k * d⁻¹ * d⁻¹ ^ n := by rw [hxd n, hddef]; group
        _ = k * d⁻¹ ^ (n + 1) := by rw [pow_succ', mul_assoc]
  have h1 := key p
  rw [hxp, one_mul, inv_one, mul_one] at h1
  have hdp : d⁻¹ ^ p = 1 := by
    have := congrArg (fun y => k⁻¹ * y) h1
    simpa using this.symm
  have hord : orderOf (⟨d⁻¹, F.inv_mem hd⟩ : ↥F) = 1 := by
    have h2 : orderOf (⟨d⁻¹, F.inv_mem hd⟩ : ↥F) ∣ p :=
      orderOf_dvd_of_pow_eq_one (Subtype.ext (by simpa using hdp))
    have h3 : orderOf (⟨d⁻¹, F.inv_mem hd⟩ : ↥F) ∣ Nat.card F := orderOf_dvd_natCard _
    rcases (Nat.dvd_prime hp.out).mp h2 with h | h
    · exact h
    · exact absurd (h ▸ h3) hpF
  have hd1 : d⁻¹ = 1 := by
    have := congrArg Subtype.val (orderOf_eq_one_iff.mp hord)
    simpa using this
  have : x * k * x⁻¹ = k * d⁻¹ := by rw [hddef]; group
  rw [this, hd1, mul_one]

variable {G : Type} [Group G] [Finite G]

namespace Setting

variable {T H K Y : Subgroup G} (S : Setting G T H K Y)
include S

theorem le_normalizer_of_not_isQuasisimple (h36 : QuasithinUnique.Vol2Native.A36CoreForSQTKCat)
    (hnq : ¬ CFSG.IsQuasisimple (↥K ⧸ CFSG.pCore 2 ↥K)) :
    K ≤ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨p, hp, hp5, hpY, P, hSyl⟩ := S.exists_prime
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hPp, hexp, hc2, hc3, hNP, hirr⟩ := S.bar_data hp2 hpY hSyl
  have hyp := QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot S.loc S.core
  have hrank : ∀ r : ℕ, r.Prime → r ≠ 2 →
      Open.pRank r (⊤ : Subgroup (↥H ⧸ CFSG.pCore 2 ↥H)) ≤ 2 :=
    CFSG.SectionRank.isStronglyQuasithin_iff.1 hyp.sqt
  rcases P134.normal_or_centralizes_fitting hyp.o2 hrank hp2 hPp hexp hc2 hc3 hNP hirr
      (H13.NQCore.comm_bar_of_sylow S.sylowIn S.YH S.xi hp2 hpY hSyl) with hn | ⟨hF, hrk⟩
  · exact S.KH.trans
      (H13.NQCore.le_normalizer_of_normal_of_sylow S.sylowIn S.YH S.xi hp2 hpY hSyl hn)
  have hcore := QuasithinUnique.Vol2Native.lemma_1_2_1_four_core S.loc h36 S.core S.comp
  have := S.normal_bar
  obtain ⟨e⟩ := SecA.C11P9B.modO2Image_equiv S.KH S.normal_subgroupOf
  have h34 : A36Case3 ↥(modO2Image H K) ∨ A36Case4 ↥(modO2Image H K) := by
    rcases hcore.1 with hc | h | h
    · exact absurd (CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hc.1) hnq
    · exact Or.inl h
    · exact Or.inr h
  set N := modO2Image H K with hN
  set F := CFSG.fittingSubgroup ↥N with hFdef
  have hpF : ¬ p ∣ Nat.card F := by
    intro hdvd
    obtain ⟨Q, -, -, hQ, -⟩ := hcore.2.2 h34 p hp hdvd
    exact false_of_rank_le_one hp2 hrk hQ
  have hpF' : ¬ p ∣ Nat.card (F.map N.subtype) := by
    rwa [Subgroup.card_map_of_injective N.subtype_injective]
  have hPF : ∀ x ∈ modO2Image H P, ∀ f ∈ F.map N.subtype, x * f = f * x := fun x hx f hf =>
    (Subgroup.mem_centralizer_iff.mp (hF hx) f (map_fitting_le hf)).symm
  obtain ⟨r, hr, hr5, ⟨eTop⟩⟩ : ∃ r : ℕ, r.Prime ∧ 5 ≤ r ∧
      Nonempty (↥N ⧸ F ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod r)) := by
    rcases h34 with ⟨p₀, hp₀, hp₀3, -, -, -, ψ, hψ, hker, -⟩ | ⟨-, -, h5, -⟩
    · have h4 : p₀ ≠ 4 := by
        rintro rfl
        norm_num at hp₀
      exact ⟨p₀, hp₀, by omega, ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)⟩⟩
    · obtain ⟨e5⟩ := h5
      exact ⟨5, by norm_num, le_rfl, ⟨e5⟩⟩
  set φ : (↥H ⧸ CFSG.pCore 2 ↥H) →* MulAut (↥N ⧸ F) :=
    (charQuotHom F).comp (MulAut.conjNormal : (↥H ⧸ CFSG.pCore 2 ↥H) →* MulAut ↥N) with hφ
  have hNφ : modO2Image H (T ⊓ Subgroup.normalizer (P : Set G)) ≤
      Subgroup.normalizer (φ.ker : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (MonoidHom.normal_ker _)]
    exact le_top
  have hker := le_ker_of_isCyclic_map hPp hexp hc2 hNP hirr φ hNφ
    (isCyclic_mulAut_sl2 hr hr5 eTop hp2 (hPp.map φ))
  have hc : modO2Image H P ≤ Subgroup.centralizer (N : Set (↥H ⧸ CFSG.pCore 2 ↥H)) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 := congrArg (fun α : MulAut (↥N ⧸ F) => α (QuotientGroup.mk ⟨k, hk⟩))
      (MonoidHom.mem_ker.mp (hker hx))
    simp only [hφ, MonoidHom.comp_apply, charQuotHom_mk, MulAut.one_apply] at h1
    rw [QuotientGroup.eq] at h1
    have hd : x * k⁻¹ * x⁻¹ * k ∈ F.map N.subtype := by
      refine ⟨_, h1, ?_⟩
      rw [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, MulAut.conjNormal_apply]
      group
    have h2 := conj_eq_of_comm_mem hpF' (hexp x hx) (hPF x hx) hd
    calc k * x = x * k * x⁻¹ * x := by rw [h2]
      _ = x * k := by group
  exact S.le_normalizer_of_le_centralizer hp2 hpY hSyl hc

end Setting

end CFSG.Quasithin.Vol2.Ch11.OE6
