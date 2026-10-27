module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res15ProofAut
import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofKDThree
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec14.Item147
public import CFSG.GroupTheory.BurnsideNormalComplement

public section

namespace CFSG.RankThree.PartTwo.Sec17.Proof17Res15

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

section Tools

theorem mem_normalizer_sup_of {H K : Subgroup G} {g : G}
    (hH : ∀ x ∈ H, g * x * g⁻¹ ∈ H ⊔ K) (hK : ∀ x ∈ K, g * x * g⁻¹ ∈ H ⊔ K) :
    g ∈ Subgroup.normalizer ((H ⊔ K : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun x hx => ?_
  have hle : (H ⊔ K).map (MulAut.conj g).toMonoidHom ≤ H ⊔ K := by
    rw [Subgroup.map_sup]
    exact sup_le (Subgroup.map_le_iff_le_comap.mpr fun y hy => hH y hy)
      (Subgroup.map_le_iff_le_comap.mpr fun y hy => hK y hy)
  exact hle ⟨x, hx, rfl⟩

omit [Finite G] in
theorem eq_one_of_isPGroup_of_mem {p : ℕ} [hp : Fact p.Prime] {Q V : Subgroup G}
    (hQ : IsPGroup p Q) (hV : ¬ p ∣ Nat.card V) {x : G} (hxQ : x ∈ Q) (hxV : x ∈ V) :
    x = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨x, hxQ⟩
  have hk' : x ^ p ^ k = 1 := by
    have := congrArg Subtype.val hk
    simpa using this
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp.out).mp (orderOf_dvd_of_pow_eq_one hk')
  have hdvd : orderOf x ∣ Nat.card V := Subgroup.orderOf_dvd_natCard V hxV
  rcases j with _ | j
  · rw [pow_zero, orderOf_eq_one_iff] at hj
    exact hj
  · exact absurd ((dvd_pow_self p (Nat.succ_ne_zero j)).trans (hj ▸ hdvd)) hV

theorem le_of_isPGroup_of_le_sup {p : ℕ} [hp : Fact p.Prime] {D N R Q : Subgroup G}
    (hDN : D ≤ Subgroup.normalizer (N : Set G)) (hDR : D ≤ N ⊔ R)
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) (hR : ¬ p ∣ Nat.card R) (hQD : Q ≤ D)
    (hQ : IsPGroup p Q) : Q ≤ N := by
  have h1 := Sec6.card_sup_mul_card_inf (hQD.trans hDN)
  have h2 : Nat.card ↥(Q ⊔ N) ∣ Nat.card ↥(N ⊔ R) :=
    Subgroup.card_dvd_of_le (sup_le (hQD.trans hDR) le_sup_left)
  have h3 : Nat.card ↥(N ⊔ R) ∣ Nat.card N * Nat.card R := by
    rw [sup_comm, mul_comm]
    exact Sec14.card_sup_dvd_card_mul hRN
  obtain ⟨k, hk⟩ := hQ.exists_card_eq
  have h4 : Nat.card Q ∣ Nat.card R * Nat.card ↥(Q ⊓ N) := by
    have h5 : Nat.card Q * Nat.card N ∣ Nat.card N * Nat.card R * Nat.card ↥(Q ⊓ N) := by
      rw [← h1]
      exact mul_dvd_mul_right (h2.trans h3) _
    rw [mul_comm (Nat.card Q), mul_assoc] at h5
    exact Nat.dvd_of_mul_dvd_mul_left Nat.card_pos h5
  have hcop : Nat.Coprime (Nat.card Q) (Nat.card R) := by
    rw [hk]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp.out).mpr hR)
  have h6 : Nat.card Q ∣ Nat.card ↥(Q ⊓ N) := hcop.dvd_of_dvd_mul_left h4
  have h7 : Q ⊓ N = Q :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (Nat.le_of_dvd Nat.card_pos h6)
  rw [← h7]
  exact inf_le_right

end Tools

section Complement

theorem le_pPrimeCoreOf_of_commutator_mem {p : ℕ} [hp : Fact p.Prime] {D N V R J : Subgroup G}
    (hDN : D ≤ Subgroup.normalizer (N : Set G)) (hDV : D ≤ Subgroup.normalizer (V : Set G))
    (hV : ¬ p ∣ Nat.card V) (hDR : D ≤ N ⊔ R) (hRN : R ≤ Subgroup.normalizer (N : Set G))
    (hR : ¬ p ∣ Nat.card R) (hJD : J ≤ D) (hJ : ¬ p ∣ Nat.card J)
    (hJN : ∀ j ∈ J, ∀ x ∈ N, ⁅x, j⁆ ∈ V) : J ≤ pPrimeCoreOf p D := by
  classical
  set C₀ : Subgroup G := D ⊓ centralizerSection N V with hC₀
  have hC₀D : C₀ ≤ D := inf_le_left
  have hJC : J ≤ C₀ := fun j hj =>
    ⟨hJD hj, hDN (hJD hj), hDV (hJD hj), fun x hx => hJN j hj x hx⟩
  have hDC : D ≤ Subgroup.normalizer (C₀ : Set G) := by
    intro d hd
    refine Subgroup.mem_normalizer_fintype fun c hc => ?_
    obtain ⟨hcD, hcN, hcV, hcs⟩ := hc
    refine ⟨D.mul_mem (D.mul_mem hd hcD) (D.inv_mem hd), ?_, ?_, fun x hx => ?_⟩
    · exact mul_mem (mul_mem (hDN hd) hcN) (inv_mem (hDN hd))
    · exact mul_mem (mul_mem (hDV hd) hcV) (inv_mem (hDV hd))
    · have hx' : d⁻¹ * x * d ∈ N := by
        have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem (hDN hd)) x).mp hx
        simpa using h1
      have h1 : ⁅d⁻¹ * x * d, c⁆ ∈ V := hcs _ hx'
      have h2 : ⁅x, d * c * d⁻¹⁆ = d * ⁅d⁻¹ * x * d, c⁆ * d⁻¹ := by
        simp only [commutatorElement_def]
        group
      rw [h2]
      exact (Subgroup.mem_normalizer_iff.mp (hDV hd) _).mp h1
  obtain ⟨P⟩ : Nonempty (Sylow p ↥C₀) := inferInstance
  have hP' : IsPGroup p ((P : Subgroup ↥C₀).map C₀.subtype) := P.isPGroup'.map _
  have hPN : ∀ x : ↥C₀, x ∈ (P : Subgroup ↥C₀) → (x : G) ∈ N := fun x hx =>
    le_of_isPGroup_of_le_sup hDN hDR hRN hR ((Subgroup.map_subtype_le _).trans hC₀D) hP'
      ⟨x, hx, rfl⟩
  have hNC : Subgroup.normalizer ((P : Subgroup ↥C₀) : Set ↥C₀) ≤
      Subgroup.centralizer ((P : Subgroup ↥C₀) : Set ↥C₀) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 : ⁅x, g⁆ ∈ (P : Subgroup ↥C₀) := by
      have h2 : ⁅x, g⁆ = x * (g * x⁻¹ * g⁻¹) := by
        rw [commutatorElement_def]
        group
      rw [h2]
      exact mul_mem hx ((Subgroup.mem_normalizer_iff.mp hg x⁻¹).mp (inv_mem hx))
    have h2 : ((⁅x, g⁆ : ↥C₀) : G) ∈ V := by
      have h3 := (Subgroup.mem_inf.mp g.2).2.2.2 (x : G) (hPN x hx)
      simpa [commutatorElement_def] using h3
    have h3 : ((⁅x, g⁆ : ↥C₀) : G) = 1 := eq_one_of_isPGroup_of_mem hP' hV ⟨_, h1, rfl⟩ h2
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subtype.ext h3)
  obtain ⟨K₀, hK₀n, hK₀p, hK₀idx, -⟩ := GroupTheory.burnside_normal_complement P hNC
  have hq : IsPGroup p (↥C₀ ⧸ K₀) := by
    obtain ⟨k, hk⟩ := P.isPGroup'.exists_card_eq
    exact IsPGroup.of_card (hK₀idx.trans hk)
  have hJ' : ¬ p ∣ Nat.card (J.subgroupOf C₀) := by
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hJC).toEquiv]
  have hJK : J.subgroupOf C₀ ≤ K₀ :=
    GroupTheory.le_of_normal_coprime_of_isPGroup_quotient K₀ _ hq hJ'
  have hK₀O : K₀ ≤ pPrimeCore p ↥C₀ :=
    le_sSup ⟨hK₀n, (Nat.Prime.coprime_iff_not_dvd hp.out).mpr hK₀p⟩
  have hJO : J ≤ pPrimeCoreOf p C₀ := fun j hj =>
    ⟨⟨j, hJC hj⟩, hK₀O (hJK (Subgroup.mem_subgroupOf.mpr hj)), rfl⟩
  exact hJO.trans (le_pPrimeCoreOf ((pPrimeCoreOf_le p C₀).trans hC₀D)
    (hDC.trans (normalizer_le_normalizer_pPrimeCoreOf p C₀)) (coprime_card_pPrimeCoreOf p C₀))

end Complement

section Section

theorem nonempty_quot_pPrimeCore_mulEquiv {O Y : Subgroup G} {Γ : Type*} [Group Γ] [Finite Γ]
    (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hO : ¬ 3 ∣ Nat.card O) (φ : ↥Y →* Γ)
    (hφ : Function.Surjective φ) (hker : ¬ 3 ∣ Nat.card φ.ker)
    (hΓ : ∀ W : Subgroup Γ, W.Normal → ¬ 3 ∣ Nat.card W → W = ⊥) :
    Nonempty (↥(O ⊔ Y) ⧸ pPrimeCore 3 ↥(O ⊔ Y) ≃* Γ) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := O ⊔ Y with hN
  set V' := pPrimeCore 3 ↥N with hV'
  have hcop3 : ∀ m : ℕ, ¬ 3 ∣ m → Nat.Coprime 3 m := fun m h =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h
  have hNO : N ≤ Subgroup.normalizer (O : Set G) := sup_le Subgroup.le_normalizer hYO
  have hOV : O ≤ pPrimeCoreOf 3 N := le_pPrimeCoreOf le_sup_left hNO (hcop3 _ hO)
  have hmemV : ∀ x : ↥N, (x : G) ∈ pPrimeCoreOf 3 N → x ∈ V' := by
    intro x hx
    obtain ⟨v, hv, hvx⟩ := hx
    rwa [Subtype.ext hvx] at hv
  set ψ : ↥Y →* ↥N ⧸ V' := (QuotientGroup.mk' V').comp (Subgroup.inclusion le_sup_right)
    with hψ
  have hψs : Function.Surjective ψ := by
    intro q
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective V' q
    have hx' : x ∈ ((Y : Set G) * (O : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right Y O hYO, sup_comm]
      exact hx
    obtain ⟨y, hy, o, ho, rfl⟩ := hx'
    refine ⟨⟨y, hy⟩, ?_⟩
    rw [hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    apply hmemV
    have h1 : (((Subgroup.inclusion le_sup_right ⟨y, hy⟩ : ↥N)⁻¹ * ⟨y * o, hx⟩ : ↥N) : G) = o := by
      simp
    rw [h1]
    exact hOV ho
  have hker₁ : ψ.ker ≤ φ.ker := by
    have hWn : (ψ.ker.map φ).Normal := (MonoidHom.normal_ker ψ).map φ hφ
    have hψk : ¬ 3 ∣ Nat.card ψ.ker := by
      have hmem : ∀ y : ↥ψ.ker, Subgroup.inclusion (le_sup_right : Y ≤ N) (y : ↥Y) ∈ V' := by
        intro y
        have h1 : QuotientGroup.mk' V' (Subgroup.inclusion le_sup_right (y : ↥Y)) = 1 :=
          MonoidHom.mem_ker.mp y.2
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      let ι : ↥ψ.ker →* ↥V' :=
        { toFun := fun y => ⟨Subgroup.inclusion le_sup_right (y : ↥Y), hmem y⟩
          map_one' := rfl
          map_mul' := fun _ _ => rfl }
      have hι : Function.Injective ι := fun a b hab => by
        have h1 := congrArg (fun v : ↥V' => ((v : ↥N) : G)) hab
        exact Subtype.ext (Subtype.ext h1)
      intro h3
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp pPrimeCore_coprime_card
        (h3.trans (Subgroup.card_dvd_of_injective ι hι))
    have hW3 : ¬ 3 ∣ Nat.card (ψ.ker.map φ) := fun h =>
      hψk (h.trans (Subgroup.card_map_dvd _ _))
    have hW := hΓ _ hWn hW3
    intro y hy
    rw [MonoidHom.mem_ker]
    have h1 : φ y ∈ ψ.ker.map φ := Subgroup.mem_map_of_mem φ hy
    rwa [hW, Subgroup.mem_bot] at h1
  have hker₂ : φ.ker ≤ ψ.ker := by
    set K₁ := φ.ker.map Y.subtype with hK₁
    have hK₁Y : K₁ ≤ Y := Subgroup.map_subtype_le _
    have hK₁O : K₁ ≤ Subgroup.normalizer (O : Set G) := hK₁Y.trans hYO
    have hYK : Y ≤ Subgroup.normalizer (K₁ : Set G) := by
      intro y hy
      refine Subgroup.mem_normalizer_fintype fun k hk => ?_
      obtain ⟨k', hk', rfl⟩ := hk
      exact ⟨⟨y, hy⟩ * k' * ⟨y, hy⟩⁻¹, (MonoidHom.normal_ker φ).conj_mem k' hk' ⟨y, hy⟩, rfl⟩
    have hN₁ : N ≤ Subgroup.normalizer ((K₁ ⊔ O : Subgroup G) : Set G) := by
      refine sup_le (fun o ho => mem_normalizer_sup_of (fun k hk => ?_) (fun x hx => ?_))
        (fun y hy => mem_normalizer_sup_of (fun k hk => ?_) (fun x hx => ?_))
      · have h1 : o * k * o⁻¹ * k⁻¹ ∈ O := by
          have h2 : k * o⁻¹ * k⁻¹ ∈ O :=
            (Subgroup.mem_normalizer_iff.mp (hK₁O hk) o⁻¹).mp (O.inv_mem ho)
          have h3 : o * k * o⁻¹ * k⁻¹ = o * (k * o⁻¹ * k⁻¹) := by group
          rw [h3]
          exact O.mul_mem ho h2
        have h3 : o * k * o⁻¹ = (o * k * o⁻¹ * k⁻¹) * k := by group
        rw [h3]
        exact mul_mem (Subgroup.mem_sup_right h1) (Subgroup.mem_sup_left hk)
      · exact Subgroup.mem_sup_right (O.mul_mem (O.mul_mem ho hx) (O.inv_mem ho))
      · exact Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp (hYK hy) k).mp hk)
      · exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hYO hy) x).mp hx)
    have hcop : Nat.Coprime 3 (Nat.card ↥(K₁ ⊔ O)) := by
      apply hcop3
      intro h3
      rcases (Nat.Prime.dvd_mul Nat.prime_three).mp
          (h3.trans (Sec14.card_sup_dvd_card_mul hK₁O)) with h5 | h5
      · rw [hK₁, Subgroup.card_map_of_injective Y.subtype_injective] at h5
        exact hker h5
      · exact hO h5
    have hle := le_pPrimeCoreOf (sup_le (hK₁Y.trans le_sup_right) le_sup_left) hN₁ hcop
    intro y hy
    rw [MonoidHom.mem_ker, hψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
    exact hmemV _ (hle (Subgroup.mem_sup_left ⟨y, hy, rfl⟩))
  have hkereq : ψ.ker = φ.ker := le_antisymm hker₁ hker₂
  exact ⟨(QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hkereq).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ))⟩

theorem le_pPrimeCoreOf_of_section
    {D O R Y J : Subgroup G} {Γ : Type} [Group Γ] [Finite Γ] [Group.IsPerfect Γ]
    (hDle : D ≤ O ⊔ Y ⊔ R) (hDN : D ≤ Subgroup.normalizer ((O ⊔ Y : Subgroup G) : Set G))
    (hYO : Y ≤ Subgroup.normalizer (O : Set G)) (hO : ¬ 3 ∣ Nat.card O)
    (hRN : R ≤ Subgroup.normalizer ((O ⊔ Y : Subgroup G) : Set G)) (hR : ¬ 3 ∣ Nat.card R)
    (hJD : J ≤ D) (hJ3 : ¬ 3 ∣ Nat.card J) [Group.IsPerfect ↥J] {n : ℕ}
    (hJSz : CFSG.Blueprint.SuzukiModel (↥J ⧸ aschbacherSolvableCore 3 ↥J) 2 n)
    (φ : ↥Y →* Γ) (hφ : Function.Surjective φ) (hker : ¬ 3 ∣ Nat.card φ.ker)
    (hΓ3 : ∀ W : Subgroup Γ, W.Normal → ¬ 3 ∣ Nat.card W → W = ⊥)
    (htypes : Sec4.IsTripleCover Γ CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover Γ (alternatingGroup (Fin 6)) ∨ IsCentralProductA6Covers Γ) :
    J ≤ pPrimeCoreOf 3 D := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := O ⊔ Y with hN
  obtain ⟨e⟩ := nonempty_quot_pPrimeCore_mulEquiv hYO hO φ hφ hker hΓ3
  have hJN : J ≤ Subgroup.normalizer (N : Set G) := hJD.trans hDN
  set ρ₀ : ↥J →* MulAut (↥N ⧸ pPrimeCore 3 ↥N) :=
    (Sec16.Proof1624KD.quotMulAut ↥N).comp (N.normalizerMonoidHom.comp (Subgroup.inclusion hJN))
    with hρ₀
  have hθ : Group.IsSolvable (aschbacherSolvableCore 3 ↥J) :=
    (solvable_prime_complement_core_characterization Nat.prime_three).1
  have hker' := ker_eq_top_of_types hθ hJSz htypes ((MulAut.congr e).toMonoidHom.comp ρ₀)
  have hcomm : ∀ j ∈ J, ∀ x ∈ N, ⁅j, x⁆ ∈ pPrimeCoreOf 3 N := by
    intro j hj x hx
    have h1 : (MulAut.congr e).toMonoidHom.comp ρ₀ ⟨j, hj⟩ = 1 := by
      rw [← MonoidHom.mem_ker, hker']
      exact Subgroup.mem_top _
    have h2 : ρ₀ ⟨j, hj⟩ = 1 := (MulAut.congr e).injective (by rw [map_one]; exact h1)
    have h3 := congrArg (fun σ : MulAut (↥N ⧸ pPrimeCore 3 ↥N) =>
      σ (((⟨x, hx⟩ : ↥N)⁻¹ : ↥N) : ↥N ⧸ pPrimeCore 3 ↥N)) h2
    simp only [hρ₀, MonoidHom.comp_apply, Sec16.Proof1624KD.quotMulAut_mk, MulAut.one_apply]
      at h3
    rw [QuotientGroup.eq] at h3
    refine ⟨_, h3, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_inclusion, commutatorElement_def]
    group
  have hV3 : ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 N)
  exact le_pPrimeCoreOf_of_commutator_mem hDN
    (hDN.trans (normalizer_le_normalizer_pPrimeCoreOf 3 N)) hV3 hDle hRN hR hJD hJ3
    (fun j hj x hx => by
      rw [← commutatorElement_inv]
      exact inv_mem (hcomm j hj x hx))

end Section

end CFSG.RankThree.PartTwo.Sec17.Proof17Res15
