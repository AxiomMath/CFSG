module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316Ord5
public import CFSG.LocalAnalysis.ComponentInitial.CLSFourGroupLinearThreeFour
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdentLieAlt
public import CFSG.Quasithin.Vol2.Ch12Sec2OrbitG2Cert
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316U35A

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp StatedProj StatedScalars
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open scoped MatrixGroups Pointwise commutatorElement

namespace L4316

theorem eq_one_of_pow_three_eq_one :
    ∀ v : Multiplicative (ZMod 2) × Multiplicative (ZMod 2), v ^ 3 = 1 → v = 1 := by
  decide

theorem commutator_eq_one_of_pow {K : Type*} [Field K] [Finite K] (hK : Nat.card K = 4)
    {a c : Kˣ ⋊[LinearThreeFourOuter.inversionAction Kˣ]
      (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))}
    (hc : c ^ 3 = 1) {e : ℕ} (ha : (a * c * a⁻¹ * c⁻¹) ^ (2 ^ e) = 1) :
    a * c * a⁻¹ * c⁻¹ = 1 := by
  set w := a * c * a⁻¹ * c⁻¹ with hw
  have hcr : SemidirectProduct.rightHom c = 1 := by
    apply eq_one_of_pow_three_eq_one
    rw [← map_pow, hc, map_one]
  have hwr : SemidirectProduct.rightHom w = 1 := by
    rw [hw, ← commutatorElement_def, map_commutatorElement, hcr, commutatorElement_one_right]
  have hwi : w ∈ (SemidirectProduct.inl : Kˣ →* _).range := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    exact hwr
  obtain ⟨x, hx⟩ := hwi
  have hw3 : w ^ 3 = 1 := by
    rw [← hx, ← map_pow, units_pow_three hK x, map_one]
  have h1 : orderOf w ∣ 3 := orderOf_dvd_of_pow_eq_one hw3
  have h2 : orderOf w ∣ 2 ^ e := orderOf_dvd_of_pow_eq_one ha
  have hcop : Nat.Coprime 3 (2 ^ e) := Nat.Coprime.pow_right _ (by norm_num)
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop h1 h2)

theorem exists_outerHom_of_isPSL {X : Type} [Group X] (hX : IsPSL 3 2 2 X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K)
      (Ψ : MulAut X →* Kˣ ⋊[LinearThreeFourOuter.inversionAction Kˣ]
        (Multiplicative (ZMod 2) × Multiplicative (ZMod 2))), Nat.card K = 4 ∧
        ∀ φ : MulAut X, Ψ φ = 1 → φ ∈ (MulAut.conj : X →* MulAut X).range := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have hK4 : Nat.card K = 4 := by rw [hK]; norm_num
  have := LinearFieldFour.charP_two_of_card_eq_four hK4
  have hσ : ∀ a, frobeniusEquiv K 2 a = a ^ 2 := fun a => frobeniusEquiv_apply K 2 a
  obtain ⟨Ψ, hΨ⟩ := LinearThreeFourOuter.exists_outerHom hσ hK4
  have hker := LinearThreeFourOuter.ker_eq_range_conj hσ hK4 hΨ
  set e' : X ≃* projectiveSL 3 K := e.trans (Id2519.projectiveSLEquivStatedProj 3 K).symm
  refine ⟨K, inferInstance, inferInstance, Ψ.comp (MulAut.congr e').toMonoidHom, hK4,
    fun φ hφ => ?_⟩
  have h1 : MulAut.congr e' φ ∈ Ψ.ker := hφ
  rw [hker] at h1
  obtain ⟨p, hp⟩ := h1
  refine ⟨e'.symm p, MulEquiv.ext fun x => ?_⟩
  have h2 := congrArg (fun f : MulAut (projectiveSL 3 K) => f (e' x)) hp
  simp only [MulAut.conj_apply, MulAut.congr_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply] at h2
  rw [MulAut.conj_apply]
  apply e'.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, h2]

end L4316

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem R₂_inf_K₂_le : R₂ ⊓ K₂ ≤ pCoreOf 2 K₂ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2 inf_le_right
    (fun _ hk => mem_normalizer_inf (s.le_normalizer_R₂ (Subgroup.mem_sup_left hk))
      (Subgroup.le_normalizer hk)) (s.isPGroup_R₂.to_le inf_le_left)

theorem exists_mul_of_mem_R₂ (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) {r : G}
    (hr : r ∈ R₂) : ∃ q ∈ q4311 I K, ∃ k ∈ pCoreOf 2 K₂, r = q * k := by
  have hr' := hr
  rw [s.R₂_eq_P₀] at hr'
  obtain ⟨⟨r', hrK⟩, hrad, rfl⟩ := hr'
  obtain ⟨k, hk, hkα⟩ := s.exists_K₂_of_mem_stE0 (SL3Pt.radE0_le_stE0 hrad)
  have hkR : k ∈ R₂ := by
    rw [s.R₂_eq_P₀]
    refine ⟨⟨k, s.K₂_le_K hk⟩, ?_, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap]
    rw [hkα]
    exact hrad
  have hmem : r' * k⁻¹ ∈ K := K.mul_mem hrK (K.inv_mem (s.K₂_le_K hk))
  refine ⟨r' * k⁻¹, ?_, k, s.R₂_inf_K₂_le ⟨hkR, hk⟩, by simp⟩
  rw [s.mem_q4311_iff h135 hR hC h37 h38 h39 hmem]
  have e : (⟨r' * k⁻¹, hmem⟩ : ↥K) = ⟨r', hrK⟩ * (⟨k, s.K₂_le_K hk⟩ : ↥K)⁻¹ := rfl
  rw [e, map_mul, map_inv, hkα, mul_inv_cancel]

theorem rho_eq_one_of_mem_pCoreOf {k : G} (hk : k ∈ pCoreOf 2 KZ) (hkG : k ∈ s.G₀) :
    s.rho ⟨k, hkG⟩ = 1 := by
  have hkK : k ∈ KZ := pCoreOf_le 2 KZ hk
  rw [s.rho_KZ hkK]
  have h1 : (QuotientGroup.mk ⟨k, hkK⟩ : ModO2 KZ) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact (mem_pCoreOf_iff' _).mp hk
  rw [h1, map_one]

theorem rho_mem_inn_of_mem_Q (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2)
    (hQL : IsPSL 3 2 2 (ModO2 KZ)) {q : G} (hq : q ∈ q4311 I K) (hqG : q ∈ s.G₀) :
    s.rho ⟨q, hqG⟩ ∈ (MulAut.conj : ModO2 KZ →* MulAut (ModO2 KZ)).range := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨K', _, _, Ψ, hK', hΨ⟩ := L4316.exists_outerHom_of_isPSL hQL
  set Inn := (MulAut.conj : ModO2 KZ →* MulAut (ModO2 KZ)).range with hInn
  set Q := q4311 I K with hQ
  have hQ2 : IsPGroup 2 ↥Q := isPGroup_q4311 I K
  have hQR := s.q4311_le_R₂ h135 hR hC h37 h38 h39
  have hYG : Subgroup.zpowers y ≤ s.G₀ := (Subgroup.zpowers_le).mpr s.y_mem_G₀
  set X := (Inn.comap s.rho).map s.G₀.subtype with hX
  have hcomm : ⁅Q, Subgroup.zpowers y⁆ ≤ X := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haG : a ∈ s.G₀ := s.R₂_le_G₀ (hQR ha)
    have hbG : b ∈ s.G₀ := hYG hb
    have hb3 : b ^ 3 = 1 := by
      have h1 := orderOf_dvd_of_mem_zpowers hb
      have h3 : 2 ^ m - 1 = 3 := by rw [hm]; norm_num
      rw [s.orderOf_y, h3] at h1
      exact orderOf_dvd_iff_pow_eq_one.mp h1
    have hYQ : b ∈ Subgroup.normalizer (Q : Set G) :=
      s.K_le_normalizer_q4311 h135 hR hC h37 h38 h39
        ((Subgroup.zpowers_le.mpr s.y_mem) hb)
    have habQ : ⁅a, b⁆ ∈ Q := by
      rw [commutatorElement_def]
      have h1 : b * a⁻¹ * b⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hYQ _).mp (Q.inv_mem ha)
      have e : a * b * a⁻¹ * b⁻¹ = a * (b * a⁻¹ * b⁻¹) := by group
      rw [e]
      exact Q.mul_mem ha h1
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp hQ2) ⟨⁅a, b⁆, habQ⟩
    have hjpow : ⁅a, b⁆ ^ (2 ^ j) = 1 := by
      have := pow_orderOf_eq_one (⟨⁅a, b⁆, habQ⟩ : ↥Q)
      rw [hj] at this
      exact congrArg Subtype.val this
    refine ⟨⟨⁅a, b⁆, s.G₀.mul_mem (s.G₀.mul_mem (s.G₀.mul_mem haG hbG) (s.G₀.inv_mem haG))
      (s.G₀.inv_mem hbG)⟩, hΨ _ ?_, rfl⟩
    set A' : ↥s.G₀ := ⟨a, haG⟩
    set B' : ↥s.G₀ := ⟨b, hbG⟩
    have hAB : (⟨⁅a, b⁆, s.G₀.mul_mem (s.G₀.mul_mem (s.G₀.mul_mem haG hbG) (s.G₀.inv_mem haG))
        (s.G₀.inv_mem hbG)⟩ : ↥s.G₀) = A' * B' * A'⁻¹ * B'⁻¹ := rfl
    have hB3 : B' ^ 3 = 1 := Subtype.ext (by simpa [B'] using hb3)
    have hAB2j : (A' * B' * A'⁻¹ * B'⁻¹) ^ (2 ^ j) = 1 :=
      Subtype.ext (by simpa [A', B', commutatorElement_def] using hjpow)
    have h1 : ∀ x : ↥s.G₀, Ψ (s.rho x) = (Ψ.comp s.rho) x := fun x => rfl
    rw [hAB, h1, map_mul, map_mul, map_mul, map_inv, map_inv]
    refine L4316.commutator_eq_one_of_pow hK' (e := j) ?_ ?_
    · rw [← map_pow, hB3, map_one]
    · rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, ← map_pow, hAB2j, map_one]
  have hQY : Q ≤ ⁅Q, Subgroup.zpowers y⁆ := by
    have hYN : Subgroup.zpowers y ≤ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.zpowers_le.mpr s.y_mem).trans (s.K_le_normalizer_q4311 h135 hR hC h37 h38 h39)
    have : Group.IsNilpotent ↥Q := hQ2.isNilpotent
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers y)) (Nat.card Q) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQ2
      rw [s.card_Y, hk, hm]
      exact Nat.Coprime.pow_right _ (by norm_num)
    have h1 := Setting4311.le_commutator_sup_centralizer' hYN inferInstance hcop
    rw [s.q4311_inf_centralizer_Y, sup_bot_eq] at h1
    exact h1
  obtain ⟨g, hg, hge⟩ := hcomm (hQY hq)
  have : g = ⟨q, hqG⟩ := Subtype.ext hge
  rw [← this]
  exact hg

theorem rho_eq_one_of_mem_Q (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) (hm : m = 2)
    (hZ : Subgroup.center (ModO2 KZ) = ⊥) (hQL : IsPSL 3 2 2 (ModO2 KZ))
    {α' : ↥(KZ ⊔ Subgroup.zpowers y) →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}
    (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ) (hO : pCoreOf 2 K₂ ≤ pCoreOf 2 KZ) {q : G}
    (hq : q ∈ q4311 I K) (hqG : q ∈ s.G₀) : s.rho ⟨q, hqG⟩ = 1 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hF4 : Nat.card F = 4 := by rw [Nat.card_eq_fintype_card, s.card_F, hm]; norm_num
  have hinj : Function.Injective (MulAut.conj : ModO2 KZ →* MulAut (ModO2 KZ)) := by
    rw [← MonoidHom.ker_eq_bot_iff, L4315.ker_conj, hZ]
  obtain ⟨z, hz⟩ := s.rho_mem_inn_of_mem_Q h135 hR hC h37 h38 h39 hm hQL hq hqG
  obtain ⟨k, rfl⟩ := QuotientGroup.mk_surjective z
  have hkΓ : (k : G) ∈ KZ ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left k.2
  have hcomm : ∀ l : G, l ∈ K₂ → ∀ hl : l ∈ KZ ⊔ Subgroup.zpowers y,
      α' ⟨k, hkΓ⟩ * α' ⟨l, hl⟩ = α' ⟨l, hl⟩ * α' ⟨k, hkΓ⟩ := by
    intro l hlK₂ hl
    have hlZ : l ∈ KZ := s.K₂_le_KZ hlK₂
    have hqR : q ∈ R₂ := s.q4311_le_R₂ h135 hR hC h37 h38 h39 hq
    have hql : q * l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 K₂ := by
      refine s.R₂_inf_K₂_le ⟨s.q4311_le_R₂ h135 hR hC h37 h38 h39 ?_, ?_⟩
      · have hlN := s.K_le_normalizer_q4311 h135 hR hC h37 h38 h39 (s.K₂_le_K hlK₂)
        have h1 : l * q⁻¹ * l⁻¹ ∈ q4311 I K :=
          (Subgroup.mem_normalizer_iff.mp hlN _).mp ((q4311 I K).inv_mem hq)
        have e : q * l * q⁻¹ * l⁻¹ = q * (l * q⁻¹ * l⁻¹) := by group
        rw [e]
        exact (q4311 I K).mul_mem hq h1
      · have h1 : q * l * q⁻¹ ∈ K₂ :=
          (Subgroup.mem_normalizer_iff.mp (s.R₂_le_normalizer_K₂ hqR) l).mp hlK₂
        exact K₂.mul_mem h1 (K₂.inv_mem hlK₂)
    have hlG : l ∈ s.G₀ := s.KZ_le_G₀ hlZ
    have hρ : s.rho ⟨q, hqG⟩ * s.rho ⟨l, hlG⟩ = s.rho ⟨l, hlG⟩ * s.rho ⟨q, hqG⟩ := by
      have h1 := s.rho_eq_one_of_mem_pCoreOf (hO hql)
        (s.G₀.mul_mem (s.G₀.mul_mem (s.G₀.mul_mem hqG hlG) (s.G₀.inv_mem hqG))
          (s.G₀.inv_mem hlG))
      have e : (⟨q * l * q⁻¹ * l⁻¹, s.G₀.mul_mem (s.G₀.mul_mem (s.G₀.mul_mem hqG hlG)
          (s.G₀.inv_mem hqG)) (s.G₀.inv_mem hlG)⟩ : ↥s.G₀) =
          ⟨q, hqG⟩ * ⟨l, hlG⟩ * (⟨q, hqG⟩ : ↥s.G₀)⁻¹ * (⟨l, hlG⟩ : ↥s.G₀)⁻¹ := rfl
      rw [e, map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      calc s.rho ⟨q, hqG⟩ * s.rho ⟨l, hlG⟩
          = s.rho ⟨q, hqG⟩ * s.rho ⟨l, hlG⟩ * (s.rho ⟨q, hqG⟩)⁻¹ * (s.rho ⟨l, hlG⟩)⁻¹ *
            (s.rho ⟨l, hlG⟩ * s.rho ⟨q, hqG⟩) := by group
        _ = s.rho ⟨l, hlG⟩ * s.rho ⟨q, hqG⟩ := by rw [h1, one_mul]
    rw [← hz, s.rho_KZ hlZ, ← map_mul, ← map_mul] at hρ
    have h2 := hinj hρ
    have h3 : (k : G) * l * (k : G)⁻¹ * l⁻¹ ∈ pCoreOf 2 KZ := by
      have h4 : (QuotientGroup.mk (k * ⟨l, hlZ⟩ * k⁻¹ * (⟨l, hlZ⟩ : ↥KZ)⁻¹) : ModO2 KZ) = 1 := by
        rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
          QuotientGroup.mk_inv, h2]
        group
      rw [QuotientGroup.eq_one_iff] at h4
      exact (mem_pCoreOf_iff' _).mpr h4
    have h5 : α' (⟨k, hkΓ⟩ * ⟨l, hl⟩ * (⟨k, hkΓ⟩ : ↥(KZ ⊔ Subgroup.zpowers y))⁻¹ *
        (⟨l, hl⟩ : ↥(KZ ⊔ Subgroup.zpowers y))⁻¹) = 1 := (hα'k _).mpr h3
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h5
    calc α' ⟨k, hkΓ⟩ * α' ⟨l, hl⟩
        = α' ⟨k, hkΓ⟩ * α' ⟨l, hl⟩ * (α' ⟨k, hkΓ⟩)⁻¹ * (α' ⟨l, hl⟩)⁻¹ *
          (α' ⟨l, hl⟩ * α' ⟨k, hkΓ⟩) := by group
      _ = α' ⟨l, hl⟩ * α' ⟨k, hkΓ⟩ := by rw [h5, one_mul]
  obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp (isPGroup_q4311 I K)) ⟨q, hq⟩
  have hqj : q ^ (2 ^ j) = 1 := by
    have := pow_orderOf_eq_one (⟨q, hq⟩ : ↥(q4311 I K))
    rw [hj] at this
    exact congrArg Subtype.val this
  have hk2 : α' ⟨k, hkΓ⟩ ^ (2 ^ j) = 1 := by
    have h1 : s.rho ⟨q, hqG⟩ ^ (2 ^ j) = 1 := by
      rw [← map_pow]
      have : (⟨q, hqG⟩ : ↥s.G₀) ^ (2 ^ j) = 1 := Subtype.ext (by simpa using hqj)
      rw [this, map_one]
    rw [← hz, ← map_pow] at h1
    have h2 := hinj (h1.trans (map_one _).symm)
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff] at h2
    have h3 : ((k ^ (2 ^ j) : ↥KZ) : G) ∈ pCoreOf 2 KZ := (mem_pCoreOf_iff' _).mpr h2
    have h4 := (hα'k (⟨k, hkΓ⟩ ^ (2 ^ j))).mpr (by simpa using h3)
    rwa [map_pow] at h4
  obtain ⟨k₁, hk₁, ho, -⟩ := s.exists_k₁ h135 hR hC h37 h38 h39 hm
  have hk₁Γ : k₁ ∈ KZ ⊔ Subgroup.zpowers y := Subgroup.mem_sup_left (s.K₂_le_KZ hk₁)
  have hz5 : α' ⟨k₁, hk₁Γ⟩ ^ 5 = 1 := by
    rw [← map_pow]
    have : (⟨k₁, hk₁Γ⟩ : ↥(KZ ⊔ Subgroup.zpowers y)) ^ 5 = 1 :=
      Subtype.ext (by simp [← ho])
    rw [this, map_one]
  have hz1 : α' ⟨k₁, hk₁Γ⟩ ≠ 1 := by
    intro h1
    have h2 := (hα'k _).mp h1
    obtain ⟨j', hj'⟩ := (IsPGroup.iff_orderOf.mp (pCoreOf_isPGroup 2 KZ)) ⟨k₁, h2⟩
    rw [Subgroup.orderOf_mk, ho] at hj'
    have h3 : 2 ∣ 5 := by
      rcases j' with _ | j'
      · simp at hj'
      · rw [pow_succ] at hj'
        exact ⟨2 ^ j', by omega⟩
    omega
  have hk1 := L4316.pgl_eq_one_of_commute_ord5_of_two_pow hF4 (hcomm k₁ hk₁ hk₁Γ) hk2 hz5 hz1
  have hkO : (k : G) ∈ pCoreOf 2 KZ := (hα'k _).mp hk1
  rw [← hz]
  have : (QuotientGroup.mk k : ModO2 KZ) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact (mem_pCoreOf_iff' _).mp hkO
  rw [this, map_one]

theorem pCoreOf_K₂_not_le (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) (hm : m = 2) (hZ : Subgroup.center (ModO2 KZ) = ⊥)
    (hQL : IsPSL 3 2 2 (ModO2 KZ))
    {α' : ↥(KZ ⊔ Subgroup.zpowers y) →* GL (Fin 3) F ⧸ Subgroup.center (GL (Fin 3) F)}
    (hα'k : ∀ γ, α' γ = 1 ↔ (γ : G) ∈ pCoreOf 2 KZ) : ¬ pCoreOf 2 K₂ ≤ pCoreOf 2 KZ := by
  intro hO
  apply s.map_R₂_ne_bot h135 hR hC h36 h37 h38 h39
  rw [eq_bot_iff]
  rintro _ ⟨⟨r, hrG⟩, hr, rfl⟩
  replace hr : r ∈ R₂ := hr
  obtain ⟨q, hq, k, hk, rfl⟩ := s.exists_mul_of_mem_R₂ h135 hR hC h37 h38 h39 hr
  have hqG : q ∈ s.G₀ := s.R₂_le_G₀ (s.q4311_le_R₂ h135 hR hC h37 h38 h39 hq)
  have hkG : k ∈ s.G₀ := s.KZ_le_G₀ (pCoreOf_le 2 KZ (hO hk))
  have e : (⟨q * k, hrG⟩ : ↥s.G₀) = ⟨q, hqG⟩ * ⟨k, hkG⟩ := rfl
  rw [Subgroup.mem_bot, e, map_mul,
    s.rho_eq_one_of_mem_Q h135 hR hC h37 h38 h39 hm hZ hQL hα'k hO hq,
    s.rho_eq_one_of_mem_pCoreOf (hO hk), mul_one]

end Setting4315

end CFSG.Quasithin.H13.Ch4
