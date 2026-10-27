module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19T
public import CFSG.Quasithin.Vol2.Ch6GL32Parab

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

namespace L619

theorem le_normalizer_of_forall_conj {Γ : Type*} [Group Γ] {H X : Subgroup Γ}
    (h : ∀ g ∈ X, ∀ x ∈ H, g * x * g⁻¹ ∈ H) : X ≤ Subgroup.normalizer (H : Set Γ) :=
  fun g hg => Subgroup.mem_normalizer_iff.mpr fun x => ⟨h g hg x, fun hx => by
    have := h g⁻¹ (X.inv_mem hg) _ hx
    simpa [mul_assoc] using this⟩

theorem isPGroup_ker_comp {A B C : Type*} [Group A] [Group B] [Group C] {p : ℕ} (θ : A →* B)
    (ρ : B →* C) (hθ : IsPGroup p θ.ker) (hρ : IsPGroup p ρ.ker) :
    IsPGroup p (ρ.comp θ).ker := by
  intro x
  obtain ⟨a, ha⟩ := hρ ⟨θ x, x.2⟩
  have ha' : θ ((x : A) ^ p ^ a) = 1 := by
    rw [map_pow]
    simpa using congrArg Subtype.val ha
  obtain ⟨b, hb⟩ := hθ ⟨_, ha'⟩
  refine ⟨a + b, Subtype.ext ?_⟩
  have hb' : ((x : A) ^ p ^ a) ^ p ^ b = 1 := by simpa using congrArg Subtype.val hb
  rw [SubgroupClass.coe_pow, OneMemClass.coe_one, pow_add, pow_mul]
  exact hb'

theorem isPGroup_ker_of_injective {A B : Type*} [Group A] [Group B] {p : ℕ} (θ : A →* B)
    (hθ : Function.Injective θ) : IsPGroup p θ.ker := by
  rw [(MonoidHom.ker_eq_bot_iff θ).mpr hθ]
  exact IsPGroup.of_bot

theorem threePartTop_eq_top_of_simple {Kt : Type*} [Group Kt] [Finite Kt] [IsSimpleGroup Kt]
    (h3 : 3 ∣ Nat.card Kt) : threePartTop Kt = ⊤ := by
  have := threePartTop_normal Kt
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (threePartTop Kt) with h | h
  · exfalso
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨k, hk⟩ := exists_prime_orderOf_dvd_card' (G := Kt) 3 h3
    have hk' : k ^ 3 ^ 1 = 1 := by rw [pow_one, ← hk, pow_orderOf_eq_one]
    have hk3 : k ∈ threePartTop Kt := Subgroup.subset_closure ⟨1, hk'⟩
    rw [h, Subgroup.mem_bot] at hk3
    rw [hk3, orderOf_one] at hk
    omega
  · exact h

theorem threePartTop_GL32 : threePartTop (GL (Fin 3) (ZMod 2)) = ⊤ := by
  have : IsSimpleGroup (GL (Fin 3) (ZMod 2)) := isSimpleGroup_GL32
  exact threePartTop_eq_top_of_simple (by rw [card_GL32]; norm_num)

section ConjIn

variable {G : Type} [Group G] {R : Subgroup G}

@[expose] def conjIn {d : G} (hd : d ∈ Subgroup.normalizer (R : Set G)) : ↥R →* ↥R where
  toFun x := ⟨d * x * d⁻¹, (Subgroup.mem_normalizer_iff.mp hd x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem conjIn_coe {d : G} (hd : d ∈ Subgroup.normalizer (R : Set G)) (x : ↥R) :
    (conjIn hd x : G) = d * x * d⁻¹ := rfl

variable {Kt : Type*} [Group Kt] (ψ₁ : ↥R →* Kt)

theorem mem_normalizer_preimage {Q : Subgroup Kt} {g : G}
    (hg : g ∈ Subgroup.normalizer (R : Set G)) {k : Kt} (hk : k ∈ Q)
    (hconj : ∀ x : ↥R, ψ₁ (conjIn hg x) = k * ψ₁ x * k⁻¹) :
    g ∈ Subgroup.normalizer (((Q.comap ψ₁).map R.subtype : Subgroup G) : Set G) := by
  refine Subgroup.mem_normalizer_iff.mpr fun y => ⟨?_, ?_⟩
  · rintro ⟨x, hx, rfl⟩
    refine ⟨conjIn hg x, ?_, rfl⟩
    show ψ₁ (conjIn hg x) ∈ Q
    rw [hconj]
    exact Q.mul_mem (Q.mul_mem hk hx) (Q.inv_mem hk)
  · rintro ⟨x, hx, hxy⟩
    have hyR : y ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp hg y).mpr (hxy ▸ x.2)
      exact this
    refine ⟨⟨y, hyR⟩, ?_, rfl⟩
    have hx' : ψ₁ x ∈ Q := hx
    have e : x = conjIn hg ⟨y, hyR⟩ := Subtype.ext hxy
    rw [e, hconj] at hx'
    have := Q.mul_mem (Q.mul_mem (Q.inv_mem hk) hx') hk
    simpa [mul_assoc] using this

theorem le_ker_of_normal_two [Finite Kt] (hψ : Function.Surjective ψ₁) [IsSimpleGroup Kt]
    (h3 : 3 ∣ Nat.card Kt) {N : Subgroup G} (hNR : N ≤ R)
    (hRN : R ≤ Subgroup.normalizer (N : Set G)) (hN2 : IsPGroup 2 N) :
    ∀ x (hx : x ∈ N), ψ₁ ⟨x, hNR hx⟩ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnorm : (N.subgroupOf R).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNR).mpr hRN
  have hN2' : IsPGroup 2 (N.subgroupOf R) :=
    hN2.of_equiv (Subgroup.subgroupOfEquivOfLe hNR).symm
  have := hnorm.map ψ₁ hψ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((N.subgroupOf R).map ψ₁) with hb | ht
  · intro x hx
    have : ψ₁ ⟨x, hNR hx⟩ ∈ (N.subgroupOf R).map ψ₁ := ⟨⟨x, hNR hx⟩, hx, rfl⟩
    rwa [hb, Subgroup.mem_bot] at this
  · exfalso
    have h2 : IsPGroup 2 ((N.subgroupOf R).map ψ₁) := hN2'.map ψ₁
    rw [ht] at h2
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp h2
    rw [Subgroup.card_top] at hk
    rw [hk] at h3
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega

theorem psi_conj_eq_of_inner [Finite Kt] (hψ : Function.Surjective ψ₁) {d : G}
    (hd : d ∈ Subgroup.normalizer (R : Set G)) (hd3 : d ^ 3 = 1)
    (hker : ∀ x : ↥R, ψ₁ x = 1 → ψ₁ (conjIn hd x) = 1)
    (hinner : ∀ α : MulAut Kt, α ^ 3 = 1 → ∃ k : Kt, ∀ x, α x = k * x * k⁻¹)
    (hZ : Subgroup.center Kt = ⊥) {U : Subgroup Kt} (hU2 : IsPGroup 2 U)
    (hNU : Subgroup.normalizer (U : Set Kt) ≤ U)
    (hdU : ∀ x : ↥R, ψ₁ x ∈ U → ψ₁ (conjIn hd x) ∈ U) (x : ↥R) :
    ψ₁ (conjIn hd x) = ψ₁ x := by
  classical
  have hle : ψ₁.ker ≤ (ψ₁.comp (conjIn hd)).ker := fun x hx => hker x hx
  set α₀ : Kt →* Kt := ψ₁.liftOfSurjective hψ ⟨ψ₁.comp (conjIn hd), hle⟩ with hα₀def
  have hα₀ : ∀ x, α₀ (ψ₁ x) = ψ₁ (conjIn hd x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hinv : ∀ y : ↥R, conjIn hd (conjIn (Subgroup.inv_mem _ hd) y) = y := fun y =>
    Subtype.ext (by simp only [conjIn_coe]; group)
  have hsurj : Function.Surjective α₀ := by
    intro k
    obtain ⟨y, rfl⟩ := hψ k
    exact ⟨ψ₁ (conjIn (Subgroup.inv_mem _ hd) y), by rw [hα₀, hinv]⟩
  have hbij : Function.Bijective α₀ := ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩
  set α : MulAut Kt := MulEquiv.ofBijective α₀ hbij with hαdef
  have hαapp : ∀ x, α (ψ₁ x) = ψ₁ (conjIn hd x) := hα₀
  have hα3 : α ^ 3 = 1 := by
    refine MulEquiv.ext fun k => ?_
    obtain ⟨y, rfl⟩ := hψ k
    have hdd : d * (d * d) = 1 := by rw [← pow_three]; exact hd3
    have hc : conjIn hd (conjIn hd (conjIn hd y)) = y := by
      apply Subtype.ext
      simp only [conjIn_coe]
      calc d * (d * (d * (y : G) * d⁻¹) * d⁻¹) * d⁻¹ = d * (d * d) * y * (d * (d * d))⁻¹ := by
            simp only [mul_inv_rev, mul_assoc]
        _ = y := by rw [hdd, one_mul, inv_one, mul_one]
    rw [pow_succ, pow_succ, pow_one, MulAut.mul_apply, MulAut.mul_apply, hαapp, hαapp, hαapp,
      hc, MulAut.one_apply]
  obtain ⟨k, hk⟩ := hinner α hα3
  have hα3app : ∀ z, α (α (α z)) = z := fun z => by
    have := congrArg (fun β : MulAut Kt => β z) hα3
    simpa [pow_succ, MulAut.mul_apply] using this
  have hαU : ∀ u ∈ U, α u ∈ U := by
    intro u hu
    obtain ⟨y, rfl⟩ := hψ u
    rw [hαapp]
    exact hdU y hu
  have hkU : k ∈ U := by
    refine hNU (Subgroup.mem_normalizer_iff.mpr fun u => ⟨fun hu => ?_, fun hu => ?_⟩)
    · rw [← hk]
      exact hαU u hu
    · have h1 := hαU _ (hαU _ (show α u ∈ U by rw [hk]; exact hu))
      rwa [hα3app] at h1
  have hk3 : k ^ 3 = 1 := by
    have hc : k ^ 3 ∈ Subgroup.center Kt := by
      rw [Subgroup.mem_center_iff]
      intro z
      have h1 := hα3app z
      rw [hk, hk, hk] at h1
      have : k ^ 3 * z * (k ^ 3)⁻¹ = z := by
        calc k ^ 3 * z * (k ^ 3)⁻¹ = k * (k * (k * z * k⁻¹) * k⁻¹) * k⁻¹ := by
              rw [pow_three]
              simp only [mul_inv_rev, mul_assoc]
          _ = z := h1
      calc z * k ^ 3 = k ^ 3 * z * (k ^ 3)⁻¹ * k ^ 3 := by rw [this]
        _ = k ^ 3 * z := inv_mul_cancel_right _ _
    rw [hZ, Subgroup.mem_bot] at hc
    exact hc
  have hk1 : k = 1 := by
    obtain ⟨b, hb⟩ := hU2 ⟨k, hkU⟩
    have hb' : k ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    have h1 : orderOf k ∣ 3 := orderOf_dvd_of_pow_eq_one hk3
    have h2 : orderOf k ∣ 2 ^ b := orderOf_dvd_of_pow_eq_one hb'
    have hcop : Nat.Coprime 3 (2 ^ b) := Nat.Coprime.pow_right _ (by norm_num)
    have : orderOf k ∣ 1 := by
      rw [← hcop.gcd_eq_one]
      exact Nat.dvd_gcd h1 h2
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp this)
  rw [← hαapp, hk, hk1]
  group

@[expose] noncomputable def conjAut {X : Type} [Group X] {H : Subgroup X} {g : X}
    (hg : g ∈ Subgroup.normalizer (H : Set X)) : MulAut ↥H where
  toFun := conjIn hg
  invFun := conjIn (Subgroup.inv_mem _ hg)
  left_inv x := Subtype.ext (by simp only [conjIn_coe]; group)
  right_inv x := Subtype.ext (by simp only [conjIn_coe]; group)
  map_mul' := map_mul (conjIn hg)

theorem exists_induced_aut [Finite Kt] (hψ : Function.Surjective ψ₁) {d : G}
    (hd : d ∈ Subgroup.normalizer (R : Set G))
    (hker : ∀ x : ↥R, ψ₁ x = 1 → ψ₁ (conjIn hd x) = 1) :
    ∃ α : MulAut Kt, ∀ x, α (ψ₁ x) = ψ₁ (conjIn hd x) := by
  classical
  have hle : ψ₁.ker ≤ (ψ₁.comp (conjIn hd)).ker := fun x hx => hker x hx
  set α₀ : Kt →* Kt := ψ₁.liftOfSurjective hψ ⟨ψ₁.comp (conjIn hd), hle⟩ with hα₀def
  have hα₀ : ∀ x, α₀ (ψ₁ x) = ψ₁ (conjIn hd x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
  have hinv : ∀ y : ↥R, conjIn hd (conjIn (Subgroup.inv_mem _ hd) y) = y := fun y =>
    Subtype.ext (by simp only [conjIn_coe]; group)
  have hsurj : Function.Surjective α₀ := by
    intro k
    obtain ⟨y, rfl⟩ := hψ k
    exact ⟨ψ₁ (conjIn (Subgroup.inv_mem _ hd) y), by rw [hα₀, hinv]⟩
  exact ⟨MulEquiv.ofBijective α₀ ⟨Finite.injective_iff_surjective.mpr hsurj, hsurj⟩, hα₀⟩

end ConjIn

end L619

variable {G : Type} [Group G] [Finite G] {T M L V H : Subgroup G} {n : ℕ} {y : G}

namespace Dat619

variable {z : G} {T' D' : Subgroup G} (hd : Dat619 T M L V H n y z T' D')
include hd

theorem parabolic_of_gl3 (h : Hyp6116 G T M L V n) (h432 : Stmt4_3_2)
    (hW : IsElemAbelian 2 (ch619W T L V z))
    {Ks : Fin 1 → Subgroup (MulAut ↥(L619.V0 hW (ch6ZS T L V)
      (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))))}
    (hdec : G6.IsTransvectionDecomposition
      (L619.img0 hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T'))) Ks)
    (hND : L619.NormDec hW (ch6ZS T L V) (conjClosure (conjSub y V) (ch619I T L V ⊔ T')) Ks)
    (hK : Nonempty (↥(Ks 0) ≃* Matrix.GeneralLinearGroup (Fin 3) (ZMod 2))) :
    ∃ P₁ : Subgroup G, P₁ ≤ ch619I T L V ∧ T' ≤ Subgroup.normalizer (P₁ : Set G) ∧
      D' ≤ Subgroup.normalizer (P₁ : Set G) ∧ ¬ P₁ ≤ M ∧ IsSylowTwoOf (T' ⊓ P₁) P₁ ∧
      Nonempty (oTwoQuot ↥P₁ ≃* Equiv.Perm (Fin 3)) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have c := hd.cfg
  have hz := hd.z619
  have hY := hd.isY
  revert Ks
  set I := ch619I T L V with hI
  set P := conjClosure (conjSub y V) (I ⊔ T') with hP
  set K := L619.img0 hW (ch6ZS T L V) P with hKdef
  set S' := T' ⊓ I with hS'
  set NW := L619.normWZX (ch619W T L V z) (ch6ZS T L V) P with hNW
  intro Ks hdec hND hK
  have hK0 : Ks 0 = K := by
    rw [← hdec.iSup_eq]
    refine le_antisymm (le_iSup Ks 0) (iSup_le fun j => ?_)
    rw [Subsingleton.elim j 0]
  rw [hK0] at hK
  obtain ⟨eK⟩ := hK
  have hcardK : Nat.card K = 168 := by rw [Nat.card_congr eK.toEquiv, L619.card_GL32]
  have h3 : 3 ∣ Nat.card ↥K := by rw [hcardK]; norm_num
  have : IsSimpleGroup ↥K := by
    have := L619.isSimpleGroup_GL32
    exact eK.isSimpleGroup
  have hZK : Subgroup.center ↥K = ⊥ := by
    have := Subgroup.map_center_eq eK
    rw [CFSG.QuasithinUnique.Setup.Family.center_GL32,
      Subgroup.map_eq_bot_iff_of_injective _ eK.injective] at this
    exact this
  have hK3 : L619.threePartTop ↥K = ⊤ := L619.threePartTop_eq_top_of_simple h3
  have hPN := c.conjClosure_E_le_normWZX hY
  set ψ := L619.actOn hW (ch6ZS T L V) P hPN (fun x => L619.act0_mem_img0 hW _ P x.2) with hψ
  have hψs : Function.Surjective ψ := L619.actOn_surjective hW _ P hPN
  have hψ1 : ∀ x : ↥P, ψ x = 1 ↔ (x : G) ∈ ch619K2 T L V z := by
    intro x
    rw [Subtype.ext_iff]
    exact c.act0_eq_one_iff h h432 hz hY hW (x := Subgroup.inclusion hPN x) x.2
  have hcyc : ∀ p [Fact p.Prime], p ≠ 2 → ∀ Q : Sylow p ↥K, IsCyclic Q := fun p hp hp2 Q =>
    CFSG.SectionRank.sylow_isCyclic_of_not_sq_dvd
      (by rw [hcardK]; exact L619.not_sq_dvd_of_small (Or.inr (Or.inr rfl)) hp.out hp2) Q
  have hPK2 : P ⊓ ch619K2 T L V z ≤ pCoreOf 2 P := c.inf_K2_le_pCoreOf h h432 hz hY hW hcyc
  have hker : IsPGroup 2 ψ.ker := by
    have hle : ψ.ker ≤ (pCoreOf 2 P).subgroupOf P := fun x hx =>
      Subgroup.mem_subgroupOf.mpr (hPK2 ⟨x.2, (hψ1 x).mp hx⟩)
    exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 P).of_equiv
      (Subgroup.subgroupOfEquivOfLe (CFSG.LieType.BorelTits.pCoreOf_le 2 P)).symm).to_le hle
  have hPI : P ≤ I := c.conjClosure_E_le_I hY
  have hIP : I ≤ Subgroup.normalizer (P : Set G) :=
    hY.I_le.trans (le_normalizer_conjClosure _ _)
  have hA := L619.threeComp_of ψ ((L619.threePart_le P).trans hPI) hIP hψs hker
    (fun N _ hNn => by
      rw [hK3] at hNn ⊢
      have : N.Normal :=
        ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hNn (Subgroup.mem_top g)) n).mp hn⟩
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N)
    (by rw [hcardK]; decide) h3
  have hO : ∀ x (hx : x ∈ P), x ∈ pCoreOf 2 I → ψ ⟨x, hx⟩ = 1 := fun x hx hxO =>
    (hψ1 ⟨x, hx⟩).mpr (Cfg619.pCoreOf_I_le_K2 h h432 z hxO)
  have hwit := L619.exists_commutator_not_mem ψ hψs hZK h3 hO
  have hP3 : ∀ x ∈ P, ∀ k : ℕ, x ^ 3 ^ k = 1 → x ∈ L619.threePart P :=
    fun x hx k hk => L619.mem_threePart hx hk
  have hDA : D' ≤ Subgroup.normalizer (L619.threePart P : Set G) := fun d hdD =>
    mem_normalizer_of_conjSub_le' (L619.ThreeComp.conjSub_eq_of_pRank hd.rank_I hA hPI hIP hP3
      hwit (hd.D'_le_I hdD) (hd.pow_three_eq_one hdD)).le
  have hS'P : IsSylowTwoOf (S' ⊓ P) P := A4.isSylowTwoOf_inf_normal hd.sylow_S' hPI hIP
  have hkerS : ψ.ker.map P.subtype ≤ S' ⊓ P := by
    rintro _ ⟨x, hx, rfl⟩
    exact F7.isSylowTwoOf_pCoreOf_le hS'P (hPK2 ⟨x.2, (hψ1 x).mp hx⟩)
  have htop : L619.threePartTop ↥K ⊔ ((S' ⊓ P).subgroupOf P).map ψ = ⊤ := by
    rw [hK3, top_sup_eq]
  have hPA : P ≤ L619.threePart P ⊔ (S' ⊓ P) :=
    L619.le_threePart_sup ψ hψs inf_le_right hkerS htop
  have heq : L619.threePart P ⊔ S' = P ⊔ S' :=
    le_antisymm (sup_le_sup_right (L619.threePart_le P) _)
      (sup_le (hPA.trans (sup_le_sup_left inf_le_left _)) le_sup_right)
  have hRI : P ⊔ S' ≤ I := sup_le hPI inf_le_right
  have hRN : P ⊔ S' ≤ NW := hRI.trans (hY.I_le.trans (Cfg619.Y_le_normWZX hY))
  have hTN : T' ≤ NW := fun t ht => Cfg619.Y_le_normWZX hY (Subgroup.mem_sup_right ht)
  let β : ↥NW →* ↥K :=
    (L619.act0 hW (ch6ZS T L V) P).codRestrict K fun g =>
      L619.act0_mem_img0_of_normDec hW _ P hdec hND g
  let ψ₁ : ↥(P ⊔ S') →* ↥K := β.comp (Subgroup.inclusion hRN)
  have hcomp : ∀ x : ↥P, ψ₁ (Subgroup.inclusion le_sup_left x) = ψ x := fun x => rfl
  have hψ₁s : Function.Surjective ψ₁ := fun k => by
    obtain ⟨x, rfl⟩ := hψs k
    exact ⟨_, hcomp x⟩
  have hker₁ : IsPGroup 2 ψ₁.ker :=
    L619.isPGroup_ker_sup ψ hd.sylow_S'.2.1 (inf_le_right.trans hIP) hψs hker ψ₁ hcomp
  have hS'R : IsSylowTwoOf S' (P ⊔ S') :=
    F7.isSylowTwoOf_mono_right hd.sylow_S' le_sup_right hRI
  set U : Subgroup ↥K := (S'.subgroupOf (P ⊔ S')).map ψ₁ with hU
  have hUsyl : IsSylowTwoOf U ⊤ := L619.isSylowTwoOf_map_surj hS'R ψ₁ hψ₁s
  obtain ⟨hNU, Q, hUQ, hQ, hρ⟩ := L619.gl32_parabolics eK hUsyl
  have hTS' : ∀ t ∈ T', t ∈ Subgroup.normalizer (S' : Set G) := fun t ht =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer ht, hd.T'_le_I ht⟩
  have hTR : ∀ t ∈ T', t ∈ Subgroup.normalizer ((P ⊔ S' : Subgroup G) : Set G) := fun t ht =>
    L619.mem_normalizer_sup
      (le_normalizer_conjClosure _ _ (Subgroup.mem_sup_right ht : t ∈ I ⊔ T'))
      (hTS' t ht)
  have hDR : ∀ d ∈ D', d ∈ Subgroup.normalizer ((P ⊔ S' : Subgroup G) : Set G) :=
    fun d hdD => by
      rw [← heq]
      exact L619.mem_normalizer_sup (hDA hdD) (hd.D'_le_S' hdD)
  have hβconj : ∀ (g : ↥NW) (hgR : (g : G) ∈ Subgroup.normalizer ((P ⊔ S' : Subgroup G) : Set G))
      (x : ↥(P ⊔ S')), ψ₁ (L619.conjIn hgR x) = β g * ψ₁ x * (β g)⁻¹ := by
    intro g hgR x
    have e : Subgroup.inclusion hRN (L619.conjIn hgR x) =
        g * Subgroup.inclusion hRN x * g⁻¹ := Subtype.ext rfl
    show β (Subgroup.inclusion hRN (L619.conjIn hgR x)) = _
    rw [e, map_mul, map_mul, map_inv]
    rfl
  have hXT : (T'.subgroupOf NW).map β ≤ Subgroup.normalizer (U : Set ↥K) := by
    refine L619.le_normalizer_of_forall_conj fun k hk u hu => ?_
    obtain ⟨t', ht', rfl⟩ := hk
    obtain ⟨s, hs, rfl⟩ := hu
    have ht'' : (t' : G) ∈ T' := Subgroup.mem_subgroupOf.mp ht'
    rw [← hβconj t' (hTR _ ht'') s]
    exact ⟨_, Subgroup.mem_subgroupOf.mpr ((Subgroup.mem_normalizer_iff.mp (hTS' _ ht'') s).mp
      (Subgroup.mem_subgroupOf.mp hs)), rfl⟩
  have hTU : ∀ t (ht : t ∈ T'), β ⟨t, hTN ht⟩ ∈ U := fun t ht =>
    hNU (hXT ⟨⟨t, hTN ht⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩)
  have hdcent : ∀ d (hdD : d ∈ D') (x : ↥(P ⊔ S')), ψ₁ (L619.conjIn (hDR d hdD) x) = ψ₁ x := by
    intro d hdD x
    have hdR := hDR d hdD
    have hkerd : ∀ x : ↥(P ⊔ S'), ψ₁ x = 1 → ψ₁ (L619.conjIn hdR x) = 1 := by
      set N : Subgroup G := (ψ₁.ker.map (P ⊔ S').subtype).map (MulAut.conj d).toMonoidHom
        with hN
      have hNR : N ≤ P ⊔ S' := by
        rintro _ ⟨_, ⟨w, -, rfl⟩, rfl⟩
        exact (Subgroup.mem_normalizer_iff.mp hdR w).mp w.2
      have hRNn : P ⊔ S' ≤ Subgroup.normalizer (N : Set G) := by
        refine L619.le_normalizer_of_forall_conj fun r hr v hv => ?_
        obtain ⟨_, ⟨w, hw, rfl⟩, rfl⟩ := hv
        have hr' : d⁻¹ * r * d ∈ P ⊔ S' := by
          have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hdR) r).mp hr
          simpa using this
        let r' : ↥(P ⊔ S') := ⟨d⁻¹ * r * d, hr'⟩
        refine ⟨((r' * w * r'⁻¹ : ↥(P ⊔ S')) : G), ⟨r' * w * r'⁻¹, ?_, rfl⟩, ?_⟩
        · rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_mul, map_inv,
            MonoidHom.mem_ker.mp hw, mul_one, mul_inv_cancel]
        · simp only [MulEquiv.toMonoidHom_eq_coe, MonoidHom.coe_ofClass, MulAut.conj_apply,
            Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_subtype, r']
          group
      have hN2 : IsPGroup 2 N := (hker₁.map (P ⊔ S').subtype).map _
      have hle := L619.le_ker_of_normal_two ψ₁ hψ₁s h3 hNR hRNn hN2
      intro x hx
      exact hle (d * x * d⁻¹) ⟨x, ⟨x, hx, rfl⟩, rfl⟩
    refine L619.psi_conj_eq_of_inner ψ₁ hψ₁s hdR (hd.pow_three_eq_one hdD) hkerd
      (L619.inner_of_cube_GL32 eK) hZK hUsyl.2.1 hNU ?_ x
    intro w hw
    obtain ⟨s, hs, hsw⟩ := hw
    have hκ : ψ₁ (s⁻¹ * w) = 1 := by rw [map_mul, map_inv, hsw, inv_mul_cancel]
    have e : w = s * (s⁻¹ * w) := by group
    rw [e, map_mul, map_mul, hkerd _ hκ, mul_one]
    exact ⟨L619.conjIn hdR s, Subgroup.mem_subgroupOf.mpr
      ((Subgroup.mem_normalizer_iff.mp (hd.D'_le_S' hdD) s).mp (Subgroup.mem_subgroupOf.mp hs)),
      rfl⟩
  set Pj : Fin 2 → Subgroup G := fun j => ((Q j).comap ψ₁).map (P ⊔ S').subtype with hPj
  have hPjR : ∀ j, Pj j ≤ P ⊔ S' := fun j => Subgroup.map_subtype_le _
  have hS'Pj : ∀ j, S' ≤ Pj j := fun j s hs =>
    ⟨⟨s, Subgroup.mem_sup_right hs⟩,
      hUQ j ⟨⟨s, Subgroup.mem_sup_right hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩, rfl⟩
  have hTPj : ∀ j, T' ≤ Subgroup.normalizer (Pj j : Set G) := fun j t ht =>
    L619.mem_normalizer_preimage ψ₁ (hTR t ht) (hUQ j (hTU t ht))
      (hβconj ⟨t, hTN ht⟩ (hTR t ht))
  have hDPj : ∀ j, D' ≤ Subgroup.normalizer (Pj j : Set G) := fun j d hdD =>
    L619.mem_normalizer_preimage ψ₁ (hDR d hdD) (Q j).one_mem fun x => by
      rw [hdcent d hdD x]
      group
  have hsup : ∀ x ∈ P, x ∈ Pj 0 ⊔ Pj 1 := by
    intro x hx
    have hx' : (⟨x, Subgroup.mem_sup_left hx⟩ : ↥(P ⊔ S')) ∈ (Q 0).comap ψ₁ ⊔ (Q 1).comap ψ₁ := by
      rw [Subgroup.comap_sup_eq ψ₁ _ _ hψ₁s, hQ, Subgroup.comap_top]
      exact Subgroup.mem_top _
    have := Subgroup.mem_map_of_mem (P ⊔ S').subtype hx'
    rwa [Subgroup.map_sup] at this
  obtain ⟨j, hjM⟩ : ∃ j, ¬ Pj j ≤ M := by
    by_contra hall
    push Not at hall
    exact c.not_le_M h h432 ((conjClosure_mono le_rfl hY.I_le).trans
      fun x hx => sup_le (hall 0) (hall 1) (hsup x hx))
  obtain ⟨ρ, hρs, hρk⟩ := hρ j
  obtain ⟨e₂⟩ := L619.nonempty_gl2_mulEquiv_perm3'
  have hPjI : Pj j ≤ I := (hPjR j).trans hRI
  refine ⟨Pj j, hPjI, hTPj j, hDPj j, hjM, ?_, ?_⟩
  · have heqS : T' ⊓ Pj j = S' :=
      le_antisymm (le_inf inf_le_left (inf_le_right.trans hPjI)) (le_inf inf_le_left (hS'Pj j))
    rw [heqS]
    exact F7.isSylowTwoOf_mono_right hd.sylow_S' (hS'Pj j) hPjI
  ·
    let ι := Subgroup.equivMapOfInjective ((Q j).comap ψ₁) (P ⊔ S').subtype
      (P ⊔ S').subtype_injective
    let θ : ↥(Pj j) →* ↥(Q j) := (ψ₁.subgroupComap (Q j)).comp ι.symm.toMonoidHom
    have hθs : Function.Surjective θ :=
      (MonoidHom.subgroupComap_surjective ψ₁ (Q j) hψ₁s).comp ι.symm.surjective
    have hsk : IsPGroup 2 (ψ₁.subgroupComap (Q j)).ker := by
      refine (hker₁.comap_of_injective ((Q j).comap ψ₁).subtype
        ((Q j).comap ψ₁).subtype_injective).to_le ?_
      intro x hx
      rw [Subgroup.mem_comap, MonoidHom.mem_ker]
      have h0 : (ψ₁.subgroupComap (Q j)) x = 1 := hx
      exact congrArg Subtype.val h0
    have hθk : IsPGroup 2 θ.ker :=
      L619.isPGroup_ker_comp _ _ (L619.isPGroup_ker_of_injective _ ι.symm.injective) hsk
    exact nonempty_quot_perm3_of_surjective (e₂.toMonoidHom.comp (ρ.comp θ))
      (e₂.surjective.comp (hρs.comp hθs))
      (L619.isPGroup_ker_comp _ _ (L619.isPGroup_ker_comp _ _ hθk hρk)
        (L619.isPGroup_ker_of_injective _ e₂.injective))

end Dat619

end CFSG.Quasithin.H13
