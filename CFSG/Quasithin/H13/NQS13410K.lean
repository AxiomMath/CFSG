module

public import CFSG.Quasithin.H13.U3FrameProducer
public import CFSG.Quasithin.H13.NQS1345B
public import CFSG.Quasithin.Vol2.Ch11SecCB51Trans
public import CFSG.Quasithin.Vol2.Ch11SecCB51Sum
public import CFSG.Quasithin.Vol2.Ch11SecCB51Ord
public import CFSG.Quasithin.Background.B4L3Coord
public import CFSG.Quasithin.Background.B5NonId
public import CFSG.Quasithin.Recognition.HSTypeModels

public section

namespace CFSG.Quasithin.H13.NQS134

open Subgroup CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.InternalSec
open CFSG.Assembly.LowTwoRank
open scoped IsMulCommutative

variable {G : Type} [Group G]

theorem l3vec_sq : ∀ m : Multiplicative L3.Vec, m ^ 2 = 1 := by decide

theorem autOn_eq_top_of_l32 [Finite G] {K X : Subgroup G} [IsMulCommutative ↥X]
    (hnat : BinaryNaturalSL (V := ↥X) (autOn K X) ⊤ ⊥ 3 1) : autOn K X = ⊤ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨D⟩ := hnat.toL3Coord
  have h1 : Nat.card ↥(autOn K X) = 168 := by
    rw [← Nat.card_congr (MulEquiv.ofBijective D.π ⟨D.π_injective, D.π_surj⟩).toEquiv]
    exact HSType.card_SL_three_two
  have hinj : Function.Injective D.β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (mem_bot.1 ((D.ker_β u).1 hu))
  have hX8 : Nat.card ↥X = 8 := by
    have h2 := Nat.card_congr (Equiv.ofBijective D.β ⟨hinj, D.β_surj⟩)
    rw [Subgroup.card_top, Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
      Nat.card_fin] at h2
    rw [h2]
    norm_num
  have hsq : ∀ a : ↥X, a ^ 2 = 1 := by
    intro a
    have h3 : D.β ⟨a ^ 2, mem_top _⟩ = 1 := by
      rw [show (⟨a ^ 2, mem_top _⟩ : ↥(⊤ : Subgroup ↥X)) = ⟨a, mem_top a⟩ ^ 2 from rfl, map_pow]
      exact l3vec_sq _
    exact mem_bot.1 ((D.ker_β _).1 h3)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 2) (n := 3)
    (W := ↥X) (fun a b => (inferInstance : IsMulCommutative ↥X).is_comm.comm a b) hsq
    (by rw [hX8]; norm_num)
  have h2 : Nat.card (MulAut ↥X) = 168 := by
    rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod]
    decide
  exact Subgroup.eq_top_of_card_eq _ (by rw [h1, h2])

theorem exists_mem_eq_conj {K X : Subgroup G} (htop : autOn K X = ⊤) {g : G}
    (hg : g ∈ normalizer (X : Set G)) : ∃ k ∈ K, ∀ x ∈ X, g * x * g⁻¹ = k * x * k⁻¹ := by
  have h1 : conjAct X ⟨g, hg⟩ ∈ autOn K X := by rw [htop]; exact mem_top _
  obtain ⟨k', hk', hk'e⟩ := Subgroup.mem_map.1 h1
  refine ⟨k', mem_subgroupOf.1 hk', fun x hx => ?_⟩
  have h2 := congrArg (fun σ : MulAut ↥X => ((σ ⟨x, hx⟩ : ↥X) : G)) hk'e
  simp only [A5.conjAct_val] at h2
  exact h2.symm

theorem isPGroup_sup_inf_centralizer [Finite G] {T K X : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (hC : IsPGroup 2 ↥(K ⊓ centralizer (X : Set G))) :
    IsPGroup 2 ↥((K ⊔ T) ⊓ centralizer (X : Set G)) := by
  intro c
  obtain ⟨k, hk⟩ := U3.exists_pow_two_pow_mem_of_mem_sup hT hTK (mem_inf.1 c.2).1
  have hkC : (c : G) ^ 2 ^ k ∈ K ⊓ centralizer (X : Set G) :=
    mem_inf.2 ⟨hk, pow_mem (mem_inf.1 c.2).2 _⟩
  obtain ⟨m, hm⟩ := hC ⟨_, hkC⟩
  refine ⟨k + m, Subtype.ext ?_⟩
  have h1 : ((c : G) ^ 2 ^ k) ^ 2 ^ m = 1 := by
    have h2 := congrArg Subtype.val hm
    simp only [Subgroup.coe_pow, Subgroup.coe_one] at h2
    exact h2
  rw [Subgroup.coe_pow, pow_add, pow_mul, h1, Subgroup.coe_one]

theorem exists_conj_R2 [Finite G] {T K X : Subgroup G} (hTsyl : IsSylowTwoOf T (K ⊔ T))
    (hTK : T ≤ normalizer (K : Set G)) (hKX : K ≤ normalizer (X : Set G))
    (hTX : T ≤ normalizer (X : Set G)) (htop : autOn K X = ⊤)
    (hC : IsPGroup 2 ↥(K ⊓ centralizer (X : Set G))) {t : G} (ht : t ∈ T) :
    ∃ k ∈ K, ∀ u ∈ reducedAggregate (K ⊔ T), t * u * t⁻¹ = k * u * k⁻¹ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk, hkx⟩ := exists_mem_eq_conj htop (hTX ht)
  set N := (K ⊔ T) ⊓ centralizer (X : Set G) with hN
  have hNn : K ⊔ T ≤ normalizer (N : Set G) := by
    refine A5.le_normalizer_of_forall_conj_mem fun g hg c hc => ?_
    obtain ⟨hcKT, hcX⟩ := mem_inf.1 hc
    refine mem_inf.2 ⟨mul_mem (mul_mem hg hcKT) (inv_mem hg), mem_centralizer_iff.2 fun x hx => ?_⟩
    have hgX : g ∈ normalizer (X : Set G) := sup_le hKX hTX hg
    have hx' : g⁻¹ * x * g⁻¹⁻¹ ∈ X := (mem_normalizer_iff.mp (inv_mem hgX) x).mp hx
    have h1 := mem_centralizer_iff.mp hcX _ hx'
    calc x * (g * c * g⁻¹) = g * ((g⁻¹ * x * g⁻¹⁻¹) * c) * g⁻¹ := by group
      _ = g * (c * (g⁻¹ * x * g⁻¹⁻¹)) * g⁻¹ := by rw [h1]
      _ = g * c * g⁻¹ * x := by group
  have hNO : N ≤ pCoreOf 2 (K ⊔ T) :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hNn
      (isPGroup_sup_inf_centralizer hTsyl.2.1 hTK hC)
  have hkt : k⁻¹ * t ∈ N := by
    refine mem_inf.2 ⟨mul_mem (inv_mem (mem_sup_left hk)) (mem_sup_right ht),
      mem_centralizer_iff.2 fun x hx => ?_⟩
    have h1 := hkx x hx
    calc x * (k⁻¹ * t) = k⁻¹ * (k * x * k⁻¹) * k * k⁻¹ * t := by group
      _ = k⁻¹ * (t * x * t⁻¹) * k * k⁻¹ * t := by rw [h1]
      _ = k⁻¹ * t * x := by group
  refine ⟨k, hk, fun u hu => ?_⟩
  have h1 := mem_centralizer_iff.mp (pCoreOf_le_centralizer_R2 (K ⊔ T) (hNO hkt)) u hu
  calc t * u * t⁻¹ = k * (k⁻¹ * t * u) * t⁻¹ := by group
    _ = k * (u * (k⁻¹ * t)) * t⁻¹ := by rw [← h1]
    _ = k * u * k⁻¹ := by group

theorem isMulCommutative_of_le' {U W : Subgroup G} [IsMulCommutative ↥W] (hUW : U ≤ W) :
    IsMulCommutative ↥U :=
  IsMulCommutative.of_comm fun a b => Subtype.ext (show (a : G) * b = b * a from
    congrArg Subtype.val (mul_comm (⟨a, hUW a.2⟩ : ↥W) ⟨b, hUW b.2⟩))

theorem exists_two_copies [Finite G] {K W : Subgroup G} [IsMulCommutative ↥W]
    (hKW : K ≤ normalizer (W : Set G)) {J : Subgroup (MulAut ↥W)}
    (hii : B51Case1ii J (autOn K W)) (h168 : Nat.card ↥(autOn K W) ≤ 168) :
    ∃ I₀ I₁ : Subgroup G, I₀ ≤ W ∧ I₁ ≤ W ∧ K ≤ normalizer (I₀ : Set G) ∧
      K ≤ normalizer (I₁ : Set G) ∧ I₀ ⊓ I₁ = ⊥ ∧ I₀ ⊔ I₁ = ⁅W, K⁆ ∧
      (∃ _ : IsMulCommutative ↥I₀, BinaryNaturalSL (V := ↥I₀) (autOn K I₀) ⊤ ⊥ 3 1) ∧
      ∃ φ : ↥I₀ ≃* ↥I₁, ∀ k ∈ K, ∀ (u : ↥I₀) (hu : k * (u : G) * k⁻¹ ∈ I₀),
        ((φ ⟨k * u * k⁻¹, hu⟩ : ↥I₁) : G) = k * (φ u : G) * k⁻¹ := by
  obtain ⟨-, n', F, _, _, hF, I', π, hind, hsup, hreal, -, -⟩ := hii
  have hn : n' = 1 := by
    have hinj := B5.realizesVia_injective (FFModel.nat_faithful _) (hreal 0)
    have hcard := Nat.card_congr (Equiv.ofBijective π ⟨hinj, (hreal 0).1⟩)
    rw [← Nat.card_congr (specialLinearGroupEquivStatedSL 3 F).toEquiv,
      Vol2.Ch11.SecC.B51.card_SL3_eq_pow hF] at hcard
    have h1 := Vol2.Ch11.SecC.B51.one_le_of_card_eq hF
    by_contra hne
    have h64 : 64 ≤ 2 ^ (3 * n') :=
      (show (64 : ℕ) = 2 ^ 6 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
    have h16 : 16 ≤ 2 ^ (2 * n') :=
      (show (16 : ℕ) = 2 ^ 4 by norm_num) ▸ Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 63 * 15 ≤ (2 ^ (3 * n') - 1) * (2 ^ (2 * n') - 1) :=
      Nat.mul_le_mul (by omega) (by omega)
    have h4 : 64 * (63 * 15) ≤ 2 ^ (3 * n') * ((2 ^ (3 * n') - 1) * (2 ^ (2 * n') - 1)) :=
      Nat.mul_le_mul h64 h3
    omega
  subst hn
  have h01 : I' 0 ⊔ I' 1 = commV (autOn K W) := by
    rw [← hsup]
    refine le_antisymm (sup_le (le_iSup I' 0) (le_iSup I' 1)) (iSup_le fun i => ?_)
    fin_cases i
    · exact le_sup_left
    · exact le_sup_right
  have hdisj : I' 0 ⊓ I' 1 = ⊥ := disjoint_iff.mp (hind.pairwiseDisjoint (by decide))
  have hinv : ∀ i, ∀ σ ∈ autOn K W, ∀ u ∈ I' i, σ u ∈ I' i :=
    fun i σ hσ u hu => (hreal i).2.2.2.1 ⟨σ, hσ⟩ u hu
  set I₀ : Subgroup G := (I' 0).map W.subtype with hI₀
  set I₁ : Subgroup G := (I' 1).map W.subtype with hI₁
  have hI₀W : I₀ ≤ W := Subgroup.map_subtype_le _
  have hI₁W : I₁ ≤ W := Subgroup.map_subtype_le _
  have hJ₀ : I₀.subgroupOf W = I' 0 :=
    Subgroup.comap_map_eq_self_of_injective W.subtype_injective _
  have hU : I₀ ⊔ I₁ = ⁅W, K⁆ := by
    rw [hI₀, hI₁, ← Subgroup.map_sup, h01, Vol2.Ch11.SecC.B51.map_commV_autOn hKW]
  have hKI₀ : K ≤ normalizer (I₀ : Set G) :=
    Vol2.Ch11.SecC.B51.le_normalizer_map_of_inv hKW (hinv 0)
  have hKI₁ : K ≤ normalizer (I₁ : Set G) :=
    Vol2.Ch11.SecC.B51.le_normalizer_map_of_inv hKW (hinv 1)
  have hc₀ : IsMulCommutative ↥I₀ := isMulCommutative_of_le' hI₀W
  have hnat₀ : BinaryNaturalSL (V := ↥I₀) (autOn K I₀) ⊤ ⊥ 3 1 := by
    have h3 : BinaryNaturalSL (autOn K W) (I₀.subgroupOf W) ((⊥ : Subgroup G).subgroupOf W)
        3 1 := by
      rw [hJ₀, Subgroup.bot_subgroupOf]
      exact ⟨F, inferInstance, inferInstance, hF, π, hreal 0⟩
    have h4 := Vol2.Ch11.SecC.B51.binaryNaturalSL_res hKW hKI₀ hI₀W h3
    rwa [Subgroup.bot_subgroupOf] at h4
  have hinf : I₀ ⊓ I₁ = ⊥ := by
    rw [hI₀, hI₁, ← Subgroup.map_inf_eq _ _ _ W.subtype_injective, hdisj, Subgroup.map_bot]
  obtain ⟨e, he⟩ := equiv_of_secIsoL
    (Vol2.Ch11.SecC.B51.secIsoL_of_realizesVia (hreal 0) (hreal 1))
  set ι₀ := Subgroup.equivMapOfInjective (I' 0) W.subtype W.subtype_injective with hι₀
  set ι₁ := Subgroup.equivMapOfInjective (I' 1) W.subtype W.subtype_injective with hι₁
  refine ⟨I₀, I₁, hI₀W, hI₁W, hKI₀, hKI₁, hinf, hU, ⟨hc₀, hnat₀⟩,
    (ι₀.symm.trans e).trans ι₁, fun k hk u hu => ?_⟩
  set w : ↥(I' 0) := ι₀.symm u with hw
  have hwu : (((w : ↥W) : G)) = u := by
    have := congrArg Subtype.val (ι₀.apply_symm_apply u)
    rw [← hw] at this
    exact this
  set σ : ↥(autOn K W) := ⟨conjAct W ⟨k, hKW hk⟩, conjAct_mem_autOn hKW hk⟩ with hσ
  have hσw : ∀ v : ↥W, (((σ : MulAut ↥W) v : ↥W) : G) = k * v * k⁻¹ :=
    fun v => A5.conjAct_val W ⟨k, hKW hk⟩ v
  have hmem₀ : (σ : MulAut ↥W) w ∈ I' 0 := hinv 0 σ σ.2 w w.2
  have hmem₁ : (σ : MulAut ↥W) (e w) ∈ I' 1 := hinv 1 σ σ.2 _ (e w).2
  have key := he σ w hmem₀ hmem₁
  have hu' : ι₀.symm ⟨k * u * k⁻¹, hu⟩ = ⟨(σ : MulAut ↥W) w, hmem₀⟩ := by
    apply ι₀.injective
    rw [MulEquiv.apply_symm_apply]
    apply Subtype.ext
    show k * (u : G) * k⁻¹ = (((σ : MulAut ↥W) w : ↥W) : G)
    rw [hσw, hwu]
  show ((ι₁ (e (ι₀.symm ⟨k * u * k⁻¹, hu⟩)) : ↥I₁) : G) = k * ((ι₁ (e w) : ↥I₁) : G) * k⁻¹
  rw [hu', key]
  show (((σ : MulAut ↥W) (e w) : ↥W) : G) = k * (((e w : ↥(I' 1)) : ↥W) : G) * k⁻¹
  rw [hσw]

end CFSG.Quasithin.H13.NQS134
