module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCoreA
public import CFSG.SignalizerFunctorTheorem.CatalogBridge.DicksonNonLocal

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.Assembly.LowTwoRank Matrix CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
  CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

private theorem conj_mem_sup_S3 {K A : Subgroup G} {g : G}
    (hK : g ∈ Subgroup.normalizer (K : Set G)) (hA : g ∈ Subgroup.normalizer (A : Set G)) {x : G}
    (hx : x ∈ K ⊔ A) : g * x * g⁻¹ ∈ K ⊔ A := by
  have hle : K ⊔ A ≤ (K ⊔ A).comap (MulAut.conj g).toMonoidHom := by
    refine sup_le (fun k hk => ?_) (fun a ha => ?_)
    · rw [Subgroup.mem_comap]
      exact (le_sup_left : K ≤ K ⊔ A) ((Subgroup.mem_normalizer_iff.mp hK k).mp hk)
    · rw [Subgroup.mem_comap]
      exact (le_sup_right : A ≤ K ⊔ A) ((Subgroup.mem_normalizer_iff.mp hA a).mp ha)
  exact hle hx

private theorem normalizer_sup_S3 {K A : Subgroup G} {g : G}
    (hK : g ∈ Subgroup.normalizer (K : Set G)) (hA : g ∈ Subgroup.normalizer (A : Set G)) :
    g ∈ Subgroup.normalizer ((K ⊔ A : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact conj_mem_sup_S3 hK hA hx
  · intro hx
    have := conj_mem_sup_S3 (Subgroup.inv_mem _ hK) (Subgroup.inv_mem _ hA) hx
    simpa [mul_assoc] using this

private theorem charP_two_of_card_S3 {F : Type} [Field F] [Fintype F] {n : ℕ}
    (hF : Fintype.card F = 2 ^ n) : CharP F 2 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact charP_of_card_eq_prime_pow hF

private theorem eq_one_of_sq_eq_one_S3 {F : Type} [Field F] [CharP F 2] {r : F}
    (hr : r ^ 2 = 1) : r = 1 := by
  have h2 : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
  have h : (r - 1) ^ 2 = 0 := by linear_combination hr + (1 - r) * h2
  exact sub_eq_zero.mp ((pow_eq_zero_iff two_ne_zero).mp h)

private theorem center_sl2_eq_bot_S3 {F : Type} [Field F] [CharP F 2] :
    Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hAr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  obtain rfl := eq_one_of_sq_eq_one_S3 hr
  rw [Subgroup.mem_bot]
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  have hA1 : (A : Matrix (Fin 2) (Fin 2) F) = 1 := by rw [← hAr, map_one]
  simp [hA1]

private theorem isSimpleGroup_sl2_S3 {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) F) := by
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) F) :=
    (CFSG.SignalizerFunctorTheorem.CatalogBridge.psl2_simple_not_isSolvable h4).1
  have hinj : Function.Injective
      (QuotientGroup.mk' (Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) F))) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', center_sl2_eq_bot_S3]
  exact (MulEquiv.ofBijective (QuotientGroup.mk' (Subgroup.center
    (Matrix.SpecialLinearGroup (Fin 2) F))) ⟨hinj, QuotientGroup.mk'_surjective _⟩).isSimpleGroup

private theorem isSimpleGroup_statedSL2_S3 {F : Type} [Field F] [Finite F] [CharP F 2]
    (h4 : 4 ≤ Nat.card F) : IsSimpleGroup ↥(StatedSL 2 F) := by
  haveI := isSimpleGroup_sl2_S3 h4
  exact (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 F).symm.isSimpleGroup

theorem le_of_mem_sup_of_ne_one {H K Y : Subgroup G}
    (hKN : H ≤ Subgroup.normalizer (K : Set G)) (hYH : Y ≤ H) (hYp : ⁅Y, Y⁆ = Y)
    {F : Type} [Field F] [Fintype F] {n : ℕ} (hn : 2 ≤ n) (hF : Fintype.card F = 2 ^ n)
    (ρ : ↥Y →* ↥(StatedSL 2 F)) (hρ : Function.Surjective ρ) (hρ2 : IsPGroup 2 ρ.ker)
    {y₀ : G} (hy₀Y : y₀ ∈ Y) (hρy : ρ ⟨y₀, hy₀Y⟩ ≠ 1) (hy₀ : y₀ ∈ K ⊔ pCoreOf 2 H) : Y ≤ K := by
  have hAH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hAK : pCoreOf 2 H ≤ Subgroup.normalizer (K : Set G) :=
    (CFSG.LieType.BorelTits.pCoreOf_le 2 H).trans hKN
  have hAsolv : Group.IsSolvable ↥(pCoreOf 2 H) := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    haveI : Group.IsNilpotent ↥(pCoreOf 2 H) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).isNilpotent
    infer_instance
  have hXN : H ≤ Subgroup.normalizer ((K ⊔ pCoreOf 2 H : Subgroup G) : Set G) := by
    intro g hg
    exact normalizer_sup_S3 (hKN hg) (hAH hg)
  set N₁ : Subgroup ↥Y := (K ⊔ pCoreOf 2 H).subgroupOf Y with hN₁def
  have hN₁ : N₁.Normal := by
    refine ⟨fun m hm g => ?_⟩
    rw [hN₁def, Subgroup.mem_subgroupOf] at hm ⊢
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact conj_mem_sup_S3 (hKN (hYH g.2)) (hAH (hYH g.2)) hm
  have h4 : 4 ≤ Nat.card F := by
    rw [Nat.card_eq_fintype_card, hF]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  haveI : CharP F 2 := charP_two_of_card_S3 hF
  haveI : IsSimpleGroup ↥(StatedSL 2 F) := isSimpleGroup_statedSL2_S3 h4
  have hMn : (N₁.map ρ).Normal := Subgroup.Normal.map hN₁ ρ hρ
  have hy₀N : (⟨y₀, hy₀Y⟩ : ↥Y) ∈ N₁ := Subgroup.mem_subgroupOf.mpr hy₀
  have hMne : N₁.map ρ ≠ ⊥ := by
    intro h
    apply hρy
    have hmem : ρ ⟨y₀, hy₀Y⟩ ∈ N₁.map ρ := Subgroup.mem_map_of_mem ρ hy₀N
    rw [h, Subgroup.mem_bot] at hmem
    exact hmem
  have hMtop : N₁.map ρ = ⊤ :=
    (Subgroup.Normal.eq_bot_or_eq_top (N₁.map ρ)).resolve_left hMne
  have hρN : ∀ z : ↥Y, ∃ m ∈ N₁, ρ m = ρ z := by
    intro z
    have hz : ρ z ∈ N₁.map ρ := by
      rw [hMtop]
      exact Subgroup.mem_top _
    exact Subgroup.mem_map.mp hz
  set W : Subgroup G := ρ.ker.map Y.subtype
  set Y₁ : Subgroup G := (K ⊔ pCoreOf 2 H) ⊓ Y
  have hWsolv : Group.IsSolvable ↥W := by
    have hkS : Group.IsSolvable ↥(ρ.ker) := by
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥(ρ.ker) := hρ2.isNilpotent
      infer_instance
    have e := ρ.ker.equivMapOfInjective Y.subtype Y.subtype_injective
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  have hYnorm : ∀ y ∈ Y, y ∈ Subgroup.normalizer (Y₁ : Set G) := by
    intro y hy
    exact Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨hXN (hYH hy), Subgroup.le_normalizer hy⟩)
  have hWN : W ≤ Subgroup.normalizer (Y₁ : Set G) := by
    rintro w hw
    obtain ⟨u, -, rfl⟩ := Subgroup.mem_map.mp hw
    exact hYnorm u.1 u.2
  have hYsub : Y ≤ W ⊔ Y₁ := by
    intro y hy
    obtain ⟨m, hm, hρm⟩ := hρN ⟨y, hy⟩
    have hw : (m⁻¹ * ⟨y, hy⟩ : ↥Y) ∈ ρ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hρm, inv_mul_cancel]
    have hmY₁ : (m : G) ∈ Y₁ := Subgroup.mem_inf.mpr ⟨Subgroup.mem_subgroupOf.mp hm, m.2⟩
    have hwW : ((m⁻¹ * ⟨y, hy⟩ : ↥Y) : G) ∈ W := Subgroup.mem_map_of_mem Y.subtype hw
    have hyeq : y = (m : G) * ((m⁻¹ * ⟨y, hy⟩ : ↥Y) : G) := by
      simp
    rw [hyeq]
    exact (W ⊔ Y₁).mul_mem ((le_sup_right : Y₁ ≤ W ⊔ Y₁) hmY₁)
      ((le_sup_left : W ≤ W ⊔ Y₁) hwW)
  have hY₁ : Y ≤ Y₁ := le_of_perfect_of_le_sup_coreA hYp hWN hWsolv hYsub
  have hYKA : Y ≤ K ⊔ pCoreOf 2 H := by
    intro y hy
    exact (Subgroup.mem_inf.mp (hY₁ hy)).1
  exact le_of_perfect_of_le_sup_coreA (K := Y) (W := pCoreOf 2 H) (N := K) hYp hAK hAsolv
    (hYKA.trans (le_of_eq (sup_comm _ _)))

end CFSG.Quasithin.H13.Ch4.CentK
