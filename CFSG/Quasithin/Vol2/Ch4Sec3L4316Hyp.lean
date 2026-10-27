module

public import CFSG.Quasithin.Vol2.Ch4Sec3L4316O2
public import CFSG.Quasithin.Vol2.Ch4Sec3L4316C1

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open hiding StatedSL StatedSp
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Assembly.LowTwoRank Vol2.KGNat
open scoped MatrixGroups Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Setting4315

variable {T M L : Subgroup G} {n : ℕ} {I H K : Subgroup G} {t : G} {m : ℕ} {F : Type} [Field F]
  [Fintype F] {α : ↥K →* ↥(StatedSL 3 F)} {β : ↥(u4311 I K) →* Multiplicative (Fin 3 → F)}
  {W' : Submodule F (Fin 3 → F)} {ZS K₂ R₂ : Subgroup G} {μ : Fˣ} {y : G} {KZ : Subgroup G}
variable (s : Setting4315 G T M L n I H K t m F α β W' ZS K₂ R₂ μ y KZ)
include s

theorem pCoreOf_star_K₂_le : pCoreOf 2 (s.star K₂) ≤ s.star R₂ := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := s.charP
  set f := s.starHom s.K₂_le_G₀ with hf
  have hfs := s.starHom_surjective s.K₂_le_G₀
  set P : Subgroup ↥K₂ := (CFSG.pCore 2 ↥(s.star K₂)).comap f with hP
  have hPn : P.Normal := (CFSG.pCore_normal : (CFSG.pCore 2 ↥(s.star K₂)).Normal).comap f
  have hN : (P.map s.levi).Normal := hPn.map _ s.levi_surjective
  have h2 : IsPGroup 2 ↥(P.map s.levi) := by
    rintro ⟨_, k, hk, rfl⟩
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥(s.star K₂))) ⟨f k, hk⟩
    refine ⟨a, Subtype.ext ?_⟩
    have h1 : f (k ^ 2 ^ a) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val ha
    have h3 : s.rho ⟨(k ^ 2 ^ a : ↥K₂), s.K₂_le_G₀ (k ^ 2 ^ a).2⟩ = 1 :=
      congrArg (fun w : ↥(s.star K₂) => ((w : ↥s.rho.range) : MulAut (ModO2 KZ))) h1
    have h4 := s.levi_eq_one_of_mem_C₀ (k ^ 2 ^ a).2 (s.mem_C₀_of_rho_eq_one _ h3)
    rw [SubgroupClass.coe_pow, ← map_pow]
    exact h4
  have hbot := eq_bot_of_normal_isPGroup_SL2 h2
  intro z hz
  obtain ⟨k, hk⟩ := hfs ⟨z, pCoreOf_le 2 _ hz⟩
  have hkP : k ∈ P := by
    rw [hP, Subgroup.mem_comap, hk]
    exact (mem_pCoreOf_iff' _).mp hz
  have hk1 : s.levi k = 1 := by
    have hmem : s.levi k ∈ P.map s.levi := ⟨k, hkP, rfl⟩
    rw [hbot, Subgroup.mem_bot] at hmem
    exact hmem
  have hkO : (k : G) ∈ pCoreOf 2 K₂ := by
    rw [mem_pCoreOf_iff', ← s.ker_levi]
    exact hk1
  exact ⟨⟨k, s.K₂_le_G₀ k.2⟩, s.pCoreOf_K₂_le_R₂ hkO, congrArg Subtype.val hk⟩

theorem rho_y_pow : s.rho.rangeRestrict ⟨y, s.y_mem_G₀⟩ ^ (2 ^ m - 1) = 1 := by
  rw [← map_pow]
  have : (⟨y, s.y_mem_G₀⟩ : ↥s.G₀) ^ (2 ^ m - 1) = 1 := by
    apply Subtype.ext
    rw [SubgroupClass.coe_pow, ← s.orderOf_y, pow_orderOf_eq_one]
    rfl
  rw [this, map_one]

theorem rho_y_mem_normalizer :
    s.rho.rangeRestrict ⟨y, s.y_mem_G₀⟩ ∈
      Subgroup.normalizer ((s.star R₂ : Subgroup ↥s.rho.range) : Set ↥s.rho.range) := by
  rw [s.mem_normalizer_star_iff]
  exact s.rho_mem_normalizer_map s.y_mem_G₀ (by simpa using s.zpow_y_mem_normalizer_R₂ 1)

theorem rho_y_comm_mem {k : ↥s.rho.range} (hk : k ∈ s.star K₂) :
    s.rho.rangeRestrict ⟨y, s.y_mem_G₀⟩ * k * (s.rho.rangeRestrict ⟨y, s.y_mem_G₀⟩)⁻¹ * k⁻¹ ∈
      pCoreOf 2 (s.star K₂) := by
  obtain ⟨g, hg, rfl⟩ := hk
  have e : s.rho.rangeRestrict ⟨y, s.y_mem_G₀⟩ * s.rho.rangeRestrict g *
      (s.rho.rangeRestrict ⟨y, s.y_mem_G₀⟩)⁻¹ * (s.rho.rangeRestrict g)⁻¹ =
      s.rho.rangeRestrict (⟨y, s.y_mem_G₀⟩ * g * (⟨y, s.y_mem_G₀⟩ : ↥s.G₀)⁻¹ * g⁻¹) := by
    simp only [map_mul, map_inv]
  rw [e]
  apply s.rangeRestrict_mem_pCoreOf
  simpa using s.commutator_Y_mem hg (Subgroup.mem_zpowers y)

theorem star_R₂_le (h135 : AsC135Three) (hR : L2RankOneSylowFact) (hC : LemmaC53C56Six)
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    s.star R₂ ≤ ⁅s.star R₂, Subgroup.zpowers (s.rho.rangeRestrict ⟨y, s.y_mem_G₀⟩)⁆ ⊔
      pCoreOf 2 (s.star K₂) := by
  set x := s.rho.rangeRestrict ⟨y, s.y_mem_G₀⟩ with hx
  have hQR := s.q4311_le_R₂ h135 hR hC h37 h38 h39
  have hYG : Subgroup.zpowers y ≤ s.G₀ := Subgroup.zpowers_le.mpr s.y_mem_G₀
  have hcomm : ⁅q4311 I K, Subgroup.zpowers y⁆ ≤
      ((⁅s.star R₂, Subgroup.zpowers x⁆).comap s.rho.rangeRestrict).map s.G₀.subtype := by
    rw [Subgroup.commutator_le]
    intro a ha b hb
    have haG : a ∈ s.G₀ := s.R₂_le_G₀ (hQR ha)
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hb
    have hbG : y ^ j ∈ s.G₀ := hYG hb
    refine ⟨⟨a, haG⟩ * ⟨y ^ j, hbG⟩ * (⟨a, haG⟩ : ↥s.G₀)⁻¹ * (⟨y ^ j, hbG⟩ : ↥s.G₀)⁻¹, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, map_mul, map_mul, map_mul, map_inv, map_inv]
    have hb' : s.rho.rangeRestrict ⟨y ^ j, hbG⟩ = x ^ j := by
      rw [hx, ← map_zpow]
      rfl
    rw [hb']
    have hmem : s.rho.rangeRestrict ⟨a, haG⟩ ∈ s.star R₂ := ⟨⟨a, haG⟩, hQR ha, rfl⟩
    have h1 := Subgroup.commutator_mem_commutator hmem (Subgroup.zpow_mem_zpowers x j)
    rwa [commutatorElement_def] at h1
  rintro _ ⟨⟨r, hrG⟩, hr, rfl⟩
  replace hr : r ∈ R₂ := hr
  obtain ⟨q, hq, k, hk, rfl⟩ := s.exists_mul_of_mem_R₂ h135 hR hC h37 h38 h39 hr
  have hqG : q ∈ s.G₀ := s.R₂_le_G₀ (hQR hq)
  have hkG : k ∈ s.G₀ := s.K₂_le_G₀ (pCoreOf_le 2 K₂ hk)
  have e : (⟨q * k, hrG⟩ : ↥s.G₀) = ⟨q, hqG⟩ * ⟨k, hkG⟩ := rfl
  rw [e, map_mul]
  refine Subgroup.mul_mem _ (Subgroup.mem_sup_left ?_)
    (Subgroup.mem_sup_right (s.rangeRestrict_mem_pCoreOf (h := ⟨k, hkG⟩) hk))
  have hq' : q ∈ ⁅q4311 I K, Subgroup.zpowers y⁆ := by
    rw [← s.q4311_eq_commutator]
    exact hq
  obtain ⟨g, hg, hgq⟩ := hcomm hq'
  have : g = ⟨q, hqG⟩ := Subtype.ext hgq
  rw [← this]
  exact hg

theorem insp (hI : Insp4316) (hF : A318Facts) (h135 : AsC135Three) (hR : L2RankOneSylowFact)
    (hC : LemmaC53C56Six) (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) :
    (m = 2 ∧ (IsPSL 3 2 2 ↥(s.star KZ) ∨ IsPSU 3 5 1 ↥(s.star KZ))) ∨
      (s.rho ⟨y, s.y_mem_G₀⟩ = 1 ∧
        (m = 2 → ¬ (IsElemAbelian 2 (s.star R₂) ∧ Nat.card ↥(s.star R₂) = 2 ^ 4 ∧
          ∀ R' : Subgroup ↥s.rho.range, R' ≤ s.star R₂ →
            s.star K₂ ≤ Subgroup.normalizer (R' : Set ↥s.rho.range) →
              R' = ⊥ ∨ R' = s.star R₂))) := by
  have hq := s.quasisimple h135 hR hC h36 h37 h38 h39
  have := s.star_KZ_normal
  rcases hI ↥s.rho.range (s.star KZ) s.star_KZ_normal (s.isSimpleGroup_star_KZ hq)
    (s.exists_not_comm_star_KZ hq) (s.a23List_star_KZ hF.list hq) (s.centralizer_star_KZ hq) m F
    s.two_le s.card_F (s.star R₂) (s.star K₂) (s.star_R₂_ne_bot h135 hR hC h36 h37 h38 h39)
    s.isPGroup_star_R₂ s.star_K₂_le s.star_K₂_perfect s.star_K₂_le_normalizer
    (s.normalizer_star_R₂_le h135 hR hC h37 h38 h39) s.exists_chi
    (s.prime_cond hF h135 hR hC h36 h37 h38 h39) s.pCoreOf_star_K₂_le
    (s.rho.rangeRestrict ⟨y, s.y_mem_G₀⟩) s.rho_y_pow s.rho_y_mem_normalizer
    (fun k hk => s.rho_y_comm_mem hk) (s.star_R₂_le h135 hR hC h37 h38 h39) with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨congrArg Subtype.val h1, h2⟩

end Setting4315

end CFSG.Quasithin.H13.Ch4
