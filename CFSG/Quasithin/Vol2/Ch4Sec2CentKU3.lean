module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKU1
public import CFSG.Quasithin.Vol2.Ch4Sec2CentKCoreA
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem coreN_cover_of_noncentral {F : Type} [Field F]
    (M : Subgroup (Matrix.SpecialLinearGroup (Fin 3) F)) [hM : M.Normal]
    {x : Matrix.SpecialLinearGroup (Fin 3) F} (hxM : x ∈ M)
    (hxc : x ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :
    ∀ g : Matrix.SpecialLinearGroup (Fin 3) F,
      ∃ m ∈ M, ∃ z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F), g = m * z := by
  have hsimp : IsSimpleGroup (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3 F) :=
    CFSG.RankThree.PartOne.KCLinearSubfield.isSimpleGroup_projectiveSL (n := 3) (K := F) le_rfl
  have hPn : (M.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)).Normal :=
    hM.map _ (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_surjective 3 F)
  rcases hsimp.eq_bot_or_eq_top_of_normal
    (M.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F)) with hbot | htop
  · exfalso
    have hmem : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F x ∈
        M.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) :=
      Subgroup.mem_map_of_mem _ hxM
    rw [hbot, Subgroup.mem_bot, CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_one_iff,
      CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center] at hmem
    exact hxc hmem
  · intro g
    have hg : CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F g ∈
        M.map (CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj 3 F) := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨m, hm, hmg⟩ := Subgroup.mem_map.mp hg
    have hz := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.proj_eq_proj_iff.mp hmg
    rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.scalars_eq_center] at hz
    exact ⟨m, hm, m⁻¹ * g, hz, (mul_inv_cancel_left m g).symm⟩

private theorem coreN_eq_top_of_perfect {X : Type*} [Group X] [Group.IsPerfect X]
    {M : Subgroup X} [hM : M.Normal]
    (hcov : ∀ g : X, ∃ m ∈ M, ∃ z ∈ Subgroup.center X, g = m * z) : M = ⊤ := by
  have hcomm : ⁅(⊤ : Subgroup X), ⊤⁆ ≤ M := by
    rw [Subgroup.commutator_le]
    intro g _ h _
    obtain ⟨m, hm, z, hz, rfl⟩ := hcov g
    have hzh : z * h * z⁻¹ = h := by
      rw [← Subgroup.mem_center_iff.mp hz h, mul_inv_cancel_right]
    have e : ⁅m * z, h⁆ = m * (h * m⁻¹ * h⁻¹) := by
      rw [commutatorElement_def]
      calc m * z * h * (m * z)⁻¹ * h⁻¹ = m * (z * h * z⁻¹) * m⁻¹ * h⁻¹ := by group
        _ = m * (h * m⁻¹ * h⁻¹) := by rw [hzh]; group
    rw [e]
    exact M.mul_mem hm (hM.conj_mem m⁻¹ (M.inv_mem hm) h)
  have h1 : ⁅(⊤ : Subgroup X), ⊤⁆ = ⊤ := Group.IsPerfect.commutator_eq_top (G := X)
  rw [h1] at hcomm
  exact eq_top_iff.mpr hcomm

theorem le_of_normal_of_noncentral {K N : Subgroup G} (hK : ⁅K, K⁆ = K) (hNK : N ≤ K)
    (hN : K ≤ Subgroup.normalizer (N : Set G)) {F : Type} [Field F] [Fintype F]
    {α : ↥K →* ↥(StatedSL 3 F)} (hα : Function.Surjective α) (hker : α.ker = CFSG.pCore 2 ↥K)
    (hnc : ∃ x, ∃ hx : x ∈ N, α ⟨x, hNK hx⟩ ∉ Subgroup.center ↥(StatedSL 3 F)) : K ≤ N := by
  let e : Matrix.SpecialLinearGroup (Fin 3) F ≃* ↥(StatedSL 3 F) :=
    CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 F
  let β : ↥K →* Matrix.SpecialLinearGroup (Fin 3) F := e.symm.toMonoidHom.comp α
  have hβs : Function.Surjective β := e.symm.surjective.comp hα
  have hβk : β.ker = CFSG.pCore 2 ↥K := by
    rw [← hker]
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    show e.symm (α x) = 1 ↔ α x = 1
    exact e.symm.map_eq_one_iff
  have hNn : (N.subgroupOf K).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mpr hN
  obtain ⟨x, hx, hxc⟩ := hnc
  have hmem : β ⟨x, hNK hx⟩ ∈ (N.subgroupOf K).map β :=
    ⟨⟨x, hNK hx⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
  have hncβ : β ⟨x, hNK hx⟩ ∉ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
    intro hc
    apply hxc
    have hαβ : α ⟨x, hNK hx⟩ = e (β ⟨x, hNK hx⟩) := (e.apply_symm_apply _).symm
    rw [Subgroup.mem_center_iff] at hc ⊢
    intro g
    obtain ⟨a, rfl⟩ := e.surjective g
    rw [hαβ, ← map_mul, ← map_mul, hc a]
  haveI : ((N.subgroupOf K).map β).Normal := hNn.map β hβs
  haveI : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (K := F) (n := 3) le_rfl
  have hcov := coreN_cover_of_noncentral ((N.subgroupOf K).map β) hmem hncβ
  have htop : (N.subgroupOf K).map β = ⊤ := coreN_eq_top_of_perfect hcov
  have hKWN : K ≤ pCoreOf 2 K ⊔ N := by
    intro k hk
    have hk' : β ⟨k, hk⟩ ∈ (N.subgroupOf K).map β := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨n', hn', hnk⟩ := Subgroup.mem_map.mp hk'
    have hu : (⟨k, hk⟩ : ↥K) * n'⁻¹ ∈ CFSG.pCore 2 ↥K := by
      rw [← hβk, MonoidHom.mem_ker, map_mul, map_inv, hnk, mul_inv_cancel]
    have hu' : (((⟨k, hk⟩ : ↥K) * n'⁻¹ : ↥K) : G) ∈ pCoreOf 2 K :=
      (mem_pCoreOf_iff' ((⟨k, hk⟩ : ↥K) * n'⁻¹)).mpr hu
    have hn'N : (n' : G) ∈ N := Subgroup.mem_subgroupOf.mp hn'
    have hkk : k = (((⟨k, hk⟩ : ↥K) * n'⁻¹ : ↥K) : G) * (n' : G) := by
      simp
    rw [hkk]
    exact Subgroup.mul_mem_sup hu' hn'N
  exact le_of_perfect_of_le_sup_coreA hK ((pCoreOf_le 2 K).trans hN)
    (isSolvable_pCoreOf_two K) hKWN

variable {T M L Mm I H K : Subgroup G} {n : ℕ}

theorem K_le_K₁ (s : Setting28 T M L Mm I H K n) {H₁ K₁ : Subgroup G} (hKH₁ : K ≤ H₁)
    (hH₁K₁ : H₁ ≤ Subgroup.normalizer (K₁ : Set G)) (hLK₁ : perfectCore (L ⊓ H) ≤ K₁) :
    K ≤ K₁ := by
  obtain ⟨⟨_, F₂, _, _, α, _, hαm, _⟩, -⟩ := (s.h2 : IsC134Case2 _ _ _)
  obtain ⟨hαs, hαker⟩ := hαm
  have hKperf : ⁅K, K⁆ = K := perfect_of_mem_cComp s.c.K_mem
  have hLHK : perfectCore (L ⊓ H) ≤ K := s.c.LH_le
  have hLHperf : ⁅perfectCore (L ⊓ H), perfectCore (L ⊓ H)⁆ = perfectCore (L ⊓ H) :=
    perfectCore_perfect _
  have hLHne : perfectCore (L ⊓ H) ≠ ⊥ := ne_bot_of_mem_cComp s.c.LH_mem
  have hLHKK₁ : perfectCore (L ⊓ H) ≤ K ⊓ K₁ := le_inf hLHK hLK₁
  have hnc : ∃ x, ∃ hx : x ∈ K ⊓ K₁,
      α ⟨x, (Subgroup.mem_inf.mp hx).1⟩ ∉ Subgroup.center ↥(StatedSL 3 F₂) := by
    by_contra hcon
    have hcon' : ∀ x (hx : x ∈ K ⊓ K₁),
        α ⟨x, (Subgroup.mem_inf.mp hx).1⟩ ∈ Subgroup.center ↥(StatedSL 3 F₂) := by
      intro x hx
      by_contra hx'
      exact hcon ⟨x, hx, hx'⟩
    have hYmap : ((perfectCore (L ⊓ H)).subgroupOf K).map K.subtype = perfectCore (L ⊓ H) := by
      rw [Subgroup.subgroupOf_map_subtype]
      exact inf_eq_left.mpr hLHK
    have hYperf : ⁅(perfectCore (L ⊓ H)).subgroupOf K, (perfectCore (L ⊓ H)).subgroupOf K⁆ =
        (perfectCore (L ⊓ H)).subgroupOf K := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, hYmap, hLHperf]
    have hZperf : ⁅((perfectCore (L ⊓ H)).subgroupOf K).map α,
        ((perfectCore (L ⊓ H)).subgroupOf K).map α⁆ =
        ((perfectCore (L ⊓ H)).subgroupOf K).map α := by
      rw [← Subgroup.map_commutator, hYperf]
    have hZcen : ∀ a ∈ ((perfectCore (L ⊓ H)).subgroupOf K).map α,
        a ∈ Subgroup.center ↥(StatedSL 3 F₂) := by
      rintro _ ⟨⟨x, hxK⟩, hxY, rfl⟩
      exact hcon' x (hLHKK₁ (Subgroup.mem_subgroupOf.mp hxY))
    have hZcomm : ⁅((perfectCore (L ⊓ H)).subgroupOf K).map α,
        ((perfectCore (L ⊓ H)).subgroupOf K).map α⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro a ha b _
      have hc : a * b = b * a := ((Subgroup.mem_center_iff.mp (hZcen a ha)) b).symm
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hc
    have hZbot : ((perfectCore (L ⊓ H)).subgroupOf K).map α = ⊥ := hZperf.symm.trans hZcomm
    have hLHle : perfectCore (L ⊓ H) ≤ pCoreOf 2 K := by
      intro l hl
      have hlK : l ∈ K := hLHK hl
      have hmem : α ⟨l, hlK⟩ ∈ ((perfectCore (L ⊓ H)).subgroupOf K).map α :=
        ⟨⟨l, hlK⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      rw [hZbot, Subgroup.mem_bot] at hmem
      have hker : (⟨l, hlK⟩ : ↥K) ∈ α.ker := MonoidHom.mem_ker.mpr hmem
      rw [hαker] at hker
      exact (mem_pCoreOf_iff' (⟨l, hlK⟩ : ↥K)).mpr hker
    apply hLHne
    exact eq_bot_of_perfect_of_isPGroup_two hLHperf ((pCoreOf_isPGroup 2 K).to_le hLHle)
  have hN' : K ≤ Subgroup.normalizer ((K ⊓ K₁ : Subgroup G) : Set G) := fun k hk =>
    Subgroup.inf_normalizer_le_normalizer_inf
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hk, hH₁K₁ (hKH₁ hk)⟩)
  exact (le_of_normal_of_noncentral (N := K ⊓ K₁) hKperf inf_le_left hN' hαs hαker hnc).trans
    inf_le_right

end CFSG.Quasithin.H13.Ch4.CentK
