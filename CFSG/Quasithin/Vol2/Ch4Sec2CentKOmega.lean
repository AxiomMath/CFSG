module

public import CFSG.Quasithin.Vol2.Ch4Sec2CentKPar
public import CFSG.Quasithin.Vol2.KGFactSL3
public import CFSG.Quasithin.Vol2.Ch4Sec3L439Mod
public import CFSG.Quasithin.Background.C48PfA
public import CFSG.Quasithin.Background.C22HoldsA37

public section

namespace CFSG.Quasithin.H13.Ch4.CentK

open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open CFSG.Open hiding StatedSL
open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T M L Mm I H K : Subgroup G}

theorem omega_inf_centralizer_le (c : Conf4212 G T M L I H K) (h37 : A37ForSQTK)
    (hKH : H ≤ Subgroup.normalizer (K : Set G))
    (h2 : IsC134Case 2 (K ⊔ pCoreOf 2 I) (pCoreOf 2 I) K)
    (hline : ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (V₁ : Subgroup G),
      1 < m ∧ Fintype.card F = 2 ^ m ∧ IsStabilizedLineOfNatural F (pCoreOf 2 I) (H ⊓ M) K V₁) :
    omegaOneCenterOf (pCoreOf 2 I) ⊓ Subgroup.centralizer (perfectCore (L ⊓ H) : Set G) ≤
      Subgroup.centralizer (K : Set G) := by
  intro z hz
  obtain ⟨hzZ, hzL⟩ := hz
  obtain ⟨hzR, hzC, hz2⟩ := mem_quasithinOmegaOneCenter_iff.mp hzZ
  set R := pCoreOf 2 I
  set LH := perfectCore (L ⊓ H)
  have hRH : R ≤ H := (pCoreOf_le 2 I).trans c.inH.1
  have hRK : R ≤ Subgroup.normalizer (K : Set G) := hRH.trans hKH
  have hLHK : LH ≤ K := c.LH_le
  have hperf : ⁅K, K⁆ = K := perfect_of_mem_cComp c.K_mem
  have hzN : z ∈ Subgroup.normalizer (K : Set G) := hKH (hRH hzR)
  have hzO : ∀ a ∈ R, a * z = z * a := fun a ha => Subgroup.mem_centralizer_iff.mp hzC a ha
  have hOS : pCoreOf 2 K ≤ R :=
    (C48Pf.pCoreOf_le_pCoreOf_sup hRK).trans
      (C48Pf.pCoreOf_sup_le (asc22Three_of_a37 h37 G) c.hypC28 c.K_mem hRK)
  obtain ⟨m, F, _, _, _, hm1, hF, hstab⟩ := hline
  have hm : 2 ≤ m := by omega
  obtain ⟨W, α', _, W', hWle, hnat, hW', hY₀ne, hY₀perf, hstab₀, hPnorm⟩ :=
    exists_parabolicData' c hstab
  have hα' : Function.Surjective α' := hnat.2.1
  have hkerα' : α'.ker = CFSG.pCore 2 ↥K := hnat.2.2.1
  have hz22 : z * z = 1 := by rw [← pow_two]; exact hz2
  have hzK : ∀ k ∈ K, ⁅z, k⁆ ∈ pCoreOf 2 K :=
    commutator_mem_pCoreOf_of_involution sl3ParabolicAutFact_holds hm hF hα' hkerα' hW'
      hY₀ne hY₀perf hstab₀ hPnorm hzN hz22 fun l hl => by
        rw [commutatorElement_eq_one_iff_mul_comm.mpr
          (Subgroup.mem_centralizer_iff.mp hzL l hl).symm]
        exact Subgroup.one_mem _
  set Q := c134Q (K ⊔ R) K
  have hOO : pCoreOf 2 K ≤ pCoreOf 2 (K ⊔ R) :=
    le_pCoreOf_of_le_normalizer 2 ((pCoreOf_le 2 K).trans le_sup_left)
      ((_root_.sup_le (fun x hx => Subgroup.le_normalizer hx) hRK).trans
        (normalizer_le_normalizer_pCoreOf 2 K)) (pCoreOf_isPGroup 2 K)
  set Zz := Subgroup.zpowers z
  have hZzN : Zz ≤ Subgroup.normalizer (K : Set G) := Subgroup.zpowers_le.mpr hzN
  have hZzcs : Zz ≤ centralizerSection ⊤ K (pCoreOf 2 K) := by
    rw [Subgroup.zpowers_le]
    refine ⟨Subgroup.mem_top z, hzN, normalizer_le_normalizer_pCoreOf 2 K hzN, fun k hk => ?_⟩
    have h1 := (pCoreOf 2 K).inv_mem (hzK k hk)
    have e : (⁅z, k⁆)⁻¹ = k * z * k⁻¹ * z⁻¹ := by simp only [commutatorElement_def]; group
    rwa [e] at h1
  have hZzK : ⁅Zz, K⁆ ≤ pCoreOf 2 K := by
    rw [Subgroup.commutator_le]
    intro g hg k hk
    have h1 := (hZzcs hg).2.2.2 k hk
    have h2' := (pCoreOf 2 K).inv_mem h1
    have e : (k * g * k⁻¹ * g⁻¹)⁻¹ = ⁅g, k⁆ := by simp only [commutatorElement_def]; group
    rwa [e] at h2'
  have hZzKK : ⁅Zz, K⁆ = ⁅⁅Zz, K⁆, K⁆ :=
    commutator_eq_commutator_commutator_of_perfect' hperf hZzN
  have hZzQ : ⁅Zz, K⁆ ≤ Q := by
    rw [hZzKK]
    exact (Subgroup.commutator_mono hZzK le_rfl).trans (Subgroup.commutator_mono hOO le_rfl)
  set A := omegaOneCenterOf (pCoreOf 2 (K ⊔ R))
  have hAO : A ≤ pCoreOf 2 (K ⊔ R) := omegaOneCenterOf_le _
  have hAQ : ⁅A, K⁆ ≤ Q := Subgroup.commutator_mono hAO le_rfl
  have hfp' : ∀ v : Fin 3 → F, (∀ l : ↥K, (l : G) ∈ LH →
      ((α' l : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec v = v) → v = 0 := by
    intro v hv
    refine eq_zero_of_mulVec_eq_of_planeStab sl3ParabolicAutFact_holds hm hF W' hW' _ hY₀ne
      hY₀perf hstab₀ hPnorm v ?_
    rintro _ ⟨l, hl, rfl⟩
    exact hv l hl
  obtain ⟨⟨-, F₂, _, _, α, -, hαm, hN⟩, -⟩ := (h2 : IsC134Case2 _ _ _)
  have hcard : Fintype.card F = Fintype.card F₂ :=
    card_eq_of_card_statedSL_eq ((card_modO2_of_surjective α' hα' hkerα').symm.trans
      (card_modO2_of_surjective α hαm.1 hαm.2))
  obtain ⟨c₀, hc0, hc1, hcc⟩ := exists_good_scalar hm (hcard.symm.trans hF)
  have hxker : ∀ a : ↥K, α a = 1 → (a : G) * z = z * a := by
    intro a ha
    have h1 : a ∈ α.ker := ha
    rw [hαm.2] at h1
    exact hzO a (hOS ((mem_pCoreOf_iff' a).mpr h1))
  have hxK : ∀ g ∈ K, z⁻¹ * (g * z * g⁻¹) ∈ Q := by
    intro g hg
    apply hZzQ
    have h1 : ⁅z⁻¹, g⁆ ∈ ⁅Zz, K⁆ :=
      Subgroup.commutator_mem_commutator (Subgroup.inv_mem _ (Subgroup.mem_zpowers z)) hg
    have e : ⁅z⁻¹, g⁆ = z⁻¹ * (g * z * g⁻¹) := by
      simp only [commutatorElement_def, inv_inv]; group
    rwa [e] at h1
  obtain ⟨n₁, hn₁N, hzn⟩ := exists_mul_mem_centralizer_of_natural hc0 hc1 hcc hαm.1 hN hxker hxK
  have hn₁L : n₁ ∈ Subgroup.centralizer (LH : Set G) := by
    have h1 : z⁻¹ ∈ Subgroup.centralizer (LH : Set G) := Subgroup.inv_mem _ hzL
    have h2' : z * n₁ ∈ Subgroup.centralizer (LH : Set G) :=
      Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hLHK) hzn
    have h3 := Subgroup.mul_mem _ h1 h2'
    simpa using h3
  obtain ⟨hKN₀, hZ₀, β, hβ, hβker, hβeq⟩ := hN
  have hβinj : Function.Injective β := by
    rw [← MonoidHom.ker_eq_bot_iff, hβker, Subgroup.bot_subgroupOf]
  have hfix : ∀ (i : Fin 2) (l : ↥K), (l : G) ∈ LH →
      ((α l : GL (Fin 3) F₂) : Matrix (Fin 3) (Fin 3) F₂).mulVec
        (Multiplicative.toAdd (β ⟨n₁, hn₁N⟩) i) = Multiplicative.toAdd (β ⟨n₁, hn₁N⟩) i := by
    intro i l hl
    have h1 := hβeq l ⟨n₁, hn₁N⟩ ⟨n₁, hn₁N⟩ (by
      show n₁ = l * n₁ * (l : G)⁻¹
      rw [Subgroup.mem_centralizer_iff.mp hn₁L l hl]
      group) i
    simpa [moduleAct] using h1.symm
  have hn₁1 : n₁ = 1 := by
    have h1 : ∀ i : Fin 2, Multiplicative.toAdd (β ⟨n₁, hn₁N⟩) i = 0 := fun i =>
      eq_zero_of_fixed_of_natural_le hcard hnat ⟨hKN₀, hZ₀, β, hβ, hβker, hβeq⟩
        (hWle.trans hAQ) hfp' _ (hfix i)
    have hβ1 : β ⟨n₁, hn₁N⟩ = 1 := by
      apply Multiplicative.toAdd.injective
      funext i
      rw [h1 i]
      rfl
    have h3 := hβinj (hβ1.trans (map_one β).symm)
    exact congrArg Subtype.val h3
  rw [hn₁1, mul_one] at hzn
  exact hzn

end CFSG.Quasithin.H13.Ch4.CentK
