module

public import CFSG.LocalAnalysis.WeakClosure81.Asc80BOddPSU
public import CFSG.LieType.SeitzGeneration.SpHyperGen
import CFSG.LieType.Chevalley.OrdinaryRootCentralizerGeneration
import CFSG.Models.Blueprint

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup CFSG.Open CFSG.RankThree.Classical CFSG.RankThree.PartOne.KCSpFull
  CFSG.RankThree.PartOne.CTP CFSG.Assembly.LowTwoRank CFSG.LieType.SeitzGeneration
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)

namespace SpSeitz

variable {r : ℕ} {K : Type} [Field K] {W : Submodule K (Fin r ⊕ Fin r → K)}

theorem eq_one_of_sq_eq_one_spRad {hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0}
    (h2K : (2 : K) ≠ 0) {g : StatedSp r K} (hg : g ∈ spRad W hW) (hg2 : g ^ 2 = 1) : g = 1 := by
  obtain ⟨hg1, hg2', hg3⟩ := hg
  set N : Module.End K (Fin r ⊕ Fin r → K) := spEnd g - 1 with hNdef
  have hNx : ∀ x, N x = spEnd g x - x := fun x => by simp [hNdef]
  have hN3 : N * N * N = 0 := by
    refine LinearMap.ext fun x => ?_
    have h1 : N x ∈ spPerp W := by rw [hNx]; exact hg1 x
    have h2 : N (N x) ∈ W := by rw [hNx]; exact hg2' _ h1
    have h3 : N (N (N x)) = 0 := by rw [hNx, hg3 _ h2, sub_self]
    simpa using h3
  have hg1' : spEnd g = 1 + N := by rw [hNdef]; abel
  have hpow := congrArg spEnd hg2
  rw [LieType.SeitzGeneration.spEnd_pow, spEnd_one, hg1',
    one_add_pow_of_cube_eq_zero (K := K) hN3 2, Nat.choose_self, Nat.cast_one, one_smul,
    Nat.cast_ofNat, add_assoc] at hpow
  have h0 : (2 : K) • N + N * N = 0 := add_eq_left.1 hpow
  have h3 : N * N = 0 := by
    have h := congrArg (fun X => N * X) h0
    simp only [mul_add, mul_zero, mul_smul_comm, ← mul_assoc, hN3, add_zero] at h
    exact (smul_eq_zero.1 h).resolve_left h2K
  have h4 : N = 0 := by
    rw [h3, add_zero] at h0
    exact (smul_eq_zero.1 h0).resolve_left h2K
  have h5 : spEnd g = 1 := by rw [hg1', h4, add_zero]
  apply spLin_injective
  rw [map_one]
  exact Units.ext h5

theorem not_two_dvd_card_spRad [Finite K] {hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0}
    (h2K : (2 : K) ≠ 0) : ¬ 2 ∣ Nat.card (spRad W hW) := by
  intro hdvd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 hdvd
  have h1 : (g : StatedSp r K) ^ 2 = 1 := by
    have := pow_orderOf_eq_one g
    rw [hg] at this
    exact congrArg Subtype.val this
  have h3 : g = 1 := Subtype.ext (eq_one_of_sq_eq_one_spRad h2K g.2 h1)
  rw [h3, orderOf_one] at hg
  exact absurd hg (by norm_num)

theorem spPerp_eq_orthogonal (X : Submodule K (Fin r ⊕ Fin r → K)) :
    spPerp X = (spForm r K).orthogonal X := rfl

theorem spForm_swap (x y : Fin r ⊕ Fin r → K) : spForm r K y x = -spForm r K x y := by
  rw [← spForm_isAlt.neg_eq]

theorem exists_sp_opposite [Finite K] (h2K : (2 : K) ≠ 0) {A : Subgroup (StatedSp r K)}
    (hA : (Nat.card A : K) ≠ 0) (hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0)
    (hWs : ∀ x ∈ A, ∀ w ∈ W, spEnd x w ∈ W) :
    ∃ W' : Submodule K (Fin r ⊕ Fin r → K), (∀ x ∈ W', ∀ y ∈ W', spForm r K x y = 0) ∧
      IsCompl (spPerp W) W' ∧ ∀ x ∈ A, ∀ w ∈ W', spEnd x w ∈ W' := by
  classical
  have hWP : ∀ w ∈ W, w ∈ spPerp W := fun w hw x hx => hW x hx w hw
  have hstab : ∀ {X : Submodule K (Fin r ⊕ Fin r → K)}, (∀ x ∈ A, ∀ w ∈ X, spEnd x w ∈ X) →
      ∀ x ∈ A, ∀ v ∈ spPerp X, spEnd x v ∈ spPerp X := fun hX x hx v hv =>
    spEnd_mem_spPerp (fun w hw => hX x⁻¹ (A.inv_mem hx) w hw) hv
  obtain ⟨C₀, hC₀, hC₀s⟩ := exists_stable_compl hA (hstab hWs)
  have hC₀P := hstab hC₀s
  have hnd := spForm_nondegenerate (r := r) (K := K)
  have hfin1 : Module.finrank K (spPerp W) = Module.finrank K (Fin r ⊕ Fin r → K) -
      Module.finrank K W := by
    rw [spPerp_eq_orthogonal]; exact LinearMap.BilinForm.finrank_orthogonal hnd W
  have hfin2 : Module.finrank K (spPerp C₀) = Module.finrank K (Fin r ⊕ Fin r → K) -
      Module.finrank K C₀ := by
    rw [spPerp_eq_orthogonal]; exact LinearMap.BilinForm.finrank_orthogonal hnd C₀
  have hfin3 : Module.finrank K (spPerp W) + Module.finrank K C₀ =
      Module.finrank K (Fin r ⊕ Fin r → K) := Submodule.finrank_add_eq_of_isCompl hC₀
  have hle1 : Module.finrank K W ≤ Module.finrank K (Fin r ⊕ Fin r → K) := Submodule.finrank_le W
  have hle2 : Module.finrank K C₀ ≤ Module.finrank K (Fin r ⊕ Fin r → K) := Submodule.finrank_le C₀
  have hdisj : Disjoint W (spPerp C₀) := by
    rw [Submodule.disjoint_def]
    intro w hw hwC
    refine hnd.1 w fun y => ?_
    have hy : y ∈ spPerp W ⊔ C₀ := by rw [hC₀.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
    rw [map_add, hu w hw, spForm_eq_zero_comm (hwC c hc), add_zero]
  have hWC : IsCompl W (spPerp C₀) := by
    refine (Submodule.isCompl_iff_disjoint W (spPerp C₀) ?_).2 hdisj
    omega
  set P : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K) := W.projection (spPerp C₀) hWC with hPdef
  have hP1 : ∀ v, P v ∈ W := fun v => Submodule.projection_apply_mem hWC v
  have hP2 : ∀ v, v - P v ∈ spPerp C₀ := fun v => Submodule.sub_projection_mem hWC v
  have hPW : ∀ w ∈ W, P w = w := fun w hw => Submodule.projection_apply_of_mem_left hWC hw
  have hPC : ∀ z ∈ spPerp C₀, P z = 0 := fun z hz =>
    Submodule.projection_apply_of_mem_right hWC hz
  have hPg : ∀ x ∈ A, ∀ v, P (spEnd x v) = spEnd x (P v) := by
    intro x hx v
    have hv : spEnd x v = spEnd x (P v) + spEnd x (v - P v) := by rw [← map_add]; congr 1; abel
    rw [hv, map_add, hPW _ (hWs x hx _ (hP1 v)), hPC _ (hC₀P x hx _ (hP2 v)), add_zero]
  have hcc : ∀ c₁ ∈ C₀, ∀ c₂ ∈ C₀, spForm r K c₁ (P c₂) = spForm r K c₁ c₂ := by
    intro c₁ hc₁ c₂ _
    have := hP2 c₂ c₁ hc₁
    rw [map_sub, sub_eq_zero] at this
    exact this.symm
  set κ : K := 2⁻¹ with hκ
  have hκ2 : κ + κ = 1 := by rw [hκ, ← two_mul, mul_inv_cancel₀ h2K]
  refine ⟨C₀.map (LinearMap.id - κ • P), ?_, ⟨?_, ?_⟩, ?_⟩
  · rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
    have e1 := hcc c₁ hc₁ c₂ hc₂
    have e2 : spForm r K (P c₁) c₂ = spForm r K c₁ c₂ := by
      rw [spForm_swap, hcc c₂ hc₂ c₁ hc₁, ← spForm_swap]
    have e3 := hW _ (hP1 c₁) _ (hP1 c₂)
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, map_sub, map_smul,
      LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul, e1, e2, e3]
    linear_combination (-(spForm r K c₁ c₂)) * hκ2
  · rw [disjoint_iff, Submodule.eq_bot_iff]
    rintro x ⟨hx, c, hc, rfl⟩
    have hcP : c ∈ spPerp W := by
      have h1 : c = (c - κ • P c) + κ • P c := by abel
      rw [h1]
      exact (spPerp W).add_mem (by simpa using hx) ((spPerp W).smul_mem _ (hWP _ (hP1 c)))
    have hc0 : c = 0 := Submodule.disjoint_def.1 hC₀.disjoint c hcP hc
    simp [hc0]
  · rw [codisjoint_iff, eq_top_iff]
    intro v _
    have hv : v ∈ spPerp W ⊔ C₀ := by rw [hC₀.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨u, hu, c, hc, rfl⟩ := Submodule.mem_sup.1 hv
    refine Submodule.mem_sup.2 ⟨u + κ • P c, ?_, c - κ • P c, ⟨c, hc, rfl⟩, by abel⟩
    exact (spPerp W).add_mem hu ((spPerp W).smul_mem _ (hWP _ (hP1 c)))
  · rintro x hx _ ⟨c, hc, rfl⟩
    refine ⟨spEnd x c, hC₀s x hx c hc, ?_⟩
    simp only [LinearMap.sub_apply, LinearMap.id_apply, LinearMap.smul_apply, map_sub, map_smul,
      hPg x hx]


theorem isPGroup_comap_proj [Finite K] (hr : 1 ≤ r) {E : Subgroup (StatedProj (StatedSp r K))}
    (hE : ∀ x ∈ E, x ^ 2 = 1) : IsPGroup 2 (E.comap (proj r K)) := by
  have hkc : Nat.card (proj r K).ker ∣ 2 := by
    rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.ker_proj,
      CFSG.LocalAnalysis.ComponentInitial.card_spScalars_eq_gcd K hr]
    exact Nat.gcd_dvd_left 2 _
  have : Finite (proj r K).ker := inferInstance
  intro g
  refine ⟨2, Subtype.ext ?_⟩
  have h1 : (g : StatedSp r K) ^ 2 ∈ (proj r K).ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hE _ g.2
  have h2 : (⟨_, h1⟩ : (proj r K).ker) ^ 2 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((_root_.orderOf_dvd_natCard _).trans hkc)
  have h3 := congrArg Subtype.val h2
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one] at h3
  simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
  rw [show 2 ^ 2 = 2 * 2 from rfl, pow_mul, h3]

theorem top_le_iSup_centralizer_of_isotropic [Finite K] (hr : 1 ≤ r) (h2K : (2 : K) ≠ 0)
    {E : Subgroup (StatedProj (StatedSp r K))} (hE : IsElemAbelian 2 E) (h4 : Nat.card E = 4)
    {W : Submodule K (Fin r ⊕ Fin r → K)} (hW0 : W ≠ ⊥)
    (hW : ∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0)
    (hstab : ∀ g : StatedSp r K, proj r K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) :
    (⊤ : Subgroup (StatedProj (StatedSp r K))) ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup _) ⊓ centralizer ({a} : Set _) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CFSG.IsElementaryAbelian 2 E := hE.isElementaryAbelian
  have hproj := CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective
    (r := r) (K := K)
  have : Finite (StatedProj (StatedSp r K)) := Finite.of_surjective (proj r K) hproj
  set Et : Subgroup (StatedSp r K) := E.comap (proj r K) with hEt
  have hEtcard : ((Nat.card Et : ℕ) : K) ≠ 0 := by
    obtain ⟨m, hm⟩ := (isPGroup_comap_proj hr hE.2).exists_card_eq
    rw [hm]
    push_cast
    exact pow_ne_zero m h2K
  have hWs : ∀ g ∈ Et, ∀ w ∈ W, spEnd g w ∈ W := fun g hg w hw => hstab g hg w hw
  obtain ⟨W', hW', hcompl, hW's⟩ := exists_sp_opposite h2K hEtcard hW hWs
  set M : Subgroup (StatedProj (StatedSp r K)) := ⨆ a ∈ E, ⨆ (_ : a ≠ 1),
    (⊤ : Subgroup _) ⊓ centralizer ({a} : Set _) with hM
  have hrad : ∀ {X : Submodule K (Fin r ⊕ Fin r → K)} (hX : ∀ x ∈ X, ∀ y ∈ X, spForm r K x y = 0),
      (∀ g ∈ Et, ∀ w ∈ X, spEnd g w ∈ X) → spRad X hX ≤ M.comap (proj r K) := by
    intro X hX hXs q hq
    have key : ∀ e ∈ E, ∀ v ∈ (spRad X hX).map (proj r K),
        e * v * e⁻¹ ∈ (spRad X hX).map (proj r K) := by
      intro e he v hv
      obtain ⟨a, rfl⟩ := hproj e
      obtain ⟨q', hq', rfl⟩ := hv
      have haEt : a ∈ Et := he
      exact ⟨a * q' * a⁻¹, spRad_conj_mem (fun w hw => hXs a haEt w hw)
        (fun w hw => hXs a⁻¹ (Et.inv_mem haEt) w hw) hq', by simp⟩
    have hnorm : E ≤ normalizer (((spRad X hX).map (proj r K) : Subgroup _) : Set _) := by
      intro e he
      rw [mem_normalizer_iff]
      intro h
      refine ⟨key e he h, fun hh => ?_⟩
      have := key e⁻¹ (E.inv_mem he) _ hh
      simpa [mul_assoc] using this
    have hQp : ¬ 2 ∣ Nat.card ((spRad X hX).map (proj r K)) := fun hd =>
      not_two_dvd_card_spRad h2K (hd.trans (card_map_dvd _ (proj r K)))
    exact CFSG.LieType.Chevalley.le_iSup_inf_centralizer_of_coprime (by omega) hQp hnorm le_top
      (mem_map_of_mem _ hq)
  have hC : ∀ c ∈ W', TransCenter (M.comap (proj r K)) c := fun c hc t =>
    hrad hW' hW's (spTransvection_mem_spRad hc t)
  have htop : M.comap (proj r K) = ⊤ := eq_top_of_spRad_of_centers hW0 hcompl (hrad hW hWs) hC
  intro k _
  obtain ⟨g, rfl⟩ := hproj k
  have hg : g ∈ M.comap (proj r K) := htop ▸ mem_top g
  exact hg

end SpSeitz

theorem top_le_iSup_centralizer_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (φ : X ≃* Y)
    {E : Subgroup X}
    (h : (⊤ : Subgroup Y) ≤ ⨆ a ∈ E.map φ.toMonoidHom, ⨆ (_ : a ≠ 1),
      (⊤ : Subgroup Y) ⊓ centralizer ({a} : Set Y)) :
    (⊤ : Subgroup X) ≤ ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup X) ⊓ centralizer ({a} : Set X) := by
  intro x _
  have hx := h (mem_top (φ x))
  have hle : (⨆ a ∈ E.map φ.toMonoidHom, ⨆ (_ : a ≠ 1),
      (⊤ : Subgroup Y) ⊓ centralizer ({a} : Set Y)) ≤
      (⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup X) ⊓ centralizer ({a} : Set X)).map
        φ.toMonoidHom := by
    refine iSup₂_le fun a ha => iSup_le fun ha1 => ?_
    obtain ⟨b, hb, rfl⟩ := ha
    have hb1 : b ≠ 1 := fun h => ha1 (by rw [h, map_one])
    intro z hz
    have hsub : (⊤ : Subgroup X) ⊓ centralizer ({b} : Set X) ≤
        ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup X) ⊓ centralizer ({a} : Set X) :=
      le_iSup₂_of_le b hb (le_iSup_of_le hb1 le_rfl)
    refine ⟨φ.symm z, hsub ⟨mem_top _, ?_⟩, by simp⟩
    show φ.symm z ∈ centralizer ({b} : Set X)
    rw [mem_centralizer_singleton_iff]
    have := mem_centralizer_singleton_iff.mp hz.2
    apply φ.injective
    simpa [map_mul] using this
  obtain ⟨w, hw, hwx⟩ := hle hx
  rw [show w = x from φ.injective hwx] at hw
  exact hw

@[expose] def SeitzFourSpAniso : Prop :=
  ∀ (K : Type) [Field K] [Finite K] (r : ℕ), 2 ≤ r → (2 : K) ≠ 0 → ¬ (r = 2 ∧ Nat.card K = 3) →
    ∀ E : Subgroup (StatedProj (StatedSp r K)), IsElemAbelian 2 E → Nat.card E = 4 →
    (∀ W : Submodule K (Fin r ⊕ Fin r → K), (∀ x ∈ W, ∀ y ∈ W, spForm r K x y = 0) →
      (∀ g : StatedSp r K, proj r K g ∈ E → ∀ w ∈ W, spEnd g w ∈ W) → W = ⊥) →
    (⊤ : Subgroup (StatedProj (StatedSp r K))) ≤
      ⨆ a ∈ E, ⨆ (_ : a ≠ 1), (⊤ : Subgroup _) ⊓ centralizer ({a} : Set _)

theorem seitzFourInner_psp_of_aniso (hA : SeitzFourSpAniso) :
    SeitzFourInner fun X _ => ∃ n p f : ℕ, 2 ≤ n ∧ p ≠ 2 ∧ CFSG.Models.LieModel X .PSp n p f := by
  intro G _ _ L E hLn hLs hnab ⟨n, p, f, hn, hp2, hm⟩ hC hE h4 hEL hexc
  classical
  have hm' : CFSG.Models.LieModel ↥L .PSp n p f := hm
  obtain ⟨⟨hp, hf, -⟩, K, _, _, hK, ⟨eS⟩⟩ :=
    CFSG.Models.LieModel.statedClassicalModel_of_ne_zero (by omega) hm'
  have h2K : (2 : K) ≠ 0 := by
    have : CharP K p := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
      hp hf hK
    intro h0
    have h2 : ((2 : ℕ) : K) = 0 := by exact_mod_cast h0
    have hdvd : p ∣ 2 := (CharP.cast_eq_zero_iff K p 2).1 h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hdvd)
  set E' : Subgroup ↥L := E.subgroupOf L with hE'
  have hE' : IsElemAbelian 2 E' := hE.subgroupOf L
  have h4' : Nat.card E' = 4 := by
    rw [← h4]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEL).toEquiv
  set E'' := E'.map eS.toMonoidHom with hE''
  have hE'' : IsElemAbelian 2 E'' :=
    CFSG.PreuniquenessRankFour.Helpers.elementary_abelian_map 2 hE' _
  have h4'' : Nat.card E'' = 4 := by
    rw [Subgroup.card_map_of_injective eS.injective, h4']
  apply iSup_centralizer_eq_of_subgroupOf
  apply top_le_iSup_centralizer_of_mulEquiv eS
  by_cases hiso : ∃ W : Submodule K (Fin n ⊕ Fin n → K), W ≠ ⊥ ∧
      (∀ x ∈ W, ∀ y ∈ W, spForm n K x y = 0) ∧
      ∀ g : StatedSp n K, proj n K g ∈ E'' → ∀ w ∈ W, spEnd g w ∈ W
  · obtain ⟨W, hW0, hW, hWs⟩ := hiso
    exact SpSeitz.top_le_iSup_centralizer_of_isotropic (by omega) h2K hE'' h4'' hW0 hW hWs
  · refine hA K n hn h2K ?_ E'' hE'' h4'' fun W hW hWs => ?_
    · rintro ⟨rfl, h3⟩
      apply hexc
      have hpf : p ^ f = 3 := hK.symm.trans h3
      have hp3 : p = 3 := by
        have : p ∣ 3 := by
          have := dvd_pow_self p (by omega : f ≠ 0)
          rwa [hpf] at this
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 this
      have hf1 : f = 1 := by
        subst hp3
        have h31 : 3 ^ f = 3 ^ 1 := by rw [pow_one]; exact hpf
        exact Nat.pow_right_injective (by norm_num) h31
      subst hp3; subst hf1
      exact Or.inr (Or.inr (Or.inr hm'))
    · by_contra hne
      exact hiso ⟨W, hne, hW, hWs⟩

end CFSG.LocalAnalysis.WeakClosure81
