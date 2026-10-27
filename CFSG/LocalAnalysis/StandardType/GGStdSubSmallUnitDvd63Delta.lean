module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvdDelta
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRule
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallUnitDvd63Model

public section

namespace CFSG.StandardType.SmallU

open scoped commutatorElement

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.SectionRank.OddCover CFSG.StandardType.LineU CFSG.StandardType.UnitTB CFSG.Assembly
  CFSG.RankThree.Classical CFSG.RankThree.Classical2 CFSG.StandardType.TableBUE

theorem ggDelta63_surj_of_cover {L' : Type} [Group L'] [Finite L'] {K : Type} [Field K] {n : ℕ}
    {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)} (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {φ : ↥(unitarySU 2 n K 6) →* L'}
    (hφ : ∀ s, ψ (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s) : Function.Surjective φ := by
  have hcomm : ⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ ≤ φ.range := by
    rw [Subgroup.commutator_le]
    intro x _ y _
    obtain ⟨s, hs⟩ : ∃ s : ↥(unitarySU 2 n K 6),
        ψ x = LargeEvenProjMk (unitarySU 2 n K 6) s := by
      obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ x)
      exact ⟨s0, hs0.symm⟩
    obtain ⟨s', hs'⟩ : ∃ s : ↥(unitarySU 2 n K 6),
        ψ y = LargeEvenProjMk (unitarySU 2 n K 6) s := by
      obtain ⟨s0, hs0⟩ := QuotientGroup.mk_surjective (ψ y)
      exact ⟨s0, hs0.symm⟩
    have hz : x * (φ s)⁻¹ ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs, mul_inv_cancel]
    have hz' : y * (φ s')⁻¹ ∈ Subgroup.center L' := by
      apply hker
      rw [MonoidHom.mem_ker, map_mul, map_inv, hφ, ← hs', mul_inv_cancel]
    have hx : x = (x * (φ s)⁻¹) * φ s := by group
    have hy : y = (y * (φ s')⁻¹) * φ s' := by group
    rw [hx, hy, comm_mul_central hz hz']
    exact ⟨⁅s, s'⁆, by rw [map_commutatorElement]⟩
  have htop : (⁅(⊤ : Subgroup L'), (⊤ : Subgroup L')⁆ : Subgroup L') = ⊤ := hperf
  rw [htop] at hcomm
  intro l
  obtain ⟨s, hs⟩ := hcomm (Subgroup.mem_top l)
  exact ⟨s, hs⟩

theorem ggDelta63_proj_eq_one_scalar {K : Type} [Field K] [Finite K] {n : ℕ}
    (g : ↥(unitarySU 2 n K 6)) (h : LargeEvenProjMk (unitarySU 2 n K 6) g = 1) :
    ∃ c : K, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal (fun _ => c) := by
  have h2 : g ∈ (LargeEvenScalars (Fin 6) K).subgroupOf (unitarySU 2 n K 6) :=
    (QuotientGroup.eq_one_iff g).mp h
  rw [Subgroup.mem_subgroupOf, largeEvenScalars_def] at h2
  obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp h2
  refine ⟨(c : K), ?_⟩
  rw [← hc]
  ext i j
  by_cases hij : i = j
  · subst hij
    simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
  · simp [Matrix.diagonal_apply, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, hij]

theorem ggDelta63_sup_elemAbelian {L' : Type} [Group L'] [Finite L'] {E₂ : Subgroup L'}
    (hE₂ : CFSG.Open.IsElemAbelian 3 E₂) {z : L'} (hz : z ∈ Subgroup.center L')
    (hzo : orderOf z = 3) (hdisj : E₂ ⊓ Subgroup.zpowers z = ⊥) :
    ∃ E : Subgroup L', CFSG.Open.IsElemAbelian 3 E ∧ Nat.card E₂ * 3 ≤ Nat.card E := by
  have hZcen : Subgroup.zpowers z ≤ Subgroup.center L' := Subgroup.zpowers_le.mpr hz
  have hcomm_z : ∀ w ∈ Subgroup.zpowers z, ∀ g : L', Commute w g := fun w hw g =>
    (Subgroup.mem_center_iff.mp (hZcen hw) g).symm
  haveI hZN : (Subgroup.zpowers z).Normal := ⟨fun w hw g => by
    have hc := Subgroup.mem_center_iff.mp (hZcen hw) g
    rw [hc, mul_inv_cancel_right]
    exact hw⟩
  have hmemE : ∀ x ∈ E₂ ⊔ Subgroup.zpowers z, ∃ y ∈ E₂, ∃ w ∈ Subgroup.zpowers z, y * w = x :=
    fun x hx => Subgroup.mem_sup_of_normal_right.mp hx
  have hEab : CFSG.Open.IsElemAbelian 3 (E₂ ⊔ Subgroup.zpowers z) := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun a ha => ?_⟩
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      obtain ⟨y₁, hy₁, w₁, hw₁, h₁⟩ := hmemE a a.2
      obtain ⟨y₂, hy₂, w₂, hw₂, h₂⟩ := hmemE b b.2
      rw [← h₁, ← h₂]
      have hyy : Commute y₁ y₂ := TableB.IsElemAbelian.comm hE₂ hy₁ hy₂
      have hcomm : Commute (y₁ * w₁) (y₂ * w₂) :=
        Commute.mul_left (Commute.mul_right hyy (hcomm_z w₂ hw₂ y₁).symm)
          (Commute.mul_right (hcomm_z w₁ hw₁ y₂) (hcomm_z w₁ hw₁ w₂))
      exact hcomm
    · obtain ⟨y, hy, w, hw, h⟩ := hmemE a ha
      rw [← h]
      have hc : Commute y w := (hcomm_z w hw y).symm
      have hw3 : w ^ 3 = 1 := by
        have h1 : orderOf w ∣ orderOf z := orderOf_dvd_of_mem_zpowers hw
        rw [hzo] at h1
        exact orderOf_dvd_iff_pow_eq_one.mp h1
      rw [hc.mul_pow, hE₂.2 y hy, hw3, one_mul]
  refine ⟨E₂ ⊔ Subgroup.zpowers z, hEab, ?_⟩
  have hf : Function.Injective (fun p : ↥E₂ × Fin 3 =>
      (⟨(p.1 : L') * z ^ (p.2 : ℕ), Subgroup.mul_mem_sup p.1.2
        (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _)⟩ : ↥(E₂ ⊔ Subgroup.zpowers z))) := by
    rintro ⟨y, k⟩ ⟨y', l⟩ hyk
    have hval : (y : L') * z ^ (k : ℕ) = (y' : L') * z ^ (l : ℕ) := congrArg Subtype.val hyk
    have hy : (y : L') = (y' : L') * z ^ (l : ℕ) * (z ^ (k : ℕ))⁻¹ := by
      rw [← hval]
      group
    have hw : (y' : L')⁻¹ * (y : L') = z ^ (l : ℕ) * (z ^ (k : ℕ))⁻¹ := by
      rw [hy]
      group
    have hmem : (y' : L')⁻¹ * (y : L') ∈ E₂ ⊓ Subgroup.zpowers z := by
      refine Subgroup.mem_inf.mpr ⟨E₂.mul_mem (E₂.inv_mem y'.2) y.2, ?_⟩
      rw [hw]
      exact Subgroup.mul_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers z) _))
    have hone : (y' : L')⁻¹ * (y : L') = 1 := by
      rw [← Subgroup.mem_bot, ← hdisj]
      exact hmem
    have hyy : (y : L') = (y' : L') := (inv_mul_eq_one.mp hone).symm
    have hzz : z ^ (l : ℕ) = z ^ (k : ℕ) := mul_inv_eq_one.mp (by rw [← hw]; exact hone)
    have hkl : (k : ℕ) = (l : ℕ) := by
      rw [pow_inj_mod, hzo] at hzz
      have hk3 := k.isLt
      have hl3 := l.isLt
      omega
    exact Prod.ext (Subtype.ext hyy) (Fin.ext hkl)
  have h1 := Nat.card_le_card_of_injective _ hf
  rw [Nat.card_prod, Nat.card_eq_fintype_card (α := Fin 3), Fintype.card_fin] at h1
  exact h1

theorem ggStdSubTwoTorusDeltaSmall_unitDvd63
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn2 : 2 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) :
    GGStdSubTwoTorusDeltaSmall 3 3 (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSUGroup (Fin 6) K (2 ^ n)))
        (LargeEvenGUSet (Fin 6) K (2 ^ n))) := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hδ a ha ha1 hEcomp hcentA hsmall
  exfalso
  have hn : 1 ≤ n := by omega
  have hp : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hne : ((6 : ℕ), n) ≠ (6, 1) := fun he => by
    have := congrArg Prod.snd he
    simp only at this
    omega
  obtain ⟨hperfSU, hcov⟩ := LineU.unitaryUniversalCover_holds n 6 K hK (by norm_num) hne
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hd3 : 3 ≤ 6 := by norm_num
  have hZR : Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))) = ⊥ :=
    center_proj_eq_bot hK hd3 hdq
  obtain ⟨φ₀, hφ₀⟩ := hcov L' ψ hψ hker hperf
  have hφ₀s : Function.Surjective φ₀ := ggDelta63_surj_of_cover hker hperf hφ₀
  have hφ₀ker : ∀ g : ↥(unitarySU 2 n K 6), φ₀ g = 1 →
      ∃ c : K, ((g : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) = diagonal (fun _ => c) := by
    intro g hg
    apply ggDelta63_proj_eq_one_scalar g
    rw [← hφ₀ g, hg]
    exact map_one ψ
  have hM₀ : UnitTB.Model φ₀ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφ₀s, hφ₀ker⟩
  obtain ⟨E₂, hE₂card, hE₂desc⟩ := exists_torus hM₀ hK hp hpq
    (S := Finset.univ.erase (0 : Fin 6)) (k₀ := (0 : Fin 6)) (by simp) id (fun k hk => hk)
  have hE₂card' : 3 ^ 4 ≤ Nat.card E₂ := by
    rw [Finset.image_id, Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ,
      Fintype.card_fin] at hE₂card
    exact hE₂card
  have hE₂ab : CFSG.Open.IsElemAbelian 3 E₂ := isElemAbelian_torus fun e he => by
    obtain ⟨g, τ, h1, h2, h3, -⟩ := hE₂desc e he
    exact ⟨g, τ, h1, h2, h3⟩
  have hA81 : 3 ^ 4 ≤ Nat.card A := by
    rcases hδ.2 with ⟨-, hbound⟩ | ⟨hdvd, hbound, -⟩
    · exact le_trans hE₂card' (hbound E₂ hE₂ab)
    ·
      obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥(Subgroup.center L')) 3 hdvd
      set z : L' := (x : L') with hzdef
      have hzc : z ∈ Subgroup.center L' := x.2
      have hzo : orderOf z = 3 := by
        rw [hzdef, Subgroup.orderOf_coe]
        exact hx
      have hψz : ψ z = 1 := by
        have hmem : ψ z ∈ Subgroup.center (LargeEvenProj (LargeEvenSUGroup (Fin 6) K (2 ^ n))) := by
          rw [Subgroup.mem_center_iff]
          intro r
          obtain ⟨l, rfl⟩ := hψ r
          rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hzc l]
        rw [hZR] at hmem
        exact Subgroup.mem_bot.mp hmem
      have hzker : z ∈ ψ.ker := MonoidHom.mem_ker.mpr hψz
      have hZsub : Subgroup.zpowers z ≤ ψ.ker := Subgroup.zpowers_le.mpr hzker
      have hE₂ker : ∀ y ∈ E₂, ψ y = 1 → y = 1 := by
        intro y hy hψy
        obtain ⟨g, τ, h1, h2, -, hτ, -⟩ := hE₂desc y hy
        have hpg : LargeEvenProjMk (unitarySU 2 n K 6) g = 1 := by
          rw [← hφ₀ g, h1]
          exact hψy
        obtain ⟨c, hc⟩ := ggDelta63_proj_eq_one_scalar g hpg
        have hmat : ((diagHom 6 τ : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K) =
            diagonal (fun _ => c) := by
          rw [← h2]
          exact hc
        have h00 : ((τ 0 : Kˣ) : K) = c := by
          have := congrFun (congrFun hmat 0) 0
          simpa [coe_diagHom] using this
        have hτ0 : τ 0 = 1 := hτ 0 (by simp)
        have hc1 : c = 1 := by
          rw [← h00, hτ0, Units.val_one]
        have hg1 : g = 1 := by
          apply Subtype.ext
          apply Units.ext
          rw [hc, hc1]
          ext i j
          simp [Matrix.diagonal_apply, Matrix.one_apply]
        rw [← h1, hg1, map_one]
      have hdisj : E₂ ⊓ Subgroup.zpowers z = ⊥ := by
        rw [eq_bot_iff]
        intro y hy
        rw [Subgroup.mem_inf] at hy
        rw [Subgroup.mem_bot]
        exact hE₂ker y hy.1 (MonoidHom.mem_ker.mp (hZsub hy.2))
      obtain ⟨E, hEab, hcard⟩ := ggDelta63_sup_elemAbelian hE₂ab hzc hzo hdisj
      have hbE := hbound E hEab
      have h2E : Nat.card E₂ ≤ Nat.card A := by omega
      exact le_trans hE₂card' h2E
  have hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s :=
    fun ψ'' hψ'' hk => hcov L' ψ'' hψ'' (fun x hx => hker (by rw [← hk]; exact hx)) hperf
  obtain ⟨φ, hφs, hφker, hdiag⟩ := Line63.exists_diagModel_of hK hn (by norm_num) hp hpq
    (by norm_num) hperfSU hψ hker hperf hA hAI (by simpa using hA81) hcov'
  have hM : Model φ := ⟨TableBU.unitaryFieldData_of_card hK hn, hφs, hφker⟩
  have hpK := dvd_card_sub_one hK hpq
  obtain ⟨t₀, ht₀⟩ := hdiag a ha
  obtain ⟨σ, -, hσ⟩ := ActsU.of_actsDiagU ht₀
  obtain ⟨i₀, hbig'⟩ := exists_bigOK_cls hM (by norm_num) hn hσ hEcomp
  have hS := cls_isCls σ i₀
  have hi₀S : i₀ ∈ cls σ i₀ := mem_cls.mpr rfl
  set S := cls σ i₀ with hSdef
  have hSd : ∃ k₀, k₀ ∉ S := by
    by_contra hall
    push Not at hall
    exact ha1 (hσ.eq_one_of_const hM i₀ fun i j => by
      rw [mem_cls.mp (hall i), mem_cls.mp (hall j)])
  obtain ⟨k₀, hk₀⟩ := hSd
  have hlayer : LargeEvenLayer (ggFix a) = (blockSU S).map φ :=
    layer_eq_block hM hσ hS (isQuasisimple_block hM hbig') hEcomp
  have hcardA := card_A_le_of_class (T := {i₀}) hM hd3 hp hpK hA hdiag ha hσ hS hbig' hEcomp
    hcentA (s₀ := i₀) (Finset.singleton_subset_iff.mpr hi₀S)
    (fun a' _ τ _ k hk => by rw [Finset.mem_singleton.mp hk])
  rw [Finset.card_singleton] at hcardA
  obtain ⟨E₃, hEcard, hEdesc⟩ := exists_torus hM hK hp hpq hk₀ id (fun k hk => hk)
  rw [Finset.image_id] at hEcard
  have hEab : CFSG.Open.IsElemAbelian 3 E₃ := isElemAbelian_torus fun e he => by
    obtain ⟨g, τ, h1, h2, h3, -⟩ := hEdesc e he
    exact ⟨g, τ, h1, h2, h3⟩
  have hElayer : E₃ ≤ LargeEvenLayer (ggFix a) := by
    rw [hlayer]
    exact torus_le_block fun e he => by
      obtain ⟨g, τ, h1, h2, -, h4, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2, h4⟩
  have hEfix : ∀ a' ∈ A, ∀ e ∈ E₃, a' e = e := by
    intro a' ha'
    obtain ⟨t', ht'⟩ := hdiag a' ha'
    obtain ⟨σ', -, hσ'⟩ := ActsU.of_actsDiagU ht'
    exact fix_of_torus hσ' fun e he => by
      obtain ⟨g, τ, h1, h2, -⟩ := hEdesc e he
      exact ⟨g, τ, h1, h2⟩
  have hEconj : ∀ e ∈ E₃, MulAut.conj e ∈ A := fun e he =>
    hδ.1 e (hEab.2 e he) (fun a' ha' => hEfix a' ha' e he)
  have hEsmall : Nat.card E₃ < 3 ^ 3 := hsmall E₃ hEab hElayer hEfix (Or.inl hEconj)
  have hSle : S.card ≤ 3 := by
    by_contra hc
    push Not at hc
    have h1 : 3 ^ 3 ≤ 3 ^ (S.card - 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  have h3S : 3 ^ (S.card - 1) ≤ 9 := by
    calc 3 ^ (S.card - 1) ≤ 3 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
      _ = 9 := by norm_num
  have h4 : 81 ≤ Nat.card A := by simpa using hA81
  omega

end CFSG.StandardType.SmallU

end
