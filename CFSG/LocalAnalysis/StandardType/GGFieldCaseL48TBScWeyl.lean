module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL48TBBridge
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerClassicalModel
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerLinearNonsplit

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

private theorem scWeyl_witness {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGSCWeylIrred p 0 R)
    {L' : Type} [Group L'] [Finite L'] (ψ : L' →* R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (h3 : p ^ 3 ≤ Nat.card A) (hsc : GGTorusSelfCent p A) :
    ∃ W : Set L',
      (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧
        ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
      (∀ A' : Subgroup (MulAut L'), A' ≤ A →
        (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') →
        A' = ⊥ ∨ A' = A) := by
  classical
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ : ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
    ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
      ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e, Λ e = a := by
    intro a ha
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    have hk : ∀ k : ℕ, ∀ l, (φ ^ k) (ψ l) = ψ ((a ^ k) l) := by
      intro k
      induction k with
      | zero => intro l; simp
      | succ k ih =>
        intro l
        rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ, ih]
    have hφp : φ ^ p = 1 := by
      refine MulEquiv.ext fun r => ?_
      obtain ⟨l, rfl⟩ := hψ r
      rw [hk, hA.2 a ha]
      rfl
    obtain ⟨e, rfl⟩ := hIp φ hφI hφp
    refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
    rw [hΛmap, ← hφ l, MulAut.conj_apply]
  set E : Subgroup R := A.comap Λ with hE
  have hΦbij : Function.Bijective (fun e : E => (⟨Λ e, e.2⟩ : A)) := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  have hcardE : Nat.card E = Nat.card A := Nat.card_congr (Equiv.ofBijective _ hΦbij)
  have hEab : IsElemAbelian p E := by
    refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
    · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
    · rw [map_pow, map_one]
      exact hA.2 _ he
  have hscE : ∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL hgp
    have hfix : ∀ a ∈ A, a n = n := by
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have heE : e ∈ E := show Λ e ∈ A from ha
      refine eq_of_lift_pow_eq_one hp hker hcpL ?_ ?_ hnp
      · rw [hΛmap, hn, ← hg e heE, mul_inv_cancel_right]
      · rw [← map_pow, hnp, map_one]
    have h1 := hsc n hfix hnp
    rw [← hΛn, hn] at h1
    exact h1
  have hirr : GGWeylIrred E :=
    h E hEab (by rw [hcardE, pow_zero]; exact le_trans (Nat.one_le_pow _ _ hp.pos) h3)
      (by rw [hcardE]; exact h3) hscE
  have hnorm_of : ∀ n : L', MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) →
      ψ n ∈ Subgroup.normalizer (E : Set R) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro e
    have h1 := hn (Λ e)
    rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
    exact h1
  have hnorm_to : ∀ n : L', ψ n ∈ Subgroup.normalizer (E : Set R) →
      MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    intro n hn
    rw [Subgroup.mem_normalizer_iff] at hn ⊢
    intro a
    constructor
    · intro ha
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have h1 := (hn e).mp ha
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul]
      exact h1
    · intro ha
      obtain ⟨e₁, he₁⟩ := hAΛ _ ha
      have he₁E : e₁ ∈ E := by
        show Λ e₁ ∈ A
        rw [he₁]
        exact ha
      have h2 : (ψ n)⁻¹ * e₁ * ψ n ∈ E := by
        refine (hn _).mpr ?_
        rw [show ψ n * ((ψ n)⁻¹ * e₁ * ψ n) * (ψ n)⁻¹ = e₁ by group]
        exact he₁E
      have h3' : a = Λ ((ψ n)⁻¹ * e₁ * ψ n) := by
        rw [map_mul, map_mul, map_inv, he₁, hΛn]
        group
      rw [h3']
      exact h2
  refine ⟨{n | MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))}, ?_, ?_⟩
  ·
    intro n hn a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have heE : e ∈ E := ha
    have hn' := hnorm_of n hn
    have he'E : ψ n * e * (ψ n)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hn' e).mp heE
    obtain ⟨x, hx, hxp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e) (hEab.2 e heE)
    have hlx : Λ e = MulAut.conj x := hΛeq hx
    have hy : ψ (n * x * n⁻¹) = ψ n * e * (ψ n)⁻¹ := by rw [map_mul, map_mul, map_inv, hx]
    have hyp : (n * x * n⁻¹) ^ p = 1 := by rw [conj_pow, hxp, mul_one, mul_inv_cancel]
    have hcomm : x * (n * x * n⁻¹) = (n * x * n⁻¹) * x :=
      commute_of_lift_pow_eq_one hp hker hcpL
        (by rw [hy, hx]; exact TableB.IsElemAbelian.comm hEab heE he'E) hyp
    have hform : n * (Λ e n)⁻¹ = (n * x * n⁻¹) * x⁻¹ := by
      rw [hlx, MulAut.conj_apply]
      group
    refine ⟨?_, fun a' ha' => ?_⟩
    · have hc : Commute (n * x * n⁻¹) x⁻¹ :=
        (show Commute x (n * x * n⁻¹) from hcomm).symm.inv_right
      rw [hform, hc.mul_pow, hyp, inv_pow, hxp, inv_one, mul_one]
    · obtain ⟨e'', rfl⟩ := hAΛ a' ha'
      have he''E : e'' ∈ E := ha'
      obtain ⟨z, hz, hzp⟩ := exists_lift_pow_eq_one hp hψ hker hcpL (g := e'')
        (hEab.2 e'' he''E)
      have hzx : z * x = x * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hx]; exact TableB.IsElemAbelian.comm hEab he''E heE) hxp
      have hzy : z * (n * x * n⁻¹) = (n * x * n⁻¹) * z :=
        commute_of_lift_pow_eq_one hp hker hcpL
          (by rw [hz, hy]; exact TableB.IsElemAbelian.comm hEab he''E he'E) hyp
      have hcy : Commute z (n * x * n⁻¹) := hzy
      have hcx : Commute z x⁻¹ := (show Commute z x from hzx).inv_right
      rw [hform, hΛeq hz, MulAut.conj_apply, (hcy.mul_right hcx).eq, mul_inv_cancel_right]
  ·
    intro A' hA'A hinv
    set E' : Subgroup R := A'.comap Λ with hE'
    have hE'E : E' ≤ E := fun e he => hA'A he
    have hinvE : ∀ g ∈ Subgroup.normalizer (E : Set R), ∀ e ∈ E', g * e * g⁻¹ ∈ E' := by
      intro g hg e he
      obtain ⟨n, rfl⟩ := hψ g
      have h1 := hinv n (hnorm_to n hg) (Λ e) he
      rw [← hΛn, ← map_inv, ← map_mul, ← map_mul] at h1
      exact h1
    rcases hirr E' hE'E hinvE with hbot | htop
    · left
      rw [eq_bot_iff]
      intro a ha
      obtain ⟨e, rfl⟩ := hAΛ a (hA'A ha)
      have he : e ∈ E' := ha
      rw [hbot, Subgroup.mem_bot] at he
      rw [he, map_one]
      exact Subgroup.one_mem _
    · right
      refine le_antisymm hA'A fun a ha => ?_
      obtain ⟨e, rfl⟩ := hAΛ a ha
      have he : e ∈ E' := by
        rw [htop]
        exact ha
      exact he

theorem ggIrredModTableB_of_scWeylIrred {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime) (hZ : Subgroup.center R = ⊥)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hcp : GGCenterPrime p R) (h : GGSCWeylIrred p 0 R) : GGIrredModTableB p R I := by
  intro M _ _ L' E θ hE hP S hDS hSE hSinv
  obtain ⟨W, hW1, hW2⟩ := scWeyl_witness hp hZ hIp hcp h (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hP.1 (TableBBridge.isElemAbelian_range_gamma hP)
    (TableBBridge.induces_range_gamma hP) (TableBBridge.pow_three_le_card_range hP hp)
    (TableBBridge.ggTorusSelfCent_range hP)
  exact TableBBridge.irred_of_witness hP hW1 hW2 S hDS hSE hSinv

private theorem center_eq_bot_of_mulEquiv' {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : Subgroup.center R' = ⊥) : Subgroup.center R = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have hx' : e x ∈ Subgroup.center R' := by
    rw [Subgroup.mem_center_iff] at hx ⊢
    intro g
    obtain ⟨y, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, hx y]
  rw [h, Subgroup.mem_bot] at hx'
  exact Subgroup.mem_bot.mpr (e.injective (hx'.trans (map_one e).symm))

private theorem ggIrredModTableB_linearNs {d p : ℕ} {K : Type} [Field K] [Finite K] [CharP K 2]
    (hp : p.Prime) (hp2 : p ≠ 2) (hpK : ¬ p ∣ Nat.card K - 1) (hd : 5 ≤ d) :
    GGIrredModTableB p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ) := by
  have hpK0 : (p : K) ≠ 0 := fun h =>
    hp2 (((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).mp
      ((CharP.cast_eq_zero_iff K 2 p).mp h)).symm)
  set e := TypeA.recipeEquiv d K with he
  refine ggIrredModTableB_of_scWeylIrred hp
    (center_eq_bot_of_mulEquiv' e (CFSG.RankThree.RegularUnipotent.center_projectiveSL_eq_bot
      (by omega)))
    (fun φ hφ hφp => NbrInnerMore.ggOutdiagPrime_linear hp hpK (by omega) φ hφ hφp)
    (ggCenterPrime_of_mulEquiv e (ggCenterPrime_projectiveSL hp hpK hd))
    (ggSCWeylIrred_of_mulEquiv e (ggSCWeylIrred_projectiveSL hp hpK0 hpK (by omega)))

private theorem largeEvenLabelAll_irredModTableB_linearNs' {p : ℕ} (hp : p.Prime)
    {lab : LargeEvenLabel} (hlab : LargeEvenInLambda2 lab) (h : GGTableBNbrInnerLinearNsLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB p R I := by
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨ht, hl, hp2, hq⟩ := h
  dsimp only at ht hl hp2 hq
  subst ht
  have hn : 1 ≤ n := hlab.1
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ'⟩ := hQ
  have : CharP K 2 := NbrInnerMore.charP_two_of_card_pow hn hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ',
    ggIrredModTableB_linearNs (d := l + 1) hp hp2 (by rwa [hK]) (by omega)⟩

theorem largeEvenLabelAll_irredModTableB_linearNs {p : ℕ} (hp : p.Prime) {lab : LargeEvenLabel}
    (hlab : LargeEvenInLambda2 lab) (h : GGTableBNbrInnerLinearNsLabel p lab) :
    LargeEvenLabelAll lab fun R _ I _ => GGIrredModTableB p R I ∨ GGWPlusTableB p R I :=
  (largeEvenLabelAll_irredModTableB_linearNs' hp hlab h).mono fun _ _ _ _ h => Or.inl h

end CFSG.StandardType

end
