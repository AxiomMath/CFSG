module

public import CFSG.LocalAnalysis.StandardType.GGTorusReflFixDefs

import CFSG.LocalAnalysis.StandardType.GGKGReflection

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem GGKGReflFix.of_mulEquiv {p s : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGKGReflFix p s R) : GGKGReflFix p s R' := by
  classical
  intro E H hEab hsc Hle hcard hV
  let f : R' →* R := e.symm.toMonoidHom
  let E' : Subgroup R := E.map f
  let H' : Subgroup R := H.map f
  have hfinj : Function.Injective f := e.symm.injective
  have hEab' : IsElemAbelian p E' := hEab.map f
  have hsc' : ∀ g : R, (∀ x ∈ E', g * x = x * g) → g ^ p = 1 → g ∈ E' := by
    intro g hg hgp
    have hge : e g ∈ E := by
      refine hsc (e g) (fun y hy => ?_) ?_
      · have hy' : e.symm y ∈ E' := Subgroup.mem_map.mpr ⟨y, hy, by simp [f]⟩
        simpa [f] using congrArg e (hg (e.symm y) hy')
      · simpa using congrArg e hgp
    exact Subgroup.mem_map.mpr ⟨e g, hge, by simp [f]⟩
  have hH'E' : H' ≤ E' := Subgroup.map_mono (f := f) Hle
  have hcard' : p ^ s ≤ Nat.card H' := by
    rw [Subgroup.card_map_of_injective hfinj]
    exact hcard
  obtain ⟨V, hVne, hV2, hVinv⟩ := hV
  let V' : Subgroup R := V.map f
  have hV'E : V'.map e.toMonoidHom = V := by
    dsimp only [V', f]
    rw [Subgroup.map_map]
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id R' := by
      ext x
      simp
    rw [hid, Subgroup.map_id]
  have hV'ne : V' ≠ ⊥ := by
    intro hbot
    apply hVne
    rw [← hV'E, hbot, Subgroup.map_bot]
  have hV'2 : IsPGroup 2 V' := hV2.map f
  have hV'norm : ∀ x ∈ H', ∀ u ∈ V', x * u * x⁻¹ ∈ V' := by
    intro x hx u hu
    obtain ⟨a, haH, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨b, hbV, rfl⟩ := Subgroup.mem_map.mp hu
    exact Subgroup.mem_map.mpr ⟨a * b * a⁻¹, hVinv a haH b hbV, by simp only [map_mul, map_inv]⟩
  obtain ⟨w', hwrefl, hwcomm⟩ :=
    h E' H' hEab' hsc' hH'E' hcard' ⟨V', hV'ne, hV'2, hV'norm⟩
  have hE'E : E'.map e.toMonoidHom = E := by
    dsimp only [E', f]
    rw [Subgroup.map_map]
    have hid : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id R' := by
      ext x
      simp
    rw [hid, Subgroup.map_id]
  refine ⟨e w', ?_, fun hx hxH => ?_⟩
  · rw [← hE'E]
    exact GGKGIsReflAt.map e.toMonoidHom e.injective hwrefl
  · have hxH' : f hx ∈ H' := Subgroup.mem_map_of_mem f hxH
    have hcomm := congrArg e (hwcomm (f hx) hxH')
    simpa [f] using hcomm

private theorem exists_liftConj {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hZ : Subgroup.center R = ⊥) :
    ∃ Λ : R →* MulAut L',
      (∀ {e : R} {x : L'}, ψ x = e → Λ e = MulAut.conj x) ∧ Function.Injective Λ ∧
      (∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :=
  ⟨ReflInner.liftConj ψ hψ hker, fun hx => ReflInner.liftConj_eq hψ hker hx,
    ReflInner.liftConj_injective hψ hker hZ, ReflInner.map_liftConj_apply hψ hker⟩

private theorem exists_liftConj_eq_of_mem {p : ℕ} {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} {I : Set (MulAut R)}
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l))
    (Λ : R →* MulAut L') (hΛ : ∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) :
    ∀ a ∈ A, ∃ e : R, Λ e = a := by
  intro a ha
  obtain ⟨φ', hφ'I, hφ'⟩ := hAI a ha
  have hk : ∀ k : ℕ, ∀ l, (φ' ^ k) (ψ l) = ψ ((a ^ k) l) := by
    intro k
    induction k with
    | zero => intro l; simp
    | succ k ih =>
      intro l
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, hφ', ih]
  have hφp : φ' ^ p = 1 := by
    refine MulEquiv.ext fun r => ?_
    obtain ⟨l, rfl⟩ := hψ r
    rw [hk, hA.2 a ha]
    rfl
  obtain ⟨e, rfl⟩ := hIp φ' hφ'I hφp
  refine ⟨e, TypeA.mulAut_eq_of_forall ψ hker hperf fun l => ?_⟩
  rw [hΛ, ← hφ' l, MulAut.conj_apply]

private theorem isElemAbelian_comap_liftConj {p : ℕ} {L' R : Type} [Group L'] [Group R]
    {Λ : R →* MulAut L'} {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A)
    (hΛinj : Function.Injective Λ) : IsElemAbelian p (A.comap Λ) := by
  refine ⟨⟨⟨fun e₁ e₂ => Subtype.ext (hΛinj ?_)⟩⟩, fun e he => hΛinj ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact TableB.IsElemAbelian.comm hA e₁.2 e₂.2
  · rw [map_pow, map_one]
    exact hA.2 _ he

private theorem mem_comap_liftConj_of_centralizer {p : ℕ} {L' R : Type} [Group L'] [Group R]
    [Finite L'] {ψ : L' →* R} (hp : p.Prime) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hcp : ¬ p ∣ Nat.card (Subgroup.center L'))
    {A : Subgroup (MulAut L')} (hsc : GGTorusSelfCent p A) {Λ : R →* MulAut L'}
    (hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n)
    (hΛ : ∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹) (hAΛ : ∀ a ∈ A, ∃ e : R, Λ e = a) :
    ∀ g : R, (∀ e ∈ A.comap Λ, g * e = e * g) → g ^ p = 1 → g ∈ A.comap Λ := by
  intro g hg hgp
  obtain ⟨n, hn, hnp⟩ := exists_lift_pow_eq_one hp hψ hker hcp hgp
  have hfix : ∀ a ∈ A, a n = n := by
    intro a ha
    obtain ⟨e, rfl⟩ := hAΛ a ha
    have he : e ∈ A.comap Λ := show Λ e ∈ A from ha
    refine eq_of_lift_pow_eq_one hp hker hcp ?_ ?_ hnp
    · rw [hΛ, hn, ← hg e he, mul_inv_cancel_right]
    · rw [← map_pow, hnp, map_one]
  have h1 := hsc n hfix hnp
  rw [← hΛn n, hn] at h1
  exact h1

private theorem card_comap_of_le_range {L' R : Type} [Group L'] [Group R] {Λ : R →* MulAut L'}
    {H : Subgroup (MulAut L')} (hΛinj : Function.Injective Λ) (hH : H ≤ Λ.range) :
    Nat.card (H.comap Λ) = Nat.card H := by
  have hmap : (H.comap Λ).map Λ = H := Subgroup.map_comap_eq_self hH
  calc Nat.card (H.comap Λ) = Nat.card ((H.comap Λ).map Λ) :=
        (Subgroup.card_map_of_injective hΛinj).symm
    _ = Nat.card H := by rw [hmap]

private theorem comap_normalizes_of_liftConj {L' R : Type} [Group L'] [Group R]
    {ψ : L' →* R} {H : Subgroup (MulAut L')} {V : Subgroup R} {Λ : R →* MulAut L'}
    (hψ : Function.Surjective ψ) (hΛ : ∀ e l, ψ (Λ e l) = e * ψ l * e⁻¹)
    (hV : ∀ h ∈ H, ∀ l : L', ψ l ∈ V → ψ (h l) ∈ V) :
    ∀ h₀ ∈ H.comap Λ, ∀ u ∈ V, h₀ * u * h₀⁻¹ ∈ V := by
  intro h₀ hh₀ u hu
  obtain ⟨l, rfl⟩ := hψ u
  have hthis : ψ (Λ h₀ l) ∈ V := hV (Λ h₀) hh₀ l hu
  rwa [hΛ h₀ l] at hthis

private theorem conj_mul_liftConj_mul_inv {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}
    {Λ : R →* MulAut L'} {n : L'} {w : R} (hn : ψ n = w)
    (hΛn : Λ (ψ n) = MulAut.conj n) (e : R) :
    MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ = Λ (w * e * w⁻¹) := by
  rw [← hΛn, hn, map_mul, map_mul, map_inv]

private theorem conj_mem_normalizer_of_lift {L' R : Type} [Group L'] [Group R] [Finite L']
    {Λ : R →* MulAut L'} {A : Subgroup (MulAut L')} {n : L'} {w : R}
    (hAΛ : ∀ a ∈ A, ∃ e : R, Λ e = a)
    (hnorm : w ∈ Subgroup.normalizer (A.comap Λ : Set R))
    (hconj : ∀ e : R, MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ = Λ (w * e * w⁻¹)) :
    MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
  have hWinv : (MulAut.conj n)⁻¹ ∈ Subgroup.normalizer (A : Set (MulAut L')) := by
    refine mem_normalizer_of_forall_conj_mem fun a ha => ?_
    obtain ⟨e, hΛe⟩ := hAΛ a ha
    have he : e ∈ A.comap Λ := by
      rw [Subgroup.mem_comap, hΛe]
      exact ha
    have hwe : w * e * w⁻¹ ∈ A.comap Λ :=
      (Subgroup.mem_normalizer_iff.mp hnorm e).mp he
    have h1 : MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ ∈ A := by
      rw [hconj e]
      exact hwe
    simpa only [inv_inv, hΛe] using h1
  simpa using Subgroup.inv_mem _ hWinv

private theorem exists_equiv_comap_of_mem {L' R : Type} [Group L'] [Group R]
    {Λ : R →* MulAut L'} {A : Subgroup (MulAut L')}
    (hΛinj : Function.Injective Λ) (hAΛ : ∀ a ∈ A, ∃ e : R, Λ e = a) :
    ∃ Φ : A.comap Λ ≃ A, ∀ e, (Φ e : MulAut L') = Λ (e : R) := by
  have hmem : ∀ e : A.comap Λ, Λ (e : R) ∈ A := fun e => e.2
  let Φfun : A.comap Λ → A := fun e => (⟨Λ (e : R), hmem e⟩ : A)
  have hbij : Function.Bijective Φfun := by
    refine ⟨fun e₁ e₂ h12 => Subtype.ext (hΛinj (congrArg Subtype.val h12)), fun a => ?_⟩
    obtain ⟨e, he⟩ := hAΛ a a.2
    exact ⟨⟨e, show Λ e ∈ A from he ▸ a.2⟩, Subtype.ext he⟩
  exact ⟨Equiv.ofBijective Φfun hbij, fun e => rfl⟩

private theorem ggConjAut_mem_automizer {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {n : L'} (hW : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ggConjAut A hW ∈ ggAutomizer (MulAut.conj : L' →* MulAut L').range A :=
  Subgroup.subset_closure
    (ggConjAut_mem_ggInduced (H := (MulAut.conj : L' →* MulAut L').range) (Bs := A)
      (g := MulAut.conj n) (MonoidHom.mem_range.mpr ⟨n, rfl⟩) hW)

private theorem ggConjAut_comm_comap_equiv {L' R : Type} [Group L'] [Group R]
    {Λ : R →* MulAut L'} {A : Subgroup (MulAut L')} {n : L'} {w : R}
    (hnorm : w ∈ Subgroup.normalizer (A.comap Λ : Set R))
    (hW : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (Φ : A.comap Λ ≃ A) (hΦ : ∀ e, (Φ e : MulAut L') = Λ (e : R))
    (hconj : ∀ e : R, MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ = Λ (w * e * w⁻¹))
    (e : A.comap Λ) :
    ggConjAut A hW (Φ e) = Φ (ggConjAut (A.comap Λ) hnorm e) := by
  refine Subtype.ext ?_
  rw [ggConjAut_apply, hΦ, hΦ, ggConjAut_apply]
  exact hconj (e : R)

private theorem ggConjAut_isReflection {p : ℕ} {L' R : Type} [Group L'] [Group R]
    {Λ : R →* MulAut L'} {A : Subgroup (MulAut L')} {n : L'} {w : R}
    (hW : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
    (hnorm : w ∈ Subgroup.normalizer (A.comap Λ : Set R))
    (Φ : A.comap Λ ≃ A)
    (hΦcomm : ∀ e : A.comap Λ,
      ggConjAut A hW (Φ e) = Φ (ggConjAut (A.comap Λ) hnorm e))
    (hinv : ∀ e ∈ A.comap Λ, w * (w * e * w⁻¹) * w⁻¹ = e)
    (hfix : Nat.card {e : A.comap Λ // w * (e : R) * w⁻¹ = e} * p =
      Nat.card (A.comap Λ)) :
    GGIsReflection p (ggConjAut A hW) := by
  have hsq : ggConjAut A hW ^ 2 = 1 := by
    refine MulEquiv.ext fun a => ?_
    obtain ⟨e, rfl⟩ := Φ.surjective a
    rw [pow_two, MulAut.mul_apply, hΦcomm e, hΦcomm (ggConjAut (A.comap Λ) hnorm e)]
    have h2 : ggConjAut (A.comap Λ) hnorm (ggConjAut (A.comap Λ) hnorm e) = e := by
      apply Subtype.ext
      rw [ggConjAut_apply, ggConjAut_apply]
      exact hinv (e : R) e.2
    rw [h2]
    rfl
  refine ⟨hsq, ?_⟩
  have hcardfix : Nat.card {a : A // ggConjAut A hW a = a} =
      Nat.card {e : A.comap Λ // ggConjAut (A.comap Λ) hnorm e = e} := by
    refine (Nat.card_congr (Equiv.subtypeEquiv Φ fun e => ?_)).symm
    rw [hΦcomm e]
    exact ⟨fun h => by rw [h], fun h => Φ.injective h⟩
  rw [hcardfix]
  have hfixeq : Nat.card {e : A.comap Λ // ggConjAut (A.comap Λ) hnorm e = e} =
      Nat.card {e : A.comap Λ // w * (e : R) * w⁻¹ = e} :=
    Nat.card_congr (Equiv.subtypeEquivRight fun e => Subtype.ext_iff)
  rw [hfixeq, hfix, Nat.card_congr Φ]

private theorem ggConjAut_fixes_of_mem_comap {L' R : Type} [Group L'] [Group R]
    {Λ : R →* MulAut L'} {A H : Subgroup (MulAut L')} {n : L'} {w : R}
    (hAΛ : ∀ a ∈ A, ∃ e : R, Λ e = a)
    (hconj : ∀ e : R, MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ = Λ (w * e * w⁻¹))
    (hwH : ∀ e ∈ H.comap Λ, w * e = e * w)
    (hW : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L')))
    {h : MulAut L'} (ha : h ∈ A) (hh : h ∈ H) :
    ggConjAut A hW ⟨h, ha⟩ = ⟨h, ha⟩ := by
  obtain ⟨e, hΛe⟩ := hAΛ h ha
  have heH : e ∈ H.comap Λ := Subgroup.mem_comap.mpr (hΛe ▸ hh)
  have hwe : w * e * w⁻¹ = e := by
    rw [hwH e heH]
    group
  refine Subtype.ext ?_
  rw [ggConjAut_apply]
  calc MulAut.conj n * h * (MulAut.conj n)⁻¹
      = MulAut.conj n * Λ e * (MulAut.conj n)⁻¹ := by rw [hΛe]
    _ = Λ (w * e * w⁻¹) := hconj e
    _ = Λ e := by rw [hwe]
    _ = h := hΛe

theorem ggTorusReflFix_of_kgReflFix {p r s : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hp : p.Prime)
    (hIp : ∀ φ ∈ I, φ ^ p = 1 → φ ∈ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (hcp : GGCenterPrime p R) (h : GGKGReflFix p s R) :
    GGTorusReflFix p r s R I := by
  classical
  intro L' _ _ ψ A hTB H hHA hHcard hV
  obtain ⟨hψ, hker, hperf, hA, hAI, -, -, hsc⟩ := hTB
  have hcpL := hcp L' ψ hψ hker hperf
  obtain ⟨Λ, hΛeq, hΛinj, hΛmap⟩ := exists_liftConj hψ hker hZ
  have hΛn : ∀ n : L', Λ (ψ n) = MulAut.conj n := fun n => hΛeq rfl
  have hAΛ : ∀ a ∈ A, ∃ e : R, Λ e = a :=
    exists_liftConj_eq_of_mem hIp hψ hker hperf hA hAI Λ hΛmap
  have hEab : IsElemAbelian p (A.comap Λ) := isElemAbelian_comap_liftConj hA hΛinj
  have hscE : ∀ g : R, (∀ e ∈ A.comap Λ, g * e = e * g) → g ^ p = 1 → g ∈ A.comap Λ :=
    mem_comap_liftConj_of_centralizer hp hψ hker hcpL hsc hΛn hΛmap hAΛ
  have hHcardE : Nat.card (H.comap Λ) = Nat.card H :=
    card_comap_of_le_range hΛinj fun h hh => hAΛ h (hHA hh)
  have hH₀s : p ^ s ≤ Nat.card (H.comap Λ) := hHcardE ▸ hHcard
  obtain ⟨V, hVne, hV2, hVinv⟩ := hV
  have hVnorm : ∀ h₀ ∈ H.comap Λ, ∀ u ∈ V, h₀ * u * h₀⁻¹ ∈ V :=
    comap_normalizes_of_liftConj hψ hΛmap hVinv
  obtain ⟨w, hwrefl, hwH⟩ :=
    h (A.comap Λ) (H.comap Λ) hEab hscE (Subgroup.comap_mono hHA) hH₀s
      ⟨V, hVne, hV2, hVnorm⟩
  obtain ⟨hnorm, hinv, hfix⟩ := hwrefl
  obtain ⟨ñ, hñ⟩ := hψ w
  have hconj : ∀ e : R, MulAut.conj ñ * Λ e * (MulAut.conj ñ)⁻¹ = Λ (w * e * w⁻¹) :=
    conj_mul_liftConj_mul_inv hñ (hΛn ñ)
  have hW : MulAut.conj ñ ∈ Subgroup.normalizer (A : Set (MulAut L')) :=
    conj_mem_normalizer_of_lift hAΛ hnorm hconj
  obtain ⟨Φ, hΦ⟩ := exists_equiv_comap_of_mem hΛinj hAΛ
  have hΦcomm : ∀ e : A.comap Λ,
      ggConjAut A hW (Φ e) = Φ (ggConjAut (A.comap Λ) hnorm e) :=
    ggConjAut_comm_comap_equiv hnorm hW Φ hΦ hconj
  refine ⟨ggConjAut A hW, ggConjAut_mem_automizer hW, ?_, ?_⟩
  · exact ggConjAut_isReflection hW hnorm Φ hΦcomm hinv hfix
  · intro h ha hh
    exact ggConjAut_fixes_of_mem_comap hAΛ hconj hwH hW ha hh

end CFSG.StandardType

end
