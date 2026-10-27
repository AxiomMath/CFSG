module

public import CFSG.LocalAnalysis.StandardType.KGLangTorusMPartDefs
public import CFSG.LocalAnalysis.StandardType.GGLFourFourThreeMarking
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL45KGForms
public import CFSG.LocalAnalysis.StandardType.GGL45NtDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangKGInputs
public import CFSG.LocalAnalysis.StandardType.GGInnLocalDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.RankThree.PerfectCover CFSG.HardMathSupport.C14Exc

theorem kgLang_coprime_of_centerPrime {p : ℕ} (hp : p.Prime) {R : Type} [Group R]
    (hcent : GGCenterPrime p R) {K : Type} [Group K] [Finite K]
    (θ : K ⧸ Subgroup.center K ≃* R) (hcomm : commutator K = ⊤) :
    Nat.Coprime (Nat.card (Subgroup.center K)) p := by
  let ψ : K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center K))
  have hsurj : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center K := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : QuotientGroup.mk' (Subgroup.center K) x = 1 := by
      apply θ.injective
      rw [map_one]
      exact hx
    exact (QuotientGroup.eq_one_iff x).1 hx1
  have hndvd : ¬ p ∣ Nat.card (Subgroup.center K) := hcent K ψ hsurj hker hcomm
  exact Nat.coprime_comm.mp ((hp.coprime_iff_not_dvd).2 hndvd)

theorem kgLangTorusDatumCont_of_comm {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hR : ∀ a b : R, a * b = b * a) : KGLangTorusDatumCont p R I F := by
  intro _ θ hcomm A hA hAI hA0 α₀ hα₀ hα₀J
  exfalso
  haveI : IsMulCommutative R := isMulCommutative_iff.mpr hR
  let ψ : HopfCover R →* R :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (HopfCover R)))
  have hker : ψ.ker ≤ Subgroup.center (HopfCover R) := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have hx1 : QuotientGroup.mk' (Subgroup.center (HopfCover R)) x = 1 := by
      apply θ.injective
      rw [map_one]
      exact hx
    exact (QuotientGroup.eq_one_iff x).1 hx1
  have hcomm_le : commutator (HopfCover R) ≤ Subgroup.center (HopfCover R) :=
    (Abelianization.commutator_subset_ker ψ).trans hker
  have hcenter : (⊤ : Subgroup (HopfCover R)) ≤ Subgroup.center (HopfCover R) := by
    rw [← hcomm]; exact hcomm_le
  haveI : IsMulCommutative (HopfCover R) :=
    isMulCommutative_iff.mpr fun a b =>
      (Subgroup.mem_center_iff.mp (hcenter trivial) b).symm
  have hbot : commutator (HopfCover R) = ⊥ :=
    le_bot_iff.mp (Abelianization.commutator_subset_ker (MonoidHom.id (HopfCover R)))
  have htopbot : (⊤ : Subgroup (HopfCover R)) = ⊥ := by rw [← hcomm]; exact hbot
  haveI : Subsingleton (HopfCover R) := by
    refine ⟨fun a b => ?_⟩
    have ha : a = 1 := Subgroup.mem_bot.mp (by rw [← htopbot]; trivial)
    have hb : b = 1 := Subgroup.mem_bot.mp (by rw [← htopbot]; trivial)
    rw [ha, hb]
  obtain ⟨α, hα, hα1, -⟩ := hA0
  exact hα1 (MulEquiv.ext fun x => Subsingleton.elim _ _)

theorem kgLangTorusMPart_of_forall_orderOf_ne {p : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hconj : GGRawFieldConj p R I F) (hs : IsSimpleGroup R) (hna : ∃ a b : R, a * b ≠ b * a)
    (hF : ∀ f ∈ F, orderOf f ≠ p) : KGLangTorusMPart p R I F := by
  intro _ θ hcomm A hA hAI hA0 α₀ hα₀ hα₀I
  exfalso
  obtain ⟨u, hu, f, hf, huf⟩ := hAI α₀ hα₀
  have hp1 : (u * f) ^ p = 1 := by
    rw [← huf, ← map_pow, hA.2 α₀ hα₀, map_one]
  have hnotmem : u * f ∉ I := by
    intro hmem
    exact hα₀I (huf ▸ hmem)
  obtain ⟨f', hf'F, -, -, horder, -⟩ := hconj hs hna u hu f hf hnotmem hp1
  exact hF f' hf'F horder

theorem kgLangBridge_eq_one_of_commute {R : Type} [Group R] {Γ : Type*} [Group Γ]
    {G : Subgroup Γ} {ρ : R →* Γ} {Θ : G →* MulAut R} (hρ : Function.Injective ρ)
    (hΘ : Function.Injective Θ)
    (hconj : ∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹)
    {g : G} (hg : ∀ r, (g : Γ) * ρ r = ρ r * g) : g = 1 := by
  have hfix : ∀ r, Θ g r = r := by
    intro r
    apply hρ
    rw [hconj g r, hg r, mul_assoc, mul_inv_cancel, mul_one]
  have hΘg : Θ g = 1 := MulEquiv.ext hfix
  apply hΘ
  rw [hΘg, map_one]

theorem kgLangBridge_pElt_mem_range {p : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    {Γ : Type*} [Group Γ] {G : Subgroup Γ} {ρ : R →* Γ} {Θ : G →* MulAut R}
    (hρ : Function.Injective ρ) (hρG : ∀ r, ρ r ∈ G) (hΘ : Function.Injective Θ)
    (hI : ∀ φ, φ ∈ I ↔ ∃ g, Θ g = φ)
    (hconj : ∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹)
    (hinn : ∀ u ∈ I, GGL45IsPElt p u → ∃ r : R, u = MulAut.conj r)
    {g : G} {k : ℕ} (hg : g ^ (p ^ k) = 1) : ∃ r : R, ρ r = (g : Γ) := by
  have hmem : Θ g ∈ I := (hI (Θ g)).2 ⟨g, rfl⟩
  have hpelt : GGL45IsPElt p (Θ g) := ⟨k, by rw [← map_pow, hg, map_one]⟩
  obtain ⟨r, hr⟩ := hinn (Θ g) hmem hpelt
  refine ⟨r, ?_⟩
  let g₁ : G := ⟨(ρ r)⁻¹ * (g : Γ), G.mul_mem (G.inv_mem (hρG r)) g.2⟩
  have hfix : g₁ = 1 := kgLangBridge_eq_one_of_commute hρ hΘ hconj (g := g₁) (by
    intro r'
    show (ρ r)⁻¹ * (g : Γ) * ρ r' = ρ r' * ((ρ r)⁻¹ * (g : Γ))
    have hcr := hconj g r'
    rw [hr, MulAut.conj_apply, map_mul, map_mul, map_inv] at hcr
    calc (ρ r)⁻¹ * (g : Γ) * ρ r'
        = (ρ r)⁻¹ * ((g : Γ) * ρ r' * (g : Γ)⁻¹) * (g : Γ) := by group
      _ = (ρ r)⁻¹ * (ρ r * ρ r' * (ρ r)⁻¹) * (g : Γ) := by rw [hcr]
      _ = ρ r' * ((ρ r)⁻¹ * (g : Γ)) := by group)
  have hgm : (ρ r)⁻¹ * (g : Γ) = 1 := by
    have := congrArg (fun x : G => (x : Γ)) hfix
    simpa [g₁] using this
  have hge : (g : Γ) = ρ r := by
    have := congrArg (fun x => ρ r * x) hgm
    simpa [mul_assoc] using this
  exact hge.symm

theorem kgLangBridge_root {p : ℕ} (hp : p.Prime) {R : Type} [Group R] {Γ : Type*} [Group Γ]
    {G : Subgroup Γ} {F₀ : Γ →* Γ} (hfix : ∀ g ∈ G, endPow F₀ p g = g)
    {ρ : R →* Γ} (hρG : ∀ r, ρ r ∈ G) {Θ : G →* MulAut R}
    (hconj : ∀ (g : G) (r : R), ρ (Θ g r) = (g : Γ) * ρ r * (g : Γ)⁻¹)
    {f : MulAut R} {j : ℕ} (hfj : ∀ r, ρ (f r) = endPow F₀ j (ρ r)) {j' : ℕ}
    (hjj : j * j' ≡ 1 [MOD p]) (g : G) :
    ∀ r, ρ (((Θ g * f * (Θ g)⁻¹) ^ j') r) = (g : Γ) * F₀ ((g : Γ)⁻¹ * ρ r * g) * (g : Γ)⁻¹ := by
  intro r
  have hfk : ∀ k r, ρ ((f ^ k) r) = endPow F₀ (j * k) (ρ r) := by
    intro k
    induction k with
    | zero => intro r; simp [endPow_apply]
    | succ k ih =>
        intro r
        have harith : j * (k + 1) = j + j * k := by rw [Nat.mul_succ, Nat.add_comm]
        rw [pow_succ', MulAut.mul_apply, hfj, ih r, endPow_apply, endPow_apply, endPow_apply,
          ← Function.iterate_add_apply, harith]
  obtain ⟨m, hm⟩ : ∃ m, j * j' = p * m + 1 := by
    have hmod : (j * j') % p = 1 := by
      have h1 : (1 : ℕ) % p = 1 := Nat.mod_eq_of_lt hp.one_lt
      rw [Nat.ModEq, h1] at hjj
      exact hjj
    refine ⟨(j * j') / p, ?_⟩
    calc j * j' = p * ((j * j') / p) + (j * j') % p := (Nat.div_add_mod (j * j') p).symm
      _ = p * ((j * j') / p) + 1 := by rw [hmod]
  have hF0_iter : ∀ x ∈ G, F₀^[p * m] x = x := by
    intro x hx
    have hpfix : F₀^[p] x = x := by
      have := hfix x hx
      rwa [endPow_apply] at this
    rw [Function.iterate_mul]
    exact Function.iterate_fixed hpfix m
  have hroot : ∀ x ∈ G, endPow F₀ (p * m + 1) x = F₀ x := by
    intro x hx
    rw [endPow_apply]
    rw [show p * m + 1 = (p * m).succ by rw [Nat.succ_eq_add_one]]
    rw [Function.iterate_succ_apply', hF0_iter x hx]
  have hmain : ρ ((f ^ j') ((Θ g)⁻¹ r)) = F₀ ((g : Γ)⁻¹ * ρ r * g) := by
    rw [hfk j' ((Θ g)⁻¹ r)]
    have hconj_inv : ρ ((Θ g)⁻¹ r) = (g : Γ)⁻¹ * ρ r * (g : Γ) := by
      have h1 : (Θ g)⁻¹ = Θ (g⁻¹) := (map_inv Θ g).symm
      rw [h1]
      simpa using hconj (g⁻¹) r
    rw [hconj_inv]
    have hxG : (g : Γ)⁻¹ * ρ r * g ∈ G :=
      G.mul_mem (G.mul_mem (G.inv_mem g.2) (hρG r)) g.2
    rw [hm]
    exact hroot _ hxG
  rw [conj_pow, MulAut.mul_apply, MulAut.mul_apply]
  rw [hconj g ((f ^ j') ((Θ g)⁻¹ r))]
  rw [hmain]

theorem kgLang_exists_mulAut_restrict {Γ : Type*} [Group Γ] {G : Subgroup Γ} [Finite G]
    (F₁ : Γ →* Γ) (hstab : ∀ g ∈ G, F₁ g ∈ G)
    (hinj : ∀ x ∈ G, ∀ y ∈ G, F₁ x = F₁ y → x = y) :
    ∃ β : MulAut G, ∀ x : G, (β x : Γ) = F₁ x := by
  let φ : G →* G :=
    { toFun := fun x => ⟨F₁ x, hstab x x.2⟩
      map_one' := Subtype.ext (map_one F₁)
      map_mul' := fun x y => Subtype.ext (map_mul F₁ (x : Γ) (y : Γ)) }
  have hinjφ : Function.Injective φ := by
    intro x y h
    apply Subtype.ext
    apply hinj x x.2 y y.2
    simpa [φ] using congrArg (fun z : G => (z : Γ)) h
  have hbij : Function.Bijective φ := Finite.injective_iff_bijective.mp hinjφ
  exact ⟨MulEquiv.ofBijective φ hbij, fun x => rfl⟩

theorem kgLang_mulAut_mem_iff {G : Type*} [Group G] [Finite G] (β : MulAut G) {N : Subgroup G}
    (hN : ∀ x ∈ N, β x ∈ N) : ∀ g, β g ∈ N ↔ g ∈ N := by
  intro g
  constructor
  · intro hg
    have hinj : Function.Injective (fun x : N => (⟨β x, hN x x.2⟩ : N)) := by
      intro x y h
      apply Subtype.ext
      apply β.injective
      exact congrArg (fun z : N => (z : G)) h
    have hsurj := Finite.injective_iff_surjective.mp hinj
    obtain ⟨n, hn⟩ := hsurj ⟨β g, hg⟩
    have hnβ : β (n : G) = β g := congrArg (fun z : N => (z : G)) hn
    have hng : (n : G) = g := β.injective hnβ
    exact hng ▸ n.2
  · exact hN g

theorem kgLang_mulAut_pow_coe {Γ : Type*} [Group Γ] {G : Subgroup Γ} (β : MulAut G)
    (F₁ : Γ →* Γ) (hβ : ∀ x : G, (β x : Γ) = F₁ x) (i : ℕ) (x : G) :
    ((β ^ i) x : Γ) = endPow F₁ i x := by
  induction i with
  | zero => rfl
  | succ i ih =>
      rw [pow_succ', MulAut.mul_apply, hβ, ih, endPow_apply, endPow_apply,
        Function.iterate_succ_apply']

theorem kgLang_isElemAbelian_closure {p : ℕ} {Γ : Type*} [Group Γ] {S : Set Γ}
    (hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x) (hpow : ∀ x ∈ S, x ^ p = 1) :
    IsElemAbelian p (Subgroup.closure S) := by
  have hcomm' : ∀ x ∈ Subgroup.closure S, ∀ y ∈ Subgroup.closure S, Commute x y := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
        intro y hy
        induction hy using Subgroup.closure_induction with
        | mem y hy => exact hcomm x hx y hy
        | one => exact Commute.one_right x
        | mul y z hy hz ihy ihz => exact ihy.mul_right ihz
        | inv y hy ihy => exact ihy.inv_right
    | one => intro y hy; exact Commute.one_left y
    | mul x y hx hy ihx ihy => intro z hz; exact (ihx z hz).mul_left (ihy z hz)
    | inv x hx ih => intro y hy; exact (ih y hy).inv_left
  refine ⟨?_, ?_⟩
  · refine isMulCommutative_iff.mpr fun a b => Subtype.ext ?_
    exact hcomm' a a.2 b b.2
  · intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx => exact hpow x hx
    | one => simp
    | mul x y hx hy ihx ihy =>
        rw [Commute.mul_pow (hcomm' x hx y hy), ihx, ihy, mul_one]
    | inv x hx ih => rw [inv_pow, ih, inv_one]

theorem kgLangExcLabel_fam {p : ℕ} {lab : LargeEvenLabel} (h : GGNbrLangRegExcLabel p lab)
    (htw : lab.tag ≠ .twF4) : GGL45KGLabel p lab ∧ GGL45NtFamEx p lab := by
  obtain ⟨tag, rank, n⟩ := lab
  rcases h with h | ⟨h, hp3⟩ | ⟨hp, hp3⟩ | ⟨h, hp3, hp5⟩
  · subst h
    simp [GGL45KGLabel, GGL45NtFamEx, GGL45FamNonTorsion, GGL45NtVacLabel, GGL45NtExcLabel]
  · subst h
    simp [GGL45KGLabel, GGL45NtFamEx, GGL45FamNonTorsion, GGL45NtVacLabel, GGL45NtExcLabel, hp3]
  · rcases hp with h | h | h | h | h <;>
      (subst h;
       simp [GGL45KGLabel, GGL45NtFamEx, GGL45FamNonTorsion, GGL45NtVacLabel, GGL45NtExcLabel, hp3])
  · subst h
    simp [GGL45KGLabel, GGL45NtFamEx, GGL45FamNonTorsion, GGL45NtVacLabel, GGL45NtExcLabel, hp3,
      hp5]

end CFSG.StandardType
