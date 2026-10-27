module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLTv
public import CFSG.LocalAnalysis.StandardType.GGNoTransvectionAutForm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB TableBSymp Matrix

namespace TableBExcTwoTv

theorem ggCenterPrime_of_mulEquiv_tv {p : ℕ} {R R' : Type} [Group R] [Group R'] (e : R ≃* R')
    (h : GGCenterPrime p R') : GGCenterPrime p R := by
  intro L' _ _ ψ hψ hker hperf
  have hker' : (e.toMonoidHom.comp ψ).ker ≤ Subgroup.center L' := by
    intro l hl
    have hl' : e (ψ l) = 1 := hl
    have h1 : ψ l = 1 := (e.map_eq_one_iff).mp hl'
    exact hker (MonoidHom.mem_ker.mpr h1)
  exact h L' (e.toMonoidHom.comp ψ) (e.surjective.comp hψ) hker' hperf

theorem ggNoTransvectionSCr_of_frameTorus {n r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime 3 R) {t : Multiplicative (Fin n → ZMod 3) →* R}
    (ht : Function.Injective t)
    (hT : ∀ E : Subgroup R, IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E →
      (∀ g : R, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) →
        ∃ c : R, E = t.range.map (MulAut.conj c).toMonoidHom)
    (hK : ∀ φ : MulAut R, (∀ x ∈ t.range, φ x ∈ t.range) →
      ∃ M : (Fin n → ZMod 3) →+ (Fin n → ZMod 3),
        (∀ v, φ (t (Multiplicative.ofAdd v)) = t (Multiplicative.ofAdd (M v))) ∧
          ∀ v w, M v ⬝ᵥ M w = v ⬝ᵥ w) :
    GGNoTransvectionSCr 3 r R I := by
  classical
  have := Fact.mk Nat.prime_three
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc α hα htv
  obtain ⟨φ, hφ⟩ := hα
  have hex : ∀ a : A, ∃ g : R, ∀ l : L', ψ ((a : MulAut L') l) = g * ψ l * g⁻¹ := by
    intro a
    obtain ⟨φa, hφaI, hφa⟩ := hAI a a.2
    obtain ⟨g, rfl⟩ := hI hφaI
    exact ⟨g, fun l => (hφa l).symm⟩
  have huniq : ∀ (a : MulAut L') (g g' : R), (∀ l, ψ (a l) = g * ψ l * g⁻¹) →
      (∀ l, ψ (a l) = g' * ψ l * g'⁻¹) → g = g' := by
    intro a g g' hg hg'
    have hc : g'⁻¹ * g ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro x
      obtain ⟨l, rfl⟩ := hψ x
      have e := (hg l).symm.trans (hg' l)
      calc ψ l * (g'⁻¹ * g) = g'⁻¹ * (g' * ψ l * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * ψ l * g⁻¹) * g := by rw [e]
        _ = (g'⁻¹ * g) * ψ l := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.mp hc).symm
  choose χf hχf using hex
  have hχmul : ∀ a b : A, χf (a * b) = χf a * χf b := by
    intro a b
    refine huniq ((a * b : A) : MulAut L') _ _ (hχf (a * b)) fun l => ?_
    rw [Subgroup.coe_mul, MulAut.mul_apply, hχf a, hχf b]
    group
  have hχone : χf 1 = 1 := huniq 1 _ _ (hχf 1) fun l => by simp
  let χ : A →* R := { toFun := χf, map_one' := hχone, map_mul' := hχmul }
  have hχ : ∀ a : A, ∀ l, ψ ((a : MulAut L') l) = χ a * ψ l * (χ a)⁻¹ := hχf
  have hinner : ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ :=
    fun a t' ht' => TableBSymp.eq_conj_of_induces hker hperf (a : MulAut L') t'
      (fun l => by rw [hχ, ht'])
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hinner a 1 (by rw [map_one]; exact ha.symm)
    apply Subtype.ext
    ext l
    rw [h1 l]
    simp
  have hEA : IsElemAbelian 3 χ.range := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcard : Nat.card χ.range = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  have hKnot3 : ∀ z : L', ψ z = 1 → z ^ 3 = 1 → z = 1 := by
    intro z hz hz3
    by_contra hne
    have hord : orderOf z = 3 := orderOf_eq_prime hz3 hne
    have hzc : z ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hz)
    have h1 : orderOf z ∣ Nat.card (Subgroup.center L') := Subgroup.orderOf_dvd_natCard _ hzc
    rw [hord] at h1
    exact hcp L' ψ hψ hker hperf h1
  have hSCE : ∀ g : R, g ^ 3 = 1 → (∀ e ∈ χ.range, g * e = e * g) → g ∈ χ.range := by
    intro g hg3 hgc
    obtain ⟨n, hn⟩ := hψ g
    set N := Nat.card ψ.ker with hNdef
    have hN3 : ¬ 3 ∣ N := by
      intro hdvd
      obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 hdvd
      have h3z : z ^ 3 = 1 := by rw [← hz]; exact pow_orderOf_eq_one z
      have hz3 : (z : L') ^ 3 = 1 := by
        have := congrArg Subtype.val h3z
        simpa using this
      have hz1 : (z : L') ≠ 1 := by
        intro h
        have hz0 : z = 1 := Subtype.ext h
        rw [hz0, orderOf_one] at hz
        norm_num at hz
      exact hz1 (hKnot3 _ (MonoidHom.mem_ker.mp z.2) hz3)
    have hN1 : N % 3 = 1 ∨ N % 3 = 2 := by omega
    have hmod : N ^ 2 % 3 = 1 := by
      rw [sq, Nat.mul_mod]
      rcases hN1 with h | h <;> simp [h]
    have hkN : ∀ k : L', ψ k = 1 → k ^ N = 1 := by
      intro k hk
      have h := pow_card_eq_one' (G := ψ.ker) (x := ⟨k, MonoidHom.mem_ker.mpr hk⟩)
      have h2 := congrArg Subtype.val h
      rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
      exact h2
    set x : L' := n ^ (N ^ 2) with hxdef
    have hxpow : ψ x = g := by
      rw [hxdef, map_pow, hn]
      obtain ⟨q, hq⟩ : ∃ q, N ^ 2 = 3 * q + 1 := ⟨N ^ 2 / 3, by omega⟩
      rw [hq, pow_succ, pow_mul, hg3, one_pow, one_mul]
    have hx3 : x ^ 3 = 1 := by
      have hk0 : n ^ 3 ∈ ψ.ker := MonoidHom.mem_ker.mpr (by rw [map_pow, hn, hg3])
      rw [hxdef, ← pow_mul, mul_comm, pow_mul, sq, pow_mul, hkN _ (MonoidHom.mem_ker.mp hk0),
        one_pow]
    have huniq3 : ∀ y : L', ψ y = g → y ^ 3 = 1 → y = x := by
      intro y hy hy3
      set k := y⁻¹ * x with hkdef
      have hk : ψ k = 1 := by
        rw [hkdef, map_mul, map_inv, hy, hxpow, inv_mul_cancel]
      have hkc : k ∈ Subgroup.center L' := hker (MonoidHom.mem_ker.mpr hk)
      have hkcomm : k * y = y * k := (Subgroup.mem_center_iff.mp hkc y).symm
      have hxk : x = y * k := by rw [hkdef]; group
      have hcomm : Commute y x := by
        show y * x = x * y
        rw [hxk, mul_assoc y k y, hkcomm]
      have hk3 : k ^ 3 = 1 := by
        rw [hkdef, Commute.mul_pow hcomm.inv_left, inv_pow, hy3, inv_one, hx3, one_mul]
      have hk1 : k = 1 := hKnot3 k hk hk3
      rw [hkdef] at hk1
      exact inv_mul_eq_one.mp hk1
    have hfix : ∀ a ∈ A, a x = x := by
      intro a ha
      apply huniq3
      · have h1 : ψ (a x) = χ ⟨a, ha⟩ * ψ x * (χ ⟨a, ha⟩)⁻¹ := hχ ⟨a, ha⟩ x
        rw [h1, hxpow]
        have hc := hgc (χ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
        rw [← hc, mul_inv_cancel_right]
      · rw [← map_pow, hx3, map_one]
    have hcA : MulAut.conj x ∈ A := hsc x hfix hx3
    exact ⟨⟨MulAut.conj x, hcA⟩, huniq (MulAut.conj x) _ g (hχ ⟨MulAut.conj x, hcA⟩)
      (fun l => by rw [MulAut.conj_apply, map_mul, map_mul, map_inv, hxpow])⟩
  obtain ⟨c, hc⟩ := hT χ.range hEA (hcard ▸ hr) hSCE
  set J : Multiplicative (Fin n → ZMod 3) →* R := (MulAut.conj c).toMonoidHom.comp t with hJdef
  have hJmem : ∀ s, J s ∈ χ.range := fun s => by
    rw [hc]
    exact Subgroup.mem_map_of_mem _ (MonoidHom.mem_range.mpr ⟨s, rfl⟩)
  have hJinj : Function.Injective J := (MulAut.conj c).injective.comp ht
  set e : A ≃* χ.range := MonoidHom.ofInjective hχinj with hedef
  set κ : Multiplicative (Fin n → ZMod 3) →* A :=
    e.symm.toMonoidHom.comp (J.codRestrict χ.range hJmem) with hκdef
  have hκ : ∀ s, χ (κ s) = J s := fun s =>
    MonoidHom.apply_ofInjective_symm hχinj (J.codRestrict χ.range hJmem s)
  have hκinj : Function.Injective κ := fun s s' h => hJinj (by rw [← hκ s, ← hκ s', h])
  have hκsurj : ∀ a : A, ∃ s, κ s = a := by
    intro a
    have ha : χ a ∈ χ.range := MonoidHom.mem_range.mpr ⟨a, rfl⟩
    rw [hc] at ha
    obtain ⟨x, hx, hxa⟩ := Subgroup.mem_map.mp ha
    obtain ⟨s, rfl⟩ := MonoidHom.mem_range.mp hx
    refine ⟨s, hχinj ?_⟩
    rw [hκ s]
    exact hxa
  set ι : Multiplicative (Fin n → ZMod 3) →* MulAut L' := A.subtype.comp κ with hιdef
  have hι : Function.Injective ι := fun s s' h => hκinj (Subtype.ext h)
  have hιrange : ι.range = A := by
    ext a
    constructor
    · rintro ⟨s, rfl⟩
      exact (κ s).2
    · intro ha
      obtain ⟨s, hs⟩ := hκsurj ⟨a, ha⟩
      exact ⟨s, congrArg Subtype.val hs⟩
  set αA : MulAut A := A.normalizerMonoidHom α with hαAdef
  have hαAcoe : ∀ b : A, ((αA b : A) : MulAut L') =
      (α : MulAut L') * (b : MulAut L') * (α : MulAut L')⁻¹ := fun b => rfl
  have hαinv : ∀ l, (α : MulAut L') ((α : MulAut L')⁻¹ l) = l := fun l => by
    rw [← MulAut.mul_apply, mul_inv_cancel, MulAut.one_apply]
  have hφinv : ∀ l, φ (ψ ((α : MulAut L')⁻¹ l)) = ψ l := fun l => by
    rw [hφ, hαinv]
  have hequiv : ∀ b : A, χ (αA b) = φ (χ b) := by
    intro b
    refine huniq _ _ _ (hχ (αA b)) (fun l => ?_)
    calc ψ (((αA b : A) : MulAut L') l)
        = ψ ((α : MulAut L') (((b : A) : MulAut L') ((α : MulAut L')⁻¹ l))) := by
          rw [hαAcoe, MulAut.mul_apply, MulAut.mul_apply]
      _ = φ (ψ (((b : A) : MulAut L') ((α : MulAut L')⁻¹ l))) := (hφ _).symm
      _ = φ (χ b * ψ ((α : MulAut L')⁻¹ l) * (χ b)⁻¹) := by rw [hχ b]
      _ = φ (χ b) * φ (ψ ((α : MulAut L')⁻¹ l)) * (φ (χ b))⁻¹ := by
          simp only [map_mul, map_inv]
      _ = φ (χ b) * ψ l * (φ (χ b))⁻¹ := by rw [hφinv l]
  have hφE : ∀ y ∈ χ.range, φ y ∈ χ.range := by
    intro y hy
    obtain ⟨a, rfl⟩ := MonoidHom.mem_range.mp hy
    rw [← hequiv a]
    exact MonoidHom.mem_range.mpr ⟨αA a, rfl⟩
  set ψ' : MulAut R := (MulAut.conj c)⁻¹ * φ * MulAut.conj c with hψ'def
  have hψ'app : ∀ x : R, ψ' x = c⁻¹ * φ (c * x * c⁻¹) * c := fun x => rfl
  have hψ'T : ∀ x ∈ t.range, ψ' x ∈ t.range := by
    intro x hx
    have h1 : c * x * c⁻¹ ∈ χ.range := by
      rw [hc]
      exact Subgroup.mem_map_of_mem _ hx
    have h2 : φ (c * x * c⁻¹) ∈ χ.range := hφE _ h1
    rw [hc] at h2
    obtain ⟨z, hz, hzeq⟩ := Subgroup.mem_map.mp h2
    have hψz : ψ' x = z := by
      rw [hψ'app, ← hzeq]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hψz]
    exact hz
  obtain ⟨M, hMψ, hMiso⟩ := hK ψ' hψ'T
  have hφJ : ∀ s : Fin n → ZMod 3,
      φ (J (Multiplicative.ofAdd s)) = J (Multiplicative.ofAdd (M s)) := by
    intro s
    have h1 := hMψ s
    rw [hψ'app] at h1
    show φ (c * t (Multiplicative.ofAdd s) * c⁻¹) = c * t (Multiplicative.ofAdd (M s)) * c⁻¹
    rw [← h1]
    group
  have hrel : ∀ (b : A) (s : Fin n → ZMod 3), (b : MulAut L') = ι (Multiplicative.ofAdd s) →
      ((αA b : A) : MulAut L') = ι (Multiplicative.ofAdd (M s)) := by
    intro b s hb
    have hbκ : b = κ (Multiplicative.ofAdd s) := Subtype.ext hb
    have hχb : χ b = J (Multiplicative.ofAdd s) := by rw [hbκ, hκ]
    have hχα : χ (αA b) = J (Multiplicative.ofAdd (M s)) := by
      rw [hequiv b, hχb, hφJ]
    have hαAκ : αA b = κ (Multiplicative.ofAdd (M s)) := hχinj (hχα.trans (hκ _).symm)
    show ((αA b : A) : MulAut L') = ((κ (Multiplicative.ofAdd (M s)) : A) : MulAut L')
    rw [hαAκ]
  obtain ⟨hcardfix, hNfix⟩ := NoTvAut.transvection_coords (p := 3) hι hιrange (t := ⇑M) hrel htv
  exact NoTvAut.false_of_isTransvection_similitude (p := 3) (by norm_num) (S := 1)
    Matrix.transpose_one (by simp) M 1 (fun x y => by simp [hMiso x y]) hcardfix hNfix

end TableBExcTwoTv

end CFSG.StandardType

end
