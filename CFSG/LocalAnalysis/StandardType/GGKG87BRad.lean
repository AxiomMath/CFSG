module

public import CFSG.LocalAnalysis.StandardType.GGKG87BRadDefs
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelQ8Kernel
public import CFSG.LocalAnalysis.StandardType.GGKG87BThreeA2
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6PerBstar
public import CFSG.LocalAnalysis.StandardType.GGTableBOutdiag
public import CFSG.LocalAnalysis.StandardType.GGNbrFieldFixPerfect

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.E6Three

namespace KG87B

variable {p : ℕ} {L' : Type} [Group L'] {A : Subgroup (MulAut L')}

private theorem mul_inv_apply_mem_center (hA : IsElemAbelian p A) {k : L'} (hk : MulAut.conj k ∈ A)
    {a : MulAut L'} (ha : a ∈ A) : k * (a k)⁻¹ ∈ Subgroup.center L' := by
  have hcomm : a * MulAut.conj k = MulAut.conj k * a :=
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨_, hk⟩)
  have h1 : ∀ l : L', a k * l * (a k)⁻¹ = k * l * k⁻¹ := by
    intro l
    have := congrArg (fun φ : MulAut L' => φ (a⁻¹ l)) hcomm
    simpa [MulAut.mul_apply, MulAut.conj_apply] using this
  have hc : k⁻¹ * a k ∈ Subgroup.center L' := by
    rw [Subgroup.mem_center_iff]
    intro l
    have := h1 l
    calc l * (k⁻¹ * a k) = k⁻¹ * (k * l * k⁻¹) * k * (k⁻¹ * a k) := by group
      _ = k⁻¹ * (a k * l * (a k)⁻¹) * k * (k⁻¹ * a k) := by rw [this]
      _ = k⁻¹ * a k * l := by group
  have e : k * (a k)⁻¹ = (k⁻¹ * a k)⁻¹ := by
    have h2 := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hc) k
    calc k * (a k)⁻¹ = k * (k⁻¹ * a k)⁻¹ * k⁻¹ := by group
      _ = (k⁻¹ * a k)⁻¹ * k * k⁻¹ := by rw [h2]
      _ = (k⁻¹ * a k)⁻¹ := by group
  rw [e]
  exact Subgroup.inv_mem _ hc

private theorem ggTorusWeylElt_of_conj_mem (hA : IsElemAbelian p A) {k : L'} (hk : MulAut.conj k ∈ A)
    (hfix : ∀ a ∈ A, ∀ a' ∈ A, a' (k * (a k)⁻¹) = k * (a k)⁻¹) : GGTorusWeylElt p A k := by
  intro a ha
  refine ⟨?_, fun a' ha' => hfix a ha a' ha'⟩
  have hz := mul_inv_apply_mem_center hA hk ha
  set z := k * (a k)⁻¹ with hzdef
  have hak : a k = z⁻¹ * k := by rw [hzdef]; group
  have haz : a z = z := hfix a ha a ha
  have hpow : ∀ m : ℕ, (a ^ m) k = (z⁻¹) ^ m * k := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, map_inv, haz, hak]
      group
  have hk' := hpow p
  rw [hA.2 a ha, MulAut.one_apply] at hk'
  have h1 : (z⁻¹) ^ p = 1 := by
    have := congrArg (· * k⁻¹) hk'
    simpa using this.symm
  rw [inv_pow] at h1
  exact inv_eq_one.mp h1

private theorem ggHeisFieldComp_of_rad {r : ℕ} {R : Type} [Group R] {I F : Set (MulAut R)}
    (hcen : ∀ g : R, (∀ h : R, g * h = h * g) → g = 1)
    (hZ : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → p ∣ Nat.card ψ.ker →
      ∀ a : MulAut L', a ^ p = 1 → ∀ z ∈ ψ.ker, a z = z)
    (hrad : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → p ∣ Nat.card ψ.ker →
      ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
        (∀ a ∈ A, ∃ φ ∈ Subgroup.closure (I ∪ F), ∀ l : L', φ (ψ l) = ψ (a l)) →
        (∃ a ∈ A, ¬ ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
        Nat.card A = p ^ r → GGTorusSelfCent p A →
        ∀ a₀ ∈ A, a₀ ≠ 1 → (∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a₀ l)) → GGFixCompCyclic p a₀ →
          (∀ k : L', MulAut.conj k ∈ A → a₀ k = k) →
          ∃ n : L', GGTorusWeylElt p A n ∧
            MulAut.conj n * a₀ * (MulAut.conj n)⁻¹ ∉ Subgroup.zpowers a₀) :
    GGHeisFieldComp p r R I F := by
  intro L' _ _ ψ hψ hker hperf hp A hA hAI hAF hcard hsc a₀ ha₀ hne hI hcomp
  by_cases hk : ∃ k : L', MulAut.conj k ∈ A ∧ a₀ k ≠ k
  · obtain ⟨k, hkA, hk₀⟩ := hk
    have hkerz : ∀ a ∈ A, k * (a k)⁻¹ ∈ ψ.ker := by
      intro a ha
      have hz := mul_inv_apply_mem_center hA hkA ha
      rw [MonoidHom.mem_ker]
      refine hcen _ fun h => ?_
      obtain ⟨l, rfl⟩ := hψ h
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    refine ⟨k, ggTorusWeylElt_of_conj_mem hA hkA fun a ha a' ha' =>
      hZ L' ψ hψ hker hperf hp a' (hA.2 a' ha') _ (hkerz a ha), Or.inr ⟨?_, ?_⟩⟩
    · exact mul_inv_apply_mem_center hA hkA ha₀
    · intro h
      exact hk₀ (by
        have := congrArg (· * a₀ k) h
        simpa using this.symm)
  · push Not at hk
    obtain ⟨n, hn, hmv⟩ := hrad L' ψ hψ hker hperf hp A hA hAI hAF hcard hsc a₀ ha₀ hne hI hcomp
      fun k hkA => hk k hkA
    exact ⟨n, hn, Or.inl hmv⟩

end KG87B

private theorem KG87B.fix_ker_twE6
    {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 3 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    (hcen : ∀ g : TwE6Delta.RecipeR K n, (∀ h, g * h = h * g) → g = 1)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {a : MulAut L'} (ha : a ^ 3 = 1) {z : L'} (hz : z ∈ ψ.ker) : a z = z := by
  have h3 := TwE6Delta.card_ker_dvd_three_q8 hn hK hψ hker hperf
  have hZk : ∀ w : L', w ∈ Subgroup.center L' → w ∈ ψ.ker := fun w hw => by
    rw [MonoidHom.mem_ker]
    refine hcen _ fun h => ?_
    obtain ⟨l, rfl⟩ := hψ h
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hw l]
  have hmapk : ∀ w ∈ ψ.ker, a w ∈ ψ.ker := fun w hw => hZk _ (by
    rw [Subgroup.mem_center_iff]
    intro l
    have hzc := Subgroup.mem_center_iff.mp (hker hw) (a⁻¹ l)
    have := congrArg a hzc
    simpa only [map_mul, MulAut.apply_inv_self] using this)
  by_cases hz1 : z = 1
  · rw [hz1, map_one]
  have hord : orderOf z = 3 := by
    have hd : orderOf z ∣ 3 := by
      have h1 := orderOf_dvd_natCard (⟨z, hz⟩ : ψ.ker)
      rw [Subgroup.orderOf_mk] at h1
      exact h1.trans h3
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hz1
    · exact h
  have hz3 : z ^ 3 = 1 := by rw [← hord]; exact pow_orderOf_eq_one z
  have hle : Subgroup.zpowers z ≤ ψ.ker := (Subgroup.zpowers_le).mpr hz
  have heq : Subgroup.zpowers z = ψ.ker := by
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [Nat.card_zpowers, hord]
    exact Nat.le_of_dvd (by norm_num) h3
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (heq ▸ hmapk z hz : a z ∈ Subgroup.zpowers z)
  have hzm : ∀ k : ℤ, z ^ k = z ^ (k % 3) := fun k =>
    zpow_eq_zpow_emod k (by exact_mod_cast hz3 : z ^ (3 : ℤ) = 1)
  rw [hzm] at hm
  have hm3 : m % 3 = 0 ∨ m % 3 = 1 ∨ m % 3 = 2 := by omega
  rcases hm3 with h | h | h
  ·
    rw [h, zpow_zero] at hm
    exact absurd (a.injective (hm.symm.trans (map_one a).symm)) hz1
  · rw [h, zpow_one] at hm
    exact hm.symm
  ·
    rw [h] at hm
    have h2 : a z = z ^ 2 := by rw [← hm]; norm_cast
    have hak : ∀ k : ℕ, a (z ^ k) = z ^ (2 * k) := fun k => by rw [map_pow, h2, ← pow_mul]
    have ha3 : (a ^ 3) z = z ^ 2 := by
      have e3 : (a ^ 3) z = a (a (a z)) := by
        simp only [pow_succ, pow_zero, one_mul, MulAut.mul_apply]
      rw [e3, h2, hak, hak, show 2 * (2 * 2) = 3 * 2 + 2 by norm_num, pow_add, pow_mul, hz3,
        one_pow, one_mul]
    rw [ha, MulAut.one_apply] at ha3
    exfalso
    apply hz1
    have : z * z = z * 1 := by rw [mul_one, ← pow_two, ← ha3]
    exact mul_left_cancel this


private theorem eq_one_of_forall_commute {R : Type} [Group R] (hs : IsSimpleGroup R)
    (hna : ∃ a b : R, a * b ≠ b * a) {g : R} (hg : ∀ h : R, g * h = h * g) : g = 1 := by
  have := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center R) with h | h
  · have : g ∈ Subgroup.center R := Subgroup.mem_center_iff.mpr fun h' => (hg h').symm
    rw [h] at this
    exact this
  · obtain ⟨a, b, hab⟩ := hna
    have : a ∈ Subgroup.center R := by rw [h]; trivial
    exact absurd (Subgroup.mem_center_iff.mp this b).symm hab

theorem ggNbrKGFieldTwE6ThreeAddHeis_of_rad
    (h : GGNbrKGFieldTwE6ThreeAddHeisRad) : GGNbrKGFieldTwE6ThreeAddHeis := by
  intro lab hlab ht h3
  have hR : LargeEvenLabelAll lab fun R _ I F =>
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGHeisFieldCompRad 3 5 R I F) →
        IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGHeisFieldComp 3 5 R I F := by
    obtain ⟨t, l, n⟩ := lab
    obtain ⟨hn, -⟩ := hlab
    dsimp only at ht h3
    subst ht
    intro Q hQ
    refine recipeTwisted_and (P := fun R _ I F =>
      (IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGHeisFieldCompRad 3 5 R I F) →
        IsSimpleGroup R → (∃ a b : R, a * b ≠ b * a) → GGHeisFieldComp 3 5 R I F)
      (fun K _ _ hK hrad hs hna => ?_) hQ
    have hcen := fun (g : TwE6Delta.RecipeR K n) (hg : ∀ h, g * h = h * g) =>
      eq_one_of_forall_commute hs hna hg
    by_cases h3n : 3 ∣ n
    ·
      have hn0 : 0 < n := hn
      have hn3 : 3 ≤ n := Nat.le_of_dvd hn0 h3n
      refine KG87B.ggHeisFieldComp_of_rad hcen
        (fun L' _ _ ψ hψ hker hperf _ a ha z hz =>
          KG87B.fix_ker_twE6 hn3 hK hcen hψ hker hperf ha hz)
        (fun L' _ _ ψ hψ hker hperf hp A hA hAI hAF hcard hsc a₀ ha₀ hne hI hcomp hrad' => ?_)
      obtain ⟨φ, hφ, hφl⟩ := hI
      refine hrad hs hna L' ψ hψ hker hperf hp A hA hAI hAF hcard hsc a₀ ha₀ hne
        ⟨φ, hφ, hφl, fun h3A2 => ?_⟩ hrad'
      obtain ⟨g, rfl, hg3, K', _, _, σ, q, ε, hK3, hσ, hKq, h3q, hq2, hdim⟩ := h3A2
      exact KG87B.not_ggFixCompCyclic_of_threeA2 hK3 hσ hKq h3q hq2 ε hψ hker hφl hg3 hdim hcomp
    ·
      intro L' _ _ ψ hψ hker hperf _ A hA hAI hAF
      exfalso
      obtain ⟨a, ha, hnot⟩ := hAF
      obtain ⟨φ, -, hφl⟩ := hAI a ha
      have hφ3 : φ ^ 3 = 1 := by
        ext r
        obtain ⟨l, rfl⟩ := hψ r
        rw [ggInduced_pow ψ hφl 3 l, hA.2 a ha]
        rfl
      exact hnot ⟨φ, TwE6Per.mem_recipeI_of_pow_eq_one hn hK Nat.prime_three (by norm_num) h3n hφ3,
        hφl⟩
  intro Q hQ
  exact largeEvenRawDatum_mono (fun _ _ _ _ h' => ⟨h'.1.1, h'.2 h'.1.2⟩)
    (hR _ (h lab hlab ht h3 Q hQ))

end CFSG.StandardType
