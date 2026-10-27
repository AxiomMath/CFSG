module

public import CFSG.LocalAnalysis.StandardType.GGTableBF4TwoTBTvFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLLine
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB TableBSymp

namespace TableBF4TwoTB

@[expose] def GGTorusIrredSCrJ (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      (∃ a ∈ A, a ≠ 1 ∧ ∃ J : Subgroup L', (∀ l ∈ J, a l = l) ∧ ¬ Group.IsSolvable J) →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        (∀ A' : Subgroup (MulAut L'), A' ≤ A →
          (∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A') → A' = ⊥ ∨ A' = A) ∧
        (∃ n ∈ W, ∃ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ≠ a) ∧
        ∀ f : MulAut L' → MulAut L', (∀ a ∈ A, f a ∈ A) →
          (∀ a ∈ A, ∀ b ∈ A, f (a * b) = f a * f b) →
          (∀ n ∈ W, ∀ a ∈ A, f (MulAut.conj n * a * (MulAut.conj n)⁻¹) =
            MulAut.conj n * f a * (MulAut.conj n)⁻¹) →
          ∃ c : ℕ, ∀ a ∈ A, f a = a ^ c

@[expose] def GGNoInvariantLineSCrJ (p r : ℕ) (R : Type) [Group R] (I : Set (MulAut R)) : Prop :=
  ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
    ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
    ∀ A : Subgroup (MulAut L'), IsElemAbelian p A →
      (∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) →
      p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A → GGTorusSelfCent p A →
      (∃ a ∈ A, a ≠ 1 ∧ ∃ J : Subgroup L', (∀ l ∈ J, a l = l) ∧ ¬ Group.IsSolvable J) →
      ∃ W : Set L',
        (∀ n ∈ W, ∀ a ∈ A, (n * (a n)⁻¹) ^ p = 1 ∧ ∀ a' ∈ A, a' (n * (a n)⁻¹) = n * (a n)⁻¹) ∧
        ∀ Λ : Subgroup (MulAut L'), Λ ≤ A → Nat.card Λ = p →
          ∃ n ∈ W, ∃ e ∈ Λ, MulAut.conj n * e * (MulAut.conj n)⁻¹ ∉ Λ

theorem ggTorusIrredSCrJ_of_secEltSC {r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime 3 R)
    (h : ∀ E : Subgroup R, IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E → 3 ^ 3 ≤ Nat.card E →
      (∀ g : R, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) →
      (∃ e ∈ E, e ≠ 1 ∧ ¬ Group.IsSolvable (Subgroup.centralizer ({e} : Set R))) →
        E6TwoTB.SecEltAt 3 E) :
    GGTorusIrredSCrJ 3 r R I := by
  classical
  have := Fact.mk Nat.prime_three
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc hJ
  have hex : ∀ a : A, ∃ t : R, ∀ l, ψ ((a : MulAut L') l) = t * ψ l * t⁻¹ := by
    intro a
    obtain ⟨φ, hφI, hφ⟩ := hAI a a.2
    obtain ⟨t, rfl⟩ := hI hφI
    exact ⟨t, fun l => (hφ l).symm⟩
  have huniq : ∀ (a : MulAut L') (t t' : R), (∀ l, ψ (a l) = t * ψ l * t⁻¹) →
      (∀ l, ψ (a l) = t' * ψ l * t'⁻¹) → t = t' := by
    intro a t t' ht ht'
    have hc : t'⁻¹ * t ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := hψ g
      have e := (ht l).symm.trans (ht' l)
      calc ψ l * (t'⁻¹ * t) = t'⁻¹ * (t' * ψ l * t'⁻¹) * t := by group
        _ = t'⁻¹ * (t * ψ l * t⁻¹) * t := by rw [e]
        _ = (t'⁻¹ * t) * ψ l := by group
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
  obtain ⟨k, τ, WR, hτE, hsec, hWE, hirr, ⟨w₀, hw₀, e₀, he₀, hwe₀⟩, hschur⟩ :=
    h χ.range hEA (hcard ▸ hr) (hcard ▸ h3) hSCE
      (exists_mem_centralizer_nonsolvable ψ hker A χ hχ hχinj hJ)
  obtain ⟨σ, hσ⟩ := hsec L' ψ hψ hker
  have hψσ : ∀ f, ψ (σ f) = τ f := fun f => DFunLike.congr_fun hσ f
  have hfp : ∀ f : Fin k → Multiplicative (ZMod 3), f ^ 3 = 1 := by
    intro f
    funext i
    rw [Pi.pow_apply, Pi.one_apply, ← ofAdd_toAdd (f i), ← ofAdd_nsmul, nsmul_eq_mul,
      ZMod.natCast_self, zero_mul, ofAdd_zero]
  have hσp : ∀ f, σ f ^ 3 = 1 := fun f => by rw [← map_pow, hfp, map_one]
  have hσc : ∀ f g, σ f * σ g = σ g * σ f := fun f g => by
    rw [← map_mul, ← map_mul, mul_comm]
  have hzc : ∀ z ∈ ψ.ker, ∀ x : L', z * x = x * z := fun z hz x =>
    (Subgroup.mem_center_iff.mp (hker hz) x).symm
  have hsecA : ∀ (a : MulAut L') (ha : a ∈ A), ∃ f, τ f = χ ⟨a, ha⟩ ∧
      ∀ l, a l = σ f * l * (σ f)⁻¹ := by
    intro a ha
    have hmem : χ ⟨a, ha⟩ ∈ τ.range := hτE ▸ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨f, hf⟩ := hmem
    exact ⟨f, hf, hinner ⟨a, ha⟩ (σ f) (by rw [hψσ, hf])⟩
  have hform : ∀ n : L', ψ n ∈ WR → ∀ (a : MulAut L') (ha : a ∈ A), ∃ g, ∃ z ∈ ψ.ker,
      z ^ 3 = 1 ∧ n * (a n)⁻¹ = σ g * z := by
    intro n hn a ha
    obtain ⟨f, hf, ha'⟩ := hsecA a ha
    have hu : ψ (n * σ f * n⁻¹) ∈ τ.range := by
      rw [hτE, map_mul, map_mul, map_inv, hψσ, hf]
      exact hWE _ hn _ ⟨⟨a, ha⟩, rfl⟩
    obtain ⟨g, hg⟩ := hu
    set z := (σ g)⁻¹ * (n * σ f * n⁻¹) with hz
    have hzk : z ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, hz, map_mul, map_inv, hψσ, hg, inv_mul_cancel]
    have h2 : n * σ f * n⁻¹ = σ g * z := by rw [hz, mul_inv_cancel_left]
    have hzp : z ^ 3 = 1 := by
      have h1 : (n * σ f * n⁻¹) ^ 3 = 1 := by rw [conj_pow, hσp, mul_one, mul_inv_cancel]
      rw [h2, Commute.mul_pow (hzc z hzk (σ g)).symm, hσp, one_mul] at h1
      exact h1
    refine ⟨g * f⁻¹, z, hzk, hzp, ?_⟩
    rw [ha' n]
    calc n * (σ f * n * (σ f)⁻¹)⁻¹ = (n * σ f * n⁻¹) * (σ f)⁻¹ := by group
      _ = σ g * z * (σ f)⁻¹ := by rw [h2]
      _ = σ g * (σ f)⁻¹ * z := by rw [mul_assoc, hzc z hzk (σ f)⁻¹, ← mul_assoc]
      _ = σ (g * f⁻¹) * z := by rw [map_mul, ← map_inv σ f]
  have hconjA : ∀ n : L', ψ n ∈ WR → ∀ a ∈ A, MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A := by
    intro n hn a ha
    obtain ⟨t, ht⟩ := hψ (χ ⟨a, ha⟩)
    have hat := hinner ⟨a, ha⟩ t ht
    obtain ⟨a', ha'⟩ : ψ n * χ ⟨a, ha⟩ * (ψ n)⁻¹ ∈ χ.range := hWE _ hn _ ⟨⟨a, ha⟩, rfl⟩
    have ha't := hinner a' (n * t * n⁻¹) (by rw [map_mul, map_mul, map_inv, ht, ha'])
    have he : MulAut.conj n * a * (MulAut.conj n)⁻¹ = (a' : MulAut L') := by
      ext l
      rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply, hat,
        ha't]
      group
    rw [he]
    exact a'.2
  have hχconj : ∀ (n : L') (a : MulAut L') (ha : a ∈ A)
      (hna : MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A),
      χ ⟨_, hna⟩ = ψ n * χ ⟨a, ha⟩ * (ψ n)⁻¹ := by
    intro n a ha hna
    refine huniq _ _ _ (hχ ⟨_, hna⟩) fun l => ?_
    simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply]
    rw [map_mul, map_mul, map_inv, hχ ⟨a, ha⟩]
    simp only [map_mul, map_inv]
    group
  refine ⟨ψ ⁻¹' WR, fun n hn a ha => ?_, fun A' hA'A hinv => ?_, ?_, fun f hfA hfmul hfW => ?_⟩
  ·
    obtain ⟨g, z, hzk, hzp, he⟩ := hform n hn a ha
    refine ⟨?_, fun a' ha' => ?_⟩
    · rw [he, Commute.mul_pow (hzc z hzk (σ g)).symm, hσp, hzp, one_mul]
    · obtain ⟨f', -, ha''⟩ := hsecA a' ha'
      rw [he, ha'']
      calc σ f' * (σ g * z) * (σ f')⁻¹ = σ f' * σ g * z * (σ f')⁻¹ := by group
        _ = σ g * σ f' * z * (σ f')⁻¹ := by rw [hσc]
        _ = σ g * (z * σ f') * (σ f')⁻¹ := by rw [hzc z hzk (σ f')]; group
        _ = σ g * z := by group
  ·
    set E' : Subgroup R := (A'.subgroupOf A).map χ with hE'
    have hE'E : E' ≤ χ.range := Subgroup.map_le_range _ _
    have hE'inv : ∀ w ∈ WR, ∀ e ∈ E', w * e * w⁻¹ ∈ E' := by
      rintro w hw _ ⟨⟨a, ha⟩, haA', rfl⟩
      obtain ⟨n, rfl⟩ := hψ w
      have hna := hinv n hw a (Subgroup.mem_subgroupOf.mp haA')
      exact ⟨⟨_, hA'A hna⟩, Subgroup.mem_subgroupOf.mpr hna, hχconj n a ha (hA'A hna)⟩
    rcases hirr E' hE'E hE'inv with hbot | htop
    · left
      rw [eq_bot_iff]
      intro a haA'
      have hmem : χ ⟨a, hA'A haA'⟩ ∈ E' :=
        ⟨⟨a, hA'A haA'⟩, Subgroup.mem_subgroupOf.mpr haA', rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      have h1 : (⟨a, hA'A haA'⟩ : A) = 1 := hχinj (hmem.trans (map_one χ).symm)
      rw [Subgroup.mem_bot]
      exact congrArg Subtype.val h1
    · right
      refine le_antisymm hA'A fun a ha => ?_
      have hmem : χ ⟨a, ha⟩ ∈ E' := by
        rw [htop]
        exact ⟨⟨a, ha⟩, rfl⟩
      obtain ⟨a', ha', he⟩ := hmem
      have he' : a' = ⟨a, ha⟩ := hχinj he
      rw [he'] at ha'
      exact Subgroup.mem_subgroupOf.mp ha'
  ·
    obtain ⟨n, rfl⟩ := hψ w₀
    obtain ⟨⟨a₀, ha₀⟩, rfl⟩ := he₀
    refine ⟨n, hw₀, a₀, ha₀, fun heq => hwe₀ ?_⟩
    rw [← hχconj n a₀ ha₀ (hconjA n hw₀ a₀ ha₀)]
    congr 1
    exact Subtype.ext heq
  ·
    let e' : A ≃* χ.range := MonoidHom.ofInjective hχinj
    let F : R → R := fun y => if hy : y ∈ χ.range then
      χ ⟨f ((e'.symm ⟨y, hy⟩ : A) : MulAut L'), hfA _ (e'.symm ⟨y, hy⟩).2⟩ else y
    have hF : ∀ (a : MulAut L') (ha : a ∈ A), F (χ ⟨a, ha⟩) = χ ⟨f a, hfA a ha⟩ := by
      intro a ha
      have hy : χ ⟨a, ha⟩ ∈ χ.range := ⟨⟨a, ha⟩, rfl⟩
      have hs : e'.symm ⟨χ ⟨a, ha⟩, hy⟩ = ⟨a, ha⟩ := by
        rw [show (⟨χ ⟨a, ha⟩, hy⟩ : χ.range) = e' ⟨a, ha⟩ from
          Subtype.ext (MonoidHom.ofInjective_apply hχinj (x := ⟨a, ha⟩)).symm,
          MulEquiv.symm_apply_apply]
      show (if hy : χ ⟨a, ha⟩ ∈ χ.range then _ else _) = _
      rw [dite_eq_left hy]
      congr 1
      apply Subtype.ext
      show f ((e'.symm ⟨χ ⟨a, ha⟩, hy⟩ : A) : MulAut L') = f a
      rw [hs]
    obtain ⟨c, hc⟩ := hschur F
      (by
        rintro _ ⟨⟨a, ha⟩, rfl⟩
        rw [hF a ha]
        exact ⟨_, rfl⟩)
      (by
        rintro _ ⟨⟨a, ha⟩, rfl⟩ _ ⟨⟨b, hb⟩, rfl⟩
        have e1 : χ ⟨a, ha⟩ * χ ⟨b, hb⟩ = χ ⟨a * b, A.mul_mem ha hb⟩ := by
          rw [← map_mul]
          rfl
        rw [e1, hF _ (A.mul_mem ha hb), hF a ha, hF b hb, ← map_mul]
        congr 1
        exact Subtype.ext (hfmul a ha b hb))
      (by
        rintro w hw _ ⟨⟨a, ha⟩, rfl⟩
        obtain ⟨n, rfl⟩ := hψ w
        have hna := hconjA n hw a ha
        have hnfa := hconjA n hw (f a) (hfA a ha)
        rw [← hχconj n a ha hna, hF _ hna, hF a ha, ← hχconj n (f a) (hfA a ha) hnfa]
        congr 1
        exact Subtype.ext (hfW n hw a ha))
    refine ⟨c, fun a ha => ?_⟩
    have h1 := hc (χ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩
    rw [hF a ha, ← map_pow] at h1
    have h2 := congrArg Subtype.val (hχinj h1)
    simpa using h2

theorem ggNoInvariantLineSCrJ_of_irredSCrJ {p r : ℕ} (hp : p.Prime) {R : Type} [Group R]
    {I : Set (MulAut R)} (h : GGTorusIrredSCrJ p r R I) : GGNoInvariantLineSCrJ p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc hJ
  obtain ⟨W, hW1, hW2, -, -⟩ := h L' ψ hψ hker hperf A hA hAI hr h3 hsc hJ
  refine ⟨W, hW1, fun Λ hΛA hΛ => ?_⟩
  by_contra hcon
  push Not at hcon
  rcases hW2 Λ hΛA (fun n hn e he => hcon n hn e he) with h0 | h0
  · have h1 : Nat.card Λ = 1 := by rw [h0]; exact Subgroup.card_bot
    rw [h1] at hΛ
    exact hp.one_lt.ne hΛ
  · rw [h0] at hΛ
    have h4 : p ^ 3 ≤ p := hΛ ▸ h3
    have h5 : p ^ 1 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [pow_one] at h5
    omega

section Config

variable {G : Type} [Group G] [Finite G]

theorem ggTableBIrred_of_irredSCrJ {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type}
    [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hBsN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBs3 : ∀ b ∈ Bs, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hlift : GGTorusLift p r R) (hT : GGTorusIrredSCrJ p r R I) :
    GGTableBIrred Bs x L := by
  classical
  obtain ⟨hp, hBs, hxB, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma L hBsN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hBsN b, ggBeta_mem L θ hBsN hBs3 b, fun l => ggBeta_ggQuotHom L hBsN θ b l⟩
  obtain ⟨hr, h3'⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hBsN hlift
  obtain ⟨W, hW1, hW2, ⟨n₀, hn₀, a₀, ha₀, hna₀⟩, hW4⟩ := hT L (ggQuotHom θ)
    (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hL γ.range hA hAI hr h3'
    (ggTorusSelfCent_ggGamma hBsN hSC) (exists_fixed_nonsolvable_ggGamma hcfg hBsN)
  have hker : ∀ b : Bs, γ b = 1 ↔ (b : G) ∈ Subgroup.zpowers x := fun b => by
    rw [hγ, ggGamma_eq_one_iff, ← inf_centralizer_eq_zpowers_of_elemAbelian hp hBs hxB hS.2.2.1
      hS.2.2.2.1.1 hS.2.2.2.2]
    exact ⟨fun h => ⟨b.2, h⟩, fun h => h.2⟩
  have hWB : ∀ n ∈ W, ∀ b ∈ Bs, (n : G) * b * (n : G)⁻¹ ∈ Bs := by
    intro n hn b hb
    obtain ⟨htp, htA⟩ := hW1 n hn (γ ⟨b, hb⟩) ⟨⟨b, hb⟩, rfl⟩
    have htG : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) = n * b * (n : G)⁻¹ * b⁻¹ := by
      push_cast
      rw [hγ, ggGamma_coe]
      group
    have htC : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b' hb'
      have h1 := congrArg Subtype.val (htA (γ ⟨b', hb'⟩) ⟨⟨b', hb'⟩, rfl⟩)
      rw [hγ, ggGamma_coe] at h1
      calc b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G)
          = b' * ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b'⁻¹ * b' := by group
        _ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b' := by rw [h1]
    have htp' : ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) ^ p = 1 := by
      have := congrArg Subtype.val htp
      simpa using this
    have htB := hSC _ htC htp'
    have e : (n : G) * b * (n : G)⁻¹ = ((n * (γ ⟨b, hb⟩ n)⁻¹ : L) : G) * b := by
      rw [htG]
      group
    rw [e]
    exact Bs.mul_mem htB hb
  have hWN : ∀ n ∈ W, (n : G) ∈ L ⊓ Subgroup.normalizer (Bs : Set G) := by
    intro n hn
    refine ⟨n.2, ?_⟩
    have h := mem_normalizer_of_forall_conj_mem (W := Bs) (g := (n : G)⁻¹) (fun w hw => by
      simpa using hWB n hn w hw)
    simpa using Subgroup.inv_mem _ h
  have hconj : ∀ n ∈ W, ∀ b : Bs, ∃ hnb : (n : G) * b * (n : G)⁻¹ ∈ Bs,
      γ ⟨(n : G) * b * (n : G)⁻¹, hnb⟩ = MulAut.conj n * γ b * (MulAut.conj n)⁻¹ :=
    fun n hn b => ⟨hWB n hn b b.2, ggGamma_conj L hBsN n b (hWB n hn b b.2)⟩
  refine ⟨?_, ?_, ?_⟩
  ·
    intro S hxS hSB hSinv
    set A' : Subgroup (MulAut L) := (S.subgroupOf Bs).map γ with hA'
    have hA'A : A' ≤ γ.range := by
      rintro _ ⟨s, -, rfl⟩
      exact ⟨s, rfl⟩
    have hA'inv : ∀ n ∈ W, ∀ a ∈ A', MulAut.conj n * a * (MulAut.conj n)⁻¹ ∈ A' := by
      rintro n hn _ ⟨s, hs, rfl⟩
      obtain ⟨hns, he⟩ := hconj n hn s
      exact ⟨⟨_, hns⟩, Subgroup.mem_subgroupOf.mpr
        (hSinv n (hWN n hn) s (Subgroup.mem_subgroupOf.mp hs)), he⟩
    rcases hW2 A' hA'A hA'inv with h | h
    · left
      refine le_antisymm (fun s hs => ?_) hxS
      have h1 : γ ⟨s, hSB hs⟩ ∈ A' := ⟨⟨s, hSB hs⟩, Subgroup.mem_subgroupOf.mpr hs, rfl⟩
      rw [h, Subgroup.mem_bot] at h1
      exact (hker _).mp h1
    · right
      refine le_antisymm hSB (fun b hb => ?_)
      have h1 : γ ⟨b, hb⟩ ∈ A' := h ▸ ⟨⟨b, hb⟩, rfl⟩
      obtain ⟨s, hs, hsb⟩ := h1
      have h2 : γ (⟨b, hb⟩ * s⁻¹) = 1 := by rw [map_mul, map_inv, ← hsb, mul_inv_cancel]
      have h3 : (b : G) * (s : G)⁻¹ ∈ S := hxS ((hker _).mp h2)
      have e : b = (b * (s : G)⁻¹) * s := by group
      rw [e]
      exact S.mul_mem h3 (Subgroup.mem_subgroupOf.mp hs)
  ·
    obtain ⟨b, rfl⟩ := ha₀
    refine ⟨n₀, hWN n₀ hn₀, b, b.2, fun hcomm => hna₀ ?_⟩
    obtain ⟨hnb, he⟩ := hconj n₀ hn₀ b
    rw [← he]
    congr 1
    exact Subtype.ext (show (n₀ : G) * b * (n₀ : G)⁻¹ = b by rw [hcomm, mul_inv_cancel_right])
  ·
    intro H hHB hHinv hHsup hHinf φ hφH hφmul hφN
    have hH1 : ∀ h (hh : h ∈ H), γ ⟨h, hHB hh⟩ = 1 → h = 1 := by
      intro h hh h1
      have h2 : h ∈ H ⊓ Subgroup.zpowers x := ⟨hh, (hker _).mp h1⟩
      rw [hHinf] at h2
      exact Subgroup.mem_bot.mp h2
    have huniq : ∀ h (hh : h ∈ H) h' (hh' : h' ∈ H), γ ⟨h, hHB hh⟩ = γ ⟨h', hHB hh'⟩ →
        h = h' := by
      intro h hh h' hh' he
      have h1 : γ ⟨h * h'⁻¹, hHB (H.mul_mem hh (H.inv_mem hh'))⟩ = 1 := by
        have e : (⟨h * h'⁻¹, hHB (H.mul_mem hh (H.inv_mem hh'))⟩ : Bs) =
            ⟨h, hHB hh⟩ * (⟨h', hHB hh'⟩ : Bs)⁻¹ := rfl
        rw [e, map_mul, map_inv, he, mul_inv_cancel]
      have h2 := hH1 _ (H.mul_mem hh (H.inv_mem hh')) h1
      rw [mul_inv_eq_one] at h2
      exact h2
    have hex : ∀ a ∈ γ.range, ∃ h, ∃ hh : h ∈ H, γ ⟨h, hHB hh⟩ = a := by
      rintro _ ⟨b, rfl⟩
      have hxH : ∀ h ∈ H, x * h = h * x := fun h hh =>
        mul_comm_of_isElemAbelian hBs hxB (hHB hh)
      have hbsup : (b : G) ∈ H ⊔ Subgroup.zpowers x := by
        rw [hHsup]
        exact b.2
      obtain ⟨h, hh, j, hj⟩ := exists_mem_mul_pow_of_mem_sup hxH hbsup
      refine ⟨h, hh, ?_⟩
      have e : b = ⟨h, hHB hh⟩ * (⟨x, hxB⟩ : Bs) ^ j := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_pow]
        exact hj)
      have hx1 : γ ⟨x, hxB⟩ = 1 := (hker _).mpr (Subgroup.mem_zpowers x)
      rw [e, map_mul, map_pow, hx1, one_pow, mul_one]
    let f : MulAut L → MulAut L := fun a =>
      if ha : ∃ h, ∃ hh : h ∈ H, γ ⟨h, hHB hh⟩ = a then
        γ ⟨φ ha.choose, hHB (hφH _ ha.choose_spec.choose)⟩
      else a
    have hf : ∀ h (hh : h ∈ H), f (γ ⟨h, hHB hh⟩) = γ ⟨φ h, hHB (hφH h hh)⟩ := by
      intro h hh
      have hex' : ∃ h', ∃ hh' : h' ∈ H, γ ⟨h', hHB hh'⟩ = γ ⟨h, hHB hh⟩ := ⟨h, hh, rfl⟩
      have heq : hex'.choose = h :=
        huniq _ hex'.choose_spec.choose _ hh hex'.choose_spec.choose_spec
      change (if ha : ∃ h', ∃ hh' : h' ∈ H, γ ⟨h', hHB hh'⟩ = γ ⟨h, hHB hh⟩ then
        γ ⟨φ ha.choose, hHB (hφH _ ha.choose_spec.choose)⟩ else γ ⟨h, hHB hh⟩) = _
      rw [dite_eq_left hex']
      congr 1
      exact Subtype.ext (congrArg φ heq)
    obtain ⟨c, hc⟩ := hW4 f
      (by
        intro a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        rw [hf h hh]
        exact ⟨_, rfl⟩)
      (by
        intro a ha b hb
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨h', hh', rfl⟩ := hex b hb
        have e : γ ⟨h, hHB hh⟩ * γ ⟨h', hHB hh'⟩ = γ ⟨h * h', hHB (H.mul_mem hh hh')⟩ := by
          rw [← map_mul]
          rfl
        rw [e, hf _ (H.mul_mem hh hh'), hf h hh, hf h' hh', ← map_mul]
        congr 1
        exact Subtype.ext (hφmul h hh h' hh'))
      (by
        intro n hn a ha
        obtain ⟨h, hh, rfl⟩ := hex a ha
        obtain ⟨hnh, he⟩ := hconj n hn ⟨h, hHB hh⟩
        have hnhH : (n : G) * h * (n : G)⁻¹ ∈ H := hHinv n (hWN n hn) h hh
        obtain ⟨hnφ, he'⟩ := hconj n hn ⟨φ h, hHB (hφH h hh)⟩
        have e1 : γ ⟨(n : G) * h * (n : G)⁻¹, hnh⟩ = γ ⟨(n : G) * h * (n : G)⁻¹, hHB hnhH⟩ :=
          rfl
        rw [← he, e1, hf _ hnhH, hf h hh, ← he']
        congr 1
        exact Subtype.ext (hφN n (hWN n hn) h hh))
    refine ⟨c, fun h hh => ?_⟩
    have h1 := hc _ ⟨⟨h, hHB hh⟩, rfl⟩
    rw [hf h hh, ← map_pow] at h1
    have hhc : h ^ c ∈ H := H.pow_mem hh c
    have e : ((⟨h, hHB hh⟩ : Bs) ^ c) = ⟨h ^ c, hHB hhc⟩ := rfl
    rw [e] at h1
    exact huniq _ (hφH h hh) _ hhc h1

theorem not_normalizer_le_of_noInvariantLineSCrJ {p r : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hcfg : GGConfig p B Bs x L D J) (hL : commutator L = ⊤) {R : Type}
    [Group R] (θ : L ⧸ Subgroup.center L ≃* R) {I : Set (MulAut R)}
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut L θ ⟨b, hN hb⟩ ∈ I)
    (hlift : GGTorusLift p r R) (hT : GGNoInvariantLineSCrJ p r R I) {E : Subgroup G}
    (hEBs : E ≤ Bs) (hxE : x ∈ E) (hE : Nat.card E = p ^ 2) :
    ¬ Subgroup.normalizer (Bs : Set G) ≤ Subgroup.normalizer (E : Set G) := by
  classical
  intro hNE
  obtain ⟨hp, hBs, hxBs, hLx, -⟩ := hcfg.tableB_facts
  have := Fact.mk hp
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hcfg.2.1.2.2.2
  set γ := ggGamma L hN with hγ
  have hBp : ∀ b : Bs, b ^ p = 1 := fun b => Subtype.ext (by simpa using hBs.2 b b.2)
  have hBc : ∀ a b : Bs, a * b = b * a := fun a b =>
    Subtype.ext (IsElemAbelian.comm hBs a.2 b.2)
  have hA : IsElemAbelian p γ.range := isElemAbelian_range hBc hBp γ
  have hAI : ∀ a ∈ γ.range, ∃ φ ∈ I, ∀ l : L, φ (ggQuotHom θ l) = ggQuotHom θ (a l) := by
    rintro _ ⟨b, rfl⟩
    exact ⟨ggBeta L θ hN b, hBsI b b.2, fun l => ggBeta_ggQuotHom L hN θ b l⟩
  obtain ⟨hr, h3⟩ := card_range_ggGamma_bstar_ge hcfg hL θ hN hlift
  obtain ⟨W, hW1, hW2⟩ := hT L (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom])
    hL γ.range hA hAI hr h3 (ggTorusSelfCent_ggGamma hN hSC)
    (exists_fixed_nonsolvable_ggGamma hcfg hN)
  set EB : Subgroup Bs := E.subgroupOf Bs with hEB
  set Λ : Subgroup (MulAut L) := EB.map γ with hΛ
  have hΛA : Λ ≤ γ.range := Subgroup.map_le_range _ _
  have hEA : IsElemAbelian p E := isElemAbelian_mono hBs hEBs
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEBs.trans hN
  have hcE := card_range_ggGamma_mul_of hp hEA hxE hS.2.2.1 hLx hS.2.2.2.2 hEN
  have hΛE : Λ = ((ggGamma L hEN).range) := by
    ext a
    constructor
    · rintro ⟨⟨b, hb⟩, hbE, rfl⟩
      exact ⟨⟨b, Subgroup.mem_subgroupOf.mp hbE⟩, rfl⟩
    · rintro ⟨⟨b, hb⟩, rfl⟩
      exact ⟨⟨b, hEBs hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩
  have hΛcard : Nat.card Λ = p := by
    rw [hΛE]
    rw [hE, pow_two] at hcE
    exact Nat.eq_of_mul_eq_mul_right hp.pos hcE
  obtain ⟨n, hnW, e, he, hne⟩ := hW2 Λ hΛA hΛcard
  apply hne
  obtain ⟨⟨b, hbBs⟩, hbE, rfl⟩ := he
  have hbE' : b ∈ E := Subgroup.mem_subgroupOf.mp hbE
  have hnN := mem_normalizer_of_weyl hN hSC (hW1 n hnW)
  have hnb : (n : G) * b * (n : G)⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp (hNE hnN) b).mp hbE'
  have hnbBs : (n : G) * b * (n : G)⁻¹ ∈ Bs := hEBs hnb
  refine ⟨⟨_, hnbBs⟩, Subgroup.mem_subgroupOf.mpr hnb, ?_⟩
  exact ggGamma_conj L hN n ⟨b, hbBs⟩ hnbBs

end Config

theorem ggTableBIrredInputOn_of_labelsSCrJ {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGTorusIrredSCrJ p r R I) :
    GGTableBIrredInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, -, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, hBs3⟩, r, hlift, hirr⟩ :=
    largeEvenRawDatum_exists hraw
  exact ggTableBIrred_of_irredSCrJ hcfg hL θ hBsN hBs3 hlift hirr

theorem ggLNoInvariantLineInputOn_of_labelsSCrJ {S : ℕ → LargeEvenLabel → Prop}
    (h : ∀ (p : ℕ) (lab : LargeEvenLabel), p.Prime → LargeEvenInLambda2 lab → S p lab →
      LargeEvenLabelAll lab fun R _ I _ => ∃ r, GGTorusLift p r R ∧ GGNoInvariantLineSCrJ p r R I) :
    GGLNoInvariantLineInputOn S := by
  intro G _ _ p B Bs x L D J hcfg hM E hEBs hxE hE
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  obtain ⟨hL, lab, hlab, hraw⟩ := largeEvenMarking_and_labelAll (S := fun lab => S p lab)
    (fun lab hlab hs => h p lab hp hlab hs) (fun _ _ _ _ _ _ hP => hP.1) hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨-, -, hBsN, h3⟩, r, hlift, hT⟩ := largeEvenRawDatum_exists hraw
  exact not_normalizer_le_of_noInvariantLineSCrJ hcfg hL θ hBsN
    (fun b hb => ggLAut_mem_of_induces L θ hBsN h3 hb) hlift hT hEBs hxE hE

end TableBF4TwoTB

end CFSG.StandardType

end
