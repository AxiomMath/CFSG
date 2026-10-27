module

public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBE7E8
public import CFSG.LocalAnalysis.StandardType.GGTableBTwE6TBIrred
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLineE7
public import CFSG.LocalAnalysis.StandardType.GGTableBExcSplitLLine
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwo
public import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOpenTableBMoreElt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley TableB TableBSymp

namespace TableBExcTwoTB

theorem ggTorusIrredSCr_of_secEltSC {r : ℕ} {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    (hcp : GGCenterPrime 3 R)
    (h : ∀ E : Subgroup R, IsElemAbelian 3 E → 3 ^ r ≤ Nat.card E → 3 ^ 3 ≤ Nat.card E →
      (∀ g : R, g ^ 3 = 1 → (∀ e ∈ E, g * e = e * g) → g ∈ E) → E6TwoTB.SecEltAt 3 E) :
    TwE6TB.GGTorusIrredSCr 3 r R I := by
  classical
  have := Fact.mk Nat.prime_three
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 hsc
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

section Labels


theorem recipeID_subset_inn_two (τ : Tag) {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) :
    TableBExc.RecipeID τ K ⊆
      Set.range (MulAut.conj : TableBExc.RecipeGroup τ K →* MulAut (TableBExc.RecipeGroup τ K)) :=
  TableBExc.idImage_subset_inn_of_top τ K (eq_top_iff.mpr fun a _ => by
    rw [show a = 1 from funext fun i => TableBExc.E6Three.eq_one_of_card_two hK (a i)]
    exact one_mem _)

theorem ggTorusIrredSCr_E7_two {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hE7 : GGE7TwoSCToral K) :
    TwE6TB.GGTorusIrredSCr 3 6 (TableBExc.RecipeGroup .E7 K) (TableBExc.RecipeID .E7 K) := by
  refine ggTorusIrredSCr_of_secEltSC (recipeID_subset_inn_two .E7 hK)
    (TableBExc.center_recipeGroup_eq_bot .E7 K) ?_ ?_
  · exact ExcSplitL.ggCenterPrime_recipe_E7 (K := K) (f := 1) le_rfl (by rw [hK]; norm_num)
      Nat.prime_three (by norm_num)
  · intro E hE hr _ hsc
    have hE' : IsElemAbelian 3 (E.map (TableBExc.recipeEquiv .E7 K).toMonoidHom) :=
      TableB.isElemAbelian_map hE _
    have hcard : Nat.card (E.map (TableBExc.recipeEquiv .E7 K).toMonoidHom) = Nat.card E :=
      (Nat.card_congr
        (E.equivMapOfInjective _ (TableBExc.recipeEquiv .E7 K).injective).toEquiv).symm
    obtain ⟨c, hc⟩ := hE7 _ hE' (hcard ▸ hr)
      (selfCent_map (TableBExc.recipeEquiv .E7 K) hsc)
    have hS : E6TwoTB.SecEltAt 3 (E.map (TableBExc.recipeEquiv .E7 K).toMonoidHom) := by
      rw [hc]
      exact secEltAt_map_conj (secEltAt_E7 hK) c
    exact E6TwoTB.SecEltAt.of_map (TableBExc.recipeEquiv .E7 K) hS

theorem ggTorusIrredSCr_E8_two {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    (hE8 : GGE8TwoSCToral K) :
    TwE6TB.GGTorusIrredSCr 3 7 (TableBExc.RecipeGroup .E8 K) (TableBExc.RecipeID .E8 K) := by
  refine ggTorusIrredSCr_of_secEltSC (recipeID_subset_inn_two .E8 hK)
    (TableBExc.center_recipeGroup_eq_bot .E8 K) ?_ ?_
  · exact ExcSplitL.ggCenterPrime_recipe_E8 (K := K) Nat.prime_three (by norm_num)
  · intro E hE hr _ hsc
    have hE' : IsElemAbelian 3 (E.map (TableBExc.recipeEquiv .E8 K).toMonoidHom) :=
      TableB.isElemAbelian_map hE _
    have hcard : Nat.card (E.map (TableBExc.recipeEquiv .E8 K).toMonoidHom) = Nat.card E :=
      (Nat.card_congr
        (E.equivMapOfInjective _ (TableBExc.recipeEquiv .E8 K).injective).toEquiv).symm
    obtain ⟨c, hc⟩ := hE8 _ hE' (hcard ▸ hr)
      (selfCent_map (TableBExc.recipeEquiv .E8 K) hsc)
    have hS : E6TwoTB.SecEltAt 3 (E.map (TableBExc.recipeEquiv .E8 K).toMonoidHom) := by
      rw [hc]
      exact secEltAt_map_conj (secEltAt_E8 hK) c
    exact E6TwoTB.SecEltAt.of_map (TableBExc.recipeEquiv .E8 K) hS

end Labels

end TableBExcTwoTB

end CFSG.StandardType

end
