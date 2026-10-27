module

public import CFSG.LocalAnalysis.ComponentInitial.RootDiagonalConjugation

public section

namespace CFSG.HardMathSupport.C14Torus

open CFSG.Blueprint.Chevalley CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem rootChar_single {τ : Tag} {K : Type} [Field K] (t : Fin τ.rank → Kˣ) (i : Fin τ.rank) :
    rootChar t (Pi.single i 1) = t i := by
  rw [rootChar, Finset.prod_eq_single i (fun j _ hj => by simp [hj])
    (fun h => absurd (Finset.mem_univ i) h)]
  simp

theorem rootChar_mul_left {τ : Tag} {K : Type} [Field K] (s t : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar (s * t) v = rootChar s v * rootChar t v := by
  simp only [rootChar, Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib]

theorem rootChar_one_left {τ : Tag} {K : Type} [Field K] (v : Fin τ.rank → ℤ) : rootChar (1 : Fin τ.rank → Kˣ) v = 1 := by
  simp [rootChar]

theorem rootChar_inv_left {τ : Tag} {K : Type} [Field K] (t : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar t⁻¹ v = (rootChar t v)⁻¹ := by
  simp only [rootChar, Pi.inv_apply, inv_zpow, Finset.prod_inv_distrib]

theorem rootChar_zpow_left {τ : Tag} {K : Type} [Field K] (t : Fin τ.rank → Kˣ) (n : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar (t ^ n) v = rootChar t v ^ n := by
  simp only [rootChar, Pi.pow_apply, ← zpow_mul]
  rw [← Finset.prod_zpow]
  exact Finset.prod_congr rfl fun i _ => by rw [← zpow_mul, mul_comm]

theorem rootChar_pow_left {τ : Tag} {K : Type} [Field K] (t : Fin τ.rank → Kˣ) (n : ℕ) (v : Fin τ.rank → ℤ) :
    rootChar (t ^ n) v = rootChar t v ^ n := by
  have := rootChar_zpow_left t n v
  simpa using this

theorem rootChar_zsmul {τ : Tag} {K : Type} [Field K] (t : Fin τ.rank → Kˣ) (n : ℤ) (v : Fin τ.rank → ℤ) :
    rootChar t (n • v) = rootChar t v ^ n := by
  simp only [rootChar, Pi.smul_apply, smul_eq_mul, ← Finset.prod_zpow, ← zpow_mul]
  exact Finset.prod_congr rfl fun i _ => by rw [mul_comm]

theorem rootChar_neg {τ : Tag} {K : Type} [Field K] (t : Fin τ.rank → Kˣ) (v : Fin τ.rank → ℤ) :
    rootChar t (-v) = (rootChar t v)⁻¹ := by
  have := rootChar_zsmul t (-1) v
  simpa using this

theorem ext_rootChar {τ : Tag} {K : Type} [Field K] {s t : Fin τ.rank → Kˣ} (h : ∀ i, rootChar s (Pi.single i 1) =
    rootChar t (Pi.single i 1)) : s = t :=
  funext fun i => by rw [← rootChar_single s i, ← rootChar_single t i, h i]

@[expose] def tmap {τ : Tag} {K : Type} [Field K] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (t : Fin τ.rank → Kˣ) :
    Fin τ.rank → Kˣ :=
  fun i => rootChar t fun j => M j i

theorem rootChar_tmap {τ : Tag} {K : Type} [Field K] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (t : Fin τ.rank → Kˣ)
    (v : Fin τ.rank → ℤ) : rootChar (tmap M t) v = rootChar t (M *ᵥ v) := by
  simp only [rootChar, tmap, Matrix.mulVec, dotProduct, ← Finset.prod_zpow, ← zpow_mul,
    ← Finset.prod_zpow_eq_zpow_sum]
  rw [Finset.prod_comm]

theorem tmap_tmap {τ : Tag} {K : Type} [Field K] (M M' : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (t : Fin τ.rank → Kˣ) :
    tmap M (tmap M' t) = tmap (M' * M) t := by
  funext i
  simp only [tmap]
  rw [rootChar_tmap]
  congr 1

theorem tmap_mul {τ : Tag} {K : Type} [Field K] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (s t : Fin τ.rank → Kˣ) :
    tmap M (s * t) = tmap M s * tmap M t := by
  funext i; simp only [tmap, Pi.mul_apply, rootChar_mul_left]

theorem tmap_one {τ : Tag} {K : Type} [Field K] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) :
    tmap M (1 : Fin τ.rank → Kˣ) = 1 := by
  funext i; simp only [tmap, rootChar_one_left, Pi.one_apply]

theorem tmap_inv {τ : Tag} {K : Type} [Field K] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (t : Fin τ.rank → Kˣ) :
    tmap M t⁻¹ = (tmap M t)⁻¹ := by
  funext i; simp only [tmap, Pi.inv_apply, rootChar_inv_left]

theorem tmap_pow {τ : Tag} {K : Type} [Field K] (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (t : Fin τ.rank → Kˣ) (n : ℕ) :
    tmap M (t ^ n) = tmap M t ^ n := by
  funext i; simp only [tmap, Pi.pow_apply, rootChar_pow_left]

theorem tmap_smul_one {τ : Tag} {K : Type} [Field K] (c : ℤ) (t : Fin τ.rank → Kˣ) :
    tmap (c • (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)) t = t ^ c := by
  refine ext_rootChar fun i => ?_
  rw [rootChar_tmap, rootChar_zpow_left, ← rootChar_zsmul, Matrix.smul_mulVec, Matrix.one_mulVec]

theorem tmap_sub {τ : Tag} {K : Type} [Field K] (M M' : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (t : Fin τ.rank → Kˣ) :
    tmap (M - M') t = tmap M t * (tmap M' t)⁻¹ := by
  refine ext_rootChar fun i => ?_
  rw [rootChar_tmap, rootChar_mul_left, rootChar_inv_left, rootChar_tmap, rootChar_tmap,
    Matrix.sub_mulVec, CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_sub]

@[expose] def zp {τ : Tag} {K : Type} [Field K] (p : ℕ) (N : AddSubgroup (Fin τ.rank → ℤ)) : Subgroup (Fin τ.rank → Kˣ) where
  carrier := {t | (∀ α ∈ N, rootChar t α = 1) ∧ ∃ n : ℕ, t ^ p ^ n = 1}
  mul_mem' := by
    rintro s t ⟨hs, m, hm⟩ ⟨ht, n, hn⟩
    refine ⟨fun α hα => by rw [rootChar_mul_left, hs α hα, ht α hα, one_mul], m + n, ?_⟩
    rw [mul_pow, pow_add, pow_mul, hm, one_pow, one_mul, mul_comm (p ^ m), pow_mul, hn, one_pow]
  one_mem' := ⟨fun α _ => rootChar_one_left α, 0, by simp⟩
  inv_mem' := by
    rintro t ⟨ht, n, hn⟩
    exact ⟨fun α hα => by rw [rootChar_inv_left, ht α hα, inv_one], n, by rw [inv_pow, hn, inv_one]⟩

theorem mem_zp {τ : Tag} {K : Type} [Field K] {p : ℕ} {N : AddSubgroup (Fin τ.rank → ℤ)} {t : Fin τ.rank → Kˣ} :
    t ∈ zp p N ↔ (∀ α ∈ N, rootChar t α = 1) ∧ ∃ n : ℕ, t ^ p ^ n = 1 := Iff.rfl

theorem exists_zmod_extension {r p : ℕ} [Fact p.Prime] (N : AddSubgroup (Fin r → ℤ))
    (hsat : ∀ v, p • v ∈ N → v ∈ N) (hN : N →+ ZMod p) :
    ∃ g : (Fin r → ZMod p) →ₗ[ZMod p] ZMod p,
      ∀ α : N, g (fun i => (((α : Fin r → ℤ) i : ℤ) : ZMod p)) = hN α := by
  classical
  set red : (Fin r → ℤ) →+ (Fin r → ZMod p) :=
    AddMonoidHom.compLeft (Int.castAddHom (ZMod p)) (Fin r) with hred
  set f : N →+ (Fin r → ZMod p) := red.comp N.subtype with hf
  have hfα : ∀ α : N, f α = fun i => (((α : Fin r → ℤ) i : ℤ) : ZMod p) := fun α => rfl
  have hker : f.ker ≤ hN.ker := by
    intro α hα
    rw [AddMonoidHom.mem_ker] at hα ⊢
    have hdiv : ∀ i, (p : ℤ) ∣ (α : Fin r → ℤ) i := fun i => by
      have := congrFun hα i
      rw [hfα] at this
      exact (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1 this
    choose w hw using hdiv
    have hαw : (α : Fin r → ℤ) = p • w := funext fun i => by
      rw [Pi.smul_apply, hw i, nsmul_eq_mul]
    have hwN : w ∈ N := hsat w (hαw ▸ α.2)
    have : α = p • (⟨w, hwN⟩ : N) := Subtype.ext (by rw [hαw]; rfl)
    rw [this, map_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul]
  have hsurj : Function.Surjective f.rangeRestrict := f.rangeRestrict_surjective
  have hker' : f.rangeRestrict.ker ≤ hN.ker := by
    intro α hα
    apply hker
    rw [AddMonoidHom.mem_ker] at hα ⊢
    have := congrArg Subtype.val hα
    simpa using this
  obtain ⟨g₀, hg₀⟩ : ∃ g₀ : f.range →+ ZMod p, ∀ α : N, g₀ (f.rangeRestrict α) = hN α :=
    ⟨f.rangeRestrict.liftOfRightInverse (Function.surjInv hsurj)
      (Function.rightInverse_surjInv hsurj) ⟨hN, hker'⟩, fun α =>
      AddMonoidHom.liftOfRightInverse_comp_apply f.rangeRestrict
        (Function.surjInv hsurj) (Function.rightInverse_surjInv hsurj) ⟨hN, hker'⟩ α⟩
  let W : Submodule (ZMod p) (Fin r → ZMod p) :=
    { carrier := f.range
      add_mem' := fun ha hb => f.range.add_mem ha hb
      zero_mem' := f.range.zero_mem
      smul_mem' := fun c x hx => by
        have e : c • x = c.val • x := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
        rw [e]
        exact f.range.nsmul_mem hx _ }
  have hmemW : ∀ x, x ∈ W ↔ x ∈ f.range := fun x => Iff.rfl
  let ι : W →+ f.range :=
    { toFun := fun w => ⟨w.1, (hmemW w.1).1 w.2⟩, map_zero' := rfl, map_add' := fun _ _ => rfl }
  let φ : W →ₗ[ZMod p] ZMod p :=
    { toFun := fun w => g₀ (ι w)
      map_add' := fun a b => by rw [map_add, map_add]
      map_smul' := fun c w => by
        have e : c • w = c.val • w := by
          rw [← Nat.cast_smul_eq_nsmul (ZMod p), ZMod.natCast_zmod_val]
        rw [e, map_nsmul, map_nsmul, RingHom.id_apply, nsmul_eq_mul, ZMod.natCast_zmod_val,
          smul_eq_mul] }
  obtain ⟨g, hg⟩ := LinearMap.exists_extend φ
  refine ⟨g, fun α => ?_⟩
  have hW' : f α ∈ W := (hmemW _).2 ⟨α, rfl⟩
  have := congrArg (fun ψ => ψ ⟨f α, hW'⟩) hg
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at this
  rw [← hfα, this, ← hg₀ α]
  rfl

theorem zp_exists_pow_p_eq {τ : Tag} {K : Type} [Field K] [IsAlgClosed K] {p : ℕ} [hpF : Fact p.Prime] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) {N : AddSubgroup (Fin τ.rank → ℤ)}
    (hsat : ∀ v, p • v ∈ N → v ∈ N) {s : Fin τ.rank → Kˣ} (hs : s ∈ zp p N) :
    ∃ u ∈ zp p N, u ^ p = s := by
  classical
  have hp := hpF.out
  obtain ⟨hsN, n, hn⟩ := hs
  have hroot : ∀ i, ∃ z : Kˣ, z ^ p = s i := fun i => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq (s i : K) hp.pos
    have hz0 : z ≠ 0 := fun h => (s i).ne_zero (by rw [← hz, h, zero_pow hp.ne_zero])
    exact ⟨Units.mk0 z hz0, Units.ext (by simp [hz])⟩
  choose u₀ hu₀ using hroot
  have hu₀p : u₀ ^ p = s := funext hu₀
  have hmem : ∀ α ∈ N, rootChar u₀ α ∈ Subgroup.zpowers ζ := fun α hα => by
    rw [hζ.zpowers_eq, mem_rootsOfUnity, ← rootChar_pow_left, hu₀p, hsN α hα]
  let h₀ : N →+ Additive (Subgroup.zpowers ζ) :=
    { toFun := fun α => Additive.ofMul ⟨rootChar u₀ α, hmem α α.2⟩
      map_zero' := by
        apply Additive.toMul.injective
        exact Subtype.ext (by simp [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_zero])
      map_add' := fun α β => by
        apply Additive.toMul.injective
        exact Subtype.ext (by
          simp [CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley.rootChar_add]) }
  let hN : N →+ ZMod p := hζ.zmodEquivZPowers.symm.toAddMonoidHom.comp h₀
  have hhN : ∀ α : N, ζ ^ ((hN α).val) = rootChar u₀ α := fun α => by
    have e1 := hζ.zmodEquivZPowers_apply_coe_nat ((hN α).val)
    rw [ZMod.natCast_zmod_val] at e1
    have e2 : hζ.zmodEquivZPowers (hN α) = h₀ α := by
      simp [hN]
    rw [e2] at e1
    have := congrArg (fun x => ((Additive.toMul x : Subgroup.zpowers ζ) : Kˣ)) e1
    simpa [h₀] using this.symm
  obtain ⟨g, hgf⟩ := exists_zmod_extension N hsat hN
  let v : Fin τ.rank → Kˣ := fun i => ζ ^ (g (Pi.single i 1)).val
  have key : ∀ a b : ℤ, (a : ZMod p) = b → ζ ^ a = ζ ^ b := fun a b hab => by
    rw [ZMod.intCast_eq_intCast_iff_dvd_sub] at hab
    have h1 : ζ ^ (b - a) = 1 := (hζ.zpow_eq_one_iff_dvd _).2 hab
    rw [zpow_sub, mul_inv_eq_one] at h1
    exact h1.symm
  have hvα : ∀ α : N, rootChar v α = rootChar u₀ α := fun α => by
    rw [← hhN α]
    have hsum : (hN α : ZMod p) = ∑ i, ((α : Fin τ.rank → ℤ) i : ZMod p) * g (Pi.single i 1) := by
      rw [← hgf α]
      have e : (fun i => (((α : Fin τ.rank → ℤ) i : ℤ) : ZMod p)) =
          ∑ i, ((α : Fin τ.rank → ℤ) i : ZMod p) • (Pi.single i 1 : Fin τ.rank → ZMod p) := by
        funext j
        simp [Finset.sum_apply, Pi.single_apply]
      rw [e, map_sum]
      exact Finset.sum_congr rfl fun i _ => by rw [map_smul, smul_eq_mul]
    have e1 : rootChar v α =
        ζ ^ (∑ i, ((g (Pi.single i 1)).val : ℤ) * (α : Fin τ.rank → ℤ) i) := by
      simp only [rootChar, v, ← zpow_natCast, ← zpow_mul, Finset.prod_zpow_eq_zpow_sum]
    rw [e1, ← zpow_natCast]
    apply key
    rw [hsum]
    push_cast
    simp only [ZMod.natCast_val, ZMod.cast_id', id_eq]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hvp : v ^ p = 1 := funext fun i => by
    simp only [v, Pi.pow_apply, Pi.one_apply]
    rw [← pow_mul, mul_comm, pow_mul, hζ.pow_eq_one, one_pow]
  have hup : (u₀ * v⁻¹) ^ p = s := by rw [mul_pow, inv_pow, hu₀p, hvp, inv_one, mul_one]
  refine ⟨u₀ * v⁻¹, ⟨fun α hα => ?_, n + 1, ?_⟩, hup⟩
  · rw [rootChar_mul_left, rootChar_inv_left, hvα ⟨α, hα⟩, mul_inv_cancel]
  · rw [pow_succ', pow_mul, hup, hn]

theorem zp_exists_pow_ppow_eq {τ : Tag} {K : Type} [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) {N : AddSubgroup (Fin τ.rank → ℤ)}
    (hsat : ∀ v, p • v ∈ N → v ∈ N) (k : ℕ) {s : Fin τ.rank → Kˣ} (hs : s ∈ zp p N) :
    ∃ u ∈ zp p N, u ^ p ^ k = s := by
  induction k generalizing s with
  | zero => exact ⟨s, hs, by simp⟩
  | succ k ih =>
    obtain ⟨u, hu, rfl⟩ := ih hs
    obtain ⟨v, hv, rfl⟩ := zp_exists_pow_p_eq hζ hsat hu
    exact ⟨v, hv, by rw [pow_succ', pow_mul]⟩

theorem zp_exists_pow_coprime_eq {τ : Tag} {K : Type} [Field K] {p : ℕ} [hpF : Fact p.Prime] {N : AddSubgroup (Fin τ.rank → ℤ)}
    {m : ℕ} (hm : Nat.Coprime m p) {s : Fin τ.rank → Kˣ} (hs : s ∈ zp p N) :
    ∃ u ∈ zp p N, u ^ m = s := by
  obtain ⟨-, n, hn⟩ := id hs
  have hcop : Nat.Coprime m (p ^ n) := Nat.Coprime.pow_right n hm
  haveI : NeZero (p ^ n) := ⟨pow_ne_zero n hpF.out.ne_zero⟩
  obtain ⟨m', hm'⟩ : ∃ m' : ℕ, m * m' ≡ 1 [MOD p ^ n] := by
    refine ⟨(((m : ZMod (p ^ n))⁻¹ : ZMod (p ^ n))).val, ?_⟩
    rw [← ZMod.natCast_eq_natCast_iff]
    push_cast
    rw [ZMod.natCast_zmod_val]
    exact ZMod.coe_mul_inv_eq_one m hcop
  refine ⟨s ^ m', (zp p N).pow_mem hs m', ?_⟩
  rw [← pow_mul]
  conv_rhs => rw [← pow_one s]
  exact (pow_eq_pow_iff_modEq).2 (Nat.ModEq.of_dvd (orderOf_dvd_of_pow_eq_one hn) (by rwa [mul_comm] at hm'))

theorem zp_exists_zpow_eq {τ : Tag} {K : Type} [Field K] [IsAlgClosed K] {p : ℕ} [hpF : Fact p.Prime] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) {N : AddSubgroup (Fin τ.rank → ℤ)}
    (hsat : ∀ v, p • v ∈ N → v ∈ N) {c : ℤ} (hc : c ≠ 0) {s : Fin τ.rank → Kˣ}
    (hs : s ∈ zp p N) : ∃ u ∈ zp p N, u ^ c = s := by
  have hnat : ∀ d : ℕ, d ≠ 0 → ∀ s ∈ (zp p N : Subgroup (Fin τ.rank → Kˣ)),
      ∃ u ∈ (zp p N : Subgroup (Fin τ.rank → Kˣ)), u ^ d = s := by
    intro d hd s hs
    obtain ⟨k, m, hpm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hd p hpF.out.one_lt.ne'
    obtain ⟨t, ht, rfl⟩ := zp_exists_pow_coprime_eq (N := N)
      ((Nat.coprime_comm.1 ((Nat.Prime.coprime_iff_not_dvd hpF.out).2 hpm))) hs
    obtain ⟨u, hu, rfl⟩ := zp_exists_pow_ppow_eq hζ hsat k ht
    exact ⟨u, hu, by rw [pow_mul]⟩
  obtain ⟨n, rfl | rfl⟩ := Int.eq_nat_or_neg c
  · obtain ⟨u, hu, rfl⟩ := hnat n (by exact_mod_cast hc) s hs
    exact ⟨u, hu, zpow_natCast u n⟩
  · obtain ⟨u, hu, rfl⟩ := hnat n (by simpa using hc) s hs
    exact ⟨u⁻¹, (zp p N).inv_mem hu, by rw [zpow_neg, zpow_natCast, inv_pow, inv_inv]⟩

theorem tmap_mem_zp {τ : Tag} {K : Type} [Field K] {p : ℕ} {N : AddSubgroup (Fin τ.rank → ℤ)}
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (hM : ∀ α ∈ N, M *ᵥ α ∈ N)
    {t : Fin τ.rank → Kˣ} (ht : t ∈ zp p N) : tmap M t ∈ zp p N := by
  obtain ⟨h1, n, hn⟩ := ht
  exact ⟨fun α hα => by rw [rootChar_tmap]; exact h1 _ (hM α hα), n,
    by rw [← tmap_pow, hn, tmap_one]⟩

theorem pow_mulVec_mem {r : ℕ} {N : AddSubgroup (Fin r → ℤ)} (B : Matrix (Fin r) (Fin r) ℤ)
    (hB : ∀ α ∈ N, B *ᵥ α ∈ N) (n : ℕ) : ∀ α ∈ N, (B ^ n) *ᵥ α ∈ N := by
  induction n with
  | zero => intro α hα; rwa [pow_zero, Matrix.one_mulVec]
  | succ n ih => intro α hα; rw [pow_succ, ← Matrix.mulVec_mulVec]; exact ih _ (hB α hα)

theorem aeval_mulVec_mem {r : ℕ} {N : AddSubgroup (Fin r → ℤ)} (B : Matrix (Fin r) (Fin r) ℤ)
    (hB : ∀ α ∈ N, B *ᵥ α ∈ N) (P : Polynomial ℤ) : ∀ α ∈ N, (Polynomial.aeval B P) *ᵥ α ∈ N := by
  induction P using Polynomial.induction_on' with
  | add P P' hP hP' =>
    intro α hα; rw [map_add, Matrix.add_mulVec]; exact N.add_mem (hP α hα) (hP' α hα)
  | monomial n c =>
    intro α hα
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      Matrix.smul_mulVec]
    exact N.zsmul_mem (pow_mulVec_mem B hB n α hα) c

theorem exists_ch_inverse {r : ℕ} {N : AddSubgroup (Fin r → ℤ)} (B : Matrix (Fin r) (Fin r) ℤ)
    (hB : ∀ α ∈ N, B *ᵥ α ∈ N) (hdet : B.det ≠ 0) :
    ∃ (C : Matrix (Fin r) (Fin r) ℤ) (c : ℤ), c ≠ 0 ∧ C * B = c • (1 : Matrix _ _ ℤ) ∧
      ∀ α ∈ N, C *ᵥ α ∈ N := by
  set P := B.charpoly
  have hP : Polynomial.aeval B P = 0 := Matrix.aeval_self_charpoly B
  have hsplit := Polynomial.X_mul_divX_add P
  refine ⟨-Polynomial.aeval B P.divX, P.coeff 0, ?_, ?_, ?_⟩
  · intro h0
    apply hdet
    rw [Matrix.det_eq_sign_charpoly_coeff, h0, mul_zero]
  · have := congrArg (Polynomial.aeval B) hsplit
    rw [hP, map_add, Polynomial.aeval_C, mul_comm, map_mul, Polynomial.aeval_X,
      Algebra.algebraMap_eq_smul_one] at this
    rw [neg_mul, neg_eq_iff_eq_neg, ← sub_eq_zero, sub_neg_eq_add]
    exact this
  · intro α hα
    rw [Matrix.neg_mulVec]
    exact N.neg_mem (aeval_mulVec_mem B hB _ α hα)

theorem zp_tmap_surjective {τ : Tag} {K : Type} [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) {N : AddSubgroup (Fin τ.rank → ℤ)}
    (hsat : ∀ v, p • v ∈ N → v ∈ N) (B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hB : ∀ α ∈ N, B *ᵥ α ∈ N) (hdet : B.det ≠ 0) {s : Fin τ.rank → Kˣ} (hs : s ∈ zp p N) :
    ∃ t ∈ zp p N, tmap B t = s := by
  obtain ⟨C, c, hc, hCB, hC⟩ := exists_ch_inverse B hB hdet
  obtain ⟨u, hu, rfl⟩ := zp_exists_zpow_eq hζ hsat hc hs
  exact ⟨tmap C u, tmap_mem_zp C hC hu, by rw [tmap_tmap, hCB, tmap_smul_one]⟩

theorem tmap_one_left {τ : Tag} {K : Type} [Field K] (t : Fin τ.rank → Kˣ) : tmap (1 : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) t = t := by
  have := tmap_smul_one 1 t
  rwa [one_smul, zpow_one] at this

theorem tmap_pow_left {τ : Tag} {K : Type} [Field K] (B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (i : ℕ) (t : Fin τ.rank → Kˣ) :
    (tmap B)^[i] t = tmap (B ^ i) t := by
  induction i generalizing t with
  | zero => rw [Function.iterate_zero_apply, pow_zero, tmap_one_left]
  | succ i ih => rw [Function.iterate_succ_apply', ih, tmap_tmap, pow_succ]

theorem zp_norm_surjective {τ : Tag} {K : Type} [Field K] [IsAlgClosed K] {p : ℕ} [Fact p.Prime] {ζ : Kˣ}
    (hζ : IsPrimitiveRoot ζ p) {N : AddSubgroup (Fin τ.rank → ℤ)}
    (hsat : ∀ v, p • v ∈ N → v ∈ N) (B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ)
    (hB : ∀ α ∈ N, B *ᵥ α ∈ N) (hdet : (B ^ p - 1).det ≠ 0) {y : Fin τ.rank → Kˣ}
    (hy : y ∈ zp p N) (hyB : tmap B y = y) :
    ∃ z ∈ zp p N, tmap (B ^ p) z = z ∧ ∏ i ∈ Finset.range p, tmap (B ^ i) z = y := by
  have hBp : ∀ α ∈ N, (B ^ p - 1) *ᵥ α ∈ N := fun α hα => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
    exact N.sub_mem (pow_mulVec_mem B hB p α hα) hα
  obtain ⟨x, hx, rfl⟩ := zp_tmap_surjective hζ hsat _ hBp hdet hy
  rw [tmap_sub, tmap_one_left] at hyB ⊢
  refine ⟨x⁻¹ * tmap B x, (zp p N).mul_mem ((zp p N).inv_mem hx) (tmap_mem_zp B hB hx), ?_, ?_⟩
  ·
    have e1 : tmap (B ^ p) (x⁻¹ * tmap B x) = (tmap (B ^ p) x)⁻¹ * tmap B (tmap (B ^ p) x) := by
      rw [tmap_mul, tmap_tmap, ← pow_succ', pow_succ, ← tmap_tmap, ← tmap_inv]
    rw [e1]
    rw [tmap_mul, tmap_inv] at hyB
    calc (tmap (B ^ p) x)⁻¹ * tmap B (tmap (B ^ p) x)
        = (tmap (B ^ p) x)⁻¹ * (tmap B (tmap (B ^ p) x) * (tmap B x)⁻¹) * tmap B x := by group
      _ = (tmap (B ^ p) x)⁻¹ * (tmap (B ^ p) x * x⁻¹) * tmap B x := by rw [hyB]
      _ = x⁻¹ * tmap B x := by group
  · have hn : ∀ n, ∏ i ∈ Finset.range n, tmap (B ^ i) (x⁻¹ * tmap B x) =
        tmap (B ^ n) x * x⁻¹ := by
      intro n
      induction n with
      | zero => simp [tmap_one_left]
      | succ n ih =>
        rw [Finset.prod_range_succ, ih, tmap_mul, tmap_inv, tmap_tmap, ← pow_succ']
        rw [mul_comm (tmap (B ^ n) x) x⁻¹, mul_assoc, mul_inv_cancel_left, mul_comm]
    exact hn p

end CFSG.HardMathSupport.C14Torus
