module

public import CFSG.RankThree.GF2n.Stroth80.Sec41Alg
public import CFSG.LargeExtraspecial.S3Fusion
public import CFSG.Milestones.LR_Glauberman_Z_star_central_Sylow_involution
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

theorem eq_one_of_commutes_odd {K E Γ : Type*} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup E] [Module K E] [Finite E] [Group Γ]
    (ρ : Γ →* Equiv.Perm E) (hρ : Function.Injective ρ)
    (hadd : ∀ γ e f, ρ γ (e + f) = ρ γ e + ρ γ f)
    (hlin : ∀ γ (c : K) e, ρ γ (c • e) = c • ρ γ e)
    (Qf : E → K) (hQc : ∀ (c : K) e, Qf (c • e) = c ^ 2 * Qf e)
    (hQ : ∀ γ e, Qf (ρ γ e) = Qf e) (hQnz : ∃ e, Qf e ≠ 0)
    (hodd : ∀ γ : Γ, Odd (orderOf γ))
    (Λ : Subgroup (E ≃ₗ[K] E)) (hΛ : IsPGroup 2 Λ) (b : E) (hb : b ≠ 0)
    (hfix : ∀ v : E, (∀ T ∈ Λ, T v = v) ↔ ∃ c : K, v = c • b)
    (hcomm : ∀ γ, ∀ T ∈ Λ, ∀ e, ρ γ (T e) = T (ρ γ e)) (γ : Γ) : γ = 1 := by
  have hρ0 : ∀ γ, ρ γ 0 = 0 := fun γ => by
    have := hadd γ 0 0
    simpa using this
  have hTb : ∀ T ∈ Λ, T b = b := fun T hT =>
    ((hfix b).mpr ⟨1, (one_smul K b).symm⟩) T hT
  obtain ⟨c, hc⟩ := (hfix (ρ γ b)).mp fun T hT => by
    rw [← hcomm γ T hT b, hTb T hT]
  have hc0 : c ≠ 0 := by
    intro h0
    have : ρ γ b = ρ γ 0 := by rw [hc, h0, zero_smul, hρ0]
    exact hb ((ρ γ).injective this)
  have hpowlin : ∀ (n : ℕ) (a : K) e, (ρ γ ^ n) (a • e) = a • (ρ γ ^ n) e := by
    intro n a e
    rw [← map_pow]
    exact hlin _ a e
  let Tl : E →ₗ[K] E :=
    { toFun := fun e => c⁻¹ • ρ γ e
      map_add' := fun e f => by simp [hadd, smul_add]
      map_smul' := fun a e => by
        show c⁻¹ • ρ γ (a • e) = a • (c⁻¹ • ρ γ e)
        rw [hlin, smul_comm] }
  have hTl : ∀ e, Tl e = c⁻¹ • ρ γ e := fun e => rfl
  have hTlb : Tl b = b := by
    rw [hTl, hc, smul_smul, inv_mul_cancel₀ hc0, one_smul]
  have hTlpow : ∀ (n : ℕ) e, (Tl ^ n) e = (c⁻¹) ^ n • (ρ γ ^ n) e := by
    intro n
    induction n with
    | zero => intro e; simp
    | succ n ih =>
      intro e
      rw [pow_succ, Module.End.mul_apply, hTl, ih, hpowlin, smul_smul, ← pow_succ,
        pow_succ (ρ γ) n, Equiv.Perm.mul_apply]
  have hρpow : (ρ γ) ^ orderOf γ = 1 := by
    rw [← map_pow, pow_orderOf_eq_one, map_one]
  have hcpow : ∀ n : ℕ, (ρ γ ^ n) b = c ^ n • b := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Equiv.Perm.mul_apply, hc, hpowlin, ih, smul_smul, ← pow_succ']
  have hco : c ^ orderOf γ = 1 := by
    have h1 := hcpow (orderOf γ)
    rw [hρpow] at h1
    have h2 : (c ^ orderOf γ - 1) • b = 0 := by
      rw [sub_smul, ← h1]
      simp
    rcases smul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h hb
  have hTlp : Tl ^ orderOf γ = 1 := by
    refine LinearMap.ext fun e => ?_
    rw [hTlpow, hρpow, inv_pow, hco, inv_one, one_smul]
    rfl
  have hker : LinearMap.ker (Tl - 1) ⊓ LinearMap.range (Tl - 1) = ⊥ :=
    ker_inf_range_eq_bot_of_pow_eq_one (hodd γ) hTlp
  have hTcomm : ∀ S ∈ Λ, ∀ e, Tl (S e) = S (Tl e) := by
    intro S hS e
    rw [hTl, hTl, hcomm γ S hS e, map_smul]
  have hRinv : ∀ S ∈ Λ, ∀ v ∈ LinearMap.range (Tl - 1), S v ∈ LinearMap.range (Tl - 1) := by
    intro S hS v hv
    obtain ⟨e, he⟩ := hv
    refine ⟨S e, ?_⟩
    have he' : Tl e - e = v := by simpa using he
    simp only [LinearMap.sub_apply, Module.End.one_apply]
    rw [hTcomm S hS e, ← he', map_sub]
  have hRbot : LinearMap.range (Tl - 1) = ⊥ := by
    by_contra hne
    obtain ⟨v, hvR, hv0, hvfix⟩ := exists_fixed_vector_of_isPGroup Λ hΛ _ hRinv hne
    obtain ⟨a, ha⟩ := (hfix v).mp hvfix
    have hvker : v ∈ LinearMap.ker (Tl - 1) := by
      rw [LinearMap.mem_ker, ha]
      simp only [LinearMap.sub_apply, Module.End.one_apply, map_smul, hTlb, sub_self, smul_zero]
    have : v ∈ LinearMap.ker (Tl - 1) ⊓ LinearMap.range (Tl - 1) := ⟨hvker, hvR⟩
    rw [hker] at this
    exact hv0 ((Submodule.mem_bot K).mp this)
  have hTone : ∀ e, Tl e = e := by
    intro e
    have : (Tl - 1) e = 0 := by
      have h := LinearMap.mem_range_self (Tl - 1) e
      rw [hRbot] at h
      exact (Submodule.mem_bot K).mp h
    simpa [sub_eq_zero] using this
  have hscalar : ∀ e, ρ γ e = c • e := by
    intro e
    have h := hTone e
    rw [hTl] at h
    calc ρ γ e = c • (c⁻¹ • ρ γ e) := by rw [smul_smul, mul_inv_cancel₀ hc0, one_smul]
      _ = c • e := by rw [h]
  obtain ⟨e₀, he₀⟩ := hQnz
  have hc2 : c ^ 2 = 1 := by
    have h1 : Qf (ρ γ e₀) = c ^ 2 * Qf e₀ := by rw [hscalar, hQc]
    rw [hQ] at h1
    have h2 : (c ^ 2 - 1) * Qf e₀ = 0 := by linear_combination -h1
    rcases mul_eq_zero.mp h2 with h | h
    · exact sub_eq_zero.mp h
    · exact absurd h he₀
  have hc1 : c = 1 := by
    have h : (c - 1) ^ 2 = 0 := by
      have : (c - 1) ^ 2 = c ^ 2 - 1 := by
        have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
        linear_combination (1 - c) * h2
      rw [this, hc2, sub_self]
    exact sub_eq_zero.mp (pow_eq_zero_iff (two_ne_zero) |>.mp h)
  apply hρ
  rw [map_one]
  refine Equiv.ext fun e => ?_
  rw [hscalar, hc1, one_smul]
  rfl

theorem exists_ne_bot_centralizer_of_odd {Γ : Type*} [Group Γ] [Finite Γ] {Λ A : Subgroup Γ}
    (hΛ : IsElemAbelian 2 Λ) (hΛ4 : 4 ≤ Nat.card Λ)
    (hn : Λ ≤ Subgroup.normalizer (A : Set Γ)) (hodd : Odd (Nat.card A)) (hA : A ≠ ⊥) :
    ∃ Λ₀ : Subgroup Γ, Λ₀ ≤ Λ ∧ Λ₀ ≠ ⊥ ∧ A ⊓ Subgroup.centralizer (Λ₀ : Set Γ) ≠ ⊥ := by
  have hgen := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_hyperplanes Nat.prime_two
    hΛ (by omega) hn (Odd.coprime_two_left hodd)
  obtain ⟨B, hB, hne⟩ : ∃ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 Λ,
      A ⊓ Subgroup.centralizer (B : Set Γ) ≠ ⊥ := by
    by_contra hcon
    push Not at hcon
    have hle : (⨆ B ∈ CFSG.SignalizerFunctorTheorem.Coprime.hyperplanes 2 Λ,
        A ⊓ Subgroup.centralizer (B : Set Γ)) ≤ ⊥ :=
      iSup₂_le fun B hB => (hcon B hB).le
    exact hA (le_bot_iff.mp (hgen.symm.le.trans hle))
  obtain ⟨hBΛ, hcard⟩ := hB
  refine ⟨B, hBΛ, ?_, hne⟩
  rintro rfl
  rw [Subgroup.card_bot] at hcard
  omega

theorem isSolvable_sup_of_odd {Γ : Type*} [Group Γ] [Finite Γ] {Λ A : Subgroup Γ}
    (hΛ : ∀ a ∈ Λ, ∀ b ∈ Λ, a * b = b * a) (hn : Λ ≤ Subgroup.normalizer (A : Set Γ))
    (hodd : Odd (Nat.card A)) : Group.IsSolvable ↥(Λ ⊔ A) := by
  have hAP : A ≤ Λ ⊔ A := le_sup_right
  have hconj : ∀ g ∈ Λ, ∀ x ∈ A, g⁻¹ * x * g ∈ A := by
    intro g hg x hx
    have h := Subgroup.mem_normalizer_iff.mp (hn (Λ.inv_mem hg)) x
    rw [inv_inv] at h
    exact h.mp hx
  have hNorm : (A.subgroupOf (Λ ⊔ A)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hAP).mpr
      (sup_le hn Subgroup.le_normalizer)
  have hdec : ∀ x ∈ Λ ⊔ A, ∃ l ∈ Λ, ∃ a ∈ A, l * a = x := by
    intro x hx
    have hx' : (⟨x, hx⟩ : ↥(Λ ⊔ A)) ∈ Λ.subgroupOf (Λ ⊔ A) ⊔ A.subgroupOf (Λ ⊔ A) := by
      rw [← Subgroup.subgroupOf_sup (le_sup_left : Λ ≤ Λ ⊔ A) hAP, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    obtain ⟨y, hy, z, hz, hyz⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
    exact ⟨(y : Γ), Subgroup.mem_subgroupOf.mp hy, (z : Γ), Subgroup.mem_subgroupOf.mp hz,
      congrArg Subtype.val hyz⟩
  have hcomm : ∀ x ∈ Λ ⊔ A, ∀ y ∈ Λ ⊔ A, (x * y)⁻¹ * (y * x) ∈ A := by
    intro x hx y hy
    obtain ⟨l, hl, a, ha, rfl⟩ := hdec x hx
    obtain ⟨m, hm, b, hb, rfl⟩ := hdec y hy
    have hlm : l⁻¹ * m = m * l⁻¹ := hΛ _ (Λ.inv_mem hl) _ hm
    have e : (l * a * (m * b))⁻¹ * (m * b * (l * a))
        = b⁻¹ * ((m⁻¹ * a⁻¹ * m) * ((l⁻¹ * b * l) * a)) := by
      calc (l * a * (m * b))⁻¹ * (m * b * (l * a))
          = b⁻¹ * m⁻¹ * a⁻¹ * (l⁻¹ * m) * b * l * a := by group
        _ = b⁻¹ * m⁻¹ * a⁻¹ * (m * l⁻¹) * b * l * a := by rw [hlm]
        _ = b⁻¹ * ((m⁻¹ * a⁻¹ * m) * ((l⁻¹ * b * l) * a)) := by group
    rw [e]
    exact A.mul_mem (A.inv_mem hb)
      (A.mul_mem (hconj m hm _ (A.inv_mem ha)) (A.mul_mem (hconj l hl _ hb) ha))
  have hQcomm : ∀ x y : ↥(Λ ⊔ A) ⧸ A.subgroupOf (Λ ⊔ A), x * y = y * x := by
    intro x y
    refine QuotientGroup.induction_on x (fun p => QuotientGroup.induction_on y (fun q => ?_))
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    exact hcomm p p.2 q q.2
  have hQs : Group.IsSolvable (↥(Λ ⊔ A) ⧸ A.subgroupOf (Λ ⊔ A)) :=
    Group.isSolvable_of_comm hQcomm
  have hsubA : Group.IsSolvable ↥(A.subgroupOf (Λ ⊔ A)) := by
    have hcard : Nat.card ↥(A.subgroupOf (Λ ⊔ A)) = Nat.card ↥A :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAP).toEquiv
    exact CFSG.FeitThompson.isSolvable_of_odd_natCard ↥(A.subgroupOf (Λ ⊔ A)) (by rw [hcard]; exact hodd)
  exact Group.isSolvable_of_ker_le_range (A.subgroupOf (Λ ⊔ A)).subtype
    (QuotientGroup.mk' (A.subgroupOf (Λ ⊔ A))) (le_of_eq (by simp))

theorem isSolvable_of_ker_pGroup {S P' : Type*} [Group S] [Group P'] [Finite S]
    (ψ : S →* P') (hker : IsPGroup 2 ψ.ker) (hrange : Group.IsSolvable ↥ψ.range) :
    Group.IsSolvable S := by
  have hNn : Group.IsNilpotent ↥ψ.ker := hker.isNilpotent
  have hNs : Group.IsSolvable ↥ψ.ker := inferInstance
  exact Group.isSolvable_of_ker_le_range ψ.ker.subtype ψ.rangeRestrict (le_of_eq (by simp))

theorem odd_card_of_normal_nilpotent {Γ : Type} [Group Γ] [Finite Γ] (hΓ : pCore 2 Γ = ⊥)
    (F : Subgroup Γ) [F.Normal] [Group.IsNilpotent F] : Odd (Nat.card F) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card F := by
    rcases Nat.even_or_odd (Nat.card F) with h | h
    · exact even_iff_two_dvd.mp h
    · exact absurd h hodd
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := F) 2 h2
  have hp : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx]
    simp
  obtain ⟨P, hP⟩ := hp.exists_le_sylow
  have h1 := Sylow.map_le_pCore (N := F) inferInstance inferInstance 2 P
  rw [hΓ] at h1
  have hx' : (x : Γ) ∈ P.map F.subtype := ⟨x, hP (Subgroup.mem_zpowers x), rfl⟩
  have := h1 hx'
  rw [Subgroup.mem_bot] at this
  have hx1 : x = 1 := Subtype.ext this
  rw [hx1, orderOf_one] at hx
  omega

theorem charP_two_of_card_eq_two_pow {K : Type*} [Field K] [Finite K] {k : ℕ}
    (h : Nat.card K = 2 ^ k) : CharP K 2 := by
  haveI := Fintype.ofFinite K
  haveI := ringChar.charP K
  obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
  have hdvd : ringChar K ∣ 2 ^ k := by
    rw [← h, Nat.card_eq_fintype_card, hn]
    exact dvd_pow_self _ n.ne_zero
  have h2 : ringChar K ∣ 2 := hp.dvd_of_dvd_pow hdvd
  have : ringChar K = 2 := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp h2
  exact ringChar.eq_iff.mp this

theorem isQuasisimple_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.IsQuasisimple A) : CFSG.IsQuasisimple B := by
  obtain ⟨hp, hs, a, b, hab⟩ := h
  have hrange : (e : A →* B).range = ⊤ := MonoidHom.range_eq_top.mpr e.surjective
  have hcenter : (Subgroup.center A).map (e : A →* B) = Subgroup.center B :=
    Subgroup.map_center_eq e
  let e' : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
    QuotientGroup.congr (Subgroup.center A) (Subgroup.center B) e hcenter
  refine ⟨?_, (MulEquiv.isSimpleGroup_congr e').mp hs, e' a, e' b, ?_⟩
  · have hmap : (commutator A).map (e : A →* B) = commutator B := by
      rw [commutator_def, Subgroup.map_commutator, Subgroup.map_top, hrange, commutator_def]
    haveI : Group.IsPerfect A := hp
    refine ⟨?_⟩
    rw [← hmap, Group.IsPerfect.commutator_eq_top, Subgroup.map_top]
    exact hrange
  · intro h
    exact hab (e'.injective (by rw [map_mul, map_mul]; exact h))

theorem comm_of_commutators_central {Γ : Type*} [Group Γ] {X : Subgroup Γ} [Group.IsPerfect X]
    {t : Γ} (hn : t ∈ Subgroup.normalizer (X : Set Γ))
    (hc : ∀ x ∈ X, ∀ y ∈ X, y * (t⁻¹ * x⁻¹ * t * x) = (t⁻¹ * x⁻¹ * t * x) * y) :
    ∀ x ∈ X, x * t = t * x := by
  have hmem : ∀ x ∈ X, t⁻¹ * x⁻¹ * t * x ∈ X := by
    intro x hx
    have h3 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) x⁻¹).mp (X.inv_mem hx)
    rw [inv_inv] at h3
    exact X.mul_mem h3 hx
  have hcen : ∀ a : ↥X, (⟨t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ), hmem a a.2⟩ : ↥X) ∈
      Subgroup.center ↥X := by
    intro a
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hc a a.2 y y.2)
  let f : ↥X →* ↥(Subgroup.center ↥X) :=
    { toFun := fun a => ⟨⟨t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ), hmem a a.2⟩, hcen a⟩
      map_one' := by
        apply Subtype.ext
        apply Subtype.ext
        simp
      map_mul' := fun a b => by
        apply Subtype.ext
        apply Subtype.ext
        show t⁻¹ * ((a : Γ) * (b : Γ))⁻¹ * t * ((a : Γ) * (b : Γ)) =
          (t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ)) * (t⁻¹ * (b : Γ)⁻¹ * t * (b : Γ))
        have hab := hc a a.2 b b.2
        have hba := hc b b.2 a a.2
        have e1 : t⁻¹ * ((a : Γ) * (b : Γ))⁻¹ * t * ((a : Γ) * (b : Γ)) =
            (t⁻¹ * (b : Γ)⁻¹ * t * (b : Γ)) *
              ((b : Γ)⁻¹ * (t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ)) * (b : Γ)) := by group
        have e2 : (b : Γ)⁻¹ * (t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ)) * (b : Γ) =
            t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ) := by
          calc (b : Γ)⁻¹ * (t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ)) * (b : Γ)
              = (b : Γ)⁻¹ * ((t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ)) * (b : Γ)) := by group
            _ = (b : Γ)⁻¹ * ((b : Γ) * (t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ))) := by rw [← hab]
            _ = t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ) := by group
        rw [e1, e2]
        have e3 := hc b b.2 (t⁻¹ * (a : Γ)⁻¹ * t * (a : Γ)) (hmem a a.2)
        exact e3.symm }
  intro x hx
  have h1 := hom_eq_one_of_perfect_of_comm (fun a b : ↥(Subgroup.center ↥X) =>
    Subtype.ext (Subtype.ext (by
      have := Subgroup.mem_center_iff.mp b.2 a.1
      exact congrArg Subtype.val this))) f ⟨x, hx⟩
  have h2 : t⁻¹ * x⁻¹ * t * x = 1 := congrArg (fun a : ↥(Subgroup.center ↥X) => ((a : ↥X) : Γ)) h1
  have h3 : x⁻¹ * t * x = t := by
    have h4 := congrArg (fun a => t * a) h2
    simp only [mul_one] at h4
    calc x⁻¹ * t * x = t * (t⁻¹ * x⁻¹ * t * x) := by group
      _ = t := h4
  calc x * t = x * (x⁻¹ * t * x) := by rw [h3]
    _ = t * x := by group

theorem comm_of_inter_eq_bot {Γ : Type} [Group Γ] [Finite Γ] {Λ X : Subgroup Γ}
    (hΛ : IsElemAbelian 2 Λ)
    (hw : ∀ x : Γ, conjSubgroup x Λ ≤ Subgroup.normalizer (Λ : Set Γ) → conjSubgroup x Λ = Λ)
    (hn : Λ ≤ Subgroup.normalizer (X : Set Γ)) (hXq : CFSG.IsQuasisimple X)
    (h0 : Λ ⊓ X = ⊥) : ∀ x ∈ X, ∀ t ∈ Λ, x * t = t * x := by
  have hΛ2 : IsPGroup 2 Λ := fun g => ⟨1, Subtype.ext (by simpa using hΛ.2 g g.2)⟩
  have hΛcomm : ∀ a ∈ Λ, ∀ b ∈ Λ, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hΛ.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hwc : CFSG.LargeExtraspecial.IsWeaklyClosedInNormalizer Λ := hw
  have hsc := CFSG.LargeExtraspecial.lemma_3_12_isStronglyClosedIn hΛ2 hΛcomm hwc
  set Y : Subgroup Γ := Λ ⊔ X with hY
  have hXY : X ≤ Y := le_sup_right
  have hΛY : Λ ≤ Y := le_sup_left
  haveI hnormX : (X.subgroupOf Y).Normal := by
    refine (Subgroup.normal_subgroupOf_iff_le_normalizer hXY).mpr ?_
    exact sup_le (fun l hl => hn hl) Subgroup.le_normalizer
  have hdec : ∀ y ∈ Y, ∃ l ∈ Λ, ∃ x ∈ X, l * x = y := by
    intro y hy
    have hy' : (⟨y, hy⟩ : ↥Y) ∈ Λ.subgroupOf Y ⊔ X.subgroupOf Y := by
      rw [← Subgroup.subgroupOf_sup hΛY hXY, Subgroup.subgroupOf_self]
      exact Subgroup.mem_top _
    obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_right.mp hy'
    exact ⟨(a : Γ), Subgroup.mem_subgroupOf.mp ha, (b : Γ), Subgroup.mem_subgroupOf.mp hb,
      congrArg Subtype.val hab⟩
  have hΛ2' : IsPGroup 2 (Λ.subgroupOf Y) := hΛ2.comap_subtype
  obtain ⟨P, hP⟩ := hΛ2'.exists_le_sylow
  set T : Subgroup Γ := (P : Subgroup ↥Y).map Y.subtype with hT
  have hT2 : IsPGroup 2 T := P.isPGroup'.map Y.subtype
  have hΛT : Λ ≤ T := fun l hl =>
    ⟨⟨l, hΛY hl⟩, hP (show (⟨l, hΛY hl⟩ : ↥Y) ∈ Λ.subgroupOf Y from hl), rfl⟩
  have hTn : T ≤ Subgroup.normalizer (Λ : Set Γ) :=
    CFSG.LargeExtraspecial.le_normalizer_of_isWeaklyClosed hwc hT2 hΛT
  have hSc : ∀ s ∈ T, s ∈ X → ∀ l ∈ Λ, s * l = l * s := by
    intro s hsT hsX l hl
    have h1 : s * l * s⁻¹ * l⁻¹ ∈ Λ :=
      Λ.mul_mem ((Subgroup.mem_normalizer_iff.mp (hTn hsT) l).mp hl) (Λ.inv_mem hl)
    have h2 : s * l * s⁻¹ * l⁻¹ ∈ X := by
      have h3 : l * s⁻¹ * l⁻¹ ∈ X :=
        (Subgroup.mem_normalizer_iff.mp (hn hl) s⁻¹).mp (X.inv_mem hsX)
      have e : s * l * s⁻¹ * l⁻¹ = s * (l * s⁻¹ * l⁻¹) := by group
      rw [e]
      exact X.mul_mem hsX h3
    have h3 : s * l * s⁻¹ * l⁻¹ ∈ Λ ⊓ X := ⟨h1, h2⟩
    rw [h0, Subgroup.mem_bot] at h3
    calc s * l = (s * l * s⁻¹ * l⁻¹) * (l * s) := by group
      _ = l * s := by rw [h3, one_mul]
  have hZ : ∀ z ∈ Λ, z ≠ 1 → ∀ x ∈ X,
      ∃ k ∈ CFSG.oddCore ↥Y, (k : Γ) = z⁻¹ * x⁻¹ * z * x := by
    intro z hz hz1 x hx
    have hzY : z ∈ Y := hΛY hz
    have hxY : x ∈ Y := hXY hx
    have hzP : (⟨z, hzY⟩ : ↥Y) ∈ (P : Subgroup ↥Y) :=
      hP (show (⟨z, hzY⟩ : ↥Y) ∈ Λ.subgroupOf Y from hz)
    let z' : ↥(P : Subgroup ↥Y) := ⟨⟨z, hzY⟩, hzP⟩
    have hzcen : z' ∈ Subgroup.center ↥(P : Subgroup ↥Y) := by
      rw [Subgroup.mem_center_iff]
      intro p
      apply Subtype.ext
      apply Subtype.ext
      have hpT : ((p : ↥Y) : Γ) ∈ T := ⟨(p : ↥Y), p.2, rfl⟩
      obtain ⟨l, hl, x', hx', hlx⟩ := hdec ((p : ↥Y) : Γ) (p : ↥Y).2
      have hx'T : x' ∈ T := by
        have e : x' = l⁻¹ * ((p : ↥Y) : Γ) := by rw [← hlx]; group
        rw [e]
        exact T.mul_mem (T.inv_mem (hΛT hl)) hpT
      have h1 : l * z = z * l := hΛcomm l hl z hz
      have h2 : x' * z = z * x' := hSc x' hx'T hx' z hz
      show ((p : ↥Y) : Γ) * z = z * ((p : ↥Y) : Γ)
      rw [← hlx]
      calc l * x' * z = l * (x' * z) := by group
        _ = l * (z * x') := by rw [h2]
        _ = (l * z) * x' := by group
        _ = (z * l) * x' := by rw [h1]
        _ = z * (l * x') := by group
    have hz2 : orderOf z' = 2 := by
      apply orderOf_eq_prime
      · apply Subtype.ext
        apply Subtype.ext
        exact hΛ.2 z hz
      · intro h
        exact hz1 (congrArg (fun a : ↥(P : Subgroup ↥Y) => ((a : ↥Y) : Γ)) h)
    have hwc' : ∀ g : ↥Y, g⁻¹ * ((z' : ↥(P : Subgroup ↥Y)) : ↥Y) * g ∈ (P : Subgroup ↥Y) →
        g⁻¹ * ((z' : ↥(P : Subgroup ↥Y)) : ↥Y) * g = ((z' : ↥(P : Subgroup ↥Y)) : ↥Y) := by
      intro g hg
      have huT : (g : Γ)⁻¹ * z * (g : Γ) ∈ T := ⟨_, hg, rfl⟩
      obtain ⟨l', hl', x', hx', hlx'⟩ := hdec (g : Γ) g.2
      have hw1 : z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ)) = z⁻¹ * x'⁻¹ * z * x' := by
        rw [← hlx']
        have h1 : l' * z = z * l' := hΛcomm l' hl' z hz
        calc z⁻¹ * ((l' * x')⁻¹ * z * (l' * x'))
            = z⁻¹ * (x'⁻¹ * (l'⁻¹ * z * l') * x') := by group
          _ = z⁻¹ * (x'⁻¹ * z * x') := by
            congr 3
            calc l'⁻¹ * z * l' = l'⁻¹ * (z * l') := by group
              _ = l'⁻¹ * (l' * z) := by rw [h1]
              _ = z := by group
          _ = z⁻¹ * x'⁻¹ * z * x' := by group
      have hwX : z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ)) ∈ X := by
        rw [hw1]
        have h3 : z⁻¹ * x'⁻¹ * z⁻¹⁻¹ ∈ X :=
          (Subgroup.mem_normalizer_iff.mp (hn (Λ.inv_mem hz)) x'⁻¹).mp (X.inv_mem hx')
        rw [inv_inv] at h3
        have e : z⁻¹ * x'⁻¹ * z * x' = (z⁻¹ * x'⁻¹ * z) * x' := rfl
        rw [e]
        exact X.mul_mem h3 hx'
      have hwT : z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ)) ∈ T := T.mul_mem (T.inv_mem (hΛT hz)) huT
      have hcentu : (g : Γ)⁻¹ * z * (g : Γ) ∈ Subgroup.centralizer (Λ : Set Γ) := by
        rw [Subgroup.mem_centralizer_iff]
        intro l hl
        have hcw := hSc _ hwT hwX l hl
        have hz' : l * z = z * l := hΛcomm l hl z hz
        have e : (g : Γ)⁻¹ * z * (g : Γ) = z * (z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ))) := by group
        rw [e]
        calc l * (z * (z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ))))
            = (l * z) * (z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ))) := by group
          _ = (z * l) * (z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ))) := by rw [hz']
          _ = z * (l * (z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ)))) := by group
          _ = z * ((z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ))) * l) := by rw [hcw.symm]
          _ = (z * (z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ)))) * l := by group
      have huΛ : (g : Γ)⁻¹ * z * (g : Γ) ∈ Λ := hsc.2 z hz (g : Γ) hcentu
      have hwΛX : z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ)) ∈ Λ ⊓ X :=
        ⟨Λ.mul_mem (Λ.inv_mem hz) huΛ, hwX⟩
      rw [h0, Subgroup.mem_bot] at hwΛX
      apply Subtype.ext
      show (g : Γ)⁻¹ * z * (g : Γ) = z
      calc (g : Γ)⁻¹ * z * (g : Γ) = z * (z⁻¹ * ((g : Γ)⁻¹ * z * (g : Γ))) := by group
        _ = z := by rw [hwΛX, mul_one]
    obtain ⟨-, hcent⟩ :=
      CFSG.Milestones.glauberman_zStar_central_sylow_involution P z' hzcen hz2 hwc'
    have hmk := Subgroup.mem_center_iff.mp hcent
      (QuotientGroup.mk (⟨x, hxY⟩ : ↥Y) : ↥Y ⧸ CFSG.oddCore ↥Y)
    have hq : (QuotientGroup.mk ((⟨x, hxY⟩ : ↥Y) * ⟨z, hzY⟩) : ↥Y ⧸ CFSG.oddCore ↥Y) =
        QuotientGroup.mk (⟨z, hzY⟩ * ⟨x, hxY⟩) := hmk
    have hk := QuotientGroup.eq.mp hq
    refine ⟨_, hk, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  have hq' : CFSG.IsQuasisimple ↥(X.subgroupOf Y) :=
    isQuasisimple_of_mulEquiv' (Subgroup.subgroupOfEquivOfLe hXY).symm hXq
  rcases quasisimple_le_or_comm (X := X.subgroupOf Y) (N := CFSG.oddCore ↥Y) hq' with hle | hcm
  · exfalso
    have hle2 : X.subgroupOf Y ≤ CFSG.pPrimeCore 2 ↥Y := hle.trans (sSup_le fun N hN =>
      le_sSup ⟨hN.1, Nat.coprime_two_left.mpr hN.2⟩)
    have hodd : Odd (Nat.card ↥(X.subgroupOf Y)) := by
      have h1 : Nat.card ↥(X.subgroupOf Y) ∣ Nat.card ↥(CFSG.pPrimeCore 2 ↥Y) :=
        Subgroup.card_dvd_of_le hle2
      have h2 : Nat.Coprime 2 (Nat.card ↥(CFSG.pPrimeCore 2 ↥Y)) := CFSG.pPrimeCore_coprime_card
      exact Nat.coprime_two_left.mp (Nat.Coprime.coprime_dvd_right h1 h2)
    haveI : Group.IsSolvable ↥(X.subgroupOf Y) := CFSG.FeitThompson.isSolvable_of_odd_natCard _ hodd
    haveI : Group.IsPerfect ↥(X.subgroupOf Y) := hq'.1
    haveI : Nontrivial ↥(X.subgroupOf Y) := by
      by_contra hcon
      rw [not_nontrivial_iff_subsingleton] at hcon
      obtain ⟨a, b, hab⟩ := hq'.2.2
      exact hab (Subsingleton.elim _ _)
    exact Group.IsPerfect.not_isSolvable ↥(X.subgroupOf Y) inferInstance
  · intro x hx t ht
    by_cases ht1 : t = 1
    · rw [ht1]
      simp
    · haveI : Group.IsPerfect ↥X := hXq.1
      refine comm_of_commutators_central (hn ht) (fun x' hx' y hy => ?_) x hx
      obtain ⟨k, hk, hkx⟩ := hZ t ht ht1 x' hx'
      have h := hcm ⟨y, hXY hy⟩ hy k hk
      have h' : y * (k : Γ) = (k : Γ) * y := congrArg Subtype.val h
      rwa [hkx] at h'

end CFSG.RankThree.GF2n.Stroth80
