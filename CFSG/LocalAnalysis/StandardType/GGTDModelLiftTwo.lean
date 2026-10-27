module

public import CFSG.LocalAnalysis.StandardType.GGTDModelDefs
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Lift

variable {K : Type} [Field K] {N m : ℕ} {L' R : Type} [Group L'] [Group R]

@[expose] def GGTDInnerTorus (M : GGTDModel K N m R) : Prop :=
  ∀ {a : MulAut R} {t : Fin (N + 1) → Kˣ}, M.Act a t →
    ∃ s : ggTDTg M.μ N, a = MulAut.conj (M.φ (M.dgm s))

theorem ggTDTg_pow_eq_one (M : GGTDModel K N m R) (s : ggTDTg M.μ N) : s ^ m = 1 := by
  apply Subtype.ext
  funext i
  have hx : (⟨(s : Fin (N + 1) → Kˣ) i, s.2.1 i⟩ : M.μ) ^ m = 1 := by
    apply M.ι.injective
    rw [map_pow, map_one]
    obtain ⟨y, hy⟩ : ∃ y : ZMod m, M.ι ⟨(s : Fin (N + 1) → Kˣ) i, s.2.1 i⟩ =
        Multiplicative.ofAdd y := ⟨_, rfl⟩
    rw [hy, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero]
  have h := congrArg (fun y : M.μ => (y : Kˣ)) hx
  simpa using h

theorem eq_one_of_isPGroup_two_of_pow_odd {G : Type*} [Group G] {S : Subgroup G}
    (hS : IsPGroup 2 S) (hm : Odd m) {z : G} (hz : z ∈ S) (hzm : z ^ m = 1) : z = 1 := by
  obtain ⟨k, hk⟩ := hS ⟨z, hz⟩
  have h1 : z ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf z ∣ Nat.gcd (2 ^ k) m :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hzm)
  rw [(Nat.Coprime.pow_left k hm.coprime_two_left).gcd_eq_one, Nat.dvd_one,
    orderOf_eq_one_iff] at h2
  exact h2

theorem eq_of_map_eq_of_pow_odd {G Q : Type*} [Group G] [Group Q] {f : G →* Q}
    (hker : f.ker ≤ Subgroup.center G) (h2 : IsPGroup 2 f.ker) (hm : Odd m) {x y : G}
    (hxy : f x = f y) (hx : x ^ m = 1) (hy : y ^ m = 1) : x = y := by
  have hz : x⁻¹ * y ∈ f.ker := by rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, inv_mul_cancel]
  have hcomm : Commute x (x⁻¹ * y) := Subgroup.mem_center_iff.mp (hker hz) x
  have hy' : y = x * (x⁻¹ * y) := by group
  have h1 : (x⁻¹ * y) ^ m = 1 := by
    have e : y ^ m = x ^ m * (x⁻¹ * y) ^ m := by
      conv_lhs => rw [hy']
      exact hcomm.mul_pow m
    rw [hx, hy, one_mul] at e
    exact e.symm
  have h3 := eq_one_of_isPGroup_two_of_pow_odd h2 hm hz h1
  calc x = x * (x⁻¹ * y) := by rw [h3, mul_one]
    _ = y := by group

theorem finite_ggTDTg (M : GGTDModel K N m R) (hm : 0 < m) : Finite (ggTDTg M.μ N) := by
  have : NeZero m := ⟨hm.ne'⟩
  have : Finite M.μ := Finite.of_equiv _ M.ι.symm.toEquiv
  exact Finite.of_injective (fun s : ggTDTg M.μ N => fun i =>
    (⟨(s : Fin (N + 1) → Kˣ) i, s.2.1 i⟩ : M.μ)) fun s s' h => Subtype.ext (funext fun i =>
      congrArg Subtype.val (congrFun h i))

theorem coprime_two_card_ggTDTg (M : GGTDModel K N m R) (hm : Odd m) :
    Nat.Coprime 2 (Nat.card (ggTDTg M.μ N)) := by
  have := finite_ggTDTg M hm.pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h2 => ?_
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have h := orderOf_dvd_of_pow_eq_one (ggTDTg_pow_eq_one M x)
  rw [hx] at h
  exact (Nat.not_even_iff_odd.mpr hm) (even_iff_two_dvd.mpr h)

variable [Finite L'] [Finite R] {ψ : L' →* R}

theorem exists_ggTDModel_liftTwo (M₀ : GGTDModel K N m R) (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (h2 : IsPGroup 2 ψ.ker) (hperf : commutator L' = ⊤)
    (hZ : Subgroup.center R = ⊥) (hm : Odd m) (hin : GGTDInnerTorus M₀) :
    ∃ M : GGTDModel K N m L',
      (∀ (a : MulAut L') (t : Fin (N + 1) → Kˣ),
        M.Act a t ↔ ∃ b : MulAut R, M₀.Act b t ∧ ∀ l, b (ψ l) = ψ (a l)) ∧
      ∀ σ, ψ (M.φ (M.Pm σ)) = M₀.φ (M₀.Pm σ) := by
  classical
  have := finite_ggTDTg M₀ hm.pos
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨dg, hdg⟩ := CFSG.Wielandt.exists_lift_of_surjective_isPGroup_ker_of_coprime ψ hψ h2
    (coprime_two_card_ggTDTg M₀ hm) (M₀.φ.comp M₀.dgm)
  have hdg' : ∀ s, ψ (dg s) = M₀.φ (M₀.dgm s) := fun s => congrArg (fun f => f s) hdg
  have hdgm : ∀ s, dg s ^ m = 1 := fun s => by rw [← map_pow, ggTDTg_pow_eq_one, map_one]
  have hcen : ∀ z ∈ Subgroup.center L', z ∈ ψ.ker := by
    intro z hz
    have h1 : ψ z ∈ Subgroup.center R := by
      rw [Subgroup.mem_center_iff]
      intro r
      obtain ⟨l, rfl⟩ := hψ r
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz l]
    rw [hZ, Subgroup.mem_bot] at h1
    exact h1
  have hfib : ∀ x y : L', ψ x = ψ y → x⁻¹ * y ∈ ψ.ker := fun x y h => by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, inv_mul_cancel]
  have hconjind : ∀ g l : L', MulAut.conj (ψ g) (ψ l) = ψ (MulAut.conj g l) := by
    intro g l
    simp only [MulAut.conj_apply, map_mul, map_inv]
  have hsame : ∀ x y : L', ψ x = ψ y → x ^ m = 1 → y ^ m = 1 → x = y := fun _ _ hxy hx hy =>
    eq_of_map_eq_of_pow_odd hker h2 hm hxy hx hy
  have hPm : ∀ σ, ∃ l : L', ψ l = M₀.φ (M₀.Pm σ) := fun σ => hψ _
  choose Pm hPm using hPm
  let Act : MulAut L' → (Fin (N + 1) → Kˣ) → Prop :=
    fun a t => ∃ b : MulAut R, M₀.Act b t ∧ ∀ l, b (ψ l) = ψ (a l)
  have hindu : ∀ {a : MulAut L'} {b b' : MulAut R}, (∀ l, b (ψ l) = ψ (a l)) →
      (∀ l, b' (ψ l) = ψ (a l)) → b = b' := fun h h' =>
    TypeA.induced_unique ψ hψ h h'
  have hinj : ∀ {a a' : MulAut L'} {b : MulAut R}, (∀ l, b (ψ l) = ψ (a l)) →
      (∀ l, b (ψ l) = ψ (a' l)) → a = a' := fun h h' =>
    TypeA.mulAut_eq_of_forall ψ hker hperf fun l => by rw [← h, ← h']
  have hAct_conj : ∀ {a : MulAut L'} {t}, Act a t → ∃ s, a = MulAut.conj (dg s) := by
    rintro a t ⟨b, hb, hbl⟩
    obtain ⟨s, rfl⟩ := hin hb
    refine ⟨s, hinj hbl fun l => ?_⟩
    rw [← hconjind, hdg']
  have hAct_dgm : ∀ s : ggTDTg M₀.μ N, Act (MulAut.conj (dg s)) (s : Fin (N + 1) → Kˣ) :=
    fun s => ⟨MulAut.conj (M₀.φ (M₀.dgm s)), M₀.act_dgm s, fun l => by rw [← hdg', hconjind]⟩
  have hfix : ∀ {a : MulAut L'} {t}, Act a t → ∀ s, a (dg s) = dg s := by
    rintro a t ⟨b, hb, hbl⟩ s
    refine hsame _ _ ?_ ?_ (hdgm s)
    · rw [← hbl, hdg', M₀.act_fix hb s]
    · rw [← map_pow, hdgm, map_one]
  have hinner : ∀ (g : L') {t}, Act (MulAut.conj g) t →
      ∃ s, ∃ z ∈ Subgroup.center L', g = dg s * z := by
    rintro g t ⟨b, hb, hbl⟩
    have hbg : b = MulAut.conj (ψ g) := hindu hbl fun l => hconjind g l
    obtain ⟨h₀, hh₀⟩ := M₀.surj (ψ g)
    rw [hbg, ← hh₀] at hb
    obtain ⟨s, z₁, hz₁, hs⟩ := M₀.inner_diag h₀ hb
    rw [hZ, Subgroup.mem_bot] at hz₁
    rw [hz₁, mul_one, hh₀, ← hdg'] at hs
    refine ⟨s, (dg s)⁻¹ * g, hker (hfib _ _ hs.symm), by group⟩
  refine ⟨{ μ := M₀.μ
            ι := M₀.ι
            H := L'
            φ := MonoidHom.id L'
            surj := fun l => ⟨l, rfl⟩
            Act := Act
            act_one := ⟨1, M₀.act_one, fun _ => rfl⟩
            act_mul := ?_
            act_inv := ?_
            act_unique := ?_
            act_ratio := ?_
            act_const := ?_
            act_ratio_mem := ?_
            dgm := dg
            act_dgm := hAct_dgm
            act_fix := hfix
            ker_dgm := ?_
            Pm := Pm
            act_perm := ?_
            act_apply_perm := ?_
            inner_diag := hinner
            central_diag := ?_
            cent_diag := ?_
            heart_mem := ?_ }, fun a t => Iff.rfl, fun σ => hPm σ⟩
  · rintro a a' t t' ⟨b, hb, hbl⟩ ⟨b', hb', hbl'⟩
    exact ⟨b * b', M₀.act_mul hb hb', fun l => by
      rw [MulAut.mul_apply, MulAut.mul_apply, hbl', hbl]⟩
  · rintro a t ⟨b, hb, hbl⟩
    refine ⟨b⁻¹, M₀.act_inv hb, fun l => ?_⟩
    apply b.injective
    rw [MulAut.apply_inv_self, hbl, MulAut.apply_inv_self]
  · rintro a a' t ⟨b, hb, hbl⟩ ⟨b', hb', hbl'⟩
    have hbb : b = b' := M₀.act_unique hb hb'
    subst hbb
    exact hinj hbl hbl'
  · rintro a t u ⟨b, hb, hbl⟩ ⟨b', hb', hbl'⟩
    have hbb : b = b' := hindu hbl hbl'
    subst hbb
    exact M₀.act_ratio hb hb'
  · rintro a c ⟨b, hb, hbl⟩
    have hb1 : b = 1 := M₀.act_const c hb
    subst hb1
    exact hinj hbl fun l => rfl
  · rintro a t ⟨b, hb, -⟩ i j
    exact M₀.act_ratio_mem hb i j
  · intro s hs
    have hs' : dg s = 1 := hs
    apply M₀.ker_dgm s
    rw [← hdg', hs', map_one]
  · rintro a t σ ⟨b, hb, hbl⟩
    refine ⟨MulAut.conj (M₀.φ (M₀.Pm σ)) * b * (MulAut.conj (M₀.φ (M₀.Pm σ)))⁻¹,
      M₀.act_perm σ hb, fun l => ?_⟩
    rw [← hPm σ]
    exact TypeA.conj_induced_apply ψ hbl (Pm σ) l
  · rintro a t σ s hat hs
    obtain ⟨s₀, rfl⟩ := hAct_conj hat
    obtain ⟨b, hb, hbl⟩ := hat
    set y : L' := Pm σ * (dg s₀)⁻¹ * (Pm σ)⁻¹ with hy
    have hyc : MulAut.conj (Pm σ) * MulAut.conj (dg s₀⁻¹) * (MulAut.conj (Pm σ))⁻¹ =
        MulAut.conj y := by
      rw [hy]
      simp only [map_mul, map_inv]
    have hyact : Act (MulAut.conj y) (fun i => (s₀⁻¹ : ggTDTg M₀.μ N).1 (σ i)) := by
      have h1 := (show Act (MulAut.conj (dg s₀⁻¹)) ((s₀⁻¹ : ggTDTg M₀.μ N) :
        Fin (N + 1) → Kˣ) from hAct_dgm _)
      obtain ⟨c, hc, hcl⟩ := h1
      refine ⟨MulAut.conj (M₀.φ (M₀.Pm σ)) * c * (MulAut.conj (M₀.φ (M₀.Pm σ)))⁻¹,
        M₀.act_perm σ hc, fun l => ?_⟩
      rw [← hPm σ, TypeA.conj_induced_apply ψ hcl (Pm σ) l, hyc]
    obtain ⟨s₁, z, hz, hyz⟩ := hinner y hyact
    have hym : y ^ m = 1 := by
      rw [hy, conj_pow, inv_pow, hdgm, inv_one, mul_one, mul_inv_cancel]
    have hy1 : y = dg s₁ := hsame _ _ (by
      rw [hyz, map_mul, (show ψ z = 1 from hcen z hz), mul_one]) hym (hdgm s₁)
    have hval : MulAut.conj (dg s₀) (Pm σ) = dg (s₀ * s₁) * Pm σ := by
      rw [map_mul, ← hy1, hy, MulAut.conj_apply]
      group
    have hRs : ψ (dg (s₀ * s₁)) = ψ (dg s) := by
      have e1 := M₀.act_apply_perm σ s hb hs
      have e2 : b (ψ (Pm σ)) = ψ (MulAut.conj (dg s₀) (Pm σ)) := hbl (Pm σ)
      rw [hPm σ, e1, hval] at e2
      have e3 : ψ (dg (s₀ * s₁) * Pm σ) = ψ (dg s) * ψ (Pm σ) := by
        rw [← e2, map_mul M₀.φ, hdg', hPm σ]
      rw [map_mul ψ] at e3
      exact mul_right_cancel e3
    have hss : dg (s₀ * s₁) = dg s :=
      hsame _ _ hRs (hdgm _) (hdgm s)
    change MulAut.conj (dg s₀) (Pm σ) = dg s * Pm σ
    rw [hval, hss]
  · intro z hz hzodd
    refine ⟨1, ?_⟩
    show z = dg 1
    rw [map_one]
    have hzk := hcen z hz
    exact eq_one_of_isPGroup_two_of_pow_odd h2 (m := orderOf z) hzodd hzk (pow_orderOf_eq_one z)
  · intro ζ hζ hζ2 g hg
    obtain ⟨h₀, hh₀⟩ := M₀.surj (ψ g)
    obtain ⟨s, z₁, hz₁, hs⟩ := M₀.cent_diag hζ hζ2 h₀ (fun k l hkl s hs => by
      have h1 : MulAut.conj g * MulAut.conj (dg s) = MulAut.conj (dg s) * MulAut.conj g :=
        hg k l hkl s hs
      have h2 : MulAut.conj (g * dg s) = MulAut.conj (dg s * g) := by
        rw [map_mul, map_mul, h1]
      have h3 : (dg s * g)⁻¹ * (g * dg s) ∈ Subgroup.center L' := by
        rw [Subgroup.mem_center_iff]
        intro x
        have := congrArg (fun f : MulAut L' => f x) h2
        simp only [MulAut.conj_apply] at this
        calc x * ((dg s * g)⁻¹ * (g * dg s))
            = (dg s * g)⁻¹ * ((dg s * g) * x * (dg s * g)⁻¹) * (g * dg s) := by group
          _ = (dg s * g)⁻¹ * ((g * dg s) * x * (g * dg s)⁻¹) * (g * dg s) := by rw [this]
          _ = (dg s * g)⁻¹ * (g * dg s) * x := by group
      have h4 : ψ (g * dg s) = ψ (dg s * g) := by
        have h5 := hcen _ h3
        rw [MonoidHom.mem_ker, map_mul, map_inv] at h5
        exact (inv_mul_eq_one.mp h5).symm
      have h5 : ψ g * ψ (dg s) = ψ (dg s) * ψ g := by
        rw [← map_mul ψ, ← map_mul ψ, h4]
      rw [hh₀, ← hdg', ← map_mul (MulAut.conj : R →* MulAut R),
        ← map_mul (MulAut.conj : R →* MulAut R), h5])
    rw [hZ, Subgroup.mem_bot] at hz₁
    rw [hz₁, mul_one, hh₀, ← hdg'] at hs
    exact ⟨s, (dg s)⁻¹ * g, hker (hfib _ _ hs.symm), show g = dg s * ((dg s)⁻¹ * g) by group⟩
  · intro p A hsc hAT s hsp
    refine hsc (dg s) (fun a ha => ?_) ?_
    · obtain ⟨t, ht⟩ := hAT a ha
      exact hfix ht s
    · have hsp' : s ^ p = 1 := Subtype.ext (funext fun i => by
        simp only [Subgroup.coe_pow, Pi.pow_apply, Subgroup.coe_one, Pi.one_apply]
        exact hsp i)
      rw [← map_pow, hsp', map_one]

end Lift

end CFSG.StandardType

end
