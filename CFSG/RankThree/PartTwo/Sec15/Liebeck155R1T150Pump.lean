module

public import CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150Defs
public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3Thm90Y
public import CFSG.LocalAnalysis.SignalizerFunctor.SolvableNormalProducts

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.RankThree.PartTwo.Sec15.Sylow155R3.Thm90
open scoped commutatorElement

namespace Pump

theorem K150For.congr {J J' : Type} [Group J] [Group J'] (e : J ≃* J') (h : K150For J) :
    K150For J' := by
  intro S _ _ hS hs hna σ h3 h1 C P hC hPC hsn hP hZ N _ hJ
  obtain ⟨e'⟩ := hJ
  obtain ⟨⟨a⟩, b⟩ := h S hS hs hna σ h3 h1 C P hC hPC hsn hP hZ N ⟨e'.trans e.symm⟩
  exact ⟨⟨e.symm.trans a⟩, b⟩

theorem not_dvd_card_center_of_surjective {M Pb J : Type*} [Group M] [Group Pb] [Group J]
    (f : M →* Pb) (hf : Function.Surjective f) (ψ : Pb →* J) (hψ : Function.Surjective ψ)
    (hJ : Subgroup.center J = ⊥) {p : ℕ} (hp : ¬ p ∣ Nat.card (ψ.comp f).ker) :
    ¬ p ∣ Nat.card (Subgroup.center Pb) := by
  intro hdvd
  have hle : Subgroup.center Pb ≤ ψ.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    have hz : ψ g ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro y
      obtain ⟨b, rfl⟩ := hψ y
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hg b]
    rw [hJ] at hz
    exact hz
  have h1 : Nat.card (Subgroup.center Pb) ∣ Nat.card ψ.ker := Subgroup.card_dvd_of_le hle
  let g : (ψ.comp f).ker →* ψ.ker :=
    (f.comp (ψ.comp f).ker.subtype).codRestrict ψ.ker fun x => x.2
  have hg : Function.Surjective g := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := hf y
    exact ⟨⟨m, hy⟩, rfl⟩
  have h2 : Nat.card ψ.ker ∣ Nat.card (ψ.comp f).ker := Subgroup.card_dvd_of_surjective hg
  exact hp (hdvd.trans (h1.trans h2))

theorem eq_bot_of_normal_isSolvable {J : Type*} [Group J] (hJs : IsSimpleGroup J)
    (hJp : Group.IsPerfect J) (N : Subgroup J) [N.Normal] (hN : Group.IsSolvable N) : N = ⊥ := by
  have := hJs
  have := hJp
  have := hN
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal N with h | h
  · exact h
  · exfalso
    subst h
    have : Group.IsSolvable J :=
      solvable_of_surjective (f := (Subgroup.topEquiv (G := J)).toMonoidHom)
        (Subgroup.topEquiv (G := J)).surjective
    exact Group.IsPerfect.not_isSolvable J inferInstance

theorem center_eq_bot_of_simple {J : Type*} [Group J] (hJs : IsSimpleGroup J)
    (hJp : Group.IsPerfect J) : Subgroup.center J = ⊥ :=
  eq_bot_of_normal_isSolvable hJs hJp _
    (Group.isSolvable_of_comm fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a))

theorem le_ker_of_solvable {J : Type*} [Group J] (hJs : IsSimpleGroup J)
    (hJp : Group.IsPerfect J) {H : Type*} [Group H] (φ : H →* J) (hφ : Function.Surjective φ)
    (K : Subgroup H) [K.Normal] (hK : Group.IsSolvable K) : K ≤ φ.ker := by
  have := hK
  have : (K.map φ).Normal := Subgroup.Normal.map inferInstance φ hφ
  have : Group.IsSolvable (K.map φ) := solvable_of_surjective (f := φ.subgroupMap K)
    (MonoidHom.subgroupMap_surjective φ K)
  have h := eq_bot_of_normal_isSolvable hJs hJp (K.map φ) inferInstance
  rwa [Subgroup.map_eq_bot_iff] at h

theorem le_ker_of_normalizes {J : Type*} [Group J] (hJs : IsSimpleGroup J)
    (hJp : Group.IsPerfect J) {W : Type*} [Group W] (M K : Subgroup W) (hK : Group.IsSolvable K)
    (hMK : ∀ m ∈ M, ∀ k ∈ K, m * k * m⁻¹ ∈ K) (φ : M →* J) (hφ : Function.Surjective φ) :
    K.subgroupOf M ≤ φ.ker := by
  have := hK
  have : (K.subgroupOf M).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hMK g g.2 n hn⟩
  have : Group.IsSolvable (K.subgroupOf M) :=
    Group.isSolvable_of_isSolvable_injective
      (f := ((M.subtype.comp (K.subgroupOf M).subtype).codRestrict K fun x => x.2))
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : K => (x : W)) hab)))
  exact le_ker_of_solvable hJs hJp φ hφ _ inferInstance

theorem eq_top_of_perfect_subnormal {Q : Type*} [Group Q] [Finite Q] (hQ : CFSG.IsQuasisimple Q)
    {P : Subgroup Q} (hP : Group.IsPerfect P) (hsub : P.IsSubnormal) (hne : P ≠ ⊥) : P = ⊤ := by
  have hcomp : CFSG.IsComponent (⊤ : Subgroup Q) :=
    ⟨CFSG.LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hQ,
      Subgroup.IsSubnormal.top⟩
  rcases CFSG.LocalCores.component_subnormal_subgroup hcomp hsub with h | h
  · exact top_le_iff.mp h
  · exfalso
    apply hne
    have hle : (⊤ : Subgroup Q) ≤ Subgroup.centralizer (P : Set Q) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    have hab : ∀ a b : P, a * b = b * a := fun a b =>
      Subtype.ext ((Subgroup.mem_centralizer_iff.mp (hle (Subgroup.mem_top (b : Q))) a a.2))
    have : Nontrivial P := (Subgroup.nontrivial_iff_ne_bot P).mpr hne
    have := hP
    exact (Group.IsPerfect.not_isSolvable P (Group.isSolvable_of_comm hab)).elim

section Action

variable {Y : Type} [Group Y] [Finite Y]

abbrev ThetaCenterQuot (Λ : Subgroup Y) : Type :=
  (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) ⧸ Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ)

@[expose] noncomputable def actOnS (Λ : Subgroup Y) :
    ↥(Subgroup.normalizer (Λ : Set Y)) →* MulAut (ThetaCenterQuot Λ) :=
  (mulAutQuotientHom (Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ))).comp
    ((Sec4.thetaQuotMulAut ↥Λ).comp Λ.normalizerMonoidHom)

theorem actOnS_ne_one {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y) {c : Y}
    (hcN : c ∈ Subgroup.normalizer (Λ : Set Y)) (hc : c ∉ Sec4.thetaQuotCentralizer Λ) :
    actOnS Λ ⟨c, hcN⟩ ≠ 1 := by
  intro h1
  apply hc
  refine mem_thetaQuotCentralizer_iff'.mpr ⟨hcN, ?_⟩
  have : Group.IsPerfect (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) := hΛ.2.2.1
  refine KFacts.eq_one_of_forall_mul_inv_mem_center fun x => ?_
  have h := congrArg (fun τ : MulAut (ThetaCenterQuot Λ) =>
    τ ((x : ↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) : ThetaCenterQuot Λ)) h1
  have hσb : ∀ y : ↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ,
      actOnS Λ ⟨c, hcN⟩ ((y : ↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) : ThetaCenterQuot Λ) =
        ((Sec4.thetaQuotMulAut ↥Λ (Λ.normalizerMonoidHom ⟨c, hcN⟩) y :
          ↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) : ThetaCenterQuot Λ) := fun y => rfl
  simp only [hσb, MulAut.one_apply] at h
  exact QuotientGroup.eq.mp h.symm

@[expose] def A10Free (A : Subgroup Y) (c : Y) (L : Subgroup Y) (J : Type) [Group J] : Prop :=
  ∀ Λ ∈ thetaComponents 3 Y, A ≤ Subgroup.normalizer (Λ : Set Y) →
    L ≤ Λ ⊓ Subgroup.centralizer ({c} : Set Y) → c ∉ Sec4.thetaQuotCentralizer Λ →
    Nonempty (J ≃* alternatingGroup (Fin 7)) →
    Nonempty (ThetaCenterQuot Λ ≃* alternatingGroup (Fin 10)) → False

end Action

theorem fixedSubgroup_thetaQuotMulAut {H : Type} [Group H] [Finite H] (τ : MulAut H)
    (hτ3 : τ ^ 3 = 1) :
    fixedSubgroup (Sec4.thetaQuotMulAut H τ) =
      (fixedSubgroup τ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 H)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θ := aschbacherSolvableCore 3 H with hθ
  set σ := Sec4.thetaQuotMulAut H τ with hσdef
  have hσmk : ∀ l : H, σ (l : H ⧸ θ) = ((τ l : H) : H ⧸ θ) := fun l => rfl
  have hθτ : ∀ n ∈ θ, τ n ∈ θ := fun n hn => by
    have h := Sec4.map_aschbacherSolvableCore τ
    have h' : τ n ∈ (aschbacherSolvableCore 3 H).map (τ : H →* H) :=
      Subgroup.mem_map_of_mem (τ : H →* H) hn
    rw [h] at h'
    exact h'
  refine le_antisymm (fun y hy => ?_) ?_
  · obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective y
    have h1' : σ (l : H ⧸ θ) = (l : H ⧸ θ) := mem_fixedSubgroup.mp hy
    rw [hσmk] at h1'
    have h2' : l⁻¹ * τ l ∈ θ := QuotientGroup.eq.mp h1'.symm
    obtain ⟨n, hn, hnfix⟩ := exists_mul_fixed (p := 3) τ hτ3 θ hθτ
      three_not_dvd_card_aschbacherSolvableCore l h2'
    refine ⟨l * n, mem_fixedSubgroup.mpr hnfix, ?_⟩
    change ((l * n : H) : H ⧸ θ) = (l : H ⧸ θ)
    rw [QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff n).mpr hn, mul_one]
  · rintro _ ⟨l, hl, rfl⟩
    refine mem_fixedSubgroup.mpr ?_
    change σ (l : H ⧸ θ) = (l : H ⧸ θ)
    rw [hσmk, mem_fixedSubgroup.mp hl]

structure K150Config (J : Type) [Group J] {S : Type} [Group S] (σ : MulAut S)
    (P : Subgroup S) : Prop where
  pow_three : σ ^ 3 = 1
  ne_one : σ ≠ 1
  fixed : ∀ x ∈ P, σ x = x
  perfect : Group.IsPerfect P
  subnormal : SubnormalIn P (fixedSubgroup σ)
  center : ¬ 3 ∣ Nat.card (Subgroup.center ↥P)
  quotient : ∃ (N : Subgroup ↥P) (_ : N.Normal), Nonempty (↥P ⧸ N ≃* J)

theorem K150Config.apply {J : Type} [Group J] (hK : K150For J) {S : Type} [Group S] [Finite S]
    (hS : SectionFourHyp S) (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a)
    {σ : MulAut S} {P : Subgroup S} (h : K150Config J σ P) :
    Nonempty (J ≃* alternatingGroup (Fin 7)) ∧ Nonempty (S ≃* alternatingGroup (Fin 10)) := by
  obtain ⟨N, hN, hJ⟩ := h.quotient
  have := hN
  exact hK S hS hs hna σ h.pow_three h.ne_one (fixedSubgroup σ) P (fun x => Iff.rfl)
    (fun x hx => h.fixed x hx) h.subnormal h.perfect h.center N hJ

theorem perfect_fixed_config {J : Type} [Group J] (hJs : IsSimpleGroup J)
    (hJp : Group.IsPerfect J) {X : Type} [Group X] [Finite X] (hX : CFSG.IsQuasisimple X)
    (σ : MulAut X) (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (P : Subgroup X)
    (hPfix : ∀ x ∈ P, σ x = x) (hPperf : Group.IsPerfect P)
    (hPsub : SubnormalIn P (fixedSubgroup σ)) (ψ : P →* J) (hψ : Function.Surjective ψ)
    {M₀ : Type} [Group M₀] (f₀ : M₀ →* P) (hf₀ : Function.Surjective f₀)
    (hker3 : ¬ 3 ∣ Nat.card (ψ.comp f₀).ker) :
    K150Config J (mulAutQuotientHom (Subgroup.center X) σ)
      (P.map (QuotientGroup.mk' (Subgroup.center X))) := by
  have : Group.IsPerfect X := hX.1
  have := hPperf
  set Z := Subgroup.center X with hZ
  let σb : MulAut (X ⧸ Z) := mulAutQuotientHom Z σ
  have hσb : ∀ x : X, σb (x : X ⧸ Z) = ((σ x : X) : X ⧸ Z) := fun x => rfl
  have hσb3 : σb ^ 3 = 1 := by rw [← map_pow, hσ3, map_one]
  have hσb1 : σb ≠ 1 := by
    intro h1
    apply hσ1
    refine KFacts.eq_one_of_forall_mul_inv_mem_center fun x => ?_
    have h := congrArg (fun τ : MulAut (X ⧸ Z) => τ (x : X ⧸ Z)) h1
    simp only [hσb, MulAut.one_apply] at h
    exact QuotientGroup.eq.mp h.symm
  have hPC : P ≤ fixedSubgroup σ := fun x hx => hPfix x hx
  have hC0 : (fixedSubgroup σ).map (QuotientGroup.mk' Z) ≤ fixedSubgroup σb := by
    rintro _ ⟨c, hc, rfl⟩
    exact (hσb c).trans (by rw [mem_fixedSubgroup.mp hc]; rfl)
  have hnorm : SubnormalIn ((fixedSubgroup σ).map (QuotientGroup.mk' Z)) (fixedSubgroup σb) := by
    refine Subgroup.Normal.isSubnormal ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨c, hc, hcn⟩ := hn
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective (g : X ⧸ Z)
    have h1 : ((σ x : X) : X ⧸ Z) = (x : X ⧸ Z) := by
      have h2 := mem_fixedSubgroup.mp g.2
      rw [← hx] at h2
      exact h2
    have hz : x⁻¹ * σ x ∈ Z := QuotientGroup.eq.mp h1.symm
    have hzc := Subgroup.mem_center_iff.mp hz
    have hσx : σ x = x * (x⁻¹ * σ x) := by group
    have hCx : x * c * x⁻¹ ∈ fixedSubgroup σ := by
      rw [mem_fixedSubgroup, map_mul, map_mul, map_inv, mem_fixedSubgroup.mp hc]
      calc σ x * c * (σ x)⁻¹ = (x * (x⁻¹ * σ x)) * c * (x * (x⁻¹ * σ x))⁻¹ := by rw [← hσx]
        _ = x * ((x⁻¹ * σ x) * c) * (x⁻¹ * σ x)⁻¹ * x⁻¹ := by group
        _ = x * (c * (x⁻¹ * σ x)) * (x⁻¹ * σ x)⁻¹ * x⁻¹ := by rw [hzc c]
        _ = x * c * x⁻¹ := by group
    refine ⟨x * c * x⁻¹, hCx, ?_⟩
    change (QuotientGroup.mk' Z) (x * c * x⁻¹) = (g : X ⧸ Z) * (n : X ⧸ Z) * (g : X ⧸ Z)⁻¹
    rw [map_mul, map_mul, map_inv, hcn, ← hx]
    rfl
  have hPb_le : P.map (QuotientGroup.mk' Z) ≤ (fixedSubgroup σ).map (QuotientGroup.mk' Z) :=
    Subgroup.map_mono hPC
  have hsub : SubnormalIn (P.map (QuotientGroup.mk' Z)) (fixedSubgroup σb) :=
    SubnormalIn.trans hPb_le hC0 (SubnormalIn.map hPC (QuotientGroup.mk' Z) hPsub) hnorm
  have hPbperf : Group.IsPerfect (P.map (QuotientGroup.mk' Z)) :=
    Group.IsPerfect.map (QuotientGroup.mk' Z)
  have hJc : Subgroup.center J = ⊥ := center_eq_bot_of_simple hJs hJp
  have hker : ((QuotientGroup.mk' Z).subgroupMap P).ker ≤ ψ.ker := by
    intro p hp
    rw [MonoidHom.mem_ker] at hp ⊢
    have hpZ : (p : X) ∈ Z := by
      have h1 : (QuotientGroup.mk' Z) (p : X) = 1 := congrArg Subtype.val hp
      exact (QuotientGroup.eq_one_iff _).mp h1
    have hcen : ψ p ∈ Subgroup.center J := by
      rw [Subgroup.mem_center_iff]
      intro j
      obtain ⟨q, rfl⟩ := hψ j
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_center_iff.mp hpZ q)
    rw [hJc] at hcen
    exact hcen
  obtain ⟨ψb, hψb⟩ := exists_lift_of_surjective _ (MonoidHom.subgroupMap_surjective _ P) ψ hker
  have hψbs : Function.Surjective ψb := by
    intro j
    obtain ⟨p, rfl⟩ := hψ j
    exact ⟨_, hψb p⟩
  let f : M₀ →* ↥(P.map (QuotientGroup.mk' Z)) := ((QuotientGroup.mk' Z).subgroupMap P).comp f₀
  have hf : Function.Surjective f := (MonoidHom.subgroupMap_surjective _ P).comp hf₀
  have hψbf : ψb.comp f = ψ.comp f₀ := MonoidHom.ext fun m => hψb (f₀ m)
  have hZ3 : ¬ 3 ∣ Nat.card (Subgroup.center ↥(P.map (QuotientGroup.mk' Z))) :=
    not_dvd_card_center_of_surjective f hf ψb hψbs hJc (by rw [hψbf]; exact hker3)
  exact ⟨hσb3, hσb1, fun x hx => (hPb_le.trans hC0) hx, hPbperf, hsub, hZ3, ψb.ker, inferInstance,
    ⟨QuotientGroup.quotientKerEquivOfSurjective ψb hψbs⟩⟩

theorem acts_config {J : Type} [Group J] (hJs : IsSimpleGroup J) (hJp : Group.IsPerfect J)
    {Y : Type} [Group Y] [Finite Y] {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y) {c : Y}
    (hcN : c ∈ Subgroup.normalizer (Λ : Set Y)) (hc3 : c ^ 3 = 1)
    (hc : c ∉ Sec4.thetaQuotCentralizer Λ) {M : Subgroup Y}
    (hMc : M ≤ Subgroup.centralizer ({c} : Set Y))
    (hMsub : (M.subgroupOf (Subgroup.centralizer ({c} : Set Y))).IsSubnormal)
    (hMperf : Group.IsPerfect M) (hMΛ : M ≤ Λ) (φ : M →* J) (hφ : Function.Surjective φ)
    (hφ3 : ¬ 3 ∣ Nat.card φ.ker) :
    K150Config J (actOnS Λ ⟨c, hcN⟩)
      (((M.subgroupOf Λ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ))).map
        (QuotientGroup.mk' (Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ)))) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θY := aschbacherSolvableCore 3 Y with hθY
  set θΛ := aschbacherSolvableCore 3 ↥Λ with hθΛ
  have hθΛY : θΛ = θY.subgroupOf Λ :=
    aschbacherSolvableCore_eq_subgroupOf Nat.prime_three hΛ.2.1
  let τ : MulAut ↥Λ := Λ.normalizerMonoidHom ⟨c, hcN⟩
  have hτ : ∀ l : ↥Λ, ((τ l : ↥Λ) : Y) = c * (l : Y) * c⁻¹ := fun l => rfl
  have hτ3 : τ ^ 3 = 1 := by
    have h : (⟨c, hcN⟩ : Subgroup.normalizer (Λ : Set Y)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [← map_pow, h, map_one]
  let σ : MulAut (↥Λ ⧸ θΛ) := Sec4.thetaQuotMulAut ↥Λ τ
  have hσ3 : σ ^ 3 = 1 := by rw [← map_pow, hτ3, map_one]
  have hσ1 : σ ≠ 1 := fun h => hc (mem_thetaQuotCentralizer_iff'.mpr ⟨hcN, h⟩)
  have hfix : fixedSubgroup σ = (fixedSubgroup τ).map (QuotientGroup.mk' θΛ) :=
    fixedSubgroup_thetaQuotMulAut τ hτ3
  set P : Subgroup (↥Λ ⧸ θΛ) := (M.subgroupOf Λ).map (QuotientGroup.mk' θΛ) with hP
  have hMfix : M.subgroupOf Λ ≤ fixedSubgroup τ := fun m hm => by
    have hmc : (m : Y) * c = c * (m : Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hMc (Subgroup.mem_subgroupOf.mp hm))
    refine mem_fixedSubgroup.mpr (Subtype.ext ?_)
    rw [hτ, ← hmc, mul_inv_cancel_right]
  have hPfix : ∀ y ∈ P, σ y = y := by
    rintro _ ⟨m, hm, rfl⟩
    have h : (QuotientGroup.mk' θΛ) m ∈ fixedSubgroup σ := by
      rw [hfix]
      exact Subgroup.mem_map_of_mem _ (hMfix hm)
    exact mem_fixedSubgroup.mp h
  have hMΛperf : Group.IsPerfect (M.subgroupOf Λ) := by
    have := hMperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hMΛ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hMΛ).symm.surjective
  have : Group.IsPerfect (M.subgroupOf Λ) := hMΛperf
  have hPperf : Group.IsPerfect P := Group.IsPerfect.map (QuotientGroup.mk' θΛ)
  have hsub1 : SubnormalIn M (Subgroup.centralizer ({c} : Set Y)) := hMsub
  have hsub2 := SubnormalIn.subgroupOf Λ (inf_le_right : Subgroup.centralizer ({c} : Set Y) ⊓ Λ ≤ Λ)
    (SubnormalIn.inf Λ hsub1)
  rw [inf_eq_left.mpr hMΛ] at hsub2
  have hcent : (Subgroup.centralizer ({c} : Set Y) ⊓ Λ).subgroupOf Λ = fixedSubgroup τ := by
    ext l
    constructor
    · intro hl
      have hlc : (l : Y) * c = c * (l : Y) :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hl)).1
      refine mem_fixedSubgroup.mpr (Subtype.ext ?_)
      rw [hτ, ← hlc, mul_inv_cancel_right]
    · intro hl
      have hl' : c * (l : Y) * c⁻¹ = l := by
        have := congrArg Subtype.val (mem_fixedSubgroup.mp hl)
        rwa [hτ] at this
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, l.2⟩)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (l : Y) * c = (c * (l : Y) * c⁻¹) * c := by rw [hl']
        _ = c * (l : Y) := inv_mul_cancel_right _ _
  rw [hcent] at hsub2
  have hsub3 : SubnormalIn P (fixedSubgroup σ) := by
    rw [hfix]
    exact SubnormalIn.map hMfix (QuotientGroup.mk' θΛ) hsub2
  have hθsol : Group.IsSolvable θY :=
    (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
  have hker0 : θY.subgroupOf M ≤ φ.ker :=
    le_ker_of_normalizes hJs hJp M θY hθsol
      (fun m _ k hk => Subgroup.Normal.conj_mem inferInstance k hk m) φ hφ
  let φ' : ↥(M.subgroupOf Λ) →* J := φ.comp (Subgroup.subgroupOfEquivOfLe hMΛ).toMonoidHom
  have hφ' : Function.Surjective φ' := hφ.comp (Subgroup.subgroupOfEquivOfLe hMΛ).surjective
  have hker : ((QuotientGroup.mk' θΛ).subgroupMap (M.subgroupOf Λ)).ker ≤ φ'.ker := by
    intro m hm
    rw [MonoidHom.mem_ker] at hm ⊢
    have h1' : (QuotientGroup.mk' θΛ) (m : ↥Λ) = 1 := congrArg Subtype.val hm
    have h2' : (m : ↥Λ) ∈ θΛ := (QuotientGroup.eq_one_iff _).mp h1'
    rw [hθΛY, Subgroup.mem_subgroupOf] at h2'
    have h3 : (⟨((m : ↥Λ) : Y), Subgroup.mem_subgroupOf.mp m.2⟩ : ↥M) ∈ θY.subgroupOf M :=
      Subgroup.mem_subgroupOf.mpr h2'
    exact hker0 h3
  obtain ⟨ψ, hψ⟩ := exists_lift_of_surjective _ (MonoidHom.subgroupMap_surjective _ _) φ' hker
  have hψs : Function.Surjective ψ := by
    intro j
    obtain ⟨m, rfl⟩ := hφ' j
    exact ⟨_, hψ m⟩
  let f₀ : ↥M →* ↥P :=
    ((QuotientGroup.mk' θΛ).subgroupMap (M.subgroupOf Λ)).comp
      (Subgroup.subgroupOfEquivOfLe hMΛ).symm.toMonoidHom
  have hf₀ : Function.Surjective f₀ :=
    (MonoidHom.subgroupMap_surjective _ _).comp (Subgroup.subgroupOfEquivOfLe hMΛ).symm.surjective
  have hψf₀ : ψ.comp f₀ = φ := MonoidHom.ext fun m => by
    change ψ (((QuotientGroup.mk' θΛ).subgroupMap (M.subgroupOf Λ))
      ((Subgroup.subgroupOfEquivOfLe hMΛ).symm m)) = φ m
    rw [hψ]
    change φ ((Subgroup.subgroupOfEquivOfLe hMΛ) ((Subgroup.subgroupOfEquivOfLe hMΛ).symm m)) = φ m
    rw [MulEquiv.apply_symm_apply]
  exact perfect_fixed_config hJs hJp hΛ.2.2 σ hσ3 hσ1 P hPfix hPperf hsub3 ψ hψs f₀ hf₀
    (by rw [hψf₀]; exact hφ3)

theorem config_of_component {Y : Type} [Group Y] [Finite Y] {J : Type} [Group J]
    (hJs : IsSimpleGroup J) {c : Y} {L : Subgroup Y} (hL : L ∈ thetaComponentsAt 3 c)
    (eJ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* J) {Λ : Subgroup Y}
    (hΛ : Λ ∈ thetaComponents 3 Y) (hcN : c ∈ Subgroup.normalizer (Λ : Set Y)) (hc3 : c ^ 3 = 1)
    (hc : c ∉ Sec4.thetaQuotCentralizer Λ) (hLΛ : L ≤ Λ) :
    K150Config J (actOnS Λ ⟨c, hcN⟩)
      (((L.subgroupOf Λ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ))).map
        (QuotientGroup.mk' (Subgroup.center (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ)))) := by
  obtain ⟨hLc, hLsub, hLperf⟩ := thetaComponentsAt_facts hL
  have := hLperf
  have : Group.IsPerfect (↥L ⧸ aschbacherSolvableCore 3 ↥L) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
      (QuotientGroup.mk'_surjective _)
  have hJp : Group.IsPerfect J := Group.IsPerfect.ofSurjective (f := eJ.toMonoidHom) eJ.surjective
  let φ : ↥L →* J := eJ.toMonoidHom.comp (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L))
  have hφ : Function.Surjective φ := eJ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker = aschbacherSolvableCore 3 ↥L := by
    ext x
    rw [MonoidHom.mem_ker]
    change eJ (x : ↥L ⧸ aschbacherSolvableCore 3 ↥L) = 1 ↔ _
    rw [eJ.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hφ3 : ¬ 3 ∣ Nat.card φ.ker := by
    rw [hker]
    exact three_not_dvd_card_aschbacherSolvableCore
  exact acts_config hJs hJp hΛ hcN hc3 hc hLc hLsub hLperf hLΛ φ hφ hφ3

section Centralizes

variable {Y : Type} [Group Y] [Finite Y]

theorem image_eq_top {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y) {c : Y}
    (hcN : c ∈ Subgroup.normalizer (Λ : Set Y)) (hc3 : c ^ 3 = 1)
    (hcΛ : c ∈ Sec4.thetaQuotCentralizer Λ) {L : Subgroup Y}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set Y))
    (hLsub : (L.subgroupOf (Subgroup.centralizer ({c} : Set Y))).IsSubnormal)
    (hLperf : Group.IsPerfect L) (hLΛ : L ≤ Λ) (hL1 : L ≠ ⊥) :
    (L.subgroupOf Λ).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Λ)) = ⊤ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set θΛ := aschbacherSolvableCore 3 ↥Λ with hθΛ
  set π := QuotientGroup.mk' θΛ with hπ
  let τ : MulAut ↥Λ := Λ.normalizerMonoidHom ⟨c, hcN⟩
  have hτ : ∀ l : ↥Λ, ((τ l : ↥Λ) : Y) = c * (l : Y) * c⁻¹ := fun l => rfl
  have hτ3 : τ ^ 3 = 1 := by
    have h : (⟨c, hcN⟩ : Subgroup.normalizer (Λ : Set Y)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hc3)
    rw [← map_pow, h, map_one]
  let σ : MulAut (↥Λ ⧸ θΛ) := Sec4.thetaQuotMulAut ↥Λ τ
  have hσ1 : σ = 1 := (mem_thetaQuotCentralizer_iff'.mp hcΛ).choose_spec
  have hfix : fixedSubgroup σ = (fixedSubgroup τ).map π := fixedSubgroup_thetaQuotMulAut τ hτ3
  have hFtop : ∀ y : ↥Λ ⧸ θΛ, ∃ x ∈ fixedSubgroup τ, π x = y := by
    intro y
    have hy : y ∈ fixedSubgroup σ := by
      rw [hσ1]
      exact mem_fixedSubgroup.mpr rfl
    rw [hfix] at hy
    obtain ⟨x, hx, rfl⟩ := hy
    exact ⟨x, hx, rfl⟩
  set M₁ := L.subgroupOf Λ with hM₁
  set F := fixedSubgroup τ with hF
  have hMfix : M₁ ≤ F := fun m hm => by
    have hmc : (m : Y) * c = c * (m : Y) :=
      Subgroup.mem_centralizer_singleton_iff.mp (hLc (Subgroup.mem_subgroupOf.mp hm))
    refine mem_fixedSubgroup.mpr (Subtype.ext ?_)
    rw [hτ, ← hmc, mul_inv_cancel_right]
  have hMΛperf : Group.IsPerfect M₁ := by
    have := hLperf
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hLΛ).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hLΛ).symm.surjective
  have : Group.IsPerfect M₁ := hMΛperf
  have hsub1 : SubnormalIn L (Subgroup.centralizer ({c} : Set Y)) := hLsub
  have hsub2 := SubnormalIn.subgroupOf Λ (inf_le_right : Subgroup.centralizer ({c} : Set Y) ⊓ Λ ≤ Λ)
    (SubnormalIn.inf Λ hsub1)
  rw [inf_eq_left.mpr hLΛ] at hsub2
  have hcent : (Subgroup.centralizer ({c} : Set Y) ⊓ Λ).subgroupOf Λ = F := by
    ext l
    constructor
    · intro hl
      have hlc : (l : Y) * c = c * (l : Y) :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hl)).1
      refine mem_fixedSubgroup.mpr (Subtype.ext ?_)
      rw [hτ, ← hlc, mul_inv_cancel_right]
    · intro hl
      have hl' : c * (l : Y) * c⁻¹ = l := by
        have := congrArg Subtype.val (mem_fixedSubgroup.mp hl)
        rwa [hτ] at this
      refine Subgroup.mem_subgroupOf.mpr (Subgroup.mem_inf.mpr ⟨?_, l.2⟩)
      rw [Subgroup.mem_centralizer_singleton_iff]
      calc (l : Y) * c = (c * (l : Y) * c⁻¹) * c := by rw [hl']
        _ = c * (l : Y) := inv_mul_cancel_right _ _
  rw [hcent] at hsub2
  let g : ↥F →* ↥Λ ⧸ θΛ := π.comp F.subtype
  have hg : Function.Surjective g := by
    intro y
    obtain ⟨x, hx, rfl⟩ := hFtop y
    exact ⟨⟨x, hx⟩, rfl⟩
  have hPsub : ((M₁.subgroupOf F).map g).IsSubnormal := Subgroup.IsSubnormal.map hg hsub2
  have hPeq : (M₁.subgroupOf F).map g = M₁.map π := by
    change (M₁.subgroupOf F).map (π.comp F.subtype) = M₁.map π
    rw [← Subgroup.map_map, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hMfix]
  rw [hPeq] at hPsub
  have hPperf : Group.IsPerfect (M₁.map π) := Group.IsPerfect.map π
  have hne : M₁.map π ≠ ⊥ := by
    intro hbot
    have hle : M₁ ≤ θΛ := by
      have := (Subgroup.map_eq_bot_iff _).mp hbot
      rwa [hπ, QuotientGroup.ker_mk'] at this
    have : Group.IsSolvable θΛ :=
      (solvable_prime_complement_core_characterization (H := ↥Λ) Nat.prime_three).1
    have : Group.IsSolvable M₁ :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hle)
    have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
    have : Nontrivial ↥M₁ := (Subgroup.subgroupOfEquivOfLe hLΛ).symm.injective.nontrivial
    exact Group.IsPerfect.not_isSolvable M₁ inferInstance
  exact eq_top_of_perfect_subnormal hΛ.2.2 hPperf hPsub hne

theorem mem_normalizer_of_mem {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    {L X U : Subgroup Y} (hLperf : Group.IsPerfect L) (hLΛ : L ≤ Λ) (hL1 : L ≠ ⊥)
    (hLX : L ≤ X) (hUX : U ≤ X) (hXU : X ≤ Subgroup.normalizer (U : Set Y))
    (hUsol : Group.IsSolvable U) {u : Y} (hu : u ∈ U) :
    u ∈ Subgroup.normalizer (Λ : Set Y) := by
  by_contra hnot
  have hne : Λ.map (MulAut.conj u).toMonoidHom ≠ Λ := fun h =>
    hnot (Subgroup.mem_normalizer_iff_map_conj_eq.mpr h)
  have hΛu : Λ.map (MulAut.conj u).toMonoidHom ∈ thetaComponents 3 Y :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj u) hΛ
  have hθsol : Group.IsSolvable (aschbacherSolvableCore 3 Y) :=
    (solvable_prime_complement_core_characterization (H := Y) Nat.prime_three).1
  set N : Subgroup Y := X ⊓ aschbacherSolvableCore 3 Y with hN
  have hNsol : Group.IsSolvable N :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_right : N ≤ aschbacherSolvableCore 3 Y))
      (Subgroup.inclusion_injective _)
  have hNU : N ≤ Subgroup.normalizer (U : Set Y) := inf_le_left.trans hXU
  have hUN : Group.IsSolvable ↥(U ⊔ N) :=
    CFSG.SignalizerFunctor.Helpers.solvable_sup_of_normalizing U N hNU hUsol hNsol
  have hluu : ∀ x ∈ X, ∀ v ∈ U, x * v * x⁻¹ ∈ U := fun x hx v hv =>
    (Subgroup.mem_normalizer_iff.mp (hXU hx) v).mp hv
  have hcomm : ∀ l₁ ∈ L, ∀ l₂ ∈ L, ⁅l₂, l₁⁆ ∈ U ⊔ N := by
    intro l₁ hl₁ l₂ hl₂
    have hX₁ : l₁ ∈ X := hLX hl₁
    have hX₂ : l₂ ∈ X := hLX hl₂
    have hu' : u ∈ X := hUX hu
    have hwU : u * l₂ * u⁻¹ * l₂⁻¹ ∈ U := by
      have h3 := hluu l₂ hX₂ u⁻¹ (U.inv_mem hu)
      have h2 : u * l₂ * u⁻¹ * l₂⁻¹ = u * (l₂ * u⁻¹ * l₂⁻¹) := by group
      rw [h2]
      exact U.mul_mem hu h3
    have ha : u * l₂ * u⁻¹ ∈ Λ.map (MulAut.conj u).toMonoidHom := ⟨l₂, hLΛ hl₂, rfl⟩
    have hn := comm_mem_of_ne Nat.prime_three hΛu hΛ hne ha (hLΛ hl₁)
    have hpX : u * l₂ * u⁻¹ ∈ X := X.mul_mem (X.mul_mem hu' hX₂) (X.inv_mem hu')
    have hnN : u * l₂ * u⁻¹ * l₁ * (u * l₂ * u⁻¹)⁻¹ * l₁⁻¹ ∈ N :=
      ⟨X.mul_mem (X.mul_mem (X.mul_mem hpX hX₁) (X.inv_mem hpX)) (X.inv_mem hX₁), hn⟩
    have heq : ⁅l₂, l₁⁆ = (u * l₂ * u⁻¹ * l₂⁻¹)⁻¹ *
        (u * l₂ * u⁻¹ * l₁ * (u * l₂ * u⁻¹)⁻¹ * l₁⁻¹) * (l₁ * (u * l₂ * u⁻¹ * l₂⁻¹) * l₁⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [heq]
    exact (U ⊔ N).mul_mem ((U ⊔ N).mul_mem ((U ⊔ N).inv_mem (Subgroup.mem_sup_left hwU))
      (Subgroup.mem_sup_right hnN)) (Subgroup.mem_sup_left (hluu l₁ hX₁ _ hwU))
  have hLle : L ≤ U ⊔ N := by
    have h := Subgroup.isPerfect_iff.mp hLperf
    rw [← h]
    exact Subgroup.commutator_le.mpr fun l₂ hl₂ l₁ hl₁ => hcomm l₁ hl₁ l₂ hl₂
  have : Group.IsSolvable L :=
    Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLle)
  have : Nontrivial ↥L := (Subgroup.nontrivial_iff_ne_bot L).mpr hL1
  have := hLperf
  exact Group.IsPerfect.not_isSolvable L inferInstance

theorem mem_thetaQuotCentralizer_of_mem {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y) {c : Y}
    (hcN : c ∈ Subgroup.normalizer (Λ : Set Y)) (hc3 : c ^ 3 = 1)
    (hcΛ : c ∈ Sec4.thetaQuotCentralizer Λ) {L X U : Subgroup Y}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set Y))
    (hLsub : (L.subgroupOf (Subgroup.centralizer ({c} : Set Y))).IsSubnormal)
    (hLperf : Group.IsPerfect L) (hLΛ : L ≤ Λ) (hL1 : L ≠ ⊥) (hLX : L ≤ X) (hUX : U ≤ X)
    (hXU : X ≤ Subgroup.normalizer (U : Set Y)) (hUsol : Group.IsSolvable U) {u : Y}
    (hu : u ∈ U) : u ∈ Sec4.thetaQuotCentralizer Λ := by
  have huN := mem_normalizer_of_mem hΛ hLperf hLΛ hL1 hLX hUX hXU hUsol hu
  refine mem_thetaQuotCentralizer_iff'.mpr ⟨huN, ?_⟩
  set θΛ := aschbacherSolvableCore 3 ↥Λ with hθΛ
  have : Group.IsPerfect (↥Λ ⧸ θΛ) := hΛ.2.2.1
  have hquasi : CFSG.IsQuasisimple (↥Λ ⧸ θΛ) := hΛ.2.2
  have htop := image_eq_top hΛ hcN hc3 hcΛ hLc hLsub hLperf hLΛ hL1
  have hluu : ∀ x ∈ X, ∀ v ∈ U, x * v * x⁻¹ ∈ U := fun x hx v hv =>
    (Subgroup.mem_normalizer_iff.mp (hXU hx) v).mp hv
  set V : Subgroup ↥Λ := U.subgroupOf Λ with hV
  set V' : Subgroup (↥Λ ⧸ θΛ) := V.map (QuotientGroup.mk' θΛ) with hV'
  have hVsol : Group.IsSolvable V :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Λ.subtype.comp V.subtype).codRestrict U fun x => x.2)
      (fun a b hab => Subtype.ext (Subtype.ext (congrArg (fun x : U => (x : Y)) hab)))
  have hV'sol : Group.IsSolvable V' :=
    solvable_of_surjective (f := (QuotientGroup.mk' θΛ).subgroupMap V)
      (MonoidHom.subgroupMap_surjective _ V)
  have hV'n : V'.Normal := ⟨fun n hn g => by
    obtain ⟨v, hv, rfl⟩ := hn
    have hg : g ∈ (L.subgroupOf Λ).map (QuotientGroup.mk' θΛ) := htop ▸ Subgroup.mem_top g
    obtain ⟨m, hm, rfl⟩ := hg
    refine ⟨m * v * m⁻¹, ?_, by simp⟩
    exact hluu (m : Y) (hLX hm) (v : Y) hv⟩
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hquasi hV'n with hVtop | hcentral
  · exfalso
    have : Group.IsSolvable (↥Λ ⧸ θΛ) := by
      rw [hVtop] at hV'sol
      exact solvable_of_surjective (f := (Subgroup.topEquiv (G := ↥Λ ⧸ θΛ)).toMonoidHom)
        Subgroup.topEquiv.surjective
    have := CFSG.LocalCores.isQuasisimple_nontrivial hquasi
    exact Group.IsPerfect.not_isSolvable (↥Λ ⧸ θΛ) inferInstance
  · refine KFacts.eq_one_of_forall_mul_inv_mem_center fun a => ?_
    have ha : a ∈ (L.subgroupOf Λ).map (QuotientGroup.mk' θΛ) := htop ▸ Subgroup.mem_top a
    obtain ⟨m, hm, rfl⟩ := ha
    have hmV : m⁻¹ * Λ.normalizerMonoidHom ⟨u, huN⟩ m ∈ V := by
      change ((m : Y))⁻¹ * (u * (m : Y) * u⁻¹) ∈ U
      have e : ((m : Y))⁻¹ * (u * (m : Y) * u⁻¹) =
          (((m : Y))⁻¹ * u * (((m : Y))⁻¹)⁻¹) * u⁻¹ := by group
      rw [e]
      exact U.mul_mem (hluu _ (X.inv_mem (hLX hm)) u hu) (U.inv_mem hu)
    have h1 : (QuotientGroup.mk' θΛ m)⁻¹ *
        Sec4.thetaQuotMulAut ↥Λ (Λ.normalizerMonoidHom ⟨u, huN⟩) (QuotientGroup.mk' θΛ m) =
        QuotientGroup.mk' θΛ (m⁻¹ * Λ.normalizerMonoidHom ⟨u, huN⟩ m) := by
      rw [map_mul, map_inv]
      rfl
    rw [h1]
    exact hcentral (Subgroup.mem_map_of_mem _ hmV)

theorem comm_mem_theta_of_centralizes {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y) {c : Y}
    (hcN : c ∈ Subgroup.normalizer (Λ : Set Y)) (hc3 : c ^ 3 = 1)
    (hcΛ : c ∈ Sec4.thetaQuotCentralizer Λ) {L X U : Subgroup Y}
    (hLc : L ≤ Subgroup.centralizer ({c} : Set Y))
    (hLsub : (L.subgroupOf (Subgroup.centralizer ({c} : Set Y))).IsSubnormal)
    (hLperf : Group.IsPerfect L) (hLΛ : L ≤ Λ) (hL1 : L ≠ ⊥) (hLX : L ≤ X) (hUX : U ≤ X)
    (hXU : X ≤ Subgroup.normalizer (U : Set Y)) (hUsol : Group.IsSolvable U) :
    ∀ u ∈ U, ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ aschbacherSolvableCore 3 Y := fun _ hu _ hl =>
  comm_mem_of_mem_thetaQuotCentralizer hΛ.2.1
    (mem_thetaQuotCentralizer_of_mem hΛ hcN hc3 hcΛ hLc hLsub hLperf hLΛ hL1 hLX hUX hXU hUsol hu)
    (hLΛ hl)

end Centralizes

theorem pump150_of_acts {Y : Type} [Group Y] [Finite Y] (hY : SectionFourHyp Y)
    (h45 : Sec4.Item4_5) (h48 : Sec4.Item4_8) {A : Subgroup Y}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27) {c : Y} (hc : c ∈ A)
    (hc1 : c ≠ 1) {L : Subgroup Y} (hL : L ∈ thetaComponentsAt 3 c) (hL1 : L ≠ ⊥)
    {X U : Subgroup Y} (hLX : L ≤ X) (hUX : U ≤ X)
    (hXU : X ≤ Subgroup.normalizer (U : Set Y)) (hUsol : Group.IsSolvable U)
    (hacts : ∀ Λ ∈ thetaComponents 3 Y, A ≤ Subgroup.normalizer (Λ : Set Y) →
      L ≤ Λ ⊓ Subgroup.centralizer ({c} : Set Y) → c ∉ Sec4.thetaQuotCentralizer Λ →
      ∀ u ∈ U, ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ aschbacherSolvableCore 3 Y) :
    ∀ u ∈ U, ∀ l ∈ L, u * l * u⁻¹ * l⁻¹ ∈ aschbacherSolvableCore 3 Y := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hLc, hLsub, hLperf⟩ := thetaComponentsAt_facts hL
  have hApG : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 (g : Y) g.2)⟩
  have hn : ∃ n : ℕ, 3 ≤ n ∧ Nat.card A = 3 ^ n := ⟨3, le_rfl, by rw [hA27]; norm_num⟩
  obtain ⟨Λ, hΛ, hLΛ⟩ := h48 Y hY A hA hn c hc hc1 L hL
  have hAN : A ≤ Subgroup.normalizer (Λ : Set Y) := h45 Y hY A hApG (Or.inr ⟨hA, hn⟩) Λ hΛ
  by_cases hcc : c ∈ Sec4.thetaQuotCentralizer Λ
  · exact comm_mem_theta_of_centralizes hΛ (hAN hc) (hA.2 c hc) hcc hLc hLsub hLperf hLΛ hL1 hLX
      hUX hXU hUsol
  · exact hacts Λ hΛ hAN (le_inf hLΛ hLc) hcc

theorem mem_thetaQuotCentralizer_of_k150 {Y : Type} [Group Y] [Finite Y] (hY : SectionFourHyp Y)
    (h1 : Sec4.Item4_1LargePrime) (h2 : Sec4.Item4_1ThreeCover) {A : Subgroup Y}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) {c : Y} (hc : c ∈ A) {L : Subgroup Y}
    (hL : L ∈ thetaComponentsAt 3 c) {J : Type} [Group J]
    (eJ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* J) (hJs : IsSimpleGroup J) (hK : K150For J)
    (hA10 : A10Free A c L J) {Λ : Subgroup Y} (hΛ : Λ ∈ thetaComponents 3 Y)
    (hAN : A ≤ Subgroup.normalizer (Λ : Set Y))
    (hLΛ : L ≤ Λ ⊓ Subgroup.centralizer ({c} : Set Y)) : c ∈ Sec4.thetaQuotCentralizer Λ := by
  by_contra hcc
  have hX : CFSG.IsQuasisimple (↥Λ ⧸ aschbacherSolvableCore 3 ↥Λ) := hΛ.2.2
  have hS : SectionFourHyp (ThetaCenterQuot Λ) :=
    Sec4.Item41Narrow.sectionFourHyp_quotient_center h1 h2
      (Sec4.Item41Narrow.sectionFourHyp_thetaQuotient h1 hY hΛ) hX
  obtain ⟨h7, h10⟩ := (config_of_component hJs hL eJ hΛ (hAN hc) (hA.2 c hc) hcc
    (le_inf_iff.mp hLΛ).1).apply hK hS hX.2.1 hX.2.2
  exact hA10 Λ hΛ hAN hLΛ hcc h7 h10

end Pump

end CFSG.RankThree.PartTwo.Sec15.Liebeck155R1T150
