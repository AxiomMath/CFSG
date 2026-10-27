module

public import CFSG.Quasithin.EmptyFaithful.SBc2SzLift
public import CFSG.Quasithin.EmptyFaithful.R3c6Psl
public import CFSG.Quasithin.EmptyFaithful.R3c3Base
public import CFSG.Quasithin.EmptyFaithful.S146yBorelBender
public import CFSG.Quasithin.EmptyFaithful.S146yBorelL3

public section

namespace CFSG.Quasithin.R3c8

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

section Three

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {K : Type} [Field K]

theorem entries_of_comm (A : SpecialLinearGroup (Fin 3) K)
    (h1 : A * SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : K) =
      SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 1 by decide) (1 : K) * A)
    (h2 : A * SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : K) =
      SpecialLinearGroup.transvection (show (1 : Fin 3) ≠ 2 by decide) (1 : K) * A) :
    (A : Matrix (Fin 3) (Fin 3) K) 0 1 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) K) 1 0 = 0 ∧ (A : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 ∧
    (A : Matrix (Fin 3) (Fin 3) K) 1 1 = (A : Matrix (Fin 3) (Fin 3) K) 0 0 ∧
    (A : Matrix (Fin 3) (Fin 3) K) 2 2 = (A : Matrix (Fin 3) (Fin 3) K) 0 0 := by
  have e1 : (A : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : K)) =
      (1 + Matrix.single (0 : Fin 3) (1 : Fin 3) (1 : K)) * (A : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h1
    simpa [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe] using this
  have e2 : (A : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : K)) =
      (1 + Matrix.single (1 : Fin 3) (2 : Fin 3) (1 : K)) * (A : Matrix (Fin 3) (Fin 3) K) := by
    have := congrArg (fun g : SpecialLinearGroup (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K)) h2
    simpa [SpecialLinearGroup.coe_mul, SpecialLinearGroup.transvection_coe] using this
  rw [mul_add, add_mul, mul_one, one_mul, add_right_inj] at e1 e2
  have a1 := fun i j => congrFun (congrFun e1 i) j
  have a2 := fun i j => congrFun (congrFun e2 i) j
  simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.single_apply] at a1 a2
  have b1 := a2 0 2
  have b2 := a1 0 2
  have b3 := a1 1 1
  have b4 := a1 2 1
  have b5 := a2 2 2
  have b6 := a1 0 1
  have b7 := a2 1 2
  simp at b1 b2 b3 b4 b5 b6 b7
  refine ⟨b1, b2.symm, b3, b4, b5, b6.symm, ?_⟩
  exact b7.symm.trans b6.symm


theorem cent_projUnitriangular_three [Finite K] [CharP K 2] :
    ∀ x : projectiveSL 3 K, (∀ s ∈ projUnitriangular 3 K, x * s = s * x) →
      x ∈ projUnitriangular 3 K := by
  intro x hc
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hxN : x ∈ Subgroup.normalizer (projUnitriangular 3 K : Set (projectiveSL 3 K)) := by
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact (hc s hs).symm
  rw [normalizer_projUnitriangular (K := K) (n := 3) 2] at hxN
  obtain ⟨A, hA, rfl⟩ := hxN
  have hcomm : ∀ u ∈ unitriangular 3 K, A * u = u * A := by
    intro u hu
    have h1 := hc (proj 3 K u) (Subgroup.mem_map_of_mem _ hu)
    have h2 : proj 3 K (A * u * A⁻¹) = proj 3 K u := by
      rw [map_mul, map_mul, map_inv, h1]
      group
    have h3 : A * u * A⁻¹ = u :=
      proj_injOn_unitriangular 3 (conj_mem_unitriangular hA hu) hu h2
    calc A * u = (A * u * A⁻¹) * A := by group
      _ = u * A := by rw [h3]
  have h01 : (0 : Fin 3) < 1 := by decide
  have h12 : (1 : Fin 3) < 2 := by decide
  have h02 : (0 : Fin 3) < 2 := by decide
  obtain ⟨b01, b12, b10, b20, b21, b11, b22⟩ := entries_of_comm A
    (hcomm _ (K1.transvection_mem_unitriangular (K := K) h01 1))
    (hcomm _ (K1.transvection_mem_unitriangular (K := K) h12 1))
  set a : K := (A : Matrix (Fin 3) (Fin 3) K) 0 0 with ha
  set c : K := (A : Matrix (Fin 3) (Fin 3) K) 0 2 with hcdef
  have hdet : a ^ 3 = 1 := by
    have h := A.2
    rw [Matrix.det_fin_three] at h
    simp only [b01, b12, b10, b20, b21, b11, b22] at h
    rw [← ha] at h
    linear_combination h
  have ha0 : a ≠ 0 := by
    intro h
    rw [h] at hdet
    norm_num at hdet
  let au : Kˣ := Units.mk0 a ha0
  have hau : au ^ 3 = 1 := Units.ext (by simpa [au] using hdet)
  let z : SpecialLinearGroup (Fin 3) K := scalarElement au hau
  let u₀ : SpecialLinearGroup (Fin 3) K := SpecialLinearGroup.transvection h02.ne (c / a)
  have hu₀ : u₀ ∈ unitriangular 3 K := K1.transvection_mem_unitriangular (K := K) h02 (c / a)
  have hu₀coe : (u₀ : Matrix (Fin 3) (Fin 3) K) =
      1 + Matrix.single (0 : Fin 3) (2 : Fin 3) (c / a) :=
    SpecialLinearGroup.transvection_coe _ _
  have hzcoe : (z : Matrix (Fin 3) (Fin 3) K) = Matrix.scalar (Fin 3) a := rfl
  have hca : (A : Matrix (Fin 3) (Fin 3) K) 0 0 *
      ((A : Matrix (Fin 3) (Fin 3) K) 0 2 / (A : Matrix (Fin 3) (Fin 3) K) 0 0) =
      (A : Matrix (Fin 3) (Fin 3) K) 0 2 := by
    rw [← ha, ← hcdef]
    field_simp
  have hmat : (A : Matrix (Fin 3) (Fin 3) K) =
      (z : Matrix (Fin 3) (Fin 3) K) * (u₀ : Matrix (Fin 3) (Fin 3) K) := by
    rw [hzcoe, hu₀coe]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.single_apply,
        b01, b12, b10, b20, b21, b11, b22, ha, hcdef, hca]
  have hAeq : A = z * u₀ := by
    refine Matrix.SpecialLinearGroup.ext _ _ fun i j => ?_
    have := congrFun (congrFun hmat i) j
    simpa [SpecialLinearGroup.coe_mul] using this
  have hz : proj 3 K z = 1 := (proj_eq_one_iff).mpr (scalarElement_mem_scalars au hau)
  refine ⟨u₀, hu₀, ?_⟩
  rw [hAeq, map_mul, hz, one_mul]


end Three

section SylowCentral

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

@[expose] def SylowCent (Y : Type) [Group Y] : Prop :=
  ∀ S : Subgroup Y, IsSylowTwoOf S ⊤ → ∀ x : Y, (∀ s ∈ S, x * s = s * x) → x ∈ S

theorem SylowCent.of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) (h : SylowCent Y) :
    SylowCent X := by
  intro S hS x hx
  have hS' : IsSylowTwoOf (S.map e.toMonoidHom) ⊤ := by
    obtain ⟨hp, hi⟩ := K1.isSylowTwoOf_top_iff.mp hS
    refine K1.isSylowTwoOf_top_iff.mpr ⟨hp.map e.toMonoidHom, ?_⟩
    rw [Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
    exact hi
  have hx' : e x ∈ S.map e.toMonoidHom := by
    refine h _ hS' (e x) ?_
    rintro _ ⟨s, hs, rfl⟩
    show e x * e s = e s * e x
    rw [← map_mul, ← map_mul, hx s hs]
  obtain ⟨x', hx', hxx⟩ := hx'
  have : x' = x := e.injective hxx
  exact this ▸ hx'

theorem sylowCent_of_one {Y : Type} [Group Y] [Finite Y] {S₀ : Subgroup Y}
    (h₀ : IsSylowTwoOf S₀ ⊤)
    (h : ∀ x : Y, (∀ s ∈ S₀, x * s = s * x) → x ∈ S₀) : SylowCent Y := by
  intro S hS x hx
  obtain ⟨g, hg⟩ := exists_conj_of_isSylowTwoOf_top h₀ hS
  have h1 : g⁻¹ * x * g ∈ S₀ := by
    apply h
    intro s hs
    have hs' : g * s * g⁻¹ ∈ S := by
      rw [← hg]
      exact ⟨s, hs, by simp⟩
    have := hx _ hs'
    calc g⁻¹ * x * g * s = g⁻¹ * (x * (g * s * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * s * g⁻¹) * x) * g := by rw [this]
      _ = s * (g⁻¹ * x * g) := by group
  have h2 : g * (g⁻¹ * x * g) * g⁻¹ ∈ S := by
    rw [← hg]
    exact ⟨_, h1, rfl⟩
  have e : g * (g⁻¹ * x * g) * g⁻¹ = x := by group
  rwa [e] at h2

theorem sylowCent_psl3 {X : Type} [Group X] [Finite X] {f : ℕ} (h : IsPSL 3 2 f X) :
    SylowCent X := by
  obtain ⟨⟨hp, hf, -⟩, K, _, hKfin, hcard, ⟨e⟩⟩ := h
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two (by omega) hcard
  let e' : X ≃* projectiveSL 3 K := e.trans (K1.statedProjEquivProjectiveSL 3 K)
  refine SylowCent.of_mulEquiv e' ?_
  obtain ⟨S, hS⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  have h0 : IsSylowTwoOf (projUnitriangular 3 K) ⊤ := by
    rw [← hS]
    exact K1.isSylowTwoOf_top_iff.mpr ⟨S.isPGroup', S.not_dvd_index⟩
  exact sylowCent_of_one h0 cent_projUnitriangular_three

end SylowCentral

section Bender

open CFSG.ProperTwoGeneratedCore.TheoremC

theorem center_eq_bot_of_simple {Y : Type} [Group Y] [Finite Y] (hs : IsSimpleGroup Y)
    (h4 : 4 ∣ Nat.card Y) : Subgroup.center Y = ⊥ := by
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center Y) with h | h
  · exact h
  · exfalso
    have hc : IsMulCommutative Y := Subgroup.center_eq_top_iff.mp h
    have hp : (Nat.card Y).Prime := Group.is_simple_iff_prime_card.mp hs
    rcases (Nat.dvd_prime hp).mp h4 with h | h
    · omega
    · rw [← h] at hp
      norm_num at hp

theorem sylowCent_of_isBenderOf {n : ℕ} {Y : Type} [Group Y] [Finite Y]
    (hs : IsSimpleGroup Y) (h : E2.IsBenderOf n Y) : SylowCent Y := by
  intro S hS x hx
  obtain ⟨Q, rfl⟩ := exists_sylow_of_isSylowTwoOf_top hS
  have facts := benderBorelFactsHold Y (isBenderGroup_of_isBenderOf h) Q
  have hfix : ∀ q ∈ (Q : Subgroup Y), (MulAut.conj x) q = q := by
    intro q hq
    show x * q * x⁻¹ = q
    rw [hx q hq]
    group
  obtain ⟨r, hrQ, hr⟩ := facts.aut_inner (MulAut.conj x) hfix
  have h4 : 4 ∣ Nat.card Y := by
    have hcard := facts.center_card
    have hle : Nat.card {w : Y // InCenterOf (Q : Subgroup Y) w} ≤ Nat.card ↥(Q : Subgroup Y) :=
      Nat.card_le_card_of_injective (fun w => (⟨w.1, w.2.1⟩ : ↥(Q : Subgroup Y)))
        (fun a b hab => Subtype.ext (congrArg (fun z : ↥(Q : Subgroup Y) => (z : Y)) hab))
    obtain ⟨k, hk⟩ := (Q.isPGroup').exists_card_eq
    have h4k : 4 ≤ 2 ^ k := by rw [← hk]; omega
    have hk2 : 2 ≤ k := by
      by_contra hk2
      have : 2 ^ k ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    have : 4 ∣ Nat.card ↥(Q : Subgroup Y) := by
      rw [hk]
      exact (pow_dvd_pow 2 hk2 : 2 ^ 2 ∣ 2 ^ k)
    exact this.trans (Subgroup.card_subgroup_dvd_card _)
  have hZ := center_eq_bot_of_simple hs h4
  have hcen : r⁻¹ * x ∈ Subgroup.center Y := by
    rw [Subgroup.mem_center_iff]
    intro k
    have h1 : x * k * x⁻¹ = r * k * r⁻¹ := hr k
    calc k * (r⁻¹ * x) = r⁻¹ * (r * k * r⁻¹) * x := by group
      _ = r⁻¹ * (x * k * x⁻¹) * x := by rw [h1]
      _ = r⁻¹ * x * k := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at hcen
  rw [← hcen]
  exact hrQ

end Bender

section Pkg

structure BorelPkg (Y : Type) [Group Y] : Prop where
  rigid : BorelRigid Y
  cent : SylowCent Y

theorem borelPkg_psl3 {X : Type} [Group X] [Finite X] {f : ℕ} (hf : 2 ≤ f) (h : IsPSL 3 2 f X) :
    BorelPkg X :=
  ⟨borelRigid_psl3 hf h, sylowCent_psl3 h⟩

theorem borelPkg_psu3 {X : Type} [Group X] [Finite X] {f : ℕ}
    (h : IsPSU 3 2 f X) : BorelPkg X := by
  have hs : IsSimpleGroup X := (R3c6.psu3Data h).2.1
  have hf : 2 ≤ f := by
    obtain ⟨⟨-, hf1, -, hne⟩, -⟩ := h
    by_contra hlt
    have : f = 1 := by omega
    subst this
    exact hne (by norm_num)
  have hb : E2.IsBenderOf f X := ⟨hf, Or.inr (Or.inr h)⟩
  exact ⟨borelRigid_of_isBenderOf hb, sylowCent_of_isBenderOf hs hb⟩

end Pkg

section Lift

variable {G : Type} [Group G] [Finite G]

theorem borelLift_of_pkg {L Q : Subgroup G} (hq : CFSG.IsQuasisimple ↥L)
    (hZ : centerOf L = pCoreOf 2 L) (hQ : IsSylowTwoOf Q L)
    (hY : BorelPkg (↥L ⧸ Subgroup.center ↥L)) :
    (∀ x ∈ L, (∀ p ∈ Q, x * p * x⁻¹ * p⁻¹ ∈ centerOf L) → x ∈ Q) ∧
    (∀ v : G, v ∈ Subgroup.normalizer (L : Set G) → v * v = 1 →
      (∀ b ∈ L ⊓ Subgroup.normalizer (Q : Set G), v * b = b * v) →
        v ∈ Subgroup.centralizer (L : Set G)) := by
  have hPL : Q ≤ L := hQ.1
  have hZP : ∀ z ∈ Subgroup.center ↥L, (z : G) ∈ Q := by
    intro z hz
    have h1 : (z : G) ∈ centerOf L := SBc2.mem_centerOf_iff_center.mpr hz
    rw [hZ] at h1
    exact QuasithinUnique.EscapingLocal.pCoreOf_le_of_isSylowTwoOf hQ h1
  have hchar : (Subgroup.center ↥L).Characteristic := inferInstance
  set Z : Subgroup ↥L := Subgroup.center ↥L with hZdef
  set π : ↥L →* ↥L ⧸ Z := QuotientGroup.mk' Z with hπ
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hker : π.ker = Z := QuotientGroup.ker_mk' Z
  set P' : Subgroup ↥L := Q.subgroupOf L with hP'
  have hZP' : Z ≤ P' := fun z hz => Subgroup.mem_subgroupOf.mpr (hZP z hz)
  let Tsyl : Sylow 2 (↥L ⧸ Z) := (A4.toSylow hQ).mapSurjective (QuotientGroup.mk'_surjective _)
  set T : Subgroup (↥L ⧸ Z) := (Tsyl : Subgroup (↥L ⧸ Z)) with hTdef
  have hT : T = P'.map π := by
    rw [hTdef, Sylow.coe_mapSurjective, A4.toSylow_coe]
  have hTsyl : IsSylowTwoOf T ⊤ :=
    K1.isSylowTwoOf_top_iff.mpr ⟨Tsyl.isPGroup', Tsyl.not_dvd_index⟩
  have hTcomap : T.comap π = P' := by
    rw [hT]
    exact Subgroup.comap_map_eq_self (by rw [hker]; exact hZP')
  have hNcomap : (Subgroup.normalizer (T : Set (↥L ⧸ Z))).comap π =
      Subgroup.normalizer (P' : Set ↥L) := by
    rw [Subgroup.comap_normalizer_eq_of_surjective T hsurj, hTcomap]
  refine ⟨?_, ?_⟩
  · intro x hx hcomm
    have hxπ : ∀ t ∈ T, π ⟨x, hx⟩ * t = t * π ⟨x, hx⟩ := by
      intro t ht
      rw [hT] at ht
      obtain ⟨p', hp', rfl⟩ := ht
      have hc : (⟨x, hx⟩ * p' * ⟨x, hx⟩⁻¹ * p'⁻¹ : ↥L) ∈ Z := by
        have := hcomm (p' : G) (Subgroup.mem_subgroupOf.mp hp')
        exact SBc2.mem_centerOf_iff_center.mp this
      have hπc : π (⟨x, hx⟩ * p' * ⟨x, hx⟩⁻¹ * p'⁻¹) = 1 := by
        rw [← MonoidHom.mem_ker, hker]
        exact hc
      have key : π (⟨x, hx⟩ * p') = π (p' * ⟨x, hx⟩) := by
        have e : (⟨x, hx⟩ * p' : ↥L) =
            (⟨x, hx⟩ * p' * ⟨x, hx⟩⁻¹ * p'⁻¹) * (p' * ⟨x, hx⟩) := by group
        rw [e, map_mul, hπc, one_mul]
      rw [← map_mul, ← map_mul]
      exact key
    have hxT : π ⟨x, hx⟩ ∈ T := hY.cent T hTsyl _ hxπ
    have : (⟨x, hx⟩ : ↥L) ∈ T.comap π := hxT
    rw [hTcomap] at this
    exact Subgroup.mem_subgroupOf.mp this
  · intro v hvL hv2 hvc
    set α : MulAut (↥L ⧸ Z) := SteinbergBS.conjQuotientHom L Z ⟨v, hvL⟩ with hα
    have hαl : ∀ l : ↥L, α (π l) = π (Subgroup.normalizerMonoidHom L ⟨v, hvL⟩ l) := fun l => rfl
    have hαcoe : ∀ l : ↥L,
        ((Subgroup.normalizerMonoidHom L ⟨v, hvL⟩ l : ↥L) : G) = v * l * v⁻¹ := fun l =>
      Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨v, hvL⟩ l
    have hαinv : ∀ y, α (α y) = y := by
      intro y
      obtain ⟨l, rfl⟩ := hsurj y
      rw [hαl, hαl]
      congr 1
      apply Subtype.ext
      rw [hαcoe, hαcoe]
      calc v * (v * (l : G) * v⁻¹) * v⁻¹ = (v * v) * (l : G) * (v * v)⁻¹ := by group
        _ = l := by rw [hv2]; group
    have hαfix : ∀ b ∈ Subgroup.normalizer (T : Set (↥L ⧸ Z)), α b = b := by
      intro b hb
      obtain ⟨l, rfl⟩ := hsurj b
      have hl : l ∈ Subgroup.normalizer (P' : Set ↥L) := by rw [← hNcomap]; exact hb
      have hlN : (l : G) ∈ Subgroup.normalizer (Q : Set G) :=
        (SBc2.mem_normalizer_subgroupOf_iff hPL l).mp hl
      have hlB : (l : G) ∈ L ⊓ Subgroup.normalizer (Q : Set G) := ⟨l.2, hlN⟩
      have hcomm := hvc _ hlB
      rw [hαl]
      congr 1
      apply Subtype.ext
      rw [hαcoe]
      calc v * (l : G) * v⁻¹ = (l : G) * v * v⁻¹ := by rw [hcomm]
        _ = l := by group
    have hα1 : α = 1 := hY.rigid T hTsyl α hαinv hαfix
    have hvCq : v ∈ SteinbergBS.quotientCentralizer (⊤ : Subgroup G) L Z := by
      rw [SteinbergBS.mem_quotientCentralizer_iff]
      refine ⟨Subgroup.mem_top _, hvL, fun l hl => ?_⟩
      have h := congrArg (fun f : MulAut (↥L ⧸ Z) => f (π ⟨l, hl⟩)) hα1
      simp only [MulAut.one_apply] at h
      rw [hαl, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_iff_div_mem] at h
      refine ⟨_, h, ?_⟩
      simp [hαcoe, div_eq_mul_inv]
    have hle : ⁅L, SteinbergBS.quotientCentralizer (⊤ : Subgroup G) L Z⁆ ≤
        Subgroup.centralizer (L : Set G) := by
      rw [Subgroup.commutator_le]
      intro l hl x hx
      rw [SteinbergBS.mem_quotientCentralizer_iff] at hx
      obtain ⟨-, -, hx3⟩ := hx
      have hxl := hx3 l hl
      have hmem : ⁅l, x⁆ ∈ Z.map L.subtype := by
        have := (Z.map L.subtype).inv_mem hxl
        have e : ⁅l, x⁆ = (x * l * x⁻¹ * l⁻¹)⁻¹ := by
          simp [commutatorElement_def, mul_assoc]
        rw [e]
        exact this
      obtain ⟨z, hz, hzeq⟩ := hmem
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have := Subgroup.mem_center_iff.mp hz ⟨g, hg⟩
      rw [← hzeq]
      exact congrArg Subtype.val this
    have hbot := S153D.commutator_eq_bot_of_quasisimple hq hle
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hm : ⁅l, v⁆ ∈ ⁅L, SteinbergBS.quotientCentralizer (⊤ : Subgroup G) L Z⁆ :=
      Subgroup.commutator_mem_commutator hl hvCq
    rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at hm
    exact hm

end Lift

section Family

variable {G : Type} [Group G] [Finite G]

theorem nine_dvd_card_of_pRank_two {L : Subgroup G} (hr : CFSG.Open.pRank 3 L = 2) :
    9 ∣ Nat.card ↥L := by
  classical
  set s : Set ℕ := {k | ∃ E : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ k} with hs
  have hr' : sSup s = 2 := hr
  have hbdd : BddAbove s := by
    refine ⟨Nat.card G, fun k hk => ?_⟩
    obtain ⟨E, -, -, hE⟩ := hk
    have h1 : Nat.card E ≤ Nat.card G :=
      Nat.card_le_card_of_injective E.subtype E.subtype_injective
    have h2 : k < 3 ^ k := Nat.lt_pow_self (by norm_num)
    omega
  have hne : s.Nonempty := by
    by_contra h
    rw [Set.not_nonempty_iff_eq_empty] at h
    rw [h] at hr'
    simp at hr'
  have hmem : 2 ∈ s := hr' ▸ Nat.sSup_mem hne hbdd
  obtain ⟨E, hEL, -, hE⟩ := hmem
  have := Subgroup.card_dvd_of_le hEL
  rwa [hE] at this

theorem borelPkg_of_family {L : Subgroup G}
    (hZ : centerOf L = pCoreOf 2 L) (hr : CFSG.Open.pRank 3 L = 2)
    (hfam : (∃ n : ℕ, IsPSL 3 2 n (↥L ⧸ Subgroup.center ↥L)) ∨
      (∃ n : ℕ, IsPSU 3 2 n (↥L ⧸ Subgroup.center ↥L))) :
    BorelPkg (↥L ⧸ Subgroup.center ↥L) := by
  rcases hfam with ⟨n, hn⟩ | ⟨n, hn⟩
  · have hn2 : 2 ≤ n := by
      by_contra hlt
      obtain ⟨-, -, -, hn1, hcard⟩ := R3c6.psl3Data hn
      have hn1' : n = 1 := by omega
      subst hn1'
      have h168 : Nat.card (↥L ⧸ Subgroup.center ↥L) = 168 := by
        norm_num at hcard
        omega
      have h9 := nine_dvd_card_of_pRank_two hr
      have hcardL := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥L)
      obtain ⟨a, ha⟩ := (R3c3.isPGroup_two_center hZ).exists_card_eq
      rw [hcardL, h168, ha] at h9
      have hcop : Nat.Coprime 9 (2 ^ a) := Nat.Coprime.pow_right a (by norm_num)
      have : 9 ∣ 168 := hcop.dvd_of_dvd_mul_right h9
      omega
    exact borelPkg_psl3 hn2 hn
  · exact borelPkg_psu3 hn

end Family

end CFSG.Quasithin.R3c8
