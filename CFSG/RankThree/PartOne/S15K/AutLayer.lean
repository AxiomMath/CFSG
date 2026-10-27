module

public import CFSG.RankThree.PartOne.S15K.CentralCover
public import CFSG.RankThree.PartOne.S15K.LayerData

public section

namespace CFSG.RankThree.PartOne.S15K

open scoped commutatorElement
open CFSG CFSG.RankThree.PartOne.KCUnitary

section Def

variable {P : Type*} [Group P]

@[expose] def fixedSub (β : MulAut P) : Subgroup P where
  carrier := {t | β t = t}
  mul_mem' {a b} ha hb := by
    change β (a * b) = a * b
    rw [map_mul]
    exact congrArg₂ (· * ·) ha hb
  one_mem' := map_one β
  inv_mem' {a} ha := by
    change β a⁻¹ = a⁻¹
    rw [map_inv]
    exact congrArg (·⁻¹) ha

structure AutLayerFamily (p : ℕ) (β : MulAut P) (S : Set (MulAut P)) {ι : Type*}
    (F : ι → Subgroup P) : Prop where
  le : ∀ i, F i ≤ fixedSub β
  comp : ∀ i, IsComponent ((F i).subgroupOf (fixedSub β))
  perfect : ∀ Y : Subgroup P, Y ≤ fixedSub β → Group.IsPerfect ↥Y → Y ≤ ⨆ i, F i
  inner : ∀ α ∈ S, ∀ i, ∃ x ∈ F i, ∀ u ∈ F i, α u = x * u * x⁻¹
  center : ∀ i, ∀ u ∈ F i, (∀ f ∈ F i, u * f = f * u) → u ^ p = 1 → u = 1

end Def

section Fixed

theorem exists_fixedPoint_of_iterate_eq_id {S : Type*} [Finite S] {p : ℕ} (hp : p.Prime)
    (φ : S → S) (hφ : φ^[p] = id) (hS : ¬ p ∣ Nat.card S) : ∃ s, φ s = s := by
  classical
  have := Fintype.ofFinite S
  have : Fact p.Prime := ⟨hp⟩
  let f : Function.End S := φ
  have hf : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    exact hφ
  have h := Equiv.Perm.card_fixedPoints_modEq (f := f) (p := p) (n := 1) hf
  by_contra hno
  have h0 : Fintype.card f.fixedPoints = 0 := by
    rw [Fintype.card_eq_zero_iff]
    exact ⟨fun ⟨s, hs⟩ => hno ⟨s, hs⟩⟩
  rw [h0] at h
  apply hS
  rw [Nat.card_eq_fintype_card]
  exact (Nat.modEq_zero_iff_dvd.mp h)

variable {I' P : Type*} [Group I'] [Group P]

theorem card_fibre (ψ : I' →* P) (y₀ : I') :
    Nat.card {y : I' // ψ y = ψ y₀} = Nat.card ψ.ker :=
  Nat.card_congr
    { toFun := fun y => ⟨y₀⁻¹ * y.1, by
        rw [MonoidHom.mem_ker, map_mul, map_inv, y.2, inv_mul_cancel]⟩
      invFun := fun k => ⟨y₀ * k.1, by
        rw [map_mul, MonoidHom.mem_ker.mp k.2, mul_one]⟩
      left_inv := fun y => Subtype.ext (by simp)
      right_inv := fun k => Subtype.ext (by simp) }

theorem exists_fixed_lift [Finite I'] {p : ℕ} (hp : p.Prime) (ψ : I' →* P)
    (hψ : Function.Surjective ψ) (hnd : ¬ p ∣ Nat.card ψ.ker) (σ : MulAut I') (hσp : σ ^ p = 1)
    (β : MulAut P) (hσβ : ∀ y, ψ (σ y) = β (ψ y)) {t : P} (ht : β t = t) :
    ∃ y : I', σ y = y ∧ ψ y = t := by
  obtain ⟨y₀, rfl⟩ := hψ t
  let φ : {y : I' // ψ y = ψ y₀} → {y : I' // ψ y = ψ y₀} :=
    fun s => ⟨σ s.1, by rw [hσβ, s.2, ht]⟩
  have hiter : ∀ (n : ℕ) (s : {y : I' // ψ y = ψ y₀}), (φ^[n] s).1 = (σ ^ n) s.1 := by
    intro n
    induction n with
    | zero => intro s; rfl
    | succ n ih =>
      intro s
      rw [Function.iterate_succ_apply', pow_succ', MulAut.mul_apply, ← ih s]
  have hφ : φ^[p] = id := by
    funext s
    apply Subtype.ext
    rw [hiter, hσp]
    rfl
  obtain ⟨s, hs⟩ := exists_fixedPoint_of_iterate_eq_id hp φ hφ (by rwa [card_fibre])
  exact ⟨s.1, congrArg Subtype.val hs, s.2⟩

end Fixed

section Cover

variable {G : Type} [Group G] [Finite G]

theorem exists_cover {p : ℕ} (hp : p.Prime) {E I : Subgroup G} {P : Type} [Group P]
    (e₀ : ↥I ⧸ Subgroup.center ↥I ≃* P) (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥I)) {b : G} (hb : b ∈ E) (hbp : b ^ p = 1) (β : MulAut P)
    (hβ : ∀ y : ↥I, β (e₀ (y : ↥I ⧸ Subgroup.center ↥I)) =
      e₀ ((I.normalizerMonoidHom ⟨b, hEI hb⟩ y : ↥I) : ↥I ⧸ Subgroup.center ↥I)) :
    ∃ Φ : ↥(I ⊓ Subgroup.centralizer ({b} : Set G)) →* ↥(fixedSub β),
      Function.Surjective Φ ∧
        Φ.ker ≤ Subgroup.center ↥(I ⊓ Subgroup.centralizer ({b} : Set G)) ∧
        ¬ p ∣ Nat.card Φ.ker ∧
        ∀ y, ((Φ y : ↥(fixedSub β)) : P) =
          e₀ ((⟨(y : G), y.2.1⟩ : ↥I) : ↥I ⧸ Subgroup.center ↥I) := by
  classical
  set Hs : Subgroup G := I ⊓ Subgroup.centralizer ({b} : Set G) with hHs
  let ψ : ↥I →* P := e₀.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥I))
  have hψ : ∀ y : ↥I, ψ y = e₀ (y : ↥I ⧸ Subgroup.center ↥I) := fun _ => rfl
  have hψsurj : Function.Surjective ψ :=
    e₀.surjective.comp (QuotientGroup.mk'_surjective _)
  have hψker : ψ.ker = Subgroup.center ↥I := by
    ext y
    rw [MonoidHom.mem_ker, hψ, MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff y
  set σ : MulAut ↥I := I.normalizerMonoidHom ⟨b, hEI hb⟩ with hσ
  have hσp : σ ^ p = 1 := by
    rw [hσ, ← map_pow]
    have : (⟨b, hEI hb⟩ : ↥(Subgroup.normalizer (I : Set G))) ^ p = 1 :=
      Subtype.ext (by simpa using hbp)
    rw [this, map_one]
  have hσcoe : ∀ y : ↥I, ((σ y : ↥I) : G) = b * y * b⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe I ⟨b, hEI hb⟩ y
  have hσψ : ∀ y, ψ (σ y) = β (ψ y) := fun y => (hβ y).symm
  have hnd : ¬ p ∣ Nat.card ψ.ker := by rwa [hψker]
  let incl : ↥Hs →* ↥I := Subgroup.inclusion inf_le_left
  have hfix : ∀ y : ↥Hs, β (ψ (incl y)) = ψ (incl y) := by
    intro y
    rw [← hσψ]
    congr 1
    apply Subtype.ext
    rw [hσcoe]
    have hy2 : (y : G) ∈ Subgroup.centralizer ({b} : Set G) := y.2.2
    have : (y : G) * b = b * (y : G) := Subgroup.mem_centralizer_singleton_iff.mp hy2
    change b * (y : G) * b⁻¹ = (y : G)
    rw [← this, mul_inv_cancel_right]
  let Φ : ↥Hs →* ↥(fixedSub β) := (ψ.comp incl).codRestrict (fixedSub β) hfix
  have hΦv : ∀ y : ↥Hs, ((Φ y : ↥(fixedSub β)) : P) = ψ (incl y) := fun _ => rfl
  have hΦsurj : Function.Surjective Φ := by
    intro t
    obtain ⟨y, hyσ, hyt⟩ := exists_fixed_lift hp ψ hψsurj hnd σ hσp β hσψ (t := (t : P)) t.2
    have hyG : (y : G) * b = b * (y : G) := by
      have := congrArg Subtype.val hyσ
      rw [hσcoe] at this
      calc (y : G) * b = b * y * b⁻¹ * b := by rw [this]
        _ = b * (y : G) := by group
    refine ⟨⟨(y : G), y.2, Subgroup.mem_centralizer_singleton_iff.mpr hyG⟩, Subtype.ext ?_⟩
    rw [hΦv]
    exact hyt
  have hΦker : Φ.ker ≤ Subgroup.center ↥Hs := by
    intro y hy
    have h1 : ψ (incl y) = 1 := by
      have := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
      rwa [hΦv] at this
    have h2 : incl y ∈ Subgroup.center ↥I := by rw [← hψker]; exact h1
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_center_iff.mp h2 (incl g)
    apply Subtype.ext
    show ((g : ↥Hs) : G) * (y : G) = (y : G) * (g : G)
    exact congrArg (fun z : ↥I => (z : G)) this
  have hΦnd : ¬ p ∣ Nat.card Φ.ker := by
    intro hdvd
    apply hZ
    have h1 : Nat.card (Φ.ker.map incl) = Nat.card Φ.ker :=
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective inf_le_left)
    have h2 : Φ.ker.map incl ≤ Subgroup.center ↥I := by
      rintro _ ⟨y, hy, rfl⟩
      have h1 : ψ (incl y) = 1 := by
        have := congrArg Subtype.val (MonoidHom.mem_ker.mp hy)
        rwa [hΦv] at this
      rw [← hψker]
      exact h1
    exact hdvd.trans (h1 ▸ Subgroup.card_dvd_of_le h2)
  exact ⟨Φ, hΦsurj, hΦker, hΦnd, fun y => rfl⟩

omit [Finite G] in
theorem conj_mem_centralizer_inf {E I : Subgroup G} (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {b : G} (hb : b ∈ E) {x : G} (hx : x ∈ E) {y : G}
    (hy : y ∈ I ⊓ Subgroup.centralizer ({b} : Set G)) :
    x * y * x⁻¹ ∈ I ⊓ Subgroup.centralizer ({b} : Set G) := by
  refine ⟨(Subgroup.mem_normalizer_iff.mp (hEI hx) y).mp hy.1, ?_⟩
  have hxb : Commute x b := hEcomm x hx b hb
  have hyb : Commute y b := Subgroup.mem_centralizer_singleton_iff.mp hy.2
  exact Subgroup.mem_centralizer_singleton_iff.mpr ((hxb.mul_left hyb).mul_left hxb.inv_left)

omit [Finite G] in
theorem exists_conj_hom {E I : Subgroup G} (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x) {b e : G} (hb : b ∈ E) (he : e ∈ E) :
    ∃ τ : ↥(I ⊓ Subgroup.centralizer ({b} : Set G)) →*
        ↥(I ⊓ Subgroup.centralizer ({b} : Set G)),
      ∀ y, ((τ y : ↥(I ⊓ Subgroup.centralizer ({b} : Set G))) : G) = e * y * e⁻¹ := by
  set Hs : Subgroup G := I ⊓ Subgroup.centralizer ({b} : Set G) with hHs
  have hn : e ∈ Subgroup.normalizer (Hs : Set G) := by
    refine Subgroup.mem_normalizer_iff.mpr fun h => ⟨fun hh => conj_mem_centralizer_inf hEI hEcomm hb he hh,
      fun hh => ?_⟩
    have := conj_mem_centralizer_inf hEI hEcomm hb (inv_mem he) hh
    have h2 : h ∈ I ∧ h ∈ Subgroup.centralizer ({b} : Set G) := by simpa [mul_assoc] using this
    exact h2
  exact ⟨(Hs.normalizerMonoidHom ⟨e, hn⟩).toMonoidHom, fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Hs ⟨e, hn⟩ y⟩

theorem eq_one_of_pow_eq_one_of_not_dvd_card {K : Type*} [Group K] [Finite K] {p : ℕ}
    (hp : p.Prime) (hnd : ¬ p ∣ Nat.card K) {u : K} (hu : u ^ p = 1) : u = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  by_contra h
  have := orderOf_eq_prime hu h
  exact hnd (this ▸ orderOf_dvd_natCard u)

theorem exists_components_of_cover {p : ℕ} (hp : p.Prime) {Hs : Subgroup G} {C : Type} [Group C]
    (Φ : ↥Hs →* C) (hΦs : Function.Surjective Φ) (hΦk : Φ.ker ≤ Subgroup.center ↥Hs)
    (hΦn : ¬ p ∣ Nat.card Φ.ker) {ι : Type} (F' : ι → Subgroup C) (hcomp : ∀ i, IsComponent (F' i))
    (hperf : ∀ Y : Subgroup C, ⁅Y, Y⁆ = Y → Y ≤ ⨆ i, F' i)
    (hcen : ∀ i, ∀ u ∈ F' i, (∀ f ∈ F' i, u * f = f * u) → u ^ p = 1 → u = 1) :
    ∃ Q : ι → Subgroup G, (∀ i, Q i ≤ Hs) ∧ (∀ i, IsComponent ((Q i).subgroupOf Hs)) ∧
      (∀ Y : Subgroup G, Y ≤ Hs → Group.IsPerfect ↥Y → Y ≤ ⨆ i, Q i) ∧
      (∀ i, ¬ p ∣ Nat.card ↥(Q i ⊓ Subgroup.centralizer (Q i : Set G))) ∧
      ∀ (i : ι) (e : G) (τ : ↥Hs →* ↥Hs), (∀ y : ↥Hs, ((τ y : ↥Hs) : G) = e * y * e⁻¹) →
        ∀ x ∈ F' i, (∀ y : ↥Hs, Φ y ∈ F' i → Φ (τ y) = x * Φ y * x⁻¹) →
          ∃ x' ∈ Q i, ∃ y' ∈ Subgroup.centralizer (Q i : Set G), e = x' * y' := by
  classical
  have hperfF : ∀ i, ⁅F' i, F' i⁆ = F' i := fun i => Subgroup.isPerfect_iff.1 (hcomp i).1.1
  obtain ⟨Qs, hQs⟩ : ∃ Qs : ι → Subgroup ↥Hs,
      ∀ i, Qs i = ⁅(F' i).comap Φ, (F' i).comap Φ⁆ :=
    ⟨fun i => ⁅(F' i).comap Φ, (F' i).comap Φ⁆, fun _ => rfl⟩
  have hQF : ∀ i, (Qs i).map Φ = F' i := fun i => by
    rw [hQs i]; exact map_commutator_comap hΦs (hperfF i)
  have hQperf : ∀ i, ⁅Qs i, Qs i⁆ = Qs i := fun i => by
    rw [hQs i]; exact commutator_comap_perfect hΦs hΦk (hperfF i)
  have hQcomp : ∀ i, IsComponent (Qs i) := fun i => by
    rw [hQs i]
    exact ⟨isQuasisimple_commutator_comap hΦs hΦk (hcomp i).1,
      isSubnormal_commutator_comap (hcomp i).2⟩
  have hQle : ∀ i, Qs i ≤ (F' i).comap Φ := fun i => by
    rw [hQs i]; exact commutator_self_le _
  refine ⟨fun i => (Qs i).map Hs.subtype, fun i => Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_⟩
  · intro i
    have : ((Qs i).map Hs.subtype).subgroupOf Hs = Qs i :=
      Subgroup.comap_map_eq_self_of_injective Hs.subtype_injective _
    rw [this]
    exact hQcomp i
  · intro Y hY hYp
    have hperfY' : ⁅Y.subgroupOf Hs, Y.subgroupOf Hs⁆ = Y.subgroupOf Hs := by
      have : Group.IsPerfect ↥Y := hYp
      have : Group.IsPerfect ↥(Y.subgroupOf Hs) :=
        Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hY).symm.toMonoidHom)
          (Subgroup.subgroupOfEquivOfLe hY).symm.surjective
      exact Subgroup.isPerfect_iff.1 this
    have hle : (Y.subgroupOf Hs).map Φ ≤ ⨆ i, F' i :=
      hperf _ (by rw [← Subgroup.map_commutator, hperfY'])
    have h2 := le_iSup_of_isPerfect_of_map_le hΦk (Q := Qs) (F := F') hQF hperfY' hle
    calc Y = (Y.subgroupOf Hs).map Hs.subtype := (Subgroup.map_subgroupOf_eq_of_le hY).symm
      _ ≤ (⨆ i, Qs i).map Hs.subtype := Subgroup.map_mono h2
      _ = ⨆ i, (Qs i).map Hs.subtype := Subgroup.map_iSup _ _
  · intro i hdvd
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨u, hu⟩ := exists_prime_orderOf_dvd_card' p hdvd
    have hu1 : (u : G) ∈ (Qs i).map Hs.subtype := u.2.1
    have hu2 : (u : G) ∈ Subgroup.centralizer (((Qs i).map Hs.subtype : Subgroup G) : Set G) :=
      u.2.2
    obtain ⟨u', hu'Q, hu'⟩ := hu1
    have hup : u' ^ p = 1 := by
      apply Hs.subtype_injective
      rw [map_pow, hu', map_one]
      have := pow_orderOf_eq_one u
      rw [hu] at this
      exact congrArg Subtype.val this
    have hcomm : ∀ f ∈ Qs i, u' * f = f * u' := by
      intro f hf
      apply Hs.subtype_injective
      rw [map_mul, map_mul, hu']
      exact (Subgroup.mem_centralizer_iff.mp hu2 (f : G) (Subgroup.mem_map_of_mem _ hf)).symm
    have hΦu : Φ u' = 1 := by
      refine hcen i (Φ u') (hQF i ▸ Subgroup.mem_map_of_mem Φ hu'Q) (fun f' hf' => ?_)
        (by rw [← map_pow, hup, map_one])
      obtain ⟨f, hf, rfl⟩ := Subgroup.mem_map.mp (hQF i ▸ hf')
      rw [← map_mul, hcomm f hf, map_mul]
    have hu'k : u' ∈ Φ.ker := hΦu
    have h1 : (⟨u', hu'k⟩ : Φ.ker) = 1 :=
      eq_one_of_pow_eq_one_of_not_dvd_card hp hΦn (Subtype.ext (by simpa using hup))
    have h2 : u' = 1 := congrArg Subtype.val h1
    have h3 : u = 1 := Subtype.ext (by rw [← hu', h2]; rfl)
    rw [h3, orderOf_one] at hu
    exact hp.one_lt.ne hu
  · intro i e τ hτ x hx hcompat
    obtain ⟨x', hx'Q, hx'⟩ := exists_inner_of_map_eq_conj hΦk (hQperf i) (hQF i) τ hx
      (fun y hy => hcompat y (hQF i ▸ Subgroup.mem_map_of_mem Φ hy))
    refine ⟨(x' : G), Subgroup.mem_map_of_mem _ hx'Q, (x' : G)⁻¹ * e, ?_, by group⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨u', hu'Q, rfl⟩
    have h1 : ((τ u' : ↥Hs) : G) = (x' : G) * u' * (x' : G)⁻¹ := by
      have := congrArg (fun z : ↥Hs => (z : G)) (hx' u' hu'Q)
      simpa using this
    rw [hτ u'] at h1
    change (u' : G) * ((x' : G)⁻¹ * e) = ((x' : G)⁻¹ * e) * (u' : G)
    calc (u' : G) * ((x' : G)⁻¹ * e) = (x' : G)⁻¹ * ((x' : G) * u' * (x' : G)⁻¹) * e := by group
      _ = (x' : G)⁻¹ * (e * u' * e⁻¹) * e := by rw [h1]
      _ = ((x' : G)⁻¹ * e) * (u' : G) := by group

theorem layerDataW_of_autFamily {p : ℕ} (hp : p.Prime) {E I : Subgroup G} {P : Type} [Group P]
    (e₀ : ↥I ⧸ Subgroup.center ↥I ≃* P) (hEI : E ≤ Subgroup.normalizer (I : Set G))
    (hEexp : ∀ x ∈ E, x ^ p = 1) (hEcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x)
    (hZ : ¬ p ∣ Nat.card (Subgroup.center ↥I)) (act : ↥E →* MulAut P)
    (hact : ∀ (x : ↥E) (y : ↥I), act x (e₀ (y : ↥I ⧸ Subgroup.center ↥I)) =
      e₀ ((I.normalizerMonoidHom ⟨(x : G), hEI x.2⟩ y : ↥I) : ↥I ⧸ Subgroup.center ↥I))
    (hfam : ∀ b : ↥E, b ≠ 1 → ∃ (ι : Type) (F : ι → Subgroup P),
      AutLayerFamily p (act b) (Set.range act) F) :
    LayerDataW p E I := by
  classical
  intro b hb hb1
  obtain ⟨ι, F, hF⟩ := hfam ⟨b, hb⟩ (fun h => hb1 (congrArg Subtype.val h))
  obtain ⟨Φ, hΦs, hΦk, hΦn, hΦv⟩ := exists_cover hp e₀ hEI hZ hb (hEexp b hb) (act ⟨b, hb⟩)
    (fun y => hact ⟨b, hb⟩ y)
  have hperf : ∀ Y : Subgroup ↥(fixedSub (act ⟨b, hb⟩)), ⁅Y, Y⁆ = Y →
      Y ≤ ⨆ i, (F i).subgroupOf (fixedSub (act ⟨b, hb⟩)) := by
    intro Y hY
    have h1 : Y.map (fixedSub (act ⟨b, hb⟩)).subtype ≤ ⨆ i, F i := by
      refine hF.perfect _ (Subgroup.map_subtype_le _) (Subgroup.isPerfect_iff.2 ?_)
      rw [← Subgroup.map_commutator, hY]
    have hmapF : (⨆ i, (F i).subgroupOf (fixedSub (act ⟨b, hb⟩))).map
        (fixedSub (act ⟨b, hb⟩)).subtype = ⨆ i, F i := by
      rw [Subgroup.map_iSup]
      exact iSup_congr fun i => Subgroup.map_subgroupOf_eq_of_le (hF.le i)
    rw [← Subgroup.map_le_map_iff_of_injective (fixedSub (act ⟨b, hb⟩)).subtype_injective, hmapF]
    exact h1
  have hcen : ∀ i, ∀ u ∈ (F i).subgroupOf (fixedSub (act ⟨b, hb⟩)),
      (∀ f ∈ (F i).subgroupOf (fixedSub (act ⟨b, hb⟩)), u * f = f * u) → u ^ p = 1 → u = 1 := by
    intro i u hu hc hup
    apply Subtype.ext
    have := hF.center i (u : P) hu (fun f hf => congrArg Subtype.val (hc ⟨f, hF.le i hf⟩ hf))
      (by simpa using congrArg Subtype.val hup)
    simpa using this
  obtain ⟨Q, hQle, hQcomp, hQperf, hQcen, hQinner⟩ := exists_components_of_cover hp Φ hΦs hΦk hΦn
    (fun i => (F i).subgroupOf (fixedSub (act ⟨b, hb⟩))) (fun i => hF.comp i) hperf hcen
  refine ⟨ι, Q, hQle, hQcomp, hQperf, fun i => ⟨?_, hQcen i⟩⟩
  intro e he
  obtain ⟨τ, hτ⟩ := exists_conj_hom hEI hEcomm hb he
  obtain ⟨x₀, hx₀F, hx₀⟩ := hF.inner (act ⟨e, he⟩) ⟨⟨e, he⟩, rfl⟩ i
  refine hQinner i e τ hτ ⟨x₀, hF.le i hx₀F⟩ hx₀F ?_
  intro y hy
  apply Subtype.ext
  have h1 : (⟨((τ y : _) : G), (τ y).2.1⟩ : ↥I) =
      I.normalizerMonoidHom ⟨e, hEI he⟩ ⟨(y : G), y.2.1⟩ := by
    apply Subtype.ext
    rw [hτ y]
    exact (Subgroup.normalizerMonoidHom_apply_apply_coe I ⟨e, hEI he⟩ ⟨(y : G), y.2.1⟩).symm
  have h2 := hact ⟨e, he⟩ ⟨(y : G), y.2.1⟩
  rw [← h1, ← hΦv y] at h2
  have h3 : ((Φ (τ y) : ↥(fixedSub (act ⟨b, hb⟩))) : P) = act ⟨e, he⟩ ((Φ y : _) : P) := by
    rw [hΦv (τ y), h2]
  rw [h3]
  exact hx₀ _ hy

end Cover

end CFSG.RankThree.PartOne.S15K
