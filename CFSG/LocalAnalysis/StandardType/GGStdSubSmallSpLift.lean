module

public import CFSG.LocalAnalysis.StandardType.GGStdSubSmall
public import CFSG.LocalAnalysis.StandardType.GGTableBSymplecticCover
import CFSG.RankThree.PartOne.S15K.CentralCover
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates

public section

namespace CFSG.StandardType

open CFSG.Assembly

@[expose] def GGStdSubEltData (p : ℕ) {R : Type} [Group R] (A : Subgroup R) (a : R) : Prop :=
  ∃ D : Subgroup R, D ≤ Subgroup.centralizer ({a} : Set R) ∧
    (∀ c ∈ Subgroup.centralizer ({a} : Set R), ∀ d ∈ D, c * d * c⁻¹ ∈ D) ∧ CFSG.IsQuasisimple D ∧
    ∃ U : Subgroup R, U ≤ D ∧ U ≠ ⊥ ∧ IsPGroup 2 U ∧ (∀ s ∈ A, ∀ u ∈ U, s * u * s⁻¹ ∈ U) ∧
      ∃ t ∈ D, t ^ p = 1 ∧ (∀ s ∈ A, s * t = t * s) ∧ t ∈ Subgroup.normalizer (U : Set R) ∧
        (∃ j ∈ D, t * j ≠ j * t) ∧
        ∃ w ∈ D, w * t * w⁻¹ = t⁻¹ ∧ ∀ s ∈ A, s⁻¹ * (w * s * w⁻¹) ∈ Subgroup.zpowers t

@[expose] def GGStdSubTwoTorusElt (p r : ℕ) (R : Type) [Group R] : Prop :=
  ∀ A : Subgroup R, IsElemAbelian p A → p ^ r ≤ Nat.card A → p ^ 3 ≤ Nat.card A →
    ∀ a ∈ A, a ≠ 1 →
      (∀ b ∈ A, (∀ c ∈ Subgroup.centralizer ({a} : Set R), b * c = c * b) →
        b ∈ Subgroup.zpowers a) →
      GGStdSubEltData p A a

namespace StdSubSp

section Transport

variable {R R' : Type} [Group R] [Group R']

theorem symm_mem_centralizer_singleton (e : R ≃* R') {a : R} {c : R'}
    (hc : c ∈ Subgroup.centralizer ({e a} : Set R')) :
    e.symm c ∈ Subgroup.centralizer ({a} : Set R) := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  apply e.injective
  rw [map_mul, map_mul, e.apply_symm_apply, hc]

theorem apply_mem_centralizer_singleton (e : R ≃* R') {a c : R}
    (hc : c ∈ Subgroup.centralizer ({a} : Set R)) :
    e c ∈ Subgroup.centralizer ({e a} : Set R') := by
  rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
  rw [← map_mul, ← map_mul, hc]

theorem GGStdSubEltData.of_mulEquiv {p : ℕ} (e : R ≃* R') {A : Subgroup R} {a : R}
    (h : GGStdSubEltData p (A.map e.toMonoidHom) (e a)) : GGStdSubEltData p A a := by
  obtain ⟨D, hDC, hDn, hDq, U, hUD, hU1, hU2, hAU, t, htD, htp, htA, htU, ⟨j, hjD, hj⟩,
    w, hwD, hwt, hwA⟩ := h
  have hmemA : ∀ s ∈ A, e s ∈ A.map e.toMonoidHom := fun s hs => ⟨s, hs, rfl⟩
  have hmap : ∀ {X : Subgroup R'} {x : R}, x ∈ X.map e.symm.toMonoidHom ↔ e x ∈ X := by
    intro X x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa using hy
    · intro hx
      exact ⟨e x, hx, by simp⟩
  refine ⟨D.map e.symm.toMonoidHom, ?_, ?_, ?_, U.map e.symm.toMonoidHom, Subgroup.map_mono hUD,
    ?_, hU2.map _, ?_, e.symm t, ⟨t, htD, rfl⟩, ?_, ?_, ?_, ⟨e.symm j, ⟨j, hjD, rfl⟩, ?_⟩,
    e.symm w, ⟨w, hwD, rfl⟩, ?_, ?_⟩
  · rintro _ ⟨d, hd, rfl⟩
    have h1 := hDC hd
    rw [← e.apply_symm_apply d] at h1
    exact symm_mem_centralizer_singleton e (by simpa using h1)
  · intro c hc d hd
    rw [hmap] at hd ⊢
    rw [map_mul, map_mul, map_inv]
    exact hDn (e c) (apply_mem_centralizer_singleton e hc) (e d) hd
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv
      (D.equivMapOfInjective _ e.symm.injective) hDq
  · rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ e.symm.injective]
    exact hU1
  · intro s hs u hu
    rw [hmap] at hu ⊢
    rw [map_mul, map_mul, map_inv]
    exact hAU (e s) (hmemA s hs) (e u) hu
  · rw [← map_pow, htp, map_one]
  · intro s hs
    apply e.injective
    rw [map_mul, map_mul, e.apply_symm_apply]
    exact htA (e s) (hmemA s hs)
  · rw [Subgroup.mem_normalizer_iff] at htU ⊢
    intro x
    rw [hmap, hmap, map_mul, map_mul, map_inv, e.apply_symm_apply]
    exact htU (e x)
  · intro h1
    apply hj
    have := congrArg e h1
    simpa using this
  · apply e.injective
    simpa using hwt
  · intro s hs
    have h1 := hwA (e s) (hmemA s hs)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h1
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, e.injective ?_⟩
    simpa using hk

end Transport

section Lift

open TableBSymp

variable {L' R : Type} [Group L'] [Group R] {ψ : L' →* R}

theorem exists_twoSubgroup_lift_le [Finite L'] (hker : ψ.ker ≤ Subgroup.center L')
    {K : Subgroup L'} {U : Subgroup R} (hU : U ≠ ⊥) (hU2 : IsPGroup 2 U) (hUK : U ≤ K.map ψ) :
    ∃ T : Subgroup L', T ≤ K ∧ T ≠ ⊥ ∧ IsPGroup 2 T ∧
      ∀ g : L', (∀ k ∈ K, g * k * g⁻¹ ∈ K) → (∀ u ∈ U, ψ g * u * (ψ g)⁻¹ ∈ U) →
        ∀ y ∈ T, g * y * g⁻¹ ∈ T := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set H : Subgroup L' := K ⊓ U.comap ψ with hH
  let f : H →* U := (ψ.comp H.subtype).codRestrict U (fun h => h.2.2)
  have hf : Function.Surjective f := by
    rintro ⟨r, hr⟩
    obtain ⟨l, hl, rfl⟩ := hUK hr
    exact ⟨⟨l, hl, hr⟩, rfl⟩
  have hfker : f.ker ≤ Subgroup.center H := by
    intro h hh
    have h1 : ψ h = 1 := congrArg Subtype.val hh
    have h2 := hker h1
    rw [Subgroup.mem_center_iff] at h2 ⊢
    intro k
    exact Subtype.ext (h2 k)
  have : Finite U := Finite.of_surjective _ hf
  have : Group.IsNilpotent U := hU2.isNilpotent
  have : Group.IsNilpotent H := Subgroup.isNilpotent_of_ker_le_center f hfker
  obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow 2 H))
  have hPn : (P : Subgroup H).Normal := inferInstance
  have := Sylow.unique_of_normal P hPn
  have htop : (⊤ : Subgroup U) = (P : Subgroup H).map f := by
    have h := (P.mapSurjective hf).is_maximal' (Q := ⊤)
      (hU2.of_equiv Subgroup.topEquiv.symm) le_top
    rwa [Sylow.coe_mapSurjective] at h
  have hmemP : ∀ h : H, ∀ k : ℕ, h ^ 2 ^ k = 1 → h ∈ (P : Subgroup H) := by
    intro h k hk
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hk)
    obtain ⟨Q, hQ⟩ := (IsPGroup.of_card (n := j) (G := Subgroup.zpowers h)
      (by rw [Nat.card_zpowers, hj])).exists_le_sylow
    have hQP : Q = P := Subsingleton.elim (α := Sylow 2 H) Q P
    rw [← hQP]
    exact hQ (Subgroup.mem_zpowers h)
  refine ⟨(P : Subgroup H).map H.subtype, ?_, ?_, P.isPGroup'.map _, ?_⟩
  · rintro _ ⟨q, -, rfl⟩
    exact q.2.1
  · intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ H.subtype_injective] at hbot
    rw [hbot, Subgroup.map_bot] at htop
    apply hU
    rw [eq_bot_iff]
    intro u hu
    have : (⟨u, hu⟩ : U) ∈ (⊥ : Subgroup U) := htop ▸ Subgroup.mem_top _
    exact congrArg Subtype.val (Subgroup.mem_bot.mp this)
  · rintro g hgK hgU _ ⟨q, hq, rfl⟩
    have hgH : g * (q : L') * g⁻¹ ∈ H := by
      refine ⟨hgK _ q.2.1, ?_⟩
      show ψ (g * (q : L') * g⁻¹) ∈ U
      rw [map_mul, map_mul, map_inv]
      exact hgU _ q.2.2
    obtain ⟨k, hk⟩ := P.isPGroup' ⟨q, hq⟩
    have hqk : (q : L') ^ 2 ^ k = 1 := by
      have := congrArg (fun z : (P : Subgroup H) => ((z : H) : L')) hk
      simpa using this
    refine ⟨⟨_, hgH⟩, hmemP _ k (Subtype.ext ?_), rfl⟩
    show (g * (q : L') * g⁻¹) ^ 2 ^ k = 1
    rw [conj_pow, hqk, mul_one, mul_inv_cancel]

theorem exists_lift_pow_eq_one_mem (hker : ψ.ker ≤ Subgroup.center L') {p : ℕ} (hp : Odd p)
    {e w : R} (he : e ^ p = 1) (hw : w * e * w⁻¹ = e⁻¹) {K : Subgroup L'} {x w' : L'}
    (hx : ψ x = e) (hxK : x ∈ K) (hw' : ψ w' = w) (hw'K : w' ∈ K) :
    ∃ t ∈ K, ψ t = e ∧ t ^ p = 1 := by
  obtain ⟨m, hm⟩ := hp
  set a := x ^ (m + 1) with ha
  have haK : a ∈ K := Subgroup.pow_mem _ hxK _
  set y := w' * a⁻¹ * w'⁻¹ with hy
  have hyK : y ∈ K := K.mul_mem (K.mul_mem hw'K (K.inv_mem haK)) (K.inv_mem hw'K)
  have hψa : ψ a = e ^ (m + 1) := by rw [ha, map_pow, hx]
  have hψy : ψ y = e ^ (m + 1) := by
    have h1 : ψ w' * e⁻¹ * (ψ w')⁻¹ = e := by
      rw [show ψ w' * e⁻¹ * (ψ w')⁻¹ = (ψ w' * e * (ψ w')⁻¹)⁻¹ by group, hw', hw, inv_inv]
    rw [hy, map_mul, map_mul, map_inv, map_inv, hψa, ← inv_pow, ← conj_pow, h1]
  have hz : a⁻¹ * y ∈ Subgroup.center L' := hker (by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hψa, hψy, inv_mul_cancel])
  have hcomm : Commute a y := by
    have e2 := Subgroup.mem_center_iff.mp hz a
    show a * y = y * a
    calc a * y = a * (a * (a⁻¹ * y)) := by group
      _ = a * ((a⁻¹ * y) * a) := by rw [e2]
      _ = y * a := by group
  refine ⟨a * y, K.mul_mem haK hyK, ?_, ?_⟩
  · rw [map_mul, hψa, hψy, ← pow_add]
    have : m + 1 + (m + 1) = p + 1 := by omega
    rw [this, pow_succ, he, one_mul]
  · rw [hcomm.mul_pow]
    have hapZ : a ^ p ∈ Subgroup.center L' := by
      refine hker ?_
      rw [MonoidHom.mem_ker, map_pow, hψa, ← pow_mul, mul_comm, pow_mul, he, one_pow]
    have hyp : y ^ p = (a ^ p)⁻¹ := by
      rw [hy, conj_pow, inv_pow, Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hapZ) w']
      group
    rw [hyp, mul_inv_cancel]

theorem commute_lift_of_inverting_mod (hker : ψ.ker ≤ Subgroup.center L') {p : ℕ} (hp : Odd p)
    {x y w' : L'} (hxp : x ^ p = 1) (hxy : Commute (ψ x) (ψ y))
    (hwx : ψ w' * ψ x * (ψ w')⁻¹ = (ψ x)⁻¹) {k : ℤ}
    (hwy : (ψ y)⁻¹ * (ψ w' * ψ y * (ψ w')⁻¹) = ψ x ^ k) : Commute x y := by
  set c := x * y * x⁻¹ * y⁻¹ with hc
  have hcZ : c ∈ Subgroup.center L' := hker (by
    rw [MonoidHom.mem_ker, hc, map_mul, map_mul, map_mul, map_inv, map_inv, hxy.eq]
    group)
  set z₁ := w' * x * w'⁻¹ * x with hz₁
  have h₁ : z₁ ∈ Subgroup.center L' := hker (by
    rw [MonoidHom.mem_ker, hz₁, map_mul, map_mul, map_mul, map_inv, hwx, inv_mul_cancel])
  set z₂ := (x ^ k)⁻¹ * (y⁻¹ * (w' * y * w'⁻¹)) with hz₂
  have h₂ : z₂ ∈ Subgroup.center L' := hker (by
    rw [MonoidHom.mem_ker, hz₂, map_mul, map_inv, map_zpow, map_mul, map_inv, map_mul, map_mul,
      map_inv, hwy, inv_mul_cancel])
  have hx' : w' * x * w'⁻¹ = z₁ * x⁻¹ := by rw [hz₁]; group
  have hy' : w' * y * w'⁻¹ = z₂ * (y * x ^ k) := by
    have e := Subgroup.mem_center_iff.mp h₂ (y * x ^ k)
    rw [← e, hz₂]
    group
  have hconj : w' * c * w'⁻¹ = c⁻¹ := by
    calc w' * c * w'⁻¹ = (w' * x * w'⁻¹) * (w' * y * w'⁻¹) * (w' * x * w'⁻¹)⁻¹ *
          (w' * y * w'⁻¹)⁻¹ := by rw [hc]; group
      _ = (z₁ * x⁻¹) * (z₂ * (y * x ^ k)) * (z₁ * x⁻¹)⁻¹ * (z₂ * (y * x ^ k))⁻¹ := by
          rw [hx', hy']
      _ = x⁻¹ * (y * x ^ k) * x⁻¹⁻¹ * (y * x ^ k)⁻¹ := commutator_mul_central h₁ h₂
      _ = x⁻¹ * y * x⁻¹⁻¹ * y⁻¹ := by group
      _ = c⁻¹ := by rw [inv_inv]; exact inv_commutator_of_central hcZ
  have hcc : w' * c * w'⁻¹ = c := by
    rw [Subgroup.mem_center_iff.mp hcZ w']
    group
  have hc2 : c ^ 2 = 1 := by
    have h := hcc.symm.trans hconj
    rw [pow_two]
    exact mul_eq_one_iff_eq_inv.mpr h
  have hcp : c ^ p = 1 := by
    have h := pow_conj_eq_of_central hcZ p
    rw [hxp, one_mul, inv_one, mul_one] at h
    exact (mul_eq_right.mp h.symm)
  have hc1 : c = 1 := by
    obtain ⟨m, hm⟩ := hp
    have h' : c ^ p = (c ^ 2) ^ m * c := by rw [hm, pow_succ, pow_mul]
    rw [hc2, one_pow, one_mul, hcp] at h'
    exact h'.symm
  have h3 : x * y * x⁻¹ * y⁻¹ = 1 := hc1
  show x * y = y * x
  calc x * y = (x * y * x⁻¹ * y⁻¹) * (y * x) := by group
    _ = y * x := by rw [h3, one_mul]

end Lift

section Main

open TableBSymp

theorem exists_inducedHom {R : Type} [Group R] {I : Set (MulAut R)}
    (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R)) (hZ : Subgroup.center R = ⊥)
    {L' : Type} [Group L'] {ψ : L' →* R} (hψ : Function.Surjective ψ)
    (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤) {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ φ ∈ I, ∀ l : L', φ (ψ l) = ψ (a l)) :
    ∃ χ : A →* R, Function.Injective χ ∧
      ∀ (a : A) (t' : L'), ψ t' = χ a → ∀ l, (a : MulAut L') l = t' * l * t'⁻¹ := by
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
    fun a t' ht' => eq_conj_of_induces hker hperf (a : MulAut L') t' (fun l => by rw [hχ, ht'])
  have hχinj : Function.Injective χ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := hinner a 1 (by rw [map_one]; exact ha.symm)
    apply Subtype.ext
    ext l
    rw [h1 l]
    simp
  exact ⟨χ, hχinj, hinner⟩

theorem ggStdSubTwoTorus_of_elt {p r : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {R : Type} [Group R]
    {I : Set (MulAut R)} (hI : I ⊆ Set.range (MulAut.conj : R →* MulAut R))
    (hZ : Subgroup.center R = ⊥) (h : GGStdSubTwoTorusElt p r R) : GGStdSubTwoTorus p r R I := by
  intro L' _ _ ψ hψ hker hperf A hA hAI hr h3 a haA ha1 hEcomp hcentA
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨χ, hχinj, hinner⟩ := exists_inducedHom hI hZ hψ hker hperf hAI
  set Ab := χ.range with hAb
  have hAbA : IsElemAbelian p Ab := isElemAbelian_range
    (fun a b => Subtype.ext (TableB.IsElemAbelian.comm hA a.2 b.2))
    (fun a => Subtype.ext (by simpa using hA.2 a a.2)) χ
  have hcardAb : Nat.card Ab = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hχinj).toEquiv).symm
  set a₀ : A := ⟨a, haA⟩ with ha₀def
  obtain ⟨t', ht'⟩ := hψ (χ a₀)
  have ha₀ := hinner a₀ t' ht'
  have hfix : ggFix a = Subgroup.centralizer ({t'} : Set L') := by
    ext l
    rw [mem_ggFix, show a = (a₀ : MulAut L') from rfl, ha₀,
      Subgroup.mem_centralizer_singleton_iff]
    constructor
    · intro hl
      calc l * t' = t' * l * t'⁻¹ * t' := by rw [hl]
        _ = t' * l := by group
    · intro hl
      rw [← hl]
      group
  set C := Subgroup.centralizer ({t'} : Set L') with hC
  set E := LargeEvenLayer (ggFix a) with hE
  have hlift : ∀ a' : A, ∃ s : L', ψ s = χ a' ∧ ∀ l, (a' : MulAut L') l = s * l * s⁻¹ := by
    intro a'
    obtain ⟨s, hs⟩ := hψ (χ a')
    exact ⟨s, hs, hinner a' s hs⟩
  have hψC : ∀ y ∈ C, ψ y ∈ Subgroup.centralizer ({χ a₀} : Set R) := by
    intro y hy
    rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
    rw [← ht', ← map_mul, ← map_mul, hy]
  have hEq : CFSG.IsQuasisimple E := (isQuasisimple_iff _).mp hEcomp.2.2
  have hEperf : ⁅E, E⁆ = E := Subgroup.isPerfect_iff.1 hEq.1
  have hEC : E ≤ C := hfix ▸ hEcomp.1
  have hECC : E ≤ ⁅C, C⁆ := by
    rw [← hEperf]
    exact Subgroup.commutator_mono hEC hEC
  have hhyp : ∀ b ∈ Ab, (∀ c ∈ Subgroup.centralizer ({χ a₀} : Set R), b * c = c * b) →
      b ∈ Subgroup.zpowers (χ a₀) := by
    rintro _ ⟨b₀, rfl⟩ hb
    obtain ⟨s, hs, hsb⟩ := hlift b₀
    have hfixE : ∀ j ∈ E, (b₀ : MulAut L') j = j := by
      intro j hj
      rw [hsb]
      have hcomm := commute_of_mem_commutator (x := s) (Y := C) (fun y hy => hker (by
        rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hs,
          hb _ (hψC y hy)]
        group)) (hECC hj)
      rw [hcomm]
      group
    have hmem := (hcentA b₀ b₀.2).mp hfixE
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    have h2 : a₀ ^ n = b₀ := Subtype.ext (by simpa using hn)
    rw [← map_zpow, h2]
  have hχa₁ : χ a₀ ≠ 1 := by
    intro h1
    apply ha1
    have h2 : a₀ = 1 := hχinj (by rw [h1, map_one])
    exact congrArg Subtype.val h2
  obtain ⟨D, hDC, hDn, hDq, Ub, hUbD, hUb1, hUb2, hAUb, tb, htbD, htbp, htbA, htbU,
    ⟨jb, hjbD, hjb⟩, w, hwD, hwt, hwA⟩ :=
    h Ab hAbA (hcardAb ▸ hr) (hcardAb ▸ h3) (χ a₀) ⟨a₀, rfl⟩ hχa₁ hhyp
  set Y := D.comap ψ with hY
  set K := ⁅Y, Y⁆ with hK
  have hDperf : ⁅D, D⁆ = D := Subgroup.isPerfect_iff.1 hDq.1
  have hKq : CFSG.IsQuasisimple K :=
    CFSG.RankThree.PartOne.S15K.isQuasisimple_commutator_comap hψ hker hDq
  have hKmap : K.map ψ = D := CFSG.RankThree.PartOne.S15K.map_commutator_comap hψ hDperf
  have hKC : K ≤ C := by
    intro k hk
    rw [hC, Subgroup.mem_centralizer_singleton_iff]
    refine (commute_of_mem_commutator (x := t') (fun y hy => hker ?_) hk).symm
    rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hDC hy)
    rw [ht', ← h1]
    group
  have hnormK : ∀ g : L', (∀ d ∈ D, ψ g * d * (ψ g)⁻¹ ∈ D) → ∀ k ∈ K, g * k * g⁻¹ ∈ K := by
    intro g hg k hk
    have hle : K.map (MulAut.conj g).toMonoidHom ≤ K := by
      rw [hK, Subgroup.map_commutator]
      have hYc : Y.map (MulAut.conj g).toMonoidHom ≤ Y := by
        rintro _ ⟨y, hy, rfl⟩
        show ψ (g * y * g⁻¹) ∈ D
        rw [map_mul, map_mul, map_inv]
        exact hg _ hy
      exact Subgroup.commutator_mono hYc hYc
    exact hle ⟨k, hk, rfl⟩
  have hKcomp : IsComponentOf K C := by
    refine ⟨hKC, IsSubnormal.step hKC ?_ (IsSubnormal.refl C), (isQuasisimple_iff _).mpr hKq⟩
    rw [Subgroup.normal_subgroupOf_iff hKC]
    intro k c hk hc
    exact hnormK c (fun d hd => hDn _ (hψC c hc) d hd) k hk
  have hKE : K ≤ E := by
    rw [hE, hfix]
    exact le_sSup hKcomp
  have hAbC : ∀ a' : A, χ a' ∈ Subgroup.centralizer ({χ a₀} : Set R) := by
    intro a'
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (TableB.IsElemAbelian.comm hA a'.2 a₀.2)
  have hmemK : ∀ d ∈ D, ∃ k ∈ K, ψ k = d := by
    intro d hd
    obtain ⟨k, hk, hk'⟩ := hKmap.ge hd
    exact ⟨k, hk, hk'⟩
  obtain ⟨U, hUK, hU1, hU2, hUn⟩ := exists_twoSubgroup_lift_le hker hUb1 hUb2 (hUbD.trans hKmap.ge)
  obtain ⟨x, hxK, hx⟩ := hmemK tb htbD
  obtain ⟨w', hw'K, hw'⟩ := hmemK w hwD
  obtain ⟨t, htK, hψt, htp⟩ := exists_lift_pow_eq_one_mem hker hpodd htbp hwt hx hxK hw' hw'K
  have htcomm : ∀ a' : A, ∀ s : L', ψ s = χ a' → Commute t s := by
    intro a' s hs
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hwA (χ a') ⟨a', rfl⟩)
    refine commute_lift_of_inverting_mod hker hpodd (w' := w') (k := k) htp ?_ ?_ ?_
    · rw [hψt, hs]
      exact (htbA _ ⟨a', rfl⟩).symm
    · rw [hψt, hw']
      exact hwt
    · rw [hψt, hs, hw']
      exact hk.symm
  have hUA : ∀ a' ∈ A, ∀ u ∈ U, a' u ∈ U := by
    intro a' ha' u hu
    obtain ⟨s, hs, hsa⟩ := hlift ⟨a', ha'⟩
    rw [show a' = ((⟨a', ha'⟩ : A) : MulAut L') from rfl, hsa]
    refine hUn s (hnormK s (fun d hd => ?_)) (fun v hv => ?_) u hu
    · rw [hs]
      exact hDn _ (hAbC _) d hd
    · rw [hs]
      exact hAUb _ ⟨_, rfl⟩ v hv
  have hN : ∀ g : L', g ∈ K → ψ g ∈ Subgroup.normalizer (Ub : Set R) →
      ∀ u ∈ U, g * u * g⁻¹ ∈ U := by
    intro g hgK hgN u hu
    refine hUn g (fun k hk => K.mul_mem (K.mul_mem hgK hk) (K.inv_mem hgK)) (fun v hv => ?_) u hu
    exact (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
  obtain ⟨j, hjK, hj⟩ := hmemK jb hjbD
  refine ⟨U, hU1, hU2, hUK.trans hKE, hUA, t, hKE htK, htp, fun a' ha' => ?_, ?_,
    j, hKE hjK, fun hcomm => hjb ?_⟩
  · obtain ⟨s, hs, hsa⟩ := hlift ⟨a', ha'⟩
    rw [show a' = ((⟨a', ha'⟩ : A) : MulAut L') from rfl, hsa, (htcomm _ s hs).symm.eq]
    group
  · rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · exact hN t htK (hψt ▸ htbU) u
    · intro hu
      have := hN t⁻¹ (K.inv_mem htK) (by rw [map_inv, hψt]; exact Subgroup.inv_mem _ htbU) _ hu
      simpa [mul_assoc] using this
  · have := congrArg ψ hcomm
    rwa [map_mul, map_mul, hψt, hj] at this

end Main



end StdSubSp

end CFSG.StandardType

end
