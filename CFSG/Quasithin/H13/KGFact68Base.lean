module

public import CFSG.Quasithin.Background.E6EightFacts
public import CFSG.Quasithin.Background.A4Defs
public import CFSG.CharacterTheory.Semidihedral.CenterAndOrders

public section

namespace CFSG.Quasithin.H13.KG68

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

variable {Y : Type} [Group Y]

@[expose] def conjOn (L : Subgroup Y) (a : Y) (ha : a ∈ Subgroup.normalizer (L : Set Y)) :
    MulAut ↥L where
  toFun x := ⟨a * x * a⁻¹, (Subgroup.mem_normalizer_iff.mp ha x).mp x.2⟩
  invFun x := ⟨a⁻¹ * x * a, by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ha) x).mp x.2
    simpa using this⟩
  left_inv x := Subtype.ext (by
    show a⁻¹ * (a * (x : Y) * a⁻¹) * a = x
    group)
  right_inv x := Subtype.ext (by
    show a * (a⁻¹ * (x : Y) * a) * a⁻¹ = x
    group)
  map_mul' x y := Subtype.ext (by
    show a * ((x : Y) * y) * a⁻¹ = a * x * a⁻¹ * (a * y * a⁻¹)
    group)

theorem conjOn_coe (L : Subgroup Y) (a : Y) (ha : a ∈ Subgroup.normalizer (L : Set Y))
    (x : ↥L) : ((conjOn L a ha x : ↥L) : Y) = a * x * a⁻¹ :=
  rfl

theorem conjOn_mul (L : Subgroup Y) {a b : Y} (ha : a ∈ Subgroup.normalizer (L : Set Y))
    (hb : b ∈ Subgroup.normalizer (L : Set Y)) :
    conjOn L (a * b) (Subgroup.mul_mem _ ha hb) = conjOn L a ha * conjOn L b hb := by
  ext x
  show a * b * (x : Y) * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹
  group

theorem conjOn_one (L : Subgroup Y) : conjOn L 1 (Subgroup.one_mem _) = 1 := by
  ext x
  show 1 * (x : Y) * 1⁻¹ = x
  group

theorem conjOn_inv (L : Subgroup Y) {b : Y} (hb : b ∈ Subgroup.normalizer (L : Set Y)) :
    conjOn L b⁻¹ (Subgroup.inv_mem _ hb) = (conjOn L b hb)⁻¹ := by
  refine eq_inv_of_mul_eq_one_left ?_
  ext x
  show b⁻¹ * (b * (x : Y) * b⁻¹) * b⁻¹⁻¹ = x
  group

theorem conjOn_eq_one_iff (L : Subgroup Y) {a : Y} (ha : a ∈ Subgroup.normalizer (L : Set Y)) :
    conjOn L a ha = 1 ↔ a ∈ Subgroup.centralizer (L : Set Y) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun φ : MulAut ↥L => ((φ ⟨x, hx⟩ : ↥L) : Y)) h
    simp only [conjOn_coe, MulAut.one_apply] at h1
    calc x * a = (a * x * a⁻¹) * a := by rw [h1]
      _ = a * x := by group
  · intro h
    ext x
    have h1 := Subgroup.mem_centralizer_iff.mp h x x.2
    show a * (x : Y) * a⁻¹ = x
    rw [← h1]
    group

@[expose] noncomputable def actHom (L A : Subgroup Y)
    (hA : A ≤ Subgroup.normalizer (L : Set Y)) : ↥A →* MulAut ↥L where
  toFun a := conjOn L a (hA a.2)
  map_one' := conjOn_one L
  map_mul' a b := conjOn_mul L (hA a.2) (hA b.2)

theorem actHom_apply (L A : Subgroup Y) (hA : A ≤ Subgroup.normalizer (L : Set Y)) (a : ↥A) :
    actHom L A hA a = conjOn L a (hA a.2) :=
  rfl

theorem ker_actHom (L A : Subgroup Y) (hA : A ≤ Subgroup.normalizer (L : Set Y)) :
    (actHom L A hA).ker = (A ⊓ Subgroup.centralizer (L : Set Y)).subgroupOf A := by
  ext a
  rw [MonoidHom.mem_ker, actHom_apply, conjOn_eq_one_iff, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf]
  exact ⟨fun h => ⟨a.2, h⟩, fun h => h.2⟩

theorem relIndex_eq_card_range (L A : Subgroup Y) (hA : A ≤ Subgroup.normalizer (L : Set Y)) :
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A = Nat.card (actHom L A hA).range := by
  rw [Subgroup.relIndex, ← ker_actHom, Subgroup.index_ker]

@[expose] def omegaZ {X : Type} [Group X] (P : Subgroup X) : Set X :=
  {g | g ∈ P ∧ (∀ x ∈ P, g * x = x * g) ∧ g * g = 1}

section Hyp

variable {L A R : Subgroup Y} {z : Y}

theorem leN (h : E6.E68Hyp L A R z) :
    A ≤ Subgroup.normalizer (L : Set Y) :=
  h.le.trans h.normalizer

@[expose] noncomputable def sylowIn (h : E6.E68Hyp L A R z) : Sylow 2 ↥L :=
  A4.toSylow h.sylow

theorem sylowIn_coe (h : E6.E68Hyp L A R z) :
    ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L) = (R ⊓ L).subgroupOf L :=
  rfl

theorem conjOn_fix_of_hyp (h : E6.E68Hyp L A R z) {a : Y} (ha : a ∈ A) {x : ↥L}
    (hx : x ∈ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L)) :
    conjOn L a (leN h ha) x = x := by
  apply Subtype.ext
  rw [conjOn_coe]
  have hxR : (x : Y) ∈ R := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hx)).1
  have hc := Subgroup.mem_centralizer_iff.mp (h.centralizer hxR) a ha
  rw [hc]
  group

theorem conjOn_sq_of_hyp (h : E6.E68Hyp L A R z) {a : Y} (ha : a ∈ A) :
    conjOn L a (leN h ha) * conjOn L a (leN h ha) = 1 := by
  rw [← conjOn_mul, conjOn_eq_one_iff]
  have h2 : a * a = 1 := by
    have := h.elemAbelian.2 a ha
    rwa [pow_two] at this
  rw [h2]
  exact Subgroup.one_mem _

end Hyp

section Inner

variable [Finite Y] {L A R : Subgroup Y} {z : Y}

theorem mem_omega_of_conj (h : E6.E68Hyp L A R z) (hZ : Subgroup.center ↥L = ⊥) {a : Y}
    (ha : a ∈ A) {g : ↥L} (hg : conjOn L a (leN h ha) = MulAut.conj g) :
    g ∈ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L) ∧
      (∀ x ∈ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L), g * x = x * g) ∧ g * g = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set P := ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L) with hPdef
  have hgP : ∀ x ∈ P, g * x = x * g := by
    intro x hx
    have h1 := conjOn_fix_of_hyp h ha hx
    rw [hg, MulAut.conj_apply] at h1
    calc g * x = (g * x * g⁻¹) * g := by group
      _ = x * g := by rw [h1]
  have hg2 : g * g = 1 := by
    have h1 := conjOn_sq_of_hyp h ha
    rw [hg, ← map_mul] at h1
    have h2 : g * g ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro y
      have h3 := congrArg (fun φ : MulAut ↥L => φ y) h1
      simp only [MulAut.conj_apply, MulAut.one_apply] at h3
      calc y * (g * g) = (g * g * y * (g * g)⁻¹) * (g * g) := by rw [h3]
        _ = g * g * y := by group
    rw [hZ, Subgroup.mem_bot] at h2
    exact h2
  have hgS : g ∈ P := by
    by_cases hg1 : g = 1
    · rw [hg1]
      exact P.one_mem
    have hz2 : IsPGroup 2 (Subgroup.zpowers g) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hg2) hg1, pow_one]
    have hzN : Subgroup.zpowers g ≤ Subgroup.normalizer (P : Set ↥L) := by
      rw [Subgroup.zpowers_le]
      refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
      have h1 : g * x * g⁻¹ = x := by rw [hgP x hx]; group
      rw [h1]
      exact hx
    have hsup := IsPGroup.to_sup_of_normal_right' hz2 (sylowIn h).isPGroup' hzN
    have heq := (sylowIn h).is_maximal' hsup le_sup_right
    have hmem : g ∈ Subgroup.zpowers g ⊔ P := Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
    rw [heq] at hmem
    exact hmem
  exact ⟨hgS, hgP, hg2⟩

theorem relIndex_le_of_inner (h : E6.E68Hyp L A R z) (hZ : Subgroup.center ↥L = ⊥)
    (hinn : ∀ a (ha : a ∈ A), ∃ g : ↥L, conjOn L a (leN h ha) = MulAut.conj g) :
    (A ⊓ Subgroup.centralizer (L : Set Y)).relIndex A ≤
      Nat.card (omegaZ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L)) := by
  classical
  rw [relIndex_eq_card_range L A (leN h)]
  have key : ∀ φ : ↥(actHom L A (leN h)).range,
      ∃ g : omegaZ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L),
        (φ : MulAut ↥L) = MulAut.conj (g : ↥L) := by
    rintro ⟨φ, a, rfl⟩
    obtain ⟨g, hg⟩ := hinn a a.2
    exact ⟨⟨g, mem_omega_of_conj h hZ a.2 hg⟩, hg⟩
  choose f hf using key
  refine Nat.card_le_card_of_injective f fun φ ψ hφψ => Subtype.ext ?_
  rw [hf φ, hf ψ, hφψ]

theorem not_e68Hyp_of_inner (h : E6.E68Hyp L A R z) (hZ : Subgroup.center ↥L = ⊥)
    (hinn : ∀ a (ha : a ∈ A), ∃ g : ↥L, conjOn L a (leN h ha) = MulAut.conj g)
    (hcard : Nat.card (omegaZ ((sylowIn h : Sylow 2 ↥L) : Subgroup ↥L)) ≤ 2) : False := by
  have h1 := relIndex_le_of_inner h hZ hinn
  have h2 := h.four_le
  omega

end Inner

section Conj

variable {Y : Type} [Group Y]

theorem conjOn_of_mem (L : Subgroup Y) (g : ↥L) (hg : (g : Y) ∈ Subgroup.normalizer (L : Set Y)) :
    conjOn L (g : Y) hg = MulAut.conj g := by
  ext x
  rfl

theorem conj_injective_of_center {X : Type} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  intro g g' hgg'
  have h1 : g⁻¹ * g' ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h2 := congrArg (fun φ : MulAut X => φ y) hgg'
    simp only [MulAut.conj_apply] at h2
    calc y * (g⁻¹ * g') = g⁻¹ * (g * y * g⁻¹) * g' := by group
      _ = g⁻¹ * (g' * y * g'⁻¹) * g' := by rw [h2]
      _ = g⁻¹ * g' * y := by group
  rw [hZ, Subgroup.mem_bot, inv_mul_eq_one] at h1
  exact h1

theorem mulAut_conj_conj {X : Type} [Group X] (β : MulAut X) (x : X) :
    β * MulAut.conj x * β⁻¹ = MulAut.conj (β x) := by
  ext y
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

theorem commutator_mem_centralizer_iff {L : Subgroup Y} (hZ : Subgroup.center ↥L = ⊥) {a : Y}
    (ha : a ∈ Subgroup.normalizer (L : Set Y)) {g : ↥L} (hg : conjOn L a ha = MulAut.conj g)
    (u : ↥L) :
    (u : Y) * a * (u : Y)⁻¹ * a⁻¹ ∈ Subgroup.centralizer (L : Set Y) ↔ u * g = g * u := by
  have hu : (u : Y) ∈ Subgroup.normalizer (L : Set Y) := Subgroup.le_normalizer u.2
  have hmem : (u : Y) * a * (u : Y)⁻¹ * a⁻¹ ∈ Subgroup.normalizer (L : Set Y) :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu ha) (Subgroup.inv_mem _ hu))
      (Subgroup.inv_mem _ ha)
  rw [← conjOn_eq_one_iff L hmem]
  have h1 : conjOn L ((u : Y) * a * (u : Y)⁻¹ * a⁻¹) hmem =
      MulAut.conj (u * g * u⁻¹ * g⁻¹) := by
    rw [conjOn_mul L (Subgroup.mul_mem _ (Subgroup.mul_mem _ hu ha) (Subgroup.inv_mem _ hu))
        (Subgroup.inv_mem _ ha),
      conjOn_mul L (Subgroup.mul_mem _ hu ha) (Subgroup.inv_mem _ hu), conjOn_mul L hu ha,
      conjOn_inv L ha, conjOn_inv L hu, hg, conjOn_of_mem L u hu, map_mul, map_mul, map_mul, map_inv,
      map_inv]
  rw [h1]
  constructor
  · intro h2
    have h3 := conj_injective_of_center hZ (h2.trans (map_one _).symm)
    calc u * g = (u * g * u⁻¹ * g⁻¹) * (g * u) := by group
      _ = g * u := by rw [h3, one_mul]
  · intro h2
    have h3 : u * g * u⁻¹ * g⁻¹ = 1 := by
      rw [h2]
      group
    rw [h3, map_one]

theorem conjOn_conj (L : Subgroup Y) (x : ↥L) {a : Y} (ha : a ∈ Subgroup.normalizer (L : Set Y))
    (hxa : (x : Y) * a * (x : Y)⁻¹ ∈ Subgroup.normalizer (L : Set Y)) :
    conjOn L ((x : Y) * a * (x : Y)⁻¹) hxa = MulAut.conj x * conjOn L a ha * (MulAut.conj x)⁻¹ := by
  ext w
  show (x : Y) * a * (x : Y)⁻¹ * (w : Y) * ((x : Y) * a * (x : Y)⁻¹)⁻¹ =
    (x : Y) * (a * ((x : Y)⁻¹ * w * x) * a⁻¹) * (x : Y)⁻¹
  group

end Conj

section Omega

variable {X : Type} [Group X]

theorem card_omegaZ_le_card_center [Finite X] (P : Subgroup X) :
    Nat.card (omegaZ P) ≤ Nat.card (Subgroup.center ↥P) := by
  classical
  let f : omegaZ P → Subgroup.center ↥P := fun g =>
    ⟨⟨g, g.2.1⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (g.2.2.1 y y.2).symm⟩
  refine Nat.card_le_card_of_injective f fun g g' hgg' => ?_
  have := congrArg (fun y : Subgroup.center ↥P => ((y : ↥P) : X)) hgg'
  exact Subtype.ext this

theorem card_center_dihedral {n : ℕ} (hn : Even n) (hn4 : 4 ≤ n) :
    Nat.card (Subgroup.center (DihedralGroup n)) = 2 := by
  have : NeZero n := ⟨by omega⟩
  rw [DihedralGroup.center_eq_closure_of_even_ne_two hn (by omega), Nat.card_zpowers,
    DihedralGroup.orderOf_r]
  obtain ⟨k, hk⟩ := hn
  have hval : ((n / 2 : ℕ) : ZMod n).val = n / 2 := ZMod.val_cast_of_lt (by omega)
  rw [hval]
  have h1 : n / 2 = k := by omega
  have hk0 : 0 < k := by omega
  have hg : (k * 2).gcd k = k := Nat.gcd_eq_right (Dvd.intro 2 rfl)
  rw [h1, show n = k * 2 by omega, hg, Nat.mul_div_cancel_left 2 hk0]

theorem even_of_dihedral [Finite X] {P : Subgroup X} (hP : IsPGroup 2 P) {n : ℕ} (hn : 4 ≤ n)
    (e : ↥P ≃* DihedralGroup n) : Even n := by
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have h1 : Nat.card ↥P = 2 * n := by rw [Nat.card_congr e.toEquiv, DihedralGroup.nat_card]
  rw [hk] at h1
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := by
    rcases k with _ | k'
    · simp at h1
      omega
    · exact ⟨k', rfl⟩
  rw [pow_succ] at h1
  have hn' : n = 2 ^ k' := by omega
  have hk' : 1 ≤ k' := by
    rcases k' with _ | k'
    · simp at hn'
      omega
    · omega
  rw [hn']
  exact (Nat.even_pow' (by omega)).mpr even_two

theorem card_center_of_shape [Finite X] (P : Subgroup X) (hP2 : IsPGroup 2 P)
    (hP : (∃ n : ℕ, 4 ≤ n ∧ Nonempty (↥P ≃* DihedralGroup n)) ∨
      Nonempty (↥P ≃* SemidihedralGroup 4)) :
    Nat.card (Subgroup.center ↥P) = 2 := by
  rcases hP with ⟨n, hn, ⟨e⟩⟩ | he
  · rw [← card_center_dihedral (even_of_dihedral hP2 hn e) hn, ← Subgroup.map_center_eq e,
      Subgroup.card_map_of_injective e.injective]
  · obtain ⟨e⟩ := he
    rw [← CFSG.Semidihedral.center_card 4 le_rfl, ← Subgroup.map_center_eq e,
      Subgroup.card_map_of_injective e.injective]

theorem mem_omegaZ_of_commute {K : Type} [Group K] [Finite K] (Q : Sylow 2 K) {g : K}
    (hgQ : ∀ t ∈ (Q : Subgroup K), g * t = t * g) (hg2 : g * g = 1) :
    g ∈ omegaZ (Q : Subgroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨?_, hgQ, hg2⟩
  by_cases hg1 : g = 1
  · rw [hg1]
    exact (Q : Subgroup K).one_mem
  have hz2 : IsPGroup 2 (Subgroup.zpowers g) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, orderOf_eq_prime (by rw [sq]; exact hg2) hg1, pow_one]
  have hzN : Subgroup.zpowers g ≤ Subgroup.normalizer ((Q : Subgroup K) : Set K) := by
    rw [Subgroup.zpowers_le]
    refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
    have h1 : g * x * g⁻¹ = x := by rw [hgQ x hx]; group
    rw [h1]
    exact hx
  have hsup := IsPGroup.to_sup_of_normal_right' hz2 Q.isPGroup' hzN
  have heq := Q.is_maximal' hsup le_sup_right
  have hmem : g ∈ Subgroup.zpowers g ⊔ (Q : Subgroup K) :=
    Subgroup.mem_sup_left (Subgroup.mem_zpowers g)
  rw [heq] at hmem
  exact hmem

theorem card_omegaZ_le_two [Finite X] (P : Subgroup X)
    (hP : IsCyclic (Subgroup.center ↥P)) : Nat.card (omegaZ P) ≤ 2 := by
  classical
  have : Fintype ↥(Subgroup.center ↥P) := Fintype.ofFinite _
  let f : omegaZ P → {a : Subgroup.center ↥P // a ^ 2 = 1} := fun g =>
    ⟨⟨⟨g, g.2.1⟩, Subgroup.mem_center_iff.mpr fun y => Subtype.ext (g.2.2.1 y y.2).symm⟩, by
      apply Subtype.ext
      apply Subtype.ext
      show (g : X) ^ 2 = 1
      rw [sq]
      exact g.2.2.2⟩
  have hf : Function.Injective f := fun g g' hgg' => by
    have := congrArg (fun a : {a : Subgroup.center ↥P // a ^ 2 = 1} =>
      (((a : Subgroup.center ↥P) : ↥P) : X)) hgg'
    exact Subtype.ext this
  calc Nat.card (omegaZ P) ≤ Nat.card {a : Subgroup.center ↥P // a ^ 2 = 1} :=
        Nat.card_le_card_of_injective f hf
    _ = (Finset.univ.filter fun a : Subgroup.center ↥P => a ^ 2 = 1).card := by
        rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
    _ ≤ 2 := IsCyclic.card_pow_eq_one_le (by norm_num)

end Omega

end CFSG.Quasithin.H13.KG68
