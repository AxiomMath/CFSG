module

public import CFSG.RankThree.PartTwo.Sec17.Item1728
public import CFSG.RankThree.PartTwo.Sec17.Item1729
public import CFSG.RankThree.PartTwo.Sec17.Item17TailData

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15

@[expose] def ConfigScalar : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L →
      ∃ (p : ℕ) (_ : Fact p.Prime) (Z : Subgroup G) (s : G) (m : ℕ),
        CFSG.Assembly.IsElemAbelian p Z ∧ Z ≠ ⊥ ∧ s ∈ Subgroup.normalizer (Z : Set G) ∧
          s * c * s⁻¹ = c⁻¹ ∧ (m : ZMod p) ^ 2 ≠ 1 ∧ ∀ z ∈ Z, c * z * c⁻¹ = z ^ m

theorem rank3II_17_28_of_scalar (h : ConfigScalar) : Item1728 := by
  intro G _ _ A c L hR
  obtain ⟨p, _, Z, s, m, hZe, hZ1, hsZ, hsc, hm, hcm⟩ := h G A c L hR
  exact hZ1 (eq_bot_of_conj_eq_pow hZe hsZ hsc hm hcm)

section OmegaOne

variable {G : Type*} [Group G]

theorem omegaOneZ_le (p : ℕ) (X : Subgroup G) : omegaOneZ p X ≤ X :=
  fun _ h => h.1

theorem isElemAbelian_omegaOneZ (p : ℕ) (X : Subgroup G) :
    CFSG.Assembly.IsElemAbelian p (omegaOneZ p X) := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => hx.2.2⟩
  exact Subgroup.mem_centralizer_iff.mp b.2.2.1 a a.2.1

theorem omegaOneZ_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {X : Subgroup G}
    (hX : IsPGroup p X) (hX1 : X ≠ ⊥) : omegaOneZ p X ≠ ⊥ := by
  have : Nontrivial X := (Subgroup.nontrivial_iff_ne_bot X).mpr hX1
  have hZ : Nontrivial (Subgroup.center X) := hX.center_nontrivial
  have hdvd : p ∣ Nat.card (Subgroup.center X) := by
    obtain ⟨k, hk⟩ := (hX.to_subgroup (Subgroup.center X)).exists_card_eq
    have h1 : 1 < Nat.card (Subgroup.center X) := Finite.one_lt_card_iff_nontrivial.mpr hZ
    rw [hk] at h1 ⊢
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at h1
      exact lt_irrefl 1 h1
    exact dvd_pow_self p hk0
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center X) p hdvd
  intro h
  have hmem : (((z : Subgroup.center X) : X) : G) ∈ omegaOneZ p X := by
    refine ⟨(z : X).2, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact congrArg Subtype.val (Subgroup.mem_center_iff.mp z.2 ⟨y, hy⟩)
    · have h1 := pow_orderOf_eq_one z
      rw [hz] at h1
      have h2 := congrArg (fun w : Subgroup.center X => ((w : X) : G)) h1
      simpa using h2
  rw [h, Subgroup.mem_bot] at hmem
  have hz1 : z = 1 := Subtype.ext (Subtype.ext hmem)
  rw [hz1, orderOf_one] at hz
  exact (Fact.out : p.Prime).one_lt.ne hz

theorem normalizer_le_normalizer_omegaOneZ (p : ℕ) (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (omegaOneZ p X : Set G) := by
  have key : ∀ g ∈ Subgroup.normalizer (X : Set G), ∀ z ∈ omegaOneZ p X,
      g * z * g⁻¹ ∈ omegaOneZ p X := by
    rintro g hg z ⟨hzX, hzC, hzp⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hg z).mp hzX, ?_, ?_⟩
    · rw [Subgroup.mem_centralizer_iff] at hzC ⊢
      intro y hy
      have hy' : g⁻¹ * y * g ∈ X := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) y).mp hy
        simpa using this
      have := hzC _ hy'
      calc y * (g * z * g⁻¹) = g * ((g⁻¹ * y * g) * z) * g⁻¹ := by group
        _ = g * (z * (g⁻¹ * y * g)) * g⁻¹ := by rw [this]
        _ = g * z * g⁻¹ * y := by group
    · rw [conj_pow, hzp, mul_one, mul_inv_cancel]
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro z
  refine ⟨key h hh z, fun hz => ?_⟩
  have := key h⁻¹ (Subgroup.inv_mem _ hh) _ hz
  simpa [mul_assoc] using this

end OmegaOne

section Scalar

variable {G : Type*} [Group G]

theorem conj_eq_pow_sup {Z H K : Subgroup G} (hZ : IsMulCommutative Z) (hH : H ≤ Z)
    (hK : K ≤ Z) {c : G} {m : ℕ} (h₁ : ∀ z ∈ H, c * z * c⁻¹ = z ^ m)
    (h₂ : ∀ z ∈ K, c * z * c⁻¹ = z ^ m) : ∀ z ∈ H ⊔ K, c * z * c⁻¹ = z ^ m := by
  let T : Subgroup G :=
    { carrier := {z | z ∈ Z ∧ c * z * c⁻¹ = z ^ m}
      mul_mem' := by
        rintro a b ⟨haZ, ha⟩ ⟨hbZ, hb⟩
        refine ⟨Z.mul_mem haZ hbZ, ?_⟩
        have hab : Commute a b :=
          congrArg Subtype.val (hZ.is_comm.comm ⟨a, haZ⟩ ⟨b, hbZ⟩)
        rw [hab.mul_pow, ← ha, ← hb]
        group
      one_mem' := ⟨Z.one_mem, by simp⟩
      inv_mem' := by
        rintro a ⟨haZ, ha⟩
        refine ⟨Z.inv_mem haZ, ?_⟩
        rw [inv_pow, ← ha]
        group }
  have hHT : H ≤ T := fun z hz => ⟨hH hz, h₁ z hz⟩
  have hKT : K ≤ T := fun z hz => ⟨hK hz, h₂ z hz⟩
  exact fun z hz => (sup_le hHT hKT hz).2

theorem conj_eq_pow_map {H : Subgroup G} {c g : G} (hcg : c * g = g * c) {m : ℕ}
    (h : ∀ z ∈ H, c * z * c⁻¹ = z ^ m) :
    ∀ z ∈ H.map (MulAut.conj g).toMonoidHom, c * z * c⁻¹ = z ^ m := by
  rintro _ ⟨y, hy, rfl⟩
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hg : g⁻¹ * c * g = c := by rw [mul_assoc, hcg, ← mul_assoc, inv_mul_cancel, one_mul]
  calc c * (g * y * g⁻¹) * c⁻¹ = g * ((g⁻¹ * c * g) * y * (g⁻¹ * c * g)⁻¹) * g⁻¹ := by group
    _ = g * y ^ m * g⁻¹ := by rw [hg, h y hy]
    _ = (g * y * g⁻¹) ^ m := by rw [conj_pow]

theorem exists_conj_eq_pow_of_card_prime [Finite G] {X : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hX : Nat.card X = p) {c : G} (hc : c ∈ Subgroup.normalizer (X : Set G)) :
    ∃ m : ℕ, ∀ z ∈ X, c * z * c⁻¹ = z ^ m := by
  have : IsCyclic X := isCyclic_of_prime_card hX
  obtain ⟨x, hx⟩ := IsCyclic.exists_generator (α := X)
  have hcx : c * (x : G) * c⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp hc x).mp x.2
  obtain ⟨m, hm⟩ := Submonoid.mem_powers_iff _ _ |>.mp
    (mem_powers_iff_mem_zpowers.mpr (hx ⟨_, hcx⟩))
  refine ⟨m, fun z hz => ?_⟩
  obtain ⟨j, hj⟩ := Submonoid.mem_powers_iff _ _ |>.mp
    (mem_powers_iff_mem_zpowers.mpr (hx ⟨z, hz⟩))
  have hm' : (x : G) ^ m = c * (x : G) * c⁻¹ := by
    have := congrArg Subtype.val hm
    simpa using this
  have hj' : (x : G) ^ j = z := by
    have := congrArg Subtype.val hj
    simpa using this
  rw [← hj', ← conj_pow, ← hm', ← pow_mul, ← pow_mul, mul_comm m j]

theorem sq_ne_one_of_conj_eq_pow {p : ℕ} [hp : Fact p.Prime] {Z : Subgroup G}
    (hZe : CFSG.Assembly.IsElemAbelian p Z) (hZ1 : Z ≠ ⊥) {c : G} (hc3 : c ^ 3 = 1)
    (hfix : Z ⊓ Subgroup.centralizer ({c} : Set G) = ⊥) {m : ℕ}
    (hcm : ∀ z ∈ Z, c * z * c⁻¹ = z ^ m) : (m : ZMod p) ^ 2 ≠ 1 := by
  obtain ⟨z, hz, hz1⟩ := (Subgroup.bot_or_exists_ne_one Z).resolve_left hZ1
  have hord : orderOf z = p := orderOf_eq_prime (hZe.2 z hz) hz1
  have h3 : z ^ 1 = z ^ (m ^ 3) := by
    have hccc : c * c * c = 1 := by rw [← hc3, pow_three, mul_assoc]
    have e1 : c * (c * (c * z * c⁻¹) * c⁻¹) * c⁻¹ = z := by
      calc c * (c * (c * z * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * z * (c * c * c)⁻¹ := by group
        _ = z := by rw [hccc]; group
    have e2 : c * (c * (c * z * c⁻¹) * c⁻¹) * c⁻¹ = z ^ (m * (m * m)) := by
      rw [hcm z hz, ← conj_pow, hcm z hz, ← pow_mul, ← conj_pow, hcm z hz, ← pow_mul]
    calc z ^ 1 = z := pow_one z
      _ = c * (c * (c * z * c⁻¹) * c⁻¹) * c⁻¹ := e1.symm
      _ = z ^ (m * (m * m)) := e2
      _ = z ^ (m ^ 3) := by rw [show m * (m * m) = m ^ 3 by ring]
  rw [pow_eq_pow_iff_modEq, hord] at h3
  have hm3 : (m : ZMod p) ^ 3 = 1 := by
    have := (ZMod.natCast_eq_natCast_iff 1 (m ^ 3) p).mpr h3
    rw [Nat.cast_one, Nat.cast_pow] at this
    exact this.symm
  intro hm2
  have hm1 : (m : ZMod p) = 1 := by
    have e : (m : ZMod p) ^ 3 = (m : ZMod p) * (m : ZMod p) ^ 2 := by ring
    rw [hm3, hm2, mul_one] at e
    exact e.symm
  apply hz1
  have hmem : z ∈ Z ⊓ Subgroup.centralizer ({c} : Set G) := by
    refine ⟨hz, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have h := hcm z hz
    rw [pow_eq_pow_of_cast_eq hZe hz (b := 1) (by rw [hm1, Nat.cast_one]), pow_one,
      mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rw [hfix, Subgroup.mem_bot] at hmem
  exact hmem

end Scalar

section Decomposition

variable {G : Type*} [Group G]

theorem norm_eq_one_of_inf_centralizer_eq_bot {Z : Subgroup G} (hZ : IsMulCommutative Z) {g : G}
    (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) (hg3 : g ^ 3 = 1)
    (hfix : Z ⊓ Subgroup.centralizer ({g} : Set G) = ⊥) {z : G} (hz : z ∈ Z) :
    z * (g * z * g⁻¹) * (g * (g * z * g⁻¹) * g⁻¹) = 1 := by
  have hc : ∀ x ∈ Z, g * x * g⁻¹ ∈ Z := fun x hx => (Subgroup.mem_normalizer_iff.mp hgZ x).mp hx
  have h1 : g * z * g⁻¹ ∈ Z := hc z hz
  have h2 : g * (g * z * g⁻¹) * g⁻¹ ∈ Z := hc _ h1
  have hggg : g * g * g = 1 := by rw [← hg3, pow_three, mul_assoc]
  have h3 : g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹ = z := by
    calc g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹ = (g * g * g) * z * (g * g * g)⁻¹ := by group
      _ = z := by rw [hggg]; group
  set n := z * (g * z * g⁻¹) * (g * (g * z * g⁻¹) * g⁻¹) with hn
  have hnZ : n ∈ Z := Z.mul_mem (Z.mul_mem hz h1) h2
  have hcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hZ.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hfixn : g * n * g⁻¹ = n := by
    have e : g * n * g⁻¹ =
        (g * z * g⁻¹) * (g * (g * z * g⁻¹) * g⁻¹) * (g * (g * (g * z * g⁻¹) * g⁻¹) * g⁻¹) := by
      rw [hn]
      group
    rw [e, h3, hcomm _ (Z.mul_mem h1 h2) z hz, ← mul_assoc]
  have hmem : n ∈ Z ⊓ Subgroup.centralizer ({g} : Set G) := by
    refine ⟨hnZ, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    rw [mul_inv_eq_iff_eq_mul] at hfixn
    exact hfixn.symm
  rw [hfix, Subgroup.mem_bot] at hmem
  exact hmem

theorem eq_sup_inf_centralizer_mul [Finite G] {Z : Subgroup G} (hZ : IsMulCommutative Z)
    (hcop : Nat.Coprime 3 (Nat.card Z)) {c d : G} (hcd : c * d = d * c) (hc3 : c ^ 3 = 1)
    (hd3 : d ^ 3 = 1) (hcZ : c ∈ Subgroup.normalizer (Z : Set G))
    (hdZ : d ∈ Subgroup.normalizer (Z : Set G))
    (hfc : Z ⊓ Subgroup.centralizer ({c} : Set G) = ⊥)
    (hfd : Z ⊓ Subgroup.centralizer ({d} : Set G) = ⊥) :
    Z = (Z ⊓ Subgroup.centralizer {c * d}) ⊔ (Z ⊓ Subgroup.centralizer {c * d⁻¹}) ∧
      (Z ⊓ Subgroup.centralizer {c * d}) ⊓ (Z ⊓ Subgroup.centralizer {c * d⁻¹}) = ⊥ := by
  let _ : CommGroup Z := { (inferInstance : Group Z) with
    mul_comm := fun x y => hZ.is_comm.comm x y }
  let σ : Z →* Z := (Z.normalizerMonoidHom ⟨c, hcZ⟩).toMonoidHom
  let τ : Z →* Z := (Z.normalizerMonoidHom ⟨d, hdZ⟩).toMonoidHom
  have hσ : ∀ y : Z, ((σ y : Z) : G) = c * y * c⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Z ⟨c, hcZ⟩ y
  have hτ : ∀ y : Z, ((τ y : Z) : G) = d * y * d⁻¹ := fun y =>
    Subgroup.normalizerMonoidHom_apply_apply_coe Z ⟨d, hdZ⟩ y
  have hccc : c * c * c = 1 := by rw [← hc3, pow_three, mul_assoc]
  have hddd : d * d * d = 1 := by rw [← hd3, pow_three, mul_assoc]
  have hσ3 : ∀ y : Z, σ (σ (σ y)) = y := fun y => Subtype.ext (by
    rw [hσ, hσ, hσ]
    calc c * (c * (c * (y : G) * c⁻¹) * c⁻¹) * c⁻¹ = (c * c * c) * y * (c * c * c)⁻¹ := by group
      _ = y := by rw [hccc]; group)
  have hτ3 : ∀ y : Z, τ (τ (τ y)) = y := fun y => Subtype.ext (by
    rw [hτ, hτ, hτ]
    calc d * (d * (d * (y : G) * d⁻¹) * d⁻¹) * d⁻¹ = (d * d * d) * y * (d * d * d)⁻¹ := by group
      _ = y := by rw [hddd]; group)
  have hστ : ∀ y : Z, σ (τ y) = τ (σ y) := fun y => Subtype.ext (by
    rw [hσ, hτ, hτ, hσ]
    calc c * (d * (y : G) * d⁻¹) * c⁻¹ = (c * d) * y * (c * d)⁻¹ := by group
      _ = (d * c) * y * (d * c)⁻¹ := by rw [hcd]
      _ = d * (c * y * c⁻¹) * d⁻¹ := by group)
  have hNσ : ∀ y : Z, σ y * σ (σ y) = y⁻¹ := fun y => by
    have h := norm_eq_one_of_inf_centralizer_eq_bot hZ hcZ hc3 hfc y.2
    rw [← hσ, ← hσ] at h
    have h' : y * (σ y * σ (σ y)) = 1 := by
      rw [← mul_assoc]
      exact Subtype.ext h
    exact eq_inv_of_mul_eq_one_right h'
  have hNτ : ∀ y : Z, τ y * τ (τ y) = y⁻¹ := fun y => by
    have h := norm_eq_one_of_inf_centralizer_eq_bot hZ hdZ hd3 hfd y.2
    rw [← hτ, ← hτ] at h
    have h' : y * (τ y * τ (τ y)) = 1 := by
      rw [← mul_assoc]
      exact Subtype.ext h
    exact eq_inv_of_mul_eq_one_right h'
  have hcdc : ∀ y : Z, (c * d) * (y : G) * (c * d)⁻¹ = ((σ (τ y) : Z) : G) := fun y => by
    rw [hσ, hτ]
    group
  have hdinv : d⁻¹ = d * d := by
    rw [inv_eq_iff_mul_eq_one, ← mul_assoc, hddd]
  have hcdi : ∀ y : Z, (c * d⁻¹) * (y : G) * (c * d⁻¹)⁻¹ = ((σ (τ (τ y)) : Z) : G) := fun y => by
    rw [hσ, hτ, hτ]
    conv_lhs => rw [hdinv]
    group
  refine ⟨le_antisymm (fun z hz => ?_) (sup_le inf_le_left inf_le_left), ?_⟩
  · set y : Z := ⟨z, hz⟩
    set n₁ : Z := y * σ (τ y) * σ (σ (τ (τ y))) with hn₁
    set n₂ : Z := y * σ (τ (τ y)) * σ (σ (τ y)) with hn₂
    have hn : n₁ * n₂ = y ^ 3 := by
      have h1 : σ (τ y) * σ (τ (τ y)) = (σ y)⁻¹ := by rw [← map_mul, hNτ, map_inv]
      have h2 : σ (σ (τ (τ y))) * σ (σ (τ y)) = (σ (σ y))⁻¹ := by
        rw [← map_mul, ← map_mul, mul_comm, hNτ, map_inv, map_inv]
      have h3 : (σ y)⁻¹ * (σ (σ y))⁻¹ = y := by rw [← mul_inv, hNσ, inv_inv]
      calc n₁ * n₂ = y * y * (σ (τ y) * σ (τ (τ y))) * (σ (σ (τ (τ y))) * σ (σ (τ y))) := by
            rw [hn₁, hn₂]
            ac_rfl
        _ = y * y * ((σ y)⁻¹ * (σ (σ y))⁻¹) := by rw [h1, h2, mul_assoc]
        _ = y ^ 3 := by rw [h3, pow_three, mul_assoc]
    have hτ4 : ∀ x : Z, τ (τ (τ (τ x))) = τ x := fun x => hτ3 (τ x)
    have hfix₁ : σ (τ n₁) = n₁ := by
      rw [hn₁, map_mul, map_mul, map_mul, map_mul]
      have e1 : σ (τ (σ (τ y))) = σ (σ (τ (τ y))) := by rw [← hστ (τ y)]
      have e2 : σ (τ (σ (σ (τ (τ y))))) = y := by
        rw [← hστ (σ (τ (τ y))), ← hστ (τ (τ y)), hτ3, hσ3]
      rw [e1, e2]
      ac_rfl
    have hfix₂ : σ (τ (τ n₂)) = n₂ := by
      rw [hn₂, map_mul, map_mul, map_mul, map_mul, map_mul, map_mul]
      have e1 : σ (τ (τ (σ (τ (τ y))))) = σ (σ (τ y)) := by
        rw [← hστ (τ (τ y)), ← hστ (τ (τ (τ y))), hτ4]
      have e2 : σ (τ (τ (σ (σ (τ y))))) = y := by
        rw [← hστ (σ (τ y)), ← hστ (τ (σ (τ y))), ← hστ (τ y), ← hστ (τ (τ y)), hτ3, hσ3]
      rw [e1, e2]
      ac_rfl
    have hmem₁ : (n₁ : G) ∈ Z ⊓ Subgroup.centralizer {c * d} := by
      refine ⟨n₁.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h := hcdc n₁
      rw [hfix₁, mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hmem₂ : (n₂ : G) ∈ Z ⊓ Subgroup.centralizer {c * d⁻¹} := by
      refine ⟨n₂.2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have h := hcdi n₂
      rw [hfix₂, mul_inv_eq_iff_eq_mul] at h
      exact h.symm
    have hz3 : z ^ 3 ∈ (Z ⊓ Subgroup.centralizer {c * d}) ⊔
        (Z ⊓ Subgroup.centralizer {c * d⁻¹}) := by
      have e : z ^ 3 = (n₁ : G) * (n₂ : G) := by
        have := congrArg Subtype.val hn
        simpa using this.symm
      rw [e]
      exact Subgroup.mul_mem_sup hmem₁ hmem₂
    have hgcd : Nat.gcd 3 (orderOf z) = 1 := by
      have hdvd : orderOf z ∣ Nat.card Z := by
        have := orderOf_dvd_natCard (⟨z, hz⟩ : Z)
        rwa [Subgroup.orderOf_mk] at this
      exact Nat.Coprime.coprime_dvd_right hdvd hcop
    have hzmem : z ∈ Subgroup.zpowers (z ^ 3) := mem_zpowers_pow_iff.mpr hgcd
    exact (Subgroup.zpowers_le.mpr hz3) hzmem
  · rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_inf] at hz
    obtain ⟨⟨hzZ, hz₁⟩, -, hz₂⟩ := hz
    rw [Subgroup.mem_centralizer_singleton_iff] at hz₁ hz₂
    have hcc : z * (c * c) = (c * c) * z := by
      calc z * (c * c) = z * ((c * d) * (c * d⁻¹)) := by
            rw [show (c * d) * (c * d⁻¹) = c * c by
              rw [mul_assoc, ← mul_assoc d c, ← hcd, mul_assoc, mul_inv_cancel, mul_one]]
        _ = (c * d) * (c * d⁻¹) * z := by
            rw [← mul_assoc, hz₁, mul_assoc, hz₂, ← mul_assoc]
        _ = (c * c) * z := by
            rw [show (c * d) * (c * d⁻¹) = c * c by
              rw [mul_assoc, ← mul_assoc d c, ← hcd, mul_assoc, mul_inv_cancel, mul_one]]
    have hc4 : c * c * (c * c) = c := by
      calc c * c * (c * c) = (c * c * c) * c := by group
        _ = c := by rw [hccc, one_mul]
    have hzc : z * c = c * z := by
      calc z * c = z * (c * c * (c * c)) := by rw [hc4]
        _ = (c * c * (c * c)) * z := by rw [← mul_assoc, hcc, mul_assoc, hcc, ← mul_assoc]
        _ = c * z := by rw [hc4]
    have hmem : z ∈ Z ⊓ Subgroup.centralizer ({c} : Set G) :=
      ⟨hzZ, Subgroup.mem_centralizer_singleton_iff.mpr hzc⟩
    rw [hfc] at hmem
    exact hmem

end Decomposition

end CFSG.RankThree.PartTwo.Sec17
