module

public import CFSG.Quasithin.Background.SmithB42HatA6Norm

public section

namespace CFSG.Quasithin

namespace F918Fine4Pf

open Equiv Equiv.Perm

section Alt

variable {α : Type*} [Fintype α] [DecidableEq α]

theorem cycleType_of_three (hα : Fintype.card α = 6) {σ : Perm α} (h3 : σ ^ 3 = 1)
    (h1 : σ ≠ 1) :
    (σ.cycleType = Multiset.replicate 1 3 ∧ ∃ a, σ a = a) ∨
      (σ.cycleType = Multiset.replicate 2 3 ∧ ∀ a, σ a ≠ a) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hord : orderOf σ = 3 := orderOf_eq_prime h3 h1
  obtain ⟨n, hn⟩ := cycleType_prime_order (hord ▸ Nat.prime_three : (orderOf σ).Prime)
  rw [hord] at hn
  have hsum := sum_cycleType σ
  rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hle : σ.support.card ≤ 6 := hα ▸ σ.support.card_le_univ
  rcases (show n = 0 ∨ n = 1 by omega) with rfl | rfl
  · refine Or.inl ⟨hn, ?_⟩
    by_contra hcon
    push Not at hcon
    have hs : σ.support = Finset.univ :=
      Finset.eq_univ_of_forall fun a => mem_support.mpr (hcon a)
    rw [hs, Finset.card_univ, hα] at hsum
    omega
  · refine Or.inr ⟨hn, fun a => ?_⟩
    have hs : σ.support = Finset.univ :=
      Finset.eq_univ_of_card _ (by rw [← hsum, hα])
    exact mem_support.mp (hs ▸ Finset.mem_univ a)

theorem not_centralizer_le_alternating_of_three (hα : Fintype.card α = 6) {σ : Perm α}
    (h3 : σ ^ 3 = 1) (h1 : σ ≠ 1) :
    ¬ Subgroup.centralizer {σ} ≤ alternatingGroup α := by
  rw [centralizer_le_alternating_iff]
  rintro ⟨-, hcard, hcount⟩
  rcases cycleType_of_three hα h3 h1 with ⟨hc, -⟩ | ⟨hc, -⟩
  · rw [hc, hα, Multiset.sum_replicate, smul_eq_mul] at hcard
    omega
  · have := hcount 3
    rw [hc, Multiset.count_replicate_self] at this
    omega

theorem isConj_alt_of_isConj {σ τ : alternatingGroup α} (hc : IsConj (σ : Perm α) (τ : Perm α))
    (hcen : ¬ Subgroup.centralizer {(σ : Perm α)} ≤ alternatingGroup α) : IsConj σ τ := by
  obtain ⟨π, hπ⟩ := isConj_iff.1 hc
  rcases Int.units_eq_one_or (sign π) with h | h
  · exact isConj_iff.2 ⟨⟨π, mem_alternatingGroup.mpr h⟩, Subtype.ext (by simpa using hπ)⟩
  · obtain ⟨ζ, hζc, hζA⟩ := Set.not_subset.mp hcen
    have hζs : sign ζ = -1 :=
      (Int.units_eq_one_or (sign ζ)).resolve_left fun h1 => hζA (mem_alternatingGroup.mpr h1)
    have hζσ : ζ * (σ : Perm α) = (σ : Perm α) * ζ :=
      Subgroup.mem_centralizer_singleton_iff.mp hζc
    refine isConj_iff.2 ⟨⟨π * ζ, mem_alternatingGroup.mpr ?_⟩, Subtype.ext ?_⟩
    · rw [map_mul, h, hζs]
      decide
    · show π * ζ * (σ : Perm α) * (π * ζ)⁻¹ = (τ : Perm α)
      rw [← hπ, mul_inv_rev, mul_assoc π ζ, hζσ]
      group

theorem alt_isConj_of_three (hα : Fintype.card α = 6) {σ τ : alternatingGroup α}
    (hσ3 : σ ^ 3 = 1) (hσ1 : σ ≠ 1) (hτ3 : τ ^ 3 = 1) (hτ1 : τ ≠ 1)
    (hfix : (∃ a, (σ : Perm α) a = a) ↔ ∃ a, (τ : Perm α) a = a) : IsConj σ τ := by
  have hσ3' : (σ : Perm α) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hσ3, Subgroup.coe_one]
  have hτ3' : (τ : Perm α) ^ 3 = 1 := by rw [← Subgroup.coe_pow, hτ3, Subgroup.coe_one]
  have hσ1' : (σ : Perm α) ≠ 1 := fun h => hσ1 (Subtype.ext h)
  have hτ1' : (τ : Perm α) ≠ 1 := fun h => hτ1 (Subtype.ext h)
  refine isConj_alt_of_isConj ?_ (not_centralizer_le_alternating_of_three hα hσ3' hσ1')
  rw [isConj_iff_cycleType_eq]
  rcases cycleType_of_three hα hσ3' hσ1' with ⟨hσc, hσf⟩ | ⟨hσc, hσf⟩ <;>
    rcases cycleType_of_three hα hτ3' hτ1' with ⟨hτc, hτf⟩ | ⟨hτc, hτf⟩
  · rw [hσc, hτc]
  · obtain ⟨a, ha⟩ := hfix.mp hσf
    exact absurd ha (hτf a)
  · obtain ⟨a, ha⟩ := hfix.mpr hτf
    exact absurd ha (hσf a)
  · rw [hσc, hτc]

end Alt

section Normalizer

open HatA6 CFSG.CharacterTheory.SteinbergBY

variable {V : Type} [CommGroup V] [Finite V]

omit [Finite V] in
theorem coordEquiv_pow_smul {hsq : ∀ v : V, v * v = 1} {z : MulAut V} {u : Fin 3 → V}
    (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w) (j : ℕ)
    (d : Fin 3 → FieldFour) :
    coordEquiv hb (Multiplicative.ofAdd ((FieldFour.ω ^ j) • d)) =
      (z ^ j) (coordEquiv hb (Multiplicative.ofAdd d)) := by
  induction j generalizing d with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', mul_smul, coordEquiv_smul hb hzz, fsmul_ω, ih, pow_succ', MulAut.mul_apply]

omit [Finite V] in
theorem fixPt_iff {hsq : ∀ v : V, v * v = 1} {z : MulAut V} {u : Fin 3 → V}
    (hb : Function.Bijective (coordHom hsq z u)) (hzz : ∀ w, z (z w) = w * z w)
    {L : Subgroup (MulAut V)} (hLz : ∀ x ∈ L, ∀ w, x (z w) = z (x w)) {O : Set V}
    (hO : ∀ l ∈ L, ∀ v ∈ O, l v ∈ O) (x : ↥L) :
    (∃ p, ptPerm hb hzz hLz O hO x p = p) ↔
      ∃ v ∈ O, ∃ j : ℕ, (x : MulAut V) v = (z ^ j) v := by
  constructor
  · rintro ⟨p, hp⟩
    obtain ⟨c, hc, hcp⟩ := (mem_pts hb O).1 p.2
    have h1 := congrArg Subtype.val hp
    rw [ptPerm_apply, ptAct_coe, ← hcp, map_span_singleton] at h1
    obtain ⟨w, hw⟩ := (span_eq_iff).1 h1
    obtain ⟨j, hj⟩ : ∃ j : ℕ, (w : FieldFour) = FieldFour.ω ^ j := by
      rcases ff_unit_cases w with h | h | h
      · exact ⟨0, by rw [h, pow_zero]⟩
      · exact ⟨1, by rw [h, pow_one]⟩
      · exact ⟨2, by rw [h]; decide⟩
    refine ⟨coordEquiv hb (Multiplicative.ofAdd c), (mem_okSet hb O).1 hc, j, ?_⟩
    rw [← coordEquiv_linL hb hzz hLz x c, ← hw, Units.smul_def, hj, coordEquiv_pow_smul hb hzz]
  · rintro ⟨v, hv, j, hj⟩
    set c := Multiplicative.toAdd ((coordEquiv hb).symm v) with hcdef
    have hcv : coordEquiv hb (Multiplicative.ofAdd c) = v := by
      rw [hcdef, ofAdd_toAdd, MulEquiv.apply_symm_apply]
    have hc : c ∈ okSet hb O := (mem_okSet hb O).2 (hcv ▸ hv)
    have hlin : linL hb hzz hLz x c = FieldFour.ω ^ j • c := by
      apply Multiplicative.ofAdd.injective
      apply (coordEquiv hb).injective
      rw [coordEquiv_linL, coordEquiv_pow_smul hb hzz, hcv, hj]
    refine ⟨⟨FieldFour ∙ c, (mem_pts hb O).2 ⟨c, hc, rfl⟩⟩, Subtype.ext ?_⟩
    rw [ptPerm_apply, ptAct_coe, map_span_singleton, hlin]
    exact Submodule.span_singleton_smul_eq
      (IsUnit.pow j (isUnit_iff_ne_zero.mpr (by decide : FieldFour.ω ≠ 0))) c

theorem exists_conj_mod_center (hsq2 : ∀ v : V, v ^ 2 = 1) (hV : Nat.card V = 2 ^ 6)
    {L : Subgroup (MulAut V)} (hperf : Group.IsPerfect ↥L)
    (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (e : ↥L ⧸ Subgroup.center ↥L ≃* alternatingGroup (Fin 6))
    (hirr : ∀ J : Subgroup V, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤)
    {g : MulAut V} (hgN : ∀ l, l ∈ L ↔ g * l * g⁻¹ ∈ L)
    {x : ↥L} (hx3 : x ^ 3 ∈ Subgroup.center ↥L) (hx1 : x ∉ Subgroup.center ↥L) :
    ∃ l : ↥L, (l * x * l⁻¹)⁻¹ * ⟨g * x * g⁻¹, (hgN x).1 x.2⟩ ∈ Subgroup.center ↥L := by
  classical
  obtain ⟨zL, hcen, h3, hfp⟩ := exists_center_fpf hsq2 hV hperf hZ e
  have hsq : ∀ v : V, v * v = 1 := fun v => by rw [← pow_two]; exact hsq2 v
  set z : MulAut V := (zL : MulAut V) with hzdef
  have hzz : ∀ w, z (z w) = w * z w := fun w =>
    H13.zz_eq_of_fpf hsq2 h3 (W := ⊤) (fun _ _ => trivial) (fun w _ hw => hfp w hw) trivial
  obtain ⟨u, hb⟩ := exists_coord hsq hV h3 hfp
  have hzc : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
  have hLz : ∀ l ∈ L, ∀ w, l (z w) = z (l w) := by
    intro l hl w
    have h1 := Subgroup.mem_center_iff.1 hzc ⟨l, hl⟩
    exact congrArg (fun y : ↥L => (y : MulAut V) w) h1
  have hperf' : commutator ↥L = ⊤ := Group.isPerfect_def.1 hperf
  have hfpf : ∀ k ∈ Subgroup.center ↥L, k ≠ 1 → ∀ v : V, (k : MulAut V) v = v → v = 1 := by
    intro k hk hk1 v hv
    rw [hcen] at hk
    obtain ⟨n, hn0⟩ := (mem_powers_iff_mem_zpowers).2 hk
    have hn0' : zL ^ n = k := hn0
    rw [← hn0'] at hk1 hv
    have hz3 : zL ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact h3)
    have hn : zL ^ n = zL ^ (n % 3) := by
      conv_lhs => rw [← Nat.div_add_mod n 3, pow_add, pow_mul, hz3, one_pow, one_mul]
    rw [hn] at hk1 hv
    have hn3 : n % 3 < 3 := Nat.mod_lt _ (by norm_num)
    interval_cases (n % 3)
    · exact absurd (pow_zero zL) hk1
    · exact hfp v (by simpa using hv)
    · apply hfp v
      have h2 : z (z v) = v := by simpa [pow_two, MulAut.mul_apply] using hv
      calc z v = z (z (z v)) := by rw [h2]
        _ = v := by
          have := congrArg (fun y : MulAut V => y v) h3
          simpa [pow_succ, MulAut.mul_apply] using this
  obtain ⟨f, hf1, hf⟩ := H13.Orbit.hatA6_orbits hV hperf' hZ e hfpf
  set O := H13.Orbit.orbitIn L f with hOdef
  have hO : ∀ l ∈ L, ∀ v ∈ O, l v ∈ O := by
    rintro l hl _ ⟨m, hm, rfl⟩
    exact ⟨l * m, L.mul_mem hl hm, rfl⟩
  have hfO : f ∈ O := ⟨1, L.one_mem, rfl⟩
  have hOcard : Nat.card O = 18 := (hf f hf1).1 hfO
  have h1O : (1 : V) ∉ O := by
    rintro ⟨m, -, hm⟩
    apply hf1
    have := congrArg (fun w => m⁻¹ w) hm
    simpa using this
  have hpres : ∀ y : MulAut V, (∀ l, l ∈ L ↔ y * l * y⁻¹ ∈ L) → ∀ v ∈ O, y v ∈ O := by
    intro y hyN v hv
    have hv1 : v ≠ 1 := fun h => h1O (h ▸ hv)
    have hyv1 : y v ≠ 1 := fun h => hv1 (y.injective (h.trans (map_one y).symm))
    have hvO : H13.Orbit.orbitIn L v = O := by
      obtain ⟨m, hm, rfl⟩ := hv
      ext w
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨n * m, L.mul_mem hn hm, rfl⟩
      · rintro ⟨n, hn, rfl⟩
        refine ⟨n * m⁻¹, L.mul_mem hn (L.inv_mem hm), ?_⟩
        simp [MulAut.mul_apply]
    by_contra hcon
    have h18 : Nat.card (H13.Orbit.orbitIn L (y v)) = 18 := by
      rw [card_orbitIn_map hyN v, hvO, hOcard]
    have h45 := (hf (y v) hyv1).2 hcon
    omega
  have hinvN : ∀ y : MulAut V, (∀ l, l ∈ L ↔ y * l * y⁻¹ ∈ L) →
      ∀ l, l ∈ L ↔ y⁻¹ * l * y⁻¹⁻¹ ∈ L := by
    intro y hyN l
    have h1 := hyN (y⁻¹ * l * y⁻¹⁻¹)
    have e1 : y * (y⁻¹ * l * y⁻¹⁻¹) * y⁻¹ = l := by group
    rw [e1] at h1
    exact h1.symm
  have hconjZ : ∀ y : MulAut V, (∀ l, l ∈ L ↔ y * l * y⁻¹ ∈ L) → ∀ k : ↥L,
      k ∈ Subgroup.center ↥L → ∀ hk : y * (k : MulAut V) * y⁻¹ ∈ L,
        (⟨_, hk⟩ : ↥L) ∈ Subgroup.center ↥L := by
    intro y hyN k hk hk'
    rw [Subgroup.mem_center_iff] at hk ⊢
    intro l
    apply Subtype.ext
    have hl' : y⁻¹ * (l : MulAut V) * y⁻¹⁻¹ ∈ L := (hinvN y hyN l).1 l.2
    have h1 := congrArg Subtype.val (hk ⟨_, hl'⟩)
    simp only [Subgroup.coe_mul] at h1
    show (l : MulAut V) * (y * k * y⁻¹) = y * k * y⁻¹ * l
    calc (l : MulAut V) * (y * k * y⁻¹) = y * ((y⁻¹ * l * y⁻¹⁻¹) * k) * y⁻¹ := by group
      _ = y * (k * (y⁻¹ * l * y⁻¹⁻¹)) * y⁻¹ := by rw [h1]
      _ = y * k * y⁻¹ * l := by group
  have hzpow : ∀ y : MulAut V, (∀ l, l ∈ L ↔ y * l * y⁻¹ ∈ L) → ∃ m : ℕ, y * z * y⁻¹ = z ^ m := by
    intro y hyN
    have hmem : y * z * y⁻¹ ∈ L := (hyN z).1 zL.2
    have hc := hconjZ y hyN zL hzc hmem
    rw [hcen] at hc
    obtain ⟨m, hm⟩ := (mem_powers_iff_mem_zpowers).2 hc
    have hm' : zL ^ m = ⟨_, hmem⟩ := hm
    exact ⟨m, by rw [hzdef, ← Subgroup.coe_pow, hm']⟩
  have htrans : ∀ y : MulAut V, (∀ l, l ∈ L ↔ y * l * y⁻¹ ∈ L) → ∀ w : ↥L,
      (∃ v ∈ O, ∃ j : ℕ, (w : MulAut V) v = (z ^ j) v) →
        ∃ v ∈ O, ∃ j : ℕ, (y * (w : MulAut V) * y⁻¹) v = (z ^ j) v := by
    rintro y hyN w ⟨v, hv, j, hj⟩
    obtain ⟨m, hm⟩ := hzpow y hyN
    refine ⟨y v, hpres y hyN v hv, m * j, ?_⟩
    have h1 : y * z ^ j * y⁻¹ = z ^ (m * j) := by rw [← conj_pow, hm, ← pow_mul]
    calc (y * (w : MulAut V) * y⁻¹) (y v) = y ((w : MulAut V) v) := by simp [MulAut.mul_apply]
      _ = y ((z ^ j) v) := by rw [hj]
      _ = (y * z ^ j * y⁻¹) (y v) := by simp [MulAut.mul_apply]
      _ = (z ^ (m * j)) (y v) := by rw [h1]
  set π := ptPerm hb hzz hLz O hO with hπdef
  have hcP : Fintype.card ↥(pts hb O) = 6 := by
    rw [Fintype.card_coe]
    exact card_pts_eq hb hzz hO rfl hOcard h1O
  have hrange := range_ptPerm hb hzz hLz hO hirr hV rfl hcen e hOcard h1O
  have hinj := altPerm_injective hb hzz hLz hO hirr hV rfl hcen e hOcard h1O
  have hker : ∀ l : ↥L, π l = 1 → l ∈ Subgroup.center ↥L := by
    intro l hl
    rw [hπdef, ptPerm_eq_altPerm hb hzz hLz hO rfl hcen e l] at hl
    have h1 : e (QuotientGroup.mk l) = 1 := hinj (hl.trans (map_one _).symm)
    have h2 : (QuotientGroup.mk l : ↥L ⧸ Subgroup.center ↥L) = 1 :=
      e.injective (h1.trans (map_one e).symm)
    exact (QuotientGroup.eq_one_iff l).mp h2
  have hZk : ∀ l : ↥L, l ∈ Subgroup.center ↥L → π l = 1 := fun l hl =>
    center_le_ker_ptPerm hb hzz hLz hO rfl hcen hl
  set y : ↥L := ⟨g * x * g⁻¹, (hgN x).1 x.2⟩ with hydef
  have hy3 : y ^ 3 ∈ Subgroup.center ↥L := by
    have hmem : g * ((x ^ 3 : ↥L) : MulAut V) * g⁻¹ ∈ L := (hgN _).1 (x ^ 3).2
    have h1 := hconjZ g hgN (x ^ 3) hx3 hmem
    have e1 : y ^ 3 = ⟨_, hmem⟩ := Subtype.ext (by
      show ((g * (x : MulAut V) * g⁻¹) ^ 3 : MulAut V) = g * ((x : MulAut V) ^ 3) * g⁻¹
      exact conj_pow)
    rw [e1]
    exact h1
  have hy1 : y ∉ Subgroup.center ↥L := by
    intro hy
    have hmem : g⁻¹ * (y : MulAut V) * g⁻¹⁻¹ ∈ L := (hinvN g hgN _).1 y.2
    have h1 := hconjZ g⁻¹ (hinvN g hgN) y hy hmem
    have e1 : (⟨_, hmem⟩ : ↥L) = x := by
      apply Subtype.ext
      show g⁻¹ * (g * (x : MulAut V) * g⁻¹) * g⁻¹⁻¹ = x
      group
    rw [e1] at h1
    exact hx1 h1
  have hσmem : π x ∈ alternatingGroup ↥(pts hb O) := hrange ▸ ⟨x, rfl⟩
  have hτmem : π y ∈ alternatingGroup ↥(pts hb O) := hrange ▸ ⟨y, rfl⟩
  have hσ3 : (⟨π x, hσmem⟩ : alternatingGroup ↥(pts hb O)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow]; exact hZk _ hx3)
  have hτ3 : (⟨π y, hτmem⟩ : alternatingGroup ↥(pts hb O)) ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow]; exact hZk _ hy3)
  have hσ1 : (⟨π x, hσmem⟩ : alternatingGroup ↥(pts hb O)) ≠ 1 :=
    fun h => hx1 (hker x (congrArg Subtype.val h))
  have hτ1 : (⟨π y, hτmem⟩ : alternatingGroup ↥(pts hb O)) ≠ 1 :=
    fun h => hy1 (hker y (congrArg Subtype.val h))
  have hfix : (∃ p, π x p = p) ↔ ∃ p, π y p = p := by
    rw [hπdef, fixPt_iff hb hzz hLz hO x, fixPt_iff hb hzz hLz hO y]
    constructor
    · exact htrans g hgN x
    · intro hy'
      obtain ⟨v, hv, j, hj⟩ := htrans g⁻¹ (hinvN g hgN) y hy'
      refine ⟨v, hv, j, ?_⟩
      have e1 : g⁻¹ * (y : MulAut V) * g⁻¹⁻¹ = x := by
        show g⁻¹ * (g * (x : MulAut V) * g⁻¹) * g⁻¹⁻¹ = x
        group
      rw [e1] at hj
      exact hj
  obtain ⟨ρ, hρ⟩ := isConj_iff.mp (alt_isConj_of_three hcP hσ3 hσ1 hτ3 hτ1 hfix)
  obtain ⟨l, hl⟩ : ∃ l : ↥L, π l = ρ := hrange.ge ρ.2
  refine ⟨l, hker _ ?_⟩
  have hρ' := congrArg Subtype.val hρ
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hρ'
  rw [map_mul, map_inv, map_mul, map_mul, map_inv, hl, hρ', inv_mul_cancel]

end Normalizer

end F918Fine4Pf

end CFSG.Quasithin
