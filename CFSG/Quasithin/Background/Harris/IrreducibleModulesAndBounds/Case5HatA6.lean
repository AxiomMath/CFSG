module

public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case5HatA6Form
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.Case5HatA6Nine
public import CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds.AutRank
public import CFSG.Quasithin.Background.Harris.OrdinaryProofs.ConjTransport

public section

namespace CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds

open CFSG.Quasithin CFSG.Quasithin.G11 Module CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.Quasithin.Background.Harris.OrdinaryProofs

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem case5_center_data {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤)
    (hZ : Nat.card (Subgroup.center ↥L) = 3) :
    ∃ zL : ↥L, Subgroup.center ↥L = Subgroup.zpowers zL ∧ (zL : GLV V) ^ 3 = 1 ∧
      (zL : GLV V) ≠ 1 ∧ ∀ v : V, (zL : GLV V) v = v → v = 0 := by
  have hZ1 : Subgroup.center ↥L ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hZ
    omega
  obtain ⟨⟨z, hzc⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hZ1
  have hz1' : z ≠ 1 := fun h => hz1 (Subtype.ext h)
  have h3 : z ^ 3 = 1 := by
    have h := pow_card_eq_one' (G := ↥(Subgroup.center ↥L)) (x := ⟨z, hzc⟩)
    rw [hZ] at h
    exact congrArg Subtype.val h
  have hzV : (z : GLV V) ≠ 1 := fun h => hz1' (Subtype.ext h)
  refine ⟨z, ?_, by rw [← Subgroup.coe_pow, h3]; rfl, hzV, ?_⟩
  · have hle : Subgroup.zpowers z ≤ Subgroup.center ↥L := Subgroup.zpowers_le.2 hzc
    have hord : orderOf z = 3 := orderOf_eq_prime h3 hz1'
    refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
    rw [hZ, Nat.card_zpowers, hord]
  ·
    let J : Submodule (ZMod 2) V := LinearMap.ker ((z : GLV V).toLinearMap - LinearMap.id)
    have hJ : ∀ v, v ∈ J ↔ (z : GLV V) v = v := by
      intro v
      simp [J, LinearMap.mem_ker, sub_eq_zero]
    have hinv : Invariant L J := by
      intro k hk v hv
      rw [hJ] at hv ⊢
      have hc := Subgroup.mem_center_iff.1 hzc ⟨k, hk⟩
      have hc' : k * (z : GLV V) = (z : GLV V) * k := congrArg Subtype.val hc
      have := congrArg (fun g : GLV V => g v) hc'
      simp only [LinearEquiv.mul_apply] at this
      rw [← this]
      simp [hv]
    rcases hirr.2.2 J hinv bot_le le_top with h | h
    · intro v hv
      have : v ∈ J := (hJ v).2 hv
      rw [h] at this
      simpa using this
    · exfalso
      apply hzV
      ext v
      have : v ∈ J := h ▸ Submodule.mem_top
      exact (hJ v).1 this

theorem case5_two_pow_mod_nine {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤)
    (hq : CFSG.Open.IsQuasisimple ↥L) (hZ : Nat.card (Subgroup.center ↥L) = 3)
    (e : (↥L ⧸ Subgroup.center ↥L) ≃* ↥(alternatingGroup (Fin 6))) :
    2 ^ finrank (ZMod 2) V % 9 = 1 := by
  obtain ⟨zL, hcen, h3, hz1, hfp⟩ := case5_center_data hirr hZ
  let L' : Subgroup (MulAut (Multiplicative V)) := toMulSub L
  let z' : ↥L' := toMulSubEquiv L zL
  have hzz : (z' : MulAut (Multiplicative V)) = linEquivMulAut (zL : GLV V) := rfl
  have hP : CFSG.Quasithin.B42TypeHatA6 ↥L' := by
    refine ⟨isQuasisimple_toMulSub hq, ?_, ⟨cqEquiv_toMulSub_comp e⟩⟩
    rw [← map_center_toMulSubEquiv L]
    rw [Subgroup.card_map_of_injective (toMulSubEquiv L).injective]
    exact hZ
  have hcen' : Subgroup.center ↥L' = Subgroup.zpowers z' := by
    rw [← map_center_toMulSubEquiv L, hcen, MonoidHom.map_zpowers]
    rfl
  have h3' : (z' : MulAut (Multiplicative V)) ^ 3 = 1 := by
    rw [hzz, ← map_pow, h3, map_one]
  have hz1' : (z' : MulAut (Multiplicative V)) ≠ 1 := by
    rw [hzz]
    intro h
    exact hz1 (linEquivMulAut.injective (h.trans (map_one _).symm))
  have hfp' : ∀ v : Multiplicative V, (z' : MulAut (Multiplicative V)) v = v → v = 1 := by
    intro v hv
    rw [hzz] at hv
    have : (zL : GLV V) (Multiplicative.toAdd v) = Multiplicative.toAdd v := by
      have := congrArg Multiplicative.toAdd hv
      exact this
    have h0 := hfp _ this
    exact Multiplicative.toAdd.injective h0
  have h9 := CFSG.Quasithin.B45HatA6.case5_card_mod_nine hP z' hcen' h3' hz1' hfp'
  rwa [natCard_multiplicative] at h9


theorem case5_mulAut_eq_of_mem_center {N : Type*} [Group N] (hperf : commutator N = ⊤)
    {φ ψ : MulAut N} (h : ∀ x : N, (ψ x)⁻¹ * φ x ∈ Subgroup.center N) : φ = ψ := by
  let f : N →* Subgroup.center N :=
    { toFun := fun x => ⟨(ψ x)⁻¹ * φ x, h x⟩
      map_one' := by
        apply Subtype.ext
        simp
      map_mul' := fun x y => by
        apply Subtype.ext
        show (ψ (x * y))⁻¹ * φ (x * y) = ((ψ x)⁻¹ * φ x) * ((ψ y)⁻¹ * φ y)
        have hc := Subgroup.mem_center_iff.1 (h x) (ψ y)⁻¹
        rw [map_mul, map_mul, mul_inv_rev]
        calc (ψ y)⁻¹ * (ψ x)⁻¹ * (φ x * φ y)
            = (ψ y)⁻¹ * ((ψ x)⁻¹ * φ x) * φ y := by simp only [mul_assoc]
          _ = ((ψ x)⁻¹ * φ x) * (ψ y)⁻¹ * φ y := by rw [hc]
          _ = ((ψ x)⁻¹ * φ x) * ((ψ y)⁻¹ * φ y) := by simp only [mul_assoc] }
  have hker : commutator N ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro a _ b _
    rw [MonoidHom.mem_ker, map_commutatorElement]
    exact commutatorElement_eq_one_iff_mul_comm.2
      (Subtype.ext (Subgroup.mem_center_iff.1 (f b).2 (f a : N)))
  rw [hperf] at hker
  ext x
  have h1 : f x = 1 := hker (Subgroup.mem_top x)
  have h2 : (ψ x)⁻¹ * φ x = 1 := congrArg Subtype.val h1
  exact (inv_mul_eq_one.1 h2).symm

@[expose] def case5_quotAut (N : Type) [Group N] : MulAut N →* MulAut (N ⧸ Subgroup.center N) where
  toFun φ := QuotientGroup.congr _ _ φ (Subgroup.map_center_eq φ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    rfl

theorem case5_quotAut_mk (N : Type) [Group N] (φ : MulAut N) (x : N) :
    case5_quotAut N φ (QuotientGroup.mk x) = QuotientGroup.mk (φ x) := rfl

theorem case5_quotAut_injective (N : Type) [Group N] (hperf : commutator N = ⊤) :
    Function.Injective (case5_quotAut N) := by
  rw [injective_iff_map_eq_one]
  intro φ hφ
  refine case5_mulAut_eq_of_mem_center hperf (ψ := 1) ?_
  intro x
  have := congrArg (fun a : MulAut (N ⧸ Subgroup.center N) => a (QuotientGroup.mk x)) hφ
  simp only [case5_quotAut_mk, MulAut.one_apply] at this
  rw [QuotientGroup.eq] at this
  have h2 := (Subgroup.center N).inv_mem this
  simpa using h2


open CFSG.QuasithinUnique.Setup in
theorem case5_autRank {N : Type} [Group N] (hperf : commutator N = ⊤)
    (e : (N ⧸ Subgroup.center N) ≃* ↥(alternatingGroup (Fin 6))) :
    ∀ B : Subgroup (MulAut N), (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) →
      (∀ x ∈ B, x * x = 1) → Nat.card B ≤ 2 ^ 3 := by
  intro B hc hs
  let Φ : MulAut N →* MulAut (alternatingGroup (Fin 6)) :=
    (MulAut.congr e).toMonoidHom.comp (case5_quotAut N)
  have hΦ : Function.Injective Φ :=
    (MulAut.congr e).injective.comp (case5_quotAut_injective N hperf)
  have hcard : Nat.card (B.map Φ) = Nat.card B := Subgroup.card_map_of_injective hΦ
  rw [← hcard]
  by_cases hbot : B.map Φ = ⊥
  · rw [hbot, Subgroup.card_bot]; norm_num
  · have : CFSG.IsElementaryAbelian 2 ↥(B.map Φ) :=
      { toIsMulCommutative := ⟨⟨by
          rintro ⟨_, a, ha, rfl⟩ ⟨_, b, hb, rfl⟩
          apply Subtype.ext
          show Φ a * Φ b = Φ b * Φ a
          rw [← map_mul, ← map_mul, hc a ha b hb]⟩⟩
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
          obtain ⟨_, a, ha, rfl⟩ := x
          apply Subtype.ext
          show Φ a ^ 2 = 1
          rw [← map_pow, pow_two, hs a ha, map_one] }
    obtain ⟨r, m, hr, -, hr3, -⟩ :=
      CFSG.QuasithinUnique.Setup.X3Aut.a6ShortGeneration.2.2.2 (B.map Φ) hbot this
    rw [hr]
    exact Nat.pow_le_pow_right (by norm_num) hr3


theorem case5_endIsField_two {L : Subgroup (GLV V)} (hirr : IsIrr L ⊤)
    (hd : finrank (ZMod 2) V = 6)
    {z : GLV V} (hzc : ∀ l ∈ L, z * l = l * z) (hz3 : z ^ 3 = 1) (hz1 : z ≠ 1)
    (hnc : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) : EndIsField L 2 := by
  classical
  have := endCommutant_nontrivial hirr
  have := endCommutant_noZeroDivisors hirr
  have : IsDomain (endCommutant L) := NoZeroDivisors.to_isDomain _
  have : Finite (Module.End (ZMod 2) V) :=
    Finite.of_injective (fun f : Module.End (ZMod 2) V => (f : V → V)) LinearMap.coe_injective
  have : Finite (endCommutant L) := Subtype.finite
  let _ : Field (endCommutant L) := (Finite.isDomain_to_isField (endCommutant L)).toField
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := endCommutant L
  have hcard : Nat.card K = 2 ^ finrank (ZMod 2) K := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod]
  generalize he : finrank (ZMod 2) K = e at hcard
  have hVK : Nat.card V = Nat.card K ^ finrank K V := Module.natCard_eq_pow_finrank (K := K)
  have hV64 : Nat.card V = 2 ^ 6 := by
    rw [Module.natCard_eq_pow_finrank (K := ZMod 2), Nat.card_zmod, hd]
  have hek : e * finrank K V = 6 := by
    rw [hVK, hcard, ← pow_mul] at hV64
    exact Nat.pow_right_injective (le_refl 2) hV64
  have hzK : (z : Module.End (ZMod 2) V) ∈ endCommutant L := by
    rw [mem_endCommutant_iff]
    intro h hh
    have := hzc h hh
    ext v
    have h2 := congrArg (fun g : GLV V => g v) this.symm
    simpa using h2
  let ζ : K := ⟨(z : Module.End (ZMod 2) V), hzK⟩
  have hζ3 : ζ ^ 3 = 1 := by
    apply Subtype.ext
    ext v
    have h1 := congrArg (fun g : GLV V => g v) hz3
    have h2 := case5_pow_apply_eq z 3 v
    simp only [OneMemClass.coe_one, Module.End.one_apply]
    rw [SubmonoidClass.coe_pow]
    rw [← h2]
    simpa using h1
  have hζ1 : ζ ≠ 1 := by
    intro h
    apply hz1
    ext v
    have : (z : Module.End (ZMod 2) V) v = (1 : Module.End (ZMod 2) V) v :=
      congrArg (fun f : K => (f : Module.End (ZMod 2) V) v) h
    simpa using this
  have hζne : ζ ≠ 0 := by
    intro h; rw [h] at hζ3; simp at hζ3
  have h3dvd : 3 ∣ 2 ^ e - 1 := by
    have : Fintype K := Fintype.ofFinite K
    have h1 := FiniteField.pow_card_sub_one_eq_one ζ hζne
    have h2 : orderOf ζ = 3 := orderOf_eq_prime hζ3 hζ1
    rw [← Nat.card_eq_fintype_card, hcard] at h1
    rw [← h2]
    exact orderOf_dvd_of_pow_eq_one h1
  have he26 : e = 2 ∨ e = 6 := by
    have hk : e ∣ 6 := ⟨_, hek.symm⟩
    have hle : e ≤ 6 := Nat.le_of_dvd (by norm_num) hk
    interval_cases e <;> omega
  rcases he26 with h2 | h6
  · have hc4 : Nat.card K = 2 ^ 2 := by rw [hcard, h2]
    exact ⟨GaloisField.algEquivGaloisField 2 2 hc4⟩
  · exfalso
    have hk1 : finrank K V = 1 := by rw [h6] at hek; omega
    obtain ⟨v, hv0, hv⟩ := finrank_eq_one_iff'.1 hk1
    obtain ⟨a, ha, b, hb, hab⟩ := hnc
    have hact : ∀ (c : K) (w : V), c • w = (c : Module.End (ZMod 2) V) w := fun c w => rfl
    have hscal : ∀ g ∈ L, ∃ cg : K, ∀ w, g w = cg • w := by
      intro g hg
      obtain ⟨cg, hcg⟩ := hv (g v)
      refine ⟨cg, fun w => ?_⟩
      obtain ⟨c, rfl⟩ := hv w
      have h1 : (c : Module.End (ZMod 2) V) (g v) = g ((c : Module.End (ZMod 2) V) v) :=
        endCommutant_apply_comm c.2 hg v
      rw [← hcg] at h1
      rw [hact, ← h1, ← hact, ← hact, smul_smul, smul_smul, mul_comm]
    obtain ⟨ca, hca⟩ := hscal a ha
    obtain ⟨cb, hcb⟩ := hscal b hb
    apply hab
    ext w
    have h1 : a (b w) = cb • (ca • w) := by
      rw [hcb w, hact cb w, ← endCommutant_apply_comm cb.2 ha w, ← hact cb, hca w]
    have h2 : b (a w) = ca • (cb • w) := by
      rw [hca w, hact ca w, ← endCommutant_apply_comm ca.2 hb w, ← hact ca, hcb w]
    show a (b w) = b (a w)
    rw [h1, h2, smul_smul, smul_smul, mul_comm]

theorem case5_hatA6_case {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* ↥(alternatingGroup (Fin 6))))
    (hZ : Nat.card (Subgroup.center ↥L) = 3) : G93Case5 L m := by
  classical
  obtain ⟨e⟩ := hX
  have hq : CFSG.Open.IsQuasisimple ↥L := h.L_comp.2.2
  have hperf : Group.IsPerfect ↥L := ⟨hq.1⟩
  obtain ⟨hq', hcardL⟩ := CFSG.Quasithin.HatA6.quasisimple_card hperf hZ e
  have hm3 : m ≤ 3 :=
    m_le_of_autRank h (MulEquiv.refl ↥L) (case5_autRank hq.1 e)
  have hmod9 := case5_two_pow_mod_nine h.H_irr hq hZ e
  have hbound := h.bound
  have hpos : 0 < finrank (ZMod 2) V := by
    obtain ⟨v, -, hv⟩ := (Submodule.ne_bot_iff _).mp (ne_of_lt h.H_irr.2.1).symm
    have : Nontrivial V := ⟨v, 0, hv⟩
    exact Module.finrank_pos
  have hd6 : finrank (ZMod 2) V = 6 := by
    have hle : finrank (ZMod 2) V ≤ 8 := by omega
    generalize finrank (ZMod 2) V = d at hpos hle hmod9
    interval_cases d <;> omega
  obtain ⟨zL, hcen, hz3, hz1, hfp⟩ := case5_center_data h.H_irr hZ
  have hzc : ∀ l ∈ L, (zL : GLV V) * l = l * (zL : GLV V) := by
    intro l hl
    have hzcen : zL ∈ Subgroup.center ↥L := hcen ▸ Subgroup.mem_zpowers zL
    have := Subgroup.mem_center_iff.1 hzcen ⟨l, hl⟩
    exact (congrArg Subtype.val this).symm
  have h5 : 5 ∣ Nat.card ↥L := by rw [hcardL]; norm_num
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨y, hy⟩ := exists_prime_orderOf_dvd_card' 5 h5
  have hy5 : (y : GLV V) ^ 5 = 1 := by
    rw [← Subgroup.coe_pow, ← hy, pow_orderOf_eq_one]; rfl
  have hy1 : (y : GLV V) ≠ 1 := by
    intro h1
    have : y = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hy
    omega
  have hnc : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    obtain ⟨a', b', hab'⟩ := hq'.2.2
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a'
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b'
    apply hab'
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
    congr 1
    exact Subtype.ext (hcon a a.2 b b.2)
  refine ⟨⟨by omega, hd6, hm3, hq', hZ, ⟨e⟩⟩, ?_, ?_⟩
  · exact case5_endIsField_two h.H_irr hd6 hzc hz3 hz1 hnc
  · exact case5_not_selfDual (by omega) zL.2 hzc hz3 hfp y.2 hy5 hy1

theorem case5_hatA6 {Γ A L : Subgroup (GLV V)} {m : ℕ} (h : G93Hyp Γ A L L m)
    (hX : Nonempty ((↥L ⧸ Subgroup.center ↥L) ≃* ↥(alternatingGroup (Fin 6))))
    (hZ : Nat.card (Subgroup.center ↥L) = 3) : G93Concl Γ L m :=
  Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (case5_hatA6_case h hX hZ))))))

end CFSG.Quasithin.Background.Harris.IrreducibleModulesAndBounds
