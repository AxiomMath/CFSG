module

public import CFSG.Quasithin.Vol2.Ch11SecAKA2
public import CFSG.Quasithin.Vol2.Ch11SecAFacts15c

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSp)

namespace KA

variable {W : Type*} [CommGroup W] {H : Subgroup (MulAut W)} {Z U : Subgroup W}

@[expose] noncomputable def qAct (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z ∈ Z) (g : ↥H) :
    W ⧸ Z →* W ⧸ Z :=
  QuotientGroup.map Z Z (g : MulAut W).toMonoidHom fun z hz => hHZ g g.2 z hz

theorem qAct_mk (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z ∈ Z) (g : ↥H) (w : W) :
    qAct hHZ g (w : W ⧸ Z) = (((g : MulAut W) w : W) : W ⧸ Z) :=
  QuotientGroup.map_mk _ _ _ _ w

theorem mk_eq_mk_iff {a b : W} : (a : W ⧸ Z) = b ↔ a * b⁻¹ ∈ Z := by
  rw [QuotientGroup.eq_iff_div_mem, div_eq_mul_inv]

theorem cocycle_mem_of_mem [Finite W] (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z ∈ Z)
    (hfix : Ch11.SecA.RadicalFixes H Z U)
    (hpt : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z) {d : ↥H → W}
    (hcoc : ∀ g h : ↥H, ((d (g * h) : W) : W ⧸ Z) = qAct hHZ g (d h) * (d g : W ⧸ Z))
    (hR : ∀ (x : ↥H) (y : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U))),
      y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)) → (y : MulAut W) = x → d x ∈ Z)
    (x : ↥H) (hx : (x : MulAut W) ∈ perfectCore (H ⊓ Ch11.SecA.stabW U)) : d x ∈ Z := by
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  set Γ := perfectCore (H ⊓ Ch11.SecA.stabW U) with hΓ
  have hΓH : ∀ y ∈ Γ, y ∈ H := fun y hy => (perfectCore_le _ hy).1
  have hR' : ∀ r : ↥Γ, r ∈ CFSG.pCore 2 ↥Γ →
      ((d ⟨r, hΓH _ r.2⟩ : W) : W ⧸ Z) = 1 := fun r hr =>
    (QuotientGroup.eq_one_iff _).mpr (hR _ r hr rfl)
  have h1 : ∀ y : ↥Γ, d ⟨y, hΓH _ y.2⟩ ∈ U := by
    intro y
    refine hfix _ fun r hr => ?_
    have hr' : y⁻¹ * r * y ∈ CFSG.pCore 2 ↥Γ := by
      have := (CFSG.pCore_normal : (CFSG.pCore 2 ↥Γ).Normal).conj_mem r hr y⁻¹
      rwa [inv_inv] at this
    have e : (⟨r, hΓH _ r.2⟩ : ↥H) * ⟨y, hΓH _ y.2⟩ =
        ⟨y, hΓH _ y.2⟩ * ⟨(y⁻¹ * r * y : ↥Γ), hΓH _ (y⁻¹ * r * y).2⟩ :=
      Subtype.ext (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group)
    have c1 := hcoc ⟨r, hΓH _ r.2⟩ ⟨y, hΓH _ y.2⟩
    rw [e, hcoc, hR' _ hr', map_one, one_mul, hR' r hr, mul_one, qAct_mk] at c1
    exact mk_eq_mk_iff.mp c1.symm
  have hperf : commutator ↥Γ = ⊤ := by
    rw [commutator_def]
    exact Group.isPerfect_def.mp (Subgroup.isPerfect_iff.mpr (perfectCore_perfect _))
  let φ : ↥Γ →* W ⧸ Z := MonoidHom.mk' (fun y => ((d ⟨y, hΓH _ y.2⟩ : W) : W ⧸ Z))
    fun a b => by
      change ((d (⟨a, hΓH _ a.2⟩ * ⟨b, hΓH _ b.2⟩) : W) : W ⧸ Z) = _
      rw [hcoc, qAct_mk, mk_eq_mk_iff.mpr (hpt _ a.2 _ (h1 b)), mul_comm]
  have h2 : φ ⟨x, hx⟩ = 1 := by
    have := Abelianization.commutator_subset_ker φ
    rw [hperf] at this
    exact this (Subgroup.mem_top _)
  exact (QuotientGroup.eq_one_iff _).mp h2

theorem radicalCocycle_of [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    (hHZ : ∀ h ∈ H, ∀ z ∈ Z, h z ∈ Z) (hfix : Ch11.SecA.RadicalFixes H Z U)
    (hpt : ∀ h ∈ perfectCore (H ⊓ Ch11.SecA.stabW U), ∀ u ∈ U, h u * u⁻¹ ∈ Z)
    {P : Subgroup (MulAut W)} (hP : QuasithinUnique.IsSylowTwoOf P H)
    (hPΓ : P ≤ perfectCore (H ⊓ Ch11.SecA.stabW U)) : Ch11.SecA.RadicalCocycle H Z U := by
  classical
  intro d hd hR
  have hcoc : ∀ g h : ↥H, ((d (g * h) : W) : W ⧸ Z) = qAct hHZ g (d h) * (d g : W ⧸ Z) := by
    intro g h
    rw [qAct_mk, ← QuotientGroup.mk_mul]
    exact mk_eq_mk_iff.mpr (hd g h)
  have hvan := cocycle_mem_of_mem hHZ hfix hpt hcoc hR
  set Q := P.subgroupOf H with hQ
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  have : Fintype (↥H ⧸ Q) := Fintype.ofFinite _
  have hQd : ∀ s : ↥H, s ∈ Q → ((d s : W) : W ⧸ Z) = 1 := fun s hs =>
    (QuotientGroup.eq_one_iff _).mpr (hvan s (hPΓ (Subgroup.mem_subgroupOf.mp hs)))
  have hsq : ∀ x : W ⧸ Z, x * x = 1 := by
    intro x
    induction x using QuotientGroup.induction_on with
    | H w => rw [← QuotientGroup.mk_mul, ← sq, hW, QuotientGroup.mk_one]
  obtain ⟨j, hj⟩ : Odd (Fintype.card (↥H ⧸ Q)) := by
    rw [← Nat.card_eq_fintype_card, ← Subgroup.index]
    exact Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hP.2.2)
  set u : W := ∏ c : ↥H ⧸ Q, d (Quotient.out c) with hu
  have key : ∀ g : ↥H, ((d g : W) : W ⧸ Z) = (((g : MulAut W) u * u⁻¹ : W) : W ⧸ Z) := by
    intro g
    have hshift : ∀ c : ↥H ⧸ Q,
        ((d (g * Quotient.out c) : W) : W ⧸ Z) = d (Quotient.out (g • c)) := by
      intro c
      have hs : (Quotient.out (g • c))⁻¹ * (g * Quotient.out c) ∈ Q := by
        rw [← QuotientGroup.eq, QuotientGroup.out_eq', ← smul_eq_mul,
          MulAction.Quotient.coe_smul_out]
      have e : g * Quotient.out c = Quotient.out (g • c) *
          ((Quotient.out (g • c))⁻¹ * (g * Quotient.out c)) := by group
      rw [e, hcoc, hQd _ hs, map_one, one_mul]
    have hc : ∀ c : ↥H ⧸ Q, qAct hHZ g (d (Quotient.out c) : W ⧸ Z) =
        (d (Quotient.out (g • c)) : W ⧸ Z) * (d g : W ⧸ Z)⁻¹ := by
      intro c
      rw [← hshift c, hcoc, mul_inv_cancel_right]
    have hg : qAct hHZ g (u : W ⧸ Z) =
        (u : W ⧸ Z) * ((d g : W ⧸ Z)⁻¹) ^ Fintype.card (↥H ⧸ Q) := by
      rw [hu, QuotientGroup.mk_prod, map_prod, Finset.prod_congr rfl (fun c _ => hc c),
        Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ]
      congr 1
      exact Fintype.prod_equiv (MulAction.toPerm g : Equiv.Perm (↥H ⧸ Q)) _ _ fun c => rfl
    have hx : ((d g : W ⧸ Z)⁻¹) ^ Fintype.card (↥H ⧸ Q) = (d g : W ⧸ Z) := by
      rw [hj, pow_succ, pow_mul, sq, hsq, one_pow, one_mul, inv_eq_of_mul_eq_one_left (hsq _)]
    rw [hx, qAct_mk] at hg
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_inv, hg, mul_comm (u : W ⧸ Z),
      mul_inv_cancel_right]
  refine ⟨u, hfix u fun r hr => ?_, fun g => mk_eq_mk_iff.mp (key g)⟩
  have h1 := key ⟨r, (perfectCore_le _ r.2).1⟩
  rw [(QuotientGroup.eq_one_iff _).mpr (hR _ r hr rfl)] at h1
  exact (QuotientGroup.eq_one_iff _).mp h1.symm

end KA

theorem factRadicalCocycleSp4_holds : Ch11.SecA.FactRadicalCocycleSp4 := by
  intro K _ _ hK W _ _ hW H Z π hπ P hP U hU
  have hK' : Nat.card K = 2 ^ 2 := hK
  have hU' : Ch11.SecA.IsFlagW H P Z (2 ^ 2) 1 U := hU
  obtain ⟨f, hf⟩ := exists_isCoord (linModelNat _) hπ
  refine KA.radicalCocycle_of hW (fun h hh z hz => ?_)
    (factRadicalFixedSp4_holds K 2 le_rfl hK' W hW H Z π hπ P hP U hU')
    (factPointSp4_holds K 2 le_rfl hK' W hW H Z π hπ P hP U hU') hP
    (factSylowLeviSp4_holds K 2 le_rfl hK' W hW H Z π hπ P hP U hU')
  obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSp 2 K), π γ = ⟨h, hh⟩ := hf.onto ⟨h, hh⟩
  have hhγ : h = ((π γ : ↥H) : MulAut W) := by rw [hγ]
  rw [← hf.ker] at hz ⊢
  rw [hhγ, hf.act4, hz, Matrix.mulVec_zero]

end CFSG.Quasithin.Vol2.KGNat
