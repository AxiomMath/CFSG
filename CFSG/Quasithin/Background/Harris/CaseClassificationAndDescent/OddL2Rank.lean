module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DihedralSylow
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.Walter.Cited.PSL2Small

public section

namespace CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent

open CFSG.GorensteinWalter CFSG.Assembly.LowTwoRank

theorem card_elemTwo_pgl2_le_four {K : Type} [Field K] [Finite K]
    (hodd : IsOddPrimePower (Nat.card K)) (E : Subgroup (PGL2 K))
    (h2 : ∀ x ∈ E, x * x = 1) : Nat.card E ≤ 4 := by
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have hP : IsPGroup 2 E := fun x => ⟨1, by
    apply Subtype.ext
    simpa [pow_two] using h2 x.1 x.2⟩
  obtain ⟨S, hS⟩ := hP.exists_le_sylow
  obtain ⟨m, -, ⟨ψ⟩⟩ := pgl2_odd_hasDihedralSylowTwo_model K hodd S
  let E' : Subgroup (DihedralGroup (2 ^ m)) :=
    (E.subgroupOf (S : Subgroup (PGL2 K))).map ψ.toMonoidHom
  have hE' : ∀ a ∈ E', a * a = 1 := by
    rintro a ⟨b, hb, rfl⟩
    have := h2 b.1 hb
    change ψ b * ψ b = 1
    rw [← map_mul]
    have hb2 : b * b = 1 := Subtype.ext this
    rw [hb2, map_one]
  have h4 := CFSG.QuasithinUnique.Setup.Family.dihedral_elemAbelian_card_le_four E' hE'
  calc Nat.card E = Nat.card (E.subgroupOf (S : Subgroup (PGL2 K))) :=
        (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS).toEquiv).symm
    _ = Nat.card E' :=
        (Nat.card_congr (Subgroup.equivMapOfInjective _ ψ.toMonoidHom ψ.injective).toEquiv)
    _ ≤ 4 := h4

theorem card_elemTwo_mulAut_psl2_le {K : Type} [Field K] [Finite K] {p f : ℕ} [Fact p.Prime]
    (hKcard : Nat.card K = p ^ f) (hodd : IsOddPrimePower (Nat.card K))
    (hcard : 3 < Nat.card K)
    (B : Subgroup (MulAut (PSL2 K))) (h2 : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 4 * Nat.card (K ≃+* K) := by
  have : Finite (K ≃+* K) := Finite.of_injective (fun σ : K ≃+* K => (σ : K → K))
    DFunLike.coe_injective
  let φ := pGammaL2ToMulAutPSL2 K hodd hcard
  have hsurj : Function.Surjective φ := pGammaL2ToMulAutPSL2_surjective K hKcard hodd hcard
  have hinj : Function.Injective φ := pGammaL2ToMulAutPSL2_injective K hodd hcard
  have : Finite (PGL2 K) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  have : Finite (PGammaL2 K) :=
    Finite.of_injective (fun x : PGammaL2 K => (x.left, x.right)) (fun x y h =>
      SemidirectProduct.ext (congrArg Prod.fst h) (congrArg Prod.snd h))
  let B' : Subgroup (PGammaL2 K) := B.comap φ
  have h1 : Nat.card B ≤ Nat.card B' :=
    Nat.card_le_card_of_surjective (fun x : B' => (⟨φ x.1, x.2⟩ : B)) (fun y => by
      obtain ⟨x, hx⟩ := hsurj y.1
      exact ⟨⟨x, by simp [B', hx]⟩, Subtype.ext hx⟩)
  let g : B' →* (K ≃+* K) := SemidirectProduct.rightHom.comp B'.subtype
  have h3 : Nat.card g.ker * Nat.card g.range = Nat.card B' := Subgroup.card_ker_mul_card_range g
  have h4 : Nat.card g.range ≤ Nat.card (K ≃+* K) := Nat.card_le_card_of_injective _
    Subtype.val_injective
  let E : Subgroup (PGL2 K) := B'.comap (SemidirectProduct.inl : PGL2 K →* PGammaL2 K)
  have hE2 : ∀ x ∈ E, x * x = 1 := by
    intro x hx
    have hx' : (SemidirectProduct.inl x : PGammaL2 K) ∈ B' := hx
    have := h2 _ hx'
    have hi : (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) (x * x) =
        (SemidirectProduct.inl : PGL2 K →* PGammaL2 K) 1 := by
      refine hinj ?_
      rw [map_mul, map_mul]
      exact this.trans (map_one φ).symm
    exact SemidirectProduct.inl_injective hi
  have h5 : Nat.card E ≤ 4 := card_elemTwo_pgl2_le_four hodd E hE2
  have h6 : Nat.card g.ker ≤ Nat.card E := by
    refine Nat.card_le_card_of_injective
      (fun x : g.ker => (⟨x.1.1.left, ?_⟩ : E)) ?_
    · have hr : x.1.1.right = 1 := x.2
      have : (SemidirectProduct.inl x.1.1.left : PGammaL2 K) = x.1.1 :=
        SemidirectProduct.ext rfl hr.symm
      change (SemidirectProduct.inl x.1.1.left : PGammaL2 K) ∈ B'
      rw [this]; exact x.1.2
    · intro x y hxy
      have hl : x.1.1.left = y.1.1.left := congrArg (fun z : E => z.1) hxy
      have hrx : x.1.1.right = 1 := x.2
      have hry : y.1.1.right = 1 := y.2
      exact Subtype.ext (Subtype.ext (SemidirectProduct.ext hl (hrx.trans hry.symm)))
  calc Nat.card B ≤ Nat.card B' := h1
    _ = Nat.card g.ker * Nat.card g.range := h3.symm
    _ ≤ 4 * Nat.card (K ≃+* K) := Nat.mul_le_mul (h6.trans h5) h4

theorem card_ringEquiv_le_two {K : Type} [Field K] [Finite K] {p : ℕ} [Fact p.Prime]
    (hK : Nat.card K = p ^ 2) : Nat.card (K ≃+* K) ≤ 2 := by
  have : Fintype K := Fintype.ofFinite K
  have hKF : Fintype.card K = p ^ 2 := by rw [← Nat.card_eq_fintype_card, hK]
  have : CharP K p := charP_of_card_eq_prime_pow hKF
  let _ : Algebra (ZMod p) K := ZMod.algebra K p
  have hfin : Module.finrank (ZMod p) K = 2 := by
    have h := Module.card_eq_pow_finrank (K := ZMod p) (V := K)
    rw [hKF, ZMod.card] at h
    exact (Nat.pow_right_injective (Fact.out : p.Prime).two_le h).symm
  have hc : ∀ σ : K ≃+* K, ∀ x : ZMod p, σ (algebraMap (ZMod p) K x) = algebraMap (ZMod p) K x :=
    fun σ x => DFunLike.congr_fun
      (RingHom.ext_zmod (σ.toRingHom.comp (algebraMap (ZMod p) K)) (algebraMap (ZMod p) K)) x
  have hle : Nat.card (K →ₐ[ZMod p] K) ≤ 2 := by
    rw [← hfin]
    exact card_algHom_le_finrank (ZMod p) K K
  refine le_trans (Nat.card_le_card_of_injective
    (fun σ : K ≃+* K => (AlgEquiv.ofRingEquiv (f := σ) (hc σ)).toAlgHom) fun σ τ h => ?_) hle
  ext x
  exact DFunLike.congr_fun h x

theorem card_elemAbelian_mulAut_psl2_prime {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hK : Nat.card K = p)
    (B : Subgroup (MulAut (PSL2 K))) (_hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (h2 : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 4 := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 1, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), le_rfl, by rw [hK, pow_one]⟩
  have : Subsingleton (K ≃+* K) := CFSG.Walter.Suzuki.subsingleton_ringEquiv_of_card_prime K hK
  have h1 : Nat.card (K ≃+* K) = 1 := Nat.card_unique
  have := card_elemTwo_mulAut_psl2_le (f := 1) (by rw [hK, pow_one]) hodd (by omega) B h2
  omega

theorem card_elemAbelian_mulAut_psl2_prime_sq {K : Type} [Field K] [Finite K] {p : ℕ}
    [Fact p.Prime] (hp5 : 5 ≤ p) (hK : Nat.card K = p ^ 2)
    (B : Subgroup (MulAut (PSL2 K))) (_hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (h2 : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ 8 := by
  have hodd : IsOddPrimePower (Nat.card K) :=
    ⟨p, 2, Fact.out, (Fact.out : p.Prime).odd_of_ne_two (by omega), by omega, hK⟩
  have h25 : 25 ≤ p ^ 2 := by nlinarith
  have := card_elemTwo_mulAut_psl2_le (f := 2) hK hodd (by omega) B h2
  have := card_ringEquiv_le_two hK
  omega

theorem card_le_of_mulAut_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (B : Subgroup (MulAut X)) (n : ℕ)
    (h : ∀ B' : Subgroup (MulAut Y), (∀ x ∈ B', ∀ y ∈ B', x * y = y * x) →
      (∀ x ∈ B', x * x = 1) → Nat.card B' ≤ n)
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) : Nat.card B ≤ n := by
  let B' : Subgroup (MulAut Y) := B.map (MulAut.congr e).toMonoidHom
  have hB' : ∀ x ∈ B', x * x = 1 := by
    rintro _ ⟨b, hb, rfl⟩
    change MulAut.congr e b * MulAut.congr e b = 1
    rw [← map_mul, h2 b hb, map_one]
  have hB'c : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    change MulAut.congr e a * MulAut.congr e b = MulAut.congr e b * MulAut.congr e a
    rw [← map_mul, ← map_mul, hc a ha b hb]
  calc Nat.card B = Nat.card B' :=
        Nat.card_congr (Subgroup.equivMapOfInjective _ (MulAut.congr e).toMonoidHom
          (MulAut.congr e).injective).toEquiv
    _ ≤ n := h B' hB'c hB'

theorem card_elemAbelian_mulAut_of_equiv_prime {X : Type} [Group X] {K : Type} [Field K]
    [Finite K] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hK : Nat.card K = p)
    (e : X ≃* StatedProj (StatedSL 2 K)) (B : Subgroup (MulAut X))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 2 := by
  refine card_le_of_mulAut_equiv (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
    B (2 ^ 2) (fun B' hc' hB' => ?_) hc h2
  exact card_elemAbelian_mulAut_psl2_prime hp5 hK B' hc' hB'

theorem card_elemAbelian_mulAut_of_equiv_prime_sq {X : Type} [Group X] {K : Type} [Field K]
    [Finite K] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p) (hK : Nat.card K = p ^ 2)
    (e : X ≃* StatedProj (StatedSL 2 K)) (B : Subgroup (MulAut X))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 3 := by
  refine card_le_of_mulAut_equiv (e.trans (projectiveSpecialLinearGroupEquivStatedProj 2 K).symm)
    B (2 ^ 3) (fun B' hc' hB' => ?_) hc h2
  exact card_elemAbelian_mulAut_psl2_prime_sq hp5 hK B' hc' hB'

theorem card_elemAbelian_mulAut_of_model_prime {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (h : StatedClassicalModel X .PSL 2 p 1) (B : Subgroup (MulAut X))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 2 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact card_elemAbelian_mulAut_of_equiv_prime hp5 (by rwa [pow_one] at hK) e B hc h2

theorem card_elemAbelian_mulAut_of_model_prime_sq {X : Type} [Group X] {p : ℕ} [Fact p.Prime]
    (hp5 : 5 ≤ p) (h : StatedClassicalModel X .PSL 2 p 2) (B : Subgroup (MulAut X))
    (hc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (h2 : ∀ x ∈ B, x * x = 1) :
    Nat.card B ≤ 2 ^ 3 := by
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := h
  exact card_elemAbelian_mulAut_of_equiv_prime_sq hp5 hK e B hc h2

end CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent
