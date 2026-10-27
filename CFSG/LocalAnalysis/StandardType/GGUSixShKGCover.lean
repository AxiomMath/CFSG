module

public import CFSG.LocalAnalysis.StandardType.GGUSixShKGCases
import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGCases
import CFSG.LocalAnalysis.StandardType.GGUSixThreeKGDescent

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section USixSh

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag CFSG.SectionRank.OddCover CFSG.RankThree.PartOne.KCUnitaryModel
  CFSG.StandardType.TableBUE CFSG.StandardType.TableBUD
open CFSG.LocalAnalysis.GLTheoremA.FQ (fixF)
open CFSG.LocalAnalysis.GLTheoremA.T156.Uni (Induced subfieldHom subfieldEquiv)

theorem ggUSixSh_perLineSh_of_cover {K : Type} [Field K] [Finite K] {n : ℕ}
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1)
    (hperfSU : commutator (unitarySU 2 n K 6) = ⊤)
    {L' : Type} [Group L'] [Finite L'] {ψ : L' →* LargeEvenProj (unitarySU 2 n K 6)}
    (hcov' : ∀ ψ'' : L' →* LargeEvenProj (unitarySU 2 n K 6), Function.Surjective ψ'' →
      ψ''.ker = ψ.ker →
      ∃ φ : ↥(unitarySU 2 n K 6) →* L', ∀ s, ψ'' (φ s) = LargeEvenProjMk (unitarySU 2 n K 6) s)
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A)
    (hAI : ∀ a ∈ A, ∃ x ∈ LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
      (LargeEvenGUSet (Fin 6) K (2 ^ n)), ∀ l : L', x (ψ l) = ψ (a l))
    (hcard : 3 ^ 3 ≤ Nat.card A) :
    GGUSixShPerLineOn ψ (ggUSixShSet (TableBU.unitaryFieldData_of_card hK hn)) A := by
  classical
  have h : UnitaryFieldData 2 n K := TableBU.unitaryFieldData_of_card hK hn
  have hdq : ((6 : ℕ), 2 ^ n) ≠ (3, 2) := fun he => by
    have := congrArg Prod.fst he
    simp only at this
    omega
  have hp3 : Nat.Prime 3 := Nat.prime_three
  haveI : Fact (Nat.Prime 3) := ⟨hp3⟩
  have hAb : CFSG.Open.IsElemAbelian 3 (TypeA.inducedSub ψ A) :=
    TypeA.isElemAbelian_inducedSub hψ hA
  have hAbI : ∀ x ∈ TypeA.inducedSub ψ A, x ∈ LargeEvenMatConjImage
      (LargeEvenProjMk (unitarySU 2 n K 6)) (LargeEvenGUSet (Fin 6) K (2 ^ n)) := by
    intro x hx
    obtain ⟨a, ha, hxa⟩ := TypeA.mem_inducedSub.mp hx
    obtain ⟨y, hy, hya⟩ := hAI a ha
    rw [TypeA.induced_unique ψ hψ hxa hya]
    exact hy
  have hcardAb : Nat.card (TypeA.inducedSub ψ A) = Nat.card A :=
    TypeA.card_inducedSub hψ hker hperf (fun a ha => by
      obtain ⟨y, -, hy⟩ := hAI a ha
      exact ⟨y, hy⟩)
  by_cases hfr : ∃ P ∈ primeFormUnitary h (idGram K 6), ∀ a ∈ TypeA.inducedSub ψ A,
      ∃ (M : GL (Fin 6) K) (hM : M ∈ LargeEvenGUSet (Fin 6) K (2 ^ n)),
        ((P⁻¹ * M * P : GL (Fin 6) K) : Matrix (Fin 6) (Fin 6) K).IsDiag ∧
          a = TableB.projConj (unitarySU 2 n K 6) ⟨M, gu_subset_normalizer h hM⟩
  · obtain ⟨P, hP, hfra⟩ := hfr
    refine ggUSixSh_perLineSh_of_frame (Sh := ggUSixShSet h) h hperfSU hcov' hψ hker hperf hA hP
      (fun a ha => ?_)
    obtain ⟨x, -, hx⟩ := hAI a ha
    have hxAb : x ∈ TypeA.inducedSub ψ A := TypeA.mem_inducedSub.mpr ⟨a, ha, hx⟩
    obtain ⟨M, hM, hdiag, hxeq⟩ := hfra x hxAb
    exact ⟨M, hM, hdiag, fun l => by rw [← hxeq]; exact hx l⟩
  · have h81 : Nat.card A < 3 ^ 4 := by
      by_contra hge
      push Not at hge
      exact hfr (TableBUD.exists_unitary_frame h hK (by norm_num) hdq hp3 hpq hAb hAbI
        (by rw [hcardAb]; simpa using hge))
    haveI : Finite (MulAut L') := Finite.of_injective (fun φ : MulAut L' => (φ : L' → L'))
      DFunLike.coe_injective
    have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hA.2 g.1 g.2)⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hA3
    have hk3 : k = 3 := by
      rw [hk] at hcard h81
      rcases Nat.lt_or_ge k 3 with hlt | hge
      · have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) (show k ≤ 2 by omega)
        omega
      · rcases Nat.lt_or_ge k 4 with hlt4 | hge4
        · omega
        · have := Nat.pow_le_pow_right (show 0 < 3 by norm_num) hge4
          omega
    have hcard27 : Nat.card A = 27 := by rw [hk, hk3]; norm_num
    have hcardAb' : 3 ^ 3 ≤ Nat.card (TypeA.inducedSub ψ A) := by rw [hcardAb]; exact hcard
    rcases TableBU63.fieldType_or_heis h hK hpq hAb hAbI hcardAb' hfr with
      ⟨M, hMN, l, hMu, hM3, hl, hMA⟩ | ⟨x, y, z, hxN, hyN, hzN, ζ, hxu, hyu, hzu, hxA, hyA, hzA,
        hx3, hz3, hζ3, hζ1, hxy, hxz, hyz, hzs⟩
    · exact ggUSixSh_perLineSh_of_fieldType h hK hpq hperfSU hcov' hψ hker hperf hA hAI hcard27 hMN hMu
        hM3 hl hMA
    · have hζ : IsPrimitiveRoot ζ 3 := by
        have := IsPrimitiveRoot.orderOf ζ
        rwa [orderOf_eq_prime hζ3 hζ1] at this
      obtain ⟨s, hs⟩ : ∃ s : Kˣ, y ^ 3 = GeneralLinearGroup.scalar (Fin 6) s := by
        have h3 : (TableB.projConj (unitarySU 2 n K 6) ⟨y, hyN⟩) ^ 3 = 1 := hAb.2 _ hyA
        rw [← map_pow] at h3
        obtain ⟨k', hk'⟩ :=
          TableBUE.mem_scalars_of_projConj_eq_one h hK (by norm_num) hdq hp3 hpq h3
        exact ⟨k', hk'.symm⟩
      by_cases hcube : ∃ t : Kˣ, t ^ 3 = s
      · obtain ⟨t, ht⟩ := hcube
        have hc : ∀ g : GL (Fin 6) K, GeneralLinearGroup.scalar (Fin 6) t⁻¹ * g =
            g * GeneralLinearGroup.scalar (Fin 6) t⁻¹ := fun g => (commute_scalar t⁻¹ g).symm.eq
        have hy'3 : (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) ^ 3 = 1 := by
          rw [TableBU63.scalar_mul_pow, hs, ← map_mul, ← ht, inv_pow, inv_mul_cancel, map_one]
        have hsU : GeneralLinearGroup.scalar (Fin 6) (t ^ 3) ∈
            primeFormUnitary h (idGram K 6) := by
          rw [ht, ← hs]
          exact pow_mem hyu 3
        have htU := UnitSixThreeKG.scalar_mem_primeFormUnitary_of_cube h hpq hsU
        have hy'u : GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y ∈
            primeFormUnitary h (idGram K 6) := by
          rw [map_inv]
          exact Subgroup.mul_mem _ (Subgroup.inv_mem _ htU) hyu
        have hsN : GeneralLinearGroup.scalar (Fin 6) t⁻¹ ∈
            Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
          TableB.scalar_mem_normalizer _ ⟨t⁻¹, rfl⟩
        have hy'N : GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y ∈
            Subgroup.normalizer (unitarySU 2 n K 6 : Set (GL (Fin 6) K)) :=
          Subgroup.mul_mem _ hsN hyN
        have hy'A : TableB.projConj (unitarySU 2 n K 6)
            ⟨GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y, hy'N⟩ ∈ TypeA.inducedSub ψ A := by
          have e : (⟨GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y, hy'N⟩ : Subgroup.normalizer
              (unitarySU 2 n K 6 : Set (GL (Fin 6) K))) = ⟨_, hsN⟩ * ⟨y, hyN⟩ := rfl
          rw [e, map_mul, TableB.projConj_of_scalar _ ⟨t⁻¹, rfl⟩, one_mul]
          exact hyA
        have hxy' : x * (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) =
            GeneralLinearGroup.scalar (Fin 6) ζ *
              ((GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) * x) := by
          calc x * (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y)
              = (x * GeneralLinearGroup.scalar (Fin 6) t⁻¹) * y := (mul_assoc _ _ _).symm
            _ = (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * x) * y := by rw [← hc x]
            _ = GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (x * y) := mul_assoc _ _ _
            _ = GeneralLinearGroup.scalar (Fin 6) t⁻¹ *
                (GeneralLinearGroup.scalar (Fin 6) ζ * (y * x)) := by rw [hxy]
            _ = GeneralLinearGroup.scalar (Fin 6) ζ *
                (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (y * x)) := by
                rw [← mul_assoc, hc (GeneralLinearGroup.scalar (Fin 6) ζ), mul_assoc]
            _ = GeneralLinearGroup.scalar (Fin 6) ζ *
                ((GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) * x) := by rw [mul_assoc]
        have hy'z : (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) * z =
            z * (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) := by
          calc (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) * z
              = GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (y * z) := mul_assoc _ _ _
            _ = GeneralLinearGroup.scalar (Fin 6) t⁻¹ * (z * y) := by rw [hyz]
            _ = (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * z) * y := (mul_assoc _ _ _).symm
            _ = (z * GeneralLinearGroup.scalar (Fin 6) t⁻¹) * y := by rw [hc z]
            _ = z * (GeneralLinearGroup.scalar (Fin 6) t⁻¹ * y) := mul_assoc _ _ _
        exact ggUSixSh_perLineSh_of_heisTriple h hpq hψ hker hperf hA hAI hcard27 hxN hy'N hzN hxu hy'u hzu
          hx3 hy'3 hz3 hζ hxy' hxz hy'z hzs hxA hy'A hzA
      · exact ggUSixSh_perLineSh_of_fieldType h hK hpq hperfSU hcov' hψ hker hperf hA hAI hcard27 hyN hyu hs
          (fun t ht => hcube ⟨t, ht⟩) hyA

private noncomputable def ggUSixShCovAux_twoPart {L' : Type} [Group L'] [Finite L'] (N : Subgroup L')
    (hN : N ≤ Subgroup.center L') : Subgroup L' where
  carrier := {z | z ∈ N ∧ z ^ (2 ^ Nat.card L') = 1}
  one_mem' := ⟨N.one_mem, one_pow _⟩
  mul_mem' := fun {x y} hx hy => ⟨N.mul_mem hx.1 hy.1, by
    rw [Commute.mul_pow (Subgroup.mem_center_iff.mp (hN hy.1) x), hx.2, hy.2, one_mul]⟩
  inv_mem' := fun {x} hx => ⟨N.inv_mem hx.1, by rw [inv_pow, hx.2, inv_one]⟩

theorem ggUSixSh_perLineSh_descent {L' R : Type} [Group L'] [Finite L'] [Group R] {ψ : L' →* R}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L') (hperf : commutator L' = ⊤)
    {A : Subgroup (MulAut L')} (hA : CFSG.Open.IsElemAbelian 3 A) {I Sh : Set (MulAut R)}
    (hAI : ∀ a ∈ A, ∃ x ∈ I, ∀ l : L', x (ψ l) = ψ (a l))
    (H : ∀ (L₁ : Type) [Group L₁] [Finite L₁] (ψ₁ : L₁ →* R), Function.Surjective ψ₁ →
      ψ₁.ker ≤ Subgroup.center L₁ → commutator L₁ = ⊤ → Odd (Nat.card ψ₁.ker) →
      ∀ A₁ : Subgroup (MulAut L₁), CFSG.Open.IsElemAbelian 3 A₁ →
        (∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L₁, x (ψ₁ l) = ψ₁ (a l)) → Nat.card A₁ = Nat.card A →
        GGUSixShPerLineOn ψ₁ Sh A₁) :
    GGUSixShPerLineOn ψ Sh A := by
  classical
  set Z := ggUSixShCovAux_twoPart ψ.ker hker with hZdef
  have hZc : Z ≤ Subgroup.center L' := fun z hz => hker hz.1
  have hcen : ∀ y ∈ Z, ∀ g : L', g * y = y * g := fun y hy g =>
    Subgroup.mem_center_iff.mp (hZc hy) g
  haveI hZn : Z.Normal := ⟨fun y hy g => by rw [hcen y hy g, mul_inv_cancel_right]; exact hy⟩
  have hZ2 : IsPGroup 2 Z := fun g => ⟨Nat.card L', Subtype.ext (by simpa using g.2.2)⟩
  have hAp : ∀ a ∈ A, a ^ 3 = 1 := hA.2
  have hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hA.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hA3 : IsPGroup 3 A := fun g => ⟨1, Subtype.ext (by simpa using hAp g.1 g.2)⟩
  have hkerA : ∀ a ∈ A, ∀ z ∈ ψ.ker, a z ∈ ψ.ker := by
    intro a ha z hz
    obtain ⟨x, -, hx⟩ := hAI a ha
    rw [MonoidHom.mem_ker, ← hx, (MonoidHom.mem_ker).mp hz, map_one]
  have hZA : ∀ a ∈ A, ∀ z ∈ Z, a z ∈ Z := fun a ha z hz =>
    ⟨hkerA a ha z hz.1, by rw [← map_pow, hz.2, map_one]⟩
  have hmap : ∀ a ∈ A, Z.map a.toMonoidHom = Z := by
    intro a ha
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩; exact hZA a ha z hz
    · intro z hz
      refine ⟨a⁻¹ z, hZA _ (A.inv_mem ha) z hz, ?_⟩
      simp
  have hπs : Function.Surjective (QuotientGroup.mk' Z) := QuotientGroup.mk'_surjective Z
  let ρf : A → MulAut (L' ⧸ Z) := fun a => QuotientGroup.congr Z Z a.1 (hmap a.1 a.2)
  have hρf : ∀ (a : A) (l : L'), ρf a (l : L' ⧸ Z) = ((a.1 l : L') : L' ⧸ Z) := fun a l =>
    QuotientGroup.congr_mk _ _ _ _ l
  let ρ : A →* MulAut (L' ⧸ Z) :=
    { toFun := ρf
      map_one' := by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        rw [hρf]; rfl
      map_mul' := fun a b => by
        ext x
        obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
        simp only [MulAut.mul_apply, hρf]
        rfl }
  have hρ : ∀ (a : A) (l : L'), ρ a (l : L' ⧸ Z) = ((a.1 l : L') : L' ⧸ Z) := hρf
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hfixl : ∀ l : L', l⁻¹ * a.1 l ∈ Z := by
      intro l
      have := hρ a l
      rw [ha, MulAut.one_apply] at this
      exact QuotientGroup.eq.mp this
    letI : CommGroup Z :=
      { (inferInstance : Group Z) with mul_comm := fun x y => Subtype.ext (hcen y y.2 x) }
    let f : L' →* Z :=
      { toFun := fun l => ⟨l⁻¹ * a.1 l, hfixl l⟩
        map_one' := Subtype.ext (by simp)
        map_mul' := fun l m => Subtype.ext (by
          show (l * m)⁻¹ * a.1 (l * m) = l⁻¹ * a.1 l * (m⁻¹ * a.1 m)
          have hc := hcen _ (hfixl l) m⁻¹
          calc (l * m)⁻¹ * a.1 (l * m) = m⁻¹ * (l⁻¹ * a.1 l) * a.1 m := by rw [map_mul]; group
            _ = (l⁻¹ * a.1 l) * m⁻¹ * a.1 m := by rw [hc]
            _ = l⁻¹ * a.1 l * (m⁻¹ * a.1 m) := by group) }
    have hf : ∀ l, f l = 1 := fun l =>
      Abelianization.commutator_subset_ker f (by rw [hperf]; exact Subgroup.mem_top l)
    apply Subtype.ext
    ext l
    have h1 : l⁻¹ * a.1 l = 1 := congrArg Subtype.val (hf l)
    exact (inv_mul_eq_one.mp h1).symm
  set A₁ := ρ.range with hA₁def
  have hA₁ : CFSG.Open.IsElemAbelian 3 A₁ := by
    refine ⟨⟨⟨?_⟩⟩, ?_⟩
    · rintro ⟨_, a, rfl⟩ ⟨_, b, rfl⟩
      apply Subtype.ext
      show ρ a * ρ b = ρ b * ρ a
      have : a * b = b * a := Subtype.ext (hAc a.1 a.2 b.1 b.2)
      rw [← map_mul, this, map_mul]
    · rintro _ ⟨a, rfl⟩
      have : a ^ 3 = 1 := Subtype.ext (by simpa using hAp a.1 a.2)
      rw [← map_pow, this, map_one]
  have hcardA : Nat.card A₁ = Nat.card A :=
    (Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv).symm
  have hZψ : Z ≤ ψ.ker := fun z hz => hz.1
  let ψ₁ : L' ⧸ Z →* R := QuotientGroup.lift Z ψ hZψ
  have hψ₁ : ∀ l : L', ψ₁ (l : L' ⧸ Z) = ψ l := fun l => QuotientGroup.lift_mk _ _ _
  have hψ₁s : Function.Surjective ψ₁ := fun r => by
    obtain ⟨l, rfl⟩ := hψ r; exact ⟨l, hψ₁ l⟩
  have hψ₁ker : ψ₁.ker ≤ Subgroup.center (L' ⧸ Z) := by
    intro x hx
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have hl : l ∈ ψ.ker := by rw [MonoidHom.mem_ker, ← hψ₁]; exact hx
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective g
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp (hker hl) g]
  have hperf₁ : commutator (L' ⧸ Z) = ⊤ := by
    have : (commutator L').map (QuotientGroup.mk' Z) = commutator (L' ⧸ Z) := by
      rw [commutator_def, commutator_def, Subgroup.map_commutator,
        Subgroup.map_top_of_surjective _ hπs]
    rw [← this, hperf, Subgroup.map_top_of_surjective _ hπs]
  have hodd : Odd (Nat.card ψ₁.ker) := by
    by_contra hne
    rw [Nat.not_odd_iff_even] at hne
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' 2 (even_iff_two_dvd.mp hne)
    obtain ⟨l, hl⟩ := QuotientGroup.mk_surjective x.1
    have hx2 : x.1 ^ 2 = 1 := by
      have := congrArg Subtype.val (pow_orderOf_eq_one x)
      rw [hx] at this; simpa using this
    have hl2 : l ^ 2 ∈ Z := by
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hl, hx2]
    have hlker : l ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, ← hψ₁, hl]; exact x.2
    have hlZ : l ∈ Z := ⟨hlker, Line63.pow_two_pow_card l (j := Nat.card L' + 1)
      (by rw [pow_succ, pow_mul', hl2.2])⟩
    have : x = 1 := Subtype.ext (by rw [← hl]; exact (QuotientGroup.eq_one_iff l).mpr hlZ)
    rw [this, orderOf_one] at hx
    norm_num at hx
  have hAI₁ : ∀ a ∈ A₁, ∃ x ∈ I, ∀ l : L' ⧸ Z, x (ψ₁ l) = ψ₁ (a l) := by
    rintro _ ⟨a, rfl⟩
    obtain ⟨x, hx, hxa⟩ := hAI a.1 a.2
    refine ⟨x, hx, fun l => ?_⟩
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective l
    rw [hψ₁, hρ, hψ₁]; exact hxa l
  have hPerLine₁ : GGUSixShPerLineOn ψ₁ Sh A₁ :=
    H (L' ⧸ Z) ψ₁ hψ₁s hψ₁ker hperf₁ hodd A₁ hA₁ hAI₁ hcardA
  intro a₀ ha₀ ha₀ne
  let a₀' : A := ⟨a₀, ha₀⟩
  set a₁ : MulAut (L' ⧸ Z) := ρ a₀' with ha₁def
  have ha₁ : a₁ ∈ A₁ := ⟨a₀', ha₁def.symm⟩
  have ha₁ne : a₁ ≠ 1 := by
    intro h1
    have h2 : a₀' = 1 := hρinj (by rw [← ha₁def, h1, map_one])
    exact ha₀ne (Subtype.ext_iff.mp h2)
  have hc₁ : ∀ l : L', a₁ (l : L' ⧸ Z) = (a₀ l : L' ⧸ Z) := by
    intro l
    rw [ha₁def]
    exact hρ a₀' l
  rcases hPerLine₁ a₁ ha₁ ha₁ne with ⟨φ, hφ, hφa⟩ | ⟨n₁, hn₁, hmv₁⟩
  · refine Or.inl ⟨φ, hφ, fun l => ?_⟩
    have hh := hφa (l : L' ⧸ Z)
    rwa [hψ₁ l, hc₁ l, hψ₁ (a₀ l)] at hh
  · obtain ⟨n₀, rfl⟩ := QuotientGroup.mk_surjective n₁
    have hu : ∀ a : A, ((n₀ * (a.1 n₀)⁻¹ : L') : L' ⧸ Z) =
        (n₀ : L' ⧸ Z) * (ρ a (n₀ : L' ⧸ Z))⁻¹ :=
      fun a => by rw [hρ, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
    have h3 : ∀ a ∈ A, (n₀ * (a n₀)⁻¹) ^ 3 ∈ Z := by
      intro a ha
      rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, hu ⟨a, ha⟩]
      exact (hn₁ (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).1
    have hfix : ∀ a ∈ A, ∀ a' ∈ A, (n₀ * (a n₀)⁻¹)⁻¹ * a' (n₀ * (a n₀)⁻¹) ∈ Z := by
      intro a ha a' ha'
      apply QuotientGroup.eq.mp
      rw [show ((a' (n₀ * (a n₀)⁻¹) : L') : L' ⧸ Z) =
          ρ ⟨a', ha'⟩ ((n₀ * (a n₀)⁻¹ : L') : L' ⧸ Z) from (hρ ⟨a', ha'⟩ _).symm, hu ⟨a, ha⟩]
      exact ((hn₁ (ρ ⟨a, ha⟩) ⟨⟨a, ha⟩, rfl⟩).2 _ ⟨⟨a', ha'⟩, rfl⟩).symm
    obtain ⟨z, hz, hzW⟩ := Line63.exists_lift_fixed hZc hZ2 hA3 hAc hZA n₀ h3 hfix
    refine Or.inr ⟨n₀ * z, hzW, ?_⟩
    intro hmem
    have hz1 : ((z : L') : L' ⧸ Z) = 1 := (QuotientGroup.eq_one_iff z).mpr hz
    have hmk : (((n₀ * z : L') : L' ⧸ Z)) = (n₀ : L' ⧸ Z) := by
      rw [QuotientGroup.mk_mul, hz1, mul_one]
    set g := MulAut.conj (n₀ * z) * a₀ * (MulAut.conj (n₀ * z))⁻¹ with hgdef
    have hgA : g ∈ A := (Subgroup.zpowers_le.mpr ha₀) hmem
    have hkey : ρ ⟨g, hgA⟩ =
        MulAut.conj (n₀ : L' ⧸ Z) * a₁ * (MulAut.conj (n₀ : L' ⧸ Z))⁻¹ := by
      ext x
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
      rw [hρ]
      change ((g l : L') : L' ⧸ Z) =
        (MulAut.conj (n₀ : L' ⧸ Z) * a₁ * (MulAut.conj (n₀ : L' ⧸ Z))⁻¹) (l : L' ⧸ Z)
      rw [hgdef]
      simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.conj_inv_apply,
        QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk]
      rw [← hρ a₀' ((n₀ * z)⁻¹ * l * (n₀ * z)), ← ha₁def]
      rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv, hmk]
    have hmem₁ : MulAut.conj (n₀ : L' ⧸ Z) * a₁ * (MulAut.conj (n₀ : L' ⧸ Z))⁻¹ ∈
        Subgroup.zpowers a₁ := by
      rw [← hkey]
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
      have hgzp : (⟨g, hgA⟩ : A) ∈ Subgroup.zpowers a₀' := by
        rw [Subgroup.mem_zpowers_iff]
        refine ⟨k, ?_⟩
        apply Subtype.ext
        simpa using hk
      have := Subgroup.mem_map_of_mem ρ hgzp
      rwa [MonoidHom.map_zpowers, ← ha₁def] at this
    exact hmv₁ hmem₁

theorem ggUSixSh_torusNoLineSh_unitSix
    {K : Type} [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) (hpq : 3 ∣ 2 ^ n + 1) (r : ℕ) :
    GGTorusNoLineSh 3 r (LargeEvenProj (unitarySU 2 n K 6))
      (LargeEvenMatConjImage (LargeEvenProjMk (unitarySU 2 n K 6))
        (LargeEvenGUSet (Fin 6) K (2 ^ n)))
      (ggUSixShSet (TableBU.unitaryFieldData_of_card hK hn)) := by
  refine ggUSixSh_torusNoLineSh_of_perLineSh fun L' _ _ ψ hψ hker hperf A hA hAI h3 => ?_
  by_cases hn1 : n = 1
  · subst hn1
    have hcov := LineU.unitaryCoverOddAt_six_two K (by simpa using hK)
    refine ggUSixSh_perLineSh_descent hψ hker hperf hA hAI
      (fun L₁ _ _ ψ₁ hs hk hp hodd A₁ hA₁ hAI₁ hc => ?_)
    exact ggUSixSh_perLineSh_of_cover hK le_rfl hpq hcov.1
      (fun ψ'' hs'' hk'' => hcov.2 L₁ ψ'' hs'' (hk'' ▸ hk) hp (hk'' ▸ hodd)) hs hk hp hA₁ hAI₁
      (by rw [hc]; exact h3)
  · have hcov := LineU.unitaryUniversalCover_holds n 6 K hK (by norm_num)
      (fun h => hn1 (Prod.mk.inj h).2)
    exact ggUSixSh_perLineSh_of_cover hK hn hpq hcov.1
      (fun ψ'' hs'' hk'' => hcov.2 L' ψ'' hs'' (hk'' ▸ hker) hperf) hψ hker hperf hA hAI h3

end USixSh

end CFSG.StandardType
