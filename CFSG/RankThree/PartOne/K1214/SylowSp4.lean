module

public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.RankThree.PartOne.KF.SpQuad
import CFSG.LieType.Classical.SteinbergBLSymplectic

public section

namespace CFSG.RankThree.PartOne.K1214

theorem sp4_card_factor {n e m p : ℕ} (hn : n + 2 = p ^ e * m) :
    (n + 1) ^ (2 ^ 2) * ∏ j ∈ Finset.Icc 1 2, ((n + 1) ^ (2 * j) - 1) =
      p ^ (2 * e) * ((n + 1) ^ 4 * n ^ 2 * ((n + 1) ^ 2 + 1) * m ^ 2) := by
  have h1 : (n + 1) ^ 2 - 1 = n * (n + 2) := Nat.sub_eq_of_eq_add (by ring)
  have h2 : (n + 1) ^ 4 - 1 = n * (n + 2) * ((n + 1) ^ 2 + 1) := Nat.sub_eq_of_eq_add (by ring)
  have h3 : (n + 2) ^ 2 = p ^ (2 * e) * m ^ 2 := by
    rw [hn, mul_pow, ← pow_mul, mul_comm e 2]
  have hprod : ∏ j ∈ Finset.Icc 1 2, ((n + 1) ^ (2 * j) - 1) =
      ((n + 1) ^ 2 - 1) * ((n + 1) ^ 4 - 1) := by
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num)]
  rw [hprod, h1, h2]
  calc (n + 1) ^ (2 ^ 2) * (n * (n + 2) * (n * (n + 2) * ((n + 1) ^ 2 + 1)))
      = (n + 1) ^ 4 * n ^ 2 * ((n + 1) ^ 2 + 1) * (n + 2) ^ 2 := by ring
    _ = p ^ (2 * e) * ((n + 1) ^ 4 * n ^ 2 * ((n + 1) ^ 2 + 1) * m ^ 2) := by rw [h3]; ring

theorem sp4_index_coprime {p e m n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he1 : 1 ≤ e)
    (hm : ¬ p ∣ m) (hn : n + 2 = p ^ e * m) :
    ¬ p ∣ (n + 1) ^ 4 * n ^ 2 * ((n + 1) ^ 2 + 1) * m ^ 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hz : ((n : ZMod p) + 2) = 0 := by
    have : ((n + 2 : ℕ) : ZMod p) = 0 :=
      (ZMod.natCast_eq_zero_iff _ _).2 (by
        rw [hn]
        exact dvd_mul_of_dvd_left (dvd_pow_self p (by omega)) m)
    simpa using this
  have h2 : ¬ p ∣ 2 := fun h =>
    hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  intro h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      ·
        have h1 : p ∣ n + 1 := hp.dvd_of_dvd_pow h
        have h2' : ((n + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h1
        push_cast at h2'
        have : (1 : ZMod p) = 0 := by linear_combination hz - h2'
        exact one_ne_zero this
      ·
        have h1 : p ∣ n := hp.dvd_of_dvd_pow h
        have h3 : (n : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h1
        have h4 : ((2 : ℕ) : ZMod p) = 0 := by
          push_cast
          linear_combination hz - h3
        exact h2 ((ZMod.natCast_eq_zero_iff _ _).1 h4)
    ·
      have h3 : (((n + 1) ^ 2 + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
      push_cast at h3
      have h4 : ((2 : ℕ) : ZMod p) = 0 := by
        push_cast
        linear_combination h3 - (n : ZMod p) * hz
      exact h2 ((ZMod.natCast_eq_zero_iff _ _).1 h4)
  · exact hm (hp.dvd_of_dvd_pow h)

section Space

open CFSG.GroupTheory.WeirSylow Module CFSG.RankThree.PartOne.KFQ
open CFSG.Assembly.LowTwoRank (StatedSp)

variable {K : Type} [Field K] [Finite K] [CharP K 2]

@[expose] noncomputable def M4 (K : Type) [Field K] [Finite K] [CharP K 2] :
    Subgroup (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :=
  formIsometryGroup K (fun x y => ∑ i, qForm (x i) (y i))

theorem mem_M4_iff (g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :
    g ∈ M4 K ↔ ∀ x y, ∑ i, qForm (g x i) (g y i) = ∑ i, qForm (x i) (y i) :=
  Iff.rfl

noncomputable abbrev sp2Space (K : Type) [Field K] [Finite K] [CharP K 2] : FormSpace K K :=
  FormSpace.pi (fun _ : Fin 2 => (⟨Qext K, fun x y => qForm x y⟩ : FormSpace K K))

theorem isSymplecticSpace_sp2 : IsSymplecticSpace (sp2Space K) :=
  isSymplecticSpace_pi _ (fun _ => ⟨qForm, fun _ _ => rfl, qForm_isAlt, qForm_nondegenerate⟩)

theorem finrank_sp2 : finrank K (sp2Space K).V = 2 * 2 := by
  rw [FormSpace.finrank_pi]
  simp [finrank_qext]

theorem nonempty_m4Equiv : Nonempty (↥(M4 K) ≃* ↥(StatedSp 2 K)) := by
  obtain ⟨B, hBF, hBa, hBn⟩ := isSymplecticSpace_sp2 (K := K)
  obtain ⟨ι⟩ := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_form_isometry B
    (CFSG.LocalAnalysis.ComponentInitial.pairedSympForm K 2) hBa hBn
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_isAlt
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.pairedSympForm_nondegenerate
    (by rw [finrank_sp2, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.finrank_standard])
  let e₁ : (sp2Space K).isom ≃* (stdSympSpace K 2).isom :=
    formIsometryGroupCongr ι.toLinearEquiv fun x y => by
      rw [hBF]
      exact ι.map_app y x
  let M := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Pi.basisFun K (Fin 2 ⊕ Fin 2))
  have hmem : ∀ g : (stdSympSpace K 2).isom, M g.1 ∈ StatedSp 2 K := fun g => by
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.map_isometryGroup_eq_statedSp]
    exact Subgroup.mem_map_of_mem _ (TauCeti.BilinForm.mem_isometryGroup_iff.2 g.2)
  let ψ₀ : (stdSympSpace K 2).isom →* StatedSp 2 K :=
    { toFun := fun g => ⟨M g.1, hmem g⟩
      map_one' := Subtype.ext (map_one M)
      map_mul' := fun g h => Subtype.ext (map_mul M g.1 h.1) }
  have hinj : Function.Injective ψ₀ := fun g h hgh =>
    Subtype.ext (M.injective (congrArg Subtype.val hgh))
  have hsurj : Function.Surjective ψ₀ := by
    rintro ⟨A, hA⟩
    have hA' := hA
    rw [← CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.map_isometryGroup_eq_statedSp] at hA'
    obtain ⟨g, hg, hgA⟩ := hA'
    refine ⟨⟨g, ?_⟩, Subtype.ext hgA⟩
    intro x y
    exact TauCeti.BilinForm.mem_isometryGroup_iff.1 hg x y
  have hbij : Function.Bijective (ψ₀.comp e₁.toMonoidHom) :=
    ⟨hinj.comp e₁.injective, hsurj.comp e₁.surjective⟩
  exact ⟨MulEquiv.ofBijective _ hbij⟩

instance : Finite (M4 K) := by
  obtain ⟨e⟩ := nonempty_m4Equiv (K := K)
  exact Finite.of_equiv _ e.symm.toEquiv

end Space

section Torus

open CFSG.GroupTheory.WeirSylow Module CFSG.RankThree.PartOne.KFQ CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] [Finite K] [CharP K 2]

theorem card_qext : Nat.card (Qext K) = Nat.card K ^ 2 := FiniteField.natCard_extension K 2 2

theorem torusEquiv_mem_M4_of_norm {x : Fin 2 → (Qext K)ˣ}
    (hx : ∀ i, (x i : Qext K) * frobQ K (x i) = 1) : torusEquiv x ∈ M4 K := by
  rw [mem_M4_iff]
  intro v w
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [torusEquiv_apply, torusEquiv_apply]
  exact qForm_mul_unit (hx i) _ _

@[expose] noncomputable def sylowHom2 (S : Subgroup (Qext K)ˣ) :
    (Fin 2 → ↥S) →* (QV K (Fin 2) ≃ₗ[K] QV K (Fin 2)) :=
  torusHom.comp (MonoidHom.pi fun i => S.subtype.comp (Pi.evalMonoidHom (fun _ : Fin 2 => ↥S) i))

theorem sylowHom2_apply (S : Subgroup (Qext K)ˣ) (x : Fin 2 → ↥S) (w : QV K (Fin 2)) (i : Fin 2) :
    sylowHom2 S x w i = ((x i : (Qext K)ˣ) : Qext K) * w i := rfl

theorem sylowHom2_eq_torusEquiv (S : Subgroup (Qext K)ˣ) (x : Fin 2 → ↥S) :
    sylowHom2 S x = torusEquiv (fun i => (x i : (Qext K)ˣ)) := rfl

theorem sylowHom2_injective (S : Subgroup (Qext K)ˣ) :
    Function.Injective (sylowHom2 (K := K) S) := by
  intro x y h
  funext i
  have := congrArg (fun g : QV K (Fin 2) ≃ₗ[K] QV K (Fin 2) => g (fun _ => 1) i) h
  simp only [sylowHom2_apply, mul_one] at this
  exact Subtype.ext (Units.ext this)

theorem sylowShape_M4 {p e m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he1 : 1 ≤ e)
    (hQ : Nat.card K + 1 = p ^ e * m) (hm : ¬ p ∣ m) : SylowShape p 2 e ↥(M4 K) := by
  classical
  have hpe : p ^ e ∣ Nat.card K + 1 := ⟨m, hQ⟩
  have hQpos : 1 ≤ Nat.card K := Nat.card_pos
  obtain ⟨n, hn⟩ : ∃ n, Nat.card K = n + 1 := ⟨Nat.card K - 1, by omega⟩
  have hn' : n + 2 = p ^ e * m := by
    have := hQ
    rw [hn] at this
    omega
  have hdvd : p ^ e ∣ Nat.card (Qext K) - 1 := by
    rw [card_qext, hn]
    have : (n + 1) ^ 2 - 1 = n * (n + 2) := Nat.sub_eq_of_eq_add (by ring)
    rw [this]
    exact Dvd.dvd.mul_left ⟨m, hn'⟩ _
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hcard := CFSG.LinearGroups.card_rootsOfUnity_of_dvd (K := Qext K) hdvd
  set S : Subgroup (Qext K)ˣ := rootsOfUnity (p ^ e) (Qext K) with hS
  set ι := sylowHom2 (K := K) S with hι
  have hinj : Function.Injective ι := sylowHom2_injective S
  have hle : ι.range ≤ M4 K := by
    rintro _ ⟨x, rfl⟩
    rw [hι, sylowHom2_eq_torusEquiv]
    refine torusEquiv_mem_M4_of_norm fun i => unit_mul_frob_eq_one_of_pow ?_
    have h1 : (x i : (Qext K)ˣ) ^ (p ^ e) = 1 := (mem_rootsOfUnity _ _).1 (x i).2
    rw [hQ, pow_mul, h1, one_pow]
  set T : Subgroup ↥(M4 K) := ι.range.subgroupOf (M4 K) with hT
  have hrange : Nat.card ι.range = p ^ (2 * e) := by
    rw [Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm, Nat.card_pi, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    have : Nat.card ↥S = p ^ e := hcard
    rw [this, ← pow_mul, mul_comm]
  have hTcard : Nat.card T = p ^ (2 * e) := by
    rw [hT, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hrange]
  have hTp : IsPGroup p ↥T := IsPGroup.of_card hTcard
  obtain ⟨φe⟩ := nonempty_m4Equiv (K := K)
  have hMcard : Nat.card ↥(M4 K) =
      p ^ (2 * e) * ((n + 1) ^ 4 * n ^ 2 * ((n + 1) ^ 2 + 1) * m ^ 2) := by
    rw [Nat.card_congr φe.toEquiv, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
      hn]
    exact sp4_card_factor hn'
  have hidx : ¬ p ∣ T.index := by
    have h1 := Subgroup.card_mul_index T
    rw [hTcard, hMcard] at h1
    have h2 : T.index = (n + 1) ^ 4 * n ^ 2 * ((n + 1) ^ 2 + 1) * m ^ 2 :=
      Nat.eq_of_mul_eq_mul_left (pow_pos hp.pos _) h1
    rw [h2]
    exact sp4_index_coprime hp hp2 he1 hm hn'
  have hcyc : IsCyclic ↥S := inferInstance
  let φ2 : Multiplicative (ZMod (p ^ e)) ≃* ↥S :=
    (((ZMod.ringEquivCongr hcard.symm).toAddEquiv).toMultiplicative).trans (zmodCyclicMulEquiv hcyc)
  let φ : ↥T ≃* (Fin 2 → Multiplicative (ZMod (p ^ e))) :=
    (Subgroup.subgroupOfEquivOfLe hle).trans
      ((MonoidHom.ofInjective hinj).symm.trans (MulEquiv.piCongrRight fun _ => φ2.symm))
  exact SylowShape.of_witness hp hTp hidx φ

theorem sylowShape_statedSp4 {p e m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (he1 : 1 ≤ e)
    (hQ : Nat.card K + 1 = p ^ e * m) (hm : ¬ p ∣ m) : SylowShape p 2 e ↥(StatedSp 2 K) := by
  obtain ⟨φe⟩ := nonempty_m4Equiv (K := K)
  exact SylowShape.of_mulEquiv φe.symm (sylowShape_M4 hp hp2 he1 hQ hm)

theorem sylowShape_of_psp4Model {X : Type} [Group X] [Finite X] {f p e m : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (he1 : 1 ≤ e) (hQ : 2 ^ f + 1 = p ^ e * m) (hm : ¬ p ∣ m)
    (hX : StatedClassicalModel X .PSp 2 2 f) : SylowShape p 2 e X := by
  obtain ⟨-, K, _, _, hK, ⟨φ⟩⟩ := hX
  have : Fintype K := Fintype.ofFinite K
  have : CharP K 2 := charP_of_card_eq_prime_pow (f := f) (by
    rw [← Nat.card_eq_fintype_card, hK])
  have hker := (CFSG.LieType.Classical.symplectic_scalar_kernel K 2 (by norm_num)).2
  have hN : ¬ p ∣ Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) := by
    have h1 : Nat.card ((StatedScalars (Fin 2 ⊕ Fin 2) K).subgroupOf (StatedSp 2 K)) =
        Nat.card ↥(StatedSp 2 K ⊓ StatedScalars (Fin 2 ⊕ Fin 2) K) := by
      rw [← Subgroup.card_map_of_injective (StatedSp 2 K).subtype_injective,
        Subgroup.subgroupOf_map_subtype, inf_comm]
    rw [h1, hker]
    intro h
    have h2 : p ∣ 2 := h.trans (Nat.gcd_dvd_left _ _)
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
  have hQ' : Nat.card K + 1 = p ^ e * m := by rw [hK]; exact hQ
  exact SylowShape.of_mulEquiv φ (SylowShape.quotient hp _ hN
    (sylowShape_statedSp4 hp hp2 he1 hQ' hm))

end Torus

end CFSG.RankThree.PartOne.K1214
