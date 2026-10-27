module

public import CFSG.RankThree.PartTwo.Sec15.Item152ExclSL2Defs
public import CFSG.RankThree.PartTwo.Sec14.Notation
public import CFSG.RankThree.PartTwo.Sec4.StatementsCensus
import CFSG.RankThree.PartTwo.Sec4.Census.Item44Groups
import CFSG.LocalAnalysis.LargeEvenClassification.CoprimeCommutators
import CFSG.RankThree.PartTwo.Sec14.Item145
public import CFSG.GroupTheory.LocalCores.PrimeSetCore
import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
open scoped MatrixGroups Pointwise commutatorElement

section OTwoP

variable {T : Type*} [Group T]

theorem isPiSubgroup_piCompl_three_of_isPGroup {q : ℕ} (hq : q.Prime) (hq3 : q ≠ 3)
    {H : Subgroup T} [Finite T] (hH : IsPGroup q H) : IsPiSubgroup (piCompl 3) H := by
  have : Fact q.Prime := ⟨hq⟩
  intro r hr hr3
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hH
  rw [hk] at hr
  have hrq : (r : ℕ) = q := (Nat.prime_dvd_prime_iff_eq r.2 hq).mp (r.2.dvd_of_dvd_pow hr)
  exact hq3 (hrq ▸ hr3)

theorem isPiSubgroup_oTwoP [Finite T] {p : ℕ} (hp : p.Prime) (hp3 : p ≠ 3) :
    IsPiSubgroup (piCompl 3) (Sec4.oTwoP p T) := by
  refine CFSG.LocalCores.isPiSubgroup_of_map_of_inf_ker (QuotientGroup.mk' (CFSG.pCore 2 T)) ?_ ?_
  · rw [Sec4.oTwoP, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _)]
    exact isPiSubgroup_piCompl_three_of_isPGroup hp hp3 CFSG.pCore_isPGroup
  · rw [QuotientGroup.ker_mk', inf_eq_right.mpr (Sec4.pCore_two_le_oTwoP p T)]
    exact isPiSubgroup_piCompl_three_of_isPGroup Nat.prime_two (by norm_num) CFSG.pCore_isPGroup

theorem oTwoP_characteristic (p : ℕ) : (Sec4.oTwoP p T).Characteristic := by
  rw [Subgroup.characteristic_iff_comap_eq]
  intro σ
  set O := CFSG.pCore 2 T with hO
  have hOσ : O.map σ.toMonoidHom = O := CFSG.pCore_map_iso 2 σ
  have hOσ' : O.map σ.symm.toMonoidHom = O := CFSG.pCore_map_iso 2 σ.symm
  set σ' : T ⧸ O ≃* T ⧸ O := QuotientGroup.congr O O σ hOσ with hσ'
  have hcomm : ∀ x : T, QuotientGroup.mk' O (σ x) = σ' (QuotientGroup.mk' O x) := fun x => rfl
  have hP : (CFSG.pCore p (T ⧸ O)).comap σ'.toMonoidHom = CFSG.pCore p (T ⧸ O) :=
    Subgroup.characteristic_iff_comap_eq.mp inferInstance σ'
  ext x
  change QuotientGroup.mk' O (σ x) ∈ CFSG.pCore p (T ⧸ O) ↔
    QuotientGroup.mk' O x ∈ CFSG.pCore p (T ⧸ O)
  rw [hcomm]
  conv_rhs => rw [← hP]
  rfl

end OTwoP

section SL2

variable {p : ℕ} [hp : Fact p.Prime]

theorem three_dvd_card_SL2 (hp3 : 3 < p) : 3 ∣ Nat.card SL(2, ZMod p) := by
  rw [Sec4.Census.card_SL2]
  have hp3' : p % 3 ≠ 0 := by
    intro h0
    have h3p : 3 ∣ p := Nat.dvd_of_mod_eq_zero h0
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp.out).mp h3p
    omega
  have hsq : p ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod]
    have : p % 3 = 1 ∨ p % 3 = 2 := by omega
    rcases this with h | h <;> rw [h]
  have hp1 : 1 ≤ p ^ 2 := Nat.one_le_pow _ _ hp.out.pos
  exact Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero (by omega)) p

theorem card_PSL2_mul_two (hp2 : p ≠ 2) :
    Nat.card PSL(2, ZMod p) * 2 = Nat.card SL(2, ZMod p) := by
  have h := Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center SL(2, ZMod p))
  rw [Sec4.Census.card_center_SL2 hp2] at h
  exact h.symm

theorem three_dvd_card_PSL2 (hp3 : 3 < p) : 3 ∣ Nat.card PSL(2, ZMod p) := by
  have h := three_dvd_card_SL2 hp3
  rw [← card_PSL2_mul_two (by omega)] at h
  exact (Nat.Coprime.dvd_mul_right (by norm_num)).mp h

theorem isSimpleGroup_PSL2 (hp5 : 5 ≤ p) : IsSimpleGroup PSL(2, ZMod p) :=
  (Sec4.Census.isQuasisimple_SL2 hp5).2.1

theorem exists_ne_comm_PSL2 (hp5 : 5 ≤ p) : ∃ a b : PSL(2, ZMod p), a * b ≠ b * a :=
  (Sec4.Census.isQuasisimple_SL2 hp5).2.2

end SL2

section Quotient

variable {T : Type*} [Group T] [Finite T] {p : ℕ} [hp : Fact p.Prime]

theorem nonempty_quotient_pPrimeCore_equiv_psl (hp5 : 5 < p)
    (e : T ⧸ Sec4.oTwoP p T ≃* SL(2, ZMod p)) :
    Nonempty (T ⧸ CFSG.pPrimeCore 3 T ≃* PSL(2, ZMod p)) := by
  set N := Sec4.oTwoP p T with hN
  set f : T →* SL(2, ZMod p) := e.toMonoidHom.comp (QuotientGroup.mk' N) with hf
  have hfs : Function.Surjective f := e.surjective.comp (QuotientGroup.mk'_surjective N)
  set Z := Subgroup.center SL(2, ZMod p) with hZ
  set g : T →* PSL(2, ZMod p) := (QuotientGroup.mk' Z).comp f with hg
  have hgs : Function.Surjective g := (QuotientGroup.mk'_surjective Z).comp hfs
  have hkerf : f.ker = N := by
    ext x
    simp only [hf, MonoidHom.mem_ker, MonoidHom.coe_comp, Function.comp_apply,
      MulEquiv.coe_toMonoidHom, map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff]
  have hkerg : g.ker = Z.comap f := by
    rw [hg, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
  have hq : IsQuasisimple SL(2, ZMod p) := Sec4.Census.isQuasisimple_SL2 (by omega)
  have h3SL := three_dvd_card_SL2 (p := p) (by omega)
  have hker3 : Nat.Coprime 3 (Nat.card g.ker) := by
    have hπ : IsPiSubgroup (piCompl 3) g.ker := by
      refine CFSG.LocalCores.isPiSubgroup_of_map_of_inf_ker f ?_ ?_
      · rw [hkerg, Subgroup.map_comap_eq_self_of_surjective hfs]
        intro r hr hr3
        have h2 : Nat.card Z = 2 := Sec4.Census.card_center_SL2 (by omega)
        rw [h2] at hr
        have := (Nat.prime_dvd_prime_iff_eq r.2 Nat.prime_two).mp hr
        change (r : ℕ) = 3 at hr3
        omega
      · rw [inf_eq_right.mpr (by rw [hkerg]; exact MonoidHom.ker_le_comap f Z), hkerf]
        exact isPiSubgroup_oTwoP hp.out (by omega)
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      ((isPiSubgroup_piCompl_iff Nat.prime_three _).mp hπ)
  have hle1 : g.ker ≤ CFSG.pPrimeCore 3 T := le_sSup ⟨g.normal_ker, hker3⟩
  have hle2 : CFSG.pPrimeCore 3 T ≤ g.ker := by
    have hn : ((CFSG.pPrimeCore 3 T).map f).Normal :=
      (CFSG.pPrimeCore_normal (p := 3) (G := T)).map f hfs
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hq hn with htop | hcen
    · exfalso
      have hc := CFSG.pPrimeCore_coprime_card (p := 3) (G := T)
      have hdvd : Nat.card SL(2, ZMod p) ∣ Nat.card (CFSG.pPrimeCore 3 T) := by
        rw [← Subgroup.card_top (G := SL(2, ZMod p)), ← htop]
        exact Subgroup.card_map_dvd _ _
      exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hc (h3SL.trans hdvd)
    · rw [hkerg]
      exact Subgroup.map_le_iff_le_comap.mp hcen
  have hker : g.ker = CFSG.pPrimeCore 3 T := le_antisymm hle1 hle2
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective g hgs)⟩

end Quotient

section ThreePrime

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
theorem not_three_dvd_card_sup {K H : Subgroup G}
    (hHK : H ≤ Subgroup.normalizer (K : Set G)) (hK : ¬ 3 ∣ Nat.card K)
    (hH : ¬ 3 ∣ Nat.card H) : ¬ 3 ∣ Nat.card (K ⊔ H : Subgroup G) := by
  set S := K ⊔ H with hS
  set K' := K.subgroupOf S with hK'
  have hKS : K ≤ S := le_sup_left
  have hHS : H ≤ S := le_sup_right
  have hK'n : K'.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKS).mpr
      (sup_le Subgroup.le_normalizer hHK)
  have hcardK' : Nat.card K' = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKS).toEquiv
  set φ : H →* S ⧸ K' := (QuotientGroup.mk' K').comp (Subgroup.inclusion hHS) with hφ
  have hφs : Function.Surjective φ := by
    intro q
    obtain ⟨⟨s, hs⟩, rfl⟩ := QuotientGroup.mk'_surjective K' q
    have hs' : s ∈ (K : Set G) * (H : Set G) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left K H hHK]
      exact hs
    obtain ⟨k, hk, h, hh, rfl⟩ := hs'
    refine ⟨⟨h, hh⟩, ?_⟩
    rw [hφ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq]
    change (⟨h, hHS hh⟩ : S)⁻¹ * ⟨k * h, hs⟩ ∈ K'
    rw [Subgroup.mem_subgroupOf]
    change h⁻¹ * (k * h) ∈ K
    have h1 := (Subgroup.mem_normalizer_iff.mp (hHK (inv_mem hh)) k).mp hk
    rw [inv_inv] at h1
    simpa [mul_assoc] using h1
  have hdvd : Nat.card (S ⧸ K') ∣ Nat.card H := Subgroup.card_dvd_of_surjective (f := φ) hφs
  intro h3
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup K'
  rw [← Subgroup.card_top (G := S), Subgroup.card_top] at hcard
  have h3' : 3 ∣ Nat.card (S ⧸ K') * Nat.card K' := by
    rw [← hcard]
    exact h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3' with h | h
  · exact hH (h.trans hdvd)
  · exact hK (hcardK' ▸ h)

end ThreePrime

section QGen

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

theorem le_qBound_sup_of_eq_delta {X N B : Subgroup G} (hΔ : X = delta A LB X)
    (hB : IsHyperplane A B) (hB3 : IsPGroup 3 B)
    (hBX : ∀ x ∈ X, ∀ b ∈ B, ⁅x, b⁆ ∈ N) : X ≤ (X ⊓ qBound A LB B) ⊔ N := by
  calc X = delta A LB X := hΔ
    _ ≤ (X ⊓ qBound A LB B) ⊔ N := by
      refine sSup_le fun Q hQ => ?_
      obtain ⟨hQq, hQX⟩ := hQ
      have hQ3 : ¬ 3 ∣ Nat.card Q :=
        (isPiSubgroup_piCompl_iff Nat.prime_three Q).mp hQq.1.2.1
      have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := hB.1.trans hQq.1.2.2
      rw [CFSG.LargeEvenClassification.Helpers.coprime_normalized_factorization
        Nat.prime_three B Q hB3 hQ3 hBQ]
      refine sup_le ?_ ?_
      · exact (le_inf (inf_le_left.trans hQX) (hQq.2 B hB)).trans le_sup_left
      · refine le_trans ?_ le_sup_right
        rw [Subgroup.commutator_le]
        intro q hq b hb
        exact hBX q (hQX hq) b hb

theorem threePrime_of_qGen {X N B : Subgroup G} (hΔ : X = delta A LB X)
    (hB : IsHyperplane A B) (hB3 : IsPGroup 3 B) (hLB : LB B = ⊥)
    (hXN : X ≤ Subgroup.normalizer (N : Set G)) (hN3 : ¬ 3 ∣ Nat.card N)
    (hBX : ∀ x ∈ X, ∀ b ∈ B, ⁅x, b⁆ ∈ N) : ¬ 3 ∣ Nat.card X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hndvd : ∀ K : Subgroup G, ¬ 3 ∣ Nat.card (pPrimeCoreOf 3 K) := fun K =>
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 K)
  have hq3 : ¬ 3 ∣ Nat.card (qBound A LB B) := by
    rw [qBound, hLB, sup_bot_eq]
    exact not_three_dvd_card_sup
      ((pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hB.1)) (hndvd _)
      (hndvd _)
  have hsup3 : ¬ 3 ∣ Nat.card ((X ⊓ qBound A LB B) ⊔ N : Subgroup G) := by
    rw [sup_comm]
    refine not_three_dvd_card_sup (inf_le_left.trans hXN) hN3 ?_
    intro h3
    exact hq3 (h3.trans (Subgroup.card_dvd_of_le inf_le_right))
  intro h3
  exact hsup3 (h3.trans (Subgroup.card_dvd_of_le (le_qBound_sup_of_eq_delta hΔ hB hB3 hBX)))

end QGen

section Hyperplane

variable {T : Type*} [Group T]

@[expose] noncomputable def quotMulAut (N : Subgroup T) [N.Normal] [hN : N.Characteristic] :
    MulAut T →* MulAut (T ⧸ N) where
  toFun σ := QuotientGroup.congr N N σ ((Subgroup.characteristic_iff_map_eq.mp hN) σ)
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl
  map_mul' σ τ := by
    ext x
    induction x using QuotientGroup.induction_on with
    | H x => rfl

theorem quotMulAut_mk (N : Subgroup T) [N.Normal] [N.Characteristic] (σ : MulAut T) (x : T) :
    quotMulAut N σ (x : T ⧸ N) = ((σ x : T) : T ⧸ N) :=
  rfl

end Hyperplane

section HyperplaneG

theorem isElemAbelian_map_hom {M M' : Type*} [Group M] [Group M'] {p : ℕ} {E : Subgroup M}
    (hE : CFSG.Assembly.IsElemAbelian p E) (φ : M →* M') :
    CFSG.Assembly.IsElemAbelian p (E.map φ) := CFSG.Open.IsElemAbelian.map hE _

variable {G : Type*} [Group G] [Finite G]

theorem exists_hyperplane_of_kSL2pAutThree (hAut : KSL2pAutThree) {A X : Subgroup G}
    (hA : CFSG.Assembly.IsElemAbelian 3 A) (hA27 : Nat.card A = 27)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) {p : ℕ} [Fact p.Prime] (hp5 : 5 < p)
    (N : Subgroup X) [N.Normal] [N.Characteristic] (e : X ⧸ N ≃* SL(2, ZMod p)) :
    ∃ B : Subgroup G, IsHyperplane A B ∧ IsPGroup 3 B ∧
      ∀ x ∈ X, ∀ b ∈ B, ⁅x, b⁆ ∈ N.map X.subtype := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ : A →* MulAut (X ⧸ N) :=
    (quotMulAut N).comp (X.normalizerMonoidHom.comp (Subgroup.inclusion hAX)) with hρ
  have hAtop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup A) := by
    refine ⟨⟨⟨fun a b => Subtype.ext (Subtype.ext ?_)⟩⟩, fun a _ => Subtype.ext (hA.2 a a.2)⟩
    exact congrArg Subtype.val (hA.1.is_comm.comm (a : A) (b : A))
  have hEab : CFSG.Assembly.IsElemAbelian 3
      (((⊤ : Subgroup A).map ρ).map (MulAut.congr e).toMonoidHom) :=
    isElemAbelian_map_hom (isElemAbelian_map_hom hAtop ρ) _
  have hcardE := hAut p hp5 _ hEab
  rw [Subgroup.card_map_of_injective (MulAut.congr e).injective, ← MonoidHom.range_eq_map]
    at hcardE
  have hcard : Nat.card ρ.range * Nat.card ρ.ker = 27 := by
    rw [← hA27, ← Nat.card_congr (QuotientGroup.quotientKerEquivRange ρ).toEquiv]
    exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker).symm
  have hker9 : 3 ^ 2 ∣ Nat.card ρ.ker := by
    have hr0 : 0 < Nat.card ρ.range := Nat.card_pos
    interval_cases h : Nat.card ρ.range <;> omega
  obtain ⟨K, hK⟩ := Sylow.exists_subgroup_card_pow_prime 3 hker9
  set B : Subgroup G := (K.map ρ.ker.subtype).map A.subtype with hB
  have hBcard : Nat.card B = 9 := by
    rw [hB, Subgroup.card_map_of_injective A.subtype_injective,
      Subgroup.card_map_of_injective ρ.ker.subtype_injective, hK]
    norm_num
  refine ⟨B, ⟨Subgroup.map_subtype_le _, by rw [hA27, hBcard]⟩,
    IsPGroup.of_card (n := 2) (by rw [hBcard]; norm_num), ?_⟩
  rintro x hx _ ⟨_, ⟨k, hk, rfl⟩, rfl⟩
  have hρk : ρ (k : A) = 1 := k.2
  set x' : X := ⟨x, hx⟩ with hx'
  set b : A := (k : A) with hbdef
  have hbX : (b : G) ∈ Subgroup.normalizer (X : Set G) := hAX b.2
  set σ := X.normalizerMonoidHom ⟨(b : G), hbX⟩ with hσ
  have h1 : ((x'⁻¹ : X) : X ⧸ N) = ((σ x'⁻¹ : X) : X ⧸ N) := by
    have h2 := congrArg (fun τ : MulAut (X ⧸ N) => τ ((x'⁻¹ : X) : X ⧸ N)) hρk
    simp only [MulAut.one_apply] at h2
    exact h2.symm
  rw [QuotientGroup.eq, inv_inv] at h1
  refine ⟨x' * σ x'⁻¹, h1, ?_⟩
  change (x : G) * (b * x⁻¹ * (b : G)⁻¹) = ⁅x, (b : G)⁆
  rw [commutatorElement_def]
  group

end HyperplaneG

end CFSG.RankThree.PartTwo.Sec15
