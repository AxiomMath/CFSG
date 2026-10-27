module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Conf
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofCompOne
import CFSG.RankThree.PartTwo.Sec14.Ronan148DM24
import CFSG.RankThree.PartTwo.Sec14.Ronan148DTwoON
import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofWE
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item134Dichotomy

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ronan152SL25

omit [Finite G] in
theorem commutator_mem_inf {P Y : Subgroup G} (hPY : P ≤ Subgroup.normalizer (Y : Set G))
    {ℓ : G} (hℓY : ℓ ∈ Y) (hℓP : ℓ ∈ Subgroup.normalizer (P : Set G)) {x : G} (hx : x ∈ P) :
    ⁅x, ℓ⁆ ∈ P ⊓ Y := by
  refine ⟨?_, ?_⟩
  · have h1 : ℓ * x⁻¹ * ℓ⁻¹ ∈ P := (Subgroup.mem_normalizer_iff.mp hℓP _).mp (P.inv_mem hx)
    have e : ⁅x, ℓ⁆ = x * (ℓ * x⁻¹ * ℓ⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact P.mul_mem hx h1
  · have h1 : x * ℓ * x⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hPY hx) _).mp hℓY
    rw [commutatorElement_def]
    exact Y.mul_mem h1 (Y.inv_mem hℓY)

omit [Finite G] in
theorem commute_of_inf_eq_bot {P Y : Subgroup G} (hPY : P ≤ Subgroup.normalizer (Y : Set G))
    {ℓ : G} (hℓY : ℓ ∈ Y) (hℓP : ℓ ∈ Subgroup.normalizer (P : Set G)) (hbot : P ⊓ Y = ⊥)
    {x : G} (hx : x ∈ P) : x * ℓ = ℓ * x := by
  have h := commutator_mem_inf hPY hℓY hℓP hx
  rw [hbot, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h
  exact h

theorem le_of_forall_commutator_mem {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) {P P₀ F : Subgroup G}
    (hP : IsPGroup p P) (hF3 : IsPGroup 3 F) (hP₀P : P₀ ≤ P)
    (hFP₀ : F ≤ Subgroup.normalizer (P₀ : Set G))
    (hcomm : ∀ x ∈ P, ∀ f ∈ F, ⁅x, f⁆ ∈ P₀)
    (hfr : P ⊓ Subgroup.centralizer (F : Set G) ≤ (frattini ↥P).map P.subtype) : P ≤ P₀ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set α : ↥F →* MulAut G := (MulAut.conj : G →* MulAut G).comp F.subtype with hα
  have hαapp : ∀ (f : ↥F) (y : G), α f y = (f : G) * y * (f : G)⁻¹ := fun _ _ => rfl
  have hP₀3 : ¬ 3 ∣ Nat.card P₀ := by
    have hP₀p : IsPGroup p P₀ := hP.to_le hP₀P
    obtain ⟨k, hk⟩ := hP₀p.exists_card_eq
    rw [hk]
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three (Fact.out : p.Prime)).mp
      (Nat.prime_three.dvd_of_dvd_pow h3)
    exact hp3 this.symm
  have hmem : ∀ x ∈ P, ∃ c ∈ P ⊓ Subgroup.centralizer (F : Set G), x⁻¹ * c ∈ P₀ := by
    intro x hx
    set S : Set G := {y | x⁻¹ * y ∈ P₀} with hS
    have hSinv : ∀ f : ↥F, ∀ y ∈ S, α f y ∈ S := by
      intro f y hy
      change x⁻¹ * ((f : G) * y * (f : G)⁻¹) ∈ P₀
      have h1 : ⁅x⁻¹, (f : G)⁆ ∈ P₀ := hcomm _ (P.inv_mem hx) _ f.2
      have h2 : (f : G) * (x⁻¹ * y) * (f : G)⁻¹ ∈ P₀ :=
        (Subgroup.mem_normalizer_iff.mp (hFP₀ f.2) _).mp hy
      have e : x⁻¹ * ((f : G) * y * (f : G)⁻¹) =
          ⁅x⁻¹, (f : G)⁆ * ((f : G) * (x⁻¹ * y) * (f : G)⁻¹) := by
        rw [commutatorElement_def]; group
      rw [e]
      exact P₀.mul_mem h1 h2
    have hScard : Nat.card S = Nat.card P₀ := Nat.card_congr
      { toFun := fun y => ⟨x⁻¹ * y.1, y.2⟩
        invFun := fun z => ⟨x * z.1, by change x⁻¹ * (x * z.1) ∈ P₀; simpa using z.2⟩
        left_inv := fun y => Subtype.ext (by simp)
        right_inv := fun z => Subtype.ext (by simp) }
    have hF3' : IsPGroup 3 ↥F := hF3
    obtain ⟨c, hcS, hcfix⟩ :=
      CFSG.Semidihedral.Principal.CoprimeFixedPoint.exists_fixed_of_invariant 3 hF3' α S hSinv
        (hScard ▸ hP₀3)
    have hcP : c ∈ P := by
      have h1 : x * (x⁻¹ * c) ∈ P := P.mul_mem hx (hP₀P hcS)
      simpa using h1
    have hcC : c ∈ Subgroup.centralizer (F : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro f hf
      have h := hcfix ⟨f, hf⟩
      rw [hαapp] at h
      calc f * c = f * c * f⁻¹ * f := by group
        _ = c * f := by rw [h]
    exact ⟨c, ⟨hcP, hcC⟩, hcS⟩
  have hsup : P₀.subgroupOf P ⊔ frattini ↥P = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    obtain ⟨c, hc, hxc⟩ := hmem x hx
    obtain ⟨φ, hφ, hφc⟩ := hfr hc
    have hφx : (φ : G) = c := hφc
    have hφmem : φ ∈ frattini ↥P := hφ
    have hrest : (⟨x, hx⟩ : ↥P) = φ * (⟨x⁻¹ * c, hP₀P hxc⟩ : ↥P)⁻¹ := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφx]
      group
    rw [hrest, sup_comm]
    exact Subgroup.mul_mem_sup hφmem (Subgroup.inv_mem _ (Subgroup.mem_subgroupOf.mpr hxc))
  have htop : P₀.subgroupOf P = ⊤ := frattini_nongenerating hsup
  intro x hx
  have h1 : (⟨x, hx⟩ : ↥P) ∈ P₀.subgroupOf P := htop ▸ Subgroup.mem_top _
  exact Subgroup.mem_subgroupOf.mp h1

theorem eq_sup_theta_of_card_le {T X : Subgroup G} (hTX : T ≤ X)
    (hcard : Nat.card (↥X ⧸ aschbacherSolvableCore 3 ↥X) ≤
      Nat.card (↥T ⧸ aschbacherSolvableCore 3 ↥T)) :
    X = T ⊔ inSubgroup (aschbacherSolvableCore 3) X := by
  have hinj : Function.Injective (Subgroup.inclusion hTX) := Subgroup.inclusion_injective hTX
  set K : Subgroup ↥T := (aschbacherSolvableCore 3 ↥X).comap (Subgroup.inclusion hTX) with hK
  have hKmap : K.map (Subgroup.inclusion hTX) ≤ aschbacherSolvableCore 3 ↥X :=
    Subgroup.map_comap_le _ _
  have hKθ : K ≤ aschbacherSolvableCore 3 ↥T := by
    obtain ⟨hθs, -, hθ3, -, -⟩ :=
      solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three
    have hmax := (solvable_prime_complement_core_characterization (H := ↥T)
      Nat.prime_three).2.2.2.1
    have hKn : K.Normal := Subgroup.Normal.comap (aschbacherSolvableCore_normal 3 ↥X) _
    set g : ↥K →* ↥(aschbacherSolvableCore 3 ↥X) :=
      (Subgroup.inclusion hKmap).comp (K.equivMapOfInjective _ hinj).toMonoidHom with hg
    have hginj : Function.Injective g :=
      (Subgroup.inclusion_injective hKmap).comp (K.equivMapOfInjective _ hinj).injective
    refine hmax K hKn (Group.isSolvable_of_isSolvable_injective (f := g) hginj) ?_
    intro h3
    apply hθ3
    have hc : Nat.card K = Nat.card (K.map (Subgroup.inclusion hTX)) :=
      (Subgroup.card_map_of_injective hinj).symm
    exact h3.trans (hc ▸ Subgroup.card_dvd_of_le hKmap)
  set f : ↥T →* ↥X ⧸ aschbacherSolvableCore 3 ↥X :=
    (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X)).comp (Subgroup.inclusion hTX) with hf
  have hker : f.ker = K := by
    ext t
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    exact QuotientGroup.eq_one_iff _
  have hrange : Nat.card (↥T ⧸ aschbacherSolvableCore 3 ↥T) ≤ Nat.card f.range := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hker]
    exact Nat.le_of_dvd Nat.card_pos (Subgroup.index_dvd_of_le hKθ)
  have htop : f.range = ⊤ := by
    refine Subgroup.eq_top_of_card_eq _ (le_antisymm (Subgroup.card_le_card_group _) ?_)
    exact hcard.trans hrange
  refine le_antisymm ?_ (sup_le hTX (Sec6.theta_le X))
  intro x hx
  have hq : QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) ⟨x, hx⟩ ∈ f.range :=
    htop ▸ Subgroup.mem_top _
  obtain ⟨t, ht⟩ := hq
  have ht' : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥X) (Subgroup.inclusion hTX t) :
      ↥X ⧸ aschbacherSolvableCore 3 ↥X) = QuotientGroup.mk' _ ⟨x, hx⟩ := ht
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at ht'
  have he : x = (t : G) * (((Subgroup.inclusion hTX t)⁻¹ * ⟨x, hx⟩ : ↥X) : G) := by
    simp [Subgroup.coe_inclusion]
  rw [he]
  exact Subgroup.mul_mem_sup t.2 ⟨_, ht', rfl⟩

omit [Finite G] in
theorem commutator_mem_of_eq_sup {K T N : Subgroup G} (hK : K = T ⊔ N) (hNK : N ≤ K)
    (hKN : K ≤ Subgroup.normalizer (N : Set G)) {f : G}
    (hfN : f ∈ Subgroup.normalizer (N : Set G)) (hfT : f ∈ Subgroup.centralizer (T : Set G))
    {x : G} (hx : x ∈ K) : ⁅x, f⁆ ∈ N := by
  let H : Subgroup G :=
    { carrier := {y | y ∈ K ∧ ⁅y, f⁆ ∈ N}
      mul_mem' := by
        rintro y z ⟨hyK, hy⟩ ⟨hzK, hz⟩
        refine ⟨K.mul_mem hyK hzK, ?_⟩
        have e : ⁅y * z, f⁆ = (y * ⁅z, f⁆ * y⁻¹) * ⁅y, f⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact N.mul_mem ((Subgroup.mem_normalizer_iff.mp (hKN hyK) _).mp hz) hy
      one_mem' := by
        refine ⟨K.one_mem, ?_⟩
        have e : ⁅(1 : G), f⁆ = 1 := by simp only [commutatorElement_def]; group
        rw [e]
        exact N.one_mem
      inv_mem' := by
        rintro y ⟨hyK, hy⟩
        refine ⟨K.inv_mem hyK, ?_⟩
        have e : ⁅y⁻¹, f⁆ = y⁻¹ * ⁅y, f⁆⁻¹ * y⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hKN (K.inv_mem hyK)) _).mp (N.inv_mem hy) }
  have hTH : T ≤ H := by
    intro t ht
    have htK : t ∈ K := by rw [hK]; exact Subgroup.mem_sup_left ht
    refine ⟨htK, ?_⟩
    rw [commutatorElement_eq_one_iff_mul_comm.mpr ((Subgroup.mem_centralizer_iff.mp hfT) t ht)]
    exact N.one_mem
  have hNH : N ≤ H := by
    intro n hn
    refine ⟨hNK hn, ?_⟩
    have e : ⁅n, f⁆ = n * (f * n⁻¹ * f⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact N.mul_mem hn ((Subgroup.mem_normalizer_iff.mp hfN _).mp (N.inv_mem hn))
  have hx' : x ∈ T ⊔ N := by rw [← hK]; exact hx
  exact (sup_le hTH hNH hx').2

theorem le_theta_of_cover {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) {P K T F B : Subgroup G}
    (hP : IsPGroup p P) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hF3 : IsPGroup 3 F) (hFK : F ≤ K) (hFP : F ≤ Subgroup.normalizer (P : Set G))
    (hfrF : P ⊓ Subgroup.centralizer (F : Set G) ≤ (frattini ↥P).map P.subtype)
    (hB3 : IsPGroup 3 B) (hBP : B ≤ Subgroup.normalizer (P : Set G))
    (hBK : B ≤ Subgroup.normalizer (K : Set G)) (hBT : B ≤ Subgroup.centralizer (T : Set G))
    (hK : K = T ⊔ inSubgroup (aschbacherSolvableCore 3) K)
    (hfrB : P ⊓ Subgroup.centralizer (B : Set G) ≤ (frattini ↥P).map P.subtype) :
    P ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
  have hPK' : P ≤ P ⊓ K := by
    refine le_of_forall_commutator_mem hp3 hP hF3 inf_le_left
      (Late.le_normalizer_inf hFP (hFK.trans Subgroup.le_normalizer)) (fun x hx f hf => ?_) hfrF
    exact commutator_mem_inf hPK (hFK hf) (hFP hf) hx
  have hPKle : P ≤ K := hPK'.trans inf_le_right
  have hBθ : B ≤ Subgroup.normalizer (θK : Set G) :=
    hBK.trans (Sec6.normalizer_le_normalizer_theta K)
  have hPθ : P ≤ P ⊓ θK := by
    refine le_of_forall_commutator_mem hp3 hP hB3 inf_le_left
      (Late.le_normalizer_inf hBP hBθ) (fun x hx f hf => ⟨?_, ?_⟩) hfrB
    · have h1 : f * x⁻¹ * f⁻¹ ∈ P :=
        (Subgroup.mem_normalizer_iff.mp (hBP hf) _).mp (P.inv_mem hx)
      have e : ⁅x, f⁆ = x * (f * x⁻¹ * f⁻¹) := by rw [commutatorElement_def]; group
      rw [e]
      exact P.mul_mem hx h1
    · exact commutator_mem_of_eq_sup hK (Sec6.theta_le K) (Sec6.le_normalizer_theta K) (hBθ hf)
        (hBT hf) (hPKle hx)
  exact hPθ.trans inf_le_right

section Config

theorem card_lB_quotTheta {A L B Lb : Subgroup G} {c b d : G} (h : Sec14Std G A c L)
    (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    Nat.card (↥(lB A B) ⧸ aschbacherSolvableCore 3 ↥(lB A B)) = 1080 := by
  obtain ⟨-, hd1⟩ := hc.ne_one hB h.isE27'
  obtain ⟨hdL, S, hdS, hSd⟩ := hc.2.2.2.2
  obtain ⟨-, htc, -, -⟩ := residual_facts Sec4.Sporadic.rank3II_4_15
    (Item148HJ.j2_of_isLBConfig hc) hdL hd1 ⟨S, hdS, hSd⟩
  rw [← Item148HJ.lB_eq_residual h hB hc] at htc
  exact card_eq_of_isTripleCover_six htc

theorem inf_centralizer_le_of_mem {B P : Subgroup G} {b : G} (hbB : b ∈ B)
    (hfr : P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype) :
    P ⊓ Subgroup.centralizer (B : Set G) ≤ (frattini ↥P).map P.subtype := fun _ hw =>
  hfr ⟨hw.1, Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB) hw.2⟩

theorem le_theta_of_one (h48 : Sec4.Item4_8) (hcomp : Step143HJCompOne) {A L : Subgroup G}
    {c : G} (h : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B)
    (hc : IsLBConfig A B b d Lb) {e : G} (heB : e ∈ B) {D L' : Subgroup G} {b' d' : G}
    (hOne : Desc143X.One A c L e b' d' D L') {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3)
    {P : Subgroup G} (hP : IsPGroup p P) (hAP : A ≤ Subgroup.normalizer (P : Set G))
    (hPe : P ≤ Subgroup.centralizer ({e} : Set G))
    (hfr : P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype) :
    ∃ K ∈ thetaComponentsAt 3 e, lB A D ≤ K ∧ lB A B ≤ K ∧
      Subgroup.centralizer ({e} : Set G) ≤ Subgroup.normalizer (K : Set G) ∧
      K = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) K ∧
      P ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  have hA := h.isE27'
  have heA : e ∈ A := hB.1 heB
  obtain ⟨K, hK, hDK⟩ := hOne.exists_mem h48
  have hN := hOne.le_normalizer hK hDK
  have hBK := hOne.lB_le h48 hK hDK hB heB
  have hKD := hcomp G A c L hOne.std e hOne.mem hOne.ne_one hOne.not_mem_omegaA D b' d' L'
    hOne.hyp hOne.mem_hyp hOne.config hOne.ne_d K hK hDK
  have h1080 := Desc143X.card_quotTheta_eq hOne hDK hKD
  have hKeq : K = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) K :=
    eq_sup_theta_of_card_le hBK (by rw [h1080, card_lB_quotTheta h hB hc])
  have hAe : A ≤ Subgroup.centralizer ({e} : Set G) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute hy heA)
  have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b _)
  have hbA : b ∈ A := hB.1 hbB
  refine ⟨K, hK, hDK, hBK, hN, hKeq, ?_⟩
  refine le_theta_of_cover hp3 hP (hPe.trans hN) (F := A ⊓ L') (hA.isPGroup.to_le inf_le_left)
    ?_ (inf_le_left.trans hAP) ?_ (hA.isPGroup.to_le hB.1) (hB.1.trans hAP)
    (hB.1.trans (hAe.trans hN)) (Subgroup.le_centralizer_iff.mp (lB_le_centralizer A B)) hKeq
    (inf_centralizer_le_of_mem hbB hfr)
  ·
    exact (Item148HJ.inf_le_residual h hOne.hyp hOne.config).trans
      ((Item148HJ.lB_eq_residual h hOne.hyp hOne.config).symm.le.trans hDK)
  ·
    intro w hw
    refine hfr ⟨hw.1, ?_⟩
    have hle : Subgroup.zpowers e ⊔ (A ⊓ L') ≤ Subgroup.centralizer ({w} : Set G) := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · exact Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hPe hw.1)).symm
      · intro y hy
        exact Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hw.2) y hy)
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      (Subgroup.mem_centralizer_singleton_iff.mp (hle (hOne.le_sup hbA))).symm

theorem le_theta_of_le_normalizer {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb)
    {e : G} (heB : e ∈ B) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 e) (hBK : lB A B ≤ K)
    (hKeq : K = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) K)
    {p : ℕ} [Fact p.Prime] (hp3 : p ≠ 3) {P : Subgroup G} (hP : IsPGroup p P)
    (hAP : A ≤ Subgroup.normalizer (P : Set G)) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hfr : P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype)
    (hfrF : P ⊓ Subgroup.centralizer ((A ⊓ Lb : Subgroup G) : Set G) ≤
      (frattini ↥P).map P.subtype) :
    P ≤ inSubgroup (aschbacherSolvableCore 3) K := by
  have hA := h.isE27'
  have heA : e ∈ A := hB.1 heB
  have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b _)
  have hBC : B ≤ Subgroup.centralizer ((lB A B : Subgroup G) : Set G) :=
    Subgroup.le_centralizer_iff.mp (lB_le_centralizer A B)
  have hBK' : B ≤ Subgroup.normalizer (K : Set G) := by
    intro f hf
    refine Ronan148D.mem_normalizer_of_normalizes_lB h hB hc hK hBK
      (Subgroup.mem_centralizer_singleton_iff.mpr (h.toSec13Data.commute (hB.1 hf) heA)) ?_
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.centralizer_le_normalizer _ (hBC hf))
  exact le_theta_of_cover hp3 hP hPK (hA.isPGroup.to_le inf_le_left)
    ((Item148HJ.inf_le_residual h hB hc).trans
      ((Item148HJ.lB_eq_residual h hB hc).symm.le.trans hBK))
    (inf_le_left.trans hAP) hfrF (hA.isPGroup.to_le hB.1) (hB.1.trans hAP) hBK' hBC hKeq
    (inf_centralizer_le_of_mem hbB hfr)

end Config

end Ronan152SL25

@[expose] noncomputable def Step152SL25ModR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
    ∀ (p : ℕ) (P : Subgroup G), PData152 A X p P → 3 < p →
      P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype →
    ∀ e ∈ B, e ∉ Subgroup.zpowers b → Subgroup.zpowers e ∉ omegaA A →
      P ≤ Subgroup.centralizer ({e} : Set G) →
    ∀ K ∈ thetaComponentsAt 3 e, lB A B ≤ K →
      K = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) K →
      P ≤ inSubgroup (aschbacherSolvableCore 3) K → False

@[expose] noncomputable def Step152SL25PureTwoR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
    ∀ (p : ℕ) (P : Subgroup G), PData152 A X p P → 3 < p →
      P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype →
    ∀ e ∈ B, e ∉ Subgroup.zpowers b → Subgroup.zpowers e ∉ omegaA A →
      P ≤ Subgroup.centralizer ({e} : Set G) →
      (∀ (D : Subgroup G) (b' d' : G) (L' : Subgroup G), IsHyperplane A D → e ∈ D →
        IsLBConfig A D b' d' L' → Subgroup.zpowers e = Subgroup.zpowers d') →
      (∀ K ∈ thetaComponentsAt 3 e, lB A B ≤ K →
        K = lB A B ⊔ inSubgroup (aschbacherSolvableCore 3) K →
        P ≤ Subgroup.normalizer (K : Set G) →
        ¬ P ⊓ Subgroup.centralizer ((A ⊓ Lb : Subgroup G) : Set G) ≤
          (frattini ↥P).map P.subtype) →
      False

theorem step152SL25ER_of_mod
    (h425 : Sec4.Item4_25Fix) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement)
    (hmod : Step152SL25ModR) (hpure : Step152SL25PureTwoR) : Step152SL25ER := by
  intro G _ _ A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe
  have hS := h.toSec14Std
  have : Fact p.Prime := ⟨hP.prime⟩
  have hp3' : p ≠ 3 := by omega
  have hPp : IsPGroup p P := by
    rcases hP.type_p with ⟨-, h2⟩ | ⟨-, h3⟩
    · exact IsPGroup.of_card h2
    · exact IsPGroup.of_card h3
  have heA : e ∈ A := hB.1 heB
  have he1 : e ≠ 1 := fun h1 => heb (h1 ▸ Subgroup.one_mem _)
  by_cases hI : ∃ (D : Subgroup G) (b' d' : G) (L' : Subgroup G), IsHyperplane A D ∧ e ∈ D ∧
      IsLBConfig A D b' d' L' ∧ Subgroup.zpowers e ≠ Subgroup.zpowers d'
  · obtain ⟨D, b', d', L', hD, heD, hc', hne⟩ := hI
    obtain ⟨K, hK, -, hBK, -, hKeq, hPK⟩ := Ronan152SL25.le_theta_of_one h48
      (Ronan148D.step143HJCompOne_of_item4_25Fix' h425 h134 h48 h41 hGW) hS hB hc heB
      ⟨hS, heA, he1, heΩ, hD, heD, hc', hne⟩ hp3' hPp hP.norm_p hPe hfr
    exact hmod G A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe
      K hK hBK hKeq hPK
  · push Not at hI
    refine hpure G A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe hI
      fun K hK hBK hKeq hPN hfrF => ?_
    exact hmod G A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe
      K hK hBK hKeq (Ronan152SL25.le_theta_of_le_normalizer hS hB hc heB hK hBK hKeq hp3' hPp
        hP.norm_p hPN hfr hfrF)

@[expose] noncomputable def Step152SL25EOmegaNCR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → AllPointsHJ A →
    ∀ M X : Subgroup G, Ctx152J A (lB A) M X →
    ∀ (B : Subgroup G) (b d : G) (Lb : Subgroup G), IsHyperplane A B → IsLBConfig A B b d Lb →
      Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) = (B : Set G) →
    ∀ (p : ℕ) (P : Subgroup G), PData152 A X p P → 3 < p →
      P ⊓ Subgroup.centralizer ({b} : Set G) ≤ (frattini ↥P).map P.subtype →
    ∀ e ∈ B, e ∉ Subgroup.zpowers b → Subgroup.zpowers e ∈ omegaA A →
      P ≤ Subgroup.centralizer ({e} : Set G) →
      (∀ (D : Subgroup G) (x d' : G) (L' : Subgroup G), IsHyperplane A D →
        Subgroup.zpowers x = Subgroup.zpowers e → ¬ IsLBConfig A D x d' L') → False

theorem step152SL25EOmegaR_of_nc
    (h142 : Item142AllS14) (hnc : Step152SL25EOmegaNCR) :
    Step152SL25EOmegaR := by
  intro G _ _ A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe
  by_cases hconf : ∃ (D : Subgroup G) (x d' : G) (L' : Subgroup G), IsHyperplane A D ∧
      Subgroup.zpowers x = Subgroup.zpowers e ∧ IsLBConfig A D x d' L'
  · obtain ⟨D, x, d', L', hD, hxe, hc'⟩ := hconf
    have hA := h.isE27
    obtain ⟨hxΩ, hL', hJ, hθ, -, -, -, -, -, -⟩ := Ronan152SL25.lbConfig_facts hA hD hc'
    obtain ⟨-, -, -, -, hbA, hb1, hdA, -, -, -⟩ := Ronan152SL25.lbConfig_facts hA hB hc
    have hxe' : x ∈ Subgroup.zpowers e := by rw [← hxe]; exact Subgroup.mem_zpowers x
    have hxB : x ∈ B := Subgroup.zpowers_le.mpr heB hxe'
    have hxb : x ∉ Subgroup.zpowers b := fun hxb => heb
      (Subgroup.zpowers_le.mpr hxb (by rw [hxe]; exact Subgroup.mem_zpowers e))
    have hxB' : x ∈ Subgroup.closure ({b, d} : Set G) := hc.1 ▸ hxB
    have hcent' : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
        (Subgroup.closure {x, b} : Set G) := by
      rw [hcent, hc.1, Proof152WE.closure_eq_of_mem hA hbA hdA hb1 hxB' hxb]
    have hPx : P ≤ Subgroup.centralizer ({x} : Set G) := by
      intro w hw
      have h1 : Subgroup.zpowers e ≤ Subgroup.centralizer ({w} : Set G) :=
        Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (Subgroup.mem_centralizer_singleton_iff.mp (hPe hw)).symm)
      exact Subgroup.mem_centralizer_singleton_iff.mpr
        (Subgroup.mem_centralizer_singleton_iff.mp (h1 hxe')).symm
    exact Ronan152SL25.not_le_centralizer_ofJ h142 h.toSec14Std hctx hxΩ hL' hJ hθ hbA hcent' hP
      (by omega) hPx
  · push Not at hconf
    exact hnc G A c L h hHJ M X hctx B b d Lb hB hc hcent p P hP hp3 hfr e heB heb heΩ hPe hconf

theorem y4CoreExclSL25HJR_of_mod
    (h142 : Item142AllS14)
    (h425 : Sec4.Item4_25Fix) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h41 : Sec4.Item4_1LargePrime) (hGW : Sec6.GWLBalanceStatement)
    (hmod : Step152SL25ModR) (hpure : Step152SL25PureTwoR) (hnc : Step152SL25EOmegaNCR) :
    Y4CoreExclSL25HJR :=
  y4CoreExclSL25HJR_of_residual h142 (step152SL25ER_of_mod h425 h134 h48 h41 hGW hmod hpure)
    (step152SL25EOmegaR_of_nc h142 hnc)

end CFSG.RankThree.PartTwo.Sec15
