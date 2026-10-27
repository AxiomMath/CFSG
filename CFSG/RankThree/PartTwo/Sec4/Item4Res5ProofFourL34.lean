module

public import CFSG.RankThree.PartTwo.Sec4.Census.Item44Quasisimple
public import CFSG.RankThree.PartTwo.Sec4.Item4Res5ProofTwoLocal
public import CFSG.RankThree.PartTwo.Sec4.Item4Res5ProofL34
public import CFSG.RankThree.PartTwo.KFacts.L34Sections

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

namespace Res5L34

open CFSG CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.RankThree.PartTwo.KFacts.L34

section GroupTheory

variable {G : Type*} [Group G] [Finite G]

theorem exists_mul_mem_normalizer_of_sylow {p : ℕ} [Fact p.Prime] (W : Subgroup G)
    (P : Sylow p W) {h : G} (hh : h ∈ Subgroup.normalizer (W : Set G)) :
    ∃ w ∈ W, w * h ∈
      Subgroup.normalizer (((P : Subgroup W).map W.subtype : Subgroup G) : Set G) := by
  classical
  let φ : MulAut W := W.normalizerMonoidHom ⟨h, hh⟩
  have hφ : ∀ x : W, ((φ x : W) : G) = h * x * h⁻¹ := fun x => rfl
  obtain ⟨w, hw⟩ := MulAction.exists_smul_eq W (φ • P) P
  have hw' : ((w • (φ • P) : Sylow p W) : Subgroup W) = (P : Subgroup W) := by rw [hw]
  rw [Sylow.coe_subgroup_smul, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def,
    Subgroup.pointwise_smul_def] at hw'
  have key : ∀ x : W, x ∈ (P : Subgroup W) ↔ (w * φ x * w⁻¹ : W) ∈ (P : Subgroup W) := by
    intro x
    constructor
    · intro hx
      rw [← hw']
      exact ⟨φ x, ⟨x, hx, rfl⟩, rfl⟩
    · intro hx
      rw [← hw'] at hx
      obtain ⟨y, ⟨x', hx', rfl⟩, hy⟩ := hx
      have h1 : (w * φ x' * w⁻¹ : W) = w * φ x * w⁻¹ := hy
      have h2 : φ x' = φ x := by
        have := congrArg (fun t => w⁻¹ * t * w) h1
        simpa [mul_assoc] using this
      rw [← φ.injective h2]
      exact hx'
  refine ⟨w, w.2, ?_⟩
  rw [Subgroup.mem_normalizer_iff]
  intro g
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨w * φ x * w⁻¹, (key x).mp hx, ?_⟩
    simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv, hφ]
    group
  · rintro ⟨y, hy, hyg⟩
    have hyg' : (y : G) = w * h * g * (w * h)⁻¹ := hyg
    have hgW : g ∈ W := by
      have hy' : (y : G) ∈ W := y.2
      rw [hyg'] at hy'
      have hwh : w * h ∈ Subgroup.normalizer (W : Set G) :=
        mul_mem (Subgroup.le_normalizer w.2) hh
      exact (Subgroup.mem_normalizer_iff.mp hwh g).mpr hy'
    refine ⟨⟨g, hgW⟩, (key ⟨g, hgW⟩).mpr ?_, rfl⟩
    have : (w * φ ⟨g, hgW⟩ * w⁻¹ : W) = y := by
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, hφ]
      rw [hyg']
      group
    rw [this]
    exact hy

omit [Finite G] in
theorem inf_eq_bot_of_not_dvd {p : ℕ} [Fact p.Prime] {P H : Subgroup G} (hP : IsPGroup p P)
    (hH : ¬ p ∣ Nat.card H) : P ⊓ H = ⊥ := by
  have hPH : IsPGroup p (P ⊓ H : Subgroup G) := hP.to_le inf_le_left
  rcases hPH.card_eq_or_dvd with h | h
  · exact Subgroup.eq_bot_of_card_eq _ h
  · exact absurd (h.trans (Subgroup.card_dvd_of_le inf_le_right)) hH

theorem card_comap_of_surjective {G' : Type*} [Group G'] {f : G →* G'}
    (hf : Function.Surjective f) (H : Subgroup G') :
    Nat.card (H.comap f) = Nat.card f.ker * Nat.card H := by
  have : Finite G' := Finite.of_surjective f hf
  have h1 := Subgroup.card_mul_index (H.comap f)
  have h2 := Subgroup.card_mul_index H
  have h3 : Nat.card f.ker * Nat.card f.range = Nat.card G := by
    rw [← Subgroup.index_ker, Subgroup.card_mul_index]
  rw [MonoidHom.range_eq_top.mpr hf, Subgroup.card_top] at h3
  rw [Subgroup.index_comap_of_surjective H hf] at h1
  have hpos : 0 < H.index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have : Nat.card (H.comap f) * H.index = Nat.card f.ker * Nat.card H * H.index := by
    rw [h1, mul_assoc, h2, h3]
  exact Nat.eq_of_mul_eq_mul_right hpos this

end GroupTheory

structure IsCore {K V X Q : Type*} [Field K] [AddCommGroup V] [Module K V] [Group X] [Group Q]
    (σ : X →* Module.End K V) (π : X →* Q) (φ : Q →* projectiveSL 3 (GaloisField 2 2)) :
    Prop where
  finrank_eq : Module.finrank K V = 4
  injective : Function.Injective σ
  det_eq : ∀ x, LinearMap.det (σ x) = 1
  surjective : Function.Surjective π
  odd_ker : Odd (Nat.card π.ker)
  minimal : ∀ H : Subgroup X, H.map π = ⊤ → H = ⊤
  quasisimple : IsQuasisimple Q
  cyclic_center : IsCyclic (Subgroup.center Q)
  card_center : Nat.card (Subgroup.center Q) = 4
  surjective_φ : Function.Surjective φ
  ker_φ : φ.ker = Subgroup.center Q

variable {K V X Q : Type*} [Field K] [AddCommGroup V] [Module K V] [Group X] [Group Q]
  [Finite X] {σ : X →* Module.End K V} {π : X →* Q} {φ : Q →* projectiveSL 3 (GaloisField 2 2)}

namespace IsCore

variable (hC : IsCore σ π φ)
include hC

theorem finite_Q : Finite Q := Finite.of_surjective π hC.surjective

omit [Finite X] in
theorem surjective_comp : Function.Surjective (φ.comp π) :=
  hC.surjective_φ.comp hC.surjective

theorem card_ker_comp : Nat.card (φ.comp π).ker = Nat.card π.ker * 4 := by
  have : Finite Q := hC.finite_Q
  have h : (φ.comp π).ker = (Subgroup.center Q).comap π := by
    rw [← hC.ker_φ]; rfl
  rw [h, card_comap_of_surjective hC.surjective, hC.card_center]

theorem card_Q : Nat.card Q = 4 * 20160 := by
  have : Finite Q := hC.finite_Q
  have h := card_comap_of_surjective hC.surjective_φ (⊤ : Subgroup (projectiveSL 3 _))
  rw [Subgroup.comap_top, Subgroup.card_top, Subgroup.card_top, hC.ker_φ, hC.card_center,
    card_projectiveSL card_galoisField_two_two] at h
  exact h

end IsCore

theorem conj_eq_of_mem_eZero {e x : projectiveSL 3 (GaloisField 2 2)}
    (he : e ∈ eZero (GaloisField 2 2)) (hx : x ∈ eZero (GaloisField 2 2)) : e * x * e⁻¹ = x := by
  rw [commute_of_mem_eZero card_galoisField_two_two he hx, mul_inv_cancel_right]

theorem false_of_not_three_dvd [IsAlgClosed K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hC : IsCore σ π φ) (hN3 : ¬ 3 ∣ Nat.card π.ker) : False := by
  classical
  have hk : Nat.card (GaloisField 2 2) = 4 := card_galoisField_two_two
  obtain ⟨u, hu⟩ := exists_units_ne_one hk
  set ψ := φ.comp π with hψdef
  have hψ : Function.Surjective ψ := hC.surjective_comp
  have hker3 : ¬ 3 ∣ Nat.card ψ.ker := by
    rw [hψdef, hC.card_ker_comp]
    intro h
    rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h | h
    · exact hN3 h
    · norm_num at h
  set E := eZero (GaloisField 2 2) with hE
  set W := E.comap ψ with hW
  have hcardW : Nat.card W = Nat.card ψ.ker * 9 := by
    rw [hW, card_comap_of_surjective hψ, card_eZero hk]
  obtain ⟨R⟩ : Nonempty (Sylow 3 W) := Sylow.nonempty
  set R₀ : Subgroup X := (R : Subgroup W).map W.subtype with hR₀
  have hR₀W : R₀ ≤ W := Subgroup.map_subtype_le _
  have hcardR : Nat.card R₀ = 3 ^ 2 := by
    have hk0 : Nat.card ψ.ker ≠ 0 := Nat.card_pos.ne'
    rw [hR₀, Subgroup.card_map_of_injective W.subtype_injective, Sylow.card_eq_multiplicity,
      hcardW, Nat.factorization_mul hk0 (by norm_num), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hker3, zero_add,
      show (9 : ℕ) = 3 ^ 2 by norm_num, Nat.Prime.factorization_pow Nat.prime_three]
    simp
  have hRp : IsPGroup 3 R₀ := IsPGroup.of_card hcardR
  have hRker : R₀ ⊓ ψ.ker = ⊥ := inf_eq_bot_of_not_dvd hRp hker3
  have hinj : ∀ x ∈ R₀, ∀ y ∈ R₀, ψ x = ψ y → x = y := by
    intro x hx y hy hxy
    have hm : x⁻¹ * y ∈ R₀ ⊓ ψ.ker := Subgroup.mem_inf.mpr ⟨R₀.mul_mem (R₀.inv_mem hx) hy,
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    rw [hRker, Subgroup.mem_bot] at hm
    exact inv_mul_eq_one.mp hm
  have hmapR : R₀.map ψ = E := by
    apply Subgroup.eq_of_le_of_card_ge
    · rintro _ ⟨x, hx, rfl⟩
      exact hR₀W hx
    · have hinj' : Function.Injective (ψ.comp R₀.subtype) := by
        intro x y hxy
        exact Subtype.ext (hinj _ x.2 _ y.2 hxy)
      have h1 : Nat.card ((⊤ : Subgroup R₀).map (ψ.comp R₀.subtype)) = Nat.card R₀ := by
        rw [Subgroup.card_map_of_injective hinj', Subgroup.card_top]
      rw [← Subgroup.map_map, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      rw [h1, hcardR, card_eZero hk]
      norm_num
  have hmemE : ∀ e ∈ E, ∃ x ∈ R₀, ψ x = e := by
    intro e he
    rw [← hmapR] at he
    obtain ⟨x, hx, rfl⟩ := he
    exact ⟨x, hx, rfl⟩
  obtain ⟨a, ha, haψ⟩ := hmemE _ (aP_mem_eZero (u := u))
  obtain ⟨b, hb, hbψ⟩ := hmemE _ (bP_mem_eZero (k := GaloisField 2 2))
  have hlift : ∀ n ∈ Subgroup.normalizer (E : Set (projectiveSL 3 (GaloisField 2 2))),
      ∃ g ∈ Subgroup.normalizer (R₀ : Set X), ∃ e ∈ E, ψ g = e * n := by
    intro n hn
    obtain ⟨h, rfl⟩ := hψ n
    have hhW : h ∈ Subgroup.normalizer (W : Set X) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      simp only [hW, Subgroup.mem_comap, map_mul, map_inv]
      exact Subgroup.mem_normalizer_iff.mp hn (ψ g)
    obtain ⟨w, hw, hwh⟩ := exists_mul_mem_normalizer_of_sylow W R hhW
    exact ⟨w * h, hwh, ψ w, hw, by rw [map_mul]⟩
  obtain ⟨f, hf, ef, hef, hfψ⟩ := hlift (fP hk hu) (fP_mem_normalizer hk hu)
  obtain ⟨j, hj, ej, hej, hjψ⟩ := hlift (jP hk hu) (jP_mem_normalizer hk hu)
  have hconjR : ∀ g ∈ Subgroup.normalizer (R₀ : Set X), ∀ x ∈ R₀, g * x * g⁻¹ ∈ R₀ :=
    fun g hg x hx => (Subgroup.mem_normalizer_iff.mp hg x).mp hx
  have hconjE : ∀ e ∈ E, ∀ n x : projectiveSL 3 (GaloisField 2 2), n * x * n⁻¹ ∈ E →
      (e * n) * x * (e * n)⁻¹ = n * x * n⁻¹ := by
    intro e he n x hx
    rw [show (e * n) * x * (e * n)⁻¹ = e * (n * x * n⁻¹) * e⁻¹ by group,
      conj_eq_of_mem_eZero he hx]
  have ha3 : a ^ 3 = 1 := hinj _ (pow_mem ha 3) _ (one_mem _) (by
    rw [map_pow, haψ, map_one]; exact pow_three_of_mem_eZero hk aP_mem_eZero)
  have hb3 : b ^ 3 = 1 := hinj _ (pow_mem hb 3) _ (one_mem _) (by
    rw [map_pow, hbψ, map_one]; exact pow_three_of_mem_eZero hk bP_mem_eZero)
  have hab : a * b = b * a := hinj _ (mul_mem ha hb) _ (mul_mem hb ha) (by
    rw [map_mul, map_mul, haψ, hbψ]; exact commute_of_mem_eZero hk aP_mem_eZero bP_mem_eZero)
  have r1 : f * a * f⁻¹ = b := hinj _ (hconjR f hf a ha) _ hb (by
    rw [map_mul, map_mul, map_inv, hfψ, haψ, hbψ, hconjE ef hef _ _ (by
      rw [fP_conj_aP hk hu]; exact bP_mem_eZero), fP_conj_aP hk hu])
  have r2 : f * b * f⁻¹ = a⁻¹ := hinj _ (hconjR f hf b hb) _ (inv_mem ha) (by
    rw [map_mul, map_mul, map_inv, map_inv, hfψ, haψ, hbψ, hconjE ef hef _ _ (by
      rw [fP_conj_bP hk hu]; exact inv_mem aP_mem_eZero), fP_conj_bP hk hu])
  have r3 : j * a * j⁻¹ = b * a⁻¹ := hinj _ (hconjR j hj a ha) _ (mul_mem hb (inv_mem ha)) (by
    rw [map_mul, map_mul, map_inv, map_mul, map_inv, hjψ, haψ, hbψ, hconjE ej hej _ _ (by
      rw [jP_conj_aP hk hu]; exact mul_mem bP_mem_eZero (inv_mem aP_mem_eZero)), jP_conj_aP hk hu])
  have r4 : j * b * j⁻¹ = a⁻¹ * b * a⁻¹ :=
    hinj _ (hconjR j hj b hb) _ (mul_mem (mul_mem (inv_mem ha) hb) (inv_mem ha)) (by
      rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv, hjψ, haψ, hbψ, hconjE ej hej _ _
        (by rw [jP_conj_bP hk hu]
            exact mul_mem (mul_mem (inv_mem aP_mem_eZero) bP_mem_eZero) (inv_mem aP_mem_eZero)),
        jP_conj_bP hk hu])
  have hainv : a⁻¹ = a ^ 2 := by
    rw [eq_comm, ← mul_eq_one_iff_eq_inv, ← pow_succ, ha3]
  have hAF : σ a * σ f⁻¹ = σ f⁻¹ * σ b := by
    rw [← map_mul, ← map_mul, ← r1]; group
  have hBF : σ b * σ f⁻¹ = σ f⁻¹ * σ a ^ 2 := by
    rw [← map_mul, ← map_pow, ← map_mul, ← hainv, ← r2]; group
  have hAJ : σ a * σ j⁻¹ = σ j⁻¹ * (σ b * σ a ^ 2) := by
    rw [← map_pow, ← map_mul, ← map_mul, ← map_mul, ← hainv, ← r3]; group
  have hab' : a⁻¹ * b * a⁻¹ = a * b := by
    have hba : b * a⁻¹ = a⁻¹ * b := by
      rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hab, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [mul_assoc, hba, ← mul_assoc, ← sq, hainv, ← pow_mul,
      show a ^ (2 * 2) = a ^ 3 * a by rw [← pow_succ], ha3, one_mul]
  have hBJ : σ b * σ j⁻¹ = σ j⁻¹ * (σ a * σ b) := by
    rw [← map_mul, ← map_mul, ← map_mul, ← hab', ← r4]; group
  have hA1 := eq_one_of_weights h3 hC.finrank_eq.le (A := σ a) (B := σ b) (F := σ f⁻¹)
    (J := σ j⁻¹) (by rw [← map_pow, ha3, map_one]) (by rw [← map_pow, hb3, map_one])
    (by rw [← map_mul, ← map_mul, hab]) (Res5L34.injective_of_group σ _)
    (Res5L34.injective_of_group σ _) hAF hBF hAJ hBJ
  have ha1 : a = 1 := hC.injective (by rw [hA1, map_one])
  apply aP_ne_one hk hu
  rw [← haψ, ha1, map_one]


theorem false_of_rep [IsAlgClosed K] (h2 : (2 : K) ≠ 0) (hC : IsCore σ π φ) {W : Type*}
    [AddCommGroup W] [Module K W] [FiniteDimensional K W] (hW : Module.finrank K W ≤ 3)
    (ρ : X →* Module.End K W) (hρ : ρ.ker.map π ≤ Subgroup.center Q) : False := by
  classical
  have : Finite Q := hC.finite_Q
  have hk : Nat.card (GaloisField 2 2) = 4 := card_galoisField_two_two
  have : CharP (GaloisField 2 2) 2 := LinearFieldFour.charP_two_of_card_eq_four hk
  set ψ := φ.comp π with hψdef
  have hψ : Function.Surjective ψ := hC.surjective_comp
  set E := eOne (GaloisField 2 2) with hE
  have hcardE : Nat.card E = 16 := by rw [hE, card_eOne, hk]
  set W₁ := E.comap ψ with hW₁
  have hcardW : Nat.card W₁ = Nat.card ψ.ker * 16 := by
    rw [hW₁, card_comap_of_surjective hψ, hcardE]
  obtain ⟨F₀⟩ : Nonempty (Sylow 2 W₁) := Sylow.nonempty
  set F : Subgroup X := (F₀ : Subgroup W₁).map W₁.subtype with hFdef
  have hFW : F ≤ W₁ := Subgroup.map_subtype_le _
  have hNodd : ¬ 2 ∣ Nat.card π.ker := by
    rw [← even_iff_two_dvd, Nat.not_even_iff_odd]; exact hC.odd_ker
  have hcardF : Nat.card F = 2 ^ 6 := by
    have hk0 : Nat.card π.ker ≠ 0 := Nat.card_pos.ne'
    rw [hFdef, Subgroup.card_map_of_injective W₁.subtype_injective, Sylow.card_eq_multiplicity,
      hcardW, hψdef, hC.card_ker_comp, Nat.factorization_mul (mul_ne_zero hk0 (by norm_num))
        (by norm_num), Nat.factorization_mul hk0 (by norm_num), Finsupp.add_apply,
      Finsupp.add_apply, Nat.factorization_eq_zero_of_not_dvd hNodd, zero_add,
      show (4 : ℕ) = 2 ^ 2 by norm_num, show (16 : ℕ) = 2 ^ 4 by norm_num,
      Nat.Prime.factorization_pow Nat.prime_two, Nat.Prime.factorization_pow Nat.prime_two]
    simp
  have hFp : IsPGroup 2 F := IsPGroup.of_card hcardF
  have hFN : F ⊓ π.ker = ⊥ := inf_eq_bot_of_not_dvd hFp hNodd
  have hπinj : ∀ x ∈ F, ∀ y ∈ F, π x = π y → x = y := by
    intro x hx y hy hxy
    have hm : x⁻¹ * y ∈ F ⊓ π.ker := Subgroup.mem_inf.mpr ⟨F.mul_mem (F.inv_mem hx) hy,
      MonoidHom.mem_ker.mpr (by rw [map_mul, map_inv, hxy, inv_mul_cancel])⟩
    rw [hFN, Subgroup.mem_bot] at hm
    exact inv_mul_eq_one.mp hm
  let ψF : F →* projectiveSL 3 (GaloisField 2 2) := ψ.comp F.subtype
  set C := ψF.ker with hCdef
  have hψFE : ∀ x : F, ψF x ∈ E := fun x => hFW x.2
  have hπC : ∀ c ∈ C, π c ∈ Subgroup.center Q := by
    intro c hc
    rw [← hC.ker_φ]
    exact hc
  have hCc : C ≤ Subgroup.center F := by
    intro c hc
    rw [Subgroup.mem_center_iff]
    intro g
    apply Subtype.ext
    apply hπinj _ (F.mul_mem g.2 c.2) _ (F.mul_mem c.2 g.2)
    simp only [map_mul]
    exact Subgroup.mem_center_iff.mp (hπC c hc) (π g)
  have hCcyc : IsCyclic C := by
    have : IsCyclic (Subgroup.center Q) := hC.cyclic_center
    let f : C →* Subgroup.center Q :=
      { toFun := fun c => ⟨π c, hπC c c.2⟩
        map_one' := by ext; simp
        map_mul' := fun a b => by ext; simp }
    refine isCyclic_of_injective f ?_
    intro a b hab
    have h' : π (a : F) = π (b : F) := congrArg Subtype.val hab
    exact Subtype.ext (Subtype.ext (hπinj _ (a : F).2 _ (b : F).2 h'))
  have hcardC : Nat.card C ≤ 4 := by
    let f : C → Subgroup.center Q := fun c => ⟨π c, hπC c c.2⟩
    have hf : Function.Injective f := by
      intro a b hab
      have h' : π (a : F) = π (b : F) := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext (hπinj _ (a : F).2 _ (b : F).2 h'))
    have := Nat.card_le_card_of_injective f hf
    rwa [hC.card_center] at this
  have hsq : ∀ x : F, x ^ 2 ∈ C := by
    intro x
    rw [hCdef, MonoidHom.mem_ker, map_pow]
    exact sq_eq_one_of_mem_eOne (hψFE x)
  have hcomm : ∀ x y : F, x * y * x⁻¹ * y⁻¹ ∈ C := by
    intro x y
    rw [hCdef, MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv,
      commute_of_mem_eOne (hψFE x) (hψFE y)]
    group
  have hcard : 16 * Nat.card C ≤ Nat.card F := by
    rw [hcardF]; omega
  have hZ : (∀ x y : F, x * y = y * x) ∨ Subgroup.center F ≤ C := by
    by_cases hZc : (Subgroup.center F).map ψF = ⊥
    · right
      intro x hx
      have : ψF x ∈ (Subgroup.center F).map ψF := ⟨x, hx, rfl⟩
      rw [hZc, Subgroup.mem_bot] at this
      exact this
    · left
      obtain ⟨⟨r, hr⟩, hr1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hZc
      obtain ⟨c₀, hc₀, hc₀r⟩ := hr
      have hall : ∀ s ∈ E, s ∈ (Subgroup.center F).map ψF := by
        intro s hs
        by_cases hs1 : s = 1
        · rw [hs1]; exact one_mem _
        obtain ⟨n, hn, hns⟩ := exists_conj_eq_of_mem_eOne (hψFE c₀) hs
          (by rw [hc₀r]; exact fun h => hr1 (Subtype.ext h)) hs1
        obtain ⟨h, rfl⟩ := hψ n
        have hhW : h ∈ Subgroup.normalizer (W₁ : Set X) := by
          rw [Subgroup.mem_normalizer_iff]
          intro g
          simp only [hW₁, Subgroup.mem_comap, map_mul, map_inv]
          exact Subgroup.mem_normalizer_iff.mp hn (ψ g)
        obtain ⟨w, hw, hwh⟩ := exists_mul_mem_normalizer_of_sylow W₁ F₀ hhW
        set g := w * h with hg
        have hgc : g * (c₀ : X) * g⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hwh _).mp c₀.2
        refine ⟨⟨_, hgc⟩, ?_, ?_⟩
        · rw [SetLike.mem_coe, Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          have hy : g⁻¹ * (y : X) * g ∈ F := by
            have := (Subgroup.mem_normalizer_iff.mp (inv_mem hwh) y).mp y.2
            rwa [inv_inv] at this
          have hcy := Subgroup.mem_center_iff.mp hc₀ ⟨_, hy⟩
          have hcy' : (g⁻¹ * (y : X) * g) * (c₀ : X) = (c₀ : X) * (g⁻¹ * (y : X) * g) :=
            congrArg Subtype.val hcy
          simp only [Subgroup.coe_mul]
          calc (y : X) * (g * c₀ * g⁻¹) = g * ((g⁻¹ * y * g) * c₀) * g⁻¹ := by group
            _ = g * (c₀ * (g⁻¹ * y * g)) * g⁻¹ := by rw [hcy']
            _ = g * c₀ * g⁻¹ * y := by group
        · rw [← hns]
          show ψ (g * (c₀ : X) * g⁻¹) = ψ h * ψF c₀ * (ψ h)⁻¹
          rw [map_mul, map_mul, map_inv, hg, map_mul,
            show ψ (c₀ : X) = ψF c₀ from rfl]
          have hc₀E := hψFE c₀
          have hwE : ψ w ∈ E := hw
          have hmid : ψ h * ψF c₀ * (ψ h)⁻¹ ∈ E := by rw [hns]; exact hs
          calc ψ w * ψ h * ψF c₀ * (ψ w * ψ h)⁻¹ =
              ψ w * (ψ h * ψF c₀ * (ψ h)⁻¹) * (ψ w)⁻¹ := by group
            _ = ψ h * ψF c₀ * (ψ h)⁻¹ := by
              rw [commute_of_mem_eOne hwE hmid, mul_inv_cancel_right]
      intro x y
      obtain ⟨c, hc, hcx⟩ := hall _ (hψFE x)
      have hxc : c⁻¹ * x ∈ C := by
        rw [hCdef, MonoidHom.mem_ker, map_mul, map_inv, hcx, inv_mul_cancel]
      have hxZ : x ∈ Subgroup.center F := by
        have := mul_mem hc (hCc hxc)
        rwa [mul_inv_cancel_left] at this
      exact (Subgroup.mem_center_iff.mp hxZ y).symm
  have hker : (ρ.comp F.subtype).ker ≤ C := by
    intro x hx
    have hx' : (x : X) ∈ ρ.ker := hx
    have hπx : π x ∈ Subgroup.center Q := hρ ⟨x, hx', rfl⟩
    rw [hCdef, MonoidHom.mem_ker]
    show φ (π x) = 1
    rw [← MonoidHom.mem_ker, hC.ker_φ]
    exact hπx
  exact false_of_twoLocal h2 hW (ρ.comp F.subtype) C hCc hCcyc hsq hcomm hcard hZ hker


theorem eq_of_three_pow_modEq_seven {a b : ℕ} (ha : a ≤ 4) (hba : b ≤ a)
    (h : 3 ^ a ≡ 3 ^ b [MOD 7]) : a = b := by
  interval_cases a <;> interval_cases b <;> simp_all [Nat.ModEq]

theorem exists_central_of_three_dvd [IsAlgClosed K] [FiniteDimensional K V] (h3 : (3 : K) ≠ 0)
    (hC : IsCore σ π φ) (hN3 : 3 ∣ Nat.card π.ker) :
    ∃ z : X, z ≠ 1 ∧ z ^ 3 = 1 ∧ z ∈ Subgroup.center X := by
  classical
  have : Finite Q := hC.finite_Q
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  set N := π.ker with hNdef
  obtain ⟨P⟩ : Nonempty (Sylow 3 N) := Sylow.nonempty
  set P₀ : Subgroup X := (P : Subgroup N).map N.subtype with hP₀
  have hP₀p : IsPGroup 3 P₀ := P.isPGroup'.map N.subtype
  have hP₀n : P₀.Normal := by
    have hsup := Sylow.normalizer_sup_eq_top (p := 3) (N := N) P
    have hmap : (Subgroup.normalizer (P₀ : Set X)).map π = ⊤ := by
      have := congrArg (Subgroup.map π) hsup
      rw [Subgroup.map_sup, Subgroup.map_top_of_surjective π hC.surjective,
        (Subgroup.map_eq_bot_iff _).mpr le_rfl, sup_bot_eq] at this
      exact this
    exact Subgroup.normalizer_eq_top_iff.mp (hC.minimal _ hmap)
  have hP₀3 : 3 ∣ Nat.card P₀ := by
    have hne := Sylow.ne_bot_of_dvd_card P hN3
    have hne' : P₀ ≠ ⊥ := by
      rw [hP₀]
      intro h
      apply hne
      rwa [Subgroup.map_eq_bot_iff_of_injective _ N.subtype_injective] at h
    rcases hP₀p.card_eq_or_dvd with h | h
    · exact absurd (Subgroup.eq_bot_of_card_eq _ h) hne'
    · exact h
  let Z : Subgroup X :=
    { carrier := {x | x ∈ P₀ ∧ x ∈ Subgroup.centralizer (P₀ : Set X) ∧ x ^ 3 = 1}
      one_mem' := ⟨one_mem _, one_mem _, one_pow 3⟩
      mul_mem' := by
        rintro x y ⟨hx, hxc, hx3⟩ ⟨hy, hyc, hy3⟩
        refine ⟨mul_mem hx hy, mul_mem hxc hyc, ?_⟩
        have hxy : Commute x y := (Subgroup.mem_centralizer_iff.mp hxc y hy).symm
        rw [hxy.mul_pow, hx3, hy3, one_mul]
      inv_mem' := by
        rintro x ⟨hx, hxc, hx3⟩
        exact ⟨inv_mem hx, inv_mem hxc, by rw [inv_pow, hx3, inv_one]⟩ }
  have hZmem : ∀ x, x ∈ Z ↔ x ∈ P₀ ∧ x ∈ Subgroup.centralizer (P₀ : Set X) ∧ x ^ 3 = 1 :=
    fun x => Iff.rfl
  have hZcomm : ∀ x ∈ Z, ∀ y ∈ Z, x * y = y * x := by
    intro x hx y hy
    exact (Subgroup.mem_centralizer_iff.mp ((hZmem x).mp hx).2.1 y ((hZmem y).mp hy).1).symm
  have hZn : Z.Normal := ⟨by
    intro x hx g
    obtain ⟨hx, hxc, hx3⟩ := (hZmem x).mp hx
    refine (hZmem _).mpr ⟨hP₀n.conj_mem x hx g, ?_, by rw [conj_pow, hx3, mul_one,
      mul_inv_cancel]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : g⁻¹ * q * g ∈ P₀ := by
      have := hP₀n.conj_mem q hq g⁻¹
      simpa using this
    have := Subgroup.mem_centralizer_iff.mp hxc _ hq'
    calc q * (g * x * g⁻¹) = g * ((g⁻¹ * q * g) * x) * g⁻¹ := by group
      _ = g * (x * (g⁻¹ * q * g)) * g⁻¹ := by rw [this]
      _ = g * x * g⁻¹ * q := by group⟩
  obtain ⟨z₀, hz₀⟩ : ∃ z₀ : X, z₀ ∈ Z ∧ z₀ ≠ 1 := by
    have : Nontrivial P₀ := by
      rw [← Finite.one_lt_card_iff_nontrivial]
      exact lt_of_lt_of_le (by norm_num) (Nat.le_of_dvd Nat.card_pos hP₀3)
    have hcen := hP₀p.center_nontrivial
    have : Fintype (Subgroup.center P₀) := Fintype.ofFinite _
    have h3c : 3 ∣ Fintype.card (Subgroup.center P₀) := by
      rw [← Nat.card_eq_fintype_card]
      rcases (hP₀p.to_subgroup (Subgroup.center P₀)).card_eq_or_dvd with h | h
      · exact absurd h (Finite.one_lt_card_iff_nontrivial.mpr hcen).ne'
      · exact h
    obtain ⟨c, hc⟩ := exists_prime_orderOf_dvd_card 3 h3c
    refine ⟨((c : P₀) : X), (hZmem _).mpr ⟨(c : P₀).2, ?_, ?_⟩, ?_⟩
    · rw [Subgroup.mem_centralizer_iff]
      intro q hq
      have := Subgroup.mem_center_iff.mp c.2 ⟨q, hq⟩
      exact congrArg Subtype.val this
    · have : (c : P₀) ^ 3 = 1 := by
        have := pow_orderOf_eq_one c
        rw [hc] at this
        exact congrArg Subtype.val this
      exact congrArg Subtype.val this
    · intro h
      have hc1 : c = 1 := Subtype.ext (Subtype.ext h)
      rw [hc1, orderOf_one] at hc
      norm_num at hc
  have hZcard : Nat.card Z ≤ 3 ^ 4 := by
    let _ : CommGroup Z :=
      { (inferInstance : Group Z) with
        mul_comm := fun x y => Subtype.ext (hZcomm x x.2 y y.2) }
    have h := card_le_pow_finrank (K := K) (V := V) (n := 3) (by norm_num) (by exact_mod_cast h3)
      (σ.comp Z.subtype) (hC.injective.comp Z.subtype_injective)
      (fun x => Subtype.ext ((hZmem _).mp x.2).2.2)
    rwa [hC.finrank_eq] at h
  obtain ⟨S⟩ : Nonempty (Sylow 7 X) := Sylow.nonempty
  have hSZ : (S : Subgroup X) ≤ Subgroup.centralizer (Z : Set X) := by
    let _ : MulAction S Z := MulAction.compHom Z ((MulAut.conjNormal (H := Z)).comp S.1.subtype)
    have hact : ∀ (s : S) (x : Z), ((s • x : Z) : X) = s * x * (s : X)⁻¹ := by
      intro s x
      exact MulAut.conjNormal_apply _ _
    have hcong := IsPGroup.card_modEq_card_fixedPoints S.isPGroup' (p := 7) Z
    let Fx : Subgroup X := Z ⊓ Subgroup.centralizer (S : Set X)
    have hfix : Nat.card (MulAction.fixedPoints S Z) = Nat.card Fx := by
      refine Nat.card_congr
        { toFun := fun x => ⟨x.1.1, x.1.2, Subgroup.mem_centralizer_iff.mpr fun s hs => ?_⟩
          invFun := fun x => ⟨⟨x.1, x.2.1⟩, fun s => ?_⟩
          left_inv := fun x => rfl
          right_inv := fun x => rfl }
      · have := congrArg Subtype.val (x.2 ⟨s, hs⟩)
        rw [hact] at this
        calc s * (x.1 : X) = (s * x.1 * s⁻¹) * s := by group
          _ = x.1 * s := by rw [this]
      · apply Subtype.ext
        rw [hact]
        have := Subgroup.mem_centralizer_iff.mp x.2.2 s s.2
        calc (s : X) * x.1 * (s : X)⁻¹ = x.1 * s * (s : X)⁻¹ := by rw [this]
          _ = x.1 := by group
    have hZp : IsPGroup 3 Z := hP₀p.to_le fun x hx => ((hZmem x).mp hx).1
    obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hZp
    have hFxZ : Nat.card Fx ∣ Nat.card Z := Subgroup.card_dvd_of_le inf_le_left
    rw [ha, Nat.dvd_prime_pow Nat.prime_three] at hFxZ
    obtain ⟨b, hba, hb⟩ := hFxZ
    have ha4 : a ≤ 4 := by
      by_contra h
      have : 3 ^ 5 ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [← ha] at this
      have := hZcard
      omega
    rw [hfix, ha, hb] at hcong
    have hab := eq_of_three_pow_modEq_seven ha4 hba hcong
    have hFxeq : Fx = Z := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [ha, hb, hab])
    intro s hs
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : x ∈ Fx := hFxeq ▸ hx
    exact (Subgroup.mem_centralizer_iff.mp hx'.2 s hs).symm
  have hD : Subgroup.centralizer (Z : Set X) = ⊤ := by
    apply hC.minimal
    have hDn : (Subgroup.centralizer (Z : Set X)).Normal := Subgroup.normal_centralizer
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hC.quasisimple
      (hDn.map π hC.surjective) with h | h
    · exact h
    · exfalso
      let S' : Sylow 7 Q := S.mapSurjective hC.surjective
      have h7 : 7 ∣ Nat.card Q := by rw [hC.card_Q]; norm_num
      have hS' : (S' : Subgroup Q) ≠ ⊥ := Sylow.ne_bot_of_dvd_card S' h7
      have hS'Z : (S' : Subgroup Q) ≤ Subgroup.center Q := by
        intro q hq
        apply h
        obtain ⟨s, hs, rfl⟩ := hq
        exact ⟨s, hSZ hs, rfl⟩
      have hdvd : Nat.card (S' : Subgroup Q) ∣ 4 := by
        rw [← hC.card_center]; exact Subgroup.card_dvd_of_le hS'Z
      rcases S'.isPGroup'.card_eq_or_dvd with h1 | h1
      · exact hS' (Subgroup.eq_bot_of_card_eq _ h1)
      · have := h1.trans hdvd
        norm_num at this
  refine ⟨z₀, hz₀.2, ((hZmem _).mp hz₀.1).2.2, ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ Subgroup.centralizer (Z : Set X) := hD ▸ Subgroup.mem_top g
  exact (Subgroup.mem_centralizer_iff.mp hg z₀ hz₀.1).symm


theorem false_of_central [IsAlgClosed K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) (hC : IsCore σ π φ) {z : X} (hz1 : z ≠ 1) (hz3 : z ^ 3 = 1)
    (hzc : z ∈ Subgroup.center X) : False := by
  classical
  have : Finite Q := hC.finite_Q
  have hss : (σ z).IsSemisimple := isSemisimple_of_pow_eq_one (n := 3) (by exact_mod_cast h3)
    (by rw [← map_pow, hz3, map_one])
  have htop := hss.iSup_eigenspace_eq_top
  have hinv : ∀ μ : K, ∀ g : X, ∀ v ∈ (σ z).eigenspace μ, σ g v ∈ (σ z).eigenspace μ := by
    intro μ g v hv
    rw [Module.End.mem_eigenspace_iff] at hv ⊢
    rw [← Module.End.mul_apply, ← map_mul, ← Subgroup.mem_center_iff.mp hzc g, map_mul,
      Module.End.mul_apply, hv, map_smul]
  have hnt : ∀ μ : K, (σ z).eigenspace μ ≠ ⊤ := by
    intro μ hμ
    have hzμ : σ z = μ • 1 := by
      apply LinearMap.ext
      intro v
      have hv : v ∈ (σ z).eigenspace μ := by rw [hμ]; exact Submodule.mem_top
      rw [Module.End.mem_eigenspace_iff.mp hv]
      simp
    have hdet := hC.det_eq z
    rw [hzμ, LinearMap.det_smul, map_one, mul_one, hC.finrank_eq] at hdet
    have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (n := 3) hC.finrank_eq
    obtain ⟨v, hv⟩ := exists_ne (0 : V)
    have h3v := pow_apply_of_apply_eq_smul (show σ z v = μ • v by rw [hzμ]; simp) 3
    rw [← map_pow, hz3, map_one, Module.End.one_apply] at h3v
    have hμ3 : μ ^ 3 = 1 := by
      have h' : (μ ^ 3 - 1) • v = 0 := by rw [sub_smul, ← h3v, one_smul, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp h').resolve_right hv)
    have hμ1 : μ = 1 := by
      have e : μ ^ 4 = μ ^ 3 * μ := pow_succ μ 3
      rw [hdet, hμ3, one_mul] at e
      exact e.symm
    apply hz1
    apply hC.injective
    rw [hzμ, hμ1, one_smul, map_one]
  have hex : ∃ μ : K, (σ z).eigenspace μ ≠ ⊥ ∧
      (restrictHom σ _ (hinv μ)).ker.map π ≠ ⊤ := by
    by_contra hno
    push Not at hno
    have hall : ∀ g : X, σ g = 1 := by
      intro g
      apply LinearMap.ext
      intro v
      have hv : v ∈ ⨆ μ, (σ z).eigenspace μ := by rw [htop]; exact Submodule.mem_top
      refine Submodule.iSup_induction _ (motive := fun v => σ g v = (1 : Module.End K V) v) hv
        ?_ ?_ ?_
      · intro μ w hw
        by_cases hμ : (σ z).eigenspace μ = ⊥
        · rw [hμ, Submodule.mem_bot] at hw
          simp [hw]
        · have hK := hC.minimal _ (hno μ hμ)
          have hg : g ∈ (restrictHom σ _ (hinv μ)).ker := hK ▸ Subgroup.mem_top g
          have := congrArg (fun T => ((T ⟨w, hw⟩ : (σ z).eigenspace μ) : V))
            (MonoidHom.mem_ker.mp hg)
          simpa [restrictHom_apply_coe] using this
      · simp
      · intro x y hx hy
        simp only [map_add, hx, hy]
    have hX : ∀ g : X, g = 1 := fun g => hC.injective (by rw [hall g, map_one])
    have hQnt := CFSG.LocalCores.isQuasisimple_nontrivial hC.quasisimple
    obtain ⟨q, hq⟩ := exists_ne (1 : Q)
    obtain ⟨g, rfl⟩ := hC.surjective q
    exact hq (by rw [hX g, map_one])
  obtain ⟨μ, -, hμK⟩ := hex
  set ρ := restrictHom σ ((σ z).eigenspace μ) (hinv μ)
  have hKn : (ρ.ker.map π).Normal := (MonoidHom.normal_ker ρ).map π hC.surjective
  have hρ : ρ.ker.map π ≤ Subgroup.center Q :=
    (CFSG.LocalCores.quasisimple_normal_subgroups hC.quasisimple hKn).resolve_left hμK
  have hdim : Module.finrank K ((σ z).eigenspace μ) ≤ 3 := by
    have := Submodule.finrank_lt (hnt μ)
    rw [hC.finrank_eq] at this
    omega
  exact false_of_rep h2 hC hdim ρ hρ

theorem false_of_core [IsAlgClosed K] [FiniteDimensional K V] (h2 : (2 : K) ≠ 0)
    (h3 : (3 : K) ≠ 0) (hC : IsCore σ π φ) : False := by
  by_cases hN3 : 3 ∣ Nat.card π.ker
  · obtain ⟨z, hz1, hz3, hzc⟩ := exists_central_of_three_dvd h3 hC hN3
    exact false_of_central h2 h3 hC hz1 hz3 hzc
  · exact false_of_not_three_dvd h3 hC hN3


end Res5L34

open Res5L34 in
theorem fourL34NotSLFourOdd_holds : FourL34NotSLFourOdd := by
  intro p _ hp5 X _ _ ρ N _ hNodd hker hq hcyc hZ4
  refine ⟨fun e => ?_⟩
  classical
  let K := AlgebraicClosure (ZMod p)
  have hcast : ∀ m : ℕ, 0 < m → m < p → (m : K) ≠ 0 := by
    intro m hm hmp h
    have := (CharP.cast_eq_zero_iff K p m).mp h
    exact absurd (Nat.le_of_dvd hm this) (by omega)
  have h2 : (2 : K) ≠ 0 := by exact_mod_cast hcast 2 (by norm_num) (by omega)
  have h3 : (3 : K) ≠ 0 := by exact_mod_cast hcast 3 (by norm_num) (by omega)
  let ι : Matrix.SpecialLinearGroup (Fin 4) (ZMod p) →* Module.End K (Fin 4 → K) :=
    (Matrix.toLinAlgEquiv' : Matrix (Fin 4) (Fin 4) K ≃ₐ[K] _).toAlgHom.toRingHom.toMonoidHom.comp
      ((algebraMap (ZMod p) K).mapMatrix.toMonoidHom.comp
        Matrix.SpecialLinearGroup.coeMonoidHom)
  have hι : Function.Injective ι := by
    intro g h hgh
    have h1 := Matrix.toLinAlgEquiv'.injective hgh
    have h2' : (g : Matrix (Fin 4) (Fin 4) (ZMod p)) = h :=
      Matrix.map_injective (algebraMap (ZMod p) K).injective h1
    exact Subtype.ext h2'
  have hιdet : ∀ g, LinearMap.det (ι g) = 1 := by
    intro g
    show LinearMap.det (Matrix.toLin' ((algebraMap (ZMod p) K).mapMatrix
      (g : Matrix (Fin 4) (Fin 4) (ZMod p)))) = 1
    rw [LinearMap.det_toLin', ← RingHom.map_det, g.2, map_one]
  let σ' : (X ⧸ ρ.ker) →* Module.End K (Fin 4 → K) := ι.comp (QuotientGroup.kerLift ρ)
  have hσ' : Function.Injective σ' := hι.comp (QuotientGroup.kerLift_injective ρ)
  let π' : (X ⧸ ρ.ker) →* X ⧸ N := QuotientGroup.lift ρ.ker (QuotientGroup.mk' N) (by
    intro x hx
    rw [MonoidHom.mem_ker, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hker hx)
  have hπ' : Function.Surjective π' :=
    QuotientGroup.lift_surjective_of_surjective _ _ (QuotientGroup.mk'_surjective N) _
  have hπ'odd : Odd (Nat.card π'.ker) := by
    have e1 : Nat.card ρ.ker * Nat.card (X ⧸ ρ.ker) = Nat.card X := by
      rw [mul_comm]; exact (Subgroup.card_eq_card_quotient_mul_card_subgroup ρ.ker).symm
    have e2 : Nat.card N * Nat.card (X ⧸ N) = Nat.card X := by
      rw [mul_comm]; exact (Subgroup.card_eq_card_quotient_mul_card_subgroup N).symm
    have e3 : Nat.card π'.ker * Nat.card (X ⧸ N) = Nat.card (X ⧸ ρ.ker) := by
      have := Subgroup.card_mul_index π'.ker
      rwa [Subgroup.index_ker, MonoidHom.range_eq_top.mpr hπ', Subgroup.card_top] at this
    have hpos : 0 < Nat.card (X ⧸ N) := Nat.card_pos
    have e4 : Nat.card N = Nat.card ρ.ker * Nat.card π'.ker := by
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [e2, mul_assoc, e3, e1]
    exact hNodd.of_dvd_nat ⟨_, e4.trans (mul_comm _ _)⟩
  have hex : ∃ n, ∃ H : Subgroup (X ⧸ ρ.ker), H.map π' = ⊤ ∧ Nat.card H = n :=
    ⟨_, ⊤, by rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr hπ'], rfl⟩
  obtain ⟨X₀, hX₀, hX₀card⟩ := Nat.find_spec hex
  let σ₀ : X₀ →* Module.End K (Fin 4 → K) := σ'.comp X₀.subtype
  let π₀ : X₀ →* X ⧸ N := π'.comp X₀.subtype
  let φ : X ⧸ N →* CFSG.LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 3
      (GaloisField 2 2) :=
    (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)).toMonoidHom.comp
      (e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center (X ⧸ N))))
  have hC : IsCore σ₀ π₀ φ :=
    { finrank_eq := Module.finrank_fin_fun K
      injective := hσ'.comp X₀.subtype_injective
      det_eq := fun x => hιdet _
      surjective := by
        intro q
        have hq' : q ∈ X₀.map π' := by rw [hX₀]; exact Subgroup.mem_top q
        obtain ⟨x, hx, rfl⟩ := hq'
        exact ⟨⟨x, hx⟩, rfl⟩
      odd_ker := by
        refine hπ'odd.of_dvd_nat ?_
        have hle : π₀.ker.map X₀.subtype ≤ π'.ker := by
          rintro _ ⟨x, hx, rfl⟩
          exact hx
        have := Subgroup.card_dvd_of_le hle
        rwa [Subgroup.card_map_of_injective X₀.subtype_injective] at this
      minimal := by
        intro H hH
        have hH' : (H.map X₀.subtype).map π' = ⊤ := by rw [Subgroup.map_map]; exact hH
        have hle := Nat.find_min' hex ⟨_, hH', rfl⟩
        rw [← hX₀card, Subgroup.card_map_of_injective X₀.subtype_injective] at hle
        exact (Subgroup.card_eq_iff_eq_top H).mp
          (le_antisymm (Subgroup.card_le_card_group H) hle)
      quasisimple := hq
      cyclic_center := hcyc
      card_center := hZ4
      surjective_φ := by
        intro y
        obtain ⟨q, rfl⟩ := (CFSG.RankThree.PartTwo.KFacts.L34.projSLEquivProjectiveSL 3
          (GaloisField 2 2)).surjective y
        obtain ⟨q', rfl⟩ := e.surjective q
        obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q'
        exact ⟨x, rfl⟩
      ker_φ := by
        ext x
        simp only [φ, MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
          MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] }
  exact false_of_core h2 h3 hC

end CFSG.RankThree.PartTwo.Sec4.Census
