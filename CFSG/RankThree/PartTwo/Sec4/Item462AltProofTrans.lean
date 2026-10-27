module

public import CFSG.RankThree.PartTwo.Sec4.Item462AltProofSetup
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.GroupTheory.ThetaQuotientTransport
import CFSG.RankThree.PartTwo.KFacts.K71Lift
public import CFSG.RankThree.PartTwo.Sec4.Item462ProofD
public import CFSG.RankThree.PartTwo.Sec4.Item462ProofUL

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item462AltProof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem exists_eq_of_mem_A {A B D : Subgroup G} {a b : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (haB : a ∈ B) (hbB : b ∈ B) (hba : b ∉ Subgroup.zpowers a) (hBA : B ≤ A)
    (hB9 : Nat.card B = 9) (hDA : D ≤ A) (hBDA : B ⊔ D = A) {x : G} (hx : x ∈ A) :
    ∃ (i j : ℤ) (d : G), d ∈ D ∧ x = a ^ i * b ^ j * d := by
  have hcomm : ∀ y ∈ A, ∀ z ∈ A, y * z = z * y := fun y hy z hz =>
    congrArg Subtype.val (hAe.1.1.comm ⟨y, hy⟩ ⟨z, hz⟩)
  have hBab : B = Subgroup.zpowers a ⊔ Subgroup.zpowers b := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr haB)
      (Subgroup.zpowers_le.mpr hbB)) ?_
    have hab : a ∉ Subgroup.zpowers b := by
      intro h
      apply hba
      have hb3 : b ^ 3 = 1 := hAe.2 b (hBA hbB)
      have hb1 : b ≠ 1 := fun h1 => hba (h1 ▸ Subgroup.one_mem _)
      have hbo : orderOf b = 3 := orderOf_eq_prime hb3 hb1
      have hzb : Subgroup.zpowers a ≤ Subgroup.zpowers b := Subgroup.zpowers_le.mpr h
      have heq : Subgroup.zpowers a = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge hzb (by rw [Nat.card_zpowers, Nat.card_zpowers, ha3, hbo])
      rw [heq]
      exact Subgroup.mem_zpowers b
    rw [sup_comm, Item462Proof.card_sup_zpowers_of_not_mem haZ ha3 hab, hB9]
    have hb3 : b ^ 3 = 1 := hAe.2 b (hBA hbB)
    have hb1 : b ≠ 1 := fun h1 => hba (h1 ▸ Subgroup.one_mem _)
    rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZ)
  have hBN : B ≤ Subgroup.normalizer (D : Set G) := fun y hy =>
    Subgroup.mem_normalizer_iff.mpr fun d => by
      constructor
      · intro hd
        rw [hcomm y (hBA hy) d (hDA hd), mul_inv_cancel_right]
        exact hd
      · intro hd
        have hdA : y * d * y⁻¹ ∈ A := hDA hd
        have : d = y * d * y⁻¹ := by
          have h1 : d ∈ A := by
            have := A.mul_mem (A.mul_mem (A.inv_mem (hBA hy)) hdA) (hBA hy)
            rwa [show y⁻¹ * (y * d * y⁻¹) * y = d by group] at this
          rw [hcomm y (hBA hy) d h1, mul_inv_cancel_right]
        rwa [← this] at hd
  have hxBD : x ∈ (B : Set G) * (D : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right B D hBN, hBDA]
    exact hx
  obtain ⟨y, hy, d, hd, rfl⟩ := hxBD
  rw [hBab] at hy
  obtain ⟨u, hu, w, hw, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hy
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hu
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hw
  exact ⟨i, j, d, hd, rfl⟩

theorem fix_of_mem_autIn {A D : Subgroup G} (hD3 : Nat.card D = 3) (hDA : D ≤ A)
    {h : G} (hN : h ∈ Subgroup.normalizer (A : Set G))
    (hhD : h ∈ Subgroup.normalizer (D : Set G))
    (h3 : (A.normalizerMonoidHom ⟨h, hN⟩) ^ 3 = 1) {d : G} (hd : d ∈ D) :
    h * d * h⁻¹ = d := by
  have hcube : h ^ 3 * d * (h ^ 3)⁻¹ = d := by
    have := congrArg (fun τ : MulAut A => ((τ ⟨d, hDA hd⟩ : A) : G)) h3
    simp only [MulAut.one_apply] at this
    rwa [Item462Proof.normalizerMonoidHom_pow_apply_coe] at this
  have h2 := Item462Proof.conj_conj_eq_of_card_three hD3 hhD hd
  have h2' : h⁻¹ * (h⁻¹ * d * h) * h = d := by
    calc h⁻¹ * (h⁻¹ * d * h) * h = h⁻¹ * (h⁻¹ * (h * (h * d * h⁻¹) * h⁻¹) * h) * h := by rw [h2]
      _ = d := by group
  have e1 : h * d * h⁻¹ = h⁻¹ * (h⁻¹ * (h ^ 3 * d * (h ^ 3)⁻¹) * h) * h := by group
  rw [e1, hcube]
  exact h2'

theorem eq_one_of_mem_autIn {A B D L : Subgroup G} {a b : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (haB : a ∈ B) (hbB : b ∈ B) (hba : b ∉ Subgroup.zpowers a) (hBA : B ≤ A)
    (hB9 : Nat.card B = 9) (hDA : D ≤ A) (hBDA : B ⊔ D = A) (hD3 : Nat.card D = 3)
    (hND : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G))
    {σ : MulAut A} (hσ : σ ∈ autIn L A) (hσ3 : σ ^ 3 = 1)
    (hσb : (σ ⟨b, hBA hbB⟩ : G) = b) : σ = 1 := by
  obtain ⟨h, hN, -, rfl⟩ := mem_autIn_iff.mp hσ
  ext ⟨x, hx⟩
  simp only [MulAut.one_apply]
  rw [Sec4.normalizerMonoidHom_apply_coe]
  have hb' : h * b * h⁻¹ = b := by rwa [Sec4.normalizerMonoidHom_apply_coe] at hσb
  have ha' : h * a * h⁻¹ = a := by
    rw [Subgroup.mem_center_iff.mp haZ h, mul_inv_cancel_right]
  obtain ⟨i, j, d, hd, rfl⟩ := exists_eq_of_mem_A hAe haZ ha3 haB hbB hba hBA hB9 hDA hBDA hx
  have hd' := fix_of_mem_autIn hD3 hDA hN (hND hN) hσ3 hd
  have hconj : ∀ y z : G, h * (y * z) * h⁻¹ = (h * y * h⁻¹) * (h * z * h⁻¹) := fun y z => by
    group
  have hzpow : ∀ (y : G) (k : ℤ), h * y ^ k * h⁻¹ = (h * y * h⁻¹) ^ k := fun y k => by
    rw [← MulAut.conj_apply, map_zpow, MulAut.conj_apply]
  show h * (a ^ i * b ^ j * d) * h⁻¹ = a ^ i * b ^ j * d
  rw [hconj, hconj, hzpow, hzpow, ha', hb', hd']

theorem card_autIn_le {A B D L : Subgroup G} {a b : G}
    (hAe : CFSG.Assembly.IsElemAbelian 3 A) (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3)
    (haB : a ∈ B) (hbB : b ∈ B) (hba : b ∉ Subgroup.zpowers a) (hBA : B ≤ A)
    (hB9 : Nat.card B = 9) (hDA : D ≤ A) (hBDA : B ⊔ D = A) (hD3 : Nat.card D = 3)
    (hND : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (D : Set G))
    (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (hexp : ∀ σ ∈ autIn L A, σ ^ 3 = 1) :
    Nat.card (autIn L A) ≤ Nat.card (A ⊓ L : Subgroup G) := by
  classical
  have hbA := hBA hbB
  have hmem : ∀ σ ∈ autIn L A, (σ ⟨b, hbA⟩ : G) * b⁻¹ ∈ A ⊓ L := by
    intro σ hσ
    obtain ⟨h, hN, hhL, rfl⟩ := mem_autIn_iff.mp hσ
    rw [Sec4.normalizerMonoidHom_apply_coe]
    refine ⟨A.mul_mem ((Subgroup.mem_normalizer_iff.mp hN b).mp hbA) (A.inv_mem hbA), ?_⟩
    have h1 : b * h⁻¹ * b⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (hAL hbA) h⁻¹).mp (L.inv_mem hhL)
    have h2 := L.mul_mem hhL h1
    rwa [show h * (b * h⁻¹ * b⁻¹) = h * b * h⁻¹ * b⁻¹ by group] at h2
  let f : autIn L A → (A ⊓ L : Subgroup G) := fun σ => ⟨_, hmem σ σ.2⟩
  have hf : Function.Injective f := by
    intro σ τ hστ
    have h1 : (σ : MulAut A) ⟨b, hbA⟩ = (τ : MulAut A) ⟨b, hbA⟩ := by
      apply Subtype.ext
      have := congrArg Subtype.val hστ
      simpa [f] using this
    have hρ : (σ : MulAut A)⁻¹ * τ ∈ autIn L A := mul_mem (inv_mem σ.2) τ.2
    have hρ3 := hexp _ hρ
    have hρb : (((σ : MulAut A)⁻¹ * τ) ⟨b, hbA⟩ : G) = b := by
      rw [MulAut.mul_apply, ← h1, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    have h2 := eq_one_of_mem_autIn hAe haZ ha3 haB hbB hba hBA hB9 hDA hBDA hD3 hND hρ hρ3 hρb
    apply Subtype.ext
    exact inv_mul_eq_one.mp h2
  exact Nat.card_le_card_of_injective f hf

omit [Finite G] in
theorem card_map_of_injOn {Q : Type*} [Group Q] (f : G →* Q) {H : Subgroup G}
    (hH : Set.InjOn f (H : Set G)) : Nat.card (H.map f) = Nat.card H := by
  have hinj : Function.Injective (f.comp H.subtype) := fun x y hxy => Subtype.ext (hH x.2 y.2 hxy)
  have hr : (f.comp H.subtype).range = H.map f := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [← hr]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem card_thetaImage_mul {L A : Subgroup G} (hL : L ∈ thetaComponents 3 G)
    (hAN : A ≤ Subgroup.normalizer (L : Set G)) (hA3 : ∀ x ∈ A, x ^ 3 = 1) :
    Nat.card (thetaImage (L ⊔ A)) * Nat.card (A ⊓ L : Subgroup G) =
      Nat.card (L ⧸ aschbacherSolvableCore 3 L) * Nat.card A := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 G with hNdef
  set ρ := QuotientGroup.mk' N with hρ
  have hAp : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hA3 x x.2)⟩
  have hinj : Set.InjOn ρ (A : Set G) := injOn_mk_of_isPGroup Nat.prime_three hAp
  obtain ⟨-, -, ⟨η, -⟩, -, -, -, hNL, -, -, -, hAiff⟩ :=
    theta_component_quotient_structure Nat.prime_three hL
  have hAK : A.map ρ ≤ Subgroup.normalizer ((L.map ρ : Subgroup (G ⧸ N)) : Set (G ⧸ N)) :=
    (hAiff A).mp hAN
  have h1 := Sec6.card_sup_mul_card_inf hAK
  have hsup : A.map ρ ⊔ L.map ρ = thetaImage (L ⊔ A) := by
    rw [thetaImage, Subgroup.map_sup, sup_comm]
  have hinf : A.map ρ ⊓ L.map ρ = (A ⊓ L).map ρ := by
    refine le_antisymm ?_ (Subgroup.map_inf_le _ _ _)
    rintro _ ⟨⟨x, hx, rfl⟩, ⟨l, hl, hlx⟩⟩
    have htN : l⁻¹ * x ∈ N := by
      rw [← QuotientGroup.eq_one_iff]
      change ρ (l⁻¹ * x) = 1
      rw [map_mul, map_inv, hlx, inv_mul_cancel]
    have hx3 : (l * (l⁻¹ * x)) ^ 3 = 1 := by rw [mul_inv_cancel_left]; exact hA3 x hx
    obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := G)
      Nat.prime_three
    have htL := Item462Proof.mem_of_mul_pow_three hNL hN3 hl htN hx3
    have hxL : x ∈ L := by
      have := L.mul_mem hl htL
      rwa [mul_inv_cancel_left] at this
    exact ⟨x, ⟨hx, hxL⟩, rfl⟩
  have hcardA : Nat.card (A.map ρ) = Nat.card A := card_map_of_injOn ρ hinj
  have hcardAL : Nat.card ((A ⊓ L).map ρ) = Nat.card (A ⊓ L : Subgroup G) :=
    card_map_of_injOn ρ (hinj.mono inf_le_left)
  rw [hsup, hinf, hcardA, hcardAL, Nat.card_congr η.toEquiv.symm] at h1
  rw [h1, mul_comm]

theorem card_inf_le_three_of_outer {A L : Subgroup G} {a : G}
    (h27 : Nat.card A = 27) (haA : a ∈ A)
    (haZ : a ∈ Subgroup.center G) (ha3 : orderOf a = 3) (haL : a ∉ L) {x : G} (hxA : x ∈ A)
    (hxo : InducesOuterTheta x L) : Nat.card (A ⊓ L : Subgroup G) ≤ 3 := by
  have hdvd : Nat.card (A ⊓ L : Subgroup G) ∣ 3 ^ 3 := by
    rw [show (3 : ℕ) ^ 3 = 27 by norm_num, ← h27]
    exact Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨k, hk3, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
  by_contra hlt
  have hk2 : 2 ≤ k := by
    by_contra h
    interval_cases k <;> simp_all
  have haAL : a ∉ A ⊓ L := fun h => haL h.2
  have hcard := Item462Proof.card_sup_zpowers_of_not_mem haZ ha3 haAL
  have hAeq : (A ⊓ L) ⊔ Subgroup.zpowers a = A := by
    refine Subgroup.eq_of_le_of_card_ge (sup_le inf_le_left (Subgroup.zpowers_le.mpr haA)) ?_
    rw [hcard, hk, h27]
    interval_cases k
    · norm_num
    · exfalso
      have hAL : A ⊓ L = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [hk, h27]; norm_num)
      apply haAL
      rw [hAL]
      exact haA
  have hZn : (Subgroup.zpowers a).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr haZ)
  have hx : x ∈ (A ⊓ L) ⊔ Subgroup.zpowers a := by rw [hAeq]; exact hxA
  obtain ⟨l, hl, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hx
  obtain ⟨hxN, hout⟩ := hxo
  apply hout
  have hzC : z ∈ thetaQuotCentralizer L :=
    mem_thetaQuotCentralizer_of_mem_center ((Subgroup.zpowers_le.mpr haZ) hz)
  obtain ⟨⟨z', hz'N⟩, hz'ker, rfl⟩ := hzC
  have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hl.2
  have hsplit : (⟨l * z', hxN⟩ : Subgroup.normalizer (L : Set G)) = ⟨l, hlN⟩ * ⟨z', hz'N⟩ :=
    Subtype.ext rfl
  change thetaQuotMulAut L (L.normalizerMonoidHom ⟨l * z', hxN⟩) ∈ _
  rw [hsplit, map_mul, map_mul]
  have h1 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨z', hz'N⟩) = 1 := MonoidHom.mem_ker.mp hz'ker
  have h2 : thetaQuotMulAut L (L.normalizerMonoidHom ⟨l, hlN⟩) =
      MulAut.conj (QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨l, hl.2⟩) :=
    KFacts.thetaQuotMulAut_compAction_of_mem hl.2 hlN
  rw [h1, mul_one, h2]
  exact ⟨_, rfl⟩

end CFSG.RankThree.PartTwo.Sec4.Item462AltProof
