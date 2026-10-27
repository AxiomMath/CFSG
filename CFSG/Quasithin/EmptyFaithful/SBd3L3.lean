module

public import CFSG.Quasithin.EmptyFaithful.SBd3L3Fin
public import CFSG.Quasithin.EmptyFaithful.SBd2L3Branch2

public section

namespace CFSG.Quasithin

namespace SBd3

open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

section Core

theorem core_aux {W : Subgroup SL3} {c : SL3 → Prop}
    (hB2 : IsPGroup 2 ↥(upperTriangular 3 (ZMod 2)))
    (hBW : upperTriangular 3 (ZMod 2) ≤ Subgroup.normalizer (W : Set SL3))
    (h24 : 24 ∣ Nat.card ↥(W ⊔ upperTriangular 3 (ZMod 2)))
    (hXc : ∀ g ∈ W ⊔ upperTriangular 3 (ZMod 2), c g)
    (hcard : Nat.card {g : SL3 // c g} = 24)
    (hexp : ∀ z : SL3, c z → z ^ 3 = 1 ∨ z ^ 4 = 1)
    (hwit : ∀ z : SL3, c z → z ^ 3 = 1 → ∃ z₁ z₂ b₁ b₂ : SL3, c z₁ ∧ z₁ ^ 3 = 1 ∧ c z₂ ∧
      z₂ ^ 3 = 1 ∧ condB b₁ ∧ condB b₂ ∧
      z = z₁ * b₁ * z₁⁻¹ * b₁⁻¹ * (z₂ * b₂ * z₂⁻¹ * b₂⁻¹)) :
    ⁅oTwoUpper W, upperTriangular 3 (ZMod 2)⁆ = oTwoUpper W := by
  set B := upperTriangular 3 (ZMod 2) with hB
  set X := W ⊔ B with hX
  have hWX : W ≤ X := le_sup_left
  let ι : ↥X → {g : SL3 // c g} := fun g => ⟨g.1, hXc g.1 g.2⟩
  have hinj : Function.Injective ι := fun a b hab =>
    Subtype.ext (congrArg (fun x : {g : SL3 // c g} => x.1) hab)
  have hXle : Nat.card ↥X ≤ 24 := by
    rw [← hcard]
    exact Nat.card_le_card_of_injective ι hinj
  have hXcard : Nat.card ↥X = 24 := le_antisymm hXle (Nat.le_of_dvd Nat.card_pos h24)
  have hbij : Function.Bijective ι :=
    hinj.bijective_of_nat_card_le (by rw [hXcard, hcard])
  have hcX : ∀ g : SL3, c g → g ∈ X := fun g hg => by
    obtain ⟨x, hx⟩ := hbij.2 ⟨g, hg⟩
    have : x.1 = g := congrArg Subtype.val hx
    rw [← this]
    exact x.2
  have hodd_in : ∀ z : SL3, z ∈ X → Odd (orderOf z) → z ∈ W := fun z hz hodd =>
    SBd2.oTwoUpper_le_of_le_sup_two (le_refl X) hB2 hBW (mem_oTwoUpper_of_odd hz hodd)
  have hgen : ∀ z : SL3, z ∈ W → Odd (orderOf z) → z ∈ ⁅oTwoUpper W, B⁆ := by
    intro z hzW hzodd
    have hzc : c z := hXc z (hWX hzW)
    have hz3 : z ^ 3 = 1 := by
      rcases hexp z hzc with h | h
      · exact h
      · have hd : orderOf z ∣ 4 := orderOf_dvd_of_pow_eq_one h
        have hle : orderOf z ≤ 4 := Nat.le_of_dvd (by norm_num) hd
        have h13 : orderOf z = 1 ∨ orderOf z = 3 := by
          obtain ⟨m, hm⟩ := hzodd
          omega
        have h1 : orderOf z = 1 := by
          rcases h13 with h1 | h3
          · exact h1
          · exfalso
            rw [h3] at hd
            exact absurd hd (by norm_num)
        rw [orderOf_eq_one_iff.mp h1]
        simp
    obtain ⟨z₁, z₂, b₁, b₂, hc₁, h₁, hc₂, h₂, hb₁, hb₂, hz⟩ := hwit z hzc hz3
    have hO : ∀ y : SL3, c y → y ^ 3 = 1 → y ∈ oTwoUpper W := fun y hy hy3 => by
      have hodd : Odd (orderOf y) :=
        Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hy3)
      exact mem_oTwoUpper_of_odd (hodd_in y (hcX y hy) hodd) hodd
    have e1 : z₁ * b₁ * z₁⁻¹ * b₁⁻¹ ∈ ⁅oTwoUpper W, B⁆ := by
      have := Subgroup.commutator_mem_commutator (hO z₁ hc₁ h₁) ((mem_upperTriangular_iff b₁).mpr hb₁)
      rwa [commutatorElement_def] at this
    have e2 : z₂ * b₂ * z₂⁻¹ * b₂⁻¹ ∈ ⁅oTwoUpper W, B⁆ := by
      have := Subgroup.commutator_mem_commutator (hO z₂ hc₂ h₂) ((mem_upperTriangular_iff b₂).mpr hb₂)
      rwa [commutatorElement_def] at this
    rw [hz]
    exact Subgroup.mul_mem _ e1 e2
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro u hu b hb
    have hbN : b ∈ Subgroup.normalizer (oTwoUpper W : Set SL3) :=
      normalizer_le_normalizer_oTwoUpper W (hBW hb)
    rw [commutatorElement_def]
    have h1 : b * u⁻¹ * b⁻¹ ∈ oTwoUpper W :=
      (Subgroup.mem_normalizer_iff.mp hbN u⁻¹).mp ((oTwoUpper W).inv_mem hu)
    have e : u * b * u⁻¹ * b⁻¹ = u * (b * u⁻¹ * b⁻¹) := by group
    rw [e]
    exact (oTwoUpper W).mul_mem hu h1
  · rw [oTwoUpper, Subgroup.closure_le]
    rintro z ⟨hzW, hzodd⟩
    exact hgen z hzW hzodd

theorem card_borel : Nat.card ↥(upperTriangular 3 (ZMod 2)) = 8 := by
  rw [Nat.card_congr (Equiv.subtypeEquivRight fun g => mem_upperTriangular_iff g), card_condB]

theorem isPGroup_borel : IsPGroup 2 ↥(upperTriangular 3 (ZMod 2)) :=
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  IsPGroup.of_card (n := 3) card_borel

theorem isSylowTwoOf_borel : IsSylowTwoOf (upperTriangular 3 (ZMod 2)) ⊤ := by
  refine ⟨le_top, isPGroup_borel, ?_⟩
  have h1 : (upperTriangular 3 (ZMod 2)).relIndex ⊤ = (upperTriangular 3 (ZMod 2)).index :=
    Subgroup.relIndex_top_right _
  have h2 := Subgroup.index_mul_card (H := upperTriangular 3 (ZMod 2))
  rw [card_borel, card_SL3] at h2
  show ¬ 2 ∣ (upperTriangular 3 (ZMod 2)).relIndex ⊤
  rw [h1]
  omega

theorem not_isSolvable_SL3 : ¬ Group.IsSolvable SL3 := by
  have hperf : Group.IsPerfect SL3 :=
    CFSG.ClassicalModels.specialLinear_isPerfect_of_three_le (by norm_num)
  have : Nontrivial SL3 := Finite.one_lt_card_iff_nontrivial.mp (by rw [card_SL3]; norm_num)
  exact Group.IsPerfect.not_isSolvable SL3

theorem core_borel {W : Subgroup SL3} (hW : Group.IsSolvable ↥W)
    (hBW : upperTriangular 3 (ZMod 2) ≤ Subgroup.normalizer (W : Set SL3))
    (h3 : 3 ∣ Nat.card ↥W) :
    ⁅oTwoUpper W, upperTriangular 3 (ZMod 2)⁆ = oTwoUpper W := by
  set B := upperTriangular 3 (ZMod 2) with hB
  have hX : Group.IsSolvable ↥(W ⊔ B) :=
    F1.isSolvable_sup_of_le_normalizer hW (F1.isSolvable_of_isPGroup_two isPGroup_borel) hBW
  have h24 : 24 ∣ Nat.card ↥(W ⊔ B) := by
    have h8 : 8 ∣ Nat.card ↥(W ⊔ B) := card_borel ▸ Subgroup.card_dvd_of_le (le_sup_right : B ≤ W ⊔ B)
    have h3' : 3 ∣ Nat.card ↥(W ⊔ B) := h3.trans (Subgroup.card_dvd_of_le le_sup_left)
    exact Nat.Coprime.mul_dvd_of_dvd_of_dvd (by norm_num : Nat.Coprime 8 3) h8 h3'
  obtain ⟨hXeq, -⟩ := borel_overgroups (W ⊔ B) le_sup_right
  have hnotTop : W ⊔ B ≠ ⊤ := by
    intro htop
    apply not_isSolvable_SL3
    let e : ↥(W ⊔ B) ≃* SL3 := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
    exact Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective
  obtain ⟨i, hi⟩ : (borelOvergroupCuts (W ⊔ B)).Nonempty := by
    rw [Set.nonempty_iff_ne_empty]
    intro hI
    apply hnotTop
    rw [hXeq, hI, flagStabilizer_empty]
  have hstab : ∀ g ∈ W ⊔ B, g ∈ stabilizer (flagSpace 3 (ZMod 2) i) := fun g hg =>
    mem_flagStabilizer.mp (hXeq ▸ hg) i hi
  obtain ⟨hi1, hi3, -⟩ := hi
  have hi12 : i = 1 ∨ i = 2 := by omega
  rcases hi12 with rfl | rfl
  · exact core_aux isPGroup_borel hBW h24 (fun g hg => cond1_of_mem_stabilizer (hstab g hg))
      card_cond1 exp_cond1 witness1
  · exact core_aux isPGroup_borel hBW h24 (fun g hg => cond2_of_mem_stabilizer (hstab g hg))
      card_cond2 exp_cond2 witness2

theorem core_sl3 {W P : Subgroup SL3} (hP : IsSylowTwoOf P ⊤) (hW : Group.IsSolvable ↥W)
    (hPW : P ≤ Subgroup.normalizer (W : Set SL3)) (h3 : 3 ∣ Nat.card ↥W) :
    ⁅oTwoUpper W, P⁆ = oTwoUpper W := by
  obtain ⟨g, -, hg⟩ := B6.isSylowTwoOf_exists_conj isSylowTwoOf_borel hP
  set B := upperTriangular 3 (ZMod 2) with hB
  set W' : Subgroup SL3 := B6.conjSub g⁻¹ W with hW'
  have hmapW : W'.map (MulAut.conj g).toMonoidHom = W := by
    show B6.conjSub g W' = W
    rw [hW', ← B6.conjSub_mul, mul_inv_cancel, B6.conjSub_one]
  have hmapB : B.map (MulAut.conj g).toMonoidHom = P := hg.symm
  have hBW' : B ≤ Subgroup.normalizer (W' : Set SL3) := by
    intro b hb
    refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
    have hk' : g * k * g⁻¹ ∈ W := by
      have := (B6.mem_conjSub (g := g⁻¹) (x := k) (X := W)).mp hk
      simpa using this
    have hb' : g * b * g⁻¹ ∈ P := by
      rw [hg, B6.mem_conjSub]
      have e : g⁻¹ * (g * b * g⁻¹) * g = b := by group
      rw [e]
      exact hb
    have h1 := (Subgroup.mem_normalizer_iff.mp (hPW hb') (g * k * g⁻¹)).mp hk'
    show b * k * b⁻¹ ∈ B6.conjSub g⁻¹ W
    rw [B6.mem_conjSub]
    have e : g⁻¹⁻¹ * (b * k * b⁻¹) * g⁻¹ = (g * b * g⁻¹) * (g * k * g⁻¹) * (g * b * g⁻¹)⁻¹ := by
      group
    rw [e]
    exact h1
  have hW'solv : Group.IsSolvable ↥W' :=
    Group.isSolvable_of_surjective (f := (MulAut.conj g⁻¹).toMonoidHom.subgroupMap W)
      (MonoidHom.subgroupMap_surjective _ _)
  have hcard : Nat.card ↥W' = Nat.card ↥W :=
    (Nat.card_congr ((MulAut.conj g⁻¹).subgroupMap W).toEquiv).symm
  have key := core_borel hW'solv hBW' (hcard ▸ h3)
  have key' := congrArg (Subgroup.map (MulAut.conj g).toMonoidHom) key
  rw [Subgroup.map_commutator, ← oTwoUpper_map, hmapW, hmapB] at key'
  exact key'

end Core

section Lift

variable {H : Type} [Group H] [Finite H]

theorem le_normalizer_commutator_left (H₁ H₂ : Subgroup H) :
    H₁ ≤ Subgroup.normalizer ((⁅H₁, H₂⁆ : Subgroup H) : Set H) := by
  intro a ha
  refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
  rw [Subgroup.commutator_def] at hk
  induction hk using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g₁, hg₁, g₂, hg₂, rfl⟩ := hx
    have e : a * ⁅g₁, g₂⁆ * a⁻¹ = ⁅a * g₁, g₂⁆ * ⁅a, g₂⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.commutator_mem_commutator (H₁.mul_mem ha hg₁) hg₂)
      (Subgroup.inv_mem _ (Subgroup.commutator_mem_commutator ha hg₂))
  | one => simp
  | mul x y _ _ hx hy =>
    have e : a * (x * y) * a⁻¹ = (a * x * a⁻¹) * (a * y * a⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have e : a * x⁻¹ * a⁻¹ = (a * x * a⁻¹)⁻¹ := by group
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem lift_commutator {K : Type} [Group K] {φ : H →* K} (hker : IsPGroup 2 ↥φ.ker)
    {S₀ Z₀ : Subgroup H} (hSZ : S₀ ≤ Subgroup.normalizer (Z₀ : Set H))
    (hdown : ⁅oTwoUpper (Z₀.map φ), S₀.map φ⁆ = oTwoUpper (Z₀.map φ)) :
    ⁅oTwoUpper Z₀, S₀⁆ = oTwoUpper Z₀ := by
  set W := oTwoUpper Z₀ with hW
  have hSW : S₀ ≤ Subgroup.normalizer (W : Set H) := fun s hs =>
    normalizer_le_normalizer_oTwoUpper Z₀ (hSZ hs)
  have hKW : ⁅W, S₀⁆ ≤ W := by
    rw [Subgroup.commutator_le]
    intro w hw s hs
    rw [commutatorElement_def]
    have h1 : s * w⁻¹ * s⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hSW hs) w⁻¹).mp (W.inv_mem hw)
    have e : w * s * w⁻¹ * s⁻¹ = w * (s * w⁻¹ * s⁻¹) := by group
    rw [e]
    exact W.mul_mem hw h1
  refine le_antisymm hKW ?_
  have hmap : (⁅W, S₀⁆ : Subgroup H).map φ = W.map φ := by
    rw [Subgroup.map_commutator, hW, ← oTwoUpper_map, hdown]
  have hcover : W ≤ ⁅W, S₀⁆ ⊔ (φ.ker ⊓ W) := by
    intro w hw
    have h1 : φ w ∈ (⁅W, S₀⁆ : Subgroup H).map φ := hmap ▸ ⟨w, hw, rfl⟩
    obtain ⟨k, hk, hkw⟩ := h1
    have hkerel : k⁻¹ * w ∈ φ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hkw, inv_mul_cancel]
    have hkw' : k⁻¹ * w ∈ W := W.mul_mem (W.inv_mem (hKW hk)) hw
    have e : w = k * (k⁻¹ * w) := by group
    rw [e]
    exact Subgroup.mul_mem_sup hk ⟨hkerel, hkw'⟩
  have hle := SBd2.oTwoUpper_le_of_le_sup_two hcover (hker.to_le inf_le_left)
    (inf_le_right.trans (le_normalizer_commutator_left W S₀))
  exact ((A4.oTwoUpper_oTwoUpper Z₀).symm.le : W ≤ oTwoUpper W).trans hle

end Lift

section Main

theorem l3SolvableOverSylow_holds : L3SolvableOverSylow := by
  intro G _ _ L S Z hL hS hZL hZsolv hSN h3
  obtain ⟨e⟩ := hL
  let ψ : _ ≃* SL3 := (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 3 (ZMod 2)).symm
  let φ : ↥L →* SL3 :=
    ψ.toMonoidHom.comp (e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)))
  have hφsurj : Function.Surjective φ :=
    ψ.surjective.comp (e.surjective.comp (QuotientGroup.mk'_surjective _))
  have hφker : φ.ker ≤ CFSG.pCore 2 ↥L := by
    intro x hx
    rw [MonoidHom.mem_ker] at hx
    have h1 : e (QuotientGroup.mk x) = 1 :=
      ψ.injective (by simpa [φ] using hx)
    have h2 : (QuotientGroup.mk x : ↥L ⧸ CFSG.pCore 2 ↥L) = 1 :=
      e.injective (by rw [h1, map_one])
    exact (QuotientGroup.eq_one_iff x).mp h2
  have hker : IsPGroup 2 ↥φ.ker := CFSG.pCore_isPGroup.to_le hφker
  set Z₀ : Subgroup ↥L := Z.subgroupOf L with hZ₀
  set S₀ : Subgroup ↥L := S.subgroupOf L with hS₀
  have hSZ₀ : S₀ ≤ Subgroup.normalizer (Z₀ : Set ↥L) := by
    intro s hs
    rw [Subgroup.mem_normalizer_iff]
    intro n
    have h1 := Subgroup.mem_normalizer_iff.mp (hSN (Subgroup.mem_subgroupOf.mp hs)) (n : G)
    exact h1
  have hZ₀solv : Group.IsSolvable ↥Z₀ :=
    Group.isSolvable_of_surjective (f := (Subgroup.subgroupOfEquivOfLe hZL).symm.toMonoidHom)
      (MulEquiv.surjective _)
  have hWsolv : Group.IsSolvable ↥(Z₀.map φ) :=
    Group.isSolvable_of_surjective (f := φ.subgroupMap Z₀) (φ.subgroupMap_surjective Z₀)
  have hP : IsSylowTwoOf (S₀.map φ) ⊤ := by
    refine ⟨le_top, ?_, ?_⟩
    · have h2 : IsPGroup 2 ↥S₀ := hS.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hS.1).symm
      exact h2.of_surjective (φ.subgroupMap S₀) (φ.subgroupMap_surjective S₀)
    · show ¬ 2 ∣ (S₀.map φ).relIndex ⊤
      rw [Subgroup.relIndex_top_right]
      intro hd
      exact hS.2.2 (hd.trans (Subgroup.index_map_dvd _ hφsurj))
  have hPW : S₀.map φ ≤ Subgroup.normalizer ((Z₀.map φ : Subgroup SL3) : Set SL3) := by
    rintro _ ⟨s, hs, rfl⟩
    refine A4.mem_normalizer_of_conj_mem fun k hk => ?_
    obtain ⟨z, hz, rfl⟩ := hk
    have h1 := (Subgroup.mem_normalizer_iff.mp (hSZ₀ hs) z).mp hz
    exact ⟨s * z * s⁻¹, h1, by simp⟩
  have h3W : 3 ∣ Nat.card ↥(Z₀.map φ) := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    let z' : ↥L := ⟨z.1, hZL z.2⟩
    have hz'Z₀ : z' ∈ Z₀ := z.2
    have hz'ord : orderOf z' = 3 := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, hz]
    have hz'1 : φ z' ≠ 1 := by
      intro h1
      have hmem : z' ∈ φ.ker := h1
      obtain ⟨k, hk⟩ := hker ⟨z', hmem⟩
      have hk' : z' ^ 2 ^ k = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hd : orderOf z' ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
      rw [hz'ord] at hd
      exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hd) (by norm_num)
    have h3pow : z' ^ 3 = 1 := by
      rw [← hz'ord]
      exact pow_orderOf_eq_one z'
    have hord3 : orderOf (φ z') = 3 :=
      orderOf_eq_prime (by rw [← map_pow, h3pow, map_one]) hz'1
    have hmemW : φ z' ∈ Z₀.map φ := ⟨z', hz'Z₀, rfl⟩
    have h4 : orderOf (⟨φ z', hmemW⟩ : ↥(Z₀.map φ)) = 3 := by
      rw [Subgroup.orderOf_mk, hord3]
    have h5 := orderOf_dvd_natCard (⟨φ z', hmemW⟩ : ↥(Z₀.map φ))
    rwa [h4] at h5
  have hdown : ⁅oTwoUpper (Z₀.map φ), S₀.map φ⁆ = oTwoUpper (Z₀.map φ) :=
    core_sl3 hP hWsolv hPW h3W
  have key : ⁅oTwoUpper Z₀, S₀⁆ = oTwoUpper Z₀ := lift_commutator hker hSZ₀ hdown
  have hmapZ : Z₀.map L.subtype = Z := Subgroup.map_subgroupOf_eq_of_le hZL
  have hmapS : S₀.map L.subtype = S := Subgroup.map_subgroupOf_eq_of_le hS.1
  calc ⁅oTwoUpper Z, S⁆ = ⁅oTwoUpper (Z₀.map L.subtype), S₀.map L.subtype⁆ := by
        rw [hmapZ, hmapS]
    _ = ⁅(oTwoUpper Z₀).map L.subtype, S₀.map L.subtype⁆ := by rw [oTwoUpper_map]
    _ = (⁅oTwoUpper Z₀, S₀⁆).map L.subtype := (Subgroup.map_commutator _ _ _).symm
    _ = (oTwoUpper Z₀).map L.subtype := by rw [key]
    _ = oTwoUpper (Z₀.map L.subtype) := (oTwoUpper_map _ _).symm
    _ = oTwoUpper Z := by rw [hmapZ]

end Main

end SBd3

end CFSG.Quasithin
