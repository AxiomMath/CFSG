module

public import CFSG.RankThree.PartTwo.Sec14.Item1411Chain
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec15.Item15Tools
import CFSG.LocalAnalysis.SignalizerFunctor.Maximality

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {LB : Subgroup G → Subgroup G}

omit [Finite G] in
theorem maxIn_scriptQPi_of_le {Y Y' : Subgroup G} (hY' : Y' ≤ Y) (π : Set Nat.Primes) :
    maxIn (scriptQPi A LB Y π) Y' = scriptQPiStar A LB Y' π := by
  have h : ∀ R, (R ∈ scriptQPi A LB Y π ∧ R ≤ Y') ↔ R ∈ scriptQPi A LB Y' π := fun R =>
    ⟨fun ⟨⟨⟨h1, _⟩, h2⟩, h3⟩ => ⟨⟨h1, h3⟩, h2⟩,
      fun ⟨⟨h1, h3⟩, h2⟩ => ⟨⟨⟨h1, h3.trans hY'⟩, h2⟩, h3⟩⟩
  ext S
  simp only [maxIn, scriptQPiStar, Set.mem_ofPred_eq, h]

omit [Finite G] in
theorem isLocallyTransitive_of_transOn {V Y Y' : Subgroup G} (hY' : Y' ≤ Y)
    (h : TransOn A LB V Y') :
    IsLocallyTransitive (V ⊓ Y) (scriptQPi A LB Y (piOf 2)) Y' := by
  intro S hS T hT
  rw [maxIn_scriptQPi_of_le hY' (piOf 2)] at hS hT
  have hc := h S hS T hT
  rwa [inf_assoc, inf_eq_right.mpr hY']

omit [Finite G] in
theorem sup_mem_scriptQ_of_item146 (hA : IsE27 A) (h146 : Item146 A LB) {U D : Subgroup G}
    (hU : U ∈ scriptQ A LB) (hD : D ∈ scriptQ A LB)
    (hUD : U ≤ Subgroup.normalizer (D : Set G)) : U ⊔ D ∈ scriptQ A LB := by
  have hZ : U ⊔ D ∈ invariantPiSubgroups ⊤ A (piCompl 3) :=
    ⟨le_top, isPiSubgroup_piCompl_sup hU.1.2.1 hD.1.2.1 hUD,
      le_normalizer_sup hU.1.2.2 hD.1.2.2⟩
  have hΔ := delta_mem_scriptQ hA h146 hZ
  have heq : delta A LB (U ⊔ D) = U ⊔ D :=
    le_antisymm (delta_le _) (sup_le (le_delta hU le_sup_left) (le_delta hD le_sup_right))
  rwa [heq] at hΔ

theorem sup_mem_scriptQPi_of_item146 (hA : IsE27 A) (h146 : Item146 A LB) {Y U D : Subgroup G}
    (hU : U ∈ scriptQPi A LB Y (piOf 2)) (hD : D ∈ scriptQPi A LB Y (piOf 2))
    (hUD : U ≤ Subgroup.normalizer (D : Set G)) : U ⊔ D ∈ scriptQPi A LB Y (piOf 2) :=
  ⟨⟨sup_mem_scriptQ_of_item146 hA h146 hU.1.1 hD.1.1 hUD, sup_le hU.1.2 hD.1.2⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      (IsPGroup.to_sup_of_normal_right' (isPGroup_of_mem_scriptQPi Nat.prime_two hU)
        (isPGroup_of_mem_scriptQPi Nat.prime_two hD) hUD)⟩

theorem not_three_dvd_delta_of_le_centralizer {Y B : Subgroup G} (hB : IsHyperplane A B)
    (hLB : LB B = ⊥) (hYB : Y ≤ Subgroup.centralizer (B : Set G)) :
    ¬ 3 ∣ Nat.card (delta A LB Y) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set OB := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hOB
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOA
  have hpi : ∀ X : Subgroup G, IsPiSubgroup (piCompl 3) (pPrimeCoreOf 3 X) := fun X =>
    (isPiSubgroup_piCompl_iff Nat.prime_three _).mpr
      ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 X))
  have hK : IsPiSubgroup (piCompl 3) (OA ⊔ OB) :=
    isPiSubgroup_piCompl_sup (hpi _) (hpi _)
      ((pPrimeCoreOf_le 3 _).trans (centralizer_le_normalizer_pPrimeCoreOf hB.1))
  have hle : delta A LB Y ≤ OA ⊔ OB := by
    refine sSup_le fun Q hQ => ?_
    have h := hQ.1.2 B hB
    rw [qBound, hLB, sup_bot_eq, inf_eq_left.mpr (hQ.2.trans hYB), sup_comm] at h
    exact h
  intro h3
  exact (isPiSubgroup_piCompl_iff Nat.prime_three _).mp hK
    (h3.trans (Subgroup.card_dvd_of_le hle))

theorem exists_inf_centralizer_not_le (hA : IsE27 A) {S T D : Subgroup G} (hS : ¬ S ≤ D)
    (hT : ¬ T ≤ D) (hAS : A ≤ Subgroup.normalizer (S : Set G))
    (hAT : A ≤ Subgroup.normalizer (T : Set G)) (hcS : Nat.Coprime 3 (Nat.card S))
    (hcT : Nat.Coprime 3 (Nat.card T)) :
    ∃ a ∈ A, a ≠ 1 ∧ ¬ S ⊓ Subgroup.centralizer {a} ≤ D ∧
      ¬ T ⊓ Subgroup.centralizer {a} ≤ D := by
  have hlarge : 3 ^ (2 + 1) ≤ Nat.card A := by rw [hA.2]; norm_num
  have hB : ∀ X : Subgroup G, ¬ X ≤ D → A ≤ Subgroup.normalizer (X : Set G) →
      Nat.Coprime 3 (Nat.card X) →
      ∃ B : Subgroup G, B ≤ A ∧ Nat.card B = 9 ∧ ¬ X ⊓ Subgroup.centralizer (B : Set G) ≤ D := by
    intro X hX hAX hcX
    have hgen := CFSG.SignalizerFunctor.Helpers.elementary_abelian_centralizer_generation 3 2
      Nat.prime_three A X hA.1 hlarge hAX hcX
    by_contra! hall
    apply hX
    rw [← hgen]
    exact iSup₂_le fun B hB => hall B hB.1 hB.2
  obtain ⟨B₁, hB₁A, hB₁, hSB⟩ := hB S hS hAS hcS
  obtain ⟨B₂, hB₂A, hB₂, hTB⟩ := hB T hT hAT hcT
  have hmeet : B₁ ⊓ B₂ ≠ ⊥ := by
    intro hbot
    have hinj : Function.Injective (fun x : B₁ × B₂ => (⟨(x.1 : G) * x.2, mul_mem
        (hB₁A x.1.2) (hB₂A x.2.2)⟩ : A)) := by
      rintro ⟨x₁, x₂⟩ ⟨y₁, y₂⟩ h
      have h' : (x₁ : G) * x₂ = y₁ * y₂ := congrArg Subtype.val h
      have hmem : (y₁ : G)⁻¹ * x₁ ∈ B₁ ⊓ B₂ := by
        refine Subgroup.mem_inf.mpr ⟨B₁.mul_mem (B₁.inv_mem y₁.2) x₁.2, ?_⟩
        have : (y₁ : G)⁻¹ * x₁ = y₂ * (x₂ : G)⁻¹ := by
          rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← h', mul_assoc, mul_inv_cancel, mul_one]
        rw [this]
        exact B₂.mul_mem y₂.2 (B₂.inv_mem x₂.2)
      rw [hbot, Subgroup.mem_bot, inv_mul_eq_one] at hmem
      have h₁ : x₁ = y₁ := Subtype.ext hmem.symm
      subst h₁
      have h₂ : (x₂ : G) = y₂ := mul_left_cancel h'
      rw [Subtype.ext h₂]
    have hle := Nat.card_le_card_of_injective _ hinj
    rw [Nat.card_prod, hB₁, hB₂, hA.2] at hle
    omega
  obtain ⟨⟨a, haB⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hmeet
  obtain ⟨haB₁, haB₂⟩ := Subgroup.mem_inf.mp haB
  refine ⟨a, hB₁A haB₁, fun h => ha1 (Subtype.ext h), fun h => hSB ?_, fun h => hTB ?_⟩
  · exact (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB₁))).trans h
  · exact (inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr haB₂))).trans h

omit [Finite G] in
theorem inf_centralizer_sup_eq_self {Y D X : Subgroup G} {a : G}
    (hYD : Y ≤ Subgroup.normalizer (D : Set G))
    (hY : (Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ D = Y) (hDX : D ≤ X) (hXY : X ≤ Y) :
    (X ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ D = X := by
  refine le_antisymm (sup_le inf_le_left hDX) fun x hx => ?_
  have hxY : x ∈ (((Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ D : Subgroup G) : Set G) := by
    rw [hY]
    exact hXY hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ (inf_le_left.trans hYD)] at hxY
  obtain ⟨y, hy, d, hd, rfl⟩ := Set.mem_mul.mp hxY
  have hyX : y ∈ X := by
    have h1 := mul_mem hx (inv_mem (hDX hd))
    rwa [mul_inv_cancel_right] at h1
  exact Subgroup.mul_mem_sup ⟨hyX, (Subgroup.mem_inf.mp hy).2⟩ hd

theorem inf_centralizer_mem_scriptQPiStar (hA : IsE27 A) (h146 : Item146 A LB)
    {Y D S : Subgroup G} {a : G} (haA : a ∈ A) (hD : D ∈ scriptQPi A LB Y (piOf 2))
    (hYD : Y ≤ Subgroup.normalizer (D : Set G))
    (hY : (Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ D = Y)
    (hS : S ∈ scriptQPiStar A LB Y (piOf 2)) (hDS : D ≤ S) :
    S ⊓ Subgroup.centralizer ({a} : Set G) ∈
      scriptQPiStar A LB (Y ⊓ Subgroup.centralizer ({a} : Set G)) (piOf 2) := by
  have hAab : IsMulCommutative A := hA.1.1
  have hAC : A ≤ Subgroup.normalizer
      ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    le_trans (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨b, hb⟩ ⟨a, haA⟩))) Subgroup.le_normalizer
  have hSY : S ≤ Y := hS.prop.1.2
  have hsplit := inf_centralizer_sup_eq_self hYD hY hDS hSY
  refine ⟨⟨⟨mem_scriptQ_of_le hS.prop.1.1 inf_le_left
      (le_normalizer_inf hS.prop.1.1.1.2.2 hAC), inf_le_inf_right _ hSY⟩,
    (isPiSubgroup_piOf_iff Nat.prime_two _).mpr
      ((isPGroup_of_mem_scriptQPi Nat.prime_two hS.prop).to_le inf_le_left)⟩, fun U hU hSU => ?_⟩
  have hUY : U ≤ Y := hU.1.2.trans inf_le_left
  have hU' : U ∈ scriptQPi A LB Y (piOf 2) := ⟨⟨hU.1.1, hUY⟩, hU.2⟩
  have hUD := sup_mem_scriptQPi_of_item146 hA h146 hU' hD (hUY.trans hYD)
  have hle : S ≤ U ⊔ D := by
    rw [← hsplit]
    exact sup_le_sup_right hSU D
  have heq : S = U ⊔ D := hS.eq_of_le hUD hle
  exact le_inf (le_sup_left.trans heq.ge) (hU.1.2.trans inf_le_right)

theorem transOn_of_residual (hA : IsE27 A) (hnat : IsNaturalFamily A LB)
    (h146 : Item146 A LB) {V Y : Subgroup G} (hVA : V ≤ Subgroup.normalizer (A : Set G))
    (hY : Y ∈ scriptY A) (hIH : ∀ Y' ∈ scriptY A, Y' < Y → TransOn A LB V Y')
    (hres : ∀ S ∈ scriptQPiStar A LB Y (piOf 2), ∀ T ∈ scriptQPiStar A LB Y (piOf 2),
      Y ≤ Subgroup.normalizer ((S ⊓ T : Subgroup G) : Set G) →
      (∀ S' ∈ scriptQPiStar A LB Y (piOf 2), ∀ T' ∈ scriptQPiStar A LB Y (piOf 2),
        Nat.card (S ⊓ T : Subgroup G) < Nat.card (S' ⊓ T' : Subgroup G) →
          IsConjIn (V ⊓ Y) S' T') →
      (∀ a ∈ A, a ≠ 1 → ¬ S ⊓ Subgroup.centralizer {a} ≤ S ⊓ T →
        ¬ T ⊓ Subgroup.centralizer {a} ≤ S ⊓ T → Y ≤ Subgroup.centralizer ({a} : Set G)) →
      IsConjIn (V ⊓ Y) S T) :
    TransOn A LB V Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAab : IsMulCommutative A := hA.1.1
  have hp : ∀ S ∈ scriptQPi A LB Y (piOf 2), IsPGroup 2 S :=
    fun S hS => isPGroup_of_mem_scriptQPi Nat.prime_two hS
  have hAinv : ∀ S ∈ scriptQPi A LB Y (piOf 2), A ≤ Subgroup.normalizer (S : Set G) :=
    fun S hS => hS.1.1.1.2.2
  have hW : ∀ S ∈ scriptQPi A LB Y (piOf 2), ∀ w ∈ V ⊓ Y,
      S.map (MulAut.conj w).toMonoidHom ∈ scriptQPi A LB Y (piOf 2) :=
    fun S hS w hw => Sec15.map_conj_mem_scriptQPi hnat (hVA (Subgroup.mem_inf.mp hw).1)
      (Subgroup.le_normalizer (Subgroup.mem_inf.mp hw).2) hS
  have hAC : ∀ a ∈ A, A ≤ Subgroup.normalizer
      ((Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
    fun a ha => le_trans (fun b hb => Subgroup.mem_centralizer_singleton_iff.mpr
      (congrArg Subtype.val (hAab.is_comm.comm ⟨b, hb⟩ ⟨a, ha⟩))) Subgroup.le_normalizer
  have hYsub : ∀ Y' : Subgroup G, Y' ≤ Y → A ≤ Subgroup.normalizer (Y' : Set G) →
      Y' ∈ scriptY A :=
    fun Y' hY'Y hAY' => ⟨fun htop => hY.1 (top_le_iff.mp (htop.symm.le.trans hY'Y)), hAY'⟩
  intro S hS T hT
  by_contra hST
  obtain ⟨S₀, T₀, hS₀, hT₀, hST₀, -, hmax⟩ :=
    Late.exists_max_pair (𝒬 := scriptQPi A LB Y (piOf 2)) (W := V ⊓ Y) hS hT hST
  have hS₀Y : S₀ ≤ Y := hS₀.prop.1.2
  have hT₀Y : T₀ ≤ Y := hT₀.prop.1.2
  have hAD : A ≤ Subgroup.normalizer ((S₀ ⊓ T₀ : Subgroup G) : Set G) :=
    le_normalizer_inf (hAinv S₀ hS₀.prop) (hAinv T₀ hT₀.prop)
  have hD𝒬 : S₀ ⊓ T₀ ∈ scriptQPi A LB Y (piOf 2) :=
    mem_scriptQPi_of_le hS₀.prop inf_le_left hAD
  have hDS : ¬ S₀ ≤ S₀ ⊓ T₀ := fun h => hST₀ (by
    rw [hS₀.eq_of_le hT₀.prop (h.trans inf_le_right)]
    exact isConjIn_refl _ T₀)
  have hDT : ¬ T₀ ≤ S₀ ⊓ T₀ := fun h => hST₀ (by
    rw [← hT₀.eq_of_le hS₀.prop (h.trans inf_le_left)]
    exact isConjIn_refl _ T₀)
  by_cases hYD : Y ≤ Subgroup.normalizer ((S₀ ⊓ T₀ : Subgroup G) : Set G)
  ·
    by_cases hgood : ∃ a ∈ A, a ≠ 1 ∧ ¬ S₀ ⊓ Subgroup.centralizer {a} ≤ S₀ ⊓ T₀ ∧
        ¬ T₀ ⊓ Subgroup.centralizer {a} ≤ S₀ ⊓ T₀ ∧ ¬ Y ≤ Subgroup.centralizer ({a} : Set G)
    swap
    ·
      exact hST₀ (hres S₀ hS₀ T₀ hT₀ hYD (fun S' hS' T' hT' hlt => hmax S' T' hS' hT' hlt)
        fun a ha ha1 hSa hTa => by_contra fun hYa => hgood ⟨a, ha, ha1, hSa, hTa, hYa⟩)
    obtain ⟨a, haA, ha1, hSa, hTa, hYa⟩ := hgood
    have hAYa : A ≤ Subgroup.normalizer
        ((Y ⊓ Subgroup.centralizer ({a} : Set G) : Subgroup G) : Set G) :=
      le_normalizer_inf hY.2 (hAC a haA)
    by_cases hYeq : (Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀) = Y
    ·
      have hlt : Y ⊓ Subgroup.centralizer ({a} : Set G) < Y :=
        lt_of_le_of_ne inf_le_left fun h => hYa (h.symm.le.trans inf_le_right)
      have htr := hIH _ (hYsub _ inf_le_left hAYa) hlt
      obtain ⟨w, hw, hwT⟩ := htr _ (inf_centralizer_mem_scriptQPiStar hA h146 haA hD𝒬 hYD hYeq
        hS₀ inf_le_left) _ (inf_centralizer_mem_scriptQPiStar hA h146 haA hD𝒬 hYD hYeq hT₀
        inf_le_right)
      have hwV : w ∈ V := (Subgroup.mem_inf.mp hw).1
      have hwY : w ∈ Y := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hw).2).1
      have hDw : (S₀ ⊓ T₀).map (MulAut.conj w).toMonoidHom = S₀ ⊓ T₀ :=
        Late.map_conj_eq_of_mem_normalizer (hYD hwY)
      apply hST₀
      refine ⟨w, Subgroup.mem_inf.mpr ⟨hwV, hwY⟩, ?_⟩
      calc T₀ = (T₀ ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀) :=
            (inf_centralizer_sup_eq_self hYD hYeq inf_le_right hT₀Y).symm
        _ = (S₀ ⊓ Subgroup.centralizer ({a} : Set G)).map (MulAut.conj w).toMonoidHom ⊔
              (S₀ ⊓ T₀).map (MulAut.conj w).toMonoidHom := by rw [← hwT, hDw]
        _ = ((S₀ ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀)).map
              (MulAut.conj w).toMonoidHom := (Subgroup.map_sup _ _ _).symm
        _ = S₀.map (MulAut.conj w).toMonoidHom := by
            rw [inf_centralizer_sup_eq_self hYD hYeq inf_le_left hS₀Y]
    ·
      have hY'le : (Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀) ≤ Y :=
        sup_le inf_le_left (inf_le_left.trans hS₀Y)
      have hloc := isLocallyTransitive_of_transOn hY'le
        (hIH _ (hYsub _ hY'le (le_normalizer_sup hAYa hAD)) (lt_of_le_of_ne hY'le hYeq))
      have grow : ∀ X : Subgroup G, Maximal (· ∈ scriptQPi A LB Y (piOf 2)) X →
          S₀ ⊓ T₀ ≤ X → ¬ X ⊓ Subgroup.centralizer {a} ≤ S₀ ⊓ T₀ →
          (X ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀) ∈ scriptQPi A LB Y (piOf 2) ∧
          (X ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀) ≤ X ∧
          (X ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀) ≤
            (Y ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀) ∧
          Nat.card (S₀ ⊓ T₀ : Subgroup G) <
            Nat.card ((X ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀) : Subgroup G) := by
        intro X hX hDX hXa
        have hRX : (X ⊓ Subgroup.centralizer ({a} : Set G)) ⊔ (S₀ ⊓ T₀) ≤ X :=
          sup_le inf_le_left hDX
        refine ⟨mem_scriptQPi_of_le hX.prop hRX (le_normalizer_sup
            (le_normalizer_inf (hAinv X hX.prop) (hAC a haA)) hAD), hRX,
          sup_le_sup_right (inf_le_inf_right _ hX.prop.1.2) _,
          Subgroup.card_lt_of_lt (lt_of_le_of_ne le_sup_right fun h => hXa ?_)⟩
        rw [h]
        exact le_sup_left
      obtain ⟨hR₁, hR₁S, hR₁Y, h₁⟩ := grow S₀ hS₀ inf_le_left hSa
      obtain ⟨hR₂, hR₂T, hR₂Y, h₂⟩ := grow T₀ hT₀ inf_le_right hTa
      exact hST₀ (isConjIn_of_local hW hmax hS₀ hT₀ hloc hR₁ hR₁S hR₁Y h₁ hR₂ hR₂T hR₂Y h₂)
  ·
    have hY'le : Y ⊓ Subgroup.normalizer ((S₀ ⊓ T₀ : Subgroup G) : Set G) ≤ Y := inf_le_left
    have hloc := isLocallyTransitive_of_transOn hY'le
      (hIH _ (hYsub _ hY'le (le_normalizer_inf hY.2 (hAD.trans Subgroup.le_normalizer)))
        (inf_lt_left.mpr hYD))
    have grow : ∀ X : Subgroup G, Maximal (· ∈ scriptQPi A LB Y (piOf 2)) X →
        S₀ ⊓ T₀ ≤ X → ¬ X ≤ S₀ ⊓ T₀ →
        X ⊓ Subgroup.normalizer ((S₀ ⊓ T₀ : Subgroup G) : Set G) ∈
            scriptQPi A LB Y (piOf 2) ∧
          X ⊓ Subgroup.normalizer ((S₀ ⊓ T₀ : Subgroup G) : Set G) ≤ X ∧
          X ⊓ Subgroup.normalizer ((S₀ ⊓ T₀ : Subgroup G) : Set G) ≤
            Y ⊓ Subgroup.normalizer ((S₀ ⊓ T₀ : Subgroup G) : Set G) ∧
          Nat.card (S₀ ⊓ T₀ : Subgroup G) <
            Nat.card (X ⊓ Subgroup.normalizer ((S₀ ⊓ T₀ : Subgroup G) : Set G) :
              Subgroup G) := by
      intro X hX hDX hXD
      obtain ⟨x, hxX, hxD, hxN⟩ := Late.exists_mem_normalizer_not_mem_of_lt (hp X hX.prop)
        (lt_of_le_of_ne hDX fun h => hXD h.ge)
      refine ⟨mem_scriptQPi_of_le hX.prop inf_le_left
          (le_normalizer_inf (hAinv X hX.prop) (hAD.trans Subgroup.le_normalizer)), inf_le_left,
        inf_le_inf_right _ hX.prop.1.2,
        Subgroup.card_lt_of_lt (lt_of_le_of_ne (le_inf hDX Subgroup.le_normalizer) ?_)⟩
      intro heq
      exact hxD (heq ▸ (⟨hxX, hxN⟩ :
        x ∈ X ⊓ Subgroup.normalizer ((S₀ ⊓ T₀ : Subgroup G) : Set G)))
    obtain ⟨hR₁, hR₁S, hR₁Y, h₁⟩ := grow S₀ hS₀ inf_le_left hDS
    obtain ⟨hR₂, hR₂T, hR₂Y, h₂⟩ := grow T₀ hT₀ inf_le_right hDT
    exact hST₀ (isConjIn_of_local hW hmax hS₀ hT₀ hloc hR₁ hR₁S hR₁Y h₁ hR₂ hR₂T hR₂Y h₂)

end CFSG.RankThree.PartTwo.Sec14
