module

public import CFSG.Quasithin.H13.A6S13821M22b
public import CFSG.LocalAnalysis.ComponentClassification.WittDesignM22Actions

public section

namespace CFSG.Quasithin.H13.A6.HatM22

open CFSG.Open CFSG.Quasithin CFSG.ComponentClassification.WittDesign MulAction
open scoped Pointwise commutatorElement

theorem commutator_sup_center_le {X : Type*} [Group X] (A Z : Subgroup X)
    (hZ : Z ≤ Subgroup.center X) : ⁅A ⊔ Z, A ⊔ Z⁆ ≤ ⁅A, A⁆ := by
  have hZn : Z.Normal := ⟨fun z hz g => by
    rw [Subgroup.mem_center_iff.mp (hZ hz) g, mul_inv_cancel_right]
    exact hz⟩
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [← SetLike.mem_coe, Subgroup.mul_normal] at ha hb
  obtain ⟨a₁, ha₁, z₁, hz₁, rfl⟩ := ha
  obtain ⟨b₁, hb₁, z₂, hz₂, rfl⟩ := hb
  have c1 := Subgroup.mem_center_iff.mp (hZ hz₁)
  have c2 := Subgroup.mem_center_iff.mp (hZ hz₂)
  have e : ⁅a₁ * z₁, b₁ * z₂⁆ = ⁅a₁, b₁⁆ := by
    rw [commutatorElement_def, commutatorElement_def]
    calc a₁ * z₁ * (b₁ * z₂) * (a₁ * z₁)⁻¹ * (b₁ * z₂)⁻¹
        = a₁ * (z₁ * (b₁ * z₂)) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * b₁⁻¹ := by group
      _ = a₁ * (b₁ * z₂ * z₁) * z₁⁻¹ * a₁⁻¹ * z₂⁻¹ * b₁⁻¹ := by rw [← c1 (b₁ * z₂)]
      _ = a₁ * b₁ * (z₂ * a₁⁻¹) * z₂⁻¹ * b₁⁻¹ := by group
      _ = a₁ * b₁ * (a₁⁻¹ * z₂) * z₂⁻¹ * b₁⁻¹ := by rw [← c2 a₁⁻¹]
      _ = a₁ * b₁ * a₁⁻¹ * b₁⁻¹ := by group
  rw [e]
  exact Subgroup.commutator_mem_commutator ha₁ hb₁

theorem mem_of_odd_of_relIndex_two_pow {X : Type*} [Group X] {N P : Subgroup X} (hNP : N ≤ P)
    (hPN : P ≤ Subgroup.normalizer (N : Set X)) {j : ℕ} (hidx : N.relIndex P = 2 ^ j)
    [Finite ↥P] {x : X} (hx : x ∈ P) {m : ℕ} (hm : Odd m) (hxm : x ^ m = 1) : x ∈ N := by
  have : (N.subgroupOf P).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hNP).mpr hPN
  have h1 : (QuotientGroup.mk (⟨x, hx⟩ : ↥P) : ↥P ⧸ N.subgroupOf P) ^ 2 ^ j = 1 := by
    rw [← hidx]
    exact pow_card_eq_one'
  have h2 : (QuotientGroup.mk (⟨x, hx⟩ : ↥P) : ↥P ⧸ N.subgroupOf P) ^ m = 1 := by
    rw [← QuotientGroup.mk_pow]
    have e : (⟨x, hx⟩ : ↥P) ^ m = 1 := Subtype.ext (by simpa using hxm)
    rw [e, QuotientGroup.mk_one]
  have hg : Nat.gcd (2 ^ j) m = 1 := Nat.Coprime.pow_left j (Nat.coprime_two_left.mpr hm)
  have h3 := pow_gcd_eq_one.mpr ⟨h1, h2⟩
  rw [hg, pow_one, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf] at h3
  exact h3

theorem map_perfectCore_resHexad
    {B : Finset (Fin 22)}
    (hB : B ∈ hexads) :
    (perfectCore (⊤ : Subgroup ↥(stabilizer M22 B))).map (resHexad B) = alternatingGroup ↥B := by
  rw [map_perfectCore, ← MonoidHom.range_eq_map, range_resHexad hB]
  exact perfectCore_eq_self_of_perfect (commutator_alternatingGroup_eq_self (by
    rw [Nat.card_eq_fintype_card, card_hexad_type hB]
    norm_num))

theorem relIndex_perfectCore_stabilizer_dvd
    {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    (perfectCore (stabilizer M22 B)).relIndex (stabilizer M22 B) ∣ 16 := by
  set Bst := stabilizer M22 B with hBst
  set C := perfectCore (⊤ : Subgroup ↥Bst) with hC
  have hCB : (perfectCore Bst).subgroupOf Bst = C := by
    have h1 := map_perfectCore Bst.subtype (⊤ : Subgroup ↥Bst)
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
    rw [← h1]
    exact Subgroup.comap_map_eq_self_of_injective Bst.subtype_injective C
  have hsup : (resHexad B).ker ⊔ C = ⊤ := by
    have h1 := Subgroup.comap_map_eq (resHexad B) C
    rw [map_perfectCore_resHexad hB, ← range_resHexad hB, MonoidHom.range_eq_map,
      Subgroup.comap_map_eq, top_sup_eq] at h1
    rw [sup_comm, ← h1]
  have hN : (resHexad B).ker ≤ Subgroup.normalizer (C : Set ↥Bst) := fun x _ =>
    normalizer_le_normalizer_perfectCore (⊤ : Subgroup ↥Bst)
      (Subgroup.mem_normalizer_iff.mpr fun g => ⟨fun _ => Subgroup.mem_top _,
        fun _ => Subgroup.mem_top _⟩)
  rw [Subgroup.relIndex, hCB, ← Subgroup.relIndex_top_right, ← hsup,
    A4.relIndex_sup_eq_of_le_normalizer' hN, ← card_ker_resHexad hB]
  exact Subgroup.relIndex_dvd_card (H := C) (K := (resHexad B).ker)

variable {Q : Type} [Group Q] [Finite Q]

@[expose] noncomputable def rhoM (φ : Q ⧸ Subgroup.center Q ≃* M22) : Q →* M22 :=
  φ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q))

omit [Finite Q] in
theorem rhoM_surjective (φ : Q ⧸ Subgroup.center Q ≃* M22) : Function.Surjective (rhoM φ) :=
  φ.surjective.comp (QuotientGroup.mk'_surjective _)

omit [Finite Q] in
theorem ker_rhoM (φ : Q ⧸ Subgroup.center Q ≃* M22) : (rhoM φ).ker = Subgroup.center Q := by
  ext x
  rw [MonoidHom.mem_ker, rhoM, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

theorem map_perfectCore_comap (φ : Q ⧸ Subgroup.center Q ≃* M22) (B : Finset (Fin 22)) :
    (perfectCore ((stabilizer M22 B).comap (rhoM φ))).map (rhoM φ) =
      perfectCore (stabilizer M22 B) := by
  rw [map_perfectCore, Subgroup.map_comap_eq_self_of_surjective (rhoM_surjective φ)]

theorem center_le_perfectCore
    (hQ : commutator Q = ⊤)
    (hZ3 : Nat.card (Subgroup.center Q) = 3) (φ : Q ⧸ Subgroup.center Q ≃* M22)
    {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    Subgroup.center Q ≤ perfectCore ((stabilizer M22 B).comap (rhoM φ)) := by
  set W := perfectCore ((stabilizer M22 B).comap (rhoM φ)) with hW
  set Y := (perfectCore (stabilizer M22 B)).comap (rhoM φ) with hYdef
  have hY : Y = W ⊔ Subgroup.center Q := by
    rw [hYdef, ← map_perfectCore_comap φ B, Subgroup.comap_map_eq, ker_rhoM]
  have hidx : Nat.Coprime Y.index 3 := by
    rw [hYdef, Subgroup.index_comap_of_surjective _ (rhoM_surjective φ),
      ← Subgroup.relIndex_mul_index (perfectCore_le _), index_stabilizer_hexad hB]
    exact Nat.Coprime.mul_left (Nat.Coprime.coprime_dvd_left
      (relIndex_perfectCore_stabilizer_dvd hB) (by norm_num)) (by norm_num)
  intro z hz
  obtain ⟨hzY, hzc⟩ := pow_index_mem_commutator hQ Y hz
  have h1 : z ^ Y.index ∈ ⁅Y, Y⁆ := by
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨_, hzc, rfl⟩
  have h2 : ⁅Y, Y⁆ ≤ W := by
    rw [hY]
    exact (commutator_sup_center_le W _ le_rfl).trans (perfectCore_perfect _).le
  have h3 := h2 h1
  have hz3 : z ^ 3 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center Q) (x := ⟨z, hz⟩)
    rw [hZ3] at this
    simpa using congrArg Subtype.val this
  set n := Y.index with hn
  have hnn : (n * n) % 3 = 1 := by
    have h3n : ¬ 3 ∣ n := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp hidx.symm
    have h' : n % 3 = 1 ∨ n % 3 = 2 := by omega
    rw [Nat.mul_mod]
    rcases h' with h | h <;> rw [h]
  have e : z = (z ^ n) ^ n := by
    rw [← pow_mul, ← Nat.div_add_mod (n * n) 3, hnn, pow_add, pow_mul, hz3, one_pow, one_mul,
      pow_one]
  rw [e]
  exact W.pow_mem h3 n

theorem isHat_perfectCore
    (hHat : IsHat Q (CFSG.Blueprint.NativeSporadic.Carrier .M22))
    (φ : Q ⧸ Subgroup.center Q ≃* M22) {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    IsHat (↥(perfectCore ((stabilizer M22 B).comap (rhoM φ))) ⧸
      CFSG.pCore 2 ↥(perfectCore ((stabilizer M22 B).comap (rhoM φ))))
      ↥(alternatingGroup (Fin 6)) := by
  classical
  set Bst := stabilizer M22 B with hBst
  set Q₁ := Bst.comap (rhoM φ) with hQ₁
  set W := perfectCore Q₁ with hW
  have hQ : commutator Q = ⊤ := Group.isPerfect_def.mp hHat.1.1
  have hZW : Subgroup.center Q ≤ W := center_le_perfectCore hQ hHat.2.1 φ hB
  have hker := ker_rhoM φ
  have hWmap : W.map (rhoM φ) = perfectCore Bst := map_perfectCore_comap φ B
  have hWp : commutator ↥W = ⊤ := by
    have : Group.IsPerfect ↥W := Subgroup.isPerfect_iff.mpr (perfectCore_perfect Q₁)
    exact Group.isPerfect_def.mp this
  let ψ : ↥W →* ↥Bst :=
    ((rhoM φ).comp W.subtype).codRestrict Bst fun w => perfectCore_le Q₁ w.2
  have hψ : ∀ w : ↥W, ((ψ w : ↥Bst) : M22) = rhoM φ w := fun w => rfl
  let e : ↥B ≃ Fin 6 := Fintype.equivFinOfCardEq (card_hexad_type hB)
  have hmemA : ∀ w : ↥W, resHexad B (ψ w) ∈ alternatingGroup ↥B := fun w => by
    rw [← range_resHexad hB]
    exact ⟨_, rfl⟩
  let f₀ : ↥W →* ↥(alternatingGroup ↥B) := ((resHexad B).comp ψ).codRestrict _ hmemA
  let f : ↥W →* ↥(alternatingGroup (Fin 6)) := (Equiv.altCongrHom e).toMonoidHom.comp f₀
  have hf₀ : Function.Surjective f₀ := by
    rintro ⟨σ, hσ⟩
    rw [← map_perfectCore_resHexad hB] at hσ
    obtain ⟨c, hc, rfl⟩ := hσ
    have hc' : (c : M22) ∈ W.map (rhoM φ) := by
      have h1 := Subgroup.mem_map_of_mem Bst.subtype hc
      rw [map_perfectCore, ← MonoidHom.range_eq_map, Subgroup.range_subtype] at h1
      rw [hWmap]
      exact h1
    obtain ⟨w, hw, hwc⟩ := hc'
    refine ⟨⟨w, hw⟩, Subtype.ext ?_⟩
    show resHexad B (ψ ⟨w, hw⟩) = resHexad B c
    congr 1
    exact Subtype.ext hwc
  have hf : Function.Surjective f := (Equiv.altCongrHom e).surjective.comp hf₀
  set Z := (Subgroup.center Q).subgroupOf W with hZ
  have hZc : Z ≤ Subgroup.center ↥W := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext ((Subgroup.mem_center_iff.mp (Subgroup.mem_subgroupOf.mp hz)) (g : Q))
  have hZ3 : Nat.card Z = 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZW).toEquiv, hHat.2.1]
  have hZk : Z ≤ f.ker := by
    intro z hz
    have hρz : rhoM φ z = 1 := by
      rw [← MonoidHom.mem_ker, hker]
      exact Subgroup.mem_subgroupOf.mp hz
    have h1 : ψ z = 1 := Subtype.ext hρz
    have h2 : f₀ z = 1 := Subtype.ext (by
      show resHexad B (ψ z) = 1
      rw [h1, map_one])
    rw [MonoidHom.mem_ker]
    show (Equiv.altCongrHom e) (f₀ z) = 1
    rw [h2, map_one]
  have h2 : ∀ x ∈ f.ker, x ^ 2 ∈ Z := by
    intro x hx
    have h1 : f₀ x = 1 := (Equiv.altCongrHom e).injective (by
      rw [map_one]
      exact hx)
    have h3 : ψ x ∈ (resHexad B).ker := congrArg Subtype.val h1
    have h4 := kernelSubgroup_sq hB (mem_ker_resHexad.mp h3)
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_pow, ← hker, MonoidHom.mem_ker, map_pow, sq]
    rw [hψ] at h4
    exact h4
  exact isHat_of_cover hWp f hf Z hZc hZ3 hZk h2

theorem relIndex_perfectCore_comap_dvd
    (hQ : commutator Q = ⊤) (hZ3 : Nat.card (Subgroup.center Q) = 3)
    (φ : Q ⧸ Subgroup.center Q ≃* M22) {B : Finset (Fin 22)} (hB : B ∈ hexads) :
    (perfectCore ((stabilizer M22 B).comap (rhoM φ))).relIndex
      ((stabilizer M22 B).comap (rhoM φ)) ∣ 16 := by
  have hZW := center_le_perfectCore hQ hZ3 φ hB
  have hWeq : perfectCore ((stabilizer M22 B).comap (rhoM φ)) =
      (perfectCore (stabilizer M22 B)).comap (rhoM φ) := by
    rw [← map_perfectCore_comap φ B, Subgroup.comap_map_eq, ker_rhoM, sup_eq_left.mpr hZW]
  rw [hWeq, Subgroup.relIndex_comap,
    Subgroup.map_comap_eq_self_of_surjective (rhoM_surjective φ)]
  exact relIndex_perfectCore_stabilizer_dvd hB

end CFSG.Quasithin.H13.A6.HatM22
