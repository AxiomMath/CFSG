module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.RankThree.PartTwo.Sec15.Item153Twin2ProofTypesTools
import CFSG.RankThree.PartTwo.Sec15.Item15Res8ProofDiag
import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofCases
import CFSG.GroupTheory.PerfectLeSupCenter
import CFSG.GroupTheory.QuasisimpleCommutingProductBound
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof155P

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14
  CFSG.RankThree.LocalRank

private theorem isQuasisimple_alternating_five :
    CFSG.IsQuasisimple (alternatingGroup (Fin 5)) := by
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
    Y4Core.isSimpleGroup_alternatingGroup 5 (by norm_num)
  exact (Y4Core.good3_of_isSimpleGroup Y4Core.alternatingGroup_five_nonabelian
    (Y4Core.three_dvd_card_alternatingGroup 5 (by norm_num))).1

private theorem center_map_le_center_of_commutator_eq_bot {T : Type*} [Group T]
    {U₀ V₀ : Subgroup T} [V₀.Normal] (hsup : U₀ ⊔ V₀ = ⊤) (hcomm : ⁅U₀, V₀⁆ = ⊥) :
    (Subgroup.center ↥U₀).map U₀.subtype ≤ Subgroup.center T := by
  have hUV : U₀ ≤ Subgroup.centralizer (V₀ : Set T) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  rintro _ ⟨z, hz, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  have hg : g ∈ U₀ ⊔ V₀ := hsup ▸ Subgroup.mem_top g
  obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
  have hzu : (z : T) * u = u * (z : T) := (congrArg Subtype.val
    (Subgroup.mem_center_iff.mp hz ⟨u, hu⟩)).symm
  have hzv : (z : T) * v = v * (z : T) :=
    (Subgroup.mem_centralizer_iff.mp (hUV z.2) v hv).symm
  calc (u * v) * (z : T) = u * (v * (z : T)) := by group
    _ = u * ((z : T) * v) := by rw [hzv]
    _ = (u * (z : T)) * v := by group
    _ = ((z : T) * u) * v := by rw [hzu]
    _ = (z : T) * (u * v) := by group

private theorem eq_of_le_of_sup_center_eq {T : Type*} [Group T] {J P Z : Subgroup T}
    (hJ : ⁅J, J⁆ = J) (hP : ⁅P, P⁆ = P) (hJP : J ≤ P) (hZ : Z ≤ Subgroup.center T)
    (hsup : J ⊔ Z = P) : J = P := by
  refine le_antisymm hJP (CFSG.le_of_perfect_of_le_sup_center hJ hP ?_)
  rw [← hsup]
  exact sup_le_sup_left hZ J

private theorem inf_eq_bot_of_normal_of_not_three_dvd {T : Type*} [Group T] [Finite T]
    {N W : Subgroup T} [W.Normal] (hN : N.Normal) (hWq : CFSG.IsQuasisimple ↥W)
    (hW3 : 3 ∣ Nat.card W) (hZW : Nat.card (Subgroup.center ↥W) ∣ 3)
    (hN3 : ¬ 3 ∣ Nat.card N) : N ⊓ W = ⊥ := by
  haveI : N.Normal := hN
  haveI : (N ⊓ W).Normal := Subgroup.normal_inf_normal N W
  have hMn : ((N ⊓ W).subgroupOf W).Normal := Subgroup.normal_subgroupOf
  rcases CFSG.LocalCores.quasisimple_normal_subgroups hWq hMn with htop | hcen
  · exfalso
    apply hN3
    have hle : W ≤ N := by
      intro x hx
      have hmem : (⟨x, hx⟩ : ↥W) ∈ (N ⊓ W).subgroupOf W :=
        htop ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥W)
      rw [Subgroup.mem_subgroupOf] at hmem
      exact hmem.1
    exact hW3.trans (Subgroup.card_dvd_of_le hle)
  · have hcard3 : Nat.card ↥(N ⊓ W) ∣ 3 := by
      calc Nat.card ↥(N ⊓ W) = Nat.card ↥((N ⊓ W).subgroupOf W) :=
            (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : N ⊓ W ≤ W)).toEquiv).symm
        _ ∣ Nat.card (Subgroup.center ↥W) := Subgroup.card_dvd_of_le hcen
        _ ∣ 3 := hZW
    have hnot3 : ¬ 3 ∣ Nat.card ↥(N ⊓ W) :=
      fun h => hN3 (h.trans (Subgroup.card_dvd_of_le inf_le_left))
    rcases (Nat.dvd_prime Nat.prime_three).mp hcard3 with h | h
    · exact (Subgroup.card_eq_one).mp h
    · exact absurd (by rw [h]) hnot3

private theorem normal_eq_bot_of_not_three_dvd {T : Type*} [Group T] [Finite T]
    {U₀ V₀ : Subgroup T} [U₀.Normal] [V₀.Normal]
    (hsup : U₀ ⊔ V₀ = ⊤) (hcomm : ⁅U₀, V₀⁆ = ⊥)
    (hUq : CFSG.IsQuasisimple ↥U₀) (hVq : CFSG.IsQuasisimple ↥V₀)
    (hU3 : 3 ∣ Nat.card U₀) (hV3 : 3 ∣ Nat.card V₀)
    (hZU : Nat.card (Subgroup.center ↥U₀) ∣ 3)
    (hZV : Nat.card (Subgroup.center ↥V₀) ∣ 3)
    {N : Subgroup T} (hN : N.Normal) (hN3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  classical
  have hNU : N ⊓ U₀ = ⊥ := inf_eq_bot_of_normal_of_not_three_dvd hN hUq hU3 hZU hN3
  have hNV : N ⊓ V₀ = ⊥ := inf_eq_bot_of_normal_of_not_three_dvd hN hVq hV3 hZV hN3
  have hNZ : N ≤ Subgroup.center T := by
    haveI : N.Normal := hN
    have hNUc : ⁅N, U₀⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact (le_inf (Subgroup.commutator_le_left N U₀)
        (Subgroup.commutator_le_right N U₀)).trans (le_of_eq hNU)
    have hNVc : ⁅N, V₀⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact (le_inf (Subgroup.commutator_le_left N V₀)
        (Subgroup.commutator_le_right N V₀)).trans (le_of_eq hNV)
    have hNcU : N ≤ Subgroup.centralizer (U₀ : Set T) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hNUc
    have hNcV : N ≤ Subgroup.centralizer (V₀ : Set T) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hNVc
    intro n hn
    rw [Subgroup.mem_center_iff]
    intro g
    have hg : g ∈ U₀ ⊔ V₀ := hsup ▸ Subgroup.mem_top g
    obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hg
    have hnu : u * n = n * u := Subgroup.mem_centralizer_iff.mp (hNcU hn) u hu
    have hnv : v * n = n * v := Subgroup.mem_centralizer_iff.mp (hNcV hn) v hv
    calc (u * v) * n = u * (v * n) := by group
      _ = u * (n * v) := by rw [hnv]
      _ = (u * n) * v := by group
      _ = (n * u) * v := by rw [hnu]
      _ = n * (u * v) := by group
  have hcenter_dvd : Nat.card (Subgroup.center T) ∣ 9 := by
    set A := (Subgroup.center ↥U₀).map U₀.subtype with hA
    set B := (Subgroup.center ↥V₀).map V₀.subtype with hB
    have hZA : A ≤ Subgroup.center T := by
      rw [hA]
      exact center_map_le_center_of_commutator_eq_bot hsup hcomm
    have hZB : B ≤ Subgroup.center T := by
      rw [hB]
      exact center_map_le_center_of_commutator_eq_bot (by rw [sup_comm]; exact hsup)
        (by rw [Subgroup.commutator_comm]; exact hcomm)
    have hcm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
      (Subgroup.mem_center_iff.mp (hZA ha) b).symm
    have hZle : Subgroup.center T ≤ A ⊔ B := by
      intro z hz
      have hzT : z ∈ U₀ ⊔ V₀ := hsup ▸ Subgroup.mem_top z
      obtain ⟨u, hu, v, hv, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hzT
      have huA : u ∈ A := by
        have hmem : (⟨u, hu⟩ : ↥U₀) ∈ Subgroup.center ↥U₀ := by
          rw [Subgroup.mem_center_iff]
          intro x
          apply Subtype.ext
          have h1 : (x : T) * (u * v) = (u * v) * (x : T) :=
            Subgroup.mem_center_iff.mp hz (x : T)
          have h2 : v * (x : T) = (x : T) * v :=
            Subgroup.mem_centralizer_iff.mp
              (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm x.2) v hv
          have h4 : (x : T) * u * v = u * (x : T) * v := by
            calc (x : T) * u * v = (x : T) * (u * v) := by group
              _ = (u * v) * (x : T) := h1
              _ = u * (v * (x : T)) := by group
              _ = u * ((x : T) * v) := by rw [h2]
              _ = u * (x : T) * v := by group
          exact mul_right_cancel h4
        exact ⟨⟨u, hu⟩, hmem, rfl⟩
      have hvB : v ∈ B := by
        have hmem : (⟨v, hv⟩ : ↥V₀) ∈ Subgroup.center ↥V₀ := by
          rw [Subgroup.mem_center_iff]
          intro y
          apply Subtype.ext
          have h1 : (y : T) * (u * v) = (u * v) * (y : T) :=
            Subgroup.mem_center_iff.mp hz (y : T)
          have h2 : u * (y : T) = (y : T) * u :=
            (Subgroup.mem_centralizer_iff.mp
              ((Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm) hu) (y : T) y.2).symm
          have h4 : u * ((y : T) * v) = u * (v * (y : T)) := by
            calc u * ((y : T) * v) = u * (y : T) * v := by group
              _ = (y : T) * u * v := by rw [← h2]
              _ = (y : T) * (u * v) := by group
              _ = (u * v) * (y : T) := h1
              _ = u * (v * (y : T)) := by group
          exact mul_left_cancel h4
        exact ⟨⟨v, hv⟩, hmem, rfl⟩
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left huA) (Subgroup.mem_sup_right hvB)
    have hdvd1 : Nat.card (Subgroup.center T) ∣ Nat.card ↥(A ⊔ B) :=
      Subgroup.card_dvd_of_le hZle
    have hcardZ : Nat.card (Subgroup.center T) ∣ Nat.card A * Nat.card B := by
      have h2 : Nat.card ↥(A ⊔ B) * Nat.card ↥(A ⊓ B) = Nat.card A * Nat.card B :=
        (CFSG.GroupTheory.card_sup_mul_card_inf_of_commute A B hcm).1
      exact hdvd1.trans ⟨Nat.card ↥(A ⊓ B), h2.symm⟩
    have hcardA : Nat.card A = Nat.card (Subgroup.center ↥U₀) := by
      rw [hA]
      exact Subgroup.card_map_of_injective U₀.subtype_injective
    have hcardB : Nat.card B = Nat.card (Subgroup.center ↥V₀) := by
      rw [hB]
      exact Subgroup.card_map_of_injective V₀.subtype_injective
    rw [hcardA, hcardB] at hcardZ
    have hfin : Nat.card (Subgroup.center ↥U₀) * Nat.card (Subgroup.center ↥V₀) ∣ 9 :=
      (Nat.mul_dvd_mul hZU hZV).trans (by norm_num : 3 * 3 ∣ 9)
    exact hcardZ.trans hfin
  have hN9 : Nat.card N ∣ 9 := (Subgroup.card_dvd_of_le hNZ).trans hcenter_dvd
  have hN1 : Nat.card N = 1 := by
    have hN9' : Nat.card N ∣ 3 ^ 2 := by
      rw [show (3 : ℕ) ^ 2 = 9 from by norm_num]
      exact hN9
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hN9'
    have hk0 : k = 0 := by
      by_contra hk0
      have hkpos : 0 < k := Nat.pos_of_ne_zero hk0
      have h3 : 3 ∣ 3 ^ k := by
        have h := pow_dvd_pow 3 hkpos
        rwa [pow_one] at h
      have h35 : 3 ∣ Nat.card N := by rw [hk]; exact h3
      exact hN3 h35
    rw [hk, hk0]
    norm_num
  exact Subgroup.card_eq_one.mp hN1

private theorem normal_eq_bot_five_five
    {N : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5))}
    (hN : N.Normal) (hN3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  classical
  set W₁ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    (MonoidHom.snd (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).ker with hW₁
  set W₂ : Subgroup (alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) :=
    (MonoidHom.fst (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).ker with hW₂
  haveI hW₁n : W₁.Normal := by rw [hW₁]; infer_instance
  haveI hW₂n : W₂.Normal := by rw [hW₂]; infer_instance
  have hmem1 : ∀ a : alternatingGroup (Fin 5), (a, 1) ∈ W₁ := by
    intro a
    rw [hW₁]
    exact MonoidHom.mem_ker.mpr rfl
  have hmem2 : ∀ b : alternatingGroup (Fin 5), (1, b) ∈ W₂ := by
    intro b
    rw [hW₂]
    exact MonoidHom.mem_ker.mpr rfl
  have hker1 : ∀ (a b : alternatingGroup (Fin 5)), (a, b) ∈ W₁ → b = 1 := by
    intro a b hab
    have h1 : (a, b) ∈ (MonoidHom.snd (alternatingGroup (Fin 5))
        (alternatingGroup (Fin 5))).ker := by
      rw [← hW₁]
      exact hab
    exact MonoidHom.mem_ker.mp h1
  have hker2 : ∀ (a b : alternatingGroup (Fin 5)), (a, b) ∈ W₂ → a = 1 := by
    intro a b hab
    have h1 : (a, b) ∈ (MonoidHom.fst (alternatingGroup (Fin 5))
        (alternatingGroup (Fin 5))).ker := by
      rw [← hW₂]
      exact hab
    exact MonoidHom.mem_ker.mp h1
  have hsup : W₁ ⊔ W₂ = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨a, b⟩ -
    have h : ((a, b) : alternatingGroup (Fin 5) × alternatingGroup (Fin 5)) =
        (a, 1) * (1, b) := by simp
    rw [h]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hmem1 a))
      (Subgroup.mem_sup_right (hmem2 b))
  have hinf : W₁ ⊓ W₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro ⟨a, b⟩ ⟨ha, hb⟩
    rw [Subgroup.mem_bot]
    simp [hker1 a b ha, hker2 a b hb]
  have hcomm : ⁅W₁, W₂⁆ = ⊥ := by
    rw [eq_bot_iff]
    exact (le_inf (Subgroup.commutator_le_left W₁ W₂)
      (Subgroup.commutator_le_right W₁ W₂)).trans (le_of_eq hinf)
  let φ₁ : alternatingGroup (Fin 5) →* W₁ := (MonoidHom.inl _ _).codRestrict W₁ hmem1
  let ψ₁ : W₁ →* alternatingGroup (Fin 5) :=
    (MonoidHom.fst (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).comp W₁.subtype
  have hleft₁ : ∀ a, ψ₁ (φ₁ a) = a := fun a => rfl
  have hright₁ : ∀ x : W₁, φ₁ (ψ₁ x) = x := by
    rintro ⟨⟨a, b⟩, hab⟩
    have hb : b = 1 := hker1 a b hab
    subst hb
    rfl
  have hφ₁i : Function.Injective φ₁ := fun a a' h => by
    have h := congrArg ψ₁ h
    rwa [hleft₁, hleft₁] at h
  have hφ₁s : Function.Surjective φ₁ := fun x => ⟨ψ₁ x, hright₁ x⟩
  have e₁ : ↥W₁ ≃* alternatingGroup (Fin 5) := (MulEquiv.ofBijective φ₁ ⟨hφ₁i, hφ₁s⟩).symm
  let φ₂ : alternatingGroup (Fin 5) →* W₂ := (MonoidHom.inr _ _).codRestrict W₂ hmem2
  let ψ₂ : W₂ →* alternatingGroup (Fin 5) :=
    (MonoidHom.snd (alternatingGroup (Fin 5)) (alternatingGroup (Fin 5))).comp W₂.subtype
  have hleft₂ : ∀ b, ψ₂ (φ₂ b) = b := fun b => rfl
  have hright₂ : ∀ x : W₂, φ₂ (ψ₂ x) = x := by
    rintro ⟨⟨a, b⟩, hab⟩
    have ha : a = 1 := hker2 a b hab
    subst ha
    rfl
  have hφ₂i : Function.Injective φ₂ := fun b b' h => by
    have h := congrArg ψ₂ h
    rwa [hleft₂, hleft₂] at h
  have hφ₂s : Function.Surjective φ₂ := fun x => ⟨ψ₂ x, hright₂ x⟩
  have e₂ : ↥W₂ ≃* alternatingGroup (Fin 5) := (MulEquiv.ofBijective φ₂ ⟨hφ₂i, hφ₂s⟩).symm
  have hW₁q : CFSG.IsQuasisimple ↥W₁ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₁.symm isQuasisimple_alternating_five
  have hW₂q : CFSG.IsQuasisimple ↥W₂ :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv e₂.symm isQuasisimple_alternating_five
  have hW₁3 : 3 ∣ Nat.card W₁ := by
    rw [Proof15Res8Diag.card_five e₁]
    norm_num
  have hW₂3 : 3 ∣ Nat.card W₂ := by
    rw [Proof15Res8Diag.card_five e₂]
    norm_num
  have hW₁Z : Nat.card (Subgroup.center ↥W₁) ∣ 3 := by
    rw [Proof15Res8Diag.center_eq_bot_five e₁, Subgroup.card_bot]
    exact one_dvd 3
  have hW₂Z : Nat.card (Subgroup.center ↥W₂) ∣ 3 := by
    rw [Proof15Res8Diag.center_eq_bot_five e₂, Subgroup.card_bot]
    exact one_dvd 3
  exact normal_eq_bot_of_not_three_dvd hsup hcomm hW₁q hW₂q hW₁3 hW₂3 hW₁Z hW₂Z hN hN3

theorem eq_bot_of_cover {T : Type*} [Group T] {P S : Type*} [Group P] [Group S]
    [IsSimpleGroup S] {ψ : P →* S} (hψ : Function.Surjective ψ)
    (hk : ψ.ker ≤ Subgroup.center P) {φ : P →* T} (hφ : Function.Surjective φ)
    {V E : Subgroup T} (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V)
    (hEp : Group.IsPerfect ↥E) (hVE : ⁅V, E⁆ = ⊥) : E = ⊥ :=
  (Proof153Twin2.eq_bot_or_eq_bot_of_commutator_eq_bot hψ hk hφ hV hVq.1 hEp hVE).resolve_left
    ((Subgroup.nontrivial_iff_ne_bot V).mp (CFSG.LocalCores.isQuasisimple_nontrivial hVq))

theorem prod148_facts {T : Type} [Group T] [Finite T] [Group.IsPerfect T]
    (hrank : ∀ F : Subgroup T, CFSG.Assembly.IsElemAbelian 3 F → Nat.card F ≤ 27)
    (hT : IsCentralProductA6Covers T ∨ IsA6CoverTimesA5 T ∨
      Nonempty (T ≃* alternatingGroup (Fin 5) × alternatingGroup (Fin 5)))
    {V E : Subgroup T} (hV : V.IsSubnormal) (hVq : CFSG.IsQuasisimple ↥V)
    (hE : E.IsSubnormal) (hEp : Group.IsPerfect ↥E) (hE1 : E ≠ ⊥) (hVE : ⁅V, E⁆ = ⊥) :
    5 ∣ Nat.card V ∧
      (Nonempty (↥E ≃* alternatingGroup (Fin 5)) ∨
        (Sec4.IsTripleCover ↥E (alternatingGroup (Fin 6)) ∧ CFSG.IsQuasisimple ↥E)) ∧
      ∀ N : Subgroup T, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥ := by
  classical
  have hV1 : V ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot V).mp
    (CFSG.LocalCores.isQuasisimple_nontrivial hVq)
  have hVJ : ⁅V, V⁆ = V := Subgroup.isPerfect_iff.mp hVq.1
  have hZ5 : Subgroup.center (alternatingGroup (Fin 5)) = ⊥ :=
    Proof15Res8Diag.center_eq_bot_five (MulEquiv.refl _)
  rcases hT with hcp | hc5 | hne55
  ·
    obtain ⟨U₀, V₀, hU₀n, hV₀n, hsup, hcomm, h3, hU₀tc, hV₀tc⟩ := hcp
    haveI : U₀.Normal := hU₀n
    haveI : V₀.Normal := hV₀n
    have hc : ∀ u ∈ U₀, ∀ v ∈ V₀, u * v = v * u := fun u hu v hv =>
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hu) v hv).symm
    have hc' : ∀ v ∈ V₀, ∀ u ∈ U₀, v * u = u * v := fun v hv u hu => (hc u hu v hv).symm
    have hU₀p : Group.IsPerfect ↥U₀ :=
      Proof15Res8Diag.isPerfect_of_six_six hc h3 hU₀tc hV₀tc hrank
    have hV₀p : Group.IsPerfect ↥V₀ :=
      Proof15Res8Diag.isPerfect_of_six_six hc' (by simpa [inf_comm] using h3) hV₀tc hU₀tc hrank
    have hUq : CFSG.IsQuasisimple ↥U₀ := Proof15Res8Diag.isQuasisimple_tripleCover hU₀p hU₀tc
    have hV₀q : CFSG.IsQuasisimple ↥V₀ := Proof15Res8Diag.isQuasisimple_tripleCover hV₀p hV₀tc
    have hNbot : ∀ N : Subgroup T, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥ := fun N hNn hN3 =>
      normal_eq_bot_of_not_three_dvd hsup hcomm hUq hV₀q
        (by rw [Proof15Res8Diag.card_tripleCover hU₀tc]; norm_num)
        (by rw [Proof15Res8Diag.card_tripleCover hV₀tc]; norm_num)
        (by rw [hU₀tc.1])
        (by rw [hV₀tc.1]) hNn hN3
    have hZ₀U : (Subgroup.center ↥U₀).map U₀.subtype ≤ Subgroup.center T :=
      center_map_le_center_of_commutator_eq_bot hsup hcomm
    have hZ₀V : (Subgroup.center ↥V₀).map V₀.subtype ≤ Subgroup.center T :=
      center_map_le_center_of_commutator_eq_bot (by rw [sup_comm]; exact hsup)
        (by rw [Subgroup.commutator_comm]; exact hcomm)
    obtain ⟨εU⟩ := hU₀tc.2
    obtain ⟨εV⟩ := hV₀tc.2
    obtain ⟨hψU, hkU⟩ := Proof153Twin2.tripleCover_cover εU
    obtain ⟨hψV, hkV⟩ := Proof153Twin2.tripleCover_cover εV
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have hloc : (V ≤ U₀ ∧ E ≤ V₀) ∨ (V ≤ V₀ ∧ E ≤ U₀) :=
      Proof153Twin2.le_or_le_of_commutator_eq_bot hsup hcomm hψU hkU
        (φ₁ := MonoidHom.id ↥U₀) Function.surjective_id hψV hkV
        (φ₂ := MonoidHom.id ↥V₀) Function.surjective_id hV hVq.1 hEp hV1 hE1 hVE
    have hmain : 5 ∣ Nat.card V ∧
        (Nonempty (↥E ≃* alternatingGroup (Fin 5)) ∨
          (Sec4.IsTripleCover ↥E (alternatingGroup (Fin 6)) ∧ CFSG.IsQuasisimple ↥E)) := by
      rcases hloc with ⟨hVU, hEV⟩ | ⟨hVU, hEV⟩
      · have hsupV : V ⊔ (Subgroup.center ↥U₀).map U₀.subtype = U₀ := by
          simpa using Proof153Twin2.sup_eq_of_le_factor hψU hkU (φ := MonoidHom.id ↥U₀)
            Function.surjective_id hV hVq.1 hV1 hVU
        have hVeq : V = U₀ := eq_of_le_of_sup_center_eq hVJ (Subgroup.isPerfect_iff.mp hU₀p)
          hVU hZ₀U hsupV
        have hsupE : E ⊔ (Subgroup.center ↥V₀).map V₀.subtype = V₀ := by
          simpa using Proof153Twin2.sup_eq_of_le_factor hψV hkV (φ := MonoidHom.id ↥V₀)
            Function.surjective_id hE hEp hE1 hEV
        have hEeq : E = V₀ := eq_of_le_of_sup_center_eq (Subgroup.isPerfect_iff.mp hEp)
          (Subgroup.isPerfect_iff.mp hV₀p) hEV hZ₀V hsupE
        have hEtc : Sec4.IsTripleCover ↥E (alternatingGroup (Fin 6)) :=
          Proof15Res8Diag.isTripleCover_congr (MulEquiv.subgroupCongr hEeq).symm hV₀tc
        have h5 : 5 ∣ Nat.card V := by
          have hcard : Nat.card ↥V = Nat.card ↥U₀ :=
            Nat.card_congr (MulEquiv.subgroupCongr hVeq).toEquiv
          rw [hcard, Proof15Res8Diag.card_tripleCover hU₀tc]
          norm_num
        exact ⟨h5, Or.inr ⟨hEtc, Proof15Res8Diag.isQuasisimple_tripleCover hEp hEtc⟩⟩
      · have hsupV : V ⊔ (Subgroup.center ↥V₀).map V₀.subtype = V₀ := by
          simpa using Proof153Twin2.sup_eq_of_le_factor hψV hkV (φ := MonoidHom.id ↥V₀)
            Function.surjective_id hV hVq.1 hV1 hVU
        have hVeq : V = V₀ := eq_of_le_of_sup_center_eq hVJ (Subgroup.isPerfect_iff.mp hV₀p)
          hVU hZ₀V hsupV
        have hsupE : E ⊔ (Subgroup.center ↥U₀).map U₀.subtype = U₀ := by
          simpa using Proof153Twin2.sup_eq_of_le_factor hψU hkU (φ := MonoidHom.id ↥U₀)
            Function.surjective_id hE hEp hE1 hEV
        have hEeq : E = U₀ := eq_of_le_of_sup_center_eq (Subgroup.isPerfect_iff.mp hEp)
          (Subgroup.isPerfect_iff.mp hU₀p) hEV hZ₀U hsupE
        have hEtc : Sec4.IsTripleCover ↥E (alternatingGroup (Fin 6)) :=
          Proof15Res8Diag.isTripleCover_congr (MulEquiv.subgroupCongr hEeq).symm hU₀tc
        have h5 : 5 ∣ Nat.card V := by
          have hcard : Nat.card ↥V = Nat.card ↥V₀ :=
            Nat.card_congr (MulEquiv.subgroupCongr hVeq).toEquiv
          rw [hcard, Proof15Res8Diag.card_tripleCover hV₀tc]
          norm_num
        exact ⟨h5, Or.inr ⟨hEtc, Proof15Res8Diag.isQuasisimple_tripleCover hEp hEtc⟩⟩
    exact ⟨hmain.1, hmain.2, hNbot⟩
  ·
    obtain ⟨U₀, V₀, hU₀n, hV₀n, hinf, hsup, hU₀tc, ⟨eV⟩⟩ := hc5
    haveI : U₀.Normal := hU₀n
    haveI : V₀.Normal := hV₀n
    have hcomm : ⁅U₀, V₀⁆ = ⊥ := by
      rw [eq_bot_iff]
      exact (le_inf (Subgroup.commutator_le_left U₀ V₀)
        (Subgroup.commutator_le_right U₀ V₀)).trans (le_of_eq hinf)
    have hc : ∀ u ∈ U₀, ∀ v ∈ V₀, u * v = v * u := fun u hu v hv =>
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hu) v hv).symm
    have hD : Group.IsPerfect (U₀ ⊔ V₀ : Subgroup T) := by
      rw [hsup]
      exact Group.IsPerfect.ofSurjective
        (f := (Subgroup.topEquiv (G := T)).symm.toMonoidHom)
        (Subgroup.topEquiv (G := T)).symm.surjective
    have hU₀p : Group.IsPerfect ↥U₀ := Proof15Res8Diag.isPerfect_of_six_five hc hinf hD
    have hUq : CFSG.IsQuasisimple ↥U₀ := Proof15Res8Diag.isQuasisimple_tripleCover hU₀p hU₀tc
    have hV₀q : CFSG.IsQuasisimple ↥V₀ :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv eV.symm isQuasisimple_alternating_five
    have hNbot : ∀ N : Subgroup T, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥ := fun N hNn hN3 =>
      normal_eq_bot_of_not_three_dvd hsup hcomm hUq hV₀q
        (by rw [Proof15Res8Diag.card_tripleCover hU₀tc]; norm_num)
        (by rw [Proof15Res8Diag.card_five eV]; norm_num)
        (by rw [hU₀tc.1])
        (by rw [Proof15Res8Diag.center_eq_bot_five eV, Subgroup.card_bot]; exact one_dvd 3)
        hNn hN3
    have hZ₀U : (Subgroup.center ↥U₀).map U₀.subtype ≤ Subgroup.center T :=
      center_map_le_center_of_commutator_eq_bot hsup hcomm
    obtain ⟨εU⟩ := hU₀tc.2
    obtain ⟨hψU, hkU⟩ := Proof153Twin2.tripleCover_cover εU
    have hkV : (eV : ↥V₀ →* alternatingGroup (Fin 5)).ker ≤ Subgroup.center ↥V₀ := by
      rw [(MonoidHom.ker_eq_bot_iff (eV : ↥V₀ →* alternatingGroup (Fin 5))).mpr eV.injective]
      exact bot_le
    haveI : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      Y4Core.isSimpleGroup_alternatingGroup 5 (by norm_num)
    have hloc : (V ≤ U₀ ∧ E ≤ V₀) ∨ (V ≤ V₀ ∧ E ≤ U₀) :=
      Proof153Twin2.le_or_le_of_commutator_eq_bot hsup hcomm hψU hkU
        (φ₁ := MonoidHom.id ↥U₀) Function.surjective_id
        (ψ₂ := (eV : ↥V₀ →* alternatingGroup (Fin 5))) eV.surjective hkV
        (φ₂ := MonoidHom.id ↥V₀) Function.surjective_id
        hV hVq.1 hEp hV1 hE1 hVE
    have hmain : 5 ∣ Nat.card V ∧
        (Nonempty (↥E ≃* alternatingGroup (Fin 5)) ∨
          (Sec4.IsTripleCover ↥E (alternatingGroup (Fin 6)) ∧ CFSG.IsQuasisimple ↥E)) := by
      rcases hloc with ⟨hVU, hEV⟩ | ⟨hVU, hEV⟩
      · have hsupV : V ⊔ (Subgroup.center ↥U₀).map U₀.subtype = U₀ := by
          simpa using Proof153Twin2.sup_eq_of_le_factor hψU hkU (φ := MonoidHom.id ↥U₀)
            Function.surjective_id hV hVq.1 hV1 hVU
        have hVeq : V = U₀ := eq_of_le_of_sup_center_eq hVJ (Subgroup.isPerfect_iff.mp hU₀p)
          hVU hZ₀U hsupV
        have hEeq : E = V₀ := Proof153Twin2.eq_of_le_simple_factor hZ5 eV hE hEp hE1 hEV
        have h5 : 5 ∣ Nat.card V := by
          have hcard : Nat.card ↥V = Nat.card ↥U₀ :=
            Nat.card_congr (MulEquiv.subgroupCongr hVeq).toEquiv
          rw [hcard, Proof15Res8Diag.card_tripleCover hU₀tc]
          norm_num
        exact ⟨h5, Or.inl ⟨(MulEquiv.subgroupCongr hEeq).trans eV⟩⟩
      · have hVeq : V = V₀ := Proof153Twin2.eq_of_le_simple_factor hZ5 eV hV hVq.1 hV1 hVU
        have hsupE : E ⊔ (Subgroup.center ↥U₀).map U₀.subtype = U₀ := by
          simpa using Proof153Twin2.sup_eq_of_le_factor hψU hkU (φ := MonoidHom.id ↥U₀)
            Function.surjective_id hE hEp hE1 hEV
        have hEeq : E = U₀ := eq_of_le_of_sup_center_eq (Subgroup.isPerfect_iff.mp hEp)
          (Subgroup.isPerfect_iff.mp hU₀p) hEV hZ₀U hsupE
        have hEtc : Sec4.IsTripleCover ↥E (alternatingGroup (Fin 6)) :=
          Proof15Res8Diag.isTripleCover_congr (MulEquiv.subgroupCongr hEeq).symm hU₀tc
        have h5 : 5 ∣ Nat.card V := by
          have hcard : Nat.card ↥V = Nat.card ↥V₀ :=
            Nat.card_congr (MulEquiv.subgroupCongr hVeq).toEquiv
          rw [hcard, Proof15Res8Diag.card_five eV]
          norm_num
        exact ⟨h5, Or.inr ⟨hEtc, Proof15Res8Diag.isQuasisimple_tripleCover hEp hEtc⟩⟩
    exact ⟨hmain.1, hmain.2, hNbot⟩
  ·
    obtain ⟨e55⟩ := hne55
    have hVperf : Group.IsPerfect ↥(V.map e55.toMonoidHom) := by
      rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, hVJ]
    have hEperf : Group.IsPerfect ↥(E.map e55.toMonoidHom) := by
      rw [Subgroup.isPerfect_iff, ← Subgroup.map_commutator, Subgroup.isPerfect_iff.mp hEp]
    have hVsn : (V.map e55.toMonoidHom).IsSubnormal := hV.map e55.surjective
    have hEsn : (E.map e55.toMonoidHom).IsSubnormal := hE.map e55.surjective
    have hVmap1 : V.map e55.toMonoidHom ≠ ⊥ := fun h =>
      hV1 ((Subgroup.map_eq_bot_iff_of_injective V (f := e55.toMonoidHom)
        e55.injective).mp h)
    have hEmap1 : E.map e55.toMonoidHom ≠ ⊥ := fun h =>
      hE1 ((Subgroup.map_eq_bot_iff_of_injective E (f := e55.toMonoidHom)
        e55.injective).mp h)
    have hcommmap : ⁅V.map e55.toMonoidHom, E.map e55.toMonoidHom⁆ = ⊥ := by
      rw [← Subgroup.map_commutator, hVE, Subgroup.map_bot]
    haveI : IsSimpleGroup (alternatingGroup (Fin 5)) :=
      Y4Core.isSimpleGroup_alternatingGroup 5 (by norm_num)
    have hpair := Proof153Twin2.pair_prod hZ5 hZ5 hVsn hEsn hVperf hEperf hVmap1 hEmap1 hcommmap
    have hNbot : ∀ N : Subgroup T, N.Normal → ¬ 3 ∣ Nat.card N → N = ⊥ := by
      intro N hNn hN3
      have hmaps : (N.map e55.toMonoidHom).Normal := Subgroup.Normal.map hNn _ e55.surjective
      have hbot : N.map e55.toMonoidHom = ⊥ :=
        normal_eq_bot_five_five hmaps (by
          rw [Subgroup.card_map_of_injective e55.injective]
          exact hN3)
      rwa [Subgroup.map_eq_bot_iff_of_injective N (f := e55.toMonoidHom) e55.injective] at hbot
    have hV5 : Nonempty (↥V ≃* alternatingGroup (Fin 5)) := by
      rcases hpair with ⟨h, -⟩ | ⟨h, -⟩
      · obtain ⟨eU⟩ := h
        exact ⟨(Subgroup.equivMapOfInjective V e55.toMonoidHom e55.injective).trans eU⟩
      · obtain ⟨eU⟩ := h
        exact ⟨(Subgroup.equivMapOfInjective V e55.toMonoidHom e55.injective).trans eU⟩
    have hE5 : Nonempty (↥E ≃* alternatingGroup (Fin 5)) := by
      rcases hpair with ⟨-, h⟩ | ⟨-, h⟩
      · obtain ⟨eV'⟩ := h
        exact ⟨(Subgroup.equivMapOfInjective E e55.toMonoidHom e55.injective).trans eV'⟩
      · obtain ⟨eV'⟩ := h
        exact ⟨(Subgroup.equivMapOfInjective E e55.toMonoidHom e55.injective).trans eV'⟩
    refine ⟨?_, Or.inl hE5, hNbot⟩
    obtain ⟨e5⟩ := hV5
    rw [Proof15Res8Diag.card_five e5]
    norm_num

theorem type155_facts {Q : Type*} [Group Q] [Finite Q]
    (h : Nonempty (Q ≃* alternatingGroup (Fin 5)) ∨
      (Sec4.IsTripleCover Q (alternatingGroup (Fin 6)) ∧ CFSG.IsQuasisimple Q)) :
    CFSG.IsQuasisimple Q ∧ 3 ∣ Nat.card Q ∧ 5 ∣ Nat.card Q ∧
      ∀ p : ℕ, p.Prime → 5 ≤ p → ¬ p ^ 2 ∣ Nat.card Q := by
  classical
  have hq : CFSG.IsQuasisimple Q := by
    rcases h with hne | ⟨-, hq⟩
    · obtain ⟨e⟩ := hne
      exact CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm isQuasisimple_alternating_five
    · exact hq
  have hcard : Nat.card Q = 60 ∨ Nat.card Q = 1080 := by
    rcases h with hne | ⟨htc, -⟩
    · obtain ⟨e⟩ := hne
      exact Or.inl (Proof15Res8Diag.card_five e)
    · exact Or.inr (Proof15Res8Diag.card_tripleCover htc)
  refine ⟨hq, ?_, ?_, ?_⟩
  · rcases hcard with h | h <;> rw [h] <;> norm_num
  · rcases hcard with h | h <;> rw [h] <;> norm_num
  · intro p hp h5 hp2
    rcases hcard with hcard | hcard
    · rw [hcard] at hp2
      have hle : p ^ 2 ≤ 60 := Nat.le_of_dvd (by norm_num) hp2
      have hp7 : p ≤ 7 := by
        by_contra hc
        simp only [not_le] at hc
        have h1 : 8 * 8 ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
        have h2 : p ^ 2 = p * p := pow_two p
        omega
      interval_cases p <;> (norm_num at hp) <;> norm_num at hp2
    · rw [hcard] at hp2
      have hle : p ^ 2 ≤ 1080 := Nat.le_of_dvd (by norm_num) hp2
      have hp32 : p ≤ 32 := by
        by_contra hc
        simp only [not_le] at hc
        have h1 : 33 * 33 ≤ p * p := Nat.mul_le_mul (by omega) (by omega)
        have h2 : p ^ 2 = p * p := pow_two p
        omega
      interval_cases p <;> (norm_num at hp) <;> norm_num at hp2

end CFSG.RankThree.PartTwo.Sec15.Proof155P
