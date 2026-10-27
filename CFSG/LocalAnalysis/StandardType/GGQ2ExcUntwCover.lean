module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcPlacementDefs
import CFSG.GroupTheory.InnerCentralizerProjection

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley
open CFSG.Open (IsElemAbelian)

private theorem subsingleton_units_of_field_card_two {K : Type} [Field K] (hK : Nat.card K = 2) :
    Subsingleton Kˣ := by
  have h : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK]
  exact (Nat.card_eq_one_iff_unique.mp h).1

private theorem chevIDImage_subset_inn_of_field_two {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ}
    {K : Type} [Field K] [Subsingleton Kˣ] (H : Subgroup (LargeEvenChevGL A K)) :
    LargeEvenChevIDImage A K H ⊆
      (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range := by
  have hH : ∀ a : Fin r → Kˣ,
      (∀ h ∈ H, TableB.diagHom A K a * h * (TableB.diagHom A K a)⁻¹ ∈ H) →
        TableB.diagHom A K a ∈ H := fun a _ => by
    rw [Subsingleton.elim a 1, map_one]
    exact H.one_mem
  intro φ hφ
  have hle : Subgroup.closure (LargeEvenInnSet _ ∪ LargeEvenChevDiagImage A K H) ≤
      (MulAut.conj : LargeEvenCenterQuot H →* MulAut (LargeEvenCenterQuot H)).range := by
    rw [Subgroup.closure_le]
    refine Set.union_subset ?_ ?_
    · rintro _ ⟨x, rfl⟩
      exact ⟨x, rfl⟩
    · intro ψ hψ
      obtain ⟨a, ha⟩ := TableB.exists_isDiagOf hψ
      rw [TableB.isDiagOf_eq_conj ha (hH a ha.1)]
      exact ⟨_, rfl⟩
  exact hle hφ

private theorem mem_of_pow_three_mem_of_centralizer {G : Type} [Group G] [Finite G]
    {H : Subgroup G} {x : G} (hx : x ∈ Subgroup.centralizer (H : Set G)) (hx3 : x ^ 3 ∈ H)
    (hC : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) : x ∈ H := by
  have hdvd : orderOf x ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)) :=
    Subgroup.orderOf_dvd_natCard _ hx
  have hcop : Nat.Coprime 3 (orderOf x) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr fun h3 => hC (h3.trans hdvd)
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime (n := 3) (x := x) hcop
  rw [← hm]
  exact H.pow_mem hx3 m

private theorem centralizer_mem_of_conj_mod_center {G : Type} [Group G] {H : Subgroup G}
    {R : Type} [Group R] (π : ↥H →* R) (hkerπ : π.ker = Subgroup.center ↥H)
    (hperf : commutator H = ⊤) {b : G} (hbN : b ∈ Subgroup.normalizer (H : Set G))
    (g : ↥H) (hbconj_mem : ∀ l : ↥H, b⁻¹ * (l : G) * b ∈ H)
    (hconj : ∀ l : ↥H, π ⟨b⁻¹ * (l : G) * b, hbconj_mem l⟩ = π (g * l * g⁻¹)) :
    (g : G)⁻¹ * b⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  have hperfH : Group.IsPerfect ↥H := ⟨hperf⟩
  let h : G := (g : G)⁻¹ * b⁻¹
  have hhN : h ∈ Subgroup.normalizer (H : Set G) := by
    exact Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer g.2))
      (Subgroup.inv_mem _ hbN)
  have hhC : h ∈ Subgroup.centralizer (H : Set G) := by
    refine CFSG.mem_centralizer_of_commutator_mem_center hperfH hhN ?_
    intro l hl
    let lH : ↥H := ⟨l, hl⟩
    let l' : ↥H := ⟨b⁻¹ * l * b, hbconj_mem lH⟩
    have h1 : h * l * h⁻¹ = (g : G)⁻¹ * (l' : G) * g := by
      simp only [h, l']
      group
    have hzmem : h * l * h⁻¹ * l⁻¹ ∈ H := by
      rw [h1]
      exact H.mul_mem (H.mul_mem (H.mul_mem (H.inv_mem g.2) (hbconj_mem lH)) g.2)
        (H.inv_mem hl)
    let z : ↥H := ⟨h * l * h⁻¹ * l⁻¹, hzmem⟩
    have hzker : π z = 1 := by
      have hz_eq : z = (g : ↥H)⁻¹ * l' * g * lH⁻¹ := by
        apply Subtype.ext
        change h * l * h⁻¹ * l⁻¹ = ((g : G)⁻¹ * (l' : G) * g) * (lH : G)⁻¹
        simp only [h, l', lH]
        group
      rw [hz_eq]
      simp only [map_mul, map_inv]
      rw [hconj lH]
      simp only [map_mul, map_inv]
      group
    have hzcenter : z ∈ Subgroup.center ↥H := by
      rw [← hkerπ]
      exact MonoidHom.mem_ker.mpr hzker
    exact Subgroup.mem_map.mpr ⟨z, hzcenter, rfl⟩
  exact hhC

private theorem mem_centralizer_of_induces {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {R : Type} [Group R] {I : Set (MulAut R)}
    (hperf : commutator H = ⊤) (hInn : ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)
    (θ : ↥H ⧸ Subgroup.center ↥H ≃* R)
    (hact : ∀ b ∈ E, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hEN : E ≤ Subgroup.normalizer (H : Set G)) {b : G} (hb : b ∈ E) :
    ∃ g : ↥H, (g : G)⁻¹ * b⁻¹ ∈ Subgroup.centralizer (H : Set G) := by
  let π : ↥H →* R := ggQuotHom θ
  have hkerπ : π.ker = Subgroup.center ↥H := ker_ggQuotHom θ
  have hπsurj : Function.Surjective π :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥H))
  have hbN : b ∈ Subgroup.normalizer (H : Set G) := hEN hb
  obtain ⟨φ, hφI, hφind⟩ := hact b hb
  obtain ⟨r, hφ⟩ := hInn φ hφI
  obtain ⟨g, hg⟩ := hπsurj r
  have hbconj_mem : ∀ l : ↥H, b⁻¹ * (l : G) * b ∈ H := by
    intro l
    simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hbN) (l : G)).mp l.2
  have hconj : ∀ l : ↥H, π ⟨b⁻¹ * (l : G) * b, hbconj_mem l⟩ = π (g * l * g⁻¹) := by
    intro l
    let l' : ↥H := ⟨b⁻¹ * (l : G) * b, hbconj_mem l⟩
    have h1 : φ (π l) = π l' := hφind l l' rfl
    have h2 : φ (π l) = π g * π l * (π g)⁻¹ := by
      rw [hφ, MulAut.conj_apply, ← hg]
    calc π l' = φ (π l) := h1.symm
      _ = π g * π l * (π g)⁻¹ := h2
      _ = π (g * l * g⁻¹) := by simp only [map_mul, map_inv]
  exact ⟨g, centralizer_mem_of_conj_mod_center π hkerπ hperf hbN g hbconj_mem hconj⟩

private theorem le_of_inner_diag_marking {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {R : Type} [Group R] {I : Set (MulAut R)}
    (hperf : commutator H = ⊤) (hInn : ∀ φ ∈ I, ∃ r : R, φ = MulAut.conj r)
    (θ : ↥H ⧸ Subgroup.center ↥H ≃* R)
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (hact : ∀ b ∈ E, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hE : IsElemAbelian 3 E)
    (hC : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G))) : E ≤ H := by
  intro b hb
  obtain ⟨g, hhC⟩ := mem_centralizer_of_induces hperf hInn θ hact hEN hb
  let h : G := (g : G)⁻¹ * b⁻¹
  have hcomm_hg : (g : G) * h = h * (g : G) :=
    Subgroup.mem_centralizer_iff.mp hhC g g.2
  have hbg : b * (g : G) = (g : G) * b := by
    have h1 : (g : G)⁻¹ * b⁻¹ * (g : G) = b⁻¹ := by
      have h' := hcomm_hg
      rw [show h = (g : G)⁻¹ * b⁻¹ from rfl] at h'
      group at h'
      simpa using h'.symm
    have h2 : (g : G)⁻¹ * b * (g : G) = b := by
      have hinv := congrArg Inv.inv h1
      calc (g : G)⁻¹ * b * (g : G) = ((g : G)⁻¹ * b⁻¹ * (g : G))⁻¹ := by group
        _ = (b⁻¹)⁻¹ := by rw [hinv]
        _ = b := inv_inv b
    calc b * (g : G) = (g : G) * ((g : G)⁻¹ * b * (g : G)) := by group
      _ = (g : G) * b := by rw [h2]
  have hb3 : b ^ 3 = 1 := hE.2 b hb
  have hh3 : h ^ 3 = ((g : G)⁻¹) ^ 3 := by
    have hcommgb : Commute ((g : G)⁻¹) (b⁻¹) :=
      (show Commute (g : G) b from hbg.symm).inv_left.inv_right
    rw [show h = (g : G)⁻¹ * b⁻¹ from rfl, hcommgb.mul_pow 3,
      show (b⁻¹) ^ 3 = 1 by rw [inv_pow, hb3, inv_one], mul_one]
  have hh3H : h ^ 3 ∈ H := by
    rw [hh3]
    exact H.pow_mem (H.inv_mem g.2) 3
  have hhH : h ∈ H := mem_of_pow_three_mem_of_centralizer hhC hh3H hC
  have hb_eq : b = h⁻¹ * (g : G)⁻¹ := by
    rw [show h = (g : G)⁻¹ * b⁻¹ from rfl]
    group
  rw [hb_eq]
  exact H.mul_mem (H.inv_mem hhH) (H.inv_mem g.2)

private theorem excUntwCover_of_data {G : Type} [Group G] [Finite G] {H E : Subgroup G}
    {τ : Tag} {r : ℕ} {A : Matrix (Fin r) (Fin r) ℤ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 2) (hperf : commutator H = ⊤) (hE : IsElemAbelian 3 E)
    (hEN : E ≤ Subgroup.normalizer (H : Set G))
    (θ : ↥H ⧸ Subgroup.center ↥H ≃* LargeEvenCenterQuot (LargeEvenChevH A K false))
    (hID : LargeEvenChevIDImage A K (LargeEvenChevH A K false) ⊆
      (MulAut.conj : LargeEvenCenterQuot (LargeEvenChevH A K false) →*
        MulAut (LargeEvenCenterQuot (LargeEvenChevH A K false))).range)
    (hact : ∀ b ∈ E, ∃ φ ∈ LargeEvenChevIDImage A K (LargeEvenChevH A K false),
      LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ)
    (hC : ¬ 3 ∣ Nat.card ↥(Subgroup.centralizer (H : Set G)))
    (e : LargeEvenCenterQuot (LargeEvenChevH A K false) ≃* adjointGroup τ K) :
    E ≤ H ∧ commutator H = ⊤ ∧ ∃ (K' : Type) (_ : Field K') (_ : Finite K'),
      Nat.card K' = 2 ∧ ∃ π : ↥H →* adjointGroup τ K', Function.Surjective π ∧
        π.ker = Subgroup.center ↥H := by
  refine ⟨le_of_inner_diag_marking hperf (fun φ hφ => ?_) θ hEN hact hE hC, hperf,
    K, inferInstance, inferInstance, hK, ?_⟩
  · obtain ⟨r, hr⟩ := hID hφ
    exact ⟨r, hr.symm⟩
  · let π : ↥H →* adjointGroup τ K := e.toMonoidHom.comp (ggQuotHom θ)
    have hsurj : Function.Surjective π := e.surjective.comp (ggQuotHom_surjective θ)
    have hker : π.ker = Subgroup.center ↥H := by
      rw [← ker_ggQuotHom θ]
      ext x
      rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
      change e (ggQuotHom θ x) = 1 ↔ ggQuotHom θ x = 1
      exact e.map_eq_one_iff
    exact ⟨π, hsurj, hker⟩

theorem excUntwCover_F4_holds :
    ExcUntwCover .F4 .F4 := by
  intro G _ _ H E h hE hC
  obtain ⟨hperf, lab, _, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, hlab_eq, hEN, hact⟩ := hQ.2.2
  rw [hlab_eq] at hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ'⟩ := hraw
  let : Field K := hKfield
  let : Finite K := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨-, -, θ, -, hEN', hact'⟩ := hQ'
  let : Subsingleton Kˣ := subsingleton_units_of_field_card_two hK2
  let e : LargeEvenCenterQuot (LargeEvenChevH LargeEvenCartanF4 K false) ≃* adjointGroup .F4 K :=
    (Classical.choice (centerQuot_chevGroup_equiv K .F4)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .F4) (K := K))).trans
        QuotientGroup.quotientBot)
  exact excUntwCover_of_data hK2 hperf hE hEN' θ
    (chevIDImage_subset_inn_of_field_two (LargeEvenChevH LargeEvenCartanF4 K false)) hact' hC e

theorem excUntwCover_E6_holds :
    ExcUntwCover .E6 .E6 := by
  intro G _ _ H E h hE hC
  obtain ⟨hperf, lab, _, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, hlab_eq, hEN, hact⟩ := hQ.2.2
  rw [hlab_eq] at hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ'⟩ := hraw
  let : Field K := hKfield
  let : Finite K := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨-, -, θ, -, hEN', hact'⟩ := hQ'
  let : Subsingleton Kˣ := subsingleton_units_of_field_card_two hK2
  let e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 6) K false) ≃* adjointGroup .E6 K :=
    (Classical.choice (centerQuot_chevGroup_equiv K .E6)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E6) (K := K))).trans
        QuotientGroup.quotientBot)
  exact excUntwCover_of_data hK2 hperf hE hEN' θ
    (chevIDImage_subset_inn_of_field_two (LargeEvenChevH (LargeEvenCartanE 6) K false)) hact' hC e

theorem excUntwCover_E7_holds :
    ExcUntwCover .E7 .E7 := by
  intro G _ _ H E h hE hC
  obtain ⟨hperf, lab, _, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, hlab_eq, hEN, hact⟩ := hQ.2.2
  rw [hlab_eq] at hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ'⟩ := hraw
  let : Field K := hKfield
  let : Finite K := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨-, -, θ, -, hEN', hact'⟩ := hQ'
  let : Subsingleton Kˣ := subsingleton_units_of_field_card_two hK2
  let e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 7) K false) ≃* adjointGroup .E7 K :=
    (Classical.choice (centerQuot_chevGroup_equiv K .E7)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E7) (K := K))).trans
        QuotientGroup.quotientBot)
  exact excUntwCover_of_data hK2 hperf hE hEN' θ
    (chevIDImage_subset_inn_of_field_two (LargeEvenChevH (LargeEvenCartanE 7) K false)) hact' hC e

theorem excUntwCover_E8_holds :
    ExcUntwCover .E8 .E8 := by
  intro G _ _ H E h hE hC
  obtain ⟨hperf, lab, _, hraw⟩ := h
  obtain ⟨_, _, _, _, hQ⟩ := largeEvenRawDatum_exists hraw
  obtain ⟨_, hlab_eq, hEN, hact⟩ := hQ.2.2
  rw [hlab_eq] at hraw
  dsimp only [CFSG.Assembly.LargeEvenRawDatum, LargeEvenRecipeChevalley] at hraw
  obtain ⟨K, hKfield, hKfinite, hKcard, hQ'⟩ := hraw
  let : Field K := hKfield
  let : Finite K := hKfinite
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  obtain ⟨-, -, θ, -, hEN', hact'⟩ := hQ'
  let : Subsingleton Kˣ := subsingleton_units_of_field_card_two hK2
  let e : LargeEvenCenterQuot (LargeEvenChevH (LargeEvenCartanE 8) K false) ≃* adjointGroup .E8 K :=
    (Classical.choice (centerQuot_chevGroup_equiv K .E8)).trans
      ((QuotientGroup.quotientMulEquivOfEq
        (CFSG.LieType.Chevalley.center_adjointGroup_eq_bot (τ := .E8) (K := K))).trans
        QuotientGroup.quotientBot)
  exact excUntwCover_of_data hK2 hperf hE hEN' θ
    (chevIDImage_subset_inn_of_field_two (LargeEvenChevH (LargeEvenCartanE 8) K false)) hact' hC e

end CFSG.StandardType.GGQ2Frame.ExcPlacement
