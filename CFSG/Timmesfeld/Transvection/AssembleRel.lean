module

public import CFSG.Timmesfeld.Transvection.PresSp
public import CFSG.Timmesfeld.Transvection.PresSU
public import CFSG.Timmesfeld.Transvection.ModelRankSp
public import CFSG.Timmesfeld.Transvection.ModelRankSU

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.Assembly.LowTwoRank CFSG.LieType CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.ARS.CaseM CFSG.Timmesfeld.LieEmbed

namespace ModelRank

theorem IsTransGroup.natCard_eq {n : ℕ} {K : Type} [Field K] {v : Fin n ⊕ Fin n → K}
    (hv : v ≠ 0) {X : Subgroup (StatedSp n K)} (hX : IsTransGroup v X) :
    Nat.card X = Nat.card K := by
  have hN : spNil v ≠ 0 := by
    rw [spNil, Ne, vecMulVec_eq_zero, not_or]
    exact ⟨hv, vecMul_spGram_ne_zero hv⟩
  refine (Nat.card_congr (Equiv.ofBijective (fun c : K => (⟨Classical.choose (hX.2 c),
    (hX.1 _).2 ⟨c, Classical.choose_spec (hX.2 c)⟩⟩ : X)) ⟨fun c d h => ?_, fun x => ?_⟩)).symm
  · have h1 := congrArg (fun x : X => Symplectic.SpExtras.mat n K x) h
    simp only at h1
    rw [Classical.choose_spec (hX.2 c), Classical.choose_spec (hX.2 d)] at h1
    exact smul_left_injective K hN (add_left_cancel h1)
  · obtain ⟨c, hc⟩ := (hX.1 x).1 x.2
    exact ⟨c, Subtype.ext (Symplectic.SpExtras.mat_injective
      ((Classical.choose_spec (hX.2 c)).trans hc.symm))⟩

theorem IsUTransGroup.natCard_eq {F : Type*} [Field F] {σ : F ≃+* F} {n : ℕ} {v : Fin n → F}
    (hv : v ≠ 0) {X : Subgroup (SU σ n)} (hX : IsUTransGroup σ v X) :
    Nat.card X = Nat.card (traceZero σ) := by
  have hN : uNil σ v ≠ 0 := by
    rw [uNil, Ne, vecMulVec_eq_zero, not_or]
    exact ⟨hv, uRow_ne_zero σ hv⟩
  refine (Nat.card_congr (Equiv.ofBijective (fun c : traceZero σ =>
    (⟨Classical.choose (hX.2 c c.2), (hX.1 _).2 ⟨c, c.2, Classical.choose_spec (hX.2 c c.2)⟩⟩ :
      X)) ⟨fun c d h => ?_, fun x => ?_⟩)).symm
  · have h1 := congrArg (fun x : X => suMat σ n x) h
    simp only at h1
    rw [Classical.choose_spec (hX.2 c c.2), Classical.choose_spec (hX.2 d d.2)] at h1
    exact Subtype.ext (smul_left_injective F hN (add_left_cancel h1))
  · obtain ⟨c, hc, hxc⟩ := (hX.1 x).1 x.2
    exact ⟨⟨c, hc⟩, Subtype.ext (suMat_injective σ
      ((Classical.choose_spec (hX.2 c hc)).trans hxc.symm))⟩

end ModelRank

open ModelRank in
theorem sp_branch_of_spRelations {K : Type} [Field K] [Finite K] [CharP K 2] {H : Type*}
    [Group H] {Δ : Set (Subgroup H)} (hΔ : IsRootClass Δ) {n : ℕ} (hn : 2 ≤ n)
    (hq : 4 ≤ Nat.card K ∨ (Nat.card K = 2 ∧ 3 ≤ n)) (R : SpRelations n K H)
    (hgen : R.Generates)
    (hlong : ((Symplectic.rootDatum n K).rootGroup (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)).map
      (R.toHom hn) ∈ Δ) :
    (∃ Φ : StatedSp n K →* H, Function.Bijective Φ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
      ∃ g, X = (conjSub ((Symplectic.rootDatum n K).rootGroup
        (Pi.single (⟨n - 1, by omega⟩ : Fin n) 1)) g).map Φ) ∧
    ∀ A ∈ Δ, Nat.card A = Nat.card K := by
  have : Nontrivial H := by
    obtain ⟨a, -, ha1⟩ := hΔ.exists_ne_one hlong
    exact ⟨⟨a, 1, ha1⟩⟩
  have hbij := R.toHom_bijective hn hq hgen
  refine ⟨⟨R.toHom hn, hbij, fun X => ⟨fun hX => ?_, ?_⟩⟩, fun A hA => ?_⟩
  · obtain ⟨h, rfl⟩ := hΔ.exists_conjSub_eq hlong hX
    obtain ⟨g, rfl⟩ := hbij.2 h
    exact ⟨g, conjSub_map _ _ _⟩
  · rintro ⟨g, rfl⟩
    rw [← conjSub_map]
    exact hΔ.conjSub_mem hlong _
  · rw [hΔ.card_eq hA hlong, Subgroup.card_map_of_injective hbij.1]
    refine ModelRank.IsTransGroup.natCard_eq (fun h => ?_)
      (isTransGroup_rootGroup_last (n := n) (K := K) (by omega))
    simpa using congrFun h (Sum.inl ⟨n - 1, by omega⟩)

theorem transvectionConclusionRank_of_spRelations {H : Type} [Group H] {Δ : Set (Subgroup H)}
    (hΔ : IsRootClass Δ) {f : ℕ} (hf : 1 ≤ f) {r : ℕ} (hr : 2 ≤ r) (hq : 2 ≤ f ∨ 3 ≤ r)
    (R : SpRelations r (GaloisField 2 f) H) (hgen : R.Generates)
    (hlong : ((Symplectic.rootDatum r (GaloisField 2 f)).rootGroup
      (Pi.single (⟨r - 1, by omega⟩ : Fin r) 1)).map (R.toHom hr) ∈ Δ) :
    TransvectionConclusionRank H Δ f hf r hr ∧ ∀ A ∈ Δ, Nat.card A = 2 ^ f := by
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hq' : 4 ≤ Nat.card (GaloisField 2 f) ∨ (Nat.card (GaloisField 2 f) = 2 ∧ 3 ≤ r) := by
    rw [hK]
    rcases hq with h | h
    · exact Or.inl (by calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) h)
    · by_cases hf2 : 2 ≤ f
      · exact Or.inl (by calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2)
      · exact Or.inr ⟨by rw [show f = 1 by omega]; rfl, h⟩
  obtain ⟨hΦ, hcard⟩ := sp_branch_of_spRelations hΔ hr hq' R hgen hlong
  exact ⟨Or.inl hΦ, fun A hA => (hcard A hA).trans hK⟩

open ModelRank in
theorem eq_one_of_mem_rootGroup_unitaryLongRoot_of_mem_center {F : Type} [Field F] [Finite F]
    {p f : ℕ} [Fact p.Prime] [CharP F p] (hF : Nat.card F = (p ^ f) ^ 2) {m : ℕ} (hm : 2 ≤ m)
    {x : SU (unitaryInvolution F p f) m}
    (hx : x ∈ (Unitary.rootDatum hF m).rootGroup (unitaryLongRoot m hm))
    (hxc : x ∈ Subgroup.center (SU (unitaryInvolution F p f) m)) : x = 1 := by
  have hσ := unitaryInvolution_involutive hF
  have hX₀ := isUTransGroup_rootGroup_unitaryLongRoot hσ hm
  set i₀ : Fin m := lowIdx (⟨m / 2 - 1, by omega⟩ : Fin (m / 2)) with hi₀
  have hi : i₀ ≠ Fin.rev i₀ := lowIdx_ne_rev _ _
  obtain ⟨c, -, hxc'⟩ := (hX₀.1 x).1 hx
  by_cases hc : c = 0
  · apply suMat_injective (unitaryInvolution F p f)
    rw [hxc', hc, uTrans_zero, map_one]
  exfalso
  obtain ⟨ζ, hζ⟩ := exists_traceZero_ne_zero hF
  have he' : uForm (unitaryInvolution F p f) (Pi.single (Fin.rev i₀) 1 : Fin m → F)
      (Pi.single (Fin.rev i₀) 1) = 0 := uForm_single_self (rev_ne_rev_rev hi)
  obtain ⟨y, hy⟩ := exists_suMat_eq_uTrans hσ he' ζ.2
  have hcomm := congrArg (suMat (unitaryInvolution F p f) m)
    ((Subgroup.mem_center_iff.1 hxc y).symm)
  rw [map_mul, map_mul, hxc', hy] at hcomm
  rcases uForm_eq_zero_of_commute _ hσ (single_one_ne_zero i₀) hc hζ hcomm with h | ⟨l, hl⟩
  · rw [uForm_single_left] at h
    simp at h
  · have := congrFun hl (Fin.rev i₀)
    simp [Ne.symm hi] at this

open ModelRank in
theorem su_branch_of_suRelations {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) {H : Type*} [Group H] {Δ : Set (Subgroup H)}
    (hΔ : IsRootClass Δ) {m : ℕ} (he : Even m) (hm : 4 ≤ m)
    (R : SURelations (m / 2) (unitaryInvolution F 2 f) H) (hgen : R.Generates)
    (hZ : Subgroup.center H = ⊥)
    (hlong : ∃ A ∈ Δ, ∀ g, g ∈ A ↔ ∃ c, unitaryInvolution F 2 f c = c ∧
      R.ξL (Sum.inl ⟨m / 2 - 1, by omega⟩) c = g) :
    (∃ Φ : SU (unitaryInvolution F 2 f) m →* H, Function.Surjective Φ ∧
      Φ.ker = Subgroup.center _ ∧ ∀ X : Subgroup H, X ∈ Δ ↔
        ∃ g, X = (conjSub ((Unitary.rootDatum hF m).rootGroup
          (unitaryLongRoot m (by omega))) g).map Φ) ∧
    ∀ A ∈ Δ, Nat.card A = 2 ^ f := by
  obtain ⟨A₀, hA₀, hA₀mem⟩ := hlong
  have : Nontrivial H := by
    obtain ⟨a, -, ha1⟩ := hΔ.exists_ne_one hA₀
    exact ⟨⟨a, 1, ha1⟩⟩
  have hsurj := R.toHom_surjective hF he hm hgen
  have hker := R.ker_toHom_eq_center hF he hm hgen hZ
  have hX₀ : ((Unitary.rootDatum hF m).rootGroup (unitaryLongRoot m (by omega))).map
      (R.toHom hF he hm) = A₀ := by
    ext g
    rw [R.mem_map_rootGroup_unitaryLongRoot hF he hm g, hA₀mem g]
  refine ⟨⟨R.toHom hF he hm, hsurj, hker, fun X => ⟨fun hX => ?_, ?_⟩⟩, fun A hA => ?_⟩
  · rw [← hX₀] at hA₀
    obtain ⟨h, rfl⟩ := hΔ.exists_conjSub_eq hA₀ hX
    obtain ⟨g, rfl⟩ := hsurj h
    exact ⟨g, conjSub_map _ _ _⟩
  · rintro ⟨g, rfl⟩
    rw [← conjSub_map, hX₀]
    exact hΔ.conjSub_mem hA₀ _
  ·
    have hinj : Set.InjOn (R.toHom hF he hm)
        ((Unitary.rootDatum hF m).rootGroup (unitaryLongRoot m (by omega)) : Set _) := by
      intro x hx y hy hxy
      have h1 : x * y⁻¹ ∈ (R.toHom hF he hm).ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
      rw [hker] at h1
      exact mul_inv_eq_one.1 (eq_one_of_mem_rootGroup_unitaryLongRoot_of_mem_center hF
        (by omega) (Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy)) h1)
    rw [hΔ.card_eq hA hA₀, ← hX₀]
    have h2 := Nat.card_image_of_injOn hinj
    rw [← Subgroup.coe_map] at h2
    rw [show Nat.card ↥(((Unitary.rootDatum hF m).rootGroup (unitaryLongRoot m (by omega))).map
      (R.toHom hF he hm)) = Nat.card ↥(((((Unitary.rootDatum hF m).rootGroup
        (unitaryLongRoot m (by omega))).map (R.toHom hF he hm)) : Set H)) from rfl, h2]
    rw [show Nat.card ↥(((Unitary.rootDatum hF m).rootGroup (unitaryLongRoot m (by omega)) :
      Set (SU (unitaryInvolution F 2 f) m))) = Nat.card ↥((Unitary.rootDatum hF m).rootGroup
        (unitaryLongRoot m (by omega))) from rfl]
    exact (ModelRank.IsUTransGroup.natCard_eq (single_one_ne_zero _)
      (isUTransGroup_rootGroup_unitaryLongRoot (m := m) (unitaryInvolution_involutive hF)
        (by omega))).trans (CFSG.LieType.Steinberg.card_traceZero hF)

theorem transvectionConclusionRank_of_suRelations {H : Type} [Group H] {Δ : Set (Subgroup H)}
    (hΔ : IsRootClass Δ) {f : ℕ} (hf : 1 ≤ f) {r : ℕ} (hr : 2 ≤ r)
    (R : SURelations r (unitaryInvolution (GaloisField 2 (2 * f)) 2 f) H) (hgen : R.Generates)
    (hZ : Subgroup.center H = ⊥)
    (hlong : ∃ A ∈ Δ, ∀ g, g ∈ A ↔ ∃ c, unitaryInvolution (GaloisField 2 (2 * f)) 2 f c = c ∧
      R.ξL (Sum.inl ⟨r - 1, by omega⟩) c = g) :
    TransvectionConclusionRank H Δ f hf r hr ∧ ∀ A ∈ Δ, Nat.card A = 2 ^ f := by
  have key : ∀ n : ℕ, r = n → ∃ R' : SURelations n (unitaryInvolution
      (GaloisField 2 (2 * f)) 2 f) H, R'.Generates ∧ ∀ a : Fin n, a.val = r - 1 →
        ∃ A ∈ Δ, ∀ g, g ∈ A ↔ ∃ c, unitaryInvolution (GaloisField 2 (2 * f)) 2 f c = c ∧
          R'.ξL (Sum.inl a) c = g := by
    rintro n rfl
    refine ⟨R, hgen, fun a ha => ?_⟩
    rw [show a = ⟨r - 1, by omega⟩ from Fin.ext ha]
    exact hlong
  obtain ⟨R', hgen', hlong'⟩ := key (2 * r / 2) (by omega)
  obtain ⟨hΦ, hcard⟩ := su_branch_of_suRelations (card_galoisField_two_mul hf) hΔ
    (m := 2 * r) ⟨r, two_mul r⟩ (by omega) R' hgen' hZ (hlong' _ (by simp only; omega))
  exact ⟨Or.inr hΦ, hcard⟩

end CFSG.Timmesfeld.Transvection
