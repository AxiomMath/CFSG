module

public import CFSG.Timmesfeld.LieEmbed.FieldEmbed
public import CFSG.Timmesfeld.RankTwo.LevisExceptional

public noncomputable section

namespace CFSG.Timmesfeld.LieEmbed

open CFSG.Blueprint.Chevalley CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Steinberg.TwistedE6
open CFSG.LieType.Steinberg.Exceptional CFSG.LieType.CurtisTits Minuscule

section BaseChange

variable {A B : Type} [Field A] [Field B] (ε : A →+* B) {n : ℕ}

theorem map_tv (i j : Fin n) (c : A) :
    Matrix.SpecialLinearGroup.map ε (tv i j c) = tv i j (ε c) := by
  by_cases h : i = j
  · subst h
    simp [tv]
  · rw [tv_of_ne h, tv_of_ne h]
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.map_apply_coe, Matrix.SpecialLinearGroup.transvection_coe,
      Matrix.SpecialLinearGroup.transvection_coe]
    ext a b
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.add_apply, Matrix.one_apply,
      Matrix.single_apply]
    split_ifs <;> simp

theorem map_sl_injective {ε : A →+* B} :
    Function.Injective (Matrix.SpecialLinearGroup.map (n := Fin n) ε) := by
  intro x y h
  apply Subtype.ext
  ext a b
  have := congrArg (fun z : Matrix.SpecialLinearGroup (Fin n) B =>
    (z : Matrix (Fin n) (Fin n) B) a b) h
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply,
    Matrix.map_apply] at this
  exact ε.injective this

end BaseChange

theorem injective_noncommCoprod_of_center {A B H : Type*} [Group A] [Group B] [Group H]
    {φ : A →* H} {ψ : B →* H} (hφ : Function.Injective φ) (hψ : Function.Injective ψ)
    (hc : ∀ a b, Commute (φ a) (ψ b)) (hB : ∀ b ∈ Subgroup.center B, b = 1) :
    Function.Injective (φ.noncommCoprod ψ hc) := by
  rw [injective_iff_map_eq_one]
  rintro ⟨a, b⟩ h
  rw [MonoidHom.noncommCoprod_apply] at h
  have e : φ a = ψ b⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left h
  have hb : b⁻¹ ∈ Subgroup.center B :=
    Subgroup.mem_center_iff.2 fun y => hψ (by rw [map_mul, map_mul, ← e]; exact (hc a y).symm.eq)
  have hb1 : b = 1 := inv_eq_one.1 (hB _ hb)
  rw [hb1, inv_one, map_one] at e
  rw [hb1, (injective_iff_map_eq_one φ).1 hφ a e]
  rfl

section Fixed

variable {k : Type*} [Field k] {θ : k →+* k}

theorem mem_fixedGroup_of_tv {A : Type*} [Field A] {n : ℕ}
    (L : Matrix.SpecialLinearGroup (Fin n) A →* e6Data_valid.minGroup k)
    (h : ∀ i j : Fin n, i ≠ j → ∀ c, L (tv i j c) ∈ fixedGroup k θ)
    (g : Matrix.SpecialLinearGroup (Fin n) A) : L g ∈ fixedGroup k θ := by
  have hle : Subgroup.closure (CFSG.LinearGroups.elementarySet n A) ≤ (fixedGroup k θ).comap L := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, j, hij, c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, ← tv_of_ne hij]
    exact h i j hij c
  rw [CFSG.LinearGroups.special_linear_elementary_generation] at hle
  exact hle (Subgroup.mem_top g)

theorem coe_twistedRootGroup_of_fixed {A : Type*} {ε : A → k}
    (hε : ∀ c, θ c = c ↔ c ∈ Set.range ε) {β : Fin (Tag.rank .F4) → ℤ}
    {α₀ : Fin (Tag.rank .E6) → ℤ} (hα₀ : IsRoot .E6 α₀) (hp : proj α₀ = β)
    (hfix : rho α₀ = α₀) {u : A → fixedGroup k θ}
    (hu : ∀ c, (u c : e6Data_valid.minGroup k) = e6Data_valid.xm k α₀ (ε c)) :
    ((twistedRootGroup k θ β : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) =
      Set.range u := by
  ext g
  rw [SetLike.mem_coe, mem_twistedRootGroup_iff_of_fixed θ hα₀ hp hfix g, Set.mem_range]
  constructor
  · rintro ⟨c, hc, hg⟩
    obtain ⟨c', rfl⟩ := (hε c).1 hc
    exact ⟨c', Subtype.ext (by rw [hu, hg])⟩
  · rintro ⟨c', rfl⟩
    exact ⟨ε c', (hε _).2 ⟨c', rfl⟩, hu c'⟩

theorem coe_twistedRootGroup_of_pair {β : Fin (Tag.rank .F4) → ℤ}
    {α₀ : Fin (Tag.rank .E6) → ℤ} (hα₀ : IsRoot .E6 α₀) (hp : proj α₀ = β)
    (hne : rho α₀ ≠ α₀) {u : k → fixedGroup k θ}
    (hu : ∀ c, (u c : e6Data_valid.minGroup k) =
      e6Data_valid.xm k α₀ c * e6Data_valid.xm k (rho α₀) ((twistSign α₀ : k) * θ c)) :
    ((twistedRootGroup k θ β : Subgroup (fixedGroup k θ)) : Set (fixedGroup k θ)) =
      Set.range u := by
  ext g
  rw [SetLike.mem_coe, mem_twistedRootGroup_iff_of_pair θ hα₀ hp hne g, Set.mem_range]
  constructor
  · rintro ⟨c, hg⟩
    exact ⟨c, Subtype.ext (by rw [hu, hg])⟩
  · rintro ⟨c, rfl⟩
    exact ⟨c, hu c⟩

end Fixed

theorem mem_of_tv_two {F G : Type*} [Field F] [Group G]
    (ψ : Matrix.SpecialLinearGroup (Fin 2) F →* G) {H : Subgroup G}
    (h01 : ∀ c, ψ (tv 0 1 c) ∈ H) (h10 : ∀ c, ψ (tv 1 0 c) ∈ H)
    (g : Matrix.SpecialLinearGroup (Fin 2) F) : ψ g ∈ H := by
  have hle : Subgroup.closure ({g | ∃ c : F, g = tv 0 1 c} ∪ {g | ∃ c : F, g = tv 1 0 c} :
      Set (Matrix.SpecialLinearGroup (Fin 2) F)) ≤ H.comap ψ := by
    rw [Subgroup.closure_le]
    rintro _ (⟨c, rfl⟩ | ⟨c, rfl⟩)
    exacts [h01 c, h10 c]
  rw [closure_tv_two] at hle
  exact hle (Subgroup.mem_top g)

variable {f : ℕ} (hf : 1 ≤ f)

@[expose] def e6n (a : Fin 6) : Fin (Tag.rank .E6) := a

set_option maxRecDepth 100000 in
theorem e6_fixed_check :
    rho (sroot (e6n 1)) = sroot (e6n 1) ∧ rho (-sroot (e6n 1)) = -sroot (e6n 1) ∧
      rho (sroot (e6n 3)) = sroot (e6n 3) ∧ rho (-sroot (e6n 3)) = -sroot (e6n 3) ∧
      rho (sroot (e6n 1) + sroot (e6n 3)) = sroot (e6n 1) + sroot (e6n 3) ∧
      rho (-(sroot (e6n 1) + sroot (e6n 3))) = -(sroot (e6n 1) + sroot (e6n 3)) := by
  decide +kernel

set_option maxRecDepth 100000 in
theorem e6_root_check :
    sroot (e6n 1) + sroot (e6n 3) ∈ rootFinset .E6 ∧
      -(sroot (e6n 1) + sroot (e6n 3)) ∈ rootFinset .E6 := by
  decide +kernel

include hf in
theorem exists_sl3ToTwistedE6 :
    ∃ l : Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 f) →* twistedE6Group 2 f,
      Function.Injective l ∧ ∀ c,
        (l (tv 0 1 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (sroot (e6n 1)) (gfEmbed 2 f hf c) ∧
        (l (tv 1 0 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (-sroot (e6n 1)) (gfEmbed 2 f hf c) ∧
        (l (tv 1 2 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (sroot (e6n 3)) (gfEmbed 2 f hf c) ∧
        (l (tv 2 1 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (-sroot (e6n 3)) (gfEmbed 2 f hf c) ∧
        (l (tv 0 2 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (sroot (e6n 1) + sroot (e6n 3)) (gfEmbed 2 f hf c) ∧
        (l (tv 2 0 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (-(sroot (e6n 1) + sroot (e6n 3))) (gfEmbed 2 f hf c) := by
  obtain ⟨l₀, hinj₀, hl₀⟩ := (simplyLacedLevis_e6 (GaloisField 2 (2 * f))).sl3 (e6n 1) (e6n 3)
    (by decide)
  set ε := (gfEmbed 2 f hf).toRingHom
  set L := l₀.comp (Matrix.SpecialLinearGroup.map (n := Fin 3) ε)
  have hL : ∀ i j c, L (tv i j c) = l₀ (tv i j (ε c)) := fun i j c => by
    rw [MonoidHom.comp_apply, map_tv]
  obtain ⟨f1, f1', f3, f3', f13, f13'⟩ := e6_fixed_check
  obtain ⟨r13, r13'⟩ := e6_root_check
  have hθ : ∀ c, frobQ 2 f (ε c) = ε c := frobQ_gfEmbed 2 f hf
  have hx : ∀ {γ}, IsRoot .E6 γ → rho γ = γ → ∀ c, e6Data_valid.xm _ γ (ε c) ∈
      fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f) := fun hγ hfix c =>
    (xFixed (frobQ 2 f) hγ hfix (ε c) (hθ c)).2
  have hfix : ∀ g, L g ∈ fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f) := by
    refine mem_fixedGroup_of_tv L fun i j hij c => ?_
    rw [hL]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show l₀ (tv 0 1 (ε c)) ∈ _
      rw [(hl₀ _).1]; exact hx (isRoot_single _ _) f1 c
    · show l₀ (tv 0 2 (ε c)) ∈ _
      rw [(hl₀ _).2.2.2.2.1]; exact hx (mem_rootFinset.1 r13) f13 c
    · show l₀ (tv 1 0 (ε c)) ∈ _
      rw [(hl₀ _).2.1]; exact hx (isRoot_neg_single _ _) f1' c
    · exact absurd rfl hij
    · show l₀ (tv 1 2 (ε c)) ∈ _
      rw [(hl₀ _).2.2.1]; exact hx (isRoot_single _ _) f3 c
    · show l₀ (tv 2 0 (ε c)) ∈ _
      rw [(hl₀ _).2.2.2.2.2]; exact hx (mem_rootFinset.1 r13') f13' c
    · show l₀ (tv 2 1 (ε c)) ∈ _
      rw [(hl₀ _).2.2.2.1]; exact hx (isRoot_neg_single _ _) f3' c
    · exact absurd rfl hij
  refine ⟨L.codRestrict _ hfix, ?_, fun c => ?_⟩
  · intro x y h
    exact map_sl_injective (hinj₀ (congrArg Subtype.val h))
  · simp only [MonoidHom.codRestrict_apply, hL]
    exact hl₀ (ε c)

set_option maxRecDepth 100000 in
theorem e6_orth_check : ∀ a ∈ ({e6n 0, e6n 2, e6n 4, e6n 5} : Finset (Fin (Tag.rank .E6))),
    ∀ s ∈ ({1, -1} : Finset ℤ), ∀ s' ∈ ({1, -1} : Finset ℤ),
      s • sroot (e6n 1) + s' • sroot a ≠ 0 ∧
        s • sroot (e6n 1) + s' • sroot a ∉ rootFinset .E6 := by
  decide +kernel

theorem commute_rankOne_one {k : Type*} [Field k] {a : Fin (Tag.rank .E6)}
    (ha : a ∈ ({e6n 0, e6n 2, e6n 4, e6n 5} : Finset (Fin (Tag.rank .E6))))
    {x y : e6Data_valid.minGroup k} (hx : x ∈ rankOne (e6Data_valid.rootGroup k) (e6n 1))
    (hy : y ∈ rankOne (e6Data_valid.rootGroup k) a) : Commute x y := by
  have key : ∀ s ∈ ({1, -1} : Finset ℤ), ∀ s' ∈ ({1, -1} : Finset ℤ), ∀ c d : k,
      Commute (e6Data_valid.xm k (s • sroot (e6n 1)) c) (e6Data_valid.xm k (s' • sroot a) d) := by
    intro s hs s' hs' c d
    obtain ⟨hne, hnr⟩ := e6_orth_check a ha s hs s' hs'
    have hroot : ∀ t ∈ ({1, -1} : Finset ℤ), ∀ b, IsRoot .E6 (t • sroot b) := by
      intro t ht b
      simp only [Finset.mem_insert, Finset.mem_singleton] at ht
      rcases ht with rfl | rfl
      · rw [one_smul]; exact isRoot_single _ _
      · rw [neg_one_smul]; exact isRoot_neg_single _ _
    exact commutatorElement_eq_one_iff_commute.1 ((e6Data_valid.commutator_xm k (hroot s hs _)
      (hroot s' hs' _) hne).2 (fun h => hnr (mem_rootFinset.2 h)) c d)
  have h1 : (1 : ℤ) ∈ ({1, -1} : Finset ℤ) := by decide
  have h2 : (-1 : ℤ) ∈ ({1, -1} : Finset ℤ) := by decide
  have cen : ∀ {γ δ : Fin (Tag.rank .E6) → ℤ},
      (∀ c d : k, Commute (e6Data_valid.xm k δ c) (e6Data_valid.xm k γ d)) →
      e6Data_valid.rootGroup k γ ≤
        Subgroup.centralizer (e6Data_valid.rootGroup k δ : Set (e6Data_valid.minGroup k)) := by
    intro γ δ h z hz
    obtain ⟨d, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hz
    rw [Subgroup.mem_centralizer_iff]
    intro w hw
    obtain ⟨c, rfl⟩ := (e6Data_valid.mem_rootGroup k).1 hw
    exact (h c d).eq
  have pp := key 1 h1 1 h1
  have pn := key 1 h1 (-1) h2
  have np := key (-1) h2 1 h1
  have nn := key (-1) h2 (-1) h2
  simp only [one_smul, neg_one_smul] at pp pn np nn
  have hle : rankOne (e6Data_valid.rootGroup k) a ≤ Subgroup.centralizer
      (rankOne (e6Data_valid.rootGroup k) (e6n 1) : Set (e6Data_valid.minGroup k)) := by
    refine sup_le ?_ ?_
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (cen fun c d => (pp d c).symm) (cen fun c d => (np d c).symm)
    · rw [Subgroup.le_centralizer_iff]
      exact sup_le (cen fun c d => (pn d c).symm) (cen fun c d => (nn d c).symm)
  exact Subgroup.mem_centralizer_iff.1 (hle hy) x hx

include hf in
theorem exists_sl2FixedToTwistedE6 :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 f) →* twistedE6Group 2 f,
      Function.Injective m ∧ (∀ c,
        (m (tv 0 1 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (sroot (e6n 1)) (gfEmbed 2 f hf c) ∧
        (m (tv 1 0 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (-sroot (e6n 1)) (gfEmbed 2 f hf c)) ∧
      ∀ g, (m g : e6Data_valid.minGroup _) ∈
        rankOne (e6Data_valid.rootGroup (GaloisField 2 (2 * f))) (e6n 1) := by
  obtain ⟨ψ, hψ, hψv⟩ := (simplyLacedLevis_e6 (GaloisField 2 (2 * f))).sl2 (e6n 1)
  set ε := (gfEmbed 2 f hf).toRingHom
  set L := ψ.comp (Matrix.SpecialLinearGroup.map (n := Fin 2) ε)
  have hL : ∀ i j c, L (tv i j c) = ψ (tv i j (ε c)) := fun i j c => by
    rw [MonoidHom.comp_apply, map_tv]
  obtain ⟨f1, f1', -, -, -, -⟩ := e6_fixed_check
  have hθ : ∀ c, frobQ 2 f (ε c) = ε c := frobQ_gfEmbed 2 f hf
  have hfix : ∀ g, L g ∈ fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f) := by
    refine mem_fixedGroup_of_tv L fun i j hij c => ?_
    rw [hL]
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · show ψ (tv 0 1 (ε c)) ∈ _
      rw [(hψv _).1]
      exact (xFixed (frobQ 2 f) (isRoot_single _ _) f1 (ε c) (hθ c)).2
    · show ψ (tv 1 0 (ε c)) ∈ _
      rw [(hψv _).2]
      exact (xFixed (frobQ 2 f) (isRoot_neg_single _ _) f1' (ε c) (hθ c)).2
    · exact absurd rfl hij
  refine ⟨L.codRestrict _ hfix, fun x y h => map_sl_injective (hψ (congrArg Subtype.val h)),
    fun c => ?_, fun g => ?_⟩
  · simp only [MonoidHom.codRestrict_apply, hL]
    exact hψv (ε c)
  · refine mem_of_tv_two ψ (fun c => ?_) (fun c => ?_) _
    · rw [(hψv c).1]
      exact Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup _ _ _)
    · rw [(hψv c).2]
      exact Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup _ _ _)

include hf in
theorem exists_sl2PairToTwistedE6 {a b : Fin (Tag.rank .E6)}
    (hab : (a = nd 2 ∧ b = nd 4) ∨ (a = nd 0 ∧ b = nd 5)) :
    ∃ m : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 (2 * f)) →* twistedE6Group 2 f,
      Function.Injective m ∧ (∀ c,
        (m (tv 0 1 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (sroot a) c * e6Data_valid.xm _ (sroot b) (frobQ 2 f c) ∧
        (m (tv 1 0 c) : e6Data_valid.minGroup _) =
          e6Data_valid.xm _ (-sroot a) c * e6Data_valid.xm _ (-sroot b) (frobQ 2 f c)) ∧
      ∀ g, (m g : e6Data_valid.minGroup _) ∈
        rankOne (e6Data_valid.rootGroup (GaloisField 2 (2 * f))) a ⊔
          rankOne (e6Data_valid.rootGroup (GaloisField 2 (2 * f))) b := by
  obtain ⟨ψ, hψ, hψv⟩ := (simplyLacedLevis_e6 (GaloisField 2 (2 * f))).sl2 a
  have hθ := frobQ_frobQ 2 f hf
  have hψr : ∀ g, ψ g ∈ rankOne (e6Data_valid.rootGroup (GaloisField 2 (2 * f))) a := by
    refine mem_of_tv_two ψ (fun c => ?_) (fun c => ?_)
    · rw [(hψv c).1]
      exact Subgroup.mem_sup_left (e6Data_valid.xm_mem_rootGroup _ _ _)
    · rw [(hψv c).2]
      exact Subgroup.mem_sup_right (e6Data_valid.xm_mem_rootGroup _ _ _)
  have hσr : ∀ g, sigma _ (frobQ 2 f) (ψ g) ∈
      rankOne (e6Data_valid.rootGroup (GaloisField 2 (2 * f))) b := fun g =>
    rhoPerm_of_orbit hab ▸ sigma_mem_rankOne (frobQ 2 f) (hψr g)
  set M := (phiOrbit (frobQ 2 f) hab).comp (ψ.codRestrict _ hψr)
  have hM : ∀ g, M g = ψ g * sigma _ (frobQ 2 f) (ψ g) := fun g => rfl
  have hfix : ∀ g, M g ∈ fixedGroup (GaloisField 2 (2 * f)) (frobQ 2 f) := by
    intro g
    rw [mem_fixedGroup, hM, map_mul, sigma_sigma (frobQ 2 f) hθ]
    exact (commute_rankOne_orbit hab (hψr g) (hσr g)).symm.eq
  refine ⟨M.codRestrict _ hfix, ?_, fun c => ?_, fun g => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro g hg
    have h1 : M g = 1 := congrArg Subtype.val hg
    rw [hM] at h1
    have e : ψ g = (sigma _ (frobQ 2 f) (ψ g))⁻¹ := eq_inv_of_mul_eq_one_left h1
    have hc : g ∈ Subgroup.center _ := Subgroup.mem_center_iff.2 fun y => hψ (by
      rw [map_mul, map_mul, e]
      exact (commute_rankOne_orbit hab (hψr y) (Subgroup.inv_mem _ (hσr g))).eq)
    exact LevisExtras.eq_one_of_mem_center_sl2 hc
  · simp only [MonoidHom.codRestrict_apply, hM]
    rw [(hψv c).1, (hψv c).2, sigma_xm_single, sigma_xm_neg_single, rhoPerm_of_orbit hab]
    exact ⟨rfl, rfl⟩
  · simp only [MonoidHom.codRestrict_apply, hM]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hψr g)) (Subgroup.mem_sup_right (hσr g))

end CFSG.Timmesfeld.LieEmbed
