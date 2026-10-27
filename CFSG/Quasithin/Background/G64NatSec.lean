module

public import CFSG.Quasithin.Background.G64Transvec
public import CFSG.Quasithin.Background.G64SymSec

public section

namespace CFSG.Quasithin.G64

open CFSG.Quasithin CFSG.Assembly.LowTwoRank Matrix

variable {V : Type*} [CommGroup V]

section Nat

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Γ : Subgroup (Matrix.GeneralLinearGroup ι K)}

theorem natAct_one_right (γ : ↥Γ) : natAct Γ γ 1 = 1 := by
  simp [natAct]

@[expose] noncomputable def natQuot (Γ : Subgroup (Matrix.GeneralLinearGroup ι K)) :
    Multiplicative (ι → K) →* (FFModel.nat Γ).Mod :=
  (QuotientGroup.mk' _).comp (Subgroup.topEquiv.symm.toMonoidHom)

theorem natQuot_injective : Function.Injective (natQuot Γ) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h1 := (QuotientGroup.eq_one_iff _).1 hx
  rw [Subgroup.mem_subgroupOf] at h1
  exact h1

theorem natQuot_surjective : Function.Surjective (natQuot Γ) := by
  intro q
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
  exact ⟨m.1, rfl⟩

theorem realizesVia_nat_of {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥Γ →* ↥H}
    (hπ : Function.Surjective π) (hZU : Z ≤ U)
    (hHU : ∀ h : ↥H, ∀ u ∈ U, (h : MulAut V) u ∈ U)
    (hHZ : ∀ h : ↥H, ∀ z ∈ Z, (h : MulAut V) z ∈ Z) (f : ↥U →* Multiplicative (ι → K))
    (hfs : Function.Surjective f) (hfk : ∀ u : ↥U, f u = 1 ↔ (u : V) ∈ Z)
    (hfe : ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) u ∈ U),
      f ⟨_, hu⟩ = natAct Γ γ (f u)) :
    (FFModel.nat Γ).RealizesVia H U Z π := by
  refine ⟨hπ, hZU, bot_le, hHU, hHZ, fun _ _ _ => trivial, ?_, ?_⟩
  · intro (γ : ↥Γ) (m : Multiplicative (ι → K)) hm
    have hm' : m = 1 := Subgroup.mem_bot.1 hm
    show natAct Γ γ m ∈ (⊥ : Subgroup (Multiplicative (ι → K)))
    rw [hm', natAct_one_right]
    exact Subgroup.one_mem _
  · refine ⟨(natQuot Γ).comp f, natQuot_surjective.comp hfs, fun u => ?_, ?_⟩
    · rw [MonoidHom.comp_apply, ← hfk u]
      exact ⟨fun h => natQuot_injective (h.trans (map_one _).symm), fun h => by
        rw [h, map_one]⟩
    · intro (γ : ↥Γ) u m hu hm hum
      have hm' : (m.1 : Multiplicative (ι → K)) = f u := by
        have : natQuot Γ m.1 = natQuot Γ (f u) := hum.symm
        exact natQuot_injective this
      show natQuot Γ (f ⟨_, hu⟩) = natQuot Γ (natAct Γ γ m.1)
      calc natQuot Γ (f ⟨_, hu⟩) = natQuot Γ (natAct Γ γ (f u)) := congrArg _ (hfe γ u hu)
        _ = natQuot Γ (natAct Γ γ m.1) := by rw [hm']

theorem exists_natMap {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥Γ →* ↥H}
    (h : (FFModel.nat Γ).RealizesVia H U Z π) :
    ∃ f : ↥U →* Multiplicative (ι → K), Function.Surjective f ∧
      (∀ u : ↥U, f u = 1 ↔ (u : V) ∈ Z) ∧
      ∀ (γ : ↥Γ) (u : ↥U) (hu : ((π γ : ↥H) : MulAut V) u ∈ U),
        f ⟨_, hu⟩ = natAct Γ γ (f u) := by
  obtain ⟨f, hfs, hfk, hfe⟩ := RealizesVia.exists_secMap (D := FFModel.nat Γ) rfl h
  refine ⟨(FFModel.nat Γ).sec.subtype.comp f, fun y => ?_, fun u => ?_, fun γ u hu => hfe γ u hu⟩
  · obtain ⟨u, hu⟩ := hfs ⟨y, trivial⟩
    exact ⟨u, congrArg Subtype.val hu⟩
  · rw [← hfk u]
    exact ⟨fun h1 => Subtype.ext h1, fun h1 => congrArg Subtype.val h1⟩

end Nat

theorem RealizesVia.card_eq {D : FFModel} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : D.Gam →* ↥H} (h : D.RealizesVia H U Z π) :
    Nat.card U = Nat.card D.Mod * Nat.card Z := by
  obtain ⟨_, hZU, _, _, _, _, _, β, hβs, hβk, _⟩ := h
  have hker : β.ker = Z.subgroupOf U := by
    ext u
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, hβk]
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup β.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective β hβs).toEquiv, hker,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZU).toEquiv]

theorem card_natMod {n : ℕ} {K : Type} [Field K] [Finite K]
    (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin n) K)) :
    Nat.card (FFModel.nat Γ).Mod = Nat.card K ^ n := by
  rw [← Nat.card_congr (MulEquiv.ofBijective (natQuot Γ)
    ⟨natQuot_injective, natQuot_surjective⟩).toEquiv, Nat.card_congr Multiplicative.toAdd,
    Nat.card_fun, Nat.card_eq_fintype_card (α := Fin n), Fintype.card_fin]

theorem mem_statedSL_zmod {n : ℕ} (x : GL (Fin n) (ZMod 2)) : x ∈ StatedSL n (ZMod 2) :=
  CFSG.Open.StatedAPI.mem_statedSL_zmod_two x

@[expose] noncomputable def ringEquivZModTwo (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = 2) : K ≃+* ZMod 2 :=
  let _ : Fintype K := Fintype.ofFinite K
  FiniteField.ringEquivOfCardEq (by rw [ZMod.card, ← Nat.card_eq_fintype_card, hK])

theorem det_map_symm {K : Type} [Field K] (e : K ≃+* ZMod 2) {n : ℕ} (g : GL (Fin n) (ZMod 2)) :
    ((Matrix.GeneralLinearGroup.map e.symm.toRingHom g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K).det = 1 := by
  have h1 : ((Matrix.GeneralLinearGroup.map e.symm.toRingHom g : GL (Fin n) K) :
      Matrix (Fin n) (Fin n) K) =
        e.symm.toRingHom.mapMatrix (g : Matrix (Fin n) (Fin n) (ZMod 2)) := rfl
  rw [h1, ← RingHom.map_det, det_eq_one, map_one]

@[expose] noncomputable def slOfZMod {K : Type} [Field K] (e : K ≃+* ZMod 2) (n : ℕ) :
    ↥(StatedSL n (ZMod 2)) →* ↥(StatedSL n K) where
  toFun g := ⟨Matrix.GeneralLinearGroup.map e.symm.toRingHom (g : GL (Fin n) (ZMod 2)),
    Subgroup.subset_closure (det_map_symm e (g : GL (Fin n) (ZMod 2)))⟩
  map_one' := by ext : 1; exact map_one _
  map_mul' g h := by ext : 1; exact map_mul _ _ _

theorem slOfZMod_coe {K : Type} [Field K] (e : K ≃+* ZMod 2) {n : ℕ}
    (g : ↥(StatedSL n (ZMod 2))) :
    (((slOfZMod e n g : ↥(StatedSL n K)) : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      ((g : GL (Fin n) (ZMod 2)) : Matrix (Fin n) (Fin n) (ZMod 2)).map e.symm :=
  rfl

theorem slOfZMod_surjective {K : Type} [Field K] (e : K ≃+* ZMod 2) (n : ℕ) :
    Function.Surjective (slOfZMod e n) := by
  intro g
  refine ⟨⟨Matrix.GeneralLinearGroup.map e.toRingHom (g : GL (Fin n) K),
    mem_statedSL_zmod _⟩, ?_⟩
  apply Subtype.ext
  apply Units.ext
  rw [slOfZMod_coe]
  ext i j
  simp

@[expose] def vecOfField {K : Type} [Field K] (e : K ≃+* ZMod 2) (n : ℕ) :
    Multiplicative (Fin n → K) →* Multiplicative (Fin n → ZMod 2) where
  toFun x := Multiplicative.ofAdd fun i => e (Multiplicative.toAdd x i)
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext i
    simp
  map_mul' x y := by
    apply Multiplicative.toAdd.injective
    funext i
    simp

theorem vecOfField_surjective {K : Type} [Field K] (e : K ≃+* ZMod 2) (n : ℕ) :
    Function.Surjective (vecOfField e n) := by
  intro y
  refine ⟨Multiplicative.ofAdd fun i => e.symm (Multiplicative.toAdd y i), ?_⟩
  apply Multiplicative.toAdd.injective
  funext i
  simp [vecOfField]

theorem vecOfField_eq_one {K : Type} [Field K] (e : K ≃+* ZMod 2) {n : ℕ}
    {x : Multiplicative (Fin n → K)} : vecOfField e n x = 1 ↔ x = 1 := by
  constructor
  · intro h
    apply Multiplicative.toAdd.injective
    funext i
    have := congrFun (congrArg Multiplicative.toAdd h) i
    simpa [vecOfField] using this
  · rintro rfl
    exact map_one _

theorem vecOfField_natAct {K : Type} [Field K] (e : K ≃+* ZMod 2) {n : ℕ}
    (γ : ↥(StatedSL n (ZMod 2))) (x : Multiplicative (Fin n → K)) :
    vecOfField e n (natAct (StatedSL n K) (slOfZMod e n γ) x) =
      natAct (StatedSL n (ZMod 2)) γ (vecOfField e n x) := by
  apply Multiplicative.toAdd.injective
  funext i
  simp only [vecOfField, natAct, MonoidHom.coe_mk, OneHom.coe_mk, toAdd_ofAdd, slOfZMod_coe]
  rw [← RingHom.coe_coe e, RingHom.map_mulVec]
  congr 1
  ext k l
  simp

theorem realizesVia_zmod {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2) {n : ℕ}
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSL n K) →* ↥H}
    (h : (FFModel.nat (StatedSL n K)).RealizesVia H U Z π) :
    (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U Z
      (π.comp (slOfZMod (ringEquivZModTwo K hK) n)) := by
  set e := ringEquivZModTwo K hK with he
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap h
  refine realizesVia_nat_of (h.1.comp (slOfZMod_surjective e n)) h.2.1 h.2.2.2.1 h.2.2.2.2.1
    ((vecOfField e n).comp f) ((vecOfField_surjective e n).comp hfs) (fun u => ?_)
    (fun γ u hu => ?_)
  · rw [MonoidHom.comp_apply, vecOfField_eq_one, hfk]
  · exact (congrArg (vecOfField e n) (hfe (slOfZMod e n γ) u hu)).trans
      (vecOfField_natAct e γ _)

theorem BinaryNaturalSL.exists_zmod {H : Subgroup (MulAut V)} {U Z : Subgroup V} {n : ℕ}
    (h : BinaryNaturalSL H U Z n 1) :
    ∃ π : ↥(StatedSL n (ZMod 2)) →* ↥H,
      (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U Z π := by
  obtain ⟨K, _, _, hK, π, hπ⟩ := h
  exact ⟨_, realizesVia_zmod (by simpa using hK) hπ⟩

theorem natSL_injective {n : ℕ} {H : Subgroup (MulAut V)} {U Z : Subgroup V}
    {π : ↥(StatedSL n (ZMod 2)) →* ↥H}
    (h : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U Z π) : Function.Injective π :=
  RealizesVia.injective_of_faithful' (FFModel.nat_faithful _) h

omit [CommGroup V] in
theorem eq_one_or_eq_of_card_two {M : Type*} [Group M] {A : Subgroup M} (hA : Nat.card A = 2)
    {w : M} (hw : w ∈ A) (hw1 : w ≠ 1) {x : M} (hx : x ∈ A) : x = 1 ∨ x = w := by
  by_contra hcon
  push Not at hcon
  exact G6.false_of_card_two hA hw hx hw1 hcon.1 (Ne.symm hcon.2)

theorem card_commV_le_of_natSL [Finite V] {n : ℕ} (hn : 2 ≤ n)
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} {π : ↥(StatedSL n (ZMod 2)) →* ↥H}
    (h : (FFModel.nat (StatedSL n (ZMod 2))).RealizesVia H U Z π) {a : MulAut V} (ha : a ∈ H)
    (ha1 : a ≠ 1) (htr : Nat.card (commV (Subgroup.zpowers a)) = 2) :
    Nat.card (commV H) ≤ 2 ^ n := by
  classical
  obtain ⟨γ₀, hγ₀⟩ : ∃ γ₀ : ↥(StatedSL n (ZMod 2)), π γ₀ = ⟨a, ha⟩ := h.1 ⟨a, ha⟩
  set x : GL (Fin n) (ZMod 2) := (γ₀ : GL (Fin n) (ZMod 2)) with hx
  obtain ⟨w, hw, hw1⟩ : ∃ w ∈ commV (Subgroup.zpowers a), w ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have : commV (Subgroup.zpowers a) = ⊥ := eq_bot_iff.2 fun y hy => hcon y hy
    rw [this, Subgroup.card_bot] at htr
    omega
  obtain ⟨f, hfs, hfk, hfe⟩ := exists_natMap h
  have hHU : ∀ u ∈ U, a u ∈ U := fun u hu => h.2.2.2.1 ⟨a, ha⟩ u hu
  have hpa : ((π γ₀ : ↥H) : MulAut V) = a := by rw [hγ₀]
  have hxt : IsTransvecGL x := by
    obtain ⟨y, hy⟩ : ∃ y : Fin n → ZMod 2,
        ∀ hwU : w ∈ U, Multiplicative.toAdd (f ⟨w, hwU⟩) = y := by
      by_cases hwU : w ∈ U
      · exact ⟨Multiplicative.toAdd (f ⟨w, hwU⟩), fun _ => rfl⟩
      · exact ⟨0, fun h' => absurd h' hwU⟩
    refine ⟨?_, y, fun v => ?_⟩
    · intro h1
      apply ha1
      have : γ₀ = 1 := Subtype.ext h1
      rw [← hpa, this, map_one]
      rfl
    · obtain ⟨u, hu⟩ := hfs (Multiplicative.ofAdd v)
      have hcU : a u * (u : V)⁻¹ ∈ U := U.mul_mem (hHU u u.2) (U.inv_mem u.2)
      have hgc : Multiplicative.toAdd (f ⟨_, hcU⟩) =
          (x : Matrix (Fin n) (Fin n) (ZMod 2)) *ᵥ v - v := by
        have h1 : (⟨_, hcU⟩ : ↥U) = ⟨a u, hHU u u.2⟩ * u⁻¹ := rfl
        have h2 := hfe γ₀ u (by rw [hpa]; exact hHU u u.2)
        have h3 : (⟨((π γ₀ : ↥H) : MulAut V) u, by rw [hpa]; exact hHU u u.2⟩ : ↥U) =
            ⟨a u, hHU u u.2⟩ := Subtype.ext (by
              show ((π γ₀ : ↥H) : MulAut V) u = a u
              rw [hpa])
        rw [h3] at h2
        rw [h1, map_mul, map_inv, toAdd_mul, toAdd_inv, h2, hu]
        simp only [natAct, toAdd_ofAdd]
        abel
      rcases eq_one_or_eq_of_card_two htr hw hw1 (G6.mem_commV_of_mem (Subgroup.mem_zpowers a) u)
        with h0 | h0
      · left
        rw [← hgc]
        have : (⟨_, hcU⟩ : ↥U) = 1 := Subtype.ext h0
        rw [this, map_one]
        rfl
      · right
        have hwU : w ∈ U := h0 ▸ hcU
        rw [← hy hwU, ← hgc]
        congr 2
        exact Subtype.ext h0
  obtain ⟨c, hc⟩ := exists_conj_closure_eq_top hn hxt
  set c' : Fin n → ↥(StatedSL n (ZMod 2)) := fun i => ⟨c i, mem_statedSL_zmod _⟩ with hc'
  have htop : Subgroup.closure (Set.range fun i => c' i * γ₀ * (c' i)⁻¹) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range fun i => c' i * γ₀ * (c' i)⁻¹)).map
        (StatedSL n (ZMod 2)).subtype = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp, ← hc]
      rfl
    rw [eq_top_iff]
    intro y _
    have hy : (y : GL (Fin n) (ZMod 2)) ∈ (Subgroup.closure (Set.range fun i =>
        c' i * γ₀ * (c' i)⁻¹)).map (StatedSL n (ZMod 2)).subtype := by
      rw [hmap]
      trivial
    obtain ⟨z, hz, hzy⟩ := hy
    rw [show y = z from Subtype.ext hzy.symm]
    exact hz
  set b : Fin n → MulAut V := fun i => ((π (c' i) : ↥H) : MulAut V) * a *
    ((π (c' i) : ↥H) : MulAut V)⁻¹ with hb
  have hHb : H ≤ Subgroup.closure (Set.range b) := by
    intro y hy
    obtain ⟨γ, hγ⟩ : ∃ γ : ↥(StatedSL n (ZMod 2)), π γ = ⟨y, hy⟩ := h.1 ⟨y, hy⟩
    have hγm : γ ∈ Subgroup.closure (Set.range fun i => c' i * γ₀ * (c' i)⁻¹) := by
      rw [htop]
      trivial
    have h1 : π γ ∈ (Subgroup.closure (Set.range fun i => c' i * γ₀ * (c' i)⁻¹)).map π :=
      Subgroup.mem_map_of_mem π hγm
    rw [MonoidHom.map_closure] at h1
    have h2 : ((π γ : ↥H) : MulAut V) ∈ (Subgroup.closure (π '' Set.range fun i =>
        c' i * γ₀ * (c' i)⁻¹)).map H.subtype := Subgroup.mem_map_of_mem H.subtype h1
    rw [MonoidHom.map_closure] at h2
    have h3 : H.subtype '' (π '' Set.range fun i => c' i * γ₀ * (c' i)⁻¹) = Set.range b := by
      ext z
      simp only [Set.mem_image, Set.mem_range, Subgroup.coe_subtype]
      constructor
      · rintro ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, rfl⟩
        refine ⟨i, ?_⟩
        simp [hb, map_mul, map_inv, hpa]
      · rintro ⟨i, rfl⟩
        refine ⟨_, ⟨_, ⟨i, rfl⟩, rfl⟩, ?_⟩
        simp [hb, map_mul, map_inv, hpa]
    rw [h3, hγ] at h2
    exact h2
  have hbt : ∀ i, Nat.card (commV (Subgroup.zpowers (b i))) = 2 := fun i => by
    rw [hb, G6.card_commV_zpowers_conj, htr]
  have hle : commV H ≤ ⨆ i ∈ (Finset.univ : Finset (Fin n)), commV (Subgroup.zpowers (b i)) := by
    refine (G6.commV_mono hHb).trans (G6.commV_closure_le ?_)
    rintro _ ⟨i, rfl⟩ v
    exact (le_iSup₂ (f := fun i (_ : i ∈ (Finset.univ : Finset (Fin n))) =>
      commV (Subgroup.zpowers (b i))) i (Finset.mem_univ i))
      (G6.mem_commV_of_mem (Subgroup.mem_zpowers _) v)
  calc Nat.card (commV H)
      ≤ Nat.card ↥(⨆ i ∈ (Finset.univ : Finset (Fin n)), commV (Subgroup.zpowers (b i))) :=
        Subgroup.card_le_of_le hle
    _ ≤ ∏ i ∈ (Finset.univ : Finset (Fin n)), Nat.card (commV (Subgroup.zpowers (b i))) :=
        card_biSup_le _ _
    _ = 2 ^ n := by simp [hbt]

end CFSG.Quasithin.G64
