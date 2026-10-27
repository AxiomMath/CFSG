module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListRank2
public import CFSG.Quasithin.Background.C35InspLift
public import CFSG.Quasithin.Background.E1Defs

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.C35Pf

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank Matrix

section Irred

variable {F : Type} [Field F]

@[expose] def sl2Upper (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, t; 0, 1], by simp [Matrix.det_fin_two]⟩

@[expose] def sl2Lower (t : F) : SpecialLinearGroup (Fin 2) F :=
  ⟨!![1, 0; t, 1], by simp [Matrix.det_fin_two]⟩

theorem sl2Upper_mulVec (t : F) (w : Fin 2 → F) :
    ((sl2Upper t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w =
      ![w 0 + t * w 1, w 1] := by
  ext i
  fin_cases i <;> simp [sl2Upper, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem sl2Lower_mulVec (t : F) (w : Fin 2 → F) :
    ((sl2Lower t : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ w =
      ![w 0, t * w 0 + w 1] := by
  ext i
  fin_cases i <;> simp [sl2Lower, Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem eq_top_of_sl2_invariant (W : AddSubgroup (Fin 2 → F))
    (hW : ∀ D : SpecialLinearGroup (Fin 2) F, ∀ w ∈ W,
      (D : Matrix (Fin 2) (Fin 2) F) *ᵥ w ∈ W) {w : Fin 2 → F} (hw : w ∈ W) (hw0 : w ≠ 0) :
    W = ⊤ := by
  have hU : ∀ t : F, ∀ w ∈ W, (![t * w 1, 0] : Fin 2 → F) ∈ W := by
    intro t w hw
    have h := W.sub_mem (hW (sl2Upper t) w hw) hw
    rw [sl2Upper_mulVec] at h
    convert h using 1
    ext i
    fin_cases i <;> simp
  have hL : ∀ t : F, ∀ w ∈ W, (![0, t * w 0] : Fin 2 → F) ∈ W := by
    intro t w hw
    have h := W.sub_mem (hW (sl2Lower t) w hw) hw
    rw [sl2Lower_mulVec] at h
    convert h using 1
    ext i
    fin_cases i <;> simp
  have hboth : (∀ s : F, (![s, 0] : Fin 2 → F) ∈ W) ∧ ∀ s : F, (![0, s] : Fin 2 → F) ∈ W := by
    by_cases h1 : w 1 = 0
    · have h0 : w 0 ≠ 0 := by
        intro h0
        apply hw0
        ext i
        fin_cases i <;> simp [h0, h1]
      have hs : ∀ s : F, (![0, s] : Fin 2 → F) ∈ W := fun s => by
        have := hL (s / w 0) w hw
        rwa [div_mul_cancel₀ s h0] at this
      refine ⟨fun s => ?_, hs⟩
      have := hU s ![0, 1] (hs 1)
      simpa using this
    · have hs : ∀ s : F, (![s, 0] : Fin 2 → F) ∈ W := fun s => by
        have := hU (s / w 1) w hw
        rwa [div_mul_cancel₀ s h1] at this
      refine ⟨hs, fun s => ?_⟩
      have := hL s ![1, 0] (hs 1)
      simpa using this
  rw [eq_top_iff]
  intro u _
  have hu : u = ![u 0, 0] + ![0, u 1] := by
    ext i
    fin_cases i <;> simp
  rw [hu]
  exact W.add_mem (hboth.1 _) (hboth.2 _)

end Irred

variable {A : Type} [Group A]

theorem isNaturalSection_of_equiv {M₀ V Z : Subgroup A} {N : Subgroup ↥M₀} {F : Type} [Field F]
    (hMV : M₀ ≤ Subgroup.normalizer (V : Set A)) (hVZ : ¬ V ≤ Z)
    (α : ↥M₀ →* SpecialLinearGroup (Fin 2) F) (hα : Function.Surjective α) (hker : α.ker = N)
    (β : ↥V →* Multiplicative (Fin 2 → F)) (hβker : β.ker = Z.subgroupOf V)
    (hequiv : ∀ (a : ↥M₀) (u v : ↥V), (v : A) = a * u * a⁻¹ →
      Multiplicative.toAdd (β v) = ((α a : SpecialLinearGroup (Fin 2) F) :
        Matrix (Fin 2) (Fin 2) F) *ᵥ Multiplicative.toAdd (β u)) :
    IsNaturalSection M₀ V Z N (StatedSL 2 F) := by
  let W : AddSubgroup (Fin 2 → F) :=
    { carrier := {w | ∃ v : ↥V, Multiplicative.toAdd (β v) = w}
      add_mem' := by
        rintro _ _ ⟨u, rfl⟩ ⟨v, rfl⟩
        exact ⟨u * v, by rw [map_mul]; rfl⟩
      zero_mem' := ⟨1, by rw [map_one]; rfl⟩
      neg_mem' := by
        rintro _ ⟨u, rfl⟩
        exact ⟨u⁻¹, by rw [map_inv]; rfl⟩ }
  have hWinv : ∀ D : SpecialLinearGroup (Fin 2) F, ∀ w ∈ W,
      (D : Matrix (Fin 2) (Fin 2) F) *ᵥ w ∈ W := by
    rintro D _ ⟨u, rfl⟩
    obtain ⟨a, rfl⟩ := hα D
    have hv : (a : A) * u * (a : A)⁻¹ ∈ V :=
      (Subgroup.mem_normalizer_iff.1 (hMV a.2) u).1 u.2
    exact ⟨⟨_, hv⟩, hequiv a u ⟨_, hv⟩ rfl⟩
  obtain ⟨v, hvV, hvZ⟩ := Set.not_subset.1 hVZ
  have hβv : Multiplicative.toAdd (β ⟨v, hvV⟩) ≠ 0 := by
    intro h0
    have h1 : β ⟨v, hvV⟩ = 1 := h0
    have h2 : (⟨v, hvV⟩ : ↥V) ∈ β.ker := h1
    rw [hβker] at h2
    exact hvZ h2
  have hWtop := eq_top_of_sl2_invariant W hWinv ⟨⟨v, hvV⟩, rfl⟩ hβv
  have hβs : Function.Surjective β := by
    intro y
    have hy : Multiplicative.toAdd y ∈ W := by
      rw [hWtop]
      exact AddSubgroup.mem_top _
    obtain ⟨u, hu⟩ := hy
    exact ⟨u, hu⟩
  refine ⟨hMV, (specialLinearGroupEquivStatedSL 2 F).toMonoidHom.comp α,
    (specialLinearGroupEquivStatedSL 2 F).surjective.comp hα, ?_, β, hβs, hβker,
    fun a u v huv => hequiv a u v huv⟩
  rw [← hker]
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff]

section Lift

variable {K M₀ : Subgroup A} (hM₀K : M₀ ≤ K) {P G : Type} [Group P] [Group G]
  (θ : ↥K →* P) (π : G →* P) (N : Subgroup G) (hinj : Set.InjOn π (N : Set G))
  (himg : img θ M₀ = N.map π)

include himg in
theorem exists_lift (x : ↥M₀) : ∃ n : G, n ∈ N ∧ π n = θ ⟨x, hM₀K x.2⟩ := by
  have hx : θ ⟨x, hM₀K x.2⟩ ∈ img θ M₀ := ⟨⟨x, hM₀K x.2⟩, Subgroup.mem_subgroupOf.2 x.2, rfl⟩
  rw [himg] at hx
  obtain ⟨n, hn, hnx⟩ := hx
  exact ⟨n, hn, hnx⟩

include hinj in
@[expose] noncomputable def liftHom : ↥M₀ →* ↥N where
  toFun x := ⟨(exists_lift hM₀K θ π N himg x).choose,
    (exists_lift hM₀K θ π N himg x).choose_spec.1⟩
  map_one' := by
    apply Subtype.ext
    refine hinj (exists_lift hM₀K θ π N himg 1).choose_spec.1 N.one_mem ?_
    rw [(exists_lift hM₀K θ π N himg 1).choose_spec.2]
    show θ 1 = π 1
    rw [map_one, map_one]
  map_mul' x y := by
    apply Subtype.ext
    refine hinj (exists_lift hM₀K θ π N himg (x * y)).choose_spec.1
      (N.mul_mem (exists_lift hM₀K θ π N himg x).choose_spec.1
        (exists_lift hM₀K θ π N himg y).choose_spec.1) ?_
    rw [(exists_lift hM₀K θ π N himg (x * y)).choose_spec.2]
    show θ (⟨x, hM₀K x.2⟩ * ⟨y, hM₀K y.2⟩) =
      π ((exists_lift hM₀K θ π N himg x).choose * (exists_lift hM₀K θ π N himg y).choose)
    rw [map_mul, map_mul, (exists_lift hM₀K θ π N himg x).choose_spec.2,
      (exists_lift hM₀K θ π N himg y).choose_spec.2]

theorem liftHom_spec (x : ↥M₀) :
    π (liftHom hM₀K θ π N hinj himg x) = θ ⟨x, hM₀K x.2⟩ :=
  (exists_lift hM₀K θ π N himg x).choose_spec.2

theorem liftHom_surjective : Function.Surjective (liftHom hM₀K θ π N hinj himg) := by
  rintro ⟨n, hn⟩
  have hn' : π n ∈ img θ M₀ := by
    rw [himg]
    exact ⟨n, hn, rfl⟩
  obtain ⟨y, hy, hyn⟩ := hn'
  refine ⟨⟨y, Subgroup.mem_subgroupOf.1 hy⟩, Subtype.ext ?_⟩
  refine hinj (liftHom hM₀K θ π N hinj himg _).2 hn ?_
  rw [liftHom_spec, ← hyn]

theorem liftHom_eq_one_iff (x : ↥M₀) :
    liftHom hM₀K θ π N hinj himg x = 1 ↔ θ ⟨x, hM₀K x.2⟩ = 1 := by
  rw [← liftHom_spec hM₀K θ π N hinj himg x]
  constructor
  · intro h
    rw [h]
    exact map_one π
  · intro h
    apply Subtype.ext
    refine hinj (liftHom hM₀K θ π N hinj himg x).2 N.one_mem ?_
    rw [h]
    exact (map_one π).symm

end Lift

theorem isPSL2_modO2 {M₀ : Subgroup A} {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hf : Nat.card F = 2 ^ f) (hf2 : 2 ≤ f) (α : ↥M₀ →* SpecialLinearGroup (Fin 2) F)
    (hα : Function.Surjective α) (hker : IsPGroup 2 α.ker) : IsPSL 2 2 f (ModO2 M₀) := by
  have hK4 : ∃ s : Finset F, s.card = 4 := by
    refine CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four ?_
    rw [hf]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  have := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hK4
  have hnab := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian hK4
  have h2f : 2 ^ 2 ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf2
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_, ?_⟩, F, inferInstance, inferInstance, hf,
    ⟨(CFSG.QuasithinUnique.Vol2Native.A312L.modO2EquivOfHom hnab α hα hker).trans
      CFSG.QuasithinUnique.Vol2Native.A312L.sl2EquivStatedProj⟩⟩
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega
  · intro h
    have := congrArg Prod.snd h
    simp only at this
    omega

theorem natural_of_radical [Finite A] {M₀ V Z : Subgroup A} (hVM : V ≤ M₀)
    (hMV : M₀ ≤ Subgroup.normalizer (V : Set A)) (hVZ : ¬ V ≤ Z) (hVO : V ≤ pCoreOf 2 M₀)
    {N : Type} [Group N] {F : Type} [Field F] [Finite F] [CharP F 2]
    (hK4 : ∃ s : Finset F, s.card = 4) (ν : ↥M₀ →* N) (hν : Function.Surjective ν)
    (hνker : IsPGroup 2 ν.ker) (act : N →* SpecialLinearGroup (Fin 2) F)
    (hact : Function.Surjective act) (hactker : IsPGroup 2 act.ker) (c : N → (Fin 2 → F))
    (hcmul : ∀ r s : N, act r = 1 → act s = 1 → c (r * s) = c r + c s)
    (hcZ : ∀ (v : A) (hv : v ∈ V), act (ν ⟨v, hVM hv⟩) = 1 →
      (c (ν ⟨v, hVM hv⟩) = 0 ↔ v ∈ Z))
    (hceq : ∀ n r : N, act r = 1 →
      c (n * r * n⁻¹) =
        ((act n : SpecialLinearGroup (Fin 2) F) : Matrix (Fin 2) (Fin 2) F) *ᵥ c r) :
    (act.comp ν).ker = CFSG.pCore 2 ↥M₀ ∧
      IsNaturalSection M₀ V Z (CFSG.pCore 2 ↥M₀) (StatedSL 2 F) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_isSimple hK4
  have hnab := CFSG.QuasithinUnique.Vol2Native.A312L.sl2_nonabelian hK4
  have hker2 : IsPGroup 2 (act.comp ν).ker := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := hactker ⟨ν x, hx⟩
    have hk' : ν (x ^ 2 ^ k) = 1 := by
      rw [map_pow]
      exact congrArg Subtype.val hk
    obtain ⟨l, hl⟩ := hνker ⟨x ^ 2 ^ k, hk'⟩
    refine ⟨k + l, Subtype.ext ?_⟩
    have hl' : (x ^ 2 ^ k) ^ 2 ^ l = 1 := congrArg Subtype.val hl
    show x ^ 2 ^ (k + l) = 1
    rw [pow_add, pow_mul, hl']
  have hO : CFSG.pCore 2 ↥M₀ = (act.comp ν).ker :=
    CFSG.QuasithinUnique.Vol2Native.A312L.pCore_two_eq_ker hnab (act.comp ν) (hact.comp hν) hker2
  have hV1 : ∀ (v : A) (hv : v ∈ V), act (ν ⟨v, hVM hv⟩) = 1 := by
    intro v hv
    obtain ⟨y, hy, hyv⟩ := hVO hv
    have hy' : y ∈ (act.comp ν).ker := by
      rw [← hO]
      exact hy
    have : y = ⟨v, hVM hv⟩ := Subtype.ext hyv
    rw [← this]
    exact hy'
  have hc1 : c 1 = 0 := by
    have h := hcmul 1 1 (map_one act) (map_one act)
    rw [mul_one] at h
    exact (add_eq_left.mp h.symm)
  let β : ↥V →* Multiplicative (Fin 2 → F) :=
    { toFun := fun v => Multiplicative.ofAdd (c (ν ⟨v, hVM v.2⟩))
      map_one' := by
        show Multiplicative.ofAdd (c (ν 1)) = 1
        rw [map_one, hc1]
        rfl
      map_mul' := fun u v => by
        show Multiplicative.ofAdd (c (ν (⟨u, hVM u.2⟩ * ⟨v, hVM v.2⟩))) = _
        rw [map_mul, hcmul _ _ (hV1 u u.2) (hV1 v v.2)]
        rfl }
  refine ⟨hO.symm, isNaturalSection_of_equiv hMV hVZ (act.comp ν) (hact.comp hν) hO.symm β ?_ ?_⟩
  · ext v
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    show Multiplicative.ofAdd (c (ν ⟨v, hVM v.2⟩)) = 1 ↔ _
    rw [← hcZ v v.2 (hV1 v v.2)]
    rfl
  · intro a u v huv
    show c (ν ⟨v, hVM v.2⟩) = _ *ᵥ c (ν ⟨u, hVM u.2⟩)
    have hv : (⟨v, hVM v.2⟩ : ↥M₀) = a * ⟨u, hVM u.2⟩ * a⁻¹ := Subtype.ext huv
    rw [hv, map_mul, map_mul, map_inv]
    exact hceq _ _ (hV1 u u.2)

theorem isMaxParabolic2_of_coatom {K Y : Subgroup A} {P : Type} [Group P]
    (θ : ↥K →* P) (hθker : θ.ker ≤ Subgroup.center ↥K) (hpar : IsParabolic2 K Y) (hne : Y ≠ K)
    (hZY : centerOf K ≤ Y) (hco : IsCoatom (img θ Y)) : IsMaxParabolic2 K Y := by
  refine ⟨hpar, hne, fun Q hQ hQK hYQ => ?_⟩
  have hle : img θ Y ≤ img θ Q := Subgroup.map_mono fun x hx =>
    Subgroup.mem_subgroupOf.2 (hYQ (Subgroup.mem_subgroupOf.1 hx))
  have hQt : img θ Q ≠ ⊤ := img_ne_top hθker hQ.1 (hZY.trans hYQ) hQK
  have heq : img θ Q = img θ Y := by
    rcases hco.le_iff.1 hle with h | h
    · exact absurd h hQt
    · exact h
  refine le_antisymm (fun x hx => ?_) hYQ
  have hxK : x ∈ K := hQ.1 hx
  have : θ ⟨x, hxK⟩ ∈ img θ Y := heq ▸ ⟨⟨x, hxK⟩, Subgroup.mem_subgroupOf.2 hx, rfl⟩
  exact mem_of_img_mem hθker hZY this

end CFSG.Quasithin.C35Pf
