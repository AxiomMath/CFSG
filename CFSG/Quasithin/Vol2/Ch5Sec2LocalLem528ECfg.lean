module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528ESL3
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.A312ListCore
public import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic

public section

namespace CFSG.Quasithin.H13.SL3E

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X7a

variable {G : Type} [Group G] {F : Type} [Field F]

theorem card_subgroupOf_eq (H K : Subgroup G) :
    Nat.card (H.subgroupOf K) = Nat.card ↥(H ⊓ K) := by
  rw [← Subgroup.subgroupOf_map_subtype, Subgroup.card_map_of_injective K.subtype_injective]

@[expose] def mulVecHom (g : SpecialLinearGroup (Fin 3) F) :
    Multiplicative (Fin 3 → F) →* Multiplicative (Fin 3 → F) where
  toFun v := Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd v)
  map_one' := by simp
  map_mul' v w := by simp [Matrix.mulVec_add]

theorem toAdd_mulVecHom (g : SpecialLinearGroup (Fin 3) F) (v : Multiplicative (Fin 3 → F)) :
    Multiplicative.toAdd (mulVecHom g v) =
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd v := rfl

theorem mulVecHom_inv_apply (g : SpecialLinearGroup (Fin 3) F) (v : Multiplicative (Fin 3 → F)) :
    mulVecHom g⁻¹ (mulVecHom g v) = v := by
  apply Multiplicative.toAdd.injective
  rw [toAdd_mulVecHom, toAdd_mulVecHom, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul,
    inv_mul_cancel, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]

theorem mulVecHom_apply_inv (g : SpecialLinearGroup (Fin 3) F) (v : Multiplicative (Fin 3 → F)) :
    mulVecHom g (mulVecHom g⁻¹ v) = v := by
  have := mulVecHom_inv_apply g⁻¹ v
  rwa [inv_inv] at this

structure SL3Data (X R : Subgroup G) (F : Type) [Field F] where
  φ : ↥X →* SpecialLinearGroup (Fin 3) F
  surj : Function.Surjective φ
  le : R ≤ X
  ker : ∀ x : ↥X, φ x = 1 ↔ (x : G) ∈ R
  ψ : ↥R →* Multiplicative (Fin 3 → F)
  ψsurj : Function.Surjective ψ
  equiv : ∀ (x : ↥X) (r r' : ↥R), (r' : G) = x * r * x⁻¹ →
    Multiplicative.toAdd (ψ r') =
      ((φ x : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (ψ r)

namespace SL3Data

variable {X R : Subgroup G} (c : SL3Data X R F)

@[expose] def img (A : Subgroup G) : Subgroup (SpecialLinearGroup (Fin 3) F) :=
  (A.subgroupOf X).map c.φ

theorem mem_img {A : Subgroup G} {g : SpecialLinearGroup (Fin 3) F} :
    g ∈ c.img A ↔ ∃ a : ↥X, (a : G) ∈ A ∧ c.φ a = g := by
  simp [img, Subgroup.mem_map, Subgroup.mem_subgroupOf]

theorem img_mono {A B : Subgroup G} (h : A ≤ B) : c.img A ≤ c.img B :=
  Subgroup.map_mono fun _ hx => h hx

@[expose] def vecOf (A : Subgroup G) : Subgroup (Multiplicative (Fin 3 → F)) :=
  (A.subgroupOf R).map c.ψ

theorem mem_vecOf {A : Subgroup G} {v : Multiplicative (Fin 3 → F)} :
    v ∈ c.vecOf A ↔ ∃ r : ↥R, (r : G) ∈ A ∧ c.ψ r = v := by
  simp [vecOf, Subgroup.mem_map, Subgroup.mem_subgroupOf]

include c in
theorem conj_mem {g : ↥X} {r : G} (hr : r ∈ R) : (g : G) * r * (g : G)⁻¹ ∈ R := by
  have hrX : r ∈ X := c.le hr
  have h1 := (c.ker ⟨r, hrX⟩).mpr hr
  have : c.φ (g * ⟨r, hrX⟩ * g⁻¹) = 1 := by rw [map_mul, map_mul, h1, mul_one, map_inv,
    mul_inv_cancel]
  exact (c.ker _).mp this

theorem card_eq_mul [Finite G] {A : Subgroup G} (hAX : A ≤ X) :
    Nat.card A = Nat.card (c.img A) * Nat.card ↥(A ⊓ R) := by
  set f := c.φ.comp (A.subgroupOf X).subtype with hf
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv] at h1
  have hrange : f.range = c.img A := by rw [hf, MonoidHom.range_comp, Subgroup.range_subtype]; rfl
  have hker : Nat.card f.ker = Nat.card ↥(A ⊓ R) := by
    have hg : Function.Injective (X.subtype.comp (A.subgroupOf X).subtype) :=
      X.subtype_injective.comp (A.subgroupOf X).subtype_injective
    have hmap : f.ker.map (X.subtype.comp (A.subgroupOf X).subtype) = A ⊓ R := by
      ext y
      constructor
      · rintro ⟨x, hx, rfl⟩
        exact ⟨x.2, (c.ker x.1).mp hx⟩
      · rintro ⟨hyA, hyR⟩
        exact ⟨⟨⟨y, hAX hyA⟩, hyA⟩, (c.ker _).mpr hyR, rfl⟩
    rw [← hmap, Subgroup.card_map_of_injective hg]
  rw [card_subgroupOf_eq, inf_eq_left.mpr hAX, hrange, hker] at h1
  exact h1

theorem vecOf_le_fixSubOf {A : Subgroup G} (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) :
    c.vecOf A ≤ fixSubOf (c.img A) := by
  intro v hv
  obtain ⟨r, hrA, rfl⟩ := c.mem_vecOf.mp hv
  rw [mem_fixSubOf]
  intro g hg
  obtain ⟨a, haA, rfl⟩ := c.mem_img.mp hg
  rw [mem_fixSub]
  have h := c.equiv a r r (by rw [hAab _ haA _ hrA, Subgroup.coe_inv, mul_inv_cancel_right])
  exact h.symm

@[expose] def conjR (g : ↥X) (r : ↥R) : ↥R := ⟨(g : G) * r * (g : G)⁻¹, c.conj_mem r.2⟩

theorem toAdd_ψ_conjR (g : ↥X) (r : ↥R) :
    Multiplicative.toAdd (c.ψ (c.conjR g r)) =
      ((c.φ g : SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *ᵥ
        Multiplicative.toAdd (c.ψ r) :=
  c.equiv g r _ (by simp [conjR])

omit [Group G] in
theorem sylow_isSylowTwoOf_top {Y : Type} [Group Y] [Finite Y] (P : Sylow 2 Y) :
    IsSylowTwoOf (P : Subgroup Y) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [show ((P : Subgroup Y).subgroupOf ⊤).index = (P : Subgroup Y).index from
    Subgroup.relIndex_top_right _]
  exact P.not_dvd_index

@[expose] def conj (g : SpecialLinearGroup (Fin 3) F) : SL3Data X R F where
  φ := (MulAut.conj g).toMonoidHom.comp c.φ
  surj := (MulAut.conj g).surjective.comp c.surj
  le := c.le
  ker x := by
    rw [← c.ker x]
    simp
  ψ := (mulVecHom g).comp c.ψ
  ψsurj v := by
    obtain ⟨r, hr⟩ := c.ψsurj (mulVecHom g⁻¹ v)
    exact ⟨r, by rw [MonoidHom.comp_apply, hr, mulVecHom_apply_inv]⟩
  equiv x r r' h := by
    simp only [MonoidHom.comp_apply, toAdd_mulVecHom, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
      Matrix.SpecialLinearGroup.coe_mul]
    rw [c.equiv x r r' h, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mul_assoc,
      Matrix.mul_assoc, ← Matrix.SpecialLinearGroup.coe_mul g⁻¹ g, inv_mul_cancel,
      Matrix.SpecialLinearGroup.coe_one, Matrix.mul_one]

theorem conj_ψ (g : SpecialLinearGroup (Fin 3) F) (r : ↥R) :
    (c.conj g).ψ r = mulVecHom g (c.ψ r) := rfl

theorem conj_ψ_eq_one_iff (g : SpecialLinearGroup (Fin 3) F) (r : ↥R) :
    (c.conj g).ψ r = 1 ↔ c.ψ r = 1 := by
  rw [conj_ψ]
  constructor
  · intro h
    have := congrArg (mulVecHom g⁻¹) h
    rwa [mulVecHom_inv_apply, map_one] at this
  · intro h
    rw [h, map_one]

theorem conj_ψ_injective (hinj : Function.Injective c.ψ) (g : SpecialLinearGroup (Fin 3) F) :
    Function.Injective (c.conj g).ψ := by
  intro r r' h
  apply hinj
  have := congrArg (mulVecHom g⁻¹) h
  simpa only [conj_ψ, mulVecHom_inv_apply] using this

theorem img_conj (g : SpecialLinearGroup (Fin 3) F) (A : Subgroup G) :
    (c.conj g).img A = (c.img A).map (MulAut.conj g).toMonoidHom := by
  rw [img, img, Subgroup.map_map]
  rfl

theorem exists_conj_eq_perfectCore_Q30 [Finite F] [CharP F 2]
    (hK4 : ∃ s : Finset F, s.card = 4) {K : Subgroup G}
    {P : Subgroup (SpecialLinearGroup (Fin 3) F)} (hP : CFSG.Quasithin.IsMaxParabolic2 ⊤ P)
    (hKP : c.img K = perfectCore P) {z : ↥R} (hzK : ∀ k ∈ K, k * (z : G) * k⁻¹ = z)
    (hz : c.ψ z ≠ 1) :
    ∃ g : SpecialLinearGroup (Fin 3) F, (c.conj g).img K = perfectCore (Q3 F 0) := by
  obtain ⟨-, S, hS, hN⟩ := hP.1
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf hS
    (CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := F) (n := 3) (by norm_num))
  have hP' := Vol2Native.A312L.isMaxParabolic2_top_map_equiv (MulAut.conj g) hP
  have hB : upperTriangular 3 F ≤ P.map (MulAut.conj g).toMonoidHom := by
    rw [← normalizer_unitriangular, ← hg, Vol2Native.A312L.normalizer_map_mulEquiv]
    exact Subgroup.map_mono fun x hx => hN ⟨Subgroup.mem_top x, hx⟩
  have himg : (c.conj g).img K = perfectCore (P.map (MulAut.conj g).toMonoidHom) := by
    rw [c.img_conj, hKP, CFSG.Quasithin.map_perfectCore]
  rcases eq_Q3_of_isMaxParabolic2 hP' hB with h0 | h1
  · exact ⟨g, himg.trans (by rw [h0])⟩
  · exfalso
    apply hz
    have hfix : ∀ x ∈ perfectCore (Q3 F 1), (c.conj g).ψ z ∈ fixSub x := by
      intro x hx
      rw [← h1, ← himg] at hx
      obtain ⟨k, hkK, rfl⟩ := (c.conj g).mem_img.mp hx
      rw [mem_fixSub]
      exact ((c.conj g).equiv k z z (hzK _ hkK).symm).symm
    have h2 := eq_one_of_fixed_perfectCore_Q31 hK4 _ hfix
    rw [conj_ψ] at h2
    have h3 := congrArg (mulVecHom g⁻¹) h2
    rwa [mulVecHom_inv_apply, map_one] at h3

theorem eq_one_of_perfectCore_Q30 [Finite G] [Finite F] [CharP F 2]
    (hK4 : ∃ s : Finset F, s.card = 4) {K R₀ : Subgroup G}
    (hK : c.img K = perfectCore (Q3 F 0)) (hR₀R : R₀ ≤ R)
    (hcomm : ∀ k ∈ K, ∀ r ∈ R, k * r * k⁻¹ * r⁻¹ ∈ R₀) (hR₀ : Nat.card R₀ ≤ Nat.card F ^ 3)
    {r : ↥R} (hr : (r : G) ∈ R₀) (h1 : c.ψ r = 1) : (r : G) = 1 := by
  have hS : c.vecOf R₀ = ⊤ := by
    refine eq_top_of_perfectCore_Q30 hK4 _ fun g hg x => ?_
    rw [← hK] at hg
    obtain ⟨k, hkK, rfl⟩ := c.mem_img.mp hg
    obtain ⟨r', rfl⟩ := c.ψsurj x
    have e1 : Multiplicative.ofAdd (((c.φ k : SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) *ᵥ Multiplicative.toAdd (c.ψ r')) = c.ψ (c.conjR k r') := by
      rw [← c.toAdd_ψ_conjR, ofAdd_toAdd]
    rw [e1, ← map_inv, ← map_mul]
    refine c.mem_vecOf.mpr ⟨_, ?_, rfl⟩
    simp only [conjR, Subgroup.coe_mul, Subgroup.coe_inv]
    exact hcomm _ hkK _ r'.2
  set f := c.ψ.comp (R₀.subgroupOf R).subtype with hf
  have hfs : Function.Surjective f := by
    intro v
    have hv : v ∈ c.vecOf R₀ := hS ▸ Subgroup.mem_top v
    obtain ⟨r', hr', rfl⟩ := c.mem_vecOf.mp hv
    exact ⟨⟨r', hr'⟩, rfl⟩
  have hcard : Nat.card ↥(R₀.subgroupOf R) ≤ Nat.card (Multiplicative (Fin 3 → F)) := by
    rw [card_subgroupOf_eq, inf_eq_left.mpr hR₀R, Nat.card_congr Multiplicative.toAdd,
      Nat.card_fun, Nat.card_fin]
    exact hR₀
  have hfi := (hfs.bijective_of_nat_card_le hcard).1
  have h2 : f ⟨r, hr⟩ = f 1 := by rw [map_one]; exact h1
  have h3 := congrArg (fun s : ↥(R₀.subgroupOf R) => ((s : ↥R) : G)) (hfi h2)
  simpa using h3

theorem exists_conj_img_eq_unitriangular [Finite G] [Finite F] [CharP F 2] {S : Subgroup G}
    (hSX : S ≤ X) (hS2 : IsPGroup 2 S) (hcard : Nat.card F ^ 3 * Nat.card ↥(S ⊓ R) ≤ Nat.card S) :
    ∃ g : SpecialLinearGroup (Fin 3) F, (c.conj g).img S = unitriangular 3 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS2' : IsPGroup 2 ↥(S.subgroupOf X) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSX).symm
  have himg2 : IsPGroup 2 ↥(c.img S) := hS2'.map c.φ
  obtain ⟨Q, hQ⟩ := himg2.exists_le_sylow
  obtain ⟨g, hg⟩ := Vol2Native.A312L.exists_conj_of_isSylowTwoOf
    (sylow_isSylowTwoOf_top Q)
    (CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := F) (n := 3) (by norm_num))
  refine ⟨g, ?_⟩
  have hle : (c.conj g).img S ≤ unitriangular 3 F := by
    rw [c.img_conj, ← hg]
    exact Subgroup.map_mono hQ
  refine Subgroup.eq_of_le_of_card_ge hle ?_
  have h1 := c.card_eq_mul hSX
  have h2 : Nat.card ((c.conj g).img S) = Nat.card (c.img S) := by
    rw [c.img_conj, Subgroup.card_map_of_injective (MulAut.conj g).injective]
  have hpos : 0 < Nat.card ↥(S ⊓ R) := Nat.card_pos
  rw [card_unitriangular, h2, show 3 * (3 - 1) / 2 = 3 from rfl]
  have : Nat.card F ^ 3 * Nat.card ↥(S ⊓ R) ≤ Nat.card (c.img S) * Nat.card ↥(S ⊓ R) :=
    hcard.trans h1.le
  exact Nat.le_of_mul_le_mul_right this hpos

end SL3Data

structure SL3Cfg (X R : Subgroup G) (F : Type) [Field F] extends SL3Data X R F where
  ψinj : Function.Injective ψ

namespace SL3Cfg

variable {X R : Subgroup G} (c : SL3Cfg X R F)

theorem card_vecOf (A : Subgroup G) : Nat.card (c.vecOf A) = Nat.card ↥(A ⊓ R) := by
  rw [SL3Data.vecOf, Subgroup.card_map_of_injective c.ψinj, card_subgroupOf_eq]

include c in
theorem card_R [Finite F] : Nat.card ↥R = Nat.card F ^ 3 := by
  rw [Nat.card_congr (Equiv.ofBijective c.ψ ⟨c.ψinj, c.ψsurj⟩),
    Nat.card_congr (Multiplicative.toAdd (α := Fin 3 → F)), Nat.card_fun, Nat.card_fin]

theorem eq_U2_of_elemAbelian [Finite G] [Finite F] [CharP F 2] {A : Subgroup G} (hAX : A ≤ X)
    (hA2 : ∀ a ∈ A, a * a = 1) (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hcard : Nat.card F ^ 4 ≤ Nat.card A) (hAU : c.img A ≤ unitriangular 3 F) :
    c.img A = U2 ∧ c.vecOf A = wSub := by
  have hq : 2 ≤ Nat.card F := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact Fintype.one_lt_card
  have hq0 : 0 < Nat.card F := by omega
  have hR := c.card_R
  have hmul := c.card_eq_mul hAX
  have hvec := c.card_vecOf A
  have hfix := c.vecOf_le_fixSubOf hAab
  have hAR : Nat.card ↥(A ⊓ R) ≤ Nat.card F ^ 3 := hR ▸ Subgroup.card_le_of_le inf_le_right
  have himg2 : ∀ x ∈ c.img A, x * x = 1 := by
    intro x hx
    obtain ⟨a, haA, rfl⟩ := c.mem_img.mp hx
    rw [← map_mul]
    have : a * a = 1 := Subtype.ext (hA2 _ haA)
    rw [this, map_one]
  have hne : c.img A ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot, one_mul] at hmul
    have : Nat.card F ^ 4 ≤ Nat.card F ^ 3 := hcard.trans (hmul ▸ hAR)
    have := Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card F) |>.mp this
    omega
  obtain ⟨u, hu1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
  rcases le_U1_or_le_U2 hAU himg2 with hU1 | hU2
  ·
    exfalso
    have h1 : Nat.card ↥(A ⊓ R) ≤ Nat.card F ^ 2 := by
      rw [← hvec]
      refine (Subgroup.card_le_of_le (hfix.trans ?_)).trans
        (card_fixSub_le_of_mem_U1 (hU1 u.2) (by simpa using hu1))
      intro v hv
      exact mem_fixSubOf.mp hv u u.2
    have h2 : Nat.card F ^ 2 ≤ Nat.card (c.img A) := by
      have : Nat.card F ^ 2 * Nat.card F ^ 2 ≤ Nat.card (c.img A) * Nat.card F ^ 2 := by
        rw [← pow_add]
        exact hcard.trans (hmul ▸ Nat.mul_le_mul_left _ h1)
      exact Nat.le_of_mul_le_mul_right this (by positivity)
    have heq : c.img A = U1 :=
      Subgroup.eq_of_le_of_card_ge hU1 (card_U1_le.trans h2)
    have h3 : Nat.card ↥(A ⊓ R) ≤ Nat.card F := by
      rw [← hvec]
      have h5 := Subgroup.card_le_of_le hfix
      rw [heq] at h5
      exact h5.trans card_fixSubOf_U1_le
    have h4 : Nat.card (c.img A) ≤ Nat.card F ^ 2 := heq ▸ card_U1_le
    have : Nat.card F ^ 4 ≤ Nat.card F ^ 2 * Nat.card F :=
      hcard.trans (hmul ▸ Nat.mul_le_mul h4 h3)
    rw [← pow_succ] at this
    have := Nat.pow_le_pow_iff_right (by omega : 1 < Nat.card F) |>.mp this
    omega
  · have hW : c.vecOf A ≤ wSub := hfix.trans fun v hv =>
      fixSub_le_wSub (hU2 u.2) (by simpa using hu1) (mem_fixSubOf.mp hv u u.2)
    have h1 : Nat.card ↥(A ⊓ R) ≤ Nat.card F ^ 2 := by
      rw [← hvec]
      exact (Subgroup.card_le_of_le hW).trans card_wSub_le
    have h2 : Nat.card F ^ 2 ≤ Nat.card (c.img A) := by
      have : Nat.card F ^ 2 * Nat.card F ^ 2 ≤ Nat.card (c.img A) * Nat.card F ^ 2 := by
        rw [← pow_add]
        exact hcard.trans (hmul ▸ Nat.mul_le_mul_left _ h1)
      exact Nat.le_of_mul_le_mul_right this (by positivity)
    have heq : c.img A = U2 := Subgroup.eq_of_le_of_card_ge hU2 (card_U2_le.trans h2)
    have h4 : Nat.card (c.img A) ≤ Nat.card F ^ 2 := heq ▸ card_U2_le
    have h5 : Nat.card F ^ 2 ≤ Nat.card (c.vecOf A) := by
      rw [hvec]
      have : Nat.card F ^ 2 * Nat.card F ^ 2 ≤ Nat.card F ^ 2 * Nat.card ↥(A ⊓ R) := by
        rw [← pow_add]
        exact hcard.trans (hmul ▸ Nat.mul_le_mul_right _ h4)
      exact Nat.le_of_mul_le_mul_left this (by positivity)
    exact ⟨heq, Subgroup.eq_of_le_of_card_ge hW (card_wSub_le.trans h5)⟩

theorem le_of_eq_U2 [Finite F] {A A' : Subgroup G} (hA'X : A' ≤ X)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA'ab : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a)
    (hA : c.img A = U2 ∧ c.vecOf A = wSub) (hA' : c.img A' = U2 ∧ c.vecOf A' = wSub) :
    A' ≤ A := by
  intro a' ha'
  set x' : ↥X := ⟨a', hA'X ha'⟩ with hx'
  have hu : c.φ x' ∈ U2 := hA'.1 ▸ c.mem_img.mpr ⟨x', ha', rfl⟩
  obtain ⟨x, hxA, hx⟩ := c.mem_img.mp (hA.1.symm ▸ hu : c.φ x' ∈ c.img A)
  have hr : ((x⁻¹ * x' : ↥X) : G) ∈ R :=
    (c.ker _).mp (by rw [map_mul, map_inv, hx, inv_mul_cancel])
  set r : ↥R := ⟨_, hr⟩ with hrdef
  suffices key : Multiplicative.toAdd (c.ψ r) 2 = 0 by
    have hmem : c.ψ r ∈ c.vecOf A := hA.2 ▸ key
    obtain ⟨r', hr'A, hr'⟩ := c.mem_vecOf.mp hmem
    have hrr : r' = r := c.ψinj hr'
    have hrA : (r : G) ∈ A := hrr ▸ hr'A
    have : a' = (x : G) * (r : G) := by simp [hrdef, hx']
    rw [this]
    exact A.mul_mem hxA hrA
  by_cases hu1 : c.φ x' = 1
  ·
    have hx1 : c.φ x = 1 := hx.trans hu1
    have hxR : (x : G) ∈ R := (c.ker x).mp hx1
    have hx'R : (x' : G) ∈ R := (c.ker x').mp hu1
    have h1 : c.ψ ⟨x, hxR⟩ ∈ c.vecOf A := c.mem_vecOf.mpr ⟨⟨x, hxR⟩, hxA, rfl⟩
    have h2 : c.ψ ⟨x', hx'R⟩ ∈ c.vecOf A' := c.mem_vecOf.mpr ⟨⟨x', hx'R⟩, ha', rfl⟩
    rw [hA.2] at h1
    rw [hA'.2] at h2
    have hrprod : r = (⟨x, hxR⟩ : ↥R)⁻¹ * ⟨x', hx'R⟩ := Subtype.ext (by simp [hrdef])
    rw [hrprod, map_mul, map_inv]
    exact (wSub (F := F)).mul_mem ((wSub (F := F)).inv_mem h1) h2
  ·
    set u := c.φ x' with hudef
    have hne := U2_ne_one hu hu1
    obtain ⟨w, hwU, hw⟩ : ∃ w : SpecialLinearGroup (Fin 3) F, w ∈ U2 ∧
        ((u : Matrix (Fin 3) (Fin 3) F) 0 2 ≠ 0 →
          (w : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 ∧ (w : Matrix (Fin 3) (Fin 3) F) 1 2 = 1) ∧
        ((u : Matrix (Fin 3) (Fin 3) F) 0 2 = 0 →
          (w : Matrix (Fin 3) (Fin 3) F) 0 2 = 1 ∧ (w : Matrix (Fin 3) (Fin 3) F) 1 2 = 0) := by
      by_cases h02 : (u : Matrix (Fin 3) (Fin 3) F) 0 2 = 0
      · exact ⟨u2El 0 1, u2El_mem 0 1, fun h => absurd h02 h, fun _ => by simp [u2El]⟩
      · exact ⟨u2El 1 0, u2El_mem 1 0, fun _ => by simp [u2El], fun h => absurd h h02⟩
    obtain ⟨y', hy'A, hy'⟩ := c.mem_img.mp (hA'.1.symm ▸ hwU : w ∈ c.img A')
    obtain ⟨y, hyA, hy⟩ := c.mem_img.mp (hA.1.symm ▸ hwU : w ∈ c.img A)
    have hs : ((y⁻¹ * y' : ↥X) : G) ∈ R :=
      (c.ker _).mp (by rw [map_mul, map_inv, hy, hy', inv_mul_cancel])
    set s : ↥R := ⟨_, hs⟩ with hsdef
    have hcomm' : (x' : G) * y' = y' * x' := hA'ab _ ha' _ hy'A
    have hcomm : (x : G) * y = y * x := hAab _ hxA _ hyA
    have hid : c.conjR x r * c.conjR (x * y) s = c.conjR y s * c.conjR (x * y) r := by
      apply Subtype.ext
      simp only [SL3Data.conjR, Subgroup.coe_mul, hrdef, hsdef, Subgroup.coe_inv,
        _root_.mul_inv_rev]
      have e1 : (x : G) * ((x : G)⁻¹ * x') * (x : G)⁻¹ * ((x : G) * y * ((y : G)⁻¹ * y') *
          ((y : G)⁻¹ * (x : G)⁻¹)) = (x' : G) * y' * (y : G)⁻¹ * (x : G)⁻¹ := by group
      have e2 : (y : G) * ((y : G)⁻¹ * y') * (y : G)⁻¹ * ((x : G) * y * ((x : G)⁻¹ * x') *
          ((y : G)⁻¹ * (x : G)⁻¹)) = (y' : G) * (y : G)⁻¹ * ((x : G) * y) * (x : G)⁻¹ * x' *
            (y : G)⁻¹ * (x : G)⁻¹ := by group
      rw [e1, e2, hcomm]
      calc (x' : G) * y' * (y : G)⁻¹ * (x : G)⁻¹ = y' * x' * (y : G)⁻¹ * (x : G)⁻¹ := by
            rw [hcomm']
        _ = (y' : G) * (y : G)⁻¹ * ((y : G) * x) * (x : G)⁻¹ * x' * (y : G)⁻¹ * (x : G)⁻¹ := by
            group
    have hψ := congrArg (fun v => Multiplicative.toAdd (c.ψ v)) hid
    simp only [map_mul, toAdd_mul, SL3Data.toAdd_ψ_conjR, map_mul c.φ, hx, hy] at hψ
    have huw : u * w ∈ U2 := U2.mul_mem hu hwU
    have e0 := congrFun hψ 0
    have e1 := congrFun hψ 1
    rw [Matrix.SpecialLinearGroup.coe_mul] at e0 e1
    simp only [Pi.add_apply] at e0 e1
    rw [← Matrix.SpecialLinearGroup.coe_mul, mulVec_of_mem_U2 hu, mulVec_of_mem_U2 huw,
      mulVec_of_mem_U2 hwU, mulVec_of_mem_U2 huw] at e0 e1
    obtain ⟨m02, m12⟩ := mul_apply_U2 hu hwU
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, m02, m12] at e0 e1
    have k0 : (u : Matrix (Fin 3) (Fin 3) F) 0 2 * Multiplicative.toAdd (c.ψ s) 2 =
        (w : Matrix (Fin 3) (Fin 3) F) 0 2 * Multiplicative.toAdd (c.ψ r) 2 := by
      linear_combination e0
    have k1 : (u : Matrix (Fin 3) (Fin 3) F) 1 2 * Multiplicative.toAdd (c.ψ s) 2 =
        (w : Matrix (Fin 3) (Fin 3) F) 1 2 * Multiplicative.toAdd (c.ψ r) 2 := by
      linear_combination e1
    by_cases h02 : (u : Matrix (Fin 3) (Fin 3) F) 0 2 = 0
    · obtain ⟨w02, w12⟩ := hw.2 h02
      have hu12 : (u : Matrix (Fin 3) (Fin 3) F) 1 2 ≠ 0 := hne.resolve_left (not_not.mpr h02)
      rw [w12, zero_mul] at k1
      have hs2 : Multiplicative.toAdd (c.ψ s) 2 = 0 :=
        (mul_eq_zero.mp k1).resolve_left hu12
      rw [h02, w02, zero_mul, one_mul] at k0
      exact k0.symm
    · obtain ⟨w02, w12⟩ := hw.1 h02
      rw [w02, zero_mul] at k0
      have hs2 : Multiplicative.toAdd (c.ψ s) 2 = 0 := (mul_eq_zero.mp k0).resolve_left h02
      rw [hs2, mul_zero, w12, one_mul] at k1
      exact k1.symm

theorem conj_mem_of_mem_Q31 [Finite F] {A : Subgroup G} (hAX : A ≤ X)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA : c.img A = U2 ∧ c.vecOf A = wSub) {x : ↥X}
    (hx : c.φ x ∈ Q3 F 1) {a : G} (ha : a ∈ A) : (x : G) * a * (x : G)⁻¹ ∈ A := by
  set A' := A.map (MulAut.conj (x : G)).toMonoidHom with hA'def
  have hmemA' : ∀ b : G, b ∈ A' ↔ ∃ a ∈ A, (x : G) * a * (x : G)⁻¹ = b := by
    intro b
    simp [hA'def, MulAut.conj_apply]
  have hA'X : A' ≤ X := by
    intro b hb
    obtain ⟨a, ha, rfl⟩ := (hmemA' b).mp hb
    exact X.mul_mem (X.mul_mem x.2 (hAX ha)) (X.inv_mem x.2)
  have hA'ab : ∀ a ∈ A', ∀ b ∈ A', a * b = b * a := by
    intro a₁ h₁ b₁ h₂
    obtain ⟨a, ha, rfl⟩ := (hmemA' a₁).mp h₁
    obtain ⟨b, hb, rfl⟩ := (hmemA' b₁).mp h₂
    calc (x : G) * a * (x : G)⁻¹ * ((x : G) * b * (x : G)⁻¹) = (x : G) * (a * b) * (x : G)⁻¹ := by
          group
      _ = (x : G) * (b * a) * (x : G)⁻¹ := by rw [hAab a ha b hb]
      _ = (x : G) * b * (x : G)⁻¹ * ((x : G) * a * (x : G)⁻¹) := by group
  have hxi : c.φ x⁻¹ ∈ Q3 F 1 := by rw [map_inv]; exact (Q3 F 1).inv_mem hx
  have himg : c.img A' = U2 := by
    apply le_antisymm
    · intro g hg
      obtain ⟨b, hbA', rfl⟩ := c.mem_img.mp hg
      obtain ⟨a, ha, hab⟩ := (hmemA' b).mp hbA'
      have hb : b = x * ⟨a, hAX ha⟩ * x⁻¹ := Subtype.ext (by simp [← hab])
      rw [hb, map_mul, map_mul, map_inv]
      exact U2_normal hx (hA.1 ▸ c.mem_img.mpr ⟨⟨a, hAX ha⟩, ha, rfl⟩)
    · intro u hu
      have hu' : (c.φ x)⁻¹ * u * (c.φ x)⁻¹⁻¹ ∈ c.img A := by
        rw [hA.1]
        exact U2_normal ((Q3 F 1).inv_mem hx) hu
      obtain ⟨a, ha, hau⟩ := c.mem_img.mp hu'
      refine c.mem_img.mpr ⟨x * a * x⁻¹, (hmemA' _).mpr ⟨a, ha, by simp⟩, ?_⟩
      rw [map_mul, map_mul, hau, map_inv]
      group
  have hvec : c.vecOf A' = wSub := by
    apply le_antisymm
    · intro v hv
      obtain ⟨r, hrA', rfl⟩ := c.mem_vecOf.mp hv
      obtain ⟨a, ha, hra⟩ := (hmemA' r).mp hrA'
      have haR : a ∈ R := by
        have h1 := c.conj_mem (g := x⁻¹) r.2
        rw [← hra] at h1
        simpa [mul_assoc] using h1
      have hr : r = c.conjR x ⟨a, haR⟩ := Subtype.ext (by simp [SL3Data.conjR, hra])
      have hw : c.ψ ⟨a, haR⟩ ∈ wSub := hA.2 ▸ c.mem_vecOf.mpr ⟨⟨a, haR⟩, ha, rfl⟩
      show Multiplicative.toAdd (c.ψ r) 2 = 0
      rw [hr, SL3Data.toAdd_ψ_conjR]
      exact mulVec_two_eq_zero_of_mem_Q31 hx hw
    · intro w hw
      have hw' : mulVecHom (c.φ x)⁻¹ w ∈ c.vecOf A := by
        rw [hA.2]
        exact mulVec_two_eq_zero_of_mem_Q31 ((Q3 F 1).inv_mem hx) hw
      obtain ⟨r, hrA, hr⟩ := c.mem_vecOf.mp hw'
      refine c.mem_vecOf.mpr ⟨c.conjR x r, (hmemA' _).mpr ⟨r, hrA, rfl⟩, ?_⟩
      apply Multiplicative.toAdd.injective
      rw [SL3Data.toAdd_ψ_conjR, hr, toAdd_mulVecHom, Matrix.mulVec_mulVec,
        ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel, Matrix.SpecialLinearGroup.coe_one,
        Matrix.one_mulVec]
  exact c.le_of_eq_U2 hA'X hAab hA'ab hA ⟨himg, hvec⟩ ((hmemA' _).mpr ⟨a, ha, rfl⟩)

theorem mem_normalizer_of_mem_Q31 [Finite F] {A : Subgroup G} (hAX : A ≤ X)
    (hAab : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA : c.img A = U2 ∧ c.vecOf A = wSub) {x : ↥X}
    (hx : c.φ x ∈ Q3 F 1) : (x : G) ∈ Subgroup.normalizer (A : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro a
  refine ⟨fun ha => c.conj_mem_of_mem_Q31 hAX hAab hA hx ha, fun ha => ?_⟩
  have hxi : c.φ x⁻¹ ∈ Q3 F 1 := by rw [map_inv]; exact (Q3 F 1).inv_mem hx
  have := c.conj_mem_of_mem_Q31 hAX hAab hA hxi ha
  simpa [mul_assoc] using this

theorem exists_isSylowTwoOf_mem [Finite G] {H : Subgroup G} {x : G} (hx : x ∈ H) {k : ℕ}
    (hk : x ^ 2 ^ k = 1) : ∃ S : Subgroup G, IsSylowTwoOf S H ∧ x ∈ S := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set x₁ : ↥H := ⟨x, hx⟩
  have hZ : IsPGroup 2 ↥(Subgroup.zpowers x₁) := by
    rintro ⟨z, hz⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine ⟨k, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, SubgroupClass.coe_zpow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← _root_.zpow_mul, mul_comm, _root_.zpow_mul, zpow_natCast, hk,
      _root_.one_zpow]
  obtain ⟨P, hP⟩ := hZ.exists_le_sylow
  refine ⟨(P : Subgroup ↥H).map H.subtype, ⟨Subgroup.map_subtype_le _, P.isPGroup'.map _, ?_⟩,
    ⟨x₁, hP (Subgroup.mem_zpowers x₁), rfl⟩⟩
  rw [show ((P : Subgroup ↥H).map H.subtype).subgroupOf H = P from
    Subgroup.comap_map_eq_self_of_injective H.subtype_injective _]
  exact P.not_dvd_index

theorem mem_of_mul_self_eq_one [Finite G] [Finite F] [CharP F 2] {S L : Subgroup G}
    (hSX : S ≤ X) (hS : c.img S = unitriangular 3 F) (hRS : R ≤ S) (hSL : S ≤ L)
    (hR2 : IsPGroup 2 R)
    (hN : ∀ x : ↥X, c.φ x ∈ Q3 F 1 → (x : G) ∈ Subgroup.normalizer (L : Set G)) {x : ↥X}
    (hx : c.φ x ∈ Q3 F 1) (hx2 : c.φ x * c.φ x = 1) : (x : G) ∈ L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K₁ : Subgroup G := ((Q3 F 1).comap c.φ).map X.subtype with hK₁
  have hmemK₁ : ∀ y : G, y ∈ K₁ ↔ ∃ h : y ∈ X, c.φ ⟨y, h⟩ ∈ Q3 F 1 := by
    intro y
    simp [hK₁]
  have hK₁X : K₁ ≤ X := Subgroup.map_subtype_le _
  have hSK₁ : S ≤ K₁ := fun s hs => (hmemK₁ s).mpr ⟨hSX hs, unitriangular_le_Q3 1
    (hS ▸ c.mem_img.mpr ⟨⟨s, hSX hs⟩, hs, rfl⟩)⟩
  have hRK₁ : R ≤ K₁ := fun r hr => (hmemK₁ r).mpr ⟨c.le hr, by
    rw [(c.ker ⟨r, c.le hr⟩).mpr hr]; exact (Q3 F 1).one_mem⟩
  have himgK₁ : c.img K₁ = Q3 F 1 := by
    apply le_antisymm
    · intro g hg
      obtain ⟨y, hyK₁, rfl⟩ := c.mem_img.mp hg
      obtain ⟨_, hy⟩ := (hmemK₁ y).mp hyK₁
      exact hy
    · intro g hg
      obtain ⟨y, rfl⟩ := c.surj g
      exact c.mem_img.mpr ⟨y, (hmemK₁ y).mpr ⟨y.2, hg⟩, rfl⟩
  have hcK₁ := c.card_eq_mul hK₁X
  have hcS := c.card_eq_mul hSX
  rw [himgK₁, inf_eq_right.mpr hRK₁] at hcK₁
  rw [hS, inf_eq_right.mpr hRS] at hcS
  have hS2 : IsPGroup 2 S := by
    rintro ⟨s, hs⟩
    obtain ⟨k, hk⟩ := (CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := F) (n := 3)
      (by norm_num)).2.1 ⟨c.φ ⟨s, hSX hs⟩, hS ▸ c.mem_img.mpr ⟨⟨s, hSX hs⟩, hs, rfl⟩⟩
    have hk' : c.φ ⟨s, hSX hs⟩ ^ 2 ^ k = 1 := congrArg Subtype.val hk
    rw [← map_pow] at hk'
    have hsR : (s : G) ^ 2 ^ k ∈ R := by
      have := (c.ker _).mp hk'
      simpa using this
    obtain ⟨j, hj⟩ := hR2 ⟨_, hsR⟩
    refine ⟨k + j, Subtype.ext ?_⟩
    have hj' : ((s : G) ^ 2 ^ k) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [pow_add, pow_mul, hj']
  have hidx : ¬ 2 ∣ (S.subgroupOf K₁).index := by
    have hU := (CFSG.Quasithin.SzN2.isSylowTwoOf_unitriangular (K := F) (n := 3)
      (by norm_num)).2.2
    have hUQ : unitriangular 3 F ≤ Q3 F 1 := unitriangular_le_Q3 1
    have h1 := Subgroup.relIndex_mul_relIndex (unitriangular 3 F) (Q3 F 1) ⊤ hUQ le_top
    have h2 : (unitriangular 3 F).relIndex (Q3 F 1) * Nat.card (unitriangular 3 F) =
        Nat.card (Q3 F 1) := by
      have := Subgroup.relIndex_mul_card (unitriangular 3 F) (Q3 F 1)
      rwa [inf_eq_left.mpr hUQ] at this
    have h3 : S.relIndex K₁ * Nat.card S = Nat.card K₁ := by
      have := Subgroup.relIndex_mul_card S K₁
      rwa [inf_eq_left.mpr hSK₁] at this
    have hpos : 0 < Nat.card (unitriangular 3 F) * Nat.card ↥R :=
      Nat.mul_pos Nat.card_pos Nat.card_pos
    have h4 : S.relIndex K₁ = (unitriangular 3 F).relIndex (Q3 F 1) := by
      refine Nat.eq_of_mul_eq_mul_right hpos ?_
      calc S.relIndex K₁ * (Nat.card (unitriangular 3 F) * Nat.card ↥R)
          = S.relIndex K₁ * Nat.card S := by rw [hcS]
        _ = Nat.card K₁ := h3
        _ = Nat.card (Q3 F 1) * Nat.card ↥R := hcK₁
        _ = (unitriangular 3 F).relIndex (Q3 F 1) * Nat.card (unitriangular 3 F) *
            Nat.card ↥R := by rw [← h2]
        _ = (unitriangular 3 F).relIndex (Q3 F 1) *
            (Nat.card (unitriangular 3 F) * Nat.card ↥R) := mul_assoc _ _ _
    show ¬ 2 ∣ S.relIndex K₁
    rw [h4]
    intro hdvd
    apply hU
    show 2 ∣ (unitriangular 3 F).relIndex ⊤
    rw [← h1]
    exact Dvd.dvd.mul_right hdvd _
  have hSyl : IsSylowTwoOf S K₁ := ⟨hSK₁, hS2, hidx⟩
  have hxK₁ : (x : G) ∈ K₁ := (hmemK₁ x).mpr ⟨x.2, hx⟩
  have hxR : ((x : G) ^ 2) ∈ R := by
    have : c.φ (x ^ 2) = 1 := by rw [map_pow, sq, hx2]
    have := (c.ker _).mp this
    simpa using this
  obtain ⟨j, hj⟩ := hR2 ⟨_, hxR⟩
  have hx2k : (x : G) ^ 2 ^ (j + 1) = 1 := by
    have hj' : ((x : G) ^ 2) ^ 2 ^ j = 1 := congrArg Subtype.val hj
    rw [pow_succ', pow_mul, hj']
  obtain ⟨S', hS', hxS'⟩ := exists_isSylowTwoOf_mem hxK₁ hx2k
  obtain ⟨k, hk, hS'eq⟩ := hSyl.exists_conj hS'
  rw [hS'eq] at hxS'
  obtain ⟨s, hs, hsx⟩ := hxS'
  have hkN := hN ⟨k, hK₁X hk⟩ ((hmemK₁ k).mp hk).2
  rw [← hsx]
  exact (Subgroup.mem_normalizer_iff.mp hkN s).mp (hSL hs)

theorem exists_mem_dMat [CharP F 2] {L : Subgroup G}
    (hL : ∀ x : ↥X, c.φ x ∈ Q3 F 1 → c.φ x * c.φ x = 1 → (x : G) ∈ L) (μ : Fˣ) :
    ∃ y : ↥X, (y : G) ∈ L ∧ c.φ y = dMat μ := by
  have hle : Subgroup.closure {x : SpecialLinearGroup (Fin 3) F | x ∈ Q3 F 1 ∧ x * x = 1} ≤
      (L.subgroupOf X).map c.φ := by
    rw [Subgroup.closure_le]
    rintro g ⟨hgQ, hg2⟩
    obtain ⟨x, rfl⟩ := c.surj g
    exact ⟨x, hL x hgQ hg2, rfl⟩
  obtain ⟨y, hyL, hy⟩ := hle (dMat_mem_closure μ)
  exact ⟨y, hyL, hy⟩

theorem eq_one_of_conj_dMat {A : Subgroup G} (hAX : A ≤ X) (hAU : c.img A ≤ U2)
    (hAW : c.vecOf A ≤ wSub) {y : ↥X} {μ : Fˣ} (hμ : μ ≠ 1) (hy : c.φ y = dMat μ) {a : G}
    (ha : a ∈ A) (hya : (y : G) * a * (y : G)⁻¹ = a) : a = 1 := by
  set x : ↥X := ⟨a, hAX ha⟩ with hx
  have hxU : c.φ x ∈ U2 := hAU (c.mem_img.mpr ⟨x, ha, rfl⟩)
  have hyx : y * x * y⁻¹ = x := Subtype.ext (by simpa [hx] using hya)
  have hyx' : y * x = x * y := by
    calc y * x = (y * x * y⁻¹) * y := by group
      _ = x * y := by rw [hyx]
  have hcomm : dMat μ * c.φ x = c.φ x * dMat μ := by
    rw [← hy, ← map_mul, ← map_mul, hyx']
  have h1 : c.φ x = 1 := eq_one_of_dMat_conj hμ hxU hcomm
  have haR : a ∈ R := (c.ker x).mp h1
  have hvec : c.ψ ⟨a, haR⟩ ∈ c.vecOf A := c.mem_vecOf.mpr ⟨⟨a, haR⟩, ha, rfl⟩
  have hfix : c.ψ ⟨a, haR⟩ ∈ fixSub (dMat μ) := by
    rw [mem_fixSub, ← hy]
    exact (c.equiv y ⟨a, haR⟩ ⟨a, haR⟩ hya.symm).symm
  have := fixSub_dMat_inf_wSub hμ _ hfix (hAW hvec)
  have h2 : (⟨a, haR⟩ : ↥R) = 1 := c.ψinj (by rw [this, map_one])
  exact congrArg Subtype.val h2

theorem false_of_fixed [Finite G] [Finite F] [CharP F 2] (hK4 : ∃ s : Finset F, s.card = 4)
    {U S L : Subgroup G} (hUX : U ≤ X) (hU2 : ∀ a ∈ U, a * a = 1)
    (hUab : ∀ a ∈ U, ∀ b ∈ U, a * b = b * a) (hUcard : Nat.card F ^ 4 ≤ Nat.card U)
    (hUS : U ≤ S) (hSX : S ≤ X) (hS : c.img S = unitriangular 3 F) (hRS : R ≤ S) (hSL : S ≤ L)
    (hR2 : IsPGroup 2 R)
    (hNL : Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hfix : ∀ y ∈ L, y ^ (Nat.card F - 1) = 1 → ∃ u ∈ U, u ≠ 1 ∧ y * u * y⁻¹ = u) : False := by
  classical
  have := Fintype.ofFinite F
  have hUW := c.eq_U2_of_elemAbelian hUX hU2 hUab hUcard ((c.img_mono hUS).trans hS.le)
  have hN : ∀ x : ↥X, c.φ x ∈ Q3 F 1 → (x : G) ∈ Subgroup.normalizer (L : Set G) :=
    fun x hx => hNL (c.mem_normalizer_of_mem_Q31 hUX hUab hUW hx)
  have hL := fun (x : ↥X) hx hx2 => c.mem_of_mul_self_eq_one hSX hS hRS hSL hR2 hN (x := x) hx hx2
  obtain ⟨μ, hμ⟩ := exists_unit_ne_one hK4
  obtain ⟨y, hyL, hy⟩ := c.exists_mem_dMat hL μ
  have hμq : ∀ ν : Fˣ, ν ^ Nat.card F = ν := fun ν => Units.ext (by
    rw [Units.val_pow_eq_pow_val, Nat.card_eq_fintype_card, FiniteField.pow_card])
  have hμ1 : μ ^ (Nat.card F - 1) = 1 := by
    rw [Nat.card_eq_fintype_card, ← Fintype.card_units]
    exact pow_card_eq_one
  have hR : Nat.card ↥R = Nat.card F ^ 3 := c.card_R
  set y' : ↥X := y ^ Nat.card ↥R with hy'
  have hy'φ : c.φ y' = dMat μ := by
    rw [hy', map_pow, hy, ← dMat_pow, hR, pow_succ, pow_succ, pow_one, pow_mul, pow_mul, hμq, hμq,
      hμq]
  have hy'q : (y' : G) ^ (Nat.card F - 1) = 1 := by
    have h1 : c.φ (y ^ (Nat.card F - 1)) = 1 := by rw [map_pow, hy, ← dMat_pow, hμ1, dMat_one]
    have h2 := (c.ker _).mp h1
    have h3 : ((⟨_, h2⟩ : ↥R) ^ Nat.card ↥R : ↥R) = 1 := pow_card_eq_one'
    have h4 := congrArg Subtype.val h3
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one] at h4
    have h5 : (((y : G) ^ (Nat.card F - 1)) ^ Nat.card ↥R) = 1 := by
      rw [← SubgroupClass.coe_pow]
      exact h4
    rw [hy', SubgroupClass.coe_pow, ← pow_mul, mul_comm, pow_mul]
    exact h5
  have hy'L : (y' : G) ∈ L := by
    rw [hy', SubgroupClass.coe_pow]
    exact pow_mem hyL _
  obtain ⟨u, huU, hu1, hyu⟩ := hfix (y' : G) hy'L hy'q
  exact hu1 (c.eq_one_of_conj_dMat hUX hUW.1.le hUW.2.le hμ hy'φ huU hyu)

end SL3Cfg

end CFSG.Quasithin.H13.SL3E
