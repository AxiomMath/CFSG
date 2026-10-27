module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeSCFourOddDefs
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryDesc
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.TwE6R4

open CFSG.Open

private theorem ct_conj_mul {G : Type} [Group G] (φ : MulAut G) (r : G) :
    MulAut.conj (φ r) = φ * MulAut.conj r * φ⁻¹ := by
  ext g
  simp only [MulAut.mul_apply, MulAut.conj_apply, MulAut.inv_apply, map_mul, map_inv,
    MulEquiv.apply_symm_apply]

private theorem ct_conj_eq_one_mem_center {G : Type} [Group G] {g : G}
    (h : MulAut.conj g = 1) : g ∈ Subgroup.center G := by
  rw [Subgroup.mem_center_iff]
  intro x
  have h' := congrArg (fun f : MulAut G => f x) h
  simp only [MulAut.conj_apply, MulAut.one_apply] at h'
  calc x * g = g * x * g⁻¹ * g := by rw [h']
    _ = g * x := by group

private theorem ct_card_comap {G H : Type} [Group G] [Group H] (f : G →* H)
    (K : Subgroup H) :
    Nat.card ↥(K.comap f) = Nat.card ↥f.ker * Nat.card ↥(f.range ⊓ K) := by
  have hle : f.ker ≤ K.comap f := fun x hx => by
    rw [Subgroup.mem_comap, MonoidHom.mem_ker.mp hx]
    exact K.one_mem
  have hker : (f.comp (K.comap f).subtype).ker = f.ker.subgroupOf (K.comap f) := by
    rw [← MonoidHom.comap_ker f (K.comap f).subtype, Subgroup.comap_subtype]
  have hker_card : Nat.card ↥((f.comp (K.comap f).subtype).ker) = Nat.card ↥f.ker := by
    rw [hker, ← Subgroup.card_subtype (K.comap f) (f.ker.subgroupOf (K.comap f)),
      Subgroup.map_subgroupOf_eq_of_le hle]
  have hrange : (f.comp (K.comap f).subtype).range = f.range ⊓ K := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, Subgroup.map_comap_eq]
  calc Nat.card ↥(K.comap f)
      = Nat.card ↥(f.comp (K.comap f).subtype).ker *
        Nat.card ↥(f.comp (K.comap f).subtype).range :=
        (Subgroup.card_ker_mul_card_range _).symm
    _ = Nat.card ↥f.ker * Nat.card ↥(f.range ⊓ K) := by rw [hker_card, hrange]

theorem oddNotTwoLocal_of_torus {R : Type} [Group R] [Finite R] (hZR : Subgroup.center R = ⊥)
    (J : Subgroup (MulAut R))
    (hsix : ∀ S : Subgroup (MulAut R), S ≤ J → IsElemAbelian 3 S → Nat.card S = 3 ^ 4 →
      (∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧ ∀ φ ∈ S, ∀ v ∈ V, φ v ∈ V) →
      ∃ Y : Subgroup (MulAut R), S ≤ Y ∧ Y ≤ J ∧ IsElemAbelian 3 Y ∧ Nat.card Y = 3 ^ 6)
    (hidx : ∀ Y : Subgroup (MulAut R), Y ≤ J → IsElemAbelian 3 Y → Nat.card Y = 3 ^ 6 →
      3 ^ 5 ≤ Nat.card ↥(Y ⊓ (MulAut.conj : R →* MulAut R).range))
    (hcov : ∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
      ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ → Odd (Nat.card ψ.ker) →
      Nat.card ψ.ker ∣ 3 ∧
      ∀ Y : Subgroup (MulAut R), Y ≤ J → IsElemAbelian 3 Y → Nat.card Y = 3 ^ 6 →
        (∀ l₁ l₂ : L', MulAut.conj (ψ l₁) ∈ Y → MulAut.conj (ψ l₂) ∈ Y → l₁ * l₂ = l₂ * l₁) ∧
        (Y ≤ (MulAut.conj : R →* MulAut R).range ∨
          ∀ l : L', MulAut.conj (ψ l) ∈ Y → l ^ 3 = 1)) :
    GGTwE6SCFourNotTwoLocalOdd R (J : Set (MulAut R)) := by
  classical
  intro L' _ _ ψ hψ hker hperf hodd A hA hAJ hA4 hSC
  rintro ⟨V, hV0, hV2, hAV⟩
  have hZ : ψ.ker = Subgroup.center L' := BstarDesc.ker_eq_center hψ hker hZR
  let D : MulAut L' →* MulAut R := BstarDesc.descAut hψ hZ
  have hDapp : ∀ (a : MulAut L') (l : L'), D a (ψ l) = ψ (a l) :=
    fun a l => BstarDesc.descAut_apply hψ hZ a l
  have hDi : Function.Injective D := BstarDesc.descAut_injective hψ hZ hperf
  have hdesc_conj : ∀ l : L',
      D (MulAut.conj l) = (MulAut.conj : R →* MulAut R) (ψ l) := by
    intro l
    apply MulEquiv.ext
    intro r
    obtain ⟨g, rfl⟩ := hψ r
    rw [hDapp, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
  have hconjinj : Function.Injective (MulAut.conj : R →* MulAut R) := by
    rw [injective_iff_map_eq_one]
    intro r hr
    have hrZ := ct_conj_eq_one_mem_center hr
    rw [hZR] at hrZ
    exact hrZ
  have hDJ : ∀ a ∈ A, D a ∈ J := by
    intro a ha
    obtain ⟨φ, hφJ, hφ⟩ := hAJ a ha
    have h : D a = φ := MulEquiv.ext fun r => by
      obtain ⟨l, rfl⟩ := hψ r
      rw [hDapp, hφ]
    rw [h]; exact hφJ
  have hSJ : A.map D ≤ J := fun φ hφ => by
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hφ
    exact hDJ a ha
  have hSAb : IsElemAbelian 3 (A.map D) := IsElemAbelian.map hA D
  have hScard : Nat.card ↥(A.map D) = 3 ^ 4 := by
    rw [Subgroup.card_map_of_injective hDi, hA4]
  have hSV : ∃ V : Subgroup R, V ≠ ⊥ ∧ IsPGroup 2 V ∧
      ∀ φ ∈ A.map D, ∀ v ∈ V, φ v ∈ V := by
    refine ⟨V, hV0, hV2, ?_⟩
    intro φ hφ v hv
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hφ
    obtain ⟨l, rfl⟩ := hψ v
    rw [hDapp]
    exact hAV a ha l hv
  obtain ⟨Y, hSY, hYJ, hYab, hYcard⟩ := hsix (A.map D) hSJ hSAb hScard hSV
  have hinfY : 3 ^ 5 ≤ Nat.card ↥(Y ⊓ (MulAut.conj : R →* MulAut R).range) :=
    hidx Y hYJ hYab hYcard
  obtain ⟨hN, hcov'⟩ := hcov L' ψ hψ hker hperf hodd
  obtain ⟨hcomm, hcase⟩ := hcov' Y hYJ hYab hYcard
  have hDY : ∀ a ∈ A, D a ∈ Y := fun a ha =>
    hSY (Subgroup.mem_map.mpr ⟨a, ha, rfl⟩)
  let P : Subgroup L' := Y.comap ((MulAut.conj : R →* MulAut R).comp ψ)
  have hPmem : ∀ l : L', l ∈ P ↔ (MulAut.conj : R →* MulAut R) (ψ l) ∈ Y :=
    fun l => Subgroup.mem_comap
  have hPcard : Nat.card ↥P = Nat.card ↥ψ.ker *
      Nat.card ↥(Y ⊓ (MulAut.conj : R →* MulAut R).range) := by
    have h := ct_card_comap ((MulAut.conj : R →* MulAut R).comp ψ) Y
    rw [MonoidHom.ker_comp_of_injective ψ (MulAut.conj : R →* MulAut R) hconjinj,
      MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hψ, Subgroup.map_top,
      inf_comm] at h
    exact h
  have hP_lower : 3 ^ 5 * Nat.card ↥ψ.ker ≤ Nat.card ↥P := by
    rw [hPcard]
    calc 3 ^ 5 * Nat.card ↥ψ.ker = Nat.card ↥ψ.ker * 3 ^ 5 := Nat.mul_comm _ _
      _ ≤ Nat.card ↥ψ.ker *
            Nat.card ↥(Y ⊓ (MulAut.conj : R →* MulAut R).range) :=
          Nat.mul_le_mul_left _ hinfY
  have hcommP : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x := fun x hx y hy =>
    hcomm x y ((hPmem x).mp hx) ((hPmem y).mp hy)
  have hNpos : 0 < Nat.card ↥ψ.ker := Nat.card_pos
  have hmod : ∀ a ∈ A, ∀ x ∈ P, ψ (a x) = ψ x := by
    intro a ha x hx
    refine hconjinj ?_
    rw [← hDapp a x, ct_conj_mul, IsElemAbelian.comm hYab (hDY a ha) ((hPmem x).mp hx)]
    group
  let A₀ : Subgroup (MulAut L') :=
    A ⊓ (MulAut.conj : R →* MulAut R).range.comap D
  have hfixP : ∀ a ∈ A₀, ∀ x ∈ P, a x = x := by
    intro a ha x hx
    have haA : a ∈ A := ha.1
    have hDaI : D a ∈ (MulAut.conj : R →* MulAut R).range := Subgroup.mem_comap.mp ha.2
    obtain ⟨r, hr⟩ := hDaI
    obtain ⟨t, rfl⟩ := hψ r
    have hat : a = MulAut.conj t := by
      apply hDi
      rw [hdesc_conj t]
      exact hr.symm
    have htP : t ∈ P := by
      rw [hPmem]
      rw [hr]
      exact hDY a haA
    rw [hat, MulAut.conj_apply, hcommP t htP x hx, mul_assoc, mul_inv_cancel, mul_one]
  have hA0map : A₀.map D = A.map D ⊓ (MulAut.conj : R →* MulAut R).range := by
    ext φ
    constructor
    · rintro ⟨a, ha, rfl⟩
      exact ⟨Subgroup.mem_map.mpr ⟨a, ha.1, rfl⟩, Subgroup.mem_comap.mp ha.2⟩
    · rintro ⟨hφA, hφI⟩
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hφA
      exact Subgroup.mem_map.mpr ⟨a, ⟨ha, Subgroup.mem_comap.mpr hφI⟩, rfl⟩
  have hA0card : Nat.card ↥A₀ =
      Nat.card ↥(A.map D ⊓ (MulAut.conj : R →* MulAut R).range) := by
    rw [← Subgroup.card_map_of_injective hDi, hA0map]
  have hA0_le : A₀ ≤ A := inf_le_left
  have hSinf : 3 ^ 3 ≤ Nat.card ↥(A.map D ⊓ (MulAut.conj : R →* MulAut R).range) := by
    have hne : (MulAut.conj : R →* MulAut R).range.relIndex Y ≠ 0 := by
      intro h0
      have h := Subgroup.relIndex_mul_card (MulAut.conj : R →* MulAut R).range Y
      rw [h0, zero_mul, hYcard] at h
      norm_num at h
    have hrel : (MulAut.conj : R →* MulAut R).range.relIndex (A.map D) ≤
        (MulAut.conj : R →* MulAut R).range.relIndex Y :=
      Subgroup.relIndex_le_of_le_right hSY hne
    have hcardY : (MulAut.conj : R →* MulAut R).range.relIndex Y *
        Nat.card ↥((MulAut.conj : R →* MulAut R).range ⊓ Y) = 3 ^ 6 := by
      rw [Subgroup.relIndex_mul_card, hYcard]
    have hYinf : 3 ^ 5 ≤
        Nat.card ↥((MulAut.conj : R →* MulAut R).range ⊓ Y) := by
      rw [inf_comm]; exact hinfY
    have hrY : (MulAut.conj : R →* MulAut R).range.relIndex Y ≤ 3 := by
      have h : (MulAut.conj : R →* MulAut R).range.relIndex Y * 3 ^ 5 ≤
          (MulAut.conj : R →* MulAut R).range.relIndex Y *
            Nat.card ↥((MulAut.conj : R →* MulAut R).range ⊓ Y) :=
        Nat.mul_le_mul_left _ hYinf
      rw [hcardY] at h
      omega
    have hrS : (MulAut.conj : R →* MulAut R).range.relIndex (A.map D) ≤ 3 :=
      hrel.trans hrY
    have hcardS : (MulAut.conj : R →* MulAut R).range.relIndex (A.map D) *
        Nat.card ↥(A.map D ⊓ (MulAut.conj : R →* MulAut R).range) = 3 ^ 4 := by
      have h := Subgroup.relIndex_mul_card (MulAut.conj : R →* MulAut R).range (A.map D)
      rw [hScard, inf_comm] at h
      exact h
    have hpos : 0 < (MulAut.conj : R →* MulAut R).range.relIndex (A.map D) := by
      apply Nat.pos_of_ne_zero
      intro h0
      rw [h0, zero_mul] at hcardS
      exact absurd hcardS (by norm_num)
    have h27 : (MulAut.conj : R →* MulAut R).range.relIndex (A.map D) * 3 ^ 3 ≤
        (MulAut.conj : R →* MulAut R).range.relIndex (A.map D) *
          Nat.card ↥(A.map D ⊓ (MulAut.conj : R →* MulAut R).range) := by
      rw [hcardS]
      nlinarith [hrS]
    exact Nat.le_of_mul_le_mul_left h27 hpos
  let F : Subgroup L' :=
    { carrier := {x | x ∈ P ∧ ∀ a ∈ A, a x = x}
      one_mem' := ⟨P.one_mem, fun a _ => map_one a⟩
      mul_mem' := by
        rintro x y ⟨hxP, hxA⟩ ⟨hyP, hyA⟩
        exact ⟨P.mul_mem hxP hyP, fun a ha => by rw [map_mul, hxA a ha, hyA a ha]⟩
      inv_mem' := by
        rintro x ⟨hxP, hxA⟩
        exact ⟨P.inv_mem hxP, fun a ha => by rw [map_inv, hxA a ha]⟩ }
  let F₃ : Subgroup L' :=
    { carrier := {x | x ∈ F ∧ x ^ 3 = 1}
      one_mem' := ⟨F.one_mem, one_pow 3⟩
      mul_mem' := by
        rintro x y ⟨hxF, hx3⟩ ⟨hyF, hy3⟩
        refine ⟨F.mul_mem hxF hyF, ?_⟩
        have hxy : Commute x y := by
          show x * y = y * x
          exact hcommP x hxF.1 y hyF.1
        rw [Commute.mul_pow hxy, hx3, hy3, one_mul]
      inv_mem' := by
        rintro x ⟨hxF, hx3⟩
        exact ⟨F.inv_mem hxF, by rw [inv_pow, hx3, inv_one]⟩ }
  have hF_le_P : F ≤ P := fun _ hx => hx.1
  have hF3_le : Nat.card ↥F₃ ≤ Nat.card ↥ψ.ker * Nat.card ↥A₀ := by
    let conjHom : ↥F₃ →* MulAut L' :=
      (MulAut.conj : L' →* MulAut L').comp F₃.subtype
    have hrange_le : conjHom.range ≤ A₀ := by
      rintro φ ⟨x, rfl⟩
      have hxF : x.1 ∈ F := x.2.1
      have hxP : x.1 ∈ P := hxF.1
      have hxfix : ∀ a ∈ A, a x.1 = x.1 := hxF.2
      have hx3 : x.1 ^ 3 = 1 := x.2.2
      have hconjA : MulAut.conj x.1 ∈ A := hSC x.1 hxfix hx3
      have hDinn : D (MulAut.conj x.1) ∈ (MulAut.conj : R →* MulAut R).range := by
        rw [hdesc_conj x.1]
        exact MonoidHom.mem_range.mpr ⟨ψ x.1, rfl⟩
      exact ⟨hconjA, Subgroup.mem_comap.mpr hDinn⟩
    have hker_le : conjHom.ker.map F₃.subtype ≤ ψ.ker := by
      intro z hz
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hz
      have hx1 : MulAut.conj x.1 = 1 := hx
      have hxcenter : x.1 ∈ Subgroup.center L' := ct_conj_eq_one_mem_center hx1
      rw [hZ]
      exact hxcenter
    have hker_card : Nat.card ↥conjHom.ker =
        Nat.card ↥(conjHom.ker.map F₃.subtype) :=
      (Subgroup.card_map_of_injective F₃.subtype_injective).symm
    calc Nat.card ↥F₃ = Nat.card ↥conjHom.ker * Nat.card ↥conjHom.range :=
          (Subgroup.card_ker_mul_card_range conjHom).symm
      _ ≤ Nat.card ↥ψ.ker * Nat.card ↥A₀ := by
          rw [hker_card]
          exact Nat.mul_le_mul (Subgroup.card_le_of_le hker_le)
            (Subgroup.card_le_of_le hrange_le)
  have hNle : Nat.card ↥ψ.ker ≤ 3 := Nat.le_of_dvd (by norm_num) hN
  rcases hcase with hYInn | hexp
  ·
    have hA0eqA : A₀ = A := by
      refine le_antisymm hA0_le fun a ha => ?_
      exact ⟨ha, Subgroup.mem_comap.mpr (hYInn (hDY a ha))⟩
    have hF_eq_P : F = P := by
      refine le_antisymm hF_le_P fun x hx => ?_
      exact ⟨hx, fun a ha => hfixP a (by rw [hA0eqA]; exact ha) x hx⟩
    let cubeHom : ↥P →* L' :=
      { toFun := fun x => (x : L') ^ 3
        map_one' := one_pow 3
        map_mul' := fun x y => by
          have hxy : Commute (x : L') (y : L') := by
            show (x : L') * (y : L') = (y : L') * (x : L')
            exact hcommP x.1 x.2 y.1 y.2
          rw [Subgroup.coe_mul]
          exact Commute.mul_pow hxy 3 }
    have hcube_range : cubeHom.range ≤ ψ.ker := by
      rintro z ⟨x, rfl⟩
      change ψ ((x : L') ^ 3) = 1
      apply hconjinj
      change (MulAut.conj : R →* MulAut R) (ψ ((x : L') ^ 3)) =
        (MulAut.conj : R →* MulAut R) 1
      rw [map_pow, map_pow, hYab.2 ((MulAut.conj : R →* MulAut R) (ψ x.1))
        ((hPmem x.1).mp x.2), map_one]
    have hF3_eq_cube : cubeHom.ker.map P.subtype = F₃ := by
      ext z
      constructor
      · rintro ⟨x, hx, rfl⟩
        have hx3 : (x : L') ^ 3 = 1 := hx
        refine ⟨⟨x.2, fun a ha => ?_⟩, hx3⟩
        exact hfixP a (by rw [hA0eqA]; exact ha) x x.2
      · rintro ⟨hzF, hz3⟩
        refine Subgroup.mem_map.mpr ⟨⟨z, hzF.1⟩, ?_, rfl⟩
        change (z : L') ^ 3 = 1
        exact hz3
    have hP_eq : Nat.card ↥P = Nat.card ↥F₃ * Nat.card ↥cubeHom.range := by
      have hk : Nat.card ↥cubeHom.ker = Nat.card ↥F₃ := by
        rw [← Subgroup.card_map_of_injective P.subtype_injective, hF3_eq_cube]
      rw [← Subgroup.card_ker_mul_card_range cubeHom, hk]
    have hYinf_eq : Y ⊓ (MulAut.conj : R →* MulAut R).range = Y := inf_eq_left.mpr hYInn
    have hPval : Nat.card ↥P = 3 ^ 6 * Nat.card ↥ψ.ker := by
      rw [hPcard, hYinf_eq, hYcard, Nat.mul_comm]
    have hF3_ge : 3 ^ 6 ≤ Nat.card ↥F₃ := by
      have h : Nat.card ↥ψ.ker * 3 ^ 6 ≤ Nat.card ↥ψ.ker * Nat.card ↥F₃ := by
        calc Nat.card ↥ψ.ker * 3 ^ 6 = Nat.card ↥P := by rw [hPval, Nat.mul_comm]
          _ = Nat.card ↥F₃ * Nat.card ↥cubeHom.range := hP_eq
          _ ≤ Nat.card ↥F₃ * Nat.card ↥ψ.ker :=
              Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hcube_range)
          _ = Nat.card ↥ψ.ker * Nat.card ↥F₃ := Nat.mul_comm _ _
      exact Nat.le_of_mul_le_mul_left h hNpos
    have hle : 3 ^ 6 ≤ Nat.card ↥ψ.ker * Nat.card ↥A₀ := le_trans hF3_ge hF3_le
    rw [hA0eqA, hA4] at hle
    nlinarith [hle, hNle, hNpos]
  ·
    have hcube1 : ∀ l ∈ P, l ^ 3 = 1 := fun l hl => hexp l ((hPmem l).mp hl)
    have hF3_eq_F : F₃ = F := by
      refine le_antisymm (fun x hx => hx.1) fun x hx => ⟨hx, hcube1 x hx.1⟩
    by_cases hA0eqA : A₀ = A
    ·
      have hF_eq_P : F = P := by
        refine le_antisymm hF_le_P fun x hx => ?_
        exact ⟨hx, fun a ha => hfixP a (by rw [hA0eqA]; exact ha) x hx⟩
      have hle : 3 ^ 5 * Nat.card ↥ψ.ker ≤ Nat.card ↥ψ.ker * 3 ^ 4 := by
        calc 3 ^ 5 * Nat.card ↥ψ.ker ≤ Nat.card ↥P := hP_lower
          _ = Nat.card ↥F₃ := by rw [hF3_eq_F, hF_eq_P]
          _ ≤ Nat.card ↥ψ.ker * Nat.card ↥A₀ := hF3_le
          _ = Nat.card ↥ψ.ker * 3 ^ 4 := by rw [hA0eqA, hA4]
      nlinarith [hle, hNpos]
    ·
      have hA0lt : A₀ < A := lt_of_le_of_ne hA0_le hA0eqA
      have hA0card27 : Nat.card ↥A₀ = 3 ^ 3 := by
        have hdvd : Nat.card ↥A₀ ∣ 3 ^ 4 := by
          rw [← hA4]; exact Subgroup.card_dvd_of_le hA0_le
        have hlt : Nat.card ↥A₀ < 3 ^ 4 := by
          rw [← hA4]; exact Subgroup.card_lt_of_lt hA0lt
        have hge : 3 ^ 3 ≤ Nat.card ↥A₀ := by
          rw [hA0card]; exact hSinf
        obtain ⟨k, hk4, hk⟩ :=
          (Nat.dvd_prime_pow (p := 3) Nat.prime_three (m := 4)).mp (by simpa using hdvd)
        rw [hk] at hge hlt ⊢
        have hk3 : k = 3 := by
          have h1 : 3 ≤ k :=
            (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp (by simpa using hge)
          have h2 : k < 4 :=
            (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp (by simpa using hlt)
          omega
        rw [hk3]
      obtain ⟨a₁, ha₁A, ha₁notA0⟩ : ∃ a₁, a₁ ∈ A ∧ a₁ ∉ A₀ := by
        by_contra h
        simp only [not_exists, not_and, not_not] at h
        exact hA0eqA (le_antisymm hA0_le fun a ha => h a ha)
      have hgen : A₀ ⊔ Subgroup.zpowers a₁ = A := by
        have hBA : A₀ ⊔ Subgroup.zpowers a₁ ≤ A :=
          sup_le hA0_le (Subgroup.zpowers_le.mpr ha₁A)
        have hlt : A₀ < A₀ ⊔ Subgroup.zpowers a₁ := by
          refine lt_of_le_of_ne le_sup_left ?_
          intro heq
          exact ha₁notA0 (by rw [heq]; exact (le_sup_right :
            Subgroup.zpowers a₁ ≤ A₀ ⊔ Subgroup.zpowers a₁) (Subgroup.mem_zpowers a₁))
        have hBcard : Nat.card ↥(A₀ ⊔ Subgroup.zpowers a₁) = 3 ^ 4 := by
          have hBdvd : Nat.card ↥(A₀ ⊔ Subgroup.zpowers a₁) ∣ 3 ^ 4 := by
            rw [← hA4]; exact Subgroup.card_dvd_of_le hBA
          have hge : 3 ^ 3 < Nat.card ↥(A₀ ⊔ Subgroup.zpowers a₁) := by
            rw [← hA0card27]; exact Subgroup.card_lt_of_lt hlt
          obtain ⟨k, hk4, hk⟩ :=
            (Nat.dvd_prime_pow (p := 3) Nat.prime_three (m := 4)).mp (by simpa using hBdvd)
          rw [hk] at hge ⊢
          have hk4' : k = 4 := by
            have h1 : 3 < k :=
              (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 3)).mp (by simpa using hge)
            omega
          rw [hk4']
        exact Subgroup.eq_of_le_of_card_ge hBA (by rw [hBcard, hA4])
      have hmodker : ∀ x ∈ P, a₁ x * x⁻¹ ∈ ψ.ker := by
        intro x hx
        rw [MonoidHom.mem_ker, map_mul, map_inv, hmod a₁ ha₁A x hx, mul_inv_cancel]
      have hstab_mem : ∀ a ∈ A, ∀ x ∈ P, a₁ x = x → a x = x := by
        intro a ha x hx ha₁x
        let stab : Subgroup (MulAut L') :=
          { carrier := {b | b x = x}
            one_mem' := rfl
            mul_mem' := by
              intro b c hb hc
              show (b * c) x = x
              rw [MulAut.mul_apply, hc, hb]
            inv_mem' := by
              intro b hb
              show b⁻¹ x = x
              have h1 : b⁻¹ (b x) = b⁻¹ x := congrArg (fun y => b⁻¹ y) hb
              have h2 : b⁻¹ (b x) = x := by
                rw [← MulAut.mul_apply, inv_mul_cancel, MulAut.one_apply]
              exact h1.symm.trans h2 }
        have ha₁stab : a₁ ∈ stab := ha₁x
        have hgenA : A ≤ stab := by
          rw [← hgen]
          refine sup_le ?_ ?_
          · intro b hb
            exact hfixP b hb x hx
          · intro b hb
            rw [Subgroup.mem_zpowers_iff] at hb
            obtain ⟨k, rfl⟩ := hb
            exact stab.zpow_mem ha₁stab k
        exact hgenA ha
      let c1 : ↥P →* L' :=
        { toFun := fun x => a₁ (x : L') * (x : L')⁻¹
          map_one' := by simp
          map_mul' := fun x y => by
            have hz : a₁ (y : L') * (y : L')⁻¹ ∈ Subgroup.center L' :=
              hker (hmodker y y.2)
            have hcz : (x : L')⁻¹ * (a₁ (y : L') * (y : L')⁻¹) =
                (a₁ (y : L') * (y : L')⁻¹) * (x : L')⁻¹ :=
              Subgroup.mem_center_iff.mp hz (x : L')⁻¹
            show a₁ ((x : L') * (y : L')) * ((x : L') * (y : L'))⁻¹ =
              (a₁ (x : L') * (x : L')⁻¹) * (a₁ (y : L') * (y : L')⁻¹)
            rw [map_mul, mul_inv_rev]
            calc a₁ (x : L') * a₁ (y : L') * ((y : L')⁻¹ * (x : L')⁻¹)
                = (a₁ (x : L') * (a₁ (y : L') * (y : L')⁻¹)) * (x : L')⁻¹ := by group
              _ = a₁ (x : L') * ((a₁ (y : L') * (y : L')⁻¹) * (x : L')⁻¹) := by group
              _ = a₁ (x : L') * ((x : L')⁻¹ * (a₁ (y : L') * (y : L')⁻¹)) := by rw [hcz]
              _ = (a₁ (x : L') * (x : L')⁻¹) * (a₁ (y : L') * (y : L')⁻¹) := by group }
      have hc1_range : c1.range ≤ ψ.ker := by
        rintro z ⟨x, rfl⟩
        exact hmodker x x.2
      have hc1_ker : c1.ker.map P.subtype = F := by
        ext z
        constructor
        · rintro ⟨x, hx, rfl⟩
          have hx1 : a₁ (x : L') = (x : L') := by
            exact mul_inv_eq_one.mp (MonoidHom.mem_ker.mp hx)
          exact ⟨x.2, fun a ha => hstab_mem a ha x x.2 hx1⟩
        · rintro ⟨hzP, hzfix⟩
          refine Subgroup.mem_map.mpr ⟨⟨z, hzP⟩, ?_, rfl⟩
          exact MonoidHom.mem_ker.mpr (mul_inv_eq_one.mpr (hzfix a₁ ha₁A))
      have hker_card : Nat.card ↥c1.ker = Nat.card ↥F := by
        rw [← Subgroup.card_map_of_injective P.subtype_injective, hc1_ker]
      have hP_le_F : Nat.card ↥P ≤ Nat.card ↥F * Nat.card ↥ψ.ker := by
        calc Nat.card ↥P = Nat.card ↥c1.ker * Nat.card ↥c1.range :=
              (Subgroup.card_ker_mul_card_range c1).symm
          _ = Nat.card ↥F * Nat.card ↥c1.range := by rw [hker_card]
          _ ≤ Nat.card ↥F * Nat.card ↥ψ.ker :=
              Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hc1_range)
      have hF_le : Nat.card ↥F ≤ Nat.card ↥ψ.ker * 3 ^ 3 := by
        rw [← hF3_eq_F]
        calc Nat.card ↥F₃ ≤ Nat.card ↥ψ.ker * Nat.card ↥A₀ := hF3_le
          _ = Nat.card ↥ψ.ker * 3 ^ 3 := by rw [hA0card27]
      have hle : 3 ^ 5 * Nat.card ↥ψ.ker ≤
          (Nat.card ↥ψ.ker * 3 ^ 3) * Nat.card ↥ψ.ker := by
        calc 3 ^ 5 * Nat.card ↥ψ.ker ≤ Nat.card ↥P := hP_lower
          _ ≤ Nat.card ↥F * Nat.card ↥ψ.ker := hP_le_F
          _ ≤ (Nat.card ↥ψ.ker * 3 ^ 3) * Nat.card ↥ψ.ker :=
              Nat.mul_le_mul_right _ hF_le
      nlinarith [hle, hNle, hNpos]

end CFSG.StandardType.TwE6R4
