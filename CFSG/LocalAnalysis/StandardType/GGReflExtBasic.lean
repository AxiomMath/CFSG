module

public import CFSG.LocalAnalysis.StandardType.GGReflExtLin
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallVerifyO
public import Certificates.Data.CFSGNative.ReflExt.Core
public import CFSG.LocalAnalysis.StandardType.GGTwoNodeSmallPosWeylLemmas

public section

namespace CFSG.ReflExt

open CFSG.TwoNodeSmall

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def HasRefl (P : Pt) (A : Subgroup (P.V ≃ₗ[ZMod P.p] P.V)) (r : Refl) : Prop :=
  ∃ e ∈ A, ∀ w, e w = w - P.dot (P.vec r.f) w • P.vec r.h

theorem reqb_eq {r s : Refl} (h : reqb r s = true) : r = s := by
  obtain ⟨rf, rh⟩ := r
  obtain ⟨sf, sh⟩ := s
  simp only [reqb, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  have h1' : rf = sf := h1
  have h2' : rh = sh := h2
  rw [h1', h2']

@[expose] def natVec (P : Pt) (v : P.V) : Vec :=
  (List.range P.D).map fun i => if h : i < P.D then (v ⟨i, h⟩).val else 0

theorem natVec_length (P : Pt) (v : P.V) : (natVec P v).length = P.D := by
  simp [natVec]

theorem natVec_lt (P : Pt) [Fact P.p.Prime] (v : P.V) : ∀ x ∈ natVec P v, x < P.p := by
  intro x hx
  simp only [natVec, List.mem_map, List.mem_range] at hx
  obtain ⟨i, hi, rfl⟩ := hx
  haveI : NeZero P.p := ⟨(Fact.out : P.p.Prime).ne_zero⟩
  rw [dif_pos hi]
  exact ZMod.val_lt _

theorem vec_natVec (P : Pt) [Fact P.p.Prime] (v : P.V) : P.vec (natVec P v) = v := by
  haveI : NeZero P.p := ⟨(Fact.out : P.p.Prime).ne_zero⟩
  funext j
  show (((natVec P v).getD j.val 0 : ℕ) : ZMod P.p) = v j
  simp only [natVec]
  rw [pww2_getD_range_map P.D (fun i => if h : i < P.D then (v ⟨i, h⟩).val else 0) j]
  rw [dif_pos j.isLt]
  exact ZMod.natCast_zmod_val (v ⟨j.val, j.isLt⟩)

theorem allVecsP_mem {p : ℕ} :
    ∀ (n : ℕ) (l : Vec), l.length = n → (∀ x ∈ l, x < p) → l ∈ allVecsP p n
  | 0, l, hlen, _ => by
      cases l with
      | nil => simp [allVecsP]
      | cons a t => simp at hlen
  | n + 1, l, hlen, hlt => by
      cases l with
      | nil => simp at hlen
      | cons a t =>
          simp only [allVecsP]
          refine List.mem_flatMap.mpr
            ⟨t, allVecsP_mem n t (by simpa using hlen) (fun x hx => hlt x (by simp [hx])), ?_⟩
          simp only [List.mem_map, List.mem_range]
          exact ⟨a, hlt a (by simp), rfl⟩

theorem natVec_mem (P : Pt) [Fact P.p.Prime] (v : P.V) : natVec P v ∈ allVecsP P.p P.D :=
  allVecsP_mem P.D _ (natVec_length P v) (natVec_lt P v)

theorem dotv_eq_zero_iff (P : Pt) [Fact P.p.Prime] (f g : Vec) :
    P.dotv f g = 0 ↔ P.dot (P.vec f) (P.vec g) = 0 := by
  rw [← Pt.dotv_spec P f g]
  have hlt : P.dotv f g < P.p := by
    unfold Pt.dotv
    exact Nat.mod_lt _ (Fact.out : P.p.Prime).pos
  constructor
  · intro h; rw [h]; simp
  · intro h
    have hd : P.p ∣ P.dotv f g := (CharP.cast_eq_zero_iff (ZMod P.p) P.p _).mp h
    exact Nat.eq_zero_of_dvd_of_lt hd hlt

theorem dotv_eq_two_iff (P : Pt) [Fact P.p.Prime] (f g : Vec) :
    P.dotv f g = 2 % P.p ↔ P.dot (P.vec f) (P.vec g) = 2 := by
  rw [← Pt.dotv_spec P f g]
  have hlt : P.dotv f g < P.p := by
    unfold Pt.dotv
    exact Nat.mod_lt _ (Fact.out : P.p.Prime).pos
  have hlt2 : 2 % P.p < P.p := Nat.mod_lt _ (Fact.out : P.p.Prime).pos
  constructor
  · intro h
    rw [h]
    simp
  · intro h
    have h2 : ((P.dotv f g : ℕ) : ZMod P.p) = ((2 % P.p : ℕ) : ZMod P.p) := by
      rw [h]; simp
    rw [ZMod.natCast_eq_natCast_iff'] at h2
    rw [Nat.mod_eq_of_lt hlt, Nat.mod_eq_of_lt hlt2] at h2
    exact h2

theorem wfR_iff (P : Pt) [Fact P.p.Prime] (r : Refl) :
    wfR P r = true ↔ P.dot (P.vec r.f) (P.vec r.h) = 2 := by
  unfold wfR
  rw [beq_iff_eq]
  exact dotv_eq_two_iff P r.f r.h

theorem mem_candList (P : Pt) (rs : List Refl) (c : Refl) (hf : c.f ∈ allVecsP P.p P.D)
    (hh : c.h ∈ allVecsP P.p P.D) (hdot : P.dotv c.f c.h = 2 % P.p)
    (hsym : ∀ ρ ∈ rs, asymR P c ρ = false) : c ∈ candList P rs := by
  have hmask : maskF P rs c.f = maskH P rs c.h := by
    unfold maskF maskH
    apply List.map_congr_left
    intro ρ hρ
    exact bne_eq_false_iff_eq.mp (hsym ρ hρ)
  unfold candList
  refine List.mem_flatMap.mpr ⟨(c.f, maskF P rs c.f), List.mem_map.mpr ⟨c.f, hf, rfl⟩, ?_⟩
  refine List.mem_filterMap.mpr ⟨(c.h, maskH P rs c.h), List.mem_map.mpr ⟨c.h, hh, rfl⟩, ?_⟩
  simp [hmask, hdot]

theorem wfR_of_wfCheck {P : Pt} (h : wfCheck P = true) {r : Refl} (hr : r ∈ P.gens) :
    wfR P r = true := List.all_eq_true.mp h r hr

theorem wfCheck_withExtra {P0 : Pt} (h0 : wfCheck P0 = true) {extra : List Refl}
    (he : ∀ r ∈ extra, wfR P0 r = true) : wfCheck (withExtra P0 extra) = true := by
  unfold wfCheck
  rw [List.all_eq_true]
  intro r hr
  simp only [withExtra, List.mem_append] at hr
  rcases hr with hr | hr
  · exact List.all_eq_true.mp h0 r hr
  · exact he r hr

theorem group_le_of_gens (P : Pt) [Fact P.p.Prime] (A : Subgroup (P.V ≃ₗ[ZMod P.p] P.V))
    (h : ∀ r ∈ P.gens, HasRefl P A r) : P.group ≤ A := by
  unfold Pt.group
  rw [Subgroup.closure_le]
  rintro e ⟨r, hr, he⟩
  obtain ⟨e', he'A, he'⟩ := h r hr
  have heq : e = e' := LinearEquiv.ext fun w => (he w).trans (he' w).symm
  rw [heq]
  exact he'A

theorem withExtra_group_le (P0 : Pt) [Fact P0.p.Prime] (extra : List Refl)
    (A : Subgroup (P0.V ≃ₗ[ZMod P0.p] P0.V))
    (h : ∀ r ∈ P0.gens ++ extra, HasRefl P0 A r) : (withExtra P0 extra).group ≤ A :=
  group_le_of_gens (withExtra P0 extra) A h

theorem realizes_hasRefl {P : Pt} [Fact P.p.Prime] (hwf : P.WF) {w : Word} {r : Refl}
    (h : realizes P w r = true) :
    ∃ γ ∈ P.group, ∀ x, γ x = x - P.dot (P.vec r.f) x • P.vec r.h := by
  unfold realizes at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  obtain ⟨hw, hall⟩ := h
  obtain ⟨γ, hγmem, hγ⟩ := Pt.applyWord_spec P hwf w hw
  refine ⟨γ, hγmem, ?_⟩
  let ρ : P.V →ₗ[ZMod P.p] P.V :=
    LinearMap.id - (pww2_dotLM P (P.vec r.f)).smulRight (P.vec r.h)
  have hext : (γ : P.V →ₗ[ZMod P.p] P.V) = ρ := by
    apply pww2_lin_ext_unit P
    intro j
    show γ (P.vec (P.unit j)) = ρ (P.vec (P.unit j))
    rw [hγ, pww2_vec_of_vecEq P _ _ (hall j.val j.isLt), Pt.vec_applyRefl]
    simp [ρ, pww2_dotLM, LinearMap.smulRight_apply]
  intro x
  have := congrArg (fun m : P.V →ₗ[ZMod P.p] P.V => m x) hext
  simpa [ρ, pww2_dotLM, LinearMap.smulRight_apply] using this

theorem dotLM_apply (P : Pt) (f w : P.V) : pww2_dotLM P f w = P.dot f w := rfl

theorem asym_transv {P : Pt} [Fact P.p.Prime] (hp2 : P.p ≠ 2)
    {A : Subgroup (P.V ≃ₗ[ZMod P.p] P.V)} {c ρ : Refl} (hc : wfR P c = true)
    (hρ : wfR P ρ = true) (hcA : HasRefl P A c) (hρA : HasRefl P A ρ)
    (h : asymR P c ρ = true) : ∃ g ∈ A, IsTransv g := by
  obtain ⟨s, hsA, hs⟩ := hcA
  obtain ⟨t, htA, ht⟩ := hρA
  have hc2 := (wfR_iff P c).mp hc
  have hρ2 := (wfR_iff P ρ).mp hρ
  have key : (P.dot (P.vec c.f) (P.vec ρ.h) = 0 ∧ P.dot (P.vec ρ.f) (P.vec c.h) ≠ 0) ∨
      (P.dot (P.vec c.f) (P.vec ρ.h) ≠ 0 ∧ P.dot (P.vec ρ.f) (P.vec c.h) = 0) := by
    by_cases h1 : P.dotv c.f ρ.h = 0
    · by_cases h2 : P.dotv ρ.f c.h = 0
      · exfalso
        have e1 : (P.dotv c.f ρ.h == 0) = true := beq_iff_eq.mpr h1
        have e2 : (P.dotv ρ.f c.h == 0) = true := beq_iff_eq.mpr h2
        unfold asymR at h
        rw [e1, e2] at h
        exact absurd h (by decide)
      · left
        exact ⟨(dotv_eq_zero_iff P _ _).mp h1, fun h3 => h2 ((dotv_eq_zero_iff P _ _).mpr h3)⟩
    · by_cases h2 : P.dotv ρ.f c.h = 0
      · right
        exact ⟨fun h3 => h1 ((dotv_eq_zero_iff P _ _).mpr h3), (dotv_eq_zero_iff P _ _).mp h2⟩
      · exfalso
        have e1 : (P.dotv c.f ρ.h == 0) = false := beq_eq_false_iff_ne.mpr h1
        have e2 : (P.dotv ρ.f c.h == 0) = false := beq_eq_false_iff_ne.mpr h2
        unfold asymR at h
        rw [e1, e2] at h
        exact absurd h (by decide)
  rcases key with ⟨k1, k2⟩ | ⟨k1, k2⟩
  · refine ⟨s * t * s * t, A.mul_mem (A.mul_mem (A.mul_mem hsA htA) hsA) htA, ?_⟩
    exact refl_asym_transv hp2 s t (pww2_dotLM P (P.vec c.f)) (pww2_dotLM P (P.vec ρ.f))
      (P.vec c.h) (P.vec ρ.h) hs ht hc2 hρ2 k1 k2
  · refine ⟨t * s * t * s, A.mul_mem (A.mul_mem (A.mul_mem htA hsA) htA) hsA, ?_⟩
    exact refl_asym_transv hp2 t s (pww2_dotLM P (P.vec ρ.f)) (pww2_dotLM P (P.vec c.f))
      (P.vec ρ.h) (P.vec c.h) ht hs hρ2 hc2 k2 k1

theorem finite_linEquiv (P : Pt) [Fact P.p.Prime] : Finite (P.V ≃ₗ[ZMod P.p] P.V) := by
  haveI : NeZero P.p := ⟨(Fact.out : P.p.Prime).ne_zero⟩
  exact Finite.of_injective (fun e : P.V ≃ₗ[ZMod P.p] P.V => (e : P.V → P.V)) DFunLike.coe_injective

theorem order_contra (P0 : Pt) [Fact P0.p.Prime] (extra : List Refl) {o : OWit}
    (hwf : (withExtra P0 extra).WF) (hv : verifyO (withExtra P0 extra) o P0.bound = true)
    (A : Subgroup (P0.V ≃ₗ[ZMod P0.p] P0.V)) (hle : (withExtra P0 extra).group ≤ A)
    (hcard : Nat.card A ≤ P0.bound) : False := by
  haveI := finite_linEquiv P0
  haveI : Fact (withExtra P0 extra).p.Prime := ‹Fact P0.p.Prime›
  have h1 : P0.bound < Nat.card (withExtra P0 extra).group := verifyO_sound hwf hv
  have h2 : Nat.card (withExtra P0 extra).group ≤ Nat.card A := Subgroup.card_le_of_le hle
  omega

end CFSG.ReflExt

end
