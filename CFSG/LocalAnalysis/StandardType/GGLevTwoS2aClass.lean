module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS2aAux
public import CFSG.LocalAnalysis.StandardType.GGLevTwoTrans
public import CFSG.ClassicalInvolution.ModelFacts.Families

public section

namespace CFSG.StandardType.LevTwo

open CFSG.LieType.RootSystem CFSG.LieType.Universal.SpecialLinear
open CFSG.ClassicalInvolution.ModelFacts
open scoped Matrix

theorem levTwoS2a_lam_root (n p : ℕ) (c : Fin n → ZMod p) {β : Fin n → ℤ} {a b : Fin (n+1)}
    (h : toStd n β = Pi.single a 1 - Pi.single b 1) :
    lam c β = levTwoS2a_D n p c a - levTwoS2a_D n p c b := by
  rw [levTwoS2a_lam_coord, h]
  simp only [Pi.sub_apply]
  push_cast
  simp only [sub_mul, Finset.sum_sub_distrib]
  congr 1
  · rw [Finset.sum_eq_single a]
    · simp
    · intro b' _ hb'; simp [Ne.symm hb']
    · intro hmem; exact absurd (Finset.mem_univ a) hmem
  · rw [Finset.sum_eq_single b]
    · simp
    · intro b' _ hb'; simp [Ne.symm hb']
    · intro hmem; exact absurd (Finset.mem_univ b) hmem

theorem levTwoS2a_Phi_eq (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (_hp : p.Prime) (_hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) :
    Φ = {β | IsRt (isFiniteType_A n) β ∧ lam c β = 0} := by
  ext β
  constructor
  · intro hβ; exact ⟨h.isRt β hβ, h.fix β hβ⟩
  · rintro ⟨hβrt, hβlam⟩
    obtain ⟨s, hsΦ, -, h3, -, -⟩ := h.rank
    have hne : s.Nonempty := Finset.card_pos.mp (by omega)
    obtain ⟨α, hαs⟩ := hne
    have hαΦ : α ∈ Φ := hsΦ hαs
    have hαrt : IsRt (isFiniteType_A n) α := h.isRt α hαΦ
    obtain ⟨κ, hκpos, hκ⟩ := levTwoS2a_form_coord n hn
    have heq : form (isFiniteType_A n) (toRat α) (toRat α) =
        form (isFiniteType_A n) (toRat β) (toRat β) := by
      rw [hκ α α, hκ β β]
      obtain ⟨a1, b1, hab1, hc1⟩ := (levTwoS2a_isRt_iff_coord n hn α).mp hαrt
      obtain ⟨a2, b2, hab2, hc2⟩ := (levTwoS2a_isRt_iff_coord n hn β).mp hβrt
      rw [levTwoS2a_dot_root_self n hab1 hc1, levTwoS2a_dot_root_self n hab2 hc2]
    obtain ⟨w, hw⟩ := exists_weylAction_eq_of_isRt (isFiniteType_A n)
      (isIrreducible_A (by omega)) hαrt hβrt heq
    exact h.sat β hβrt hβlam ⟨α, hαΦ, w, hw⟩

theorem levTwoS2a_Phi_fibre (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) :
    Φ = {β | ∃ a b : Fin (n+1), a ≠ b ∧ toStd n β = Pi.single a 1 - Pi.single b 1 ∧
      levTwoS2a_D n p c a = levTwoS2a_D n p c b} := by
  rw [levTwoS2a_Phi_eq n hn p hp hp2 c Φ h]
  ext β
  constructor
  · rintro ⟨hrt, hlam⟩
    obtain ⟨a, b, hab, hc⟩ := (levTwoS2a_isRt_iff_coord n hn β).mp hrt
    exact ⟨a, b, hab, hc, sub_eq_zero.mp (by rw [← levTwoS2a_lam_root n p c hc]; exact hlam)⟩
  · rintro ⟨a, b, hab, hc, hD⟩
    exact ⟨(levTwoS2a_isRt_iff_coord n hn β).mpr ⟨a, b, hab, hc⟩, by
      rw [levTwoS2a_lam_root n p c hc, hD, sub_self]⟩

theorem levTwoS2a_form_eq_zero_of_disjoint (n : ℕ) (hn : 1 ≤ n) {β γ : Fin n → ℤ}
    {a b c d : Fin (n+1)} (hac : a ≠ c) (had : a ≠ d) (hbc : b ≠ c) (hbd : b ≠ d)
    (hβ : toStd n β = Pi.single a 1 - Pi.single b 1)
    (hγ : toStd n γ = Pi.single c 1 - Pi.single d 1) :
    form (isFiniteType_A n) (toRat β) (toRat γ) = 0 := by
  obtain ⟨κ, hκpos, hκ⟩ := levTwoS2a_form_coord n hn
  rw [hκ β γ, levTwoS2a_dot_root_root n hβ hγ]
  rw [if_neg hac, if_neg hbd, if_neg had, if_neg hbc]
  ring

def levTwoS2a_inFibre (n p : ℕ) (c : Fin n → ZMod p) (a : Fin (n+1)) (β : Fin n → ℤ) : Prop :=
  ∃ a' b' : Fin (n+1), a' ≠ b' ∧ toStd n β = Pi.single a' 1 - Pi.single b' 1 ∧
    levTwoS2a_D n p c a' = levTwoS2a_D n p c a ∧
    levTwoS2a_D n p c a' = levTwoS2a_D n p c b'

theorem levTwoS2a_inFibre_step (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {a : Fin (n+1)} {β γ : Fin n → ℤ}
    (hβ : levTwoS2a_inFibre n p c a β) (hγ : γ ∈ Φ)
    (hform : form (isFiniteType_A n) (toRat β) (toRat γ) ≠ 0) :
    levTwoS2a_inFibre n p c a γ := by
  obtain ⟨a', b', hab, hβc, hDa', hDab⟩ := hβ
  have hγE : ∃ c' d' : Fin (n+1), c' ≠ d' ∧ toStd n γ = Pi.single c' 1 - Pi.single d' 1 ∧
      levTwoS2a_D n p c c' = levTwoS2a_D n p c d' := by
    have := hγ
    rw [levTwoS2a_Phi_fibre n hn p hp hp2 c Φ h] at this
    simpa only [Set.mem_setOf_eq] using this
  obtain ⟨c', d', hcd, hγc, hDcd⟩ := hγE
  have hmeet : a' = c' ∨ a' = d' ∨ b' = c' ∨ b' = d' := by
    by_contra hc
    simp only [not_or] at hc
    obtain ⟨h1, h2, h3, h4⟩ := hc
    exact hform (levTwoS2a_form_eq_zero_of_disjoint n hn h1 h2 h3 h4 hβc hγc)
  rcases hmeet with hh | hh | hh | hh
  · have hda : levTwoS2a_D n p c c' = levTwoS2a_D n p c a := by rw [← hh]; exact hDa'
    exact ⟨c', d', hcd, hγc, hda, hDcd⟩
  · have hd : levTwoS2a_D n p c d' = levTwoS2a_D n p c a := by rw [← hh]; exact hDa'
    exact ⟨c', d', hcd, hγc, hDcd.trans hd, hDcd⟩
  · have hb : levTwoS2a_D n p c b' = levTwoS2a_D n p c a' := hDab.symm
    have hcb : levTwoS2a_D n p c c' = levTwoS2a_D n p c b' := by rw [← hh]
    exact ⟨c', d', hcd, hγc, hcb.trans (hb.trans hDa'), hDcd⟩
  · have hb : levTwoS2a_D n p c b' = levTwoS2a_D n p c a' := hDab.symm
    have hdb : levTwoS2a_D n p c d' = levTwoS2a_D n p c b' := by rw [← hh]
    exact ⟨c', d', hcd, hγc, hDcd.trans (hdb.trans (hb.trans hDa')), hDcd⟩

theorem levTwoS2a_inFibre_of_irred (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {a : Fin (n+1)} {β γ : Fin n → ℤ}
    (hβ : levTwoS2a_inFibre n p c a β)
    (hirr : Relation.ReflTransGen (fun x y => y ∈ Φ ∧
      form (isFiniteType_A n) (toRat x) (toRat y) ≠ 0) β γ) :
    levTwoS2a_inFibre n p c a γ := by
  induction hirr with
  | refl => exact hβ
  | tail hab hbc ih => exact levTwoS2a_inFibre_step n hn p hp hp2 c Φ h ih hbc.1 hbc.2

theorem levTwoS2a_single_sub_single {n : ℕ} {a b c d : Fin (n+1)} (hab : a ≠ b)
    (h : (Pi.single a 1 - Pi.single b 1 : Fin (n+1) → ℤ) = Pi.single c 1 - Pi.single d 1) :
    a = c ∧ b = d := by
  have ha : (1:ℤ) = (if a = c then 1 else 0) - (if a = d then 1 else 0) := by
    simpa [Pi.sub_apply, Pi.single_apply, hab, Ne.symm hab] using congrFun h a
  have hb : (-1:ℤ) = (if b = c then 1 else 0) - (if b = d then 1 else 0) := by
    simpa [Pi.sub_apply, Pi.single_apply, hab, Ne.symm hab] using congrFun h b
  constructor
  · by_contra hc
    rw [if_neg hc] at ha
    split_ifs at ha <;> omega
  · by_contra hd
    rw [if_neg hd] at hb
    split_ifs at hb <;> omega

theorem levTwoS2a_inFibre_conflict {n p : ℕ} {c : Fin n → ZMod p} {a b : Fin (n+1)}
    {γ : Fin n → ℤ} (hab : levTwoS2a_D n p c a ≠ levTwoS2a_D n p c b)
    (h1 : levTwoS2a_inFibre n p c a γ) (h2 : levTwoS2a_inFibre n p c b γ) : False := by
  obtain ⟨a', b', hab', hc1, hDa', -⟩ := h1
  obtain ⟨a'', b'', hab'', hc2, hDa'', -⟩ := h2
  obtain ⟨rfl, rfl⟩ := levTwoS2a_single_sub_single hab' (hc1.symm.trans hc2)
  exact hab (hDa'.symm.trans hDa'')

theorem levTwoS2a_exists_large_fibre (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) :
    ∃ B : Fin (n+1), (∃ b : Fin (n+1), b ≠ B ∧ levTwoS2a_D n p c b = levTwoS2a_D n p c B) ∧
      ∀ a : Fin (n+1), (∃ b : Fin (n+1), b ≠ a ∧ levTwoS2a_D n p c b = levTwoS2a_D n p c a) →
        levTwoS2a_D n p c a = levTwoS2a_D n p c B := by
  obtain ⟨s, hsΦ, -, h3, -, -⟩ := h.rank
  have hne : s.Nonempty := Finset.card_pos.mp (by omega)
  obtain ⟨β, hβs⟩ := hne
  have hβΦ : β ∈ Φ := hsΦ hβs
  have hβE : ∃ a b : Fin (n+1), a ≠ b ∧ toStd n β = Pi.single a 1 - Pi.single b 1 ∧
      levTwoS2a_D n p c a = levTwoS2a_D n p c b := by
    have := hβΦ
    rw [levTwoS2a_Phi_fibre n hn p hp hp2 c Φ h] at this
    simpa only [Set.mem_setOf_eq] using this
  obtain ⟨B, b0, hBb0, hβc, hDBb0⟩ := hβE
  refine ⟨B, ⟨b0, hBb0.symm, hDBb0.symm⟩, ?_⟩
  intro a ha
  by_contra hne'
  obtain ⟨b1, hb1a, hDb1a⟩ := ha
  have hβf : levTwoS2a_inFibre n p c B β := by
    refine ⟨B, b0, ?_, hβc, rfl, hDBb0⟩
    exact hBb0
  have hγΦ : levTwoS2a_eps n a b1 ∈ Φ := by
    rw [levTwoS2a_Phi_fibre n hn p hp hp2 c Φ h]
    exact ⟨a, b1, hb1a.symm, levTwoS2a_toStd_eps n a b1, hDb1a.symm⟩
  have hγf : levTwoS2a_inFibre n p c a (levTwoS2a_eps n a b1) := by
    refine ⟨a, b1, ?_, levTwoS2a_toStd_eps n a b1, rfl, ?_⟩
    · exact hb1a.symm
    · exact hDb1a.symm
  have hirr := h.irred β hβΦ (levTwoS2a_eps n a b1) hγΦ
  exact levTwoS2a_inFibre_conflict (Ne.symm hne')
    (levTwoS2a_inFibre_of_irred n hn p hp hp2 c Φ h hβf hirr) hγf

@[expose] def levTwoS2a_fibreF (n p : ℕ) (c : Fin n → ZMod p) (B : Fin (n+1)) : Finset (Fin (n+1)) :=
  Finset.univ.filter (fun k => levTwoS2a_D n p c k = levTwoS2a_D n p c B)

theorem levTwoS2a_fibre_card_ge (n : ℕ) (hn : 1 ≤ n) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (c : Fin n → ZMod p) (Φ : Set (Fin n → ℤ))
    (h : LevTwoData (isFiniteType_A n) p c Φ) {B : Fin (n+1)}
    (_hB : ∃ b : Fin (n+1), b ≠ B ∧ levTwoS2a_D n p c b = levTwoS2a_D n p c B)
    (huniq : ∀ a : Fin (n+1), (∃ b : Fin (n+1), b ≠ a ∧ levTwoS2a_D n p c b = levTwoS2a_D n p c a) →
      levTwoS2a_D n p c a = levTwoS2a_D n p c B) :
    n - 1 ≤ (levTwoS2a_fibreF n p c B).card := by
  obtain ⟨s, hsΦ, hlin, h3, hnle, -⟩ := h.rank
  let t : Finset (Fin (n+1)) := (levTwoS2a_fibreF n p c B).erase B
  let w : Set (Fin (n+1) → ℚ) := Set.range (fun k : t =>
    (fun x : Fin (n+1) => (if x = (k : Fin (n+1)) then (1:ℚ) else 0) -
      (if x = B then (1:ℚ) else 0)))
  have hBmem : B ∈ levTwoS2a_fibreF n p c B :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ B, rfl⟩
  have htcard : t.card = (levTwoS2a_fibreF n p c B).card - 1 := by
    simp only [t]
    rw [Finset.card_erase_of_mem hBmem]
  have hv : LinearIndependent ℚ (fun β : s => toRat (toStd n (β : Fin n → ℤ))) := by
    have h1 : LinearIndependent ℚ (fun β : s =>
        levTwoS2a_toStdLinQ n (toRat (β : Fin n → ℤ))) :=
      hlin.map' (levTwoS2a_toStdLinQ n)
        (LinearMap.ker_eq_bot.mpr (levTwoS2a_toStdLinQ_injective n hn))
    simpa only [Function.comp_def, levTwoS2a_toStdLinQ_toRat] using h1
  have hsub : Set.range (fun β : s => toRat (toStd n (β : Fin n → ℤ))) ⊆
      Submodule.span ℚ w := by
    rintro y ⟨β, hβy⟩
    rw [← hβy]
    have hβΦ : (β : Fin n → ℤ) ∈ Φ := hsΦ β.2
    obtain ⟨a, b, hab, hc, hD⟩ : ∃ a b : Fin (n+1), a ≠ b ∧
        toStd n (β : Fin n → ℤ) = Pi.single a 1 - Pi.single b 1 ∧
        levTwoS2a_D n p c a = levTwoS2a_D n p c b := by
      have := hβΦ
      rw [levTwoS2a_Phi_fibre n hn p hp hp2 c Φ h] at this
      simpa only [Set.mem_setOf_eq] using this
    have hDaB : levTwoS2a_D n p c a = levTwoS2a_D n p c B :=
      huniq a ⟨b, hab.symm, hD.symm⟩
    have hDbB : levTwoS2a_D n p c b = levTwoS2a_D n p c B :=
      huniq b ⟨a, hab, hD⟩
    have htoRat : toRat (toStd n (β : Fin n → ℤ)) =
        (fun x : Fin (n+1) => (if x = a then (1:ℚ) else 0) - (if x = B then 1 else 0)) -
        (fun x : Fin (n+1) => (if x = b then (1:ℚ) else 0) - (if x = B then 1 else 0)) := by
      rw [hc]
      funext x
      simp only [Pi.sub_apply, Pi.single_apply, toRat_apply]
      push_cast
      ring
    dsimp only
    rw [htoRat]
    refine Submodule.sub_mem _ ?_ ?_
    · by_cases haB : a = B
      · rw [haB]
        simp only [sub_self]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span
          ⟨⟨a, Finset.mem_erase.mpr ⟨haB, Finset.mem_filter.mpr ⟨Finset.mem_univ a, hDaB⟩⟩⟩, rfl⟩
    · by_cases hbB : b = B
      · rw [hbB]
        simp only [sub_self]
        exact Submodule.zero_mem _
      · exact Submodule.subset_span
          ⟨⟨b, Finset.mem_erase.mpr ⟨hbB, Finset.mem_filter.mpr ⟨Finset.mem_univ b, hDbB⟩⟩⟩, rfl⟩
  have hcard := linearIndependent_le_span' (fun β : s => toRat (toStd n (β : Fin n → ℤ))) hv w hsub
  have hcard' : s.card ≤ Fintype.card w := by
    have h : (s.card : Cardinal) ≤ (Fintype.card w : Cardinal) := by
      simpa only [Cardinal.mk_fintype, Fintype.card_coe] using hcard
    exact_mod_cast h
  rw [Fintype.card_fin] at hnle
  have hw : Fintype.card w ≤ t.card := by
    have := Fintype.card_range_le (f := fun k : t =>
      (fun x : Fin (n+1) => (if x = (k : Fin (n+1)) then (1:ℚ) else 0) -
        (if x = B then (1:ℚ) else 0)))
    simpa only [w, Fintype.card_coe] using this
  omega

theorem levTwoS2a_rRefl_coord (n : ℕ) (hn : 1 ≤ n) {β v : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_A n) β) {c d : Fin (n+1)} (hcd : c ≠ d)
    (hc : toStd n β = Pi.single c 1 - Pi.single d 1) :
    toStd n (weylAction (isFiniteType_A n) (rRefl (isFiniteType_A n) β) v) =
      toStd n v ∘ Equiv.swap c d := by
  obtain ⟨k, hk, hw⟩ := weylAction_rRefl (isFiniteType_A n) hβ v
  obtain ⟨κ, hκpos, hκ⟩ := levTwoS2a_form_coord n hn
  have hk' : (k:ℚ) = (toStd n v c : ℚ) - (toStd n v d : ℚ) := by
    have h1 : form (isFiniteType_A n) (toRat β) (toRat β) = κ * 2 := by
      rw [hκ β β, levTwoS2a_dot_root_self n hcd hc]
    have h2 : form (isFiniteType_A n) (toRat β) (toRat v) =
        κ * ((toStd n v c : ℚ) - (toStd n v d : ℚ)) := by
      rw [hκ β v]
      have hsum : (∑ k : Fin (n+1), (toStd n β k : ℚ) * (toStd n v k : ℚ)) =
          (toStd n v c : ℚ) - (toStd n v d : ℚ) := by
        rw [hc]
        rw [← levTwoS2a_dot_eps_left n c d (fun k => (toStd n v k : ℚ))]
        apply Finset.sum_congr rfl
        intro k _
        simp only [Pi.sub_apply, Pi.single_apply]
        push_cast
        rfl
      rw [hsum]
    rw [h1, h2] at hk
    have hk2 : (k:ℚ) * (κ * 2) =
        ((toStd n v c : ℚ) - (toStd n v d : ℚ)) * (κ * 2) := by
      rw [hk]; ring
    exact mul_right_cancel₀ (by positivity : κ * 2 ≠ 0) hk2
  have hkZ : k = toStd n v c - toStd n v d := by exact_mod_cast hk'
  have hsub : toStd n (v - k • β) = toStd n v - k • toStd n β := by
    rw [toStd_sub, toStd_smul]
  rw [hw, hsub, hc]
  funext x
  simp only [Pi.sub_apply, Pi.smul_apply, Pi.single_apply, Function.comp_apply]
  simp only [zsmul_eq_mul]
  by_cases hxc : x = c
  · subst hxc
    simp [hcd, hkZ, Equiv.swap_apply_left]
  · by_cases hxd : x = d
    · subst hxd
      simp [hxc, hkZ, Equiv.swap_apply_right]
    · simp [hxc, hxd, hkZ, Equiv.swap_apply_of_ne_of_ne hxc hxd]

theorem levTwoS2a_weylAction_rRefl_self (n : ℕ) (hn : 1 ≤ n) {β : Fin n → ℤ}
    (hβ : IsRt (isFiniteType_A n) β) :
    weylAction (isFiniteType_A n) (rRefl (isFiniteType_A n) β) β = -β := by
  obtain ⟨k, hk, hw⟩ := weylAction_rRefl (isFiniteType_A n) hβ β
  obtain ⟨κ, hκpos, hκ⟩ := levTwoS2a_form_coord n hn
  obtain ⟨a, b, hab, hc⟩ := (levTwoS2a_isRt_iff_coord n hn β).mp hβ
  have hff : form (isFiniteType_A n) (toRat β) (toRat β) ≠ 0 := by
    rw [hκ β β, levTwoS2a_dot_root_self n hab hc]
    positivity
  have hk2 : (k:ℚ) = 2 := mul_right_cancel₀ hff hk
  have hkZ : k = 2 := by exact_mod_cast hk2
  rw [hw, hkZ]
  abel

end CFSG.StandardType.LevTwo
