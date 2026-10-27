module

public import CFSG.RankThree.PartOne.KS.LyFiveGeneric
public import CFSG.RankThree.PartOne.KS.LyFiveInputs

public section

namespace CFSG.RankThree.PartOne.LyFive

open CFSG.RankThree.Native Subgroup
open scoped Matrix commutatorElement

theorem card_centralizer_fiveQ_ge {G : Type*} [Group G] [Finite G] {x : G} {v : Fin 4 → G}
    {ω : Fin 4 → Fin 4 → ZMod 5} (h : FiveQRel x v ω) {g : G} (hg : g ∈ fiveQ x v) :
    625 ≤ Nat.card (Subgroup.centralizer ({g} : Set G) ⊓ fiveQ x v : Subgroup G) := by
  have hz : zpowers x ≤ fiveQ x v := Subgroup.zpowers_le.2 FiveQRel.x_mem
  let χ : fiveQ x v →* zpowers x :=
    { toFun := fun q => ⟨⁅(q : G), g⁆, h.comm_mem q.2 hg⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun q q' => Subtype.ext (by
        have hc : Commute ⁅(q' : G), g⁆ (q : G) := h.zpowers_comm (h.comm_mem q'.2 hg) q.2
        have e1 := commutator_mul_left_of_commute hc
        have hc2 : Commute ⁅(q : G), g⁆ ⁅(q' : G), g⁆ :=
          h.zpowers_comm (h.comm_mem q.2 hg) (hz (h.comm_mem q'.2 hg))
        show ⁅(q : G) * q', g⁆ = ⁅(q : G), g⁆ * ⁅(q' : G), g⁆
        rw [e1]
        exact hc2.symm.eq) }
  have hker : Nat.card χ.ker = Nat.card (Subgroup.centralizer ({g} : Set G) ⊓ fiveQ x v : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun q => ⟨(q.1 : G), Subgroup.mem_inf.mpr ⟨?_, q.1.2⟩⟩
        invFun := fun r => ⟨⟨r.1, (Subgroup.mem_inf.mp r.2).2⟩, ?_⟩
        left_inv := fun q => rfl
        right_inv := fun r => rfl }
    · have hq := q.2
      rw [MonoidHom.mem_ker] at hq
      have := congrArg Subtype.val hq
      simp only [OneMemClass.coe_one] at this
      rw [Subgroup.mem_centralizer_singleton_iff]
      obtain ⟨q0, hq0⟩ : ∃ q0 : G, q0 = (q.1 : G) := ⟨_, rfl⟩
      have h1 : q0 * g * q0⁻¹ * g⁻¹ = 1 := by rw [hq0]; exact this
      rw [← hq0]
      calc q0 * g = (q0 * g * q0⁻¹ * g⁻¹) * (g * q0) := by group
        _ = g * q0 := by rw [h1, one_mul]
    · rw [MonoidHom.mem_ker]
      apply Subtype.ext
      have := Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp r.2).1
      show ⁅r.1, g⁆ = 1
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact this
  have hrange : Nat.card χ.range ≤ 5 := by
    calc Nat.card χ.range ≤ Nat.card (zpowers x) := Subgroup.card_le_card_group _
      _ = 5 := by rw [Nat.card_zpowers, h.orderOf_x]
  have hprod := Subgroup.card_ker_mul_card_range χ
  rw [h.card_fiveQ] at hprod
  rw [← hker]
  by_contra hlt
  have hlt' := lt_of_not_ge hlt
  nlinarith [hprod, hrange, hlt']

@[expose] def uvec (u : List ℕ) : Fin 4 → ZMod 5 := fun j => ((u.getD j.val 0 : ℕ) : ZMod 5)

@[expose] def dEl {G : Type*} [Group G] (x : G) (v : Fin 4 → G) (a b : G)
    (d : List ℤ × ℕ × List ℕ) : G :=
  fiveWord a b d.1 * fiveNF x v ((d.2.1 : ℕ) : ZMod 5) (uvec d.2.2)

@[expose] def rhoMat (Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5)) (d : List ℤ × ℕ × List ℕ) :
    Matrix (Fin 4) (Fin 4) (ZMod 5) :=
  (d.1.map fun l => if l = 1 then Ab else Bb).prod

theorem fiveWord_mem_sub {G : Type*} [Group G] {M : Subgroup G} {a b : G} (ha : a ∈ M)
    (hb : b ∈ M) (w : List ℤ) : fiveWord a b w ∈ M := by
  apply Subgroup.list_prod_mem
  intro g hg
  obtain ⟨z, -, rfl⟩ := List.mem_map.1 hg
  split_ifs
  · exact ha
  · exact hb
  · exact M.inv_mem ha
  · exact M.inv_mem hb

theorem rho_fiveWord {G : Type*} [Group G] {a b : G} {M : Subgroup G} (ha : a ∈ M) (hb : b ∈ M)
    (ρ : M →* GL (Fin 4) (ZMod 5)) (Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5))
    (hρA : ∀ g : M, (g : G) = a → (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 5)) = Ab)
    (hρB : ∀ g : M, (g : G) = b → (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 5)) = Bb)
    (w : List ℤ) (hw : ∀ l ∈ w, l = 1 ∨ l = 2) :
    (ρ ⟨fiveWord a b w, fiveWord_mem_sub ha hb w⟩ : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      (w.map fun l => if l = 1 then Ab else Bb).prod := by
  induction w with
  | nil =>
    have : (⟨fiveWord a b [], fiveWord_mem_sub ha hb []⟩ : M) = 1 := rfl
    rw [this, map_one]
    simp
  | cons l w ih =>
    have hl := hw l (List.mem_cons_self)
    have hw' : ∀ l' ∈ w, l' = 1 ∨ l' = 2 := fun l' hl' => hw l' (List.mem_cons_of_mem _ hl')
    have hmem : fiveWord a b (l :: w) = (if l = 1 then a else b) * fiveWord a b w := by
      rcases hl with rfl | rfl <;> simp [fiveWord, List.prod_cons]
    have e : (⟨fiveWord a b (l :: w), fiveWord_mem_sub ha hb (l :: w)⟩ : M) =
        ⟨if l = 1 then a else b, by split_ifs <;> assumption⟩ *
          ⟨fiveWord a b w, fiveWord_mem_sub ha hb w⟩ := Subtype.ext hmem
    rw [e, map_mul, Units.val_mul, ih hw']
    rcases hl with rfl | rfl
    · simp only [↓reduceIte, List.map_cons, List.prod_cons]
      rw [hρA ⟨a, ha⟩ rfl]
    · simp only [show ¬ ((2 : ℤ) = 1) by decide, ↓reduceIte, List.map_cons, List.prod_cons]
      rw [hρB ⟨b, hb⟩ rfl]

theorem y_core {G : Type*} [Group G] [Finite G] {x : G} {v : Fin 4 → G}
    {ω : Fin 4 → Fin 4 → ZMod 5} (hQ : FiveQRel x v ω) {a b : G} (M : Subgroup G)
    (ha : a ∈ M) (hb : b ∈ M)
    (hQM : fiveQ x v ≤ M) (hQN : ((fiveQ x v).subgroupOf M).Normal)
    (φ : fiveQ x v →* Multiplicative (Fin 4 → ZMod 5))
    (hφ : ∀ (c : ZMod 5) (e : Fin 4 → ZMod 5) (q : fiveQ x v), (q : G) = fiveNF x v c e →
      φ q = Multiplicative.ofAdd e)
    (ρ : M →* GL (Fin 4) (ZMod 5)) (Ab Bb : Matrix (Fin 4) (Fin 4) (ZMod 5))
    (hρ : ∀ (g : M) (q q' : fiveQ x v), (q' : G) = g * q * (g : G)⁻¹ →
        φ q' = Multiplicative.ofAdd ((ρ g : Matrix (Fin 4) (Fin 4) (ZMod 5)) *ᵥ
          Multiplicative.toAdd (φ q)))
    (hρA : ∀ g : M, (g : G) = a → (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 5)) = Ab)
    (hρB : ∀ g : M, (g : G) = b → (ρ g : Matrix (Fin 4) (Fin 4) (ZMod 5)) = Bb)
    (hρker : ρ.ker = (fiveQ x v).subgroupOf M)
    (hcomm : ∀ d ∈ dLifts, dEl x v a b d * (v 0 * v 1) = (v 0 * v 1) * dEl x v a b d)
    (hcommu : ∀ u ∈ uVecs, fiveNF x v 0 (uvec u) * (v 0 * v 1) =
      (v 0 * v 1) * fiveNF x v 0 (uvec u))
    (hlet : ∀ d ∈ dLifts, ∀ l ∈ d.1, l = 1 ∨ l = 2)
    (hD : dLifts.toFinset.card = 6)
    (hdist : ∀ d ∈ dLifts, ∀ d' ∈ dLifts, rhoMat Ab Bb d = rhoMat Ab Bb d' → d = d')
    (hfix : ∀ d ∈ dLifts, (∀ u ∈ uVecs, rhoMat Ab Bb d *ᵥ uvec u = uvec u) →
      rhoMat Ab Bb d = 1)
    (hle : Nat.card (Subgroup.centralizer ({v 0 * v 1} : Set G)) ≤ 3750) :
    Subgroup.centralizer ({v 0 * v 1} : Set G) ≤ M ∧
      Nat.card (Subgroup.centralizer ({v 0 * v 1} : Set G)) = 3750 ∧ FiveCoreAt' (v 0 * v 1) := by
  classical
  set y : G := v 0 * v 1 with hy
  have hyQ : y ∈ fiveQ x v :=
    Subgroup.mul_mem _ (FiveQRel.v_mem (x := x) (v := v) 0) (FiveQRel.v_mem (x := x) (v := v) 1)
  have h625 := card_centralizer_fiveQ_ge hQ hyQ
  have hρ1 : ∀ (q : G) (hqQ : q ∈ fiveQ x v) (hqM : q ∈ M), ρ ⟨q, hqM⟩ = 1 := by
    intro q hqQ hqM
    have : (⟨q, hqM⟩ : M) ∈ ρ.ker := by
      rw [hρker]; exact Subgroup.mem_subgroupOf.mpr hqQ
    exact MonoidHom.mem_ker.mp this
  have hdM : ∀ d, dEl x v a b d ∈ M := fun d =>
    M.mul_mem (fiveWord_mem_sub ha hb d.1) (hQM (FiveQRel.nf_mem _ _))
  have hrd : ∀ d ∈ dLifts, (ρ ⟨dEl x v a b d, hdM d⟩ : Matrix (Fin 4) (Fin 4) (ZMod 5)) =
      rhoMat Ab Bb d := by
    intro d hd
    have e : (⟨dEl x v a b d, hdM d⟩ : M) =
        ⟨fiveWord a b d.1, fiveWord_mem_sub ha hb d.1⟩ *
          ⟨fiveNF x v ((d.2.1 : ℕ) : ZMod 5) (uvec d.2.2), hQM (FiveQRel.nf_mem _ _)⟩ :=
      Subtype.ext rfl
    rw [e, map_mul, hρ1 _ (FiveQRel.nf_mem _ _) _, mul_one,
      rho_fiveWord ha hb ρ Ab Bb hρA hρB d.1 (hlet d hd)]
    rfl
  let D : Finset (List ℤ × ℕ × List ℕ) := dLifts.toFinset
  let Φ : (↥D × ↥(Subgroup.centralizer ({y} : Set G) ⊓ fiveQ x v : Subgroup G)) →
      ↥(Subgroup.centralizer ({y} : Set G) ⊓ M : Subgroup G) := fun p =>
    ⟨p.2.1 * dEl x v a b p.1.1, by
      have hd : p.1.1 ∈ dLifts := List.mem_toFinset.mp p.1.2
      obtain ⟨hrC, hrQ⟩ := Subgroup.mem_inf.mp p.2.2
      exact Subgroup.mem_inf.mpr ⟨Subgroup.mul_mem _ hrC
        (Subgroup.mem_centralizer_singleton_iff.mpr (hcomm _ hd)), M.mul_mem (hQM hrQ) (hdM _)⟩⟩
  have hΦinj : Function.Injective Φ := by
    rintro ⟨⟨d, hd⟩, ⟨r, hr⟩⟩ ⟨⟨d', hd'⟩, ⟨r', hr'⟩⟩ h
    have h1 : r * dEl x v a b d = r' * dEl x v a b d' := congrArg Subtype.val h
    have hdL : d ∈ dLifts := List.mem_toFinset.mp hd
    have hdL' : d' ∈ dLifts := List.mem_toFinset.mp hd'
    have hrQ := (Subgroup.mem_inf.mp hr).2
    have hr'Q := (Subgroup.mem_inf.mp hr').2
    have hρeq : ρ (⟨r, hQM hrQ⟩ * ⟨dEl x v a b d, hdM d⟩) =
        ρ (⟨r', hQM hr'Q⟩ * ⟨dEl x v a b d', hdM d'⟩) := congrArg ρ (Subtype.ext h1)
    rw [map_mul, map_mul, hρ1 r hrQ (hQM hrQ), hρ1 r' hr'Q (hQM hr'Q), one_mul, one_mul] at hρeq
    have hmat : rhoMat Ab Bb d = rhoMat Ab Bb d' := by
      rw [← hrd d hdL, ← hrd d' hdL', hρeq]
    have hdd : d = d' := hdist d hdL d' hdL' hmat
    subst hdd
    have hrr : r = r' := mul_right_cancel h1
    subst hrr
    rfl
  have hcardP : Nat.card (↥D × ↥(Subgroup.centralizer ({y} : Set G) ⊓ fiveQ x v : Subgroup G)) =
      6 * Nat.card (Subgroup.centralizer ({y} : Set G) ⊓ fiveQ x v : Subgroup G) := by
    rw [Nat.card_prod, Nat.card_eq_fintype_card (α := ↥D), Fintype.card_coe]
    rw [show D.card = 6 from hD]
  have hle1 := Nat.card_le_card_of_injective Φ hΦinj
  rw [hcardP] at hle1
  have hCM : Nat.card (Subgroup.centralizer ({y} : Set G) ⊓ M : Subgroup G) ≤
      Nat.card (Subgroup.centralizer ({y} : Set G)) := Subgroup.card_le_of_le inf_le_left
  have hCQ : Nat.card (Subgroup.centralizer ({y} : Set G) ⊓ fiveQ x v : Subgroup G) = 625 := by
    omega
  have hCMcard : Nat.card (Subgroup.centralizer ({y} : Set G) ⊓ M : Subgroup G) = 3750 := by
    omega
  have hCeq : Subgroup.centralizer ({y} : Set G) ⊓ M = Subgroup.centralizer ({y} : Set G) :=
    Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  have hCleM : ∀ g ∈ Subgroup.centralizer ({y} : Set G), g ∈ M := fun g hg => by
    have : g ∈ Subgroup.centralizer ({y} : Set G) ⊓ M := by rw [hCeq]; exact hg
    exact (Subgroup.mem_inf.mp this).2
  have hΦbij : Function.Bijective Φ :=
    hΦinj.bijective_of_nat_card_le (by rw [hcardP, hCQ, hCMcard])
  have hCcard : Nat.card (Subgroup.centralizer ({y} : Set G)) = 3750 := by
    rw [← hCeq]; exact hCMcard
  refine ⟨fun g hg => hCleM g hg, hCcard, Subgroup.centralizer ({y} : Set G) ⊓ fiveQ x v,
    inf_le_left, ?_, ?_, ?_⟩
  ·
    intro g hg f hf
    obtain ⟨hfC, hfQ⟩ := Subgroup.mem_inf.mp hf
    have hgM := hCleM g hg
    have hQ' : g * f * g⁻¹ ∈ fiveQ x v := by
      have := hQN.conj_mem ⟨f, hQM hfQ⟩ (Subgroup.mem_subgroupOf.mpr hfQ) ⟨g, hgM⟩
      exact Subgroup.mem_subgroupOf.mp this
    refine Subgroup.mem_inf.mpr ⟨?_, hQ'⟩
    have hgc : Commute g y := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hfc : Commute f y := Subgroup.mem_centralizer_singleton_iff.mp hfC
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((Commute.mul_left (Commute.mul_left hgc hfc) hgc.inv_left).eq)
  · have hQcard : IsPGroup 5 (fiveQ x v) :=
      IsPGroup.of_card (n := 5) (by rw [hQ.card_fiveQ]; norm_num)
    exact hQcard.to_le inf_le_right
  ·
    intro g hg hgc
    have hgM := hCleM g hg
    have hgCM : g ∈ Subgroup.centralizer ({y} : Set G) ⊓ M := Subgroup.mem_inf.mpr ⟨hg, hgM⟩
    obtain ⟨⟨⟨d, hd⟩, ⟨r, hr⟩⟩, hΦg⟩ := hΦbij.2 ⟨g, hgCM⟩
    have hgeq : r * dEl x v a b d = g := congrArg Subtype.val hΦg
    have hdL : d ∈ dLifts := List.mem_toFinset.mp hd
    have hrQ := (Subgroup.mem_inf.mp hr).2
    have hρg : (ρ ⟨g, hgM⟩ : Matrix (Fin 4) (Fin 4) (ZMod 5)) = rhoMat Ab Bb d := by
      have e : (⟨g, hgM⟩ : M) = ⟨r, hQM hrQ⟩ * ⟨dEl x v a b d, hdM d⟩ := Subtype.ext hgeq.symm
      rw [e, map_mul, hρ1 r hrQ (hQM hrQ), one_mul]
      exact hrd d hdL
    have hfixu : ∀ u ∈ uVecs, rhoMat Ab Bb d *ᵥ uvec u = uvec u := by
      intro u hu
      have hfQ : fiveNF x v 0 (uvec u) ∈ fiveQ x v := FiveQRel.nf_mem _ _
      have hfC : fiveNF x v 0 (uvec u) ∈ Subgroup.centralizer ({y} : Set G) :=
        Subgroup.mem_centralizer_singleton_iff.mpr (hcommu u hu)
      have hfmem : fiveNF x v 0 (uvec u) ∈ Subgroup.centralizer ({y} : Set G) ⊓ fiveQ x v :=
        Subgroup.mem_inf.mpr ⟨hfC, hfQ⟩
      have hcomm' := hgc _ hfmem
      have hconj : fiveNF x v 0 (uvec u) = g * fiveNF x v 0 (uvec u) * g⁻¹ := by
        rw [hcomm', mul_assoc]; simp
      have := hρ ⟨g, hgM⟩ ⟨_, hfQ⟩ ⟨_, hfQ⟩ hconj
      rw [hφ 0 (uvec u) ⟨_, hfQ⟩ rfl, hρg] at this
      have h2 := Multiplicative.ofAdd.injective this
      exact h2.symm
    have hone := hfix d hdL hfixu
    have hdQ : dEl x v a b d ∈ fiveQ x v := by
      have : (⟨dEl x v a b d, hdM d⟩ : M) ∈ ρ.ker := by
        rw [MonoidHom.mem_ker]
        apply Units.ext
        rw [hrd d hdL, hone]
        rfl
      rw [hρker] at this
      exact Subgroup.mem_subgroupOf.mp this
    have hgQ : g ∈ fiveQ x v := by
      rw [← hgeq]; exact Subgroup.mul_mem _ hrQ hdQ
    exact Subgroup.mem_inf.mpr ⟨hg, hgQ⟩

end CFSG.RankThree.PartOne.LyFive
