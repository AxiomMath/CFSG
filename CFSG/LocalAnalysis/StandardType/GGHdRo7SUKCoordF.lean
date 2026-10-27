module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7SUKCoordE
public import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordModelB

public section

namespace CFSG.StandardType.HdRo7SU

open CFSG.StandardType.HdRo7C
open CFSG.Assembly
open CFSG.StandardType.UCoord

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7SUKCoordAux_centralizer
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  have hspec := hdRo7SUKCoordAux_rowRank_spec hrow
  have hp3 : p = 3 := hspec.1
  have hp : p.Prime := by rw [hp3]; exact Nat.prime_three
  haveI : Fact p.Prime := ⟨hp⟩
  have hSHat : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  have hy1 : y ≠ 1 := hSHat.2.2.1
  have hyp : y ^ p = 1 := hH.1.2.1.2.1.2 y hyBs
  let C := Subgroup.centralizer (K : Set G)
  let T : Subgroup G := Bs ⊓ K
  have hyle : Subgroup.zpowers y ≤ Bs ⊓ C :=
    Subgroup.zpowers_le.mpr (hdRo7SUKCoordAux_axisCentral hH)
  let f : ↥T × ↥(Bs ⊓ C) → ↥Bs :=
    fun q => ⟨(q.1 : G) * (q.2 : G),
      Bs.mul_mem (Subgroup.mem_inf.mp q.1.2).1 (Subgroup.mem_inf.mp q.2.2).1⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨t1, c1⟩ ⟨t2, c2⟩ heq
    have h1 : (t1 : G) * (c1 : G) = (t2 : G) * (c2 : G) := congrArg Subtype.val heq
    have h2 : (t2 : G)⁻¹ * (t1 : G) = (c2 : G) * (c1 : G)⁻¹ := by
      have := congrArg (fun z : G => (t2 : G)⁻¹ * z * (c1 : G)⁻¹) h1
      simpa [mul_assoc] using this
    have hmemT : (t2 : G)⁻¹ * (t1 : G) ∈ T :=
      ⟨Bs.mul_mem (Bs.inv_mem (Subgroup.mem_inf.mp t2.2).1) (Subgroup.mem_inf.mp t1.2).1,
        K.mul_mem (K.inv_mem (Subgroup.mem_inf.mp t2.2).2) (Subgroup.mem_inf.mp t1.2).2⟩
    have hmemC : (t2 : G)⁻¹ * (t1 : G) ∈ C := by
      rw [h2]
      exact (Subgroup.centralizer (K : Set G)).mul_mem (Subgroup.mem_inf.mp c2.2).2
        ((Subgroup.centralizer (K : Set G)).inv_mem (Subgroup.mem_inf.mp c1.2).2)
    have hone : (t2 : G)⁻¹ * (t1 : G) = 1 :=
      hdRo7SUKCoordAux_inf_center_eq_bot hH hRig hrow _ (Subgroup.mem_inf.mp hmemT).1
        (Subgroup.mem_inf.mp hmemT).2 hmemC
    have ht : t1 = t2 := by
      apply Subtype.ext
      have := congrArg (fun z : G => (t2 : G) * z) hone
      simpa [mul_assoc] using this
    have hc : c2 = c1 := by
      apply Subtype.ext
      have h2' : (c2 : G) * (c1 : G)⁻¹ = 1 := by rw [← h2]; exact hone
      have := congrArg (fun z : G => z * (c1 : G)) h2'
      simpa [mul_assoc] using this
    exact Prod.ext ht hc.symm
  have hf_surj : Function.Surjective f := by
    rintro ⟨b, hb⟩
    obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SUKCoordAux_split hH hRig hrow b hb
    exact ⟨(⟨t, ht⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩
  have hcard : Nat.card ↥Bs = Nat.card ↥T * Nat.card ↥(Bs ⊓ C) := by
    rw [← Nat.card_prod]
    exact (Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩)).symm
  have hTu : Nat.card ↥T = p ^ (hdRo7SUKCoordAux_rowRank hrow - 1) :=
    hdRo7SUKCoordAux_torusLower hH hRig hrow
  have hupper : Nat.card ↥Bs ≤ p ^ (hdRo7SUKCoordAux_rowRank hrow) :=
    hdRo7SUKCoordAux_rankUpper hH hRig hrow
  have h7 : 7 ≤ hdRo7SUKCoordAux_rowRank hrow := (hdRo7SUKCoordAux_rowRank_spec hrow).2.1
  have hleC : Nat.card ↥(Bs ⊓ C) ≤ p := by
    have hpos : 0 < Nat.card ↥T := Nat.card_pos
    have hle : Nat.card ↥T * Nat.card ↥(Bs ⊓ C) ≤ Nat.card ↥T * p := by
      rw [← hcard]
      calc Nat.card ↥Bs ≤ p ^ (hdRo7SUKCoordAux_rowRank hrow) := hupper
        _ = p ^ (hdRo7SUKCoordAux_rowRank hrow - 1) * p := by
              conv_lhs => rw [show hdRo7SUKCoordAux_rowRank hrow =
                (hdRo7SUKCoordAux_rowRank hrow - 1) + 1 by omega]
              rw [pow_succ]
        _ = Nat.card ↥T * p := by rw [hTu]
    exact Nat.le_of_mul_le_mul_left hle hpos
  have hgeC : p ≤ Nat.card ↥(Bs ⊓ C) := by
    have hmono : Nat.card ↥(Subgroup.zpowers y) ≤ Nat.card ↥(Bs ⊓ C) :=
      Nat.card_le_card_of_injective (Subgroup.inclusion hyle)
        (Subgroup.inclusion_injective hyle)
    rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1, hp3] at hmono
    rw [hp3]
    exact hmono
  have hC : Nat.card ↥(Bs ⊓ C) = p := le_antisymm hleC hgeC
  have hzy : Nat.card ↥(Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers, orderOf_eq_prime hyp hy1]
  exact (Subgroup.eq_of_le_of_card_ge hyle (by rw [hC, hzy])).symm

@[expose] noncomputable def hdRo7SUKCoordAux_axisEquiv
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    Multiplicative (ZMod p) ≃* ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) := by
  have hspec := hdRo7SUKCoordAux_rowRank_spec hrow
  have hp3 : p = 3 := hspec.1
  have hp : Nat.Prime p := by rw [hp3]; exact Nat.prime_three
  haveI : Fact p.Prime := ⟨hp⟩
  have hSHat : LargeEvenSHat p B y K := hH.2.2.2.2.1.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 hSHat.2.1
  have hy1 : y ≠ 1 := hSHat.2.2.1
  have hyp : y ^ p = 1 := hH.1.2.1.2.1.2 y hyBs
  have hCeq := hdRo7SUKCoordAux_centralizer hH hRig hrow
  let g : ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
    ⟨y, by rw [hCeq]; exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩⟩
  have hgp : g ^ p = 1 := Subtype.ext (by simpa using hyp)
  have hgpG : (g : G) ^ p = 1 := congrArg Subtype.val hgp
  have hgne : g ≠ 1 := fun h => hy1 (Subtype.ext_iff.mp h)
  have hordg : orderOf g = p := orderOf_eq_prime hgp hgne
  let f : Multiplicative (ZMod p) →* ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) :=
    MonoidHom.mk' (fun a => g ^ (Multiplicative.toAdd a).val) (by
      intro a b
      apply Subtype.ext
      show (g : G) ^ (Multiplicative.toAdd a + Multiplicative.toAdd b).val =
        (g : G) ^ (Multiplicative.toAdd a).val * (g : G) ^ (Multiplicative.toAdd b).val
      rw [ZMod.val_add, ← pow_eq_pow_mod (n := p) (a := (g : G))
        ((Multiplicative.toAdd a).val + (Multiplicative.toAdd b).val) hgpG, ← pow_add])
  have hfa : ∀ a : Multiplicative (ZMod p), f a = g ^ (Multiplicative.toAdd a).val := fun _ => rfl
  have hf1 : f (Multiplicative.ofAdd (1 : ZMod p)) = g := by
    rw [hfa]
    haveI : Fact (1 < p) := ⟨hp.one_lt⟩
    have : (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = 1 := by
      simp [ZMod.val_one p]
    rw [this, pow_one]
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : f (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : g ^ (Multiplicative.toAdd (a * b⁻¹)).val = 1 := h1
    have h3 : (Multiplicative.toAdd (a * b⁻¹)).val = 0 := by
      have hdvd : orderOf g ∣ (Multiplicative.toAdd (a * b⁻¹)).val :=
        orderOf_dvd_iff_pow_eq_one.mpr h2
      rw [hordg] at hdvd
      exact Nat.eq_zero_of_dvd_of_lt hdvd (ZMod.val_lt _)
    have h4 : Multiplicative.toAdd (a * b⁻¹) = 0 := (ZMod.val_eq_zero _).mp h3
    have h5 : Multiplicative.toAdd a + -Multiplicative.toAdd b = 0 := by simpa using h4
    have h6 : Multiplicative.toAdd a = Multiplicative.toAdd b := by
      have := add_eq_zero_iff_eq_neg.mp h5
      simpa using this
    exact Multiplicative.toAdd.injective h6
  have hcard_dom : Nat.card (Multiplicative (ZMod p)) = p := by
    rw [Nat.card_congr (Multiplicative.toAdd (α := ZMod p)), Nat.card_zmod]
  have hcard_cod : Nat.card ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) = p := by
    rw [hCeq, Nat.card_zpowers, orderOf_eq_prime hyp hy1]
  exact MulEquiv.ofBijective f
    ((Nat.bijective_iff_injective_and_card f).mpr ⟨hinj, by rw [hcard_cod, hcard_dom]⟩)

theorem hdRo7SUKCoordAux_axisEquiv_apply_one
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    (hdRo7SUKCoordAux_axisEquiv hH hRig hrow) (Multiplicative.ofAdd (1 : ZMod p)) =
      (⟨y, by
        rw [hdRo7SUKCoordAux_centralizer hH hRig hrow]
        exact Subgroup.mem_zpowers_iff.mpr ⟨1, by simp⟩⟩ :
        ↥(Bs ⊓ Subgroup.centralizer (K : Set G))) := by
  have hspec := hdRo7SUKCoordAux_rowRank_spec hrow
  have hp3 : p = 3 := hspec.1
  unfold hdRo7SUKCoordAux_axisEquiv
  simp only [MulEquiv.ofBijective_apply, MonoidHom.mk'_apply]
  rw [show (Multiplicative.toAdd (Multiplicative.ofAdd (1 : ZMod p))).val = 1 by
    haveI : Fact (1 < p) := ⟨by rw [hp3]; norm_num⟩
    simp [ZMod.val_one p]]
  rw [pow_one]

@[expose] noncomputable def hdRo7SUKCoordAux_prodEquiv
    {G : Type} [Group G] [Finite G]
    {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hRig : GGLabelRigidInput)
    (hrow : GGResRowAt ggRowSUCorank2 p J K) :
    ↥(Bs ⊓ K) × ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) ≃* ↥Bs := by
  let f : ↥(Bs ⊓ K) × ↥(Bs ⊓ Subgroup.centralizer (K : Set G)) →* ↥Bs :=
    MonoidHom.mk' (fun q => ⟨(q.1 : G) * (q.2 : G),
      Bs.mul_mem (Subgroup.mem_inf.mp q.1.2).1 (Subgroup.mem_inf.mp q.2.2).1⟩) (by
      intro q r
      apply Subtype.ext
      show ((q.1 : G) * (r.1 : G)) * ((q.2 : G) * (r.2 : G)) =
        ((q.1 : G) * (q.2 : G)) * ((r.1 : G) * (r.2 : G))
      have h : (r.1 : G) * (q.2 : G) = (q.2 : G) * (r.1 : G) :=
        Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp q.2.2).2 (r.1 : G)
          (Subgroup.mem_inf.mp r.1.2).2
      calc ((q.1 : G) * (r.1 : G)) * ((q.2 : G) * (r.2 : G))
          = (q.1 : G) * ((r.1 : G) * (q.2 : G)) * (r.2 : G) := by group
        _ = (q.1 : G) * ((q.2 : G) * (r.1 : G)) * (r.2 : G) := by rw [h]
        _ = ((q.1 : G) * (q.2 : G)) * ((r.1 : G) * (r.2 : G)) := by group)
  refine MulEquiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨q1, q2⟩ ⟨r1, r2⟩ h
    have h' : (q1 : G) * (q2 : G) = (r1 : G) * (r2 : G) := congrArg Subtype.val h
    have hmemT : (r1 : G)⁻¹ * (q1 : G) ∈ Bs ⊓ K :=
      ⟨Bs.mul_mem (Bs.inv_mem (Subgroup.mem_inf.mp r1.2).1) (Subgroup.mem_inf.mp q1.2).1,
        K.mul_mem (K.inv_mem (Subgroup.mem_inf.mp r1.2).2) (Subgroup.mem_inf.mp q1.2).2⟩
    have hmemC : (r1 : G)⁻¹ * (q1 : G) ∈ Subgroup.centralizer (K : Set G) := by
      have h2 : (r1 : G)⁻¹ * (q1 : G) = (r2 : G) * (q2 : G)⁻¹ := by
        have h3 : (q1 : G) * (q2 : G) * (q2 : G)⁻¹ = (r1 : G) * (r2 : G) * (q2 : G)⁻¹ := by
          rw [h']
        rw [mul_inv_cancel_right] at h3
        rw [h3]
        group
      rw [h2]
      exact (Subgroup.centralizer (K : Set G)).mul_mem (Subgroup.mem_inf.mp r2.2).2
        ((Subgroup.centralizer (K : Set G)).inv_mem (Subgroup.mem_inf.mp q2.2).2)
    have hz1 : (r1 : G)⁻¹ * (q1 : G) = 1 :=
      hdRo7SUKCoordAux_inf_center_eq_bot hH hRig hrow _ (Subgroup.mem_inf.mp hmemT).1
        (Subgroup.mem_inf.mp hmemT).2 hmemC
    have hq1 : q1 = r1 := by
      have h4 : (r1 : G) * ((r1 : G)⁻¹ * (q1 : G)) = (r1 : G) * 1 := by rw [hz1]
      rw [mul_inv_cancel_left, mul_one] at h4
      exact Subtype.ext h4
    have hq2 : q2 = r2 := by
      have h5 : (q1 : G) * (q2 : G) = (q1 : G) * (r2 : G) := by rw [h', ← hq1]
      exact Subtype.ext (mul_left_cancel h5)
    exact Prod.ext hq1 hq2
  · intro b
    obtain ⟨t, ht, c, hc, hbc⟩ := hdRo7SUKCoordAux_split hH hRig hrow b b.2
    exact ⟨(⟨t, ht⟩, ⟨c, hc⟩), Subtype.ext hbc.symm⟩

end CFSG.StandardType.HdRo7SU

end
