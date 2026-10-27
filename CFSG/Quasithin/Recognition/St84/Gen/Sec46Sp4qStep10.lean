module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4qCore

import CFSG.Quasithin.Recognition.St84.Sec6QQuot
import CFSG.CGT.Timmesfeld75.NodeAux

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement Pointwise

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

structure CaseBStep8 (X : Setup Γ G) : Prop where
  n_eq : X.n 0 = X.n 1
  sec : ∀ i : ℤ, i = 0 ∨ i = 1 → IsElemSec (centerOf (X.L i)) (X.Z i)
  nat : ∀ i : ℤ, i = 0 ∨ i = 1 → NatQuot (X.L i) (X.Z i) (centerOf (X.L i)) (X.n i)
  inf_Q : ∀ i : ℤ, i = 0 ∨ i = 1 →
    X.Z i ⊓ X.Q (1 - i) = relCent (X.Z i) (centerOf (X.L i)) X.S

variable {X : Setup Γ G}

theorem odd_card_Ki (X : Setup Γ G) (i : ℤ) (hn : 1 ≤ X.n i) : Odd (Nat.card (X.Ki i)) := by
  rw [X.card_Ki i]
  have h : 1 ≤ 2 ^ X.n i := Nat.one_le_two_pow
  exact Nat.Even.sub_odd h (Nat.even_pow.mpr ⟨even_two, by omega⟩) odd_one

theorem Ki_ne_bot (X : Setup Γ G) (i : ℤ) (hn : 2 ≤ X.n i) : X.Ki i ≠ ⊥ := by
  intro h
  have hc := X.card_Ki i
  rw [h, Subgroup.card_bot] at hc
  have h4 : 4 ≤ 2 ^ X.n i := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ X.n i := Nat.pow_le_pow_right (by norm_num) hn
  omega

private theorem s46sp4q_D_le_Q_of_smul (B : X.CaseBGen) (h8 : X.CaseBStep8) {i o : ℤ}
    (hi : i = 0 ∨ i = 1) {g : G} (hg : g ∈ X.L i) (hgo : g • X.vert o = X.vert (1 - i)) :
    X.Q i ⊓ Subgroup.centralizer (X.Ki i : Set G) ≤ X.Q o := by
  set K' := conjSub g (X.Ki i) with hK'
  have hK'L : K' ≤ X.L i := by
    intro k hk
    have h := mem_conjSub.mp hk
    have : k = g * (g⁻¹ * k * g) * g⁻¹ := by group
    rw [this]
    exact mul_mem (mul_mem hg (Subgroup.mem_inf.mp h).2) (inv_mem hg)
  have hK'G : K' ≤ X.Gi (1 - i) := by
    intro k hk
    have h := mem_conjSub.mp hk
    have hko : (g⁻¹ * k * g) • X.vert o = X.vert o :=
      X.K_le_Gi o (Subgroup.mem_inf.mp h).1
    change k • X.vert (1 - i) = X.vert (1 - i)
    rw [← hgo]
    have : k * g = g * (g⁻¹ * k * g) := by group
    rw [← mul_smul, this, mul_smul, hko]
  have hcard : Nat.card K' = Nat.card (X.Ki i) :=
    Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective
  have hodd : Odd (Nat.card K') := by
    rw [hcard]
    exact X.odd_card_Ki i (by have := B.two_le_n i; omega)
  have hne : K' ≠ ⊥ := fun h => X.Ki_ne_bot i (B.two_le_n i) ((conjSub_eq_bot_iff g).mp h)
  have hle := B.cent_le_Q hi h8.n_eq (h8.nat i hi) (h8.inf_Q i hi) hK'L hK'G hodd hne
  intro x hx
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hgx : g * x * g⁻¹ ∈ X.Q i ⊓ Subgroup.centralizer (K' : Set G) := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact (Subgroup.mem_normalizer_iff.mp
        ((X.Gi_le_normalizer_L_Q_Z i).2.1 (X.L_le_Gi i hg)) x).mp hxQ
    · rw [Subgroup.mem_centralizer_iff]
      intro k hk
      have hk' := mem_conjSub.mp hk
      have hc : (g⁻¹ * k * g) * x = x * (g⁻¹ * k * g) :=
        Subgroup.mem_centralizer_iff.mp hxC _ hk'
      calc k * (g * x * g⁻¹) = g * ((g⁻¹ * k * g) * x) * g⁻¹ := by group
        _ = g * (x * (g⁻¹ * k * g)) * g⁻¹ := by rw [hc]
        _ = g * x * g⁻¹ * k := by group
  have hgxQ := hle hgx
  have hQo : X.Q o = conjSub g⁻¹ (X.Q (1 - i)) := by
    refine X.Q_smul X ?_
    rw [← hgo, ← mul_smul, inv_mul_cancel, one_smul]
  rw [hQo, mem_conjSub, inv_inv]
  exact hgxQ

theorem CaseBGen.D_le_Q_adj (B : X.CaseBGen) (h8 : X.CaseBStep8) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    X.Q i ⊓ Subgroup.centralizer (X.Ki i : Set G) ≤ X.Q (i - 1) ⊓ X.Q (i + 1) := by
  have hj := B.cent_le_Q hi h8.n_eq (h8.nat i hi) (h8.inf_Q i hi) (inf_le_right : X.Ki i ≤ _)
    (inf_le_left.trans (X.K_le_Gi (1 - i))) (X.odd_card_Ki i (by have := B.two_le_n i; omega))
    (X.Ki_ne_bot i (B.two_le_n i))
  have hN := (X.hyp.isLocL2_oTwoPrime (X.vert i)).trans
  have hpred : Γ.Adj (X.vert i) (X.vert (i - 1)) := X.toTrack.adj_pred i
  have hsucc : Γ.Adj (X.vert i) (X.vert (i + 1)) := X.adj i
  rcases hi with rfl | rfl
  · obtain ⟨g, hg, hgo⟩ := hN _ _ hpred hsucc
    have ho := s46sp4q_D_le_Q_of_smul B h8 (i := 0) (o := 0 - 1) (Or.inl rfl) hg
      (by simpa using hgo)
    exact le_inf ho (by simpa using hj)
  · obtain ⟨g, hg, hgo⟩ := hN _ _ hsucc hpred
    have ho := s46sp4q_D_le_Q_of_smul B h8 (i := 1) (o := 1 + 1) (Or.inr rfl) hg
      (by simpa using hgo)
    exact le_inf (by simpa using hj) ho

private theorem s46sp4q_isElemAbelian_of_sq {D : Subgroup G} (hsq : ∀ x ∈ D, x ^ 2 = 1) :
    IsElemAbelian 2 D := by
  have hinv : ∀ x ∈ D, x⁻¹ = x := fun x hx =>
    inv_eq_of_mul_eq_one_right (by rw [← sq]; exact hsq x hx)
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, hsq⟩
  show (a : G) * b = b * a
  calc (a : G) * b = ((b : G) * a)⁻¹ := by
        rw [mul_inv_rev, hinv a a.2, hinv b b.2]
    _ = b * a := hinv _ (mul_mem b.2 a.2)

theorem CaseBGen.D_elem (B : X.CaseBGen) (h8 : X.CaseBStep8) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    IsElemAbelian 2 (X.Q i ⊓ Subgroup.centralizer (X.Ki i : Set G)) := by
  have hadj := B.D_le_Q_adj h8 hi
  refine s46sp4q_isElemAbelian_of_sq fun x hx => ?_
  have hx2 : x ^ 2 ∈ X.Q i ⊓ Subgroup.centralizer (X.Ki i : Set G) := pow_mem hx 2
  have hQi : x ^ 2 ∈ X.Q i := (Subgroup.mem_inf.mp hx2).1
  have hadj2 := Subgroup.mem_inf.mp (hadj hx2)
  have hbot : X.Q (-1) ⊓ X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2 = ⊥ := B.inf_bot
  rcases hi with rfl | rfl
  · have hx1 : x ∈ X.Q 1 := by simpa using (Subgroup.mem_inf.mp (hadj hx)).2
    have hS : X.edgeSylow 1 ≤ X.L (1 + 1) := (X.isSylowTwoOf_edgeSylow_L_succ 1).1
    have h2 : x ^ 2 ∈ X.Q (1 + 1) := X.sq_mem_Q_of_relIndex hS
      (X.relIndex_Q_succ_edgeSylow 1) x (X.Q_le_edgeSylow_left 1 hx1)
    have hmem : x ^ 2 ∈ X.Q (-1) ⊓ X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2 := by
      simp only [Subgroup.mem_inf]
      exact ⟨⟨⟨by simpa using hadj2.1, hQi⟩, by simpa using hadj2.2⟩, by simpa using h2⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem
  · have hx0 : x ∈ X.Q (-1 + 1) := by simpa using (Subgroup.mem_inf.mp (hadj hx)).1
    have hS : X.edgeSylow (-1) ≤ X.L (-1) := (X.isSylowTwoOf_edgeSylow_L (-1)).1
    have h2 : x ^ 2 ∈ X.Q (-1) := X.sq_mem_Q_of_relIndex hS
      (X.relIndex_Q_edgeSylow (-1)) x (X.Q_le_edgeSylow (-1) hx0)
    have hmem : x ^ 2 ∈ X.Q (-1) ⊓ X.Q 0 ⊓ X.Q 1 ⊓ X.Q 2 := by
      simp only [Subgroup.mem_inf]
      exact ⟨⟨⟨h2, by simpa using hadj2.1⟩, hQi⟩, by simpa using hadj2.2⟩
    rw [hbot] at hmem
    exact Subgroup.mem_bot.mp hmem

theorem CaseBGen.Q_comm (B : X.CaseBGen) (h8 : X.CaseBStep8) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    ∀ x ∈ X.Q i, ∀ y ∈ X.Q i, x * y = y * x := by
  have hD := B.D_elem h8 hi
  have hodd := X.odd_card_Ki i (by have := B.two_le_n i; omega)
  have hZc : ∀ z ∈ X.Z i, ∀ w ∈ X.Q i, z * w = w * z := fun z hz w hw =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center i hz)).2 w hw).symm
  intro x hx y hy
  obtain ⟨c, hc, z, hz, rfl⟩ := B.exists_mul_of_odd hi (inf_le_right : X.Ki i ≤ _) hodd hx
  obtain ⟨c', hc', z', hz', rfl⟩ := B.exists_mul_of_odd hi (inf_le_right : X.Ki i ≤ _) hodd hy
  have h1 : z * c' = c' * z := hZc z hz c' (Subgroup.mem_inf.mp hc').1
  have h2 : z' * c = c * z' := hZc z' hz' c (Subgroup.mem_inf.mp hc).1
  have h3 : c * c' = c' * c := (CFSG.CGT.Timmesfeld75.commute_of_isElemAbelian hD hc hc').eq
  have h4 : z * z' = z' * z := hZc z hz z' (X.Z_le_Q i hz')
  calc c * z * (c' * z') = c * (z * c') * z' := by group
    _ = c * (c' * z) * z' := by rw [h1]
    _ = (c * c') * (z * z') := by group
    _ = (c' * c) * (z' * z) := by rw [h3, h4]
    _ = c' * (c * z') * z := by group
    _ = c' * (z' * c) * z := by rw [h2]
    _ = c' * z' * (c * z) := by group

theorem CaseBGen.inf_le_centerOf_S (B : X.CaseBGen) (h8 : X.CaseBStep8) :
    X.Q 0 ⊓ X.Q 1 ≤ centerOf X.S := by
  have hcomm0 := B.Q_comm h8 (Or.inl rfl)
  have hcomm1 := B.Q_comm h8 (Or.inr rfl)
  have hQ0N : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.Q_le_S (Or.inl rfl)).trans ((X.isSylowTwoOf_S_Gi (Or.inr rfl)).1.trans
      (X.Gi_le_normalizer_L_Q_Z 1).2.1)
  intro a ha
  obtain ⟨ha0, ha1⟩ := Subgroup.mem_inf.mp ha
  refine Subgroup.mem_inf.mpr ⟨X.Q_le_S (Or.inl rfl) ha0, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right (X.Q 0) (X.Q 1) hQ0N
  have hs' : s ∈ ((X.Q 0 ⊔ X.Q 1 : Subgroup G) : Set G) := by
    rw [B.Q_sup_Q]
    exact hs
  rw [hcoe] at hs'
  obtain ⟨u, hu, v, hv, rfl⟩ := hs'
  calc u * v * a = u * (v * a) := mul_assoc _ _ _
    _ = u * (a * v) := by rw [hcomm1 v hv a ha1]
    _ = u * a * v := (mul_assoc _ _ _).symm
    _ = a * u * v := by rw [hcomm0 u hu a ha0]
    _ = a * (u * v) := mul_assoc _ _ _

theorem CaseBGen.Q_eq_Z (B : X.CaseBGen) (h8 : X.CaseBStep8) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    X.Q i = X.Z i ∧
      centerOf (X.L i) = X.Q i ⊓ Subgroup.centralizer (X.Ki i : Set G) ∧
      Nat.card (centerOf (X.L i)) = 2 ^ X.n i := by
  have hodd := X.odd_card_Ki i (by have := B.two_le_n i; omega)
  have hne := X.Ki_ne_bot i (B.two_le_n i)
  have hnat := h8.nat i hi
  have hadj := B.D_le_Q_adj h8 hi
  have hD01 : X.Q i ⊓ Subgroup.centralizer (X.Ki i : Set G) ≤ X.Q 0 ⊓ X.Q 1 := by
    intro x hx
    have h := Subgroup.mem_inf.mp (hadj hx)
    have hxQ := (Subgroup.mem_inf.mp hx).1
    rcases hi with rfl | rfl
    · exact Subgroup.mem_inf.mpr ⟨hxQ, by simpa using h.2⟩
    · exact Subgroup.mem_inf.mpr ⟨by simpa using h.1, hxQ⟩
  have hDZ : X.Q i ⊓ Subgroup.centralizer (X.Ki i : Set G) ≤ X.Z i :=
    (hD01.trans (B.inf_le_centerOf_S h8)).trans
      (X.centerOf_sylow_le_Z B.char i (X.isSylowTwoOf_S_Gi hi)).1
  have hDcen : X.Q i ⊓ Subgroup.centralizer (X.Ki i : Set G) = centerOf (X.L i) := by
    refine le_antisymm ?_ ?_
    · rw [← B.inf_centralizer_eq hnat (inf_le_right : X.Ki i ≤ _) hodd hne]
      exact le_inf hDZ inf_le_right
    · intro z hz
      refine Subgroup.mem_inf.mpr ⟨X.Z_le_Q i (X.centerOf_L_le_Z B.char i hz), ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro k hk
      exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 k
        (Subgroup.mem_inf.mp hk).2
  refine ⟨le_antisymm (fun x hx => ?_) (X.Z_le_Q i), hDcen.symm, ?_⟩
  · obtain ⟨c, hc, z, hz, rfl⟩ := B.exists_mul_of_odd hi (inf_le_right : X.Ki i ≤ _) hodd hx
    exact mul_mem (hDZ hc) hz
  · rw [← hDcen]
    exact B.card_cent hi h8.n_eq hnat (inf_le_right : X.Ki i ≤ _) hodd hne

end Setup

end CFSG.Quasithin.St84

end
