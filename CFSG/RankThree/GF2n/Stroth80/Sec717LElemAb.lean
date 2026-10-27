module

public import CFSG.RankThree.GF2n.Stroth80.Sec717ZNProof

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

section Squares

variable {G : Type} [Group G]

@[expose] def sec717SqSub (N Z0 : Subgroup G) (hcomm : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Z0)
    (hZ : ∀ x ∈ N, ∀ z ∈ Z0, x * z * x⁻¹ ∈ Z0) : Subgroup G where
  carrier := {x | x ∈ N ∧ x * x ∈ Z0}
  mul_mem' := by
    rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
    refine ⟨N.mul_mem hx hy, ?_⟩
    have c : ⁅y, x⁆ ∈ Z0 := hcomm y hy x hx
    have key : x * y * (x * y) = (x * ⁅y, x⁆ * x⁻¹) * (x * x) * (y * y) := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact Z0.mul_mem (Z0.mul_mem (hZ x hx _ c) hx2) hy2
  one_mem' := ⟨N.one_mem, by rw [mul_one]; exact Z0.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hx2⟩
    refine ⟨N.inv_mem hx, ?_⟩
    have h := Z0.inv_mem hx2
    rw [mul_inv_rev] at h
    exact h

@[expose] def sec717SqQ (L Q : Subgroup G) (hLc : ∀ a ∈ L, ∀ b ∈ L, ⁅a, b⁆ ∈ Q)
    (hQn : ∀ x ∈ L, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q) : Subgroup G where
  carrier := {x | x ∈ L ∧ x * x ∈ Q}
  mul_mem' := by
    rintro x y ⟨hx, hx2⟩ ⟨hy, hy2⟩
    refine ⟨L.mul_mem hx hy, ?_⟩
    have c : ⁅y, x⁆ ∈ Q := hLc y hy x hx
    have key : x * y * (x * y) = (x * ⁅y, x⁆ * x⁻¹) * (x * x) * (y * y) := by
      simp only [commutatorElement_def]
      group
    rw [key]
    exact Q.mul_mem (Q.mul_mem (hQn x hx _ c) hx2) hy2
  one_mem' := ⟨L.one_mem, by rw [mul_one]; exact Q.one_mem⟩
  inv_mem' := by
    rintro x ⟨hx, hx2⟩
    refine ⟨L.inv_mem hx, ?_⟩
    have h := Q.inv_mem hx2
    rw [mul_inv_rev] at h
    exact h

theorem sec717_sq_mem_of_sup {N Z0 A₁ A₂ : Subgroup G} (hcomm : ∀ a ∈ N, ∀ b ∈ N, ⁅a, b⁆ ∈ Z0)
    (hZ : ∀ x ∈ N, ∀ z ∈ Z0, x * z * x⁻¹ ∈ Z0) (hsup : A₁ ⊔ A₂ = N)
    (hA₁N : A₁ ≤ N) (hA₂N : A₂ ≤ N) (hA₁ : ∀ a ∈ A₁, a * a ∈ Z0)
    (hA₂ : ∀ a ∈ A₂, a * a ∈ Z0) : ∀ x ∈ N, x * x ∈ Z0 := by
  have hle : A₁ ⊔ A₂ ≤ sec717SqSub N Z0 hcomm hZ := by
    refine sup_le ?_ ?_
    · intro a ha
      exact ⟨hA₁N ha, hA₁ a ha⟩
    · intro a ha
      exact ⟨hA₂N ha, hA₂ a ha⟩
  intro x hx
  exact ((le_of_eq hsup.symm).trans hle hx).2

end Squares

theorem sec717L_sq_mem_Q (h51 : Stroth51Statement)
    (hA : Sec7AExistsStatement) (hPts : Sec5NatPointsOmegaStatement)
    (hCN : Sec7CommNStatement) (hCM : Sec7CentreMpStatement) (hZc : Sec7ZCardStatement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} [(Q.subgroupOf M).Normal]
    (hc : Ctx M Q Z B) {n : ℕ} {t : G} (hs : Sec7Hyp hc n t) (hp3 : OmegaPlusNat hc t 3)
    {Z0 : Subgroup G} (hZ0 : IsCentrePre Z0 (Rt M (LB M Q B) t) Q) {L : Subgroup G}
    (hL : Sec717L hc t Z0 L) : ∀ x ∈ L, x * x ∈ Q := by
  classical
  unfold Sec717L at hL
  obtain ⟨hQL, hLN, hLcard, hLR, hLc, hZ0L⟩ := hL
  have ht : t ∈ LB M Q B := hs.toSec5.mem
  have hRM : Rt M (LB M Q B) t ≤ M := hc.Rt_le_M t
  have hQnorm : ∀ g ∈ M, ∀ y ∈ Q, g * y * g⁻¹ ∈ Q := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 hg) y).mp hy
  have hZ0n : ∀ g ∈ Rt M (LB M Q B) t, ∀ y ∈ Z0, g * y * g⁻¹ ∈ Z0 := fun g hg y hy =>
    (Subgroup.mem_normalizer_iff.mp
      (hZ0.mem_normalizer (fun ρ hρ y hy => hQnorm ρ (hRM hρ) y hy) hg) y).mp hy
  have hQZ0 : Q ≤ Z0 := fun x hx => (hZ0 x).mpr ⟨hc.Q_le_Rt ht hx, fun r hr => by
    have h1 := hQnorm r (hRM hr) x⁻¹ (Q.inv_mem hx)
    have h2 := Q.mul_mem hx h1
    simpa [commutatorElement_def, mul_assoc] using h2⟩
  have hZN : Z0 ≤ hc.CN t := sec7ctr_Z0_le_CN hc hs hZ0
  have hZ0card : Nat.card Z0 = Nat.card Q * Nat.card Z :=
    hZc G M Q Z B hc n t hs Z0 hZ0
  have hZsq : ∀ z ∈ Z0, z * z ∈ Q := fun z hz => by
    have h1 := hc.sq_mem_Q_of_mem_LB (hCM G M Q Z B hc n t hs Z0 hZ0 z hz).1
    rwa [pow_two] at h1
  obtain ⟨r, hr⟩ := hA G M Q Z B hc n t hs
  obtain ⟨-, hopp, -⟩ := sec7ctr_Z0_data h51 hc hs.toSec5 (Or.inr hs.omegaNat) hr hZ0 hZN
  have hcommN : ∀ a ∈ hc.CN t, ∀ b ∈ hc.CN t, ⁅a, b⁆ ∈ Z0 := fun a ha b hb =>
    hCN G M Q Z B hc n t hs Z0 hZ0 (Subgroup.commutator_mem_commutator ha hb)
  have hZN' : ∀ x ∈ hc.CN t, ∀ z ∈ Z0, x * z * x⁻¹ ∈ Z0 := fun x hx z hz =>
    hZ0n x (Ctx.mem_CN.mp hx).1 z hz
  have hA₁ : ∀ a ∈ LB M Q B ⊓ hc.CN t, a * a ∈ Z0 := fun a ha => by
    have h1 := hc.sq_mem_Q_of_mem_LB (Subgroup.mem_inf.mp ha).1
    rw [pow_two] at h1
    exact hQZ0 h1
  have hLC : LB M Q (conjSubgroup r B) = conjSubgroup r (LB M Q B) :=
    hc.LB_conj (hc.Rt_le_M t hr.mem)
  have hA₂ : ∀ a ∈ LB M Q (conjSubgroup r B) ⊓ hc.CN t, a * a ∈ Z0 := fun a ha => by
    have haC := (Subgroup.mem_inf.mp ha).1
    rw [hLC, mem_conjSubgroup] at haC
    have hy : (r⁻¹ * a * r) * (r⁻¹ * a * r) ∈ Q := by
      have h1 := hc.sq_mem_Q_of_mem_LB haC
      rwa [pow_two] at h1
    have hyy : a * a = r * ((r⁻¹ * a * r) * (r⁻¹ * a * r)) * r⁻¹ := by group
    rw [hyy]
    exact hQZ0 (hQnorm r (hRM hr.mem) _ hy)
  have hsqCN : ∀ x ∈ hc.CN t, x * x ∈ Z0 :=
    sec717_sq_mem_of_sup hcommN hZN' hopp.2.2.2.2.1 inf_le_right inf_le_right hA₁ hA₂
  have hsqL : ∀ x ∈ L, x * x ∈ Z0 := fun x hx => hsqCN x (hLN hx)
  have hLQ : ∀ x ∈ L, ∀ q ∈ Q, x * q * x⁻¹ ∈ Q := fun x hx q hq =>
    hQnorm x (hRM (Ctx.mem_CN.mp (hLN hx)).1) q hq
  set W : Subgroup G := sec717SqQ L Q hLc hLQ with hWdef
  have hWmem : ∀ x, x ∈ W ↔ x ∈ L ∧ x * x ∈ Q := fun x => Iff.rfl
  have hZW : Z0 ≤ W := fun z hz => (hWmem z).mpr ⟨hZ0L hz, hZsq z hz⟩
  have hWL : W ≤ L := fun x hx => ((hWmem x).mp hx).1
  have hWN : W ≤ hc.CN t := fun x hx => hLN (hWL hx)
  have hWR : ∀ r' ∈ Rt M (LB M Q B) t, conjSubgroup r' W = W := by
    apply sec717_conj_eq_of_inv
    intro g hg w hw
    obtain ⟨hwL, hwq⟩ := (hWmem w).mp hw
    refine (hWmem _).mpr ⟨?_, ?_⟩
    · have h1 : g * w * g⁻¹ ∈ conjSubgroup g L := by
        rw [mem_conjSubgroup]
        simpa [mul_assoc] using hwL
      rwa [hLR g hg] at h1
    · have hyy : g * w * g⁻¹ * (g * w * g⁻¹) = g * (w * w) * g⁻¹ := by group
      rw [hyy]
      exact hQnorm g (hRM hg) _ hwq
  obtain ⟨k, hk⟩ := sec717CardDvd_of_omegaPlus h51 hA hPts hc hs (le_refl 3) hp3 hZ0 hZW
    hWN hWR
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hWL' : Nat.card W ≤ Nat.card L := Subgroup.card_le_of_le hWL
  have hLcard' : Nat.card L = Nat.card Z0 * Nat.card Z ^ 4 := by
    rw [hLcard, hZ0card]
    ring
  have hk1 : k ≤ 1 := by
    rw [hk, hLcard'] at hWL'
    have h2 : Nat.card Z ^ (2 ^ (3 - 1) * k) ≤ Nat.card Z ^ 4 :=
      Nat.le_of_mul_le_mul_left hWL' Nat.card_pos
    have h3 : 2 ^ (3 - 1) * k ≤ 4 := (Nat.pow_le_pow_iff_right (by omega)).mp h2
    norm_num at h3
    omega
  obtain rfl | rfl : k = 0 ∨ k = 1 := by omega
  ·
    exfalso
    have hcard : Nat.card W = Nat.card Z0 := by
      rw [hk]
      simp
    have hWZ : W = Z0 := (Subgroup.eq_of_le_of_card_ge hZW (le_of_eq hcard)).symm
    have hZM : ∀ z ∈ Z0, z ∈ M := fun z hz => hRM (Ctx.mem_CN.mp (hZN hz)).1
    haveI hQZn : (Q.subgroupOf Z0).Normal := ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using hQnorm (g : G) (hZM g g.2) _ hn⟩
    have hmul : ∀ x y : ↥L,
        (QuotientGroup.mk ⟨((x : G) * y) * ((x : G) * y), hsqL _ (L.mul_mem x.2 y.2)⟩ :
          Z0 ⧸ Q.subgroupOf Z0) =
          QuotientGroup.mk ⟨(x : G) * x, hsqL x x.2⟩ * QuotientGroup.mk ⟨(y : G) * y, hsqL y y.2⟩
              := by
      intro x y
      have hu : (x : G) * ⁅(y : G), (x : G)⁆ * (x : G)⁻¹ ∈ Q :=
        hLQ x x.2 _ (hLc y y.2 x x.2)
      have huZ : (x : G) * ⁅(y : G), (x : G)⁆ * (x : G)⁻¹ ∈ Z0 := hQZ0 hu
      have e : (⟨((x : G) * y) * ((x : G) * y), hsqL _ (L.mul_mem x.2 y.2)⟩ : Z0) =
          ⟨(x : G) * ⁅(y : G), (x : G)⁆ * (x : G)⁻¹, huZ⟩ * ⟨(x : G) * x, hsqL x x.2⟩ *
            ⟨(y : G) * y, hsqL y y.2⟩ := by
        apply Subtype.ext
        simp only [Subgroup.coe_mul, commutatorElement_def]
        group
      rw [e, QuotientGroup.mk_mul, QuotientGroup.mk_mul]
      have h1 : (QuotientGroup.mk ⟨(x : G) * ⁅(y : G), (x : G)⁆ * (x : G)⁻¹, huZ⟩ :
          Z0 ⧸ Q.subgroupOf Z0) = 1 := by
        rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        exact hu
      rw [h1, one_mul]
    let g : ↥L →* (Z0 ⧸ Q.subgroupOf Z0) :=
      MonoidHom.mk' (fun x => QuotientGroup.mk ⟨(x : G) * x, hsqL x x.2⟩) hmul
    have hker : g.ker = Z0.subgroupOf L := by
      ext x
      rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
      show (QuotientGroup.mk ⟨(x : G) * x, hsqL x x.2⟩ : Z0 ⧸ Q.subgroupOf Z0) = 1 ↔
        (x : G) ∈ Z0
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      constructor
      · intro h
        have hxW : (x : G) ∈ W := (hWmem _).mpr ⟨x.2, h⟩
        rw [hWZ] at hxW
        exact hxW
      · intro hx
        have hxW : (x : G) ∈ W := by
          rw [hWZ]
          exact hx
        exact ((hWmem _).mp hxW).2
    have hkerCard : Nat.card g.ker = Nat.card Z0 := by
      rw [hker]
      exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZ0L).toEquiv
    have hquot : Nat.card (Z0 ⧸ Q.subgroupOf Z0) = Nat.card Z := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (Q.subgroupOf Z0)
      have h2 : Nat.card (Q.subgroupOf Z0) = Nat.card Q :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQZ0).toEquiv
      rw [h2, hZ0card] at h1
      have hpos : 0 < Nat.card Q := Nat.card_pos
      apply Nat.eq_of_mul_eq_mul_right hpos
      rw [← h1]
      ring
    have hrange : Nat.card g.range ≤ Nat.card Z := by
      rw [← hquot]
      exact Subgroup.card_le_card_group (H := g.range)
    have hsplit := Subgroup.card_ker_mul_card_range g
    rw [hkerCard, hLcard, hZ0card] at hsplit
    have hpos : 0 < Nat.card Q := Nat.card_pos
    have hq4' : 4 ≤ Nat.card Z := hq4
    have hbound : Nat.card Q * Nat.card Z ^ 5 ≤ Nat.card Q * Nat.card Z * Nat.card Z := by
      rw [← hsplit]
      exact Nat.mul_le_mul_left _ hrange
    have hbound' : Nat.card Z ^ 5 ≤ Nat.card Z * Nat.card Z := by
      have h' : Nat.card Q * Nat.card Z ^ 5 ≤ Nat.card Q * (Nat.card Z * Nat.card Z) := by
        calc Nat.card Q * Nat.card Z ^ 5 ≤ Nat.card Q * Nat.card Z * Nat.card Z := hbound
          _ = Nat.card Q * (Nat.card Z * Nat.card Z) := by ring
      exact Nat.le_of_mul_le_mul_left h' hpos
    have hlt : Nat.card Z * Nat.card Z < Nat.card Z ^ 5 := by
      have h2 : Nat.card Z * Nat.card Z = Nat.card Z ^ 2 := by ring
      rw [h2]
      exact Nat.pow_lt_pow_right (by omega) (by norm_num)
    omega
  ·
    intro x hx
    have hxW : x ∈ W := by
      have hcard : Nat.card W = Nat.card L := by
        rw [hk, hLcard']
        norm_num
      have heq : W = L := Subgroup.eq_of_le_of_card_ge hWL (le_of_eq hcard.symm)
      rw [heq]
      exact hx
    exact ((hWmem x).mp hxW).2



variable {G : Type} [Group G] {M Q : Subgroup G} [(Q.subgroupOf M).Normal]

theorem sec717_bar_isElemAbelian {L H : Subgroup G} (hLM : L ≤ M)
    (hLc : ∀ a ∈ L, ∀ b ∈ L, ⁅a, b⁆ ∈ Q) (hsq : ∀ a ∈ L, a * a ∈ Q) :
    IsElemAbelian 2 ((bar M Q L).subgroupOf (bar M Q H)) := by
  have rep : ∀ x : ↥(bar M Q H), x ∈ (bar M Q L).subgroupOf (bar M Q H) →
      ∃ s : ↥M, (s : G) ∈ L ∧ QuotientGroup.mk s = (x : ↥M ⧸ Q.subgroupOf M) := by
    intro x hx
    obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hx)
    exact ⟨s, Subgroup.mem_subgroupOf.mp hs, hsx⟩
  have comm_mk : ∀ u v : ↥M ⧸ Q.subgroupOf M, ∀ s s' : ↥M, (s : G) ∈ L → (s' : G) ∈ L →
      u = QuotientGroup.mk s → v = QuotientGroup.mk s' → u * v = v * u := by
    intro u v s s' hs hs' hu hv
    subst hu
    subst hv
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have h := hLc s'⁻¹ (L.inv_mem hs') s⁻¹ (L.inv_mem hs)
    have key : ((s : G) * s')⁻¹ * ((s' : G) * s) = ⁅(s' : G)⁻¹, (s : G)⁻¹⁆ := by
      rw [commutatorElement_def]
      group
    rw [key]
    exact h
  have sq_mk : ∀ u : ↥M ⧸ Q.subgroupOf M, ∀ s : ↥M, (s : G) ∈ L →
      u = QuotientGroup.mk s → u * u = 1 := by
    intro u s hs hu
    subst hu
    rw [← QuotientGroup.mk_mul, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
    simp only [Subgroup.coe_mul]
    exact hsq s hs
  refine ⟨⟨⟨fun a b => ?_⟩⟩, fun x hx => ?_⟩
  · obtain ⟨s, hs, hsa⟩ := rep a a.2
    obtain ⟨s', hs', hsb⟩ := rep b b.2
    apply Subtype.ext
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    exact comm_mk _ _ s s' hs hs' hsa.symm hsb.symm
  · obtain ⟨s, hs, hsx⟩ := rep x hx
    apply Subtype.ext
    simp only [pow_two, Subgroup.coe_mul, Subgroup.coe_one]
    exact sq_mk _ s hs hsx.symm


end CFSG.RankThree.GF2n.Stroth80
