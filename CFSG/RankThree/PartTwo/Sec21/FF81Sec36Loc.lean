module

public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36W
public import CFSG.RankThree.PartTwo.Sec21.FF81Sec36Defs
import CFSG.RankThree.PartTwo.Sec21.FF81Sec43T
import CFSG.RankThree.PartTwo.Sec21.FF81Prop51
import CFSG.RankThree.PartTwo.Sec21.FF81HoltHyp4
import CFSG.RankThree.PartTwo.Sec21.FF81Step0

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79

namespace S36

variable {G : Type} [Group G] [Finite G]

theorem le_op_two_of_normalizes {S Q : Subgroup G} (hQS : Q ≤ S)
    (hN : ∀ s ∈ S, ∀ q ∈ Q, s * q * s⁻¹ ∈ Q) (hp : IsPGroup 2 Q) : Q ≤ Op 2 S := by
  intro q hq
  have hnorm : (Q.subgroupOf S).Normal := ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hN g g.2 n hn⟩
  have hp' : IsPGroup 2 (Q.subgroupOf S) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hQS).symm
  have hle : Q.subgroupOf S ≤ CFSG.pCore 2 ↥S := le_sSup ⟨hnorm, hp'⟩
  exact ⟨⟨q, hQS hq⟩, hle (Subgroup.mem_subgroupOf.mpr hq), rfl⟩

theorem op_two_le' (K : Subgroup G) : Op 2 K ≤ K := Subgroup.map_subtype_le _

theorem isPGroup_op_two (K : Subgroup G) : IsPGroup 2 (Op 2 K) :=
  CFSG.pCore_isPGroup.map K.subtype

theorem conj_mem_op_two_of_mem_nor {K : Subgroup G} {g o : G} (hg : g ∈ Nor K)
    (ho : o ∈ Op 2 K) : g * o * g⁻¹ ∈ Op 2 K := by
  have hON := CFSG.pCore_normal (p := 2) (G := ↥K)
  have hle : conjBy g (Op 2 K) ≤ Op 2 K := by
    refine le_op_two_of_normalizes ?_ ?_ ((isPGroup_op_two K).map _)
    · rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp hg y).mp (op_two_le' K hy)
    · intro s hs q hq
      rw [mem_conjBy_iff] at hq ⊢
      have hs' : g⁻¹ * s * g ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) s).mp hs
        rwa [inv_inv] at this
      have := inSubgroup_conj_mem hON hs' hq
      rw [show g⁻¹ * (s * q * s⁻¹) * g = (g⁻¹ * s * g) * (g⁻¹ * q * g) * (g⁻¹ * s * g)⁻¹ by
        group]
      exact this
  exact hle ⟨o, ho, rfl⟩

theorem mem_cenS_pair {p q y : G} :
    y ∈ CenS (Subgroup.closure {p, q}) ↔ y * p = p * y ∧ y * q = q * y := by
  rw [CenS, Subgroup.centralizer_closure, Subgroup.mem_centralizer_iff]
  constructor
  · intro h
    exact ⟨(h p (by simp)).symm, (h q (by simp)).symm⟩
  · rintro ⟨hp, hq⟩ z (rfl | rfl)
    · exact hp.symm
    · exact hq.symm

theorem commute_conj {g x y : G} (h : x * y = y * x) :
    (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹) := by
  simp only [mul_assoc, inv_mul_cancel_left]
  rw [← mul_assoc x, h, mul_assoc]

theorem commute_of_conj {g x y : G}
    (h : (g * x * g⁻¹) * (g * y * g⁻¹) = (g * y * g⁻¹) * (g * x * g⁻¹)) : x * y = y * x :=
  calc x * y = g⁻¹ * ((g * x * g⁻¹) * (g * y * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * y * g⁻¹) * (g * x * g⁻¹)) * g := by rw [h]
    _ = y * x := by group

theorem commute_conj_inv {g h z : G} (H : h * (g * z * g⁻¹) = (g * z * g⁻¹) * h) :
    (g⁻¹ * h * g) * z = z * (g⁻¹ * h * g) :=
  calc (g⁻¹ * h * g) * z = g⁻¹ * (h * (g * z * g⁻¹)) * g := by group
    _ = g⁻¹ * ((g * z * g⁻¹) * h) * g := by rw [H]
    _ = z * (g⁻¹ * h * g) := by group

theorem orderOf_conj'' (g k : G) : orderOf (g * k * g⁻¹) = orderOf k :=
  orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective k

variable {b : G} {L B : Subgroup G} {b₁ b₂ b₃ : G}

theorem wt3_eq_torWt (x : Fin 3 → ZMod 3) : wt3 x = torWt x := rfl

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.B₁_le (hB : FF81Basis b L B b₁ b₂ b₃) : Subgroup.closure {b₁, b₂, b₃} ≤ L :=
  (Subgroup.closure_le _).mpr (by
    rintro y (rfl | rfl | rfl)
    · exact hB.hb₁
    · exact hB.hb₂
    · exact hB.hb₃)

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.B₁_comm (hB : FF81Basis b L B b₁ b₂ b₃) {β γ : G}
    (hβ : β ∈ Subgroup.closure {b₁, b₂, b₃}) (hγ : γ ∈ Subgroup.closure {b₁, b₂, b₃}) :
    β * γ = γ * β :=
  comm_of_isElemAb hB.elem β hβ γ hγ

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.mem_B₁_of_mem (hB : FF81Basis b L B b₁ b₂ b₃) {z : G} (hzB : z ∈ B)
    (hzL : z ∈ L) : z ∈ Subgroup.closure {b₁, b₂, b₃} := by
  obtain ⟨v, rfl⟩ := ε4_surj hB.mono.1 hB.mono.2.1 hzB
  set x : Fin 3 → ZMod 3 := ![v 1, v 2, v 3]
  have hv : ε4 b b₁ b₂ b₃ v = b ^ (v 0).val * ε3 b₁ b₂ b₃ x := by
    simp only [ε4, ε3, x, mul_assoc]; rfl
  have hεL : ε3 b₁ b₂ b₃ x ∈ L := hB.B₁_le (ε3_mem x)
  have hbL : b ^ (v 0).val ∈ L := by
    have := L.mul_mem hzL (L.inv_mem hεL)
    rwa [hv, mul_inv_cancel_right] at this
  have hbC : b ^ (v 0).val ∈ CenS L := Subgroup.pow_mem _ (Subgroup.mem_centralizer_iff.mpr
    fun y hy => Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hy)) _
  have h1 : b ^ (v 0).val = 1 := by
    have hmem : b ^ (v 0).val ∈ L ⊓ CenS L := Subgroup.mem_inf.mpr ⟨hbL, hbC⟩
    rwa [hB.inf_cenS_self, Subgroup.mem_bot] at hmem
  rw [hv, h1, one_mul]
  exact ε3_mem x

theorem _root_.CFSG.RankThree.PartTwo.Sec21.FF81.FF81Basis.t₀_mem_nor (hB : FF81Basis b L B b₁ b₂ b₃) {t₀ : G} (ht₀L : t₀ ∈ CenS L)
    (ht₀b : t₀ * b * t₀⁻¹ = b⁻¹) : t₀ ∈ Nor B := by
  rw [hB.mono.2.1]
  refine Subgroup.mem_normalizer_fintype fun y hy => conj_mem_of_closure (fun w hw => ?_) hy
  have hfix : ∀ c ∈ L, t₀ * c * t₀⁻¹ = c := fun c hc => by
    rw [(Subgroup.mem_centralizer_iff.mp ht₀L c hc).symm, mul_inv_cancel_right]
  rcases hw with rfl | rfl | rfl | rfl
  · rw [ht₀b]; exact Subgroup.inv_mem _ (Subgroup.subset_closure (by simp))
  · rw [hfix _ hB.hb₁]; exact Subgroup.subset_closure (by simp)
  · rw [hfix _ hB.hb₂]; exact Subgroup.subset_closure (by simp)
  · rw [hfix _ hB.hb₃]; exact Subgroup.subset_closure (by simp)

theorem local_bound (hKF : KF_Sp6RefS)
    (hB : FF81Basis b L B b₁ b₂ b₃) (hbad : CaseBad b B) {t₀ : G} (ht₀ : orderOf t₀ = 2)
    (ht₀L : t₀ ∈ CenS L) (ht₀b : t₀ * b * t₀⁻¹ = b⁻¹) (i : Fin 13) :
    (hypW i = 1 → Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) ≤ 2) ∧
    (hypW i = 2 → Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) ≤ 8 ∧
      (∀ u ∈ Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i), ∀ v ∈ Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i),
        u * v = v * u) ∧
      ∃ S₂ : Subgroup G, IsPGroup 2 S₂ ∧ Nat.card S₂ = 8 ∧ S₂ ≤ CenS (hyp b₁ b₂ b₃ i) ⊓ Cen t₀ ∧
        Subgroup.closure {b₁, b₂, b₃} ≤ Nor S₂) ∧
    (hypW i = 3 → Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) ≤ 8 ∧
      (Nat.card ↥(Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i)) = 8 →
        ∃ u ∈ Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i),
          ∃ v ∈ Op 2 (Cen t₀) ⊓ CenS (hyp b₁ b₂ b₃ i), u * v ≠ v * u)) := by
  obtain ⟨g, hg, x, hx0, hwx, hgu, ⟨t, hgl⟩, t', y, hyind, hgl'⟩ := geom hB hbad i
  set u := hypU i with hu
  set a := hypA i with ha
  set T := Op 2 (Cen t₀) with hT
  set A := hyp b₁ b₂ b₃ i with hA
  set B₁ : Subgroup G := Subgroup.closure {b₁, b₂, b₃} with hB₁
  set s := g * t₀ * g⁻¹ with hs
  set w := g * ε3 b₁ b₂ b₃ u * g⁻¹ with hw
  have hβL : ∀ β ∈ B₁, β ∈ L := fun β hβ => hB.B₁_le hβ
  have ht₀β : ∀ β ∈ B₁, t₀ * β = β * t₀ := fun β hβ =>
    (Subgroup.mem_centralizer_iff.mp ht₀L β (hβL β hβ)).symm
  have huA : ε3 b₁ b₂ b₃ u ∈ A := Subgroup.subset_closure (Set.mem_insert _ _)
  have haA : ε3 b₁ b₂ b₃ (a + t • u) ∈ A := by
    rw [hB.ε3_add, hB.ε3_smul]
    exact A.mul_mem (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) (A.pow_mem huA _)
  have hcenA : ∀ z : G, z * ε3 b₁ b₂ b₃ u = ε3 b₁ b₂ b₃ u * z →
      z * ε3 b₁ b₂ b₃ (a + t • u) = ε3 b₁ b₂ b₃ (a + t • u) * z → z ∈ CenS A := by
    intro z h1 h2
    rw [hA, hyp, mem_cenS_pair]
    refine ⟨h1, ?_⟩
    have he : ε3 b₁ b₂ b₃ a = ε3 b₁ b₂ b₃ (a + t • u) * (ε3 b₁ b₂ b₃ u ^ t.val)⁻¹ := by
      rw [hB.ε3_add, hB.ε3_smul, mul_inv_cancel_right]
    have h1' : z * (ε3 b₁ b₂ b₃ u ^ t.val)⁻¹ = (ε3 b₁ b₂ b₃ u ^ t.val)⁻¹ * z :=
      ((Commute.pow_right h1 t.val).inv_right).eq
    rw [he, ← mul_assoc, h2, mul_assoc, h1', mul_assoc]
  have hcomA : ∀ z ∈ CenS A, ∀ β ∈ A, z * β = β * z := fun z hz β hβ =>
    (Subgroup.mem_centralizer_iff.mp hz β hβ).symm
  have hcen_b : ∀ z : G, z * w = w * z → z * b = b * z := by
    intro z hz
    rcases hgu with h | h
    · rw [← h]; exact hz
    · have : b = w⁻¹ := by rw [h, inv_inv]
      rw [this]; exact (Commute.inv_right hz).eq
  have hcen_w : ∀ z : G, z * b = b * z → z * w = w * z := by
    intro z hz
    rcases hgu with h | h
    · rw [h]; exact hz
    · rw [h]; exact (Commute.inv_right hz).eq
  have hs2 : orderOf s = 2 := by rw [hs, orderOf_conj'', ht₀]
  have hsw : s * w = w * s := commute_conj (ht₀β _ (ε3_mem u))
  have hsb : s * b = b * s := hcen_b s hsw
  have hsl : s * ε3 b₁ b₂ b₃ x = ε3 b₁ b₂ b₃ x * s := by rw [← hgl]; exact commute_conj (ht₀β _ (ε3_mem _))
  have hsl' : s * ε3 b₁ b₂ b₃ y = ε3 b₁ b₂ b₃ y * s := by
    rw [← hgl']; exact commute_conj (ht₀β _ (ε3_mem _))
  have hsL : s ∈ L := by
    refine hB.mem_of_pow_two (Subgroup.mem_centralizer_singleton_iff.mpr hsb) (k := 1) ?_
    rw [pow_one, ← hs2]; exact pow_orderOf_eq_one s
  have hsNB : s ∈ Nor B := Subgroup.mul_mem _ (Subgroup.mul_mem _ hg
    (hB.t₀_mem_nor ht₀L ht₀b)) (Subgroup.inv_mem _ hg)
  have hsN : s ∈ Nor B₁ := by
    refine Subgroup.mem_normalizer_fintype fun β hβ => ?_
    have hβB : β ∈ B := by
      rw [hB.mono.2.1]; exact Subgroup.closure_mono (Set.subset_insert _ _) hβ
    exact hB.mem_B₁_of_mem ((Subgroup.mem_normalizer_iff.mp hsNB β).mp hβB)
      (L.mul_mem (L.mul_mem hsL (hβL β hβ)) (L.inv_mem hsL))
  obtain ⟨k2, k1, k3⟩ := hKF G L hB.hyp.model b₁ b₂ b₃ hB.hb₁ hB.hb₂ hB.hb₃ hB.elem hB.selfcen
    hB.monoL_stab s hsL hs2 hsN x y hx0 hyind hsl hsl'
  rw [← wt3_eq_torWt] at k1 k2 k3
  change wt3 x = 2 → Nat.card ↥(Op 2 (L ⊓ Cen s ⊓ Cen (ε3 b₁ b₂ b₃ x))) ≤ 2 at k2
  set H := L ⊓ Cen s ⊓ Cen (ε3 b₁ b₂ b₃ x) with hH
  change wt3 x = 1 → Nat.card ↥(Op 2 H) = 8 ∧ (∀ u ∈ Op 2 H, ∀ v ∈ Op 2 H, u * v = v * u) ∧
    ∀ u ∈ Op 2 H, u * u = 1 at k1
  change wt3 x = 3 → Nat.card ↥(Op 2 H) = 8 ∧ ∃ u ∈ Op 2 H, ∃ v ∈ Op 2 H, u * v ≠ v * u at k3
  set C := T ⊓ CenS A with hC
  set R := conjBy g C with hR
  have hCp : IsPGroup 2 C := (op_two_isPGroup t₀).to_le inf_le_left
  have hRp : IsPGroup 2 R := hCp.map _
  have hRmem : ∀ r ∈ R, g⁻¹ * r * g ∈ C := fun r hr => mem_conjBy_iff.mp hr
  have hconjC : ∀ c ∈ C, g * c * g⁻¹ ∈ R := fun c hc => ⟨c, hc, rfl⟩
  have hRb : R ≤ Cen b := by
    intro r hr
    have hc := hRmem r hr
    have h1 : (g⁻¹ * r * g) * ε3 b₁ b₂ b₃ u = ε3 b₁ b₂ b₃ u * (g⁻¹ * r * g) :=
      hcomA _ hc.2 _ huA
    have h2 := commute_conj (g := g) h1
    rw [show g * (g⁻¹ * r * g) * g⁻¹ = r by group] at h2
    exact Subgroup.mem_centralizer_singleton_iff.mpr (hcen_b r h2)
  have hRH : R ≤ H := by
    intro r hr
    have hc := hRmem r hr
    have hr' : g * (g⁻¹ * r * g) * g⁻¹ = r := by group
    refine ⟨⟨hB.le_of_isPGroup hRb hRp hr, ?_⟩, ?_⟩
    · have h1 : (g⁻¹ * r * g) * t₀ = t₀ * (g⁻¹ * r * g) :=
        Subgroup.mem_centralizer_singleton_iff.mp (op_two_le t₀ hc.1)
      have h2 := commute_conj (g := g) h1
      rw [hr'] at h2
      exact Subgroup.mem_centralizer_singleton_iff.mpr h2
    · have h1 := hcomA _ hc.2 _ haA
      have h2 := commute_conj (g := g) h1
      rw [hr', hgl] at h2
      exact Subgroup.mem_centralizer_singleton_iff.mpr h2
  have hRnorm : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R := by
    intro h hh r hr
    obtain ⟨⟨hhL, hhs⟩, hhl⟩ := hh
    have hc := hRmem r hr
    set h' := g⁻¹ * h * g with hh'
    have hh's : h' * t₀ = t₀ * h' :=
      commute_conj_inv (Subgroup.mem_centralizer_singleton_iff.mp hhs)
    have hh'u : h' * ε3 b₁ b₂ b₃ u = ε3 b₁ b₂ b₃ u * h' :=
      commute_conj_inv (hcen_w h (Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hhL)))
    have hh'a : h' * ε3 b₁ b₂ b₃ (a + t • u) = ε3 b₁ b₂ b₃ (a + t • u) * h' := by
      have h1 := Subgroup.mem_centralizer_singleton_iff.mp hhl
      rw [← hgl] at h1
      exact commute_conj_inv h1
    rw [hR, mem_conjBy_iff]
    rw [show g⁻¹ * (h * r * h⁻¹) * g = h' * (g⁻¹ * r * g) * h'⁻¹ by rw [hh']; group]
    set c := g⁻¹ * r * g
    refine ⟨op_two_conj (Subgroup.mem_centralizer_singleton_iff.mpr hh's) hc.1, ?_⟩
    have hcu := hcomA _ hc.2 _ huA
    have hca := hcomA _ hc.2 _ haA
    refine hcenA _ ?_ ?_
    · calc h' * c * h'⁻¹ * ε3 b₁ b₂ b₃ u = h' * c * (h'⁻¹ * ε3 b₁ b₂ b₃ u) := by group
        _ = h' * c * (ε3 b₁ b₂ b₃ u * h'⁻¹) := by rw [(Commute.inv_left hh'u).eq]
        _ = h' * (c * ε3 b₁ b₂ b₃ u) * h'⁻¹ := by group
        _ = h' * (ε3 b₁ b₂ b₃ u * c) * h'⁻¹ := by rw [hcu]
        _ = (h' * ε3 b₁ b₂ b₃ u) * c * h'⁻¹ := by group
        _ = ε3 b₁ b₂ b₃ u * (h' * c * h'⁻¹) := by rw [hh'u]; group
    · calc h' * c * h'⁻¹ * ε3 b₁ b₂ b₃ (a + t • u)
          = h' * c * (h'⁻¹ * ε3 b₁ b₂ b₃ (a + t • u)) := by group
        _ = h' * c * (ε3 b₁ b₂ b₃ (a + t • u) * h'⁻¹) := by rw [(Commute.inv_left hh'a).eq]
        _ = h' * (c * ε3 b₁ b₂ b₃ (a + t • u)) * h'⁻¹ := by group
        _ = h' * (ε3 b₁ b₂ b₃ (a + t • u) * c) * h'⁻¹ := by rw [hca]
        _ = (h' * ε3 b₁ b₂ b₃ (a + t • u)) * c * h'⁻¹ := by group
        _ = ε3 b₁ b₂ b₃ (a + t • u) * (h' * c * h'⁻¹) := by rw [hh'a]; group
  have hRO : R ≤ Op 2 H := le_op_two_of_normalizes hRH hRnorm hRp
  have hcard : Nat.card R = Nat.card C := card_conjBy g C
  have hle : Nat.card C ≤ Nat.card (Op 2 H) := hcard ▸ Subgroup.card_le_of_le hRO
  have hwx' : ∀ w0, hypW i = w0 → wt3 x = φw w0 := fun w0 h => h ▸ hwx
  refine ⟨fun h1 => ?_, fun h2 => ?_, fun h3 => ?_⟩
  · exact hle.trans (k2 (hwx' 1 h1))
  · obtain ⟨c8, cab, -⟩ := k1 (hwx' 2 h2)
    refine ⟨c8 ▸ hle, fun p hp q hq => ?_, ?_⟩
    · exact commute_of_conj (g := g) (cab _ (hRO (hconjC p hp)) _ (hRO (hconjC q hq)))
    · refine ⟨conjBy g⁻¹ (Op 2 H), (isPGroup_op_two H).map _, by rw [card_conjBy, c8], ?_, ?_⟩
      · intro z hz
        rw [mem_conjBy_iff, inv_inv] at hz
        set o := g * z * g⁻¹ with ho
        have hoH := op_two_le' H hz
        obtain ⟨⟨hoL, hos⟩, hol⟩ := hoH
        have hz' : z = g⁻¹ * o * g := by rw [ho]; group
        refine ⟨?_, ?_⟩
        · refine hcenA z ?_ ?_
          · rw [hz']
            exact commute_conj_inv
              (hcen_w o (Subgroup.mem_centralizer_singleton_iff.mp (hB.hyp.hLC hoL)))
          · have h1 := Subgroup.mem_centralizer_singleton_iff.mp hol
            rw [← hgl] at h1
            rw [hz']
            exact commute_conj_inv h1
        · refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
          rw [hz']
          exact commute_conj_inv (Subgroup.mem_centralizer_singleton_iff.mp hos)
      · intro β hβ
        refine mem_nor_conjBy fun o ho => ?_
        rw [inv_inv]
        set γ := g * β * g⁻¹ with hγ
        have hγs : γ * s = s * γ := commute_conj (ht₀β β hβ).symm
        have hγw : γ * w = w * γ := commute_conj (hB.B₁_comm hβ (ε3_mem u))
        have hγl : γ * ε3 b₁ b₂ b₃ x = ε3 b₁ b₂ b₃ x * γ := by
          rw [← hgl]; exact commute_conj (hB.B₁_comm hβ (ε3_mem _))
        have hγb : γ ∈ Cen b := Subgroup.mem_centralizer_singleton_iff.mpr (hcen_b γ hγw)
        have hγN : γ ∈ Nor H := by
          refine Subgroup.mem_normalizer_fintype fun h hh => ?_
          obtain ⟨⟨hhL, hhs⟩, hhl⟩ := hh
          refine ⟨⟨(Subgroup.mem_normalizer_iff.mp (hB.hyp.hLN hγb) h).mp hhL, ?_⟩, ?_⟩
          · exact (Cen s).mul_mem ((Cen s).mul_mem
              (Subgroup.mem_centralizer_singleton_iff.mpr hγs) hhs)
              ((Cen s).inv_mem (Subgroup.mem_centralizer_singleton_iff.mpr hγs))
          · exact (Cen (ε3 b₁ b₂ b₃ x)).mul_mem ((Cen (ε3 b₁ b₂ b₃ x)).mul_mem
              (Subgroup.mem_centralizer_singleton_iff.mpr hγl) hhl)
              ((Cen (ε3 b₁ b₂ b₃ x)).inv_mem (Subgroup.mem_centralizer_singleton_iff.mpr hγl))
        exact conj_mem_op_two_of_mem_nor hγN ho
  · obtain ⟨c8, p, hp, q, hq, hpq⟩ := k3 (hwx' 3 h3)
    refine ⟨c8 ▸ hle, fun hC8 => ?_⟩
    have hReq : R = Op 2 H := Subgroup.eq_of_le_of_card_ge hRO (by rw [hcard, hC8, c8])
    rw [← hReq] at hp hq
    refine ⟨g⁻¹ * p * g, hRmem p hp, g⁻¹ * q * g, hRmem q hq, fun h => hpq ?_⟩
    calc p * q = g * ((g⁻¹ * p * g) * (g⁻¹ * q * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * q * g) * (g⁻¹ * p * g)) * g⁻¹ := by rw [h]
      _ = q * p := by group

end S36

end CFSG.RankThree.PartTwo.Sec21.FF81
