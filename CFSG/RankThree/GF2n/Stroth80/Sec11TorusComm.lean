module

public import CFSG.RankThree.GF2n.Stroth80.Ctx
import CFSG.RankThree.GF2n.Smith81.Lin26Roots
import CFSG.RankThree.GF2n.Smith81.Sec220Conj
import CFSG.RankThree.GF2n.Stroth80.Sec5Comm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem normalizes_of_centralizes {S : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.centralizer (S : Set G)) : y ∈ Subgroup.normalizer (S : Set G) := by
  refine Subgroup.mem_normalizer_fintype fun h hh => ?_
  have e : y * h * y⁻¹ = h := by rw [← Subgroup.mem_centralizer_iff.mp hy h hh]; group
  rw [e]
  exact hh

theorem Ctx.rootSwap (hc : Ctx M Q Z B) : Ctx (Subgroup.normalizer (B : Set G)) (QB B) B Z := by
  obtain ⟨g, hg⟩ := hc.conj
  have hQc : conjSubgroup g Q = QB B := by rw [← Smith81.QB_conj_eq hc.hyp g, hg]
  have hMc : conjSubgroup g M = Subgroup.normalizer (B : Set G) := by
    rw [← Smith81.normalizer_conj_eq hc.hyp g, hg]
  exact
    { hyp := by rw [← hMc, ← hQc, hg]; exact hc.hyp.conj g
      conj := ⟨g⁻¹, by rw [hg, conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one]⟩
      le := (Ctx.Z_le_QB hc).1
      ne := hc.ne.symm }

theorem Ctx.conj_Q_QB_of_swap (hc : Ctx M Q Z B) {n : G} (hZ : conjSubgroup n Z = B)
    (hB : conjSubgroup n B = Z) : conjSubgroup n Q = QB B ∧ conjSubgroup n (QB B) = Q := by
  constructor
  · rw [← QB_Z_eq hc, ← QB_conj, hZ]
  · rw [← QB_conj, hB, QB_Z_eq hc]

theorem Ctx.normalizer_B_le_normalizer_QB (hc : Ctx M Q Z B) :
    Subgroup.normalizer (B : Set G) ≤ Subgroup.normalizer ((QB B : Subgroup G) : Set G) :=
  hc.rootSwap.hyp.Q_normal.2

private theorem comm_PB_ZB (hc : Ctx M Q Z B) {a : G} (ha : a ∈ QB B ⊓ M) :
    ∀ w ∈ Z ⊔ B, a * w = w * a := by
  intro w hw
  obtain ⟨z, hz, b, hb, rfl⟩ := (Smith81.Ctx.mem_sup_iff hc).mp hw
  have h1 : z * a = a * z := Subgroup.mem_centralizer_iff.mp ((Ctx.QB_inf_M_eq hc).le ha).2 z hz
  have h2 : b * a = a * b := Smith81.Ctx.B_central_QB hc hb ha.1
  calc a * (z * b) = (a * z) * b := by group
    _ = z * (a * b) := by rw [← h1]; group
    _ = z * b * a := by rw [← h2]; group

theorem Ctx.comm_Q_PB_mem (hc : Ctx M Q Z B) {x a : G} (hx : x ∈ Q) (ha : a ∈ QB B ⊓ M) :
    ⁅x, a⁆ ∈ Q ⊓ Subgroup.centralizer (B : Set G) := by
  refine ⟨hc.comm_mem_Q ha.2 hx, Subgroup.mem_centralizer_iff.mpr fun b hb => ?_⟩
  have hxb : x⁻¹ * b * x ∈ Z ⊔ B := by
    have hN := Smith81.Ctx.Q_le_normalizer_ZB hc (Q.inv_mem hx)
    have := (Subgroup.mem_normalizer_iff.mp hN b).mp (Subgroup.mem_sup_right hb)
    simpa using this
  have h3 := comm_PB_ZB hc ha _ hxb
  have h4 : x * a * x⁻¹ * b = b * (x * a * x⁻¹) := by
    calc x * a * x⁻¹ * b = x * (a * (x⁻¹ * b * x)) * x⁻¹ := by group
      _ = x * ((x⁻¹ * b * x) * a) * x⁻¹ := by rw [h3]
      _ = b * (x * a * x⁻¹) := by group
  have h5 : a⁻¹ * b = b * a⁻¹ := by
    have h6 : b * a = a * b := Smith81.Ctx.B_central_QB hc hb ha.1
    calc a⁻¹ * b = a⁻¹ * (b * a) * a⁻¹ := by group
      _ = a⁻¹ * (a * b) * a⁻¹ := by rw [h6]
      _ = b * a⁻¹ := by group
  rw [commutatorElement_def]
  calc b * (x * a * x⁻¹ * a⁻¹) = (b * (x * a * x⁻¹)) * a⁻¹ := by group
    _ = x * a * x⁻¹ * (b * a⁻¹) := by rw [← h4]; group
    _ = x * a * x⁻¹ * a⁻¹ * b := by rw [← h5]; group

theorem Ctx.comm_QB_P_mem (hc : Ctx M Q Z B) {u p : G} (hu : u ∈ QB B)
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G)) : ⁅u, p⁆ ∈ QB B ⊓ M := by
  have hp' : p ∈ QB Z ⊓ Subgroup.normalizer (B : Set G) :=
    ⟨by rw [QB_Z_eq hc]; exact hp.1, normalizes_of_centralizes hp.2⟩
  have h := hc.rootSwap.comm_Q_PB_mem hu hp'
  refine ⟨h.1, ?_⟩
  rw [← hc.hyp.normalizer_Z.1]
  exact normalizes_of_centralizes h.2

theorem Ctx.comm_P_PB_mem (hc : Ctx M Q Z B) {p a : G}
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G)) (ha : a ∈ QB B ⊓ M) : ⁅p, a⁆ ∈ Q ⊓ QB B := by
  refine ⟨hc.comm_mem_Q ha.2 hp.1, ?_⟩
  have hpN := hc.normalizer_B_le_normalizer_QB (normalizes_of_centralizes hp.2)
  have h1 : p * a * p⁻¹ ∈ QB B := (Subgroup.mem_normalizer_iff.mp hpN a).mp ha.1
  rw [commutatorElement_def]
  exact (QB B).mul_mem h1 ((QB B).inv_mem ha.1)

theorem Ctx.comm_Q_PB_mul_right (hc : Ctx M Q Z B) {x a a' : G} (hx : x ∈ Q)
    (ha : a ∈ QB B ⊓ M) (ha' : a' ∈ QB B ⊓ M) :
    (⁅x, a⁆ * ⁅x, a'⁆)⁻¹ * ⁅x, a * a'⁆ ∈ QB B := by
  have hn := hc.comm_Q_PB_mem hx ha'
  have hnN := hc.normalizer_B_le_normalizer_QB
    (Subgroup.inv_mem _ (normalizes_of_centralizes hn.2))
  have e : (⁅x, a⁆ * ⁅x, a'⁆)⁻¹ * ⁅x, a * a'⁆ = ⁅x, a'⁆⁻¹ * a * ⁅x, a'⁆⁻¹⁻¹ * a⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact (QB B).mul_mem ((Subgroup.mem_normalizer_iff.mp hnN a).mp ha.1) ((QB B).inv_mem ha.1)

theorem Ctx.comm_Q_PB_congr_right (hc : Ctx M Q Z B) {x a a' : G} (hx : x ∈ Q)
    (ha : a ∈ QB B ⊓ M) (ha' : a' ∈ QB B ⊓ M) (h : a⁻¹ * a' ∈ Q) :
    ⁅x, a⁆⁻¹ * ⁅x, a'⁆ ∈ QB B := by
  have hd : a⁻¹ * a' ∈ QB B ⊓ M :=
    ⟨(QB B).mul_mem ((QB B).inv_mem ha.1) ha'.1, M.mul_mem (M.inv_mem ha.2) ha'.2⟩
  have h1 := hc.comm_Q_PB_mul_right hx ha hd
  have h2 : ⁅x, a⁻¹ * a'⁆ ∈ QB B := (Ctx.Z_le_QB hc).1 (Smith81.comm_mem_Z hc.hyp hx h)
  rw [show a * (a⁻¹ * a') = a' by group] at h1
  have e : ⁅x, a⁆⁻¹ * ⁅x, a'⁆ = ⁅x, a⁻¹ * a'⁆ * ((⁅x, a⁆ * ⁅x, a⁻¹ * a'⁆)⁻¹ * ⁅x, a'⁆) := by
    group
  rw [e]
  exact (QB B).mul_mem h2 h1

theorem Ctx.comm_Q_PB_mul_left (hc : Ctx M Q Z B) {x x' a : G} (hx : x ∈ Q) (hx' : x' ∈ Q)
    (ha : a ∈ QB B ⊓ M) : (⁅x, a⁆ * ⁅x', a⁆)⁻¹ * ⁅x * x', a⁆ ∈ Z := by
  have hA : ⁅x, a⁆ ∈ Q := (hc.comm_Q_PB_mem hx ha).1
  have hC : ⁅x', a⁆ ∈ Q := (hc.comm_Q_PB_mem hx' ha).1
  have h1 : ⁅x, ⁅x', a⁆⁆ ∈ Z := Smith81.comm_mem_Z hc.hyp hx hC
  have h2 : ⁅⁅x', a⁆⁻¹, ⁅x, a⁆⁻¹⁆ ∈ Z :=
    Smith81.comm_mem_Z hc.hyp (Q.inv_mem hC) (Q.inv_mem hA)
  have h3 : ⁅x, ⁅x', a⁆⁆ * (⁅x', a⁆ * ⁅x, a⁆) = (⁅x', a⁆ * ⁅x, a⁆) * ⁅x, ⁅x', a⁆⁆ :=
    Smith81.Z_central hc.hyp h1 (Q.mul_mem hC hA)
  have e : (⁅x, a⁆ * ⁅x', a⁆)⁻¹ * ⁅x * x', a⁆ =
      (⁅x, a⁆ * ⁅x', a⁆)⁻¹ * (⁅x, ⁅x', a⁆⁆ * (⁅x', a⁆ * ⁅x, a⁆)) := by
    simp only [commutatorElement_def]
    group
  have e' : (⁅x, a⁆ * ⁅x', a⁆)⁻¹ * (⁅x', a⁆ * ⁅x, a⁆ * ⁅x, ⁅x', a⁆⁆) =
      ⁅⁅x', a⁆⁻¹, ⁅x, a⁆⁻¹⁆ * ⁅x, ⁅x', a⁆⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, h3, e']
  exact Z.mul_mem h2 h1

theorem Ctx.comm_Q_PB_congr_left (hc : Ctx M Q Z B) {x x' a : G} (hx : x ∈ Q) (hx' : x' ∈ Q)
    (hxx : x⁻¹ * x' ∈ Subgroup.centralizer (B : Set G)) (ha : a ∈ QB B ⊓ M) :
    ⁅x, a⁆⁻¹ * ⁅x', a⁆ ∈ QB B := by
  have hp : x⁻¹ * x' ∈ Q ⊓ Subgroup.centralizer (B : Set G) := ⟨Q.mul_mem (Q.inv_mem hx) hx', hxx⟩
  have h1 := hc.comm_Q_PB_mul_left hx hp.1 ha
  have h2 : ⁅x⁻¹ * x', a⁆ ∈ QB B := (hc.comm_P_PB_mem hp ha).2
  rw [show x * (x⁻¹ * x') = x' by group] at h1
  have e : ⁅x, a⁆⁻¹ * ⁅x', a⁆ = ⁅x⁻¹ * x', a⁆ * ((⁅x, a⁆ * ⁅x⁻¹ * x', a⁆)⁻¹ * ⁅x', a⁆) := by
    group
  rw [e]
  exact (QB B).mul_mem h2 ((Ctx.Z_le_QB hc).1 h1)

private theorem mem_swap_PB (hc : Ctx M Q Z B) {p : G}
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    p ∈ QB Z ⊓ Subgroup.normalizer (B : Set G) :=
  ⟨by rw [QB_Z_eq hc]; exact hp.1, normalizes_of_centralizes hp.2⟩

theorem Ctx.comm_QB_P_mul_right (hc : Ctx M Q Z B) {u p p' : G} (hu : u ∈ QB B)
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G))
    (hp' : p' ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    (⁅u, p⁆ * ⁅u, p'⁆)⁻¹ * ⁅u, p * p'⁆ ∈ Q := by
  have h := hc.rootSwap.comm_Q_PB_mul_right hu (mem_swap_PB hc hp) (mem_swap_PB hc hp')
  rwa [QB_Z_eq hc] at h

theorem Ctx.comm_QB_P_congr_right (hc : Ctx M Q Z B) {u p p' : G} (hu : u ∈ QB B)
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G))
    (hp' : p' ∈ Q ⊓ Subgroup.centralizer (B : Set G)) (h : p⁻¹ * p' ∈ QB B) :
    ⁅u, p⁆⁻¹ * ⁅u, p'⁆ ∈ Q := by
  have h' := hc.rootSwap.comm_Q_PB_congr_right hu (mem_swap_PB hc hp) (mem_swap_PB hc hp') h
  rwa [QB_Z_eq hc] at h'

theorem Ctx.comm_QB_P_congr_left (hc : Ctx M Q Z B) {u u' p : G} (hu : u ∈ QB B)
    (hu' : u' ∈ QB B) (huu : u⁻¹ * u' ∈ Subgroup.centralizer (Z : Set G))
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G)) : ⁅u, p⁆⁻¹ * ⁅u', p⁆ ∈ Q := by
  have h := hc.rootSwap.comm_Q_PB_congr_left hu hu' huu (mem_swap_PB hc hp)
  rwa [QB_Z_eq hc] at h

theorem Ctx.weylQ_conj_P (hc : Ctx M Q Z B) {x u p : G} (hx : x ∈ Q) (hu : u ∈ QB B)
    (hp : p ∈ Q ⊓ Subgroup.centralizer (B : Set G)) :
    ⁅u, p⁆⁻¹ * (x * u * x * p * (x * u * x)⁻¹) ∈ Q := by
  have hm := hc.comm_QB_P_mem hu hp
  have hz : ⁅x, p⁆ ∈ Z ⊔ B := Subgroup.mem_sup_left (Smith81.comm_mem_Z hc.hyp hx hp.1)
  have hZBQ : Z ⊔ B ≤ Q := sup_le hc.Z_le_Q hc.le
  have h1 : u * ⁅x, p⁆ * u⁻¹ ∈ Q :=
    hZBQ ((Subgroup.mem_normalizer_iff.mp (Smith81.Ctx.QB_le_normalizer_ZB hc hu) _).mp hz)
  have h2 : x * (u * ⁅x, p⁆ * u⁻¹) * x⁻¹ * ⁅x, ⁅u, p⁆⁆ ∈ Q :=
    Q.mul_mem (Q.mul_mem (Q.mul_mem hx h1) (Q.inv_mem hx)) (hc.comm_mem_Q hm.2 hx)
  have h3 : ⁅u, p⁆⁻¹ * (x * (u * ⁅x, p⁆ * u⁻¹) * x⁻¹ * ⁅x, ⁅u, p⁆⁆) * ⁅u, p⁆ ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem hm.2)) _).mp h2
    simpa using this
  have e : ⁅u, p⁆⁻¹ * (x * u * x * p * (x * u * x)⁻¹) =
      (⁅u, p⁆⁻¹ * (x * (u * ⁅x, p⁆ * u⁻¹) * x⁻¹ * ⁅x, ⁅u, p⁆⁆) * ⁅u, p⁆) * (x * p * x⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Q.mul_mem h3 (Q.mul_mem (Q.mul_mem hx hp.1) (Q.inv_mem hx))

theorem Ctx.weylQB_conj_PB (hc : Ctx M Q Z B) {x u a : G} (hx : x ∈ Q) (hu : u ∈ QB B)
    (ha : a ∈ QB B ⊓ M) : ⁅x, a⁆⁻¹ * (u * x * u * a * (u * x * u)⁻¹) ∈ QB B := by
  have ha' : a ∈ QB B ⊓ Subgroup.centralizer (Z : Set G) := (Ctx.QB_inf_M_eq hc).le ha
  exact hc.rootSwap.weylQ_conj_P hu (by rw [QB_Z_eq hc]; exact hx) ha'

theorem Ctx.weylQ_comm_comm_PB (hc : Ctx M Q Z B) {x u a : G} (hx : x ∈ Q) (hu : u ∈ QB B)
    (ha : a ∈ QB B ⊓ M) (hw : x * u * x * a * (x * u * x)⁻¹ ∈ Q) : ⁅u, ⁅x, a⁆⁆ * a ∈ Q := by
  have hn := hc.comm_Q_PB_mem hx ha
  have hm := hc.comm_QB_P_mem hu hn
  have hb : ⁅u, a⁆ ∈ Q := hc.le (Smith81.Ctx.QB_comm_mem hc hu ha.1)
  have hq₁ : ⁅x, ⁅u, ⁅x, a⁆⁆⁆ ∈ Q := hc.comm_mem_Q hm.2 hx
  have hq₂ : ⁅x, ⁅x, a⁆⁆ * ⁅x, a⁆ * ⁅x, ⁅u, a⁆⁆ * ⁅u, a⁆ * ⁅x, a⁆ ∈ Q := by
    have h1 : ⁅x, ⁅x, a⁆⁆ ∈ Q := hc.Z_le_Q (Smith81.comm_mem_Z hc.hyp hx hn.1)
    have h2 : ⁅x, ⁅u, a⁆⁆ ∈ Q := hc.Z_le_Q (Smith81.comm_mem_Z hc.hyp hx hb)
    exact Q.mul_mem (Q.mul_mem (Q.mul_mem (Q.mul_mem h1 hn.1) h2) hb) hn.1
  have hq₃ : a⁻¹ * (⁅x, ⁅x, a⁆⁆ * ⁅x, a⁆ * ⁅x, ⁅u, a⁆⁆ * ⁅u, a⁆ * ⁅x, a⁆)⁻¹ * a ∈ Q := by
    have := (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 (M.inv_mem ha.2)) _).mp
      (Q.inv_mem hq₂)
    simpa [mul_assoc] using this
  have e : ⁅u, ⁅x, a⁆⁆ * a = ⁅x, ⁅u, ⁅x, a⁆⁆⁆⁻¹ * (x * u * x * a * (x * u * x)⁻¹) *
      (a⁻¹ * (⁅x, ⁅x, a⁆⁆ * ⁅x, a⁆ * ⁅x, ⁅u, a⁆⁆ * ⁅u, a⁆ * ⁅x, a⁆)⁻¹ * a) := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact Q.mul_mem (Q.mul_mem (Q.inv_mem hq₁) hw) hq₃

end CFSG.RankThree.GF2n.Stroth80
