module

public import CFSG.RankThree.GF2n.Stroth80.Sec10SevenChi
public import CFSG.RankThree.GF2n.Stroth80.Sec10Swap
public import CFSG.RankThree.GF2n.Smith81.Lin213Outside
public import CFSG.RankThree.GF2n.Smith81.Sec220S7Root
public import CFSG.RankThree.GF2n.Stroth80.Sec10CardU

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

private theorem chi_swap (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n : ℕ} (H : Sec10Hyp hc n)
    {t : G} {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G}
    (hgZ : conjSubgroup g Z = Y)
    {hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B} (H' : Sec10Hyp hcY n) {z : G}
    (hz103 : Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z)
    (hzVt : Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z =
      (Q ⊓ QB Y) ⊔ Y)
    {w : G} (hw : w ∈ QB Y) :
    ⁅w, z⁆ ∈ (Q ⊓ QB Y) ⊔ Y ↔ w ∈ Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y) := by
  have hQg : conjSubgroup g Q = QB Y := by
    rw [← Smith81.QB_conj_eq hs.hyp g, hgZ]
  have hw' : w ∈ conjSubgroup g Q := hQg ▸ hw
  have h := Good103.comm_mem_Vt_iff h34 h311a hspread H' hz103 hw'
  rw [hzVt, hQg] at h
  exact h

private theorem exists_not_mem_wt {m : ℕ} {Y : Subgroup G} {g : G}
    (hgZ : conjSubgroup g Z = Y)
    {hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B} {z₀ : G}
    (hVt : Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z₀ =
      (Q ⊓ QB Y) ⊔ Y)
    (hSL : SLMNat hcY z₀ m) (hm2 : 2 ≤ m) :
    ∃ h' : G, h' ∈ QB Y ∧ h' ∉ Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y) := by
  have hYcard : Nat.card ↥Y = Nat.card Z := by
    rw [← hgZ, CFSG.RankThree.GF2n.card_conjSubgroup]
  have hVcard : Nat.card ↥((Q ⊓ QB Y) ⊔ Y) = Nat.card Z ^ (m + 1) := by
    have h1 : Nat.card ↥((Q ⊓ QB Y) ⊔ Y) =
        Nat.card ↥(Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B)
          B Y z₀) := by rw [hVt]
    rw [h1, SLMNat.card_Vt hSL, hYcard]
  have hQcard : Nat.card ↥(QB Y) = Nat.card Q := by
    rw [hcY.hyp.QB_Z, CFSG.RankThree.GF2n.card_conjSubgroup]
  have hcard : Nat.card ↥(Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y)) * Nat.card Z ^ (m + 1) =
      Nat.card Q * Nat.card Z := by
    have h := hcY.card_Wt_mul_card_Vt z₀
    rw [hVt, hYcard, hVcard, ← hcY.hyp.QB_Z, hQcard] at h
    exact h
  have hmul : Nat.card ↥(Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y)) * Nat.card Z ^ m = Nat.card Q := by
    have h2 : Nat.card ↥(Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y)) * Nat.card Z ^ m * Nat.card Z =
        Nat.card Q * Nat.card Z := by
      rw [Nat.mul_assoc, ← pow_succ]
      exact hcard
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  have hq : 1 < Nat.card Z := by
    have := hcY.hyp.q4
    omega
  have hpow : 1 < Nat.card Z ^ m := one_lt_pow' hq (by omega)
  have hlt : Nat.card ↥(Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y)) < Nat.card Q := by
    calc Nat.card ↥(Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y))
        = Nat.card ↥(Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y)) * 1 := (Nat.mul_one _).symm
      _ < Nat.card ↥(Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y)) * Nat.card Z ^ m :=
          Nat.mul_lt_mul_of_pos_left hpow
            (Nat.card_pos (α := ↥(Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y))))
      _ = Nat.card Q := hmul
  have hnotle : ¬ QB Y ≤ Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y) := by
    intro hle
    have hc := Subgroup.card_le_of_le hle
    rw [hQcard] at hc
    omega
  exact SetLike.not_le_iff_exists.mp hnotle

private theorem comm_mul_mem_Q {hc : Ctx M Q Z B} {Y : Subgroup G}
    {h' c z : G}
    (hcA : c ∈ Q ⊓ QB Y) (hzZ : z ∈ Z)
    (hwQBX : c * z ∈ QB (conjSubgroup h' Z)) :
    ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ ∈ Q := by
  have hQBX : QB (conjSubgroup h' Z) = conjSubgroup h' Q := Smith81.QB_conj_eq hc.hyp h'
  have hvQ : h'⁻¹ * (c * z) * h' ∈ Q := by
    rw [hQBX, mem_conjSubgroup] at hwQBX
    exact hwQBX
  have hcQ : c ∈ Q := (Subgroup.mem_inf.mp hcA).1
  have hzQ : z ∈ Q := hc.hyp.Z_normal.1 hzZ
  have hc₁eq : h'⁻¹ * c * h' = c * ⁅c⁻¹, h'⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  have hweq : h'⁻¹ * z * h' = ⁅h'⁻¹, z⁆ * z := by
    simp only [commutatorElement_def]; group
  have hve : h'⁻¹ * (c * z) * h' = c * ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ * z := by
    calc h'⁻¹ * (c * z) * h' = (h'⁻¹ * c * h') * (h'⁻¹ * z * h') := by group
      _ = (c * ⁅c⁻¹, h'⁻¹⁆) * (⁅h'⁻¹, z⁆ * z) := by rw [hc₁eq, hweq]
      _ = c * ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ * z := by group
  have h1 : c * ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ * z ∈ Q := hve ▸ hvQ
  have h3 : ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ * z ∈ Q := by
    have h := Q.mul_mem (Q.inv_mem hcQ) h1
    rwa [show c⁻¹ * (c * ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ * z) =
      ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ * z by group] at h
  have h := Q.mul_mem h3 (Q.inv_mem hzQ)
  rwa [show ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ * z * z⁻¹ =
    ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ by group] at h

private theorem comm_inv_mem_QB {Y : Subgroup G} {g : G} {h' z : G}
    {hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B}
    (hh'QB : h' ∈ QB Y) (hzM : z ∈ conjSubgroup g M) :
    ⁅h'⁻¹, z⁆ ∈ QB Y := by
  have hh'Q : h' ∈ conjSubgroup g Q := by
    rw [← hcY.hyp.QB_Z]
    exact hh'QB
  have hzN : z ∈ Subgroup.normalizer (conjSubgroup g Q : Set G) :=
    hcY.hyp.Q_normal.2 hzM
  have hzh' : z * h' * z⁻¹ ∈ QB Y := by
    have := (Subgroup.mem_normalizer_iff.mp hzN h').mp hh'Q
    rwa [← hcY.hyp.QB_Z] at this
  have h := (QB Y).mul_mem ((QB Y).inv_mem hh'QB) hzh'
  rwa [show h'⁻¹ * (z * h' * z⁻¹) = ⁅h'⁻¹, z⁆ by
    simp only [commutatorElement_def]; group] at h

private theorem decomp_eq_one (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n m : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G}
    (hgZ : conjSubgroup g Z = Y)
    {hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B} (H' : Sec10Hyp hcY n)
    (hzswap : ∀ z ∈ Z, z ≠ 1 →
      Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z ∧
      Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z ∧
      Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z =
        (Q ⊓ QB Y) ⊔ Y ∧
      SLMNat hcY z m)
    {h' c z : G} (hh'QB : h' ∈ QB Y)
    (hh'W : h' ∉ Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y))
    (hcA : c ∈ Q ⊓ QB Y) (hzZ : z ∈ Z)
    (hwQBX : c * z ∈ QB (conjSubgroup h' Z)) : z = 1 := by
  by_contra hz1
  have hc₁wQ : ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ ∈ Q :=
    comm_mul_mem_Q (hc := hc) hcA hzZ hwQBX
  have hsz : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z :=
    (hzswap z hzZ hz1).1
  have hwV' : ⁅h'⁻¹, z⁆ ∉ (Q ⊓ QB Y) ⊔ Y := by
    intro hmem
    have hchi := chi_swap h34 h311a hspread H hs hgZ (hcY := hcY) H'
      (hzswap z hzZ hz1).2.1 (hzswap z hzZ hz1).2.2.1 ((QB Y).inv_mem hh'QB)
    have hW : h'⁻¹ ∈ Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y) := hchi.mp hmem
    exact hh'W (by simpa using (Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y)).inv_mem hW)
  have hwQB : ⁅h'⁻¹, z⁆ ∈ QB Y := comm_inv_mem_QB (hcY := hcY) hh'QB hsz.memM
  have hc₁Y : ⁅c⁻¹, h'⁻¹⁆ ∈ Y :=
    Sit.comm_QB_mem_X hs ((QB Y).inv_mem hcA.2) ((QB Y).inv_mem hh'QB)
  have hYleQB : Y ≤ QB Y := by
    have := hcY.hyp.Z_normal.1
    rwa [← hcY.hyp.QB_Z] at this
  have hc₁wV' : ⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆ ∈ (Q ⊓ QB Y) ⊔ Y :=
    Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨hc₁wQ, (QB Y).mul_mem (hYleQB hc₁Y) hwQB⟩)
  have hc₁V' : ⁅c⁻¹, h'⁻¹⁆ ∈ (Q ⊓ QB Y) ⊔ Y := Subgroup.mem_sup_right hc₁Y
  have hwV'' : ⁅h'⁻¹, z⁆ ∈ (Q ⊓ QB Y) ⊔ Y := by
    have h := (Q ⊓ QB Y ⊔ Y).mul_mem ((Q ⊓ QB Y ⊔ Y).inv_mem hc₁V') hc₁wV'
    rwa [show ⁅c⁻¹, h'⁻¹⁆⁻¹ * (⁅c⁻¹, h'⁻¹⁆ * ⁅h'⁻¹, z⁆) = ⁅h'⁻¹, z⁆ by group] at h
  exact hwV' hwV''

private theorem Vt_inf_QB_le (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n m : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t) {g : G}
    (hgZ : conjSubgroup g Z = Y)
    {hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B} (H' : Sec10Hyp hcY n)
    {h' : G} (hh'QB : h' ∈ QB Y)
    (hh'W : h' ∉ Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y))
    (hzswap : ∀ z ∈ Z, z ≠ 1 →
      Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z ∧
      Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z ∧
      Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z =
        (Q ⊓ QB Y) ⊔ Y ∧
      SLMNat hcY z m) :
    Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup h' Z) ≤
      Q ⊓ QB Y ⊓ QB (conjSubgroup h' Z) := by
  have hV : Vt M (LB M Q B) B Z t = (Q ⊓ QB Y) ⊔ Z := Good103.Vt_eq ht hs
  intro v hv
  obtain ⟨hvV, hvQBX⟩ := Subgroup.mem_inf.mp hv
  have hnorm : (Q ⊓ QB Y) ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (Subgroup.mem_inf.mp hx).1)
  obtain ⟨c, hcA, z, hzZ, hcv⟩ :=
    exists_mul_of_mem_sup_of_le_normalizer hnorm (hV ▸ hvV)
  have hz1 : z = 1 :=
    decomp_eq_one h34 h311a hspread H ht hs hgZ (hcY := hcY) H' hzswap
      hh'QB hh'W hcA hzZ (hcv ▸ hvQBX)
  refine Subgroup.mem_inf.mpr ⟨?_, hvQBX⟩
  rw [← hcv, hz1, mul_one]
  exact hcA

private theorem centralizes_Vt {hc : Ctx M Q Z B} {t : G}
    {Y X : Subgroup G} {y : G} (hs : Sit M Q Z Y t) (hsy : Sit M Q Z X y)
    {g : G} (hQg : conjSubgroup g Q = QB Y)
    {h' z₀ : G} (hy : y = h' * z₀ * h'⁻¹) (hh'QB : h' ∈ QB Y)
    (hsz₀ : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z₀)
    (hV : Vt M (LB M Q B) B Z t = (Q ⊓ QB Y) ⊔ Z) :
    ∀ v ∈ Vt M (LB M Q B) B Z t, y * v = v * y := by
  have hz₀cent : ∀ d ∈ (Q ⊓ QB Y) ⊔ Y, z₀ * d = d * z₀ := by
    have h := (Sit.inf_QB_sup_Z_comm hsz₀).2
    rw [hQg, hc.hyp.QB_Z, inf_comm] at h
    exact h
  intro v hv
  rw [hV] at hv
  have hnorm : (Q ⊓ QB Y) ≤ Subgroup.normalizer (Z : Set G) := fun x hx =>
    hc.hyp.Z_normal.2 (hc.hyp.Q_normal.1 (Subgroup.mem_inf.mp hx).1)
  obtain ⟨c, hcA, z, hzZ, hcv⟩ := exists_mul_of_mem_sup_of_le_normalizer hnorm hv
  have hyz : y * z = z * y := by
    have hyH0 : y ∈ H0 M Z := (Smith81.smith_1_12 hsy).1 hsy.mem
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hyH0).2 z hzZ).symm
  have hyc : y * c = c * y := by
    have hc₁Y : ⁅c⁻¹, h'⁻¹⁆ ∈ Y :=
      Sit.comm_QB_mem_X hs ((QB Y).inv_mem hcA.2) ((QB Y).inv_mem hh'QB)
    have hc' : h'⁻¹ * c * h' ∈ (Q ⊓ QB Y) ⊔ Y := by
      have hident : h'⁻¹ * c * h' = c * ⁅c⁻¹, h'⁻¹⁆ := by
        simp only [commutatorElement_def]; group
      rw [hident]
      exact (Q ⊓ QB Y ⊔ Y).mul_mem (Subgroup.mem_sup_left hcA)
        (Subgroup.mem_sup_right hc₁Y)
    have hcomm := hz₀cent (h'⁻¹ * c * h') hc'
    calc y * c = h' * z₀ * h'⁻¹ * c := by rw [hy]
      _ = h' * (z₀ * (h'⁻¹ * c * h')) * h'⁻¹ := by group
      _ = h' * ((h'⁻¹ * c * h') * z₀) * h'⁻¹ := by rw [hcomm]
      _ = c * (h' * z₀ * h'⁻¹) := by group
      _ = c * y := by rw [hy]
  calc y * v = y * (c * z) := by rw [hcv]
    _ = (y * c) * z := by group
    _ = (c * y) * z := by rw [hyc]
    _ = c * (y * z) := by group
    _ = c * (z * y) := by rw [hyz]
    _ = (c * z) * y := by group
    _ = v * y := by rw [hcv]

private theorem comm_mem_inf_QB {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}
    (hs : Sit M Q Z Y t) {u y z₀ : G} (huQB : u ∈ QB Y) (huM : u ∈ M)
    (hz₀Z : z₀ ∈ Z) (huz : u * z₀ = z₀ * u) (hyu : y = u * z₀) :
    ∀ x ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), ⁅x, y⁆ ∈ Q ⊓ QB Y := by
  intro x hx
  obtain ⟨hxQ, hxC⟩ := Subgroup.mem_inf.mp hx
  have hxt : x * t = t * x := Subgroup.mem_centralizer_singleton_iff.mp hxC
  have hxK : x ∈ Kx Q Y :=
    Subgroup.mem_inf.mpr ⟨hxQ, mem_normalizer_of_comm_Y hs hxt⟩
  have huL : u ∈ Lx M Y := Subgroup.mem_inf.mpr ⟨huQB, huM⟩
  have hcomm : ⁅x, u⁆ ∈ Q ⊓ QB Y :=
    (Smith81.smith_1_13 hs).1 (Subgroup.commutator_mem_commutator hxK huL)
  have hxz : ⁅x, z₀⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Z_central hc.hyp hz₀Z hxQ).symm
  have e : ⁅x, y⁆ = ⁅x, u⁆ := by
    rw [hyu, commutatorElement_mul_right_eq_mul_conj, hxz, mul_one]
    group
  rwa [e]

private theorem C_eq_centralizer {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}
    (hs : Sit M Q Z Y t) {h' : G} (hh'QB : h' ∈ QB Y) :
    Q ⊓ QB Y ⊓ QB (conjSubgroup h' Z) =
      (Q ⊓ QB Y) ⊓ Subgroup.centralizer ({h'} : Set G) := by
  have hQBX : QB (conjSubgroup h' Z) = conjSubgroup h' Q := Smith81.QB_conj_eq hc.hyp h'
  apply le_antisymm
  · intro c hcA'
    obtain ⟨hcA, hcQBX⟩ := Subgroup.mem_inf.mp hcA'
    have hcQ : c ∈ Q := (Subgroup.mem_inf.mp hcA).1
    have hcQBY : c ∈ QB Y := (Subgroup.mem_inf.mp hcA).2
    rw [hQBX, mem_conjSubgroup] at hcQBX
    have hmemY : ⁅c⁻¹, h'⁻¹⁆ ∈ Y :=
      Sit.comm_QB_mem_X hs ((QB Y).inv_mem hcQBY) ((QB Y).inv_mem hh'QB)
    have hident : h'⁻¹ * c * h' = c * ⁅c⁻¹, h'⁻¹⁆ := by
      simp only [commutatorElement_def]; group
    have hmemQ : ⁅c⁻¹, h'⁻¹⁆ ∈ Q := by
      have h2 : c * ⁅c⁻¹, h'⁻¹⁆ ∈ Q := hident ▸ hcQBX
      have h3 : c⁻¹ * (c * ⁅c⁻¹, h'⁻¹⁆) ∈ Q := Q.mul_mem (Q.inv_mem hcQ) h2
      rwa [show c⁻¹ * (c * ⁅c⁻¹, h'⁻¹⁆) = ⁅c⁻¹, h'⁻¹⁆ by group] at h3
    have hmem : ⁅c⁻¹, h'⁻¹⁆ ∈ Q ⊓ Y := ⟨hmemQ, hmemY⟩
    rw [inf_comm, (Smith81.smith_1_12 hs).2, Subgroup.mem_bot] at hmem
    have hcc : c * h' = h' * c := by
      have h1 : h'⁻¹ * c * h' = c := by rw [hident, hmem, mul_one]
      calc c * h' = h' * (h'⁻¹ * c * h') := by group
        _ = h' * c := by rw [h1]
    exact Subgroup.mem_inf.mpr ⟨hcA, Subgroup.mem_centralizer_singleton_iff.mpr hcc⟩
  · intro c hc
    obtain ⟨hcA, hcC⟩ := Subgroup.mem_inf.mp hc
    have hcc : c * h' = h' * c := Subgroup.mem_centralizer_singleton_iff.mp hcC
    refine Subgroup.mem_inf.mpr ⟨hcA, ?_⟩
    rw [hQBX, mem_conjSubgroup]
    have h1 : h'⁻¹ * c * h' = c := by
      calc h'⁻¹ * c * h' = h'⁻¹ * (c * h') := by group
        _ = h'⁻¹ * (h' * c) := by rw [hcc]
        _ = c := by group
    rw [h1]
    exact (Subgroup.mem_inf.mp hcA).1


private theorem A₀_le_centralizer {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}
    (hs : Sit M Q Z Y t) {h' : G} (hh'QB : h' ∈ QB Y)
    (hA₀le : Q ⊓ QB Y ≤ QB (conjSubgroup h' Z)) :
    (Q ⊓ QB Y) ≤ Subgroup.centralizer ({h'} : Set G) := by
  intro c hcA
  have hcQ : c ∈ Q := (Subgroup.mem_inf.mp hcA).1
  have hcQBY : c ∈ QB Y := (Subgroup.mem_inf.mp hcA).2
  have hcQX : h'⁻¹ * c * h' ∈ Q := by
    have h := hA₀le hcA
    rw [Smith81.QB_conj_eq hc.hyp h', mem_conjSubgroup] at h
    exact h
  have hmemY : ⁅c⁻¹, h'⁻¹⁆ ∈ Y :=
    Sit.comm_QB_mem_X hs ((QB Y).inv_mem hcQBY) ((QB Y).inv_mem hh'QB)
  have hident : h'⁻¹ * c * h' = c * ⁅c⁻¹, h'⁻¹⁆ := by
    simp only [commutatorElement_def]; group
  have hmemQ : ⁅c⁻¹, h'⁻¹⁆ ∈ Q := by
    have h2 : c * ⁅c⁻¹, h'⁻¹⁆ ∈ Q := hident ▸ hcQX
    have h3 : c⁻¹ * (c * ⁅c⁻¹, h'⁻¹⁆) ∈ Q := Q.mul_mem (Q.inv_mem hcQ) h2
    rwa [show c⁻¹ * (c * ⁅c⁻¹, h'⁻¹⁆) = ⁅c⁻¹, h'⁻¹⁆ by group] at h3
  have hmem : ⁅c⁻¹, h'⁻¹⁆ ∈ Q ⊓ Y := ⟨hmemQ, hmemY⟩
  rw [inf_comm, (Smith81.smith_1_12 hs).2, Subgroup.mem_bot] at hmem
  have hcc : c * h' = h' * c := by
    have h1 : h'⁻¹ * c * h' = c := by rw [hident, hmem, mul_one]
    calc c * h' = h' * (h'⁻¹ * c * h') := by group
      _ = h' * c := by rw [h1]
  exact Subgroup.mem_centralizer_singleton_iff.mpr hcc

private theorem C_ne_inf {hc : Ctx M Q Z B} {t : G} {Y : Subgroup G}
    (hs : Sit M Q Z Y t) {g : G}
    {hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B} {h' : G}
    (hh'QB : h' ∈ QB Y) (hh'W : h' ∉ Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y)) :
    Q ⊓ QB Y ⊓ QB (conjSubgroup h' Z) ≠ Q ⊓ QB Y := by
  intro heq
  have hQBX : QB (conjSubgroup h' Z) = conjSubgroup h' Q := Smith81.QB_conj_eq hc.hyp h'
  have hA₀le : Q ⊓ QB Y ≤ QB (conjSubgroup h' Z) := by
    intro c hc
    have hmem : c ∈ Q ⊓ QB Y ⊓ QB (conjSubgroup h' Z) := by
      rw [heq]
      exact hc
    exact (Subgroup.mem_inf.mp hmem).2
  have hcent := A₀_le_centralizer (hc := hc) hs hh'QB hA₀le
  have hYle : Y ≤ Subgroup.centralizer ({h'} : Set G) := by
    intro v hv
    have hh'Q : h' ∈ conjSubgroup g Q := by
      rw [← hcY.hyp.QB_Z]
      exact hh'QB
    exact Subgroup.mem_centralizer_singleton_iff.mpr (Z_central hcY.hyp hv hh'Q)
  have hV'le : (Q ⊓ QB Y) ⊔ Y ≤ Subgroup.centralizer ({h'} : Set G) :=
    sup_le hcent hYle
  have hW' : h' ∈ Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y) := by
    refine Subgroup.mem_inf.mpr ⟨hh'QB, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr fun v hv => ?_
    exact (Subgroup.mem_centralizer_iff.mp (hV'le hv) h' rfl).symm
  exact hh'W hW'

private structure TransverseSetup (hc : Ctx M Q Z B) (n m : ℕ) (H : Sec10Hyp hc n)
    (t : G) (ht : Good103 M Q Z B t) (Y : Subgroup G) (hs : Sit M Q Z Y t) where
  hm : SLMNat hc t m
  g : G
  hgZ : conjSubgroup g Z = Y
  hcY : Ctx (conjSubgroup g M) (conjSubgroup g Q) Y B
  H' : Sec10Hyp hcY n
  hzswap : ∀ z ∈ Z, z ≠ 1 →
    Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z ∧
    Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z ∧
    Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B) B Y z =
      (Q ⊓ QB Y) ⊔ Y ∧
    SLMNat hcY z m
  z₀ : G
  hz₀Z : z₀ ∈ Z
  hz₀1 : z₀ ≠ 1
  h' : G
  hh'QB : h' ∈ QB Y
  hh'W : h' ∉ Wt (QB Y) ((Q ⊓ QB Y) ⊔ Y)
  u : G
  hu : u = ⁅h', z₀⁆
  huQB : u ∈ QB Y
  huM : u ∈ M
  huz : u * z₀ = z₀ * u

private noncomputable def exists_setup (h34 : Stroth34Statement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n m : ℕ}
    (H : Sec10Hyp hc n) {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G}
    (hs : Sit M Q Z Y t) (hm : SLMNat hc t m) (hm2 : 2 ≤ m) :
    TransverseSetup hc n m H t ht Y hs := by
  classical
  choose g hgZ hgB hcY H' hzswap using ht.exists_swap h34 hspread H hs hm
  have hZne : Z ≠ ⊥ := by
    intro hbot
    have h4 := hc.hyp.q4
    rw [hbot, Subgroup.card_bot] at h4
    omega
  choose z hz1 using Subgroup.ne_bot_iff_exists_ne_one.mp hZne
  let z₀ : G := (z : G)
  have hz₀Z : z₀ ∈ Z := z.2
  have hz₀1' : z₀ ≠ 1 := fun h => hz1 (Subtype.ext h)
  have hsz₀ : Sit (conjSubgroup g M) (conjSubgroup g Q) Y Z z₀ :=
    (hzswap z₀ hz₀Z hz₀1').1
  have h103z₀ : Good103 (conjSubgroup g M) (conjSubgroup g Q) Y B z₀ :=
    (hzswap z₀ hz₀Z hz₀1').2.1
  have hVtz₀ : Vt (conjSubgroup g M) (LB (conjSubgroup g M) (conjSubgroup g Q) B)
      B Y z₀ = (Q ⊓ QB Y) ⊔ Y := (hzswap z₀ hz₀Z hz₀1').2.2.1
  have hSLz₀ : SLMNat hcY z₀ m := (hzswap z₀ hz₀Z hz₀1').2.2.2
  choose h' hh'QB hh'W using exists_not_mem_wt hgZ hVtz₀ hSLz₀ hm2
  let u : G := ⁅h', z₀⁆
  have hh'Q : h' ∈ conjSubgroup g Q := by
    rw [← hcY.hyp.QB_Z]
    exact hh'QB
  have huU : u ∈ Ut (conjSubgroup g Q) Y z₀ := comm_mem_Ut hh'Q
  have huQB : u ∈ QB Y := by
    have h := hcY.Ut_le_Q hsz₀.memM huU
    rwa [← hcY.hyp.QB_Z] at h
  have h5z : Sec5Hyp hcY n z₀ := H'.toSec5 h103z₀.1.mem_LB h103z₀.1.2.2.1
  have hSLnat : SLNat hcY z₀ := SLMNat.toSLNat hSLz₀ hm2
  have hz₀sq : z₀ ^ 2 = 1 := by rw [sq]; exact hsz₀.x_sq
  have huC : u ∈ Subgroup.centralizer ({z₀} : Set G) :=
    Ctx.Ut_le_centralizer h34 hcY h5z hSLnat hz₀sq huU
  have huz : u * z₀ = z₀ * u := Subgroup.mem_centralizer_singleton_iff.mp huC
  have huM : u ∈ M := by
    have huN : u ∈ Subgroup.normalizer (Z : Set G) :=
      CFSG.RankThree.GF2n.Tim77.mem_normalizer_of_commute_of_isTI
        hc.hyp.ti hz₀Z hz₀1' huz
    exact hc.hyp.normalizer_Z.1 ▸ huN
  exact ⟨hm, g, hgZ, hcY, H', hzswap, z₀, hz₀Z, hz₀1', h', hh'QB, hh'W,
    u, rfl, huQB, huM, huz⟩

private theorem exists_y (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n m : ℕ}
    {H : Sec10Hyp hc n} {t : G} {ht : Good103 M Q Z B t} {Y : Subgroup G}
    {hs : Sit M Q Z Y t} (S : TransverseSetup hc n m H t ht Y hs) :
    ∃ y : G, y = S.h' * S.z₀ * S.h'⁻¹ ∧
      Sit M Q Z (conjSubgroup S.h' Z) y := by
  have hyu : S.h' * S.z₀ * S.h'⁻¹ = S.u * S.z₀ := by
    rw [S.hu]
    simp only [commutatorElement_def]
    group
  have hyM : S.h' * S.z₀ * S.h'⁻¹ ∈ M := by
    rw [hyu]
    exact M.mul_mem S.huM (hc.hyp.Q_normal.1 (hc.hyp.Z_normal.1 S.hz₀Z))
  have hyQ : S.h' * S.z₀ * S.h'⁻¹ ∉ Q := by
    intro hyQ
    have huV' : S.u ∉ (Q ⊓ QB Y) ⊔ Y := by
      intro hmem
      have hmem' : ⁅S.h', S.z₀⁆ ∈ (Q ⊓ QB Y) ⊔ Y := by rwa [S.hu] at hmem
      have hchi := chi_swap h34 h311a hspread H hs S.hgZ (hcY := S.hcY) S.H'
        (S.hzswap S.z₀ S.hz₀Z S.hz₀1).2.1
        (S.hzswap S.z₀ S.hz₀Z S.hz₀1).2.2.1 S.hh'QB
      exact S.hh'W (hchi.mp hmem')
    apply huV'
    have huQ : S.u ∈ Q := by
      have h1 : S.u = (S.h' * S.z₀ * S.h'⁻¹) * S.z₀⁻¹ := by
        rw [S.hu]
        rfl
      rw [h1]
      exact Q.mul_mem hyQ (Q.inv_mem (hc.hyp.Z_normal.1 S.hz₀Z))
    exact Subgroup.mem_sup_left (Subgroup.mem_inf.mpr ⟨huQ, S.huQB⟩)
  exact ⟨S.h' * S.z₀ * S.h'⁻¹, rfl,
    Sit.of_conj hc.hyp S.hz₀Z S.hz₀1 hyM hyQ⟩

private theorem y_properties (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n m : ℕ}
    {H : Sec10Hyp hc n} {t : G} {ht : Good103 M Q Z B t} {Y : Subgroup G}
    {hs : Sit M Q Z Y t} (S : TransverseSetup hc n m H t ht Y hs) {y : G}
    (hy : y = S.h' * S.z₀ * S.h'⁻¹)
    (hsy : Sit M Q Z (conjSubgroup S.h' Z) y) :
    (∀ v ∈ Vt M (LB M Q B) B Z t, y * v = v * y) ∧
      (∀ x ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), ⁅x, y⁆ ∈ Q ⊓ QB Y) ∧
      Vt M (LB M Q B) B Z t ⊓ QB (conjSubgroup S.h' Z) ≤
        Q ⊓ QB Y ⊓ QB (conjSubgroup S.h' Z) := by
  have hQg : conjSubgroup S.g Q = QB Y := by
    rw [← Smith81.QB_conj_eq hs.hyp S.g, S.hgZ]
  have hyu : y = S.u * S.z₀ := by
    rw [hy, S.hu]
    simp only [commutatorElement_def]
    group
  refine ⟨?_, ?_, ?_⟩
  · exact centralizes_Vt (hc := hc) hs hsy hQg (hy := hy) S.hh'QB
      (S.hzswap S.z₀ S.hz₀Z S.hz₀1).1 (Good103.Vt_eq ht hs)
  · exact comm_mem_inf_QB (hc := hc) hs S.huQB S.huM S.hz₀Z S.huz hyu
  · exact Vt_inf_QB_le h34 h311a hspread H ht hs S.hgZ (hcY := S.hcY) S.H'
      S.hh'QB S.hh'W S.hzswap

private theorem y_bounds {hc : Ctx M Q Z B} {n m : ℕ} {H : Sec10Hyp hc n}
    {t : G} {ht : Good103 M Q Z B t} {Y : Subgroup G} {hs : Sit M Q Z Y t}
    (S : TransverseSetup hc n m H t ht Y hs) :
    Nat.card Z ^ m ≤
        Nat.card ↥(Q ⊓ QB Y ⊓ QB (conjSubgroup S.h' Z)) * Nat.card Z ∧
      Nat.card ↥(Q ⊓ QB Y ⊓ QB (conjSubgroup S.h' Z)) < Nat.card Z ^ m := by
  have hCeq := C_eq_centralizer (hc := hc) (t := t) hs S.hh'QB
  have hCne := C_ne_inf (hc := hc) (t := t) hs (g := S.g) (hcY := S.hcY)
    S.hh'QB S.hh'W
  have hA₀card : Nat.card ↥(Q ⊓ QB Y) = Nat.card Z ^ m :=
    Good103.card_inf_QB_eq_pow hc ht hs (SLMNat.card_Vt S.hm)
  have hYcard : Nat.card ↥Y = Nat.card Z := by
    rw [← S.hgZ, CFSG.RankThree.GF2n.card_conjSubgroup]
  have hweak : Nat.card Z ^ m ≤
      Nat.card ↥(Q ⊓ QB Y ⊓ QB (conjSubgroup S.h' Z)) * Nat.card Z := by
    have hQg : conjSubgroup S.g Q = QB Y := by
      rw [← Smith81.QB_conj_eq hs.hyp S.g, S.hgZ]
    have hSQ : Q ⊓ QB Y ≤ conjSubgroup S.g Q := by rw [hQg]; exact inf_le_right
    have hh'Q : S.h' ∈ conjSubgroup S.g Q := by rw [hQg]; exact S.hh'QB
    have h := CFSG.RankThree.GF2n.Smith81.card_le_card_inf_centralizer_mul S.hcY.hyp
      (S := Q ⊓ QB Y) hSQ hh'Q
    rw [← hCeq, hYcard, hA₀card] at h
    exact h
  have hlt : Nat.card ↥(Q ⊓ QB Y ⊓ QB (conjSubgroup S.h' Z)) < Nat.card Z ^ m := by
    have hle : (Q ⊓ QB Y ⊓ QB (conjSubgroup S.h' Z)) ≤ Q ⊓ QB Y := inf_le_left
    have hlt' : Nat.card ↥(Q ⊓ QB Y ⊓ QB (conjSubgroup S.h' Z)) <
        Nat.card ↥(Q ⊓ QB Y) := by
      by_contra hge
      exact hCne (Subgroup.eq_of_le_of_card_ge hle (Nat.le_of_not_lt hge))
    rwa [hA₀card] at hlt'
  exact ⟨hweak, hlt⟩

theorem Good103.exists_transverse (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hspread : StrothNoA2SpreadStatement) {hc : Ctx M Q Z B} {n m : ℕ} (H : Sec10Hyp hc n)
    {t : G} (ht : Good103 M Q Z B t) {Y : Subgroup G} (hs : Sit M Q Z Y t)
    (hm : SLMNat hc t m) (hm2 : 2 ≤ m) :
    ∃ (X : Subgroup G) (y : G), Sit M Q Z X y ∧
      (∀ v ∈ Vt M (LB M Q B) B Z t, y * v = v * y) ∧
      (∀ x ∈ Q ⊓ Subgroup.centralizer ({t} : Set G), ⁅x, y⁆ ∈ Q ⊓ QB Y) ∧
      Vt M (LB M Q B) B Z t ⊓ QB X ≤ Q ⊓ QB Y ⊓ QB X ∧
      Nat.card Z ^ m ≤ Nat.card ↥(Q ⊓ QB Y ⊓ QB X) * Nat.card Z ∧
      Nat.card ↥(Q ⊓ QB Y ⊓ QB X) < Nat.card Z ^ m := by
  let S := exists_setup h34 hspread H ht hs hm hm2
  obtain ⟨y, hy, hsy⟩ := exists_y h34 h311a hspread S
  obtain ⟨hcent, hcomm, hinf⟩ := y_properties h34 h311a hspread S hy hsy
  obtain ⟨hweak, hstrict⟩ := y_bounds S
  exact ⟨conjSubgroup S.h' Z, y, hsy, hcent, hcomm, hinf, hweak, hstrict⟩

end CFSG.RankThree.GF2n.Stroth80
