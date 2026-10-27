module

public import CFSG.RankThree.GF2n.Stroth80.Sec1110LgenNorm
public import CFSG.RankThree.GF2n.Stroth80.Sec1110LgenCount
import CFSG.RankThree.GF2n.Stroth80.Sec12TorusFpf
import CFSG.RankThree.GF2n.Stroth80.Sec123Torus
import CFSG.RankThree.GF2n.Stroth80.Sec34TI

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G}

private theorem conj_comm_eq_of_commute {y s d u z b : G} (hys : y * s * y⁻¹ = u * s)
    (hyd : y * d * y⁻¹ = z * b * d) (hsz : s * z * s⁻¹ = z) (hsb : s * b * s⁻¹ = b)
    (huz : Commute u z) (hub : Commute u b) (huc : Commute u ⁅s, d⁆) (hud : Commute u d)
    (hcz : Commute ⁅s, d⁆ z) (hcb : Commute ⁅s, d⁆ b) :
    y * ⁅s, d⁆ * y⁻¹ = ⁅s, d⁆ := by
  set c := ⁅s, d⁆ with hcdef
  have hA : s * (z * b * d) * s⁻¹ = z * b * (c * d) := by
    have e : s * (z * b * d) * s⁻¹ = (s * z * s⁻¹) * (s * b * s⁻¹) * (s * d * s⁻¹) := by group
    have hsd : s * d * s⁻¹ = c * d := by
      rw [hcdef]
      simp only [commutatorElement_def]
      group
    rw [e, hsz, hsb, hsd]
  have hB' : u * (z * b * (c * d)) * u⁻¹ = z * b * (c * d) := by
    rw [((huz.mul_right hub).mul_right (huc.mul_right hud)).eq]
    group
  have hC : z * b * (c * d) * (z * b * d)⁻¹ = c := by
    calc z * b * (c * d) * (z * b * d)⁻¹ = z * b * c * (z * b)⁻¹ := by group
      _ = c := by
        rw [← (hcz.mul_right hcb).eq]
        group
  calc y * c * y⁻¹ = ⁅y * s * y⁻¹, y * d * y⁻¹⁆ := by
        rw [hcdef]
        simp only [commutatorElement_def]
        group
    _ = u * (s * (z * b * d) * s⁻¹) * u⁻¹ * (z * b * d)⁻¹ := by
        rw [hys, hyd]
        simp only [commutatorElement_def]
        group
    _ = c := by rw [hA, hB', hC]

private theorem Ctx.torus_comm_mem_inf (hc : Ctx M Q Z B) {y : G} (hyM : y ∈ M)
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) {s x : G} (hs : s ∈ QB B ⊓ M) (hx : x ∈ Q)
    (hyl : y * (s * x) * y⁻¹ * (s * x)⁻¹ ∈ Q) : y * s * y⁻¹ * s⁻¹ ∈ Q ⊓ QB B := by
  have hQn : ∀ m ∈ M, ∀ q ∈ Q, m * q * m⁻¹ ∈ Q := fun m hm q hq =>
    (hc.conj_mem_Q_of_mem_M hm).1 q hq
  have hsQB : s ∈ QB B := (Subgroup.mem_inf.mp hs).1
  have hyQB : y * s * y⁻¹ ∈ QB B := by
    have h1 : QB B = conjSubgroup y (QB B) := by
      rw [← QB_conj, conjSubgroup_eq_self_iff.mpr hyB]
    rw [h1]
    exact mem_conjSubgroup.mpr (by
      have e : y⁻¹ * (y * s * y⁻¹) * y = s := by group
      rw [e]
      exact hsQB)
  have huQ : y * s * y⁻¹ * s⁻¹ ∈ Q := by
    have e : y * (s * x) * y⁻¹ * (s * x)⁻¹ =
        (y * s * y⁻¹ * s⁻¹) * (s * (y * x * y⁻¹ * x⁻¹) * s⁻¹) := by group
    have h2 : s * (y * x * y⁻¹ * x⁻¹) * s⁻¹ ∈ Q :=
      hQn s (Subgroup.mem_inf.mp hs).2 _ (Q.mul_mem (hQn y hyM x hx) (Q.inv_mem hx))
    have h3 := Q.mul_mem (e ▸ hyl) (Q.inv_mem h2)
    rwa [mul_inv_cancel_right] at h3
  exact Subgroup.mem_inf.mpr ⟨huQ, (QB B).mul_mem hyQB ((QB B).inv_mem hsQB)⟩

private theorem Ctx.comm_eq_one_of_torus (hc : Ctx M Q Z B) {y : G} (hyX : y ∈ Q ⊔ QB B)
    (hyZ : y ∈ Subgroup.normalizer (Z : Set G)) (hyB : y ∈ Subgroup.normalizer (B : Set G))
    (hreg : ∀ v ∈ Z, y * v = v * y → v = 1) {s : G} (hs : s ∈ QB B ⊓ M)
    (hu : y * s * y⁻¹ * s⁻¹ ∈ Q ⊓ QB B) {d : G} (hd : d ∈ Q ⊓ QB B) : ⁅s, d⁆ = 1 := by
  have hsQB : s ∈ QB B := (Subgroup.mem_inf.mp hs).1
  have huQ : y * s * y⁻¹ * s⁻¹ ∈ Q := (Subgroup.mem_inf.mp hu).1
  have huQB : y * s * y⁻¹ * s⁻¹ ∈ QB B := (Subgroup.mem_inf.mp hu).2
  have hsZ : ∀ z ∈ Z, s * z * s⁻¹ = z := hc.LB_centralizes_Z (Subgroup.mem_sup_right hs)
  have hcB : ⁅s, d⁆ ∈ B := hc.comm_QB_le_B hsQB (Subgroup.mem_inf.mp hd).2
  have hcQ : ⁅s, d⁆ ∈ Q := hc.le hcB
  refine hc.eq_one_of_mem_B_of_torus_fix hyX hyZ hyB hreg hcB ?_
  obtain ⟨z, hz, b, hb, hzb⟩ := (Ctx.mem_sup_iff hc).mp (Ctx.sup_QB_comm_inf_mem hc hyX hd)
  have hud : Commute (y * s * y⁻¹ * s⁻¹) d :=
    congrArg Subtype.val ((Ctx.inf_QB_elemAbelian hc).1.is_comm.comm ⟨_, hu⟩ ⟨d, hd⟩)
  refine conj_comm_eq_of_commute (u := y * s * y⁻¹ * s⁻¹) (by group) ?_ (hsZ z hz) ?_
    (hc.hyp.toHyp79.V_central hz huQ).symm (Ctx.B_central_QB hc hb huQB).symm
    (Ctx.B_central_QB hc hcB huQB).symm hud (hc.hyp.toHyp79.V_central hz hcQ).symm
    (Ctx.B_central_QB hc hb (hc.B_le_QB hcB)).symm
  · calc y * d * y⁻¹ = ⁅y, d⁆ * d := by simp only [commutatorElement_def]; group
      _ = z * b * d := by rw [hzb]
  · rw [← Ctx.B_central_QB hc hb hsQB]
    group

theorem Ctx.comm_mem_Z_of_torus_comm_mem (hc : Ctx M Q Z B) {y : G} (hyX : y ∈ Q ⊔ QB B)
    (hyM : y ∈ M) (hyZ : y ∈ Subgroup.normalizer (Z : Set G))
    (hyB : y ∈ Subgroup.normalizer (B : Set G)) (hreg : ∀ v ∈ Z, y * v = v * y → v = 1)
    {l : G} (hl : l ∈ LB M Q B) (hyl : y * l * y⁻¹ * l⁻¹ ∈ Q) :
    ∀ d ∈ Q ⊓ QB B, ⁅l, d⁆ ∈ Z := by
  obtain ⟨s, hs, x, hx, rfl⟩ := hc.exists_mul_of_mem_LB hl
  have hsZ : ∀ z ∈ Z, s * z * s⁻¹ = z := hc.LB_centralizes_Z (Subgroup.mem_sup_right hs)
  have hu := hc.torus_comm_mem_inf hyM hyB hs hx hyl
  intro d hd
  have hxd : ⁅x, d⁆ ∈ Z := hc.hyp.toHyp79.comm_mem_V hx (Subgroup.mem_inf.mp hd).1
  have e : ⁅s * x, d⁆ = (s * ⁅x, d⁆ * s⁻¹) * ⁅s, d⁆ := by
    simp only [commutatorElement_def]
    group
  rw [e, hc.comm_eq_one_of_torus hyX hyZ hyB hreg hs hu hd, mul_one, hsZ _ hxd]
  exact hxd

private theorem mul_pow_mem_of_normalizer {L : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (L : Set G)) {l : G} (hl : l ∈ L) {m : ℕ} (hm : t ^ m = 1) :
    (l * t) ^ m ∈ L := by
  have key : ∀ m : ℕ, ∃ l' ∈ L, (l * t) ^ m = l' * t ^ m := by
    intro m
    induction m with
    | zero => exact ⟨1, L.one_mem, by simp⟩
    | succ m ih =>
      obtain ⟨l', hl', he⟩ := ih
      have hc : t ^ m * l * (t ^ m)⁻¹ ∈ L :=
        (Subgroup.mem_normalizer_iff.1 (Subgroup.pow_mem _ ht m) l).1 hl
      refine ⟨l' * (t ^ m * l * (t ^ m)⁻¹), L.mul_mem hl' hc, ?_⟩
      rw [pow_succ, he, pow_succ]
      group
  obtain ⟨l', hl', he⟩ := key m
  rw [he, hm, mul_one]
  exact hl'

private theorem mul_pow_conj_eq (t l : G) (k : ℕ) :
    t * (l * t) ^ k * t⁻¹ = l⁻¹ * (l * t) ^ k * l := by
  have h1 : t * (l * t) ^ k * t⁻¹ = (t * (l * t) * t⁻¹) ^ k := conj_pow.symm
  have h2 : l⁻¹ * (l * t) ^ k * l = (l⁻¹ * (l * t) * l) ^ k := by
    have h := (conj_pow (a := l⁻¹) (b := l * t) (i := k)).symm
    rwa [inv_inv] at h
  rw [h1, h2]
  congr 1
  group

private theorem odd_card_Z_sub_one (hc : Ctx M Q Z B) : Odd (Nat.card Z - 1) := by
  obtain ⟨r, -, hr, -⟩ := hc.hyp.cp
  have hq4 : 4 ≤ Nat.card Z := hc.hyp.q4
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [pow_zero] at hr
    omega
  have h2 : Even (Nat.card Z) := by
    rw [hr]
    exact Nat.even_pow.mpr ⟨even_two, hr0⟩
  obtain ⟨c, hc'⟩ := h2
  exact ⟨c - 1, by omega⟩

variable [(Q.subgroupOf M).Normal] {n : ℕ}

theorem XbarCore.exists_swap_comm_mem_Z (hc : Ctx M Q Z B) (hn : 3 ≤ n)
    (S : XbarCore M Q Z B n) {l : G} (hl : l ∈ LB M Q B)
    (hsw : conjSubgroup l S.V₁ = S.V₂ ∧ conjSubgroup l S.V₂ = S.V₁) :
    ∃ f ∈ LB M Q B, (conjSubgroup f S.V₁ = S.V₂ ∧ conjSubgroup f S.V₂ = S.V₁) ∧
      ∀ d ∈ Q ⊓ QB B, ⁅f, d⁆ ∈ Z := by
  obtain ⟨τ, hτX, hτM, hτB, hτZ, hτord, hτreg⟩ := hc.exists_torusOrd
  have hodd := odd_card_Z_sub_one hc
  have hτk : τ ^ (Nat.card Z - 1) = 1 := by
    rw [← hτord]
    exact pow_orderOf_eq_one τ
  have hτV := S.conj_eq_of_pow_eq_one hc hn hτM hodd hτk
  have hτL : τ ∈ Subgroup.normalizer (LB M Q B : Set G) := by
    rw [← conjSubgroup_eq_self_iff]
    exact hc.conj_LB_eq_of_le_sup_Z hτM (by
      rw [conjSubgroup_eq_self_iff.mpr hτB]
      exact le_sup_left)
  have hreg : ∀ v ∈ Z, τ * v = v * τ → v = 1 := fun v hv h =>
    hτreg 1 one_pos (by have := hc.hyp.q4; omega) v hv (by rwa [pow_one])
  have h₁ : conjSubgroup (l * τ) S.V₁ = S.V₂ := by rw [conjSubgroup_mul, hτV.1, hsw.1]
  have h₂ : conjSubgroup (l * τ) S.V₂ = S.V₁ := by rw [conjSubgroup_mul, hτV.2, hsw.2]
  have hfL : (l * τ) ^ (Nat.card Z - 1) ∈ LB M Q B := mul_pow_mem_of_normalizer hτL hl hτk
  refine ⟨_, hfL, ⟨conjSubgroup_pow_of_odd h₁ h₂ hodd, conjSubgroup_pow_of_odd h₂ h₁ hodd⟩, ?_⟩
  refine hc.comm_mem_Z_of_torus_comm_mem hτX hτM hτZ hτB hreg hfL ?_
  rw [mul_pow_conj_eq]
  have h := hc.commutator_LB_le_Q
    (Subgroup.commutator_mem_commutator ((LB M Q B).inv_mem hl) hfL)
  simpa [commutatorElement_def, mul_assoc] using h

private theorem inf_le_of_conj_eq {V₁ V₂ D : Subgroup G} {f : G} (hZ₂ : Z ≤ V₂)
    (hinf : V₁ ⊓ V₂ = Z) (hf : conjSubgroup f V₁ = V₂) (hfD : ∀ d ∈ D, ⁅f, d⁆ ∈ Z) :
    V₁ ⊓ D ≤ Z := by
  intro d hd
  have hd₁ : d ∈ V₁ := (Subgroup.mem_inf.mp hd).1
  have h1 : f * d * f⁻¹ ∈ V₂ := by
    rw [← hf, mem_conjSubgroup]
    simpa [mul_assoc] using hd₁
  have h2 : d ∈ V₂ := by
    have h3 := V₂.mul_mem (V₂.inv_mem (hZ₂ (hfD d (Subgroup.mem_inf.mp hd).2))) h1
    have e : ⁅f, d⁆⁻¹ * (f * d * f⁻¹) = d := by
      simp only [commutatorElement_def]
      group
    rwa [e] at h3
  rw [← hinf]
  exact Subgroup.mem_inf.mpr ⟨hd₁, h2⟩

private theorem comm_mem_Z_of_le (hc : Ctx M Q Z B) {V : Subgroup G} (hVQ : V ≤ Q)
    (hD : V ⊓ (Q ⊓ QB B) ≤ Z) {y : G} (hy : y ∈ LB M Q B)
    (hyV : y ∈ Subgroup.normalizer (V : Set G)) {c : G}
    (hcV : c ∈ V ⊓ Subgroup.centralizer (B : Set G)) : ⁅y, c⁆ ∈ Z := by
  have hc₁ : c ∈ V := (Subgroup.mem_inf.mp hcV).1
  refine hD (Subgroup.mem_inf.mpr ⟨?_, hc.comm_mem_inf_of_mem_LB hy
    (Subgroup.mem_inf.mpr ⟨hVQ hc₁, (Subgroup.mem_inf.mp hcV).2⟩)⟩)
  have h1 : y * c * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV c).mp hc₁
  rw [commutatorElement_def]
  exact V.mul_mem h1 (V.inv_mem hc₁)

theorem XbarCore.card_LB_le_two_mul (hc : Ctx M Q Z B) (hn : 3 ≤ n) (S : XbarCore M Q Z B n)
    {l₀ : G} (hl₀ : l₀ ∈ LB M Q B)
    (h₀ : conjSubgroup l₀ S.V₁ = S.V₂ ∧ conjSubgroup l₀ S.V₂ = S.V₁) :
    Nat.card (LB M Q B) ≤ 2 * Nat.card ↥(LB M Q B ⊓ XbarPre M Q Z B) := by
  have hsub : (LB M Q B : Set G) ⊆ (↑(LB M Q B ⊓ XbarPre M Q Z B) : Set G) ∪
      (fun x => l₀⁻¹ * x) '' (↑(LB M Q B ⊓ XbarPre M Q Z B) : Set G) := by
    intro l hl
    rcases S.conj_dichotomy hc hn (hc.LB_le_M hl) with h | h
    · exact Or.inl (Subgroup.mem_inf.mpr ⟨hl, S.mem_XbarPre_of_conj_eq hc hn hl h.1 h.2⟩)
    · refine Or.inr ⟨l₀ * l, Subgroup.mem_inf.mpr ⟨(LB M Q B).mul_mem hl₀ hl,
        S.mem_XbarPre_of_conj_eq hc hn ((LB M Q B).mul_mem hl₀ hl) ?_ ?_⟩, by simp⟩
      · rw [conjSubgroup_mul, h.1, h₀.2]
      · rw [conjSubgroup_mul, h.2, h₀.1]
  have hfin : ((↑(LB M Q B ⊓ XbarPre M Q Z B) : Set G) ∪
      (fun x => l₀⁻¹ * x) '' (↑(LB M Q B ⊓ XbarPre M Q Z B) : Set G)).Finite := Set.toFinite _
  rw [← SetLike.coe_sort_coe, ← SetLike.coe_sort_coe, Nat.card_coe_set_eq, Nat.card_coe_set_eq]
  calc (LB M Q B : Set G).ncard ≤ _ := Set.ncard_le_ncard hsub hfin
    _ ≤ _ := Set.ncard_union_le _ _
    _ = 2 * (↑(LB M Q B ⊓ XbarPre M Q Z B) : Set G).ncard := by
        rw [Set.ncard_image_of_injective _ (mul_right_injective l₀⁻¹)]
        ring

theorem XbarCore.conj_eq_of_mem_LB (hc : Ctx M Q Z B) (hw : Width Q Z n) (hn : 3 ≤ n)
    (S : XbarCore M Q Z B n) {l : G} (hl : l ∈ LB M Q B) :
    conjSubgroup l S.V₁ = S.V₁ ∧ conjSubgroup l S.V₂ = S.V₂ := by
  rcases S.conj_dichotomy hc hn (hc.LB_le_M hl) with h | h
  · exact h
  exfalso
  obtain ⟨f, -, hfs, hfD⟩ := S.exists_swap_comm_mem_Z hc hn hl h
  have hD₁ := inf_le_of_conj_eq S.Z_le₂ S.inf_eq hfs.1 hfD
  have hD₂ := inf_le_of_conj_eq S.Z_le₁ (by rw [inf_comm]; exact S.inf_eq) hfs.2 hfD
  have hY := S.card_le_of_comm_mem_Z hc hn (Y := LB M Q B ⊓ XbarPre M Q Z B) inf_le_right
    (fun y hy c hcV => comm_mem_Z_of_le hc S.le_Q₁ hD₁ (Subgroup.mem_inf.mp hy).1
      (S.act₁.1 (Subgroup.mem_inf.mp hy).2) hcV)
    (fun y hy c hcV => comm_mem_Z_of_le hc S.le_Q₂ hD₂ (Subgroup.mem_inf.mp hy).1
      (S.act₂.1 (Subgroup.mem_inf.mp hy).2) hcV)
  have hLB := S.card_LB_le_two_mul hc hn hl h
  have hge := hc.card_LB_ge hw (by omega)
  have hq := hc.hyp.q4
  have h1 : Nat.card Q * Nat.card Z ^ (n - 1) ≤ Nat.card Q * (2 * Nat.card Z) := by
    calc Nat.card Q * Nat.card Z ^ (n - 1) ≤ Nat.card (LB M Q B) := hge
      _ ≤ 2 * Nat.card ↥(LB M Q B ⊓ XbarPre M Q Z B) := hLB
      _ ≤ 2 * (Nat.card Q * Nat.card Z) := Nat.mul_le_mul_left 2 hY
      _ = Nat.card Q * (2 * Nat.card Z) := by ring
  have h2 := Nat.le_of_mul_le_mul_left h1 Nat.card_pos
  have h3 : Nat.card Z ^ 2 ≤ Nat.card Z ^ (n - 1) :=
    Nat.pow_le_pow_right (by omega) (by omega)
  nlinarith

theorem LB_le_XbarPre_of_caseVICore (hc : Ctx M Q Z B) (hw : Width Q Z n) (hn : 3 ≤ n)
    (hcore : CaseVICore M Q Z (XbarPre M Q Z B) n) : LB M Q B ≤ XbarPre M Q Z B := by
  obtain ⟨S⟩ := XbarCore.nonempty_of_caseVICore hcore
  intro l hl
  have h := S.conj_eq_of_mem_LB hc hw hn hl
  exact S.mem_XbarPre_of_conj_eq hc hn hl h.1 h.2

end CFSG.RankThree.GF2n.Stroth80
