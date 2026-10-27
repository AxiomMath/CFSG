module

public import Certificates.Kernel.Co2.Chain
public import CFSG.Certificates.Kernel.HOrbSound
public import CFSG.Certificates.Kernel.Co2KillSound
public import CFSG.Certificates.Kernel.McLLabSound
public import CFSG.Certificates.Kernel.Co2.Bound.Checks.P_H_0
public import CFSG.Certificates.Kernel.Co2.Bound.Checks.A
public import CFSG.Certificates.Kernel.Co2.Bound.Checks.O
public import CFSG.Certificates.Kernel.Co2.Bound3.Checks.Pair
public import CFSG.Certificates.Kernel.Co2.Bound.Data.A
public import CFSG.Certificates.Kernel.Co2.Bound.Data.O
import CFSG.Certificates.Kernel.Common.Harness

public section

namespace CertificateChecks.KernelCo2

open CFSG.KC CFSG.KC.LceS CFSG.KC.HOrb CFSG.KC.Co2K CFSG.Certificates CFSG.Certificates.LCE

noncomputable abbrev HB : Subgroup (PresentedGroup P.relatorSet) :=
  Subgroup.closure ((fun j => bval tg (wWord (CFSG.KD.Co2BP.selST j)) (wLen (CFSG.KD.Co2BP.selST j))) ''
    {j | j < nat_lit 7})

theorem bray_walk : ∃ rep : ℕ → PresentedGroup P.relatorSet, rep 0 = 1 ∧
    ∀ w x R y, x < 2 ^ 20 → walkTo CFSG.KD.Co2BP.blk (nat_lit 289901) w x R y = true →
      rep x * bval tg (wWord w) (wLen w) * (rep y)⁻¹ ∈ HB := by
  have h := factsOk_intro (nR := nat_lit 10) (nS := nat_lit 7) (nf := nat_lit 289901)
    CFSG.KD.Co2BP.sH1 CFSG.KD.Co2BP.sH0 (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl)
    (by quickRfl) (by quickRfl) (by quickRfl) (by quickRfl) BPfacts
  exact HO.walkTo_sound tg HB h (fun r hr => rel_val r hr)
    (fun j hj => Subgroup.subset_closure ⟨j, hj, rfl⟩)

theorem loop2_spec (f : ℕ → Bool)
    (h : Nat.rec (motive := fun _ => Bool) true (fun h ih => andB
      (Nat.rec (motive := fun _ => Bool) true
        (fun l ih2 => andB (f (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) ih2)
        (nat_lit 256)) ih) (nat_lit 256) = true) : ∀ k < 65536, f k = true := by
  have inner : ∀ (g : ℕ → Bool) (n : ℕ),
      Nat.rec (motive := fun _ => Bool) true (fun l ih2 => andB (g l) ih2) n = true → ∀ l < n, g l = true := by
    intro g n
    induction n with
    | zero => intro _ l hl; omega
    | succ n ih =>
      intro hn l hl
      obtain ⟨h1, h2⟩ := KB.andB_true hn
      rcases Nat.lt_succ_iff_lt_or_eq.mp hl with hl | rfl
      · exact ih h2 l hl
      · exact h1
  have outer := inner (fun h => Nat.rec (motive := fun _ => Bool) true
    (fun l ih2 => andB (f (Nat.add (Nat.shiftLeft h (nat_lit 8)) l)) ih2) (nat_lit 256)) (nat_lit 256) h
  intro k hk
  have e : k = Nat.add (Nat.shiftLeft (k / 256) (nat_lit 8)) (k % 256) := by
    rw [show Nat.shiftLeft (k / 256) (nat_lit 8) = k / 256 * 2 ^ 8 from Nat.shiftLeft_eq _ _]
    simp only [Nat.add_eq]
    omega
  rw [e]
  exact inner (fun l => f (Nat.add (Nat.shiftLeft (k / 256) (nat_lit 8)) l)) (nat_lit 256)
    (outer (k / 256) (by change k / 256 < 256; omega)) (k % 256) (by change k % 256 < 256; omega)

set_option maxRecDepth 20000 in
theorem wtPer0_spec {WT : ℕ → ℕ} {m P : ℕ} (h : CFSG.KC.LceSR.wtPer0 WT m P = true) :
    ∀ k < 65536, WT k = 0 ∨ ∃ k' < m, WT k = WT k' := by
  intro k hk
  have h' : orB (Nat.beq (WT k) (nat_lit 0))
      (andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P)))) = true :=
    loop2_spec (fun k => orB (Nat.beq (WT k) (nat_lit 0))
      (andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P))))) h k hk
  cases h0 : Nat.beq (WT k) (nat_lit 0)
  · rw [h0] at h'
    have h1 : andB (Nat.blt (Nat.mod k P) m) (Nat.beq (WT k) (WT (Nat.mod k P))) = true := h'
    obtain ⟨h2, h3⟩ := KB.andB_true h1
    exact Or.inr ⟨k % P, Nat.le_of_ble_eq_true h2, Nat.eq_of_beq_eq_true h3⟩
  · exact Or.inl (Nat.eq_of_beq_eq_true h0)

theorem a_cent : HB ≤ Subgroup.centralizer {tg 0} := by
  have hA := McLLab.targets_sound tg (hwords := CFSG.KD.Co2BA.wd) (hinv := CFSG.KD.Co2BA.inv)
    (hanc := CFSG.KD.Co2BA.anc) (hfacts := CFSG.KD.Co2BA.f0) (htg := CFSG.KD.Co2BA.tg)
    (by intro r _; exact rel_all r) (wtPer0_spec (P := 8) (by quickRfl))
    ⟨by decide, by decide, by decide⟩ (by decide) (Nat.eq_of_beq_eq_true CFSG.KD.Co2BA.one)
    ⟨by decide, by decide⟩ (by decide) (by rfl) (by rfl) (by decide) (by rfl) (by rfl) (by rfl)
  have hnT : CFSG.KD.Co2BA.nT = 7 := Nat.eq_of_beq_eq_true CFSG.KD.Co2BA.nt
  have hc : ∀ k < 7, bval tg (wWord (Co2B.sub k)) (wLen (Co2B.sub k)) * tg 0 =
      tg 0 * bval tg (wWord (Co2B.sub k)) (wLen (Co2B.sub k)) := by
    intro k hk
    have hb : andB (Nat.beq (CFSG.KD.Co2BA.TW k) (commEnt (Co2B.sub k)))
        (Nat.beq (CFSG.KD.Co2BA.TL k) (CFSG.KC.McL.pid CFSG.KD.Co2BA.d)) = true := by
      interval_cases k
      exacts [CFSG.KD.Co2BA.bind0, CFSG.KD.Co2BA.bind1, CFSG.KD.Co2BA.bind2, CFSG.KD.Co2BA.bind3,
        CFSG.KD.Co2BA.bind4, CFSG.KD.Co2BA.bind5, CFSG.KD.Co2BA.bind6]
    obtain ⟨h1, h2⟩ := KB.andB_true hb
    have hv := hA k (by rw [hnT]; exact hk) (Nat.eq_of_beq_eq_true h2)
    rw [Nat.eq_of_beq_eq_true h1] at hv
    have he : HO.entOK (Co2B.sub k) (nat_lit 254) (nat_lit 510) = true := by
      interval_cases k <;> quickRfl
    rw [HO.bval_commEnt tg he] at hv
    set s := bval tg (wWord (Co2B.sub k)) (wLen (Co2B.sub k))
    have : (tg 0)⁻¹ * s⁻¹ * tg 0 * s = (s * tg 0)⁻¹ * (tg 0 * s) := by group
    rw [this] at hv
    exact (inv_mul_eq_one.mp hv)
  rw [Subgroup.closure_le]
  rintro _ ⟨j, hj, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
  rintro _ rfl
  exact (hc j hj).symm

theorem root_rel {U m k : ℕ} (hk : k < 10) (hb : Nat.beq (Co2B.rel k) (commPow U m) = true)
    (he : HO.entOK U (nat_lit 254) (nat_lit 510) = true)
    (hwf : Nat.blt (wWord (commEnt U)) (2 ^ (8 * wLen (commEnt U))) = true)
    (hm : Nat.blt (m * wLen (commEnt U)) 1024 = true) :
    ((tg 0)⁻¹ * (bval tg (wWord U) (wLen U))⁻¹ * tg 0 * bval tg (wWord U) (wLen U)) ^ m = 1 := by
  have hv := rel_val k hk
  rw [Nat.eq_of_beq_eq_true hb, show commPow U m = powEnt (commEnt U) m from rfl,
    HO.bval_powEnt tg (by simpa using hwf) (by simpa using hm), HO.bval_commEnt tg he] at hv
  exact hv

theorem pi_rel : ∀ r < 23, bval (fun k => bval tg (wWord (Co2K.gen (k + 1))) (wLen (Co2K.gen (k + 1))))
    (wWord (CFSG.KD.Co2KM.XRs r)) (wLen (CFSG.KD.Co2KM.XRs r)) = 1 := by
  obtain ⟨rep, h0, hw⟩ := bray_walk
  have hcent : ∀ x ∈ HB, x * tg 0 = tg 0 * x := fun x hx =>
    (Subgroup.mem_centralizer_iff.mp (a_cent hx) (tg 0) rfl).symm
  have hsub : ∀ j, HO.entOK (Co2B.sub j) (nat_lit 4) (nat_lit 16) = true ∧
      bval tg (wWord (Co2B.sub j)) (wLen (Co2B.sub j)) ∈ HB := by
    intro j
    by_cases hj : j < 7
    · refine ⟨by interval_cases j <;> quickRfl, Subgroup.subset_closure ⟨j, hj, rfl⟩⟩
    · rw [sub_ge (by omega)]
      exact ⟨by quickRfl, HB.one_mem⟩
  have hU : ∀ ρ, 1 ≤ ρ → ρ ≤ 4 →
      HO.entOK (rootWord CFSG.KD.Co2BO.UW0 CFSG.KD.Co2BO.UW1 CFSG.KD.Co2BO.UW2 CFSG.KD.Co2BO.UW3 ρ)
        (nat_lit 4) (nat_lit 64) = true ∧
      ((tg 0)⁻¹ * (bval tg (wWord (rootWord CFSG.KD.Co2BO.UW0 CFSG.KD.Co2BO.UW1 CFSG.KD.Co2BO.UW2
        CFSG.KD.Co2BO.UW3 ρ)) (wLen (rootWord CFSG.KD.Co2BO.UW0 CFSG.KD.Co2BO.UW1 CFSG.KD.Co2BO.UW2
        CFSG.KD.Co2BO.UW3 ρ)))⁻¹ * tg 0 * bval tg (wWord (rootWord CFSG.KD.Co2BO.UW0 CFSG.KD.Co2BO.UW1
        CFSG.KD.Co2BO.UW2 CFSG.KD.Co2BO.UW3 ρ)) (wLen (rootWord CFSG.KD.Co2BO.UW0 CFSG.KD.Co2BO.UW1
        CFSG.KD.Co2BO.UW2 CFSG.KD.Co2BO.UW3 ρ))) ^ rootExp ρ = 1 := by
    intro ρ h1 h4
    interval_cases ρ
    · exact ⟨by quickRfl, root_rel (k := 3) (by norm_num) CFSG.KD.Co2BO.rel1 (by quickRfl)
        (by quickRfl) (by quickRfl)⟩
    · exact ⟨by quickRfl, root_rel (k := 5) (by norm_num) CFSG.KD.Co2BO.rel2 (by quickRfl)
        (by quickRfl) (by quickRfl)⟩
    · exact ⟨by quickRfl, root_rel (k := 6) (by norm_num) CFSG.KD.Co2BO.rel3 (by quickRfl)
        (by quickRfl) (by quickRfl)⟩
    · exact ⟨by quickRfl, root_rel (k := 8) (by norm_num) CFSG.KD.Co2BO.rel4 (by quickRfl)
        (by quickRfl) (by quickRfl)⟩
  have key := fun {XRk i j m w R1 c ρ hl hn R2 : ℕ} (hargs : Co2Kill.pairArgsOK i j w hn = true)
      (h : pairOK CFSG.KD.Co2BP.blk Co2K.gen (nat_lit 289901) CFSG.KD.Co2BO.UW0 CFSG.KD.Co2BO.UW1
        CFSG.KD.Co2BO.UW2 CFSG.KD.Co2BO.UW3 XRk i j m w R1 c ρ hl hn R2 = true) =>
    Co2Kill.pairOK_sound tg HB rep h0 hw hsub hcent a_sq (by quickRfl) hU hargs h
  intro r hr
  interval_cases r
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr0
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr1
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr2
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr3
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr4
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr5
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr6
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr7
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr8
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr9
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr10
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr11
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr12
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr13
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr14
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr15
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr16
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr17
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr18
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr19
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr20
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr21
  · exact key (by quickRfl) CFSG.KD.Co2KM.pr22

end CertificateChecks.KernelCo2

end
