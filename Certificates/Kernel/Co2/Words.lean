module

public import CFSG.Certificates.Kernel.LceSTabSound
public import CFSG.Certificates.Kernel.CosetBounds
public import CFSG.Certificates.Kernel.Co2.Bound.RelsTC
import CFSG.Sporadic.Presentation.Common

public section

namespace CertificateChecks.KernelCo2

open CFSG.KC CFSG.KC.LceS CFSG.Certificates CFSG.Certificates.LCE

theorem letV_map {G H : Type*} [Group G] [Group H] (φ : G →* H) (gen : ℕ → G) (c : ℕ) :
    φ (letV gen c) = letV (fun k => φ (gen k)) c := by
  unfold letV
  split_ifs <;> simp

theorem bval_map {G H : Type*} [Group G] [Group H] (φ : G →* H) (gen : ℕ → G) (W n : ℕ) :
    φ (bval gen W n) = bval (fun k => φ (gen k)) W n := by
  unfold bval
  rw [map_list_prod, List.map_map]
  congr 1
  apply List.map_congr_left
  intro q _
  exact letV_map φ gen _

theorem bval_congr {G : Type*} [Group G] {gen gen' : ℕ → G} (h : ∀ k, gen k = gen' k) (W n : ℕ) :
    bval gen W n = bval gen' W n := by
  rw [show gen = gen' from funext h]

theorem wLet_eq (W i : ℕ) : wLet W i = W / 2 ^ (8 * i) % 256 := by
  change (W >>> (8 * i)) &&& (2 ^ 8 - 1) = _
  rw [Nat.shiftRight_eq_div_pow]
  exact Nat.and_two_pow_sub_one_eq_mod _ 8

theorem bval_succ {G : Type*} [Group G] (gen : ℕ → G) (W n : ℕ) :
    bval gen W (n + 1) = letV gen (wLet W 0) * bval gen (W / 256) n := by
  unfold bval
  rw [List.range_succ_eq_map, List.map_cons, List.prod_cons, List.map_map]
  congr 2
  apply List.map_congr_left
  intro q _
  simp only [Function.comp_apply, wLet_eq, Nat.div_div_eq_div_mul]
  congr 3
  rw [Nat.succ_eq_add_one, Nat.mul_add, pow_add]
  ring

theorem brec_beq_ne {k i : ℕ} (h : k ≠ i) (a b : ℕ) :
    Bool.rec (motive := fun _ => ℕ) a b (Nat.beq k i) = a := by
  have : Nat.beq k i = false := Bool.eq_false_iff.mpr fun h' => h (Nat.eq_of_beq_eq_true h')
  rw [this]

@[expose] noncomputable def swd {G : Type*} [Group G] (gen : ℕ → G) (w : List (ℕ × Bool)) : G :=
  (w.map fun x => if x.2 then gen x.1 else (gen x.1)⁻¹).prod

theorem bval_wordNat {G : Type*} [Group G] (gen : ℕ → G) :
    ∀ w : List (ℕ × Bool), (∀ l ∈ w, l.1 < 127) →
      bval gen (Co2B.wordNat w) w.length = swd gen w
  | [], _ => rfl
  | l :: w, hw => by
    obtain ⟨g, b⟩ := l
    have hg : g < 127 := hw (g, b) List.mem_cons_self
    have hc : Co2B.code (g, b) = 2 * g + (if b then 0 else 1) := rfl
    have hc' : Co2B.code (g, b) < 255 := by
      rw [hc]
      split_ifs <;> omega
    have e0 : Co2B.wordNat ((g, b) :: w) = Co2B.code (g, b) + 256 * Co2B.wordNat w := rfl
    have e1 : wLet (Co2B.wordNat ((g, b) :: w)) 0 = Co2B.code (g, b) := by
      rw [wLet_eq, e0, Nat.mul_zero, pow_zero, Nat.div_one]
      omega
    have e2 : Co2B.wordNat ((g, b) :: w) / 256 = Co2B.wordNat w := by
      rw [e0]
      omega
    rw [List.length_cons, bval_succ, e1, e2,
      bval_wordNat gen w fun l' h' => hw l' (List.mem_cons_of_mem _ h')]
    unfold swd
    rw [List.map_cons, List.prod_cons]
    congr 1
    unfold letV
    simp only [hc]
    cases b
    · have h1 : ¬ (2 * g + 1) % 2 = 0 := by omega
      have h2 : (2 * g + 1) / 2 = g := by omega
      have h3 : ¬ 2 * g + 1 = 255 := by omega
      simp only [Bool.false_eq_true, ↓reduceIte, h1, h2, h3]
    · have h1 : (2 * g + 0) % 2 = 0 := by omega
      have h2 : (2 * g + 0) / 2 = g := by omega
      have h3 : ¬ 2 * g + 0 = 255 := by omega
      simp only [↓reduceIte, h1, h2, h3]

theorem bval_ent {G : Type*} [Group G] (gen : ℕ → G) (w : List (ℕ × Bool))
    (hw : ∀ l ∈ w, l.1 < 127) (hlen : w.length < 1024) :
    bval gen (wWord (Co2B.ent w)) (wLen (Co2B.ent w)) = swd gen w := by
  have h1 : wWord (Co2B.ent w) = Co2B.wordNat w := by
    change (4 * w.length + 4096 * Co2B.wordNat w) >>> 12 = _
    rw [Nat.shiftRight_eq_div_pow]
    omega
  have h2 : wLen (Co2B.ent w) = w.length := by
    change ((4 * w.length + 4096 * Co2B.wordNat w) >>> 2) &&& (2 ^ 10 - 1) = _
    rw [Nat.shiftRight_eq_div_pow, Nat.and_two_pow_sub_one_eq_mod]
    omega
  rw [h1, h2]
  exact bval_wordNat gen w hw

@[expose] noncomputable def pgen {n : ℕ} (rels : Set (FreeGroup (Fin n))) (k : ℕ) : PresentedGroup rels :=
  if h : k < n then PresentedGroup.of ⟨k, h⟩ else 1

theorem pgen_lt {n : ℕ} (rels : Set (FreeGroup (Fin n))) {k : ℕ} (h : k < n) :
    pgen rels k = PresentedGroup.of ⟨k, h⟩ := by
  simp [pgen, h]

theorem closure_pgen {n : ℕ} (rels : Set (FreeGroup (Fin n))) :
    Subgroup.closure (pgen rels '' {g | g < n}) = ⊤ := by
  rw [← PresentedGroup.closure_range_of]
  congr 1
  ext x
  simp only [Set.mem_image, Set.mem_ofPred_eq, Set.mem_range]
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, (pgen_lt rels hg).symm⟩
  · rintro ⟨j, rfl⟩
    exact ⟨j.val, j.isLt, pgen_lt rels j.isLt⟩

theorem swd_pgen (P : TauCeti.GroupPresentation) (w : List (Fin P.generatorCount × Bool)) :
    swd (pgen P.relatorSet) (w.map fun l => (l.1.val, l.2)) =
      PresentedGroup.mk P.relatorSet (FreeGroup.mk w) := by
  induction w with
  | nil => rfl
  | cons l w ih =>
    unfold swd at ih ⊢
    rw [List.map_cons, List.map_cons, List.prod_cons, ih,
      show FreeGroup.mk (l :: w) = FreeGroup.mk [l] * FreeGroup.mk w from rfl, map_mul]
    congr 1
    obtain ⟨j, b⟩ := l
    have hj := pgen_lt P.relatorSet j.isLt
    cases b
    · rw [show FreeGroup.mk [(j, false)] = (FreeGroup.of j)⁻¹ from rfl, map_inv]
      simp only [Bool.false_eq_true, ↓reduceIte, hj]
      rfl
    · rw [show FreeGroup.mk [(j, true)] = FreeGroup.of j from rfl]
      simp only [↓reduceIte, hj]
      rfl

theorem swd_relatorLetters (P : TauCeti.GroupPresentation) :
    ∀ r ∈ P.relatorLetters, swd (pgen P.relatorSet) r = 1 := by
  intro r hr
  rw [TauCeti.GroupPresentation.relatorLetters_def, List.mem_map] at hr
  obtain ⟨w, hw, rfl⟩ := hr
  rw [swd_pgen]
  apply PresentedGroup.one_of_mem
  rw [CFSG.Sporadic.Presentation.relatorSet_eq]
  exact List.mem_map_of_mem hw

theorem relsNorm_spec {RT : ℕ → ℕ} {nR : ℕ} (h : relsNorm RT nR = true) :
    ∀ r < nR, wWord (RT r) < 2 ^ (8 * wLen (RT r)) := by
  induction nR with
  | zero => intro r hr; omega
  | succ n ih =>
    intro r hr
    have h' : andB (Nat.blt (wWord (RT n)) (Nat.shiftLeft 1 (Nat.mul 8 (wLen (RT n)))))
      (relsNorm RT n) = true := h
    obtain ⟨h1, h2⟩ := KB.andB_true h'
    rcases Nat.lt_succ_iff_lt_or_eq.mp hr with hr | rfl
    · exact ih h2 r hr
    · simpa [Nat.shiftLeft_eq] using h1

end CertificateChecks.KernelCo2

end
