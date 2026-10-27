module

public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNotLeBasic
public import CFSG.Quasithin.Recognition.Stroth.Str86LemmaF
public import CFSG.Quasithin.Recognition.Stroth.Str86CaseIIaNatZ1
public import CFSG.Quasithin.Background.F6F613Basic
public import TauCeti.Algebra.Group.Subgroup.ModularLaw
public import CFSG.Monster.B.Fischer.Fi22Order

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem str86_caseIIa_notLe_q1_eq_z1
    {L1 L2 S : Subgroup G} {k m : ℕ} {F : Type} [Field F] [Finite F]
    (hF : F112Hyp L1 L2 S) (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G))
    (hk : 2 ≤ k) (hFc : Nat.card F = (2 ^ k) ^ 2)
    (hU3 : Nonempty (oTwoQuot ↥L1 ≃* StatedSU 3 (2 ^ k) F) ∨
      Nonempty (oTwoQuot ↥L1 ≃* StatedProj (StatedSU 3 (2 ^ k) F)))
    (hB2 : VBig L2) (hm : IsL2Quot m (oTwoQuot ↥L2))
    (hIIa : L2 ⊔ Q2 L1 L2 S ≤ Subgroup.centralizer (Z2 L1 L2 S : Set G))
    (hZ : ¬ Z1 L1 L2 S ≤ Q2 L1 L2 S) :
    Q1 L1 L2 S = Z1 L1 L2 S := by
  classical
  set H : Subgroup G := L1 ⊔ S with hHdef
  have hQ1S : Q1 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P1 hF.toW)
  have hQ2S : Q2 L1 L2 S ≤ S :=
    CFSG.Quasithin.F7.isSylowTwoOf_pCoreOf_le (f112_isSylowTwoOf_P2 hF.toW)
  have hSH : S ≤ H := by rw [hHdef]; exact le_sup_right
  have hHZ : H ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
    rw [hHdef]
    exact str86_sup_normalizes_z1 hF hSB hk hFc hU3
  have hZ1Q1 : Z1 L1 L2 S ≤ Q1 L1 L2 S := omegaOneCenterOf_le (Q1 L1 L2 S)
  have hZ1S : Z1 L1 L2 S ≤ S := hZ1Q1.trans hQ1S
  have hHP1 : H ≤ P1 L1 L2 S := by
    rw [hHdef, show P1 L1 L2 S = L1 ⊔ bigB L1 L2 S from rfl]
    exact sup_le le_sup_left ((le_sup_right : S ≤ bigB L1 L2 S).trans le_sup_right)
  have hQ1nH : H ≤ Subgroup.normalizer (Q1 L1 L2 S : Set G) :=
    hHP1.trans (le_normalizer_pCoreOf 2 (P1 L1 L2 S))
  have hBNZ1 : bigB L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans
      ((le_normalizer_pCoreOf 2 (P1 L1 L2 S)).trans
        (A4.normalizer_le_normalizer_omegaOneCenterOf (Q1 L1 L2 S)))
  obtain ⟨E, hEQ, hEn, hEH, hEmin⟩ := str86_lemmaF_exists hF hSB hB2 ⟨m, hm⟩
  have hFl := str86_lemmaF hF hSB hB2 ⟨m, hm⟩ hEQ hEn hEH hEmin
  have hEQ2Z : ⁅E, Q2 L1 L2 S⁆ ≤ Z1 L1 L2 S := hFl.2.2.1 (Z1 L1 L2 S) hZ1S hBNZ1 hZ
  have hEnotQ1 : ¬ E ≤ Q1 L1 L2 S := hFl.2.2.2 hZ
  have hQ2FZ : ⁅Q2 L1 L2 S, E⁆ ≤ Z1 L1 L2 S := by
    rw [Subgroup.commutator_comm]
    exact hEQ2Z
  obtain ⟨hZQ2S, -⟩ := str86_z1_sup_q2_of_not_le hF hSB hB2 hm hZ
  have hQ2NZ1 : Q2 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    hQ2S.trans (hSH.trans hHZ)
  have hmod : Z1 L1 L2 S ⊔ (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = Q1 L1 L2 S := by
    have h := Subgroup.inf_sup_assoc_of_le (H := Q2 L1 L2 S) (K := Q1 L1 L2 S)
      (N := Z1 L1 L2 S) hQ2NZ1 hZ1Q1
    rw [sup_comm (Q2 L1 L2 S) (Z1 L1 L2 S), hZQ2S, inf_eq_left.mpr hQ1S] at h
    rw [sup_comm]
    exact h
  have hKZ1 : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) :=
    (inf_le_right : Q1 L1 L2 S ⊓ Q2 L1 L2 S ≤ Q2 L1 L2 S).trans hQ2NZ1
  have hZ1EZ : ⁅Z1 L1 L2 S, E⁆ ≤ Z1 L1 L2 S := by
    rw [Subgroup.commutator_le]
    intro a ha f hf
    have hfH : f ∈ H := hSH (hQ2S (hEQ hf))
    have hfa : f * a * f⁻¹ ∈ Z1 L1 L2 S :=
      (Subgroup.mem_normalizer_iff.mp (hHZ hfH) a).mp ha
    have h1 : ⁅a, f⁆ = a * (f * a⁻¹ * f⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [h1]
    refine (Z1 L1 L2 S).mul_mem ha ?_
    have h2 : f * a⁻¹ * f⁻¹ = (f * a * f⁻¹)⁻¹ := by group
    rw [h2]
    exact (Z1 L1 L2 S).inv_mem hfa
  have hQ1EZ : ⁅Q1 L1 L2 S, E⁆ ≤ Z1 L1 L2 S := by
    rw [Subgroup.commutator_le]
    intro q hq f hf
    have hq' : q ∈ Z1 L1 L2 S ⊔ (Q1 L1 L2 S ⊓ Q2 L1 L2 S) := by
      rw [hmod]
      exact hq
    obtain ⟨a, ha, b, hb, hab⟩ :=
      (F1.mem_sup_iff_exists_mul_of_normalizes (H := Z1 L1 L2 S)
        (K := Q1 L1 L2 S ⊓ Q2 L1 L2 S) hKZ1).mp hq'
    have hbf : ⁅b, f⁆ ∈ Z1 L1 L2 S :=
      hQ2FZ (Subgroup.commutator_mono inf_le_right le_rfl
        (Subgroup.commutator_mem_commutator hb hf))
    have haf : ⁅a, f⁆ ∈ Z1 L1 L2 S :=
      hZ1EZ (Subgroup.commutator_mem_commutator ha hf)
    have hstep : ⁅a * b, f⁆ = a * ⁅b, f⁆ * a⁻¹ * ⁅a, f⁆ :=
      commutatorElement_mul_left_eq_conj_mul a b f
    rw [hab, hstep]
    exact (Z1 L1 L2 S).mul_mem
      ((Z1 L1 L2 S).mul_mem ((Z1 L1 L2 S).mul_mem ha hbf) ((Z1 L1 L2 S).inv_mem ha)) haf
  set M : Subgroup G := conjClosure E H with hMdef
  have hEHle : E ≤ H := (hEQ.trans hQ2S).trans hSH
  have hMH : M ≤ H := by
    rw [hMdef]
    refine conjClosure_le fun h hh f hf => ?_
    exact H.mul_mem (H.mul_mem hh (hEHle hf)) (H.inv_mem hh)
  have hQ1NM : Q1 L1 L2 S ≤ Subgroup.normalizer (M : Set G) :=
    ((hQ1S.trans hSH)).trans (le_normalizer_conjClosure E H)
  have hQ1MZ : ⁅Q1 L1 L2 S, M⁆ ≤ Z1 L1 L2 S := by
    let X : Set G := (Q1 L1 L2 S : Set G)
    let Y : Set G := {x : G | ∃ h ∈ H, ∃ f ∈ E, h * f * h⁻¹ = x}
    have hX : Subgroup.closure X = Q1 L1 L2 S := Subgroup.closure_eq (Q1 L1 L2 S)
    have hY : Subgroup.closure Y = M := by rw [hMdef]; rfl
    have hXcl : Subgroup.closure X ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
      rw [hX]
      exact (hQ1S.trans hSH).trans hHZ
    have hYcl : Subgroup.closure Y ≤ Subgroup.normalizer (Z1 L1 L2 S : Set G) := by
      rw [hY]
      exact hMH.trans hHZ
    have hpoint : ∀ x ∈ X, ∀ y ∈ Y, ⁅x, y⁆ ∈ Z1 L1 L2 S := by
      intro x hx y hy
      obtain ⟨h, hh, f, hf, rfl⟩ := hy
      have hx' : h⁻¹ * x * h ∈ Q1 L1 L2 S := by
        simpa using (Subgroup.mem_normalizer_iff.mp (hQ1nH (H.inv_mem hh)) x).mp hx
      have hc : ⁅h⁻¹ * x * h, f⁆ ∈ Z1 L1 L2 S :=
        hQ1EZ (Subgroup.commutator_mem_commutator hx' hf)
      have hleft : h * ⁅h⁻¹ * x * h, f⁆ * h⁻¹ ∈ Z1 L1 L2 S :=
        (Subgroup.mem_normalizer_iff.mp (hHZ hh) _).mp hc
      have hconj := conjugate_commutatorElement (g₁ := h⁻¹ * x * h) (g₂ := f) (g₃ := h)
      have hconj' : h * ⁅h⁻¹ * x * h, f⁆ * h⁻¹ = ⁅x, h * f * h⁻¹⁆ := by
        simpa [mul_assoc] using hconj
      rwa [← hconj']
    have hmain := TauCeti.commutator_closure_closure_le hXcl hYcl hpoint
    rw [hX, hY] at hmain
    exact hmain
  have hQ2p : IsPGroup 2 (Q2 L1 L2 S) := pCoreOf_isPGroup 2 (P2 L1 L2 S)
  have hEp : IsPGroup 2 E := hQ2p.to_le hEQ
  have hEz : IsSzU3Quot (oTwoQuot ↥H) (2 ^ k) := by
    rw [hHdef]
    exact str86_isSzU3Quot_sup hF hSB hk hFc hU3
  have hQ1core : pCoreOf 2 H = Q1 L1 L2 S := by
    rw [hHdef]
    exact str86_pCoreOf_sup_s_eq_q1 hF hSB hk hFc hU3
  have hKH : M ⊔ Q1 L1 L2 S ≤ H :=
    sup_le hMH (hQ1S.trans hSH)
  have hKN : H ≤ Subgroup.normalizer ((M ⊔ Q1 L1 L2 S : Subgroup G) : Set G) :=
    F1.le_normalizer_sup (X := H) (H := M) (K := Q1 L1 L2 S)
      (le_normalizer_conjClosure E H) hQ1nH
  have hQK : pCoreOf 2 H ≤ M ⊔ Q1 L1 L2 S := by
    rw [hQ1core]
    exact le_sup_right
  have hKHtop : M ⊔ Q1 L1 L2 S = H := by
    rcases eq_or_mem_pCoreOf_of_normal (H := H) (K := M ⊔ Q1 L1 L2 S) hEz hKH hKN hQK
      with htop | htwo
    · exact htop
    · exfalso
      apply hEnotQ1
      intro f hf
      have hfK : f ∈ M ⊔ Q1 L1 L2 S := Subgroup.mem_sup_left ((le_conjClosure E H) hf)
      have hfpow : ∃ n : ℕ, f ^ 2 ^ n = 1 := by
        obtain ⟨n, hn⟩ := hEp.exists_pow_pow_eq_one (⟨f, hf⟩ : ↥E)
        exact ⟨n, by simpa using congrArg Subtype.val hn⟩
      have hmem := htwo f hfK hfpow
      rwa [hQ1core] at hmem
  have hO2M : oTwoUpper H ≤ M := by
    have hHsup : H ≤ M ⊔ Q1 L1 L2 S := hKHtop.ge
    exact CFSG.Quasithin.Vol2.Ch11.SecD.oTwoUpper_le_of_le_sup'
      (X := H) (Y := M) (T := Q1 L1 L2 S) hHsup
      (pCoreOf_isPGroup 2 (P1 L1 L2 S)) hQ1NM
  have hO2supS : oTwoUpper H ⊔ S = H := by
    have h1 : oTwoUpper H ⊔ Q1 L1 L2 S = H := by
      rw [hHdef]
      exact str86_oTwoUpper_sup_q1 hF hSB hk hFc hU3
    refine le_antisymm (sup_le (oTwoUpper_le H) hSH) ?_
    calc H = oTwoUpper H ⊔ Q1 L1 L2 S := h1.symm
      _ ≤ oTwoUpper H ⊔ S := sup_le le_sup_left (hQ1S.trans le_sup_right)
  have hCbot : Q1 L1 L2 S ⊓
      Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ := by
    by_contra hNne
    let C : Subgroup G := Subgroup.centralizer (oTwoUpper H : Set G)
    let N : Subgroup G := Q1 L1 L2 S ⊓ C
    have hNdef : N = Q1 L1 L2 S ⊓ C := rfl
    have hNne' : N ≠ ⊥ := by rw [hNdef]; exact hNne
    have hNleS : N ≤ S := (inf_le_left : N ≤ Q1 L1 L2 S).trans hQ1S
    have hO2NH : H ≤ Subgroup.normalizer (oTwoUpper H : Set G) := le_normalizer_oTwoUpper H
    have hCNH : H ≤ Subgroup.normalizer (C : Set G) :=
      hO2NH.trans (CFSG.BenderSuzuki.normalizer_le_normalizer_centralizer (oTwoUpper H))
    have hNH : H ≤ Subgroup.normalizer (N : Set G) := by
      refine (le_inf hQ1nH hCNH).trans ?_
      exact Subgroup.inf_normalizer_le_normalizer_inf
    have hSN : S ≤ Subgroup.normalizer (N : Set G) := hSH.trans hNH
    obtain ⟨w, hwN, hwZ, hw1, hw2⟩ :=
      F6.exists_involution_mem_centerOf (P := S) (N := N) hF.1.h1.pgroup hNleS hSN hNne'
    have hwS : w ∈ S := A4.centerOf_le S hwZ
    have hwcent : w ∈ Subgroup.centralizer (S : Set G) := A4.centerOf_le_centralizer S hwZ
    have hwOmegaS : w ∈ omegaOneCenterOf S := by
      refine mem_omegaOneCenterOf hwS (fun y hy => ?_) hw2
      exact Subgroup.mem_centralizer_iff.mp hwcent y hy
    have hwZ1 : w ∈ Z1 L1 L2 S := omegaOneCenterOf_le_omegaOneCenterOf_pCoreOf hF.1 hwOmegaS
    have hwO2 : w ∈ C := (Subgroup.mem_inf.mp hwN).2
    have h1 : Subgroup.zpowers w ≤ Subgroup.centralizer (oTwoUpper H : Set G) :=
      Subgroup.zpowers_le.mpr hwO2
    have h2 : Subgroup.zpowers w ≤ Subgroup.centralizer (S : Set G) :=
      Subgroup.zpowers_le.mpr hwcent
    have h3 := CFSG.GorensteinWalter.le_centralizer_sup_of_le_centralizers h1 h2
    rw [hO2supS] at h3
    have hwCH : w ∈ Subgroup.centralizer (H : Set G) := Subgroup.zpowers_le.mp h3
    have hwbot : w ∈ (⊥ : Subgroup G) := by
      have hmem : w ∈ Z1 L1 L2 S ⊓ Subgroup.centralizer (H : Set G) :=
        Subgroup.mem_inf.mpr ⟨hwZ1, hwCH⟩
      rw [hHdef] at hmem
      rw [str86_centralizer_z1_sup_eq_bot hF hSB hk hFc hU3 hIIa] at hmem
      exact hmem
    exact hw1 (Subgroup.mem_bot.mp hwbot)
  have hsq : ∀ x ∈ Q1 L1 L2 S, x ^ 2 = 1 := by
    intro x hx
    have hx2C : x ^ 2 ∈ Subgroup.centralizer (oTwoUpper H : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hhM : h ∈ M := hO2M hh
      have hc : ⁅x, h⁆ ∈ Z1 L1 L2 S :=
        hQ1MZ (Subgroup.commutator_mem_commutator hx hhM)
      have hc2 : ⁅x, h⁆ ^ 2 = 1 := sq_eq_one_of_mem_omegaOneCenterOf hc
      have hxc : x * ⁅x, h⁆ = ⁅x, h⁆ * x :=
        mem_centralizer_of_mem_omegaOneCenterOf hc hx
      have hcinv : ⁅x, h⁆⁻¹ = ⁅x, h⁆ := (mul_eq_one_iff_inv_eq).mp (by
        simpa [pow_two] using hc2)
      have hxh : h * x * h⁻¹ = ⁅x, h⁆⁻¹ * x := by
        simp only [commutatorElement_def]
        group
      have hcancel : ⁅x, h⁆⁻¹ * ⁅x, h⁆⁻¹ = 1 := by
        rw [hcinv]
        simpa [pow_two] using hc2
      have hstep : (⁅x, h⁆⁻¹ * x) * (⁅x, h⁆⁻¹ * x) =
          (⁅x, h⁆⁻¹ * ⁅x, h⁆⁻¹) * (x * x) := by
        calc (⁅x, h⁆⁻¹ * x) * (⁅x, h⁆⁻¹ * x)
            = ⁅x, h⁆⁻¹ * (x * ⁅x, h⁆⁻¹) * x := by group
          _ = ⁅x, h⁆⁻¹ * (⁅x, h⁆⁻¹ * x) * x := by
              rw [show x * ⁅x, h⁆⁻¹ = ⁅x, h⁆⁻¹ * x by
                rw [hcinv]; exact hxc]
          _ = (⁅x, h⁆⁻¹ * ⁅x, h⁆⁻¹) * (x * x) := by group
      have hconj : h * (x * x) * h⁻¹ = x * x := by
        calc h * (x * x) * h⁻¹ = (h * x * h⁻¹) * (h * x * h⁻¹) := by group
          _ = (⁅x, h⁆⁻¹ * x) * (⁅x, h⁆⁻¹ * x) := by rw [hxh]
          _ = (⁅x, h⁆⁻¹ * ⁅x, h⁆⁻¹) * (x * x) := hstep
          _ = x * x := by rw [hcancel, one_mul]
      calc h * x ^ 2 = h * (x * x) := by rw [pow_two]
        _ = (h * (x * x) * h⁻¹) * h := by group
        _ = (x * x) * h := by rw [hconj]
        _ = x ^ 2 * h := by rw [pow_two]
    have hx2N : x ^ 2 ∈ Q1 L1 L2 S ⊓
        Subgroup.centralizer (oTwoUpper H : Set G) :=
      Subgroup.mem_inf.mpr ⟨(Q1 L1 L2 S).pow_mem hx 2, hx2C⟩
    rw [show Q1 L1 L2 S ⊓ Subgroup.centralizer (oTwoUpper H : Set G) = ⊥ from hCbot] at hx2N
    exact Subgroup.mem_bot.mp hx2N
  have hQ1Z : Q1 L1 L2 S ≤ Z1 L1 L2 S := by
    intro x hx
    have hx2 : x ^ 2 = 1 := hsq x hx
    have hxinv : x⁻¹ = x := (mul_eq_one_iff_inv_eq).mp (by simpa [pow_two] using hx2)
    have hcent : ∀ y ∈ Q1 L1 L2 S, y * x = x * y := by
      intro y hy
      have hy2 : y ^ 2 = 1 := hsq y hy
      have hyinv : y⁻¹ = y := (mul_eq_one_iff_inv_eq).mp (by simpa [pow_two] using hy2)
      have hxy2 : (x * y) ^ 2 = 1 := hsq (x * y) ((Q1 L1 L2 S).mul_mem hx hy)
      have hxyinv : (x * y)⁻¹ = x * y :=
        (mul_eq_one_iff_inv_eq).mp (by simpa [pow_two] using hxy2)
      calc y * x = (x * y)⁻¹ := by rw [mul_inv_rev, hxinv, hyinv]
        _ = x * y := hxyinv
    exact mem_omegaOneCenterOf hx hcent hx2
  exact le_antisymm hQ1Z (omegaOneCenterOf_le (Q1 L1 L2 S))

end CFSG.Quasithin.Stroth

end
