module

public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6
public import CFSG.RankThree.PartTwo.Sec19.SimsSolEvenRSmall6Transfer

public section

namespace CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6

open CFSG CFSG.QuasithinUnique CFSG.RankThree.PartTwo CFSG.CGT.PushingUpLit.SolK Equiv Equiv.Perm
open CFSG.RankThree.PartTwo.Sec19.SolEven.Comb (barPar)
open CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall (card_conj)
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {C : Cfg G M X 6}

theorem sig1_mul_self (π : Perm (Fin 6)) : sig1 π * sig1 π = 1 := by
  have h1 : sig1 1 * sig1 1 = 1 := by decide
  rw [sig1_eq π]
  calc π * sig1 1 * π⁻¹ * (π * sig1 1 * π⁻¹) = π * (sig1 1 * sig1 1) * π⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem sig2_mul_self (π : Perm (Fin 6)) : sig2 π * sig2 π = 1 := by
  have h1 : sig2 1 * sig2 1 = 1 := by decide
  rw [sig2_eq π]
  calc π * sig2 1 * π⁻¹ * (π * sig2 1 * π⁻¹) = π * (sig2 1 * sig2 1) * π⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem sig3_mul_self (π : Perm (Fin 6)) : sig3 π * sig3 π = 1 := by
  have h1 : sig3 1 * sig3 1 = 1 := by decide
  rw [sig3_eq π]
  calc π * sig3 1 * π⁻¹ * (π * sig3 1 * π⁻¹) = π * (sig3 1 * sig3 1) * π⁻¹ := by group
    _ = 1 := by rw [h1]; group

theorem sig2_ne_one (π : Perm (Fin 6)) : sig2 π ≠ 1 := by
  intro h
  have h1 := congrArg (fun σ : Perm (Fin 6) => σ (π 0)) h
  simp only [sig2, Perm.mul_apply, Perm.one_apply] at h1
  rw [swap_apply_of_ne_of_ne (π.injective.ne (by decide)) (π.injective.ne (by decide)),
    swap_apply_left] at h1
  exact π.injective.ne (by decide : (1 : Fin 6) ≠ 0) h1

theorem mem_normalizer_of_comm (S : Setting G M X 6) {g t c : G}
    (ht : t ∈ conjSubgroup g (Rc X)) (ht1 : t ≠ 1) (hc : c * t = t * c) :
    c ∈ Subgroup.normalizer ((conjSubgroup g (Rc X) : Subgroup G) : Set G) := by
  have hcM := RSmall.conj_mem_of_comm S ht ht1 hc
  have hc' : c⁻¹ * t = t * c⁻¹ := by
    calc c⁻¹ * t = c⁻¹ * (t * c) * c⁻¹ := by group
      _ = c⁻¹ * (c * t) * c⁻¹ := by rw [hc]
      _ = t * c⁻¹ := by group
  have hciM := RSmall.conj_mem_of_comm S ht ht1 hc'
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact RSmall.conj_normalized S hcM
  · intro hh
    have := RSmall.conj_normalized S hciM hh
    simpa [mul_assoc] using this

private theorem permBar_add_swap {a b c d : permBar 6} (h : a + b = c + d) : a + c = b + d := by
  have hn : ∀ x : permBar 6, -x = x := fun x => neg_eq_of_add_eq_zero_left (permBar_add_self x)
  calc a + c = (a + b) - b + c := by abel
    _ = (c + d) - b + c := by rw [h]
    _ = (c + c) + d - b := by abel
    _ = d - b := by rw [permBar_add_self, zero_add]
    _ = d + b := by rw [sub_eq_add_neg, hn]
    _ = b + d := add_comm _ _

theorem parK_eq_of_pairs (D : C.PiData) (π : Perm (Fin 6))
    {t₁ t₂ s₁ s₂ : G} (ht₁ : t₁ ∈ M) (ht₂ : t₂ ∈ M) (hs₁ : s₁ ∈ M) (hs₂ : s₂ ∈ M)
    (ht₁₁ : t₁ * t₁ = 1) (ht₂₂ : t₂ * t₂ = 1) (hs₁₁ : s₁ * s₁ = 1) (hs₂₂ : s₂ * s₂ = 1)
    (htc : t₁ * t₂ = t₂ * t₁) (hsc : s₁ * s₂ = s₂ * s₁)
    (hθt₁ : C.θ ⟨t₁, ht₁⟩ = sig1 π) (hθt₂ : C.θ ⟨t₂, ht₂⟩ = sig2 π)
    (hθs₁ : C.θ ⟨s₁, hs₁⟩ = sig1 π) (hθs₂ : C.θ ⟨s₂, hs₂⟩ = sig2 π)
    {x₁ x₂ : G} (hx₁ : x₁ ∈ M) (hx₂ : x₂ ∈ M) (hθx₁ : C.θ ⟨x₁, hx₁⟩ = sig1 π)
    (hθx₂ : C.θ ⟨x₂, hx₂⟩ = sig2 π) :
    parK D ⟨x₁⁻¹ * s₁, inv_mul_mem_K hx₁ hs₁ (hθx₁.trans hθs₁.symm)⟩ =
      parK D ⟨x₁⁻¹ * t₁, inv_mul_mem_K hx₁ ht₁ (hθx₁.trans hθt₁.symm)⟩ ∧
    parK D ⟨x₂⁻¹ * s₂, inv_mul_mem_K hx₂ hs₂ (hθx₂.trans hθs₂.symm)⟩ =
      parK D ⟨x₂⁻¹ * t₂, inv_mul_mem_K hx₂ ht₂ (hθx₂.trans hθt₂.symm)⟩ := by
  have hd₁ := inv_mul_mem_K hx₁ ht₁ (hθx₁.trans hθt₁.symm)
  have hd₂ := inv_mul_mem_K hx₂ ht₂ (hθx₂.trans hθt₂.symm)
  have he₁ := inv_mul_mem_K hx₁ hs₁ (hθx₁.trans hθs₁.symm)
  have he₂ := inv_mul_mem_K hx₂ hs₂ (hθx₂.trans hθs₂.symm)
  have hxx : ∀ {x : G} (hx : x ∈ M) {σ : Perm (Fin 6)}, C.θ ⟨x, hx⟩ = σ → σ * σ = 1 →
      x * x ∈ C.K := by
    intro x hx σ hθ hσ
    refine C.mem_K.2 ⟨M.mul_mem hx hx, ?_⟩
    have e : (⟨x * x, M.mul_mem hx hx⟩ : ↥M) = ⟨x, hx⟩ * ⟨x, hx⟩ := rfl
    rw [e, map_mul, hθ, hσ]
  have hxx₁ := hxx hx₁ hθx₁ (sig1_mul_self π)
  have hxx₂ := hxx hx₂ hθx₂ (sig2_mul_self π)
  have q₁ := piv_sq D hx₁ ht₁ ht₁₁ (hθx₁.trans hθt₁.symm) (by rw [hθt₁]; exact sig1_mul_self π)
    hd₁ hxx₁
  have q₁' := piv_sq D hx₁ hs₁ hs₁₁ (hθx₁.trans hθs₁.symm) (by rw [hθs₁]; exact sig1_mul_self π)
    he₁ hxx₁
  have q₂ := piv_sq D hx₂ ht₂ ht₂₂ (hθx₂.trans hθt₂.symm) (by rw [hθt₂]; exact sig2_mul_self π)
    hd₂ hxx₂
  have q₂' := piv_sq D hx₂ hs₂ hs₂₂ (hθx₂.trans hθs₂.symm) (by rw [hθs₂]; exact sig2_mul_self π)
    he₂ hxx₂
  rw [hθt₁] at q₁
  rw [hθs₁] at q₁'
  rw [hθt₂] at q₂
  rw [hθs₂] at q₂'
  have hk : (x₂ * x₁)⁻¹ * (x₁ * x₂) ∈ C.K := by
    refine C.mem_K.2 ⟨M.mul_mem (M.inv_mem (M.mul_mem hx₂ hx₁)) (M.mul_mem hx₁ hx₂), ?_⟩
    have e : (⟨(x₂ * x₁)⁻¹ * (x₁ * x₂), M.mul_mem (M.inv_mem (M.mul_mem hx₂ hx₁))
        (M.mul_mem hx₁ hx₂)⟩ : ↥M) = (⟨x₂, hx₂⟩ * ⟨x₁, hx₁⟩)⁻¹ * (⟨x₁, hx₁⟩ * ⟨x₂, hx₂⟩) := rfl
    rw [e, map_mul, map_inv, map_mul, map_mul, hθx₁, hθx₂, sig2_mul_sig1, inv_mul_cancel]
  have c₁ := piv_comm D hx₁ hx₂ ht₁ ht₂ htc (hθx₁.trans hθt₁.symm) (hθx₂.trans hθt₂.symm)
    (by rw [hθt₁]; exact sig1_mul_self π) (by rw [hθt₂]; exact sig2_mul_self π) hd₁ hd₂ hk
  have c₂ := piv_comm D hx₁ hx₂ hs₁ hs₂ hsc (hθx₁.trans hθs₁.symm) (hθx₂.trans hθs₂.symm)
    (by rw [hθs₁]; exact sig1_mul_self π) (by rw [hθs₂]; exact sig2_mul_self π) he₁ he₂ hk
  rw [hθt₁, hθt₂] at c₁
  rw [hθs₁, hθs₂] at c₂
  set v₁ := piv D (x₁⁻¹ * t₁) hd₁
  set v₂ := piv D (x₂⁻¹ * t₂) hd₂
  set v₁' := piv D (x₁⁻¹ * s₁) he₁
  set v₂' := piv D (x₂⁻¹ * s₂) he₂
  have hw₁ : barAct (sig1 π) (v₁ + v₁') = v₁ + v₁' := by
    rw [map_add]
    exact permBar_add_swap (q₁.symm.trans q₁')
  have hw₂ : barAct (sig2 π) (v₂ + v₂') = v₂ + v₂' := by
    rw [map_add]
    exact permBar_add_swap (q₂.symm.trans q₂')
  have hsum : barAct (sig2 π) (v₁ + v₁') + (v₁ + v₁') +
      (barAct (sig1 π) (v₂ + v₂') + (v₂ + v₂')) = 0 := by
    have h := c₁.symm.trans c₂
    rw [map_add, map_add]
    calc barAct (sig2 π) v₁ + barAct (sig2 π) v₁' + (v₁ + v₁') +
          (barAct (sig1 π) v₂ + barAct (sig1 π) v₂' + (v₂ + v₂'))
        = (barAct (sig1 π) v₂ + v₂ + (barAct (sig2 π) v₁ + v₁)) +
          (barAct (sig1 π) v₂' + v₂' + (barAct (sig2 π) v₁' + v₁')) := by abel
      _ = (barAct (sig1 π) v₂' + v₂' + (barAct (sig2 π) v₁' + v₁')) +
          (barAct (sig1 π) v₂' + v₂' + (barAct (sig2 π) v₁' + v₁')) := by rw [h]
      _ = 0 := permBar_add_self _
  obtain ⟨p₁, p₂⟩ := barPar_eq_zero_of_fixed even_six π hw₁ hw₂ hsum
  rw [map_add] at p₁ p₂
  have h2 : ∀ a b : ZMod 2, a + b = 0 → b = a := by decide
  exact ⟨h2 _ _ p₁, h2 _ _ p₂⟩

theorem parK_eq_zero_of_pair (D : C.PiData)
    (hA : ∀ y (hy : y ∈ CFSG.Open.pCoreOf 2 X), parK D ⟨y, Y_le_K C hy⟩ = 0) (π : Perm (Fin 6))
    {t₁ t₂ : G} (ht₁ : t₁ ∈ M) (ht₂ : t₂ ∈ M) (ht₁₁ : t₁ * t₁ = 1) (ht₂₂ : t₂ * t₂ = 1)
    (htc : t₁ * t₂ = t₂ * t₁) (hθt₁ : C.θ ⟨t₁, ht₁⟩ = sig1 π) (hθt₂ : C.θ ⟨t₂, ht₂⟩ = sig2 π)
    {x₁ x₂ : G} (hx₁ : x₁ ∈ X) (hx₂ : x₂ ∈ X) (hθx₁ : C.θ ⟨x₁, C.S.le hx₁⟩ = sig1 π)
    (hθx₂ : C.θ ⟨x₂, C.S.le hx₂⟩ = sig2 π) :
    parK D ⟨x₁⁻¹ * t₁, inv_mul_mem_K (C.S.le hx₁) ht₁ (hθx₁.trans hθt₁.symm)⟩ = 0 ∧
    parK D ⟨x₂⁻¹ * t₂, inv_mul_mem_K (C.S.le hx₂) ht₂ (hθx₂.trans hθt₂.symm)⟩ = 0 := by
  obtain ⟨r, hr⟩ := C.exists_lift (rho3_mem_alternatingGroup π)
  have hrM : (r : G) ∈ M := C.S.le r.2
  set ρ := rho3 π
  set s₁ := (r : G) * (t₁ * t₂) * (r : G)⁻¹ with hs₁'
  set s₂ := (r : G) * t₁ * (r : G)⁻¹ with hs₂'
  have ht₁₂ : t₁ * t₂ ∈ M := M.mul_mem ht₁ ht₂
  have hs₁ : s₁ ∈ M := M.mul_mem (M.mul_mem hrM ht₁₂) (M.inv_mem hrM)
  have hs₂ : s₂ ∈ M := M.mul_mem (M.mul_mem hrM ht₁) (M.inv_mem hrM)
  have hθconj : ∀ {g : G} (hg : g ∈ M) (hg' : (r : G) * g * (r : G)⁻¹ ∈ M),
      C.θ ⟨(r : G) * g * (r : G)⁻¹, hg'⟩ = ρ * C.θ ⟨g, hg⟩ * ρ⁻¹ := by
    intro g hg hg'
    have e : (⟨(r : G) * g * (r : G)⁻¹, hg'⟩ : ↥M) = ⟨r, hrM⟩ * ⟨g, hg⟩ * ⟨r, hrM⟩⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hr]
  have hθ₁₂ : C.θ ⟨t₁ * t₂, ht₁₂⟩ = sig1 π * sig2 π := by
    have e : (⟨t₁ * t₂, ht₁₂⟩ : ↥M) = ⟨t₁, ht₁⟩ * ⟨t₂, ht₂⟩ := rfl
    rw [e, map_mul, hθt₁, hθt₂]
  have hθs₁ : C.θ ⟨s₁, hs₁⟩ = sig1 π := by
    rw [hθconj ht₁₂ hs₁, hθ₁₂]
    calc ρ * (sig1 π * sig2 π) * ρ⁻¹ = (ρ * sig1 π * ρ⁻¹) * (ρ * sig2 π * ρ⁻¹) := by group
      _ = sig2 π * (sig1 π * sig2 π) := by rw [rho3_conj_sig1, rho3_conj_sig2]
      _ = sig1 π * (sig2 π * sig2 π) := by rw [← mul_assoc, sig2_mul_sig1, mul_assoc]
      _ = sig1 π := by rw [sig2_mul_self, mul_one]
  have hθs₂ : C.θ ⟨s₂, hs₂⟩ = sig2 π := by rw [hθconj ht₁ hs₂, hθt₁, rho3_conj_sig1]
  have hconj_sq : ∀ g : G, g * g = 1 → (r : G) * g * (r : G)⁻¹ * ((r : G) * g * (r : G)⁻¹) = 1 := by
    intro g hg
    calc (r : G) * g * (r : G)⁻¹ * ((r : G) * g * (r : G)⁻¹) = (r : G) * (g * g) * (r : G)⁻¹ := by
          group
      _ = 1 := by rw [hg]; group
  have h12sq : t₁ * t₂ * (t₁ * t₂) = 1 := by
    calc t₁ * t₂ * (t₁ * t₂) = t₁ * (t₂ * t₁) * t₂ := by group
      _ = t₁ * (t₁ * t₂) * t₂ := by rw [htc]
      _ = (t₁ * t₁) * (t₂ * t₂) := by group
      _ = 1 := by rw [ht₁₁, ht₂₂, one_mul]
  have hs₁₁ : s₁ * s₁ = 1 := hconj_sq _ h12sq
  have hs₂₂ : s₂ * s₂ = 1 := hconj_sq _ ht₁₁
  have hsc : s₁ * s₂ = s₂ * s₁ := by
    have h : t₁ * t₂ * t₁ = t₁ * (t₁ * t₂) := by rw [mul_assoc, ← htc]
    calc s₁ * s₂ = (r : G) * (t₁ * t₂ * t₁) * (r : G)⁻¹ := by rw [hs₁', hs₂']; group
      _ = (r : G) * (t₁ * (t₁ * t₂)) * (r : G)⁻¹ := by rw [h]
      _ = s₂ * s₁ := by rw [hs₁', hs₂']; group
  obtain ⟨u₁, u₂⟩ := parK_eq_of_pairs D π ht₁ ht₂ hs₁ hs₂ ht₁₁ ht₂₂ hs₁₁ hs₂₂ htc hsc hθt₁ hθt₂
    hθs₁ hθs₂ (C.S.le hx₁) (C.S.le hx₂) hθx₁ hθx₂
  have hx₁₂ : x₁ * x₂ ∈ X := X.mul_mem hx₁ hx₂
  have hrx₁₂ : (r : G) * (x₁ * x₂) * (r : G)⁻¹ ∈ X := X.mul_mem (X.mul_mem r.2 hx₁₂) (X.inv_mem r.2)
  have hθrx₁₂ : C.θ ⟨_, C.S.le hrx₁₂⟩ = C.θ ⟨x₁, C.S.le hx₁⟩ := by
    rw [hθconj (C.S.le hx₁₂) (C.S.le hrx₁₂), hθx₁]
    have e : (⟨x₁ * x₂, C.S.le hx₁₂⟩ : ↥M) = ⟨x₁, C.S.le hx₁⟩ * ⟨x₂, C.S.le hx₂⟩ := rfl
    rw [e, map_mul, hθx₁, hθx₂]
    calc ρ * (sig1 π * sig2 π) * ρ⁻¹ = (ρ * sig1 π * ρ⁻¹) * (ρ * sig2 π * ρ⁻¹) := by group
      _ = sig2 π * (sig1 π * sig2 π) := by rw [rho3_conj_sig1, rho3_conj_sig2]
      _ = sig1 π * (sig2 π * sig2 π) := by rw [← mul_assoc, sig2_mul_sig1, mul_assoc]
      _ = sig1 π := by rw [sig2_mul_self, mul_one]
  have hA' : ∀ y (hy : y ∈ CFSG.Open.pCoreOf 2 X), parK D ⟨y, Y_le_K C hy⟩ = 0 := hA
  have k1 : x₁⁻¹ * s₁ ∈ C.K := inv_mul_mem_K (C.S.le hx₁) hs₁ (hθx₁.trans hθs₁.symm)
  have k2 : ((r : G) * (x₁ * x₂) * (r : G)⁻¹)⁻¹ * s₁ ∈ C.K :=
    inv_mul_mem_K (C.S.le hrx₁₂) hs₁ (hθrx₁₂.trans (hθx₁.trans hθs₁.symm))
  have k3 : (x₁ * x₂)⁻¹ * (t₁ * t₂) ∈ C.K := by
    refine inv_mul_mem_K (C.S.le hx₁₂) ht₁₂ ?_
    have e : (⟨x₁ * x₂, C.S.le hx₁₂⟩ : ↥M) = ⟨x₁, C.S.le hx₁⟩ * ⟨x₂, C.S.le hx₂⟩ := rfl
    rw [e, map_mul, hθx₁, hθx₂, hθ₁₂]
  have hd₁ := inv_mul_mem_K (C.S.le hx₁) ht₁ (hθx₁.trans hθt₁.symm)
  have hd₂ := inv_mul_mem_K (C.S.le hx₂) ht₂ (hθx₂.trans hθt₂.symm)
  have l1 : parK D ⟨x₁⁻¹ * s₁, k1⟩ = parK D ⟨x₁⁻¹ * t₁, hd₁⟩ + parK D ⟨x₂⁻¹ * t₂, hd₂⟩ := by
    rw [parK_lift_eq D hA' hx₁ hrx₁₂ hθrx₁₂.symm k1 k2]
    rw [parK_conj_lift D hrM k3 k2]
    exact parK_mul_lift D (C.S.le hx₂) hd₁ hd₂ k3
  have hrx₁ : (r : G) * x₁ * (r : G)⁻¹ ∈ X := X.mul_mem (X.mul_mem r.2 hx₁) (X.inv_mem r.2)
  have hθrx₁ : C.θ ⟨_, C.S.le hrx₁⟩ = C.θ ⟨x₂, C.S.le hx₂⟩ := by
    rw [hθconj (C.S.le hx₁) (C.S.le hrx₁), hθx₁, rho3_conj_sig1, hθx₂]
  have k4 : x₂⁻¹ * s₂ ∈ C.K := inv_mul_mem_K (C.S.le hx₂) hs₂ (hθx₂.trans hθs₂.symm)
  have k5 : ((r : G) * x₁ * (r : G)⁻¹)⁻¹ * s₂ ∈ C.K :=
    inv_mul_mem_K (C.S.le hrx₁) hs₂ (hθrx₁.trans (hθx₂.trans hθs₂.symm))
  have l2 : parK D ⟨x₂⁻¹ * s₂, k4⟩ = parK D ⟨x₁⁻¹ * t₁, hd₁⟩ := by
    rw [parK_lift_eq D hA' hx₂ hrx₁ hθrx₁.symm k4 k5]
    exact parK_conj_lift D hrM hd₁ k5
  rw [u₁] at l1
  rw [u₂] at l2
  have h3 : ∀ a b : ZMod 2, a = a + b → b = a → a = 0 ∧ b = 0 := by decide
  exact h3 _ _ l1 l2

theorem lemma3Lift_holds : Lemma3Lift := by
  intro G _ _ M X C D hRsyl hRab hR4 g hTM hne hTK π hπ
  classical
  have hInP : ∀ σ, InP π σ → σ * σ = 1 := by
    rintro σ (rfl | rfl | rfl | rfl)
    · exact mul_one 1
    · exact sig1_mul_self π
    · exact sig2_mul_self π
    · exact sig3_mul_self π
  have hTsq : ∀ t ∈ conjSubgroup g (Rc X), t * t = 1 := by
    intro t ht
    have hK : t * t ∈ C.K := by
      refine C.mem_K.2 ⟨M.mul_mem (hTM ht) (hTM ht), ?_⟩
      have e : (⟨t * t, M.mul_mem (hTM ht) (hTM ht)⟩ : ↥M) = ⟨t, hTM ht⟩ * ⟨t, hTM ht⟩ := rfl
      rw [e, map_mul]
      exact hInP _ (hπ t ht)
    have hmem : t * t ∈ conjSubgroup g (Rc X) ⊓ C.K :=
      ⟨(conjSubgroup g (Rc X)).mul_mem ht ht, hK⟩
    rw [hTK, Subgroup.mem_bot] at hmem
    exact hmem
  have hRel : ∀ r ∈ Rc X, r * r = 1 := by
    intro r hr
    have ht : g * r * g⁻¹ ∈ conjSubgroup g (Rc X) :=
      mem_conjSubgroup.2 (by simpa [mul_assoc] using hr)
    have h := hTsq _ ht
    calc r * r = g⁻¹ * (g * r * g⁻¹ * (g * r * g⁻¹)) * g := by group
      _ = 1 := by rw [h]; group
  have hTc : ∀ t ∈ conjSubgroup g (Rc X), ∀ t' ∈ conjSubgroup g (Rc X), t * t' = t' * t := by
    intro t ht t' ht'
    have h1 := hRab _ (mem_conjSubgroup.1 ht) _ (mem_conjSubgroup.1 ht')
    calc t * t' = g * ((g⁻¹ * t * g) * (g⁻¹ * t' * g)) * g⁻¹ := by group
      _ = g * ((g⁻¹ * t' * g) * (g⁻¹ * t * g)) * g⁻¹ := by rw [h1]
      _ = t' * t := by group
  obtain ⟨-, ⟨t₁, ht₁T, ht₁M, hθt₁⟩, ⟨t₂, ht₂T, ht₂M, hθt₂⟩⟩ :=
    card_eq_four_of_pairing C hTM (by omega) hTK hπ
  have ht₁1 : t₁ ≠ 1 := by
    rintro rfl
    exact sig1_ne_one π (by rw [← hθt₁]; exact map_one C.θ)
  have ht₂1 : t₂ ≠ 1 := by
    rintro rfl
    exact sig2_ne_one π (by rw [← hθt₂]; exact map_one C.θ)
  obtain ⟨x₁, hx₁⟩ := C.exists_lift (sig1_mem_alternatingGroup π)
  obtain ⟨x₂, hx₂⟩ := C.exists_lift (sig2_mem_alternatingGroup π)
  obtain ⟨r₁, hr₁3, hr₁⟩ := RSmall.exists_lift_pow_three C (rot1_isThreeCycle π)
  obtain ⟨r₂, hr₂3, hr₂⟩ := RSmall.exists_lift_pow_three C (rot2_isThreeCycle π)
  have hθr₁ : C.θ ⟨r₁, C.S.le r₁.2⟩ = rot1 π := by rw [C.θ_X]; exact hr₁
  have hθr₂ : C.θ ⟨r₂, C.S.le r₂.2⟩ = rot2 π := by rw [C.θ_X]; exact hr₂
  have hconjX : ∀ {a : G}, a ∈ X → ∀ r : ↥X, (r : G) * a * (r : G)⁻¹ ∈ X :=
    fun ha r => X.mul_mem (X.mul_mem r.2 ha) (X.inv_mem r.2)
  have hθconj : ∀ {a : G} (ha : a ∈ X) (r : ↥X), C.θ ⟨_, C.S.le (hconjX ha r)⟩ =
      C.θ ⟨r, C.S.le r.2⟩ * C.θ ⟨a, C.S.le ha⟩ * (C.θ ⟨r, C.S.le r.2⟩)⁻¹ := by
    intro a ha r
    have e : (⟨_, C.S.le (hconjX ha r)⟩ : ↥M) =
        ⟨r, C.S.le r.2⟩ * ⟨a, C.S.le ha⟩ * (⟨r, C.S.le r.2⟩ : ↥M)⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv]
  by_cases hA : ∀ y (hy : y ∈ CFSG.Open.pCoreOf 2 X), parK D ⟨y, Y_le_K C hy⟩ = 0
  ·
    have hYel : ∀ y ∈ CFSG.Open.pCoreOf 2 X, y * y = 1 :=
      fun y hy => mul_self_eq_one_of_parK D hRsyl hRel hy (hA y hy)
    obtain ⟨p₁, p₂⟩ := parK_eq_zero_of_pair D hA π ht₁M ht₂M (hTsq _ ht₁T) (hTsq _ ht₂T)
      (hTc _ ht₁T _ ht₂T) hθt₁ hθt₂ x₁.2 x₂.2 hx₁ hx₂
    obtain ⟨a₁, ha₁, -, -, -, ha₁₁, hθa₁, hCa₁⟩ := exists_involution_of_lift D hRsyl hRel ht₁M
      (hTsq _ ht₁T) x₁.2 (hx₁.trans hθt₁.symm) (exists_mem_Y_pi_eq D _ (Or.inl p₁))
    obtain ⟨a₂, ha₂, -, -, -, ha₂₂, hθa₂, hCa₂⟩ := exists_involution_of_lift D hRsyl hRel ht₂M
      (hTsq _ ht₂T) x₂.2 (hx₂.trans hθt₂.symm) (exists_mem_Y_pi_eq D _ (Or.inl p₂))
    have hb₁ := comm_conj_of_mul_self D hYel ha₁ r₁.2 ha₁₁ hr₁3 (hθa₁.trans hθt₁) hθr₁
      (rot1_conj_sig1 π) (rot1_conj_esc1 π) (sig1_mul_esc1 π)
      (fun _ h1 h2 => barAct_rot1_eq π h1 h2)
    have hb₂ := comm_conj_of_mul_self D hYel ha₂ r₂.2 ha₂₂ hr₂3 (hθa₂.trans hθt₂) hθr₂
      (rot2_conj_sig2 π) (rot2_conj_esc2 π) (sig2_mul_esc2 π)
      (fun _ h1 h2 => barAct_rot2_eq π h1 h2)
    set b₁ := (r₁ : G) * a₁ * (r₁ : G)⁻¹ with hb₁'
    set b₂ := (r₂ : G) * a₂ * (r₂ : G)⁻¹ with hb₂'
    have hb₁X : b₁ ∈ X := hconjX ha₁ r₁
    have hb₂X : b₂ ∈ X := hconjX ha₂ r₂
    have hb₁t : b₁ * t₁ = t₁ * b₁ := (hCa₁ b₁ hb₁X).2 hb₁.symm
    have hb₂t : b₂ * t₂ = t₂ * b₂ := (hCa₂ b₂ hb₂X).2 hb₂.symm
    have hθb₁ : C.θ ⟨b₁, C.S.le hb₁X⟩ = esc1 π := by
      rw [hθconj ha₁ r₁, hθr₁, hθa₁, hθt₁, rot1_conj_sig1]
    have hθb₂ : C.θ ⟨b₂, C.S.le hb₂X⟩ = esc2 π := by
      rw [hθconj ha₂ r₂, hθr₂, hθa₂, hθt₂, rot2_conj_sig2]
    set z₀ := b₁ * b₂ with hz₀'
    have hz₀X : z₀ ∈ X := X.mul_mem hb₁X hb₂X
    have hz₀N : z₀ ∈ Subgroup.normalizer ((conjSubgroup g (Rc X) : Subgroup G) : Set G) :=
      Subgroup.mul_mem _ (mem_normalizer_of_comm C.S ht₁T ht₁1 hb₁t)
        (mem_normalizer_of_comm C.S ht₂T ht₂1 hb₂t)
    have hθz₀ : C.θ ⟨z₀, C.S.le hz₀X⟩ = esc1 π * esc2 π := by
      have e : (⟨z₀, C.S.le hz₀X⟩ : ↥M) = ⟨b₁, C.S.le hb₁X⟩ * ⟨b₂, C.S.le hb₂X⟩ := rfl
      rw [e, map_mul, hθb₁, hθb₂]
    have hz₀3X : z₀ ^ 3 ∈ X := X.pow_mem hz₀X 3
    have hz₀3Y : z₀ ^ 3 ∈ CFSG.Open.pCoreOf 2 X := by
      refine mem_Y_of_mem_K C hz₀3X (C.mem_K.2 ⟨C.S.le hz₀3X, ?_⟩)
      have e : (⟨z₀ ^ 3, C.S.le hz₀3X⟩ : ↥M) = (⟨z₀, C.S.le hz₀X⟩ : ↥M) ^ 3 := rfl
      rw [e, map_pow, hθz₀, esc1_mul_esc2_pow_three]
    obtain ⟨j, hj⟩ := isPGroup_pCoreOf' X ⟨z₀ ^ 3, hz₀3Y⟩
    have hj' : (z₀ ^ 3) ^ (2 ^ j) = 1 := by simpa using congrArg Subtype.val hj
    have hzX : z₀ ^ (2 ^ j) ∈ X := X.pow_mem hz₀X _
    refine ⟨⟨z₀ ^ (2 ^ j), hzX⟩, Subgroup.pow_mem _ hz₀N _, ?_, ?_⟩
    · show (z₀ ^ (2 ^ j)) ^ 3 = 1
      rw [← pow_mul, mul_comm, pow_mul, hj']
    · show C.θ ⟨z₀ ^ (2 ^ j), C.S.le hzX⟩ ≠ 1
      have e : (⟨z₀ ^ (2 ^ j), C.S.le hzX⟩ : ↥M) = (⟨z₀, C.S.le hz₀X⟩ : ↥M) ^ (2 ^ j) := rfl
      rw [e, map_pow, hθz₀]
      intro h
      have ho : orderOf (esc1 π * esc2 π) = 3 :=
        orderOf_eq_prime (esc1_mul_esc2_pow_three π) (esc1_mul_esc2_ne_one π)
      have hdvd := orderOf_dvd_of_pow_eq_one h
      rw [ho] at hdvd
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
        (Nat.Prime.dvd_of_dvd_pow Nat.prime_three hdvd)
      omega
  ·
    push Not at hA
    obtain ⟨y₀, hy₀, hodd'⟩ := hA
    have hodd : parK D ⟨y₀, Y_le_K C hy₀⟩ = 1 := by
      have h01 : ∀ a : ZMod 2, a ≠ 0 → a = 1 := by decide
      exact h01 _ hodd'
    obtain ⟨a₁, ha₁, -, -, -, ha₁₁, hθa₁, -⟩ := exists_involution_of_lift D hRsyl hRel ht₁M
      (hTsq _ ht₁T) x₁.2 (hx₁.trans hθt₁.symm)
      (exists_mem_Y_pi_eq D _ (Or.inr ⟨y₀, hy₀, hodd⟩))
    obtain ⟨a₂, ha₂, -, -, -, ha₂₂, hθa₂, -⟩ := exists_involution_of_lift D hRsyl hRel ht₂M
      (hTsq _ ht₂T) x₂.2 (hx₂.trans hθt₂.symm)
      (exists_mem_Y_pi_eq D _ (Or.inr ⟨y₀, hy₀, hodd⟩))
    have hb₁X := hconjX ha₁ r₁
    have hb₁₁ : (r₁ : G) * a₁ * (r₁ : G)⁻¹ * ((r₁ : G) * a₁ * (r₁ : G)⁻¹) = 1 := by
      calc (r₁ : G) * a₁ * (r₁ : G)⁻¹ * ((r₁ : G) * a₁ * (r₁ : G)⁻¹) =
          (r₁ : G) * (a₁ * a₁) * (r₁ : G)⁻¹ := by group
        _ = 1 := by rw [ha₁₁]; group
    have hθb₁ : C.θ ⟨_, C.S.le hb₁X⟩ = esc1 π := by
      rw [hθconj ha₁ r₁, hθr₁, hθa₁, hθt₁, rot1_conj_sig1]
    exact (false_of_odd_of_involutions D π hy₀ hodd ha₁ ha₂ hb₁X ha₁₁ ha₂₂ hb₁₁
      (hθa₁.trans hθt₁) (hθa₂.trans hθt₂) hθb₁).elim

end CFSG.RankThree.PartTwo.Sec19.SolEven.RSmall6
