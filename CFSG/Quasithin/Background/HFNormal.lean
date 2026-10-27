module

public import CFSG.Quasithin.Background.HFCodeInputs

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.QuasithinUnique.Setup.X1

section Chain

variable {d : ℕ} {T : PT d} [Fact (T.check = true)]

theorem conj_mem_subprods_of_normalChainB {l : List T.Elem} (h : normalChainB T l = true)
    (t : T.Elem) {s : T.Elem} (hs : s ∈ subprods l) (hl : IsCommInvol l) :
    t * s * t⁻¹ ∈ subprods l := by
  classical
  have hcl : ∀ a ∈ l, t * a * t⁻¹ ∈ subprods l := by
    intro a ha
    simp only [normalChainB, List.all_eq_true, decide_eq_true_eq] at h
    have := h (T.elemEquiv t) (List.mem_finRange _) a ha
    rwa [Equiv.symm_apply_apply] at this
  let B : Subgroup T.Elem :=
    { carrier := {x | x ∈ subprods l}
      mul_mem' := fun {x y} hx hy => mul_mem_subprods hl x hx y hy
      one_mem' := one_mem_subprods l
      inv_mem' := fun {x} hx => by
        have hx2 := sq_eq_one_of_mem_subprods hl x hx
        have : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
        simpa [this] using hx }
  have key : ∀ y ∈ l, y ∈ B.comap (MulAut.conj t).toMonoidHom := fun y hy => hcl y hy
  exact subprods_subset key s hs

theorem conj_mem_of_forallGreedy {pred : List T.Elem → Bool} {k : ℕ}
    (hg : forallGreedy T.invols pred k [] = true)
    (hpred : ∀ l : List T.Elem, IndepList l → l.length = k → pred l = true →
      normalChainB T l = true)
    (B : Subgroup T.Elem) (hcomm : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hsq : ∀ x ∈ B, x * x = 1)
    (hcard : Nat.card B = 2 ^ k) (t : T.Elem) {b : T.Elem} (hb : b ∈ B) : t * b * t⁻¹ ∈ B := by
  classical
  obtain ⟨l, hlen, hind, hBl, hpl⟩ := forallGreedy_sound hg B hcomm hsq
    (fun x _ hx1 => T.mem_invols hx1 (hsq x ‹_›)) hcard
  have hN := hpred l hind hlen hpl
  exact (hBl _).2 (conj_mem_subprods_of_normalChainB hN t ((hBl b).1 hb)
    (isCommInvol_of_indepList hind))

end Chain

section Sylow

variable {X K P : Type*} [Group X] [Group K] [Finite K] [Group P]

theorem le_normalizer_of_sylow (ψ : K →* X) (hψ : Function.Injective ψ) (φ : P →* K)
    (hφ : Function.Injective φ) (hsyl : Nat.card P = 2 ^ (Nat.card K).factorization 2) {k : ℕ}
    (hP : ∀ B : Subgroup P, (∀ x ∈ B, ∀ y ∈ B, x * y = y * x) → (∀ x ∈ B, x * x = 1) →
      Nat.card B = 2 ^ k → ∀ t : P, ∀ b ∈ B, t * b * t⁻¹ ∈ B)
    {S A : Subgroup X} (hSR : S ≤ ψ.range) (hS : IsPGroup 2 S) (hAS : A ≤ S)
    (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAs : ∀ x ∈ A, x * x = 1)
    (hcard : Nat.card A = 2 ^ k) : S ≤ Subgroup.normalizer (A : Set X) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS' : IsPGroup 2 (S.comap ψ) := hS.comap_of_injective ψ hψ
  obtain ⟨g, hg⟩ := exists_conj_le_range φ hφ hsyl hS'
  set A' : Subgroup K := A.comap ψ with hA'
  set B : Subgroup P := (A'.map (MulAut.conj g).toMonoidHom).comap φ with hB
  have hA'S : A' ≤ S.comap ψ := Subgroup.comap_mono hAS
  have hmemB : ∀ a' ∈ A', ∃ b ∈ B, φ b = g * a' * g⁻¹ := by
    intro a' ha'
    obtain ⟨b, hb⟩ := hg a' (hA'S ha')
    exact ⟨b, ⟨a', ha', hb.symm⟩, hb⟩
  have hBmem : ∀ b ∈ B, ∃ a' ∈ A', g * a' * g⁻¹ = φ b := by
    rintro b ⟨a', ha', hab⟩
    exact ⟨a', ha', hab⟩
  set c : P →* X := (MulAut.conj (ψ g⁻¹)).toMonoidHom.comp (ψ.comp φ) with hcdef
  have hc_apply : ∀ b, c b = ψ (g⁻¹ * φ b * g) := by
    intro b
    show ψ g⁻¹ * ψ (φ b) * (ψ g⁻¹)⁻¹ = _
    rw [map_mul, map_mul, map_inv, inv_inv]
  have hcinj : Function.Injective c :=
    (MulAut.conj (ψ g⁻¹)).injective.comp (hψ.comp hφ)
  have hBψ : ∀ b ∈ B, c b ∈ A := by
    intro b hb
    obtain ⟨a', ha', hab⟩ := hBmem b hb
    have : g⁻¹ * φ b * g = a' := by rw [← hab]; group
    rw [hc_apply, this]
    exact ha'
  have hBc : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x := by
    intro x hx y hy
    apply hcinj
    rw [map_mul, map_mul]
    exact hAc _ (hBψ x hx) _ (hBψ y hy)
  have hBs : ∀ x ∈ B, x * x = 1 := by
    intro x hx
    apply hcinj
    rw [map_mul, map_one]
    exact hAs _ (hBψ x hx)
  have hBcard : Nat.card B = 2 ^ k := by
    rw [← hcard]
    refine Nat.card_congr (Equiv.ofBijective (fun b : B => (⟨c b, hBψ b b.2⟩ : A))
      ⟨fun b d hbd => Subtype.ext (hcinj (congrArg Subtype.val hbd)), ?_⟩)
    rintro ⟨a, ha⟩
    obtain ⟨a', rfl⟩ := hSR (hAS ha)
    obtain ⟨b, hb, hba⟩ := hmemB a' ha
    refine ⟨⟨b, hb⟩, Subtype.ext ?_⟩
    show c b = ψ a'
    rw [hc_apply, hba]
    congr 1
    group
  have hBN := hP B hBc hBs hBcard
  have hfwd : ∀ s ∈ S, ∀ a ∈ A, s * a * s⁻¹ ∈ A := by
    intro s hs a ha
    obtain ⟨s', rfl⟩ := hSR hs
    obtain ⟨a', rfl⟩ := hSR (hAS ha)
    obtain ⟨t, ht⟩ := hg s' hs
    obtain ⟨b, hb, hba⟩ := hmemB a' ha
    obtain ⟨d, hd, hda⟩ := hBmem _ (hBN t b hb)
    have h1 : g * (s' * a' * s'⁻¹) * g⁻¹ = φ (t * b * t⁻¹) := by
      rw [map_mul, map_mul, map_inv, ht, hba]
      group
    have h2 : s' * a' * s'⁻¹ = d := mul_left_cancel (mul_right_cancel (h1.trans hda.symm))
    show ψ s' * ψ a' * (ψ s')⁻¹ ∈ A
    rw [← map_inv, ← map_mul, ← map_mul, h2]
    exact hd
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro a
  constructor
  · exact hfwd s hs a
  · intro h
    have := hfwd s⁻¹ (S.inv_mem hs) _ h
    simpa [mul_assoc] using this

end Sylow

end CFSG.Quasithin.H.Mathieu
