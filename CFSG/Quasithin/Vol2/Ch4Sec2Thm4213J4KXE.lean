module

public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

variable {Q : Type} [Group Q] [Finite Q]

theorem le_pRank_of_elemAbelian_card {H E : Subgroup Q} {k : ℕ} (hEH : E ≤ H)
    (hE : CFSG.Open.IsElemAbelian 3 E) (hk : Nat.card E = 3 ^ k) :
    k ≤ CFSG.Open.pRank 3 H := by
  unfold CFSG.Open.pRank
  apply le_csSup
  · refine ⟨Nat.card Q, fun m hm => ?_⟩
    obtain ⟨F, -, -, hFc⟩ := hm
    have h1 : Nat.card F ≤ Nat.card Q := Subgroup.card_le_card_group F
    rw [hFc] at h1
    exact le_of_lt ((Nat.lt_pow_self (by norm_num : 1 < 3)).trans_le h1)
  · exact ⟨E, hEH, hE, hk⟩

theorem false_of_two_E9 {H A B : Subgroup Q} (hrank : CFSG.Open.pRank 3 H ≤ 2)
    (hAH : A ≤ H) (hBH : B ≤ H) (hA : CFSG.Open.IsElemAbelian 3 A)
    (hB : CFSG.Open.IsElemAbelian 3 B) (hAc : Nat.card A = 9) (hBc : Nat.card B = 9)
    (hcomm : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) (hint : Nat.card ↥(A ⊓ B) ≤ 3) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨b, hbB, hbA⟩ : ∃ b ∈ B, b ∉ A := by
    by_contra hcon
    have hBA : B ≤ A := fun x hx => Classical.byContradiction fun hxA => hcon ⟨x, hx, hxA⟩
    have hABB : A ⊓ B = B := inf_eq_right.mpr hBA
    rw [hABB, hBc] at hint
    norm_num at hint
  have hb3 : b ^ 3 = 1 := hB.2 b hbB
  have hb1 : b ≠ 1 := fun h => hbA (h ▸ A.one_mem)
  have hord : orderOf b = 3 := orderOf_eq_prime hb3 hb1
  have hCc : Nat.card ↥(Subgroup.zpowers b) = 3 := by rw [Nat.card_zpowers, hord]
  have hCB : Subgroup.zpowers b ≤ B := Subgroup.zpowers_le.mpr hbB
  have hAC : ∀ c ∈ Subgroup.zpowers b, c ∈ A → c = 1 := by
    intro c hcC hcA
    by_contra hc1
    have hc3 : c ^ 3 = 1 := (hB.2 c (hCB hcC))
    have hcord : orderOf c = 3 := orderOf_eq_prime hc3 hc1
    have heq : Subgroup.zpowers c = Subgroup.zpowers b :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcC)
        (le_of_eq (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hcord]))
    apply hbA
    have hbz : b ∈ Subgroup.zpowers c := by rw [heq]; exact Subgroup.mem_zpowers b
    exact (Subgroup.zpowers_le.mpr hcA) hbz
  have hcomm' : ∀ (a : ↥A) (c : Q), c ∈ Subgroup.zpowers b → (a : Q) * c = c * (a : Q) :=
    fun a c hc => hcomm (a : Q) a.2 c (hCB hc)
  have hmul : ∀ p q : ↥A × ↥(Subgroup.zpowers b),
      ((p * q).1 : Q) * ((p * q).2 : Q) = ((p.1 : Q) * (p.2 : Q)) * ((q.1 : Q) * (q.2 : Q)) := by
    intro p q
    simp only [Prod.fst_mul, Prod.snd_mul, Subgroup.coe_mul]
    have h := hcomm' q.1 (p.2 : Q) p.2.2
    calc (p.1 : Q) * (q.1 : Q) * ((p.2 : Q) * (q.2 : Q))
        = (p.1 : Q) * ((q.1 : Q) * (p.2 : Q)) * (q.2 : Q) := by group
      _ = (p.1 : Q) * ((p.2 : Q) * (q.1 : Q)) * (q.2 : Q) := by rw [h]
      _ = (p.1 : Q) * (p.2 : Q) * ((q.1 : Q) * (q.2 : Q)) := by group
  let φ : (↥A × ↥(Subgroup.zpowers b)) →* Q :=
    MonoidHom.mk' (fun p => (p.1 : Q) * (p.2 : Q)) (fun p q => hmul p q)
  have hφ : ∀ p, φ p = (p.1 : Q) * (p.2 : Q) := fun p => rfl
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    intro p hp
    rw [hφ] at hp
    have h2 : (p.2 : Q) = ((p.1 : Q))⁻¹ := eq_inv_of_mul_eq_one_right hp
    have h2A : (p.2 : Q) ∈ A := by rw [h2]; exact A.inv_mem p.1.2
    have h2one : (p.2 : Q) = 1 := hAC _ p.2.2 h2A
    have h1one : (p.1 : Q) = 1 := by
      rw [h2one, mul_one] at hp
      exact hp
    exact Prod.ext (Subtype.ext h1one) (Subtype.ext h2one)
  set R : Subgroup Q := φ.range with hRdef
  have hRc : Nat.card ↥R = 27 := by
    rw [hRdef, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod, hAc, hCc]
  have hRH : R ≤ H := by
    rintro _ ⟨p, rfl⟩
    rw [hφ]
    exact H.mul_mem (hAH p.1.2) (hBH (hCB p.2.2))
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x := by
    rintro _ ⟨p, rfl⟩ _ ⟨q, rfl⟩
    rw [← map_mul, ← map_mul]
    have hpq : (p.1 : Q) * (q.1 : Q) = (q.1 : Q) * (p.1 : Q) :=
      congrArg Subtype.val (hA.1.is_comm.comm p.1 q.1)
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp p.2.2
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp q.2.2
    have hcc : (p.2 : Q) * (q.2 : Q) = (q.2 : Q) * (p.2 : Q) := by
      rw [← hm, ← hn]
      exact (Commute.zpow_zpow_self b m n).eq
    congr 1
    exact Prod.ext (Subtype.ext hpq) (Subtype.ext hcc)
  have hRexp : ∀ x ∈ R, x ^ 3 = 1 := by
    rintro _ ⟨p, rfl⟩
    rw [hφ]
    have hc : Commute (p.1 : Q) (p.2 : Q) := hcomm' p.1 p.2 p.2.2
    rw [hc.mul_pow, hA.2 _ p.1.2, hB.2 _ (hCB p.2.2), one_mul]
  have hRel : CFSG.Open.IsElemAbelian 3 R :=
    ⟨⟨⟨fun x y => Subtype.ext (hRcomm x.1 x.2 y.1 y.2)⟩⟩, hRexp⟩
  have hk := le_pRank_of_elemAbelian_card (k := 3) hRH hRel (by rw [hRc]; norm_num)
  omega

end CFSG.Quasithin.H13.Ch4.J4KX

end
