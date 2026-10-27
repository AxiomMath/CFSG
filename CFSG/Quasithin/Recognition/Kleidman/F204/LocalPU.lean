module

public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalFive
public import CFSG.Quasithin.Recognition.Kleidman.F204.LocalQ

public section

namespace CFSG.Quasithin.Kleidman.F204

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
  CFSG.Quasithin.FA5 CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X : Subgroup G}

omit [Finite G] in
theorem eq_or_eq_of_relIndex_five {K L H : Subgroup G} (h : K.relIndex L = 5) (hKH : K ≤ H)
    (hHL : H ≤ L) : H = K ∨ H = L := by
  have hmul := Subgroup.relIndex_mul_relIndex K H L hKH hHL
  rw [h] at hmul
  have hd : K.relIndex H ∣ 5 := ⟨_, hmul.symm⟩
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 5)).mp hd with h1 | h1
  · left
    exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hKH
  · right
    rw [h1] at hmul
    have : H.relIndex L = 1 := by omega
    exact le_antisymm hHL (Subgroup.relIndex_eq_one.mp this)

theorem eq_or_eq_B_P1 (F : Frame L1 L2 S D X) {H : Subgroup G} (hBH : bigB L1 L2 S ≤ H)
    (hHP : H ≤ P1 L1 L2 S) : H = bigB L1 L2 S ∨ H = P1 L1 L2 S :=
  eq_or_eq_of_relIndex_five F.pair.relIndex_bigB_left hBH hHP

omit [Finite G] in
theorem pow_three_of_mem_D (F : Frame L1 L2 S D X) {d : G} (hd : d ∈ D) : d ^ 3 = 1 := by
  have := pow_card_eq_one' (G := ↥D) (x := ⟨d, hd⟩)
  rw [F.D_card] at this
  simpa using congrArg Subtype.val this

theorem D_normalizes_conj_Q2 (F : Frame L1 L2 S D X) {d q : G} (hd : d ∈ D)
    (hq : q ∈ P1 L1 L2 S) : d ∈ Subgroup.normalizer ((conjSub q (Q2 L1 L2 S) : Subgroup G) : Set G) := by
  have hdP : d ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) (F.D_le_B hd)
  have hx : q⁻¹ * d * q ∈ bigB L1 L2 S := three_conj_mem_B F hdP (pow_three_of_mem_D F hd) hq
  have hxQ : q⁻¹ * d * q ∈ Subgroup.normalizer ((Q2 L1 L2 S : Subgroup G) : Set G) :=
    P2_le_normalizer_Q2 L1 L2 S ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hx)
  have e : d = q * (q⁻¹ * d * q) * q⁻¹ := by group
  rw [e]
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [mem_conjSub, mem_conjSub]
  have := Subgroup.mem_normalizer_iff.mp hxQ (q⁻¹ * y * q)
  have e2 : q⁻¹ * (q * (q⁻¹ * d * q) * q⁻¹ * y * (q * (q⁻¹ * d * q) * q⁻¹)⁻¹) * q =
      (q⁻¹ * d * q) * (q⁻¹ * y * q) * (q⁻¹ * d * q)⁻¹ := by group
  rw [e2]
  exact this

theorem Q1_eq_sup_of_not_normal (F : Frame L1 L2 S D X)
    (hPU : ¬ P1 L1 L2 S ≤ Subgroup.normalizer ((Q1 L1 L2 S ⊓ Q2 L1 L2 S : Subgroup G) : Set G))
    {q : G} (hq : q ∈ P1 L1 L2 S) (hqB : q ∉ bigB L1 L2 S) :
    (Q1 L1 L2 S ⊓ Q2 L1 L2 S) ⊔ conjSub q (Q1 L1 L2 S ⊓ Q2 L1 L2 S) = Q1 L1 L2 S := by
  set K := Q1 L1 L2 S ⊓ Q2 L1 L2 S with hK
  have hN1 := P1_le_normalizer_Q1 L1 L2 S
  have hqQ1 : conjSub q (Q1 L1 L2 S) = Q1 L1 L2 S := conjSub_eq_of_mem_normalizer (hN1 hq)
  have hKq : conjSub q K ≤ Q1 L1 L2 S := by
    rw [hK, conjSub_inf, hqQ1]; exact inf_le_left
  set M := K ⊔ conjSub q K with hM
  have hMQ1 : M ≤ Q1 L1 L2 S := sup_le inf_le_left hKq
  have hDM : ∀ d ∈ D, conjSub d M = M := by
    intro d hd
    have hdB : d ∈ bigB L1 L2 S := F.D_le_B hd
    have hdP1 : d ∈ P1 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S) hdB
    have hdP2 : d ∈ P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) hdB
    have h1 : conjSub d (Q1 L1 L2 S) = Q1 L1 L2 S := conjSub_eq_of_mem_normalizer (hN1 hdP1)
    have h2 : conjSub d (Q2 L1 L2 S) = Q2 L1 L2 S :=
      conjSub_eq_of_mem_normalizer (P2_le_normalizer_Q2 L1 L2 S hdP2)
    have h3 : conjSub d (conjSub q (Q2 L1 L2 S)) = conjSub q (Q2 L1 L2 S) :=
      conjSub_eq_of_mem_normalizer (D_normalizes_conj_Q2 F hd hq)
    have h4 : conjSub d K = K := by rw [hK, conjSub_inf, h1, h2]
    have h5 : conjSub d (conjSub q K) = conjSub q K := by
      rw [hK, conjSub_inf, hqQ1, conjSub_inf, h1, h3]
    rw [hM, conjSub_sup, h4, h5]
  have hSP2 : S ≤ P2 L1 L2 S := (show S ≤ bigB L1 L2 S from le_sup_right).trans le_sup_right
  have hMN2 : M ≤ Subgroup.normalizer ((Q2 L1 L2 S : Subgroup G) : Set G) := fun m hm =>
    P2_le_normalizer_Q2 L1 L2 S (hSP2 (F.Q1_le_S (hMQ1 hm)))
  set N := Q2 L1 L2 S ⊔ M with hNdef
  have hQN : Q2 L1 L2 S ≤ N := le_sup_left
  have hNS : N ≤ S := sup_le F.Q2_le_S (hMQ1.trans F.Q1_le_S)
  have hDN : ∀ d ∈ D, ∀ n ∈ N, d * n * d⁻¹ ∈ N := by
    intro d hd n hn
    have hdP2 : d ∈ P2 L1 L2 S := (le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (F.D_le_B hd)
    have h2 : conjSub d (Q2 L1 L2 S) = Q2 L1 L2 S :=
      conjSub_eq_of_mem_normalizer (P2_le_normalizer_Q2 L1 L2 S hdP2)
    have : conjSub d N = N := by rw [hNdef, conjSub_sup, h2, hDM d hd]
    rw [← this]
    exact mem_conjSub_of_mem' hn
  rcases eq_or_eq_of_D_invariant F hQN hNS hDN with hN | hN
  ·
    exfalso
    have hMK : M ≤ K := le_inf hMQ1 (le_sup_right.trans hN.le)
    have hle : conjSub q K ≤ K := le_sup_right.trans hMK
    have heq : conjSub q K = K :=
      Subgroup.eq_of_le_of_card_ge hle (card_conjSub q K).ge
    have hqN : q ∈ Subgroup.normalizer ((K : Subgroup G) : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        have : q * y * q⁻¹ ∈ conjSub q K := mem_conjSub_of_mem' hy
        rwa [heq] at this
      · intro hy
        rw [← heq] at hy
        have := mem_conjSub.mp hy
        simpa [mul_assoc] using this
    have hBK : bigB L1 L2 S ≤ Subgroup.normalizer ((K : Subgroup G) : Set G) :=
      le_normalizer_inf ((le_sup_right : bigB L1 L2 S ≤ P1 L1 L2 S).trans hN1)
        ((le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S).trans (P2_le_normalizer_Q2 L1 L2 S))
    rcases eq_or_eq_B_P1 F (H := Subgroup.normalizer ((K : Subgroup G) : Set G) ⊓ P1 L1 L2 S)
        (le_inf hBK le_sup_right) inf_le_right with h | h
    · exact hqB (h ▸ (⟨hqN, hq⟩ : q ∈ Subgroup.normalizer ((K : Subgroup G) : Set G) ⊓ P1 L1 L2 S))
    · exact hPU (h ▸ inf_le_left)
  · refine le_antisymm hMQ1 (fun x hx => ?_)
    have hxS : x ∈ N := by rw [hN]; exact F.Q1_le_S hx
    obtain ⟨a, ha, b, hb, hab⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hMN2).mp hxS
    have haQ1 : a ∈ Q1 L1 L2 S := by
      have : a = x * b⁻¹ := by rw [hab]; group
      rw [this]; exact (Q1 L1 L2 S).mul_mem hx ((Q1 L1 L2 S).inv_mem (hMQ1 hb))
    have haM : a ∈ M := le_sup_left (a := K) (b := conjSub q K) ⟨haQ1, ha⟩
    rw [hab]
    exact M.mul_mem haM hb

end CFSG.Quasithin.Kleidman.F204
