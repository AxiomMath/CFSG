module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem528BEmb
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem le_normalizer_sup_of_normalizes {A B C : Subgroup G} (hA : C ≤ Subgroup.normalizer (A : Set G))
    (hB : C ≤ Subgroup.normalizer (B : Set G)) :
    C ≤ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := fun c hc => by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq] at *
  rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hc),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hB hc)]

omit [Finite G] in
theorem commutator_le_of_sup_center {W Z Q : Subgroup G} (hQ : W ⊔ Z = Q)
    (hZ : Z ≤ Subgroup.centralizer (Q : Set G)) (hQW : Q ≤ Subgroup.normalizer (W : Set G)) :
    ⁅Q, Q⁆ ≤ W := by
  let S : Subgroup G :=
    { carrier := {a | a ∈ Q ∧ ∀ b ∈ Q, ⁅a, b⁆ ∈ W}
      one_mem' := ⟨Q.one_mem, fun b _ => by rw [commutatorElement_one_left]; exact W.one_mem⟩
      mul_mem' := fun {a₁ a₂} h₁ h₂ => ⟨Q.mul_mem h₁.1 h₂.1, fun b hb => by
        have e : ⁅a₁ * a₂, b⁆ = a₁ * ⁅a₂, b⁆ * a₁⁻¹ * ⁅a₁, b⁆ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact W.mul_mem ((Subgroup.mem_normalizer_iff.mp (hQW h₁.1) _).mp (h₂.2 b hb))
          (h₁.2 b hb)⟩
      inv_mem' := fun {a} h => ⟨Q.inv_mem h.1, fun b hb => by
        have e : ⁅a⁻¹, b⁆ = a⁻¹ * ⁅a, b⁆⁻¹ * a⁻¹⁻¹ := by
          simp only [commutatorElement_def]; group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (hQW (Q.inv_mem h.1)) _).mp
          (W.inv_mem (h.2 b hb))⟩ }
  have hWS : W ≤ S := fun w hw => by
    have hwQ : w ∈ Q := hQ ▸ (le_sup_left : W ≤ W ⊔ Z) hw
    refine ⟨hwQ, fun b hb => ?_⟩
    rw [commutatorElement_def, show w * b * w⁻¹ * b⁻¹ = w * (b * w⁻¹ * b⁻¹) by group]
    exact W.mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hQW hb) _).mp (W.inv_mem hw))
  have hZS : Z ≤ S := fun z hz => by
    have hzQ : z ∈ Q := hQ ▸ (le_sup_right : Z ≤ W ⊔ Z) hz
    refine ⟨hzQ, fun b hb => ?_⟩
    have hc : b * z = z * b := Subgroup.mem_centralizer_iff.mp (hZ hz) b hb
    rw [commutatorElement_def, show z * b * z⁻¹ * b⁻¹ = (z * b) * z⁻¹ * b⁻¹ from rfl, ← hc]
    simp only [mul_inv_cancel_right, mul_inv_cancel]
    exact W.one_mem
  have hQS : Q ≤ S := hQ ▸ sup_le hWS hZS
  rw [Subgroup.commutator_le]
  intro a ha b hb
  exact (hQS ha).2 b hb

namespace Emb528

variable {T K Kh : Subgroup G}

theorem not_isPGroup (e : Emb528 T K Kh) : ¬ IsPGroup 2 K := by
  intro hp
  have hperf : Group.IsPerfect ↥K := Subgroup.isPerfect_iff.mpr e.locK.2.1.2.1
  have hnt : Nontrivial ↥K := by
    rw [Subgroup.nontrivial_iff_ne_bot]
    exact e.locK.2.1.1
  have := Fintype.ofFinite G
  have : Group.IsNilpotent ↥K := hp.isNilpotent
  exact Group.IsPerfect.not_isNilpotent ↥K inferInstance

theorem charTwo_Kh (e : Emb528 T K Kh) (h37 : A37ForSQTK) : CharTwo Kh :=
  CharTwo.of_normal e.charTwo le_sup_left
    ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (e.sup_le_normalizer h37))

theorem le_pCoreOf_of_irred (e : Emb528 T K Kh) (h37 : A37ForSQTK)
    (hQQ : ⁅pCoreOf 2 K, pCoreOf 2 K⁆ = centerOf (pCoreOf 2 K))
    (hcent : K ≤ Subgroup.centralizer (centerOf (pCoreOf 2 K) : Set G))
    (hirr : ∀ W : Subgroup G, centerOf (pCoreOf 2 K) ≤ W → W ≤ pCoreOf 2 K →
      K ≤ Subgroup.normalizer (W : Set G) → W = centerOf (pCoreOf 2 K) ∨ W = pCoreOf 2 K) :
    pCoreOf 2 K ≤ pCoreOf 2 Kh := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 K with hQ
  set Z := centerOf Q with hZ
  set W := ⁅pCoreOf 2 (Kh ⊔ T), K⁆ with hW
  have hWQ : W ≤ Q := e.commutator_le_inf.trans e.inf_le_blockQ
  have hWW : ⁅W, K⁆ = W := e.commutator_commutator
  have hW1 : W ≠ ⊥ := e.commutator_ne_bot
  have hKW : K ≤ Subgroup.normalizer (W : Set G) :=
    le_normalizer_commutator_of e.K_le_normalizer Subgroup.le_normalizer
  have hZQ : Z ≤ Q := inf_le_left
  have hKZ : K ≤ Subgroup.normalizer (Z : Set G) :=
    hcent.trans (Subgroup.centralizer_le_normalizer _)
  have hQK : Q ≤ K := pCoreOf_le 2 K
  rcases hirr (W ⊔ Z) le_sup_right (sup_le hWQ hZQ) (le_normalizer_sup_of_normalizes hKW hKZ) with h | h
  ·
    exfalso
    apply hW1
    have hWZ : W ≤ Z := h ▸ le_sup_left
    rw [← hWW, eq_bot_iff, Subgroup.commutator_le]
    intro w hw k hk
    have hc : w * k = k * w := Subgroup.mem_centralizer_iff.mp (hcent hk) w (hWZ hw)
    rw [Subgroup.mem_bot, commutatorElement_def, hc]
    group
  ·
    have hZcent : Z ≤ Subgroup.centralizer (Q : Set G) := fun z hz =>
      Subgroup.mem_centralizer_iff.mpr fun q hq =>
        (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz).2 q hq)
    have hQW : Q ≤ Subgroup.normalizer (W : Set G) := hQK.trans hKW
    have hZW : Z ≤ W := by
      rw [← hQQ]
      exact commutator_le_of_sup_center h hZcent hQW
    have hQW' : Q ≤ W := h ▸ sup_le le_rfl hZW
    rw [← e.inf_pCoreOf_eq h37]
    exact le_inf (hQK.trans e.le) (hQW'.trans (e.commutator_le_inf.trans inf_le_right))

end Emb528

theorem le_of_stabilizes {Kh Q : Subgroup G}
    (hchar : Kh ⊓ Subgroup.centralizer (pCoreOf 2 Kh : Set G) ≤ pCoreOf 2 Kh) (hQ : Q ≤ Kh)
    (h1 : Q ≤ Subgroup.centralizer (centerOf (pCoreOf 2 Kh) : Set G))
    (h2 : ∀ q ∈ Q, ∀ r ∈ pCoreOf 2 Kh, q * r * q⁻¹ * r⁻¹ ∈ centerOf (pCoreOf 2 Kh)) :
    Q ≤ pCoreOf 2 Kh := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set R := pCoreOf 2 Kh with hR
  set C := centerOf R with hC
  have hCR : C ≤ R := inf_le_left
  have hKhR : Kh ≤ Subgroup.normalizer (R : Set G) := le_normalizer_pCoreOf 2 Kh
  have hR2 : IsPGroup 2 R := pCoreOf_isPGroup 2 Kh
  have hKhC : ∀ k ∈ Kh, ∀ c ∈ C, k * c * k⁻¹ ∈ C := by
    intro k hk c hc
    obtain ⟨hcR, hcc⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨(Subgroup.mem_normalizer_iff.mp (hKhR hk) c).mp hcR,
      Subgroup.mem_centralizer_iff.mpr fun r hr => ?_⟩
    have hr' : k⁻¹ * r * k ∈ R := by
      have := (Subgroup.mem_normalizer_iff.mp (hKhR (Kh.inv_mem hk)) r).mp hr
      simpa using this
    have h3 := Subgroup.mem_centralizer_iff.mp hcc _ hr'
    calc r * (k * c * k⁻¹) = k * ((k⁻¹ * r * k) * c) * k⁻¹ := by group
      _ = k * (c * (k⁻¹ * r * k)) * k⁻¹ := by rw [h3]
      _ = k * c * k⁻¹ * r := by group
  let A : Subgroup G :=
    { carrier := {g | g ∈ Kh ∧ (∀ c ∈ C, g * c * g⁻¹ = c) ∧ ∀ r ∈ R, g * r * g⁻¹ * r⁻¹ ∈ C}
      one_mem' := ⟨Kh.one_mem, fun c _ => by group, fun r _ => by
        rw [show (1 : G) * r * 1⁻¹ * r⁻¹ = 1 by group]; exact C.one_mem⟩
      mul_mem' := fun {g h} hg hh => ⟨Kh.mul_mem hg.1 hh.1, fun c hc => by
          rw [show g * h * c * (g * h)⁻¹ = g * (h * c * h⁻¹) * g⁻¹ by group, hh.2.1 c hc,
            hg.2.1 c hc], fun r hr => by
          set c := h * r * h⁻¹ * r⁻¹ with hc
          have hcC : c ∈ C := hh.2.2 r hr
          have e : g * h * r * (g * h)⁻¹ * r⁻¹ = (g * c * g⁻¹) * (g * r * g⁻¹ * r⁻¹) := by
            rw [hc]; group
          rw [e, hg.2.1 c hcC]
          exact C.mul_mem hcC (hg.2.2 r hr)⟩
      inv_mem' := fun {g} hg => ⟨Kh.inv_mem hg.1, fun c hc => by
          have h3 := hg.2.1 c hc
          calc g⁻¹ * c * g⁻¹⁻¹ = g⁻¹ * (g * c * g⁻¹) * g := by rw [inv_inv, h3]
            _ = c := by group, fun r hr => by
          have hs : g⁻¹ * r * g ∈ R := by
            have := (Subgroup.mem_normalizer_iff.mp (hKhR (Kh.inv_mem hg.1)) r).mp hr
            simpa using this
          have h3 := hg.2.2 _ hs
          have e : g⁻¹ * r * g⁻¹⁻¹ * r⁻¹ = (g * (g⁻¹ * r * g) * g⁻¹ * (g⁻¹ * r * g)⁻¹)⁻¹ := by
            group
          rw [e]
          exact C.inv_mem h3⟩ }
  have hAKh : A ≤ Kh := fun g hg => hg.1
  have hKhA : Kh ≤ Subgroup.normalizer (A : Set G) := by
    intro k hk
    rw [Subgroup.mem_normalizer_iff]
    intro g
    have key : ∀ k ∈ Kh, ∀ g ∈ A, k * g * k⁻¹ ∈ A := by
      intro k hk g hg
      refine ⟨Kh.mul_mem (Kh.mul_mem hk hg.1) (Kh.inv_mem hk), fun c hc => ?_, fun r hr => ?_⟩
      · have hc' : k⁻¹ * c * k ∈ C := by
          have := hKhC k⁻¹ (Kh.inv_mem hk) c hc
          simpa using this
        have h3 := hg.2.1 _ hc'
        calc k * g * k⁻¹ * c * (k * g * k⁻¹)⁻¹ = k * (g * (k⁻¹ * c * k) * g⁻¹) * k⁻¹ := by group
          _ = c := by rw [h3]; group
      · have hr' : k⁻¹ * r * k ∈ R := by
          have := (Subgroup.mem_normalizer_iff.mp (hKhR (Kh.inv_mem hk)) r).mp hr
          simpa using this
        have h3 := hg.2.2 _ hr'
        have h4 := hKhC k hk _ h3
        have e : k * g * k⁻¹ * r * (k * g * k⁻¹)⁻¹ * r⁻¹ =
            k * (g * (k⁻¹ * r * k) * g⁻¹ * (k⁻¹ * r * k)⁻¹) * k⁻¹ := by group
        rw [e]
        exact h4
    constructor
    · exact key k hk g
    · intro hg
      have := key k⁻¹ (Kh.inv_mem hk) _ hg
      simpa [mul_assoc] using this
  have hA2 : IsPGroup 2 A := by
    intro g
    obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
    refine ⟨a, ?_⟩
    set h := g ^ 2 ^ a with hh
    have hhb : h ^ b = 1 := by rw [hh, ← pow_mul, ← hab, pow_orderOf_eq_one]
    have hhA : (h : G) ∈ A := h.2
    have hcent : ∀ r ∈ R, (h : G) * r = r * h := by
      intro r hr
      set c := (h : G) * r * (h : G)⁻¹ * r⁻¹ with hc
      have hcC : c ∈ C := hhA.2.2 r hr
      have hpow : ∀ j : ℕ, (h : G) ^ j * r * ((h : G) ^ j)⁻¹ = c ^ j * r := by
        intro j
        induction j with
        | zero => simp
        | succ j ih =>
          have hhc : (h : G) * c ^ j * (h : G)⁻¹ = c ^ j := by
            rw [← conj_pow, hhA.2.1 c hcC]
          have hcr : c * r = (h : G) * r * (h : G)⁻¹ := by rw [hc]; group
          calc (h : G) ^ (j + 1) * r * ((h : G) ^ (j + 1))⁻¹ =
              (h : G) * ((h : G) ^ j * r * ((h : G) ^ j)⁻¹) * (h : G)⁻¹ := by group
            _ = ((h : G) * c ^ j * (h : G)⁻¹) * ((h : G) * r * (h : G)⁻¹) := by rw [ih]; group
            _ = c ^ (j + 1) * r := by rw [hhc, pow_succ, mul_assoc (c ^ j) c r, hcr]
      have h1b : ((h : G)) ^ b = 1 := by
        have := congrArg Subtype.val hhb
        simpa using this
      have hcb : c ^ b = 1 := by
        have := hpow b
        rw [h1b, one_mul, inv_one, mul_one] at this
        exact (mul_eq_right.mp this.symm)
      obtain ⟨t, ht⟩ := hR2 ⟨c, hCR hcC⟩
      have ht' : c ^ 2 ^ t = 1 := by
        have := congrArg Subtype.val ht
        simpa using this
      have hc1 : c = 1 := by
        have hd : orderOf c ∣ Nat.gcd (2 ^ t) b :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ht') (orderOf_dvd_of_pow_eq_one hcb)
        have hg1 : Nat.gcd (2 ^ t) b = 1 :=
          Nat.Coprime.pow_left t (Nat.coprime_two_left.mpr hb)
        rw [hg1, Nat.dvd_one, orderOf_eq_one_iff] at hd
        exact hd
      have : (h : G) * r * (h : G)⁻¹ * r⁻¹ = 1 := hc1
      calc (h : G) * r = ((h : G) * r * (h : G)⁻¹ * r⁻¹) * r * h := by group
        _ = r * h := by rw [this, one_mul]
    have hhR : (h : G) ∈ R := hchar (Subgroup.mem_inf.mpr ⟨hhA.1,
      Subgroup.mem_centralizer_iff.mpr fun r hr => (hcent r hr).symm⟩)
    obtain ⟨s, hs⟩ := hR2 ⟨h, hhR⟩
    have hs' : (h : G) ^ 2 ^ s = 1 := by
      have := congrArg Subtype.val hs
      simpa using this
    have h1b : (h : G) ^ b = 1 := by
      have := congrArg Subtype.val hhb
      simpa using this
    have hd : orderOf (h : G) ∣ Nat.gcd (2 ^ s) b :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hs') (orderOf_dvd_of_pow_eq_one h1b)
    rw [Nat.Coprime.pow_left s (Nat.coprime_two_left.mpr hb), Nat.dvd_one,
      orderOf_eq_one_iff] at hd
    exact Subtype.ext hd
  have hAR : A ≤ R := le_pCoreOf_of_le_normalizer 2 hAKh hKhA hA2
  intro q hq
  refine hAR ⟨hQ hq, fun c hc => ?_, h2 q hq⟩
  have := Subgroup.mem_centralizer_iff.mp (h1 hq) c hc
  rw [← this]
  group

end CFSG.Quasithin.H13
