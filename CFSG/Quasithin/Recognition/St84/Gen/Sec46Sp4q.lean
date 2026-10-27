module

public import CFSG.Quasithin.Recognition.St84.Gen.Sec46Sp4qStep10


public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86 CFSG.GH74.QTGen4.DSGen4
open scoped commutatorElement Pointwise

variable {V : Type*} {G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Setup

variable {X : Setup Γ G}

theorem CaseBGen.commutator_Z_S (B : X.CaseBGen) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    ⁅X.Z i, X.S⁆ = ⁅X.Z 0, X.Z 1⁆ := by
  have hj : 1 - i = 0 ∨ 1 - i = 1 := by rcases hi with rfl | rfl <;> simp
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro z hz s hs
    obtain ⟨y, hy, a, ha, rfl⟩ := B.mem_mul_of_mem_S hj hs
    rw [sub_sub_cancel] at ha
    have hza : z * a = a * z :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (X.Z_le_center i hz)).2 a ha).symm
    have he : ⁅z, y * a⁆ = ⁅z, y⁆ := by
      rw [commutatorElement_def, commutatorElement_def,
        show z * (y * a) * z⁻¹ * (y * a)⁻¹ = z * y * (a * z⁻¹) * a⁻¹ * y⁻¹ by group,
        show a * z⁻¹ = z⁻¹ * a by
          rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hza, ← mul_assoc, inv_mul_cancel, one_mul]]
      group
    rw [he]
    rcases hi with rfl | rfl
    · exact Subgroup.commutator_mem_commutator hz hy
    · rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hz (by simpa using hy)
  · rcases hi with rfl | rfl
    · exact Subgroup.commutator_mono le_rfl (B.Z_le_S (Or.inr rfl))
    · rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono le_rfl (B.Z_le_S (Or.inl rfl))

theorem CaseBGen.relCent_eq (B : X.CaseBGen) (h8 : X.CaseBStep8) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    relCent (X.Z i) (centerOf (X.L i)) X.S = ⁅X.Z 0, X.Z 1⁆ ⊔ centerOf (X.L i) := by
  rw [← (h8.nat i hi).comm_eq X.S (X.isSylowTwoOf_S_L hi), B.commutator_Z_S hi]

private theorem s46sp4q_K_le_normalizer_R (X : Setup Γ G) :
    X.K ≤ Subgroup.normalizer ((⁅X.Z 0, X.Z 1⁆ : Subgroup G) : Set G) := by
  intro k hk
  have hK : ∀ j : ℤ, k ∈ Subgroup.normalizer (X.Z j : Set G) := fun j =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (X.Z_normal j k (X.K_le_Gi j hk))
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK 0),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (hK 1)]

private theorem s46sp4q_not_mem_Q (X : Setup Γ G) (i : ℤ) {k : G} (hodd : Odd (orderOf k))
    (hk1 : k ≠ 1) : k ∉ X.Q i := by
  intro hkQ
  obtain ⟨e, he⟩ := (pCoreOf_isPGroup' (X.Gi i)) ⟨k, hkQ⟩
  have h2 : orderOf k ∣ 2 ^ e :=
    orderOf_dvd_of_pow_eq_one (by simpa using congrArg Subtype.val he)
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rcases m with _ | m
  · exact hk1 (orderOf_eq_one_iff.mp (by simpa using hm))
  · exact (Nat.not_even_iff_odd.mpr hodd)
      (even_iff_two_dvd.mpr (hm ▸ dvd_pow_self 2 (Nat.succ_ne_zero m)))

theorem CaseBGen.center_le_R (B : X.CaseBGen) (h8 : X.CaseBStep8) {i : ℤ}
    (hi : i = 0 ∨ i = 1) : centerOf (X.L (1 - i)) ≤ ⁅X.Z 0, X.Z 1⁆ := by
  classical
  have hj : 1 - i = 0 ∨ 1 - i = 1 := by rcases hi with rfl | rfl <;> simp
  obtain ⟨hQZ, -, -⟩ := B.Q_eq_Z h8 hi
  have hnatQ : NatQuot (X.L i) (X.Q i) (centerOf (X.L i)) (X.n i) := hQZ ▸ h8.nat i hi
  have hZLjQi : centerOf (X.L (1 - i)) ≤ X.Q i := by
    rcases hi with rfl | rfl
    · simpa using (X.centerOf_L_le_Q_adj B.char 0).1
    · simpa using (X.centerOf_L_le_Q_adj B.char 0).2
  have hZLjQj : centerOf (X.L (1 - i)) ≤ X.Q (1 - i) :=
    (X.centerOf_L_le_Z B.char (1 - i)).trans (X.Z_le_Q (1 - i))
  have hZLinf : centerOf (X.L i) ⊓ centerOf (X.L (1 - i)) = ⊥ := by
    have h := X.centerOf_L_inf_succ B.char 0
    rcases hi with rfl | rfl
    · simpa using h
    · simpa [inf_comm] using h
  have hQinf : X.Q i ⊓ X.Q (1 - i) = ⁅X.Z 0, X.Z 1⁆ ⊔ centerOf (X.L i) := by
    rw [← B.relCent_eq h8 hi, ← h8.inf_Q i hi, hQZ]
  obtain ⟨⟨k, hkKi⟩, hk1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp (X.Ki_ne_bot i (B.two_le_n i))
  have hk1' : k ≠ 1 := fun h => hk1 (Subtype.ext h)
  have hkK : k ∈ X.K := (Subgroup.mem_inf.mp hkKi).1
  have hkL : k ∈ X.L i := (Subgroup.mem_inf.mp hkKi).2
  have hkodd : Odd (orderOf k) :=
    Odd.of_dvd_nat (X.odd_card_Ki i (by have := B.two_le_n i; omega))
      (Subgroup.orderOf_dvd_natCard (X.Ki i) hkKi)
  have hknotQ := s46sp4q_not_mem_Q X i hkodd hk1'
  have hkN : k ∈ Subgroup.normalizer (centerOf (X.L (1 - i)) : Set G) :=
    X.Gi_le_normalizer_centerOf_L (1 - i) (X.K_le_Gi (1 - i) hkK)
  have hkR := s46sp4q_K_le_normalizer_R X hkK
  have hRQi : ⁅X.Z 0, X.Z 1⁆ ≤ X.Q i := by
    rcases hi with rfl | rfl
    · exact (B.R_le.trans inf_le_left).trans (X.Z_le_Q 0)
    · exact (B.R_le.trans inf_le_right).trans (X.Z_le_Q 1)
  have hRnorm : ⁅X.Z 0, X.Z 1⁆ ≤ Subgroup.normalizer (centerOf (X.L i) : Set G) :=
    (hRQi.trans ((X.Q_le_L i).trans (X.L_le_Gi i))).trans (X.Gi_le_normalizer_centerOf_L i)
  have hcoe := Subgroup.coe_mul_of_left_le_normalizer_right _ _ hRnorm
  have hchar : ∀ b ∈ centerOf (X.L (1 - i)), ⁅b, k⁆ ∈ ⁅X.Z 0, X.Z 1⁆ := by
    intro b hb
    have hbInf : b ∈ ((⁅X.Z 0, X.Z 1⁆ ⊔ centerOf (X.L i) : Subgroup G) : Set G) := by
      rw [← hQinf]
      exact Subgroup.mem_inf.mpr ⟨hZLjQi hb, hZLjQj hb⟩
    rw [hcoe] at hbInf
    obtain ⟨r, hr, a, ha, rfl⟩ := hbInf
    have hak : a * k = k * a :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp ha).2 k hkL).symm
    have he : ⁅r * a, k⁆ = ⁅r, k⁆ := by
      rw [commutatorElement_def, commutatorElement_def,
        show r * a * k * (r * a)⁻¹ * k⁻¹ = r * (a * k) * a⁻¹ * r⁻¹ * k⁻¹ by group, hak]
      group
    rw [he, commutatorElement_def]
    have hkr : k * r⁻¹ * k⁻¹ ∈ ⁅X.Z 0, X.Z 1⁆ :=
      (Subgroup.mem_normalizer_iff.mp hkR r⁻¹).mp (inv_mem hr)
    rw [show r * k * r⁻¹ * k⁻¹ = r * (k * r⁻¹ * k⁻¹) by group]
    exact mul_mem hr hkr
  have hinj : ∀ b₁ ∈ centerOf (X.L (1 - i)), ∀ b₂ ∈ centerOf (X.L (1 - i)),
      ⁅b₁, k⁆ = ⁅b₂, k⁆ → b₁ = b₂ := by
    intro b1 hb1 b2 hb2 heq
    have hcomm : (b2⁻¹ * b1) * k = k * (b2⁻¹ * b1) := by
      have h1 : b1 * k * b1⁻¹ = b2 * k * b2⁻¹ := by
        have := congrArg (· * k) heq
        simpa [commutatorElement_def, mul_assoc] using this
      have := congrArg (fun x => b2⁻¹ * x * b1) h1
      simpa [mul_assoc] using this
    have hu : b2⁻¹ * b1 ∈ centerOf (X.L (1 - i)) := mul_mem (inv_mem hb2) hb1
    have huZi : b2⁻¹ * b1 ∈ centerOf (X.L i) := by
      refine hnatQ.fpf k hkL hkodd hknotQ (b2⁻¹ * b1) (hZLjQi hu) ?_
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
      exact one_mem _
    have hu1 : b2⁻¹ * b1 = 1 := by
      have h : b2⁻¹ * b1 ∈ centerOf (X.L i) ⊓ centerOf (X.L (1 - i)) :=
        Subgroup.mem_inf.mpr ⟨huZi, hu⟩
      rw [hZLinf] at h
      exact Subgroup.mem_bot.mp h
    calc b1 = b2 * (b2⁻¹ * b1) := by group
      _ = b2 := by rw [hu1, mul_one]
  haveI : Finite ↥(centerOf (X.L (1 - i))) := finite_of_le_stabilizer X.hyp
    (H := centerOf (X.L (1 - i))) ((X.centerOf_L_le_Z B.char (1 - i)).trans (X.Z_le_Gi (1 - i)))
  have hmemZ : ∀ b ∈ centerOf (X.L (1 - i)), ⁅b, k⁆ ∈ centerOf (X.L (1 - i)) := by
    intro b hb
    rw [commutatorElement_def, show b * k * b⁻¹ * k⁻¹ = b * (k * b⁻¹ * k⁻¹) by group]
    exact mul_mem hb ((Subgroup.mem_normalizer_iff.mp hkN b⁻¹).mp (inv_mem hb))
  let f : ↥(centerOf (X.L (1 - i))) → ↥(centerOf (X.L (1 - i))) := fun b =>
    ⟨⁅(b : G), k⁆, hmemZ (b : G) b.2⟩
  have hfinj : Function.Injective f := fun b1 b2 h =>
    Subtype.ext (hinj (b1 : G) b1.2 (b2 : G) b2.2 (congrArg Subtype.val h))
  have hfsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hfinj
  intro b hb
  obtain ⟨b', hb'⟩ := hfsurj ⟨b, hb⟩
  have hbeq : b = ⁅(b' : G), k⁆ := by
    have h := congrArg Subtype.val hb'
    exact h.symm
  rw [hbeq]
  exact hchar (b' : G) b'.2

private theorem s46sp4q_commutator_le_Q (X : Setup Γ G) (i : ℤ) : ⁅X.Q i, X.L i⁆ ≤ X.Q i := by
  have hLQ : X.L i ≤ Subgroup.normalizer (X.Q i : Set G) :=
    (X.L_le_Gi i).trans (X.Gi_le_normalizer_L_Q_Z i).2.1
  rw [Subgroup.commutator_le]
  intro x hx l hl
  rw [commutatorElement_def, show x * l * x⁻¹ * l⁻¹ = x * (l * x⁻¹ * l⁻¹) by group]
  exact mul_mem hx ((Subgroup.mem_normalizer_iff.mp (hLQ hl) x⁻¹).mp (inv_mem hx))

theorem CaseBGen.indec (B : X.CaseBGen) (h8 : X.CaseBStep8) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    ⁅X.Q i, X.L i⁆ = X.Q i := by
  have hj : 1 - i = 0 ∨ 1 - i = 1 := by rcases hi with rfl | rfl <;> simp
  obtain ⟨hQZ, -, -⟩ := B.Q_eq_Z h8 hi
  have hnatQ : NatQuot (X.L i) (X.Q i) (centerOf (X.L i)) (X.n i) := hQZ ▸ h8.nat i hi
  have hZLR : centerOf (X.L i) ≤ ⁅X.Z 0, X.Z 1⁆ := by
    have h := B.center_le_R h8 hj
    rwa [sub_sub_cancel] at h
  have hRcomm : ⁅X.Z 0, X.Z 1⁆ ≤ ⁅X.Q i, X.L i⁆ := by
    rcases hi with rfl | rfl
    · exact Subgroup.commutator_mono (X.Z_le_Q 0) (by simpa using B.Z_le_L (Or.inl rfl))
    · rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mono (X.Z_le_Q 1) (by simpa using B.Z_le_L (Or.inr rfl))
  have hZLc : centerOf (X.L i) ≤ ⁅X.Q i, X.L i⁆ := hZLR.trans hRcomm
  have hcommQ := s46sp4q_commutator_le_Q X i
  have hZLQ : centerOf (X.L i) ≤ X.Q i := (X.centerOf_L_le_Z B.char i).trans (X.Z_le_Q i)
  have hLQ : X.L i ≤ Subgroup.normalizer (X.Q i : Set G) :=
    (X.L_le_Gi i).trans (X.Gi_le_normalizer_L_Q_Z i).2.1
  have hnorm : X.L i ≤
      Subgroup.normalizer ((⁅X.Q i, X.L i⁆ ⊔ centerOf (X.L i) : Subgroup G) : Set G) := by
    intro l hl
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_sup, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hLQ hl),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hl),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp
        (X.Gi_le_normalizer_centerOf_L i (X.L_le_Gi i hl))]
  rcases hnatQ.irred _ le_sup_right (sup_le hcommQ hZLQ) hnorm with hZ | hQ
  · exfalso
    have hrel : relCent (X.Q i) (centerOf (X.L i)) X.S = X.Q i := by
      refine le_antisymm (fun _ h => h.1) fun x hx =>
        (mem_relCent ((X.Q_le_L i).trans (X.L_le_Gi i) |>.trans
          (X.Gi_le_normalizer_centerOf_L i))).mpr ⟨hx, fun s hs => ?_⟩
      rw [← hZ]
      exact Subgroup.mem_sup_left
        (Subgroup.commutator_mem_commutator hx ((X.isSylowTwoOf_S_L hi).1 hs))
    have hline := hnatQ.line X.S (X.isSylowTwoOf_S_L hi)
    rw [hrel, hnatQ.index] at hline
    have h2 := Nat.pow_right_injective le_rfl hline
    have := B.two_le_n i
    omega
  · rw [sup_eq_left.mpr hZLc] at hQ
    exact hQ

theorem CaseBGen.elem_Q (B : X.CaseBGen) (h8 : X.CaseBStep8) {i : ℤ} (hi : i = 0 ∨ i = 1) :
    IsElemAbelian 2 (X.Q i) := by
  obtain ⟨hQZ, -, -⟩ := B.Q_eq_Z h8 hi
  have hcomm := B.Q_comm h8 hi
  have hsec := h8.sec i hi
  have hLQ : X.L i ≤ Subgroup.normalizer (X.Q i : Set G) :=
    (X.L_le_Gi i).trans (X.Gi_le_normalizer_L_Q_Z i).2.1
  have hT : ⁅X.Q i, X.L i⁆ ≤
      { carrier := {y : G | y ∈ X.Q i ∧ y ^ 2 = 1}
        one_mem' := ⟨one_mem _, by simp⟩
        mul_mem' := by
          rintro a b ⟨ha, ha2⟩ ⟨hb, hb2⟩
          exact ⟨mul_mem ha hb, by rw [Commute.mul_pow (hcomm a ha b hb) 2, ha2, hb2, mul_one]⟩
        inv_mem' := by
          rintro a ⟨ha, ha2⟩
          exact ⟨inv_mem ha, by rw [inv_pow, ha2, inv_one]⟩ } := by
    rw [Subgroup.commutator_le]
    intro x hx l hl
    refine ⟨s46sp4q_commutator_le_Q X i (Subgroup.commutator_mem_commutator hx hl), ?_⟩
    have hw : l * x * l⁻¹ ∈ X.Q i := (Subgroup.mem_normalizer_iff.mp (hLQ hl) x).mp hx
    have hx2 : x ^ 2 ∈ centerOf (X.L i) := hsec.2.2 x (hQZ ▸ hx)
    have hx2c : l * x ^ 2 * l⁻¹ = x ^ 2 := by
      have h := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx2).2 l hl
      rw [h, mul_inv_cancel_right]
    have he : ⁅x, l⁆ = x * (l * x * l⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [he, Commute.mul_pow (hcomm x hx _ (inv_mem hw)) 2, inv_pow, conj_pow, hx2c,
      mul_inv_cancel]
  have hsq : ∀ x ∈ X.Q i, x ^ 2 = 1 := fun x hx =>
    (hT (by rw [B.indec h8 hi]; exact hx)).2
  exact ⟨⟨⟨fun a b => Subtype.ext (hcomm _ a.2 _ b.2)⟩⟩, hsq⟩

theorem CaseBGen.card_Q_inf (B : X.CaseBGen) (hn : X.n 0 = X.n 1) :
    Nat.card ↥(X.Q 0 ⊓ X.Q 1) = 2 ^ (2 * X.n 0) := by
  haveI : Finite ↥(X.Gi 0 ⊓ X.Gi 1) :=
    finite_of_le_stabilizer X.hyp (H := X.Gi 0 ⊓ X.Gi 1) inf_le_left
  have hSP : X.S ≤ X.Gi 0 ⊓ X.Gi 1 :=
    le_inf (X.isSylowTwoOf_S_Gi (Or.inl rfl)).1 (X.isSylowTwoOf_S_Gi (Or.inr rfl)).1
  have hN : X.Q 0 ≤ Subgroup.normalizer (X.Q 1 : Set G) :=
    (X.Q_le_S (Or.inl rfl)).trans ((X.isSylowTwoOf_S_Gi (Or.inr rfl)).1.trans
      (X.Gi_le_normalizer_L_Q_Z 1).2.1)
  have h := card_sup_mul_card_inf_of_le_finite ((X.Q_le_S (Or.inl rfl)).trans hSP)
    ((X.Q_le_S (Or.inr rfl)).trans hSP) hN
  have h0 := B.card_Q (i := 0) (Or.inl rfl)
  have h1 := B.card_Q (i := 1) (Or.inr rfl)
  simp only [sub_zero, sub_self] at h0 h1
  rw [B.Q_sup_Q, B.card_S, h0, h1, ← hn] at h
  have e : 2 ^ (X.n 0 + 2 * X.n 0) * 2 ^ (X.n 0 + 2 * X.n 0) =
      2 ^ (2 * X.n 0 + 2 * X.n 0) * 2 ^ (2 * X.n 0) := by
    rw [← pow_add, ← pow_add]
    ring_nf
  exact Nat.eq_of_mul_eq_mul_left (by positivity) (h.trans e)

theorem CaseBGen.Ki_inf_eq_bot (B : X.CaseBGen) (h8 : X.CaseBStep8) : X.Ki 0 ⊓ X.Ki 1 = ⊥ := by
  have hZ0 : centerOf (X.L 0) ≤ X.Q 1 := by
    have h := B.center_le_R h8 (i := 1) (Or.inr rfl)
    rw [sub_self] at h
    exact h.trans (B.R_le.trans (inf_le_right.trans (X.Z_le_Q 1)))
  have hnat1 : NatQuot (X.L 1) (X.Q 1) (centerOf (X.L 1)) (X.n 1) := by
    have h := h8.nat 1 (Or.inr rfl)
    rwa [← (B.Q_eq_Z h8 (Or.inr rfl)).1] at h
  obtain ⟨u, hu, hu1⟩ : ∃ u ∈ centerOf (X.L 0), u ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have h := (B.Q_eq_Z h8 (Or.inl rfl)).2.2
    rw [(Subgroup.eq_bot_iff_forall _).mpr hcon, Subgroup.card_bot] at h
    have h2 : 2 ≤ 2 ^ X.n 0 := Nat.le_self_pow (by have := B.two_le_n 0; omega) 2
    omega
  rw [eq_bot_iff]
  intro k hk
  rw [Subgroup.mem_bot]
  by_contra hk1
  obtain ⟨hk0, hk1'⟩ := Subgroup.mem_inf.mp hk
  have hkodd : Odd (orderOf k) := Odd.of_dvd_nat
    (X.odd_card_Ki 1 (by have := B.two_le_n 1; omega)) (Subgroup.orderOf_dvd_natCard _ hk1')
  have hcomm : k * u = u * k := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hu).2 k
    ((inf_le_right : X.Ki 0 ≤ X.L 0) hk0)
  have hu' : u ∈ centerOf (X.L 1) := by
    refine hnat1.fpf k ((inf_le_right : X.Ki 1 ≤ X.L 1) hk1') hkodd
      (s46sp4q_not_mem_Q X 1 hkodd hk1) u (hZ0 hu) ?_
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm.symm]
    exact one_mem _
  have hinf := X.centerOf_L_inf_succ B.char 0
  rw [zero_add] at hinf
  have h : u ∈ centerOf (X.L 0) ⊓ centerOf (X.L 1) := Subgroup.mem_inf.mpr ⟨hu, hu'⟩
  rw [hinf] at h
  exact hu1 (Subgroup.mem_bot.mp h)

end Setup

end CFSG.Quasithin.St84

end
