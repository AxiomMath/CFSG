module

public import CFSG.Quasithin.Vol2.Ch6Sec1Lem5R2Omega

public section

namespace CFSG.Quasithin.H13.R2

open CFSG.Open
open scoped commutatorElement

variable {P : Type} [Group P] [Finite P]

theorem false_of_case1a {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (h9 : Nat.card (omegaCenter P) = 9) (hnc : ∃ g k : P, g * k ≠ k * g)
    (hcl2 : ∀ g k : P, ⁅g, k⁆ ∈ omegaCenter P) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := omegaCenter P with hZdef
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp h.p3
  obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (hk ▸ Group.exponent_dvd_nat_card (G := P))
  have hm2 : 2 ≤ m := by
    by_contra hlt
    obtain ⟨g, l, hgl⟩ := hnc
    have hall : ∀ g : P, g ∈ Z := fun g => mem_omegaCenter_of_pow_three h h9 (by
      have h1 := Monoid.pow_exponent_eq_one g
      rw [hm] at h1
      interval_cases m
      · simp at h1; rw [h1, one_pow]
      · simpa using h1)
    exact hgl (omegaCenter_central (hall g) l)
  obtain ⟨n, rfl⟩ : ∃ n, m = n + 1 := ⟨m - 1, by omega⟩
  have hn1 : 1 ≤ n := by omega
  have hcen : ∀ g l : P, ∀ k : P, ⁅l, g⁆ * k = k * ⁅l, g⁆ := fun g l k =>
    omegaCenter_central (hcl2 l g) k
  let θ : P →* P :=
    { toFun := fun g => g ^ 3 ^ n
      map_one' := one_pow _
      map_mul' := fun g l => by
        show (g * l) ^ 3 ^ n = g ^ 3 ^ n * l ^ 3 ^ n
        obtain ⟨t, ht⟩ := three_dvd_choose_two hn1
        rw [mul_pow_of_central (hcen g l), ht, pow_mul, (hcl2 l g).2, one_pow, mul_one] }
  have hθ : ∀ g, θ g = g ^ 3 ^ n := fun _ => rfl
  have hθZ : ∀ g, θ g ∈ Z := fun g => mem_omegaCenter_of_pow_three h h9 (by
    rw [hθ, ← pow_mul, ← pow_succ, ← hm]; exact Monoid.pow_exponent_eq_one g)
  have hθa : ∀ (φ : MulAut P) g, θ (φ g) = φ (θ g) := fun φ g => by rw [hθ, hθ, map_pow]
  have hker1 : frattini P ≤ θ.ker := by
    have := CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary (p := 3)
      (θ.codRestrict Z hθZ) (fun u v => Subtype.ext (omegaCenter_central u.2 v))
      (fun u => Subtype.ext u.2.2)
    rwa [MonoidHom.ker_codRestrict] at this
  have hkerne : θ.ker ≠ ⊤ := by
    intro htop
    have hdvd : Monoid.exponent P ∣ 3 ^ n :=
      Monoid.exponent_dvd_of_forall_pow_eq_one fun g => by
        have : g ∈ θ.ker := htop ▸ Subgroup.mem_top g
        exact this
    rw [hm] at hdvd
    exact absurd (Nat.le_of_dvd (by positivity) hdvd)
      (by rw [not_le]; exact Nat.pow_lt_pow_right (by norm_num) (by omega))
  have hker : θ.ker = frattini P := by
    rcases eq_frattini_or_top h hker1 (fun g hg => by
        rw [MonoidHom.mem_ker, hθa, MonoidHom.mem_ker.mp hg, map_one])
      (fun g hg => by rw [MonoidHom.mem_ker, hθa, MonoidHom.mem_ker.mp hg, map_one]) with
      he | ht
    · exact he
    · exact absurd ht hkerne
  have hrange : θ.range = Z := by
    have hle : θ.range ≤ Z := by rintro _ ⟨g, rfl⟩; exact hθZ g
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [h9, ← Subgroup.index_ker, hker, h.index]
  set c := ⁅x, y⁆ with hc
  have hc1 : c ≠ 1 := by
    intro h1
    obtain ⟨g, l, hgl⟩ := hnc
    exact hgl (comm_of_closure_pair h.gen (commutatorElement_eq_one_iff_mul_comm.mp h1) g l)
  have hΦZ : ∀ f ∈ frattini P, ∀ g : P, g * f = f * g := by
    intro f hf g
    have hcomm : ∀ l k' : P, ⁅g, l⁆ * k' = k' * ⁅g, l⁆ := fun l k' =>
      omegaCenter_central (hcl2 g l) k'
    have := CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary (p := 3)
      ((commHom g hcomm).codRestrict Z fun l => hcl2 g l)
      (fun u v => Subtype.ext (omegaCenter_central u.2 v)) (fun u => Subtype.ext u.2.2) hf
    rw [MonoidHom.mem_ker] at this
    have h1 : ⁅g, f⁆ = 1 := congrArg Subtype.val this
    exact commutatorElement_eq_one_iff_mul_comm.mp h1
  have hcentΦ : ∀ f ∈ frattini P, ∀ k' : P, f * k' = k' * f := fun f hf k' =>
    (hΦZ f hf k').symm
  have hac : a c = c⁻¹ := by
    have e1 : a x = (a x * x) * x⁻¹ := by group
    have e2 : a y = y * (y⁻¹ * a y) := by group
    rw [hc, map_commutatorElement, e1, e2, comm_central_mul_left (hcentΦ _ h.ax),
      comm_mul_central_right (hcentΦ _ h.ay), comm_inv_left_of_central (hcen y x)]
  have hsc : s c = c⁻¹ := by
    have e1 : s x = y * (y⁻¹ * s x) := by group
    have e2 : s y = x * (x⁻¹ * s y) := by group
    rw [hc, map_commutatorElement, e1, e2, comm_mul_central_right (hcentΦ _ h.sy)]
    rw [show ⁅y * (y⁻¹ * s x), x⁆ = ⁅(y⁻¹ * s x) * y, x⁆ by rw [hcentΦ _ h.sx y],
      comm_central_mul_left (hcentΦ _ h.sx), comm_swap]
  have hcZ : c ∈ θ.range := hrange ▸ hcl2 x y
  obtain ⟨g₀, hg₀⟩ := hcZ
  have hinv : ∀ φ : MulAut P, φ c = c⁻¹ → φ g₀ * g₀ ∈ frattini P := by
    intro φ hφ
    rw [← hker, MonoidHom.mem_ker, map_mul, hθa, hg₀, hφ, inv_mul_cancel]
  have hg₀Φ := mem_frattini_of_inv h (hinv a hac) (hinv s hsc)
  rw [← hker, MonoidHom.mem_ker, hg₀] at hg₀Φ
  exact hc1 hg₀Φ

theorem comm_comm_of_card_27 {Q : Type} [Group Q] [Finite Q] (h27 : Nat.card Q = 27)
    (u v w : Q) : ⁅⁅u, v⁆, w⁆ = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨k, hk0, hk⟩ := IsPGroup.card_center_eq_prime_pow (p := 3) (G := Q) (n := 3)
    (by rw [h27]; norm_num) (by norm_num)
  have hcard : Nat.card (Q ⧸ Subgroup.center Q) * Nat.card (Subgroup.center Q) = 27 := by
    rw [← h27, Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center Q)]
  have hd : Nat.card (Q ⧸ Subgroup.center Q) ∣ 3 ^ 2 := by
    have h1 : Nat.card (Q ⧸ Subgroup.center Q) * 3 ∣ 3 ^ 2 * 3 := by
      rw [show 3 ^ 2 * 3 = 27 by norm_num, ← hcard, hk]
      exact Nat.mul_dvd_mul_left _ (dvd_pow_self 3 hk0.ne')
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h1
  have hcomm : ∀ q q' : Q ⧸ Subgroup.center Q, q * q' = q' * q := by
    obtain ⟨i, hi, he⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hd
    have hi2 : i ≤ 2 := by
      have : 3 ^ i ≤ 3 ^ 2 := by rw [← he]; exact Nat.le_of_dvd (by positivity) hd
      exact (Nat.pow_le_pow_iff_right (by norm_num)).mp this
    interval_cases i
    · have : Subsingleton (Q ⧸ Subgroup.center Q) := by
        rw [pow_zero] at he
        exact (Nat.card_eq_one_iff_unique.mp he).1
      intro q q'
      exact Subsingleton.elim _ _
    · have : IsCyclic (Q ⧸ Subgroup.center Q) := isCyclic_of_prime_card (p := 3) (by simpa using he)
      let _ := IsCyclic.commGroup (α := Q ⧸ Subgroup.center Q)
      intro q q'
      exact mul_comm q q'
    · exact (IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 3) he).is_comm.comm
  have hab : ⁅u, v⁆ ∈ Subgroup.center Q := by
    have h1 : QuotientGroup.mk' (Subgroup.center Q) ⁅u, v⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm _ _
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  rw [commutatorElement_eq_one_iff_mul_comm]
  exact (Subgroup.mem_center_iff.mp hab w).symm

theorem frattini_le_center_of_exp3 {Q : Type} [Group Q] [Finite Q]
    (hcl : ∀ u v w : Q, ⁅⁅u, v⁆, w⁆ = 1) (h3 : ∀ q : Q, q ^ 3 = 1) :
    frattini Q ≤ Subgroup.center Q := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  intro f hf
  rw [Subgroup.mem_center_iff]
  intro g
  have hcen : ∀ l k : Q, ⁅g, l⁆ * k = k * ⁅g, l⁆ := fun l k =>
    commutatorElement_eq_one_iff_mul_comm.mp (hcl g l k)
  have hZ : ∀ l, ⁅g, l⁆ ∈ Subgroup.center Q := fun l =>
    Subgroup.mem_center_iff.mpr fun k => (hcen l k).symm
  have := CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary (p := 3)
    ((commHom g hcen).codRestrict (Subgroup.center Q) hZ)
    (fun u v => Subtype.ext (Subgroup.mem_center_iff.mp v.2 u))
    (fun u => Subtype.ext (by rw [Subgroup.coe_pow]; exact h3 _)) hf
  rw [MonoidHom.mem_ker] at this
  have h1 : ⁅g, f⁆ = 1 := congrArg Subtype.val this
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

theorem false_of_case1b {x y : P} {a s : MulAut P} (h : Hyp P x y a s)
    (h9 : Nat.card (omegaCenter P) = 9) (h27 : Nat.card (P ⧸ omegaCenter P) = 27)
    (h3 : ∀ q : P ⧸ omegaCenter P, q ^ 3 = 1)
    (hnot : ¬ ∀ g k : P, ⁅g, k⁆ ∈ omegaCenter P) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Z := omegaCenter P with hZdef
  set π := QuotientGroup.mk' Z with hπdef
  have hmemZ : ∀ g, π g = 1 → g ∈ Z := fun g hg => (QuotientGroup.eq_one_iff _).mp hg
  have hcube : ∀ g : P, g ^ 3 ∈ Z := fun g => hmemZ _ (by rw [map_pow]; exact h3 _)
  have hgenQ : Subgroup.closure {π x, π y} = ⊤ := by
    have := congrArg (Subgroup.map π) h.gen
    rw [MonoidHom.map_closure, Set.image_pair,
      Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at this
    exact this
  have hcZ : ⁅x, y⁆ ∉ Z := by
    intro hc
    apply hnot
    have hxy : π x * π y = π y * π x := by
      rw [← commutatorElement_eq_one_iff_mul_comm, ← map_commutatorElement, hπdef,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hc
    have hcomm := comm_of_closure_pair hgenQ hxy
    intro g k
    exact hmemZ _ (by rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
                      exact hcomm _ _)
  have hc31 : ⁅x, y⁆ ^ 3 ≠ 1 := fun e => hcZ (mem_omegaCenter_of_pow_three h h9 e)
  have hcg : ∀ g, ⁅⁅x, y⁆, g⁆ ∈ Z := fun g => hmemZ _ (by
    rw [map_commutatorElement, map_commutatorElement]
    exact comm_comm_of_card_27 h27 _ _ _)
  have hcen : ∀ g k : P, ⁅⁅x, y⁆, g⁆ * k = k * ⁅⁅x, y⁆, g⁆ := fun g k =>
    omegaCenter_central (hcg g) k
  set ψ := commHom ⁅x, y⁆ hcen with hψdef
  have hψ : ∀ g, ψ g = ⁅⁅x, y⁆, g⁆ := fun _ => rfl
  have hkerne : ψ.ker ≠ ⊤ := by
    intro htop
    have hcc : ∀ k : P, ⁅x, y⁆ * k = k * ⁅x, y⁆ := fun k => by
      have : ψ k = 1 := (htop ▸ Subgroup.mem_top k : k ∈ ψ.ker)
      exact commutatorElement_eq_one_iff_mul_comm.mp this
    have e1 := comm_pow_left_of_central hcc 3
    have e2 : ⁅x ^ 3, y⁆ = 1 := by
      rw [commutatorElement_eq_one_iff_mul_comm]
      exact omegaCenter_central (hcube x) y
    exact hc31 (by rw [← e1, e2])
  have hker1 : frattini P ≤ ψ.ker := by
    intro f hf
    have := CFSG.SectionRank.Ccomm.frattini_le_ker_of_elementary (p := 3)
      (ψ.codRestrict Z hcg) (fun u v => Subtype.ext (omegaCenter_central u.2 v))
      (fun u => Subtype.ext u.2.2) hf
    rw [MonoidHom.mem_ker] at this ⊢
    exact congrArg Subtype.val this
  have hQcl : ∀ u v w : P ⧸ Z, ⁅⁅u, v⁆, w⁆ = 1 := comm_comm_of_card_27 h27
  have hQΦ : frattini (P ⧸ Z) ≤ Subgroup.center (P ⧸ Z) := frattini_le_center_of_exp3 hQcl h3
  have hΦmap : ∀ f ∈ frattini P, ∀ w : P ⧸ Z, π f * w = w * π f := fun f hf w =>
    (Subgroup.mem_center_iff.mp (hQΦ (frattini_le_comap_frattini_of_surjective
      (QuotientGroup.mk'_surjective Z) hf)) w).symm
  have hQcen : ∀ u v w : P ⧸ Z, ⁅u, v⁆ * w = w * ⁅u, v⁆ := fun u v w =>
    commutatorElement_eq_one_iff_mul_comm.mp (hQcl u v w)
  have hac : a ⁅x, y⁆ * ⁅x, y⁆ ∈ Z := by
    apply hmemZ
    have e1 : π (a x) = π (a x * x) * (π x)⁻¹ := by rw [map_mul, mul_inv_cancel_right]
    have e2 : π (a y) = π y * π (y⁻¹ * a y) := by rw [map_mul, map_inv, mul_inv_cancel_left]
    rw [map_mul, map_commutatorElement a, map_commutatorElement π, e1, e2,
      comm_central_mul_left (hΦmap _ h.ax), comm_mul_central_right (hΦmap _ h.ay),
      comm_inv_left_of_central (hQcen _ _), ← map_commutatorElement π]
    exact inv_mul_cancel _
  have hsc : s ⁅x, y⁆ * ⁅x, y⁆ ∈ Z := by
    apply hmemZ
    have e1 : π (s x) = π y * π (y⁻¹ * s x) := by rw [map_mul, map_inv, mul_inv_cancel_left]
    have e2 : π (s y) = π x * π (x⁻¹ * s y) := by rw [map_mul, map_inv, mul_inv_cancel_left]
    rw [map_mul, map_commutatorElement s, map_commutatorElement π, e1, e2,
      comm_mul_central_right (hΦmap _ h.sy), ← hΦmap _ h.sx (π y),
      comm_central_mul_left (hΦmap _ h.sx), comm_swap, ← map_commutatorElement π]
    exact inv_mul_cancel _
  have hφψ : ∀ φ : MulAut P, φ ⁅x, y⁆ * ⁅x, y⁆ ∈ Z → ∀ g, φ (ψ g) = (ψ (φ g))⁻¹ := by
    intro φ hφ g
    have e : φ ⁅x, y⁆ = (φ ⁅x, y⁆ * ⁅x, y⁆) * ⁅x, y⁆⁻¹ := by group
    rw [hψ, map_commutatorElement, e, comm_central_mul_left (omegaCenter_central hφ),
      comm_inv_left_of_central (hcen _), hψ]
  have hinvar : ∀ φ : MulAut P, φ ⁅x, y⁆ * ⁅x, y⁆ ∈ Z → ∀ g ∈ ψ.ker, φ g ∈ ψ.ker := by
    intro φ hφ g hg
    rw [MonoidHom.mem_ker] at hg ⊢
    have := hφψ φ hφ g
    rw [hg, map_one] at this
    exact inv_eq_one.mp this.symm
  have hker : ψ.ker = frattini P := by
    rcases eq_frattini_or_top h hker1 (hinvar a hac) (hinvar s hsc) with he | ht
    · exact he
    · exact absurd ht hkerne
  have hrange : ψ.range = Z := by
    have hle : ψ.range ≤ Z := by rintro _ ⟨g, rfl⟩; exact hcg g
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [h9, ← Subgroup.index_ker, hker, h.index]
  obtain ⟨g₀, hg₀⟩ : ⁅x, y⁆ ^ 3 ∈ ψ.range := hrange ▸ hcube _
  have hcube_inv : ∀ φ : MulAut P, φ ⁅x, y⁆ * ⁅x, y⁆ ∈ Z → φ (⁅x, y⁆ ^ 3) = (⁅x, y⁆ ^ 3)⁻¹ := by
    intro φ hφ
    have e : φ ⁅x, y⁆ = (φ ⁅x, y⁆ * ⁅x, y⁆) * ⁅x, y⁆⁻¹ := by group
    have hcomm : Commute (φ ⁅x, y⁆ * ⁅x, y⁆) ⁅x, y⁆⁻¹ := omegaCenter_central hφ _
    rw [map_pow, e, hcomm.mul_pow, hφ.2, one_mul, inv_pow]
  have hfix : ∀ φ : MulAut P, φ ⁅x, y⁆ * ⁅x, y⁆ ∈ Z → g₀⁻¹ * φ g₀ ∈ frattini P := by
    intro φ hφ
    rw [← hker, MonoidHom.mem_ker, map_mul, map_inv]
    have h1 := hφψ φ hφ g₀
    rw [hg₀, hcube_inv φ hφ] at h1
    have h2 : ⁅x, y⁆ ^ 3 = ψ (φ g₀) := inv_inj.mp h1
    rw [hg₀, ← h2, inv_mul_cancel]
  have hg₀Φ := mem_frattini_of_fix h (hfix a hac) (hfix s hsc)
  rw [← hker, MonoidHom.mem_ker, hg₀] at hg₀Φ
  exact hc31 hg₀Φ

end CFSG.Quasithin.H13.R2
