module

public import CFSG.LocalAnalysis.SectionRank.Ccomm.NonabelianCube
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection4.lemma_4_5_a

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.SectionRank.Ccomm
open scoped commutatorElement

variable {Q : Type*} [Group Q]

theorem aut_commute_on_cyclic {C : Subgroup Q} (hC : IsCyclic C) {σ τ : MulAut Q}
    (hσ : ∀ c ∈ C, σ c ∈ C) (hτ : ∀ c ∈ C, τ c ∈ C) (c : Q) (hc : c ∈ C) :
    σ (τ c) = τ (σ c) := by
  obtain ⟨g, hg⟩ := hC.exists_generator
  have hmem : ∀ x ∈ C, ∃ k : ℤ, x = (g : Q) ^ k := fun x hx => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg ⟨x, hx⟩)
    exact ⟨k, by rw [← SubgroupClass.coe_zpow, hk]⟩
  obtain ⟨m, hm⟩ := hmem _ (hσ g g.2)
  obtain ⟨n, hn⟩ := hmem _ (hτ g g.2)
  obtain ⟨k, rfl⟩ := hmem c hc
  simp only [map_zpow, hm, hn, ← zpow_mul]
  congr 1
  ring

theorem perfect_fixes_cyclic {H : Type*} [Group H] [Group.IsPerfect H] (α : H →* MulAut Q)
    {C : Subgroup Q} (hC : IsCyclic C) (hinv : ∀ h : H, ∀ c ∈ C, α h c ∈ C) (h : H) (c : Q)
    (hc : c ∈ C) : α h c = c := by
  let K : Subgroup H :=
    { carrier := {h | ∀ c ∈ C, α h c = c}
      mul_mem' := fun {a b} ha hb c hc => by
        rw [map_mul, MulAut.mul_apply, hb c hc, ha c hc]
      one_mem' := fun c _ => by rw [map_one, MulAut.one_apply]
      inv_mem' := fun {a} ha c hc => by
        have h1 := MulAut.inv_apply_self Q (α a) c
        rw [ha c hc] at h1
        rw [map_inv]
        exact h1 }
  have hcomm : commutator H ≤ K := by
    rw [commutator_eq_closure, closure_le]
    rintro _ ⟨a, b, rfl⟩ c hc
    have hc' : (α a)⁻¹ ((α b)⁻¹ c) ∈ C := by
      rw [← map_inv, ← map_inv]
      exact hinv _ _ (hinv _ _ hc)
    change α ⁅a, b⁆ c = c
    simp only [commutatorElement_def, map_mul, map_inv, MulAut.mul_apply]
    rw [aut_commute_on_cyclic hC (hinv a) (hinv b) _ hc', MulAut.apply_inv_self,
      MulAut.apply_inv_self]
  have htop : K = ⊤ := by
    rw [eq_top_iff, ← Group.IsPerfect.commutator_eq_top (G := H)]
    exact hcomm
  have hK : h ∈ K := by rw [htop]; exact mem_top h
  exact hK c hc

theorem supercritical_nonabelian_eq_top {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite Q]
    (hQ : IsPGroup p Q) {H : Type*} [Group H] [Group.IsPerfect H] (α : H →* MulAut Q)
    (D : Subgroup Q) [D.Characteristic]
    (hQH : closure {y : Q | ∃ x : Q, ∃ h : H, x⁻¹ * α h x = y} = ⊤)
    (htors : ∀ x ∈ centralizer (D : Set Q), orderOf x = p → x ∈ D)
    (hnc : ¬ IsMulCommutative D) (hcard : Nat.card D = p ^ 3)
    (hΦ : frattini D = center D) (hΦcard : Nat.card (frattini D) = p)
    (hQtriv : ∀ q : Q, frattiniAction D (MulAut.conj q) = 1) : D = ⊤ := by
  classical
  set C := centralizer (D : Set Q) with hCdef
  have hDinv : ∀ (σ : MulAut Q) (x : Q), x ∈ D → σ x ∈ D := fun σ x hx =>
    (MulAut.characteristic D σ ⟨x, hx⟩).2
  have hnc' : ∃ a b : D, a * b ≠ b * a := by
    by_contra h
    push Not at h
    exact hnc ⟨⟨h⟩⟩
  obtain ⟨-, -, -, -, -, -, hinner⟩ := nonabelian_prime_cube_central_structure hcard hnc'
  have hDC : ∀ q : Q, ∃ d ∈ D, ∃ c ∈ C, q = d * c := by
    intro q
    have hker : MulAut.conj q ∈ (frattiniAction D).ker := hQtriv q
    rw [mem_ker_frattiniAction, hΦ] at hker
    obtain ⟨g, hg⟩ := hinner _ hker
    refine ⟨g, g.2, (g : Q)⁻¹ * q, ?_, by group⟩
    rw [mem_centralizer_iff]
    intro x hx
    have h1 := congrArg (fun β : MulAut D => ((β ⟨x, hx⟩ : D) : Q)) hg
    change q * x * q⁻¹ = (g : Q) * x * (g : Q)⁻¹ at h1
    calc x * ((g : Q)⁻¹ * q) = (g : Q)⁻¹ * ((g : Q) * x * (g : Q)⁻¹) * q := by group
      _ = (g : Q)⁻¹ * (q * x * q⁻¹) * q := by rw [h1]
      _ = (g : Q)⁻¹ * q * x := by group
  have hZcard : Nat.card ((center D).map D.subtype) = p := by
    rw [card_map_of_injective D.subtype_injective, ← hΦ, hΦcard]
  have hCcyc : IsCyclic C := by
    by_contra hncyc
    have : Fact (IsPGroup p C) := ⟨hQ.to_subgroup C⟩
    obtain ⟨S, -, hScard, hSel⟩ := CFSG.lemma_4_5_a hp2 hncyc
    have hle : S.map C.subtype ≤ (center D).map D.subtype := by
      rintro _ ⟨s, hs, rfl⟩
      have hsC : (s : Q) ∈ C := s.2
      have hsp : (s : Q) ^ p = 1 := by
        have := hSel
        have h1 : s ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian s hs
        rw [← SubgroupClass.coe_pow, h1, OneMemClass.coe_one]
      have hsD : (s : Q) ∈ D := by
        by_cases hs1 : (s : Q) = 1
        · rw [hs1]
          exact one_mem D
        · exact htors _ hsC (orderOf_eq_prime hsp hs1)
      refine ⟨⟨s, hsD⟩, mem_center_iff.mpr fun y => Subtype.ext ?_, rfl⟩
      exact mem_centralizer_iff.mp hsC y y.2
    have h1 := card_le_of_le hle
    rw [card_map_of_injective C.subtype_injective, hScard, hZcard] at h1
    have h2 : p ^ 2 ≤ p ^ 1 := by rwa [pow_one]
    have := (Nat.pow_le_pow_iff_right hp.out.one_lt).mp h2
    omega
  have hCinv : ∀ h : H, ∀ c ∈ C, α h c ∈ C := by
    intro h c hc
    rw [mem_centralizer_iff]
    intro y hy
    have hy' : (α h)⁻¹ y ∈ D := hDinv _ _ hy
    have h1 := mem_centralizer_iff.mp hc _ hy'
    have h2 := congrArg (α h) h1
    rw [map_mul, map_mul, MulAut.apply_inv_self] at h2
    exact h2
  have hCfix := perfect_fixes_cyclic α hCcyc hCinv
  rw [eq_top_iff, ← hQH, closure_le]
  rintro _ ⟨x, h, rfl⟩
  obtain ⟨d, hd, c, hc, rfl⟩ := hDC x
  rw [map_mul, hCfix h c hc]
  have h1 : d⁻¹ * α h d ∈ D := mul_mem (inv_mem hd) (hDinv _ _ hd)
  have h2 := mem_centralizer_iff.mp hc _ h1
  have e : (d * c)⁻¹ * (α h d * c) = d⁻¹ * α h d := by
    calc (d * c)⁻¹ * (α h d * c) = c⁻¹ * ((d⁻¹ * α h d) * c) := by group
      _ = c⁻¹ * (c * (d⁻¹ * α h d)) := by rw [h2]
      _ = d⁻¹ * α h d := by group
  rw [SetLike.mem_coe, e]
  exact h1

@[expose] def commPowHom (hcomm : ∀ x y : Q, x * y = y * x) (n : ℕ) : Q →* Q where
  toFun x := x ^ n
  map_one' := one_pow n
  map_mul' x y := Commute.mul_pow (hcomm x y) n

theorem commPowHom_apply (hcomm : ∀ x y : Q, x * y = y * x) (n : ℕ) (x : Q) :
    commPowHom hcomm n x = x ^ n := rfl

theorem card_le_of_pow_prime_pow_eq_one {p : ℕ} [Finite Q]
    (hcomm : ∀ x y : Q, x * y = y * x) (D : Subgroup Q) (hD : ∀ x : Q, x ^ p = 1 ↔ x ∈ D)
    (hcard : Nat.card D = p ^ 2) (k : ℕ) (K : Subgroup Q) (hK : ∀ x ∈ K, x ^ p ^ k = 1) :
    Nat.card K ≤ p ^ (2 * k) := by
  induction k generalizing K with
  | zero =>
    have hK1 : K = ⊥ := eq_bot_iff.mpr fun x hx => by
      rw [mem_bot]
      simpa using hK x hx
    rw [hK1, card_bot]
    simp
  | succ k ih =>
    set f := (commPowHom hcomm p).comp K.subtype with hf
    have hrange : Nat.card f.range ≤ p ^ (2 * k) := ih _ (by
      rintro _ ⟨x, rfl⟩
      change ((x : Q) ^ p) ^ p ^ k = 1
      rw [← pow_mul, ← pow_succ']
      exact hK x x.2)
    have hker : Nat.card f.ker ≤ p ^ 2 := by
      rw [← hcard]
      refine Nat.card_le_card_of_injective (fun x => ⟨((x : K) : Q), (hD ((x : K) : Q)).mp
        (by have h1 := x.2; rw [MonoidHom.mem_ker] at h1; exact h1)⟩) ?_
      intro x y hxy
      have h := congrArg Subtype.val hxy
      exact Subtype.ext (Subtype.ext h)
    have hprod := f.ker.card_mul_index
    rw [Subgroup.index_ker] at hprod
    rw [← hprod]
    calc Nat.card f.ker * Nat.card f.range ≤ p ^ 2 * p ^ (2 * k) := Nat.mul_le_mul hker hrange
      _ = p ^ (2 * (k + 1)) := by
          rw [← pow_add]
          congr 1
          ring

theorem homocyclic_of_invariant_omega {p : ℕ} [hp : Fact p.Prime] [Finite Q]
    (hcomm : ∀ x y : Q, x * y = y * x) (hQ : IsPGroup p Q) (D : Subgroup Q)
    (hD : ∀ x : Q, x ^ p = 1 ↔ x ∈ D) (hcard : Nat.card D = p ^ 2)
    (hirr : ∀ U : Subgroup Q, U ≤ D → Nat.card U = p →
      (∀ (σ : MulAut Q) (u : Q), u ∈ U → σ u ∈ U) → False) :
    ∃ a : ℕ, 1 ≤ a ∧
      Nonempty (Q ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a))) := by
  classical
  have hp1 := hp.out.one_lt
  have hex : ∃ e : ℕ, ∀ x : Q, x ^ p ^ e = 1 := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
    exact ⟨n, fun x => by rw [← hn]; exact pow_card_eq_one'⟩
  set a := Nat.find hex with ha
  have hpa : ∀ x : Q, x ^ p ^ a = 1 := Nat.find_spec hex
  have ha1 : 1 ≤ a := by
    by_contra h0
    have h0' : a = 0 := by omega
    have hD1 : D = ⊥ := eq_bot_iff.mpr fun x _ => (mem_bot).mpr (by simpa [h0'] using hpa x)
    rw [hD1, card_bot] at hcard
    have : 1 < p ^ 2 := Nat.one_lt_pow two_ne_zero hp1
    omega
  obtain ⟨x₀, hx₀⟩ : ∃ x : Q, x ^ p ^ (a - 1) ≠ 1 := by
    have := Nat.find_min hex (show a - 1 < a by omega)
    push Not at this
    exact this
  have hpa' : p ^ a = p ^ (a - 1) * p := by rw [← pow_succ, Nat.sub_add_cancel ha1]
  set φ := commPowHom hcomm (p ^ (a - 1)) with hφ
  have hIle : φ.range ≤ D := by
    rintro _ ⟨x, rfl⟩
    rw [← hD]
    change (x ^ p ^ (a - 1)) ^ p = 1
    rw [← pow_mul, ← hpa']
    exact hpa x
  have hIne : φ.range ≠ ⊥ := by
    intro h
    apply hx₀
    have : φ x₀ ∈ φ.range := ⟨x₀, rfl⟩
    rw [h, mem_bot] at this
    exact this
  have hIinv : ∀ (σ : MulAut Q) (u : Q), u ∈ φ.range → σ u ∈ φ.range := by
    rintro σ _ ⟨x, rfl⟩
    exact ⟨σ x, by
      change (σ x) ^ p ^ (a - 1) = σ (x ^ p ^ (a - 1))
      rw [map_pow]⟩
  have hID : φ.range = D := by
    have hdvd : Nat.card φ.range ∣ p ^ 2 := hcard ▸ card_dvd_of_le hIle
    obtain ⟨j, hj, hjc⟩ := (Nat.dvd_prime_pow hp.out).mp hdvd
    interval_cases j
    · exact absurd (card_eq_one.mp (by rw [hjc, pow_zero])) hIne
    · exact (hirr _ hIle (by rw [hjc, pow_one]) hIinv).elim
    · exact eq_of_le_of_card_ge hIle (by rw [hcard, hjc])
  set d₁ := x₀ ^ p ^ (a - 1) with hd₁
  have hd₁D : d₁ ∈ D := hIle ⟨x₀, rfl⟩
  have hord₁ : orderOf d₁ = p := orderOf_eq_prime ((hD d₁).mpr hd₁D) hx₀
  obtain ⟨d₂, hd₂D, hd₂⟩ : ∃ d₂ ∈ D, d₂ ∉ zpowers d₁ := by
    by_contra hcon
    push Not at hcon
    have h1 := card_le_of_le (show D ≤ zpowers d₁ from hcon)
    rw [hcard, Nat.card_zpowers, hord₁] at h1
    have h2 : p ^ 2 ≤ p ^ 1 := by rwa [pow_one]
    have := (Nat.pow_le_pow_iff_right hp1).mp h2
    omega
  have hd₂ne : d₂ ≠ 1 := fun h => hd₂ (h ▸ one_mem _)
  have hord₂ : orderOf d₂ = p := orderOf_eq_prime ((hD d₂).mpr hd₂D) hd₂ne
  obtain ⟨x₂, hx₂⟩ : ∃ x₂ : Q, x₂ ^ p ^ (a - 1) = d₂ := by
    rw [← hID] at hd₂D
    obtain ⟨x, hx⟩ := hd₂D
    exact ⟨x, hx⟩
  have hordx : ∀ x : Q, x ^ p ^ (a - 1) ≠ 1 → orderOf x = p ^ a := by
    intro x hx
    have h1 : orderOf x ∣ p ^ a := orderOf_dvd_of_pow_eq_one (hpa x)
    obtain ⟨j, hj, hjx⟩ := (Nat.dvd_prime_pow hp.out).mp h1
    have hja : ¬ j ≤ a - 1 := by
      intro hj'
      apply hx
      rw [← orderOf_dvd_iff_pow_eq_one, hjx]
      exact pow_dvd_pow p hj'
    rw [hjx]
    congr 1
    omega
  have hordx₀ := hordx x₀ hx₀
  have hordx₂ := hordx x₂ (by rw [hx₂]; exact hd₂ne)
  have hlow : ∀ x : Q, orderOf x = p ^ a → ∀ w ∈ zpowers x, w ^ p = 1 →
      w ∈ zpowers (x ^ p ^ (a - 1)) := by
    intro x hx w hw hwp
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hw
    have h1 : x ^ (m * (p : ℤ)) = 1 := by rw [zpow_mul, zpow_natCast, hwp]
    rw [← orderOf_dvd_iff_zpow_eq_one, hx, hpa'] at h1
    have h2 : (p : ℤ) ^ (a - 1) ∣ m := by
      have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.out.ne_zero
      push_cast at h1
      exact (mul_dvd_mul_iff_right hp0).mp h1
    obtain ⟨m', rfl⟩ := h2
    exact mem_zpowers_iff.mpr ⟨m', by rw [← zpow_natCast, ← zpow_mul, Nat.cast_pow]⟩
  have hprime_eq : ∀ w d : Q, orderOf d = p → w ∈ zpowers d → w ≠ 1 →
      zpowers w = zpowers d := by
    intro w d hd hw hw1
    have hwp : w ^ p = 1 := by
      obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hw
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hd,
        pow_orderOf_eq_one, one_zpow]
    refine eq_of_le_of_card_ge (zpowers_le.mpr hw) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers, hd, orderOf_eq_prime hwp hw1]
  have hdisj : zpowers x₀ ⊓ zpowers x₂ = ⊥ := by
    rw [eq_bot_iff]
    intro z hz
    rw [mem_bot]
    by_contra hz1
    obtain ⟨hz₀, hz₂⟩ := mem_inf.mp hz
    obtain ⟨j, hj⟩ := IsPGroup.iff_orderOf.mp hQ z
    have hj0 : j ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hj
      exact hz1 hj
    set w := z ^ p ^ (j - 1) with hw
    have hwp : w ^ p = 1 := by
      rw [hw, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hj0), ← hj,
        pow_orderOf_eq_one]
    have hw1 : w ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hj, Nat.pow_dvd_pow_iff_le_right hp1] at h1
      omega
    have hw₀ : w ∈ zpowers d₁ := hlow x₀ hordx₀ w (pow_mem hz₀ _) hwp
    have hw₂ : w ∈ zpowers d₂ := by
      rw [← hx₂]
      exact hlow x₂ hordx₂ w (pow_mem hz₂ _) hwp
    have e₁ := hprime_eq w _ hord₁ hw₀ hw1
    have e₂ := hprime_eq w _ hord₂ hw₂ hw1
    apply hd₂
    rw [← e₁, e₂]
    exact mem_zpowers d₂
  set A := zpowers x₀ with hA
  set B := zpowers x₂ with hB
  let ψ : A × B →* Q :=
    { toFun := fun uv => (uv.1 : Q) * uv.2
      map_one' := by simp
      map_mul' := fun u v => by
        change (u.1 : Q) * v.1 * ((u.2 : Q) * v.2) = (u.1 : Q) * u.2 * ((v.1 : Q) * v.2)
        rw [mul_assoc, ← mul_assoc (v.1 : Q), hcomm (v.1 : Q) (u.2 : Q)]
        group }
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨u, v⟩ huv
    change (u : Q) * v = 1 at huv
    have hu : (u : Q) = (v : Q)⁻¹ := eq_inv_of_mul_eq_one_left huv
    have hu1 : (u : Q) = 1 := by
      have h1 : (u : Q) ∈ A ⊓ B := mem_inf.mpr ⟨u.2, by rw [hu]; exact inv_mem v.2⟩
      rw [hdisj, mem_bot] at h1
      exact h1
    have hv1 : (v : Q) = 1 := by
      rw [hu1, one_mul] at huv
      exact huv
    exact Prod.ext (Subtype.ext hu1) (Subtype.ext hv1)
  have hcardA : Nat.card A = p ^ a := by rw [hA, Nat.card_zpowers, hordx₀]
  have hcardB : Nat.card B = p ^ a := by rw [hB, Nat.card_zpowers, hordx₂]
  have hbij : Function.Bijective ψ := by
    refine hψinj.bijective_of_nat_card_le ?_
    rw [Nat.card_prod, hcardA, hcardB, ← pow_add, ← two_mul]
    have h1 := card_le_of_pow_prime_pow_eq_one hcomm D hD hcard a ⊤ (fun x _ => hpa x)
    rwa [card_top] at h1
  have hgenA : ∀ y : A, y ∈ zpowers (⟨x₀, mem_zpowers x₀⟩ : A) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    exact mem_zpowers_iff.mpr ⟨m, Subtype.ext (by simp)⟩
  have hgenB : ∀ y : B, y ∈ zpowers (⟨x₂, mem_zpowers x₂⟩ : B) := by
    rintro ⟨y, hy⟩
    obtain ⟨m, rfl⟩ := mem_zpowers_iff.mp hy
    exact mem_zpowers_iff.mpr ⟨m, Subtype.ext (by simp)⟩
  exact ⟨a, ha1, ⟨(MulEquiv.ofBijective ψ hbij).symm.trans
    (MulEquiv.prodCongr (zmodMulEquivOfGenerator hgenA hcardA).symm
      (zmodMulEquivOfGenerator hgenB hcardB).symm)⟩⟩

theorem supercritical_elementary_homocyclic {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2)
    [Finite Q] (hQ : IsPGroup p Q) {H : Type*} [Group H] (α : H →* MulAut Q)
    (D : Subgroup Q) [D.Characteristic]
    (htors : ∀ x ∈ centralizer (D : Set Q), orderOf x = p → x ∈ D)
    (hDel : IsElementaryAbelian p D) (hcard : Nat.card D = p ^ 2)
    (hirr : ∀ U : Subgroup (D ⧸ frattini D), Nat.card U = p →
      ∃ h : H, ∃ u ∈ U, frattiniAction D (α h) u ∉ U)
    (hQtriv : ∀ q : Q, frattiniAction D (MulAut.conj q) = 1)
    {t : H} (ht : t ^ 2 = 1) (htinv : ∀ w, frattiniAction D (α t) w = w⁻¹) :
    IsMulCommutative Q ∧
      (∃ a : ℕ, 1 ≤ a ∧
        Nonempty (Q ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a)))) ∧
      D = CFSG.omega₁ Q (p := p) := by
  classical
  have : Fact (IsPGroup p D) := ⟨hQ.to_subgroup D⟩
  have hΦ : frattini D = ⊥ := CFSG.frattini_eq_bot_of_isElementaryAbelian (R := D) (p := p)
  have hcen : ∀ q : Q, ∀ d ∈ D, q * d * q⁻¹ = d := by
    intro q d hd
    have hker : MulAut.conj q ∈ (frattiniAction D).ker := hQtriv q
    rw [mem_ker_frattiniAction, hΦ] at hker
    have h1 := hker ⟨d, hd⟩
    rw [mem_bot, inv_mul_eq_one] at h1
    exact (congrArg Subtype.val h1).symm
  have hcentr : ∀ x : Q, x ∈ centralizer (D : Set Q) := fun x =>
    mem_centralizer_iff.mpr fun d hd => by
      have h1 := hcen x d hd
      calc d * x = x * d * x⁻¹ * x := by rw [h1]
        _ = x * d := by group
  have hDp : ∀ x : Q, x ^ p = 1 ↔ x ∈ D := by
    intro x
    constructor
    · intro hx
      by_cases hx1 : x = 1
      · rw [hx1]
        exact one_mem D
      · exact htors x (hcentr x) (orderOf_eq_prime hx hx1)
    · intro hx
      exact CFSG.elemPow_eq_one_of_isElementaryAbelian x hx
  have hΩ : D = CFSG.omega₁ Q (p := p) := by
    apply le_antisymm
    · intro x hx
      exact subset_closure (show x ^ p ^ 1 = 1 by rw [pow_one]; exact (hDp x).mpr hx)
    · refine (closure_le D).mpr fun x hx => (hDp x).mp ?_
      have hx' : x ^ p ^ 1 = 1 := hx
      rwa [pow_one] at hx'
  have htD : ∀ d ∈ D, α t d = d⁻¹ := by
    intro d hd
    have h1 := htinv ((⟨d, hd⟩ : D) : D ⧸ frattini D)
    rw [frattiniAction_mk, ← QuotientGroup.mk_inv, QuotientGroup.eq, hΦ, mem_bot] at h1
    have h2 := congrArg Subtype.val h1
    simp only [coe_mul, coe_inv, OneMemClass.coe_one] at h2
    exact inv_mul_eq_one.mp h2
  have hDfix : ∀ y ∈ D, α t y = y → y = 1 := by
    intro y hy hfix
    have h1 : y = y⁻¹ := hfix.symm.trans (htD y hy)
    have h2 : y ^ 2 = 1 := by
      calc y ^ 2 = y * y := sq y
        _ = y * y⁻¹ := congrArg (y * ·) h1
        _ = 1 := mul_inv_cancel y
    have h3 : y ^ p = 1 := (hDp y).mpr hy
    have hcop : Nat.gcd p 2 = 1 := (Nat.coprime_primes hp.out Nat.prime_two).mpr hp2
    have h4 : orderOf y ∣ Nat.gcd p 2 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h3) (orderOf_dvd_of_pow_eq_one h2)
    rw [hcop, Nat.dvd_one, orderOf_eq_one_iff] at h4
    exact h4
  have hfpf : MonoidHom.FixedPointFree (α t) := by
    intro x hx
    by_contra hx1
    obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp hQ x
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero, orderOf_eq_one_iff] at hk
      exact hx1 hk
    set y := x ^ p ^ (k - 1) with hy
    have hyp : y ^ p = 1 := by
      rw [hy, ← pow_mul, ← pow_succ, Nat.sub_add_cancel (Nat.one_le_iff_ne_zero.mpr hk0), ← hk,
        pow_orderOf_eq_one]
    have hy1 : y ≠ 1 := by
      intro h
      have h1 := orderOf_dvd_of_pow_eq_one h
      rw [hk, Nat.pow_dvd_pow_iff_le_right hp.out.one_lt] at h1
      omega
    exact hy1 (hDfix y ((hDp y).mp hyp) (by rw [hy, map_pow, hx]))
  have hinvol : Function.Involutive (α t) := fun x => by
    rw [← MulAut.mul_apply, ← map_mul, ← sq, ht, map_one, MulAut.one_apply]
  have hcomm : ∀ x y : Q, x * y = y * x := fun x y =>
    MonoidHom.FixedPointFree.commute_all_of_involutive hfpf hinvol x y
  have hirr' : ∀ U : Subgroup Q, U ≤ D → Nat.card U = p →
      (∀ (σ : MulAut Q) (u : Q), u ∈ U → σ u ∈ U) → False := by
    intro U hUD hUp hUinv
    set U' : Subgroup (D ⧸ frattini D) := (U.subgroupOf D).map (QuotientGroup.mk' (frattini D))
      with hU'
    have hinj : Function.Injective (QuotientGroup.mk' (frattini D)) := by
      rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hΦ]
    have hU'card : Nat.card U' = p := by
      rw [hU', card_map_of_injective hinj, ← hUp]
      exact Nat.card_congr (subgroupOfEquivOfLe hUD).toEquiv
    obtain ⟨h, u, hu, hnot⟩ := hirr U' hU'card
    obtain ⟨v, hv, rfl⟩ := hu
    apply hnot
    have hmem : MulAut.characteristic D (α h) v ∈ U.subgroupOf D := by
      rw [mem_subgroupOf]
      have h1 : ((MulAut.characteristic D (α h) v : D) : Q) = α h v := by simp
      rw [h1]
      exact hUinv (α h) v (mem_subgroupOf.mp hv)
    exact ⟨_, hmem, rfl⟩
  exact ⟨⟨⟨hcomm⟩⟩, homocyclic_of_invariant_omega hcomm hQ D hDp hcard hirr', hΩ⟩

theorem supercritical_whole_pgroup_shape {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) [Finite Q]
    (hQ : IsPGroup p Q) {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (α : H →* MulAut Q) (D : Subgroup Q) [D.Characteristic]
    (hQH : closure {y : Q | ∃ x : Q, ∃ h : H, x⁻¹ * α h x = y} = ⊤)
    (htors : ∀ x ∈ centralizer (D : Set Q), orderOf x = p → x ∈ D)
    (hD : (IsElementaryAbelian p D ∧ Nat.card D = p ^ 2) ∨
      (¬ IsMulCommutative D ∧ Nat.card D = p ^ 3 ∧ (∀ x ∈ D, x ^ p = 1) ∧
        frattini D = center D ∧ Nat.card (frattini D) = p))
    (hirr : ∀ U : Subgroup (D ⧸ frattini D), Nat.card U = p →
      ∃ h : H, ∃ u ∈ U, frattiniAction D (α h) u ∉ U)
    (hQtriv : ∀ q : Q, frattiniAction D (MulAut.conj q) = 1)
    (ht : ∃ t : H, orderOf t = 2 ∧ ∀ w, frattiniAction D (α t) w = w⁻¹) :
    (¬ IsMulCommutative D → D = ⊤) ∧
      (IsElementaryAbelian p D → IsMulCommutative Q ∧
        (∃ a : ℕ, 1 ≤ a ∧
          Nonempty (Q ≃* Multiplicative (ZMod (p ^ a)) × Multiplicative (ZMod (p ^ a)))) ∧
        D = CFSG.omega₁ Q (p := p)) := by
  constructor
  · intro hnc
    rcases hD with ⟨hel, -⟩ | ⟨-, hcard, -, hΦ, hΦcard⟩
    · exact absurd hel.toIsMulCommutative hnc
    · exact supercritical_nonabelian_eq_top hp2 hQ α D hQH htors hnc hcard hΦ hΦcard hQtriv
  · intro hel
    obtain ⟨t, ht2, htinv⟩ := ht
    rcases hD with ⟨-, hcard⟩ | ⟨hnc, -⟩
    · exact supercritical_elementary_homocyclic hp2 hQ α D htors hel hcard hirr hQtriv
        (by rw [← ht2]; exact pow_orderOf_eq_one t) htinv
    · exact absurd hel.toIsMulCommutative hnc

end CFSG.Quasithin.H13.NQBlock
