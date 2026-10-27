module

public import Mathlib.Tactic.NormNum.Prime
public import CFSG.LocalAnalysis.ComponentInitial.SelfCentralizingCoreAutomorphisms

public noncomputable section

namespace CFSG.Sporadic.J4Schreier

open CFSG.LocalAnalysis.ComponentInitial MulAction

theorem exists_fixed_of_iterate {X : Type*} {φ : X → X} {Δ : Set X} [Finite Δ] {p : ℕ}
    [Fact p.Prime] (hΔ : ∀ x ∈ Δ, φ x ∈ Δ) (hφ : ∀ x, φ^[p] x = x) (hd : ¬ p ∣ Nat.card Δ) :
    ∃ x ∈ Δ, φ x = x := by
  classical
  have : Fintype Δ := Fintype.ofFinite Δ
  let f : Function.End Δ := fun x => ⟨φ x.1, hΔ x.1 x.2⟩
  have e : ∀ (m : ℕ) (x : Δ), ((f ^ m) x).1 = φ^[m] x.1 := by
    intro m
    induction m with
    | zero => intro x; rfl
    | succ m ih =>
      intro x
      rw [pow_succ', Function.iterate_succ_apply', ← ih]
      rfl
  have hf : f ^ p ^ 1 = 1 := by
    rw [pow_one]
    funext x
    exact Subtype.ext ((e p x).trans (hφ x.1))
  have hmod := Equiv.Perm.card_fixedPoints_modEq hf
  by_contra hno
  have hempty : IsEmpty (Function.fixedPoints f) :=
    ⟨fun x => hno ⟨x.1.1, x.1.2, congrArg Subtype.val (x.2 : Function.IsFixedPt f x.1)⟩⟩
  rw [Fintype.card_eq_zero_iff.2 hempty, Nat.modEq_zero_iff_dvd] at hmod
  exact hd (by rw [Nat.card_eq_fintype_card]; exact hmod)

@[expose] def ptPick (G : Type*) {X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]
    (r p : X) : G :=
  Classical.choose (exists_smul_eq G r p)

theorem ptPick_spec (G : Type*) {X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]
    (r p : X) : ptPick G r p • r = p :=
  Classical.choose_spec (exists_smul_eq G r p)

@[expose] def autHat {G : Type*} {X : Type*} [Group G] [MulAction G X] [IsPretransitive G X]
    (r : X) (α : MulAut G) (p : X) : X :=
  α (ptPick G r p) • r

section Hat

variable {G : Type*} [Group G] {X : Type*} [MulAction G X] [IsPretransitive G X]
  {H : Subgroup G} {r : X} {α : MulAut G}

omit [IsPretransitive G X] in
theorem mem_iff_smul_eq (hstab : stabilizer G r = H) {g : G} : g ∈ H ↔ g • r = r := by
  rw [← hstab, mem_stabilizer_iff]

theorem autHat_smul (hstab : stabilizer G r = H) (hα : α ∈ pointwiseFixingAut H) (g : G) :
    autHat r α (g • r) = α g • r := by
  have h1 : g⁻¹ * ptPick G r (g • r) ∈ H := by
    rw [mem_iff_smul_eq hstab, mul_smul, ptPick_spec, inv_smul_smul]
  have h2 : α (g⁻¹ * ptPick G r (g • r)) = g⁻¹ * ptPick G r (g • r) := hα _ h1
  rw [map_mul, map_inv] at h2
  have h3 : α (ptPick G r (g • r)) = α g * (g⁻¹ * ptPick G r (g • r)) := by
    rw [← h2]
    group
  rw [autHat, h3, mul_smul, (mem_iff_smul_eq hstab).1 h1]

theorem autHat_comm (hstab : stabilizer G r = H) (hα : α ∈ pointwiseFixingAut H) {h : G}
    (hh : h ∈ H) (p : X) : autHat r α (h • p) = h • autHat r α p := by
  rw [← ptPick_spec G r p, ← mul_smul, autHat_smul hstab hα, autHat_smul hstab hα, map_mul,
    hα h hh, mul_smul]

theorem autHat_injective (hstab : stabilizer G r = H) (hα : α ∈ pointwiseFixingAut H) :
    Function.Injective (autHat r α) := by
  intro p q hpq
  rw [← ptPick_spec G r p, ← ptPick_spec G r q, autHat_smul hstab hα,
    autHat_smul hstab hα] at hpq
  have h1 : α ((ptPick G r p)⁻¹ * ptPick G r q) ∈ H := by
    rw [map_mul, map_inv, mem_iff_smul_eq hstab, mul_smul, ← hpq, inv_smul_smul]
  have h2 : (ptPick G r p)⁻¹ * ptPick G r q ∈ H := by
    have h3 : α⁻¹ (α ((ptPick G r p)⁻¹ * ptPick G r q)) =
        α ((ptPick G r p)⁻¹ * ptPick G r q) := (pointwiseFixingAut H).inv_mem hα _ h1
    rw [MulAut.inv_apply, MulEquiv.symm_apply_apply] at h3
    rw [h3]
    exact h1
  rw [mem_iff_smul_eq hstab, mul_smul, inv_smul_eq_iff] at h2
  rw [← ptPick_spec G r p, ← ptPick_spec G r q]
  exact h2.symm

theorem autHat_mul (hstab : stabilizer G r = H) (hα : α ∈ pointwiseFixingAut H) {β : MulAut G}
    (hβ : β ∈ pointwiseFixingAut H) (p : X) : autHat r (α * β) p = autHat r α (autHat r β p) := by
  rw [← ptPick_spec G r p, autHat_smul hstab ((pointwiseFixingAut H).mul_mem hα hβ),
    autHat_smul hstab hβ, autHat_smul hstab hα, MulAut.mul_apply]

theorem autHat_one (p : X) : autHat r (1 : MulAut G) p = p := by
  rw [autHat, MulAut.one_apply, ptPick_spec]

theorem autHat_pow (hstab : stabilizer G r = H) (hα : α ∈ pointwiseFixingAut H) (m : ℕ)
    (p : X) : autHat r (α ^ m) p = (autHat r α)^[m] p := by
  induction m generalizing p with
  | zero => rw [pow_zero, autHat_one]; rfl
  | succ m ih =>
    rw [pow_succ, autHat_mul hstab ((pointwiseFixingAut H).pow_mem hα m) hα, ih,
      Function.iterate_succ_apply]

theorem orbit_autHat (hstab : stabilizer G r = H) (hα : α ∈ pointwiseFixingAut H) (p : X) :
    orbit H (autHat r α p) = autHat r α '' orbit H p := by
  ext q
  constructor
  · rintro ⟨h, rfl⟩
    refine ⟨h • p, ⟨h, rfl⟩, ?_⟩
    show autHat r α ((h : G) • p) = (h : G) • autHat r α p
    exact autHat_comm hstab hα h.2 p
  · rintro ⟨_, ⟨h, rfl⟩, rfl⟩
    refine ⟨h, ?_⟩
    show (h : G) • autHat r α p = autHat r α ((h : G) • p)
    exact (autHat_comm hstab hα h.2 p).symm

theorem ncard_orbit_autHat (hstab : stabilizer G r = H) (hα : α ∈ pointwiseFixingAut H)
    (p : X) : (orbit H (autHat r α p)).ncard = (orbit H p).ncard := by
  rw [orbit_autHat hstab hα, Set.ncard_image_of_injective _ (autHat_injective hstab hα)]

theorem exists_autHat_fixed [Finite X] (hstab : stabilizer G r = H)
    (hα : α ∈ pointwiseFixingAut H) {p : ℕ} [Fact p.Prime] (hαp : α ^ p = 1) {x₀ : X}
    (huniq : ∀ x, (orbit H x).ncard = (orbit H x₀).ncard → orbit H x = orbit H x₀)
    (hd : ¬ p ∣ (orbit H x₀).ncard) : ∃ x ∈ orbit H x₀, autHat r α x = x := by
  refine exists_fixed_of_iterate (φ := autHat r α) (Δ := orbit H x₀) (fun x hx => ?_)
    (fun x => ?_) (by rwa [Nat.card_coe_set_eq])
  · have h1 : orbit H x = orbit H x₀ := orbit_eq_iff.2 hx
    have h2 : orbit H (autHat r α x) = orbit H x₀ := by
      apply huniq
      rw [ncard_orbit_autHat hstab hα, h1]
    rw [← h2]
    exact mem_orbit_self _
  · rw [← autHat_pow hstab hα, hαp, autHat_one]

theorem pow_apply_eq_mul (hα : α ∈ pointwiseFixingAut H) {g h : G} (hh : h ∈ H)
    (e : α g = g * h) (m : ℕ) : (α ^ m) g = g * h ^ m := by
  induction m with
  | zero => rw [pow_zero, pow_zero, mul_one]; rfl
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, ih, map_mul, e, hα _ (H.pow_mem hh m), mul_assoc,
      ← pow_succ']

theorem eq_one_of_fix (hcoatom : IsCoatom H) (hα : α ∈ pointwiseFixingAut H) {g : G}
    (hg : g ∉ H) (e : α g = g) : α = 1 := by
  let F : Subgroup G :=
    { carrier := {j | α j = j}
      mul_mem' := fun {a b} (ha : α a = a) (hb : α b = b) =>
        show α (a * b) = a * b by rw [map_mul, ha, hb]
      one_mem' := map_one α
      inv_mem' := fun {a} (ha : α a = a) => show α a⁻¹ = a⁻¹ by rw [map_inv, ha] }
  have hHF : H ≤ F := fun h hh => hα h hh
  have hgF : g ∈ F := e
  have hlt : H < F := lt_of_le_of_ne hHF fun h => hg (by rw [h]; exact hgF)
  have htop : F = ⊤ := hcoatom.2 F hlt
  ext j
  have hj : j ∈ F := by rw [htop]; exact Subgroup.mem_top j
  exact hj

@[expose] def Dg (H : Subgroup G) (g : G) : Subgroup G := H ⊓ H.comap (MulAut.conj g).toMonoidHom

theorem mem_Dg {g d : G} : d ∈ Dg H g ↔ d ∈ H ∧ g * d * g⁻¹ ∈ H := by
  rw [Dg, Subgroup.mem_inf, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]

theorem Dg_le (g : G) : Dg H g ≤ H := inf_le_left

theorem commute_Dg (hα : α ∈ pointwiseFixingAut H) {g h : G} (e : α g = g * h) {d : G}
    (hd : d ∈ Dg H g) : Commute h d := by
  rw [mem_Dg] at hd
  have h1 : α (g * d * g⁻¹) = g * d * g⁻¹ := hα _ hd.2
  rw [map_mul, map_mul, map_inv, e, hα d hd.1] at h1
  have h2 : h * d * h⁻¹ = d := by
    have h3 : g⁻¹ * (g * h * d * (g * h)⁻¹) * g = g⁻¹ * (g * d * g⁻¹) * g := by rw [h1]
    rwa [show g⁻¹ * (g * h * d * (g * h)⁻¹) * g = h * d * h⁻¹ by group,
      show g⁻¹ * (g * d * g⁻¹) * g = d by group] at h3
  show h * d = d * h
  calc h * d = h * d * h⁻¹ * h := by group
    _ = d * h := by rw [h2]

omit [IsPretransitive G X] in
theorem card_Dg (hstab : stabilizer G r = H) (g : G) :
    Nat.card (Dg H g) * (orbit H (g • r)).ncard = Nat.card H := by
  have e : Dg H g ≃ stabilizer H (g • r) :=
    { toFun := fun d => ⟨⟨g * d * g⁻¹, (mem_Dg.1 d.2).2⟩, by
        rw [mem_stabilizer_iff]
        show (g * d * g⁻¹) • g • r = g • r
        rw [mul_smul, mul_smul, inv_smul_smul, (mem_iff_smul_eq hstab).1 (mem_Dg.1 d.2).1]⟩
      invFun := fun s => ⟨g⁻¹ * s * g, by
        rw [mem_Dg]
        have hs : (s : G) • g • r = g • r := mem_stabilizer_iff.1 s.2
        refine ⟨?_, ?_⟩
        · rw [mem_iff_smul_eq hstab, mul_smul, mul_smul, hs, inv_smul_smul]
        · rw [show g * (g⁻¹ * (s : G) * g) * g⁻¹ = s by group]
          exact s.1.2⟩
      left_inv := fun d => Subtype.ext (by dsimp only; group)
      right_inv := fun s => Subtype.ext (Subtype.ext (by dsimp only; group)) }
  rw [Nat.card_congr e, ← index_stabilizer, Subgroup.card_mul_index]

theorem exists_centralizing_element [Finite X] (hstab : stabilizer G r = H)
    (hcoatom : IsCoatom H) (hα : α ∈ pointwiseFixingAut H) (hα1 : α ≠ 1) {p : ℕ}
    [Fact p.Prime] (hαp : α ^ p = 1) {x₀ : X}
    (huniq : ∀ x, (orbit H x).ncard = (orbit H x₀).ncard → orbit H x = orbit H x₀)
    (hd : ¬ p ∣ (orbit H x₀).ncard) (hd1 : (orbit H x₀).ncard ≠ 1) :
    ∃ g : G, ∃ h ∈ H, orderOf h = p ∧ (∀ d ∈ Dg H g, Commute h d) ∧
      Nat.card (Dg H g) * (orbit H x₀).ncard = Nat.card H := by
  obtain ⟨x, hx, hfix⟩ := exists_autHat_fixed hstab hα hαp huniq hd
  have hgx : ptPick G r x • r = x := ptPick_spec G r x
  have hfix' : α (ptPick G r x) • r = ptPick G r x • r := by
    rw [← autHat_smul hstab hα, hgx, hfix]
  have hhH : (ptPick G r x)⁻¹ * α (ptPick G r x) ∈ H := by
    rw [mem_iff_smul_eq hstab, mul_smul, hfix', inv_smul_smul]
  have e : α (ptPick G r x) = ptPick G r x * ((ptPick G r x)⁻¹ * α (ptPick G r x)) := by group
  have hxo : orbit H x = orbit H x₀ := orbit_eq_iff.2 hx
  have hgH : ptPick G r x ∉ H := by
    intro hgH
    apply hd1
    have h1 : x = r := by rw [← hgx]; exact (mem_iff_smul_eq hstab).1 hgH
    have h2 : orbit H r = {r} := by
      ext y
      constructor
      · rintro ⟨k, rfl⟩
        exact (mem_iff_smul_eq hstab).1 k.2
      · intro hy
        rw [Set.mem_singleton_iff.1 hy]
        exact mem_orbit_self r
    rw [← hxo, h1, h2, Set.ncard_singleton]
  refine ⟨ptPick G r x, _, hhH, ?_, fun d hd => commute_Dg hα e hd, ?_⟩
  · have hp1 : ((ptPick G r x)⁻¹ * α (ptPick G r x)) ^ p = 1 := by
      have h1 := pow_apply_eq_mul hα hhH e p
      rw [hαp, MulAut.one_apply] at h1
      exact mul_left_cancel (h1.symm.trans (mul_one _).symm)
    have hne : (ptPick G r x)⁻¹ * α (ptPick G r x) ≠ 1 := by
      intro h1
      apply hα1
      refine eq_one_of_fix hcoatom hα hgH ?_
      rw [e, h1, mul_one]
    exact orderOf_eq_prime hp1 hne
  · have h1 := card_Dg hstab (ptPick G r x)
    rw [hgx, hxo] at h1
    exact h1

end Hat

section Semidirect

variable {G : Type*} [Group G] {H N K : Subgroup G}

theorem pow_mul_inv_mem (hKH : K ≤ H) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) {n k : G}
    (hn : n ∈ N) (hk : k ∈ K) (m : ℕ) : (n * k) ^ m * (k ^ m)⁻¹ ∈ N := by
  induction m with
  | zero => rw [pow_zero, pow_zero, inv_one, mul_one]; exact N.one_mem
  | succ m ih =>
    have e : (n * k) ^ (m + 1) * (k ^ (m + 1))⁻¹ =
        ((n * k) ^ m * (k ^ m)⁻¹) * (k ^ m * n * (k ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [e]
    exact N.mul_mem ih (hnorm _ (H.pow_mem (hKH hk) m) n hn)

theorem orderOf_part (hKH : K ≤ H) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hNK : N ⊓ K = ⊥) (hN2 : IsPGroup 2 N) {p : ℕ} [hp : Fact p.Prime] (hp2 : p ≠ 2) {n k : G}
    (hn : n ∈ N) (hk : k ∈ K) (ho : orderOf (n * k) = p) : orderOf k = p := by
  have hkp : k ^ p = 1 := by
    have h1 := pow_mul_inv_mem hKH hnorm hn hk p
    have h2 : (n * k) ^ p = 1 := by rw [← ho]; exact pow_orderOf_eq_one _
    rw [h2, one_mul] at h1
    have h3 : (k ^ p)⁻¹ ∈ N ⊓ K := Subgroup.mem_inf.2 ⟨h1, K.inv_mem (K.pow_mem hk p)⟩
    rw [hNK, Subgroup.mem_bot, inv_eq_one] at h3
    exact h3
  have hk1 : k ≠ 1 := by
    intro hk1
    rw [hk1, mul_one] at ho
    obtain ⟨m, hm⟩ := hN2 ⟨n, hn⟩
    have h4 := orderOf_dvd_of_pow_eq_one hm
    rw [Subgroup.orderOf_mk, ho] at h4
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 (hp.out.dvd_of_dvd_pow h4))
  exact orderOf_eq_prime hkp hk1

theorem commute_part_of_mem (hKH : K ≤ H) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) {n k m : G} (hn : n ∈ N) (hk : k ∈ K)
    (hm : m ∈ N) (hc : Commute (n * k) m) : Commute k m := by
  have h1 : k * m * k⁻¹ ∈ N := hnorm k (hKH hk) m hm
  have h2 : n * k * m * (n * k)⁻¹ = k * m * k⁻¹ := by
    calc n * k * m * (n * k)⁻¹ = n * (k * m * k⁻¹) * n⁻¹ := by group
      _ = k * m * k⁻¹ * n * n⁻¹ := by rw [hcomm n hn _ h1]
      _ = k * m * k⁻¹ := by group
  have h3 : n * k * m * (n * k)⁻¹ = m := by
    rw [hc.eq, mul_inv_cancel_right]
  show k * m = m * k
  calc k * m = k * m * k⁻¹ * k := by group
    _ = m * k := by rw [← h2, h3]

theorem commute_parts (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) (hNK : N ⊓ K = ⊥)
    {h d n n' k k' : G} (hh : h ∈ H) (hd : d ∈ H) (hn : n ∈ N) (hn' : n' ∈ N) (hk : k ∈ K)
    (hk' : k' ∈ K) (eh : h = n * k) (ed : d = n' * k') (hc : Commute h d) : Commute k k' := by
  have ek : k = n⁻¹ * h := by rw [eh]; group
  have ek' : k' = n'⁻¹ * d := by rw [ed]; group
  have hdh : h * d * h⁻¹ = d := by rw [hc.eq, mul_inv_cancel_right]
  have hmem : k * k' * k⁻¹ * k'⁻¹ ∈ N := by
    have e : k * k' * k⁻¹ * k'⁻¹ = n⁻¹ * (h * n'⁻¹ * h⁻¹) * (d * n * d⁻¹) * n' := by
      rw [ek, ek']
      calc n⁻¹ * h * (n'⁻¹ * d) * (n⁻¹ * h)⁻¹ * (n'⁻¹ * d)⁻¹
          = n⁻¹ * (h * n'⁻¹ * h⁻¹) * (h * d * h⁻¹) * n * d⁻¹ * n' := by group
        _ = n⁻¹ * (h * n'⁻¹ * h⁻¹) * (d * n * d⁻¹) * n' := by rw [hdh]; group
    rw [e]
    exact N.mul_mem (N.mul_mem (N.mul_mem (N.inv_mem hn) (hnorm h hh _ (N.inv_mem hn')))
      (hnorm d hd n hn)) hn'
  have h1 : k * k' * k⁻¹ * k'⁻¹ ∈ N ⊓ K := Subgroup.mem_inf.2
    ⟨hmem, K.mul_mem (K.mul_mem (K.mul_mem hk hk') (K.inv_mem hk)) (K.inv_mem hk')⟩
  rw [hNK, Subgroup.mem_bot] at h1
  show k * k' = k' * k
  calc k * k' = k * k' * k⁻¹ * k'⁻¹ * (k' * k) := by group
    _ = k' * k := by rw [h1, one_mul]

theorem card_mul_card_dvd [Finite G] (hNH : N ≤ H) {D : Subgroup G} (hDH : D ≤ H)
    (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N) :
    Nat.card N * Nat.card D ∣ Nat.card (N ⊓ D : Subgroup G) * Nat.card H := by
  have hN' : (N.subgroupOf H).Normal := ⟨fun a ha b => by
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    exact hnorm b b.2 a ha⟩
  have hcN : Nat.card (N.subgroupOf H) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  have hinf : N.subgroupOf H ⊓ D.subgroupOf H = (N ⊓ D).subgroupOf H := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
  have hcI : Nat.card (N.subgroupOf H ⊓ D.subgroupOf H : Subgroup H) =
      Nat.card (N ⊓ D : Subgroup G) := by
    rw [hinf]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hNH)).toEquiv
  have hcD : Nat.card (D.subgroupOf H) = Nat.card D :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDH).toEquiv
  have h1 := Subgroup.relIndex_sup_right (D.subgroupOf H) (N.subgroupOf H)
  have h2 := Subgroup.relIndex_mul_card (H := N.subgroupOf H)
    (K := D.subgroupOf H ⊔ N.subgroupOf H)
  rw [inf_eq_left.2 le_sup_right, h1] at h2
  have h3 := Subgroup.relIndex_mul_card (H := N.subgroupOf H) (K := D.subgroupOf H)
  have h4 := Subgroup.card_subgroup_dvd_card (D.subgroupOf H ⊔ N.subgroupOf H)
  have h5 := Subgroup.card_mul_index (D.subgroupOf H)
  rw [hcN] at h2
  rw [hcI, hcD] at h3
  rw [hcD] at h5
  set j := (N.subgroupOf H).relIndex (D.subgroupOf H)
  set cI := Nat.card (N ⊓ D : Subgroup G)
  set idx := (D.subgroupOf H).index
  have hj : 0 < j := by
    rcases Nat.eq_zero_or_pos j with h | h
    · rw [h, zero_mul] at h3
      exact absurd h3.symm Nat.card_pos.ne'
    · exact h
  have h6 : Nat.card N ∣ cI * idx := by
    rw [← h2, ← h5, ← h3, mul_assoc] at h4
    exact Nat.dvd_of_mul_dvd_mul_left hj h4
  calc Nat.card N * Nat.card D = Nat.card N * (j * cI) := by rw [h3]
    _ ∣ (cI * idx) * (j * cI) := mul_dvd_mul_right h6 _
    _ = cI * Nat.card H := by rw [← h5, ← h3]; ring

end Semidirect

section Kernel

variable {G : Type*} [Group G] [Finite G] {X : Type*} [MulAction G X] [Finite X]
  [IsPretransitive G X] {H N K : Subgroup G} {r : X}

theorem prime_dvd_cases {p : ℕ} (hp : p.Prime) (h : p ∣ 501397585920) :
    p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 ∨ p = 11 ∨ p = 23 := by
  rw [show (501397585920 : ℕ) = 2 ^ 21 * 3 ^ 3 * 5 * 7 * 11 * 23 by norm_num] at h
  have e : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hd
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
          · exact Or.inl (e 2 Nat.prime_two (hp.dvd_of_dvd_pow h))
          · exact Or.inr (Or.inl (e 3 Nat.prime_three (hp.dvd_of_dvd_pow h)))
        · exact Or.inr (Or.inr (Or.inl (e 5 (by norm_num) h)))
      · exact Or.inr (Or.inr (Or.inr (Or.inl (e 7 (by norm_num) h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (e 11 (by norm_num) h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (e 23 (by norm_num) h)))))

theorem not_dvd_15180 {p : ℕ} (hp : p.Prime) (h2 : p ≠ 2) (h3 : p ≠ 3) (h5 : p ≠ 5)
    (h11 : p ≠ 11) (h23 : p ≠ 23) : ¬ p ∣ 15180 := by
  intro h
  have e : ∀ q : ℕ, q.Prime → p ∣ q → p = q := fun q hq hd =>
    (Nat.prime_dvd_prime_iff_eq hp hq).1 hd
  rw [show (15180 : ℕ) = 2 ^ 2 * 3 * 5 * 11 * 23 by norm_num] at h
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
        · exact h2 (e 2 Nat.prime_two (hp.dvd_of_dvd_pow h))
        · exact h3 (e 3 Nat.prime_three h)
      · exact h5 (e 5 (by norm_num) h)
    · exact h11 (e 11 (by norm_num) h)
  · exact h23 (e 23 (by norm_num) h)

theorem pointwise_kernel_element_trivial (hstab : stabilizer G r = H) (hcoatom : IsCoatom H)
    (hNH : N ≤ H) (hKH : K ≤ H) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNK : N ⊓ K = ⊥)
    (hprod : ∀ h ∈ H, ∃ n ∈ N, ∃ k ∈ K, h = n * k) (hN2 : IsPGroup 2 N)
    (hcardN : Nat.card N = 2048) (hcardH : Nat.card H = 501397585920)
    (horb : ∀ d ∈ ({28336, 15180, 82575360} : Set ℕ), ∃ x₀ : X, (orbit H x₀).ncard = d ∧
      ∀ x : X, (orbit H x).ncard = d → orbit H x = orbit H x₀)
    (h5 : ∀ k ∈ K, orderOf k = 5 → Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup G) = 8)
    (h7 : ∀ k ∈ K, orderOf k = 7 → Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup G) = 4)
    (h1123 : ∀ e ∈ K, ∀ f ∈ K, orderOf e = 11 → orderOf f = 23 → Commute e f → False)
    {α : MulAut G} (hα : α ∈ pointwiseFixingAut H) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hαp : α ^ p = 1) : α = 1 := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  by_contra hα1
  have key : ∀ d ∈ ({28336, 15180, 82575360} : Set ℕ), ¬ p ∣ d →
      ∃ g : G, ∃ h ∈ H, orderOf h = p ∧ (∀ x ∈ Dg H g, Commute h x) ∧
        Nat.card (Dg H g) * d = 501397585920 := by
    intro d hd hpd
    obtain ⟨x₀, hx₀, hu⟩ := horb d hd
    have hd1 : (orbit H x₀).ncard ≠ 1 := by
      rw [hx₀]
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hd
      rcases hd with rfl | rfl | rfl <;> norm_num
    obtain ⟨g, h, hh, ho, hc, hcard⟩ := exists_centralizing_element hstab hcoatom hα hα1 hαp
      (fun x hx => hu x (hx.trans hx₀)) (by rwa [hx₀]) hd1
    exact ⟨g, h, hh, ho, hc, by rw [← hx₀, hcard, hcardH]⟩
  have big : ∀ {g : G} {d : ℕ}, Nat.card (Dg H g) * d = 501397585920 →
      2048 ∣ Nat.card (N ⊓ Dg H g : Subgroup G) * d ∧
        Nat.card (N ⊓ Dg H g : Subgroup G) ∣ 2048 := by
    intro g d hD
    have h1 := card_mul_card_dvd hNH (Dg_le g) hnorm
    rw [hcardN, hcardH, ← hD] at h1
    have hpos : 0 < Nat.card (Dg H g) := Nat.card_pos
    refine ⟨Nat.dvd_of_mul_dvd_mul_left hpos ?_, ?_⟩
    · rw [show Nat.card (Dg H g) * (Nat.card (N ⊓ Dg H g : Subgroup G) * d) =
          Nat.card (N ⊓ Dg H g : Subgroup G) * (Nat.card (Dg H g) * d) by ring]
      rw [mul_comm (Nat.card (Dg H g)) 2048]
      exact h1
    · rw [← hcardN]
      exact Subgroup.card_dvd_of_le inf_le_left
  have central : ∀ (q d c : ℕ), q = p → (∀ k ∈ K, orderOf k = q →
      Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup G) = c) →
      d ∈ ({28336, 15180, 82575360} : Set ℕ) → ¬ p ∣ d →
      (∀ m : ℕ, m ≤ c → 2048 ∣ m * d → m ∣ 2048 → False) → False := by
    intro q d c hq hcent hd hpd hm
    obtain ⟨g, h, hh, ho, hc, hD⟩ := key d hd hpd
    obtain ⟨n, hn, k, hk, rfl⟩ := hprod h hh
    have hok : orderOf k = q := hq ▸ orderOf_part hKH hnorm hNK hN2 hp2 hn hk ho
    have hle : (N ⊓ Dg H g : Subgroup G) ≤ Subgroup.centralizer {k} ⊓ N := by
      intro m hm
      rw [Subgroup.mem_inf] at hm
      refine Subgroup.mem_inf.2 ⟨Subgroup.mem_centralizer_singleton_iff.2 ?_, hm.1⟩
      exact (commute_part_of_mem hKH hnorm hcomm hn hk hm.1 (hc m hm.2)).eq.symm
    have hcard := Subgroup.card_le_of_le hle
    rw [hcent k hk hok] at hcard
    obtain ⟨hb1, hb2⟩ := big hD
    exact hm _ hcard hb1 hb2
  have cauchy : ∀ {g : G} (q : ℕ), q.Prime → q ∣ 6072 → Nat.card (Dg H g) = 6072 →
      ∃ d ∈ Dg H g, orderOf d = q := by
    intro g q hq hqd hD
    have : Fact q.Prime := ⟨hq⟩
    obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := Dg H g) q (hD ▸ hqd)
    exact ⟨d, d.2, by rw [← hd, Subgroup.orderOf_coe]⟩
  have h82 : (82575360 : ℕ) ∈ ({28336, 15180, 82575360} : Set ℕ) := by simp
  have hD82 : ∀ {g : G}, Nat.card (Dg H g) * 82575360 = 501397585920 →
      Nat.card (Dg H g) = 6072 := by
    intro g hD
    omega
  rcases eq_or_ne p 5 with rfl | h5p
  · refine central 5 28336 8 rfl h5 (by simp) (by norm_num) fun m hm h1 h2 => ?_
    revert h1 h2
    interval_cases m <;> decide
  rcases eq_or_ne p 7 with rfl | h7p
  · refine central 7 15180 4 rfl h7 (by simp) (by norm_num) fun m hm h1 h2 => ?_
    revert h1 h2
    interval_cases m <;> decide
  rcases eq_or_ne p 11 with rfl | h11p
  · obtain ⟨g, h, hh, ho, hc, hD⟩ := key 82575360 h82 (by norm_num)
    obtain ⟨d, hd, hod⟩ := cauchy 23 (by norm_num) (by norm_num) (hD82 hD)
    obtain ⟨n, hn, k, hk, rfl⟩ := hprod h hh
    obtain ⟨n', hn', k', hk', rfl⟩ := hprod d (Dg_le g hd)
    have : Fact (Nat.Prime 23) := ⟨by norm_num⟩
    exact h1123 k hk k' hk' (orderOf_part hKH hnorm hNK hN2 hp2 hn hk ho)
      (orderOf_part hKH hnorm hNK hN2 (by norm_num) hn' hk' hod)
      (commute_parts hnorm hNK hh (Dg_le g hd) hn hn' hk hk' rfl rfl (hc _ hd))
  rcases eq_or_ne p 23 with rfl | h23p
  · obtain ⟨g, h, hh, ho, hc, hD⟩ := key 82575360 h82 (by norm_num)
    obtain ⟨d, hd, hod⟩ := cauchy 11 (by norm_num) (by norm_num) (hD82 hD)
    obtain ⟨n, hn, k, hk, rfl⟩ := hprod h hh
    obtain ⟨n', hn', k', hk', rfl⟩ := hprod d (Dg_le g hd)
    have : Fact (Nat.Prime 11) := ⟨by norm_num⟩
    exact h1123 k' hk' k hk (orderOf_part hKH hnorm hNK hN2 (by norm_num) hn' hk' hod)
      (orderOf_part hKH hnorm hNK hN2 hp2 hn hk ho)
      (commute_parts hnorm hNK hh (Dg_le g hd) hn hn' hk hk' rfl rfl (hc _ hd)).symm
  obtain ⟨g, h, hh, ho, -, -⟩ := key 15180 (by simp)
    (not_dvd_15180 hp hp2 (by omega) h5p h11p h23p)
  have hdvd : p ∣ 501397585920 := by
    have h1 := orderOf_dvd_natCard (⟨h, hh⟩ : H)
    rw [Subgroup.orderOf_mk, ho, hcardH] at h1
    exact h1
  rcases prime_dvd_cases hp hdvd with h | h | h | h | h | h <;> omega

theorem pointwise_kernel_no_large_primes (hstab : stabilizer G r = H) (hcoatom : IsCoatom H)
    (hNH : N ≤ H) (hKH : K ≤ H) (hnorm : ∀ h ∈ H, ∀ n ∈ N, h * n * h⁻¹ ∈ N)
    (hcomm : ∀ a ∈ N, ∀ b ∈ N, a * b = b * a) (hNK : N ⊓ K = ⊥)
    (hprod : ∀ h ∈ H, ∃ n ∈ N, ∃ k ∈ K, h = n * k) (hN2 : IsPGroup 2 N)
    (hcardN : Nat.card N = 2048) (hcardH : Nat.card H = 501397585920)
    (horb : ∀ d ∈ ({28336, 15180, 82575360} : Set ℕ), ∃ x₀ : X, (orbit H x₀).ncard = d ∧
      ∀ x : X, (orbit H x).ncard = d → orbit H x = orbit H x₀)
    (h5 : ∀ k ∈ K, orderOf k = 5 → Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup G) = 8)
    (h7 : ∀ k ∈ K, orderOf k = 7 → Nat.card (Subgroup.centralizer {k} ⊓ N : Subgroup G) = 4)
    (h1123 : ∀ e ∈ K, ∀ f ∈ K, orderOf e = 11 → orderOf f = 23 → Commute e f → False) :
    (∀ p : ℕ, p.Prime → 5 ≤ p → ∀ A : Subgroup (pointwiseFixingAut H), IsPGroup p A → A = ⊥) ∧
      ∀ p : ℕ, p.Prime → p ∣ Nat.card (pointwiseFixingAut H) → p = 2 ∨ p = 3 := by
  have htriv := fun {α : MulAut G} (hα : α ∈ pointwiseFixingAut H) {p : ℕ} (hp : p.Prime)
      (hp5 : 5 ≤ p) (hαp : α ^ p = 1) =>
    pointwise_kernel_element_trivial hstab hcoatom hNH hKH hnorm hcomm hNK hprod hN2 hcardN
      hcardH horb h5 h7 h1123 hα hp hp5 hαp
  have hpow : ∀ {p : ℕ}, p.Prime → 5 ≤ p → ∀ (k : ℕ) (β : pointwiseFixingAut H),
      β ^ p ^ k = 1 → β = 1 := by
    intro p hp hp5 k
    induction k with
    | zero => intro β hβ; rwa [pow_zero, pow_one] at hβ
    | succ k ih =>
      intro β hβ
      refine ih β (Subtype.ext ?_)
      refine htriv (β ^ p ^ k).2 hp hp5 ?_
      rw [← Subgroup.coe_pow, ← pow_mul, ← pow_succ, hβ, Subgroup.coe_one]
  refine ⟨fun p hp hp5 A hA => ?_, fun p hp hdvd => ?_⟩
  · rw [eq_bot_iff]
    intro β hβ
    obtain ⟨k, hk⟩ := hA ⟨β, hβ⟩
    rw [Subgroup.mem_bot]
    exact hpow hp hp5 k β (congrArg Subtype.val hk)
  · have : Finite (MulAut G) := Finite.of_injective _ (DFunLike.coe_injective (F := MulAut G))
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨β, hβ⟩ := exists_prime_orderOf_dvd_card' (G := pointwiseFixingAut H) p hdvd
    by_contra hne
    have hp5 : 5 ≤ p := by
      rcases Nat.lt_or_ge p 5 with hlt | h
      · have h2 := hp.two_le
        interval_cases p
        · exact absurd (Or.inl rfl) hne
        · exact absurd (Or.inr rfl) hne
        · exact absurd hp (by norm_num)
      · exact h
    have h1 := hpow hp hp5 1 β (by rw [pow_one, ← hβ, pow_orderOf_eq_one])
    rw [h1, orderOf_one] at hβ
    exact hp.one_lt.ne hβ

end Kernel

end CFSG.Sporadic.J4Schreier
