module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.PrimeOrderFix

open MulAction Subgroup

variable {G α : Type*} [Group G] [Finite G] [MulAction G α]

theorem factorization_eq_one {p n : ℕ} (hp : p.Prime) (hn : n ≠ 0) (h1 : p ∣ n)
    (h2 : ¬ p ^ 2 ∣ n) : n.factorization p = 1 := by
  have a := (hp.pow_dvd_iff_le_factorization (k := 1) hn).1 (by rwa [pow_one])
  have b := mt (hp.pow_dvd_iff_le_factorization (k := 2) hn).2 h2
  omega

theorem exists_normalizer_smul {p : ℕ} [hp : Fact p.Prime] {P : Subgroup G} (hP : Nat.card P = p)
    (hG : ¬ p ^ 2 ∣ Nat.card G) {x y : α} (hx : P ≤ stabilizer G x) (hy : P ≤ stabilizer G y)
    (hxy : y ∈ orbit G x) : ∃ n ∈ (normalizer (P : Set G)), n • x = y := by
  obtain ⟨g, rfl⟩ := hxy
  set K := stabilizer G x
  let Q : Subgroup G := P.map (MulAut.conj g⁻¹).toMonoidHom
  have hinj : ∀ c : G, Function.Injective (MulAut.conj c).toMonoidHom :=
    fun c => (MulAut.conj c).injective
  have hQ : Q ≤ K := by
    rintro _ ⟨h, hh, rfl⟩
    have h' := hy hh
    rw [mem_stabilizer_iff] at h' ⊢
    change (g⁻¹ * h * g⁻¹⁻¹) • x = x
    rw [inv_inv, mul_smul, mul_smul, h', inv_smul_smul]
  have hcQ : Nat.card Q = p := (card_map_of_injective (hinj _)).trans hP
  have hK0 : Nat.card K ≠ 0 := Nat.card_pos.ne'
  have hKf : (Nat.card K).factorization p = 1 := by
    refine factorization_eq_one hp.out hK0 (hP ▸ card_dvd_of_le hx) fun h => hG ?_
    exact h.trans (card_subgroup_dvd_card K)
  have e1 : Nat.card (P.subgroupOf K) = p ^ (Nat.card K).factorization p := by
    rw [hKf, pow_one, Nat.card_congr (subgroupOfEquivOfLe hx).toEquiv, hP]
  have e2 : Nat.card (Q.subgroupOf K) = p ^ (Nat.card K).factorization p := by
    rw [hKf, pow_one, Nat.card_congr (subgroupOfEquivOfLe hQ).toEquiv, hcQ]
  obtain ⟨k, hk⟩ := MulAction.exists_smul_eq K (Sylow.ofCard _ e2) (Sylow.ofCard _ e1)
  have hm : P.map (MulAut.conj ((k : G) * g⁻¹)).toMonoidHom = P := by
    refine eq_of_le_of_card_ge ?_ (card_map_of_injective (hinj _)).ge
    rintro _ ⟨h, hh, rfl⟩
    have hq : (⟨g⁻¹ * h * g⁻¹⁻¹, hQ ⟨h, hh, rfl⟩⟩ : K) ∈ Q.subgroupOf K :=
      mem_subgroupOf.2 ⟨h, hh, rfl⟩
    have hmem : k * ⟨g⁻¹ * h * g⁻¹⁻¹, hQ ⟨h, hh, rfl⟩⟩ * k⁻¹ ∈
        ((k • Sylow.ofCard _ e2 : Sylow p K) : Set K) := by
      rw [Sylow.coe_smul]
      exact ⟨_, hq, rfl⟩
    rw [hk] at hmem
    have hmem' := mem_subgroupOf.1 hmem
    change (k : G) * (g⁻¹ * h * g⁻¹⁻¹) * (k : G)⁻¹ ∈ P at hmem'
    change ((k : G) * g⁻¹) * h * ((k : G) * g⁻¹)⁻¹ ∈ P
    convert hmem' using 1
    group
  refine ⟨((k : G) * g⁻¹)⁻¹, inv_mem (mem_normalizer_iff_map_conj_eq.2 hm), ?_⟩
  have hk' : (k : G)⁻¹ • x = x := by
    rw [inv_smul_eq_iff]
    exact k.2.symm
  rw [mul_inv_rev, inv_inv, mul_smul, hk']

theorem card_normalizer_le (u : G) :
    Nat.card (normalizer (zpowers u : Set G)) ≤ Nat.card (zpowers u) * Nat.card (centralizer {u}) := by
  classical
  have hc : ∀ n : (normalizer (zpowers u : Set G)), (n : G) * u * (n : G)⁻¹ ∈ zpowers u :=
    fun n => (mem_normalizer_iff.1 n.2 u).1 (mem_zpowers u)
  let f : (normalizer (zpowers u : Set G)) → zpowers u := fun n => ⟨_, hc n⟩
  let r : zpowers u → (normalizer (zpowers u : Set G)) := fun q =>
    if h : ∃ n, f n = q then h.choose else 1
  have hr : ∀ n, f (r (f n)) = f n := fun n => by
    have h : ∃ m, f m = f n := ⟨n, rfl⟩
    simp only [r, dif_pos h]
    exact h.choose_spec
  have hcen : ∀ a b : (normalizer (zpowers u : Set G)), f a = f b →
      ((a : G)⁻¹ * b) ∈ centralizer {u} := fun a b h => by
    have h' : (a : G) * u * (a : G)⁻¹ = (b : G) * u * (b : G)⁻¹ := congrArg Subtype.val h
    rw [mem_centralizer_singleton_iff]
    calc (a : G)⁻¹ * b * u = (a : G)⁻¹ * ((b : G) * u * (b : G)⁻¹) * b := by group
      _ = (a : G)⁻¹ * ((a : G) * u * (a : G)⁻¹) * b := by rw [h']
      _ = u * ((a : G)⁻¹ * b) := by group
  let F : (normalizer (zpowers u : Set G)) → zpowers u × centralizer {u} := fun n =>
    (f n, ⟨_, hcen _ _ (hr n)⟩)
  have hF : Function.Injective F := fun a b h => by
    have h1 : f a = f b := congrArg Prod.fst h
    have h2 := congrArg (fun z => (z.2 : G)) h
    simp only [F, h1] at h2
    exact Subtype.ext (mul_left_cancel h2)
  exact (Nat.card_le_card_of_injective F hF).trans_eq (Nat.card_prod _ _)

theorem not_dvd_card_orbit {p : ℕ} {u : G} (hu : orderOf u = p) (hG : ¬ p ^ 2 ∣ Nat.card G)
    {x : α} (hx : u • x = x) : ¬ p ∣ Nat.card (orbit G x) := by
  intro hd
  have hs : p ∣ Nat.card (stabilizer G x) := by
    rw [← hu, ← Nat.card_zpowers]
    exact card_dvd_of_le (zpowers_le.2 hx)
  have hcard := card_mul_index (stabilizer G x)
  rw [index_stabilizer, ← Nat.card_coe_set_eq] at hcard
  apply hG
  rw [← hcard, pow_two]
  exact Nat.mul_dvd_mul hs hd

theorem fix_orbit_eq [Finite α] {p : ℕ} [hp : Fact p.Prime] {u : G} (hu : orderOf u = p)
    (hG : ¬ p ^ 2 ∣ Nat.card G) (hC : Nat.card (centralizer {u}) ≤ p) {x : α}
    (hO : Nat.card (orbit G x) % p = 1) {y z : α} (hy : y ∈ orbit G x) (hz : z ∈ orbit G x)
    (hyu : u • y = y) (hzu : u • z = z) : y = z := by
  set P := zpowers u
  have hP : Nat.card P = p := by rw [Nat.card_zpowers, hu]
  have hPy : P ≤ stabilizer G y := zpowers_le.2 hyu
  let T := fixedPoints P (orbit G x)
  have hT : ∀ t : T, P ≤ stabilizer G (t.1 : α) := fun t => zpowers_le.2 (by
    have := (mem_fixedPoints.1 t.2) ⟨u, mem_zpowers u⟩
    rw [mem_stabilizer_iff]
    exact congrArg Subtype.val this)
  have hyO : y ∈ orbit G x := hy
  have hTy : ∀ t : T, ∃ n : (normalizer (P : Set G)), n • y = (t.1 : α) := fun t => by
    have hty : (t.1 : α) ∈ orbit G y := by
      rw [orbit_eq_iff.2 hyO]
      exact t.1.2
    obtain ⟨n, hn, he⟩ := exists_normalizer_smul hP hG hPy (hT t) hty
    exact ⟨⟨n, hn⟩, he⟩
  let g : T → orbit (normalizer (P : Set G)) y := fun t => ⟨t.1, (hTy t).choose, (hTy t).choose_spec⟩
  have hg : Function.Injective g := fun a b h => by
    have h' : ((g a : α)) = (g b : α) := congrArg Subtype.val h
    exact Subtype.ext (Subtype.ext h')
  have hN := card_mul_index (stabilizer (normalizer (P : Set G)) y)
  rw [index_stabilizer] at hN
  have hPs : P.subgroupOf (normalizer (P : Set G)) ≤ stabilizer (normalizer (P : Set G)) y := fun n hn => by
    rw [mem_stabilizer_iff]
    exact hPy (mem_subgroupOf.1 hn)
  have hPc : Nat.card (P.subgroupOf (normalizer (P : Set G))) = p := by
    rw [Nat.card_congr (subgroupOfEquivOfLe le_normalizer).toEquiv, hP]
  have hps : p ≤ Nat.card (stabilizer (normalizer (P : Set G)) y) :=
    hPc ▸ card_le_of_le hPs
  have hNle := card_normalizer_le u
  rw [← Nat.card_coe_set_eq] at hN
  have horb : Nat.card (orbit (normalizer (P : Set G)) y) ≤ p := by
    have hp0 := hp.out.pos
    have : Nat.card (orbit (normalizer (P : Set G)) y) * p ≤ p * p := by
      calc Nat.card (orbit (normalizer (P : Set G)) y) * p
          ≤ Nat.card (orbit (normalizer (P : Set G)) y) * Nat.card (stabilizer (normalizer (P : Set G)) y) :=
            Nat.mul_le_mul_left _ hps
        _ = Nat.card (normalizer (P : Set G)) := by rw [mul_comm, hN]
        _ ≤ p * p := hNle.trans (by rw [hP]; exact Nat.mul_le_mul_left _ hC)
    exact Nat.le_of_mul_le_mul_right this hp0
  have hTc : Nat.card T ≤ p := (Nat.card_le_card_of_injective g hg).trans horb
  have hmod := (IsPGroup.of_card (n := 1) (hP.trans (pow_one p).symm)).card_modEq_card_fixedPoints
    (orbit G x)
  have hT1 : Nat.card T = 1 := by
    have h1 : Nat.card T % p = 1 := by
      rw [← hO]
      exact hmod.symm
    have hp2 := hp.out.two_le
    rcases Nat.lt_or_ge (Nat.card T) p with h | h
    · rwa [Nat.mod_eq_of_lt h] at h1
    · have : Nat.card T = p := le_antisymm hTc h
      rw [this, Nat.mod_self] at h1
      omega
  have hfix : ∀ w : α, (hw : w ∈ orbit G x) → u • w = w → (⟨w, hw⟩ : orbit G x) ∈ T :=
    fun w hw hwu => mem_fixedPoints.2 fun m => Subtype.ext (by
      obtain ⟨m, hm⟩ := m
      obtain ⟨k, rfl⟩ := mem_zpowers_iff.1 hm
      change u ^ k • w = w
      exact (mem_stabilizer_iff.1 ((zpowers_le.2 hwu) (zpow_mem (mem_zpowers u) k))))
  have hs := (Nat.card_eq_one_iff_unique.1 hT1).1
  have := Subsingleton.elim (⟨_, hfix y hy hyu⟩ : T) ⟨_, hfix z hz hzu⟩
  exact congrArg (fun t : T => (t.1 : α)) this

end CFSG.PrimeOrderFix

end
