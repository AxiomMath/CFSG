module

public import CFSG.RankThree.PartOne.Q1327Z.Transport
public import CFSG.RankThree.PartOne.Q1327Z.Row10Base
public import CFSG.RankThree.PartOne.S13K.Sp6Comm

public section

namespace CFSG.RankThree.PartOne.Q1327Z

section Abstract

variable {Γ : Type*} [Group Γ]

theorem noncomm_via_block {m c : Γ} {B₀ S : Subgroup Γ}
    (ha : ∀ s ∈ S, ∀ b ∈ B₀, Commute (m⁻¹ * s * m) b)
    (hc : m⁻¹ * c * m ∈ B₀) (hc1 : m⁻¹ * c * m ≠ 1)
    (hnc : ∀ l ∈ B₀, l ≠ 1 → ∃ y ∈ B₀, ¬ Commute l (y * l * y⁻¹)) :
    ∃ y ∈ Subgroup.centralizer (S : Set Γ), ¬ Commute c (y * c * y⁻¹) := by
  obtain ⟨y₀, hy₀, hnc'⟩ := hnc _ hc hc1
  refine ⟨m * y₀ * m⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have h1 := (ha s hs y₀ hy₀).eq
    calc s * (m * y₀ * m⁻¹) = m * (m⁻¹ * s * m * y₀) * m⁻¹ := by group
      _ = m * (y₀ * (m⁻¹ * s * m)) * m⁻¹ := by rw [h1]
      _ = m * y₀ * m⁻¹ * s := by group
  · intro hcomm
    apply hnc'
    have h2 := hcomm.map (MulAut.conj m⁻¹).toMonoidHom
    have e1 : (MulAut.conj m⁻¹).toMonoidHom c = m⁻¹ * c * m := by
      simp
    have e2 : (MulAut.conj m⁻¹).toMonoidHom ((m * y₀ * m⁻¹) * c * (m * y₀ * m⁻¹)⁻¹) =
        y₀ * (m⁻¹ * c * m) * y₀⁻¹ := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e1, e2] at h2
    exact h2

theorem eq_one_of_conj_eq_one {m c : Γ} (h : m⁻¹ * c * m = 1) : c = 1 :=
  calc c = m * (m⁻¹ * c * m) * m⁻¹ := by group
    _ = 1 := by rw [h]; group

end Abstract

section Model

open CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.KFQ CFSG.RankThree.PartOne.KFU

variable {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ}

theorem tor10_injective (hpq : p ∣ Nat.card K + 1) {x y : Fin 3 → (Qext K)ˣ}
    {hx : ∀ i, x i ^ p = 1} {hy : ∀ i, y i ^ p = 1} (h : tor10 hpq x hx = tor10 hpq y hy) :
    x = y :=
  torusEquiv_injective (congrArg Subtype.val h)

theorem tor10_congr (hpq : p ∣ Nat.card K + 1) {x y : Fin 3 → (Qext K)ˣ}
    {hx : ∀ i, x i ^ p = 1} {hy : ∀ i, y i ^ p = 1} (h : x = y) :
    tor10 hpq x hx = tor10 hpq y hy := by
  subst h
  rfl

theorem tor10_one (hpq : p ∣ Nat.card K + 1) :
    tor10 hpq (1 : Fin 3 → (Qext K)ˣ) (fun _ => one_pow _) = 1 :=
  Subtype.ext torusEquiv_one

theorem exists_tor10_of_isTor (hpq : p ∣ Nat.card K + 1) {g : ↥(M10 K)} (h : IsTor p g) :
    ∃ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1), g = tor10 hpq x hx := by
  obtain ⟨x, hx, hgx⟩ := h
  exact ⟨x, hx, Subtype.ext hgx⟩

theorem conj_tor10 (hpq : p ∣ Nat.card K + 1) (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1) :
    sg10 π s * tor10 hpq x hx * (sg10 π s)⁻¹ = tor10 hpq (sact π s x) (sact_pow hx) :=
  Subtype.ext (sgnPerm_conj hpq π s x (sact π s x) hx (fun _ => rfl))

theorem conj_tor10_symm (hpq : p ∣ Nat.card K + 1) (π : Equiv.Perm (Fin 3)) (s : Fin 3 → Bool)
    {x y : Fin 3 → (Qext K)ˣ} (hx : ∀ i, x i ^ p = 1) (hy : ∀ i, y i ^ p = 1)
    (h : sact π s x = y) :
    (sg10 π s)⁻¹ * tor10 hpq y hy * sg10 π s = tor10 hpq x hx := by
  have h1 := conj_tor10 hpq π s x hx
  rw [tor10_congr hpq h.symm (hy := sact_pow hx)] at *
  rw [← h1]
  group

theorem conj_tor10_perm (hpq : p ∣ Nat.card K + 1) (σ : Equiv.Perm (Fin 3))
    {a : Fin 3 → (Qext K)ˣ} (ha : ∀ i, a i ^ p = 1) :
    (sg10 σ (fun _ => false))⁻¹ * tor10 hpq a ha * sg10 σ (fun _ => false) =
      tor10 hpq (fun k => a (σ k)) (fun _ => ha _) := by
  refine conj_tor10_symm hpq σ (fun _ => false) (fun _ => ha _) ha ?_
  funext j
  simp [sact_apply]

theorem r10_fixed (hpq : p ∣ Nat.card K + 1) {g : ↥(M10 K)} {π : Equiv.Perm (Fin 3)}
    {ε : Fin 3 → Bool}
    (hπε : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1),
      g * tor10 hpq x hx * g⁻¹ = tor10 hpq (sact π ε x) (sact_pow hx))
    {s : ↥(M10 K)} (hs : IsTor p s) (hgs : g * s * g⁻¹ = s) :
    ∃ (a : Fin 3 → (Qext K)ˣ) (ha : ∀ i, a i ^ p = 1), s = tor10 hpq a ha ∧
      sact π ε a = a := by
  obtain ⟨a, ha, rfl⟩ := exists_tor10_of_isTor hpq hs
  refine ⟨a, ha, rfl, ?_⟩
  rw [hπε a ha] at hgs
  exact tor10_injective hpq hgs

theorem r10_inv (hpq : p ∣ Nat.card K + 1) {g : ↥(M10 K)} {π : Equiv.Perm (Fin 3)}
    {ε : Fin 3 → Bool}
    (hπε : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ i, x i ^ p = 1),
      g * tor10 hpq x hx * g⁻¹ = tor10 hpq (sact π ε x) (sact_pow hx))
    {c : ↥(M10 K)} (hc : IsTor p c) (hgc : g * c * g⁻¹ = c⁻¹) :
    ∃ (a : Fin 3 → (Qext K)ˣ) (ha : ∀ i, a i ^ p = 1), c = tor10 hpq a ha ∧
      sact π ε a = a⁻¹ := by
  obtain ⟨a, ha, rfl⟩ := exists_tor10_of_isTor hpq hc
  refine ⟨a, ha, rfl, ?_⟩
  rw [hπε a ha, tor10_inv] at hgc
  exact tor10_injective hpq hgc

omit [Finite K] in
theorem eq_one_of_inv_eq (hp : Odd p) {u : (Qext K)ˣ} (hu : u ^ p = 1) (h : u⁻¹ = u) : u = 1 := by
  apply eq_of_sq_eq hp hu (one_pow p)
  rw [mul_one]
  calc u * u = u⁻¹ * u := by rw [h]
    _ = 1 := inv_mul_cancel u

theorem r10_fam1 (hpq : p ∣ Nat.card K + 1)
    (hsN : ∀ l ∈ sBlk K, l ≠ 1 → ∃ y ∈ sBlk K, ¬ Commute l (y * l * y⁻¹))
    (hsM : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ k, x k ^ p = 1), x 1 = 1 → x 2 = 1 →
      tor10 hpq x hx ∈ sBlk K)
    (i : Fin 3) {S : Subgroup ↥(M10 K)}
    (hS : ∀ s ∈ S, ∃ (a : Fin 3 → (Qext K)ˣ) (ha : ∀ k, a k ^ p = 1),
      s = tor10 hpq a ha ∧ a i = 1)
    {xc : Fin 3 → (Qext K)ˣ} (hxc : ∀ k, xc k ^ p = 1) (hxc1 : ∀ j, j ≠ i → xc j = 1)
    (hc1 : tor10 hpq xc hxc ≠ 1) :
    ∃ y ∈ Subgroup.centralizer (S : Set ↥(M10 K)),
      ¬ Commute (tor10 hpq xc hxc) (y * tor10 hpq xc hxc * y⁻¹) := by
  have hσ0 : (Equiv.swap (0 : Fin 3) i) 0 = i := Equiv.swap_apply_left 0 i
  have hσ1 : (Equiv.swap (0 : Fin 3) i) 1 ≠ i := fun h =>
    absurd ((Equiv.swap (0 : Fin 3) i).injective (h.trans hσ0.symm)) (by decide)
  have hσ2 : (Equiv.swap (0 : Fin 3) i) 2 ≠ i := fun h =>
    absurd ((Equiv.swap (0 : Fin 3) i).injective (h.trans hσ0.symm)) (by decide)
  refine noncomm_via_block (m := sg10 (Equiv.swap 0 i) (fun _ => false)) (B₀ := sBlk K) ?_ ?_ ?_
    hsN
  · intro s hs b hb
    obtain ⟨a, ha, rfl, hai⟩ := hS s hs
    rw [conj_tor10_perm hpq _ ha]
    exact (Subtype.ext (sBlk_comm_tor hb (by simpa [hσ0] using hai))).symm
  · rw [conj_tor10_perm hpq _ hxc]
    exact hsM _ _ (hxc1 _ hσ1) (hxc1 _ hσ2)
  · exact fun h => hc1 (eq_one_of_conj_eq_one h)

theorem r10_fam2 (hpq : p ∣ Nat.card K + 1)
    (hdN : ∀ l ∈ dBlk K, l ≠ 1 → ∃ y ∈ dBlk K, ¬ Commute l (y * l * y⁻¹))
    (hdM : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ k, x k ^ p = 1), x 2 = 1 → x 0 * x 1 = 1 →
      tor10 hpq x hx ∈ dBlk K)
    {a b : Fin 3} (hab : a ≠ b) {S : Subgroup ↥(M10 K)}
    (hS : ∀ s ∈ S, ∃ (z : Fin 3 → (Qext K)ˣ) (hz : ∀ k, z k ^ p = 1),
      s = tor10 hpq z hz ∧ z b = z a)
    {xc : Fin 3 → (Qext K)ˣ} (hxc : ∀ k, xc k ^ p = 1) (hxcab : xc b = (xc a)⁻¹)
    (hxc1 : ∀ j, j ≠ a → j ≠ b → xc j = 1) (hc1 : tor10 hpq xc hxc ≠ 1) :
    ∃ y ∈ Subgroup.centralizer (S : Set ↥(M10 K)),
      ¬ Commute (tor10 hpq xc hxc) (y * tor10 hpq xc hxc * y⁻¹) := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_of_ne a b hab
  have hσ2a : σ 2 ≠ a := fun h => absurd (σ.injective (h.trans hσ0.symm)) (by decide)
  have hσ2b : σ 2 ≠ b := fun h => absurd (σ.injective (h.trans hσ1.symm)) (by decide)
  refine noncomm_via_block (m := sg10 σ (fun _ => false)) (B₀ := dBlk K) ?_ ?_ ?_ hdN
  · intro s hs bb hb
    obtain ⟨z, hz, rfl, hzab⟩ := hS s hs
    rw [conj_tor10_perm hpq σ hz]
    exact (Subtype.ext (dBlk_comm_tor hb (by simp [hσ0, hσ1, hzab]))).symm
  · rw [conj_tor10_perm hpq σ hxc]
    refine hdM _ _ (hxc1 _ hσ2a hσ2b) ?_
    simp only [hσ0, hσ1, hxcab]
    exact mul_inv_cancel _
  · exact fun h => hc1 (eq_one_of_conj_eq_one h)

theorem r10_fam3 (hpq : p ∣ Nat.card K + 1)
    (hdN : ∀ l ∈ dBlk K, l ≠ 1 → ∃ y ∈ dBlk K, ¬ Commute l (y * l * y⁻¹))
    (hdM : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ k, x k ^ p = 1), x 2 = 1 → x 0 * x 1 = 1 →
      tor10 hpq x hx ∈ dBlk K)
    {a b : Fin 3} (hab : a ≠ b) {S : Subgroup ↥(M10 K)}
    (hS : ∀ s ∈ S, ∃ (z : Fin 3 → (Qext K)ˣ) (hz : ∀ k, z k ^ p = 1),
      s = tor10 hpq z hz ∧ (z b)⁻¹ = z a)
    {xc : Fin 3 → (Qext K)ˣ} (hxc : ∀ k, xc k ^ p = 1) (hxcab : xc a = xc b)
    (hxc1 : ∀ j, j ≠ a → j ≠ b → xc j = 1) (hc1 : tor10 hpq xc hxc ≠ 1) :
    ∃ y ∈ Subgroup.centralizer (S : Set ↥(M10 K)),
      ¬ Commute (tor10 hpq xc hxc) (y * tor10 hpq xc hxc * y⁻¹) := by
  obtain ⟨σ, hσ0, hσ1⟩ := exists_perm_of_ne a b hab
  have hσ2a : σ 2 ≠ a := fun h => absurd (σ.injective (h.trans hσ0.symm)) (by decide)
  have hσ2b : σ 2 ≠ b := fun h => absurd (σ.injective (h.trans hσ1.symm)) (by decide)
  let tw : (Fin 3 → (Qext K)ˣ) → (Fin 3 → (Qext K)ˣ) := fun z j => if j = b then (z j)⁻¹ else z j
  have htw_pow : ∀ z : Fin 3 → (Qext K)ˣ, (∀ k, z k ^ p = 1) → ∀ k, tw z k ^ p = 1 := by
    intro z hz k
    simp only [tw]
    split_ifs
    · rw [inv_pow, hz k, inv_one]
    · exact hz k
  have hconj : ∀ (z : Fin 3 → (Qext K)ˣ) (hz : ∀ k, z k ^ p = 1),
      (sg10 1 (fun j => decide (j = b)) * sg10 σ (fun _ => false))⁻¹ * tor10 hpq z hz *
        (sg10 1 (fun j => decide (j = b)) * sg10 σ (fun _ => false)) =
      tor10 hpq (fun k => tw z (σ k)) (fun _ => htw_pow z hz _) := by
    intro z hz
    have h1 : (sg10 1 (fun j => decide (j = b)))⁻¹ * tor10 hpq z hz *
        sg10 1 (fun j => decide (j = b)) = tor10 hpq (tw z) (htw_pow z hz) := by
      refine conj_tor10_symm hpq 1 (fun j => decide (j = b)) (htw_pow z hz) hz ?_
      funext j
      by_cases hj : j = b
      · subst hj
        simp [sact_apply, tw]
      · simp [sact_apply, tw, hj]
    calc (sg10 1 (fun j => decide (j = b)) * sg10 σ (fun _ => false))⁻¹ * tor10 hpq z hz *
          (sg10 1 (fun j => decide (j = b)) * sg10 σ (fun _ => false))
        = (sg10 σ (fun _ => false))⁻¹ * ((sg10 1 (fun j => decide (j = b)))⁻¹ *
            tor10 hpq z hz * sg10 1 (fun j => decide (j = b))) * sg10 σ (fun _ => false) := by
          group
      _ = _ := by rw [h1, conj_tor10_perm hpq σ (htw_pow z hz)]
  refine noncomm_via_block (m := sg10 1 (fun j => decide (j = b)) * sg10 σ (fun _ => false))
    (B₀ := dBlk K) ?_ ?_ ?_ hdN
  · intro s hs bb hb
    obtain ⟨z, hz, rfl, hzab⟩ := hS s hs
    rw [hconj z hz]
    refine (Subtype.ext (dBlk_comm_tor hb ?_)).symm
    simp only [tw, hσ0, hσ1]
    simp [hab, hzab]
  · rw [hconj xc hxc]
    refine hdM _ _ ?_ ?_
    · simp only [tw, hσ2b, ite_false]
      exact hxc1 _ hσ2a hσ2b
    · simp only [tw, hσ0, hσ1]
      simp [hab, hxcab]
  · exact fun h => hc1 (eq_one_of_conj_eq_one h)

theorem noncommOK_T10_of_base (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1)
    (hsN : ∀ l ∈ sBlk K, l ≠ 1 → ∃ y ∈ sBlk K, ¬ Commute l (y * l * y⁻¹))
    (hdN : ∀ l ∈ dBlk K, l ≠ 1 → ∃ y ∈ dBlk K, ¬ Commute l (y * l * y⁻¹))
    (hsM : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ k, x k ^ p = 1), x 1 = 1 → x 2 = 1 →
      tor10 hpq x hx ∈ sBlk K)
    (hdM : ∀ (x : Fin 3 → (Qext K)ˣ) (hx : ∀ k, x k ^ p = 1), x 2 = 1 → x 0 * x 1 = 1 →
      tor10 hpq x hx ∈ dBlk K) :
    NoncommOK p ((emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K)) := by
  classical
  have hp2 : p ≠ 2 := by omega
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  obtain ⟨ζ, hζ⟩ := exists_unit_primitiveRoot hp hp2 hpq
  intro g hgN S hST hSidx hgS hgT hginv hcyc c hcT hcS hcinv
  have hmemT := fun y : ↥(M10 K) => (isTor_iff_mem (K := K) hp hp2 y).symm
  have hg1 : ∀ x, IsTor p x → IsTor p (g * x * g⁻¹) := fun x hx =>
    (hmemT _).1 ((Subgroup.mem_normalizer_iff.1 hgN x).1 ((hmemT x).2 hx))
  obtain ⟨π, ε, hπε⟩ := exists_sgn hp hp2 hpq hg1
  have hinvA : ∀ x : Fin 3 → (Qext K)ˣ, (∀ k, x k ^ p = 1) →
      sact π ε (sact π ε x) = x := by
    intro x hx
    have h1 := hginv (tor10 hpq x hx) ((hmemT _).2 (tor10_isTor hpq x hx))
    rw [hπε x hx, hπε (sact π ε x) (sact_pow hx)] at h1
    exact tor10_injective hpq h1
  have hneA : ∃ x : Fin 3 → (Qext K)ˣ, (∀ k, x k ^ p = 1) ∧ sact π ε x ≠ x := by
    obtain ⟨y, hyT, hy⟩ := hgT
    obtain ⟨a, ha, rfl⟩ := exists_tor10_of_isTor hpq ((hmemT y).1 hyT)
    refine ⟨a, ha, fun h => hy ?_⟩
    rw [hπε a ha]
    exact tor10_congr hpq h
  have hpropA : ∀ x x' : Fin 3 → (Qext K)ˣ, (∀ k, x k ^ p = 1) → (∀ k, x' k ^ p = 1) →
      phiv π ε x ≠ 1 → ∃ k : ℕ, phiv π ε x' = (phiv π ε x) ^ k := by
    intro x x' hx hx' hne
    have hmv : ∀ (z : Fin 3 → (Qext K)ˣ) (hz : ∀ k, z k ^ p = 1),
        g * tor10 hpq z hz * g⁻¹ * (tor10 hpq z hz)⁻¹ = tor10 hpq (phiv π ε z) (phiv_pow hz) := by
      intro z hz
      rw [hπε z hz, tor10_inv, tor10_mul]
      rfl
    have hne' : g * tor10 hpq x hx * g⁻¹ * (tor10 hpq x hx)⁻¹ ≠ 1 := by
      rw [hmv x hx]
      intro h
      exact hne (tor10_injective hpq (h.trans (tor10_one hpq).symm))
    obtain ⟨k, hk⟩ := hcyc _ ((hmemT _).2 (tor10_isTor hpq x hx)) _
      ((hmemT _).2 (tor10_isTor hpq x' hx')) hne'
    rw [hmv x' hx', hmv x hx, tor10_npow] at hk
    exact ⟨k, tor10_injective hpq hk⟩
  have hshape : ReflShape π ε := classify hζ hp5 hinvA hneA hpropA
  obtain ⟨xc, hxc, hcxc, hxcs⟩ := r10_inv hpq hπε ((hmemT c).1 hcT) hcinv
  have hSdata : ∀ s ∈ S, ∃ (a : Fin 3 → (Qext K)ˣ) (ha : ∀ k, a k ^ p = 1),
      s = tor10 hpq a ha ∧ sact π ε a = a := fun s hs =>
    r10_fixed hpq hπε ((hmemT s).1 (hST hs)) (hgS s hs)
  subst hcxc
  have hc1 : tor10 hpq xc hxc ≠ 1 := fun h => hcS (h ▸ S.one_mem)
  rcases shape_cases π ε hshape with ⟨i, rfl, rfl⟩ | ⟨a, b, hab, rfl, rfl⟩ |
    ⟨a, b, hab, rfl, rfl⟩
  ·
    refine r10_fam1 hpq hsN hsM i ?_ hxc ?_ hc1
    · intro s hs
      obtain ⟨a, ha, hsa, hfix⟩ := hSdata s hs
      refine ⟨a, ha, hsa, ?_⟩
      have h1 := congrFun hfix i
      simp [sact_apply] at h1
      exact eq_one_of_inv_eq hpodd (ha i) h1
    · intro j hj
      have h1 := congrFun hxcs j
      simp [sact_apply, hj] at h1
      exact eq_one_of_inv_eq hpodd (hxc j) h1.symm
  ·
    refine r10_fam2 hpq hdN hdM hab ?_ hxc ?_ ?_ hc1
    · intro s hs
      obtain ⟨z, hz, hsz, hfix⟩ := hSdata s hs
      refine ⟨z, hz, hsz, ?_⟩
      have h1 := congrFun hfix a
      simpa [sact_apply] using h1
    · have h1 := congrFun hxcs a
      simpa [sact_apply] using h1
    · intro j hja hjb
      have hsw : (Equiv.swap a b) j = j := Equiv.swap_apply_of_ne_of_ne hja hjb
      have h1 := congrFun hxcs j
      simp [sact_apply, hsw] at h1
      exact eq_one_of_inv_eq hpodd (hxc j) h1.symm
  ·
    refine r10_fam3 hpq hdN hdM hab ?_ hxc ?_ ?_ hc1
    · intro s hs
      obtain ⟨z, hz, hsz, hfix⟩ := hSdata s hs
      refine ⟨z, hz, hsz, ?_⟩
      have h1 := congrFun hfix a
      simpa [sact_apply] using h1
    · have h1 := congrFun hxcs a
      simp [sact_apply] at h1
      exact h1.symm
    · intro j hja hjb
      have hsw : (Equiv.swap a b) j = j := Equiv.swap_apply_of_ne_of_ne hja hjb
      have h1 := congrFun hxcs j
      simp [sact_apply, hsw, hja, hjb] at h1
      exact eq_one_of_inv_eq hpodd (hxc j) h1.symm

theorem noncommOK_T10 (hp : p.Prime) (hp5 : 5 ≤ p) (hpq : p ∣ Nat.card K + 1) :
    NoncommOK p ((emb10 : torusVec p 4 (Qext K) →*
      (QV K (Fin 3) ≃ₗ[K] QV K (Fin 3))).range.subgroupOf (M10 K)) := by
  have hK4 : 4 ≤ Nat.card K := by
    have := Nat.le_of_dvd (Nat.succ_pos _) hpq
    omega
  exact noncommOK_T10_of_base hp hp5 hpq (fun _ hl hl1 => sBlk_noncomm hK4 hl hl1)
    (fun _ hl hl1 => dBlk_noncomm hK4 hl hl1) (fun _ hx h1 h2 => tor10_mem_sBlk hpq hx h1 h2)
    (fun _ hx h2 h01 => tor10_mem_dBlk hpq hx h2 h01)

end Model

end CFSG.RankThree.PartOne.Q1327Z
