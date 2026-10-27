module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.CommZvSurj
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.ZvCentralizer
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S42B1Tri

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 Equiv S42B1

namespace S34

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem perm3_sixth : ∀ σ : Perm (Fin 3), σ ^ 6 = 1 := by decide

theorem perm3_odd_cube : ∀ σ : Perm (Fin 3), ∀ r : Fin 6, r.val % 2 = 1 → σ ^ r.val = 1 →
    σ ^ 3 = 1 := by decide

theorem perm3_cls : ∀ σ τ : Perm (Fin 3), τ ^ 3 = 1 → τ ≠ 1 → σ ^ 3 = 1 →
    σ = 1 ∨ σ = τ ∨ σ = τ ^ 2 := by decide

theorem perm3_mul_cube : ∀ σ τ : Perm (Fin 3), σ ^ 2 = 1 → τ ^ 2 = 1 → σ ≠ 1 → τ ≠ 1 →
    σ ≠ τ → (σ * τ) ^ 3 = 1 := by decide

theorem perm3_mul_ne : ∀ σ τ : Perm (Fin 3), σ ^ 2 = 1 → τ ^ 2 = 1 → σ ≠ 1 → τ ≠ 1 →
    σ ≠ τ → σ * τ ≠ 1 := by decide

theorem perm3_pow_three_of_odd {σ : Perm (Fin 3)} {m : ℕ} (hm : Odd m) (h : σ ^ m = 1) :
    σ ^ 3 = 1 := by
  have h6 : σ ^ m = σ ^ (m % 6) := by
    conv_lhs => rw [← Nat.div_add_mod m 6, pow_add, pow_mul, perm3_sixth, one_pow, one_mul]
  have hlt : m % 6 < 6 := Nat.mod_lt _ (by norm_num)
  have hodd : (m % 6) % 2 = 1 := by
    obtain ⟨k, rfl⟩ := hm
    omega
  exact perm3_odd_cube σ ⟨m % 6, hlt⟩ hodd (h6 ▸ h)

theorem mem_normalizer_of_conj_mem {Y : Subgroup G} {g : G} (h : ∀ y ∈ Y, g * y * g⁻¹ ∈ Y) :
    g ∈ Subgroup.normalizer (Y : Set G) :=
  Subgroup.mem_normalizer_fintype h

omit [Finite G] in
theorem conj_mem_sup_of {A B : Subgroup G} (g : G) (hA : ∀ a ∈ A, g * a * g⁻¹ ∈ A ⊔ B)
    (hB : ∀ b ∈ B, g * b * g⁻¹ ∈ A ⊔ B) : ∀ y ∈ A ⊔ B, g * y * g⁻¹ ∈ A ⊔ B := by
  have h : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom :=
    sup_le (fun a ha => hA a ha) (fun b hb => hB b hb)
  intro y hy
  exact h hy

theorem mem_normalizer_of_comm {Y : Subgroup G} {u : G} (h : ∀ y ∈ Y, u * y = y * u) :
    u ∈ Subgroup.normalizer (Y : Set G) := by
  refine mem_normalizer_of_conj_mem fun y hy => ?_
  rw [h y hy, mul_assoc, mul_inv_cancel, mul_one]
  exact hy

open EmptyFaithful.Stellmacher.OrdinaryProofs in
theorem rel3 (hA : F53Amalgam H M S) {μ δ : Geo H M} (hμ : vtype μ = true) (hδ : δ ∈ nbrs μ)
    (hz : Zv δ ≤ centerOf (stab δ)) {d : G} (hd : d ∈ stab μ) (hd1 : d ∉ Qv μ)
    (hd3 : d ^ 3 ∈ Qv μ) {z : G} (hzμ : z ∈ Zv μ) :
    z * (d * z * d⁻¹) * (d ^ 2 * z * (d ^ 2)⁻¹) = 1 := by
  obtain ⟨n, ψ, hn, -, hker⟩ := exists_quotHom hA μ
  have hn3 : n = 3 := by
    rcases hn with ⟨-, h⟩ | ⟨h, -⟩
    · rw [hμ] at h; exact absurd h (by simp)
    · exact h
  subst hn3
  have hcb : d ^ 2 * z * (d ^ 2)⁻¹ = d * (d * z * d⁻¹) * d⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]; group
  have hd3' : d ^ 3 * z * (d ^ 3)⁻¹ = d * (d * (d * z * d⁻¹) * d⁻¹) * d⁻¹ := by
    simp only [pow_succ, pow_zero, one_mul, mul_inv_rev]; group
  rw [hcb]
  have hdZ : ∀ x ∈ Zv μ, d * x * d⁻¹ ∈ Zv μ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA μ hd) x).mp hx
  generalize hb : d * z * d⁻¹ = b at hcb hd3' ⊢
  generalize hc : d * b * d⁻¹ = c at hcb hd3' ⊢
  have hbZ : b ∈ Zv μ := hb ▸ hdZ z hzμ
  have hcZ : c ∈ Zv μ := hc ▸ hdZ b hbZ
  have hQc : ∀ k ∈ Qv μ, ∀ x ∈ Zv μ, k * x = x * k := fun k hk x hx =>
    Subgroup.mem_centralizer_iff.mp (Zv_le_centerOf_Qv hA μ hx).2 k hk
  have hd3z : d ^ 3 * z = z * d ^ 3 := hQc _ hd3 z hzμ
  have hw : z * b * c ∈ Zv μ := mul_mem (mul_mem hzμ hbZ) hcZ
  have hdw : d * (z * b * c) = (z * b * c) * d := by
    have e1 : d * (z * b * c) * d⁻¹ = (d * z * d⁻¹) * (d * b * d⁻¹) * (d * c * d⁻¹) := by group
    have e4 : d * c * d⁻¹ = z := by
      rw [← hd3', hd3z]; group
    have e5 : (d * z * d⁻¹) * (d * b * d⁻¹) * (d * c * d⁻¹) = z * b * c := by
      rw [hb, hc, e4]
      calc b * c * z = z * (b * c) :=
            comm_Zv_comm hA μ _ (mul_mem hbZ hcZ) _ hzμ
        _ = z * b * c := by rw [mul_assoc]
    have : d * (z * b * c) * d⁻¹ = z * b * c := e1.trans e5
    calc d * (z * b * c) = d * (z * b * c) * d⁻¹ * d := by group
      _ = (z * b * c) * d := by rw [this]
  have hd2w : d ^ 2 * (z * b * c) = (z * b * c) * d ^ 2 := by
    rw [pow_two, mul_assoc, hdw, ← mul_assoc, hdw, mul_assoc]
  have hQw : ∀ k ∈ Qv μ, k * (z * b * c) = (z * b * c) * k := fun k hk => hQc k hk _ hw
  have hcent : z * b * c ∈ Subgroup.centralizer (oTwoRes (stab μ) : Set G) := by
    have hle : oTwoRes (stab μ) ≤ Subgroup.centralizer ({z * b * c} : Set G) := by
      unfold oTwoRes
      rw [Subgroup.closure_le]
      rintro x ⟨hx, m, hm, hxm⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro w hw'
      rw [Set.mem_singleton_iff] at hw'
      subst hw'
      have hσ : ψ ⟨x, hx⟩ ^ 3 = 1 := by
        refine perm3_pow_three_of_odd hm ?_
        rw [← map_pow]
        have : (⟨x, hx⟩ : ↥(stab μ)) ^ m = 1 := Subtype.ext hxm
        rw [this, map_one]
      have hτ3 : ψ ⟨d, hd⟩ ^ 3 = 1 := by
        rw [← map_pow]; exact (hker _).mpr hd3
      have hτ1 : ψ ⟨d, hd⟩ ≠ 1 := fun h => hd1 ((hker _).mp h)
      have hcomb : ∀ k ∈ Qv μ, ∀ e : G, e * (z * b * c) = (z * b * c) * e →
          (z * b * c) * (k * e) = (k * e) * (z * b * c) := by
        intro k hk e he
        calc (z * b * c) * (k * e) = ((z * b * c) * k) * e := (mul_assoc _ _ _).symm
          _ = (k * (z * b * c)) * e := by rw [hQw k hk]
          _ = k * ((z * b * c) * e) := mul_assoc _ _ _
          _ = k * (e * (z * b * c)) := by rw [he]
          _ = (k * e) * (z * b * c) := (mul_assoc _ _ _).symm
      rcases perm3_cls _ _ hτ3 hτ1 hσ with h | h | h
      · have hxQ : x ∈ Qv μ := (hker ⟨x, hx⟩).mp h
        exact (hQw x hxQ).symm
      · have hk : x * d⁻¹ ∈ Qv μ :=
          (hker (⟨x, hx⟩ * ⟨d, hd⟩⁻¹)).mp (by rw [map_mul, map_inv, h]; simp)
        have := hcomb _ hk d hdw
        rwa [show x * d⁻¹ * d = x by group] at this
      · have hk : x * (d ^ 2)⁻¹ ∈ Qv μ :=
          (hker (⟨x, hx⟩ * (⟨d, hd⟩ ^ 2)⁻¹)).mp (by rw [map_mul, map_inv, map_pow, h]; simp)
        have := hcomb _ hk (d ^ 2) hd2w
        rwa [show x * (d ^ 2)⁻¹ * d ^ 2 = x by group] at this
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (Subgroup.mem_centralizer_iff.mp (hle hh) (z * b * c) (Set.mem_singleton _)).symm
  have hbot := Zv_inf_centralizer_oTwoRes_eq_bot hA hδ hz
  have : z * b * c ∈ Zv μ ⊓ Subgroup.centralizer (oTwoRes (stab μ) : Set G) := ⟨hw, hcent⟩
  rw [hbot, Subgroup.mem_bot] at this
  exact this

theorem three_cycle (hA : F53Amalgam H M S) {μ : Geo H M} (hμ : vtype μ = true) {q s : G}
    (hq : q ∈ stab μ) (hs : s ∈ stab μ) (hq1 : q ∉ Qv μ) (hs1 : s ∉ Qv μ)
    (hq2 : q ^ 2 ∈ Qv μ) (hs2 : s ^ 2 ∈ Qv μ) (hqs : q * s⁻¹ ∉ Qv μ) :
    q * s ∉ Qv μ ∧ (q * s) ^ 3 ∈ Qv μ := by
  obtain ⟨n, ψ, hn, -, hker⟩ := exists_quotHom hA μ
  have hn3 : n = 3 := by
    rcases hn with ⟨-, h⟩ | ⟨h, -⟩
    · rw [hμ] at h; exact absurd h (by simp)
    · exact h
  subst hn3
  have h1 : ψ ⟨q, hq⟩ ≠ 1 := fun h => hq1 ((hker _).mp h)
  have h2 : ψ ⟨s, hs⟩ ≠ 1 := fun h => hs1 ((hker _).mp h)
  have h3 : ψ ⟨q, hq⟩ ^ 2 = 1 := by rw [← map_pow]; exact (hker _).mpr hq2
  have h4 : ψ ⟨s, hs⟩ ^ 2 = 1 := by rw [← map_pow]; exact (hker _).mpr hs2
  have h5 : ψ ⟨q, hq⟩ ≠ ψ ⟨s, hs⟩ := fun h =>
    hqs ((hker (⟨q, hq⟩ * ⟨s, hs⟩⁻¹)).mp (by rw [map_mul, map_inv, h]; simp))
  constructor
  · intro h
    have : ψ (⟨q, hq⟩ * ⟨s, hs⟩) = 1 := (hker _).mpr h
    rw [map_mul] at this
    exact perm3_mul_ne _ _ h3 h4 h1 h2 h5 this
  · have : ψ ((⟨q, hq⟩ * ⟨s, hs⟩) ^ 3) = 1 := by
      rw [map_pow, map_mul]; exact perm3_mul_cube _ _ h3 h4 h1 h2 h5
    exact (hker _).mp this

end S34

end F53.Stellmacher

end CFSG.Quasithin
