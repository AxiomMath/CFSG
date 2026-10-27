module

public import CFSG.RankThree.PartOne.SP4C.Frat

public section

namespace CFSG.RankThree.PartOne.SP4C

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
open CFSG.RankThree.PartOne.KFU

variable {G : Type} [Group G]

theorem inv_heart {p : ℕ} (hpodd : Odd p) {c g : G} {S : Subgroup G} (hcp : c ^ p = 1)
    (hginv : g * c * g⁻¹ = c⁻¹) (hgS : g ∈ Subgroup.normalizer (S : Set G))
    (hcS : c ∈ Subgroup.normalizer (S : Set G)) (hk : ∃ k : ℤ, ∀ s ∈ S, c * s * c⁻¹ = s ^ k) :
    ∀ s ∈ S, c * s * c⁻¹ = s := by
  obtain ⟨k, hk⟩ := hk
  have hg' : g⁻¹ ∈ Subgroup.normalizer (S : Set G) := (Subgroup.normalizer (S : Set G)).inv_mem hgS
  have h1 : ∀ s ∈ S, c⁻¹ * s * c = s ^ k := by
    intro s hs
    have hs' : g⁻¹ * s * g ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 hg' s).1 hs
      simpa [mul_assoc] using this
    have hc : c = g * c⁻¹ * g⁻¹ := by
      have : c⁻¹ = g * c * g⁻¹ := hginv.symm
      calc c = (c⁻¹)⁻¹ := (inv_inv c).symm
        _ = (g * c * g⁻¹)⁻¹ := by rw [this]
        _ = g * c⁻¹ * g⁻¹ := by group
    calc c⁻¹ * s * c = (g * c * g⁻¹) * s * (g * c⁻¹ * g⁻¹) := by rw [hginv, ← hc]
      _ = g * (c * (g⁻¹ * s * g) * c⁻¹) * g⁻¹ := by group
      _ = g * (g⁻¹ * s * g) ^ k * g⁻¹ := by rw [hk _ hs']
      _ = (g * (g⁻¹ * s * g) * g⁻¹) ^ k := by rw [conj_zpow]
      _ = s ^ k := by group
  have h2 : ∀ s ∈ S, (c * c) * s * (c * c)⁻¹ = s := by
    intro s hs
    have hcs : c * s * c⁻¹ ∈ S := by
      have := (Subgroup.mem_normalizer_iff.1 hcS s).1 hs
      exact this
    calc (c * c) * s * (c * c)⁻¹ = c * (c * s * c⁻¹) * c⁻¹ := by group
      _ = c * s ^ k * c⁻¹ := by rw [hk s hs]
      _ = (c * s * c⁻¹) ^ k := by rw [conj_zpow]
      _ = (s ^ k) ^ k := by rw [hk s hs]
      _ = s ^ (k * k) := by rw [← zpow_mul]
      _ = s := by
        have e : s = c * (c⁻¹ * s * c) * c⁻¹ := by group
        have e2 : c * (c⁻¹ * s * c) * c⁻¹ = s ^ (k * k) := by
          rw [h1 s hs, ← conj_zpow, hk s hs, ← zpow_mul]
        exact (e.trans e2).symm
  intro s hs
  have hc2 : (c * c) ^ ((p + 1) / 2) = c := by
    have hp1 : 2 * ((p + 1) / 2) = p + 1 := by
      obtain ⟨t, ht⟩ := hpodd
      omega
    rw [← pow_two, ← pow_mul, hp1, pow_succ, hcp, one_mul]
  have hc2' : Commute (c * c) s := by
    show c * c * s = s * (c * c)
    exact mul_inv_eq_iff_eq_mul.1 (h2 s hs)
  have hcs : Commute ((c * c) ^ ((p + 1) / 2)) s := hc2'.pow_left _
  rw [hc2] at hcs
  exact mul_inv_eq_iff_eq_mul.2 hcs.eq

theorem exists_swap_two_element [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
    (ctx : Fus12Ctx G p A c L E) {b : G} {K I X P Q : Subgroup G}
    (hL : Layer1212 p A c L E b K I) (hC : Choice1212 p E b I X P Q)
    (hF : Field1213 p A c L b K I) (hout : Out1214 p c L E I P Q)
    {g : G} (hg : g ∈ cNormalizer c) (hginv : g * c * g⁻¹ = c⁻¹) :
    ∃ n : G, n ∈ torusNormalizer E ∧ n * c * n⁻¹ = c⁻¹ ∧ (∃ a : ℕ, n ^ (2 ^ a) = 1) ∧
      ¬ ∃ h ∈ L, h ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ∧
        ∃ k : ℤ, ∀ f ∈ E ⊓ L, n * f * n⁻¹ = h * f ^ k * h⁻¹ := by
  classical
  have h := ctx.hyp
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hAel := h.A_elem
  have hcA : c ∈ A := h.c_mem
  have hcp : c ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c hcA
  have hcord : orderOf c = p := orderOf_eq_prime hcp h.c_ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G) := by
    obtain ⟨L', -, hL'⟩ := h.L_mem.2
    rw [← hL']
    exact Subgroup.map_subtype_le _
  have hLH : L ≤ cNormalizer c := fun l hl =>
    mem_cNormalizer_of_commute (Subgroup.mem_centralizer_singleton_iff.1 (hLc hl))
  have hcne : c ≠ c⁻¹ := by
    intro hc
    have h2 : c ^ 2 = 1 := by
      calc c ^ 2 = c * c := pow_two c
        _ = c * c⁻¹ := by rw [← hc]
        _ = 1 := mul_inv_cancel c
    have := orderOf_dvd_of_pow_eq_one h2
    rw [hcord] at this
    have h2p : p ≤ 2 := Nat.le_of_dvd (by norm_num) this
    have h5 := Sec12Three.five_le ctx.hyp
    omega
  obtain ⟨x, hx, n, hn, hgxn⟩ := frat_core ctx hout g hg
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.1 hx
  have hnc : n * c * n⁻¹ = c⁻¹ := by
    have h1 : g * c * g⁻¹ = x * (n * c * n⁻¹) * x⁻¹ := by rw [hgxn]; group
    have h2 : n * c * n⁻¹ = x⁻¹ * (g * c * g⁻¹) * x := by rw [h1]; group
    rw [h2, hginv]
    have h3 : x⁻¹ * c⁻¹ * x = c⁻¹ := by
      have := (Commute.inv_right (show Commute x c from hxc)).eq
      calc x⁻¹ * c⁻¹ * x = x⁻¹ * (c⁻¹ * x) := by group
        _ = x⁻¹ * (x * c⁻¹) := by rw [this]
        _ = c⁻¹ := by group
    exact h3
  have hord0 : orderOf n ≠ 0 := (orderOf_pos n).ne'
  obtain ⟨a, m, hmodd, hom⟩ := Nat.exists_eq_two_pow_mul_odd hord0
  have hn2c : n ^ 2 * c * (n ^ 2)⁻¹ = c := by
    calc n ^ 2 * c * (n ^ 2)⁻¹ = n * (n * c * n⁻¹) * n⁻¹ := by rw [pow_two]; group
      _ = n * c⁻¹ * n⁻¹ := by rw [hnc]
      _ = (n * c * n⁻¹)⁻¹ := by group
      _ = c := by rw [hnc, inv_inv]
  have hnmc : (n ^ m) * c * (n ^ m)⁻¹ = c⁻¹ := by
    obtain ⟨t, ht⟩ := hmodd
    have e : n ^ m = (n ^ 2) ^ t * n := by rw [ht, pow_succ, pow_mul]
    have hcn2 : Commute (n ^ 2) c := by
      show n ^ 2 * c = c * n ^ 2
      exact mul_inv_eq_iff_eq_mul.1 hn2c
    have hcd : Commute ((n ^ 2) ^ t) c := hcn2.pow_left t
    rw [e]
    generalize (n ^ 2) ^ t = d at hcd ⊢
    calc d * n * c * (d * n)⁻¹ = d * (n * c * n⁻¹) * d⁻¹ := by group
      _ = d * c⁻¹ * d⁻¹ := by rw [hnc]
      _ = c⁻¹ := by
        have := (Commute.inv_right hcd).eq
        calc d * c⁻¹ * d⁻¹ = c⁻¹ * d * d⁻¹ := by rw [this]
          _ = c⁻¹ := by group
  have hnW : n ∈ torusNormalizer E := hn.2
  have hn₂W : n ^ m ∈ torusNormalizer E := (torusNormalizer E).pow_mem hnW m
  have hn₂c : n ^ m ∈ cNormalizer c := (cNormalizer c).pow_mem hn.1 m
  refine ⟨n ^ m, hn₂W, hnmc, ⟨a, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hom]
    exact pow_orderOf_eq_one n
  · rintro ⟨l, hlL, hlF, k, hk⟩
    have hbE : b ∈ E ⊓ L := ⟨h.A_le_E hL.b_mem.1, hL.b_mem.2.1⟩
    have hlc : l * c = c * l := Subgroup.mem_centralizer_singleton_iff.1 (hLc hlL)
    have hmW : l⁻¹ * n ^ m ∈ torusNormalizer E :=
      (torusNormalizer E).mul_mem
        (ctx.mem_torusNormalizer (L.inv_mem hlL) ((Subgroup.normalizer _).inv_mem hlF)) hn₂W
    have hmb : l⁻¹ * n ^ m ∈ Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
      refine mem_normalizer_zpowers_of_conj_mem ?_
      have : l⁻¹ * n ^ m * b * (l⁻¹ * n ^ m)⁻¹ = b ^ k := by
        calc l⁻¹ * n ^ m * b * (l⁻¹ * n ^ m)⁻¹ = l⁻¹ * (n ^ m * b * (n ^ m)⁻¹) * l := by group
          _ = l⁻¹ * (l * b ^ k * l⁻¹) * l := by rw [hk b hbE]
          _ = b ^ k := by group
      rw [this]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers b) k
    have hmc : l⁻¹ * n ^ m ∈ cNormalizer c :=
      (cNormalizer c).mul_mem ((cNormalizer c).inv_mem (hLH hlL)) hn₂c
    have hcen := n_centralizes ctx hL hC hF hmW hmb hmc
    apply hcne
    calc c = l⁻¹ * n ^ m * c * (l⁻¹ * n ^ m)⁻¹ := hcen.symm
      _ = l⁻¹ * (n ^ m * c * (n ^ m)⁻¹) * l := by group
      _ = l⁻¹ * c⁻¹ * l := by rw [hnmc]
      _ = c⁻¹ := by
        have := (Commute.inv_right (show Commute l c from hlc)).eq
        calc l⁻¹ * c⁻¹ * l = l⁻¹ * (c⁻¹ * l) := by group
          _ = l⁻¹ * (l * c⁻¹) := by rw [← this]
          _ = c⁻¹ := by group

@[expose] def KF1215Sp4InvCore : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → ∀ (b : G) (K I X P Q : Subgroup G),
      Layer1212 p A c L E b K I → Choice1212 p E b I X P Q → Field1213 p A c L b K I →
      Out1214 p c L E I P Q → IsSylowOf p P ⊤ → RowModel p L 7 →
      ∀ g : G, g ∈ torusNormalizer E → g * c * g⁻¹ = c⁻¹ → (∃ a : ℕ, g ^ (2 ^ a) = 1) →
        (¬ ∃ h ∈ L, h ∈ Subgroup.normalizer ((E ⊓ L : Subgroup G) : Set G) ∧
          ∃ k : ℤ, ∀ f ∈ E ⊓ L, g * f * g⁻¹ = h * f ^ k * h⁻¹) →
        ∃ S : Subgroup G, g ∈ Subgroup.normalizer (S : Set G) ∧
          c ∈ Subgroup.normalizer (S : Set G) ∧ (∃ k : ℤ, ∀ s ∈ S, c * s * c⁻¹ = s ^ k) ∧
          ∃ s ∈ S, c * s * c⁻¹ ≠ s

theorem kf1215Sp4Inv_of_core (hcore : KF1215Sp4InvCore) : KF1215Sp4Inv := by
  intro G _ _ p A c L E ctx b K I X P Q hL hC hF hout hsyl h7 g hg hginv
  obtain ⟨n, hnW, hnc, hn2, hswap⟩ := exists_swap_two_element ctx hL hC hF hout hg hginv
  obtain ⟨S, hnS, hcS, hk, s, hsS, hs⟩ :=
    hcore G p A c L E ctx b K I X P Q hL hC hF hout hsyl h7 n hnW hnc hn2 hswap
  have hp := ctx.hyp.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcA : c ∈ A := ctx.hyp.c_mem
  have hAel := ctx.hyp.A_elem
  have hcp : c ^ p = 1 := CFSG.elemPow_eq_one_of_isElementaryAbelian (p := p) (A := A) c hcA
  have hpodd : Odd p := hp.odd_of_ne_two (by have := Sec12Three.five_le ctx.hyp; omega)
  exact hs (inv_heart hpodd hcp hnc hnS hcS hk s hsS)

end CFSG.RankThree.PartOne.SP4C
