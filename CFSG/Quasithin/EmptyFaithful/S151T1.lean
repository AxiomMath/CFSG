module

public import CFSG.Quasithin.EmptyFaithful.S151T0

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped Pointwise commutatorElement

variable {G : Type} [Group G]

theorem s151t_conjSub_commutator (g : G) (A B : Subgroup G) :
    B6.conjSub g ⁅A, B⁆ = ⁅B6.conjSub g A, B6.conjSub g B⁆ :=
  Subgroup.map_commutator A B (MulAut.conj g).toMonoidHom

theorem s151t_conjSub_perf {g : G} {A : Subgroup G} (h : ⁅A, A⁆ = A) :
    ⁅B6.conjSub g A, B6.conjSub g A⁆ = B6.conjSub g A := by
  rw [← s151t_conjSub_commutator, h]

theorem s151t_mem_normalizer_of_conjSub {g : G} {X : Subgroup G} (h : B6.conjSub g X = X) :
    g ∈ Subgroup.normalizer (X : Set G) := A38.map_conj_eq_iff.mp h

theorem s151t_conjSub_sup (g : G) (A B : Subgroup G) :
    B6.conjSub g (A ⊔ B) = B6.conjSub g A ⊔ B6.conjSub g B :=
  (B6.conjSub g).map_sup A B

theorem s151t_mem_normalizer_sup {g : G} {A B : Subgroup G} (hA : g ∈ Subgroup.normalizer (A : Set G))
    (hB : g ∈ Subgroup.normalizer (B : Set G)) : g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  apply s151t_mem_normalizer_of_conjSub
  rw [s151t_conjSub_sup, B6.conjSub_eq_self hA, B6.conjSub_eq_self hB]

theorem s151t_isPGroup_sup_of_commute {A B : Subgroup G} (hA : IsPGroup 2 ↥A) (hB : IsPGroup 2 ↥B)
    (hc : B ≤ Subgroup.centralizer (A : Set G)) : IsPGroup 2 ↥(A ⊔ B) := by
  rintro ⟨x, hx⟩
  obtain ⟨a, ha, b, hb, rfl⟩ := zb_mem_sup (P := A) (S := B) (hc.trans (Subgroup.centralizer_le_normalizer _)) hx
  obtain ⟨i, hi⟩ := hA ⟨a, ha⟩
  obtain ⟨j, hj⟩ := hB ⟨b, hb⟩
  have ha' : a ^ 2 ^ i = 1 := by simpa using congrArg Subtype.val hi
  have hb' : b ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
  have hcom : Commute a b := (Subgroup.mem_centralizer_iff.mp (hc hb) a ha)
  refine ⟨i + j, Subtype.ext ?_⟩
  show (a * b) ^ 2 ^ (i + j) = 1
  rw [hcom.mul_pow, pow_add, pow_mul, ha', one_pow, mul_comm (2 ^ i), pow_mul, hb', one_pow, one_mul]

structure WreathCfg (L P S : Subgroup G) (s : G) : Prop where
  s2 : IsPGroup 2 ↥S
  hs : s ∈ S
  hsN : s ∉ Subgroup.normalizer (L : Set G)
  hSH : ∀ x ∈ S, x ∈ Subgroup.normalizer (L : Set G) ∨ s⁻¹ * x ∈ Subgroup.normalizer (L : Set G)
  blk : IsLnBlock L 3
  perf : ⁅L, L⁆ = L
  nLL' : L ≤ Subgroup.normalizer ((B6.conjSub s L : Subgroup G) : Set G)
  nL'L : B6.conjSub s L ≤ Subgroup.normalizer (L : Set G)
  comm : ⁅L, B6.conjSub s L⁆ ≤ pCoreOf 2 L
  par : Par2 L (S ⊓ Subgroup.normalizer (L : Set G)) P
  big : ParBig L P

namespace WreathCfg

variable {L P S : Subgroup G} {s : G} (c : WreathCfg L P S s)
include c

theorem commLL' [Finite G] : ⁅L, B6.conjSub s L⁆ = ⊥ :=
  s151t_blocks_commute c.blk c.perf (s151t_conjSub_perf c.perf) c.nLL' c.nL'L c.comm

theorem sq_mem : s * s ∈ S ⊓ Subgroup.normalizer (L : Set G) := by
  refine ⟨S.mul_mem c.hs c.hs, ?_⟩
  rcases c.hSH (s * s) (S.mul_mem c.hs c.hs) with h | h
  · exact h
  · exact absurd (by simpa using h) c.hsN

theorem conj_mem {h : G} (hh : h ∈ S ⊓ Subgroup.normalizer (L : Set G)) :
    s⁻¹ * h * s ∈ S ⊓ Subgroup.normalizer (L : Set G) := by
  have hhs : h * s ∈ S := S.mul_mem hh.1 c.hs
  refine ⟨S.mul_mem (S.mul_mem (S.inv_mem c.hs) hh.1) c.hs, ?_⟩
  rcases c.hSH (h * s) hhs with h1 | h1
  · exfalso
    apply c.hsN
    have := Subgroup.mul_mem _ (Subgroup.inv_mem _ hh.2) h1
    simpa using this
  · simpa [mul_assoc] using h1

theorem SH_normalizes_conj {A : Subgroup G}
    (hA : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (A : Set G)) :
    S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer ((B6.conjSub s A : Subgroup G) : Set G) := by
  intro h hh
  apply s151t_mem_normalizer_of_conjSub
  have hk := c.conj_mem hh
  have e : h * s = s * (s⁻¹ * h * s) := by group
  have h1 : B6.conjSub h (B6.conjSub s A) = B6.conjSub (h * s) A := (B6.conjSub_mul h s A).symm
  have h2 : B6.conjSub (h * s) A = B6.conjSub s A := by
    rw [e, B6.conjSub_mul, B6.conjSub_eq_self (hA hk)]
  rw [h1, h2]

theorem conjSub_sq {A : Subgroup G}
    (hA : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (A : Set G)) :
    B6.conjSub s (B6.conjSub s A) = A := by
  rw [← B6.conjSub_mul]
  exact B6.conjSub_eq_self (hA c.sq_mem)

theorem commPP' [Finite G] : ⁅P, B6.conjSub s P⁆ = ⊥ := by
  rw [eq_bot_iff, ← c.commLL']
  exact Subgroup.commutator_mono c.par.le ((B6.conjSub s).le_iff_le.mpr c.par.le)

theorem P'_le_centralizer [Finite G] : B6.conjSub s P ≤ Subgroup.centralizer (P : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact c.commPP'

theorem PP'_inf_le [Finite G] : P ⊓ B6.conjSub s P ≤ pCoreOf 2 L := by
  intro x hx
  have hxL : x ∈ L := c.par.le hx.1
  have hxL' : x ∈ B6.conjSub s L := (B6.conjSub s).le_iff_le.mpr c.par.le hx.2
  have hcent : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : ⁅l, x⁆ ∈ ⁅L, B6.conjSub s L⁆ := Subgroup.commutator_mem_commutator hl hxL'
    rw [c.commLL'] at h1
    exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp h1)
  exact (c.blk.1.2.1) ⟨hxL, Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr
    (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hcent⟩

theorem L'_le_centralizer [Finite G] : B6.conjSub s L ≤ Subgroup.centralizer (L : Set G) := by
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact c.commLL'

theorem L_le_centralizer' [Finite G] : L ≤ Subgroup.centralizer ((B6.conjSub s L : Subgroup G) : Set G) :=
  Subgroup.commutator_eq_bot_iff_le_centralizer.mp c.commLL'

theorem S_le_normalizer_sup {A : Subgroup G}
    (hA : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (A : Set G)) :
    S ≤ Subgroup.normalizer ((A ⊔ B6.conjSub s A : Subgroup G) : Set G) := by
  have hA' := c.SH_normalizes_conj hA
  have hSH : S ⊓ Subgroup.normalizer (L : Set G) ≤
      Subgroup.normalizer ((A ⊔ B6.conjSub s A : Subgroup G) : Set G) := fun h hh =>
    s151t_mem_normalizer_sup (hA hh) (hA' hh)
  have hs : s ∈ Subgroup.normalizer ((A ⊔ B6.conjSub s A : Subgroup G) : Set G) := by
    apply s151t_mem_normalizer_of_conjSub
    rw [s151t_conjSub_sup, c.conjSub_sq hA, sup_comm]
  intro x hx
  rcases c.hSH x hx with h | h
  · exact hSH ⟨hx, h⟩
  · have hk : s⁻¹ * x ∈ S ⊓ Subgroup.normalizer (L : Set G) := ⟨S.mul_mem (S.inv_mem c.hs) hx, h⟩
    have e : x = s * (s⁻¹ * x) := by group
    rw [e]
    exact Subgroup.mul_mem _ hs (hSH hk)

theorem S_le_normalizer_N : S ≤ Subgroup.normalizer ((P ⊔ B6.conjSub s P : Subgroup G) : Set G) :=
  c.S_le_normalizer_sup c.par.sP

theorem N_le_normalizer_P [Finite G] :
    P ⊔ B6.conjSub s P ≤ Subgroup.normalizer (P : Set G) :=
  sup_le Subgroup.le_normalizer (c.P'_le_centralizer.trans (Subgroup.centralizer_le_normalizer _))

theorem mem_N [Finite G] {x : G} (hx : x ∈ P ⊔ B6.conjSub s P) :
    ∃ p ∈ P, ∃ p' ∈ B6.conjSub s P, x = p * p' :=
  zb_mem_sup (c.P'_le_centralizer.trans (Subgroup.centralizer_le_normalizer _)) hx

theorem H_eq : P ⊔ S = (P ⊔ B6.conjSub s P) ⊔ S := by
  apply le_antisymm
  · exact sup_le_sup_right le_sup_left _
  · refine sup_le (sup_le le_sup_left ?_) le_sup_right
    intro x hx
    rw [B6.mem_conjSub] at hx
    have e : x = s * (s⁻¹ * x * s) * s⁻¹ := by group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_right c.hs)
      (Subgroup.mem_sup_left hx)) (Subgroup.inv_mem _ (Subgroup.mem_sup_right c.hs))

theorem mem_H {x : G} (hx : x ∈ P ⊔ S) : ∃ n ∈ P ⊔ B6.conjSub s P, ∃ t ∈ S, x = n * t := by
  rw [c.H_eq] at hx
  exact zb_mem_sup c.S_le_normalizer_N hx

theorem two_pow : ∀ x ∈ P ⊔ S, ∃ k : ℕ, x ^ 2 ^ k ∈ P ⊔ B6.conjSub s P := by
  intro x hx
  obtain ⟨n, hn, t, ht, rfl⟩ := c.mem_H hx
  obtain ⟨k, hk⟩ := c.s2 ⟨t, ht⟩
  refine ⟨k, ?_⟩
  obtain ⟨q, hq, hqe⟩ := zb_mul_pow_mem (c.S_le_normalizer_N ht) hn (2 ^ k)
  have htk : t ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  rw [hqe, htk, mul_one]
  exact hq

theorem charTwo [Finite G] : CharTwo (P ⊔ S) := by
  set H : Subgroup G := P ⊔ S with hHdef
  set R : Subgroup G := pCoreOf 2 L with hRdef
  set R' : Subgroup G := B6.conjSub s R with hR'def
  have hRp : IsPGroup 2 ↥R := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L
  have hR'p : IsPGroup 2 ↥R' := by
    rintro ⟨x, hx⟩
    have hx' : s⁻¹ * x * s ∈ R := B6.mem_conjSub.mp hx
    obtain ⟨k, hk⟩ := hRp ⟨s⁻¹ * x * s, hx'⟩
    refine ⟨k, Subtype.ext ?_⟩
    have h1 : (s⁻¹ * x * s) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    show x ^ 2 ^ k = 1
    calc x ^ 2 ^ k = (s * (s⁻¹ * x * s) * s⁻¹) ^ 2 ^ k := by congr 1; group
      _ = s * (s⁻¹ * x * s) ^ 2 ^ k * s⁻¹ := conj_pow
      _ = 1 := by rw [h1]; group
  have hRL : R ≤ L := CFSG.LieType.BorelTits.pCoreOf_le 2 L
  have hR'L' : R' ≤ B6.conjSub s L := (B6.conjSub s).le_iff_le.mpr hRL
  have hP'L' : B6.conjSub s P ≤ B6.conjSub s L := (B6.conjSub s).le_iff_le.mpr c.par.le
  have hR'C : R' ≤ Subgroup.centralizer (R : Set G) :=
    (hR'L'.trans c.L'_le_centralizer).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRL))
  have hP'CR : B6.conjSub s P ≤ Subgroup.centralizer (R : Set G) :=
    (hP'L'.trans c.L'_le_centralizer).trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRL))
  have hPCL' : P ≤ Subgroup.centralizer ((B6.conjSub s L : Subgroup G) : Set G) :=
    c.par.le.trans c.L_le_centralizer'
  have hPCR' : P ≤ Subgroup.centralizer (R' : Set G) :=
    hPCL'.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hR'L'))
  have hRP : R ≤ P := (c.par.syl.pCoreOf_le).trans c.par.sl
  have hNH : P ⊔ B6.conjSub s P ≤ H := by
    calc P ⊔ B6.conjSub s P ≤ (P ⊔ B6.conjSub s P) ⊔ S := le_sup_left
      _ = H := c.H_eq.symm
  have hR'P' : R' ≤ B6.conjSub s P := (B6.conjSub s).le_iff_le.mpr hRP
  have hQp : IsPGroup 2 ↥(R ⊔ R') :=
    s151t_isPGroup_sup_of_commute hRp hR'p hR'C
  have hQH : R ⊔ R' ≤ H := sup_le (hRP.trans (le_sup_left.trans (le_refl _))) (hR'P'.trans (le_sup_right.trans hNH))
  have hSHR : S ⊓ Subgroup.normalizer (L : Set G) ≤ Subgroup.normalizer (R : Set G) := fun h hh =>
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 L hh.2
  have hHN : H ≤ Subgroup.normalizer ((R ⊔ R' : Subgroup G) : Set G) := by
    refine sup_le ?_ (c.S_le_normalizer_sup hSHR)
    intro p hp
    exact s151t_mem_normalizer_sup
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L (c.par.le hp))
      ((hPCR' hp |> Subgroup.centralizer_le_normalizer _))
  have hQO : R ⊔ R' ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hQH hHN hQp
  set C : Subgroup G := H ⊓ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) with hCdef
  have hCp : IsPGroup 2 ↥C := by
    rintro ⟨x, hx⟩
    obtain ⟨k, hk⟩ := c.two_pow x hx.1
    have hnC : x ^ 2 ^ k ∈ Subgroup.centralizer ((R ⊔ R' : Subgroup G) : Set G) :=
      Subgroup.pow_mem _ hx.2 _
    obtain ⟨p, hp, p', hp', hpp'⟩ := c.mem_N hk
    have hnR : ∀ q ∈ R ⊔ R', q * (x ^ 2 ^ k) = (x ^ 2 ^ k) * q := fun q hq =>
      Subgroup.mem_centralizer_iff.mp hnC q hq
    have hp'R : ∀ r ∈ R, r * p' = p' * r := fun r hr =>
      Subgroup.mem_centralizer_iff.mp (hP'CR hp') r hr
    have hpR' : ∀ r' ∈ R', r' * p = p * r' := fun r' hr' =>
      Subgroup.mem_centralizer_iff.mp (hPCR' hp) r' hr'
    have hpR : p ∈ R := by
      have hpC : p ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have h1 : r * (p * p') = (p * p') * r := by
          rw [← hpp']; exact hnR r (Subgroup.mem_sup_left hr)
        have h2 : r * p * p' = p * r * p' := by
          calc r * p * p' = r * (p * p') := by group
            _ = (p * p') * r := h1
            _ = p * (p' * r) := by group
            _ = p * (r * p') := by rw [hp'R r hr]
            _ = p * r * p' := by group
        exact mul_right_cancel h2
      exact c.blk.1.2.1 ⟨c.par.le hp, hpC⟩
    have hp'R' : p' ∈ R' := by
      have hp'C : p' ∈ Subgroup.centralizer (R' : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r' hr'
        have h1 : r' * (p * p') = (p * p') * r' := by
          rw [← hpp']; exact hnR r' (Subgroup.mem_sup_right hr')
        have h2 : p * (r' * p') = p * (p' * r') := by
          calc p * (r' * p') = r' * p * p' := by rw [hpR' r' hr']; group
            _ = r' * (p * p') := by group
            _ = (p * p') * r' := h1
            _ = p * (p' * r') := by group
        exact mul_left_cancel h2
      have hp'L : s⁻¹ * p' * s ∈ P := B6.mem_conjSub.mp hp'
      have hconj : s⁻¹ * p' * s ∈ Subgroup.centralizer (R : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hrR' : s * r * s⁻¹ ∈ R' := by
          rw [B6.mem_conjSub]
          have e : s⁻¹ * (s * r * s⁻¹) * s = r := by group
          rw [e]
          exact hr
        have := Subgroup.mem_centralizer_iff.mp hp'C _ hrR'
        calc r * (s⁻¹ * p' * s) = s⁻¹ * ((s * r * s⁻¹) * p') * s := by group
          _ = s⁻¹ * (p' * (s * r * s⁻¹)) * s := by rw [this]
          _ = (s⁻¹ * p' * s) * r := by group
      have : s⁻¹ * p' * s ∈ R := c.blk.1.2.1 ⟨c.par.le hp'L, hconj⟩
      exact B6.mem_conjSub.mpr this
    have hnQ : x ^ 2 ^ k ∈ R ⊔ R' := by
      rw [hpp']
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hpR) (Subgroup.mem_sup_right hp'R')
    obtain ⟨j, hj⟩ := hQp ⟨x ^ 2 ^ k, hnQ⟩
    have hj' : (x ^ 2 ^ k) ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    refine ⟨k + j, Subtype.ext ?_⟩
    show x ^ 2 ^ (k + j) = 1
    rw [pow_add, pow_mul]
    exact hj'
  have hHC : H ≤ Subgroup.normalizer (C : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have key : ∀ g ∈ H, ∀ c' ∈ C, g * c' * g⁻¹ ∈ C := by
      intro g hg c' hc'
      refine ⟨H.mul_mem (H.mul_mem hg hc'.1) (H.inv_mem hg), Subgroup.mem_centralizer_iff.mpr ?_⟩
      intro r hr
      have hr' : g⁻¹ * r * g ∈ R ⊔ R' := by
        have := (Subgroup.mem_normalizer_iff.mp (hHN (H.inv_mem hg)) r).mp hr
        simpa using this
      have hcomm := Subgroup.mem_centralizer_iff.mp hc'.2 _ hr'
      calc r * (g * c' * g⁻¹) = g * ((g⁻¹ * r * g) * c') * g⁻¹ := by group
        _ = g * (c' * (g⁻¹ * r * g)) * g⁻¹ := by rw [hcomm]
        _ = g * c' * g⁻¹ * r := by group
    intro x
    constructor
    · exact key g hg x
    · intro hx
      have := key g⁻¹ (H.inv_mem hg) _ hx
      simpa [mul_assoc] using this
  have hCO : C ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hHC hCp
  intro x hx
  exact hCO ⟨hx.1, Subgroup.centralizer_le hQO hx.2⟩

end WreathCfg

end CFSG.Quasithin
