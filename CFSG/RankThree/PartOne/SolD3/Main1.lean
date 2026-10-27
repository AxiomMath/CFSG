module

public import CFSG.RankThree.PartOne.SolD3.Cfg
public import CFSG.RankThree.PartOne.SolD3.Small

public section

namespace CFSG.RankThree.PartOne.SolD3

open CFSG CFSG.Assembly CFSG.CGT.PushingUpLit.SolK CFSG.GH74
open CFSG.ComponentClassification.HSFLit
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem exists_sylow_pair {M P : Subgroup G} (hP : IsPGroup 2 P) (hPM : P ≤ M) :
    ∃ (S : Subgroup G) (T : Sylow 2 G), P ≤ S ∧ S ≤ M ∧ IsPGroup 2 S ∧
      (∀ U : Subgroup G, U ≤ M → IsPGroup 2 U → S ≤ U → U = S) ∧
      S ≤ (T : Subgroup G) ∧ (T : Subgroup G) ⊓ M = S := by
  classical
  have hP' : IsPGroup 2 (P.subgroupOf M) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPM).symm
  obtain ⟨S₀, hS₀⟩ := hP'.exists_le_sylow
  let S : Subgroup G := (S₀ : Subgroup ↥M).map M.subtype
  have hSM : S ≤ M := Subgroup.map_subtype_le _
  have hS2 : IsPGroup 2 S := S₀.isPGroup'.map M.subtype
  have hPS : P ≤ S := by
    intro x hx
    have : (⟨x, hPM hx⟩ : ↥M) ∈ P.subgroupOf M := hx
    exact ⟨⟨x, hPM hx⟩, hS₀ this, rfl⟩
  have hmax : ∀ U : Subgroup G, U ≤ M → IsPGroup 2 U → S ≤ U → U = S := by
    intro U hUM hU2 hSU
    have hU2' : IsPGroup 2 (U.subgroupOf M) :=
      hU2.of_equiv (Subgroup.subgroupOfEquivOfLe hUM).symm
    have hle : (S₀ : Subgroup ↥M) ≤ U.subgroupOf M := by
      intro y hy
      exact hSU ⟨y, hy, rfl⟩
    have heq : U.subgroupOf M = (S₀ : Subgroup ↥M) := S₀.is_maximal' hU2' hle
    calc U = (U.subgroupOf M).map M.subtype := (Subgroup.map_subgroupOf_eq_of_le hUM).symm
      _ = S := by rw [heq]
  obtain ⟨T, hT⟩ := hS2.exists_le_sylow
  refine ⟨S, T, hPS, hSM, hS2, hmax, hT, ?_⟩
  apply hmax
  · exact inf_le_right
  · exact T.isPGroup'.of_injective (Subgroup.inclusion (inf_le_left : (T : Subgroup G) ⊓ M ≤ T))
      (Subgroup.inclusion_injective _)
  · exact le_inf hT hSM

theorem card_le_two_mul_inf {S Q K : Subgroup G} (hidx : (Q.subgroupOf S).index = 2)
    (hKS : K ≤ S) {u : G} (huK : u ∈ K) (huQ : u ∉ Q) :
    Nat.card ↥K ≤ 2 * Nat.card ↥(K ⊓ Q : Subgroup G) := by
  classical
  have huS : u ∈ S := hKS huK
  let φ : ↥K → ↥(K ⊓ Q : Subgroup G) × Fin 2 := fun x =>
    if hx : (x : G) ∈ Q then (⟨x, Subgroup.mem_inf.2 ⟨x.2, hx⟩⟩, 0)
    else (⟨u⁻¹ * x, Subgroup.mem_inf.2 ⟨K.mul_mem (K.inv_mem huK) x.2,
      inv_mul_mem_of_index_two hidx huS (hKS x.2) huQ hx⟩⟩, 1)
  have h1 : ∀ x : ↥K, (x : G) ∈ Q → ((φ x).1 : G) = x ∧ (φ x).2 = 0 := by
    intro x hx
    simp [φ, hx]
  have h2 : ∀ x : ↥K, (x : G) ∉ Q → ((φ x).1 : G) = u⁻¹ * x ∧ (φ x).2 = 1 := by
    intro x hx
    simp [φ, hx]
  have hφ : Function.Injective φ := by
    intro x y hxy
    by_cases hx : (x : G) ∈ Q <;> by_cases hy : (y : G) ∈ Q
    · have e1 := (h1 x hx).1
      have e2 := (h1 y hy).1
      have e3 : ((φ x).1 : G) = ((φ y).1 : G) := by rw [hxy]
      exact Subtype.ext (by rw [← e1, ← e2, e3])
    · have e := congrArg Prod.snd hxy
      rw [(h1 x hx).2, (h2 y hy).2] at e
      exact absurd e (by decide)
    · have e := congrArg Prod.snd hxy
      rw [(h2 x hx).2, (h1 y hy).2] at e
      exact absurd e (by decide)
    · have e1 := (h2 x hx).1
      have e2 := (h2 y hy).1
      have e3 : ((φ x).1 : G) = ((φ y).1 : G) := by rw [hxy]
      rw [e1, e2] at e3
      exact Subtype.ext (mul_left_cancel e3)
  have := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_prod] at this
  simpa [mul_comm] using this

end Sylow

namespace Cfg3

variable {G : Type} [Group G] [Finite G] {M X : Subgroup G} {a : G} (c : Cfg3 G M X a)
include c

theorem ti_R {g x : G} (hg : g ∉ M) (hx : x ∈ rOf M X) (hgx : g⁻¹ * x * g ∈ rOf M X) :
    x = 1 := by
  by_contra hx1
  obtain ⟨k, hk⟩ := isPGroup_pCoreOf' M ⟨x, hx.1⟩
  have hk' : x ^ (2 ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hord : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one hk'
  obtain ⟨j, -, hjx⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hord
  have hj0 : j ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by simpa using hjx))
  have h2 : 2 ∣ orderOf x := by
    rw [hjx]
    exact dvd_pow_self 2 hj0
  have hz2 : orderOf (x ^ (orderOf x / 2)) = 2 :=
    orderOf_pow_orderOf_div (orderOf_pos x).ne' h2
  have hzR : x ^ (orderOf x / 2) ∈ rOf M X := (rOf M X).pow_mem hx _
  have hgzR : g⁻¹ * x ^ (orderOf x / 2) * g ∈ rOf M X := by
    have e : g⁻¹ * x ^ (orderOf x / 2) * g = (g⁻¹ * x * g) ^ (orderOf x / 2) := by
      have hc := conj_pow (a := g⁻¹) (b := x) (i := orderOf x / 2)
      rw [inv_inv] at hc
      exact hc.symm
    rw [e]
    exact (rOf M X).pow_mem hgx _
  have hgM : g⁻¹ ∈ M := by
    refine c.h.mem_of_common_involution c.hb hzR.2 hz2 ?_
    rw [inv_inv]
    exact hgzR.2
  exact hg (by simpa using M.inv_mem hgM)

theorem card_le_four_of_le_S {S R' : Subgroup G} (hS2 : IsPGroup 2 S) (hSM : S ≤ M)
    (hQS : pCoreOf 2 M ≤ S) (hcardS : Nat.card ↥S ≤ 2 * Nat.card ↥(pCoreOf 2 M))
    (hR'S : R' ≤ S) (hab : ∀ x ∈ R', ∀ y ∈ R', x * y = y * x) (hR'R : R' ⊓ rOf M X = ⊥) :
    Nat.card ↥R' ≤ 4 := by
  classical
  by_cases hR'Q : R' ≤ pCoreOf 2 M
  · exact c.card_le_four_of_inf_R hR'Q hR'R
  · obtain ⟨u, huR', huQ⟩ := Set.not_subset.1 hR'Q
    have huS : u ∈ S := hR'S huR'
    have hSn : ∀ s ∈ S, ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ ∈ pCoreOf 2 X :=
      fun s hs w hw => c.h.W_normalized (hSM hs) hw
    obtain ⟨c₀, -, -, -, hfix⟩ := exists_fixed_of_not_centralizes c.hb hS2 hSn huS
      (c.not_centralizes_of_not_mem_Q hS2 hSM huS huQ)
    have hSQ : pCoreOf 2 M ≠ S := fun h => huQ (h ▸ huS)
    have hidx := index_two_of_lt hQS hSQ hcardS
    have hB2 : Nat.card ↥(R' ⊓ pCoreOf 2 M : Subgroup G) ≤ 2 := by
      refine c.card_le_two_of_inf_R (K := R' ⊓ pCoreOf 2 M) inf_le_right ?_ (hSM huS) ?_ hfix
      · refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
        have hx' : x ∈ R' ⊓ rOf M X :=
          Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 (Subgroup.mem_inf.1 hx).1).1,
            (Subgroup.mem_inf.1 hx).2⟩
        rw [hR'R, Subgroup.mem_bot] at hx'
        exact hx'
      · intro k hk
        have h1 := hab u huR' k (Subgroup.mem_inf.1 hk).1
        calc u * k * u⁻¹ = (k * u) * u⁻¹ := by rw [h1]
          _ = k := by group
    have := card_le_two_mul_inf hidx hR'S huR' huQ
    omega

theorem card_CQ_le {y : G} (hy : y ∈ M) {c₀ : G}
    (hfix : ∀ w ∈ pCoreOf 2 X, y * w * y⁻¹ = w → w = 1 ∨ w = c₀) :
    Nat.card ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) ≤
      2 * Nat.card ↥(rOf M X ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
  classical
  have hq : ∀ q : ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G),
      ∃ w ∈ pCoreOf 2 X, ∃ r ∈ rOf M X, (q : G) = w * r :=
    fun q => c.h.q_eq_W_mul_R c.hb (Subgroup.mem_inf.1 q.2).1
  choose f hfW r hrR hfq using hq
  have hyq : ∀ q : ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G),
      y * f q * y⁻¹ = f q ∧ y * r q * y⁻¹ = r q := by
    intro q
    have h1 : y * (q : G) = (q : G) * y := by
      have := Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 q.2).2 y rfl
      exact this
    have h2 : y * (q : G) * y⁻¹ = q := by
      calc y * (q : G) * y⁻¹ = ((q : G) * y) * y⁻¹ := by rw [h1]
        _ = q := by group
    have hyw : y * f q * y⁻¹ ∈ pCoreOf 2 X := c.h.W_normalized hy (hfW q)
    have hyr : y * r q * y⁻¹ ∈ rOf M X := c.h.R_normalized hy (hrR q)
    have h3 : (y * f q * y⁻¹) * (y * r q * y⁻¹) = f q * r q := by
      calc (y * f q * y⁻¹) * (y * r q * y⁻¹) = y * (f q * r q) * y⁻¹ := by group
        _ = y * (q : G) * y⁻¹ := by rw [hfq q]
        _ = f q * r q := by rw [h2, hfq q]
    exact c.decomp_unique hyw (hfW q) hyr (hrR q) h3
  have hmem : ∀ q : ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G),
      f q ∈ ({1, c₀} : Set G) := by
    intro q
    rcases hfix _ (hfW q) (hyq q).1 with h | h
    · simp [h]
    · simp [h]
  let g : ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) →
      ↥({1, c₀} : Set G) × ↥(rOf M X ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) :=
    fun q => (⟨f q, hmem q⟩, ⟨r q, Subgroup.mem_inf.2 ⟨hrR q, by
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h = y := hh
      rw [hh']
      have := (hyq q).2
      calc y * r q = (y * r q * y⁻¹) * y := by group
        _ = r q * y := by rw [this]⟩⟩)
  have hinj : Function.Injective g := by
    intro q₁ q₂ hq12
    have e1 : f q₁ = f q₂ := congrArg (fun z => (z.1 : G)) hq12
    have e2 : r q₁ = r q₂ := congrArg (fun z => (z.2 : G)) hq12
    refine Subtype.ext ?_
    rw [hfq q₁, hfq q₂, e1, e2]
  have h1 := Nat.card_le_card_of_injective g hinj
  rw [Nat.card_prod] at h1
  have h2 : Nat.card ↥({1, c₀} : Set G) ≤ 2 := by
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (by simp)
  exact h1.trans (Nat.mul_le_mul_right _ h2)

theorem false_of_lt {S : Subgroup G} {T : Sylow 2 G} (hS2 : IsPGroup 2 S) (hSM : S ≤ M)
    (hQS : pCoreOf 2 M ≤ S) (hcardS : Nat.card ↥S ≤ 2 * Nat.card ↥(pCoreOf 2 M))
    (hST : S ≤ (T : Subgroup G)) (hTM : (T : Subgroup G) ⊓ M = S)
    (hne : S ≠ (T : Subgroup G)) (hR3 : 3 ≤ Nat.card ↥(rOf M X)) : False := by
  classical
  obtain ⟨t, htT, htS, htN⟩ := exists_mem_normalizer_of_lt T.isPGroup' hST hne
  have htM : t ∉ M := fun htM => htS (hTM ▸ Subgroup.mem_inf.2 ⟨htT, htM⟩)
  have hSQ : pCoreOf 2 M ≠ S := by
    intro h
    apply htM
    rw [← c.h.normalizer_Q_eq c.hb, h]
    exact htN
  have hidx := index_two_of_lt hQS hSQ hcardS
  have hSn : ∀ s ∈ S, ∀ w ∈ pCoreOf 2 X, s * w * s⁻¹ ∈ pCoreOf 2 X :=
    fun s hs w hw => c.h.W_normalized (hSM hs) hw
  have htS' : ∀ s ∈ S, t * s * t⁻¹ ∈ S := fun s hs => (Subgroup.mem_normalizer_iff.1 htN s).1 hs
  have htS'' : ∀ s ∈ S, t⁻¹ * s * t ∈ S := by
    intro s hs
    refine (Subgroup.mem_normalizer_iff.1 htN (t⁻¹ * s * t)).2 ?_
    have e : t * (t⁻¹ * s * t) * t⁻¹ = s := by group
    rw [e]
    exact hs
  let Q' : Subgroup G := (pCoreOf 2 M).map (MulAut.conj t).toMonoidHom
  have hQ'mem : ∀ x, x ∈ Q' ↔ ∃ q ∈ pCoreOf 2 M, t * q * t⁻¹ = x := by
    intro x
    simp [Q', Subgroup.mem_map, MulAut.conj_apply]
  have hQ'S : Q' ≤ S := by
    intro x hx
    obtain ⟨q, hq, rfl⟩ := (hQ'mem x).1 hx
    exact htS' q (hQS hq)
  have hQ'card : Nat.card ↥Q' = Nat.card ↥(pCoreOf 2 M) :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hQ'Q : ¬ (Q' ≤ pCoreOf 2 M) := by
    intro hle
    have heq : Q' = pCoreOf 2 M := Subgroup.eq_of_le_of_card_ge hle (by rw [hQ'card])
    apply htM
    rw [← c.h.normalizer_Q_eq c.hb, Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      exact hle ((hQ'mem _).2 ⟨h, hh, rfl⟩)
    · intro hh
      have h1 : t * h * t⁻¹ ∈ Q' := by rw [heq]; exact hh
      obtain ⟨q, hq, hqe⟩ := (hQ'mem _).1 h1
      have h2 : q = h := mul_left_cancel (mul_right_cancel hqe)
      rw [← h2]
      exact hq
  obtain ⟨y, hyQ', hyQ⟩ := Set.not_subset.1 hQ'Q
  have hyS : y ∈ S := hQ'S hyQ'
  obtain ⟨c₀, -, -, -, hfix⟩ := exists_fixed_of_not_centralizes c.hb hS2 hSn hyS
    (c.not_centralizes_of_not_mem_Q hS2 hSM hyS hyQ)
  have hQ'ab : ∀ x ∈ Q', ∀ x' ∈ Q', x * x' = x' * x := by
    intro x hx x' hx'
    obtain ⟨q, hq, rfl⟩ := (hQ'mem x).1 hx
    obtain ⟨q', hq', rfl⟩ := (hQ'mem x').1 hx'
    have := c.Q_comm hq hq'
    calc t * q * t⁻¹ * (t * q' * t⁻¹) = t * (q * q') * t⁻¹ := by group
      _ = t * (q' * q) * t⁻¹ := by rw [this]
      _ = t * q' * t⁻¹ * (t * q * t⁻¹) := by group
  have hyR : ∀ r ∈ rOf M X, y * r = r * y := by
    have h1 := card_le_two_mul_inf hidx hQ'S hyQ' hyQ
    have h2 : Nat.card ↥(Q' ⊓ pCoreOf 2 M : Subgroup G) ≤
        Nat.card ↥(pCoreOf 2 M ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
      refine Subgroup.card_le_of_le fun e he => Subgroup.mem_inf.2
        ⟨(Subgroup.mem_inf.1 he).2, ?_⟩
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      have hh' : h = y := hh
      rw [hh']
      exact hQ'ab _ hyQ' _ (Subgroup.mem_inf.1 he).1
    have h3 := c.card_CQ_le (hSM hyS) hfix
    have h4 := c.card_Q
    have h5 : Nat.card ↥(rOf M X) ≤
        Nat.card ↥(rOf M X ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) := by
      omega
    have h6 : (rOf M X ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) = rOf M X :=
      Subgroup.eq_of_le_of_card_ge inf_le_left h5
    intro r hr
    have : r ∈ rOf M X ⊓ Subgroup.centralizer ({y} : Set G) := by rw [h6]; exact hr
    exact Subgroup.mem_centralizer_iff.1 (Subgroup.mem_inf.1 this).2 y rfl
  have hRS : ∀ r ∈ rOf M X, ∀ s ∈ S, s * r = r * s := by
    intro r hr s hs
    by_cases hsQ : s ∈ pCoreOf 2 M
    · exact c.Q_comm hsQ hr.1
    · have hq := inv_mul_mem_of_index_two hidx hyS hs hyQ hsQ
      have e : s = y * (y⁻¹ * s) := by group
      have h1 := c.Q_comm hq hr.1
      have h2 := hyR r hr
      calc s * r = y * (y⁻¹ * s) * r := by rw [← e]
        _ = y * ((y⁻¹ * s) * r) := by group
        _ = y * (r * (y⁻¹ * s)) := by rw [h1]
        _ = (y * r) * (y⁻¹ * s) := by group
        _ = (r * y) * (y⁻¹ * s) := by rw [h2]
        _ = r * (y * (y⁻¹ * s)) := by group
        _ = r * s := by rw [← e]
  let R'' : Subgroup G := (rOf M X).map (MulAut.conj t).toMonoidHom
  have hR''mem : ∀ x, x ∈ R'' ↔ ∃ r ∈ rOf M X, t * r * t⁻¹ = x := by
    intro x
    simp [R'', Subgroup.mem_map, MulAut.conj_apply]
  have hR''card : Nat.card ↥R'' = Nat.card ↥(rOf M X) :=
    Subgroup.card_map_of_injective (MulAut.conj t).injective
  have hR''S : R'' ≤ S := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := (hR''mem x).1 hx
    exact htS' r (hQS hr.1)
  have hR''cent : ∀ x ∈ R'', ∀ s ∈ S, s * x = x * s := by
    intro x hx s hs
    obtain ⟨r, hr, rfl⟩ := (hR''mem x).1 hx
    have h1 := hRS r hr (t⁻¹ * s * t) (htS'' s hs)
    calc s * (t * r * t⁻¹) = t * ((t⁻¹ * s * t) * r) * t⁻¹ := by group
      _ = t * (r * (t⁻¹ * s * t)) * t⁻¹ := by rw [h1]
      _ = t * r * t⁻¹ * s := by group
  have hR''Q : R'' ≤ pCoreOf 2 M := by
    intro x hx
    by_contra hxQ
    refine c.not_centralizes_of_not_mem_Q hS2 hSM (hR''S hx) hxQ fun w hw => ?_
    have := hR''cent x hx w (hQS (c.h.W_le_Q hw))
    calc x * w * x⁻¹ = (w * x) * x⁻¹ := by rw [this]
      _ = w := by group
  have hR''R : R'' ⊓ rOf M X = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨r, hr, rfl⟩ := (hR''mem x).1 (Subgroup.mem_inf.1 hx).1
    refine c.ti_R htM (Subgroup.mem_inf.1 hx).2 ?_
    have e : t⁻¹ * (t * r * t⁻¹) * t = r := by group
    rw [e]
    exact hr
  have hR''y : ∀ k ∈ R'', y * k * y⁻¹ = k := by
    intro k hk
    have := hR''cent k hk y hyS
    calc y * k * y⁻¹ = (k * y) * y⁻¹ := by rw [this]
      _ = k := by group
  have h2 := c.card_le_two_of_inf_R hR''Q hR''R (hSM hyS) hR''y hfix
  omega

theorem gen4_main (hHar : HaradaInput) (hRne : rOf M X ≠ ⊥) {g : G} (hg : g ∉ M)
    (hgR : ∀ r ∈ rOf M X, g * r * g⁻¹ ∈ M) : SectionalTwoRankLE G 4 := by
  classical
  by_cases hR2 : Nat.card ↥(rOf M X) = 2
  · exact c.gen4_of_card_R_two hHar hR2
  have hR3 : 3 ≤ Nat.card ↥(rOf M X) := by
    have h1 : 1 < Nat.card ↥(rOf M X) := (Subgroup.one_lt_card_iff_ne_bot (rOf M X)).2 hRne
    omega
  let R' : Subgroup G := (rOf M X).map (MulAut.conj g).toMonoidHom
  have hR'mem : ∀ x, x ∈ R' ↔ ∃ r ∈ rOf M X, g * r * g⁻¹ = x := by
    intro x
    simp [R', Subgroup.mem_map, MulAut.conj_apply]
  have hR'M : R' ≤ M := by
    intro x hx
    obtain ⟨r, hr, rfl⟩ := (hR'mem x).1 hx
    exact hgR r hr
  have hRQ : rOf M X ≤ pCoreOf 2 M := inf_le_left
  have hR'2 : IsPGroup 2 R' := ((isPGroup_pCoreOf' M).of_injective
    (Subgroup.inclusion hRQ) (Subgroup.inclusion_injective hRQ)).map _
  have hR'card : Nat.card ↥R' = Nat.card ↥(rOf M X) :=
    Subgroup.card_map_of_injective (MulAut.conj g).injective
  have hR'ab : ∀ x ∈ R', ∀ y ∈ R', x * y = y * x := by
    intro x hx y hy
    obtain ⟨r, hr, rfl⟩ := (hR'mem x).1 hx
    obtain ⟨r', hr', rfl⟩ := (hR'mem y).1 hy
    have := c.Rab r hr r' hr'
    calc g * r * g⁻¹ * (g * r' * g⁻¹) = g * (r * r') * g⁻¹ := by group
      _ = g * (r' * r) * g⁻¹ := by rw [this]
      _ = g * r' * g⁻¹ * (g * r * g⁻¹) := by group
  have hR'R : R' ⊓ rOf M X = ⊥ := by
    refine (Subgroup.eq_bot_iff_forall _).2 fun x hx => ?_
    obtain ⟨r, hr, rfl⟩ := (hR'mem x).1 (Subgroup.mem_inf.1 hx).1
    refine c.ti_R hg (Subgroup.mem_inf.1 hx).2 ?_
    have e : g⁻¹ * (g * r * g⁻¹) * g = r := by group
    rw [e]
    exact hr
  have hnormQ : M ≤ Subgroup.normalizer ((pCoreOf 2 M : Subgroup G) : Set G) :=
    (c.h.normalizer_Q_eq c.hb).ge
  have hP2 : IsPGroup 2 (pCoreOf 2 M ⊔ R' : Subgroup G) :=
    (isPGroup_pCoreOf' M).to_sup_of_normal_left' hR'2 (fun x hx => hnormQ (hR'M hx))
  obtain ⟨S, T, hPS, hSM, hS2, -, hST, hTM⟩ :=
    exists_sylow_pair hP2 (sup_le (pCoreOf_le_self M) hR'M)
  have hQS : pCoreOf 2 M ≤ S := le_trans le_sup_left hPS
  have hR'S : R' ≤ S := le_trans le_sup_right hPS
  have hcardS : Nat.card ↥S ≤ 2 * Nat.card ↥(pCoreOf 2 M) := c.card_S_le hS2 hSM hQS
  have hR'4 : Nat.card ↥R' ≤ 4 := c.card_le_four_of_le_S hS2 hSM hQS hcardS hR'S hR'ab hR'R
  have hcardQ := c.card_Q
  have hTS : (T : Subgroup G) = S := by
    by_contra hne
    exact c.false_of_lt hS2 hSM hQS hcardS hST hTM (Ne.symm hne) hR3
  refine sectionalTwoRankLE_four_of_noE32G T ?_
  rw [hTS]
  refine noE32G_of_card_le_32 (by omega) fun h32 => ?_
  have hSQ : pCoreOf 2 M ≠ S := by
    intro h
    rw [← h] at h32
    omega
  obtain ⟨u, huS, huQ⟩ := IsConcreteLE.exists_of_lt (lt_of_le_of_ne hQS hSQ)
  have hns := c.not_centralizes_of_not_mem_Q hS2 hSM huS huQ
  push Not at hns
  obtain ⟨w, hw, hwu⟩ := hns
  refine ⟨u, huS, w, hQS (c.h.W_le_Q hw), fun h => hwu ?_⟩
  calc u * w * u⁻¹ = (w * u) * u⁻¹ := by rw [← h]
    _ = w := by group

end Cfg3

end CFSG.RankThree.PartOne.SolD3
