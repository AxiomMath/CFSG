module

public import CFSG.LocalAnalysis.UniquenessCase.UC6M591G
public import CFSG.LocalAnalysis.UniquenessCase.UC6C623Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools CFSG.LocalAnalysis.UniquenessCase.UC22

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

noncomputable def CenL (S : Set G) : Subgroup G where
  carrier := {x | x ∈ normalizer (m.L : Set G) ∧ ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ m.OL}
  one_mem' := ⟨one_mem _, fun s _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hasa⟩ ⟨hb, hbsb⟩
    refine ⟨mul_mem ha hb, fun s hs => ?_⟩
    have h3 : a * (b * s * b⁻¹ * s⁻¹) * a⁻¹ ∈ m.OL :=
      (mem_normalizer_iff.1 (m.mem_normalizer_OL ha) _).1 (hbsb s hs)
    have e : a * b * s * (a * b)⁻¹ * s⁻¹ =
        (a * (b * s * b⁻¹ * s⁻¹) * a⁻¹) * (a * s * a⁻¹ * s⁻¹) := by group
    rw [e]
    exact m.OL.mul_mem h3 (hasa s hs)
  inv_mem' := by
    rintro a ⟨ha, hasa⟩
    refine ⟨inv_mem ha, fun s hs => ?_⟩
    have h3 : a⁻¹ * (a * s * a⁻¹ * s⁻¹) * a⁻¹⁻¹ ∈ m.OL :=
      (mem_normalizer_iff.1 (m.mem_normalizer_OL (inv_mem ha)) _).1 (hasa s hs)
    have e : a⁻¹ * s * a⁻¹⁻¹ * s⁻¹ = (a⁻¹ * (a * s * a⁻¹ * s⁻¹) * a⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact m.OL.inv_mem h3

noncomputable abbrev KerL : Subgroup G := m.CenL (m.L : Set G)

theorem mem_CenL {S : Set G} {x : G} :
    x ∈ m.CenL S ↔ x ∈ normalizer (m.L : Set G) ∧ ∀ s ∈ S, x * s * x⁻¹ * s⁻¹ ∈ m.OL := Iff.rfl

theorem conj_mem_KerL {n y : G} (hn : n ∈ normalizer (m.L : Set G)) (hy : y ∈ m.KerL) :
    n * y * n⁻¹ ∈ m.KerL := by
  refine ⟨mul_mem (mul_mem hn hy.1) (inv_mem hn), fun l hl => ?_⟩
  have hl' : n⁻¹ * l * n ∈ m.L := by
    have := (mem_normalizer_iff.1 (inv_mem hn) l).1 hl
    simpa using this
  have h1 := hy.2 _ hl'
  have h2 : n * (y * (n⁻¹ * l * n) * y⁻¹ * (n⁻¹ * l * n)⁻¹) * n⁻¹ ∈ m.OL :=
    (mem_normalizer_iff.1 (m.mem_normalizer_OL hn) _).1 h1
  have e : n * y * n⁻¹ * l * (n * y * n⁻¹)⁻¹ * l⁻¹ =
      n * (y * (n⁻¹ * l * n) * y⁻¹ * (n⁻¹ * l * n)⁻¹) * n⁻¹ := by group
  rw [e]
  exact h2

theorem mem_KerL_iff {y : G} (hy : y ∈ normalizer (m.L : Set G)) :
    y ∈ m.KerL ↔ ⁅zpowers y, m.L⁆ ≤ m.OL := by
  constructor
  · intro h
    rw [Subgroup.commutator_le]
    intro x hx l hl
    have hxK : x ∈ m.KerL := Subgroup.zpowers_le.2 h hx
    rw [commutatorElement_def]
    exact hxK.2 l hl
  · intro h
    exact ⟨hy, fun l hl => by
      have := h (Subgroup.commutator_mem_commutator (mem_zpowers y) hl)
      rwa [commutatorElement_def] at this⟩

noncomputable def CenMod (x : G) : Subgroup G where
  carrier := {c | c ∈ normalizer (m.L : Set G) ∧ ∃ κ ∈ m.KerL, c * x * c⁻¹ = x * κ}
  one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, κa, hκa, hax⟩ ⟨hb, κb, hκb, hbx⟩
    refine ⟨mul_mem ha hb, κa * (a * κb * a⁻¹), mul_mem hκa (m.conj_mem_KerL ha hκb), ?_⟩
    calc a * b * x * (a * b)⁻¹ = a * (b * x * b⁻¹) * a⁻¹ := by group
      _ = a * (x * κb) * a⁻¹ := by rw [hbx]
      _ = (a * x * a⁻¹) * (a * κb * a⁻¹) := by group
      _ = (x * κa) * (a * κb * a⁻¹) := by rw [hax]
      _ = x * (κa * (a * κb * a⁻¹)) := by group
  inv_mem' := by
    rintro a ⟨ha, κ, hκ, hax⟩
    have hκ' : a⁻¹ * κ * a ∈ m.KerL := by simpa using m.conj_mem_KerL (inv_mem ha) hκ
    refine ⟨inv_mem ha, (a⁻¹ * κ * a)⁻¹, m.KerL.inv_mem hκ', ?_⟩
    have key : a⁻¹ * x * a * (a⁻¹ * κ * a) = x := by
      calc a⁻¹ * x * a * (a⁻¹ * κ * a) = a⁻¹ * (x * κ) * a := by group
        _ = a⁻¹ * (a * x * a⁻¹) * a := by rw [hax]
        _ = x := by group
    have := eq_mul_inv_of_mul_eq key
    simpa using this

theorem KerL_le_CenMod {x : G} (hx : x ∈ m.L) : m.KerL ≤ m.CenMod x := by
  intro c hc
  refine ⟨hc.1, (x⁻¹ * c * x⁻¹⁻¹) * c⁻¹, ?_, ?_⟩
  · exact m.KerL.mul_mem (m.conj_mem_KerL (inv_mem (Subgroup.le_normalizer hx)) hc) (m.KerL.inv_mem hc)
  · group

theorem EL_le_R : m.EL ≤ m.R := inf_le_left.trans m.A_le_R

theorem EL_le_L : m.EL ≤ m.L := inf_le_right

theorem comm_R_EL (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) {e x : G} (he : e ∈ m.EL) (hx : x ∈ m.R) :
    e * x = x * e :=
  (m.hZ.sixteen h69).1 e he.1 x hx

theorem exists_orderOf_eq_pow_of_mem_R {x : G} (hx : x ∈ m.R) : ∃ k : ℕ, orderOf x = m.r ^ k := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 m.d.sylow.isPGroup) ⟨x, hx⟩
  exact ⟨k, by rwa [Subgroup.orderOf_mk] at hk⟩

theorem normalizer_R_le_M : normalizer (m.R : Set G) ≤ m.M := by
  have hE1 : m.E ≠ ⊥ := by
    intro h
    have : m.r ^ 2 = 1 := by rw [← m.d.E_card, h]; exact Subgroup.card_bot
    rcases pow_eq_one_iff.1 this with h1 | h1
    · exact m.hr.ne_one h1
    · exact two_ne_zero h1
  exact m.d.normalizer_le_of_le_pGroup m.hC le_rfl hE1 m.E_le_R m.d.sylow.isPGroup

theorem mem_normalizer_EL {l : G} (hlN : l ∈ normalizer (m.L : Set G))
    (hlA : l ∈ normalizer (m.A : Set G)) : l ∈ normalizer (m.EL : Set G) := by
  rw [mem_normalizer_iff] at hlN hlA ⊢
  intro w
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨(hlA w).1 h1, (hlN w).1 h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨(hlA w).2 h1, (hlN w).2 h2⟩

theorem centralizer_EL_le_M (h620 : m.C620) (h632 : m.C632) : centralizer (m.EL : Set G) ≤ m.M := by
  have hne : m.EL ≠ ⊥ := by
    intro h
    have hc : Nat.card ↥m.EL = m.r ^ 2 := m.card_A_inf_L h620
    rw [h, Subgroup.card_bot] at hc
    have h2 : 1 < m.r ^ 2 := Nat.one_lt_pow two_ne_zero m.hr.one_lt
    omega
  obtain ⟨a, ha⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hne
  have ha1 : (a : G) ≠ 1 := fun h => ha (Subtype.ext h)
  intro x hx
  have hxa : x ∈ centralizer ({(a : G)} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 a.2) hx
  exact m.normalizer_le_M_of_le_EL h632 (Subgroup.zpowers_le.2 a.2)
    (fun h => ha1 (Subgroup.zpowers_eq_bot.1 h)) (centralizer_singleton_le_normalizer_zpowers _ hxa)

theorem EL_inf_KerL_eq_bot (h619 : m.C619) (h620 : m.C620) (h621 : m.C621) (h632 : m.C632) :
    m.EL ⊓ m.KerL = ⊥ := by
  rcases h621 (m.EL ⊓ m.KerL) inf_le_left (fun l hl => by
      refine mem_normalizer_of_forward_uc6 fun w hw => ⟨?_, ?_⟩
      · exact (mem_normalizer_iff.1 (m.mem_normalizer_EL (Subgroup.le_normalizer hl.1) hl.2) w).1 hw.1
      · exact m.conj_mem_KerL (Subgroup.le_normalizer hl.1) hw.2) with h | h
  · exact h
  · exfalso
    have hEK : m.EL ≤ m.KerL := fun e he => by
      have : e ∈ m.EL ⊓ m.KerL := by rw [h]; exact he
      exact this.2
    have hcent : ∀ y ∈ m.L, ∀ e ∈ m.EL, y * e * y⁻¹ * e⁻¹ ∈ m.OL := by
      intro y hy e he
      have h1 := (hEK he).2 y hy
      have : y * e * y⁻¹ * e⁻¹ = (e * y * e⁻¹ * y⁻¹)⁻¹ := by group
      rw [this]
      exact m.OL.inv_mem h1
    have hsup := m.eq_sup_centralizer_EL (Y := m.L) (fun x hx => Subgroup.le_normalizer hx)
      (fun e he => Subgroup.le_normalizer (m.EL_le_L he)) hcent
    exact m.not_L_le_M h619 ((le_of_eq hsup).trans (sup_le
      (inf_le_right.trans (m.OL_le_M h620 h632))
      (inf_le_right.trans (m.centralizer_EL_le_M h620 h632))))

theorem exists_EL_mul_mem_KerL (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (hKC : m.KC633) {x : G}
    (hx : x ∈ m.R) : ∃ e ∈ m.EL, e⁻¹ * x ∈ m.KerL := by
  have hxN : x ∈ normalizer (m.L : Set G) := m.H_le_normalizer_L (m.hZ.R_le_centralizer h69 hx)
  obtain ⟨e, he, hcomm⟩ := hKC x hxN (m.exists_orderOf_eq_pow_of_mem_R hx) (fun e he => by
    have h1 : x * e * x⁻¹ * e⁻¹ = 1 := by rw [← m.comm_R_EL h69 he hx]; group
    rw [h1]
    exact one_mem _)
  exact ⟨e, he, (m.mem_KerL_iff (mul_mem (inv_mem (Subgroup.le_normalizer (m.EL_le_L he))) hxN)).2 hcomm⟩

theorem R_le_CenMod (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) {e : G} (he : e ∈ m.EL) :
    m.R ≤ m.CenMod e := by
  intro c hc
  refine ⟨m.H_le_normalizer_L (m.hZ.R_le_centralizer h69 hc), 1, one_mem _, ?_⟩
  rw [← m.comm_R_EL h69 he hc]
  group

theorem exists_gen_R_inf_K (h625 : m.C625) :
    ∃ g ∈ m.R ⊓ m.K, ∀ x ∈ m.R ⊓ m.K, ∃ k : ℤ, g ^ k = x := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hsyl : IsSylowOf m.r (m.R ⊓ m.K) m.K :=
    m.d.sylow.inf_of_le_normalizer m.K_le_M (fun g hg => m.mem_normalizer_K hg)
  obtain ⟨Q, hQ⟩ := hsyl.exists_sylow_eq_subgroupOf
  have hcyc : IsCyclic ↥Q := m.sylow_cyclic_of_pRank_eq_one h625 (m.hr.odd_of_ne_two m.d.odd) Q
  have hcyc' : IsCyclic ↥((m.R ⊓ m.K).subgroupOf m.K) := by
    rw [← hQ]
    exact hcyc
  have hle : m.R ⊓ m.K ≤ m.K := inf_le_right
  haveI : IsCyclic ↥(m.R ⊓ m.K) :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hle).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hle).surjective
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(m.R ⊓ m.K))
  refine ⟨g, g.2, fun x hx => ?_⟩
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨x, hx⟩)
  exact ⟨k, by simpa using congrArg Subtype.val hk⟩

theorem exists_normalizer_R (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (hKC : m.KC633) {l : G}
    (hlL : l ∈ m.L) (hlA : l ∈ normalizer (m.A : Set G)) :
    ∃ c ∈ m.R ⊔ (m.KerL ⊓ m.H), l * c ∈ normalizer (m.R : Set G) := by
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hRH : m.R ≤ m.H := m.hZ.R_le_centralizer h69
  have hJH : m.R ⊔ (m.KerL ⊓ m.H) ≤ m.H := sup_le hRH inf_le_right
  have hSylJ : IsSylowOf m.r m.R (m.R ⊔ (m.KerL ⊓ m.H)) :=
    (m.hZ.R_sylow hRH).of_le le_sup_left hJH
  have hlN : l ∈ normalizer (m.L : Set G) := Subgroup.le_normalizer hlL
  have hQp : IsPGroup m.r (m.R.map (MulAut.conj l⁻¹).toMonoidHom) :=
    m.d.sylow.isPGroup.map _
  have hQJ : m.R.map (MulAut.conj l⁻¹).toMonoidHom ≤ m.R ⊔ (m.KerL ⊓ m.H) := by
    rintro _ ⟨y, hy, rfl⟩
    obtain ⟨e, he, hw⟩ := m.exists_EL_mul_mem_KerL h69 hKC hy
    have hconj : (MulAut.conj l⁻¹).toMonoidHom y = (l⁻¹ * e * l) * (l⁻¹ * (e⁻¹ * y) * l) := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [hconj]
    refine mul_mem (mem_sup_left ?_) (mem_sup_right ⟨?_, ?_⟩)
    · have : l⁻¹ * e * l⁻¹⁻¹ ∈ m.A := (mem_normalizer_iff.1 (inv_mem hlA) e).1 he.1
      simpa using m.A_le_R this
    · simpa using m.conj_mem_KerL (inv_mem hlN) hw
    · exact m.H.mul_mem (m.H.mul_mem (m.H.inv_mem (m.L_le_H hlL))
        (m.H.mul_mem (m.H.inv_mem (m.L_le_H (m.EL_le_L he))) (hRH hy))) (m.L_le_H hlL)
  obtain ⟨c, hcJ, hc⟩ := exists_conj_le_of_isSylowOf hSylJ hQJ hQp
  refine ⟨c, hcJ, ?_⟩
  have hn : (l * c)⁻¹ ∈ normalizer (m.R : Set G) := by
    refine mem_normalizer_of_forward_uc6 fun w hw => ?_
    have h1 := hc ((MulAut.conj l⁻¹).toMonoidHom w) ⟨w, hw, rfl⟩
    have e : (l * c)⁻¹ * w * ((l * c)⁻¹)⁻¹ = c⁻¹ * (MulAut.conj l⁻¹).toMonoidHom w * c := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact h1
  simpa using (normalizer (m.R : Set G)).inv_mem hn

theorem R_inf_K_le_KerL (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h619 : m.C619) (h620 : m.C620)
    (h621 : m.C621) (h625 : m.C625) (h632 : m.C632) (hKC : m.KC633) : m.R ⊓ m.K ≤ m.KerL := by
  obtain ⟨g, hg, hgen⟩ := m.exists_gen_R_inf_K h625
  obtain ⟨e₀, he₀, hw₀⟩ := m.exists_EL_mul_mem_KerL h69 hKC hg.1
  obtain ⟨w₀, hw₀', hgdec⟩ : ∃ w₀ ∈ m.KerL, g = e₀ * w₀ := ⟨e₀⁻¹ * g, hw₀, by group⟩
  have hbot := m.EL_inf_KerL_eq_bot h619 h620 h621 h632
  have he₀N : e₀ ∈ normalizer (m.L : Set G) := Subgroup.le_normalizer (m.EL_le_L he₀)
  have hT : ∀ k : ℤ, (e₀ ^ k)⁻¹ * g ^ k ∈ m.KerL := by
    intro k
    refine Int.induction_on k (by simp) (fun i ih => ?_) (fun i ih => ?_)
    · have h1 := m.conj_mem_KerL (inv_mem he₀N) ih
      have h2 := m.KerL.mul_mem h1 hw₀
      have e : (e₀ ^ ((i : ℤ) + 1))⁻¹ * g ^ ((i : ℤ) + 1) =
          (e₀⁻¹ * ((e₀ ^ (i : ℤ))⁻¹ * g ^ (i : ℤ)) * e₀⁻¹⁻¹) * (e₀⁻¹ * g) := by group
      rw [e]
      exact h2
    · have h1 := m.conj_mem_KerL he₀N ih
      have h2 := m.conj_mem_KerL he₀N (m.KerL.inv_mem hw₀)
      have h3 := m.KerL.mul_mem h1 h2
      have e : (e₀ ^ (-(i : ℤ) - 1))⁻¹ * g ^ (-(i : ℤ) - 1) =
          (e₀ * ((e₀ ^ (-(i : ℤ)))⁻¹ * g ^ (-(i : ℤ))) * e₀⁻¹) * (e₀ * (e₀⁻¹ * g)⁻¹ * e₀⁻¹) := by group
      rw [e]
      exact m.KerL.mul_mem h1 (by simpa using h2)
  have hinv : ∀ l ∈ m.L ⊓ normalizer (m.A : Set G), ∃ k : ℤ, l * e₀ * l⁻¹ = e₀ ^ k := by
    intro l hl
    have hlN : l ∈ normalizer (m.L : Set G) := Subgroup.le_normalizer hl.1
    obtain ⟨c, hcJ, hlc⟩ := m.exists_normalizer_R h69 hKC hl.1 hl.2
    have hcmod : c ∈ m.CenMod e₀ :=
      (sup_le (m.R_le_CenMod h69 he₀) (inf_le_left.trans (m.KerL_le_CenMod (m.EL_le_L he₀)))) hcJ
    obtain ⟨hcN, κ, hκ, hcκ⟩ := hcmod
    have hnM : l * c ∈ m.M := m.normalizer_R_le_M hlc
    have hgR' : (l * c) * g * (l * c)⁻¹ ∈ m.R := (mem_normalizer_iff.1 hlc g).1 hg.1
    have hgK' : (l * c) * g * (l * c)⁻¹ ∈ m.K := m.conj_mem_K hnM hg.2
    obtain ⟨k, hk⟩ := hgen _ ⟨hgR', hgK'⟩
    have h1 : c * g * c⁻¹ = (c * e₀ * c⁻¹) * (c * w₀ * c⁻¹) := by rw [hgdec]; group
    rw [hcκ] at h1
    have hκ₃ : l * (κ * (c * w₀ * c⁻¹)) * l⁻¹ ∈ m.KerL :=
      m.conj_mem_KerL hlN (m.KerL.mul_mem hκ (m.conj_mem_KerL hcN hw₀'))
    have h2 : g ^ k = (l * e₀ * l⁻¹) * (l * (κ * (c * w₀ * c⁻¹)) * l⁻¹) := by
      rw [hk]
      calc l * c * g * (l * c)⁻¹ = l * (c * g * c⁻¹) * l⁻¹ := by group
        _ = l * (e₀ * κ * (c * w₀ * c⁻¹)) * l⁻¹ := by rw [h1]
        _ = _ := by group
    have h3 : (e₀ ^ k)⁻¹ * (l * e₀ * l⁻¹) =
        ((e₀ ^ k)⁻¹ * g ^ k) * (l * (κ * (c * w₀ * c⁻¹)) * l⁻¹)⁻¹ := by
      rw [h2]
      group
    have hmemEL : (e₀ ^ k)⁻¹ * (l * e₀ * l⁻¹) ∈ m.EL :=
      m.EL.mul_mem (m.EL.inv_mem (m.EL.zpow_mem he₀ k))
        ((mem_normalizer_iff.1 (m.mem_normalizer_EL hlN hl.2) e₀).1 he₀)
    have hmemK : (e₀ ^ k)⁻¹ * (l * e₀ * l⁻¹) ∈ m.KerL := by
      rw [h3]
      exact m.KerL.mul_mem (hT k) (m.KerL.inv_mem hκ₃)
    have hmem1 : (e₀ ^ k)⁻¹ * (l * e₀ * l⁻¹) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hmemEL, hmemK⟩
    exact ⟨k, ((inv_mul_eq_one.1 (Subgroup.mem_bot.1 hmem1))).symm⟩
  have hnorm : m.L ⊓ normalizer (m.A : Set G) ≤ normalizer ((zpowers e₀ : Subgroup G) : Set G) := by
    intro l hl
    refine mem_normalizer_of_forward_uc6 fun w hw => ?_
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.1 hw
    obtain ⟨k, hk⟩ := hinv l hl
    have e : l * e₀ ^ j * l⁻¹ = (l * e₀ * l⁻¹) ^ j := conj_zpow.symm
    rw [e, hk]
    exact Subgroup.mem_zpowers_iff.2 ⟨k * j, by rw [zpow_mul]⟩
  have he₀1 : e₀ = 1 := by
    rcases h621 (zpowers e₀) (Subgroup.zpowers_le.2 he₀) hnorm with h | h
    · exact Subgroup.zpowers_eq_bot.1 h
    · exfalso
      have hc : Nat.card ↥m.EL = m.r ^ 2 := m.card_A_inf_L h620
      have hz : Nat.card ↥(zpowers e₀) = orderOf e₀ := Nat.card_zpowers e₀
      have hdvd : orderOf e₀ ∣ m.r := orderOf_dvd_of_pow_eq_one (m.isElemAbelian_A.2 e₀ he₀.1)
      have hle : orderOf e₀ ≤ m.r := Nat.le_of_dvd m.hr.pos hdvd
      have hcard : Nat.card ↥(zpowers e₀) = m.r ^ 2 := by rw [h]; exact hc
      have := m.hr.two_le
      nlinarith
  have hgK : g ∈ m.KerL := by simpa [he₀1] using hw₀
  intro x hx
  obtain ⟨k, rfl⟩ := hgen x hx
  exact m.KerL.zpow_mem hgK k

theorem rElt_trivial_on_Lbar (h69 : R6_9 (dataOfSetup4 m.hS m.hU m.S)) (h619 : m.C619) (h620 : m.C620)
    (h621 : m.C621) (h625 : m.C625) (h632 : m.C632) (hKC : m.KC633) :
    ∀ y ∈ m.K ⊓ normalizer (m.L : Set G), (∃ k : ℕ, orderOf y = m.r ^ k) →
      ⁅zpowers y, m.L⁆ ≤ m.OL := by
  rintro y hy ⟨k, hk⟩
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  refine (m.mem_KerL_iff hy.2).1 ?_
  have hsyl : IsSylowOf m.r (m.R ⊓ m.K) m.K :=
    m.d.sylow.inf_of_le_normalizer m.K_le_M (fun g hg => m.mem_normalizer_K hg)
  have hX : m.R ⊓ m.K ≤ m.K ⊓ normalizer (m.L : Set G) := fun x hx =>
    ⟨hx.2, m.H_le_normalizer_L (m.hZ.R_le_centralizer h69 hx.1)⟩
  have hsylX : IsSylowOf m.r (m.R ⊓ m.K) (m.K ⊓ normalizer (m.L : Set G)) :=
    hsyl.of_le hX inf_le_left
  have hQp : IsPGroup m.r (zpowers y) := IsPGroup.of_card (n := k) (by rw [Nat.card_zpowers, hk])
  obtain ⟨κ, hκX, hκ⟩ := exists_conj_le_of_isSylowOf hsylX (Subgroup.zpowers_le.2 hy) hQp
  have h1 : κ⁻¹ * y * κ ∈ m.KerL :=
    m.R_inf_K_le_KerL h69 h619 h620 h621 h625 h632 hKC (hκ y (mem_zpowers y))
  have h2 := m.conj_mem_KerL hκX.2 h1
  have e : κ * (κ⁻¹ * y * κ) * κ⁻¹ = y := by group
  rwa [e] at h2

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6
