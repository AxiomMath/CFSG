module

public import CFSG.Quasithin.MS93.S36SpStmt
public import CFSG.Quasithin.MS93.M15Lift
public import CFSG.Quasithin.MS93.S33Base

public section

namespace CFSG.Quasithin.MS93.S36SP

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

section TrivW

@[expose] def trivW (h : PUHyp M T L) : Subgroup G where
  carrier := {m | m ∈ M ∧ ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Zq M L}
  one_mem' := ⟨M.one_mem, fun u _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
    refine ⟨M.mul_mem hxM hyM, fun u hu => ?_⟩
    have hZn := le_normalizer_Zq h.le_normalizer
    have e : x * y * u * (x * y)⁻¹ * u⁻¹ =
        (x * (y * u * y⁻¹ * u⁻¹) * x⁻¹) * (x * u * x⁻¹ * u⁻¹) := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hZn hxM) _).1 (hy u hu)) (hx u hu)
  inv_mem' := by
    rintro x ⟨hxM, hx⟩
    refine ⟨M.inv_mem hxM, fun u hu => ?_⟩
    have hZn := le_normalizer_Zq h.le_normalizer
    have e : x⁻¹ * u * x⁻¹⁻¹ * u⁻¹ = (x⁻¹ * (x * u * x⁻¹ * u⁻¹) * x⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ((Subgroup.mem_normalizer_iff.1 (hZn (M.inv_mem hxM)) _).1 (hx u hu))

theorem mem_trivW (h : PUHyp M T L) {m : G} :
    m ∈ trivW h ↔ m ∈ M ∧ ∀ u ∈ Uq M T L, m * u * m⁻¹ * u⁻¹ ∈ Zq M L := Iff.rfl

theorem trivW_le (h : PUHyp M T L) : trivW h ≤ M := fun _ hm => hm.1

theorem le_normalizer_trivW (h : PUHyp M T L) :
    M ≤ Subgroup.normalizer (trivW h : Set G) := by
  have hUn := le_normalizer_Uq (T := T) h.le_normalizer
  have hZn := le_normalizer_Zq h.le_normalizer
  have key : ∀ m ∈ M, ∀ x ∈ trivW h, m * x * m⁻¹ ∈ trivW h := by
    rintro m hm x ⟨hxM, hx⟩
    refine ⟨M.mul_mem (M.mul_mem hm hxM) (M.inv_mem hm), fun u hu => ?_⟩
    have hu' : m⁻¹ * u * m⁻¹⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hUn (M.inv_mem hm)) u).1 hu
    have e : m * x * m⁻¹ * u * (m * x * m⁻¹)⁻¹ * u⁻¹ =
        m * (x * (m⁻¹ * u * m⁻¹⁻¹) * x⁻¹ * (m⁻¹ * u * m⁻¹⁻¹)⁻¹) * m⁻¹ := by group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.1 (hZn hm) _).1 (hx _ hu')
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key m hm x, fun hx => ?_⟩
  have := key m⁻¹ (M.inv_mem hm) _ hx
  simpa [mul_assoc] using this

theorem not_L_le_trivW (h : PUHyp M T L) : ¬ L ≤ trivW h := by
  intro hL
  have hUL : ⁅Uq M T L, L⁆ ≤ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    have h1 := (hL hl).2 u⁻¹ (inv_mem hu)
    have hc : l * u⁻¹ * l⁻¹ * u⁻¹⁻¹ ∈ Uq M T L :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (le_normalizer_Uq h.le_normalizer (h.L_le hl))
        _).1 (inv_mem hu)) (inv_mem (inv_mem hu))
    have h2 : l * u⁻¹ * l⁻¹ * u⁻¹⁻¹ ∈ Uq M T L ⊓ Zq M L := ⟨hc, h1⟩
    rw [h.Uq_inf_Zq] at h2
    have e : ⁅u, l⁆ = u * (l * u⁻¹ * l⁻¹ * u⁻¹⁻¹) * u⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e, Sp4L.uq_comm h hu h2.1, mul_inv_cancel_right]
    exact h2.2
  have h3 : ⁅⁅Uq M T L, L⁆, L⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro x hx l hl
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 (hUL hx) l hl).symm
  rw [h.commutator_uq, h.commutator_uq] at h3
  exact h.Uq_ne_bot h3

theorem mem_centralizer_of_mem_trivW (h : PUHyp M T L) {y : G} (hy : y ∈ trivW h) :
    y ∈ Subgroup.centralizer (Uq M T L : Set G) := by
  have hcomm : ⁅trivW h, L⁆ ≤ pCoreOf 2 M :=
    h.commutator_le_pCoreOf_M (trivW_le h) (le_normalizer_trivW h) (not_L_le_trivW h)
  have hQ : pCoreOf 2 M ≤ Subgroup.centralizer (Uq M T L : Set G) :=
    h.pCoreOf_le_centralizer_Z0q.trans (Subgroup.centralizer_le (Uq_le_Z0q h.L_le))
  have hMU : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have hyM : y ∈ M := hy.1
  have key : ∀ u ∈ Uq M T L, ∀ l ∈ L, y * ⁅u, l⁆ * y⁻¹ = ⁅u, l⁆ := by
    intro u hu l hl
    set c := y * u * y⁻¹ * u⁻¹ with hc
    set n := y * l * y⁻¹ * l⁻¹ with hn
    have hcU : c ∈ Uq M T L :=
      mul_mem ((Subgroup.mem_normalizer_iff.1 (hMU hyM) u).1 hu) (inv_mem hu)
    have hcL : c ∈ Subgroup.centralizer (L : Set G) := by
      have h2 : c ∈ Uq M T L ⊓ Zq M L := ⟨hcU, hy.2 u hu⟩
      rw [h.Uq_inf_Zq] at h2
      exact h2.2
    have hnU : n ∈ Subgroup.centralizer (Uq M T L : Set G) := by
      apply hQ
      apply hcomm
      have := Subgroup.commutator_mem_commutator hy hl
      rwa [commutatorElement_def] at this
    have hw : l * u⁻¹ * l⁻¹ ∈ Uq M T L :=
      (Subgroup.mem_normalizer_iff.1 (hMU (h.L_le hl)) _).1 (inv_mem hu)
    have hcl : l * c⁻¹ * l⁻¹ = c⁻¹ := by
      have := Subgroup.mem_centralizer_iff.1 hcL l hl
      calc l * c⁻¹ * l⁻¹ = (l * c * l⁻¹)⁻¹ := by group
        _ = c⁻¹ := by rw [this, mul_inv_cancel_right]
    have hnw : ∀ w ∈ Uq M T L, n * w * n⁻¹ = w := fun w hw => by
      rw [← Subgroup.mem_centralizer_iff.1 hnU w hw, mul_inv_cancel_right]
    have hwc : l * u⁻¹ * l⁻¹ * c⁻¹ ∈ Uq M T L := mul_mem hw (inv_mem hcU)
    have e0 : y * ⁅u, l⁆ * y⁻¹ = (c * u) * (n * l) * (c * u)⁻¹ * (n * l)⁻¹ := by
      simp only [hc, hn, commutatorElement_def]
      group
    rw [e0]
    calc (c * u) * (n * l) * (c * u)⁻¹ * (n * l)⁻¹ =
        c * u * (n * ((l * u⁻¹ * l⁻¹) * (l * c⁻¹ * l⁻¹)) * n⁻¹) := by group
      _ = c * u * (n * (l * u⁻¹ * l⁻¹ * c⁻¹) * n⁻¹) := by rw [hcl]
      _ = c * u * (l * u⁻¹ * l⁻¹ * c⁻¹) := by rw [hnw _ hwc]
      _ = u * c * (l * u⁻¹ * l⁻¹ * c⁻¹) := by rw [Sp4L.uq_comm h hcU hu]
      _ = u * (c * (l * u⁻¹ * l⁻¹)) * c⁻¹ := by group
      _ = u * ((l * u⁻¹ * l⁻¹) * c) * c⁻¹ := by rw [Sp4L.uq_comm h hcU hw]
      _ = ⁅u, l⁆ := by
          simp only [commutatorElement_def]
          group
  have hle : ⁅Uq M T L, L⁆ ≤ Subgroup.centralizer ({y} : Set G) := by
    rw [Subgroup.commutator_le]
    intro u hu l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff.1 hz]
    calc y * ⁅u, l⁆ = y * ⁅u, l⁆ * y⁻¹ * y := by group
      _ = ⁅u, l⁆ * y := by rw [key u hu l hl]
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  rw [← h.commutator_uq] at hu
  exact ((Subgroup.mem_centralizer_iff.1 (hle hu)) y rfl).symm

theorem mem_pCoreOf_of_mem_trivW (h : PUHyp M T L) {t : G} (htT : t ∈ T) (ht : t ∈ trivW h) :
    t ∈ pCoreOf 2 M := by
  rw [← S33.inf_centralizer_Uq h]
  exact ⟨htT, mem_centralizer_of_mem_trivW h ht⟩

end TrivW

section Sections

@[expose] def secKer (M A B : Subgroup G) (hB : M ≤ Subgroup.normalizer (B : Set G)) :
    Subgroup G where
  carrier := {m | m ∈ M ∧ ∀ x ∈ A, m * x * m⁻¹ * x⁻¹ ∈ B}
  one_mem' := ⟨M.one_mem, fun x _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxM, hx⟩ ⟨hyM, hy⟩
    refine ⟨M.mul_mem hxM hyM, fun a ha => ?_⟩
    have e : x * y * a * (x * y)⁻¹ * a⁻¹ =
        (x * (y * a * y⁻¹ * a⁻¹) * x⁻¹) * (x * a * x⁻¹ * a⁻¹) := by group
    rw [e]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 (hB hxM) _).1 (hy a ha)) (hx a ha)
  inv_mem' := by
    rintro x ⟨hxM, hx⟩
    refine ⟨M.inv_mem hxM, fun a ha => ?_⟩
    have e : x⁻¹ * a * x⁻¹⁻¹ * a⁻¹ = (x⁻¹ * (x * a * x⁻¹ * a⁻¹) * x⁻¹⁻¹)⁻¹ := by group
    rw [e]
    exact inv_mem ((Subgroup.mem_normalizer_iff.1 (hB (M.inv_mem hxM)) _).1 (hx a ha))

omit [Finite G] in
theorem secKer_normal {A B : Subgroup G} (hA : M ≤ Subgroup.normalizer (A : Set G))
    (hB : M ≤ Subgroup.normalizer (B : Set G)) :
    ((secKer M A B hB).subgroupOf M).Normal := by
  refine ⟨fun x hx m => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  obtain ⟨hxM, hx⟩ := hx
  obtain ⟨y, hyM⟩ := x
  obtain ⟨g, hgM⟩ := m
  simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hx hxM ⊢
  refine ⟨M.mul_mem (M.mul_mem hgM hyM) (M.inv_mem hgM), fun a ha => ?_⟩
  have ha' : g⁻¹ * a * g⁻¹⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hA (M.inv_mem hgM)) a).1 ha
  have e : g * y * g⁻¹ * a * (g * y * g⁻¹)⁻¹ * a⁻¹ =
      g * (y * (g⁻¹ * a * g⁻¹⁻¹) * y⁻¹ * (g⁻¹ * a * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
  rw [e]
  exact (Subgroup.mem_normalizer_iff.1 (hB hgM) _).1 (hx _ ha')

theorem actsLike_of_mem_centralizer (h : PUHyp M T L) {t l : G} (htM : t ∈ M) (hlL : l ∈ L)
    (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1) (hl2 : ∃ e : ℕ, l ^ 2 ^ e = 1)
    (hc : t * l⁻¹ ∈ Subgroup.centralizer (Uq M T L : Set G)) : ActsLike M t l := by
  intro A B hA hB hBA hAQ hAQB a ha
  set K := secKer M A B hB with hK
  have hlM : l ∈ M := h.L_le hlL
  set c := t * l⁻¹ with hcdef
  have hcM : c ∈ M := M.mul_mem htM (M.inv_mem hlM)
  have hQK : ∀ x ∈ pCoreOf 2 M, x ∈ K := by
    intro x hx
    refine ⟨pCoreOf_le' M hx, fun a ha => ?_⟩
    have := hAQB (Subgroup.commutator_mem_commutator ha hx)
    have e : x * a * x⁻¹ * a⁻¹ = ⁅a, x⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact inv_mem this
  set N := M ⊓ Subgroup.centralizer (Uq M T L : Set G) with hN
  have hNn : M ≤ Subgroup.normalizer (N : Set G) :=
    le_normalizer_inf (fun _ hm => (Subgroup.mem_normalizer_iff.2 fun x =>
      ⟨fun hx => M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm), fun hx => by
        simpa [mul_assoc] using M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm⟩))
      (le_normalizer_centralizer (le_normalizer_Uq h.le_normalizer))
  have hLN : ¬ L ≤ N := by
    intro hL
    apply h.Uq_ne_bot
    rw [← h.commutator_uq, eq_bot_iff, Subgroup.commutator_le]
    intro u hu l hl
    rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_centralizer_iff.1 (hL hl).2 u hu)
  have hcN : c ∈ N := ⟨hcM, hc⟩
  have hNL : ⁅N, L⁆ ≤ pCoreOf 2 M := h.commutator_le_pCoreOf_M inf_le_left hNn hLN
  have hKn := secKer_normal hA hB
  set π := QuotientGroup.mk' ((secKer M A B hB).subgroupOf M) with hπ
  have hπ1 : ∀ x : ↥M, π x = 1 ↔ (x : G) ∈ secKer M A B hB := fun x => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set c' : ↥M := ⟨c, hcM⟩
  set l' : ↥M := ⟨l, hlM⟩
  have hcomm : Commute (π c') (π l') := by
    have h1 : π (c' * l' * c'⁻¹ * l'⁻¹) = 1 := by
      rw [hπ1]
      exact hQK _ (hNL (Subgroup.commutator_mem_commutator hcN hlL))
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact commutatorElement_eq_one_iff_mul_comm.1 (by rw [commutatorElement_def]; exact h1)
  obtain ⟨e₁, he₁⟩ := ht2
  obtain ⟨e₂, he₂⟩ := hl2
  have ht' : (⟨t, htM⟩ : ↥M) = c' * l' := Subtype.ext (by simp [c', l', hcdef])
  have hce : π c' ^ 2 ^ (e₁ + e₂) = 1 := by
    have h1 : π ⟨t, htM⟩ ^ 2 ^ (e₁ + e₂) = 1 := by
      rw [← map_pow]
      have : (⟨t, htM⟩ : ↥M) ^ 2 ^ (e₁ + e₂) = 1 := Subtype.ext (by
        simp only [Subgroup.coe_pow, Subgroup.coe_one]
        rw [pow_add, pow_mul, he₁, one_pow])
      rw [this, map_one]
    have h2 : π l' ^ 2 ^ (e₁ + e₂) = 1 := by
      rw [← map_pow]
      have : l' ^ 2 ^ (e₁ + e₂) = 1 := Subtype.ext (by
        simp only [l', Subgroup.coe_pow, Subgroup.coe_one]
        rw [pow_add, mul_comm, pow_mul, he₂, one_pow])
      rw [this, map_one]
    rw [ht', map_mul, hcomm.mul_pow, h2, mul_one] at h1
    exact h1
  obtain ⟨a₀, m₀, hm₀, hord⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos c').ne'
  have hcm : π c' ^ m₀ = 1 := by
    rw [← map_pow, hπ1]
    apply hQK
    have hcoe : ((c' ^ m₀ : ↥M) : G) = c ^ m₀ := by simp [c']
    rw [hcoe]
    refine h.mem_pCoreOf_of_rel hNn hLN (M.pow_mem hcM m₀) ⟨a₀, ?_⟩ fun l hl => ?_
    · have := pow_orderOf_eq_one c'
      rw [hord, mul_comm, pow_mul] at this
      have := congrArg Subtype.val this
      simpa [c'] using this
    · have hdN : (c : G) ^ m₀ ∈ N := N.pow_mem hcN m₀
      have e : ⁅(c : G) ^ m₀, l⁆ = (c : G) ^ m₀ * (l * ((c : G) ^ m₀)⁻¹ * l⁻¹) := by
        simp only [commutatorElement_def]
        group
      rw [e]
      exact N.mul_mem hdN ((Subgroup.mem_normalizer_iff.1 (hNn (h.L_le hl)) _).1 (N.inv_mem hdN))
  have hc1 : π c' = 1 := by
    have hg : Nat.gcd m₀ (2 ^ (e₁ + e₂)) = 1 := Nat.Coprime.pow_right _ hm₀.coprime_two_right
    have := pow_gcd_eq_one.2 ⟨hcm, hce⟩
    rwa [hg, pow_one] at this
  have hcK : c ∈ secKer M A B hB := (hπ1 c').1 hc1
  have hla : l * a * l⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.1 (hA hlM) a).1 ha
  have e : t * a * t⁻¹ * (l * a * l⁻¹)⁻¹ = c * (l * a * l⁻¹) * c⁻¹ * (l * a * l⁻¹)⁻¹ := by
    simp only [hcdef]
    group
  rw [e]
  exact hcK.2 _ hla

end Sections

end CFSG.Quasithin.MS93.S36SP
