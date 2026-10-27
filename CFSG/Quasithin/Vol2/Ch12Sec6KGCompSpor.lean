module

public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompL3Small
public import CFSG.Quasithin.Vol2.Ch12Sec6KGCompHatA6
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Sporadic

public section

namespace CFSG.Quasithin.H13.S126C

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

@[expose] def NoTwoCentralNine (M : Type) [Group M] : Prop :=
  ∀ t : M, orderOf t = 2 → ¬ 2 ∣ (Subgroup.centralizer ({t} : Set M)).index →
    ¬ 9 ∣ Nat.card (Subgroup.centralizer ({t} : Set M))

section Transport

variable {M M' : Type} [Group M] [Group M']

theorem center_eq_bot_of_mulEquiv (e : M ≃* M') (h : Subgroup.center M' = ⊥) :
    Subgroup.center M = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  have hz' : e z ∈ Subgroup.center M' := Subgroup.mem_center_iff.mpr fun g => by
    obtain ⟨x, rfl⟩ := e.surjective g
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz x]
  rw [h, Subgroup.mem_bot] at hz'
  rw [Subgroup.mem_bot]
  exact e.injective (hz'.trans (map_one e).symm)

theorem exists_elemAbelian_nine_of_mulEquiv (e : M ≃* M')
    (h : ∃ E : Subgroup M', IsElemAbelian 3 E ∧ Nat.card E = 9) :
    ∃ E : Subgroup M, IsElemAbelian 3 E ∧ Nat.card E = 9 := by
  obtain ⟨E, hE, h9⟩ := h
  exact ⟨E.map e.symm.toMonoidHom, isElemAbelian_map _ hE,
    by rw [Subgroup.card_map_of_injective e.symm.injective, h9]⟩

theorem card_map_mulAut_congr (e : M ≃* M') (Pb : Subgroup (MulAut M)) :
    Nat.card (Pb.map (MulAut.congr e).toMonoidHom) = Nat.card Pb :=
  Subgroup.card_map_of_injective (MulAut.congr e).injective

end Transport

section Generic

theorem card_centralizer_subtype_inf {G : Type*} [Group G] (H : Subgroup G) (t : H) :
    Nat.card (Subgroup.centralizer ({t} : Set H)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({(t : G)} : Set G)) := by
  have hmap : (Subgroup.centralizer ({t} : Set H)).map H.subtype =
      H ⊓ Subgroup.centralizer ({(t : G)} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      Subgroup.coe_subtype]
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, by simpa using congrArg Subtype.val hy⟩
    · rintro ⟨hx, hxt⟩
      exact ⟨⟨x, hx⟩, Subtype.ext (by simpa using hxt), rfl⟩
  rw [← hmap, Subgroup.card_map_of_injective H.subtype_injective]

theorem card_inf_centralizer_conj {G : Type*} [Group G] (H : Subgroup G) {g : G} (hg : g ∈ H)
    (t : G) : Nat.card ↥(H ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G)) =
      Nat.card ↥(H ⊓ Subgroup.centralizer ({t} : Set G)) := by
  have hmap : (H ⊓ Subgroup.centralizer ({t} : Set G)).map (MulAut.conj g).toMonoidHom =
      H ⊓ Subgroup.centralizer ({g * t * g⁻¹} : Set G) := by
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff,
      MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, ⟨hy, hyt⟩, rfl⟩
      refine ⟨H.mul_mem (H.mul_mem hg hy) (H.inv_mem hg), ?_⟩
      calc g * y * g⁻¹ * (g * t * g⁻¹) = g * (y * t) * g⁻¹ := by group
        _ = g * (t * y) * g⁻¹ := by rw [hyt]
        _ = g * t * g⁻¹ * (g * y * g⁻¹) := by group
    · rintro ⟨hx, hxt⟩
      refine ⟨g⁻¹ * x * g, ⟨H.mul_mem (H.mul_mem (H.inv_mem hg) hx) hg, ?_⟩, by group⟩
      calc g⁻¹ * x * g * t = g⁻¹ * (x * (g * t * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * t * g⁻¹) * x) * g := by rw [hxt]
        _ = t * (g⁻¹ * x * g) := by group
  rw [← hmap, Subgroup.card_map_of_injective (f := (MulAut.conj g).toMonoidHom)
    (MulAut.conj g).injective]

theorem isElemAbelian_closure_pair {G : Type*} [Group G] {a b : G} (ha : a ^ 3 = 1)
    (hb : b ^ 3 = 1) (hab : Commute a b) :
    IsElemAbelian 3 (Subgroup.closure ({a, b} : Set G)) := by
  have hpw : ({a, b} : Set G).Pairwise Commute := by
    intro x hx y hy _
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Commute.refl _
    · exact hab
    · exact hab.symm
    · exact Commute.refl _
  have hc := Subgroup.isMulCommutative_closure hpw
  refine ⟨hc, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ha
    · exact hb
  | one => exact one_pow 3
  | mul x y hx hy ihx ihy =>
    have hxy : Commute x y := congrArg Subtype.val (hc.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
    rw [hxy.mul_pow, ihx, ihy, one_mul]
  | inv x hx ihx => rw [inv_pow, ihx, inv_one]

theorem center_eq_bot_of_simple_of_not_prime {M : Type*} [Group M] [IsSimpleGroup M]
    (hM : ¬ (Nat.card M).Prime) : Subgroup.center M = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center M) with h | h
  · exact h
  · exfalso
    have : IsMulCommutative M :=
      ⟨⟨fun a b => (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b : b ∈ _) a)⟩⟩
    exact hM (Group.is_simple_iff_prime_card.mp inferInstance)

variable {M : Type} [Group M]

theorem not_three_dvd_card_outer_of_le_two [Finite M] (h : Nat.card (Outer M) ≤ 2) :
    ¬ 3 ∣ Nat.card (Outer M) := by
  have hO : 0 < Nat.card (Outer M) := Nat.card_pos
  intro h3
  have := Nat.le_of_dvd hO h3
  omega

theorem NoTwoCentralNine.of_cards {N : ℕ} (hN : Nat.card M = N) (cs : List ℕ)
    (hcs : ∀ t : M, orderOf t = 2 → Nat.card (Subgroup.centralizer ({t} : Set M)) ∈ cs)
    (hchk : ∀ c ∈ cs, ∀ i : ℕ, c * i = N → ¬ 2 ∣ i → ¬ 9 ∣ c) : NoTwoCentralNine M := by
  intro t ht hi h9
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({t} : Set M))
  rw [hN] at hmul
  exact hchk _ (hcs t ht) _ hmul hi h9

theorem noTwoCentralNine_of_reps {G : Type} [Group G] {P R : Subgroup G} (hPR : P ≤ R) {N : ℕ}
    (hN : Nat.card P = N) {α : Type*} (rows : List α) (f : α → G) (c : α → ℕ)
    (hcov : ∀ t ∈ R, orderOf t = 2 → ∃ r ∈ rows, ∃ g ∈ P, t = g * f r * g⁻¹)
    (hcard : ∀ r ∈ rows, Nat.card ↥(P ⊓ Subgroup.centralizer ({f r} : Set G)) = c r)
    (hchk : ∀ r ∈ rows, ∀ i : ℕ, c r * i = N → ¬ 2 ∣ i → ¬ 9 ∣ c r) :
    NoTwoCentralNine ↥P := by
  intro t ht hi h9
  obtain ⟨r, hr, g, hg, htr⟩ := hcov t (hPR t.2) (by rw [Subgroup.orderOf_coe]; exact ht)
  have hC : Nat.card (Subgroup.centralizer ({t} : Set ↥P)) = c r := by
    rw [card_centralizer_subtype_inf, htr, card_inf_centralizer_conj P hg, hcard r hr]
  have hmul := Subgroup.card_mul_index (Subgroup.centralizer ({t} : Set ↥P))
  rw [hC, hN] at hmul
  exact hchk r hr _ hmul hi (hC ▸ h9)

theorem not_three_dvd_card_outer_of_le [Finite M] (hZ : Subgroup.center M = ⊥)
    (h : Nat.card (MulAut M) ≤ 2 * Nat.card M) : ¬ 3 ∣ Nat.card (Outer M) := by
  have hInn : Nat.card (inner M) = Nat.card M :=
    (Nat.card_congr (MonoidHom.ofInjective (conj_injective_of_center_eq_bot hZ)).toEquiv).symm
  have hcard := (inner M).card_eq_card_quotient_mul_card_subgroup
  rw [hInn] at hcard
  have hpos : 0 < Nat.card M := Nat.card_pos
  have hO : 0 < Nat.card (Outer M) := Nat.card_pos
  have hle : Nat.card (Outer M) * Nat.card M ≤ 2 * Nat.card M := by
    rw [← hcard]
    exact h
  have h2 := Nat.le_of_mul_le_mul_right hle hpos
  intro h3
  have := Nat.le_of_dvd hO h3
  omega

theorem mem_range_conj_of_pow_three (hout : ¬ 3 ∣ Nat.card (Outer M)) (α : MulAut M)
    (hα : α ^ 3 = 1) : α ∈ (MulAut.conj : M →* MulAut M).range := by
  set o : Outer M := QuotientGroup.mk α with ho
  have hop : o ^ 3 = 1 := by rw [ho, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  rcases (Nat.dvd_prime Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one hop) with h1 | h1
  · have hmem : α ∈ inner M :=
      (QuotientGroup.eq_one_iff (N := inner M) α).1 (orderOf_eq_one_iff.1 h1)
    exact hmem
  · exact absurd (h1 ▸ orderOf_dvd_natCard o) hout

variable {ν : MulAut M} {Lb Pb : Subgroup (MulAut M)}

theorem not_autConf_of_noTwoCentralNine [Finite M] (h : AutConf M ν Lb Pb)
    (h9 : Nat.card Pb = 9) (hZ : Subgroup.center M = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer M))
    (hν : ∃ l : M, ∀ x, ν x = l⁻¹ * x * l) (hnc : NoTwoCentralNine M) : False := by
  obtain ⟨l, hl⟩ := hν
  obtain ⟨hl2, hfix⟩ := h.involution_of_inner hZ hl
  have hinj := conj_injective_of_center_eq_bot hZ
  have hPin : Pb ≤ (MulAut.conj : M →* MulAut M).range := fun π hπ =>
    mem_range_conj_of_pow_three hout π (h.elem.2 π hπ)
  have hE9 : Nat.card (Pb.comap (MulAut.conj : M →* MulAut M)) = 9 := by
    rw [← Subgroup.card_map_of_injective hinj, Subgroup.map_comap_eq, inf_eq_right.mpr hPin, h9]
  have hEC : Pb.comap (MulAut.conj : M →* MulAut M) ≤ Subgroup.centralizer ({l} : Set M) :=
    fun e he => (hfix e).mp (h.fix_of_mem_innerPart hZ (h.le he))
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨S, hS⟩ := h.exists_sylow_fixed
  have hSC : (S : Subgroup M) ≤ Subgroup.centralizer ({l} : Set M) := fun s hs =>
    (hfix s).mp (hS s hs)
  refine hnc l hl2 (fun h2 => S.not_dvd_index (h2.trans (Subgroup.index_dvd_of_le hSC))) ?_
  rw [← hE9]
  exact Subgroup.card_dvd_of_le hEC

end Generic

section Conf

variable {Q : Type} [Group Q] {K L P T : Subgroup Q} {v : Q}

theorem isInnerAut_of_sporadicAutInner (hQ : Vol2Native.SQTKHypCat Q)
    (hS : Ch1.SporadicAutInner) {s : TauCeti.SporadicName} (hs : Ch1.IsSQTKSporadicName s)
    (hs1 : s ≠ .J1) (e : ↥K ≃* CFSG.Blueprint.NativeSporadic.Carrier s) (β : MulAut ↥K)
    (hβ : ∀ x, β (β x) = x) (hP : ∃ S : Sylow 2 ↥K, ∀ t ∈ (S : Subgroup ↥K), β t = t) :
    ∃ l : ↥K, ∀ x, β x = l⁻¹ * x * l := by
  have := hQ.finite
  exact hS s hs hs1 ↥K ⟨e⟩ β hβ hP

theorem Conf12626.false_of_noTwoCentralNine (hQ : Vol2Native.SQTKHypCat Q)
    (h : Conf12626 K L P T v) {M : Type} [Group M] (e : ↥K ≃* M)
    (hZ : Subgroup.center M = ⊥) (hout : ¬ 3 ∣ Nat.card (Outer M))
    (hE : ∃ E : Subgroup M, IsElemAbelian 3 E ∧ Nat.card E = 9) (hnc : NoTwoCentralNine M)
    (hinn : ∀ β : MulAut ↥K, (∀ x, β (β x) = x) →
      (∃ S : Sylow 2 ↥K, ∀ t ∈ (S : Subgroup ↥K), β t = t) → ∃ l : ↥K, ∀ x, β x = l⁻¹ * x * l) :
    False := by
  have := hQ.finite
  have : Finite M := Finite.of_equiv _ e.toEquiv
  obtain ⟨E, hE3, hE9⟩ := hE
  have hA := h.autConf
  obtain ⟨l, hl⟩ := hinn h.nu (apply_apply_of_sq hA.sq) hA.exists_sylow_fixed
  refine not_autConf_of_noTwoCentralNine (hA.map e)
    (h.card_map_rhoP_eq_nine hQ e (fun z hz => by rwa [hZ, Subgroup.mem_bot] at hz) hE3 hE9) hZ
    hout ⟨e l, fun x => ?_⟩ hnc
  rw [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply, hl, map_mul, map_mul,
    map_inv, MulEquiv.apply_symm_apply]

end Conf

end CFSG.Quasithin.H13.S126C
