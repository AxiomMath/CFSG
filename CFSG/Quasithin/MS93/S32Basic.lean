module

public import CFSG.Quasithin.MS93.S32Cent
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

variable {G : Type} [Group G]

section RelCent

@[expose] def relCent (M L D : Subgroup G) (hDn : M ≤ Subgroup.normalizer (D : Set G))
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) : Subgroup G where
  carrier := {m | m ∈ M ∧ ∀ l ∈ L, ⁅m, l⁆ ∈ D}
  one_mem' := ⟨M.one_mem, fun l _ => by simp [D.one_mem]⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.mul_mem ha hb, fun l hl => ?_⟩
    have e : ⁅a * b, l⁆ = a * ⁅b, l⁆ * a⁻¹ * ⁅a, l⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact D.mul_mem ((Subgroup.mem_normalizer_iff.mp (hDn ha) _).mp (hb' l hl)) (ha' l hl)
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨M.inv_mem ha, fun l hl => ?_⟩
    have h1 : ⁅a, a⁻¹ * l * a⁆ ∈ D := by
      refine ha' _ ?_
      have := (Subgroup.mem_normalizer_iff.mp (hLn (M.inv_mem ha)) l).mp hl
      simpa using this
    have e : ⁅a⁻¹, l⁆ = ⁅a, a⁻¹ * l * a⁆⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact D.inv_mem h1

variable {M L D : Subgroup G} {hDn : M ≤ Subgroup.normalizer (D : Set G)}
  {hLn : M ≤ Subgroup.normalizer (L : Set G)}

theorem relCent_le : relCent M L D hDn hLn ≤ M := fun _ h => h.1

theorem le_normalizer_relCent :
    M ≤ Subgroup.normalizer (relCent M L D hDn hLn : Set G) := by
  have key : ∀ g ∈ M, ∀ x ∈ relCent M L D hDn hLn, g * x * g⁻¹ ∈ relCent M L D hDn hLn := by
    rintro g hg x ⟨hx, hx'⟩
    refine ⟨M.mul_mem (M.mul_mem hg hx) (M.inv_mem hg), fun l hl => ?_⟩
    have hl' : g⁻¹ * l * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.mp (hLn (M.inv_mem hg)) l).mp hl
      simpa using this
    have e : ⁅g * x * g⁻¹, l⁆ = g * ⁅x, g⁻¹ * l * g⁆ * g⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact (Subgroup.mem_normalizer_iff.mp (hDn hg) _).mp (hx' _ hl')
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (M.inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem not_le_relCent (hperf : ⁅L, L⁆ = L) (hLD : ¬ L ≤ D) :
    ¬ L ≤ relCent M L D hDn hLn := by
  intro hL
  apply hLD
  rw [← hperf, Subgroup.commutator_le]
  intro x hx y hy
  exact (hL hx).2 y hy

end RelCent

section TwoElt

theorem exists_pow_isTwoElt {H : Type*} [Group H] [Finite G] (φ : G →* H) (g : G) {e : ℕ}
    (he : φ g ^ 2 ^ e = 1) : ∃ k : ℕ, φ (g ^ k) = φ g ∧ ∃ f : ℕ, (g ^ k) ^ 2 ^ f = 1 := by
  obtain ⟨a, b, hb, hab⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos g).ne'
  have hcop : Nat.Coprime b (2 ^ (a + e + 1)) :=
    Nat.Coprime.pow_right _ (Nat.coprime_two_right.mpr hb)
  obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop
    (Nat.one_lt_two_pow (by omega : a + e + 1 ≠ 0))
  refine ⟨b * u, ?_, a, ?_⟩
  · have hq := Nat.div_add_mod (b * u) (2 ^ (a + e + 1))
    rw [hu] at hq
    rw [map_pow, ← hq, pow_add, pow_one, pow_mul,
      show 2 ^ (a + e + 1) = 2 ^ e * 2 ^ (a + 1) by ring, pow_mul, he, one_pow, one_pow,
      one_mul]
  · rw [← pow_mul, show b * u * 2 ^ a = (2 ^ a * b) * u by ring, pow_mul, ← hab,
      pow_orderOf_eq_one, one_pow]

end TwoElt

section CoreTwo

variable [Finite G]

omit [Finite G] in
theorem exists_pow_mem_of_eq_sup {M L T : Subgroup G} (hLM : L ≤ M)
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) (hMLT : M = L ⊔ T) (hT : IsPGroup 2 T) {m : G}
    (hm : m ∈ M) : ∃ e : ℕ, m ^ 2 ^ e ∈ L := by
  have hTM : T ≤ M := hMLT ▸ le_sup_right
  set L' : Subgroup ↥M := L.subgroupOf M
  have hL' : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hLn
  have hsup : L' ⊔ T.subgroupOf M = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hLM hTM, ← hMLT, Subgroup.subgroupOf_self]
  have hmem : (⟨m, hm⟩ : ↥M) ∈ L' ⊔ T.subgroupOf M := by rw [hsup]; exact Subgroup.mem_top _
  obtain ⟨l, hl, t, ht, hlt⟩ := Subgroup.mem_sup_of_normal_left.mp hmem
  obtain ⟨e, he⟩ := hT ⟨(t : G), ht⟩
  refine ⟨e, ?_⟩
  have hq : (QuotientGroup.mk (⟨m, hm⟩ : ↥M) : ↥M ⧸ L') = QuotientGroup.mk t := by
    rw [← hlt, QuotientGroup.mk_mul, (QuotientGroup.eq_one_iff l).mpr hl, one_mul]
  have h1 : (QuotientGroup.mk ((⟨m, hm⟩ : ↥M) ^ 2 ^ e) : ↥M ⧸ L') = 1 := by
    rw [QuotientGroup.mk_pow, hq, ← QuotientGroup.mk_pow]
    have ht' : t ^ 2 ^ e = 1 := Subtype.ext (by simpa using congrArg Subtype.val he)
    rw [ht', QuotientGroup.mk_one]
  rw [QuotientGroup.eq_one_iff] at h1
  simpa [L', Subgroup.mem_subgroupOf] using h1

theorem sup_sylow_eq_top {M L T : Subgroup G} (hLM : L ≤ M)
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) (hMLT : M = L ⊔ T) (hT : IsPGroup 2 T)
    (S : Sylow 2 ↥M) : L.subgroupOf M ⊔ (S : Subgroup ↥M) = ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hodd : ¬ 2 ∣ (S : Subgroup ↥M).index := S.not_dvd_index
  set L' : Subgroup ↥M := L.subgroupOf M
  have hL' : L'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).2 hLn
  have hp : IsPGroup 2 (↥M ⧸ L') := by
    intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨e, he⟩ := exists_pow_mem_of_eq_sup hLM hLn hMLT hT m.2
    refine ⟨e, ?_⟩
    rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff]
    simpa [L', Subgroup.mem_subgroupOf] using he
  obtain ⟨n, hn⟩ := hp.exists_card_eq
  have h1 : (L' ⊔ (S : Subgroup ↥M)).index ∣ (S : Subgroup ↥M).index :=
    Subgroup.index_dvd_of_le le_sup_right
  have h2 : (L' ⊔ (S : Subgroup ↥M)).index ∣ 2 ^ n := by
    rw [← hn, ← Subgroup.index]
    exact Subgroup.index_dvd_of_le le_sup_left
  rw [← Subgroup.index_eq_one]
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  rcases k with _ | k
  · simpa using hk
  · exfalso
    apply hodd
    rw [hk, pow_succ] at h1
    exact (Dvd.intro_left _ rfl).trans h1

theorem mem_pCoreOf_of_commutator_mem {M L T : Subgroup G} (hLM : L ≤ M)
    (hLn : M ≤ Subgroup.normalizer (L : Set G)) (hMLT : M = L ⊔ T) (hT : IsPGroup 2 T)
    {t : G} (htM : t ∈ M) (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1)
    (htL : ∀ l ∈ L, ⁅t, l⁆ ∈ pCoreOf 2 M) : t ∈ pCoreOf 2 M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 M with hQ
  have hQn : M ≤ Subgroup.normalizer (Q : Set G) := le_normalizer_pCoreOf M
  set C₀ := relCent M L Q hQn hLn with hC₀
  have htp : IsPGroup 2 (Subgroup.zpowers (⟨t, htM⟩ : ↥M)) := by
    obtain ⟨e, he⟩ := ht2
    rintro ⟨y, hy⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    refine ⟨e, Subtype.ext (Subtype.ext ?_)⟩
    simp only [SubgroupClass.coe_pow, SubgroupClass.coe_zpow, OneMemClass.coe_one]
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, he, one_zpow]
  obtain ⟨S, hS⟩ := htp.exists_le_sylow
  set S' : Subgroup G := (S : Subgroup ↥M).map M.subtype with hS'
  have hS'M : S' ≤ M := Subgroup.map_subtype_le _
  have hS'2 : IsPGroup 2 S' := (S.isPGroup').map M.subtype
  have hQS : Q ≤ S' := by
    have hQ' : (Q.subgroupOf M).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer (pCoreOf_le' M)).2 hQn
    have hQ2 : IsPGroup 2 (Q.subgroupOf M) :=
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M).of_equiv
        (Subgroup.subgroupOfEquivOfLe (pCoreOf_le' M)).symm
    have := hQ2.le_sylow_of_normal S
    intro q hq
    exact ⟨⟨q, pCoreOf_le' M hq⟩, this (Subgroup.mem_subgroupOf.mpr hq), rfl⟩
  have htS' : t ∈ S' := ⟨⟨t, htM⟩, hS (Subgroup.mem_zpowers _), rfl⟩
  set P := S' ⊓ C₀ with hP
  have hC₀n : M ≤ Subgroup.normalizer (C₀ : Set G) := le_normalizer_relCent
  have hSn : S' ≤ Subgroup.normalizer (P : Set G) :=
    le_normalizer_inf Subgroup.le_normalizer (hS'M.trans hC₀n)
  have hLP : L ≤ Subgroup.normalizer (P : Set G) := by
    have key : ∀ l ∈ L, ∀ p ∈ P, l * p * l⁻¹ ∈ P := by
      intro l hl p hp
      have hc : ⁅p, l⁆ ∈ Q := hp.2.2 l hl
      have e : l * p * l⁻¹ = ⁅p, l⁆⁻¹ * p := by
        simp only [commutatorElement_def]
        group
      refine ⟨?_, (Subgroup.mem_normalizer_iff.mp (hC₀n (hLM hl)) p).mp hp.2⟩
      rw [e]
      exact S'.mul_mem (hQS (Q.inv_mem hc)) hp.1
    intro l hl
    rw [Subgroup.mem_normalizer_iff]
    intro p
    refine ⟨key l hl p, fun hp => ?_⟩
    have := key l⁻¹ (L.inv_mem hl) _ hp
    simpa [mul_assoc] using this
  have hMS : M = L ⊔ S' := by
    have h := sup_sylow_eq_top hLM hLn hMLT hT S
    refine le_antisymm ?_ (sup_le hLM hS'M)
    intro m hm
    have hm' : (⟨m, hm⟩ : ↥M) ∈ L.subgroupOf M ⊔ (S : Subgroup ↥M) := by
      rw [h]; exact Subgroup.mem_top _
    have := Subgroup.map_mono (f := M.subtype) (le_of_eq (rfl : L.subgroupOf M ⊔
      (S : Subgroup ↥M) = _)) (Subgroup.mem_map_of_mem M.subtype hm')
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hLM] at this
    exact this
  have hPn : M ≤ Subgroup.normalizer (P : Set G) := hMS.le.trans (sup_le hLP hSn)
  have hPQ : P ≤ Q := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
    (inf_le_left.trans hS'M) hPn (hS'2.to_le inf_le_left)
  exact hPQ ⟨htS', htM, htL⟩

variable {M T L : Subgroup G}

theorem PUHyp.mem_pCoreOf_of_rel (h : PUHyp M T L) {D : Subgroup G}
    (hDn : M ≤ Subgroup.normalizer (D : Set G)) (hLD : ¬ L ≤ D) {t : G} (htM : t ∈ M)
    (ht2 : ∃ e : ℕ, t ^ 2 ^ e = 1) (htL : ∀ l ∈ L, ⁅t, l⁆ ∈ D) : t ∈ pCoreOf 2 M := by
  set N := relCent M L D hDn h.le_normalizer
  have hcomm : ⁅N, L⁆ ≤ pCoreOf 2 M :=
    h.commutator_le_pCoreOf_M relCent_le le_normalizer_relCent
      (not_le_relCent h.perfect hLD)
  exact mem_pCoreOf_of_commutator_mem h.L_le h.le_normalizer h.eq_sup h.isPGroup htM ht2
    fun l hl => hcomm (Subgroup.commutator_mem_commutator ⟨htM, htL⟩ hl)

theorem PUHyp.exists_pow_mem_L (h : PUHyp M T L) {m : G} (hm : m ∈ M) :
    ∃ e : ℕ, m ^ 2 ^ e ∈ L :=
  exists_pow_mem_of_eq_sup h.L_le h.le_normalizer h.eq_sup h.isPGroup hm

end CoreTwo

section Objects

variable [Finite G] {M T L : Subgroup G}

theorem PUHyp.Uq_comm (h : PUHyp M T L) : ⁅Uq M T L, L⁆ = Uq M T L :=
  (commutator_eq_commutator_commutator (Z0q_le M T) h.L_le (le_normalizer_Z0q M T)
    h.le_normalizer h.perfect).symm

theorem PUHyp.Uq_ne_bot (h : PUHyp M T L) : Uq M T L ≠ ⊥ := by
  intro hU
  apply h.not_le_centralizer_Z0q
  rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
  exact hU

theorem PUHyp.not_le_centralizer_of_Uq_le (h : PUHyp M T L) {W : Subgroup G}
    (hUW : Uq M T L ≤ W) : ¬ L ≤ Subgroup.centralizer (W : Set G) := by
  intro hL
  apply h.Uq_ne_bot
  rw [← h.Uq_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
  exact Subgroup.le_centralizer_iff.mp (hL.trans (Subgroup.centralizer_le hUW))

theorem PUHyp.isElemAbelian_Xq (_h : PUHyp M T L) : IsElemAbelian 2 (Xq M) := by
  have hZ := PU.omegaOneCenterOf_le_centerOf (pCoreOf 2 M)
  refine B2F.isElemAbelian_closure (fun a ha b hb => ?_) (fun a ha => ha.2)
  exact Subgroup.mem_centralizer_iff.mp hb.1.2 a ha.1.1

theorem PUHyp.isElemAbelian_Z0q (h : PUHyp M T L) : IsElemAbelian 2 (Z0q M T) :=
  isElemAbelian_of_le h.isElemAbelian_Xq h.Z0q_le_Xq

theorem PUHyp.isElemAbelian_Uq (h : PUHyp M T L) : IsElemAbelian 2 (Uq M T L) :=
  isElemAbelian_of_le h.isElemAbelian_Xq h.Uq_le_Xq

theorem PUHyp.omegaOneCenterOf_eq (h : PUHyp M T L) :
    omegaOneCenterOf T = Xq M ⊓ Subgroup.centralizer (T : Set G) := by
  apply le_antisymm
  · refine le_inf ?_ ?_
    · have h1 := PU.omegaOneCenterOf_le_pCoreOf h.le h.pCore_le h.charTwo
      unfold Xq omegaOneCenterOf omegaOneOf
      rw [Subgroup.closure_le]
      rintro x ⟨⟨hxT, hxC⟩, hx2⟩
      refine Subgroup.subset_closure ⟨⟨h1 (Subgroup.subset_closure ⟨⟨hxT, hxC⟩, hx2⟩), ?_⟩, hx2⟩
      exact Subgroup.centralizer_le h.pCore_le hxC
    · exact (PU.omegaOneCenterOf_le_centerOf T).trans inf_le_right
  · rintro x ⟨hxX, hxC⟩
    have hxQ : x ∈ pCoreOf 2 M := Xq_le_pCoreOf M hxX
    have hxT : x ∈ T := h.pCore_le hxQ
    have hx2 : x ^ 2 = 1 := h.isElemAbelian_Xq.2 x hxX
    exact Subgroup.subset_closure ⟨⟨hxT, Subgroup.centralizer_le (fun _ h => h) hxC⟩, hx2⟩

theorem PUHyp.Z0q_eq_sup (h : PUHyp M T L) :
    Z0q M T = omegaOneCenterOf T ⊔ Uq M T L := by
  set A₀ := omegaOneCenterOf T
  have hA₀Z : A₀ ≤ Z0q M T := omegaOneCenterOf_le_Z0q M T h.le
  refine le_antisymm ?_ (sup_le hA₀Z (Uq_le_Z0q h.L_le))
  have hUn : M ≤ Subgroup.normalizer (Uq M T L : Set G) := le_normalizer_Uq h.le_normalizer
  have key : ∀ g ∈ M, (∀ a ∈ A₀, g * a * g⁻¹ ∈ A₀ ⊔ Uq M T L) →
      ∀ x ∈ A₀ ⊔ Uq M T L, g * x * g⁻¹ ∈ A₀ ⊔ Uq M T L := by
    intro g hg hA x hx
    have hle : A₀ ⊔ Uq M T L ≤ (A₀ ⊔ Uq M T L).comap (MulAut.conj g).toMonoidHom := by
      refine sup_le (fun a ha => hA a ha) (fun u hu => ?_)
      exact Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp (hUn hg) u).mp hu)
    exact hle hx
  have hL : ∀ l ∈ L, ∀ a ∈ A₀, l * a * l⁻¹ ∈ A₀ ⊔ Uq M T L := by
    intro l hl a ha
    have hc : ⁅l, a⁆ ∈ Uq M T L := by
      rw [Uq, Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hl (hA₀Z ha)
    have e : l * a * l⁻¹ = ⁅l, a⁆ * a := by
      simp only [commutatorElement_def]
      group
    rw [e, sup_comm]
    exact Subgroup.mul_mem_sup hc ha
  have hT : ∀ t ∈ T, ∀ a ∈ A₀, t * a * t⁻¹ ∈ A₀ ⊔ Uq M T L := by
    intro t ht a ha
    have hcom := Subgroup.mem_centralizer_iff.mp
      ((PU.omegaOneCenterOf_le_centerOf T ha).2) t ht
    rw [hcom, mul_inv_cancel_right]
    exact Subgroup.mem_sup_left ha
  have hnorm : ∀ S : Subgroup G, S ≤ M → (∀ g ∈ S, ∀ a ∈ A₀, g * a * g⁻¹ ∈ A₀ ⊔ Uq M T L) →
      S ≤ Subgroup.normalizer ((A₀ ⊔ Uq M T L : Subgroup G) : Set G) := by
    intro S hSM hS g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨key g (hSM hg) (hS g hg) x, fun hx => ?_⟩
    have := key g⁻¹ (M.inv_mem (hSM hg)) (hS g⁻¹ (S.inv_mem hg)) _ hx
    simpa [mul_assoc] using this
  have hn : M ≤ Subgroup.normalizer ((A₀ ⊔ Uq M T L : Subgroup G) : Set G) :=
    h.eq_sup.le.trans (sup_le (hnorm L h.L_le hL) (hnorm T h.le hT))
  have hNM : A₀ ⊔ Uq M T L ≤ M := sup_le (hA₀Z.trans (Z0q_le M T)) (Uq_le h.L_le)
  exact normalClosureIn_le_of hNM ((Subgroup.normal_subgroupOf_iff_le_normalizer hNM).2 hn)
    (inf_le_left.trans le_sup_left)

end Objects

end CFSG.Quasithin.MS93
