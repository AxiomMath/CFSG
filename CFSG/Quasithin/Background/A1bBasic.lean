module

public import CFSG.Quasithin.Background.TwoReduced
public import CFSG.Assembly.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PCore

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits

variable {G : Type*} [Group G]

@[expose] def IsSylowIn (p : ℕ) (P H : Subgroup G) : Prop :=
  P ≤ H ∧ IsPGroup p P ∧ ¬ p ∣ P.relIndex H

namespace IsSylowIn

variable {p : ℕ} {P H : Subgroup G}

theorem le (h : IsSylowIn p P H) : P ≤ H := h.1

theorem isPGroup (h : IsSylowIn p P H) : IsPGroup p P := h.2.1

theorem not_dvd_relIndex (h : IsSylowIn p P H) : ¬ p ∣ P.relIndex H := h.2.2

@[expose] noncomputable def toSylow [Fact p.Prime] (h : IsSylowIn p P H) : Sylow p H :=
  (h.isPGroup.of_equiv (Subgroup.subgroupOfEquivOfLe h.le).symm).toSylow h.not_dvd_relIndex

@[simp] theorem coe_toSylow [Fact p.Prime] (h : IsSylowIn p P H) :
    (h.toSylow : Subgroup H) = P.subgroupOf H := rfl

theorem le_of_normal [Fact p.Prime] (h : IsSylowIn p P H) {N : Subgroup G} (hNH : N ≤ H)
    (hN : (N.subgroupOf H).Normal) (hp : IsPGroup p N) : N ≤ P := by
  have hp' : IsPGroup p (N.subgroupOf H) :=
    hp.of_equiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have := hp'.le_sylow_of_normal h.toSylow
  intro x hx
  have hxH : x ∈ H := hNH hx
  have h1 : (⟨x, hxH⟩ : H) ∈ N.subgroupOf H := hx
  exact this h1

end IsSylowIn

theorem exists_isSylowIn_ge [Finite G] (p : ℕ) [Fact p.Prime] {H P : Subgroup G} (hPH : P ≤ H)
    (hP : IsPGroup p P) : ∃ S : Subgroup G, IsSylowIn p S H ∧ P ≤ S := by
  have hP' : IsPGroup p (P.subgroupOf H) := hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPH).symm
  obtain ⟨Q, hQ⟩ := hP'.exists_le_sylow
  have hQS : (Q : Subgroup H).map H.subtype ⊓ H = (Q : Subgroup H).map H.subtype :=
    inf_eq_left.2 (Subgroup.map_subtype_le _)
  have hsub : ((Q : Subgroup H).map H.subtype).subgroupOf H = (Q : Subgroup H) := by
    ext x
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.subtype_apply]
    constructor
    · rintro ⟨y, hy, hyx⟩
      have : y = x := Subtype.ext hyx
      rwa [← this]
    · intro hx
      exact ⟨x, hx, rfl⟩
  refine ⟨(Q : Subgroup H).map H.subtype, ⟨Subgroup.map_subtype_le _, Q.isPGroup'.map _, ?_⟩, ?_⟩
  · change ¬ p ∣ (((Q : Subgroup H).map H.subtype).subgroupOf H).index
    rw [hsub]
    exact Sylow.not_dvd_index Q
  · intro x hx
    refine ⟨⟨x, hPH hx⟩, hQ ?_, rfl⟩
    exact hx

@[expose] def opResidual (p : ℕ) (A : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ A ∧ (orderOf x).Coprime p}

theorem opResidual_le (p : ℕ) (A : Subgroup G) : opResidual p A ≤ A := by
  rw [opResidual, Subgroup.closure_le]
  exact fun x hx => hx.1

theorem mem_opResidual_of_coprime {p : ℕ} {A : Subgroup G} {x : G} (hx : x ∈ A)
    (hc : (orderOf x).Coprime p) : x ∈ opResidual p A :=
  Subgroup.subset_closure ⟨hx, hc⟩

theorem opResidual_normal (p : ℕ) (A : Subgroup G) : ((opResidual p A).subgroupOf A).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  have key : ∀ y ∈ opResidual p A, (g : G) * y * (g : G)⁻¹ ∈ opResidual p A := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem y hy =>
      refine mem_opResidual_of_coprime (A.mul_mem (A.mul_mem g.2 hy.1) (A.inv_mem g.2)) ?_
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact hy.2
    | one => simp
    | mul y z _ _ ihy ihz =>
      simpa [mul_assoc] using (opResidual p A).mul_mem ihy ihz
    | inv y _ ih =>
      simpa [mul_assoc] using (opResidual p A).inv_mem ih
  simpa [mul_assoc] using key _ hx

theorem exists_pow_mem_opResidual [Finite G] {p : ℕ} [hp : Fact p.Prime] {A : Subgroup G} {x : G}
    (hx : x ∈ A) : ∃ k : ℕ, x ^ p ^ k ∈ opResidual p A := by
  obtain ⟨k, m, hm, hdecomp⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x).ne' p hp.out.ne_one
  refine ⟨k, mem_opResidual_of_coprime (A.pow_mem hx _) ?_⟩
  rw [orderOf_pow_of_dvd (pow_ne_zero k hp.out.ne_zero) ⟨m, hdecomp⟩, hdecomp,
    Nat.mul_div_cancel_left _ (pow_pos hp.out.pos k)]
  exact ((Nat.Prime.coprime_iff_not_dvd hp.out).2 hm).symm

theorem opResidual_le_of_pow_mem {p : ℕ} {A N : Subgroup G}
    (h : ∀ x ∈ A, ∃ k : ℕ, x ^ p ^ k ∈ N) : opResidual p A ≤ N := by
  rw [opResidual, Subgroup.closure_le]
  rintro x ⟨hxA, hxc⟩
  obtain ⟨k, hk⟩ := h x hxA
  have hcop : (p ^ k).Coprime (orderOf x) := (Nat.Coprime.pow_right k hxc).symm
  obtain ⟨m, hm⟩ := exists_pow_eq_self_of_coprime hcop
  rw [← hm]
  exact N.pow_mem hk m

theorem IsSylowIn.card_eq [Finite G] {p : ℕ} [Fact p.Prime] {P H : Subgroup G}
    (h : IsSylowIn p P H) : Nat.card P = p ^ (Nat.card H).factorization p := by
  have h1 := Sylow.card_eq_multiplicity h.toSylow
  rw [IsSylowIn.coe_toSylow] at h1
  rw [← h1]
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv).symm

theorem isSylowIn_of_card_eq [Finite G] {p : ℕ} [hp : Fact p.Prime] {P H : Subgroup G}
    (hPH : P ≤ H) (hc : Nat.card P = p ^ (Nat.card H).factorization p) : IsSylowIn p P H := by
  refine ⟨hPH, IsPGroup.of_card hc, ?_⟩
  intro hdvd
  have h1 := Subgroup.relIndex_mul_card (H := P) (K := H)
  rw [inf_eq_left.2 hPH, hc] at h1
  have hHpos : Nat.card H ≠ 0 := Nat.card_pos.ne'
  have h2 : p ^ ((Nat.card H).factorization p + 1) ∣ Nat.card H := by
    have h3 : p ^ ((Nat.card H).factorization p + 1) ∣
        P.relIndex H * p ^ (Nat.card H).factorization p := by
      rw [pow_succ']
      exact mul_dvd_mul hdvd dvd_rfl
    exact h3.trans (dvd_of_eq h1)
  have := (hp.out.pow_dvd_iff_le_factorization hHpos).1 h2
  omega

theorem card_inf_normal_of_sylow {H : Type*} [Group H] [Finite H] {p : ℕ} [hp : Fact p.Prime]
    (Q N : Subgroup H) [N.Normal] (hQ : Nat.card Q = p ^ (Nat.card H).factorization p) :
    Nat.card (N ⊓ Q : Subgroup H) = p ^ (Nat.card N).factorization p := by
  set m := (Nat.card H).factorization p with hm
  set v := (Nat.card N).factorization p with hv
  have hr1 := Subgroup.relIndex_mul_card (H := N) (K := Q)
  have hr2 : N.relIndex (Q ⊔ N) = N.relIndex Q := Subgroup.relIndex_sup_right Q N
  have hr3 := Subgroup.relIndex_mul_card (H := N) (K := Q ⊔ N)
  rw [inf_eq_left.2 le_sup_right, hr2] at hr3
  rw [hQ] at hr1
  have hbp : IsPGroup p (N ⊓ Q : Subgroup H) :=
    (IsPGroup.of_card hQ).to_le (inf_le_right : N ⊓ Q ≤ Q)
  obtain ⟨e, he⟩ := (IsPGroup.iff_card).1 hbp
  have hrd : N.relIndex Q ∣ p ^ m := ⟨Nat.card (N ⊓ Q : Subgroup H), hr1.symm⟩
  obtain ⟨j, hj, hrj⟩ := (Nat.dvd_prime_pow hp.out).1 hrd
  rw [hrj, he, ← pow_add] at hr1
  have hje : j + e = m := Nat.pow_right_injective hp.out.two_le hr1
  have hdvdH : Nat.card (Q ⊔ N : Subgroup H) ∣ Nat.card H := Subgroup.card_subgroup_dvd_card _
  have hpv : p ^ v ∣ Nat.card N := (hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 le_rfl
  have hA : p ^ (j + v) ∣ Nat.card (Q ⊔ N : Subgroup H) := by
    rw [← hr3, hrj, pow_add]
    exact mul_dvd_mul_left _ hpv
  have h1' : j + v ≤ m :=
    (hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 (hA.trans hdvdH)
  have hbN : p ^ e ∣ Nat.card N := by
    rw [← he]
    exact Subgroup.card_dvd_of_le inf_le_left
  have h2' : e ≤ v := (hp.out.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hbN
  have : e = v := by omega
  rw [he, this]

theorem IsSylowIn.inf_normal [Finite G] {p : ℕ} [hp : Fact p.Prime] {P H : Subgroup G}
    (h : IsSylowIn p P H) {N : Subgroup G} (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) :
    IsSylowIn p (P ⊓ N) N := by
  have hcard := h.card_eq
  have hQ : Nat.card (P.subgroupOf H) = p ^ (Nat.card H).factorization p := by
    rw [← hcard]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe h.le).toEquiv
  have key := card_inf_normal_of_sylow (p := p) (P.subgroupOf H) (N.subgroupOf H) hQ
  refine isSylowIn_of_card_eq inf_le_right ?_
  have e1 : Nat.card (P ⊓ N : Subgroup G) =
      Nat.card ((N.subgroupOf H) ⊓ (P.subgroupOf H) : Subgroup H) := by
    have e0 : ((P ⊓ N).subgroupOf H) = (N.subgroupOf H) ⊓ (P.subgroupOf H) := by
      ext x
      simp [Subgroup.mem_subgroupOf, and_comm]
    rw [← e0]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans h.le)).toEquiv).symm
  have e2 : Nat.card (N.subgroupOf H) = Nat.card N :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hNH).toEquiv
  rw [e1, key, e2]

theorem exists_mul_eq_of_pow_mem [Finite G] {p : ℕ} [Fact p.Prime] {D N S : Subgroup G}
    (hN : (N.subgroupOf D).Normal) (hq : ∀ x ∈ D, ∃ k : ℕ, x ^ p ^ k ∈ N)
    (hS : IsSylowIn p S D) : ∀ x ∈ D, ∃ s ∈ S, ∃ n ∈ N, x = s * n := by
  intro x hx
  let π : D →* D ⧸ N.subgroupOf D := QuotientGroup.mk' (N.subgroupOf D)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  let P' : Sylow p (D ⧸ N.subgroupOf D) := hS.toSylow.mapSurjective hπ
  have htop : IsPGroup p (⊤ : Subgroup (D ⧸ N.subgroupOf D)) := by
    intro y
    obtain ⟨z, hz⟩ := hπ y.1
    obtain ⟨k, hk⟩ := hq z z.2
    refine ⟨k, ?_⟩
    apply Subtype.ext
    change (y.1) ^ p ^ k = 1
    rw [← hz, ← map_pow]
    exact (QuotientGroup.eq_one_iff _).2 (by simpa [Subgroup.mem_subgroupOf] using hk)
  have hle := P'.is_maximal' htop le_top
  have hmem : π ⟨x, hx⟩ ∈ P'.toSubgroup := by
    rw [← hle]
    exact Subgroup.mem_top _
  have hmem' : π ⟨x, hx⟩ ∈ (hS.toSylow : Subgroup D).map π := hmem
  obtain ⟨s, hs, hsx⟩ := Subgroup.mem_map.1 hmem'
  have hsx' : s⁻¹ * ⟨x, hx⟩ ∈ N.subgroupOf D := QuotientGroup.eq.1 hsx
  have hs' : (s : G) ∈ S := by
    have := hs
    rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at this
    exact this
  refine ⟨(s : G), hs', (s : G)⁻¹ * x, ?_, by group⟩
  simpa [Subgroup.mem_subgroupOf] using hsx'

theorem pCoreOf_le_of_isSylowIn [Finite G] {p : ℕ} [Fact p.Prime] {K T : Subgroup G}
    (hT : IsSylowIn p T K) : pCoreOf p K ≤ T := by
  have : (pCore p K).Normal := CFSG.pCore_normal (p := p)
  have hle : pCore p K ≤ (hT.toSylow : Subgroup K) :=
    (CFSG.pCore_isPGroup (p := p)).le_sylow_of_normal hT.toSylow
  rintro _ ⟨y, hy, rfl⟩
  have hy' := hle hy
  rw [IsSylowIn.coe_toSylow, Subgroup.mem_subgroupOf] at hy'
  exact hy'

namespace A1b

@[expose] def conjSub (g : G) (H : Subgroup G) : Subgroup G := H.map (MulAut.conj g).toMonoidHom

theorem mem_conjSub_iff {g x : G} {H : Subgroup G} : x ∈ conjSub g H ↔ g⁻¹ * x * g ∈ H := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [MulAut.conj_apply, mul_assoc] using hy
  · intro hx
    refine ⟨g⁻¹ * x * g, hx, ?_⟩
    simp [MulAut.conj_apply, mul_assoc]

theorem mem_conjSub_of_mem {g x : G} {H : Subgroup G} (hx : x ∈ H) : g * x * g⁻¹ ∈ conjSub g H :=
  ⟨x, hx, by simp [MulAut.conj_apply]⟩

theorem conjSub_mul (a b : G) (H : Subgroup G) : conjSub (a * b) H = conjSub a (conjSub b H) := by
  ext x
  simp only [mem_conjSub_iff, mul_inv_rev]
  simp [mul_assoc]

theorem conjSub_one (H : Subgroup G) : conjSub 1 H = H := by
  ext x
  simp [mem_conjSub_iff]

theorem conjSub_mono (g : G) {H K : Subgroup G} (h : H ≤ K) : conjSub g H ≤ conjSub g K :=
  Subgroup.map_mono h

theorem conjSub_le_conjSub_iff (g : G) {H K : Subgroup G} : conjSub g H ≤ conjSub g K ↔ H ≤ K := by
  refine ⟨fun h x hx => ?_, conjSub_mono g⟩
  have := h (mem_conjSub_of_mem (g := g) hx)
  rw [mem_conjSub_iff] at this
  simpa [mul_assoc] using this

theorem conjSub_inj (g : G) {H K : Subgroup G} : conjSub g H = conjSub g K ↔ H = K := by
  rw [le_antisymm_iff, le_antisymm_iff, conjSub_le_conjSub_iff, conjSub_le_conjSub_iff]

theorem conjSub_normalizer (g : G) (H : Subgroup G) :
    conjSub g (Subgroup.normalizer (H : Set G)) = Subgroup.normalizer (conjSub g H : Set G) :=
  Subgroup.map_equiv_normalizer_eq H (MulAut.conj g)

end A1b

@[expose] def twoReducedProduct (H : Subgroup G) : Subgroup G :=
  ⨆ (V : Subgroup G) (_ : IsTwoReducedIn H V), V

theorem le_twoReducedProduct {H V : Subgroup G} (hV : IsTwoReducedIn H V) :
    V ≤ twoReducedProduct H :=
  le_iSup₂_of_le V hV le_rfl

end CFSG.Quasithin
