module

public import CFSG.Quasithin.Recognition.SzR1Perm
public import CFSG.Quasithin.Background.F7Basic

public section

namespace CFSG.Quasithin.SzR1

open CFSG.Quasithin
open scoped commutatorElement

namespace Vert

variable {G : Type*} [Group G]

theorem conjSub_eq_of_mem_normalizer {k : G} {V : Subgroup G}
    (hk : k ∈ Subgroup.normalizer (V : Set G)) : conjSub k V = V := by
  ext y
  rw [mem_conjSub]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hk) y
  simpa using this.symm

theorem mem_normalizer_of_conjSub_eq {k : G} {V : Subgroup G} (h : conjSub k V = V) :
    k ∈ Subgroup.normalizer (V : Set G) := by
  refine F7.mem_normalizer_of_conj_le h.le ?_
  calc conjSub k⁻¹ V = conjSub k⁻¹ (conjSub k V) := by rw [h]
    _ = V := conjSub_conjSub_inv k V
    _ ≤ V := le_rfl

theorem conjSub_le_of_mem {X P : Subgroup G} (hXP : X ≤ P) {x : G} (hx : x ∈ P) :
    conjSub x X ≤ P := by
  intro z hz
  have hz' := hXP (mem_conjSub.mp hz)
  have e : z = x * (x⁻¹ * z * x) * x⁻¹ := by group
  rw [e]
  exact P.mul_mem (P.mul_mem hx hz') (P.inv_mem hx)

theorem card_conjSub (g : G) (H : Subgroup G) : Nat.card (conjSub g H) = Nat.card H :=
  Subgroup.card_map_of_injective (MulEquiv.injective (MulAut.conj g))

theorem inf_eq_bot_of_card_two [Finite G] {A B : Subgroup G} (hA : Nat.card A = 2)
    (hB : Nat.card B = 2) (hne : B ≠ A) : A ⊓ B = ⊥ := by
  by_contra hbot
  apply hne
  have h1 : Nat.card (A ⊓ B : Subgroup G) ≠ 1 := fun hc => hbot (Subgroup.eq_bot_of_card_eq _ hc)
  have h2 : Nat.card (A ⊓ B : Subgroup G) ∣ 2 := hA ▸ Subgroup.card_dvd_of_le inf_le_left
  have h3 : Nat.card (A ⊓ B : Subgroup G) = 2 :=
    ((Nat.dvd_prime Nat.prime_two).mp h2).resolve_left h1
  have hl : A ⊓ B = A := Subgroup.eq_of_le_of_card_ge inf_le_left (by omega)
  have hr : A ⊓ B = B := Subgroup.eq_of_le_of_card_ge inf_le_right (by omega)
  exact hr.symm.trans hl

theorem eq_or_eq_of_relIndex_prime {p : ℕ} (hp : p.Prime) {A B H : Subgroup G}
    (hAB : A.relIndex B = p) (hAH : A ≤ H) (hHB : H ≤ B) : H = A ∨ H = B := by
  have h := Subgroup.relIndex_mul_relIndex A H B hAH hHB
  rw [hAB] at h
  rcases (Nat.dvd_prime hp).mp (Dvd.intro _ h) with h1 | h1
  · exact Or.inl (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hAH)
  · refine Or.inr (le_antisymm hHB (Subgroup.relIndex_eq_one.mp ?_))
    rw [h1] at h
    exact Nat.eq_of_mul_eq_mul_left hp.pos (h.trans (mul_one p).symm)

theorem sup_eq_of_relIndex_two {Q S W : Subgroup G} (hQS : Q ≤ S) (hWS : W ≤ S)
    (hQ2 : Q.relIndex S = 2) (hWQ : ¬ W ≤ Q) : Q ⊔ W = S := by
  rcases eq_or_eq_of_relIndex_prime Nat.prime_two hQ2 le_sup_left (sup_le hQS hWS) with h | h
  · exact absurd (le_sup_right.trans h.le) hWQ
  · exact h

theorem not_mem_normalizer_of_not_mem {P S Z : Subgroup G} {x : G} (hSP : S ≤ P)
    (hS3 : S.relIndex P = 3) (hSZ : S ≤ Subgroup.normalizer (Z : Set G))
    (hZP : ¬ P ≤ Subgroup.normalizer (Z : Set G)) (hxP : x ∈ P) (hxS : x ∉ S) :
    x ∉ Subgroup.normalizer (Z : Set G) := by
  intro hx
  rcases eq_or_eq_of_relIndex_prime Nat.prime_three hS3
    (H := Subgroup.normalizer (Z : Set G) ⊓ P) (le_inf hSZ hSP) inf_le_right with h | h
  · exact hxS (h.le (Subgroup.mem_inf.mpr ⟨hx, hxP⟩))
  · exact hZP (h.ge.trans inf_le_left)

theorem commutator_le_of_le {A B Q : Subgroup G} (hA : A ≤ Q) (hB : B ≤ Q) : ⁅A, B⁆ ≤ Q := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  rw [commutatorElement_def]
  exact Q.mul_mem (Q.mul_mem (Q.mul_mem (hA ha) (hB hb)) (Q.inv_mem (hA ha))) (Q.inv_mem (hB hb))

theorem exists_central_of_normalizes [Finite G] {S K : Subgroup G} (hS : IsPGroup 2 S)
    (hKS : K ≤ S) (hK1 : K ≠ ⊥) (hSN : S ≤ Subgroup.normalizer (K : Set G)) :
    ∃ k ∈ K, k ≠ 1 ∧ ∀ s ∈ S, k * s = s * k := by
  have hnorm : (K.subgroupOf S).Normal :=
    ⟨fun x hx g => (Subgroup.mem_normalizer_iff.1 (hSN g.2) x).1 hx⟩
  have hne : K.subgroupOf S ≠ ⊥ := by
    intro h
    apply hK1
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hKS hx⟩ : S) ∈ K.subgroupOf S := hx
    rw [h, Subgroup.mem_bot] at this
    exact (Subgroup.mem_bot).2 (congrArg Subtype.val this)
  have : Group.IsNilpotent S := hS.isNilpotent
  obtain ⟨⟨u, huK, huZ⟩, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne)
  exact ⟨u, huK, fun h => hu1 (Subtype.ext (Subtype.ext h)), fun s hs =>
    (congrArg Subtype.val (Subgroup.mem_center_iff.1 huZ ⟨s, hs⟩)).symm⟩

theorem exists_involution_central [Finite G] {R D : Subgroup G} (hR : IsPGroup 2 R)
    (hDR : D ≤ R) (hD1 : D ≠ ⊥) (hRN : R ≤ Subgroup.normalizer (D : Set G)) :
    ∃ u ∈ D, u ≠ 1 ∧ u * u = 1 ∧ ∀ s ∈ R, u * s = s * u := by
  obtain ⟨k, hkD, hk1, hkc⟩ := exists_central_of_normalizes hR hDR hD1 hRN
  obtain ⟨n, hn⟩ := hR ⟨k, hDR hkD⟩
  have hkn : k ^ (2 ^ n) = 1 := by simpa using congrArg Subtype.val hn
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (orderOf_dvd_of_pow_eq_one hkn)
  have he0 : e ≠ 0 := by
    rintro rfl
    exact hk1 (orderOf_eq_one_iff.mp (by simpa using he))
  have h2 : 2 ∣ orderOf k := by
    rw [he]
    exact dvd_pow_self 2 he0
  have hord : orderOf (k ^ (orderOf k / 2)) = 2 :=
    orderOf_pow_orderOf_div (by rw [he]; positivity) h2
  refine ⟨k ^ (orderOf k / 2), D.pow_mem hkD _, ?_, ?_, fun s hs => ?_⟩
  · intro h1
    rw [h1, orderOf_one] at hord
    omega
  · have := pow_orderOf_eq_one (k ^ (orderOf k / 2))
    rwa [hord, sq] at this
  · exact (Commute.pow_left (show Commute k s from hkc s hs) _).eq

theorem exists_two_others {Δ : Type*} [Finite Δ] (h3 : Nat.card Δ = 3) (β : Δ) :
    ∃ lam δ : Δ, lam ≠ β ∧ δ ≠ β ∧ δ ≠ lam ∧ ∀ x : Δ, x = β ∨ x = lam ∨ x = δ := by
  have := Fintype.ofFinite Δ
  have hc : Fintype.card Δ = 3 := by rw [← Nat.card_eq_fintype_card]; exact h3
  let e : Δ ≃ Fin 3 := Fintype.equivFinOfCardEq hc
  have key : ∀ a : Fin 3, ∃ b c : Fin 3, b ≠ a ∧ c ≠ a ∧ c ≠ b ∧
      ∀ x : Fin 3, x = a ∨ x = b ∨ x = c := by decide
  obtain ⟨b, c, hba, hca, hcb, hall⟩ := key (e β)
  refine ⟨e.symm b, e.symm c, ?_, ?_, ?_, fun x => ?_⟩
  · intro h
    exact hba (by simpa using congrArg e h)
  · intro h
    exact hca (by simpa using congrArg e h)
  · intro h
    exact hcb (by simpa using congrArg e h)
  · rcases hall (e x) with h | h | h
    · exact Or.inl (e.injective h)
    · exact Or.inr (Or.inl (by rw [← h]; simp))
    · exact Or.inr (Or.inr (by rw [← h]; simp))

theorem smul_mk {H : Type*} [Group H] {S' : Subgroup H} (a k : H) :
    a • ((k : H) : H ⧸ S') = ((a * k : H) : H ⧸ S') := rfl

theorem smul_base_iff {H : Type*} [Group H] {S' : Subgroup H} (p : H) :
    p • ((1 : H) : H ⧸ S') = ((1 : H) : H ⧸ S') ↔ p ∈ S' := by
  rw [smul_mk, mul_one, QuotientGroup.eq, mul_one, inv_mem_iff]

theorem exists_elements {H : Type*} [Group H] [Finite H] {S' : Subgroup H}
    (hsurj : Function.Surjective (MulAction.toPermHom H (H ⧸ S'))) (h3 : S'.index = 3) :
    ∃ g b y : H, g ∉ S' ∧ g * g ∈ S' ∧ b ∉ S' ∧ b * g ∈ S' ∧ y ∈ conjSub g S' ∧ y ∉ S' ∧
      ∀ s ∈ conjSub b S', (s ∈ S' ∧ g⁻¹ * s * g ∈ S') ∨ (g⁻¹ * s ∈ S' ∧ s * g ∈ S') := by
  classical
  have hcard : Nat.card (H ⧸ S') = 3 := h3
  have hperm : ∀ σ : Equiv.Perm (H ⧸ S'), ∃ p : H, ∀ x, p • x = σ x := fun σ => by
    obtain ⟨p, hp⟩ := hsurj σ
    exact ⟨p, fun x => by rw [← hp, MulAction.toPermHom_apply]; rfl⟩
  obtain ⟨β, hβ⟩ : ∃ β : H ⧸ S', β = ((1 : H) : H ⧸ S') := ⟨_, rfl⟩
  have hbase : ∀ p : H, p • β = β ↔ p ∈ S' := fun p => by
    rw [hβ]
    exact smul_base_iff p
  obtain ⟨lam, δ, hlb, hδb, hδl, hall⟩ := exists_two_others hcard β
  obtain ⟨g, hg⟩ := hperm (Equiv.swap β lam)
  obtain ⟨y, hy⟩ := hperm (Equiv.swap β δ)
  obtain ⟨b, hb⟩ := hperm (Equiv.swap lam δ * Equiv.swap β lam)
  have hgβ : g • β = lam := by rw [hg]; exact Equiv.swap_apply_left β lam
  have hgl : g • lam = β := by rw [hg]; exact Equiv.swap_apply_right β lam
  have hyβ : y • β = δ := by rw [hy]; exact Equiv.swap_apply_left β δ
  have hyl : y • lam = lam := by
    rw [hy]; exact Equiv.swap_apply_of_ne_of_ne hlb hδl.symm
  have hbβ : b • β = δ := by
    rw [hb, Equiv.Perm.mul_apply, Equiv.swap_apply_left, Equiv.swap_apply_left]
  have hbl : b • lam = β := by
    rw [hb, Equiv.Perm.mul_apply, Equiv.swap_apply_right,
      Equiv.swap_apply_of_ne_of_ne hlb.symm hδb.symm]
  have hgi : g⁻¹ • lam = β := by rw [inv_smul_eq_iff]; exact hgβ.symm
  refine ⟨g, b, y, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact fun h => hlb (hgβ.symm.trans ((hbase g).mpr h))
  · exact (hbase _).mp (by rw [mul_smul, hgβ, hgl])
  · exact fun h => hδb (hbβ.symm.trans ((hbase b).mpr h))
  · exact (hbase _).mp (by rw [mul_smul, hgβ, hbl])
  · refine mem_conjSub.mpr ((hbase _).mp ?_)
    rw [mul_smul, mul_smul, hgβ, hyl, hgi]
  · exact fun h => hδb (hyβ.symm.trans ((hbase y).mpr h))
  · intro s hs
    have h2 := (hbase _).mpr (mem_conjSub.mp hs)
    rw [mul_smul, mul_smul, hbβ, inv_smul_eq_iff, hbβ] at h2
    have hsβδ : s • β ≠ δ := fun h => hδb.symm (MulAction.injective s (h.trans h2.symm))
    have hslδ : s • lam ≠ δ := fun h => hδl.symm (MulAction.injective s (h.trans h2.symm))
    have hsne : s • β ≠ s • lam := fun h => hlb.symm (MulAction.injective s h)
    have hβs : s • β = β ∨ s • β = lam := by
      rcases hall (s • β) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hsβδ
    have hls : s • lam = β ∨ s • lam = lam := by
      rcases hall (s • lam) with h | h | h
      · exact Or.inl h
      · exact Or.inr h
      · exact absurd h hslδ
    rcases hβs with h1 | h1 <;> rcases hls with h3 | h3
    · exact absurd (h1.trans h3.symm) hsne
    · refine Or.inl ⟨(hbase s).mp h1, (hbase _).mp ?_⟩
      rw [mul_smul, mul_smul, hgβ, h3, hgi]
    · refine Or.inr ⟨(hbase _).mp ?_, (hbase _).mp ?_⟩
      · rw [mul_smul, h1, hgi]
      · rw [mul_smul, hgβ, h3]
    · exact absurd (h1.trans h3.symm) hsne

theorem exists_vertex_elements [Finite G] {P S Q : Subgroup G} (hSP : S ≤ P) (hQS : Q ≤ S)
    (hQN : P ≤ Subgroup.normalizer (Q : Set G)) (hS2 : IsPGroup 2 S)
    (hmax : ∀ N : Subgroup G, N ≤ P → P ≤ Subgroup.normalizer (N : Set G) → IsPGroup 2 N →
      N ≤ Q)
    (hS3 : S.relIndex P = 3) (hQ2 : Q.relIndex S = 2) :
    ∃ g b y : G, g ∈ P ∧ g ∉ S ∧ g * g ∈ S ∧ b ∈ P ∧ b ∉ S ∧ b * g ∈ S ∧
      y ∈ conjSub g S ∧ y ∉ S ∧
      ∀ s ∈ conjSub b S, (s ∈ S ∧ g⁻¹ * s * g ∈ S) ∨ (g⁻¹ * s ∈ S ∧ s * g ∈ S) := by
  have hQn : (Q.subgroupOf P).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hQN
  have hS2' : IsPGroup 2 (S.subgroupOf P) :=
    hS2.of_equiv (Subgroup.subgroupOfEquivOfLe hSP).symm
  have hQS' : Q.subgroupOf P ≤ S.subgroupOf P := fun x hx => hQS hx
  have hmax' : ∀ N : Subgroup P, N.Normal → IsPGroup 2 N → N ≤ Q.subgroupOf P := by
    intro N hN hN2
    have hle : N.map P.subtype ≤ Q := by
      refine hmax _ (Subgroup.map_subtype_le N) ?_ (hN2.map P.subtype)
      rw [Subgroup.le_normalizer_iff]
      intro p hp k hk
      obtain ⟨n, hn, rfl⟩ := Subgroup.mem_map.mp hk
      exact Subgroup.mem_map.mpr ⟨⟨p, hp⟩ * n * ⟨p, hp⟩⁻¹, hN.conj_mem n hn ⟨p, hp⟩, rfl⟩
    exact fun x hx => hle (Subgroup.mem_map.mpr ⟨x, hx, rfl⟩)
  have hS3' : (S.subgroupOf P).index = 3 := hS3
  have hQ6' : (Q.subgroupOf P).index = 6 := by
    have h := Subgroup.relIndex_mul_relIndex Q S P hQS hSP
    rw [hQ2, hS3] at h
    have h6 : Q.relIndex P = 6 := by omega
    exact h6
  have hsurj := perm_surjective hQn hS2' hQS' hmax' hS3' hQ6'
  obtain ⟨g, b, y, h1, h2, h3, h4, h5, h6, h7⟩ := exists_elements hsurj hS3'
  refine ⟨g, b, y, g.2, fun h => h1 (Subgroup.mem_subgroupOf.mpr h),
    Subgroup.mem_subgroupOf.mp h2, b.2, fun h => h3 (Subgroup.mem_subgroupOf.mpr h),
    Subgroup.mem_subgroupOf.mp h4, ?_, fun h => h6 (Subgroup.mem_subgroupOf.mpr h), ?_⟩
  · exact mem_conjSub.mpr (Subgroup.mem_subgroupOf.mp (mem_conjSub.mp h5))
  · intro s hs
    have hsP : s ∈ P := conjSub_le_of_mem hSP b.2 hs
    have hs' : (⟨s, hsP⟩ : P) ∈ conjSub b (S.subgroupOf P) :=
      mem_conjSub.mpr (Subgroup.mem_subgroupOf.mpr (mem_conjSub.mp hs))
    rcases h7 _ hs' with ⟨k1, k2⟩ | ⟨k1, k2⟩
    · exact Or.inl ⟨Subgroup.mem_subgroupOf.mp k1, Subgroup.mem_subgroupOf.mp k2⟩
    · exact Or.inr ⟨Subgroup.mem_subgroupOf.mp k1, Subgroup.mem_subgroupOf.mp k2⟩

structure Hyp (P S Q W Z M : Subgroup G) : Prop where
  sp : S ≤ P
  qs : Q ≤ S
  qn : P ≤ Subgroup.normalizer (Q : Set G)
  s3 : S.relIndex P = 3
  q2 : Q.relIndex S = 2
  ws : W ≤ S
  sw : S ≤ Subgroup.normalizer (W : Set G)
  sm : S ≤ Subgroup.normalizer (M : Set G)
  wm : W ≤ M
  zw : ∀ g ∈ P, conjSub g Z ≤ W
  ww : ⁅W, W⁆ ≤ Z
  mw : ⁅M, W⁆ ≤ Z
  wq : ¬ W ≤ Q
  nonab : ⁅W ⊓ Q, W ⊓ Q⁆ ≠ ⊥
  b1 : ∀ s ∈ Q, (∀ w ∈ W ⊓ Q, s * w * s⁻¹ * w⁻¹ ∈ Z) → s ∈ M

namespace Hyp

variable {P S Q W Z M : Subgroup G}

theorem Q_le_normalizer (h : Hyp P S Q W Z M) {g : G} (hg : g ∈ P) :
    Q ≤ Subgroup.normalizer ((W ⊓ conjSub g M : Subgroup G) : Set G) := by
  refine F7.le_normalizer_inf (h.qs.trans h.sw) ?_
  calc Q = conjSub g Q := (conjSub_eq_of_mem_normalizer (h.qn hg)).symm
    _ ≤ conjSub g S := conjSub_mono g h.qs
    _ ≤ Subgroup.normalizer (conjSub g M : Set G) := conjSub_le_normalizer h.sm

theorem W_le_normalizer (h : Hyp P S Q W Z M) {g : G} (hg : g ∈ P) :
    W ≤ Subgroup.normalizer ((W ⊓ conjSub g M : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro w hw t ht
  obtain ⟨htW, htM⟩ := Subgroup.mem_inf.mp ht
  refine Subgroup.mem_inf.mpr ⟨W.mul_mem (W.mul_mem hw htW) (W.inv_mem hw), ?_⟩
  have hZ : Z ≤ conjSub g W := (le_conjSub_iff g).mpr (h.zw g⁻¹ (P.inv_mem hg))
  have hc : ⁅w, t⁆ ∈ Z := h.ww (Subgroup.commutator_mem_commutator hw htW)
  have e : w * t * w⁻¹ = ⁅w, t⁆ * t := by rw [commutatorElement_def]; group
  rw [e]
  exact (conjSub g M).mul_mem (conjSub_mono g h.wm (hZ hc)) htM

theorem conjSub_W_le_normalizer (h : Hyp P S Q W Z M) {g : G} (hg : g ∈ P) :
    conjSub g W ≤ Subgroup.normalizer ((W ⊓ conjSub g M : Subgroup G) : Set G) := by
  rw [Subgroup.le_normalizer_iff]
  intro w hw t ht
  obtain ⟨htW, htM⟩ := Subgroup.mem_inf.mp ht
  have hwM : w ∈ conjSub g M := conjSub_mono g h.wm hw
  refine Subgroup.mem_inf.mpr ⟨?_, (conjSub g M).mul_mem
    ((conjSub g M).mul_mem hwM htM) ((conjSub g M).inv_mem hwM)⟩
  have hcm : ⁅w, t⁆ ∈ conjSub g ⁅W, M⁆ := by
    rw [← conjSub_commutator]
    exact Subgroup.commutator_mem_commutator hw htM
  have hZ : conjSub g ⁅W, M⁆ ≤ conjSub g Z :=
    conjSub_mono g (by rw [Subgroup.commutator_comm]; exact h.mw)
  have e : w * t * w⁻¹ = ⁅w, t⁆ * t := by rw [commutatorElement_def]; group
  rw [e]
  exact W.mul_mem (h.zw g hg (hZ hcm)) htW

theorem le_normalizer_T (h : Hyp P S Q W Z M) {g y : G} (hg : g ∈ P) (hyg : y ∈ conjSub g S)
    (hyS : y ∉ S) :
    P ≤ Subgroup.normalizer ((W ⊓ conjSub g M : Subgroup G) : Set G) := by
  have hS : S = Q ⊔ W := (sup_eq_of_relIndex_two h.qs h.ws h.q2 h.wq).symm
  have hSN : S ≤ Subgroup.normalizer ((W ⊓ conjSub g M : Subgroup G) : Set G) := by
    rw [hS]
    exact sup_le (h.Q_le_normalizer hg) (h.W_le_normalizer hg)
  have hgS : conjSub g S = Q ⊔ conjSub g W := by
    rw [hS, conjSub_sup, conjSub_eq_of_mem_normalizer (h.qn hg)]
  have hgSN : conjSub g S ≤ Subgroup.normalizer ((W ⊓ conjSub g M : Subgroup G) : Set G) := by
    rw [hgS]
    exact sup_le (h.Q_le_normalizer hg) (h.conjSub_W_le_normalizer hg)
  rcases eq_or_eq_of_relIndex_prime Nat.prime_three h.s3 (H := S ⊔ conjSub g S)
      le_sup_left (sup_le h.sp (conjSub_le_of_mem h.sp hg)) with hh | hh
  · exact absurd (hh.le (Subgroup.mem_sup_right hyg)) hyS
  · rw [← hh]
    exact sup_le hSN hgSN

theorem T_le_conjSub (h : Hyp P S Q W Z M) {g x : G} (hxg : x * g ∈ S)
    (hT : conjSub x (W ⊓ conjSub g M) = W ⊓ conjSub g M) :
    W ⊓ conjSub g M ≤ conjSub x W := by
  calc W ⊓ conjSub g M = conjSub x (W ⊓ conjSub g M) := hT.symm
    _ = conjSub x W ⊓ M := by
      rw [conjSub_inf, ← conjSub_mul, conjSub_eq_of_mem_normalizer (h.sm hxg)]
    _ ≤ conjSub x W := inf_le_left

theorem commutator_T_eq_bot (h : Hyp P S Q W Z M) {g : G}
    (hT : W ⊓ conjSub g M ≤ conjSub g W) (hZZ : Z ⊓ conjSub g Z = ⊥) :
    ⁅W ⊓ conjSub g M, W ⊓ conjSub g M⁆ = ⊥ := by
  refine le_antisymm ((le_inf ?_ ?_).trans hZZ.le) bot_le
  · exact (Subgroup.commutator_mono inf_le_left inf_le_left).trans h.ww
  · calc ⁅W ⊓ conjSub g M, W ⊓ conjSub g M⁆ ≤ ⁅conjSub g W, conjSub g W⁆ :=
          Subgroup.commutator_mono hT hT
      _ = conjSub g ⁅W, W⁆ := conjSub_commutator g W W
      _ ≤ conjSub g Z := conjSub_mono g h.ww

theorem not_commutator_le (h : Hyp P S Q W Z M) {g : G} (hg : g ∈ P) (hgg : g * g ∈ S)
    (hTab : ⁅W ⊓ conjSub g M, W ⊓ conjSub g M⁆ = ⊥) :
    ¬ ⁅W ⊓ Q, conjSub g W ⊓ Q⁆ ≤ Z := by
  intro hD
  have hWl : conjSub g W ⊓ Q ≤ M := by
    intro u hu
    refine h.b1 u (Subgroup.mem_inf.mp hu).2 fun w hw => ?_
    have hc : ⁅u, w⁆ ∈ ⁅W ⊓ Q, conjSub g W ⊓ Q⁆ := by
      rw [Subgroup.commutator_comm]
      exact Subgroup.commutator_mem_commutator hu hw
    simpa [commutatorElement_def] using hD hc
  have hWQ : W ⊓ Q ≤ W ⊓ conjSub g M := by
    refine le_inf inf_le_left ?_
    have h2 : conjSub g (conjSub g W ⊓ Q) = W ⊓ Q := by
      rw [conjSub_inf, ← conjSub_mul, conjSub_eq_of_mem_normalizer (h.sw hgg),
        conjSub_eq_of_mem_normalizer (h.qn hg)]
    calc W ⊓ Q = conjSub g (conjSub g W ⊓ Q) := h2.symm
      _ ≤ conjSub g M := conjSub_mono g hWl
  apply h.nonab
  exact le_antisymm ((Subgroup.commutator_mono hWQ hWQ).trans hTab.le) bot_le

theorem conjSub_D (h : Hyp P S Q W Z M) {g s : G} (hs : s ∈ P)
    (hcase : (s ∈ S ∧ g⁻¹ * s * g ∈ S) ∨ (g⁻¹ * s ∈ S ∧ s * g ∈ S)) :
    conjSub s ⁅W ⊓ Q, conjSub g W ⊓ Q⁆ = ⁅W ⊓ Q, conjSub g W ⊓ Q⁆ := by
  rw [← conjSub_commutator, conjSub_inf, conjSub_inf, conjSub_eq_of_mem_normalizer (h.qn hs)]
  rcases hcase with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : conjSub s W = W := conjSub_eq_of_mem_normalizer (h.sw h1)
    have e2 : conjSub s (conjSub g W) = conjSub g W := by
      rw [← conjSub_mul]
      have : s * g = g * (g⁻¹ * s * g) := by group
      rw [this, conjSub_mul, conjSub_eq_of_mem_normalizer (h.sw h2)]
    rw [e1, e2]
  · have e1 : conjSub s W = conjSub g W := by
      have : s = g * (g⁻¹ * s) := by group
      rw [this, conjSub_mul, conjSub_eq_of_mem_normalizer (h.sw h1)]
    have e2 : conjSub s (conjSub g W) = W := by
      rw [← conjSub_mul]
      exact conjSub_eq_of_mem_normalizer (h.sw h2)
    rw [e1, e2, Subgroup.commutator_comm]

theorem D_le_T (h : Hyp P S Q W Z M) {g : G} (hg : g ∈ P) :
    ⁅W ⊓ Q, conjSub g W ⊓ Q⁆ ≤ W ⊓ conjSub g M := by
  rw [Subgroup.commutator_le]
  intro a ha c hc
  obtain ⟨haW, haQ⟩ := Subgroup.mem_inf.mp ha
  obtain ⟨hcW, hcQ⟩ := Subgroup.mem_inf.mp hc
  have hcN : c ∈ Subgroup.normalizer (W : Set G) := h.sw (h.qs hcQ)
  have hQN : Q ≤ Subgroup.normalizer (conjSub g W : Set G) :=
    calc Q = conjSub g Q := (conjSub_eq_of_mem_normalizer (h.qn hg)).symm
      _ ≤ conjSub g S := conjSub_mono g h.qs
      _ ≤ Subgroup.normalizer (conjSub g W : Set G) := conjSub_le_normalizer h.sw
  have haN : a ∈ Subgroup.normalizer (conjSub g W : Set G) := hQN haQ
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have e : ⁅a, c⁆ = a * (c * a⁻¹ * c⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem haW ((Subgroup.mem_normalizer_iff.mp hcN a⁻¹).mp (W.inv_mem haW))
  · have e : ⁅a, c⁆ = (a * c * a⁻¹) * c⁻¹ := by rw [commutatorElement_def]
    have h1 : ⁅a, c⁆ ∈ conjSub g W := by
      rw [e]
      exact (conjSub g W).mul_mem ((Subgroup.mem_normalizer_iff.mp haN c).mp hcW)
        ((conjSub g W).inv_mem hcW)
    exact conjSub_mono g h.wm h1

end Hyp

end Vert

end CFSG.Quasithin.SzR1
