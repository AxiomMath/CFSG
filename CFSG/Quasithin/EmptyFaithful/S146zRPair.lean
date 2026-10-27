module

public import CFSG.Quasithin.EmptyFaithful.S146zRElem
public import CFSG.Quasithin.EmptyFaithful.SBc16S
public import CFSG.Quasithin.EmptyFaithful.SBc13Pair
public import CFSG.Quasithin.EmptyFaithful.SBc15C2Dec
public import CFSG.Quasithin.EmptyFaithful.S146zRQFour

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open scoped Pointwise

section Images

variable {G : Type} [Group G]

theorem q_image_sup {G₁ K L : Subgroup G} (hK : K ≤ G₁) (hL : L ≤ G₁) :
    imageOTwoQuot G₁ (K ⊔ L) = imageOTwoQuot G₁ K ⊔ imageOTwoQuot G₁ L := by
  unfold imageOTwoQuot
  rw [Subgroup.subgroupOf_sup hK hL, Subgroup.map_sup]

theorem q_image_conjSub {G₁ K : Subgroup G} {y : G} (hy : y ∈ G₁) :
    imageOTwoQuot G₁ (conjSub y K) =
      (imageOTwoQuot G₁ K).map (MulAut.conj (qPi G₁ ⟨y, hy⟩)).toMonoidHom := by
  ext z
  constructor
  · rintro ⟨x, hx, rfl⟩
    have hxK : y⁻¹ * (x : G) * y ∈ K := mem_conjSub.mp (Subgroup.mem_subgroupOf.mp hx)
    have hk : (⟨y⁻¹ * (x : G) * y, G₁.mul_mem (G₁.mul_mem (G₁.inv_mem hy) x.2) hy⟩ : ↥G₁) ∈
        K.subgroupOf G₁ := hxK
    refine ⟨qPi G₁ ⟨y⁻¹ * (x : G) * y, G₁.mul_mem (G₁.mul_mem (G₁.inv_mem hy) x.2) hy⟩,
      ⟨_, hk, rfl⟩, ?_⟩
    change qPi G₁ ⟨y, hy⟩ * qPi G₁ ⟨y⁻¹ * (x : G) * y, _⟩ * (qPi G₁ ⟨y, hy⟩)⁻¹ = qPi G₁ x
    rw [← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    simp [mul_assoc]
  · rintro ⟨w, ⟨k, hk, rfl⟩, rfl⟩
    refine ⟨⟨y, hy⟩ * k * ⟨y, hy⟩⁻¹, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr (mul_mem_conjSub (Subgroup.mem_subgroupOf.mp hk))
    · change qPi G₁ (⟨y, hy⟩ * k * ⟨y, hy⟩⁻¹) = qPi G₁ ⟨y, hy⟩ * qPi G₁ k * (qPi G₁ ⟨y, hy⟩)⁻¹
      rw [map_mul, map_mul, map_inv]

theorem q_image_normalizes {G₁ K L : Subgroup G} (hn : L ≤ Subgroup.normalizer (K : Set G)) :
    ∀ x ∈ imageOTwoQuot G₁ L, ∀ y ∈ imageOTwoQuot G₁ K, x * y * x⁻¹ ∈ imageOTwoQuot G₁ K := by
  rintro _ ⟨l, hl, rfl⟩ _ ⟨k, hk, rfl⟩
  refine ⟨l * k * l⁻¹, ?_, ?_⟩
  · refine Subgroup.mem_subgroupOf.mpr ?_
    have := (Subgroup.mem_normalizer_iff.mp (hn (Subgroup.mem_subgroupOf.mp hl)) (k : G)).mp
      (Subgroup.mem_subgroupOf.mp hk)
    simpa using this
  · simp only [map_mul, map_inv]

end Images

section Pair

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

theorem q_pair_comm_disjoint {G₁ K₁ K₂ : Subgroup G} (hK₁ : K₁ ∈ cComp G₁) (hK₂ : K₂ ∈ cComp G₁)
    (hne : K₁ ≠ K₂) (hs : IsSimpleGroup ↥(imageOTwoQuot G₁ K₁))
    (h12 : K₂ ≤ Subgroup.normalizer (K₁ : Set G)) (h21 : K₁ ≤ Subgroup.normalizer (K₂ : Set G)) :
    (∀ a ∈ imageOTwoQuot G₁ K₁, ∀ b ∈ imageOTwoQuot G₁ K₂, a * b = b * a) ∧
      imageOTwoQuot G₁ K₁ ⊓ imageOTwoQuot G₁ K₂ = ⊥ := by
  classical
  have hK₁G : K₁ ≤ G₁ := le_of_mem_cComp hK₁
  have hK₂G : K₂ ≤ G₁ := le_of_mem_cComp hK₂
  set N₁ := imageOTwoQuot G₁ K₁ with hN₁
  set N₂ := imageOTwoQuot G₁ K₂ with hN₂
  have n21 := q_image_normalizes (G₁ := G₁) h12
  have n12 := q_image_normalizes (G₁ := G₁) h21
  have hdisj : N₁ ⊓ N₂ = ⊥ := by
    have hnormal : ((N₁ ⊓ N₂).subgroupOf N₁).Normal := by
      refine ⟨fun a ha g => ?_⟩
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      refine ⟨N₁.mul_mem (N₁.mul_mem g.2 ha.1) (N₁.inv_mem g.2), ?_⟩
      have := n12 (g : OTwoQuot G₁) g.2 a ha.2
      simpa using this
    rcases hnormal.eq_bot_or_eq_top with h | h
    · rw [Subgroup.eq_bot_iff_forall] at h ⊢
      intro x hx
      have := h ⟨x, hx.1⟩ (Subgroup.mem_subgroupOf.mpr hx)
      exact congrArg Subtype.val this
    · exfalso
      have hle : N₁ ≤ N₂ := fun x hx =>
        ((Subgroup.mem_subgroupOf.mp (h ▸ Subgroup.mem_top (⟨x, hx⟩ : ↥N₁)) : x ∈ N₁ ⊓ N₂)).2
      have hc₁ := q_image_mem_cComp hK₁
      have hc₂ := q_image_mem_cComp hK₂
      have heq : N₁ = N₂ := by
        by_contra hne'
        exact not_subnormal_of_mem_cComp hc₂ (lt_of_le_of_ne hle hne') (ne_bot_of_mem_cComp hc₁)
          (perfect_of_mem_cComp hc₁) (subnormal_of_mem_cComp hc₁)
      exact hne (q_image_injOn hK₁ hK₂ heq)
  refine ⟨fun a ha b hb => ?_, hdisj⟩
  have h1 : a * b * a⁻¹ * b⁻¹ ∈ N₁ ⊓ N₂ := by
    refine ⟨?_, ?_⟩
    · have := N₁.mul_mem ha (n21 b hb a⁻¹ (N₁.inv_mem ha))
      simpa [mul_assoc] using this
    · exact N₂.mul_mem (n12 a ha b hb) (N₂.inv_mem hb)
  rw [hdisj, Subgroup.mem_bot] at h1
  have h2 : a * b * a⁻¹ = b := mul_inv_eq_one.mp h1
  calc a * b = a * b * a⁻¹ * a := by group
    _ = b * a := by rw [h2]

end Pair

section Facts

variable {G : Type} [Group G] [Finite G] {T M H PQ : Subgroup G} {p : ℕ}

structure CaseIFacts {X : Type*} [Group X] (N₁ N₂ : Subgroup X) (ŝ : X) : Prop where
  conj : N₂ = N₁.map (MulAut.conj ŝ).toMonoidHom
  comm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a
  disj : N₁ ⊓ N₂ = ⊥
  perm : ∀ x : X, N₁.map (MulAut.conj x).toMonoidHom = N₁ ∨
    N₁.map (MulAut.conj x).toMonoidHom = N₂
  normal : (N₁ ⊔ N₂).Normal
  cen : ∀ x : X, (∀ n ∈ N₁ ⊔ N₂, x * n = n * x) → x ∈ N₁ ⊔ N₂
  centreless : ∀ n ∈ N₁, (∀ m ∈ N₁, n * m = m * n) → n = 1

theorem q_exists_elemAbelian_pair {X : Type*} [Group X] [Finite X] {N₁ N₂ : Subgroup X} {ŝ : X}
    (hs : N₂ = N₁.map (MulAut.conj ŝ).toMonoidHom) (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (hdisj : N₁ ⊓ N₂ = ⊥) (r : ℕ) [hr : Fact r.Prime] (hdvd : r ∣ Nat.card N₁) :
    ∃ E : Subgroup X, E ≤ N₁ ⊔ N₂ ∧ IsElemAbelian r E ∧ Nat.card E = r ^ 2 := by
  classical
  obtain ⟨a, ha⟩ := exists_prime_orderOf_dvd_card' (G := ↥N₁) r hdvd
  have haX : orderOf (a : X) = r := by rw [Subgroup.orderOf_coe]; exact ha
  have hb : ŝ * (a : X) * ŝ⁻¹ ∈ N₂ := by
    rw [hs]
    exact ⟨a, a.2, rfl⟩
  have hbo : orderOf (ŝ * (a : X) * ŝ⁻¹) = r := by
    have : ŝ * (a : X) * ŝ⁻¹ = MulAut.conj ŝ (a : X) := by simp [MulAut.conj_apply]
    rw [this, MulEquiv.orderOf_eq]
    exact haX
  have hA1 : (a : X) ^ r = 1 := by rw [← haX]; exact pow_orderOf_eq_one _
  have hB1 : (ŝ * (a : X) * ŝ⁻¹) ^ r = 1 := by rw [← hbo]; exact pow_orderOf_eq_one _
  have hZA := zmElemAbelian_zpowers (p := r) hA1
  have hZB := zmElemAbelian_zpowers (p := r) hB1
  have hzA : Subgroup.zpowers (a : X) ≤ N₁ := (Subgroup.zpowers_le.mpr a.2)
  have hzB : Subgroup.zpowers (ŝ * (a : X) * ŝ⁻¹) ≤ N₂ := (Subgroup.zpowers_le.mpr hb)
  have hcomm' : ∀ x ∈ Subgroup.zpowers (a : X), ∀ y ∈ Subgroup.zpowers (ŝ * (a : X) * ŝ⁻¹),
      x * y = y * x := fun x hx y hy => hcomm x (hzA hx) y (hzB hy)
  have hdisj' : Disjoint (Subgroup.zpowers (a : X)) (Subgroup.zpowers (ŝ * (a : X) * ŝ⁻¹)) := by
    rw [Subgroup.disjoint_def]
    intro x hx hy
    have : x ∈ N₁ ⊓ N₂ := ⟨hzA hx, hzB hy⟩
    rw [hdisj, Subgroup.mem_bot] at this
    exact this
  refine ⟨_, sup_le_sup hzA hzB, zmElemAbelian_sup hZA hZB hcomm', ?_⟩
  rw [SBc15.card_sup_eq_mul_of_commute hcomm' hdisj', Nat.card_zpowers, Nat.card_zpowers, haX, hbo]
  ring

theorem q_centreless_conj {X : Type*} [Group X] {N : Subgroup X}
    (h : ∀ n ∈ N, (∀ m ∈ N, n * m = m * n) → n = 1) (g : X) :
    ∀ n ∈ N.map (MulAut.conj g).toMonoidHom,
      (∀ m ∈ N.map (MulAut.conj g).toMonoidHom, n * m = m * n) → n = 1 := by
  rintro _ ⟨a, ha, rfl⟩ hc
  have : a = 1 := h a ha fun m hm => by
    have h1 := hc (MulAut.conj g m) ⟨m, hm, rfl⟩
    have h2 : MulAut.conj g (a * m) = MulAut.conj g (m * a) := by
      rw [map_mul, map_mul]
      exact h1
    exact (MulAut.conj g).injective h2
  simp [this]

theorem q_centreless_sup {X : Type*} [Group X] {N₁ N₂ : Subgroup X}
    (hcomm : ∀ a ∈ N₁, ∀ b ∈ N₂, a * b = b * a)
    (h₁ : ∀ n ∈ N₁, (∀ m ∈ N₁, n * m = m * n) → n = 1)
    (h₂ : ∀ n ∈ N₂, (∀ m ∈ N₂, n * m = m * n) → n = 1) :
    ∀ n ∈ N₁ ⊔ N₂, (∀ m ∈ N₁ ⊔ N₂, n * m = m * n) → n = 1 := by
  intro n hn hc
  have hnorm : N₁ ≤ Subgroup.normalizer (N₂ : Set X) := fun x hx => by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      have : x * y * x⁻¹ = y := by rw [hcomm x hx y hy]; group
      rw [this]; exact hy
    · intro hy
      have e1 := hcomm x hx _ hy
      have e2 : x * y * x⁻¹ = y := by
        have e3 : x * (x * y * x⁻¹) = x * y := by rw [e1]; group
        exact mul_left_cancel e3
      rw [e2] at hy
      exact hy
  have hmul : (↑(N₁ ⊔ N₂) : Set X) = ↑N₁ * ↑N₂ :=
    Subgroup.coe_mul_of_left_le_normalizer_right N₁ N₂ hnorm
  have hn' : n ∈ (↑(N₁ ⊔ N₂) : Set X) := hn
  rw [hmul] at hn'
  obtain ⟨a, ha, b, hb, rfl⟩ := hn'
  have ha1 : a = 1 := h₁ a ha fun m hm => by
    have := hc m (Subgroup.mem_sup_left hm)
    have hbm : b * m = m * b := (hcomm m hm b hb).symm
    calc a * m = a * m * b * b⁻¹ := by group
      _ = a * (m * b) * b⁻¹ := by group
      _ = a * (b * m) * b⁻¹ := by rw [hbm]
      _ = (a * b) * m * b⁻¹ := by group
      _ = m * (a * b) * b⁻¹ := by rw [this]
      _ = m * a * (b * b⁻¹) := by group
      _ = m * a := by group
  have hb1 : b = 1 := h₂ b hb fun m hm => by
    have := hc m (Subgroup.mem_sup_right hm)
    have ham : a * m = m * a := hcomm a ha m hm
    calc b * m = a⁻¹ * (a * b * m) := by group
      _ = a⁻¹ * (m * (a * b)) := by rw [this]
      _ = a⁻¹ * (m * a) * b := by group
      _ = a⁻¹ * (a * m) * b := by rw [ham]
      _ = m * b := by group
  show a * b = 1
  rw [ha1, hb1, one_mul]

theorem q_caseI_facts (h36 : A36ForSQTK) (hlist : SQTKList3Dvd) (iS : Input14614NoSz)
    (S : Setting146 G T M) (hred : IsRedCE T M H PQ p) (hmax : PMaximal T M p)
    {K₁ : Subgroup G} {s : G} (hK₁ : K₁ ∈ cComp (mcOf T)) (hsG : s ∈ mcOf T)
    (hsN : s ∉ Subgroup.normalizer (K₁ : Set G))
    (hKz : conjClosure (oTwoUpper H) (mcOf T) = K₁ ⊔ conjSub s K₁)
    (hs : IsSimpleGroup ↥(imageOTwoQuot (mcOf T) K₁))
    (hnc : ∃ a b : ↥(imageOTwoQuot (mcOf T) K₁), a * b ≠ b * a)
    (h3 : 3 ∣ Nat.card (imageOTwoQuot (mcOf T) K₁))
    (hp : p ∣ Nat.card (imageOTwoQuot (mcOf T) K₁)) :
    CaseIFacts (imageOTwoQuot (mcOf T) K₁) (imageOTwoQuot (mcOf T) (conjSub s K₁))
      (qPi (mcOf T) ⟨s, hsG⟩) := by
  classical
  have hK₁G : K₁ ≤ mcOf T := le_of_mem_cComp hK₁
  have hK₂ : conjSub s K₁ ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK₁ hsG
  have hK₂G : conjSub s K₁ ≤ mcOf T := le_of_mem_cComp hK₂
  have hne : K₁ ≠ conjSub s K₁ := fun h => hsN (CosetGeom.mem_normalizer_of_conjSub_eq h.symm)
  have h12 : conjSub s K₁ ≤ Subgroup.normalizer (K₁ : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK₁ hK₂)
  have h21 : K₁ ≤ Subgroup.normalizer (conjSub s K₁ : Set G) :=
    le_sup_right.trans (SBc16.sup_le_normalizer_of_mem_cComp hK₂ hK₁)
  obtain ⟨hcomm, hdisj⟩ := q_pair_comm_disjoint hK₁ hK₂ hne hs h12 h21
  have hconj : imageOTwoQuot (mcOf T) (conjSub s K₁) =
      (imageOTwoQuot (mcOf T) K₁).map (MulAut.conj (qPi (mcOf T) ⟨s, hsG⟩)).toMonoidHom :=
    q_image_conjSub hsG
  have hKzn : mcOf T ≤ Subgroup.normalizer (conjClosure (oTwoUpper H) (mcOf T) : Set G) :=
    le_normalizer_conjClosure _ _
  have hperm : ∀ x : OTwoQuot (mcOf T),
      (imageOTwoQuot (mcOf T) K₁).map (MulAut.conj x).toMonoidHom = imageOTwoQuot (mcOf T) K₁ ∨
      (imageOTwoQuot (mcOf T) K₁).map (MulAut.conj x).toMonoidHom =
        imageOTwoQuot (mcOf T) (conjSub s K₁) := by
    intro x
    obtain ⟨y, rfl⟩ := qPi_surjective (mcOf T) x
    have hy : (y : G) ∈ mcOf T := y.2
    have h1 : imageOTwoQuot (mcOf T) (conjSub (y : G) K₁) =
        (imageOTwoQuot (mcOf T) K₁).map (MulAut.conj (qPi (mcOf T) y)).toMonoidHom :=
      q_image_conjSub hy
    rw [← h1]
    have hC : conjSub (y : G) K₁ ∈ cComp (mcOf T) := conjSub_mem_cComp_of_mem hK₁ hy
    have hCle : conjSub (y : G) K₁ ≤ K₁ ⊔ conjSub s K₁ := by
      intro z hz
      have hz' : (y : G)⁻¹ * z * y ∈ K₁ := mem_conjSub.mp hz
      have h2 : (y : G)⁻¹ * z * y ∈ conjClosure (oTwoUpper H) (mcOf T) := by
        rw [hKz]
        exact Subgroup.mem_sup_left hz'
      have h3' := (Subgroup.mem_normalizer_iff.mp (hKzn hy) _).mp h2
      have e : (y : G) * ((y : G)⁻¹ * z * y) * (y : G)⁻¹ = z := by group
      rw [e, hKz] at h3'
      exact h3'
    rcases SBc13.eq_or_eq_of_mem_cComp_of_le_sup hK₁ hK₂ hC hCle with h | h
    · exact Or.inl (by rw [h])
    · exact Or.inr (by rw [h])
  have hsup : imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁) =
      imageOTwoQuot (mcOf T) (conjClosure (oTwoUpper H) (mcOf T)) := by
    rw [hKz, q_image_sup hK₁G hK₂G]
  have hnormal : (imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁)).Normal := by
    rw [hsup]
    exact q_normal_image_of_normal (SBc13.kz_le_mcOf S hred) hKzn
  have hZ₁ := q_forall_comm_eq_one_of_equiv hnc (MulEquiv.refl ↥(imageOTwoQuot (mcOf T) K₁))
  have hZ₂ : ∀ n ∈ imageOTwoQuot (mcOf T) (conjSub s K₁),
      (∀ m ∈ imageOTwoQuot (mcOf T) (conjSub s K₁), n * m = m * n) → n = 1 := by
    rw [hconj]
    exact q_centreless_conj hZ₁ _
  have hZ := q_centreless_sup hcomm hZ₁ hZ₂
  have hE3 := q_exists_elemAbelian_pair (hr := ⟨Nat.prime_three⟩) hconj hcomm hdisj 3 h3
  have hE5 : p = 5 → ∃ E : Subgroup (OTwoQuot (mcOf T)),
      E ≤ imageOTwoQuot (mcOf T) K₁ ⊔ imageOTwoQuot (mcOf T) (conjSub s K₁) ∧
      IsElemAbelian 5 E ∧ Nat.card E = 5 ^ 2 := by
    intro hp5
    subst hp5
    exact q_exists_elemAbelian_pair (hr := ⟨by norm_num⟩) hconj hcomm hdisj 5 hp
  have hcen0 := q_centralizer_eq_bot (hNn := hnormal) h36 hlist iS S hred hmax _ hZ
    (by obtain ⟨E, hE, hEa, hEc⟩ := hE3; exact ⟨E, hE, hEa, hEc⟩)
    (fun hp5 => by obtain ⟨E, hE, hEa, hEc⟩ := hE5 hp5; exact ⟨E, hE, hEa, hEc⟩)
  refine ⟨hconj, hcomm, hdisj, hperm, hnormal, fun x hx => ?_, hZ₁⟩
  have hxc : x ∈ Subgroup.centralizer (↑(imageOTwoQuot (mcOf T) K₁ ⊔
      imageOTwoQuot (mcOf T) (conjSub s K₁)) : Set (OTwoQuot (mcOf T))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact (hx h hh).symm
  rw [hcen0, Subgroup.mem_bot] at hxc
  rw [hxc]
  exact one_mem _

end Facts


end CFSG.Quasithin
