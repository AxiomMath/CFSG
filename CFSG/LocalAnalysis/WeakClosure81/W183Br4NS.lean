module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open Subgroup

structure Br4TwoSimple (S : Type) [Group S] (A₁ A₂ : Subgroup S) : Prop where
  normal₁ : A₁.Normal
  normal₂ : A₂.Normal
  simple₁ : IsSimpleGroup ↥A₁
  simple₂ : IsSimpleGroup ↥A₂
  nonab₁ : ∃ a ∈ A₁, ∃ b ∈ A₁, a * b ≠ b * a
  nonab₂ : ∃ a ∈ A₂, ∃ b ∈ A₂, a * b ≠ b * a
  disj : A₁ ⊓ A₂ = ⊥
  sup : A₁ ⊔ A₂ = ⊤

namespace Br4TwoSimple

variable {S : Type} [Group S] {A₁ A₂ : Subgroup S}

theorem symm (h : Br4TwoSimple S A₁ A₂) : Br4TwoSimple S A₂ A₁ :=
  ⟨h.normal₂, h.normal₁, h.simple₂, h.simple₁, h.nonab₂, h.nonab₁, by rw [inf_comm, h.disj],
    by rw [sup_comm, h.sup]⟩

theorem commute (h : Br4TwoSimple S A₁ A₂) {a b : S} (ha : a ∈ A₁) (hb : b ∈ A₂) :
    a * b = b * a :=
  haveI := h.normal₁
  haveI := h.normal₂
  Subgroup.commute_of_normal_of_disjoint A₁ A₂ h.normal₁ h.normal₂ (disjoint_iff.2 h.disj) a b
    ha hb

theorem commutator_left (h : Br4TwoSimple S A₁ A₂) : ⁅A₁, A₁⁆ = A₁ := by
  haveI := h.normal₁
  haveI := h.simple₁
  have hle : ⁅A₁, A₁⁆ ≤ A₁ := commutator_le_left (H₁ := A₁) (H₂ := A₁)
  have hHnormal : ((⁅A₁, A₁⁆ : Subgroup S).subgroupOf A₁).Normal :=
    (commutator_normal (H₁ := A₁) (H₂ := A₁)).subgroupOf A₁
  haveI := hHnormal
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((⁅A₁, A₁⁆ : Subgroup S).subgroupOf A₁) with
    hbot | htop
  · exfalso
    have hKbot : (⁅A₁, A₁⁆ : Subgroup S) = ⊥ := by
      have hmap : ((⁅A₁, A₁⁆ : Subgroup S).subgroupOf A₁).map A₁.subtype = ⁅A₁, A₁⁆ :=
        map_subgroupOf_eq_of_le hle
      rw [hbot, Subgroup.map_bot] at hmap
      exact hmap.symm
    have hcent : A₁ ≤ Subgroup.centralizer (A₁ : Set S) :=
      (commutator_eq_bot_iff_le_centralizer (H₁ := A₁) (H₂ := A₁)).mp hKbot
    obtain ⟨a, ha, b, hb, hab⟩ := h.nonab₁
    exact hab (Subgroup.mem_centralizer_iff.mp (hcent ha) b hb).symm
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)

theorem commutator_top (h : Br4TwoSimple S A₁ A₂) : ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ = ⊤ := by
  have hmono₁ : ⁅A₁, A₁⁆ ≤ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ :=
    commutator_mono le_top le_top
  rw [commutator_left h] at hmono₁
  have hmono₂ : ⁅A₂, A₂⁆ ≤ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ :=
    commutator_mono le_top le_top
  rw [commutator_left h.symm] at hmono₂
  have htop : A₁ ⊔ A₂ ≤ ⁅(⊤ : Subgroup S), (⊤ : Subgroup S)⁆ := sup_le hmono₁ hmono₂
  rw [h.sup] at htop
  exact le_antisymm le_top htop

private theorem w183br4_inf_centralizer_eq_bot_of_isSimpleGroup {G : Type*} [Group G]
    {H : Subgroup G} [IsSimpleGroup ↥H]
    (hnab : ∃ a ∈ H, ∃ b ∈ H, a * b ≠ b * a) :
    H ⊓ Subgroup.centralizer (H : Set G) = ⊥ := by
  have hZcenter : (H ⊓ Subgroup.centralizer (H : Set G)).subgroupOf H ≤
      Subgroup.center ↥H := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 (g : G) g.2)
  haveI : ((H ⊓ Subgroup.centralizer (H : Set G)).subgroupOf H).Normal :=
    Subgroup.normal_of_le_center hZcenter
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((H ⊓ Subgroup.centralizer (H : Set G)).subgroupOf H) with hZbot | hZtop
  · have hd := Subgroup.subgroupOf_eq_bot.mp hZbot
    have h := disjoint_iff.mp hd
    rwa [inf_eq_left.mpr inf_le_left] at h
  · exfalso
    obtain ⟨a, ha, b, hb, hab⟩ := hnab
    have hle := Subgroup.subgroupOf_eq_top.mp hZtop
    exact hab ((Subgroup.mem_centralizer_iff.mp (hle ha).2 b hb).symm)

private theorem w183br4_center_eq_bot (h : Br4TwoSimple S A₁ A₂) :
    Subgroup.center S = ⊥ := by
  haveI : IsSimpleGroup ↥A₁ := h.simple₁
  haveI : IsSimpleGroup ↥A₂ := h.simple₂
  have hbot₁ : A₁ ⊓ Subgroup.centralizer (A₁ : Set S) = ⊥ :=
    w183br4_inf_centralizer_eq_bot_of_isSimpleGroup h.nonab₁
  have hbot₂ : A₂ ⊓ Subgroup.centralizer (A₂ : Set S) = ⊥ :=
    w183br4_inf_centralizer_eq_bot_of_isSimpleGroup h.nonab₂
  rw [eq_bot_iff]
  intro z hz
  rw [Subgroup.mem_bot]
  have hzsup : z ∈ A₁ ⊔ A₂ := by rw [h.sup]; trivial
  haveI := h.normal₁
  obtain ⟨y, hy, w, hw, hyw⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := A₁) (t := A₂) (x := z)).mp hzsup
  have hy_eq : z * w⁻¹ = y := by rw [← hyw]; group
  have hw_eq : y⁻¹ * z = w := by rw [← hyw]; group
  have hycent : y ∈ Subgroup.centralizer (A₁ : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * y = x * (z * w⁻¹) := by rw [← hy_eq]
      _ = (x * z) * w⁻¹ := by group
      _ = (z * x) * w⁻¹ := by rw [Subgroup.mem_center_iff.mp hz x]
      _ = z * (x * w⁻¹) := by group
      _ = z * (w⁻¹ * x) := by rw [h.commute hx (A₂.inv_mem hw)]
      _ = (z * w⁻¹) * x := by group
      _ = y * x := by rw [hy_eq]
  have hy_one : y = 1 := by
    have : y ∈ A₁ ⊓ Subgroup.centralizer (A₁ : Set S) := ⟨hy, hycent⟩
    rw [hbot₁] at this
    simpa using this
  have hwcent : w ∈ Subgroup.centralizer (A₂ : Set S) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    calc x * w = x * (y⁻¹ * z) := by rw [← hw_eq]
      _ = (x * y⁻¹) * z := by group
      _ = (y⁻¹ * x) * z := by rw [← h.commute (A₁.inv_mem hy) hx]
      _ = y⁻¹ * (x * z) := by group
      _ = y⁻¹ * (z * x) := by rw [Subgroup.mem_center_iff.mp hz x]
      _ = (y⁻¹ * z) * x := by group
      _ = w * x := by rw [hw_eq]
  have hw_one : w = 1 := by
    have : w ∈ A₂ ⊓ Subgroup.centralizer (A₂ : Set S) := ⟨hw, hwcent⟩
    rw [hbot₂] at this
    simpa using this
  rw [← hyw, hy_one, hw_one, one_mul]

private theorem w183br4_inf_eq_bot_or_le_of_isSimpleGroup {G : Type*} [Group G]
    {K H : Subgroup G} [IsSimpleGroup ↥H] (hK : K.Normal) : K ⊓ H = ⊥ ∨ H ≤ K := by
  haveI : (K.subgroupOf H).Normal := hK.subgroupOf H
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf H) with hbot | htop
  · left
    exact disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot)
  · right
    exact Subgroup.subgroupOf_eq_top.mp htop

theorem eq_bot_of_inf_eq_bot (h : Br4TwoSimple S A₁ A₂) {M : Subgroup S} (hM : M.Normal)
    (h₁ : M ⊓ A₁ = ⊥) (h₂ : M ⊓ A₂ = ⊥) : M = ⊥ := by
  haveI := hM
  haveI := h.normal₁
  haveI := h.normal₂
  have hc₁ : ⁅M, A₁⁆ = ⊥ := by
    have hle : ⁅M, A₁⁆ ≤ M ⊓ A₁ :=
      le_inf (commutator_le_left (H₁ := M) (H₂ := A₁))
        (commutator_le_right (H₁ := M) (H₂ := A₁))
    rw [h₁] at hle
    exact le_bot_iff.mp hle
  have hc₂ : ⁅M, A₂⁆ = ⊥ := by
    have hle : ⁅M, A₂⁆ ≤ M ⊓ A₂ :=
      le_inf (commutator_le_left (H₁ := M) (H₂ := A₂))
        (commutator_le_right (H₁ := M) (H₂ := A₂))
    rw [h₂] at hle
    exact le_bot_iff.mp hle
  have hc : ⁅M, A₁ ⊔ A₂⁆ = ⊥ := by
    rw [commutator_sup_left (N := M) (H := A₁) (K := A₂), hc₁, hc₂, sup_idem]
  have hMsup : M ≤ Subgroup.centralizer ((A₁ ⊔ A₂ : Subgroup S) : Set S) :=
    commutator_eq_bot_iff_le_centralizer.mp hc
  have hMcenter : M ≤ Subgroup.center S := by
    rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, ← h.sup]
    exact hMsup
  rw [w183br4_center_eq_bot h] at hMcenter
  exact le_bot_iff.mp hMcenter

theorem le_or_le_of_ne_bot (h : Br4TwoSimple S A₁ A₂) {M : Subgroup S} (hM : M.Normal)
    (hne : M ≠ ⊥) : A₁ ≤ M ∨ A₂ ≤ M := by
  haveI : IsSimpleGroup ↥A₁ := h.simple₁
  haveI : IsSimpleGroup ↥A₂ := h.simple₂
  rcases w183br4_inf_eq_bot_or_le_of_isSimpleGroup (K := M) (H := A₁) hM with h₁ | h₁
  · rcases w183br4_inf_eq_bot_or_le_of_isSimpleGroup (K := M) (H := A₂) hM with h₂ | h₂
    · exact absurd (eq_bot_of_inf_eq_bot h hM h₁ h₂) hne
    · exact Or.inr h₂
  · exact Or.inl h₁

theorem eq_bot_of_isPGroup [Finite S] (h : Br4TwoSimple S A₁ A₂) {M : Subgroup S}
    (hM : M.Normal) (h3 : IsPGroup 3 ↥M) : M = ⊥ := by
  by_contra hne
  haveI : IsSimpleGroup ↥A₁ := h.simple₁
  haveI : IsSimpleGroup ↥A₂ := h.simple₂
  rcases le_or_le_of_ne_bot h hM hne with hle | hle
  · obtain ⟨a, ha, b, hb, hab⟩ := h.nonab₁
    have hA₁p : IsPGroup 3 ↥A₁ := fun x => by
      obtain ⟨k, hk⟩ := h3 ⟨(x : S), hle x.2⟩
      exact ⟨k, Subtype.ext (congrArg (fun g : ↥M => (g : S)) hk)⟩
    haveI : Group.IsNilpotent ↥A₁ := IsPGroup.isNilpotent (p := 3) hA₁p
    exact hab (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A₁) ⟨b, hb⟩))
  · obtain ⟨a, ha, b, hb, hab⟩ := h.nonab₂
    have hA₂p : IsPGroup 3 ↥A₂ := fun x => by
      obtain ⟨k, hk⟩ := h3 ⟨(x : S), hle x.2⟩
      exact ⟨k, Subtype.ext (congrArg (fun g : ↥M => (g : S)) hk)⟩
    haveI : Group.IsNilpotent ↥A₂ := IsPGroup.isNilpotent (p := 3) hA₂p
    exact hab (congrArg Subtype.val (mul_comm (⟨a, ha⟩ : ↥A₂) ⟨b, hb⟩))

theorem eq_bot_of_not_dvd [Finite S] (h : Br4TwoSimple S A₁ A₂) (h₁ : 3 ∣ Nat.card ↥A₁)
    (h₂ : 3 ∣ Nat.card ↥A₂) {M : Subgroup S} (hM : M.Normal) (h3 : ¬ 3 ∣ Nat.card ↥M) :
    M = ⊥ := by
  by_contra hne
  rcases le_or_le_of_ne_bot h hM hne with hle | hle
  · exact h3 (h₁.trans (Subgroup.card_dvd_of_le hle))
  · exact h3 (h₂.trans (Subgroup.card_dvd_of_le hle))

end Br4TwoSimple

theorem br4_elem_sup {X : Type} [Group X] {E₁ E₂ : Subgroup X}
    (hc : ∀ a ∈ E₁, ∀ b ∈ E₂, a * b = b * a) (hd : E₁ ⊓ E₂ = ⊥) (h₁ : IsElemAbelian 3 E₁)
    (h₂ : IsElemAbelian 3 E₂) (c₁ : Nat.card ↥E₁ = 9) (c₂ : Nat.card ↥E₂ = 9) :
    IsElemAbelian 3 (E₁ ⊔ E₂) ∧ Nat.card ↥(E₁ ⊔ E₂) = 81 := by
  haveI : IsMulCommutative ↥E₁ := h₁.1
  haveI : IsMulCommutative ↥E₂ := h₂.1
  let φ : (↥E₁ × ↥E₂) →* X :=
    { toFun := fun p => (p.1 : X) * (p.2 : X)
      map_one' := by simp
      map_mul' := fun p q => by
        have hcomm : (q.1 : X) * (p.2 : X) = (p.2 : X) * (q.1 : X) :=
          hc q.1 q.1.2 p.2 p.2.2
        change (p.1 : X) * (q.1 : X) * ((p.2 : X) * (q.2 : X)) =
          (p.1 : X) * (p.2 : X) * ((q.1 : X) * (q.2 : X))
        calc (p.1 : X) * (q.1 : X) * ((p.2 : X) * (q.2 : X))
            = (p.1 : X) * ((q.1 : X) * (p.2 : X)) * (q.2 : X) := by group
          _ = (p.1 : X) * ((p.2 : X) * (q.1 : X)) * (q.2 : X) := by rw [hcomm]
          _ = (p.1 : X) * (p.2 : X) * ((q.1 : X) * (q.2 : X)) := by group }
  have hφrange : φ.range = E₁ ⊔ E₂ := by
    apply le_antisymm
    · rintro x ⟨p, rfl⟩
      exact Subgroup.mul_mem_sup p.1.2 p.2.2
    · refine sup_le ?_ ?_
      · intro a ha
        exact ⟨(⟨a, ha⟩, 1), by simp [φ]⟩
      · intro b hb
        exact ⟨(1, ⟨b, hb⟩), by simp [φ]⟩
  have hinj : Function.Injective φ := by
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    have hval : (a : X) * (b : X) = (c : X) * (d : X) := h
    have h' : (c : X)⁻¹ * (a : X) = (d : X) * (b : X)⁻¹ := by
      calc (c : X)⁻¹ * (a : X)
          = (c : X)⁻¹ * ((a : X) * (b : X)) * (b : X)⁻¹ := by group
        _ = (c : X)⁻¹ * ((c : X) * (d : X)) * (b : X)⁻¹ := by rw [hval]
        _ = (d : X) * (b : X)⁻¹ := by group
    have hm₁ : (c : X)⁻¹ * (a : X) ∈ E₁ := E₁.mul_mem (E₁.inv_mem c.2) a.2
    have hm₂ : (d : X) * (b : X)⁻¹ ∈ E₂ := E₂.mul_mem d.2 (E₂.inv_mem b.2)
    have hm : (c : X)⁻¹ * (a : X) ∈ E₁ ⊓ E₂ := ⟨hm₁, h'.symm ▸ hm₂⟩
    rw [hd] at hm
    have hca : (c : X)⁻¹ * (a : X) = 1 := by simpa using hm
    have hac : (a : X) = (c : X) := by
      have := congrArg (fun z : X => (c : X) * z) hca
      simpa using this
    have hbd : (b : X) = (d : X) := by
      rw [hac] at hval
      exact mul_left_cancel hval
    exact Prod.ext (Subtype.ext hac) (Subtype.ext hbd)
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI : IsMulCommutative (↥E₁ × ↥E₂) := inferInstance
    exact hφrange ▸ (Subgroup.range_isMulCommutative (f := φ))
  · intro x hx
    rw [← hφrange] at hx
    obtain ⟨p, hp⟩ := hx
    rw [← hp]
    have hp3 : p ^ 3 = 1 := by
      obtain ⟨a, b⟩ := p
      have ha : a ^ 3 = (1 : ↥E₁) := Subtype.ext (h₁.2 (a : X) a.2)
      have hb : b ^ 3 = (1 : ↥E₂) := Subtype.ext (h₂.2 (b : X) b.2)
      calc ((a, b) ^ 3 : ↥E₁ × ↥E₂) = (a ^ 3, b ^ 3) := rfl
        _ = (1, 1) := by rw [ha, hb]
        _ = 1 := rfl
    rw [← map_pow, hp3, map_one]
  · rw [← hφrange]
    rw [← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv]
    rw [Nat.card_prod, c₁, c₂]

end CFSG.LocalAnalysis.WeakClosure81

end
