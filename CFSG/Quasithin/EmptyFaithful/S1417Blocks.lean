module

public import CFSG.Quasithin.Background.StabSubBasics
public import CFSG.Quasithin.EmptyFaithful.S1417Natural
public import CFSG.Quasithin.Background.B1Basic

public section

namespace CFSG.Quasithin

namespace S1417

section General

variable {G : Type*} [Group G]

theorem exists_mul_of_mem_sup_of_commute {A B : Subgroup G} (hc : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a)
    {x : G} (hx : x ∈ A ⊔ B) : ∃ a ∈ A, ∃ b ∈ B, a * b = x := by
  have hA : A ≤ Subgroup.normalizer (B : Set G) := by
    intro a ha
    exact Subgroup.centralizer_le_normalizer (s := (B : Set G))
      (Subgroup.mem_centralizer_iff.mpr fun b hb => (hc a ha b hb).symm)
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right A B hA] at hx
  obtain ⟨a, ha, b, hb, h⟩ := Set.mem_mul.mp hx
  exact ⟨a, ha, b, hb, h⟩

theorem eq_of_mul_eq_of_inf_eq_bot {A B : Subgroup G} (hAB : A ⊓ B = ⊥) {a a' b b' : G}
    (ha : a ∈ A) (ha' : a' ∈ A) (hb : b ∈ B) (hb' : b' ∈ B) (h : a * b = a' * b') :
    a = a' ∧ b = b' := by
  have h1 : a'⁻¹ * a = b' * b⁻¹ := by
    calc a'⁻¹ * a = a'⁻¹ * (a * b) * b⁻¹ := by group
      _ = a'⁻¹ * (a' * b') * b⁻¹ := by rw [h]
      _ = b' * b⁻¹ := by group
  have h2 : a'⁻¹ * a ∈ A ⊓ B :=
    ⟨A.mul_mem (A.inv_mem ha') ha, by rw [h1]; exact B.mul_mem hb' (B.inv_mem hb)⟩
  rw [hAB, Subgroup.mem_bot] at h2
  have h3 : a = a' := by
    calc a = a' * (a'⁻¹ * a) := by group
      _ = a' := by rw [h2, mul_one]
  refine ⟨h3, ?_⟩
  rw [h3] at h
  exact mul_left_cancel h

end General

section Conj

variable {W : Type*} [CommGroup W]

theorem conjAut_mul (g h : MulAut W) (A : Subgroup (MulAut W)) :
    B1.conjAut (g * h) A = B1.conjAut g (B1.conjAut h A) := by
  ext x
  simp [B1.mem_conjAut, mul_assoc]

theorem conjAut_eq_of_mem {a : MulAut W} {L : Subgroup (MulAut W)} (ha : a ∈ L) :
    B1.conjAut a L = L := by
  ext x
  rw [B1.mem_conjAut]
  constructor
  · intro h
    have := L.mul_mem (L.mul_mem ha h) (L.inv_mem ha)
    simpa [mul_assoc] using this
  · intro h
    exact L.mul_mem (L.mul_mem (L.inv_mem ha) h) ha

theorem conjAut_eq_of_commute {a : MulAut W} {L : Subgroup (MulAut W)}
    (ha : ∀ b ∈ L, a * b = b * a) : B1.conjAut a L = L := by
  ext x
  rw [B1.mem_conjAut]
  constructor
  · intro h
    have h1 : a * (a⁻¹ * x * a) = (a⁻¹ * x * a) * a := ha _ h
    have h2 : x * a = (a⁻¹ * x * a) * a := by
      calc x * a = a * (a⁻¹ * x * a) := by group
        _ = (a⁻¹ * x * a) * a := h1
    have h3 : x = a⁻¹ * x * a := mul_right_cancel h2
    rw [h3]
    exact h
  · intro h
    have h1 : a * x = x * a := ha x h
    have h2 : a⁻¹ * x * a = x := by
      calc a⁻¹ * x * a = a⁻¹ * (x * a) := by group
        _ = a⁻¹ * (a * x) := by rw [h1]
        _ = x := by group
    rw [h2]
    exact h

theorem mem_stabSub_of_map_eq {U : Subgroup W} {g : MulAut W} (h : U.map g.toMonoidHom = U) :
    g ∈ stabSub U :=
  CFSG.Quasithin.StabLat.mem_stabSub_of_map_eq h

end Conj

section Two

variable {W : Type*} [CommGroup W] {L₁ L₂ : Subgroup (MulAut W)}

theorem commV_stable_of_commute (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a) {l : MulAut W}
    (hl : l ∈ L₁) {u : W} (hu : u ∈ commV L₂) : l u ∈ commV L₂ := by
  induction hu using Subgroup.closure_induction with
  | mem w hw =>
    obtain ⟨x, hx, v, rfl⟩ := hw
    refine Subgroup.subset_closure ⟨x, hx, l v, ?_⟩
    have hlx : l * x = x * l := hc l hl x hx
    have h1 : l (x v) = x (l v) := by
      have := congrArg (fun φ : MulAut W => φ v) hlx
      simpa using this
    rw [map_mul, map_inv, h1]
  | one => simp
  | mul a b _ _ ha hb => rw [map_mul]; exact (commV L₂).mul_mem ha hb
  | inv a _ ha => rw [map_inv]; exact (commV L₂).inv_mem ha

theorem apply_eq_of_mem_commV_of_commute (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hinf : commV L₁ ⊓ commV L₂ = ⊥) {l : MulAut W} (hl : l ∈ L₁) {u : W} (hu : u ∈ commV L₂) :
    l u = u := by
  have h1 : l u * u⁻¹ ∈ commV L₁ := Subgroup.subset_closure ⟨l, hl, u, rfl⟩
  have h2 : l u * u⁻¹ ∈ commV L₂ :=
    (commV L₂).mul_mem (commV_stable_of_commute hc hl hu) ((commV L₂).inv_mem hu)
  have h3 : l u * u⁻¹ ∈ commV L₁ ⊓ commV L₂ := ⟨h1, h2⟩
  rw [hinf, Subgroup.mem_bot] at h3
  exact mul_inv_eq_one.mp h3

theorem exists_mem_sup_apply_eq (hN₁ : ActsAsNaturalL2 L₁ (commV L₁))
    (hN₂ : ActsAsNaturalL2 L₂ (commV L₂)) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hinf : commV L₁ ⊓ commV L₂ = ⊥) {g : MulAut W} (hg₁ : g ∈ stabSub (commV L₁))
    (hg₂ : g ∈ stabSub (commV L₂)) :
    ∃ y ∈ L₁ ⊔ L₂, ∀ u ∈ commV L₁ ⊔ commV L₂, g u = y u := by
  have hc' : ∀ a ∈ L₂, ∀ b ∈ L₁, a * b = b * a := fun a ha b hb => (hc b hb a ha).symm
  have hinf' : commV L₂ ⊓ commV L₁ = ⊥ := by rw [inf_comm]; exact hinf
  obtain ⟨l₁, hl₁, h₁⟩ := exists_apply_eq_of_stab hN₁ (fun l hl u hu => commV_stable L₁ hl hu) hg₁
  obtain ⟨l₂, hl₂, h₂⟩ := exists_apply_eq_of_stab hN₂ (fun l hl u hu => commV_stable L₂ hl hu) hg₂
  refine ⟨l₁ * l₂, Subgroup.mul_mem_sup hl₁ hl₂, fun u hu => ?_⟩
  obtain ⟨u₁, hu₁, u₂, hu₂, rfl⟩ := Subgroup.mem_sup.mp hu
  have e1 : l₂ u₁ = u₁ := apply_eq_of_mem_commV_of_commute hc' hinf' hl₂ hu₁
  have e2 : l₁ (l₂ u₂) = l₂ u₂ :=
    apply_eq_of_mem_commV_of_commute hc hinf hl₁ (commV_stable L₂ hl₂ hu₂)
  have e3 : (l₁ * l₂) (u₁ * u₂) = l₁ u₁ * l₂ u₂ := by
    rw [MulAut.mul_apply, map_mul, e1, map_mul, e2]
  rw [e3, map_mul, h₁ u₁ hu₁, h₂ u₂ hu₂]

theorem mem_sup_of_fix {X : Subgroup (MulAut W)} (hN₁ : ActsAsNaturalL2 L₁ (commV L₁))
    (hN₂ : ActsAsNaturalL2 L₂ (commV L₂)) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hinf : commV L₁ ⊓ commV L₂ = ⊥) (hUtop : commV L₁ ⊔ commV L₂ = ⊤)
    (hcv₁ : ∀ g ∈ X, (commV L₁).map g.toMonoidHom = commV (B1.conjAut g L₁))
    (hcv₂ : ∀ g ∈ X, (commV L₂).map g.toMonoidHom = commV (B1.conjAut g L₂)) {g : MulAut W}
    (hg : g ∈ X) (h₁ : B1.conjAut g L₁ = L₁) (h₂ : B1.conjAut g L₂ = L₂) : g ∈ L₁ ⊔ L₂ := by
  have hs₁ : g ∈ stabSub (commV L₁) := mem_stabSub_of_map_eq (by rw [hcv₁ g hg, h₁])
  have hs₂ : g ∈ stabSub (commV L₂) := mem_stabSub_of_map_eq (by rw [hcv₂ g hg, h₂])
  obtain ⟨y, hy, hgy⟩ := exists_mem_sup_apply_eq hN₁ hN₂ hc hinf hs₁ hs₂
  have : g = y := MulEquiv.ext fun w => hgy w (by rw [hUtop]; exact Subgroup.mem_top w)
  rw [this]
  exact hy

theorem eq_sup_or_exists_swap {X : Subgroup (MulAut W)} (hN₁ : ActsAsNaturalL2 L₁ (commV L₁))
    (hN₂ : ActsAsNaturalL2 L₂ (commV L₂)) (hc : ∀ a ∈ L₁, ∀ b ∈ L₂, a * b = b * a)
    (hLinf : L₁ ⊓ L₂ = ⊥) (hinf : commV L₁ ⊓ commV L₂ = ⊥) (hUtop : commV L₁ ⊔ commV L₂ = ⊤)
    (hL₁X : L₁ ≤ X) (hL₂X : L₂ ≤ X)
    (hperm : ∀ g ∈ X, (B1.conjAut g L₁ = L₁ ∧ B1.conjAut g L₂ = L₂) ∨
      (B1.conjAut g L₁ = L₂ ∧ B1.conjAut g L₂ = L₁))
    (hcv₁ : ∀ g ∈ X, (commV L₁).map g.toMonoidHom = commV (B1.conjAut g L₁))
    (hcv₂ : ∀ g ∈ X, (commV L₂).map g.toMonoidHom = commV (B1.conjAut g L₂)) :
    X = L₁ ⊔ L₂ ∨ ∃ t ∈ X, t ^ 2 = 1 ∧ t ≠ 1 ∧ B1.conjAut t L₁ = L₂ ∧ B1.conjAut t L₂ = L₁ ∧
      X = (L₁ ⊔ L₂) ⊔ Subgroup.zpowers t := by
  have hL₁ne : L₁ ≠ L₂ := by
    intro h
    have h6 := (card_of_actsAsNaturalL2 hN₁).1
    rw [← h, inf_idem] at hLinf
    rw [hLinf, Subgroup.card_bot] at h6
    omega
  have hfix : ∀ g ∈ X, B1.conjAut g L₁ = L₁ → g ∈ L₁ ⊔ L₂ := by
    intro g hg h₁
    rcases hperm g hg with ⟨-, h₂⟩ | ⟨h, -⟩
    · exact mem_sup_of_fix hN₁ hN₂ hc hinf hUtop hcv₁ hcv₂ hg h₁ h₂
    · exact absurd (h₁.symm.trans h) hL₁ne
  have hJX : L₁ ⊔ L₂ ≤ X := sup_le hL₁X hL₂X
  by_cases hall : ∀ g ∈ X, B1.conjAut g L₁ = L₁
  · left
    exact le_antisymm (fun g hg => hfix g hg (hall g hg)) hJX
  · right
    push Not at hall
    obtain ⟨s, hsX, hs1⟩ := hall
    obtain ⟨hs₁, hs₂⟩ : B1.conjAut s L₁ = L₂ ∧ B1.conjAut s L₂ = L₁ := by
      rcases hperm s hsX with ⟨h, -⟩ | h
      · exact absurd h hs1
      · exact h
    have hss : s * s ∈ L₁ ⊔ L₂ := by
      refine hfix (s * s) (X.mul_mem hsX hsX) ?_
      rw [conjAut_mul, hs₁, hs₂]
    obtain ⟨a, ha, b, hb, hab⟩ := exists_mul_of_mem_sup_of_commute hc hss
    have hcab : a * b = b * a := hc a ha b hb
    have hsa : s * a * s⁻¹ ∈ L₂ := by
      have : s * a * s⁻¹ ∈ B1.conjAut s L₁ := by
        rw [B1.mem_conjAut]
        simpa [mul_assoc] using ha
      rwa [hs₁] at this
    have hsb : s * b * s⁻¹ ∈ L₁ := by
      have : s * b * s⁻¹ ∈ B1.conjAut s L₂ := by
        rw [B1.mem_conjAut]
        simpa [mul_assoc] using hb
      rwa [hs₂] at this
    have hprod : (s * b * s⁻¹) * (s * a * s⁻¹) = a * b := by
      calc (s * b * s⁻¹) * (s * a * s⁻¹) = s * (b * a) * s⁻¹ := by group
        _ = s * (a * b) * s⁻¹ := by rw [hcab]
        _ = s * (s * s) * s⁻¹ := by rw [hab]
        _ = s * s := by group
        _ = a * b := hab.symm
    obtain ⟨-, hsab⟩ := eq_of_mul_eq_of_inf_eq_bot hLinf hsb ha hsa hb hprod
    refine ⟨s * a⁻¹, X.mul_mem hsX (X.inv_mem (hL₁X ha)), ?_, ?_, ?_, ?_, ?_⟩
    · have h1 : s * a⁻¹ * s⁻¹ = b⁻¹ := by
        have := congrArg (fun z => z⁻¹) hsab
        simpa [mul_assoc] using this
      calc (s * a⁻¹) ^ 2 = (s * a⁻¹) * (s * a⁻¹) := pow_two _
        _ = (s * a⁻¹ * s⁻¹) * (s * s) * a⁻¹ := by group
        _ = b⁻¹ * (a * b) * a⁻¹ := by rw [h1, ← hab]
        _ = 1 := by rw [hcab]; group
    · intro h
      have h1 : B1.conjAut (s * a⁻¹) L₁ = B1.conjAut 1 L₁ := by rw [h]
      rw [conjAut_mul, conjAut_eq_of_mem (L₁.inv_mem ha), hs₁] at h1
      have h2 : B1.conjAut 1 L₁ = L₁ := by ext x; simp [B1.mem_conjAut]
      rw [h2] at h1
      exact hL₁ne h1.symm
    · rw [conjAut_mul, conjAut_eq_of_mem (L₁.inv_mem ha), hs₁]
    · have hcomm : ∀ y ∈ L₂, a⁻¹ * y = y * a⁻¹ := fun y hy =>
        (Commute.inv_left (show Commute a y from hc a ha y hy)).eq
      rw [conjAut_mul, conjAut_eq_of_commute hcomm, hs₂]
    · apply le_antisymm
      · intro g hg
        rcases hperm g hg with ⟨h₁, -⟩ | ⟨h₁, h₂⟩
        · exact Subgroup.mem_sup_left (hfix g hg h₁)
        · have hgt : g * (s * a⁻¹) ∈ L₁ ⊔ L₂ := by
            refine hfix _ (X.mul_mem hg (X.mul_mem hsX (X.inv_mem (hL₁X ha)))) ?_
            rw [conjAut_mul, conjAut_mul, conjAut_eq_of_mem (L₁.inv_mem ha), hs₁, h₂]
          have : g = (g * (s * a⁻¹)) * (s * a⁻¹)⁻¹ := by group
          rw [this]
          refine Subgroup.mul_mem _ (Subgroup.mem_sup_left hgt) (Subgroup.mem_sup_right ?_)
          exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
      · refine sup_le hJX ?_
        rw [Subgroup.zpowers_le]
        exact X.mul_mem hsX (X.inv_mem (hL₁X ha))

theorem eq_top_of_commV_eq_top {L : Subgroup (MulAut W)} (hN : ActsAsNaturalL2 L (commV L))
    (htop : commV L = ⊤) : L = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have hg : g ∈ stabSub (commV L) := by
    rw [htop]
    intro u
    simp
  obtain ⟨l, hl, hlg⟩ := exists_apply_eq_of_stab hN (fun l hl u hu => commV_stable L hl hu) hg
  have : l = g := MulEquiv.ext fun w => hlg w (by rw [htop]; exact Subgroup.mem_top w)
  rw [← this]
  exact hl

end Two

end S1417

end CFSG.Quasithin
