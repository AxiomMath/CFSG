module

public import CFSG.Quasithin.EmptyFaithful.S153EDefs2

public section

namespace CFSG.Quasithin

namespace S153E57

variable {Q : Type*} [CommGroup Q]

@[expose] def IsInv (K : Subgroup (MulAut Q)) (B : Subgroup Q) : Prop :=
  ∀ k ∈ K, ∀ b ∈ B, k b ∈ B

@[expose] def fixSub (g : MulAut Q) : Subgroup Q where
  carrier := {x | g x = x}
  one_mem' := map_one g
  mul_mem' := fun {a b} ha hb => by
    change g (a * b) = a * b
    rw [map_mul, show g a = a from ha, show g b = b from hb]
  inv_mem' := fun {a} ha => by
    change g a⁻¹ = a⁻¹
    rw [map_inv, show g a = a from ha]

theorem isInv_bot (K : Subgroup (MulAut Q)) : IsInv K (⊥ : Subgroup Q) := by
  intro k _ b hb
  rw [Subgroup.mem_bot] at hb ⊢
  rw [hb]
  exact map_one k

theorem isInv_top (K : Subgroup (MulAut Q)) : IsInv K (⊤ : Subgroup Q) :=
  fun _ _ _ _ => Subgroup.mem_top _

theorem irr_inv {K : Subgroup (MulAut Q)} {B : Subgroup Q} (h : IsIrrOn153 K B) : IsInv K B := h.2.1

theorem IsInv.inf {K : Subgroup (MulAut Q)} {B C : Subgroup Q} (hB : IsInv K B) (hC : IsInv K C) :
    IsInv K (B ⊓ C) :=
  fun k hk b hb => ⟨hB k hk b hb.1, hC k hk b hb.2⟩

theorem IsInv.sup {K : Subgroup (MulAut Q)} {B C : Subgroup Q} (hB : IsInv K B) (hC : IsInv K C) :
    IsInv K (B ⊔ C) := by
  intro k hk b hb
  obtain ⟨x, hx, y, hy, rfl⟩ := Subgroup.mem_sup.1 hb
  rw [map_mul]
  exact Subgroup.mul_mem_sup (hB k hk x hx) (hC k hk y hy)

theorem sSup_stable (g : MulAut Q) {S : Set (Subgroup Q)}
    (h : ∀ J ∈ S, ∀ x ∈ J, g x ∈ sSup S) : ∀ x ∈ sSup S, g x ∈ sSup S := by
  intro x hx
  have hx' : x ∈ ⨆ J : S, (J : Subgroup Q) := by rwa [← sSup_eq_iSup']
  refine Subgroup.iSup_induction (fun J : S => (J : Subgroup Q)) (C := fun y => g y ∈ sSup S) hx'
    ?_ ?_ ?_
  · intro J y hy
    exact h J J.2 y hy
  · rw [map_one]
    exact one_mem _
  · intro x y hx hy
    rw [map_mul]
    exact mul_mem hx hy

theorem isInv_sSup {K : Subgroup (MulAut Q)} {S : Set (Subgroup Q)} (h : ∀ J ∈ S, IsInv K J) :
    IsInv K (sSup S) :=
  fun k hk x hx => sSup_stable k (fun J hJ y hy => le_sSup hJ (h J hJ k hk y hy)) x hx

theorem IsInv.map {K H : Subgroup (MulAut Q)} (hKH : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    {g : MulAut Q} (hg : g ∈ H) {B : Subgroup Q} (hB : IsInv K B) :
    IsInv K (B.map (g : Q →* Q)) := by
  intro k hk y hy
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
  have hk' : g⁻¹ * k * g ∈ K := by
    have := hKH g⁻¹ (H.inv_mem hg) k hk
    simpa using this
  refine Subgroup.mem_map.2 ⟨(g⁻¹ * k * g) x, hB _ hk' x hx, ?_⟩
  change g ((g⁻¹ * k * g) x) = k (g x)
  rw [MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self]

theorem isIrr_map {K H : Subgroup (MulAut Q)} (hKH : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K)
    {g : MulAut Q} (hg : g ∈ H) {B : Subgroup Q} (hB : IsIrrOn153 K B) :
    IsIrrOn153 K (B.map (g : Q →* Q)) := by
  have hinj : Function.Injective (g : Q →* Q) := g.injective
  refine ⟨?_, (irr_inv hB).map hKH hg, fun B' hB'le hB'inv => ?_⟩
  · intro h
    exact hB.1 ((Subgroup.map_eq_bot_iff_of_injective B hinj).1 h)
  · have hle : B'.map ((g⁻¹ : MulAut Q) : Q →* Q) ≤ B := by
      intro y hy
      obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 (hB'le hx)
      have : (g⁻¹ : MulAut Q) x = z := by
        rw [← hzx]
        change g⁻¹ (g z) = z
        exact MulAut.inv_apply_self _ _ _
      change (g⁻¹ : MulAut Q) x ∈ B
      rw [this]
      exact hz
    have hinv : IsInv K (B'.map ((g⁻¹ : MulAut Q) : Q →* Q)) :=
      (show IsInv K B' from hB'inv).map hKH (H.inv_mem hg)
    rcases hB.2.2 _ hle hinv with h | h
    · left
      rw [Subgroup.eq_bot_iff_forall]
      intro x hx
      have : (g⁻¹ : MulAut Q) x ∈ B'.map ((g⁻¹ : MulAut Q) : Q →* Q) := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
      rw [h, Subgroup.mem_bot] at this
      have h2 : g ((g⁻¹ : MulAut Q) x) = x := MulAut.apply_inv_self _ _ _
      rw [this, map_one] at h2
      exact h2.symm
    · right
      ext x
      constructor
      · intro hx
        have : (g⁻¹ : MulAut Q) x ∈ B'.map ((g⁻¹ : MulAut Q) : Q →* Q) := Subgroup.mem_map.2 ⟨x, hx, rfl⟩
        rw [h] at this
        exact Subgroup.mem_map.2 ⟨_, this, MulAut.apply_inv_self _ _ _⟩
      · intro hx
        obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.1 hx
        rw [← h] at hy
        obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.1 hy
        change g ((g⁻¹ : MulAut Q) x') ∈ B'
        rw [MulAut.apply_inv_self]
        exact hx'

theorem card_map_eq (g : MulAut Q) (B : Subgroup Q) : Nat.card (B.map (g : Q →* Q)) = Nat.card B :=
  Subgroup.card_map_of_injective g.injective

theorem exists_irr_le [Finite Q] {K : Subgroup (MulAut Q)} {B : Subgroup Q} (hB : IsInv K B)
    (hne : B ≠ ⊥) : ∃ J ≤ B, IsIrrOn153 K J := by
  classical
  obtain ⟨J, ⟨hJB, hJinv, hJne⟩, hmin⟩ := WellFounded.has_min (wellFounded_lt (α := Subgroup Q))
    {J : Subgroup Q | J ≤ B ∧ IsInv K J ∧ J ≠ ⊥} ⟨B, le_rfl, hB, hne⟩
  refine ⟨J, hJB, hJne, hJinv, fun B' hB'J hB'inv => ?_⟩
  by_contra hcon
  push Not at hcon
  exact hmin B' ⟨hB'J.trans hJB, hB'inv, hcon.1⟩ (lt_of_le_of_ne hB'J hcon.2)

theorem exists_compl [Finite Q] {K : Subgroup (MulAut Q)}
    (hsum : sSup {J : Subgroup Q | IsIrrOn153 K J} = ⊤) {B : Subgroup Q} (hB : IsInv K B) :
    ∃ B' : Subgroup Q, IsInv K B' ∧ B ⊓ B' = ⊥ ∧ B ⊔ B' = ⊤ := by
  classical
  let S : Set (Subgroup Q) := {B' | IsInv K B' ∧ B ⊓ B' = ⊥}
  obtain ⟨B', ⟨hB'inv, hB'dis⟩, hmax⟩ := Set.Finite.exists_maximal (Set.toFinite S)
    ⟨⊥, isInv_bot K, inf_bot_eq B⟩
  refine ⟨B', hB'inv, hB'dis, ?_⟩
  by_contra hne
  have hex : ∃ J, IsIrrOn153 K J ∧ ¬ J ≤ B ⊔ B' := by
    by_contra hcon
    push Not at hcon
    apply hne
    rw [eq_top_iff, ← hsum]
    exact sSup_le fun J hJ => hcon J hJ
  obtain ⟨J, hJ, hJn⟩ := hex
  have hinf : J ⊓ (B ⊔ B') = ⊥ := by
    rcases hJ.2.2 (J ⊓ (B ⊔ B')) inf_le_left ((irr_inv hJ).inf (hB.sup hB'inv)) with h | h
    · exact h
    · exact absurd (h ▸ inf_le_right) hJn
  have hS : B' ⊔ J ∈ S := by
    refine ⟨hB'inv.sup (irr_inv hJ), ?_⟩
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    obtain ⟨hxB, hxBJ⟩ := Subgroup.mem_inf.1 hx
    obtain ⟨b', hb', j, hj, rfl⟩ := Subgroup.mem_sup.1 hxBJ
    have hj' : j ∈ J ⊓ (B ⊔ B') := by
      refine ⟨hj, ?_⟩
      have hjeq : j = (b' * j) * b'⁻¹ := by
        rw [mul_comm b' j]
        exact (mul_inv_cancel_right j b').symm
      rw [hjeq]
      exact (B ⊔ B').mul_mem (Subgroup.mem_sup_left hxB)
        ((B ⊔ B').inv_mem (Subgroup.mem_sup_right hb'))
    rw [hinf, Subgroup.mem_bot] at hj'
    subst hj'
    have : b' * 1 ∈ B ⊓ B' := ⟨hxB, by simpa using hb'⟩
    rw [hB'dis, Subgroup.mem_bot] at this
    exact this
  have hle : B' ≤ B' ⊔ J := le_sup_left
  have hle2 : B' ⊔ J ≤ B' := hmax hS hle
  apply hJ.1
  rw [eq_bot_iff]
  intro x hx
  have h1 : x ∈ B ⊔ B' := Subgroup.mem_sup_right (hle2 (Subgroup.mem_sup_right hx))
  have h2 : x ∈ J ⊓ (B ⊔ B') := ⟨hx, h1⟩
  rw [hinf] at h2
  exact h2

theorem sSup_irr_eq_top [Finite Q] [Nontrivial Q] {K H : Subgroup (MulAut Q)}
    (hH : IsIrrOn153 H ⊤) (hKH : ∀ h ∈ H, ∀ k ∈ K, h * k * h⁻¹ ∈ K) :
    sSup {J : Subgroup Q | IsIrrOn153 K J} = ⊤ := by
  obtain ⟨J₀, -, hJ₀⟩ := exists_irr_le (K := K) (isInv_top K) top_ne_bot
  let S : Subgroup Q := ⨆ h : H, J₀.map (((h : H) : MulAut Q) : Q →* Q)
  have hSinv : IsInv H S := by
    intro g hg x hx
    refine Subgroup.iSup_induction (fun h : H => J₀.map (((h : H) : MulAut Q) : Q →* Q))
      (C := fun y => g y ∈ S) hx ?_ ?_ ?_
    · intro h y hy
      obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.1 hy
      refine Subgroup.mem_iSup_of_mem (⟨g, hg⟩ * h) (Subgroup.mem_map.2 ⟨a, ha, ?_⟩)
      rfl
    · rw [map_one]; exact one_mem _
    · intro x y hx hy
      rw [map_mul]
      exact mul_mem hx hy
  have hSne : S ≠ ⊥ := by
    intro hbot
    apply hJ₀.1
    rw [eq_bot_iff, ← hbot]
    exact (le_iSup (fun h : H => J₀.map (((h : H) : MulAut Q) : Q →* Q)) 1).trans' (fun x hx =>
      Subgroup.mem_map.2 ⟨x, hx, rfl⟩)
  have hSeq : S = ⊤ := by
    rcases hH.2.2 S le_top hSinv with h | h
    · exact absurd h hSne
    · exact h
  rw [eq_top_iff, ← hSeq]
  exact iSup_le fun h => le_sSup (isIrr_map hKH h.2 hJ₀)

theorem stable_of_irr [Finite Q] {K : Subgroup (MulAut Q)}
    (hsum : sSup {J : Subgroup Q | IsIrrOn153 K J} = ⊤) {g : MulAut Q}
    (hg : ∀ J : Subgroup Q, IsIrrOn153 K J → ∀ x ∈ J, g x ∈ J) {B : Subgroup Q} (hB : IsInv K B) :
    ∀ x ∈ B, g x ∈ B := by
  let S : Set (Subgroup Q) := {J | IsIrrOn153 K J ∧ J ≤ B}
  have hB₀le : sSup S ≤ B := sSup_le fun J hJ => hJ.2
  have hB₀inv : IsInv K (sSup S) := isInv_sSup fun J hJ => hJ.1.2.1
  have hB₀stab : ∀ x ∈ sSup S, g x ∈ sSup S :=
    sSup_stable g fun J hJ x hx => le_sSup hJ (hg J hJ.1 x hx)
  obtain ⟨C, hCinv, hdis, hsup⟩ := exists_compl hsum hB₀inv
  have hBC : B ⊓ C = ⊥ := by
    by_contra hne
    obtain ⟨J, hJle, hJ⟩ := exists_irr_le (hB.inf hCinv) hne
    have h1 : J ≤ sSup S := le_sSup ⟨hJ, hJle.trans inf_le_left⟩
    have h2 : J ≤ sSup S ⊓ C := le_inf h1 (hJle.trans inf_le_right)
    rw [hdis] at h2
    exact hJ.1 (le_bot_iff.1 h2)
  have hBeq : B = sSup S := by
    have h1 : (sSup S ⊔ C) ⊓ B = sSup S ⊔ C ⊓ B := sup_inf_assoc_of_le C hB₀le
    rw [hsup, top_inf_eq, inf_comm C B, hBC, sup_bot_eq] at h1
    exact h1
  rw [hBeq]
  exact hB₀stab

theorem isPGroup_two_of_mul_self (hQ : ∀ q : Q, q * q = 1) (B : Subgroup Q) : IsPGroup 2 B := by
  intro x
  refine ⟨1, ?_⟩
  apply Subtype.ext
  have := hQ x
  simpa [pow_two] using this

theorem exists_fixed_of_isPGroup [Finite Q] {S : Subgroup (MulAut Q)} (hS : IsPGroup 2 S)
    {B : Subgroup Q} (hB : ∀ s ∈ S, ∀ b ∈ B, s b ∈ B) (hBne : B ≠ ⊥) (hB2 : IsPGroup 2 B) :
    ∃ x ∈ B, x ≠ 1 ∧ ∀ s ∈ S, s x = x := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let act : MulAction S B :=
    { smul := fun s u => ⟨(s : MulAut Q) u, hB s s.2 u u.2⟩
      one_smul := fun u => Subtype.ext rfl
      mul_smul := fun s t u => Subtype.ext rfl }
  have hdvd : 2 ∣ Nat.card B := by
    obtain ⟨n, hn⟩ := hB2.exists_card_eq
    rcases n with _ | n
    · exact absurd (Subgroup.card_eq_one.mp (by simpa using hn)) hBne
    · rw [hn]
      exact dvd_pow_self 2 (Nat.succ_ne_zero n)
  have h1 : (1 : B) ∈ MulAction.fixedPoints S B := fun s =>
    Subtype.ext (map_one (s : MulAut Q))
  obtain ⟨b, hb, hb1⟩ := hS.exists_fixed_point_of_prime_dvd_card_of_fixed_point B hdvd h1
  refine ⟨b, b.2, fun h => hb1 (Subtype.ext h.symm), fun s hs => ?_⟩
  exact congrArg Subtype.val (hb ⟨s, hs⟩)

def fixIn (S : Subgroup (MulAut Q)) (B : Subgroup Q) : Subgroup Q where
  carrier := {x | x ∈ B ∧ ∀ s ∈ S, s x = x}
  one_mem' := ⟨B.one_mem, fun s _ => map_one s⟩
  mul_mem' := fun {a b} ha hb => ⟨B.mul_mem ha.1 hb.1, fun s hs => by
    rw [map_mul, ha.2 s hs, hb.2 s hs]⟩
  inv_mem' := fun {a} ha => ⟨B.inv_mem ha.1, fun s hs => by rw [map_inv, ha.2 s hs]⟩

theorem mem_fixIn {S : Subgroup (MulAut Q)} {B : Subgroup Q} {x : Q} :
    x ∈ fixIn S B ↔ x ∈ B ∧ ∀ s ∈ S, s x = x := Iff.rfl

theorem exists_fixed_two [Finite Q] {S₁ S₂ : Subgroup (MulAut Q)} (h₁ : IsPGroup 2 S₁)
    (h₂ : IsPGroup 2 S₂) (hN : ∀ s ∈ S₂, ∀ a ∈ S₁, s * a * s⁻¹ ∈ S₁) {B : Subgroup Q}
    (hB₁ : ∀ s ∈ S₁, ∀ b ∈ B, s b ∈ B) (hB₂ : ∀ s ∈ S₂, ∀ b ∈ B, s b ∈ B) (hBne : B ≠ ⊥)
    (hB2 : IsPGroup 2 B) :
    ∃ x ∈ B, x ≠ 1 ∧ (∀ s ∈ S₁, s x = x) ∧ ∀ s ∈ S₂, s x = x := by
  have hFne : fixIn S₁ B ≠ ⊥ := by
    obtain ⟨x, hxB, hx1, hx⟩ := exists_fixed_of_isPGroup h₁ hB₁ hBne hB2
    intro hbot
    have : x ∈ fixIn S₁ B := ⟨hxB, hx⟩
    rw [hbot, Subgroup.mem_bot] at this
    exact hx1 this
  have hFstab : ∀ s ∈ S₂, ∀ b ∈ fixIn S₁ B, s b ∈ fixIn S₁ B := by
    intro s hs b hb
    refine ⟨hB₂ s hs b hb.1, fun a ha => ?_⟩
    have ha' : s⁻¹ * a * s⁻¹⁻¹ ∈ S₁ := hN s⁻¹ (S₂.inv_mem hs) a ha
    have h1 := hb.2 _ ha'
    have : a (s b) = s ((s⁻¹ * a * s⁻¹⁻¹ : MulAut Q) b) := by
      rw [MulAut.mul_apply, MulAut.mul_apply]
      simp
    rw [this, h1]
  obtain ⟨x, hxF, hx1, hx⟩ := exists_fixed_of_isPGroup h₂ hFstab hFne
    (hB2.to_le fun x hx => hx.1)
  exact ⟨x, hxF.1, hx1, hxF.2, hx⟩

theorem card_sup_of_inf_eq_bot {A B : Subgroup Q} (h : A ⊓ B = ⊥) :
    Nat.card ↥(A ⊔ B) = Nat.card A * Nat.card B := by
  let f : A × B → ↥(A ⊔ B) := fun p => ⟨(p.1 : Q) * p.2, Subgroup.mul_mem_sup p.1.2 p.2.2⟩
  have hf : Function.Bijective f := by
    constructor
    · rintro ⟨a, b⟩ ⟨a', b'⟩ hab
      have h1 : (a : Q) * b = a' * b' := congrArg Subtype.val hab
      have h2 : (a : Q)⁻¹ * a' = b * (b' : Q)⁻¹ := by
        calc (a : Q)⁻¹ * a' = (a : Q)⁻¹ * (a' * b') * (b' : Q)⁻¹ := by group
          _ = (a : Q)⁻¹ * (a * b) * (b' : Q)⁻¹ := by rw [← h1]
          _ = b * (b' : Q)⁻¹ := by group
      have h3 : (a : Q)⁻¹ * a' ∈ A ⊓ B :=
        ⟨A.mul_mem (A.inv_mem a.2) a'.2, h2 ▸ B.mul_mem b.2 (B.inv_mem b'.2)⟩
      rw [h, Subgroup.mem_bot] at h3
      have ha : a = a' := Subtype.ext (by
        calc (a : Q) = a * ((a : Q)⁻¹ * a') := by rw [h3, mul_one]
          _ = a' := by group)
      subst ha
      have hb : b = b' := Subtype.ext (mul_left_cancel h1)
      rw [hb]
    · rintro ⟨x, hx⟩
      obtain ⟨a, ha, b, hb, rfl⟩ := Subgroup.mem_sup.1 hx
      exact ⟨(⟨a, ha⟩, ⟨b, hb⟩), rfl⟩
  rw [← Nat.card_prod]
  exact (Nat.card_congr (Equiv.ofBijective f hf)).symm

end S153E57

end CFSG.Quasithin
