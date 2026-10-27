module

public import CFSG.Timmesfeld.Bridge.RootStructR2Prime
public import CFSG.Timmesfeld.Bridge.RootSetsSyl

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

variable {G : Type*} [Group G] {D : Set G}

theorem ncard_rootLines_eq [Finite G] (hclass : ∃ d₀ : G, D = {g | IsConj d₀ g}) {a c : G}
    (ha : a ∈ D) (hc : c ∈ D) : (rootLines D c).ncard = (rootLines D a).ncard := by
  have key : ∀ (g x : G), (rootLines D x).ncard ≤ (rootLines D (g * x * g⁻¹)).ncard := by
    intro g x
    rw [← Set.ncard_image_of_injective _
      (Subgroup.map_injective (f := (MulAut.conj g).toMonoidHom) (MulAut.conj g).injective)]
    exact Set.ncard_le_ncard (by
      rintro _ ⟨L, hL, rfl⟩
      exact map_conj_mem_rootLines_conj hclass hL g)
  obtain ⟨g, rfl⟩ := isConj_iff.1 (isConj_of_isClass hclass ha hc)
  refine le_antisymm ?_ (key g a)
  have := key g⁻¹ (g * a * g⁻¹)
  rwa [show g⁻¹ * (g * a * g⁻¹) * g⁻¹⁻¹ = a by group] at this

theorem three_le_ncard_rootLines (h : Hyp G D) (h3 : ThreeLines D) :
    ∃ b ∈ D, 3 ≤ (rootLines D b).ncard := by
  have := h.finite
  obtain ⟨b, hb, c₁, hc₁, c₂, hc₂, c₃, hc₃, hcol, h21, h31, h32⟩ := h3
  obtain ⟨hb1, hb1D, h1T⟩ := hcol c₁ (by simp)
  obtain ⟨hb2, hb2D, h2T⟩ := hcol c₂ (by simp)
  obtain ⟨hb3, hb3D, h3T⟩ := hcol c₃ (by simp)
  refine ⟨b, hb, ?_⟩
  have hsub : ({rootGroup D b ⊔ rootGroup D c₁, rootGroup D b ⊔ rootGroup D c₂,
      rootGroup D b ⊔ rootGroup D c₃} : Set (Subgroup G)) ⊆ rootLines D b := by
    rintro L (rfl | rfl | rfl)
    · exact ⟨c₁, hc₁, hb1, hb1D, h1T, rfl⟩
    · exact ⟨c₂, hc₂, hb2, hb2D, h2T, rfl⟩
    · exact ⟨c₃, hc₃, hb3, hb3D, h3T, rfl⟩
  have hne : ∀ {u v : G}, v ∈ D → v ∉ rootGroup D b ⊔ rootGroup D u →
      rootGroup D b ⊔ rootGroup D u ≠ rootGroup D b ⊔ rootGroup D v := fun hv hvL heq =>
    hvL (heq ▸ right_mem_line hv)
  calc 3 = ({rootGroup D b ⊔ rootGroup D c₁, rootGroup D b ⊔ rootGroup D c₂,
        rootGroup D b ⊔ rootGroup D c₃} : Set (Subgroup G)).ncard :=
        (Set.ncard_eq_three.2 ⟨_, _, _, hne hc₂ h21, hne hc₃ h31, hne hc₃ h32, rfl⟩).symm
    _ ≤ (rootLines D b).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)

theorem thinManyStepE_of (hPow : RootLinesPowerStep) (hTor : RootLinesTorusStep)
    (h48 : ThinGateManyStep) (h410 : ThinGateOneStep) : ThinManyStepE := by
  intro G _ D h IH hl hc hs hconn h3
  have := h.finite
  have hD := h.root
  have hclass := h.isClass
  refine thinOneOpposite_of_gate h hc hs fun a ha d hd had hadD hdT hLad => ?_
  by_contra hcounter
  have hAll := allLinesTI_of_lineTI h hc hs hconn ha hd had hadD hdT hLad
  have hLS : LineSetting G D := ⟨h, hc, hs, hconn, ⟨a, ha, d, hd, had, hadD, hdT, hLad⟩⟩
  set q := Nat.card (rootGroup D a) with hqdef
  have hq : ∀ c ∈ D, Nat.card (rootGroup D c) = q := fun c hc' => card_rootGroup_eq hclass hc' ha
  obtain ⟨n, hn⟩ := hPow G D hLS a ha
  have hQ : ∀ c ∈ D, (rootLines D c).ncard = q ^ n + 1 := fun c hc' =>
    (ncard_rootLines_eq hclass ha hc').trans hn
  have hq4 : 4 ≤ q := four_le_card_rootGroup hclass hD hc hl ha
  have hn1 : 1 ≤ n := by
    obtain ⟨b, hb, hb3⟩ := three_le_ncard_rootLines h h3
    rw [hQ b hb] at hb3
    by_contra hn0
    rw [show n = 0 by omega, pow_zero] at hb3
    omega
  have hQ4 : 4 ≤ q ^ n := le_trans hq4 (by
    calc q = q ^ 1 := (pow_one q).symm
      _ ≤ q ^ n := Nat.pow_le_pow_right (by omega) hn1)
  obtain ⟨b, hb, x, hx, hbx, hoddbx, hx1, a', ha', hba', hba'D, ha'T, hno⟩ :
      ∃ b ∈ D, ∃ x ∈ D, ¬ Commute b x ∧ Odd (orderOf (b * x)) ∧ OneOpposite D b x ∧
        ∃ a' ∈ D, Commute b a' ∧ b * a' ∈ D ∧ a' ∉ rootSet D b ∧
          ∀ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a' → orderOf (x * p) ≠ 4 := by
    by_contra hall
    apply hcounter
    intro b hb x hx hbx hoddbx hx1 a' ha' hba' hba'D ha'T
    by_contra hp
    push Not at hp
    exact hall ⟨b, hb, x, hx, hbx, hoddbx, hx1, a', ha', hba', hba'D, ha'T, hp⟩
  set k := (gatedLines D b x).ncard with hkdef
  have hk : ∀ c ∈ D, ∀ y ∈ D, ¬ Commute c y → Odd (orderOf (c * y)) → OneOpposite D c y →
      (gatedLines D c y).ncard = k := fun c hc' y hy hcy hoddcy hy1 =>
    ncard_gatedLines_eq h hc hs hconn hAll rootLinesRegularStep h3 hb hx hbx hoddbx hx1 hc' hy
      hcy hoddcy hy1
  have hkQ : k ≠ q ^ n + 1 := by
    intro hkQ
    have hsub : gatedLines D b x ⊆ rootLines D b := fun L hL => hL.1
    have heq : gatedLines D b x = rootLines D b :=
      Set.eq_of_subset_of_ncard_le hsub (by rw [hQ b hb, ← hkQ]) (Set.toFinite _)
    have hmem : rootGroup D b ⊔ rootGroup D a' ∈ gatedLines D b x := by
      rw [heq]
      exact ⟨a', ha', hba', hba'D, ha'T, rfl⟩
    obtain ⟨-, p, hp, hpL, h4⟩ := hmem
    exact hno p hp hpL h4
  have hkval := hLS.gatedLines_card_mem hAll hTor hQ hQ4 hk hb hx hbx hoddbx hx1
  have hcount : ThinGateCount G D q n k := by
    refine ⟨hq, hQ, hk, fun c hc' T hT => ?_, fun c hc' => ?_⟩
    · rw [hLS.ncard_gatedPoints hAll hQ hc' hT, hq c hc']
      ring
    · rw [hLS.ncard_oneOmega_mul hAll hQ hc' (hk c hc'), hq c hc']
      ring
  have hgen : ∀ b ∈ D, ∀ a ∈ D, ∀ x ∈ D, Commute b a → b * a ∈ D → a ∉ rootSet D b →
      ¬ Commute b x → Odd (orderOf (b * x)) → OneOpposite D b x →
      (∀ p ∈ D, p ∈ rootGroup D b ⊔ rootGroup D a → orderOf (x * p) ≠ 4) →
      rootGroup D b ⊔ rootGroup D a ⊔ rootGroup D x = ⊤ :=
    fun b hb a ha x hx hba hbaD haT hbx hoddbx h1 hno' =>
      top_of_forall_not_special h hc hs hconn hAll IH hl hb ha hba hbaD haT hx hbx hoddbx h1 hno'
  have hTGC : ThinGateCounter G D := ⟨h, IH, hl, hc, hs, hconn, hAll, h3, hgen, hcounter⟩
  rcases eq_or_lt_of_le hn1 with hn1' | hn2
  ·
    subst hn1'
    rw [pow_one] at hkval hkQ
    refine h410 G D q k hTGC hcount ?_
    rcases hkval with h' | h' | h' | h'
    · exact Or.inl h'
    · exact Or.inr (Or.inl h')
    · exact Or.inr (Or.inr h')
    · exact absurd h' hkQ
  ·
    have hqe : Even q := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      obtain ⟨r, hr⟩ := (IsPGroup.iff_card).1 (isPGroup_rootGroup hclass hD hc ha)
      rw [← hqdef] at hr
      rw [hr]
      exact (Nat.even_pow' (by rintro rfl; simp at hr; omega)).2 even_two
    obtain ⟨p, hp, hpQ, hpq⟩ := exists_prime_dvd_pow_sub_one (by omega) hqe hn2
    have hp2 : p ≠ 2 := by
      rintro rfl
      obtain ⟨r, hr⟩ := hqe
      have : Even (q ^ n) := (Nat.even_pow' (by omega)).2 ⟨r, hr⟩
      obtain ⟨s, hs'⟩ := this
      omega
    have hpq' : ∀ c ∈ D, ¬ p ∣ Nat.card (rootGroup D c) - 1 := fun c hc' => by
      rw [hq c hc']
      exact hpq
    rcases hkval with h' | h' | h' | h'
    · exact hLS.false_of_prime_dvd_sub_one hAll hTor IH hl hQ (by omega) hk hp hp2 hpQ hpq'
        (by rw [h']; exact dvd_zero p)
    · rw [h'] at hcount
      exact h48 G D q n hTGC hcount hn2
    · exact hLS.false_of_prime_dvd_sub_one hAll hTor IH hl hQ (by omega) hk hp hp2 hpQ hpq'
        (by rw [h']; exact hpQ)
    · exact absurd h' hkQ

end CFSG.Timmesfeld.Bridge
