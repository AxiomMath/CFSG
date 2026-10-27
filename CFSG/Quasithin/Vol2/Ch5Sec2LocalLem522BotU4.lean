module

public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotW
public import CFSG.Quasithin.Vol2.Ch5Sec2LocalLem522BotList

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open scoped commutatorElement

section Special

variable {G : Type} [Group G] [Finite G]

theorem false_of_sixteen_le_of_isSpecialPow {R W : Subgroup G} (hR : IsSpecialPow 2 2 2 ↥R)
    (hWR : W ≤ R) (hWc : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a) (hW : 16 ≤ Nat.card ↥W) : False := by
  obtain ⟨⟨-, hsp⟩, hRc, hZ⟩ := hR
  have hR32 : Nat.card ↥R = 32 := by rw [hRc]; norm_num
  have hcomm : commutator ↥R = Subgroup.center ↥R := by
    rcases hsp with ⟨hab, -⟩ | ⟨hc, -, -⟩
    · exfalso
      have htop : Subgroup.center ↥R = ⊤ := by
        rw [eq_top_iff]
        intro x _
        rw [Subgroup.mem_center_iff]
        intro y
        exact hab.is_comm.comm y x
      rw [htop, Subgroup.card_top, hR32] at hZ
      omega
    · exact hc
  set W' := W.subgroupOf R with hW'
  have hW'c : Nat.card ↥W' = Nat.card ↥W :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hWR).toEquiv
  have hW'ab : ∀ a b : ↥W', a * b = b * a := fun a b =>
    Subtype.ext (Subtype.ext (hWc _ (Subgroup.mem_subgroupOf.mp a.2) _
      (Subgroup.mem_subgroupOf.mp b.2)))
  have hdvd : Nat.card ↥W' ∣ 32 := hR32 ▸ Subgroup.card_subgroup_dvd_card W'
  have hW16 : Nat.card ↥W' = 16 := by
    have h16 : 16 ≤ Nat.card ↥W' := hW'c ▸ hW
    have hle : Nat.card ↥W' ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
    have hdvd' : Nat.card ↥W' ∣ 2 ^ 5 := by norm_num; exact hdvd
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd'
    have hk4 : 4 ≤ k := by
      rw [hk'] at h16
      exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 2)).mp (by simpa using h16)
    rcases (show k = 4 ∨ k = 5 by omega) with rfl | rfl
    · rw [hk']; norm_num
    exfalso
    have htop : W' = ⊤ := Subgroup.eq_top_of_card_eq W' (by rw [hk', hR32]; norm_num)
    have hZtop : Subgroup.center ↥R = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_center_iff]
      intro y
      have hx : x ∈ W' := by rw [htop]; exact Subgroup.mem_top x
      have hy : y ∈ W' := by rw [htop]; exact Subgroup.mem_top y
      exact congrArg Subtype.val (hW'ab ⟨y, hy⟩ ⟨x, hx⟩)
    rw [hZtop, Subgroup.card_top, hR32] at hZ
    omega
  obtain ⟨p, hp⟩ : ∃ p : ↥R, p ∉ W' := by
    by_contra hcon
    push Not at hcon
    have htop : W' = ⊤ := eq_top_iff.mpr fun x _ => hcon x
    rw [htop, Subgroup.card_top, hR32] at hW16
    omega
  have hcen : ∀ w : ↥R, ⁅p, w⁆ ∈ Subgroup.center ↥R := fun w => by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_top p) (Subgroup.mem_top w)
  let f : ↥W' →* ↥(Subgroup.center ↥R) :=
    { toFun := fun w => ⟨⁅p, (w : ↥R)⁆, hcen w⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => by
        apply Subtype.ext
        show ⁅p, (a : ↥R) * b⁆ = ⁅p, (a : ↥R)⁆ * ⁅p, (b : ↥R)⁆
        have hb := Subgroup.mem_center_iff.mp (hcen b)
        rw [commutatorElement_def] at hb
        rw [commutatorElement_def, commutatorElement_def, commutatorElement_def]
        calc p * (↑a * ↑b) * p⁻¹ * (↑a * ↑b)⁻¹ =
            (p * ↑a * p⁻¹) * ((p * ↑b * p⁻¹ * (↑b)⁻¹) * (↑a)⁻¹) := by group
          _ = (p * ↑a * p⁻¹) * ((↑a)⁻¹ * (p * ↑b * p⁻¹ * (↑b)⁻¹)) := by rw [← hb (↑a)⁻¹]
          _ = p * ↑a * p⁻¹ * (↑a)⁻¹ * (p * ↑b * p⁻¹ * (↑b)⁻¹) := by group }
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup f.ker
  have hrange : Nat.card (↥W' ⧸ f.ker) ≤ 2 := by
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, ← hZ]
    exact Subgroup.card_le_of_le le_top |>.trans (le_of_eq (Subgroup.card_top))
  have hker8 : 8 ≤ Nat.card ↥f.ker := by
    rw [hW16] at hcard
    have hpos : 0 < Nat.card (↥W' ⧸ f.ker) := Nat.card_pos
    nlinarith
  have hsup : W' ⊔ Subgroup.zpowers p = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    have h1 : W' < W' ⊔ Subgroup.zpowers p :=
      lt_of_le_of_ne le_sup_left fun h => hp (h ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers p))
    have h2 : Nat.card ↥W' < Nat.card ↥(W' ⊔ Subgroup.zpowers p) :=
      Subgroup.card_lt_of_lt h1
    have h3 : Nat.card ↥(W' ⊔ Subgroup.zpowers p) ∣ 32 := hR32 ▸ Subgroup.card_subgroup_dvd_card _
    rw [hR32]
    rw [hW16] at h2
    have h4 : Nat.card ↥(W' ⊔ Subgroup.zpowers p) ≤ 32 := Nat.le_of_dvd (by norm_num) h3
    have h3' : Nat.card ↥(W' ⊔ Subgroup.zpowers p) ∣ 2 ^ 5 := by norm_num; exact h3
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h3'
    have hk5 : 5 ≤ k := by
      rw [hk'] at h2
      by_contra hk4
      have : 2 ^ k ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hk', show k = 5 by omega]
    norm_num
  have hkerZ : ∀ c : ↥W', c ∈ f.ker → (c : ↥R) ∈ Subgroup.center ↥R := by
    intro c hc
    have hpc : ⁅p, (c : ↥R)⁆ = 1 := congrArg Subtype.val hc
    rw [commutatorElement_eq_one_iff_mul_comm] at hpc
    have hle : W' ⊔ Subgroup.zpowers p ≤ Subgroup.centralizer ({(c : ↥R)} : Set ↥R) := by
      refine sup_le (fun w hw => ?_) (Subgroup.zpowers_le.mpr ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hW'ab ⟨w, hw⟩ c)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact hpc
    rw [hsup] at hle
    rw [Subgroup.mem_center_iff]
    intro g
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle (Subgroup.mem_top g)))
  have hle : Nat.card ↥f.ker ≤ Nat.card ↥(Subgroup.center ↥R) := by
    have hinj : Function.Injective (fun c : ↥f.ker => (⟨((c : ↥W') : ↥R), hkerZ c c.2⟩ :
        ↥(Subgroup.center ↥R))) := by
      intro a b hab
      have := congrArg Subtype.val hab
      exact Subtype.ext (Subtype.ext this)
    exact Nat.card_le_card_of_injective _ hinj
  rw [hZ] at hle
  omega

end Special

theorem stmt5_2_2_bot_U4_of (h510 : Stmt5_1_10) (h331 : Stmt3_3_1) (hR : L2RankOneSylowFact) :
    Stmt5_2_2_bot_U4 := by
  intro G _ _ T M L V H B D L₂ Dp n hyp _ _ _ _ _ hsp _ _ _ _
  obtain ⟨-, -, hWc, -, h16⟩ := hyp.commutator_facts h510 h331 hR
  exact false_of_sixteen_le_of_isSpecialPow hsp (hyp.commutator_le_pCoreOf h510 h331 hR) hWc h16

end CFSG.Quasithin.H13
