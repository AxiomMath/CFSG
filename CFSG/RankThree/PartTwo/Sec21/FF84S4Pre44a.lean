module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreThetaModel
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec21.FF79Lemma14Base
public import CFSG.RankThree.PartTwo.Sec21.FF84S4PreG1a

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open Equiv Equiv.Perm

variable {G : Type} [Group G] [Finite G] {b b₁ b₂ : G} {L B K : Subgroup G}

theorem Z1_of_odd (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    (h41 : Opp 3 (Cen b) ≤ Opp 3 (Cen (b * b₁)))
    (hodd : Odd (Nat.card (Opp 3 (Cen (b * b₁))))) : Subgroup.center L = ⊥ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set Zc : Subgroup G := (Subgroup.center ↥L).map L.subtype with hZc
  have hcard : Nat.card Zc ∣ 2 := by
    rw [hZc, Subgroup.card_map_of_injective L.subtype_injective]; exact hA.2
  have hZcL : Zc ≤ L := Subgroup.map_subtype_le _
  have hZc3 : Nat.Coprime 3 (Nat.card Zc) :=
    Nat.Coprime.coprime_dvd_right hcard (by norm_num)
  have hn : ∀ g ∈ Cen b, ∀ z ∈ Zc, g * z * g⁻¹ ∈ Zc := by
    intro g hg z hz
    obtain ⟨z', hz', rfl⟩ := Subgroup.mem_map.1 hz
    have hgL : g ∈ Nor L := h.hyp.hLN hg
    have hmem : g * (z' : G) * g⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 hgL _).1 z'.2
    refine Subgroup.mem_map.2 ⟨⟨g * z' * g⁻¹, hmem⟩, ?_, rfl⟩
    rw [Subgroup.mem_center_iff]
    intro l
    have hmem' : g⁻¹ * (l : G) * g ∈ L := by
      have := (Subgroup.mem_normalizer_iff.1 hgL (g⁻¹ * (l : G) * g)).2
      rw [show g * (g⁻¹ * (l : G) * g) * g⁻¹ = l by group] at this
      exact this l.2
    have hc : (g⁻¹ * (l : G) * g) * (z' : G) = (z' : G) * (g⁻¹ * (l : G) * g) :=
      congrArg Subtype.val (Subgroup.mem_center_iff.1 hz' ⟨g⁻¹ * (l : G) * g, hmem'⟩)
    apply Subtype.ext
    show (l : G) * (g * z' * g⁻¹) = (g * z' * g⁻¹) * l
    have e1 : (l : G) * (g * z' * g⁻¹) = g * ((g⁻¹ * (l : G) * g) * z') * g⁻¹ := by group
    have e2 : (g * z' * g⁻¹) * l = g * (z' * (g⁻¹ * (l : G) * g)) * g⁻¹ := by group
    rw [e1, e2, hc]
  have hZcX : Zc ≤ Opp 3 (Cen b) :=
    FF79.L14.le_Opp_of_normalized (hZcL.trans h.hyp.hLC) hn hZc3
  have hZcY : Zc ≤ Opp 3 (Cen (b * b₁)) := hZcX.trans h41
  have hdvd : Nat.card Zc ∣ Nat.card (Opp 3 (Cen (b * b₁))) := Subgroup.card_dvd_of_le hZcY
  have h1 : Nat.card Zc = 1 := by
    rcases (Nat.dvd_prime Nat.prime_two).1 hcard with h1 | h2
    · exact h1
    · exfalso
      rw [h2] at hdvd
      have := Nat.odd_iff.1 hodd
      omega
  have hZ1 : Zc = ⊥ := Subgroup.card_eq_one.1 h1
  rw [Subgroup.eq_bot_iff_forall]
  intro z hz
  have : (z : G) ∈ Zc := Subgroup.mem_map.2 ⟨z, hz, rfl⟩
  rw [hZ1, Subgroup.mem_bot] at this
  exact Subtype.ext this

theorem cen_L_of_coprime6 (hA : A8Model L)
    (h : FF84Sec4 b L B K b₁ b₂) {w : G} (hw1 : w ∈ Cen b) (hw2 : w ∈ Cen (b₁ * b₂))
    (hord : Nat.Coprime (orderOf w) 6) : w ∈ CenS L := by
  obtain ⟨θ, hker, -, -, hc, hd⟩ := theta_model hA h
  have hwN : w ∈ Nor L := h.hyp.hLN hw1
  have hb₁L : b₁ ∈ L := (Subgroup.mem_inf.1 h.hb₁).2
  have hb₂L : b₂ ∈ L := (Subgroup.mem_inf.1 h.hb₂).2
  set w' : ↥(Nor L) := ⟨w, hwN⟩ with hw'
  have hcomm : θ w' ∈ Subgroup.centralizer ({sig} : Set (Perm (Fin 8))) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hac : w * (b₁ * b₂) = (b₁ * b₂) * w := Subgroup.mem_centralizer_singleton_iff.1 hw2
    have hcomm' : w' * ((⟨b₁, Subgroup.le_normalizer hb₁L⟩ : ↥(Nor L)) * ⟨b₂, Subgroup.le_normalizer hb₂L⟩) =
        ((⟨b₁, Subgroup.le_normalizer hb₁L⟩ : ↥(Nor L)) * ⟨b₂, Subgroup.le_normalizer hb₂L⟩) * w' :=
      Subtype.ext hac
    have := congrArg θ hcomm'
    simp only [map_mul, hc, hd] at this
    exact this
  have h1 : orderOf (θ w') ∣ 36 := by
    have := orderOf_dvd_natCard (⟨θ w', hcomm⟩ :
      ↥(Subgroup.centralizer ({sig} : Set (Perm (Fin 8)))))
    rwa [card_cent_sig, Subgroup.orderOf_mk] at this
  have h2 : orderOf (θ w') ∣ orderOf w := by
    have := orderOf_map_dvd θ w'
    rwa [← Subgroup.orderOf_coe w'] at this
  have hcop : Nat.Coprime (orderOf (θ w')) 6 := Nat.Coprime.coprime_dvd_left h2 hord
  have h36 : Nat.Coprime (orderOf (θ w')) 36 := by
    have := Nat.Coprime.pow_right 2 hcop
    simpa using this
  have h3 : orderOf (θ w') = 1 := Nat.Coprime.eq_one_of_dvd h36 h1
  exact (hker w').1 (orderOf_eq_one_iff.1 h3)

theorem le_X (hA : A8Model L) (h : FF84Sec4 b L B K b₁ b₂)
    {W : Subgroup G} (hWb : W ≤ Cen b) (hW2 : W ≤ Cen (b₁ * b₂))
    (hWo : ∀ w ∈ W, Nat.Coprime (orderOf w) 6) (hW3 : Nat.Coprime 3 (Nat.card W))
    (hWn : ∀ c ∈ Cen b ⊓ CenS L, ∀ w ∈ W, c * w * c⁻¹ ∈ W) : W ≤ Opp 3 (Cen b) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hWZ : W ≤ Cen b ⊓ CenS L := fun w hw =>
    Subgroup.mem_inf.2 ⟨hWb hw, cen_L_of_coprime6 hA h (hWb hw) (hW2 hw) (hWo w hw)⟩
  have h1 : W ≤ Opp 3 (Cen b ⊓ CenS L) := FF79.L14.le_Opp_of_normalized hWZ hWn hW3
  refine h1.trans (FF79.L14.Opp_le_Opp_of_normalized inf_le_left ?_)
  intro g hg c hc
  obtain ⟨hcb, hcL⟩ := Subgroup.mem_inf.1 hc
  refine Subgroup.mem_inf.2 ⟨mul_mem (mul_mem hg hcb) (inv_mem hg), ?_⟩
  have hgL : g ∈ Nor L := h.hyp.hLN hg
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hl' : g⁻¹ * l * g ∈ L := by
    have := (Subgroup.mem_normalizer_iff.1 hgL (g⁻¹ * l * g)).2
    rw [show g * (g⁻¹ * l * g) * g⁻¹ = l by group] at this
    exact this hl
  have hc' : (g⁻¹ * l * g) * c = c * (g⁻¹ * l * g) := Subgroup.mem_centralizer_iff.1 hcL _ hl'
  have e1 : l * (g * c * g⁻¹) = g * ((g⁻¹ * l * g) * c) * g⁻¹ := by group
  have e2 : (g * c * g⁻¹) * l = g * (c * (g⁻¹ * l * g)) * g⁻¹ := by group
  rw [e1, e2, hc']

end CFSG.RankThree.PartTwo.Sec21.FF84.S4
