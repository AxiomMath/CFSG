module

public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
import CFSG.RankThree.PartTwo.Sec15.Sylow155CDK3
import CFSG.RankThree.PartTwo.Sec15.Sylow155NOQ
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddNormalizerOrderThreeCentralizes

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155CD

variable {Q : Type} [Group Q] [Finite Q]

private theorem mem_centralizer_of_odd {F : Subgroup Q} (hF : Nat.card F = 3) {g : Q}
    (hgF : g ∈ Subgroup.normalizer (F : Set Q)) (hodd : Odd (orderOf g)) :
    g ∈ Subgroup.centralizer (F : Set Q) :=
  CFSG.GorensteinWalter.odd_subgroup_le_centralizer_of_le_normalizer_card_three
    (Subgroup.zpowers g) F (by rwa [Nat.card_zpowers]) hF (Subgroup.zpowers_le.2 hgF)
    (Subgroup.mem_zpowers g)

omit [Finite Q] in
private theorem mem_normalizer_inf {J₁ J₂ : Subgroup Q} {g : Q}
    (h₁ : g ∈ Subgroup.normalizer (J₁ : Set Q)) (h₂ : g ∈ Subgroup.normalizer (J₂ : Set Q)) :
    g ∈ Subgroup.normalizer ((J₁ ⊓ J₂ : Subgroup Q) : Set Q) := by
  refine Subgroup.mem_normalizer_iff.mpr fun x => ⟨fun hx => ⟨?_, ?_⟩, fun hx => ⟨?_, ?_⟩⟩
  · exact (Subgroup.mem_normalizer_iff.mp h₁ x).mp hx.1
  · exact (Subgroup.mem_normalizer_iff.mp h₂ x).mp hx.2
  · exact (Subgroup.mem_normalizer_iff.mp h₁ x).mpr hx.1
  · exact (Subgroup.mem_normalizer_iff.mp h₂ x).mpr hx.2

private theorem normalizes_of_odd {J₁ J₂ : Subgroup Q} (hJ : ⁅J₁, J₂⁆ = ⊥)
    (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3) (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6))) {g : Q}
    (hgY : g ∈ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q)) (hgodd : Odd (orderOf g)) :
    g ∈ Subgroup.normalizer (J₁ : Set Q) ∧ g ∈ Subgroup.normalizer (J₂ : Set Q) := by
  have hc₁ := Sec14.Item148PtRes.card_eq_of_isTripleCover hT₁
  have hc₂ := Sec14.Item148PtRes.card_eq_of_isTripleCover hT₂
  have hJ' : ⁅J₂, J₁⁆ = ⊥ := by rw [Subgroup.commutator_comm, hJ]
  have hne : J₁ ≠ J₂ := by
    intro h
    rw [h, inf_idem, hc₂] at h3
    norm_num at h3
  have hm₁ := Sylow155NO.map_conj_eq_or_eq hJ h3 hT₁ hT₂ hgY (J := J₁) le_sup_left
    (Sylow155NO.sup_le_normalizer_left hJ) hc₁
  have hm₂ := Sylow155NO.map_conj_eq_or_eq hJ h3 hT₁ hT₂ hgY (J := J₂) le_sup_right
    (by rw [sup_comm]; exact Sylow155NO.sup_le_normalizer_left hJ') hc₂
  have hinj : ∀ W W' : Subgroup Q, W.map (MulAut.conj g).toMonoidHom =
      W'.map (MulAut.conj g).toMonoidHom → W = W' :=
    fun W W' h => Subgroup.map_injective (MulAut.conj g).injective h
  have hfix : J₁.map (MulAut.conj g).toMonoidHom = J₁ ∧
      J₂.map (MulAut.conj g).toMonoidHom = J₂ := by
    rcases hm₁ with h1 | h1
    · refine ⟨h1, ?_⟩
      rcases hm₂ with h2 | h2
      · exact absurd (hinj J₂ J₁ (h2.trans h1.symm)) hne.symm
      · exact h2
    · exfalso
      rcases hm₂ with h2 | h2
      ·
        have hg2 : g ^ 2 ∈ Subgroup.normalizer (J₁ : Set Q) := by
          have hcomp : (MulAut.conj (g ^ 2)).toMonoidHom =
              (MulAut.conj g).toMonoidHom.comp (MulAut.conj g).toMonoidHom := by
            rw [pow_two, map_mul]
            rfl
          refine Subgroup.mem_normalizer_iff_map_conj_eq.mpr ?_
          show J₁.map (MulAut.conj (g ^ 2)).toMonoidHom = J₁
          rw [hcomp, ← Subgroup.map_map, h1, h2]
        obtain ⟨m, hm⟩ := Sylow155T.eq_pow_sq_of_odd hgodd
        have hgJ : g ∈ Subgroup.normalizer (J₁ : Set Q) := by
          rw [hm]
          exact pow_mem hg2 m
        exact hne ((Subgroup.mem_normalizer_iff_map_conj_eq.mp hgJ).symm.trans h1)
      · exact hne (hinj J₁ J₂ (h1.trans h2.symm))
  exact ⟨Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix.1,
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hfix.2⟩

private theorem centralizes_of_perfect {Ā J : Subgroup Q} (hĀ3 : ∀ a ∈ Ā, a ^ 3 = 1)
    (hĀC : ∀ q ∈ Subgroup.centralizer (Ā : Set Q), q ^ 3 = 1 → q ∈ Ā)
    (hperf : commutator ↥J = ⊤) (hT : Sec4.IsTripleCover ↥J (alternatingGroup (Fin 6)))
    (hĀJ : Ā ≤ Subgroup.normalizer (J : Set Q)) {g : Q}
    (hgĀ : g ∈ Subgroup.centralizer (Ā : Set Q)) (hgJ : g ∈ Subgroup.normalizer (J : Set Q))
    (hgZ : ∀ z ∈ Sec14.Item148PtRes.centerIn J, g * z * g⁻¹ = z) (hg3 : ¬ 3 ∣ orderOf g) :
    ∀ x ∈ J, g * x * g⁻¹ = x := by
  have hf : ∃ f ∈ Ā, ∃ x ∈ J, f * x * f⁻¹ ≠ x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨x, hx3, hxZ⟩ := Sylow155NO.exists_pow_three_not_mem_center hT
    have hxC : (x : Q) ∈ Subgroup.centralizer (Ā : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      have h := hcon a ha x x.2
      calc a * (x : Q) = a * x * a⁻¹ * a := by group
        _ = x * a := by rw [h]
    have hxĀ : (x : Q) ∈ Ā := hĀC x hxC (congrArg Subtype.val hx3)
    apply hxZ
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have h := hcon x hxĀ y y.2
    calc ((y * x : ↥J) : Q) = (y : Q) * x := rfl
      _ = ((x : Q) * y * (x : Q)⁻¹) * x := by rw [h]
      _ = x * y := by group
  obtain ⟨f, hfĀ, x₁, hx₁, hfx⟩ := hf
  exact conj_eq_of_commute_of_pow_three hperf hT
    (fun x hx => (Subgroup.mem_normalizer_iff.1 hgJ x).1 hx)
    (fun x hx => (Subgroup.mem_normalizer_iff.1 (hĀJ hfĀ) x).1 hx) hgZ
    (Subgroup.mem_centralizer_iff.1 hgĀ f hfĀ).symm (hĀ3 f hfĀ) ⟨x₁, hx₁, hfx⟩ hg3

theorem mem_centralizer_of_commute {Ā J₁ J₂ : Subgroup Q}
    (hĀc : ∀ a ∈ Ā, ∀ b ∈ Ā, a * b = b * a) (hĀ3 : ∀ a ∈ Ā, a ^ 3 = 1)
    (hĀ27 : Nat.card Ā = 27)
    (hĀC : ∀ q ∈ Subgroup.centralizer (Ā : Set Q), q ^ 3 = 1 → q ∈ Ā)
    (hĀY : Ā ≤ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q))
    (hJ : ⁅J₁, J₂⁆ = ⊥) (h3 : Nat.card ↥(J₁ ⊓ J₂) = 3)
    (hT₁ : Sec4.IsTripleCover ↥J₁ (alternatingGroup (Fin 6)))
    (hT₂ : Sec4.IsTripleCover ↥J₂ (alternatingGroup (Fin 6)))
    {g : Q} (hgĀ : g ∈ Subgroup.centralizer (Ā : Set Q))
    (hgY : g ∈ Subgroup.normalizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q))
    (hgodd : Odd (orderOf g)) (hg3 : ¬ 3 ∣ orderOf g) :
    g ∈ Subgroup.centralizer ((J₁ ⊔ J₂ : Subgroup Q) : Set Q) := by
  have hJ' : ⁅J₂, J₁⁆ = ⊥ := by rw [Subgroup.commutator_comm, hJ]
  have h3' : Nat.card ↥(J₂ ⊓ J₁) = 3 := by rwa [inf_comm]
  have hĀJ : ∀ a ∈ Ā, a ∈ Subgroup.normalizer (J₁ : Set Q) ∧
      a ∈ Subgroup.normalizer (J₂ : Set Q) := fun a ha =>
    Sylow155NO.normalizes_of_pow_three hJ h3 hT₁ hT₂ (hĀ3 a ha) (hĀY ha)
  have hĀJ₁ : Ā ≤ Subgroup.normalizer (J₁ : Set Q) := fun a ha => (hĀJ a ha).1
  have hĀJ₂ : Ā ≤ Subgroup.normalizer (J₂ : Set Q) := fun a ha => (hĀJ a ha).2
  have hperf₁ := Sylow155NO.commutator_eq_top_of_elemAbelian hĀc hĀ3 hĀ27 hĀC hĀJ₁ hĀJ₂ hJ h3 hT₁
    hT₂
  have hperf₂ := Sylow155NO.commutator_eq_top_of_elemAbelian hĀc hĀ3 hĀ27 hĀC hĀJ₂ hĀJ₁ hJ' h3'
    hT₂ hT₁
  obtain ⟨hg₁, hg₂⟩ := normalizes_of_odd hJ h3 hT₁ hT₂ hgY hgodd
  have hgF := mem_centralizer_of_odd h3 (mem_normalizer_inf hg₁ hg₂) hgodd
  have hgZ : ∀ z ∈ J₁ ⊓ J₂, g * z * g⁻¹ = z := fun z hz => by
    rw [← Subgroup.mem_centralizer_iff.1 hgF z hz, mul_inv_cancel_right]
  have hZ₁ := Sec14.Item148PtRes.inf_eq_centerIn_left hJ h3 hT₁.1
  have hZ₂ := Sec14.Item148PtRes.inf_eq_centerIn_right hJ h3 hT₂.1
  have h₁ := centralizes_of_perfect hĀ3 hĀC hperf₁ hT₁ hĀJ₁ hgĀ hg₁
    (fun z hz => hgZ z (by rw [hZ₁]; exact hz)) hg3
  have h₂ := centralizes_of_perfect hĀ3 hĀC hperf₂ hT₂ hĀJ₂ hgĀ hg₂
    (fun z hz => hgZ z (by rw [hZ₂]; exact hz)) hg3
  have hcomm : ∀ x : Q, g * x * g⁻¹ = x → x * g = g * x := fun x hx => by
    calc x * g = g * x * g⁻¹ * g := by rw [hx]
      _ = g * x := by group
  have hle : J₁ ⊔ J₂ ≤ Subgroup.centralizer ({g} : Set Q) := by
    refine sup_le (fun x hx => ?_) (fun x hx => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hcomm x (h₁ x hx)).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro y hy
      rw [Set.mem_singleton_iff.1 hy]
      exact (hcomm x (h₂ x hx)).symm
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  exact (Subgroup.mem_centralizer_iff.1 (hle hy) g rfl).symm

end CFSG.RankThree.PartTwo.Sec15.Sylow155CD
