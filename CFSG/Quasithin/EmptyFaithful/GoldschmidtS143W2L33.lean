module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Fpf
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2NoDih
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Res
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2Out
public import CFSG.Quasithin.EmptyFaithful.Insp7NumF
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239InspL33Core
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_15FactsSL3
public import CFSG.LocalAnalysis.ComponentInitial.LinearModelOuterTwoPart
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS143W2DihB

public section

namespace CFSG.Quasithin

open CFSG.QuasithinUnique.Vol2Native.L239.L33Insp
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

namespace S143

namespace InspW2

theorem not_comm_T16 : ¬ ∀ a ∈ T16, ∀ b ∈ T16, a * b = b * a := by
  intro h
  have key : ∃ a ∈ t16p, ∃ b ∈ t16p, nmul a b ≠ nmul b a := by decide +kernel
  obtain ⟨a, ha, b, hb, hne⟩ := key
  obtain ⟨ha1, ha2⟩ := t16_facts.1 a ha
  obtain ⟨hb1, hb2⟩ := t16_facts.1 b hb
  have haT : ofN a ha2 ∈ T16 := by rw [mem_T16, rn_ofN a ha1 ha2]; exact ha
  have hbT : ofN b hb2 ∈ T16 := by rw [mem_T16, rn_ofN b hb1 hb2]; exact hb
  have := congrArg rn (h _ haT _ hbT)
  rw [rn_mul, rn_mul, rn_ofN a ha1 ha2, rn_ofN b hb1 hb2] at this
  exact hne this

theorem no_abelian_sixteen {A : Subgroup S3} (hA : Nat.card A = 16)
    (hc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) : False := by
  have hApg : IsPGroup 2 A := IsPGroup.of_card (n := 4) (by rw [hA]; norm_num)
  obtain ⟨QA, hQA⟩ := hApg.exists_le_sylow
  obtain ⟨QT, hQT⟩ := T16_pgroup.exists_le_sylow
  have hAQ : A = (QA : Subgroup S3) :=
    Subgroup.eq_of_le_of_card_ge hQA (by
      rw [hA]
      exact Nat.le_of_dvd (by norm_num) (card_dvd_sixteen QA.isPGroup'))
  have hTQ : T16 = (QT : Subgroup S3) :=
    Subgroup.eq_of_le_of_card_ge hQT (by
      rw [card_T16]
      exact Nat.le_of_dvd (by norm_num) (card_dvd_sixteen QT.isPGroup'))
  let e : QA ≃* QT := Sylow.equiv QA QT
  apply not_comm_T16
  intro a ha b hb
  have haQ : a ∈ (QT : Subgroup S3) := hTQ ▸ ha
  have hbQ : b ∈ (QT : Subgroup S3) := hTQ ▸ hb
  obtain ⟨a', ha'⟩ := e.surjective ⟨a, haQ⟩
  obtain ⟨b', hb'⟩ := e.surjective ⟨b, hbQ⟩
  have hab : a' * b' = b' * a' :=
    Subtype.ext (hc _ (hAQ ▸ a'.2) _ (hAQ ▸ b'.2))
  have := congrArg Subtype.val (show e (a' * b') = e (b' * a') by rw [hab])
  rw [map_mul, map_mul, ha', hb'] at this
  exact this

theorem resW_l33 : ResW Insp7.L33Fam := by
  intro L _ _ _ hF Gc _ _ ρ ž Ŝ Kh hin _
  obtain ⟨e₀⟩ := CFSG.QuasithinUnique.Unc25K1.psl33_equiv hF
  let φ : L ≃* S3 := e₀.trans CFSG.QuasithinUnique.Unc25K1.psl33EquivS3
  have hZ : Subgroup.center L = ⊥ :=
    center_eq_bot_of_mulEquiv φ CFSG.QuasithinUnique.Unc25K1.center_S3_eq_bot
  have hinj : Function.Injective (MulAut.conj : L →* MulAut L) := by
    rw [← MonoidHom.ker_eq_bot_iff, Insp7.ker_conj_eq_center, hZ]
  obtain ⟨-, -, -, -, hout⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.linear_model_outer_two_part_bound L 3 3 1 hF
  have hO : Nat.card (Outer L) ∣ 2 := by simpa using hout (by norm_num)
  obtain ⟨E, y, -, ⟨eE⟩, hy3, hyN, hfpf⟩ := hin.E
  set N : Subgroup Gc := (MulAut.conj : L →* MulAut L).range.comap ρ with hN
  have hNn : N.Normal := conj_range_normal.comap ρ
  have hNidx : N.index ∣ 2 := (index_comap_conj_dvd_outer ρ).trans hO
  have hEc' : ∀ a b : ↥E, a * b = b * a := fun a b =>
    eE.injective (by rw [map_mul, map_mul, mul_comm])
  have hEc : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hEc' ⟨a, ha⟩ ⟨b, hb⟩)
  have hE16 : Nat.card E = 16 := by
    rw [Nat.card_congr eE.toEquiv, Nat.card_prod]
    simp [Nat.card_eq_fintype_card]
  have hy3' : y ^ 3 = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3] at this
  have hyE : ∀ e ∈ E, y * e * y⁻¹ ∈ E := fun e he =>
    (Subgroup.mem_normalizer_iff.mp hyN e).mp he
  have hEN : E ≤ N :=
    le_of_relIndex_le_two_fpf hEc hy3' hyE hfpf
      (Nat.le_of_dvd (by norm_num) ((Subgroup.relIndex_dvd_index_of_normal N E).trans hNidx))
  let θ0 : ↥E →* ↥(MulAut.conj : L →* MulAut L).range :=
    (ρ.comp E.subtype).codRestrict _ (fun g => hEN g.2)
  let θ : ↥E →* S3 :=
    φ.toMonoidHom.comp ((MonoidHom.ofInjective hinj).symm.toMonoidHom.comp θ0)
  have hθ : Function.Injective θ := by
    refine φ.injective.comp ((MonoidHom.ofInjective hinj).symm.injective.comp ?_)
    intro a b h
    apply Subtype.ext
    apply hin.inj
    exact congrArg Subtype.val h
  have hθc : Nat.card θ.range = Nat.card E := Nat.card_range_of_injective hθ
  refine no_abelian_sixteen (A := θ.range) (by rw [hθc, hE16]) ?_
  rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
  rw [← map_mul, ← map_mul, hEc' a b]

end InspW2

end S143

end CFSG.Quasithin
