module

public import CFSG.RankThree.PartTwo.Sec14.Std
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.RankThree.PartTwo.Sec14.Ronan148AConjComp
import CFSG.RankThree.PartTwo.Sec14.Ronan148JProd
import CFSG.RankThree.PartTwo.Sec14.Item14Res2ProofLBalComp
import CFSG.RankThree.PartTwo.Sec4.Ronan148VON
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.LocalAnalysis.GLTheoremA.CatA.Rk2Tab.LowerLift
import CFSG.Sporadic.ONOddCore.OuterOrder
import CFSG.Sporadic.ON
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148A

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS

@[expose] def NoE81TwoLocal (Q : Type*) [Group Q] : Prop :=
  ∀ T E : Subgroup Q, T ≠ ⊥ → IsPGroup 2 T → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 3 ^ 4 →
    E ≤ Subgroup.normalizer (T : Set Q) → False

variable {G : Type} [Group G] [Finite G]

theorem noE81TwoLocal_quot {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {H : Subgroup G}
    {N : Subgroup ↥H} [N.Normal] (hN : ¬ 3 ∣ Nat.card N) : NoE81TwoLocal (↥H ⧸ N) := by
  intro T E hT hT2 hE hEcard hTE
  have h1 := CFSG.LocalAnalysis.GLTheoremA.le_evenRank_of_quotient (G := ↥H)
    (N := N) Nat.prime_three (by norm_num) hN hT hT2 hE hEcard hTE
  have h2 := evenRank_subgroup_le H
  have h3 := h.evenRank_eq
  omega

section Group

variable {Q : Type} [Group Q] [Finite Q]

theorem false_of_commuting_twoLocal_quot (hQ : NoE81TwoLocal Q) {J T E₁ E₂ : Subgroup Q}
    (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTJ : T ≤ J) (hE₁J : E₁ ≤ J)
    (hE₁T : E₁ ≤ Subgroup.normalizer (T : Set Q)) (hE₁ : CFSG.Open.IsElemAbelian 3 E₁)
    (hE₂C : E₂ ≤ Subgroup.centralizer (J : Set Q)) (hE₂ : CFSG.Open.IsElemAbelian 3 E₂)
    (hint : E₁ ⊓ E₂ = ⊥) (hcard : Nat.card E₁ * Nat.card E₂ = 81) : False := by
  have hcomm : ∀ x ∈ E₁, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    Subgroup.mem_centralizer_iff.mp (hE₂C hy) x (hE₁J hx)
  have hc₁ : ∀ x ∈ E₁, ∀ y ∈ E₁, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₁.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hc₂ : ∀ x ∈ E₂, ∀ y ∈ E₂, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE₂.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hmem : ∀ x ∈ E₁ ⊔ E₂, ∃ x₁ ∈ E₁, ∃ x₂ ∈ E₂, x = x₁ * x₂ := by
    intro x hx
    rw [← Ronan148J.commProdHom_range hcomm] at hx
    obtain ⟨⟨x₁, x₂⟩, rfl⟩ := MonoidHom.mem_range.mp hx
    exact ⟨x₁, x₁.2, x₂, x₂.2, Ronan148J.commProdHom_apply hcomm _⟩
  have hE : CFSG.Open.IsElemAbelian 3 (E₁ ⊔ E₂) := by
    refine ⟨⟨⟨fun x y => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · obtain ⟨x₁, hx₁, x₂, hx₂, hx⟩ := hmem x.1 x.2
      obtain ⟨y₁, hy₁, y₂, hy₂, hy⟩ := hmem y.1 y.2
      change (x : Q) * y = y * x
      rw [hx, hy]
      have h1 : x₂ * y₁ = y₁ * x₂ := (hcomm y₁ hy₁ x₂ hx₂).symm
      have h2 : y₂ * x₁ = x₁ * y₂ := (hcomm x₁ hx₁ y₂ hy₂).symm
      calc x₁ * x₂ * (y₁ * y₂) = x₁ * (x₂ * y₁) * y₂ := by simp only [mul_assoc]
        _ = x₁ * (y₁ * x₂) * y₂ := by rw [h1]
        _ = (x₁ * y₁) * (x₂ * y₂) := by simp only [mul_assoc]
        _ = (y₁ * x₁) * (y₂ * x₂) := by rw [hc₁ x₁ hx₁ y₁ hy₁, hc₂ x₂ hx₂ y₂ hy₂]
        _ = y₁ * (x₁ * y₂) * x₂ := by simp only [mul_assoc]
        _ = y₁ * (y₂ * x₁) * x₂ := by rw [h2]
        _ = y₁ * y₂ * (x₁ * x₂) := by simp only [mul_assoc]
    · obtain ⟨x₁, hx₁, x₂, hx₂, rfl⟩ := hmem x hx
      rw [(Commute.mul_pow (hcomm x₁ hx₁ x₂ hx₂) 3), hE₁.2 x₁ hx₁, hE₂.2 x₂ hx₂, one_mul]
  have hN : E₁ ≤ Subgroup.normalizer (E₂ : Set Q) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      (hcomm x hx z hz).symm)
  have hcard' := Sec6.card_sup_mul_card_inf hN
  rw [hint, Subgroup.card_bot, mul_one, hcard] at hcard'
  have hE₂T : E₂ ≤ Subgroup.normalizer (T : Set Q) := fun x hx =>
    Subgroup.centralizer_le_normalizer _ ((Subgroup.centralizer_le hTJ) (hE₂C hx))
  exact hQ T (E₁ ⊔ E₂) hT hT2 hE (by rw [hcard']; norm_num) (sup_le hE₁T hE₂T)

theorem map_conj_eq_of_twoLocal_quot (hQ : NoE81TwoLocal Q) {J T E₁ F : Subgroup Q}
    (hJ : IsComponent J) (hT : T ≠ ⊥) (hT2 : IsPGroup 2 T) (hTJ : T ≤ J) (hE₁J : E₁ ≤ J)
    (hE₁T : E₁ ≤ Subgroup.normalizer (T : Set Q)) (hE₁ : CFSG.Open.IsElemAbelian 3 E₁)
    (hFJ : F ≤ J) (hF : CFSG.Open.IsElemAbelian 3 F)
    (hFZ : F ⊓ Subgroup.centralizer (J : Set Q) = ⊥)
    (hcard : Nat.card E₁ * Nat.card F = 81) (x : Q) :
    J.map (MulAut.conj x).toMonoidHom = J := by
  by_contra hne
  set D := J.map (MulAut.conj x).toMonoidHom with hD
  have hDc : IsComponent D := Res2LBal.isComponent_conj hJ x
  have hDC : D ≤ Subgroup.centralizer (J : Set Q) := fun y hy =>
    Res2LBal.mem_centralizer_of_mem_of_ne hJ hDc (fun h' => hne h'.symm) hy
  set E₂ := F.map (MulAut.conj x).toMonoidHom with hE₂
  have hE₂D : E₂ ≤ D := Subgroup.map_mono hFJ
  have hinj : Function.Injective (MulAut.conj x).toMonoidHom := (MulAut.conj x).injective
  have hint : E₁ ⊓ E₂ = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hy₁, hy₂⟩
    obtain ⟨f, hf, rfl⟩ := hy₂
    have hfC : f ∈ Subgroup.centralizer (J : Set Q) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have hc := Subgroup.mem_centralizer_iff.mp (hDC (Res2LBal.conj_mem_map hj x))
        ((MulAut.conj x).toMonoidHom f) (hE₁J hy₁)
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hc
      have : x * (f * j) * x⁻¹ = x * (j * f) * x⁻¹ := by
        calc x * (f * j) * x⁻¹ = x * f * x⁻¹ * (x * j * x⁻¹) := by group
          _ = x * j * x⁻¹ * (x * f * x⁻¹) := hc
          _ = x * (j * f) * x⁻¹ := by group
      exact (mul_left_cancel (mul_right_cancel this)).symm
    have : f ∈ F ⊓ Subgroup.centralizer (J : Set Q) := ⟨hf, hfC⟩
    rw [hFZ, Subgroup.mem_bot] at this
    rw [this, map_one]
    exact Subgroup.one_mem _
  exact false_of_commuting_twoLocal_quot hQ hT hT2 hTJ hE₁J hE₁T hE₁ (hE₂D.trans hDC)
    (CFSG.SectionRank.isElemAbelian_map hF _) hint
    (by rw [Subgroup.card_map_of_injective hinj]; exact hcard)

theorem map_conj_eq_of_tripleCover_ON_quot
    (hQ : NoE81TwoLocal Q) {J : Subgroup Q} (hJ : IsComponent J)
    (hJON : Sec4.IsTripleCover ↥J CFSG.Blueprint.NativeSporadic.ON) (x : Q) :
    J.map (MulAut.conj x).toMonoidHom = J := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨T, E, hT, hT2, hE, hEc, hET⟩ :=
    exists_twoLocal_rank_three_of_tripleCover_ON hJON hJ.1.1
  obtain ⟨u, hu3, huZ⟩ := Sec4.Ronan148V.exists_noncentral_of_isTripleCover_ON hJON
  have hinj : Function.Injective J.subtype := J.subtype_injective
  have hu1 : u ≠ 1 := fun h1 => huZ (h1 ▸ Subgroup.one_mem _)
  have hu1' : (u : Q) ≠ 1 := fun h1 => hu1 (Subtype.ext h1)
  have hu3' : (u : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hu3
  have hFJ : Subgroup.zpowers (u : Q) ≤ J := Subgroup.zpowers_le.mpr u.2
  have hF : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers (u : Q)) := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a.2
      obtain ⟨l, hl⟩ := Subgroup.mem_zpowers_iff.mp b.2
      change (a : Q) * b = b * a
      rw [← hk, ← hl, ← zpow_add, ← zpow_add, add_comm]
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu3', one_zpow]
  have hFc : Nat.card (Subgroup.zpowers (u : Q)) = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hu3' hu1']
  have hFZ : Subgroup.zpowers (u : Q) ⊓ Subgroup.centralizer (J : Set Q) = ⊥ := by
    have hdvd : Nat.card ↥(Subgroup.zpowers (u : Q) ⊓ Subgroup.centralizer (J : Set Q)) ∣ 3 :=
      hFc ▸ Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h1
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have heq := Subgroup.eq_of_le_of_card_ge (inf_le_left :
        Subgroup.zpowers (u : Q) ⊓ Subgroup.centralizer (J : Set Q) ≤ Subgroup.zpowers (u : Q))
        (by rw [hFc, h1])
      have huC : (u : Q) ∈ Subgroup.centralizer (J : Set Q) :=
        (heq.symm ▸ Subgroup.mem_zpowers (u : Q)).2
      apply huZ
      rw [Subgroup.mem_center_iff]
      intro g
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp huC g g.2)
  refine map_conj_eq_of_twoLocal_quot hQ hJ
    ((Subgroup.map_eq_bot_iff_of_injective T hinj).not.mpr hT)
    (hT2.map _) (Subgroup.map_subtype_le T) (Subgroup.map_subtype_le E)
    ((Subgroup.map_mono hET).trans (Subgroup.le_normalizer_map _))
    (CFSG.SectionRank.isElemAbelian_map hE _) hFJ hF hFZ ?_ x
  rw [Subgroup.card_map_of_injective hinj, hEc, hFc]

theorem normal_of_forall_map_conj_eq {J : Subgroup Q}
    (h : ∀ x : Q, J.map (MulAut.conj x).toMonoidHom = J) : J.Normal := by
  refine ⟨fun n hn g => ?_⟩
  rw [← h g]
  exact ⟨n, hn, rfl⟩

end Group

theorem card_outer_dvd_four_of_tripleCover_ON
    {X : Type*} [Group X]
    (hX : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) (hXp : Group.IsPerfect X) :
    Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer X) ∣ 4 := by
  haveI := hXp
  obtain ⟨-, ⟨e⟩⟩ := hX
  have hinj := CFSG.ComponentClassification.OuterAutomorphisms.centerQuotient_outer_injective X
  set f := (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toMonoidHom.comp
    (CFSG.ComponentClassification.OuterAutomorphisms.centerQuotientOuterHom X) with hf
  have hfinj : Function.Injective f :=
    (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).injective.comp hinj
  exact (Subgroup.card_dvd_of_injective f hfinj).trans
    CFSG.Sporadic.ONOddCore.r3e_on_outer_order_divides_four.1

theorem not_twentyfive_dvd_card_mulAut_of_tripleCover_ON
    {X : Type*} [Group X]
    (hX : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) (hXp : Group.IsPerfect X) :
    ¬ 25 ∣ Nat.card (MulAut X) := by
  have hout := card_outer_dvd_four_of_tripleCover_ON hX hXp
  obtain ⟨hZ, ⟨e⟩⟩ := hX
  have hXcard : Nat.card X = 460815505920 * 3 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center X), hZ,
      Nat.card_congr e.toEquiv, CFSG.Sporadic.ON.card_ON]
  have hinn : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.inner X) ∣ Nat.card X :=
    Subgroup.card_range_dvd _
  have hmul := (CFSG.ComponentClassification.OuterAutomorphisms.inner X).card_mul_index
  rw [Subgroup.index] at hmul
  have hdvd : Nat.card (MulAut X) ∣ 460815505920 * 3 * 4 := by
    rw [← hmul, ← hXcard]
    exact Nat.mul_dvd_mul hinn hout
  intro h25
  have := h25.trans hdvd
  norm_num at this

section Count

variable {R : Type} [Group R] [Finite R]

theorem card_subgroupOf_dvd {X W : Subgroup R} : Nat.card (W.subgroupOf X) ∣ Nat.card W := by
  let f : ↥(W.subgroupOf X) →* ↥W :=
    { toFun := fun x => ⟨((x : X) : R), Subgroup.mem_subgroupOf.mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Subgroup.card_dvd_of_injective f fun x y hxy => by
    apply Subtype.ext; apply Subtype.ext
    exact congrArg (fun z : ↥W => (z : R)) hxy

theorem commutator_mem_of_mul_mem {X V W : Subgroup R} (hXW : X ≤ Subgroup.normalizer (W : Set R))
    (hXV : ⁅X, V⁆ ≤ W) {x v : R} (hv : v ∈ V) (hxv : x * v ∈ W) {x₁ : R} (hx₁ : x₁ ∈ X) :
    x₁ * x * x₁⁻¹ * x⁻¹ ∈ W := by
  set w := x * v with hw
  have hx : x = w * v⁻¹ := by rw [hw]; group
  have h1 : x₁ * w * x₁⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hXW hx₁) w).mp hxv
  have h2 : x₁ * v⁻¹ * x₁⁻¹ * v⁻¹⁻¹ ∈ W := by
    have := hXV (Subgroup.commutator_mem_commutator hx₁ (V.inv_mem hv))
    rwa [commutatorElement_def] at this
  have e : x₁ * x * x₁⁻¹ * x⁻¹ = (x₁ * w * x₁⁻¹) * (x₁ * v⁻¹ * x₁⁻¹ * v⁻¹⁻¹) * w⁻¹ := by
    rw [hx]; group
  rw [e]
  exact W.mul_mem (W.mul_mem h1 h2) (W.inv_mem hxv)

theorem map_eq_one_of_commutator_mem {X W : Subgroup R} (hXW : X ≤ Subgroup.normalizer (W : Set R))
    (hW3 : ¬ 3 ∣ Nat.card W) {S : Type} [Group S] [Finite S] (hS : IsSimpleGroup S)
    (h3S : 3 ∣ Nat.card S) (hSab : ∃ a b : S, a * b ≠ b * a) (f : ↥X →* S)
    (hf : Function.Surjective f) {x : ↥X} (hx : ∀ x₁ : ↥X, (x₁ : R) * x * x₁⁻¹ * x⁻¹ ∈ W) :
    f x = 1 := by
  have hnorm : (W.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hXW g.2) n).mp hn
  have hmapN : ((W.subgroupOf X).map f).Normal := hnorm.map f hf
  have hbot : (W.subgroupOf X).map f = ⊥ := by
    haveI := hmapN
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((W.subgroupOf X).map f) with h | h
    · exact h
    · exfalso
      have hc : Nat.card ((W.subgroupOf X).map f) ∣ Nat.card W :=
        (Subgroup.card_map_dvd _ _).trans card_subgroupOf_dvd
      rw [h, Subgroup.card_top] at hc
      exact hW3 (h3S.trans hc)
  have hcen : f x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro s
    obtain ⟨x₁, rfl⟩ := hf s
    have hmem : x₁ * x * x₁⁻¹ * x⁻¹ ∈ W.subgroupOf X := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hx x₁
    have h1 : f (x₁ * x * x₁⁻¹ * x⁻¹) = 1 := by
      have : f (x₁ * x * x₁⁻¹ * x⁻¹) ∈ (W.subgroupOf X).map f := ⟨_, hmem, rfl⟩
      rwa [hbot, Subgroup.mem_bot] at this
    simp only [map_mul, map_inv] at h1
    calc f x₁ * f x = f x₁ * f x * (f x₁)⁻¹ * (f x)⁻¹ * (f x * f x₁) := by group
      _ = f x * f x₁ := by rw [h1, one_mul]
  have hZ : Subgroup.center S = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
    · exact h
    · exfalso
      obtain ⟨a, b, hab⟩ := hSab
      exact hab (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top b) a)
  rw [hZ, Subgroup.mem_bot] at hcen
  exact hcen

theorem card_mul_card_dvd_of_commutator_le {X V W : Subgroup R}
    (hXW : X ≤ Subgroup.normalizer (W : Set R)) (hVW : V ≤ Subgroup.normalizer (W : Set R))
    (hXV : ⁅X, V⁆ ≤ W) (hW3 : ¬ 3 ∣ Nat.card W)
    {S T : Type} [Group S] [Group T] [Finite S] [Finite T] (hS : IsSimpleGroup S)
    (hT : IsSimpleGroup T) (h3S : 3 ∣ Nat.card S) (h3T : 3 ∣ Nat.card T)
    (hSab : ∃ a b : S, a * b ≠ b * a) (hTab : ∃ a b : T, a * b ≠ b * a)
    (f : ↥X →* S) (hf : Function.Surjective f) (g : ↥V →* T) (hg : Function.Surjective g) :
    Nat.card S * Nat.card T ∣ Nat.card ↥(X ⊔ V ⊔ W) := by
  set Nm := Subgroup.normalizer (W : Set R) with hNm
  set H := X ⊔ V ⊔ W with hH
  have hHN : H ≤ Nm := sup_le (sup_le hXW hVW) Subgroup.le_normalizer
  haveI hWn : (W.subgroupOf Nm).Normal := Subgroup.normal_in_normalizer
  set π := QuotientGroup.mk' (W.subgroupOf Nm) with hπ
  have hπW : ∀ y : ↥Nm, π y = 1 ↔ (y : R) ∈ W := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  have hVX : ⁅V, X⁆ ≤ W := (Subgroup.commutator_comm V X).le.trans hXV
  have hcomm : ∀ (x : ↥X) (v : ↥V), π ⟨x, hXW x.2⟩ * π ⟨v, hVW v.2⟩ =
      π ⟨v, hVW v.2⟩ * π ⟨x, hXW x.2⟩ := by
    intro x v
    have hmem : (x : R) * v * (x : R)⁻¹ * (v : R)⁻¹ ∈ W := by
      have := hXV (Subgroup.commutator_mem_commutator x.2 v.2)
      rwa [commutatorElement_def] at this
    have h1 : π (⟨x, hXW x.2⟩ * ⟨v, hVW v.2⟩ * (⟨x, hXW x.2⟩)⁻¹ * (⟨v, hVW v.2⟩)⁻¹) = 1 :=
      (hπW _).mpr hmem
    simp only [map_mul, map_inv] at h1
    calc π ⟨x, hXW x.2⟩ * π ⟨v, hVW v.2⟩
        = π ⟨x, hXW x.2⟩ * π ⟨v, hVW v.2⟩ * (π ⟨x, hXW x.2⟩)⁻¹ * (π ⟨v, hVW v.2⟩)⁻¹ *
          (π ⟨v, hVW v.2⟩ * π ⟨x, hXW x.2⟩) := by group
      _ = π ⟨v, hVW v.2⟩ * π ⟨x, hXW x.2⟩ := by rw [h1, one_mul]
  let μ : ↥X × ↥V →* ↥Nm ⧸ W.subgroupOf Nm :=
    (π.comp (Subgroup.inclusion hXW)).noncommCoprod (π.comp (Subgroup.inclusion hVW))
      (fun x v => hcomm x v)
  have hμ : ∀ p : ↥X × ↥V, μ p = π ⟨p.1, hXW p.1.2⟩ * π ⟨p.2, hVW p.2.2⟩ := fun _ => rfl
  have hker : μ.ker ≤ (f.prodMap g).ker := by
    intro p hp
    rw [MonoidHom.mem_ker, hμ, ← map_mul] at hp
    have hxv : (p.1 : R) * p.2 ∈ W := (hπW _).mp hp
    have hvx : (p.2 : R) * p.1 ∈ W := by
      have := (Subgroup.mem_normalizer_iff.mp (hXW (X.inv_mem p.1.2)) _).mp hxv
      simpa [mul_assoc] using this
    rw [MonoidHom.mem_ker, MonoidHom.coe_prodMap, Prod.map_apply, Prod.mk_eq_one]
    refine ⟨map_eq_one_of_commutator_mem hXW hW3 hS h3S hSab f hf fun x₁ =>
      commutator_mem_of_mul_mem hXW hXV p.2.2 hxv x₁.2,
      map_eq_one_of_commutator_mem hVW hW3 hT h3T hTab g hg fun v₁ =>
      commutator_mem_of_mul_mem hVW hVX p.1.2 hvx v₁.2⟩
  have hfg : Function.Surjective (f.prodMap g) := fun ⟨s, t⟩ => by
    obtain ⟨x, rfl⟩ := hf s
    obtain ⟨v, rfl⟩ := hg t
    exact ⟨(x, v), rfl⟩
  have e1 := Subgroup.card_eq_card_quotient_mul_card_subgroup μ.ker
  have e2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (f.prodMap g).ker
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange μ).toEquiv] at e1
  rw [Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _ hfg).toEquiv] at e2
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hker
  have hpos : 0 < Nat.card μ.ker := Nat.card_pos
  have hrange : Nat.card μ.range = Nat.card (S × T) * k := by
    rw [e2, hk] at e1
    apply Nat.eq_of_mul_eq_mul_right hpos
    rw [← e1]
    ring
  have hST : Nat.card S * Nat.card T ∣ Nat.card μ.range := by
    rw [hrange, ← Nat.card_prod]
    exact Dvd.intro k rfl
  have hle : μ.range ≤ (H.subgroupOf Nm).map π := by
    rintro _ ⟨p, rfl⟩
    rw [hμ, ← map_mul]
    refine ⟨⟨p.1, hXW p.1.2⟩ * ⟨p.2, hVW p.2.2⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
    exact H.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left p.1.2))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right p.2.2))
  refine hST.trans ((Subgroup.card_dvd_of_le hle).trans ((Subgroup.card_map_dvd _ _).trans ?_))
  exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hHN).toEquiv).dvd

theorem exists_lift_range {P M S : Type} [Group P] [Group M] [Group S] (u : P →* M) (φ : P →* S)
    (hφ : Function.Surjective φ) (hker : u.ker ≤ φ.ker) :
    ∃ f : ↥u.range →* S, Function.Surjective f ∧ ∀ p : P, f (u.rangeRestrict p) = φ p := by
  let e := QuotientGroup.quotientKerEquivRange u
  let φ' := QuotientGroup.lift u.ker φ hker
  refine ⟨φ'.comp e.symm.toMonoidHom, ?_, fun p => ?_⟩
  · intro s
    obtain ⟨p, rfl⟩ := hφ s
    exact ⟨e (p : P ⧸ u.ker), by simp [φ']⟩
  · have : e.symm (u.rangeRestrict p) = (p : P ⧸ u.ker) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    simp [this, φ']

end Count

end CFSG.RankThree.PartTwo.Sec14.Ronan148A
