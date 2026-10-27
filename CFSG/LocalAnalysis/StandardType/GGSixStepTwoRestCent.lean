module

public import CFSG.LocalAnalysis.StandardType.GGSixStepThreeCFComp
import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank

section Elem

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ggSup_card_eq_of_commute {A Z : Subgroup G}
    (hcomm : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a) (hAZ : A ⊓ Z = ⊥) :
    Nat.card ↥(A ⊔ Z) = Nat.card A * Nat.card Z := by
  set φ : A × Z →* G := A.subtype.noncommCoprod Z.subtype (fun a z => hcomm a a.2 z z.2)
  have hφ : ∀ (a : A) (z : Z), φ (a, z) = (a : G) * z := fun _ _ => rfl
  have hrange : φ.range = A ⊔ Z := (MonoidHom.noncommCoprod_range _ _ _).trans
    (by rw [Subgroup.range_subtype, Subgroup.range_subtype])
  have hinj : Function.Injective φ := by
    rw [injective_iff_map_eq_one]
    rintro ⟨a, z⟩ h
    rw [hφ] at h
    have ha : (a : G) = (z : G)⁻¹ := eq_inv_of_mul_eq_one_left h
    have ha1 : (a : G) = 1 := by
      have hmem : (a : G) ∈ A ⊓ Z := ⟨a.2, ha ▸ Z.inv_mem z.2⟩
      rw [hAZ] at hmem
      exact hmem
    have hz1 : (z : G) = 1 := by
      rw [ha1, one_mul] at h
      exact h
    exact Prod.ext (Subtype.ext ha1) (Subtype.ext hz1)
  rw [← hrange, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, Nat.card_prod]

omit [Finite G] in
theorem ggIsElemAbelian_sup_of_commute {p : ℕ} {A Z : Subgroup G} (hA : IsElemAbelian p A)
    (hZ : IsElemAbelian p Z) (hcomm : ∀ a ∈ A, ∀ z ∈ Z, a * z = z * a) :
    IsElemAbelian p (A ⊔ Z) := CFSG.Open.IsElemAbelian.sup_of_commute hA hZ hcomm

theorem ggCard_mul_card_le_of_commute {D S Bs : Subgroup G} (hD : D ≤ Bs) (hS : S ≤ Bs)
    (hcomm : ∀ x ∈ D, ∀ y ∈ S, x * y = y * x) (hDS : D ⊓ S = ⊥) :
    Nat.card D * Nat.card S ≤ Nat.card Bs := by
  rw [← ggSup_card_eq_of_commute hcomm hDS]
  exact Subgroup.card_le_of_le (sup_le hD hS)

end Elem

section Components

variable {G : Type} [Group G] [Finite G]

theorem ggComponentOf_eq_or_le_centralizer {K L₁ N : Subgroup G} (hK : IsComponentOf K N)
    (hL : IsComponentOf L₁ N) : K = L₁ ∨ K ≤ Subgroup.centralizer (L₁ : Set G) := by
  have hK' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hK.1).mp hK
  have hL' := (CFSG.LocalAnalysis.ComponentInitial.isComponentOf_iff_isComponent_subgroupOf
    hL.1).mp hL
  rcases CFSG.LocalCores.distinct_components_commute hK' hL' with h | h
  · left
    have h' := Subgroup.subgroupOf_inj.mp h
    rwa [inf_eq_left.mpr hK.1, inf_eq_left.mpr hL.1] at h'
  · right
    have hc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hmem := hc (Subgroup.mem_subgroupOf.mpr (show ((⟨k, hK.1 hk⟩ : N) : G) ∈ K from hk))
    rw [Subgroup.mem_centralizer_iff] at hmem
    have := hmem ⟨l, hL.1 hl⟩ (Subgroup.mem_subgroupOf.mpr hl)
    exact congrArg Subtype.val this

theorem ggComponent_normal_of_forall {L₁ N : Subgroup G} (hL : IsComponentOf L₁ N)
    (h : ∀ n ∈ N, L₁.map (MulAut.conj n).toMonoidHom ≤ Subgroup.centralizer (L₁ : Set G) →
      L₁.map (MulAut.conj n).toMonoidHom = L₁) :
    (L₁.subgroupOf N).Normal := by
  rw [Subgroup.normal_subgroupOf_iff hL.1]
  intro l n hl hn
  have heq : L₁.map (MulAut.conj n).toMonoidHom = L₁ := by
    rcases ggComponentOf_eq_or_le_centralizer (ggIsComponentOf_conj hL hn) hL with h' | h'
    · exact h'
    · exact h n hn h'
  have hmem : n * l * n⁻¹ ∈ L₁.map (MulAut.conj n).toMonoidHom :=
    ⟨l, hl, by simp [MulAut.conj_apply]⟩
  rwa [heq] at hmem

omit [Finite G] in
theorem ggIsElemAbelian_zpowers {p : ℕ} {b : G} (hb : b ^ p = 1) :
    IsElemAbelian p (Subgroup.zpowers b) := CFSG.Open.isElemAbelian_zpowers hb

theorem ggStepTwo_normal_of_rank {p : ℕ} (hp : p.Prime) {Bs L₁ : Subgroup G} {b : G}
    (hBs : IsElemAbelian p Bs) (hb : b ∈ Bs) (hb1 : b ≠ 1)
    (hL : IsComponentOf L₁ (Subgroup.centralizer {b})) (hA : p ^ 2 ≤ Nat.card ↥(Bs ⊓ L₁))
    (hbL : b ∉ L₁)
    (hrank : ∀ F : Subgroup G, F ≤ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L₁ : Set G) →
      IsElemAbelian p F → Nat.card F ≤ p ^ 2) :
    (L₁.subgroupOf (Subgroup.centralizer {b})).Normal := by
  have : Fact p.Prime := ⟨hp⟩
  have hbo : orderOf b = p := orderOf_eq_prime (hBs.2 b hb) hb1
  refine ggComponent_normal_of_forall hL fun n hn hcent => ?_
  by_contra hne
  have hAel : IsElemAbelian p (Bs ⊓ L₁) :=
    ⟨⟨⟨fun u v => Subtype.ext (show (u : G) * v = v * u from congrArg Subtype.val
      (hBs.1.is_comm.comm ⟨u, u.2.1⟩ ⟨v, v.2.1⟩))⟩⟩, fun u hu => hBs.2 u hu.1⟩
  have hA'el : IsElemAbelian p ((Bs ⊓ L₁).map (MulAut.conj n).toMonoidHom) :=
    isElemAbelian_map_hom hAel _
  have hA'card : Nat.card ((Bs ⊓ L₁).map (MulAut.conj n).toMonoidHom) = Nat.card ↥(Bs ⊓ L₁) :=
    Subgroup.card_map_of_injective (MulAut.conj n).injective
  have hA'L : (Bs ⊓ L₁).map (MulAut.conj n).toMonoidHom ≤ L₁.map (MulAut.conj n).toMonoidHom :=
    Subgroup.map_mono inf_le_right
  have hLC : L₁.map (MulAut.conj n).toMonoidHom ≤ Subgroup.centralizer {b} := by
    have h := Subgroup.map_mono (f := (MulAut.conj n).toMonoidHom) hL.1
    have hN : (Subgroup.centralizer {b}).map (MulAut.conj n).toMonoidHom =
        Subgroup.centralizer {b} :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hn)
    rwa [hN] at h
  have hbX : b ∈ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L₁ : Set G) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr rfl, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hL.1 hl)⟩
  have hbA' : b ∉ (Bs ⊓ L₁).map (MulAut.conj n).toMonoidHom := by
    rintro ⟨a, ha, hab⟩
    have hnb : n * b = b * n := Subgroup.mem_centralizer_singleton_iff.mp hn
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hab
    have hab' : a = b := by
      calc a = n⁻¹ * (n * a * n⁻¹) * n := by group
        _ = n⁻¹ * b * n := by rw [hab]
        _ = b := by rw [mul_assoc, ← hnb, ← mul_assoc, inv_mul_cancel, one_mul]
    exact hbL (hab' ▸ ha.2)
  have hcomm : ∀ a ∈ (Bs ⊓ L₁).map (MulAut.conj n).toMonoidHom, ∀ z ∈ Subgroup.zpowers b,
      a * z = z * a := by
    intro a ha z hz
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hab : a * b = b * a := Subgroup.mem_centralizer_singleton_iff.mp (hLC (hA'L ha))
    exact (Commute.zpow_right hab k).eq
  have hinf : (Bs ⊓ L₁).map (MulAut.conj n).toMonoidHom ⊓ Subgroup.zpowers b = ⊥ := by
    rcases ((Bs ⊓ L₁).map (MulAut.conj n).toMonoidHom ⊓ Subgroup.zpowers b).bot_or_exists_ne_one
      with h | ⟨y, hy, hy1⟩
    · exact h
    · exfalso
      have hbmem : b ∈ Subgroup.zpowers y :=
        mem_zpowers_of_orderOf_prime (hbo ▸ hp) (Subgroup.mem_inf.mp hy).2 hy1
      exact hbA' (Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hy).1 hbmem)
  have hFel := ggIsElemAbelian_sup_of_commute hA'el (ggIsElemAbelian_zpowers (hBs.2 b hb)) hcomm
  have hFcard := ggSup_card_eq_of_commute hcomm hinf
  have hFX : (Bs ⊓ L₁).map (MulAut.conj n).toMonoidHom ⊔ Subgroup.zpowers b ≤
      Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L₁ : Set G) :=
    sup_le (le_inf (hA'L.trans hLC) (hA'L.trans hcent)) (Subgroup.zpowers_le.mpr hbX)
  have h := hrank _ hFX hFel
  rw [hFcard, hA'card, Nat.card_zpowers, hbo] at h
  have h' : p ^ 2 * p ≤ p ^ 2 := (Nat.mul_le_mul_right p hA).trans h
  have hp1 := hp.one_lt
  nlinarith

end Components

section Pairs

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}

theorem ggStepTwo_inf_ne_bot_of_card_le (hp : p.Prime) (hBs : IsElemAbelian p Bs) (hDBs : D ≤ Bs)
    (hDcard : Nat.card D = p ^ 2) {e : G} {Le : Subgroup G}
    (hpair : GGStepTwoPair p B Bs x L D J e Le)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (Le : Set G)) ≤ p)
    (hidx : Nat.card Bs ≤
      p * Nat.card ↥((Bs ⊓ Le) ⊔ (Bs ⊓ Subgroup.centralizer (Le : Set G)))) :
    D ⊓ (Subgroup.zpowers e ⊔ Le) ≠ ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have := hBs.1
  have heo : orderOf e = p := orderOf_eq_prime (hBs.2 e hpair.1) hpair.2.1
  have heC : Subgroup.zpowers e ≤ Bs ⊓ Subgroup.centralizer (Le : Set G) := by
    rw [Subgroup.zpowers_le]
    refine Subgroup.mem_inf.mpr ⟨hpair.1, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact Subgroup.mem_centralizer_singleton_iff.mp (hpair.le_centralizer hl)
  have hCeq : Bs ⊓ Subgroup.centralizer (Le : Set G) = Subgroup.zpowers e :=
    (Subgroup.eq_of_le_of_card_ge heC (by rw [Nat.card_zpowers, heo]; exact hC)).symm
  have hSle : (Bs ⊓ Le) ⊔ (Bs ⊓ Subgroup.centralizer (Le : Set G)) ≤ Subgroup.zpowers e ⊔ Le :=
    sup_le (inf_le_right.trans le_sup_right) (hCeq.le.trans le_sup_left)
  intro hbot
  have hDS : D ⊓ ((Bs ⊓ Le) ⊔ (Bs ⊓ Subgroup.centralizer (Le : Set G))) = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left D hSle).trans hbot.le)
  have hSBs : (Bs ⊓ Le) ⊔ (Bs ⊓ Subgroup.centralizer (Le : Set G)) ≤ Bs :=
    sup_le inf_le_left inf_le_left
  have hcomm : ∀ a ∈ D, ∀ c ∈ (Bs ⊓ Le) ⊔ (Bs ⊓ Subgroup.centralizer (Le : Set G)),
      a * c = c * a := fun a ha c hc =>
    congrArg Subtype.val (mul_comm' (⟨a, hDBs ha⟩ : Bs) ⟨c, hSBs hc⟩)
  have hle := ggCard_mul_card_le_of_commute hDBs hSBs hcomm hDS
  rw [hDcard] at hle
  have hpos : 0 < Nat.card ↥((Bs ⊓ Le) ⊔ (Bs ⊓ Subgroup.centralizer (Le : Set G))) :=
    Nat.card_pos
  have h2 := hle.trans hidx
  have h3 : p ^ 2 ≤ p := Nat.le_of_mul_le_mul_right h2 hpos
  have hp1 := hp.one_lt
  nlinarith

end Pairs

section Inputs

@[expose] def GGStepTwoBstarIndexInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        Nat.card Bs ≤ p * Nat.card ↥((Bs ⊓ L₁) ⊔ (Bs ⊓ Subgroup.centralizer (L₁ : Set G)))

theorem ggStepTwo_controls_of_card_le (h613 : GGStepTwoLemmaSixThirteenInput)
    (h614 : GGStepTwoSubnormalInput) (hidx : GGStepTwoBstarIndexInput)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {t : StatedLieTag} {n f : ℕ} {ψ : (ggU t n f).K →* G}
    (hctx : GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ) (s1 : GGSixStepOne p B Bs x L D J)
    (hlin : ¬ GGStepTwoLinearType p t f) {e : G} {Le : Subgroup G}
    (hpair : GGStepTwoPair p B Bs x L D J e Le)
    (hC : Nat.card ↥(Bs ⊓ Subgroup.centralizer (Le : Set G)) ≤ p) :
    GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers e) := by
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨⟨hBBs, hBsEl, -⟩, ⟨⟨hDB, -, hDcard, -⟩, -⟩, -, -, -, ⟨hBsM, -⟩, -⟩ := hctx.2
  have hsn := h614 G p B Bs x L D J t n f ψ hctx s1 hlin e Le hpair
  have hne := ggStepTwo_inf_ne_bot_of_card_le hp hBsEl (hDB.trans hBBs) hDcard hpair hC
    (hidx G p B Bs x L D J t n f ψ hctx s1 hlin e Le hpair)
  rcases (D ⊓ (Subgroup.zpowers e ⊔ Le)).bot_or_exists_ne_one with hbot | ⟨d, hd, hd1⟩
  · exact absurd hbot hne
  have hCe := hpair.centralizer_le_of_mem hBsM s1.2.1 hsn (Subgroup.mem_inf.mp hd).1 hd1
    (Subgroup.mem_inf.mp hd).2
  exact (hpair.stepTwo_of_fusion hp hBsEl hBsM hCe
    (h613 G p B Bs x L D J t n f ψ hctx s1 hlin e hpair.1 hCe)).2

@[expose] def GGStepTwoContraryWitnessInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        IsSubnormal L₁ (Subgroup.centralizer {b}) → D ⊓ (Subgroup.zpowers b ⊔ L₁) = ⊥ →
          ∃ e ∈ Bs ⊓ Subgroup.centralizer (L₁ : Set G), e ≠ 1 ∧ ∃ Le : Subgroup G,
            IsComponentOf Le (ggG0 p B x L D J ⊓ Subgroup.centralizer {e}) ∧
            Nat.card ↥(Bs ⊓ Subgroup.centralizer (Le : Set G)) ≤ p

@[expose] def GGStepTwoContraryXInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        IsSubnormal L₁ (Subgroup.centralizer {b}) → D ⊓ (Subgroup.zpowers b ⊔ L₁) = ⊥ →
        (∃ e ∈ Bs ⊓ Subgroup.centralizer (L₁ : Set G), e ≠ 1 ∧
          GGControlsStrongFusion (ggM p B x L D J) (Subgroup.zpowers e)) →
          Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L₁ : Set G) ≤ ggM p B x L D J

@[expose] def GGStepTwoContraryNormalizerInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        IsSubnormal L₁ (Subgroup.centralizer {b}) → D ⊓ (Subgroup.zpowers b ⊔ L₁) = ⊥ →
          Subgroup.centralizer {b} ⊓ Subgroup.normalizer (L₁ : Set G) ≤ ggM p B x L D J →
            Subgroup.centralizer {b} ≤ ggM p B x L D J

@[expose] def GGStepTwoContraryRankInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (B Bs : Subgroup G) (x : G) (L D J : Subgroup G)
    (t : StatedLieTag) (n f : ℕ) (ψ : (ggU t n f).K →* G),
    GGSixCtxV2 p B Bs x L D J (ggU t n f).D t n f ψ → GGSixStepOne p B Bs x L D J →
    ¬ GGStepTwoLinearType p t f →
      ∀ (b : G) (L₁ : Subgroup G), GGStepTwoPair p B Bs x L D J b L₁ →
        IsSubnormal L₁ (Subgroup.centralizer {b}) → D ⊓ (Subgroup.zpowers b ⊔ L₁) = ⊥ →
          p ^ 2 ≤ Nat.card ↥(Bs ⊓ L₁) ∧ b ∉ L₁ ∧
          ∀ F : Subgroup G,
            F ≤ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L₁ : Set G) →
              IsElemAbelian p F → Nat.card F ≤ p ^ 2

theorem ggStepTwoContraryNormalizerInput_of_rank (h : GGStepTwoContraryRankInput) :
    GGStepTwoContraryNormalizerInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR hN
  have hp : p.Prime := hctx.1.2.2.2.2.2.1.1
  obtain ⟨⟨-, hBsEl, -⟩, -⟩ := hctx.2
  obtain ⟨hA, hbL, hrank⟩ := h G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR
  have hL : IsComponentOf L₁ (Subgroup.centralizer {b}) :=
    ⟨hpair.le_centralizer, hsn, hpair.2.2.1.2.2⟩
  have hnorm := ggStepTwo_normal_of_rank hp hBsEl hpair.1 hpair.2.1 hL hA hbL hrank
  exact fun g hg => hN (Subgroup.mem_inf.mpr ⟨hg, ggMem_normalizer_of_normal hL.1 hnorm hg⟩)

theorem ggStepTwo_normalizer_le {G : Type} [Group G] {M L₁ : Subgroup G} {b e : G}
    (hfus : GGControlsStrongFusion M (Subgroup.zpowers e)) (he1 : e ≠ 1)
    (heX : e ∈ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L₁ : Set G))
    (hXM : Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L₁ : Set G) ≤ M) :
    Subgroup.centralizer {b} ⊓ Subgroup.normalizer (L₁ : Set G) ≤ M := by
  intro n hn
  obtain ⟨hnb, hnL⟩ := Subgroup.mem_inf.mp hn
  obtain ⟨heb, heL⟩ := Subgroup.mem_inf.mp heX
  refine hfus.mem_of_conj_mem (Subgroup.mem_zpowers e) he1 (hXM (Subgroup.mem_inf.mpr ⟨?_, ?_⟩))
  · exact (Subgroup.centralizer {b}).mul_mem
      ((Subgroup.centralizer {b}).mul_mem ((Subgroup.centralizer {b}).inv_mem hnb) heb) hnb
  · rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have hl' : n * l * n⁻¹ ∈ L₁ := (Subgroup.mem_normalizer_iff.mp hnL l).mp hl
    have hc : n * l * n⁻¹ * e = e * (n * l * n⁻¹) := Subgroup.mem_centralizer_iff.mp heL _ hl'
    calc l * (n⁻¹ * e * n) = n⁻¹ * (n * l * n⁻¹ * e) * n := by group
      _ = n⁻¹ * (e * (n * l * n⁻¹)) * n := by rw [hc]
      _ = n⁻¹ * e * n * l := by group

theorem ggStepTwoCentralizerInput_of_rest (h613 : GGStepTwoLemmaSixThirteenInput)
    (h614 : GGStepTwoSubnormalInput) (hidx : GGStepTwoBstarIndexInput)
    (hwit : GGStepTwoContraryWitnessInput) (hX : GGStepTwoContraryXInput)
    (hN : GGStepTwoContraryNormalizerInput) : GGStepTwoCentralizerInput := by
  intro G _ _ p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR
  obtain ⟨⟨-, hBsEl, -⟩, -⟩ := hctx.2
  obtain ⟨e, he, he1, Le, hLe, hLeC⟩ :=
    hwit G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR
  have hepair : GGStepTwoPair p B Bs x L D J e Le :=
    ⟨(Subgroup.mem_inf.mp he).1, he1, hLe, hLeC.trans (Nat.le_self_pow two_ne_zero p)⟩
  have hfus := ggStepTwo_controls_of_card_le h613 h614 hidx hctx s1 hlin hepair hLeC
  have hXM := hX G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR ⟨e, he, he1, hfus⟩
  have := hBsEl.1
  have heX : e ∈ Subgroup.centralizer {b} ⊓ Subgroup.centralizer (L₁ : Set G) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mpr (congrArg Subtype.val
      (mul_comm' (⟨e, (Subgroup.mem_inf.mp he).1⟩ : Bs) ⟨b, hpair.1⟩)),
      (Subgroup.mem_inf.mp he).2⟩
  exact hN G p B Bs x L D J t n f ψ hctx s1 hlin b L₁ hpair hsn hDR
    (ggStepTwo_normalizer_le hfus he1 heX hXM)

end Inputs

end CFSG.StandardType
