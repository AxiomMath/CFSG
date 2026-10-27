module

public import CFSG.LocalAnalysis.StandardType.TableC.HypDefs
public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutInnerExcSixE
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerAdj
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerE7
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcAutRank
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcE8Five
public import CFSG.RankThree.PartOne.Mult.Exceptional
public import CFSG.Adapters.TauCetiExceptional.EvenAll
public import CFSG.HardMathSupport.Timmesfeld.CrossChar.ExcInnerSylow
public import CFSG.LieType.SeitzGeneration.ExcHigh.FrameLayer
public import CFSG.RankThree.Classical2.TwistedE6Phi3Centralizer
public import CFSG.RankThree.Lattice.SteinbergBIE6EvenBruhat
public import CFSG.RankThree.Lattice.SteinbergBIE6Qplus
public import CFSG.RankThree.Lattice.SteinbergBIGenPerfect
public import CFSG.RankThree.Lattice.SteinbergBIGenQuasisimple
public import CFSG.RankThree.PartOne.KE.A1Fixed
public import CFSG.RankThree.PartOne.KE.E7FourLattice
public import CFSG.RankThree.PartOne.KE.E7FourStabBase
public import CFSG.RankThree.PartOne.KE.E8ClassLists
public import CFSG.RankThree.PartOne.KE.E8D4Family
public import CFSG.RankThree.PartOne.KE.E8FourA1Family
public import CFSG.RankThree.PartOne.KE.SLnShape
public import CFSG.RankThree.PartOne.KE6.Phi3Arith
public import CFSG.RankThree.PartOne.KE6.Phi6Arith
public import CFSG.RankThree.PartOne.KF4.KernelTools
public import CFSG.RankThree.PartOne.KGD.D4QA1
public import CFSG.Sporadic.Schreier.J4SProfileNode

public section

namespace CFSG.StandardType.TableCRes

open CFSG.Assembly CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.Open
open CFSG.LieType.Steinberg.Isogeny CFSG.LieType.SeitzGeneration
open CFSG.Blueprint.Chevalley (Tag)
open CFSG.LocalAnalysis.GLTheoremA.S267.BadExc (card_le_cat_F4 card_le_cat_E6 card_le_cat_E7
  card_le_cat_E8_all five_le_of_three_le_orderOf)
open CFSG.HardMathSupport.Timmesfeld.CrossChar (eq_of_three_le_degCount_E6
  eq_of_three_le_degCount_E7 eq_of_three_le_degCount_E8)

section Embedding

variable {X : Type} [Group X]

private theorem conj_mem_centralizer_of_mem_normalizer {G₀ : Subgroup X} {n c : X}
    (hn : n ∈ Subgroup.normalizer (G₀ : Set X)) (hc : c ∈ Subgroup.centralizer (G₀ : Set X)) :
    n * c * n⁻¹ ∈ Subgroup.centralizer (G₀ : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hc ⊢
  intro y hy
  have hy' : n⁻¹ * y * n ∈ G₀ := by
    have h1 := (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * y * n)).mpr
    have h2 : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
    exact h1 (by rw [h2]; exact hy)
  have h3 := hc _ hy'
  calc y * (n * c * n⁻¹) = n * ((n⁻¹ * y * n) * c) * n⁻¹ := by group
    _ = n * (c * (n⁻¹ * y * n)) * n⁻¹ := by rw [h3]
    _ = n * c * n⁻¹ * y := by group

theorem exists_injective_hom_of_inner {G₀ B : Subgroup X}
    (hcomm : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a)
    (hBN : B ≤ Subgroup.normalizer (G₀ : Set X))
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    (hfaith : B ⊓ Subgroup.centralizer (G₀ : Set X) = ⊥) :
    ∃ β : B →* ↥G₀ ⧸ Subgroup.center ↥G₀, Function.Injective β := by
  classical
  choose! g hg hbg using hin
  have hcen : ∀ a b : ↥G₀, (a : X)⁻¹ * b ∈ Subgroup.centralizer (G₀ : Set X) →
      (QuotientGroup.mk a : ↥G₀ ⧸ Subgroup.center ↥G₀) = QuotientGroup.mk b := by
    intro a b hab
    rw [QuotientGroup.eq, Subgroup.mem_center_iff]
    intro z
    have := Subgroup.mem_centralizer_iff.mp hab (z : X) z.2
    exact Subtype.ext (by simpa using this)
  have hkey : ∀ b₁ ∈ B, ∀ b₂ ∈ B, (g (b₁ * b₂))⁻¹ * (g b₂ * g b₁) ∈
      Subgroup.centralizer (G₀ : Set X) := by
    intro b₁ hb₁ b₂ hb₂
    have h1 := hbg b₁ hb₁
    have h2 := hbg b₂ hb₂
    have h3 := hbg (b₁ * b₂) (B.mul_mem hb₁ hb₂)
    have h4 : b₁ * (b₂ * g b₂) * b₁⁻¹ ∈ Subgroup.centralizer (G₀ : Set X) :=
      conj_mem_centralizer_of_mem_normalizer (hBN hb₁) h2
    have h5 : b₁ * b₂ * (g b₂ * g b₁) ∈ Subgroup.centralizer (G₀ : Set X) := by
      have : b₁ * b₂ * (g b₂ * g b₁) = (b₁ * (b₂ * g b₂) * b₁⁻¹) * (b₁ * g b₁) := by group
      rw [this]
      exact mul_mem h4 h1
    have h6 := mul_mem (inv_mem h3) h5
    have : (b₁ * b₂ * g (b₁ * b₂))⁻¹ * (b₁ * b₂ * (g b₂ * g b₁)) =
        (g (b₁ * b₂))⁻¹ * (g b₂ * g b₁) := by group
    rwa [this] at h6
  let γ : B → ↥G₀ ⧸ Subgroup.center ↥G₀ := fun b =>
    QuotientGroup.mk (⟨g b, hg b b.2⟩ : ↥G₀)
  have hmul : ∀ b₁ b₂ : B, γ (b₁ * b₂) = γ b₂ * γ b₁ := by
    intro b₁ b₂
    change (QuotientGroup.mk (⟨g (b₁ * b₂ : B), _⟩ : ↥G₀) : ↥G₀ ⧸ Subgroup.center ↥G₀) =
      QuotientGroup.mk ⟨g b₂, _⟩ * QuotientGroup.mk ⟨g b₁, _⟩
    rw [← QuotientGroup.mk_mul]
    exact hcen _ _ (hkey b₁ b₁.2 b₂ b₂.2)
  let β : B →* ↥G₀ ⧸ Subgroup.center ↥G₀ := MonoidHom.mk' γ fun b₁ b₂ =>
    calc γ (b₁ * b₂) = γ (b₂ * b₁) := by
          congr 1
          exact Subtype.ext (hcomm _ b₁.2 _ b₂.2)
      _ = γ b₁ * γ b₂ := hmul b₂ b₁
  refine ⟨β, (injective_iff_map_eq_one β).mpr fun b hb => ?_⟩
  have h1 : (⟨g b, hg b b.2⟩ : ↥G₀) ∈ Subgroup.center ↥G₀ := (QuotientGroup.eq_one_iff _).mp hb
  have h2 : g b ∈ Subgroup.centralizer (G₀ : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have := Subgroup.mem_center_iff.mp h1 ⟨z, hz⟩
    exact congrArg Subtype.val this
  have h3 : (b : X) ∈ Subgroup.centralizer (G₀ : Set X) := by
    have := mul_mem (hbg b b.2) (inv_mem h2)
    simpa using this
  have h4 : (b : X) ∈ B ⊓ Subgroup.centralizer (G₀ : Set X) := ⟨b.2, h3⟩
  rw [hfaith, Subgroup.mem_bot] at h4
  exact Subtype.ext h4

end Embedding

section InnerCard

variable {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.presents
    {ψ : (ggU t n f).K →* X} (h : GGTCHyp t n f ψ p G₀ B D J L x) :
    GGPresentsG0 G₀ (ggU t n f).D t n f ψ :=
  ⟨⟨h.adm, h.rank_two⟩, ⟨h.range, h.ker⟩, h.perfect, h.model⟩

theorem GGTCHyp.card_le_of_inner
    {ψ : (ggU t n f).K →* X}
    (h : GGTCHyp t n f ψ p G₀ B D J L x)
    (hin : ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X))
    {Y : Type} [Group Y] (e : ↥G₀ ⧸ Subgroup.center ↥G₀ ≃* Y) {k : ℕ}
    (hY : ∀ F : Subgroup Y, IsElemAbelian p F → Nat.card F ≤ p ^ k) : Nat.card B ≤ p ^ k := by
  obtain ⟨β, hβ⟩ := exists_injective_hom_of_inner
    (fun a ha b hb => IsElemAbelian.comm h.b_elem ha hb) h.b_norm hin h.b_faithful
  set φ : ↥B →* Y := e.toMonoidHom.comp β with hφdef
  have hφ : Function.Injective φ := e.injective.comp hβ
  have hel : IsElemAbelian p φ.range := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨a', ha'⟩ := a.2
      obtain ⟨b', hb'⟩ := b.2
      apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul, ← ha', ← hb', ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (IsElemAbelian.comm h.b_elem a'.2 b'.2)
    · obtain ⟨b', rfl⟩ := hy
      have hb : b' ^ p = 1 := Subtype.ext (h.b_elem.2 b' b'.2)
      rw [← map_pow, hb, map_one]
  have hcard : Nat.card B = Nat.card φ.range :=
    Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv
  rw [hcard]
  exact hY _ hel

end InnerCard

section InnerTags

variable {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

theorem GGTCHyp.inner_F4
    {ψ : (ggU .F4 n f).K →* X} (h : GGTCHyp .F4 n f ψ p G₀ B D J L x) :
    ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X) := fun b hb =>
  ggPsiDiagInner_F4 X n f ψ G₀ h.presents b (h.b_norm hb) (h.b_diag b hb)

theorem GGTCHyp.inner_E7
    {ψ : (ggU .E7 n f).K →* X} (h : GGTCHyp .E7 n f ψ p G₀ B D J L x) :
    ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X) := fun b hb =>
  ggPsiDiagInner_E7 X n f ψ G₀ h.presents b (h.b_norm hb) (h.b_diag b hb)

theorem GGTCHyp.inner_E8
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x) :
    ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X) := fun b hb =>
  ggPsiDiagInner_E8 X n f ψ G₀ h.presents b (h.b_norm hb) (h.b_diag b hb)

theorem GGTCHyp.inner_E6
    {ψ : (ggU .E6 n f).K →* X} (h : GGTCHyp .E6 n f ψ p G₀ B D J L x)
    (hp3 : p ≠ 3 ∨ ¬ 3 ∣ 2 ^ f - 1) :
    ∀ b ∈ B, ∃ g ∈ G₀, b * g ∈ Subgroup.centralizer (G₀ : Set X) := by
  intro b hb
  have hcN : b ∈ Subgroup.normalizer (G₀ : Set X) := h.b_norm hb
  have hcp : b ^ p = 1 := h.b_elem.2 b hb
  have hci := h.b_diag b hb
  have hker := h.ker
  have hperf := h.perfect
  have hf : 1 ≤ f := h.adm.2.1
  have hrange := h.range
  subst hrange
  have hkπ := LayerSixE.ker_le_ker_e6Isogeny hker
  obtain ⟨α, hαD, hα⟩ := LayerSixE.exists_induces_E6 ψ hker hcN hci
  have hπ := e6Isogeny_surjective (GaloisField 2 f)
  have hαp : α ^ p = 1 := by
    have h1 := hα.pow hkπ hcN p
    rw [hcp] at h1
    exact LayerSixE.GGInduces.unique hπ (Subgroup.one_mem _) h1 (LayerSixE.GGInduces.one hkπ)
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hinn := OrdPInnerExc.mem_inn_of_inndiag_E6 h.prime (by rw [hK]; exact hp3) hαD hαp
  have hkc := CFSG.ClassicalInvolution.ModelFacts.ChevAut.e6Isogeny_ker_le_center
    (GaloisField 2 f)
  obtain ⟨y, rfl⟩ := hinn
  obtain ⟨w, rfl⟩ := hπ y
  have hwN : ψ w⁻¹ ∈ Subgroup.normalizer (ψ.range : Set X) :=
    Subgroup.le_normalizer ⟨w⁻¹, rfl⟩
  have hd := hα.mul hwN (LayerSixE.GGInduces.psi hkπ w⁻¹)
  rw [← map_mul, ← map_mul, mul_inv_cancel, map_one, map_one] at hd
  have hcd := OrdPInnerExc.mem_centralizer_of_induces_one hkc hperf (mul_mem hcN hwN) hd
  exact ⟨ψ w⁻¹, ⟨w⁻¹, rfl⟩, hcd⟩

end InnerTags

section Gen

variable {t : StatedLieTag} {X : Type} [Group X] [Finite X] {n f p : ℕ}
  {G₀ B D J L : Subgroup X} {x : X}

private theorem degCount_E6_le {e : ℕ} (he : 3 ≤ e) : degCount Tag.E6 e ≤ 3 := by
  by_contra hlt
  rcases eq_of_three_le_degCount_E6 (e := e) (by omega) with rfl | rfl | rfl
  · omega
  · omega
  · exact hlt (by decide)

private theorem degCount_E7_le {e : ℕ} (he : 3 ≤ e) : degCount Tag.E7 e ≤ 3 := by
  by_contra hlt
  rcases eq_of_three_le_degCount_E7 (e := e) (by omega) with rfl | rfl | rfl | rfl
  · omega
  · omega
  · exact hlt (by decide)
  · exact hlt (by decide)

private theorem degCount_E8_le {e : ℕ} (he3 : e ≠ 3) (he4 : e ≠ 4) (he6 : e ≠ 6) (he : 3 ≤ e) :
    degCount Tag.E8 e ≤ 2 := by
  by_contra hlt
  rcases eq_of_three_le_degCount_E8 (e := e) (by omega) with rfl | rfl | rfl | rfl | rfl <;> omega

private theorem three_le_orderOf_of_ne {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hc1 : orderOf ((2 : ZMod p) ^ f) ≠ 1) (hc2 : orderOf ((2 : ZMod p) ^ f) ≠ 2) :
    3 ≤ orderOf ((2 : ZMod p) ^ f) := by
  have : Fact p.Prime := ⟨hp⟩
  have h2 : (2 : ZMod p) ≠ 0 := by
    intro h0
    have : ((2 : ℕ) : ZMod p) = 0 := by exact_mod_cast h0
    rw [ZMod.natCast_eq_zero_iff] at this
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp this)
  have h0 : (2 : ZMod p) ^ f ≠ 0 := pow_ne_zero f h2
  have hfin : orderOf ((2 : ZMod p) ^ f) ≠ 0 := by
    have : orderOf ((2 : ZMod p) ^ f) ∣ p - 1 :=
      orderOf_dvd_of_pow_eq_one (ZMod.pow_card_sub_one_eq_one h0)
    intro h
    rw [h, zero_dvd_iff] at this
    have := hp.two_le
    omega
  omega

private theorem exists_cat_equiv
    {G : Type} [Group G] {t : StatedLieTag} {f : ℕ}
    (ht : t ∈ chevalleyExceptionalTags) (hm : ChevalleyExceptionalModel G t 2 f) :
    ∃ d : TauCeti.ValidLieTypeIndex, CFSG.Models.NamesTag d.1 t 2 f ∧ Nonempty (G ≃* Cat d) :=
  CFSG.RankThree.PartOne.Mult.exists_index_of_chevalley
    CFSG.TauCetiBridge.Even.chevalleyBridgesAll Nat.prime_two ht hm

theorem upper_E6_gen
    {ψ : (ggU .E6 n f).K →* X} (h : GGTCHyp .E6 n f ψ p G₀ B D J L x)
    (hc1 : orderOf ((2 : ZMod p) ^ f) ≠ 1) (hc2 : orderOf ((2 : ZMod p) ^ f) ≠ 2) :
    Nat.card B ≤ p ^ 3 := by
  have hp := h.prime
  have hc := three_le_orderOf_of_ne hp h.ne_two hc1 hc2
  obtain ⟨⟨d, hv⟩, hn, ⟨e⟩⟩ := exists_cat_equiv (t := .E6) (by decide)
    (h.model.chevalleyExceptionalModel (by decide))
  cases d with
  | E6 Q =>
    obtain ⟨hQp, hQe⟩ := hn
    have hQc : Q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def, hQp, hQe]
    have hQ : ((Q.card : ℕ) : ZMod p) = (2 : ZMod p) ^ f := by rw [hQc]; push_cast; rfl
    have he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p) := by rw [hQ]; exact hc
    have hpq : p ≠ Q.p := by rw [hQp]; exact h.ne_two
    have hp3 : p ≠ 3 := by have := five_le_of_three_le_orderOf hp he; omega
    refine h.card_le_of_inner (h.inner_E6 (Or.inl hp3)) e (k := 3) fun F hF => ?_
    exact (card_le_cat_E6 hv hp hpq he hF).trans
      (Nat.pow_le_pow_right hp.pos (max_le (by norm_num) (degCount_E6_le he)))
  | _ => exact hn.elim

theorem upper_E7_gen
    {ψ : (ggU .E7 n f).K →* X} (h : GGTCHyp .E7 n f ψ p G₀ B D J L x)
    (hc1 : orderOf ((2 : ZMod p) ^ f) ≠ 1) (hc2 : orderOf ((2 : ZMod p) ^ f) ≠ 2) :
    Nat.card B ≤ p ^ 3 := by
  have hp := h.prime
  have hc := three_le_orderOf_of_ne hp h.ne_two hc1 hc2
  obtain ⟨⟨d, hv⟩, hn, ⟨e⟩⟩ := exists_cat_equiv (t := .E7) (by decide)
    (h.model.chevalleyExceptionalModel (by decide))
  cases d with
  | E7 Q =>
    obtain ⟨hQp, hQe⟩ := hn
    have hQc : Q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def, hQp, hQe]
    have hQ : ((Q.card : ℕ) : ZMod p) = (2 : ZMod p) ^ f := by rw [hQc]; push_cast; rfl
    have he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p) := by rw [hQ]; exact hc
    have hpq : p ≠ Q.p := by rw [hQp]; exact h.ne_two
    refine h.card_le_of_inner h.inner_E7 e (k := 3) fun F hF => ?_
    exact (card_le_cat_E7 hv hp hpq he hF).trans
      (Nat.pow_le_pow_right hp.pos (max_le (by norm_num) (degCount_E7_le he)))
  | _ => exact hn.elim

theorem upper_E8_gen_ne
    {ψ : (ggU .E8 n f).K →* X} (h : GGTCHyp .E8 n f ψ p G₀ B D J L x)
    (hc1 : orderOf ((2 : ZMod p) ^ f) ≠ 1) (hc2 : orderOf ((2 : ZMod p) ^ f) ≠ 2)
    (hc3 : orderOf ((2 : ZMod p) ^ f) ≠ 3) (hc4 : orderOf ((2 : ZMod p) ^ f) ≠ 4)
    (hc6 : orderOf ((2 : ZMod p) ^ f) ≠ 6) : Nat.card B ≤ p ^ 2 := by
  have hp := h.prime
  have hc := three_le_orderOf_of_ne hp h.ne_two hc1 hc2
  obtain ⟨⟨d, hv⟩, hn, ⟨e⟩⟩ := exists_cat_equiv (t := .E8) (by decide)
    (h.model.chevalleyExceptionalModel (by decide))
  cases d with
  | E8 Q =>
    obtain ⟨hQp, hQe⟩ := hn
    have hQc : Q.card = 2 ^ f := by rw [TauCeti.PrimePower.card_def, hQp, hQe]
    have hQ : ((Q.card : ℕ) : ZMod p) = (2 : ZMod p) ^ f := by rw [hQc]; push_cast; rfl
    have he : 3 ≤ orderOf ((Q.card : ℕ) : ZMod p) := by rw [hQ]; exact hc
    have hpq : p ≠ Q.p := by rw [hQp]; exact h.ne_two
    have hd : degCount Tag.E8 (orderOf ((Q.card : ℕ) : ZMod p)) ≤ 2 := by
      rw [hQ]
      exact degCount_E8_le hc3 hc4 hc6 hc
    refine h.card_le_of_inner h.inner_E8 e (k := 2) fun F hF => ?_
    exact (card_le_cat_E8_all hv hp hpq he hF).trans
      (Nat.pow_le_pow_right hp.pos (max_le (by norm_num) hd))
  | _ => exact hn.elim

end Gen

end CFSG.StandardType.TableCRes

end
