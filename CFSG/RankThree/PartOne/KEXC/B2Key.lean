module

public import CFSG.RankThree.PartOne.KLR.B2Twist
public import CFSG.RankThree.PartOne.KEXC.AbstractKey
public import CFSG.RankThree.PartOne.KEXC.BTSz
public import CFSG.RankThree.PartOne.KEXC.SzCentralizer
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.RankThree.PartOne.KEXC

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.PartOne.KE CFSG.RankThree.PartOne.KF4 CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KLR CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

section B2Struct

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a : ℕ}
  {L : Type} [Field L] [Algebra K L] [CharP L 2] [IsAlgClosed L] (D : ReeFrameData K L a)

theorem b2_exists_struct (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support) :
    ∃ Ξ : B2Q L ≃* antiSp L, (∀ g ∈ B2Q L, twistMap D.F n' g ∈ B2Q L) ∧
      ∀ x : B2Q L, ((x : ModGL ReeTag.F4.tag L) ∈ twistedFixed D.F n' ↔
        Ξ x ∈ (szEmbed hK (algebraMap K L)).range) := by
  classical
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  obtain ⟨ω, hω, hε1, hε2⟩ := b2_exists_eps hstab
  have hεW := wordProd_mem_parabolicWeylGroup_b2 (b2Words_letters ω hω)
  set ε := (coxeterSystem ReeTag.F4.tag).wordProd ω with hε
  set m := canonicalRep (coxeterSystem ReeTag.F4.tag) L ε with hm
  have hmQ : m ∈ B2Q L := canonicalRep_mem_subsystemGroup hεW
  have heq : ∀ g ∈ B2Q L, twistMap D.F n' g = twistMap D.F m g := fun g hg =>
    twist_eq_on_B2Q D hperm hε1 hε2 hg
  obtain ⟨S₀, hS₀, hLang⟩ := antiSp_lang_aut L a
  let mQ : B2Q L := ⟨m, hmQ⟩
  let M : antiSp L := B2eQ L mQ
  obtain ⟨h, hh⟩ := hLang M
  let Fm : B2Q L →* B2Q L := (MulAut.conj mQ).toMonoidHom.comp (B2Ftilde D)
  have hFm : ∀ x, B2eQ L (Fm x) = M * S₀ (B2eQ L x) * M⁻¹ := by
    intro x
    show B2eQ L (mQ * B2Ftilde D x * mQ⁻¹) = _
    rw [map_mul, map_mul, map_inv, B2eQ_Ftilde D hS₀]
  let Ξ : B2Q L ≃* antiSp L := (B2eQ L).trans (MulAut.conj h)
  have hΞ : ∀ x, Ξ x = h * B2eQ L x * h⁻¹ := fun x => rfl
  refine ⟨Ξ, ?_, ?_⟩
  · intro g hg
    rw [heq g hg]
    unfold twistMap
    exact mul_mem (mul_mem hmQ (fext_mem_B2Q D hg)) (inv_mem hmQ)
  · intro x
    have hxad := B2Q_le_adjointGroup x.2
    have hfix : (x : ModGL ReeTag.F4.tag L) ∈ twistedFixed D.F n' ↔ Fm x = x := by
      constructor
      · rintro ⟨-, hfx⟩
        refine Subtype.ext ?_
        show m * Fext D.F x * m⁻¹ = x
        have : twistMap D.F n' x = x := hfx
        rw [heq x x.2] at this
        exact this
      · intro hFx
        refine ⟨hxad, ?_⟩
        have h1 : m * Fext D.F x * m⁻¹ = x := congrArg Subtype.val hFx
        show twistMap D.F n' x = x
        rw [heq x x.2]
        exact h1
    rw [hfix, ← fixed_S0_iff_mem_range hK hS₀ (Ξ x)]
    have hShh : S₀ h = h * M := by rw [hh]; group
    have hS0 : S₀ (Ξ x) = h * (M * S₀ (B2eQ L x) * M⁻¹) * h⁻¹ := by
      rw [hΞ, map_mul, map_mul, map_inv, hShh]
      group
    rw [hS0, hΞ]
    constructor
    · intro hFx
      have := congrArg (B2eQ L) hFx
      rw [hFm] at this
      rw [this]
    · intro h1
      apply (B2eQ L).injective
      rw [hFm]
      have h2 : h * (M * S₀ (B2eQ L x) * M⁻¹) * h⁻¹ = h * B2eQ L x * h⁻¹ := h1
      have h3 := mul_right_cancel h2
      exact mul_left_cancel h3


theorem b2_key (ha : 1 ≤ a) (hK : Nat.card K = 2 ^ (2 * a + 1))
    {n' : ModGL ReeTag.F4.tag L} {w' : WeylGroup ReeTag.F4.tag} (hperm : PermAct n' w')
    (hstab : ∀ γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support,
      w' • ReeTag.F4.dualRoot γ ∈ parabolicRoots ReeTag.F4.tag f4B2Support)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpq : ¬ p ∣ Nat.card K - 1)
    {R : Subgroup (ModGL ReeTag.F4.tag L)} (hR0 : R ≠ ⊥) (hR2 : IsPGroup 2 R)
    (hRP : R ≤ B2Q L ⊓ twistedFixed D.F n')
    {b : Fin ReeTag.F4.tag.rank → Lˣ} (hbp : ∀ k, b k ^ p = 1)
    (hbfix : rootDiagUnit ReeTag.F4.tag b ∈ twistedFixed D.F n')
    (hbN : rootDiagUnit ReeTag.F4.tag b ∈ Subgroup.normalizer (R : Set (ModGL ReeTag.F4.tag L)))
    (hnt : b b2i1 ≠ 1 ∨ b b2i2 ≠ 1) : False := by
  classical
  obtain ⟨Ξ, hφQ, hΞ⟩ := b2_exists_struct D hK hperm hstab
  obtain ⟨m, hm⟩ := hp.odd_of_ne_two hp2
  set c₁ : Lˣ := b b2i1 with hc₁
  set c₂ : Lˣ := b b2i2 with hc₂
  let s₁ : Lˣ := c₁ * c₂
  let s₂ : Lˣ := (c₁ * c₂ ^ 2) ^ (m + 1)
  have hu : (c₁ * c₂ ^ 2) ^ p = 1 := by
    rw [mul_pow, ← pow_mul, mul_comm 2 p, pow_mul, hbp b2i1, hbp b2i2, one_pow, one_mul]
  have hs₂sq : s₂ ^ 2 = c₁ * c₂ ^ 2 := by
    show ((c₁ * c₂ ^ 2) ^ (m + 1)) ^ 2 = _
    rw [← pow_mul, show (m + 1) * 2 = p + 1 by omega, pow_succ, hu, one_mul]
  have hs₁p : s₁ ^ p = 1 := by
    show (c₁ * c₂) ^ p = 1
    rw [mul_pow, hbp b2i1, hbp b2i2, one_mul]
  have hs₂p : s₂ ^ p = 1 := by
    show ((c₁ * c₂ ^ 2) ^ (m + 1)) ^ p = 1
    rw [← pow_mul, mul_comm (m + 1) p, pow_mul, hu, one_pow]
  let bt : Fin ReeTag.F4.tag.rank → Lˣ := fun l =>
    s₁ ^ (Tag.F4.cartan b2i1 l) * s₂ ^ (Tag.F4.cartan b2i2 l)
  have hc11 : Tag.F4.cartan b2i1 b2i1 = 2 := by decide
  have hc21 : Tag.F4.cartan b2i2 b2i1 = -2 := by decide
  have hc12 : Tag.F4.cartan b2i1 b2i2 = -1 := by decide
  have hc22 : Tag.F4.cartan b2i2 b2i2 = 2 := by decide
  have hbt1 : bt b2i1 = c₁ := by
    show s₁ ^ (Tag.F4.cartan b2i1 b2i1) * s₂ ^ (Tag.F4.cartan b2i2 b2i1) = c₁
    rw [hc11, hc21, zpow_neg, zpow_ofNat, zpow_ofNat, hs₂sq]
    show (c₁ * c₂) ^ 2 * (c₁ * c₂ ^ 2)⁻¹ = c₁
    apply Units.ext
    have h1 : (c₁ : L) ≠ 0 := c₁.ne_zero
    have h2 : (c₂ : L) ≠ 0 := c₂.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  have hbt2 : bt b2i2 = c₂ := by
    show s₁ ^ (Tag.F4.cartan b2i1 b2i2) * s₂ ^ (Tag.F4.cartan b2i2 b2i2) = c₂
    rw [hc12, hc22, zpow_neg, zpow_one, zpow_ofNat, hs₂sq]
    show (c₁ * c₂)⁻¹ * (c₁ * c₂ ^ 2) = c₂
    apply Units.ext
    have h1 : (c₁ : L) ≠ 0 := c₁.ne_zero
    have h2 : (c₂ : L) ≠ 0 := c₂.ne_zero
    simp only [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_inv_eq_inv_val]
    field_simp
  have hK2 : CharP K 2 := ‹CharP K ReeTag.F4.prime›
  let δ : ModGL ReeTag.F4.tag L := rootDiagUnit ReeTag.F4.tag bt
  let e : ModGL ReeTag.F4.tag L := rootDiagUnit ReeTag.F4.tag b
  have hδ' : δ = torusElt ReeTag.F4.tag L b2i1 s₁ * torusElt ReeTag.F4.tag L b2i2 s₂ := by
    rw [torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul]
    rfl
  have hδQ : δ ∈ B2Q L := by
    rw [hδ']
    refine mul_mem ?_ ?_
    · exact subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus
        ((mem_f4B2Support _).2 (Or.inl rfl)) s₁)
    · exact subsystemTorus_le_subsystemGroup (torusElt_mem_subsystemTorus
        ((mem_f4B2Support _).2 (Or.inr rfl)) s₂)
  have hconj : ∀ x ∈ B2Q L, e * x * e⁻¹ = δ * x * δ⁻¹ := by
    intro x hx
    have hx' : x ∈ Subgroup.closure {g : ModGL ReeTag.F4.tag L |
        ∃ i : Fin ReeTag.F4.tag.rank, i ∈ f4B2Support ∧ ∃ c : L,
          g = xUnit ReeTag.F4.tag L i c ∨ g = yUnit ReeTag.F4.tag L i c} := hx
    refine MonoidHom.eqOn_closure (f := (MulAut.conj e).toMonoidHom)
      (g := (MulAut.conj δ).toMonoidHom) ?_ hx'
    rintro y ⟨i, hi, c, rfl | rfl⟩
    · show e * xUnit ReeTag.F4.tag L i c * e⁻¹ = δ * xUnit ReeTag.F4.tag L i c * δ⁻¹
      rw [(root_diagonal_conjugation ReeTag.F4.tag L b).1 i c,
        (root_diagonal_conjugation ReeTag.F4.tag L bt).1 i c]
      rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [hbt1]
      · rw [hbt2]
    · show e * yUnit ReeTag.F4.tag L i c * e⁻¹ = δ * yUnit ReeTag.F4.tag L i c * δ⁻¹
      rw [(root_diagonal_conjugation ReeTag.F4.tag L b).2.1 i c,
        (root_diagonal_conjugation ReeTag.F4.tag L bt).2.1 i c]
      rcases (mem_f4B2Support i).1 hi with rfl | rfl
      · rw [hbt1]
      · rw [hbt2]
  have hδφ : twistMap D.F n' δ = δ := by
    refine twist_delta_fixed (twistMap D.F n') (adjointGroup ReeTag.F4.tag L)
      (fun x hx y hy => twistMap_mul n' hx hy) (fun x hx => twistMap_inv n' hx) (B2Q L)
      (fun x hx => B2Q_le_adjointGroup hx) hφQ (B2Q L ⊓ twistedFixed D.F n')
      (fun g hg => ⟨hg.1, hg.2.2⟩) ?_ hδQ hconj ?_
    · intro y hy hcomm
      let yQ : B2Q L := ⟨y, hy⟩
      have hyQ : yQ = 1 := by
        apply Ξ.injective
        rw [map_one]
        apply szEmbed_centralizer_trivial ha hK (algebraMap K L) (Ξ yQ)
        intro s
        have hgΞ : Ξ (Ξ.symm (szEmbed hK (algebraMap K L) s)) = szEmbed hK (algebraMap K L) s :=
          Ξ.apply_symm_apply _
        have hgtw : ((Ξ.symm (szEmbed hK (algebraMap K L) s) : B2Q L) : ModGL ReeTag.F4.tag L) ∈
            twistedFixed D.F n' := (hΞ _).2 ⟨s, by rw [hgΞ]⟩
        have h1 := hcomm _ ⟨(Ξ.symm (szEmbed hK (algebraMap K L) s)).2, hgtw⟩
        have h2 : yQ * Ξ.symm (szEmbed hK (algebraMap K L) s) =
            Ξ.symm (szEmbed hK (algebraMap K L) s) * yQ := Subtype.ext h1
        have h3 := congrArg Ξ h2
        rwa [map_mul, map_mul, hgΞ] at h3
      exact congrArg Subtype.val hyQ
    · intro g hg
      refine ⟨?_, Subgroup.mul_mem _ (Subgroup.mul_mem _ hbfix hg.2) (Subgroup.inv_mem _ hbfix)⟩
      rw [hconj g hg.1]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hδQ hg.1) (Subgroup.inv_mem _ hδQ)
  have hδP : δ ∈ B2Q L ⊓ twistedFixed D.F n' := ⟨hδQ, B2Q_le_adjointGroup hδQ, hδφ⟩
  let Λ : suzukiGroup a K →* ModGL ReeTag.F4.tag L :=
    (B2Q L).subtype.comp ((Ξ.symm : antiSp L →* B2Q L).comp (szEmbed hK (algebraMap K L)))
  have hΛinj : Function.Injective Λ :=
    Subtype.val_injective.comp (Ξ.symm.injective.comp (szEmbed_injective hK _))
  have hΛP : ∀ g, g ∈ B2Q L ⊓ twistedFixed D.F n' ↔ ∃ s, g = Λ s := by
    intro g
    constructor
    · rintro ⟨hgQ, hgtw⟩
      obtain ⟨s, hs⟩ := (hΞ ⟨g, hgQ⟩).1 hgtw
      refine ⟨s, ?_⟩
      show g = ((Ξ.symm (szEmbed hK (algebraMap K L) s) : B2Q L) : ModGL ReeTag.F4.tag L)
      rw [hs, MulEquiv.symm_apply_apply]
    · rintro ⟨s, rfl⟩
      exact ⟨(Ξ.symm (szEmbed hK (algebraMap K L) s)).2, (hΞ _).2 ⟨s,
        (Ξ.apply_symm_apply (szEmbed hK (algebraMap K L) s)).symm⟩⟩
  have hzp : ∀ u : Lˣ, u ^ p = 1 → ∀ z : ℤ, (u ^ z) ^ p = 1 := fun u hu z => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hu, one_zpow]
  have hbtp : bt ^ p = 1 := by
    funext l
    simp only [Pi.pow_apply, Pi.one_apply, bt]
    rw [mul_pow, hzp _ hs₁p, hzp _ hs₂p, one_mul]
  have hδp : δ ^ p = 1 := by
    have := map_pow (rootDiagUnitHom ReeTag.F4.tag L) bt p
    rw [hbtp, map_one] at this
    exact this.symm
  have hpq' : ¬ p ∣ 2 ^ (2 * a + 1) - 1 := by rwa [← hK]
  have hnorm : ∀ x ∈ B2Q L ⊓ twistedFixed D.F n', (x ∈ R ↔ δ * x * δ⁻¹ ∈ R) := fun x hx => by
    rw [← hconj x hx.1]
    exact Subgroup.mem_normalizer_iff.1 hbN x
  have hδ1 : δ = 1 :=
    bt_of_param Λ hΛinj hΛP hR0 hR2 hRP
      (fun R₁ h0 h2 s hs hsN => suzukiGroup_bt ha hK hp hp2 hpq' h0 h2 hs hsN) hδP hδp hnorm
  have hact : ∀ i ∈ f4B2Support, (b i : Lˣ) = 1 := by
    intro i hi
    have hx : xUnit ReeTag.F4.tag L i 1 ∈ B2Q L := xUnit_mem_subsystemGroup hi _
    have h1 := hconj _ hx
    rw [hδ1, one_mul, inv_one, mul_one, (root_diagonal_conjugation ReeTag.F4.tag L b).1 i 1] at h1
    exact Units.ext (by simpa using xUnit_inj_F4 h1)
  rcases hnt with hnt | hnt
  · exact hnt (hact b2i1 ((mem_f4B2Support _).2 (Or.inl rfl)))
  · exact hnt (hact b2i2 ((mem_f4B2Support _).2 (Or.inr rfl)))

end B2Struct

end CFSG.RankThree.PartOne.KEXC
