module

public import CFSG.Milestones.ASVolI.F48.Id
public import CFSG.GH74.KGroups.Generic6
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP1Emb

public section

namespace CFSG.ASVolI

open CFSG.Quasithin CFSG.Quasithin.H13.F431.U42Aut
open CFSG.Quasithin.H13.F431.U42 (Y P45 Xs Xs_eq card_Xs lieModel_Y
  isSimpleGroup_of_lieModel_PSU_four_two)
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45 exists_model)

theorem burnsideF48s_autc_self_of_lie {X : Type} [Group X] [IsSimpleGroup X] {p : ℕ}
    {B P₁ P₂ : Subgroup X} (hX : ChF.IsLieParabolics p (⊤ : Subgroup X) B P₁ P₂)
    {Q : Subgroup X} (hQ : Q = P₁ ∨ Q = P₂) :
    ∀ g : X, (∀ x, x ∈ Q ↔ g * x * g⁻¹ ∈ Q) → g ∈ Q := by
  obtain ⟨-, hne, -, hmax⟩ := hX
  have hcoat : ∀ R : Subgroup X, (R = P₁ ∨ R = P₂) →
      R ≠ ⊤ ∧ ∀ R' : Subgroup X, R < R' → R' = ⊤ := fun R hR => by
    obtain ⟨-, -, htop, hm⟩ := (hmax R).2 hR
    exact ⟨htop, fun R' h => hm R' h le_top⟩
  intro g hg
  by_contra hgQ
  have hN : Q < Subgroup.normalizer (Q : Set X) :=
    lt_of_le_of_ne Subgroup.le_normalizer fun h =>
      hgQ (by rw [h]; exact Subgroup.mem_normalizer_iff.2 hg)
  haveI hQn : Q.Normal := Subgroup.normalizer_eq_top_iff.1 ((hcoat Q hQ).2 _ hN)
  rcases hQn.eq_bot_or_eq_top with h | h
  · obtain ⟨Q', hQ', hne'⟩ : ∃ Q', (Q' = P₁ ∨ Q' = P₂) ∧ Q ≠ Q' := by
      rcases hQ with rfl | rfl
      · exact ⟨P₂, Or.inr rfl, hne⟩
      · exact ⟨P₁, Or.inl rfl, Ne.symm hne⟩
    exact (hcoat Q' hQ').1 ((hcoat Q hQ).2 Q' (lt_of_le_of_ne (by rw [h]; exact bot_le) hne'))
  · exact (hcoat Q hQ).1 h

section Normalizer


theorem burnsideF48s_autc_normalizer_eq {P : Subgroup Y} {Phat : Subgroup Ah}
    (hself : ∀ g : Y, (∀ x, x ∈ P ↔ g * x * g⁻¹ ∈ P) → g ∈ P) (h1 : P.map incl ≤ Phat)
    (h2 : Phat ≤ Subgroup.normalizer ((P.map incl : Subgroup Ah) : Set Ah)) {t : Ah} (ht : t ∈ Phat)
    (htY : t ∉ Yh) : Subgroup.normalizer ((P.map incl : Subgroup Ah) : Set Ah) = Phat := by
  have hY : ∀ h ∈ Subgroup.normalizer ((P.map incl : Subgroup Ah) : Set Ah), h ∈ Yh → h ∈ Phat := by
    intro h hN hYh
    obtain ⟨y, rfl⟩ := (mem_Yh_iff_incl h).1 hYh
    have hy : y ∈ P := hself y fun x => by
      have e := Subgroup.mem_normalizer_iff.1 hN (incl x)
      have e2 : incl y * incl x * (incl y)⁻¹ = incl (y * x * y⁻¹) := by
        rw [map_mul, map_mul, map_inv]
      rw [e2, Subgroup.mem_map_iff_mem incl_injective,
        Subgroup.mem_map_iff_mem incl_injective] at e
      exact e
    exact h1 (Subgroup.mem_map_of_mem incl hy)
  refine le_antisymm (fun h hN => ?_) h2
  by_cases hYh : h ∈ Yh
  · exact hY h hN hYh
  · have htY' : t⁻¹ ∉ Yh := fun h' => htY (Yh.inv_mem_iff.1 h')
    have hm : h * t⁻¹ ∈ Yh :=
      (Subgroup.mul_mem_iff_of_index_two index_Yh).2 (iff_of_false hYh htY')
    have hmN : h * t⁻¹ ∈ Subgroup.normalizer ((P.map incl : Subgroup Ah) : Set Ah) :=
      Subgroup.mul_mem _ hN (Subgroup.inv_mem _ (h2 ht))
    have := Phat.mul_mem (hY _ hmN hm) ht
    simpa using this

end Normalizer

theorem burnsideF48s_autc_eq_normalizer {X E : Type} [Group X] [Group E]
    {Gp M₁ M₂ M : Subgroup E} [hGp : Gp.Normal] (ε : X ≃* ↥Gp) {Q : Subgroup X}
    (hQ : burnsideF48_img ε Q = Gp ⊓ M)
    (hself : ∀ g : X, (∀ x, x ∈ Q ↔ g * x * g⁻¹ ∈ Q) → g ∈ Q)
    (hsplit : ∀ e : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, e = n * h) (hM : M₁ ⊓ M₂ ≤ M) :
    M = Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
  have hnorm : ∀ m ∈ M, m ∈ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
    intro m hm
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · rintro ⟨hyG, hyM⟩
      exact ⟨hGp.conj_mem y hyG m, M.mul_mem (M.mul_mem hm hyM) (M.inv_mem hm)⟩
    · rintro ⟨hyG, hyM⟩
      refine ⟨?_, ?_⟩
      · have := hGp.conj_mem _ hyG m⁻¹
        simpa [mul_assoc] using this
      · have := M.mul_mem (M.mul_mem (M.inv_mem hm) hyM) hm
        simpa [mul_assoc] using this
  refine le_antisymm (fun m hm => hnorm m hm) fun x hx => ?_
  obtain ⟨n, hn, h, hh, rfl⟩ := hsplit x
  have hhM : h ∈ M := hM hh
  have hnN : n ∈ Subgroup.normalizer ((Gp ⊓ M : Subgroup E) : Set E) := by
    have := Subgroup.mul_mem _ hx (Subgroup.inv_mem _ (hnorm h hhM))
    simpa using this
  have hny : ((ε (ε.symm ⟨n, hn⟩) : ↥Gp) : E) = n := by simp
  have hyQ : ε.symm ⟨n, hn⟩ ∈ Q := by
    refine hself _ fun z => ?_
    rw [← burnsideF48_mem_img ε Q z, ← burnsideF48_mem_img ε Q, hQ, map_mul, map_mul, map_inv,
      Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hny]
    exact Subgroup.mem_normalizer_iff.1 hnN _
  have hnM : n ∈ M := by
    have := (burnsideF48_mem_img ε Q _).2 hyQ
    rw [hQ, hny] at this
    exact this.2
  exact M.mul_mem hnM hhM

theorem burnsideF48s_autc_identify {p : ℕ} [Fact p.Prime] {X E : Type} [Group X] [Group E]
    {Gp M₁ M₂ : Subgroup E} [Finite ↥Gp] (ε₀ : X ≃* ↥Gp) {B P₁ P₂ : Subgroup X}
    (hX : ChF.IsLieParabolics p (⊤ : Subgroup X) B P₁ P₂)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) :
    ∃ g : ↥Gp, (burnsideF48_img (ε₀.trans (MulAut.conj g)) P₁ = Gp ⊓ M₁ ∧
        burnsideF48_img (ε₀.trans (MulAut.conj g)) P₂ = Gp ⊓ M₂) ∨
      (burnsideF48_img (ε₀.trans (MulAut.conj g)) P₁ = Gp ⊓ M₂ ∧
        burnsideF48_img (ε₀.trans (MulAut.conj g)) P₂ = Gp ⊓ M₁) := by
  obtain ⟨⟨S₀, hS₀, hB⟩, hne, -, hmax⟩ := hX
  obtain ⟨⟨S, hS, hB'⟩, -, -, hmax'⟩ := hP
  have hS₀img : ChF.IsSylowOf p (burnsideF48_img ε₀ S₀) Gp :=
    burnsideF48_isSylowOf_of_equiv_top ε₀ hS₀
  obtain ⟨g, hg⟩ := burnsideF48_sylow_conj hS hS₀img
  refine ⟨g, ?_⟩
  set ε : X ≃* ↥Gp := ε₀.trans (MulAut.conj g) with hε
  have hSimg : burnsideF48_img ε S₀ = S := by
    rw [hε, burnsideF48_img_conj, ← hg]
  have hBimg : burnsideF48_img ε B = Gp ⊓ (M₁ ⊓ M₂) := by
    rw [hB', hB, top_inf_eq, burnsideF48_img_normalizer, hSimg]
  have hkey : ∀ Q : Subgroup X,
      (B ≤ Q ∧ Q ≤ ⊤ ∧ Q ≠ ⊤ ∧ ∀ R : Subgroup X, Q < R → R ≤ ⊤ → R = ⊤) →
      (burnsideF48_img ε Q = Gp ⊓ M₁ ∨ burnsideF48_img ε Q = Gp ⊓ M₂) := by
    rintro Q ⟨hBQ, -, hQtop, hQmax⟩
    refine (hmax' (burnsideF48_img ε Q)).1 ⟨?_, burnsideF48_img_le ε Q, ?_, ?_⟩
    · rw [← hBimg]
      exact (burnsideF48_img_le_iff ε).2 hBQ
    · intro h
      apply hQtop
      apply burnsideF48_img_injective ε
      rw [h, burnsideF48_img_top]
    · intro R hQR hRG
      obtain ⟨R₀, rfl⟩ := burnsideF48_exists_img ε hRG
      have hlt : Q < R₀ := lt_of_le_of_ne ((burnsideF48_img_le_iff ε).1 hQR.le)
        (fun h => hQR.ne (by rw [h]))
      have := hQmax R₀ hlt le_top
      rw [this, burnsideF48_img_top]
  have h1 := hkey P₁ ((hmax P₁).2 (Or.inl rfl))
  have h2 := hkey P₂ ((hmax P₂).2 (Or.inr rfl))
  have hne2 : burnsideF48_img ε P₁ ≠ burnsideF48_img ε P₂ := fun h =>
    hne (burnsideF48_img_injective ε h)
  rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2
  · exact absurd (h1.trans h2.symm) hne2
  · exact Or.inl ⟨h1, h2⟩
  · exact Or.inr ⟨h1, h2⟩
  · exact absurd (h1.trans h2.symm) hne2

section Ext


theorem burnsideF48s_autc_ext_equiv {E : Type} [Group E] [Finite E] {Gp : Subgroup E}
    [Gp.Normal] (e : ↥Gp ≃* ↥QP45.originalSubgroup)
    (hcent : Subgroup.centralizer (Gp : Set E) = ⊥) (hGp : Gp ≠ ⊤) :
    ∃ (ρ : E ≃* Ah) (ε₀ : Y ≃* ↥Gp), ∀ y : Y, ρ (ε₀ y : E) = incl y := by
  obtain ⟨M, hMP, hMA⟩ := exists_model e
  have hPA : M.P ≤ M.A := by
    rw [hMP, hMA, ← Xs_eq]
    exact Xs_le_A
  have hmem : ∀ g : E, M.actHom Gp g ∈ QA45.originalSubgroup := fun g =>
    hMA ▸ M.actHom_mem Gp g
  let ρ : E →* Ah := (M.actHom Gp).codRestrict QA45.originalSubgroup hmem
  have hρ : ∀ g : E, ((ρ g : Ah) : P45) = M.actHom Gp g := fun g => rfl
  have hρinj : Function.Injective ρ := fun a b h => by
    have h' : ((ρ a : Ah) : P45) = ((ρ b : Ah) : P45) := congrArg Subtype.val h
    rw [hρ, hρ] at h'
    exact M.actHom_injective Gp hcent h'
  have hρGp : ∀ n : ↥Gp, ((ρ n : Ah) : P45) = ((M.e n : M.P) : P45) := by
    intro n
    have hτA : ((M.e n : M.P) : P45) ∈ M.A := hPA (M.e n).2
    have hσA : M.actHom Gp n ∈ M.A := M.actHom_mem Gp n
    have key : ∀ x : ↥Gp, M.actHom Gp n * ((M.e x : M.P) : P45) * (M.actHom Gp n)⁻¹ =
        ((M.e n : M.P) : P45) * ((M.e x : M.P) : P45) * ((M.e n : M.P) : P45)⁻¹ := by
      intro x
      rw [← M.actHom_spec Gp n x]
      have hc : MulAut.conjNormal (n : E) x = n * x * n⁻¹ :=
        Subtype.ext (by simp [MulAut.conjNormal_apply])
      rw [hc, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    have hz := M.centralizer_trivial (M.A.mul_mem (M.A.inv_mem hτA) hσA) fun x hx => by
      obtain ⟨y, hy⟩ := M.e.surjective ⟨x, hx⟩
      have hk := key y
      have hyx : ((M.e y : M.P) : P45) = x := congrArg Subtype.val hy
      rw [hyx] at hk
      calc ((M.e n : M.P) : P45)⁻¹ * M.actHom Gp n * x
          = ((M.e n : M.P) : P45)⁻¹ * (M.actHom Gp n * x * (M.actHom Gp n)⁻¹) *
              M.actHom Gp n := by group
        _ = ((M.e n : M.P) : P45)⁻¹ * (((M.e n : M.P) : P45) * x * ((M.e n : M.P) : P45)⁻¹) *
              M.actHom Gp n := by rw [hk]
        _ = x * (((M.e n : M.P) : P45)⁻¹ * M.actHom Gp n) := by group
    rw [hρ]
    exact (inv_mul_eq_one.1 hz).symm
  have hcGp : Nat.card ↥Gp = 25920 := by
    rw [Nat.card_congr e.toEquiv, ← Xs_eq]
    exact card_Xs
  have hcE : Nat.card E = 51840 := by
    have h1 : Nat.card E ≤ Nat.card Ah := Nat.card_le_card_of_injective ρ hρinj
    rw [card_A] at h1
    have h2 := Subgroup.card_mul_index Gp
    rw [hcGp] at h2
    have h3 : Gp.index ≠ 1 := fun h => hGp (Subgroup.index_eq_one.1 h)
    have h4 : Gp.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    omega
  have hρbij : Function.Bijective ρ :=
    hρinj.bijective_of_nat_card_le (le_of_eq (by rw [card_A, hcE]))
  refine ⟨MulEquiv.ofBijective ρ hρbij,
    (MulEquiv.subgroupCongr (Xs_eq.trans hMP.symm)).trans M.e.symm, fun y => ?_⟩
  apply Subtype.ext
  rw [MulEquiv.ofBijective_apply, hρGp, coe_incl]
  simp

end Ext

section Chart


theorem burnsideF48s_autc_chart_of {p : ℕ} [Fact p.Prime] {B P₁ P₂ : Subgroup Y}
    (hX : ChF.IsLieParabolics p (⊤ : Subgroup Y) B P₁ P₂) {Bhat Phat₁ Phat₂ : Subgroup Ah}
    (hN1 : Subgroup.normalizer ((P₁.map incl : Subgroup Ah) : Set Ah) = Phat₁)
    (hN2 : Subgroup.normalizer ((P₂.map incl : Subgroup Ah) : Set Ah) = Phat₂)
    (hB : Phat₁ ⊓ Phat₂ = Bhat) {E : Type} [Group E] [Finite E] {Gp M₁ M₂ : Subgroup E} [Gp.Normal]
    (e : ↥Gp ≃* ↥QP45.originalSubgroup) (hcent : Subgroup.centralizer (Gp : Set E) = ⊥)
    (hsplit : ∀ x : E, ∃ n ∈ Gp, ∃ h ∈ M₁ ⊓ M₂, x = n * h)
    (hP : ChF.IsLieParabolics p Gp (Gp ⊓ (M₁ ⊓ M₂)) (Gp ⊓ M₁) (Gp ⊓ M₂)) (hGp : Gp ≠ ⊤) :
    ∃ θ : Ah ≃* E, M₁ ⊓ M₂ = Bhat.map θ.toMonoidHom ∧
      ((M₁ = Phat₁.map θ.toMonoidHom ∧ M₂ = Phat₂.map θ.toMonoidHom) ∨
        (M₁ = Phat₂.map θ.toMonoidHom ∧ M₂ = Phat₁.map θ.toMonoidHom)) := by
  haveI : IsSimpleGroup Y := isSimpleGroup_of_lieModel_PSU_four_two lieModel_Y
  obtain ⟨ρ, ε₀, hε₀⟩ := burnsideF48s_autc_ext_equiv e hcent hGp
  obtain ⟨g, hε⟩ := burnsideF48s_autc_identify ε₀ hX hP
  set ε : Y ≃* ↥Gp := ε₀.trans (MulAut.conj g) with hεdef
  let θ : Ah ≃* E := ρ.symm.trans (MulAut.conj (g : E))
  have hθ : ∀ y : Y, θ (incl y) = ((ε y : ↥Gp) : E) := by
    intro y
    have h1 : ρ.symm (incl y) = (ε₀ y : E) := by
      rw [MulEquiv.symm_apply_eq]
      exact (hε₀ y).symm
    simp [θ, hεdef, h1, MulAut.conj_apply]
  have himg : ∀ Q : Subgroup Y, (Q.map incl).map θ.toMonoidHom = burnsideF48_img ε Q := by
    intro Q
    ext x
    rw [burnsideF48_mem_img_iff]
    simp only [Subgroup.mem_map]
    constructor
    · rintro ⟨_, ⟨y, hy, rfl⟩, rfl⟩
      exact ⟨y, hy, (hθ y).symm⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨incl y, ⟨y, hy, rfl⟩, hθ y⟩
  have hpar : ∀ (Q : Subgroup Y) (Qhat M : Subgroup E), (Q = P₁ ∨ Q = P₂) →
      Subgroup.normalizer ((Q.map incl : Subgroup Ah) : Set Ah) = Qhat.comap θ.toMonoidHom →
      burnsideF48_img ε Q = Gp ⊓ M → M₁ ⊓ M₂ ≤ M → M = Qhat := by
    intro Q Qhat M hQ hN hQM hMle
    have h1 := burnsideF48s_autc_eq_normalizer ε hQM (burnsideF48s_autc_self_of_lie hX hQ)
      hsplit hMle
    have h2 := congrArg (Subgroup.map θ.toMonoidHom) hN
    rw [Subgroup.map_equiv_normalizer_eq, himg, hQM, ← h1,
      Subgroup.map_comap_eq_self_of_surjective θ.surjective] at h2
    exact h2
  have hcomap : ∀ R : Subgroup Ah, (R.map θ.toMonoidHom).comap θ.toMonoidHom = R := fun R =>
    Subgroup.comap_map_eq_self_of_injective θ.injective R
  refine ⟨θ, ?_⟩
  rcases hε with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · have e1 : M₁ = Phat₁.map θ.toMonoidHom :=
      hpar P₁ _ M₁ (Or.inl rfl) (by rw [hcomap, hN1]) h1 inf_le_left
    have e2 : M₂ = Phat₂.map θ.toMonoidHom :=
      hpar P₂ _ M₂ (Or.inr rfl) (by rw [hcomap, hN2]) h2 inf_le_right
    refine ⟨?_, Or.inl ⟨e1, e2⟩⟩
    rw [← hB, Subgroup.map_inf _ _ _ θ.injective, ← e1, ← e2]
  · have e1 : M₁ = Phat₂.map θ.toMonoidHom :=
      hpar P₂ _ M₁ (Or.inr rfl) (by rw [hcomap, hN2]) h2 inf_le_left
    have e2 : M₂ = Phat₁.map θ.toMonoidHom :=
      hpar P₁ _ M₂ (Or.inl rfl) (by rw [hcomap, hN1]) h1 inf_le_right
    refine ⟨?_, Or.inr ⟨e1, e2⟩⟩
    rw [← hB, Subgroup.map_inf _ _ _ θ.injective, ← e1, ← e2, inf_comm]

end Chart

end CFSG.ASVolI
